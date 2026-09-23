#include <math.h>
#include <stdlib.h>


#include "blake3.h"
#include "pibnd.h"
#include "pismall.h"
#include "serial.h"
#include "common.h"
#include "test.h"
#include "bench.h"
#include "assert.h"
#include "sample_z_small.h"

/*============================================================================*/
/* Private definitions                                                        */
/*============================================================================*/


/* An params::poly_q is 16 KiB, so anything dimensioned by MSGS is far too
 * large to be a local variable: at MSGS = 1000 the buffers below add up to
 * hundreds of megabytes, which gcc reported as stack frames of 295 MB for run()
 * and 328 MB for bench(). They are allocated on the heap by shuffle_alloc() and
 * the pointers index exactly like the arrays they replace; the functions that
 * take them as arguments keep their signatures, since an array parameter is a
 * pointer either way. inv_tmp is simul_inverse's scratch space and _r, theta
 * and inv are the prover's, all equally oversized. */
/* One pass of the product argument has soundness error at most MSGS / q. The
 * challenges are uniform over R_q and the ring is fully split, so a false
 * statement passes when the challenge vanishes in a slot where the identity
 * fails, which is a root of a degree-MSGS polynomial there. That is about
 * 2^-49 at MSGS = 1000, short of the LEVEL bits everything else is chosen for,
 * so the argument is repeated with independent challenges and the verifier
 * requires every pass.
 *
 * The errors multiply only if a prover who fails one pass has to start over.
 * tau and mu are hashed from the P_i, which are sent once for every pass, and
 * beta from every pass's D_i at once, so re-rolling either re-rolls them all. */
static constexpr int shuffle_ilog2(unsigned long long x) {
    return x <= 1 ? 0 : 1 + shuffle_ilog2(x >> 1);
}

static constexpr unsigned long long P_MIN = nfl::params<uint64_t>::P[0];
static constexpr int SHUFFLE_BITS =
        shuffle_ilog2(P_MIN) - shuffle_ilog2(2 * (unsigned long long) MSGS - 1);
static_assert(SHUFFLE_BITS > 0, "MSGS is too large for the modulus");
static constexpr int SHUFFLE_REPS = (LEVEL + SHUFFLE_BITS - 1) / SHUFFLE_BITS;

/* How many times each linear proof is run. Its final check reduces to
 * beta L = 0 for the residual L of the relation, so a prover whose committed
 * messages violate it passes exactly when beta vanishes in a slot where L does
 * not, which is 1 / q at best: the ring splits into DEGREE slots and the
 * challenge set is sparse, so no smaller bound is available here either. The
 * LIN_REPS challenges come from one hash of all LIN_REPS first messages, so
 * re-rolling any of them re-rolls all, and a forged relation has to survive
 * every one at once. */
static constexpr int LIN_REPS =
        (LEVEL + shuffle_ilog2(P_MIN) - 1) / shuffle_ilog2(P_MIN);
static_assert(LIN_REPS > 1, "one linear proof cannot reach LEVEL on its own");

static commit_t *com, *d;
static vector<params::poly_q> *r, *_r;
static params::poly_q *ms, *_ms, *s, *theta, *inv, *inv_tmp;
/* The commitments to the permutation elements sigma_i of Lemma 5, their
 * randomness, the sigma_i themselves in the NTT domain, and the factors
 * a_i = m_i + g(i) tau - mu and b_i = m'_i + sigma_i tau - mu the product
 * argument now runs over. */
static commit_t *pcom;
static vector<params::poly_q> *pr;
static params::poly_q *sg, *fa, *fb;
/* The proof that those openings are short, which is what pins the value of
 * each committed constant. It is produced with the P_i and consumed by the
 * verifier, so it is kept here rather than threaded through the argument
 * lists of the prover and the verifier. */
static pibnd_short_t *bnd;
/* And the proof that each of them is a ring constant, which is the other half
 * of the membership Lemma 5 asks for: short alone would leave a prover free to
 * commit to something that is not an index at all. */
static pismall_const_t *cst;
static params::poly_q (*y)[LIN_REPS][NTRU_WIDTH], (*w)[LIN_REPS][NTRU_WIDTH];
static params::poly_q (*_y)[LIN_REPS][NTRU_WIDTH];
/* What a linear proof publishes besides its responses: the hash its challenges
 * come from. The first messages are not sent -- each is determined by the
 * responses, the commitments and the challenge, so the verifier rebuilds them
 * and checks this hash instead. At three passes of three repetitions they were
 * 44% of the proof. */
static uint8_t (*lh)[BLAKE3_OUT_LEN];

static void shuffle_alloc(void) {
    com = new commit_t[MSGS];
    d = new commit_t[SHUFFLE_REPS * MSGS];
    r = new vector<params::poly_q>[MSGS];
    _r = new vector<params::poly_q>[SHUFFLE_REPS * MSGS];
    ms = new params::poly_q[MSGS];
    _ms = new params::poly_q[MSGS];
    s = new params::poly_q[MSGS];
    theta = new params::poly_q[SHUFFLE_REPS * MSGS];
    inv = new params::poly_q[MSGS];
    inv_tmp = new params::poly_q[MSGS];
    pcom = new commit_t[MSGS];
    pr = new vector<params::poly_q>[MSGS];
    sg = new params::poly_q[MSGS];
    fa = new params::poly_q[MSGS];
    fb = new params::poly_q[MSGS];
    y = new params::poly_q[MSGS][LIN_REPS][NTRU_WIDTH];
    w = new params::poly_q[MSGS][LIN_REPS][NTRU_WIDTH];
    _y = new params::poly_q[MSGS][LIN_REPS][NTRU_WIDTH];
    lh = new uint8_t[MSGS][BLAKE3_OUT_LEN];
}

static void shuffle_free(void) {
    delete[] com;
    delete[] d;
    delete[] r;
    delete[] _r;
    delete[] ms;
    delete[] _ms;
    delete[] s;
    delete[] theta;
    delete[] inv;
    delete[] inv_tmp;
    delete[] pcom;
    delete[] pr;
    delete[] sg;
    delete[] fa;
    delete[] fb;
    pibnd_short_free(bnd);
    bnd = NULL;
    pismall_const_free(cst);
    cst = NULL;
    pismall_const_clear();
    delete[] y;
    delete[] w;
    delete[] _y;
    delete[] lh;
}


/**
 * The map g : [MSGS] -> D of Lemma 5, instantiated as g(i) = i: the ring
 * constant with that value, in the coefficient domain.
 *
 * @param[out] out			- the constant.
 * @param[in] i				- its value.
 */
static void index_scalar(params::poly_q &out, size_t i) {
    array<mpz_t, params::poly_q::degree> coeffs;

    for (size_t k = 0; k < params::poly_q::degree; k++) {
        mpz_init2(coeffs[k], (params::poly_q::bits_in_moduli_product() << 2));
        mpz_set_ui(coeffs[k], k == 0 ? i : 0);
    }
    out.mpz2poly(coeffs);
    for (size_t k = 0; k < params::poly_q::degree; k++) {
        mpz_clear(coeffs[k]);
    }
}

/**
 * The prover's first message: commit to the permutation elements sigma_i. An
 * honest prover has sigma_i = g(pi(i)) for the permutation with m'_i = m_pi(i).
 * It precedes the challenges tau and mu, which is what stops a prover from
 * choosing the sigma_i once it knows them.
 *
 * @param[out] p			- the commitments.
 * @param[out] pr			- their randomness.
 * @param[in] sigma			- the permutation elements, coefficient domain.
 * @param[in] key			- the commitment key.
 */
static void shuffle_commit_sigma(commit_t p[MSGS], vector<params::poly_q> pr[MSGS],
                                 params::poly_q sigma[MSGS], comkey_t &key) {
    for (size_t i = 0; i < MSGS; i++) {
        pr[i].resize(NTRU_WIDTH);
        bdlop_sample_rand(pr[i]);
        bdlop_commit(p[i], {sigma[i]}, key, pr[i]);
        sg[i] = sigma[i];
        sg[i].ntt_pow_phi();
    }

    pismall_const_free(cst);
    cst = pismall_const_prove(key, p, pr, sigma, MSGS);
    pibnd_short_free(bnd);
    bnd = pibnd_short_prove(key, p, pr, sigma, MSGS);
}

/**
 * The challenges tau and mu of Lemma 5, hashed from the commitments they are
 * about so that the prover is bound to them.
 */
static void shuffle_chal_hash(params::poly_q &tau, params::poly_q &mu,
                              commit_t c[MSGS], commit_t p[MSGS],
                              params::poly_q _ms[MSGS], int rep) {
    uint8_t hash[BLAKE3_OUT_LEN];
    blake3_hasher hasher;

    blake3_hasher_init(&hasher);
    for (int i = 0; i < MSGS; i++) {
        blake3_hasher_update(&hasher, (const uint8_t *) c[i].c2[0].data(),
                             8 * NTRU_DEGREE);
        blake3_hasher_update(&hasher, (const uint8_t *) p[i].c1.data(),
                             8 * NTRU_DEGREE);
        blake3_hasher_update(&hasher, (const uint8_t *) p[i].c2[0].data(),
                             8 * NTRU_DEGREE);
        blake3_hasher_update(&hasher, (const uint8_t *) _ms[i].data(),
                             8 * NTRU_DEGREE);
    }
    blake3_hasher_update(&hasher, (const uint8_t *) &rep, sizeof(rep));
    blake3_hasher_finalize(&hasher, hash, BLAKE3_OUT_LEN);

    nfl::fastrandombytes_seed(hash);
    tau = nfl::uniform();
    mu = nfl::uniform();
    nfl::fastrandombytes_reseed();
}

/**
 * The factors of Lemma 5: a_i pairs the input with its index, b_i pairs the
 * output with the permutation element the prover committed to. A product
 * identity over these pairs is a permutation of pairs, which a list mixed
 * across the CRT components cannot satisfy -- the identity over the messages
 * alone can be, which is the attack of Section 4.1 of ePrint 2025/658.
 */
static void shuffle_factors(params::poly_q ms[MSGS], params::poly_q _ms[MSGS],
                            params::poly_q &tau, params::poly_q &mu) {
    params::poly_q gl;

    for (size_t i = 0; i < MSGS; i++) {
        index_scalar(gl, i);
        gl.ntt_pow_phi();
        fa[i] = ms[i] + gl * tau - mu;
        fb[i] = _ms[i] + sg[i] * tau - mu;
    }
}

/**
 * The coefficients of the l-th linear proof. b_l is no longer public, since
 * sigma_l is committed rather than sent, so the term that multiplies it splits
 * into a public part and one that multiplies the commitment P_l.
 */
static void shuffle_coeffs(params::poly_q coef[3], size_t l, params::poly_q s[MSGS],
                           params::poly_q _ms[MSGS], params::poly_q &beta,
                           params::poly_q &tau, params::poly_q &mu) {
    params::poly_q raw, gl, zero = 0;

    if (l == 0) {
        coef[0] = beta;
    } else {
        coef[0] = s[l - 1];
    }

    if (l < MSGS - 1) {
        raw = s[l];
    } else {
        if (MSGS & 1) {
            raw = zero - beta;
        } else {
            raw = beta;
        }
    }

    index_scalar(gl, l);
    gl.ntt_pow_phi();
    gl = gl * tau - mu;
    coef[2] = coef[0] * gl + raw * (_ms[l] - mu);
    coef[1] = raw * tau;
}

static void lin_hash(uint8_t h[BLAKE3_OUT_LEN], comkey_t &key, commit_t x,
                     commit_t p, commit_t y, params::poly_q coef[3],
                     params::poly_q u[LIN_REPS], params::poly_q t[LIN_REPS],
                     params::poly_q tp[LIN_REPS], params::poly_q _t[LIN_REPS]) {
    blake3_hasher hasher;

    blake3_hasher_init(&hasher);

    /* Hash public key. */
    for (size_t i = 0; i < NTRU_HEIGHT; i++) {
        for (int j = 0; j < NTRU_WIDTH - NTRU_HEIGHT; j++) {
            blake3_hasher_update(&hasher, (const uint8_t *) key.A1[i][j].data(),
                                 8 * NTRU_DEGREE);
        }
    }
    for (size_t j = 0; j < NTRU_WIDTH; j++) {
        blake3_hasher_update(&hasher, (const uint8_t *) key.A2[0][j].data(),
                             8 * NTRU_DEGREE);
    }

    /* Hash the coefficients of the linear relation. */
    for (size_t i = 0; i < 3; i++) {
        blake3_hasher_update(&hasher, (const uint8_t *) coef[i].data(),
                             8 * NTRU_DEGREE);
    }

    blake3_hasher_update(&hasher, (const uint8_t *) x.c1.data(), 8 * NTRU_DEGREE);
    blake3_hasher_update(&hasher, (const uint8_t *) p.c1.data(), 8 * NTRU_DEGREE);
    blake3_hasher_update(&hasher, (const uint8_t *) y.c1.data(), 8 * NTRU_DEGREE);
    blake3_hasher_update(&hasher, (const uint8_t *) x.c2[0].data(),
                         8 * NTRU_DEGREE);
    blake3_hasher_update(&hasher, (const uint8_t *) p.c2[0].data(),
                         8 * NTRU_DEGREE);
    blake3_hasher_update(&hasher, (const uint8_t *) y.c2[0].data(),
                         8 * NTRU_DEGREE);

    /* Every repetition's first message, so that re-rolling any of them moves
     * every challenge and a forged relation has to survive all of them. */
    for (int j = 0; j < LIN_REPS; j++) {
        blake3_hasher_update(&hasher, (const uint8_t *) u[j].data(),
                             8 * NTRU_DEGREE);
        blake3_hasher_update(&hasher, (const uint8_t *) t[j].data(),
                             8 * NTRU_DEGREE);
        blake3_hasher_update(&hasher, (const uint8_t *) tp[j].data(),
                             8 * NTRU_DEGREE);
        blake3_hasher_update(&hasher, (const uint8_t *) _t[j].data(),
                             8 * NTRU_DEGREE);
    }

    blake3_hasher_finalize(&hasher, h, BLAKE3_OUT_LEN);
}

/* The LIN_REPS challenges of one linear proof, all from that single hash. */
static void lin_chal(params::poly_q beta[LIN_REPS],
                     const uint8_t h[BLAKE3_OUT_LEN]) {
    nfl::fastrandombytes_seed(h);
    for (int j = 0; j < LIN_REPS; j++) {
        bdlop_sample_chal(beta[j]);
    }
    nfl::fastrandombytes_reseed();
}


static int simul_inverse(params::poly_q inv[MSGS], params::poly_q m[MSGS]) {
    params::poly_q u;
    inv[0] = m[0];
    inv_tmp[0] = m[0];

    for (size_t i = 1; i < MSGS; i++) {
        inv_tmp[i] = m[i];
        inv[i] = inv[i - 1] * m[i];
    }

    u = inv[MSGS - 1];
    if (!util::invert(u, u)) {
        return 0;
    }

    for (size_t i = MSGS - 1; i > 0; i--) {
        inv[i] = u * inv[i - 1];
        u = u * inv_tmp[i];
    }
    inv[0] = u;

    return 1;
}

/* The three openings of every repetition are masked from one Gaussian and
 * stand or fall together, since a fresh first message anywhere moves every
 * challenge. So the dot products and norms of all of them are accumulated
 * here and the decision is taken once, over the batch: testing each vector on
 * its own would multiply the rejection rate by the number of vectors. */
static void rej_accum(mpz_t dot, mpz_t norm, params::poly_q z[NTRU_WIDTH],
                      params::poly_q v[NTRU_WIDTH]) {
    array<mpz_t, params::poly_q::degree> coeffs0, coeffs1;
    params::poly_q t;
    mpz_t qDivBy2, tmp;

    mpz_inits(qDivBy2, tmp, nullptr);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_init2(coeffs0[i], (params::poly_q::bits_in_moduli_product() << 2));
        mpz_init2(coeffs1[i], (params::poly_q::bits_in_moduli_product() << 2));
    }

    mpz_fdiv_q_2exp(qDivBy2, params::poly_q::moduli_product(), 1);
    for (int i = 0; i < NTRU_WIDTH; i++) {
        t = z[i];
        t.invntt_pow_invphi();
        t.poly2mpz(coeffs0);
        t = v[i];
        t.invntt_pow_invphi();
        t.poly2mpz(coeffs1);
        for (size_t j = 0; j < params::poly_q::degree; j++) {
            util::center(coeffs0[j], coeffs0[j],
                         params::poly_q::moduli_product(), qDivBy2);
            util::center(coeffs1[j], coeffs1[j],
                         params::poly_q::moduli_product(), qDivBy2);
            mpz_mul(tmp, coeffs0[j], coeffs1[j]);
            mpz_add(dot, dot, tmp);
            mpz_mul(tmp, coeffs1[j], coeffs1[j]);
            mpz_add(norm, norm, tmp);
        }
    }

    mpz_clears(qDivBy2, tmp, nullptr);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_clear(coeffs0[i]);
        mpz_clear(coeffs1[i]);
    }
}

/* Accept with probability min(1, exp((-2<z, v> + ||v||^2) / 2 s2) / M). */
static int rej_decide(mpz_t dot, mpz_t norm, uint64_t s2) {
    double r, M = 1.75;
    int64_t seed;
    mpf_t u;
    uint8_t buf[8];
    gmp_randstate_t state;
    int result;

    mpf_init(u);
    gmp_randinit_mt(state);
    if (getrandom(buf, sizeof(buf), 0) != sizeof(buf)) {
        fprintf(stderr, "ERROR: could not read entropy for rejection sampling\n");
        abort();
    }
    memcpy(&seed, buf, sizeof(buf));
    gmp_randseed_ui(state, seed);
    mpf_urandomb(u, state, mpf_get_default_prec());

    r = -2.0 * mpz_get_d(dot) + mpz_get_d(norm);
    r = r / (2.0 * s2);
    r = exp(r) / M;
    result = mpf_get_d(u) > r;

    mpf_clear(u);
    gmp_randclear(state);
    return result;
}

static void lin_prover(params::poly_q y[LIN_REPS][NTRU_WIDTH],
                       params::poly_q w[LIN_REPS][NTRU_WIDTH],
                       params::poly_q _y[LIN_REPS][NTRU_WIDTH],
                       uint8_t h[BLAKE3_OUT_LEN], commit_t x, commit_t p,
                       commit_t _x, params::poly_q coef[3], comkey_t &key,
                       vector<params::poly_q> r, vector<params::poly_q> pr,
                       vector<params::poly_q> _r) {
    params::poly_q beta[LIN_REPS];
    params::poly_q t[LIN_REPS], tp[LIN_REPS], _t[LIN_REPS], u[LIN_REPS];
    params::poly_q tmp[NTRU_WIDTH], ptmp[NTRU_WIDTH], _tmp[NTRU_WIDTH];
    array<mpz_t, params::poly_q::degree> coeffs;
    mpz_t dot, norm;
    int rej;

    mpz_inits(dot, norm, nullptr);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
    }

    do {
        /* Prover samples y, w and y' from Gaussian, once per repetition. */
        for (int j = 0; j < LIN_REPS; j++) {
            for (int i = 0; i < NTRU_WIDTH; i++) {
                for (size_t k = 0; k < params::poly_q::degree; k++) {
                    mpz_set_si(coeffs[k], sample_z(0.0, NTRU_SIGMA_C));
                }
                y[j][i].mpz2poly(coeffs);
                y[j][i].ntt_pow_phi();
                for (size_t k = 0; k < params::poly_q::degree; k++) {
                    mpz_set_si(coeffs[k], sample_z(0.0, NTRU_SIGMA_C));
                }
                w[j][i].mpz2poly(coeffs);
                w[j][i].ntt_pow_phi();
                for (size_t k = 0; k < params::poly_q::degree; k++) {
                    mpz_set_si(coeffs[k], sample_z(0.0, NTRU_SIGMA_C));
                }
                _y[j][i].mpz2poly(coeffs);
                _y[j][i].ntt_pow_phi();
            }

            t[j] = y[j][0];
            tp[j] = w[j][0];
            _t[j] = _y[j][0];
            for (int i = 0; i < NTRU_HEIGHT; i++) {
                for (int k = 0; k < NTRU_WIDTH - NTRU_HEIGHT; k++) {
                    t[j] = t[j] + key.A1[i][k] * y[j][k + NTRU_HEIGHT];
                    tp[j] = tp[j] + key.A1[i][k] * w[j][k + NTRU_HEIGHT];
                    _t[j] = _t[j] + key.A1[i][k] * _y[j][k + NTRU_HEIGHT];
                }
            }

            u[j] = 0;
            for (int i = 0; i < NTRU_WIDTH; i++) {
                u[j] = u[j] + coef[0] * (key.A2[0][i] * y[j][i]);
                u[j] = u[j] + coef[1] * (key.A2[0][i] * w[j][i]);
                u[j] = u[j] - (key.A2[0][i] * _y[j][i]);
            }
        }

        /* Sample every challenge from one hash of every first message. */
        lin_hash(h, key, x, p, _x, coef, u, t, tp, _t);
        lin_chal(beta, h);

        /* Prover, and one rejection test over all of the openings. */
        mpz_set_ui(dot, 0);
        mpz_set_ui(norm, 0);
        for (int j = 0; j < LIN_REPS; j++) {
            for (int i = 0; i < NTRU_WIDTH; i++) {
                tmp[i] = beta[j] * r[i];
                ptmp[i] = beta[j] * pr[i];
                _tmp[i] = beta[j] * _r[i];
                y[j][i] = y[j][i] + tmp[i];
                w[j][i] = w[j][i] + ptmp[i];
                _y[j][i] = _y[j][i] + _tmp[i];
            }
            rej_accum(dot, norm, y[j], tmp);
            rej_accum(dot, norm, w[j], ptmp);
            rej_accum(dot, norm, _y[j], _tmp);
        }
        rej = rej_decide(dot, norm, NTRU_SIGMA_C * NTRU_SIGMA_C);
    } while (rej);

    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_clear(coeffs[i]);
    }
    mpz_clears(dot, norm, nullptr);
}

static int lin_verifier(params::poly_q z[LIN_REPS][NTRU_WIDTH],
                        params::poly_q wz[LIN_REPS][NTRU_WIDTH],
                        params::poly_q _z[LIN_REPS][NTRU_WIDTH],
                        const uint8_t h[BLAKE3_OUT_LEN], commit_t x, commit_t p,
                        commit_t _x, params::poly_q coef[3], comkey_t &key) {
    params::poly_q beta[LIN_REPS], v, pv, _v, acc;
    params::poly_q t[LIN_REPS], tp[LIN_REPS], _t[LIN_REPS], u[LIN_REPS];
    uint8_t h2[BLAKE3_OUT_LEN];
    int result = 1;

    /* The challenges come from the published hash, and the first messages are
     * then whatever makes each verification equation hold: rebuilding them and
     * hashing them back is the same check as receiving them and testing the
     * equations, for a thirty-second of the bytes. */
    lin_chal(beta, h);

    for (int j = 0; j < LIN_REPS; j++) {
        /* Verifier checks norm, reconstruct from NTT representation. */
        for (int i = 0; i < NTRU_WIDTH; i++) {
            v = z[j][i];
            v.invntt_pow_invphi();
            result &= bdlop_test_norm(v, NTRU_SIGMA_C * NTRU_SIGMA_C);
            v = wz[j][i];
            v.invntt_pow_invphi();
            result &= bdlop_test_norm(v, NTRU_SIGMA_C * NTRU_SIGMA_C);
            v = _z[j][i];
            v.invntt_pow_invphi();
            result &= bdlop_test_norm(v, NTRU_SIGMA_C * NTRU_SIGMA_C);
        }

        /* Verifier computes A1z, A1w and A1z'. */
        v = z[j][0];
        pv = wz[j][0];
        _v = _z[j][0];
        for (int i = 0; i < NTRU_HEIGHT; i++) {
            for (int k = 0; k < NTRU_WIDTH - NTRU_HEIGHT; k++) {
                v = v + key.A1[i][k] * z[j][k + NTRU_HEIGHT];
                pv = pv + key.A1[i][k] * wz[j][k + NTRU_HEIGHT];
                _v = _v + key.A1[i][k] * _z[j][k + NTRU_HEIGHT];
            }
        }

        t[j] = v - beta[j] * x.c1;
        tp[j] = pv - beta[j] * p.c1;
        _t[j] = _v - beta[j] * _x.c1;

        v = 0;
        for (int i = 0; i < NTRU_WIDTH; i++) {
            v = v + coef[0] * (key.A2[0][i] * z[j][i]);
            v = v + coef[1] * (key.A2[0][i] * wz[j][i]);
            v = v - (key.A2[0][i] * _z[j][i]);
        }
        acc = (coef[0] * x.c2[0] + coef[1] * p.c2[0] + coef[2] - _x.c2[0])
                * beta[j];
        u[j] = v - acc;
    }

    lin_hash(h2, key, x, p, _x, coef, u, t, tp, _t);
    result &= (memcmp(h, h2, BLAKE3_OUT_LEN) == 0);

    return result;
}

/* Every pass's beta, from a single hash of every pass's first message. Drawing
 * them together is what makes the passes multiply: a prover who re-rolls one
 * D_i moves every beta, so it cannot settle the passes one at a time. */
static void shuffle_beta_hash(params::poly_q beta[SHUFFLE_REPS], commit_t c[MSGS],
                              commit_t p[MSGS], commit_t d[],
                              params::poly_q _ms[MSGS],
                              params::poly_q tau[SHUFFLE_REPS],
                              params::poly_q mu[SHUFFLE_REPS]) {
    uint8_t hash[BLAKE3_OUT_LEN];
    blake3_hasher hasher;

    blake3_hasher_init(&hasher);

    for (int i = 0; i < MSGS; i++) {
        blake3_hasher_update(&hasher, (const uint8_t *) _ms[i].data(),
                             8 * NTRU_DEGREE);
        blake3_hasher_update(&hasher, (const uint8_t *) c[i].c2[0].data(),
                             8 * NTRU_DEGREE);
        blake3_hasher_update(&hasher, (const uint8_t *) p[i].c2[0].data(),
                             8 * NTRU_DEGREE);
    }

    for (int rep = 0; rep < SHUFFLE_REPS; rep++) {
        blake3_hasher_update(&hasher, (const uint8_t *) tau[rep].data(),
                             8 * NTRU_DEGREE);
        blake3_hasher_update(&hasher, (const uint8_t *) mu[rep].data(),
                             8 * NTRU_DEGREE);
        for (int i = 0; i < MSGS; i++) {
            blake3_hasher_update(&hasher,
                                 (const uint8_t *) d[rep * MSGS + i].c2[0].data(),
                                 8 * NTRU_DEGREE);
        }
    }

    blake3_hasher_finalize(&hasher, hash, BLAKE3_OUT_LEN);

    /* Sample challenges from RNG seeded with hash. */
    nfl::fastrandombytes_seed(hash);
    for (int rep = 0; rep < SHUFFLE_REPS; rep++) {
        beta[rep] = nfl::uniform();
    }
    nfl::fastrandombytes_reseed();
}

/* The half of a pass the prover can send before beta: its D_i, built from the
 * factors its own tau and mu fix. Every pass reaches this point before any
 * beta is drawn, which is what binds the passes to each other. */
static int shuffle_prover_commit(commit_t d[MSGS], vector<params::poly_q> _r[MSGS],
                                 params::poly_q theta[MSGS], params::poly_q ms[MSGS],
                                 params::poly_q _ms[MSGS], params::poly_q &tau,
                                 params::poly_q &mu, comkey_t &key) {
    params::poly_q t0;

    shuffle_factors(ms, _ms, tau, mu);

    /* The s_i divide by the b_i, so the pass is only usable if their product
     * inverts. Testing it here saves discovering it after the linear proofs
     * have been built. */
    if (!simul_inverse(inv, fb)) {
        return 0;
    }

    /* Prover samples theta_i and computes commitments D_i. */
    for (size_t i = 0; i < MSGS - 1; i++) {
        theta[i] = nfl::ZO_dist();
        theta[i].ntt_pow_phi();
        if (i == 0) {
            t0 = theta[0] * fb[0];
        } else {
            t0 = theta[i - 1] * fa[i] + theta[i] * fb[i];
        }
        t0.invntt_pow_invphi();
        _r[i].resize(NTRU_WIDTH);
        bdlop_sample_rand(_r[i]);
        bdlop_commit(d[i], {t0}, key, _r[i]);
    }
    t0 = theta[MSGS - 2] * fa[MSGS - 1];
    t0.invntt_pow_invphi();
    _r[MSGS - 1].resize(NTRU_WIDTH);
    bdlop_sample_rand(_r[MSGS - 1]);
    bdlop_commit(d[MSGS - 1], {t0}, key, _r[MSGS - 1]);

    return 1;
}

/* The second half, once beta is known. The factors and their inverses follow
 * from the pass's tau and mu, and recomputing them is cheaper than holding a
 * copy per pass. */
static int shuffle_prover_respond(params::poly_q y[MSGS][LIN_REPS][NTRU_WIDTH],
                           params::poly_q w[MSGS][LIN_REPS][NTRU_WIDTH],
                           params::poly_q _y[MSGS][LIN_REPS][NTRU_WIDTH],
                           uint8_t lh[MSGS][BLAKE3_OUT_LEN], commit_t d[MSGS],
                           commit_t p[MSGS],
                           vector<params::poly_q> pr[MSGS],
                           vector<params::poly_q> _r[MSGS],
                           params::poly_q theta[MSGS],
                           params::poly_q s[MSGS], commit_t c[MSGS], params::poly_q ms[MSGS],
                           params::poly_q _ms[MSGS], vector<params::poly_q> r[MSGS],
                           params::poly_q &beta, params::poly_q &tau,
                           params::poly_q &mu, comkey_t &key) {
    params::poly_q coef[3];

    shuffle_factors(ms, _ms, tau, mu);
    if (!simul_inverse(inv, fb)) {
        return 0;
    }

    for (size_t i = 0; i < MSGS - 1; i++) {
        if (i == 0) {
            s[0] = theta[0] * fb[0] - beta * fa[0];
        } else {
            s[i] = theta[i - 1] * fa[i] + theta[i] * fb[i] - s[i - 1] * fa[i];
        }
        s[i] = s[i] * inv[i];
    }

    /* Now run \Prod_LIN instances, one for each commitment. */
    for (size_t l = 0; l < MSGS; l++) {
        shuffle_coeffs(coef, l, s, _ms, beta, tau, mu);
        lin_prover(y[l], w[l], _y[l], lh[l], c[l], p[l], d[l], coef, key,
                   r[l], pr[l], _r[l]);
    }

    return 1;
}

static int shuffle_verifier(params::poly_q y[MSGS][LIN_REPS][NTRU_WIDTH],
                            params::poly_q w[MSGS][LIN_REPS][NTRU_WIDTH],
                            params::poly_q _y[MSGS][LIN_REPS][NTRU_WIDTH],
                            uint8_t lh[MSGS][BLAKE3_OUT_LEN], commit_t d[MSGS],
                            commit_t p[MSGS],
                            params::poly_q s[MSGS], commit_t c[MSGS], params::poly_q _ms[MSGS],
                            params::poly_q &beta, params::poly_q &tau,
                            params::poly_q &mu, comkey_t &key) {
    params::poly_q coef[3];
    int result = 1;

    for (size_t l = 0; l < MSGS; l++) {
        shuffle_coeffs(coef, l, s, _ms, beta, tau, mu);
        result &= lin_verifier(y[l], w[l], _y[l], lh[l], c[l], p[l], d[l],
                               coef, key);
    }

    return result;
}

/**
 * Executes the run function of a cryptographic protocol involving commitments.
 *
 * @param com Array of commitments of size MSGS.
 * @param m Vector of vectors containing polynomial values.
 * @param _m Vector of vectors containing adjusted polynomial values.
 * @param key Commitment key.
 * @param r Array of vectors containing polynomial values of size MSGS.
 *
 * @return Returns the result of the shuffle_verifier function.
 *
 * @note This function extends commitments, adjusts keys, and then invokes
 *       the shuffle_prover and shuffle_verifier functions.
 */
static int run(commit_t com[MSGS], vector<params::poly_q> m,
               vector<params::poly_q> _m, vector<params::poly_q> sigma,
               comkey_t &key, vector<params::poly_q> r[MSGS]) {
    // Declare local variables for the function
    params::poly_q tau[SHUFFLE_REPS], mu[SHUFFLE_REPS];
    params::poly_q beta[SHUFFLE_REPS], vbeta[SHUFFLE_REPS];
    int result = 1;

    for (size_t i = 0; i < MSGS; i++) {
        ms[i] = m[i];
        ms[i].ntt_pow_phi();
        _ms[i] = _m[i];
        _ms[i].ntt_pow_phi();
    }

    /* The first message: the commitments to the sigma_i and the two sub-proofs
     * that place them in D. They are sent once and shared by every pass, so
     * re-rolling them re-rolls every pass at once; a first message per pass
     * would let a prover settle the passes one at a time. */
    shuffle_commit_sigma(pcom, pr, sigma.data(), key);

    /* Every pass commits its D_i before any of them has a beta, for the same
     * reason: beta is a hash of all of them together. */
    for (int rep = 0; rep < SHUFFLE_REPS; rep++) {
        shuffle_chal_hash(tau[rep], mu[rep], com, pcom, _ms, rep);
        if (!shuffle_prover_commit(&d[rep * MSGS], &_r[rep * MSGS],
                                   &theta[rep * MSGS], ms, _ms, tau[rep],
                                   mu[rep], key)) {
            return 0;
        }
    }

    /* The sub-proofs about the P_i are checked once, here: they are the first
     * message and do not belong to any one pass. */
    if (!pismall_const_verify(cst, key, pcom, MSGS)) {
        return 0;
    }
    if (!pibnd_short_verify(bnd, key, pcom, MSGS)) {
        return 0;
    }

    /* Twice, because the verifier derives its challenges from the transcript
     * rather than taking the prover's word for them; the two must agree. */
    shuffle_beta_hash(beta, com, pcom, d, _ms, tau, mu);
    shuffle_beta_hash(vbeta, com, pcom, d, _ms, tau, mu);

    for (int rep = 0; rep < SHUFFLE_REPS; rep++) {
        if (!shuffle_prover_respond(y, w, _y, lh, &d[rep * MSGS],
                                    pcom, pr, &_r[rep * MSGS],
                                    &theta[rep * MSGS], s, com, ms, _ms, r,
                                    beta[rep], tau[rep], mu[rep], key)) {
            return 0;
        }
        result &= shuffle_verifier(y, w, _y, lh, &d[rep * MSGS], pcom, s, com,
                                   _ms, vbeta[rep], tau[rep], mu[rep], key);
    }

    return result;
}

static void run2(commit_t com[MSGS], vector<params::poly_q> m,
               vector<params::poly_q> _m, vector<params::poly_q> sigma,
               comkey_t &key, vector<params::poly_q> r[MSGS]) {
    // Declare local variables for the function
    params::poly_q tau[SHUFFLE_REPS], mu[SHUFFLE_REPS], beta[SHUFFLE_REPS];

    for (size_t i = 0; i < MSGS; i++) {
        ms[i] = m[i];
        ms[i].ntt_pow_phi();
        _ms[i] = _m[i];
        _ms[i].ntt_pow_phi();
    }

    shuffle_commit_sigma(pcom, pr, sigma.data(), key);

    for (int rep = 0; rep < SHUFFLE_REPS; rep++) {
        shuffle_chal_hash(tau[rep], mu[rep], com, pcom, _ms, rep);
        shuffle_prover_commit(&d[rep * MSGS], &_r[rep * MSGS],
                              &theta[rep * MSGS], ms, _ms, tau[rep], mu[rep],
                              key);
    }
    shuffle_beta_hash(beta, com, pcom, d, _ms, tau, mu);
    for (int rep = 0; rep < SHUFFLE_REPS; rep++) {
        shuffle_prover_respond(y, w, _y, lh, &d[rep * MSGS], pcom, pr,
                               &_r[rep * MSGS], &theta[rep * MSGS], s, com,
                               ms, _ms, r, beta[rep], tau[rep], mu[rep], key);
    }
}



#ifdef MAIN

/**
 * Mix two ring elements by swapping half of their NTT slots. R_q splits into
 * DEGREE linear factors, since q = 1 mod 2d, so the result is a permutation of
 * the inputs inside each factor and not over the ring: the manipulation of
 * Section 4.1 of ePrint 2025/658. Both arguments are in the coefficient domain
 * on entry and on exit.
 *
 * @param[in,out] a			- the first element.
 * @param[in,out] b			- the second element.
 */
static void crt_mix(params::poly_q &a, params::poly_q &b) {
    a.ntt_pow_phi();
    b.ntt_pow_phi();
    for (size_t i = 0; i < params::poly_q::degree / 2; i++) {
        uint64_t t = a(0, i);
        a(0, i) = b(0, i);
        b(0, i) = t;
    }
    a.invntt_pow_invphi();
    b.invntt_pow_invphi();
}

/**
 * Neff's product, prod_i (v_i - chi), the identity the proof of shuffle checks.
 *
 * @param[out] out			- the product, in the NTT domain.
 * @param[in] v				- the list, in the NTT domain.
 * @param[in] chi			- the challenge, in the NTT domain.
 */
static void neff_product(params::poly_q &out, vector<params::poly_q> &v,
                         params::poly_q &chi) {
    params::poly_q acc = 1;

    acc.ntt_pow_phi();
    for (size_t i = 0; i < v.size(); i++) {
        acc = acc * (v[i] - chi);
    }
    out = acc;
}

static void test() {
    comkey_t key;
    vector<params::poly_q> m(MSGS), _m(MSGS), am(MSGS), sigma(MSGS);
    vector<params::poly_q> asigma(MSGS);

    /* Generate commitment key-> */
    bdlop_keygen(key);
    for (int i = 0; i < MSGS; i++) {
        m[i] = nfl::ZO_dist();
        r[i].resize(NTRU_WIDTH);
        bdlop_sample_rand(r[i]);
        bdlop_commit(com[i], {m[i]}, key, r[i]);
    }

    /* Prover shuffles messages (only a circular shift for simplicity), and
     * states the permutation as the elements sigma_i = g(pi(i)) of Lemma 5. */
    for (int i = 0; i < MSGS; i++) {
        _m[i] = m[(i + 1) % MSGS];
        index_scalar(sigma[i], (i + 1) % MSGS);
    }

    TEST_ONCE("polynomial inverse is correct")
    {
        params::poly_q alpha[2] = {nfl::uniform(), nfl::uniform()};

        alpha[0].ntt_pow_phi();
        TEST_ASSERT(util::invert(alpha[1], alpha[0]) == 1, end);
        alpha[0] = alpha[0] * alpha[1];
        alpha[0] = alpha[0] * alpha[1];
        TEST_ASSERT(util::equal(alpha[0], alpha[1]), end);
    }
    TEST_END;

    TEST_ONCE("serialisation round-trips both encodings")
    {
        serial::bits bu, bg;
        params::poly_q a = nfl::uniform(), a2, g, g2;
        array<mpz_t, params::poly_q::degree> cf;

        for (size_t i = 0; i < params::poly_q::degree; i++) {
            mpz_init2(cf[i], (params::poly_q::bits_in_moduli_product() << 2));
            mpz_set_si(cf[i], sample_z(0.0, NTRU_SIGMA_C));
        }
        g.mpz2poly(cf);
        for (size_t i = 0; i < params::poly_q::degree; i++) {
            mpz_clear(cf[i]);
        }

        serial::put_uniform(bu, a);
        serial::get_uniform(bu, a2);
        TEST_ASSERT(util::equal(a, a2), end);

        serial::put_gauss(bg, g, NTRU_SIGMA_C);
        serial::get_gauss(bg, g2, NTRU_SIGMA_C);
        TEST_ASSERT(util::equal(g, g2), end);

        /* And it is smaller than writing the opening at full width. */
        TEST_ASSERT(bg.bytes() * 2 < bu.bytes(), end);
    }
    TEST_END;

    TEST_ONCE("shuffle proof is consistent")
    {
        TEST_ASSERT(run(com, m, _m, sigma, key, r) == 1, end);
    }
    TEST_END;

    /* The attack of Section 4.1 of ePrint 2025/658. The output list is mixed
     * rather than permuted: two of its entries exchange half of their CRT
     * components, so the list is a permutation of the input inside each of the
     * DEGREE fields the ring splits into, and is not a permutation of it over
     * the ring. Neff's product is a product over the same ring, so it cannot
     * tell the two apart. */
    for (int i = 0; i < MSGS; i++) {
        am[i] = _m[i];
    }
    crt_mix(am[0], am[1]);

    TEST_ONCE("CRT-mixed list is not a permutation but passes Neff's product")
    {
        vector<params::poly_q> v(MSGS), av(MSGS);
        params::poly_q chi = nfl::uniform(), p0, p1;

        for (int i = 0; i < MSGS; i++) {
            v[i] = _m[i];
            v[i].ntt_pow_phi();
            av[i] = am[i];
            av[i].ntt_pow_phi();
        }
        TEST_ASSERT(!util::equal(am[0], _m[0]), end);
        TEST_ASSERT(!util::equal(am[0], _m[1]), end);
        neff_product(p0, v, chi);
        neff_product(p1, av, chi);
        TEST_ASSERT(util::equal(p0, p1), end);
    }
    TEST_END;

    TEST_ONCE("shuffle proof rejects the CRT-mixing attack")
    {
        TEST_ASSERT(run(com, m, am, sigma, key, r) == 0, end);
    }
    TEST_END;

    /* Second-order attack, on the membership half: the prover applies to the
     * permutation elements the same mix it applied to the messages, so the
     * pairs balance again in every slot. A mix of two constants across the NTT
     * slots is not a constant -- it is dense in the coefficient domain, with
     * coefficients the size of q -- so the norm bound rejects it. */
    for (int i = 0; i < MSGS; i++) {
        asigma[i] = sigma[i];
    }
    crt_mix(asigma[0], asigma[1]);

    TEST_ONCE("shuffle proof rejects CRT-mixed sigma")
    {
        TEST_ASSERT(run(com, m, am, asigma, key, r) == 0, end);
    }
    TEST_END;

    end:
    return;
}

/* The size of the transcript the last run() produced. The pass-local buffers
 * are reused across passes, so one pass is measured and multiplied; everything
 * else is measured as it stands. */
static void proof_size(void) {
    serial::bits pass, once;
    params::poly_q t0;

    for (size_t i = 0; i < MSGS; i++) {
        serial::put_uniform(pass, d[i].c1);
        serial::put_uniform(pass, d[i].c2[0]);
        serial::put_uniform(pass, s[i]);
        for (int j = 0; j < LIN_REPS; j++) {
            for (int k = 0; k < NTRU_WIDTH; k++) {
                t0 = y[i][j][k];
                t0.invntt_pow_invphi();
                serial::put_gauss(pass, t0, NTRU_SIGMA_C);
                t0 = w[i][j][k];
                t0.invntt_pow_invphi();
                serial::put_gauss(pass, t0, NTRU_SIGMA_C);
                t0 = _y[i][j][k];
                t0.invntt_pow_invphi();
                serial::put_gauss(pass, t0, NTRU_SIGMA_C);
            }
        }
        pass.put(0, 8 * BLAKE3_OUT_LEN);        /* the linear proof's hash */
        serial::put_uniform(once, pcom[i].c1);
        serial::put_uniform(once, pcom[i].c2[0]);
    }

    size_t per_pass = pass.bytes();
    size_t first = once.bytes() + pismall_const_bytes(cst)
            + pibnd_short_bytes(bnd);
    size_t total = SHUFFLE_REPS * per_pass + first;

    printf("\n** Proof size, measured, at MSGS = %d:\n\n", (int) MSGS);
    printf("  a pass                                = %8.1f KB/vote\n",
           per_pass / 1024.0 / MSGS);
    printf("  three passes                          = %8.1f KB/vote\n",
           SHUFFLE_REPS * per_pass / 1024.0 / MSGS);
    printf("  P_i, Pi_SMALL and Pi_BND, sent once   = %8.1f KB/vote\n",
           first / 1024.0 / MSGS);
    printf("    of which Pi_SMALL                   = %8.1f KB/vote\n",
           pismall_const_bytes(cst) / 1024.0 / MSGS);
    printf("    of which Pi_BND                     = %8.1f KB/vote\n",
           pibnd_short_bytes(bnd) / 1024.0 / MSGS);
    printf("  TOTAL                                 = %8.1f KB/vote\n",
           total / 1024.0 / MSGS);
}

static void microbench() {
    params::poly_q alpha[2] = {nfl::uniform(), nfl::uniform()};

    alpha[0].ntt_pow_phi();
    alpha[1].ntt_pow_phi();

    BENCH_BEGIN("Polynomial addition")
        {
            BENCH_ADD(alpha[0] = alpha[0] + alpha[1]);
        }
    BENCH_END;

    BENCH_BEGIN("Polynomial multiplication")
        {
            BENCH_ADD(alpha[0] = alpha[0] * alpha[1]);
        }
    BENCH_END;

    BENCH_BEGIN("Polynomial inverse")
        {
            BENCH_ADD(util::invert(alpha[1], alpha[0]));
        }
    BENCH_END;
}

static void bench() {
    comkey_t key;
    vector<params::poly_q> m(MSGS), _m(MSGS), sigma(MSGS);
    params::poly_q y[LIN_REPS][NTRU_WIDTH], w[LIN_REPS][NTRU_WIDTH];
    params::poly_q _y[LIN_REPS][NTRU_WIDTH];
    params::poly_q coef[3];
    uint8_t h[BLAKE3_OUT_LEN];

    /* Generate commitment key-> */
    bdlop_keygen(key);
    for (int i = 0; i < MSGS; i++) {
        m[i] = nfl::ZO_dist();
        r[i].resize(NTRU_WIDTH);
        bdlop_sample_rand(r[i]);
        bdlop_commit(com[i], {m[i]}, key, r[i]);
    }

    /* Prover shuffles messages (only a circular shift for simplicity). */
    for (int i = 0; i < MSGS; i++) {
        _m[i] = m[(i + 1) % MSGS];
        index_scalar(sigma[i], (i + 1) % MSGS);
    }

    for (int i = 0; i < 3; i++) {
        coef[i] = nfl::ZO_dist();
        coef[i].ntt_pow_phi();
    }
    params::poly_q beta[LIN_REPS];
    BENCH_BEGIN("linear challenges")
        {
            BENCH_ADD(lin_chal(beta, h));
        }
    BENCH_END;

    BENCH_BEGIN("linear proof")
        {
            BENCH_ADD(lin_prover(y, w, _y, h, com[0], com[1], com[2], coef,
                                 key, r[0], r[1], r[2]));
        }
    BENCH_END;

    BENCH_BEGIN("linear verifier")
        {
            BENCH_ADD(lin_verifier(y, w, _y, h, com[0], com[1], com[2], coef,
                                   key));
        }
    BENCH_END;

    BENCH_SMALL("shuffle-proof (N messages)", run(com, m, _m, sigma, key, r));
    BENCH_SMALL("shuffle proof (only proof)", run2(com, m, _m, sigma, key, r));
}

int main(int argc, char *argv[]) {
    shuffle_alloc();

    printf("\n** Tests for lattice-based shuffle proof:\n\n");
    test();

    proof_size();

    printf("\n** Microbenchmarks for polynomial arithmetic:\n\n");
    microbench();

    printf("\n** Benchmarks for lattice-based shuffle proof:\n\n");
    bench();

    shuffle_free();
}

#endif