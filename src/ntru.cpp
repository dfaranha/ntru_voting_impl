#include "test.h"
#include "bench.h"
#include "common.h"
#include <sys/random.h>
#include <math.h>
#include <stdlib.h>
#include <gmp.h>
#include "blake3.h"
#include "assert.h"
#include "sample_z_small.h"


void ntru_sample_message(params::poly_p &m) {
    // Same as BGV, but we are going to use different params so created a specific one.
    std::array <mpz_t, NTRU_DEGREE> coeffs;
    uint64_t buf;
    size_t bits_in_moduli_product = params::poly_p::bits_in_moduli_product();
    for (size_t i = 0; i < params::poly_p::degree; i++) {
        mpz_init2(coeffs[i], bits_in_moduli_product << 2);
    }
    for (size_t j = 0; j < params::poly_p::degree; j += 32) {
        ssize_t grret = getrandom(&buf, sizeof(buf), 0);
        if (grret == -1) {
            throw "Could not generate random seed. Check if something is wrong with the system prng.";
        }
        for (size_t k = 0; k < 64; k += 2) {
            mpz_set_ui(coeffs[j + k / 2], (buf >> k) % NTRU_PRIMEP);
        }
    }
    m.mpz2poly(coeffs);
    for (size_t i = 0; i < params::poly_p::degree; i++) {
        mpz_clear(coeffs[i]);
    }
}

/**
 * @brief Computes the multiplicative inverse of a polynomial in a given field.
 *
 * @param inv Output parameter to store the computed inverse polynomial.
 * @param p Input polynomial for which the inverse is to be computed.
 */

/*
 * Test norm of polynomial less than some bound sqrRoot(t^2*sigma^2*degree)
 * */
bool ntru_test_norm(params::poly_q r, double_t sigma_sqr, double_t t) {
    array <mpz_t, params::poly_q::degree> coeffs;
    mpz_t norm, qDivBy2, tmp;
    mpz_inits(norm, qDivBy2, tmp, nullptr);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_init2(coeffs[i], params::poly_q::bits_in_moduli_product() << 2);
    }
    r.poly2mpz(coeffs);
    mpz_fdiv_q_2exp(qDivBy2, params::poly_q::moduli_product(), 1);
    mpz_set_ui(norm, 0);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        util::center(coeffs[i], coeffs[i], params::poly_q::moduli_product(), qDivBy2);
        mpz_mul(tmp, coeffs[i], coeffs[i]);
        mpz_add(norm, norm, tmp);
    }
    double_t bound = t * t * sigma_sqr * params::poly_q::degree;
    int result = mpz_cmp_ui(norm, bound) < 0;
    mpz_clears(norm, qDivBy2, tmp, nullptr);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_clear(coeffs[i]);
    }
    return result;
}

void ntru_keygen(params::poly_q &pk, params::poly_q &sk) {
    params::poly_q f, g, f_inv;
    array <mpz_t, params::poly_q::degree> coeffs_f, coeffs_g, coeffs;
    int ok;

    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_init2(coeffs_f[i], params::poly_q::bits_in_moduli_product() << 2);
        mpz_init2(coeffs_g[i], params::poly_q::bits_in_moduli_product() << 2);
        mpz_init2(coeffs[i], params::poly_q::bits_in_moduli_product() << 2);
    }

    do {
        for (size_t k = 0; k < params::poly_q::degree; k++) {
            int64_t coeff_f, residue;
            /* f = 1 mod p asks for the least non-negative residue. C's % keeps
             * the sign of the dividend, so testing it directly rejected every
             * negative odd coefficient and left f[0] on the positive half. */
            do {
                coeff_f = sample_z(0.0, NTRU_SIGMA);
                residue = ((coeff_f % NTRU_PRIMEP) + NTRU_PRIMEP) % NTRU_PRIMEP;
            } while (residue != (k == 0 ? 1 : 0));
            int64_t coeff_g = sample_z(0.0, NTRU_SIGMA);
            mpz_set_si(coeffs_f[k], coeff_f);
            mpz_set_si(coeffs_g[k], coeff_g);
        }
        f.mpz2poly(coeffs_f);
        g.mpz2poly(coeffs_g);
        /* KeyGen resamples when a norm is too large or when f is not invertible
         * in R_q. The inverse is taken slot by slot, so f has to be in the NTT
         * domain first; it stays there, which is where sk is wanted anyway. */
        ok = ntru_test_norm(f, NTRU_SIGMA * NTRU_SIGMA, 1.058) &&
             ntru_test_norm(g, NTRU_SIGMA * NTRU_SIGMA, 1.058);
        if (ok) {
            f.ntt_pow_phi();
            ok = util::invert(f_inv, f);
        }
    } while (!ok);

    g.ntt_pow_phi();

    pk = g * f_inv;
    sk = f;

    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_clear(coeffs_f[i]);
        mpz_clear(coeffs_g[i]);
        mpz_clear(coeffs[i]);
    }
}

void ntru_keyshare(params::poly_q s[], size_t shares, params::poly_q &sk) {
    params::poly_q t = sk;
    for (size_t i = 1; i < shares; i++) {
        s[i] = nfl::uniform();
        s[i].ntt_pow_phi();
        t = t - s[i];
    }
    s[0] = t;
}

/* As ntru_encrypt, and also return the randomness s and e, in the coefficient
 * domain, for the voter's ballot proof. */
void ntru_encrypt_rand(params::poly_q &c, params::poly_q &pk, params::poly_p &m,
                       params::poly_q &s_out, params::poly_q &e_out) {
    params::poly_q s = nfl::ZO_dist();
    params::poly_q e = nfl::ZO_dist();
    params::poly_q m_;
    std::array <mpz_t, NTRU_DEGREE> coeffs;

    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_init2(coeffs[i], params::poly_q::bits_in_moduli_product() << 2);
    }

    s_out = s;
    e_out = e;
    s.ntt_pow_phi();
    e.ntt_pow_phi();

    m.poly2mpz(coeffs);
    m_.mpz2poly(coeffs);

    m_.ntt_pow_phi();

    c = (pk * s + e) + (pk * s + e) + m_;

    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_clear(coeffs[i]);
    }
}

void ntru_encrypt(params::poly_q &c, params::poly_q &pk, params::poly_p &m) {
    params::poly_q s, e;

    ntru_encrypt_rand(c, pk, m, s, e);
}

void ntru_add(params::poly_q &c, params::poly_q &c1, params::poly_q &c2) {
    c = c1 + c2;
}

void ntru_decrypt(params::poly_p &m, params::poly_q &c, params::poly_q &sk) {
    std::array <mpz_t, NTRU_DEGREE> coeffs;
    params::poly_q t = sk * c;
    mpz_t qDivBy2;

    mpz_init(qDivBy2);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_init2(coeffs[i], params::poly_q::bits_in_moduli_product() << 2);
    }

    mpz_fdiv_q_2exp(qDivBy2, params::poly_q::moduli_product(), 1);
    t.invntt_pow_invphi();
    t.poly2mpz(coeffs);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        util::center(coeffs[i], coeffs[i], params::poly_q::moduli_product(), qDivBy2);
        mpz_mod_ui(coeffs[i], coeffs[i], NTRU_PRIMEP);
    }
    m.mpz2poly(coeffs);

    mpz_clear(qDivBy2);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_clear(coeffs[i]);
    }
}

void ntru_distdec(params::poly_q &dsj, params::poly_q &ci, params::poly_q &dkj) {
    std::array <mpz_t, NTRU_DEGREE> coeffs;
    params::poly_q dsij, Ej;
    mpz_t qDivBy2, bound, span;

    mpz_init(qDivBy2);
    mpz_init(bound);
    mpz_init(span);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_init2(coeffs[i], params::poly_q::bits_in_moduli_product() << 2);
    }

    mpz_fdiv_q_2exp(qDivBy2, params::poly_q::moduli_product(), 1);
    mpz_set_str(bound, NTRU_BOUND_D, 10);
    /* S_B is the set of a with ||a||_inf <= B, so a coefficient is uniform over
     * the 2B + 1 values in [-B, B]. Reducing modulo B alone, as this did, lands
     * in [0, B): half the set, every coefficient non-negative, and twice the
     * statistical distance that the noise drowning is there to bound. */
    mpz_mul_ui(span, bound, 2);
    mpz_add_ui(span, span, 1);

    Ej = nfl::uniform();
    Ej.poly2mpz(coeffs);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        util::center(coeffs[i], coeffs[i], params::poly_q::moduli_product(), qDivBy2);
        mpz_mod(coeffs[i], coeffs[i], span);
        mpz_sub(coeffs[i], coeffs[i], bound);
    }
    Ej.mpz2poly(coeffs);
    Ej.ntt_pow_phi();
    dsij = dkj * ci;
    dsj = dsij;
    for (size_t i = 0; i < NTRU_PRIMEP; i++) {
        dsj = dsj + Ej;
    }

    mpz_clear(qDivBy2);
    mpz_clear(bound);
    mpz_clear(span);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_clear(coeffs[i]);
    }
}

void ntru_comb(params::poly_p &m, params::poly_q c, params::poly_q dsj[], size_t shares) {
    std::array <mpz_t, NTRU_DEGREE> coeffs;
    params::poly_q v;
    mpz_t qDivBy2;

    mpz_init(qDivBy2);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_init2(coeffs[i], params::poly_q::bits_in_moduli_product() << 2);
    }

    mpz_fdiv_q_2exp(qDivBy2, params::poly_q::moduli_product(), 1);
    v = dsj[0];
    for (size_t i = 1; i < shares; i++) {
        v = v + dsj[i];
    }
    v.invntt_pow_invphi();
    v.poly2mpz(coeffs);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        util::center(coeffs[i], coeffs[i], params::poly_q::moduli_product(), qDivBy2);
        mpz_mod_ui(coeffs[i], coeffs[i], NTRU_PRIMEP);
    }
    m.mpz2poly(coeffs);

    mpz_clear(qDivBy2);
    for (size_t i = 0; i < params::poly_q::degree; i++) {
        mpz_clear(coeffs[i]);
    }
}

#ifdef MAIN

static void ntru_test() {

    params::poly_q sk, pk, c1, c2, s[PARTIES], t[PARTIES], acc;
    params::poly_p m, _m;

    ntru_keygen(pk, sk);
    ntru_sample_message(m);

    // Test that NTRU encryption is consistent.
    TEST_BEGIN("NTRU encryption is consistent") {
        ntru_encrypt(c1, pk, m);  // Encrypt the message.
        ntru_decrypt(_m, c1, sk);  // Decrypt the ciphertext.
        TEST_ASSERT(util::equal(m, _m), end);  // Check that the decrypted message matches the original.

        ntru_sample_message(m);  // Sample another message.
        ntru_decrypt(_m, c1, sk);  // Decrypt the previous ciphertext.
        TEST_ASSERT(!util::equal(m, _m), end);  // Check that the decrypted message does not match the new message.

        ntru_encrypt(c1, pk, m);  // Encrypt the new message.
        ntru_keygen(pk, sk);  // Generate a new key pair.
        ntru_decrypt(_m, c1, sk);  // Decrypt the ciphertext with the new secret key.
        TEST_ASSERT(!util::equal(m, _m), end);  // Check that the decryption is not successful with the wrong key.
    }
    TEST_END;
    TEST_BEGIN("NTRU distributed decryption is consistent") {
        ntru_keygen(pk, sk);
        ntru_encrypt(c1, pk, m);
        ntru_keyshare(s, NTRU_PARTIES, sk);
        acc = s[0];
        for (size_t j = 1; j < NTRU_PARTIES; j++) {
            acc = acc + s[j];
        }
        TEST_ASSERT(util::equal(sk, acc), end);
        for (size_t j = 0; j < NTRU_PARTIES; j++) {
            ntru_distdec(t[j], c1, s[j]);
        }
        ntru_comb(_m, c1, t, NTRU_PARTIES);
        TEST_ASSERT(util::equal(m, _m), end);
    }
    TEST_END;

    end:
    return;
}

static void bench() {
    params::poly_q pk, sk, s[NTRU_PARTIES], t[NTRU_PARTIES], acc;
    params::poly_p m, _m;
    params::poly_q c;

    BENCH_SMALL("ntru_keygen", ntru_keygen(pk, sk));

    BENCH_BEGIN("ntru_sample_message")
        {
            BENCH_ADD(ntru_sample_message(m));
        }
    BENCH_END;

    BENCH_BEGIN("ntru_encrypt")
        {
            BENCH_ADD(ntru_encrypt(c, pk, m));
        }
    BENCH_END;

    BENCH_BEGIN("ntru_decrypt")
        {
            ntru_encrypt(c, pk, m);
            BENCH_ADD(ntru_decrypt(_m, c, sk));
        }
    BENCH_END;

    ntru_keyshare(t, NTRU_PARTIES, sk);
    BENCH_BEGIN("ntru_distdec")
        {
            ntru_encrypt(c, pk, m);
            BENCH_ADD(ntru_distdec(t[0], c, s[0]));
        }
    BENCH_END;
    for (size_t i = 1; i < PARTIES; i++) {
        ntru_distdec(t[i], c, s[i]);
    }

    BENCH_BEGIN("ntru_comb")
        {
            BENCH_ADD(ntru_comb(_m, c, t, PARTIES));
        }
    BENCH_END;
}

// Main function to run tests and benchmarks.
int main(int argc, char *arv[]) {
    printf("\n** Tests for NTRU encryption:\n\n");
    ntru_test();

    printf("\n** Benchmarks for NTRU encryption:\n\n");
    bench();

    return 0;
}

#endif
