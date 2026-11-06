/**
 * @file
 *
 * The mix-net end to end, with MSGS voters, MIXERS mix servers and
 * NTRU_PARTIES trustees, as the paper puts the pieces together:
 *
 *   1. Key generation: an NTRU key pair, its secret key additively shared
 *      among the trustees (ntru_keyshare, a dealer, as the repository does),
 *      and each share dk_j committed to and published as [[dk_j]].
 *   2. Voting: each voter encrypts its vote, X^j for one of NCAND candidates,
 *      and proves the ballot well formed (src/ntru_ballot.c, on LaZer): an
 *      encryption with short randomness of X^j or of 0, bound to the election
 *      and the voter. The board checks every proof.
 *   3. Mixing, by each server in turn: re-encrypt every ciphertext c_i as
 *      c_i + E_i with E_i = p (h s' + e') a fresh encryption of zero, publish
 *      a commitment to E_i and prove, with one amortized Pi_SMALL over all of
 *      them, that each opens to such an encryption with ternary s', e' (Figure
 *      5 of the paper; pismall.h, pismall_mix_*). The verifier adds each input
 *      c_i into the commitment to E_i itself, which makes it a commitment to
 *      the re-encryption; the server publishes the re-encryptions permuted,
 *      with a proof of shuffle of known values over those commitments. The
 *      next server takes the published list as input.
 *   4. Decryption: each trustee publishes its partial decryption
 *      ds_ij = dk_j c_i + p E_ij of every ciphertext of the last list, with
 *      noise drowning, a commitment to each E_ij, a linear proof per
 *      ciphertext that the openings of [[dk_j]] and [[E_ij]] satisfy that
 *      equation, and one exact Pi_Bnd that every ||E_ij||_inf <= B_Drown
 *      (Figure 6 of the paper; pismall.h, pismall_dec_*). Anyone checks the
 *      proofs, combines the shares into the plaintexts and tallies.
 *
 * Then the ballots, the mixing and the decryption are attacked: a ballot proof
 * moved to another voter or kept for a changed ciphertext, and a ballot for two
 * candidates, must be refused; a server that changes an output, replaces a
 * ballot with one of its own, or commits to something other than an encryption
 * of zero must not get its proofs accepted; and a trustee whose partial
 * decryption is wrong, or whose noise is out of bounds, must not get its proof
 * of decryption accepted.
 *
 * The proof of shuffle is internal to ntru_shuffle.cpp, so this file includes
 * it; its own tests are behind MAIN, which is left undefined here. Its prover
 * and verifier run together, in run().
 */

#include "ntru_shuffle.cpp"
#include "ntru_ballot.h"

static_assert(NTRU_BALLOT_DEG == NTRU_DEGREE && NTRU_BALLOT_Q == NTRU_PRIMEQ,
		"the ballot proof is for this ring");

/* The distributed NTRU of src/ntru.cpp that common.h does not declare. */
void ntru_keyshare(params::poly_q s[], size_t shares, params::poly_q & sk);
void ntru_add(params::poly_q & c, params::poly_q & c1, params::poly_q & c2);
void ntru_distdec(params::poly_q & dsj, params::poly_q & ci, params::poly_q & dkj);
void ntru_distdec_noise(params::poly_q & dsj, params::poly_q & Ej,
		params::poly_q & ci, params::poly_q & dkj);
void ntru_comb(params::poly_p & m, params::poly_q c, params::poly_q dsj[],
		size_t shares);

/* Mix servers. The decryption bounds in common.h were set for the noise of 4
 * servers' re-encryptions, so fewer are fine and more need them recomputed. */
#ifndef MIXERS
#define MIXERS 		4
#endif
#if MIXERS < 1 || MIXERS > 4
#error "ntru_voting_impl: the decryption bounds allow 1 to 4 mix servers (MIXERS)"
#endif
/* Candidates: a vote for candidate j is X^j. */
#ifndef NCAND
#define NCAND 		8
#endif

/* A uniform integer in [0, n), from the operating system. */
static uint32_t uniform_below(uint32_t n) {
	uint32_t x, lim = UINT32_MAX - UINT32_MAX % n;
	do {
		if (getrandom(&x, sizeof(x), 0) != sizeof(x)) {
			fprintf(stderr, "ERROR: could not read entropy\n");
			abort();
		}
	} while (x >= lim);
	return x % n;
}

/* The coefficients of a, centred mod q, as the ballot proof takes them; ntt
 * says whether a is in the NTT domain. */
static void to_i64(int64_t out[NTRU_DEGREE], const params::poly_q & a, bool ntt) {
	params::poly_q b = a;
	std::array < mpz_t, NTRU_DEGREE > c;
	mpz_t half;

	if (ntt) {
		b.invntt_pow_invphi();
	}
	for (size_t i = 0; i < NTRU_DEGREE; i++) {
		mpz_init2(c[i], params::poly_q::bits_in_moduli_product() << 2);
	}
	mpz_init(half);
	mpz_fdiv_q_2exp(half, params::poly_q::moduli_product(), 1);
	b.poly2mpz(c);
	for (size_t i = 0; i < NTRU_DEGREE; i++) {
		util::center(c[i], c[i], params::poly_q::moduli_product(), half);
		out[i] = mpz_get_si(c[i]);
		mpz_clear(c[i]);
	}
	mpz_clear(half);
}

/* The context a ballot proof is bound to: the election and the voter. */
#define CTX_BYTES 	(16 + 16 + 4)
static void ballot_ctx(uint8_t ctx[CTX_BYTES], const uint8_t eid[16], int voter) {
	memcpy(ctx, "ntru_voting/vote", 16);
	memcpy(ctx + 16, eid, 16);
	for (int b = 0; b < 4; b++) {
		ctx[32 + b] = (uint8_t) ((uint32_t) voter >> (8 * b));
	}
}

/* The plaintext X^0 + X^1, in the coefficient domain: binary, but two votes. */
static void make_two_votes(params::poly_p & m) {
	std::array < mpz_t, NTRU_DEGREE > c;

	for (size_t i = 0; i < NTRU_DEGREE; i++) {
		mpz_init_set_ui(c[i], i < 2);
	}
	m.mpz2poly(c);
	for (size_t i = 0; i < NTRU_DEGREE; i++) {
		mpz_clear(c[i]);
	}
}

/* The vote X^j, in the coefficient domain as ntru_encrypt takes it. */
static void make_vote(params::poly_p & m, int j) {
	std::array < mpz_t, NTRU_DEGREE > c;

	for (size_t i = 0; i < NTRU_DEGREE; i++) {
		mpz_init_set_ui(c[i], (int) i == j);
	}
	m.mpz2poly(c);
	for (size_t i = 0; i < NTRU_DEGREE; i++) {
		mpz_clear(c[i]);
	}
}

/* The candidate a plaintext votes for, or -1 if it is not X^j, j < NCAND. */
static int candidate(params::poly_p & m) {
	std::array < mpz_t, NTRU_DEGREE > c;
	int j = -1, ok = 1;

	for (size_t i = 0; i < NTRU_DEGREE; i++) {
		mpz_init(c[i]);
	}
	m.poly2mpz(c);
	for (size_t i = 0; i < NTRU_DEGREE && ok; i++) {
		if (mpz_cmp_ui(c[i], 1) == 0 && (int) i < NCAND && j < 0) {
			j = i;
		} else if (mpz_sgn(c[i]) != 0) {
			ok = 0;
		}
	}
	for (size_t i = 0; i < NTRU_DEGREE; i++) {
		mpz_clear(c[i]);
	}
	return ok ? j : -1;
}

/* A ciphertext in the coefficient domain, the form the commitments and the
 * proof of shuffle take messages in. */
static params::poly_q as_message(params::poly_q & c) {
	params::poly_q m = c;

	m.invntt_pow_invphi();
	return m;
}

/* --- The trustees' proof of correct decryption ----------------------------
 *
 * Trustee j has its key share dk_j committed as S_j = [[dk_j]] at key
 * generation. For the i-th ciphertext c_i of the last list it publishes its
 * partial decryption ds_ij = dk_j c_i + p E_ij, a commitment Y_ij = [[E_ij]] to
 * the drowning noise, and the proof below that the openings of S_j and Y_ij
 * satisfy c_i s + p E = ds_ij: Pi_Lin of Figure 6 of the paper, which writes it
 * as [[E_ij - p^-1 ds_ij]] = -p^-1 c_i [[dk_j]]. Its proof that every E_ij is
 * bounded is one exact Pi_Bnd over the Y_ij (pismall_dec_prove).
 *
 * It is the linear proof of the proof of shuffle (lin_prover) with two
 * openings instead of three and this relation, under the same NTRU_SIGMA_C,
 * the same rejection sampling over all the openings at once, and LIN_REPS
 * repetitions against challenges from one hash.
 */
#define DLIN_TRIES  256
/* A ring element as the hashes absorb it: one 64-bit word a coefficient, as
 * ntru_shuffle.cpp's own hashes take it, which is all of it at q < 2^64. */
#define POLY_BYTES  (8 * NTRU_DEGREE)
static_assert(POLY_BYTES == sizeof(params::poly_q::value_type)
		* params::poly_q::nmoduli * params::poly_q::degree,
		"the hashes absorb a whole ring element");

static void dlin_hash(uint8_t h[BLAKE3_OUT_LEN], comkey_t & key, commit_t & X,
		commit_t & Y, params::poly_q & c, params::poly_q & ds,
		params::poly_q w[LIN_REPS], params::poly_q _w[LIN_REPS],
		params::poly_q v[LIN_REPS], uint32_t trustee, uint32_t index) {
	static const char label[] = "ntru_voting/ddec/";
	blake3_hasher hasher;

	blake3_hasher_init(&hasher);
	blake3_hasher_update(&hasher, (const uint8_t *)label, sizeof(label) - 1);
	blake3_hasher_update(&hasher, (const uint8_t *)&trustee, sizeof(trustee));
	blake3_hasher_update(&hasher, (const uint8_t *)&index, sizeof(index));
	for (int k = 0; k < NTRU_WIDTH - NTRU_HEIGHT; k++) {
		blake3_hasher_update(&hasher, (const uint8_t *)key.A1[0][k].data(),
				POLY_BYTES);
	}
	for (int k = 0; k < NTRU_WIDTH; k++) {
		blake3_hasher_update(&hasher, (const uint8_t *)key.A2[0][k].data(),
				POLY_BYTES);
	}
	blake3_hasher_update(&hasher, (const uint8_t *)X.c1.data(), POLY_BYTES);
	blake3_hasher_update(&hasher, (const uint8_t *)X.c2[0].data(), POLY_BYTES);
	blake3_hasher_update(&hasher, (const uint8_t *)Y.c1.data(), POLY_BYTES);
	blake3_hasher_update(&hasher, (const uint8_t *)Y.c2[0].data(), POLY_BYTES);
	blake3_hasher_update(&hasher, (const uint8_t *)c.data(), POLY_BYTES);
	blake3_hasher_update(&hasher, (const uint8_t *)ds.data(), POLY_BYTES);
	for (int j = 0; j < LIN_REPS; j++) {
		blake3_hasher_update(&hasher, (const uint8_t *)w[j].data(), POLY_BYTES);
		blake3_hasher_update(&hasher, (const uint8_t *)_w[j].data(), POLY_BYTES);
		blake3_hasher_update(&hasher, (const uint8_t *)v[j].data(), POLY_BYTES);
	}
	blake3_hasher_finalize(&hasher, h, BLAKE3_OUT_LEN);
}

/* A1 z, the first row of a commitment equation, for a response z. */
static params::poly_q dlin_row0(comkey_t & key, params::poly_q z[NTRU_WIDTH]) {
	params::poly_q a = z[0];

	for (int k = 0; k < NTRU_WIDTH - NTRU_HEIGHT; k++) {
		a = a + key.A1[0][k] * z[k + NTRU_HEIGHT];
	}
	return a;
}

/* A2[0] z, the second row less the message. */
static params::poly_q dlin_row1(comkey_t & key, params::poly_q z[NTRU_WIDTH]) {
	params::poly_q a = 0;

	for (int k = 0; k < NTRU_WIDTH; k++) {
		a = a + key.A2[0][k] * z[k];
	}
	return a;
}

/* Prove that the openings of X = [[s]] (randomness rs) and Y = [[E]]
 * (randomness re) satisfy c s + p E = ds. Returns 0 if rejection sampling did
 * not succeed within DLIN_TRIES, in which case nothing may be published. */
static int dlin_prove(params::poly_q z[LIN_REPS][NTRU_WIDTH],
		params::poly_q _z[LIN_REPS][NTRU_WIDTH], uint8_t h[BLAKE3_OUT_LEN],
		commit_t & X, commit_t & Y, params::poly_q & c, params::poly_q & ds,
		comkey_t & key, vector < params::poly_q > &rs,
		vector < params::poly_q > &re, uint32_t trustee, uint32_t index) {
	params::poly_q beta[LIN_REPS], w[LIN_REPS], _w[LIN_REPS], v[LIN_REPS];
	params::poly_q tmp[NTRU_WIDTH], _tmp[NTRU_WIDTH], p = NTRU_PRIMEP;
	int64_t coeffs[params::poly_q::degree];
	long double dot, norm;
	int rej, tries = 0;

	p.ntt_pow_phi();
	do {
		for (int j = 0; j < LIN_REPS; j++) {
			for (int i = 0; i < NTRU_WIDTH; i++) {
				for (size_t k = 0; k < params::poly_q::degree; k++) {
					coeffs[k] = sample_z(0.0, NTRU_SIGMA_C);
				}
				util::set_signed(z[j][i], coeffs);
				z[j][i].ntt_pow_phi();
				for (size_t k = 0; k < params::poly_q::degree; k++) {
					coeffs[k] = sample_z(0.0, NTRU_SIGMA_C);
				}
				util::set_signed(_z[j][i], coeffs);
				_z[j][i].ntt_pow_phi();
			}
			w[j] = dlin_row0(key, z[j]);
			_w[j] = dlin_row0(key, _z[j]);
			v[j] = c * dlin_row1(key, z[j]) + p * dlin_row1(key, _z[j]);
		}

		dlin_hash(h, key, X, Y, c, ds, w, _w, v, trustee, index);
		lin_chal(beta, h);

		dot = 0;
		norm = 0;
		for (int j = 0; j < LIN_REPS; j++) {
			for (int i = 0; i < NTRU_WIDTH; i++) {
				tmp[i] = beta[j] * rs[i];
				_tmp[i] = beta[j] * re[i];
				z[j][i] = z[j][i] + tmp[i];
				_z[j][i] = _z[j][i] + _tmp[i];
			}
			rej_accum(dot, norm, z[j], tmp);
			rej_accum(dot, norm, _z[j], _tmp);
		}
		rej = rej_decide(dot, norm, NTRU_SIGMA_C * NTRU_SIGMA_C);
	} while (rej && ++tries < DLIN_TRIES);

	return !rej;
}

static int dlin_verify(params::poly_q z[LIN_REPS][NTRU_WIDTH],
		params::poly_q _z[LIN_REPS][NTRU_WIDTH], uint8_t h[BLAKE3_OUT_LEN],
		commit_t & X, commit_t & Y, params::poly_q & c, params::poly_q & ds,
		comkey_t & key, uint32_t trustee, uint32_t index) {
	params::poly_q beta[LIN_REPS], w[LIN_REPS], _w[LIN_REPS], v[LIN_REPS];
	params::poly_q a, p = NTRU_PRIMEP;
	uint8_t h2[BLAKE3_OUT_LEN];
	int result = 1;

	p.ntt_pow_phi();
	lin_chal(beta, h);
	for (int j = 0; j < LIN_REPS; j++) {
		for (int i = 0; i < NTRU_WIDTH; i++) {
			a = z[j][i];
			a.invntt_pow_invphi();
			result &= bdlop_test_norm(a, NTRU_SIGMA_C * NTRU_SIGMA_C);
			a = _z[j][i];
			a.invntt_pow_invphi();
			result &= bdlop_test_norm(a, NTRU_SIGMA_C * NTRU_SIGMA_C);
		}
		w[j] = dlin_row0(key, z[j]) - beta[j] * X.c1;
		_w[j] = dlin_row0(key, _z[j]) - beta[j] * Y.c1;
		a = c * X.c2[0] + p * Y.c2[0] - ds;
		v[j] = c * dlin_row1(key, z[j]) + p * dlin_row1(key, _z[j])
				- beta[j] * a;
	}
	dlin_hash(h2, key, X, Y, c, ds, w, _w, v, trustee, index);
	result &= (memcmp(h, h2, BLAKE3_OUT_LEN) == 0);

	return result;
}

/* Commit to a single message m, in the coefficient domain, under fresh
 * randomness. */
static void commit_one(commit_t & cm, vector < params::poly_q > &rc,
		const params::poly_q & m, comkey_t & key) {
	rc.resize(NTRU_WIDTH);
	bdlop_sample_rand(rc);
	bdlop_commit(cm, {m}, key, rc);
}

/* What a mix server publishes besides its output list: the commitments to the
 * encryptions of zero E_i it added, and the proof that each is one. The
 * randomness of the E_i is its witness. */
static commit_t ecom[MSGS];
static params::poly_q es_[MSGS], ee_[MSGS];

/* One mix server: from the list in, compute the re-encryptions, commit to the
 * encryptions of zero E_i into ecom[], and leave in out the re-encryptions
 * permuted by pi, out[i] = c_pi(i) + E_pi(i). The randomness of the
 * commitments goes to ntru_shuffle.cpp's r[], the messages and the permutation
 * elements to m, _m and sigma, ready for run(); com[] is left for the verifier
 * to build (verifier_commitments). Returns 0 if a commitment built
 * homomorphically differs from a direct one. */
static int mix(params::poly_q out[MSGS], params::poly_q in[MSGS],
		vector < params::poly_q > &m, vector < params::poly_q > &_m,
		vector < params::poly_q > &sigma, params::poly_q & pk,
		comkey_t & key) {
	static params::poly_q re[MSGS];
	params::poly_p zero = 0;
	int pi[MSGS], ok = 1;

	for (int i = 0; i < MSGS; i++) {
		params::poly_q e;
		commit_t direct, sum;

		/* E_i, the re-encryption, and the commitment to E_i. */
		ntru_encrypt_rand(e, pk, zero, es_[i], ee_[i]);
		ntru_add(re[i], in[i], e);
		r[i].resize(NTRU_WIDTH);
		bdlop_sample_rand(r[i]);
		bdlop_commit(ecom[i], {as_message(e)}, key, r[i]);
		m[i] = as_message(re[i]);

		/* + c_i: a commitment to c_i + E_i under the same randomness. */
		sum = ecom[i];
		sum.c2[0] = sum.c2[0] + in[i];
		bdlop_commit(direct, {m[i]}, key, r[i]);
		ok &= util::equal(direct.c1, sum.c1);
		ok &= util::equal(direct.c2[0], sum.c2[0]);
	}

	/* A uniform permutation, and sigma_i = g(pi(i)). */
	for (int i = 0; i < MSGS; i++) {
		pi[i] = i;
	}
	for (int i = MSGS - 1; i > 0; i--) {
		int j = uniform_below(i + 1), x = pi[i];
		pi[i] = pi[j];
		pi[j] = x;
	}
	for (int i = 0; i < MSGS; i++) {
		out[i] = re[pi[i]];
		_m[i] = m[pi[i]];
		index_scalar(sigma[i], pi[i]);
	}
	return ok;
}

/* The verifier's side of a mix: from the input list and the published
 * commitments to the E_i, the commitments to the re-encryptions c_i + E_i that
 * the proof of shuffle is about, into ntru_shuffle.cpp's com[]. Nothing in it
 * comes from the mix server but ecom[], which the proof of re-encryption
 * covers. */
static void verifier_commitments(params::poly_q in[MSGS]) {
	for (int i = 0; i < MSGS; i++) {
		com[i] = ecom[i];
		com[i].c2[0] = com[i].c2[0] + in[i];
	}
}

/* One mix server end to end: mix, prove the re-encryptions, have them
 * checked, the commitments rebuilt from public data and the proof of shuffle
 * run. The proof of re-encryption's time and size are added to the totals. */
static double t_remix, t_rr_prove, t_rr_verify;
static size_t rr_bytes;

static int mix_and_prove(params::poly_q out[MSGS], params::poly_q in[MSGS],
		vector < params::poly_q > &m, vector < params::poly_q > &_m,
		vector < params::poly_q > &sigma, params::poly_q & pk, comkey_t & key,
		int &commit_ok, int &rr_ok) {
	pismall_mix_t *pr;
	serial::bits b;
	double t0;

	t0 = shuffle_now();
	commit_ok &= mix(out, in, m, _m, sigma, pk, key);
	t_remix += shuffle_now() - t0;
	t0 = shuffle_now();
	pr = pismall_mix_prove(key, pk, ecom, r, es_, ee_, MSGS);
	t_rr_prove += shuffle_now() - t0;

	t0 = shuffle_now();
	rr_ok &= pismall_mix_verify(pr, key, pk, ecom, MSGS);
	verifier_commitments(in);
	t_rr_verify += shuffle_now() - t0;

	for (int i = 0; i < MSGS; i++) {
		serial::put_uniform(b, ecom[i].c1);
		serial::put_uniform(b, ecom[i].c2[0]);
	}
	rr_bytes += pismall_mix_bytes(pr) + b.bytes();
	pismall_mix_free(pr);

	return run(com, m, _m, sigma, key, r);
}

static int cmp_int(const void *a, const void *b) {
	return *(const int *) a - *(const int *) b;
}

static void test() {
	static comkey_t key;
	static params::poly_q pk, sk, share[NTRU_PARTIES], part[NTRU_PARTIES];
	static params::poly_q list[MIXERS + 1][MSGS];
	static params::poly_p vote[MSGS], plain[MSGS];
	vector < params::poly_q > m(MSGS), _m(MSGS), sigma(MSGS);
	int votes[MSGS], tally[MSGS], count[NCAND] = { };
	int commit_ok = 1, shuffle_ok = 1, valid = 1, cast_ok = 1, board_ok = 1;
	int rr_ok = 1, dec_ok = 1, dlin_ok = 1, dbnd_ok = 1;
	/* The trustees' commitments to their key shares, and what each publishes
	 * for the decryption: shares DS, commitments Y to the noise E, and their
	 * randomness ry. One trustee's E, Y and ry are live at a time. */
	static commit_t scom[NTRU_PARTIES], Y[MSGS];
	static vector < params::poly_q > srand[NTRU_PARTIES], ry[MSGS];
	static params::poly_q DS[NTRU_PARTIES][MSGS], E[MSGS];
	static params::poly_q dz[LIN_REPS][NTRU_WIDTH], d_z[LIN_REPS][NTRU_WIDTH];
	uint8_t dh[BLAKE3_OUT_LEN];
	size_t share_bytes = 0, dproof_bytes = 0;
	/* The voters' ballot proofs, and the ring elements they take. */
	static std::vector < uint8_t > proof[MSGS];
	static int64_t h64[NTRU_DEGREE], c64[NTRU_DEGREE], s64[NTRU_DEGREE],
			e64[NTRU_DEGREE], m64[NTRU_DEGREE];
	params::poly_q rs, re, two;
	params::poly_p v2;
	uint8_t eid[16], ctx[CTX_BYTES];
	size_t len, proof_bytes = 0;
	/* Wall-clock times of the phases, reported at the end; the attack tests
	 * below run the shuffle again and are not counted. */
	double t0, t_key, t_vote, t_board = 0, t_prove, t_verify, t_shared,
			t_dprove = 0, t_dverify = 0, t_comb;

	t0 = shuffle_now();
	bdlop_keygen(key);
	ntru_keygen(pk, sk);
	ntru_keyshare(share, NTRU_PARTIES, sk);
	for (int j = 0; j < NTRU_PARTIES; j++) {
		params::poly_q sj = share[j];

		sj.invntt_pow_invphi();
		commit_one(scom[j], srand[j], sj, key);
	}
	t_key = shuffle_now() - t0;
	ntru_ballot_setup();
	to_i64(h64, pk, true);
	if (getrandom(eid, sizeof(eid), 0) != sizeof(eid)) {
		fprintf(stderr, "ERROR: could not read entropy\n");
		abort();
	}

	/* Voting. The votes are the test oracle, kept apart from what the mix
	 * servers and the trustees use. Each voter proves its ballot is X^j or 0
	 * under short randomness, bound to this election and to the voter. */
	t0 = shuffle_now();
	for (int i = 0; i < MSGS; i++) {
		votes[i] = uniform_below(NCAND);
		make_vote(vote[i], votes[i]);
		ntru_encrypt_rand(list[0][i], pk, vote[i], rs, re);
		to_i64(c64, list[0][i], true);
		to_i64(s64, rs, false);
		to_i64(e64, re, false);
		memset(m64, 0, sizeof(m64));
		m64[votes[i]] = 1;
		ballot_ctx(ctx, eid, i);
		proof[i].resize(ntru_ballot_proof_len());
		cast_ok &= ntru_ballot_prove(proof[i].data(), &len, c64, h64, s64, e64,
				m64, ctx, sizeof(ctx));
		proof[i].resize(len);
		proof_bytes += len;
	}
	t_vote = shuffle_now() - t0;

	TEST_ONCE("every voter proves its ballot") {
		TEST_ASSERT(cast_ok, end);
	} TEST_END;

	TEST_ONCE("the board accepts every voter's ballot proof") {
		t0 = shuffle_now();
		for (int i = 0; i < MSGS; i++) {
			to_i64(c64, list[0][i], true);
			ballot_ctx(ctx, eid, i);
			board_ok &= ntru_ballot_verify(proof[i].data(), proof[i].size(),
					c64, h64, ctx, sizeof(ctx));
		}
		t_board = shuffle_now() - t0;
		TEST_ASSERT(board_ok, end);
	} TEST_END;

	TEST_ONCE("a ballot proof does not verify for another voter") {
		to_i64(c64, list[0][0], true);
		ballot_ctx(ctx, eid, 1);
		TEST_ASSERT(ntru_ballot_verify(proof[0].data(), proof[0].size(), c64,
				h64, ctx, sizeof(ctx)) == 0, end);
	} TEST_END;

	TEST_ONCE("a ballot changed after its proof is rejected") {
		/* c + 2: the same randomness, now an encryption of m + 2. */
		to_i64(c64, list[0][0], true);
		c64[0] += 2;
		if (c64[0] > NTRU_BALLOT_Q / 2) {
			c64[0] -= NTRU_BALLOT_Q;
		}
		ballot_ctx(ctx, eid, 0);
		TEST_ASSERT(ntru_ballot_verify(proof[0].data(), proof[0].size(), c64,
				h64, ctx, sizeof(ctx)) == 0, end);
	} TEST_END;

	TEST_ONCE("a ballot for two candidates cannot be proven") {
		std::vector < uint8_t > pf(ntru_ballot_proof_len());

		make_two_votes(v2);
		ntru_encrypt_rand(two, pk, v2, rs, re);
		to_i64(c64, two, true);
		to_i64(s64, rs, false);
		to_i64(e64, re, false);
		memset(m64, 0, sizeof(m64));
		m64[0] = m64[1] = 1;
		ballot_ctx(ctx, eid, 0);
		TEST_ASSERT(ntru_ballot_prove(pf.data(), &len, c64, h64, s64, e64, m64,
				ctx, sizeof(ctx)) == 0, end);
	} TEST_END;

	/* Mixing: server s takes list[s] and publishes list[s + 1]. */
	for (int srv = 0; srv < MIXERS; srv++) {
		shuffle_ok &= mix_and_prove(list[srv + 1], list[srv], m, _m, sigma, pk,
				key, commit_ok, rr_ok);
	}
	t_prove = shuffle_t_prove;
	t_verify = shuffle_t_verify;
	t_shared = shuffle_t_shared;

	TEST_ONCE("every commitment to a re-encryption is the homomorphic one") {
		TEST_ASSERT(commit_ok, end);
	} TEST_END;

	TEST_ONCE("every mix server's proof of re-encryption verifies") {
		TEST_ASSERT(rr_ok, end);
	} TEST_END;

	TEST_ONCE("every mix server's proof of shuffle verifies") {
		TEST_ASSERT(shuffle_ok, end);
	} TEST_END;

	/* Decryption. Each trustee in turn publishes its partial decryption of
	 * every ciphertext of the last list, a commitment to each drowning noise
	 * and a linear proof per ciphertext, then one exact Pi_Bnd over all of its
	 * noise. A linear proof is checked as soon as it is produced, so only one
	 * is ever live. */
	for (int j = 0; j < NTRU_PARTIES; j++) {
		serial::bits b, sb;
		pismall_dec_t *bp;

		for (int i = 0; i < MSGS; i++) {
			params::poly_q & c = list[MIXERS][i];

			t0 = shuffle_now();
			ntru_distdec_noise(DS[j][i], E[i], c, share[j]);
			commit_one(Y[i], ry[i], E[i], key);
			dec_ok &= dlin_prove(dz, d_z, dh, scom[j], Y[i], c, DS[j][i], key,
					srand[j], ry[i], j, i);
			t_dprove += shuffle_now() - t0;

			t0 = shuffle_now();
			dlin_ok &= dlin_verify(dz, d_z, dh, scom[j], Y[i], c, DS[j][i],
					key, j, i);
			t_dverify += shuffle_now() - t0;

			serial::put_uniform(sb, DS[j][i]);
			serial::put_uniform(b, Y[i].c1);
			serial::put_uniform(b, Y[i].c2[0]);
			for (int k = 0; k < LIN_REPS; k++) {
				for (int l = 0; l < NTRU_WIDTH; l++) {
					params::poly_q a = dz[k][l];

					a.invntt_pow_invphi();
					serial::put_gauss(b, a, NTRU_SIGMA_C);
					a = d_z[k][l];
					a.invntt_pow_invphi();
					serial::put_gauss(b, a, NTRU_SIGMA_C);
				}
			}
		}

		t0 = shuffle_now();
		bp = pismall_dec_prove(key, Y, ry, E, MSGS);
		t_dprove += shuffle_now() - t0;
		t0 = shuffle_now();
		dbnd_ok &= pismall_dec_verify(bp, key, Y, MSGS);
		t_dverify += shuffle_now() - t0;

		share_bytes += sb.bytes();
		dproof_bytes += b.bytes() + MSGS * BLAKE3_OUT_LEN + pismall_dec_bytes(bp);
		pismall_dec_free(bp);
	}

	/* Anyone: combine the shares, once every proof has been checked. */
	t0 = shuffle_now();
	for (int i = 0; i < MSGS; i++) {
		for (int j = 0; j < NTRU_PARTIES; j++) {
			part[j] = DS[j][i];
		}
		ntru_comb(plain[i], list[MIXERS][i], part, NTRU_PARTIES);
		tally[i] = candidate(plain[i]);
		valid &= tally[i] >= 0;
	}
	t_comb = shuffle_now() - t0;

	TEST_ONCE("every trustee proves each of its partial decryptions") {
		TEST_ASSERT(dec_ok, end);
	} TEST_END;

	TEST_ONCE("every trustee's linear proofs of decryption verify") {
		TEST_ASSERT(dlin_ok, end);
	} TEST_END;

	TEST_ONCE("every trustee's proof that its noise is bounded verifies") {
		TEST_ASSERT(dbnd_ok, end);
	} TEST_END;

	TEST_ONCE("the decrypted ballots are valid votes") {
		TEST_ASSERT(valid, end);
	} TEST_END;

	TEST_ONCE("the tally is the votes cast") {
		qsort(tally, MSGS, sizeof(int), cmp_int);
		qsort(votes, MSGS, sizeof(int), cmp_int);
		TEST_ASSERT(memcmp(tally, votes, sizeof(votes)) == 0, end);
	} TEST_END;

	TEST_ONCE("a mix server that changes an output is rejected") {
		/* Mix the first list again and add 1 to an output: the outputs are no
		 * longer the committed re-encryptions permuted. */
		params::poly_q one = 1;
		static params::poly_q out[MSGS];

		mix(out, list[0], m, _m, sigma, pk, key);
		verifier_commitments(list[0]);
		_m[0] = _m[0] + one;
		TEST_ASSERT(run(com, m, _m, sigma, key, r) == 0, end);
	} TEST_END;

	TEST_ONCE("a mix server that replaces a ballot is rejected") {
		/* Publish, in place of one output, a fresh encryption of a vote of
		 * the server's choosing. */
		static params::poly_q out[MSGS];
		params::poly_q own;
		params::poly_p v;

		mix(out, list[0], m, _m, sigma, pk, key);
		verifier_commitments(list[0]);
		make_vote(v, NCAND - 1);
		ntru_encrypt(own, pk, v);
		_m[0] = as_message(own);
		TEST_ASSERT(run(com, m, _m, sigma, key, r) == 0, end);
	} TEST_END;

	TEST_ONCE("a mix server that commits to other than a zero is rejected") {
		/* The attack the proof of re-encryption is there for: commit, in
		 * place of E_0, to own - c_0 for an encryption own of a vote of the
		 * server's choosing. The verifier's commitment to c_0 + E_0 is then a
		 * commitment to own, and the proof of shuffle goes through with own
		 * among the outputs; only the proof that E_0 encrypts zero can fail. */
		static params::poly_q out[MSGS];
		params::poly_q own;
		params::poly_p v;
		pismall_mix_t *pr;

		mix(out, list[0], m, _m, sigma, pk, key);
		make_vote(v, NCAND - 1);
		ntru_encrypt(own, pk, v);
		bdlop_commit(ecom[0], {as_message(own) - as_message(list[0][0])}, key,
				r[0]);
		pr = pismall_mix_prove(key, pk, ecom, r, es_, ee_, MSGS);
		TEST_ASSERT(pismall_mix_verify(pr, key, pk, ecom, MSGS) == 0, end);
		pismall_mix_free(pr);
	} TEST_END;

	TEST_ONCE("a trustee whose partial decryption is wrong is rejected") {
		/* ds + 1 for the last trustee's first share, with the proof made for
		 * it from the true witness. */
		params::poly_q one = 1, bad;

		one.ntt_pow_phi();
		bad = DS[NTRU_PARTIES - 1][0] + one;
		dlin_prove(dz, d_z, dh, scom[NTRU_PARTIES - 1], Y[0], list[MIXERS][0],
				bad, key, srand[NTRU_PARTIES - 1], ry[0], NTRU_PARTIES - 1, 0);
		TEST_ASSERT(dlin_verify(dz, d_z, dh, scom[NTRU_PARTIES - 1], Y[0],
				list[MIXERS][0], bad, key, NTRU_PARTIES - 1, 0) == 0, end);
	} TEST_END;

	TEST_ONCE("a trustee whose noise is out of bounds is rejected") {
		/* A share ds = dk c + p E' whose E' has one coefficient at B_Drown + 1:
		 * the linear proof holds, the share being consistent with its
		 * commitment, and only the exact bound can fail. The proof is exact,
		 * so one past the bound is enough. */
		int64_t cf[NTRU_DEGREE] = { };
		params::poly_q ent;
		pismall_dec_t *bp;
		int lin;

		util::centred(cf, E[0]);
		cf[0] = 36028797018963968LL + 1;
		util::set_signed(E[0], cf);
		commit_one(Y[0], ry[0], E[0], key);
		ent = E[0];
		ent.ntt_pow_phi();
		DS[NTRU_PARTIES - 1][0] = share[NTRU_PARTIES - 1] * list[MIXERS][0]
				+ ent + ent;
		dlin_prove(dz, d_z, dh, scom[NTRU_PARTIES - 1], Y[0], list[MIXERS][0],
				DS[NTRU_PARTIES - 1][0], key, srand[NTRU_PARTIES - 1], ry[0],
				NTRU_PARTIES - 1, 0);
		lin = dlin_verify(dz, d_z, dh, scom[NTRU_PARTIES - 1], Y[0],
				list[MIXERS][0], DS[NTRU_PARTIES - 1][0], key,
				NTRU_PARTIES - 1, 0);
		bp = pismall_dec_prove(key, Y, ry, E, MSGS);
		TEST_ASSERT(lin == 1 && pismall_dec_verify(bp, key, Y, MSGS) == 0, end);
		pismall_dec_free(bp);
	} TEST_END;

	for (int i = 0; i < MSGS; i++) {
		int j = candidate(plain[i]);
		if (j >= 0) {
			count[j]++;
		}
	}
	printf("\n    %d voters, %d mix servers, %d trustees; tally:", MSGS,
			MIXERS, NTRU_PARTIES);
	for (int j = 0; j < NCAND; j++) {
		printf(" %d", count[j]);
	}
	printf("\n");
	printf("    ballot proof %.1f KB on average\n", proof_bytes / 1024.0 / MSGS);
	printf("    timing, wall clock: key generation %.2f s; voting (encrypt and "
			"prove) %.2f s, %.2f ms per ballot; board check %.2f s, %.2f ms per "
			"ballot\n", t_key, t_vote, 1e3 * t_vote / MSGS, t_board,
			1e3 * t_board / MSGS);
	printf("    timing, per mix server: re-encryption and commitments %.2f s, "
			"prove %.2f s, verify %.2f s, both (NTT form) %.2f s\n",
			t_remix / MIXERS, t_prove / MIXERS, t_verify / MIXERS,
			t_shared / MIXERS);
	printf("    timing, per mix server: proof of re-encryption, prove %.2f s, "
			"verify %.2f s; %.1f KB per ballot (commitments to the E_i "
			"included)\n", t_rr_prove / MIXERS, t_rr_verify / MIXERS,
			rr_bytes / 1024.0 / MIXERS / MSGS);
	printf("    timing, per trustee: partial decryptions and their proofs %.2f "
			"s, %.2f ms per ballot; verify them %.2f s, %.2f ms per ballot\n",
			t_dprove / NTRU_PARTIES, 1e3 * t_dprove / NTRU_PARTIES / MSGS,
			t_dverify / NTRU_PARTIES, 1e3 * t_dverify / NTRU_PARTIES / MSGS);
	printf("    decryption, per ballot and trustee: share %.1f KB, proof %.1f KB "
			"(commitment to the noise, linear proof, share of Pi_Bnd)\n",
			share_bytes / 1024.0 / NTRU_PARTIES / MSGS,
			dproof_bytes / 1024.0 / NTRU_PARTIES / MSGS);
	printf("    timing: combining the shares %.2f s, %.2f ms per ballot (%d "
			"trustees)\n", t_comb, 1e3 * t_comb / MSGS, NTRU_PARTIES);

  end:
	return;
}

int main(void) {
	setvbuf(stdout, NULL, _IONBF, 0);
	shuffle_alloc();

	printf("\n** End-to-end test of the mix-net:\n\n");
	test();

	shuffle_free();
	return test_failures() != 0;
}
