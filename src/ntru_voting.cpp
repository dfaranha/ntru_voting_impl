/**
 * @file
 *
 * The mix-net end to end, with MSGS voters, MIXERS mix servers and
 * NTRU_PARTIES trustees, as the paper puts the pieces together:
 *
 *   1. Key generation: an NTRU key pair, its secret key additively shared
 *      among the trustees (ntru_keyshare, a dealer, as the repository does).
 *   2. Voting: each voter encrypts its vote, X^j for one of NCAND candidates,
 *      and proves the ballot well formed (src/ntru_ballot.c, on LaZer): an
 *      encryption with short randomness of X^j or of 0, bound to the election
 *      and the voter. The board checks every proof.
 *   3. Mixing, by each server in turn: re-encrypt every ciphertext c_i as
 *      c_i + E_i with E_i a fresh encryption of zero, commit to E_i, and add
 *      c_i into that commitment, which makes it a commitment to the
 *      re-encryption under the same randomness; then publish the
 *      re-encryptions permuted, with a proof of shuffle of known values over
 *      those commitments. The next server takes the published list as input.
 *   4. Decryption: each trustee publishes its partial decryption of every
 *      ciphertext of the last list (with noise drowning), and anyone combines
 *      them into the plaintexts and tallies.
 *
 * Then the ballots and the mixing are attacked: a ballot proof moved to
 * another voter or kept for a changed ciphertext, and a ballot for two
 * candidates, must be refused; a server that changes an output, or replaces a
 * ballot with one of its own, must not get its proof of shuffle accepted.
 *
 * What the repository does not implement is left out, and so is not tested:
 * the proof that each E_i is an encryption of zero with short randomness, and
 * the trustees' proofs of correct decryption.
 * Without the second, the commitments to the E_i are not tied to encryptions
 * of zero; the proof of shuffle checked here is about the commitments.
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

/* One mix server: from the list in, compute the re-encryptions, commit to
 * them through the commitments to the encryptions of zero, and leave in out
 * the re-encryptions permuted by pi, out[i] = c_pi(i) + E_pi(i). The
 * commitments and their randomness go to ntru_shuffle.cpp's com[] and r[], the
 * messages and the permutation elements to m, _m and sigma, ready for run().
 * Returns 0 if a commitment built homomorphically differs from a direct one. */
static int mix(params::poly_q out[MSGS], params::poly_q in[MSGS],
		vector < params::poly_q > &m, vector < params::poly_q > &_m,
		vector < params::poly_q > &sigma, params::poly_q & pk,
		comkey_t & key) {
	static params::poly_q re[MSGS];
	params::poly_p zero = 0;
	int pi[MSGS], ok = 1;

	for (int i = 0; i < MSGS; i++) {
		params::poly_q e;
		commit_t direct;

		/* E_i, the re-encryption, and the commitment to E_i. */
		ntru_encrypt(e, pk, zero);
		ntru_add(re[i], in[i], e);
		r[i].resize(NTRU_WIDTH);
		bdlop_sample_rand(r[i]);
		bdlop_commit(com[i], {as_message(e)}, key, r[i]);
		/* + c_i: a commitment to c_i + E_i under the same randomness. */
		com[i].c2[0] = com[i].c2[0] + in[i];
		m[i] = as_message(re[i]);

		bdlop_commit(direct, {m[i]}, key, r[i]);
		ok &= util::equal(direct.c1, com[i].c1);
		ok &= util::equal(direct.c2[0], com[i].c2[0]);
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
	double t0, t_key, t_vote, t_board = 0, t_mix = 0, t_prove, t_verify,
			t_shared, t_dec;

	t0 = shuffle_now();
	bdlop_keygen(key);
	ntru_keygen(pk, sk);
	ntru_keyshare(share, NTRU_PARTIES, sk);
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
		t0 = shuffle_now();
		commit_ok &= mix(list[srv + 1], list[srv], m, _m, sigma, pk, key);
		t_mix += shuffle_now() - t0;
		shuffle_ok &= run(com, m, _m, sigma, key, r);
	}
	t_prove = shuffle_t_prove;
	t_verify = shuffle_t_verify;
	t_shared = shuffle_t_shared;

	TEST_ONCE("every commitment to a re-encryption is the homomorphic one") {
		TEST_ASSERT(commit_ok, end);
	} TEST_END;

	TEST_ONCE("every mix server's proof of shuffle verifies") {
		TEST_ASSERT(shuffle_ok, end);
	} TEST_END;

	/* Decryption: the trustees' partial decryptions, combined. */
	t0 = shuffle_now();
	for (int i = 0; i < MSGS; i++) {
		for (int j = 0; j < NTRU_PARTIES; j++) {
			ntru_distdec(part[j], list[MIXERS][i], share[j]);
		}
		ntru_comb(plain[i], list[MIXERS][i], part, NTRU_PARTIES);
		tally[i] = candidate(plain[i]);
		valid &= tally[i] >= 0;
	}
	t_dec = shuffle_now() - t0;

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
		make_vote(v, NCAND - 1);
		ntru_encrypt(own, pk, v);
		_m[0] = as_message(own);
		TEST_ASSERT(run(com, m, _m, sigma, key, r) == 0, end);
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
			t_mix / MIXERS, t_prove / MIXERS, t_verify / MIXERS,
			t_shared / MIXERS);
	printf("    timing: decryption %.2f s, %.2f ms per ballot (%d trustees)\n",
			t_dec, 1e3 * t_dec / MSGS, NTRU_PARTIES);

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
