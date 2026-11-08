/**
 * @file
 *
 * The voter's proof that a ballot is well formed, on LaZer's linear proofs: c
 * is an NTRU encryption c = 2 h s + 2 e + m of a vote m = X^(NTRU_BALLOT_STRIDE j)
 * (or of 0) with short randomness (s, e). The proof is bound to a context, such as the
 * election and the voter, so it cannot be moved to another ballot.
 *
 * C, so that the C++ code can call it without compiling LaZer's headers:
 * elements of R_q are passed as their NTRU_BALLOT_DEG coefficients, centred
 * mod NTRU_BALLOT_Q.
 */

#ifndef NTRU_BALLOT_H
#define NTRU_BALLOT_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* The ring the ballots live in: degree and modulus (NTRU_DEGREE and
 * NTRU_PRIMEQ of common.h, which ntru_voting.cpp checks). */
#define NTRU_BALLOT_DEG 	2048
#define NTRU_BALLOT_Q 		576460752303439873LL

/* A vote for candidate j is X^(NTRU_BALLOT_STRIDE j): the proof is stated over
 * LaZer's ring of degree 64, and these are the elements of R_q that lie in
 * one element of it. So there are at most NTRU_BALLOT_MAXCAND candidates. */
#define NTRU_BALLOT_STRIDE 	(NTRU_BALLOT_DEG / 64)
#define NTRU_BALLOT_MAXCAND 64

/* Initialise LaZer; call once before proving or verifying. */
void ntru_ballot_setup(void);

/* An upper bound on the size in bytes of a proof; its encoding varies. */
size_t ntru_ballot_proof_len(void);

/**
 * Prove that c = 2 h s + 2 e + m with s, e ternary and short and
 * m = X^(NTRU_BALLOT_STRIDE j), j < ncand <= NTRU_BALLOT_MAXCAND, or 0, bound to ctx. Refuses (returns 0, no proof) if the witness is not of that
 * form or the equation does not hold.
 *
 * @param[out] proof		- room for ntru_ballot_proof_len() bytes.
 * @param[out] len			- the bytes written, at most that.
 * @return 1 if a proof was made, 0 otherwise.
 */
int ntru_ballot_prove(uint8_t *proof, size_t *len, const int64_t c[],
		const int64_t h[], const int64_t s[], const int64_t e[],
		const int64_t m[], int ncand, const uint8_t *ctx, size_t ctxlen);

/**
 * Verify a ballot proof for c under the public key h, for an election of
 * ncand candidates, and the context ctx.
 *
 * @return 1 if it verifies, 0 otherwise.
 */
int ntru_ballot_verify(const uint8_t *proof, size_t len, const int64_t c[],
		const int64_t h[], int ncand, const uint8_t *ctx, size_t ctxlen);

#ifdef __cplusplus
}
#endif

#endif /* NTRU_BALLOT_H */
