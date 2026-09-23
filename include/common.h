#include <cstddef>

#include <gmpxx.h>
#include <algorithm>
#include <chrono>
#include <iostream>
#include <memory>
#include <nfl.hpp>
#include <cmath>

#include "bench.h"
#include <sys/random.h>

using namespace std;

#ifndef COMMON_H
#define COMMON_H

/* Number of messages in the shuffle. Overridable: the proof holds all of them
 * in memory. It lives here rather than in src/ntru_shuffle.cpp because the
 * norm proof's short instance is amortized over exactly these commitments and
 * is compiled on its own. */
#ifndef MSGS
#define MSGS        1000
#endif
/* Security level to attain. */
#define LEVEL       128
/* The \infty-norm bound of certain elements: the commitment randomness is
 * ternary, which is the B_Com = 1 of Table 2. */
#define BETA        1
/* Width k of the commitment matrix. */
#define WIDTH        4
/* Height of the commitment matrix. */
#define HEIGHT        1
/* Dimension of the committed messages: how many ring elements a commitment
 * key can carry. The shuffle commits one at a time, but the membership proof
 * of pismall.h commits to the R = HEIGHT + 1 rows of a commitment equation
 * under the same key, so the key needs two rows and the scheme uses the first.
 * Hiding needs WIDTH > HEIGHT + SIZE, which at 4 > 3 still holds. */
#ifndef SIZE
#define SIZE        2
#endif
/* Degree of the irreducible polynomial. */
#define DEGREE      2048//4096
/* Parties that run the distributed decryption protocol. */
#define PARTIES     4
/* Security level for Distributed Decryption. */

/*
 * NTRU DEFINEs
 * */
#define NTRU_PRIMEQ 576460752303439873
#define NTRU_PRIMEP 2
#define NTRU_SIGMA 7.12
#define NTRU_DEGREE 2048
/* B_Drown, the infinity norm of the noise drowning term E_ij. Table 6 of the
 * paper sets B_Drown = 2^sec * (B_Dec / (p * xi_2)) with B_Dec = 262144, so
 * 2^40 * 32768 = 2^55, the value in Table 2. It was 2^57 here, which is the
 * same formula without the xi_2 = 4 decryption servers, and only fits under a
 * modulus three bits larger than the paper's.
 *
 * Correctness wants B_Dec + p * xi_2 * B_Drown <= floor(q/2). At these values
 * that is 2^18 + 2^58 against 288230376151719936, which the 2^18 exceeds by
 * 253952 -- an artefact of Table 2 rounding B_Dec down from 262267 to 2^18.
 * It costs nothing in practice, since B_Dec is a worst case for ||f c||_inf
 * that an honest ciphertext is nowhere near. */
#define NTRU_BOUND_D "36028797018963968"
#define NTRU_PARTIES 4
/* Dimension of the committed messages. */
#ifndef NTRU_SIZE
#define NTRU_SIZE 1
#endif
/* Width k of the commitment matrix. */
#define NTRU_WIDTH 4
/* Height of the commitment matrix. */
#define NTRU_HEIGHT 1

/* Maximum l1-norm kappa of a challenge, and the standard deviation of the masks
 * in the proofs of linear relations. kappa = 14 is the smallest value with
 * |C| = binom(d, kappa) * 2^kappa > 2^lambda at d = 2048, which is 2^131.6.
 *
 * These used to sit beside a second pair, NONZERO = 36 and SIGMA_C = 2^12,
 * inherited unchanged from the ABGS23 codebase this one was forked from, where
 * d is 4096; bdlop.cpp still drew its challenges from them, so ntru_pismall
 * committed under a different instantiation of the same scheme than the
 * shuffle did. Table 6 would put sigma_Com at kappa * B_Com * sqrt(k d) = 1267,
 * a little above the 2^10 below, which is left as the authors wrote it. */
#define NTRU_SIGMA_C (1u << 10)
#define NTRU_NONZERO 14


/* One ring for the whole scheme. Table 2 gives a single q as the "ciphertext
 * and commitment modulus" and a single ring dimension d, so the ciphertexts of
 * the NTRU cryptosystem and the BDLOP commitments live in the same R_q. This
 * was written twice, as params and ntru_params, which read like two rings --
 * and was two rings until the basis in NFLlib was corrected, since one of them
 * named a 62-bit modulus and the other the paper's q. */
static_assert(NTRU_DEGREE == DEGREE, "the scheme has one ring dimension");

namespace params {
    using poly_p = nfl::poly_from_modulus<uint32_t, DEGREE, 30>;
    using poly_q = nfl::poly_from_modulus<uint64_t, DEGREE, 60>;
    using poly_big = nfl::poly_from_modulus<uint64_t, 4 * DEGREE, 60>;
}

/*============================================================================*/
/* Type definitions                                                           */
/*============================================================================*/

/* Class that represents a commitment key pair. */
class comkey_t {
public:
    params::poly_q A1[HEIGHT][WIDTH - HEIGHT];
    params::poly_q A2[SIZE][WIDTH];
};

/* Class that represents a commitment in CRT representation. */
class commit_t {
public:
    params::poly_q c1;
    vector<params::poly_q> c2;
};

/* Class that represents a BGV key pair. */
class bgvkey_t {
public:
    params::poly_q a;
    params::poly_q b;
};

class bgvenc_t {
public:
    params::poly_q u;
    params::poly_q v;
};

#include "util.hpp"

void bdlop_sample_rand(vector<params::poly_q> &r);

void bdlop_sample_chal(params::poly_q &f);

bool bdlop_test_norm(params::poly_q r, double_t sigma_sqr);

void bdlop_commit(commit_t &com, vector<params::poly_q> m, comkey_t &key, vector<params::poly_q> r);

int bdlop_open(commit_t &com, vector<params::poly_q> m, comkey_t &key, vector<params::poly_q> r, params::poly_q &f);

void bdlop_keygen(comkey_t &key);

void bgv_sample_message(params::poly_p &r);

void bgv_sample_short(params::poly_q &r);

void bgv_keygen(bgvkey_t &pk, params::poly_q &sk);

void bgv_encrypt(bgvenc_t &c, bgvkey_t &pk, params::poly_p &m);

void bgv_decrypt(params::poly_p &m, bgvenc_t &c, params::poly_q &sk);

// ntru




void ntru_keygen(params::poly_q &pk, params::poly_q &sk);
void ntru_sample_message(params::poly_p &r);
void ntru_encrypt(params::poly_q &c, params::poly_q &pk, params::poly_p &m);


#endif
