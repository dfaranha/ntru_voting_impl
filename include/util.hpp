#pragma once

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>

#include <algorithm>
#include <chrono>
#include <iostream>
#include <memory>
#include "zq.hpp"

namespace util {
/// Helper functions for messages conversion

/**
 * Center op1 modulo op2
 * @param rop     result
 * @param op1     number op1 already reduced modulo op2, i.e. such that 0 <= op1
 * < op2-1
 * @param op2     modulus
 * @param op2Div2 floor(modulus/2)
 */
inline void center(mpz_t & rop, mpz_t const &op1, mpz_t const &op2,
		mpz_t const &op2Div2) {
	mpz_set(rop, op1);
	if (mpz_cmp(op1, op2Div2) > 0) {
		mpz_sub(rop, rop, op2);
	}
}

/* Exact comparison of ring elements. NFLlib's operator== is element-wise and
 * its operator bool is "some coefficient is non-zero", so `a == b` holds as
 * soon as a and b agree in one of the nmoduli * degree values they store,
 * which is far too weak for a verification equation. Both arguments have to be
 * in the same domain. operator!= is fine as it stands. */
template <class P> inline bool equal(P const &a, P const &b) {
	for (size_t cm = 0; cm < P::nmoduli; cm++) {
		for (size_t i = 0; i < P::degree; i++) {
			if (a(cm, i) != b(cm, i)) {
				return false;
			}
		}
	}
	return true;
}

/* Inversion in R_q. The modulus satisfies q = 1 mod 2d, so x^d + 1 splits into
 * d linear factors and a polynomial in the NTT domain already is its own CRT
 * decomposition: inverting it is inverting each slot, and it is invertible
 * exactly when no slot is zero. Both arguments are in the NTT domain, and they
 * may be the same polynomial. Returns 0 on a zero divisor, leaving inv alone.
 *
 * The slots are inverted together, by Montgomery's trick: the prefix products
 * a_0 ... a_(i-1), one Fermat inversion of the product of all of them, and a
 * pass back that peels off one slot at a time. That is three multiplications
 * a slot and one exponentiation, where a Fermat inversion per slot was about
 * 90 multiplications a slot. Every slot is checked for zero before anything is
 * written, and each slot of a is read before inv's is written, so inv may be a.
 *
 * This replaced a dense inversion through FLINT -- convert to GMP, build a
 * polynomial mod x^d + 1, call invmod, convert back -- which cost about 95
 * million cycles and could not report a zero divisor without the caller
 * checking the return of fmpz_mod_poly_invmod, which no caller did. */
template <class P> inline int invert(P &inv, P const &a) {
	using T = typename P::value_type;
	static_assert(P::nmoduli == 1 && P::get_modulus(0) == zq::Q, "a zq polynomial");
	auto mulmod = [](T x, T y, size_t) { return zq::mulmod(x, y); };
	T pre[P::degree];

	for (size_t cm = 0; cm < P::nmoduli; cm++) {
		for (size_t i = 0; i < P::degree; i++) {
			if (a(cm, i) == 0) {
				return 0;
			}
		}
	}
	for (size_t cm = 0; cm < P::nmoduli; cm++) {
		const T q = P::get_modulus(cm);
		T acc = 1, x, r = 1;

		for (size_t i = 0; i < P::degree; i++) {
			pre[i] = acc;
			acc = mulmod(acc, a(cm, i), cm);
		}
		/* Fermat: acc^(q - 2) = acc^-1, since q is prime. */
		x = acc;
		for (T e = q - 2; e != 0; e >>= 1) {
			if (e & 1) {
				r = mulmod(r, x, cm);
			}
			x = mulmod(x, x, cm);
		}
		/* r is now (a_0 ... a_i)^-1 for i = degree - 1. */
		for (size_t i = P::degree; i-- > 0;) {
			const T ai = a(cm, i);

			inv(cm, i) = mulmod(r, pre[i], cm);
			r = mulmod(r, ai, cm);
		}
	}
	return 1;
}

/* The coefficients of a, read as they are stored (the coefficient domain, for
 * them to mean anything), centred into (-q/2, q/2]. With one modulus below
 * 2^60 they fit 64 bits, which is what spares a GMP integer a coefficient. */
template <class P> inline void centred(int64_t out[], P const &a) {
	static_assert(P::nmoduli == 1, "one modulus, so a coefficient is one residue");
	const uint64_t q = P::get_modulus(0);

	for (size_t i = 0; i < P::degree; i++) {
		const uint64_t c = a(0, i);
		out[i] = (c > q / 2) ? (int64_t) c - (int64_t) q : (int64_t) c;
	}
}

/* a = the polynomial with signed coefficients v, in the coefficient domain. */
template <class P> inline void set_signed(P &a, const int64_t v[]) {
	static_assert(P::nmoduli == 1, "one modulus, so a coefficient is one residue");
	const uint64_t q = P::get_modulus(0);

	for (size_t i = 0; i < P::degree; i++) {
		const uint64_t m = (v[i] < 0 ? (uint64_t) 0 - (uint64_t) v[i] : (uint64_t) v[i]) % q;
		a(0, i) = (v[i] < 0 && m != 0) ? q - m : m;
	}
}

/* dot += sum_k a_k b_k and norm += sum_k b_k^2 over n centred coefficients.
 * Exact in 128 bits when every |a_k| and |b_k| is below 2^57, so that n <= 2^12
 * products stay below 2^126; in long double otherwise. The callers turn both
 * into doubles for a rejection test, as mpz_get_d did. */
inline void dot_norm(long double &dot, long double &norm, const int64_t a[],
		const int64_t b[], size_t n) {
	const int64_t lim = (int64_t) 1 << 57;
	bool small = n <= 4096;

	for (size_t k = 0; k < n && small; k++) {
		small = a[k] > -lim && a[k] < lim && b[k] > -lim && b[k] < lim;
	}
	if (small) {
		__int128 d = 0, s = 0;

		for (size_t k = 0; k < n; k++) {
			d += (__int128) a[k] * b[k];
			s += (__int128) b[k] * b[k];
		}
		dot += (long double) d;
		norm += (long double) s;
	} else {
		for (size_t k = 0; k < n; k++) {
			dot += (long double) a[k] * (long double) b[k];
			norm += (long double) b[k] * (long double) b[k];
		}
	}
}

/* The exact squared l2-norm of a's centred coefficients, provided (q/2)^2
 * times the degree fits 128 bits, which it does for q = 2^59 + 16385 at
 * degree 2048 (2^127); the check is what keeps it exact for any other q. */
template <class P> inline unsigned __int128 norm2(P const &a) {
	static_assert(P::nmoduli == 1, "one modulus, so a coefficient is one residue");
	const uint64_t q = P::get_modulus(0);
	unsigned __int128 s = 0;

	if ((unsigned __int128) (q / 2) * (q / 2) > ~(unsigned __int128) 0 / P::degree) {
		fprintf(stderr, "util::norm2: q is too large for an exact 128-bit norm\n");
		abort();
	}

	for (size_t i = 0; i < P::degree; i++) {
		const uint64_t c = a(0, i), m = (c > q / 2) ? q - c : c;
		s += (unsigned __int128) m * m;
	}
	return s;
}

template <class P> inline bool is_zero(P const &a) {
	for (size_t cm = 0; cm < P::nmoduli; cm++) {
		for (size_t i = 0; i < P::degree; i++) {
			if (a(cm, i) != 0) {
				return false;
			}
		}
	}
	return true;
}
} // namespace util
