/*
 * zq.hpp
 *
 * Arithmetic in Z_q[X]/(X^D + 1) for the NTRU modulus q = 576460752303439873
 * (60 bits, NTRU_PRIMEQ in common.h), at the two degrees the code uses:
 * DEGREE = 2048 for params::poly_q and params::poly_p, and 4 * DEGREE for
 * params::poly_big. q - 1 is divisible by 2^14, just enough for the negacyclic
 * NTT of degree 8192.
 *
 * It replaces NFLlib, which this code held to one modulus anyway (its table
 * of 64-bit primes had been cut down to this one), and implements the part of
 * NFLlib's poly the code calls, with the same meaning, so the callers did not
 * change: a polynomial is D coefficients in [0, q) in one 32-byte aligned
 * array of uint64_t, so sizeof(value_type), nmoduli and the bytes every hash
 * absorbs are as they were. As in NFLlib, + - * act coefficient-wise, so * is
 * the ring product only on polynomials in NTT form. The samplers draw from
 * the same generator as before (src/fastrandombytes.cpp) and follow
 * lattice-verifiable-mixnet's zq.hpp, which matches NFLlib's distributions.
 *
 * Two departures: == and != compare every coefficient and return a bool
 * (NFLlib's == was true as soon as one coefficient agreed), and uniform()
 * samples exactly, by rejection.
 *
 * The forward NTT is lattice-verifiable-mixnet's: coefficients to evaluations
 * at the odd powers of psi, in bit-reversed order, psi a primitive 2D-th root
 * of unity found from the smallest non-residue.
 */
#ifndef ZQ_HPP
#define ZQ_HPP

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <vector>
#include <gmp.h>
#include "nfl.hpp"

namespace zq {

typedef unsigned __int128 u128;

static constexpr uint64_t Q = 576460752303439873ULL;
static constexpr int QBITS = 60;
static_assert(Q >> (QBITS - 1) == 1, "q has QBITS bits");

/* a * b mod q for a, b < q: Barrett with k = QBITS and mu = floor(2^2k / q).
 * The quotient estimate is at most two below the true one. */
/* x - m if x >= m, else x, without a branch: whether a reduced value lands
 * above the modulus is a coin toss, which a conditional jump mispredicts half
 * the time. Valid for x < 2^63 and m < 2^63, which every value here is. */
static inline uint64_t csub(uint64_t x, uint64_t m) {
	const uint64_t t = x - m;
	return t + (m & (uint64_t) ((int64_t) t >> 63));
}

static constexpr uint64_t BARRETT_MU = (uint64_t) ((((u128) 1) << (2 * QBITS)) / Q);
static inline uint64_t mulmod(uint64_t a, uint64_t b) {
	const uint64_t MU = BARRETT_MU;
	const u128 x = (u128) a * b;
	const uint64_t q1 = (uint64_t) (x >> (QBITS - 1));
	const uint64_t q3 = (uint64_t) (((u128) q1 * MU) >> (QBITS + 1));
	uint64_t r = (uint64_t) x - q3 * Q;
	r = csub(r, Q);
	r = csub(r, Q);
	return r;
}

static inline uint64_t addmod(uint64_t a, uint64_t b) {
	return csub(a + b, Q);
}

static inline uint64_t submod(uint64_t a, uint64_t b) {
	return csub(a - b + Q, Q);
}

static inline uint64_t negmod(uint64_t a) {
	return a == 0 ? 0 : Q - a;
}

static inline uint64_t powmod(uint64_t a, uint64_t e) {
	uint64_t r = 1;
	while (e) {
		if (e & 1) r = mulmod(r, a);
		a = mulmod(a, a);
		e >>= 1;
	}
	return r;
}

/* w * b mod q for a fixed w < q, with wp = floor(w 2^64 / q): Shoup. */
static inline uint64_t mulshoup(uint64_t w, uint64_t wp, uint64_t b) {
	const uint64_t qh = (uint64_t) (((u128) wp * b) >> 64);
	return csub(w * b - qh * Q, Q);
}

/* The same without the final correction, in [0, 2q) for any 64-bit b: what the
 * lazy butterflies below use. */
static inline uint64_t mulshoup_lazy(uint64_t w, uint64_t wp, uint64_t b) {
	const uint64_t qh = (uint64_t) (((u128) wp * b) >> 64);
	return w * b - qh * Q;
}

static inline uint64_t shoup(uint64_t w) {
	return (uint64_t) ((((u128) w) << 64) / Q);
}

/* q as a GMP integer, made once. */
static inline const mpz_t &modulus_mpz() {
	static struct m {
		mpz_t v;
		m() { mpz_init_set_ui(v, Q); }
	} mod;
	return mod.v;
}

/* The twiddle factors of the negacyclic NTT of degree D. */
template <size_t D> struct ntt_tables {
	uint64_t fwd[D], fwdp[D];	/* psi^brv(i) and its Shoup constant */
	uint64_t bwd[D], bwdp[D];	/* psi^-brv(i) */
	uint64_t ninv, ninvp;

	static const ntt_tables &get() {
		static ntt_tables t;
		return t;
	}

  private:
	ntt_tables() {
		static_assert((D & (D - 1)) == 0, "D a power of two");
		if ((Q - 1) % (2 * D) != 0) {
			throw std::runtime_error("zq: q has no 2D-th roots of unity");
		}
		uint64_t g = 2;
		while (powmod(g, (Q - 1) / 2) != Q - 1) g++;
		const uint64_t psi = powmod(g, (Q - 1) / (2 * D));
		if (powmod(psi, D) != Q - 1) {
			throw std::runtime_error("zq: no primitive 2D-th root of unity");
		}
		const uint64_t psiinv = powmod(psi, Q - 2);
		unsigned logd = 0;
		while (((size_t) 1 << logd) < D) logd++;
		for (size_t i = 0; i < D; i++) {
			size_t r = 0;
			for (unsigned b = 0; b < logd; b++) r |= ((i >> b) & 1) << (logd - 1 - b);
			fwd[i] = powmod(psi, r);
			fwdp[i] = shoup(fwd[i]);
			bwd[i] = powmod(psiinv, r);
			bwdp[i] = shoup(bwd[i]);
		}
		ninv = powmod(D, Q - 2);
		ninvp = shoup(ninv);
	}
};

template <size_t Degree> class poly {
  public:
	typedef uint64_t value_type;
	typedef int64_t signed_value_type;
	static constexpr size_t degree = Degree;
	static constexpr size_t nmoduli = 1;

	poly() {
		std::memset(_data, 0, sizeof(_data));
	}
	/* The constant v (coefficient 0), as NFLlib's poly(v). */
	poly(value_type v) {
		std::memset(_data, 0, sizeof(_data));
		_data[0] = v % Q;
	}
	poly(int v) : poly(v < 0 ? negmod((value_type) (-(int64_t) v) % Q) : (value_type) v) {}
	poly(nfl::uniform const &m) {
		set(m);
	}
	poly(nfl::ZO_dist const &m) {
		set(m);
	}
	poly(nfl::hwt_dist const &m) {
		set(m);
	}

	/* Without these, x = 0 would be ambiguous: the samplers' tags are
	 * implicitly constructible from integers too. */
	poly &operator=(int v) {
		return *this = poly(v);
	}
	poly &operator=(value_type v) {
		return *this = poly(v);
	}
	poly &operator=(nfl::uniform const &m) {
		set(m);
		return *this;
	}
	poly &operator=(nfl::ZO_dist const &m) {
		set(m);
		return *this;
	}
	poly &operator=(nfl::hwt_dist const &m) {
		set(m);
		return *this;
	}

	static constexpr value_type get_modulus(size_t) {
		return Q;
	}
	static const mpz_t &moduli_product() {
		return modulus_mpz();
	}
	static constexpr size_t bits_in_moduli_product() {
		return QBITS;
	}

	value_type &operator()(size_t, size_t i) {
		return _data[i];
	}
	value_type const &operator()(size_t, size_t i) const {
		return _data[i];
	}
	value_type *data() {
		return _data;
	}
	value_type const *data() const {
		return _data;
	}
	value_type *begin() {
		return _data;
	}
	value_type *end() {
		return _data + Degree;
	}
	value_type const *begin() const {
		return _data;
	}
	value_type const *end() const {
		return _data + Degree;
	}

	/* Uniform in [0, q), by rejection on 60-bit words. */
	void set(nfl::uniform const &) {
		uint64_t buf[64];
		size_t i = 0, k = 64;

		while (i < Degree) {
			if (k == 64) {
				nfl::fastrandombytes((unsigned char *) buf, sizeof(buf));
				k = 0;
			}
			const uint64_t x = buf[k++] & ((1ULL << QBITS) - 1);
			if (x < Q) {
				_data[i++] = x;
			}
		}
	}

	/* +-1 with probability rho / 256 each half, else 0, as NFLlib's ZO_dist. */
	void set(nfl::ZO_dist const &m) {
		uint8_t rnd[Degree];

		nfl::fastrandombytes(rnd, sizeof(rnd));
		for (size_t i = 0; i < Degree; i++) {
			_data[i] = rnd[i] <= m.rho ? ((rnd[i] & 2) ? Q - 1 : 1) : 0;
		}
	}

	/* hwt coefficients +-1 at uniform positions, the others 0, as NFLlib's
	 * hwt_dist: reservoir sampling of the positions, then a sign each. */
	void set(nfl::hwt_dist const &m) {
		if (m.hwt == 0 || m.hwt > Degree) {
			throw std::runtime_error("zq: hwt_dist weight out of range");
		}
		std::vector<size_t> hit(m.hwt), rnd(m.hwt);
		std::iota(hit.begin(), hit.end(), 0U);
		auto ptr = rnd.end();
		for (size_t k = m.hwt; k < Degree; ++k) {
			size_t pos;
			const size_t lim = std::numeric_limits<size_t>::max() / k;
			for (;;) {
				if (ptr == rnd.end()) {
					nfl::fastrandombytes((unsigned char *) rnd.data(),
							rnd.size() * sizeof(size_t));
					ptr = rnd.begin();
				}
				pos = *ptr++;
				if (pos <= lim * k) {
					pos %= k;
					break;
				}
			}
			if (pos < m.hwt) {
				hit[pos] = k;
			}
		}
		std::memset(_data, 0, sizeof(_data));
		nfl::fastrandombytes((unsigned char *) rnd.data(),
				rnd.size() * sizeof(size_t));
		for (size_t j = 0; j < hit.size(); j++) {
			_data[hit[j]] = (rnd[j] & 2) ? 1 : Q - 1;
		}
	}

	/* Negacyclic NTT, in place: coefficients to evaluations at the odd powers
	 * of psi, in bit-reversed order. Harvey's lazy butterflies, as NFLlib's:
	 * values stay in [0, 4q), which fits since q < 2^60, and are reduced once
	 * at the end. */
	void ntt_pow_phi() {
		const ntt_tables<Degree> &t = ntt_tables<Degree>::get();
		const uint64_t q2 = 2 * Q;
		size_t k = 1;
		for (size_t len = Degree / 2; len >= 1; len >>= 1) {
			for (size_t start = 0; start < Degree; start += 2 * len) {
				const uint64_t z = t.fwd[k], zp = t.fwdp[k];
				k++;
				for (size_t j = start; j < start + len; j++) {
					uint64_t u = _data[j];
					u = csub(u, q2);
					const uint64_t v = mulshoup_lazy(z, zp, _data[j + len]);
					_data[j] = u + v;
					_data[j + len] = u - v + q2;
				}
			}
		}
		for (size_t j = 0; j < Degree; j++) {
			uint64_t u = _data[j];
			u = csub(u, q2);
			u = csub(u, Q);
			_data[j] = u;
		}
	}

	void invntt_pow_invphi() {
		const ntt_tables<Degree> &t = ntt_tables<Degree>::get();
		for (size_t len = 1; len < Degree; len <<= 1) {
			/* Undo the forward butterflies of this level, block by block. */
			size_t k = Degree / (2 * len);
			for (size_t start = 0; start < Degree; start += 2 * len) {
				const uint64_t z = t.bwd[k], zp = t.bwdp[k];
				k++;
				/* Lazy too: values stay in [0, 2q) until the factor 1/D. */
				for (size_t j = start; j < start + len; j++) {
					const uint64_t u = _data[j], v = _data[j + len];
					uint64_t s = u + v;
					s = csub(s, 2 * Q);
					_data[j] = s;
					_data[j + len] = mulshoup_lazy(z, zp, u - v + 2 * Q);
				}
			}
		}
		for (size_t j = 0; j < Degree; j++) {
			_data[j] = mulshoup(t.ninv, t.ninvp, _data[j]);
		}
	}

	/* The coefficients as integers in [0, q) (or values, in the NTT domain). */
	template <class A> void poly2mpz(A &out) const {
		for (size_t i = 0; i < Degree; i++) {
			mpz_set_ui(out[i], _data[i]);
		}
	}

	/* From integers, reduced mod q (negative ones too). */
	template <class A> void mpz2poly(A const &in) {
		for (size_t i = 0; i < Degree; i++) {
			_data[i] = mpz_fdiv_ui(in[i], Q);
		}
	}

	poly &operator+=(poly const &b) {
		for (size_t i = 0; i < Degree; i++) {
			_data[i] = addmod(_data[i], b._data[i]);
		}
		return *this;
	}
	poly &operator-=(poly const &b) {
		for (size_t i = 0; i < Degree; i++) {
			_data[i] = submod(_data[i], b._data[i]);
		}
		return *this;
	}
	poly &operator*=(poly const &b) {
		for (size_t i = 0; i < Degree; i++) {
			_data[i] = mulmod(_data[i], b._data[i]);
		}
		return *this;
	}
	friend poly operator+(poly a, poly const &b) {
		return a += b;
	}
	friend poly operator-(poly a, poly const &b) {
		return a -= b;
	}
	friend poly operator*(poly a, poly const &b) {
		return a *= b;
	}
	friend poly operator-(poly a) {
		for (size_t i = 0; i < Degree; i++) {
			a._data[i] = negmod(a._data[i]);
		}
		return a;
	}
	/* Exact, unlike NFLlib's element-wise operator==. */
	friend bool operator==(poly const &a, poly const &b) {
		return std::memcmp(a._data, b._data, sizeof(a._data)) == 0;
	}
	friend bool operator!=(poly const &a, poly const &b) {
		return !(a == b);
	}

  private:
	alignas(32) value_type _data[Degree];
};

}	/* namespace zq */

#endif /* ZQ_HPP */
