/**
 * @file
 *
 * Serialisation of a proof, and the only place that says how many bytes one
 * takes. Sizes quoted anywhere else in this repository are derived from a
 * model; the figures this produces are the transcript itself.
 *
 * Two encodings, because a proof carries two kinds of ring element.
 *
 * A *uniform* element -- a commitment, a published scalar, a first message --
 * is uniform over Z_q and costs ceil(log2 q) bits a coefficient. There is
 * nothing to exploit.
 *
 * A *masked opening* is a discrete Gaussian of width sigma, and writing it at
 * the width of its bound wastes the difference between that and its entropy.
 * The entropy of a discrete Gaussian is about log2(sigma sqrt(2 pi e)), which
 * at sigma = 2^10 is 12.05 bits against the 14 a flat encoding spends. What is
 * used here is Golomb-Rice: zigzag the centred coefficient and split it at a
 * parameter k, low k bits raw and the quotient in unary. That is within about
 * half a bit of the entropy of a two-sided geometric and, for a Gaussian, of
 * this one -- see serial_rice_k() for the choice of k.
 */

#ifndef SERIAL_H
#define SERIAL_H

#include <cmath>
#include <cstdint>
#include <cstring>
#include <vector>

#include "common.h"

namespace serial {

/** Bits in a uniform coefficient: the modulus is a single prime here. */
static inline size_t qbits(void) {
	static size_t b = 0;
	if (b == 0) {
		uint64_t q = params::poly_q::get_modulus(0);
		while (q != 0) {
			b++;
			q >>= 1;
		}
	}
	return b;
}

/** A growable bit buffer, written and read most-significant bit first. */
class bits {
  public:
	std::vector < uint8_t > buf;
	size_t nbits = 0;             /* written */
	size_t pos = 0;               /* read cursor */
	/* Set by a read past the end, or of an encoding no writer produces; a
	 * transcript read with it set is to be rejected. */
	bool bad = false;

	bits() = default;
	/** A reader over len published bytes. */
	bits(const uint8_t *in, size_t len) : buf(in, in + len), nbits(8 * len) {}
	/** A reader over a writer's bytes, which it takes over. */
	explicit bits(std::vector < uint8_t > &&in) : buf(std::move(in)), nbits(8 * buf.size()) {}

	/* The low n bits of v, most significant first; for n > 64, the bits
	 * above v's 64 are zeros, written without shifting a 64-bit value by 64
	 * or more, which is undefined (proof_size puts a 256-bit hash this way). */
	void put(uint64_t v, int n) {
		for (int i = n - 1; i >= 0; i--) {
			if ((nbits & 7) == 0) {
				buf.push_back(0);
			}
			if (i < 64 && ((v >> i) & 1)) {
				buf[nbits >> 3] |= 0x80 >> (nbits & 7);
			}
			nbits++;
		}
	}

	uint64_t get(int n) {
		uint64_t v = 0;
		if (pos + n > 8 * buf.size()) {
			bad = true;
			pos = 8 * buf.size();
			return 0;
		}
		for (int i = 0; i < n; i++) {
			v <<= 1;
			v |= (buf[pos >> 3] >> (7 - (pos & 7))) & 1;
			pos++;
		}
		return v;
	}

	/** Whether a reader ended exactly where its writer did: nothing flagged,
	 * no byte left over and the padding bits of the last byte zero. */
	bool finish(void) const {
		return !bad && (pos + 7) / 8 == buf.size()
				&& ((pos & 7) == 0 || (buf[pos >> 3] & (0xff >> (pos & 7))) == 0);
	}

	/** Bytes the transcript occupies, which is what a size is. */
	size_t bytes(void) const {
		return (nbits + 7) / 8;
	}
};

/** Zigzag, so that a small negative is a small unsigned. */
static inline uint64_t zigzag(int64_t x) {
	return ((uint64_t) x << 1) ^ (uint64_t) (x >> 63);
}

static inline int64_t unzigzag(uint64_t u) {
	return (int64_t) (u >> 1) ^ -(int64_t) (u & 1);
}

/**
 * The Rice parameter for a discrete Gaussian of width sigma. The mean of the
 * zigzagged value is about 2 sigma sqrt(2/pi), and Rice is near-optimal when
 * the split falls at the mean, so k = round(log2(mean)).
 */
static inline int rice_k(double sigma) {
	double mean = 2.0 * sigma * 0.7978845608;
	int k = (int) (std::log2(mean) + 0.5);
	return k < 0 ? 0 : k;
}

static inline void put_rice(bits & b, int64_t x, int k) {
	uint64_t u = zigzag(x);
	uint64_t q = u >> k;

	/* Unary quotient. Capped so that a coefficient far outside the bound
	 * cannot make the encoding enormous; the escape spends the full width. */
	if (q >= 24) {
		b.put(0xffffff, 24);
		b.put(u, 64);
		return;
	}
	for (uint64_t i = 0; i < q; i++) {
		b.put(1, 1);
	}
	b.put(0, 1);
	if (k > 0) {
		b.put(u & (((uint64_t) 1 << k) - 1), k);
	}
}

static inline int64_t get_rice(bits & b, int k) {
	uint64_t q = 0;

	while (q < 24 && b.get(1) == 1) {
		q++;
	}
	if (q >= 24) {
		uint64_t u = b.get(64);
		/* The writer escapes only what the unary run cannot carry. */
		if ((u >> k) < 24) {
			b.bad = true;
		}
		return unzigzag(u);
	}
	uint64_t u = q << k;
	if (k > 0) {
		u |= b.get(k);
	}
	return unzigzag(u);
}

/** Centre a residue into (-q/2, q/2]. */
static inline int64_t centre(uint64_t c, uint64_t q) {
	return c > q / 2 ? (int64_t) c - (int64_t) q : (int64_t) c;
}

/**
 * Write a uniform ring element: every coefficient at full width. The element
 * is taken in the coefficient domain, which is how it is transmitted.
 */
static inline void put_uniform(bits & b, const params::poly_q & p) {
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		b.put(p(0, i), qbits());
	}
}

static inline void get_uniform(bits & b, params::poly_q & p) {
	const uint64_t q = params::poly_q::get_modulus(0);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		uint64_t v = b.get(qbits());
		if (v >= q) {
			b.bad = true;
			v = 0;
		}
		p(0, i) = v;
	}
}

/** Write a masked opening, Rice-coded about its own width. */
static inline void put_gauss(bits & b, const params::poly_q & p, double sigma) {
	const uint64_t q = params::poly_q::get_modulus(0);
	int k = rice_k(sigma);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		put_rice(b, centre(p(0, i), q), k);
	}
}

static inline void get_gauss(bits & b, params::poly_q & p, double sigma) {
	const uint64_t q = params::poly_q::get_modulus(0);
	int k = rice_k(sigma);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		int64_t c = get_rice(b, k);
		if (c > (int64_t) (q / 2) || c < -(int64_t) (q / 2)) {
			b.bad = true;
			c = 0;
		}
		p(0, i) = c < 0 ? (uint64_t) ((int64_t) q + c) : (uint64_t) c;
	}
}

/** A Gaussian element held in the NTT domain, sent in the coefficient one. */
static inline void put_gauss_ntt(bits & b, const params::poly_q & p, double sigma) {
	params::poly_q t = p;
	t.invntt_pow_invphi();
	put_gauss(b, t, sigma);
}

static inline void get_gauss_ntt(bits & b, params::poly_q & p, double sigma) {
	get_gauss(b, p, sigma);
	p.ntt_pow_phi();
}

/** A ternary element held in the NTT domain: 2 bits a coefficient, 0, 1 or
 * 2 for -1. Returns 0, writing nothing usable, if it is not ternary. */
static inline int put_ternary_ntt(bits & b, const params::poly_q & p) {
	const uint64_t q = params::poly_q::get_modulus(0);
	params::poly_q t = p;
	int ok = 1;

	t.invntt_pow_invphi();
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		uint64_t c = t(0, i);
		ok &= c <= 1 || c == q - 1;
		b.put(c <= 1 ? c : 2, 2);
	}
	return ok;
}

static inline void get_ternary_ntt(bits & b, params::poly_q & p) {
	const uint64_t q = params::poly_q::get_modulus(0);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		uint64_t c = b.get(2);
		if (c == 3) {
			b.bad = true;
			c = 0;
		}
		p(0, i) = c == 2 ? q - 1 : c;
	}
	p.ntt_pow_phi();
}

static inline void put_bytes(bits & b, const uint8_t *v, size_t n) {
	for (size_t i = 0; i < n; i++) {
		b.put(v[i], 8);
	}
}

static inline void get_bytes(bits & b, uint8_t *v, size_t n) {
	for (size_t i = 0; i < n; i++) {
		v[i] = (uint8_t) b.get(8);
	}
}

/** A commitment: c1 and its n message rows, uniform, as held. */
static inline void put_commit(bits & b, const commit_t & c) {
	put_uniform(b, c.c1);
	for (size_t i = 0; i < c.c2.size(); i++) {
		put_uniform(b, c.c2[i]);
	}
}

static inline void get_commit(bits & b, commit_t & c, size_t n) {
	get_uniform(b, c.c1);
	c.c2.resize(n);
	for (size_t i = 0; i < n; i++) {
		get_uniform(b, c.c2[i]);
	}
}

}                               /* namespace serial */

#endif                          /* SERIAL_H */
