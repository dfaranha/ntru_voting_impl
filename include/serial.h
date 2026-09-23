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
		uint64_t q = nfl::params < uint64_t >::P[0];
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

	void put(uint64_t v, int n) {
		for (int i = n - 1; i >= 0; i--) {
			if ((nbits & 7) == 0) {
				buf.push_back(0);
			}
			if ((v >> i) & 1) {
				buf[nbits >> 3] |= 0x80 >> (nbits & 7);
			}
			nbits++;
		}
	}

	uint64_t get(int n) {
		uint64_t v = 0;
		for (int i = 0; i < n; i++) {
			v <<= 1;
			v |= (buf[pos >> 3] >> (7 - (pos & 7))) & 1;
			pos++;
		}
		return v;
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
		return unzigzag(b.get(64));
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
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		p(0, i) = b.get(qbits());
	}
}

/** Write a masked opening, Rice-coded about its own width. */
static inline void put_gauss(bits & b, const params::poly_q & p, double sigma) {
	const uint64_t q = nfl::params < uint64_t >::P[0];
	int k = rice_k(sigma);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		put_rice(b, centre(p(0, i), q), k);
	}
}

static inline void get_gauss(bits & b, params::poly_q & p, double sigma) {
	const uint64_t q = nfl::params < uint64_t >::P[0];
	int k = rice_k(sigma);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		int64_t c = get_rice(b, k);
		p(0, i) = c < 0 ? (uint64_t) ((int64_t) q + c) : (uint64_t) c;
	}
}

}                               /* namespace serial */

#endif                          /* SERIAL_H */
