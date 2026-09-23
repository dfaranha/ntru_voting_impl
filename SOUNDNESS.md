# Soundness of the proof of shuffle

This document covers the work needed to fulfil Lemma 5 of
[ePrint 2025/658](https://eprint.iacr.org/2025/658) in this codebase: the
attack that makes it necessary, the ring that admits the attack, the repair,
the two membership sub-proofs the repair rests on, and the repetitions that
carry it to `LEVEL = 128` bits. It is the reason branch `fix-pkc` exists.

Everything below is checked by tests in `src/ntru_shuffle.cpp` and
`src/ntru_pismall.cpp` rather than asserted: each link has a test that fails if
the link is removed.

## 1. The attack

The published proof of shuffle argues a permutation through Neff's product: the
verifier is convinced that the output list `m'` is a permutation of the input
list `m` because

    prod_i (m_i - chi) = prod_i (m'_i - chi)

for a challenge `chi`. That product is taken in `R_q`, and `R_q` is not a
field. It splits, and the identity is therefore checked in each of the fields
it splits into, *independently*. A prover who permutes the list differently in
each of them satisfies every one of those identities at once while producing an
output that is not a permutation of the input over the ring.

`TEST_ONCE("CRT-mixed list is not a permutation but passes Neff's product")`
exhibits exactly that: two outputs exchange half of their NTT slots, the test
asserts that the resulting list differs from the honest one, and that Neff's
product is unchanged. Before the repair, the proof of shuffle accepted it.

## 2. The ring

`q = 576460752303439873 = 2^59 + 16385` is prime, `d = 2048`, and NFLlib's NTT
requires `q = 1 mod 2d`, which holds: `q - 1` is divisible by `2^14`. So
`x^d + 1` splits into `d` linear factors and

    R_q = Z_q[x]/(x^2048 + 1)  ~  (Z_q)^2048.

There are 2048 independent components, and a permutation of the list inside
each of them is what Section 1 exploits. This is not a defect of the
implementation: the NTT the scheme is built on requires the modulus that
produces it.

## 3. Lemma 5, with g(i) = i

The repair is to stop arguing about the messages alone and argue about pairs.
Fix a public injection `g : [MSGS] -> D` and have the prover commit, before any
challenge exists, to elements `sigma_i` claimed to be `g(pi(i))` for its
permutation `pi`. The product then runs over

    a_i = m_i  + g(i)    * tau - mu
    b_i = m'_i + sigma_i * tau - mu

for challenges `tau` and `mu`. An index travels with each message, so a list
mixed across components can no longer balance the product: matching the message
in one component and the index in another is not a matching of pairs.

`g(i) = i`, the ring constant with that value (`index_scalar`). The `sigma_i`
are committed in `shuffle_commit_sigma`, which is the prover's first message,
sent once and shared by every pass; `tau` and `mu` are hashed from those
commitments, so a prover cannot choose the `sigma_i` knowing them.

One consequence reaches into the linear proof. `b_l` now contains the committed
`sigma_l`, so it is no longer public, and the term multiplying it must reach
the verifier as a commitment. Each linear proof therefore relates **three**
commitments instead of two:

    coef[0] * <msg of c_l> + coef[1] * <msg of p_l> + coef[2] = <msg of d_l>

with `coef[1] = raw * tau` carrying `P_l`, the commitment to `sigma_l`.

`TEST_ONCE("shuffle proof rejects the CRT-mixing attack")` is the test that
fails without any of this.

## 4. Membership

Lemma 5 needs the `sigma_i` to lie in `D`. A product identity cannot establish
that on its own: a prover who mixes the `sigma_i` across components the same
way it mixes the messages rebalances the pairs. Two sub-proofs about the same
commitments `P_i` close it.

### 4.1 Pi_SMALL, that each sigma_i is a ring constant

`src/ntru_pismall.cpp` is the exact proof of Lemma 2, instantiated on the
commitment equation — `R = HEIGHT + 1` rows, `V = WIDTH + 1` components — and
amortized over the `MSGS` commitments, padded to the power of two its
interpolation nodes need. Each witness component carries its own coefficient
set; the commitment randomness is `AEX_TER` and the message is `AEX_SCALAR`,
which is *free at coefficient 0 and zero everywhere else*. That is precisely
"is a ring constant".

Two parameters carry its soundness.

* **The challenge extension.** The algebraic part of Lemma 2 is
  `18 TAU / q^AEX_DEG`. Challenges live in `GR(q, AEX_DEG)` with
  `AEX_DEG = 4`, which is `2^-222` at `TAU = 1024`. The extension is
  `Y^4 - AEX_NR`; the `AEX_NR = 3` of the mix-net this proof came from does not
  work here, 3 being a square modulo this `q`. `AEX_NR = 5` is a non-residue
  and `-20` is not a fourth power, so `Y^4 - 5` is irreducible.
* **The opened columns.** The proximity part is bounded by
  `2 max((g/(l - ETA))^ETA, (1 - 2(g - g')/3l)^ETA)`, minimized over the
  threshold `g` between the message length `g' = 2N + ETA` and the code length
  `l = AEX_COLS`. Here `l` is `4N = 8192`, and the two branches balance at
  `g = 6500`-odd: `ETA = 549` is where that crosses `2^-LEVEL`, and the code
  uses 550. **This is half the code length of the mix-net**, whose `l` is
  16384, and at its `ETA = 452` the bound here would be only `2^-112`. The
  formula reproduces that repository's own figures — `ETA = 325` gives `2^-95`
  and 451 gives `2^-128.1`, both as its comments state — which is what says it
  is being read correctly.

**The coefficient sets are exact over `Z_q`.** This modulus is a single prime,
so `f^3 - f` has exactly the three roots `-1, 0, 1` and `f(f - 1)` exactly two.
The mix-net has a composite `q`, where the same identity admits every CRT
combination of those roots — 27 of them, not 3 — and needs a norm bound to rule
the rest out. Nothing of that kind is needed here, and the witness that
exhibits it cannot be written down with one prime.
`TEST_ONCE("the coefficient sets are exact over Z_q")` asserts the consequence:
a coefficient of 2 is rejected.

### 4.2 Pi_BND, that the openings are short

`src/pibnd.cpp` is the amortized approximate norm proof, instantiated on the
same commitment equation and amortized over exactly the `MSGS` commitments.
`NTI = 130` columns give `NTI >= LEVEL + 2`, which is what its extractor needs.

Its last witness row is not the decryption noise the proof was written for: it
holds the `sigma_i`, whose infinity norm reaches `MSGS`. The instance therefore
declares `ANEX_E_INF = TAU` (`-DPIBND_SHORT`, resolved in `src/pibnd.cpp`).
Sized for a ternary row instead, `sigma-hat` would leave the rejection sampling
of that row accepting about once in ninety attempts at `MSGS = 256`, and the
honest prover would give up.

### 4.3 What each sub-proof actually catches

`TEST_ONCE("shuffle proof rejects CRT-mixed sigma")` applies to the permutation
elements the same mix applied to the messages. Disabling each verifier in turn
shows that **either sub-proof rejects it on its own**, for different reasons: a
slot-mix of two constants is not a constant, which `Pi_SMALL` sees; and it is
dense with coefficients the size of `q`, so its opening cannot pass rejection
sampling, which `Pi_BND` sees. The test does not separate them.

In the mix-net, `Pi_BND` is what makes the coefficient sets exact and what feeds
the CRT argument that `sigma_i` is the same constant in both components;
neither applies here. Section 6 works out what remains, and the answer is that
the permutation argument does not use it: membership in `D` follows from the
product identity together with constancy, without a norm bound. What it still
buys is stated there.

## 5. Repetitions

Two counts, both derived in the code from the modulus rather than chosen.

**The product argument.** One pass has soundness error at most `MSGS / q`: the
challenges are uniform over `R_q`, so a false statement passes when the
challenge vanishes in a component where the identity fails, which is a root of
a degree-`MSGS` polynomial there. That is `2^-57` at `MSGS = 4`, `2^-51` at 256
and `2^-49` at 1000, so `SHUFFLE_REPS = 3` at every supported size.

**The linear proof.** Its final check reduces to `beta L = 0` for the residual
`L`, so a false relation passes when `beta` vanishes in a component where `L`
does not: `1/q = 2^-59`, and no better, the challenge set being sparse. Hence
`LIN_REPS = 3`.

Repetitions multiply only if a prover who fails one cannot retry it alone, so
both are staged:

* The `P_i` and their sub-proofs are sent once for all passes.
* Every pass derives its own `tau` and `mu` — from those commitments and the
  pass index — and commits its `D_i`, before any `beta` exists.
* `shuffle_beta_hash` then draws all three `beta` from a single hash of every
  pass's first message.
* Inside a pass, `lin_hash` absorbs all three repetitions' first messages and
  `lin_chal` derives all three challenges from that one hash.

Rejection sampling follows the same logic: the three repetitions' three
openings stand or fall together, so `rej_accum` accumulates over all of them
and `rej_decide` decides once. Testing each separately would multiply the
rejection rate by nine.

## 6. The extraction argument

What the preceding sections establish, assembled: from an accepting transcript,
either the output list is a permutation of the input or one of the stated
assumptions fails.

**Notation.** A commitment is `c1 = A1 r`, `c2 = A2 r + m`. Write `v_i` for the
scalar the prover commits to in `P_i`, `m_i` and `m'_i` for the input and
output messages, and `a_i`, `b_i` for the factors of Section 3. Components
means the `d` fields `R_q` splits into; `f^(k)` is `f` in the `k`-th.

**What is extracted.**

* `Pi_SMALL` is an *exact* proof of knowledge: its extractor returns, for each
  `i`, an opening `(r_i, sigma_i)` of `P_i` with `r_i` ternary and `sigma_i` in
  the declared set. Over a prime modulus that set is exact (Section 4.1), so
  `sigma_i` is a ring constant: a scalar `v_i` in `Z_q`, the same in every
  component.
* Each linear proof is 2-special-sound. Two accepting transcripts sharing a
  first message and differing in `beta` yield, for the `l`-th proof, a short
  `c = beta - beta'`, non-zero, and openings satisfying the relation multiplied
  by `c`.

**Lemma A (the two proofs speak about one opening).** Let `(r, sigma)` be the
exact opening of `P_l` and `(r', sigma')` the relaxed one, with factor `c`.
If MSIS over `R_q` is hard at norm `||c r|| + ||r'||`, then `r' = c r` and
`sigma' = c sigma`.

*Proof.* `A1 (c r) = c (A1 r) = c · c1 = A1 r'`, so `c r - r'` is in the kernel
of `A1`. It is short: `r` is ternary, and a challenge is itself a difference of two
ternary polynomials of Hamming weight `NTRU_NONZERO`, so `||beta||_1 <= 2 ·
NTRU_NONZERO` and `||c||_1 <= 4 · NTRU_NONZERO = 56`, giving
`||c r||_inf <= 56`; and `r'` is short because the verifier checks its norm. By the assumption the difference is
zero, and the message row then gives `sigma' = c sigma`. []

This is where the single prime pays. The mix-net this proof came from cannot
run this step over `Z_q` at all — its exact proof is exact only per CRT
component, so `r` is ternary only componentwise and `c r` need not be short —
and it has to redo the argument modulo each prime, using `Pi_BND`'s norm bound
to get there. Here `r` is ternary as an integer polynomial and the step is the
ordinary one.

**Lemma B (the relation holds where `c` does not vanish).** Let `R_l` be the
residual of the `l`-th linear relation on the extracted openings. Extraction
gives `c R_l = 0`, so `R_l^(k) = 0` for every component `k` with `c^(k) != 0`.

*Proof.* Immediate, the product being componentwise. []

Write `S` for the set of components where `c` is non-zero. With `LIN_REPS`
repetitions the extractor obtains a factor `c_j` per repetition, and the
relations hold on the union `S_1 ∪ ... ∪ S_LIN_REPS`: the repetitions buy
coverage of components as well as soundness bits.

**Lemma C (the product identity gives a matching, per component).** Fix a
component `k` in `S`. If the telescoping relations hold there and the pass's
challenges `tau`, `mu` were drawn after the `D_i` were committed, then with
probability at least `1 - MSGS/q` over those challenges the multisets

    { (m_i^(k), i) }   and   { (m'_i^(k), v_i) }

coincide.

*Proof.* The relations chain into `prod_i a_i^(k) = prod_i b_i^(k)`. Read as
polynomials in two formal variables `T`, `M` over the field `Z_q`, the two
sides are products of `MSGS` linear factors; if the multisets of pairs differ,
the polynomials differ, and two distinct polynomials of total degree `MSGS`
agree at a uniformly chosen point with probability at most `MSGS/q`. The
challenges are a hash of the commitments, so they are not chosen by the prover
after the fact. []

**Theorem.** Suppose MSIS holds at the norm of Lemma A, the challenge
differences `c_j` do not all vanish in any component, and every pass accepts.
Then there is a single permutation `pi` with `m'_i = m_{pi(i)}`, and each `v_i`
lies in `D = {0, ..., MSGS - 1}`.

*Proof.* By Lemmas A and B the relations hold in every component. By Lemma C,
for each component `k` there is a bijection `psi_k` with
`(m'_i^(k), v_i) = (m_{psi_k(i)}^(k), psi_k(i))`. Comparing second coordinates
gives `v_i = psi_k(i)` in `Z_q`; since `MSGS < q` the indices are distinct
scalars, so `psi_k(i)` is determined by `v_i` and **does not depend on `k`** —
this is exactly what `sigma_i` being a ring *constant* buys, its value being
the same scalar in every component. Write `pi` for that common bijection. Then
`m'^(k)_i = m^(k)_{pi(i)}` for every `k`, hence `m'_i = m_{pi(i)}` in `R_q`.
Membership `v_i = pi(i) ∈ D` falls out of the same comparison rather than being
assumed. []

**Where the argument is incomplete.** One hypothesis is not discharged: that
the extracted challenge differences do not all vanish in some component. A
`beta` is a difference of two sparse ternary polynomials, and in a ring that
splits into `d` linear factors such an element can be a zero divisor; Corollary
1.2 of the usual reference is vacuous at this splitting. The same gap is open
in the mix-net, which records it as a known gap rather than closing it. Note
its shape here: a component in which *every* `c_j` vanishes is one in which the
argument says nothing at all about the list, so this is not a loss of a few
bits but a hole of unknown size. What would close it is either a challenge set
whose differences are invertible, or a bound on how many components a short
non-zero element can vanish in, applied across the `LIN_REPS` factors.

**What this says about `Pi_BND`.** The argument above does not use it. The
norm it needs on the linear proof's opening comes from that proof's own check,
and the exactness it needs comes from `Pi_SMALL` over a prime modulus. This is
the answer to the question raised in Section 4.3, and it is a negative
one: on this ring `Pi_BND` is not load-bearing for the permutation argument. It
still bounds what a committed constant can be, which is worth having — a
`v_i` outside `D` is ruled out above only *given* that every pass accepts,
whereas the norm bound rules it out unconditionally — and it is what the
sub-proof of the decryption phase will need. But nothing in Lemma 5's chain
rests on it, and a future version of this branch may reasonably drop it from
the shuffle.

## 7. Parameters

| | | |
| --- | --- | --- |
| `q` | ciphertext and commitment modulus | `2^59 + 16385`, prime, `= 1 mod 2d` |
| `d` | ring dimension | 2048, so `R_q` splits into 2048 components |
| `WIDTH, HEIGHT, SIZE` | commitment shape | 4, 1, 2; hiding needs `WIDTH > HEIGHT + SIZE` |
| `SHUFFLE_REPS` | passes of the product argument | 3 |
| `LIN_REPS` | repetitions per linear proof | 3 |
| `AEX_DEG`, `AEX_NR` | challenge extension of `Pi_SMALL` | 4, over `Y^4 - 5` |
| `ETA` | columns opened | 550, for `2^-128.2` |
| `AEX_COLS` | code length | `4N = 8192`, tied to `params::poly_big` |
| `NTI` | columns of `Pi_BND`'s response | 130, `>= LEVEL + 2` |
| `ANEX_E_INF` | last row's bound, short instance | `TAU`, the `sigma_i` reaching `MSGS` |

### 7.1 What the repair costs

Sizes per vote at `MSGS = 1000`, from the serialiser of `include/serial.h`
rather than from a model. What a pass costs is measured directly and is the
same at `MSGS = 4` and `MSGS = 64` — 156.3 KB a vote either way, the buffers
being per vote — so it carries to 1000 unchanged. What is sent once is measured
at 64 and scaled by the part of it that grows: `Pi_SMALL` is opened columns,
`ETA · V · (2 + 3 TAU) · 16` bytes of them, flat per vote once `TAU` tracks
`MSGS`; `Pi_BND` is `V · NTI` openings whose width grows with `sigma`.

| | per vote |
| --- | --- |
| `D_i` and `s_i`, three passes | 135.1 KB |
| responses of the linear proofs, three passes of three repetitions | 333.9 KB |
| `P_i`, the commitments to the `sigma_i` | 30.0 KB |
| `Pi_SMALL`, almost all opened columns | 133.4 KB |
| `Pi_BND` | 4.2 KB |
| **total** | **636.6 KB** |

**The openings are entropy-coded, which is worth 12% of them.** A masked
opening is a discrete Gaussian, and writing it at the width of the bound the
verifier checks spends 14 bits a coefficient where the distribution's entropy
is `log2(sigma sqrt(2 pi e))`, or 12.05. `serial::put_gauss` zigzags each
centred coefficient and Golomb-Rice codes it about its own width; measured, the
responses come to **12.4 bits a coefficient**, within 0.35 bits of the entropy.
That is 45 KB a vote off the total, and it applies to no other part of the
proof: commitments, published scalars and opened columns are all uniform, with
nothing to exploit.

The first messages of the linear proofs are not in the table because they are
not sent. Each of `t`, `tp`, `_t` and `u` is determined by the responses, the
commitments and the challenge, so the prover publishes only the hash its
challenges come from and the verifier rebuilds them and hashes them back. That
is the same check — the rebuilt `u` agrees with the prover's exactly when the
relation holds — for 32 bytes instead of four ring elements a repetition, and
it is what takes this proof from 1220 KB per vote to 681.

The same accounting applied to the shuffle as published — one pass, one linear
proof per message, two commitments in each, no entropy coding — gives 118 KB
against the 130 KB of Table 1 of the paper. Reproducing a published figure to
within a tenth is what says the convention here is the paper's own, so the
comparison below is a comparison of protocols rather than of spreadsheets.

**The repair costs about five times the proof size.** Three quarters of that is
repetition — three passes, and three repetitions of each linear proof, which
Section 5 derives from a 60-bit modulus and cannot be argued away at this
`LEVEL`. The rest is structural: a third commitment in every linear proof
because `b_i` is no longer public, and the two membership sub-proofs, of which
`Pi_SMALL`'s opened columns are 133 KB and flat per vote, since they scale with
`TAU` rather than with anything a single vote owns.

**Nearly half of it was the first messages, and they are gone.** They were
540 KB of the 1220, and sending them was never necessary. The obstacle is
circularity — the challenges are a hash of those first messages — and the way
out is to publish the hash, derive the challenges from it, rebuild the first
messages from the responses, and check the hash: `lin_hash` and `lin_chal` were
split for exactly this during the port. The three equations the verifier used
to test are now the definitions of what it rebuilds, and the binding is the
hash comparison; a response altered after the fact moves the rebuilt first
messages and fails it, which a test confirms.

## 8. What the port turned up

`Pi_SMALL` and `Pi_BND` were brought across from the mix-net of ePrint
2022/422. Adapting them to this ring surfaced five things, each of which would
have been a silent defect:

1. **`ETA = 452` is `2^-112` here**, not `2^-128`: the code length is `4N` and
   this ring's `N` is half. Now 550. Section 4.1.
2. **`AEX_COLS` was the literal 16384**, which is `4N` only for a ring of
   degree 4096. The encoder wrote 16384 entries into an 8192-entry transform.
   It is now `params::poly_big::degree`, with a `static_assert` that the
   message still fits.
3. **`Y^4 - 3` is reducible** over this `q`. Section 4.1.
4. **Two CRT fast paths assumed two moduli**, one of them behind a
   `static_assert(nmoduli == 2)`. With one prime there is nothing to recombine.
5. **A hash absorbed `16 * DEGREE` bytes per polynomial**, twice this ring's
   16384. Prover and verifier then derived different challenges from the same
   commitment. This was the third instance of that constant in this codebase:
   `ntru_pismall.cpp` had it before the port, and `src/pibnd.cpp` arrived with
   it.

Before the port, `pismall_verifier` in this repository checked the amortized
linear relation and the commitment opening, and nothing else: it never read the
codewords, the columns or the `beta` it derived, and `ETA` appeared only in the
prover's randomness. It could not have served as the membership half of Lemma
5, whatever its parameters.

## 9. Coverage, and what is not done

Fixed on `main` before this branch, and so not documented here: a memory-safety
defect that invalidated a proof, the NFLlib element-wise comparisons, the
keygen residue test, and ring inversion moving off FLINT.

`rho` was removed rather than repaired. It was a uniform shift the prover
subtracted from every message and commitment, and in `a_i` and `b_i` it entered
only beside the uniform challenge `mu`, so it added nothing `mu` did not
already give.

Open:

* Nothing here has run at the paper's `MSGS = 1000`. The largest exercised is
  64, with `NTI` at its real 130; peak memory there was under 400 MB, so 1000
  should be about 6 GB and hours rather than minutes.
* The zero-divisor hypothesis of Section 6: that the extracted challenge
  differences do not all vanish in some component. This is the one hypothesis
  of the theorem that is not discharged, and it is open in the mix-net too.
