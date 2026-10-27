# More Efficient Post-Quantum Electronic Voting from NTRU 

Code accompannying the paper "More Efficient Post-Quantum Electronic Voting from NTRU" (Submission #10) for CiC 2024. 

Dependencies are the [NFLlib](https://github.com/quarkslab/NFLlib) and [FLINT](https://flintlib.org/doc/) libraries.
NFLLib is already included in this repository, but instructions for installing its dependencies can be found in the link above.
FLINT is usually included in package managers and can be easily installed in most systems out there; version 3.1 or later is required, since the code uses the `flint_rand_init()` spelling introduced there.
The voters' ballot proofs use [LaZer](https://github.com/lazer-crypto/lazer), the submodule `third_party/lazer` (branch `skip-zeros` of [this fork](https://github.com/dfaranha/lazer), with fixes and speed-ups); fetch it with `git submodule update --init third_party/lazer`. The first `make` of `ntru_voting` builds it, HEXL included, and it needs MPFR.

### Building dependencies

To build NFLLib, run the following inside a cloned version of this repository:

```
$ mkdir deps
$ cd deps
$ cmake ../NFLlib -DCMAKE_BUILD_TYPE=Release -DNFL_OPTIMIZED=ON
$ make
$ make test
```
### Building and running the code

For building the actual code, run `make` inside the source directory. This will build the binaries for `ntru_bdlop`, `ntru`, `ntru_pismall`, `ntru_pibnd` and `ntru_shuffle` to test and benchmark different modules of the code, and `ntru_voting`, which runs the mix-net end to end.

The published parameters need tens of gigabytes of memory, so the sizes that dominate the cost can be overridden at build time through `CONFIG`, which is passed to every compilation:

```
$ make clean
$ make CONFIG="-DMSGS=4 -DTAU=8 -DBENCH=1"
```

`MSGS` is the number of messages in the shuffle and `TAU` the number of relations the membership proof is amortized over, which must be a power of two. `BENCH` and `TESTS` set how many times each benchmark and test is run. A build records its `CONFIG` in `obj/.config`, so changing it rebuilds the objects that bake it in rather than silently linking objects compiled at the old size.

The binaries respectively implement the BDLOP commitment scheme, the distributed NTRU cryptosystem, the exact proof of smallness, the amortized norm proof and the shuffle itself. The last two are the membership sub-proofs of Lemma 5 of [ePrint 2025/658](https://eprint.iacr.org/2025/658): the shuffle proves a permutation by a product over pairs `(m_i, g(i))`, and the elements `sigma_i` it pairs the output with are committed, proved to be ring constants by `ntru_pismall` and proved short by `ntru_pibnd`. Without them the product identity is satisfied by a list that is permuted differently in each of the `d` fields the ring splits into, which is not a permutation at all; `ntru_shuffle` carries tests that exhibit that attack and its rejection. Tests and benchmarks are included for each of them, such that they can be used independently. NFLlib is quite memory-hungry due to being a template library, so we recommend to adjust the stack size with `ulimit -s unlimited` to avoid crashing in the largest benchmarks.

`ntru_voting` puts them together, with `MSGS` voters, 4 mix servers and 4
trustees: the trustees share an NTRU key; each voter encrypts a vote for one of 8
candidates and proves the ballot well formed, which the board checks (below);
each mix server in turn re-encrypts every ciphertext with a fresh
encryption of zero, commits to that encryption of zero and adds the input into
the commitment, which makes it a commitment to the re-encryption, and publishes
the re-encryptions permuted with a proof of shuffle over those commitments; and
the trustees' partial decryptions of the last list are combined and tallied. It
also checks that a ballot proof moved to another voter or kept for a changed
ciphertext is rejected, that a ballot for two candidates cannot be proven, and
that a mix server that changes an output, or replaces a ballot with one of its
own, is rejected. What this branch does not implement is not in it: the proof
that each re-encryption adds an encryption of zero with short randomness, and
the trustees' proofs of correct decryption.

The ballot proof (`src/ntru_ballot.c`) shows, with LaZer's linear proofs, that
c = 2hs + 2e + m with s, e ternary and short and m = X^j or 0: one vote or
none. It proves m binary and equal to a u with ||u|| <= 1, which leaves only
those. It is bound to the election and the voter, so it cannot be copied to
another voter's ballot. LaZer lifts the statement to its ring of degree 64 and
an 84-bit proof modulus; `lazer/ntru_ballot.py` describes it, and
`lazer/ntru_ballot.h` is generated from it, from `third_party/lazer/scripts`,
with `sage lin-codegen.sage ../../../lazer/ntru_ballot.py >
../../../lazer/ntru_ballot.h`. LaZer's default target, a root Hermite factor
of 1.0044, is about 102 bits under the lattice-estimator here, so the file asks
for 1.0036: MLWE 136.1 and MSIS 141.3 bits, knowledge error 2^-127. The proof
is about 44 KiB.
`make CONFIG=-DMSGS=25 ntru_voting` runs the same election size as the
end-to-end tests of the other codebases, 25 voters and 8 candidates, in about
55 seconds, about 33 of them the ballot proofs (0.8 s to prove and 0.5 s to
check each, on a laptop); `-DNCAND=<n>` and `-DMIXERS=<n>` set the candidates and the mix
servers.

__WARNING__: This is an academic proof of concept, and in particular has not received code review. This implementation is NOT ready for any type of production use.
