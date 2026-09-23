# More Efficient Post-Quantum Electronic Voting from NTRU 

Code accompannying the paper "More Efficient Post-Quantum Electronic Voting from NTRU" (Submission #10) for CiC 2024. 

Dependencies are the [NFLlib](https://github.com/quarkslab/NFLlib) and [FLINT](https://flintlib.org/doc/) libraries.
NFLLib is already included in this repository, but instructions for installing its dependencies can be found in the link above.
FLINT is usually included in package managers and can be easily installed in most systems out there; version 3.1 or later is required, since the code uses the `flint_rand_init()` spelling introduced there.

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

For building the actual code, run `make` inside the source directory. This will build the binaries for `ntru_bdlop`, `ntru`, `ntru_pismall`, `ntru_pibnd` and `ntru_shuffle` to test and benchmark different modules of the code.

The published parameters need tens of gigabytes of memory, so the sizes that dominate the cost can be overridden at build time through `CONFIG`, which is passed to every compilation:

```
$ make clean
$ make CONFIG="-DMSGS=4 -DTAU=8 -DBENCH=1"
```

`MSGS` is the number of messages in the shuffle and `TAU` the number of relations the membership proof is amortized over, which must be a power of two. `BENCH` and `TESTS` set how many times each benchmark and test is run. A build records its `CONFIG` in `obj/.config`, so changing it rebuilds the objects that bake it in rather than silently linking objects compiled at the old size.

The binaries respectively implement the BDLOP commitment scheme, the distributed NTRU cryptosystem, the exact proof of smallness, the amortized norm proof and the shuffle itself. The last two are the membership sub-proofs of Lemma 5 of [ePrint 2025/658](https://eprint.iacr.org/2025/658): the shuffle proves a permutation by a product over pairs `(m_i, g(i))`, and the elements `sigma_i` it pairs the output with are committed, proved to be ring constants by `ntru_pismall` and proved short by `ntru_pibnd`. Without them the product identity is satisfied by a list that is permuted differently in each of the `d` fields the ring splits into, which is not a permutation at all; `ntru_shuffle` carries tests that exhibit that attack and its rejection. Tests and benchmarks are included for each of them, such that they can be used independently. NFLlib is quite memory-hungry due to being a template library, so we recommend to adjust the stack size with `ulimit -s unlimited` to avoid crashing in the largest benchmarks.

__WARNING__: This is an academic proof of concept, and in particular has not received code review. This implementation is NOT ready for any type of production use.
