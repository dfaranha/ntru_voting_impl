CPP      = g++

# NFLlib predates C++20 and uses std::allocator<void>::const_pointer, which was
# removed in that standard, so the language level has to be pinned. The GNU
# dialect is required for the `Q` suffix on __float128 literals in param.h.
STD      = -std=gnu++17

# A params::poly_q is 32 KiB, so it is very easy to write a function whose
# locals silently overflow the stack. Fail loudly instead: 4 MiB is half the
# usual default limit, and every function here is well under it.
WARN     = -Wall -Wframe-larger-than=4194304
OPT      = -O3 -march=native -mtune=native -flto
INCLUDE  = -I NFLlib/include/ -I NFLlib/include/nfl -I NFLlib/include/nfl/prng -I include
DEFINE   = -DNFL_OPTIMIZED=ON -DNTT_AVX2
# Extra defines for a build, e.g. make CONFIG="-DMSGS=4 -DTAU=8 -DBENCH=1" to
# shrink the proofs enough to run them on a machine without tens of gigabytes
# of RAM. TAU must stay a power of two.
CONFIG   =
CFLAGS   = $(STD) $(OPT) $(WARN) -ggdb $(INCLUDE) $(DEFINE) $(CONFIG) -MMD -MP

LIBS     = deps/libnfllib_static.a -lgmp -lmpfr -lquadmath
# FLINT is a system library here, but CI builds its own, so keep the flags in
# one variable that a build can override. Only ntru_pismall needs it now that
# ring inversion goes through the NTT slots rather than a dense FLINT
# polynomial; everything else works through NFLlib alone.
FLINT    = -lflint

OBJ      = obj
BIN      = ntru ntru_bdlop ntru_pibnd ntru_pismall ntru_shuffle

# The first rule below is the config stamp, and its target contains a slash, so
# make would take it as the default goal and a bare `make` would build nothing.
.DEFAULT_GOAL := all

# The objects bake SIZE, MSGS and TAU in, and make has no way to notice that
# CONFIG changed since they were built: it compares timestamps against the
# sources, which have not moved. Without this, building at one MSGS and then
# another silently links objects compiled for the first. Record CONFIG in a
# stamp that every object depends on, rewritten only when it actually changes
# so that repeated builds at the same settings still do nothing.
STAMP    = $(OBJ)/.config
.PHONY: FORCE
$(STAMP): FORCE | $(OBJ)
	@printf '%s' '$(CONFIG)' | cmp -s - $@ 2>/dev/null || printf '%s' '$(CONFIG)' > $@

BLAKE3_SRC = src/blake3/blake3.c src/blake3/blake3_dispatch.c \
             src/blake3/blake3_portable.c \
             src/blake3/blake3_sse2_x86-64_unix.S \
             src/blake3/blake3_sse41_x86-64_unix.S \
             src/blake3/blake3_avx2_x86-64_unix.S \
             src/blake3/blake3_avx512_x86-64_unix.S
BLAKE3   = $(OBJ)/blake3.o
COMMON   = $(OBJ)/test.o $(OBJ)/bench.o $(OBJ)/cpucycles.o

.PHONY: all clean
.SECONDARY:

all: $(BIN)

$(OBJ):
	mkdir -p $(OBJ)

# Support code, compiled once and shared by every binary.
$(OBJ)/%.o: src/%.c $(STAMP) | $(OBJ)
	$(CPP) $(CFLAGS) -c $< -o $@

$(OBJ)/%.o: src/%.cpp $(STAMP) | $(OBJ)
	$(CPP) $(CFLAGS) -c $< -o $@

# BLAKE3 is bundled as a mix of C and assembly; keep it in a single object.
$(BLAKE3): $(BLAKE3_SRC) | $(OBJ)
	$(CPP) $(CFLAGS) -r -nostdlib $(BLAKE3_SRC) -o $@

# The commitment scheme's own tests and benchmarks. Built at SIZE = 2 because
# its second test commits to two messages and folds one into the other, which
# is what a single-message build cannot exercise; the library objects above are
# built at the SIZE their own binary needs.
ntru_bdlop: src/ntru_bdlop.cpp $(COMMON) $(STAMP)
	$(CPP) $(CFLAGS) -DSIZE=2 -DMAIN src/ntru_bdlop.cpp $(COMMON) -o $@ $(LIBS)

# The amortized norm proof, and the instance the proof of shuffle links: the
# openings of its MSGS commitments to the sigma_i. The Makefile selects that
# one with -DPIBND_SHORT and src/pibnd.cpp derives what follows from it.
$(OBJ)/pibnd-short.o: src/pibnd.cpp $(STAMP) | $(OBJ)
	$(CPP) $(CFLAGS) -DPIBND_SHORT -c $< -o $@

ntru_pibnd: src/pibnd.cpp $(OBJ)/sample_z_small.o $(OBJ)/sample_z_large.o \
		$(COMMON) $(BLAKE3) $(STAMP)
	$(CPP) $(CFLAGS) -DMAIN src/pibnd.cpp $(OBJ)/sample_z_small.o \
		$(OBJ)/sample_z_large.o $(COMMON) $(BLAKE3) -o $@ $(LIBS)

ntru: src/ntru.cpp $(OBJ)/sample_z_small.o $(COMMON) $(BLAKE3) $(STAMP)
	$(CPP) $(CFLAGS) -DMAIN src/ntru.cpp $(OBJ)/sample_z_small.o \
		$(COMMON) $(BLAKE3) -o $@ $(LIBS)

# pismall as a library, for the proof that each committed sigma_i is a ring
# constant. It is amortized over exactly the MSGS commitments the shuffle has,
# rounded up to the power of two its interpolation nodes need, and takes the
# shape of a commitment equation rather than the mix-net's own.
$(OBJ)/pismall-const.o: src/ntru_pismall.cpp $(STAMP) | $(OBJ)
	$(CPP) $(CFLAGS) -UTAU -DTAU='AEX_PAD2(MSGS)' -c $< -o $@

ntru_pismall: src/ntru_pismall.cpp $(OBJ)/ntru_bdlop.o $(COMMON) $(BLAKE3) \
		$(STAMP)
	$(CPP) $(CFLAGS) -DMAIN src/ntru_pismall.cpp \
		$(OBJ)/ntru_bdlop.o $(COMMON) $(BLAKE3) -o $@ $(LIBS) $(FLINT)

ntru_shuffle: src/ntru_shuffle.cpp $(OBJ)/ntru_bdlop.o $(OBJ)/pismall-const.o \
		$(OBJ)/pibnd-short.o $(OBJ)/sample_z_small.o $(OBJ)/sample_z_large.o \
		$(COMMON) $(BLAKE3) $(STAMP)
	$(CPP) $(CFLAGS) -DMAIN src/ntru_shuffle.cpp $(OBJ)/ntru_bdlop.o \
		$(OBJ)/pismall-const.o $(OBJ)/pibnd-short.o $(OBJ)/sample_z_small.o \
		$(OBJ)/sample_z_large.o $(COMMON) $(BLAKE3) -o $@ $(LIBS) $(FLINT)

clean:
	rm -rf $(OBJ) $(BIN) *.d

# The object rules drop their dependency files in $(OBJ); the rules that compile
# and link a binary from its source in one step drop theirs next to the binary,
# in the working directory. Both sets have to be included or editing a header
# leaves the binaries stale, which is silent and costs a debugging session.
-include $(wildcard $(OBJ)/*.d) $(wildcard *.d)
