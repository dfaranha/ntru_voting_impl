from math import sqrt
vname = "ntru_ballot"
# The voter's proof of a well-formed ballot (src/ntru_ballot.c), for LaZer's
# lin-codegen.sage, stated over LaZer's own ring R_64 = Z_q[Y]/(Y^64 + 1), q the
# NTRU prime. R_q of degree 2048 is R_64[X]/(X^32 - Y), an element a being
# sum_r X^r a_r(Y); a vote for candidate j is X^(32 j) = Y^j, in piece 0 alone.
# With witness w = (s_0..s_31, e_0..e_31, u, m, m'):
#
#   c_r = (2 h s)_r + 2 e_r + [r = 0] m      for r < 32
#   0   = m - u
#   0   = Y^(64 - NCAND) m - m'
#
# with (s, e) short, ||u|| <= 1 and m, m' binary, so m is Y^j or 0, a vote for
# one candidate or none. The last row bounds j: R_64 is negacyclic, so
# Y^(64 - NCAND) Y^j is Y^(64 - NCAND + j), binary, when j < NCAND, and
# -Y^(j - NCAND), not binary, when j >= NCAND. NCAND is a coefficient of A, set
# at run time; the parameters here do not depend on it.
deg   = 64
mod   = 576460752303439873
dim   = (34, 67)
wpart = [list(range(64)), [64], [65, 66]]
# ZO_dist: each coefficient of s and e is +-1 with probability 1/2, so
# ||(s, e)||^2 is about 2048, 32 standard deviations below 1.2^2 * 2048.
wl2   = [1.2*sqrt(2*2048*0.5), 1, 0]
wbin  = [0, 0, 1]
wlinf = 1
# LaZer's default target, a root Hermite factor of 1.0044, is about 102 bits
# under the lattice-estimator here; 1.0036 asks for more (see the header).
DELTA_TARGET = 1.0036
