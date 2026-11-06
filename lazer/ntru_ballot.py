from math import sqrt
vname = "ntru_ballot"
# The voter's proof of a well-formed ballot (src/ntru_ballot.c), for LaZer's
# lin-codegen.sage. The statement over R_q, q the NTRU prime and degree 2048:
#
#   c = 2 h s + 2 e + m
#   0 = m - u
#   0 = X^(2048 - NCAND) m - m'
#
# with witness w = (s, e, u, m, m'): (s, e) short, ||u|| <= 1 and m, m' binary,
# so m is X^j or 0, a vote for one candidate or none. The last row bounds j:
# the ring is negacyclic, so X^(2048 - NCAND) X^j is X^(2048 - NCAND + j),
# binary, when j < NCAND, and -X^(j - NCAND), not binary, when j >= NCAND.
# NCAND is a coefficient of A, set at run time; the parameters here do not
# depend on it.
deg   = 2048
mod   = 576460752303439873
dim   = (3, 5)
wpart = [[0, 1], [2], [3, 4]]
# ZO_dist: each coefficient of s and e is +-1 with probability 1/2, so
# ||(s, e)||^2 is about 2048, 32 standard deviations below 1.2^2 * 2048.
wl2   = [1.2*sqrt(2*2048*0.5), 1, 0]
wbin  = [0, 0, 1]
wlinf = 1
# LaZer's default target, a root Hermite factor of 1.0044, is about 102 bits
# under the lattice-estimator here; 1.0036 gives MLWE 136.7 and MSIS 135.8.
DELTA_TARGET = 1.0036
