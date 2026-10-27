from math import sqrt
vname = "ntru_ballot"
# The voter's proof of a well-formed ballot (src/ntru_ballot.c), for LaZer's
# lin-codegen.sage. The statement over R_q, q the NTRU prime and degree 2048:
#
#   c = 2 h s + 2 e + m
#   0 = m - u
#
# with witness w = (s, e, u, m): (s, e) short, ||u|| <= 1 and m binary, so m is
# X^j or 0, a vote for one candidate or none.
deg   = 2048
mod   = 576460752303439873
dim   = (2, 4)
wpart = [[0, 1], [2], [3]]
# ZO_dist: each coefficient of s and e is +-1 with probability 1/2, so
# ||(s, e)||^2 is about 2048, 32 standard deviations below 1.2^2 * 2048.
wl2   = [1.2*sqrt(2*2048*0.5), 1, 0]
wbin  = [0, 0, 1]
wlinf = 1
# LaZer's default target, a root Hermite factor of 1.0044, is about 102 bits
# under the lattice-estimator here; 1.0036 gives MLWE 136.1 and MSIS 141.3.
DELTA_TARGET = 1.0036
