# Beating GMW: deterministic FPTAS below O~(n^2.5 eps^-1.5)

Branch: `det-fptas`. Target: the deterministic #Knapsack FPTAS record -
GMW (ICALP 2018, arXiv 1802.05791), O(n^2.5 eps^-1.5 log(n/eps) log(n eps)),
held since 2018 (confirmed 2026-08-20: Feng-Jin 2410.22267 still cite it
as the deterministic SOTA; no newer work found).

## The GMW cost ledger (full read of the 14-page paper)

Framework: sum approximations. F is a (1+eps)-SUM approximation of f if
F^<= approximates f^<= pointwise multiplicatively. Closed under +, shift,
convolution ((1+eps)^2), and Sparsify(delta) compresses any F to
s = log_{1+delta} M <= n/delta breakpoints (M <= 2^n).

Algorithm: balanced D&C. |S| > sqrt(n/eps): split in half, recurse,
merge = CONVOLUTION of the two sparse lists + sparsify at
delta_i = eps^{3/4}/(2c 2^{i/2} n^{1/4}). |S| <= sqrt(n/eps):
Halman-style linear insertion at delta = Omega(sqrt(eps/n)).

| piece | cost | where |
|---|---|---|
| merge at depth i | s_{i+1}^2 log, s_i = (n/2^i)/delta_i | naive pairwise products of sparse lists |
| per level total | n^2.5 eps^-1.5 log | EVERY level pays the same |
| base case | n^2.5 eps^-1.5 total | sqrt(n eps) copies of Halman on sqrt(n/eps) items |
| levels | log(n eps) | |

THE bottleneck, unambiguously: the merge computes all |F|x|G| pairwise
products and then throws almost all of them away (sparsify back to s
points). Everything else is balanced bookkeeping. Any merge in s^c time,
c < 2, improves the total polynomially.

## The attack: breakpoint merges via deterministic monotone MinConv

After Sparsify(delta), a list is determined by its breakpoint sequence
x_1 <= ... <= x_s: positions where F^<= crosses the value grid
r_j ~ (1+delta)^j. Values are implicit (grid-indexed). Two observations:

1. MAX-TERM STRUCTURE. (F*G)^<=(y) is dominated by the block pair (k,l)
   maximizing k+l subject to x_F(k)+x_G(l) <= y. The output breakpoint
   y_m = min_{k+l=m} (x_F(k)+x_G(l)) is a MIN-PLUS CONVOLUTION of the
   two monotone breakpoint sequences. Deterministic monotone MinConv is
   n^{1.5+o(1)} - Jin-Park-Saha-Xu, arXiv 2605.07150 (May 2026!),
   explicitly advertised for knapsack derandomization. RELY-ON candidate.
2. NEAR-MAX CORRECTION. The max term alone loses a factor up to s
   (sum of s cells vs max cell) - a (1+delta)^{log_{1+delta} s} error,
   unacceptable. Fix (our mechanism): cells on anti-diagonal k+l=d all
   have value ~ delta^2 r_d (grid multiplicativity r_k r_l = r_{k+l} for
   exact powers) - so (F*G)^<=(y) ~ delta^2 sum_d r_d c_d(y) where
   c_d(y) = #{k: x_F(k)+x_G(d-k) <= y}: only the top O(log_{1+delta} s)
   = O~(1/delta) diagonals matter for (1+delta)-accuracy. Counting
   near-max diagonal cells under a position threshold - deterministic,
   offline-sortable: O~(s/delta) per merge, plus the MinConv s^{1.5+o(1)}.

Candidate merge cost: s^{1.5+o(1)} + O~(s/delta), replacing s^2.

## Open design questions (the research program)

U1. [RESOLVED] Det monotone MinConv: n^{1.5+o(1)} (JPSX 2605.07150).
    Need the exact theorem: monotone requirement, value-range bound
    ([n^mu] variants exist), rectangular forms. Read the paper.
U2. Value-range reduction: breakpoint positions are capacities up to C -
    unbounded. Monotone-unbounded -> bounded via block-splitting /
    rectangular MinConv (the ESA'24 balancing toolkit) or via a
    class/window decomposition. Design needed. This is where FJ's class
    structure may re-enter deterministically.
U3. Exact error accounting for the diagonal-value claim: after
    Sparsify, block masses are F_k = f~^<=(x_k)-f~^<=(x_{k-1}) in
    [r_k - r_{k-1}, ...] - NOT exactly delta r_k. Need the merge to work
    with (1+O(delta))-approximate cell values - seems fine (absorb into
    schedule) but must be written carefully.
U4. Rebalance the D&C + base case for merge cost s^{1.5} + s/delta.
    Quick estimates give total in the n^{1.75}-n^2 eps^-1..1.5 range
    depending on how U2 resolves; even a weak c < 2 merge beats SOTA.
    The bottom of the recursion dominates; the Halman base case likely
    shrinks or disappears.
U5. Integer version (Theorem 2 of GMW) - port after the 0/1 case lands.

## Barrier map

- Randomized comparison floor: Dyer's n^{2.5}-era is passed; FJ/our
  FPRAS at n^{1.5} is the randomized frontier - no deterministic
  obstruction known above it. The det construction inherits the
  MinConv frontier: n^{1.5+o(1)} per length-s merge is today's wall.
- The eps-dependence floor: sparsified lists NEED s ~ n/delta points at
  the top; any breakpoint-based method pays s per level. Sub-eps^{-1}
  total looks blocked without abandoning breakpoints.

## Assets

- The repo's `Complexity.lean` IS a machine-checked GMW development
  (`fptas`, SparseFun namespace) - sum-approximation primitives may be
  reusable directly for the New/ folder.
- lemma_33 etc. (FengJin/) if class windows re-enter via U2.
