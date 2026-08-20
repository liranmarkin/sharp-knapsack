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

## Design-phase findings (day 1)

### Barrier theorems (new, ours)

B1. RAMP HARDNESS. The breakpoint-merge-as-MinConv reduction requires
monotone MinConv with UNBOUNDED values (positions up to C), and adding
a linear ramp k*R makes any MinConv instance monotone - so
unbounded-monotone MinConv is general-MinConv-hard. JPSX n^{1.5+o(1)}
(bounded [n]-range) cannot apply as-is. The U2 wall is fundamental,
not technical.

B2. ATOM ISOLATION IS NP-HARD. Any scheme that isolates a narrow
capacity window around C (peeling annuli, quantized positions +
boundary recursion) bottoms out at approximating #{x : w*x = C'} -
and even DECIDING nonzero is Subset-Sum, so no FPTAS exists unless
P=NP. Sum approximations survive only because breakpoints count
cumulatively from zero; position-space is rigid at atoms in
principle, not just in technique. (Also checked: two-sided sum
approximations DO compose, and position-UP-rounding costs only one
(1+delta) value factor - but dense position-cells reduce back to the
same wall, consistent with B2.)

Also checked and closed: bounded-weight regimes are vacuous (exact DP
is polynomial there); halfspace-PRG enumeration gives only additive
error (useless for relative counting, known since GKM11).

### The live question: in-band crossing complexity

In the merge sweep, pair (k,l) with position-sum T = x_F(k)+x_G(l)
contributes meaningfully only if the cumulative at T is at most
r_{k+l+w} (w = O~(1/delta) accuracy band) - "crosses in-band". Pairs
crossing out-of-band are ignorable forever (proved: a pair always
crosses at cumulative >= delta*r_{k+l}, i.e. within w' BELOW its
diagonal; if by then the max has raced PAST k+l+w, the pair's mass is
band-negligible at all later times).

Define X(F, G, delta) = #in-band crossings. If worst-case
X = O~(s poly(1/delta)): the merge is subquadratic (aggregate
maintenance + pruned enumeration) and the GMW record falls. If
X = Theta(s^2): this wall joins B1/B2 and the merge is tight for
breakpoint representations. Budget arguments give s/delta^3 per output
step but do not exclude adversarial concentration. EMPIRICAL PROBE
FIRST, per methodology.

## Probe results (B3 settled) and the program forward

`experiments/probe_inband_crossings.py` (asserted, CI): the in-band
crossing number X is Theta(s^2) in the worst case - witness family:
ARITHMETIC positions with geometric values (x_k = c*k). There, the
cumulative's log tracks the diagonal index so closely that every pair
crosses in-band; growth factor exactly 4.00 under doubling s. Genuinely
wild families (doubling positions, heavy-tail random gaps) show
X ~ s*w - near-linear (growth 1.9-2.2). So the sweep alone cannot
break the s^2 merge; the wall B3 joins B1/B2.

### The dichotomy program (live, multi-week scale)

The quadratic witnesses are all additively STRUCTURED (unions of few
arithmetic progressions); the wild families have few in-band
coincidences. Conjectured engine, in algorithmic form:

  merge cost = O~( rho_F * rho_G + X_wild )   where rho = AP-cover
  number of the breakpoint sequence, and X_wild = in-band crossings
  outside AP-blocks.

- AP-block pairs merge in closed form: the block contribution is a
  geometric-weighted lattice-point sum under a line - computable in
  polylog by Euclid/continued-fraction recursion (Barvinok-style).
  This piece is concretely designable and Lean-able.
- High X forces additive energy, and high energy forces small AP-cover
  (Freiman / Balog-Szemeredi-Gowers). The needed statement is an
  ALGORITHMIC, DETERMINISTIC version - the machinery of
  Chan-Lewenstein (STOC'15 clustered 3SUM) is the closest published
  toolkit; their decompositions would enter as a `<PriorAuthors>/`
  reliance.
- Crude greedy maximal-run covers are NOT enough (probed: alternating
  gaps = union of 2 APs, but greedy sees s runs; interleaved AP-unions
  likewise) - the cover detector must find AP-unions, which is where
  the real difficulty lives.
- If the interpolation theorem holds with cover-vs-energy trade
  rho^2 + X = O~(s^{2-c}) for some c > 0, the GMW record falls to
  O~(n^{2.5-c'} eps^{-1.5+c''}). No such bound is claimed today.

### Honest status

No new deterministic record is claimed. Landed: the barrier map
(B1 ramp-hardness - machine-checked; B2 atom-isolation NP-hardness -
prose reduction; B3 - asserted probe with witness family), and the
dichotomy program with its first concrete sub-targets (closed-form
AP-block merge; deterministic AP-union covers).

## Night session: the curvature dichotomy (the program's engine, sharpened)

Probes landed tonight (`probe_pruned_merge.py`, `probe_fit_cover.py`,
`probe_relaxed_fit.py`, all asserted):

1. The multiplicative band-PRUNE (via deterministic (1+eta)-approx
   MinConv: scale-round + per-level boolean FFT, O~(s/eta)) handles
   CURVED families (doubling: X near-linear) and is defeated by
   near-arithmetic noise (random-gaps: X = s^2).
2. ORDER-EXACT piecewise-linear fits compress only structured families
   (rho linear-in-s on all noisy/wild ones).
3. RELAXED order-K fits (residual <= K*local-gap; each crossing rank
   shifts <= K; value error (1+delta)^K absorbed by schedule at
   poly(K) slowdown) crush diffusive noise: sorted sequences with
   concentrated increments are near-arithmetic - uniform-random
   positions fit with rho = 1 at K ~ sqrt(s); bounded noise likewise.
   Heavy tails (pareto-alpha < 2) are marginal (rho*K ~ const).
   Curvature (doubling) defeats fits at every K - and is prune-sparse.

### The conjectured theorem (curvature dichotomy)

Locally, at every scale: either second differences are LARGE relative
to gap scale (high curvature => diagonal minima are sharp => few
near-min band survivors => the prune is sparse there), or SMALL (=>
locally near-affine => relaxed-fit block, closed-form lattice-sum
merge). Both mechanisms are local; a scale-partition composes them.
Conjecture: adaptive merge cost O~(s * poly(1/delta)) worst-case, via
per-window min(fit, prune). Proof shape for the collision side:
t near-min cells on a diagonal force x-increments to match reversed
y-increments within window slack (matched gap-substrings); matches
across shifted diagonals compose into approximate self-periodicity =
fit structure. Elementary path - no BSG machinery required - but the
slack bookkeeping across scales is a real paper's worth of work.

If the dichotomy lemma lands, the GMW record falls to
O~(n^{1.5} eps^{-1} polylog)-scale (rebalancing the D&C with
near-linear merges; exact exponent TBD after the lemma's polylogs are
known). Reduction statement: RECORD <= DICHOTOMY LEMMA; everything
else (prune correctness via approx-MinConv-from-below, fit value-error
accounting, Pareto w=0 bound, closed-form lattice sums) is either
machine-checked already or mechanically formalizable.

### Heavy-tail gap regime (the one marginal case)

pareto-alpha, 1 < alpha < 2: fluctuation L^{1/alpha} vs K*gap:
rho ~ s/K^{alpha}... measured rho*K ~ const (alpha-1.2 -> exponent 1).
Candidate fix: exception-decomposition (arithmetic backbone + few
large-jump insertions; jumps beyond B number s*B^{-alpha}) - the
multi-resolution merge. Open within the program.

### End-to-end prototype finding (probe_adaptive_gmw.py)

Wired an adaptive merge into the repo's actual GMW implementation
(python/sharp_knapsack.py). Query-based adaptation - binary-searching
output crossings with per-entry threshold evaluation - costs 4.6x MORE
than the naive pairwise merge (out * s * log > s^2). Mass conservation
verified. Conclusion: the subquadratic win lives ONLY in the
closed-form block-pair lattice sums (polylog per fitted-segment-pair,
Euclid/continued-fraction recursion) - that engine is the program's
next engineering milestone, not query tricks.

## Night conclusion: B4 - the GMW merge is conditionally optimal (machine-checked)

`b4_merge_conditional_optimality` (New/DetBarriers.lean, standard
axioms): for ANY bounded integer sequences, the ramped encodings are
monotone and the value-sparsified position-EXACT merged frontier of the
encoded breakpoint lists determines every MinConv value of the original
instance. Combined with the PUBLISHED lower bound of Funke-Hespe-
Sanders-Storandt-Truschel (ESA 2023: exact Pareto sum has no O(n^{2-d})
under the MinConv hypothesis, even for linear output), and our
lit-survey (subagent report integrated below): the GMW merge step - as
a computational task - cannot be done in s^{2-c} worst-case unless the
MinConv hypothesis fails.

Escape routes, each now mapped and closed or bounded:
- position-approximate internal frontiers: B2 (atom isolation NP-hard);
  FJ-class band arguments give only polylog-factor deterministic
  approximations, not FPTAS;
- additive structure of positions: Jin-Xu (STOC 2023) - 3SUM stays
  hard on Sidon sets; input additive energy alone is not a lever;
- the weak-approximation toolkit (JPSX 2026 deterministic n^{1.5+o(1)}
  bounded-monotone MinConv; BC22; GKST SoCG'26 Pareto-sum equivalence):
  lives in the both-coordinates-slack world; strong FPTAS forbids
  capacity slack (B2).

HONEST SCOPE: B4 is a hardness statement about the MERGE TASK, i.e.
about every algorithm in the sum-approximation-merge framework (which
includes all known deterministic FPTASes: GKMSVV, SVV, RT, Halman,
GMW). It is NOT an unconditional lower bound for the PROBLEM: an
algorithm outside this framework is constrained by B2/Jin-Xu but not
excluded. Breaking the record now requires either refuting the MinConv
hypothesis or inventing a non-merge framework - both recognized-hard.

Constructive complement (the beyond-worst-case program): the curvature
dichotomy adaptive merge (probes landed) - subquadratic empirically on
every structured family; worst-case blocked by B4, as it must be.

## Full-verification pass (night 3)

Everything in the result is now Lean (New/DetReduction.lean; 20
theorems total across DetBarriers + DetReduction, all standard axioms):
the encoding of a MinConv instance as SparseFun lists; the identity
that the repo's own executable verified conv has the pair-sum double
sum as its cumulative; the 2^{wM} spread sandwich; exact and
SPARSIFIED block-logarithm read-off (against the very sparsify/conv
the verified fptas runs); bottom-padding placing every diagonal in the
upper half (with a third exclusion case - beyond-domain splits - that
the proof itself caught); the N-side ramp; and one composed statement
det_reduction_complete gluing pad + ramp + read-off with all
constructions explicit (detH/detR/detExt/detA/detB). B2's core
(approx_decides_subset_sum) and B3's witness (witness_all_inband) are
also machine-checked. Remaining non-Lean ingredients: exactly two
citations used as published (Funke et al. ESA'23 lower bound; the
MinConv hypothesis) plus Subset-Sum NP-hardness - all prior work,
named per law 2.
