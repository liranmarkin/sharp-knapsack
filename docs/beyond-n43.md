# The amortized witness sampler: proof document (branch `beyond-n43`)

Refines `docs/witness-sampler.md`. One algorithmic change, one new ledger
mode, a strictly dominating bound.

## Theorem (candidate)

The witness sampler can be run with per-(node, position) alias caches so
that the total time is

    Õ( n^1.5  +  min(n^{4/3}·ε⁻², n^{1.5}·ε⁻¹)  +  n·ε⁻² ).

This is ≤ the previous bound Õ(n^1.5 + n^{4/3}ε⁻²) for every instance
and every ε, strictly below it for every ε < n^{-1/6}, and equal to the
output-optimal Õ(n·ε⁻²) once ε ≤ n^{-1/2}.

## The change

The split-draw at node `u` with position `s` samples over the active
level rectangles - previously enumerated afresh (Õ(min(M_u, L_u)) per
draw). Observation: **the position `s` is an index into u's stored
array, so at most `L_u` distinct (u, s) pairs ever occur - however many
times u is visited.** On the first visit to (u, s), build an alias table
over the active rectangles (Õ(M_u): ≤ M_u rectangles, masses in polylog
from the correlation tables) and cache it; every later draw at (u, s)
costs polylog.

## The ledger

Sampling = cache builds + draws:
- draws: N·k·polylog = Õ(n·ε⁻²)          (pruned visits, polylog each);
- builds: Σ_u min(N_u, L_u)·M_u, bounded both by
  (B) Σ_u N_u·M_u = Õ(n²/(ℓε²))            (rebuild every visit), and
  (C) Σ_u L_u·M_u = Σ_h 2^h·(ℓ/2^{h/2})·(n_m/2^h) = Õ(ℓ·n)   (ε-free);
- the old scan mode (A) = Õ(n√ℓ·ε⁻²) remains available per node, so the
  algorithm is never slower than before.

max over ℓ of min(A, B, C): for ε ≥ n^{-1/6} the old worst case
ℓ = n^{2/3} gives n^{4/3}ε⁻² (mode C inactive); for ε < n^{-1/6} the
worst case moves to the B = C crossover ℓ* = √n/ε and gives n^{1.5}/ε.

Machine-checked (branch `beyond-n43`, `lake build` green, standard
axioms): `cache_ledger` (mode C sums to ≤ 4·L·M), `cache_collapse`
(min(n²E/ℓ, nℓ)² ≤ n³E - the n^{1.5}√E exponent), and the composed
headline `fprasSharper` (= `fprasSharp`'s correctness and enumeration
modes ∧ cacheLedger ≤ 32·ℓ·n ∧ N·k ≤ 8·n·E). Probe:
`experiments/probe_cache_ledger.py` - the distinct-position bound holds
and the amortization win grows with N (18.5× at N = 4·10⁴).

## The v2 sharpening: the rectangle count is array-bounded

A build at (u, s) enumerates the active rectangles - and their number is
at most min(M_u, L_u), NOT M_u: every level present in the array
occupies at least one of its L_u cells. Re-summing mode C with the min:

  - deep levels (M below L): the old geometric tail, ≤ ℓ·n_m/2^{h*/2} = ℓ²;
  - shallow levels (M above L): 2^h·(ℓ/2^{h/2})² = ℓ² per level, ×polylog levels.

Mode C' = Õ(ℓ²) per class, Õ(ℓ²) overall (polylog classes) - free of
BOTH ε and n. Collapse against mode B: n²/(ℓε²) = ℓ² at
ℓ = (n²/ε²)^{1/3}, value (n⁴/ε⁴)^{1/3} = n^{4/3}·ε^{-4/3}, capped by n²
when ℓ hits its 8n ceiling. Total:

    Õ( n^1.5  +  min(n^{4/3}·ε^{-4/3}, n²)  +  n·ε⁻² ).

Strictly below n^{4/3}ε⁻² for EVERY ε < 1; flat Õ(n^1.5) for all
ε ≥ n^{-1/8}; output-optimal n·ε⁻² once ε ≤ n^{-1/2}.

Machine-checked: `cache_ledger2`, `cache_collapse2`, and the composed
headline `fprasSharpest` (all standard axioms, build green).

## The v3 mode: lazy dyadic block-merges

Dead end 1 above (prefix-window queries have no small certificate)
has a batch escape: precompute their Theorem 6.1 merge on dyadic
sub-blocks of the left child. For block B, store C_B(s) and W_B(s); the
exact identity (Lean: `block_split_exact`)

    W(s) = [C_B1(s) = C(s)]*W_B1(s) + [C_B2(s) = C(s)]*W_B2(s)

lets a draw binary-search down the block tree in polylog per level.
A full block tree is unaffordable (2^d * L per depth - the wall again),
but LAZY DOUBLING - deepen a node only as its visits double, keeping
4^d <= visits - balances build against draw at L*sqrt(visits) per node.
Tree total: mode D = O~(l*sqrt(N*k)) (Lean: `dyadic_ledger`). Collapse
against the rebuild mode (Lean: `cache_collapse3`): balance at value
n^{5/4} * eps^{-3/2}. Final total, taking the best mode per l:

    O~( n^1.5 + min(n^{5/4} eps^{-3/2}, n^2) + n eps^-2 ).

Strictly below v2 for every eps in (n^{-1/2}, 1); flat O~(n^1.5) for
all eps >= n^{-1/6}; output-optimal n eps^-2 once eps <= n^{-1/2}.
Probe: v3 constants are real (~10x per node) - its win regime needs
sqrt(N*k) well under l, exactly as the ledger says; there it beats v2
by a factor growing with N (4.2x measured).

## Honest limits

1. At ε = Θ(1) the total still ties Feng-Jin at Õ(n^1.5) (construction
   cost). Improving THAT is the field's stated open problem
   (near-linear FPRAS; the (max,+) frontier) - not claimed.
2. Space rises to Õ(min(N·n, ℓ²)) words for the caches (n^{4/3}ε^{-4/3}
   at the worst-case ℓ) - a genuine trade-off.
3. The residual ε-term min(n^{5/4}ε^{-3/2}, n²) sits at the B = D
   crossover; the next open sub-problem is answering a fresh position's
   witness-structure query below the L·√(visits) doubling balance -
   e.g. block-merges whose cost scales with the block, not the output.
4. Cost unit unchanged: the witness-oracle machinery of Feng-Jin's
   Theorem 6.1, used as published.
