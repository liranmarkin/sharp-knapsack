# The resolution lever: proof document (branch `resolution-lever`)

Supersedes the amortization machinery of `docs/beyond-n43.md` with one
mechanism.

## Theorem (candidate)

The Feng-Jin pipeline, run at a grid fine enough that the total
round-down error stays below one band width T/l, with the pruned
witness scan as the sampler, has total time

    O~( n^1.5  +  n * eps^-2 ),

uniformly in eps and in the popular-class parameter l. This is the
optimal shape for this framework: construction + output-optimal
sampling. It is <= every previous bound (Feng-Jin, PR #1, PR #2) for
all eps, strictly better than PR #2 on all eps in (n^{-1/2}, n^{-1/6}),
and closes the open sub-problems left by PR #2.

## The mechanism (one idea)

Feng-Jin couple the grid step to T/l^2, which makes the rounded count
over-shoot by 1/p = O~(n/l) and forces N = O~(n/(l eps^2)) samples.
The coupling is NOT forced by correctness - only by their query cost,
which READS arrays (O~(L sqrt(n)) per sample), so finer grids would
explode their sampling phase. Our pruned witness scan enumerates
LEVELS, never positions: per-sample O~(n_m), independent of array
length. That decouples the grid from sampling entirely:

1. Boost the grid by F = n/l (step ~ T/(l n polylog)). Total
   accumulated round-down error E < gap = T/l.
2. Round-down gives Omega subset Omega'; the excess lies in
   band(T, E) subset band(T, T/l), whose mass is O~(h)|Omega| by their
   Lemma 3.3 - machine-checked as `lemma_33`, resolution-free.
   Hence p >= 1/polylog and N = O~(eps^-2)   [`resolution_p_bound`].
3. Construction: per-merge O~(L sqrt(M)) (their Thm 6.1, parametric
   in L): summed, O~(F l sqrt(n)) = O~(n^1.5) at full crank -
   independent of l   [`boost_construction_ledger`].
4. Sampling: N x per-sample = O~(eps^-2 * n)   [`scan_ledger`].

No caches, no alias tables, no dyadic doubling: at eps^-2 samples the
plain scan is affordable.

## Machine-checked (standard axioms, build green)

`rounded_superset`, `rounded_band_split`, `bandSet_mono` (the sandwich),
`resolution_p_bound` (the p-bound, composed with `lemma_33`),
`boost_construction_ledger`, `scan_ledger`, and the composed headline
`fprasUniform` in `lean/SharpKnapsack/New/SamplerResolution.lean`.
Probe: `experiments/probe_resolution_lever.py` - overcount
1.97 -> 1.016 as the boost grows, subset property exact on every mask.

## Honest limits

1. At eps = Theta(1) the bound is O~(n^1.5), tying Feng-Jin - their
   #1.3 open problem, not claimed.
2. Space: boosted arrays cost O~(n^1.5) words - same order as their
   construction, but a larger constant/polylog than the unboosted
   pipeline.
3. Relied on, as published: their Thm 6.1 merge at boosted lengths
   (parametric in L), and the two-phase outer pipeline; the E_max
   error-accumulation constant (error per merge <= grid step, depth
   many merges) is prose + probe, same category as the cost-model
   seams of PR #1/#2.
4. The p-bound inherits `lemma_33`'s instance-side hypotheses
   (bounded-ratio popular class etc.) - Feng-Jin's own §3 setting,
   discharged the same way (their reduction + `params_choice`).
