# Formal verification roadmap: the witness-sampler FPRAS

Goal: machine-check the full result of `witness-sampler.md` in Lean, the way
`main` verifies the FPTAS. Staged so every stage is a complete, buildable,
meaningful theorem; later stages depend only on earlier ones.

- [x] **Stage 0 - core lemmas** (`WitnessSampler.lean`, done): the exact
  witness factorization, δ-domination, lazy amortization, ledger collapse.
- [x] **Stage A - exact sampler is uniform** (`SamplerExact.lean`, done): model
  outcomes as Boolean masks; define the recursive split sampler's mass
  function over exact count arrays; prove it equals the uniform distribution
  over solutions (root ≤-draw + exact-sum recursion; `splitMass_spec`,
  `samplerMass_spec` - standard axioms only). Pure finite ℚ arithmetic, no
  measure theory. A.2 (done): the ∅-split pruning equality
  (`splitMassP_eq`) and totality (`samplerMass_total`, via the enumeration
  bridge `allMasks_countP` tying masks to the trusted `count` spec).
- [x] **Stage B - approximate arrays: L1/TV bound** (`SamplerApprox.lean`,
  done): the kernel-parametrized sampler `splitMassK`; the damage-control
  theorem `splitMassK_l1` (per-node kernel error η costs at most
  η · #internal nodes in L1, telescoped by a hybrid argument); the
  assembled root bound `samplerMassK_l1`; and the local kernel lemma
  `kernel_l1_of_approx` (a (1±δ)-perturbed, witness-restricted kernel with
  γ dropped mass has L1 error ≤ 4δ + 3γ - the shape Stage 0's domination
  provides). Standard axioms only.
- [x] **Stage C - the estimator** (`SamplerEstimator.lean`, done): finite
  product measures over sample vectors (`prodMass_total`), mean and
  variance of the empirical sum with the independence cross-term vanishing
  (`sum_dev_zero`, `sum_sq_dev`), the Chebyshev tail bound
  `estimator_chebyshev` (≤ 1/(4Na²) for indicators - the ε⁻² engine), and
  robustness: product-measure L1 subadditivity `prodMass_l1` +
  `event_prob_diff`, the bridge that lets the estimator run on Stage B's
  approximate sampler. Standard axioms only.
- [~] **Stage D - the combinatorial reductions** (`SamplerReduction.lean`,
  D.1 done): the deterministic core of Feng-Jin Lemma 3.3 -
  `band_card_gt` (band subsets have > ℓ/2 items in the bounded-ratio
  regime) and `band_hit_le` (the delete-one-hit-item injection: the H-hit
  band has size ≤ |H|·|Ω|). D.2 (done): `greedy_hitting` - a
  fully constructive hitting set: h greedy rounds leave ≤ |F|·((n−s)/n)^h
  of any family of >s-sized sets unhit - plus `pow_shrink` (each n/s
  rounds halve the unhit family, via Bernoulli over ℚ). Replaces their
  probabilistic method deterministically. D.3 (done, `SamplerPopular.lean`):
  Feng-Jin Lemma 3.1 - `popular_class`: some dyadic class ℓ = 2^k ∈ [2,8n]
  holds ≥ ℓ/(8⌈log₂ 4n⌉) items (dyadic assignment + fiberwise pigeonhole,
  all conditions multiplicative). D.4 (done): Feng-Jin Lemma 3.2 -
  `exists_peel` (≤ d large-item removals land any excess-≤-dg subset in Ω)
  and `band_d_le` (|Ω_d| ≤ #{small sets}·|Ω| ≤ d·n^d·|Ω| via
  `small_sets_card_le`). D.5 (done): `bipartite_double_count`,
  the counting skeleton of Lemma 3.4 (min-degree vs max-degree). D.6 (done): the two
  combinatorial engines of 3.4's claims - `card_union_pool` (pool addition
  gives 2^|G| distinct neighbors, Claim 3.5's degree) and
  `card_small_subsets_lt` (≤ m·n^m small subsets, Claim 3.6's choices).
  D.7 (done): `pool_neighbors_card`
  (base + disjoint pool under capacity give 2^|G| solutions extending the
  base - Claim 3.5 modulo taxonomy arithmetic) and `fiber_card_le` (fibers
  decomposing as (X∖R)∪H are bounded by |P|·|Q| - Claim 3.6's counting).
  D.8-D.9 (done): `hat_weight_le`
  (the huge-stripped set weighs ≤ 9T/10), `huge_count_le` (≤ ℓ/(20L²) huge
  items fit under 2T), `pool_exists` (a g₀-pool of good items disjoint
  from X remains). D.10 (done): **Claims 3.5 and
  3.6 assembled and Lemma 3.4 proven** - `claim_35` (every Ω^△ member has
  ≥ 2^g₀ neighbor solutions), `claim_36` (each solution neighbors at most
  (m₁+1)n^{m₁+1}·(m₂+1)n^{m₂+1} of them), `lemma_34` (100·|Ω^△| ≤ |Ω|,
  parametrized by the paper's arithmetic conditions incl. the exponent
  gap). D.11-D.12 (done):
  `exponent_gap` + `params_choice` (parameters discharged from ℓ ≥ 4000L²)
  and **`lemma_33` - Feng-Jin Lemma 3.3 proven**: 100·|Ω₁| ≤ (1+200h)·|Ω|,
  composed from lemma_34, the core-restricted greedy hitting set
  (`greedy_hitting_core`), and the H-local deletion mapping
  (`band_hit_le'`). **Stage D is complete**: all of Feng-Jin §3 is
  machine-checked (parametrized by explicit arithmetic hypotheses that
  `params_choice`-style lemmas discharge).
- [~] **Stage E - sampling cost** (`SamplerCost.lean`, E.1 done): the
  pruning payoff `sampler_visit_bound` - a sample selecting k items
  activates ≤ (⌈log₂ n⌉+1)·k tree nodes (`activeNodes_le`, `treeDepth_le`);
  with Stage 0's `lazy_amortization` + `ledger_collapse` this covers the
  tree-structural half of the cost ledger. E.2 (done,
  `SamplerLedger.lean`): the two ledger modes - `ledger_flat`
  (Σ min(2^h,k)·(A/2^h) ≤ D·A) and `ledger_sqrt`
  (Σ min(2^h,k)·(B/2^(h/2)) ≤ 32·B·(√k+1)), with the geometric toolkit
  (`geom_sum_le`, `geom_half_root`, `staircase_le`) proven from scratch.
  Remaining in E: connecting the per-node model to a concrete
  data-structure cost function (with Stage F).
- [~] **Stage F - construction** (F.0 done, `SamplerInstance.lean`): the
  exact-arrays instantiation - `exactKernel_ok`, `samplerMassK_exact_eq`
  (the stored-kernel sampler with exact kernels IS the uniform sampler),
  the meaning lemma `expect1_uniform_indicator` (the estimated quantity is
  exactly #(solutions with P)/#solutions), and the headline corollary
  `fpras_relative`: N ≥ 1/(ε²ρ²) samples give relative error ε except with
  probability ≤ 1/4. The arrays-to-kernels bridge is also done
  (`SamplerArrays.lean`): `ArraysOK` (the spec the construction must meet:
  pointwise (1±δ) arrays + witness sets with γ dropped mass) with
  `arrayKernel_ok` and `arrayKernel_close` (induced kernels are valid and
  within local L1 12δ+3γ of exact). F.1a (done, `SamplerMerge.lean`):
  the merge layer - `WitnessOracle` (Theorem 6.1's postcondition),
  `merge_dominates` (oracle output pointwise within [convQ/(1+δ), convQ]),
  `convQ_sandwich`, and `merge_spec` (the full induction step: children
  within (1±δᵢ) + oracle ⇒ parent within the compounded budget), now with
  residue-class separation and the mod-3 piece decomposition
  (`pieceOf_residue`, `convQ_pieces`) discharging it for arbitrary arrays.
  The oracle is inhabited by verified
  executable code (`slowOracle`, `slowOracle_spec`), so The construction-side cost
  accounting is also verified (`construction_ledger`: the balanced
  schedule makes every tree level cost O(L·√M) oracle-units, total
  O(D·L·√M) - the Õ(n^{1.5}) shape). ONLY the oracle's internal speed
  remains: F.1b - the fast implementation (Feng-Jin Theorem 6.1 / BDP24:
  FFT + random primes) meeting the per-call O(L·√M) unit - the last item
  of the entire campaign.

- [x] **Headline** (`SamplerHeadline.lean`, done): **`fprasSharp`** - the
  single composed theorem of the new result, mirroring `fptasSharp`:
  correctness (relative-ε except probability ≤ 1/4) ∧ the cost ledger in
  its min(n√ℓ, n²/ℓ)·ε⁻² form ∧ the cube-collapse
  (N·perSample)³ ≤ 4194304·(D+1)·n⁴·E³ - the Õ(n^{4/3}·ε⁻²) sampling
  bound. Ledger unit: one node-draw; the oracle speed realizing it is the
  one outside-Lean assumption.
- [x] **Assembly** (`SamplerAssembly.lean`, done): `fpras_assembly` -
  Stages A+B+C composed into the top-level guarantee: under the
  stored-kernel sampler's N-fold run, the empirical indicator mean is
  within `a + (η₀ + η·#nodes)` of the expectation under the EXACT uniform
  solution distribution, except with probability ≤ 1/(4Na²).

- [x] **Introduced mechanisms audit** (`SamplerMechanisms.lean`, done):
  the four remaining prose-only mechanisms of `witness-sampler.md` are now
  machine-checked - the de-rounding layer (`div_preimage_interval`,
  `roundedDraw_exact`: the grid draw is exact), rectangle enumeration
  bounded by levels (`levels_card_le`), the correlation-count identity
  (`corr_count`), and the class-envelope rejection (`rejection_exact`,
  `rejection_accept_ge`). **Every mechanism introduced by this work is now
  in Lean**; reliance on Feng-Jin is limited to their published pipeline
  structure and the Theorem 6.1 subroutine.

Stages A-E verify everything new in this result plus the probabilistic
glue, treating the construction as a specified interface; Stage F closes
the loop on Feng-Jin's side. Status lives in this file; each completed
stage updates the checkbox and lands in CI.

## Branch `beyond-n43` (the amortized refinement)

- [x] `cache_ledger` - the ε-free mode-C sum ≤ 4·L·M.
- [x] `cache_collapse` - min(n²E/ℓ, nℓ)² ≤ n³E (the n^{1.5}√E exponent).
- [x] `fprasSharper` - the composed headline: fprasSharp ∧ cache mode
  (builds ≤ 32·ℓ·n, draws N·k ≤ 8·n·E). Total:
  Õ(n^1.5 + min(n^{4/3}ε⁻², n^{1.5}ε⁻¹) + n·ε⁻²).
- [x] `cache_ledger2` - rectangle count capped by array length: mode
  C' ≤ 2(D+1)·L² (ε- and n-free).
- [x] `cache_collapse2` - min(n²E/ℓ, ℓ²)³ ≤ n⁴E² (the n^{4/3}ε^{-4/3}
  exponent).
- [x] `fprasSharpest` - the composed v2 headline. Total:
  Õ(n^1.5 + min(n^{4/3}ε^{-4/3}, n²) + n·ε⁻²) - strictly below
  n^{4/3}ε⁻² for every ε < 1, flat Õ(n^1.5) for ε ≥ n^{-1/8}.
- [ ] Open sub-problem: builds in o(min(M,L)) per position, or an
  ε-free mode below ℓ² → uniform Õ(n^1.5 + n·ε⁻²).
