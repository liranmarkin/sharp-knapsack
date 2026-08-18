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
  the counting skeleton of Lemma 3.4 (min-degree vs max-degree). Remaining
  in D: instantiating Lemma 3.4's two degree claims (good/huge item
  taxonomy + binomial-sum arithmetic) and composing Lemma 3.3's final
  constant from 3.1 + 3.2 + 3.4 + the greedy hitting set.
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
  within local L1 12δ+3γ of exact). Remaining (F.1): produce ArraysOK
  arrays in Õ(n^1.5) - Feng-Jin Theorem 6.1 / BDP24 with FFT and random
  primes - the last and largest item.

- [x] **Assembly** (`SamplerAssembly.lean`, done): `fpras_assembly` -
  Stages A+B+C composed into the top-level guarantee: under the
  stored-kernel sampler's N-fold run, the empirical indicator mean is
  within `a + (η₀ + η·#nodes)` of the expectation under the EXACT uniform
  solution distribution, except with probability ≤ 1/(4Na²).

Stages A-E verify everything new in this result plus the probabilistic
glue, treating the construction as a specified interface; Stage F closes
the loop on Feng-Jin's side. Status lives in this file; each completed
stage updates the checkbox and lands in CI.
