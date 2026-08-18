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
  band has size ≤ |H|·|Ω|). D.2 (open): probabilistic-method existence of
  an Õ(n/ℓ) hitting set covering 1−o(1) of the band; Lemma 3.4 (the
  popular-class structural lemma for the general case).
- [~] **Stage E - sampling cost** (`SamplerCost.lean`, E.1 done): the
  pruning payoff `sampler_visit_bound` - a sample selecting k items
  activates ≤ (⌈log₂ n⌉+1)·k tree nodes (`activeNodes_le`, `treeDepth_le`);
  with Stage 0's `lazy_amortization` + `ledger_collapse` this covers the
  tree-structural half of the cost ledger. E.2 (open): the per-node
  array-work model (level enumeration + class draws) and the
  Σ_h min(2^h,k)·min(n/2^h, ℓ/2^{h/2}) arithmetic.
- [ ] **Stage F - construction**: a verified-executable merge meeting the
  witness spec (naive convolution + witness rounding suffices for
  correctness; the Õ(n^1.5) *time* of the sophisticated merge - Theorem 6.1
  / BDP24 with FFT and random primes - is the last and largest item).

Stages A-E verify everything new in this result plus the probabilistic
glue, treating the construction as a specified interface; Stage F closes
the loop on Feng-Jin's side. Status lives in this file; each completed
stage updates the checkbox and lands in CI.
