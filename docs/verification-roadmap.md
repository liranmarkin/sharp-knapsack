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
- [ ] **Stage D - the combinatorial reductions**: Feng-Jin's Lemma 3.1
  (popular class) and Lemma 3.3 (hitting-set ratio ≥ ℓ/Õ(n)) - finite
  injection arguments; connects Stage C's ratio to |Ω|.
- [ ] **Stage E - sampling cost**: structural cost model for the query stage
  (as `Complexity.lean` does for the FPTAS) and the ledger bound
  Õ(min(n√ℓ, n²/ℓ)·ε⁻²), reusing Stage 0's amortization and collapse.
- [ ] **Stage F - construction**: a verified-executable merge meeting the
  witness spec (naive convolution + witness rounding suffices for
  correctness; the Õ(n^1.5) *time* of the sophisticated merge - Theorem 6.1
  / BDP24 with FFT and random primes - is the last and largest item).

Stages A-E verify everything new in this result plus the probabilistic
glue, treating the construction as a specified interface; Stage F closes
the loop on Feng-Jin's side. Status lives in this file; each completed
stage updates the checkbox and lands in CI.
