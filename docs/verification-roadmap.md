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
- [ ] **Stage B - approximate arrays: TV bound**: replace exact counts by
  arrays satisfying the (1±δ) witness spec; define the tree measure the
  arrays induce; prove TV(tree measure, uniform) ≤ f(δ, depth) by
  telescoping the per-merge factors (uses Stage 0's identity + domination).
- [ ] **Stage C - the estimator**: Monte Carlo mean of indicators over N
  samples; multiplicative concentration (Chebyshev suffices for ε⁻² sample
  complexity); combine with Stage B's TV to get the (1±ε, 3/4) guarantee
  relative to the ratio being estimated.
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
