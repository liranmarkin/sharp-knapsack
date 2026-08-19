# `FengJin/` - what we rely on from Feng-Jin (SODA 2025, arXiv 2410.22267)

This folder contains *their* results, in two forms:

* **Formalized by us**: their §3 structural lemmas - Lemma 3.1
  (`Popular.lean`) and Lemmas 3.2/3.3/3.4 with the hitting-set machinery
  (`Reduction.lean`) - machine-checked here so the new result's sample
  complexity does not rest on unverified combinatorics.
* **Used as published**: the interface of their Theorem 6.1
  (`Oracle.lean`: the `WitnessOracle` postcondition and the §6.2 mod-3
  piece decomposition). Its *fast implementation* (FFT + random primes,
  [FJ25]/[BDP24]) is the one component cited rather than verified; a
  verified slow implementation inhabiting the same interface lives in
  `New/SamplerMerge.lean`.
