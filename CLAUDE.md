# CLAUDE.md - The system of operations for this repo

This repository produces algorithmic results (currently: #Knapsack
counting). Every result follows the same pipeline. Follow it exactly; it
is the reason the results are credible.

## The three laws

1. **Formally verify everything new.** Every claim, mechanism, lemma, or
   bound *introduced by us* must be machine-checked in Lean 4 before it
   is called a result. No exceptions for "obvious" steps - the obvious
   steps are where bugs live.
2. **Prior published work may be relied on.** Peer-reviewed results we
   build on are cited, not re-proven - BUT the reliance must be explicit
   and minimal: state their result as a formal interface (a Lean `def` /
   hypothesis), inhabit the interface with verified (possibly slow) code
   when feasible, and formalize their supporting lemmas whenever our
   claim's correctness depends on them. The boundary between "ours" and
   "theirs" must be visible in the directory structure itself.
3. **Every result ships with a memo.** A short LaTeX memo whose only job
   is understanding. If a smart reader can't follow the idea from the
   memo alone, the result is not done.

## Verification rules (explicit)

- Language: Lean 4 + mathlib, pinned toolchain in `lean/`. Build with
  `lake build` from `lean/` (`export PATH="$HOME/.elan/bin:$PATH"`).
- **Zero `sorry`. Zero `native_decide`.** Every headline theorem must be
  checked with `#print axioms` and depend only on
  `propext, Classical.choice, Quot.sound`.
- **Two folders per result**: `lean/SharpKnapsack/New/` holds what we
  present - keep it *minimal*, every file load-bearing for the headline
  theorem. `lean/SharpKnapsack/<PriorAuthors>/` (e.g. `FengJin/`) holds
  what we rely on: their lemmas we chose to formalize, and their
  subroutine interfaces used as published. Each folder has a README
  stating the boundary in one paragraph.
- **One composed headline theorem** per result (`fptas`, `fptasSharp`,
  `fprasSharp` are the precedents): a single Lean statement conjoining
  correctness and the cost bound. Partial verification is tracked, but
  the result "exists" only when the headline theorem compiles.
- **Roadmap discipline**: maintain `docs/verification-roadmap.md` with a
  checkbox per stage. Work stage by stage; a stage is done only when it
  builds green, its axioms are checked, and it is committed and pushed.
  Every commit must build green - never commit broken or `sorry` states.
- **CI is the referee**: `.github/workflows/ci.yml` rebuilds all proofs
  from scratch and runs all tests on every push. A result whose CI is
  red does not exist.

## Empirical rules (before and alongside proving)

- **Prototype before claiming.** Every new mechanism gets an executable
  prototype validated against brute force (distribution exactness by TV
  distance, bounds by direct measurement) *before* any bound is claimed.
- Prototypes live in `experiments/` as self-contained Python with hard
  `assert`s (exit nonzero on failure), wired into CI. No eyeball-only
  scripts in the PR.
- Add `#guard` evaluation checks in Lean for executable definitions, so
  `lake build` itself re-tests them on concrete instances.

## Research-process rules

- **Read the SOTA paper in full first.** Build a complete cost ledger
  (where every factor of their bound comes from) and a barrier map
  (which improvements are blocked by which recognized open problems)
  before attempting anything.
- **Document dead ends** with their precise failure modes in
  `docs/research/` notes - so no future session retraces them. Keep the
  full exploration trail on a `<branch>-research` branch; the PR branch
  contains *exactly* what is required to state, prove, and test the
  result - nothing else.
- **Honesty is non-negotiable**: a bound is a "theorem-candidate" until
  its headline theorem compiles; never present a candidate as proven;
  never absorb an unverified assumption silently - name it (as we name
  the FFT subroutine of Feng-Jin's Theorem 6.1). When a comparison has a
  tie regime or untracked polylogs, say so unprompted.

## The memo (explicit)

- Location: `paper/memo.tex`, compiled to `paper/memo.pdf` with
  `tectonic` (installed via Homebrew). Both are committed.
- Style: **idea only**. No code structure, no verification internals
  (one footnote pointing at the repo is the maximum), no formality for
  its own sake. Target 3-5 pages.
- Structure that works: (1) problem and result with a theorem box and a
  concrete ε comparison; (2) where the prior algorithm's time goes;
  (3) THE observation, pulled out as a display quote; (4) the algorithm
  in numbered plain-language steps; (5) the two-line cost arithmetic;
  (6) discussion: adaptivity, remaining bottleneck, open problems.
- The memo leads the PR description.

## Deliverable checklist for a new result

1. Research notes + ledger + barrier map (`docs/research/`).
2. Validated prototypes (`experiments/`, asserted, in CI).
3. Proof document (`docs/<result>.md`): theorem, lemmas, algorithm,
   cost ledger, explicit list of what is relied on.
4. Lean development: `New/` (minimal, ours) + `<PriorAuthors>/`
   (reliance), headline theorem, axioms checked, roadmap complete.
5. Memo (`paper/memo.tex` + pdf).
6. PR: minimal diff, description = result + memo link + boundary table
   + test plan; CI green.
