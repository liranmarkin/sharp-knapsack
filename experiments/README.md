# Experiments: validation scripts for the witness sampler

Prototype validations backing `docs/research/2026-08-18-beat-feng-jin-notes.md`
and `docs/research/2026-08-18-witness-sampler-proof.md`. Each is a
self-contained Python 3 script (no dependencies); run with `python3 <file>`.

| Script | What it validates |
|---|---|
| `probe_logconcave.py` | Subset-sum count arrays are not log-concave (kills shape-based sampling) |
| `probe_envelope.py` | Tilted-rejection retries track the Chernoff-envelope gap (kills naive tilting) |
| `pruned_sampler.py` | The ∅-split pruned tree sampler is distribution-exact; work savings scale with n |
| `witness_sampler.py` | Witness-diagonal split draw: exactness (TV ~ noise), witness-mass fraction ~ 1, level compression M << L |
| `sublevel_sampler.py` | Sub-level class draw: exact with <= 4 expected retries; attaining-mass domination under D^-3 separation |
