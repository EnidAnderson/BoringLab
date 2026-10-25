# AGENTS.md — BoringLab

`BoringLab` is the experimental laboratory (combinatorial games, motives,
transcendence theory). It imports `BoringMath` and is bound by the same
boring style: **the binding rules live in `../BoringMath/docs/STYLE.md` —
read them before writing any code.** The style backstop is
`../BoringMath/scripts/check-style.sh`.

Differences from `BoringMath`:

- Sorries may persist indefinitely here (still with peeling plans, correct
  names, and references).
- No PR notes are required; keep loose notes in `docs/`.
- Everything else — exact proofs, banned tactics, eta discipline, naming,
  references, headers — is identical.

Pull requests from the work assistant are never merged blind: follow the
review protocol in `../BoringMath/docs/PR-WORKFLOW.md`.

## Commands

```bash
lake update          # refresh dependencies (rare; pinned to v4.35.0-rc3)
lake exe cache get   # fetch/refresh prebuilt mathlib oleans
lake build           # build (must be warning-clean except deliberate sorries)
../BoringMath/scripts/check-style.sh .   # style backstop
../BoringMath/scripts/fetch-pr.sh <N>    # fetch pull request #N (run in this repo)
```

## Layout

- `BoringLab/<Area>/<Topic>.lean` — experimental modules, importable as
  `BoringLab.<Area>.<Topic>`.
- `docs/` — loose notes.

`BoringLab` depends on `BoringMath` by local path: clone the two
repositories as sibling directories. Machine-specific environment details
live in `AGENTS.local.md`, which is git-ignored.
