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

## Commands

```bash
lake update          # refresh dependencies (rare; pinned to v4.35.0-rc3)
lake exe cache get   # fetch/refresh prebuilt mathlib oleans
lake build           # build (must be warning-clean except deliberate sorries)
../BoringMath/scripts/check-style.sh .   # style backstop
```

## Environment facts

- Toolchain pinned to `leanprover/lean4:v4.35.0-rc3` in `lean-toolchain`.
- Depends on `BoringMath` via the local path `../BoringMath`: build
  `BoringMath` first (`cd ../BoringMath && lake build`).
- `.lake/packages` is a **directory junction** shared with `BoringMath` and
  the pre-existing `EnidsMathMadness` project, which owns the single mathlib
  checkout and its built oleans. Do not delete `EnidsMathMadness`. Mathlib
  is bumped only in lockstep across all projects.
- Git identity: local `Enid <enid@localhost>` (see `BoringMath/AGENTS.md`).
