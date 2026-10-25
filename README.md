# BoringLab

The experimental laboratory: combinatorial games, motives, and transcendence
theory. Imports [`BoringMath`](../BoringMath) (candidate mathlib
contributions) and follows the same **boring style**; see
[`../BoringMath/docs/STYLE.md`](../BoringMath/docs/STYLE.md). Unlike
`BoringMath`, sorries may persist indefinitely here.

## Build

```bash
(cd ../BoringMath && lake build)   # dependency
lake exe cache get
lake build
```

Requires the `leanprover/lean4:v4.35.0-rc3` toolchain (installed via elan).
