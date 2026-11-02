# LAB LINF.0 — L∞ algebras as polygraphs

Issue: `EnidAnderson/BoringLab#109`. The pure-composition form of an
L∞ algebra: a one-object computad whose generators are the brackets `lₙ`
(arity ports, degree ports), with the generalized Jacobi identities as
declared relations on FORMAL SUMS of paths (the doctrine of linear
relations).

## What landed

`BoringLab/Deform/LInf.lean`:

- `linfComputad` — one object (`PUnit`, the graded space), port monoid
  `ℤ` with `+`, generators `(n, d)` with arity `n ≥ 1`; left port `[n]`,
  right port `[d]`; port-word laws proved
  (`pathLeftWord_toPath` = arity, `pathRightWord_toPath` = degree).
- `FormalSum c X Y` = `List (Path X Y × ℤ)` — the linear relation layer;
  `LInfPres` (computad + root + declared relations) with eta.
- `LInfAxioms` — `l₁² = 0` as a declared single-tree relation (field
  `d_squared`), and the generalized Jacobi as explicit data `jacobiSum n`
  with the axiom field `jacobi` (`n ≥ 2 → jacobiSum n ∈ relations`); the
  shuffle-sum construction is the named `shuffleSum` hole.
- Toy: the strict dg case (`lₙ = 0` for `n ≥ 3`) — `linfPresToy` /
  `linfAxiomsToy`, with `l₁² = 0` and the empty Jacobi sums proved by
  membership.

## Named holes

- `shuffleSum n` — the generalized Jacobi shuffle-sum of trees as a
  `FormalSum` (peeling plan: shuffles of `[k] ⊗ [n-k+1]` subtrees, recursive
  on `n`, sign = Koszul sign; then `jacobi` follows by the field).
- MC equation (DEFORM.0 #108 shadow): degree-1 elements with `Σ lₙ(e,…,e)
  = 0` — as the sequent layer; deformation functor = localization shadow.

## References

[Lada–Stasheff] JPAA 48 (1987); [Getzler] Annals 170 (2009), 271–310;
[Merkulov] homotopy-Lie/wheeled props; [Lurie] DAG.
