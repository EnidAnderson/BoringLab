# LAB LISP.0 — On Lisp macros as computadic rewriting

Issue: `EnidAnderson/BoringLab#68`. The human's hint, made literal: the rules
of Common Lisp and its distinction between **macros** and **functions** mirror
computadic rewriting — computadic rewriting is a refined, well-typed
explanation of the Lisp macro system. This note records the reading and what
landed, at the polygraph level (per the human's standing direction: no graph
rewriting, no chosen category-theory machinery).

## The reading

* **Functions are 1-cells.** A Lisp signature is a computad
  (`lispComputad arityOf`, `BoringLab/Lisp/Macro.lean`): one object (the sort
  `expr`), one generator per function name, port monoid `ℕ` with `+`, and
  port typing = arity — a function of arity `n` consumes port word `[n]` and
  produces `[1]`. Evaluation order/argument passing is the port discipline.
* **Macros are declared moves (2-cells).** A `defmacro` binds a name to a
  pattern and an expansion ([Graham] ch. 7); at the polygraph level this is a
  relation between parallel paths (Mimram Def. 3.5) — the call path
  `toPath ⟨name⟩` and the expansion path `lispPath expansion` — declared in
  `macroDoctrine`. Macro expansion = rewriting in the doctrine; the
  GL-line's geometric-sequent shape (`Doctrine.toSequent`,
  `BoringLab/Doctrine/Geometric.lean`).
* **The falsifiable shadow.** ANSI CL §3.1.2.1: `macroexpand` returns a form
  equivalent under evaluation. Data-level shadow: the declared macro move is
  inverted in the doctrine-localization (`macroCall_inverted`) — expansion
  is an isomorphism in the localized theory.
* **The function/macro distinction as data**: `isMacro macros g` tags exactly
  the declared macros; functions are the generators without a declared move.

## What landed

* `BoringLab/Lisp/Sexpr.lean` — `Sexpr` (atom/list, [McCarthy] 1960), `size`,
  `isAtom`, and the toy `when` pattern/expansion ([Graham] ch. 7), printed by
  `#eval`.
* `BoringLab/Lisp/Macro.lean` — `lispComputad`, `lispPath` (S-expression →
  path), `MacroDef`, `macroDoctrine`, `macroRule_is_move`,
  `macroCall_inverted`, `isMacro` / `isMacro_of_mem`, toy `when` macro with
  `#eval` (tag + expansion path length).
* `BoringLab/Doctrine/Nim.lean` (GL instance, ticket #14 item (iii)) —
  `nimComputad` (positions `ℕ`, legal removals as generators, addition-only
  typing), `nimDoctrine` (commutation of two removals as the declared
  sequent), `nim_commute_witness` (at `5, k=2, j=1`, all legality equations
  `rfl`), `nim_commute_inverted`, `nimCommuteSequent`.
* `BoringLab/Epistemology/Learning.lean` (ticket #31, EPI.3.1) — see the note
  in that module; `singleton_identifies` and the converse-failure witness
  `identifiable_not_falsifiable_witness` proved; two declared holes
  (`falsifiable_family_identifiable`, `exists_conservative_method`) with
  peeling plans.

## Declared out of scope (honest-absence ledger)

Pattern matching and destructuring, backquote/unquote, hygiene and variable
capture ([Graham] ch. 9), and any evaluator/interpreter (the computad is the
syntax layer; semantics would be the doctrine-localization's models).
Named next holes with peeling plans: `macroexpand-1` as a single-step
path-rewriting lemma (then iterate by path composition); the hygiene ledger
as a `Prop`-field on `MacroDef` (no capture: expansion symbols disjoint from
pattern variables, checkable on `Sexpr` by enumeration).

## References

* [Graham] P. Graham, *On Lisp: Advanced Techniques for Common Lisp*,
  Prentice Hall, 1993, ISBN 0130305529 — ch. 7 "Macros", §7.4
  (`macroexpand`/`macroexpand-1`), ch. 9 (variable capture).
* [ANSI CL] ANSI INCITS 226-1994 (R1999) *Common Lisp*, §3.1.2.1.
* [McCarthy] J. McCarthy, CACM 3(4):184–195, 1960.
* [Mimram] arXiv:2312.00429, LMCS 21(3) (2025), Def. 3.5; [Burroni] TCS 126
  (1994), 257–291; [Conway] ONAG 2nd ed. 2000; [Berlekamp–Conway–Guy],
  *Winning Ways* vol. 1 (1982).
