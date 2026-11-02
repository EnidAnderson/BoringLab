# LAB META.0 — the reprogrammable Lisp: the doctrine of doctrines (PREP note + 1-skeleton)

Issue: `EnidAnderson/BoringLab#72`. User steering (2026-11-02): each
doctrine supplies a Lisp, but there should be a "reprogrammable Lisp" — a
syntax for defining new doctrines or named scopes; same structure as
cdh/Nisnevich descent.

## The reading (no-woo-gated)

A doctrine already supplies a Lisp: computad generators = special forms,
declared moves = the macro table (LISP.0, #68), doctrine-localization =
the quotient semantics (`misereSequent_inverted` inverts exactly what the
macro table declares). The reprogrammable Lisp is the 2-layer: a syntax for
defining doctrines is a doctrine OF doctrines — a 2-computad whose
objects are doctrines, 1-cells are doctrine morphisms (landed:
`Computad.Morph` + move preservation), 2-cells are rewrites of
presentations (a rewrite of a doctrine's declared moves is a
macro-expansion at the meta level). The scope hyperdoctrine is secretly
this: fibers are doctrines and `subst` rewrites whole fibers along
generators — now made explicit as `Hyperdoctrine.substMorph`.

## What landed

`BoringLab/Doctrine/Meta.lean`: `DoctrineMorph` (polygraph morphism +
`preservesMoves`), `id` (proved via `mapPath_id`), `comp` (preservation
chains), `comp_assoc` (declared hole; peeling plan = `Computad.Morph.ext`,
mirroring `RegimeMap.ext'`), `PresentationRewrite` (2-cell 1-skeleton: lax
naturality over declared moves), `Hyperdoctrine.substMorph` (the
substitution of a scope hyperdoctrine IS a doctrine morphism between
fibers — proved).

## Hygiene = freshness

Variable capture = an owned-vs-unowned hole violation: hygiene of
scope-generator substitution is the FRESHNESS condition. Instances:
game-side = GAL.0 #16 (deck semantics, hidden information as un-owned
holes); syntactic side = `BoringLab.Lisp/Hygiene.lean` (capture-as-data).

## Descent connection

Same structure as cdh/Nisnevich descent (#69, GL.0.2): the convention as a
cd-structure on the computad, descent as referee invariance. The
2-computad's 2-cells rewriting presentations are the meta-level analog of
the cd-structure's distinguished squares.

## References

[Mimram] arXiv:2312.00429, LMCS 21(3) 2025; [Burroni] TCS 126 (1994);
[Gabriel–Zisman] LNM 1 (1967) ch. I. Tickets: #3, #14, #16, #68, #69, #72.
