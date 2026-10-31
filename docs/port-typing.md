# LAB A2.0 — port-typing design decision (issue EnidAnderson/BoringLab#3)

Status: PREP/LANDED-in-working-tree for `BoringLab/Doctrine/Computad.lean` and
`BoringLab/Doctrine/Doctrine.lean`. No `axiom` declarations anywhere; hypotheses
enter as explicit structure fields or theorem binders.

## The decision

A `Computad` is a typed quiver with ports:

- `obj : Type u` — objects (0-cells);
- `gen : Type u` — generators (1-cells), each with explicit `src`/`tgt`;
- `port : Type u` — a fixed port universe, carrying a **port monoid as explicit
  structure data** (`portMul`, `portOne`, and the three monoid laws as fields),
  *not* as a typeclass instance: per STYLE §2.3 data parameters are taken
  explicitly, never instance-chosen, and this keeps every declaration
  computable and free of instance diamonds (a `Monoid port` field caused
  instance mismatches between def bodies and proofs in probes at the pin).
- each generator carries `leftPorts g : List port` and `rightPorts g :
  List port`.

Composition typing is **additive** (the PROP-shaped discipline): the ports of
a composite path are the concatenation of the ports of its factors
(`Computad.pathLeftPorts_comp`, `Computad.pathRightPorts_comp`), and the port
word of a concatenation is the product of the port words
(`Computad.portWord_append`). The substrate is mathlib's own quiver/path
machinery at pin v4.35.0-rc3 (`Quiver`, `Quiver.Path`,
`CategoryTheory.Paths`).

## KZ-client pressure (why this shape)

The client that forces the shape is the KZ computad for MTM(ℤ), where
Left-ports = forms/Stokes and Right-ports = chains/subdivision — the two
player-ports. A generator whose left ports are forms and right ports are
chains needs exactly the two-sided list typing above; a single-sided
(src/tgt-only) quiver cannot express it. The additive law is what makes
composition of such generators type-check port-wise.

## Doctrine = computad + declared reversible moves

`Doctrine` adds `move : ∀ {X Y}, Quiver.Path X Y → Quiver.Path X Y → Prop` —
a relation on parallel paths, the 1-categorical shadow of the sub-2-groupoid
of certified reversible moves. The localization `C[W⁻¹]` is mathlib's in-tree
`CategoryTheory/Localization` machinery with `W = Doctrine.moveClass d` (the
sides of the declared moves). First theorems: `Doctrine.localization_exists`
(localization exists), `Doctrine.declared_move_inverted` /
`Doctrine.declared_move_inversion` (declared-move inversion is the explicit
data `Localization.Construction.wIso`/`wInv`, not a global axiom).

Honest scope note: at the pin there are no (∞,1)-categories in mathlib, so the
free (∞,1)-category on a computad is a recorded gap ([O]); the 1-categorical
shadow is what is implemented. Note also that a localization can only invert
morphisms, so a declared move `p ⇄ q` of parallel paths is shadowed by
inverting both sides `p` and `q`; the *equality* `Q(p) = Q(q)` is 2-categorical
content and is deliberately not claimed at depth 1.

## Falsifiable shadow (stated, not proved)

`misereQuotient (r : Game → Game → Prop) : Doctrine` states the
Plambeck–Siegel misère quotient (arXiv:math/0609825) as a doctrine over a
given misère-equivalence relation `r` on games: objects = games, generators =
`r`-related pairs, trivial port monoid, moves = pairs of parallel
single-generator paths. `misereQuotient_generator_inverted` shows the syntax
can state (and derive) that `r`-related games become isomorphic in the
localization. The design passes the issue's falsifiability test: the misère
quotient is statable in this syntax.

## GOLD-at-pin verification (v4.35.0-rc3) and choice-taint report

All consumed mathlib names were verified by probe files run with
`lake env lean` against the pin:

- `Quiver` (`Mathlib.Combinatorics.Quiver.Basic`), `Quiver.Path`,
  `Quiver.Path.nil/cons/comp`, `Quiver.Path.comp_nil/comp_cons`,
  `Quiver.Hom.toPath` (`Mathlib.Combinatorics.Quiver.Path`) — computable,
  no choice.
- `CategoryTheory.Paths`, `CategoryTheory.Paths.categoryPaths`
  (`Mathlib.CategoryTheory.PathCategory.Basic`) — computable (homs are
  `Quiver.Path`, an inductive in `Type`), no choice.
- `CategoryTheory.MorphismProperty` (a plain predicate
  `∀ ⦃X Y⦄, (X ⟶ Y) → Prop` at this pin — no `iso_stable` field),
  `MorphismProperty.IsInvertedBy`, `MorphismProperty.Q_inverts`
  (`Mathlib.CategoryTheory.MorphismProperty.*`) — Prop-level, no choice.
- `MorphismProperty.Localization`, `MorphismProperty.Q`,
  `Localization.Construction.wIso`, `wInv`, `Functor.IsLocalization`,
  `Functor.q_isLocalization` (`Mathlib.CategoryTheory.Localization.*`) —
  **choice-tainted at the pin**: these are declared inside a
  `noncomputable section` (they use `Classical.choice` via
  `CategoryTheory.Quotient`'s `deriving Category` / `Quotient.functor`).
  We consume them **only inside `theorem` statements (Prop-valued)**, never in
  a `def`, so no `noncomputable` declaration arises on our side; all of our
  `def`s/`structure`s are computable. This is recorded here per the issue's
  instruction to build around choice-tainted consumed names narrowly.
- Not used: `CategoryTheory.Limits` chosen-limit data (`HasLimit`, pullback) —
  choice-tainted at the pin and not needed for this scope.
- `Monoid PUnit` instance exists (`Mathlib.Algebra.Group.PUnit`), but the
  port monoid is carried as explicit fields (see above), so no instance is
  relied on.

## Open questions

- Whether `move` should later be closed under path composition (the saturated
  congruence generated by the declared moves) at the level of the `Doctrine`
  structure; currently saturation is left to the localization.
- The KZ computad for MTM(ℤ) (Left-ports = forms/Stokes, Right-ports =
  chains/subdivision) is the next client to instantiate; it needs the
  port-monoid of forms/chains, not the trivial `PUnit` monoid.
