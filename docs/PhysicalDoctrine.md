# LAB PHYS.0 — PhysicalDoctrine: design decisions and GOLD-at-pin record

Ticket: EnidAnderson/BoringLab#6 "LAB PHYS.0: the PhysicalDoctrine structure +
calibration registry". Module: `BoringLab/Physical/PhysicalDoctrine.lean`.

## The structure (depth 1-2)

`BoringLab.PhysicalDoctrine` bundles the five axioms as explicit FIELDS (no
`axiom` declarations anywhere in the lab):

- P1 `system : Type u`, `[systemCategory : Category.{v} system]`,
  `unit : system` — a category with a distinguished unit/interface object
  (operationality: interaction is the only interface). Anchors: Barrett, Phys.
  Rev. A 75, 022103 (2007), arXiv:quant-ph/0508211; Hardy, arXiv:quant-ph/0101012;
  Chiribella–D'Ariano–Perinotti, Phys. Rev. A 84, 012311 (2011),
  arXiv:1011.6451; Masanes–Müller, New J. Phys. 13, 063001 (2011),
  arXiv:1004.1483.
- P2 `resource` with `[CommMonoid resource] [Preorder resource]
  [IsOrderedMonoid resource]` — the ordered commutative monoid of resources
  (thermodynamic ordering; Landauer, Nature 237, 177–192 (1967), as an ordering
  statement; Fritz–Coecke–Spekkens, Math. Struct. in Comp. Science 27, 850–938
  (2017), arXiv:1504.03661).
- P3 `neighborhood` with `[Category]` and `locality : Coverage neighborhood`.
- P4 `referee : Type w₁` with `[Group referee]`, `value : Type u₂` with
  `[MulAction referee value]`, `ruling : Set value`, and the Prop
  `ruling_eq_invariants : ruling = MulAction.fixedPoints referee value`
  (Wigner, Group Theory and its Application to the Quantum Mechanics of Atomic
  Spectra, Academic Press, 1959).
- P5 `base : Type u₃` with `[Category]`, `transport : base ⥤ system`, and the
  Prop `nonIsotrivial : ∃ (b b' : base), ¬ Nonempty (b ≅ b')` (Atiyah, Publ.
  Math. IHÉS 49, 1–26 (1988), §1, for the functor-from-a-base reading).

## Design decision 1: P3 is a `Coverage`, not a `GrothendieckTopology`

Chosen: `CategoryTheory.Coverage`. At the pin, `Coverage C` (mathlib
`Mathlib/CategoryTheory/Sites/Coverage.lean:159`) extends `Precoverage C`
(`coverings : ∀ X, Set (Presieve X)`, line 46 of `Precoverage.lean`) with a
single `pullback` axiom; it carries NO saturation demand, matching the rawness
of the locality axiom. A `GrothendieckTopology` (saturated sieves) is the
sheaf-theoretic closure of the axiom, recoverable via `Coverage.toGrothendieck`
when a sheaf condition is actually needed — that is a later ticket. Literature:
[Elephant] C2.1 (as cited in mathlib's own Coverage header); Mac Lane–Moerdijk,
Sheaves in Geometry and Logic, Ch. III (Grothendieck topologies).
Both calibration instances use the trivial coverage
`(GrothendieckTopology.trivial C).toCoverage`, where `trivial` (only the maximal
sieve covers) is `Mathlib/CategoryTheory/Sites/Grothendieck.lean:237` and
`toCoverage` is `Coverage.lean`. A genuine locality coverage on `MeasCat`
(e.g. jointly surjective measurable families) is deferred — recorded under
open questions.

## Design decision 2: P5 non-isotriviality is a Prop, stated base-side

Chosen: a `Prop` field (the issue's "prop vs data" fork), formulated as
`∃ (b b' : base), ¬ Nonempty (b ≅ b')` — the base category is not isotrivial
(it has two non-isomorphic objects). Reason: every image-side or
essential-constancy reading of "non-isotrivial transport" is UNSATISFIABLE for
the terminal doctrine — any functor into a terminal category is essentially
constant, and any two images are isomorphic — yet acceptance criterion (a)
requires the terminal/trivial doctrine to satisfy the structure. So the honest
1-categorical shadow at depth 1 is the base-side statement. Both calibrations
witness it with `base = Discrete (Fin 2)` and `discrete_fin_two_noniso`
(`Discrete.Hom.eq` turns an iso into `0 = 1 : Fin 2`, killed by
`Fin.zero_ne_one'`).

## Design decision 3: P2 substrate — GOLD finding at pin v4.35.0-rc3

The issue text says "mathlib `OrderedCommMonoid` substrate at pin, GOLD-verified".
GOLD result: the bundled class `OrderedCommMonoid` DOES NOT EXIST at
v4.35.0-rc3 (mathlib refactored to unbundled order classes). The substrate at the
pin is `IsOrderedMonoid` (`Mathlib/Algebra/Order/Monoid/Defs.lean:34`):
`class IsOrderedMonoid (α) [CommMonoid α] [Preorder α]` with `mul_le_mul_left` /
`mul_le_mul_right`. The structure therefore carries `[CommMonoid resource]
[Preorder resource] [IsOrderedMonoid resource]` as three explicit instance
fields. Instances verified by `#synth` at the pin (probe
`probes/ProbeDoctrine.lean`): `IsOrderedMonoid Nat` and `IsOrderedMonoid NNReal`
both synthesize via `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`
(`Mathlib/Algebra/Order/GroupWithZero/Canonical.lean:60`). The trivial doctrine
uses `resource := Nat`; the classical doctrine uses `resource := NNReal`.

## Design decision 4: P4 shape and computability

P4 is encoded as: referee group `referee` (instance field `[Group referee]`), a
standalone value type `value : Type u₂` with `[MulAction referee value]`, a ruling
set `ruling : Set value`, and the Prop field `ruling_eq_invariants :
ruling = MulAction.fixedPoints referee value` — the invariants functor is
`MulAction.fixedPoints` (`Mathlib/GroupTheory/GroupAction/Defs.lean:116`). The
value object is deliberately NOT an object of `system`: an action on hom types
`value ⟶ value` would need computable `SMul` instances on bundled hom subtypes
(e.g. measurable maps), which is deferred (open questions).

Computability note: `MeasureTheory.ProbabilityMeasure.map` is `noncomputable` at
the pin (`ProbabilityMeasure.lean:627`), so the classical doctrine's value type is
the computable `Fin 2 → NNReal` with the contravariant action `σ • f = f ∘ σ⁻¹`
of `S₂ = Equiv.Perm (Fin 2)` (instances `permArrowSMul`, `permArrowMulAction` in
the module; `Equiv.Perm.permGroup` is `Mathlib/Algebra/Group/End.lean:73`). The
`MeasureTheory` contact is carried by `MeasCat` (P1/P3 categories), `classicalValue`
(point masses of a probability measure), `Measure.dirac_apply_of_mem`, and the
`InformationTheory` calibration theorem. No `noncomputable`, no `Classical.choice`,
no `Rat.add/mul/div`, no limits family anywhere in the module.

## Calibration registry (depth 1)

- (a) `trivialDoctrine : PhysicalDoctrine` — terminal category `Discrete PUnit`,
  `Nat` resources, trivial coverage, `PUnit` referee with `Monoid.toMulAction`
  (`Mathlib/Algebra/Group/Action/Defs.lean:470`) and `ruling := Set.univ` proven to
  equal the fixed points (`trivial_ruling_eq_invariants`), constant transport from
  `Discrete (Fin 2)`. Proven by `terminal_calibration : Nonempty PhysicalDoctrine`.
- (b) `classicalDoctrine : PhysicalDoctrine` — `system := MeasureTheory.MeasCat`
  (`MeasCat.lean:43`, `LargeCategory` at :60), `unit := MeasCat.of PUnit`,
  `NNReal` resources, trivial coverage on `MeasCat`, referee `Equiv.Perm (Fin 2)`
  on `value := Fin 2 → NNReal` with `ruling := {f | f 0 = f 1}` proven equal to
  the invariants (`classical_ruling_eq_invariants`: the `S₂`-invariants are exactly
  the diagonal valuations), constant transport at `MeasCat.of (Fin 2)`.
  Proven by `classical_calibration : Nonempty PhysicalDoctrine`.
- (c) game-doctrine instance: DEFERRED to post-V.0 (it should instantiate against
  the value 2-groupoid, not a placeholder). Not built in this ticket.
- Ports (A9): FORBIDDEN in this ticket.
- Extra `InformationTheory` calibration: `classical_klDiv_eq_zero_iff_eq`
  (`InformationTheory.klDiv_eq_zero_iff`, `KullbackLeibler/Basic.lean:377` at the
  pin): KL divergence of probability measures on `Fin 2` vanishes iff the measures
  are equal; plus `classicalValue` / `classical_value_dirac_self` tying the value
  type to `MeasureTheory.ProbabilityMeasure` entry points.

## GOLD-verified mathlib entry points at pin v4.35.0-rc3

All verified by `lake env lean` probe (`probes/ProbeDoctrine.lean`) and by reading
the pinned sources under `.lake/packages/mathlib`:
`Coverage` (Sites/Coverage.lean:159), `Precoverage` (Sites/Precoverage.lean:46),
`GrothendieckTopology.trivial` (Sites/Grothendieck.lean:237),
`GrothendieckTopology.toCoverage` (Sites/Coverage.lean), `Discrete` +
`discreteCategory` + `Discrete.Hom.eq` + `instSubsingletonDiscreteHom`
(CategoryTheory/Discrete/Basic.lean), `Functor.const` (CategoryTheory/Functor/
Const.lean:36), `IsOrderedMonoid` (Algebra/Order/Monoid/Defs.lean:34),
`LinearOrderedCommMonoidWithZero.toIsOrderedMonoid` (Algebra/Order/GroupWithZero/
Canonical.lean:60), `MeasCat`/`MeasCat.of`/`LargeCategory MeasCat`
(MeasureTheory/Category/MeasCat.lean:43,60), `PUnit.instMeasurableSpace`
(MeasureTheory/MeasurableSpace/Instances.lean:24), `Fin.instMeasurableSpace`
(:34), `Fin.instMeasurableSingletonClass` (:66), `ProbabilityMeasure`
(Measure/ProbabilityMeasure.lean:103), `Measure.dirac.isProbabilityMeasure`,
`Measure.dirac_apply_of_mem` (Measure/Dirac/Basic.lean), `InformationTheory.klDiv`
(InformationTheory/KullbackLeibler/Basic.lean:57), `klDiv_self` (:78),
`klDiv_eq_zero_iff` (:377), `MulAction.fixedPoints` (GroupTheory/GroupAction/
Defs.lean:116), `PUnit.commGroup` (Algebra/Group/PUnit.lean:24), `Monoid.toMulAction`
(Algebra/Group/Action/Defs.lean:470), `Equiv.Perm.permGroup` (Algebra/Group/
End.lean:73), `Equiv.Perm.mul_apply`/`Equiv.Perm.one_apply`, `Equiv.swap_apply_left`
(Logic/Equiv/Basic.lean:652), `Equiv.symm_apply_eq` (Logic/Equiv/Defs.lean:296),
`Fin.forall_fin_two`, `Fin.zero_ne_one'` (Data/Fin/SuccPred.lean:59), `mul_inv_rev`,
`inv_one`, `Set.ext`, `Set.mem_univ`, `Subsingleton.elim`.

## What a port ticket needs from this registry (stop-rule)

A port ticket must supply a full `PhysicalDoctrine` instantiation for the ported
structure — all five fields, including a proven `ruling_eq_invariants` and a
non-isotrivial base — and compose its wiring against `transport : base ⥤ system`;
no port before (a) + (b) + (c) all hold.

## Open questions

- P3 for the classical doctrine uses the trivial coverage at depth 1; the honest
  locality (coverage on `MeasCat` by jointly surjective measurable families, or a
  coverage of measurable partitions) needs pullback stability on `MeasCat` —
  deferred.
- P4's `value` is a standalone type, not yet an object of `system`; tying it down
  (action on `End value` of a system object) needs computable `SMul` on hom subtypes
  — deferred.
- P5's non-isotriviality is base-side by necessity (see decision 2); a
  transport-side strengthening awaits the game-doctrine instance (c), where the
  base is the 2-groupoid of contexts.
- `REVIEW(citation)` tags remain on section-level pins (Barrett/Hardy/CDP/Wigner/
  Dummit–Foote/Mac Lane/Cover–Thomas) per the W5 citation process.
