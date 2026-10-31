/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringMath.Foundations.Eta
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Basic.NNReal.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.End
import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# The physical doctrine structure and its calibration registry

`PhysicalDoctrine` bundles the five physicality axioms (P1-P5) as explicit
structure fields - never as `axiom` declarations - and the calibration registry
proves two non-vacuity instances by theorem: the terminal (trivial) doctrine
and the classical-probability doctrine riding mathlib's `MeasureTheory` /
`InformationTheory` entry points at the pinned mathlib `v4.35.0-rc3`.
The game-doctrine instance is deferred (post-V.0); ports are out of scope.

Design decisions (Coverage vs GrothendieckTopology for P3, prop vs data for P5
non-isotriviality, and the GOLD findings at the pin) are recorded in
`docs/PhysicalDoctrine.md`.

## References
* [Barrett] J. Barrett, "Information processing in generalized probabilistic
  theories", Phys. Rev. A 75, 022103 (2007), arXiv:quant-ph/0508211.
* [Hardy] L. Hardy, "Quantum theory from five reasonable axioms",
  arXiv:quant-ph/0101012 (2001).
* [CDP] G. Chiribella, G. M. D'Ariano, P. Perinotti, "Informational derivation of
  quantum theory", Phys. Rev. A 84, 012311 (2011), arXiv:1011.6451.
* [Masanes-Muller] L. Masanes, M. P. Muller, "A derivation of quantum theory from
  physical requirements", New J. Phys. 13, 063001 (2011), arXiv:1004.1483.
* [Fritz-Coecke-Spekkens] T. Fritz, B. Coecke, R. W. Spekkens, "Resource
  convertibility and ordered commutative monoids", Math. Struct. in Comp.
  Science 27, 850-938 (2017), arXiv:1504.03661.
* [Landauer] R. Landauer, "Irreversibility and heat generation in the computing
  process", Nature 237, 177-192 (1967).
* [Atiyah] M. F. Atiyah, "Topological quantum field theories", Publ. Math. IHES
  49, 1-26 (1988).
* [Wigner] E. P. Wigner, *Group Theory and its Application to the Quantum
  Mechanics of Atomic Spectra*, Academic Press, 1959.
* [Elephant] P. T. Johnstone, *Sketches of an Elephant*, Oxford, 2002, C2.1.
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed.,
  Springer, 1998.
* [Mac Lane-Moerdijk] S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*,
  Springer, 1992.
* [Dummit-Foote] D. S. Dummit, R. M. Foote, *Abstract Algebra*, 3rd ed., Wiley,
  2004.
* [Cover-Thomas] T. M. Cover, J. A. Thomas, *Elements of Information Theory*,
  2nd ed., Wiley, 2006.
* [Barendregt] H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*,
  North-Holland, 1984.
-/

universe u v w u₁ v₁ w₁ u₂ u₃ v₃

namespace BoringLab

open CategoryTheory MeasureTheory

-- Reference: [Barrett], Phys. Rev. A 75, 022103 (2007), §2 (generalized
-- probabilistic theories); [Hardy], arXiv:quant-ph/0101012, Axioms 1-5;
-- [CDP], Phys. Rev. A 84, 012311 (2011), §2; [Masanes-Muller], New J. Phys. 13,
-- 063001 (2011); [Fritz-Coecke-Spekkens], Math. Struct. in Comp. Science 27,
-- 850-938 (2017), §2 (ordered commutative monoids); [Landauer], Nature 237,
-- 177-192 (1967); [Atiyah], Publ. Math. IHES 49, 1-26 (1988), §1; [Wigner]
-- (1959); [Elephant], C2.1 (coverages).
-- REVIEW(citation): pin the section numbers of [Barrett], [Hardy], [CDP],
-- [Fritz-Coecke-Spekkens], [Wigner] in review.
/-- A **physical doctrine**: the hypothesis-generic structure of a physical
theory, with the five physicality axioms as explicit fields (never `axiom`
declarations). No field smuggles a theorem: each axiom is data or a `Prop`.

* (P1) `system` is a category of systems and processes with a distinguished
  unit/interface object `unit` (operationality: interaction is the only
  interface).
* (P2) `resource` is an ordered commutative monoid (thermodynamic ordering;
  Landauer's principle as an ordering statement). GOLD finding at the pinned
  mathlib `v4.35.0-rc3`: the bundled class `OrderedCommMonoid` no longer exists;
  the substrate is the unbundled `IsOrderedMonoid` over `CommMonoid` + `Preorder`
  (`Mathlib/Algebra/Order/Monoid/Defs.lean`).
* (P3) `locality` is a `Coverage` (not a `GrothendieckTopology`) on the category
  `neighborhood` of measurement neighborhoods: a coverage carries no saturation
  demand, matching the rawness of the axiom ([Elephant], C2.1).
* (P4) referee fairness: the group `referee` acts on the value object `value`,
  and the referee rules by the invariants, `MulAction.fixedPoints` of the action
  (Wigner-shaped).
* (P5) `transport` is a functor from the base category `base`, with
  non-isotriviality as a `Prop` field: the base contains two non-isomorphic
  objects. An image-side reading of non-isotriviality is unsatisfiable for the
  terminal doctrine, which must calibrate the structure (see
  `docs/PhysicalDoctrine.md`). -/
-- Reference: [Barrett], §2; [Elephant], C2.1; [Wigner] (1959); [Atiyah], §1;
-- [Fritz-Coecke-Spekkens], §2; [Landauer], Nature 237, 177-192 (1967).
structure PhysicalDoctrine where
  /-- (P1) The category of systems and processes. -/
  system : Type u
  /-- (P1) The category instance on `system`. -/
  [systemCategory : Category.{v} system]
  /-- (P1) The distinguished unit/interface object. -/
  unit : system
  /-- (P2) The commutative monoid of resources. -/
  resource : Type w
  /-- (P2) The commutative monoid instance on `resource`. -/
  [resourceCommMonoid : CommMonoid resource]
  /-- (P2) The preorder on `resource`. -/
  [resourcePreorder : Preorder resource]
  /-- (P2) Multiplication in `resource` is monotone in both arguments. -/
  [resourceOrderedMonoid : IsOrderedMonoid resource]
  /-- (P3) The category of measurement neighborhoods. -/
  neighborhood : Type u₁
  /-- (P3) The category instance on `neighborhood`. -/
  [neighborhoodCategory : Category.{v₁} neighborhood]
  /-- (P3) The locality field: a coverage on the category of neighborhoods. -/
  locality : Coverage neighborhood
  /-- (P4) The referee group (Wigner symmetries). -/
  referee : Type w₁
  /-- (P4) The group instance on `referee`. -/
  [refereeGroup : Group referee]
  /-- (P4) The value object (state space) acted upon by the referee. -/
  value : Type u₂
  /-- (P4) The referee action on the value object. -/
  [refereeAction : MulAction referee value]
  /-- (P4) The referee's ruling predicate on the value object. -/
  ruling : Set value
  /-- (P4) Ruling by invariants: the ruling set equals the fixed points of the
  referee action (the invariants functor). -/
  ruling_eq_invariants : ruling = MulAction.fixedPoints referee value
  /-- (P5) The base category (contexts/frames). -/
  base : Type u₃
  /-- (P5) The category instance on `base`. -/
  [baseCategory : Category.{v₃} base]
  /-- (P5) The transport functor from the base category. -/
  transport : base ⥤ system
  /-- (P5) Non-isotriviality, as a `Prop`: the base has two non-isomorphic
  objects. -/
  nonIsotrivial : ∃ (b b' : base), ¬ Nonempty (b ≅ b')

/-! ## P4 helpers: the permutation action on valuations -/

-- Reference: [Dummit-Foote], Abstract Algebra, 3rd ed., §1.7 (group actions).
-- REVIEW(citation): pin §1.7 against the physical text in review.
/-- The inverse of the identity permutation acts as the identity. -/
theorem perm_one_inv_apply (x : Fin 2) : (1 : Equiv.Perm (Fin 2))⁻¹ x = x :=
  Eq.subst (motive := fun g : Equiv.Perm (Fin 2) => g x = x) inv_one.symm (Equiv.Perm.one_apply x)

-- Reference: [Dummit-Foote], §1.7 (group actions). REVIEW(citation): pin §1.7.
/-- `(σ * τ)⁻¹` acts as `τ⁻¹` after `σ⁻¹` (the contravariant permutation action). -/
theorem perm_mul_inv_apply (σ τ : Equiv.Perm (Fin 2)) (x : Fin 2) :
    (σ * τ)⁻¹ x = τ⁻¹ (σ⁻¹ x) :=
  Eq.subst (motive := fun g : Equiv.Perm (Fin 2) => g x = τ⁻¹ (σ⁻¹ x)) (mul_inv_rev σ τ)
    (Equiv.Perm.mul_apply τ⁻¹ σ⁻¹ x)

-- Reference: [Dummit-Foote], §1.7 (the swap is an involution).
-- REVIEW(citation): pin §1.7.
/-- The swap permutation sends `1` to `0` also after inversion. -/
theorem perm_swap_inv_one :
    (Equiv.swap 0 1 : Equiv.Perm (Fin 2))⁻¹ (1 : Fin 2) = 0 :=
  (Equiv.symm_apply_eq (Equiv.swap 0 1 : Equiv.Perm (Fin 2))).2
    (Equiv.swap_apply_left 0 1).symm

-- Reference: [Dummit-Foote], §1.7 (the contravariant action of a permutation
-- group on functions out of its domain). REVIEW(citation): pin §1.7.
/-- The permutation group of `Fin 2` acts on valuations `Fin 2 → NNReal` by
precomposition with the inverse, `σ • f = fun x => f (σ⁻¹ x)`
(a left action). -/
instance permArrowSMul : SMul (Equiv.Perm (Fin 2)) (Fin 2 → NNReal) :=
  ⟨fun σ f x => f (σ⁻¹ x)⟩

-- Reference: [Barendregt], Chapter 2 (eta conversion). REVIEW(citation): pin.
/-- One-step lemma: the identity permutation acts trivially on valuations,
`(1 : Perm (Fin 2)) • f = fun x => f ((1)⁻¹ x) = fun x => f x = f`, the last step
being `BoringMath.eta`. -/
theorem perm_arrow_one_smul (f : Fin 2 → NNReal) :
    (1 : Equiv.Perm (Fin 2)) • f = f := by
  have h : (1 : Equiv.Perm (Fin 2)) • f = fun x => f x :=
    funext (fun x => congrArg f (perm_one_inv_apply x))
  exact h.trans (BoringMath.eta f)

-- Reference: [Dummit-Foote], §1.7 (multiplicativity of the action).
-- REVIEW(citation): pin §1.7.
/-- One-step lemma: the permutation action on valuations is multiplicative. -/
theorem perm_arrow_mul_smul (σ τ : Equiv.Perm (Fin 2)) (f : Fin 2 → NNReal) :
    (σ * τ) • f = σ • (τ • f) := by
  funext x
  change f ((σ * τ)⁻¹ x) = f (τ⁻¹ (σ⁻¹ x))
  exact congrArg f (perm_mul_inv_apply σ τ x)

-- Reference: [Dummit-Foote], §1.7 (group actions). REVIEW(citation): pin §1.7.
/-- The contravariant permutation action on valuations is a `MulAction`. -/
instance permArrowMulAction : MulAction (Equiv.Perm (Fin 2)) (Fin 2 → NNReal) where
  __ := permArrowSMul
  one_smul := perm_arrow_one_smul
  mul_smul := perm_arrow_mul_smul

-- Reference: [Wigner], Group Theory and its Application to the Quantum Mechanics
-- of Atomic Spectra, Academic Press, 1959 (symmetries leave the invariant states
-- fixed). REVIEW(citation): pin the chapter treating symmetry operations on states.
/-- The invariants of the `S₂`-action on `Fin 2 → NNReal` are exactly the diagonal
valuations `f 0 = f 1`. -/
theorem classical_ruling_eq_invariants :
    {f : Fin 2 → NNReal | f 0 = f 1} =
      MulAction.fixedPoints (Equiv.Perm (Fin 2)) (Fin 2 → NNReal) := by
  refine Set.ext (fun f => ⟨?_, ?_⟩)
  · intro h σ
    funext x
    change f (σ⁻¹ x) = f x
    have hf : ∀ i : Fin 2, f i = f 0 := Fin.forall_fin_two.2 ⟨Eq.refl (f 0), h.symm⟩
    exact (hf (σ⁻¹ x)).trans (hf x).symm
  · intro h
    have h1 : f ((Equiv.swap 0 1 : Equiv.Perm (Fin 2))⁻¹ (1 : Fin 2)) = f 1 :=
      congrFun (h (Equiv.swap 0 1)) 1
    exact Eq.subst (motive := fun y => f y = f 1) perm_swap_inv_one h1

/-! ## The calibration registry -/

-- Reference: [Dummit-Foote], §1.7 (the trivial action: every element is a fixed
-- point). REVIEW(citation): pin §1.7.
/-- In the terminal doctrine the ruling set `univ` equals the invariants of the
trivial `PUnit` action on `PUnit`. -/
theorem trivial_ruling_eq_invariants :
    (Set.univ : Set PUnit) = MulAction.fixedPoints PUnit PUnit :=
  Set.ext (fun a => ⟨fun _ m => Subsingleton.elim (m • a) a, fun _ => Set.mem_univ a⟩)

-- Reference: [Mac Lane], Categories for the Working Mathematician, 2nd ed.,
-- §IV.1 (the discrete category: isomorphisms are equalities).
-- REVIEW(citation): pin §IV.1 against the physical text in review.
/-- The two objects of the discrete category on `Fin 2` are not isomorphic. -/
theorem discrete_fin_two_noniso :
    ¬ Nonempty (Discrete.mk (0 : Fin 2) ≅ Discrete.mk (1 : Fin 2)) :=
  fun h => Fin.zero_ne_one' (Discrete.Hom.eq h.some.hom)

-- Reference: [Barrett], §2 (the trivial generalized probabilistic theory);
-- [Elephant], C2.1, via `GrothendieckTopology.trivial` and
-- `GrothendieckTopology.toCoverage` at the pinned mathlib v4.35.0-rc3.
-- REVIEW(citation): pin [Barrett] section in review.
/-- The terminal (trivial) doctrine: the one-object discrete category, `Nat` as
resource monoid, the trivial coverage (P3), the trivial `PUnit` action with
`univ` ruling (P4), and the constant transport from the two-object discrete base
(P5). Registry item (a), proven to satisfy `PhysicalDoctrine`. -/
def trivialDoctrine : PhysicalDoctrine.{0, 0, 0, 0, 0, 0, 0, 0, 0} where
  system := Discrete PUnit
  unit := Discrete.mk PUnit.unit
  resource := Nat
  neighborhood := Discrete PUnit
  locality := (GrothendieckTopology.trivial (Discrete PUnit)).toCoverage
  referee := PUnit
  value := PUnit
  ruling := Set.univ
  ruling_eq_invariants := trivial_ruling_eq_invariants
  base := Discrete (Fin 2)
  transport := (Functor.const (Discrete (Fin 2))).obj (Discrete.mk PUnit.unit)
  nonIsotrivial := ⟨Discrete.mk 0, Discrete.mk 1, discrete_fin_two_noniso⟩

-- Reference: [CDP], Phys. Rev. A 84, 012311 (2011), §2 (classical probability as
-- an informational-derivation instance); mathlib pin v4.35.0-rc3 entry points
-- `MeasureTheory.MeasCat` (Mathlib/MeasureTheory/Category/MeasCat.lean) and
-- `Equiv.Perm` acting on valuations.
-- REVIEW(citation): pin [CDP] section in review.
/-- The classical-probability doctrine: systems are measurable spaces
(`MeasureTheory.MeasCat`), the interface object is the one-point space, resources
are `NNReal`, locality is the trivial coverage on `MeasCat` (P3), the referee is
`S₂ = Equiv.Perm (Fin 2)` acting on valuations `Fin 2 → NNReal` with ruling by
the invariants (the diagonal, P4), and the transport is the constant functor at
the two-point measurable space from the two-object discrete base (P5). Registry
item (b), proven to satisfy `PhysicalDoctrine`. -/
def classicalDoctrine : PhysicalDoctrine.{1, 0, 0, 1, 0, 0, 0, 0, 0} where
  system := MeasCat.{0}
  unit := MeasCat.of PUnit
  resource := NNReal
  neighborhood := MeasCat.{0}
  locality := (GrothendieckTopology.trivial MeasCat.{0}).toCoverage
  referee := Equiv.Perm (Fin 2)
  value := Fin 2 → NNReal
  ruling := {f : Fin 2 → NNReal | f 0 = f 1}
  ruling_eq_invariants := classical_ruling_eq_invariants
  base := Discrete (Fin 2)
  transport := (Functor.const (Discrete (Fin 2))).obj (MeasCat.of (Fin 2))
  nonIsotrivial := ⟨Discrete.mk 0, Discrete.mk 1, discrete_fin_two_noniso⟩

-- Reference: [Barrett], §2 (the trivial theory calibrates the axioms).
-- REVIEW(citation): pin [Barrett] section in review.
/-- Non-vacuity of the registry, item (a): the terminal doctrine is a
`PhysicalDoctrine`. -/
theorem terminal_calibration :
    Nonempty PhysicalDoctrine.{0, 0, 0, 0, 0, 0, 0, 0, 0} := ⟨trivialDoctrine⟩

-- Reference: [CDP], §2 (classical probability calibrates the axioms).
-- REVIEW(citation): pin [CDP] section in review.
/-- Non-vacuity of the registry, item (b): the classical-probability doctrine is
a `PhysicalDoctrine`. -/
theorem classical_calibration :
    Nonempty PhysicalDoctrine.{1, 0, 0, 1, 0, 0, 0, 0, 0} := ⟨classicalDoctrine⟩

/-! ## The classical value map and the `InformationTheory` entry point -/

-- Reference: mathlib pin v4.35.0-rc3, `MeasureTheory.ProbabilityMeasure`
-- (Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean: probability measures as
-- the subtype `{μ : Measure Ω // IsProbabilityMeasure μ}`).
/-- The value map of the classical doctrine: a probability measure on `Fin 2`
yields a valuation `Fin 2 → NNReal` by point masses. -/
def classicalValue {μ : MeasureTheory.Measure (Fin 2)}
    [MeasureTheory.IsProbabilityMeasure μ] : Fin 2 → NNReal :=
  fun i => (μ {i}).toNNReal

-- Reference: mathlib pin v4.35.0-rc3, `Measure.dirac_apply_of_mem` and
-- `Measure.dirac.isProbabilityMeasure`
-- (Mathlib/MeasureTheory/Measure/Dirac/Basic.lean).
/-- The Dirac state at `i` has value `1` at `i`. -/
theorem classical_value_dirac_self (i : Fin 2) :
    classicalValue (μ := MeasureTheory.Measure.dirac i) i = 1 :=
  (congrArg ENNReal.toNNReal
    (Measure.dirac_apply_of_mem (Set.mem_singleton i))).trans ENNReal.toNNReal_one

-- Reference: [Cover-Thomas], Elements of Information Theory, 2nd ed., Ch. 2
-- (relative entropy is nonnegative, with equality iff the measures are equal),
-- as `InformationTheory.klDiv_eq_zero_iff` at mathlib pin v4.35.0-rc3
-- (Mathlib/InformationTheory/KullbackLeibler/Basic.lean).
-- REVIEW(citation): pin the theorem number in [Cover-Thomas] in review.
/-- Calibration at the `InformationTheory` entry point: for probability measures
on `Fin 2`, the Kullback-Leibler divergence vanishes exactly on the diagonal. -/
theorem classical_klDiv_eq_zero_iff_eq {μ ν : MeasureTheory.Measure (Fin 2)}
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν] :
    InformationTheory.klDiv μ ν = 0 ↔ μ = ν :=
  InformationTheory.klDiv_eq_zero_iff


end BoringLab
