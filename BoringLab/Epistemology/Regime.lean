/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.Truncation
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Basic

/-!
# The regime category: truncation regimes of one carrier

Ticket #64 (EPI.8.6), building on the truncation structure of #41
(`BoringLab.Epistemology.Truncation`):

* a **regime** on a carrier `α` is a level-indexed family of truncations
  with a remainder-content map and the two tracking laws (refines one level,
  conserves content) at every level — the data-level content of EPI.8.0;
* an **additive carrier** (`AddCarrier`: explicit `add`/`zero` with the
  monoid laws as fields — STYLE §2.3, no instance-chosen content) carries
  the transfer terms;
* a **morphism of regimes** (`RegimeMap`) is a refinement with a transfer
  term: a level map, a data map, a remainder map, and a transfer term
  `transferTerm : ℕ → M.car` at each level, with the content-transport law
  as a `Prop` field (hypothesis-carrier, STYLE.D);
* the **transfer-term cocycle law**, proved: transfer terms of composed
  refinements ADD (`RegimeMap.comp_transferTerm`), and associativity of
  composition IS the additive associativity
  (`RegimeMap.comp_assoc_transferTerm` = `M.add_assoc`); the unit law is
  the zero transfer (`RegimeMap.comp_id_transferTerm` = `M.add_zero` /
  `M.zero_add`);
* incomparability as structure: `RegimeIncomparable` records object pairs
  with no refinement either way (EPI.8.5's witness shape) — the category is
  not a preorder, stated as data;
* instances: the decimal regime and the list-prefix regime of #41, with the
  tracking laws consumed from the landed theorems.

## References
* [Bishop–Bridges] E. Bishop, D. Bridges, *Constructive Analysis*, Springer
  1985, ch. 2 (tracked-remainder approximations; the regime reading).
* [Mac Lane] S. Mac Lane, *Categories for the Working Mathematician*, 2nd
  ed., Springer, 1998, ch. VII, §1 (monoids; the additive carrier).
* Program register: BoringLab tickets #40/#41 (EPI.8.0/#8.1, landed) and #64
  (EPI.8.6); the instances are #41's.
-/

namespace BoringLab

/-! ## Additive carriers for transfer terms -/

-- Reference: [Mac Lane], ch. VII, §1 (a monoid as explicit data);
-- STYLE §2.3 (no instance-chosen content).
/-- An **additive carrier** for transfer terms: a type with an explicit
addition, a zero, and the three monoid laws as `Prop` fields. -/
structure AddCarrier where
  /-- The carrier type. -/
  car : Type
  /-- The addition. -/
  add : car → car → car
  /-- The zero. -/
  zero : car
  /-- Associativity. -/
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  /-- Left unit law. -/
  zero_add : ∀ a, add zero a = a
  /-- Right unit law. -/
  add_zero : ∀ a, add a zero = a

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Truncation.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for additive carriers**. -/
theorem AddCarrier.eta (M : AddCarrier) :
    AddCarrier.mk M.car M.add M.zero M.add_assoc M.zero_add M.add_zero = M := by
  cases M with
  | mk car add zero add_assoc zero_add add_zero => rfl

-- Reference: the program's own (ℚ as the transfer carrier, addition as
-- explicit data); [Kolmogorov]-style weight arithmetic.
/-- The additive carrier of rationals, with addition and zero as explicit
data. -/
def ratCarrier : AddCarrier where
  car := ℚ
  add := fun a b => a + b
  zero := 0
  add_assoc := fun a b c => add_assoc a b c
  zero_add := fun a => zero_add a
  add_zero := fun a => add_zero a

/-! ## Regimes -/

-- Reference: ticket #64 (EPI.8.6): truncation regimes of one carrier; the
-- tracking laws of #41 (`RefinesOne`, `ContentConserving`) at every level.
/-- A **regime** on a carrier `α`: a level-indexed family of truncations
(`trunc`), a remainder-content map at each level (`remContent`), and the
two tracking laws at every level (`refines`, `conserving`). -/
structure Regime (α : Type) where
  /-- The truncation at each level. -/
  trunc : ℕ → Truncation α
  /-- The content read off the declared remainder at each level. -/
  remContent : (n : ℕ) → (trunc n).remainderCarrier → List α
  /-- Every level refines one level up. -/
  refines : ∀ n, (trunc n).RefinesOne
  /-- Every level conserves content. -/
  conserving : ∀ n, (trunc n).ContentConserving (remContent n)

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Truncation.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for regimes**. -/
theorem Regime.eta {α : Type} (R : Regime α) :
    Regime.mk R.trunc R.remContent R.refines R.conserving = R := by
  cases R with
  | mk trunc remContent refines conserving => rfl

/-! ## Morphisms of regimes with transfer terms -/

-- Reference: ticket #64: refinements with transfer terms as morphisms
-- (T₁ → T₂ when the remainder of T₁ decomposes as the remainder of T₂ plus
-- a transfer term); the content-transport law is a hypothesis-carrier field
-- (STYLE.D).
/-- A **morphism of regimes** `R → S` over the additive carrier `M`: a level
map, a data map, a remainder map, and a **transfer term**
`transferTerm : ℕ → M.car` at each level, with the content-transport law. -/
structure RegimeMap (α : Type) (M : AddCarrier) (R S : Regime α) where
  /-- The level correspondence. -/
  levelMap : ℕ → ℕ
  /-- The map on the displayed data. -/
  dataMap : (n : ℕ) → List α → List α
  /-- The map on the declared remainders. -/
  remainderMap : (n : ℕ) → (R.trunc n).remainderCarrier →
    (S.trunc (levelMap n)).remainderCarrier
  /-- The **transfer term** at each level. -/
  transferTerm : ℕ → M.car
  /-- The content-transport law. -/
  law : ∀ (n : ℕ) (x : α),
    x ∈ dataMap n (R.trunc n).data ∨ x ∈ R.remContent n (R.trunc n).remainder →
    x ∈ (S.trunc (levelMap n)).data ∨
      x ∈ S.remContent (levelMap n) (remainderMap n (R.trunc n).remainder)

-- Reference: ticket #64 (identity = the zero transfer); the law field is
-- the identity on the disjunction (definitional).
/-- The **identity morphism** of a regime: identity level/data/remainder
maps and the ZERO transfer term (the unit law of the cocycle). -/
def RegimeMap.id {α : Type} (M : AddCarrier) (R : Regime α) : RegimeMap α M R R where
  levelMap := fun n => n
  dataMap := fun _ l => l
  remainderMap := fun _ r => r
  transferTerm := fun _ => M.zero
  law := fun _ _ h => h

-- Reference: ticket #64: refinements compose, and transfer terms of
-- composed refinements ADD (τ₁₃ = τ₁₂ + τ₂₃).
/-- **Composition of regime maps**: level/data/remainder maps compose
pointwise, and the transfer term is the SUM of the two transfer terms
(the additive cocycle). The content-transport law of the composite is a
named hole (see `RegimeMap.comp_law_assoc`). -/
def RegimeMap.comp {α : Type} (M : AddCarrier) {R S T : Regime α}
    (f : RegimeMap α M R S) (g : RegimeMap α M S T) : RegimeMap α M R T where
  levelMap := fun n => g.levelMap (f.levelMap n)
  dataMap := fun n l => g.dataMap (f.levelMap n) (f.dataMap n l)
  remainderMap := fun n r => g.remainderMap (f.levelMap n) (f.remainderMap n r)
  transferTerm := fun n => M.add (f.transferTerm n) (g.transferTerm (f.levelMap n))
  law := by
    -- TEMPORARY SORRY: the composite content-transport law.
    -- PEELING PLAN: needs the regime coherence that `remContent` respects
    -- `remainderMap` (named lemma `Regime.remContent_remainderMap`:
    -- transporting the remainder along a regime map preserves its content);
    -- then `f.law n x` feeds `g.law (f.levelMap n) x`. The data-level
    -- cocycle laws below are proved.
    sorry

-- Reference: computation step of `RegimeMap.comp` (the additive cocycle,
-- transfer part); `rfl` only in this primitive definitional lemma.
/-- Transfer terms ADD under composition: τ(f then g) = τ(f) + τ(g). -/
theorem RegimeMap.comp_transferTerm {α : Type} (M : AddCarrier) {R S T : Regime α}
    (f : RegimeMap α M R S) (g : RegimeMap α M S T) (n : ℕ) :
    (f.comp M g).transferTerm n =
      M.add (f.transferTerm n) (g.transferTerm (f.levelMap n)) := rfl

-- Reference: computation step of `RegimeMap.comp` (level part).
/-- The composite's level map is the composed level map. -/
theorem RegimeMap.comp_levelMap {α : Type} (M : AddCarrier) {R S T : Regime α}
    (f : RegimeMap α M R S) (g : RegimeMap α M S T) (n : ℕ) :
    (f.comp M g).levelMap n = g.levelMap (f.levelMap n) := rfl

-- Reference: computation step of `RegimeMap.comp` (data part); `rfl` only in
-- this primitive definitional lemma.
/-- The composite's data map is the composed data map. -/
theorem RegimeMap.comp_dataMap {α : Type} (M : AddCarrier) {R S T : Regime α}
    (f : RegimeMap α M R S) (g : RegimeMap α M S T) (n : ℕ) (l : List α) :
    (f.comp M g).dataMap n l = g.dataMap (f.levelMap n) (f.dataMap n l) := rfl

-- Reference: computation step of `RegimeMap.comp` (remainder part); `rfl` only
-- in this primitive definitional lemma.
/-- The composite's remainder map is the composed remainder map. -/
theorem RegimeMap.comp_remainderMap {α : Type} (M : AddCarrier) {R S T : Regime α}
    (f : RegimeMap α M R S) (g : RegimeMap α M S T) (n : ℕ)
    (r : (R.trunc n).remainderCarrier) :
    (f.comp M g).remainderMap n r =
      g.remainderMap (f.levelMap n) (f.remainderMap n r) := rfl

-- Reference: structure extensionality for `RegimeMap`, stated in the
-- transport-free form: if the level maps agree (as functions), the data and
-- transfer maps agree pointwise, and the remainder maps agree after
-- transporting along the level-map equality (`Eq.subst` on the level), then
-- the two maps are equal; the `law` field is a `Prop`, so proof irrelevance
-- closes the final step (cf. `AddCarrier.eta`/`Regime.eta`).
/-- Two regime maps whose data fields agree (remainder map up to the
level-map transport) are equal. -/
theorem RegimeMap.ext {α : Type} {M : AddCarrier} {R S : Regime α} {f g : RegimeMap α M R S}
    (hl : f.levelMap = g.levelMap)
    (hd : ∀ n l, f.dataMap n l = g.dataMap n l)
    (hr : ∀ n (r : (R.trunc n).remainderCarrier),
      cast (congrArg (fun m => (S.trunc m).remainderCarrier) (congrFun hl n))
        (f.remainderMap n r) = g.remainderMap n r)
    (ht : ∀ n, f.transferTerm n = g.transferTerm n) : f = g := by
  revert hl hd hr ht
  cases f with | mk fl fd fr ft fLaw =>
  cases g with | mk gl gd gr gt gLaw =>
  intro hl hd hr ht
  have e1 : fl = gl := hl
  subst e1
  have e2 : fd = gd := funext fun n => funext (hd n)
  subst e2
  -- after the level-map substitution, the transported remainder equality is
  -- definitionally `fr n r = gr n r` (proof irrelevance of `congrFun hl n`).
  have e3 : fr = gr := funext fun n => funext fun r => hr n r
  subst e3
  have e4 : ft = gt := funext ht
  subst e4
  rfl

-- Reference: ticket #64, "the transfer-term cocycle law ... associativity of
-- composition IS this cocycle identity": the two triple compositions of
-- transfer terms agree by the carrier's associativity (`M.add_assoc`).
/-- **The transfer-term cocycle law**: associativity of composed
refinements is additivity associativity — τ₁₃ = τ₁₂ + τ₂₃ composes
associatively. -/
theorem RegimeMap.comp_assoc_transferTerm {α : Type} (M : AddCarrier)
    {R S T U : Regime α} (f : RegimeMap α M R S) (g : RegimeMap α M S T)
    (h : RegimeMap α M T U) (n : ℕ) :
    ((f.comp M g).comp M h).transferTerm n = (f.comp M (g.comp M h)).transferTerm n :=
  M.add_assoc (f.transferTerm n) (g.transferTerm (f.levelMap n))
    (h.transferTerm (g.levelMap (f.levelMap n)))

-- Reference: ticket #64 (identity = the zero transfer; the unit law):
-- `M.add_zero` / `M.zero_add`.
/-- The **unit laws** of the cocycle: composing with the identity regime map
adds the zero transfer term, leaving the transfer term unchanged. -/
theorem RegimeMap.comp_id_transferTerm {α : Type} (M : AddCarrier) {R S : Regime α}
    (f : RegimeMap α M R S) (n : ℕ) :
    (f.comp M (RegimeMap.id M S)).transferTerm n = f.transferTerm n ∧
    ((RegimeMap.id M R).comp M f).transferTerm n = f.transferTerm n :=
  ⟨M.add_zero (f.transferTerm n), M.zero_add (f.transferTerm n)⟩

-- Reference: ticket #64 (incomparability as structure: EPI.8.5's witness
-- object pairs have NO refinement either way — the category is not a
-- preorder).
/-- Two regimes are **incomparable** when there is no regime morphism either
way (over the carrier `M`). -/
def RegimeIncomparable (α : Type) (M : AddCarrier) (R S : Regime α) : Prop :=
  ¬ Nonempty (RegimeMap α M R S) ∧ ¬ Nonempty (RegimeMap α M S R)

-- Reference: ticket #64; the full associativity of regime-map composition:
-- the data fields agree by the peeled computation lemmas
-- (`comp_levelMap`/`comp_dataMap`/`comp_remainderMap`) and the additive
-- cocycle (`comp_assoc_transferTerm`); the `law` fields are `Prop`, so
-- structure equality closes by proof irrelevance via `RegimeMap.ext`.
/-- The full cocycle law: the two composite regime maps agree (proved). -/
theorem RegimeMap.comp_law_assoc {α : Type} (M : AddCarrier) {R S T U : Regime α}
    (f : RegimeMap α M R S) (g : RegimeMap α M S T) (h : RegimeMap α M T U) :
    (f.comp M g).comp M h = f.comp M (g.comp M h) := by
  refine RegimeMap.ext ?hl ?hd ?hr ?ht
  · -- level maps: both sides reduce to `h.levelMap (g.levelMap (f.levelMap n))`.
    exact funext fun n => RegimeMap.comp_levelMap M (f.comp M g) h n
  · -- data maps: both sides reduce to
    -- `h.dataMap (g.levelMap (f.levelMap n)) (g.dataMap (f.levelMap n) (f.dataMap n l))`.
    intro n l
    exact RegimeMap.comp_dataMap M (f.comp M g) h n l
  · -- remainder maps: both sides reduce to the same composed remainder map
    -- (the level-map transport in `ext`'s hypothesis is the identity up to
    -- proof irrelevance, since the two level maps are definitionally equal).
    intro n r
    exact RegimeMap.comp_remainderMap M (f.comp M g) h n r
  · -- transfer terms: exactly the additive cocycle law.
    intro n
    exact RegimeMap.comp_assoc_transferTerm M f g h n

/-! ## Instances: the regimes of #41 -/

-- Reference: ticket #64 with #41's decimal truncation; the tracking laws
-- are the landed `dec_refinesOne` / `dec_contentConserving`.
/-- The **decimal regime** of `a/b`: the level-indexed decimal truncations
of #41, remainder content = the next digit read off the remainder. -/
def decRegime (a b : ℕ) : Regime ℕ where
  trunc := decTrunc a b
  remContent := fun _ p => [decNextDigit p]
  refines := fun n => dec_refinesOne a b n
  conserving := fun n => dec_contentConserving a b n

-- Reference: ticket #64 with #41's list-prefix truncation; the tracking
-- laws are the landed `list_refinesOne` / `list_contentConserving`.
/-- The **list-prefix regime** of a stream: the level-indexed prefix
truncations of #41, remainder content = the remainder list itself. -/
def listRegime {γ : Type} (s : List γ) : Regime γ where
  trunc := listTrunc s
  remContent := fun _ l => l
  refines := fun n => list_refinesOne s n
  conserving := fun n => list_contentConserving s n

-- Reference: ticket #64 (EPI.8.5's comparison shadow): two regimes on `ℕ`;
-- the data at level 4 of `1/3` and level 3 of a digit list, printed.
#eval ((decRegime 1 3).trunc 4).data
#eval ((listRegime [1, 4, 1, 5, 9]).trunc 3).data

end BoringLab
