/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.TheoryElement

/-!
# The theory-element category: BMS links as morphisms

Ticket #62 (EPI.2.2), building on the theory-elements of #30
(`BoringLab.Epistemology.TheoryElement`). The category-native part of the
Balzer–Moulines–Sneed formalism, as data:

* objects: theory-elements (`TheoryElement carrier`);
* morphisms: **links** (`TheoryLink`) — a specialization link `t → t'` (the
  BMS relation: `t'`'s models and intended applications are subsets of
  `t`'s, and the actual-model predicate agrees on them);
* composition (`TheoryLink.comp`), identity (`TheoryLink.id`), with
  associativity and unit laws PROVED (the law fields are `Prop`, so the
  structure equalities close by `cases` + `rfl` — relational composition at
  data level, proved anyway per house style);
* this is the DOMAIN category of the ladder functor of EPI.7.5 (#61) — the
  connection is recorded at comment level (statement layer, graded);
* the analyticity enrichment of #62 lives here: `AnalyticTheoryElement`
  extends the theory-element data with the analyticity ledger (the
  theory-internal observable structure), so the EM/AP obstruction of #61
  is handled at the domain;
* the Kuhn dynamics row (#34) acts on this category — normal science =
  accumulation along specializations, revolution = a base change — graded
  interpretation, statement layer, no dynamics-claim (D.4 tag).

## References
* [BMS] W. Balzer, C. U. Moulines, J. D. Sneed, *An Architectonic for
  Science: The Structuralist Program*, Synthese Library vol. 186, D. Reidel,
  1987, ch. 2 (theory-elements and their links; specialization).
* [Sneed] J. D. Sneed, *The Logical Structure of Mathematical Physics*,
  Synthese Library vol. 114, 1979, ch. 2.
* [Suppes] P. Suppes, *Representation and Invariance of Scientific
  Structures*, CSLI Publications, 2002, sec. 2.2.
* Program register: BoringLab tickets #30 (EPI.2.1, landed) and #62
  (EPI.2.2); the toy is the #30 coin theory-element, the program's own.
-/

universe u

namespace BoringLab

/-! ## Links (morphisms of theory-elements) -/

-- Reference: [BMS], ch. 2 (specialization: T' specializes T when T' is a
-- sub-structure of T — models and intended applications included, with the
-- predicates agreeing); ticket #62, morphisms (a).
-- REVIEW(citation): pin the exact definition of specialization in [BMS].
/-- A **link** (specialization) from theory-element `t` to `t'`: `t'`'s
potential models and intended applications are subsets of `t`'s, and the
actual-model predicate agrees on them. -/
structure TheoryLink (carrier : Type u) (t t' : TheoryElement carrier) where
  /-- The potential models of `t'` are among those of `t`. -/
  models_subset : ∀ m ∈ t'.models, m ∈ t.models
  /-- The actual-model predicate agrees on `t'`'s models. -/
  actual_agree : ∀ m ∈ t'.models, t'.isActual m = t.isActual m
  /-- The intended applications of `t'` are among those of `t`. -/
  apps_subset : ∀ i ∈ t'.applications, i ∈ t.applications

-- Reference: [Barendregt], ch. 2 (eta conversion), as in
-- `Truncation.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for theory links**. -/
theorem TheoryLink.eta {carrier : Type u} {t t' : TheoryElement carrier}
    (f : TheoryLink carrier t t') :
    TheoryLink.mk f.models_subset f.actual_agree f.apps_subset = f := by
  cases f with
  | mk models_subset actual_agree apps_subset => rfl

-- Reference: [BMS], ch. 2 (the identity link); definitional on the fields.
-- `linter.defProp` is off here: a link is a Prop-valued structure, and `id`
-- must stay a computable `def` (the unit law closes by `cases` + `rfl`).
set_option linter.defProp false in
/-- The **identity link** of a theory-element. -/
def TheoryLink.id {carrier : Type u} (t : TheoryElement carrier) :
    TheoryLink carrier t t where
  models_subset := fun _ hm => hm
  actual_agree := fun _ _ => rfl
  apps_subset := fun _ hi => hi

-- Reference: [BMS], ch. 2 (links compose); ticket #62, composition =
-- specialization composition. `linter.defProp` off as on `TheoryLink.id`.
set_option linter.defProp false in
/-- **Composition of links**: `t → t' → t''` composes field-wise. -/
def TheoryLink.comp {carrier : Type u} {t t' t'' : TheoryElement carrier}
    (f : TheoryLink carrier t t') (g : TheoryLink carrier t' t'') :
    TheoryLink carrier t t'' where
  models_subset := fun m hm => f.models_subset m (g.models_subset m hm)
  actual_agree := fun m hm =>
    (g.actual_agree m hm).trans (f.actual_agree m (g.models_subset m hm))
  apps_subset := fun i hi => f.apps_subset i (g.apps_subset i hi)

-- Reference: [BMS], ch. 2 (associativity of link composition); the law
-- fields are `Prop`, so the equality closes by proof irrelevance after
-- `cases` (house style: proved anyway, relational composition is trivial
-- at data level).
/-- **Associativity of link composition**. -/
theorem TheoryLink.comp_assoc {carrier : Type u} {t t' t'' t''' : TheoryElement carrier}
    (f : TheoryLink carrier t t') (g : TheoryLink carrier t' t'')
    (h : TheoryLink carrier t'' t''') :
    TheoryLink.comp (TheoryLink.comp f g) h = TheoryLink.comp f (TheoryLink.comp g h) := by
  cases f; cases g; cases h; rfl

-- Reference: [BMS], ch. 2 (unit laws); definitional eta on the `Prop`
-- fields closes by `cases` + `rfl`.
/-- The **unit laws** of link composition. -/
theorem TheoryLink.comp_id {carrier : Type u} {t t' : TheoryElement carrier}
    (f : TheoryLink carrier t t') :
    TheoryLink.comp f (TheoryLink.id t') = f ∧ TheoryLink.comp (TheoryLink.id t) f = f := by
  cases f; exact ⟨rfl, rfl⟩

/-! ## The analyticity enrichment (the #62 domain fix) -/

-- Reference: ticket #62 (the analyticity enrichment: the domain must
-- remember analyticity — the analytic/smooth ledger of the theory's
-- observable structure — so the EM/AP obstruction of #61 is handled at the
-- domain, not by fiat).
/-- An **analytic theory-element**: a theory-element plus its analyticity
ledger (the theory-internal components of the observable structure). -/
structure AnalyticTheoryElement (carrier : Type u) extends TheoryElement carrier where
  /-- The analyticity ledger: the theory-internal components. -/
  analyticLedger : List carrier

-- Reference: [Barendregt], ch. 2 (eta conversion), as in
-- `Truncation.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for analytic theory-elements**. -/
theorem AnalyticTheoryElement.eta {carrier : Type u} (a : AnalyticTheoryElement carrier) :
    AnalyticTheoryElement.mk a.toTheoryElement a.analyticLedger = a := by
  cases a with
  | mk toTheoryElement analyticLedger => rfl

/-! ## Toy: the coin theory-element of #30 and a specialization -/

-- Reference: program's own toy (the #30 coin family, narrowed).
/-- The narrowed coin theory-element: only the two nonempty models of length
≤ 2 headed by `true`, the same actual predicate and application. -/
def coinTheoryNarrow : TheoryElement CoinData :=
  { models := [[true], [true, false]]
    isActual := coinActual
    isPartial := fun _ => true
    applications := [coinObserved]
    links := []
    empiricalClaim := coinTheory_empirical }

-- Reference: [BMS], ch. 2 (specialization); ticket #62, instance: the
-- narrowed coin theory specializes the full coin theory — membership steps
-- through `List.mem_cons`.
/-- **Instance link**: `coinTheoryNarrow` specializes `coinTheory`. -/
theorem coinLink : TheoryLink CoinData coinTheory coinTheoryNarrow where
  models_subset := by
    intro m hm
    have hmem1 : ([true] : CoinData) ∈ coinModels := by
      unfold coinModels
      exact List.mem_cons_of_mem [] (List.mem_cons_self)
    have hmem2 : ([true, false] : CoinData) ∈ coinModels := by
      unfold coinModels
      exact List.mem_cons_of_mem [] (List.mem_cons_of_mem [true]
        (List.mem_cons_of_mem [false] (List.mem_cons_of_mem [true, true]
          (List.mem_cons_self))))
    rcases List.mem_cons.mp hm with h1 | h2
    · exact Eq.subst (motive := fun x => x ∈ coinModels) h1.symm hmem1
    · rcases List.mem_cons.mp h2 with h2' | h2n
      · exact Eq.subst (motive := fun x => x ∈ coinModels) h2'.symm hmem2
      · exact absurd h2n List.not_mem_nil
  actual_agree := fun _ _ => rfl
  apps_subset := fun i hi => by
    rcases List.mem_cons.mp hi with h | hn
    · exact Eq.subst (motive := fun x => x ∈ [coinObserved]) h.symm List.mem_cons_self
    · exact absurd hn List.not_mem_nil

end BoringLab
