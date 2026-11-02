/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.TheoryCategory
import BoringLab.Epistemology.SampleComplexity
import Mathlib.CategoryTheory.Category.Basic

/-!
# Learning as a limit: hypotheses as theory-elements, identification as a
limiting cone

Ticket #165 (EPI.9.1), building on #62's theory-element category
(`TheoryElement`/`TheoryLink`, `BoringLab.Epistemology.TheoryCategory`),
#31's `IdentifiesInLimit`, and #43's `TruncatedIdentification`.

* `hypTheory` — a hypothesis `h` (with mass function and outcome list) as a
  theory-element over the datum carrier: its potential models are the
  allowed outcomes (the Popper-content reading of #28/#32);
* `link_of_allowed_subset` — PROVED: if `h'`'s allowed set is contained in
  `h`'s, there is a specialization link `hypTheory h → hypTheory h'`
  (falsification/refinement = specialization, data-level);
* `IsLimitingOutput` / `IsLimitingOutputAtLevel` — identification past a
  bound, restated as a limit; PROVED iff-lemmas against #31's
  `IdentifiesInLimit` (singleton) and #43's `TruncatedIdentification`;
* `identification_stable_links` — PROVED: identification makes the output
  theory-chain eventually the identity link (the limiting cone);
* toy: `coinLink_loaded_of_fair` (loaded specializes fair, PROVED) and the
  NEGATIVE `no_link_loaded_to_fair` (PROVED); `coin_elim_isLimiting` (the coin
  elimination learner identifies the fair coin, PROVED); `#eval` prints the
  models of each coin hypothesis-theory;
* `theoryElementCategory` — named hole: the `Category` instance (peeling
  plan below).

## References
* [BMS] Balzer–Moulines–Sneed, *An Architectonic for Science*, 1987, ch. 2
  (theory-elements, specialization links) — via #62.
* [Gold] E. M. Gold 1967 (identification in the limit) — via #31.
* [Sneed] 1979, ch. 2. Program register: BoringLab tickets #165 (EPI.9.1),
  #30, #31, #43, #62. REVIEW(citation): pin the categorical colimit reading
  at review; the ∞-categorical reading stays parked per gate G4 (tracker #2).
-/

namespace BoringLab

/-! ## Hypotheses as theory-elements -/

-- Reference: ticket #165 — [Sneed] ch. 2 via #30/#62: the potential models
-- of the hypothesis-theory are the allowed outcomes (the #28/#32 Popper
-- content as the model set). All data explicit (STYLE §2.3).
/-- The **theory-element of a hypothesis**: over the datum carrier, potential
models = the allowed outcomes in `os`; no intended applications (the claim
field is vacuous); actual/partial predicates trivial. -/
def hypTheory {datum : Type} (mass : datum → ℚ) (os : List datum) : TheoryElement datum where
  models := os.filter (fun d => if mass d = 0 then false else true)
  isActual := fun _ => true
  isPartial := fun _ => true
  applications := []
  links := []
  empiricalClaim := fun _ hi => absurd hi List.not_mem_nil

-- Reference: ticket #165 — computation: membership in the models is
-- membership in `os` plus allowance (`List.mem_filter`); `massAllows` is the
-- same `ite` (`unfold massAllows`).
/-- Membership in the hypothesis-theory's models. -/
theorem mem_hypTheory_models {datum : Type} (mass : datum → ℚ) (os : List datum)
    (m : datum) :
    m ∈ (hypTheory mass os).models ↔ m ∈ os ∧ (if mass m = 0 then false else true) = true :=
  List.mem_filter

-- Reference: ticket #165 — PROVED: refinement of allowed sets is a
-- specialization link ([BMS] ch. 2 via #62). `List.mem_filter` both ways;
-- the actual predicates are constant `true`, so `actual_agree` is `rfl`.
/-- **Falsification/refinement is specialization**: if every outcome allowed
by `h'` is allowed by `h`, there is a link `hypTheory h → hypTheory h'`. -/
theorem link_of_allowed_subset {hyp datum : Type} (mass : hyp → datum → ℚ)
    (os : List datum) (h h' : hyp)
    (hsub : ∀ d ∈ os, (if mass h' d = 0 then false else true) = true →
      (if mass h d = 0 then false else true) = true) :
    TheoryLink datum (hypTheory (mass h) os) (hypTheory (mass h') os) where
  models_subset := fun m hm => by
    rcases List.mem_filter.mp hm with ⟨hmos, hma⟩
    exact List.mem_filter.mpr ⟨hmos, hsub m hmos hma⟩
  actual_agree := fun _ _ => rfl
  apps_subset := fun i hi => absurd hi List.not_mem_nil

/-! ## Identification as a limit -/

-- Reference: ticket #165 — [Gold] 1967 via #31: the limit reading of
-- identification — the output is `h` on every compatible prefix past a
-- bound (the cone is limiting on the finite-prefix carrier).
/-- **Limiting output**: the learner outputs `h` on every compatible prefix
past a bound `N`. -/
def IsLimitingOutput {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (h : hyp) : Prop :=
  ∃ N : ℕ, ∀ p : List datum, Compatible mass h p → N ≤ p.length → M p = h

-- Reference: ticket #165 — PROVED: `IdentifiesInLimit` on the singleton
-- `[h]` is exactly `IsLimitingOutput` (`List.mem_cons`).
/-- Identification of the singleton family iff the output is limiting. -/
theorem identifiesInLimit_singleton_iff {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (h : hyp) :
    IdentifiesInLimit M mass [h] ↔ IsLimitingOutput M mass h := by
  refine Iff.intro (fun hid => hid h List.mem_cons_self) (fun hlim h' hh' => ?_)
  rcases List.mem_cons.mp hh' with he | hn
  · exact Eq.subst (motive := fun x => ∃ N : ℕ, ∀ p : List datum,
      Compatible mass x p → N ≤ p.length → M p = x) he.symm hlim
  · exact absurd hn List.not_mem_nil

-- Reference: ticket #165 — the level-`n` form (#43's truncation of the cone).
/-- **Limiting output at level `n`**: the output is `h` on every compatible
prefix of length `≤ n` past a bound `N`. -/
def IsLimitingOutputAtLevel {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (h : hyp) (n : ℕ) : Prop :=
  ∃ N : ℕ, ∀ p : List datum, Compatible mass h p → p.length ≤ n → N ≤ p.length →
    M p = h

-- Reference: ticket #165 — PROVED: #43's `TruncatedIdentification` on the
-- singleton `[h]` is exactly `IsLimitingOutputAtLevel` at level `n`.
/-- Truncated identification of the singleton family iff the output is
limiting at level `n`. -/
theorem truncatedIdentification_singleton_iff {hyp datum : Type} (M : List datum → hyp)
    (mass : hyp → datum → ℚ) (h : hyp) (n : ℕ) :
    TruncatedIdentification M mass [h] n ↔ IsLimitingOutputAtLevel M mass h n := by
  refine Iff.intro (fun hid => hid h List.mem_cons_self) (fun hlim h' hh' => ?_)
  rcases List.mem_cons.mp hh' with he | hn
  · exact Eq.subst (motive := fun x => ∃ N : ℕ, ∀ p : List datum,
      Compatible mass x p → p.length ≤ n → N ≤ p.length → M p = x) he.symm hlim
  · exact absurd hn List.not_mem_nil

-- Reference: ticket #165 — PROVED: identification makes the output
-- theory-chain eventually the identity link (the limiting cone): past `N`,
-- `M p = M q = h`, so the link is `TheoryLink.id` after `Eq.subst`.
/-- **Identification stabilizes the output theory-chain**: past the bound,
the theory-elements of any two outputs are linked by the identity. -/
theorem identification_stable_links {hyp datum : Type} (mass : hyp → datum → ℚ)
    (os : List datum) (M : List datum → hyp) (h : hyp)
    (hlim : IsLimitingOutput M mass h) :
    ∃ N : ℕ, ∀ p q : List datum, Compatible mass h p → Compatible mass h q →
      N ≤ p.length → N ≤ q.length →
      TheoryLink datum (hypTheory (mass (M p)) os) (hypTheory (mass (M q)) os) := by
  obtain ⟨N, hN⟩ := hlim
  refine ⟨N, fun p q hpc hqc hpN hqN => ?_⟩
  have e1 : M p = h := hN p hpc hpN
  have e2 : M q = h := hN q hqc hqN
  exact Eq.subst (motive := fun x => TheoryLink datum (hypTheory (mass x) os)
      (hypTheory (mass (M q)) os)) e1.symm
    (Eq.subst (motive := fun y => TheoryLink datum (hypTheory (mass h) os)
      (hypTheory (mass y) os)) e2.symm (TheoryLink.id (hypTheory (mass h) os)))

/-! ## Toy: the coin hypothesis-theories -/

-- Reference: ticket #165 toy — PROVED: the loaded coin's theory-element
-- specializes the fair coin's (allowed(loaded) = {heads} ⊆ allowed(fair)),
-- via `link_of_allowed_subset` + `massAllows_coin_fair` (#163).
/-- **The loaded coin specializes the fair coin** (falsification as
specialization, data-level). -/
theorem coinLink_loaded_of_fair :
    TheoryLink Coin (hypTheory (coinMass CoinHyp.fair) coinOutcomes)
      (hypTheory (coinMass CoinHyp.loaded) coinOutcomes) :=
  link_of_allowed_subset coinMass coinOutcomes CoinHyp.fair CoinHyp.loaded
    (fun d _ _ => massAllows_coin_fair d)

-- Reference: ticket #165 toy, NEGATIVE RESULT (first-class): the converse
-- link does not exist — `tails` is a model of the fair theory
-- (`massAllows_coin_fair`) but not of the loaded one
-- (`massAllows_coin_loaded_tails`, #163).
/-- **NEGATIVE**: the loaded coin's theory-element does NOT specialize to the
fair one (tails is fair-allowed but not loaded-allowed). -/
theorem no_link_loaded_to_fair :
    ¬ TheoryLink Coin (hypTheory (coinMass CoinHyp.loaded) coinOutcomes)
      (hypTheory (coinMass CoinHyp.fair) coinOutcomes) := by
  intro l
  have htails : Coin.tails ∈ (hypTheory (coinMass CoinHyp.fair) coinOutcomes).models :=
    List.mem_filter.mpr ⟨List.mem_cons_of_mem Coin.heads List.mem_cons_self,
      massAllows_coin_fair Coin.tails⟩
  have hmem := l.models_subset Coin.tails htails
  rcases List.mem_filter.mp hmem with ⟨_, hma⟩
  exact Bool.false_ne_true
    (Eq.subst (motive := fun b => b = true) massAllows_coin_loaded_tails hma)

-- Reference: ticket #165 toy — PROVED: the coin elimination learner's output
-- is limiting on the fair coin (`elimLearner_coin_fair`, #163); via the iff,
-- it identifies `[fair]` in the limit.
/-- **The coin elimination learner identifies the fair coin in the
limit**. -/
theorem coin_elim_isLimiting :
    IsLimitingOutput (elimLearner coinHypotheses coinMass CoinHyp.fair) coinMass
      CoinHyp.fair :=
  ⟨0, fun p _ _ => elimLearner_coin_fair p⟩

-- Reference: ticket #165 toy — via `identifiesInLimit_singleton_iff`, the
-- #31 predicate on the singleton family.
/-- The coin elimination learner identifies the singleton family `[fair]`
(#31's `IdentifiesInLimit`). -/
theorem coin_elim_identifies :
    IdentifiesInLimit (elimLearner coinHypotheses coinMass CoinHyp.fair) coinMass
      [CoinHyp.fair] :=
  (identifiesInLimit_singleton_iff _ _ CoinHyp.fair).mpr coin_elim_isLimiting

/-! ## The category instance (named hole) -/

-- Reference: ticket #165 — named hole.
-- TEMPORARY SORRY: the `Category` instance has not been assembled yet.
-- PEELING PLAN: `Hom t t' := TheoryLink carrier t t'`, `id := TheoryLink.id`,
-- `comp := TheoryLink.comp`, laws from `TheoryLink.comp_assoc`/`comp_id`
-- (the fields are `Prop`, so the laws close by proof irrelevance after
-- `cases`); then the prefix diagram `D p := hypTheory (mass (M p)) os` and
-- `identification_stable_links` upgrades to the colimit universal property
-- (in this poset-like category a filtered colimit is eventual constancy).
-- Next named lemmas: `theoryElementCategory`, `prefixDiagramFunctor`,
-- `colimit_eq_of_stable_links`.
/-- The **category of theory-elements** over a carrier (named hole). -/
def theoryElementCategory (carrier : Type) :
    CategoryTheory.Category.{0} (TheoryElement carrier) := by
  sorry

-- Reference: ticket #165, acceptance — `#eval` prints the potential models of
-- each coin hypothesis-theory: fair [heads, tails], biased [heads, tails],
-- loaded [heads].
#eval coinHypotheses.map fun h => (h, (hypTheory (coinMass h) coinOutcomes).models)

end BoringLab
