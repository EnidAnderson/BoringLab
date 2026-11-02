/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Epistemology.LocationMap
import BoringLab.Epistemology.Regime
import BoringLab.Epistemology.TheoryCategory

/-!
# MI.0.1: the Motivic Information theory-element, assembled

Ticket #67 (statement layer — the charter's goal 2 made precise): to BE a
theory of physics is to be a THEORY-ELEMENT, and the program now has every
component. The assembly, field by field, every field a built ticket or a
named hole:

* `te` — the theory-element core (Mp, M, Mpp, I, links; EPI.2.1 #30,
  category EPI.2.2 #62);
* `location` — the location map: fibers of observables, the prediction map
  on fiber data, periods-as-observables shadow (EPI.7.0/#7.1, #36/#37);
* `measurement` — the truncation regime: level-indexed claims carrying what
  they exclude, the transfer-term cocycle as the composition law of
  successive measurements (EPI.8.0–8.6, #40–#43, #54, #64);
* `vanishing` — the empirical claim class: vanishing statements on
  observable values (the D_N falsifier pattern), as a `Prop` predicate;
* `applications` + `worldConnection` — THE ONE WORLD-FACING FIELD: the
  intended applications as data, with the world-connection confined to
  exactly one typed `Prop` field (hypothesis-carrier, graded speculative,
  never assumed, never paid).

Anti-crank battery enacted, not weakened: every field quantifies over
carrier data with the theory as a variable; physics readings are citation
records; every analogy row states its explicit structure; the reflexive
rows (#65, MI.0.3) are recorded in the module docstring as satisfaction
statements about data, never world-claims.

## References
* [Sneed] J. D. Sneed, *The Logical Structure of Mathematical Physics*,
  Synthese Library vol. 114, 1979, ch. 2 (theory-elements).
* [BMS] W. Balzer, C. U. Moulines, J. D. Sneed, *An Architectonic for
  Science*, Synthese Library vol. 186, 1987, ch. 2.
* Program register: BoringLab ticket #67 (MI.0.1), depending on #30, #36,
  #37, #40–#43, #54, #62, #64 (all landed on feat/epi-gl-foundations-v3); the
  toy is the #28 coin family, the program's own.
-/

universe u

namespace BoringLab

/-! ## The assembled theory-element -/

-- Reference: ticket #67 — the assembly; every field a ticket reference or a
-- named hole; the world-connection confined to ONE typed field.
/-- The **Motivic Information theory-element**, assembled: the
theory-element core, the location map (observables + prediction map), the
measurement regime, the vanishing-statement claim class, and the ONE
world-facing field (intended applications + world-connection as a
hypothesis-carrier `Prop` field). -/
structure MotivicInformation (carrier : Type) where
  /-- The theory-element core (EPI.2.1 #30 / category EPI.2.2 #62). -/
  te : TheoryElement carrier
  /-- The location map: fibers of observables + prediction map (#36/#37). -/
  location : LocationMap carrier
  /-- The measurement regime (EPI.8.x #40–#43, #54, #64). -/
  measurement : Regime carrier
  /-- The empirical claim class: vanishing statements on observable values
  (the D_N falsifier pattern), as a `Prop` predicate on applications. -/
  vanishing : carrier → Prop
  /-- The intended applications (data). -/
  applications : List carrier
  /-- THE ONE WORLD-FACING FIELD: the world-connection — every intended
  application has a live observable in the located fiber
  (hypothesis-carrier, STYLE.D; graded speculative, never assumed). -/
  worldConnection : ∀ i ∈ applications,
    ∃ o : location.fiber ⟨te, 0, fun _ hi => absurd hi List.not_mem_nil⟩,
      location.predict ⟨te, 0, fun _ hi => absurd hi List.not_mem_nil⟩ i o ≠ 0

-- Reference: [Barendregt], ch. 2 (eta conversion), as in
-- `LocationMap.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for Motivic Information structures**. -/
theorem MotivicInformation.eta {carrier : Type} (MI : MotivicInformation carrier) :
    MotivicInformation.mk MI.te MI.location MI.measurement MI.vanishing
      MI.applications MI.worldConnection = MI := by
  cases MI with
  | mk te location measurement vanishing applications worldConnection => rfl

/-! ## Toy: the coin Motivic Information element -/

-- Reference: ticket #67, toy: the #28 coin family as carrier; vanishing =
-- the tails cell vanishes; the single application is the loaded coin.
/-- The coin Motivic Information element: the coin-hypothesis
theory-element (#36), the coin location map (#36/#37), the list-prefix
regime on the coin family (#64), vanishing = zero tails mass, one intended
application (the loaded coin). -/
def coinMI : MotivicInformation CoinHyp where
  te := coinHypTheory
  location := coinLocation
  measurement := listRegime coinHypotheses
  vanishing := fun h => tableMassOf coinPredict h Coin.tails = 0
  applications := [CoinHyp.loaded]
  worldConnection := by
    intro i hi
    rcases List.mem_cons.mp hi with h | hn
    · obtain ⟨o, ho⟩ := coin_live CoinHyp.loaded
      exact ⟨o, Eq.subst (motive := fun x => tableMassOf coinPredict x o ≠ 0) h.symm ho⟩
    · exact absurd hn List.not_mem_nil

-- Reference: ticket #67 — the reflexive rows (MI.0.3 #65), recorded as
-- satisfaction statements about data, never world-claims: (a) the
-- measurement regime's levels ARE the fair-experiment levels (#28);
-- (b) the process machine's normal phase accumulates them (#29);
-- (c) the falsifiers are the vanishing statements (#33/#67);
-- (d) the Kuhn anomaly ledger is the open named holes (#34).
-- Printed: the coin MI's application and its live observable.
#eval (coinMI.applications, isZeroQ (tableMassOf coinPredict CoinHyp.loaded Coin.tails))

end BoringLab
