/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import Mathlib.Init

/-!
# Theory-elements as data: the structuralist reconstruction

The structuralist program's core concept, made constructive (BoringLab
ticket #30, EPI.2.1): a theory is a set-theoretic predicate, and a
*theory-element* is the quadruple `(Mp, M, Mpp, I)` of Sneed — potential
models, actual models, partial models, and intended applications — here
carried as an explicit typed record over a bounded family of potential
models, with the empirical claim as a `Prop`-valued structure field (the
hypothesis-carrier pattern of STYLE.D / BoringMath #119: never an `axiom`).

The non-vacuity witness (D.5) is the toy coin-statistics instance at the end
of the file, proved and printed by `#eval`.

## References
* [Sneed] J. D. Sneed, *The Logical Structure of Mathematical Physics*,
  Synthese Library vol. 114, D. Reidel, 1979, ch. 2 (theory-elements:
  `Mp`, `M`, `Mpp`, `I` and links).
* [Stegmüller] W. Stegmüller, *The Structuralist View of Theories*,
  Springer, 1976, ch. 1.
* [BMS] W. Balzer, C. U. Moulines, J. D. Sneed, *An Architectonic for
  Science: The Structuralist Program*, Synthese Library vol. 186, D. Reidel,
  1987, ch. 2.
* [Suppes] P. Suppes, *Representation and Invariance of Scientific
  Structures*, CSLI Publications, 2002, sec. 2.2 ("to axiomatize a theory is
  to define a set-theoretical predicate").
-/

universe u

namespace BoringLab

-- Reference: [Sneed], ch. 2 (a theory-element is the quadruple
-- (Mp, M, Mpp, I) with links between elements); [Suppes], sec. 2.2
-- (set-theoretical predicate); [BMS], ch. 2.
-- REVIEW(citation): pin down exact page numbers in review.
/-- A **theory-element** in the sense of Sneed, as explicit computable data
over a bounded family of potential models `carrier`: the potential models
`models` (a finite list, the `Mp`), the actual models as a decidable
predicate `isActual` (the `M ⊆ Mp`), the partial-model projection
`isPartial` (the `Mpp` — which components are observable), the intended
applications `applications` (the `I`), and the links as an explicit table.
The empirical claim "every intended application is an actual model" is
carried as a `Prop` field, per the STYLE.D hypothesis-carrier law. -/
structure TheoryElement (carrier : Type u) where
  /-- The potential models `Mp`, as a bounded family. -/
  models : List carrier
  /-- The actual models `M ⊆ Mp`, as a decidable predicate. -/
  isActual : carrier → Bool
  /-- The partial models `Mpp`: which components are observable. -/
  isPartial : carrier → Bool
  /-- The intended applications `I`. -/
  applications : List carrier
  /-- Links between elements of `Mp`, as an explicit table. -/
  links : List (carrier × carrier)
  /-- The empirical claim: every intended application is an actual model.
  Hypothesis-carrier field (STYLE.D D.3): the statement mentions the fields
  `applications` and `isActual`. -/
  empiricalClaim : ∀ i ∈ applications, isActual i = true

-- Reference: [Sneed], ch. 2 (theoretical vs non-theoretical components are
-- distinguished only via the theory itself); [BMS], ch. 2.
-- REVIEW(citation): the full definability-theoretic account of
-- theoretical terms is deferred to a later ticket (honest absence, named).
/-- The T-theoreticity ledger tag: marks which components of a potential
model are theoretical-in-Sneed's-sense (measurable only through the theory
itself). Data-level tag; the definability account is deferred. -/
def TheoryElement.theoretical {carrier : Type u} (t : TheoryElement carrier) :
    carrier → Bool := t.isPartial

/-! ## Toy instance: coin statistics (the D.5 non-vacuity witness) -/

-- Reference: [Suppes], sec. 2.2 (models of data as set-theoretical
-- structures); the toy is the program's own.
-- REVIEW(citation): program's own toy, no external source.
/-- The carrier of the toy theory: a coin experiment is a finite list of
toss outcomes. -/
def CoinData := List Bool

-- Reference: program's own toy (Suppes-style hierarchy: models of data).
-- REVIEW(citation): program's own.
/-- The bounded family `Mp`: all outcome lists of length at most two. -/
def coinModels : List CoinData :=
  [[], [true], [false], [true, true], [true, false], [false, true], [false, false]]

-- Reference: program's own toy.
-- REVIEW(citation): program's own.
/-- `M`: the actual models are exactly the nonempty data lists. -/
def coinActual : CoinData → Bool :=
  fun d => match d with
    | [] => false
    | _ :: _ => true

-- Reference: program's own toy.
-- REVIEW(citation): program's own.
/-- The observed application: one experiment, heads then tails. -/
def coinObserved : CoinData := [true, false]

-- Reference: program's own toy.
-- REVIEW(citation): program's own.
/-- Primitive definitional lemma: the observed experiment is an actual model
(computation step; `rfl` is permitted only in such primitive lemmas). -/
theorem coinActual_observed : coinActual coinObserved = true := rfl

-- Reference: [Sneed], ch. 2 (the empirical claim `I ⊆ M`); the program's
-- own toy instance proves it by enumeration of the singleton list.
-- REVIEW(citation): program's own.
/-- The toy instance's empirical claim: its single intended application is
an actual model. -/
theorem coinTheory_empirical : ∀ i ∈ ([coinObserved] : List CoinData),
    coinActual i = true := by
  intro i hi
  cases hi with
  | head _ => exact coinActual_observed
  | tail _ h => cases h

-- Reference: program's own toy.
-- REVIEW(citation): program's own.
/-- The toy theory-element: coin statistics over `CoinData`. -/
def coinTheory : TheoryElement CoinData :=
  { models := coinModels
    isActual := coinActual
    isPartial := fun _ => true
    applications := [coinObserved]
    links := [([true], coinObserved), (coinObserved, [false])]
    empiricalClaim := coinTheory_empirical }

end BoringLab
