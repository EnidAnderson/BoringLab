/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Morph
import BoringLab.Doctrine.Localization

/-!
# Geometric logic over computads: sequents, sieves, and the scope hyperdoctrine

The buildable core of the GL reading (`EnidAnderson/BoringLab#14`, LAB TREE
GL.0: "rules of play as geometric theory — the hyperdoctrine whose base is
scopes and whose fibers are games"), kept at the **computad/polygraph level**
per the human's direction — no graph rewriting, no chosen categorical
machinery:

* a **geometric sequent** over a computad is a pair of parallel paths
  (`GeometricSequent`) — the 2-polygraph shape of a relation between parallel
  cells [Mimram, Def. 3.5]; a `Doctrine`'s declared moves are exactly the
  sequent layer of its presentation (`Doctrine.toSequent`);
* a **sieve** on an object is a list of paths into it, closed under
  precomposition (`Sieve`), with pullback along any path as data
  (`Sieve.pullback`); a **coverage** is declared sieve data per object
  (`Coverage`) — the GL.0 reading: a CONVENTION (normal / misère /
  stalemate-as-draw) is a coverage on the terminal stratum;
* a **Lawvere hyperdoctrine as data** (`Hyperdoctrine`): the base is a scope
  computad, each scope carries a doctrine as its fiber of predicates
  (single-sorted per fiber: predicates are endo-paths at a declared root),
  each scope generator carries a substitution polygraph-morphism
  `f* : fiber (tgt g) → fiber (src g)` preserving declared moves, and the
  quantifier maps `∃_g`, `∀_g` with the two adjunction laws `∃_g ⊣ f* ⊣ ∀_g`
  as explicit `Prop` fields — hypothesis-carriers (STYLE.D), never global
  axioms.

The falsifiable shadow (ticket #14, item (iii), binding): the
Plambeck–Siegel misère quotient is presented by sequent data whose
localization inverts exactly the generator paths of `r`-related pairs
(`misereSequent_inverted`).

Scope honesty: at the pin there are no (∞,1)-categories in mathlib and no
topos machinery is consumed — the classifying-topos reading of #14 remains a
documented reading (see `docs/geometric-logic.md`); what is built here is the
computad-level substrate it stands on.

## References
* [Lawvere] F. W. Lawvere, *Adjointness in foundations*, Dialectica 23 (1969),
  135–145 — hyperdoctrines: fibers with finite meets and quantifier
  adjoints `∃ ⊣ f* ⊣ ∀` to substitution.
* [Mimram] S. Mimram, *Polygraphs: from rewriting to higher categories*,
  arXiv:2312.00429, Logical Methods in Computer Science 21(3) (2025),
  7:1–7:47 — Definition 3.5 (2-polygraph: generators plus relations between
  parallel paths = sequents) and §3 (morphisms).
* [Mac Lane–Moerdijk] S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and
  Logic*, Springer, 1992, ch. III, §2 (sieves and coverages; the
  `Coverage`-not-`GrothendieckTopology` choice follows the PHYS.0 precedent,
  ticket #14 item (iv)).
* [Plambeck–Siegel] T. E. Plambeck, A. N. Siegel, *Misère quotients for
  impartial games*, arXiv:math/0609825 (2006), §2.
* [Caramello] O. Caramello, *Theories, Sites, Toposes*, Oxford UP, 2017 —
  the classifying-topos reading (the nearest modern anchor for #14).
-/

universe u

namespace BoringLab

open CategoryTheory

/-! ## Geometric sequents: the sequent layer of a polygraph presentation -/

-- Reference: [Mimram], LMCS 21(3) (2025), Definition 3.5 (a relation between
-- parallel paths); GL.0 reading (ticket #14): a rule of play is a geometric
-- sequent `antecedent ⊢ succedent` over the position grammar.
-- REVIEW(citation): pin the exact definition number in review.
/-- A **geometric sequent** over a computad `c`: two parallel paths from
`src` to `tgt` — the antecedent and the succedent. -/
structure GeometricSequent (c : Computad.{u}) where
  /-- The source object (the context's domain). -/
  src : c.obj
  /-- The target object (the context's codomain). -/
  tgt : c.obj
  /-- The antecedent path. -/
  antecedent : c.Path src tgt
  /-- The succedent path. -/
  succedent : c.Path src tgt

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Computad.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for geometric sequents**. -/
theorem GeometricSequent.eta {c : Computad.{u}} (s : GeometricSequent c) :
    GeometricSequent.mk s.src s.tgt s.antecedent s.succedent = s := by
  cases s with
  | mk src tgt antecedent succedent => rfl

-- Reference: [Mimram], Definition 3.5; ticket #14 item (i): the declared
-- moves of a doctrine ARE the sequent layer of its geometric presentation.
/-- The sequent carried by a declared move of a doctrine. -/
def Doctrine.toSequent (d : Doctrine.{u}) {X Y : d.computad.obj}
    (p q : d.computad.Path X Y) : GeometricSequent d.computad :=
  ⟨X, Y, p, q⟩

-- Reference: [Mimram], Definition 3.5; ticket #14 item (i): the move
-- relation certifies the sequent's declaration.
/-- The declared-move certificate of a sequent obtained from a move. -/
theorem Doctrine.toSequent_move (d : Doctrine.{u}) {X Y : d.computad.obj}
    (p q : d.computad.Path X Y) (h : d.move p q) :
    d.move (Doctrine.toSequent d p q).antecedent (Doctrine.toSequent d p q).succedent := h

/-! ## Sieves and coverages: the convention layer -/

-- Reference: [Mac Lane–Moerdijk], ch. III, §2 (a sieve on `X` is a set of
-- arrows into `X` closed under precomposition); at the computad level the
-- arrows are paths, and membership is a decidable predicate (explicit data,
-- STYLE §2.3).
-- REVIEW(citation): pin the exact page in review.
/-- A **sieve** on an object `X` of a computad, as data: a decidable predicate
on pairs of a domain and a path into `X`, closed under precomposition (the
`closed` field). -/
structure Sieve (c : Computad.{u}) (X : c.obj) where
  /-- Membership in the sieve: pairs of a domain and a path into `X`. -/
  arrows : Sigma (fun Y => c.Path Y X) → Bool
  /-- Closure under precomposition. -/
  closed : ∀ (a : Sigma fun Y => c.Path Y X), arrows a = true →
    ∀ (Z : c.obj) (q : c.Path Z a.1), arrows ⟨Z, q.comp a.2⟩ = true

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Computad.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for sieves**. -/
theorem Sieve.eta {c : Computad.{u}} {X : c.obj} (s : Sieve c X) :
    Sieve.mk s.arrows s.closed = s := by
  cases s with
  | mk arrows closed => rfl

-- Reference: [Mac Lane–Moerdijk], ch. III, §2 (the pullback `g*(S)` of a
-- sieve `S` on `X` along `g : Y → X` is `{ h : Z → Y | h.comp g ∈ S }`, and
-- it is a sieve); closure by `Quiver.Path.comp_assoc`.
-- REVIEW(citation): pin the exact page in review.
/-- The **pullback of a sieve** along a path `g : Y ⟶ X`: the sieve on `Y`
whose arrows are the paths `h` with `h.comp g` in the original sieve. -/
def Sieve.pullback {c : Computad.{u}} {X Y : c.obj} (s : Sieve c X) (g : c.Path Y X) :
    Sieve c Y where
  arrows := fun h => s.arrows ⟨h.1, h.2.comp g⟩
  closed := by
    intro h hh Z q
    have h1 : s.arrows ⟨Z, q.comp (h.2.comp g)⟩ = true :=
      s.closed ⟨h.1, h.2.comp g⟩ hh Z q
    exact Eq.subst (motive := fun p => s.arrows ⟨Z, p⟩ = true)
      (Quiver.Path.comp_assoc q h.2 g).symm h1

-- Reference: [Mac Lane–Moerdijk], ch. III, §2 (a Grothendieck topology as a
-- coverage); ticket #14 item (iv): `Coverage`, not `GrothendieckTopology`,
-- matching the rawness of the axiom (the PHYS.0 precedent).
-- REVIEW(citation): pin the exact page in review.
/-- A **coverage** on a computad, as declared data: for each object a family
of covering sieves, indexed by data. The GL.0 reading: a play CONVENTION is
a coverage on the terminal stratum. -/
def Coverage (c : Computad.{u}) : Type u := ∀ X : c.obj, List (Sieve c X)

/-! ## The scope hyperdoctrine (Lawvere-style categorical logic as data) -/

-- Reference: [Lawvere], *Adjointness in foundations*, Dialectica 23 (1969),
-- 135–145 (a hyperdoctrine: fibers of predicates with substitution `f*`
-- and quantifier adjoints `∃_f ⊣ f* ⊣ ∀_f`); ticket #14: base = scopes,
-- fibers = games/doctrines. Predicates are taken single-sorted per fiber:
-- a predicate on scope `X` is an endo-path at the declared `root X`, so the
-- adjunction laws typecheck as moves between parallel endo-paths, with the
-- root transport made explicit by `Eq.subst`.
-- REVIEW(citation): pin the exact page of [Lawvere] in review.
/-- A **Lawvere hyperdoctrine as data** over a scope computad. All
quantifier content enters as explicit structure fields (STYLE.D
 hypothesis-carriers), never as global axioms. -/
structure Hyperdoctrine where
  /-- The base computad of scopes (contexts). -/
  scope : Computad.{u}
  /-- The fiber doctrine over each scope (its predicates and moves). -/
  fiber : scope.obj → Doctrine.{u}
  /-- The root object of each fiber (the single sort of its predicates). -/
  root : (X : scope.obj) → (fiber X).computad.obj
  /-- Substitution (pullback) along a scope generator `g : src g → tgt g`:
  a polygraph morphism `fiber (tgt g) → fiber (src g)`. -/
  subst : (g : scope.gen) →
    Computad.Morph (fiber (scope.tgt g)).computad (fiber (scope.src g)).computad
  /-- Substitution preserves the root. -/
  subst_root : ∀ (g : scope.gen),
    (subst g).objMap (root (scope.tgt g)) = root (scope.src g)
  /-- Substitution preserves declared moves (the finite-limit + ∃ fragment
  is stable under pullback, as data). -/
  subst_move : ∀ (g : scope.gen) {X Y : (fiber (scope.tgt g)).computad.obj}
    (p q : (fiber (scope.tgt g)).computad.Path X Y),
    (fiber (scope.tgt g)).move p q →
    (fiber (scope.src g)).move ((subst g).mapPath p) ((subst g).mapPath q)
  /-- The existential-quantifier map along a scope generator:
  `∃_g : predicates on src g → predicates on tgt g`. -/
  existsMap : (g : scope.gen) →
    (fiber (scope.src g)).computad.Path (root (scope.src g)) (root (scope.src g)) →
    (fiber (scope.tgt g)).computad.Path (root (scope.tgt g)) (root (scope.tgt g))
  /-- The universal-quantifier map along a scope generator:
  `∀_g : predicates on src g → predicates on tgt g`. -/
  forallMap : (g : scope.gen) →
    (fiber (scope.src g)).computad.Path (root (scope.src g)) (root (scope.src g)) →
    (fiber (scope.tgt g)).computad.Path (root (scope.tgt g)) (root (scope.tgt g))
  /-- The adjunction `∃_g ⊣ f*` as a hypothesis-carrier field:
  `φ ⊢ f* ψ` in the source fiber iff `∃_g φ ⊢ ψ` in the target fiber. The
  pulled-back predicate is transported along `subst_root g` by `cast` (the
  `Sort`-motive transport; `Eq.subst` at the pin is `Prop`-motive only). -/
  exists_adj : ∀ (g : scope.gen)
    (φ : (fiber (scope.src g)).computad.Path (root (scope.src g)) (root (scope.src g)))
    (ψ : (fiber (scope.tgt g)).computad.Path (root (scope.tgt g)) (root (scope.tgt g))),
    (fiber (scope.src g)).move φ
      (cast (congrArg (fun W => (fiber (scope.src g)).computad.Path W W) (subst_root g))
        ((subst g).mapPath ψ)) ↔
      (fiber (scope.tgt g)).move (existsMap g φ) ψ
  /-- The adjunction `f* ⊣ ∀_g` as a hypothesis-carrier field:
  `f* ψ ⊢ φ` in the source fiber iff `ψ ⊢ ∀_g φ` in the target fiber. -/
  forall_adj : ∀ (g : scope.gen)
    (φ : (fiber (scope.src g)).computad.Path (root (scope.src g)) (root (scope.src g)))
    (ψ : (fiber (scope.tgt g)).computad.Path (root (scope.tgt g)) (root (scope.tgt g))),
    (fiber (scope.src g)).move
      (cast (congrArg (fun W => (fiber (scope.src g)).computad.Path W W) (subst_root g))
        ((subst g).mapPath ψ)) φ ↔
      (fiber (scope.tgt g)).move ψ (forallMap g φ)

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Computad.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for hyperdoctrines**. -/
theorem Hyperdoctrine.eta (H : Hyperdoctrine.{u}) :
    Hyperdoctrine.mk H.scope H.fiber H.root H.subst H.subst_root H.subst_move
      H.existsMap H.forallMap H.exists_adj H.forall_adj = H := by
  cases H with
  | mk scope fiber root subst subst_root subst_move existsMap forallMap exists_adj
      forall_adj => rfl

/-! ## Falsifiable shadow: the misère quotient as a sequent presentation -/

-- Reference: ticket #14, item (iii) (the falsifiable shadow, binding);
-- [Plambeck–Siegel], arXiv:math/0609825, §2; [Mimram], Definition 3.5.
-- REVIEW(citation): pin the exact section of [Plambeck–Siegel] in review.
/-- The sequent of a misère-quotient generator: the self-move of a
single-generator path, read as a geometric sequent of the misère computad
(the checkable instance of "a doctrine presents the theory whose models are
the legal plays"). -/
def misereSequent (r : Game.{u} → Game.{u} → Prop) {X Y : Game.{u}}
    (g : (misereQuotientComputad r).Hom X Y) :
    GeometricSequent (misereQuotientComputad r) :=
  Doctrine.toSequent (misereQuotient r)
    ((misereQuotientComputad r).toPath g) ((misereQuotientComputad r).toPath g)

-- Reference: ticket #14, item (iii); [Plambeck–Siegel], §2;
-- [Gabriel–Zisman], Chapter I (inversion in the localization), via
-- `misereQuotient_generator_inverted` (BoringLab.Doctrine.Localization).
-- REVIEW(citation): as on `misereSequent`.
/-- **The falsifiable shadow, derived**: the antecedent of every misère
sequent is inverted in the doctrine-localization — the generator paths of
`r`-related pairs become isomorphisms. -/
theorem misereSequent_inverted (r : Game.{u} → Game.{u} → Prop) {X Y : Game.{u}}
    (g : (misereQuotientComputad r).Hom X Y) :
    IsIso ((misereQuotient r).moveClass.Q.map (misereSequent r g).antecedent) :=
  misereQuotient_generator_inverted r g

end BoringLab
