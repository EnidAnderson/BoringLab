# LAB TREE GL.0 — rules of play as geometric theory: the computad-level build

Companion note to `docs/doctrine-localization.md` and `docs/port-typing.md`,
covering the GL line's first buildable layer. Issue:
`EnidAnderson/BoringLab#14` (LAB TREE GL.0). Per the human's direction, the
layer is built at the **computad/polygraph level** (Burroni/Mimram), not via
graph rewriting or chosen categorical machinery: the files are
`BoringLab/Doctrine/Morph.lean` and `BoringLab/Doctrine/Geometric.lean`, on
top of `BoringLab/Doctrine/{Computad,Doctrine,Localization}.lean`.

## The reading (PREP content of #14, unchanged)

Nori × Conway = Voevodsky as a hyperdoctrine whose base is scopes and whose
fibers are games: positions are the syntactic layer of a polygraph
presentation; RULES OF PLAY are geometric sequents (relations between
parallel paths — exactly Mimram Def. 3.5); a CONVENTION (normal / misère /
stalemate-as-draw) is a coverage on the terminal stratum; sieves are sets of
certified value-neutral simplifications; referee transformations are the
morphisms of the presentation; the classifying-topos reading is the universe
of plays (points = plays). Anchors: [Lawvere] *Adjointness in foundations*
(1969); [Caramello], *Theories, Sites, Toposes* (2017); the
topology-as-convention dictionary (Nisnevich = explicit-witness referee;
Zariski = generic play; étale = pure trades; cdh = reversible-move folding).

## What landed (the buildable core, computad level)

`BoringLab/Doctrine/Morph.lean` — morphisms of computads (polygraph
morphisms [Mimram §3], [Street §1]):

- `Computad.Morph` — port-monoid homomorphism + object map + generator map
  into hom-types (source/target preservation carried by the hom-type),
  port-word laws as `Prop` fields; `Computad.Morph.eta`.
- `Computad.Morph.mapPath` with `mapPath_nil`/`mapPath_cons`/`mapPath_comp`
  (path transport compatible with composition) and `mapPath_leftWord` /
  `mapPath_rightWord` (port words preserved), `Computad.Morph.id`,
  `Computad.Morph.comp`, `mapPath_id`, `mapPath_comp_morph`.

`BoringLab/Doctrine/Geometric.lean`:

- `GeometricSequent c` — a pair of parallel paths (the sequent layer);
  `Doctrine.toSequent` / `Doctrine.toSequent_move`: a doctrine's declared
  moves ARE the sequents of its presentation.
- `Sieve c X` — decidable membership predicate on paths into `X`, closed
  under precomposition; `Sieve.pullback` along a path (closure by
  `Quiver.Path.comp_assoc`); `Coverage c` — declared sieve data per object
  (the `Coverage`-not-`GrothendieckTopology` choice per #14 item (iv)).
- `Hyperdoctrine` — a Lawvere hyperdoctrine as data: base scope computad,
  fiber doctrines, root per fiber (single-sorted predicates = endo-paths at
  the root), substitution along each scope generator as a polygraph morphism
  `f* : fiber (tgt g) → fiber (src g)` preserving roots and declared moves,
  quantifier maps `∃_g`, `∀_g`, and the two adjunction laws `∃_g ⊣ f* ⊣ ∀_g`
  as explicit `Prop` fields (hypothesis-carriers, STYLE.D — never global
  axioms). `Hyperdoctrine.eta`.
- Falsifiable shadow (#14 item (iii), binding): `misereSequent` presents the
  Plambeck–Siegel misère quotient as sequent data, and
  `misereSequent_inverted` derives that every such sequent's antecedent is
  inverted in the doctrine-localization (via `misereQuotient_generator_inverted`).

## Sequent forms for one small doctrine (misère, #14 acceptance)

Over the misère computad (`misereQuotientComputad r`: objects = games,
generators = `r`-related pairs): the sequent of a generator `g : X → Y` is
`toPath g ⊢ toPath g` (`misereSequent`), declared by `misereQuotient_move_self`;
its localization inverts the antecedent (`misereSequent_inverted`), i.e. the
presentation presents the theory whose models are the legal plays, with the
`r`-related pairs identified up to isomorphism
(`misereQuotient_related_iso`). A failed presentation check would be a
first-class negative finding; none occurred at this layer.

## Honest scope

At pin `v4.35.0-rc3` mathlib has no (∞,1)-categories and the localization
construction is choice-tainted, so: no topos is consumed, the
classifying-topos reading stays a documented reading, and all quantifier
content enters as structure fields, not axioms. The six-functors-as-∃/∀
statement (#14 item (ii)) is represented here by the `existsMap`/`forallMap`
fields and adjunction laws of `Hyperdoctrine`, stated, not proved — the
Beck–Chevalley/quantifier laws are the named next holes (peeling plan: state
them as additional `Prop` fields on `Hyperdoctrine`, then prove them for the
toy misère instance by enumeration on bounded games).

## Follow-on instances (same branch)

* `BoringLab/Doctrine/Nim.lean` — normal-play Nim as a geometric theory
  (ticket #14 item (iii)): `nimComputad` (positions `ℕ`, legal removals as
  generators, addition-only typing), `nimDoctrine` (commutation of two
  removals as the declared sequent), `nim_commute_witness` (at `5, k=2,
  j=1`), `nim_commute_inverted`, `nimCommuteSequent`.
* `BoringLab/Doctrine/NimHyperdoctrine.lean` — the first fully proved
  `Hyperdoctrine` instance (`nimHyperdoctrine`): one-scope base `nimScope`,
  fiber = the Nim doctrine, identity substitution, `∃ = ∀ = id` on root
  endo-paths; adjunctions proved by `mapPath_id`;
  `nimHyperdoctrine_commute_transport`.
* `BoringLab/Lisp/` + `docs/lisp-macros.md` — the LAB LISP line (ticket #68):
  On Lisp macros as computadic rewriting (functions as 1-cells, macros as
  declared moves), the Common Lisp function/macro distinction as data.
* `BoringLab/Epistemology/Learning.lean`, `BoringLab/Epistemology/Kuhn.lean` —
  EPI.3.1 (#31) and EPI.5.1 (#34).

## Companion epistemology build (same session, EPI line)

`BoringLab/Epistemology/Process.lean` (ticket #29, EPI.1.2, on the #28
fair-experiment carrier): `SciPhase` + `SciPhase.next` (the cycle
HYPOTHESIS → PREDICTION → EXPERIMENT → COMPARISON → UPDATE/FALSIFIED, with
falsified absorbing), the Bayesian count-table ledger (`bayesUpdate`,
`ledgerWeight`), the proved monotonicity law `falsified_never_resurrects`,
`SciState`/`SciState.round`/`runOn` (replication = re-running), and the toy
coin run printed by `#eval` (final phase `falsified`, loaded weight `0`).
