# The mature Games library: architecture roadmap (L-line charter companion)

Companion to the L-line tickets in `EnidAnderson/BoringLab` and the lab-tree
root tracker `EnidAnderson/BoringLab#2` (LAB TREE X.0). This note answers:
which games tickets already exist, what a fully mature `BoringLab/Games/`
library needs, and how its modules are designed to plug, when the time comes,
into the computad rewriting layers (`Doctrine/`, A2.0 #3 / A2.1 #8 / E.0 #9 /
GL.0 #14) and the Voevodsky/Nori motive layers of `BoringMath`
(`AlgebraicGeometry/Motives`, `Correspondence`, T.1 #23, K.0 #31, C.4 #117,
WISH W1/W2/W6).

North star (notes-only, per #2): ONE sheaf of stable categories over the
moduli of doctrines; value theory of games and cohomology of motives are the
same functor `Hom(1, -)` in different fibers (Nori x Conway = Voevodsky, the
GL.0 reading of #14). In Lean this enters only through 1-categorical shadows,
honestly graded — never as an axiom.

## 1. What exists today

Modules in `BoringLab/Games/`:

- `Games/Basic.lean` — the partizan `Game` structure (Conway `G = {G^L |
  G^R}` as indexed option families), `Game.eta`, `zero`, `one`, `zero_ne_one`.
- `Games/Misere.lean` — ticket #20 (L.1.1): the depth-truncated carrier
  `TGame n`, `TGame.toGame`, computable `misereOutcome`, worked examples and
  the truncation-antimonotonicity shadow on the chain family.
- `Games/Referee.lean` — ticket #21 (L.1.2): the S3 action on `TGame` by
  option reindexing, enumerated equivariance shadows, the `mixed3` node.
- `Games/Trace.lean` — ticket #10 (LAB TR.0): the free-standing
  `WinLoseTree` substrate, minimax `valueAux`/`value`, the play filtration,
  the capital process, one-step super/submartingale inequalities, birthday
  0/1/2 strata.

Games plug into the doctrine layer in `BoringLab/Doctrine/`:

- `Doctrine/GameDoctrine.lean` — #14 (GL.0) items (i)/(iii)/(iv):
  `gameComputad` (objects `Game`, generators = moves, ports = mover tag),
  `gameDoctrine`, `gameSequent`, `gameCoverage`.
- `Doctrine/Nim.lean`, `Doctrine/NimHyperdoctrine.lean` — #14 item (iii):
  Nim as a geometric theory; the first proved `Hyperdoctrine` instance.

Open tickets touching games:

- L-line (lab games, folder `Games/`): #20 (L.1.1), #21 (L.1.2),
  #52 (L.2.1 thermographs on truncated games), #56 (L.3.1 misere quotient as
  computable monoid data), #63 (L.4.1 truncated-game category, value quotient
  as computable shadow functor).
- Lab tree: #3 (A2.0 computads/doctrine-localization), #4 (PHI.0
  calibration), #5 (V.0 value 2-groupoid), #7 (PHI.1 misere shell as
  doctrine-localization), #8 (A2.1 Focus/Port), #9 (E.0 E-test),
  #10 (TR.0 trace), #11 (RAD.0 play-line complex / Lemma C), #12 (U.0 K0 =
  Conway's group U), #13 (C3.0 consensus heart), #14 (GL.0), #15 (PD.1
  derivative), #16 (GAL.0 deck semantics).
- BoringMath: #12 / W4 (cg wiring ruling: pin-back `vihdzp/combinatorial-games`
  @ d949bd1; G1 gate), #37 (A.1 OutcomeClass on cg, wiring-gated), A.2
  (cooling/thermograph on Short, wiring-gated), #23 (T.1 Verdier), #31 (K.0
  Grothendieck group), C-line (C.0–C.4, DM^eff #117), WISH W2 (the
  Conway-motives problem), CFSG.GAMES.0–3.
- Epistemology bridge: the truncation layer already carries a depth-truncated
  game-tree toy instance (#41, EPI.8.1, `Epistemology/Truncation.lean` toy
  (iii)); #64 (EPI.8.6, `Epistemology/Regime.lean`) gives regimes with
  transfer terms and the cocycle law — the shape a games-as-regimes module
  should take.

Gap statement: `Games/` has the substrate (`Game`, `TGame`), one convention
(misere outcomes), one symmetry shadow (S3), and the trace semantics — but no
normal-play order, no arithmetic, no numbers, no Sprague–Grundy, no canonical
forms, no loopy games, no strategies-as-data, no ruleset zoo, and no bridge
modules toward the computad and motive layers. That is what the new tickets
below fill.

## 2. The two-carrier design principle (binding for the whole line)

Every games module works with TWO carriers:

1. **`Game`** (`Games/Basic.lean`) — the general partizan game, universe-
   polymorphic, Prop-level theory. General theorems (order laws, Sprague–
   Grundy, simplicity, canonical forms) are stated here with named holes
   (sorries with peeling plans, STYLE §7). Recursion on `Game` requires a
   well-foundedness hypothesis (the type is not inductive); the line
   introduces `Game.WellFounded` / birthday and the induction principle
   (L.5.1).
2. **`TGame n`** (`Games/Misere.lean`) — the depth-truncated carrier,
   `Type 0`, fully computable. Every decision (outcome, order, value, SG,
   canonical form, thermograph) is a computable `Bool`/number here, and small
   strata are PROVEN outright as named `rfl`/enumeration theorems — never
   unit tests (lab epistemics, #2).

The pair is exactly a truncation regime in the sense of EPI.8.0–8.6
(`Epistemology/Truncation.lean`, `Epistemology/Regime.lean`): levels = depth,
data = the truncated tree, remainder = the un-truncated subtree, and the
tracking laws (refines one level, conserves content) are the truncation
shadows already proved on the chain family in `Misere.lean`. L.14.1 makes
this precise: `TGame` as a `Regime` with the value map as `remContent` and
play-composition transfer terms satisfying the cocycle law.

Rule: a general statement is never "proven" by citing a truncated instance;
truncated theorems are honest shadows, named `_bounded` where the general
statement is a named hole (the D.2 discipline of #52).

## 3. Layer map (modules under `BoringLab/Games/`)

| Layer | Modules | Content | Tickets |
|---|---|---|---|
| 0 substrate | `Basic.lean` (exists) | `Game`, eta, 0, 1 | — charter #83 (L.0) |
| 0 truncation carrier | `Misere.lean` (exists), `Truncated.lean` (new) | `TGame`, `toGame`, regime structure | #20; #102 (L.14.1) |
| 1 trace | `Trace.lean` (exists) | `WinLoseTree`, value process, filtration | #10 (TR.0) |
| 2 normal-play outcomes & order | `Order.lean` (new) | outcome classes, `<=`, `<`, `=` on `Game` and `TGame` | #82 (L.5.2) |
| 2 arithmetic | `Arithmetic.lean` (new) | negation, disjunctive sum, monoid laws, order compatibility | #84 (L.5.3), #81 (L.5.4) |
| 3 numbers & surreals | `Numbers.lean`, `Surreal.lean` (new) | number predicate, dyadics, simplicity; surreal bridge | #86 (L.6.1), #87 (L.6.2) |
| 4 impartial & SG | `Impartial.lean`, `Nimbers.lean` (new) | mex, nimbers, Sprague–Grundy | #91 (L.7.1), #89 (L.7.2) |
| 5 canonical forms | `Canonical.lean` (new) | dominated/reversible options, canonical form | #92 (L.8.1) |
| 6 thermography | `Thermo.lean` (new) | stops, cooling, thermograph, temperature | #52 (L.2.1); #96 (L.12.1) |
| 7 misere | `MisereQuotient.lean` (new) | congruence, quotient monoid, genus | #56 (L.3.1), #7 (PHI.1); #99 (L.13.1) |
| 8 category & value | `Category.lean` (new) | truncated-game category, monoidal sum, value shadow functor | #63 (L.4.1); #12 (U.0), #5 (V.0) |
| 9 ruleset zoo | `Ruleset.lean`, `Zoo/*.lean` (new) | generic finite ruleset engine + dozens of standard games | #88 (L.9.1), #90 (L.9.2), #93 (L.9.3), #98 (L.9.4) |
| 10 loopy | `Loopy.lean` (new) | loopy games on finite graphs, draws | #95 (L.10.1), #97 (L.10.2) |
| 11 strategies | `Strategy.lean` (new) | strategies as data, stealing, pairing, equality-strategies | #94 (L.11.1) |
| 12 computad pre-wiring | `Computad.lean` (new) | uniform `toComputad`/`toDoctrine` for every module | #100 (L.15.1; with #3/#8/#14) |
| 13 motive bridge | `MotiveBridge.lean` (new) | statement-layer dictionary to motives | #101 (L.16.1; with #11/#12/#13, WISH W2/W6) |

## 4. The standard games zoo (several dozen libraries, enumerated)

Each zoo entry is a module `Games/Zoo/<Name>.lean` presenting the ruleset as
data (positions, legal moves, turn) over the generic `Ruleset` engine of
L.9.1, with computed small-case theorems (outcome/SG/value on small boards
proven outright) and a `toComputad`/`toDoctrine` view (L.15.1). Grouped by
family; anchors: [BCG] Winning Ways vols. 1–4; [Conway] ONAG; [Siegel],
*Combinatorial Game Theory*; [Gatm]? no — [Albert–Nowakowski–Wolfe], *Lessons
in Play*. REVIEW(citation) per module until pinned.

- **Nim and subtraction games**: Nim (multi-pile), subtraction games
  S(1,2), S(1,2,3), S(1,3,4)...; `Doctrine/Nim.lean` already presents
  one-pile Nim as a computad — the zoo module is the ruleset twin.
- **Octal games** (the dozen-plus classic codes): 0.07 (Treblecross),
  0.137 (Dawson's Kayles), 0.33, 0.007, 0.17, 0.27, 0.34, 0.36, 0.45,
  0.52–0.77 family, 0.06, 0.106, 0.333... each with SG sequences computed on
  bounded heap sizes as theorems.
- **Welter's game** (coins on a strip, the Sprague–Grundy irregularity
  witness), **Antonim**, **Grundy's game** (splitting heaps).
- **Domineering** (polyomino placement, partizan; small-board values:
  2x2, 2x3, 3x3 proven).
- **Hackenbush**: Blue-Red (finite stalks, values = dyadic rationals),
  Blue-Red-Green (nimbers), with the colon and fusion principles as theorems
  on small graphs.
- **Toads-and-Frogs**, **Clobber**, **Konane** (Hawaiian checkers),
  **Amazons** (small boards), **Checkers/draughts** endgames as finite
  rulesets.
- **Go**: small boards (1xN, 2x2, 2x3) with **ko** and **seki** — the flagship
  LOOPY instance (see §5); positions as stone configurations, suicide rule
  variants recorded as data choices.
- **Dawson's Chess**, **Fox and Geese**, **peg solitaire** (one-player =
  impartial with a single outcome), **Sprouts** (finite small cases).
- **Partizan classics**: **Snort**, **Col**, **Snort on graphs**, **Cutcake**,
  **Chomp** (strategy stealing — the L.11.1 flagship), **NimG**, **Poisoned
  chocolate**.
- **Sum-type compounds**: disjunctive sums of any zoo entries via the
  arithmetic layer (L.5.3), with outcome computation on small sums.

Count: 30+ named rulesets, each a module. None has a unified proof-library
referent (cg has pieces; no prover has the zoo as computable data with proven
small cases) — the zoo as such is one of the no-referent libraries (§6).

## 5. Loopy game theory

ONAG's loopy chapter and the Fraenkel–Scheinerman–Ullman loopy literature
anchor the theory; the lab's honest door is finite directed position graphs
where play may cycle: outcomes are FOUR-valued (L/R/N/D — Left wins, Right
wins, Next player wins, Draw), computed by the attractor/greatest-fixpoint
recursion (a genuinely different recursion from the well-founded one — this
is where `Game.WellFounded` is dropped and the finite-graph fixpoint enters).
L.10.1 builds `LoopyGame` (finite graph + turn + terminal marking), the
4-valued outcome, and proves the fixpoint equations on small graphs; L.10.2
states the loopy value reading (stalemate-as-draw; the loopy extension of
the value group — un-parking U.0 #12 item (iv)) and connects draws to the
consensus heart (C3.0 #13: draws = non-split extensions, mutual stalemate).
Go with ko (#L.9.4) is the flagship instance.

## 6. Libraries with no literature referent (the program's own)

These are formalized as structure + named anchor + computable/falsifiable
shadow (the no-woo gate, #2), tagged [S]:

1. **The two-carrier truncation discipline for games** — `Game`/`TGame` as a
   regime (EPI.8.6 shape; L.14.1). Anchor: the truncation layer #41/#64.
2. **The generic finite ruleset engine** (L.9.1) — one `Ruleset` structure,
   one generic outcome/SG/value recursion, ONE correctness theorem
   (recursion = minimax on finite rulesets) proven generically, then every
   zoo entry is data. No proof library has this shape.
3. **Strategies as explicit data** (L.11.1) — winning strategies, strategy
   stealing, pairing strategies, and the equality-strategy (P-strategy on
   G - H) classes that V.0 (#5) needs as 1-cells.
4. **The value shadow functor** (L.4.1 #63) — value map as a computable
   monoidal functor on the truncated category; the calibration instance for
   the sigma-checklist.
5. **The computad view of every games module** (L.15.1) — objects =
   positions, generators = moves, ports = mover tag; doctrine = value-neutral
   sequents; makes A2.0/A2.1/E.0/GL.0 apply uniformly to all games.
6. **The play-line complex finite shadows** (RAD.0 #11) and the **trace
   semantics** (TR.0 #10) — already ticketed.
7. **Transfer-term cocycle for plays** (L.14.1) — composed plays' transfer
   terms add (the `RegimeMap.comp_transferTerm` law of Regime.lean applied to
   game regimes).

## 7. Pre-emption of the computad rewriting layer

Design rule (binding, L.15.1): every `Games/` module ships, next to its data,
(a) `toComputad : Computad` — positions as objects, legal moves as generators,
ports = mover tag (`false` = Left, `true` = Right, the `gameComputad`
convention of `Doctrine/GameDoctrine.lean`), and (b) `toDoctrine` — declared
moves = pairs of parallel paths whose endpoints are value-equal (the
sieve/value-neutral content of GL.0). This makes the A2.0 localization, the
A2.1 Focus/Port legality axioms (#8), the E-test (#9), and the GL.0
hyperdoctrine reading (#14) apply to every games module without redesign.
Port discipline: composition typing is additive (port words concatenate,
`Computad.pathLeftPorts_comp`) — the mover-tag bookkeeping of composed plays
is exactly the transfer-term cocycle of L.14.1, so the two layers meet.

## 8. Pre-emption of the Voevodsky/Nori motive layer

Design rule (binding, L.16.1): every `Games/` module ships a computable
**shadow** on bounded carriers: outcome class, value/SG class, K0 class, or
play-line data. The statement-layer bridge (`Games/MotiveBridge.lean`,
hypothesis-carriers only, no `axiom` declarations) records the dictionary:

- value theory = K0(heart) + order: `K0` of the truncated-game category
  recovers Conway's group U (U.0 #12, on BoringMath #31's
  `Algebra.GrothendieckGroup`; stalemate-as-zero = the K0 axiom);
- the partizan order is the polarization cone on K0;
- draws/loopy stalemates = non-split extensions, the consensus heart
  (C3.0 #13); Nori's diagram category as the docking point (anchor, [S]);
- the play-line complex and Lemma C / Theorem HD finite shadows (RAD.0 #11);
- temperature/cooling as the t-exact realization bet (WISH W6 — a BET,
  never a proof); thermography data from #52 / L.12.1;
- the god's-eye frame (one sheaf over moduli of doctrines; Voevodsky's
  DM^eff via BoringMath C-line/T.1) stays notes-only per #2 — the bridge
  module states only 1-categorical shadows at pin.

## 9. House rules for the line

- Boring style binding (STYLE.md): exact term proofs, whitelisted tactics
  only, `-- Reference:` per declaration with REVIEW(citation) until pinned,
  eta discipline (§5), sorries with peeling plans (§7; may persist in the
  lab), 100 columns, header, docstrings.
- Computability discipline (STYLE §2.3): explicit data, never instance-chosen;
  `TGame`/zoo modules fully computable; no `Classical.choice` in definitions.
- No `axiom` declarations (house law): hypotheses enter as structure fields or
  theorem binders (STYLE.D hypothesis-carriers).
- Mintage/F13: names stay cg-compatible for the W4 wiring (pin-back cg @
  d949bd1); nothing lab-side rebuilds a cg-owned name; the pre-wiring `Game`
  of `Games/Basic.lean` is the lab substrate until supersession at wiring.
- Lab epistemics: no unit tests — small cases are proven theorems; negative
  results are first-class deliverables; no-woo gate ([K]/[S]/[O] tags).
- POLYGRAPH-FIRST DISCIPLINE (see `docs/polygraph-first.md`, proposed for the
  LAB.0 charter #22 via #134, retitled): polygraphs (higher computads)
  generalize computads, so every theorem is stated at the HIGHEST class of
  polygraph it applies to — 1-computads when the statement lives at dimension
  1 (`GradedGameComputad.win_equation` in `Games/Graded.lean`), 2-polygraphs
  for relations between parallel paths (`Doctrine.move` = 2-cells; imperfect-
  info observational equivalences, info sets = pi0 of the path complex,
  #149/#153), 3-polygraphs for coherences (regime cocycle #64/#102, Beck-
  Chevalley #71, #154); localization = homotopy quotient; no category/set/
  infinity-category catch-alls at pin; ports carry the mover/initiative/
  time (Tate) typing at every dimension.
- Ticket naming: `L.<layer>.<n>` continuing L.1.1 (#20), L.1.2 (#21),
  L.2.1 (#52), L.3.1 (#56), L.4.1 (#63); label `work-order` (+ `lab-tree` for
  bridge nodes); bodies carry Line/node, gates, depth, scope contract, tags,
  dependencies, acceptance, protocol footer.

## 10. Sequencing (dependency-driven)

1. #85 (L.5.1 well-foundedness/induction) — unblocks all general statements.
2. #82 (L.5.2 order/outcomes), #84 (L.5.3), #81 (L.5.4) (arithmetic + equality) — the core;
   feeds L.4.1 #63's category and U.0 #12.
3. #91, #89 (L.7.1/L.7.2 nimbers/SG), #86, #87 (L.6.1/L.6.2 numbers/surreals), #92 (L.8.1) (canonical
   forms) — classical CGT proper.
4. #88 (L.9.1 ruleset engine) then #90, #93, #98 (L.9.2–L.9.4 zoo) — the dozens of standard
   libraries; #98 (Go/ko) feeds #95, #97 (L.10.1/L.10.2 loopy).
5. #94 (L.11.1 strategies) — feeds V.0 #5 (2-groupoid) and #101 (L.16.1).
6. #96 (L.12.1 thermography theorems; extends #52), #99 (L.13.1 misere completion;
   extends #56, PHI.1 #7).
7. #102 (L.14.1 games as regimes; ties to EPI.8 #41/#64), #100 (L.15.1 computad
   pre-wiring; ties to #3/#8/#9/#14), #101 (L.16.1 motive bridge statement layer;
   ties to #11/#12/#13, WISH W2/W6, BoringMath C/T/K lines).

## 11. Acceptance criteria for "mature Games library"

- Every layer 0–13 has landed modules, warning-clean under `lake build`,
  style-clean under `check-style.sh`, with the sorries only where the
  general (untruncated) statement is an honest named hole.
- Classical CGT core (order, arithmetic, numbers, SG, canonical forms)
  stated on `Game` and proven at every bounded stratum.
- 30+ zoo rulesets as data with proven small cases and computad/doctrine
  views.
- Loopy theory with the 4-valued outcome and the Go/ko instance.
- Strategy-as-data layer feeding V.0.
- Both bridges landed: regimes (EPI.8) and computad (A2.x/GL.0) views in
  every module; the motive bridge present as statement layer with
  hypothesis-carriers.

## 12. Ticket register cut in this round

New `EnidAnderson/BoringLab` issues (all label `work-order`; the three bridge
nodes also `lab-tree`), continuing the L-line:

- #83 L.0 — this charter/roadmap.
- #85 L.5.1 well-foundedness/birthday/induction for `Game`; #82 L.5.2
  normal-play outcomes + partizan order (four classes); #84 L.5.3 arithmetic
  (negation, sum, monoid laws, order compatibility); #81 L.5.4 equality +
  value quotient as computable shadow.
- #86 L.6.1 numbers as games (dyadics, simplicity); #87 L.6.2 surreal bridge.
- #91 L.7.1 nimbers/mex/Sprague-Grundy on `TGame`; #89 L.7.2 impartial worked
  families (Nim, subtraction, octal basics).
- #92 L.8.1 canonical forms (dominated/reversible options).
- #88 L.9.1 generic finite ruleset engine; #90 L.9.2 zoo I (octal/heap);
  #93 L.9.3 zoo II (partizan placement: Domineering, Hackenbush, ...);
  #98 L.9.4 zoo III (Go with ko/seki — loopy flagship — + Sprouts, peg
  solitaire, Dawson's Chess, Fox and Geese).
- #95 L.10.1 loopy games on finite graphs (4-valued outcome, greatest
  fixpoint); #97 L.10.2 loopy values (stalemate-as-draw; un-parks U.0 #12(iv)).
- #94 L.11.1 strategies as data (stealing, pairing, equality-strategies for
  V.0 #5).
- #96 L.12.1 thermography at theorem level (extends #52); #99 L.13.1 misere
  completion (kernel ledger, genus; extends #56, PHI.1 #7).
- #102 L.14.1 games as regimes (EPI.8.6 bridge to `Epistemology/Regime.lean`);
  #100 L.15.1 computad pre-wiring (`toComputad`/`toDoctrine` everywhere; A2.0
  #3 / A2.1 #8 / GL.0 #14); #101 L.16.1 motive bridge statement layer (U.0
  #12, RAD.0 #11, C3.0 #13, V.0 #5; WISH W2/W6; BoringMath C/T/K lines).

## 14. Frontier explored 2026-11-01: games as the organizing principle (tickets #142-#151)

Structural connections noticed while reading BoringMath/BoringLab, filed as
tickets (all lab-tree where they bridge):

- **The Conway motive of a game** (#143 L.17.1): the triple (K0-class in U
  #12, play-line complex #11, temperature #96) as a motive-shaped shadow in
  the games fiber — the Nori x Conway frame's finite door.
- **Plays as finite correspondences** (#145 L.17.2): the play-line complex
  `Lines ⊂ P × ∂P` is exactly a finite-correspondence shape (formal cycle on
  a product, BoringMath `Correspondence/Finite.lean` C.1); Rad/Back of #11
  are the graph-correspondence pushforward/pullback shapes.
- **A1-homotopy of plays** (#142 L.17.3): the time grading (Tate = time,
  #105/#107) as the A1 parameter of `Motives/A1.lean` (C.4 #117); value =
  A1-localization of the play correspondence; cooling = the cold heart (W6).
- **Chow = value** (#144 L.17.4): one shared pattern `K0Quotient` — Chow
  A_*(X) = K0(cycles/rational eq) (#281, BoringMath #31) vs the value group
  U = K0(positions/game equality) (#12, #81); rational equivalence ↔ game
  equality, cone ↔ partizan order.
- **The moduli of game kinds** (#147 L.18.1): `GameKind` as data (perfectInfo
  /chance/simultaneous/zeroSum/loopy) = variants on the ruleset-site (#106);
  poker-vs-chess as computed data (`Games/Kind.lean` landed: minimax-
  computable iff perfect+chance-free+alternating+acyclic; poker/go are not).
  Solvers NOT implemented.
- **Imperfect information** (#149 L.18.2): information sets = path-equivalence
  by PORT-WORDS (observability = ports, #100/#107); GAL.0 #16 deck as the
  epistemic layer.
- **Quantum games** (#146 L.18.3): statement layer only, [O]-graded, EWL 1999
  anchor; no QIT library at pin.
- **Core-computad re-anchor** (#148 L.19.1): the computad primitive graduated
  to `BoringMath.Foundations.Computad` (#391, with `ofCategory` #392) —
  supersede the lab's `GradedGameComputad` onto the core; present #63's
  category via `ofCategory`.
- **Referee automorphism invariance** (#150 L.19.2): Aut(ruleset) acts on the
  game computad; `Win` invariant — the general theorem behind #21's S3
  enumeration.
- **Games as epistemic processes** (#151 L.19.3): plays = fair experiments
  (#28), value process = identification in the limit (#31/#285),
  RegimeExperiment ↔ game regimes (#102); entropy bounds as game values
  (QG #24/#50, statement layer).

## 15. Higher computads / polygraphs (2026-11-01, tickets #152-#154)

The path structure of imperfect-information games is homotopical: on a
2-polygraph the path space has a genuine homotopy type, and information sets
are its pi0-components (observability = port words, #107). Filed:

- #153 L.20.1 — the 2-computad of games: `Doctrine.move` = 2-cells; imperfect
  info = observational 2-cells; `win_twoCell_invariant` (Win descends to pi0);
  localization = homotopy quotient (pi0 of plays / value-neutral 2-cells =
  the value quotient #81 on bounded strata).
- #152 L.20.3 — quantum strategies as local systems on the path 2-groupoid
  (amplitudes = functor to Vect; Born rule over homotopy classes; classical
  = pi0-functions); statement layer, EWL 1999 anchor.
- #154 L.20.2 — the path complex = the play-line complex (#11):
  Lemma C as a homotopy statement; the dark sector as higher homotopy.
- #155 L.20.4 — 3-cells as coherence: regime cocycle (#64/#102),
  Beck-Chevalley (#71) as 3-cell laws at the 3-polygraph level.

Discipline upgraded: `docs/polygraph-first.md` (supersedes
`docs/computad-first.md`); LAB META.1 #134 retitled polygraph-first.
