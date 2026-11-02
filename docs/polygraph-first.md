# The polygraph-first discipline (proposed charter rule; supersedes docs/computad-first.md)

Status: recorded here and in `docs/games-library-roadmap.md` §9; proposed for
adoption as a binding rule of the LAB.0 charter (`EnidAnderson/BoringLab#22`)
via ticket LAB META.1 (#134, retitled). **Polygraphs (higher computads)
generalize computads**: a computad is a 1-polygraph; an n-polygraph adds
k-cells (k >= 2) between parallel lower-dimensional cells — 2-cells relate
parallel paths (Mimram Def. 3.5's sequents), 3-cells are coherences between
2-cells, etc. Anchors: #2 (LAB TREE X.0), #3 (A2.0), #14 (GL.0), #22 (charter),
#72 (META.0), #134, #152/#153 (L.20.x).

## The rule

**State every theorem at the highest class of polygraph (higher computad) to
which it applies; use polygraphs as the ambient formalism instead of category
theory or set theory wherever possible. "Category theory" and
"infinity-category theory" are never used as a catch-all; in particular an
ordinary (1-dimensional) computad is used only when the statement genuinely
lives at dimension 1.**

Concretely:

1. **Upgrade to the dimension the theorem needs.** If a theorem holds for all
   graded 1-computads, prove it there (`GradedGameComputad.win_equation`,
   `Games/Graded.lean`); if it needs relations between parallel paths, state
   it for 2-polygraphs (our `Doctrine.move` is exactly a 2-cell layer; the
   imperfect-information observational equivalences — equal port words — are
   2-cells, so information sets are pi0-components of the path complex, #149/
   #153); if it needs coherences between 2-cells, state it for 3-polygraphs
   (the regime transfer-term cocycle #64/#102 and Beck-Chevalley #71 are
   3-cell coherence laws, #154).
2. **Ports carry the typing at every dimension.** Composition typing is
   additive (port words concatenate, `Computad.pathLeftPorts_comp`); mover
   tags, initiative tokens, and the time/ply (Tate) grading are ports/gradings
   on the cells, not ambient metadata (#100/#105/#107).
3. **Localization = homotopy quotient.** The doctrine-localization (inverting
   the declared-move class, #14) is, homotopically, collapsing the 2-cells:
   pi0 of the path complex of a 2-polygraph is the quotient of plays by the
   declared relations (the value quotient of #81 on bounded strata). State
   this dictionary at the polygraph level (#153).
4. **No infinity-categorical catch-alls at pin.** mathlib at `v4.35.0-rc3` has
   no (∞,1)-categories; the honest doors are (i) 1-categorical localization
   in-tree, (ii) the triangulated/quotient layer (BoringMath #23), (iii)
   group-completion shadows (BoringMath #31), and (iv) FINITE polygraphs,
   which need no ∞-machinery: our n-polygraphs at the lab are finite/computable
   presentations, so the higher-dimensional content enters as explicit cells,
   never as an ∞-catch-all. Would-be ∞-statements stay notes-only (#2).
5. **Category theory only when the content IS categorical**, via in-tree
   1-categorical machinery with STYLE §2.3 explicit data; **set theory only at
   the substrate** (object types of a polygraph).

## Why

Polygraphs are extremely expressive and exactly match the game-theoretic
content: positions = 0-cells, moves = 1-cells (port-typed), rules of play /
observational equivalences / value-neutral simplifications = 2-cells,
coherences (cocycles, Beck-Chevalley) = 3-cells. The path complex of the
polygraph has a genuine homotopy type — pi0 = information sets / value
classes, higher homotopy = the play-line complex phenomena (Lemma C, the dark
sector, #11/#20.2) — and quantum strategies are local systems on it (#152).
This keeps the lab's proofs computable and falsifiable and pre-empts the
motive layers (value/K0 shadows live on the same polygraphs).

## References

- [Burroni] A. Burroni, TCS 126 (1994) 257-291 — polygraphs (n-computads).
- [Mimram] S. Mimram, arXiv:2312.00429, LMCS 21(3) (2025), Def. 3.1 (1-
  polygraph) and 3.5 (2-polygraph: relations between parallel paths).
- [Street] R. Street, JPAA 49 (1987) 283-335 — computads and free higher
  categories.
- [Makkai] — computads/polygraphs as presentations of higher categories.
- Program register: BoringLab #2, #3, #14, #22, #72, #100, #105-#107,
  #134, #142-#154; `BoringLab/Doctrine/Computad.lean`,
  `BoringLab/Games/Graded.lean`.
