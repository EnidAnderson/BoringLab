/-
Copyright (c) 2026 Enid. All rights reserved.
Released under the Hippocratic Mathematics License v1.0, as described in the file LICENSE.
Authors: Enid
-/
import BoringLab.Doctrine.Coverage
import BoringLab.Doctrine.Nim

/-!
# GL.0.2: the cd-structure on computads; the convention as cd-structure

Ticket #69 (child of GL.0 #14; the axiomatized-coverage rung of the
convention layer). BoringMath owns the category-level `CdStructure`
(`BoringMath/CategoryTheory/Sites/CdStructure.lean`, consumed-or-cited,
never duplicated — house law F13); this module is the COMPUTAD-level
shadow, where no `Category` instance is formed (STYLE §2.3):

* `CdSquare c` — a distinguished square of paths: objects `A B C D` with
  bottom `A → C`, left `A → B`, top `B → D`, right `C → D`;
* `CdStruct c` — distinguished squares as `Prop`-valued membership (the
  GL.0.1 #70 direction) + a `Coverage` + the leg-covering law (the top leg
  of every distinguished square is covering) + pullback-stability as the
  path-level sieve statement (every path into the source corner of a
  distinguished square is covered — the descent/referee-invariance shadow);
* the **Nim instance** (the falsifiable shadow, binding): the first
  NON-maximal convention — the distinguished squares are exactly the
  commutation squares of two removals, and every one commutes up to a
  DECLARED move (`nimCdSquare_commutes`, proved from the move witness).

## References
* [Voevodsky] V. Voevodsky, "Homotopy theory of simplicial sheaves in
  completely decomposable topologies", *J. Pure Appl. Algebra* 214 (2010)
  — the cd-structure axioms (distinguished squares; pullback stability).
* [Mac Lane–Moerdijk] S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and
  Logic*, Springer, 1992, ch. III, §6 (cd-structures and their topologies).
* Program register: BoringLab ticket #69 (GL.0.2), child of #14; the Nim
  instance uses the landed `nimDoctrine` move of the GL instance.
-/

namespace BoringLab

/-! ## Squares of paths -/

-- Reference: [Voevodsky] 2010 (a distinguished square); at the computad
-- level a square is four objects and four paths (no pullback object
-- needed — squares are data).
/-- A **square of paths** in a computad: objects `A B C D` with the bottom
`A → C`, left `A → B`, top `B → D`, right `C → D`. -/
structure CdSquare (c : Computad) where
  /-- The source corner. -/
  A : c.obj
  /-- The top-left corner. -/
  B : c.obj
  /-- The bottom-right corner. -/
  C : c.obj
  /-- The target corner. -/
  D : c.obj
  /-- The bottom leg `A → C`. -/
  bot : c.Path A C
  /-- The left leg `A → B`. -/
  left : c.Path A B
  /-- The top leg `B → D`. -/
  top : c.Path B D
  /-- The right leg `C → D`. -/
  right : c.Path C D

-- Reference: [Barendregt], ch. 2 (eta conversion), as in `Sieve.eta`.
-- REVIEW(citation): pin down the exact section in review.
/-- **Eta conversion for cd-squares**. -/
theorem CdSquare.eta {c : Computad} (sq : CdSquare c) :
    CdSquare.mk sq.A sq.B sq.C sq.D sq.bot sq.left sq.top sq.right = sq := by
  cases sq with
  | mk A B C D bot left top right => rfl

/-! ## The cd-structure on a computad -/

-- Reference: ticket #69, item (i); [Voevodsky] 2010; membership
-- `Prop`-valued (the GL.0.1 #70 direction), the coverage as the induced
-- covering data, the leg-covering law, and pullback stability as the
-- path-level sieve statement (descent = referee invariance).
/-- A **cd-structure on a computad**: distinguished squares
(`Prop`-valued membership), a coverage, the leg-covering law (the top leg
of every distinguished square is covering), and path-level pullback
stability (every path into the source corner of a distinguished square is
covered). -/
structure CdStruct (c : Computad) where
  /-- The distinguished squares. -/
  squares : CdSquare c → Prop
  /-- The induced coverage. -/
  covering : Coverage c
  /-- The top leg of every distinguished square is covering. -/
  legCovering : ∀ (sq : CdSquare c), squares sq →
    (covering sq.D).any (fun s => s.arrows ⟨sq.B, sq.top⟩) = true
  /-- Path-level pullback stability: every path into the source corner of
  a distinguished square is covered (descent as referee invariance). -/
  stable : ∀ (sq : CdSquare c), squares sq →
    ∀ (W : c.obj) (p : c.Path W sq.A),
      (covering sq.A).any (fun s => s.arrows ⟨W, p⟩) = true

/-! ## The Nim instance: commutation squares -/

-- Reference: ticket #69, item (ii) (the first NON-maximal convention):
-- the commutation square of two removals from `X` — left = remove `k` to
-- `M`, bot = remove `j` to `M'`, top = remove `j` from `M` to `Y`, right =
-- remove `k` from `M'` to `Y`.
/-- The **Nim commutation square** at `X Y M M' k j` with the legality data. -/
def nimCdSquare {X Y M M' k j : ℕ} (hk : 0 < k) (hj : 0 < j)
    (h1 : M + k = X) (h2 : Y + j = M) (h3 : M' + j = X) (h4 : Y + k = M') :
    CdSquare nimComputad where
  A := X
  B := M
  C := M'
  D := Y
  bot := nimComputad.toPath ⟨⟨⟨X, M', j⟩, h3, hj⟩, rfl, rfl⟩
  left := nimComputad.toPath ⟨⟨⟨X, M, k⟩, h1, hk⟩, rfl, rfl⟩
  top := nimComputad.toPath ⟨⟨⟨M, Y, j⟩, h2, hj⟩, rfl, rfl⟩
  right := nimComputad.toPath ⟨⟨⟨M', Y, k⟩, h4, hk⟩, rfl, rfl⟩

-- Reference: ticket #69, item (ii) — binding falsifiable shadow: every
-- distinguished Nim square COMMUTES UP TO A DECLARED MOVE — the two paths
-- around the square are exactly the `nimDoctrine.move` witness.
/-- The Nim commutation square commutes up to a declared move. -/
theorem nimCdSquare_commutes {X Y M M' k j : ℕ} (hk : 0 < k) (hj : 0 < j)
    (h1 : M + k = X) (h2 : Y + j = M) (h3 : M' + j = X) (h4 : Y + k = M') :
    nimDoctrine.move
      ((nimCdSquare hk hj h1 h2 h3 h4).left.comp (nimCdSquare hk hj h1 h2 h3 h4).top)
      ((nimCdSquare hk hj h1 h2 h3 h4).bot.comp (nimCdSquare hk hj h1 h2 h3 h4).right) :=
  ⟨M, M', k, j, hk, hj, h1, h2, h3, h4, rfl, rfl⟩

-- Reference: ticket #69, item (ii): the Nim cd-structure — distinguished
-- squares = the commutation squares; coverage = the landed `nimCoverage`
-- (maximal); the leg and stability laws hold because the maximal sieve
-- contains every arrow (`Sieve.maximal_arrows`, `List.any_eq_true`).
/-- The **Nim cd-structure**: the commutation squares are distinguished,
with the maximal coverage. -/
def nimCdStruct : CdStruct nimComputad where
  squares := fun sq =>
    ∃ (X Y M M' k j : ℕ) (hk : 0 < k) (hj : 0 < j)
      (h1 : M + k = X) (h2 : Y + j = M) (h3 : M' + j = X) (h4 : Y + k = M'),
      sq = nimCdSquare hk hj h1 h2 h3 h4
  covering := nimCoverage
  legCovering := fun sq _ =>
    List.any_eq_true.mpr ⟨Sieve.maximal nimComputad sq.D, List.mem_cons_self,
      Sieve.maximal_arrows nimComputad sq.D ⟨sq.B, sq.top⟩⟩
  stable := fun sq _ W p =>
    List.any_eq_true.mpr ⟨Sieve.maximal nimComputad sq.A, List.mem_cons_self,
      Sieve.maximal_arrows nimComputad sq.A ⟨W, p⟩⟩

-- Reference: the concrete witness of the instance: the `5, k=2, j=1`
-- commutation square is distinguished.
/-- The `5,2,1` commutation square is a distinguished square of the Nim
cd-structure. -/
theorem nimCdStruct_square_mem :
    nimCdStruct.squares (nimCdSquare (X := 5) (Y := 2) (M := 3) (M' := 4) (k := 2) (j := 1)
      (Nat.succ_pos 1) (Nat.succ_pos 0) rfl rfl rfl rfl) :=
  ⟨5, 2, 3, 4, 2, 1, Nat.succ_pos 1, Nat.succ_pos 0, rfl, rfl, rfl, rfl, rfl⟩

end BoringLab
