import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.Module.PUnit
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.End
import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.InformationTheory.KullbackLeibler.Basic

open CategoryTheory MeasureTheory

#check @IsOrderedMonoid
#synth CommMonoid Nat
#synth Preorder Nat
#synth IsOrderedMonoid Nat
#synth CommMonoid NNReal
#synth Preorder NNReal
#synth IsOrderedMonoid NNReal

#check @GrothendieckTopology.trivial
#check @GrothendieckTopology.toCoverage
#synth Category (Discrete PUnit)
#synth Category MeasCat
#check @Coverage
#check (GrothendieckTopology.trivial (Discrete PUnit)).toCoverage

#synth Group PUnit
#synth MulAction PUnit PUnit
#check @MulAction.fixedPoints

#synth Group (Equiv.Perm (Fin 2))
#check @Functor.const
#synth Category (Discrete (Fin 2))
#check @MeasCat.of
#synth MeasurableSpace PUnit
#check @MeasureTheory.ProbabilityMeasure
#check @Measure.dirac.isProbabilityMeasure
#check @InformationTheory.klDiv
#check @InformationTheory.klDiv_self
#check @InformationTheory.klDiv_eq_zero_iff

#check @Discrete.Hom.eq
#check @Fin.forall_fin_two
#check @Equiv.swap_apply_left
#check @Equiv.swap_apply_right
#check @Equiv.Perm.permGroup
#check (Fin.zero_ne_one' (n := 1) : (0 : Fin 2) ≠ 1)
#check @Set.ext
#check @Set.mem_setOf_eq
#check @Equiv.Perm.mul_apply
#check @Equiv.Perm.one_apply
#check @Subsingleton.elim

-- Reference: probe for BoringLab#6 (structure instance-field synthesis). -/
universe u v w
-- Reference: probe for BoringLab#6 (structure with instance-implicit fields).
structure TestPD where
  sys : Type u
  [sysCat : Category.{v} sys]
  unit : sys
  res : Type w
  [resCM : CommMonoid res]
  [resPre : Preorder res]
  [resOrd : IsOrderedMonoid res]

#check @TestPD.mk
-- Reference: probe for BoringLab#6 (omitted instance fields are synthesized).
def testInst : TestPD :=
  { sys := Discrete PUnit, unit := Discrete.mk PUnit.unit, res := Nat }

-- Reference: probe for BoringLab#6 (explicit instance fields).
def testInst2 : TestPD :=
  { sys := Discrete PUnit, sysCat := inferInstance, unit := Discrete.mk PUnit.unit,
    res := Nat, resCM := inferInstance, resPre := inferInstance, resOrd := inferInstance }
