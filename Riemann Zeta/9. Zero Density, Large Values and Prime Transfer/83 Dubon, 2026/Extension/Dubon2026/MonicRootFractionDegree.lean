import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.LinearAlgebra.Dimension.Free

/-! # The actual fraction-field degree of the original monic root algebra -/

namespace Dubon2026
noncomputable section

open Polynomial

/-- Localization of the original power basis gives the actual field degree
and finite-dimensionality. No field-rank conclusion is supplied as a premise. -/
theorem monicRootFraction_finrank_and_finite
    (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] (f : R[X]) [IsDomain (AdjoinRoot f)]
    [Algebra (AdjoinRoot f) L] [IsFractionRing (AdjoinRoot f) L]
    [IsScalarTower R (AdjoinRoot f) L]
    (hf : f.Monic) (hd : 0 < f.natDegree) :
    Module.finrank K L = f.natDegree ∧ FiniteDimensional K L := by
  haveI : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  have hinj : Function.Injective (algebraMap R (AdjoinRoot f)) := by
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    intro h
    exact (Nat.ne_of_gt hd) (Polynomial.natDegree_eq_of_degree_eq_some h)
  haveI : FaithfulSMul R (AdjoinRoot f) :=
    (faithfulSMul_iff_algebraMap_injective R (AdjoinRoot f)).mpr hinj
  have hdegree : Module.finrank K L = f.natDegree :=
    (Algebra.IsAlgebraic.finrank_of_isFractionRing R K (AdjoinRoot f) L).trans
      (AdjoinRoot.powerBasis' hf).finrank
  exact ⟨hdegree, Module.finite_of_finrank_pos (hdegree.symm ▸ hd)⟩

end
end Dubon2026
