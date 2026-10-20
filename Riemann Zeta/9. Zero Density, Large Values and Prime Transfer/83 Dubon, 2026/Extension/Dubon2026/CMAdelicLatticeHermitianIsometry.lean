import Dubon2026.CMAdelicLatticeTraceIsometry

/-! # Recovering the original CM Hermitian isometry from equal invariants

The recovered map is linear over the original field and preserves the
original rational trace pairing. Testing all original field multiples
of the second vector and using the native nondegenerate field trace
recovers the full original Hermitian pairing. This removes the
Hermitian-isometry assumption from DUB-17's double-coset recovery step.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix Module LinearMap.BilinForm

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Equal original Gram and CM action invariants recover the original Hermitian pairing. -/
theorem cmAdelicLatticeFieldEquiv_hermitian (H : Matrix ι ι K)
    (d : ℤ) (hd : d ≠ 0) (hIntegral : ∀ i j, IsIntegral ℤ (d • H i j))
    (g h : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val))
    (c : Basis κ ℤ (numberFieldAdelicLattice K ι h.val))
    (hGram : toMatrix b (cmAdelicLatticeIntegralTraceForm K H d hIntegral g) =
      toMatrix c (cmAdelicLatticeIntegralTraceForm K H d hIntegral h))
    (hAct : cmAdelicLatticeIntegralActions K H g b = cmAdelicLatticeIntegralActions K H h c)
    (x y : ι → K) :
    dotProduct (star (cmAdelicLatticeFieldEquiv K H g h b c hAct x))
      (H.mulVec (cmAdelicLatticeFieldEquiv K H g h b c hAct y)) =
        dotProduct (star x) (H.mulVec y) := by
  let e := cmAdelicLatticeFieldEquiv K H g h b c hAct
  apply sub_eq_zero.mp
  apply (traceForm_nondegenerate ℚ K).1
  intro a
  change Algebra.trace ℚ K
    ((dotProduct (star (e x)) (H.mulVec (e y)) - dotProduct (star x) (H.mulVec y)) * a) = 0
  rw [sub_mul, map_sub]
  apply sub_eq_zero.mpr
  have ht := cmAdelicLatticeRationalEquiv_trace K H d hd hIntegral g h b c hGram x (a • y)
  change Algebra.trace ℚ K (dotProduct (star (e x)) (H.mulVec (e (a • y)))) =
    Algebra.trace ℚ K (dotProduct (star x) (H.mulVec (a • y))) at ht
  rw [e.map_smul, mulVec_smul, dotProduct_smul, mulVec_smul, dotProduct_smul] at ht
  simpa only [smul_eq_mul, mul_comm] using ht

end
end Dubon2026
