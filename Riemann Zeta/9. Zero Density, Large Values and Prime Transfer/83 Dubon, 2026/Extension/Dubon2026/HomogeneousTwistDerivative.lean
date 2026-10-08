import Dubon2026.HomogeneousNormDerivative
import Dubon2026.HomogeneousDeterminantTwist
import Dubon2026.HomogeneousEulerAction
import Dubon2026.ComplexIdentityMatrixCurve

/-! # Genuine norm derivatives of the original determinant-twisted algebraic GL₂ action -/

namespace Dubon2026

noncomputable section
open MvPolynomial Filter
open scoped Topology

/-- The actual determinant character has its exact original trace derivative along the genuine identity matrix curve. -/
theorem complexIdentityMatrixCurve_det_zpow_hasDerivAt (a : Matrix (Fin 2) (Fin 2) ℂ) (m : ℤ) :
    HasDerivAt (fun t : ℂ => Matrix.det (1 + t • a) ^ m) ((m : ℂ) * Matrix.trace a) 0 := by
  have hd := (hasDerivAt_zpow m (Matrix.det (1 + (0 : ℂ) • a)) (Or.inl (by simp))).comp 0
    (complexIdentityMatrixCurve_det_hasDerivAt a)
  simpa using hd

/-- The genuine twisted matrix orbit has its actual norm derivative, including the exact determinant trace contribution. -/
theorem homogeneousDeterminantTwist_hasDerivAt (n : ℕ) (m : ℤ)
    (a : Matrix (Fin 2) (Fin 2) ℂ) (p : homogeneousSubmodule (Fin 2) ℂ n) :
    HasDerivAt (fun t : ℂ => homogeneousDeterminantTwist n m (complexIdentityGLCurve a t) p)
      (((m : ℂ) * Matrix.trace a) • p + homogeneousMatrixLieAction n a p) 0 := by
  have h₁ : homogeneousMatrixAction n (1 : Matrix (Fin 2) (Fin 2) ℂ) p = p :=
    LinearMap.congr_fun (map_one (homogeneousMatrixRepresentation n)) p
  have hd := (complexIdentityMatrixCurve_det_zpow_hasDerivAt a m).smul
    (homogeneousMatrixOrbit_hasDerivAt n a p)
  simp only [zero_smul, add_zero, Matrix.det_one, one_zpow, h₁, one_smul] at hd
  have he : (fun t : ℂ => homogeneousDeterminantTwist n m (complexIdentityGLCurve a t) p) =ᶠ[𝓝 0]
      (fun t : ℂ => Matrix.det (1 + t • a) ^ m • homogeneousMatrixAction n (1 + t • a) p) := by
    filter_upwards [complexIdentityGLCurve_eventually a] with t ht
    change Matrix.det (complexIdentityGLCurve a t : Matrix (Fin 2) (Fin 2) ℂ) ^ m •
      homogeneousMatrixAction n (complexIdentityGLCurve a t : Matrix (Fin 2) (Fin 2) ℂ) p = _
    rw [ht]
  simpa only [add_comm] using hd.congr_of_eventuallyEq he

/-- For degree 2m and determinant twist det^-m, the true original GL₂ norm derivative is the genuine traceless projection action. -/
theorem homogeneousNormalizedTwist_hasDerivAt (m : ℕ) (a : Matrix (Fin 2) (Fin 2) ℂ)
    (p : homogeneousSubmodule (Fin 2) ℂ (2 * m)) :
    HasDerivAt (fun t : ℂ => homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) (complexIdentityGLCurve a t) p)
      (homogeneousSl2Action (2 * m) (complexTracelessProjection a) p) 0 := by
  have hd := homogeneousDeterminantTwist_hasDerivAt (2 * m) (-(m : ℤ)) a p
  push_cast at hd
  have he : ((-(m : ℂ)) * Matrix.trace a) • p + homogeneousMatrixLieAction (2 * m) a p =
      homogeneousSl2Action (2 * m) (complexTracelessProjection a) p := by
    have hs := homogeneousMatrixLieAction_sub_scalar (2 * m) a (Matrix.trace a / 2) p
    change homogeneousSl2Action (2 * m) (complexTracelessProjection a) p = _ at hs
    rw [hs]
    have hc : (Matrix.trace a / 2) * ((2 * m : ℕ) : ℂ) = (m : ℂ) * Matrix.trace a := by push_cast; ring
    rw [hc]
    simp only [neg_mul, neg_smul, sub_eq_add_neg, add_comm]
  exact he ▸ hd

end
end Dubon2026
