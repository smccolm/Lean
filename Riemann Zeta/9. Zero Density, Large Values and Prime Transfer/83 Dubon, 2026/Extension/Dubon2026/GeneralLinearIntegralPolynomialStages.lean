import Dubon2026.GeneralLinearIntegralDeterminantTwist
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! Exact polynomial stages of the original integral induced module.
Each stage bounds the actual determinant denominator and numerator degree;
over the source PID it is finite free, and every original induced function
belongs to some stage. A uniform stage for a fixed source weight is still
required. Exhaustion by finite stages is not finite generation of the union.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R : Type u) [CommRing R] (n : ℕ)

/-- The actual determinant unit has precisely the original determinant polynomial as its value. -/
theorem generalLinearRegularDeterminantUnit_val :
    (generalLinearRegularDeterminantUnit (R := R) (n := n) : GeneralLinearRegularFunctions R n) =
      generalLinearRegularPolynomialMap R n (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)) := by
  change Matrix.det ((Matrix.mvPolynomialX (Fin n) (Fin n) R).map
    (generalLinearRegularPolynomialMap R n)) = _
  exact (AlgHom.map_det (generalLinearRegularPolynomialMap R n) _).symm

/-- The original polynomial numerator is sent to its actual fraction with a specified determinant denominator. -/
def generalLinearRegularFractionMap (d : ℕ) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] GeneralLinearRegularFunctions R n :=
  (LinearMap.mulLeft R (((generalLinearRegularDeterminantUnit ^ d)⁻¹ :
    (GeneralLinearRegularFunctions R n)ˣ) : GeneralLinearRegularFunctions R n)).comp
      (generalLinearRegularPolynomialMap R n).toLinearMap

/-- Every original regular function has an actual polynomial numerator and determinant denominator. -/
theorem generalLinearRegular_exists_fraction (p : GeneralLinearRegularFunctions R n) :
    ∃ (d : ℕ) (P : MvPolynomial (Fin n × Fin n) R),
      generalLinearRegularFractionMap R n d P = p := by
  obtain ⟨d, P, hP⟩ := IsLocalization.Away.surj
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)) p
  refine ⟨d, P, ?_⟩
  change ((generalLinearRegularDeterminantUnit ^ d)⁻¹ :
    (GeneralLinearRegularFunctions R n)ˣ) * generalLinearRegularPolynomialMap R n P = p
  change p * (generalLinearRegularPolynomialMap R n
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))) ^ d =
      generalLinearRegularPolynomialMap R n P at hP
  rw [← hP, ← generalLinearRegularDeterminantUnit_val, ← Units.val_pow_eq_pow_val]
  rw [mul_left_comm, Units.inv_mul, mul_one]

/-- Clearing the actual determinant denominator gives the exact shifted Borel covariance of the same original polynomial numerator. -/
theorem generalLinearIntegralInduced_polynomial_numerator (lam : Fin n → ℤ)
    (d : ℕ) (P : MvPolynomial (Fin n × Fin n) R)
    (hP : generalLinearRegularFractionMap R n d P ∈
      generalLinearIntegralInducedSubmodule R n lam) :
    generalLinearRegularPolynomialMap R n P ∈
      generalLinearIntegralInducedSubmodule R n (fun i => lam i + (d : ℤ)) := by
  have h := generalLinearIntegralInduced_determinant_twist lam (d : ℤ) hP
  simpa only [zpow_natCast, generalLinearRegularFractionMap, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, ← mul_assoc,
    Units.mul_inv, one_mul] using h

/-- The original regular functions with fixed determinant denominator and bounded numerator degree. -/
def generalLinearRegularPolynomialStage (d D : ℕ) :
    Submodule R (GeneralLinearRegularFunctions R n) :=
  (MvPolynomial.restrictTotalDegree (Fin n × Fin n) R D).map
    (generalLinearRegularFractionMap R n d)

/-- The exact source induced functions within an actual bounded polynomial stage. -/
def generalLinearIntegralInducedStage (lam : Fin n → ℤ) (d D : ℕ) :
    Submodule R (GeneralLinearRegularFunctions R n) :=
  generalLinearIntegralInducedSubmodule R n lam ⊓ generalLinearRegularPolynomialStage R n d D

/-- A bounded polynomial stage is finite over the original coefficient ring. -/
instance generalLinearRegularPolynomialStageFinite (d D : ℕ) :
    Module.Finite R (generalLinearRegularPolynomialStage R n d D) :=
  inferInstanceAs (Module.Finite R ((MvPolynomial.restrictTotalDegree (Fin n × Fin n) R D).map
    (generalLinearRegularFractionMap R n d)))

/-- Over the source Noetherian ring, the exact induced functions in each bounded polynomial stage form a finite module. -/
instance generalLinearIntegralInducedStageFinite [IsNoetherianRing R]
    (lam : Fin n → ℤ) (d D : ℕ) :
    Module.Finite R (generalLinearIntegralInducedStage R n lam d D) := by
  exact Module.Finite.of_injective
    (Submodule.inclusion (show generalLinearIntegralInducedStage R n lam d D ≤
      generalLinearRegularPolynomialStage R n d D from inf_le_right))
    (Submodule.inclusion_injective _)

/-- Over the source PID, every exact induced polynomial stage is finite free; no uniform-stage conclusion is asserted. -/
instance generalLinearIntegralInducedStageFree [IsDomain R] [IsPrincipalIdealRing R]
    (lam : Fin n → ℤ) (d D : ℕ) :
    Module.Free R (generalLinearIntegralInducedStage R n lam d D) := inferInstance

/-- The bounded stages exhaust the actual induced module, with both bounds attached to the same original function. -/
theorem generalLinearIntegralInducedStage_exhausts (lam : Fin n → ℤ)
    (p : generalLinearIntegralInducedSubmodule R n lam) :
    ∃ d D, p.val ∈ generalLinearIntegralInducedStage R n lam d D := by
  obtain ⟨d, P, hP⟩ := generalLinearRegular_exists_fraction R n p.val
  refine ⟨d, P.totalDegree, p.property, ?_⟩
  exact Submodule.mem_map.mpr ⟨P,
    (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl, hP⟩

end
end Dubon2026
