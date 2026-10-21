import Dubon2026.HeckeTriangular
import Dubon2026.SourceJPolynomialDescent
import Dubon2026.SourceLaurentReindex


/-! DUB-17/18 -> original differential realization -> finite function-field
extension -> monic relations. Identify each literal formal prime conjugate with
the actual analytic translate, using the already proved native Hecke matrices.
This retains the full upper-half-plane convergence and coefficient embeddings.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_hasSum_qParam_heckeMatrix_smul.lean and diagonal companion.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups
local notation "𝕢" => Function.Periodic.qParam

theorem coe_primeUpper_smul (ℓ : ℕ) [NeZero ℓ] (b : ℕ) (τ : ℍ) :
    ((heckeTriangularMatrix 1 ℓ b • τ : ℍ) : ℂ) = ((τ : ℂ) + b) / ℓ := by
  rw [heckeTriangularMatrix_smul]
  change (((levelRaiseMatrix 1 • τ : ℍ) : ℂ) + b) / ℓ = _
  rw [coe_levelRaiseMatrix_smul]
  simp

theorem coe_primeDiagonal_smul (ℓ : ℕ) [NeZero ℓ] (τ : ℍ) :
    ((heckeTriangularMatrix ℓ 1 0 • τ : ℍ) : ℂ) = (ℓ : ℂ) * (τ : ℂ) := by
  rw [heckeTriangularMatrix_smul]
  change (((levelRaiseMatrix ℓ • τ : ℍ) : ℂ) + (0 : ℕ)) / (1 : ℕ) = _
  rw [coe_levelRaiseMatrix_smul]
  simp

namespace Realized

theorem hasSum_qParam_heckeMatrix_smul (ℓ : ℕ) [NeZero ℓ] (b : ℕ) (A : LaurentSeries ℂ) (F : ℍ → ℂ)
    (hA : ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 1 (τ : ℂ) ^ m) (F τ)) (τ : ℍ) :
    HasSum (fun m : ℤ => (Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) * A.coeff m) * 𝕢 ℓ (τ : ℂ) ^ m)
      (F (heckeTriangularMatrix 1 ℓ b • τ)) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have hℓ' : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ
  have e : 𝕢 1 ((heckeTriangularMatrix 1 ℓ b • τ : ℍ) : ℂ)
      = Complex.exp (2 * Real.pi * Complex.I * b / ℓ) * 𝕢 ℓ (τ : ℂ) := by
    rw [coe_primeUpper_smul, Periodic.qParam, Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have e2 : ∀ m : ℤ, Complex.exp (2 * Real.pi * Complex.I * b / ℓ) ^ m
      = Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) := by
    intro m
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  have hfg : (fun m : ℤ => (Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) * A.coeff m) * 𝕢 ℓ (τ : ℂ) ^ m)
      = fun m : ℤ => A.coeff m * 𝕢 1 ((heckeTriangularMatrix 1 ℓ b • τ : ℍ) : ℂ) ^ m := by
    funext m
    rw [e, mul_zpow, e2]
    ring
  rw [hfg]
  exact hA _


theorem hasSum_qParam_heckeDiagMatrix_smul (ℓ : ℕ) [NeZero ℓ] (A : LaurentSeries ℂ) (F : ℍ → ℂ)
    (hA : ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 1 (τ : ℂ) ^ m) (F τ)) (τ : ℍ) :
    HasSum (fun m : ℤ => (Dubon2026.SourceFunctionField.qExpand ℂ (ℓ * ℓ) A).coeff m * 𝕢 ℓ (τ : ℂ) ^ m)
      (F (heckeTriangularMatrix ℓ 1 0 • τ)) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have hℓ' : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ
  have hN : ((ℓ * ℓ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne (ℓ * ℓ))
  have e : 𝕢 1 ((heckeTriangularMatrix ℓ 1 0 • τ : ℍ) : ℂ) = 𝕢 ℓ (τ : ℂ) ^ ((ℓ * ℓ : ℕ) : ℤ) := by
    rw [coe_primeDiagonal_smul, Periodic.qParam, Periodic.qParam, zpow_natCast,
      ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hinj : Function.Injective (fun m : ℤ => ((ℓ * ℓ : ℕ) : ℤ) * m) := mul_right_injective₀ hN
  rw [← hinj.hasSum_iff]
  · have hfg : (fun m : ℤ => (Dubon2026.SourceFunctionField.qExpand ℂ (ℓ * ℓ) A).coeff m * 𝕢 ℓ (τ : ℂ) ^ m) ∘
        (fun m : ℤ => ((ℓ * ℓ : ℕ) : ℤ) * m)
        = fun m : ℤ => A.coeff m * 𝕢 1 ((heckeTriangularMatrix ℓ 1 0 • τ : ℍ) : ℂ) ^ m := by
      funext m
      simp only [Function.comp_apply]
      rw [Dubon2026.SourceFunctionField.qExpand_coeff_mul, e, ← zpow_mul]
    rw [hfg]
    exact hA _
  · intro m hm
    rw [Dubon2026.SourceFunctionField.qExpand_coeff_of_not_dvd (ℓ * ℓ) A (fun ⟨c, hc⟩ => hm ⟨c, hc.symm⟩), zero_mul]


end Realized

end
end Dubon2026.SourceFunctionField
