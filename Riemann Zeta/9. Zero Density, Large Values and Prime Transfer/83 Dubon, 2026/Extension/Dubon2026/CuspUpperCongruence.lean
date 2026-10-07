import Dubon2026.HeckeTriangular
import Dubon2026.PrincipalCuspAction

/-! # Actual rescaling from Gamma0(N) to the upper congruence group -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

/-- The genuine upper congruence subgroup Γ⁰(N), defined by its upper-right entry. -/
def GammaUpper (N : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {γ | (γ 0 1 : ZMod N) = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (((a * b) 0 1 : ℤ) : ZMod N) = 0
    simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    change (a 0 0 : ZMod N) * (b 0 1 : ZMod N) + (a 0 1 : ZMod N) * (b 1 1 : ZMod N) = 0
    rw [ha, hb, mul_zero, zero_mul, add_zero]
  inv_mem' := by
    intro a ha
    change (((a⁻¹) 0 1 : ℤ) : ZMod N) = 0
    rw [SL2_inv_expl]
    simpa using congrArg Neg.neg ha

/-- Every principal-level matrix is in the upper congruence group. -/
theorem Gamma_le_GammaUpper (N : ℕ) : Gamma N ≤ GammaUpper N :=
  fun _ h => (Gamma_mem.mp h).2.1

/-- The integral conjugate by diag(1,N), available exactly when N divides the upper-right entry. -/
def upperCongruenceConjugate (N : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ GammaUpper N) : SL(2, ℤ) :=
  ⟨!![γ 0 0, γ 0 1 / N; N * γ 1 0, γ 1 1], by
    have hd : (N : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
    rw [Matrix.det_fin_two_of]
    linear_combination (Matrix.det_fin_two γ.val).symm.trans γ.property +
      γ 1 0 * (Int.ediv_mul_cancel hd).symm⟩

/-- The rescaling conjugate belongs to the actual lower congruence group of the same level. -/
theorem upperCongruenceConjugate_mem (N : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ GammaUpper N) :
    upperCongruenceConjugate N γ hγ ∈ Gamma0 N := by
  change (((N : ℤ) * γ 1 0 : ℤ) : ZMod N) = 0
  simp

/-- The exact integral matrix transition for the rescaling z ↦ z/N. -/
theorem upperCongruenceConjugate_mul (N : ℕ) [NeZero N]
    (γ : SL(2, ℤ)) (hγ : γ ∈ GammaUpper N) :
    mapGL ℝ (upperCongruenceConjugate N γ hγ) * heckeTriangularMatrix 1 N 0 =
      heckeTriangularMatrix 1 N 0 * mapGL ℝ γ := by
  have hd : (N : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  have hreal : ((γ 0 1 / (N : ℤ) : ℤ) : ℝ) * N = (γ 0 1 : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hd
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    heckeTriangularMatrix_val, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [upperCongruenceConjugate, hreal]
  exact mul_comm _ _

/-- The upper congruence group lies in the translated Gamma0 invariance group. -/
theorem GammaUpper_le_rescaledGamma0 (N : ℕ) [NeZero N] :
    (GammaUpper N).map (mapGL ℝ) ≤
      ConjAct.toConjAct (heckeTriangularMatrix 1 N 0)⁻¹ • (Gamma0 N).map (mapGL ℝ) := by
  rintro g ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨mapGL ℝ (upperCongruenceConjugate N γ hγ),
    ⟨_, upperCongruenceConjugate_mem N γ hγ, rfl⟩, ?_⟩
  change (heckeTriangularMatrix 1 N 0)⁻¹ * mapGL ℝ (upperCongruenceConjugate N γ hγ) *
    heckeTriangularMatrix 1 N 0 = mapGL ℝ γ
  rw [mul_assoc, upperCongruenceConjugate_mul, inv_mul_cancel_left]

/-- The actual linear rescaling f(z) ↦ f(z/N), now as a cusp form for Γ⁰(N). -/
def cuspUpperRescale (N : ℕ) [NeZero N] (k : ℤ) :
    CuspForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((GammaUpper N).map (mapGL ℝ)) k where
  toFun f := (N : ℂ) • cuspRestrictSubgroup (GammaUpper_le_rescaledGamma0 N)
    (CuspForm.translate f (heckeTriangularMatrix 1 N 0))
  map_add' f g := by
    ext τ
    change (N : ℂ) • ((⇑(f + g) ∣[k] heckeTriangularMatrix 1 N 0) τ) = _
    simp only [CuspForm.coe_add, SlashAction.add_slash, Pi.add_apply, smul_add]
    rfl
  map_smul' c f := by
    ext τ
    change (N : ℂ) * ((⇑(c • f) ∣[k] heckeTriangularMatrix 1 N 0) τ) =
      c * ((N : ℂ) * ((⇑f ∣[k] heckeTriangularMatrix 1 N 0) τ))
    simp only [show (⇑(c • f) : ℍ → ℂ) = c • ⇑f from rfl,
      heckeTriangular_slash_apply, Pi.smul_apply, smul_eq_mul]
    ring1

/-- No determinant normalization remains in the actual rescaled function. -/
theorem cuspUpperRescale_apply (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (τ : ℍ) :
    cuspUpperRescale N k f τ = f (heckeUpperPoint N 0 τ) := by
  change (N : ℂ) * ((⇑f ∣[k] heckeTriangularMatrix 1 N 0) τ) = _
  rw [heckeTriangular_slash_apply]
  have he : levelRaiseMatrix 1 • τ = τ := by
    apply UpperHalfPlane.ext
    simp [coe_levelRaiseMatrix_smul]
  rw [he]
  simp [Nat.cast_ne_zero.mpr (NeZero.ne N)]

end
end Dubon2026
