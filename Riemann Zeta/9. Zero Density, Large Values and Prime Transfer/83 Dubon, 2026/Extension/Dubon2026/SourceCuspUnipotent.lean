import Dubon2026.SL2Reduction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic

/-! DUB-17/18 -> residual Galois association -> nonparabolic original
complex weight-two eigenclass -> its finite cusp-boundary function.
These exact integral matrices prove that cusp evaluation depends only on
the reduced primitive column. Adapted from the archived Apache-2.0
anthropics/fermats-last-theorem revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul.
Only the original Gamma0 case is needed in the downstream boundary consumer.
-/
namespace Dubon2026.SourceCuspBoundary
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The exact integral unipotent attached to a primitive cusp column. -/
def unipMat (p q m : ℤ) : SL(2, ℤ) :=
  ⟨!![1 - m * p * q, m * p * p; -(m * q * q), 1 + m * p * q], by
    rw [Matrix.det_fin_two_of]; ring⟩

/-- The exact 00 entry of the original cusp unipotent. -/
@[scoped simp] theorem unipMat_apply_00 (p q m : ℤ) : (unipMat p q m) 0 0 = 1 - m * p * q := rfl
/-- The exact 01 entry of the original cusp unipotent. -/
@[scoped simp] theorem unipMat_apply_01 (p q m : ℤ) : (unipMat p q m) 0 1 = m * p * p := rfl
/-- The exact 10 entry of the original cusp unipotent. -/
@[scoped simp] theorem unipMat_apply_10 (p q m : ℤ) : (unipMat p q m) 1 0 = -(m * q * q) := rfl
/-- The exact 11 entry of the original cusp unipotent. -/
@[scoped simp] theorem unipMat_apply_11 (p q m : ℤ) : (unipMat p q m) 1 1 = 1 + m * p * q := rfl

/-- Conjugating the actual integral translation gives the explicit cusp unipotent. -/
theorem conj_T_zpow_eq_unipMat (δ : SL(2, ℤ)) (m : ℤ) :
    δ * ModularGroup.T ^ m * δ⁻¹ = unipMat (δ 0 0) (δ 1 0) m := by
  obtain ⟨M, hM⟩ := δ
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rwa [Matrix.det_fin_two] at hM
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.SL2_inv_expl, ModularGroup.coe_T_zpow m]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, unipMat]
  · linear_combination hdet
  · ring
  · ring
  · linear_combination hdet

/-- Powers of a cusp unipotent multiply its integral translation parameter. -/
theorem unipMat_pow (δ : SL(2, ℤ)) (h : ℤ) (n : ℕ) :
    (unipMat (δ 0 0) (δ 1 0) h) ^ n = unipMat (δ 0 0) (δ 1 0) (h * n) := by
  rw [← conj_T_zpow_eq_unipMat, ← conj_T_zpow_eq_unipMat, conj_pow, ← zpow_natCast, ← _root_.zpow_mul]

/-- Integral conjugation transports the original cusp column. -/
theorem inv_mul_unipMat_mul (r δ : SL(2, ℤ)) (m : ℤ) :
    r⁻¹ * unipMat (δ 0 0) (δ 1 0) m * r = unipMat ((r⁻¹ * δ) 0 0) ((r⁻¹ * δ) 1 0) m := by
  rw [← conj_T_zpow_eq_unipMat, ← conj_T_zpow_eq_unipMat]
  group

/-- The level-multiple cusp unipotent lies in the actual principal congruence subgroup. -/
theorem unipMat_mem_Gamma (N : ℕ) (p q : ℤ) : unipMat p q N ∈ Gamma N := by
  rw [Gamma_mem]
  simp only [unipMat_apply_00, unipMat_apply_01, unipMat_apply_10, unipMat_apply_11]
  push_cast
  simp

/-- The first column of an integral determinant-one matrix is primitive. -/
theorem isCoprime_col (δ : SL(2, ℤ)) : IsCoprime (δ 0 0) (δ 1 0) := by
  have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe δ
    rwa [Matrix.det_fin_two] at h
  exact ⟨δ 1 1, -(δ 0 1), by linear_combination hdet⟩

/-- Equal reduced primitive columns give a principal-congruence conjugacy of every cusp translation. -/
theorem exists_conj_of_col_congr (N : ℕ) (σ₁ σ₂ : SL(2, ℤ))
    (h0 : ((σ₁ 0 0 : ℤ) : ZMod N) = σ₂ 0 0) (h1 : ((σ₁ 1 0 : ℤ) : ZMod N) = σ₂ 1 0) :
    ∃ g ∈ Gamma N, ∀ m : ℤ,
      σ₁ * ModularGroup.T ^ m * σ₁⁻¹ = g * (σ₂ * ModularGroup.T ^ m * σ₂⁻¹) * g⁻¹ := by
  set τ : SL(2, ℤ) := σ₂⁻¹ * σ₁ with hτ
  have hdet₂ : σ₂ 0 0 * σ₂ 1 1 - σ₂ 0 1 * σ₂ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe σ₂; rwa [Matrix.det_fin_two] at h
  have hτ00 : τ 0 0 = σ₂ 1 1 * σ₁ 0 0 - σ₂ 0 1 * σ₁ 1 0 := by
    rw [hτ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have hτ10 : τ 1 0 = -(σ₂ 1 0) * σ₁ 0 0 + σ₂ 0 0 * σ₁ 1 0 := by
    rw [hτ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hτdet : τ 0 0 * τ 1 1 - τ 0 1 * τ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe τ; rwa [Matrix.det_fin_two] at h
  have c00 : ((τ 0 0 : ℤ) : ZMod N) = 1 := by
    rw [hτ00]; push_cast; rw [h0, h1]
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₂
    push_cast at this
    linear_combination this
  have c10 : ((τ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [hτ10]; push_cast; rw [h0, h1]; ring
  have c11 : ((τ 1 1 : ℤ) : ZMod N) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hτdet
    push_cast at this
    rw [c00, c10] at this
    linear_combination this
  set W : SL(2, ℤ) := τ * ModularGroup.T ^ (-(τ 0 1)) with hW
  have hWmem : W ∈ Gamma N := by
    have hmul : ∀ i j, (τ * ModularGroup.T ^ (-(τ 0 1)) : SL(2, ℤ)) i j =
        τ i 0 * (ModularGroup.T ^ (-(τ 0 1))) 0 j + τ i 1 * (ModularGroup.T ^ (-(τ 0 1))) 1 j := by
      intro i j
      rw [Matrix.SpecialLinearGroup.coe_mul]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Gamma_mem, hW, hmul, hmul, hmul, hmul, ModularGroup.coe_T_zpow]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero]
    push_cast
    refine ⟨c00, ?_, c10, ?_⟩
    · rw [c00]; ring
    · rw [c10, c11]; ring
  refine ⟨σ₂ * W * σ₂⁻¹, (Gamma_normal N).conj_mem W hWmem σ₂, fun m => ?_⟩
  have hσ₁ : σ₁ = σ₂ * τ := by rw [hτ]; group
  rw [hσ₁, hW]
  group


end Dubon2026.SourceCuspBoundary
