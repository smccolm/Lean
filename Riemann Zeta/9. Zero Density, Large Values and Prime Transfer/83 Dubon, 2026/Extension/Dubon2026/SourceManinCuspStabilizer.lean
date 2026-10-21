import Dubon2026.SourceManinCuspSpace
import Dubon2026.SourceCuspBoundaryValues

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual Galois association -> original parabolic Hecke
realization -> reverse period dimension inequality -> actual cusp potentials
and finite Manin relations. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_Period_six_mul_finrank_parabolicHoms_add_le_index.lean
and Definitions/Def_ModularCurve_CuspSpace.lean. The target is the existing
original complex parabolic character space; no new cohomology model or
dimension assumption is introduced.
-/
namespace Dubon2026.SourceManin
noncomputable section
open Matrix Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup OnePoint
open scoped MatrixGroups

theorem smul_infty_eq_iff (γ : SL(2, ℤ)) :
    mapGL ℚ γ • (∞ : OnePoint ℚ) = ∞ ↔ γ 1 0 = 0 := by
  rw [OnePoint.smul_infty_eq_self_iff]
  simp

theorem trace_sq_of_lower_left (γ : SL(2, ℤ)) (h : γ 1 0 = 0) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  have hdet := Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
  rw [γ.det_coe, h, mul_zero, sub_zero] at hdet
  rw [Matrix.trace_fin_two]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;> norm_num

theorem trace_conj (σ δ : SL(2, ℤ)) :
    ((σ⁻¹ * δ * σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      (δ : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [coe_mul, coe_mul, Matrix.trace_mul_cycle, ← coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mul]

theorem neg_one_lower : (-1 : SL(2, ℤ)) 1 0 = 0 := by simp

theorem T_inv_lower : (T⁻¹ : SL(2, ℤ)) 1 0 = 0 := by rw [coe_T_inv]; rfl

theorem T_lower : (T : SL(2, ℤ)) 1 0 = 0 := by rw [coe_T]; rfl

theorem S_inv_eq : (S : SL(2, ℤ))⁻¹ = S * (-1) :=
  inv_eq_of_mul_eq_one_right (by decide)

theorem ST_inv_mul_S : (S * T : SL(2, ℤ))⁻¹ * S = T⁻¹ := by group

theorem ST_cube : (S * T : SL(2, ℤ)) * (S * T) * (S * T) = -1 := by decide

theorem ST_inv_mul_ST_inv : (S * T : SL(2, ℤ))⁻¹ * (S * T)⁻¹ = S * T * (-1) := by
  calc ((S * T : SL(2, ℤ))⁻¹ * (S * T)⁻¹)
      = (S * T) * ((S * T) * (S * T) * (S * T))⁻¹ := by group
    _ = S * T * (-1) := by rw [ST_cube]; simp

theorem neg_one_mem_Gamma0 (N : ℕ) : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by simp [Gamma0_mem]

variable (Γ : Subgroup SL(2, ℤ))

open Classical in

/-- Extend an actual subgroup character by zero for evaluating chosen integral lifts. -/
noncomputable def Phi (φ : Additive Γ →+ ℂ) (g : SL(2, ℤ)) : ℂ :=
  if h : g ∈ Γ then φ (Additive.ofMul ⟨g, h⟩) else 0

theorem Phi_of_mem (φ : Additive Γ →+ ℂ) {g : SL(2, ℤ)} (h : g ∈ Γ) :
    Phi Γ φ g = φ (Additive.ofMul ⟨g, h⟩) := dif_pos h

theorem Phi_mul (φ : Additive Γ →+ ℂ) {g h : SL(2, ℤ)} (hg : g ∈ Γ) (hh : h ∈ Γ) :
    Phi Γ φ (g * h) = Phi Γ φ g + Phi Γ φ h := by
  rw [Phi_of_mem Γ φ (mul_mem hg hh), Phi_of_mem Γ φ hg, Phi_of_mem Γ φ hh, ← map_add]
  rfl

theorem Phi_one (φ : Additive Γ →+ ℂ) : Phi Γ φ 1 = 0 := by
  rw [Phi_of_mem Γ φ (one_mem Γ)]
  exact map_zero φ

theorem Phi_inv (φ : Additive Γ →+ ℂ) {g : SL(2, ℤ)} (hg : g ∈ Γ) :
    Phi Γ φ g⁻¹ = -Phi Γ φ g := by
  have h := Phi_mul Γ φ (inv_mem hg) hg
  rw [inv_mul_cancel, Phi_one] at h
  linear_combination -h

theorem Phi_add (φ ψ : Additive Γ →+ ℂ) (g : SL(2, ℤ)) :
    Phi Γ (φ + ψ) g = Phi Γ φ g + Phi Γ ψ g := by
  unfold Phi
  split_ifs <;> simp

theorem Phi_smul (c : ℂ) (φ : Additive Γ →+ ℂ) (g : SL(2, ℤ)) :
    Phi Γ (c • φ) g = c * Phi Γ φ g := by
  unfold Phi
  split_ifs <;> simp

theorem Phi_parabolic {φ : Additive Γ →+ ℂ} (hφ : ∀ γ : Γ, γ.val.val.trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0) {g : SL(2, ℤ)} (hg : g ∈ Γ)
    (htr : (g : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) : Phi Γ φ g = 0 := by
  rw [Phi_of_mem Γ φ hg]
  exact hφ ⟨g, hg⟩ htr


end
end Dubon2026.SourceManin
