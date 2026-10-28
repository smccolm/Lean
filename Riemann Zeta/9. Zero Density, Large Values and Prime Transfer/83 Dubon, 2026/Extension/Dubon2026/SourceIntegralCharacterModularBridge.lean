import Dubon2026.SourceIntegralCharacterModularFacts

/-! DUB-17/18 -> original all-weight association -> Gamma1 Picard/H1
-> Abel-Jacobi -> unitary multiplier logarithms -> integral parabolic-character
lifting. Adapted from the Apache-2.0 scope-796 primary at revision
6e837e75355538c7f80bab5b956861e86c4eacc2. Reuse the repository
SourceParabolic.classification and the audited actual projective free-product
equivalence. The theorem uses literal squared-trace-four vanishing, all finite
indices and all natural moduli, including zero. It assumes no lifting theorem. -/
namespace Dubon2026.SourceIntegralCharacterLift
noncomputable section
open Subgroup
open scoped MatrixGroups
section Bridge

open Matrix.SpecialLinearGroup ModularGroup

variable (ρ : SL(2, ℤ) →* G23) (hker : ∀ z, ρ z = 1 ↔ z ∈ Subgroup.center SL(2, ℤ))
  (hT : ρ T = tP)

include hker

theorem rho_neg (γ : SL(2, ℤ)) : ρ (-γ) = ρ γ := by
  rw [← neg_one_mul, map_mul, (hker _).mpr neg_one_mem_center, one_mul]

theorem eq_or_eq_neg_of_rho_eq {γ δ : SL(2, ℤ)} (h : ρ γ = ρ δ) : γ = δ ∨ γ = -δ := by
  have h1 : ρ (δ⁻¹ * γ) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  rcases eq_one_or_eq_neg_one_of_mem_center ((hker _).mp h1) with h2 | h2
  · left; exact (inv_mul_eq_one.mp h2).symm
  · right
    rw [inv_mul_eq_iff_eq_mul] at h2
    rw [h2, mul_neg_one]

theorem isOfFinOrder_of_rho {γ : SL(2, ℤ)} (h : IsOfFinOrder (ρ γ)) : IsOfFinOrder γ := by
  obtain ⟨n, hn, hpow⟩ := h.exists_pow_eq_one
  rw [← map_pow] at hpow
  rcases eq_one_or_eq_neg_one_of_mem_center ((hker _).mp hpow) with h2 | h2
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, h2⟩
  · refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n * 2, by omega, ?_⟩
    rw [pow_mul, h2, sq, neg_mul_neg, one_mul]

theorem isOfFinOrder_of_rho_eq_conj_of {γ : SL(2, ℤ)} {i : Fin 2} (x : M23 i) (g : G23)
    (h : ρ γ = g * Monoid.CoprodI.of (M := M23) x * g⁻¹) : IsOfFinOrder γ := by
  apply isOfFinOrder_of_rho ρ hker
  obtain ⟨n, hn, hxn⟩ := (isOfFinOrder_of_finite x).exists_pow_eq_one
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  rw [h, conj_pow, ← map_pow, hxn, map_one, mul_one, mul_inv_cancel]

include hT

theorem exists_rho_eq_conj_tP_zpow {γ : SL(2, ℤ)} (h : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    ∃ (g : G23) (k : ℤ), ρ γ = g * tP ^ k * g⁻¹ := by
  obtain ⟨ε, δ, k, hε, hγ⟩ := SourceParabolic.classification γ h
  refine ⟨ρ δ, k, ?_⟩
  have hε0 : ρ ε = 1 := by
    rcases hε with rfl | rfl
    · exact map_one ρ
    · exact (hker _).mpr neg_one_mem_center
  rw [hγ, map_mul, hε0, one_mul, map_mul, map_mul, map_zpow, map_inv, hT]

theorem trace_sq_of_rho_eq_conj_tP_zpow (hsurj : Function.Surjective ρ) {γ : SL(2, ℤ)} {g : G23} {k : ℤ}
    (h : ρ γ = g * tP ^ k * g⁻¹) : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  obtain ⟨δ, rfl⟩ := hsurj g
  have h' : ρ γ = ρ (δ * T ^ k * δ⁻¹) := by
    rw [h, map_mul, map_mul, map_zpow, map_inv, hT]
  rcases eq_or_eq_neg_of_rho_eq ρ hker h' with h2 | h2
  · rw [h2, trace_conj_T_zpow]; norm_num
  · have : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = -2 := by
      rw [h2, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, trace_conj_T_zpow]
    rw [this]; norm_num

end Bridge

end
end Dubon2026.SourceIntegralCharacterLift
