import Dubon2026.SourceSiegelIntegralCoefficients

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> source leading Fourier unit.
The actual cyclotomic phase and its inverse are integral. A finite
geometric-sum identity expresses N/(1-zeta) as an integral polynomial in
zeta, discharging the level-cleared inverse obligation for the nonzero
leading coefficient. No integrality-of-an-inverse premise is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion
noncomputable section
open Complex
open scoped Real

/-- The actual cyclotomic phase in the source Siegel coefficients. -/
def zeta (N : ℕ) (s : ℤ) : ℂ := cexp (2 * π * I * (s : ℂ) / (N : ℂ))

theorem norm_zeta (N : ℕ) (s : ℤ) : ‖zeta N s‖ = 1 := by
  unfold zeta
  rw [show 2 * (π : ℂ) * I * (s : ℂ) / (N : ℂ) = ((2 * π * s / N : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_zeta_inv (N : ℕ) (s : ℤ) : ‖(zeta N s)⁻¹‖ = 1 := by
  rw [norm_inv, norm_zeta, inv_one]

theorem zeta_pow (N : ℕ) (hN : 0 < N) (s : ℤ) : zeta N s ^ N = 1 := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show (N : ℂ) * (2 * π * I * (s : ℂ) / (N : ℂ)) = s * (2 * π * I) by field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I s

theorem isIntegral_zeta (N : ℕ) (hN : 0 < N) (s : ℤ) : IsIntegral ℤ (zeta N s) := by
  refine IsIntegral.of_pow hN ?_
  rw [zeta_pow N hN s]
  exact isIntegral_one

theorem zeta_inv_eq_pow (N : ℕ) (hN : 0 < N) (s : ℤ) : (zeta N s)⁻¹ = zeta N s ^ (N - 1) := by
  have h := zeta_pow N hN s
  have h' : zeta N s ^ (N - 1) * zeta N s = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hN, h]
  exact (eq_inv_of_mul_eq_one_left h').symm

theorem isIntegral_zeta_inv (N : ℕ) (hN : 0 < N) (s : ℤ) : IsIntegral ℤ (zeta N s)⁻¹ := by
  rw [zeta_inv_eq_pow N hN s]
  exact (isIntegral_zeta N hN s).pow _

theorem N_mul_inv_one_sub (N : ℕ) (ζ : ℂ) (hζN : ζ ^ N = 1) (hζ : ζ ≠ 1) :
    (N : ℂ) * (1 - ζ)⁻¹ = ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ζ ^ j := by
  have hne : (1 - ζ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ)
  have hgeom : ∑ k ∈ Finset.range N, ζ ^ k = 0 := by
    have h := mul_geom_sum ζ N
    rw [hζN, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hζ)
  have key : (1 - ζ) * ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ζ ^ j = N := by
    rw [Finset.mul_sum]
    have hk : ∀ k : ℕ, (1 - ζ) * ∑ j ∈ Finset.range (k + 1), ζ ^ j = 1 - ζ ^ (k + 1) := fun k => by
      have h := mul_geom_sum ζ (k + 1)
      linear_combination -h
    simp_rw [hk, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have : ∑ k ∈ Finset.range N, ζ ^ (k + 1) = ζ * ∑ k ∈ Finset.range N, ζ ^ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, hgeom, mul_zero, sub_zero]
  calc (N : ℂ) * (1 - ζ)⁻¹ = ((1 - ζ) * ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ζ ^ j) *
        (1 - ζ)⁻¹ := by rw [key]
    _ = _ := by field_simp

theorem isIntegral_N_mul_inv_one_sub (N : ℕ) (ζ : ℂ) (hζi : IsIntegral ℤ ζ) (hζN : ζ ^ N = 1)
    (hζ : ζ ≠ 1) : IsIntegral ℤ ((N : ℂ) * (1 - ζ)⁻¹) := by
  rw [N_mul_inv_one_sub N ζ hζN hζ]
  exact IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun j _ => hζi.pow j

theorem zeta_ne_one (N : ℕ) (hN : 0 < N) (s : ℤ) (hs : ¬ (N : ℤ) ∣ s) : zeta N s ≠ 1 := by
  intro h
  unfold zeta at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [div_eq_iff hN'] at hn
  have h2 : (2 * π * I : ℂ) * (s : ℂ) = (2 * π * I) * ((n : ℂ) * (N : ℂ)) := by
    linear_combination hn
  have h3 : (s : ℂ) = (n : ℂ) * (N : ℂ) := mul_left_cancel₀ hπ h2
  have h4 : ((s : ℤ) : ℂ) = ((n * N : ℤ) : ℂ) := by push_cast; exact h3
  exact hs (Dvd.intro_left n (Int.cast_injective h4).symm)


end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion
