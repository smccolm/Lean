import TaoTrudgianYang2025.SargosSecondDerivativeScale

/-! The actual unweighted quartic prefix, with a proved radians conversion. -/

noncomputable section

open GafniTao Set RiemannZeta.GuthMaynard
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosQuarticRadianSample (N : ℕ) (α γ x : ℝ) : ℝ :=
  2*Real.pi*(((N : ℝ)+x+1)^2*α+((N : ℝ)+x+1)^4*γ)

theorem sargosQuarticPrefix_eq_radian_sum (N H : ℕ) (α γ : ℝ) :
    sargosQuarticPrefix N H (fun _ => 1) α γ =
      ∑ j ∈ Finset.range H, unitaryPhase (sargosQuarticRadianSample N α γ j) := by
  rw [sargosQuarticPrefix,sargos_sum_Ioc_eq_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_mul]
  unfold fordAdditiveCharacter unitaryPhase sargosQuarticRadianSample
  congr 1
  push_cast
  ring

theorem sargosQuarticRadianSample_second_difference {N L : ℕ}
    (hN : 1 ≤ N) (hL : L+1 ≤ N) {α γ : ℝ}
    (hγ : |γ| ≤ 1/(N : ℝ)^3) (hα : 128/(N : ℝ) ≤ α)
    (j : ℕ) (hj : j < L) :
    2*Real.pi*α ≤
      (sargosQuarticRadianSample N α γ (j+2)-sargosQuarticRadianSample N α γ (j+1))-
        (sargosQuarticRadianSample N α γ (j+1)-sargosQuarticRadianSample N α γ j) ∧
    (sargosQuarticRadianSample N α γ (j+2)-sargosQuarticRadianSample N α γ (j+1))-
        (sargosQuarticRadianSample N α γ (j+1)-sargosQuarticRadianSample N α γ j) ≤
      6*Real.pi*α := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hjN : (j : ℝ)+1 ≤ N := by exact_mod_cast (by omega : j+1 ≤ N)
  have hx : (N : ℝ)+j+1 ∈ Icc (N : ℝ) (2*N) := by
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have he :
      (sargosQuarticRadianSample N α γ (j+2)-sargosQuarticRadianSample N α γ (j+1))-
        (sargosQuarticRadianSample N α γ (j+1)-sargosQuarticRadianSample N α γ j) =
      2*Real.pi*(2*α+(12*((N : ℝ)+j+1)^2+24*((N : ℝ)+j+1)+14)*γ) := by
    unfold sargosQuarticRadianSample
    ring
  rw [he]
  have hc := sargos_quartic_curvature hNr hx hγ hα
  constructor
  · exact mul_le_mul_of_nonneg_left hc.1 (by positivity)
  · calc
      _ ≤ 2*Real.pi*(3*α) := mul_le_mul_of_nonneg_left hc.2 (by positivity)
      _ = _ := by ring

theorem norm_sargosQuarticPrefix_le_curvature {N H : ℕ}
    (hN : 1 ≤ N) (hH : H ≤ N) {α γ : ℝ}
    (hγ : |γ| ≤ 1/(N : ℝ)^3) (hα : 128/(N : ℝ) ≤ α) (hα1 : α ≤ 1) :
    ‖sargosQuarticPrefix N H (fun _ => 1) α γ‖ ≤ 64*(N : ℝ)*Real.sqrt α := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hαp : 0 < α := lt_of_lt_of_le (by positivity) hα
  have hscale : 1 ≤ (N : ℝ)*α := by
    have h := (div_le_iff₀ hNp).1 hα
    nlinarith
  cases H with
  | zero =>
      rw [sargosQuarticPrefix_zero,norm_zero]
      positivity
  | succ L =>
      rw [sargosQuarticPrefix_eq_radian_sum]
      have hb := vanDerCorput_second_derivative
        (fun j => sargosQuarticRadianSample N α γ j) L
        (2*Real.pi*α) (6*Real.pi*α) (Real.sqrt α)
        (by positivity) (by positivity)
        (fun j hj => by simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using
          (sargosQuarticRadianSample_second_difference hN hH hγ hα j hj).1)
        (fun j hj => by simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using
          (sargosQuarticRadianSample_second_difference hN hH hγ hα j hj).2)
      exact hb.trans (sargos_second_derivative_scale hNp.le
        (by exact_mod_cast (by omega : L ≤ N)) hαp hα1 hscale)

theorem sargosQuarticPrefixMaximum_le_curvature {N : ℕ}
    (hN : 1 ≤ N) {α γ : ℝ}
    (hγ : |γ| ≤ 1/(N : ℝ)^3) (hα : 128/(N : ℝ) ≤ α) (hα1 : α ≤ 1) :
    sargosQuarticPrefixMaximum N (fun _ => 1) α γ ≤ 64*(N : ℝ)*Real.sqrt α := by
  obtain ⟨H,hH,he⟩ := sargosQuarticPrefixMaximum_attained N (fun _ => 1) α γ
  rw [he]
  exact norm_sargosQuarticPrefix_le_curvature hN hH hγ hα hα1

theorem sargosQuarticPrefixMaximum_sq_le_curvature {N : ℕ}
    (hN : 1 ≤ N) {α γ : ℝ}
    (hγ : |γ| ≤ 1/(N : ℝ)^3) (hα : 128/(N : ℝ) ≤ α) (hα1 : α ≤ 1) :
    (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^2 ≤ 4096*(N : ℝ)^2*α := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hαp : 0 < α := lt_of_lt_of_le (by positivity) hα
  calc
    _ ≤ (64*(N : ℝ)*Real.sqrt α)^2 := pow_le_pow_left₀
      (sargosQuarticPrefixMaximum_nonneg N (fun _ => 1) α γ)
      (sargosQuarticPrefixMaximum_le_curvature hN hγ hα hα1) 2
    _ = 4096*(N : ℝ)^2*(Real.sqrt α)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt hαp.le]

end TaoTrudgianYang2025
