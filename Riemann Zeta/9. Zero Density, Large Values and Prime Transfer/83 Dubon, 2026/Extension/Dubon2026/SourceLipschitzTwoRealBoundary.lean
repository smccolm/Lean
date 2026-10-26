import Dubon2026.SourceLipschitzTwo

/-! DUB-17/18 -> higher symmetric-power continuation -> arithmetic
automorphy -> original all-weight association -> original finite Gamma1
character realization -> Picard/H1 and diamond comparison -> differential
realization -> rational Fourier structure -> actual Fricke expansions.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0).
Native Lipschitz summation and Weierstrass absolute summability are reused.
No external proof module or toolchain is imported. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

open Metric Set Filter Topology in

theorem lipschitz_two_closed {x : ℂ} (hx : x ∈ Complex.integerComplement) :
    ∑' n : ℤ, 1 / (x + n) ^ 2 =
      (2 * π * I) ^ 2 * (cexp (2 * π * I * x) / (1 - cexp (2 * π * I * x)) ^ 2) := by
  rcases lt_trichotomy x.im 0 with h | h | h
  · exact lipschitz_two_closed_of_im_neg h
  swap
  · exact lipschitz_two_closed_of_im_pos h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Complex.isOpen_compl_range_intCast x hx
  set U : Set ℂ := ball x (ε / 2) with hUdef
  have hUsub : U ⊆ Complex.integerComplement :=
    (ball_subset_ball (half_le_self hε.le)).trans hball

  have hsep : ∀ y ∈ U, ∀ n : ℤ, ε / 2 ≤ ‖y + n‖ := by
    intro y hy n
    by_contra! hlt
    have hmem : ((-n : ℤ) : ℂ) ∈ ball x ε := by
      rw [mem_ball, dist_comm, dist_eq_norm]
      calc ‖x - ((-n : ℤ) : ℂ)‖ = ‖(x - y) + (y + n)‖ := by push_cast; ring_nf
        _ ≤ ‖x - y‖ + ‖y + n‖ := norm_add_le _ _
        _ < ε / 2 + ε / 2 := by
            gcongr
            rw [← dist_eq_norm, dist_comm]; exact hy
        _ = ε := by ring
    exact hball hmem ⟨-n, rfl⟩
  have hne : ∀ y ∈ U, ∀ n : ℤ, y + n ≠ 0 := fun y hy n h0 ↦ by
    have := hsep y hy n
    rw [h0, norm_zero] at this
    linarith
  have hnormU : ∀ y ∈ U, ‖y‖ ≤ ‖x‖ + ε / 2 := by
    intro y hy
    have : ‖y - x‖ < ε / 2 := by rw [← dist_eq_norm]; exact hy
    calc ‖y‖ = ‖x + (y - x)‖ := by ring_nf
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ ‖x‖ + ε / 2 := by linarith
  set R : ℝ := ‖x‖ + ε / 2 with hRdef
  set K : ℕ := ⌈2 * R⌉₊ with hKdef

  set u : ℤ → ℝ := fun n ↦
    (if n ∈ Finset.Icc (-(K : ℤ)) K then 4 / ε ^ 2 else 0) + 4 * (1 / (n : ℝ) ^ 2) with hudef
  have hu : Summable u := by
    refine Summable.add ?_ ((summable_one_div_int_pow.mpr one_lt_two).mul_left 4)
    exact summable_of_ne_finset_zero (s := Finset.Icc (-(K : ℤ)) K) (by intro b hb; simp [hb])
  have hbound : ∀ (n : ℤ) (y : ℂ), y ∈ U → ‖1 / (y + n) ^ 2‖ ≤ u n := by
    intro n y hy
    have hpos : 0 < ‖y + n‖ := norm_pos_iff.mpr (hne y hy n)
    rw [norm_div, norm_one, norm_pow]
    by_cases hn : n ∈ Finset.Icc (-(K : ℤ)) K
    · simp only [hudef, hn, if_true]
      have h1 : 1 / ‖y + ↑n‖ ^ 2 ≤ 4 / ε ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        nlinarith [hsep y hy n, norm_nonneg (y + n)]
      have h2 : (0 : ℝ) ≤ 4 * (1 / (n : ℝ) ^ 2) := by positivity
      linarith
    · simp only [hudef, hn, if_false, zero_add]

      have hnK : (K : ℝ) < |(n : ℝ)| := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        rw [← Int.cast_abs]
        rcases hn with hn | hn
        · have : (K : ℤ) < |n| := by rw [abs_of_neg (by omega)]; omega
          exact_mod_cast this
        · have : (K : ℤ) < |n| := lt_of_lt_of_le hn (le_abs_self n)
          exact_mod_cast this
      have hR2 : 2 * R ≤ K := Nat.le_ceil _
      have hyR : ‖y‖ ≤ R := hnormU y hy
      have hlow : |(n : ℝ)| / 2 ≤ ‖y + n‖ := by
        have : |(n : ℝ)| ≤ ‖y + n‖ + ‖y‖ := by
          calc |(n : ℝ)| = ‖((n : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
            _ = ‖(y + n) - y‖ := by push_cast; ring_nf
            _ ≤ ‖y + n‖ + ‖y‖ := norm_sub_le _ _
        linarith
      have hnpos : 0 < |(n : ℝ)| := by linarith [Nat.cast_nonneg (α := ℝ) K]
      rw [show (4 : ℝ) * (1 / (n : ℝ) ^ 2) = 1 / (|(n : ℝ)| / 2) ^ 2 by
        rw [div_pow, sq_abs]; field_simp; ring]
      exact one_div_le_one_div_of_le (by positivity) (by gcongr)
  have hF : DifferentiableOn ℂ (fun y : ℂ ↦ ∑' n : ℤ, 1 / (y + n) ^ 2) U := by
    refine differentiableOn_tsum_of_summable_norm hu (fun n ↦ ?_) isOpen_ball hbound
    exact DifferentiableOn.div (by fun_prop) (by fun_prop) fun y hy ↦ pow_ne_zero _ (hne y hy n)
  have hG : DifferentiableOn ℂ
      (fun y : ℂ ↦ (2 * π * I) ^ 2 * (cexp (2 * π * I * y) / (1 - cexp (2 * π * I * y)) ^ 2))
      U := by
    refine DifferentiableOn.mul (by fun_prop) (DifferentiableOn.div (by fun_prop) (by fun_prop) ?_)
    intro y hy
    exact pow_ne_zero _ (sub_ne_zero.mpr (cexp_two_pi_I_mul_ne_one (hUsub hy)).symm)

  set z₀ : ℂ := x + (ε / 4 : ℝ) * I with hz₀def
  have hz₀U : z₀ ∈ U := by
    rw [hUdef, mem_ball, dist_eq_norm, hz₀def, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hz₀im : 0 < z₀.im := by simp [hz₀def, h, hε]
  have hfg : (fun y : ℂ ↦ ∑' n : ℤ, 1 / (y + n) ^ 2) =ᶠ[𝓝 z₀]
      (fun y : ℂ ↦ (2 * π * I) ^ 2 * (cexp (2 * π * I * y) / (1 - cexp (2 * π * I * y)) ^ 2)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz₀im] with y hy
    exact lipschitz_two_closed_of_im_pos hy
  exact (hF.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd isOpen_ball) (convex_ball x _).isPreconnected hz₀U hfg
    (mem_ball_self (half_pos hε))


end
end Dubon2026.SourceFricke
