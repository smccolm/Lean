import Dubon2026.CuspRankinRegular
import Dubon2026.CuspNormalizedEnergy
import GafniTao.WienerSource

/-! # The actual normalized cusp mean-square limit from the proved Rankin pole -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Filter Asymptotics
open scoped Topology

noncomputable section

/-- The range convention in the imported Tauberian theorem agrees exactly with the actual positive-index cusp square sum after one shift. -/
theorem cusp_square_cumsum_succ {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (N : ℕ) :
    cumsum (fun n => ‖normalizedCuspCoefficients f n‖ ^ 2) (N + 1) =
      ∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2 := by
  have he : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [cumsum, he, Finset.sum_insert (by simp)]
  simp [normalizedCuspCoefficients, shiftedCoefficients, cuspCoefficients_zero]

/-- The actual normalized coefficients satisfy the linear sum bound required by the existing cleaned Wiener theorem. -/
theorem cusp_square_cheby {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    cheby (fun n => ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨B, hB, hb⟩ := exists_normalized_cusp_square_upper f hk
  refine ⟨B, fun N => ?_⟩
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_sq]
  cases N with
  | zero => simp
  | succ N =>
    rw [cusp_square_cumsum_succ]
    exact (hb N).trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast Nat.le_succ N) hB.le)

/-- The genuine normalized cusp square coefficients satisfy Wiener-Ikehara with their proved Petersson residue. -/
theorem tendsto_cusp_square_cumsum_div {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    Tendsto (fun N : ℕ => cumsum (fun n => ‖normalizedCuspCoefficients f n‖ ^ 2) N / N)
      atTop (𝓝 (cuspRankinResidue f)) := by
  apply WienerIkeharaTheorem' (G := cuspRankinRegular f)
  · exact fun n => sq_nonneg _
  · intro σ hσ
    simpa only [← nterm_eq_norm_term] using
      (normalized_cusp_square_lseries_summable f hk.le (s := (σ : ℂ)) hσ).norm
  · exact cusp_square_cheby f hk
  · exact continuousOn_cuspRankinRegular f hk
  · exact fun s hs => cuspRankinRegular_eq_series_sub_pole f hk hs

/-- The actual positive-index normalized mean-square sum tends to its true Petersson residue. This asserts the leading asymptotic, not the sharper x^(3/5) error. -/
theorem tendsto_cusp_square_mean {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2) / N)
      atTop (𝓝 (cuspRankinResidue f)) := by
  have hm := (tendsto_cusp_square_cumsum_div f hk).comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (N : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [inv_div, inv_one] using
      (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (1 : ℝ)).inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)
  have hp := hm.mul hr
  simp only [mul_one] at hp
  apply hp.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
  dsimp only [Function.comp_def]
  rw [cusp_square_cumsum_succ, Nat.cast_add, Nat.cast_one]
  field_simp [hN0, hN1]

/-- The proved cusp mean holds at every real cutoff, with the literal floor-indexed sum. -/
theorem tendsto_cusp_squareSummatory_div {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    Tendsto (fun x : ℝ => squareSummatory (normalizedCuspCoefficients f) x / x)
      atTop (𝓝 (cuspRankinResidue f)) := by
  have hh := ((tendsto_cusp_square_mean f hk).comp
    (tendsto_nat_floor_atTop (α := ℝ))).mul (tendsto_nat_floor_div_atTop (R := ℝ))
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hn : (⌊x⌋₊ : ℝ) ≠ 0 := by
    exact_mod_cast (show ⌊x⌋₊ ≠ 0 by have := Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hx); omega)
  dsimp only [Function.comp_def, squareSummatory]
  exact div_mul_div_cancel₀ hn

/-- The actual Rankin main term has a proved o(x) remainder; the source's sharper
x^(3/5) remainder is a separate quantitative obligation. -/
theorem cusp_squareSummatory_sub_main_isLittleO {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    (fun x : ℝ => squareSummatory (normalizedCuspCoefficients f) x - cuspRankinResidue f * x)
      =o[atTop] (fun x : ℝ => x) := by
  apply (isLittleO_iff_tendsto' (eventually_gt_atTop (0 : ℝ) |>.mono
    (fun x hx h => False.elim (hx.ne' h)))).mpr
  have hh := (tendsto_cusp_squareSummatory_div f hk).sub_const (cuspRankinResidue f)
  simp only [sub_self] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [sub_div, mul_div_cancel_right₀ _ hx.ne']

end
end Dubon2026
