import Dubon2026.RankinConvolutionReflection
import Dubon2026.GammaRieszHorizontal

/-! # Actual convergence-boundary and reflected-boundary Rankin bounds -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The actual Rankin coefficient series is uniformly bounded throughout every closed convergence half-plane. -/
theorem exists_rankinConvolution_LSeries_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {σ : ℝ} (hσ : 1 < σ) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, σ ≤ s.re → ‖LSeries (rankinConvolutionCoefficients f) s‖ ≤ B := by
  have hsum := (rankinConvolution_lseriesSummable f hk (s := (σ : ℂ)) hσ).norm
  let B : ℝ := ∑' n, ‖LSeries.term (rankinConvolutionCoefficients f) (σ : ℂ) n‖
  have hB : 0 ≤ B := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨B + 1, by linarith, ?_⟩
  intro s hs
  exact (tsum_of_norm_bounded hsum.hasSum
    (fun n => LSeries.norm_term_le_of_re_le_re _ (s := (σ : ℂ)) hs n)).trans (by linarith)

/-- The actual entire pole numerator has linear growth on the original convergence boundary. -/
theorem exists_rankinConvolutionEntireNumerator_right_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, s.re = 9 / 8 →
      ‖rankinConvolutionEntireNumerator f s‖ ≤ B * (1 + ‖s‖) := by
  obtain ⟨B, hB, hbound⟩ := exists_rankinConvolution_LSeries_bound f hk (show (1 : ℝ) < 9 / 8 by norm_num)
  refine ⟨B, hB, ?_⟩
  intro s hs
  rw [rankinConvolutionEntireNumerator_eq_series f hk (by rw [hs]; norm_num), norm_mul]
  have hn : ‖s - 1‖ ≤ 1 + ‖s‖ := by
    have hh := norm_sub_le s 1
    simpa only [norm_one, add_comm] using hh
  calc
    _ ≤ (1 + ‖s‖) * B := mul_le_mul hn (hbound s hs.ge) (norm_nonneg _) (by positivity)
    _ = _ := mul_comm _ _

/-- On the left Rankin line the actual Riesz Gamma symbol has the sharp inverse-square-root amplitude at both heights. -/
theorem norm_gammaRieszSymbol_two_left_le {k : ℝ} (hk : 2 ≤ k) {s : ℂ}
    (hs : s.re = -1 / 8) (ht : 1 ≤ |s.im|) :
    ‖gammaRieszSymbol k 2 s‖ ≤ gammaRieszStripConstant k * |s.im| ^ (-(1 / 2 : ℝ)) := by
  have h := norm_gammaRieszMellinFunction_le_abs_height (k := k) (r := 2) (β := -1 / 8)
    (x := 1) (t := s.im) hk (by norm_num) le_rfl (by norm_num)
    (by norm_num [gammaRieszLine]) (by norm_num) ht
  have he : gammaVerticalPoint (-1 / 8) s.im = s := by
    apply Complex.ext <;> simp [gammaVerticalPoint, hs]
  simpa only [gammaRieszMellinFunction, ofReal_one, one_cpow, one_mul,
    Real.log_one, abs_zero, Real.exp_zero, he] using h

/-- Four actual linear contour factors cost at most a fixed fourth power of the height on the left boundary. -/
theorem norm_rankin_left_factors_le {s : ℂ} (hs : s.re = -1 / 8) (ht : 1 ≤ |s.im|) :
    ‖(s - 1) * (s * (s + 1) * (s + 2))‖ ≤ 81 * |s.im| ^ 4 := by
  have h0 : ‖s‖ ≤ 3 * |s.im| := by
    have h := s.norm_le_abs_re_add_abs_im
    rw [hs] at h
    norm_num at h
    linarith
  have hm : ‖s - 1‖ ≤ 3 * |s.im| := by
    have h := (s - 1).norm_le_abs_re_add_abs_im
    simp only [sub_re, sub_im, one_re, one_im, sub_zero, hs] at h
    norm_num at h
    linarith
  have h1 : ‖s + 1‖ ≤ 3 * |s.im| := by
    have h := (s + 1).norm_le_abs_re_add_abs_im
    simp only [add_re, add_im, one_re, one_im, add_zero, hs] at h
    norm_num at h
    linarith
  have h2 : ‖s + 2‖ ≤ 3 * |s.im| := by
    have h := (s + 2).norm_le_abs_re_add_abs_im
    norm_num [hs] at h
    linarith
  simp only [norm_mul]
  calc
    _ ≤ (3 * |s.im|) * ((3 * |s.im|) * (3 * |s.im|) * (3 * |s.im|)) := by gcongr
    _ = _ := by ring

/-- The genuine full-level pole numerator has the precise seven-halves reflected boundary growth. -/
theorem exists_rankinConvolutionEntireNumerator_left_bound {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = -1 / 8 → 1 ≤ |s.im| →
      ‖rankinConvolutionEntireNumerator f s‖ ≤ C * |s.im| ^ (7 / 2 : ℝ) := by
  have hk0 : 0 ≤ k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨B, hB, hBb⟩ := exists_rankinConvolution_LSeries_bound f hk0 (show (1 : ℝ) < 9 / 8 by norm_num)
  let A : ℝ := 4 * Real.pi ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  let P : ℝ := A ^ (-(5 / 4 : ℝ))
  have hP : 0 < P := Real.rpow_pos_of_pos hA _
  let G : ℝ := gammaRieszStripConstant k
  have hG : 0 < G := Real.exp_pos _
  refine ⟨81 * P * G * B, by positivity, ?_⟩
  intro s hs ht
  have hs0 : s ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro he; rw [he] at hs; norm_num at hs
  have hp1 : s + 1 ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num [hs] at hh
  have hp2 : s + 2 ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num [hs] at hh
  have href := (div_eq_iff (mul_ne_zero (mul_ne_zero hs0 hp1) hp2)).mp
    (rankinConvolution_riesz_reflection f hk0 (by rw [hs]; norm_num) (by rw [hs]; norm_num))
  have hN : rankinConvolutionEntireNumerator f s =
      ((s - 1) * (s * (s + 1) * (s + 2))) *
        ((4 * Real.pi ^ 2 : ℂ) ^ (2 * s - 1) * gammaRieszSymbol (k : ℝ) 2 s *
          LSeries (rankinConvolutionCoefficients f) (1 - s)) := by
    rw [rankinConvolutionGlobalContinuation] at href
    have hh := (div_eq_iff (sub_ne_zero.mpr hs1)).mp href
    rw [hh]
    ring
  have hpower : ‖(4 * Real.pi ^ 2 : ℂ) ^ (2 * s - 1)‖ = P := by
    have hh := Complex.norm_cpow_eq_rpow_re_of_pos hA (2 * s - 1)
    norm_num [A, hs] at hh
    exact hh
  have hseries : ‖LSeries (rankinConvolutionCoefficients f) (1 - s)‖ ≤ B :=
    hBb _ (by simp only [sub_re, one_re, hs]; norm_num)
  have hg := norm_gammaRieszSymbol_two_left_le hkR hs ht
  have hR : ‖(4 * Real.pi ^ 2 : ℂ) ^ (2 * s - 1) * gammaRieszSymbol (k : ℝ) 2 s *
      LSeries (rankinConvolutionCoefficients f) (1 - s)‖ ≤
      P * (G * |s.im| ^ (-(1 / 2 : ℝ))) * B := by
    simp only [norm_mul, hpower]
    gcongr
  rw [hN, norm_mul]
  calc
    _ ≤ (81 * |s.im| ^ 4) * (P * (G * |s.im| ^ (-(1 / 2 : ℝ))) * B) :=
      mul_le_mul (norm_rankin_left_factors_le hs ht) hR (norm_nonneg _) (by positivity)
    _ = (81 * P * G * B) * (|s.im| ^ (4 : ℝ) * |s.im| ^ (-(1 / 2 : ℝ))) := by
      norm_num only [Real.rpow_ofNat]
      ring
    _ = _ := by rw [← Real.rpow_add (by linarith : 0 < |s.im|)]; norm_num

end
end Dubon2026
