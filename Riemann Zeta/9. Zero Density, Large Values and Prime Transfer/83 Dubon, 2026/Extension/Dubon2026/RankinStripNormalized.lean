import Dubon2026.GeneralRankinBoundary
import Dubon2026.RankinConvolutionExponential
import Mathlib.Analysis.Complex.PhragmenLindelof

/-! # The actual analytic normalization for the Rankin strip maximum principle -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup Set

noncomputable section

/-- The genuine entire Rankin numerator divided by the exact seven-halves contour weight. -/
def rankinStripNormalized {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) : ℂ :=
  rankinConvolutionEntireNumerator f s / (s + 2) ^ ((7 / 2 : ℝ) : ℂ)

/-- The actual normalization is holomorphic throughout the half-plane Re(s)>-2. -/
theorem differentiableAt_rankinStripNormalized {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {s : ℂ} (hs : -2 < s.re) :
    DifferentiableAt ℂ (rankinStripNormalized f) s := by
  have hslit : s + 2 ∈ slitPlane := Or.inl (by norm_num; linarith)
  have hd : DifferentiableAt ℂ (fun z : ℂ => (z + 2) ^ ((7 / 2 : ℝ) : ℂ)) s :=
    (differentiableAt_id.add_const 2).cpow_const hslit
  exact (differentiable_rankinConvolutionEntireNumerator f s).div hd
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero hslit)))

/-- The actual normalization meets the holomorphy and boundary continuity conditions on the closed Rankin strip. -/
theorem diffContOnCl_rankinStripNormalized {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    DiffContOnCl ℂ (rankinStripNormalized f) (Complex.re ⁻¹' Ioo (-1 / 8) (9 / 8)) := by
  apply DifferentiableOn.diffContOnCl
  have hclosed : IsClosed {s : ℂ | -1 / 8 ≤ s.re} := isClosed_le continuous_const Complex.continuous_re
  have hsub : closure (Complex.re ⁻¹' Ioo (-1 / 8) (9 / 8)) ⊆ {s : ℂ | -1 / 8 ≤ s.re} :=
    closure_minimal (fun _ h => h.1.le) hclosed
  intro s hs
  exact (differentiableAt_rankinStripNormalized f (by have := hsub hs; change -1 / 8 ≤ s.re at this; linarith)).differentiableWithinAt

/-- The contour normalization has base norm at least one throughout the actual closed strip. -/
theorem rankinStrip_base_norm_one_le {s : ℂ} (hs : -1 / 8 ≤ s.re) : 1 ≤ ‖s + 2‖ := by
  have hh := Complex.re_le_norm (s + 2)
  norm_num at hh
  linarith

/-- The genuine normalization's modulus is the original numerator divided by the real seven-halves norm power. -/
theorem norm_rankinStripNormalized {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) :
    ‖rankinStripNormalized f s‖ = ‖rankinConvolutionEntireNumerator f s‖ / ‖s + 2‖ ^ (7 / 2 : ℝ) := by
  rw [rankinStripNormalized, norm_div, Complex.norm_cpow_real]

/-- Dividing by the actual contour weight cannot enlarge the numerator on the closed strip. -/
theorem norm_rankinStripNormalized_le_numerator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {s : ℂ} (hs : -1 / 8 ≤ s.re) :
    ‖rankinStripNormalized f s‖ ≤ ‖rankinConvolutionEntireNumerator f s‖ := by
  rw [norm_rankinStripNormalized]
  exact div_le_self (norm_nonneg _) (Real.one_le_rpow (rankinStrip_base_norm_one_le hs) (by norm_num))

/-- Both actual vertical boundaries of the normalized general-level Rankin function are uniformly bounded, including small heights. -/
theorem exists_rankinStripNormalized_boundary_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = -1 / 8 ∨ s.re = 9 / 8 → ‖rankinStripNormalized f s‖ ≤ C := by
  obtain ⟨A, hA, hAb⟩ := exists_general_rankinConvolutionEntireNumerator_left_bound f hk
  obtain ⟨B, hB, hBb⟩ := exists_rankinConvolutionEntireNumerator_right_bound f (by omega)
  have hcompact : IsCompact (Icc (-1 / 8 : ℝ) (9 / 8) ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨D, hD⟩ := hcompact.exists_bound_of_continuousOn (show ContinuousOn (rankinStripNormalized f)
      (Icc (-1 / 8 : ℝ) (9 / 8) ×ℂ Icc (-1 : ℝ) 1) from by
    intro s hs
    exact (differentiableAt_rankinStripNormalized f (by have := hs.1.1; linarith)).continuousAt.continuousWithinAt)
  refine ⟨A + 4 * B + |D| + 1, by positivity, ?_⟩
  intro s hs
  have hslo : -1 / 8 ≤ s.re := by rcases hs with hs | hs <;> norm_num [hs]
  have hn := rankinStrip_base_norm_one_le hslo
  have hnp : 0 < ‖s + 2‖ ^ (7 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  by_cases ht : 1 ≤ |s.im|
  · rcases hs with hs | hs
    · have hi : |s.im| ≤ ‖s + 2‖ := by simpa using Complex.abs_im_le_norm (s + 2)
      have hb : ‖rankinStripNormalized f s‖ ≤ A := by
        rw [norm_rankinStripNormalized, div_le_iff₀ hnp]
        exact (hAb s hs ht).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) hi (by norm_num)) hA.le)
      linarith [abs_nonneg D]
    · have hnshift : 1 + ‖s‖ ≤ 4 * ‖s + 2‖ := by
        have h := norm_sub_le (s + 2) (2 : ℂ)
        norm_num at h
        linarith
      have hb : ‖rankinStripNormalized f s‖ ≤ 4 * B := by
        rw [norm_rankinStripNormalized, div_le_iff₀ hnp]
        calc
          _ ≤ B * (1 + ‖s‖) := hBb s hs
          _ ≤ B * (4 * ‖s + 2‖) := mul_le_mul_of_nonneg_left hnshift hB.le
          _ ≤ (4 * B) * ‖s + 2‖ ^ (7 / 2 : ℝ) := by
            have hh : ‖s + 2‖ ≤ ‖s + 2‖ ^ (7 / 2 : ℝ) := by
              simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn (show (1 : ℝ) ≤ 7 / 2 by norm_num)
            nlinarith
      linarith [abs_nonneg D]
  · have hmem : s ∈ Icc (-1 / 8 : ℝ) (9 / 8) ×ℂ Icc (-1 : ℝ) 1 := by
      refine ⟨⟨hslo, ?_⟩, ?_⟩
      · rcases hs with hs | hs <;> norm_num [hs]
      · have hh := abs_le.mp (le_of_lt (lt_of_not_ge ht))
        exact hh
    have hh := (hD s hmem).trans (le_abs_self D)
    linarith

end
end Dubon2026
