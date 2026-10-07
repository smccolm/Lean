import Dubon2026.RankinStripNormalized

/-! # Polynomial strip growth for the genuine general-level Rankin convolution -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup Set Filter Asymptotics
open scoped Topology

noncomputable section

/-- The actual fixed-strip polynomial and exponential majorant satisfies the growth condition of the strip maximum principle. -/
theorem rankinStrip_exponential_majorant {s : ℂ} (hl : -1 / 8 ≤ s.re) (hr : s.re ≤ 9 / 8) :
    (1 + ‖s‖) ^ 2 * Real.exp (2 * Real.pi * |s.im|) ≤
      16 * Real.exp ((2 + 2 * Real.pi) * Real.exp |s.im|) := by
  have hab : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hnorm : ‖s‖ ≤ 2 + |s.im| := s.norm_le_abs_re_add_abs_im.trans (add_le_add hab le_rfl)
  have he1 : 1 ≤ Real.exp |s.im| := Real.one_le_exp (abs_nonneg _)
  have het : |s.im| ≤ Real.exp |s.im| := by linarith [Real.add_one_le_exp |s.im|]
  have hn : 1 + ‖s‖ ≤ 4 * Real.exp |s.im| := by linarith
  calc
    _ ≤ (4 * Real.exp |s.im|) ^ 2 * Real.exp (2 * Real.pi * |s.im|) := by gcongr
    _ = 16 * ((Real.exp |s.im| * Real.exp |s.im|) * Real.exp (2 * Real.pi * |s.im|)) := by ring
    _ = 16 * Real.exp ((2 + 2 * Real.pi) * |s.im|) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by gcongr

/-- The actual normalized Rankin function has the precise large-height growth input required by Phragmen-Lindelof. -/
theorem rankinStripNormalized_growth {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ c < Real.pi / ((9 / 8 : ℝ) - (-1 / 8)), ∃ B : ℝ,
      rankinStripNormalized f =O[comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (-1 / 8) (9 / 8))]
        (fun s : ℂ => Real.exp (B * Real.exp (c * |s.im|))) := by
  obtain ⟨C, hC, hCb⟩ := exists_rankinConvolutionEntireNumerator_strip_exponential f hk
  refine ⟨1, ?_, 2 + 2 * Real.pi, ?_⟩
  · apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 9 / 8 - (-1 / 8))).mpr
    linarith [Real.pi_gt_three]
  · apply Asymptotics.IsBigO.of_bound (16 * C)
    apply eventually_inf_principal.mpr
    have ht : ∀ᶠ s : ℂ in comap (abs ∘ Complex.im) atTop, 1 ≤ |s.im| :=
      preimage_mem_comap (eventually_ge_atTop (1 : ℝ))
    filter_upwards [ht] with s ht
    intro hs
    have hn := (norm_rankinStripNormalized_le_numerator f hs.1.le).trans (hCb s hs.1.le hs.2.le ht)
    have hb := mul_le_mul_of_nonneg_left (rankinStrip_exponential_majorant hs.1.le hs.2.le) hC.le
    simp only [one_mul, Real.norm_eq_abs, Real.abs_exp]
    calc
      _ ≤ C * (1 + ‖s‖) ^ 2 * Real.exp (2 * Real.pi * |s.im|) := hn
      _ ≤ (16 * C) * Real.exp ((2 + 2 * Real.pi) * Real.exp |s.im|) := by nlinarith [hb]

/-- The actual normalized general-level Rankin function is uniformly bounded on the entire closed contour strip. -/
theorem exists_rankinStripNormalized_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 / 8 ≤ s.re → s.re ≤ 9 / 8 → ‖rankinStripNormalized f s‖ ≤ C := by
  obtain ⟨C, hC, hCb⟩ := exists_rankinStripNormalized_boundary_bound f hk
  refine ⟨C, hC, ?_⟩
  intro s hl hr
  exact PhragmenLindelof.vertical_strip (diffContOnCl_rankinStripNormalized f)
    (rankinStripNormalized_growth f hk) (fun z hz => hCb z (Or.inl hz))
    (fun z hz => hCb z (Or.inr hz)) hl hr

/-- The genuine general-level entire pole numerator has seven-halves polynomial growth throughout the closed strip. -/
theorem exists_rankinConvolutionEntireNumerator_polynomial_strip_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 / 8 ≤ s.re → s.re ≤ 9 / 8 →
      ‖rankinConvolutionEntireNumerator f s‖ ≤ C * ‖s + 2‖ ^ (7 / 2 : ℝ) := by
  obtain ⟨C, hC, hCb⟩ := exists_rankinStripNormalized_bound f hk
  refine ⟨C, hC, ?_⟩
  intro s hl hr
  have hn : 0 < ‖s + 2‖ ^ (7 / 2 : ℝ) := Real.rpow_pos_of_pos
    (lt_of_lt_of_le zero_lt_one (rankinStrip_base_norm_one_le hl)) _
  exact (div_le_iff₀ hn).mp (by simpa only [norm_rankinStripNormalized] using hCb s hl hr)

end
end Dubon2026
