import DongWangWangZhang2026.DiskZeroGeometry

/-!
# Transfer from the actual weighted zero sum to an open disk

The finite near sum and the absolutely convergent far sum partition the
full multiplicity index. Boundary zeros belong to the far sum.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Set
open scoped Classical

/-- The actual weighted zero sum is bounded by the disk count and the farther resolvent. -/
theorem weighted_zero_sum_le_disk_and_resolvent {a l η φ : ℝ} (hl : 0 < l)
    (hla : l ≤ a) (hη : |η| ≤ a / 10) :
    (∑' p : XiZero,
      l / ‖(((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2) ≤
      (zeroCountIn (sourceZeroDisk φ (2 * a)) : ℝ) / l +
        (5 * l / a) * ∑' p : XiZero,
          (1 / ((((1 + a : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p)).re := by
  let f : XiZero → ℝ := fun p =>
    l / ‖(((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2
  let g : XiZero → ℝ := fun p =>
    (1 / ((((1 + a : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p)).re
  let S := (finite_xiZero_sourceDisk φ (2 * a)).toFinset
  have hf : Summable f := (source_zero_kernel_neg_height hl (φ + η)).1
  have ha : 0 < a := hl.trans_le hla
  have hg : Summable g :=
    (re_xi_logDeriv_eq_tsum_of_one_le_re (s := ((1 + a : ℝ) : ℂ) + (φ : ℂ) * I)
      (by simp; linarith)).1
  have hg0 : ∀ p, 0 ≤ g p := fun p =>
    (div_nonneg ha.le (sq_nonneg _)).trans (source_inverse_square_le_real_resolvent a φ p)
  have hfar : (∑' p : ↑(S : Set XiZero)ᶜ, f p) ≤
      (5 * l / a) * ∑' p : XiZero, g p := by
    calc
      _ ≤ ∑' p : ↑(S : Set XiZero)ᶜ, (5 * l / a) * g p := by
        apply Summable.tsum_le_tsum _ (hf.subtype _) ((hg.subtype _).mul_left _)
        intro p
        apply source_far_kernel_le_real_resolvent hl hla hη
        have hp := p.property
        change p.val ∉ S at hp
        simp only [S, Set.Finite.mem_toFinset, mem_setOf_eq, sourceZeroDisk] at hp
        rw [norm_sub_rev] at hp
        exact le_of_not_gt hp
      _ = (5 * l / a) * ∑' p : ↑(S : Set XiZero)ᶜ, g p := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Summable.tsum_subtype_le g _ hg0 hg) (by positivity)
  have hnear : ∑ p ∈ S, f p ≤ (S.card : ℝ) / l := by
    calc
      _ ≤ ∑ _p ∈ S, (1 / l : ℝ) :=
        Finset.sum_le_sum (fun p _ => source_zero_kernel_le_reciprocal hl (φ + η) p)
      _ = _ := by simp [div_eq_mul_inv]
  have hcard : (S.card : ℝ) = (zeroCountIn (sourceZeroDisk φ (2 * a)) : ℝ) := by
    rw [zeroCountIn, Set.ncard_eq_toFinset_card _ (finite_xiZero_sourceDisk φ (2 * a))]
  change (∑' p, f p) ≤ _
  rw [← hf.sum_add_tsum_compl (s := S)]
  simpa only [hcard] using add_le_add hnear hfar

/-- With the linked source scales, near zeros carry at least lY/9 units of multiplicity. -/
theorem source_disk_count_of_weighted_forcing {l Y Q η φ : ℝ}
    (hl : 0 < l) (hY : 0 < Y) (hYQ : Y ≤ Q / 2)
    (hη : |η| ≤ 2 * l * Real.sqrt (Q / Y))
    (hforce : Y / 4 ≤ ∑' p : XiZero,
      l / ‖(((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2)
    (hupper : (∑' p : XiZero,
      (1 / ((((1 + 20 * l * Q / Y : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p)).re) ≤
        5 * Q / 9) :
    l * Y / 9 ≤ (zeroCountIn (sourceZeroDisk φ (40 * l * Q / Y)) : ℝ) := by
  have hQ : 0 < Q := by linarith
  obtain ⟨hla, heta⟩ := source_eta_le_outer_tenth hl hY hYQ hη
  have hbound := weighted_zero_sum_le_disk_and_resolvent (φ := φ) hl hla heta
  have hscale : 5 * l / (20 * l * Q / Y) = Y / (4 * Q) := by
    field_simp
    ring
  have hradius : 2 * (20 * l * Q / Y) = 40 * l * Q / Y := by ring
  rw [hscale, hradius] at hbound
  have hu := mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ Y / (4 * Q))
  have he : Y / (4 * Q) * (5 * Q / 9) = 5 * Y / 36 := by
    field_simp
    ring
  rw [he] at hu
  have hnear : Y / 9 ≤ (zeroCountIn (sourceZeroDisk φ (40 * l * Q / Y)) : ℝ) / l := by
    linarith
  have h := (le_div_iff₀ hl).mp hnear
  nlinarith only [h]

end
end DongWangWangZhang2026
