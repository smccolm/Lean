import PrimeShell.Admissible

namespace PrimeShell

noncomputable section

/-- The exact exponent test for a short-interval theorem with threshold
`theta`: at a prime scale `N = T^alpha`, the resonant length `N/T` is
strictly longer than `N^theta` exactly when `alpha > 1/(1-theta)`. -/
theorem short_interval_overlap_iff
    {θ α : ℝ} (hθ1 : θ < 1) (hα : 0 < α) :
    θ < 1 - 1 / α ↔ 1 / (1 - θ) < α := by
  have hone : 0 < 1 - θ := sub_pos.mpr hθ1
  constructor
  · intro h
    have hrecip : 1 / α < 1 - θ := by linarith
    rw [div_lt_iff₀ hα] at hrecip
    rw [div_lt_iff₀ hone]
    nlinarith
  · intro h
    rw [div_lt_iff₀ hone] at h
    have hrecip : 1 / α < 1 - θ := by
      rw [div_lt_iff₀ hα]
      nlinarith
    linarith

/-- MRT Theorem 1.3(i)'s `8/33` long-shift threshold reaches the resonant
range exactly beyond `alpha = 33/25`. -/
theorem mrt_overlap_iff_alpha_gt_thirtythree_twentyfive
    {α : ℝ} (hα : 0 < α) :
    8 / 33 < 1 - 1 / α ↔ 33 / 25 < α := by
  have h := short_interval_overlap_iff
    (θ := (8 / 33 : ℝ)) (α := α) (by norm_num) hα
  norm_num at h ⊢
  exact h

/-- Strict epsilon-budget form of the MRT threshold. -/
theorem exists_strict_mrt_margin_iff_alpha_gt_thirtythree_twentyfive
    {α : ℝ} (hα : 0 < α) :
    (∃ ε : ℝ, 0 < ε ∧ 8 / 33 + ε < 1 - 1 / α) ↔
      33 / 25 < α := by
  constructor
  · rintro ⟨ε, hε, h⟩
    exact (mrt_overlap_iff_alpha_gt_thirtythree_twentyfive hα).mp (by linarith)
  · intro h
    have hbase : 8 / 33 < 1 - 1 / α :=
      (mrt_overlap_iff_alpha_gt_thirtythree_twentyfive hα).mpr h
    exact ⟨((1 - 1 / α) - 8 / 33) / 2, by linarith, by linarith⟩

/-- A coverage predicate for a contiguous beyond-support-one band.  It says
that every exponent strictly between one and the full bandwidth lies in the
range of an arithmetic theorem beginning strictly beyond `threshold`. -/
def CoversEveryBeyondOneScale (threshold lam : ℝ) : Prop :=
  ∀ α : ℝ, 1 < α → α < lam → threshold < α

/-- Any arithmetic theorem whose usable range starts at a fixed exponent
strictly above one necessarily leaves a nonempty uncovered band immediately
above support one. -/
theorem not_coversEveryBeyondOneScale
    {threshold lam : ℝ} (hthreshold : 1 < threshold) (hlam : threshold < lam) :
    ¬ CoversEveryBeyondOneScale threshold lam := by
  intro hcover
  let α := (1 + threshold) / 2
  have h1α : 1 < α := by dsimp [α]; linarith
  have hαthreshold : α < threshold := by dsimp [α]; linarith
  have hαlam : α < lam := hαthreshold.trans hlam
  exact (not_lt_of_ge (hcover α h1α hαlam).le) hαthreshold

/-- In particular, MRT's range alone cannot cover the complete contiguous
prime band between support one and any admissible cutoff that reaches MRT. -/
theorem mrt_does_not_cover_full_contiguous_band
    (A : PrimeShellMRTAdmissible) :
    ¬ CoversEveryBeyondOneScale (33 / 25)
      A.toPrimeShellAdmissible.P.lam :=
  not_coversEveryBeyondOneScale (by norm_num) A.mrt_overlap

/-- The analogous exact gap for the Guth--Maynard `2/15` short-interval
threshold. -/
theorem gm_does_not_cover_full_contiguous_band
    {lam : ℝ} (hlam : (15 / 13 : ℝ) < lam) :
    ¬ CoversEveryBeyondOneScale (15 / 13) lam :=
  not_coversEveryBeyondOneScale (by norm_num) hlam

end

end PrimeShell
