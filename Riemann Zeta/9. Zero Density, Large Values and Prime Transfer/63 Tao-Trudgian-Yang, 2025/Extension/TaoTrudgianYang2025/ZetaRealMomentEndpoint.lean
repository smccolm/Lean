import TaoTrudgianYang2025.ZetaOneLineLowerMean
import TaoTrudgianYang2025.ZetaLargeValueDiscreteness

/-!
# The endpoint moment obstruction and the complete source moment transfer

On Re s=1, the actual first moment forces every real p>=1 moment exponent
to be at least one. This closes the endpoint without moving a contour
through the pole or imposing M>=1 as an extra source hypothesis.
-/

noncomputable section
open Complex Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem eventually_zetaOneLine_realMoment_ge {p : ℝ} (hp : 1 ≤ p) :
    ∀ᶠ H : ℝ in atTop,
      H/(2 : ℝ)^p ≤ ∫ t in H..2*H, zetaMomentLineNorm 1 t^p := by
  filter_upwards [eventually_integral_zetaOneLine_norm_ge,eventually_gt_atTop (0 : ℝ)] with H hLower hH
  have hle : H ≤ 2*H := by linarith
  have hc : ContinuousOn (zetaMomentLineNorm 1) (Ioi 0) := by
    simpa only [zetaMomentLineNorm,Complex.ofReal_one] using continuousOn_zetaOneLine_positive.norm
  have hsubset : Set.uIcc H (2*H) ⊆ Ioi (0 : ℝ) := by
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    exact hH.trans_le ht.1
  have hfInt : IntervalIntegrable (zetaMomentLineNorm 1) volume H (2*H) :=
    (hc.mono hsubset).intervalIntegrable
  have hfpInt : IntervalIntegrable (fun t => zetaMomentLineNorm 1 t^p) volume H (2*H) :=
    ((hc.rpow_const (fun _ _ => Or.inr (by linarith))).mono hsubset).intervalIntegrable
  have hwInt : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc H (2*H))) :=
    (continuous_const.intervalIntegrable H (2*H)).1
  have hmass : (∫ _t : ℝ, (1 : ℝ) ∂volume.restrict (Ioc H (2*H))) = H := by
    rw [← intervalIntegral.integral_of_le hle]
    simp
    ring
  have hraw := integral_weighted_realMoment
    (μ := volume.restrict (Ioc H (2*H))) (w := fun _ => (1 : ℝ))
    (f := zetaMomentLineNorm 1) hp (fun _ => zero_le_one) (fun _ => norm_nonneg _)
    hwInt (by simpa only [one_mul] using hfInt.1)
    (by simpa only [one_mul] using hfpInt.1) (by rw [hmass]; exact hH)
  simp only [one_mul,hmass,← intervalIntegral.integral_of_le hle] at hraw
  have hpower := Real.rpow_le_rpow (by positivity : 0 ≤ H/2) hLower (by linarith : 0 ≤ p)
  have hlhs : (H/2)^p = H^(p-1)*(H/(2 : ℝ)^p) := by
    rw [Real.div_rpow hH.le (by norm_num)]
    have hh : H^p = H^(p-1)*H := by
      simpa only [sub_add_cancel] using Real.rpow_add_one hH.ne' (p-1)
    rw [hh]
    ring
  rw [hlhs] at hpower
  exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hH (p-1))).mp (hpower.trans hraw)

theorem one_le_zetaOneLine_moment_exponent {p M : ℝ} (hp : 1 ≤ p)
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2*H, zetaMomentLineNorm 1 u^p) ≤ C*H^(M+η)) :
    1 ≤ M := by
  by_contra hM
  have hM1 : M < 1 := lt_of_not_ge hM
  let η : ℝ := (1-M)/2
  have hη : 0 < η := by dsimp [η]; linarith
  have hgap : 0 < 1-(M+η) := by dsimp [η]; linarith
  obtain ⟨C,T₀,hC,hbound⟩ := hDyadic η hη
  have hlarge : ∀ᶠ H : ℝ in atTop, C*(2 : ℝ)^p < H^(1-(M+η)) :=
    (tendsto_rpow_atTop hgap).eventually (eventually_gt_atTop _)
  obtain ⟨H,⟨⟨hLower,hH₀⟩,hHp⟩,hgt⟩ :=
    (eventually_zetaOneLine_realMoment_ge hp |>.and
      (eventually_ge_atTop T₀) |>.and (eventually_gt_atTop (0 : ℝ)) |>.and hlarge).exists
  have hlow := hLower.trans (hbound H hH₀ hHp)
  have htwo : 0 < (2 : ℝ)^p := Real.rpow_pos_of_pos (by norm_num) p
  have hh : H ≤ C*(2 : ℝ)^p*H^(M+η) := by
    have hs := (div_le_iff₀ htwo).mp hlow
    nlinarith
  have hquot : H^(1-(M+η)) ≤ C*(2 : ℝ)^p := by
    rw [Real.rpow_sub hHp,Real.rpow_one]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hHp (M+η))).mpr hh
  exact (not_lt_of_ge hquot) hgt

/-- Printed add-bound(ii), with both closed real-line endpoints and every
real order p>=1. All analytic transfer premises are discharged; only the
source's actual dyadic zeta moment hypothesis remains. -/
theorem zetaRealMoment_largeValueBound_closed_strip
    {c p M : ℝ} (hc : 1/2 ≤ c) (hc1 : c ≤ 1) (hp : 1 ≤ p)
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2*H, zetaMomentLineNorm c u^p) ≤ C*H^(M+η))
    {σ τ : ℝ} (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 2 ≤ τ) :
    IsZetaLargeValueBound σ τ (τ*M-p*(σ-c)) := by
  rcases lt_or_eq_of_le hc1 with hlt | heq
  · exact zetaRealMoment_largeValueBound_of_dyadic hc hlt hp hDyadic hσ hτ
  · subst c
    have hM := one_le_zetaOneLine_moment_exponent hp hDyadic
    apply isZetaLargeValueBound_of_exponent_le
    apply (zetaLargeValueExponent_le_tau σ (by linarith : 0 ≤ τ)).trans
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [mul_nonneg (show 0 ≤ p by linarith) (sub_nonneg.mpr hσ1),
      mul_nonneg (show 0 ≤ τ by linarith) (sub_nonneg.mpr hM)]

theorem zetaLargeValueExponent_le_of_realMoment_closed_strip
    {c p M : ℝ} (hc : 1/2 ≤ c) (hc1 : c ≤ 1) (hp : 1 ≤ p)
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2*H, zetaMomentLineNorm c u^p) ≤ C*H^(M+η))
    {σ τ : ℝ} (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 2 ≤ τ) :
    zetaLargeValueExponent σ τ ≤ ((τ*M-p*(σ-c) : ℝ) : EReal) :=
  zetaLargeValueExponent_le_of_bound
    (zetaRealMoment_largeValueBound_closed_strip hc hc1 hp hDyadic hσ hσ1 hτ)

end TaoTrudgianYang2025
