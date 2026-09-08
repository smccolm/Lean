import GafniTao.SharpPerronGoodHeightChoice

/-!
# The local partial-fraction estimate at a selected Perron height

This applies the proved Landau--Jensen logarithmic-derivative theorem to the
literal normalized Riemann zeta function.  The point is tied to the physical
horizontal segment, and exclusion from the larger zero disk is deduced from
the finite good-height separation rather than assumed.
-/

open Complex Set Metric Finset
open RiemannZeta.GuthMaynard
open scoped BigOperators

noncomputable section

namespace GafniTao

/-- Normalized coordinate of the physical point `sigma + i R` in the Landau
disk centered at height `T + 1/2`. -/
noncomputable def sharpLandauCoord (T σ R : ℝ) : ℂ :=
  (((σ : ℂ) + (R : ℂ) * Complex.I) - sharpLandauCenter T) /
    (7 / 4 : ℝ)

theorem sharpLandauMap_coord (T σ R : ℝ) :
    sharpLandauMap T (sharpLandauCoord T σ R) =
      (σ : ℂ) + (R : ℂ) * Complex.I := by
  rw [sharpLandauMap, sharpLandauCoord]
  push_cast
  field_simp
  ring

theorem norm_sharpLandauCoord_le
    {T σ R : ℝ} (hR : R ∈ Set.Icc T (T + 1))
    (hσ : σ ∈ Set.Icc (1 / 2) 2) :
    ‖sharpLandauCoord T σ R‖ ≤ 19 / 20 := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 19 / 20)]
  simp only [sharpLandauCoord, norm_div, Complex.norm_real, Real.norm_eq_abs,
    div_pow]
  rw [Complex.sq_norm]
  norm_num [sharpLandauCenter, Complex.normSq_apply]
  rcases hR with ⟨hR₁, hR₂⟩
  rcases hσ with ⟨hσ₁, hσ₂⟩
  nlinarith [sq_nonneg (σ - 1 / 2), sq_nonneg (2 - σ),
    sq_nonneg (R - T), sq_nonneg (T + 1 - R)]

theorem sharpLandauCoord_im (T σ R : ℝ) :
    (sharpLandauMap T (sharpLandauCoord T σ R)).im = R := by
  rw [sharpLandauMap_coord]
  simp

theorem sharpLandau_good_height_distance
    {T σ R : ℝ} (hT : 8 ≤ T) { ρ : ℂ }
    (hρ : ρ ∈ sharpLandauZeroFinset T hT)
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
      (7 / 4 : ℝ) * ‖sharpLandauCoord T σ R - ρ‖ := by
  have heq :
      R - (sharpLandauMap T ρ).im =
        (7 / 4 : ℝ) * (sharpLandauCoord T σ R - ρ).im := by
    simp only [sharpLandauMap, sharpLandauCoord, sharpLandauCenter,
      Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.div_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, zero_add, add_zero]
    norm_num
    ring
  have hsep := hfar ρ hρ
  rw [heq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 4)] at hsep
  exact hsep.trans
    (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (by norm_num))

theorem norm_sharpLandau_zeroTerm_le
    {T σ R : ℝ} (hT : 8 ≤ T) { ρ : ℂ }
    (hρ : ρ ∈ sharpLandauZeroFinset T hT)
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    ‖(analyticOrderNatAt (sharpLandauNormalized T) ρ : ℂ) /
        (sharpLandauCoord T σ R - ρ)‖ ≤
      (7 / 2 : ℝ) *
        (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1) *
          analyticOrderNatAt (sharpLandauNormalized T) ρ := by
  set q : ℝ := ((sharpLandauZeroOrdinates T hT).card : ℝ) + 1
  have hq : 0 < q := by
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  have hdist := sharpLandau_good_height_distance (T := T) (σ := σ)
    (R := R) hT hρ hfar
  have hnormPos : 0 < ‖sharpLandauCoord T σ R - ρ‖ := by
    by_contra h
    have hz : ‖sharpLandauCoord T σ R - ρ‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hz, mul_zero] at hdist
    have : 0 < 1 / (2 * q) := by positivity
    exact (not_lt_of_ge hdist) this
  rw [norm_div, RCLike.norm_natCast]
  change (analyticOrderNatAt (sharpLandauNormalized T) ρ : ℝ) /
      ‖sharpLandauCoord T σ R - ρ‖ ≤
    (7 / 2 : ℝ) * q * analyticOrderNatAt (sharpLandauNormalized T) ρ
  rw [div_le_iff₀ hnormPos]
  have hscaled : 1 ≤ (7 / 2 : ℝ) * q *
      ‖sharpLandauCoord T σ R - ρ‖ := by
    calc
      1 = (2 * q) * (1 / (2 * q)) := by field_simp
      _ ≤ (2 * q) * ((7 / 4 : ℝ) *
          ‖sharpLandauCoord T σ R - ρ‖) :=
        mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = (7 / 2 : ℝ) * q *
          ‖sharpLandauCoord T σ R - ρ‖ := by ring
  calc
    (analyticOrderNatAt (sharpLandauNormalized T) ρ : ℝ) ≤
        ((7 / 2 : ℝ) * q *
          ‖sharpLandauCoord T σ R - ρ‖) *
            analyticOrderNatAt (sharpLandauNormalized T) ρ := by
          exact le_mul_of_one_le_left (Nat.cast_nonneg _) hscaled
    _ = ((7 / 2 : ℝ) * q *
          analyticOrderNatAt (sharpLandauNormalized T) ρ) *
            ‖sharpLandauCoord T σ R - ρ‖ := by ring

theorem norm_sharpLandau_zeroSum_le
    {T σ R : ℝ} (hT : 8 ≤ T)
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    ‖∑ ρ ∈ sharpLandauZeroFinset T hT,
        (analyticOrderNatAt (sharpLandauNormalized T) ρ : ℂ) /
          (sharpLandauCoord T σ R - ρ)‖ ≤
      (7 / 2 : ℝ) *
        (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1) *
          sharpLandauZeroMass T hT := by
  calc
    ‖∑ ρ ∈ sharpLandauZeroFinset T hT,
        (analyticOrderNatAt (sharpLandauNormalized T) ρ : ℂ) /
          (sharpLandauCoord T σ R - ρ)‖ ≤
        ∑ ρ ∈ sharpLandauZeroFinset T hT,
          ‖(analyticOrderNatAt (sharpLandauNormalized T) ρ : ℂ) /
            (sharpLandauCoord T σ R - ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ sharpLandauZeroFinset T hT,
          (7 / 2 : ℝ) *
            (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1) *
              analyticOrderNatAt (sharpLandauNormalized T) ρ := by
        exact Finset.sum_le_sum (fun ρ hρ ↦
          norm_sharpLandau_zeroTerm_le hT hρ hfar)
    _ = (7 / 2 : ℝ) *
        (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1) *
          sharpLandauZeroMass T hT := by
      simp only [sharpLandauZeroMass, Nat.cast_sum]
      rw [Finset.mul_sum]

theorem sharpLandauCoord_not_mem_large_zeros
    {T σ R : ℝ} (hT : 8 ≤ T)
    (hR : R ∈ Set.Icc T (T + 1)) (hσ : σ ∈ Set.Icc (1 / 2) 2)
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    sharpLandauCoord T σ R ∉
      SetOfZeros (97 / 100) (sharpLandauNormalized T) := by
  intro hz
  have hzNorm : ‖sharpLandauCoord T σ R‖ ≤ 24 / 25 := by
    exact (norm_sharpLandauCoord_le hR hσ).trans (by norm_num)
  have hzSmall : sharpLandauCoord T σ R ∈ sharpLandauZeroFinset T hT := by
    exact (finiteSetOfZeros_mono (by norm_num : (24 / 25 : ℝ) < 1)
      (finite_sharpLandauNormalized_zeros hT)).mem_toFinset.mpr
        ⟨hzNorm, hz.2⟩
  have hsep := hfar _ hzSmall
  rw [sharpLandauCoord_im, sub_self, abs_zero] at hsep
  have hcard : (0 : ℝ) ≤ (sharpLandauZeroOrdinates T hT).card := by positivity
  have : 0 < 1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) := by
    positivity
  linarith

/-- Direct `FinalBound` specialization on the selected physical horizontal
segment.  The finite sum is precisely over the genuine normalized zeta zeros
with their analytic orders. -/
theorem sharpLandau_partialFraction_bound
    {T σ R : ℝ} (hT : 8 ≤ T)
    (hR : R ∈ Set.Icc T (T + 1)) (hσ : σ ∈ Set.Icc (1 / 2) 2)
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    ‖deriv (sharpLandauNormalized T) (sharpLandauCoord T σ R) /
          sharpLandauNormalized T (sharpLandauCoord T σ R) -
        ∑ ρ ∈ sharpLandauZeroFinset T hT,
          analyticOrderNatAt (sharpLandauNormalized T) ρ /
            (sharpLandauCoord T σ R - ρ)‖ ≤
      (16 * (24 / 25 : ℝ) ^ 2 / ((24 / 25 : ℝ) - 19 / 20) ^ 3 +
          1 / (((49 / 50 : ℝ) ^ 2 / (97 / 100 : ℝ) - 97 / 100) *
            Real.log ((49 / 50 : ℝ) / (97 / 100 : ℝ)))) *
        Real.log (200 * T ^ (3 : ℝ)) := by
  have hTT : T ∈ Set.Icc (T - 1) (2 * T) := ⟨by linarith, by linarith⟩
  have hB : 1 < 200 * T ^ (3 : ℝ) := by
    have hpow : 1 ≤ T ^ (3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    nlinarith
  apply FinalBound (B := 200 * T ^ (3 : ℝ))
      (r' := 19 / 20) (r := 24 / 25) (R' := 97 / 100) (R := 49 / 50)
  · exact hB
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact analyticOnNhd_sharpLandauNormalized hT hTT
  · exact sharpLandauNormalized_zero T
  · exact finite_sharpLandauNormalized_zeros hT
  · intro w hw
    exact norm_sharpLandauNormalized_le hT hTT (by linarith)
  · exact ⟨by
      simpa [Metric.mem_closedBall, Complex.dist_eq] using
        norm_sharpLandauCoord_le hR hσ,
      sharpLandauCoord_not_mem_large_zeros hT hR hσ hfar⟩

end GafniTao
