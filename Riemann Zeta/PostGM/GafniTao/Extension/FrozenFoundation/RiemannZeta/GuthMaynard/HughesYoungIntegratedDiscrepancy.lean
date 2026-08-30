import RiemannZeta.GuthMaynard.HughesYoungReducedFubini
import RiemannZeta.GuthMaynard.HughesYoungReducedConsumer
import RiemannZeta.GuthMaynard.HughesYoungCentralContinuity

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Cancellation-preserving integrated DFI discrepancy

Hughes--Young applies DFI before the compact Mellin-ordinate integral is
evaluated.  Consequently the source-faithful main term is the integral of
the signed pointwise DFI central series.  Keeping that expression intact is
essential: taking norms of the individual central series would destroy the
four-term cancellation in Hughes--Young Sections 6--7.
-/

/-- The exact signed DFI main term for a finite shift family, integrated in
the Mellin ordinate in the order used by Hughes--Young. -/
noncomputable def hughesYoungIntegratedPointwiseSignedCentral
    (T c H X Y : ℝ) (h k : ℕ) (s : Finset ℤ) : ℂ :=
  ∫ u in -H..H, (T : ℂ) *
    (∑ r ∈ s,
      dfiSignedCentralSeries
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r))

/-- Exact finite-source discrepancy from the cancellation-preserving
integrated central term. -/
noncomputable def hughesYoungIntegratedPointwiseDFIDiscrepancy
    (T c H X Y : ℝ) (h k M N : ℕ) (s : Finset ℤ) : ℂ :=
  (∑ r ∈ s,
      dfiDyadicShiftedDivisorSum
        (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N r) -
    hughesYoungIntegratedPointwiseSignedCentral T c H X Y h k s

/-- The exact finite shifted-divisor source is its integrated signed DFI
main term plus the literal integrated DFI error. -/
theorem sum_dfiDyadicShiftedDivisorSum_gcdReducedIntegratedBox_eq_pointwiseCentral_add_discrepancy
    (T c H X Y : ℝ) (h k M N : ℕ) (s : Finset ℤ) :
    (∑ r ∈ s,
      dfiDyadicShiftedDivisorSum
        (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N r) =
      hughesYoungIntegratedPointwiseSignedCentral T c H X Y h k s +
        hughesYoungIntegratedPointwiseDFIDiscrepancy
          T c H X Y h k M N s := by
  unfold hughesYoungIntegratedPointwiseDFIDiscrepancy
  ring

/-- The exact integrated DFI discrepancy is the compact Mellin integral of
the literal pointwise DFI Theorem-1 discrepancy.  The infinite signed
central series is continuous by the profile-uniform equation-(27) argument,
so this subtraction is a justified Bochner integral identity rather than a
formal rearrangement of non-integrable expressions. -/
theorem hughesYoungIntegratedPointwiseDFIDiscrepancy_eq_integral
    {T c H X Y P U : ℝ} {h k M N : ℕ} {s : Finset ℤ}
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hh : 0 < h) (hk : 0 < k)
    (hP : 1 ≤ P) (hU : 0 < U) (hscale : U ≤ P⁻¹ * min X Y)
    (hs : ∀ r ∈ s,
      r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧ T * (|(r : ℝ)| / Y) ≤ P) :
    hughesYoungIntegratedPointwiseDFIDiscrepancy
        T c H X Y h k M N s =
      ∫ u in -H..H, (T : ℂ) *
        ((∑ r ∈ s,
            dfiDyadicShiftedDivisorSum
              (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              M N r) -
          ∑ r ∈ s,
            dfiSignedCentralSeries
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
              (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)) := by
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let F : ℝ → ℂ := fun u => (T : ℂ) *
    (∑ r ∈ s,
      dfiDyadicShiftedDivisorSum
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
        a b M N r)
  let G : ℝ → ℂ := fun u => (T : ℂ) *
    (∑ r ∈ s,
      dfiSignedCentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r))
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hFcont : Continuous F := by
    exact continuous_const.mul
      (continuous_finsetSum s fun r _ =>
        continuous_dfiDyadicShiftedDivisorSum_reducedCleaned_ordinate
          hT0 hc X Y hh hk ha hb r)
  have hGcont : Continuous G := by
    exact continuous_const.mul
      (by
        simpa only [a, b] using
          continuous_sum_dfiSignedCentralSeries_reducedCleaned_ordinate
            hT hc hc1 hX hY hh hk hP hU hscale hs)
  unfold hughesYoungIntegratedPointwiseDFIDiscrepancy
    hughesYoungIntegratedPointwiseSignedCentral
  rw [sum_dfiDyadicShiftedDivisorSum_gcdReducedIntegratedBox_eq_integral
    hT0 hc H X Y hh hk ha hb s]
  change (∫ u in -H..H, F u) - (∫ u in -H..H, G u) = _
  rw [← intervalIntegral.integral_sub
    (hFcont.intervalIntegrable _ _) (hGcont.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro u _hu
  dsimp only [F, G, a, b]
  ring

/-- The compact Mellin integral of the literal DFI discrepancy inherits
the published pointwise DFI error, with the signed central series left
untouched.  This is the cancellation-preserving Hughes--Young consumer of
the exact DFI remainder. -/
theorem exists_uniform_norm_hughesYoungIntegratedPointwiseDFIDiscrepancy
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ Cγ C : ℝ, 0 < Cγ ∧ 0 < C ∧
      ∀ {T c H X Y P U Q : ℝ} {h k M N : ℕ} {s : Finset ℤ},
      1 ≤ T → 0 < c → c ≤ 1 → 0 ≤ H →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k → 1 ≤ P → 0 < U →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      (hughesYoungReducedLeft h k : ℝ) ≤ 2 * X →
      (hughesYoungReducedRight h k : ℝ) ≤ 2 * Y →
      (∀ r ∈ s,
        r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧
        T * (|(r : ℝ)| / Y) ≤ P ∧
        (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
        (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y)) →
      ‖hughesYoungIntegratedPointwiseDFIDiscrepancy
          T c H X Y h k M N s‖ ≤
        ∫ u in -H..H, T *
          ((s.card : ℝ) *
            (‖hughesYoungLocalizedStaticScalar T h k‖ *
              hughesYoungScaledDFINormalization c u X Y
                (hughesYoungSmallLineEnvelope Cγ T c u)
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) *
              (C * dfiTheorem1ErrorScale P X Y ε))) := by
  obtain ⟨Cγ, hCγ, hheight⟩ :=
    exists_norm_one_div_mul_iteratedDeriv_hughesYoungHeightTransform_le
  obtain ⟨C, hC, hdfi⟩ :=
    exists_uniform_norm_sum_hughesYoungReducedCleanedShiftWeight_dfiDiscrepancy
      ε hε0 hε4
  refine ⟨Cγ, C, hCγ, hC, ?_⟩
  intro T c H X Y P U Q h k M N s hT hc hc1 hH hX hY hh hk hP hU
    hscale hQ hUQ hQsq hM hN haX hbY hs
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let A : ℝ → ℝ := hughesYoungSmallLineEnvelope Cγ T c
  let F : ℝ → ℂ := fun u => (T : ℂ) *
    ((∑ r ∈ s,
        dfiDyadicShiftedDivisorSum
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
          a b M N r) -
      ∑ r ∈ s,
        dfiSignedCentralSeries a b r
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r))
  let G : ℝ → ℝ := fun u => T *
    ((s.card : ℝ) *
      (‖hughesYoungLocalizedStaticScalar T h k‖ *
        hughesYoungScaledDFINormalization c u X Y (A u) a b *
        (C * dfiTheorem1ErrorScale P X Y ε)))
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hApos : ∀ u : ℝ, 0 < A u := fun u =>
    hughesYoungSmallLineEnvelope_pos hT0 hc u
  have hAcont : Continuous A :=
    continuous_hughesYoungSmallLineEnvelope Cγ T c
  have hsCore : ∀ r ∈ s,
      r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧ T * (|(r : ℝ)| / Y) ≤ P := by
    intro r hr
    exact ⟨(hs r hr).1, (hs r hr).2.1, (hs r hr).2.2.1⟩
  have hFcont : Continuous F := by
    apply continuous_const.mul
    apply Continuous.sub
    · exact continuous_finsetSum s fun r _ =>
        continuous_dfiDyadicShiftedDivisorSum_reducedCleaned_ordinate
          hT0 hc X Y hh hk ha hb r
    · simpa only [a, b] using
        continuous_sum_dfiSignedCentralSeries_reducedCleaned_ordinate
          hT hc hc1 hX hY hh hk hP hU hscale hsCore
  have hGcont : Continuous G := by
    dsimp only [G]
    apply continuous_const.mul
    apply continuous_const.mul
    apply (continuous_const.mul ?_).mul continuous_const
    exact (((hAcont.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.pow 2)))).mul_const
        (((a : ℝ) / X) ^ ((1 / 2 : ℝ) + c))).mul_const
          (((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)))
  have hpoint : ∀ u : ℝ, ‖F u‖ ≤ G u := by
    intro u
    have hderiv : ∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A u) := by
      intro n xi
      simpa only [A, hughesYoungSmallLineEnvelope] using
        hheight T u c hT hc hc1 n xi
    have hraw := hdfi hT hc hc1 hX hY hh hk hP (hApos u) hderiv
      hscale hQ hUQ hQsq M N hM hN haX hbY hs
    dsimp only [F, G]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    exact mul_le_mul_of_nonneg_left hraw hT0.le
  rw [hughesYoungIntegratedPointwiseDFIDiscrepancy_eq_integral
    hT hc hc1 hX hY hh hk hP hU hscale hsCore]
  change ‖∫ u in -H..H, F u‖ ≤ ∫ u in -H..H, G u
  have hHH : -H ≤ H := by linarith
  calc
    ‖∫ u in -H..H, F u‖ ≤ ∫ u in -H..H, ‖F u‖ :=
      intervalIntegral.norm_integral_le_integral_norm hHH
    _ ≤ ∫ u in -H..H, G u := by
      apply intervalIntegral.integral_mono_on hHH
        (hFcont.norm.intervalIntegrable (-H) H)
        (hGcont.intervalIntegrable (-H) H)
      intro u _hu
      exact hpoint u

/-- Compact Mellin integration of the coefficient-unrestricted DFI
discrepancy.  The lattice coefficients may exceed their dyadic scales;
the exact DFI error then absorbs the empty lattice sum against its signed
Ramanujan main term. -/
theorem exists_uniform_norm_hughesYoungIntegratedPointwiseDFIDiscrepancy_unrestricted
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ Cγ C : ℝ, 0 < Cγ ∧ 0 < C ∧
      ∀ {T c H X Y P U Q : ℝ} {h k M N : ℕ} {s : Finset ℤ},
      1 ≤ T → 0 < c → c ≤ 1 → 0 ≤ H →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k → 1 ≤ P → 0 < U →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      (∀ r ∈ s,
        r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧
        T * (|(r : ℝ)| / Y) ≤ P ∧
        (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
        (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y)) →
      ‖hughesYoungIntegratedPointwiseDFIDiscrepancy
          T c H X Y h k M N s‖ ≤
        ∫ u in -H..H, T *
          ((s.card : ℝ) *
            (‖hughesYoungLocalizedStaticScalar T h k‖ *
              hughesYoungScaledDFINormalization c u X Y
                (hughesYoungSmallLineEnvelope Cγ T c u)
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) *
              (C * dfiTheorem1ErrorScale P X Y ε))) := by
  obtain ⟨Cγ, hCγ, hheight⟩ :=
    exists_norm_one_div_mul_iteratedDeriv_hughesYoungHeightTransform_le
  obtain ⟨C, hC, hdfi⟩ :=
    exists_uniform_norm_sum_hughesYoungReducedCleanedShiftWeight_dfiDiscrepancy_unrestricted
      ε hε0 hε4
  refine ⟨Cγ, C, hCγ, hC, ?_⟩
  intro T c H X Y P U Q h k M N s hT hc hc1 hH hX hY hh hk hP hU
    hscale hQ hUQ hQsq hM hN hs
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let A : ℝ → ℝ := hughesYoungSmallLineEnvelope Cγ T c
  let F : ℝ → ℂ := fun u => (T : ℂ) *
    ((∑ r ∈ s,
        dfiDyadicShiftedDivisorSum
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
          a b M N r) -
      ∑ r ∈ s,
        dfiSignedCentralSeries a b r
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r))
  let G : ℝ → ℝ := fun u => T *
    ((s.card : ℝ) *
      (‖hughesYoungLocalizedStaticScalar T h k‖ *
        hughesYoungScaledDFINormalization c u X Y (A u) a b *
        (C * dfiTheorem1ErrorScale P X Y ε)))
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hApos : ∀ u : ℝ, 0 < A u := fun u =>
    hughesYoungSmallLineEnvelope_pos hT0 hc u
  have hAcont : Continuous A :=
    continuous_hughesYoungSmallLineEnvelope Cγ T c
  have hsCore : ∀ r ∈ s,
      r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧ T * (|(r : ℝ)| / Y) ≤ P := by
    intro r hr
    exact ⟨(hs r hr).1, (hs r hr).2.1, (hs r hr).2.2.1⟩
  have hFcont : Continuous F := by
    apply continuous_const.mul
    apply Continuous.sub
    · exact continuous_finsetSum s fun r _ =>
        continuous_dfiDyadicShiftedDivisorSum_reducedCleaned_ordinate
          hT0 hc X Y hh hk ha hb r
    · simpa only [a, b] using
        continuous_sum_dfiSignedCentralSeries_reducedCleaned_ordinate
          hT hc hc1 hX hY hh hk hP hU hscale hsCore
  have hGcont : Continuous G := by
    dsimp only [G]
    apply continuous_const.mul
    apply continuous_const.mul
    apply (continuous_const.mul ?_).mul continuous_const
    exact (((hAcont.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.pow 2)))).mul_const
        (((a : ℝ) / X) ^ ((1 / 2 : ℝ) + c))).mul_const
          (((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)))
  have hpoint : ∀ u : ℝ, ‖F u‖ ≤ G u := by
    intro u
    have hderiv : ∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A u) := by
      intro n xi
      simpa only [A, hughesYoungSmallLineEnvelope] using
        hheight T u c hT hc hc1 n xi
    have hraw := hdfi hT hc hc1 hX hY hh hk hP (hApos u) hderiv
      hscale hQ hUQ hQsq M N hM hN hs
    dsimp only [F, G]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    exact mul_le_mul_of_nonneg_left hraw hT0.le
  rw [hughesYoungIntegratedPointwiseDFIDiscrepancy_eq_integral
    hT hc hc1 hX hY hh hk hP hU hscale hsCore]
  change ‖∫ u in -H..H, F u‖ ≤ ∫ u in -H..H, G u
  have hHH : -H ≤ H := by linarith
  calc
    ‖∫ u in -H..H, F u‖ ≤ ∫ u in -H..H, ‖F u‖ :=
      intervalIntegral.norm_integral_le_integral_norm hHH
    _ ≤ ∫ u in -H..H, G u := by
      apply intervalIntegral.integral_mono_on hHH
        (hFcont.norm.intervalIntegrable (-H) H)
        (hGcont.intervalIntegrable (-H) H)
      intro u _hu
      exact hpoint u

/-- The exact signed equation-(27) contribution for a finite shift family
inherits the source central-series estimate before the compact Mellin
ordinate is integrated.  This is deliberately stated for
`hughesYoungIntegratedPointwiseSignedCentral`, the object occurring in the
global Hughes--Young decomposition, rather than for a parallel surrogate. -/
theorem exists_uniform_norm_hughesYoungIntegratedPointwiseSignedCentral :
    ∃ Cγ C : ℝ, 0 < Cγ ∧ 0 < C ∧
      ∀ {T c H X Y P U : ℝ} {h k : ℕ} {s : Finset ℤ},
      1 ≤ T → 0 < c → c ≤ 1 → 0 ≤ H →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k → 1 ≤ P → 0 < U →
      U ≤ P⁻¹ * min X Y →
      (∀ r ∈ s,
        r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧ T * (|(r : ℝ)| / Y) ≤ P) →
      ‖hughesYoungIntegratedPointwiseSignedCentral
          T c H X Y h k s‖ ≤
        ∫ u in -H..H, T *
          (∑ r ∈ s,
            ‖hughesYoungLocalizedStaticScalar T h k‖ *
              hughesYoungScaledDFINormalization c u X Y
                (hughesYoungSmallLineEnvelope Cγ T c u)
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) *
              (C * (hughesYoungCentralArithmeticScale X Y
                  (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
                  r.natAbs +
                hughesYoungCentralArithmeticScale Y X
                  (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)
                  r.natAbs))) := by
  obtain ⟨Cγ, hCγ, hheight⟩ :=
    exists_norm_one_div_mul_iteratedDeriv_hughesYoungHeightTransform_le
  obtain ⟨C, hC, hcentral⟩ :=
    exists_uniform_norm_hughesYoungReducedCleanedShiftWeight_signedCentralSeries
  refine ⟨Cγ, C, hCγ, hC, ?_⟩
  intro T c H X Y P U h k s hT hc hc1 hH hX hY hh hk hP hU hscale
    hs
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let A : ℝ → ℝ := hughesYoungSmallLineEnvelope Cγ T c
  let F : ℝ → ℂ := fun u => (T : ℂ) *
    (∑ r ∈ s, dfiSignedCentralSeries a b r
      (hughesYoungReducedCleanedShiftWeight T c u X Y h k r))
  let G : ℝ → ℝ := fun u => T *
    (∑ r ∈ s,
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        hughesYoungScaledDFINormalization c u X Y (A u) a b *
        (C * (hughesYoungCentralArithmeticScale X Y a b r.natAbs +
          hughesYoungCentralArithmeticScale Y X b a r.natAbs)))
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hApos : ∀ u : ℝ, 0 < A u := fun u =>
    hughesYoungSmallLineEnvelope_pos hT0 hc u
  have hAcont : Continuous A :=
    continuous_hughesYoungSmallLineEnvelope Cγ T c
  have hFcont : Continuous F := by
    exact continuous_const.mul (by
      simpa only [a, b] using
        continuous_sum_dfiSignedCentralSeries_reducedCleaned_ordinate
          hT hc hc1 hX hY hh hk hP hU hscale hs)
  have hGcont : Continuous G := by
    dsimp only [G]
    apply continuous_const.mul
    apply continuous_finsetSum s
    intro _r _hr
    apply (continuous_const.mul ?_).mul continuous_const
    unfold hughesYoungScaledDFINormalization
    exact (((hAcont.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.pow 2)))).mul_const
        (((a : ℝ) / X) ^ ((1 / 2 : ℝ) + c))).mul_const
          (((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)))
  have hpoint : ∀ u : ℝ, ‖F u‖ ≤ G u := by
    intro u
    have hderiv : ∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A u) := by
      intro n xi
      simpa only [A, hughesYoungSmallLineEnvelope] using
        hheight T u c hT hc hc1 n xi
    have hraw : ‖∑ r ∈ s, dfiSignedCentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)‖ ≤
        ∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization c u X Y (A u) a b *
            (C * (hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs)) := by
      calc
        ‖∑ r ∈ s, dfiSignedCentralSeries a b r
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)‖ ≤
            ∑ r ∈ s, ‖dfiSignedCentralSeries a b r
              (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)‖ :=
          norm_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro r hr
          obtain ⟨hr0, hrY, hrP⟩ := hs r hr
          simpa only [a, b] using
            hcentral hT hc hc1 hX hY hh hk hr0 hrY hP hrP
              (hApos u) hderiv hU hscale
    dsimp only [F, G]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    exact mul_le_mul_of_nonneg_left hraw hT0.le
  unfold hughesYoungIntegratedPointwiseSignedCentral
  change ‖∫ u in -H..H, F u‖ ≤ ∫ u in -H..H, G u
  have hHH : -H ≤ H := by linarith
  calc
    ‖∫ u in -H..H, F u‖ ≤ ∫ u in -H..H, ‖F u‖ :=
      intervalIntegral.norm_integral_le_integral_norm hHH
    _ ≤ ∫ u in -H..H, G u := by
      apply intervalIntegral.integral_mono_on hHH
        (hFcont.norm.intervalIntegrable (-H) H)
        (hGcont.intervalIntegrable (-H) H)
      intro u _hu
      exact hpoint u

/-- Small-contour specialization of the exact signed equation-(27) sum.
The four source central terms remain grouped inside
`dfiSignedCentralSeries`; the estimate is taken only after their exact
combination and after the finite shift sum has been formed. -/
theorem exists_uniform_norm_hughesYoungSmallContourPointwiseSignedCentral :
    ∃ Cγ C L : ℝ, 0 < Cγ ∧ 0 < C ∧ 0 < L ∧
      ∀ {T H X Y P U : ℝ} {h k : ℕ} {s : Finset ℤ},
      Real.exp 1 ≤ T → 0 ≤ H →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k → 1 ≤ P → 0 < U →
      U ≤ P⁻¹ * min X Y →
      (∀ r ∈ s,
        r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧ T * (|(r : ℝ)| / Y) ≤ P) →
      ‖hughesYoungIntegratedPointwiseSignedCentral
          T (hughesYoungSmallContour T) H X Y h k s‖ ≤
        (T * (Real.log T * Real.exp (4 * Cγ) *
          ((hughesYoungReducedLeft h k : ℝ) / X) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
          ((hughesYoungReducedRight h k : ℝ) / Y) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
          (∑ r ∈ s,
            ‖hughesYoungLocalizedStaticScalar T h k‖ *
              (C * (hughesYoungCentralArithmeticScale X Y
                  (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
                  r.natAbs +
                hughesYoungCentralArithmeticScale Y X
                  (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)
                  r.natAbs)))) * L := by
  obtain ⟨Cγ, C, hCγ, hC, hsource⟩ :=
    exists_uniform_norm_hughesYoungIntegratedPointwiseSignedCentral
  obtain ⟨L, hL, hfactor⟩ :=
    exists_uniform_intervalIntegral_hughesYoungIntegratedOrdinateFactor_le hCγ
  refine ⟨Cγ, C, L, hCγ, hC, hL, ?_⟩
  intro T H X Y P U h k s hT hH hX hY hh hk hP hU hscale hs
  obtain ⟨hc, hc1, hcinv⟩ := hughesYoungSmallContour_spec hT
  have hT1 : 1 ≤ T :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hT
  have hfirst := hsource hT1 hc hc1 hH hX hY hh hk hP hU hscale
    hs
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let E : ℝ := ∑ r ∈ s,
    ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (C * (hughesYoungCentralArithmeticScale X Y a b r.natAbs +
        hughesYoungCentralArithmeticScale Y X b a r.natAbs))
  let D : ℝ := T * (Real.log T * Real.exp (4 * Cγ) *
    ((a : ℝ) / X) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
    ((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T)) * E
  have hE : 0 ≤ E := by
    dsimp only [E]
    apply Finset.sum_nonneg
    intro r _hr
    exact mul_nonneg (norm_nonneg _)
      (mul_nonneg hC.le (add_nonneg
        (hughesYoungCentralArithmeticScale_nonneg hX hY a b r.natAbs)
        (hughesYoungCentralArithmeticScale_nonneg hY hX b a r.natAbs)))
  have hD : 0 ≤ D := by
    dsimp only [D]
    have ha : 0 < a := hughesYoungReducedLeft_pos hh
    have hb : 0 < b := hughesYoungReducedRight_pos hh hk
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha
    have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
    have hX0 : 0 < X := zero_lt_one.trans_le hX
    have hY0 : 0 < Y := zero_lt_one.trans_le hY
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
    positivity
  have heq :
      (∫ u in -H..H, T *
        (∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization
              (hughesYoungSmallContour T) u X Y
              (hughesYoungSmallLineEnvelope Cγ T
                (hughesYoungSmallContour T) u) a b *
            (C * (hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs)))) =
        D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ
            (hughesYoungSmallContour T) u) := by
    calc
      (∫ u in -H..H, T *
        (∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization
              (hughesYoungSmallContour T) u X Y
              (hughesYoungSmallLineEnvelope Cγ T
                (hughesYoungSmallContour T) u) a b *
            (C * (hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs)))) =
          ∫ u in -H..H, D *
            hughesYoungIntegratedOrdinateFactor Cγ
              (hughesYoungSmallContour T) u := by
        apply intervalIntegral.integral_congr
        intro u _hu
        simp_rw [hughesYoungScaledDFINormalization_smallLine_eq]
        dsimp only [D, E]
        rw [rpow_smallContour_four_mul_eq Cγ hT, hcinv]
        let B : ℝ := Real.log T * Real.exp (4 * Cγ) *
          ((a : ℝ) / X) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
          ((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T)
        let O : ℝ := hughesYoungIntegratedOrdinateFactor Cγ
          (hughesYoungSmallContour T) u
        let F : ℤ → ℝ := fun r =>
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            (C * (hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs))
        change T * (∑ r ∈ s,
            ‖hughesYoungLocalizedStaticScalar T h k‖ * (B * O) *
              (C * (hughesYoungCentralArithmeticScale X Y a b r.natAbs +
                hughesYoungCentralArithmeticScale Y X b a r.natAbs))) =
          T * B * (∑ r ∈ s, F r) * O
        calc
          _ = T * (B * (∑ r ∈ s, F r) * O) := by
            apply congrArg (fun z : ℝ => T * z)
            calc
              _ = ∑ r ∈ s, B * F r * O := by
                apply Finset.sum_congr rfl
                intro r _hr
                dsimp only [F]
                ring
              _ = B * (∑ r ∈ s, F r) * O := by
                rw [Finset.mul_sum, Finset.sum_mul]
          _ = T * B * (∑ r ∈ s, F r) * O := by ring
      _ = D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ
            (hughesYoungSmallContour T) u) := by
        rw [intervalIntegral.integral_const_mul]
  calc
    ‖hughesYoungIntegratedPointwiseSignedCentral
        T (hughesYoungSmallContour T) H X Y h k s‖ ≤
        ∫ u in -H..H, T *
          (∑ r ∈ s,
            ‖hughesYoungLocalizedStaticScalar T h k‖ *
              hughesYoungScaledDFINormalization
                (hughesYoungSmallContour T) u X Y
                (hughesYoungSmallLineEnvelope Cγ T
                  (hughesYoungSmallContour T) u) a b *
              (C * (hughesYoungCentralArithmeticScale X Y a b r.natAbs +
                hughesYoungCentralArithmeticScale Y X b a r.natAbs))) := by
          simpa only [a, b] using hfirst
    _ = D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ
            (hughesYoungSmallContour T) u) := heq
    _ ≤ D * L := mul_le_mul_of_nonneg_left (hfactor hc hc1 hH) hD
    _ = _ := by rfl

/-- Hughes--Young's small-contour specialization of the literal integrated
DFI discrepancy.  Unlike the older full-DFI majorant, this estimate contains
only the published DFI error scale: all four signed central series remain in
the main term and are available for the Section 6 cancellation. -/
theorem exists_uniform_norm_hughesYoungSmallContourPointwiseDFIDiscrepancy
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ Cγ C L : ℝ, 0 < Cγ ∧ 0 < C ∧ 0 < L ∧
      ∀ {T H X Y P U Q : ℝ} {h k M N : ℕ} {s : Finset ℤ},
      Real.exp 1 ≤ T → 0 ≤ H →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k → 1 ≤ P → 0 < U →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      (hughesYoungReducedLeft h k : ℝ) ≤ 2 * X →
      (hughesYoungReducedRight h k : ℝ) ≤ 2 * Y →
      (∀ r ∈ s,
        r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧
        T * (|(r : ℝ)| / Y) ≤ P ∧
        (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
        (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y)) →
      ‖hughesYoungIntegratedPointwiseDFIDiscrepancy
          T (hughesYoungSmallContour T) H X Y h k M N s‖ ≤
        (T * (Real.log T * Real.exp (4 * Cγ) *
          ((hughesYoungReducedLeft h k : ℝ) / X) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
          ((hughesYoungReducedRight h k : ℝ) / Y) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
          ((s.card : ℝ) *
            (‖hughesYoungLocalizedStaticScalar T h k‖ *
              (C * dfiTheorem1ErrorScale P X Y ε)))) * L := by
  obtain ⟨Cγ, C, hCγ, hC, hsource⟩ :=
    exists_uniform_norm_hughesYoungIntegratedPointwiseDFIDiscrepancy
      ε hε0 hε4
  obtain ⟨L, hL, hfactor⟩ :=
    exists_uniform_intervalIntegral_hughesYoungIntegratedOrdinateFactor_le hCγ
  refine ⟨Cγ, C, L, hCγ, hC, hL, ?_⟩
  intro T H X Y P U Q h k M N s hT hH hX hY hh hk hP hU hscale hQ
    hUQ hQsq hM hN haX hbY hs
  obtain ⟨hc, hc1, hcinv⟩ := hughesYoungSmallContour_spec hT
  have hT1 : 1 ≤ T :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hT
  have hfirst := hsource hT1 hc hc1 hH hX hY hh hk hP hU hscale hQ
    hUQ hQsq hM hN haX hbY hs
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let E : ℝ := (s.card : ℝ) *
    (‖hughesYoungLocalizedStaticScalar T h k‖ *
      (C * dfiTheorem1ErrorScale P X Y ε))
  let D : ℝ := T * (Real.log T * Real.exp (4 * Cγ) *
    ((a : ℝ) / X) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
    ((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T)) * E
  have hE : 0 ≤ E := by
    dsimp only [E]
    unfold dfiTheorem1ErrorScale
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    have ha : 0 < a := hughesYoungReducedLeft_pos hh
    have hb : 0 < b := hughesYoungReducedRight_pos hh hk
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha
    have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
    have hX0 : 0 < X := zero_lt_one.trans_le hX
    have hY0 : 0 < Y := zero_lt_one.trans_le hY
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
    positivity
  have heq :
      (∫ u in -H..H, T *
        ((s.card : ℝ) *
          (‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization
              (hughesYoungSmallContour T) u X Y
              (hughesYoungSmallLineEnvelope Cγ T
                (hughesYoungSmallContour T) u) a b *
            (C * dfiTheorem1ErrorScale P X Y ε)))) =
        D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ
            (hughesYoungSmallContour T) u) := by
    calc
      (∫ u in -H..H, T *
        ((s.card : ℝ) *
          (‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization
              (hughesYoungSmallContour T) u X Y
              (hughesYoungSmallLineEnvelope Cγ T
                (hughesYoungSmallContour T) u) a b *
            (C * dfiTheorem1ErrorScale P X Y ε)))) =
          ∫ u in -H..H, D *
            hughesYoungIntegratedOrdinateFactor Cγ
              (hughesYoungSmallContour T) u := by
        apply intervalIntegral.integral_congr
        intro u _hu
        simp_rw [hughesYoungScaledDFINormalization_smallLine_eq]
        dsimp only [D, E]
        rw [rpow_smallContour_four_mul_eq Cγ hT, hcinv]
        ring
      _ = D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ
            (hughesYoungSmallContour T) u) := by
        rw [intervalIntegral.integral_const_mul]
  calc
    ‖hughesYoungIntegratedPointwiseDFIDiscrepancy
        T (hughesYoungSmallContour T) H X Y h k M N s‖ ≤
        ∫ u in -H..H, T *
          ((s.card : ℝ) *
            (‖hughesYoungLocalizedStaticScalar T h k‖ *
              hughesYoungScaledDFINormalization
                (hughesYoungSmallContour T) u X Y
                (hughesYoungSmallLineEnvelope Cγ T
                  (hughesYoungSmallContour T) u) a b *
              (C * dfiTheorem1ErrorScale P X Y ε))) := by
          simpa only [a, b] using hfirst
    _ = D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ
            (hughesYoungSmallContour T) u) := heq
    _ ≤ D * L := mul_le_mul_of_nonneg_left (hfactor hc hc1 hH) hD
    _ = _ := by rfl

/-- Small-contour specialization of the coefficient-unrestricted
integrated DFI discrepancy. -/
theorem exists_uniform_norm_hughesYoungSmallContourPointwiseDFIDiscrepancy_unrestricted
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ Cγ C L : ℝ, 0 < Cγ ∧ 0 < C ∧ 0 < L ∧
      ∀ {T H X Y P U Q : ℝ} {h k M N : ℕ} {s : Finset ℤ},
      Real.exp 1 ≤ T → 0 ≤ H →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k → 1 ≤ P → 0 < U →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      (∀ r ∈ s,
        r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧
        T * (|(r : ℝ)| / Y) ≤ P ∧
        (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
        (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y)) →
      ‖hughesYoungIntegratedPointwiseDFIDiscrepancy
          T (hughesYoungSmallContour T) H X Y h k M N s‖ ≤
        (T * (Real.log T * Real.exp (4 * Cγ) *
          ((hughesYoungReducedLeft h k : ℝ) / X) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
          ((hughesYoungReducedRight h k : ℝ) / Y) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
          ((s.card : ℝ) *
            (‖hughesYoungLocalizedStaticScalar T h k‖ *
              (C * dfiTheorem1ErrorScale P X Y ε)))) * L := by
  obtain ⟨Cγ, C, hCγ, hC, hsource⟩ :=
    exists_uniform_norm_hughesYoungIntegratedPointwiseDFIDiscrepancy_unrestricted
      ε hε0 hε4
  obtain ⟨L, hL, hfactor⟩ :=
    exists_uniform_intervalIntegral_hughesYoungIntegratedOrdinateFactor_le hCγ
  refine ⟨Cγ, C, L, hCγ, hC, hL, ?_⟩
  intro T H X Y P U Q h k M N s hT hH hX hY hh hk hP hU hscale hQ
    hUQ hQsq hM hN hs
  obtain ⟨hc, hc1, hcinv⟩ := hughesYoungSmallContour_spec hT
  have hT1 : 1 ≤ T :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hT
  have hfirst := hsource hT1 hc hc1 hH hX hY hh hk hP hU hscale hQ
    hUQ hQsq hM hN hs
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let E : ℝ := (s.card : ℝ) *
    (‖hughesYoungLocalizedStaticScalar T h k‖ *
      (C * dfiTheorem1ErrorScale P X Y ε))
  let D : ℝ := T * (Real.log T * Real.exp (4 * Cγ) *
    ((a : ℝ) / X) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
    ((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T)) * E
  have hE : 0 ≤ E := by
    dsimp only [E]
    unfold dfiTheorem1ErrorScale
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    have ha : 0 < a := hughesYoungReducedLeft_pos hh
    have hb : 0 < b := hughesYoungReducedRight_pos hh hk
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha
    have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
    have hX0 : 0 < X := zero_lt_one.trans_le hX
    have hY0 : 0 < Y := zero_lt_one.trans_le hY
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
    positivity
  have heq :
      (∫ u in -H..H, T *
        ((s.card : ℝ) *
          (‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization
              (hughesYoungSmallContour T) u X Y
              (hughesYoungSmallLineEnvelope Cγ T
                (hughesYoungSmallContour T) u) a b *
            (C * dfiTheorem1ErrorScale P X Y ε)))) =
        D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ
            (hughesYoungSmallContour T) u) := by
    calc
      (∫ u in -H..H, T *
        ((s.card : ℝ) *
          (‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization
              (hughesYoungSmallContour T) u X Y
              (hughesYoungSmallLineEnvelope Cγ T
                (hughesYoungSmallContour T) u) a b *
            (C * dfiTheorem1ErrorScale P X Y ε)))) =
          ∫ u in -H..H, D *
            hughesYoungIntegratedOrdinateFactor Cγ
              (hughesYoungSmallContour T) u := by
        apply intervalIntegral.integral_congr
        intro u _hu
        simp_rw [hughesYoungScaledDFINormalization_smallLine_eq]
        dsimp only [D, E]
        rw [rpow_smallContour_four_mul_eq Cγ hT, hcinv]
        ring
      _ = D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ
            (hughesYoungSmallContour T) u) := by
        rw [intervalIntegral.integral_const_mul]
  calc
    ‖hughesYoungIntegratedPointwiseDFIDiscrepancy
        T (hughesYoungSmallContour T) H X Y h k M N s‖ ≤
        ∫ u in -H..H, T *
          ((s.card : ℝ) *
            (‖hughesYoungLocalizedStaticScalar T h k‖ *
              hughesYoungScaledDFINormalization
                (hughesYoungSmallContour T) u X Y
                (hughesYoungSmallLineEnvelope Cγ T
                  (hughesYoungSmallContour T) u) a b *
              (C * dfiTheorem1ErrorScale P X Y ε))) := by
          simpa only [a, b] using hfirst
    _ = D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ
            (hughesYoungSmallContour T) u) := heq
    _ ≤ D * L := mul_le_mul_of_nonneg_left (hfactor hc hc1 hH) hD
    _ = _ := by rfl

end RiemannZeta.GuthMaynard
