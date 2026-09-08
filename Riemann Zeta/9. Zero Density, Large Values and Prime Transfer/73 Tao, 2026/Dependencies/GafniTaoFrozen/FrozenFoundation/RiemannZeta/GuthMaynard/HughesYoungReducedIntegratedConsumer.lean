import RiemannZeta.GuthMaynard.HughesYoungReducedFubini
import RiemannZeta.GuthMaynard.HughesYoungIntegratedConsumer

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Integrated DFI theorem in the exact gcd-reduced Hughes--Young coordinates
-/

/-- The complete finite near-shift DFI estimate for the actual localized
Hughes--Young source after its exact gcd reduction. -/
theorem exists_uniform_norm_sum_hughesYoungGCDReducedIntegratedBox_full_dfi
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ Cγ C : ℝ, 0 < Cγ ∧ 0 < C ∧
      ∀ {T c H X Y P U Q : ℝ} {h k M N : ℕ} {s : Finset ℤ},
      1 ≤ T → 0 < c → c ≤ 1 → 0 ≤ H →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k →
      1 ≤ P → U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      ((hughesYoungReducedLeft h k : ℕ) : ℝ) ≤ 2 * X →
      ((hughesYoungReducedRight h k : ℕ) : ℝ) ≤ 2 * Y →
      (∀ r ∈ s,
        r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧
        T * (|(r : ℝ)| / Y) ≤ P ∧
        (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
        (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y)) →
      ‖∑ r ∈ s,
          dfiDyadicShiftedDivisorSum
            (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            M N r‖ ≤
        ∫ u in -H..H, T *
          (∑ r ∈ s,
            ‖hughesYoungLocalizedStaticScalar T h k‖ *
              hughesYoungScaledDFINormalization c u X Y
                (hughesYoungSmallLineEnvelope Cγ T c u)
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) *
              (C * (dfiTheorem1ErrorScale P X Y ε +
                hughesYoungCentralArithmeticScale X Y
                  (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
                  r.natAbs +
                hughesYoungCentralArithmeticScale Y X
                  (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)
                  r.natAbs))) := by
  obtain ⟨Cγ, hCγ, hheight⟩ :=
    exists_norm_one_div_mul_iteratedDeriv_hughesYoungHeightTransform_le
  obtain ⟨C, hC, hdfi⟩ :=
    exists_uniform_norm_hughesYoungReducedCleanedShiftWeight_full_dfi
      ε hε0 hε4
  refine ⟨Cγ, C, hCγ, hC, ?_⟩
  intro T c H X Y P U Q h k M N s hT hc hc1 hH hX hY hh hk hP
    hscale hQ hU hQsq hM hN haX hbY hs
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let A : ℝ → ℝ := hughesYoungSmallLineEnvelope Cγ T c
  let F : ℝ → ℂ := fun u => (T : ℂ) *
    (∑ r ∈ s, dfiDyadicShiftedDivisorSum
      (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) a b M N r)
  let G : ℝ → ℝ := fun u => T *
    (∑ r ∈ s,
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        hughesYoungScaledDFINormalization c u X Y (A u) a b *
        (C * (dfiTheorem1ErrorScale P X Y ε +
          hughesYoungCentralArithmeticScale X Y a b r.natAbs +
          hughesYoungCentralArithmeticScale Y X b a r.natAbs)))
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hApos : ∀ u : ℝ, 0 < A u := fun u =>
    hughesYoungSmallLineEnvelope_pos hT0 hc u
  have hAcont : Continuous A :=
    continuous_hughesYoungSmallLineEnvelope Cγ T c
  have hFcont : Continuous F := by
    exact continuous_const.mul
      (continuous_finsetSum s fun r _ =>
        continuous_dfiDyadicShiftedDivisorSum_reducedCleaned_ordinate
          hT0 hc X Y hh hk ha hb r)
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
    have hraw : ‖∑ r ∈ s,
        dfiDyadicShiftedDivisorSum
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
          a b M N r‖ ≤
        ∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization c u X Y (A u) a b *
            (C * (dfiTheorem1ErrorScale P X Y ε +
              hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs)) := by
      calc
        ‖∑ r ∈ s,
            dfiDyadicShiftedDivisorSum
              (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
              a b M N r‖ ≤
            ∑ r ∈ s, ‖dfiDyadicShiftedDivisorSum
              (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
              a b M N r‖ := norm_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro r hr
          obtain ⟨hr0, hrY, hrP, hrPos, hrNeg⟩ := hs r hr
          simpa only [a, b] using hdfi hT hc hc1 hX hY hh hk hrY hP
            hrP (hApos u) hderiv hscale hQ hU hQsq M N hM hN
            haX hbY hr0 hrPos hrNeg
    dsimp only [F, G]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    exact mul_le_mul_of_nonneg_left hraw hT0.le
  rw [sum_dfiDyadicShiftedDivisorSum_gcdReducedIntegratedBox_eq_integral
    hT0 hc H X Y hh hk ha hb s]
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

/-- Pointwise separation of the ordinate factor when the mollifier scalar
uses the original pair `(h,k)` but the DFI normalization uses the coprime
pair `(a,b)`. -/
theorem hughesYoungReducedIntegratedDFIMajorant_eq
    (Cγ C T c P X Y ε : ℝ) (h k a b : ℕ) (s : Finset ℤ) (u : ℝ) :
    T *
        (∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization c u X Y
              (hughesYoungSmallLineEnvelope Cγ T c u) a b *
            (C * (dfiTheorem1ErrorScale P X Y ε +
              hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs))) =
      (T * (c⁻¹ * T ^ (4 * Cγ * c) *
          ((a : ℝ) / X) ^ ((1 / 2 : ℝ) + c) *
          ((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)) *
        hughesYoungIntegratedDFIArithmeticTotal C T P X Y ε h k a b s) *
          hughesYoungIntegratedOrdinateFactor Cγ c u := by
  simp_rw [hughesYoungScaledDFINormalization_smallLine_eq]
  unfold hughesYoungIntegratedDFIArithmeticTotal
  let D : ℝ := c⁻¹ * T ^ (4 * Cγ * c) *
    ((a : ℝ) / X) ^ ((1 / 2 : ℝ) + c) *
    ((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + c)
  let F : ℤ → ℝ := fun r =>
    ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (C * (dfiTheorem1ErrorScale P X Y ε +
        hughesYoungCentralArithmeticScale X Y a b r.natAbs +
        hughesYoungCentralArithmeticScale Y X b a r.natAbs))
  change T * (∑ r ∈ s,
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (D * hughesYoungIntegratedOrdinateFactor Cγ c u) *
        (C * (dfiTheorem1ErrorScale P X Y ε +
          hughesYoungCentralArithmeticScale X Y a b r.natAbs +
          hughesYoungCentralArithmeticScale Y X b a r.natAbs))) =
    (T * D * ∑ r ∈ s, F r) *
      hughesYoungIntegratedOrdinateFactor Cγ c u
  calc
    T * (∑ r ∈ s,
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (D * hughesYoungIntegratedOrdinateFactor Cγ c u) *
          (C * (dfiTheorem1ErrorScale P X Y ε +
            hughesYoungCentralArithmeticScale X Y a b r.natAbs +
            hughesYoungCentralArithmeticScale Y X b a r.natAbs))) =
      T * (∑ r ∈ s,
        (D * hughesYoungIntegratedOrdinateFactor Cγ c u) * F r) := by
          congr 1
          apply Finset.sum_congr rfl
          intro r _
          dsimp only [F]
          ring
    _ = T * ((D * hughesYoungIntegratedOrdinateFactor Cγ c u) *
        ∑ r ∈ s, F r) := by
          congr 1
          exact (Finset.mul_sum s F
            (D * hughesYoungIntegratedOrdinateFactor Cγ c u)).symm
    _ = (T * D * ∑ r ∈ s, F r) *
        hughesYoungIntegratedOrdinateFactor Cγ c u := by ring

/-- Small-contour version of the reduced near-shift theorem with the
ordinate integral evaluated uniformly. -/
theorem exists_uniform_norm_sum_hughesYoungSmallContourGCDReduced_full_dfi
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ Cγ C L : ℝ, 0 < Cγ ∧ 0 < C ∧ 0 < L ∧
      ∀ {T H X Y P U Q : ℝ} {h k M N : ℕ} {s : Finset ℤ},
      Real.exp 1 ≤ T → 0 ≤ H →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k → 1 ≤ P →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      ((hughesYoungReducedLeft h k : ℕ) : ℝ) ≤ 2 * X →
      ((hughesYoungReducedRight h k : ℕ) : ℝ) ≤ 2 * Y →
      (∀ r ∈ s,
        r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧
        T * (|(r : ℝ)| / Y) ≤ P ∧
        (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
        (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y)) →
      ‖∑ r ∈ s,
          dfiDyadicShiftedDivisorSum
            (hughesYoungGCDReducedIntegratedBoxWeight T
              (hughesYoungSmallContour T) H X Y h k)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            M N r‖ ≤
        (T * (Real.log T * Real.exp (4 * Cγ) *
          ((hughesYoungReducedLeft h k : ℝ) / X) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
          ((hughesYoungReducedRight h k : ℝ) / Y) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
          hughesYoungIntegratedDFIArithmeticTotal C T P X Y ε h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) s) * L := by
  obtain ⟨Cγ, C, hCγ, hC, hsource⟩ :=
    exists_uniform_norm_sum_hughesYoungGCDReducedIntegratedBox_full_dfi
      ε hε0 hε4
  obtain ⟨L, hL, hfactor⟩ :=
    exists_uniform_intervalIntegral_hughesYoungIntegratedOrdinateFactor_le hCγ
  refine ⟨Cγ, C, L, hCγ, hC, hL, ?_⟩
  intro T H X Y P U Q h k M N s hT hH hX hY hh hk hP hscale hQ
    hU hQsq hM hN haX hbY hs
  obtain ⟨hc, hc1, _⟩ := hughesYoungSmallContour_spec hT
  have hT1 : 1 ≤ T :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hT
  have hfirst := hsource hT1 hc hc1 hH hX hY hh hk hP hscale hQ hU hQsq
    hM hN haX hbY hs
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let D : ℝ := T * (Real.log T * Real.exp (4 * Cγ) *
    ((a : ℝ) / X) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
    ((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
    hughesYoungIntegratedDFIArithmeticTotal C T P X Y ε h k a b s
  have hE : 0 ≤ dfiTheorem1ErrorScale P X Y ε := by
    unfold dfiTheorem1ErrorScale
    positivity
  have htotal :
      0 ≤ hughesYoungIntegratedDFIArithmeticTotal C T P X Y ε h k a b s := by
    unfold hughesYoungIntegratedDFIArithmeticTotal
    apply Finset.sum_nonneg
    intro r _
    exact mul_nonneg (norm_nonneg _)
      (mul_nonneg hC.le
        (add_nonneg
          (add_nonneg hE
            (hughesYoungCentralArithmeticScale_nonneg hX hY a b r.natAbs))
          (hughesYoungCentralArithmeticScale_nonneg hY hX b a r.natAbs)))
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hD : 0 ≤ D := by
    dsimp only [D]
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha
    have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
    have hX0 : 0 < X := zero_lt_one.trans_le hX
    have hY0 : 0 < Y := zero_lt_one.trans_le hY
    have hTone : 1 ≤ T :=
      (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hT
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hTone
    have hinner : 0 ≤ Real.log T * Real.exp (4 * Cγ) *
        ((a : ℝ) / X) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
        ((b : ℝ) / Y) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) := by
      positivity
    exact mul_nonneg (mul_nonneg (zero_le_one.trans hTone) hinner) htotal
  have heq :
      (∫ u in -H..H, T *
        (∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization (hughesYoungSmallContour T) u X Y
              (hughesYoungSmallLineEnvelope Cγ T
                (hughesYoungSmallContour T) u) a b *
            (C * (dfiTheorem1ErrorScale P X Y ε +
              hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs)))) =
        D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ
            (hughesYoungSmallContour T) u) := by
    calc
      (∫ u in -H..H, T *
        (∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization (hughesYoungSmallContour T) u X Y
              (hughesYoungSmallLineEnvelope Cγ T
                (hughesYoungSmallContour T) u) a b *
            (C * (dfiTheorem1ErrorScale P X Y ε +
              hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs)))) =
          ∫ u in -H..H, D *
            hughesYoungIntegratedOrdinateFactor Cγ
              (hughesYoungSmallContour T) u := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only [D, a, b]
        rw [hughesYoungReducedIntegratedDFIMajorant_eq]
        rw [rpow_smallContour_four_mul_eq Cγ hT]
        obtain ⟨_, _, hcinv⟩ := hughesYoungSmallContour_spec hT
        rw [hcinv]
      _ = D * (∫ u in -H..H,
          hughesYoungIntegratedOrdinateFactor Cγ
            (hughesYoungSmallContour T) u) := by
        rw [intervalIntegral.integral_const_mul]
  have hsecond :
      (∫ u in -H..H, T *
        (∑ r ∈ s,
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization (hughesYoungSmallContour T) u X Y
              (hughesYoungSmallLineEnvelope Cγ T
                (hughesYoungSmallContour T) u) a b *
            (C * (dfiTheorem1ErrorScale P X Y ε +
              hughesYoungCentralArithmeticScale X Y a b r.natAbs +
              hughesYoungCentralArithmeticScale Y X b a r.natAbs)))) ≤ D * L := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hfactor hc hc1 hH) hD
  dsimp only [a, b, D] at hsecond ⊢
  exact hfirst.trans hsecond

end RiemannZeta.GuthMaynard
