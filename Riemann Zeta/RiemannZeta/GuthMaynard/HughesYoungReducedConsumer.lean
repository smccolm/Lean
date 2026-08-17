import RiemannZeta.GuthMaynard.HughesYoungReducedCleaning
import RiemannZeta.GuthMaynard.HughesYoungConsumer

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# DFI consumption in the coprime Hughes--Young coordinates
-/

/-- Equation (70) after the exact gcd reduction. -/
noncomputable def hughesYoungReducedCleanedShiftWeight
    (T c u X Y : ℝ) (h k : ℕ) (r : ℤ) (x y : ℝ) : ℂ :=
  (1 / (T : ℂ)) *
    hughesYoungReducedLocalizedStaticWeight T c u X Y h k x y *
      hughesYoungHeightTransform T c u
        (-Real.log (1 + (r : ℝ) / y))

theorem hughesYoungReducedCleanedShiftWeight_eq_heightIntegral
    (T c u X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℤ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hshift : x - y = (r : ℝ)) :
    hughesYoungReducedCleanedShiftWeight T c u X Y h k r x y =
      (1 / (T : ℂ)) *
        (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungReducedLocalizedMellinWeight T t c u X Y h k x y) := by
  unfold hughesYoungReducedCleanedShiftWeight
  rw [← log_div_eq_neg_log_one_add_shift_div hx hy r hshift]
  rw [integral_heightWeight_mul_hughesYoungReducedLocalizedMellinWeight_eq_transform
    T c u X Y hh hk hx hy]
  ring

/-- Exact scalar/core decomposition: the scalar remembers the original
mollifier pair while the DFI core uses its coprime reduction. -/
theorem hughesYoungReducedCleanedShiftWeight_eq_staticScalar_mul_dfiCore
    (T c u X Y : ℝ) (h k : ℕ) (r : ℤ) (x y : ℝ) :
    hughesYoungReducedCleanedShiftWeight T c u X Y h k r x y =
      hughesYoungLocalizedStaticScalar T h k *
        hughesYoungDFICore T c u X Y
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r x y := by
  unfold hughesYoungReducedCleanedShiftWeight
    hughesYoungReducedLocalizedStaticWeight hughesYoungDFICore
    hughesYoungLocalizedLogKernel hughesYoungLocalizedOneFactor
  dsimp only
  ring

/-- The published DFI error applied to the exact gcd-reduced
Hughes--Young equation-(70) weight. -/
theorem exists_uniform_norm_hughesYoungReducedCleanedShiftWeight_scaled_dfiError
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U Q : ℝ} {h k : ℕ} {r : ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y →
      0 < h → 0 < k →
      |(r : ℝ)| ≤ Y / 2 → 1 ≤ P →
      T * (|(r : ℝ)| / Y) ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (M N : ℕ),
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      ((hughesYoungReducedLeft h k : ℕ) : ℝ) ≤ 2 * X →
      ((hughesYoungReducedRight h k : ℕ) : ℝ) ≤ 2 * Y →
      r ≠ 0 →
      (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) →
      (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y) →
      ‖dfiDyadicShiftedDivisorSum
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N r -
        dfiSignedCentralSeries
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)‖ ≤
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          hughesYoungScaledDFINormalization c u X Y A
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) *
          (C * dfiTheorem1ErrorScale P X Y ε) := by
  obtain ⟨C, hC, hBound⟩ :=
    exists_uniform_norm_hughesYoungScaledNormalizedDFICore_dfiError
      ε hε0 hε4
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U Q h k r hT hc hc1 hX hY hh hk hr hP hTR
    hA hheight hscale hQ hU hQsq M N hM hN haX hbY hr0 hrPos hrNeg
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hab : a.Coprime b := hughesYoungReduced_coprime hh
  let S : ℝ := hughesYoungScaledDFINormalization c u X Y A a b
  let z : ℂ := hughesYoungLocalizedStaticScalar T h k * (S : ℂ)
  have hS : 0 < S := hughesYoungScaledDFINormalization_pos
    (c := c) (lt_of_lt_of_le zero_lt_one hX)
    (lt_of_lt_of_le zero_lt_one hY) hA ha hb u
  have hnormalized := hBound hT hc hc1 hX hY ha haX hb hbY hr hP
    hTR hA hheight hscale hQ hU hQsq a b M N ha hb hr0 hab hM hN
    haX hbY hrPos hrNeg
  have hweight :
      hughesYoungReducedCleanedShiftWeight T c u X Y h k r =
        dfiComplexScaleWeight z
          (hughesYoungScaledNormalizedDFICore T c u X Y A a b r) := by
    funext x y
    rw [hughesYoungReducedCleanedShiftWeight_eq_staticScalar_mul_dfiCore]
    rw [hughesYoungDFICore_eq_scaledNormalization_mul_normalized
      (lt_of_lt_of_le zero_lt_one hX)
      (lt_of_lt_of_le zero_lt_one hY) hA ha hb T u r]
    unfold dfiComplexScaleWeight
    dsimp only [z, S, a, b]
    ring
  change ‖dfiDyadicShiftedDivisorSum
      (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) a b M N r -
    dfiSignedCentralSeries a b r
      (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)‖ ≤ _
  rw [hweight]
  have hscaled := norm_dfiSignedDiscrepancy_scale_le z
    (hughesYoungScaledNormalizedDFICore T c u X Y A a b r)
    a b M N r hnormalized
  have hnormz : ‖z‖ = ‖hughesYoungLocalizedStaticScalar T h k‖ * S := by
    dsimp only [z]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hS]
  rw [hnormz] at hscaled
  simpa only [S, a, b] using hscaled

/-! ## Finite reduced near-shift discrepancy -/

/-- The exact finite-family DFI discrepancy in the coprime Hughes--Young
coordinates.  The signed equation-(27) series is retained as the main term;
only the literal DFI Theorem-1 remainder is estimated. -/
theorem exists_uniform_norm_sum_hughesYoungReducedCleanedShiftWeight_dfiDiscrepancy
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U Q : ℝ} {h k : ℕ} {s : Finset ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k →
      1 ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (M N : ℕ),
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      ((hughesYoungReducedLeft h k : ℕ) : ℝ) ≤ 2 * X →
      ((hughesYoungReducedRight h k : ℕ) : ℝ) ≤ 2 * Y →
      (∀ r ∈ s,
        r ≠ 0 ∧
        |(r : ℝ)| ≤ Y / 2 ∧
        T * (|(r : ℝ)| / Y) ≤ P ∧
        (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
        (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y)) →
      ‖(∑ r ∈ s,
          dfiDyadicShiftedDivisorSum
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            M N r) -
        ∑ r ∈ s,
          dfiSignedCentralSeries
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)‖ ≤
        (s.card : ℝ) *
          (‖hughesYoungLocalizedStaticScalar T h k‖ *
            hughesYoungScaledDFINormalization c u X Y A
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) *
            (C * dfiTheorem1ErrorScale P X Y ε)) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_uniform_norm_hughesYoungReducedCleanedShiftWeight_scaled_dfiError
      ε hε0 hε4
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U Q h k s hT hc hc1 hX hY hh hk hP hA
    hheight hscale hQ hU hQsq M N hM hN haX hbY hs
  apply norm_sum_sub_sum_le_card_mul_of_uniform_norm_sub_le
    s
    (fun r => dfiDyadicShiftedDivisorSum
      (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N r)
    (fun r => dfiSignedCentralSeries
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
      (hughesYoungReducedCleanedShiftWeight T c u X Y h k r))
  intro r hr
  obtain ⟨hr0, hrY, hrP, hrPos, hrNeg⟩ := hs r hr
  exact hpoint hT hc hc1 hX hY hh hk hrY hP hrP hA hheight
    hscale hQ hU hQsq M N hM hN haX hbY hr0 hrPos hrNeg

/-- The complete signed equation-(27) series for the reduced source weight. -/
theorem exists_uniform_norm_hughesYoungReducedCleanedShiftWeight_signedCentralSeries :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U : ℝ} {h k : ℕ} {r : ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k →
      r ≠ 0 → |(r : ℝ)| ≤ Y / 2 →
      1 ≤ P → T * (|(r : ℝ)| / Y) ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      0 < U → U ≤ P⁻¹ * min X Y →
      ((hughesYoungReducedLeft h k : ℕ) : ℝ) ≤ 2 * X →
      ((hughesYoungReducedRight h k : ℕ) : ℝ) ≤ 2 * Y →
      ‖dfiSignedCentralSeries
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)‖ ≤
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          hughesYoungScaledDFINormalization c u X Y A
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) *
          (C * (hughesYoungCentralArithmeticScale X Y
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              r.natAbs +
            hughesYoungCentralArithmeticScale Y X
              (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)
              r.natAbs)) := by
  obtain ⟨C, hC, hBound⟩ :=
    exists_uniform_norm_hughesYoungScaledNormalizedDFICore_signedCentralSeries
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U h k r hT hc hc1 hX hY hh hk hr0 hrY
    hP hTR hA hheight hU hscale haX hbY
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  let S : ℝ := hughesYoungScaledDFINormalization c u X Y A a b
  let z : ℂ := hughesYoungLocalizedStaticScalar T h k * (S : ℂ)
  have hS : 0 < S := hughesYoungScaledDFINormalization_pos
    (c := c) (lt_of_lt_of_le zero_lt_one hX)
    (lt_of_lt_of_le zero_lt_one hY) hA ha hb u
  have hnormalized := hBound hT hc hc1 hX hY ha haX hb hbY hr0 hrY
    hP hTR hA hheight hU hscale ha hb
  have hweight :
      hughesYoungReducedCleanedShiftWeight T c u X Y h k r =
        dfiComplexScaleWeight z
          (hughesYoungScaledNormalizedDFICore T c u X Y A a b r) := by
    funext x y
    rw [hughesYoungReducedCleanedShiftWeight_eq_staticScalar_mul_dfiCore]
    rw [hughesYoungDFICore_eq_scaledNormalization_mul_normalized
      (lt_of_lt_of_le zero_lt_one hX)
      (lt_of_lt_of_le zero_lt_one hY) hA ha hb T u r]
    unfold dfiComplexScaleWeight
    dsimp only [z, S, a, b]
    ring
  change ‖dfiSignedCentralSeries a b r
    (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)‖ ≤ _
  rw [hweight, dfiSignedCentralSeries_scale, norm_mul]
  have hnormz : ‖z‖ = ‖hughesYoungLocalizedStaticScalar T h k‖ * S := by
    dsimp only [z]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hS]
  rw [hnormz]
  simpa only [S, a, b] using
    (mul_le_mul_of_nonneg_left hnormalized
      (mul_nonneg (norm_nonneg _) hS.le))

/-- Complete one-shift DFI theorem for the exact coprime-coordinate
Hughes--Young source. -/
theorem exists_uniform_norm_hughesYoungReducedCleanedShiftWeight_full_dfi
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U Q : ℝ} {h k : ℕ} {r : ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k →
      |(r : ℝ)| ≤ Y / 2 → 1 ≤ P →
      T * (|(r : ℝ)| / Y) ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (M N : ℕ),
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      ((hughesYoungReducedLeft h k : ℕ) : ℝ) ≤ 2 * X →
      ((hughesYoungReducedRight h k : ℕ) : ℝ) ≤ 2 * Y →
      r ≠ 0 →
      (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) →
      (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y) →
      ‖dfiDyadicShiftedDivisorSum
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N r‖ ≤
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          hughesYoungScaledDFINormalization c u X Y A
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) *
          (C * (dfiTheorem1ErrorScale P X Y ε +
            hughesYoungCentralArithmeticScale X Y
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              r.natAbs +
            hughesYoungCentralArithmeticScale Y X
              (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)
              r.natAbs)) := by
  obtain ⟨Ce, hCe, hError⟩ :=
    exists_uniform_norm_hughesYoungReducedCleanedShiftWeight_scaled_dfiError
      ε hε0 hε4
  obtain ⟨Cm, hCm, hMain⟩ :=
    exists_uniform_norm_hughesYoungReducedCleanedShiftWeight_signedCentralSeries
  let C : ℝ := Ce + Cm
  refine ⟨C, add_pos hCe hCm, ?_⟩
  intro T c u X Y P A U Q h k r hT hc hc1 hX hY hh hk hrY hP hTR
    hA hheight hscale hQ hU hQsq M N hM hN haX hbY hr0 hrPos hrNeg
  let a : ℕ := hughesYoungReducedLeft h k
  let b : ℕ := hughesYoungReducedRight h k
  let D : ℂ := dfiDyadicShiftedDivisorSum
    (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) a b M N r
  let M0 : ℂ := dfiSignedCentralSeries a b r
    (hughesYoungReducedCleanedShiftWeight T c u X Y h k r)
  let S : ℝ := hughesYoungScaledDFINormalization c u X Y A a b
  let E : ℝ := dfiTheorem1ErrorScale P X Y ε
  let R : ℝ := hughesYoungCentralArithmeticScale X Y a b r.natAbs +
    hughesYoungCentralArithmeticScale Y X b a r.natAbs
  have hU0 : 0 < U := by rw [hU]; positivity
  have hDisc : ‖D - M0‖ ≤
      ‖hughesYoungLocalizedStaticScalar T h k‖ * S * (Ce * E) := by
    dsimp only [D, M0, S, E, a, b]
    exact hError hT hc hc1 hX hY hh hk hrY hP hTR hA hheight hscale
      hQ hU hQsq M N hM hN haX hbY hr0 hrPos hrNeg
  have hCentral : ‖M0‖ ≤
      ‖hughesYoungLocalizedStaticScalar T h k‖ * S * (Cm * R) := by
    dsimp only [M0, S, R, a, b]
    exact hMain hT hc hc1 hX hY hh hk hr0 hrY hP hTR hA hheight
      hU0 hscale haX hbY
  have hE : 0 ≤ E := by
    dsimp only [E, dfiTheorem1ErrorScale]
    positivity
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg
      (hughesYoungCentralArithmeticScale_nonneg hX hY a b r.natAbs)
      (hughesYoungCentralArithmeticScale_nonneg hY hX b a r.natAbs)
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    exact (hughesYoungScaledDFINormalization_pos
      (c := c) (lt_of_lt_of_le zero_lt_one hX)
      (lt_of_lt_of_le zero_lt_one hY) hA
      (hughesYoungReducedLeft_pos hh)
      (hughesYoungReducedRight_pos hh hk) u).le
  have hp : 0 ≤ ‖hughesYoungLocalizedStaticScalar T h k‖ * S :=
    mul_nonneg (norm_nonneg _) hS0
  have hNorm : ‖D‖ ≤ ‖D - M0‖ + ‖M0‖ := by
    have h := norm_add_le (D - M0) M0
    simpa only [sub_add_cancel] using h
  calc
    ‖D‖ ≤ ‖D - M0‖ + ‖M0‖ := hNorm
    _ ≤ ‖hughesYoungLocalizedStaticScalar T h k‖ * S * (Ce * E) +
        ‖hughesYoungLocalizedStaticScalar T h k‖ * S * (Cm * R) :=
      add_le_add hDisc hCentral
    _ ≤ ‖hughesYoungLocalizedStaticScalar T h k‖ * S * (C * E) +
        ‖hughesYoungLocalizedStaticScalar T h k‖ * S * (C * R) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right hCm.le) hE) hp)
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left hCe.le) hR) hp)
    _ = ‖hughesYoungLocalizedStaticScalar T h k‖ * S *
        (C * (E + R)) := by ring
    _ = _ := by
      dsimp only [D, S, E, R, C, a, b]
      ring

end RiemannZeta.GuthMaynard
