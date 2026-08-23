import RiemannZeta.GuthMaynard.HughesYoungActiveComplementGlobalBound
import RiemannZeta.GuthMaynard.HughesYoungIntegratedSmallContourTail

open Asymptotics Complex Filter Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The active-complement tail on the small Hughes--Young contour

The whole-line contour continuation is already exact.  This file supplies
the missing quantitative estimate on the part of the original small line
outside the physical truncation.  Unlike an arbitrary-strip compactness
bound, the estimate below keeps the `c⁻³` loss explicit; at
`c = 1 / log T` this is only a logarithmic loss.
-/

set_option maxHeartbeats 4000000 in
/-- Explicit positive-shift summand bound on an arbitrary source line
`0 < Re w ≤ 1`.  This is the source-line analogue of the even-opening-line
bound, with the exact `9 c⁻³` contribution from the large physical variable. -/
theorem norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_source_le
    {T c : ℝ} {a b R K : ℕ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) (t u : ℝ) (h k : ℕ) {r q : ℕ} (hr : 0 < r) :
    ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q‖ ≤
      ‖((a : ℂ) * b)⁻¹‖ *
        (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
        ((r : ℝ) *
          (‖z‖ *
            ‖hughesYoungReducedMellinScaleConstantComplex T t
              ((c : ℂ) + (u : ℂ) * I) h k‖ *
            ((r : ℝ) ^ (-(1 + 2 * c : ℝ))) *
            ((2312 * max 1
                (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
                  (-(3 / 4 : ℝ))) + 9 * c⁻¹ ^ 3) *
              (hughesYoungEquation84LogBudget a b r +
                4 * Real.log (q : ℝ)) ^ 2))) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  by_cases hq0 : q = 0
  · subst q
    simp [hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    let delta : ℝ := (1 / hughesYoungDyadicRatio) / (r : ℝ)
    let qx : ℕ := dfiReducedDenominator a q
    let qy : ℕ := dfiReducedDenominator b q
    let S : ℝ := 1 +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖
    let F : ℝ → ℂ := fun x =>
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
        ((r : ℝ) * x + r) ((r : ℝ) * x)
    let J : ℝ → ℂ := fun x => (Set.Ioi delta).indicator F x
    let D : ℝ :=
      ‖z‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k‖ *
        ((r : ℝ) ^ (-(1 + 2 * c : ℝ)))
    have hdelta : 0 < delta := div_pos
      (one_div_pos.mpr hughesYoungDyadicRatio_pos) hrR
    have hGint : Integrable
        (hughesYoungCriticalAffineBetaFullStripMajorant c delta S) :=
      integrable_hughesYoungCriticalAffineBetaFullStripMajorant hc
    have hD0 : 0 ≤ D := by dsimp only [D]; positivity
    have hDGint : Integrable (fun x : ℝ =>
        D * hughesYoungCriticalAffineBetaFullStripMajorant c delta S x) :=
      hGint.const_mul D
    have hJbound (x : ℝ) :
        ‖J x‖ ≤ D *
          hughesYoungCriticalAffineBetaFullStripMajorant c delta S x := by
      by_cases hxmem : x ∈ Set.Ioi delta
      · have hx : 0 < x := hdelta.trans hxmem
        have hsource :=
          norm_dfiEquation27C_scalar_mul_nonLowerActiveComplement_dilate_le
            (T := T) ha hb hR hstrong z t u c h k
              (show (0 : ℝ) ≤ 0 by norm_num) hrR hx qx qy
        have hrpow := norm_hughesYoungDilationPowerPair_horizontal t c u hrR
        have hbeta :=
          norm_hughesYoungCriticalAffineBetaIntegrand_le_fullStripMajorant
            (t := t) (u := u) (c₀ := c) (c := c) (δ := delta) (x := x)
            (CX := (Real.log r : ℂ) + dfiEquation27LogConstant b qy)
            (COne := (Real.log r : ℂ) + dfiEquation27LogConstant a qx)
            hc le_rfl hc1 hdelta hxmem
        have hkernel :
            ‖((r : ℝ) : ℂ) ^ (-(afeCriticalPoint t +
                  (((c - 0 : ℝ) : ℂ) + (u : ℂ) * I))) *
                ((r : ℝ) : ℂ) ^ (-(afeCriticalPoint (-t) +
                  (((c - 0 : ℝ) : ℂ) + (u : ℂ) * I))) *
                hughesYoungCriticalAffineBetaIntegrand t u (c - 0) x
                  ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
                  ((Real.log r : ℂ) + dfiEquation27LogConstant a qx)‖ ≤
              (r : ℝ) ^ (-(1 + 2 * c : ℝ)) *
                hughesYoungCriticalAffineBetaFullStripMajorant c delta S x := by
          simp only [sub_zero]
          rw [norm_mul]
          calc
            ‖((r : ℝ) : ℂ) ^ (-(afeCriticalPoint t +
                    ((c : ℂ) + (u : ℂ) * I))) *
                  ((r : ℝ) : ℂ) ^ (-(afeCriticalPoint (-t) +
                    ((c : ℂ) + (u : ℂ) * I)))‖ *
                ‖hughesYoungCriticalAffineBetaIntegrand t u c x
                    ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
                    ((Real.log r : ℂ) + dfiEquation27LogConstant a qx)‖ ≤
              (r : ℝ) ^ (-(1 + 2 * c : ℝ)) *
                hughesYoungCriticalAffineBetaFullStripMajorant c delta S x := by
                  rw [hrpow]
                  gcongr
            _ = _ := rfl
        have hJ : J x = F x := by simp [J, hxmem]
        rw [hJ]
        simp only [sub_zero, neg_zero, Real.rpow_zero, mul_one] at hsource
        refine hsource.trans ?_
        dsimp only [D]
        have hpre : 0 ≤
            ‖z‖ * ‖hughesYoungReducedMellinScaleConstantComplex T t
              ((c : ℂ) + (u : ℂ) * I) h k‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        have hmul := mul_le_mul_of_nonneg_left hkernel hpre
        simpa only [sub_zero, mul_assoc] using hmul
      · have hJ : J x = 0 := by simp [J, hxmem]
        rw [hJ, norm_zero]
        exact mul_nonneg hD0
          hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
    have hIntRaw := MeasureTheory.norm_integral_le_of_norm_le hDGint
      (Filter.Eventually.of_forall hJbound)
    have hInt :
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ ≤
          D * (2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) * S ^ 2 +
            9 * S ^ 2 * c⁻¹ ^ 3) := by
      calc
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ = ‖∫ x : ℝ, J x‖ := by
          simp only [J, MeasureTheory.integral_indicator measurableSet_Ioi]
        _ ≤ ∫ x : ℝ,
            D * hughesYoungCriticalAffineBetaFullStripMajorant c delta S x :=
          hIntRaw
        _ = D * ∫ x : ℝ,
            hughesYoungCriticalAffineBetaFullStripMajorant c delta S x := by
          rw [MeasureTheory.integral_const_mul]
        _ = D * (2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) * S ^ 2 +
            9 * S ^ 2 * c⁻¹ ^ 3) := by
          rw [integral_hughesYoungCriticalAffineBetaFullStripMajorant_eq hc]
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
    let A : ℝ := hughesYoungEquation84LogBudget a b r
    have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
      have hCX := norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
      have hCOne := norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
      dsimp only [S, A, qx, qy]
      unfold hughesYoungEquation84LogBudget
      linarith
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
      zero_le_one.trans
        (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
    have hCentral :=
      dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
        T t ((c : ℂ) + (u : ℂ) * I) z h k a b qx qy R K hrR
    unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      dfiEquation27CentralSummand
    rw [hCentral]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrR]
    calc
      ‖((a : ℂ) * b)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ((r : ℝ) * ‖∫ x : ℝ in Set.Ioi delta, F x‖) ≤
        ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) *
            (D * (2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) * S ^ 2 +
              9 * S ^ 2 * c⁻¹ ^ 3))) := by gcongr
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) *
            (D * ((2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) +
                9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2))) := by
        gcongr
        calc
          2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) * S ^ 2 +
                9 * S ^ 2 * c⁻¹ ^ 3 =
              (2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) +
                9 * c⁻¹ ^ 3) * S ^ 2 := by ring
          _ ≤ (2312 * max 1 (delta ^ (-(3 / 4 : ℝ))) +
                9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
      _ = _ := by dsimp only [D, delta, A]

/-- The part of the source-line positive-shift estimate independent of the
Ramanujan modulus. -/
noncomputable def hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
    (z : ℂ) (T t u c : ℝ) (h k a b r : ℕ) : ℝ :=
  ‖((a : ℂ) * b)⁻¹‖ * (((a * b * r ^ 2 : ℕ) : ℝ)) * (r : ℝ) *
    (‖z‖ *
      ‖hughesYoungReducedMellinScaleConstantComplex T t
        ((c : ℂ) + (u : ℂ) * I) h k‖ *
      ((r : ℝ) ^ (-(1 + 2 * c : ℝ))) *
      (2312 * max 1
          (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
            (-(3 / 4 : ℝ))) + 9 * c⁻¹ ^ 3))

theorem hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor_nonneg
    (z : ℂ) (T t u : ℝ) {c : ℝ} (hc : 0 < c) (h k a b r : ℕ) :
    0 ≤ hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
      z T t u c h k a b r := by
  unfold hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
  positivity

theorem norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_source_le_prefactor
    {T c : ℝ} {a b R K : ℕ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) (t u : ℝ) (h k : ℕ) {r : ℕ} (hr : 0 < r) (q : ℕ) :
    ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q‖ ≤
      hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
          z T t u c h k a b r *
        (((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
  refine
    (norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_source_le
      hc hc1 ha hb hR hstrong z t u h k hr).trans_eq ?_
  unfold hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
  ring

/-- The complete positive Ramanujan series on the source line, with every
small-contour loss still explicit. -/
theorem norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_source_le
    {T c : ℝ} {a b R K : ℕ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (z : ℂ) (t u : ℝ) (h k : ℕ) {r : ℕ} (hr : 0 < r) :
    ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r‖ ≤
      hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
          z T t u c h k a b r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let C : ℝ :=
    hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
      z T t u c h k a b r
  let F : ℕ → ℂ := fun q =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q
  let M : ℕ → ℝ := fun q =>
    C * (((q : ℝ) ^ 2)⁻¹ * (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hM : Summable M := by
    simpa only [M, mul_assoc] using
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left C
  have hpoint (q : ℕ) : ‖F q‖ ≤ M q := by
    simpa only [F, M, C, A] using
      norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_source_le_prefactor
        hc hc1 ha hb hR hstrong z t u h k hr q
  have hF : Summable F := Summable.of_norm_bounded hM hpoint
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
  change ‖∑' q : ℕ, F q‖ ≤ _
  calc
    ‖∑' q : ℕ, F q‖ ≤ ∑' q : ℕ, ‖F q‖ :=
      norm_tsum_le_tsum_norm hF.norm
    _ ≤ ∑' q : ℕ, M q := hF.norm.tsum_le_tsum hpoint hM
    _ = C * (∑' q : ℕ,
        ((q : ℝ) ^ 2)⁻¹ * (A + 4 * Real.log (q : ℝ)) ^ 2) := by
      rw [tsum_mul_left]
    _ = _ := rfl

/-- Exact positive/negative source-line majorant for one nonzero signed DFI
shift. -/
noncomputable def hughesYoungNonLowerActiveComplementSourceSignedMajorant
    (T t u c : ℝ) (h k a b : ℕ) : ℤ → ℝ
  | Int.ofNat r =>
      hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
          (hughesYoungHeightWeight T t : ℂ) T t u c h k a b r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2)
  | Int.negSucc m =>
      let r := m + 1
      hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
          (hughesYoungHeightWeight T t : ℂ) T (-t) u c k h b a r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget b a r +
            4 * Real.log (q : ℝ)) ^ 2)

theorem hughesYoungNonLowerActiveComplementSourceSignedMajorant_nonneg
    (T t u : ℝ) {c : ℝ} (hc : 0 < c) (h k a b : ℕ) (r : ℤ) :
    0 ≤ hughesYoungNonLowerActiveComplementSourceSignedMajorant
      T t u c h k a b r := by
  cases r with
  | ofNat n =>
      simp only [hughesYoungNonLowerActiveComplementSourceSignedMajorant]
      exact mul_nonneg
        (hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor_nonneg
          (hughesYoungHeightWeight T t : ℂ) T t u hc h k a b n)
        (tsum_nonneg fun _ => mul_nonneg (by positivity) (sq_nonneg _))
  | negSucc m =>
      simp only [hughesYoungNonLowerActiveComplementSourceSignedMajorant]
      exact mul_nonneg
        (hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor_nonneg
          (hughesYoungHeightWeight T t : ℂ) T (-t) u hc k h b a (m + 1))
        (tsum_nonneg fun _ => mul_nonneg (by positivity) (sq_nonneg _))

theorem norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_source_le
    {T c : ℝ} {a b R K : ℕ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (t u : ℝ) (h k : ℕ) {r : ℤ} (hr0 : r ≠ 0) :
    ‖(hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r‖ ≤
      hughesYoungNonLowerActiveComplementSourceSignedMajorant
        T t u c h k a b r := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hn0
        subst n
        exact hr0 rfl
      have heq :=
        heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K n
      change
        ‖(hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementSignedCentralComplex
              T t ((c : ℂ) + (u : ℂ) * I) h k a b R K (n : ℤ)‖ ≤ _
      rw [heq]
      simpa only [hughesYoungNonLowerActiveComplementSourceSignedMajorant,
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex,
        hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex] using
        norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_source_le
          hc hc1 ha hb hR hstrong (hughesYoungHeightWeight T t : ℂ) t u h k hn
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by dsimp only [n]; omega
      have heq :=
        heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K hn
      rw [hrCast, heq,
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive]
      simpa only [hughesYoungNonLowerActiveComplementSourceSignedMajorant] using
        norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_source_le
          hc hc1 hb ha hR (by simpa only [Nat.mul_comm a b] using hstrong)
            (hughesYoungHeightWeight T t : ℂ) (-t) u k h hn

/-- The complete finite signed complement source on the small line is
bounded by the finite sum of its exact signed-shift majorants. -/
theorem norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_source_le
    {T c : ℝ} {a b R K : ℕ} (hc : 0 < c) (hc1 : c ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio * ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (t u : ℝ) (h k : ℕ) :
    ‖(hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedSourceComplex
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K‖ ≤
      ∑ r ∈ hughesYoungShiftInterval a b
          (hughesYoungFullDyadicBound (K + 1))
          (hughesYoungFullDyadicBound (K + 1)),
        if r = 0 then 0 else
          hughesYoungNonLowerActiveComplementSourceSignedMajorant
            T t u c h k a b r := by
  classical
  unfold hughesYoungNonLowerActiveComplementSignedSourceComplex
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro r _hr
  by_cases hr0 : r = 0
  · subst r
    simp
  · simp only [hr0, if_false]
    exact
      norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_source_le
        hc hc1 ha hb hR hstrong t u h k hr0

/-- The exact source-line majorant is dominated by the already-defined pure
small-contour arithmetic coefficient times the completed contour factor and
the explicit beta loss.  Thus the complement introduces no new arithmetic
sum, only one extra shift magnitude and logarithmic powers. -/
theorem hughesYoungNonLowerActiveComplementSourcePositiveMajorant_le_smallContourCoefficient_scalar
    {T : ℝ} (hT : Real.exp 1 ≤ T) {h k r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hr : 0 < r) (z : ℂ) (t u : ℝ) :
    hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
          z T t u
          (hughesYoungSmallContour T) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r +
            4 * Real.log (q : ℝ)) ^ 2) ≤
      hughesYoungSmallContourSignedShiftCoefficient T h k (r : ℤ) *
        (‖z‖ *
          ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ *
          (2312 * max 1
              (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
                (-(3 / 4 : ℝ))) +
            9 * (hughesYoungSmallContour T)⁻¹ ^ 3)) := by
  let c := hughesYoungSmallContour T
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let A := hughesYoungEquation84LogBudget a b r
  let L : ℝ := 2312 * max 1
      (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^ (-(3 / 4 : ℝ))) +
    9 * c⁻¹ ^ 3
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hc : 0 < c := by
    dsimp only [c]
    exact (hughesYoungSmallContour_spec hT).1
  have hprofile := tsum_natCast_inv_sq_mul_four_log_profile_sq_le
    (one_le_hughesYoungEquation84LogBudget a b r)
  have hpref0 : 0 ≤
      hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
        z T t u c h k a b r :=
    hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor_nonneg
      z T t u hc h k a b r
  have hfirst :
      hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
            z T t u c h k a b r *
          (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
            (A + 4 * Real.log (q : ℝ)) ^ 2) ≤
        hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
            z T t u c h k a b r *
          (A ^ 2 * hughesYoungEquation84LogProfileMass) :=
    mul_le_mul_of_nonneg_left hprofile hpref0
  have hscale :
      ‖((a : ℂ) * b)⁻¹‖ *
          ‖hughesYoungReducedMellinScaleConstantComplex T t
            ((c : ℂ) + (u : ℂ) * I) h k‖ =
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2) *
          ‖hughesYoungRightContourWeight t c u‖ := by
    rw [hughesYoungReducedMellinScaleConstantComplex_eq_static_mul_contour,
      norm_mul, hughesYoungRightContourWeightComplex_vertical]
    have hstatic :=
      norm_inv_reduced_mul_hughesYoungReducedMellinStaticComplex_eq
        hh hk T t c u
    calc
      ‖((a : ℂ) * b)⁻¹‖ *
          (‖hughesYoungReducedMellinStaticComplex T t h k
              ((c : ℂ) + (u : ℂ) * I)‖ *
            ‖hughesYoungRightContourWeight t c u‖) =
        ‖((a : ℂ) * b)⁻¹ *
          hughesYoungReducedMellinStaticComplex T t h k
            ((c : ℂ) + (u : ℂ) * I)‖ *
            ‖hughesYoungRightContourWeight t c u‖ := by
              rw [norm_mul]
              ring
      _ = _ := by
        have hmul := congrArg
          (fun x : ℝ => x * ‖hughesYoungRightContourWeight t c u‖) hstatic
        simpa only [a, b] using hmul
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrpow :
      (r : ℝ) ^ (-2 * c) =
        (r : ℝ) * (r : ℝ) ^ (-(1 + 2 * c : ℝ)) := by
    calc
      (r : ℝ) ^ (-2 * c) =
          (r : ℝ) ^ ((1 : ℝ) + (-(1 + 2 * c : ℝ))) := by ring_nf
      _ = (r : ℝ) ^ (1 : ℝ) *
          (r : ℝ) ^ (-(1 + 2 * c : ℝ)) :=
        Real.rpow_add hrR 1 (-(1 + 2 * c : ℝ))
      _ = _ := by rw [Real.rpow_one]
  have hrZ : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcoeff :
      hughesYoungSmallContourSignedShiftCoefficient T h k (r : ℤ) =
        (‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (c - 1 / 2) * (b : ℝ) ^ (c - 1 / 2) *
          (r : ℝ) ^ (-2 * c)) *
        (4 * (((a * b * r ^ 2 : ℕ) : ℝ) * A ^ 2 *
          hughesYoungEquation84LogProfileMass)) := by
    simp only [hughesYoungSmallContourSignedShiftCoefficient, hrZ,
      Int.natCast_nonneg, Int.toNat_natCast, if_false, if_true]
    dsimp only [a, b, A, c]
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hright0 : 0 ≤ ‖z‖ *
      ‖hughesYoungRightContourWeight t c u‖ * L := by positivity
  calc
    _ ≤ hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
          z T t u c h k a b r *
        (A ^ 2 * hughesYoungEquation84LogProfileMass) := hfirst
    _ = (1 / 4 : ℝ) *
        (hughesYoungSmallContourSignedShiftCoefficient T h k (r : ℤ) *
          (‖z‖ *
            ‖hughesYoungRightContourWeight t c u‖ * L)) := by
      rw [hcoeff]
      unfold hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
      rw [show
          ‖((a : ℂ) * b)⁻¹‖ * ↑(a * b * r ^ 2) * (r : ℝ) *
              (‖z‖ *
                ‖hughesYoungReducedMellinScaleConstantComplex T t
                  ((c : ℂ) + (u : ℂ) * I) h k‖ *
                (r : ℝ) ^ (-(1 + 2 * c : ℝ)) * L) *
              (A ^ 2 * hughesYoungEquation84LogProfileMass) =
            (‖((a : ℂ) * b)⁻¹‖ *
              ‖hughesYoungReducedMellinScaleConstantComplex T t
                ((c : ℂ) + (u : ℂ) * I) h k‖) *
              (↑(a * b * r ^ 2) *
                ((r : ℝ) * (r : ℝ) ^ (-(1 + 2 * c : ℝ))) *
                (A ^ 2 * hughesYoungEquation84LogProfileMass) *
                (‖z‖ * L)) by ring,
        hscale, ← hrpow]
      dsimp only [L, A, a, b]
      ring
    _ ≤ hughesYoungSmallContourSignedShiftCoefficient T h k (r : ℤ) *
          (‖z‖ *
            ‖hughesYoungRightContourWeight t c u‖ * L) := by
      have hcoeff0 := hughesYoungSmallContourSignedShiftCoefficient_nonneg
        T h k (r : ℤ)
      nlinarith [mul_nonneg hcoeff0 hright0]

/-- Height-weight specialization of the scalar source comparison. -/
theorem hughesYoungNonLowerActiveComplementSourcePositiveMajorant_le_smallContourCoefficient
    {T : ℝ} (hT : Real.exp 1 ≤ T) {h k r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hr : 0 < r) (t u : ℝ) :
    hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
          (hughesYoungHeightWeight T t : ℂ) T t u
          (hughesYoungSmallContour T) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r +
            4 * Real.log (q : ℝ)) ^ 2) ≤
      hughesYoungSmallContourSignedShiftCoefficient T h k (r : ℤ) *
        (‖hughesYoungHeightWeight T t‖ *
          ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ *
          (2312 * max 1
              (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
                (-(3 / 4 : ℝ))) +
            9 * (hughesYoungSmallContour T)⁻¹ ^ 3)) := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hughesYoungHeightWeight_nonneg T t)] using
    hughesYoungNonLowerActiveComplementSourcePositiveMajorant_le_smallContourCoefficient_scalar
      hT hh hk hr (hughesYoungHeightWeight T t : ℂ) t u

/-- On the physical small contour the explicit beta loss is polynomially
bounded.  The factor `r` is the genuine cost of retaining the complementary
part of the DFI beta integral. -/
theorem hughesYoungComplementBetaLoss_smallContour_le
    {T : ℝ} (hT : Real.exp 4 ≤ T) {r : ℕ} (hr : 0 < r) :
    2312 * max 1
          (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^ (-(3 / 4 : ℝ))) +
        9 * (hughesYoungSmallContour T)⁻¹ ^ 3 ≤
      5009 * (r : ℝ) * T ^ (3 : ℕ) := by
  have hT1 : 1 ≤ T := by
    have hexp : Real.exp 1 ≤ Real.exp 4 := Real.exp_le_exp.mpr (by norm_num)
    linarith [Real.exp_one_gt_two, hexp.trans hT]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hc := hughesYoungSmallContour_spec
    ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT)
  have hbase :=
    RiemannZeta.GuthMaynard.hughesYoungComplementBetaLoss_le_fiveThousand_mul hr
  have hmain :
      2312 * max 1
          (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^ (-(3 / 4 : ℝ))) ≤
        5000 * (r : ℝ) := by
    linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog : Real.log T ≤ T := Real.log_le_self hT0.le
  have hlog3 : (Real.log T) ^ (3 : ℕ) ≤ T ^ (3 : ℕ) :=
    pow_le_pow_left₀ hlog0 hlog 3
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hT3 : 1 ≤ T ^ (3 : ℕ) := one_le_pow₀ hT1
  have hfirst : 5000 * (r : ℝ) ≤
      5000 * (r : ℝ) * T ^ (3 : ℕ) := by
    nlinarith
  have hsecond : 9 * T ^ (3 : ℕ) ≤
      9 * (r : ℝ) * T ^ (3 : ℕ) := by
    have hT30 : 0 ≤ T ^ (3 : ℕ) := by positivity
    nlinarith
  rw [hc.2.2]
  calc
    _ ≤ 5000 * (r : ℝ) + 9 * T ^ (3 : ℕ) := by gcongr
    _ ≤ 5000 * (r : ℝ) * T ^ (3 : ℕ) +
          9 * (r : ℝ) * T ^ (3 : ℕ) := by
      linarith
    _ = 5009 * (r : ℝ) * T ^ (3 : ℕ) := by ring

/-- The positive complementary shift on the small contour has Gaussian
ordinate decay, with its one additional shift magnitude displayed
explicitly. -/
theorem hughesYoungNonLowerActiveComplementSourcePositiveMajorant_le_gaussian
    {C K T : ℝ} (hK : 0 < K)
    (hright : ∀ {T t u : ℝ},
      Real.exp 1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) →
      ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ ≤
        Real.log T * Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2))
    (hT : Real.exp 4 ≤ T) {h k r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hr : 0 < r)
    {t : ℝ} (ht : t ∈ Set.Icc (T / 4) (4 * T)) (u : ℝ) :
    hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
          (hughesYoungHeightWeight T t : ℂ) T t u
          (hughesYoungSmallContour T) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r *
        (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r +
            4 * Real.log (q : ℝ)) ^ 2) ≤
      hughesYoungSmallContourSignedShiftCoefficient T h k (r : ℤ) *
        ((r : ℝ) *
          ((5009 * Real.exp (4 * C) * K) * T ^ (4 : ℕ) *
            Real.exp (-80 * u ^ 2))) := by
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  have hOneT : 1 ≤ T := (Real.one_le_exp (by norm_num)).trans hT1
  have hT0 : 0 < T := zero_lt_one.trans_le hOneT
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hOneT
  have hlog : Real.log T ≤ T := Real.log_le_self hT0.le
  have hcoeff0 := hughesYoungSmallContourSignedShiftCoefficient_nonneg
    T h k (r : ℤ)
  have hheight := hughesYoungHeightWeight_le_one T t
  have hheightNorm : ‖hughesYoungHeightWeight T t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hughesYoungHeightWeight_nonneg T t)]
    exact hheight
  have hweight := hright hT1 ht (u := u)
  have hbeta := hughesYoungComplementBetaLoss_smallContour_le hT hr
  let W : ℝ := Real.log T * Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2)
  let B : ℝ := 5009 * (r : ℝ) * T ^ (3 : ℕ)
  let L : ℝ := 2312 * max 1
      (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^ (-(3 / 4 : ℝ))) +
    9 * (hughesYoungSmallContour T)⁻¹ ^ 3
  have hW0 : 0 ≤ W := by dsimp only [W]; positivity
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hc0 : 0 < hughesYoungSmallContour T :=
    (hughesYoungSmallContour_spec hT1).1
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hinner : ‖hughesYoungHeightWeight T t‖ *
        ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ * L ≤
      1 * W * B := by
    calc
      _ ≤ 1 * ‖hughesYoungRightContourWeight t
            (hughesYoungSmallContour T) u‖ * L := by gcongr
      _ ≤ 1 * W * L := by
        dsimp only [W] at hweight ⊢
        gcongr
      _ ≤ 1 * W * B := by
        dsimp only [L, B] at hbeta ⊢
        exact mul_le_mul_of_nonneg_left hbeta (mul_nonneg zero_le_one hW0)
  have hp : 0 ≤ Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2) *
      (5009 * (r : ℝ) * T ^ (3 : ℕ)) := by positivity
  have hlogmul := mul_le_mul_of_nonneg_right hlog hp
  have hfinal : 1 * W * B ≤
      (r : ℝ) *
        ((5009 * Real.exp (4 * C) * K) * T ^ (4 : ℕ) *
          Real.exp (-80 * u ^ 2)) := by
    calc
      1 * W * B = Real.log T *
          (Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2) *
            (5009 * (r : ℝ) * T ^ (3 : ℕ))) := by
        dsimp only [W, B]
        ring
      _ ≤ T *
          (Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2) *
            (5009 * (r : ℝ) * T ^ (3 : ℕ))) := hlogmul
      _ = _ := by ring
  calc
    _ ≤ hughesYoungSmallContourSignedShiftCoefficient T h k (r : ℤ) *
        (‖hughesYoungHeightWeight T t‖ *
          ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ *
          (2312 * max 1
              (((1 / hughesYoungDyadicRatio) / (r : ℝ)) ^
                (-(3 / 4 : ℝ))) +
            9 * (hughesYoungSmallContour T)⁻¹ ^ 3)) :=
      hughesYoungNonLowerActiveComplementSourcePositiveMajorant_le_smallContourCoefficient
        hT1 hh hk hr t u
    _ ≤ hughesYoungSmallContourSignedShiftCoefficient T h k (r : ℤ) *
        (1 * W * B) := mul_le_mul_of_nonneg_left hinner hcoeff0
    _ ≤ hughesYoungSmallContourSignedShiftCoefficient T h k (r : ℤ) *
        ((r : ℝ) *
          ((5009 * Real.exp (4 * C) * K) * T ^ (4 : ℕ) *
            Real.exp (-80 * u ^ 2))) := by
      exact mul_le_mul_of_nonneg_left hfinal hcoeff0

/-- Uniform Gaussian domination for either sign of a nonzero complementary
shift. -/
theorem exists_hughesYoungNonLowerActiveComplementSourceSignedMajorant_le_gaussian :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ {T t u : ℝ} {h k : ℕ} {r : ℤ},
      Real.exp 4 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) →
      0 < h → 0 < k → r ≠ 0 →
      hughesYoungNonLowerActiveComplementSourceSignedMajorant
          T t u (hughesYoungSmallContour T) h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r ≤
        hughesYoungSmallContourSignedShiftCoefficient T h k r *
          ((r.natAbs : ℝ) *
            (D * T ^ (4 : ℕ) * Real.exp (-80 * u ^ 2))) := by
  obtain ⟨C, K, hC, hK, hright⟩ :=
    exists_norm_hughesYoungRightContourWeight_small_le_gaussian
  let D : ℝ := 5009 * Real.exp (4 * C) * K
  refine ⟨C, D, hC, ?_, ?_⟩
  · dsimp only [D]
    positivity
  · intro T t u h k r hT ht hh hk hr0
    cases r with
    | ofNat n =>
        have hn : 0 < n := by
          apply Nat.pos_of_ne_zero
          intro hn0
          subst n
          exact hr0 rfl
        simpa [hughesYoungNonLowerActiveComplementSourceSignedMajorant, D] using
          hughesYoungNonLowerActiveComplementSourcePositiveMajorant_le_gaussian
            hK hright hT hh hk hn ht u
    | negSucc m =>
        let n : ℕ := m + 1
        have hn : 0 < n := by dsimp only [n]; omega
        have hrEq : Int.negSucc m = -(n : ℤ) := by dsimp only [n]; omega
        have hcompare :=
          hughesYoungNonLowerActiveComplementSourcePositiveMajorant_le_smallContourCoefficient_scalar
            ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT)
            hk hh hn (hughesYoungHeightWeight T t : ℂ) (-t) u
        rw [hughesYoungReducedLeft_swap h k, hughesYoungReducedRight_swap h k]
          at hcompare
        have hrightEq :
            ‖hughesYoungRightContourWeight (-t) (hughesYoungSmallContour T) u‖ =
              ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ := by
          have heq := hughesYoungRightContourWeightComplex_neg t
            (((hughesYoungSmallContour T : ℝ) : ℂ) + (u : ℂ) * I)
          rw [hughesYoungRightContourWeightComplex_vertical,
            hughesYoungRightContourWeightComplex_vertical] at heq
          exact congrArg norm heq.symm
        rw [hrightEq] at hcompare
        have hT1 : Real.exp 1 ≤ T :=
          (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
        have hOneT : 1 ≤ T := (Real.one_le_exp (by norm_num)).trans hT1
        have hT0 : 0 < T := zero_lt_one.trans_le hOneT
        have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hOneT
        have hlog : Real.log T ≤ T := Real.log_le_self hT0.le
        have hweight := hright hT1 ht (u := u)
        have hbeta := hughesYoungComplementBetaLoss_smallContour_le hT hn
        have hcoeff0 := hughesYoungSmallContourSignedShiftCoefficient_nonneg
          T k h (n : ℤ)
        have hheightNorm : ‖hughesYoungHeightWeight T t‖ ≤ 1 := by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (hughesYoungHeightWeight_nonneg T t)]
          exact hughesYoungHeightWeight_le_one T t
        let W : ℝ := Real.log T * Real.exp (4 * C) * K *
          Real.exp (-80 * u ^ 2)
        let B : ℝ := 5009 * (n : ℝ) * T ^ (3 : ℕ)
        let L : ℝ := 2312 * max 1
            (((1 / hughesYoungDyadicRatio) / (n : ℝ)) ^ (-(3 / 4 : ℝ))) +
          9 * (hughesYoungSmallContour T)⁻¹ ^ 3
        have hW0 : 0 ≤ W := by dsimp only [W]; positivity
        have hB0 : 0 ≤ B := by dsimp only [B]; positivity
        have hc0 : 0 < hughesYoungSmallContour T :=
          (hughesYoungSmallContour_spec hT1).1
        have hL0 : 0 ≤ L := by dsimp only [L]; positivity
        have hinner : ‖hughesYoungHeightWeight T t‖ *
              ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ * L ≤
            1 * W * B := by
          calc
            _ ≤ 1 * ‖hughesYoungRightContourWeight t
                  (hughesYoungSmallContour T) u‖ * L := by gcongr
            _ ≤ 1 * W * L := by
              dsimp only [W] at hweight ⊢
              gcongr
            _ ≤ 1 * W * B := by
              dsimp only [L, B] at hbeta ⊢
              exact mul_le_mul_of_nonneg_left hbeta
                (mul_nonneg zero_le_one hW0)
        have hp : 0 ≤ Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2) *
            (5009 * (n : ℝ) * T ^ (3 : ℕ)) := by positivity
        have hlogmul := mul_le_mul_of_nonneg_right hlog hp
        have hfinal : 1 * W * B ≤
            (n : ℝ) *
              (D * T ^ (4 : ℕ) * Real.exp (-80 * u ^ 2)) := by
          calc
            1 * W * B = Real.log T *
                (Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2) *
                  (5009 * (n : ℝ) * T ^ (3 : ℕ))) := by
              dsimp only [W, B]
              ring
            _ ≤ T *
                (Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2) *
                  (5009 * (n : ℝ) * T ^ (3 : ℕ))) := hlogmul
            _ = _ := by dsimp only [D]; ring
        have hbound :
            hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
                  (hughesYoungHeightWeight T t : ℂ) T (-t) u
                  (hughesYoungSmallContour T) k h
                  (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k) n *
                (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
                  (hughesYoungEquation84LogBudget
                      (hughesYoungReducedRight h k)
                      (hughesYoungReducedLeft h k) n +
                    4 * Real.log (q : ℝ)) ^ 2) ≤
              hughesYoungSmallContourSignedShiftCoefficient T k h (n : ℤ) *
                ((n : ℝ) *
                  (D * T ^ (4 : ℕ) * Real.exp (-80 * u ^ 2))) := by
          calc
            _ ≤ hughesYoungSmallContourSignedShiftCoefficient T k h (n : ℤ) *
                (‖hughesYoungHeightWeight T t‖ *
                  ‖hughesYoungRightContourWeight t
                    (hughesYoungSmallContour T) u‖ * L) := by
              simpa only [L, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (hughesYoungHeightWeight_nonneg T t)] using hcompare
            _ ≤ hughesYoungSmallContourSignedShiftCoefficient T k h (n : ℤ) *
                (1 * W * B) := mul_le_mul_of_nonneg_left hinner hcoeff0
            _ ≤ _ := mul_le_mul_of_nonneg_left hfinal hcoeff0
        calc
          hughesYoungNonLowerActiveComplementSourceSignedMajorant
              T t u (hughesYoungSmallContour T) h k
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
                (Int.negSucc m) =
            hughesYoungScalarNonLowerActiveComplementSourcePositivePrefactor
                  (hughesYoungHeightWeight T t : ℂ) T (-t) u
                  (hughesYoungSmallContour T) k h
                  (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k) n *
                (∑' q : ℕ, ((q : ℝ) ^ 2)⁻¹ *
                  (hughesYoungEquation84LogBudget
                      (hughesYoungReducedRight h k)
                      (hughesYoungReducedLeft h k) n +
                    4 * Real.log (q : ℝ)) ^ 2) := by
              simp only [hughesYoungNonLowerActiveComplementSourceSignedMajorant]
              rfl
          _ ≤ hughesYoungSmallContourSignedShiftCoefficient T k h (n : ℤ) *
                ((n : ℝ) *
                  (D * T ^ (4 : ℕ) * Real.exp (-80 * u ^ 2))) := hbound
          _ = hughesYoungSmallContourSignedShiftCoefficient T h k (Int.negSucc m) *
                (((Int.negSucc m).natAbs : ℝ) *
                  (D * T ^ (4 : ℕ) * Real.exp (-80 * u ^ 2))) := by
              rw [hrEq,
                hughesYoungSmallContourSignedShiftCoefficient_neg_eq_swap T h k n hn]
              simp

/-- The exact finite arithmetic mass for the small-contour complement.  In
comparison with the pure equation-(84) mass it contains precisely the one
additional absolute shift factor forced by the complementary beta range. -/
noncomputable def hughesYoungActiveComplementSmallContourShiftMass
    (T : ℝ) (h k K : ℕ) : ℝ :=
  ∑ r ∈ hughesYoungShiftInterval
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
      (hughesYoungFullDyadicBound (K + 1))
      (hughesYoungFullDyadicBound (K + 1)),
    hughesYoungSmallContourSignedShiftCoefficient T h k r * (r.natAbs : ℝ)

theorem hughesYoungActiveComplementSmallContourShiftMass_nonneg
    (T : ℝ) (h k K : ℕ) :
    0 ≤ hughesYoungActiveComplementSmallContourShiftMass T h k K := by
  unfold hughesYoungActiveComplementSmallContourShiftMass
  apply Finset.sum_nonneg
  intro r _hr
  exact mul_nonneg
    (hughesYoungSmallContourSignedShiftCoefficient_nonneg T h k r) (by positivity)

theorem intNatAbs_le_add_mul_of_mem_hughesYoungShiftInterval
    {a b M : ℕ} {r : ℤ}
    (hr : r ∈ hughesYoungShiftInterval a b M M) :
    r.natAbs ≤ (a + b) * M := by
  simp only [hughesYoungShiftInterval, Finset.mem_Icc] at hr
  cases r with
  | ofNat n =>
      have hn : n ≤ a * M := Int.ofNat_le.mp (by
        simpa only [Int.natCast_mul] using hr.2)
      have ha : a * M ≤ (a + b) * M := Nat.mul_le_mul_right M (Nat.le_add_right a b)
      exact hn.trans ha
  | negSucc m =>
      let n : ℕ := m + 1
      have heq : Int.negSucc m = -(n : ℤ) := by dsimp only [n]; omega
      have hn : n ≤ b * M := by
        have hneg : (-(b * M : ℕ) : ℤ) ≤ -(n : ℤ) := by
          simpa only [heq] using hr.1
        exact_mod_cast (neg_le_neg_iff.mp hneg)
      have hb : b * M ≤ (a + b) * M :=
        Nat.mul_le_mul_right M (Nat.le_add_left b a)
      simpa only [n] using hn.trans hb

/-- The weighted complementary mass is at most the pure small-contour mass
times the largest possible signed shift. -/
theorem hughesYoungActiveComplementSmallContourShiftMass_le
    (T : ℝ) (h k K : ℕ) :
    hughesYoungActiveComplementSmallContourShiftMass T h k K ≤
      (((hughesYoungReducedLeft h k + hughesYoungReducedRight h k) *
          hughesYoungFullDyadicBound (K + 1) : ℕ) : ℝ) *
        hughesYoungFiniteSmallContourShiftMass T h k K := by
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let M := hughesYoungFullDyadicBound (K + 1)
  let E : ℝ := ((a + b) * M : ℕ)
  have hE0 : 0 ≤ E := by positivity
  unfold hughesYoungActiveComplementSmallContourShiftMass
  change (∑ r ∈ hughesYoungShiftInterval a b M M,
      hughesYoungSmallContourSignedShiftCoefficient T h k r * (r.natAbs : ℝ)) ≤ _
  calc
    _ ≤ ∑ r ∈ hughesYoungShiftInterval a b M M,
        E * hughesYoungSmallContourSignedShiftCoefficient T h k r := by
      apply Finset.sum_le_sum
      intro r hr
      have hmagNat := intNatAbs_le_add_mul_of_mem_hughesYoungShiftInterval hr
      have hmag : (r.natAbs : ℝ) ≤ E := by
        dsimp only [E]
        exact_mod_cast hmagNat
      have hcoeff0 := hughesYoungSmallContourSignedShiftCoefficient_nonneg T h k r
      nlinarith
    _ = E * hughesYoungFiniteSmallContourShiftMass T h k K := by
      unfold hughesYoungFiniteSmallContourShiftMass
      rw [Finset.mul_sum]
    _ = _ := by rfl

/-- The complete finite complementary source inherits the signed-shift
Gaussian bound, with no cancellation discarded beyond the displayed
weighted arithmetic mass. -/
theorem exists_norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_small_le_gaussian :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {T t u : ℝ} {h k R K : ℕ},
        Real.exp 4 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) →
        0 < h → 0 < k → 0 < R →
        hughesYoungDyadicRatio *
            ((((hughesYoungReducedLeft h k) *
              (hughesYoungReducedRight h k) * R : ℕ) : ℝ)) ≤
          hughesYoungDyadicRatio ^ (K + 1) →
        ‖(hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementSignedSourceComplex
              T t (((hughesYoungSmallContour T : ℝ) : ℂ) + (u : ℂ) * I)
                h k (hughesYoungReducedLeft h k)
                  (hughesYoungReducedRight h k) R K‖ ≤
          hughesYoungActiveComplementSmallContourShiftMass T h k K *
            (D * T ^ (4 : ℕ) * Real.exp (-80 * u ^ 2)) := by
  obtain ⟨C, D, hC, hD, hshift⟩ :=
    exists_hughesYoungNonLowerActiveComplementSourceSignedMajorant_le_gaussian
  refine ⟨C, D, hC, hD, ?_⟩
  intro T t u h k R K hT ht hh hk hR hstrong
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  obtain ⟨hc, hc1, _⟩ := hughesYoungSmallContour_spec hT1
  have hbase :=
    norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_source_le
      (T := T) hc hc1 (hughesYoungReducedLeft_pos hh)
        (hughesYoungReducedRight_pos hh hk) hR hstrong t u h k
  let G : ℝ := D * T ^ (4 : ℕ) * Real.exp (-80 * u ^ 2)
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  calc
    _ ≤ ∑ r ∈ hughesYoungShiftInterval
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound (K + 1))
          (hughesYoungFullDyadicBound (K + 1)),
        if r = 0 then 0 else
          hughesYoungNonLowerActiveComplementSourceSignedMajorant
            T t u (hughesYoungSmallContour T) h k
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r := hbase
    _ ≤ ∑ r ∈ hughesYoungShiftInterval
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound (K + 1))
          (hughesYoungFullDyadicBound (K + 1)),
        (hughesYoungSmallContourSignedShiftCoefficient T h k r *
          (r.natAbs : ℝ)) * G := by
      apply Finset.sum_le_sum
      intro r _hr
      by_cases hr0 : r = 0
      · subst r
        simp
      · simp only [hr0, if_false]
        simpa only [G, mul_assoc] using hshift hT ht hh hk hr0
    _ = hughesYoungActiveComplementSmallContourShiftMass T h k K * G := by
      unfold hughesYoungActiveComplementSmallContourShiftMass
      rw [Finset.sum_mul]
    _ = _ := rfl

/-- Local vertical integrability of the complete finite signed complement.
This is the finite-shift assembly of the already-proved nonzero-shift
vertical integrability theorem. -/
theorem intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (t : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h k : ℕ)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (R K : ℕ) :
    IntervalIntegrable
      (fun u : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedSourceComplex
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K)
      volume (-H) H := by
  classical
  let M := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b M M
  let f : ℤ → ℝ → ℂ := fun r u =>
    (hughesYoungHeightWeight T t : ℂ) *
      (if r = 0 then 0 else
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r)
  have hsum' : IntervalIntegrable (∑ r ∈ S, f r)
      volume (-H) H := by
    apply Finset.sum_induction (s := S) (f := f)
      (p := fun g : ℝ → ℂ => IntervalIntegrable g volume (-H) H)
    · intro g j hg hj
      exact hg.add hj
    · exact (integrable_zero ℝ ℂ volume).intervalIntegrable
    · intro r _hr
      by_cases hr0 : r = 0
      · subst r
        simp [f]
      · simpa only [f, hr0, if_false] using
          intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_vertical
            hc hc1 t hH h k ha hb R K hr0 (T := T)
  apply hsum'.congr
  intro u _hu
  simp only [S, M, f, hughesYoungNonLowerActiveComplementSignedSourceComplex,
    Finset.mul_sum, Finset.sum_apply]

/-- The literal non-lower complementary source is globally Bochner
integrable on the small Hughes--Young line.  Local integrability supplies
measurability on an exhaustion by symmetric compact intervals, while the
quantitative source estimate supplies one integrable Gaussian majorant. -/
theorem integrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_small
    {T t : ℝ} {h k R K : ℕ}
    (hT : Real.exp 4 ≤ T) (ht : t ∈ Set.Icc (T / 4) (4 * T))
    (hh : 0 < h) (hk : 0 < k) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio *
        ((((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ)) ≤
      hughesYoungDyadicRatio ^ (K + 1)) :
    Integrable (fun u : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungNonLowerActiveComplementSignedSourceComplex
        T t (((hughesYoungSmallContour T : ℝ) : ℂ) + (u : ℂ) * I)
          h k (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) R K) := by
  obtain ⟨C, D, hC, hD, hpoint⟩ :=
    exists_norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_small_le_gaussian
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  have hc := hughesYoungSmallContour_spec hT1
  let f : ℝ → ℂ := fun u => (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungNonLowerActiveComplementSignedSourceComplex
      T t (((hughesYoungSmallContour T : ℝ) : ℂ) + (u : ℂ) * I)
        h k (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) R K
  let A : ℝ := hughesYoungActiveComplementSmallContourShiftMass T h k K *
    (D * T ^ (4 : ℕ))
  let g : ℝ → ℝ := fun u => A * Real.exp (-80 * u ^ 2)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (hughesYoungActiveComplementSmallContourShiftMass_nonneg T h k K)
      (mul_nonneg hD.le (by positivity))
  have hg : Integrable g := by
    exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 80)).const_mul A
  have hlocal (n : ℕ) : AEStronglyMeasurable f
      (volume.restrict (Set.Icc (-(n : ℝ)) (n : ℝ))) := by
    have hint :=
      intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical
        (T := T) (a := hughesYoungReducedLeft h k)
          (b := hughesYoungReducedRight h k)
          hc.1 hc.2.1 t (show 0 ≤ (n : ℝ) by positivity) h k
          (hughesYoungReducedLeft_pos hh)
          (hughesYoungReducedRight_pos hh hk) R K
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le
      (show (-(n : ℝ)) ≤ (n : ℝ) by
        have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith)).mp hint).aestronglyMeasurable
  have hunion : (⋃ n : ℕ, Set.Icc (-(n : ℝ)) (n : ℝ)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    refine ⟨n, ?_⟩
    constructor
    · linarith [neg_le_abs x]
    · linarith [le_abs_self x]
  have hfMeas : AEStronglyMeasurable f := by
    have hm := AEStronglyMeasurable.iUnion hlocal
    rw [hunion, Measure.restrict_univ] at hm
    exact hm
  apply hg.mono' hfMeas
  filter_upwards [] with u
  have hp := hpoint hT ht hh hk hR hstrong (u := u)
  simpa only [f, g, A, mul_assoc] using hp

/-- One mollifier pair on the whole literal small contour. -/
noncomputable def hughesYoungNonLowerActiveComplementSmallWholeAtHeight
    (T : ℝ) (h k R K : ℕ) (t : ℝ) : ℂ :=
  ∫ u : ℝ, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungNonLowerActiveComplementSignedSourceComplex
      T t (((hughesYoungSmallContour T : ℝ) : ℂ) + (u : ℂ) * I)
        h k (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) R K

/-- One mollifier pair on a finite segment of the literal small contour. -/
noncomputable def hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
    (T H : ℝ) (h k R K : ℕ) (t : ℝ) : ℂ :=
  ∫ u in -H..H, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungNonLowerActiveComplementSignedSourceComplex
      T t (((hughesYoungSmallContour T : ℝ) : ℂ) + (u : ℂ) * I)
        h k (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) R K

/-- One mollifier pair on the genuine whole even opening line. -/
noncomputable def hughesYoungNonLowerActiveComplementEvenOpeningAtHeight
    (Q : ℕ) (T : ℝ) (h k R K : ℕ) (t : ℝ) : ℂ :=
  ∫ u : ℝ, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungNonLowerActiveComplementSignedSourceComplex
      T t (((((2 * Q : ℕ) : ℝ)) : ℂ) + (u : ℂ) * I)
        h k (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) R K

/-- Exact contour transport identifies the whole literal small line with
the genuine whole even opening line. -/
theorem hughesYoungNonLowerActiveComplementSmallWholeAtHeight_eq_evenOpening
    {T : ℝ} (hT : Real.exp 4 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {h k R K : ℕ} (hh : 0 < h) (hk : 0 < k) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio *
        ((((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ)) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) :
    hughesYoungNonLowerActiveComplementSmallWholeAtHeight T h k R K t =
      hughesYoungNonLowerActiveComplementEvenOpeningAtHeight Q T h k R K t := by
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  have hc := hughesYoungSmallContour_spec hT1
  have hsmall := MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_small
      hT ht hh hk hR hstrong)
    tendsto_neg_atTop_atBot tendsto_id
  have hopen :=
    tendsto_intervalIntegral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_source_to_even
      (show 1 ≤ T by linarith [Real.exp_one_gt_d9]) hc.1 hc.2.1 ht
        (hughesYoungReducedLeft_pos hh)
        (hughesYoungReducedRight_pos hh hk) hR hstrong hQ h k
  exact (tendsto_nhds_unique hopen hsmall).symm

/-- Deleting a symmetric finite segment from the literal complementary
source costs exactly the explicit Gaussian tail furnished by the
source-line estimate. -/
theorem exists_norm_hughesYoungNonLowerActiveComplementSmallWholeAtHeight_sub_finite_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {T t H : ℝ} {h k R K : ℕ},
        Real.exp 4 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) →
        0 < h → 0 < k → 0 < R →
        hughesYoungDyadicRatio *
            ((((hughesYoungReducedLeft h k) *
              (hughesYoungReducedRight h k) * R : ℕ) : ℝ)) ≤
          hughesYoungDyadicRatio ^ (K + 1) →
        0 ≤ H →
        ‖hughesYoungNonLowerActiveComplementSmallWholeAtHeight T h k R K t -
            hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
              T H h k R K t‖ ≤
          hughesYoungActiveComplementSmallContourShiftMass T h k K *
            (D * T ^ (4 : ℕ)) *
              (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
  obtain ⟨C, D, hC, hD, hpoint⟩ :=
    exists_norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_small_le_gaussian
  refine ⟨C, D, hC, hD, ?_⟩
  intro T t H h k R K hT ht hh hk hR hstrong hH
  let f : ℝ → ℂ := fun u => (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungNonLowerActiveComplementSignedSourceComplex
      T t (((hughesYoungSmallContour T : ℝ) : ℂ) + (u : ℂ) * I)
        h k (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) R K
  let A : ℝ := hughesYoungActiveComplementSmallContourShiftMass T h k K *
    (D * T ^ (4 : ℕ))
  have hf :=
    integrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_small
      hT ht hh hk hR hstrong
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (hughesYoungActiveComplementSmallContourShiftMass_nonneg T h k K)
      (mul_nonneg hD.le (by positivity))
  have hg : Integrable (fun u : ℝ => A * Real.exp (-80 * u ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 80)).const_mul A
  unfold hughesYoungNonLowerActiveComplementSmallWholeAtHeight
    hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
  calc
    _ ≤ ∫ u in (Set.Ioc (-H) H)ᶜ, ‖f u‖ :=
      norm_integral_sub_symmetricIntervalIntegral_le_compl_norm hf hH
    _ ≤ ∫ u in (Set.Ioc (-H) H)ᶜ,
        A * Real.exp (-80 * u ^ 2) := by
      apply MeasureTheory.setIntegral_mono_on hf.norm.integrableOn
        hg.integrableOn measurableSet_Ioc.compl
      intro u _hu
      have hp := hpoint hT ht hh hk hR hstrong (u := u)
      simpa only [f, A, mul_assoc] using hp
    _ = A * (∫ u in (Set.Ioc (-H) H)ᶜ,
        Real.exp (-80 * u ^ 2)) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ A * (Real.exp (-40 * H ^ 2) *
          Real.sqrt (Real.pi / 40)) := by
      exact mul_le_mul_of_nonneg_left
        (integral_compl_Ioc_exp_neg_eighty_sq_le hH) hA
    _ = _ := by rfl

/-- The active reassembled source is jointly measurable on the whole
physical-height/Mellin-ordinate plane.  The existing compact-strip
integrability theorem is exhausted in the Mellin coordinate and then
transported through the product-coordinate swap. -/
theorem aestronglyMeasurable_heightWeight_mul_hughesYoungActiveReassembledSignedCentralAtHeight_joint_global
    {T c : ℝ} (hT : 0 < T) (hc : 0 < c)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (R K : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ) *
        hughesYoungActiveReassembledSignedCentralAtHeight
          T p.1 c p.2 h k (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) R K) (volume.prod volume) := by
  let f : ℝ × ℝ → ℂ := fun p =>
    (hughesYoungHeightWeight T p.1 : ℂ) *
      hughesYoungActiveReassembledSignedCentralAtHeight
        T p.1 c p.2 h k (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) R K
  have hlocal (n : ℕ) : AEStronglyMeasurable f
      ((volume.prod volume).restrict
        (Set.univ ×ˢ Set.Ioc (-(n : ℝ)) (n : ℝ))) := by
    have hraw :=
      (integrable_uncurry_heightWeight_mul_hughesYoungActiveReassembledSignedCentralAtHeight
        hT hc (show 0 ≤ (n : ℝ) by positivity) hh hk R K).aestronglyMeasurable.prod_swap
    have hle : (-(n : ℝ)) ≤ (n : ℝ) := by
      have hn0 : (0 : ℝ) ≤ n := by positivity
      linarith
    have huniv : volume.restrict (Set.univ : Set ℝ) = volume :=
      Measure.restrict_univ
    rw [Set.uIoc_of_le hle, ← huniv, Measure.prod_restrict] at hraw
    simpa [f] using hraw
  have hunion : (⋃ n : ℕ,
      (Set.univ : Set ℝ) ×ˢ Set.Ioc (-(n : ℝ)) (n : ℝ)) =
        (Set.univ : Set (ℝ × ℝ)) := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_univ, true_and, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt |p.2|
    refine ⟨n, ?_⟩
    constructor
    · linarith [neg_le_abs p.2]
    · exact (le_abs_self p.2).trans hn.le
  have hm := AEStronglyMeasurable.iUnion hlocal
  rw [hunion, Measure.restrict_univ] at hm
  simpa only [f] using hm

/-- Joint measurability of the literal non-lower complementary source on
the small contour follows from its exact decomposition into the pure,
lower-boundary, and active-reassembled sources. -/
theorem aestronglyMeasurable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralAtHeight_joint
    {T c : ℝ} (hT : 0 < T) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (R K : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralAtHeight
          T p.1 c p.2 h k (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) R K) (volume.prod volume) := by
  have hpure :=
    aestronglyMeasurable_uncurry_hughesYoungFinitePureSignedCentralAtHeight
      (μ := volume) (ν := volume) T hc (hc4.trans_lt (by norm_num))
        (a := hughesYoungReducedLeft h k)
        (b := hughesYoungReducedRight h k)
        hh hk (hughesYoungReducedLeft_pos hh)
          (hughesYoungReducedRight_pos hh hk) K
  have hlower :=
    aestronglyMeasurable_heightWeight_mul_hughesYoungFiniteLowerBoundarySignedCentralAtHeight_joint
      T hc hh hk K
      (a := hughesYoungReducedLeft h k)
      (b := hughesYoungReducedRight h k)
  have hactive :=
    aestronglyMeasurable_heightWeight_mul_hughesYoungActiveReassembledSignedCentralAtHeight_joint_global
      hT hc hh hk R K
  refine (hpure.sub hlower).sub hactive |>.congr ?_
  filter_upwards [] with p
  exact
    (heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralAtHeight_eq
      hT hc hc4 p.1 p.2 hh hk (hughesYoungReducedLeft_pos hh)
        (hughesYoungReducedRight_pos hh hk) R K).symm

/-- The whole small-contour value of one mollifier pair is strongly
measurable as a function of physical height. -/
theorem aestronglyMeasurable_hughesYoungNonLowerActiveComplementSmallWholeAtHeight
    {T : ℝ} (hT : Real.exp 4 ≤ T)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (R K : ℕ) :
    AEStronglyMeasurable
      (hughesYoungNonLowerActiveComplementSmallWholeAtHeight T h k R K) := by
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  have hc := hughesYoungSmallContour_spec hT1
  have hlog4 : 4 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 4) hT
  have hc4 : hughesYoungSmallContour T ≤ 1 / 4 := by
    unfold hughesYoungSmallContour
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlog4
  have hjoint :=
    aestronglyMeasurable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralAtHeight_joint
      ((Real.exp_pos 4).trans_le hT) hc.1 hc4 hh hk R K
  have hout := hjoint.integral_prod_right'
  refine hout.congr ?_
  filter_upwards [] with t
  unfold hughesYoungNonLowerActiveComplementSmallWholeAtHeight
  apply integral_congr_ae
  filter_upwards [] with u
  rw [hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_eq
    T t (hughesYoungSmallContour T) u hh hk
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K]

/-- The finite small-contour value of one mollifier pair is strongly
measurable as a function of physical height. -/
theorem aestronglyMeasurable_hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
    {T : ℝ} (hT : Real.exp 4 ≤ T) {H : ℝ} (hH : 0 ≤ H)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (R K : ℕ) :
    AEStronglyMeasurable
      (hughesYoungNonLowerActiveComplementSmallFiniteAtHeight T H h k R K) := by
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  have hc := hughesYoungSmallContour_spec hT1
  have hlog4 : 4 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 4) hT
  have hc4 : hughesYoungSmallContour T ≤ 1 / 4 := by
    unfold hughesYoungSmallContour
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlog4
  have hjoint :=
    aestronglyMeasurable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralAtHeight_joint
      ((Real.exp_pos 4).trans_le hT) hc.1 hc4 hh hk R K
  have hrestricted : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralAtHeight
          T p.1 (hughesYoungSmallContour T) p.2 h k
            (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K)
      (volume.prod (volume.restrict (Set.Ioc (-H) H))) := by
    have hres := hjoint.restrict
      (s := Set.univ ×ˢ Set.Ioc (-H) H)
    have huniv : volume.restrict (Set.univ : Set ℝ) = volume :=
      Measure.restrict_univ
    rw [← huniv, Measure.prod_restrict]
    simpa using hres
  have hout := hrestricted.integral_prod_right'
  refine hout.congr ?_
  filter_upwards [] with t
  unfold hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
  rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H)]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_eq
    T t (hughesYoungSmallContour T) u hh hk
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K]

/-- The whole small-contour value is Bochner integrable over physical
height, with compact height support and the explicit Gaussian majorant in
the Mellin ordinate. -/
theorem integrable_hughesYoungNonLowerActiveComplementSmallWholeAtHeight
    {T : ℝ} (hT : Real.exp 4 ≤ T)
    {h k R K : ℕ} (hh : 0 < h) (hk : 0 < k) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio *
        ((((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ)) ≤
      hughesYoungDyadicRatio ^ (K + 1)) :
    Integrable
      (hughesYoungNonLowerActiveComplementSmallWholeAtHeight T h k R K) := by
  obtain ⟨C, D, hC, hD, hpoint⟩ :=
    exists_norm_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_small_le_gaussian
  let A : ℝ := hughesYoungActiveComplementSmallContourShiftMass T h k K *
    (D * T ^ (4 : ℕ))
  let B : ℝ := A * ∫ u : ℝ, Real.exp (-80 * u ^ 2)
  let g : ℝ → ℝ := (Set.Icc (T / 4) (4 * T)).indicator (fun _ => B)
  have hp : Integrable (fun u : ℝ => Real.exp (-80 * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (hughesYoungActiveComplementSmallContourShiftMass_nonneg T h k K)
      (mul_nonneg hD.le (by positivity))
  have hpInt : 0 ≤ ∫ u : ℝ, Real.exp (-80 * u ^ 2) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hB : 0 ≤ B := mul_nonneg hA hpInt
  have hg : Integrable g := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hmeas :=
    aestronglyMeasurable_hughesYoungNonLowerActiveComplementSmallWholeAtHeight
      hT hh hk R K
  refine hg.mono' hmeas ?_
  filter_upwards [] with t
  by_cases hw : hughesYoungHeightWeight T t = 0
  · have hzero :
        hughesYoungNonLowerActiveComplementSmallWholeAtHeight T h k R K t = 0 := by
      unfold hughesYoungNonLowerActiveComplementSmallWholeAtHeight
      simp [hw]
    rw [hzero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hB) t
  · have ht := hughesYoungHeightWeight_support
      ((Real.exp_pos 4).trans_le hT) hw
    have hAp : Integrable (fun u : ℝ => A * Real.exp (-80 * u ^ 2)) :=
      hp.const_mul A
    have hinner :
        ‖hughesYoungNonLowerActiveComplementSmallWholeAtHeight T h k R K t‖ ≤ B := by
      unfold hughesYoungNonLowerActiveComplementSmallWholeAtHeight
      apply (norm_integral_le_of_norm_le hAp ?_).trans_eq
      · rw [integral_const_mul]
      · filter_upwards [] with u
        have hs := hpoint hT ht hh hk hR hstrong (u := u)
        simpa only [A, mul_assoc] using hs
    dsimp only [g]
    rw [Set.indicator_of_mem ht]
    exact hinner

/-- The physically truncated small-contour value is Bochner integrable over
height.  This is obtained from the whole value and the now-measurable,
Gaussian-dominated deleted tail. -/
theorem integrable_hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
    {T H : ℝ} (hT : Real.exp 4 ≤ T) (hH : 0 ≤ H)
    {h k R K : ℕ} (hh : 0 < h) (hk : 0 < k) (hR : 0 < R)
    (hstrong : hughesYoungDyadicRatio *
        ((((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ)) ≤
      hughesYoungDyadicRatio ^ (K + 1)) :
    Integrable
      (hughesYoungNonLowerActiveComplementSmallFiniteAtHeight T H h k R K) := by
  have hwhole :=
    integrable_hughesYoungNonLowerActiveComplementSmallWholeAtHeight
      hT hh hk hR hstrong
  have hfiniteMeas :=
    aestronglyMeasurable_hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
      hT hH hh hk R K
  obtain ⟨C, D, hC, hD, htail⟩ :=
    exists_norm_hughesYoungNonLowerActiveComplementSmallWholeAtHeight_sub_finite_le
  let A : ℝ := hughesYoungActiveComplementSmallContourShiftMass T h k K *
    (D * T ^ (4 : ℕ)) *
      (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))
  let g : ℝ → ℝ := (Set.Icc (T / 4) (4 * T)).indicator (fun _ => A)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (hughesYoungActiveComplementSmallContourShiftMass_nonneg T h k K)
        (mul_nonneg hD.le (by positivity)))
      (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
  have hg : Integrable g := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hdiff : Integrable (fun t =>
      hughesYoungNonLowerActiveComplementSmallWholeAtHeight T h k R K t -
        hughesYoungNonLowerActiveComplementSmallFiniteAtHeight T H h k R K t) := by
    refine hg.mono' (hwhole.aestronglyMeasurable.sub hfiniteMeas) ?_
    filter_upwards [] with t
    by_cases hw : hughesYoungHeightWeight T t = 0
    · have hwholeZero :
          hughesYoungNonLowerActiveComplementSmallWholeAtHeight T h k R K t = 0 := by
        unfold hughesYoungNonLowerActiveComplementSmallWholeAtHeight
        simp [hw]
      have hfiniteZero :
          hughesYoungNonLowerActiveComplementSmallFiniteAtHeight T H h k R K t = 0 := by
        unfold hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
        simp [hw]
      rw [hwholeZero, hfiniteZero, sub_zero, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hA) t
    · have ht := hughesYoungHeightWeight_support
        ((Real.exp_pos 4).trans_le hT) hw
      have hfixed := htail hT ht hh hk hR hstrong hH
      dsimp only [g]
      rw [Set.indicator_of_mem ht]
      simpa only [A] using hfixed
  have hfiniteEq :
      hughesYoungNonLowerActiveComplementSmallFiniteAtHeight T H h k R K =
        fun t =>
          hughesYoungNonLowerActiveComplementSmallWholeAtHeight T h k R K t -
            (hughesYoungNonLowerActiveComplementSmallWholeAtHeight T h k R K t -
              hughesYoungNonLowerActiveComplementSmallFiniteAtHeight T H h k R K t) := by
    funext t
    ring
  rw [hfiniteEq]
  exact hwhole.sub hdiff

/-- The complete mollifier-weighted complementary source on the whole
literal small contour. -/
noncomputable def hughesYoungNonLowerActiveComplementSmallWhole
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ,
        hughesYoungNonLowerActiveComplementSmallWholeAtHeight T h k R K t

/-- The complete mollifier-weighted complementary source on a finite
segment of the literal small contour. -/
noncomputable def hughesYoungNonLowerActiveComplementSmallFinite
    (T H : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ,
        hughesYoungNonLowerActiveComplementSmallFiniteAtHeight T H h k R K t

/-- The finite source already used by the native Hughes--Young assembly is
definitionally the finite literal small-contour source after the exact
vertical source identity is applied pairwise. -/
theorem hughesYoungNonLowerActiveComplementSmallFinite_eq_integratedCentralSource
    {T H : ℝ} {R K : ℕ} (hH : H = T / 8) :
    hughesYoungNonLowerActiveComplementSmallFinite T H R K =
      hughesYoungNonLowerActiveComplementIntegratedCentralSource T R K := by
  subst H
  unfold hughesYoungNonLowerActiveComplementSmallFinite
    hughesYoungNonLowerActiveComplementIntegratedCentralSource
    hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
  apply Finset.sum_congr rfl
  intro h hhmem
  apply Finset.sum_congr rfl
  intro k hkmem
  have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
  apply integral_congr_ae
  filter_upwards [] with t
  apply intervalIntegral.integral_congr
  intro u _hu
  change (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungNonLowerActiveComplementSignedSourceComplex
        T t (((hughesYoungSmallContour T : ℝ) : ℂ) + (u : ℂ) * I)
          h k (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) R K =
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungNonLowerActiveComplementSignedCentralAtHeight
        T t (hughesYoungSmallContour T) u h k
          (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) R K
  rw [hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_eq
    T t (hughesYoungSmallContour T) u hh hk
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K]

/-- Exact global contour transport: the whole literal small contour is the
already-defined genuine whole even opening line. -/
theorem hughesYoungNonLowerActiveComplementSmallWhole_eq_evenOpeningWhole
    {T : ℝ} (hT : Real.exp 4 ≤ T) {R K : ℕ} (hR : 0 < R)
    (hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        hughesYoungDyadicRatio *
            (((hughesYoungReducedLeft h k) *
              (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
          hughesYoungDyadicRatio ^ (K + 1))
    {Q : ℕ} (hQ : 0 < Q) :
    hughesYoungNonLowerActiveComplementSmallWhole T R K =
      hughesYoungNonLowerActiveComplementEvenOpeningWhole Q T R K := by
  unfold hughesYoungNonLowerActiveComplementSmallWhole
    hughesYoungNonLowerActiveComplementEvenOpeningWhole
  apply Finset.sum_congr rfl
  intro h hhmem
  apply Finset.sum_congr rfl
  intro k hkmem
  have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
  change (∫ t : ℝ,
      hughesYoungNonLowerActiveComplementSmallWholeAtHeight T h k R K t) =
    ∫ t : ℝ,
      hughesYoungNonLowerActiveComplementEvenOpeningAtHeight Q T h k R K t
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hw : hughesYoungHeightWeight T t = 0
  · unfold hughesYoungNonLowerActiveComplementSmallWholeAtHeight
      hughesYoungNonLowerActiveComplementEvenOpeningAtHeight
    simp [hw]
  · have ht := hughesYoungHeightWeight_support
      ((Real.exp_pos 4).trans_le hT) hw
    exact hughesYoungNonLowerActiveComplementSmallWholeAtHeight_eq_evenOpening
      hT ht hh hk hR (hcover h hhmem k hkmem) hQ

/-- The complete deleted complementary tail between the whole small line
and the physical Hughes--Young truncation. -/
noncomputable def hughesYoungNonLowerActiveComplementSmallContourTail
    (T : ℝ) (R K : ℕ) : ℂ :=
  hughesYoungNonLowerActiveComplementSmallWhole T R K -
    hughesYoungNonLowerActiveComplementIntegratedCentralSource T R K

/-- The total shift-weighted arithmetic mass occurring in the literal
complementary small-contour tail. -/
noncomputable def hughesYoungTerminalActiveComplementSmallContourShiftMass
    (T : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungActiveComplementSmallContourShiftMass
        T h k (hughesYoungGlobalDepth T)

theorem hughesYoungTerminalActiveComplementSmallContourShiftMass_nonneg
    (T : ℝ) :
    0 ≤ hughesYoungTerminalActiveComplementSmallContourShiftMass T := by
  unfold hughesYoungTerminalActiveComplementSmallContourShiftMass
  apply Finset.sum_nonneg
  intro h _hh
  apply Finset.sum_nonneg
  intro k _hk
  exact hughesYoungActiveComplementSmallContourShiftMass_nonneg
    T h k (hughesYoungGlobalDepth T)

/-- The extra absolute-shift weight costs at most `126 T^102` over the
already-controlled pure small-contour mass. -/
theorem hughesYoungTerminalActiveComplementSmallContourShiftMass_le
    {T : ℝ} (hT : Real.exp 4 ≤ T) :
    hughesYoungTerminalActiveComplementSmallContourShiftMass T ≤
      (126 * T ^ (102 : ℕ)) * hughesYoungTerminalSmallContourTotalMass T := by
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  have hT1 : 1 ≤ T := by
    have h14 : Real.exp 1 ≤ Real.exp 4 :=
      Real.exp_le_exp.mpr (by norm_num)
    linarith [Real.exp_one_gt_two, h14.trans hT]
  have hTexp1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  have hcut := detectorCutoff_le_three_mul T hT1
  have hcutSq : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ 9 * T ^ (2 : ℕ) := by
    push_cast
    calc
      (detectorCutoff T : ℝ) ^ 2 ≤ (3 * T) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcut 2
      _ = 9 * T ^ (2 : ℕ) := by ring
  have hfull :
      (hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℝ) ≤
        7 * T ^ (100 : ℕ) :=
    hughesYoungTerminalFullDyadicBound_le_seven_mul_pow_hundred hTexp1
  have hpair : ∀ h ∈ S, ∀ k ∈ S,
      hughesYoungActiveComplementSmallContourShiftMass
          T h k (hughesYoungGlobalDepth T) ≤
        (126 * T ^ (102 : ℕ)) *
          hughesYoungFiniteSmallContourShiftMass
            T h k (hughesYoungGlobalDepth T) := by
    intro h hhmem k hkmem
    have hhCast : (h : ℝ) ≤ 9 * T ^ (2 : ℕ) := by
      have hhCast0 : (h : ℝ) ≤ ((detectorCutoff T) ^ 2 : ℕ) := by
        exact_mod_cast (Finset.mem_Icc.mp hhmem).2
      exact hhCast0.trans hcutSq
    have hkCast : (k : ℝ) ≤ 9 * T ^ (2 : ℕ) := by
      have hkCast0 : (k : ℝ) ≤ ((detectorCutoff T) ^ 2 : ℕ) := by
        exact_mod_cast (Finset.mem_Icc.mp hkmem).2
      exact hkCast0.trans hcutSq
    have haCast : (hughesYoungReducedLeft h k : ℝ) ≤ 9 * T ^ (2 : ℕ) :=
      (by exact_mod_cast hughesYoungReducedLeft_le h k :
        (hughesYoungReducedLeft h k : ℝ) ≤ h).trans hhCast
    have hbCast : (hughesYoungReducedRight h k : ℝ) ≤ 9 * T ^ (2 : ℕ) :=
      (by exact_mod_cast hughesYoungReducedRight_le h k :
        (hughesYoungReducedRight h k : ℝ) ≤ k).trans hkCast
    have hab :
        (hughesYoungReducedLeft h k : ℝ) +
          hughesYoungReducedRight h k ≤
            18 * T ^ (2 : ℕ) := by
      linarith
    have hfactor :
        (((hughesYoungReducedLeft h k +
            hughesYoungReducedRight h k) *
          hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℕ) : ℝ) ≤
            126 * T ^ (102 : ℕ) := by
      push_cast
      calc
        ((hughesYoungReducedLeft h k : ℝ) +
              hughesYoungReducedRight h k) *
            hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) ≤
          (18 * T ^ (2 : ℕ)) * (7 * T ^ (100 : ℕ)) := by
            exact mul_le_mul hab hfull (by positivity) (by positivity)
        _ = 126 * T ^ (102 : ℕ) := by ring
    have hbase :=
      hughesYoungActiveComplementSmallContourShiftMass_le
        T h k (hughesYoungGlobalDepth T)
    exact hbase.trans (mul_le_mul_of_nonneg_right hfactor
      (hughesYoungFiniteSmallContourShiftMass_nonneg
        T h k (hughesYoungGlobalDepth T)))
  unfold hughesYoungTerminalActiveComplementSmallContourShiftMass
    hughesYoungTerminalSmallContourTotalMass
  change (∑ h ∈ S, ∑ k ∈ S,
      hughesYoungActiveComplementSmallContourShiftMass
        T h k (hughesYoungGlobalDepth T)) ≤ _
  calc
    _ ≤ ∑ h ∈ S, ∑ k ∈ S,
        (126 * T ^ (102 : ℕ)) *
          hughesYoungFiniteSmallContourShiftMass
            T h k (hughesYoungGlobalDepth T) := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      exact hpair h hhmem k hkmem
    _ = (126 * T ^ (102 : ℕ)) *
        (∑ h ∈ S, ∑ k ∈ S,
          hughesYoungFiniteSmallContourShiftMass
            T h k (hughesYoungGlobalDepth T)) := by
      simp only [Finset.mul_sum]
    _ = _ := by rfl

/-- After both mollifier sums and the physical-height integration, the
literal active-complement tail has the expected Gaussian truncation loss.
No opening-line estimate is used here: this is the direct source-line
tail required to transport the whole-line cancellation theorem back to the
finite native source. -/
theorem exists_norm_hughesYoungNonLowerActiveComplementSmallContourTail_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {T : ℝ} {R : ℕ}, Real.exp 4 ≤ T → 16 ≤ T → 0 < R →
        (∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            hughesYoungDyadicRatio *
                (((hughesYoungReducedLeft h k) *
                  (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
              hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1)) →
        ‖hughesYoungNonLowerActiveComplementSmallContourTail
            T R (hughesYoungGlobalDepth T)‖ ≤
          (15 * T / 4) *
            hughesYoungTerminalActiveComplementSmallContourShiftMass T *
              (D * T ^ (4 : ℕ)) *
                (Real.exp (-40 * (T / 8) ^ 2) *
                  Real.sqrt (Real.pi / 40)) := by
  obtain ⟨C, D, hC, hD, hpoint⟩ :=
    exists_norm_hughesYoungNonLowerActiveComplementSmallWholeAtHeight_sub_finite_le
  refine ⟨C, D, hC, hD, ?_⟩
  intro T R hT hT16 hR hcover
  have hH : 0 ≤ T / 8 := by linarith
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let E : ℝ := (D * T ^ (4 : ℕ)) *
    (Real.exp (-40 * (T / 8) ^ 2) * Real.sqrt (Real.pi / 40))
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hpair : ∀ h ∈ S, ∀ k ∈ S,
      ‖(∫ t : ℝ,
          hughesYoungNonLowerActiveComplementSmallWholeAtHeight
            T h k R (hughesYoungGlobalDepth T) t) -
        ∫ t : ℝ,
          hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
            T (T / 8) h k R (hughesYoungGlobalDepth T) t‖ ≤
        (15 * T / 4) *
          (hughesYoungActiveComplementSmallContourShiftMass
            T h k (hughesYoungGlobalDepth T) * E) := by
    intro h hhmem k hkmem
    have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
    have hwhole :=
      integrable_hughesYoungNonLowerActiveComplementSmallWholeAtHeight
        hT hh hk hR (hcover h hhmem k hkmem)
    have hfinite :=
      integrable_hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
        hT hH hh hk hR (hcover h hhmem k hkmem)
    let A : ℝ := hughesYoungActiveComplementSmallContourShiftMass
      T h k (hughesYoungGlobalDepth T) * E
    let g : ℝ → ℝ := (Set.Icc (T / 4) (4 * T)).indicator (fun _ => A)
    have hA : 0 ≤ A := mul_nonneg
      (hughesYoungActiveComplementSmallContourShiftMass_nonneg
        T h k (hughesYoungGlobalDepth T)) hE
    have hg : Integrable g := by
      rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const isCompact_Icc.measure_ne_top
    rw [← integral_sub hwhole hfinite]
    apply (norm_integral_le_of_norm_le hg ?_).trans_eq
    · rw [show (∫ t : ℝ, g t) =
          ∫ _t in Set.Icc (T / 4) (4 * T), A by
        exact MeasureTheory.integral_indicator measurableSet_Icc]
      rw [MeasureTheory.setIntegral_const]
      simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ 4 * T - T / 4)]
      ring
    · filter_upwards [] with t
      by_cases hw : hughesYoungHeightWeight T t = 0
      · have hwholeZero :
            hughesYoungNonLowerActiveComplementSmallWholeAtHeight
              T h k R (hughesYoungGlobalDepth T) t = 0 := by
          unfold hughesYoungNonLowerActiveComplementSmallWholeAtHeight
          simp [hw]
        have hfiniteZero :
            hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
              T (T / 8) h k R (hughesYoungGlobalDepth T) t = 0 := by
          unfold hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
          simp [hw]
        rw [hwholeZero, hfiniteZero, sub_zero, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => hA) t
      · have ht := hughesYoungHeightWeight_support
          ((Real.exp_pos 4).trans_le hT) hw
        have hp := hpoint hT ht hh hk hR
          (hcover h hhmem k hkmem) hH
        dsimp only [g]
        rw [Set.indicator_of_mem ht]
        simpa only [A, E, mul_assoc] using hp
  unfold hughesYoungNonLowerActiveComplementSmallContourTail
  rw [← hughesYoungNonLowerActiveComplementSmallFinite_eq_integratedCentralSource
    (T := T) (R := R) (K := hughesYoungGlobalDepth T) rfl]
  unfold hughesYoungNonLowerActiveComplementSmallWhole
    hughesYoungNonLowerActiveComplementSmallFinite
  change ‖(∑ h ∈ S, ∑ k ∈ S,
      ∫ t : ℝ,
        hughesYoungNonLowerActiveComplementSmallWholeAtHeight
          T h k R (hughesYoungGlobalDepth T) t) -
    ∑ h ∈ S, ∑ k ∈ S,
      ∫ t : ℝ,
        hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
          T (T / 8) h k R (hughesYoungGlobalDepth T) t‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ h ∈ S, ∑ k ∈ S,
        ‖(∫ t : ℝ,
            hughesYoungNonLowerActiveComplementSmallWholeAtHeight
              T h k R (hughesYoungGlobalDepth T) t) -
          ∫ t : ℝ,
            hughesYoungNonLowerActiveComplementSmallFiniteAtHeight
              T (T / 8) h k R (hughesYoungGlobalDepth T) t‖ := by
      exact (norm_sum_le _ _).trans <|
        Finset.sum_le_sum fun h _ => norm_sum_le _ _
    _ ≤ ∑ h ∈ S, ∑ k ∈ S,
        (15 * T / 4) *
          (hughesYoungActiveComplementSmallContourShiftMass
            T h k (hughesYoungGlobalDepth T) * E) := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      exact hpair h hhmem k hkmem
    _ = (15 * T / 4) *
          ((∑ h ∈ S, ∑ k ∈ S,
            hughesYoungActiveComplementSmallContourShiftMass
              T h k (hughesYoungGlobalDepth T)) * E) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = (15 * T / 4) *
          hughesYoungTerminalActiveComplementSmallContourShiftMass T *
            (D * T ^ (4 : ℕ)) *
              (Real.exp (-40 * (T / 8) ^ 2) *
                Real.sqrt (Real.pi / 40)) := by
      change (15 * T / 4) *
          (hughesYoungTerminalActiveComplementSmallContourShiftMass T * E) = _
      dsimp only [E]
      ring

/-- The finite truncation error for the literal active complement is
negligible at the native Hughes--Young fourth-moment scale. -/
theorem hughesYoungConductorNonLowerActiveComplementSmallContourTail_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungNonLowerActiveComplementSmallContourTail
        T (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨C, D, hC, hD, htail⟩ :=
    exists_norm_hughesYoungNonLowerActiveComplementSmallContourTail_le
  let M : ℝ := 12 * (5 + 4 * |Real.eulerMascheroniConstant|) ^ 2 *
    hughesYoungEquation84LogProfileMass * 9 ^ (11 : ℕ) * 7 ^ (5 : ℕ)
  let A : ℝ := (15 / 4 : ℝ) * 126 * M * D * Real.sqrt (Real.pi / 40)
  have hM : 0 ≤ M := by
    dsimp only [M]
    have hprofile := hughesYoungEquation84LogProfileMass_pos.le
    positivity
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hbaseRpow : Tendsto (fun T : ℝ =>
      T ^ (629 : ℝ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2))
      atTop (nhds 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
      (by norm_num : (0 : ℝ) < 5 / 8) 629).tendsto_zero_of_tendsto
        (Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg
            (by norm_num : (-(1 / 2 : ℝ)) < 0)))
  have hbase : Tendsto (fun T : ℝ =>
      T ^ (629 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2))
      atTop (nhds 0) := by
    simpa only [← Real.rpow_natCast] using hbaseRpow
  have hlimit : Tendsto (fun T : ℝ =>
      A * (T ^ (629 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hbase.const_mul A
  have hsmall : ∀ᶠ T : ℝ in atTop,
      A * (T ^ (629 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2)) ≤ 1 :=
    (hlimit.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      fun _ h => h.le
  apply IsBigO.of_bound 1
  filter_upwards [hsmall, eventually_ge_atTop (max (Real.exp 4) 16)]
      with T hsmallT hT
  have hTexp4 : Real.exp 4 ≤ T := (le_max_left _ _).trans hT
  have hT16 : 16 ≤ T := (le_max_right _ _).trans hT
  have hT2 : 2 ≤ T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hR : 0 < hughesYoungConductorRadius T :=
    hughesYoungConductorRadius_pos hT1
  have hraw := htail hTexp4 hT16 hR
    (fun h hh k hk => hughesYoungConductor_cover_with_ratio hT2 hh hk)
  have hweighted :=
    hughesYoungTerminalActiveComplementSmallContourShiftMass_le hTexp4
  have hpure :=
    hughesYoungTerminalSmallContourTotalMass_le_pow_fiveHundredTwentyTwo hTexp4
  have hweightedFinal :
      hughesYoungTerminalActiveComplementSmallContourShiftMass T ≤
        (126 * M) * T ^ (624 : ℕ) := by
    calc
      _ ≤ (126 * T ^ (102 : ℕ)) *
          hughesYoungTerminalSmallContourTotalMass T := hweighted
      _ ≤ (126 * T ^ (102 : ℕ)) * (M * T ^ (522 : ℕ)) := by
        gcongr
      _ = (126 * M) * T ^ (624 : ℕ) := by ring
  have hbound :
      ‖hughesYoungNonLowerActiveComplementSmallContourTail
          T (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤
        A * (T ^ (629 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2)) := by
    calc
      _ ≤ (15 * T / 4) *
            hughesYoungTerminalActiveComplementSmallContourShiftMass T *
              (D * T ^ (4 : ℕ)) *
                (Real.exp (-40 * (T / 8) ^ 2) *
                  Real.sqrt (Real.pi / 40)) := hraw
      _ ≤ (15 * T / 4) * ((126 * M) * T ^ (624 : ℕ)) *
            (D * T ^ (4 : ℕ)) *
              (Real.exp (-40 * (T / 8) ^ 2) *
                Real.sqrt (Real.pi / 40)) := by
        gcongr
      _ = A * (T ^ (629 : ℕ) *
            Real.exp (-(5 / 8 : ℝ) * T ^ 2)) := by
        dsimp only [A]
        ring_nf
  have htarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungNonLowerActiveComplementSmallContourTail
        T (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T))), htarget]
  have hone : 1 ≤ 1 * T ^ (1 + ε) := by
    simpa using Real.one_le_rpow hT1 (show 0 ≤ 1 + ε by linarith)
  exact hbound.trans (hsmallT.trans hone)

/-- At the conductor radius, the literal finite complementary source is
the genuine even-opening whole-line source minus its explicitly controlled
small-contour truncation tail. -/
theorem hughesYoungConductorNonLowerActiveComplementIntegratedCentralSource_eq_evenOpening_sub_tail
    {T : ℝ} (hT : Real.exp 4 ≤ T) :
    hughesYoungNonLowerActiveComplementIntegratedCentralSource
        T (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) =
      hughesYoungNonLowerActiveComplementEvenOpeningWhole
          30000 T (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) -
        hughesYoungNonLowerActiveComplementSmallContourTail
          T (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) := by
  have hT2 : 2 ≤ T := by
    have h24 : Real.exp 2 ≤ Real.exp 4 :=
      Real.exp_le_exp.mpr (by norm_num)
    have he2 : 3 < Real.exp 2 := by
      calc
        (3 : ℝ) = 2 + 1 := by norm_num
        _ < Real.exp 2 := Real.add_one_lt_exp (by norm_num)
    linarith [h24.trans hT]
  have hT1 : 1 ≤ T := by linarith
  have hR : 0 < hughesYoungConductorRadius T :=
    hughesYoungConductorRadius_pos hT1
  have hwhole :=
    hughesYoungNonLowerActiveComplementSmallWhole_eq_evenOpeningWhole
      hT hR
        (fun h hh k hk => hughesYoungConductor_cover_with_ratio hT2 hh hk)
        (Q := 30000) (by norm_num)
  unfold hughesYoungNonLowerActiveComplementSmallContourTail
  rw [hwhole]
  ring

/-- The actual finite product-complement source has native
Hughes--Young size.  This is the missing consumer of both the exact
whole-line cancellation theorem and the literal small-contour tail. -/
theorem hughesYoungConductorNonLowerActiveComplementIntegratedCentralSource_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungNonLowerActiveComplementIntegratedCentralSource
        T (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  have hsum :=
    (hughesYoungConductorNonLowerActiveComplementEvenOpeningWhole_epsilonPowerBound.add
      hughesYoungConductorNonLowerActiveComplementSmallContourTail_epsilonPowerBound)
      ε hε
  obtain ⟨C, hC, hbound⟩ := hsum.exists_nonneg
  have hbound' := hbound.bound
  apply IsBigO.of_bound C
  filter_upwards [hbound', eventually_ge_atTop (Real.exp 4)] with T hsumT hT
  have heq :=
    hughesYoungConductorNonLowerActiveComplementIntegratedCentralSource_eq_evenOpening_sub_tail
      hT
  have htri :
      ‖hughesYoungNonLowerActiveComplementIntegratedCentralSource
          T (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤
        ‖hughesYoungNonLowerActiveComplementEvenOpeningWhole
          30000 T (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ +
        ‖hughesYoungNonLowerActiveComplementSmallContourTail
          T (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ := by
    rw [heq]
    exact norm_sub_le _ _
  have hfinal := htri.trans <| by
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (norm_nonneg _) (norm_nonneg _))] using hsumT
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfinal

end RiemannZeta.GuthMaynard
