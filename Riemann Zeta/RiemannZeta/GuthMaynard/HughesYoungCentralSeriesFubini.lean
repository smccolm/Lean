import RiemannZeta.GuthMaynard.HughesYoungCentralFubini
import RiemannZeta.GuthMaynard.HughesYoungCentralSeriesBounds

open Complex MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

set_option maxHeartbeats 500000

namespace RiemannZeta.GuthMaynard

/-!
# Series-level Fubini for the Hughes--Young central term

This module upgrades the fixed-modulus height-integral identity to the
complete Ramanujan series.  The required Tonelli hypothesis is stated in
the literal form consumed by `MeasureTheory.integral_tsum`; later source
estimates discharge it from the inverse-square DFI coefficient and the two
logarithmic factors.
-/

/-- A reusable Tonelli criterion for a countable family with one common
compact interval of support and a summable real norm majorant. -/
theorem tsum_lintegral_enorm_ne_top_of_summable_bound_Icc
    {F : ℕ → ℝ → ℂ} {A B : ℝ} {g : ℕ → ℝ}
    (hg0 : ∀ q, 0 ≤ g q) (hgsum : Summable g)
    (hsupport : ∀ q, Function.support (F q) ⊆ Set.Icc A B)
    (hbound : ∀ q t, ‖F q t‖ ≤ g q) :
    ∑' q : ℕ, ∫⁻ t : ℝ, ‖F q t‖ₑ ≠ ∞ := by
  let gNN : ℕ → NNReal := fun q => ⟨g q, hg0 q⟩
  have hcoe : Summable (fun q : ℕ => (gNN q : ℝ)) := by
    simpa only [gNN, NNReal.coe_mk] using hgsum
  have htsum : (∑' q : ℕ, (gNN q : ENNReal)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hcoe
  have hterm : ∀ q : ℕ,
      (∫⁻ t : ℝ, ‖F q t‖ₑ) ≤
        (gNN q : ENNReal) * volume (Set.Icc A B) := by
    intro q
    calc
      (∫⁻ t : ℝ, ‖F q t‖ₑ) ≤
          ∫⁻ t : ℝ, (Set.Icc A B).indicator
            (fun _ => (gNN q : ENNReal)) t := by
        apply MeasureTheory.lintegral_mono
        intro t
        by_cases ht : t ∈ Set.Icc A B
        · rw [Set.indicator_of_mem ht]
          change ‖F q t‖ₑ ≤ (gNN q : ENNReal)
          rw [← ofReal_norm, ENNReal.coe_nnreal_eq]
          exact ENNReal.ofReal_le_ofReal (by
            simpa only [gNN, NNReal.coe_mk] using hbound q t)
        · rw [Set.indicator_of_notMem ht]
          have hz : F q t = 0 := by
            by_contra hn
            exact ht (hsupport q (by
              simpa only [Function.mem_support] using hn))
          simp [hz]
      _ = (gNN q : ENNReal) * volume (Set.Icc A B) :=
        MeasureTheory.lintegral_indicator_const measurableSet_Icc _
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top htsum
      (measure_Icc_lt_top (μ := (volume : Measure ℝ))).ne)
  calc
    (∑' q : ℕ, ∫⁻ t : ℝ, ‖F q t‖ₑ) ≤
        ∑' q : ℕ, (gNN q : ENNReal) * volume (Set.Icc A B) :=
      ENNReal.tsum_le_tsum hterm
    _ = (∑' q : ℕ, (gNN q : ENNReal)) * volume (Set.Icc A B) :=
      ENNReal.tsum_mul_right

/-- The height integrand of one modulus term in the positive-shift DFI
central series. -/
noncomputable def hughesYoungCentralSeriesHeightTerm
    (T t c u X Y : ℝ) (h k a b r q : ℕ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    dfiEquation27CentralSummand a b r
      (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) q

/-- Each fixed modulus height term is continuous.  This follows by first
integrating the jointly continuous physical/height kernel over its fixed
compact physical support. -/
theorem continuous_hughesYoungCentralSeriesHeightTerm
    (T : ℝ) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b r q : ℕ) :
    Continuous (fun t : ℝ =>
      hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q) := by
  let J : ℝ → ℝ → ℂ := fun t x =>
    hughesYoungCentralHeightIntegrand T c u X Y h k (r : ℤ) a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) x t
  have hJ : Continuous (Function.uncurry J) := by
    have hbase :=
      continuous_uncurry_hughesYoungCentralHeightIntegrand
        T hc u hX hY hh hk (r : ℤ) a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
    simpa only [J, Function.uncurry_apply_pair] using hbase.comp
      (continuous_snd.prodMk continuous_fst)
  have hset : ∀ t : ℝ,
      (∫ x : ℝ, J t x) = ∫ x in Set.Icc X (2 * X), J t x := by
    intro t
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hweight :
        hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
          x (x - (r : ℝ)) = 0 := by
      have hcut : hughesYoungDyadicCutoffAt X x = 0 := by
        by_contra hn
        exact hx (support_hughesYoungDyadicCutoffAt_subset hX hn)
      unfold hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    dsimp only [J]
    unfold hughesYoungCentralHeightIntegrand dfiEquation27C
    simp [hweight]
  have hint : Continuous (fun t : ℝ => ∫ x : ℝ, J t x) := by
    rw [show (fun t : ℝ => ∫ x : ℝ, J t x) =
        fun t => ∫ x in Set.Icc X (2 * X), J t x by
      funext t
      exact hset t]
    exact continuous_parametric_integral_of_continuous hJ isCompact_Icc
  have heq : (fun t : ℝ =>
      hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q) =
      fun t => (((a : ℂ) * b)⁻¹ *
          dfiEquation27ArithmeticCoefficient a b r q) * ∫ x : ℝ, J t x := by
    funext t
    rw [show (∫ x : ℝ, J t x) =
        (hughesYoungHeightWeight T t : ℂ) *
          ∫ x : ℝ, dfiEquation27C a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)
            x (x - (r : ℝ)) by
      unfold J hughesYoungCentralHeightIntegrand
      rw [MeasureTheory.integral_const_mul]
      simp only [Int.cast_natCast]]
    unfold hughesYoungCentralSeriesHeightTerm
      dfiEquation27CentralSummand dfiEquation27CentralIntegral
    ring
  rw [heq]
  exact continuous_const.mul hint

/-- Every modulus height term has the literal Hughes--Young compact height
support. -/
theorem support_hughesYoungCentralSeriesHeightTerm_subset
    {T : ℝ} (hT : 0 < T) (c u X Y : ℝ)
    (h k a b r q : ℕ) :
    Function.support (fun t : ℝ =>
      hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q) ⊆
      Set.Icc (T / 4) (4 * T) := by
  intro t ht
  have hhgt : hughesYoungHeightWeight T t ≠ 0 := by
    intro hz
    apply ht
    unfold hughesYoungCentralSeriesHeightTerm
    simp [hz]
  exact hughesYoungHeightWeight_support hT hhgt

/-- The summable inverse-square profile carrying both equation-(27)
logarithmic losses. -/
noncomputable def hughesYoungCentralModulusProfile
    (X Y : ℝ) (a b q : ℕ) : ℝ :=
  let A := 1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
    2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
    |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant|
  ((q : ℝ) ^ 2)⁻¹ * (A + 2 * Real.log (q : ℝ)) ^ 2

theorem summable_hughesYoungCentralModulusProfile
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (a b : ℕ) :
    Summable (hughesYoungCentralModulusProfile X Y a b) := by
  let A := 1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
    2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
    |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant|
  have hlogX : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hlogY : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  simpa only [hughesYoungCentralModulusProfile, A] using
    summable_natCast_inv_sq_mul_log_profile_sq A hA

theorem hughesYoungCentralModulusProfile_nonneg
    (X Y : ℝ) (a b q : ℕ) :
    0 ≤ hughesYoungCentralModulusProfile X Y a b q := by
  unfold hughesYoungCentralModulusProfile
  positivity

/-- The part of the height/physical integrand independent of the DFI
modulus and its two logarithmic factors. -/
noncomputable def hughesYoungCentralHeightBase
    (T t c u X Y : ℝ) (h k : ℕ) (r : ℤ) (x : ℝ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
      x (x - (r : ℝ))

theorem continuous_uncurry_hughesYoungCentralHeightBase
    (T : ℝ) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ) :
    Continuous (Function.uncurry
      (fun t x => hughesYoungCentralHeightBase T t c u X Y h k r x)) := by
  have hheight : Continuous (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ)) :=
    Complex.ofRealCLM.continuous.comp
      ((contDiff_hughesYoungHeightWeight T).continuous.comp continuous_fst)
  have hweight0 :=
    continuous_uncurry_hughesYoungReducedLocalizedMellinWeight_on_line_height
      T hc u hX hY hh hk r
  have hweight : Continuous (fun p : ℝ × ℝ =>
      hughesYoungReducedLocalizedMellinWeight T p.1 c u X Y h k
        p.2 (p.2 - (r : ℝ))) := by
    simpa only [Function.uncurry_apply_pair] using hweight0.comp
      (continuous_snd.prodMk continuous_fst)
  unfold Function.uncurry hughesYoungCentralHeightBase
  exact hheight.mul hweight

theorem hughesYoungCentralHeightBase_mem_support_box
    {T : ℝ} (hT : 0 < T) (c u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (r : ℤ) {t x : ℝ}
    (hn : hughesYoungCentralHeightBase T t c u X Y h k r x ≠ 0) :
    t ∈ Set.Icc (T / 4) (4 * T) ∧
      x ∈ Set.Icc X (2 * X) ∧ x - (r : ℝ) ∈ Set.Icc Y (2 * Y) := by
  dsimp only [hughesYoungCentralHeightBase] at hn
  have hheightC : (hughesYoungHeightWeight T t : ℂ) ≠ 0 :=
    left_ne_zero_of_mul hn
  have hheight : hughesYoungHeightWeight T t ≠ 0 := by
    intro hz
    apply hheightC
    simp only [hz, Complex.ofReal_zero]
  have hweight :
      hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
        x (x - (r : ℝ)) ≠ 0 := right_ne_zero_of_mul hn
  have hpair : (x, x - (r : ℝ)) ∈
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
    support_uncurry_hughesYoungReducedLocalizedMellinWeight_subset
      T t c u hX hY h k hweight
  exact ⟨hughesYoungHeightWeight_support hT hheight, hpair.1, hpair.2⟩

/-- Compactness supplies one modulus-independent bound for the exact base
height/physical kernel. -/
theorem exists_uniform_norm_hughesYoungCentralHeightBase_le
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t x : ℝ,
      ‖hughesYoungCentralHeightBase T t c u X Y h k r x‖ ≤ B := by
  let W : C(ℝ × ℝ, ℂ) :=
    ⟨Function.uncurry
      (fun t x => hughesYoungCentralHeightBase T t c u X Y h k r x),
      continuous_uncurry_hughesYoungCentralHeightBase
        T hc u hX hY hh hk r⟩
  let K : TopologicalSpace.Compacts (ℝ × ℝ) :=
    ⟨Set.Icc (T / 4) (4 * T) ×ˢ Set.Icc X (2 * X),
      isCompact_Icc.prod isCompact_Icc⟩
  let B : ℝ := ‖W.restrict K‖
  refine ⟨B, norm_nonneg _, ?_⟩
  intro t x
  by_cases hz : hughesYoungCentralHeightBase T t c u X Y h k r x = 0
  · simp [hz, B]
  · have hmem : (t, x) ∈ (K : Set (ℝ × ℝ)) := by
      have hs := hughesYoungCentralHeightBase_mem_support_box
        hT c u hX hY h k r hz
      exact ⟨hs.1, hs.2.1⟩
    have hraw := ContinuousMap.norm_coe_le_norm (W.restrict K) ⟨(t, x), hmem⟩
    simpa only [W, K, B, ContinuousMap.restrict_apply,
      Function.uncurry_apply_pair] using hraw

/-- Either logarithmic factor in the physical DFI kernel is bounded by
the common positive profile used for the complete modulus series. -/
theorem norm_dfiEquation27LogFactor_reduced_le_centralProfile
    {S R : ℝ} (hS : 1 ≤ S) (hR : 1 ≤ R)
    (a b q : ℕ) (hq : 0 < q) {x : ℝ}
    (hx : x ∈ Set.Icc S (2 * S)) :
    ‖dfiEquation27LogFactor a (dfiReducedDenominator a q) x‖ ≤
      1 + Real.log (2 * S) + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + Real.log (2 * R) +
        |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ) := by
  have hxlog := abs_log_le_log_two_mul_of_mem_Icc hS hx
  have hred := abs_log_dfiReducedDenominator_le a q hq
  have hlogS : 0 ≤ Real.log (2 * S) :=
    Real.log_nonneg (by linarith)
  have hlogR : 0 ≤ Real.log (2 * R) :=
    Real.log_nonneg (by linarith)
  have hbase := norm_dfiEquation27LogFactor_le
    a (dfiReducedDenominator a q) x
  calc
    ‖dfiEquation27LogFactor a (dfiReducedDenominator a q) x‖ ≤
        |Real.log x| + |Real.log (a : ℝ)| +
          2 * |Real.eulerMascheroniConstant| +
          2 * |Real.log (dfiReducedDenominator a q : ℝ)| := hbase
    _ ≤ 1 + Real.log (2 * S) + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + Real.log (2 * R) +
        |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ) := by
      linarith [abs_nonneg (Real.log (b : ℝ)),
        abs_nonneg Real.eulerMascheroniConstant]

/-- The exact physical kernel after the height weight is moved through the
DFI central integral. -/
noncomputable def hughesYoungCentralHeightKernel
    (T t c u X Y : ℝ) (h k a b r q : ℕ) (x : ℝ) : ℂ :=
  dfiEquation27LogFactor a (dfiReducedDenominator a q) x *
    dfiEquation27LogFactor b (dfiReducedDenominator b q) (x - (r : ℝ)) *
    hughesYoungCentralHeightBase T t c u X Y h k (r : ℤ) x

/-- The height term is exactly the arithmetic coefficient times the
integral of the physical height kernel. -/
theorem hughesYoungCentralSeriesHeightTerm_eq_integral_heightKernel
    (T t c u X Y : ℝ) (h k a b r q : ℕ) :
    hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q =
      (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b r q) *
        ∫ x : ℝ,
          hughesYoungCentralHeightKernel T t c u X Y h k a b r q x := by
  unfold hughesYoungCentralSeriesHeightTerm dfiEquation27CentralSummand
    dfiEquation27CentralIntegral hughesYoungCentralHeightKernel
    dfiEquation27C hughesYoungCentralHeightBase
  let A : ℂ := ((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q
  let F : ℝ → ℂ := fun x =>
    dfiEquation27LogFactor a (dfiReducedDenominator a q) x *
      dfiEquation27LogFactor b (dfiReducedDenominator b q) (x - (r : ℝ)) *
      hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
        x (x - (r : ℝ))
  calc
    (hughesYoungHeightWeight T t : ℂ) * (A * ∫ x : ℝ, F x) =
        A * ((hughesYoungHeightWeight T t : ℂ) * ∫ x : ℝ, F x) := by ring
    _ = A * ∫ x : ℝ, (hughesYoungHeightWeight T t : ℂ) * F x := by
      rw [MeasureTheory.integral_const_mul]
    _ = A * ∫ x : ℝ,
        dfiEquation27LogFactor a (dfiReducedDenominator a q) x *
          dfiEquation27LogFactor b (dfiReducedDenominator b q) (x - (r : ℝ)) *
          ((hughesYoungHeightWeight T t : ℂ) *
            hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
              x (x - (r : ℝ))) := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      dsimp only [F]
      ring

/-- Uniform physical-kernel bound with all modulus dependence exposed in
the summable common logarithmic profile. -/
theorem norm_hughesYoungCentralHeightKernel_le
    {T : ℝ} (hT : 0 < T) (c u : ℝ)
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (h k : ℕ) {a b r q : ℕ} (hq : 0 < q)
    {B : ℝ} (hB : 0 ≤ B)
    (hbaseBound : ∀ t x : ℝ,
      ‖hughesYoungCentralHeightBase T t c u X Y h k (r : ℤ) x‖ ≤ B)
    (t x : ℝ) :
      ‖hughesYoungCentralHeightKernel T t c u X Y h k a b r q x‖ ≤
        (1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
          2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
          |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
          2 * Real.log (q : ℝ)) ^ 2 * B := by
  by_cases hz : hughesYoungCentralHeightBase
      T t c u X Y h k (r : ℤ) x = 0
  · rw [show hughesYoungCentralHeightKernel
        T t c u X Y h k a b r q x = 0 by
          simp [hughesYoungCentralHeightKernel, hz]]
    simpa only [norm_zero] using mul_nonneg (sq_nonneg
      (1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
        |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ))) hB
  · have hs := hughesYoungCentralHeightBase_mem_support_box
      hT c u (zero_lt_one.trans_le hX) (zero_lt_one.trans_le hY)
        h k (r : ℤ) hz
    let P : ℝ := 1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
      2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
      |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
      2 * Real.log (q : ℝ)
    have hP : 0 ≤ P := by
      have hlogX : 0 ≤ Real.log (2 * X) :=
        Real.log_nonneg (by linarith)
      have hlogY : 0 ≤ Real.log (2 * Y) :=
        Real.log_nonneg (by linarith)
      have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
      dsimp only [P]
      positivity
    have hleft :
        ‖dfiEquation27LogFactor a (dfiReducedDenominator a q) x‖ ≤ P := by
      simpa only [P] using
        norm_dfiEquation27LogFactor_reduced_le_centralProfile
          hX hY a b q hq hs.2.1
    have hright :
        ‖dfiEquation27LogFactor b (dfiReducedDenominator b q)
          (x - (r : ℝ))‖ ≤ P := by
      have hswap := norm_dfiEquation27LogFactor_reduced_le_centralProfile
        hY hX b a q hq hs.2.2
      dsimp only [P]
      calc
        _ ≤ 1 + Real.log (2 * Y) + |Real.log (b : ℝ)| +
            2 * |Real.eulerMascheroniConstant| + Real.log (2 * X) +
            |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
            2 * Real.log (q : ℝ) := hswap
        _ = _ := by ring
    unfold hughesYoungCentralHeightKernel
    simp only [norm_mul]
    calc
      _ ≤ P * P * B := by gcongr; exact hbaseBound t x
      _ = P ^ 2 * B := by ring

/-- The physical integral of one positive-shift height term has the same
summable logarithmic profile, with the dyadic interval length exactly `X`. -/
theorem norm_integral_hughesYoungCentralHeightKernel_le
    {T : ℝ} (hT : 0 < T) (c u : ℝ)
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (h k : ℕ) {a b r q : ℕ} (hq : 0 < q)
    {B : ℝ} (hB : 0 ≤ B)
    (hbaseBound : ∀ t x : ℝ,
      ‖hughesYoungCentralHeightBase T t c u X Y h k (r : ℤ) x‖ ≤ B)
    (t : ℝ) :
      ‖∫ x : ℝ,
          hughesYoungCentralHeightKernel T t c u X Y h k a b r q x‖ ≤
        X * ((1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
          2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
          |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
          2 * Real.log (q : ℝ)) ^ 2 * B) := by
  have hbound := norm_hughesYoungCentralHeightKernel_le
    hT c u hX hY h k (a := a) (b := b) (r := r) (q := q)
      hq hB hbaseBound
  have heq : (∫ x : ℝ,
      hughesYoungCentralHeightKernel T t c u X Y h k a b r q x) =
      ∫ x in Set.Icc X (2 * X),
        hughesYoungCentralHeightKernel T t c u X Y h k a b r q x := by
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hweight :
        hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
          x (x - (r : ℝ)) = 0 := by
      have hcut : hughesYoungDyadicCutoffAt X x = 0 := by
        by_contra hn
        exact hx (support_hughesYoungDyadicCutoffAt_subset
          (zero_lt_one.trans_le hX) hn)
      unfold hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    unfold hughesYoungCentralHeightKernel hughesYoungCentralHeightBase
    simp [hweight]
  rw [heq]
  have hset := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume) (s := Set.Icc X (2 * X))
    (C := (1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
      2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
      |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
      2 * Real.log (q : ℝ)) ^ 2 * B)
    (f := hughesYoungCentralHeightKernel T t c u X Y h k a b r q)
    measure_Icc_lt_top (fun x _hx => hbound t x)
  rw [Real.volume_real_Icc_of_le (by linarith : X ≤ 2 * X)] at hset
  calc
    _ ≤ ((1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
        |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ)) ^ 2 * B) * X := by
      convert hset using 1
      ring
    _ = _ := by ring

/-- One constant bounds every height and every DFI modulus term by the
explicit summable inverse-square/log-squared profile. -/
theorem exists_uniform_norm_hughesYoungCentralSeriesHeightTerm_le_profile
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ q : ℕ, ∀ t : ℝ,
      ‖hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q‖ ≤
        D * hughesYoungCentralModulusProfile X Y a b q := by
  obtain ⟨B, hB, hbaseBound⟩ :=
    exists_uniform_norm_hughesYoungCentralHeightBase_le
      hT hc u (zero_lt_one.trans_le hX) (zero_lt_one.trans_le hY)
        hh hk (r : ℤ)
  let D : ℝ := ‖(((a : ℂ) * b)⁻¹)‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * X * B
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro q t
  by_cases hq₀ : q = 0
  · subst q
    simp [hughesYoungCentralSeriesHeightTerm,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient,
      hughesYoungCentralModulusProfile]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq₀
    letI : NeZero q := ⟨hq₀⟩
    have hCoeff := norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
      a b r q ha hb hr
    have hIntegral := norm_integral_hughesYoungCentralHeightKernel_le
      hT c u hX hY h k (a := a) (b := b) (r := r) (q := q)
        hq hB hbaseBound t
    rw [hughesYoungCentralSeriesHeightTerm_eq_integral_heightKernel]
    simp only [norm_mul]
    calc
      ‖(((a : ℂ) * b)⁻¹)‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ‖∫ x : ℝ,
            hughesYoungCentralHeightKernel T t c u X Y h k a b r q x‖ ≤
        ‖(((a : ℂ) * b)⁻¹)‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          (X * ((1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
            2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
            |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
            2 * Real.log (q : ℝ)) ^ 2 * B)) := by
          gcongr
      _ = D * hughesYoungCentralModulusProfile X Y a b q := by
        dsimp only [D, hughesYoungCentralModulusProfile]
        ring

/-- Exact interchange of the DFI Ramanujan series and the Hughes--Young
height integral.  The second hypothesis is precisely the Tonelli
summability obligation; no convergence is inferred from the formal
existence of either side. -/
theorem dfiEquation27CentralSeries_reducedCleaned_eq_heightIntegral_of_tonelli
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b r : ℕ)
    (htonelli :
      ∑' q : ℕ, ∫⁻ t : ℝ,
        ‖hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q‖ₑ ≠ ∞) :
    dfiEquation27CentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ)) =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSeries a b r
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) := by
  let F : ℕ → ℝ → ℂ := fun q t =>
    hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q
  have hmeas : ∀ q : ℕ, AEStronglyMeasurable (F q) := by
    intro q
    exact (continuous_hughesYoungCentralSeriesHeightTerm
      T hc u hX hY hh hk a b r q).aestronglyMeasurable
  have hswap : (∫ t : ℝ, ∑' q : ℕ, F q t) =
      ∑' q : ℕ, ∫ t : ℝ, F q t := by
    exact MeasureTheory.integral_tsum hmeas (by simpa only [F] using htonelli)
  unfold dfiEquation27CentralSeries
  simp_rw [dfiEquation27CentralSummand_reducedCleaned_eq_heightIntegral
    hT hc u hX hY hh hk r]
  calc
    (∑' q : ℕ, (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSummand a b r
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) q) =
      (1 / (T : ℂ)) * ∑' q : ℕ, ∫ t : ℝ, F q t := by
        rw [tsum_mul_left]
        rfl
    _ = (1 / (T : ℂ)) * ∫ t : ℝ, ∑' q : ℕ, F q t := by rw [hswap]
    _ = (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          ∑' q : ℕ, dfiEquation27CentralSummand a b r
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) q := by
      apply congrArg ((1 / (T : ℂ)) * ·)
      apply integral_congr_ae
      filter_upwards with t
      unfold F hughesYoungCentralSeriesHeightTerm
      rw [tsum_mul_left]

/-- The exact DFI inverse-square coefficient bound and compact
Hughes--Young support discharge the Tonelli condition for the complete
positive-shift central series. -/
theorem tsum_lintegral_enorm_hughesYoungCentralSeriesHeightTerm_ne_top
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∑' q : ℕ, ∫⁻ t : ℝ,
      ‖hughesYoungCentralSeriesHeightTerm T t c u X Y h k a b r q‖ₑ ≠ ∞ := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_uniform_norm_hughesYoungCentralSeriesHeightTerm_le_profile
      hT hc u hX hY hh hk ha hb hr
  apply tsum_lintegral_enorm_ne_top_of_summable_bound_Icc
    (g := fun q => D * hughesYoungCentralModulusProfile X Y a b q)
  · intro q
    exact mul_nonneg hD (hughesYoungCentralModulusProfile_nonneg X Y a b q)
  · exact (summable_hughesYoungCentralModulusProfile hX hY a b).mul_left D
  · intro q
    exact support_hughesYoungCentralSeriesHeightTerm_subset
      hT c u X Y h k a b r q
  · exact hbound

/-- Unconditional series-level Fubini for the exact positive-shift
Hughes--Young/DFI central term. -/
theorem dfiEquation27CentralSeries_reducedCleaned_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    dfiEquation27CentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ)) =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSeries a b r
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) := by
  exact dfiEquation27CentralSeries_reducedCleaned_eq_heightIntegral_of_tonelli
    hT hc u (zero_lt_one.trans_le hX) (zero_lt_one.trans_le hY) hh hk a b r
      (tsum_lintegral_enorm_hughesYoungCentralSeriesHeightTerm_ne_top
        hT hc u hX hY hh hk ha hb hr)

end RiemannZeta.GuthMaynard
