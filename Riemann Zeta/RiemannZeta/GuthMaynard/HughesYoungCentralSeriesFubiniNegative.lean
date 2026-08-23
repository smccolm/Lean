import RiemannZeta.GuthMaynard.HughesYoungCentralSeriesFubini

open Complex Filter MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

set_option maxHeartbeats 500000

namespace RiemannZeta.GuthMaynard

/-!
# Series-level Fubini for the negative Hughes--Young central term

This is the coordinate-swapped companion of the positive-shift theorem.
It retains the source convention: a negative original shift of magnitude
`r` is represented by the positive central line for coefficients `b,a`
and the swapped physical weight.
-/

noncomputable def hughesYoungNegativeCentralSeriesHeightTerm
    (T t c u X Y : ℝ) (h k a b r q : ℕ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    dfiEquation27CentralSummand b a r
      (dfiSwapWeight
        (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) q

noncomputable def hughesYoungNegativeCentralHeightBase
    (T t c u X Y : ℝ) (h k : ℕ) (r : ℤ) (x : ℝ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
      (x - (r : ℝ)) x

noncomputable def hughesYoungNegativeCentralHeightIntegrand
    (T c u X Y : ℝ) (h k : ℕ) (r : ℕ)
    (a b qx qy : ℕ) (x t : ℝ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    dfiEquation27C b a qx qy
      (dfiSwapWeight
        (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k))
      x (x - (r : ℝ))

theorem continuous_uncurry_hughesYoungNegativeCentralHeightIntegrand
    (T : ℝ) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℕ)
    (a b qx qy : ℕ) :
    Continuous (Function.uncurry
      (hughesYoungNegativeCentralHeightIntegrand
        T c u X Y h k r a b qx qy)) := by
  have hbase := continuous_uncurry_hughesYoungCentralHeightIntegrand
    T hc u hX hY hh hk (-(r : ℤ)) a b qy qx
  have hmap : Continuous (fun p : ℝ × ℝ =>
      (p.1 - (r : ℝ), p.2)) := by fun_prop
  have hcomp := hbase.comp hmap
  convert hcomp using 1
  funext p
  unfold Function.comp Function.uncurry
    hughesYoungNegativeCentralHeightIntegrand
    hughesYoungCentralHeightIntegrand dfiEquation27C dfiSwapWeight
  simp only [Int.cast_neg, Int.cast_natCast]
  ring

theorem support_uncurry_hughesYoungNegativeCentralHeightIntegrand_subset
    {T : ℝ} (hT : 0 < T) (c u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k r a b qx qy : ℕ) :
    Function.support (Function.uncurry
      (hughesYoungNegativeCentralHeightIntegrand
        T c u X Y h k r a b qx qy)) ⊆
      Set.Icc (X + r) (2 * X + r) ×ˢ Set.Icc (T / 4) (4 * T) := by
  intro p hp
  have heq :
      hughesYoungNegativeCentralHeightIntegrand
          T c u X Y h k r a b qx qy p.1 p.2 =
        hughesYoungCentralHeightIntegrand
          T c u X Y h k (-(r : ℤ)) a b qy qx
            (p.1 - (r : ℝ)) p.2 := by
    unfold hughesYoungNegativeCentralHeightIntegrand
      hughesYoungCentralHeightIntegrand dfiEquation27C dfiSwapWeight
    simp only [Int.cast_neg, Int.cast_natCast]
    ring
  have hp' : hughesYoungCentralHeightIntegrand
      T c u X Y h k (-(r : ℤ)) a b qy qx
        (p.1 - (r : ℝ)) p.2 ≠ 0 := by
    rw [← heq]
    exact hp
  have hpMem : (p.1 - (r : ℝ), p.2) ∈ Function.support
      (Function.uncurry (hughesYoungCentralHeightIntegrand
        T c u X Y h k (-(r : ℤ)) a b qy qx)) := by
    simpa only [Function.mem_support, Function.uncurry_apply_pair] using hp'
  have hs := support_uncurry_hughesYoungCentralHeightIntegrand_subset
    hT c u hX hY h k (-(r : ℤ)) a b qy qx hpMem
  constructor
  · constructor
    · exact le_sub_iff_add_le.mp hs.1.1
    · exact (sub_le_iff_le_add).mp hs.1.2
  · exact hs.2

theorem integrable_uncurry_hughesYoungNegativeCentralHeightIntegrand
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℕ)
    (a b qx qy : ℕ) :
    Integrable (Function.uncurry
      (hughesYoungNegativeCentralHeightIntegrand
        T c u X Y h k r a b qx qy)) := by
  exact (continuous_uncurry_hughesYoungNegativeCentralHeightIntegrand
    T hc u hX hY hh hk r a b qx qy).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc)
        (support_uncurry_hughesYoungNegativeCentralHeightIntegrand_subset
          hT c u hX hY h k r a b qx qy))

theorem dfiEquation27CentralIntegral_swappedReducedCleaned_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℕ)
    (a b qx qy : ℕ) :
    dfiEquation27CentralIntegral b a qx qy
        (dfiSwapWeight
          (hughesYoungReducedCleanedShiftWeight
            T c u X Y h k (-(r : ℤ)))) r =
      (1 / (T : ℂ)) * ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralIntegral b a qx qy
          (dfiSwapWeight
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) r := by
  let J : ℝ → ℝ → ℂ :=
    hughesYoungNegativeCentralHeightIntegrand
      T c u X Y h k r a b qx qy
  have hJ : Integrable (Function.uncurry J) :=
    integrable_uncurry_hughesYoungNegativeCentralHeightIntegrand
      hT hc u hX hY hh hk r a b qx qy
  have hpoint : ∀ x : ℝ,
      dfiEquation27C b a qx qy
          (dfiSwapWeight
            (hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (-(r : ℤ)))) x (x - (r : ℝ)) =
        (1 / (T : ℂ)) * ∫ t : ℝ, J x t := by
    intro x
    by_cases hx : 0 < x
    · by_cases hy : 0 < x - (r : ℝ)
      · unfold dfiEquation27C dfiSwapWeight
        rw [hughesYoungReducedCleanedShiftWeight_eq_heightIntegral
          T c u X Y hh hk hy hx (r := -(r : ℤ)) (by
            simp only [Int.cast_neg, Int.cast_natCast]
            ring)]
        let L : ℂ := dfiEquation27LogFactor b qx x *
          dfiEquation27LogFactor a qy (x - (r : ℝ))
        let F : ℝ → ℂ := fun t =>
          (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
              (x - (r : ℝ)) x
        calc
          dfiEquation27LogFactor b qx x *
                dfiEquation27LogFactor a qy (x - (r : ℝ)) *
                ((1 / (T : ℂ)) * ∫ t : ℝ, F t) =
              (1 / (T : ℂ)) * (L * ∫ t : ℝ, F t) := by
            dsimp only [L]
            ring
          _ = (1 / (T : ℂ)) * ∫ t : ℝ, L * F t := by
            rw [MeasureTheory.integral_const_mul]
          _ = (1 / (T : ℂ)) * ∫ t : ℝ, J x t := by
            apply congrArg ((1 / (T : ℂ)) * ·)
            apply integral_congr_ae
            filter_upwards with t
            unfold J hughesYoungNegativeCentralHeightIntegrand F L
              dfiEquation27C dfiSwapWeight
            ring
      · have hyLe : x - (r : ℝ) ≤ 0 := le_of_not_gt hy
        have hcut : hughesYoungDyadicCutoffAt X (x - (r : ℝ)) = 0 := by
          apply hughesYoungDyadicCutoff_eq_zero_of_le_one
          exact (div_le_one hX).2 (hyLe.trans (le_of_lt hX))
        have hJx : (fun t : ℝ => J x t) = fun _ => 0 := by
          funext t
          unfold J hughesYoungNegativeCentralHeightIntegrand dfiEquation27C
            dfiSwapWeight hughesYoungReducedLocalizedMellinWeight
            hughesYoungLocalizedLogKernel
          simp [hcut]
        have hleft : dfiEquation27C b a qx qy
            (dfiSwapWeight
              (hughesYoungReducedCleanedShiftWeight
                T c u X Y h k (-(r : ℤ)))) x (x - (r : ℝ)) = 0 := by
          unfold dfiEquation27C dfiSwapWeight
            hughesYoungReducedCleanedShiftWeight
            hughesYoungReducedLocalizedStaticWeight
            hughesYoungLocalizedLogKernel
          simp [hcut]
        rw [hleft, hJx]
        simp
    · have hxLe : x ≤ 0 := le_of_not_gt hx
      have hcut : hughesYoungDyadicCutoffAt Y x = 0 := by
        apply hughesYoungDyadicCutoff_eq_zero_of_le_one
        exact (div_le_one hY).2 (hxLe.trans (le_of_lt hY))
      have hJx : (fun t : ℝ => J x t) = fun _ => 0 := by
        funext t
        unfold J hughesYoungNegativeCentralHeightIntegrand dfiEquation27C
          dfiSwapWeight hughesYoungReducedLocalizedMellinWeight
          hughesYoungLocalizedLogKernel
        simp [hcut]
      have hleft : dfiEquation27C b a qx qy
          (dfiSwapWeight
            (hughesYoungReducedCleanedShiftWeight
              T c u X Y h k (-(r : ℤ)))) x (x - (r : ℝ)) = 0 := by
        unfold dfiEquation27C dfiSwapWeight
          hughesYoungReducedCleanedShiftWeight
          hughesYoungReducedLocalizedStaticWeight
          hughesYoungLocalizedLogKernel
        simp [hcut]
      rw [hleft, hJx]
      simp
  unfold dfiEquation27CentralIntegral
  rw [integral_congr_ae (Eventually.of_forall hpoint)]
  calc
    (∫ x : ℝ, (1 / (T : ℂ)) * ∫ t : ℝ, J x t) =
        (1 / (T : ℂ)) * ∫ x : ℝ, ∫ t : ℝ, J x t :=
      MeasureTheory.integral_const_mul _ _
    _ = (1 / (T : ℂ)) * ∫ t : ℝ, ∫ x : ℝ, J x t := by
      rw [MeasureTheory.integral_integral_swap hJ]
    _ = (1 / (T : ℂ)) * ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
          ∫ x : ℝ, dfiEquation27C b a qx qy
            (dfiSwapWeight
              (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k))
            x (x - (r : ℝ)) := by
      apply congrArg ((1 / (T : ℂ)) * ·)
      apply integral_congr_ae
      filter_upwards with t
      unfold J hughesYoungNegativeCentralHeightIntegrand
      rw [MeasureTheory.integral_const_mul]

theorem dfiEquation27CentralSummand_swappedReducedCleaned_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r q : ℕ)
    (a b : ℕ) :
    dfiEquation27CentralSummand b a r
        (dfiSwapWeight
          (hughesYoungReducedCleanedShiftWeight
            T c u X Y h k (-(r : ℤ)))) q =
      (1 / (T : ℂ)) * ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralSummand b a r
          (dfiSwapWeight
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) q := by
  let A : ℂ := (((b : ℂ) * a)⁻¹ *
    dfiEquation27ArithmeticCoefficient b a r q)
  unfold dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_swappedReducedCleaned_eq_heightIntegral
    hT hc u hX hY hh hk r a b
      (dfiReducedDenominator b q) (dfiReducedDenominator a q)]
  calc
    A * ((1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralIntegral b a
            (dfiReducedDenominator b q) (dfiReducedDenominator a q)
            (dfiSwapWeight
              (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) r) =
      (1 / (T : ℂ)) * (A * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralIntegral b a
            (dfiReducedDenominator b q) (dfiReducedDenominator a q)
            (dfiSwapWeight
              (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) r) := by
        ring
    _ = (1 / (T : ℂ)) * ∫ t : ℝ, A *
        ((hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralIntegral b a
            (dfiReducedDenominator b q) (dfiReducedDenominator a q)
            (dfiSwapWeight
              (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) r) := by
      rw [MeasureTheory.integral_const_mul]
    _ = (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          (A * dfiEquation27CentralIntegral b a
            (dfiReducedDenominator b q) (dfiReducedDenominator a q)
            (dfiSwapWeight
              (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) r) := by
      apply congrArg ((1 / (T : ℂ)) * ·)
      apply integral_congr_ae
      filter_upwards with t
      ring

theorem continuous_uncurry_hughesYoungNegativeCentralHeightBase
    (T : ℝ) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ) :
    Continuous (Function.uncurry
      (fun t x => hughesYoungNegativeCentralHeightBase
        T t c u X Y h k r x)) := by
  have hheight : Continuous (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ)) :=
    Complex.ofRealCLM.continuous.comp
      ((contDiff_hughesYoungHeightWeight T).continuous.comp continuous_fst)
  have hweight0 :=
    continuous_uncurry_hughesYoungReducedLocalizedMellinWeight_on_line_height
      T hc u hX hY hh hk (-r)
  have hweight : Continuous (fun p : ℝ × ℝ =>
      hughesYoungReducedLocalizedMellinWeight T p.1 c u X Y h k
        (p.2 - (r : ℝ)) p.2) := by
    have hmap : Continuous (fun p : ℝ × ℝ =>
        (p.2 - (r : ℝ), p.1)) := by fun_prop
    have hcomp := hweight0.comp hmap
    convert hcomp using 1
    funext p
    dsimp only [Function.comp_apply]
    congr 2
    push_cast
    ring
  unfold Function.uncurry hughesYoungNegativeCentralHeightBase
  exact hheight.mul hweight

theorem hughesYoungNegativeCentralHeightBase_mem_support_box
    {T : ℝ} (hT : 0 < T) (c u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (r : ℤ) {t x : ℝ}
    (hn : hughesYoungNegativeCentralHeightBase
      T t c u X Y h k r x ≠ 0) :
    t ∈ Set.Icc (T / 4) (4 * T) ∧
      x - (r : ℝ) ∈ Set.Icc X (2 * X) ∧
      x ∈ Set.Icc Y (2 * Y) := by
  dsimp only [hughesYoungNegativeCentralHeightBase] at hn
  have hheightC : (hughesYoungHeightWeight T t : ℂ) ≠ 0 :=
    left_ne_zero_of_mul hn
  have hheight : hughesYoungHeightWeight T t ≠ 0 := by
    intro hz
    apply hheightC
    simp only [hz, Complex.ofReal_zero]
  have hweight :
      hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
        (x - (r : ℝ)) x ≠ 0 := right_ne_zero_of_mul hn
  have hpair : (x - (r : ℝ), x) ∈
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
    support_uncurry_hughesYoungReducedLocalizedMellinWeight_subset
      T t c u hX hY h k hweight
  exact ⟨hughesYoungHeightWeight_support hT hheight, hpair.1, hpair.2⟩

theorem exists_uniform_norm_hughesYoungNegativeCentralHeightBase_le
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t x : ℝ,
      ‖hughesYoungNegativeCentralHeightBase T t c u X Y h k r x‖ ≤ B := by
  let W : C(ℝ × ℝ, ℂ) :=
    ⟨Function.uncurry
      (fun t x => hughesYoungNegativeCentralHeightBase T t c u X Y h k r x),
      continuous_uncurry_hughesYoungNegativeCentralHeightBase
        T hc u hX hY hh hk r⟩
  let K : TopologicalSpace.Compacts (ℝ × ℝ) :=
    ⟨Set.Icc (T / 4) (4 * T) ×ˢ Set.Icc Y (2 * Y),
      isCompact_Icc.prod isCompact_Icc⟩
  let B : ℝ := ‖W.restrict K‖
  refine ⟨B, norm_nonneg _, ?_⟩
  intro t x
  by_cases hz : hughesYoungNegativeCentralHeightBase
      T t c u X Y h k r x = 0
  · simp [hz, B]
  · have hs := hughesYoungNegativeCentralHeightBase_mem_support_box
      hT c u hX hY h k r hz
    have hmem : (t, x) ∈ (K : Set (ℝ × ℝ)) :=
      ⟨hs.1, hs.2.2⟩
    have hraw := ContinuousMap.norm_coe_le_norm
      (W.restrict K) ⟨(t, x), hmem⟩
    simpa only [W, K, B, ContinuousMap.restrict_apply,
      Function.uncurry_apply_pair] using hraw

noncomputable def hughesYoungNegativeCentralHeightKernel
    (T t c u X Y : ℝ) (h k a b r q : ℕ) (x : ℝ) : ℂ :=
  dfiEquation27LogFactor b (dfiReducedDenominator b q) x *
    dfiEquation27LogFactor a (dfiReducedDenominator a q) (x - (r : ℝ)) *
    hughesYoungNegativeCentralHeightBase T t c u X Y h k (r : ℤ) x

theorem continuous_uncurry_hughesYoungNegativeCentralHeightKernel
    (T : ℝ) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b r q : ℕ) :
    Continuous (Function.uncurry
      (fun t x => hughesYoungNegativeCentralHeightKernel
        T t c u X Y h k a b r q x)) := by
  have hbase := continuous_uncurry_hughesYoungCentralHeightIntegrand
    T hc u hX hY hh hk (-(r : ℤ)) a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
  have hmap : Continuous (fun p : ℝ × ℝ =>
      (p.2 - (r : ℝ), p.1)) := by fun_prop
  have hcomp := hbase.comp hmap
  convert hcomp using 1
  funext p
  unfold Function.comp Function.uncurry hughesYoungNegativeCentralHeightKernel
    hughesYoungNegativeCentralHeightBase hughesYoungCentralHeightIntegrand
    dfiEquation27C
  simp only [Int.cast_neg, Int.cast_natCast]
  ring

theorem hughesYoungNegativeCentralSeriesHeightTerm_eq_integral_heightKernel
    (T t c u X Y : ℝ) (h k a b r q : ℕ) :
    hughesYoungNegativeCentralSeriesHeightTerm T t c u X Y h k a b r q =
      (((b : ℂ) * a)⁻¹ * dfiEquation27ArithmeticCoefficient b a r q) *
        ∫ x : ℝ,
          hughesYoungNegativeCentralHeightKernel
            T t c u X Y h k a b r q x := by
  unfold hughesYoungNegativeCentralSeriesHeightTerm
    dfiEquation27CentralSummand dfiEquation27CentralIntegral
    hughesYoungNegativeCentralHeightKernel dfiEquation27C
    hughesYoungNegativeCentralHeightBase dfiSwapWeight
  let A : ℂ := ((b : ℂ) * a)⁻¹ *
    dfiEquation27ArithmeticCoefficient b a r q
  let F : ℝ → ℂ := fun x =>
    dfiEquation27LogFactor b (dfiReducedDenominator b q) x *
      dfiEquation27LogFactor a (dfiReducedDenominator a q) (x - (r : ℝ)) *
      hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
        (x - (r : ℝ)) x
  calc
    (hughesYoungHeightWeight T t : ℂ) * (A * ∫ x : ℝ, F x) =
        A * ((hughesYoungHeightWeight T t : ℂ) * ∫ x : ℝ, F x) := by ring
    _ = A * ∫ x : ℝ, (hughesYoungHeightWeight T t : ℂ) * F x := by
      rw [MeasureTheory.integral_const_mul]
    _ = A * ∫ x : ℝ,
        dfiEquation27LogFactor b (dfiReducedDenominator b q) x *
          dfiEquation27LogFactor a (dfiReducedDenominator a q) (x - (r : ℝ)) *
          ((hughesYoungHeightWeight T t : ℂ) *
            hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
              (x - (r : ℝ)) x) := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      dsimp only [F]
      ring

theorem continuous_hughesYoungNegativeCentralSeriesHeightTerm
    (T : ℝ) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b r q : ℕ) :
    Continuous (fun t : ℝ =>
      hughesYoungNegativeCentralSeriesHeightTerm T t c u X Y h k a b r q) := by
  let J : ℝ → ℝ → ℂ := fun t x =>
    hughesYoungNegativeCentralHeightKernel T t c u X Y h k a b r q x
  have hJ : Continuous (Function.uncurry J) := by
    simpa only [J] using
      continuous_uncurry_hughesYoungNegativeCentralHeightKernel
        T hc u hX hY hh hk a b r q
  have hset : ∀ t : ℝ,
      (∫ x : ℝ, J t x) = ∫ x in Set.Icc Y (2 * Y), J t x := by
    intro t
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hweight :
        hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
          (x - (r : ℝ)) x = 0 := by
      have hcut : hughesYoungDyadicCutoffAt Y x = 0 := by
        by_contra hn
        exact hx (support_hughesYoungDyadicCutoffAt_subset hY hn)
      unfold hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    dsimp only [J]
    unfold hughesYoungNegativeCentralHeightKernel
      hughesYoungNegativeCentralHeightBase
    simp [hweight]
  have hint : Continuous (fun t : ℝ => ∫ x : ℝ, J t x) := by
    rw [show (fun t : ℝ => ∫ x : ℝ, J t x) =
        fun t => ∫ x in Set.Icc Y (2 * Y), J t x by
      funext t
      exact hset t]
    exact continuous_parametric_integral_of_continuous hJ isCompact_Icc
  rw [show (fun t : ℝ =>
      hughesYoungNegativeCentralSeriesHeightTerm T t c u X Y h k a b r q) =
      fun t => (((b : ℂ) * a)⁻¹ *
          dfiEquation27ArithmeticCoefficient b a r q) * ∫ x : ℝ, J t x by
    funext t
    exact hughesYoungNegativeCentralSeriesHeightTerm_eq_integral_heightKernel
      T t c u X Y h k a b r q]
  exact continuous_const.mul hint

theorem support_hughesYoungNegativeCentralSeriesHeightTerm_subset
    {T : ℝ} (hT : 0 < T) (c u X Y : ℝ)
    (h k a b r q : ℕ) :
    Function.support (fun t : ℝ =>
      hughesYoungNegativeCentralSeriesHeightTerm T t c u X Y h k a b r q) ⊆
      Set.Icc (T / 4) (4 * T) := by
  intro t ht
  have hheight : hughesYoungHeightWeight T t ≠ 0 := by
    intro hz
    apply ht
    unfold hughesYoungNegativeCentralSeriesHeightTerm
    simp [hz]
  exact hughesYoungHeightWeight_support hT hheight

theorem norm_hughesYoungNegativeCentralHeightKernel_le
    {T : ℝ} (hT : 0 < T) (c u : ℝ)
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (h k : ℕ) {a b r q : ℕ} (hq : 0 < q)
    {B : ℝ} (hB : 0 ≤ B)
    (hbaseBound : ∀ t x : ℝ,
      ‖hughesYoungNegativeCentralHeightBase T t c u X Y h k (r : ℤ) x‖ ≤ B)
    (t x : ℝ) :
    ‖hughesYoungNegativeCentralHeightKernel T t c u X Y h k a b r q x‖ ≤
      (1 + Real.log (2 * Y) + |Real.log (b : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + Real.log (2 * X) +
        |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ)) ^ 2 * B := by
  by_cases hz : hughesYoungNegativeCentralHeightBase
      T t c u X Y h k (r : ℤ) x = 0
  · rw [show hughesYoungNegativeCentralHeightKernel
        T t c u X Y h k a b r q x = 0 by
          simp [hughesYoungNegativeCentralHeightKernel, hz]]
    simpa only [norm_zero] using mul_nonneg (sq_nonneg
      (1 + Real.log (2 * Y) + |Real.log (b : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + Real.log (2 * X) +
        |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ))) hB
  · have hs := hughesYoungNegativeCentralHeightBase_mem_support_box
      hT c u (zero_lt_one.trans_le hX) (zero_lt_one.trans_le hY)
        h k (r : ℤ) hz
    let P : ℝ := 1 + Real.log (2 * Y) + |Real.log (b : ℝ)| +
      2 * |Real.eulerMascheroniConstant| + Real.log (2 * X) +
      |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
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
        ‖dfiEquation27LogFactor b (dfiReducedDenominator b q) x‖ ≤ P := by
      simpa only [P] using
        norm_dfiEquation27LogFactor_reduced_le_centralProfile
          hY hX b a q hq hs.2.2
    have hright :
        ‖dfiEquation27LogFactor a (dfiReducedDenominator a q)
          (x - (r : ℝ))‖ ≤ P := by
      have hswap := norm_dfiEquation27LogFactor_reduced_le_centralProfile
        hX hY a b q hq hs.2.1
      dsimp only [P]
      calc
        _ ≤ 1 + Real.log (2 * X) + |Real.log (a : ℝ)| +
            2 * |Real.eulerMascheroniConstant| + Real.log (2 * Y) +
            |Real.log (b : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
            2 * Real.log (q : ℝ) := hswap
        _ = _ := by ring
    unfold hughesYoungNegativeCentralHeightKernel
    simp only [norm_mul]
    calc
      _ ≤ P * P * B := by gcongr; exact hbaseBound t x
      _ = P ^ 2 * B := by ring

theorem norm_integral_hughesYoungNegativeCentralHeightKernel_le
    {T : ℝ} (hT : 0 < T) (c u : ℝ)
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (h k : ℕ) {a b r q : ℕ} (hq : 0 < q)
    {B : ℝ} (hB : 0 ≤ B)
    (hbaseBound : ∀ t x : ℝ,
      ‖hughesYoungNegativeCentralHeightBase T t c u X Y h k (r : ℤ) x‖ ≤ B)
    (t : ℝ) :
    ‖∫ x : ℝ,
        hughesYoungNegativeCentralHeightKernel T t c u X Y h k a b r q x‖ ≤
      Y * ((1 + Real.log (2 * Y) + |Real.log (b : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + Real.log (2 * X) +
        |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ)) ^ 2 * B) := by
  have hbound := norm_hughesYoungNegativeCentralHeightKernel_le
    hT c u hX hY h k (a := a) (b := b) (r := r) (q := q)
      hq hB hbaseBound
  have heq : (∫ x : ℝ,
      hughesYoungNegativeCentralHeightKernel T t c u X Y h k a b r q x) =
      ∫ x in Set.Icc Y (2 * Y),
        hughesYoungNegativeCentralHeightKernel T t c u X Y h k a b r q x := by
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hweight :
        hughesYoungReducedLocalizedMellinWeight T t c u X Y h k
          (x - (r : ℝ)) x = 0 := by
      have hcut : hughesYoungDyadicCutoffAt Y x = 0 := by
        by_contra hn
        exact hx (support_hughesYoungDyadicCutoffAt_subset
          (zero_lt_one.trans_le hY) hn)
      unfold hughesYoungReducedLocalizedMellinWeight
        hughesYoungLocalizedLogKernel
      simp [hcut]
    unfold hughesYoungNegativeCentralHeightKernel
      hughesYoungNegativeCentralHeightBase
    simp [hweight]
  rw [heq]
  have hset := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume) (s := Set.Icc Y (2 * Y))
    (C := (1 + Real.log (2 * Y) + |Real.log (b : ℝ)| +
      2 * |Real.eulerMascheroniConstant| + Real.log (2 * X) +
      |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
      2 * Real.log (q : ℝ)) ^ 2 * B)
    (f := hughesYoungNegativeCentralHeightKernel T t c u X Y h k a b r q)
    measure_Icc_lt_top (fun x _hx => hbound t x)
  rw [Real.volume_real_Icc_of_le (by linarith : Y ≤ 2 * Y)] at hset
  calc
    _ ≤ ((1 + Real.log (2 * Y) + |Real.log (b : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + Real.log (2 * X) +
        |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ)) ^ 2 * B) * Y := by
      convert hset using 1
      ring
    _ = _ := by ring

theorem exists_uniform_norm_hughesYoungNegativeCentralSeriesHeightTerm_le_profile
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ q : ℕ, ∀ t : ℝ,
      ‖hughesYoungNegativeCentralSeriesHeightTerm
        T t c u X Y h k a b r q‖ ≤
        D * hughesYoungCentralModulusProfile Y X b a q := by
  obtain ⟨B, hB, hbaseBound⟩ :=
    exists_uniform_norm_hughesYoungNegativeCentralHeightBase_le
      hT hc u (zero_lt_one.trans_le hX) (zero_lt_one.trans_le hY)
        hh hk (r : ℤ)
  let D : ℝ := ‖(((b : ℂ) * a)⁻¹)‖ *
    ((b * a * r ^ 2 : ℕ) : ℝ) * Y * B
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro q t
  by_cases hq₀ : q = 0
  · subst q
    simp [hughesYoungNegativeCentralSeriesHeightTerm,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient,
      hughesYoungCentralModulusProfile]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq₀
    letI : NeZero q := ⟨hq₀⟩
    have hCoeff := norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
      b a r q hb ha hr
    have hIntegral := norm_integral_hughesYoungNegativeCentralHeightKernel_le
      hT c u hX hY h k (a := a) (b := b) (r := r) (q := q)
        hq hB hbaseBound t
    rw [hughesYoungNegativeCentralSeriesHeightTerm_eq_integral_heightKernel]
    simp only [norm_mul]
    calc
      ‖(((b : ℂ) * a)⁻¹)‖ *
          ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
          ‖∫ x : ℝ,
            hughesYoungNegativeCentralHeightKernel
              T t c u X Y h k a b r q x‖ ≤
        ‖(((b : ℂ) * a)⁻¹)‖ *
          (((b * a * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          (Y * ((1 + Real.log (2 * Y) + |Real.log (b : ℝ)| +
            2 * |Real.eulerMascheroniConstant| + Real.log (2 * X) +
            |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
            2 * Real.log (q : ℝ)) ^ 2 * B)) := by
          gcongr
      _ = D * hughesYoungCentralModulusProfile Y X b a q := by
        dsimp only [D, hughesYoungCentralModulusProfile]
        ring

theorem dfiEquation27CentralSeries_swappedReducedCleaned_eq_heightIntegral_of_tonelli
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b r : ℕ)
    (htonelli :
      ∑' q : ℕ, ∫⁻ t : ℝ,
        ‖hughesYoungNegativeCentralSeriesHeightTerm
          T t c u X Y h k a b r q‖ₑ ≠ ∞) :
    dfiEquation27CentralSeries b a r
        (dfiSwapWeight
          (hughesYoungReducedCleanedShiftWeight
            T c u X Y h k (-(r : ℤ)))) =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSeries b a r
            (dfiSwapWeight
              (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) := by
  let F : ℕ → ℝ → ℂ := fun q t =>
    hughesYoungNegativeCentralSeriesHeightTerm T t c u X Y h k a b r q
  have hmeas : ∀ q : ℕ, AEStronglyMeasurable (F q) := by
    intro q
    exact (continuous_hughesYoungNegativeCentralSeriesHeightTerm
      T hc u hX hY hh hk a b r q).aestronglyMeasurable
  have hswap : (∫ t : ℝ, ∑' q : ℕ, F q t) =
      ∑' q : ℕ, ∫ t : ℝ, F q t := by
    exact MeasureTheory.integral_tsum hmeas (by simpa only [F] using htonelli)
  unfold dfiEquation27CentralSeries
  simp_rw [dfiEquation27CentralSummand_swappedReducedCleaned_eq_heightIntegral
    hT hc u hX hY hh hk r]
  calc
    (∑' q : ℕ, (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSummand b a r
            (dfiSwapWeight
              (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) q) =
      (1 / (T : ℂ)) * ∑' q : ℕ, ∫ t : ℝ, F q t := by
        rw [tsum_mul_left]
        rfl
    _ = (1 / (T : ℂ)) * ∫ t : ℝ, ∑' q : ℕ, F q t := by rw [hswap]
    _ = (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          ∑' q : ℕ, dfiEquation27CentralSummand b a r
            (dfiSwapWeight
              (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) q := by
      apply congrArg ((1 / (T : ℂ)) * ·)
      apply integral_congr_ae
      filter_upwards with t
      unfold F hughesYoungNegativeCentralSeriesHeightTerm
      rw [tsum_mul_left]

theorem tsum_lintegral_enorm_hughesYoungNegativeCentralSeriesHeightTerm_ne_top
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∑' q : ℕ, ∫⁻ t : ℝ,
      ‖hughesYoungNegativeCentralSeriesHeightTerm
        T t c u X Y h k a b r q‖ₑ ≠ ∞ := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_uniform_norm_hughesYoungNegativeCentralSeriesHeightTerm_le_profile
      hT hc u hX hY hh hk ha hb hr
  apply tsum_lintegral_enorm_ne_top_of_summable_bound_Icc
    (g := fun q => D * hughesYoungCentralModulusProfile Y X b a q)
  · intro q
    exact mul_nonneg hD (hughesYoungCentralModulusProfile_nonneg Y X b a q)
  · exact (summable_hughesYoungCentralModulusProfile
      (by linarith) (by linarith) b a).mul_left D
  · intro q
    exact support_hughesYoungNegativeCentralSeriesHeightTerm_subset
      hT c u X Y h k a b r q
  · exact hbound

theorem dfiEquation27CentralSeries_swappedReducedCleaned_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    dfiEquation27CentralSeries b a r
        (dfiSwapWeight
          (hughesYoungReducedCleanedShiftWeight
            T c u X Y h k (-(r : ℤ)))) =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSeries b a r
            (dfiSwapWeight
              (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)) := by
  exact dfiEquation27CentralSeries_swappedReducedCleaned_eq_heightIntegral_of_tonelli
    hT hc u (zero_lt_one.trans_le hX) (zero_lt_one.trans_le hY) hh hk a b r
      (tsum_lintegral_enorm_hughesYoungNegativeCentralSeriesHeightTerm_ne_top
        hT hc u hX hY hh hk ha hb hr)

/-- Exact height decomposition of the complete signed DFI central series.
The nonzero-shift hypothesis excludes the diagonal, which is a separate
Hughes--Young term rather than part of DFI equation (27). -/
theorem dfiSignedCentralSeries_reducedCleaned_eq_heightIntegral
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) {r : ℤ} (hr : r ≠ 0) :
    dfiSignedCentralSeries a b r
        (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) =
      (1 / (T : ℂ)) * ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k) := by
  cases r with
  | ofNat r =>
      have hrPos : 0 < r := by
        by_contra hzero
        exact hr (congrArg Int.ofNat (Nat.eq_zero_of_not_pos hzero))
      exact dfiEquation27CentralSeries_reducedCleaned_eq_heightIntegral
        hT hc u hX hY hh hk ha hb hrPos
  | negSucc n =>
      let r : ℕ := n + 1
      have hrPos : 0 < r := by dsimp only [r]; omega
      have hrEq : Int.negSucc n = -((r : ℕ) : ℤ) := by
        dsimp only [r]
        omega
      rw [hrEq]
      simp_rw [dfiSignedCentralSeries_neg_ofNat a b r hrPos]
      exact dfiEquation27CentralSeries_swappedReducedCleaned_eq_heightIntegral
        hT hc u hX hY hh hk ha hb hrPos

end RiemannZeta.GuthMaynard
