import RiemannZeta.GuthMaynard.DFIProposition1
import RiemannZeta.GuthMaynard.GammaVerticalDecay
import Mathlib.Analysis.Complex.PhragmenLindelof

/-! Periodic Estermann strip bounds and the unconditional Mellin--Barnes
form of DFI Proposition 1. -/

open Complex Finset Set Filter Topology MeasureTheory Asymptotics
open scoped BigOperators Topology
open Classical

namespace RiemannZeta.GuthMaynard

noncomputable def periodicMean (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) : ℂ :=
  (q : ℂ)⁻¹ * ∑ a : ZMod q, Ψ a

noncomputable def periodicCentered (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) (a : ZMod q) : ℂ :=
  Ψ a - periodicMean q Ψ

theorem sum_periodicCentered (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) :
    ∑ a : ZMod q, periodicCentered q Ψ a = 0 := by
  unfold periodicCentered periodicMean
  rw [sum_sub_distrib, sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  field_simp
  ring

theorem sum_range_periodicCentered_period (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) :
    ∑ k ∈ range q, periodicCentered q Ψ (k : ZMod q) = 0 := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
      rw [← Fin.sum_univ_eq_sum_range]
      refine (Fintype.sum_equiv (ZMod.finEquiv (q + 1)).toEquiv
        (fun i : Fin (q + 1) => periodicCentered (q + 1) Ψ ((i : ℕ) : ZMod (q + 1)))
        (periodicCentered (q + 1) Ψ) ?_).trans
          (sum_periodicCentered (q + 1) Ψ)
      intro i
      have hi : (i.val : ZMod (q + 1)) =
          (ZMod.finEquiv (q + 1)).toEquiv i := by
        apply ZMod.val_injective
        rw [ZMod.val_natCast_of_lt i.isLt]
        rfl
      change periodicCentered (q + 1) Ψ (i.val : ZMod (q + 1)) = _
      rw [hi]

theorem sum_range_periodicCentered_reduce (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) (n : ℕ) :
    ∑ k ∈ range n, periodicCentered q Ψ (k : ZMod q) =
      ∑ k ∈ range (n % q), periodicCentered q Ψ (k : ZMod q) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < q
      · rw [Nat.mod_eq_of_lt hn]
      · have hqle : q ≤ n := Nat.le_of_not_gt hn
        have hqpos : 0 < q := NeZero.pos q
        have hnpos : 0 < n := hqpos.trans_le hqle
        have hsub : n - q < n := Nat.sub_lt hnpos hqpos
        have hnEq : n = q + (n - q) := by omega
        rw [hnEq, sum_range_add, sum_range_periodicCentered_period, zero_add]
        have hshift : (∑ x ∈ range (n - q),
              periodicCentered q Ψ ((q + x : ℕ) : ZMod q)) =
            ∑ x ∈ range (n - q), periodicCentered q Ψ (x : ZMod q) := by
          apply sum_congr rfl
          intro x _hx
          congr 1
          simp
        rw [hshift, ih (n - q) hsub]
        congr 2
        simp

theorem sum_Icc_one_eq_sum_range_succ_sub_zero
    (f : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = (∑ k ∈ range (n + 1), f k) - f 0 := by
  have hset : range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, sum_insert (by simp [Finset.mem_Icc])]
  ring

noncomputable def periodicCenteredBound (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) : ℝ :=
  ∑ a : ZMod q, ‖periodicCentered q Ψ a‖

theorem norm_sum_Icc_periodicCentered_le (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) (n : ℕ) :
    ‖∑ k ∈ Icc 1 n, periodicCentered q Ψ (k : ZMod q)‖ ≤
      2 * periodicCenteredBound q Ψ := by
  rw [sum_Icc_one_eq_sum_range_succ_sub_zero,
    sum_range_periodicCentered_reduce]
  simp only [Nat.cast_zero]
  unfold periodicCenteredBound
  calc
    ‖(∑ k ∈ range ((n + 1) % q), periodicCentered q Ψ (k : ZMod q)) -
        periodicCentered q Ψ 0‖ ≤
        ‖∑ k ∈ range ((n + 1) % q), periodicCentered q Ψ (k : ZMod q)‖ +
          ‖periodicCentered q Ψ 0‖ := norm_sub_le _ _
    _ ≤ (∑ k ∈ range ((n + 1) % q),
          ‖periodicCentered q Ψ (k : ZMod q)‖) +
          ‖periodicCentered q Ψ 0‖ := by gcongr; exact norm_sum_le _ _
    _ ≤ periodicCenteredBound q Ψ + periodicCenteredBound q Ψ := by
      gcongr
      · calc
          (∑ k ∈ range ((n + 1) % q),
              ‖periodicCentered q Ψ (k : ZMod q)‖) ≤
              ∑ k ∈ range q, ‖periodicCentered q Ψ (k : ZMod q)‖ := by
            exact sum_le_sum_of_subset_of_nonneg
              (range_mono (Nat.mod_lt _ (NeZero.pos q)).le)
              (fun _ _ _ => norm_nonneg _)
          _ = ∑ a : ZMod q, ‖periodicCentered q Ψ a‖ := by
            cases q with
            | zero => exact (NeZero.ne 0 rfl).elim
            | succ q =>
                rw [← Fin.sum_univ_eq_sum_range]
                exact Fintype.sum_equiv (ZMod.finEquiv (q + 1)).toEquiv
                  (fun i : Fin (q + 1) =>
                    ‖periodicCentered (q + 1) Ψ ((i : ℕ) : ZMod (q + 1))‖)
                  (fun a : ZMod (q + 1) => ‖periodicCentered (q + 1) Ψ a‖)
                  (fun i => by
                    have hi : (i.val : ZMod (q + 1)) =
                        (ZMod.finEquiv (q + 1)).toEquiv i := by
                      apply ZMod.val_injective
                      rw [ZMod.val_natCast_of_lt i.isLt]
                      rfl
                    change ‖periodicCentered (q + 1) Ψ
                      (i.val : ZMod (q + 1))‖ = _
                    rw [hi])
      · exact single_le_sum (fun a _ => norm_nonneg (periodicCentered q Ψ a)) (mem_univ 0)
    _ = 2 * periodicCenteredBound q Ψ := by ring

theorem sum_Icc_periodicCentered_isBigO (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, periodicCentered q Ψ (k : ZMod q))
      =O[atTop] (fun _n : ℕ => (1 : ℝ)) := by
  apply IsBigO.of_bound (2 * periodicCenteredBound q Ψ)
  filter_upwards with n
  simpa using norm_sum_Icc_periodicCentered_le q Ψ n

noncomputable def periodicCenteredPartialSum (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 n, periodicCentered q Ψ (k : ZMod q)

noncomputable def periodicCenteredKernel (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) (x : ℝ) : ℂ :=
  if 1 < x then periodicCenteredPartialSum q Ψ ⌊x⌋₊ else 0

theorem measurable_periodicCenteredKernel (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) : Measurable (periodicCenteredKernel q Ψ) := by
  unfold periodicCenteredKernel
  exact Measurable.ite measurableSet_Ioi
    ((measurable_of_countable (f := periodicCenteredPartialSum q Ψ)).comp
      Nat.measurable_floor) measurable_const

theorem norm_periodicCenteredKernel_le (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) (x : ℝ) :
    ‖periodicCenteredKernel q Ψ x‖ ≤ 2 * periodicCenteredBound q Ψ := by
  by_cases hx : 1 < x
  · rw [periodicCenteredKernel, if_pos hx]
    exact norm_sum_Icc_periodicCentered_le q Ψ ⌊x⌋₊
  · rw [periodicCenteredKernel, if_neg hx, norm_zero]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem locallyIntegrableOn_periodicCenteredKernel (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) :
    LocallyIntegrableOn (periodicCenteredKernel q Ψ) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k _hk hkCompact
  apply IntegrableOn.of_bound hkCompact.measure_lt_top
  · exact (measurable_periodicCenteredKernel q Ψ).aestronglyMeasurable.restrict
  · filter_upwards with x
    exact norm_periodicCenteredKernel_le q Ψ x

theorem periodicCenteredKernel_isBigO_atTop (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) :
    periodicCenteredKernel q Ψ =O[atTop] (fun _x : ℝ => (1 : ℝ)) := by
  apply IsBigO.of_bound (2 * periodicCenteredBound q Ψ)
  filter_upwards with x
  simpa using norm_periodicCenteredKernel_le q Ψ x

theorem periodicCenteredKernel_eq_zero_of_le_one (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) {x : ℝ} (hx : x ≤ 1) :
    periodicCenteredKernel q Ψ x = 0 := by
  simp [periodicCenteredKernel, not_lt.mpr hx]

theorem periodicCenteredKernel_isBigO_zero (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) (b : ℝ) :
    periodicCenteredKernel q Ψ =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-b)) := by
  apply IsBigO.of_bound 1
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
  rw [periodicCenteredKernel_eq_zero_of_le_one q Ψ hx.2.le, norm_zero]
  positivity

noncomputable def periodicCenteredAbel (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) (s : ℂ) : ℂ :=
  s * mellin (periodicCenteredKernel q Ψ) (-s)

theorem differentiableAt_periodicCenteredAbel (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (periodicCenteredAbel q Ψ) s := by
  unfold periodicCenteredAbel
  have hMellin : DifferentiableAt ℂ (mellin (periodicCenteredKernel q Ψ)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
      (locallyIntegrableOn_periodicCenteredKernel q Ψ)
      (by simpa using periodicCenteredKernel_isBigO_atTop q Ψ)
      (by simpa using hs)
      (periodicCenteredKernel_isBigO_zero q Ψ (-s.re - 1)) (by simp)
  exact differentiableAt_id.mul
    (hMellin.comp s (hasDerivAt_neg s).differentiableAt)

theorem periodicCenteredAbel_eq_integral (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) {s : ℂ} (hs : 0 < s.re) :
    periodicCenteredAbel q Ψ s =
      s * ∫ t in Ioi (1 : ℝ),
        periodicCenteredPartialSum q Ψ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1)) := by
  have hConv : MellinConvergent (periodicCenteredKernel q Ψ) (-s) :=
    mellinConvergent_of_isBigO_rpow (a := 0) (b := -s.re - 1)
      (locallyIntegrableOn_periodicCenteredKernel q Ψ)
      (by simpa using periodicCenteredKernel_isBigO_atTop q Ψ)
      (by simpa using hs)
      (periodicCenteredKernel_isBigO_zero q Ψ (-s.re - 1)) (by simp)
  let F : ℝ → ℂ := fun t =>
    (t : ℂ) ^ (-s - 1) * periodicCenteredKernel q Ψ t
  have hF : IntegrableOn F (Ioi (0 : ℝ)) := by
    simpa [MellinConvergent, F, smul_eq_mul] using hConv
  have hFleft : IntegrableOn F (Ioc (0 : ℝ) 1) :=
    hF.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have hFright : IntegrableOn F (Ioi (1 : ℝ)) :=
    hF.mono_set (Ioi_subset_Ioi (by norm_num))
  unfold periodicCenteredAbel mellin
  change s * (∫ t in Ioi (0 : ℝ), F t) = _
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hFleft hFright]
  have hLeft : ∫ t in Ioc (0 : ℝ) 1, F t = 0 := by
    rw [show (∫ t in Ioc (0 : ℝ) 1, F t) =
        ∫ _t in Ioc (0 : ℝ) 1, (0 : ℂ) by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp [F, periodicCenteredKernel_eq_zero_of_le_one q Ψ ht.2]]
    simp
  rw [hLeft, zero_add]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change 1 < t at ht
  dsimp [F]
  rw [periodicCenteredKernel, if_pos ht]
  dsimp [periodicCenteredPartialSum]
  rw [mul_comm]
  congr 1
  ring_nf

theorem periodicCentered_LFunction_eq_abel_of_one_lt_re
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) {s : ℂ} (hs : 1 < s.re) :
    ZMod.LFunction (periodicCentered q Ψ) s = periodicCenteredAbel q Ψ s := by
  rw [ZMod.LFunction_eq_LSeries _ hs,
    LSeries_eq_mul_integral (fun n : ℕ => periodicCentered q Ψ n)
      (r := (0 : ℝ)) (by norm_num) (by linarith)
      (ZMod.LSeriesSummable_of_one_lt_re _ hs)
      (by simpa [periodicCenteredPartialSum] using
        sum_Icc_periodicCentered_isBigO q Ψ)]
  rw [periodicCenteredAbel_eq_integral q Ψ (by linarith)]
  rfl

theorem periodicCentered_LFunction_eq_abel
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) {s : ℂ} (hs : 0 < s.re) :
    ZMod.LFunction (periodicCentered q Ψ) s = periodicCenteredAbel q Ψ s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hL : AnalyticOnNhd ℂ (ZMod.LFunction (periodicCentered q Ψ)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z _hz =>
      (ZMod.differentiableAt_LFunction _ z (Or.inr ?_)).differentiableWithinAt) hUOpen
    exact sum_periodicCentered q Ψ
  have hADiff : DifferentiableOn ℂ (periodicCenteredAbel q Ψ) U :=
    fun z hz => (differentiableAt_periodicCenteredAbel q Ψ hz).differentiableWithinAt
  have hA : AnalyticOnNhd ℂ (periodicCenteredAbel q Ψ) U :=
    hADiff.analyticOnNhd hUOpen
  have hEventually : ZMod.LFunction (periodicCentered q Ψ) =ᶠ[𝓝 (2 : ℂ)]
      periodicCenteredAbel q Ψ := by
    have hOpen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hOpen.mem_nhds (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    exact periodicCentered_LFunction_eq_abel_of_one_lt_re q Ψ hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hA
    (convex_halfSpace_re_gt 0).isPreconnected (by change (0 : ℝ) < 2; norm_num)
      hEventually hs

theorem norm_periodicCenteredAbel_le (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) {s : ℂ} (hre : (1 / 4 : ℝ) ≤ s.re) :
    ‖periodicCenteredAbel q Ψ s‖ ≤
      8 * periodicCenteredBound q Ψ * ‖s‖ := by
  have hspos : 0 < s.re := lt_of_lt_of_le (by norm_num) hre
  rw [periodicCenteredAbel_eq_integral q Ψ hspos, norm_mul]
  let C : ℝ := 2 * periodicCenteredBound q Ψ
  have hC : 0 ≤ C := by
    dsimp [C, periodicCenteredBound]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hPower : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hDom : IntegrableOn (fun t : ℝ => C * t ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
    hPower.const_mul C
  have hIntegral :
      ‖∫ t in Ioi (1 : ℝ),
          periodicCenteredPartialSum q Ψ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1))‖ ≤
        ∫ t in Ioi (1 : ℝ), C * t ^ (-s.re - 1) := by
    apply norm_integral_le_of_norm_le hDom
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    change 1 < t at ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht)]
    have hSum : ‖periodicCenteredPartialSum q Ψ ⌊t⌋₊‖ ≤ C := by
      simpa [periodicCenteredPartialSum, C] using
        norm_sum_Icc_periodicCentered_le q Ψ ⌊t⌋₊
    have hPow : 0 ≤ t ^ (-s.re - 1) := Real.rpow_nonneg (zero_lt_one.trans ht).le _
    change ‖periodicCenteredPartialSum q Ψ ⌊t⌋₊‖ *
      t ^ (-(s.re + 1)) ≤ C * t ^ (-s.re - 1)
    rw [show -(s.re + 1) = -s.re - 1 by ring]
    exact mul_le_mul_of_nonneg_right hSum hPow
  have hEval : (∫ t in Ioi (1 : ℝ), C * t ^ (-s.re - 1)) = C / s.re := by
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
    rw [show -s.re - 1 + 1 = -s.re by ring, neg_div_neg_eq]
    rw [one_div, div_eq_mul_inv]
  rw [hEval] at hIntegral
  calc
    ‖s‖ * ‖∫ t in Ioi (1 : ℝ),
        periodicCenteredPartialSum q Ψ ⌊t⌋₊ * (t : ℂ) ^ (-(s + 1))‖ ≤
        ‖s‖ * (C / s.re) := mul_le_mul_of_nonneg_left hIntegral (norm_nonneg s)
    _ ≤ ‖s‖ * (4 * C) := by
      gcongr
      exact (div_le_iff₀ hspos).2 (by nlinarith)
    _ = 8 * periodicCenteredBound q Ψ * ‖s‖ := by
      dsimp [C]
      ring

theorem ZMod.LFunction_one_eq_riemannZeta
    (q : ℕ) [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    ZMod.LFunction (fun _a : ZMod q => (1 : ℂ)) s = riemannZeta s := by
  have h := ZMod.LFunction_stdAddChar_eq_expZeta (N := q) (0 : ZMod q) s
    (Or.inr hs)
  have h0 : ZMod.toAddCircle (0 : ZMod q) = 0 := by simp
  simpa only [zero_mul, AddChar.map_zero_eq_one, h0,
    HurwitzZeta.expZeta_zero] using h

theorem ZMod.LFunction_periodicCentered
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) (s : ℂ) :
    ZMod.LFunction (periodicCentered q Ψ) s =
      ZMod.LFunction Ψ s -
        periodicMean q Ψ * ZMod.LFunction (fun _a : ZMod q => (1 : ℂ)) s := by
  unfold ZMod.LFunction periodicCentered
  simp_rw [sub_mul, one_mul]
  rw [Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  simp only [← Finset.mul_sum]
  ring

theorem ZMod.LFunction_eq_centered_add_mean_zeta
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) {s : ℂ} (hs : s ≠ 1) :
    ZMod.LFunction Ψ s =
      ZMod.LFunction (periodicCentered q Ψ) s +
        periodicMean q Ψ * riemannZeta s := by
  rw [ZMod.LFunction_periodicCentered q Ψ s,
    ZMod.LFunction_one_eq_riemannZeta q hs]
  ring

noncomputable def periodicLFunctionRightGrowthConstant
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) : ℝ :=
  8 * periodicCenteredBound q Ψ + 5 * ‖periodicMean q Ψ‖

theorem periodicLFunctionRightGrowthConstant_nonneg
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) :
    0 ≤ periodicLFunctionRightGrowthConstant q Ψ := by
  unfold periodicLFunctionRightGrowthConstant periodicCenteredBound
  positivity

theorem norm_periodicLFunction_le_rightGrowth
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) {s : ℂ}
    (hre : (1 / 4 : ℝ) ≤ s.re) (him : 1 ≤ |s.im|) :
    ‖ZMod.LFunction Ψ s‖ ≤
      periodicLFunctionRightGrowthConstant q Ψ * ‖s‖ := by
  have hs : s ≠ 1 := by
    intro hs
    subst s
    norm_num at him
  rw [ZMod.LFunction_eq_centered_add_mean_zeta q Ψ hs,
    periodicCentered_LFunction_eq_abel q Ψ
      (lt_of_lt_of_le (by norm_num) hre)]
  have hCentered := norm_periodicCenteredAbel_le q Ψ hre
  have hZeta := norm_riemannZeta_le_five_mul_norm hre him
  calc
    ‖periodicCenteredAbel q Ψ s + periodicMean q Ψ * riemannZeta s‖ ≤
        ‖periodicCenteredAbel q Ψ s‖ +
          ‖periodicMean q Ψ * riemannZeta s‖ := norm_add_le _ _
    _ ≤ 8 * periodicCenteredBound q Ψ * ‖s‖ +
          ‖periodicMean q Ψ‖ * (5 * ‖s‖) := by
      rw [norm_mul]
      gcongr
    _ = periodicLFunctionRightGrowthConstant q Ψ * ‖s‖ := by
      unfold periodicLFunctionRightGrowthConstant
      ring

theorem norm_betaIntegral_le_re_betaIntegral
    (s t : ℂ) :
    ‖Complex.betaIntegral s t‖ ≤
      (Complex.betaIntegral (s.re : ℂ) (t.re : ℂ)).re := by
  unfold Complex.betaIntegral
  calc
    ‖∫ x : ℝ in 0..1,
        (x : ℂ) ^ (s - 1) * (1 - (x : ℂ)) ^ (t - 1)‖ ≤
        ∫ x : ℝ in 0..1,
          ‖(x : ℂ) ^ (s - 1) * (1 - (x : ℂ)) ^ (t - 1)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ∫ x : ℝ in 0..1,
          x ^ (s.re - 1) * (1 - x) ^ (t.re - 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [MeasureTheory.volume.ae_ne (1 : ℝ)] with x hxeq
      intro hx
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have hx0 : 0 < x := hx.1
      have hx1 : 0 < 1 - x := sub_pos.mpr (hx.2.lt_of_ne hxeq)
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
        show 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) by norm_cast,
        Complex.norm_cpow_eq_rpow_re_of_pos hx1]
      norm_num
    _ = (∫ x : ℝ in 0..1,
          ((x ^ (s.re - 1) * (1 - x) ^ (t.re - 1) : ℝ) : ℂ)).re := by
      rw [intervalIntegral.integral_ofReal]
      simp
    _ = (∫ x : ℝ in 0..1,
          (x : ℂ) ^ ((s.re : ℂ) - 1) *
            (1 - (x : ℂ)) ^ ((t.re : ℂ) - 1)).re := by
      apply congrArg Complex.re
      apply intervalIntegral.integral_congr_ae
      filter_upwards [MeasureTheory.volume.ae_ne (1 : ℝ)] with x hxeq
      intro hx
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have hx0 : 0 < x := hx.1
      have hx1 : 0 < 1 - x := sub_pos.mpr (hx.2.lt_of_ne hxeq)
      rw [Complex.ofReal_mul]
      congr 1
      · rw [Complex.ofReal_cpow hx0.le]
        norm_num
      · rw [show 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) by norm_cast,
          Complex.ofReal_cpow hx1.le]
        norm_num

theorem norm_Gamma_le_realGamma_ratio_mul_general_anchor
    {a A u : ℝ} (ha0 : 0 < a) (ha : a ≤ A) :
    ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * I)‖ * Real.Gamma A ≤
      Real.Gamma a * ‖Complex.Gamma ((A : ℂ) + (u : ℂ) * I)‖ := by
  rcases ha.eq_or_lt with rfl | haLt
  · simp [mul_comm]
  let s : ℂ := (a : ℂ) + (u : ℂ) * I
  let b : ℝ := A - a
  have hb : 0 < b := by dsimp [b]; linarith
  have hs : 0 < s.re := by simpa [s] using ha0
  have hGamma := Complex.Gamma_mul_Gamma_eq_betaIntegral hs
    (show 0 < ((b : ℂ)).re by simpa using hb)
  have hsum : s + (b : ℂ) = (A : ℂ) + (u : ℂ) * I := by
    dsimp [s, b]
    push_cast
    ring
  rw [hsum] at hGamma
  have hNorm := congrArg norm hGamma
  simp only [norm_mul, Complex.Gamma_ofReal] at hNorm
  have hBeta := norm_betaIntegral_le_re_betaIntegral s (b : ℂ)
  have hBetaReal :
      (Complex.betaIntegral (a : ℂ) (b : ℂ)).re =
        Real.Gamma a * Real.Gamma b / Real.Gamma A := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div (a : ℂ) (b : ℂ)
      (by simpa using ha0) (by simpa using hb)]
    rw [show (a : ℂ) + (b : ℂ) = (A : ℝ) by
      dsimp [b]
      push_cast
      ring]
    rw [Complex.Gamma_ofReal a, Complex.Gamma_ofReal b,
      Complex.Gamma_ofReal A]
    norm_cast
  have hBeta' :
      ‖Complex.betaIntegral s (b : ℂ)‖ ≤
        Real.Gamma a * Real.Gamma b / Real.Gamma A := by
    rw [show s.re = a by simp [s], show ((b : ℂ)).re = b by simp,
      hBetaReal] at hBeta
    exact hBeta
  have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha0
  have hGb : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
  have hA0 : 0 < A := ha0.trans_le ha
  have hGanchor : 0 < Real.Gamma A := Real.Gamma_pos_of_pos hA0
  have hAnchorNorm : 0 ≤
      ‖Complex.Gamma ((A : ℂ) + (u : ℂ) * I)‖ := norm_nonneg _
  have hMul :
      ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * I)‖ * Real.Gamma b ≤
        ‖Complex.Gamma ((A : ℂ) + (u : ℂ) * I)‖ *
          (Real.Gamma a * Real.Gamma b / Real.Gamma A) := by
    calc
      ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * I)‖ * Real.Gamma b =
          ‖Complex.Gamma s‖ * ‖(Real.Gamma b : ℂ)‖ := by
        simp [s, abs_of_pos hGb]
      _ = ‖Complex.Gamma ((A : ℂ) + (u : ℂ) * I)‖ *
          ‖Complex.betaIntegral s (b : ℂ)‖ := hNorm
      _ ≤ ‖Complex.Gamma ((A : ℂ) + (u : ℂ) * I)‖ *
          (Real.Gamma a * Real.Gamma b / Real.Gamma A) :=
        mul_le_mul_of_nonneg_left hBeta' hAnchorNorm
  have hCancel :
      ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * I)‖ ≤
        ‖Complex.Gamma ((A : ℂ) + (u : ℂ) * I)‖ *
          Real.Gamma a / Real.Gamma A := by
    have hEq :
        ‖Complex.Gamma ((A : ℂ) + (u : ℂ) * I)‖ *
            (Real.Gamma a * Real.Gamma b / Real.Gamma A) =
          (‖Complex.Gamma ((A : ℂ) + (u : ℂ) * I)‖ *
            Real.Gamma a / Real.Gamma A) * Real.Gamma b := by ring
    rw [hEq] at hMul
    nlinarith
  have hFinal := (le_div_iff₀ hGanchor).mp hCancel
  nlinarith

theorem norm_Gamma_le_realGamma_ratio_mul_anchor
    {a u : ℝ} (ha0 : 0 < a) (ha : a ≤ 3 / 2) :
    ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * I)‖ * Real.Gamma (3 / 2) ≤
      Real.Gamma a *
        ‖Complex.Gamma ((3 / 2 : ℂ) + (u : ℂ) * I)‖ :=
  by
    simpa using
      (norm_Gamma_le_realGamma_ratio_mul_general_anchor
        (A := (3 / 2 : ℝ)) (u := u) ha0 ha)

theorem norm_dfiGammaRecurrenceProduct_le (k : ℕ) (u : ℝ) :
    ‖∏ j ∈ Finset.range k,
        ((3 / 2 : ℂ) - (u : ℂ) * I + (j : ℂ))‖ ≤
      (((k : ℝ) + 2) * (1 + |u|)) ^ k := by
  rw [norm_prod]
  calc
    ∏ j ∈ Finset.range k,
          ‖(3 / 2 : ℂ) - (u : ℂ) * I + (j : ℂ)‖ ≤
        ∏ _j ∈ Finset.range k, ((k : ℝ) + 2) * (1 + |u|) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        have hjk : (j : ℝ) ≤ k := by
          exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
        have hre :
            (((3 / 2 : ℂ) - (u : ℂ) * I + (j : ℂ))).re =
              (3 / 2 : ℝ) + j := by simp
        have him :
            (((3 / 2 : ℂ) - (u : ℂ) * I + (j : ℂ))).im = -u := by simp
        calc
          ‖(3 / 2 : ℂ) - (u : ℂ) * I + (j : ℂ)‖ ≤
              |(3 / 2 : ℝ) + j| + |-u| := by
            simpa [hre, him] using
              Complex.norm_le_abs_re_add_abs_im
                ((3 / 2 : ℂ) - (u : ℂ) * I + (j : ℂ))
          _ = (3 / 2 : ℝ) + j + |u| := by
            rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / 2 + j), abs_neg]
          _ ≤ ((k : ℝ) + 2) * (1 + |u|) := by
            nlinarith [abs_nonneg u]
    _ = (((k : ℝ) + 2) * (1 + |u|)) ^ k := by simp

theorem norm_Gamma_mul_voronoiExp_shifted_anchor_le
    (k : ℕ) (u : ℝ) :
    ‖Complex.Gamma ((((3 / 2 : ℝ) + k : ℝ) : ℂ) - (u : ℂ) * I) *
        Complex.exp (Real.pi * I *
          ((((3 / 2 : ℝ) + k : ℝ) : ℂ) - (u : ℂ) * I) / 2)‖ ≤
      4 * (((k : ℝ) + 2) * (1 + |u|)) ^ k * (1 + |u|) ∧
    ‖Complex.Gamma ((((3 / 2 : ℝ) + k : ℝ) : ℂ) - (u : ℂ) * I) *
        Complex.exp (-Real.pi * I *
          ((((3 / 2 : ℝ) + k : ℝ) : ℂ) - (u : ℂ) * I) / 2)‖ ≤
      4 * (((k : ℝ) + 2) * (1 + |u|)) ^ k * (1 + |u|) := by
  let s : ℂ := (3 / 2 : ℂ) - (u : ℂ) * I
  have hs : ∀ j < k, s + (j : ℂ) ≠ 0 := by
    intro j hj hzero
    have hre := congrArg Complex.re hzero
    simp [s] at hre
    have hjpos : (0 : ℝ) < 3 / 2 + j := by positivity
    linarith
  have hRec := Gamma_add_nat_eq_prod_mul s k hs
  have hArg : s + k =
      ((((3 / 2 : ℝ) + k : ℝ) : ℂ) - (u : ℂ) * I) := by
    dsimp [s]
    push_cast
    ring
  rw [hArg] at hRec
  have hProd := norm_dfiGammaRecurrenceProduct_le k u
  have hExpPos :
      ‖Complex.exp (Real.pi * I *
          ((((3 / 2 : ℝ) + k : ℝ) : ℂ) - (u : ℂ) * I) / 2)‖ =
        ‖Complex.exp (Real.pi * I * s / 2)‖ := by
    rw [Complex.norm_exp, Complex.norm_exp]
    simp [s]
  have hExpNeg :
      ‖Complex.exp (-Real.pi * I *
          ((((3 / 2 : ℝ) + k : ℝ) : ℂ) - (u : ℂ) * I) / 2)‖ =
        ‖Complex.exp (-Real.pi * I * s / 2)‖ := by
    rw [Complex.norm_exp, Complex.norm_exp]
    simp [s]
  constructor
  · rw [hRec, norm_mul, norm_mul, hExpPos]
    calc
      ‖∏ j ∈ Finset.range k, (s + (j : ℂ))‖ *
          ‖Complex.Gamma s‖ * ‖Complex.exp (Real.pi * I * s / 2)‖ =
          ‖∏ j ∈ Finset.range k, (s + (j : ℂ))‖ *
            ‖Complex.Gamma s * Complex.exp (Real.pi * I * s / 2)‖ := by
        rw [norm_mul]
        ring
      _ ≤ (((k : ℝ) + 2) * (1 + |u|)) ^ k *
          (4 * (1 + |u|)) := by
        exact mul_le_mul
          (by simpa [s] using hProd)
          (by simpa [s] using norm_Gamma_mul_voronoiExp_pos_le u)
          (norm_nonneg _)
          (by positivity)
      _ = 4 * (((k : ℝ) + 2) * (1 + |u|)) ^ k * (1 + |u|) := by ring
  · rw [hRec, norm_mul, norm_mul, hExpNeg]
    calc
      ‖∏ j ∈ Finset.range k, (s + (j : ℂ))‖ *
          ‖Complex.Gamma s‖ * ‖Complex.exp (-Real.pi * I * s / 2)‖ =
          ‖∏ j ∈ Finset.range k, (s + (j : ℂ))‖ *
            ‖Complex.Gamma s * Complex.exp (-Real.pi * I * s / 2)‖ := by
        rw [norm_mul]
        ring
      _ ≤ (((k : ℝ) + 2) * (1 + |u|)) ^ k *
          (4 * (1 + |u|)) := by
        exact mul_le_mul
          (by simpa [s] using hProd)
          (by simpa [s] using norm_Gamma_mul_voronoiExp_neg_le u)
          (norm_nonneg _)
          (by positivity)
      _ = 4 * (((k : ℝ) + 2) * (1 + |u|)) ^ k * (1 + |u|) := by ring

theorem exists_realGamma_bound_three_halves_shift (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ,
      3 / 2 ≤ a → a ≤ 3 / 2 + k → Real.Gamma a ≤ C := by
  have hne : (Set.Icc (3 / 2 : ℝ) (3 / 2 + k)).Nonempty :=
    Set.nonempty_Icc.mpr (le_add_of_nonneg_right (Nat.cast_nonneg k))
  have hcont : ContinuousOn Real.Gamma
      (Set.Icc (3 / 2 : ℝ) (3 / 2 + k)) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (by
      intro a ha
      exact lt_of_lt_of_le (by norm_num) ha.1)
  obtain ⟨a₀, ha₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨Real.Gamma a₀, Real.Gamma_pos_of_pos
    (lt_of_lt_of_le (by norm_num) ha₀.1), ?_⟩
  intro a haLower haUpper
  exact hmax ⟨haLower, haUpper⟩

theorem exists_norm_Gamma_mul_voronoiExp_shifted_strip_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ),
      3 / 2 ≤ a → a ≤ 3 / 2 + k → ∀ u : ℝ,
      ‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I) *
          Complex.exp (Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖ ≤
          C * (1 + |u|) ^ (k + 1) ∧
      ‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I) *
          Complex.exp (-Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖ ≤
          C * (1 + |u|) ^ (k + 1) := by
  obtain ⟨B, hB, hBound⟩ := exists_realGamma_bound_three_halves_shift k
  let A : ℝ := 3 / 2 + k
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hGA : 0 < Real.Gamma A := Real.Gamma_pos_of_pos hA0
  refine ⟨4 * B * ((k : ℝ) + 2) ^ k / Real.Gamma A, by positivity, ?_⟩
  intro a haLower haUpper u
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) haLower
  have haA : a ≤ A := by simpa [A] using haUpper
  have hRatio := norm_Gamma_le_realGamma_ratio_mul_general_anchor
    (A := A) (u := -u) ha0 haA
  have hRatio' :
      ‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ * Real.Gamma A ≤
        Real.Gamma a *
          ‖Complex.Gamma ((A : ℂ) - (u : ℂ) * I)‖ := by
    simpa [Complex.ofReal_neg, neg_mul, mul_comm] using hRatio
  have hGaB : Real.Gamma a ≤ B := hBound a haLower haUpper
  have hAnchor := norm_Gamma_mul_voronoiExp_shifted_anchor_le k u
  have hAComplex :
      ((((3 / 2 : ℝ) + k : ℝ) : ℂ) - (u : ℂ) * I) =
        (A : ℂ) - (u : ℂ) * I := by simp [A]
  rw [hAComplex] at hAnchor
  constructor
  · have hExpEq :
        ‖Complex.exp (Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖ =
          ‖Complex.exp (Real.pi * I *
            ((A : ℂ) - (u : ℂ) * I) / 2)‖ := by
      rw [Complex.norm_exp, Complex.norm_exp]
      simp
    have hProduct :
        (‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
          ‖Complex.exp (Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖) * Real.Gamma A ≤
          B * (4 * (((k : ℝ) + 2) * (1 + |u|)) ^ k * (1 + |u|)) := by
      calc
        (‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
            ‖Complex.exp (Real.pi * I *
              ((a : ℂ) - (u : ℂ) * I) / 2)‖) * Real.Gamma A =
            (‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ * Real.Gamma A) *
              ‖Complex.exp (Real.pi * I *
                ((a : ℂ) - (u : ℂ) * I) / 2)‖ := by ring
        _ ≤ (Real.Gamma a *
              ‖Complex.Gamma ((A : ℂ) - (u : ℂ) * I)‖) *
              ‖Complex.exp (Real.pi * I *
                ((a : ℂ) - (u : ℂ) * I) / 2)‖ :=
          mul_le_mul_of_nonneg_right hRatio' (norm_nonneg _)
        _ = Real.Gamma a *
            ‖Complex.Gamma ((A : ℂ) - (u : ℂ) * I) *
              Complex.exp (Real.pi * I *
                ((A : ℂ) - (u : ℂ) * I) / 2)‖ := by
          rw [norm_mul, hExpEq]
          ring
        _ ≤ B * (4 * (((k : ℝ) + 2) * (1 + |u|)) ^ k * (1 + |u|)) :=
          mul_le_mul hGaB hAnchor.1 (norm_nonneg _) hB.le
    have hDiv := (le_div_iff₀ hGA).2 hProduct
    rw [norm_mul]
    calc
      ‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
          ‖Complex.exp (Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖ ≤
          B * (4 * (((k : ℝ) + 2) * (1 + |u|)) ^ k * (1 + |u|)) /
            Real.Gamma A := hDiv
      _ = (4 * B * ((k : ℝ) + 2) ^ k / Real.Gamma A) *
          (1 + |u|) ^ (k + 1) := by
        rw [mul_pow, pow_succ]
        ring
  · have hExpEq :
        ‖Complex.exp (-Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖ =
          ‖Complex.exp (-Real.pi * I *
            ((A : ℂ) - (u : ℂ) * I) / 2)‖ := by
      rw [Complex.norm_exp, Complex.norm_exp]
      simp
    have hProduct :
        (‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
          ‖Complex.exp (-Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖) * Real.Gamma A ≤
          B * (4 * (((k : ℝ) + 2) * (1 + |u|)) ^ k * (1 + |u|)) := by
      calc
        (‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
            ‖Complex.exp (-Real.pi * I *
              ((a : ℂ) - (u : ℂ) * I) / 2)‖) * Real.Gamma A =
            (‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ * Real.Gamma A) *
              ‖Complex.exp (-Real.pi * I *
                ((a : ℂ) - (u : ℂ) * I) / 2)‖ := by ring
        _ ≤ (Real.Gamma a *
              ‖Complex.Gamma ((A : ℂ) - (u : ℂ) * I)‖) *
              ‖Complex.exp (-Real.pi * I *
                ((a : ℂ) - (u : ℂ) * I) / 2)‖ :=
          mul_le_mul_of_nonneg_right hRatio' (norm_nonneg _)
        _ = Real.Gamma a *
            ‖Complex.Gamma ((A : ℂ) - (u : ℂ) * I) *
              Complex.exp (-Real.pi * I *
                ((A : ℂ) - (u : ℂ) * I) / 2)‖ := by
          rw [norm_mul, hExpEq]
          ring
        _ ≤ B * (4 * (((k : ℝ) + 2) * (1 + |u|)) ^ k * (1 + |u|)) :=
          mul_le_mul hGaB hAnchor.2 (norm_nonneg _) hB.le
    have hDiv := (le_div_iff₀ hGA).2 hProduct
    rw [norm_mul]
    calc
      ‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
          ‖Complex.exp (-Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖ ≤
          B * (4 * (((k : ℝ) + 2) * (1 + |u|)) ^ k * (1 + |u|)) /
            Real.Gamma A := hDiv
      _ = (4 * B * ((k : ℝ) + 2) ^ k / Real.Gamma A) *
          (1 + |u|) ^ (k + 1) := by
        rw [mul_pow, pow_succ]
        ring

theorem exists_realGamma_bound_quarter_three_halves :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ,
      1 / 4 ≤ a → a ≤ 3 / 2 → Real.Gamma a ≤ C := by
  have hne : (Set.Icc (1 / 4 : ℝ) (3 / 2)).Nonempty :=
    Set.nonempty_Icc.mpr (by norm_num)
  have hcont : ContinuousOn Real.Gamma (Set.Icc (1 / 4 : ℝ) (3 / 2)) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (by
      intro a ha
      exact lt_of_lt_of_le (by norm_num) ha.1)
  obtain ⟨a₀, ha₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨Real.Gamma a₀, Real.Gamma_pos_of_pos
    (lt_of_lt_of_le (by norm_num) ha₀.1), ?_⟩
  intro a haLower haUpper
  exact hmax ⟨haLower, haUpper⟩

theorem exists_norm_Gamma_mul_voronoiExp_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ),
      1 / 4 ≤ a → a ≤ 3 / 2 → ∀ u : ℝ,
      ‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I) *
          Complex.exp (Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖ ≤ C * (1 + |u|) ∧
      ‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I) *
          Complex.exp (-Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖ ≤ C * (1 + |u|) := by
  obtain ⟨B, hB, hBound⟩ := exists_realGamma_bound_quarter_three_halves
  have hG : 0 < Real.Gamma (3 / 2) :=
    Real.Gamma_pos_of_pos (by norm_num)
  refine ⟨4 * B / Real.Gamma (3 / 2), by positivity, ?_⟩
  intro a haLower haUpper u
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) haLower
  have hRatio := norm_Gamma_le_realGamma_ratio_mul_anchor
    (u := -u) ha0 haUpper
  have hRatio' :
      ‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ * Real.Gamma (3 / 2) ≤
        Real.Gamma a *
          ‖Complex.Gamma ((3 / 2 : ℂ) - (u : ℂ) * I)‖ := by
    simpa [Complex.ofReal_neg, neg_mul, mul_comm] using hRatio
  have hGa : 0 ≤ Real.Gamma a := (Real.Gamma_pos_of_pos ha0).le
  have hGaB : Real.Gamma a ≤ B := hBound a haLower haUpper
  have hOne : 0 ≤ 1 + |u| := by positivity
  constructor
  · have hAnchor := norm_Gamma_mul_voronoiExp_pos_le u
    rw [norm_mul]
    have hExp : 0 ≤
        ‖Complex.exp (Real.pi * I *
          ((a : ℂ) - (u : ℂ) * I) / 2)‖ := norm_nonneg _
    have hExpEq :
        ‖Complex.exp (Real.pi * I *
          ((a : ℂ) - (u : ℂ) * I) / 2)‖ =
        ‖Complex.exp (Real.pi * I *
          ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ := by
      repeat' rw [Complex.norm_exp]
      norm_num
    have hProduct :
        (‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
          ‖Complex.exp (Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖) * Real.Gamma (3 / 2) ≤
          B * (4 * (1 + |u|)) := by
      calc
        (‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
            ‖Complex.exp (Real.pi * I *
              ((a : ℂ) - (u : ℂ) * I) / 2)‖) * Real.Gamma (3 / 2) =
            (‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
              Real.Gamma (3 / 2)) *
              ‖Complex.exp (Real.pi * I *
                ((a : ℂ) - (u : ℂ) * I) / 2)‖ := by ring
        _ ≤ (Real.Gamma a *
              ‖Complex.Gamma ((3 / 2 : ℂ) - (u : ℂ) * I)‖) *
              ‖Complex.exp (Real.pi * I *
                ((a : ℂ) - (u : ℂ) * I) / 2)‖ :=
          mul_le_mul_of_nonneg_right hRatio' hExp
        _ = Real.Gamma a *
            ‖Complex.Gamma ((3 / 2 : ℂ) - (u : ℂ) * I) *
              Complex.exp (Real.pi * I *
                ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ := by
          rw [norm_mul, hExpEq]
          ring
        _ ≤ B * (4 * (1 + |u|)) := by gcongr
    have hDiv := (le_div_iff₀ hG).2 hProduct
    calc
      ‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
          ‖Complex.exp (Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖ ≤
          B * (4 * (1 + |u|)) / Real.Gamma (3 / 2) := hDiv
      _ = (4 * B / Real.Gamma (3 / 2)) * (1 + |u|) := by ring
  · have hAnchor := norm_Gamma_mul_voronoiExp_neg_le u
    rw [norm_mul]
    have hExp : 0 ≤
        ‖Complex.exp (-Real.pi * I *
          ((a : ℂ) - (u : ℂ) * I) / 2)‖ := norm_nonneg _
    have hExpEq :
        ‖Complex.exp (-Real.pi * I *
          ((a : ℂ) - (u : ℂ) * I) / 2)‖ =
        ‖Complex.exp (-Real.pi * I *
          ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ := by
      repeat' rw [Complex.norm_exp]
      norm_num
    have hProduct :
        (‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
          ‖Complex.exp (-Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖) * Real.Gamma (3 / 2) ≤
          B * (4 * (1 + |u|)) := by
      calc
        (‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
            ‖Complex.exp (-Real.pi * I *
              ((a : ℂ) - (u : ℂ) * I) / 2)‖) * Real.Gamma (3 / 2) =
            (‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
              Real.Gamma (3 / 2)) *
              ‖Complex.exp (-Real.pi * I *
                ((a : ℂ) - (u : ℂ) * I) / 2)‖ := by ring
        _ ≤ (Real.Gamma a *
              ‖Complex.Gamma ((3 / 2 : ℂ) - (u : ℂ) * I)‖) *
              ‖Complex.exp (-Real.pi * I *
                ((a : ℂ) - (u : ℂ) * I) / 2)‖ :=
          mul_le_mul_of_nonneg_right hRatio' hExp
        _ = Real.Gamma a *
            ‖Complex.Gamma ((3 / 2 : ℂ) - (u : ℂ) * I) *
              Complex.exp (-Real.pi * I *
                ((3 / 2 : ℂ) - (u : ℂ) * I) / 2)‖ := by
          rw [norm_mul, hExpEq]
          ring
        _ ≤ B * (4 * (1 + |u|)) := by gcongr
    have hDiv := (le_div_iff₀ hG).2 hProduct
    calc
      ‖Complex.Gamma ((a : ℂ) - (u : ℂ) * I)‖ *
          ‖Complex.exp (-Real.pi * I *
            ((a : ℂ) - (u : ℂ) * I) / 2)‖ ≤
          B * (4 * (1 + |u|)) / Real.Gamma (3 / 2) := hDiv
      _ = (4 * B / Real.Gamma (3 / 2)) * (1 + |u|) := by ring

theorem exists_periodicLFunctionDual_scalar_strip_bound
    (q : ℕ) [NeZero q] :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ),
      3 / 4 ≤ a → a ≤ 3 / 2 → ∀ u : ℝ,
      ‖(q : ℂ) ^ (((a : ℂ) - (u : ℂ) * I) - 1) *
          (2 * Real.pi : ℂ) ^ (-((a : ℂ) - (u : ℂ) * I))‖ ≤ C := by
  let F : ℝ → ℝ := fun a =>
    ‖(q : ℂ) ^ ((a : ℂ) - 1) *
      (2 * Real.pi : ℂ) ^ (-(a : ℂ))‖
  have hcont : Continuous F := by
    dsimp [F]
    have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    have hpi : (2 * Real.pi : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    apply Continuous.norm
    apply Continuous.mul
    · exact ((Complex.continuous_ofReal.comp continuous_id).sub continuous_const).const_cpow
        (Or.inl hq)
    · exact (Complex.continuous_ofReal.comp continuous_id).neg.const_cpow
        (Or.inl hpi)
  obtain ⟨a₀, ha₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (3 / 4 : ℝ) ≤ 3 / 2))
    hcont.continuousOn
  refine ⟨F a₀ + 1, by positivity, ?_⟩
  intro a haLower haUpper u
  have hBaseQ : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hBasePi : 0 < 2 * Real.pi := by positivity
  have hNormEq :
      ‖(q : ℂ) ^ (((a : ℂ) - (u : ℂ) * I) - 1) *
          (2 * Real.pi : ℂ) ^ (-((a : ℂ) - (u : ℂ) * I))‖ = F a := by
    unfold F
    repeat' rw [norm_mul]
    rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos q),
      Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by norm_cast]
    repeat' rw [Complex.norm_cpow_eq_rpow_re_of_pos hBasePi]
    congr 2 <;> norm_num
  rw [hNormEq]
  exact (hmax ⟨haLower, haUpper⟩).trans (le_add_of_nonneg_right zero_le_one)

theorem periodicLFunctionDual_strip_bound
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ),
      3 / 4 ≤ a → a ≤ 3 / 2 → ∀ u : ℝ, 1 ≤ |u| →
      ‖periodicLFunctionDual q Ψ
        ((a : ℂ) - (u : ℂ) * I)‖ ≤ C * (1 + |u|) ^ 2 := by
  obtain ⟨A, hA, hScalar⟩ := exists_periodicLFunctionDual_scalar_strip_bound q
  obtain ⟨B, hB, hGamma⟩ := exists_norm_Gamma_mul_voronoiExp_strip_bound
  let L₁ : ℝ := periodicLFunctionRightGrowthConstant q (ZMod.dft Ψ)
  let L₂ : ℝ := periodicLFunctionRightGrowthConstant q
    (ZMod.dft fun x => Ψ (-x))
  have hL₁ : 0 ≤ L₁ := periodicLFunctionRightGrowthConstant_nonneg q _
  have hL₂ : 0 ≤ L₂ := periodicLFunctionRightGrowthConstant_nonneg q _
  refine ⟨A * B * 2 * (L₁ + L₂), by positivity, ?_⟩
  intro a haLower haUpper u hu
  let s : ℂ := (a : ℂ) - (u : ℂ) * I
  have hre : (1 / 4 : ℝ) ≤ s.re := by
    dsimp [s]
    norm_num
    linarith
  have him : 1 ≤ |s.im| := by simpa [s] using hu
  have hsNorm : ‖s‖ ≤ 2 * (1 + |u|) := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = |a| + |u| := by simp [s]
      _ ≤ 2 * (1 + |u|) := by
        rw [abs_of_nonneg (le_trans (by norm_num) haLower)]
        nlinarith [abs_nonneg u]
  have hLBound₁ : ‖ZMod.LFunction (ZMod.dft Ψ) s‖ ≤
      L₁ * (2 * (1 + |u|)) := by
    calc
      ‖ZMod.LFunction (ZMod.dft Ψ) s‖ ≤ L₁ * ‖s‖ :=
        norm_periodicLFunction_le_rightGrowth q (ZMod.dft Ψ) hre him
      _ ≤ L₁ * (2 * (1 + |u|)) :=
        mul_le_mul_of_nonneg_left hsNorm hL₁
  have hLBound₂ : ‖ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s‖ ≤
      L₂ * (2 * (1 + |u|)) := by
    calc
      ‖ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s‖ ≤ L₂ * ‖s‖ :=
        norm_periodicLFunction_le_rightGrowth q
          (ZMod.dft fun x => Ψ (-x)) hre him
      _ ≤ L₂ * (2 * (1 + |u|)) :=
        mul_le_mul_of_nonneg_left hsNorm hL₂
  have hGammaBound := hGamma a (by linarith) haUpper u
  have hScalarBound := hScalar a haLower haUpper u
  have hOne : 0 ≤ 1 + |u| := by positivity
  unfold periodicLFunctionDual
  change ‖(q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) *
    Complex.Gamma s *
      (Complex.exp (Real.pi * I * s / 2) * ZMod.LFunction (ZMod.dft Ψ) s +
       Complex.exp (-Real.pi * I * s / 2) *
         ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s)‖ ≤ _
  have hInside :
      ‖Complex.Gamma s *
        (Complex.exp (Real.pi * I * s / 2) * ZMod.LFunction (ZMod.dft Ψ) s +
         Complex.exp (-Real.pi * I * s / 2) *
           ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s)‖ ≤
        B * 2 * (L₁ + L₂) * (1 + |u|) ^ 2 := by
    rw [mul_add]
    calc
      ‖Complex.Gamma s *
            (Complex.exp (Real.pi * I * s / 2) * ZMod.LFunction (ZMod.dft Ψ) s) +
          Complex.Gamma s *
            (Complex.exp (-Real.pi * I * s / 2) *
              ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s)‖ ≤
          ‖Complex.Gamma s * Complex.exp (Real.pi * I * s / 2)‖ *
              ‖ZMod.LFunction (ZMod.dft Ψ) s‖ +
            ‖Complex.Gamma s * Complex.exp (-Real.pi * I * s / 2)‖ *
              ‖ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s‖ := by
        simpa [mul_assoc, norm_mul] using norm_add_le
          (Complex.Gamma s *
            (Complex.exp (Real.pi * I * s / 2) * ZMod.LFunction (ZMod.dft Ψ) s))
          (Complex.Gamma s *
            (Complex.exp (-Real.pi * I * s / 2) *
              ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s))
      _ ≤ (B * (1 + |u|)) * (L₁ * (2 * (1 + |u|))) +
            (B * (1 + |u|)) * (L₂ * (2 * (1 + |u|))) := by
        gcongr
        · simpa [s] using hGammaBound.1
        · simpa [s] using hGammaBound.2
      _ = B * 2 * (L₁ + L₂) * (1 + |u|) ^ 2 := by ring
  have hScalarNonneg : 0 ≤ A := hA.le
  calc
    ‖(q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) *
        Complex.Gamma s *
          (Complex.exp (Real.pi * I * s / 2) * ZMod.LFunction (ZMod.dft Ψ) s +
           Complex.exp (-Real.pi * I * s / 2) *
             ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s)‖ =
      ‖(q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s)‖ *
        ‖Complex.Gamma s *
          (Complex.exp (Real.pi * I * s / 2) * ZMod.LFunction (ZMod.dft Ψ) s +
           Complex.exp (-Real.pi * I * s / 2) *
             ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s)‖ := by
        rw [← norm_mul]
        congr 1
        ring
    _ ≤ A * (B * 2 * (L₁ + L₂) * (1 + |u|) ^ 2) := by
      gcongr
    _ = (A * B * 2 * (L₁ + L₂)) * (1 + |u|) ^ 2 := by ring

noncomputable def periodicLFunctionDualStripConstant
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) : ℝ :=
  Classical.choose (periodicLFunctionDual_strip_bound q Ψ)

theorem periodicLFunctionDualStripConstant_nonneg
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ) :
    0 ≤ periodicLFunctionDualStripConstant q Ψ :=
  (Classical.choose_spec (periodicLFunctionDual_strip_bound q Ψ)).1

theorem norm_periodicLFunctionDual_le_strip
    (q : ℕ) [NeZero q] (Ψ : ZMod q → ℂ)
    {a u : ℝ} (haLower : 3 / 4 ≤ a) (haUpper : a ≤ 3 / 2)
    (hu : 1 ≤ |u|) :
    ‖periodicLFunctionDual q Ψ
      ((a : ℂ) - (u : ℂ) * I)‖ ≤
      periodicLFunctionDualStripConstant q Ψ * (1 + |u|) ^ 2 :=
  (Classical.choose_spec (periodicLFunctionDual_strip_bound q Ψ)).2
    a haLower haUpper u hu

noncomputable def periodicEstermannLeftStripConstant
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) : ℝ :=
  ∑ a : ZMod q, ∑ b : ZMod q,
    ‖Φ (a * b)‖ *
      periodicLFunctionDualStripConstant q (fun x => if x = a then 1 else 0) *
      periodicLFunctionDualStripConstant q (fun x => if x = b then 1 else 0)

theorem periodicEstermannLeftStripConstant_nonneg
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) :
    0 ≤ periodicEstermannLeftStripConstant q Φ := by
  unfold periodicEstermannLeftStripConstant
  apply Finset.sum_nonneg
  intro a _ha
  apply Finset.sum_nonneg
  intro b _hb
  exact mul_nonneg
    (mul_nonneg (norm_nonneg _)
      (periodicLFunctionDualStripConstant_nonneg q _))
    (periodicLFunctionDualStripConstant_nonneg q _)

theorem norm_periodicEstermann_le_leftStrip
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ)
    {x u : ℝ} (hxLower : -(1 / 2 : ℝ) ≤ x)
    (hxUpper : x ≤ 1 / 4) (hu : 1 ≤ |u|) :
    ‖periodicEstermann q Φ ((x : ℂ) + (u : ℂ) * I)‖ ≤
      periodicEstermannLeftStripConstant q Φ * (1 + |u|) ^ 4 := by
  let s : ℂ := ((1 - x : ℝ) : ℂ) - (u : ℂ) * I
  have hsPole : s ≠ 1 := by
    intro hs
    have hi := congrArg Complex.im hs
    simp [s] at hi
    have : u = 0 := by linarith
    subst u
    norm_num at hu
  have hsGamma : ∀ n : ℕ, s ≠ -n := by
    intro n hs
    have hr := congrArg Complex.re hs
    simp [s] at hr
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  have hFE := periodicEstermann_one_sub q Φ hsPole hsGamma
  have hOneSub : 1 - s = (x : ℂ) + (u : ℂ) * I := by
    dsimp [s]
    push_cast
    ring
  rw [hOneSub] at hFE
  rw [hFE]
  have haLower : (3 / 4 : ℝ) ≤ 1 - x := by linarith
  have haUpper : 1 - x ≤ (3 / 2 : ℝ) := by linarith
  unfold periodicEstermannDual
  calc
    ‖∑ a : ZMod q, ∑ b : ZMod q,
        Φ (a * b) *
          periodicLFunctionDual q (fun y => if y = a then 1 else 0) s *
          periodicLFunctionDual q (fun y => if y = b then 1 else 0) s‖ ≤
      ∑ a : ZMod q, ∑ b : ZMod q,
        ‖Φ (a * b) *
          periodicLFunctionDual q (fun y => if y = a then 1 else 0) s *
          periodicLFunctionDual q (fun y => if y = b then 1 else 0) s‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a : ZMod q, ∑ b : ZMod q,
        (‖Φ (a * b)‖ *
          periodicLFunctionDualStripConstant q (fun y => if y = a then 1 else 0) *
          periodicLFunctionDualStripConstant q (fun y => if y = b then 1 else 0)) *
            (1 + |u|) ^ 4 := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro b _hb
      rw [norm_mul, norm_mul]
      have hA := norm_periodicLFunctionDual_le_strip q
        (fun y => if y = a then 1 else 0) haLower haUpper hu
      have hB := norm_periodicLFunctionDual_le_strip q
        (fun y => if y = b then 1 else 0) haLower haUpper hu
      have hCA : 0 ≤ periodicLFunctionDualStripConstant q
          (fun y => if y = a then 1 else 0) :=
        periodicLFunctionDualStripConstant_nonneg q _
      have hPow : 0 ≤ (1 + |u|) ^ 2 := sq_nonneg _
      change ‖Φ (a * b)‖ *
          ‖periodicLFunctionDual q (fun y => if y = a then 1 else 0) s‖ *
          ‖periodicLFunctionDual q (fun y => if y = b then 1 else 0) s‖ ≤ _
      calc
        ‖Φ (a * b)‖ *
            ‖periodicLFunctionDual q (fun y => if y = a then 1 else 0) s‖ *
            ‖periodicLFunctionDual q (fun y => if y = b then 1 else 0) s‖ ≤
          ‖Φ (a * b)‖ *
            (periodicLFunctionDualStripConstant q
              (fun y => if y = a then 1 else 0) * (1 + |u|) ^ 2) *
            (periodicLFunctionDualStripConstant q
              (fun y => if y = b then 1 else 0) * (1 + |u|) ^ 2) := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left hA (norm_nonneg _)) hB
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (mul_nonneg hCA hPow))
        _ = (‖Φ (a * b)‖ *
              periodicLFunctionDualStripConstant q (fun y => if y = a then 1 else 0) *
              periodicLFunctionDualStripConstant q (fun y => if y = b then 1 else 0)) *
                (1 + |u|) ^ 4 := by ring
    _ = periodicEstermannLeftStripConstant q Φ * (1 + |u|) ^ 4 := by
      unfold periodicEstermannLeftStripConstant
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_mul]

noncomputable def periodicEstermannRightStripConstant
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) : ℝ :=
  4 * ∑ a : ZMod q, ∑ b : ZMod q,
    ‖Φ (a * b)‖ *
      periodicLFunctionRightGrowthConstant q (fun x => if x = a then 1 else 0) *
      periodicLFunctionRightGrowthConstant q (fun x => if x = b then 1 else 0)

theorem periodicEstermannRightStripConstant_nonneg
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) :
    0 ≤ periodicEstermannRightStripConstant q Φ := by
  unfold periodicEstermannRightStripConstant
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro a _ha
  apply Finset.sum_nonneg
  intro b _hb
  exact mul_nonneg
    (mul_nonneg (norm_nonneg _)
      (periodicLFunctionRightGrowthConstant_nonneg q _))
    (periodicLFunctionRightGrowthConstant_nonneg q _)

theorem norm_periodicEstermann_le_rightStrip
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ)
    {x u : ℝ} (hxLower : (1 / 4 : ℝ) ≤ x)
    (hxUpper : x ≤ 3 / 2) (hu : 1 ≤ |u|) :
    ‖periodicEstermann q Φ ((x : ℂ) + (u : ℂ) * I)‖ ≤
      periodicEstermannRightStripConstant q Φ * (1 + |u|) ^ 2 := by
  let s : ℂ := (x : ℂ) + (u : ℂ) * I
  have hsNorm : ‖s‖ ≤ 2 * (1 + |u|) := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = |x| + |u| := by simp [s]
      _ ≤ 2 * (1 + |u|) := by
        rw [abs_of_nonneg (le_trans (by norm_num) hxLower)]
        nlinarith [abs_nonneg u]
  have him : 1 ≤ |s.im| := by simpa [s] using hu
  have hre : (1 / 4 : ℝ) ≤ s.re := by simpa [s] using hxLower
  unfold periodicEstermann
  calc
    ‖∑ a : ZMod q, ∑ b : ZMod q,
        Φ (a * b) * ZMod.LFunction (fun y => if y = a then 1 else 0) s *
          ZMod.LFunction (fun y => if y = b then 1 else 0) s‖ ≤
      ∑ a : ZMod q, ∑ b : ZMod q,
        ‖Φ (a * b) * ZMod.LFunction (fun y => if y = a then 1 else 0) s *
          ZMod.LFunction (fun y => if y = b then 1 else 0) s‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a : ZMod q, ∑ b : ZMod q,
        4 * (‖Φ (a * b)‖ *
          periodicLFunctionRightGrowthConstant q (fun y => if y = a then 1 else 0) *
          periodicLFunctionRightGrowthConstant q (fun y => if y = b then 1 else 0)) *
            (1 + |u|) ^ 2 := by
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro b _hb
      rw [norm_mul, norm_mul]
      let Ca := periodicLFunctionRightGrowthConstant q
        (fun y => if y = a then 1 else 0)
      let Cb := periodicLFunctionRightGrowthConstant q
        (fun y => if y = b then 1 else 0)
      have hCa : 0 ≤ Ca := periodicLFunctionRightGrowthConstant_nonneg q _
      have hCb : 0 ≤ Cb := periodicLFunctionRightGrowthConstant_nonneg q _
      have hA0 := norm_periodicLFunction_le_rightGrowth q
        (fun y => if y = a then 1 else 0) hre him
      have hB0 := norm_periodicLFunction_le_rightGrowth q
        (fun y => if y = b then 1 else 0) hre him
      have hA : ‖ZMod.LFunction (fun y => if y = a then 1 else 0) s‖ ≤
          Ca * (2 * (1 + |u|)) := hA0.trans
        (mul_le_mul_of_nonneg_left hsNorm hCa)
      have hB : ‖ZMod.LFunction (fun y => if y = b then 1 else 0) s‖ ≤
          Cb * (2 * (1 + |u|)) := hB0.trans
        (mul_le_mul_of_nonneg_left hsNorm hCb)
      change ‖Φ (a * b)‖ *
          ‖ZMod.LFunction (fun y => if y = a then 1 else 0) s‖ *
          ‖ZMod.LFunction (fun y => if y = b then 1 else 0) s‖ ≤ _
      calc
        ‖Φ (a * b)‖ *
            ‖ZMod.LFunction (fun y => if y = a then 1 else 0) s‖ *
            ‖ZMod.LFunction (fun y => if y = b then 1 else 0) s‖ ≤
          ‖Φ (a * b)‖ * (Ca * (2 * (1 + |u|))) *
            (Cb * (2 * (1 + |u|))) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hA (norm_nonneg _)) hB
            (norm_nonneg _)
            (mul_nonneg (norm_nonneg _)
              (mul_nonneg hCa (by positivity)))
        _ = 4 * (‖Φ (a * b)‖ * Ca * Cb) * (1 + |u|) ^ 2 := by ring
    _ = periodicEstermannRightStripConstant q Φ * (1 + |u|) ^ 2 := by
      unfold periodicEstermannRightStripConstant
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum, Finset.sum_mul]

noncomputable def periodicEstermannStripConstant
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) : ℝ :=
  periodicEstermannLeftStripConstant q Φ +
    periodicEstermannRightStripConstant q Φ

theorem norm_periodicEstermann_le_strip
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ)
    {x u : ℝ} (hxLower : -(1 / 2 : ℝ) ≤ x)
    (hxUpper : x ≤ 3 / 2) (hu : 1 ≤ |u|) :
    ‖periodicEstermann q Φ ((x : ℂ) + (u : ℂ) * I)‖ ≤
      periodicEstermannStripConstant q Φ * (1 + |u|) ^ 4 := by
  by_cases hx : x ≤ 1 / 4
  · have h := norm_periodicEstermann_le_leftStrip q Φ hxLower hx hu
    have hRight : 0 ≤ periodicEstermannRightStripConstant q Φ :=
      periodicEstermannRightStripConstant_nonneg q Φ
    calc
      ‖periodicEstermann q Φ ((x : ℂ) + (u : ℂ) * I)‖ ≤
          periodicEstermannLeftStripConstant q Φ * (1 + |u|) ^ 4 := h
      _ ≤ (periodicEstermannLeftStripConstant q Φ +
          periodicEstermannRightStripConstant q Φ) * (1 + |u|) ^ 4 := by
        have hP : 0 ≤ (1 + |u|) ^ 4 := by positivity
        exact mul_le_mul_of_nonneg_right (by linarith) hP
      _ = periodicEstermannStripConstant q Φ * (1 + |u|) ^ 4 := rfl
  · have hx' : (1 / 4 : ℝ) ≤ x := le_of_not_ge hx
    have h := norm_periodicEstermann_le_rightStrip q Φ hx' hxUpper hu
    have hLeft : 0 ≤ periodicEstermannLeftStripConstant q Φ :=
      periodicEstermannLeftStripConstant_nonneg q Φ
    have hPow : (1 + |u|) ^ 2 ≤ (1 + |u|) ^ 4 := by
      have hOne : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
      nlinarith [sq_nonneg ((1 + |u|) ^ 2 - 1)]
    calc
      ‖periodicEstermann q Φ ((x : ℂ) + (u : ℂ) * I)‖ ≤
          periodicEstermannRightStripConstant q Φ * (1 + |u|) ^ 2 := h
      _ ≤ periodicEstermannRightStripConstant q Φ * (1 + |u|) ^ 4 :=
        mul_le_mul_of_nonneg_left hPow
          (periodicEstermannRightStripConstant_nonneg q Φ)
      _ ≤ (periodicEstermannLeftStripConstant q Φ +
          periodicEstermannRightStripConstant q Φ) * (1 + |u|) ^ 4 := by
        have hP : 0 ≤ (1 + |u|) ^ 4 := by positivity
        nlinarith
      _ = periodicEstermannStripConstant q Φ * (1 + |u|) ^ 4 := rfl

/-- On each fixed vertical line, the Mellin transform of a DFI test
function decays faster than every prescribed power. -/
theorem DFIVoronoiTestFunction.mellin_polynomial_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      |u| ^ n * ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  let F : SchwartzMap ℝ ℂ :=
    SchwartzMap.fourierTransformCLM ℂ (dfiVoronoiMellinKernelSchwartz hg σ)
  let C : ℝ := (2 * Real.pi) ^ n * SchwartzMap.seminorm ℝ n 0 F
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro u
  have hSem := SchwartzMap.le_seminorm' (𝕜 := ℝ) n 0 F
    (u / (2 * Real.pi))
  rw [iteratedDeriv_zero] at hSem
  have hSem' : ‖u / (2 * Real.pi)‖ ^ n *
      ‖F (u / (2 * Real.pi))‖ ≤ SchwartzMap.seminorm ℝ n 0 F := hSem
  rw [hg.mellin_eq_fourier_mellinKernel σ u]
  change |u| ^ n * ‖F (u / (2 * Real.pi))‖ ≤ C
  have hpi : 0 < 2 * Real.pi := by positivity
  have hAbs : |u| = (2 * Real.pi) * ‖u / (2 * Real.pi)‖ := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpi]
    field_simp [hpi.ne']
  rw [hAbs, mul_pow]
  dsimp only [C]
  calc
    (2 * Real.pi) ^ n * ‖u / (2 * Real.pi)‖ ^ n *
          ‖F (u / (2 * Real.pi))‖ =
        (2 * Real.pi) ^ n *
          (‖u / (2 * Real.pi)‖ ^ n * ‖F (u / (2 * Real.pi))‖) := by ring
    _ ≤ (2 * Real.pi) ^ n * SchwartzMap.seminorm ℝ n 0 F :=
      mul_le_mul_of_nonneg_left hSem' (pow_nonneg hpi.le n)

/-- Compact support gives a Mellin bound uniform on any prescribed finite
vertical strip.  This general form is needed when a Voronoi dual contour is
moved farther left to obtain arbitrary decay in its discrete frequency. -/
theorem DFIVoronoiTestFunction.exists_mellin_interval_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (c d : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ), c ≤ σ → σ ≤ d → ∀ u : ℝ,
      ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  let Fleft : SchwartzMap ℝ ℂ :=
    dfiVoronoiMellinKernelSchwartz hg c
  let Fright : SchwartzMap ℝ ℂ :=
    dfiVoronoiMellinKernelSchwartz hg d
  let C : ℝ := (∫ v : ℝ, ‖Fleft v‖) + ∫ v : ℝ, ‖Fright v‖
  have hLeftInt : Integrable (fun v : ℝ ↦ ‖Fleft v‖) := Fleft.integrable.norm
  have hRightInt : Integrable (fun v : ℝ ↦ ‖Fright v‖) := Fright.integrable.norm
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)
      (integral_nonneg fun _ ↦ norm_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro σ hσLower hσUpper u
  let Fσ : SchwartzMap ℝ ℂ := dfiVoronoiMellinKernelSchwartz hg σ
  have hPoint : ∀ v : ℝ, ‖Fσ v‖ ≤ ‖Fleft v‖ + ‖Fright v‖ := by
    intro v
    have hExp : Real.exp (-σ * v) ≤
        Real.exp (-c * v) + Real.exp (-d * v) := by
      by_cases hv : 0 ≤ v
      · have hlin : -σ * v ≤ -c * v := by nlinarith
        exact (Real.exp_le_exp.mpr hlin).trans
          (le_add_of_nonneg_right (Real.exp_pos _).le)
      · have hv' : v < 0 := lt_of_not_ge hv
        have hlin : -σ * v ≤ -d * v := by nlinarith
        exact (Real.exp_le_exp.mpr hlin).trans
          (le_add_of_nonneg_left (Real.exp_pos _).le)
    change ‖(Real.exp (-σ * v) : ℂ) * g (Real.exp (-v))‖ ≤
      ‖(Real.exp (-c * v) : ℂ) * g (Real.exp (-v))‖ +
      ‖(Real.exp (-d * v) : ℂ) * g (Real.exp (-v))‖
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    nlinarith [norm_nonneg (g (Real.exp (-v)))]
  have hLone : ‖Fσ.toLp 1‖ ≤ C := by
    rw [SchwartzMap.norm_toLp_one]
    calc
      (∫ v : ℝ, ‖Fσ v‖) ≤
          ∫ v : ℝ, (‖Fleft v‖ + ‖Fright v‖) := by
        exact integral_mono Fσ.integrable.norm
          (hLeftInt.add hRightInt) hPoint
      _ = C := by
        rw [integral_add hLeftInt hRightInt]
  rw [hg.mellin_eq_fourier_mellinKernel σ u]
  exact (SchwartzMap.norm_fourier_apply_le_toLp_one Fσ
    (u / (2 * Real.pi))).trans hLone

/-- Rapid Mellin decay on one arbitrary vertical line, expressed using the
inhomogeneous weight used by the DFI multiplier estimates. -/
theorem DFIVoronoiTestFunction.exists_mellin_one_add_abs_pow_line_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (j : ℕ) (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      (1 + |u|) ^ j *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨M, hM, hBound⟩ := hg.exists_mellin_interval_bound σ σ
  obtain ⟨D, hD, hDecay⟩ := hg.mellin_polynomial_decay σ j
  refine ⟨2 ^ (j - 1) * (M + D), by positivity, ?_⟩
  intro u
  have hMu : ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ M :=
    hBound σ le_rfl le_rfl u
  have hDu := hDecay u
  have hBinom : (1 + |u|) ^ j ≤ 2 ^ (j - 1) * (1 + |u| ^ j) := by
    simpa using add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg u) j
  calc
    (1 + |u|) ^ j *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        (2 ^ (j - 1) * (1 + |u| ^ j)) *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ :=
      mul_le_mul_of_nonneg_right hBinom (norm_nonneg _)
    _ = 2 ^ (j - 1) *
        (‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ +
          |u| ^ j * ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ 2 ^ (j - 1) * (M + D) := by gcongr

/-- The compact support gives a bound for the Mellin transform uniform on
the complete DFI contour-shift strip. -/
theorem DFIVoronoiTestFunction.exists_mellin_strip_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 3 / 2 → ∀ u : ℝ,
      ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C :=
  hg.exists_mellin_interval_bound (-(1 / 2 : ℝ)) (3 / 2 : ℝ)

theorem DFIVoronoiTestFunction.differentiable_mellin
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    Differentiable ℂ (mellin g) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow
    (hg.continuous.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0))
    (hg.isBigO_atTop (s.re + 1)) (by linarith)
    (hg.isBigO_atZero (s.re - 1)) (by linarith)

/-- Arbitrary-order polynomial Mellin bound on either boundary of the
standard DFI strip. -/
theorem DFIVoronoiTestFunction.exists_mellin_pow_boundary_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (j : ℕ) (σ : ℝ)
    (hσLower : -(1 / 2 : ℝ) ≤ σ) (hσUpper : σ ≤ 3 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖(((σ : ℂ) + (u : ℂ) * I) - 3) ^ j *
        mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨M, hM, hMellin⟩ := hg.exists_mellin_strip_bound
  obtain ⟨D, hD, hDecay⟩ := hg.mellin_polynomial_decay σ j
  refine ⟨4 ^ j * 2 ^ (j - 1) * (M + D), by positivity, ?_⟩
  intro u
  let s : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hSigma : |σ - 3| ≤ 4 := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hsNorm : ‖s - 3‖ ≤ 4 * (1 + |u|) := by
    calc
      ‖s - 3‖ ≤ |(s - 3).re| + |(s - 3).im| :=
        Complex.norm_le_abs_re_add_abs_im (s - 3)
      _ = |σ - 3| + |u| := by simp [s]
      _ ≤ 4 * (1 + |u|) := by nlinarith [abs_nonneg u]
  have hPow : ‖s - 3‖ ^ j ≤ 4 ^ j * (1 + |u|) ^ j := by
    simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg (s - 3)) hsNorm j
  have hBinom : (1 + |u|) ^ j ≤ 2 ^ (j - 1) * (1 + |u| ^ j) := by
    simpa using add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg u) j
  have hMu : ‖mellin g s‖ ≤ M := hMellin σ hσLower hσUpper u
  have hDu : |u| ^ j * ‖mellin g s‖ ≤ D := hDecay u
  have hCombined : (1 + |u| ^ j) * ‖mellin g s‖ ≤ M + D := by
    calc
      (1 + |u| ^ j) * ‖mellin g s‖ =
          ‖mellin g s‖ + |u| ^ j * ‖mellin g s‖ := by ring
      _ ≤ M + D := add_le_add hMu hDu
  rw [norm_mul, norm_pow]
  calc
    ‖s - 3‖ ^ j * ‖mellin g s‖ ≤
        (4 ^ j * (1 + |u|) ^ j) * ‖mellin g s‖ :=
      mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
    _ ≤ (4 ^ j * (2 ^ (j - 1) * (1 + |u| ^ j))) *
        ‖mellin g s‖ := by gcongr
    _ = 4 ^ j * 2 ^ (j - 1) *
        ((1 + |u| ^ j) * ‖mellin g s‖) := by ring
    _ ≤ 4 ^ j * 2 ^ (j - 1) * (M + D) := by gcongr

/-- Phragmén--Lindelöf makes the arbitrary-order boundary estimate uniform
throughout the standard DFI strip. -/
theorem DFIVoronoiTestFunction.exists_mellin_pow_strip_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 3 / 2 → ∀ u : ℝ,
      ‖(((σ : ℂ) + (u : ℂ) * I) - 3) ^ j *
        mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨Ca, hCa, hBoundA⟩ :=
    hg.exists_mellin_pow_boundary_bound j (-(1 / 2 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨Cb, hCb, hBoundB⟩ :=
    hg.exists_mellin_pow_boundary_bound j (3 / 2 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨M, hM, hMellin⟩ := hg.exists_mellin_strip_bound
  let f : ℂ → ℂ := fun s ↦ (s - 3) ^ j * mellin g s
  let strip : Set ℂ := Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (3 / 2 : ℝ)
  let l : Filter ℂ := comap (abs ∘ Complex.im) atTop ⊓ Filter.principal strip
  have hDiff : Differentiable ℂ f := by
    dsimp [f]
    exact ((differentiable_id.sub_const 3).pow j).mul hg.differentiable_mellin
  have hStripEventually : ∀ᶠ z : ℂ in l, z ∈ strip := by
    exact (show ∀ᶠ z : ℂ in Filter.principal strip, z ∈ strip by
      simp).filter_mono inf_le_right
  have hFPoly : f =O[l] (fun z : ℂ ↦ (4 + |z.im|) ^ j) := by
    apply IsBigO.of_bound M
    filter_upwards [hStripEventually] with z hz
    have hzLower : -(1 / 2 : ℝ) ≤ z.re := hz.1.le
    have hzUpper : z.re ≤ 3 / 2 := hz.2.le
    have hRe : |z.re - 3| ≤ 4 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hzNorm : ‖z - 3‖ ≤ 4 + |z.im| := by
      calc
        ‖z - 3‖ ≤ |(z - 3).re| + |(z - 3).im| :=
          Complex.norm_le_abs_re_add_abs_im (z - 3)
        _ = |z.re - 3| + |z.im| := by simp
        _ ≤ 4 + |z.im| := by linarith
    have hPow : ‖z - 3‖ ^ j ≤ (4 + |z.im|) ^ j := by
      simpa using pow_le_pow_left₀ (norm_nonneg (z - 3)) hzNorm j
    have hMellinZ : ‖mellin g z‖ ≤ M := by
      have hzEq : ((z.re : ℂ) + (z.im : ℂ) * I) = z := by
        apply Complex.ext <;> simp
      rw [← hzEq]
      exact hMellin z.re hzLower hzUpper z.im
    change ‖(z - 3) ^ j * mellin g z‖ ≤ M * ‖(4 + |z.im|) ^ j‖
    rw [norm_mul, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (4 + |z.im|) ^ j)]
    calc
      ‖z - 3‖ ^ j * ‖mellin g z‖ ≤
          (4 + |z.im|) ^ j * ‖mellin g z‖ :=
        mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
      _ ≤ (4 + |z.im|) ^ j * M :=
        mul_le_mul_of_nonneg_left hMellinZ (by positivity)
      _ = M * (4 + |z.im|) ^ j := by ring
  have hRealPoly :
      (fun t : ℝ ↦ (4 + t) ^ j) =O[atTop]
        (fun t : ℝ ↦ Real.exp (Real.exp t)) := by
    have hShift := (Real.isLittleO_pow_exp_atTop (n := j)).comp_tendsto
      (tendsto_atTop_add_const_left atTop (4 : ℝ) tendsto_id)
    have hFirst : (fun t : ℝ ↦ (4 + t) ^ j) =O[atTop]
        (fun t : ℝ ↦ Real.exp (t + 4)) := by
      simpa [add_comm] using hShift.isBigO
    have hSecond : (fun t : ℝ ↦ Real.exp (t + 4)) =O[atTop]
        (fun t : ℝ ↦ Real.exp (Real.exp t)) := by
      apply IsBigO.of_bound (Real.exp 4)
      filter_upwards with t
      have htExp : t ≤ Real.exp t :=
        (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)).trans
          (Real.add_one_le_exp t)
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [Real.exp_add]
      calc
        Real.exp t * Real.exp 4 = Real.exp 4 * Real.exp t := by ring
        _ ≤ Real.exp 4 * Real.exp (Real.exp t) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htExp)
            (Real.exp_pos 4).le
    exact hFirst.trans hSecond
  have hToTop : Tendsto (abs ∘ Complex.im) l atTop := by
    exact tendsto_comap.mono_left inf_le_left
  have hPolyComplex :
      (fun z : ℂ ↦ (4 + |z.im|) ^ j) =O[l]
        (fun z : ℂ ↦ Real.exp (Real.exp |z.im|)) := by
    simpa [Function.comp_def] using hRealPoly.comp_tendsto hToTop
  have hGrowth : ∃ c < Real.pi / ((3 / 2 : ℝ) - (-(1 / 2 : ℝ))), ∃ B,
      f =O[l] (fun z ↦ Real.exp (B * Real.exp (c * |z.im|))) := by
    refine ⟨1, ?_, 1, ?_⟩
    · nlinarith [Real.pi_gt_three]
    · simpa using hFPoly.trans hPolyComplex
  refine ⟨Ca + Cb, add_nonneg hCa hCb, ?_⟩
  intro σ hσLower hσUpper u
  let z : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hPL := PhragmenLindelof.vertical_strip
    (f := f) (a := -(1 / 2 : ℝ)) (b := (3 / 2 : ℝ))
    (C := Ca + Cb) hDiff.diffContOnCl (by simpa [l, strip] using hGrowth)
    (fun w hw ↦ by
      have hwEq : (-(1 / 2 : ℂ) + (w.im : ℂ) * I) = w := by
        apply Complex.ext
        · norm_num
          exact hw.symm
        · simp
      have h := (hBoundA w.im).trans (le_add_of_nonneg_right hCb)
      push_cast at h
      rw [hwEq] at h
      exact h)
    (fun w hw ↦ by
      have hwEq : ((3 / 2 : ℂ) + (w.im : ℂ) * I) = w := by
        apply Complex.ext
        · norm_num
          exact hw.symm
        · simp
      have h := (hBoundB w.im).trans (le_add_of_nonneg_left hCa)
      push_cast at h
      rw [hwEq] at h
      exact h)
    (z := z) (by simpa [z] using hσLower) (by simpa [z] using hσUpper)
  simpa [f, z] using hPL

theorem DFIVoronoiTestFunction.exists_mellin_six_boundary_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ)
    (hσLower : -(1 / 2 : ℝ) ≤ σ) (hσUpper : σ ≤ 3 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖(((σ : ℂ) + (u : ℂ) * I) - 3) ^ 6 *
        mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨M, hM, hMellin⟩ := hg.exists_mellin_strip_bound
  obtain ⟨D, hD, hDecay⟩ := hg.mellin_polynomial_decay σ 6
  refine ⟨4 ^ 6 * 2 ^ 5 * (M + D), by positivity, ?_⟩
  intro u
  let s : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hSigma : |σ - 3| ≤ 4 := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hsNorm : ‖s - 3‖ ≤ 4 * (1 + |u|) := by
    calc
      ‖s - 3‖ ≤ |(s - 3).re| + |(s - 3).im| :=
        Complex.norm_le_abs_re_add_abs_im (s - 3)
      _ = |σ - 3| + |u| := by simp [s]
      _ ≤ 4 * (1 + |u|) := by nlinarith [abs_nonneg u]
  have hPow : ‖s - 3‖ ^ 6 ≤ 4 ^ 6 * (1 + |u|) ^ 6 := by
    simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg (s - 3)) hsNorm 6
  have hBinom : (1 + |u|) ^ 6 ≤ 2 ^ 5 * (1 + |u| ^ 6) := by
    simpa using add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg u) 6
  have hMu : ‖mellin g s‖ ≤ M := hMellin σ hσLower hσUpper u
  have hDu : |u| ^ 6 * ‖mellin g s‖ ≤ D := hDecay u
  have hCombined : (1 + |u| ^ 6) * ‖mellin g s‖ ≤ M + D := by
    calc
      (1 + |u| ^ 6) * ‖mellin g s‖ =
          ‖mellin g s‖ + |u| ^ 6 * ‖mellin g s‖ := by ring
      _ ≤ M + D := add_le_add hMu hDu
  rw [norm_mul, norm_pow]
  calc
    ‖s - 3‖ ^ 6 * ‖mellin g s‖ ≤
        (4 ^ 6 * (1 + |u|) ^ 6) * ‖mellin g s‖ :=
      mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
    _ ≤ (4 ^ 6 * (2 ^ 5 * (1 + |u| ^ 6))) * ‖mellin g s‖ := by
      gcongr
    _ = 4 ^ 6 * 2 ^ 5 * ((1 + |u| ^ 6) * ‖mellin g s‖) := by ring
    _ ≤ 4 ^ 6 * 2 ^ 5 * (M + D) := by gcongr

/-- Phragmén--Lindelöf upgrades the two boundary estimates to a uniform
sixth-order decay estimate throughout the complete DFI shift strip. -/
theorem DFIVoronoiTestFunction.exists_mellin_six_strip_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 3 / 2 → ∀ u : ℝ,
      ‖(((σ : ℂ) + (u : ℂ) * I) - 3) ^ 6 *
        mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨Ca, hCa, hBoundA⟩ :=
    hg.exists_mellin_six_boundary_bound (-(1 / 2 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨Cb, hCb, hBoundB⟩ :=
    hg.exists_mellin_six_boundary_bound (3 / 2 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨M, hM, hMellin⟩ := hg.exists_mellin_strip_bound
  let f : ℂ → ℂ := fun s ↦ (s - 3) ^ 6 * mellin g s
  let strip : Set ℂ := Complex.re ⁻¹' Ioo (-(1 / 2 : ℝ)) (3 / 2 : ℝ)
  let l : Filter ℂ := comap (abs ∘ Complex.im) atTop ⊓ Filter.principal strip
  have hDiff : Differentiable ℂ f := by
    dsimp [f]
    exact ((differentiable_id.sub_const 3).pow 6).mul hg.differentiable_mellin
  have hStripEventually : ∀ᶠ z : ℂ in l, z ∈ strip := by
    exact (show ∀ᶠ z : ℂ in Filter.principal strip, z ∈ strip by
      simp).filter_mono inf_le_right
  have hFPoly : f =O[l] (fun z : ℂ ↦ (4 + |z.im|) ^ 6) := by
    apply IsBigO.of_bound M
    filter_upwards [hStripEventually] with z hz
    have hzLower : -(1 / 2 : ℝ) ≤ z.re := hz.1.le
    have hzUpper : z.re ≤ 3 / 2 := hz.2.le
    have hRe : |z.re - 3| ≤ 4 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hzNorm : ‖z - 3‖ ≤ 4 + |z.im| := by
      calc
        ‖z - 3‖ ≤ |(z - 3).re| + |(z - 3).im| :=
          Complex.norm_le_abs_re_add_abs_im (z - 3)
        _ = |z.re - 3| + |z.im| := by simp
        _ ≤ 4 + |z.im| := by linarith
    have hPow : ‖z - 3‖ ^ 6 ≤ (4 + |z.im|) ^ 6 := by
      simpa using pow_le_pow_left₀ (norm_nonneg (z - 3)) hzNorm 6
    have hMellinZ : ‖mellin g z‖ ≤ M := by
      have hzEq : ((z.re : ℂ) + (z.im : ℂ) * I) = z := by
        apply Complex.ext <;> simp
      rw [← hzEq]
      exact hMellin z.re hzLower hzUpper z.im
    change ‖(z - 3) ^ 6 * mellin g z‖ ≤ M * ‖(4 + |z.im|) ^ 6‖
    rw [norm_mul, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (4 + |z.im|) ^ 6)]
    calc
      ‖z - 3‖ ^ 6 * ‖mellin g z‖ ≤
          (4 + |z.im|) ^ 6 * ‖mellin g z‖ :=
        mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
      _ ≤ (4 + |z.im|) ^ 6 * M :=
        mul_le_mul_of_nonneg_left hMellinZ (by positivity)
      _ = M * (4 + |z.im|) ^ 6 := by ring
  have hRealPoly :
      (fun t : ℝ ↦ (4 + t) ^ 6) =O[atTop]
        (fun t : ℝ ↦ Real.exp (Real.exp t)) := by
    have hShift := (Real.isLittleO_pow_exp_atTop (n := 6)).comp_tendsto
      (tendsto_atTop_add_const_left atTop (4 : ℝ) tendsto_id)
    have hFirst : (fun t : ℝ ↦ (4 + t) ^ 6) =O[atTop]
        (fun t : ℝ ↦ Real.exp (t + 4)) := by
      simpa [add_comm] using hShift.isBigO
    have hSecond : (fun t : ℝ ↦ Real.exp (t + 4)) =O[atTop]
        (fun t : ℝ ↦ Real.exp (Real.exp t)) := by
      apply IsBigO.of_bound (Real.exp 4)
      filter_upwards with t
      have htExp : t ≤ Real.exp t :=
        (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)).trans
          (Real.add_one_le_exp t)
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [Real.exp_add]
      calc
        Real.exp t * Real.exp 4 = Real.exp 4 * Real.exp t := by ring
        _ ≤ Real.exp 4 * Real.exp (Real.exp t) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htExp)
            (Real.exp_pos 4).le
    exact hFirst.trans hSecond
  have hToTop : Tendsto (abs ∘ Complex.im) l atTop := by
    exact tendsto_comap.mono_left inf_le_left
  have hPolyComplex :
      (fun z : ℂ ↦ (4 + |z.im|) ^ 6) =O[l]
        (fun z : ℂ ↦ Real.exp (Real.exp |z.im|)) := by
    simpa [Function.comp_def] using hRealPoly.comp_tendsto hToTop
  have hGrowth : ∃ c < Real.pi / ((3 / 2 : ℝ) - (-(1 / 2 : ℝ))), ∃ B,
      f =O[l] (fun z ↦ Real.exp (B * Real.exp (c * |z.im|))) := by
    refine ⟨1, ?_, 1, ?_⟩
    · nlinarith [Real.pi_gt_three]
    · simpa using hFPoly.trans hPolyComplex
  refine ⟨Ca + Cb, add_nonneg hCa hCb, ?_⟩
  intro σ hσLower hσUpper u
  let z : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hPL := PhragmenLindelof.vertical_strip
    (f := f) (a := -(1 / 2 : ℝ)) (b := (3 / 2 : ℝ))
    (C := Ca + Cb) hDiff.diffContOnCl (by simpa [l, strip] using hGrowth)
    (fun w hw ↦ by
      have hwEq : (-(1 / 2 : ℂ) + (w.im : ℂ) * I) = w := by
        apply Complex.ext
        · norm_num
          exact hw.symm
        · simp
      have h := (hBoundA w.im).trans (le_add_of_nonneg_right hCb)
      push_cast at h
      rw [hwEq] at h
      exact h)
    (fun w hw ↦ by
      have hwEq : ((3 / 2 : ℂ) + (w.im : ℂ) * I) = w := by
        apply Complex.ext
        · norm_num
          exact hw.symm
        · simp
      have h := (hBoundB w.im).trans (le_add_of_nonneg_left hCa)
      push_cast at h
      rw [hwEq] at h
      exact h)
    (z := z) (by simpa [z] using hσLower) (by simpa [z] using hσUpper)
  simpa [f, z] using hPL

/-- Translating by the inverse source weight moves the sixth-order Mellin
bound one full unit to the left.  This is the strip used for the absolutely
convergent form of the DFI double Voronoi expansion. -/
theorem DFIVoronoiTestFunction.exists_mellin_six_deep_strip_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(3 / 2 : ℝ) ≤ σ → σ ≤ 1 / 2 → ∀ u : ℝ,
      ‖(((σ : ℂ) + (u : ℂ) * I) - 2) ^ 6 *
        mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨C, hC, hStrip⟩ := hg.invWeight.exists_mellin_six_strip_bound
  refine ⟨C, hC, ?_⟩
  intro σ hσLower hσUpper u
  let z : ℂ := (σ : ℂ) + (u : ℂ) * I
  have h := hStrip (σ + 1) (by linarith) (by linarith) u
  have hLine : (((σ + 1 : ℝ) : ℂ) + (u : ℂ) * I) = z + 1 := by
    dsimp [z]
    push_cast
    ring
  rw [hLine, hg.mellin_invWeight_add_one z] at h
  have hCenter : z + 1 - 3 = z - 2 := by ring
  rw [hCenter] at h
  exact h

/-- Arbitrary-order version of the preceding contour translation.  After
`k` inverse source weights, the standard sixth-order Mellin bound is valid
on the strip translated `k` units to the left. -/
theorem DFIVoronoiTestFunction.exists_mellin_six_shifted_strip_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) - k ≤ σ → σ ≤ 3 / 2 - k → ∀ u : ℝ,
      ‖(((σ : ℂ) + (u : ℂ) * I) + k - 3) ^ 6 *
        mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨C, hC, hStrip⟩ :=
    (hg.invWeightIterate k).exists_mellin_six_strip_bound
  refine ⟨C, hC, ?_⟩
  intro σ hσLower hσUpper u
  let z : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hLower : -(1 / 2 : ℝ) ≤ σ + k := by
    norm_num at hσLower ⊢
    linarith
  have hUpper : σ + k ≤ 3 / 2 := by
    norm_num at hσUpper ⊢
    linarith
  have h := hStrip (σ + k) hLower hUpper u
  have hLine : (((σ + k : ℝ) : ℂ) + (u : ℂ) * I) = z + k := by
    dsimp [z]
    push_cast
    ring
  rw [hLine, hg.mellin_invWeightIterate_add_nat k z] at h
  exact h

/-- Arbitrary vertical polynomial order on every integer translate of the
DFI Mellin strip. -/
theorem DFIVoronoiTestFunction.exists_mellin_pow_shifted_strip_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (j k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) - k ≤ σ → σ ≤ 3 / 2 - k → ∀ u : ℝ,
      ‖(((σ : ℂ) + (u : ℂ) * I) + k - 3) ^ j *
        mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨C, hC, hStrip⟩ :=
    (hg.invWeightIterate k).exists_mellin_pow_strip_bound j
  refine ⟨C, hC, ?_⟩
  intro σ hσLower hσUpper u
  let z : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hLower : -(1 / 2 : ℝ) ≤ σ + k := by
    norm_num at hσLower ⊢
    linarith
  have hUpper : σ + k ≤ 3 / 2 := by
    norm_num at hσUpper ⊢
    linarith
  have h := hStrip (σ + k) hLower hUpper u
  have hLine : (((σ + k : ℝ) : ℂ) + (u : ℂ) * I) = z + k := by
    dsimp [z]
    push_cast
    ring
  rw [hLine, hg.mellin_invWeightIterate_add_nat k z] at h
  exact h

/-- Uniform rapid decay in the standard `1 + |u|` weight on every translated
DFI strip.  This is the form used simultaneously on vertical and horizontal
sides of the equation (29) contour rectangles. -/
theorem DFIVoronoiTestFunction.exists_mellin_one_add_abs_pow_shifted_strip_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (j k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) - k ≤ σ → σ ≤ 3 / 2 - k → ∀ u : ℝ,
      (1 + |u|) ^ j *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨C₀, hC₀, hZero⟩ := hg.exists_mellin_pow_shifted_strip_bound 0 k
  obtain ⟨Cj, hCj, hPowBound⟩ := hg.exists_mellin_pow_shifted_strip_bound j k
  refine ⟨2 ^ (j - 1) * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσLower hσUpper u
  let z : ℂ := (σ : ℂ) + (u : ℂ) * I
  let center : ℂ := z + k - 3
  have hZero' : ‖mellin g z‖ ≤ C₀ := by
    simpa [z] using hZero σ hσLower hσUpper u
  have hWeighted : ‖center‖ ^ j * ‖mellin g z‖ ≤ Cj := by
    have h := hPowBound σ hσLower hσUpper u
    rw [norm_mul, norm_pow] at h
    simpa [center, z] using h
  have hCenterIm : center.im = u := by simp [center, z]
  have hAbs : |u| ≤ ‖center‖ := by
    simpa [hCenterIm] using Complex.abs_im_le_norm center
  have hAbsPow : |u| ^ j ≤ ‖center‖ ^ j :=
    pow_le_pow_left₀ (abs_nonneg u) hAbs j
  have hDecay : |u| ^ j * ‖mellin g z‖ ≤ Cj :=
    (mul_le_mul_of_nonneg_right hAbsPow (norm_nonneg _)).trans hWeighted
  have hBinom : (1 + |u|) ^ j ≤ 2 ^ (j - 1) * (1 + |u| ^ j) := by
    simpa using add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg u) j
  calc
    (1 + |u|) ^ j * ‖mellin g z‖ ≤
        (2 ^ (j - 1) * (1 + |u| ^ j)) * ‖mellin g z‖ :=
      mul_le_mul_of_nonneg_right hBinom (norm_nonneg _)
    _ = 2 ^ (j - 1) *
        (‖mellin g z‖ + |u| ^ j * ‖mellin g z‖) := by ring
    _ ≤ 2 ^ (j - 1) * (C₀ + Cj) := by gcongr

/-- Uniform sixth-order vertical decay on every integer translate of the
DFI Mellin strip. -/
theorem DFIVoronoiTestFunction.exists_mellin_decay_shifted_strip
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) - k ≤ σ → σ ≤ 3 / 2 - k → ∀ u : ℝ, 1 ≤ |u| →
      (1 + |u|) ^ 6 *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨D, hD, hStrip⟩ := hg.exists_mellin_six_shifted_strip_bound k
  let R : ℝ := 2 + |(k : ℝ) - 3|
  have hR : 0 ≤ R := by positivity
  refine ⟨R ^ 6 * D, mul_nonneg (pow_nonneg hR 6) hD, ?_⟩
  intro σ hσLower hσUpper u hu
  let s : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hIm : |u| ≤ ‖s + k - 3‖ := by
    have him := Complex.abs_im_le_norm (s + k - 3)
    simpa [s] using him
  have hLinear : 1 + |u| ≤ R * ‖s + k - 3‖ := by
    have hNormOne : 1 ≤ ‖s + k - 3‖ := by
      calc
        1 ≤ |u| := hu
        _ ≤ ‖s + k - 3‖ := hIm
    have hRone : 2 ≤ R := by
      dsimp [R]
      linarith [abs_nonneg ((k : ℝ) - 3)]
    calc
      1 + |u| ≤ 2 * ‖s + k - 3‖ := by nlinarith
      _ ≤ R * ‖s + k - 3‖ := by gcongr
  have hPow : (1 + |u|) ^ 6 ≤
      R ^ 6 * ‖s + k - 3‖ ^ 6 := by
    simpa [mul_pow] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |u|) hLinear 6
  have hStrip' := hStrip σ hσLower hσUpper u
  rw [norm_mul, norm_pow] at hStrip'
  calc
    (1 + |u|) ^ 6 * ‖mellin g s‖ ≤
        (R ^ 6 * ‖s + k - 3‖ ^ 6) * ‖mellin g s‖ :=
      mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
    _ = R ^ 6 * (‖s + k - 3‖ ^ 6 * ‖mellin g s‖) := by ring
    _ ≤ R ^ 6 * D := by gcongr

theorem DFIVoronoiTestFunction.exists_mellin_decay_strip
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 3 / 2 → ∀ u : ℝ, 1 ≤ |u| →
      (1 + |u|) ^ 6 *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨D, hD, hStrip⟩ := hg.exists_mellin_six_strip_bound
  refine ⟨2 ^ 6 * D, by positivity, ?_⟩
  intro σ hσLower hσUpper u hu
  let s : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hIm : |u| ≤ ‖s - 3‖ := by
    have := Complex.abs_im_le_norm (s - 3)
    simpa [s] using this
  have hLinear : 1 + |u| ≤ 2 * ‖s - 3‖ := by
    nlinarith
  have hPow : (1 + |u|) ^ 6 ≤ 2 ^ 6 * ‖s - 3‖ ^ 6 := by
    simpa [mul_pow] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |u|) hLinear 6
  have hStrip' := hStrip σ hσLower hσUpper u
  rw [norm_mul, norm_pow] at hStrip'
  calc
    (1 + |u|) ^ 6 * ‖mellin g s‖ ≤
        (2 ^ 6 * ‖s - 3‖ ^ 6) * ‖mellin g s‖ :=
      mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
    _ = 2 ^ 6 * (‖s - 3‖ ^ 6 * ‖mellin g s‖) := by ring
    _ ≤ 2 ^ 6 * D := by gcongr

/-- Sixth-order vertical decay on the left-shifted DFI Mellin strip. -/
theorem DFIVoronoiTestFunction.exists_mellin_decay_deep_strip
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(3 / 2 : ℝ) ≤ σ → σ ≤ 1 / 2 → ∀ u : ℝ, 1 ≤ |u| →
      (1 + |u|) ^ 6 *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  obtain ⟨D, hD, hStrip⟩ := hg.exists_mellin_six_deep_strip_bound
  refine ⟨2 ^ 6 * D, by positivity, ?_⟩
  intro σ hσLower hσUpper u hu
  let s : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hIm : |u| ≤ ‖s - 2‖ := by
    have := Complex.abs_im_le_norm (s - 2)
    simpa [s] using this
  have hLinear : 1 + |u| ≤ 2 * ‖s - 2‖ := by
    nlinarith
  have hPow : (1 + |u|) ^ 6 ≤ 2 ^ 6 * ‖s - 2‖ ^ 6 := by
    simpa [mul_pow] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |u|) hLinear 6
  have hStrip' := hStrip σ hσLower hσUpper u
  rw [norm_mul, norm_pow] at hStrip'
  calc
    (1 + |u|) ^ 6 * ‖mellin g s‖ ≤
        (2 ^ 6 * ‖s - 2‖ ^ 6) * ‖mellin g s‖ :=
      mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
    _ = 2 ^ 6 * (‖s - 2‖ ^ 6 * ‖mellin g s‖) := by ring
    _ ≤ 2 ^ 6 * D := by gcongr

theorem DFIVoronoiTestFunction.exists_periodicEstermann_mul_mellin_strip_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 3 / 2 → ∀ u : ℝ, 1 ≤ |u| →
      ‖periodicEstermann q Φ ((σ : ℂ) + (u : ℂ) * I) *
        mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          C / (1 + |u|) ^ 2 := by
  obtain ⟨D, hD, hMellin⟩ := hg.exists_mellin_decay_strip
  let A : ℝ := periodicEstermannStripConstant q Φ
  have hA : 0 ≤ A := add_nonneg
    (periodicEstermannLeftStripConstant_nonneg q Φ)
    (periodicEstermannRightStripConstant_nonneg q Φ)
  refine ⟨A * D, mul_nonneg hA hD, ?_⟩
  intro σ hσLower hσUpper u hu
  have hEst := norm_periodicEstermann_le_strip q Φ hσLower hσUpper hu
  have hMel := hMellin σ hσLower hσUpper u hu
  have hPos : 0 < (1 + |u|) ^ 2 := by positivity
  apply (le_div_iff₀ hPos).2
  rw [norm_mul]
  calc
    ‖periodicEstermann q Φ ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ * (1 + |u|) ^ 2 ≤
        (A * (1 + |u|) ^ 4) *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ * (1 + |u|) ^ 2 := by
      gcongr
    _ = A * ((1 + |u|) ^ 6 *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ A * D := mul_le_mul_of_nonneg_left hMel hA

/-- The two horizontal sides and the two vertical tails in the DFI
rectangle tend to zero.  This discharges the final analytic premise of the
finite-to-infinite Estermann contour shift. -/
theorem DFIVoronoiTestFunction.periodicEstermann_mul_mellin_tails
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) :
    Tendsto (fun H : ℝ ↦
      (1 / (2 * Real.pi * I)) •
        (UpperUIntegral (fun s : ℂ ↦ periodicEstermann q Φ s * mellin g s)
            (-(1 / 2 : ℝ)) (3 / 2 : ℝ) H -
          LowerUIntegral (fun s : ℂ ↦ periodicEstermann q Φ s * mellin g s)
            (-(1 / 2 : ℝ)) (3 / 2 : ℝ) H))
      atTop (nhds 0) := by
  let f : ℂ → ℂ := fun s ↦ periodicEstermann q Φ s * mellin g s
  obtain ⟨C, hC, hDecay⟩ :=
    hg.exists_periodicEstermann_mul_mellin_strip_decay q Φ
  let envelope : ℝ → ℝ := fun H ↦ C / (1 + |H|) ^ 2
  have hEnv0 : Tendsto envelope atTop (nhds 0) := by
    have hDen : Tendsto (fun H : ℝ ↦ (1 + |H|) ^ 2) atTop atTop := by
      have hAbs : Tendsto (fun H : ℝ ↦ |H|) atTop atTop := by
        exact tendsto_atTop_mono' atTop (Eventually.of_forall fun H ↦ le_abs_self H)
          tendsto_id
      exact tendsto_pow_atTop (by norm_num) |>.comp
        (tendsto_const_nhds.add_atTop hAbs)
    exact tendsto_const_nhds.div_atTop hDen
  have hTop : Tendsto (fun H : ℝ ↦
      HIntegral f (-(1 / 2 : ℝ)) (3 / 2 : ℝ) H) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      unfold HIntegral
      have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun x : ℝ ↦ f (x + H * I)) (C := envelope H)
        (fun x hx ↦ by
          have hx' : x ∈ Set.uIcc (-(1 / 2 : ℝ)) (3 / 2 : ℝ) :=
            Set.uIoc_subset_uIcc hx
          have hxBounds : -(1 / 2 : ℝ) ≤ x ∧ x ≤ 3 / 2 := by
            rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 3 / 2)] at hx'
            exact hx'
          simpa [f, envelope] using hDecay x hxBounds.1 hxBounds.2 H
            (by rw [abs_of_nonneg (by linarith)]; exact hH))
      simpa [envelope] using hInt
    · convert hEnv0.mul_const (2 : ℝ) using 1 <;> norm_num [envelope]
  have hBottom : Tendsto (fun H : ℝ ↦
      HIntegral f (-(1 / 2 : ℝ)) (3 / 2 : ℝ) (-H)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      unfold HIntegral
      have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun x : ℝ ↦ f (x + (-H) * I)) (C := envelope H)
        (fun x hx ↦ by
          have hx' : x ∈ Set.uIcc (-(1 / 2 : ℝ)) (3 / 2 : ℝ) :=
            Set.uIoc_subset_uIcc hx
          have hxBounds : -(1 / 2 : ℝ) ≤ x ∧ x ≤ 3 / 2 := by
            rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 3 / 2)] at hx'
            exact hx'
          simpa [f, envelope, abs_neg] using hDecay x hxBounds.1 hxBounds.2 (-H)
            (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hH))
      simpa [envelope] using hInt
    · convert hEnv0.mul_const (2 : ℝ) using 1 <;> norm_num [envelope]
  have hIntLeft := hg.integrable_periodicEstermann_mul_mellin_left q Φ
  have hIntRight := hg.integrable_periodicEstermann_mul_mellin_right q Φ
    (c := (3 / 2 : ℝ)) (by norm_num)
  have hRightTop : Tendsto (fun H : ℝ ↦
      ∫ y : ℝ in Ici H, f ((3 / 2 : ℝ) + y * I)) atTop (nhds 0) := by
    exact tendsto_integral_Ici_zero tendsto_id
  have hLeftTop : Tendsto (fun H : ℝ ↦
      ∫ y : ℝ in Ici H, f (-(1 / 2 : ℝ) + y * I)) atTop (nhds 0) := by
    exact tendsto_integral_Ici_zero tendsto_id
  have hRightBottom : Tendsto (fun H : ℝ ↦
      ∫ y : ℝ in Iic (-H), f ((3 / 2 : ℝ) + y * I)) atTop (nhds 0) := by
    exact tendsto_integral_Iic_zero tendsto_neg_atTop_atBot
  have hLeftBottom : Tendsto (fun H : ℝ ↦
      ∫ y : ℝ in Iic (-H), f (-(1 / 2 : ℝ) + y * I)) atTop (nhds 0) := by
    exact tendsto_integral_Iic_zero tendsto_neg_atTop_atBot
  have hUpper : Tendsto (fun H : ℝ ↦
      UpperUIntegral f (-(1 / 2 : ℝ)) (3 / 2 : ℝ) H) atTop (nhds 0) := by
    simpa [UpperUIntegral] using
      hTop.add (hRightTop.const_smul I) |>.sub (hLeftTop.const_smul I)
  have hLower : Tendsto (fun H : ℝ ↦
      LowerUIntegral f (-(1 / 2 : ℝ)) (3 / 2 : ℝ) H) atTop (nhds 0) := by
    simpa [LowerUIntegral] using
      hBottom.sub (hRightBottom.const_smul I) |>.add (hLeftBottom.const_smul I)
  simpa [f] using
    (hUpper.sub hLower).const_smul (1 / (2 * Real.pi * I))

/-- DFI Proposition 1 in exact Mellin--Barnes form, with every analytic
hypothesis discharged for the source test-function class. -/
theorem DFIVoronoiTestFunction.periodicDivisorVoronoi_mellinBarnes_native
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) :
    periodicDivisorWeightedSum q Φ g =
      periodicEstermannPoleCleared q Φ 1 * deriv (mellin g) 1 +
        periodicEstermannResidueCoeff q Φ * mellin g 1 +
        VerticalIntegral'
          (periodicEstermannReflectedIntegrand q Φ (mellin g))
          (-(1 / 2 : ℝ)) := by
  apply periodicDivisorVoronoi_mellinBarnes q Φ g (mellin g)
    hg.differentiable_mellin (d := -(1 / 2 : ℝ)) (c := (3 / 2 : ℝ))
    (by norm_num) (by norm_num) rfl
  · intro n hn
    exact hg.mellinInversion (3 / 2 : ℝ) (by exact_mod_cast hn)
  · intro n
    exact hg.integrable_periodicDivisorMellinTerm q Φ (3 / 2 : ℝ) n
  · exact DFIVoronoiTestFunction.summable_integral_norm_periodicDivisorMellinTerm
      g q Φ (by norm_num)
  · simpa only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using
      hg.integrable_periodicEstermann_mul_mellin_left q Φ
  · exact hg.integrable_periodicEstermann_mul_mellin_right q Φ (by norm_num)
  · exact hg.periodicEstermann_mul_mellin_tails q Φ

end RiemannZeta.GuthMaynard
