import GafniTao.FordZeroDetectorEdges
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalAverage

/-!
# Convexity input for Ford's explicit real-axis zeta bound

Ford bounds the zeta series by integrating the convex function
`x ↦ x⁻ˢ` over unit intervals centred at the integers.  This file proves
the source convexity statement on the entire physical range `x ≥ 1`.
-/

open Set MeasureTheory intervalIntegral Filter Topology
open scoped Interval

namespace GafniTao

theorem ford_convexOn_rpow_neg {sigma : ℝ} (hsigma : 0 < sigma) :
    ConvexOn ℝ (Ici 1) (fun x : ℝ => x ^ (-sigma)) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici (1 : ℝ))
  · intro x hx
    have hx1 : 1 ≤ x := hx
    exact (Real.continuousAt_rpow_const x (-sigma)
      (Or.inl (by linarith : x ≠ 0))).continuousWithinAt
  · intro x hx
    have hxpos : 0 < x := by
      rw [interior_Ici] at hx
      exact zero_lt_one.trans hx
    exact (Real.hasDerivAt_rpow_const (x := x) (p := -sigma)
      (Or.inl hxpos.ne')).hasDerivWithinAt
  · intro x hx
    have hxpos : 0 < x := by
      rw [interior_Ici] at hx
      exact zero_lt_one.trans hx
    exact ((Real.hasDerivAt_rpow_const (x := x) (p := -sigma - 1)
      (Or.inl hxpos.ne')).const_mul (-sigma)).hasDerivWithinAt
  · intro x hx
    have hxpos : 0 < x := by
      rw [interior_Ici] at hx
      exact zero_lt_one.trans hx
    have hpow : 0 < x ^ (-sigma - 2) := Real.rpow_pos_of_pos hxpos _
    have hcoeff : 0 < (-sigma) * (-sigma - 1) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    rw [show -sigma - 1 - 1 = -sigma - 2 by ring]
    rw [← mul_assoc]
    exact mul_nonneg hcoeff.le hpow.le

/-- Each value at an integer at least two is bounded by the integral over
the unit interval centred at that integer. -/
theorem ford_rpow_le_centered_integral
    {sigma : ℝ} (hsigma : 0 < sigma) {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ (-sigma) ≤
      ∫ x in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2), x ^ (-sigma) := by
  let a : ℝ := (n : ℝ) - 1 / 2
  let b : ℝ := (n : ℝ) + 1 / 2
  have hab : a < b := by dsimp [a, b]; linarith
  have ha : 1 ≤ a := by
    dsimp [a]
    have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsub : uIcc a b ⊆ Ici (1 : ℝ) := by
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    have hx' : a ≤ x := (mem_Icc.mp hx).1
    exact ha.trans hx'
  have hcont : ContinuousOn (fun x : ℝ => x ^ (-sigma)) (Ici 1) := by
    intro x hx
    have hx1 : 1 ≤ x := hx
    exact (Real.continuousAt_rpow_const x (-sigma)
      (Or.inl (by linarith : x ≠ 0))).continuousWithinAt
  have havgId : (⨍ x in a..b, x) = (n : ℝ) := by
    rw [interval_average_eq_div, integral_id]
    dsimp [a, b]
    ring
  have hJensen :
      (fun x : ℝ => x ^ (-sigma)) (⨍ x in a..b, x) ≤
        ⨍ x in a..b, x ^ (-sigma) := by
    refine (ford_convexOn_rpow_neg hsigma).map_set_average_le
      (t := uIoc a b) (f := id) (g := fun x : ℝ => x ^ (-sigma))
      hcont isClosed_Ici ?_ ?_ ?_ ?_ ?_
    · rw [Real.volume_uIoc, ENNReal.ofReal_ne_zero_iff]
      positivity
    · rw [Real.volume_uIoc]
      exact ENNReal.ofReal_ne_top
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
      exact hsub (uIoc_subset_uIcc hx)
    · exact continuous_id.integrableOn_uIoc
    · exact (hcont.mono hsub).integrableOn_Icc.mono_set uIoc_subset_uIcc
  rw [havgId] at hJensen
  rw [interval_average_eq_div] at hJensen
  have hlen : b - a = 1 := by dsimp [a, b]; ring
  rw [hlen, div_one] at hJensen
  exact hJensen

/-- The centered intervals used by Ford, reindexed from zero. -/
noncomputable def fordCenteredIntegral (sigma : ℝ) (k : ℕ) : ℝ :=
  ∫ x in ((k : ℝ) + 3 / 2)..((k : ℝ) + 5 / 2), x ^ (-sigma)

theorem fordCenteredIntegral_nonneg (sigma : ℝ) (k : ℕ) :
    0 ≤ fordCenteredIntegral sigma k := by
  unfold fordCenteredIntegral
  apply intervalIntegral.integral_nonneg
  · linarith
  · intro x hx
    exact Real.rpow_nonneg (by linarith [hx.1]) _

theorem fordCenteredIntegral_eq
    {sigma : ℝ} (hsigma : 1 < sigma) (k : ℕ) :
    fordCenteredIntegral sigma k =
      (((k : ℝ) + 3 / 2) ^ (1 - sigma) -
        ((k : ℝ) + 5 / 2) ^ (1 - sigma)) / (sigma - 1) := by
  unfold fordCenteredIntegral
  rw [integral_rpow]
  · have hinv : (1 - sigma)⁻¹ = -(sigma - 1)⁻¹ := by
      rw [show 1 - sigma = -(sigma - 1) by ring, inv_neg]
    rw [show -sigma + 1 = 1 - sigma by ring, div_eq_mul_inv, hinv]
    ring
  · right
    constructor
    · linarith
    · rw [uIcc_of_le (by linarith : (k : ℝ) + 3 / 2 ≤ (k : ℝ) + 5 / 2)]
      intro hzero
      exact (not_lt_of_ge hzero.1) (by positivity)

theorem hasSum_fordCenteredIntegral {sigma : ℝ} (hsigma : 1 < sigma) :
    HasSum (fordCenteredIntegral sigma)
      ((3 / 2 : ℝ) ^ (1 - sigma) / (sigma - 1)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fordCenteredIntegral_nonneg sigma)]
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 3 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => ((n : ℝ) + 3 / 2) ^ (1 - sigma))
      atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (sub_pos.mpr hsigma)).comp hbase using 1
    · ext n
      congr 1
      ring
  have hdiv : Tendsto
      (fun n : ℕ => ((n : ℝ) + 3 / 2) ^ (1 - sigma) / (sigma - 1))
      atTop (𝓝 0) := by
      simpa using hpow.div_const (sigma - 1)
  have hsum (n : ℕ) :
      (∑ k ∈ Finset.range n, fordCenteredIntegral sigma k) =
        (3 / 2 : ℝ) ^ (1 - sigma) / (sigma - 1) -
          ((n : ℝ) + 3 / 2) ^ (1 - sigma) / (sigma - 1) := by
    simp_rw [fordCenteredIntegral_eq hsigma]
    rw [← Finset.sum_div]
    have htel := Finset.sum_range_sub
        (fun k : ℕ => ((k : ℝ) + 3 / 2) ^ (1 - sigma)) n
    rw [show (∑ k ∈ Finset.range n,
        (((k : ℝ) + 3 / 2) ^ (1 - sigma) -
          ((k : ℝ) + 5 / 2) ^ (1 - sigma))) =
        (3 / 2 : ℝ) ^ (1 - sigma) -
          ((n : ℝ) + 3 / 2) ^ (1 - sigma) by
        calc
          _ = -(∑ k ∈ Finset.range n,
              ((((k + 1 : ℕ) : ℝ) + 3 / 2) ^ (1 - sigma) -
                ((k : ℝ) + 3 / 2) ^ (1 - sigma))) := by
                  rw [← Finset.sum_neg_distrib]
                  apply Finset.sum_congr rfl
                  intro k hk
                  push_cast
                  ring_nf
          _ = _ := by simpa using congrArg Neg.neg htel]
    ring
  have ht : Tendsto
      (fun n : ℕ => (3 / 2 : ℝ) ^ (1 - sigma) / (sigma - 1) -
        ((n : ℝ) + 3 / 2) ^ (1 - sigma) / (sigma - 1))
      atTop (𝓝 ((3 / 2 : ℝ) ^ (1 - sigma) / (sigma - 1) - 0)) :=
    tendsto_const_nhds.sub hdiv
  simpa only [hsum, sub_zero] using ht

theorem summable_ford_rpow_tail {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun k : ℕ => (((k + 2 : ℕ) : ℝ) ^ (-sigma))) := by
  have hall : Summable (fun n : ℕ => ((n : ℝ) ^ (-sigma))) := by
    simpa only [Real.rpow_neg (Nat.cast_nonneg _)] using
      (Real.summable_nat_rpow_inv.mpr hsigma)
  simpa using (summable_nat_add_iff 2).mpr hall

theorem ford_rpow_tail_le_centered {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' k : ℕ, (((k + 2 : ℕ) : ℝ) ^ (-sigma))) ≤
      (3 / 2 : ℝ) ^ (1 - sigma) / (sigma - 1) := by
  rw [← (hasSum_fordCenteredIntegral hsigma).tsum_eq]
  apply (summable_ford_rpow_tail hsigma).tsum_le_tsum
    (fun k => ?_) (hasSum_fordCenteredIntegral hsigma).summable
  have h := ford_rpow_le_centered_integral (show 0 < sigma by linarith)
      (n := k + 2) (by omega)
  convert h using 1
  all_goals simp only [fordCenteredIntegral, Nat.cast_add, Nat.cast_ofNat]
  all_goals ring_nf

theorem ford_riemannZeta_real_series {sigma : ℝ} (hsigma : 1 < sigma) :
    (riemannZeta (sigma : ℂ)).re =
      ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-sigma)) := by
  have hsummable : Summable
      (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (sigma : ℂ)) := by
    have hall := Complex.summable_one_div_nat_cpow.mpr
      (show 1 < (sigma : ℂ).re by simpa using hsigma)
    simpa [Nat.cast_add] using (summable_nat_add_iff 1).mpr hall
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hsigma),
    Complex.re_tsum hsummable]
  apply tsum_congr
  intro n
  rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (x := ((n + 1 : ℕ) : ℝ)) (by positivity)
      (y := sigma)]
  rw [Real.rpow_neg (by positivity)]
  simp [← Complex.ofReal_inv]

theorem ford_riemannZeta_real_le_centered
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (riemannZeta (sigma : ℂ)).re ≤
      1 + (3 / 2 : ℝ) ^ (1 - sigma) / (sigma - 1) := by
  rw [ford_riemannZeta_real_series hsigma]
  have hsummable : Summable
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-sigma))) := by
    have hall : Summable (fun n : ℕ => ((n : ℝ) ^ (-sigma))) := by
      simpa only [Real.rpow_neg (Nat.cast_nonneg _)] using
        (Real.summable_nat_rpow_inv.mpr hsigma)
    simpa using (summable_nat_add_iff 1).mpr hall
  rw [hsummable.tsum_eq_zero_add]
  norm_num
  convert ford_rpow_tail_le_centered hsigma using 1
  congr 1 with b
  congr 1
  push_cast
  ring

/-- Ford's elementary second-order exponential estimate. -/
theorem ford_exp_neg_le_quadratic {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - Real.exp (-x)
  let f' : ℝ → ℝ := fun x => -1 + x + Real.exp (-x)
  have hderiv (x : ℝ) : HasDerivAt f (f' x) x := by
    dsimp [f, f']
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (-u))
        (-Real.exp (-x)) x := by
      convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1
      ring
    convert (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const 2)).sub hexp using 1
    all_goals simp only [id_eq]
    all_goals ring_nf
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
    · intro x hx
      exact (hderiv x).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      dsimp [f']
      have hexp := Real.add_one_le_exp (-x)
      linarith
  have hcompare := hmono (show 0 ∈ Ici (0 : ℝ) by simp)
    (show y ∈ Ici (0 : ℝ) by exact hy) hy
  dsimp [f] at hcompare
  norm_num at hcompare
  linarith

theorem ford_log_three_halves_lower :
    (152 / 375 : ℝ) ≤ Real.log (3 / 2) := by
  have hsum := Real.hasSum_log_one_add (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hle := sum_le_hasSum (Finset.range 2) (fun k hk => by positivity) hsum
  norm_num at hle ⊢
  exact hle

theorem ford_log_three_halves_upper :
    Real.log (3 / 2) ≤ (5 / 12 : ℝ) := by
  let f : ℝ → ℝ := fun x => x - x ^ 2 / 2 + x ^ 3 / 3 - Real.log (1 + x)
  let f' : ℝ → ℝ := fun x => 1 - x + x ^ 2 - (1 + x)⁻¹
  have hderiv (x : ℝ) (hx : 0 ≤ x) : HasDerivAt f (f' x) x := by
    dsimp [f, f']
    have hne : 1 + x ≠ 0 := by linarith
    have hlog : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 + x)⁻¹ x := by
      convert (Real.hasDerivAt_log hne).comp x
        ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)) using 1
      ring
    convert ((((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2).div_const 2)).add
      (((hasDerivAt_id x).pow 3).div_const 3)).sub hlog) using 1
    all_goals simp only [id_eq]
    all_goals ring_nf
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x hx.le).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hden : 0 < 1 + x := add_pos_of_pos_of_nonneg zero_lt_one hx.le
      dsimp [f']
      rw [inv_eq_one_div]
      rw [sub_nonneg, div_le_iff₀ hden]
      nlinarith [mul_nonneg hx.le (sq_nonneg x)]
  have hcompare := hmono (show 0 ∈ Ici (0 : ℝ) by simp)
    (show (1 / 2 : ℝ) ∈ Ici 0 by norm_num) (by norm_num)
  dsimp [f] at hcompare
  norm_num at hcompare ⊢
  linarith

theorem ford_three_halves_rpow_linear
    {sigma : ℝ} (hsigma : 1 < sigma) (hsigmaUpper : sigma ≤ 53 / 50) :
    (3 / 2 : ℝ) ^ (1 - sigma) ≤ 1 - (2 / 5) * (sigma - 1) := by
  let u : ℝ := sigma - 1
  let L : ℝ := Real.log (3 / 2)
  have hu : 0 < u := by dsimp [u]; linarith
  have huUpper : u ≤ 3 / 50 := by dsimp [u]; linarith
  have hLlower : (152 / 375 : ℝ) ≤ L := by
    exact ford_log_three_halves_lower
  have hLupper : L ≤ (5 / 12 : ℝ) := ford_log_three_halves_upper
  have hLnonneg : 0 ≤ L := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2))
  have hLsq : L ^ 2 ≤ (5 / 12 : ℝ) ^ 2 := by
    nlinarith [mul_self_le_mul_self hLnonneg hLupper]
  have huLsq : u * L ^ 2 ≤ (3 / 50 : ℝ) * (5 / 12 : ℝ) ^ 2 := by
    exact mul_le_mul huUpper hLsq (sq_nonneg L) (by norm_num)
  have hcoefficient : (2 / 5 : ℝ) ≤ L - u * L ^ 2 / 2 := by
    nlinarith
  have huy : 0 ≤ u * L := mul_nonneg hu.le hLnonneg
  have hquad := ford_exp_neg_le_quadratic huy
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  have hexponent : Real.log (3 / 2) * (1 - sigma) = -(u * L) := by
    dsimp [u, L]
    ring
  rw [hexponent]
  calc
    Real.exp (-(u * L)) ≤ 1 - u * L + (u * L) ^ 2 / 2 := hquad
    _ ≤ 1 - (2 / 5) * u := by
      have hmul := mul_le_mul_of_nonneg_left hcoefficient hu.le
      nlinarith [hmul]
    _ = 1 - (2 / 5) * (sigma - 1) := by rfl

theorem ford_riemannZeta_real_le_explicit
    {sigma : ℝ} (hsigma : 1 < sigma) (hsigmaUpper : sigma ≤ 53 / 50) :
    (riemannZeta (sigma : ℂ)).re ≤ 3 / 5 + 1 / (sigma - 1) := by
  let u : ℝ := sigma - 1
  have hu : 0 < u := by dsimp [u]; linarith
  calc
    (riemannZeta (sigma : ℂ)).re ≤
        1 + (3 / 2 : ℝ) ^ (1 - sigma) / (sigma - 1) :=
      ford_riemannZeta_real_le_centered hsigma
    _ ≤ 1 + (1 - (2 / 5) * (sigma - 1)) / (sigma - 1) := by
      gcongr
      exact ford_three_halves_rpow_linear hsigma hsigmaUpper
    _ = 3 / 5 + 1 / (sigma - 1) := by
      have hs : sigma - 1 ≠ 0 := sub_ne_zero.mpr hsigma.ne'
      field_simp [hs]
      ring

end GafniTao
