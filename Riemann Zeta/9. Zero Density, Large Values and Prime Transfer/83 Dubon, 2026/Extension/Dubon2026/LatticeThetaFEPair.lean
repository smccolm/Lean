import Dubon2026.LatticeThetaHolomorphic
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-! # The actual lattice theta series as a proved Mellin functional-equation pair -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory Set Filter Asymptotics
open scoped Topology

noncomputable section

/-- Uniform Gaussian domination gives continuity on every positive closed half-line. -/
theorem continuousOn_latticeTheta_Ici (z : ℍ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (latticeTheta z) (Ici a) := by
  apply continuousOn_tsum (fun v => (continuous_latticeThetaTerm z v).continuousOn)
    (summable_latticeThetaTerm z ha)
  intro v t ht
  rw [Real.norm_eq_abs, abs_of_pos (latticeThetaTerm_pos z t v)]
  unfold latticeThetaTerm
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonpos_left ht
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (latticeQuadratic_nonneg z v))
  nlinarith

/-- The actual theta series is continuous at every positive real parameter. -/
theorem continuousOn_latticeTheta (z : ℍ) : ContinuousOn (latticeTheta z) (Ioi 0) := by
  intro t ht
  have ha : 0 < t / 2 := div_pos ht (by norm_num)
  have hh : t / 2 < t := by change 0 < t at ht; linarith
  exact ((continuousOn_latticeTheta_Ici z ha t hh.le).continuousAt (Ici_mem_nhds hh)).continuousWithinAt

/-- The actual theta remainder is bounded by a genuine decaying exponential at infinity. -/
theorem latticeTheta_sub_one_isBigO_exp (z : ℍ) :
    (fun t : ℝ => latticeTheta z t - 1) =O[atTop]
      (fun t : ℝ => Real.exp (-(Real.pi * latticeQuadraticLower z / 2) * t)) := by
  apply IsBigO.of_bound (latticeThetaRemainder z (1 / 2))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [← latticeThetaRemainder_eq z (lt_of_lt_of_le zero_lt_one ht),
    Real.norm_eq_abs, abs_of_nonneg (latticeThetaRemainder_nonneg z t),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact latticeThetaRemainder_decay z ht

/-- The actual theta constant term has rapid decay after subtraction, for every real power. -/
theorem latticeTheta_sub_one_isBigO_rpow (z : ℍ) (r : ℝ) :
    (fun t : ℝ => (latticeTheta z t : ℂ) - 1) =O[atTop] (fun t : ℝ => t ^ r) := by
  have hb : 0 < Real.pi * latticeQuadraticLower z / 2 :=
    div_pos (mul_pos Real.pi_pos (latticeQuadraticLower_pos z)) (by norm_num)
  have h := (latticeTheta_sub_one_isBigO_exp z).trans
    (isLittleO_exp_neg_mul_rpow_atTop hb r).isBigO
  simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
    Complex.isBigO_ofReal_left.mpr h

/-- A genuine self-dual Mellin pair: every field is proved from the actual lattice theta series. -/
def latticeThetaFEPair (z : ℍ) : WeakFEPair ℂ where
  f := fun t => (latticeTheta z t : ℂ)
  g := fun t => (latticeTheta z t : ℂ)
  k := 1
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_latticeTheta z)).locallyIntegrableOn measurableSet_Ioi
  hg_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_latticeTheta z)).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := one_ne_zero
  hf_top := latticeTheta_sub_one_isBigO_rpow z
  hg_top := latticeTheta_sub_one_isBigO_rpow z
  h_feq t ht := by
    have h := latticeTheta_reciprocal z (inv_pos.mpr ht)
    simpa only [inv_inv, one_div, Real.rpow_one, one_mul, smul_eq_mul,
      Complex.ofReal_mul] using congrArg Complex.ofReal h

/-- The constructed actual theta pair is self-dual, including its root number. -/
theorem latticeThetaFEPair_symm (z : ℍ) : (latticeThetaFEPair z).symm = latticeThetaFEPair z := by
  unfold latticeThetaFEPair WeakFEPair.symm
  congr 1
  simp

end
end Dubon2026
