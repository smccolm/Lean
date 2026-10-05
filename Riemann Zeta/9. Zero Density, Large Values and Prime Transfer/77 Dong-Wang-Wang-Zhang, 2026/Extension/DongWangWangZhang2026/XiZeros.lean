import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Actual xi zeros with multiplicity

The installed genus-one factorization uses the genuine entire xi divisor.
This module proves its critical-strip and reflection interfaces; no zero
enumeration or symmetry of multiplicities is supplied as a hypothesis.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Complex.Hadamard Set Filter
open scoped Topology

/-- The installed entire xi function is nonzero on the closed right half-plane. -/
theorem xi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    riemannXi s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    norm_num [riemannXi]
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  have hz := riemannZeta_ne_zero_of_one_le_re hs
  have hc : completedRiemannZeta s ≠ 0 := by
    rw [riemannZeta_def_of_ne_zero hs0] at hz
    exact (div_ne_zero_iff.mp hz).1
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hc)
    (by norm_num)

/-- Every zero of the entire xi function lies strictly inside the critical strip. -/
theorem xi_zero_re_mem_Ioo {s : ℂ} (hs : riemannXi s = 0) :
    s.re ∈ Ioo (0 : ℝ) 1 := by
  have hu : s.re < 1 := lt_of_not_ge (fun h => xi_ne_zero_of_one_le_re h hs)
  refine ⟨?_, hu⟩
  by_contra h
  have hr : 1 ≤ (1 - s).re := by simp only [sub_re, one_re]; linarith
  exact xi_ne_zero_of_one_le_re hr ((riemannXi_one_sub s).trans hs)

/-- Xi's exact zeta factorization throughout the positive half-plane, away from the pole. -/
theorem xi_eq_factor_mul_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = (s * (s - 1) * Gammaℝ s / 2) * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hs
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    riemannZeta_def_of_ne_zero hs0]
  field_simp [Gammaℝ_ne_zero_of_re_pos hs]

/-- The gamma and rational factor is an analytic unit at each positive nonpole point. -/
theorem analyticAt_xi_zeta_factor {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => z * (z - 1) * Gammaℝ z / 2) s ∧
      s * (s - 1) * Gammaℝ s / 2 ≠ 0 := by
  have hg : AnalyticAt ℂ Gammaℝ s := by
    have h := (differentiable_Gammaℝ_inv.analyticAt s).inv
      (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))
    have he : (fun z : ℂ => (Gammaℝ z)⁻¹)⁻¹ = Gammaℝ := by
      funext z
      exact inv_inv _
    rwa [he] at h
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hs
  constructor
  · exact ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hg).div_const
  · exact div_ne_zero
      (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (Gammaℝ_ne_zero_of_re_pos hs))
      (by norm_num)

/-- The genuine zeta and xi analytic orders agree; the gamma/pole factor loses no multiplicity. -/
theorem xi_analyticOrder_eq_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt riemannXi s = analyticOrderAt riemannZeta s := by
  have he : riemannXi =ᶠ[𝓝 s]
      ((fun z : ℂ => z * (z - 1) * Gammaℝ z / 2) * riemannZeta) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs,
      isOpen_ne.mem_nhds hs1] with z hz hz1
    exact xi_eq_factor_mul_zeta hz hz1
  rw [analyticOrderAt_congr he]
  have hz : AnalyticAt ℂ riemannZeta s :=
    (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) s hs1
  have hf := analyticAt_xi_zeta_factor hs hs1
  rw [analyticOrderAt_mul hf.1 hz, hf.1.analyticOrderAt_eq_zero.mpr hf.2, zero_add]

/-- On the positive half-plane away from one, xi and zeta have the same zeros. -/
theorem xi_eq_zero_iff_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  rw [xi_eq_factor_mul_zeta hs hs1, mul_eq_zero]
  simp only [(analyticAt_xi_zeta_factor hs hs1).2, false_or]

/-- The entire fiber, not just a chosen label, has the exact zeta multiplicity. -/
theorem xi_zero_fiber_card {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (divisorZeroIndex₀_fiberFinset (f := riemannXi) s).card =
      analyticOrderNatAt riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hs
  rw [divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    differentiable_riemannXi hs0]
  simp only [analyticOrderNatAt, xi_analyticOrder_eq_zeta hs hs1]

/-- Xi's divisor, counted with analytic multiplicity and with the origin excluded. -/
abbrev XiZero := divisorZeroIndex₀ riemannXi (univ : Set ℂ)

/-- The actual complex point carried by a multiplicity index. -/
abbrev xiZeroPoint (p : XiZero) : ℂ := divisorZeroIndex₀_val p

/-- A divisor index really is a zero of xi, not an arbitrary complex parameter. -/
theorem xiZeroPoint_zero (p : XiZero) : riemannXi (xiZeroPoint p) = 0 := by
  have hd := divisorZeroIndex₀_val_mem_divisor_support p
  rw [divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi] at hd
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (by simpa using hd)

/-- The critical-strip bounds hold for every multiplicity index. -/
theorem xiZeroPoint_re (p : XiZero) : 0 < (xiZeroPoint p).re ∧ (xiZeroPoint p).re < 1 :=
  xi_zero_re_mem_Ioo (xiZeroPoint_zero p)

/-- Every indexed xi zero is an actual nontrivial zeta zero. -/
theorem xiZeroPoint_zeta_zero (p : XiZero) : riemannZeta (xiZeroPoint p) = 0 := by
  have hs1 : xiZeroPoint p ≠ 1 := by
    intro h
    have hr := (xiZeroPoint_re p).2
    simp [h] at hr
  have h := xiZeroPoint_zero p
  rw [xi_eq_factor_mul_zeta (xiZeroPoint_re p).1 hs1] at h
  exact (mul_eq_zero.mp h).resolve_left
    (analyticAt_xi_zeta_factor (xiZeroPoint_re p).1 hs1).2

/-- The index multiplicity equals zeta's analytic vanishing order. -/
theorem xiZeroPoint_multiplicity (p : XiZero) :
    MeromorphicOn.divisor riemannXi univ (xiZeroPoint p) =
      (analyticOrderNatAt riemannZeta (xiZeroPoint p) : ℤ) := by
  have hs1 : xiZeroPoint p ≠ 1 := by
    intro h
    have hr := (xiZeroPoint_re p).2
    simp [h] at hr
  rw [divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi]
  simp only [analyticOrderNatAt, xi_analyticOrder_eq_zeta (xiZeroPoint_re p).1 hs1]

/-- Xi's analytic order is unchanged by its functional-equation reflection. -/
theorem xi_analyticOrder_reflect (s : ℂ) :
    analyticOrderAt riemannXi (1 - s) = analyticOrderAt riemannXi s := by
  have ha : AnalyticAt ℂ (fun z : ℂ => 1 - z) s := by fun_prop
  have hd : deriv (fun z : ℂ => 1 - z) s ≠ 0 := by simp
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannXi) ha hd
  have he : riemannXi ∘ (fun z : ℂ => 1 - z) = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  rw [he] at h
  exact h.symm

/-- The reflection preserves the integer divisor multiplicity exactly. -/
theorem xi_divisor_reflect (s : ℂ) :
    MeromorphicOn.divisor riemannXi univ (1 - s) =
      MeromorphicOn.divisor riemannXi univ s := by
  simp only [divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi,
    analyticOrderNatAt, xi_analyticOrder_reflect]

/-- Multiplicity-preserving reflection on the actual zero index. -/
def xiZeroReflect (p : XiZero) : XiZero :=
  ⟨⟨1 - xiZeroPoint p, ⟨p.1.2.val, by
      simpa only [xi_divisor_reflect] using p.1.2.isLt⟩⟩, by
    intro h
    have hr := congrArg Complex.re h
    simp only [sub_re, one_re, zero_re] at hr
    linarith [(xiZeroPoint_re p).2]⟩

/-- Reflection acts on the point, not only on an unweighted set of zeros. -/
theorem xiZeroPoint_reflect (p : XiZero) :
    xiZeroPoint (xiZeroReflect p) = 1 - xiZeroPoint p := rfl

/-- Reflecting twice fixes every multiplicity label. -/
theorem xiZeroReflect_involutive : Function.Involutive xiZeroReflect := by
  intro p
  apply Subtype.ext
  apply Sigma.ext
  · change 1 - (1 - xiZeroPoint p) = xiZeroPoint p
    ring
  · refine (Fin.heq_ext_iff
      (i := (xiZeroReflect (xiZeroReflect p)).1.2) (j := p.1.2) ?_).2 ?_
    · change (MeromorphicOn.divisor riemannXi univ (1 - (1 - xiZeroPoint p))).toNat =
        (MeromorphicOn.divisor riemannXi univ (xiZeroPoint p)).toNat
      rw [sub_sub_cancel]
    · rfl

/-- An equivalence usable for absolutely convergent zero sums. -/
def xiZeroReflectEquiv : XiZero ≃ XiZero :=
  Function.Involutive.toPerm xiZeroReflect xiZeroReflect_involutive

/-- The actual genus-one zero divisor has inverse-square summability. -/
theorem summable_xiZero_norm_inv_sq :
    Summable (fun p : XiZero => ‖xiZeroPoint p‖⁻¹ ^ (2 : ℕ)) :=
  summable_riemannXi_divisorZeroIndex₀_norm_inv_sq

/-- Bounded sets contain only finitely many zero indices, including multiplicity. -/
theorem finite_xiZero_norm_le (R : ℝ) :
    {p : XiZero | ‖xiZeroPoint p‖ ≤ R}.Finite :=
  divisorZeroIndex₀_norm_le_finite R (subset_univ _)

end
end DongWangWangZhang2026
