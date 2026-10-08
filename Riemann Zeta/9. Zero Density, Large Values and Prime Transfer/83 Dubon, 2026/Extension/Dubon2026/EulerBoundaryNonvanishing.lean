import Mathlib.NumberTheory.LSeries.Nonvanishing
import Dubon2026.RankinConvolutionGlobal

/-! # Boundary nonvanishing from the three-four-one Euler inequality

The analytic argument follows the pinned Mathlib Dirichlet nonvanishing proof,
generalized to a displayed genuine meromorphic function and a separately proved
Euler-product inequality. The inequality is not assumed for a cusp form here.
-/

namespace Dubon2026

open Filter Asymptotics
open scoped Topology

noncomputable section

/-- Holomorphy at a specified boundary point gives a bounded horizontal approach. -/
theorem boundary_horizontal_isBigO_one {F : ℂ → ℂ} {y : ℝ}
    (hF : DifferentiableAt ℂ F (1 + Complex.I * y)) :
    (fun x : ℝ => F (1 + x + Complex.I * y)) =O[𝓝[>] 0] fun _ => (1 : ℂ) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have hc := hF.continuousAt
  rw [← zero_add (1 + _)] at hc
  exact (hc.comp (f := fun x : ℝ => x + (1 + Complex.I * y)) (x := 0)
    (by fun_prop)).tendsto.isBigO_one ℂ

/-- A genuine holomorphic zero has at least linear decay along the horizontal approach. -/
theorem boundary_horizontal_isBigO_of_zero {F : ℂ → ℂ} {y : ℝ}
    (hF : DifferentiableAt ℂ F (1 + Complex.I * y)) (hz : F (1 + Complex.I * y) = 0) :
    (fun x : ℝ => F (1 + x + Complex.I * y)) =O[𝓝[>] 0] fun x : ℝ => (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have hd := hF.hasDerivAt
  rw [← zero_add (1 + _)] at hd
  simpa only [zero_add, hz, sub_zero] using
    (Complex.isBigO_comp_ofReal_nhds
      (hd.comp_add_const 0 _).differentiableAt.isBigO_sub).mono nhdsWithin_le_nhds

/-- A simple-pole bound and the genuine three-four-one Euler inequality exclude a holomorphic zero on the boundary. -/
theorem boundary_ne_zero_of_three_four_one {F : ℂ → ℂ} {y : ℝ}
    (h0 : (fun x : ℝ => F (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x)
    (h1 : DifferentiableAt ℂ F (1 + Complex.I * y))
    (h2 : DifferentiableAt ℂ F (1 + Complex.I * (2 * y)))
    (hEuler : ∀ x : ℝ, 0 < x →
      1 ≤ ‖F (1 + x) ^ 3 * F (1 + x + Complex.I * y) ^ 4 *
        F (1 + x + 2 * Complex.I * y)‖) :
    F (1 + Complex.I * y) ≠ 0 := by
  intro hz
  have hcancel (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hx)), one_mul, mul_one]
  have hlower : (fun _ : ℝ => (1 : ℝ)) =O[𝓝[>] 0]
      fun x => F (1 + x) ^ 3 * F (1 + x + Complex.I * y) ^ 4 *
        F (1 + x + 2 * Complex.I * y) :=
    IsBigO.of_bound' (eventually_nhdsWithin_of_forall
      (fun x hx => (norm_one (α := ℝ)).symm ▸ hEuler x hx))
  have hupper := ((h0.pow 3).mul ((boundary_horizontal_isBigO_of_zero h1 hz).pow 4)).mul
    (boundary_horizontal_isBigO_one (y := 2 * y)
      (by simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using h2))
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, mul_left_comm Complex.I,
    ← mul_assoc, hcancel] at hupper
  have hh := (hlower.trans hupper).norm_right
  simp only [Complex.norm_real] at hh
  exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero))
    (hh.of_norm_right.trans_isLittleO (isLittleO_id_one.mono nhdsWithin_le_nhds))

/-- The actual entire Rankin numerator supplies the simple-pole horizontal bound required by the Euler argument. -/
theorem rankinConvolutionGlobal_isBigO_near_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    (fun x : ℝ => rankinConvolutionGlobalContinuation f (1 + x)) =O[𝓝[>] 0]
      fun x => (1 : ℂ) / x := by
  have hc : ContinuousAt (fun x : ℝ => rankinConvolutionEntireNumerator f (1 + x)) 0 :=
    ((differentiable_rankinConvolutionEntireNumerator f).continuous.continuousAt).comp (by fun_prop)
  have hb := (hc.tendsto.isBigO_one ℂ).mono (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have ht := hb.mul (isBigO_refl (fun x : ℝ => ((x : ℂ)⁻¹)) (𝓝[>] 0))
  simpa only [rankinConvolutionGlobalContinuation, add_sub_cancel_left,
    div_eq_mul_inv, one_mul] using ht

end
end Dubon2026
