import Dubon2026.SourceMeromorphicLaurentRealization
import Dubon2026.SourceOriginalJCuspGerm
import Mathlib.Analysis.Analytic.Uniqueness

/-! DUB-17/18 -> original all-weight arithmetic association -> actual
Gamma1 character realization -> differential/cusp comparison -> rational
Fourier structure. Reuse the existing meromorphic cusp-germ representation
to make Laurent coefficient descent apply to actual functions. The analytic
identity principle proves injectivity; no Fourier injectivity is assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology Manifold

theorem mdifferentiable_eq_of_eventuallyEq_atImInfty {f g : ℍ → ℂ}
    (hf : MDiff f) (hg : MDiff g) (he : f =ᶠ[atImInfty] g) : f = g := by
  obtain ⟨Y, _, hY⟩ := atImInfty_basis.eventually_iff.mp he
  let z₀ : ℂ := (max Y 0 + 1) * Complex.I
  have hz : z₀.im = max Y 0 + 1 := by simp [z₀]
  have hz0 : 0 < z₀.im := by rw [hz]; linarith [le_max_right Y 0]
  have hzY : max Y 0 < z₀.im := by rw [hz]; linarith
  have hn : {z : ℂ | max Y 0 < z.im} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzY
  have hlocal : f ∘ ofComplex =ᶠ[𝓝 z₀] g ∘ ofComplex := by
    filter_upwards [hn] with z hz'
    have hp : 0 < z.im := lt_of_le_of_lt (le_max_right Y 0) hz'
    exact hY (by
      simpa only [Set.mem_preimage, Set.mem_Ici, ofComplex_apply_of_im_pos hp] using
        le_trans (le_max_left Y 0) hz'.le)
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have heq := (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd hU
    |>.eqOn_of_preconnected_of_eventuallyEq
      ((UpperHalfPlane.mdifferentiable_iff.mp hg).analyticOnNhd hU)
      (convex_halfSpace_im_gt 0).isPreconnected hz0 hlocal
  funext τ
  simpa only [Function.comp_apply, ofComplex_apply] using heq τ.im_pos

namespace CuspTaylor

theorem represents_qExpansion {h : ℝ} {f : ℍ → ℂ} (hh : 0 < h)
    (hper : Function.Periodic (f ∘ ofComplex) h) (hf : MDiff f)
    (hb : IsBoundedAtImInfty f) :
    Represents (qExpansion h f : LaurentSeries ℂ) (cuspFunction h f) := by
  rw [← series_cuspFunction]
  exact represents_analytic (analyticAt_cuspFunction_zero hh hper hf hb)

theorem Represents.eq_upperHalfPlane {h : ℝ} {A : LaurentSeries ℂ} {f g : ℍ → ℂ}
    (hfA : Represents A (cuspFunction h f)) (hgA : Represents A (cuspFunction h g))
    (hh : 0 < h) (hf : MDiff f) (hg : MDiff g)
    (hfper : Function.Periodic (f ∘ ofComplex) h)
    (hgper : Function.Periodic (g ∘ ofComplex) h) : f = g := by
  apply mdifferentiable_eq_of_eventuallyEq_atImInfty hf hg
  have he := (hfA.unique hgA).comp_tendsto
    ((Function.Periodic.qParam_tendsto hh).comp tendsto_coe_atImInfty)
  filter_upwards [he] with τ hτ
  simpa only [Function.comp_apply, eq_cuspFunction τ hh.ne' hfper, eq_cuspFunction τ hh.ne' hgper] using hτ

theorem represents_cusp_const (h : ℝ) (c : ℂ) :
    Represents (algebraMap ℂ (LaurentSeries ℂ) c) (cuspFunction h (fun _ : ℍ => c)) := by
  apply (represents_const c).congr
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact Function.Periodic.cuspFunction_eq_of_nonzero h _ hq

theorem Represents.cusp_add {h : ℝ} {A B : LaurentSeries ℂ} {f g : ℍ → ℂ}
    (hf : Represents A (cuspFunction h f)) (hg : Represents B (cuspFunction h g)) :
    Represents (A + B) (cuspFunction h (f + g)) := by
  apply (hf.add hg).congr
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
    Function.comp_apply, Pi.add_apply]

theorem Represents.cusp_mul {h : ℝ} {A B : LaurentSeries ℂ} {f g : ℍ → ℂ}
    (hf : Represents A (cuspFunction h f)) (hg : Represents B (cuspFunction h g)) :
    Represents (A * B) (cuspFunction h (f * g)) := by
  apply (hf.mul hg).congr
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
    Function.comp_apply, Pi.mul_apply]

theorem Represents.cusp_inv {h : ℝ} {A : LaurentSeries ℂ} {f : ℍ → ℂ}
    (hf : Represents A (cuspFunction h f)) :
    Represents A⁻¹ (cuspFunction h f⁻¹) := by
  apply hf.inv.congr
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
    Function.comp_apply, Pi.inv_apply]

theorem Represents.cusp_div {h : ℝ} {A B : LaurentSeries ℂ} {f g : ℍ → ℂ}
    (hf : Represents A (cuspFunction h f)) (hg : Represents B (cuspFunction h g)) :
    Represents (A / B) (cuspFunction h (f / g)) := by
  simpa only [div_eq_mul_inv] using hf.cusp_mul hg.cusp_inv

theorem Represents.cusp_pow {h : ℝ} {A : LaurentSeries ℂ} {f : ℍ → ℂ}
    (hf : Represents A (cuspFunction h f)) (n : ℕ) :
    Represents (A ^ n) (cuspFunction h (f ^ n)) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using represents_cusp_const h 1
  | succ n ih => simpa only [pow_succ] using ih.cusp_mul hf

end CuspTaylor
end
end Dubon2026.SourceFunctionField
