import Dubon2026.SourceRealPeriodicity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.NumberTheory.ModularForms.QExpansion

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> period-pair injectivity -> real-part constancy. Actual periodicity,
derived from the finite cusp limit, permits the pinned removable-cusp
theorem. The maximum principle applied to the exponential then handles
a maximum at the cusp without a new strip-integral development.
-/
namespace Dubon2026
noncomputable section
open Complex UpperHalfPlane Filter Set Function
open scoped Topology Manifold

/-- The real part of a holomorphic function attaining its maximum on an
open connected domain is constant there. -/
theorem sourceHolomorphic_re_eq_of_isMaxOn
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hmax : ∀ z ∈ U, (f z).re ≤ (f z₀).re) {z : ℂ} (hz : z ∈ U) :
    (f z).re = (f z₀).re := by
  have hm : IsMaxOn (norm ∘ fun w => Complex.exp (f w)) U z₀ := by
    intro w hw
    simpa only [Function.comp_apply, Complex.norm_exp, Real.exp_le_exp] using hmax w hw
  have he := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hconn hU
    (Complex.differentiable_exp.comp_differentiableOn hf) hz₀ hm hz
  exact Real.exp_injective (by simpa only [Function.comp_apply, Function.const_apply,
    Complex.norm_exp] using he)

/-- The real-periodic upper-half-plane primitive with a finite cusp limit
has the full complex period required by the pinned cusp-function API. -/
theorem sourceUpperHalfPlane_period_of_re_period_of_tendsto
    {φ φ' : ℍ → ℂ} (p : ℝ) (L : ℂ)
    (hφ : ∀ τ : ℍ, HasDerivAt (φ ∘ ofComplex) (φ' τ) (τ : ℂ))
    (hre : ∀ τ : ℍ, (φ (p +ᵥ τ)).re = (φ τ).re)
    (hlim : Tendsto φ atImInfty (𝓝 L)) :
    Function.Periodic (φ ∘ ofComplex) (p : ℂ) := by
  have hp (τ : ℍ) := sourceHolomorphic_period_of_re_period_of_tendsto p L hφ
    (fun τ => by
      have he : ofComplex ((τ : ℂ) + p) = p +ᵥ τ := by
        rw [ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]
        apply UpperHalfPlane.ext
        simp only [coe_vadd, add_comm]
      simpa only [Function.comp_apply, he, ofComplex_apply] using hre τ)
    (by simpa only [Function.comp_def, ofComplex_apply] using hlim) τ
  intro z
  by_cases hz : 0 < z.im
  · exact hp ⟨z, hz⟩
  · exact congrArg φ (ofComplex_apply_eq_of_im_nonpos
      (by simpa using le_of_not_gt hz) (le_of_not_gt hz))

/-- A real-part upper bound attained at the finite cusp limit forces
constancy, using the actual holomorphic cusp function on the unit disk. -/
theorem sourceUpperHalfPlane_re_eq_of_cusp_max
    {φ φ' : ℍ → ℂ} {p : ℝ} (hp : 0 < p) (L : ℂ)
    (hφ : ∀ τ : ℍ, HasDerivAt (φ ∘ ofComplex) (φ' τ) (τ : ℂ))
    (hre : ∀ τ : ℍ, (φ (p +ᵥ τ)).re = (φ τ).re)
    (hlim : Tendsto φ atImInfty (𝓝 L))
    (hmax : ∀ τ : ℍ, (φ τ).re ≤ L.re) (z : ℍ) : (φ z).re = L.re := by
  have hper := sourceUpperHalfPlane_period_of_re_period_of_tendsto p L hφ hre hlim
  have hhol : MDiff φ := UpperHalfPlane.mdifferentiable_iff.mpr
    (fun w hw => (hφ ⟨w, hw⟩).differentiableAt.differentiableWithinAt)
  have hb : IsBoundedAtImInfty φ := hlim.isBigO_one ℝ
  let f := UpperHalfPlane.cuspFunction p φ
  have hd : DifferentiableOn ℂ f (Metric.ball 0 1) :=
    UpperHalfPlane.differentiableOn_cuspFunction_ball hp hper hhol hb
  have hzero : f 0 = L := by
    dsimp only [f]
    rw [UpperHalfPlane.cuspFunction_apply_zero hp
      (UpperHalfPlane.analyticAt_cuspFunction_zero hp hper hhol hb) hper]
    exact hlim.limUnder_eq
  have hm (q : ℂ) (hq : q ∈ Metric.ball 0 1) : (f q).re ≤ (f 0).re := by
    rw [hzero]
    by_cases hq0 : q = 0
    · simp only [hq0, hzero, le_refl]
    · let τ : ℍ := ⟨Function.Periodic.invQParam p q,
        Function.Periodic.im_invQParam_pos_of_norm_lt_one hp
          (mem_ball_zero_iff.mp hq) hq0⟩
      have he := UpperHalfPlane.eq_cuspFunction τ hp.ne' hper
      rw [Function.Periodic.qParam_right_inv hp.ne' hq0] at he
      change (UpperHalfPlane.cuspFunction p φ q).re ≤ L.re
      rw [he]
      exact hmax τ
  have hz : Function.Periodic.qParam p (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    apply mem_ball_zero_iff.mpr
    simpa only [mul_zero, zero_div, Real.exp_zero] using
      (Function.Periodic.norm_qParam_lt_iff hp 0 (z : ℂ)).mpr z.im_pos
  have h := sourceHolomorphic_re_eq_of_isMaxOn Metric.isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected hd (Metric.mem_ball_self zero_lt_one) hm hz
  simpa only [f, UpperHalfPlane.eq_cuspFunction z hp.ne' hper, hzero] using h

end
end Dubon2026
