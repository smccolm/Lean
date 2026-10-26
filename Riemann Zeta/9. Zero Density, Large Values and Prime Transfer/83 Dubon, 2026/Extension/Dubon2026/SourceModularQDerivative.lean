import Dubon2026.SourceModularDerivativeCuspBounds
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! DUB-17/18 -> arithmetic Gamma1 realization -> Picard/H1 comparison ->
regular differential/cusp comparison -> finite-coordinate modular integral bound.
The literal analytic normalized derivative must match the existing q-Euler
derivation. Reuse native analytic power-series differentiation and the local
bounded-derivative theorem; no new norm-polynomial or Ramanujan system.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_coe_qExpansion_normalizedDerivOfComplex.lean. -/
namespace Dubon2026.SourceFunctionField.ModularQDerivative
noncomputable section
open UpperHalfPlane Complex Function
open scoped Real Manifold

theorem norm_qParam_one_lt_one (τ : ℍ) : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := by
  have h1 : 0 < 2 * Real.pi * τ.im / 1 := by positivity
  simpa [Function.Periodic.qParam, Complex.norm_exp, neg_div] using h1

theorem hasDerivAt_qParam_one (z : ℂ) :
    HasDerivAt (fun w : ℂ => Function.Periodic.qParam 1 w)
      (2 * Real.pi * Complex.I * Function.Periodic.qParam 1 z) z := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  have h0 : HasDerivAt (fun w : ℂ => 2 * (Real.pi : ℂ) * Complex.I * w)
      (2 * (Real.pi : ℂ) * Complex.I) z := by
    simpa using (hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I)
  simpa [mul_comm] using h0.cexp

theorem normalizedDerivOfComplex_eq_qParam_mul_deriv
    (F : ℍ → ℂ) (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) (τ : ℍ) :
    Derivative.normalizedDerivOfComplex F τ =
      Function.Periodic.qParam 1 (τ : ℂ) *
        deriv (UpperHalfPlane.cuspFunction 1 F) (Function.Periodic.qParam 1 (τ : ℂ)) := by
  have hper' : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) ((1 : ℝ) : ℂ) := by
    rwa [Complex.ofReal_one]
  have hmem : (τ : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := τ.2
  have heq : (F ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (τ : ℂ)]
      (fun z => UpperHalfPlane.cuspFunction 1 F (Function.Periodic.qParam 1 z)) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hmem] with z hz
    have h2 := UpperHalfPlane.eq_cuspFunction (f := F) (⟨z, hz⟩ : ℍ) one_ne_zero hper'
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    exact h2.symm
  have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := norm_qParam_one_lt_one τ
  have hg : DifferentiableAt ℂ (UpperHalfPlane.cuspFunction 1 F)
      (Function.Periodic.qParam 1 (τ : ℂ)) :=
    UpperHalfPlane.differentiableAt_cuspFunction one_pos hper' hhol hbdd hq
  have hcomp : HasDerivAt (fun z => UpperHalfPlane.cuspFunction 1 F (Function.Periodic.qParam 1 z))
      (deriv (UpperHalfPlane.cuspFunction 1 F) (Function.Periodic.qParam 1 (τ : ℂ)) *
        (2 * Real.pi * Complex.I * Function.Periodic.qParam 1 (τ : ℂ))) (τ : ℂ) :=
    hg.hasDerivAt.comp (τ : ℂ) (hasDerivAt_qParam_one (τ : ℂ))
  show (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * deriv (F ∘ UpperHalfPlane.ofComplex) (τ : ℂ) = _
  rw [Filter.EventuallyEq.deriv_eq heq, hcomp.deriv]
  have h2πI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  field_simp

theorem periodic_normalizedDerivOfComplex
    (F : ℍ → ℂ) (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1) :
    Function.Periodic (Derivative.normalizedDerivOfComplex F ∘ UpperHalfPlane.ofComplex) 1 := by
  intro w
  by_cases! hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    have hderiv : deriv (F ∘ UpperHalfPlane.ofComplex) (w + 1) =
        deriv (F ∘ UpperHalfPlane.ofComplex) w := by
      conv_rhs => rw [show (F ∘ UpperHalfPlane.ofComplex) =
        fun z => (F ∘ UpperHalfPlane.ofComplex) (z + 1) from funext fun z => (hper z).symm]
      rw [deriv_comp_add_const]
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw1,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw, Derivative.normalizedDerivOfComplex]
    rw [hderiv]
  · have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_nonpos hw1,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw]

end
end Dubon2026.SourceFunctionField.ModularQDerivative
