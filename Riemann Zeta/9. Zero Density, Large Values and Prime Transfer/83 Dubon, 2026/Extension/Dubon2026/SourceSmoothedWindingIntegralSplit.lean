import Dubon2026.SourceSmoothComparisonDbar
import Dubon2026.SourceSmoothOrbitIntegralGeometry
import Dubon2026.SourceModularSmoothPlaneIntegral
import Dubon2026.SourceMeromorphicUntwistDerivative

/-! DUB-17/18 -> original arithmetic association -> Gamma1 Picard/H1 ->
Abel-Jacobi converse -> reciprocity -> splitting the normalized smooth integral.
Existing compact-support integration and the literal source cutoff discharge
integrability. Almost-everywhere nonvanishing is supplied by the already
proved actual meromorphic untwist, rather than a new exceptional-set argument. -/
namespace Dubon2026.SourceSmoothComparison
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex MeasureTheory Set
open SourceComplexReciprocity SourceComplexReciprocity.Dipole SourceSmoothOrbitIntegral
open SourceSmoothedFundamental
open scoped MatrixGroups Topology Real
variable (Γ : Subgroup SL(2, ℤ))

theorem integrable_smoothed_dbar
    (g : CuspForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2)
    (L : ℂ → ℂ) (hL : ∀ τ : ℍ, ContDiffAt ℝ 1 L τ)
    (Γ' : Subgroup SL(2, ℤ)) [Γ'.FiniteIndex] (T : ℝ) :
    Integrable fun z : ℂ => g (ofComplex z) * (smoothedFundamental Γ' T z : ℂ) *
      dbarL (fderiv ℝ L z) := by
  have hg : ContinuousOn (fun z : ℂ => g (ofComplex z)) upperHalfPlaneSet :=
    fun z hz => ((ModularFormClass.continuous g).continuousAt.comp
      (continuousAt_ofComplex' hz)).continuousWithinAt
  have hfd : ContinuousOn (fderiv ℝ L) upperHalfPlaneSet :=
    fun z hz => ((hL ⟨z, hz⟩).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hd : ContinuousOn (fun z => dbarL (fderiv ℝ L z)) upperHalfPlaneSet :=
    ((hfd.clm_apply continuousOn_const).add
      (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const _
  have hc : Continuous (fun z : ℂ => (smoothedFundamental Γ' T z : ℂ)) :=
    Complex.continuous_ofReal.comp (SourceSmoothedFundamental.contDiff Γ' T 0).continuous
  have hs : HasCompactSupport (fun z : ℂ => (smoothedFundamental Γ' T z : ℂ)) :=
    (SourceSmoothedFundamental.hasCompactSupport Γ' T).comp_left Complex.ofReal_zero
  have hu : tsupport (fun z : ℂ => (smoothedFundamental Γ' T z : ℂ)) ⊆ upperHalfPlaneSet :=
    (tsupport_comp_subset (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero _).trans
      (SourceSmoothedFundamental.tsupport_subset Γ' T)
  simpa only [mul_right_comm _ _ (dbarL _)] using
    integrable_mul_of_tsupport_subset isOpen_upperHalfPlaneSet (hg.mul hd) hc hs hu

theorem smoothed_integral_quotient_split
    (g : CuspForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2)
    {Φ V L : ℂ → ℂ} {n : ℍ → ℤ}
    (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n)
    (hLd : ∀ τ : ℍ, HasFDerivAt L ((quot Φ V τ)⁻¹ • fderiv ℝ (quot Φ V) τ) τ)
    (hL : ∀ τ : ℍ, ContDiffAt ℝ 1 L τ)
    (hne : ∀ᵐ z : ℂ, 0 < z.im → Φ z ≠ 0)
    (Γ' : Subgroup SL(2, ℤ)) [Γ'.FiniteIndex] (T : ℝ)
    (hVi : Integrable fun z : ℂ => g (ofComplex z) * (smoothedFundamental Γ' T z : ℂ) *
      (dbarL (fderiv ℝ V z) / V z)) :
    2 / (π : ℂ) * (∫ z : ℂ, g (ofComplex z) * (smoothedFundamental Γ' T z : ℂ) *
        (dbarL (fderiv ℝ Φ z) / Φ z)) =
      2 / (π : ℂ) * (∫ z : ℂ, g (ofComplex z) * (smoothedFundamental Γ' T z : ℂ) *
        dbarL (fderiv ℝ L z)) +
      2 / (π : ℂ) * (∫ z : ℂ, g (ofComplex z) * (smoothedFundamental Γ' T z : ℂ) *
        (dbarL (fderiv ℝ V z) / V z)) := by
  have he := weighted_dbar_quotient_split_ae hΦ hV hLd hne
    (fun z => g (ofComplex z)) (fun z => (smoothedFundamental Γ' T z : ℂ))
    (fun z hz => by dsimp only; rw [SourceSmoothedUnfolding.smooth_eq_zero_of_im_nonpos Γ' hz]; rfl)
  rw [integral_congr_ae he, integral_add (integrable_smoothed_dbar Γ g L hL Γ' T) hVi, mul_add]

end
end Dubon2026.SourceSmoothComparison
