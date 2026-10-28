import Dubon2026.SourceGammaOnePeterssonReciprocity
import Dubon2026.SourceGammaOneRepresentativePeriodCorrection

/-! DUB17/18 -> actual Gamma1 Picard/H1 comparison -> forward Abel-Jacobi
implication. Reuse the actual smooth comparison, winding logarithm, Green
boundary and integer-period proofs with the zero untwisting cusp form.
An invariant meromorphic function with the actual finite divisor has an
original integral period class. No new analytic foundations are needed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup MeasureTheory Filter Complex Set
open Matrix.SpecialLinearGroup SourceSmoothComparison SourcePeriodUntwist
open SourceSmoothedFundamental (smoothedFundamental)
open SourceModularGreenPairing SourceModularSidePairing SourceSmoothedUnfolding
open SourceComplexReciprocity.Dipole
open scoped SourceSmoothedFundamental
open scoped MatrixGroups Topology Real Classical ComplexConjugate GammaOne

theorem period_mem_of_invariant_meromorphic_function (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (c : ℍ →₀ ℤ) (hc : c.sum (fun _ n => n) = 0)
    (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (hInv : ∀ (γ : Gamma1 N) (τ : ℍ), F (γ.val • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (ho : ∀ τ : ℍ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) *
        (Finsupp.mapDomain (analyticPlace hT) c) (analyticPlace hT τ) : ℤ) : WithTop ℤ)) :
    c.sum (fun τ n => n • sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I τ) ∈
      sourceWeightTwoIntegralLattice (Gamma1 N) := by
  classical
  let D := Finsupp.mapDomain (analyticPlace hT) c
  let n : ℍ → ℤ := fun τ => (analyticRamification hT τ : ℤ) * D (analyticPlace hT τ)
  let k : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2 := 0
  have hperiod : ∀ (γ : Gamma1 N) (τ : ℍ), F (γ.val • τ) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((sourceWeightTwoPeriodValue (Gamma1 N) k γ).re : ℂ)) * F τ := by
    intro γ τ
    simpa [k] using hInv γ τ
  have hΦ : HasLocalModels (SourcePeriodUntwist.Φ F k) n :=
    fun τ => Φ_local F k hF τ (n τ) (ho τ)
  have hΦinv : ∀ γ ∈ plusMinus (Gamma1 N), ∀ τ : ℍ,
      SourcePeriodUntwist.Φ F k ((γ • τ : ℍ) : ℂ) = SourcePeriodUntwist.Φ F k τ := by
    intro γ hγ τ
    obtain ⟨δ, hδ⟩ := exists_gamma_smul_eq_of_mem_plusMinus (Gamma1 N) hγ τ
    rw [← hδ]
    exact Φ_smul F k hF hperiod δ τ
  have hΦcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => SourcePeriodUntwist.Φ F k ((σ • τ : ℍ) : ℂ))
        atImInfty (𝓝 L) := by
    intro σ
    obtain ⟨L, hL, hlim⟩ := hcusp σ
    exact Φ_cusp F k hF σ hL hlim
  have hΦdecay : ∀ σ : SL(2, ℤ), Tendsto
      (fun τ : ℍ => fderiv ℝ (fun u : ℂ =>
        SourcePeriodUntwist.Φ F k (SourceSmoothDivisor.sm σ u)) (τ : ℂ))
      atImInfty (𝓝 0) := by
    intro σ
    obtain ⟨L, hL, hlim⟩ := hcusp σ
    exact Φ_decay F k hF σ hL hlim
  obtain ⟨S, hsub, hinj, hcov, V, hVi, hVl, hVc, hVint, hVlim⟩ :=
    exists_original_divisor_smooth_period_limit N hT c hc
  have hcov' : ∀ τ : ℍ, n τ ≠ 0 →
      ∃ s ∈ S, ∃ γ : plusMinus (Gamma1 N), γ.val • s = τ := by
    intro τ hτ
    obtain ⟨s, hs, γ, hγ⟩ := hcov τ (fun he => hτ (by simp [n, D, he]))
    exact ⟨s, hs, ⟨γ.val, le_plusMinus (Gamma1 N) γ.property⟩, hγ⟩
  obtain ⟨hqlim, hQcusp, L, m, hmpar, hLcd, hLd, hLexp, hLper, hLlim⟩ :=
    exists_filled_winding_log (plusMinus (Gamma1 N)) S n hcov' hΦ hVl
      hΦinv (fun γ hγ τ => hVi ⟨γ, hγ⟩ τ) hVc hΦcusp hΦdecay
  have hQ : ∀ τ : ℍ, DifferentiableAt ℝ (quot (SourcePeriodUntwist.Φ F k) V) (τ : ℂ) :=
    fun τ => (contDiffAt_quot hΦ hVl τ).differentiableAt (by norm_num)
  obtain ⟨Λs, hΛs, he⟩ := SourceParabolicEdgePeriod.exists_integral_period_eq_winding_edges
    (plusMinus (Gamma1 N)) (neg_one_mem_plusMinus (Gamma1 N)) m hmpar
  let Λ := Λs.comp (SignedForms.extend (Gamma1 N))
  have hΛ : Λ ∈ sourceWeightTwoIntegralLattice (Gamma1 N) :=
    SignedForms.integralLattice_comp_extend (Gamma1 N) Λs hΛs
  let C := c.sum (fun τ a => a • sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I τ)
  let R := ∑ s ∈ S, D (analyticPlace hT s) • sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I s
  have hne : ∀ᵐ z : ℂ, 0 < z.im → SourcePeriodUntwist.Φ F k z ≠ 0 :=
    (Φ_ae (F := F) (hF := hF) (hfinite := fun τ => ⟨n τ, ho τ⟩) (k := k)).mono
      fun _ hz hi => (hz hi).1
  have hzero (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) : Λ g + R g = 0 := by
    have hw := (winding_boundary_limit (plusMinus (Gamma1 N)) (neg_one_mem_plusMinus (Gamma1 N))
      L (quot (SourcePeriodUntwist.Φ F k) V) m hQ hLcd hLd hLper hLlim hQcusp
      (SignedForms.extend (Gamma1 N) g)).2
    rw [he (SignedForms.extend (Gamma1 N) g)] at hw
    have ht := (hw.add (hVlim g)).congr fun T =>
      (smoothed_integral_quotient_split (Gamma1 N) g hΦ hVl hLd hLcd hne
        (plusMinus (Gamma1 N)) T (hVint T g)).symm
    have hr := tendsto_nhds_unique ht (tendsto_Φ_smoothed_petersson N F k g hF
      (fun τ => ⟨n τ, ho τ⟩))
    simpa only [Λ, R, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      zsmul_eq_mul, k, petersson, CuspForm.coe_zero, Pi.zero_apply, map_zero,
      mul_zero, zero_mul, integral_zero] using hr
  have hR : R = -Λ := by
    ext g
    simp only [LinearMap.neg_apply]
    exact eq_neg_of_add_eq_zero_right (hzero g)
  have hcor : C - R ∈ sourceWeightTwoIntegralLattice (Gamma1 N) :=
    representative_period_difference_mem N hT c S hinj hcov
  have hm := add_mem hcor (hR ▸ neg_mem hΛ)
  simpa only [sub_add_cancel] using hm

end
end Dubon2026.SourceFunctionField.GammaOne
