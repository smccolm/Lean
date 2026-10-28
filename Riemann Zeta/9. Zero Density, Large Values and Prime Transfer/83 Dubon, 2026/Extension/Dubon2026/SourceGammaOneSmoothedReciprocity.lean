import Dubon2026.SourceGammaOneDivisorWindingIntegralPeriod
import Dubon2026.SourceSmoothedWindingIntegralSplit

/-! DUB-17/18 -> original arithmetic association -> Gamma1 Picard/H1 ->
Abel-Jacobi converse -> analytic reciprocity. The actual filled quotient and
its winding integral period are combined with the actual smooth-divisor
period limit. Existing almost-everywhere untwist nonvanishing discharges the
exceptional-set input. The exact normalized dbar integral tends to an original
integer period plus the original degree-zero divisor endpoint functional. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup MeasureTheory Filter Complex Set
open Matrix.SpecialLinearGroup SourceSmoothComparison SourcePeriodUntwist
open SourceSmoothedFundamental (smoothedFundamental)
open SourceModularGreenPairing SourceModularSidePairing SourceSmoothedUnfolding
open SourceComplexReciprocity.Dipole
open scoped SourceSmoothedFundamental
open scoped MatrixGroups Topology Real Classical ComplexConjugate GammaOne

theorem exists_original_divisor_smoothed_reciprocity (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (c : ℍ →₀ ℤ) (hc : c.sum (fun _ n => n) = 0)
    (F : ℍ → ℂ) (χ : Gamma1 N → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (hχ : ∀ (γ : Gamma1 N) (τ : ℍ), F (γ.val • τ) = χ γ * F τ)
    (hunit : ∀ γ, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (ho : ∀ τ : ℍ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) *
        (Finsupp.mapDomain (analyticPlace hT) c) (analyticPlace hT τ) : ℤ) : WithTop ℤ)) :
    let D := Finsupp.mapDomain (analyticPlace hT) c
    ∃ k : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2,
      (∀ γ : Gamma1 N, χ γ = Complex.exp (2 * Real.pi * Complex.I *
        ((sourceWeightTwoPeriodValue (Gamma1 N) k γ).re : ℂ))) ∧
    ∃ S : Finset ℍ, (S : Set ℍ) ⊆ c.support ∧
      (∀ s ∈ S, ∀ t ∈ S, (∃ γ : Gamma1 N, γ.val • s = t) → s = t) ∧
      (∀ τ : ℍ, D (analyticPlace hT τ) ≠ 0 →
        ∃ s ∈ S, ∃ γ : Gamma1 N, γ.val • s = τ) ∧
    ∃ Λ ∈ sourceWeightTwoIntegralLattice (Gamma1 N),
      ∀ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2,
        Tendsto (fun T : ℝ => 2 / (π : ℂ) * ∫ z : ℂ,
          g (ofComplex z) * (smoothedFundamental (plusMinus (Gamma1 N)) T z : ℂ) *
            (dbarL (fderiv ℝ (SourcePeriodUntwist.Φ F k) z) / SourcePeriodUntwist.Φ F k z))
          atTop (𝓝 (Λ g + ∑ s ∈ S, (D (analyticPlace hT s) : ℂ) *
            sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I s g)) := by
  classical
  dsimp only
  obtain ⟨k, hk, S, hsub, hinj, hcov, V, hVi, hVl, hVc, hVint, hVlim,
    hqlim, hQcusp, L, m, hmpar, hLcd, hLd, hLexp, hLper, hLlim, Λ, hΛ, hwind⟩ :=
    exists_original_divisor_winding_integral_period N hT c hc F χ hF hχ hunit hcusp ho
  let D := Finsupp.mapDomain (analyticPlace hT) c
  let n : ℍ → ℤ := fun τ => (analyticRamification hT τ : ℤ) * D (analyticPlace hT τ)
  have hΦ : HasLocalModels (SourcePeriodUntwist.Φ F k) n :=
    fun τ => Φ_local F k hF τ (n τ) (ho τ)
  have hne : ∀ᵐ z : ℂ, 0 < z.im → SourcePeriodUntwist.Φ F k z ≠ 0 :=
    (Φ_ae (F := F) (hF := hF) (hfinite := fun τ => ⟨n τ, ho τ⟩) (k := k)).mono
      fun _ hz hi => (hz hi).1
  refine ⟨k, hk, S, hsub, hinj, hcov, Λ, hΛ, fun g => ?_⟩
  have ht := ((hwind g).2).add (hVlim g)
  refine ht.congr fun T => ?_
  exact (smoothed_integral_quotient_split (Gamma1 N) g hΦ hVl hLd hLcd hne
    (plusMinus (Gamma1 N)) T (hVint T g)).symm

end
end Dubon2026.SourceFunctionField.GammaOne
