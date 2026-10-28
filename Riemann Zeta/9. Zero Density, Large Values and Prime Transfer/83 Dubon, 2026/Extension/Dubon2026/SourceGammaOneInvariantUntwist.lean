import Dubon2026.SourceMeromorphicUntwistDerivative
import Dubon2026.SourceGammaOneMeromorphicMultiplierPeriods

/-! DUB-17/18 -> original all-weight arithmetic association -> original
Gamma1 homogeneous-coefficient Hecke characters -> Picard/H1 -> Abel-Jacobi
converse -> analytic reciprocity. The same actual meromorphic function and
literal ramification-weighted original divisor yield an invariant untwist,
nonzero translated cusp limits, derivative decay and the exact almost-
everywhere logarithmic derivative formula. Cusp-form period realization is
derived from the actual multiplier; it is not a supplied hypothesis. -/
namespace Dubon2026
noncomputable section
open UpperHalfPlane Filter MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup
open SourceCurve SourceFunctionField SourceFunctionField.GammaOne SourcePeriodUntwist
open scoped MatrixGroups Topology

theorem sourceMeromorphic_exists_invariant_untwist
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (F : ℍ → ℂ) (k : CuspForm (Γ.map (mapGL ℝ)) 2) (n : ℍ → ℤ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (ho : ∀ τ : ℍ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) = (n τ : WithTop ℤ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F (γ.val • τ) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((sourceWeightTwoPeriodValue Γ k γ).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ H : ℂ → ℂ,
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        H =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z) ∧
      (∀ (γ : Γ) (τ : ℍ), H ((γ.val • τ : ℍ) : ℂ) = H τ) ∧
      (∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
        Tendsto (fun τ : ℍ => H ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c)) ∧
      (∀ σ : SL(2, ℤ), Tendsto (fun τ : ℍ =>
        fderiv ℝ (fun u : ℂ => H ((σ • ofComplex u : ℍ) : ℂ)) (τ : ℂ))
          atImInfty (𝓝 0)) ∧
      (∀ᵐ z : ℂ, 0 < z.im → H z ≠ 0 ∧ DifferentiableAt ℝ H z ∧
        fderiv ℝ H z 1 = H z *
          (deriv (F ∘ ofComplex) z / F (ofComplex z) -
            2 * Real.pi * Complex.I * ((k (ofComplex z)).re : ℂ)) ∧
        fderiv ℝ H z Complex.I = H z *
          (Complex.I * (deriv (F ∘ ofComplex) z / F (ofComplex z)) +
            2 * Real.pi * Complex.I * ((k (ofComplex z)).im : ℂ))) := by
  refine ⟨Φ F k, fun τ => Φ_local F k hF τ (n τ) (ho τ), Φ_smul F k hF hχ, ?_, ?_, ?_⟩
  · intro σ
    obtain ⟨L, hL0, hL⟩ := hcusp σ
    exact Φ_cusp F k hF σ hL0 hL
  · intro σ
    obtain ⟨L, hL0, hL⟩ := hcusp σ
    exact Φ_decay F k hF σ hL0 hL
  · exact Φ_ae (F := F) (hF := hF) (hfinite := fun τ => ⟨n τ, ho τ⟩) (k := k)

theorem sourceGamma1_meromorphic_invariant_untwist (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N)
    (D : Divisor ℂ (functionFieldOver (Gamma1 N) ℂ))
    (F : ℍ → ℂ) (χ : Gamma1 N → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (hχ : ∀ (γ : Gamma1 N) (τ : ℍ), F (γ.val • τ) = χ γ * F τ)
    (hunit : ∀ γ, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (ho : ∀ τ : ℍ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) * D (analyticPlace hT τ) : ℤ) : WithTop ℤ)) :
    ∃ k : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2,
      (∀ γ : Gamma1 N, χ γ =
        Complex.exp (2 * Real.pi * Complex.I *
          ((sourceWeightTwoPeriodValue (Gamma1 N) k γ).re : ℂ))) ∧
      ∃ H : ℂ → ℂ,
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        H =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ ((analyticRamification hT τ : ℤ) * D (analyticPlace hT τ)) * Ψ z) ∧
      (∀ (γ : Gamma1 N) (τ : ℍ), H ((γ.val • τ : ℍ) : ℂ) = H τ) ∧
      (∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
        Tendsto (fun τ : ℍ => H ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c)) ∧
      (∀ σ : SL(2, ℤ), Tendsto (fun τ : ℍ =>
        fderiv ℝ (fun u : ℂ => H ((σ • ofComplex u : ℍ) : ℂ)) (τ : ℂ))
          atImInfty (𝓝 0)) ∧
      (∀ᵐ z : ℂ, 0 < z.im → H z ≠ 0 ∧ DifferentiableAt ℝ H z ∧
        fderiv ℝ H z 1 = H z *
          (deriv (F ∘ ofComplex) z / F (ofComplex z) -
            2 * Real.pi * Complex.I * ((k (ofComplex z)).re : ℂ)) ∧
        fderiv ℝ H z Complex.I = H z *
          (Complex.I * (deriv (F ∘ ofComplex) z / F (ofComplex z)) +
            2 * Real.pi * Complex.I * ((k (ofComplex z)).im : ℂ))) := by
  obtain ⟨k, hk⟩ := sourceGamma1_meromorphic_multiplier_eq_exp_real_period
    N hT D F χ hF hχ hunit hcusp ho
  refine ⟨k, hk, sourceMeromorphic_exists_invariant_untwist F k
    (fun τ => (analyticRamification hT τ : ℤ) * D (analyticPlace hT τ)) hF ho ?_ hcusp⟩
  intro γ τ
  rw [hχ, hk]

end
end Dubon2026
