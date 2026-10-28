import Dubon2026.SourceGammaOneFiniteDivisorReciprocity
import Dubon2026.SourceGammaOnePeterssonIntegralRealPeriods
import Dubon2026.SourceGammaOneMeromorphicPrincipalDivisor

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi principal-divisor converse. Actual finite-divisor reciprocity
and the proved integral Petersson implication force the given unitary
multiplier to be trivial. Existing function-field realization then gives the
literal principal divisor. Constructing the meromorphic function with the
prescribed orders remains an upstream obligation; it is not assumed invariant. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup MeasureTheory Filter Complex Set
open Matrix.SpecialLinearGroup SourceSmoothedUnfolding
open scoped MatrixGroups Topology Real Classical ComplexConjugate GammaOne

theorem multiplier_eq_one_of_original_period_mem (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (c : ℍ →₀ ℤ) (hc : c.sum (fun _ n => n) = 0)
    (F : ℍ → ℂ) (χ : Gamma1 N → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (hχ : ∀ (γ : Gamma1 N) (τ : ℍ), F (γ.val • τ) = χ γ * F τ)
    (hunit : ∀ γ, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (ho : ∀ τ : ℍ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) *
        (Finsupp.mapDomain (analyticPlace hT) c) (analyticPlace hT τ) : ℤ) : WithTop ℤ))
    (hclass : c.sum (fun τ n => n • sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I τ) ∈
      sourceWeightTwoIntegralLattice (Gamma1 N)) :
    ∀ γ : Gamma1 N, χ γ = 1 := by
  obtain ⟨k, hk, Λ, hΛ, hrec⟩ :=
    exists_original_finite_divisor_reciprocity N hT c hc F χ hF hχ hunit hcusp ho
  let C := c.sum (fun τ n => n • sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I τ)
  have hpet : ∃ L ∈ sourceWeightTwoIntegralLattice (Gamma1 N),
      ∀ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2,
        Complex.I * (∫ τ in closedDomain (plusMinus (Gamma1 N)), petersson 2 k g τ) = L g := by
    refine ⟨-(Λ + C), (sourceWeightTwoIntegralLattice (Gamma1 N)).neg_mem
      ((sourceWeightTwoIntegralLattice (Gamma1 N)).add_mem hΛ hclass), fun g => ?_⟩
    simp only [LinearMap.neg_apply, LinearMap.add_apply]
    have he := hrec g
    change Λ g + C g = _ at he
    linear_combination he
  intro γ
  obtain ⟨n, hn⟩ := real_periods_integral_of_petersson_mem_lattice N k hpet γ
  rw [hk γ, hn]
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨n, ?_⟩
  push_cast
  ring

theorem analytic_divisor_isPrincipal_of_unitary_meromorphic_function (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (c : ℍ →₀ ℤ) (hc : c.sum (fun _ n => n) = 0)
    (F : ℍ → ℂ) (χ : Gamma1 N → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (hχ : ∀ (γ : Gamma1 N) (τ : ℍ), F (γ.val • τ) = χ γ * F τ)
    (hunit : ∀ γ, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (ho : ∀ τ : ℍ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) *
        (Finsupp.mapDomain (analyticPlace hT) c) (analyticPlace hT τ) : ℤ) : WithTop ℤ))
    (hclass : c.sum (fun τ n => n • sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I τ) ∈
      sourceWeightTwoIntegralLattice (Gamma1 N)) :
    Divisor.IsPrincipal (Finsupp.mapDomain (analyticPlace hT) c) := by
  have htriv := multiplier_eq_one_of_original_period_mem N hT c hc F χ hF hχ hunit hcusp ho hclass
  apply analytic_divisor_isPrincipal_of_meromorphic_function N hT c F hF ?_ hcusp ho
  intro γ hγ τ
  rw [hχ ⟨γ, hγ⟩ τ, htriv, one_mul]

end
end Dubon2026.SourceFunctionField.GammaOne
