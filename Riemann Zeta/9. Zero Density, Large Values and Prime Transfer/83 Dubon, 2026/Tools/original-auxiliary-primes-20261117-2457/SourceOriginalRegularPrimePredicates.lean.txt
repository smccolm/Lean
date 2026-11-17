import Dubon2026.ArithmeticRegularCocycleFrobenius

/-! Exact interfaces for DUB-17/18's original root-detection to regular-prime
assembly. These are propositions about the native groups, cocycles, local
restriction and Frobenius class; the subsequent consumer must prove them. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] rationalArithmeticOriginalFiniteGalois

/-- The precise root-fixing regular non-coboundary input to Chebotarev. -/
def HasArithmeticRegularRootDetection
    (a : 𝓞 ℚ) (p level : ℕ)
    {K ι : Type} [Field K] [TopologicalSpace K] [Fintype ι] [DecidableEq ι]
    (A : Rep.{0} K (rationalArithmeticGaloisGroup a)) [TopologicalSpace A]
    [DiscreteTopology A] [ContinuousSMul K A]
    (ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι K)
    (c : continuousRepresentationCocyclesOne A) : Prop :=
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  ∀ ζ : U, IsPrimitiveRoot ζ (p ^ (level + 1)) →
    ∃ σ : Gal(U/ℚ), σ ζ = ζ ∧ (ρ σ).val.charpoly.Separable ∧
      c.val σ ∉ LinearMap.range (A.ρ σ - 1)

/-- Actual regular detecting primes and their common finite affine factor,
with nonzero localization of the original continuous cohomology class. -/
def HasArithmeticRegularDetectingPrimes
    (a : 𝓞 ℚ) (p level : ℕ)
    {K ι : Type} [Field K] [TopologicalSpace K] [Fintype ι] [DecidableEq ι]
    (A : Rep.{0} K (rationalArithmeticGaloisGroup a))
    [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul K A]
    (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2))
    (ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι K)
    (c : continuousRepresentationCocyclesOne A) : Prop :=
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  ∃ D : FiniteGaloisIntermediateField ℚ U,
    ∃ ψ : Gal(D/ℚ) →* Matrix.GeneralLinearGroup ι K × Equiv.Perm A,
      (∀ w : Gal(U/ℚ), ψ (AlgEquiv.restrictNormalHom D w) =
        (ρ w, cocycleAffinePermutation A c.val w)) ∧
      (letI : NumberField D := NumberField.of_module_finite ℚ D
       ∀ S : Finset ℕ, ∃ q : ℕ, ∃ hq : q.Prime,
         q ∉ S ∧ ¬ (q : 𝓞 ℚ) ∣ a ∧ q ≡ 1 [MOD p ^ (level + 1)] ∧
         Chebotarev.UnramifiedIn ℚ D (Ideal.span {(q : 𝓞 ℚ)}) ∧
         (∃ γ : Gal(rationalPrimeLocalClosure q hq / rationalPrimeLocalField q hq),
           Chebotarev.frobeniusClass ℚ D (Ideal.span {(q : 𝓞 ℚ)}) =
             ConjClasses.mk (AlgEquiv.restrictNormalHom D
               (rationalPrimeArithmeticRestriction a q hq γ)) ∧
           (ρ (rationalPrimeArithmeticRestriction a q hq γ)).val.charpoly.Separable) ∧
         rationalArithmeticH1PrimeRestriction a A hA q hq (Submodule.Quotient.mk c) ≠ 0)

end
end Dubon2026
