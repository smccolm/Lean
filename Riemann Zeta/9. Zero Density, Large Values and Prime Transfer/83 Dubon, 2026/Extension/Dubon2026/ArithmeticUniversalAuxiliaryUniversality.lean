import Dubon2026.ArithmeticUniversalAuxiliaryQuotient

/-! The original continuous coefficient maps from the actual universal
auxiliary quotient classify exactly its genuine framed lifts with
prescribed determinant and trivial original auxiliary inertia. This
uses the native universal-ring classification and evaluation, so no
classification certificate or universal lift is supplied. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

variable {ι O A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [Algebra O A] [WithIdeal A] [IsAdicComplete (maximalIdeal A) A]

/-- The actual auxiliary quotient has the exact framed
fixed-determinant universal property with all original auxiliary
inertia equations, on every complete Noetherian local coefficient
ring with the specified residue field. -/
def arithmeticUniversalAuxiliaryFramedFiberEquiv
    (hA : (WithIdeal.i : Ideal A) = maximalIdeal A)
    (eA : ResidueField A ≃ₐ[O] ResidueField O)
    (b : 𝓞 ℚ) (hb : b ≠ 0) (q : ℕ) (hq : q.Prime) (hqb : (q : 𝓞 ℚ) ∣ b)
    [CharP (ResidueField O) q]
    (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup b →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (Q : Finset Nat.Primes)
    (hI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      σ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1) :
    (letI := arithmeticAuxiliaryUniversalRing_isLocal b hb q hq hqb σ hσ δ hδ Q hI
     OriginalContinuousCoefficientFiber
       (arithmeticAuxiliaryUniversalResidueEquiv b hb q hq hqb σ hσ δ hδ Q hI) eA ≃
       {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup b) σ //
         (∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ g)) ∧
         ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
           f.val (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1}) := by
  letI := arithmeticFixedDeterminantRing_isLocal b hb q hq hqb σ hσ δ hδ
  exact arithmeticAuxiliaryQuotientFramedFiberEquiv
    (arithmeticFixedDeterminantResidueEquiv b hb q hq hqb σ hσ δ hδ) eA b Q σ δ
    (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ).toMonoidHom
    (arithmeticFixedDeterminantRepresentation_auxiliary_residue_one b hb q hq hqb σ hσ δ hδ Q hI)
    (arithmeticFixedDeterminantFramedFiberEquiv hA eA b hb q hq hqb σ hσ δ hδ)
    (arithmeticFixedDeterminantFramedFiberEquiv_evaluation hA eA b hb q hq hqb σ hσ δ hδ)

end
end Dubon2026
