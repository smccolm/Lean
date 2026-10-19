import Dubon2026.ArithmeticUniversalAuxiliaryUniversality
import Dubon2026.ArithmeticUniversalAuxiliaryRepresentation

/-! The actual auxiliary quotient classification evaluates the same
universal matrices through the original coefficient map. This concrete
identity is the compatibility needed to prove inverse coefficient maps
in the original-support ring comparison. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

/-- Classifying an original coefficient map evaluates the actual
universal auxiliary representation, on every original group element. -/
theorem arithmeticUniversalAuxiliaryFramedFiberEquiv_evaluation
    {ι O A : Type} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra O A] [WithIdeal A] [IsAdicComplete (maximalIdeal A) A]
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
     ∀ (f : OriginalContinuousCoefficientFiber
       (arithmeticAuxiliaryUniversalResidueEquiv b hb q hq hqb σ hσ δ hδ Q hI) eA) g,
       (arithmeticUniversalAuxiliaryFramedFiberEquiv hA eA b hb q hq hqb σ hσ δ hδ Q hI f).val.val g =
         GeneralLinearGroup.map f.val.toRingHom
           (arithmeticAuxiliaryUniversalRepresentation b hb q hq hqb σ hσ δ Q g)) := by
  letI := arithmeticFixedDeterminantRing_isLocal b hb q hq hqb σ hσ δ hδ
  exact arithmeticAuxiliaryQuotientFramedFiberEquiv_evaluation
    (arithmeticFixedDeterminantResidueEquiv b hb q hq hqb σ hσ δ hδ) eA b Q σ δ
    (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ).toMonoidHom
    (arithmeticFixedDeterminantRepresentation_auxiliary_residue_one b hb q hq hqb σ hσ δ hδ Q hI)
    (arithmeticFixedDeterminantFramedFiberEquiv hA eA b hb q hq hqb σ hσ δ hδ)
    (arithmeticFixedDeterminantFramedFiberEquiv_evaluation hA eA b hb q hq hqb σ hσ δ hδ)

end
end Dubon2026
