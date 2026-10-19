import Dubon2026.ArithmeticUniversalOriginalSupportAugmentation
import Dubon2026.LocalQuotientAlgEquivContinuity

/-! The actual auxiliary family augmentation recovers the original
fixed-determinant framed ring and all original universal matrices.
This assembles the character quotient, arithmetic support descent and
the two actual universal-ring maps. Further local deformation conditions
and arithmetic Hecke, patching and automorphy inputs remain separate. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

/-- The actual selected degree-parameter character family has an
augmentation quotient isomorphic to the genuine original-support
fixed-determinant framed ring, continuously in both directions in the original quotient topologies. Every universal matrix agrees under
arithmetic restriction. All auxiliary inertia and residue compatibility
conditions are derived from the original support and selected primes. -/
def arithmeticUniversalOriginalSupportTopologicalAugmentationComparison
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (b : 𝓞 ℚ) (hb : b ≠ 0) (hab : a ∣ b)
    (q degree level : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
    (hlevel : 0 < level) (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (Q : Finset Nat.Primes) (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ))
    (hgood : ∀ p : Q, RationalArithmeticTorusAuxiliaryPrime a q degree level
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val) :=
  let π := rationalArithmeticSupportRestriction a b hab
  let σb := σ.comp π.toMonoidHom
  let hσb : Continuous σb := hσ.comp π.continuous
  let δb := δ.comp π.toMonoidHom
  let hδb : ∀ g, GeneralLinearGroup.det (σb g) =
      Units.map (algebraMap O (ResidueField O)) (δb g) := fun g => hδ (π g)
  let hqb := dvd_trans hqa hab
  letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb
  letI := arithmeticFixedDeterminantRing_isLocal a ha q (Fact.out : q.Prime) hqa σ hσ δ hδ
  let c := arithmeticUniversalOriginalSupportAugmentationComparison
    a ha b hb hab q degree level hqa hlevel eO σ hσ δ hδ Q hba hgood
  auxiliaryFamilyAugmentationTopologicalComparisonOfAdic O
    (R := ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) hqb σb hσb δb)
    (A := ArithmeticFixedDeterminantRing a ha q (Fact.out : q.Prime) hqa σ hσ δ)
    (ι := Fin degree)
    (fun p : Q => RationalPrimeTameCoefficientQuotient p.val.val q)
    (arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σb hσb δb)
    (fun g => arithmeticFixedDeterminantRepresentation a ha q (Fact.out : q.Prime) hqa σ hσ δ (π g))
    (arithmeticFixedDeterminantRing_localData b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb).2.2
    (arithmeticFixedDeterminantRing_localData a ha q (Fact.out : q.Prime) hqa σ hσ δ hδ).2.2 c

end
end Dubon2026
