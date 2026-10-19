import Dubon2026.AuxiliaryParameterActionFactorization
import Dubon2026.ArithmeticFixedDeterminantCompactness

/-! Apply the compatible parameter action to the original compact arithmetic
coefficient ring. Its residue comparison and topology derive the action
factorization; these are not new inputs to arithmetic selection. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

/-- The original fixed-determinant ring supplies the compact separated topology
and residue comparison required for the compatible auxiliary action. -/
def arithmeticFixedDeterminantConvergingParameterData
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (b : 𝓞 ℚ) (hb : b ≠ 0) (q degree level : ℕ) [Fact q.Prime]
    [CharP (ResidueField O) q] (hqb : (q : 𝓞 ℚ) ∣ b)
    (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup b →* Oˣ)
    (hδ : ∀ x, GeneralLinearGroup.det (σ x) = Units.map (algebraMap O (ResidueField O)) (δ x))
    {A ι η : Type} [CommRing A] [Algebra O A] [Fintype ι] [DecidableEq ι] [Fintype η]
    (Q : Finset Nat.Primes)
    (τ₀ : rationalArithmeticGaloisGroup b → GeneralLinearGroup (Fin (degree + 1)) A)
    (d : letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ
      AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q
        (arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σ hσ δ) τ₀ η)
    (hmod : ∀ p : Q, p.val.val ≡ 1 [MOD q ^ level]) :
    letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ
    AuxiliaryCompatibleConvergingParameterData O (ι := ι) (η := η) Q q level
      (arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σ hσ δ) τ₀ :=
  letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ
  letI := (arithmeticFixedDeterminantRing_localData b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ).1
  letI := (arithmeticFixedDeterminantRing_localData b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ).2.1
  letI := arithmeticFixedDeterminantRing_compactSpace b hb q (Fact.out : q.Prime) hqb σ hσ δ
  letI := arithmeticFixedDeterminantRing_t2Space b hb q (Fact.out : q.Prime) hqb σ hσ δ
  auxiliaryComparisonCompatibleConvergingParameterAction O Q q level
    (arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σ hσ δ) τ₀ d hmod
    (arithmeticFixedDeterminantResidueEquiv b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ)

end
end Dubon2026
