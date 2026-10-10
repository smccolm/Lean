import Dubon2026.ArithmeticLocalCotangentDual
import Dubon2026.ArithmeticUnramifiedTraceZeroClasses

/-! # Actual arithmetic cotangent classes in trace-zero cohomology -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The ordinary dual of the actual arithmetic cotangent quotient maps linearly to the genuine trace-zero inertia kernel. -/
def arithmeticLocalCotangentDualTraceZeroClassLinearMap
    (hn : (Fintype.card ι : IsLocalRing.ResidueField O) ≠ 0)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP →ₗ[IsLocalRing.ResidueField O]
      arithmeticUnramifiedTraceZeroClasses a σ hσ P.asIdeal :=
  (arithmeticUnramifiedTraceZeroFixedDeterminantEquiv hn a σ hσ P.asIdeal).symm.toLinearMap.comp
    (arithmeticLocalCotangentDualClassLinearMap a ha p hp hpa σ hσ δ hδ P hP)

/-- Every genuine trace-zero inertia class is attained by the ordinary residue dual of the same actual arithmetic cotangent quotient. -/
theorem arithmeticLocalCotangentDualTraceZeroClassLinearMap_surjective
    (hn : (Fintype.card ι : IsLocalRing.ResidueField O) ≠ 0)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Surjective (arithmeticLocalCotangentDualTraceZeroClassLinearMap hn a ha p hp hpa σ hσ δ hδ P hP) :=
  (arithmeticUnramifiedTraceZeroFixedDeterminantEquiv hn a σ hσ P.asIdeal).symm.surjective.comp
    (arithmeticLocalCotangentDualClassLinearMap_surjective a ha p hp hpa σ hσ δ hδ P hP)

/-- The dimension of the genuine trace-zero inertia kernel is bounded by the dimension of the literal original relative maximal-ideal cotangent quotient. -/
theorem arithmeticTraceZeroLocalClass_finrank_le_cotangent
    (hn : (Fintype.card ι : IsLocalRing.ResidueField O) ≠ 0)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    (letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
     letI : AddCommMonoid (RelativeMaximalCotangent O
       (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)) :=
         (instAddCommGroupRelativeMaximalCotangent O
           (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)).toAddCommMonoid
     letI := originalMaximalCotangentResidueModule (arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP)
     Module.finrank (IsLocalRing.ResidueField O)
       (arithmeticUnramifiedTraceZeroClasses a σ hσ P.asIdeal) ≤
         Module.finrank (IsLocalRing.ResidueField O)
           (RelativeMaximalCotangent O (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P))) := by
  exact (le_of_eq (arithmeticUnramifiedTraceZeroClasses_finrank hn a σ hσ P.asIdeal)).trans
    (arithmeticLocalClass_finrank_le_cotangent a ha p hp hpa σ hσ δ hδ P hP)

end
end Dubon2026
