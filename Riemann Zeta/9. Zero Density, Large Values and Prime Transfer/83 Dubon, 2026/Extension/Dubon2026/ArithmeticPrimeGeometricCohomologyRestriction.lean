import Dubon2026.ArithmeticPrimeGeometricCohomologySubmodule
import Dubon2026.OriginalGeometricCohomologyRestriction

/-! # The constructed arithmetic geometric submodule satisfies the genuine local restriction criterion -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {O L : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (Multiplicative (ι → IsLocalRing.ResidueField O))
      (matrixUnderlyingGroupAction (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)))

/-- Membership in the constructed arithmetic geometric submodule is exactly the
genuine global trace condition and the local geometric condition after restriction
along the constructed continuous map at the original prime completion. -/
theorem arithmeticPrimeGeometricFiniteFlatClasses_restriction_iff
    (x : ContinuousMatrixAdjointH1 σ hσ) :
    x ∈ arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m ↔
      x ∈ continuousFixedDeterminantClasses σ hσ ∧
        continuousMatrixAdjointH1Restriction σ hσ
          (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
          (rationalPrimeArithmeticRestriction a p hp).continuous x ∈
            localGeometricFiniteFlatCohomologyCondition
              (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp)
              (rationalPrimeLocalClosure p hp)
              (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
              (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) := by
  exact (arithmeticPrimeGeometricFiniteFlatClasses_mem_iff (L := L)
    a ha p hp hpa σ hσ i₀ δ hδ m x).trans
      (originalGeometricFiniteFlatCohomologyCondition_restriction_iff
        (rationalArithmeticGaloisGroup a) σ hσ δ hδ
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalPrimeArithmeticRestriction a p hp).continuous x)

end
end Dubon2026
