import Dubon2026.ArithmeticPrimeGeometricCohomologyRestriction
import Dubon2026.ArithmeticPrimeGeometricTraceZeroCohomology
import Dubon2026.ContinuousTraceZeroRestriction

/-! # Genuine trace-zero localization of the arithmetic geometric condition -/

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

/-- The actual geometric trace-zero submodule is characterized by the genuine
local finite-flat condition on the actual restricted trace-zero class. The trace
condition is automatic under the original inclusion; no local vanishing or numerical
Selmer formula is imposed as an extra hypothesis. -/
theorem arithmeticPrimeGeometricTraceZeroClasses_restriction_iff
    (x : ContinuousTraceZeroAdjointH1 σ hσ) :
    x ∈ arithmeticPrimeGeometricTraceZeroClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m ↔
      continuousTraceZeroH1Inclusion
        (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
        (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)
        (continuousTraceZeroH1Restriction σ hσ
          (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
          (rationalPrimeArithmeticRestriction a p hp).continuous x) ∈
        localGeometricFiniteFlatCohomologyCondition
          (rationalPrimeLocalIntegerRing p hp) (rationalPrimeLocalField p hp)
          (rationalPrimeLocalClosure p hp)
          (σ.comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
          (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) := by
  change continuousTraceZeroH1Inclusion σ hσ x ∈
    arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m ↔ _
  rw [continuousTraceZeroH1Restriction_inclusion σ hσ
    (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    (rationalPrimeArithmeticRestriction a p hp).continuous x]
  exact (arithmeticPrimeGeometricFiniteFlatClasses_restriction_iff (L := L)
    a ha p hp hpa σ hσ i₀ δ hδ m (continuousTraceZeroH1Inclusion σ hσ x)).trans
      (and_iff_right (continuousTraceZeroH1ToFixedDeterminant σ hσ x).property)

end
end Dubon2026
