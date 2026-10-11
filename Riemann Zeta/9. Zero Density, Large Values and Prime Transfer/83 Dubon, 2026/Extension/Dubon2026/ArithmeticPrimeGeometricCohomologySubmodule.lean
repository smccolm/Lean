import Dubon2026.ArithmeticPrimeGeometricFiniteFlatCohomology
import Dubon2026.RelativeDualNumberDeterminantCohomology

/-! # The constructed intrinsic arithmetic finite-flat submodule lies in the actual trace kernel -/

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

/-- The unique intrinsic geometric finite-flat cohomology submodule constructed from
actual arithmetic universality, at the original prime completion. Its characterization
is independent of a separately specified linear condition. -/
def arithmeticPrimeGeometricFiniteFlatClasses :
    Submodule (IsLocalRing.ResidueField O) (ContinuousMatrixAdjointH1 σ hσ) :=
  Classical.choose (arithmeticPrimeGeometricFiniteFlatCohomology_existsUnique (L := L) a ha p hp hpa σ hσ i₀ δ hδ m)

/-- Membership in the constructed actual submodule is precisely the original geometric
condition on prescribed-determinant dual-number deformation classes. -/
theorem arithmeticPrimeGeometricFiniteFlatClasses_mem_iff
    (x : ContinuousMatrixAdjointH1 σ hσ) :
    x ∈ (arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m) ↔
      x ∈ originalGeometricFiniteFlatCohomologyCondition
        (R := rationalPrimeLocalIntegerRing p hp) (rationalArithmeticGaloisGroup a) σ hσ δ
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom :=
  (Classical.choose_spec (arithmeticPrimeGeometricFiniteFlatCohomology_existsUnique (L := L) a ha p hp hpa σ hσ i₀ δ hδ m)).1.1 x

/-- The same constructed original geometric finite-flat submodule is finite dimensional
by the already proved finiteness of the actual arithmetic continuous cohomology. -/
theorem arithmeticPrimeGeometricFiniteFlatClasses_finiteDimensional :
    Module.Finite (IsLocalRing.ResidueField O) (arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m) :=
  (Classical.choose_spec (arithmeticPrimeGeometricFiniteFlatCohomology_existsUnique (L := L) a ha p hp hpa σ hσ i₀ δ hδ m)).1.2

/-- The actual geometric submodule lies in the original trace-kernel condition: the true
original determinant condition and residual compatibility prove this inclusion through
the exact class/cohomology comparison. No trace condition is assumed. -/
theorem arithmeticPrimeGeometricFiniteFlatClasses_le_fixedDeterminant :
    (arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m) ≤ continuousFixedDeterminantClasses σ hσ := by
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  intro x hx
  have hc := (arithmeticPrimeGeometricFiniteFlatClasses_mem_iff (L := L) a ha p hp hpa σ hσ i₀ δ hδ m x).mp hx
  obtain ⟨c, hc, hcx⟩ := hc
  rw [← hcx]
  exact (relativeDualNumberUnframedHasDeterminant_iff
    (rationalArithmeticGaloisGroup a) σ hσ δ hδ c).mp hc.1

end
end Dubon2026
