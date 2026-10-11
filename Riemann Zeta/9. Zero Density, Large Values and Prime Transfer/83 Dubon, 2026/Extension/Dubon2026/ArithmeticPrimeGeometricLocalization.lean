import Dubon2026.LocalGeometricFiniteFlatLinearity
import Dubon2026.ArithmeticPrimeGeometricTraceZeroRestriction

/-! # The actual prime-local geometric deformation space is a genuine localization preimage -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual full-adjoint localization preimage intersected with the original
global fixed-determinant subspace. Generic coefficients keep the quotient structures
explicit before specializing to the arithmetic Galois groups. -/
def continuousFixedDeterminantLocalPreimage
    {G H k : Type} [Group G] [Group H] [Field k]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace k]
    [IsTopologicalRing k]
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (j : H →* G) (hj : Continuous j)
    (S : Submodule k (ContinuousMatrixAdjointH1 (ρ.comp j) (hρ.comp hj))) :
    Submodule k (ContinuousMatrixAdjointH1 ρ hρ) :=
  continuousFixedDeterminantClasses ρ hρ ⊓
    S.comap (continuousMatrixAdjointH1Restriction ρ hρ j hj)

/-- The actual trace-zero localization preimage in the same original full-adjoint
local space, using the proved trace-zero restriction and inclusion. -/
def continuousTraceZeroLocalPreimage
    {G H k : Type} [Group G] [Group H] [Field k]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace k]
    [IsTopologicalRing k]
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (j : H →* G) (hj : Continuous j)
    (S : Submodule k (ContinuousMatrixAdjointH1 (ρ.comp j) (hρ.comp hj))) :
    Submodule k (ContinuousTraceZeroAdjointH1 ρ hρ) :=
  S.comap ((continuousTraceZeroH1Inclusion (ρ.comp j) (hρ.comp hj)).comp
    (continuousTraceZeroH1Restriction ρ hρ j hj))

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

/-- The original arithmetic geometric submodules are the actual localization
preimages of the constructed local finite-flat subspace, with the original global
trace condition in the full-adjoint presentation. This supplies the genuine linear
local-condition description; other exceptional-prime conditions and numerical Selmer
formulas remain separate obligations. -/
theorem arithmeticPrimeGeometricClasses_localization
    :
    letI : CharZero (rationalPrimeLocalField p hp) :=
      Algebra.charZero_of_charZero (R := ℚ) (A := rationalPrimeLocalField p hp)
    let j := rationalPrimeArithmeticRestriction a p hp
    let S := localGeometricFiniteFlatCohomologySubmodule (σ.comp j.toMonoidHom)
      (hσ.comp j.continuous) m
    arithmeticPrimeGeometricFiniteFlatClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m =
        continuousFixedDeterminantLocalPreimage σ hσ j.toMonoidHom j.continuous S ∧
      arithmeticPrimeGeometricTraceZeroClasses (L := L) a ha p hp hpa σ hσ i₀ δ hδ m =
        continuousTraceZeroLocalPreimage σ hσ j.toMonoidHom j.continuous S := by
  letI : CharZero (rationalPrimeLocalField p hp) :=
    Algebra.charZero_of_charZero (R := ℚ) (A := rationalPrimeLocalField p hp)
  constructor
  · apply Submodule.ext
    intro x
    exact arithmeticPrimeGeometricFiniteFlatClasses_restriction_iff (L := L)
      a ha p hp hpa σ hσ i₀ δ hδ m x
  · apply Submodule.ext
    intro x
    exact arithmeticPrimeGeometricTraceZeroClasses_restriction_iff (L := L)
      a ha p hp hpa σ hσ i₀ δ hδ m x

end
end Dubon2026
