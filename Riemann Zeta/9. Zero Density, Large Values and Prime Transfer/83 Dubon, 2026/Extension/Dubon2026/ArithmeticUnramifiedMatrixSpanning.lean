import Dubon2026.LocalMatrixRepresentationCentralizer
import Dubon2026.ArithmeticUnramifiedRepresentation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Actual original universal arithmetic matrices span their full completed coefficient algebra -/

namespace Dubon2026
noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The same original universal unramified fixed-determinant arithmetic representation spans its genuine completed coefficient matrix algebra under explicit absolute irreducibility of the original residual representation. -/
theorem arithmeticUnramifiedRepresentation_span_eq_top
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure (IsLocalRing.ResidueField O)) σ))]
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Submodule.span (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)
      (Set.range (fun g => (arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P g).val)) = ⊤ := by
  letI := arithmeticUnramifiedDeformationRing_isLocal a ha p hp hpa σ hσ δ hδ P hP
  let e := arithmeticUnramifiedDeformationResidueEquiv a ha p hp hpa σ hσ δ hδ P hP
  let r := (localCoefficientReduction e).toRingHom
  let ρ := (arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P).toMonoidHom
  have hred : (GeneralLinearGroup.map r).comp ρ = σ :=
    arithmeticUnramifiedRepresentation_residue a ha p hp hpa σ hσ δ hδ P hP
  letI : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure (IsLocalRing.ResidueField O))
        ((GeneralLinearGroup.map r).comp ρ))) := by
    rw [hred]
    infer_instance
  exact localMatrixRepresentation_span_eq_top_of_reduction
    (L := AlgebraicClosure (IsLocalRing.ResidueField O)) r
    (localCoefficientReduction_surjective e) (localCoefficientReduction_eq_zero_iff e) ρ

/-- A genuine invertible stabilizer of the original universal arithmetic representation is an original completed-coefficient scalar unit. -/
theorem arithmeticUnramifiedRepresentation_stabilizer_scalar_unit
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure (IsLocalRing.ResidueField O)) σ))]
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (U : GeneralLinearGroup ι (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P))
    (hU : ∀ g, U * arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P g =
      arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P g * U) :
    ∃ u : (ArithmeticUnramifiedDeformationRing a ha p hp hpa σ hσ δ P)ˣ,
      U = GeneralLinearGroup.scalar ι u := by
  exact matrixRepresentation_stabilizer_scalar_unit_of_span
    (arithmeticUnramifiedRepresentation a ha p hp hpa σ hσ δ P).toMonoidHom
    (arithmeticUnramifiedRepresentation_span_eq_top a ha p hp hpa σ hσ δ hδ P hP) U hU

end
end Dubon2026
