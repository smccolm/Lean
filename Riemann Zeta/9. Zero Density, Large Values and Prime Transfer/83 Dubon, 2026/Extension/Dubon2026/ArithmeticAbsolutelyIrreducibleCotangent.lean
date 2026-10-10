import Dubon2026.ArithmeticLocalCotangentDimension
import Dubon2026.MatrixAdjointInvariantDimension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Genuine original arithmetic cotangent dimension under absolute residual irreducibility -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Irreducibility of the actual residual column-vector representation over its algebraic closure discharges the invariant-matrix term in the original arithmetic framed cotangent dimension formula. -/
theorem arithmeticLocalCotangentDual_finrank_of_absoluteIrreducible
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure (IsLocalRing.ResidueField O)) σ))]
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Module.finrank (IsLocalRing.ResidueField O) (ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP) + 1 =
      Module.finrank (IsLocalRing.ResidueField O)
        (arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal) + Fintype.card ι ^ 2 := by
  have hi := matrixAdjointInvariants_finrank_of_extension
    (AlgebraicClosure (IsLocalRing.ResidueField O)) σ
  exact (congrArg (fun n : ℕ =>
    Module.finrank (IsLocalRing.ResidueField O) (ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP) + n)
      hi.symm).trans (arithmeticLocalCotangentDual_finrank_add_invariants a ha p hp hpa σ hσ δ hδ P hP)

end
end Dubon2026
