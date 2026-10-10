import Dubon2026.ArithmeticAbsolutelyIrreducibleCotangent
import Dubon2026.ArithmeticUnramifiedTraceZeroClasses
import Dubon2026.TraceZeroAdjointInvariants
import Dubon2026.MatrixAdjointInvariantDimension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The original trace-zero arithmetic local tangent formula -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The same original absolutely irreducible residual representation has vanishing trace-zero invariants and the genuine framed cotangent dimension expressed by its actual trace-zero inertia kernel. -/
theorem arithmeticLocalCotangent_traceZero_invariants_dimension
    (hn : (Fintype.card ι : IsLocalRing.ResidueField O) ≠ 0)
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
    (matrixTraceZeroAdjointRepresentation σ).invariants = ⊥ ∧
    Module.finrank (IsLocalRing.ResidueField O) (ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP) + 1 =
      Module.finrank (IsLocalRing.ResidueField O)
        (arithmeticUnramifiedTraceZeroClasses a σ hσ P.asIdeal) + Fintype.card ι ^ 2 := by
  refine ⟨matrixTraceZeroAdjointInvariants_eq_bot
    (L := AlgebraicClosure (IsLocalRing.ResidueField O)) hn σ, ?_⟩
  have hd := arithmeticLocalCotangentDual_finrank_of_absoluteIrreducible
    a ha p hp hpa σ hσ δ hδ P hP
  exact hd.trans (congrArg (fun n : ℕ => n + Fintype.card ι ^ 2)
    (arithmeticUnramifiedTraceZeroClasses_finrank hn a σ hσ P.asIdeal).symm)

end
end Dubon2026
