import Dubon2026.ArithmeticTraceUniversalRing
import Dubon2026.FixedResidualTraceUnframedUniversality

/-! # Actual complete local unframed universal trace ring for the original arithmetic Galois group -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι O L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

/-- The literal original arithmetic trace ring is complete local and Noetherian and one actual whole arithmetic representation over it classifies every original unframed lift over every complete Noetherian local target. The genuine original arithmetic finite presentation, fixed-residual quotient transport and trace-ring properties are all derived. -/
theorem arithmeticTraceUnframedUniversality_exists
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] (i₀ : ι) :
    ∃ hlocal : IsLocalRing (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ),
      letI := hlocal
      IsNoetherianRing (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ) ∧
      IsAdic (IsLocalRing.maximalIdeal (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ))
        (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ) ∧
      ∃ (eT : IsLocalRing.ResidueField (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ)
          ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup ι
          (ArithmeticTraceCoefficientRing a ha p hp hpa σ hσ))
        (hτres : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
          [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
          (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
          Function.Bijective (originalCoefficientRepresentationClass eT eA
            (rationalArithmeticGaloisGroup a) σ τ hτres) := by
  exact fixedResidualTraceUnframedUniversality_exists (L := L) p hp
    (rationalArithmeticGaloisGroup a) σ hσ
    (arithmeticResidualGenerators a ha p hp hpa σ hσ)
    (arithmeticResidualGenerators_surjective a ha p hp hpa σ hσ) i₀

end
end Dubon2026
