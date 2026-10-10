import Dubon2026.ArithmeticFixedDeterminantRepresentation

/-! # Original compact Hausdorff arithmetic fixed-determinant coefficients -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The genuine arithmetic fixed-determinant coefficient ring is compact in its original quotient topology. -/
theorem arithmeticFixedDeterminantRing_compactSpace
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ) :
    CompactSpace (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ) := by
  let R := ArithmeticFramedUniversalRing a ha p hp hpa σ hσ
  let H := originalResidualProfiniteGroup p (rationalArithmeticGaloisGroup a) σ hσ
  let q := profiniteGeneratorPresentation H (arithmeticResidualGenerators a ha p hp hpa σ hσ)
  let τ := fixedResidualOriginalRepresentation p (rationalArithmeticGaloisGroup a) σ hσ
  letI : CompactSpace R := originalPresentedCoefficientRing_compactSpace H q τ
  exact inferInstanceAs (CompactSpace (R ⧸ representationDeterminantIdeal
    (arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ).toMonoidHom δ))

/-- The original arithmetic fixed-determinant coefficient topology is Hausdorff because its genuine ideal is closed in the original complete Noetherian coefficient ring. -/
theorem arithmeticFixedDeterminantRing_t2Space
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ) :
    T2Space (ArithmeticFixedDeterminantRing a ha p hp hpa σ hσ δ) := by
  let R := ArithmeticFramedUniversalRing a ha p hp hpa σ hσ
  letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
  letI : IsNoetherianRing R := (arithmeticFramedUniversalRing_localData a ha p hp hpa σ hσ).1
  let H := originalResidualProfiniteGroup p (rationalArithmeticGaloisGroup a) σ hσ
  let q := profiniteGeneratorPresentation H (arithmeticResidualGenerators a ha p hp hpa σ hσ)
  let τ := fixedResidualOriginalRepresentation p (rationalArithmeticGaloisGroup a) σ hσ
  letI : CompactSpace R := originalPresentedCoefficientRing_compactSpace H q τ
  letI : T2Space R := originalPresentedCoefficientRing_t2Space H q τ
  exact compactNoetherianQuotient_t2Space (representationDeterminantIdeal
    (arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ).toMonoidHom δ)

end
end Dubon2026
