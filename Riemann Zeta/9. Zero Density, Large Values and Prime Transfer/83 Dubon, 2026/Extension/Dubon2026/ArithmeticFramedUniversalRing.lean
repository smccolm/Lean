import Dubon2026.ArithmeticResidualProfinitePresentation
import Dubon2026.FixedResidualFramedUniversality

/-! # The actual complete local framed ring of an original arithmetic residual representation -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- Choose actual finitely many generators from the proved presentation of the original arithmetic fixed residual quotient. -/
def arithmeticResidualGenerators
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :
    Finset (originalResidualProfiniteGroup p (rationalArithmeticGaloisGroup a) σ hσ) :=
  Classical.choose (rationalArithmeticResidual_has_profinite_presentation a ha p hp hpa σ hσ)

omit [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- The chosen original arithmetic generators give a genuine surjective presentation of the entire fixed residual quotient. -/
theorem arithmeticResidualGenerators_surjective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :
    Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p (rationalArithmeticGaloisGroup a) σ hσ)
      (arithmeticResidualGenerators a ha p hp hpa σ hσ)) :=
  Classical.choose_spec (rationalArithmeticResidual_has_profinite_presentation a ha p hp hpa σ hσ)

/-- The genuine completed all-relation coefficient ring for the original arithmetic residual representation. Its finitely many group generators are derived, and every original relation is retained. -/
abbrev ArithmeticFramedUniversalRing
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :=
  FixedResidualFramedCoefficientRing p (rationalArithmeticGaloisGroup a) σ hσ
    (arithmeticResidualGenerators a ha p hp hpa σ hσ)

/-- The actual arithmetic framed ring is local because its original relations vanish at the given original residual representation. -/
theorem arithmeticFramedUniversalRing_isLocal
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :
    IsLocalRing (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ) :=
  fixedResidualFramedCoefficientRing_isLocal p (rationalArithmeticGaloisGroup a) σ hσ
    (arithmeticResidualGenerators a ha p hp hpa σ hσ)

/-- The actual arithmetic framed ring has its true original coefficient residue field. -/
def arithmeticFramedUniversalResidueEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :
    (letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
     IsLocalRing.ResidueField (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ) ≃ₐ[O]
       IsLocalRing.ResidueField O) :=
  fixedResidualFramedCoefficientResidueEquiv p (rationalArithmeticGaloisGroup a) σ hσ
    (arithmeticResidualGenerators a ha p hp hpa σ hσ)

/-- The actual arithmetic all-relation ring is Noetherian and complete in its genuine maximal-adic topology. These are derived properties of the same ring. -/
theorem arithmeticFramedUniversalRing_localData
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :
    (letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
     IsNoetherianRing (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ))
         (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ) ∧
       (inferInstance : TopologicalSpace (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ)) =
         (IsLocalRing.maximalIdeal (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ)).adicTopology) :=
  fixedResidualFramedCoefficientRing_localData p (rationalArithmeticGaloisGroup a) σ hσ
    (arithmeticResidualGenerators a ha p hp hpa σ hσ)

/-- The actual universal whole arithmetic representation over its derived complete local coefficient ring. -/
def arithmeticFramedUniversalRepresentation
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :
    rationalArithmeticGaloisGroup a →ₜ*
      GeneralLinearGroup ι (ArithmeticFramedUniversalRing a ha p hp hpa σ hσ) :=
  ⟨fixedResidualFramedUniversalRepresentation p (rationalArithmeticGaloisGroup a) σ hσ
    (arithmeticResidualGenerators a ha p hp hpa σ hσ)
    (arithmeticResidualGenerators_surjective a ha p hp hpa σ hσ),
   fixedResidualFramedUniversalRepresentation_continuous p (rationalArithmeticGaloisGroup a) σ hσ
    (arithmeticResidualGenerators a ha p hp hpa σ hσ)
    (arithmeticResidualGenerators_surjective a ha p hp hpa σ hσ)⟩

/-- The genuine continuous universal arithmetic representation reduces through its true residue field to the original entire residual representation. -/
theorem arithmeticFramedUniversalRepresentation_residue
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :
    (letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
     (GeneralLinearGroup.map (n := ι)
       (localCoefficientReduction (arithmeticFramedUniversalResidueEquiv a ha p hp hpa σ hσ)).toRingHom).comp
         (arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ).toMonoidHom = σ) :=
  fixedResidualFramedUniversalRepresentation_residue p (rationalArithmeticGaloisGroup a) σ hσ
    (arithmeticResidualGenerators a ha p hp hpa σ hσ)
    (arithmeticResidualGenerators_surjective a ha p hp hpa σ hσ)

end
end Dubon2026
