import Dubon2026.ArithmeticFramedUniversalRing

/-! # Natural classification of every original arithmetic framed lift -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {ι O A : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Genuine continuous residue-preserving maps from the actual derived arithmetic ring classify every original continuous framed lift. No presentation, finite-character or universal-ring certificate is an external premise. -/
def arithmeticFramedFiberEquiv
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :
    (letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
     OriginalContinuousCoefficientFiber (arithmeticFramedUniversalResidueEquiv a ha p hp hpa σ hσ) eA ≃
       OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup a) σ) :=
  fixedResidualFramedFiberEquiv hA eA p hp (rationalArithmeticGaloisGroup a) σ hσ
    (arithmeticResidualGenerators a ha p hp hpa σ hσ)
    (arithmeticResidualGenerators_surjective a ha p hp hpa σ hσ)

/-- The actual arithmetic framed classification evaluates the genuine universal representation at every original arithmetic Galois element. -/
theorem arithmeticFramedFiberEquiv_evaluation
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) :
    (letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
     ∀ (f : OriginalContinuousCoefficientFiber
       (arithmeticFramedUniversalResidueEquiv a ha p hp hpa σ hσ) eA)
       (g : rationalArithmeticGaloisGroup a),
       (arithmeticFramedFiberEquiv hA eA a ha p hp hpa σ hσ f).val g =
         GeneralLinearGroup.map (n := ι) f.val.toRingHom
           (arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ g)) := by
  intro f g
  rfl

variable {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- The actual arithmetic coefficient-map classification is natural for every original continuous residue-preserving map of complete Noetherian local coefficient algebras. This is the literal original universal-matrix evaluation identity. -/
theorem arithmeticFramedFiberEquiv_natural
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    (letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
     ∀ f : OriginalContinuousCoefficientFiber
       (arithmeticFramedUniversalResidueEquiv a ha p hp hpa σ hσ) eA,
       arithmeticFramedFiberEquiv hB eB a ha p hp hpa σ hσ
         (originalCoefficientFiberPostcomp _ eA eB k hk hres f) =
           originalFramedFiberPostcomp eA eB (rationalArithmeticGaloisGroup a) σ k hk hres
             (arithmeticFramedFiberEquiv hA eA a ha p hp hpa σ hσ f)) := by
  intro f
  apply Subtype.ext
  apply DFunLike.ext
  intro g
  rfl

end
end Dubon2026
