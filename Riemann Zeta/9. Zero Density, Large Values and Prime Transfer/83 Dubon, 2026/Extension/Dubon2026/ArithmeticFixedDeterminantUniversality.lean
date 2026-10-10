import Dubon2026.ArithmeticFixedDeterminantRing

/-! # Classification of actual arithmetic framed lifts with prescribed determinant -/

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

/-- Maps from the actual arithmetic fixed-determinant ring classify precisely all original continuous framed lifts having the prescribed determinant at every group element. -/
def arithmeticFixedDeterminantFramedFiberEquiv
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
     OriginalContinuousCoefficientFiber
       (arithmeticFixedDeterminantResidueEquiv a ha p hp hpa σ hσ δ hδ) eA ≃
         {f : OriginalContinuousFramedFiber eA (rationalArithmeticGaloisGroup a) σ //
           ∀ g, GeneralLinearGroup.det (f.val g) = Units.map (algebraMap O A) (δ g)}) := by
  letI := arithmeticFramedUniversalRing_isLocal a ha p hp hpa σ hσ
  letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
  let eR := arithmeticFramedUniversalResidueEquiv a ha p hp hpa σ hσ
  let ρ := (arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ).toMonoidHom
  let J := representationDeterminantIdeal ρ δ
  exact (originalLocalQuotientCoefficientFiberEquiv eR eA J).trans
    ((arithmeticFramedFiberEquiv hA eA a ha p hp hpa σ hσ).subtypeEquiv
      (fun f => representationDeterminantIdeal_le_kernel_iff ρ δ f.val))

/-- The actual fixed-determinant classification evaluates the original universal matrices through the genuine determinant quotient. -/
theorem arithmeticFixedDeterminantFramedFiberEquiv_evaluation
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g)) :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
     ∀ (f : OriginalContinuousCoefficientFiber
       (arithmeticFixedDeterminantResidueEquiv a ha p hp hpa σ hσ δ hδ) eA)
       (g : rationalArithmeticGaloisGroup a),
       (arithmeticFixedDeterminantFramedFiberEquiv hA eA a ha p hp hpa σ hσ δ hδ f).val.val g =
         GeneralLinearGroup.map (n := ι) f.val.toRingHom
           (GeneralLinearGroup.map (n := ι)
             (Ideal.Quotient.mk (representationDeterminantIdeal
               (arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ).toMonoidHom δ))
             (arithmeticFramedUniversalRepresentation a ha p hp hpa σ hσ g))) := by
  intro f g
  rfl

variable {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- The genuine arithmetic fixed-determinant classification is natural under every continuous residue-preserving coefficient map, on every original group element. -/
theorem arithmeticFixedDeterminantFramedFiberEquiv_natural
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha p hp hpa σ hσ δ hδ
     ∀ (f : OriginalContinuousCoefficientFiber
       (arithmeticFixedDeterminantResidueEquiv a ha p hp hpa σ hσ δ hδ) eA)
       (g : rationalArithmeticGaloisGroup a),
       (arithmeticFixedDeterminantFramedFiberEquiv hB eB a ha p hp hpa σ hσ δ hδ
         (originalCoefficientFiberPostcomp _ eA eB k hk hres f)).val.val g =
           GeneralLinearGroup.map (n := ι) k.toRingHom
             ((arithmeticFixedDeterminantFramedFiberEquiv hA eA a ha p hp hpa σ hσ δ hδ f).val.val g)) := by
  intro f g
  rfl

end
end Dubon2026
