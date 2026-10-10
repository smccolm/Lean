import Dubon2026.ArithmeticRelativeLocalDualNumberFramedEquiv
import Dubon2026.ArithmeticUnramifiedUniversality

/-! # Actual relative dual-number points of the original arithmetic local deformation ring -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- All original continuous residue-preserving coefficient maps from the actual local deformation ring to its residual dual numbers over the original coefficient ring. -/
def ArithmeticLocalTangentPoint
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) : Type :=
  letI : Finite (DualNumber (IsLocalRing.ResidueField O)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O))
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O)))
      (DualNumber (IsLocalRing.ResidueField O)) :=
    finiteDualNumber_maximal_isAdicComplete (IsLocalRing.ResidueField O)
  ArithmeticUnramifiedCoefficientFiber (relativeDualNumberResidueEquiv O)
    a ha p hp hpa σ hσ δ hδ P hP

/-- The actual relative dual-number points of the original local deformation ring classify all original continuous first-order lifts satisfying its inertia and determinant conditions. -/
def arithmeticLocalTangentPointEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalTangentPoint a ha p hp hpa σ hσ δ hδ P hP ≃
      ArithmeticLocalFirstOrderLift a σ P.asIdeal := by
  letI : Finite (DualNumber (IsLocalRing.ResidueField O)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O))
  letI : WithIdeal (DualNumber (IsLocalRing.ResidueField O)) :=
    ⟨IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O))⟩
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (DualNumber (IsLocalRing.ResidueField O)))
      (DualNumber (IsLocalRing.ResidueField O)) :=
    finiteDualNumber_maximal_isAdicComplete (IsLocalRing.ResidueField O)
  exact (arithmeticUnramifiedFramedFiberEquiv rfl (relativeDualNumberResidueEquiv O)
    a ha p hp hpa σ hσ δ hδ P hP).trans
      (arithmeticRelativeLocalDualNumberFramedFiberEquiv a σ δ hδ P.asIdeal).symm

/-- Every original continuous first-order local lift corresponds uniquely to an actual relative dual-number point of the original local deformation ring. -/
theorem arithmeticLocalTangentPointEquiv_bijective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Bijective (arithmeticLocalTangentPointEquiv a ha p hp hpa σ hσ δ hδ P hP) :=
  (arithmeticLocalTangentPointEquiv a ha p hp hpa σ hσ δ hδ P hP).bijective

/-- The original coefficient point determines its actual continuous local cohomology class via the same whole first-order representation. -/
def arithmeticLocalTangentPointClass
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (f : ArithmeticLocalTangentPoint a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal :=
  arithmeticLocalFirstOrderClass a σ hσ P.asIdeal hP
    (arithmeticLocalTangentPointEquiv a ha p hp hpa σ hσ δ hδ P hP f)

/-- Every actual local cohomology class is obtained from a genuine relative dual-number coefficient point of the original universal ring. -/
theorem arithmeticLocalTangentPointClass_surjective
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Function.Surjective (arithmeticLocalTangentPointClass a ha p hp hpa σ hσ δ hδ P hP) :=
  (arithmeticLocalFirstOrderClass_surjective a σ hσ P.asIdeal hP).comp
    (arithmeticLocalTangentPointEquiv a ha p hp hpa σ hσ δ hδ P hP).surjective

/-- Two original relative coefficient points have equal local classes exactly when their actual entire first-order representations are strictly conjugate. -/
theorem arithmeticLocalTangentPointClass_eq_iff
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker)
    (f g : ArithmeticLocalTangentPoint a ha p hp hpa σ hσ δ hδ P hP) :
    arithmeticLocalTangentPointClass a ha p hp hpa σ hσ δ hδ P hP f =
      arithmeticLocalTangentPointClass a ha p hp hpa σ hσ δ hδ P hP g ↔
        MatrixFirstOrderStrictlyConjugate σ
          (arithmeticLocalTangentPointEquiv a ha p hp hpa σ hσ δ hδ P hP f).val.val
          (arithmeticLocalTangentPointEquiv a ha p hp hpa σ hσ δ hδ P hP g).val.val :=
  arithmeticLocalFirstOrderClass_eq_iff a σ hσ P.asIdeal hP _ _

end
end Dubon2026
