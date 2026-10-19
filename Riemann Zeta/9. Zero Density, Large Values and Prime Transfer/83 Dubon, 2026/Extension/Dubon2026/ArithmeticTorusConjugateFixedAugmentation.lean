import Dubon2026.ArithmeticTorusFixedAugmentation
import Dubon2026.MatrixRelationIdealConjugacy

/-! The actual selected-prime lift supplies the scalar group-algebra
parameters whose literal augmentation specialization imposes original
local unramifiedness. No diagonal presentation or quotient comparison is
assumed. The determinant is explicitly unramified on original inertia. This closes that local algebraic dependency on the arithmetic
patching route to Dubon Theorem 2.6; it does not supply modular realization
or arithmetic Hecke patching. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The same actual selected prime and complete adic global lift construct
exactly degree scalar inertia parameters for the rank degree+1 fixed-determinant lift. Their augmentation ideal is exactly the actual
local inertia matrix relation ideal, and all parameters reduce to one. -/
theorem rationalArithmetic_torus_conjugate_fixedDeterminant_augmentation_comparison
    (O : Type) [CommRing O]
    (a b : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime] (hlevel : 0 < level)
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes) [NeZero p.val]
    (hgood : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    (hpb : (p.val : 𝓞 ℚ) ∣ b)
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [WithIdeal A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra O A]
    (hA : (WithIdeal.i : Ideal A) = maximalIdeal A)
    (eA : ResidueField A ≃+* ZMod q)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) A)
    (hτ : Continuous τ)
    (c : GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (hred : ∀ g, GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        c⁻¹ * R (rationalPrimeArithmeticRestriction a p.val p.property g) * c)
    (hdet : ∀ g ∈ rationalPrimeNormInertia p.val p.property,
      GeneralLinearGroup.det (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) = 1) :
    ∃ κ : RationalPrimeTameCoefficientQuotient p.val q →* (Fin degree → A)ˣ,
      (∀ d i, residue A ((κ d).val i) = 1) ∧
      auxiliaryCharacterAugmentationIdeal O (D := RationalPrimeTameCoefficientQuotient p.val q) κ =
        matrixRepresentationRelationIdeal
          (τ.comp (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom)
          (rationalPrimeNormInertia p.val p.property) := by
  let f := eA.toRingHom.comp (residue A)
  obtain ⟨V, hV⟩ := generalLinearGroup_map_surjective f
    (eA.surjective.comp residue_surjective) c
  let τ' := matrixRepresentationConjugate τ V
  have hτ' : Continuous τ' := matrixRepresentationConjugate_continuous τ hτ V
  have hred' (g) : GeneralLinearGroup.map f
      (τ' (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g) := by
    change GeneralLinearGroup.map f
      (V * τ (rationalPrimeArithmeticRestriction b p.val p.property g) * V⁻¹) = _
    rw [map_mul, map_mul, map_inv, hV, hred g]
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  have hdet' (g) (hg : g ∈ rationalPrimeNormInertia p.val p.property) :
      GeneralLinearGroup.det (τ' (rationalPrimeArithmeticRestriction b p.val p.property g)) = 1 := by
    change GeneralLinearGroup.det (V * τ (rationalPrimeArithmeticRestriction b p.val p.property g) * V⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hdet g hg, mul_one, mul_inv_cancel]
  obtain ⟨κ, hκ, hJ⟩ := rationalArithmetic_torus_fixedDeterminant_augmentation_comparison
    O a b q degree level hlevel R p hgood hpb hA eA τ' hτ' hred' hdet'
  refine ⟨κ, hκ, ?_⟩
  change auxiliaryCharacterAugmentationIdeal O κ = matrixRepresentationRelationIdeal
    (matrixRepresentationConjugate (τ.comp
      (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom) V)
    (rationalPrimeNormInertia p.val p.property) at hJ
  exact hJ.trans (matrixRepresentationRelationIdeal_conjugate _ V _)

end
end Dubon2026
