import Dubon2026.ArithmeticUniversalAuxiliaryFamily
import Dubon2026.ArithmeticSupportInertia

/-! The original-support determinant automatically satisfies every
selected local unramifiedness condition. The universal finite-family
augmentation comparison therefore needs no separately supplied inertia
condition for that determinant. Residual modular realization and the
literal local residual compatibility remain upstream inputs for the
Dubon Theorem 2.6 deformation and arithmetic patching chain. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The actual universal ring carries one family parameter map with
degree coordinates per selected prime. Its augmentation specializes
exactly to all the original selected local unramifiedness relations. -/
theorem arithmeticUniversal_support_auxiliary_family_augmentation
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a b : 𝓞 ℚ) (hab : a ∣ b) (hb : b ≠ 0) (q degree level : ℕ) [Fact q.Prime]
    (hqb : (q : 𝓞 ℚ) ∣ b) (hlevel : 0 < level)
    (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) ((δ.comp (rationalArithmeticSupportRestriction a b hab).toMonoidHom) g))
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (Q : Finset Nat.Primes)
    (hgood : ∀ p : Q, RationalArithmeticTorusAuxiliaryPrime a q degree level R p.val)
    (hpb : ∀ p : Q, (p.val.val : 𝓞 ℚ) ∣ b)
    (hcompat : ∀ (p : Q) g, GeneralLinearGroup.map eO.toRingHom
      (σ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val.val p.val.property g)) :
    let A := ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) hqb σ hσ (δ.comp (rationalArithmeticSupportRestriction a b hab).toMonoidHom)
    letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σ hσ (δ.comp (rationalArithmeticSupportRestriction a b hab).toMonoidHom) hδ
    ∃ κ : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q →* (Fin degree → A)ˣ,
      (∀ p d i, residue A ((κ p d).val i) = 1) ∧
      auxiliaryFamilyAugmentationIdeal O
        (D := fun p : Q => RationalPrimeTameCoefficientQuotient p.val.val q) κ =
        ⨆ p : Q, matrixRepresentationRelationIdeal
          ((arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σ hσ (δ.comp (rationalArithmeticSupportRestriction a b hab).toMonoidHom)).toMonoidHom.comp
            (rationalPrimeArithmeticRestriction b p.val.val p.val.property).toMonoidHom)
          (rationalPrimeNormInertia p.val.val p.val.property) := by
  apply arithmeticUniversal_auxiliary_family_augmentation a b hb q degree level hqb hlevel
    eO σ hσ (δ.comp (rationalArithmeticSupportRestriction a b hab).toMonoidHom) hδ R Q hgood hpb
  · intro p g hg
    exact rationalArithmeticSupportCharacter_inertia_eq_one a b hab δ
      p.val.val p.val.property (hgood p).1 g hg
  · exact hcompat

end
end Dubon2026
