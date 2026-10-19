import Dubon2026.ArithmeticUniversalConjugateAuxiliaryFamily
import Dubon2026.ArithmeticSupportInertia
import Dubon2026.ArithmeticSupportLocalConjugacy
import Dubon2026.AuxiliaryFamilyAugmentation

/-! Actual base-support residual and determinant characters are pulled
back through the constructed arithmetic restriction. Both determinant
unramifiedness and local residual conjugacy are then proved. The single
universal-ring family augmentation imposes exactly all selected original
inertia relations. This is the auxiliary coefficient specialization in
the Dubon Theorem 2.6 arithmetic patching chain; the identification with
the entire base-support deformation ring and Hecke comparison remain open. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The universal ring of the actual pulled-back original data carries
the full selected auxiliary family. Its augmentation image is exactly
the sum of the original local inertia relation ideals. Neither local
residual compatibility nor determinant inertia triviality is an input. -/
theorem arithmeticUniversal_original_support_family_augmentation
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a b : 𝓞 ℚ) (hab : a ∣ b) (hb : b ≠ 0) (q degree level : ℕ) [Fact q.Prime]
    (hqb : (q : 𝓞 ℚ) ∣ b) (hlevel : 0 < level) (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (Q : Finset Nat.Primes)
    (hgood : ∀ p : Q, RationalArithmeticTorusAuxiliaryPrime a q degree level
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val)
    (hpb : ∀ p : Q, (p.val.val : 𝓞 ℚ) ∣ b) :
    let π := rationalArithmeticSupportRestriction a b hab
    let σb := σ.comp π.toMonoidHom
    let hσb : Continuous σb := hσ.comp π.continuous
    let δb := δ.comp π.toMonoidHom
    let hδb : ∀ g, GeneralLinearGroup.det (σb g) =
      Units.map (algebraMap O (ResidueField O)) (δb g) := fun g => hδ (π g)
    let A := ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) hqb σb hσb δb
    letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb
    ∃ κ : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q →* (Fin degree → A)ˣ,
      (∀ p d i, residue A ((κ p d).val i) = 1) ∧
      auxiliaryFamilyAugmentationIdeal O
        (D := fun p : Q => RationalPrimeTameCoefficientQuotient p.val.val q) κ =
        ⨆ p : Q, matrixRepresentationRelationIdeal
          ((arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σb hσb δb).toMonoidHom.comp
            (rationalPrimeArithmeticRestriction b p.val.val p.val.property).toMonoidHom)
          (rationalPrimeNormInertia p.val.val p.val.property) := by
  let π := rationalArithmeticSupportRestriction a b hab
  let σb := σ.comp π.toMonoidHom
  let hσb : Continuous σb := hσ.comp π.continuous
  let δb := δ.comp π.toMonoidHom
  let hδb : ∀ g, GeneralLinearGroup.det (σb g) =
    Units.map (algebraMap O (ResidueField O)) (δb g) := fun g => hδ (π g)
  let R := (GeneralLinearGroup.map eO.toRingHom).comp σ
  have hc : ∀ p : Q, ∃ c : GeneralLinearGroup (Fin (degree + 1)) (ZMod q),
      ∀ g, GeneralLinearGroup.map eO.toRingHom
        (σb (rationalPrimeArithmeticRestriction b p.val.val p.val.property g)) =
          c⁻¹ * R (rationalPrimeArithmeticRestriction a p.val.val p.val.property g) * c := by
    intro p
    obtain ⟨u, hu⟩ := rationalArithmeticSupportRestriction_local_conjugacy a b hab p.val.val p.val.property
    refine ⟨R u, ?_⟩
    intro g
    change R (π (rationalPrimeArithmeticRestriction b p.val.val p.val.property g)) = _
    rw [hu g, map_mul, map_mul, map_inv]
  choose c hc using hc
  have hδI (p : Q) (g) (hg : g ∈ rationalPrimeNormInertia p.val.val p.val.property) :
      δb (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1 :=
    rationalArithmeticSupportCharacter_inertia_eq_one a b hab δ
      p.val.val p.val.property (hgood p).1 g hg
  exact arithmeticUniversal_conjugate_auxiliary_family_augmentation
    a b hb q degree level hqb hlevel eO σb hσb δb hδb R Q hgood hpb hδI c hc

end
end Dubon2026
