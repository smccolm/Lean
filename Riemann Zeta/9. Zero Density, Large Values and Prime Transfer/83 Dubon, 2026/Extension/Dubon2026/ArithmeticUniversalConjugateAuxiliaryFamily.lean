import Dubon2026.ArithmeticUniversalConjugateTorusAugmentation
import Dubon2026.AuxiliaryFamilyAugmentation

/-! One actual finite auxiliary-prime set supplies a single parameter
group-algebra map on the same arithmetic universal fixed-determinant
ring. Its augmentation imposes exactly all original local inertia
relations together, as required by the Dubon Theorem 2.6 arithmetic
patching chain. The residual arithmetic representation and determinant
unramifiedness remain explicit upstream data. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

private theorem family_augmentation_of_local_comparisons
    (O : Type*) [CommRing O] {A S ι : Type*} [CommRing A] [IsLocalRing A] [Algebra O A]
    [Fintype S] [Fintype ι] {D : S → Type*} [∀ s, Group (D s)] (J : S → Ideal A)
    (h : ∀ s, ∃ κ : D s →* (ι → A)ˣ,
      (∀ d i, residue A ((κ d).val i) = 1) ∧ auxiliaryCharacterAugmentationIdeal O κ = J s) :
    ∃ κ : ∀ s, D s →* (ι → A)ˣ,
      (∀ s d i, residue A ((κ s d).val i) = 1) ∧
      auxiliaryFamilyAugmentationIdeal O κ = ⨆ s, J s := by
  choose κ hres hJ using h
  refine ⟨κ, hres, ?_⟩
  rw [auxiliaryFamilyAugmentationIdeal_eq_iSup]
  exact iSup_congr hJ

/-- The actual universal ring carries one family parameter map with
degree coordinates per selected prime. Its augmentation specializes
exactly to all the original selected local unramifiedness relations. -/
theorem arithmeticUniversal_conjugate_auxiliary_family_augmentation
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a b : 𝓞 ℚ) (hb : b ≠ 0) (q degree level : ℕ) [Fact q.Prime]
    (hqb : (q : 𝓞 ℚ) ∣ b) (hlevel : 0 < level)
    (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup b →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (Q : Finset Nat.Primes)
    (hgood : ∀ p : Q, RationalArithmeticTorusAuxiliaryPrime a q degree level R p.val)
    (hpb : ∀ p : Q, (p.val.val : 𝓞 ℚ) ∣ b)
    (hδI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      δ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1)
    (c : Q → GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (hcompat : ∀ (p : Q) g, GeneralLinearGroup.map eO.toRingHom
      (σ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g)) =
        (c p)⁻¹ * R (rationalPrimeArithmeticRestriction a p.val.val p.val.property g) * c p) :
    let A := ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) hqb σ hσ δ
    letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ
    ∃ κ : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q →* (Fin degree → A)ˣ,
      (∀ p d i, residue A ((κ p d).val i) = 1) ∧
      auxiliaryFamilyAugmentationIdeal O
        (D := fun p : Q => RationalPrimeTameCoefficientQuotient p.val.val q) κ =
        ⨆ p : Q, matrixRepresentationRelationIdeal
          ((arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σ hσ δ).toMonoidHom.comp
            (rationalPrimeArithmeticRestriction b p.val.val p.val.property).toMonoidHom)
          (rationalPrimeNormInertia p.val.val p.val.property) := by
  let A := ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) hqb σ hσ δ
  letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ
  apply family_augmentation_of_local_comparisons O
  intro p
  letI : NeZero p.val.val := ⟨p.val.property.ne_zero⟩
  exact arithmeticUniversal_torus_conjugate_fixedDeterminant_augmentation_comparison
    a b hb q degree level hqb hlevel eO σ hσ δ hδ R p.val (hgood p) (hpb p) (hδI p) (c p) (hcompat p)

end
end Dubon2026
