import Dubon2026.ArithmeticTorusFixedAugmentation
import Dubon2026.ArithmeticFixedDeterminantRepresentation

/-! The literal arithmetic universal fixed-determinant ring carries the
auxiliary scalar character parameters. Its augmentation ideal equals the
actual local inertia relation ideal. The universal representation and its
Noetherian, complete, residue-compatible coefficient data are reused,
removing the supplied global lift in this local patching input for Dubon
Theorem 2.6. The residual arithmetic representation and unramifiedness of the prescribed determinant at this auxiliary prime remain explicit inputs. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

private theorem matrix_continuous_of_topology_eq
    {A ι G : Type} [CommRing A] [Fintype ι] [DecidableEq ι] [Group G] [TopologicalSpace G]
    (t s : TopologicalSpace A) (ht : t = s) (ρ : G →* GeneralLinearGroup ι A)
    (hρ : letI : TopologicalSpace A := t; Continuous ρ) :
    letI : TopologicalSpace A := s; Continuous ρ := by
  subst s
  exact hρ

private theorem originalCoefficient_torus_fixed_augmentation_comparison
    {O A : Type} [CommRing O] [IsLocalRing O]
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A]
    [TopologicalSpace A] [IsAdicComplete (maximalIdeal A) A]
    (a b : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime] (hlevel : 0 < level)
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes) [NeZero p.val]
    (hgood : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    (hpb : (p.val : 𝓞 ℚ) ∣ b)
    (htop : (inferInstance : TopologicalSpace A) = (maximalIdeal A).adicTopology)
    (eO : ResidueField O ≃+* ZMod q) (e : ResidueField A ≃ₐ[O] ResidueField O)
    (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (τ : rationalArithmeticGaloisGroup b →ₜ* GeneralLinearGroup (Fin (degree + 1)) A)
    (hres : (GeneralLinearGroup.map (localCoefficientReduction e).toRingHom).comp τ.toMonoidHom = σ)
    (hcompat : ∀ g, GeneralLinearGroup.map eO.toRingHom
      (σ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g))
    (hdet : ∀ g ∈ rationalPrimeNormInertia p.val p.property,
      GeneralLinearGroup.det (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) = 1) :
    ∃ κ : RationalPrimeTameCoefficientQuotient p.val q →* (Fin degree → A)ˣ,
      (∀ d i, residue A ((κ d).val i) = 1) ∧
      auxiliaryCharacterAugmentationIdeal O (D := RationalPrimeTameCoefficientQuotient p.val q) κ =
        matrixRepresentationRelationIdeal
          (τ.toMonoidHom.comp (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom)
          (rationalPrimeNormInertia p.val p.property) := by
  let eA := e.toRingEquiv.trans eO
  have hτ := matrix_continuous_of_topology_eq _ _ htop τ.toMonoidHom τ.continuous
  letI : WithIdeal A := ⟨maximalIdeal A⟩
  have he : eA.toRingHom.comp (residue A) = eO.toRingHom.comp (localCoefficientReduction e).toRingHom := by
    ext x
    rfl
  have hred (g) : GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g) := by
    rw [he, GeneralLinearGroup.map_comp, MonoidHom.comp_apply]
    change GeneralLinearGroup.map eO.toRingHom
      (((GeneralLinearGroup.map (localCoefficientReduction e).toRingHom).comp τ.toMonoidHom)
        (rationalPrimeArithmeticRestriction b p.val p.property g)) = _
    rw [hres]
    exact hcompat g
  exact rationalArithmetic_torus_fixedDeterminant_augmentation_comparison O a b q degree level hlevel R p
    hgood hpb rfl eA τ.toMonoidHom hτ hred hdet

private theorem arithmeticUniversal_inertia_determinant
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (b : 𝓞 ℚ) (hb : b ≠ 0) (q degree : ℕ) [Fact q.Prime] (hqb : (q : 𝓞 ℚ) ∣ b)
    (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup b →* Oˣ) (p : Nat.Primes)
    (hδI : ∀ g ∈ rationalPrimeNormInertia p.val p.property,
      δ (rationalPrimeArithmeticRestriction b p.val p.property g) = 1) :
    ∀ g ∈ rationalPrimeNormInertia p.val p.property,
      GeneralLinearGroup.det (arithmeticFixedDeterminantRepresentation b hb q
        (Fact.out : q.Prime) hqb σ hσ δ (rationalPrimeArithmeticRestriction b p.val p.property g)) = 1 := by
  let A := ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) hqb σ hσ δ
  let f : Oˣ →* Aˣ := Units.map (algebraMap O A).toMonoidHom
  intro g hg
  exact (arithmeticFixedDeterminantRepresentation_det b hb q (Fact.out : q.Prime) hqb σ hσ δ _).trans
    ((congrArg f (hδI g hg)).trans f.map_one)

/-- The actual universal fixed-determinant arithmetic coefficients have
exactly degree scalar auxiliary parameters for rank degree+1 whose augmentation specializes exactly to
trivial original local inertia. No global lift or quotient comparison is
provided as a premise. -/
theorem arithmeticUniversal_torus_fixedDeterminant_augmentation_comparison
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a b : 𝓞 ℚ) (hb : b ≠ 0) (q degree level : ℕ) [Fact q.Prime]
    (hqb : (q : 𝓞 ℚ) ∣ b) (hlevel : 0 < level)
    (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup b →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes) [NeZero p.val]
    (hgood : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    (hpb : (p.val : 𝓞 ℚ) ∣ b)
    (hδI : ∀ g ∈ rationalPrimeNormInertia p.val p.property,
      δ (rationalPrimeArithmeticRestriction b p.val p.property g) = 1)
    (hcompat : ∀ g, GeneralLinearGroup.map eO.toRingHom
      (σ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g)) :
    let A := ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) hqb σ hσ δ
    letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ
    ∃ κ : RationalPrimeTameCoefficientQuotient p.val q →* (Fin degree → A)ˣ,
      (∀ d i, residue A ((κ d).val i) = 1) ∧
      auxiliaryCharacterAugmentationIdeal O (D := RationalPrimeTameCoefficientQuotient p.val q) κ =
        matrixRepresentationRelationIdeal
          ((arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σ hσ δ).toMonoidHom.comp
            (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom)
          (rationalPrimeNormInertia p.val p.property) := by
  let A := ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) hqb σ hσ δ
  letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ
  have hlocal := arithmeticFixedDeterminantRing_localData b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ
  letI : IsNoetherianRing A := hlocal.1
  letI : IsAdicComplete (maximalIdeal A) A := hlocal.2.1
  exact originalCoefficient_torus_fixed_augmentation_comparison a b q degree level hlevel R p hgood hpb
    hlocal.2.2 eO
    (arithmeticFixedDeterminantResidueEquiv b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ) σ
    (arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σ hσ δ)
    (arithmeticFixedDeterminantRepresentation_residue b hb q (Fact.out : q.Prime) hqb σ hσ δ hδ) hcompat
    (arithmeticUniversal_inertia_determinant b hb q degree hqb σ hσ δ p hδI)

end
end Dubon2026
