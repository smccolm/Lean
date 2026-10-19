import Dubon2026.ArithmeticUniversalAuxiliaryQuotient
import Dubon2026.ArithmeticUniversalOriginalSupportFamily
import Dubon2026.AuxiliaryFamilyAugmentationSpecialization

/-! The actual universal auxiliary character augmentation quotient is
the literal universal inertia quotient. The algebra equivalence fixes
every original coefficient class, so it retains the universal matrix
values required for the original-support deformation comparison. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

/-- The constructed universal character family specializes its
actual augmentation quotient to the simultaneous original inertia
quotient, preserving every original coefficient class. -/
theorem arithmeticUniversal_original_support_augmentation_quotient
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
    let R := ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) hqb σb hσb δb
    letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb
    let τ := (arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σb hσb δb).toMonoidHom
    Nonempty (AuxiliaryFamilyAugmentationSpecialization O (ι := Fin degree) (R := R)
      (fun p : Q => RationalPrimeTameCoefficientQuotient p.val.val q)
      (arithmeticAuxiliaryInertiaRelationIdeal b Q τ)) := by
  let π := rationalArithmeticSupportRestriction a b hab
  let σb := σ.comp π.toMonoidHom
  let hσb : Continuous σb := hσ.comp π.continuous
  let δb := δ.comp π.toMonoidHom
  let hδb : ∀ g, GeneralLinearGroup.det (σb g) =
      Units.map (algebraMap O (ResidueField O)) (δb g) := fun g => hδ (π g)
  letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb
  exact auxiliaryFamilyAugmentationSpecialization_of_exists O _ _
    (arithmeticUniversal_original_support_family_augmentation
      a b hab hb q degree level hqb hlevel eO σ hσ δ hδ Q hgood hpb)

end
end Dubon2026
