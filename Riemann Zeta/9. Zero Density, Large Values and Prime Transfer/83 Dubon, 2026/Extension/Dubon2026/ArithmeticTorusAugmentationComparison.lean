import Dubon2026.ArithmeticTorusAdicPrimaryCharacters
import Dubon2026.InertiaCharacterAugmentationComparison

/-! The actual selected-prime lift supplies the scalar group-algebra
parameters whose literal augmentation specialization imposes original
local unramifiedness. No diagonal presentation or quotient comparison is
assumed. This closes that local algebraic dependency on the arithmetic
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
scalar inertia parameters. Their augmentation ideal is exactly the actual
local inertia matrix relation ideal, and all parameters reduce to one. -/
theorem rationalArithmetic_torus_global_augmentation_comparison
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
    (hred : ∀ g, GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g)) :
    ∃ κ : RationalPrimeTameCoefficientQuotient p.val q →* (Fin (degree + 1) → A)ˣ,
      (∀ d i, residue A ((κ d).val i) = 1) ∧
      auxiliaryCharacterAugmentationIdeal O (D := RationalPrimeTameCoefficientQuotient p.val q) κ =
        matrixRepresentationRelationIdeal
          (τ.comp (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom)
          (rationalPrimeNormInertia p.val p.property) := by
  obtain ⟨_, _, W, χ, κ, _, _, hχ, _, hκ, hres⟩ :=
    rationalArithmetic_torus_global_adic_primary_characters
      a b q degree level hlevel R p hgood hpb hA eA τ hτ hred
  let π := (QuotientGroup.mk' (rationalPrimeTameCoefficientKernel p.val q)).comp
    (rationalPrimeCyclotomicCharacter p.val p.property p.val).toMonoidHom
  have hp2 : p.val ≠ 2 := by
    have hm := hgood.2.1.of_dvd (dvd_pow_self q (Nat.ne_of_gt hlevel))
    have hpone : (p.val : ZMod q) = 1 := by
      simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff p.val 1 q).mpr hm
    intro h
    have he : (1 : ZMod q) + 1 = 1 + 0 := by simpa only [h, Nat.cast_ofNat, one_add_one_eq_two, add_zero] using hpone
    exact one_ne_zero (add_left_cancel he)
  have hs (d : RationalPrimeTameCoefficientQuotient p.val q) :
      ∃ g ∈ rationalPrimeNormInertia p.val p.property, π g = d := by
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (rationalPrimeTameCoefficientKernel p.val q) d
    obtain ⟨g, hg, hv⟩ := rationalPrimeCyclotomicCharacter_inertia_surjective p.val p.property hp2 v
    exact ⟨g, hg, congrArg (QuotientGroup.mk' _) hv⟩
  refine ⟨κ, hres, ?_⟩
  apply inertiaCharacter_augmentationIdeal_eq O _ _ π W κ ?_ hs
  intro g hg
  rw [show κ (π g) = χ g from hκ g hg]
  exact hχ g

end
end Dubon2026
