import Dubon2026.ArithmeticTorusCyclotomicDescent
import Dubon2026.ArtinianCyclotomicPrimaryDescent

/-! The actual selected auxiliary prime and global Artinian deformation
produce the unique inertia action through the fixed coefficient-primary
tame quotient. This is the literal finite group action to be represented
by the local deformation ring, on the Dubon Theorem 2.6 patching chain. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The same selected prime and actual global Artinian lift supply the
unique action of the fixed maximal coefficient-prime quotient on inertia. -/
theorem rationalArithmetic_torus_global_primary_descent
    (a b : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime] (hlevel : 0 < level)
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes) [NeZero p.val]
    (hgood : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    (hpb : (p.val : 𝓞 ℚ) ∣ b)
    {A : Type} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [TopologicalSpace A] [DiscreteTopology A]
    (eA : ResidueField A ≃+* ZMod q)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) A)
    (hτ : Continuous τ)
    (hred : ∀ g, GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g)) :
    ∃! η : RationalPrimeTameCoefficientQuotient p.val q →* GeneralLinearGroup (Fin (degree + 1)) A,
      ∀ g ∈ rationalPrimeNormInertia p.val p.property,
        η (QuotientGroup.mk' (rationalPrimeTameCoefficientKernel p.val q)
          (rationalPrimeCyclotomicCharacter p.val p.property p.val g)) =
            τ (rationalPrimeArithmeticRestriction b p.val p.property g) := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  letI : CharP (ResidueField A) q := charP_of_injective_ringHom (f := eA.symm.toRingHom) eA.symm.injective q
  have hm : p.val ≡ 1 [MOD q] := hgood.2.1.of_dvd (dvd_pow_self q (Nat.ne_of_gt hlevel))
  have hpone : (p.val : ZMod q) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff p.val 1 q).mpr hm
  have hp2 : p.val ≠ 2 := by
    intro h
    have he : (1 : ZMod q) + 1 = 1 + 0 := by simpa only [h, Nat.cast_ofNat, one_add_one_eq_two, add_zero] using hpone
    exact one_ne_zero (add_left_cancel he)
  obtain ⟨θ, hθ, hθuniq⟩ := rationalArithmetic_torus_global_cyclotomic_descent
    a b q degree level hlevel R p hgood hpb eA τ hτ hred
  have hiner := rationalArithmetic_regular_auxiliary_inertia a q level R p (hgood.regular a q degree level R p)
  have hres : ∀ u, GeneralLinearGroup.map (residue A) (θ u) = 1 := by
    intro u
    obtain ⟨g, hg, rfl⟩ := rationalPrimeCyclotomicCharacter_inertia_surjective p.val p.property hp2 u
    rw [hθ g hg]
    have hz := (hred g).trans (hiner hg)
    apply Units.ext
    ext i j
    apply eA.injective
    have hz' := congrArg (fun X : GeneralLinearGroup (Fin (degree + 1)) (ZMod q) => X.val i j) hz
    simpa [Matrix.one_apply] using hz'
  obtain ⟨η, hη, hηuniq⟩ := artinian_cyclotomic_unique_primary_factor p.val q θ hres
  refine ⟨η, ?_, ?_⟩
  · intro g hg
    exact (DFunLike.congr_fun hη _).trans (hθ g hg)
  · intro η' hη'
    apply hηuniq η'
    exact hθuniq (η'.comp (QuotientGroup.mk' (rationalPrimeTameCoefficientKernel p.val q))) hη'

end
end Dubon2026
