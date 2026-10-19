import Dubon2026.ArithmeticTorusPrimaryDescent

/-! The fixed coefficient-primary quotient acts by actual unit-valued
characters in the same diagonal basis as the whole local representation.
Their residual values and the selected Frobenius weights are retained.
These are the concrete parameters to be represented by the auxiliary local
deformation ring on the Dubon Theorem 2.6 arithmetic patching chain. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The actual selected prime and global lift produce whole local
characters and characters of the fixed tame coefficient quotient in one
basis, with the exact residual Frobenius weights and trivial residual
quotient characters. No local character or factorization is supplied. -/
theorem rationalArithmetic_torus_global_primary_characters
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
    ∃ (φ : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property))
      (u : (ZMod q)ˣ) (W : GeneralLinearGroup (Fin (degree + 1)) A)
      (χ : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property) →*
        (Fin (degree + 1) → A)ˣ)
      (κ : RationalPrimeTameCoefficientQuotient p.val q →* (Fin (degree + 1) → A)ˣ),
      (∀ x : ResidueField (algebraicLocalIntegerRing (rationalPrimeLocalClosure p.val p.property)),
        φ • x = x ^ p.val) ∧ 2 * degree < orderOf u ∧
      (∀ g, diagonal (χ g).val =
        (MulAut.conj W (τ (rationalPrimeArithmeticRestriction b p.val p.property g))).val) ∧
      (∀ i, eA (residue A ((χ φ).val i)) =
        (u : ZMod q) ^ i.val * (↑u⁻¹ : ZMod q) ^ (degree - i.val)) ∧
      (∀ g ∈ rationalPrimeNormInertia p.val p.property,
        κ (QuotientGroup.mk' (rationalPrimeTameCoefficientKernel p.val q)
          (rationalPrimeCyclotomicCharacter p.val p.property p.val g)) = χ g) ∧
      ∀ d i, residue A ((κ d).val i) = 1 := by
  obtain ⟨φ, δ, u, W, χ, hφ, hu, _, _, hχ, hχφ, _, _⟩ :=
    rationalArithmetic_torus_global_lift_characters a b q degree level hlevel R p hgood eA τ hτ hred
  obtain ⟨η, hη, _⟩ := rationalArithmetic_torus_global_primary_descent
    a b q degree level hlevel R p hgood hpb eA τ hτ hred
  let π := (QuotientGroup.mk' (rationalPrimeTameCoefficientKernel p.val q)).comp
    (rationalPrimeCyclotomicCharacter p.val p.property p.val).toMonoidHom
  have hp2 : p.val ≠ 2 := by
    have hm := hgood.2.1.of_dvd (dvd_pow_self q (Nat.ne_of_gt hlevel))
    have hpone : (p.val : ZMod q) = 1 := by
      simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff p.val 1 q).mpr hm
    intro h
    have he : (1 : ZMod q) + 1 = 1 + 0 := by simpa only [h, Nat.cast_ofNat, one_add_one_eq_two, add_zero] using hpone
    exact one_ne_zero (add_left_cancel he)
  have hsurj (d : RationalPrimeTameCoefficientQuotient p.val q) :
      ∃ g ∈ rationalPrimeNormInertia p.val p.property, π g = d := by
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (rationalPrimeTameCoefficientKernel p.val q) d
    obtain ⟨g, hg, hv⟩ := rationalPrimeCyclotomicCharacter_inertia_surjective p.val p.property hp2 v
    exact ⟨g, hg, congrArg (QuotientGroup.mk' _) hv⟩
  let σ := (MulAut.conj W).toMonoidHom.comp η
  have hσ (d) : (σ d).val = diagonal (fun i => (σ d).val i i) := by
    obtain ⟨g, hg, rfl⟩ := hsurj d
    have he : (σ (π g)).val = diagonal (χ g).val := by
      change (MulAut.conj W (η (π g))).val = _
      rw [show η (π g) = _ from hη g hg]
      exact (hχ g).symm
    rw [he]
    simp only [diagonal_apply_eq]
  obtain ⟨κ, hκ⟩ := diagonal_representation_exists_characters σ hσ
  have hfactor (g) (hg : g ∈ rationalPrimeNormInertia p.val p.property) : κ (π g) = χ g := by
    apply Units.ext
    apply diagonal_injective
    rw [hκ]
    change (MulAut.conj W (η (π g))).val = diagonal (χ g).val
    rw [show η (π g) = _ from hη g hg]
    exact (hχ g).symm
  refine ⟨φ, u, W, χ, κ, hφ, hu, hχ, hχφ, hfactor, ?_⟩
  intro d i
  obtain ⟨g, hg, rfl⟩ := hsurj d
  rw [hfactor g hg]
  have hiner := rationalArithmetic_regular_auxiliary_inertia a q level R p (hgood.regular a q degree level R p)
  have hτres : GeneralLinearGroup.map (residue A)
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) = 1 := by
    have hz := (hred g).trans (hiner hg)
    apply Units.ext
    ext j k
    apply eA.injective
    have hz' := congrArg (fun X : GeneralLinearGroup (Fin (degree + 1)) (ZMod q) => X.val j k) hz
    simpa [Matrix.one_apply] using hz'
  let D := Units.map (diagonalRingHom (Fin (degree + 1)) A).toMonoidHom
  have he : D (χ g) = MulAut.conj W (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) :=
    Units.ext (hχ g)
  have hz : GeneralLinearGroup.map (residue A) (D (χ g)) = 1 := by
    rw [he]
    simp only [MulAut.conj_apply, map_mul, map_inv, hτres, mul_one, mul_inv_cancel]
  have hi := congrArg (fun X : GeneralLinearGroup (Fin (degree + 1)) (ResidueField A) => X.val i i) hz
  simpa [D] using hi

end
end Dubon2026
