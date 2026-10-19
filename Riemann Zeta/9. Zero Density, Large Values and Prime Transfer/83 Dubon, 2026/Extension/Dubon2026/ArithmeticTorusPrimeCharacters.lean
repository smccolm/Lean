import Dubon2026.ArithmeticTorusAuxiliaryPrime
import Dubon2026.ResidualConjugateBasisLift
import Dubon2026.RationalPrimeTameCharacters

/-! Whole local character decomposition at the very same selected auxiliary
prime. The source obligation is DUB-17, Theorem 2.6, through the ramified local
deformation rings required by arithmetic patching and higher symmetric-power
continuation. The finite local factor and its actual residual compatibility
remain displayed inputs; local residual unramifiedness and splitting are derived.
-/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- Every Artinian local lift at a selected split auxiliary prime is a direct
sum of actual characters after a constructed coefficient basis change. The
selected prime itself supplies residual unramifiedness, the arithmetic
Frobenius, distinct residual weights and the tame exponent equation. -/
theorem rationalArithmetic_torus_prime_character_decomposition
    (a : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime] (hlevel : 0 < level)
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes) (hgood : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    {F A : Type} [Field F] [NumberField F]
    [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (eA : ResidueField A ≃+* ZMod q)
    (e : F →+* rationalPrimeLocalClosure p.val p.property)
    (r : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property) →*
      Gal(F/ℚ)) (he : ∀ g x, e (r g x) = g (e x))
    (ρ : (Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property) ⧸
      r.ker) →* GeneralLinearGroup (Fin (degree + 1)) A)
    (hred : ∀ g, GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (ρ (QuotientGroup.mk' r.ker g)) = R (rationalPrimeArithmeticRestriction a p.val p.property g)) :
    ∃ (φ : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property))
      (u : (ZMod q)ˣ)
      (t : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property) ⧸ r.ker)
      (W : GeneralLinearGroup (Fin (degree + 1)) A)
      (χ : (Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property) ⧸
        r.ker) →* (Fin (degree + 1) → A)ˣ),
      (∀ x : ResidueField (algebraicLocalIntegerRing (rationalPrimeLocalClosure p.val p.property)),
        φ • x = x ^ p.val) ∧ 2 * degree < orderOf u ∧
      t ∈ (rationalPrimeNormInertia p.val p.property).map (QuotientGroup.mk' r.ker) ∧
      ((rationalPrimeNormInertia p.val p.property).map (QuotientGroup.mk' r.ker)).map ρ =
        Subgroup.zpowers (ρ t) ∧
      (∀ g, diagonal (χ g).val = (MulAut.conj W (ρ g)).val) ∧
      (∀ i, eA (residue A ((χ (QuotientGroup.mk' r.ker φ)).val i)) =
        (u : ZMod q) ^ i.val * (↑u⁻¹ : ZMod q) ^ (degree - i.val)) ∧
      (∀ i, residue A ((χ t).val i) = 1) ∧
      ∀ i, ((χ t).val i) ^ p.val = (χ t).val i := by
  letI : CharP (ResidueField A) q :=
    charP_of_injective_ringHom (f := eA.symm.toRingHom) eA.symm.injective q
  have hm : p.val ≡ 1 [MOD q] := hgood.2.1.of_dvd (dvd_pow_self q (Nat.ne_of_gt hlevel))
  have hponeq : (p.val : ZMod q) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff p.val 1 q).mpr hm
  have hpq : p.val ≠ q := by
    intro h
    simp only [h, ZMod.natCast_self, zero_ne_one] at hponeq
  have hpone : (p.val : ResidueField A) = 1 := by
    apply eA.injective
    simpa only [map_natCast, map_one] using hponeq
  have hiner := rationalArithmetic_regular_auxiliary_inertia a q level R p
    (hgood.regular a q degree level R p)
  have hres : ∀ g ∈ (rationalPrimeNormInertia p.val p.property).map (QuotientGroup.mk' r.ker),
      GeneralLinearGroup.map (residue A) (ρ g) = 1 := by
    intro g hg
    obtain ⟨δ, hδ, rfl⟩ := hg
    have hz := (hred δ).trans (hiner hδ)
    apply Units.ext
    ext i j
    apply eA.injective
    have hz' := congrArg (fun X : GeneralLinearGroup (Fin (degree + 1)) (ZMod q) => X.val i j) hz
    simpa [Matrix.one_apply] using hz'
  obtain ⟨φ, hφ⟩ := rationalPrimeOriginalNorm_exists_frobenius p.val p.property
  obtain ⟨u, hu, hconj⟩ := hgood.original_frobenius_conjugate a q degree level R p φ hφ
  let α (i : Fin (degree + 1)) := (u : ZMod q) ^ i.val * (↑u⁻¹ : ZMod q) ^ (degree - i.val)
  have hconj' : IsConj (GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (ρ (QuotientGroup.mk' r.ker φ)))
      (homogeneousSymmetricGL degree (SpecialLinearGroup.toGL (ringSL2UnitDiagonal u))) := by
    rw [hred]
    exact hconj
  obtain ⟨V, hV⟩ := regularResidue_lift_conjugate_basis eA (ρ (QuotientGroup.mk' r.ker φ))
    _ α (homogeneousSymmetricGL_unitDiagonal u degree) hconj'
  let σ := (MulAut.conj V).toMonoidHom.comp ρ
  have hσres : ∀ g ∈ (rationalPrimeNormInertia p.val p.property).map (QuotientGroup.mk' r.ker),
      GeneralLinearGroup.map (residue A) (σ g) = 1 := by
    intro g hg
    simp only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv, hres g hg, mul_one, mul_inv_cancel]
  have hα := eA.symm.injective.comp (symmetric_unit_weights_injective u degree hu)
  obtain ⟨t, U, χ, ht, himage, _, hχ, hχφ, hχt, hχtp⟩ :=
    rationalPrime_artinian_tame_character_decomposition p.val q p.property (Fact.out : q.Prime)
      hpq hpone e r he φ hφ σ hσres (fun i => eA.symm (α i)) hα hV
  have himage' : ((rationalPrimeNormInertia p.val p.property).map (QuotientGroup.mk' r.ker)).map ρ =
      Subgroup.zpowers (ρ t) := by
    apply Subgroup.map_injective (f := (MulAut.conj V).toMonoidHom) (MulAut.conj V).injective
    rw [Subgroup.map_map, MonoidHom.map_zpowers]
    exact himage
  refine ⟨φ, u, t, U⁻¹ * V, χ, hφ, hu, ht, himage', ?_, ?_, hχt, hχtp⟩
  · intro g
    rw [hχ]
    simp only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      _root_.mul_inv_rev, inv_inv, mul_assoc]
  · intro i
    rw [hχφ, RingEquiv.apply_symm_apply]

end
end Dubon2026
