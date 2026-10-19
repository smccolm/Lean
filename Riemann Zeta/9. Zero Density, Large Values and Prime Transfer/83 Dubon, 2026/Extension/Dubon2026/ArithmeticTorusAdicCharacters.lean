import Dubon2026.ArithmeticTorusAdicCommutativity
import Dubon2026.RegularResidueCommutingCharacters

/-! Whole local character decomposition over the original complete
Noetherian coefficient ring at the very same selected auxiliary prime.
This supplies scalar parameters for the actual deformation-ring group
algebra map on the Dubon Theorem 2.6 arithmetic patching chain. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The actual selected prime supplies one diagonal basis and the whole
local characters over complete Noetherian adic coefficients, with the
precise residual Frobenius weights. No character or basis is assumed. -/
theorem rationalArithmetic_torus_global_adic_characters
    (a b : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime] (hlevel : 0 < level)
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes)
    (hgood : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [WithIdeal A]
    [IsAdicComplete (maximalIdeal A) A]
    (hA : (WithIdeal.i : Ideal A) = maximalIdeal A)
    (eA : ResidueField A ≃+* ZMod q)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) A)
    (hτ : Continuous τ)
    (hred : ∀ g, GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g)) :
    ∃ (φ : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property))
      (u : (ZMod q)ˣ) (W : GeneralLinearGroup (Fin (degree + 1)) A)
      (χ : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property) →*
        (Fin (degree + 1) → A)ˣ),
      (∀ x : ResidueField (algebraicLocalIntegerRing (rationalPrimeLocalClosure p.val p.property)),
        φ • x = x ^ p.val) ∧ 2 * degree < orderOf u ∧
      (∀ g, diagonal (χ g).val =
        (MulAut.conj W (τ (rationalPrimeArithmeticRestriction b p.val p.property g))).val) ∧
      ∀ i, eA (residue A ((χ φ).val i)) =
        (u : ZMod q) ^ i.val * (↑u⁻¹ : ZMod q) ^ (degree - i.val) := by
  obtain ⟨φ, hφ⟩ := rationalPrimeOriginalNorm_exists_frobenius p.val p.property
  obtain ⟨u, hu, hconj⟩ := hgood.original_frobenius_conjugate a q degree level R p φ hφ
  let ρ := τ.comp (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom
  let α (i : Fin (degree + 1)) := (u : ZMod q) ^ i.val * (↑u⁻¹ : ZMod q) ^ (degree - i.val)
  have hconj' : IsConj (GeneralLinearGroup.map (eA.toRingHom.comp (residue A)) (ρ φ))
      (homogeneousSymmetricGL degree (SpecialLinearGroup.toGL (ringSL2UnitDiagonal u))) := by
    change IsConj (GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property φ))) _
    rw [hred]
    exact hconj
  obtain ⟨V, hV⟩ := regularResidue_lift_conjugate_basis eA (ρ φ)
    _ α (homogeneousSymmetricGL_unitDiagonal u degree) hconj'
  let σ := (MulAut.conj V).toMonoidHom.comp ρ
  have hcomm (g) : Commute (σ φ) (σ g) :=
    (rationalArithmetic_torus_global_adic_commute a b q degree level hlevel R p hgood
      hA eA τ hτ hred φ g).map (MulAut.conj V).toMonoidHom
  have hα := eA.symm.injective.comp (symmetric_unit_weights_injective u degree hu)
  obtain ⟨U, χ, _, hχ, hχφ⟩ := regularResidue_commuting_character_decomposition
    σ φ (fun i => eA.symm (α i)) hV hα hcomm
  refine ⟨φ, u, U⁻¹ * V, χ, hφ, hu, ?_, ?_⟩
  · intro g
    rw [hχ]
    simp only [σ, ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      _root_.mul_inv_rev, inv_inv, mul_assoc]
    rfl
  · intro i
    rw [hχφ, RingEquiv.apply_symm_apply]

end
end Dubon2026
