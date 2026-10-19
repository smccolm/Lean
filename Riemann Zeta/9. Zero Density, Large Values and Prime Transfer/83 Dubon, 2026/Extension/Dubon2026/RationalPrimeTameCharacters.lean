import Dubon2026.RationalPrimeTameStrictDiagonalization
import Dubon2026.AlgebraicLocalFiniteInertiaGeneration
import Dubon2026.DiagonalCharacterFactorization

/-! # Character decomposition of the whole original auxiliary local lift

The native finite-quotient Frobenius generation theorem and the proved tame
matrix classification construct actual characters of the original finite
local Galois quotient. This is a local deformation dependency of the
arithmetic patching route to Dubon Theorem 2.6.
-/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing

attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
  algebraicLocalIntegerBaseAlgebra
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The whole actual residual-unramified auxiliary local deformation splits
into unit-valued characters after a constructed strict change of basis.
The original tame generator and its coefficient equations are retained. -/
theorem rationalPrime_artinian_tame_character_decomposition
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {F A ι : Type} [Field F] [NumberField F]
    [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [Fintype ι] [DecidableEq ι] [CharP (ResidueField A) q]
    (hpone : (p : ResidueField A) = 1)
    (e : F →+* rationalPrimeLocalClosure p hp)
    (r : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* Gal(F/ℚ))
    (he : ∀ g x, e (r g x) = g (e x))
    (φ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hφ : ∀ x : ResidueField (algebraicLocalIntegerRing
      (rationalPrimeLocalClosure p hp)), φ • x = x ^ p)
    (ρ : (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker) →*
      GeneralLinearGroup ι A)
    (hres : ∀ g ∈ (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker),
      GeneralLinearGroup.map (residue A) (ρ g) = 1)
    (α : ι → ResidueField A) (hα : Function.Injective α)
    (hF : (ρ (QuotientGroup.mk' r.ker φ)).val.map (residue A) = diagonal α) :
    ∃ (t : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker)
      (U : GeneralLinearGroup ι A)
      (χ : (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker) →*
        (ι → A)ˣ),
      t ∈ (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker) ∧
      ((rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker)).map ρ =
        Subgroup.zpowers (ρ t) ∧
      GeneralLinearGroup.map (residue A) U = 1 ∧
      (∀ g, diagonal (χ g).val = (MulAut.conj U⁻¹ (ρ g)).val) ∧
      (∀ i, residue A ((χ (QuotientGroup.mk' r.ker φ)).val i) = α i) ∧
      (∀ i, residue A ((χ t).val i) = 1) ∧
      ∀ i, ((χ t).val i) ^ p = (χ t).val i := by
  let K := rationalPrimeLocalField p hp
  let L := rationalPrimeLocalClosure p hp
  letI : Finite (ResidueField (algebraicLocalIntegerRing K)) := normLocal_residue_finite K
  have hf (x : algebraicLocalIntegerRing L) :
      residue _ (φ • x) = (residue _ x) ^ Nat.card (ResidueField (algebraicLocalIntegerRing K)) := by
    rw [rationalPrimeOriginalNorm_residue_card p hp, ResidueField.residue_smul]
    exact hφ _
  have hgen := algebraicLocal_finite_inertia_frobenius_generate e r he φ hf
  obtain ⟨t, U, l, b, ht, himage, hU, hdiagF, hdiagT, hl, hb, _, _, hbp⟩ :=
    rationalPrime_artinian_tame_strict_diagonalization p q hp hq hpq hpone e r he φ hφ ρ hres α hα hF
  let c := (MulAut.conj U⁻¹).toMonoidHom
  let σ := c.comp ρ
  have himage' : ((rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker)).map σ =
      Subgroup.zpowers (σ t) := by
    rw [show σ = c.comp ρ from rfl, ← Subgroup.map_map, himage, MonoidHom.map_zpowers]
    rfl
  have hφdiag : (σ (QuotientGroup.mk' r.ker φ)).val =
      diagonal (fun i => (σ (QuotientGroup.mk' r.ker φ)).val i i) := by
    change (MulAut.conj U⁻¹ (ρ (QuotientGroup.mk' r.ker φ))).val = _
    simp only [σ, c, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hdiagF, diagonal_apply_eq]
  have htdiag : (σ t).val = diagonal (fun i => (σ t).val i i) := by
    change (MulAut.conj U⁻¹ (ρ t)).val = _
    simp only [σ, c, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hdiagT, diagonal_apply_eq]
  have hall := inertia_frobenius_diagonal_image
    ((rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker))
    (QuotientGroup.mk' r.ker φ) t hgen σ himage' hφdiag htdiag
  obtain ⟨χ, hχ⟩ := diagonal_representation_exists_characters σ hall
  have hχφ (i : ι) : (χ (QuotientGroup.mk' r.ker φ)).val i = l i := by
    have h := (hχ (QuotientGroup.mk' r.ker φ)).trans hdiagF
    simpa only [diagonal_apply_eq] using congrArg (fun M : Matrix ι ι A => M i i) h
  have hχt (i : ι) : (χ t).val i = b i := by
    have h := (hχ t).trans hdiagT
    simpa only [diagonal_apply_eq] using congrArg (fun M : Matrix ι ι A => M i i) h
  refine ⟨t, U, χ, ht, himage, hU, hχ, ?_, ?_, ?_⟩
  · intro i; rw [hχφ]; exact hl i
  · intro i; rw [hχt]; exact hb i
  · intro i; rw [hχt]; exact hbp i

end
end Dubon2026
