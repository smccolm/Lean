import Dubon2026.ArtinianResidualMatrixPGroup
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-! Existing native Artinian residual-kernel theory kills the residue-prime
wild subgroup in every residual-unramified matrix lift away from the coefficient
prime. Its inertia image is cyclic and satisfies the tame Frobenius relation.
These are the matrix constraints for the ramified auxiliary deformation rings
needed by arithmetic patching and Dubon Theorem 2.6. -/

namespace Dubon2026

open Matrix

theorem coprime_pGroup_hom_eq_one
    {G H : Type*} [Group G] [Group H] (p q : ℕ) (hpq : p.Coprime q)
    (hG : IsPGroup p G) (hH : IsPGroup q H) (f : G →* H) (g : G) : f g = 1 := by
  obtain ⟨a, ha⟩ := hG g
  obtain ⟨b, hb⟩ := hH (f g)
  have hfa : f g ^ (p ^ a) = 1 := by rw [← map_pow, ha, map_one]
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (hpq.pow a b)
    (orderOf_dvd_of_pow_eq_one hfa) (orderOf_dvd_of_pow_eq_one hb)

theorem artinian_residual_unramified_kills_wild
    {G A ι : Type*} [Group G] [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [Fintype ι] [DecidableEq ι]
    (p q : ℕ) (hq : q.Prime) (hpq : p.Coprime q)
    [CharP (IsLocalRing.ResidueField A) q]
    (I W : Subgroup G) (hW : W ≤ I) (hWp : IsPGroup p W)
    (ρ : G →* GeneralLinearGroup ι A)
    (hres : ∀ g ∈ I, GeneralLinearGroup.map (IsLocalRing.residue A) (ρ g) = 1) :
    W ≤ ρ.ker := by
  let f : W →* (GeneralLinearGroup.map (n := ι) (IsLocalRing.residue A)).ker :=
    { toFun := fun g => ⟨ρ g, hres g (hW g.property)⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun a b => Subtype.ext (map_mul ρ (a : G) (b : G)) }
  intro g hg
  have h := coprime_pGroup_hom_eq_one p q hpq hWp
    (artinianResidualMatrixKernel_isPGroup (ι := ι) (A := A) q hq) f ⟨g, hg⟩
  exact congrArg Subtype.val h

theorem tame_inertia_image_and_frobenius
    {G H : Type*} [Group G] [Group H] (I W : Subgroup G) (φ t : G) (p : ℕ)
    (hgen : I = W ⊔ Subgroup.zpowers t)
    (hrel : φ * t * φ⁻¹ * (t ^ p)⁻¹ ∈ W)
    (ρ : G →* H) (hW : W ≤ ρ.ker) :
    I.map ρ = Subgroup.zpowers (ρ t) ∧ ρ φ * ρ t * (ρ φ)⁻¹ = ρ t ^ p := by
  constructor
  · rw [hgen, Subgroup.map_sup, (Subgroup.map_eq_bot_iff W).mpr hW,
      bot_sup_eq, ρ.map_zpowers]
  · have h := hW hrel
    change ρ (φ * t * φ⁻¹ * (t ^ p)⁻¹) = 1 at h
    simpa only [map_mul, map_inv, map_pow, mul_inv_eq_one] using h

end Dubon2026
