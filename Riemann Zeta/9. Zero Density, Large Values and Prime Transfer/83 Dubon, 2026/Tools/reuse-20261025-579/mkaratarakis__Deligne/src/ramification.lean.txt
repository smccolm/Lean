/-
Copyright (c) 2023 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

import ring_theory.ideal.local_ring
import ring_theory.valuation.valuation_subring
import number_theory.number_field.basic
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.valuation.ramification_group

namespace local_ring

variables {A : Type*} {B : Type*} [comm_ring B] [comm_ring A]
  [local_ring A] [local_ring B] [algebra A B] [is_local_ring_hom (algebra_map A B)]

instance (e : B ≃+* B) : is_local_ring_hom (e.to_ring_hom) := {
  map_nonunit := begin
  rintros b  ⟨u, hu⟩,
  have huinv : u * u⁻¹ = 1,
    { simp only [mul_right_inv], },
  unfold is_unit,
  change ∃ v, _,
  let v := units.map((e.symm).to_ring_hom.to_monoid_hom) u,
  use v,
  change e.symm(u) = b,
  change (u : B) = e b at hu,
  rw hu,
  simp only [ring_equiv.symm_apply_apply],
end }

/- -/
noncomputable instance general_algebra_map : 
  algebra (local_ring.residue_field A) (local_ring.residue_field B) :=
ring_hom.to_algebra (local_ring.residue_field.map (algebra_map A B))

/-- The group homomorphism from the Galois group to the Galois group of residue fields. -/
def algebra_equiv_to_residue_equiv :
(B ≃ₐ[A] B) →* ((local_ring.residue_field B) ≃ₐ[local_ring.residue_field A] (local_ring.residue_field B)) :=
{ to_fun := λ x, 
  { to_fun := local_ring.residue_field.map (x.to_ring_equiv.to_ring_hom),
    inv_fun := local_ring.residue_field.map (x.symm.to_ring_equiv.to_ring_hom),
    left_inv := λ y, begin
      simp only [alg_equiv.to_ring_equiv_eq_coe, alg_equiv.symm_to_ring_equiv, residue_field.map_map,
      ring_equiv.symm_to_ring_hom_comp_to_ring_hom, residue_field.map_id, ring_hom.id_apply],
      end,
    right_inv := λ y, begin
      simp only [alg_equiv.to_ring_equiv_eq_coe, alg_equiv.symm_to_ring_equiv, residue_field.map_map,
      ring_equiv.to_ring_hom_comp_symm_to_ring_hom, residue_field.map_id, ring_hom.id_apply],
      end,
    map_mul' := λ x y, begin
      simp only [map_mul],
      end,
    map_add' := λ x y, begin
      simp only [map_add], 
      end,
    commutes' := begin
      have hx := x.commutes,
      suffices : (residue_field.map x.to_ring_equiv.to_ring_hom).comp (algebra_map (residue_field A) (residue_field B)) = algebra_map (residue_field A) (residue_field B),
      rwa fun_like.ext_iff at this,
      have hres : function.surjective (residue A), {
      exact (ideal.quotient.mk (maximal_ideal A)).is_surjective,
      },
      rw ← ring_hom.cancel_right hres,
      rw ring_hom.comp_assoc,
      change _ = (residue_field.map _).comp _,
      rw residue_field.map_comp_residue,
      change (residue_field.map x.to_ring_equiv.to_ring_hom).comp ((residue_field.map _).comp _) = _,
      rw residue_field.map_comp_residue,
      rw ← ring_hom.comp_assoc,
      rw residue_field.map_comp_residue,
      ext r,
      simp only [alg_equiv.to_ring_equiv_eq_coe, ring_hom.coe_comp, function.comp_app],
      congr',
      exact hx r,
      end, },
  map_one' := begin
    ext,
    simp only [alg_equiv.to_ring_equiv_eq_coe, alg_equiv.coe_mk, alg_equiv.one_apply],
    have hid := local_ring.residue_field.map_id_apply a,
    apply hid,
    end,
  map_mul' := λ x y,
    begin
    ext,
    simp only [alg_equiv.to_ring_equiv_eq_coe, residue_field.map_map, alg_equiv.coe_mk, alg_equiv.mul_apply],
    refl,
    end }

end local_ring

namespace valuation_subring

variables {K L : Type*} [field K] [field L]

/-- The map from the pullback of a valuation subring A to A along a ring homomorphism K →+* L -/
def ring_hom.valuation_subring_comap (A : valuation_subring L) (f : K →+* L):
   (comap A f) →+* A :=
{ to_fun := λ x, ⟨f x.1, x.2⟩,
  map_one' := subtype.eq f.map_one,
  map_mul' := λ x y, subtype.eq (f.map_mul x y),
  map_add' := λ x y, subtype.eq (f.map_add x y),
  map_zero' := subtype.eq f.map_zero, }

/-- The map from the pullback of a valuation subring A to A along a ring homomorphism K →+* L, is local -/
instance valuation_subring_comap_local (A : valuation_subring L) (f : K →+* L) :
  (is_local_ring_hom (ring_hom.valuation_subring_comap A f))  :=
{ map_nonunit :=
  begin
    rintros ⟨a, ha⟩ ⟨y, hy : (y : ↥A) = ⟨f a, _⟩⟩,
    have hainv : a * a⁻¹ = 1,
    { apply mul_inv_cancel,
      rintro rfl,
      have hy0 : (y : A) = 0, simp [hy, f.map_zero], refl,
      have this : (0 : A) ≠ 1 := zero_ne_one,
      rw [← zero_mem_nonunits, ← hy0] at this,
      exact this (units.is_unit y),
    },
    refine is_unit_of_mul_eq_one ⟨a, ha⟩ ⟨a⁻¹, (_ : f a⁻¹ ∈ A)⟩
      (_ : (⟨a * a⁻¹, _⟩ : A.comap f)= ⟨1, _⟩), swap, simp [hainv],
    rcases y with ⟨⟨y1, h₁⟩, ⟨y2, h₂⟩, h1, h2⟩,
    convert h₂,
    have hy' : y1 = f a, simpa using hy,
    have h1' : y1 * y2 = 1 := subtype.mk.inj h1,
    apply_fun f at hainv,
    rw [map_mul, map_one] at hainv,
    rw hy' at h1',
    exact inv_unique hainv h1',
  end
}
/-  -/
noncomputable instance algebra_comap (A : valuation_subring L) (f : K →+* L) : 
   algebra (local_ring.residue_field (comap A f)) (local_ring.residue_field A) :=
ring_hom.to_algebra (local_ring.residue_field.map (ring_hom.valuation_subring_comap A f))

section

variables (K) [algebra K L]

open_locale 

/-- The group homomorphism from the decomposition group to the group 
 of automorphisms of the residue field of a valuation subring A-/
def decomposition_subgroup_to_residue_aut (A : valuation_subring L) : 
 (A.decomposition_subgroup K) →* ring_aut (local_ring.residue_field A) :=
 (local_ring.residue_field.map_aut).comp
 (mul_semiring_action.to_ring_aut (A.decomposition_subgroup K) A)

instance foo (A : valuation_subring L) : algebra (comap A (algebra_map K L)) A :=
ring_hom.to_algebra (ring_hom.valuation_subring_comap A (algebra_map K L))

/-- The group homomorphism from the decomposition group to the Galois group of 
A fixing the pullback of A. -/
def decomposition_subgroup.restrict (A : valuation_subring L) :
  (A.decomposition_subgroup K) →* (A ≃ₐ[comap A (algebra_map K L)] A) := {
  to_fun := λ x, {
    commutes' := begin
      rintros ⟨r, hr⟩,
      cases x with d hd,
      have := d.commutes,
      specialize this r,
      apply subtype.ext,
      exact this,
    end,
    ..(mul_semiring_action.to_ring_aut (A.decomposition_subgroup K) A x) },
  map_one' := begin
    ext,
    simp only [map_one, alg_equiv.coe_mk, alg_equiv.one_apply],
    refl,
    end,
  map_mul' := begin
    rintros x y,
    ext,
    simp only [alg_equiv.mul_apply, alg_equiv.coe_mk, map_mul],
    refl,
    end,
    }

end

open_locale number_field
open is_dedekind_domain

variables [number_field K] [number_field L] [algebra K L] [is_galois K L] (K)

open valuation_subring

/-- Obtaining the valuation subring of L from the nonzero prime 
 ideals of its ring of integers-/
noncomputable def _root_.is_dedekind_domain.height_one_spectrum.valuation_subring
 (q : height_one_spectrum (𝓞 L)) : valuation_subring L := 
  q.valuation.valuation_subring

/-- The natural reduction homomorphism from the decomposition group 
  to the Galois group of the residue field of A 
  fixing the residue field of the pullback of A -/
noncomputable def decomposition_subgroup.to_residue_field_equiv (A : valuation_subring L) :
  (decomposition_subgroup K A) →* 
  ((local_ring.residue_field A) ≃ₐ[local_ring.residue_field (comap A (algebra_map K L))]
  (local_ring.residue_field A)) := 
  (local_ring.algebra_equiv_to_residue_equiv).comp (decomposition_subgroup.restrict K A)

/- The natural reduction homomorphism is surjective. -/
theorem decomposition_subgroup.surjective (q : height_one_spectrum (𝓞 L)) :
  function.surjective (decomposition_subgroup.to_residue_field_equiv K
  q.valuation_subring) := sorry

lemma equal_kernels (q : height_one_spectrum (𝓞 L)) :
  (decomposition_subgroup.to_residue_field_equiv K
q.valuation_subring).ker = inertia_subgroup K q.valuation_subring := sorry

/-- If inertia is trivial, the natural reduction homomorphism is bijective. -/
theorem decomposition_subgroup.bijective (q : height_one_spectrum (𝓞 L))
  (h : inertia_subgroup K q.valuation_subring = ⊥) :
function.bijective (decomposition_subgroup.to_residue_field_equiv K
 q.valuation_subring) := 
begin
split,
{ have : (decomposition_subgroup.to_residue_field_equiv K
 q.valuation_subring).ker = ⊥,
{ rw equal_kernels K q,
  exact h,},
exact (decomposition_subgroup.to_residue_field_equiv K
 q.valuation_subring).ker_eq_bot_iff.mp this,},
{exact decomposition_subgroup.surjective K q}
end

/-- The Frobenius element as an element of the decomposition group -/
def frobq (ha : algebra.is_algebraic K L)
  (q : height_one_spectrum (𝓞 L))
  (h : inertia_subgroup K q.valuation_subring = ⊥) : 
  (decomposition_subgroup K q.valuation_subring) := sorry

end valuation_subring
