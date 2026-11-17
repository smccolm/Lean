/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
import Dubon2026.SourceDicksonClassification

/-! DUB-17/18 -> original residual large image -> explicit projective subfield conjugacy.
Reuse the exact containment, cardinality and index-two arguments of the pinned
Dickson proof, retaining its intermediate subgroup equality. This removes the
abstract-isomorphism-to-projective-matrix comparison; arithmetic exclusions and
the subsequent linear-image/coefficient-field comparison remain open.
Upstream: ImperialCollegeLondon/FLT@478c1013cd29c27d72f57aa8b691fa46083664b3. -/
namespace Dubon2026.SourceDickson
attribute [local instance] instFintypeOfFinite
noncomputable section
variable (p : ℕ) [Fact p.Prime] [Fact (2 < p)]

/-- An index-two subgroup is the literal projective special linear image. -/
theorem index_two_subgroup_eq_standardPSL (F : Type*) [Field F] [CharP F p] [Fintype F]
    (hcard : 5 ≤ Fintype.card F) (H : Subgroup (PGLOf F)) (hH : H.index = 2) :
    H = PSLImageInPGL F := by
  have hle := PSLImageInPGL_le_of_index_two p F H hH
  have hidx := PSLImageInPGL_index p F hcard
  apply Eq.symm
  apply SetLike.ext'
  apply Set.eq_of_subset_of_card_le hle
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  have h := (Subgroup.card_mul_index H).trans
    (Subgroup.card_mul_index (PSLImageInPGL F)).symm
  rw [hH, hidx] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).le

/-- The cardinality recognition inside a finite subfield gives equality of subgroups. -/
theorem pgl_subgroup_eq_standardPSL_of_card (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (H : Subgroup (PGLOf (K p)))
    (hH_le : H ≤ (pglMap (galoisFieldRingHom (p := p) m)).range)
    (hH_card : Nat.card H = p ^ m * (p ^ (2 * m) - 1) / 2) :
    H = (PSLImageInPGL (GaloisField p m)).map
      (pglMap (galoisFieldRingHom (p := p) m)) := by
  let φ := pglMap (galoisFieldRingHom (p := p) m)
  let H' := H.comap φ
  have h_equiv : H' ≃* H :=
    (H'.equivMapOfInjective φ (pglMap_injective _ (RingHom.injective _))).trans (MulEquiv.subgroupCongr (by
      ext x; rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; obtain ⟨y, rfl⟩ := hH_le hx; exact ⟨y, hx, rfl⟩))
  have hH'_index : H'.index = 2 := by
    have h_card : Nat.card (PGLOf (GaloisField p m)) = p ^ m * (p ^ (2 * m) - 1) := by
      rw [card_PGL2, Fintype.card_eq_nat_card.trans (GaloisField.card p m (ne_of_gt hm)), pow_mul']
    have hp_gt_two : p > 2 := Fact.out
    have h_even : 2 ∣ p ^ (2 * m) - 1 := by
      rw [← even_iff_two_dvd, Nat.even_sub (Nat.one_le_pow _ _ (Nat.le_trans (by norm_num : 1 ≤ 2) hp_gt_two.le))]
      have h_odd : ¬ Even p := fun h ↦ ne_of_gt hp_gt_two ((Nat.Prime.even_iff Fact.out).mp h)
      exact iff_of_false (fun h ↦ h_odd (Nat.even_pow.mp h).1) (by norm_num)
    have h_dvd : 2 ∣ p ^ m * (p ^ (2 * m) - 1) := dvd_mul_of_dvd_right h_even _
    have hp2m : 1 < p ^ (2 * m) := one_lt_pow₀ (Nat.Prime.one_lt Fact.out) (by omega)
    have h_nz : p ^ m * (p ^ (2 * m) - 1) / 2 ≠ 0 :=
      ne_of_gt (Nat.div_pos (Nat.le_of_dvd (mul_pos (show 0 < p ^ m by omega) (Nat.sub_pos_of_lt hp2m)) h_dvd) (by norm_num))
    exact mul_right_cancel₀ h_nz <|
      calc H'.index * (p ^ m * (p ^ (2 * m) - 1) / 2)
        _ = H'.index * Nat.card H' := by rw [Nat.card_congr h_equiv.toEquiv, hH_card]
        _ = Nat.card (PGLOf (GaloisField p m)) := Subgroup.index_mul_card H'
        _ = p ^ m * (p ^ (2 * m) - 1) := h_card
        _ = (p ^ m * (p ^ (2 * m) - 1) / 2) * 2 := (Nat.div_mul_cancel h_dvd).symm
        _ = 2 * (p ^ m * (p ^ (2 * m) - 1) / 2) := mul_comm _ _
  have heq := index_two_subgroup_eq_standardPSL p (GaloisField p m) (by
    rw [Fintype.card_eq_nat_card, GaloisField.card p m (by omega)]
    exact hpm) H' hH'_index
  calc H = H'.map φ := (Subgroup.map_comap_eq_self hH_le).symm
       _ = (PSLImageInPGL (GaloisField p m)).map φ := by rw [heq]

/-- A projective subgroup of PSL₂ cardinality is conjugate to the standard finite-field image. -/
theorem psl_conjugate_to_standard (G : Subgroup (PGLOf (K p))) [Finite G]
    (m : ℕ) (hm : 5 ≤ p ^ m)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2) :
    ∃ g : PGLOf (K p), G.map (MulEquiv.toMonoidHom (MulAut.conj g)) =
      (PSLImageInPGL (GaloisField p m)).map (pglMap (galoisFieldRingHom (p := p) m)) := by
  have hm1 : 1 ≤ m := m_ge_one_of_pow_ge_three p m (by omega)
  obtain ⟨g, hg⟩ := psl_G_le_pgl_range_from_orbit p G m hm1 hm hn
  refine ⟨g, pgl_subgroup_eq_standardPSL_of_card p m hm1 hm _ hg ?_⟩
  rw [← Nat.card_congr (G.equivMapOfInjective
    (MulEquiv.toMonoidHom (MulAut.conj g)) (MulEquiv.injective _)).toEquiv, hn]

end
end Dubon2026.SourceDickson
