import Dubon2026.HeckeLowerCosets

/-! # The genuine Hecke coset domains in the faithful real projective action -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups Pointwise

noncomputable section

/-- The actual Gamma0 matrix map, with codomain its real projective image. -/
def gamma0ToRealProjective (Q : ℕ) : Gamma0 Q →* realProjectiveGamma0 Q :=
  (slToRealProjective.comp (Gamma0 Q).subtype).codRestrict (realProjectiveGamma0 Q)
    (fun γ => ⟨QuotientGroup.mk γ.val, ⟨γ.val, γ.property, rfl⟩, rfl⟩)

/-- Every element of the real projective image comes from an actual Gamma0 matrix. -/
theorem gamma0ToRealProjective_surjective (Q : ℕ) :
    Function.Surjective (gamma0ToRealProjective Q) := by
  intro q
  obtain ⟨δ, hδ, he⟩ := q.property
  obtain ⟨γ, hγ, hγδ⟩ := hδ
  refine ⟨⟨γ, hγ⟩, Subtype.ext ?_⟩
  change modularProjectiveEmbedding (QuotientGroup.mk γ) = q.val
  change modularProjectiveEmbedding ((QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) γ) = q.val
  rw [hγδ]
  exact he

/-- The genuine real projective Gamma0 group is countable, as its integral source is. -/
instance realProjectiveGamma0Countable (Q : ℕ) : Countable (realProjectiveGamma0 Q) :=
  (gamma0ToRealProjective_surjective Q).countable

/-- Projectivization removes only scalar matrices, whose two off-diagonal entries vanish. -/
theorem gamma0ToRealProjective_ker_entries (Q : ℕ) (γ : Gamma0 Q)
    (hγ : γ ∈ (gamma0ToRealProjective Q).ker) : γ.val 0 1 = 0 ∧ γ.val 1 0 = 0 := by
  have hz : slToRealProjective γ.val = 1 := congrArg Subtype.val hγ
  have hc : γ.val ∈ Subgroup.center SL(2, ℤ) := by
    rw [← slToRealProjective_ker]
    exact hz
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  constructor
  · have h := congrFun (congrFun hr 0) 1
    simpa [Matrix.scalar] using h.symm
  · have h := congrFun (congrFun hr 1) 0
    simpa [Matrix.scalar] using h.symm

/-- The kernel is absorbed by the actual upper congruence subgroup. -/
theorem gamma0ToRealProjective_ker_le_upper (Q p : ℕ) :
    (gamma0ToRealProjective Q).ker ≤ heckeUpperSubgroup Q p := by
  intro γ hγ
  change ((γ.val 0 1 : ℤ) : ZMod p) = 0
  simp [(gamma0ToRealProjective_ker_entries Q γ hγ).1]

/-- The kernel is absorbed by the actual lower congruence subgroup. -/
theorem gamma0ToRealProjective_ker_le_lower (Q p : ℕ) :
    (gamma0ToRealProjective Q).ker ≤ heckeLowerSubgroup Q p := by
  intro γ hγ
  change ((γ.val 1 0 : ℤ) : ZMod p) = 0
  simp [(gamma0ToRealProjective_ker_entries Q γ hγ).2]

/-- Mapping a nested subgroup through inclusion preserves its actual action and fundamental domain. -/
theorem fundamentalDomain_map_subtype {G α : Type*} [Group G] [MeasurableSpace α]
    [MulAction G α] {μ : Measure α} (H : Subgroup G) (K : Subgroup H)
    {S : Set α} (hS : IsFundamentalDomain K S μ) :
    IsFundamentalDomain (K.map H.subtype) S μ := by
  have he : (Equiv.refl α) '' S = S := by simp
  rw [← he]
  refine hS.image_of_equiv (Equiv.refl α) (Measure.QuasiMeasurePreserving.id _)
    ((Subgroup.equivMapOfInjective K H.subtype Subtype.val_injective).toEquiv.symm) ?_
  intro g x
  let e := Subgroup.equivMapOfInjective K H.subtype Subtype.val_injective
  have hv : (g : G) = ((e.symm g : K) : G) := by
    have h := congrArg Subtype.val (e.apply_symm_apply g)
    exact h.symm
  change ((e.symm g : K) : G) • x = (g : G) • x
  rw [hv]

/-- The genuine upper congruence subgroup in the real projective ambient group. -/
def heckeRealUpperSubgroup (Q p : ℕ) : Subgroup PGL(2, ℝ) :=
  ((heckeUpperSubgroup Q p).map (gamma0ToRealProjective Q)).map (realProjectiveGamma0 Q).subtype

/-- The genuine lower congruence subgroup in the real projective ambient group. -/
def heckeRealLowerSubgroup (Q p : ℕ) : Subgroup PGL(2, ℝ) :=
  ((heckeLowerSubgroup Q p).map (gamma0ToRealProjective Q)).map (realProjectiveGamma0 Q).subtype

/-- The literal union of upper representative translates is the actual upper-subgroup domain. -/
theorem isFundamentalDomain_heckeUpper {p Q : ℕ} [NeZero Q] [NeZero p]
    (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    IsFundamentalDomain (heckeRealUpperSubgroup Q p)
      (⋃ x : Option (ZMod p), slToRealProjective (heckeUpperRepresentative p Q hpQ x).val •
        gamma0FundamentalDomain Q) (volume : Measure ℍ) := by
  let e := (heckeUpperCosetEquiv hp hpQ).trans
    (subgroupCosetEquiv (gamma0ToRealProjective Q) (heckeUpperSubgroup Q p)
      (gamma0ToRealProjective_surjective Q) (gamma0ToRealProjective_ker_le_upper Q p))
  have he : ∀ x, e x = QuotientGroup.mk ((gamma0ToRealProjective Q
      (heckeUpperRepresentative p Q hpQ x))⁻¹) := by
    intro x
    change QuotientGroup.mk (gamma0ToRealProjective Q ((heckeUpperRepresentative p Q hpQ x)⁻¹)) = _
    rw [map_inv]
  exact fundamentalDomain_map_subtype (realProjectiveGamma0 Q) _
    (fundamentalDomain_iUnion_smul_of_transversal (isFundamentalDomain_realGamma0 Q) e he)

/-- The literal union of lower representative translates is the actual lower-subgroup domain. -/
theorem isFundamentalDomain_heckeLower {p Q : ℕ} [NeZero Q] [NeZero p]
    (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    IsFundamentalDomain (heckeRealLowerSubgroup Q p)
      (⋃ x : Option (ZMod p), slToRealProjective (heckeLowerRepresentative p Q hpQ x).val •
        gamma0FundamentalDomain Q) (volume : Measure ℍ) := by
  let e := (heckeLowerCosetEquiv hp hpQ).trans
    (subgroupCosetEquiv (gamma0ToRealProjective Q) (heckeLowerSubgroup Q p)
      (gamma0ToRealProjective_surjective Q) (gamma0ToRealProjective_ker_le_lower Q p))
  have he : ∀ x, e x = QuotientGroup.mk ((gamma0ToRealProjective Q
      (heckeLowerRepresentative p Q hpQ x))⁻¹) := by
    intro x
    change QuotientGroup.mk (gamma0ToRealProjective Q ((heckeLowerRepresentative p Q hpQ x)⁻¹)) = _
    rw [map_inv]
  exact fundamentalDomain_map_subtype (realProjectiveGamma0 Q) _
    (fundamentalDomain_iUnion_smul_of_transversal (isFundamentalDomain_realGamma0 Q) e he)

/-- The upper representatives remain distinct in the actual real projective Gamma0 group. -/
theorem heckeUpperRepresentative_projective_injective {p Q : ℕ}
    (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    Function.Injective (fun x => gamma0ToRealProjective Q (heckeUpperRepresentative p Q hpQ x)) := by
  intro x y he
  apply heckeUpperCoset_injective hp hpQ
  apply subgroupCosetMap_injective (gamma0ToRealProjective Q) (heckeUpperSubgroup Q p)
    (gamma0ToRealProjective_ker_le_upper Q p)
  change QuotientGroup.mk (gamma0ToRealProjective Q ((heckeUpperRepresentative p Q hpQ x)⁻¹)) =
    QuotientGroup.mk (gamma0ToRealProjective Q ((heckeUpperRepresentative p Q hpQ y)⁻¹))
  simp only [map_inv, he]

/-- The lower representatives remain distinct in the actual real projective Gamma0 group. -/
theorem heckeLowerRepresentative_projective_injective {p Q : ℕ}
    (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    Function.Injective (fun x => gamma0ToRealProjective Q (heckeLowerRepresentative p Q hpQ x)) := by
  intro x y he
  apply heckeLowerCoset_injective hp hpQ
  apply subgroupCosetMap_injective (gamma0ToRealProjective Q) (heckeLowerSubgroup Q p)
    (gamma0ToRealProjective_ker_le_lower Q p)
  change QuotientGroup.mk (gamma0ToRealProjective Q ((heckeLowerRepresentative p Q hpQ x)⁻¹)) =
    QuotientGroup.mk (gamma0ToRealProjective Q ((heckeLowerRepresentative p Q hpQ y)⁻¹))
  simp only [map_inv, he]

/-- The actual lower Hecke subgroup is countable through its faithful image description. -/
instance heckeRealLowerCountable (Q p : ℕ) : Countable (heckeRealLowerSubgroup Q p) :=
  (Subgroup.equivMapOfInjective ((heckeLowerSubgroup Q p).map (gamma0ToRealProjective Q))
    (realProjectiveGamma0 Q).subtype Subtype.val_injective).symm.injective.countable

end
end Dubon2026
