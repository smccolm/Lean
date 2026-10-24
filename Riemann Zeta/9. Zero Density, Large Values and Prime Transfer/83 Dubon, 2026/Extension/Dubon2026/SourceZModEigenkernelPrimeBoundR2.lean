import Dubon2026.SourceZModQuadraticEigenkernelsR2

/-! DUB-17/18 -> reverse genus -> exceptional j-fiber census ->
cyclic-subgroup fixed points of the order-two/order-three automorphisms.
The literal quadratic eigenkernels in the existing rank-two torsion
coordinates are used. The quadratic identity and non-scalar action on
prime torsion remain explicit upstream inputs until proved for the
specific elliptic automorphisms. No exceptional-fiber count is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo.lean. -/
namespace Dubon2026.SourceQuadraticCyclicCount
noncomputable section
variable {n : ℕ} [NeZero n]

theorem card_eig_pTorsion_le (τ : (ZMod n × ZMod n) →+ (ZMod n × ZMod n)) (k : ZMod n) {p : ℕ} (hp : p.Prime)
    (hns : ∃ v : (ZMod n × ZMod n), addOrderOf v = p ∧ ∀ m : ℕ, τ v ≠ m • v) :
    Nat.card {g : eig τ k // p • g = 0} ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨v₀, hv₀, hv₀ns⟩ := hns

  have hv₀K : v₀ ∉ eig τ k := fun h => hv₀ns k.val (by
    rw [mem_eig] at h; rw [h, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_zmod_val])
  let Z : AddSubgroup (ZMod n × ZMod n) := AddSubgroup.zmultiples v₀
  have hZcard : Nat.card Z = p := by rw [Nat.card_zmultiples, hv₀]
  haveI : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZcard]; exact hp.ne_zero)

  let Kp : AddSubgroup (ZMod n × ZMod n) :=
    { carrier := {v | τ v = k • v ∧ p • v = 0}
      zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, smul_zero, and_self]
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha.1, hb.1, smul_add, nsmul_add, ha.2, hb.2, add_zero]; exact ⟨rfl, rfl⟩
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_neg, ha.1, smul_neg, smul_neg, ha.2, neg_zero]; exact ⟨rfl, rfl⟩ }
  have hKp : Nat.card {g : eig τ k // p • g = 0} = Nat.card Kp := by
    refine Nat.card_congr ⟨fun g => ⟨g.1.1, g.1.2, ?_⟩, fun v => ⟨⟨v.1, v.2.1⟩, ?_⟩, ?_, ?_⟩
    · exact congrArg Subtype.val g.2
    · exact Subtype.ext v.2.2
    · intro g; rfl
    · intro v; rfl

  have hdisj : ∀ x, x ∈ Kp → x ∈ Z → x = 0 := by
    intro x hxK hxZ
    by_contra hx0

    have hpx : p • x = 0 := hxK.2
    have hordx : addOrderOf x = p :=
      (hp.eq_one_or_self_of_dvd _ (addOrderOf_dvd_of_nsmul_eq_zero hpx)).resolve_left
        (fun h1 => hx0 (AddMonoid.addOrderOf_eq_one_iff.mp h1))
    have hle : AddSubgroup.zmultiples x ≤ Z := AddSubgroup.zmultiples_le_of_mem hxZ
    have heq : AddSubgroup.zmultiples x = Z :=
      AddSubgroup.eq_of_le_of_card_ge hle (by rw [hZcard, Nat.card_zmultiples, hordx])
    have hv₀x : v₀ ∈ AddSubgroup.zmultiples x := by rw [heq]; exact AddSubgroup.mem_zmultiples v₀
    have hxk : AddSubgroup.zmultiples x ≤ eig τ k := AddSubgroup.zmultiples_le_of_mem hxK.1
    exact hv₀K (hxk hv₀x)

  let f : Kp × Z → {v : (ZMod n × ZMod n) // p • v = 0} := fun gz => ⟨gz.1.1 + gz.2.1, by
    obtain ⟨⟨g, hg⟩, ⟨z, hz⟩⟩ := gz
    obtain ⟨a, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
    show p • (g + a • v₀) = 0
    rw [nsmul_add, hg.2, zero_add, smul_comm, ← hv₀, addOrderOf_nsmul_eq_zero, smul_zero]⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨g, hg⟩, ⟨z, hz⟩⟩ ⟨⟨g', hg'⟩, ⟨z', hz'⟩⟩ h
    have h' : g + z = g' + z' := congrArg Subtype.val h
    have hd : g - g' = z' - z := sub_eq_sub_iff_add_eq_add.mpr (by rw [h', add_comm])
    have h0 : g - g' = 0 := hdisj _ (Kp.sub_mem hg hg') (hd ▸ Z.sub_mem hz' hz)
    have hg0 : g = g' := sub_eq_zero.mp h0
    have hz0 : z = z' := by rw [hg0] at h'; exact add_left_cancel h'
    subst hg0 hz0; rfl
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hZcard] at hle
  have hle2 := le_trans hle (card_pTorsion_le hp)
  rw [sq] at hle2
  rw [hKp]
  exact Nat.le_of_mul_le_mul_right hle2 hp.pos

end
end Dubon2026.SourceQuadraticCyclicCount
