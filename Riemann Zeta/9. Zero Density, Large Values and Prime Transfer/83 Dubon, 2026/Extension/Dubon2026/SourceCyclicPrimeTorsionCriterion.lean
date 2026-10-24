import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Index

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular good reduction
-> reverse genus -> exceptional j-fiber counts -> order-two/order-three
cyclic-subgroup fixed points -> cyclicity of quadratic eigenkernels.
Prime-torsion bounds suffice for the native cyclicity criterion. The
kernel/range cardinality induction avoids a new abelian-group structure
classification. This foundation will discharge eigenkernel cyclicity;
the elliptic non-scalar prime-torsion inputs remain separate obligations.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo.lean. -/
namespace Dubon2026.SourceQuadraticCyclicCount
noncomputable section

theorem isAddCyclic_of_card_pTorsion_le {G : Type*} [AddCommGroup G]
    [Finite G] (h : ∀ p : ℕ, p.Prime → Nat.card {g : G // p • g = 0} ≤ p) :
    IsAddCyclic G := by
  classical
  obtain ⟨_⟩ := nonempty_fintype G
  let T : ℕ → AddSubgroup G := fun m =>
    { carrier := {g | m • g = 0}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb =>
        show m • (a + b) = 0 by rw [nsmul_add, ha, hb, add_zero]
      neg_mem' := fun {a} ha =>
        show m • (-a) = 0 by rw [smul_neg, ha, neg_zero] }
  have hTcard : ∀ m, Nat.card (T m) = Nat.card {g : G // m • g = 0} := fun m => rfl
  suffices hbound : ∀ m : ℕ, 0 < m → Nat.card (T m) ≤ m by
    refine isAddCyclic_of_card_nsmul_eq_zero_le (fun m hm => ?_)
    have hfs : (Finset.univ.filter (fun a : G => m • a = 0)).card
        = Fintype.card {g : G // m • g = 0} := (Fintype.card_subtype _).symm
    calc (Finset.univ.filter (fun a : G => m • a = 0)).card
        = Nat.card (T m) := hfs.trans (Nat.card_eq_fintype_card (α := T m)).symm
      _ ≤ m := hbound m hm
  intro m hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases eq_or_ne m 1 with rfl | hm1
  · have h1 : T 1 = ⊥ := by
      refine le_antisymm (fun g hg => ?_) bot_le
      exact AddSubgroup.mem_bot.mpr (one_nsmul g ▸ hg)
    rw [h1, AddSubgroup.card_bot]
  · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    have hmp : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos
    have hmpm : m / p < m := Nat.div_lt_self hm hp.one_lt
    let φ : T m →+ T p :=
      { toFun := fun g => ⟨(m/p) • g.1, by
          show p • ((m/p) • g.1) = 0
          rw [← mul_nsmul', Nat.mul_div_cancel' hpm]; exact g.2⟩
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp) }
    have hkerφ : Nat.card φ.ker ≤ m / p := by
      have hψ : ∀ g : φ.ker, (m/p) • (g.1.1 : G) = 0 := fun g =>
        congrArg Subtype.val (φ.mem_ker.mp g.2)
      let ψ : φ.ker → T (m/p) := fun g => ⟨g.1.1, hψ g⟩
      have hψinj : Function.Injective ψ := fun a b hab => by
        have hv : (a.1.1 : G) = b.1.1 := congrArg (fun x : T (m/p) => (x : G)) hab
        exact Subtype.ext (Subtype.ext hv)
      exact le_trans (Nat.card_le_card_of_injective ψ hψinj) (ih (m/p) hmpm hmp)
    have himφ : Nat.card φ.range ≤ p :=
      le_trans (Nat.card_le_card_of_injective (AddSubgroup.subtype φ.range)
        (AddSubgroup.subtype_injective _)) ((hTcard p).symm ▸ h p hp)
    calc Nat.card (T m)
        = Nat.card φ.ker * Nat.card φ.range := by
          rw [mul_comm, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv,
            ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]
      _ ≤ (m/p) * p := Nat.mul_le_mul hkerφ himφ
      _ = m := Nat.div_mul_cancel hpm

end
end Dubon2026.SourceQuadraticCyclicCount
