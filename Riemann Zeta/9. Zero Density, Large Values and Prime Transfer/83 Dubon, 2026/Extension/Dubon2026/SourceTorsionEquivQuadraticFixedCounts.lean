import Dubon2026.SourceZModQuadraticStableCyclicCountR2
import Dubon2026.SourceInvariantCyclicTorsionTransport

/-! DUB-17/18 -> reverse genus -> exceptional j-fiber census ->
fixed cyclic subgroups of the specific elliptic automorphisms.
The existing actual torsion equivalence transports the quadratic action
and non-scalar prime-torsion conditions to rank-two coordinates. Reuse
the local cyclic-subgroup transport instead of reproving map/comap
equivalences. The elliptic quadratic and non-scalar inputs remain open.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the corresponding
S_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq source solutions. -/
namespace Dubon2026.SourceQuadraticCyclicCount
noncomputable section
open SourceLevelProjective

theorem stable_cyclic_card_of_torsion_equiv_eq_nuTwo
    {A : Type*} [AddCommGroup A] (n : ℕ) [NeZero n]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n)
    (σ : A →+ A) (hσ : ∀ a : A, σ (σ a) = -a)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = n ∧ H.map σ = H}
      = nuTwo n := by

  have memV : ∀ a : A, a ∈ Submodule.torsionBy ℤ A n ↔ n • a = 0 := fun a => by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  have σV : ∀ a ∈ Submodule.torsionBy ℤ A n, σ a ∈ Submodule.torsionBy ℤ A n := fun a ha => by
    rw [memV] at ha ⊢; rw [← map_nsmul, ha, map_zero]

  let ι : ZMod n × ZMod n →+ A :=
    (Submodule.torsionBy ℤ A n).subtype.toAddMonoidHom.comp e.toAddMonoidHom
  have ι_apply : ∀ m, ι m = (e m : A) := fun m => rfl
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιr : ∀ a : A, n • a = 0 → ∃ m, ι m = a := fun a ha =>
    ⟨e.symm ⟨a, (memV a).mpr ha⟩, by rw [ι_apply, AddEquiv.apply_symm_apply]⟩

  let σr : Submodule.torsionBy ℤ A n →+ Submodule.torsionBy ℤ A n :=
    (σ.comp (Submodule.torsionBy ℤ A n).subtype.toAddMonoidHom).codRestrict
      (Submodule.torsionBy ℤ A n) (fun x => σV x.1 x.2)
  have σr_apply : ∀ x, ((σr x : Submodule.torsionBy ℤ A n) : A) = σ x := fun x => rfl
  let T : ZMod n × ZMod n →+ ZMod n × ZMod n := e.symm.toAddMonoidHom.comp (σr.comp e.toAddMonoidHom)
  have T_apply : ∀ m, T m = e.symm (σr (e m)) := fun m => rfl
  have hT : ∀ m, ι (T m) = σ (ι m) := fun m => by
    simp only [T_apply, ι_apply, AddEquiv.apply_symm_apply, σr_apply]
  have hT2 : ∀ m, T (T m) = -m := fun m =>
    hι (by rw [hT, hT, hσ, map_neg])

  have hnsT : ∀ p : ℕ, p.Prime → p ∣ n →
      ∃ v : ZMod n × ZMod n, addOrderOf v = p ∧ ∀ k : ℕ, T v ≠ k • v := by
    intro p hp hpn
    obtain ⟨a, ha, hane⟩ := hns p hp hpn
    obtain ⟨m, rfl⟩ := hιr a (by
      rw [← ha] at hpn
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp hpn)
    refine ⟨m, by rwa [addOrderOf_injective ι hι] at ha, fun k hk => hane k ?_⟩
    rw [← hT, hk, map_nsmul]
  rw [← stable_cyclic_subgroup_card_transport n ι hι hιr T σ (AddMonoidHom.ext hT)]
  exact stable_cyclic_card_eq_nuTwo n T hT2 hnsT

theorem stable_cyclic_card_of_torsion_equiv_eq_nuThree
    {A : Type*} [AddCommGroup A] (n : ℕ) [NeZero n]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n)
    (σ : A →+ A) (hσ : ∀ a : A, σ (σ a) + σ a + a = 0)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = n ∧ H.map σ = H}
      = nuThree n := by

  have memV : ∀ a : A, a ∈ Submodule.torsionBy ℤ A n ↔ n • a = 0 := fun a => by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  have σV : ∀ a ∈ Submodule.torsionBy ℤ A n, σ a ∈ Submodule.torsionBy ℤ A n := fun a ha => by
    rw [memV] at ha ⊢; rw [← map_nsmul, ha, map_zero]

  let ι : ZMod n × ZMod n →+ A :=
    (Submodule.torsionBy ℤ A n).subtype.toAddMonoidHom.comp e.toAddMonoidHom
  have ι_apply : ∀ m, ι m = (e m : A) := fun m => rfl
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιr : ∀ a : A, n • a = 0 → ∃ m, ι m = a := fun a ha =>
    ⟨e.symm ⟨a, (memV a).mpr ha⟩, by rw [ι_apply, AddEquiv.apply_symm_apply]⟩

  let σr : Submodule.torsionBy ℤ A n →+ Submodule.torsionBy ℤ A n :=
    (σ.comp (Submodule.torsionBy ℤ A n).subtype.toAddMonoidHom).codRestrict
      (Submodule.torsionBy ℤ A n) (fun x => σV x.1 x.2)
  have σr_apply : ∀ x, ((σr x : Submodule.torsionBy ℤ A n) : A) = σ x := fun x => rfl
  let T : ZMod n × ZMod n →+ ZMod n × ZMod n := e.symm.toAddMonoidHom.comp (σr.comp e.toAddMonoidHom)
  have T_apply : ∀ m, T m = e.symm (σr (e m)) := fun m => rfl
  have hT : ∀ m, ι (T m) = σ (ι m) := fun m => by
    simp only [T_apply, ι_apply, AddEquiv.apply_symm_apply, σr_apply]
  have hT2 : ∀ m, T (T m) + T m + m = 0 := fun m =>
    hι (by rw [map_add, map_add, hT, hT, hσ, map_zero])

  have hnsT : ∀ p : ℕ, p.Prime → p ∣ n →
      ∃ v : ZMod n × ZMod n, addOrderOf v = p ∧ ∀ k : ℕ, T v ≠ k • v := by
    intro p hp hpn
    obtain ⟨a, ha, hane⟩ := hns p hp hpn
    obtain ⟨m, rfl⟩ := hιr a (by
      rw [← ha] at hpn
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp hpn)
    refine ⟨m, by rwa [addOrderOf_injective ι hι] at ha, fun k hk => hane k ?_⟩
    rw [← hT, hk, map_nsmul]
  rw [← stable_cyclic_subgroup_card_transport n ι hι hιr T σ (AddMonoidHom.ext hT)]
  exact stable_cyclic_card_eq_nuThree n T hT2 hnsT

end
end Dubon2026.SourceQuadraticCyclicCount
