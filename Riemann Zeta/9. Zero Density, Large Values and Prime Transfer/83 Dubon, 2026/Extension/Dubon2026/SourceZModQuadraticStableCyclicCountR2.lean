import Dubon2026.SourceZModEigenkernelPrimeBoundR2

/-! DUB-17/18 -> reverse genus -> exceptional j-fiber census ->
fixed cyclic subgroups of the specific elliptic automorphisms.
Quadratic eigenkernels classify the invariant cyclic subgroups and give
the exact nuTwo/nuThree counts, conditional on the explicit quadratic
identity and non-scalar action on each prime torsion. Those elliptic
inputs remain to be derived; this does not close the exceptional census.
The two trace values share the same rank-two kernel argument.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo.lean
and S_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree.lean. -/
namespace Dubon2026.SourceQuadraticCyclicCount
noncomputable section
open SourceLevelProjective
variable {n : ℕ} [NeZero n]

section Count

variable (τ : (ZMod n × ZMod n) →+ (ZMod n × ZMod n)) (s : ZMod n) (hτ : ∀ v, τ (τ v) = s • τ v - v)
  (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ v : (ZMod n × ZMod n), addOrderOf v = p ∧ ∀ m : ℕ, τ v ≠ m • v)
include hτ hns

omit hτ in
theorem eig_cyclic_card_le (k : ZMod n) : IsAddCyclic (eig τ k) ∧ Nat.card (eig τ k) ≤ n := by
  have step1 : ∀ p : ℕ, p.Prime → Nat.card {g : eig τ k // p • g = 0} ≤ p := by
    intro p hp
    by_cases hpn : p ∣ n
    · exact card_eig_pTorsion_le τ k hp (hns p hp hpn)
    · have hpn' : ∀ g : eig τ k, p • g = 0 → g = 0 := by
        intro g hg
        have hg' : p • (g : (ZMod n × ZMod n)) = 0 := congrArg Subtype.val hg
        have hgord : addOrderOf (g : (ZMod n × ZMod n)) ∣ Nat.gcd p n :=
          Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hg')
            (addOrderOf_dvd_of_nsmul_eq_zero (nsmul_self_eq_zero (g : (ZMod n × ZMod n))))
        rw [(hp.coprime_iff_not_dvd.mpr hpn), Nat.dvd_one] at hgord
        refine Subtype.ext ?_
        have : (1:ℕ) • (g : (ZMod n × ZMod n)) = 0 := hgord ▸ addOrderOf_nsmul_eq_zero _
        simpa using this
      haveI hsub : Subsingleton {g : eig τ k // p • g = 0} :=
        ⟨fun a b => Subtype.ext ((hpn' a.1 a.2).trans (hpn' b.1 b.2).symm)⟩
      have hc1 : Nat.card {g : eig τ k // p • g = 0} = 1 :=
        Nat.card_of_subsingleton (⟨0, by simp only [nsmul_zero]⟩ : {g : eig τ k // p • g = 0})
      exact hc1 ▸ hp.one_lt.le
  have hcyc := isAddCyclic_of_card_pTorsion_le step1
  refine ⟨hcyc, ?_⟩
  have hexp : AddMonoid.exponent (eig τ k) ∣ n :=
    AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero (fun g => Subtype.ext (nsmul_self_eq_zero (g : (ZMod n × ZMod n))))
  calc Nat.card (eig τ k) = AddMonoid.exponent (eig τ k) := IsAddCyclic.exponent_eq_card.symm
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hexp

theorem eig_cyclic_card_eq {k : ZMod n} (hk : k * k = s * k - 1) :
    IsAddCyclic (eig τ k) ∧ Nat.card (eig τ k) = n := by
  obtain ⟨hc, hle⟩ := eig_cyclic_card_le τ hns k
  obtain ⟨_, hle'⟩ := eig_cyclic_card_le τ hns (s - k)
  have hge := sq_le_card_mul_card τ s hτ hk
  refine ⟨hc, le_antisymm hle ?_⟩
  have hmul := Nat.mul_le_mul hle hle'
  rw [sq] at hge
  nlinarith [hge, hmul, hle, hle', Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)]

theorem card_stable_eq_card_roots :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n ∧ H.map τ = H}
      = Nat.card {k : ZMod n // k * k = s * k - 1} := by

  have gen : ∀ H : AddSubgroup (ZMod n × ZMod n), IsAddCyclic H → Nat.card H = n →
      ∃ v : (ZMod n × ZMod n), addOrderOf v = n ∧ AddSubgroup.zmultiples v = H := by
    intro H hc hcard
    haveI := hc
    haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; exact NeZero.ne n)
    obtain ⟨g, hg⟩ := (isAddCyclic_iff_exists_addOrderOf_eq_natCard (α := H)).mp hc
    have hgn : addOrderOf (g : (ZMod n × ZMod n)) = n := by
      rw [show addOrderOf (g : (ZMod n × ZMod n)) = addOrderOf g from
        addOrderOf_injective H.subtype H.subtype_injective g, hg, hcard]
    refine ⟨g, hgn, ?_⟩
    exact AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le_of_mem g.2)
      (by rw [hcard, Nat.card_zmultiples, hgn])
  symm
  refine Nat.card_eq_of_bijective
    (fun k : {k : ZMod n // k * k = s * k - 1} =>
      (⟨eig τ k.1, (eig_cyclic_card_eq τ s hτ hns k.2).1, (eig_cyclic_card_eq τ s hτ hns k.2).2,
        map_eig_eq τ s hτ k.1⟩ : {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n ∧ H.map τ = H}))
    ⟨?_, ?_⟩
  ·
    intro k k' h
    have h' : eig τ k.1 = eig τ k'.1 := congrArg Subtype.val h
    obtain ⟨v, hv, hvH⟩ := gen (eig τ k.1) (eig_cyclic_card_eq τ s hτ hns k.2).1
      (eig_cyclic_card_eq τ s hτ hns k.2).2
    have hv1 : τ v = k.1 • v := (mem_eig τ k.1 v).mp (hvH ▸ AddSubgroup.mem_zmultiples v)
    have hv2 : τ v = k'.1 • v := (mem_eig τ k'.1 v).mp (h' ▸ hvH ▸ AddSubgroup.mem_zmultiples v)
    refine Subtype.ext (sub_eq_zero.mp (eq_zero_of_smul_eq_zero hv ?_))
    rw [sub_smul, ← hv1, ← hv2, sub_self]
  ·
    rintro ⟨H, hc, hcard, hst⟩
    obtain ⟨v, hv, hvH⟩ := gen H hc hcard
    have hτv : τ v ∈ H := by rw [← hst]; exact AddSubgroup.mem_map_of_mem τ (hvH ▸ AddSubgroup.mem_zmultiples v)
    rw [← hvH, AddSubgroup.mem_zmultiples_iff] at hτv
    obtain ⟨a, ha⟩ := hτv
    have hk : τ v = (a : ZMod n) • v := by rw [Int.cast_smul_eq_zsmul, ha]
    have hroot : (a : ZMod n) * (a : ZMod n) = s * (a : ZMod n) - 1 := root_of_eigen τ s hτ hv hk
    refine ⟨⟨(a : ZMod n), hroot⟩, Subtype.ext ?_⟩

    show eig τ (a : ZMod n) = H
    haveI : Finite (eig τ (a : ZMod n)) := inferInstance
    symm
    refine AddSubgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [← hvH]; exact AddSubgroup.zmultiples_le_of_mem ((mem_eig τ _ v).mpr hk)
    · rw [(eig_cyclic_card_eq τ s hτ hns hroot).2, hcard]

end Count

theorem stable_cyclic_card_eq_nuTwo (n : ℕ) [NeZero n]
    (τ : ZMod n × ZMod n →+ ZMod n × ZMod n) (hτ : ∀ v, τ (τ v) = -v)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ v : ZMod n × ZMod n, addOrderOf v = p ∧ ∀ k : ℕ, τ v ≠ k • v) :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n ∧ H.map τ = H}
      = nuTwo n := by
  have hτ' : ∀ v, τ (τ v) = (0 : ZMod n) • τ v - v := fun v => by rw [hτ, zero_smul, zero_sub]
  rw [card_stable_eq_card_roots τ 0 hτ' hns, nuTwo]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun k => by
    constructor <;> intro h <;> linear_combination h)

theorem stable_cyclic_card_eq_nuThree (n : ℕ) [NeZero n]
    (τ : ZMod n × ZMod n →+ ZMod n × ZMod n) (hτ : ∀ v, τ (τ v) + τ v + v = 0)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ v : ZMod n × ZMod n, addOrderOf v = p ∧ ∀ k : ℕ, τ v ≠ k • v) :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n ∧ H.map τ = H}
      = nuThree n := by
  have hτ' : ∀ v, τ (τ v) = (-1 : ZMod n) • τ v - v := fun v => by
    rw [neg_one_smul, ← sub_eq_zero, ← hτ v]; abel
  rw [card_stable_eq_card_roots τ (-1) hτ' hns, nuThree]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun k => by
    constructor <;> intro h <;> linear_combination h)

end
end Dubon2026.SourceQuadraticCyclicCount
