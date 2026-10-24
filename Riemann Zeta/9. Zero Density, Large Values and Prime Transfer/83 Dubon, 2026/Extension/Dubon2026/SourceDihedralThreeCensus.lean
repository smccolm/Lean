import Dubon2026.SourceDihedralThreeOrbits

/-! DUB-17/18 -> characteristic-three wild genus equality -> exceptional
fiber census. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_Function_orbitCensus_of_dihedralThree_relations. Only the exact finite-set
census is developed; its concrete elliptic and modular inputs remain to
be discharged by the actual consumer. -/
namespace Dubon2026.SourceDihedralThree
theorem orbit_census
    {X : Type*} [Fintype X] [DecidableEq X] (a b : X → X)
    (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b (b x)) = x) (hab : ∀ x, a (b x) = b (b (a x)))
    {ι : Type*} [DecidableEq ι] (c : X → ι)
    (hc : ∀ x y, c x = c y ↔
      (y = x ∨ y = a x ∨ y = b x ∨ y = b (b x) ∨ y = a (b x) ∨ y = a (b (b x))))
    (S : Finset ι) (hS : ∀ p, p ∈ S ↔ ∃ x, c x = p) :
    (∀ x, (Finset.univ.filter fun y => c y = c x).card = 1 ∨
        (Finset.univ.filter fun y => c y = c x).card = 2 ∨
        (Finset.univ.filter fun y => c y = c x).card = 3 ∨
        (Finset.univ.filter fun y => c y = c x).card = 6) ∧
    (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1 ∨
        (Finset.univ.filter fun y => c y = p).card = 3).card =
      (Finset.univ.filter fun x => a x = x).card ∧
    (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1).card +
        2 * (S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 2).card =
      (Finset.univ.filter fun x => b x = x).card := by
  have hfib := fibre_eq_six a b hb hab c hc
  refine ⟨fun x => by rw [hfib]; exact card_six_mem a b ha hb hab x, ?_, ?_⟩
  ·
    symm
    apply Finset.card_bij (fun x _ => c x)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨(hS _).mpr ⟨x, rfl⟩, ?_⟩
      rw [hfib, odd_iff a b ha hb hab]
      rw [hx.2]; exact self_mem_T b x
    · intro x hx x' hx' hxx'
      rw [Finset.mem_filter] at hx hx'
      have hmem : x' ∈ six a b x := (c_eq_iff_mem_six a b hb hab c hc x x').mp hxx'.symm
      have hT : T b (a x) = T b x := by rw [hx.2]
      rw [six, hT, Finset.union_idempotent, mem_T] at hmem
      rcases hmem with h | h | h
      · exact h.symm
      ·
        have hfix : a (b x) = b x := by rw [← h]; exact hx'.2
        rw [hab x, hx.2] at hfix

        have : b x = x := b_injective b hb hfix
        rw [h, this]
      · have hfix : a (b (b x)) = b (b x) := by rw [← h]; exact hx'.2
        rw [abb a b hb hab x, hx.2] at hfix

        have h1 : x = b x := b_injective b hb hfix
        rw [h, ← h1, ← h1]
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨x, rfl⟩ := (hS p).mp hp.1
      have hodd : (six a b x).card = 1 ∨ (six a b x).card = 3 := by rw [← hfib]; exact hp.2
      have hmem : a x ∈ T b x := (odd_iff a b ha hb hab x).mp hodd
      rcases (mem_T b).mp hmem with h | h | h
      · exact ⟨x, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩, rfl⟩
      ·
        refine ⟨b (b x), ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [abb a b hb hab x, h]
        · exact (c_eq_iff_mem_six a b hb hab c hc x _).mpr
            ((mem_six a b hb hab).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      ·
        refine ⟨b x, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hab x, h, hb]
        · exact (c_eq_iff_mem_six a b hb hab c hc x _).mpr
            ((mem_six a b hb hab).mpr (Or.inr (Or.inr (Or.inl rfl))))
  ·
    set S1 := S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 1 with hS1
    set S2 := S.filter fun p => (Finset.univ.filter fun y => c y = p).card = 2 with hS2
    have hdisj : Disjoint S1 S2 := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      omega

    have hunion : (Finset.univ.filter fun x => b x = x) =
        (S1 ∪ S2).biUnion fun p => Finset.univ.filter fun y => c y = p := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_union,
        hS1, hS2]
      constructor
      · intro hfix
        refine ⟨c x, ?_, rfl⟩
        have hsmall := (small_iff a b ha hb hab x).mpr hfix
        rw [← hfib] at hsmall
        rcases hsmall with h | h
        · exact Or.inl ⟨(hS _).mpr ⟨x, rfl⟩, h⟩
        · exact Or.inr ⟨(hS _).mpr ⟨x, rfl⟩, h⟩
      · rintro ⟨p, hp, rfl⟩
        apply (small_iff a b ha hb hab x).mp
        rw [← hfib]
        rcases hp with ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr h
    rw [hunion, Finset.card_biUnion]
    · rw [Finset.sum_union hdisj]
      have h1 : ∑ p ∈ S1, (Finset.univ.filter fun y => c y = p).card = ∑ p ∈ S1, 1 :=
        Finset.sum_congr rfl fun p hp => by rw [hS1, Finset.mem_filter] at hp; exact hp.2
      have h2 : ∑ p ∈ S2, (Finset.univ.filter fun y => c y = p).card = ∑ p ∈ S2, 2 :=
        Finset.sum_congr rfl fun p hp => by rw [hS2, Finset.mem_filter] at hp; exact hp.2
      rw [h1, h2, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
    · intro p _ q _ hpq
      rw [Function.onFun, Finset.disjoint_filter]
      intro x _ h1 h2
      exact hpq (h1.symm.trans h2)

end Dubon2026.SourceDihedralThree
