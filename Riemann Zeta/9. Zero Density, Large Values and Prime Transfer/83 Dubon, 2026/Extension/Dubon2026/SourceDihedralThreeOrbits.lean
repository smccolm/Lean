import Dubon2026.SourceDihedralThreeCycles

/-! DUB-17/18 -> characteristic-three wild genus equality -> exceptional
fiber census. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_Function_orbitCensus_of_dihedralThree_relations. Only the exact finite-set
census is developed; its concrete elliptic and modular inputs remain to
be discharged by the actual consumer. -/
namespace Dubon2026.SourceDihedralThree
variable {X : Type*} [DecidableEq X] (a b : X → X)
  (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b (b x)) = x) (hab : ∀ x, a (b x) = b (b (a x)))

/-- The union of the two possible order-three orbits. -/
def six (x : X) : Finset X := T b x ∪ T b (a x)

include hb hab in
theorem mem_six {x y : X} :
    y ∈ six a b x ↔ (y = x ∨ y = a x ∨ y = b x ∨ y = b (b x) ∨ y = a (b x) ∨ y = a (b (b x))) := by
  rw [six, Finset.mem_union, mem_T, mem_T_a_iff a b hb hab]
  tauto

include ha hb hab in

theorem card_six (x : X) :
    (T b (a x) = T b x ∧ (six a b x).card = (T b x).card) ∨
      (Disjoint (T b x) (T b (a x)) ∧ (six a b x).card = 2 * (T b x).card) := by
  rcases T_eq_or_disjoint b hb x (a x) with h | h
  · left
    refine ⟨h, ?_⟩
    rw [six, h, Finset.union_idempotent]
  · right
    refine ⟨h, ?_⟩
    rw [six, Finset.card_union_of_disjoint h, card_T_a a b ha hb hab, two_mul]

include ha hb hab in
theorem card_six_mem (x : X) :
    (six a b x).card = 1 ∨ (six a b x).card = 2 ∨ (six a b x).card = 3 ∨ (six a b x).card = 6 := by
  rcases card_six a b ha hb hab x with ⟨-, h⟩ | ⟨-, h⟩ <;>
    rcases card_T b hb x with ⟨h1, -⟩ | ⟨h3, -⟩
  · exact Or.inl (by rw [h, h1])
  · exact Or.inr (Or.inr (Or.inl (by rw [h, h3])))
  · exact Or.inr (Or.inl (by rw [h, h1]))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, h3])))

include ha hb hab in

theorem odd_iff (x : X) :
    ((six a b x).card = 1 ∨ (six a b x).card = 3) ↔ a x ∈ T b x := by
  constructor
  · intro hodd
    rcases card_six a b ha hb hab x with ⟨h, -⟩ | ⟨-, h⟩
    · rw [← h]; exact self_mem_T b (a x)
    · exfalso
      rw [h] at hodd
      rcases hodd with h' | h' <;> omega
  · intro hmem
    have hT : T b (a x) = T b x := T_eq_of_mem b hb hmem
    have : (six a b x).card = (T b x).card := by rw [six, hT, Finset.union_idempotent]
    rw [this]
    rcases card_T b hb x with ⟨h1, -⟩ | ⟨h3, -⟩
    · exact Or.inl h1
    · exact Or.inr h3

include ha hb hab in

theorem small_iff (x : X) :
    ((six a b x).card = 1 ∨ (six a b x).card = 2) ↔ b x = x := by
  constructor
  · intro hsmall
    by_contra hne
    have h3 := card_T_of_not_fix b hb hne
    rcases card_six a b ha hb hab x with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h, h3] at hsmall <;> omega
  · intro hfix
    have h1 := card_T_of_fix b hfix
    rcases card_six a b ha hb hab x with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl (by rw [h, h1])
    · exact Or.inr (by rw [h, h1])

variable [Fintype X] {ι : Type*} [DecidableEq ι] (c : X → ι)
  (hc : ∀ x y, c x = c y ↔
    (y = x ∨ y = a x ∨ y = b x ∨ y = b (b x) ∨ y = a (b x) ∨ y = a (b (b x))))

include hb hab hc in
theorem fibre_eq_six (x : X) : (Finset.univ.filter fun y => c y = c x) = six a b x := by
  ext y
  rw [Finset.mem_filter, mem_six a b hb hab]
  simp only [Finset.mem_univ, true_and]
  rw [eq_comm, hc x y]

include hb hab hc in
omit [Fintype X] [DecidableEq ι] in
theorem c_eq_iff_mem_six (x y : X) : c y = c x ↔ y ∈ six a b x := by
  rw [mem_six a b hb hab, eq_comm, hc x y]


end Dubon2026.SourceDihedralThree
