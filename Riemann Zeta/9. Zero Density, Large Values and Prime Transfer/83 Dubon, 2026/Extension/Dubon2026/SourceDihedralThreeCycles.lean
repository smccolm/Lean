import Mathlib.Tactic

/-! DUB-17/18 -> characteristic-three wild genus equality -> exceptional
fiber census. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_Function_orbitCensus_of_dihedralThree_relations. Only the exact finite-set
census is developed; its concrete elliptic and modular inputs remain to
be discharged by the actual consumer. -/
namespace Dubon2026.SourceDihedralThree
variable {X : Type*} (a b : X → X)
  (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b (b x)) = x) (hab : ∀ x, a (b x) = b (b (a x)))

include hb in
theorem b_injective : Function.Injective b := fun x y h => by
  have := congrArg (fun z => b (b z)) h
  simpa [hb] using this

include hb hab in

theorem abb (x : X) : a (b (b x)) = b (a x) := by
  have h := hab (b x)
  rw [hab x] at h
  rw [h, hb]

include hb hab in
theorem ba (x : X) : b (a x) = a (b (b x)) := (abb a b hb hab x).symm

variable [DecidableEq X]

/-- The orbit of a point under the order-three generator. -/
def T (x : X) : Finset X := {x, b x, b (b x)}

theorem mem_T {x y : X} : y ∈ T b x ↔ y = x ∨ y = b x ∨ y = b (b x) := by
  simp [T]

theorem self_mem_T (x : X) : x ∈ T b x := (mem_T b).mpr (Or.inl rfl)

include hb in
theorem T_b (x : X) : T b (b x) = T b x := by
  ext y
  simp only [mem_T, hb]
  tauto

include hb in
theorem T_eq_of_mem {x y : X} (h : y ∈ T b x) : T b y = T b x := by
  rcases (mem_T b).mp h with rfl | rfl | rfl
  · rfl
  · exact T_b b hb x
  · rw [T_b b hb, T_b b hb]

include hb in

theorem T_eq_or_disjoint (x y : X) : T b y = T b x ∨ Disjoint (T b x) (T b y) := by
  by_cases h : Disjoint (T b x) (T b y)
  · exact Or.inr h
  · left
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨z, hzx, hzy⟩ := h
    rw [← T_eq_of_mem b hb hzy, T_eq_of_mem b hb hzx]

theorem card_T_of_fix {x : X} (h : b x = x) : (T b x).card = 1 := by
  have : T b x = {x} := by
    ext y; simp [mem_T, h]
  rw [this, Finset.card_singleton]

include hb in
theorem card_T_of_not_fix {x : X} (h : b x ≠ x) : (T b x).card = 3 := by
  have h1 : b x ≠ x := h
  have h2 : b (b x) ≠ x := by
    intro h2
    apply h
    have := congrArg b h2
    rw [hb] at this
    exact this.symm
  have h3 : b (b x) ≠ b x := by
    intro h3
    exact h ((b_injective b hb) h3)
  rw [T, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simpa using h3.symm
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1.symm, h2.symm⟩

include hb in
theorem card_T (x : X) : ((T b x).card = 1 ∧ b x = x) ∨ ((T b x).card = 3 ∧ b x ≠ x) := by
  by_cases h : b x = x
  · exact Or.inl ⟨card_T_of_fix b h, h⟩
  · exact Or.inr ⟨card_T_of_not_fix b hb h, h⟩

omit [DecidableEq X] in
include ha hb hab in
theorem bfix_a_iff (x : X) : b (a x) = a x ↔ b x = x := by
  constructor
  · intro h

    have h' : b (a (a x)) = a (a x) := by
      rw [ba a b hb hab (a x)]
      have hbb : b (b (a x)) = a x := by rw [h, h]
      rw [hbb]
    rwa [ha] at h'
  · intro h
    rw [ba a b hb hab x, h, h]

include ha hb hab in
theorem card_T_a (x : X) : (T b (a x)).card = (T b x).card := by
  rcases card_T b hb x with ⟨h1, hx⟩ | ⟨h3, hx⟩
  · rw [h1, card_T_of_fix b ((bfix_a_iff a b ha hb hab x).mpr hx)]
  · rw [h3, card_T_of_not_fix b hb (fun h => hx ((bfix_a_iff a b ha hb hab x).mp h))]

include hb hab in

theorem mem_T_a_iff {x y : X} : y ∈ T b (a x) ↔ y = a x ∨ y = a (b x) ∨ y = a (b (b x)) := by
  have h1 : b (a x) = a (b (b x)) := ba a b hb hab x
  have h2 : b (b (a x)) = a (b x) := (hab x).symm
  rw [mem_T, h2, h1]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)


end Dubon2026.SourceDihedralThree
