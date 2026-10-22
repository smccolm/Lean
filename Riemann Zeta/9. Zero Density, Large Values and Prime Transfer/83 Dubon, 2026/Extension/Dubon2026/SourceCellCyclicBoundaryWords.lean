import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Chain
import Mathlib.Tactic

/-! DUB-17/18 -> original Abel-Jacobi -> raw matrix reciprocity -> polygon word.
These cyclic-list gluing lemmas are used when joining actual cells across
cotree edges. The unused source monotonicity helper is omitted; native list
chain extraction replaces the source reachability induction.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.CyclicBoundaryWords
noncomputable section
variable {α : Type*}

/-- Consecutive-letter relation including the last-to-first corner. -/
def Cyc (P : α → α → Prop) (l : List α) : Prop :=
  l.IsChain P ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, P x y

theorem cyc_shift {P : α → α → Prop} {a : α} {l : List α} (h : Cyc P (a :: l)) :
    Cyc P (l ++ [a]) := by
  obtain ⟨hchain, hwrap⟩ := h
  rw [List.isChain_cons] at hchain
  refine ⟨List.isChain_append.2 ⟨hchain.2, List.isChain_singleton _, ?_⟩, ?_⟩
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    cases l with
    | nil => simp at hx
    | cons b l' =>
      exact hwrap x (by simpa using hx) _ (by simp)
  · intro x hx y hy
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_def,
      Option.some.injEq] at hx
    subst hx
    cases l with
    | nil =>
      simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hwrap _ (by simp) _ (by simp)
    | cons b l' =>
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hchain.1 _ (by simp)

theorem cyc_rotate {P : α → α → Prop} : ∀ (n : ℕ) {l : List α}, Cyc P l → Cyc P (l.rotate n)
  | 0, l, h => by simpa using h
  | n + 1, [], h => by simpa using h
  | n + 1, a :: l, h => by
    rw [List.rotate_cons_succ]
    exact cyc_rotate n (cyc_shift h)

theorem cyc_getElem {P : α → α → Prop} {l : List α} (h : Cyc P l) (k : ℕ)
    (hk : k < l.length) :
    P (l[k]) (l[(k + 1) % l.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hk))) := by
  obtain ⟨hchain, hwrap⟩ := h
  by_cases hk1 : k + 1 < l.length
  · have := List.isChain_iff_getElem.1 hchain k hk1
    simpa [Nat.mod_eq_of_lt hk1] using this
  · have hk2 : k + 1 = l.length := by omega
    have hmod : (k + 1) % l.length = 0 := by rw [hk2, Nat.mod_self]
    have hne : l ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hx : l[k] ∈ l.getLast? := by
      rw [List.getLast?_eq_some_getLast hne, Option.mem_def, Option.some.injEq,
        List.getLast_eq_getElem]
      congr 1; omega
    have hy : l[(k + 1) % l.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)) ∈
        l.head? := by
      rw [List.head?_eq_some_head hne, Option.mem_def, Option.some.injEq, List.head_eq_getElem]
      congr 1; omega
    exact hwrap _ hx _ hy

theorem cyc_of_getElem {P : α → α → Prop} {l : List α}
    (h : ∀ (k : ℕ) (hk : k < l.length),
      P (l[k]) (l[(k + 1) % l.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)))) :
    Cyc P l := by
  refine ⟨List.isChain_iff_getElem.2 (fun i hi => ?_), fun x hx y hy => ?_⟩
  · have := h i (by omega)
    simpa [Nat.mod_eq_of_lt hi] using this
  · have hne : l ≠ [] := by rintro rfl; simp at hx
    have hpos : 0 < l.length := List.length_pos_of_ne_nil hne
    rw [List.getLast?_eq_some_getLast hne, Option.mem_def, Option.some.injEq] at hx
    rw [List.head?_eq_some_head hne, Option.mem_def, Option.some.injEq] at hy
    subst hx; subst hy
    have := h (l.length - 1) (by omega)
    have hmod : (l.length - 1 + 1) % l.length = 0 := by
      rw [Nat.sub_add_cancel hpos, Nat.mod_self]
    rw [List.getLast_eq_getElem, List.head_eq_getElem]
    simpa [hmod] using this

theorem cyc_splice {P P' : α → α → Prop} {a b : α} {l₁ l₂ : List α}
    (h₁ : Cyc P (a :: l₁)) (h₂ : Cyc P (b :: l₂))
    (hmono : ∀ x y, P x y → P' x y)
    (hja : ∀ x y, P' x a → P b y → P' x y)
    (hjb : ∀ x y, P' x b → P a y → P' x y) :
    Cyc P' (l₁ ++ l₂) := by
  obtain ⟨hc₁, hw₁⟩ := h₁
  obtain ⟨hc₂, hw₂⟩ := h₂
  rw [List.isChain_cons] at hc₁ hc₂

  have hlast₁ : ∀ x ∈ l₁.getLast?, P x a := fun x hx =>
    hw₁ x (by cases l₁ with | nil => simp at hx | cons c l => simpa using hx) a (by simp)
  have hlast₂ : ∀ x ∈ l₂.getLast?, P x b := fun x hx =>
    hw₂ x (by cases l₂ with | nil => simp at hx | cons c l => simpa using hx) b (by simp)
  have haa : l₁ = [] → P a a := fun h => by subst h; exact hw₁ a (by simp) a (by simp)
  have hbb : l₂ = [] → P b b := fun h => by subst h; exact hw₂ b (by simp) b (by simp)
  refine ⟨List.isChain_append.2 ⟨hc₁.2.imp (fun _ _ h => hmono _ _ h),
    hc₂.2.imp (fun _ _ h => hmono _ _ h), fun x hx y hy => hja x y (hmono _ _ (hlast₁ x hx))
      (hc₂.1 y hy)⟩, ?_⟩
  intro x hx y hy
  rw [List.getLast?_append] at hx
  rw [List.head?_append] at hy
  cases l₂ with
  | nil =>
    cases l₁ with
    | nil => simp at hx
    | cons c l =>
      simp only [List.getLast?_nil, Option.none_or, List.head?_nil, Option.or_none] at hx hy

      have h1 : P' x b := hja x b (hmono _ _ (hlast₁ x hx)) (hbb rfl)
      exact hjb x y h1 (hc₁.1 y hy)
  | cons d l =>
    have hx' : x ∈ (d :: l).getLast? := by
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil d l)] at hx ⊢
      simpa using hx
    have hxb : P x b := hlast₂ x hx'
    cases l₁ with
    | nil =>
      simp only [List.head?_nil, Option.none_or] at hy

      have h1 : P' x a := hjb x a (hmono _ _ hxb) (haa rfl)
      exact hja x y h1 (hc₂.1 y hy)
    | cons c l' =>
      simp only [List.head?_cons, Option.or_some, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hjb x c (hmono _ _ hxb) (hc₁.1 c (by simp))

theorem exists_rotate_cons {l : List α} {a : α} (ha : a ∈ l) :
    ∃ (n : ℕ) (l' : List α), l.rotate n = a :: l' := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
  refine ⟨i, (l.rotate i).tail, ?_⟩
  have hlen : 0 < (l.rotate i).length := by rw [List.length_rotate]; omega
  have hne : l.rotate i ≠ [] := List.ne_nil_of_length_pos hlen
  conv_lhs => rw [← List.cons_head_tail hne]
  congr 1
  rw [List.head_eq_getElem, List.getElem_rotate]
  congr 1
  simp [Nat.mod_eq_of_lt hi]

theorem exists_list_of_rtg {r : α → α → Prop} {a b : α} (h : Relation.ReflTransGen r a b) :
    ∃ cs : List α, cs.head? = some a ∧ cs.getLast? = some b ∧ cs.IsChain r := by
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen h
  exact ⟨a :: l, rfl, by rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hlast], hl⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.CyclicBoundaryWords
