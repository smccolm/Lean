import Dubon2026.SourceMeromorphicLeadingCoefficient

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. Meromorphic functions with a fixed effective
pole bound satisfy a linear relation once their number exceeds its degree
plus one. Removing one leading coefficient reduces the allowed pole degree;
compact holomorphic constancy supplies degree zero. This is the analytic
dimension bound required to identify functions with original field elements.
Adapted from S_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.MeromorphicCompact
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- The actual meromorphic germ and prescribed lower order bound at every point. -/
def Bdd (D : M →₀ ℕ) (ψ : M → ℂ) : Prop :=
  ∀ x : M, MeromorphicAt (rd ψ x) (ctr x) ∧
    ((-(D x : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (rd ψ x) (ctr x)

variable {D : M →₀ ℕ}

theorem Bdd.zero : Bdd D (0 : M → ℂ) := fun x => by
  refine ⟨MeromorphicAt.const 0 (ctr x), ?_⟩
  have : rd (0 : M → ℂ) x = fun _ => (0 : ℂ) := rfl
  rw [this, meromorphicOrderAt_const]
  simp

theorem Bdd.add {ψ₁ ψ₂ : M → ℂ} (h₁ : Bdd D ψ₁) (h₂ : Bdd D ψ₂) : Bdd D (ψ₁ + ψ₂) := fun x => by
  have e : rd (ψ₁ + ψ₂) x = rd ψ₁ x + rd ψ₂ x := rfl
  refine ⟨by rw [e]; exact (h₁ x).1.add (h₂ x).1, ?_⟩
  rw [e]
  exact (le_min (h₁ x).2 (h₂ x).2).trans (meromorphicOrderAt_add (h₁ x).1 (h₂ x).1)

theorem Bdd.smul {ψ : M → ℂ} (a : ℂ) (h : Bdd D ψ) : Bdd D (a • ψ) := fun x => by
  by_cases ha : a = 0
  · rw [ha, zero_smul]; exact Bdd.zero x
  have e : rd (a • ψ) x = (fun _ => a) * rd ψ x := by
    funext z; simp [rd, smul_eq_mul]
  have hc : MeromorphicAt (fun _ : ℂ => a) (ctr x) := MeromorphicAt.const a _
  refine ⟨by rw [e]; exact hc.mul (h x).1, ?_⟩
  rw [e, meromorphicOrderAt_mul hc (h x).1, meromorphicOrderAt_const, if_neg ha, zero_add]
  exact (h x).2

theorem Bdd.sub {ψ₁ ψ₂ : M → ℂ} (h₁ : Bdd D ψ₁) (h₂ : Bdd D ψ₂) : Bdd D (ψ₁ - ψ₂) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ₂]
  exact h₁.add (h₂.smul (-1))

theorem Bdd.sum {ι : Type*} (s : Finset ι) {ψ : ι → M → ℂ} (c : ι → ℂ) (h : ∀ i, Bdd D (ψ i)) :
    Bdd D (∑ i ∈ s, c i • ψ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Bdd.zero
  | insert i s hi ih => rw [Finset.sum_insert hi]; exact ((h i).smul (c i)).add ih

theorem Bdd.of_lead_eq_zero {ψ : M → ℂ} (h : Bdd D ψ) {x₀ : M} (hx₀ : 1 ≤ D x₀)
    (h0 : lead (D x₀) (rd ψ x₀) (ctr x₀) = 0) : Bdd (D - Finsupp.single x₀ 1) ψ := by
  classical
  intro x
  refine ⟨(h x).1, ?_⟩
  rw [Finsupp.tsub_apply]
  by_cases hx : x₀ = x
  · subst hx
    rw [Finsupp.single_eq_same]
    obtain ⟨k, hk⟩ : ∃ k, D x₀ = k + 1 := ⟨D x₀ - 1, by omega⟩
    rw [hk] at h0 ⊢
    rw [Nat.add_sub_cancel]
    exact le_order_of_lead_eq_zero (h x₀).1 (by rw [← hk]; exact (h x₀).2) h0
  · rw [Finsupp.single_apply, if_neg hx, Nat.sub_zero]
    exact (h x).2


end
end Dubon2026.SourceFunctionField.MeromorphicCompact
