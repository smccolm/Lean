import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> cover Abel converse -> prescribed cycle coordinates.
The existing finite reindexing argument is performed before specializing
the loop domain to the actual cover. Both common-coefficient quantifiers
and arbitrary residue terms are retained exactly. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section

theorem reindex_integer_generation
    {E K R X : Type*} {Γ : X → Type*} [Fintype K]
    (s : Finset E) (e : K ≃ {l // l ∈ s})
    (f : (x : X) → Γ x → R → ℂ) (z : E → R → ℂ)
    (h : ∀ x g, ∃ a : E → ℤ, ∀ r, f x g r = ∑ l ∈ s, (a l : ℂ) * z l r) :
    ∀ x g, ∃ a : K → ℤ, ∀ r, f x g r = ∑ k, (a k : ℂ) * z (e k).1 r := by
  intro x g
  obtain ⟨a, ha⟩ := h x g
  refine ⟨fun k => a (e k).1, fun r => ?_⟩
  rw [ha r, Equiv.sum_comp e (fun l => (a l.1 : ℂ) * z l.1 r)]
  exact (Finset.sum_coe_sort _ _).symm

theorem reindex_integer_generation_with_residues
    {E K R X W : Type*} {Γ : X → Type*} [Fintype K]
    (s : Finset E) (e : K ≃ {l // l ∈ s})
    (f : (x : X) → Γ x → R → ℂ) (z : E → R → ℂ) (res : W → R → ℂ)
    (A : (x : X) → Γ x → Prop) (H₁ H₂ : R → Prop)
    (h : ∀ x g, A x g → ∃ (a : E → ℤ) (w : W), ∀ r, H₁ r → H₂ r →
      f x g r = (∑ l ∈ s, (a l : ℂ) * z l r) + res w r) :
    ∀ x g, A x g → ∃ (a : K → ℤ) (w : W), ∀ r, H₁ r → H₂ r →
      f x g r = (∑ k, (a k : ℂ) * z (e k).1 r) + res w r := by
  intro x g hg
  obtain ⟨a, w, ha⟩ := h x g hg
  refine ⟨fun k => a (e k).1, w, fun r h₁ h₂ => ?_⟩
  rw [ha r h₁ h₂, Equiv.sum_comp e (fun l => (a l.1 : ℂ) * z l.1 r)]
  exact congrArg (fun v => v + res w r) (Finset.sum_coe_sort s (fun l => (a l : ℂ) * z l r)).symm

end
end Dubon2026.SourceFunctionField.CellGeometry
