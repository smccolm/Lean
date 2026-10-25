import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> cover Abel converse -> prescribed reciprocity coordinates.
The same finite reindexing transports the bilinear expression and its one
common integer correction. Divisors and differentials remain arbitrary
parameters, so this can consume the actual cover identity as a whole. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section

theorem reindex_third_kind_reciprocity
    {E K I X R : Type*} [Fintype K]
    (s : Finset E) (e : K ≃ {l // l ∈ s}) (Q : E → E → ℤ)
    (z : E → I → ℂ) (f : E → R → ℂ) (A : X → I → ℂ) (scale : ℂ)
    (H₁ : R → Prop) (H₂ : X → R → Prop) (H₃ : X → Prop)
    (h : ∀ x r, H₁ r → H₂ x r → H₃ x → ∃ c : E → ℤ, ∀ i,
      (∑ j ∈ s, ∑ l ∈ s, (Q j l : ℂ) * z j i * f l r) =
        scale * (A x i + ∑ l ∈ s, (c l : ℂ) * z l i)) :
    ∀ x r, H₁ r → H₂ x r → H₃ x → ∃ c : K → ℤ, ∀ i,
      (∑ j, ∑ l, (Q (e j).1 (e l).1 : ℂ) * z (e j).1 i * f (e l).1 r) =
        scale * (A x i + ∑ l, (c l : ℂ) * z (e l).1 i) := by
  have hre : ∀ g : E → ℂ, (∑ k, g (e k).1) = ∑ l ∈ s, g l := by
    intro g
    rw [Equiv.sum_comp e (fun l => g l.1)]
    exact Finset.sum_coe_sort _ g
  have hdouble : ∀ g : E → E → ℂ,
      (∑ k, ∑ l, g (e k).1 (e l).1) = ∑ j ∈ s, ∑ l ∈ s, g j l := by
    intro g
    rw [hre (fun j => ∑ l, g j (e l).1)]
    exact Finset.sum_congr rfl fun j _ => hre (g j)
  intro x r h₁ h₂ h₃
  obtain ⟨c, hc⟩ := h x r h₁ h₂ h₃
  refine ⟨fun k => c (e k).1, fun i => ?_⟩
  rw [hdouble (fun j l => (Q j l : ℂ) * z j i * f l r),
    hre (fun l => (c l : ℂ) * z l i)]
  exact hc i

end
end Dubon2026.SourceFunctionField.CellGeometry
