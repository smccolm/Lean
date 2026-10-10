import Dubon2026.ContinuousImageTopologicalGenerators
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Finite continuous representation sets from original finite topological generators -/

namespace Dubon2026

noncomputable section

variable {G H : Type*} [Group G] [Group H]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [T2Space H]

/-- Original continuous homomorphisms agreeing on an actual finite topological generating set agree on the entire original group. -/
theorem continuousMonoidHom_eq_of_topological_generators
    (S : Finset G) (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤)
    (f g : G →ₜ* H) (hfg : ∀ x ∈ S, f x = g x) : f = g := by
  have hclosed : IsClosed (f.toMonoidHom.eqLocus g.toMonoidHom : Set G) :=
    isClosed_eq f.continuous g.continuous
  have hgen : Subgroup.closure (S : Set G) ≤ f.toMonoidHom.eqLocus g.toMonoidHom :=
    MonoidHom.eqOn_closure hfg
  have hall := Subgroup.topologicalClosure_minimal _ hgen hclosed
  rw [hS] at hall
  apply DFunLike.ext
  intro x
  exact hall (Subgroup.mem_top x)

/-- The actual continuous homomorphisms into any finite Hausdorff target form a finite set when the original group has genuine finitely many topological generators. -/
theorem finite_continuousMonoidHom_of_topological_generators
    [Finite H] (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤) :
    Finite (G →ₜ* H) := by
  apply Finite.of_injective (fun f : G →ₜ* H => fun x : S => f x.val)
  intro f g hfg
  apply continuousMonoidHom_eq_of_topological_generators S hS f g
  intro x hx
  exact congrFun hfg ⟨x, hx⟩

end
end Dubon2026
