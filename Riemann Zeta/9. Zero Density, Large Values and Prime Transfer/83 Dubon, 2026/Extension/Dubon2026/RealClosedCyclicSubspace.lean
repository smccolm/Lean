import Dubon2026.RealSmoothInfinitesimalOperator
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Original closed cyclic subspaces and their genuine infinitesimal stability -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup Filter
open scoped MatrixGroups ContDiff Topology

/-- The closed span of an original bounded group orbit is invariant under the same original action. -/
theorem closedCyclicSpan_invariant {G V : Type*} [Group G] [NormedAddCommGroup V]
    [NormedSpace ℂ V] (ρ : Representation ℂ G V) (L : G → V →L[ℂ] V)
    (hL : ∀ g v, L g v = ρ g v) (v : V) (g : G) (w : V)
    (hw : w ∈ (Submodule.span ℂ (Set.range (fun h => ρ h v))).topologicalClosure) :
    ρ g w ∈ (Submodule.span ℂ (Set.range (fun h => ρ h v))).topologicalClosure := by
  let p := Submodule.span ℂ (Set.range (fun h => ρ h v))
  have hs : ∀ u ∈ p, L g u ∈ p.topologicalClosure := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        rw [hL, ← Module.End.mul_apply, ← map_mul]
        exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g * h, rfl⟩)
    | zero => simpa only [map_zero] using p.topologicalClosure.zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using p.topologicalClosure.add_mem ihx ihy
    | smul c x hx ih => simpa only [map_smul] using p.topologicalClosure.smul_mem c ih
  have he := closure_minimal hs (p.isClosed_topologicalClosure.preimage (L g).continuous) hw
  exact (hL g w) ▸ he

/-- The original norm derivative of a curve in a closed complex subspace belongs to that same subspace. -/
theorem deriv_mem_closedSubmodule {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] (p : Submodule ℂ V) (hp : IsClosed (p : Set V))
    (C : ℝ → V) (hC : ∀ t, C t ∈ p) (t : ℝ) (hd : DifferentiableAt ℝ C t) : deriv C t ∈ p := by
  apply hp.mem_of_tendsto hd.hasDerivAt.tendsto_slope_zero
  exact Eventually.of_forall (fun u => (p.restrictScalars ℝ).smul_mem u⁻¹ (p.sub_mem (hC _) (hC _)))

/-- A genuine closed real-invariant subspace is stable under every original smooth-curve infinitesimal. -/
theorem realMatrixSmoothInfinitesimal_mem_closedInvariant {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    (ρ : Representation ℂ SL(2, ℝ) V) (L : SL(2, ℝ) → V →L[ℝ] V)
    (hL : ∀ g v, L g v = ρ g v) (p : Submodule ℂ V) (hp : IsClosed (p : Set V))
    (hi : ∀ g v, v ∈ p → ρ g v ∈ p) (c : ℝ → SL(2, ℝ))
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j))
    (v : realMatrixSmoothSubmodule ρ) (hv : v.val ∈ p) :
    (realMatrixSmoothInfinitesimal ρ L hL c hc v).val ∈ p := by
  exact deriv_mem_closedSubmodule p hp (fun t => ρ (c t) v.val) (fun t => hi (c t) v.val hv) 0
    (((contDiff_infty.mp (v.property ℝ c hc) 1).differentiable (by norm_num)) 0)

end
end Dubon2026
