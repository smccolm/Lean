import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Actual compact orbits with open stabilizer have finite original span -/

namespace Dubon2026

noncomputable section

/-- A genuine compact group orbit is finite when an actual open subgroup fixes its original vector. -/
theorem compactOrbit_finite_of_open_stabilizer {G V : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) (hH : IsOpen (H : Set G)) (v : V)
    (hv : ∀ g ∈ H, ρ g v = v) : Set.Finite (Set.range (fun g => ρ g v)) := by
  letI : Finite (G ⧸ H) := H.quotient_finite_of_isOpen hH
  let F : G ⧸ H → V := Quotient.lift (fun g => ρ g v) (by
    intro a b hab
    have hh : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have he := congrArg (ρ a) (hv (a⁻¹ * b) hh)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at he
    exact he.symm)
  have hs : Set.range (fun g => ρ g v) ⊆ Set.range F := by
    rintro _ ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk g, rfl⟩
  exact (Set.finite_range F).subset hs

/-- The original span of a compact orbit with genuine open stabilizer is finite dimensional. -/
theorem compactOrbitSpan_finite_of_open_stabilizer {G V : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) (hH : IsOpen (H : Set G)) (v : V)
    (hv : ∀ g ∈ H, ρ g v = v) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun g => ρ g v))) :=
  FiniteDimensional.span_of_finite ℂ (compactOrbit_finite_of_open_stabilizer ρ H hH v hv)

end
end Dubon2026
