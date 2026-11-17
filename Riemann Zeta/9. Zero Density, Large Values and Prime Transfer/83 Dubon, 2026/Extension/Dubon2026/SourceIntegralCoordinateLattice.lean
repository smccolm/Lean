import Dubon2026.CompactOrbitSpanFinite
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! DUB-17/18 -> original all-weight residual realization -> open coordinate lattice.
The literal integer-coordinate inclusion has finite range and open image.
This supplies the compact-orbit finite-generation lemma's two hypotheses. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable (E : Type*) [Field E] [ValuativeRel E]

/-- The literal inclusion of two integral coordinates into the coefficient field. -/
def sourceIntegralCoordinateMap : (Fin 2 → 𝒪[E]) →ₗ[𝒪[E]] (Fin 2 → E) :=
  LinearMap.pi fun i => (Algebra.linearMap 𝒪[E] E).comp (LinearMap.proj i)

/-- The coordinate lattice given by the range of the integral-coordinate inclusion. -/
def sourceIntegralCoordinateLattice : Submodule 𝒪[E] (Fin 2 → E) :=
  (sourceIntegralCoordinateMap E).range

theorem mem_sourceIntegralCoordinateLattice (v : Fin 2 → E) :
    v ∈ sourceIntegralCoordinateLattice E ↔ ∀ i, v i ∈ (ValuativeRel.valuation E).integer := by
  constructor
  · rintro ⟨x, rfl⟩ i
    exact (x i).property
  · intro h
    exact ⟨fun i => ⟨v i, h i⟩, rfl⟩

theorem sourceIntegralCoordinateLattice_fg : (sourceIntegralCoordinateLattice E).FG :=
  Submodule.fg_range (sourceIntegralCoordinateMap E)

theorem sourceIntegralCoordinateLattice_open [UniformSpace E] [IsNonarchimedeanLocalField E] :
    IsOpen (sourceIntegralCoordinateLattice E : Set (Fin 2 → E)) := by
  have he : (sourceIntegralCoordinateLattice E : Set (Fin 2 → E)) =
      ⋂ i : Fin 2, {v | v i ∈ (ValuativeRel.valuation E).integer} := by
    ext v
    simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe,
      mem_sourceIntegralCoordinateLattice]
  rw [he]
  exact isOpen_iInter_of_finite fun i =>
    (ValuativeRel.valuation E).isOpen_integer.preimage (continuous_apply i)

end
end Dubon2026
