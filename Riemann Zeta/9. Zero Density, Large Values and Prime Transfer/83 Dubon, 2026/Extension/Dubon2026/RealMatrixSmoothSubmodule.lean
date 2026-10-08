import Dubon2026.RealGroupSmoothCoordinates

/-! # Actual smooth vectors for genuine entrywise smooth real matrix families -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

/-- The genuine complex subspace of vectors whose original real matrix orbits are smooth in every real normed parameter space. -/
def realMatrixSmoothSubmodule (ρ : Representation ℂ SL(2, ℝ) V) : Submodule ℂ V where
  carrier := {v | ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : E → SL(2, ℝ)), (∀ i j : Fin 2, ContDiff ℝ ∞ (fun w => h w i j)) →
      ContDiff ℝ ∞ (fun w => ρ (h w) v)}
  zero_mem' := by
    intro E _ _ h hh
    simpa only [map_zero] using (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : V)))
  add_mem' := by
    intro v w hv hw E _ _ h hh
    simpa only [map_add] using (hv E h hh).add (hw E h hh)
  smul_mem' := by
    intro a v hv E _ _ h hh
    simpa only [map_smul] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : E => a)).smul (hv E h hh)

/-- Right multiplication by an actual fixed matrix preserves the smoothness of all original matrix entries. -/
theorem realSL2_right_mul_entries_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : SL(2, ℝ)) (h : E → SL(2, ℝ))
    (hh : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun w => h w i j)) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun w => (h w * g) i j) := by
  change ContDiff ℝ ∞ (fun w => ∑ l : Fin 2, h w i l * g l j)
  exact ContDiff.sum (fun l _ => (hh i l).mul contDiff_const)

/-- The actual smooth-vector subspace is invariant under every original real-group translate. -/
theorem realMatrixSmoothSubmodule_invariant (ρ : Representation ℂ SL(2, ℝ) V)
    (v : V) (hv : v ∈ realMatrixSmoothSubmodule ρ) (g : SL(2, ℝ)) :
    ρ g v ∈ realMatrixSmoothSubmodule ρ := by
  intro E _ _ h hh
  have hs := hv E (fun w => h w * g) (realSL2_right_mul_entries_contDiff g h hh)
  simpa only [map_mul, Module.End.mul_apply] using hs

end
end Dubon2026
