import Dubon2026.FirstOrderDeformationEquiv
import Mathlib.Topology.Instances.TrivSqZeroExt
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Units

/-! # Continuity for the original first-order lift and adjoint cocycle constructions -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalGroup G] in
/-- A continuous original first-order lift has a continuous actual adjoint cocycle. -/
theorem matrixFirstOrderCocycle_continuous (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    Continuous (fun g => matrixFirstOrderCocycle ρ τ g) := by
  have hs : Continuous (fun g => dualMatrixSnd (τ.val g).val) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact TrivSqZeroExt.continuous_snd.comp ((continuous_apply j).comp
      ((continuous_apply i).comp ((Units.continuous_val (M := Matrix ι ι (DualNumber R))).comp hτ)))
  have hr (g : G) : dualMatrixReduction (τ.val g) = ρ g :=
    DFunLike.congr_fun τ.property g
  change Continuous (fun g => dualMatrixSnd (τ.val g).val *
    ((dualMatrixReduction (τ.val g))⁻¹).val)
  simp_rw [hr]
  exact hs.mul ((Units.continuous_val (M := Matrix ι ι R)).comp hρ.inv)

omit [IsTopologicalGroup G] in
/-- The original reconstructed matrix entries are continuous when the original representation and cocycle are continuous. -/
theorem firstOrderLiftFromCocycle_continuous_val (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (c : groupCohomology.cocycles₁ (matrixAdjointRep ρ))
    (hc : Continuous (fun g => c g)) :
    Continuous (fun g => ((firstOrderLiftFromCocycle ρ c).val g).val) := by
  have hv := (Units.continuous_val (M := Matrix ι ι R)).comp hρ
  have he := hc.mul hv
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun g => ((ρ g).val i j, (c g * (ρ g).val) i j) : G → DualNumber R)
  exact ((continuous_apply j).comp ((continuous_apply i).comp hv)).prodMk
    ((continuous_apply j).comp ((continuous_apply i).comp he))

/-- The entire genuine reconstructed representation is continuous, including its inverse matrix coordinate. -/
theorem firstOrderLiftFromCocycle_continuous (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (c : groupCohomology.cocycles₁ (matrixAdjointRep ρ))
    (hc : Continuous (fun g => c g)) :
    Continuous (firstOrderLiftFromCocycle ρ c).val := by
  apply Units.continuous_iff.mpr
  refine ⟨firstOrderLiftFromCocycle_continuous_val ρ hρ c hc, ?_⟩
  have hi := (firstOrderLiftFromCocycle_continuous_val ρ hρ c hc).comp continuous_inv
  simpa only [map_inv] using hi

/-- For the original continuous representation, a genuine first-order lift is continuous exactly when its actual adjoint cocycle is continuous. -/
theorem matrixFirstOrderLift_continuous_iff (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (τ : MatrixFirstOrderLift ρ) :
    Continuous τ.val ↔ Continuous (fun g => matrixFirstOrderCocycle ρ τ g) := by
  constructor
  · exact matrixFirstOrderCocycle_continuous ρ hρ τ
  · intro hc
    have h := firstOrderLiftFromCocycle_continuous ρ hρ (matrixFirstOrderCocycle ρ τ) hc
    rwa [firstOrderLiftFromCocycle_cocycle] at h

end
end Dubon2026
