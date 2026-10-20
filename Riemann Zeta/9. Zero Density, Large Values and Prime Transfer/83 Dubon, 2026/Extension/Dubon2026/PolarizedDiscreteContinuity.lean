import Dubon2026.PolarizedCocycleLift
import Dubon2026.PolarizedPointTopology
import Dubon2026.ContinuousRepresentationCohomology
import Mathlib.Topology.Instances.TrivSqZeroExt

/-! Continuity of the actual polarized first-order fiber over discrete
residual coefficients. The source residual field is finite and discrete;
the existing coordinate topology and generic continuous cohomology suffice
without developing a separate analytic deformation framework. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [DiscreteTopology R]

/-- The source coordinate topology is discrete for a discrete original coefficient ring. -/
instance polarizedPointDiscreteTopology : DiscreteTopology (PolarizedGaloisGroup ι R) :=
  (polarizedPointHomeomorph (R := R) (ι := ι)).symm.discreteTopology

variable {G : Type} [Group G] [TopologicalSpace G]

/-- Continuous original polarized lifts have continuous full adjoint cocycles. -/
theorem polarizedFirstOrderCocycle_continuous (ρ : G →* PolarizedGaloisGroup ι R)
    (hρ : Continuous ρ) (τ : PolarizedFirstOrderLift ρ) (hτ : Continuous τ.val) :
    Continuous (fun g => polarizedFirstOrderCocycle ρ τ g) := by
  letI : DiscreteTopology (DualNumber R) := inferInstanceAs (DiscreteTopology (R × R))
  have h : Continuous (fun z : PolarizedGaloisGroup ι (DualNumber R) × PolarizedGaloisGroup ι R =>
      dualMatrixInfinitesimal (z.1 * (polarizedDualConstant (R := R) (ι := ι) z.2)⁻¹).left.1) :=
    continuous_of_discreteTopology
  simp_rw [polarizedFirstOrderCocycle_apply]
  exact Continuous.comp (f := fun g : G => (τ.val g, ρ g)) h (hτ.prodMk hρ)

/-- Reconstructing the actual polarized lift preserves continuity of its original cocycle. -/
theorem polarizedFirstOrderLiftFromCocycle_continuous
    (ρ : G →* PolarizedGaloisGroup ι R) (hρ : Continuous ρ)
    (c : groupCohomology.cocycles₁ (polarizedAdjointRep ρ))
    (hc : Continuous (fun g => c g)) :
    Continuous (polarizedFirstOrderLiftFromCocycle ρ c).val := by
  have h : Continuous (fun z : Matrix ι ι R × PolarizedGaloisGroup ι R =>
      polarizedStrictPoint z.1 * polarizedDualConstant (R := R) (ι := ι) z.2) :=
    continuous_of_discreteTopology
  change Continuous (fun g => (polarizedFirstOrderLiftFromCocycle ρ c).val g)
  simp_rw [polarizedFirstOrderLiftFromCocycle_apply]
  exact Continuous.comp (f := fun g : G => (c g, ρ g)) h (hc.prodMk hρ)

/-- Continuity of an original fixed-similitude lift is equivalent to continuity of its actual cocycle. -/
theorem polarizedFirstOrderLift_continuous_iff
    (ρ : G →* PolarizedGaloisGroup ι R) (hρ : Continuous ρ)
    (τ : PolarizedFirstOrderLift ρ) :
    Continuous τ.val ↔ Continuous (fun g => polarizedFirstOrderCocycle ρ τ g) := by
  constructor
  · exact polarizedFirstOrderCocycle_continuous ρ hρ τ
  · intro hc
    have h := polarizedFirstOrderLiftFromCocycle_continuous ρ hρ (polarizedFirstOrderCocycle ρ τ) hc
    rwa [polarizedFirstOrderLiftFromCocycle_cocycle] at h

/-- The source full adjoint has the actual joint continuity required by the existing continuous cohomology. -/
theorem polarizedAdjointAction_continuous (ρ : G →* PolarizedGaloisGroup ι R)
    (hρ : Continuous ρ) :
    Continuous (fun z : G × Matrix ι ι R => (polarizedAdjointRep ρ).ρ z.1 z.2) := by
  have h : Continuous (fun z : PolarizedGaloisGroup ι R × Matrix ι ι R =>
      polarizedAdjointRepresentation (R := R) (ι := ι) z.1 z.2) := continuous_of_discreteTopology
  change Continuous (fun z : G × Matrix ι ι R => polarizedAdjointRepresentation (ρ z.1) z.2)
  exact Continuous.comp (f := fun z : G × Matrix ι ι R => (ρ z.1, z.2)) h
    ((hρ.comp continuous_fst).prodMk continuous_snd)

end
end Dubon2026
