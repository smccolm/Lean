import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.RingTheory.Finiteness.Basic

/-! DUB-17/18 -> continuous original rank-two representation -> finite
coefficient algebra and coordinate topology. A genuine rank-two linear
equivalence forces coefficient finiteness. Canonical module topology
then transports continuous vector actions to continuous invertible
two-by-two matrices. -/
namespace Dubon2026
noncomputable section

theorem finite_coefficients_of_rankTwo {K T V : Type*} [CommRing K] [CommRing T]
    [Algebra K T] [AddCommMonoid V] [Module K V] [Module.Finite K V]
    (e : V ≃ₗ[K] (Fin 2 → T)) : Module.Finite K T := by
  letI : Module.Finite K (Fin 2 → T) := Module.Finite.equiv e
  exact Module.Finite.of_pi (fun _ : Fin 2 => T) 0

theorem rankTwo_coordinate_action_continuous {K T V G : Type*}
    [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [CommRing T] [Algebra K T] [TopologicalSpace T] [IsModuleTopology K T]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V]
    [Monoid G] [TopologicalSpace G]
    (e : V ≃ₗ[K] (Fin 2 → T)) (ρ : G →* Module.End K V)
    (τ : G →* Module.End T (Fin 2 → T))
    (he : ∀ g x, τ g (e x) = e (ρ g x))
    (hρ : ∀ x, Continuous (fun g => ρ g x)) (y : Fin 2 → T) :
    Continuous (fun g => τ g y) := by
  letI := IsModuleTopology.toContinuousAdd K T
  have h := (IsModuleTopology.continuous_of_linearMap e.toLinearMap).comp (hρ (e.symm y))
  apply h.congr
  intro g
  exact (he g (e.symm y)).symm.trans (congrArg (τ g) (e.apply_symm_apply y))

/-- The invertible two-by-two matrices of a genuine coefficient-linear group action. -/
def rankTwoGeneralLinearRep {T G : Type*} [CommRing T] [Group G]
    (ρ : G →* Module.End T (Fin 2 → T)) : G →* Matrix.GeneralLinearGroup (Fin 2) T :=
  (((LinearMap.toMatrixAlgEquiv (Pi.basisFun T (Fin 2))).toRingHom.toMonoidHom).comp ρ).toHomUnits

open Matrix in
theorem rankTwoGeneralLinearRep_action {T G : Type*} [CommRing T] [Group G]
    (ρ : G →* Module.End T (Fin 2 → T)) (g : G) (y : Fin 2 → T) :
    (rankTwoGeneralLinearRep ρ g).val *ᵥ y = ρ g y := by
  simpa only [Pi.basisFun_repr] using
    LinearMap.toMatrix_mulVec_repr (Pi.basisFun T (Fin 2)) (Pi.basisFun T (Fin 2)) (ρ g) y

theorem rankTwoGeneralLinearRep_continuous {T G : Type*}
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : G →* Module.End T (Fin 2 → T))
    (hρ : ∀ y, Continuous (fun g => ρ g y)) : Continuous (rankTwoGeneralLinearRep ρ) := by
  have hm : Continuous (fun g => LinearMap.toMatrix (Pi.basisFun T (Fin 2))
      (Pi.basisFun T (Fin 2)) (ρ g)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simpa only [LinearMap.toMatrix_apply, Pi.basisFun_repr] using
      (continuous_apply i).comp (hρ (Pi.basisFun T (Fin 2) j))
  apply Units.continuous_iff.mpr
  constructor
  · exact hm
  · exact hm.comp continuous_inv

end
end Dubon2026
