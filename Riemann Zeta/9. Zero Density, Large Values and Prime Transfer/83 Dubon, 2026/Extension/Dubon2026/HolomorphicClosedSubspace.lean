import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Analytic continuation of genuine closed Hilbert-subspace membership -/

namespace Dubon2026

noncomputable section
open Filter Set
open scoped Topology

/-- A holomorphic Hilbert-valued function locally in an original closed subspace stays in that same subspace throughout its connected domain. -/
theorem differentiableOn_mem_closedSubmodule {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (F : ℂ → V) {U : Set ℂ}
    (hF : DifferentiableOn ℂ F U) (hU : IsOpen U) (hconn : IsPreconnected U)
    (p : Submodule ℂ V) (hp : IsClosed (p : Set V)) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hlocal : ∀ᶠ z in 𝓝 z₀, F z ∈ p) : ∀ z ∈ U, F z ∈ p := by
  letI : CompleteSpace p := hp.isComplete.completeSpace_coe
  let T : V →L[ℂ] V := ContinuousLinearMap.id ℂ V - p.starProjection
  have hd : DifferentiableOn ℂ (fun z => T (F z)) U := by
    intro z hz
    exact T.differentiableAt.comp_differentiableWithinAt z (hF z hz)
  have he : (fun z => T (F z)) =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hlocal] with z hz
    change F z - p.starProjection (F z) = 0
    rw [p.starProjection_eq_self_iff.mpr hz, sub_self]
  have hall := (hd.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀ he
  intro z hz
  have hz' : F z - p.starProjection (F z) = 0 := hall hz
  exact p.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz').symm

end
end Dubon2026
