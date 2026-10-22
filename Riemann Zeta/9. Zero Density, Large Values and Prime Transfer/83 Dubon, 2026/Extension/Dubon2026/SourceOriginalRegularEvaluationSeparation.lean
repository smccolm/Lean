import Dubon2026.SourceOriginalDifferentialReadingLinear
import Dubon2026.SourceOriginalCanonicalDivisors

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> Jacobi inversion.
Center evaluations of original regular differentials separate those
differentials. The original place space is infinite by an injective chart
disk. Vanishing at every center would give positive order at every place,
contradicting the already proved finite support of any nonzero original
differential. This reuses finite support directly, without another
canonical-divisor construction or a derivative nonvanishing argument.
Adapted from S_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem place_infinite : Infinite (Place ℂ (modularFunctionFieldOver N ℂ)) := by
  let v := originalAnalyticPlace N UpperHalfPlane.I
  have hball : (ball (0 : ℂ) (placeRadius N v)).Infinite :=
    infinite_of_mem_nhds 0 (ball_mem_nhds _ (place_spec N v).1)
  have him := hball.image (placeFamily_injOn N v)
  exact Set.infinite_univ_iff.mp (him.mono (subset_univ _))

theorem readDifferential_center (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ]) :
    readDifferential N v ω 0 = originalPlaceEval N ℂ v (v.differentialCoeff ω) := by
  rw [readDifferential_eq_coefficient N v ω (mem_ball_self (place_spec N v).1), chartRead,
    (place_spec N v).2.1]

theorem eq_zero_of_forall_readDifferential_center
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (hz : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), readDifferential N v ω 0 = 0) : ω = 0 := by
  haveI := place_infinite N
  by_contra hne
  have hpos : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), 0 < v.ordDifferential ω := by
    intro v
    haveI := original_place_dCoordGenerates N ℂ v
    have hc : v.differentialCoeff ω ≠ 0 := by
      intro h
      apply hne
      rw [← v.differentialCoeff_smul_dCoord ω, h, zero_smul]
    have hv := hz v
    rw [readDifferential_center] at hv
    exact (originalPlaceEval_eq_zero_iff_ord_pos N ℂ v
      ((mem_original_regularDifferentials_iff N ℂ ω).mp hω v) hc).mp hv
  have hf : (univ : Set (Place ℂ (modularFunctionFieldOver N ℂ))).Finite :=
    (finite_original_differential_support N ℂ hne).subset (fun v _ => (hpos v).ne')
  exact (Set.finite_univ_iff.mp hf).not_infinite inferInstance

end
end Dubon2026.SourceFunctionField.OriginalChart
