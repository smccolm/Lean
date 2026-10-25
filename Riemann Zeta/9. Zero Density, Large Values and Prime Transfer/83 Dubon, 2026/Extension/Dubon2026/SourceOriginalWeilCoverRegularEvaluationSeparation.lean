import Dubon2026.SourceOriginalWeilCoverDifferentialReadingLinear
import Dubon2026.SourceOriginalWeilCoverCanonicalSupport

/-! DUB-17/18 -> auxiliary point division -> cover Jacobi inversion.
Adapt the native original-curve evaluation and inverse-function arguments
to the literal Kummer cover, using actual residue readings and Abel vectors.
Finite coordinate support replaces any numerical genus assumption.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem place_infinite : Infinite (Place ℂ (EE)) := by
  let v : Place ℂ EE := Classical.choice (nonempty_cover_place N n r)
  have hball : (ball (0 : ℂ) (placeRadius N n r A hr hrA v)).Infinite :=
    infinite_of_mem_nhds 0 (ball_mem_nhds _ (place_spec N n r A hr hrA v).1)
  have him := hball.image (placeChart N n r A hr hrA v).symm.injOn
  exact Set.infinite_univ_iff.mp (him.mono (subset_univ _))

theorem readDifferential_center (v : Place ℂ (EE))
    (ω : Ω[EE⁄ℂ]) :
    readDifferential N n r A hr hrA v ω 0 = v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n r v) (v.differentialCoeff ω) := by
  rw [readDifferential_eq_coefficient N n r A hr hrA v ω (mem_ball_self (place_spec N n r A hr hrA v).1)]
  simp only [chartRead, (place_spec N n r A hr hrA v).2.1]

theorem eq_zero_of_forall_readDifferential_center
    (ω : Ω[EE⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (EE))
    (hz : ∀ v : Place ℂ (EE), readDifferential N n r A hr hrA v ω 0 = 0) : ω = 0 := by
  haveI := place_infinite N n r A hr hrA
  by_contra hne
  have hpos : ∀ v : Place ℂ (EE), 0 < v.ordDifferential ω := by
    intro v
    haveI := cover_place_dCoordGenerates N n r v
    have hc : v.differentialCoeff ω ≠ 0 := by
      intro h
      apply hne
      rw [← v.differentialCoeff_smul_dCoord ω, h, zero_smul]
    have hv := hz v
    rw [readDifferential_center] at hv
    exact (v.rationalEval_eq_zero_iff_ord_pos (originalWeilKummerCover_residue_bijective N ℂ n r v)
      ((mem_cover_regularDifferentials_iff N n r ω).mp hω v) hc).mp hv
  have hf : (univ : Set (Place ℂ (EE))).Finite :=
    (finite_cover_differential_support N n r hne).subset (fun v _ => (hpos v).ne')
  exact (Set.finite_univ_iff.mp hf).not_infinite inferInstance

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
