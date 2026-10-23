import Dubon2026.SourceOriginalFinitePathModularPeriods
import Dubon2026.SourceOriginalConstructedRegularPeriods
import Dubon2026.SourceOriginalDissectionSkeletonRegularity

/-! DUB-17/18 -> original Picard-period Hecke comparison -> exact lattice
identification. The existing marked cell construction places the finite
support of j inside cell interiors. Its proved generating loops therefore
avoid the poles of j. Their actual periods belong to the modular period
lattice by the preceding local comparison; the already proved integer
generation theorem handles every original loop. No new covering or
homotopy theory, or assumption about chosen loop representatives, is needed.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve Set KaehlerDifferential CellGeometry
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology placeChartedSpace

theorem exists_original_finite_loop_generation {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (P : Place ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked)
      (T Ts : Finset A.dissection.ιE)
      (γ : (j : A.dissection.ιE) →
        Path (A.dissection.vert (A.dissection.ends j).1)
          (A.dissection.vert (A.dissection.ends j).1)),
      (∀ j t, jOver N ℂ ∈ (γ j t).toValuationSubring) ∧
      DissectionPeriods.RegularCycleGeneration A.dissection (fun i => (b i).val) T Ts γ := by
  classical
  let S := (finite_original_divisor_support N ℂ (jOver N ℂ)).toFinset
  obtain ⟨Marked, A, T, Ts, Z, hcent, hsep, ht, hts, hd, hc, hw, hword,
    hz, hdelta, hzero, hdec, γ, hγs, hγi, C₀, V, Ψ, J, hP₀, hV, hΨ, hJ, hJ0, hΨ0,
    hcir, hgen, hW, hR⟩ := exists_original_regular_cycle_generation.{0, 0} P S
      (fun i => (b i).val) (fun i => (b i).property)
  have hinter : ∀ v ∈ S, ∃ C : A.dissection.ιC, v ∈ (A.dissection.cell C).interior' := by
    intro v hv
    obtain ⟨i, hi, _⟩ := hcent v (mem_insert_of_mem P hv)
    exact ⟨i, hi⟩
  have hfinite : ∀ j t, jOver N ℂ ∈ (γ j t).toValuationSubring := by
    intro j t
    have hn : γ j t ∉ S := fun hS =>
      A.dissection.pole_not_mem_skeleton S hinter hS (hγs j t)
    have he : (γ j t).ord (jOver N ℂ) = 0 := by
      by_contra he
      apply hn
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using he
    exact (γ j t).mem_of_ord_nonneg (he ▸ le_rfl)
  exact ⟨Marked, A, T, Ts, γ, hfinite, hR⟩

theorem original_loop_period_mem_cusp_lattice {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (P : Place ℂ (modularFunctionFieldOver N ℂ)) (δ : Path P P) :
    (fun i => pathIntegral N (b i).val δ) ∈ originalCuspPeriodLattice N b := by
  classical
  obtain ⟨Marked, A, T, Ts, γ, hfinite, hR⟩ := exists_original_finite_loop_generation N b P
  have hloop := fun j => original_finite_loop_period_mem_cusp_lattice N b (γ j) (hfinite j)
  obtain ⟨a, ha⟩ := hR P δ
  have hs : (∑ j ∈ (T ∪ Ts)ᶜ, a j • (fun i => pathIntegral N (b i).val (γ j))) ∈
      originalCuspPeriodLattice N b :=
    (originalCuspPeriodLattice N b).sum_mem fun j _ =>
      (originalCuspPeriodLattice N b).smul_mem (a j) (hloop j)
  have he : (fun i => pathIntegral N (b i).val δ) =
      ∑ j ∈ (T ∪ Ts)ᶜ, a j • (fun i => pathIntegral N (b i).val (γ j)) := by
    funext i
    simpa only [Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul] using ha i
  exact he ▸ hs

theorem pathPeriodLattice_le_originalCuspPeriodLattice {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    pathPeriodLattice N (fun i => (b i).val) ≤ originalCuspPeriodLattice N b := by
  apply Submodule.span_le.mpr
  rintro _ ⟨P, δ, rfl⟩
  exact original_loop_period_mem_cusp_lattice N b P δ

theorem originalCuspPeriodLattice_eq_pathPeriodLattice {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    originalCuspPeriodLattice N b = pathPeriodLattice N (fun i => (b i).val) :=
  le_antisymm (originalCuspPeriodLattice_le_pathPeriodLattice N b)
    (pathPeriodLattice_le_originalCuspPeriodLattice N b)

end
end Dubon2026.SourceFunctionField.OriginalChart
