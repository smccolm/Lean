import TaoTrudgianYang2025.LargeValueBlockVariance
import TaoTrudgianYang2025.LargeValueRandomLattice

/-! Genuine coherent-block source patterns with exact physical parameters. -/

open Finset

noncomputable section

namespace TaoTrudgianYang2025

theorem exists_block_largeValuePattern (N L : ℕ) (hN : 2 ≤ N)
    (hL : 0 < L) (hLN : L ≤ N) (T : ℝ) (hT : 0 < T) :
    ∃ P : LargeValuePattern, P.N = (N:ℝ) ∧ P.T = T ∧
      P.V = Real.sqrt ((N:ℝ)*(L:ℝ)/16) ∧
      min T ((N:ℝ)/(2*(L:ℝ))) ≤ 12*(P.ordinates.card:ℝ) := by
  classical
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLp : (0:ℝ) < L := by exact_mod_cast hL
  let R := min T ((N:ℝ)/(2*(L:ℝ)))
  have hR : 0 < R := lt_min hT (div_pos hNp (by positivity))
  let I := Icc N (2*N)
  have hvar (t : ℝ) (ht : t ∈ largeValueLattice R) :
      (N:ℝ)*(L:ℝ)/8 ≤ ((largeValueBlockBasis N L).map
        (fun b => Complex.normSq (∑ n ∈ I, b n*dirichletPhase n t))).sum := by
    have hp := largeValueLattice_in_interval hR.le ht
    exact largeValueBlockBasis_variance (by omega) hL hLN hp.1
      (hp.2.trans (min_le_right _ _))
  obtain ⟨a,ha,hcount⟩ := exists_bounded_sign_coefficients_of_variance I
    (largeValueBlockBasis N L) (largeValueLattice R) (fun t n => dirichletPhase n t)
    ((N:ℝ)*(L:ℝ)/8) (by positivity) (largeValueBlockBasis_norm_sum N L) hvar
  have he : ((N:ℝ)*(L:ℝ)/8)/2 = (N:ℝ)*(L:ℝ)/16 := by ring
  rw [he] at hcount
  let W := {t ∈ largeValueLattice R |
    (N:ℝ)*(L:ℝ)/16 ≤ Complex.normSq (∑ n ∈ I, a n*dirichletPhase n t)}
  let P : LargeValuePattern :=
    { N := N
      scale := N
      T := T
      V := Real.sqrt ((N:ℝ)*(L:ℝ)/16)
      coeff := a
      indices := I
      intervalLeft := 0
      intervalRight := T
      ordinates := W
      N_eq_scale := rfl
      one_lt_N := by exact_mod_cast (show 1 < N by omega)
      T_pos := hT
      V_pos := Real.sqrt_pos.mpr (by positivity)
      mem_indices_iff := by
        intro n
        simp only [I,mem_Icc]
        norm_cast
      coeff_one_bounded := fun n _ => ha n
      interval_length := sub_zero T
      ordinates_in_interval := by
        intro t ht
        have hp := largeValueLattice_in_interval hR.le (mem_filter.mp ht).1
        exact ⟨hp.1,hp.2.trans (min_le_left _ _)⟩
      ordinates_oneSeparated := by
        intro t ht u hu htu
        exact largeValueLattice_oneSeparated R t (mem_filter.mp ht).1
          u (mem_filter.mp hu).1 htu
      large := by
        intro t ht
        have h := (mem_filter.mp ht).2
        rw [Complex.normSq_eq_norm_sq] at h
        exact (Real.sqrt_le_iff).mpr ⟨norm_nonneg _,h⟩ }
  exact ⟨P,rfl,rfl,rfl,(largeValueLattice_card_lower R).trans hcount⟩

end TaoTrudgianYang2025

