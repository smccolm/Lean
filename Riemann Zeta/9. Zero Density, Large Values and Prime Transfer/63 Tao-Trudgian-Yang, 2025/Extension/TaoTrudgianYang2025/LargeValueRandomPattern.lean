import TaoTrudgianYang2025.FiniteRandomCoefficients
import TaoTrudgianYang2025.LargeValueRandomLattice

/-! Genuine random-sign source patterns at the square-root threshold. -/

open Finset

noncomputable section

namespace TaoTrudgianYang2025

theorem exists_half_largeValuePattern (N : ℕ) (hN : 2 ≤ N)
    (T : ℝ) (hT : 0 < T) :
    ∃ P : LargeValuePattern, P.N = (N:ℝ) ∧ P.T = T ∧
      P.V = Real.sqrt (((N:ℝ)+1)/2) ∧ T ≤ 12*(P.ordinates.card:ℝ) := by
  classical
  let I := Icc N (2*N)
  have hI : I.Nonempty := ⟨N,mem_Icc.mpr ⟨le_refl _,by omega⟩⟩
  have hIc : I.card = N+1 := by dsimp [I]; simp; omega
  have hIcr : (I.card:ℝ) = (N:ℝ)+1 := by exact_mod_cast hIc
  have hw (t : ℝ) (_ht : t ∈ largeValueLattice T) (n : ℕ) (hn : n ∈ I) :
      Complex.normSq (dirichletPhase n t) = 1 := by
    have hnpos : 0 < n := by have := (mem_Icc.mp hn).1; omega
    have hnorm : ‖dirichletPhase n t‖ = 1 := by
      simpa [dirichletPhase] using
        Complex.norm_natCast_cpow_of_pos hnpos (-(Complex.I*(t:ℂ)))
    rw [Complex.normSq_eq_norm_sq,hnorm]
    norm_num
  obtain ⟨a,ha,hcount⟩ := exists_bounded_coefficients_many_large I hI
    (largeValueLattice T) (fun t n => dirichletPhase n t) hw
  let W := {t ∈ largeValueLattice T |
    (I.card:ℝ)/2 ≤ Complex.normSq (∑ n ∈ I, a n*dirichletPhase n t)}
  let P : LargeValuePattern :=
    { N := N
      scale := N
      T := T
      V := Real.sqrt (((N:ℝ)+1)/2)
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
      ordinates_in_interval := fun t ht =>
        largeValueLattice_in_interval hT.le ((mem_filter.mp ht).1)
      ordinates_oneSeparated := by
        intro t ht u hu htu
        exact largeValueLattice_oneSeparated T t (mem_filter.mp ht).1
          u (mem_filter.mp hu).1 htu
      large := by
        intro t ht
        have h := (mem_filter.mp ht).2
        rw [hIcr,Complex.normSq_eq_norm_sq] at h
        exact (Real.sqrt_le_iff).mpr ⟨norm_nonneg _,h⟩ }
  refine ⟨P,rfl,rfl,rfl,?_⟩
  exact (largeValueLattice_card_lower T).trans hcount

end TaoTrudgianYang2025
