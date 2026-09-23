import TaoTrudgianYang2025.SargosInitialSixthMoment
import TaoTrudgianYang2025.SargosShiftedNearCount

/-! Actual ordered triples in 1 through N and their square/fourth-power frequencies. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

abbrev SargosInitialMomentTuple (N p : ℕ) := Fin p → ↥(Finset.Ioc (0:ℤ) N)

def sargosInitialTuplePower {N p : ℕ} (k : ℕ) (t : SargosInitialMomentTuple N p) : ℤ :=
  ∑ i, (t i : ℤ)^k

theorem card_sargosInitialMomentTuple (N p : ℕ) :
    Fintype.card (SargosInitialMomentTuple N p) = N^p := by
  simp [SargosInitialMomentTuple]

theorem sargosInitialQuarticSum_pow_eq_tuple_sum (N p : ℕ) (α γ : ℝ) :
    (sargosInitialQuarticSum N (fun _ => 1) α γ)^p =
      sargosPlanarSum (Finset.univ : Finset (SargosInitialMomentTuple N p)) (fun _ => 1)
        (fun t => (sargosInitialTuplePower 2 t : ℝ))
        (fun t => (sargosInitialTuplePower 4 t : ℝ)) α γ := by
  unfold sargosInitialQuarticSum sargosPlanarSum
  simp only [one_mul]
  rw [← Finset.sum_coe_sort,Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [sargos_character_finset_prod]
  congr 1
  simp only [sargosInitialTuplePower,Int.cast_sum,Int.cast_pow]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul]

theorem sargosInitialQuarticSum_norm_even_eq_tuple_norm_sq (N p : ℕ) (α γ : ℝ) :
    ‖sargosInitialQuarticSum N (fun _ => 1) α γ‖^(2*p) =
      ‖sargosPlanarSum (Finset.univ : Finset (SargosInitialMomentTuple N p)) (fun _ => 1)
        (fun t => (sargosInitialTuplePower 2 t : ℝ))
        (fun t => (sargosInitialTuplePower 4 t : ℝ)) α γ‖^2 := by
  rw [← sargosInitialQuarticSum_pow_eq_tuple_sum,norm_pow,← pow_mul,Nat.mul_comm p 2]

def sargosInitialSextupleWindow (N : ℕ) (c B : ℝ) :
    Finset (SargosInitialMomentTuple N 3 × SargosInitialMomentTuple N 3) :=
  Finset.univ.filter (fun q =>
    sargosInitialTuplePower 2 q.1 = sargosInitialTuplePower 2 q.2 ∧
    c ≤ ((sargosInitialTuplePower 4 q.1-sargosInitialTuplePower 4 q.2 : ℤ):ℝ) ∧
    ((sargosInitialTuplePower 4 q.1-sargosInitialTuplePower 4 q.2 : ℤ):ℝ) ≤ c+B)

theorem sargosInitialSextupleWindow_subset_shifted (N : ℕ) (c B : ℝ) :
    sargosInitialSextupleWindow N c B ⊆
      sargosShiftedNearPairs Finset.univ
        (fun t : SargosInitialMomentTuple N 3 => (sargosInitialTuplePower 2 t : ℝ))
        (fun t => (sargosInitialTuplePower 4 t : ℝ)) 0 c 1 B := by
  intro q hq
  have hp := (Finset.mem_filter.mp hq).2
  apply Finset.mem_filter.mpr
  refine ⟨by simp,?_,?_⟩
  · simp [hp.1]
  · have hlow := hp.2.1
    have hupp := hp.2.2
    push_cast at hlow hupp
    rw [abs_of_nonneg (by linarith only [hlow])]
    linarith only [hupp]

end TaoTrudgianYang2025

