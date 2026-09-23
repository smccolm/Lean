import TaoTrudgianYang2025.SargosQuarticSource
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Literal tuples of source integers and exact higher-power expansions. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

abbrev SargosMomentTuple (N p : ℕ) := Fin p → ↥(sargosSourceInterval N)

def sargosTupleCoefficient {N p : ℕ} (z : ℤ → ℂ) (t : SargosMomentTuple N p) : ℂ :=
  ∏ i, z (t i)

def sargosTupleSquareFrequency {N p : ℕ} (t : SargosMomentTuple N p) : ℝ :=
  ∑ i, ((t i : ℤ) : ℝ)^2

def sargosTupleFourthFrequency {N p : ℕ} (t : SargosMomentTuple N p) : ℝ :=
  ∑ i, ((t i : ℤ) : ℝ)^4

theorem sargos_character_finset_prod {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ S, fordAdditiveCharacter (f i)) =
      fordAdditiveCharacter (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [fordAdditiveCharacter]
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha,Finset.sum_insert ha,ih,fordAdditiveCharacter_add]

theorem sargosQuarticSum_pow_eq_tuple_sum (N p : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    (sargosQuarticSum N z α γ)^p =
      sargosPlanarSum (Finset.univ : Finset (SargosMomentTuple N p))
        (sargosTupleCoefficient z) sargosTupleSquareFrequency sargosTupleFourthFrequency α γ := by
  unfold sargosQuarticSum sargosPlanarSum
  rw [← Finset.sum_coe_sort,Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_mul_distrib,sargos_character_finset_prod]
  have he : (∑ i : Fin p, (((t i : ℤ) : ℝ)^2*α+((t i : ℤ) : ℝ)^4*γ)) =
      (∑ i : Fin p, ((t i : ℤ) : ℝ)^2)*α+
        (∑ i : Fin p, ((t i : ℤ) : ℝ)^4)*γ := by
    rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul]
  rw [he]
  rfl

theorem sargosQuarticSum_norm_even_eq_tuple_norm_sq
    (N p : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    ‖sargosQuarticSum N z α γ‖^(2*p) =
      ‖sargosPlanarSum (Finset.univ : Finset (SargosMomentTuple N p))
        (sargosTupleCoefficient z) sargosTupleSquareFrequency sargosTupleFourthFrequency α γ‖^2 := by
  rw [← sargosQuarticSum_pow_eq_tuple_sum,norm_pow,← pow_mul,Nat.mul_comm p 2]

theorem sargosTupleCoefficient_norm_le_one {N p : ℕ} {z : ℤ → ℂ}
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1) (t : SargosMomentTuple N p) :
    ‖sargosTupleCoefficient z t‖ ≤ 1 := by
  unfold sargosTupleCoefficient
  rw [norm_prod]
  calc
    _ ≤ ∏ _i : Fin p, (1 : ℝ) :=
      Finset.prod_le_prod (fun i hi => norm_nonneg _) (fun i hi => hz (t i) (t i).property)
    _ = _ := by simp

theorem sargosTupleCoefficient_one {N p : ℕ} (t : SargosMomentTuple N p) :
    sargosTupleCoefficient (fun _ => 1) t = 1 := by
  simp [sargosTupleCoefficient]

end TaoTrudgianYang2025
