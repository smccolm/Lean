import TaoTrudgianYang2025.RobertSargosInitialDyadic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Explicit logarithmic constants in the source dyadic A-process estimate. -/

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem nat_clog_two_le_twice_log (H : ℕ) (hH : 2 ≤ H) :
    (Nat.clog 2 H:ℝ) ≤ 2*(Real.log H/Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmono : Real.log 2 ≤ Real.log H :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hH)
  have hratio : 1 ≤ Real.log H/Real.log 2 :=
    (le_div_iff₀ hlog).mpr (by simpa only [one_mul] using hmono)
  have hc := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
    (show (1:ℝ) ≤ H by exact_mod_cast (show 1 ≤ H by omega)))
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num,Real.natCeil_logb_natCast] at hc
  simp only [Real.logb,Nat.cast_ofNat] at hc
  linarith

theorem exists_robertSargos_initial_dyadic_log (f : ℝ → ℝ) (M H : ℕ)
    (hH : 2 ≤ H) (hHM : H ≤ M) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      ‖∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)‖^2 ≤
        15*(Real.log H/Real.log 2)*
          ((M:ℝ)^2/H+((M:ℝ)/H)*‖robertSargosSymmetricSum f M k‖) := by
  obtain ⟨k,hk,hkH,hs⟩ := exists_robertSargos_initial_dyadic f M H hH hHM
  refine ⟨k,hk,hkH,?_⟩
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmono : Real.log 2 ≤ Real.log H :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hH)
  have hratio : 1 ≤ Real.log H/Real.log 2 :=
    (le_div_iff₀ hlog).mpr (by simpa only [one_mul] using hmono)
  have hc := nat_clog_two_le_twice_log H hH
  have h₁ : 3+6*(Nat.clog 2 H:ℝ) ≤ 15*(Real.log H/Real.log 2) := by linarith
  have h₂ : 6*(Nat.clog 2 H:ℝ) ≤ 15*(Real.log H/Real.log 2) := by linarith
  calc
    _ ≤ (3+6*(Nat.clog 2 H:ℝ))*(M:ℝ)^2/H+
        (6*(M:ℝ)*(Nat.clog 2 H:ℝ)/H)*‖robertSargosSymmetricSum f M k‖ := hs
    _ = (3+6*(Nat.clog 2 H:ℝ))*((M:ℝ)^2/H)+
        (6*(Nat.clog 2 H:ℝ))*(((M:ℝ)/H)*‖robertSargosSymmetricSum f M k‖) := by ring
    _ ≤ (15*(Real.log H/Real.log 2))*((M:ℝ)^2/H)+
        (15*(Real.log H/Real.log 2))*(((M:ℝ)/H)*‖robertSargosSymmetricSum f M k‖) :=
      add_le_add (mul_le_mul_of_nonneg_right h₁ (by positivity))
        (mul_le_mul_of_nonneg_right h₂ (by positivity))
    _ = _ := by ring

end TaoTrudgianYang2025
