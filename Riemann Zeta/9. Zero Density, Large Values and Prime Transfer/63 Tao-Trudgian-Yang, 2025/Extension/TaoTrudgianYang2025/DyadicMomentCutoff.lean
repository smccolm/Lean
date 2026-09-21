import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-!
# Dyadic cutoff choice and its logarithmic counting cost

A power of two is chosen within a factor two of any real cutoff at least
one. The square of its block count is bounded by any positive power of
that dyadic length, with the constant chosen before the length.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem exists_dyadic_cutoff {X : ℝ} (hX : 1 ≤ X) :
    ∃ M : ℕ, X ≤ (2:ℝ)^M ∧ (2:ℝ)^M ≤ 2*X := by
  obtain ⟨m,hm,hupper⟩ := exists_nat_pow_near hX (by norm_num : (1:ℝ)<2)
  refine ⟨m+1,hupper.le,?_⟩
  rw [pow_succ']
  exact mul_le_mul_of_nonneg_left hm (by norm_num)

theorem exists_dyadic_count_sq_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ M : ℕ, ((M:ℝ)+1)^2 ≤ D*((2:ℝ)^M)^ε := by
  let a : ℝ := ε/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := 1+1/(a*Real.log 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C^2,pow_pos hC 2,?_⟩
  intro M
  have hp : 1 ≤ ((2:ℝ)^M)^a :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) ha.le
  have hl := Real.log_le_rpow_div (by positivity : (0:ℝ) ≤ (2:ℝ)^M) ha
  rw [Real.log_pow] at hl
  have hm : (M:ℝ) ≤ ((2:ℝ)^M)^a/(a*Real.log 2) := by
    apply (le_div_iff₀ (mul_pos ha hlog)).mpr
    have h := (le_div_iff₀ ha).mp hl
    nlinarith
  have hcount : (M:ℝ)+1 ≤ C*((2:ℝ)^M)^a := by
    calc
      _ ≤ ((2:ℝ)^M)^a/(a*Real.log 2)+((2:ℝ)^M)^a := add_le_add hm hp
      _ = _ := by dsimp [C]; ring
  calc
    _ ≤ (C*((2:ℝ)^M)^a)^2 :=
      pow_le_pow_left₀ (by positivity) hcount 2
    _ = _ := by
      rw [mul_pow,← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ (2:ℝ)^M)]
      congr 2
      dsimp [a]
      norm_num

end TaoTrudgianYang2025
