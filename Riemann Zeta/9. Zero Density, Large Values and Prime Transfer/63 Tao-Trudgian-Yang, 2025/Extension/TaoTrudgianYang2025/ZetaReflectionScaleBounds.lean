import TaoTrudgianYang2025.ZetaReflectionFrequencyBlocks

/-! Physical scale comparisons for the literal reflected frequency annulus. -/

noncomputable section
open Complex MeasureTheory Set
open scoped Classical BigOperators
namespace TaoTrudgianYang2025

theorem reflection_floor_scale_bounds {M : ℝ} (hM : 4 ≤ M) :
    2 ≤ Nat.floor M ∧ M/2 ≤ (Nat.floor M : ℝ) ∧ (Nat.floor M : ℝ) ≤ M := by
  have hu := Nat.lt_floor_add_one M
  have hl := Nat.floor_le (show 0 ≤ M by linarith)
  have ht : (2 : ℝ) ≤ Nat.floor M := by linarith
  exact ⟨by exact_mod_cast ht,by linarith,hl⟩

theorem reflection_ceil_le_eight_floor {M : ℝ} (hM : 4 ≤ M) :
    Nat.ceil (4*M) ≤ 8*Nat.floor M := by
  apply Nat.ceil_le.mpr
  have h := (reflection_floor_scale_bounds hM).2.1
  push_cast
  linarith

theorem reflection_dyadic_scale_bounds {M : ℝ} (hM : 4 ≤ M) (i : Fin 3) :
    1 < 2^i.val*Nat.floor M ∧
      M/2 ≤ ((2^i.val*Nat.floor M : ℕ) : ℝ) ∧
      ((2^i.val*Nat.floor M : ℕ) : ℝ) ≤ 4*M := by
  obtain ⟨hn,hl,hr⟩ := reflection_floor_scale_bounds hM
  fin_cases i <;> norm_num <;> constructor
  all_goals first | omega | constructor <;> nlinarith

theorem zetaReflectionCommonInterval_eq_scaled (T N : ℝ) :
    zetaReflectionCommonInterval T N =
      Finset.Icc (Nat.floor (T/(4*Real.pi*N))+1)
        (Nat.ceil (4*(T/(4*Real.pi*N)))) := by
  unfold zetaReflectionCommonInterval
  congr 2
  ring

end TaoTrudgianYang2025
