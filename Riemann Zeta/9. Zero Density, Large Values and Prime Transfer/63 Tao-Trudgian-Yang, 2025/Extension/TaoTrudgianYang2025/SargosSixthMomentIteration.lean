import TaoTrudgianYang2025.SargosSixthMomentExponents

/-! Iterating the proved exponent improvement to every positive epsilon. -/

noncomputable section

namespace TaoTrudgianYang2025

def sargosSixthIterationExponent (n : ℕ) : ℝ := 3/(1+3*(n:ℝ))

theorem sargosSixthIterationExponent_nonneg (n : ℕ) :
    0 ≤ sargosSixthIterationExponent n := by
  dsimp [sargosSixthIterationExponent]
  positivity

theorem sargosSixthIterationExponent_step (n : ℕ) :
    sargosSixthExponentStep (sargosSixthIterationExponent n) =
      sargosSixthIterationExponent (n+1) := by
  have hd : 0 < 1+3*(n:ℝ) := by positivity
  have he : 0 < 1+3*((n:ℝ)+1) := by positivity
  dsimp [sargosSixthExponentStep,sargosSixthIterationExponent]
  push_cast
  field_simp
  ring

theorem sargosSixthMomentExponent_iterate (n : ℕ) :
    SargosSixthMomentExponent (sargosSixthIterationExponent n) := by
  induction n with
  | zero => simpa only [sargosSixthIterationExponent,Nat.cast_zero,mul_zero,add_zero,div_one]
      using sargosSixthMomentExponent_three
  | succ n ih =>
    rw [← sargosSixthIterationExponent_step]
    exact sargosSixthMomentExponent_step (sargosSixthIterationExponent_nonneg n) ih

theorem sargosSixthBaseMoment_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      sargosSixthBaseMoment N ≤ C*(N:ℝ)^ε := by
  obtain ⟨n,hn⟩ := exists_nat_gt (2/ε)
  have hnε : 2 < (n:ℝ)*ε := (div_lt_iff₀ hε).mp hn
  have he : sargosSixthIterationExponent n ≤ ε/2 := by
    dsimp [sargosSixthIterationExponent]
    apply (div_le_iff₀ (by positivity : 0 < 1+3*(n:ℝ))).2
    nlinarith only [hnε,hε]
  obtain ⟨C,hC,hbound⟩ := sargosSixthMomentExponent_iterate n (ε/2) (by positivity)
  refine ⟨C,hC,?_⟩
  intro N hN
  apply (hbound N hN).trans
  apply mul_le_mul_of_nonneg_left _ (by linarith only [hC] : 0 ≤ C)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    (by linarith only [he])

end TaoTrudgianYang2025
