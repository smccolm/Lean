import TaoTrudgianYang2025.RobertSargosZeroQPerturbedPrefix
import TaoTrudgianYang2025.SquareRootBlockAssembly

/-! Actual zero-q source prefixes assembled from the square-root blocks. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_zero_q_full_prefix
    (f : ℝ → ℝ) (A : ℝ) (N : ℕ) {a b h r C D lam M : ℝ}
    (hh : 0 ≤ h) (hhr : 0 ≤ h+r) (hr : r ≠ 0)
    (hC : 1 ≤ C) (hD : 0 ≤ D) (hlam : 0 < lam) (hscale : 2*|r| *lam ≤ 1)
    (hN : (N:ℝ) ≤ M) (hM : (2*|r| *lam)^(-(1:ℝ)/2) ≤ M)
    (hslow : C*lam*(h^3+(h+r)^3)/3 ≤ D*Real.sqrt (2*|r| *lam))
    (ha : a ≤ A-h) (hb : A+N+h ≤ b)
    (har : a ≤ A-(h+r)) (hbr : A+N+(h+r) ≤ b)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc a b, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc a b, iteratedDeriv 4 f x ≤ C*lam) :
    ‖∑ n ∈ Finset.range N, fordAdditiveCharacter
      (robertSargosSymmetricDifference f (A+n) h -
        robertSargosSymmetricDifference f (A+n) (h+r))‖ ≤
      120*C*(1+2*Real.pi*D)*M*(2*|r| *lam)^((1:ℝ)/12) := by
  let μ := 2*|r| *lam
  have hμ : 0 < μ := mul_pos (mul_pos (by norm_num) (abs_pos.mpr hr)) hlam
  apply norm_range_from_square_root_blocks
    (fun n => fordAdditiveCharacter
      (robertSargosSymmetricDifference f (A+n) h -
        robertSargosSymmetricDifference f (A+n) (h+r))) N
    (zero_le_one.trans hC) hD hμ hscale hN hM
  intro k n hkn hn
  have hknc : (k:ℝ)+n ≤ N := by exact_mod_cast hkn
  have hnc : (n:ℝ) ≤ μ^(-(1:ℝ)/2) :=
    (show (n:ℝ) ≤ (⌊μ^(-(1:ℝ)/2)⌋₊:ℝ) by exact_mod_cast hn).trans
      (Nat.floor_le (Real.rpow_nonneg hμ.le _))
  have hp := robertSargos_zero_q_perturbed_prefix f (A+k) n hh hhr hr hC hlam hscale
    (show a ≤ A+k-h by linarith [Nat.cast_nonneg (α := ℝ) k])
    (show A+k+n+h ≤ b by linarith)
    (show a ≤ A+k-(h+r) by linarith [Nat.cast_nonneg (α := ℝ) k])
    (show A+k+n+(h+r) ≤ b by linarith) hf hlo hhi
  have hb' := hp.trans (third_derivative_abel_block_budget (Nat.cast_nonneg n)
    (zero_le_one.trans hC) hD hμ hscale hnc hslow)
  simpa only [Nat.cast_add,add_assoc] using hb'

end TaoTrudgianYang2025
