import GafniTao.Pintz2023Equation42Quantitative

/-!
# Pintz (2023), equation (4.8): the finite mollifier factor

The paper suppresses a logarithmic factor in Vinogradov notation.  We retain
it as the exact harmonic number, so that its later epsilon absorption is
visible in the theorem chain.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- A finite power-weighted harmonic estimate used in equation (4.8). -/
theorem sum_rpow_sub_one_le_rpow_mul_harmonic
    {X : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (a - 1)) ≤
      (X : ℝ) ^ a * (harmonic X : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnPos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
  have hnX : (n : ℝ) ≤ X := by
    exact_mod_cast (Finset.mem_Icc.mp hn).2
  rw [show a - 1 = a + (-1 : ℝ) by ring, Real.rpow_add hnPos]
  rw [Real.rpow_neg_one]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hnPos.le hnX ha)
    (inv_nonneg.mpr hnPos.le)

/-- The literal finite-mollifier estimate on Pintz's shifted line
`Re(rho_j+s)=1-eta_j-eta`. -/
theorem norm_zetaMollifier_pintz2023_left_le
    {X : ℕ} {eta etaJ gamma t : ℝ}
    (hetaSum : 0 ≤ eta + etaJ) :
    ‖zetaMollifier X
        (pintz2023Rho etaJ gamma + ((-eta : ℝ) + I * t))‖ ≤
      (X : ℝ) ^ (eta + etaJ) * (harmonic X : ℝ) := by
  have hraw := norm_zetaMollifier_le_sum_rpow X
    (pintz2023Rho etaJ gamma + ((-eta : ℝ) + I * t))
  have hre :
      -(pintz2023Rho etaJ gamma + ((-eta : ℝ) + I * t)).re =
        eta + etaJ - 1 := by
    simp [pintz2023Rho]
    ring
  rw [hre] at hraw
  exact hraw.trans (sum_rpow_sub_one_le_rpow_mul_harmonic hetaSum)

#print axioms sum_rpow_sub_one_le_rpow_mul_harmonic
#print axioms norm_zetaMollifier_pintz2023_left_le

end

end GafniTao
