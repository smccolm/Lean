import GafniTao.HeathBrownLemmaOneCompact
import GafniTao.HeathBrownInteriorShift

/-!
# Monotonicity of the source-scale majorant

The endpoint repair replaces `N` by `N-2`.  All three critical monomials
are nondecreasing in the length because their `N` exponents are nonnegative.
-/

namespace GafniTao

noncomputable section

theorem heathBrownThreeTerm_mono
    {M N k : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) (hk : 2 ≤ k)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    heathBrownThreeTerm M k lambda ≤
      heathBrownThreeTerm N k lambda := by
  let r := heathBrownCriticalReciprocal k
  have hr0 : 0 ≤ r :=
    (heathBrownCriticalReciprocal_pos hk).le
  have hrHalf : r ≤ 1 / 2 :=
    heathBrownCriticalReciprocal_le_half hk
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hMNReal : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hFirstExp : 0 ≤ 1 - r := by linarith
  have hLastExp : 0 ≤ 1 - 2 * r := by linarith
  have hfirst :
      (M : ℝ) ^ (1 - r) ≤ (N : ℝ) ^ (1 - r) :=
    Real.rpow_le_rpow hM0 hMNReal hFirstExp
  have hmiddle :
      (M : ℝ) * lambda ^ r ≤ (N : ℝ) * lambda ^ r :=
    mul_le_mul_of_nonneg_right hMNReal (by positivity)
  have hlast :
      (M : ℝ) ^ (1 - 2 * r) *
          lambda ^ (-2 * r / (k : ℝ)) ≤
        (N : ℝ) ^ (1 - 2 * r) *
          lambda ^ (-2 * r / (k : ℝ)) := by
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hM0 hMNReal hLastExp) (by positivity)
  unfold heathBrownThreeTerm
  dsimp only
  linarith

theorem heathBrown_sourceScale_main_mono
    {M N k : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) (hk : 3 ≤ k)
    {A lambda epsilon C : ℝ}
    (hlambda : 0 < lambda) (hepsilon : 0 < epsilon)
    (hconstant : 0 ≤ heathBrownLemmaOneSourceConstant k A C epsilon) :
    heathBrownLemmaOneSourceConstant k A C epsilon *
        (M : ℝ) ^ epsilon * heathBrownThreeTerm M k lambda ≤
      heathBrownLemmaOneSourceConstant k A C epsilon *
        (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda := by
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hMNReal : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hpow := Real.rpow_le_rpow hM0 hMNReal hepsilon.le
  have hthree := heathBrownThreeTerm_mono hM hMN
    (by omega : 2 ≤ k) hlambda
  have hthreeM0 : 0 ≤ heathBrownThreeTerm M k lambda :=
    (heathBrownThreeTerm_pos (k := k) hM hlambda).le
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (mul_le_mul hpow hthree hthreeM0 (by positivity)) hconstant)

#print axioms heathBrownThreeTerm_mono
#print axioms heathBrown_sourceScale_main_mono

end

end GafniTao
