import GafniTao.FordCorollary64Root

/-!
# Ford Corollary 6.4: endpoint remainders

The raw TeX of Ford's paper prints `N^(1/(k+1))` as the final remainder,
while the immediately following proof only establishes
`M = N^mu <= N^(2/(k+1))`.  This module records the exact consequence of
the stated parameter choice; no exponent is silently strengthened.
-/

namespace GafniTao

noncomputable section

theorem fordCorollary64_div_scale_le
    {k : ℕ} {N M lambda : ℝ}
    (hN : 1 ≤ N) (hupper : lambda ≤ k)
    (hMscale : M = N ^ fordCorollary64Mu k lambda) :
    N / M ≤ N ^ ((k : ℝ) / (k + 1 : ℝ)) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hdiv :
      N / M = N ^ (1 - fordCorollary64Mu k lambda) := by
    rw [hMscale, Real.rpow_sub hNpos, Real.rpow_one]
  rw [hdiv]
  apply Real.rpow_le_rpow_of_exponent_le hN
  have hden : (0 : ℝ) < k + 1 := by positivity
  unfold fordCorollary64Mu
  rw [show 1 - (1 - lambda / (k + 1 : ℝ)) =
    lambda / (k + 1 : ℝ) by ring]
  exact (div_le_div_iff_of_pos_right hden).2 hupper

theorem fordCorollary64_scale_le_two
    {k : ℕ} {N M lambda : ℝ}
    (hN : 1 ≤ N) (hlower : (k : ℝ) - 1 ≤ lambda)
    (hupper : lambda ≤ k)
    (hMscale : M = N ^ fordCorollary64Mu k lambda) :
    M ≤ N ^ (2 / (k + 1 : ℝ)) := by
  rw [hMscale]
  exact Real.rpow_le_rpow_of_exponent_le hN
    (fordCorollary64Mu_bounds hlower hupper).2

theorem fordCorollary64_remainders_le_corrected
    {k : ℕ} {N M lambda : ℝ}
    (hN : 1 ≤ N) (hlower : (k : ℝ) - 1 ≤ lambda)
    (hupper : lambda ≤ k)
    (hMscale : M = N ^ fordCorollary64Mu k lambda) :
    N / M + M ≤
      N ^ ((k : ℝ) / (k + 1 : ℝ)) +
        N ^ (2 / (k + 1 : ℝ)) := by
  exact add_le_add
    (fordCorollary64_div_scale_le hN hupper hMscale)
    (fordCorollary64_scale_le_two hN hlower hupper hMscale)

#print axioms fordCorollary64_div_scale_le
#print axioms fordCorollary64_remainders_le_corrected

end

end GafniTao
