import GafniTao.FordLemma63

/-!
# Ford Corollary 6.4: exact scale algebra

Ford takes `t = N^lambda`, `mu = 1 - lambda/(k+1)`, and `M = N^mu`.
This module proves the real-power identities independently of the integral
cutoff issue.  The latter is kept explicit in the consumer rather than being
hidden by treating a generally nonintegral power as a natural number.
-/

namespace GafniTao

noncomputable section

/-- Ford's scale exponent in Corollary 6.4. -/
def fordCorollary64Mu (k : ℕ) (lambda : ℝ) : ℝ :=
  1 - lambda / (k + 1 : ℝ)

theorem fordCorollary64Mu_bounds
    {k : ℕ} {lambda : ℝ}
    (hlower : (k : ℝ) - 1 ≤ lambda) (hupper : lambda ≤ k) :
    1 / (k + 1 : ℝ) ≤ fordCorollary64Mu k lambda ∧
      fordCorollary64Mu k lambda ≤ 2 / (k + 1 : ℝ) := by
  have hden : (0 : ℝ) < k + 1 := by positivity
  have hden_ne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hden
  unfold fordCorollary64Mu
  constructor
  · apply (div_le_iff₀ hden).2
    field_simp [hden_ne]
    nlinarith
  · apply (le_div_iff₀ hden).2
    field_simp [hden_ne]
    nlinarith

theorem fordCorollary64Mu_nonneg
    {k : ℕ} {lambda : ℝ} (hupper : lambda ≤ k) :
    0 ≤ fordCorollary64Mu k lambda := by
  have hden : (0 : ℝ) < k + 1 := by positivity
  unfold fordCorollary64Mu
  rw [sub_nonneg, div_le_one hden]
  exact hupper.trans (by norm_num)

/-- The chosen height and scale multiply to the exact source endpoint. -/
theorem fordCorollary64_height_mul_scale
    {k : ℕ} {N lambda : ℝ} (hN : 0 < N) :
    N ^ lambda *
        (N ^ fordCorollary64Mu k lambda) ^ (k + 1 : ℕ) =
      N ^ (k + 1 : ℕ) := by
  have hexp :
      lambda + fordCorollary64Mu k lambda * ((k : ℝ) + 1) =
        (k : ℝ) + 1 := by
    unfold fordCorollary64Mu
    have hden : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hden]
    ring
  have hexp' :
      lambda + fordCorollary64Mu k lambda * ((k + 1 : ℕ) : ℝ) =
        ((k + 1 : ℕ) : ℝ) := by
    simpa using hexp
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le,
    ← Real.rpow_add hN]
  exact (congrArg (fun e : ℝ => N ^ e) hexp').trans
    (Real.rpow_natCast N (k + 1))

theorem fordCorollary64_height_le_degree
    {k : ℕ} {N lambda : ℝ} (hN : 1 ≤ N)
    (hupper : lambda ≤ k) :
    N ^ lambda ≤ N ^ (k : ℕ) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hN hupper

theorem fordCorollary64_scale_one_le
    {k : ℕ} {N lambda : ℝ} (hN : 1 ≤ N)
    (hupper : lambda ≤ k) :
    1 ≤ N ^ fordCorollary64Mu k lambda :=
  Real.one_le_rpow hN (fordCorollary64Mu_nonneg hupper)

theorem fordCorollary64_scale_le_sqrt
    {k : ℕ} {N lambda : ℝ} (hk : 4 ≤ k) (hN : 1 ≤ N)
    (hlower : (k : ℝ) - 1 ≤ lambda) (hupper : lambda ≤ k) :
    N ^ fordCorollary64Mu k lambda ≤ N ^ (1 / 2 : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_le hN
  have hmu := (fordCorollary64Mu_bounds hlower hupper).2
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < k + 1 := by positivity
  calc
    fordCorollary64Mu k lambda ≤ 2 / (k + 1 : ℝ) := hmu
    _ ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
      nlinarith

#print axioms fordCorollary64Mu_bounds
#print axioms fordCorollary64_height_mul_scale
#print axioms fordCorollary64_height_le_degree

end

end GafniTao
