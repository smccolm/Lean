import GafniTao.FordCoreCoefficientSharp

/-!
# Uniform large-parameter form of Ford's Lemma 5.1

The exact moment recurrence has now been bounded at source scale.  This file
substitutes the resulting absolute rooted coefficient into the literal Lemma
5.1 inequality and combines its boundary and central terms without any
`N`-versus-`k` absorption hypothesis.
-/

namespace GafniTao

noncomputable section

def fordLemma51UniformConstant : ℝ := 3 + 2 * (2 : ℝ) ^ 128

theorem ford_boundary_exponent_le_full_decay
    {k : ℕ} (hk : 1 ≤ k) :
    (3 / 10 : ℝ) ≤
      1 - 1 / ((1091200 : ℝ) * (k : ℝ) ^ 2) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hdenPos : (0 : ℝ) < (1091200 : ℝ) * (k : ℝ) ^ 2 := by positivity
  have hq : 1 / ((1091200 : ℝ) * (k : ℝ) ^ 2) ≤ 7 / 10 := by
    rw [div_le_iff₀ hdenPos]
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  linarith

/-- Coefficient-free Lemma 5.1 on Ford's large-parameter band. -/
theorem ford_exponential_lemma_5_1_uniform
    {k N R : ℕ} {u t : ℝ}
    (hk : fordCoefficientKThreshold ≤ k) (hN : 1024 ≤ N)
    (hR : R ≤ 2 * N) (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t)
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      fordLemma51UniformConstant * (N : ℝ) ^
        (1 - 1 / ((1091200 : ℝ) * (k : ℝ) ^ 2)) := by
  have hk1 : 1 ≤ k := by
    exact (show 1 ≤ fordCoefficientKThreshold by
      exact le_trans (by norm_num) fordCoefficientKThreshold_ge_thousand).trans hk
  have hsource := ford_exponential_lemma_5_1_quantitative
    (fordCoefficientKThreshold_ge_thousand.trans hk)
    hN hR hu huOne ht hlower hupper
  have hroot := fordScaledCoreCoefficient_root_le_uniform hk
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  let q : ℝ := 1 / ((1091200 : ℝ) * (k : ℝ) ^ 2)
  have htail0 : 0 ≤ (N : ℝ) ^ (-q) := by positivity
  have hboundaryPow :
      (N : ℝ) ^ (3 / 10 : ℝ) ≤ (N : ℝ) ^ (1 - q) := by
    apply Real.rpow_le_rpow_of_exponent_le hNreal
    simpa [q] using ford_boundary_exponent_le_full_decay hk1
  have hmerge : (N : ℝ) * (N : ℝ) ^ (-q) = (N : ℝ) ^ (1 - q) := by
    calc
      (N : ℝ) * (N : ℝ) ^ (-q) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-q) := by simp
      _ = (N : ℝ) ^ ((1 : ℝ) + (-q)) := by rw [Real.rpow_add hNpos]
      _ = (N : ℝ) ^ (1 - q) := by ring_nf
  have hcentral :
      2 * (N : ℝ) * (fordScaledCoreCoefficient k) ^
          (1 / (((8 * k ^ 4 : ℕ) : ℝ))) * (N : ℝ) ^ (-q) ≤
        (2 * (2 : ℝ) ^ 128) * (N : ℝ) ^ (1 - q) := by
    calc
      _ ≤ 2 * (N : ℝ) * (2 : ℝ) ^ 128 * (N : ℝ) ^ (-q) := by
        gcongr
      _ = (2 * (2 : ℝ) ^ 128) * ((N : ℝ) * (N : ℝ) ^ (-q)) := by ring
      _ = (2 * (2 : ℝ) ^ 128) * (N : ℝ) ^ (1 - q) := by rw [hmerge]
  calc
    ‖fordShiftedExponentialSum N R u t‖ ≤
        3 * (N : ℝ) ^ (3 / 10 : ℝ) +
          2 * (N : ℝ) * (fordScaledCoreCoefficient k) ^
            (1 / (((8 * k ^ 4 : ℕ) : ℝ))) * (N : ℝ) ^ (-q) := by
      simpa [q] using hsource
    _ ≤ 3 * (N : ℝ) ^ (1 - q) +
        (2 * (2 : ℝ) ^ 128) * (N : ℝ) ^ (1 - q) := by gcongr
    _ = fordLemma51UniformConstant * (N : ℝ) ^ (1 - q) := by
      unfold fordLemma51UniformConstant
      ring
    _ = fordLemma51UniformConstant * (N : ℝ) ^
        (1 - 1 / ((1091200 : ℝ) * (k : ℝ) ^ 2)) := rfl

#print axioms ford_exponential_lemma_5_1_uniform

end

end GafniTao
