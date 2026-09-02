import GafniTao.FordUniversalCoreCoefficient
import GafniTao.FordLemma51UniformBound

/-!
# Ford Lemma 5.1 for every degree `k ≥ 1000`
-/

namespace GafniTao

noncomputable section

def fordLemma51AbsoluteConstant : ℝ := 3 + 2 * fordUniversalRootCoefficient

theorem ford_exponential_lemma_5_1_all_large_degrees
    {k N R : ℕ} {u t : ℝ}
    (hk : 1000 ≤ k) (hN : 1024 ≤ N)
    (hR : R ≤ 2 * N) (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t)
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      fordLemma51AbsoluteConstant * (N : ℝ) ^
        (1 - 1 / ((1091200 : ℝ) * (k : ℝ) ^ 2)) := by
  have hk1 : 1 ≤ k := by omega
  have hsource := ford_exponential_lemma_5_1_quantitative
    hk hN hR hu huOne ht hlower hupper
  have hroot := fordScaledCoreCoefficient_root_le_absolute hk
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  let q : ℝ := 1 / ((1091200 : ℝ) * (k : ℝ) ^ 2)
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
        (2 * fordUniversalRootCoefficient) * (N : ℝ) ^ (1 - q) := by
    calc
      _ ≤ 2 * (N : ℝ) * fordUniversalRootCoefficient * (N : ℝ) ^ (-q) := by
        gcongr
      _ = (2 * fordUniversalRootCoefficient) *
          ((N : ℝ) * (N : ℝ) ^ (-q)) := by ring
      _ = (2 * fordUniversalRootCoefficient) * (N : ℝ) ^ (1 - q) := by
        rw [hmerge]
  calc
    ‖fordShiftedExponentialSum N R u t‖ ≤
        3 * (N : ℝ) ^ (3 / 10 : ℝ) +
          2 * (N : ℝ) * (fordScaledCoreCoefficient k) ^
            (1 / (((8 * k ^ 4 : ℕ) : ℝ))) * (N : ℝ) ^ (-q) := by
      simpa [q] using hsource
    _ ≤ 3 * (N : ℝ) ^ (1 - q) +
        (2 * fordUniversalRootCoefficient) * (N : ℝ) ^ (1 - q) := by
      gcongr
    _ = fordLemma51AbsoluteConstant * (N : ℝ) ^ (1 - q) := by
      unfold fordLemma51AbsoluteConstant
      ring
    _ = fordLemma51AbsoluteConstant * (N : ℝ) ^
        (1 - 1 / ((1091200 : ℝ) * (k : ℝ) ^ 2)) := rfl

#print axioms ford_exponential_lemma_5_1_all_large_degrees

end

end GafniTao
