import TaoTrudgianYang2025.ClassicalReflectedCoefficients
import TaoTrudgianYang2025.ZeroEnergyDichotomy

/-!
# Actual reflected weights to bounded coefficient-one ordinates

The original finite index type is kept. The normalization M^sigma is
carried into both the Fourier radius and the resulting threshold.
The energy displacement estimate is retained alongside the pointwise
coefficient-one largeness; no cardinality or energy powering is used here.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem exists_classicalReflected_explicitBoundedOrdinate_family
    {ι : Type*} [Fintype ι]
    (M N k : ℕ) (sigma V : ℝ) (W : ι → ℝ)
    (hM : 0 < M) (hN : 0 < N) (hV : 0 < V) (hk : 1 < k)
    (hlarge : ∀ x,
      V ≤ ‖dirichletPoly N (normalizedTypeIReflectedCoeff sigma M) (W x)‖) :
    let sourceV := (M : ℝ) ^ sigma * V
    let R := classicalTypeIFourierRadius M N k (-sigma) sourceV
    ∃ W' : ι → ℝ,
      (∀ x, |W' x - W x| ≤ 2 * Real.pi * R) ∧
      (∀ x,
        sourceV / (4 * (N : ℝ) ^ sigma * classicalTypeIFourierL1 (-sigma)) ≤
          ‖∑ n ∈ Finset.Ioc N (min (2 * N) M), dirichletPhase n (W' x)‖) ∧
      approximateAdditiveEnergyOf 1 W ≤
        (4 * Nat.ceil (1 + 4 * (2 * Real.pi * R)) + 6) *
          approximateAdditiveEnergyOf 1 W' := by
  dsimp only
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsourceV : 0 < (M : ℝ) ^ sigma * V :=
    mul_pos (Real.rpow_pos_of_pos hMpos _) hV
  have hsource : ∀ x,
      (M : ℝ) ^ sigma * V ≤
        ‖dirichletPoly N (classicalZetaLongLineCoeff M (-sigma)) (W x)‖ := by
    intro x
    rw [← rpow_mul_norm_reflected_eq_norm_line sigma (W x) N M hM]
    exact mul_le_mul_of_nonneg_left (hlarge x) (Real.rpow_nonneg hMpos.le _)
  simpa only [neg_neg] using
    exists_classicalTypeI_explicitBoundedOrdinate_family
      M N k (-sigma) ((M : ℝ) ^ sigma * V) W hN hsourceV hk hsource

end TaoTrudgianYang2025
