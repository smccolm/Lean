import Definitions.Def_TateCurve_Defect
import Theorems.Thm_TateCurve_equation_of_defectCoeff_eq_zero
import Theorems.Thm_TateCurve_exists_zpow_mul_mem_annulus
import Theorems.Thm_TateCurve_pointX_zpow_mul
import Theorems.Thm_TateCurve_pointY_zpow_mul
import P2M.Util
namespace P2MW.S_TateCurve_equation_pointX_pointY_of_defectCoeff_eq_zero
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K}
    (hD : ∀ v : K, v ≠ 0 → v ≠ 1 → ∀ N : ℕ, 0 < N → defectCoeff v N = 0)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) :
    pointY q u ^ 2 + pointX q u * pointY q u
      = pointX q u ^ 3 + a₄ q * pointX q u + a₆ q := by
  obtain ⟨n, hqu, hqu'⟩ := TateCurve.exists_zpow_mul_mem_annulus hq0 hq hu0
  have hv0 : q ^ n * u ≠ 0 := mul_ne_zero (zpow_ne_zero n hq0) hu0
  have hvlat : ∀ m : ℤ, q ^ m * (q ^ n * u) ≠ 1 := by
    intro m; rw [← mul_assoc, ← zpow_add₀ hq0]; exact hu (m + n)
  have hv1 : q ^ n * u ≠ 1 := by simpa using hvlat 0
  have heq := TateCurve.equation_of_defectCoeff_eq_zero hq0 hq hv0 hvlat hqu hqu' (hD _ hv0 hv1)
  rwa [TateCurve.pointX_zpow_mul hq0 n, TateCurve.pointY_zpow_mul hq0 n] at heq
