import PrimeShell.Admissible
import Zeta23.XiPrime.Certificate.AtOne
import Zeta23.XiPrime.Window

open scoped BigOperators
open Set intervalIntegral

noncomputable section

namespace PrimeShell

open Zeta23 Zeta23.XiPrime

/-- The concrete exponent used by the native Prime Shell candidate. -/
def primeShellLambda : ℝ := 199 / 150

/-- A uniform rational majorant for the tail of `D1trunc 9` on
`[0, 4/3]`.  The geometric ratio is
`(20/231) * (4/3)^2 = 320/2079`. -/
def eps9FourThirds : ℝ :=
  D1coeff 9 * (4 / 3 : ℝ) ^ 21 * (1 - 320 / 2079 : ℝ)⁻¹

theorem eps9FourThirds_pos : 0 < eps9FourThirds := by
  unfold eps9FourThirds
  have hden : (0 : ℝ) < 1 - 320 / 2079 := by norm_num
  exact mul_pos (mul_pos (D1coeff_pos 9) (pow_pos (by norm_num) 21))
    (inv_pos.mpr hden)

/-- The ninth tail of `D1` is uniformly controlled throughout the full
explicit-formula range needed by Prime Shell. -/
theorem D1tail9_le_four_thirds {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 4 / 3) :
    ∑' j : ℕ, D1term (j + 9) s ≤ eps9FourThirds := by
  have hq0 : (0 : ℝ) ≤ 320 / 2079 := by norm_num
  have hq1 : (320 / 2079 : ℝ) < 1 := by norm_num
  have hgeo : Summable
      (fun j : ℕ => D1coeff 9 * (4 / 3 : ℝ) ^ 21 * (320 / 2079 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hsum : Summable (fun j : ℕ => D1term (j + 9) s) :=
    (summable_nat_add_iff 9).mpr (summable_D1term s)
  have hle : ∀ j : ℕ,
      D1term (j + 9) s ≤
        D1coeff 9 * (4 / 3 : ℝ) ^ 21 * (320 / 2079 : ℝ) ^ j := by
    intro j
    have hsPow : s ^ (2 * (j + 9) + 3) ≤ (4 / 3 : ℝ) ^ (2 * (j + 9) + 3) :=
      pow_le_pow_left₀ hs0 hs1 _
    have hc := D1coeff_tail_le j
    have hratio : (20 / 231 : ℝ) * (4 / 3 : ℝ) ^ 2 = 320 / 2079 := by
      norm_num
    unfold D1term
    calc
      D1coeff (j + 9) * s ^ (2 * (j + 9) + 3)
          ≤ D1coeff (j + 9) * (4 / 3 : ℝ) ^ (2 * (j + 9) + 3) := by
            exact mul_le_mul_of_nonneg_left hsPow (D1coeff_nonneg _)
      _ = D1coeff (9 + j) * (4 / 3 : ℝ) ^ (21 + 2 * j) := by
            congr 2 <;> omega
      _ ≤ (D1coeff 9 * (20 / 231 : ℝ) ^ j) *
            (4 / 3 : ℝ) ^ (21 + 2 * j) := by
            gcongr
      _ = D1coeff 9 * (4 / 3 : ℝ) ^ 21 *
            ((20 / 231 : ℝ) ^ j * ((4 / 3 : ℝ) ^ 2) ^ j) := by
            rw [pow_add, pow_mul]
            ring
      _ = D1coeff 9 * (4 / 3 : ℝ) ^ 21 *
            (((20 / 231 : ℝ) * (4 / 3 : ℝ) ^ 2) ^ j) := by
            rw [mul_pow]
      _ = D1coeff 9 * (4 / 3 : ℝ) ^ 21 * (320 / 2079 : ℝ) ^ j := by
            rw [hratio]
  calc
    ∑' j : ℕ, D1term (j + 9) s
        ≤ ∑' j : ℕ,
            D1coeff 9 * (4 / 3 : ℝ) ^ 21 * (320 / 2079 : ℝ) ^ j :=
          hsum.tsum_le_tsum hle hgeo
    _ = D1coeff 9 * (4 / 3 : ℝ) ^ 21 *
          ∑' j : ℕ, (320 / 2079 : ℝ) ^ j := by
          rw [← tsum_mul_left]
    _ = D1coeff 9 * (4 / 3 : ℝ) ^ 21 *
          (1 - 320 / 2079 : ℝ)⁻¹ := by
          rw [tsum_geometric_of_lt_one hq0 hq1]
    _ = eps9FourThirds := rfl

theorem D1_le_D1trunc9_add_four_thirds {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 4 / 3) :
    D1 s ≤ D1trunc 9 s + eps9FourThirds := by
  rw [D1_eq_trunc_add_tail 9]
  linarith [D1tail9_le_four_thirds hs0 hs1]

/-- Coefficients of
`r ↦ D1trunc 9 (primeShellLambda * r) * (1-r)`. -/
def prodFlatPrimeShell : List ℝ :=
  [0,
   primeShellLambda,
   -primeShellLambda - 4 * primeShellLambda ^ 2,
   4 * primeShellLambda ^ 2 + 4 * primeShellLambda ^ 3,
   -4 * primeShellLambda ^ 3,
   4 / 3 * primeShellLambda ^ 5,
   -(4 / 3 * primeShellLambda ^ 5),
   16 / 45 * primeShellLambda ^ 7,
   -(16 / 45 * primeShellLambda ^ 7),
   8 / 105 * primeShellLambda ^ 9,
   -(8 / 105 * primeShellLambda ^ 9),
   64 / 4725 * primeShellLambda ^ 11,
   -(64 / 4725 * primeShellLambda ^ 11),
   64 / 31185 * primeShellLambda ^ 13,
   -(64 / 31185 * primeShellLambda ^ 13),
   256 / 945945 * primeShellLambda ^ 15,
   -(256 / 945945 * primeShellLambda ^ 15),
   64 / 2027025 * primeShellLambda ^ 17,
   -(64 / 2027025 * primeShellLambda ^ 17),
   1024 / 310134825 * primeShellLambda ^ 19,
   -(1024 / 310134825 * primeShellLambda ^ 19)]

theorem T9_mul_flat_primeShell_eq :
    (fun r : ℝ => T9 (primeShellLambda * r) * (1 - r)) =
      polyEval prodFlatPrimeShell := by
  ext r
  simp [T9, primeShellLambda, polyEval, prodFlatPrimeShell,
    Finset.sum_range_succ]
  ring

/-- Exact rational evaluation of the ninth truncation at the Prime Shell
exponent.  The unwieldy rational is intentionally kept behind the
definition; downstream certification uses `norm_num` on the finite sum. -/
def primeShellJ9 : ℝ :=
  2 * polyInt prodFlatPrimeShell 0 1

theorem jWin_trunc9_primeShell_vFlat :
    jWin (D1trunc 9) primeShellLambda vFlat = primeShellJ9 := by
  unfold jWin primeShellJ9
  have h :
      (fun r : ℝ => D1trunc 9 (primeShellLambda * r) * vConv vFlat r) =
        fun r : ℝ => T9 (primeShellLambda * r) * (1 - r) := by
    ext r
    rw [D1trunc9_eq, vConv_vFlat]
  rw [h, T9_mul_flat_primeShell_eq, integral_polyEval]

/-- The full `D1` window contribution is bounded by the exact finite
polynomial value plus the certified uniform tail. -/
theorem jWin_D1_primeShell_vFlat_le :
    jWin D1 primeShellLambda vFlat ≤ primeShellJ9 + eps9FourThirds := by
  have hlam0 : 0 ≤ primeShellLambda := by norm_num [primeShellLambda]
  have hlam43 : primeShellLambda ≤ (4 / 3 : ℝ) := by norm_num [primeShellLambda]
  have h := jWin_one_le_of_le
    (D := fun r : ℝ => D1 (primeShellLambda * r))
    (E := fun r : ℝ => D1trunc 9 (primeShellLambda * r))
    (w := fun r : ℝ => 1 - r)
    ((continuous_D1.comp (continuous_const.mul continuous_id)).continuousOn)
    (((continuous_D1trunc 9).comp
      (continuous_const.mul continuous_id)).continuousOn)
    (by fun_prop)
    (fun r hr => by linarith [hr.2])
    (e := eps9FourThirds)
    (fun r hr => D1_le_D1trunc9_add_four_thirds
      (mul_nonneg hlam0 hr.1)
      ((mul_le_mul hlam43 hr.2 hr.1 (by norm_num)).trans (by norm_num)))
    (fun r _ => vConv_vFlat r)
  rw [two_integral_vConv_vFlat, mul_one] at h
  have h' : jWin D1 primeShellLambda vFlat ≤
      jWin (D1trunc 9) primeShellLambda vFlat + eps9FourThirds := by
    simpa [jWin] using h
  rw [jWin_trunc9_primeShell_vFlat] at h'
  exact h'

/-- The certified ideal second-moment constant at the MRT-compatible
Prime Shell exponent is strictly below `397/300`. -/
theorem kappaXi_primeShell_vFlat_lt :
    kappaXi primeShellLambda vFlat < (397 / 300 : ℝ) := by
  rw [kappaXi_vFlat (by norm_num [primeShellLambda])]
  have h := jWin_D1_primeShell_vFlat_le
  calc
    1 / primeShellLambda + jWin D1 primeShellLambda vFlat
        ≤ 1 / primeShellLambda + (primeShellJ9 + eps9FourThirds) := by
          gcongr
    _ < (397 / 300 : ℝ) := by
      unfold primeShellJ9 prodFlatPrimeShell polyInt eps9FourThirds primeShellLambda
      rw [D1coeff_nine]
      simp only [List.length_cons, List.length_nil, List.getD, Finset.sum_range_succ,
        Finset.sum_range_zero]
      norm_num

/-- Consequently the ideal flat-window spectral output clears `2/3` by
the explicit rational margin `1/100`. -/
theorem two_thirds_add_one_hundredth_lt_primeShell_output :
    (2 / 3 : ℝ) + 1 / 100 < 2 - kappaXi primeShellLambda vFlat := by
  linarith [kappaXi_primeShell_vFlat_lt]

end PrimeShell
