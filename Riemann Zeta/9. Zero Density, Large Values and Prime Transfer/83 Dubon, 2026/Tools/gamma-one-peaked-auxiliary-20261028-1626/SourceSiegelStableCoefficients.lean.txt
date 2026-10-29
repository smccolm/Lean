import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> integral Siegel expansion.
Use stabilized coefficients of actual finite polynomial products. The
coefficient of degree m cannot change when factors of order > m are
appended. This is the necessary coefficient calculation for the native
local-uniform/Taylor route, not a general formal infinite-product theory.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun, with the
existing SourceDiscriminantProductExpansion analytic proof route. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion
noncomputable section
open Polynomial Filter Topology

/-- The actual expanded polynomial factor as a formal series. -/
def fac (P : ℕ → ℂ[X]) (n : ℕ) : PowerSeries ℂ :=
  ((Polynomial.expand ℂ (n + 1) (P n) : ℂ[X]) : PowerSeries ℂ)

/-- The actual finite truncation of the source product. -/
def pp (P : ℕ → ℂ[X]) (N : ℕ) : ℂ[X] := ∏ n ∈ Finset.range N, Polynomial.expand ℂ (n + 1) (P n)

theorem pp_zero (P : ℕ → ℂ[X]) : pp P 0 = 1 := Finset.prod_range_zero _

theorem pp_succ (P : ℕ → ℂ[X]) (N : ℕ) : pp P (N + 1) = pp P N * Polynomial.expand ℂ (N + 1) (P N) :=
  Finset.prod_range_succ _ _

theorem coe_pp (P : ℕ → ℂ[X]) (N : ℕ) :
    ((pp P N : ℂ[X]) : PowerSeries ℂ) = ∏ n ∈ Finset.range N, fac P n := by
  show Polynomial.coeToPowerSeries.ringHom (∏ n ∈ Finset.range N, Polynomial.expand ℂ (n + 1) (P n))
    = _
  rw [map_prod]
  rfl

variable {P : ℕ → ℂ[X]}

theorem fac_sub_one (P : ℕ → ℂ[X]) (n : ℕ) :
    fac P n - 1 = ((Polynomial.expand ℂ (n + 1) (P n - 1) : ℂ[X]) : PowerSeries ℂ) := by
  unfold fac
  rw [map_sub, map_one, Polynomial.coe_sub, Polynomial.coe_one]

theorem coeff_fac_sub_one (hP : ∀ n, (P n).coeff 0 = 1) (n i : ℕ) (hi : i < n + 1) :
    PowerSeries.coeff i (fac P n - 1) = 0 := by
  rw [fac_sub_one, Polynomial.coeff_coe, Polynomial.coeff_expand (Nat.succ_pos n)]
  split_ifs with hd
  · rw [Nat.eq_zero_of_dvd_of_lt hd hi, Nat.zero_div, Polynomial.coeff_sub,
      Polynomial.coeff_one_zero, hP n, sub_self]
  · rfl

theorem order_fac_sub_one (hP : ∀ n, (P n).coeff 0 = 1) (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (fac P n - 1).order :=
  PowerSeries.nat_le_order _ _ fun i hi => coeff_fac_sub_one hP n i hi

theorem coeff_mul_fac_of_le (hP : ∀ n, (P n).coeff 0 = 1) {m n : ℕ} (h : m ≤ n) (φ : PowerSeries ℂ) :
    PowerSeries.coeff m (φ * fac P n) = PowerSeries.coeff m φ := by
  have : φ * fac P n = φ + φ * (fac P n - 1) := by ring
  rw [this, map_add, PowerSeries.coeff_mul_of_lt_order, add_zero]
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le h) (order_fac_sub_one hP n)

theorem coeff_prod_range_fac (hP : ∀ n, (P n).coeff 0 = 1) (m N : ℕ) (hN : m ≤ N) :
    PowerSeries.coeff m (∏ n ∈ Finset.range N, fac P n) =
      PowerSeries.coeff m (∏ n ∈ Finset.range m, fac P n) := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hmN ih => rw [Finset.prod_range_succ, coeff_mul_fac_of_le hP hmN, ih]

theorem coeff_pp_stable (hP : ∀ n, (P n).coeff 0 = 1) {m N : ℕ} (h : m ≤ N) :
    (pp P N).coeff m = (pp P m).coeff m := by
  have := coeff_prod_range_fac hP m N h
  rwa [← coe_pp, ← coe_pp, Polynomial.coeff_coe, Polynomial.coeff_coe] at this


/-- The stabilized coefficient of the actual finite product. -/
def stableCoeff (P : ℕ → ℂ[X]) (m : ℕ) : ℂ := (pp P m).coeff m

theorem stableCoeff_eq {P : ℕ → ℂ[X]} (hP : ∀ n, (P n).coeff 0 = 1)
    {m N : ℕ} (h : m ≤ N) : stableCoeff P m = (pp P N).coeff m :=
  (coeff_pp_stable hP h).symm

theorem stableCoeff_zero (P : ℕ → ℂ[X]) : stableCoeff P 0 = 1 := by
  rw [stableCoeff, pp_zero, Polynomial.coeff_one_zero]

theorem eval_pp (P : ℕ → ℂ[X]) (N : ℕ) (x : ℂ) :
    (pp P N).eval x = ∏ n ∈ Finset.range N, (P n).eval (x ^ (n + 1)) := by
  simp [pp, Polynomial.eval_prod, Polynomial.expand_eval]

end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion
