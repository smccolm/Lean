import Dubon2026.SourceExactIntegralModularPolynomial
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! Common-root vanishing for the precise padded resultant used in modular
polynomial composition. Native factorization by X minus the root and native
resultant multiplicativity avoid an algebraic-closure splitting detour.
This serves the all-level cyclic quotient polynomial relation required for
the DUB-17/18 generic root and inertia census. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial

/-- A common root annihilates the resultant with the actual first degree and any valid second bound. -/
theorem resultant_zero_of_common_root {K : Type*} [Field K]
    (f g : K[X]) (n : ℕ) (hg : g.natDegree ≤ n) (hf : f ≠ 0)
    (a : K) (hfa : f.IsRoot a) (hga : g.IsRoot a) :
    f.resultant g f.natDegree n = 0 := by
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot).mpr hfa
  have hq0 : q ≠ 0 := by intro hz; apply hf; rw [hq, hz, mul_zero]
  rw [hq, natDegree_mul (X_sub_C_ne_zero a) hq0, resultant_mul_left _ _ _ n hg,
    natDegree_X_sub_C, resultant_X_sub_C_left g n a hg, hga.eq_zero, zero_mul]

end Dubon2026.SourceFunctionField.IntegralJCoordinate
