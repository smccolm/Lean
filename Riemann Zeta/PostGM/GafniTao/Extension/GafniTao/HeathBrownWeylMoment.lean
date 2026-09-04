import GafniTao.HeathBrownNuMoments
import GafniTao.FordVinogradovMomentMonotone

/-!
# The polynomial Weyl moment in Heath-Brown Lemma 1

The source polynomial `S(x; alpha)` has degrees `1, ..., k-1`.  At an
integer cutoff `Q` it is exactly Ford's complete Weyl sum.  Its `2s` moment
is therefore the concrete Vinogradov solution count, and monotonicity permits
the replacement `Q <= H` used in the source.
-/

open Finset Set MeasureTheory
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

abbrev heathBrownWeylSum (k Q : ℕ)
    (α : HeathBrownCoefficientTorus k) : ℂ :=
  fordVinogradovWeylSum (k - 1) Q α

theorem integral_heathBrownWeylSum_pow (s k Q : ℕ) :
    ∫ α : HeathBrownCoefficientTorus k,
        ‖heathBrownWeylSum k Q α‖ ^ (2 * s)
        ∂(heathBrownCoefficientMeasure k) =
      (fordVinogradovMomentNat s (k - 1) Q : ℝ) := by
  exact ford_vinogradov_torus_real_mean_eq s (k - 1) Q

theorem integral_heathBrownWeylSum_pow_le
    (s k : ℕ) {Q H : ℕ} (hQH : Q ≤ H) :
    ∫ α : HeathBrownCoefficientTorus k,
        ‖heathBrownWeylSum k Q α‖ ^ (2 * s)
        ∂(heathBrownCoefficientMeasure k) ≤
      (fordVinogradovMomentNat s (k - 1) H : ℝ) := by
  rw [integral_heathBrownWeylSum_pow]
  exact_mod_cast fordVinogradovMomentNat_mono s (k - 1) hQH

#print axioms integral_heathBrownWeylSum_pow
#print axioms integral_heathBrownWeylSum_pow_le

end

end GafniTao
