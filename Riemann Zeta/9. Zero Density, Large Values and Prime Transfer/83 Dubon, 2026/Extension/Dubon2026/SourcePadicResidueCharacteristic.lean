import Dubon2026.SourcePadicIntegerCoefficientMap
import Mathlib.Algebra.CharP.Basic

/-! DUB-17/18 -> actual residual association -> residue characteristic.
The constructed coefficient valuation extends the original p-adic norm.
Since the valuation of p is strictly below one, its actual residue field
has characteristic p. No residue characteristic is assumed. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable (p : ℕ) [Fact p.Prime]
private local instance : ValuativeRel ℚ_[p] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))
variable (E : Type) [Field E] [Algebra ℚ_[p] E] [ValuativeRel E]
variable [(ValuativeRel.valuation ℚ_[p]).HasExtension (ValuativeRel.valuation E)]

theorem padicCoefficient_valuation_prime_lt_one : ValuativeRel.valuation E (p : E) < 1 := by
  letI : (NormedField.valuation (K := ℚ_[p])).Compatible :=
    Valuation.Compatible.ofValuation _
  have hp : ValuativeRel.valuation ℚ_[p] (p : ℚ_[p]) < 1 :=
    (ValuativeRel.isEquiv (ValuativeRel.valuation ℚ_[p])
      (NormedField.valuation (K := ℚ_[p]))).lt_one_iff_lt_one.mpr
        (show ‖(p : ℚ_[p])‖₊ < 1 from Padic.norm_p_lt_one)
  simpa only [map_natCast] using
    (Valuation.HasExtension.val_map_lt_one_iff
      (ValuativeRel.valuation ℚ_[p]) (ValuativeRel.valuation E) (p : ℚ_[p])).mpr hp

theorem padicCoefficientResidue_charP : CharP 𝓀[E] p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  rw [← map_natCast (IsLocalRing.residue 𝒪[E]) p]
  apply (IsLocalRing.residue_eq_zero_iff _).mpr
  change ¬ IsUnit (p : 𝒪[E])
  apply Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr
  exact padicCoefficient_valuation_prime_lt_one p E

end
end Dubon2026
