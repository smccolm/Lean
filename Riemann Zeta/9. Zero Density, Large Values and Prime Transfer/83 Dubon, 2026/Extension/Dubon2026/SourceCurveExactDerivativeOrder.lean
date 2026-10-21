import Dubon2026.SourceCurveIntegralDerivatives
import Dubon2026.SourceCurveAdeleLocalQuotient

/-! DUB-17/18 -> matching cusp-form dimension -> numerical geometric genus
-> the actual canonical j divisor -> exact local derivative orders.
The proved integral derivative coefficient and the pinned derivation rule
for integer powers give ord(Df) = ord(f) - 1 when ord(f) is nonzero in
characteristic zero. This discharges the local ramification-order input;
global canonical-degree and cusp-form identifications remain separate.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem differentialCoeff_D_unit_mul_zpow
    (u : v.toValuationSubringˣ) (n : ℤ) :
    v.differentialCoeff (D K F (((u : v.toValuationSubring) : F) * v.uniformizer ^ n)) =
      v.uniformizer ^ (n - 1) *
        (v.uniformizer * v.differentialCoeff (D K F ((u : v.toValuationSubring) : F)) +
          (n : F) * ((u : v.toValuationSubring) : F)) := by
  apply v.differentialCoeff_unique
  rw [Derivation.leibniz, Derivation.leibniz_zpow]
  conv_lhs => rw [← v.differentialCoeff_smul_dCoord (D K F ((u : v.toValuationSubring) : F))]
  change ((u : v.toValuationSubring) : F) • (n • v.uniformizer ^ (n - 1) • v.dCoord) +
    v.uniformizer ^ n • (v.differentialCoeff (D K F ((u : v.toValuationSubring) : F)) • v.dCoord) = _
  rw [← Int.cast_smul_eq_zsmul F, smul_smul, smul_smul, smul_smul, ← add_smul]
  congr 1
  have he : v.uniformizer ^ (n - 1) * v.uniformizer = v.uniformizer ^ n := by
    calc
      _ = v.uniformizer ^ ((n - 1) + 1) := by
        rw [zpow_add₀ v.uniformizer_ne_zero, zpow_one]
      _ = v.uniformizer ^ n := by congr 1; omega
  linear_combination -v.differentialCoeff (D K F ((u : v.toValuationSubring) : F)) * he

variable [CharZero K] [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField]

theorem ordDifferential_D_eq_ord_sub_one {f : F} (hf : v.ord f ≠ 0) :
    v.ordDifferential (D K F f) = v.ord f - 1 := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hf0 : f ≠ 0 := by
    intro h
    exact hf (h ▸ v.ord_zero)
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 v.irreducible_uniformizerSubring
  change f = ((u : v.toValuationSubring) : F) * v.uniformizer ^ v.ord f at hu
  have hu0 : ((u : v.toValuationSubring) : F) ≠ 0 := by
    exact_mod_cast u.ne_zero
  have hn0 : (v.ord f : F) ≠ 0 := Int.cast_ne_zero.mpr hf
  let a : F := v.differentialCoeff (D K F ((u : v.toValuationSubring) : F))
  let b : F := (v.ord f : F) * ((u : v.toValuationSubring) : F)
  have hb0 : b ≠ 0 := mul_ne_zero hn0 hu0
  have hob : v.ord b = 0 := by
    rw [v.ord_mul hn0 hu0, v.ord_coe_unit, add_zero]
    simpa only [map_intCast] using v.ord_algebraMap (v.ord f : K)
  have ha : a ∈ v.toValuationSubring :=
    v.differentialCoeff_D_mem_of_mem (u : v.toValuationSubring).2
  have hs : v.ord (v.uniformizer * a + b) = 0 := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · rw [ha0, mul_zero, zero_add, hob]
    · rw [add_comm, v.ord_add_eq_of_lt hb0 (mul_ne_zero v.uniformizer_ne_zero ha0), hob]
      rw [hob, v.ord_mul v.uniformizer_ne_zero ha0, v.ord_uniformizer]
      have := v.ord_nonneg_of_mem ha
      omega
  have hs0 : v.uniformizer * a + b ≠ 0 := by
    intro hz
    have he : v.uniformizer * a = -b := eq_neg_of_add_eq_zero_left hz
    have hval : v.adicValuation (v.uniformizer * a) < v.adicValuation b := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · rw [ha0, mul_zero, Valuation.map_zero]
        exact bot_lt_iff_ne_bot.mpr (v.adicValuation_ne_zero hb0)
      · rw [v.adicValuation_eq_exp_neg_ord (mul_ne_zero v.uniformizer_ne_zero ha0),
          v.adicValuation_eq_exp_neg_ord hb0, v.ord_mul v.uniformizer_ne_zero ha0,
          v.ord_uniformizer, hob]
        apply WithZero.exp_lt_exp.mpr
        have := v.ord_nonneg_of_mem ha
        omega
    rw [he, Valuation.map_neg] at hval
    exact (lt_irrefl _) hval
  unfold ordDifferential
  conv_lhs => rw [hu]
  rw [v.differentialCoeff_D_unit_mul_zpow,
    v.ord_mul (zpow_ne_zero _ v.uniformizer_ne_zero) hs0,
    v.ord_zpow, v.ord_uniformizer, mul_one, hs, add_zero]

end
end Dubon2026.SourceCurve.Place
