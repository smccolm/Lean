import Dubon2026.SourceAlgebraicValuationPowers
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera inequality ->
dimension one of the algebraic coefficient valuation. Positive valuation
powers already proved from minimal polynomials make comparable extending
valuations equal and detect the trivial valuation. This specializes the
external transcendence-degree argument to the required algebraic case. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]

theorem algebraic_valuation_eq_of_le {V W : ValuationSubring E}
    (hle : V ≤ W) (hcomap : V.comap (algebraMap F E) = W.comap (algebraMap F E)) : V = W := by
  refine le_antisymm hle fun x hx => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨n, a, hn, ha, heq⟩ := exists_valuation_pow_eq_of_isIntegral V.valuation hx0
    (Algebra.IsIntegral.isIntegral (R := F) x)
  have haE : algebraMap F E a ≠ 0 := (_root_.map_ne_zero _).mpr ha
  have huv : V.valuation (x ^ n / algebraMap F E a) = 1 := by
    rw [map_div₀, map_pow, heq, div_self ((Valuation.ne_zero_iff _).mpr haE)]
  have hu : IsUnit (⟨x ^ n / algebraMap F E a, (V.valuation_le_one_iff _).mp huv.le⟩ : V) :=
    (V.valuation_eq_one_iff _).mpr huv
  have huw := (W.valuation_eq_one_iff _).mp (hu.map (V.inclusion W hle))
  change W.valuation (x ^ n / algebraMap F E a) = 1 at huw
  rw [map_div₀, map_pow, div_eq_one_iff_eq ((Valuation.ne_zero_iff _).mpr haE)] at huw
  have hamem : algebraMap F E a ∈ W := (W.valuation_le_one_iff _).mp (by
    rw [← huw]
    exact pow_le_one₀ zero_le' ((W.valuation_le_one_iff _).mpr hx))
  have hamemV : algebraMap F E a ∈ V := by
    change a ∈ V.comap (algebraMap F E)
    rwa [hcomap]
  rw [← V.valuation_le_one_iff]
  exact (pow_le_one_iff_of_nonneg zero_le' hn.ne').mp
    (heq ▸ (V.valuation_le_one_iff _).mpr hamemV)

theorem algebraic_valuation_eq_top_of_comap_eq_top (V : ValuationSubring E)
    (hV : V.comap (algebraMap F E) = ⊤) : V = ⊤ := by
  apply le_antisymm le_top
  intro x _
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨n, a, hn, ha, heq⟩ := exists_valuation_pow_eq_of_isIntegral V.valuation hx0
    (Algebra.IsIntegral.isIntegral (R := F) x)
  have hamem : algebraMap F E a ∈ V := by
    change a ∈ V.comap (algebraMap F E)
    rw [hV]
    trivial
  rw [← V.valuation_le_one_iff]
  exact (pow_le_one_iff_of_nonneg zero_le' hn.ne').mp
    (heq ▸ (V.valuation_le_one_iff _).mpr hamem)

end
end Dubon2026.SourceCurve
