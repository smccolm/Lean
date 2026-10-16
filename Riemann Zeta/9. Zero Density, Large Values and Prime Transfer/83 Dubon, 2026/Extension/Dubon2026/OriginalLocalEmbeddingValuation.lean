import Dubon2026.OriginalLocalEmbeddingPrime

/-! # The original local embedding induces exactly its prime-adic valuation

The pinned denominator theorem and the one-dimensional valuation-overring
theorem identify the pulled-back valuation ring with the original prime
localization. This supplies the exact topology needed to extend the
arithmetic orbit embedding to the individual completion on DUB-17's route.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField ValuativeRel

variable (L E : Type) [Field L] [NumberField L] [Field E] [Algebra L E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]

/-- The literal pulled-back local valuation is equivalent to the
original adic valuation of the genuinely induced number-field prime. -/
theorem originalLocalEmbeddingPrime_valuation_isEquiv :
    ((originalLocalEmbeddingPrime L E p hp).valuation L).IsEquiv
      ((ValuativeRel.valuation E).comap (algebraMap L E)) := by
  let w := originalLocalEmbeddingPrime L E p hp
  let v := (ValuativeRel.valuation E).comap (algebraMap L E)
  have hint (n : 𝓞 L) : v (algebraMap (𝓞 L) L n) ≤ 1 :=
    originalIntegerMap_mem_valuationInteger L E n
  have hle : valuationSubringAtPrime L w ≤ v.valuationSubring := by
    intro x hx
    have hxv : w.valuation L x ≤ 1 := valuationSubringAtPrime_le_valuation w hx
    obtain ⟨n, d, hxd⟩ := w.exists_primeCompl_mul_eq_of_integer x hxv
    have hd : v (algebraMap (𝓞 L) L (d : 𝓞 L)) = 1 := by
      apply le_antisymm (hint d)
      apply not_lt.mp
      intro hdlt
      exact d.property ((originalLocalEmbeddingPrime_mem_iff L E p hp d).mpr hdlt)
    have he := congrArg v hxd
    rw [map_mul, hd, mul_one] at he
    exact he.trans_le (hint n)
  have hpv : v (p : L) < 1 := by
    have h := (originalLocalEmbeddingPrime_mem_iff L E p hp (p : 𝓞 L)).mp
      (originalLocalEmbeddingPrime_prime_mem L E p hp)
    change ValuativeRel.valuation E (algebraMap L E (p : L)) < 1
    simpa only [map_natCast] using h
  have hp0 : 0 < v (p : L) :=
    pos_iff_ne_zero.mpr ((v.ne_zero_iff).mpr (Nat.cast_ne_zero.mpr hp.ne_zero))
  have hn : v.IsNontrivial := Valuation.IsNontrivial_iff_exists_one_lt.mpr
    ⟨(p : L)⁻¹, by rw [map_inv₀]; exact (one_lt_inv₀ hp0).mpr hpv⟩
  have heq : valuationSubringAtPrime L w = v.valuationSubring :=
    ValuationSubring.eq_of_le_of_ne_top _ hle
      (fun h => ((Valuation.valuationSubring_eq_top_iff v).mp h) hn)
  apply (Valuation.isEquiv_iff_valuationSubring (w.valuation L) v).mpr
  exact (valuationSubringAtPrime_eq_valuationSubring (K := L) w).symm.trans heq

end
end Dubon2026
