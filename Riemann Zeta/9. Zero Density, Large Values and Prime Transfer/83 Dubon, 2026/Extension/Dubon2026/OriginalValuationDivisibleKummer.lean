import Dubon2026.OriginalValuationUnitLocalization

/-! # Valuation-divisible Kummer roots at the original finite primes

Rescaling by an actual base-field element turns a valuation-divisible root
into a unit root at the same prime. Localizing away from that prime reuses
the proved original finite étale root algebra and its normalization theorem.
This is the nonunit root input for the q-primary class comparison in DUB-17.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain IntermediateField
open scoped NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- A generating Kummer root is unramified at an original prime where its radicand valuation is an actual qth power and q is a unit. -/
theorem originalValuationDivisibleKummer_unramified
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (q : ℕ) [Fact q.Prime] (hq : (q : 𝓞 K) ∉ v.asIdeal)
    (u c : Kˣ) (hv : v.valuation K (u : K) = v.valuation K (c : K) ^ q)
    (β : L) (hβ : β ^ q = algebraMap K L (u : K))
    (hgen : IntermediateField.adjoin K {β} = ⊤) :
    v.asIdeal.ramificationIdx w.asIdeal = 1 := by
  let u' : Kˣ := u / c ^ q
  have hu' : v.valuation K (u' : K) = 1 := by
    rw [show (u' : K) = (u : K) / (c : K) ^ q from Units.val_div_eq_div_val _ _]
    rw [map_div₀, map_pow, hv, div_self]
    exact pow_ne_zero q ((map_ne_zero (v.valuation K)).mpr c.ne_zero)
  obtain ⟨b, hb, hbmem, hqb, z, hz⟩ := originalValuationUnit_exists_localization K v q hq u' hu'
  let γ : L := β / algebraMap K L (c : K)
  have hc : algebraMap K L (c : K) ≠ 0 := (map_ne_zero (algebraMap K L)).mpr c.ne_zero
  have hγ : γ ^ q = algebraMap (originalLocalizedIntegers K b hb) L z.val := by
    change (β / algebraMap K L (c : K)) ^ q = algebraMap K L z.val.val
    rw [hz]
    rw [show (u' : K) = (u : K) / (c : K) ^ q from Units.val_div_eq_div_val _ _]
    rw [div_pow, hβ, map_div₀, map_pow]
  have hγgen : IntermediateField.adjoin K {γ} = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply IntermediateField.adjoin_le_iff.mpr
    apply Set.singleton_subset_iff.mpr
    have hback : γ * algebraMap K L (c : K) = β := div_mul_cancel₀ β hc
    rw [← hback]
    exact (IntermediateField.adjoin K {γ}).mul_mem
      (IntermediateField.subset_adjoin K {γ} (Set.mem_singleton γ))
      ((IntermediateField.adjoin K {γ}).algebraMap_mem (c : K))
  have hbUpper : algebraMap (𝓞 K) (𝓞 L) b ∉ w.asIdeal := by
    intro h
    apply hbmem
    rw [Ideal.over_def w.asIdeal v.asIdeal]
    exact h
  have h := originalLocalizedUnitKummer_unramifiedAway K b hb q L z γ hγ hqb hγgen w hbUpper
  rwa [← Ideal.over_def w.asIdeal v.asIdeal] at h

end
end Dubon2026
