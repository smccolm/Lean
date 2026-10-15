import Dubon2026.OriginalSPlaceBaseChangeInjective

/-! # Reflection of original support under actual idele base change

The original local valuation power formula reflects integral-unit
membership because every actual ramification index is nonzero. This
supplies the supported coefficient needed when descending outside units
for DUB-17's arithmetic class-formation invariant comparison.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)

include hST

/-- Original idele inclusion reflects the actual pulled-back support condition. -/
theorem originalIdeleBaseChangeMap_reflects_supported
    (x : (AdeleRing (𝓞 K) K)ˣ)
    (hx : originalIdeleBaseChangeMap K L x ∈ numberFieldSupportedIdeles L T) :
    x ∈ numberFieldSupportedIdeles K S := by
  simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one] at hx ⊢
  intro v hv
  obtain ⟨w, rfl⟩ := originalFinitePrimeBelow_surjective K L v
  letI := originalFinitePrimeBelow_liesOver K L w
  have hw := hx w (fun hw => hv ((hST w).mp hw))
  change Valued.v (originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w
    (numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) x).val) = 1 at hw
  rw [originalAdicBaseChangeMap_valuation] at hw
  exact (pow_eq_one_iff_of_nonneg zero_le
    (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w.asIdeal
      (originalFinitePrimeBelow K L w).ne_bot)).mp hw

end
end Dubon2026
