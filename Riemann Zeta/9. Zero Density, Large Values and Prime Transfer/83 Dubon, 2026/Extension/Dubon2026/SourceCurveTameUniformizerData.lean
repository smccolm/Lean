import Dubon2026.SourceCurveUniformizerResidue

/-! The actual chosen uniformizer supplies the two hypotheses of the
already proved residue-unit character. The principal maximal ideal and
ordinary cancellation replace any new uniformizer existence construction.
This discharges the character's local algebra inputs on the DUB-17/18
wild different chain. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsLocalRing
variable {K M : Type*} [Field K] [Field M] [Algebra K M] (v : Place K M)

theorem uniformizer_mem_maximalIdeal :
    v.uniformizerSubring ∈ maximalIdeal v.toValuationSubring := by
  rw [v.maximalIdeal_eq_span_uniformizer]
  exact Ideal.mem_span_singleton_self _

theorem uniformizer_generates_mod_square :
    ∀ x ∈ maximalIdeal v.toValuationSubring, ∃ y : v.toValuationSubring,
      x - v.uniformizerSubring * y ∈ (maximalIdeal v.toValuationSubring) ^ 2 := by
  intro x hx
  rw [v.maximalIdeal_eq_span_uniformizer, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, by rw [sub_self]; exact zero_mem _⟩

theorem uniformizer_regular_mod_square :
    ∀ c : v.toValuationSubring,
      c * v.uniformizerSubring ∈ (maximalIdeal v.toValuationSubring) ^ 2 →
      c ∈ maximalIdeal v.toValuationSubring := by
  intro c hc
  rw [v.maximalIdeal_eq_span_uniformizer, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hc
  rw [v.maximalIdeal_eq_span_uniformizer, Ideal.mem_span_singleton]
  have h : v.uniformizerSubring * v.uniformizerSubring ∣ v.uniformizerSubring * c := by
    simpa only [pow_two, mul_comm c] using hc
  exact (mul_dvd_mul_iff_left v.irreducible_uniformizerSubring.ne_zero).mp h

end
end Dubon2026.SourceCurve.Place
