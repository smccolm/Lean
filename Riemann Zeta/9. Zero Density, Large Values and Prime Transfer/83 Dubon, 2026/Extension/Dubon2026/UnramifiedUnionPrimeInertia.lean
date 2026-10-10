import Dubon2026.UnramifiedUnionInfiniteInertia

/-! # Original arithmetic primes and their actual trivial inertia -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Every actual prime above an original base prime outside the exceptional integer has trivial inertia in the whole constructed arithmetic extension. -/
theorem originalUnramifiedUnion_prime_inertia_eq_bot
    (a : 𝓞 K) (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 K)) (hv : a ∉ v.asIdeal)
    (w : HeightOneSpectrum (𝓞 (originalUnramifiedGaloisUnion (Ω := Ω) a)))
    [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.inertia Gal((originalUnramifiedGaloisUnion (Ω := Ω) a)/K) = ⊥ := by
  apply originalUnramifiedUnion_inertia_eq_bot a ha w.asIdeal w.ne_bot
  intro h
  exact hv ((Ideal.mem_of_liesOver w.asIdeal v.asIdeal a).mpr h)

/-- Every original base prime outside the exceptional integer admits an actual prime of the whole arithmetic extension above it, with proved trivial original inertia. -/
theorem originalUnramifiedUnion_exists_prime_trivial_inertia
    (a : 𝓞 K) (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 K)) (hv : a ∉ v.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 (originalUnramifiedGaloisUnion (Ω := Ω) a)),
      w.asIdeal.LiesOver v.asIdeal ∧
        w.asIdeal.inertia Gal((originalUnramifiedGaloisUnion (Ω := Ω) a)/K) = ⊥ := by
  obtain ⟨w, hw⟩ := heightOnePrime_exists_liesOver
    (S := 𝓞 (originalUnramifiedGaloisUnion (Ω := Ω) a)) v
  letI := hw
  exact ⟨w, hw, originalUnramifiedUnion_prime_inertia_eq_bot a ha v hv w⟩

end
end Dubon2026
