import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Basic

/-! # Original unramified prime indices throughout a genuine finite Galois extension -/

namespace Dubon2026

open scoped NumberField

open IsDedekindDomain

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- The actual ramification indices of original primes above the same base prime agree in the original Galois number-field extension. -/
theorem numberField_galois_ramificationIdx_eq
    (v : HeightOneSpectrum (𝓞 K)) (w z : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [z.asIdeal.LiesOver v.asIdeal] :
    v.asIdeal.ramificationIdx w.asIdeal = v.asIdeal.ramificationIdx z.asIdeal :=
  Ideal.ramificationIdx_eq_of_isGaloisGroup v.asIdeal w.asIdeal z.asIdeal Gal(L/K)

/-- One actual unramified prime over the original base prime makes every original prime above it unramified. -/
theorem numberField_galois_unramified_at_every_prime
    (v : HeightOneSpectrum (𝓞 K))
    (h : ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal ∧
      v.asIdeal.ramificationIdx w.asIdeal = 1)
    (z : HeightOneSpectrum (𝓞 L)) [z.asIdeal.LiesOver v.asIdeal] :
    v.asIdeal.ramificationIdx z.asIdeal = 1 := by
  obtain ⟨w, hw, he⟩ := h
  letI := hw
  exact (numberField_galois_ramificationIdx_eq v z w).trans he

end Dubon2026
