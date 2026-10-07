import Dubon2026.PrimeEmpiricalIntegral
import Dubon2026.SatoTateCharacterCriterion
import Dubon2026.PrimitiveNormalizedRecurrence
import Dubon2026.FiniteBadPrimeAverages

/-! # Genuine prime character averages imply the actual Sato--Tate weak limit

The final primitive-form theorem displays the unproved arithmetic bound and
positive-order prime-power averages separately. It proves their analytic and
normalization consequences, and does not assert those arithmetic premises.
-/

namespace Dubon2026

open Polynomial MeasureTheory Filter Set
open scoped Topology

noncomputable section

/-- The nonconstant character criterion for actual prime values; the constant mode and finite empirical normalization are derived. -/
theorem prime_satoTate_of_character_averages {x : ℕ → ℝ} {C : ℝ} (hC : 2 ≤ C)
    (hx : ∀ p, Nat.Prime p → |x p| ≤ C)
    (hav : ∀ r : ℕ, 0 < r → Tendsto (fun N : ℕ =>
      (∑ p ∈ Nat.primesLE N, (Chebyshev.S ℝ (r : ℤ)).eval (x p)) /
        Nat.primeCounting N) atTop (𝓝 0)) :
    Tendsto (primeEmpirical x) atTop (𝓝 satoTateProbability) := by
  apply satoTate_tendsto_of_character_integrals (a := -C) (b := C) (by linarith) hC
    (primeEmpirical_ae_mem_Icc (by linarith) (by linarith)
      (fun p hp => abs_le.mp (hx p hp)))
  intro r
  by_cases hr : r = 0
  · subst r
    simpa only [Nat.cast_zero, Chebyshev.S_zero, eval_one, integral_const,
      probReal_univ, one_smul, if_true] using (tendsto_const_nhds (x := (1 : ℝ)))
  · rw [if_neg hr]
    apply (hav r (Nat.pos_of_ne_zero hr)).congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact (integral_primeEmpirical hN (Chebyshev.S ℝ (r : ℤ)).continuous).symm

/-- For the actual primitive form, the good-prime bound and literal prime-power averages suffice; finite ramified terms, Hecke normalization and the complete weak probability bridge are all discharged. -/
theorem primitive_satoTate_of_primePower_averages {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (hav : ∀ r : ℕ, 0 < r → Tendsto (fun N : ℕ =>
      (∑ p ∈ Nat.primesLE N, (normalizedCuspCoefficients f.toCuspForm (p ^ r)).re) /
        Nat.primeCounting N) atTop (𝓝 0)) :
    Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability) := by
  obtain ⟨C, hC, hx⟩ := exists_prime_value_bound_of_good_bound (Nat.pos_of_neZero Q)
    (fun p hp hpQ => (Complex.abs_re_le_norm _).trans (hbound p hp hpQ))
  apply prime_satoTate_of_character_averages hC hx
  intro r hr
  have hd := tendsto_prime_average_difference_of_good_eq (Q := Q) (Nat.pos_of_neZero Q)
    (u := fun p => (Chebyshev.S ℝ (r : ℤ)).eval (normalizedCuspCoefficients f.toCuspForm p).re)
    (v := fun p => (normalizedCuspCoefficients f.toCuspForm (p ^ r)).re)
    (fun p hp hpQ => (primitiveCuspForm_normalized_primePower_re f hp hpQ r).symm)
  have he := hd.add (hav r hr)
  simpa only [sub_add_cancel, add_zero] using he

end
end Dubon2026
