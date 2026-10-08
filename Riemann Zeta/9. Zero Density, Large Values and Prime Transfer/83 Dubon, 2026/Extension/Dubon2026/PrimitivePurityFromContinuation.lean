import Dubon2026.PrimitiveHigherTensorEuler
import Dubon2026.SpectralLocalConvergence

/-! # Local Hecke purity from genuine higher even symmetric continuations -/

namespace Dubon2026

noncomputable section

/-- Holomorphic continuation of the actual even symmetric Euler functions to Re(s)>1
forces both actual good-prime Hecke roots to have norm at most one. The continuation inputs
are stated on their proved far convergence half-planes, without a purity premise. -/
theorem primitiveSatake_norm_le_one_of_even_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (H : ℕ → ℂ → ℂ)
    (hH : ∀ t, DifferentiableOn ℂ (H t) {s : ℂ | 1 < s.re})
    (hmatch : ∀ t, Set.EqOn (H t) (primitiveSymmetricLFunction f (2 * t))
      {s : ℂ | (2 * t : ℕ) + 1 < s.re}) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) :
    ‖primitiveSatakePlus f p‖ ≤ 1 ∧ ‖primitiveSatakeMinus f p‖ ≤ 1 := by
  have hroot (r : ℕ) (i : Fin (r + 1) × Fin (r + 1)) :
      ‖primitiveHigherTensorRoots f r ⟨p, hp⟩ i‖ < (p : ℝ) ^ 2 := by
    have hs : LSeriesSummable (primitiveHigherTensorCoefficient f r) (2 : ℂ) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re
        ((primitiveHigherTensor_abscissa_le_of_even_continuation f hk H hH hmatch r).trans_lt (by exact_mod_cast (show (1 : ℝ) < (2 : ℂ).re by norm_num)))
    have hh := spectral_root_norm_lt_of_LSeriesSummable (primitiveHigherTensorRoots f r) hs ⟨p, hp⟩ i
    simpa using hh
  have hplus (r : ℕ) : (‖primitiveSatakePlus f p‖ ^ 2) ^ r < (p : ℝ) ^ 2 := by
    have hh := hroot r (Fin.last r, Fin.last r)
    simpa only [primitiveHigherTensorRoots, primitiveSymmetricSpectralRoots, if_neg hpQ,
      Fin.val_last, Nat.sub_self, pow_zero, mul_one, norm_mul, norm_pow,
      ← pow_two, ← pow_mul, Nat.mul_comm r 2] using hh
  have hminus (r : ℕ) : (‖primitiveSatakeMinus f p‖ ^ 2) ^ r < (p : ℝ) ^ 2 := by
    have hh := hroot r (0, 0)
    simpa only [primitiveHigherTensorRoots, primitiveSymmetricSpectralRoots, if_neg hpQ,
      Fin.val_zero, Nat.sub_zero, pow_zero, one_mul, norm_mul, norm_pow,
      ← pow_two, ← pow_mul, Nat.mul_comm r 2] using hh
  have hsq (x : ℝ) (h : ∀ r : ℕ, (x ^ 2) ^ r < (p : ℝ) ^ 2) : x ^ 2 ≤ 1 := by
    by_contra hn
    obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt ((p : ℝ) ^ 2) (lt_of_not_ge hn)
    exact (not_lt_of_ge (h r).le) hr
  exact ⟨by nlinarith [hsq _ hplus, norm_nonneg (primitiveSatakePlus f p)],
    by nlinarith [hsq _ hminus, norm_nonneg (primitiveSatakeMinus f p)]⟩

/-- The genuine determinant-one roots have exact unit norm once the actual even symmetric
continuations have been supplied. -/
theorem primitiveSatake_unit_of_even_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (H : ℕ → ℂ → ℂ)
    (hH : ∀ t, DifferentiableOn ℂ (H t) {s : ℂ | 1 < s.re})
    (hmatch : ∀ t, Set.EqOn (H t) (primitiveSymmetricLFunction f (2 * t))
      {s : ℂ | (2 * t : ℕ) + 1 < s.re}) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) :
    ‖primitiveSatakePlus f p‖ = 1 ∧ ‖primitiveSatakeMinus f p‖ = 1 := by
  obtain ⟨ha, hb⟩ := primitiveSatake_norm_le_one_of_even_continuation f hk H hH hmatch hp hpQ
  have hd : ‖primitiveSatakePlus f p‖ * ‖primitiveSatakeMinus f p‖ = 1 := by
    rw [← norm_mul, (primitiveSatake_trace_det f p).2, norm_one]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (primitiveSatakePlus f p))]
  · nlinarith [mul_le_mul_of_nonneg_right ha (norm_nonneg (primitiveSatakeMinus f p))]

/-- The exact good-prime Deligne bound is a proved consequence of the displayed genuine
even symmetric continuation inputs, with no coefficient-bound premise. -/
theorem primitive_prime_bound_of_even_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (H : ℕ → ℂ → ℂ)
    (hH : ∀ t, DifferentiableOn ℂ (H t) {s : ℂ | 1 < s.re})
    (hmatch : ∀ t, Set.EqOn (H t) (primitiveSymmetricLFunction f (2 * t))
      {s : ℂ | (2 * t : ℕ) + 1 < s.re}) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) :
    ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2 :=
  (primitiveSatake_unit_iff_bound f hp hpQ).mp
    (primitiveSatake_unit_of_even_continuation f hk H hH hmatch hp hpQ)

end
end Dubon2026
