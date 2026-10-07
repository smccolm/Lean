import Dubon2026.PrimitiveSymmetricSpectral

/-! # The actual prime-character series and the higher-prime-power correction

This identifies the original prime series with the sum of genuine local
Euler logarithmic derivatives minus a proved holomorphic remainder. A
boundary extension of the logarithmic derivative series remains an input.
-/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The actual sum of negative local logarithmic derivatives of the incomplete symmetric-power Euler factors. -/
def primitiveSymmetricLogSeries {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -logDeriv (primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f r) p) s

/-- At every actual prime, the spectral first term is precisely the Mathlib L-series term of the original prime-character coefficients. -/
theorem primitiveSymmetricSpectralFirstTerm_lseries {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (s : ℂ) :
    primeSpectralFirstTerm (primitiveSymmetricSpectralRoots f r) p s =
      LSeries.term (fun n => (primeLogCoefficients (primitivePrimeCharacter f r) n : ℂ)) s p := by
  rw [primitiveSymmetricSpectralFirstTerm_eq, LSeries.term_def, if_neg p.property.ne_zero,
    Complex.cpow_neg, div_eq_mul_inv]

/-- The genuine prime-supported L-series has exactly its spectral sum over the actual prime subtype. -/
theorem tsum_primitiveSymmetricSpectralFirstTerm {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (s : ℂ) :
    (∑' p : Nat.Primes, primeSpectralFirstTerm (primitiveSymmetricSpectralRoots f r) p s) =
      LSeries (fun n => (primeLogCoefficients (primitivePrimeCharacter f r) n : ℂ)) s := by
  simp_rw [primitiveSymmetricSpectralFirstTerm_lseries]
  unfold LSeries
  apply tsum_subtype_eq_of_support_subset
  intro n hn
  by_contra hp
  have hp' : ¬Nat.Prime n := fun h => hp ((Nat.irreducible_iff_nat_prime n).mpr h)
  apply hn
  simp only [LSeries.term_def, primeLogCoefficients, if_neg hp', Complex.ofReal_zero,
    zero_div, ite_self]

/-- The genuine prime-character first terms are absolutely summable on Re(s)>1 under the displayed coefficient bound. -/
theorem summable_primitiveSymmetricSpectralFirstTerm {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => primeSpectralFirstTerm (primitiveSymmetricSpectralRoots f r) p s) := by
  have he := (lseriesSummable_of_abs_le_vonMangoldt
    (abs_primeLogCoefficients_le (C := (r : ℝ) + 1) (by positivity)
      (fun p hp => abs_primitivePrimeCharacter_le f hbound r hp)) hs).comp_injective
        (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p : ℕ)))
  apply he.congr
  intro p
  exact (primitiveSymmetricSpectralFirstTerm_lseries f r p s).symm

/-- The genuine local logarithmic derivative series equals the original prime-character L-series plus the complete holomorphic higher-prime-power remainder. -/
theorem primitiveSymmetricLogSeries_eq {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) {s : ℂ} (hs : 1 < s.re) :
    primitiveSymmetricLogSeries f r s =
      LSeries (fun n => (primeLogCoefficients (primitivePrimeCharacter f r) n : ℂ)) s +
        primeSpectralTail (primitiveSymmetricSpectralRoots f r) s := by
  unfold primitiveSymmetricLogSeries
  simp_rw [primeSpectralEulerFactor_logDeriv (norm_primitiveSymmetricSpectralRoots_le f hbound r)
    _ (by linarith : 0 < s.re)]
  rw [(summable_primitiveSymmetricSpectralFirstTerm f hbound r hs).tsum_add
    (summable_norm_primeSpectralTailTerm (norm_primitiveSymmetricSpectralRoots_le f hbound r)
      (by linarith : 1 / 2 < s.re)).of_norm, tsum_primitiveSymmetricSpectralFirstTerm]
  rfl

/-- The actual primitive Sato--Tate conclusion follows from its local bound and continuous boundary extension of the genuine local Euler logarithmic derivative series. -/
theorem primitive_satoTate_of_symmetric_log_boundary {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (hboundary : ∀ r : ℕ, 0 < r → ∃ G : ℂ → ℂ,
      ContinuousOn G {s | 1 ≤ s.re} ∧ Set.EqOn G (primitiveSymmetricLogSeries f r) {s | 1 < s.re}) :
    Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability) := by
  apply primitive_satoTate_of_character_boundary f hbound
  intro r hr
  obtain ⟨G,hG,hseries⟩ := hboundary r hr
  refine ⟨fun s => G s - primeSpectralTail (primitiveSymmetricSpectralRoots f r) s, ?_, ?_⟩
  · apply hG.sub
    exact (primitiveSymmetricSpectralTail_analyticOnNhd f hbound r).continuousOn.mono
      (fun s hs => by dsimp at hs ⊢; linarith)
  · intro s hs
    dsimp only
    rw [hseries hs, primitiveSymmetricLogSeries_eq f hbound r hs, add_sub_cancel_right]

end
end Dubon2026
