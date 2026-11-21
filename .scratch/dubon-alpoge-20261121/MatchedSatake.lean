import Dubon2026.PrimitiveSymmetricSpectral

/-! # Applying a rank-independent Satake bound to the original Hecke roots

Alpöge's `GlobalTheory.T.satakeParameter_normSq_lt_absNorm_unitaryCusp`
bounds every Satake parameter of a unitary cuspidal representation at an
unramified place of a totally complex field. Its bound is the residue norm,
independent of the rank. Here the lifted spectrum is supplied in its original
multiset-of-units format. Matching it to Dubon's normalized roots is a separate
arithmetic input at the chosen prime.
-/

namespace Dubon2026

open Filter
noncomputable section

/-- A single matched lifted spectrum controls both extreme powers of the
original Hecke roots, allowing repeated eigenvalues and either ordering. -/
theorem primitive_satake_power_bounds_of_matched_lift {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (hpQ : ¬(p : ℕ) ∣ Q)
    (r : ℕ) (B : Multiset ℂˣ) {q : ℝ}
    (hmatch : B.map (fun z : ℂˣ => (z : ℂ)) =
      (Finset.univ : Finset (Fin (r+1))).val.map (primitiveSymmetricSpectralRoots f r p))
    (hlift : ∀ z ∈ B, ‖(z : ℂ)‖ ^ 2 < q) :
    (‖primitiveSatakePlus f p‖ ^ r) ^ 2 < q ∧
      (‖primitiveSatakeMinus f p‖ ^ r) ^ 2 < q := by
  have h (i : Fin (r + 1)) : ‖primitiveSymmetricSpectralRoots f r p i‖ ^ 2 < q := by
    have hm : primitiveSymmetricSpectralRoots f r p i ∈ B.map (fun z : ℂˣ => (z : ℂ)) := by
      rw [hmatch]
      exact Multiset.mem_map_of_mem _ (Finset.mem_univ i)
    obtain ⟨z, hz, he⟩ := Multiset.mem_map.mp hm
    rw [← he]
    exact hlift z hz
  constructor
  · simpa [primitiveSymmetricSpectralRoots, hpQ] using h (Fin.last r)
  · simpa [primitiveSymmetricSpectralRoots, hpQ] using h 0

/-- Matching in unbounded degrees at a fixed good prime with a common local
bound gives the sharp coefficient inequality, even along a sparse set of degrees. -/
theorem primitive_prime_bound_of_matched_lifts {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (p : Nat.Primes) (hpQ : ¬(p : ℕ) ∣ Q)
    (B : ℕ → Multiset ℂˣ) (q : ℝ)
    (hlift : ∀ r, ∀ z ∈ B r, ‖(z : ℂ)‖ ^ 2 < q)
    (hmatch : ∃ᶠ r in atTop, (B r).map (fun z : ℂˣ => (z : ℂ)) =
      (Finset.univ : Finset (Fin (r+1))).val.map (primitiveSymmetricSpectralRoots f r p)) :
    ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2 := by
  have bounds := hmatch.mono fun r hm =>
    primitive_satake_power_bounds_of_matched_lift f p hpQ r (B r) hm (hlift r)
  have le_one (x : ℝ) (hx : ∃ᶠ r : ℕ in atTop, (x ^ r)^2 < q) : x ≤ 1 := by
    by_contra! h
    obtain ⟨r, hr, hbig⟩ := (hx.and_eventually
      ((tendsto_pow_atTop_atTop_of_one_lt h).eventually_ge_atTop (max q 1))).exists
    have hq := (le_max_left q 1).trans hbig
    have h1 := (le_max_right q 1).trans hbig
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : 0 ≤ x^r)]
  have ha := le_one _ (bounds.mono fun _ h => h.1)
  have hb := le_one _ (bounds.mono fun _ h => h.2)
  rw [← (primitiveSatake_trace_det f p).1]
  exact (norm_add_le _ _).trans (by linarith)

end
end Dubon2026
