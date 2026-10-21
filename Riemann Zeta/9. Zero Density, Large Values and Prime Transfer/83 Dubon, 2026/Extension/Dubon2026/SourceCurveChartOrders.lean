import Dubon2026.SourceCurvePlaceCenters

/-! DUB-17/18 -> principal divisor degree zero and local derivative orders.
This identifies the actual normalized place order with the Dedekind prime
valuation of its actual chart center. It is the bridge needed to consume
pinned ideal norm and ramification identities without renormalizing orders.
The normalization argument is adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver,
Uniqueness section only.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain WithZero IsLocalRing

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

theorem eq_ord_of_addHom_of_nonneg_iff (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x := by
  obtain ⟨t, ht0, ht1⟩ := hone

  have hφ1 : φ 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega

  have hinv : ∀ y, y ≠ 0 → φ y⁻¹ = -φ y := by
    intro y hy
    have h1 : φ (y * y⁻¹) = φ y + φ y⁻¹ := hmul y y⁻¹ hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, hφ1] at h1
    omega

  have hpow : ∀ (y : F), y ≠ 0 → ∀ m : ℕ, φ (y ^ m) = m * φ y := by
    intro y hy m
    induction m with
    | zero => simpa using hφ1
    | succ m ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hy) hy, ih]
      push_cast
      ring
  have hzpow : ∀ (y : F) (n : ℤ), y ≠ 0 → φ (y ^ n) = n * φ y := by
    intro y n hy
    rcases n with m | m
    · simpa using hpow y hy m
    · rw [zpow_negSucc, hinv _ (pow_ne_zero _ hy), hpow y hy, Int.negSucc_eq]
      push_cast
      ring

  have hsign : ∀ y, y ≠ 0 → (0 ≤ φ y ↔ 0 ≤ w.ord y) := by
    intro y hy
    rw [hiff y hy, w.mem_iff_ord_nonneg]
  have hzero : ∀ y, y ≠ 0 → (φ y = 0 ↔ w.ord y = 0) := by
    intro y hy
    have h1 := hsign y hy
    have h2 := hsign y⁻¹ (inv_ne_zero hy)
    rw [hinv y hy, w.ord_inv] at h2
    omega

  have htord : 0 < w.ord t := by
    have h1 := (hsign t ht0).mp (by omega)
    have h2 := (hzero t ht0).not.mp (by omega)
    omega

  have hcancel : ∀ y, y ≠ 0 → w.ord y = φ y * w.ord t := by
    intro y hy
    have hyt : y * t ^ (-(φ y)) ≠ 0 := mul_ne_zero hy (zpow_ne_zero _ ht0)
    have h1 : φ (y * t ^ (-(φ y))) = 0 := by
      rw [hmul _ _ hy (zpow_ne_zero _ ht0), hzpow t _ ht0, ht1]
      ring
    have h2 : w.ord (y * t ^ (-(φ y))) = 0 := (hzero _ hyt).mp h1
    rw [w.ord_mul hy (zpow_ne_zero _ ht0), w.ord_zpow] at h2
    linarith

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπcancel := hcancel (π : F) hπ0
  rw [w.ord_coe_irreducible hπ] at hπcancel

  have htord1 : w.ord t = 1 := by
    have hdvd : w.ord t ∣ 1 := ⟨φ (π : F), by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have := hcancel x hx
  rw [htord1, mul_one] at this
  exact this.symm

end Uniqueness

theorem ord_eq_neg_log_center_valuation
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    (v : Place K F) (hR : ∀ r : R, algebraMap R F r ∈ v.toValuationSubring)
    {x : F} (hx : x ≠ 0) :
    v.ord x = -log ((centerHeightOneSpectrum R v hR).valuation F x) := by
  let P := centerHeightOneSpectrum R v hR
  symm
  apply eq_ord_of_addHom_of_nonneg_iff v (fun y => -log (P.valuation F y))
  · intro a b ha hb
    rw [map_mul, log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
    ring
  · obtain ⟨t, ht⟩ := P.valuation_exists_uniformizer F
    refine ⟨t, ?_, ?_⟩
    · intro h
      rw [h, map_zero] at ht
      exact exp_ne_zero ht.symm
    · rw [ht, log_exp]
      ring
  · intro y hy
    have hy0 : P.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    have hm : y ∈ v.toValuationSubring ↔ P.valuation F y ≤ 1 := by
      rw [toValuationSubring_eq_of_forall_mem v hR,
        HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      rfl
    rw [hm, ← WithZero.log_le_log hy0 one_ne_zero, log_one]
    omega
  · exact hx

end
end Dubon2026.SourceCurve.Place
