import Dubon2026.Gamma0LatticeSieve

/-! # The exact gcd decomposition of the congruence-sieved lattice series -/

namespace Dubon2026

open UpperHalfPlane EisensteinSeries

noncomputable section

/-- The actual Eisenstein row kernel restricted by the congruence and coprimality sieve. -/
def gamma0SievedTerm (Q : ℕ) (s : ℂ) (z : ℍ) : (Fin 2 → ℤ) → ℂ :=
  (gamma0SievedRows Q).indicator (fun v => nonholomorphicEisensteinTerm s v z)

/-- The sieved lattice series, with the same division by the two signs as the primitive series. -/
def gamma0SievedSeries (Q : ℕ) (s : ℂ) (z : ℍ) : ℂ :=
  (1 / 2 : ℂ) * ∑' v : Fin 2 → ℤ, gamma0SievedTerm Q s z v

/-- Restricting the actual absolutely convergent lattice sum preserves convergence. -/
theorem summable_gamma0SievedTerm (Q : ℕ) {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    Summable (gamma0SievedTerm Q s z) :=
  (summable_norm_nonholomorphicEisensteinTerm hs z).of_norm.indicator _

/-- The exact dilation factor in the sieved kernel includes the multiplier's coprimality. -/
theorem gamma0SievedTerm_nsmul (Q n : ℕ) (s : ℂ) (z : ℍ) (v : gammaSet 1 1 0) :
    gamma0SievedTerm Q s z (n • v.val) =
      (if Nat.Coprime n Q then (n : ℂ) ^ (-(2 * s)) else 0) *
        (if (Q : ℤ) ∣ v.val 0 then nonholomorphicEisensteinTerm s v.val z else 0) := by
  classical
  simp only [gamma0SievedTerm, Set.indicator_apply, gamma0SievedRows_nsmul,
    nonholomorphicEisensteinTerm_nsmul]
  split_ifs <;> simp_all

/-- Restricting the genuine gcd-one fiber to Q-divisible first entries is exactly the primitive series. -/
theorem tsum_primitive_gamma0_indicator (Q : ℕ) (s : ℂ) (z : ℍ) :
    (∑' v : gammaSet 1 1 0,
      if (Q : ℤ) ∣ v.val 0 then nonholomorphicEisensteinTerm s v.val z else 0) =
        2 * gamma0Eisenstein Q s z := by
  classical
  rw [gamma0Eisenstein,
    tsum_subtype (gammaSet 1 1 0)
      (fun v => if (Q : ℤ) ∣ v 0 then nonholomorphicEisensteinTerm s v z else 0),
    tsum_subtype (gamma0PrimitiveRows Q) (fun v => nonholomorphicEisensteinTerm s v z)]
  have he : (∑' v : Fin 2 → ℤ, (gammaSet 1 1 0).indicator
      (fun v => if (Q : ℤ) ∣ v 0 then nonholomorphicEisensteinTerm s v z else 0) v) =
      ∑' v : Fin 2 → ℤ, (gamma0PrimitiveRows Q).indicator
        (fun v => nonholomorphicEisensteinTerm s v z) v := by
    apply tsum_congr
    intro v
    simp only [Set.indicator_apply, gammaSet_one_eq, Set.mem_setOf_eq, gamma0PrimitiveRows]
    split_ifs <;> simp_all
  rw [he]
  ring

/-- A nonzero gcd fiber of the actual sieved series has the exact coprime scalar factor. -/
theorem tsum_gamma0SievedTerm_gcd (Q : ℕ) {s : ℂ} (hs : 1 < s.re) (z : ℍ) (n : ℕ) :
    (∑' v : gammaSet 1 n 0, gamma0SievedTerm Q s z v.val) =
      (if Nat.Coprime n Q then (n : ℂ) ^ (-(2 * s)) else 0) *
        (2 * gamma0Eisenstein Q s z) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hs0 : -(2 * s) ≠ 0 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [Complex.neg_re, two_mul, Complex.add_re, Complex.zero_re] at h'
      linarith
    have he : ∀ v : gammaSet 1 0 0, gamma0SievedTerm Q s z v.val = 0 := by
      intro v
      simp only [gamma0SievedTerm, Set.indicator_apply, nonholomorphicEisensteinTerm_gcd,
        Nat.cast_zero, Complex.zero_cpow hs0, zero_mul, ite_self]
    simp [he, Complex.zero_cpow hs0]
  · letI : NeZero n := ⟨hn⟩
    have he : (∑' v : gammaSet 1 n 0, gamma0SievedTerm Q s z v.val) =
        ∑' v : gammaSet 1 n 0,
          (if Nat.Coprime n Q then (n : ℂ) ^ (-(2 * s)) else 0) *
            (if (Q : ℤ) ∣ divIntMap n v.val 0 then
              nonholomorphicEisensteinTerm s (divIntMap n v.val) z else 0) := by
      apply tsum_congr
      intro v
      conv_lhs => rw [gammaSet_eq_gcd_mul_divIntMap v.property]
      exact gamma0SievedTerm_nsmul Q n s z (gammaSetDivGcdEquiv n v)
    rw [he, tsum_mul_left]
    congr 1
    rw [← tsum_primitive_gamma0_indicator Q s z]
    simpa only [gammaSetDivGcdEquiv_eq] using
      (gammaSetDivGcdEquiv n).tsum_eq (fun v : gammaSet 1 1 0 =>
        if (Q : ℤ) ∣ v.val 0 then nonholomorphicEisensteinTerm s v.val z else 0)

/-- The full congruence sieve decomposes into its actual coprime Dirichlet series and primitive rows. -/
theorem gamma0SievedSeries_eq_coprime_series (Q : ℕ) {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    gamma0SievedSeries Q s z =
      (∑' n : ℕ, if Nat.Coprime n Q then (n : ℂ) ^ (-(2 * s)) else 0) *
        gamma0Eisenstein Q s z := by
  classical
  have hh : Summable (fun v : Σ n : ℕ, gammaSet 1 n 0 => gamma0SievedTerm Q s z v.2.val) := by
    simpa only [gammaSetDivGcdSigmaEquiv_symm_eq] using
      gammaSetDivGcdSigmaEquiv.symm.summable_iff.mpr (summable_gamma0SievedTerm Q hs z)
  have he : (∑' v : Fin 2 → ℤ, gamma0SievedTerm Q s z v) =
      (∑' n : ℕ, if Nat.Coprime n Q then (n : ℂ) ^ (-(2 * s)) else 0) *
        (2 * gamma0Eisenstein Q s z) := by
    rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq]
    simp only [gammaSetDivGcdSigmaEquiv_symm_eq]
    rw [hh.tsum_sigma]
    exact (tsum_congr (fun n => tsum_gamma0SievedTerm_gcd Q hs z n)).trans tsum_mul_right
  rw [gamma0SievedSeries, he]
  ring

end
end Dubon2026
