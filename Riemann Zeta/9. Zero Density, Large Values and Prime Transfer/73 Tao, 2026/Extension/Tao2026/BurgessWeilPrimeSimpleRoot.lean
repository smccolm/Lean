import Tao2026.FiniteFieldNormStepanov

/-!
# Sharp Weil bounds for split polynomials with a simple root

Stepanov's explicit eventual square-root bound is amplified through the
unconditional Newton recurrence. This proves the sharp root-support bound
in every extension, and its base-field monic split-polynomial specialization.
-/

namespace Tao2026
open Finset Polynomial Filter
open scoped BigOperators Topology
noncomputable section

theorem real_sqrt_nat_pow_eq_pow_sqrt (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

theorem primeKummerExtensionCorrelation_eventually_norm_le_of_simple_root
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1)
    (P : (ZMod p)[X]) (hP : P ≠ 0) (a : ZMod p) (ha : P.rootMultiplicity a = 1) :
    ∀ᶠ q : ℕ in atTop, ‖primeKummerExtensionCorrelation p χ P q‖ ≤
      (4 * (p - 1 : ℕ) * ((p - 1 : ℕ) * (P.natDegree : ℝ) + 1) ^ 2 + P.natDegree) *
        Real.sqrt p ^ (q + 1) := by
  let C := 16 * (p - 1) ^ 2 * ((p - 1) * P.natDegree + 1) ^ 2
  filter_upwards [eventually_ge_atTop (max 1 C)] with q hq
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show q ≠ 0 by omega)
  let E := FiniteField.Extension (ZMod p) p (q + 2)
  letI : Fintype E := Fintype.ofFinite E
  letI : CharP E p := charP_of_injective_algebraMap' (ZMod p) p
  let f := algebraMap (ZMod p) E
  have hcard : Fintype.card E = p ^ (q + 2) := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using
      (FiniteField.natCard_extension (ZMod p) p (q + 2))
  have hlarge : 16 * (p - 1) ^ 2 * ((p - 1) * (P.map f).natDegree + 1) ^ 2 ≤ p ^ (q + 2) := by
    rw [natDegree_map]
    change C ≤ p ^ (q + 2)
    exact (show C ≤ q + 2 by omega).trans (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have hroot : (P.map f).rootMultiplicity (f a) = 1 := by
    rw [← eq_rootMultiplicity_map f.injective a]
    exact ha
  have h := finiteField_norm_polynomial_sum_le_sqrt_of_rootMultiplicity_one p E (q + 2)
    hcard (P.map f) (Polynomial.map_ne_zero hP) (f a) hroot χ hχ hlarge
  rw [primeKummerExtensionCorrelation_succ_eq_normLift]
  change ‖∑ x : E, χ (Algebra.norm (ZMod p) ((P.map f).eval x))‖ ≤ _
  simpa only [natDegree_map, real_sqrt_nat_pow_eq_pow_sqrt _ (Nat.cast_nonneg p), Nat.add_assoc] using h

theorem primeRootMultisetExtensionWeilBounds_of_simple_root
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1)
    (R : Multiset (ZMod p)) (a : ZMod p) (ha : R.count a = 1) :
    PrimeRootMultisetExtensionWeilBounds p χ R := by
  have hmem : a ∈ R := Multiset.count_pos.1 (by omega)
  have hcount : R.count a < orderOf χ := by
    have horder := mulChar_orderOf_two_le_of_ne_one χ hχ
    omega
  let P := primeKummerRootMultisetPolynomial R
  have hP : P ≠ 0 := (primeKummerRootMultisetPolynomial_monic R).ne_zero
  have hroot : P.rootMultiplicity a = 1 := by
    simpa only [P, primeKummerRootMultisetPolynomial_rootMultiplicity] using ha
  have hbound := primeKummerExtensionCorrelation_eventually_norm_le_of_simple_root p χ hχ P hP a hroot
  apply primeRootMultisetExtensionWeilBounds_of_eventually_norm_le p χ R a hmem hcount
    (4 * (p - 1 : ℕ) * ((p - 1 : ℕ) * (P.natDegree : ℝ) + 1) ^ 2 + P.natDegree) (by positivity)
  simpa only [P, primeKummerExtensionCorrelation_eq_rootMultiset] using hbound

theorem norm_primePolynomialCharacterCorrelation_le_of_monic_split_simple_root
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1)
    (P : (ZMod p)[X]) (hP : P.Splits) (hmonic : P.Monic)
    (a : ZMod p) (ha : P.rootMultiplicity a = 1) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      (P.roots.toFinset.card - 1 : ℕ) * Real.sqrt p := by
  have hcount : P.roots.count a = 1 := by rw [Polynomial.count_roots]; exact ha
  have h := primeRootMultisetExtensionWeilBounds_of_simple_root p χ hχ P.roots a hcount 0
  rw [← primeKummerExtensionCorrelation_eq_rootMultiset,
    ← eq_primeKummerRootMultisetPolynomial_roots P hP hmonic, primeKummerExtensionCorrelation_zero] at h
  simpa only [primeRootMultisetSpectralRank, zero_add, pow_one] using h

end
end Tao2026
