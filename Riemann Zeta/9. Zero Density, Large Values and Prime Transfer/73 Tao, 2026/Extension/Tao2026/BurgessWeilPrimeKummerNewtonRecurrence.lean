import Tao2026.BurgessWeilPrimeKummerNewtonPolynomial

/-!
# Finite recurrence form of the higher-root trace conditions

The power sums of the canonical roots satisfy the characteristic recurrence
of the Newton polynomial.  Since that polynomial is monic, any other sequence
satisfying the same recurrence is determined by its first `degree` values.
Consequently, the all-extension trace identities are equivalent to finitely
many initial identities together with one recurrence valid in every degree.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators

noncomputable section

theorem finset_sum_multiset_sum_swap
    {ι α R : Type*} [CommSemiring R]
    (s : Finset ι) (A : Multiset α) (f : ι → α → R) :
    (∑ i ∈ s, (A.map fun a => f i a).sum) =
      (A.map fun a => ∑ i ∈ s, f i a).sum := by
  induction A using Multiset.induction_on with
  | empty => simp
  | @cons a A ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [← ih]
      simp [Finset.sum_add_distrib]

theorem polynomial_root_powerSum_recurrence
    (P : Polynomial ℂ) (A : Multiset ℂ) (n : ℕ)
    (hdeg : P.natDegree = n)
    (hroot : ∀ a ∈ A, P.eval a = 0) (d : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      P.coeff k * (A.map fun a => a ^ (d + k)).sum) = 0 := by
  calc
    _ = (A.map fun a => ∑ k ∈ Finset.range (n + 1),
        P.coeff k * a ^ (d + k)).sum := by
      simpa [Multiset.sum_map_mul_left] using
        (finset_sum_multiset_sum_swap (Finset.range (n + 1)) A
          (fun k a => P.coeff k * a ^ (d + k)))
    _ = (A.map fun a => a ^ d * P.eval a).sum := by
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro a ha
      rw [P.eval_eq_sum_range, hdeg]
      simp_rw [pow_add]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (A.map fun _ => (0 : ℂ)).sum := by
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro a ha
      rw [hroot a ha, mul_zero]
    _ = 0 := by simp

theorem canonicalEigenvalues_powerSum_recurrence
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (d : ℕ) :
    (∑ k ∈ Finset.range (primeRootMultisetSpectralRank R + 1),
      (primeRootMultisetNewtonPolynomial p χ R).coeff k *
        ((primeRootMultisetCanonicalEigenvalues p χ R).map
          fun a => a ^ (d + k)).sum) = 0 := by
  apply polynomial_root_powerSum_recurrence
    (primeRootMultisetNewtonPolynomial p χ R)
    (primeRootMultisetCanonicalEigenvalues p χ R)
    (primeRootMultisetSpectralRank R)
    (primeRootMultisetNewtonPolynomial_natDegree p χ R)
  intro a ha
  exact (Polynomial.mem_roots
    (primeRootMultisetNewtonPolynomial_monic p χ R).ne_zero).mp ha

/-- A sequence obeys the characteristic recurrence of `P` through degree
`n`. -/
def PolynomialPowerSumRecurrence
    (P : Polynomial ℂ) (n : ℕ) (u : ℕ → ℂ) : Prop :=
  ∀ d : ℕ, ∑ k ∈ Finset.range (n + 1), P.coeff k * u (d + k) = 0

/-- A monic characteristic recurrence and the first `n` values uniquely
determine a sequence. -/
theorem polynomialPowerSumRecurrence_unique
    (P : Polynomial ℂ) (n : ℕ) (u v : ℕ → ℂ)
    (hdeg : P.natDegree = n) (hmonic : P.Monic)
    (hu : PolynomialPowerSumRecurrence P n u)
    (hv : PolynomialPowerSumRecurrence P n v)
    (hinit : ∀ d < n, u d = v d) :
    u = v := by
  funext m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm : m < n
      · exact hinit m hm
      · have hnm : n ≤ m := Nat.le_of_not_gt hm
        let d := m - n
        have hdm : d + n = m := Nat.sub_add_cancel hnm
        have hlead : P.coeff n = 1 := by
          rw [← hdeg]
          exact hmonic.coeff_natDegree
        have hup := hu d
        have hvp := hv d
        rw [Finset.sum_range_succ, hlead, one_mul, hdm] at hup hvp
        have hprefix :
            (∑ k ∈ Finset.range n, P.coeff k * u (d + k)) =
              ∑ k ∈ Finset.range n, P.coeff k * v (d + k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih (d + k)]
          have hk' : k < n := Finset.mem_range.mp hk
          omega
        rw [hprefix] at hup
        linear_combination hup - hvp

theorem primeRootMultisetNewtonPolynomial_coeff
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (j : ℕ) (hj : j ≤ primeRootMultisetSpectralRank R) :
    (primeRootMultisetNewtonPolynomial p χ R).coeff
        (primeRootMultisetSpectralRank R - j) =
      (-1 : ℂ) ^ j * primeRootMultisetNewtonElementary p χ R j := by
  unfold primeRootMultisetNewtonPolynomial
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · rw [← mul_assoc]
    have hC : (-1 : Polynomial ℂ) ^ j *
        Polynomial.C (primeRootMultisetNewtonElementary p χ R j) =
          Polynomial.C ((-1 : ℂ) ^ j *
            primeRootMultisetNewtonElementary p χ R j) := by simp
    rw [hC, Polynomial.coeff_C_mul_X_pow]
    simp
  · intro b hb hbj
    have hble : b ≤ primeRootMultisetSpectralRank R := by
      simpa [Nat.lt_succ_iff] using hb
    have hne : primeRootMultisetSpectralRank R - j ≠
        primeRootMultisetSpectralRank R - b := by omega
    rw [← mul_assoc]
    have hC : (-1 : Polynomial ℂ) ^ b *
        Polynomial.C (primeRootMultisetNewtonElementary p χ R b) =
          Polynomial.C ((-1 : ℂ) ^ b *
            primeRootMultisetNewtonElementary p χ R b) := by simp
    rw [hC, Polynomial.coeff_C_mul_X_pow]
    simp [hne]
  · simp [hj]

theorem esymm_primeRootMultisetCanonicalEigenvalues_eq_newtonElementary
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (j : ℕ) (hj : j ≤ primeRootMultisetSpectralRank R) :
    (primeRootMultisetCanonicalEigenvalues p χ R).esymm j =
      primeRootMultisetNewtonElementary p χ R j := by
  let P := primeRootMultisetNewtonPolynomial p χ R
  have hv := Polynomial.coeff_eq_esymm_roots_of_splits
    (IsAlgClosed.splits P) (k := primeRootMultisetSpectralRank R - j)
    (by rw [primeRootMultisetNewtonPolynomial_natDegree]; exact Nat.sub_le _ _)
  have hcoeff := primeRootMultisetNewtonPolynomial_coeff p χ R j hj
  change P.coeff (primeRootMultisetSpectralRank R - j) = _ at hcoeff
  have hsub : primeRootMultisetSpectralRank R -
      (primeRootMultisetSpectralRank R - j) = j := by omega
  rw [primeRootMultisetNewtonPolynomial_natDegree,
    (primeRootMultisetNewtonPolynomial_monic p χ R).leadingCoeff,
    hsub] at hv
  change P.roots.esymm j = _
  rw [hv] at hcoeff
  have hneg : (-1 : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hneg
  simpa using hcoeff

theorem complexNewtonElementary_newtonIdentity
    (u : ℕ → ℂ) (k : ℕ) :
    (k : ℂ) * complexNewtonElementary u k =
      (-1 : ℂ) ^ (k + 1) *
        ∑ a ∈ Finset.antidiagonal k with a.1 < k,
          (-1 : ℂ) ^ a.1 * complexNewtonElementary u a.1 * u a.2 := by
  cases k with
  | zero => simp [complexNewtonElementary]
  | succ k =>
      rw [complexNewtonElementary_succ]
      have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      field_simp
      norm_num

/-- The first `n` elementary coefficients determine the first `n` positive
power sums.  This is the inverse direction of Newton's identities for an
arbitrary sequence. -/
theorem complexNewtonPowerSum_eq_of_elementary_eq
    (u v : ℕ → ℂ) (n : ℕ)
    (he : ∀ j ≤ n,
      complexNewtonElementary u j = complexNewtonElementary v j) :
    ∀ k ≤ n, 0 < k → u k = v k := by
  intro k hkn hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
      let S := {a ∈ Finset.antidiagonal k | a.1 < k}
      have hzero : (0, k) ∈ S := by simp [S, hk]
      have hrest :
          (∑ a ∈ S.erase (0, k),
            (-1 : ℂ) ^ a.1 * complexNewtonElementary u a.1 * u a.2) =
          ∑ a ∈ S.erase (0, k),
            (-1 : ℂ) ^ a.1 * complexNewtonElementary v a.1 * v a.2 := by
        apply Finset.sum_congr rfl
        intro a ha
        have haS := (Finset.mem_erase.mp ha).2
        have hane := (Finset.mem_erase.mp ha).1
        have ha' := haS
        simp only [S, Finset.mem_filter, Finset.mem_antidiagonal] at ha'
        have ha1pos : 0 < a.1 := by
          by_contra hnot
          have ha1 : a.1 = 0 := Nat.eq_zero_of_not_pos hnot
          have ha2 : a.2 = k := by omega
          apply hane
          exact Prod.ext ha1 ha2
        have ha2pos : 0 < a.2 := by omega
        have ha2lt : a.2 < k := by omega
        rw [he a.1 (by omega), ih a.2 ha2lt (by omega) ha2pos]
      have hu := complexNewtonElementary_newtonIdentity u k
      have hv := complexNewtonElementary_newtonIdentity v k
      change (k : ℂ) * complexNewtonElementary u k =
        (-1 : ℂ) ^ (k + 1) * ∑ a ∈ S,
          (-1 : ℂ) ^ a.1 * complexNewtonElementary u a.1 * u a.2 at hu
      change (k : ℂ) * complexNewtonElementary v k =
        (-1 : ℂ) ^ (k + 1) * ∑ a ∈ S,
          (-1 : ℂ) ^ a.1 * complexNewtonElementary v a.1 * v a.2 at hv
      rw [← Finset.sum_erase_add _ _ hzero] at hu hv
      simp [complexNewtonElementary] at hu hv
      rw [he k hkn, hrest] at hu
      have hsign : (-1 : ℂ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hscaled := hu.symm.trans hv
      have hsums := mul_left_cancel₀ hsign hscaled
      exact add_left_cancel hsums

/-- The initial power-sum identities are automatic from the Newton
construction of the polynomial. -/
theorem primeRootMultisetNewtonPowerSum_eq_canonical_of_lt_rank
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (d : ℕ) (hd : d < primeRootMultisetSpectralRank R) :
    primeRootMultisetNewtonPowerSum p χ R d =
      ((primeRootMultisetCanonicalEigenvalues p χ R).map
        fun a => a ^ d).sum := by
  cases d with
  | zero =>
      simp [primeRootMultisetNewtonPowerSum,
        card_primeRootMultisetCanonicalEigenvalues]
  | succ d =>
      apply complexNewtonPowerSum_eq_of_elementary_eq
        (primeRootMultisetNewtonPowerSum p χ R)
        (fun k => ((primeRootMultisetCanonicalEigenvalues p χ R).map
          fun a => a ^ k).sum)
        (primeRootMultisetSpectralRank R)
      · intro j hj
        calc
          complexNewtonElementary (primeRootMultisetNewtonPowerSum p χ R) j =
              primeRootMultisetNewtonElementary p χ R j := rfl
          _ = (primeRootMultisetCanonicalEigenvalues p χ R).esymm j :=
            (esymm_primeRootMultisetCanonicalEigenvalues_eq_newtonElementary
              p χ R j hj).symm
          _ = complexNewtonElementary
              (fun k => ((primeRootMultisetCanonicalEigenvalues p χ R).map
                fun a => a ^ k).sum) j :=
            (complexNewtonElementary_powerSum_eq_esymm
              (primeRootMultisetCanonicalEigenvalues p χ R) j).symm
      · omega
      · omega

/-- The finite-recurrence replacement for all higher-root extension-trace
identities. -/
def PrimeRootMultisetNewtonRecurrenceConditions
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : Prop :=
  (∀ a ∈ primeRootMultisetCanonicalEigenvalues p χ R,
      IsIntegral ℤ a) ∧
  (∀ a ∈ primeRootMultisetCanonicalEigenvalues p χ R,
      ‖a‖ ≤ Real.sqrt p) ∧
  (∀ d < primeRootMultisetSpectralRank R,
    primeRootMultisetNewtonPowerSum p χ R d =
      ((primeRootMultisetCanonicalEigenvalues p χ R).map
        fun a => a ^ d).sum) ∧
  PolynomialPowerSumRecurrence
    (primeRootMultisetNewtonPolynomial p χ R)
    (primeRootMultisetSpectralRank R)
    (primeRootMultisetNewtonPowerSum p χ R)

theorem primeRootMultisetNewtonSpectrumConditions_iff_recurrenceConditions
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)} :
    PrimeRootMultisetNewtonSpectrumConditions p χ R ↔
      PrimeRootMultisetNewtonRecurrenceConditions p χ R := by
  constructor
  · rintro ⟨hintegral, hweight, htrace⟩
    have hseq : ∀ d : ℕ,
        primeRootMultisetNewtonPowerSum p χ R d =
          ((primeRootMultisetCanonicalEigenvalues p χ R).map
            fun a => a ^ d).sum := by
      intro d
      cases d with
      | zero =>
          simp [primeRootMultisetNewtonPowerSum,
            card_primeRootMultisetCanonicalEigenvalues]
      | succ d =>
          rw [primeRootMultisetNewtonPowerSum, htrace]
          simp
    refine ⟨hintegral, hweight, ?_, ?_⟩
    · intro d hd
      exact hseq d
    · intro d
      simpa only [hseq] using
        (canonicalEigenvalues_powerSum_recurrence p χ R d)
  · rintro ⟨hintegral, hweight, hinit, hrec⟩
    have hrootrec : PolynomialPowerSumRecurrence
        (primeRootMultisetNewtonPolynomial p χ R)
        (primeRootMultisetSpectralRank R)
        (fun d => ((primeRootMultisetCanonicalEigenvalues p χ R).map
          fun a => a ^ d).sum) := by
      intro d
      exact canonicalEigenvalues_powerSum_recurrence p χ R d
    have hseq : primeRootMultisetNewtonPowerSum p χ R =
        (fun d => ((primeRootMultisetCanonicalEigenvalues p χ R).map
          fun a => a ^ d).sum) :=
      polynomialPowerSumRecurrence_unique
        (primeRootMultisetNewtonPolynomial p χ R)
        (primeRootMultisetSpectralRank R)
        (primeRootMultisetNewtonPowerSum p χ R)
        (fun d => ((primeRootMultisetCanonicalEigenvalues p χ R).map
          fun a => a ^ d).sum)
        (primeRootMultisetNewtonPolynomial_natDegree p χ R)
        (primeRootMultisetNewtonPolynomial_monic p χ R)
        hrec hrootrec hinit
    refine ⟨hintegral, hweight, ?_⟩
    intro q
    have hs := congrFun hseq (q + 1)
    rw [primeRootMultisetNewtonPowerSum] at hs
    linear_combination -hs

def TaoPrimeKummerNewtonRecurrenceConditionsFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)),
    χ ≠ 1 → 0 ∈ R → 1 ∈ R → 4 ≤ R.toFinset.card →
      (∀ r ∈ R.toFinset, R.count r < orderOf χ) →
        PrimeRootMultisetNewtonRecurrenceConditions p χ R

theorem taoPrimeKummerNewtonSpectrumConditionsFourRootsOrMore_iff_recurrenceConditions :
    TaoPrimeKummerNewtonSpectrumConditionsFourRootsOrMore ↔
      TaoPrimeKummerNewtonRecurrenceConditionsFourRootsOrMore := by
  constructor
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact primeRootMultisetNewtonSpectrumConditions_iff_recurrenceConditions.mp
      (h p χ R hχ hzero hone hcard hreduced)
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact primeRootMultisetNewtonSpectrumConditions_iff_recurrenceConditions.mpr
      (h p χ R hχ hzero hone hcard hreduced)

/-- After the automatic initial Newton identities are discharged, the
higher-root source consists only of fixed-root integrality and weight plus
the characteristic recurrence for the literal sequence. -/
def PrimeRootMultisetNewtonCharacteristicConditions
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : Prop :=
  (∀ a ∈ primeRootMultisetCanonicalEigenvalues p χ R,
      IsIntegral ℤ a) ∧
  (∀ a ∈ primeRootMultisetCanonicalEigenvalues p χ R,
      ‖a‖ ≤ Real.sqrt p) ∧
  PolynomialPowerSumRecurrence
    (primeRootMultisetNewtonPolynomial p χ R)
    (primeRootMultisetSpectralRank R)
    (primeRootMultisetNewtonPowerSum p χ R)

theorem primeRootMultisetNewtonRecurrenceConditions_iff_characteristicConditions
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)} :
    PrimeRootMultisetNewtonRecurrenceConditions p χ R ↔
      PrimeRootMultisetNewtonCharacteristicConditions p χ R := by
  constructor
  · rintro ⟨hintegral, hweight, _hinit, hrec⟩
    exact ⟨hintegral, hweight, hrec⟩
  · rintro ⟨hintegral, hweight, hrec⟩
    exact ⟨hintegral, hweight,
      primeRootMultisetNewtonPowerSum_eq_canonical_of_lt_rank p χ R, hrec⟩

theorem primeRootMultisetNewtonSpectrumConditions_iff_characteristicConditions
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)} :
    PrimeRootMultisetNewtonSpectrumConditions p χ R ↔
      PrimeRootMultisetNewtonCharacteristicConditions p χ R := by
  rw [primeRootMultisetNewtonSpectrumConditions_iff_recurrenceConditions,
    primeRootMultisetNewtonRecurrenceConditions_iff_characteristicConditions]

def TaoPrimeKummerNewtonCharacteristicConditionsFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)),
    χ ≠ 1 → 0 ∈ R → 1 ∈ R → 4 ≤ R.toFinset.card →
      (∀ r ∈ R.toFinset, R.count r < orderOf χ) →
        PrimeRootMultisetNewtonCharacteristicConditions p χ R

theorem taoPrimeKummerNewtonSpectrumConditionsFourRootsOrMore_iff_characteristicConditions :
    TaoPrimeKummerNewtonSpectrumConditionsFourRootsOrMore ↔
      TaoPrimeKummerNewtonCharacteristicConditionsFourRootsOrMore := by
  constructor
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact primeRootMultisetNewtonSpectrumConditions_iff_characteristicConditions.mp
      (h p χ R hχ hzero hone hcard hreduced)
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact primeRootMultisetNewtonSpectrumConditions_iff_characteristicConditions.mpr
      (h p χ R hχ hzero hone hcard hreduced)

end
end Tao2026
