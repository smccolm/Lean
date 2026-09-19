import Tao2026.BurgessWeilPrimeKummerNewtonIntegrality
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# Literal Weil bounds for arbitrary higher-root Newton spectra

Uniform power-sum bounds control every member of a finite complex multiset.
The proof applies Newton identities to all powered multisets, uniformly bounds
their characteristic polynomials, and then uses Cauchy's root bound plus
exponential divergence.  This turns the remaining canonical-root weight
condition into the literal sharp Weil bounds for all extension correlations.
-/

namespace Tao2026

open Finset Complex Polynomial Filter
open scoped BigOperators Topology

noncomputable section

def complexNewtonNormBound (M : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 =>
      (k + 1 : ℝ)⁻¹ *
        ∑ a ∈ ({a ∈ Finset.antidiagonal (k + 1) | a.1 < k + 1}).attach,
          complexNewtonNormBound M (a : ℕ × ℕ).1 * M
termination_by k => k
decreasing_by
  have ha := a.property
  simp only [Finset.mem_filter] at ha
  omega

theorem complexNewtonNormBound_succ (M : ℝ) (k : ℕ) :
    complexNewtonNormBound M (k + 1) =
      (k + 1 : ℝ)⁻¹ *
        ∑ a ∈ Finset.antidiagonal (k + 1) with a.1 < k + 1,
          complexNewtonNormBound M a.1 * M := by
  rw [complexNewtonNormBound]
  congr 1
  let S := {a ∈ Finset.antidiagonal (k + 1) | a.1 < k + 1}
  simpa [S] using
    (Finset.sum_attach S (fun a : ℕ × ℕ => complexNewtonNormBound M a.1 * M))

theorem complexNewtonNormBound_nonneg (M : ℝ) (hM : 0 ≤ M) :
    ∀ k : ℕ, 0 ≤ complexNewtonNormBound M k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero => rw [complexNewtonNormBound]; norm_num
      | succ k =>
          rw [complexNewtonNormBound_succ]
          apply mul_nonneg (inv_nonneg.mpr (by positivity))
          apply Finset.sum_nonneg
          intro a ha
          have ha' := ha
          simp only [Finset.mem_filter] at ha'
          exact mul_nonneg (ih a.1 (by omega)) hM

theorem norm_complexNewtonElementary_le
    (u : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ j : ℕ, 0 < j → ‖u j‖ ≤ M) :
    ∀ k : ℕ, ‖complexNewtonElementary u k‖ ≤ complexNewtonNormBound M k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero => rw [complexNewtonElementary, complexNewtonNormBound]; norm_num
      | succ k =>
          rw [complexNewtonElementary_succ, complexNewtonNormBound_succ]
          have hnorm : ‖(k : ℂ) + 1‖⁻¹ = ((k : ℝ) + 1)⁻¹ := by
            rw [← Nat.cast_one, ← Nat.cast_add, norm_natCast]
            norm_num
          rw [norm_mul, norm_inv, hnorm, norm_mul, norm_pow, norm_neg, norm_one,
            one_pow, one_mul]
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
          calc
            ‖∑ a ∈ Finset.antidiagonal (k + 1) with a.1 < k + 1,
                (-1 : ℂ) ^ a.1 * complexNewtonElementary u a.1 * u a.2‖
                ≤ ∑ a ∈ Finset.antidiagonal (k + 1) with a.1 < k + 1,
                    ‖(-1 : ℂ) ^ a.1 * complexNewtonElementary u a.1 * u a.2‖ :=
              norm_sum_le _ _
            _ ≤ ∑ a ∈ Finset.antidiagonal (k + 1) with a.1 < k + 1,
                    complexNewtonNormBound M a.1 * M := by
              apply Finset.sum_le_sum
              intro a ha
              have ha' := ha
              simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha'
              rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
              exact mul_le_mul (ih a.1 ha'.2) (hu a.2 (by omega))
                (norm_nonneg _) (complexNewtonNormBound_nonneg M hM a.1)

def complexNewtonCauchyBound (M : ℝ) (n : ℕ) : NNReal :=
  (∑ j ∈ Finset.range (n + 1),
    Real.toNNReal (complexNewtonNormBound M j)) + 1

theorem cauchyBound_multiset_prod_le_complexNewtonCauchyBound
    (A : Multiset ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ k : ℕ, 0 < k → ‖(A.map fun z => z ^ k).sum‖ ≤ M) :
    Polynomial.cauchyBound ((A.map fun z => Polynomial.X - Polynomial.C z).prod) ≤
      complexNewtonCauchyBound M A.card := by
  let Q : Polynomial ℂ := (A.map fun z => Polynomial.X - Polynomial.C z).prod
  have hmonic : Q.Monic := Polynomial.monic_multisetProd_X_sub_C A
  have hcoeff (i : ℕ) (hi : i < A.card) :
      ‖Q.coeff i‖ ≤ complexNewtonNormBound M (A.card - i) := by
    have he := norm_complexNewtonElementary_le
      (fun k => (A.map fun z => z ^ k).sum) M hM hp (A.card - i)
    rw [complexNewtonElementary_powerSum_eq_esymm] at he
    change ‖(A.map fun z => Polynomial.X - Polynomial.C z).prod.coeff i‖ ≤ _
    rw [A.prod_X_sub_C_coeff (Nat.le_of_lt hi)]
    simpa [norm_mul, norm_pow] using he
  unfold Polynomial.cauchyBound complexNewtonCauchyBound
  rw [hmonic.leadingCoeff]
  simp only [nnnorm_one, div_one]
  rw [add_le_add_iff_right]
  change (Finset.range Q.natDegree).sup (fun i => ‖Q.coeff i‖₊) ≤ _
  rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
  apply Finset.sup_le
  intro i hi
  have hi' : i < A.card := Finset.mem_range.mp hi
  have hbnonneg : 0 ≤ complexNewtonNormBound M (A.card - i) :=
    complexNewtonNormBound_nonneg M hM _
  have hc : ‖Q.coeff i‖₊ ≤
      Real.toNNReal (complexNewtonNormBound M (A.card - i)) := by
    apply NNReal.coe_le_coe.mp
    simpa [Real.coe_toNNReal _ hbnonneg] using hcoeff i hi'
  refine hc.trans ?_
  refine Finset.single_le_sum
    (s := Finset.range (A.card + 1))
    (f := fun j => Real.toNNReal (complexNewtonNormBound M j))
    (fun j hj => bot_le) ?_
  simp

theorem complexMultiset_norm_le_one_of_powerSum_norm_le_card
    (A : Multiset ℂ)
    (hp : ∀ k : ℕ, 0 < k →
      ‖(A.map fun z => z ^ k).sum‖ ≤ A.card) :
    ∀ a ∈ A, ‖a‖ ≤ 1 := by
  intro a ha
  by_contra hnot
  have ha1 : 1 < ‖a‖ := lt_of_not_ge hnot
  let K : NNReal := complexNewtonCauchyBound (A.card : ℝ) A.card
  have hpowBound : ∀ n : ℕ, 0 < n → ‖a‖ ^ n < (K : ℝ) := by
    intro n hn
    let B : Multiset ℂ := A.map fun z => z ^ n
    let Q : Polynomial ℂ := (B.map fun z => Polynomial.X - Polynomial.C z).prod
    have hBcard : B.card = A.card := by simp [B]
    have hBpow : ∀ k : ℕ, 0 < k →
        ‖(B.map fun z => z ^ k).sum‖ ≤ (A.card : ℝ) := by
      intro k hk
      change ‖((A.map fun z => z ^ n).map fun z => z ^ k).sum‖ ≤ _
      rw [Multiset.map_map]
      simpa [pow_mul] using hp (n * k) (Nat.mul_pos hn hk)
    have hc : Polynomial.cauchyBound Q ≤ K := by
      change Polynomial.cauchyBound
          ((B.map fun z => Polynomial.X - Polynomial.C z).prod) ≤ _
      have h := cauchyBound_multiset_prod_le_complexNewtonCauchyBound
        B (A.card : ℝ) (by positivity) hBpow
      simpa [K, hBcard] using h
    have hmem : a ^ n ∈ B := by
      exact Multiset.mem_map.mpr ⟨a, ha, rfl⟩
    have hroot : Q.IsRoot (a ^ n) := by
      apply (Polynomial.mem_roots
        (Polynomial.monic_multisetProd_X_sub_C B).ne_zero).mp
      change a ^ n ∈ (B.map fun z => Polynomial.X - Polynomial.C z).prod.roots
      rw [Polynomial.roots_multiset_prod_X_sub_C]
      exact hmem
    have hlt := hroot.norm_lt_cauchyBound
      (Polynomial.monic_multisetProd_X_sub_C B).ne_zero
    have hlt' : ‖a ^ n‖₊ < K := hlt.trans_le hc
    have hr : ‖a ^ n‖ < (K : ℝ) := by exact_mod_cast hlt'
    simpa [norm_pow] using hr
  have ht : Tendsto (fun n : ℕ => ‖a‖ ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt ha1
  have hev : ∀ᶠ n : ℕ in atTop, (K : ℝ) ≤ ‖a‖ ^ n :=
    (Filter.tendsto_atTop.1 ht (K : ℝ))
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  obtain ⟨n, hnK, hnpos⟩ := (hev.and hpos).exists
  exact (not_lt_of_ge hnK) (hpowBound n hnpos)

theorem complexMultiset_norm_le_iff_powerSum_bound
    (A : Multiset ℂ) (R : ℝ) (hR : 0 ≤ R) :
    (∀ a ∈ A, ‖a‖ ≤ R) ↔
      ∀ n : ℕ, 0 < n →
        ‖(A.map fun a => a ^ n).sum‖ ≤ A.card * R ^ n := by
  constructor
  · intro h n hn
    induction A using Multiset.induction_on with
    | empty => simp
    | @cons a A ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
        calc
          ‖a ^ n + (A.map fun a => a ^ n).sum‖ ≤
              ‖a ^ n‖ + ‖(A.map fun a => a ^ n).sum‖ := norm_add_le _ _
          _ ≤ R ^ n + A.card * R ^ n := by
            apply add_le_add
            · rw [norm_pow]
              exact pow_le_pow_left₀ (norm_nonneg _) (h a (by simp)) n
            · exact ih (fun b hb => h b (by simp [hb]))
          _ = (↑(A.card + 1) : ℝ) * R ^ n := by push_cast; ring
  · intro h
    by_cases hR0 : R = 0
    · subst R
      have hpzero : ∀ n : ℕ, 0 < n → (A.map fun a => a ^ n).sum = 0 := by
        intro n hn
        have hb := h n hn
        simp [hn.ne'] at hb
        exact hb
      let Z : Multiset ℂ := Multiset.replicate A.card 0
      have hAZ : A = Z := by
        apply complexMultiset_eq_of_card_eq_of_powerSums_eq
        · simp [Z]
        · intro n hn
          rw [hpzero n hn]
          simp [Z, hn.ne']
      intro a ha
      rw [hAZ] at ha
      have ha0 : a = 0 := Multiset.eq_of_mem_replicate ha
      simp [ha0]
    · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
      let B : Multiset ℂ := A.map fun a => a / (R : ℂ)
      have hB : ∀ n : ℕ, 0 < n →
          ‖(B.map fun a => a ^ n).sum‖ ≤ B.card := by
        intro n hn
        have hnR : 0 < R ^ n := pow_pos hRpos n
        have hb := h n hn
        change ‖((A.map fun a => a / (R : ℂ)).map fun a => a ^ n).sum‖ ≤ _
        rw [Multiset.map_map]
        simp only [Function.comp_apply, div_pow]
        rw [Multiset.sum_map_div, norm_div]
        rw [show ‖((R : ℂ) ^ n)‖ = R ^ n by
          simp [norm_pow, abs_of_pos hRpos]]
        rw [Multiset.card_map]
        exact (div_le_iff₀ hnR).2 (by simpa [Nat.cast_mul] using hb)
      have hunit := complexMultiset_norm_le_one_of_powerSum_norm_le_card B hB
      intro a ha
      have hab : a / (R : ℂ) ∈ B := Multiset.mem_map.mpr ⟨a, ha, rfl⟩
      have hb := hunit (a / (R : ℂ)) hab
      rw [norm_div, show ‖(R : ℂ)‖ = R by simp [abs_of_pos hRpos]] at hb
      exact (div_le_one hRpos).mp hb

theorem primeRootMultisetNewtonPowerSum_eq_canonical_of_recurrence
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (hrec : PolynomialPowerSumRecurrence
      (primeRootMultisetNewtonPolynomial p χ R)
      (primeRootMultisetSpectralRank R)
      (primeRootMultisetNewtonPowerSum p χ R)) :
    ∀ d : ℕ, primeRootMultisetNewtonPowerSum p χ R d =
      ((primeRootMultisetCanonicalEigenvalues p χ R).map
        fun a => a ^ d).sum := by
  have hrootrec : PolynomialPowerSumRecurrence
      (primeRootMultisetNewtonPolynomial p χ R)
      (primeRootMultisetSpectralRank R)
      (fun d => ((primeRootMultisetCanonicalEigenvalues p χ R).map
        fun a => a ^ d).sum) := by
    intro d
    exact canonicalEigenvalues_powerSum_recurrence p χ R d
  have hseq := polynomialPowerSumRecurrence_unique
    (primeRootMultisetNewtonPolynomial p χ R)
    (primeRootMultisetSpectralRank R)
    (primeRootMultisetNewtonPowerSum p χ R)
    (fun d => ((primeRootMultisetCanonicalEigenvalues p χ R).map
      fun a => a ^ d).sum)
    (primeRootMultisetNewtonPolynomial_natDegree p χ R)
    (primeRootMultisetNewtonPolynomial_monic p χ R)
    hrec hrootrec
    (primeRootMultisetNewtonPowerSum_eq_canonical_of_lt_rank p χ R)
  exact congrFun hseq

def PrimeRootMultisetExtensionWeilBounds
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : Prop :=
  ∀ q : ℕ,
    ‖primeRootMultisetExtensionCorrelation p χ R q‖ ≤
      primeRootMultisetSpectralRank R * Real.sqrt p ^ (q + 1)

theorem primeRootMultisetCanonicalWeight_iff_extensionWeilBounds_of_recurrence
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (hrec : PolynomialPowerSumRecurrence
      (primeRootMultisetNewtonPolynomial p χ R)
      (primeRootMultisetSpectralRank R)
      (primeRootMultisetNewtonPowerSum p χ R)) :
    (∀ a ∈ primeRootMultisetCanonicalEigenvalues p χ R,
        ‖a‖ ≤ Real.sqrt p) ↔
      PrimeRootMultisetExtensionWeilBounds p χ R := by
  let A := primeRootMultisetCanonicalEigenvalues p χ R
  have hcard : A.card = primeRootMultisetSpectralRank R :=
    card_primeRootMultisetCanonicalEigenvalues p χ R
  have hseq := primeRootMultisetNewtonPowerSum_eq_canonical_of_recurrence
    p χ R hrec
  rw [complexMultiset_norm_le_iff_powerSum_bound A (Real.sqrt p)
    (Real.sqrt_nonneg p)]
  constructor
  · intro hpower q
    have hs := hseq (q + 1)
    rw [primeRootMultisetNewtonPowerSum] at hs
    have hp := hpower (q + 1) (by omega)
    change ‖((primeRootMultisetCanonicalEigenvalues p χ R).map
      fun a => a ^ (q + 1)).sum‖ ≤ _ at hp
    rw [← hs, norm_neg] at hp
    simpa [hcard] using hp
  · intro hweil d hd
    have hs := hseq d
    have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
    have hw := hweil (d - 1)
    rw [← hs]
    rw [show d = (d - 1) + 1 by omega, primeRootMultisetNewtonPowerSum,
      norm_neg, hdsub]
    rw [hdsub] at hw
    simpa [hcard] using hw

def PrimeRootMultisetNewtonLiteralConditions
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : Prop :=
  PrimeRootMultisetNewtonCoefficientIntegrality p χ R ∧
  PrimeRootMultisetExtensionWeilBounds p χ R ∧
  PolynomialPowerSumRecurrence
    (primeRootMultisetNewtonPolynomial p χ R)
    (primeRootMultisetSpectralRank R)
    (primeRootMultisetNewtonPowerSum p χ R)

theorem primeRootMultisetNewtonCoefficientCharacteristicConditions_iff_literalConditions
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)} :
    PrimeRootMultisetNewtonCoefficientCharacteristicConditions p χ R ↔
      PrimeRootMultisetNewtonLiteralConditions p χ R := by
  constructor
  · rintro ⟨hintegral, hweight, hrec⟩
    exact ⟨hintegral,
      (primeRootMultisetCanonicalWeight_iff_extensionWeilBounds_of_recurrence
        p χ R hrec).mp hweight, hrec⟩
  · rintro ⟨hintegral, hweil, hrec⟩
    exact ⟨hintegral,
      (primeRootMultisetCanonicalWeight_iff_extensionWeilBounds_of_recurrence
        p χ R hrec).mpr hweil, hrec⟩

def TaoPrimeKummerNewtonLiteralConditionsFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)),
    χ ≠ 1 → 0 ∈ R → 1 ∈ R → 4 ≤ R.toFinset.card →
      (∀ r ∈ R.toFinset, R.count r < orderOf χ) →
        PrimeRootMultisetNewtonLiteralConditions p χ R

theorem taoPrimeKummerNewtonCoefficientCharacteristicConditionsFourRootsOrMore_iff_literalConditions :
    TaoPrimeKummerNewtonCoefficientCharacteristicConditionsFourRootsOrMore ↔
      TaoPrimeKummerNewtonLiteralConditionsFourRootsOrMore := by
  constructor
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact primeRootMultisetNewtonCoefficientCharacteristicConditions_iff_literalConditions.mp
      (h p χ R hχ hzero hone hcard hreduced)
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact primeRootMultisetNewtonCoefficientCharacteristicConditions_iff_literalConditions.mpr
      (h p χ R hχ hzero hone hcard hreduced)

end
end Tao2026
