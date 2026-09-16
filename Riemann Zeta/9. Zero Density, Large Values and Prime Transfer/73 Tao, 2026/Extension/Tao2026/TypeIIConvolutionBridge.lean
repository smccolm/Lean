import Tao2026.ConvolutionRearrangement
import Tao2026.TypeIIReduction

open Complex Finset
open scoped BigOperators

namespace Tao2026

noncomputable section

def typeIIProductRestrictedOuterSum
    (I K S : Finset ℕ) (β γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) : ℂ :=
  ∑ m ∈ K, β m * typeIIProductRestrictedInnerSum I S γ N M j m

theorem typeIIProductRestrictedOuterSum_eq_productSum
    (I K S : Finset ℕ) (β γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) :
    typeIIProductRestrictedOuterSum I K S β γ N M j =
      ∑ mn ∈ (K ×ˢ S).filter (fun mn => mn.1 * mn.2 ∈ I),
        β mn.1 * γ mn.2 *
          standardAdditiveCharacter (reciprocalPhase N M j (mn.1 * mn.2)) := by
  classical
  unfold typeIIProductRestrictedOuterSum typeIIProductRestrictedInnerSum
    typeIIInnerSum
  simp_rw [Finset.mul_sum]
  calc
    (∑ m ∈ K, ∑ n ∈ S,
        β m * ((if m * n ∈ I then γ n else 0) *
          standardAdditiveCharacter (reciprocalPhase N M j (m * n)))) =
        ∑ mn ∈ K ×ˢ S,
          β mn.1 * ((if mn.1 * mn.2 ∈ I then γ mn.2 else 0) *
            standardAdditiveCharacter
              (reciprocalPhase N M j (mn.1 * mn.2))) := by
      rw [Finset.sum_product]
    _ = ∑ mn ∈ (K ×ˢ S).filter (fun mn => mn.1 * mn.2 ∈ I),
          β mn.1 * γ mn.2 *
            standardAdditiveCharacter
              (reciprocalPhase N M j (mn.1 * mn.2)) := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro mn _hmn
      by_cases hprod : mn.1 * mn.2 ∈ I
      · simp [hprod, mul_assoc]
      · simp [hprod]

theorem norm_typeIIProductRestrictedOuterSum_sq_le
    (I K S : Finset ℕ) (β γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {L : ℝ}
    (hβ : ∀ m ∈ K, ‖β m‖ ≤ L) :
    ‖typeIIProductRestrictedOuterSum I K S β γ N M j‖ ^ 2 ≤
      (K.card : ℝ) * L ^ 2 *
        ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 := by
  have hcs := norm_sum_sq_le_card_mul_sum_norm_sq K
    (fun m => β m * typeIIProductRestrictedInnerSum I S γ N M j m)
  rw [typeIIProductRestrictedOuterSum]
  refine hcs.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg K.card)
  calc
    (∑ m ∈ K, ‖β m * typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2) ≤
        ∑ m ∈ K, L ^ 2 *
          ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hβ m hm) 2) (sq_nonneg _)
    _ = L ^ 2 *
        ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 := by
      rw [Finset.mul_sum]

/-- The portion of one canonical Vaughan block lying in the literal bounded
product box. -/
def vaughanProductBlockSupport (B : ℕ) (sk : ℕ × ℕ) : Finset ℕ :=
  (Finset.Ioc 0 B).filter fun n =>
    n ∈ dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget B) sk

theorem weightedConvolutionProductVaughanDoubleBlockSum_eq_typeIIOuterSum
    (I : Finset ℕ) (B : ℕ) (sk tl : ℕ × ℕ)
    (f g : ArithmeticFunction ℝ) (N M : ℝ) (j : ℕ) :
    weightedConvolutionProductVaughanDoubleBlockSum I B sk tl
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n)) f g =
      typeIIProductRestrictedOuterSum I
        (vaughanProductBlockSupport B sk) (vaughanProductBlockSupport B tl)
        (vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk)
        (vaughanShortIntervalCoefficient (fun n => (g n : ℂ)) B tl)
        N M j := by
  classical
  rw [typeIIProductRestrictedOuterSum_eq_productSum]
  unfold weightedConvolutionProductVaughanDoubleBlockSum
  simp only [Nat.cast_mul]
  symm
  apply Finset.sum_subset
  · intro mn hmn
    simp only [Finset.mem_filter, Finset.mem_product] at hmn ⊢
    exact ⟨⟨(Finset.mem_filter.mp hmn.1.1).1,
      (Finset.mem_filter.mp hmn.1.2).1⟩, hmn.2⟩
  · intro mn hmnBox hmnSmall
    simp only [Finset.mem_filter, Finset.mem_product] at hmnBox
    by_cases hβ :
        vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk mn.1 = 0
    · simp [hβ]
    by_cases hγ :
        vaughanShortIntervalCoefficient (fun n => (g n : ℂ)) B tl mn.2 = 0
    · simp [hγ]
    exfalso
    apply hmnSmall
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, hmnBox.2⟩
    · exact Finset.mem_filter.mpr ⟨hmnBox.1.1,
        mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero
          (fun m => (f m : ℂ)) (Finset.mem_Ioc.mp hmnBox.1.1).1 hβ⟩
    · exact Finset.mem_filter.mpr ⟨hmnBox.1.2,
        mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero
          (fun n => (g n : ℂ)) (Finset.mem_Ioc.mp hmnBox.1.2).1 hγ⟩

/-- Once the product itself is bounded by `B`, intersecting the inner block
with `[1,B]` does not change a product-restricted inner sum. -/
theorem typeIIProductRestrictedInnerSum_vaughanProductBlockSupport_eq
    {I : Finset ℕ} {B : ℕ} {tl : ℕ × ℕ} (γ : ℕ → ℂ)
    (N M : ℝ) (j : ℕ) {m : ℕ} (hm : 0 < m)
    (hI : ∀ x ∈ I, x ≤ B) :
    typeIIProductRestrictedInnerSum I (vaughanProductBlockSupport B tl)
        γ N M j m =
      typeIIProductRestrictedInnerSum I
        (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget B) tl)
        γ N M j m := by
  classical
  unfold typeIIProductRestrictedInnerSum typeIIInnerSum
  apply Finset.sum_subset
  · intro n hn
    exact (Finset.mem_filter.mp hn).2
  · intro n hnBlock hnSupport
    have hnpos : 0 < n := by
      have hnRaw := hnBlock
      rw [dyadicShortIntervalIndexedBlock, mem_shortIntervalBlock] at hnRaw
      exact lt_of_lt_of_le (pow_pos (by omega) tl.1) hnRaw.1
    have hnLarge : B < n := by
      by_contra hnNot
      apply hnSupport
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hnpos, Nat.le_of_not_gt hnNot⟩, hnBlock⟩
    have hnotProduct : m * n ∉ I := by
      intro hprod
      have hprodB := hI (m * n) hprod
      have hmOne : 1 ≤ m := hm
      have hnProd : n ≤ m * n := by
        simpa [one_mul] using Nat.mul_le_mul_right n hmOne
      omega
    simp [hnotProduct]

/-- The bounded support used by the literal product box can therefore be
enlarged back to the complete canonical Vaughan blocks before applying the
analytic squared-inner-sum estimate. -/
theorem sum_typeIIProductRestrictedInnerSum_vaughanProductBlockSupport_le
    {I : Finset ℕ} {B : ℕ} (sk tl : ℕ × ℕ) (γ : ℕ → ℂ)
    (N M : ℝ) (j : ℕ) (hI : ∀ x ∈ I, x ≤ B) :
    ∑ m ∈ vaughanProductBlockSupport B sk,
        ‖typeIIProductRestrictedInnerSum I
          (vaughanProductBlockSupport B tl) γ N M j m‖ ^ 2 ≤
      ∑ m ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget B) sk,
        ‖typeIIProductRestrictedInnerSum I
          (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget B) tl)
          γ N M j m‖ ^ 2 := by
  calc
    ∑ m ∈ vaughanProductBlockSupport B sk,
        ‖typeIIProductRestrictedInnerSum I
          (vaughanProductBlockSupport B tl) γ N M j m‖ ^ 2 =
      ∑ m ∈ vaughanProductBlockSupport B sk,
        ‖typeIIProductRestrictedInnerSum I
          (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget B) tl)
          γ N M j m‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [typeIIProductRestrictedInnerSum_vaughanProductBlockSupport_eq
          γ N M j (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1 hI]
    _ ≤ ∑ m ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget B) sk,
        ‖typeIIProductRestrictedInnerSum I
          (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget B) tl)
          γ N M j m‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          exact (Finset.mem_filter.mp hm).2
        · intro m _hm _hnot
          positivity

/-- Exact Cauchy--Schwarz bridge from one literal Vaughan convolution block
to the complete-block squared inner sum estimated by the Weyl--Vinogradov
machinery. -/
theorem norm_weightedConvolutionProductVaughanDoubleBlockSum_sq_le
    (I : Finset ℕ) (B : ℕ) (sk tl : ℕ × ℕ)
    (f g : ArithmeticFunction ℝ) (N M : ℝ) (j : ℕ) {L : ℝ}
    (hβ : ∀ m ∈ vaughanProductBlockSupport B sk,
      ‖vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk m‖ ≤ L)
    (hI : ∀ x ∈ I, x ≤ B) :
    ‖weightedConvolutionProductVaughanDoubleBlockSum I B sk tl
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n)) f g‖ ^ 2 ≤
      ((dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget B) sk).card : ℝ) * L ^ 2 *
        ∑ m ∈ dyadicShortIntervalIndexedBlock
            (vaughanShortIntervalBudget B) sk,
          ‖typeIIProductRestrictedInnerSum I
            (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget B) tl)
            (vaughanShortIntervalCoefficient (fun n => (g n : ℂ)) B tl)
            N M j m‖ ^ 2 := by
  rw [weightedConvolutionProductVaughanDoubleBlockSum_eq_typeIIOuterSum]
  have hcs := norm_typeIIProductRestrictedOuterSum_sq_le I
    (vaughanProductBlockSupport B sk) (vaughanProductBlockSupport B tl)
    (vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk)
    (vaughanShortIntervalCoefficient (fun n => (g n : ℂ)) B tl)
    N M j hβ
  refine hcs.trans ?_
  have hcardNat : (vaughanProductBlockSupport B sk).card ≤
      (dyadicShortIntervalIndexedBlock
        (vaughanShortIntervalBudget B) sk).card :=
    Finset.card_le_card fun m hm => (Finset.mem_filter.mp hm).2
  have hcard : ((vaughanProductBlockSupport B sk).card : ℝ) ≤
      ((dyadicShortIntervalIndexedBlock
        (vaughanShortIntervalBudget B) sk).card : ℝ) := by
    exact_mod_cast hcardNat
  have hsum :=
    sum_typeIIProductRestrictedInnerSum_vaughanProductBlockSupport_le
      sk tl (vaughanShortIntervalCoefficient (fun n => (g n : ℂ)) B tl)
      N M j hI
  have hLsq : 0 ≤ L ^ 2 := sq_nonneg L
  have hleft : 0 ≤ ((vaughanProductBlockSupport B sk).card : ℝ) * L ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) hLsq
  calc
    ((vaughanProductBlockSupport B sk).card : ℝ) * L ^ 2 *
        ∑ m ∈ vaughanProductBlockSupport B sk,
          ‖typeIIProductRestrictedInnerSum I (vaughanProductBlockSupport B tl)
            (vaughanShortIntervalCoefficient (fun n => (g n : ℂ)) B tl)
            N M j m‖ ^ 2 ≤
      ((vaughanProductBlockSupport B sk).card : ℝ) * L ^ 2 *
        ∑ m ∈ dyadicShortIntervalIndexedBlock
            (vaughanShortIntervalBudget B) sk,
          ‖typeIIProductRestrictedInnerSum I
            (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget B) tl)
            (vaughanShortIntervalCoefficient (fun n => (g n : ℂ)) B tl)
            N M j m‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsum hleft
    _ ≤ ((dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget B) sk).card : ℝ) * L ^ 2 *
        ∑ m ∈ dyadicShortIntervalIndexedBlock
            (vaughanShortIntervalBudget B) sk,
          ‖typeIIProductRestrictedInnerSum I
            (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget B) tl)
            (vaughanShortIntervalCoefficient (fun n => (g n : ℂ)) B tl)
            N M j m‖ ^ 2 := by
      gcongr

theorem norm_vaughanShortIntervalTypeIIBetaCoefficient_le_one
    (U B : ℕ) (sk : ℕ × ℕ) (m : ℕ) :
    ‖vaughanShortIntervalCoefficient
        (fun m => (vaughanTypeIIBetaCoefficient U m : ℂ)) B sk m‖ ≤ 1 := by
  unfold vaughanShortIntervalCoefficient dyadicShortIntervalCoefficient
  split_ifs
  · simpa [Complex.norm_real, Real.norm_eq_abs] using
      abs_vaughanTypeIIBetaCoefficient_le_one U m
  · simp

/-- On an indexed Vaughan block, the divisor-tail coefficient has the
uniform logarithmic envelope needed by the Type II squared-inner-sum bound. -/
theorem norm_vaughanShortIntervalTypeIIGammaCoefficient_le_log_two_mul
    (V B : ℕ) (hB : 0 < B) {tl : ℕ × ℕ}
    (htl : tl ∈ vaughanShortIntervalIndexBox B) (n : ℕ) :
    ‖vaughanShortIntervalCoefficient
        (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) B tl n‖ ≤
      Real.log (2 * B) := by
  unfold vaughanShortIntervalCoefficient dyadicShortIntervalCoefficient
  by_cases hidx : dyadicShortIntervalIndex (vaughanShortIntervalBudget B) n = tl
  · rw [if_pos hidx]
    by_cases hn0 : n = 0
    · subst n
      simp [vaughanTypeIIGammaCoefficient]
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ 2 * B)
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnmem := (dyadicShortIntervalIndex_spec
      (vaughanShortIntervalBudget_pos B) hnpos le_rfl).2
    rw [hidx] at hnmem
    have hnraw := hnmem
    rw [dyadicShortIntervalIndexedBlock, mem_shortIntervalBlock] at hnraw
    have htlData : tl.1 < Nat.log 2 B + 1 := by
      rw [vaughanShortIntervalIndexBox, dyadicShortIntervalIndexBox] at htl
      exact Finset.mem_range.mp (Finset.mem_product.mp htl).1
    have htlLe : tl.1 ≤ Nat.log 2 B := by omega
    have hpowLe : 2 ^ tl.1 ≤ B :=
      (Nat.pow_le_pow_right (by omega) htlLe).trans
        (Nat.pow_log_le_self 2 hB.ne')
    have hnB : n ≤ 2 * B := by omega
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (vaughanTypeIIGammaCoefficient_nonneg V n)]
    exact (vaughanTypeIIGammaCoefficient_le_log V n).trans
      (by simpa [Nat.cast_mul] using
        (log_natCast_mono (Nat.one_le_iff_ne_zero.mpr hn0) hnB))
  · simp [hidx]
    have : 0 ≤ Real.log (2 * B) := by
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ 2 * B)
    exact this

/-- Source-coefficient specialization: the Möbius-tail outer coefficient is
removed completely, so a squared-inner-sum estimate for the divisor-tail
coefficient immediately bounds the actual Vaughan Type II double block. -/
theorem norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le
    (I : Finset ℕ) (B U V : ℕ) (sk tl : ℕ × ℕ)
    (N M : ℝ) (j : ℕ) (hI : ∀ x ∈ I, x ≤ B) :
    ‖weightedConvolutionProductVaughanDoubleBlockSum I B sk tl
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIIBetaCoefficient U) (vaughanTypeIIGammaCoefficient V)‖ ^ 2 ≤
      ((dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget B) sk).card : ℝ) *
        ∑ m ∈ dyadicShortIntervalIndexedBlock
            (vaughanShortIntervalBudget B) sk,
          ‖typeIIProductRestrictedInnerSum I
            (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget B) tl)
            (vaughanShortIntervalCoefficient
              (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) B tl)
            N M j m‖ ^ 2 := by
  simpa using
    (norm_weightedConvolutionProductVaughanDoubleBlockSum_sq_le
      I B sk tl (vaughanTypeIIBetaCoefficient U)
      (vaughanTypeIIGammaCoefficient V) N M j
      (L := 1)
      (fun m _hm => norm_vaughanShortIntervalTypeIIBetaCoefficient_le_one
        U B sk m) hI)

/-- Summing square bounds for every canonical double block controls the full
product-restricted convolution.  This is the exact finite passage from the
blockwise Type II estimates back to one Vaughan convolution term. -/
theorem norm_weightedConvolutionProductSum_le_sum_sqrt_vaughanDoubleBlocks
    (I : Finset ℕ) (B : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) (R : (ℕ × ℕ) → (ℕ × ℕ) → ℝ)
    (hR : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ tl ∈ vaughanShortIntervalIndexBox B,
        ‖weightedConvolutionProductVaughanDoubleBlockSum
          I B sk tl w f g‖ ^ 2 ≤ R sk tl) :
    ‖weightedConvolutionProductSum I B w f g‖ ≤
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ∑ tl ∈ vaughanShortIntervalIndexBox B, Real.sqrt (R sk tl) := by
  rw [weightedConvolutionProductSum_eq_sum_vaughanDoubleBlocks]
  calc
    ‖∑ sk ∈ vaughanShortIntervalIndexBox B,
        ∑ tl ∈ vaughanShortIntervalIndexBox B,
          weightedConvolutionProductVaughanDoubleBlockSum
            I B sk tl w f g‖ ≤
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ‖∑ tl ∈ vaughanShortIntervalIndexBox B,
          weightedConvolutionProductVaughanDoubleBlockSum
            I B sk tl w f g‖ := norm_sum_le _ _
    _ ≤ ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ∑ tl ∈ vaughanShortIntervalIndexBox B,
          ‖weightedConvolutionProductVaughanDoubleBlockSum
            I B sk tl w f g‖ := by
      apply Finset.sum_le_sum
      intro sk _hsk
      exact norm_sum_le _ _
    _ ≤ ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ∑ tl ∈ vaughanShortIntervalIndexBox B, Real.sqrt (R sk tl) := by
      apply Finset.sum_le_sum
      intro sk hsk
      apply Finset.sum_le_sum
      intro tl htl
      have hsq := hR sk hsk tl htl
      have hR0 : 0 ≤ R sk tl :=
        (sq_nonneg
          ‖weightedConvolutionProductVaughanDoubleBlockSum
            I B sk tl w f g‖).trans hsq
      exact (Real.le_sqrt (norm_nonneg _) hR0).2 hsq

/-- A uniform square bound for every canonical double block costs exactly the
square of the canonical family cardinality in the full convolution norm. -/
theorem norm_weightedConvolutionProductSum_le_familyCard_sq_mul_sqrt
    (I : Finset ℕ) (B : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) (R : ℝ)
    (hR : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ tl ∈ vaughanShortIntervalIndexBox B,
        ‖weightedConvolutionProductVaughanDoubleBlockSum
          I B sk tl w f g‖ ^ 2 ≤ R) :
    ‖weightedConvolutionProductSum I B w f g‖ ≤
      ((vaughanShortIntervalIndexBox B).card : ℝ) ^ 2 * Real.sqrt R := by
  have hsum :=
    norm_weightedConvolutionProductSum_le_sum_sqrt_vaughanDoubleBlocks
      I B w f g (fun _ _ => R) hR
  calc
    ‖weightedConvolutionProductSum I B w f g‖ ≤
        ∑ sk ∈ vaughanShortIntervalIndexBox B,
          ∑ tl ∈ vaughanShortIntervalIndexBox B, Real.sqrt R := hsum
    _ = ((vaughanShortIntervalIndexBox B).card : ℝ) ^ 2 * Real.sqrt R := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The exact polynomial-logarithmic loss corresponding to the canonical
`(log₂ B+1)^102` block family. -/
theorem norm_weightedConvolutionProductSum_le_logTwo_pow_twoHundredFour_mul_sqrt
    (I : Finset ℕ) (B : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) (R : ℝ)
    (hR : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ tl ∈ vaughanShortIntervalIndexBox B,
        ‖weightedConvolutionProductVaughanDoubleBlockSum
          I B sk tl w f g‖ ^ 2 ≤ R) :
    ‖weightedConvolutionProductSum I B w f g‖ ≤
      ((Nat.log 2 B + 1 : ℕ) : ℝ) ^ 204 * Real.sqrt R := by
  have h := norm_weightedConvolutionProductSum_le_familyCard_sq_mul_sqrt
    I B w f g R hR
  rw [card_vaughanShortIntervalIndexBox] at h
  calc
    ‖weightedConvolutionProductSum I B w f g‖ ≤
        ((((Nat.log 2 B + 1) ^ 102 : ℕ) : ℝ) ^ 2) * Real.sqrt R := h
    _ = ((Nat.log 2 B + 1 : ℕ) : ℝ) ^ 204 * Real.sqrt R := by
      rw [Nat.cast_pow]
      ring

end

end Tao2026
