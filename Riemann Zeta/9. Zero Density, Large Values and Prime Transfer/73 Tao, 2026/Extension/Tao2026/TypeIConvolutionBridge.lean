import Tao2026.ConvolutionRearrangement
import Tao2026.PartialSummation
import Tao2026.TypeIReduction

/-!
# Literal Type I convolution bridge

This module connects the two Type I blocks in the source-oriented Vaughan
identity to the one-dimensional reciprocal-phase sums used by the analytic
estimate.  The product restriction is retained exactly, then identified with
the ceiling-divided interval `(1 / m) [a,b)`.  The logarithmically weighted
inner sum is also connected directly to the finite Abel-summation interface.
-/

open ArithmeticFunction Complex Finset
open scoped BigOperators Moebius zeta

namespace Tao2026

noncomputable section

/-- The part of a canonical outer Vaughan block lying in the bounded product
box used by the literal convolution sum. -/
def vaughanTypeIProductBlockSupport (B : ℕ) (sk : ℕ × ℕ) : Finset ℕ :=
  (Finset.Ioc 0 B).filter fun m =>
    m ∈ dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget B) sk

/-- The exact inner support left by the condition `m*n ∈ I`. -/
def typeIProductRestrictedSupport
    (I S : Finset ℕ) (m : ℕ) : Finset ℕ :=
  S.filter fun n => m * n ∈ I

/-- A weighted Type I inner sum with the literal product restriction. -/
def typeIProductRestrictedWeightedInnerSum
    (I S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j m : ℕ) : ℂ :=
  ∑ n ∈ typeIProductRestrictedSupport I S m,
    γ n * standardAdditiveCharacter (reciprocalPhase N M j (m * n))

/-- The corresponding Type I outer sum. -/
def typeIProductRestrictedWeightedOuterSum
    (I K S : Finset ℕ) (β γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) : ℂ :=
  ∑ m ∈ K, β m *
    typeIProductRestrictedWeightedInnerSum I S γ N M j m

/-- The product-restricted outer sum is exactly the filtered product-box
sum, with no support convention suppressed. -/
theorem typeIProductRestrictedWeightedOuterSum_eq_productSum
    (I K S : Finset ℕ) (β γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) :
    typeIProductRestrictedWeightedOuterSum I K S β γ N M j =
      ∑ mn ∈ (K ×ˢ S).filter (fun mn => mn.1 * mn.2 ∈ I),
        β mn.1 * γ mn.2 *
          standardAdditiveCharacter
            (reciprocalPhase N M j (mn.1 * mn.2)) := by
  classical
  unfold typeIProductRestrictedWeightedOuterSum
    typeIProductRestrictedWeightedInnerSum typeIProductRestrictedSupport
  simp_rw [Finset.mul_sum]
  calc
    (∑ m ∈ K, ∑ n ∈ S.filter (fun n => m * n ∈ I),
        β m * (γ n *
          standardAdditiveCharacter (reciprocalPhase N M j (m * n)))) =
      ∑ mn ∈ K ×ˢ S,
        if mn.1 * mn.2 ∈ I then
          β mn.1 * (γ mn.2 * standardAdditiveCharacter
            (reciprocalPhase N M j (mn.1 * mn.2))) else 0 := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_product]
    _ = ∑ mn ∈ (K ×ˢ S).filter (fun mn => mn.1 * mn.2 ∈ I),
        β mn.1 * γ mn.2 * standardAdditiveCharacter
          (reciprocalPhase N M j (mn.1 * mn.2)) := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro mn _hmn
      by_cases hprod : mn.1 * mn.2 ∈ I
      · simp [hprod, mul_assoc]
      · simp [hprod]

/-- One literal Vaughan outer block is exactly a product-restricted Type I
outer sum. -/
theorem weightedConvolutionProductVaughanBlockSum_eq_typeIOuterSum
    (I : Finset ℕ) (B : ℕ) (sk : ℕ × ℕ)
    (f g : ArithmeticFunction ℝ) (N M : ℝ) (j : ℕ) :
    weightedConvolutionProductVaughanBlockSum I B sk
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n)) f g =
      typeIProductRestrictedWeightedOuterSum I
        (vaughanTypeIProductBlockSupport B sk) (Finset.Ioc 0 B)
        (vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk)
        (fun n => (g n : ℂ)) N M j := by
  classical
  rw [typeIProductRestrictedWeightedOuterSum_eq_productSum]
  unfold weightedConvolutionProductVaughanBlockSum
  simp only [Nat.cast_mul]
  symm
  apply Finset.sum_subset
  · intro mn hmn
    simp only [Finset.mem_filter, Finset.mem_product] at hmn ⊢
    exact ⟨⟨(Finset.mem_filter.mp hmn.1.1).1, hmn.1.2⟩, hmn.2⟩
  · intro mn hmnBox hmnSmall
    simp only [Finset.mem_filter, Finset.mem_product] at hmnBox
    by_cases hβ :
        vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk mn.1 = 0
    · simp [hβ]
    exfalso
    apply hmnSmall
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨Finset.mem_filter.mpr ⟨hmnBox.1.1,
      mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero
        (fun m => (f m : ℂ)) (Finset.mem_Ioc.mp hmnBox.1.1).1 hβ⟩,
      hmnBox.1.2⟩, hmnBox.2⟩

/-- Multiplying a half-open interval by a positive outer variable gives the
literal ceiling-divided inner interval.  The ambient `[1,B]` cutoff is
redundant once `b ≤ B`. -/
theorem typeIProductRestrictedSupport_Ico_eq
    {a b B m : ℕ} (ha : 0 < a) (hbB : b ≤ B) (hm : 0 < m) :
    typeIProductRestrictedSupport (Finset.Ico a b) (Finset.Ioc 0 B) m =
      Finset.Ico (a ⌈/⌉ m) (b ⌈/⌉ m) := by
  ext n
  simp only [typeIProductRestrictedSupport, Finset.mem_filter,
    Finset.mem_Ioc]
  have hprod : m * n ∈ Finset.Ico a b ↔
      n ∈ Finset.Ico (a ⌈/⌉ m) (b ⌈/⌉ m) := by
    simpa only [Nat.mul_comm] using
      (mul_mem_Ico_iff_mem_Ico_ceilDiv (a := a) (b := b) (m := n) (n := m) hm)
  constructor
  · rintro ⟨_hnBox, hnProd⟩
    exact hprod.mp hnProd
  · intro hn
    have hnProd := hprod.mpr hn
    have hnProdBounds := Finset.mem_Ico.mp hnProd
    have hnPos : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      simp at hnProdBounds
      omega
    have hnLeProd : n ≤ m * n := by
      simpa only [one_mul] using Nat.mul_le_mul_right n (Nat.one_le_iff_ne_zero.mpr hm.ne')
    refine ⟨⟨hnPos, ?_⟩, hnProd⟩
    omega

/-- Exact rescaling of a product-restricted weighted Type I inner sum. -/
theorem typeIProductRestrictedWeightedInnerSum_rescale
    (I S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j m : ℕ) :
    typeIProductRestrictedWeightedInnerSum I S γ N M j m =
      ∑ n ∈ typeIProductRestrictedSupport I S m,
        γ n * standardAdditiveCharacter
          (reciprocalPhase (N / m) (M / (m : ℝ) ^ j) j n) := by
  unfold typeIProductRestrictedWeightedInnerSum
  apply Finset.sum_congr rfl
  intro n _hn
  rw [reciprocalPhase_mul_rescale]

/-- On the source interval, the restricted inner sum is a weighted
reciprocal-phase sum on the exact ceiling-divided interval. -/
theorem typeIProductRestrictedWeightedInnerSum_Ico_eq
    {a b B m : ℕ} (ha : 0 < a) (hbB : b ≤ B) (hm : 0 < m)
    (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) :
    typeIProductRestrictedWeightedInnerSum
        (Finset.Ico a b) (Finset.Ioc 0 B) γ N M j m =
      ∑ n ∈ Finset.Ico (a ⌈/⌉ m) (b ⌈/⌉ m),
        γ n * standardAdditiveCharacter
          (reciprocalPhase (N / m) (M / (m : ℝ) ^ j) j n) := by
  rw [typeIProductRestrictedWeightedInnerSum_rescale,
    typeIProductRestrictedSupport_Ico_eq ha hbB hm]

/-- Unweighted specialization of the exact inner-interval bridge. -/
theorem typeIProductRestrictedInnerSum_Ico_eq
    {a b B m : ℕ} (ha : 0 < a) (hbB : b ≤ B) (hm : 0 < m)
    (N M : ℝ) (j : ℕ) :
    typeIProductRestrictedWeightedInnerSum
        (Finset.Ico a b) (Finset.Ioc 0 B) (fun _ => 1) N M j m =
      reciprocalPhaseSum (N / m) (M / (m : ℝ) ^ j) j
        (a ⌈/⌉ m) (b ⌈/⌉ m) := by
  rw [typeIProductRestrictedWeightedInnerSum_Ico_eq ha hbB hm]
  simp [reciprocalPhaseSum]

/-- Logarithmically weighted specialization in the scalar form consumed by
finite Abel summation. -/
theorem typeIProductRestrictedLogInnerSum_Ico_eq
    {a b B m : ℕ} (ha : 0 < a) (hbB : b ≤ B) (hm : 0 < m)
    (N M : ℝ) (j : ℕ) :
    typeIProductRestrictedWeightedInnerSum
        (Finset.Ico a b) (Finset.Ioc 0 B)
        (fun n => (Real.log n : ℂ)) N M j m =
      ∑ n ∈ Finset.Ico (a ⌈/⌉ m) (b ⌈/⌉ m),
        Real.log n • standardAdditiveCharacter
          (reciprocalPhase (N / m) (M / (m : ℝ) ^ j) j n) := by
  rw [typeIProductRestrictedWeightedInnerSum_Ico_eq ha hbB hm]
  apply Finset.sum_congr rfl
  intro n _hn
  simp [real_smul]

/-- Abel-summation entry point for the logarithmically weighted Type I
inner sum. -/
theorem norm_typeIProductRestrictedLogInnerSum_Ico_le
    {a b B m : ℕ} (ha : 0 < a) (hbB : b ≤ B) (hm : 0 < m)
    (N M : ℝ) (j : ℕ) {Q : ℝ}
    (hab : a ⌈/⌉ m < b ⌈/⌉ m) (hQ : 0 ≤ Q)
    (hpartial : ∀ k, a ⌈/⌉ m < k → k ≤ b ⌈/⌉ m →
      ‖reciprocalPhaseSum (N / m) (M / (m : ℝ) ^ j) j
        (a ⌈/⌉ m) k‖ ≤ Q) :
    ‖typeIProductRestrictedWeightedInnerSum
        (Finset.Ico a b) (Finset.Ioc 0 B)
        (fun n => (Real.log n : ℂ)) N M j m‖ ≤
      2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) * Q := by
  rw [typeIProductRestrictedLogInnerSum_Ico_eq ha hbB hm]
  apply norm_sum_Ico_log_smul_le
  · have haLe : a ≤ m * (a ⌈/⌉ m) := (ceilDiv_le_iff_le_mul hm).1 le_rfl
    exact Nat.one_le_iff_ne_zero.mpr fun hzero => by
      rw [hzero] at haLe
      simp at haLe
      omega
  · exact hab
  · exact hQ
  · intro k hak hkb
    simpa only [reciprocalPhaseSum, intervalPartialSum] using hpartial k hak hkb

/-- Triangle reduction for a product-restricted weighted Type I outer sum. -/
theorem norm_typeIProductRestrictedWeightedOuterSum_le
    (I K S : Finset ℕ) (β γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {L : ℝ}
    (hβ : ∀ m ∈ K, ‖β m‖ ≤ L) :
    ‖typeIProductRestrictedWeightedOuterSum I K S β γ N M j‖ ≤
      L * ∑ m ∈ K,
        ‖typeIProductRestrictedWeightedInnerSum I S γ N M j m‖ := by
  unfold typeIProductRestrictedWeightedOuterSum
  calc
    ‖∑ m ∈ K, β m *
        typeIProductRestrictedWeightedInnerSum I S γ N M j m‖ ≤
      ∑ m ∈ K, ‖β m *
        typeIProductRestrictedWeightedInnerSum I S γ N M j m‖ :=
        norm_sum_le K _
    _ ≤ ∑ m ∈ K, L *
        ‖typeIProductRestrictedWeightedInnerSum I S γ N M j m‖ := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hβ m hm) (norm_nonneg _)
    _ = L * ∑ m ∈ K,
        ‖typeIProductRestrictedWeightedInnerSum I S γ N M j m‖ := by
      rw [Finset.mul_sum]

/-- The first Type I short coefficient retains the unit envelope. -/
theorem norm_vaughanShortIntervalTypeICoefficient_le_one
    (U B : ℕ) (sk : ℕ × ℕ) (m : ℕ) :
    ‖vaughanShortIntervalCoefficient
        (fun m => (vaughanTypeICoefficient U m : ℂ)) B sk m‖ ≤ 1 := by
  unfold vaughanShortIntervalCoefficient dyadicShortIntervalCoefficient
  split_ifs
  · simpa [Complex.norm_real, Real.norm_eq_abs] using
      abs_vaughanTypeICoefficient_le_one U m
  · simp

/-- The second Type I short coefficient has the uniform `log(2B)` envelope
on every canonical block. -/
theorem norm_vaughanShortIntervalTypeIPrimeCoefficient_le_log_two_mul
    (U V B : ℕ) (hB : 0 < B) {sk : ℕ × ℕ}
    (hsk : sk ∈ vaughanShortIntervalIndexBox B) (m : ℕ) :
    ‖vaughanShortIntervalCoefficient
        (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)) B sk m‖ ≤
      Real.log (2 * B) := by
  unfold vaughanShortIntervalCoefficient dyadicShortIntervalCoefficient
  by_cases hidx : dyadicShortIntervalIndex (vaughanShortIntervalBudget B) m = sk
  · rw [if_pos hidx]
    by_cases hm0 : m = 0
    · subst m
      simp [vaughanTypeIPrimeCoefficient]
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ 2 * B)
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hmmem := (dyadicShortIntervalIndex_spec
      (vaughanShortIntervalBudget_pos B) hmpos le_rfl).2
    rw [hidx] at hmmem
    have hmraw := hmmem
    rw [dyadicShortIntervalIndexedBlock, mem_shortIntervalBlock] at hmraw
    have hskData : sk.1 < Nat.log 2 B + 1 := by
      rw [vaughanShortIntervalIndexBox, dyadicShortIntervalIndexBox] at hsk
      exact Finset.mem_range.mp (Finset.mem_product.mp hsk).1
    have hskLe : sk.1 ≤ Nat.log 2 B := by omega
    have hpowLe : 2 ^ sk.1 ≤ B :=
      (Nat.pow_le_pow_right (by omega) hskLe).trans
        (Nat.pow_log_le_self 2 hB.ne')
    have hmB : m ≤ 2 * B := by omega
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_vaughanTypeIPrimeCoefficient_le_log U V m).trans
      (by simpa [Nat.cast_mul] using
        (log_natCast_mono (Nat.one_le_iff_ne_zero.mpr hm0) hmB))
  · simp [hidx]
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * B)

/-- Source specialization for the logarithmically weighted first Type I
Vaughan block. -/
theorem norm_weightedConvolutionProductVaughanTypeILogBlockSum_le
    (I : Finset ℕ) (B U : ℕ) (sk : ℕ × ℕ)
    (N M : ℝ) (j : ℕ) :
    ‖weightedConvolutionProductVaughanBlockSum I B sk
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeICoefficient U) log‖ ≤
      ∑ m ∈ vaughanTypeIProductBlockSupport B sk,
        ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
          (fun n => (Real.log n : ℂ)) N M j m‖ := by
  rw [weightedConvolutionProductVaughanBlockSum_eq_typeIOuterSum]
  simpa using
    (norm_typeIProductRestrictedWeightedOuterSum_le I
      (vaughanTypeIProductBlockSupport B sk) (Finset.Ioc 0 B)
      (vaughanShortIntervalCoefficient
        (fun m => (vaughanTypeICoefficient U m : ℂ)) B sk)
      (fun n => (Real.log n : ℂ)) N M j (L := 1)
      (fun m _hm => norm_vaughanShortIntervalTypeICoefficient_le_one
        U B sk m))

/-- Source specialization for the unweighted second Type I Vaughan block. -/
theorem norm_weightedConvolutionProductVaughanTypeIPrimeBlockSum_le
    (I : Finset ℕ) (B U V : ℕ) (sk : ℕ × ℕ)
    (hB : 0 < B) (hsk : sk ∈ vaughanShortIntervalIndexBox B)
    (N M : ℝ) (j : ℕ) :
    ‖weightedConvolutionProductVaughanBlockSum I B sk
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      Real.log (2 * B) *
        ∑ m ∈ vaughanTypeIProductBlockSupport B sk,
          ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
            (fun _ => 1) N M j m‖ := by
  rw [weightedConvolutionProductVaughanBlockSum_eq_typeIOuterSum]
  have hbound := norm_typeIProductRestrictedWeightedOuterSum_le I
    (vaughanTypeIProductBlockSupport B sk) (Finset.Ioc 0 B)
    (vaughanShortIntervalCoefficient
      (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)) B sk)
    (fun n => ((ζ : ArithmeticFunction ℝ) n : ℂ)) N M j
    (L := Real.log (2 * B))
    (fun m _hm => norm_vaughanShortIntervalTypeIPrimeCoefficient_le_log_two_mul
      U V B hB hsk m)
  have hinner (m : ℕ) :
      typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
          (fun n => ((ζ : ArithmeticFunction ℝ) n : ℂ)) N M j m =
        typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
          (fun _ => 1) N M j m := by
    unfold typeIProductRestrictedWeightedInnerSum
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos := (Finset.mem_Ioc.mp
      (Finset.mem_filter.mp hn).1).1
    simp [Nat.ne_of_gt hnpos]
  simpa only [hinner] using hbound

/-- Reassembly of all canonical outer blocks for the first, logarithmically
weighted Type I convolution. -/
theorem norm_weightedConvolutionProductVaughanTypeILogSum_le
    (I : Finset ℕ) (B U : ℕ) (N M : ℝ) (j : ℕ) :
    ‖weightedConvolutionProductSum I B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeICoefficient U) log‖ ≤
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ∑ m ∈ vaughanTypeIProductBlockSupport B sk,
          ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
            (fun n => (Real.log n : ℂ)) N M j m‖ := by
  rw [weightedConvolutionProductSum_eq_sum_vaughanOuterBlocks]
  calc
    ‖∑ sk ∈ vaughanShortIntervalIndexBox B,
        weightedConvolutionProductVaughanBlockSum I B sk
          (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
          (vaughanTypeICoefficient U) log‖ ≤
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ‖weightedConvolutionProductVaughanBlockSum I B sk
          (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
          (vaughanTypeICoefficient U) log‖ := norm_sum_le _ _
    _ ≤ ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ∑ m ∈ vaughanTypeIProductBlockSupport B sk,
          ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
            (fun n => (Real.log n : ℂ)) N M j m‖ := by
      apply Finset.sum_le_sum
      intro sk _hsk
      exact norm_weightedConvolutionProductVaughanTypeILogBlockSum_le
        I B U sk N M j

/-- Reassembly of all canonical outer blocks for the second, unweighted
Type I convolution. -/
theorem norm_weightedConvolutionProductVaughanTypeIPrimeSum_le
    (I : Finset ℕ) (B U V : ℕ) (hB : 0 < B)
    (N M : ℝ) (j : ℕ) :
    ‖weightedConvolutionProductSum I B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      Real.log (2 * B) *
        ∑ sk ∈ vaughanShortIntervalIndexBox B,
          ∑ m ∈ vaughanTypeIProductBlockSupport B sk,
            ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
              (fun _ => 1) N M j m‖ := by
  rw [weightedConvolutionProductSum_eq_sum_vaughanOuterBlocks]
  calc
    ‖∑ sk ∈ vaughanShortIntervalIndexBox B,
        weightedConvolutionProductVaughanBlockSum I B sk
          (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
          (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ‖weightedConvolutionProductVaughanBlockSum I B sk
          (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
          (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ sk ∈ vaughanShortIntervalIndexBox B,
        Real.log (2 * B) *
          ∑ m ∈ vaughanTypeIProductBlockSupport B sk,
            ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
              (fun _ => 1) N M j m‖ := by
      apply Finset.sum_le_sum
      intro sk hsk
      exact norm_weightedConvolutionProductVaughanTypeIPrimeBlockSum_le
        I B U V sk hB hsk N M j
    _ = Real.log (2 * B) *
        ∑ sk ∈ vaughanShortIntervalIndexBox B,
          ∑ m ∈ vaughanTypeIProductBlockSupport B sk,
            ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
              (fun _ => 1) N M j m‖ := by
      rw [Finset.mul_sum]

/-- Source-interval form of the complete first Type I reduction.  Every
remaining summand is precisely the logarithmically weighted, rescaled
reciprocal-phase sum on `(1/m)[a,b)`. -/
theorem norm_weightedConvolutionProductVaughanTypeILogSum_Ico_le
    {a b : ℕ} (ha : 0 < a) (U : ℕ) (N M : ℝ) (j : ℕ) :
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeICoefficient U) log‖ ≤
      ∑ sk ∈ vaughanShortIntervalIndexBox b,
        ∑ m ∈ vaughanTypeIProductBlockSupport b sk,
          ‖∑ n ∈ Finset.Ico (a ⌈/⌉ m) (b ⌈/⌉ m),
            Real.log n • standardAdditiveCharacter
              (reciprocalPhase (N / m) (M / (m : ℝ) ^ j) j n)‖ := by
  have hbase := norm_weightedConvolutionProductVaughanTypeILogSum_le
    (Finset.Ico a b) b U N M j
  refine hbase.trans_eq ?_
  apply Finset.sum_congr rfl
  intro sk _hsk
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1
  rw [typeIProductRestrictedLogInnerSum_Ico_eq ha le_rfl hmpos]

/-- Source-interval form of the complete second Type I reduction.  Every
remaining summand is one unweighted reciprocal-phase sum with the exact
rescaled parameters. -/
theorem norm_weightedConvolutionProductVaughanTypeIPrimeSum_Ico_le
    {a b : ℕ} (ha : 0 < a) (U V : ℕ) (N M : ℝ) (j : ℕ) :
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      Real.log (2 * b) *
        ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ m ∈ vaughanTypeIProductBlockSupport b sk,
            ‖reciprocalPhaseSum (N / m) (M / (m : ℝ) ^ j) j
              (a ⌈/⌉ m) (b ⌈/⌉ m)‖ := by
  by_cases hab : a < b
  · have hbase := norm_weightedConvolutionProductVaughanTypeIPrimeSum_le
      (Finset.Ico a b) b U V (ha.trans hab) N M j
    refine hbase.trans_eq ?_
    congr 1
    apply Finset.sum_congr rfl
    intro sk _hsk
    apply Finset.sum_congr rfl
    intro m hm
    have hmpos : 0 < m :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1
    rw [typeIProductRestrictedInnerSum_Ico_eq ha le_rfl hmpos]
  · have hI : Finset.Ico a b = ∅ := Finset.Ico_eq_empty hab
    rw [hI]
    have hleft : weightedConvolutionProductSum ∅ b
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ) = 0 := by
      simp [weightedConvolutionProductSum]
    rw [hleft, norm_zero]
    apply mul_nonneg
    · by_cases hb0 : b = 0
      · simp [hb0]
      · apply Real.log_nonneg
        exact_mod_cast (by omega : 1 ≤ 2 * b)
    · positivity

/-! ## Coefficient-active Type I supports -/

/-- The actual nonzero outer support of one Vaughan Type I block.  Keeping
this filter is essential quantitatively: the first source coefficient is
supported only up to `U`, and the second only up to `U*V`. -/
def vaughanTypeIActiveProductBlockSupport
    (B : ℕ) (sk : ℕ × ℕ) (β : ℕ → ℂ) : Finset ℕ :=
  (vaughanTypeIProductBlockSupport B sk).filter fun m =>
    vaughanShortIntervalCoefficient β B sk m ≠ 0

/-- Zero outer coefficients may be removed exactly before applying the
triangle inequality. -/
theorem typeIProductRestrictedWeightedOuterSum_eq_filter_ne_zero
    (I K S : Finset ℕ) (β γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) :
    typeIProductRestrictedWeightedOuterSum I K S β γ N M j =
      typeIProductRestrictedWeightedOuterSum I
        (K.filter fun m => β m ≠ 0) S β γ N M j := by
  classical
  unfold typeIProductRestrictedWeightedOuterSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hβ : β m = 0 <;> simp [hβ]

/-- Active-support form of the exact literal block identity. -/
theorem weightedConvolutionProductVaughanBlockSum_eq_typeIActiveOuterSum
    (I : Finset ℕ) (B : ℕ) (sk : ℕ × ℕ)
    (f g : ArithmeticFunction ℝ) (N M : ℝ) (j : ℕ) :
    weightedConvolutionProductVaughanBlockSum I B sk
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n)) f g =
      typeIProductRestrictedWeightedOuterSum I
        (vaughanTypeIActiveProductBlockSupport B sk
          (fun m => (f m : ℂ)))
        (Finset.Ioc 0 B)
        (vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk)
        (fun n => (g n : ℂ)) N M j := by
  rw [weightedConvolutionProductVaughanBlockSum_eq_typeIOuterSum]
  exact typeIProductRestrictedWeightedOuterSum_eq_filter_ne_zero
    I (vaughanTypeIProductBlockSupport B sk) (Finset.Ioc 0 B)
      (vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk)
      (fun n => (g n : ℂ)) N M j

/-- Active indices of the first Type I coefficient retain its literal cutoff
`m≤U`. -/
theorem mem_vaughanTypeIActiveProductBlockSupport_typeI_imp_le
    {B U m : ℕ} {sk : ℕ × ℕ}
    (hm : m ∈ vaughanTypeIActiveProductBlockSupport B sk
      (fun m => (vaughanTypeICoefficient U m : ℂ))) :
    m ≤ U := by
  have hne := (Finset.mem_filter.mp hm).2
  by_contra hnot
  have hzero := vaughanTypeICoefficient_eq_zero_of_lt U m
    (Nat.lt_of_not_ge hnot)
  apply hne
  unfold vaughanShortIntervalCoefficient dyadicShortIntervalCoefficient
  split_ifs
  · simp [hzero]
  · rfl

/-- Active indices of the second Type I coefficient retain the convolution
cutoff `m≤U*V`. -/
theorem mem_vaughanTypeIActiveProductBlockSupport_typeIPrime_imp_le
    {B U V m : ℕ} {sk : ℕ × ℕ}
    (hm : m ∈ vaughanTypeIActiveProductBlockSupport B sk
      (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ))) :
    m ≤ U * V := by
  have hne := (Finset.mem_filter.mp hm).2
  by_contra hnot
  have hzero := vaughanTypeIPrimeCoefficient_eq_zero_of_mul_lt U V m
    (Nat.lt_of_not_ge hnot)
  apply hne
  unfold vaughanShortIntervalCoefficient dyadicShortIntervalCoefficient
  split_ifs
  · simp [hzero]
  · rfl

theorem card_vaughanTypeIActiveProductBlockSupport_typeI_le
    (B U : ℕ) (sk : ℕ × ℕ) :
    (vaughanTypeIActiveProductBlockSupport B sk
      (fun m => (vaughanTypeICoefficient U m : ℂ))).card ≤ U := by
  calc
    _ ≤ (Finset.Ioc 0 U).card := Finset.card_le_card fun m hm => by
      have hmRaw := (Finset.mem_filter.mp hm).1
      exact Finset.mem_Ioc.mpr
        ⟨(Finset.mem_Ioc.mp (Finset.mem_filter.mp hmRaw).1).1,
          mem_vaughanTypeIActiveProductBlockSupport_typeI_imp_le hm⟩
    _ = U := by simp

theorem card_vaughanTypeIActiveProductBlockSupport_typeIPrime_le
    (B U V : ℕ) (sk : ℕ × ℕ) :
    (vaughanTypeIActiveProductBlockSupport B sk
      (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ))).card ≤ U * V := by
  calc
    _ ≤ (Finset.Ioc 0 (U * V)).card := Finset.card_le_card fun m hm => by
      have hmRaw := (Finset.mem_filter.mp hm).1
      exact Finset.mem_Ioc.mpr
        ⟨(Finset.mem_Ioc.mp (Finset.mem_filter.mp hmRaw).1).1,
          mem_vaughanTypeIActiveProductBlockSupport_typeIPrime_imp_le hm⟩
    _ = U * V := by simp

/-- Strengthened first Type I block bound which pays only for active cutoff
indices. -/
theorem norm_weightedConvolutionProductVaughanTypeILogBlockSum_le_active
    (I : Finset ℕ) (B U : ℕ) (sk : ℕ × ℕ)
    (N M : ℝ) (j : ℕ) :
    ‖weightedConvolutionProductVaughanBlockSum I B sk
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeICoefficient U) log‖ ≤
      ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
          (fun m => (vaughanTypeICoefficient U m : ℂ)),
        ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
          (fun n => (Real.log n : ℂ)) N M j m‖ := by
  rw [weightedConvolutionProductVaughanBlockSum_eq_typeIActiveOuterSum]
  simpa using
    (norm_typeIProductRestrictedWeightedOuterSum_le I
      (vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient U m : ℂ)))
      (Finset.Ioc 0 B)
      (vaughanShortIntervalCoefficient
        (fun m => (vaughanTypeICoefficient U m : ℂ)) B sk)
      (fun n => (Real.log n : ℂ)) N M j (L := 1)
      (fun m _hm => norm_vaughanShortIntervalTypeICoefficient_le_one
        U B sk m))

/-- Strengthened second Type I block bound which pays only for active cutoff
indices. -/
theorem norm_weightedConvolutionProductVaughanTypeIPrimeBlockSum_le_active
    (I : Finset ℕ) (B U V : ℕ) (sk : ℕ × ℕ)
    (hB : 0 < B) (hsk : sk ∈ vaughanShortIntervalIndexBox B)
    (N M : ℝ) (j : ℕ) :
    ‖weightedConvolutionProductVaughanBlockSum I B sk
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      Real.log (2 * B) *
        ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
            (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
          ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
            (fun _ => 1) N M j m‖ := by
  rw [weightedConvolutionProductVaughanBlockSum_eq_typeIActiveOuterSum]
  have hbound := norm_typeIProductRestrictedWeightedOuterSum_le I
    (vaughanTypeIActiveProductBlockSupport B sk
      (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)))
    (Finset.Ioc 0 B)
    (vaughanShortIntervalCoefficient
      (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)) B sk)
    (fun n => ((ζ : ArithmeticFunction ℝ) n : ℂ)) N M j
    (L := Real.log (2 * B))
    (fun m _hm => norm_vaughanShortIntervalTypeIPrimeCoefficient_le_log_two_mul
      U V B hB hsk m)
  have hinner (m : ℕ) :
      typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
          (fun n => ((ζ : ArithmeticFunction ℝ) n : ℂ)) N M j m =
        typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
          (fun _ => 1) N M j m := by
    unfold typeIProductRestrictedWeightedInnerSum
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos := (Finset.mem_Ioc.mp
      (Finset.mem_filter.mp hn).1).1
    simp [Nat.ne_of_gt hnpos]
  simpa only [hinner] using hbound

/-- Full first Type I family with the cutoff-active outer supports retained. -/
theorem norm_weightedConvolutionProductVaughanTypeILogSum_le_active
    (I : Finset ℕ) (B U : ℕ) (N M : ℝ) (j : ℕ) :
    ‖weightedConvolutionProductSum I B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeICoefficient U) log‖ ≤
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
            (fun m => (vaughanTypeICoefficient U m : ℂ)),
          ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
            (fun n => (Real.log n : ℂ)) N M j m‖ := by
  rw [weightedConvolutionProductSum_eq_sum_vaughanOuterBlocks]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro sk _hsk
  exact norm_weightedConvolutionProductVaughanTypeILogBlockSum_le_active
    I B U sk N M j

/-- Full second Type I family with the cutoff-active outer supports retained. -/
theorem norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_active
    (I : Finset ℕ) (B U V : ℕ) (hB : 0 < B)
    (N M : ℝ) (j : ℕ) :
    ‖weightedConvolutionProductSum I B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      Real.log (2 * B) *
        ∑ sk ∈ vaughanShortIntervalIndexBox B,
          ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
              (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
            ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
              (fun _ => 1) N M j m‖ := by
  rw [weightedConvolutionProductSum_eq_sum_vaughanOuterBlocks]
  calc
    ‖∑ sk ∈ vaughanShortIntervalIndexBox B,
        weightedConvolutionProductVaughanBlockSum I B sk
          (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
          (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ‖weightedConvolutionProductVaughanBlockSum I B sk
          (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
          (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ sk ∈ vaughanShortIntervalIndexBox B,
        Real.log (2 * B) *
          ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
              (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
            ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
              (fun _ => 1) N M j m‖ := by
      apply Finset.sum_le_sum
      intro sk hsk
      exact norm_weightedConvolutionProductVaughanTypeIPrimeBlockSum_le_active
        I B U V sk hB hsk N M j
    _ = Real.log (2 * B) *
        ∑ sk ∈ vaughanShortIntervalIndexBox B,
          ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
              (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
            ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
              (fun _ => 1) N M j m‖ := by
      rw [Finset.mul_sum]

/-- A uniform inner estimate on one first-Type-I block pays only its true
cutoff cardinality. -/
theorem norm_weightedConvolutionProductVaughanTypeILogBlockSum_le_uniform
    (I : Finset ℕ) (B U : ℕ) (sk : ℕ × ℕ)
    (N M : ℝ) (j : ℕ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hinner : ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
      (fun m => (vaughanTypeICoefficient U m : ℂ)),
      ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
        (fun n => (Real.log n : ℂ)) N M j m‖ ≤ Q) :
    ‖weightedConvolutionProductVaughanBlockSum I B sk
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeICoefficient U) log‖ ≤ U * Q := by
  refine (norm_weightedConvolutionProductVaughanTypeILogBlockSum_le_active
    I B U sk N M j).trans ?_
  calc
    (∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient U m : ℂ)),
      ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
        (fun n => (Real.log n : ℂ)) N M j m‖) ≤
      ∑ _m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient U m : ℂ)), Q := by
      apply Finset.sum_le_sum
      intro m hm
      exact hinner m hm
    _ = ((vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient U m : ℂ))).card : ℝ) * Q := by
      simp
    _ ≤ U * Q := by
      apply mul_le_mul_of_nonneg_right _ hQ
      exact_mod_cast card_vaughanTypeIActiveProductBlockSupport_typeI_le B U sk

/-- A uniform inner estimate on one second-Type-I block pays only `U*V`,
besides its source coefficient envelope. -/
theorem norm_weightedConvolutionProductVaughanTypeIPrimeBlockSum_le_uniform
    (I : Finset ℕ) (B U V : ℕ) (sk : ℕ × ℕ)
    (hB : 0 < B) (hsk : sk ∈ vaughanShortIntervalIndexBox B)
    (N M : ℝ) (j : ℕ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hinner : ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
      (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
      ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
        (fun _ => 1) N M j m‖ ≤ Q) :
    ‖weightedConvolutionProductVaughanBlockSum I B sk
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      Real.log (2 * B) * (U * V) * Q := by
  refine (norm_weightedConvolutionProductVaughanTypeIPrimeBlockSum_le_active
    I B U V sk hB hsk N M j).trans ?_
  have hlog : 0 ≤ Real.log (2 * B) := by
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * B)
  calc
    Real.log (2 * B) *
        ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
          (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
          ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
            (fun _ => 1) N M j m‖ ≤
      Real.log (2 * B) *
        ∑ _m ∈ vaughanTypeIActiveProductBlockSupport B sk
          (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)), Q := by
      apply mul_le_mul_of_nonneg_left _ hlog
      apply Finset.sum_le_sum
      intro m hm
      exact hinner m hm
    _ = Real.log (2 * B) *
        ((vaughanTypeIActiveProductBlockSupport B sk
          (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ))).card : ℝ) * Q := by
      simp
      ring
    _ ≤ Real.log (2 * B) * (U * V) * Q := by
      gcongr
      exact_mod_cast
        card_vaughanTypeIActiveProductBlockSupport_typeIPrime_le B U V sk

/-- Exact complete-family loss for the first Type I term under one uniform
active-inner estimate. -/
theorem norm_weightedConvolutionProductVaughanTypeILogSum_le_uniform
    (I : Finset ℕ) (B U : ℕ) (N M : ℝ) (j : ℕ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hinner : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient U m : ℂ)),
        ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
          (fun n => (Real.log n : ℂ)) N M j m‖ ≤ Q) :
    ‖weightedConvolutionProductSum I B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeICoefficient U) log‖ ≤
      (Nat.log 2 B + 1 : ℕ) ^ 102 * U * Q := by
  rw [weightedConvolutionProductSum_eq_sum_vaughanOuterBlocks]
  calc
    ‖∑ sk ∈ vaughanShortIntervalIndexBox B,
        weightedConvolutionProductVaughanBlockSum I B sk
          (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
          (vaughanTypeICoefficient U) log‖ ≤
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ‖weightedConvolutionProductVaughanBlockSum I B sk
          (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
          (vaughanTypeICoefficient U) log‖ := norm_sum_le _ _
    _ ≤ ∑ _sk ∈ vaughanShortIntervalIndexBox B, (U : ℝ) * Q := by
      apply Finset.sum_le_sum
      intro sk hsk
      exact norm_weightedConvolutionProductVaughanTypeILogBlockSum_le_uniform
        I B U sk N M j hQ (hinner sk hsk)
    _ = (Nat.log 2 B + 1 : ℕ) ^ 102 * U * Q := by
      rw [Finset.sum_const, card_vaughanShortIntervalIndexBox]
      push_cast
      ring

/-- Exact complete-family loss for the second Type I term under one uniform
active-inner estimate. -/
theorem norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_uniform
    (I : Finset ℕ) (B U V : ℕ) (hB : 0 < B)
    (N M : ℝ) (j : ℕ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hinner : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
        ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
          (fun _ => 1) N M j m‖ ≤ Q) :
    ‖weightedConvolutionProductSum I B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      (Nat.log 2 B + 1 : ℕ) ^ 102 *
        (Real.log (2 * B) * (U * V) * Q) := by
  rw [weightedConvolutionProductSum_eq_sum_vaughanOuterBlocks]
  calc
    ‖∑ sk ∈ vaughanShortIntervalIndexBox B,
        weightedConvolutionProductVaughanBlockSum I B sk
          (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
          (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ‖weightedConvolutionProductVaughanBlockSum I B sk
          (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
          (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _sk ∈ vaughanShortIntervalIndexBox B,
        Real.log (2 * B) * (U * V) * Q := by
      apply Finset.sum_le_sum
      intro sk hsk
      exact norm_weightedConvolutionProductVaughanTypeIPrimeBlockSum_le_uniform
        I B U V sk hB hsk N M j hQ (hinner sk hsk)
    _ = (Nat.log 2 B + 1 : ℕ) ^ 102 *
        (Real.log (2 * B) * (U * V) * Q) := by
      rw [Finset.sum_const, card_vaughanShortIntervalIndexBox]
      push_cast
      rw [nsmul_eq_mul]
      push_cast
      rfl

/-! ## Type I scale and ceiling geometry -/

/-- The reciprocal-phase scale is antitone in its positive scale argument. -/
theorem reciprocalPhaseScale_anti
    (N M : ℝ) (j : ℕ) {X Y : ℝ}
    (hX : 0 < X) (hXY : X ≤ Y) :
    reciprocalPhaseScale N M j Y ≤ reciprocalPhaseScale N M j X := by
  have hY : 0 < Y := hX.trans_le hXY
  unfold reciprocalPhaseScale
  apply add_le_add
  · exact div_le_div_of_nonneg_left (abs_nonneg N) hX hXY
  · apply div_le_div_of_nonneg_left (abs_nonneg M) (pow_pos hX j)
    exact pow_le_pow_left₀ hX.le hXY j

/-- Exact invariance of the phase scale under the Type I substitution
`t=m*n`. -/
theorem reciprocalPhaseScale_rescale
    (N M X : ℝ) (j m : ℕ) (hX : X ≠ 0) (hm : 0 < m) :
    reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ j) j (X / m) =
      reciprocalPhaseScale N M j X := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmNonneg : (0 : ℝ) ≤ m := by positivity
  unfold reciprocalPhaseScale
  rw [abs_div, abs_div, abs_pow, abs_of_nonneg hmNonneg]
  rw [div_pow]
  field_simp [hmR]

/-- Equivalent multiplication form of Type I scale invariance. -/
theorem reciprocalPhaseScale_rescale_mul
    (N M X : ℝ) (j m : ℕ) (hX : X ≠ 0) (hm : 0 < m) :
    reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ j) j X =
      reciprocalPhaseScale N M j ((m : ℝ) * X) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmul : (m : ℝ) * X ≠ 0 := mul_ne_zero hmR hX
  have hbase := reciprocalPhaseScale_rescale N M ((m : ℝ) * X) j m hmul hm
  simpa [hmR] using hbase

/-- Ceiling division by a positive natural cannot exceed the numerator. -/
theorem ceilDiv_le_self_of_pos (P m : ℕ) (hm : 0 < m) :
    P ⌈/⌉ m ≤ P := by
  apply (ceilDiv_le_iff_le_mul hm).2
  have hmOne : 1 ≤ m := hm
  simpa only [one_mul] using Nat.mul_le_mul_right P hmOne

/-- Ceiling division commutes with doubling in the inequality direction
needed for a dyadic Type I fiber. -/
theorem ceilDiv_two_mul_le_two_mul_ceilDiv
    (P m : ℕ) (hm : 0 < m) :
    (2 * P) ⌈/⌉ m ≤ 2 * (P ⌈/⌉ m) := by
  apply (ceilDiv_le_iff_le_mul hm).2
  have hceil : P ≤ m * (P ⌈/⌉ m) :=
    (ceilDiv_le_iff_le_mul hm).1 le_rfl
  calc
    2 * P ≤ 2 * (m * (P ⌈/⌉ m)) := Nat.mul_le_mul_left 2 hceil
    _ = m * (2 * (P ⌈/⌉ m)) := by ac_rfl

/-- The exact Type I fiber of any subinterval of `[P,2P)` lies in the
ceiling-divided dyadic interval `[⌈P/m⌉,2⌈P/m⌉)`. -/
theorem typeI_ceilDiv_dyadic_geometry
    {P a b m : ℕ} (hm : 0 < m) (hPa : P ≤ a) (hbP : b ≤ 2 * P) :
    P ⌈/⌉ m ≤ a ⌈/⌉ m ∧ b ⌈/⌉ m ≤ 2 * (P ⌈/⌉ m) := by
  constructor
  · apply (ceilDiv_le_iff_le_mul hm).2
    exact hPa.trans ((ceilDiv_le_iff_le_mul hm).1 le_rfl)
  · apply (ceilDiv_le_iff_le_mul hm).2
    have hb : b ≤ 2 * P := hbP
    have hceil : P ≤ m * (P ⌈/⌉ m) :=
      (ceilDiv_le_iff_le_mul hm).1 le_rfl
    calc
      b ≤ 2 * P := hb
      _ ≤ 2 * (m * (P ⌈/⌉ m)) := Nat.mul_le_mul_left 2 hceil
      _ = m * (2 * (P ⌈/⌉ m)) := by ac_rfl

/-- The ceiling-rounded Type I scale remains positive. -/
theorem typeI_ceilDiv_pos {P m : ℕ} (hP : 0 < P) (hm : 0 < m) :
    0 < P ⌈/⌉ m := by
  by_contra hzero
  have heq : P ⌈/⌉ m = 0 := Nat.eq_zero_of_not_pos hzero
  have hceil : P ≤ m * (P ⌈/⌉ m) :=
    (ceilDiv_le_iff_le_mul hm).1 le_rfl
  rw [heq] at hceil
  simp at hceil
  omega

/-- Passing from the exact rescaled real scale `P/m` to the rounded natural
scale `⌈P/m⌉` can only decrease the reciprocal-phase scale. -/
theorem reciprocalPhaseScale_typeI_rescale_ceilDiv_le
    (N M : ℝ) (j : ℕ) {P m : ℕ} (hP : 0 < P) (hm : 0 < m) :
    reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ j) j (P ⌈/⌉ m : ℕ) ≤
      reciprocalPhaseScale N M j P := by
  let X : ℝ := (P ⌈/⌉ m : ℕ)
  have hXnat : 0 < P ⌈/⌉ m := typeI_ceilDiv_pos hP hm
  have hX : 0 < X := by
    change (0 : ℝ) < (P ⌈/⌉ m : ℕ)
    exact_mod_cast hXnat
  have hPXnat : P ≤ m * (P ⌈/⌉ m) :=
    (ceilDiv_le_iff_le_mul hm).1 le_rfl
  have hPX : (P : ℝ) ≤ (m : ℝ) * X := by
    dsimp only [X]
    exact_mod_cast hPXnat
  rw [reciprocalPhaseScale_rescale_mul N M X j m hX.ne' hm]
  exact reciprocalPhaseScale_anti N M j (by exact_mod_cast hP) hPX

/-- Consequently a source upper bound `F≤(P/m)^4` supplies the low-scale
Weyl condition at the rounded Type I scale. -/
theorem reciprocalPhaseScale_typeI_rescale_ceilDiv_le_pow_four
    (N M : ℝ) (j : ℕ) {P m : ℕ} (hP : 0 < P) (hm : 0 < m)
    (hFlow : reciprocalPhaseScale N M j P ≤
      ((P : ℝ) / m) ^ 4) :
    reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ j) j
        (P ⌈/⌉ m : ℕ) ≤ ((P ⌈/⌉ m : ℕ) : ℝ) ^ 4 := by
  have hscale := reciprocalPhaseScale_typeI_rescale_ceilDiv_le
    N M j hP hm
  have hdiv : (P : ℝ) / m ≤ (P ⌈/⌉ m : ℕ) := by
    rw [div_le_iff₀ (by exact_mod_cast hm)]
    have hceil : P ≤ m * (P ⌈/⌉ m) :=
      (ceilDiv_le_iff_le_mul hm).1 le_rfl
    have hceil' : P ≤ (P ⌈/⌉ m) * m := by
      simpa only [Nat.mul_comm] using hceil
    exact_mod_cast hceil'
  exact hscale.trans (hFlow.trans (pow_le_pow_left₀ (by positivity) hdiv 4))

end

end Tao2026
