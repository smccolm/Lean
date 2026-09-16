import Tao2026.TypeIIConvolutionBridge
import Tao2026.WeylDifferencing

open Complex Finset Filter Topology
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- The complete conditional estimate for one actual source Type II Vaughan
double block. -/
theorem eventually_norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le_sourceVinogradov
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b U V : ℕ) (N : ℝ) (orders : Finset ℕ) (sk tl : ℕ × ℕ) (d : ℝ),
        0 < b → 2 ≤ Real.log b →
        sk ∈ vaughanShortIntervalIndexBox b →
        tl ∈ vaughanShortIntervalIndexBox b →
        (vaughanShortIntervalBudget b : ℝ) ≤ (2 ^ sk.1 : ℕ) →
        N ≠ 0 → 5 ∈ orders → 6 ∈ orders → 0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N N 2
          (((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
            ((2 * 2 ^ tl.1 : ℕ) : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log
          ((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) →
        let qouter := dyadicShortIntervalLength (2 ^ sk.1)
          (vaughanShortIntervalBudget b)
        let qinner := dyadicShortIntervalLength (2 ^ tl.1)
          (vaughanShortIntervalBudget b)
        let K : ℝ := (dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ)
        let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
        let F := reciprocalPhaseScale N N 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖weightedConvolutionProductVaughanDoubleBlockSum
            (Finset.Ico a b) b sk tl
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient U)
            (vaughanTypeIIGammaCoefficient V)‖ ^ 2 ≤
          ((dyadicShortIntervalIndexedBlock
              (vaughanShortIntervalBudget b) sk).card : ℝ) *
            ((qouter : ℝ) * (qinner : ℝ) * (Real.log (2 * b)) ^ 2 +
              (Real.log (2 * b)) ^ 2 * ((qinner : ℝ) *
                (Q * (4 *
                    (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                      (1 - (1 / 1024 : ℝ))) * B *
                        F ^ (-(1 / 1024 : ℝ)))) +
                  (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) +
                    3 * (Real.log P) ^ (-T)))))) := by
  have hinner :=
    eventually_sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_sourceVinogradov
      hVinogradov hA hA₀ hc hε ha hAT
  filter_upwards [hinner] with P hinnerP
  intro a b U V N orders sk tl d hb hlog hsk htl hDouter hN
    hrFive hrSix hd hFhigh hNupper hKlower
  let γ : ℕ → ℂ := vaughanShortIntervalCoefficient
    (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) b tl
  let L : ℝ := Real.log (2 * b)
  have hL : 0 ≤ L := by
    unfold L
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * b)
  have hγ : ∀ n, ‖γ n‖ ≤ L := by
    intro n
    exact norm_vaughanShortIntervalTypeIIGammaCoefficient_le_log_two_mul
      V b hb htl n
  have hinnerBound := hinnerP a b b γ N orders sk tl L d hb hlog hDouter
    hL hγ hN hrFive hrSix hd hFhigh hNupper hKlower
  have hI : ∀ x ∈ Finset.Ico a b, x ≤ b := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    omega
  have hbridge :=
    norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le
      (Finset.Ico a b) b U V sk tl N N 2 hI
  exact hbridge.trans (mul_le_mul_of_nonneg_left
    (by simpa only [γ, L] using hinnerBound) (Nat.cast_nonneg _))

/-- A Vaughan beta block vanishes whenever its complete dyadic band lies at
or below the Möbius-tail cutoff. -/
theorem vaughanShortIntervalTypeIIBetaCoefficient_eq_zero_of_dyadicBand
    (B U : ℕ) (sk : ℕ × ℕ) (hcut : 2 * 2 ^ sk.1 ≤ U) (m : ℕ) :
    vaughanShortIntervalCoefficient
        (fun m => (vaughanTypeIIBetaCoefficient U m : ℂ)) B sk m = 0 := by
  by_cases hcoefficient :
      vaughanShortIntervalCoefficient
          (fun m => (vaughanTypeIIBetaCoefficient U m : ℂ)) B sk m = 0
  · exact hcoefficient
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp [vaughanShortIntervalCoefficient,
      dyadicShortIntervalCoefficient] at hcoefficient
  have hmblock :=
    mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero
      (fun m => (vaughanTypeIIBetaCoefficient U m : ℂ)) hmpos hcoefficient
  have hmbounds := hmblock
  rw [dyadicShortIntervalIndexedBlock, mem_shortIntervalBlock] at hmbounds
  have hmU : m ≤ U := by omega
  have hraw := vaughanTypeIIBetaCoefficient_eq_zero_of_le U m hmU
  unfold vaughanShortIntervalCoefficient dyadicShortIntervalCoefficient
  split_ifs
  · simp [hraw]
  · rfl

/-- If the outer dyadic band lies below the common subdivision budget and the
Möbius-tail cutoff dominates twice that budget, its restricted Type II
coefficient vanishes identically. -/
theorem vaughanShortIntervalTypeIIBetaCoefficient_eq_zero_of_outerSmall
    (B U : ℕ) (sk : ℕ × ℕ)
    (hsmall : 2 ^ sk.1 < vaughanShortIntervalBudget B)
    (hU : 2 * vaughanShortIntervalBudget B ≤ U) (m : ℕ) :
    vaughanShortIntervalCoefficient
        (fun m => (vaughanTypeIIBetaCoefficient U m : ℂ)) B sk m = 0 := by
  by_cases hcoefficient :
      vaughanShortIntervalCoefficient
          (fun m => (vaughanTypeIIBetaCoefficient U m : ℂ)) B sk m = 0
  · exact hcoefficient
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp [vaughanShortIntervalCoefficient,
      dyadicShortIntervalCoefficient] at hcoefficient
  have hmblock :=
    mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero
      (fun m => (vaughanTypeIIBetaCoefficient U m : ℂ)) hmpos hcoefficient
  have hmbounds := hmblock
  rw [dyadicShortIntervalIndexedBlock, mem_shortIntervalBlock] at hmbounds
  have hmU : m ≤ U := by omega
  have hraw := vaughanTypeIIBetaCoefficient_eq_zero_of_le U m hmU
  unfold vaughanShortIntervalCoefficient dyadicShortIntervalCoefficient
  split_ifs
  · simp [hraw]
  · rfl

/-- Every literal source Type II double block with a small outer dyadic band
is exactly zero. -/
theorem weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_outerSmall
    (I : Finset ℕ) (B U V : ℕ) (sk tl : ℕ × ℕ) (N M : ℝ) (j : ℕ)
    (hsmall : 2 ^ sk.1 < vaughanShortIntervalBudget B)
    (hU : 2 * vaughanShortIntervalBudget B ≤ U) :
    weightedConvolutionProductVaughanDoubleBlockSum I B sk tl
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIIBetaCoefficient U) (vaughanTypeIIGammaCoefficient V) = 0 := by
  classical
  unfold weightedConvolutionProductVaughanDoubleBlockSum
  apply Finset.sum_eq_zero
  intro mn _hmn
  rw [vaughanShortIntervalTypeIIBetaCoefficient_eq_zero_of_outerSmall
    B U sk hsmall hU mn.1]
  simp

/-- Literal block form of cutoff vanishing for the outer Type II factor. -/
theorem weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_outerCutoff
    (I : Finset ℕ) (B U V : ℕ) (sk tl : ℕ × ℕ) (N M : ℝ) (j : ℕ)
    (hcut : 2 * 2 ^ sk.1 ≤ U) :
    weightedConvolutionProductVaughanDoubleBlockSum I B sk tl
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIIBetaCoefficient U) (vaughanTypeIIGammaCoefficient V) = 0 := by
  classical
  unfold weightedConvolutionProductVaughanDoubleBlockSum
  apply Finset.sum_eq_zero
  intro mn _hmn
  rw [vaughanShortIntervalTypeIIBetaCoefficient_eq_zero_of_dyadicBand
    B U sk hcut mn.1]
  simp

/-- A Vaughan gamma block vanishes whenever its complete dyadic band lies at
or below the divisor-tail cutoff. -/
theorem vaughanShortIntervalTypeIIGammaCoefficient_eq_zero_of_dyadicBand
    (B V : ℕ) (tl : ℕ × ℕ) (hcut : 2 * 2 ^ tl.1 ≤ V) (n : ℕ) :
    vaughanShortIntervalCoefficient
        (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) B tl n = 0 := by
  by_cases hcoefficient :
      vaughanShortIntervalCoefficient
          (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) B tl n = 0
  · exact hcoefficient
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [vaughanShortIntervalCoefficient,
      dyadicShortIntervalCoefficient] at hcoefficient
  have hnblock :=
    mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero
      (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) hnpos hcoefficient
  have hnbounds := hnblock
  rw [dyadicShortIntervalIndexedBlock, mem_shortIntervalBlock] at hnbounds
  have hnV : n ≤ V := by omega
  have hraw := vaughanTypeIIGammaCoefficient_eq_zero_of_le V n hnV
  unfold vaughanShortIntervalCoefficient dyadicShortIntervalCoefficient
  split_ifs
  · simp [hraw]
  · rfl

/-- The same cutoff mechanism annihilates the divisor-tail coefficient on a
small inner dyadic band. -/
theorem vaughanShortIntervalTypeIIGammaCoefficient_eq_zero_of_innerSmall
    (B V : ℕ) (tl : ℕ × ℕ)
    (hsmall : 2 ^ tl.1 < vaughanShortIntervalBudget B)
    (hV : 2 * vaughanShortIntervalBudget B ≤ V) (n : ℕ) :
    vaughanShortIntervalCoefficient
        (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) B tl n = 0 := by
  by_cases hcoefficient :
      vaughanShortIntervalCoefficient
          (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) B tl n = 0
  · exact hcoefficient
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [vaughanShortIntervalCoefficient,
      dyadicShortIntervalCoefficient] at hcoefficient
  have hnblock :=
    mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero
      (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) hnpos hcoefficient
  have hnbounds := hnblock
  rw [dyadicShortIntervalIndexedBlock, mem_shortIntervalBlock] at hnbounds
  have hnV : n ≤ V := by omega
  have hraw := vaughanTypeIIGammaCoefficient_eq_zero_of_le V n hnV
  unfold vaughanShortIntervalCoefficient dyadicShortIntervalCoefficient
  split_ifs
  · simp [hraw]
  · rfl

/-- Every literal source Type II double block with a small inner dyadic band
is exactly zero once the divisor-tail cutoff dominates the common budget. -/
theorem weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_innerSmall
    (I : Finset ℕ) (B U V : ℕ) (sk tl : ℕ × ℕ) (N M : ℝ) (j : ℕ)
    (hsmall : 2 ^ tl.1 < vaughanShortIntervalBudget B)
    (hV : 2 * vaughanShortIntervalBudget B ≤ V) :
    weightedConvolutionProductVaughanDoubleBlockSum I B sk tl
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIIBetaCoefficient U) (vaughanTypeIIGammaCoefficient V) = 0 := by
  classical
  unfold weightedConvolutionProductVaughanDoubleBlockSum
  apply Finset.sum_eq_zero
  intro mn _hmn
  rw [vaughanShortIntervalTypeIIGammaCoefficient_eq_zero_of_innerSmall
    B V tl hsmall hV mn.2]
  simp

/-- Literal block form of cutoff vanishing for the inner Type II factor. -/
theorem weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_innerCutoff
    (I : Finset ℕ) (B U V : ℕ) (sk tl : ℕ × ℕ) (N M : ℝ) (j : ℕ)
    (hcut : 2 * 2 ^ tl.1 ≤ V) :
    weightedConvolutionProductVaughanDoubleBlockSum I B sk tl
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIIBetaCoefficient U) (vaughanTypeIIGammaCoefficient V) = 0 := by
  classical
  unfold weightedConvolutionProductVaughanDoubleBlockSum
  apply Finset.sum_eq_zero
  intro mn _hmn
  rw [vaughanShortIntervalTypeIIGammaCoefficient_eq_zero_of_dyadicBand
    B V tl hcut mn.2]
  simp

/-- The complementary small-inner regime is diagonal, so the literal source
double block has an unconditional square bound. -/
theorem norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le_of_innerSmall
    (a b U V : ℕ) (N : ℝ) (sk tl : ℕ × ℕ)
    (hb : 0 < b) (htl : tl ∈ vaughanShortIntervalIndexBox b)
    (hsmall : 2 ^ tl.1 < vaughanShortIntervalBudget b) :
    let qouter := dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget b)
    ‖weightedConvolutionProductVaughanDoubleBlockSum
        (Finset.Ico a b) b sk tl
        (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
        (vaughanTypeIIBetaCoefficient U)
        (vaughanTypeIIGammaCoefficient V)‖ ^ 2 ≤
      ((dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget b) sk).card : ℝ) *
        (qouter : ℝ) * (Real.log (2 * b)) ^ 2 := by
  dsimp only
  let γ : ℕ → ℂ := vaughanShortIntervalCoefficient
    (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) b tl
  let L : ℝ := Real.log (2 * b)
  have hL : 0 ≤ L := by
    unfold L
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * b)
  have hγ : ∀ n, ‖γ n‖ ≤ L := by
    intro n
    exact norm_vaughanShortIntervalTypeIIGammaCoefficient_le_log_two_mul
      V b hb htl n
  have hinner :=
    sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_singleton
      a b b γ N sk tl hsmall hL hγ
  have hI : ∀ x ∈ Finset.Ico a b, x ≤ b := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    omega
  have hbridge :=
    norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le
      (Finset.Ico a b) b U V sk tl N N 2 hI
  exact hbridge.trans <| by
    have hcard : 0 ≤
        ((dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget b) sk).card : ℝ) := Nat.cast_nonneg _
    simpa only [γ, L, mul_assoc] using
      (mul_le_mul_of_nonneg_left hinner hcard)

/-- Canonical product pairs carried by one Vaughan Type II double block and
the literal source interval. -/
def vaughanTypeIIDoubleBlockProductSupport
    (a b : ℕ) (sk tl : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget b) sk ×ˢ
    dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget b) tl).filter
      fun mn => mn.1 * mn.2 ∈ Finset.Ico a b

/-- A double block with no canonical product pair in the source interval is
literally zero, independently of its coefficient values. -/
theorem weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_productSupport_eq_empty
    (a b U V : ℕ) (sk tl : ℕ × ℕ) (N : ℝ)
    (hsupport : vaughanTypeIIDoubleBlockProductSupport a b sk tl = ∅) :
    weightedConvolutionProductVaughanDoubleBlockSum
        (Finset.Ico a b) b sk tl
        (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
        (vaughanTypeIIBetaCoefficient U) (vaughanTypeIIGammaCoefficient V) = 0 := by
  classical
  unfold weightedConvolutionProductVaughanDoubleBlockSum
  apply Finset.sum_eq_zero
  intro mn hmn
  by_cases hβ : vaughanShortIntervalCoefficient
      (fun m => (vaughanTypeIIBetaCoefficient U m : ℂ)) b sk mn.1 = 0
  · simp [hβ]
  by_cases hγ : vaughanShortIntervalCoefficient
      (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) b tl mn.2 = 0
  · simp [hγ]
  have hmnData := Finset.mem_filter.mp hmn
  have hbox := Finset.mem_product.mp hmnData.1
  have hmpos := (Finset.mem_Ioc.mp hbox.1).1
  have hnpos := (Finset.mem_Ioc.mp hbox.2).1
  have hmblock := mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero
    (fun m => (vaughanTypeIIBetaCoefficient U m : ℂ)) hmpos hβ
  have hnblock := mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero
    (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) hnpos hγ
  have hcanonical : mn ∈ vaughanTypeIIDoubleBlockProductSupport a b sk tl := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmblock, hnblock⟩, hmnData.2⟩
  rw [hsupport] at hcanonical
  simp at hcanonical

/-- Any contributing canonical double block has analytic product scale at
most twice the upper source endpoint. -/
theorem vaughanTypeIIDoubleBlockProductScale_le_two_mul
    {a b : ℕ} {sk tl : ℕ × ℕ} {mn : ℕ × ℕ}
    (hmn : mn ∈ vaughanTypeIIDoubleBlockProductSupport a b sk tl) :
    ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ) ≤ 2 * b := by
  have hdata := Finset.mem_filter.mp hmn
  have hblocks := Finset.mem_product.mp hdata.1
  have hmBounds := mem_dyadicShortIntervalIndexedBlock_bounds
    (vaughanShortIntervalBudget_pos b) hblocks.1
  have hnBounds := mem_dyadicShortIntervalIndexedBlock_bounds
    (vaughanShortIntervalBudget_pos b) hblocks.2
  have hDinnerLeft : 2 ^ tl.1 ≤ dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) tl := by
    unfold dyadicShortIntervalLeftEndpoint
    omega
  have hDinnerN : 2 ^ tl.1 ≤ mn.2 := hDinnerLeft.trans hnBounds.1
  have hnat : dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk * (2 * 2 ^ tl.1) ≤ 2 * b := by
    calc
      dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk * (2 * 2 ^ tl.1) ≤
          mn.1 * (2 * mn.2) :=
        Nat.mul_le_mul hmBounds.1 (Nat.mul_le_mul_left 2 hDinnerN)
      _ = 2 * (mn.1 * mn.2) := by ring
      _ ≤ 2 * b := Nat.mul_le_mul_left 2
        (Nat.le_of_lt (Finset.mem_Ico.mp hdata.2).2)
  exact_mod_cast hnat

/-- Product support bounds the product of the two underlying dyadic scales by
the source endpoint. -/
theorem vaughanTypeIIDoubleBlockDyadicProduct_le
    {a b : ℕ} {sk tl : ℕ × ℕ} {mn : ℕ × ℕ}
    (hmn : mn ∈ vaughanTypeIIDoubleBlockProductSupport a b sk tl) :
    (((2 ^ sk.1 : ℕ) : ℝ) * ((2 ^ tl.1 : ℕ) : ℝ)) ≤ b := by
  have hscale := vaughanTypeIIDoubleBlockProductScale_le_two_mul hmn
  norm_num [Nat.cast_mul, Nat.cast_pow] at hscale
  have hDKNat : 2 ^ sk.1 ≤ dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk := by
    unfold dyadicShortIntervalLeftEndpoint
    omega
  have hDK : ((2 ^ sk.1 : ℕ) : ℝ) ≤
      (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) := by exact_mod_cast hDKNat
  have hKE :
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
          ((2 ^ tl.1 : ℕ) : ℝ) ≤ b := by
    have hscale' :
        2 * (((dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
            ((2 ^ tl.1 : ℕ) : ℝ)) ≤ 2 * b := by
      calc
      2 * (((dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
            ((2 ^ tl.1 : ℕ) : ℝ)) =
          ((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
              (2 * ((2 ^ tl.1 : ℕ) : ℝ)) := by ring
      _ ≤ 2 * b := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hscale
    nlinarith
  exact (mul_le_mul_of_nonneg_right hDK (by positivity)).trans hKE

/-- The first dyadic cubic monomial in the Type II block square is at most
`b²` on product support. -/
theorem vaughanTypeIIDoubleBlockOuterSquareInner_le_sq
    {a b : ℕ} {sk tl : ℕ × ℕ} {mn : ℕ × ℕ}
    (hmn : mn ∈ vaughanTypeIIDoubleBlockProductSupport a b sk tl) :
    ((2 ^ sk.1 : ℕ) : ℝ) * ((2 ^ sk.1 : ℕ) : ℝ) *
        ((2 ^ tl.1 : ℕ) : ℝ) ≤ (b : ℝ) ^ 2 := by
  have hproduct := vaughanTypeIIDoubleBlockDyadicProduct_le hmn
  have hinnerOne : (1 : ℝ) ≤ (2 ^ tl.1 : ℕ) := by
    exact_mod_cast (one_le_pow₀ (by omega : 0 < (2 : ℕ)))
  have houter : ((2 ^ sk.1 : ℕ) : ℝ) ≤ b := by
    have := mul_le_mul_of_nonneg_left hinnerOne
      (show (0 : ℝ) ≤ (2 ^ sk.1 : ℕ) by positivity)
    nlinarith
  calc
    ((2 ^ sk.1 : ℕ) : ℝ) * ((2 ^ sk.1 : ℕ) : ℝ) *
        ((2 ^ tl.1 : ℕ) : ℝ) =
        ((2 ^ sk.1 : ℕ) : ℝ) *
          (((2 ^ sk.1 : ℕ) : ℝ) * ((2 ^ tl.1 : ℕ) : ℝ)) := by ring
    _ ≤ (b : ℝ) * b :=
      mul_le_mul houter hproduct (by positivity) (by positivity)
    _ = (b : ℝ) ^ 2 := by ring

/-- The endpoint-weighted dyadic quartic monomial occurring in both analytic
error terms is at most `b²` on product support. -/
theorem vaughanTypeIIDoubleBlockEndpointInnerSquare_le_sq
    {a b : ℕ} {sk tl : ℕ × ℕ} {mn : ℕ × ℕ}
    (hmn : mn ∈ vaughanTypeIIDoubleBlockProductSupport a b sk tl) :
    ((2 ^ sk.1 : ℕ) : ℝ) *
        (dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ) *
        ((2 ^ tl.1 : ℕ) : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 := by
  have hscale := vaughanTypeIIDoubleBlockProductScale_le_two_mul hmn
  norm_num [Nat.cast_mul, Nat.cast_pow] at hscale
  have hKE :
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
          ((2 ^ tl.1 : ℕ) : ℝ) ≤ b := by
    have hscale' :
        2 * (((dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
            ((2 ^ tl.1 : ℕ) : ℝ)) ≤ 2 * b := by
      calc
      2 * (((dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
            ((2 ^ tl.1 : ℕ) : ℝ)) =
          ((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
              (2 * ((2 ^ tl.1 : ℕ) : ℝ)) := by ring
      _ ≤ 2 * b := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hscale
    nlinarith
  have hDE := vaughanTypeIIDoubleBlockDyadicProduct_le hmn
  calc
    ((2 ^ sk.1 : ℕ) : ℝ) *
        (dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ) *
        ((2 ^ tl.1 : ℕ) : ℝ) ^ 2 =
        (((2 ^ sk.1 : ℕ) : ℝ) * ((2 ^ tl.1 : ℕ) : ℝ)) *
          ((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) *
              ((2 ^ tl.1 : ℕ) : ℝ)) := by ring
    _ ≤ (b : ℝ) * b :=
      mul_le_mul hDE hKE (by positivity) (by positivity)
    _ = (b : ℝ) ^ 2 := by ring

/-- A single global lower bound for the original phase scale supplies the
lower-frequency premise on every contributing double block. -/
theorem logPower_le_reciprocalPhaseScale_of_productSupport
    {a b : ℕ} {N d : ℝ} {sk tl : ℕ × ℕ} {mn : ℕ × ℕ}
    (hlog : 0 ≤ Real.log b)
    (hglobal : 2 * (b : ℝ) * (Real.log b) ^ d ≤ |N|)
    (hmn : mn ∈ vaughanTypeIIDoubleBlockProductSupport a b sk tl) :
    (Real.log b) ^ d ≤ reciprocalPhaseScale N N 2
      (((dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ)) := by
  let X : ℝ := ((dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
      ((2 * 2 ^ tl.1 : ℕ) : ℝ)
  have hXpos : 0 < X := by
    unfold X
    have hleft : 0 < dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk := by
      unfold dyadicShortIntervalLeftEndpoint
      exact (pow_pos (by omega : 0 < (2 : ℕ)) sk.1).trans_le
        (Nat.le_add_right _ _)
    have hright : 0 < 2 * 2 ^ tl.1 := by positivity
    exact mul_pos (by exact_mod_cast hleft) (by exact_mod_cast hright)
  have hXupper : X ≤ 2 * b := by
    simpa only [X] using vaughanTypeIIDoubleBlockProductScale_le_two_mul hmn
  have hpow : 0 ≤ (Real.log b) ^ d := Real.rpow_nonneg hlog d
  have hfirst : (Real.log b) ^ d * X ≤ |N| := by
    calc
      (Real.log b) ^ d * X ≤ (Real.log b) ^ d * (2 * b) :=
        mul_le_mul_of_nonneg_left hXupper hpow
      _ = 2 * (b : ℝ) * (Real.log b) ^ d := by ring
      _ ≤ |N| := hglobal
  have habs : |N| ≤ reciprocalPhaseScale N N 2 X * X :=
    abs_le_reciprocalPhaseScale_mul_scale N N 2 hXpos
  have hmul : (Real.log b) ^ d * X ≤
      reciprocalPhaseScale N N 2 X * X := hfirst.trans habs
  have hresult : (Real.log b) ^ d ≤ reciprocalPhaseScale N N 2 X :=
    le_of_mul_le_mul_right hmul hXpos
  simpa only [X] using hresult

/-- Survival past the outer tail cutoff turns one global cutoff-size bound
into the logarithmic lower bound required by every analytic block theorem. -/
theorem log_outerEndpoint_lower_of_not_cutoff
    {P c : ℝ} {b U : ℕ} {sk : ℕ × ℕ}
    (hUlower : 2 * Real.exp (c * Real.log P) ≤ (U : ℝ))
    (hnotCutoff : ¬2 * 2 ^ sk.1 ≤ U) :
    c * Real.log P ≤ Real.log
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) := by
  let K := dyadicShortIntervalLeftEndpoint (vaughanShortIntervalBudget b) sk
  have hUupperNat : U < 2 * 2 ^ sk.1 := Nat.lt_of_not_ge hnotCutoff
  have hUupper : (U : ℝ) < 2 * ((2 ^ sk.1 : ℕ) : ℝ) := by
    exact_mod_cast hUupperNat
  have hExpD : Real.exp (c * Real.log P) < ((2 ^ sk.1 : ℕ) : ℝ) := by
    nlinarith
  have hDKNat : 2 ^ sk.1 ≤ K := by
    unfold K dyadicShortIntervalLeftEndpoint
    omega
  have hDK : ((2 ^ sk.1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hDKNat
  have hExpK : Real.exp (c * Real.log P) < (K : ℝ) := hExpD.trans_le hDK
  have hKpos : (0 : ℝ) < K := (Real.exp_pos _).trans hExpK
  calc
    c * Real.log P = Real.log (Real.exp (c * Real.log P)) := by
      rw [Real.log_exp]
    _ ≤ Real.log (K : ℝ) :=
      (Real.strictMonoOn_log (Real.exp_pos _) hKpos hExpK).le

/-- The canonical natural-valued Vaughan tail cutoff, obtained by rounding
the source scale `B^(1/3)` down. -/
def vaughanSourceTailCutoff (B : ℕ) : ℕ :=
  ⌊(B : ℝ) ^ (1 / 3 : ℝ)⌋₊

/-- Elementary comparison between the discrete base-two logarithm and the
real logarithm, used to place the subdivision budget below a power scale. -/
theorem source_natLogTwo_cast_le_log_div {n : ℕ} (hn : 0 < n) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have hpowNat : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hpowReal : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log
    (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 n) hpowReal
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 (by
    simpa only [mul_comm] using hlog)

/-- On the source logarithmic range, the exact base-two family count is at
most three times the real logarithm. -/
theorem source_natLogTwo_add_one_cast_le_three_mul_log
    {n : ℕ} (hn : 0 < n) (hlog : 2 ≤ Real.log n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * Real.log n := by
  have hlogNonneg : 0 ≤ Real.log n := by linarith
  have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hnatlog := source_natLogTwo_cast_le_log_div hn
  have hdiv : Real.log n / Real.log 2 ≤ 2 * Real.log n := by
    apply (div_le_iff₀ hlogTwoPos).2
    have hfactor : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith
    calc
      Real.log n ≤ Real.log n * (2 * Real.log 2) :=
        le_mul_of_one_le_right hlogNonneg hfactor
      _ = 2 * Real.log n * Real.log 2 := by ring
  push_cast
  linarith

/-- Every fixed negative power eventually dominates any prescribed negative
logarithmic power.  This is the generic absorption used for the two fixed
power savings in the Type II ledger. -/
theorem eventually_rpow_neg_le_log_rpow_neg
    {c : ℝ} (hc : 0 < c) (E : ℝ) :
    ∀ᶠ x : ℝ in atTop, x ^ (-c) ≤ (Real.log x) ^ (-E) := by
  have hsmall := isLittleO_log_rpow_rpow_atTop E hc
  have hdom : ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ E ≤ x ^ c := by
    filter_upwards [hsmall.eventuallyLE,
      eventually_ge_atTop (Real.exp 1)] with x hx hxlarge
    have hxpos : 0 < x := (Real.exp_pos 1).trans_le hxlarge
    have hlogpos : 0 < Real.log x :=
      (Real.log_exp 1 ▸ show (0 : ℝ) < 1 by norm_num) |>.trans_le
        (Real.log_le_log (Real.exp_pos 1) hxlarge)
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlogpos.le _),
      abs_of_nonneg (Real.rpow_nonneg hxpos.le _)] using hx
  filter_upwards [hdom, eventually_ge_atTop (Real.exp 1)] with x hx hxlarge
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hxlarge
  have hlogpos : 0 < Real.log x :=
    (Real.log_exp 1 ▸ show (0 : ℝ) < 1 by norm_num) |>.trans_le
      (Real.log_le_log (Real.exp_pos 1) hxlarge)
  rw [Real.rpow_neg hxpos.le, Real.rpow_neg hlogpos.le]
  simpa only [one_div] using
    (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlogpos E) hx)

/-- Combine a negative real power and a natural-power denominator, while
allowing the logarithmic base to increase. -/
theorem rpow_neg_div_pow_le_rpow_neg
    {x y u E : ℝ} {n : ℕ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hE : 0 ≤ E)
    (hbudget : E ≤ u + n) :
    y ^ (-u) / y ^ n ≤ x ^ (-E) := by
  have hy : 1 ≤ y := hx.trans hxy
  have hypos : 0 < y := zero_lt_one.trans_le hy
  calc
    y ^ (-u) / y ^ n = y ^ (-(u + n)) := by
      rw [← Real.rpow_natCast, div_eq_mul_inv,
        ← Real.rpow_neg hypos.le, ← Real.rpow_add hypos]
      congr 1
      ring
    _ ≤ y ^ (-E) :=
      Real.rpow_le_rpow_of_exponent_le hy (by linarith)
    _ ≤ x ^ (-E) :=
      Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy
        (neg_nonpos.mpr hE)

/-- Mixed-base version used by the `(log P)^(-T)/(log b)^297` source term.
-/
theorem rpow_neg_div_larger_pow_le_rpow_neg
    {x y u E : ℝ} {n : ℕ}
    (hx : 1 ≤ x) (hxy : x ≤ y)
    (hbudget : E ≤ u + n) :
    x ^ (-u) / y ^ n ≤ x ^ (-E) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hypos : 0 < y := hxpos.trans_le hxy
  have hpow : x ^ n ≤ y ^ n := by gcongr
  have hden : 1 / y ^ n ≤ 1 / x ^ n :=
    one_div_le_one_div_of_le (pow_pos hxpos n) hpow
  calc
    x ^ (-u) / y ^ n ≤ x ^ (-u) / x ^ n := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hden)
        (Real.rpow_nonneg hxpos.le _)
    _ = x ^ (-(u + n)) := by
      rw [← Real.rpow_natCast, div_eq_mul_inv,
        ← Real.rpow_neg hxpos.le, ← Real.rpow_add hxpos]
      congr 1
      ring
    _ ≤ x ^ (-E) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)

/-- The cube-root Vaughan cutoff eventually dominates twice the complete
polylogarithmic short-interval subdivision budget. -/
theorem eventually_two_mul_vaughanShortIntervalBudget_le_vaughanSourceTailCutoff :
    ∀ᶠ B : ℕ in atTop,
      2 * vaughanShortIntervalBudget B ≤ vaughanSourceTailCutoff B := by
  let C : ℝ := 2 * 3 ^ (101 : ℕ)
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (101 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 3)).const_mul_left C
  have hdomReal : ∀ᶠ x : ℝ in atTop,
      C * Real.log x ^ (101 : ℝ) ≤ x ^ (1 / 3 : ℝ) := by
    filter_upwards [hsmall.eventuallyLE,
      eventually_ge_atTop (1 : ℝ)] with x hx hxOne
    have hxPos : 0 < x := zero_lt_one.trans_le hxOne
    have hlogNonneg : 0 ≤ Real.log x := Real.log_nonneg hxOne
    have hleftNonneg : 0 ≤ C * Real.log x ^ (101 : ℝ) := by
      dsimp [C]
      positivity
    have hrightNonneg : 0 ≤ x ^ (1 / 3 : ℝ) :=
      Real.rpow_nonneg hxPos.le _
    have hx' : |C * Real.log x ^ (101 : ℝ)| ≤ x ^ (1 / 3 : ℝ) := by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg hrightNonneg] using hx
    exact (le_abs_self _).trans hx'
  have hlogNat : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [tendsto_natCast_atTop_atTop.eventually hdomReal,
      hlogNat.eventually (eventually_ge_atTop (2 : ℝ)),
      eventually_ge_atTop (1 : ℕ)] with B hdom hlog hn
  have hnPos : 0 < B := by omega
  have hlogNonneg : 0 ≤ Real.log B := by linarith
  have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hnatlog := source_natLogTwo_cast_le_log_div hnPos
  have hdiv : Real.log B / Real.log 2 ≤ 2 * Real.log B := by
    apply (div_le_iff₀ hlogTwoPos).2
    have hfactor : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith
    calc
      Real.log B ≤ Real.log B * (2 * Real.log 2) :=
        le_mul_of_one_le_right hlogNonneg hfactor
      _ = 2 * Real.log B * Real.log 2 := by ring
  have hcount : ((Nat.log 2 B + 1 : ℕ) : ℝ) ≤ 3 * Real.log B := by
    push_cast
    linarith
  have hcountPow : (((Nat.log 2 B + 1 : ℕ) : ℝ) ^ (101 : ℕ)) ≤
      (3 * Real.log B) ^ (101 : ℕ) := by
    gcongr
  have hcast : ((2 * vaughanShortIntervalBudget B : ℕ) : ℝ) ≤
      (B : ℝ) ^ (1 / 3 : ℝ) := by
    have hdomNat : C * Real.log B ^ (101 : ℕ) ≤
        (B : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact hdom
    calc
      ((2 * vaughanShortIntervalBudget B : ℕ) : ℝ) =
          2 * (((Nat.log 2 B + 1 : ℕ) : ℝ) ^ (101 : ℕ)) := by
        norm_num only [vaughanShortIntervalBudget, Nat.cast_mul,
          Nat.cast_ofNat, Nat.cast_pow]
      _ ≤ 2 * (3 * Real.log B) ^ (101 : ℕ) := by gcongr
      _ = C * Real.log B ^ (101 : ℕ) := by
        dsimp [C]
        rw [mul_pow]
        ring
      _ ≤ (B : ℝ) ^ (1 / 3 : ℝ) := hdomNat
  exact Nat.le_floor hcast

/-- The floor loss in the cube-root cutoff is eventually negligible against
the strict exponent gap between `1/4` and `1/3`. -/
theorem eventually_two_mul_quarter_rpow_le_vaughanSourceTailCutoff :
    ∀ᶠ B : ℕ in atTop,
      2 * (B : ℝ) ^ (1 / 4 : ℝ) ≤ (vaughanSourceTailCutoff B : ℝ) := by
  have hsmall :=
    (GafniTao.rpow_isLittleO_rpow
      (by norm_num : (1 / 4 : ℝ) < 1 / 3)).const_mul_left (4 : ℝ)
  have hdomReal : ∀ᶠ x : ℝ in atTop,
      4 * x ^ (1 / 4 : ℝ) ≤ x ^ (1 / 3 : ℝ) := by
    filter_upwards [hsmall.eventuallyLE,
      eventually_ge_atTop (1 : ℝ)] with x hx hxOne
    have hquarterNonneg : 0 ≤ 4 * x ^ (1 / 4 : ℝ) := by positivity
    have hthirdNonneg : 0 ≤ x ^ (1 / 3 : ℝ) := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hquarterNonneg,
      abs_of_nonneg hthirdNonneg] using hx
  filter_upwards
    [tendsto_natCast_atTop_atTop.eventually hdomReal,
      eventually_ge_atTop (1 : ℕ)] with B hdom hB
  have hBReal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hquarterOne : (1 : ℝ) ≤ (B : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hBReal (by norm_num)
  have hfloor := Nat.lt_floor_add_one ((B : ℝ) ^ (1 / 3 : ℝ))
  have hfloorReal : (B : ℝ) ^ (1 / 3 : ℝ) <
      (vaughanSourceTailCutoff B : ℝ) + 1 := by
    simpa only [vaughanSourceTailCutoff] using hfloor
  nlinarith

/-- A named dyadic short block contains no more points than its defining
quotient-block length. -/
theorem card_dyadicShortIntervalIndexedBlock_le_length
    {L : ℕ} (hL : 0 < L) (sk : ℕ × ℕ) :
    (dyadicShortIntervalIndexedBlock L sk).card ≤
      dyadicShortIntervalLength (2 ^ sk.1) L := by
  simpa only [dyadicShortIntervalIndexedBlock] using
    card_shortIntervalBlock_le (2 ^ sk.1) (2 * 2 ^ sk.1)
      (dyadicShortIntervalLength (2 ^ sk.1) L) sk.2
      (dyadicShortIntervalLength_pos (pow_pos (by omega) sk.1) hL)

/-- Every large canonical block length is bounded by the global source scale
divided by the literal hundredth logarithmic power. -/
theorem vaughanShortIntervalLength_cast_le_global_realLog
    {b : ℕ} {sk : ℕ × ℕ} (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hsk : sk ∈ vaughanShortIntervalIndexBox b)
    (hlarge : (vaughanShortIntervalBudget b : ℝ) ≤ (2 ^ sk.1 : ℕ)) :
    (dyadicShortIntervalLength (2 ^ sk.1)
        (vaughanShortIntervalBudget b) : ℝ) ≤
      (b : ℝ) / (Real.log b) ^ 100 := by
  have hslt : sk.1 < Nat.log 2 b + 1 := by
    exact Finset.mem_range.mp (Finset.mem_product.mp hsk).1
  have hsle : sk.1 ≤ Nat.log 2 b := by omega
  have hDleNat : 2 ^ sk.1 ≤ b := by
    calc
      2 ^ sk.1 ≤ 2 ^ Nat.log 2 b :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hsle
      _ ≤ b := Nat.pow_log_le_self 2 hb.ne'
  have hDle : ((2 ^ sk.1 : ℕ) : ℝ) ≤ b := by exact_mod_cast hDleNat
  have hwidth := vaughanShortIntervalLength_cast_le_realLog hb hlog hlarge
  exact hwidth.trans <| by
    exact div_le_div_of_nonneg_right hDle (by positivity)

/-- The component-count logarithm of a large canonical outer block costs at
most twice the global source logarithm. -/
theorem one_add_log_vaughanShortIntervalLength_le_two_mul_log
    {b : ℕ} {sk : ℕ × ℕ} (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hsk : sk ∈ vaughanShortIntervalIndexBox b)
    (hlarge : (vaughanShortIntervalBudget b : ℝ) ≤ (2 ^ sk.1 : ℕ)) :
    1 + Real.log (dyadicShortIntervalLength (2 ^ sk.1)
        (vaughanShortIntervalBudget b) : ℝ) ≤ 2 * Real.log b := by
  have hwidth := vaughanShortIntervalLength_cast_le_global_realLog
    hb hlog hsk hlarge
  have hlogPowPos : 0 < (Real.log b) ^ 100 := by positivity
  have hdivLe : (b : ℝ) / (Real.log b) ^ 100 ≤ b := by
    apply (div_le_iff₀ hlogPowPos).2
    have hpowOne : (1 : ℝ) ≤ (Real.log b) ^ 100 := by
      exact one_le_pow₀ (by linarith)
    nlinarith [mul_nonneg (Nat.cast_nonneg b) (sub_nonneg.mpr hpowOne)]
  have hqposNat : 0 < dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget b) :=
    dyadicShortIntervalLength_pos (pow_pos (by omega) sk.1)
      (vaughanShortIntervalBudget_pos b)
  have hqpos : (0 : ℝ) < dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget b) := by exact_mod_cast hqposNat
  have hqle : (dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget b) : ℝ) ≤ b := hwidth.trans hdivLe
  have hlogq : Real.log (dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget b) : ℝ) ≤ Real.log b :=
    Real.log_le_log hqpos hqle
  linarith

/-- On the source range, replacing `log (2b)` by `2 log b` loses only the
literal factor two. -/
theorem realLog_two_mul_nat_le_two_mul_log
    {b : ℕ} (hb : 0 < b) (hlog : 2 ≤ Real.log b) :
    Real.log (2 * b) ≤ 2 * Real.log b := by
  have hbne : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hbne]
  nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Squared logarithmic version of `realLog_two_mul_nat_le_two_mul_log`. -/
theorem realLog_two_mul_nat_sq_le_four_mul_log_sq
    {b : ℕ} (hb : 0 < b) (hlog : 2 ≤ Real.log b) :
    (Real.log (2 * b)) ^ 2 ≤ 4 * (Real.log b) ^ 2 := by
  have hupper := realLog_two_mul_nat_le_two_mul_log hb hlog
  have hbne : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hlogTwoB : 0 ≤ Real.log (2 * b) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hbne]
    have hlogTwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  nlinarith [sq_nonneg (2 * Real.log b - Real.log (2 * b))]

/-- Survival past the canonical outer cutoff forces the literal outer block
endpoint above `b^(1/4)`. -/
theorem quarter_rpow_lt_outerEndpoint_of_not_vaughanSourceTailCutoff
    {b : ℕ} {sk : ℕ × ℕ}
    (hquarter : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ))
    (hnotCutoff : ¬2 * 2 ^ sk.1 ≤ vaughanSourceTailCutoff b) :
    (b : ℝ) ^ (1 / 4 : ℝ) <
      (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) := by
  have hcutNat : vaughanSourceTailCutoff b < 2 * 2 ^ sk.1 :=
    Nat.lt_of_not_ge hnotCutoff
  have hcut : (vaughanSourceTailCutoff b : ℝ) <
      2 * ((2 ^ sk.1 : ℕ) : ℝ) := by exact_mod_cast hcutNat
  have hquarterD : (b : ℝ) ^ (1 / 4 : ℝ) < (2 ^ sk.1 : ℕ) := by
    nlinarith
  have hDKNat : 2 ^ sk.1 ≤ dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk := by
    unfold dyadicShortIntervalLeftEndpoint
    omega
  have hDK : ((2 ^ sk.1 : ℕ) : ℝ) ≤
      (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) := by exact_mod_cast hDKNat
  exact hquarterD.trans_le hDK

/-- Survival past the canonical inner cutoff forces the doubled inner dyadic
scale above `2*b^(1/4)`. -/
theorem two_mul_quarter_rpow_lt_innerScale_of_not_vaughanSourceTailCutoff
    {b : ℕ} {tl : ℕ × ℕ}
    (hquarter : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ))
    (hnotCutoff : ¬2 * 2 ^ tl.1 ≤ vaughanSourceTailCutoff b) :
    2 * (b : ℝ) ^ (1 / 4 : ℝ) < ((2 * 2 ^ tl.1 : ℕ) : ℝ) := by
  have hcutNat : vaughanSourceTailCutoff b < 2 * 2 ^ tl.1 :=
    Nat.lt_of_not_ge hnotCutoff
  have hcut : (vaughanSourceTailCutoff b : ℝ) <
      ((2 * 2 ^ tl.1 : ℕ) : ℝ) := by exact_mod_cast hcutNat
  exact hquarter.trans_lt hcut

/-- Survival past the inner cube-root cutoff gives the diagonal dyadic cubic
monomial an additional quarter-power saving. -/
theorem vaughanTypeIIDoubleBlockOuterSquareInner_mul_quarter_rpow_le_sq
    {a b : ℕ} {sk tl : ℕ × ℕ} {mn : ℕ × ℕ}
    (hquarter : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ))
    (hnotCutoff : ¬2 * 2 ^ tl.1 ≤ vaughanSourceTailCutoff b)
    (hmn : mn ∈ vaughanTypeIIDoubleBlockProductSupport a b sk tl) :
    ((2 ^ sk.1 : ℕ) : ℝ) * ((2 ^ sk.1 : ℕ) : ℝ) *
        ((2 ^ tl.1 : ℕ) : ℝ) * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (b : ℝ) ^ 2 := by
  have hinner :=
    two_mul_quarter_rpow_lt_innerScale_of_not_vaughanSourceTailCutoff
      hquarter hnotCutoff
  norm_num [Nat.cast_mul, Nat.cast_pow] at hinner
  have hinner' : (b : ℝ) ^ (1 / 4 : ℝ) <
      ((2 ^ tl.1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hinner
  have hquarterInner : (b : ℝ) ^ (1 / 4 : ℝ) ≤
      ((2 ^ tl.1 : ℕ) : ℝ) := hinner'.le
  have hDE := vaughanTypeIIDoubleBlockDyadicProduct_le hmn
  have hDR : ((2 ^ sk.1 : ℕ) : ℝ) * (b : ℝ) ^ (1 / 4 : ℝ) ≤ b :=
    (mul_le_mul_of_nonneg_left hquarterInner (by positivity)).trans hDE
  calc
    ((2 ^ sk.1 : ℕ) : ℝ) * ((2 ^ sk.1 : ℕ) : ℝ) *
        ((2 ^ tl.1 : ℕ) : ℝ) * (b : ℝ) ^ (1 / 4 : ℝ) =
        (((2 ^ sk.1 : ℕ) : ℝ) * ((2 ^ tl.1 : ℕ) : ℝ)) *
          (((2 ^ sk.1 : ℕ) : ℝ) * (b : ℝ) ^ (1 / 4 : ℝ)) := by ring
    _ ≤ (b : ℝ) * b :=
      mul_le_mul hDE hDR (by positivity) (by positivity)
    _ = (b : ℝ) ^ 2 := by ring

/-- Divided form of the quarter-power diagonal saving. -/
theorem vaughanTypeIIDoubleBlockOuterSquareInner_le_sq_div_quarter_rpow
    {a b : ℕ} {sk tl : ℕ × ℕ} {mn : ℕ × ℕ}
    (hb : 0 < b)
    (hquarter : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ))
    (hnotCutoff : ¬2 * 2 ^ tl.1 ≤ vaughanSourceTailCutoff b)
    (hmn : mn ∈ vaughanTypeIIDoubleBlockProductSupport a b sk tl) :
    ((2 ^ sk.1 : ℕ) : ℝ) * ((2 ^ sk.1 : ℕ) : ℝ) *
        ((2 ^ tl.1 : ℕ) : ℝ) ≤
      (b : ℝ) ^ 2 / (b : ℝ) ^ (1 / 4 : ℝ) := by
  have hpowPos : 0 < (b : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hb) _
  apply (le_div_iff₀ hpowPos).2
  simpa only [mul_assoc] using
    vaughanTypeIIDoubleBlockOuterSquareInner_mul_quarter_rpow_le_sq
      hquarter hnotCutoff hmn

/-- The two derivative orders needed by the intrinsic quadratic low-scale
branch.  The high-scale Vinogradov callback constructs its own complete order
range, so no larger external order family is needed. -/
def vaughanTypeIICanonicalOrders : Finset ℕ := {5, 6}

@[simp] theorem five_mem_vaughanTypeIICanonicalOrders :
    5 ∈ vaughanTypeIICanonicalOrders := by
  simp [vaughanTypeIICanonicalOrders]

@[simp] theorem six_mem_vaughanTypeIICanonicalOrders :
    6 ∈ vaughanTypeIICanonicalOrders := by
  simp [vaughanTypeIICanonicalOrders]

@[simp] theorem card_vaughanTypeIICanonicalOrders :
    vaughanTypeIICanonicalOrders.card = 2 := by
  simp [vaughanTypeIICanonicalOrders]

/-- The explicit source majorant used to sum every Type II Vaughan double
block: zero when either tail coefficient lies below its cutoff budget, and the
mixed Weyl--Vinogradov expression for a large--large pair. -/
noncomputable def vaughanTypeIISourceBlockMajorant
    (P : ℝ) (a b U V : ℕ) (N : ℝ) (orders : Finset ℕ)
    (sk tl : ℕ × ℕ) (T : ℝ) : ℝ :=
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget b)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget b)
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget b) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  let F := reciprocalPhaseScale N N 2 (K * B)
  let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  if 2 * 2 ^ sk.1 ≤ U then 0
  else if 2 * 2 ^ tl.1 ≤ V then 0
  else if vaughanTypeIIDoubleBlockProductSupport a b sk tl = ∅ then 0
  else
    ((dyadicShortIntervalIndexedBlock
        (vaughanShortIntervalBudget b) sk).card : ℝ) *
      ((qouter : ℝ) * (qinner : ℝ) * (Real.log (2 * b)) ^ 2 +
        (Real.log (2 * b)) ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B *
                  F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) +
              3 * (Real.log P) ^ (-T))))))

/-- The explicit source block majorant with both canonical cube-root cutoffs
and the minimal derivative-order family already substituted. -/
noncomputable def vaughanTypeIICanonicalSourceBlockMajorant
    (P : ℝ) (a b : ℕ) (N : ℝ) (sk tl : ℕ × ℕ) (T : ℝ) : ℝ :=
  vaughanTypeIISourceBlockMajorant P a b
    (vaughanSourceTailCutoff b) (vaughanSourceTailCutoff b) N
    vaughanTypeIICanonicalOrders sk tl T

/-- Absolute scalar left after substituting the two-element canonical order
set and bounding `1 + log qouter` by `2 log b`. -/
def vaughanTypeIICanonicalQConstant : ℝ :=
  913 * (960 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
    (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1))

/-- First geometric compression of the canonical Type II block majorant.  It
replaces the outer block cardinality by its length and the critical-component
factor by one absolute constant times `log b * K`; the remaining terms retain
their exact analytic scales. -/
noncomputable def vaughanTypeIICanonicalGeometricBlockMajorant
    (P : ℝ) (b : ℕ) (N : ℝ) (sk tl : ℕ × ℕ) (T : ℝ) : ℝ :=
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget b)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget b)
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget b) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  let F := reciprocalPhaseScale N N 2 (K * B)
  (qouter : ℝ) *
    ((qouter : ℝ) * (qinner : ℝ) * (Real.log (2 * b)) ^ 2 +
      (Real.log (2 * b)) ^ 2 * (qinner : ℝ) *
        (vaughanTypeIICanonicalQConstant * Real.log b * K *
          (4 * (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
            (1 - (1 / 1024 : ℝ))) * B *
              F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) +
              3 * (Real.log P) ^ (-T)))))

/-- Uniform-length form of the canonical geometric Type II block majorant.
Both short-block lengths are replaced by the common source bound
`b / (log b)^100`, while the exact endpoint and phase scales are retained. -/
noncomputable def vaughanTypeIICanonicalUniformGeometricBlockMajorant
    (P : ℝ) (b : ℕ) (N : ℝ) (sk tl : ℕ × ℕ) (T : ℝ) : ℝ :=
  let q : ℝ := b / (Real.log b) ^ 100
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget b) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  let F := reciprocalPhaseScale N N 2 (K * B)
  q *
    (q * q * (Real.log (2 * b)) ^ 2 +
      (Real.log (2 * b)) ^ 2 * q *
        (vaughanTypeIICanonicalQConstant * Real.log b * K *
          (4 * (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
            (1 - (1 / 1024 : ℝ))) * B *
              F ^ (-(1 / 1024 : ℝ)))) +
            q * ((1 / K) ^ (1 / 1024 : ℝ) +
              3 * (Real.log P) ^ (-T)))))

/-- Log-compressed form of the canonical uniform geometric majorant, with
`(log (2b))²` replaced by `4(log b)²`. -/
noncomputable def vaughanTypeIICanonicalLogCompressedBlockMajorant
    (P : ℝ) (b : ℕ) (N : ℝ) (sk tl : ℕ × ℕ) (T : ℝ) : ℝ :=
  let q : ℝ := b / (Real.log b) ^ 100
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget b) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  let F := reciprocalPhaseScale N N 2 (K * B)
  4 * q * (Real.log b) ^ 2 *
    (q * q + q *
      (vaughanTypeIICanonicalQConstant * Real.log b * K *
        (4 * (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
          (1 - (1 / 1024 : ℝ))) * B *
            F ^ (-(1 / 1024 : ℝ)))) +
          q * ((1 / K) ^ (1 / 1024 : ℝ) +
            3 * (Real.log P) ^ (-T)))))

/-- Source-critical dyadic geometric majorant.  The outer and inner widths are
kept at their own dyadic scales divided by `(log b)^100`, preserving the
product geometry needed for the final `b²` block bound. -/
noncomputable def vaughanTypeIICanonicalDyadicGeometricBlockMajorant
    (P : ℝ) (b : ℕ) (N : ℝ) (sk tl : ℕ × ℕ) (T : ℝ) : ℝ :=
  let qouter : ℝ := (2 ^ sk.1 : ℕ) / (Real.log b) ^ 100
  let qinner : ℝ := (2 ^ tl.1 : ℕ) / (Real.log b) ^ 100
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget b) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  let F := reciprocalPhaseScale N N 2 (K * B)
  4 * qouter * (Real.log b) ^ 2 *
    (qouter * qinner + qinner *
      (vaughanTypeIICanonicalQConstant * Real.log b * K *
        (4 * (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
          (1 - (1 / 1024 : ℝ))) * B *
            F ^ (-(1 / 1024 : ℝ)))) +
          qinner * ((1 / K) ^ (1 / 1024 : ℝ) +
            3 * (Real.log P) ^ (-T)))))

/-- Product-compressed Type II block majorant.  Product support has replaced
both dyadic cubic monomials by `b²`; only the phase and endpoint decay factors
remain block-dependent. -/
noncomputable def vaughanTypeIICanonicalProductCompressedBlockMajorant
    (P : ℝ) (b : ℕ) (N : ℝ) (sk tl : ℕ × ℕ) (T : ℝ) : ℝ :=
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget b) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  let F := reciprocalPhaseScale N N 2 (K * B)
  (b : ℝ) ^ 2 *
    (4 / (Real.log b) ^ 298 +
      64 * vaughanTypeIICanonicalQConstant *
          (2 ^ (1 - (1 / 1024 : ℝ)) / (1 - (1 / 1024 : ℝ))) *
          F ^ (-(1 / 1024 : ℝ)) / (Real.log b) ^ 197 +
      4 * vaughanTypeIICanonicalQConstant *
          ((1 / K) ^ (1 / 1024 : ℝ) +
            3 * (Real.log P) ^ (-T)) / (Real.log b) ^ 297)

/-- Product-compressed block majorant with the diagonal term retaining the
quarter-power saving supplied by the canonical inner cutoff. -/
noncomputable def vaughanTypeIICanonicalPowerSavedBlockMajorant
    (P : ℝ) (b : ℕ) (N : ℝ) (sk tl : ℕ × ℕ) (T : ℝ) : ℝ :=
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget b) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  let F := reciprocalPhaseScale N N 2 (K * B)
  (4 / (Real.log b) ^ 298) *
      ((b : ℝ) ^ 2 / (b : ℝ) ^ (1 / 4 : ℝ)) +
    (b : ℝ) ^ 2 *
      (64 * vaughanTypeIICanonicalQConstant *
          (2 ^ (1 - (1 / 1024 : ℝ)) / (1 - (1 / 1024 : ℝ))) *
          F ^ (-(1 / 1024 : ℝ)) / (Real.log b) ^ 197 +
        4 * vaughanTypeIICanonicalQConstant *
          ((1 / K) ^ (1 / 1024 : ℝ) +
            3 * (Real.log P) ^ (-T)) / (Real.log b) ^ 297)

/-- Block-independent decay form of the canonical Type II majorant.  The
phase scale is replaced by its global logarithmic lower bound and the outer
endpoint by the canonical quarter-power lower bound. -/
noncomputable def vaughanTypeIICanonicalDecayAbsorbedBlockMajorant
    (P : ℝ) (b : ℕ) (d T : ℝ) : ℝ :=
  (4 / (Real.log b) ^ 298) *
      ((b : ℝ) ^ 2 / (b : ℝ) ^ (1 / 4 : ℝ)) +
    (b : ℝ) ^ 2 *
      (64 * vaughanTypeIICanonicalQConstant *
          (2 ^ (1 - (1 / 1024 : ℝ)) / (1 - (1 / 1024 : ℝ))) *
          ((Real.log b) ^ d) ^ (-(1 / 1024 : ℝ)) /
            (Real.log b) ^ 197 +
        4 * vaughanTypeIICanonicalQConstant *
          (((1 : ℝ) / (b : ℝ) ^ (1 / 4 : ℝ)) ^ (1 / 1024 : ℝ) +
            3 * (Real.log P) ^ (-T)) / (Real.log b) ^ 297)

/-- The decay-absorbed block ledger with all nested real powers flattened.
Its three savings are respectively a fixed power of `b`, the chosen phase
logarithmic power, and the fixed endpoint power `b⁻¹/⁴⁰⁹⁶`. -/
noncomputable def vaughanTypeIICanonicalExplicitDecayBlockMajorant
    (P : ℝ) (b : ℕ) (d T : ℝ) : ℝ :=
  (4 / (Real.log b) ^ 298) * (b : ℝ) ^ (7 / 4 : ℝ) +
    (b : ℝ) ^ 2 *
      (64 * vaughanTypeIICanonicalQConstant *
          (2 ^ (1 - (1 / 1024 : ℝ)) / (1 - (1 / 1024 : ℝ))) *
          (Real.log b) ^ (-d / 1024) / (Real.log b) ^ 197 +
        4 * vaughanTypeIICanonicalQConstant *
          ((b : ℝ) ^ (-(1 / 4096 : ℝ)) +
            3 * (Real.log P) ^ (-T)) / (Real.log b) ^ 297)

/-- Absolute coefficient obtained after bounding each of the four normalized
decay terms by the same target logarithmic power. -/
noncomputable def vaughanTypeIICanonicalDecayConstant : ℝ :=
  4 +
    64 * vaughanTypeIICanonicalQConstant *
      (2 ^ (1 - (1 / 1024 : ℝ)) / (1 - (1 / 1024 : ℝ))) +
    16 * vaughanTypeIICanonicalQConstant

/-- The absolute coefficient after square-root extraction and the complete
canonical double-family loss. -/
noncomputable def vaughanTypeIICanonicalFamilyDecayConstant : ℝ :=
  6 ^ (204 : ℕ) * Real.sqrt vaughanTypeIICanonicalDecayConstant

/-- Explicit phase logarithmic exponent sufficient for a target Type II
saving `(log P)⁻ˢ`. -/
def vaughanTypeIILogSavingPhaseExponent (S : ℝ) : ℝ :=
  2048 * S + 216064

/-- Explicit source-error exponent sufficient for the same target saving. -/
def vaughanTypeIILogSavingSourceExponent (S : ℝ) : ℝ :=
  2 * S + 111

/-- Vinogradov parameter exponent that makes the source-error budget exact. -/
def vaughanTypeIILogSavingVinogradovExponent (S : ℝ) : ℝ :=
  (2 * S + 113) / 3

/-- Flatten the phase logarithmic power in the decay ledger. -/
theorem log_rpow_rpow_neg_one_over_1024
    {b : ℕ} {d : ℝ} (hlog : 2 ≤ Real.log b) :
    ((Real.log b) ^ d) ^ (-(1 / 1024 : ℝ)) =
      (Real.log b) ^ (-d / 1024) := by
  rw [← Real.rpow_mul (by linarith : 0 ≤ Real.log b)]
  congr 1
  ring

/-- Flatten the quarter-power endpoint decay. -/
theorem one_div_quarter_rpow_rpow_one_over_1024
    {b : ℕ} (hb : 0 < b) :
    (((1 : ℝ) / (b : ℝ) ^ (1 / 4 : ℝ)) ^ (1 / 1024 : ℝ)) =
      (b : ℝ) ^ (-(1 / 4096 : ℝ)) := by
  have hb0 : (0 : ℝ) ≤ b := by positivity
  rw [one_div, ← Real.rpow_neg hb0, ← Real.rpow_mul hb0]
  congr 1
  ring

/-- Rewrite the diagonal quarter-power saving as the exponent `7/4`. -/
theorem sq_div_quarter_rpow_eq_seven_quarters
    {b : ℕ} (hb : 0 < b) :
    (b : ℝ) ^ 2 / (b : ℝ) ^ (1 / 4 : ℝ) =
      (b : ℝ) ^ (7 / 4 : ℝ) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  rw [← Real.rpow_natCast, ← Real.rpow_sub hbpos]
  congr 1
  norm_num

/-- The absorbed and flattened decay ledgers agree exactly. -/
theorem vaughanTypeIICanonicalDecayAbsorbedBlockMajorant_eq_explicit
    {P d T : ℝ} {b : ℕ} (hb : 0 < b) (hlog : 2 ≤ Real.log b) :
    vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T =
      vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T := by
  unfold vaughanTypeIICanonicalDecayAbsorbedBlockMajorant
    vaughanTypeIICanonicalExplicitDecayBlockMajorant
  rw [log_rpow_rpow_neg_one_over_1024 hlog,
    one_div_quarter_rpow_rpow_one_over_1024 hb,
    sq_div_quarter_rpow_eq_seven_quarters hb]

/-- Once the phase exponents cover a target squared logarithmic exponent
`E`, the explicit Type II block ledger is uniformly at most
`C * b² * (log P)⁻ᴱ`.  Fixed powers of the source scale absorb the diagonal
and endpoint terms eventually. -/
theorem eventually_vaughanTypeIICanonicalExplicitDecayBlockMajorant_le
    {d T E : ℝ} (hE : 0 ≤ E)
    (hd : E ≤ d / 1024 + 197) (hT : E ≤ T + 297) :
    ∀ᶠ P : ℝ in atTop, ∀ b : ℕ,
      P ≤ (b : ℝ) →
      vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T ≤
        vaughanTypeIICanonicalDecayConstant * (b : ℝ) ^ 2 *
          (Real.log P) ^ (-E) := by
  have hquarter := eventually_rpow_neg_le_log_rpow_neg
    (by norm_num : (0 : ℝ) < 1 / 4) E
  have hendpoint := eventually_rpow_neg_le_log_rpow_neg
    (by norm_num : (0 : ℝ) < 1 / 4096) E
  filter_upwards [hquarter, hendpoint,
      eventually_ge_atTop (Real.exp 1)] with P hquarterP hendpointP hPlarge
  intro b hPb
  have hPpos : 0 < P := (Real.exp_pos 1).trans_le hPlarge
  have hbpos : (0 : ℝ) < b := hPpos.trans_le hPb
  have hlogPone : 1 ≤ Real.log P :=
    (Real.le_log_iff_exp_le hPpos).2 hPlarge
  have hlogPb : Real.log P ≤ Real.log b :=
    Real.log_le_log hPpos hPb
  have hlogbone : 1 ≤ Real.log b := hlogPone.trans hlogPb
  have hdiagDecay :
      (b : ℝ) ^ (-(1 / 4 : ℝ)) / (Real.log b) ^ 298 ≤
        (Real.log P) ^ (-E) := by
    have hbase : (b : ℝ) ^ (-(1 / 4 : ℝ)) ≤ P ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hPpos hPb (by norm_num)
    exact (div_le_self (Real.rpow_nonneg hbpos.le _)
      (one_le_pow₀ hlogbone)).trans (hbase.trans hquarterP)
  have hphaseDecay :
      (Real.log b) ^ (-d / 1024) / (Real.log b) ^ 197 ≤
        (Real.log P) ^ (-E) := by
    have h := rpow_neg_div_pow_le_rpow_neg (u := d / 1024) (n := 197)
      hlogPone hlogPb hE (by linarith)
    simpa only [neg_div] using h
  have hendpointDecay :
      (b : ℝ) ^ (-(1 / 4096 : ℝ)) / (Real.log b) ^ 297 ≤
        (Real.log P) ^ (-E) := by
    have hbase : (b : ℝ) ^ (-(1 / 4096 : ℝ)) ≤
        P ^ (-(1 / 4096 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hPpos hPb (by norm_num)
    exact (div_le_self (Real.rpow_nonneg hbpos.le _)
      (one_le_pow₀ hlogbone)).trans (hbase.trans hendpointP)
  have hsourceDecay :
      (Real.log P) ^ (-T) / (Real.log b) ^ 297 ≤
        (Real.log P) ^ (-E) :=
    rpow_neg_div_larger_pow_le_rpow_neg hlogPone hlogPb hT
  have hbidentity : (b : ℝ) ^ (7 / 4 : ℝ) =
      (b : ℝ) ^ 2 * (b : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hbpos]
    congr 1
    norm_num
  have hC0 : 0 ≤ vaughanTypeIICanonicalQConstant := by
    unfold vaughanTypeIICanonicalQConstant
    positivity
  have hc0 : 0 ≤
      (2 : ℝ) ^ (1 - (1 / 1024 : ℝ)) /
        (1 - (1 / 1024 : ℝ)) := by positivity
  have hphaseCoeff0 : 0 ≤
      64 * vaughanTypeIICanonicalQConstant *
        (2 ^ (1 - (1 / 1024 : ℝ)) /
          (1 - (1 / 1024 : ℝ))) := by positivity
  have hdiagTerm :
      4 / (Real.log b) ^ 298 *
          ((b : ℝ) ^ 2 * (b : ℝ) ^ (-(1 / 4 : ℝ))) ≤
        (b : ℝ) ^ 2 * (4 * (Real.log P) ^ (-E)) := by
    calc
      4 / (Real.log b) ^ 298 *
          ((b : ℝ) ^ 2 * (b : ℝ) ^ (-(1 / 4 : ℝ))) =
          4 * (b : ℝ) ^ 2 *
            ((b : ℝ) ^ (-(1 / 4 : ℝ)) / (Real.log b) ^ 298) := by ring
      _ ≤ 4 * (b : ℝ) ^ 2 * (Real.log P) ^ (-E) := by gcongr
      _ = (b : ℝ) ^ 2 * (4 * (Real.log P) ^ (-E)) := by ring
  have hphaseTerm :
      64 * vaughanTypeIICanonicalQConstant *
          (2 ^ (1 - (1 / 1024 : ℝ)) /
            (1 - (1 / 1024 : ℝ))) *
          (Real.log b) ^ (-d / 1024) / (Real.log b) ^ 197 ≤
        64 * vaughanTypeIICanonicalQConstant *
          (2 ^ (1 - (1 / 1024 : ℝ)) /
            (1 - (1 / 1024 : ℝ))) * (Real.log P) ^ (-E) := by
    simpa only [mul_div_assoc] using
      (mul_le_mul_of_nonneg_left hphaseDecay hphaseCoeff0)
  have hendpointInner :
      ((b : ℝ) ^ (-(1 / 4096 : ℝ)) +
          3 * (Real.log P) ^ (-T)) / (Real.log b) ^ 297 ≤
        (Real.log P) ^ (-E) + 3 * (Real.log P) ^ (-E) := by
    calc
      ((b : ℝ) ^ (-(1 / 4096 : ℝ)) +
          3 * (Real.log P) ^ (-T)) / (Real.log b) ^ 297 =
          (b : ℝ) ^ (-(1 / 4096 : ℝ)) / (Real.log b) ^ 297 +
            3 * ((Real.log P) ^ (-T) / (Real.log b) ^ 297) := by ring
      _ ≤ (Real.log P) ^ (-E) + 3 * (Real.log P) ^ (-E) := by gcongr
  have hendpointTerm :
      4 * vaughanTypeIICanonicalQConstant *
          ((b : ℝ) ^ (-(1 / 4096 : ℝ)) +
            3 * (Real.log P) ^ (-T)) / (Real.log b) ^ 297 ≤
        4 * vaughanTypeIICanonicalQConstant *
          ((Real.log P) ^ (-E) + 3 * (Real.log P) ^ (-E)) := by
    simpa only [mul_div_assoc] using
      (mul_le_mul_of_nonneg_left hendpointInner (by positivity :
        0 ≤ 4 * vaughanTypeIICanonicalQConstant))
  unfold vaughanTypeIICanonicalExplicitDecayBlockMajorant
    vaughanTypeIICanonicalDecayConstant
  rw [hbidentity]
  calc
    4 / (Real.log b) ^ 298 *
          ((b : ℝ) ^ 2 * (b : ℝ) ^ (-(1 / 4 : ℝ))) +
        (b : ℝ) ^ 2 *
          (64 * vaughanTypeIICanonicalQConstant *
              (2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) *
              (Real.log b) ^ (-d / 1024) / (Real.log b) ^ 197 +
            4 * vaughanTypeIICanonicalQConstant *
              ((b : ℝ) ^ (-(1 / 4096 : ℝ)) +
                3 * (Real.log P) ^ (-T)) / (Real.log b) ^ 297) ≤
        (b : ℝ) ^ 2 *
          (4 * (Real.log P) ^ (-E) +
            64 * vaughanTypeIICanonicalQConstant *
              (2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * (Real.log P) ^ (-E) +
            16 * vaughanTypeIICanonicalQConstant *
              (Real.log P) ^ (-E)) := by
      calc
        4 / (Real.log b) ^ 298 *
              ((b : ℝ) ^ 2 * (b : ℝ) ^ (-(1 / 4 : ℝ))) +
            (b : ℝ) ^ 2 *
              (64 * vaughanTypeIICanonicalQConstant *
                  (2 ^ (1 - (1 / 1024 : ℝ)) /
                    (1 - (1 / 1024 : ℝ))) *
                  (Real.log b) ^ (-d / 1024) / (Real.log b) ^ 197 +
                4 * vaughanTypeIICanonicalQConstant *
                  ((b : ℝ) ^ (-(1 / 4096 : ℝ)) +
                    3 * (Real.log P) ^ (-T)) / (Real.log b) ^ 297) ≤
            (b : ℝ) ^ 2 * (4 * (Real.log P) ^ (-E)) +
              (b : ℝ) ^ 2 *
                (64 * vaughanTypeIICanonicalQConstant *
                    (2 ^ (1 - (1 / 1024 : ℝ)) /
                      (1 - (1 / 1024 : ℝ))) * (Real.log P) ^ (-E) +
                  4 * vaughanTypeIICanonicalQConstant *
                    ((Real.log P) ^ (-E) +
                      3 * (Real.log P) ^ (-E))) := by
          exact add_le_add hdiagTerm
            (mul_le_mul_of_nonneg_left
              (add_le_add hphaseTerm hendpointTerm) (by positivity))
        _ = (b : ℝ) ^ 2 *
            (4 * (Real.log P) ^ (-E) +
              64 * vaughanTypeIICanonicalQConstant *
                (2 ^ (1 - (1 / 1024 : ℝ)) /
                  (1 - (1 / 1024 : ℝ))) * (Real.log P) ^ (-E) +
              16 * vaughanTypeIICanonicalQConstant *
                (Real.log P) ^ (-E)) := by ring
    _ = (4 +
          64 * vaughanTypeIICanonicalQConstant *
            (2 ^ (1 - (1 / 1024 : ℝ)) /
              (1 - (1 / 1024 : ℝ))) +
          16 * vaughanTypeIICanonicalQConstant) *
        (b : ℝ) ^ 2 * (Real.log P) ^ (-E) := by ring

/-- Extract the square root of the common block envelope and cancel the exact
`204`-power family loss against `E = 2A+408`. -/
theorem three_mul_log_pow_mul_sqrt_decay_le
    {P A E C : ℝ} {b : ℕ}
    (hlogP : 1 ≤ Real.log P)
    (hlogb : Real.log b ≤ 2 * Real.log P)
    (hC : 0 ≤ C) (hE : E = 2 * A + 408) :
    (3 * Real.log b) ^ 204 *
        Real.sqrt (C * (b : ℝ) ^ 2 * (Real.log P) ^ (-E)) ≤
      6 ^ (204 : ℕ) * Real.sqrt C * (b : ℝ) *
        (Real.log P) ^ (-A) := by
  have hlogPpos : 0 < Real.log P := zero_lt_one.trans_le hlogP
  have hfamily : (3 * Real.log b) ^ (204 : ℕ) ≤
      (6 * Real.log P) ^ (204 : ℕ) := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 204
  calc
    (3 * Real.log b) ^ 204 *
        Real.sqrt (C * (b : ℝ) ^ 2 * (Real.log P) ^ (-E)) ≤
      (6 * Real.log P) ^ 204 *
        Real.sqrt (C * (b : ℝ) ^ 2 * (Real.log P) ^ (-E)) := by
          gcongr
    _ = 6 ^ (204 : ℕ) * Real.sqrt C * (b : ℝ) *
        (Real.log P) ^ (-A) := by
      rw [show C * (b : ℝ) ^ 2 * (Real.log P) ^ (-E) =
        C * ((b : ℝ) ^ 2 * (Real.log P) ^ (-E)) by ring]
      rw [Real.sqrt_mul hC, Real.sqrt_mul (sq_nonneg (b : ℝ)),
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ b)]
      simp only [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul hlogPpos.le, mul_pow, ← Real.rpow_natCast]
      rw [show (Real.log P) ^ (204 : ℕ) =
        (Real.log P) ^ (204 : ℝ) by
          exact (Real.rpow_natCast (Real.log P) 204).symm]
      rw [hE]
      calc
        6 ^ (204 : ℝ) * (Real.log P) ^ (204 : ℝ) *
            (C ^ (1 / 2 : ℝ) *
              ((b : ℝ) * (Real.log P) ^ (-(2 * A + 408) * (1 / 2)))) =
            6 ^ (204 : ℝ) * C ^ (1 / 2 : ℝ) * (b : ℝ) *
              ((Real.log P) ^ (204 : ℝ) *
                (Real.log P) ^ (-(2 * A + 408) * (1 / 2))) := by ring
        _ = 6 ^ (204 : ℝ) * C ^ (1 / 2 : ℝ) * (b : ℝ) *
              (Real.log P) ^ (-A) := by
          rw [← Real.rpow_add hlogPpos]
          congr 1
          ring_nf

/-- Monotonicity of the two replacements used in the first geometric
compression of a Type II source block. -/
theorem typeIISourceBlockMajorant_mono
    {card qouter qinner S Q Q' W V : ℝ}
    (hcard : card ≤ qouter) (hQ : Q ≤ Q')
    (hqouter0 : 0 ≤ qouter)
    (hqinner0 : 0 ≤ qinner) (hS0 : 0 ≤ S)
    (hQ0 : 0 ≤ Q) (hW0 : 0 ≤ W) (hV0 : 0 ≤ V) :
    card * (qouter * qinner * S + S * (qinner * (Q * (W + qinner * V)))) ≤
      qouter *
        (qouter * qinner * S + S * (qinner * (Q' * (W + qinner * V)))) := by
  have hgroup : 0 ≤ W + qinner * V := by positivity
  have hinner : Q * (W + qinner * V) ≤ Q' * (W + qinner * V) :=
    mul_le_mul_of_nonneg_right hQ hgroup
  have hblock :
      qouter * qinner * S + S * (qinner * (Q * (W + qinner * V))) ≤
        qouter * qinner * S + S * (qinner * (Q' * (W + qinner * V))) := by
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinner hqinner0) hS0)
  have hleft :
      0 ≤ qouter * qinner * S + S * (qinner * (Q * (W + qinner * V))) := by
    positivity
  calc
    card * (qouter * qinner * S + S * (qinner * (Q * (W + qinner * V)))) ≤
        qouter * (qouter * qinner * S + S * (qinner * (Q * (W + qinner * V)))) :=
      mul_le_mul_of_nonneg_right hcard hleft
    _ ≤ qouter *
        (qouter * qinner * S + S * (qinner * (Q' * (W + qinner * V)))) :=
      mul_le_mul_of_nonneg_left hblock hqouter0

/-- Monotonicity in both short-block lengths for the canonical geometric
expression. -/
theorem typeIIGeometricBlockMajorant_mono
    {qouter qinner q S Q W V : ℝ}
    (hqouter : qouter ≤ q) (hqinner : qinner ≤ q)
    (hqouter0 : 0 ≤ qouter) (hqinner0 : 0 ≤ qinner) (hq0 : 0 ≤ q)
    (hS0 : 0 ≤ S) (hQ0 : 0 ≤ Q) (hW0 : 0 ≤ W) (hV0 : 0 ≤ V) :
    qouter *
        (qouter * qinner * S + S * qinner * (Q * (W + qinner * V))) ≤
      q * (q * q * S + S * q * (Q * (W + q * V))) := by
  gcongr

/-- Monotonicity step replacing the squared local logarithm by a global
squared logarithmic envelope. -/
theorem typeIIUniformGeometricBlockMajorant_log_mono
    {q S L Q W V : ℝ}
    (hq0 : 0 ≤ q) (hQ0 : 0 ≤ Q) (hW0 : 0 ≤ W) (hV0 : 0 ≤ V)
    (hS : S ≤ 4 * L ^ 2) :
    q * (q * q * S + S * q * (Q * (W + q * V))) ≤
      4 * q * L ^ 2 * (q * q + q * (Q * (W + q * V))) := by
  calc
    q * (q * q * S + S * q * (Q * (W + q * V))) =
        q * S * (q * q + q * (Q * (W + q * V))) := by ring
    _ ≤ q * (4 * L ^ 2) * (q * q + q * (Q * (W + q * V))) := by
      gcongr
    _ = 4 * q * L ^ 2 * (q * q + q * (Q * (W + q * V))) := by ring

/-- Simultaneous monotonicity in two independent block widths and in the
squared logarithmic factor. -/
theorem typeIIGeometricBlockMajorant_dyadic_mono
    {qouter qinner Qouter Qinner S L Q W V : ℝ}
    (hqouter : qouter ≤ Qouter) (hqinner : qinner ≤ Qinner)
    (hqouter0 : 0 ≤ qouter) (hqinner0 : 0 ≤ qinner)
    (hQouter0 : 0 ≤ Qouter) (hQinner0 : 0 ≤ Qinner)
    (hS0 : 0 ≤ S) (hQ0 : 0 ≤ Q) (hW0 : 0 ≤ W) (hV0 : 0 ≤ V)
    (hS : S ≤ 4 * L ^ 2) :
    qouter *
        (qouter * qinner * S + S * qinner * (Q * (W + qinner * V))) ≤
      4 * Qouter * L ^ 2 *
        (Qouter * Qinner + Qinner * (Q * (W + Qinner * V))) := by
  calc
    qouter *
        (qouter * qinner * S + S * qinner * (Q * (W + qinner * V))) =
      qouter * S *
        (qouter * qinner + qinner * (Q * (W + qinner * V))) := by ring
    _ ≤ Qouter * (4 * L ^ 2) *
        (Qouter * Qinner + Qinner * (Q * (W + Qinner * V))) := by
      gcongr
    _ = 4 * Qouter * L ^ 2 *
        (Qouter * Qinner + Qinner * (Q * (W + Qinner * V))) := by ring

/-- Exact exponent ledger for the dyadic geometric majorant.  Once its two
dyadic product monomials are bounded by `b²`, the three surviving terms have
logarithmic denominators `298`, `197`, and `297`. -/
theorem typeIIDyadicGeometricBlockMajorant_product_mono
    {D E K L C c Fdecay V b2 : ℝ}
    (hL : 0 < L)
    (hC0 : 0 ≤ C) (hc0 : 0 ≤ c) (hF0 : 0 ≤ Fdecay) (hV0 : 0 ≤ V)
    (hDDE : D * D * E ≤ b2)
    (hDKEE : D * K * E ^ 2 ≤ b2) :
    4 * (D / L ^ 100) * L ^ 2 *
        ((D / L ^ 100) * (E / L ^ 100) +
          (E / L ^ 100) *
            (C * L * K *
              (4 * (2 * (c * (2 * E) * Fdecay)) +
                (E / L ^ 100) * V))) ≤
      b2 * (4 / L ^ 298 +
        64 * C * c * Fdecay / L ^ 197 +
        4 * C * V / L ^ 297) := by
  have hLne : L ≠ 0 := hL.ne'
  have hexpand :
      4 * (D / L ^ 100) * L ^ 2 *
          ((D / L ^ 100) * (E / L ^ 100) +
            (E / L ^ 100) *
              (C * L * K *
                (4 * (2 * (c * (2 * E) * Fdecay)) +
                  (E / L ^ 100) * V))) =
        (4 / L ^ 298) * (D * D * E) +
          (64 * C * c * Fdecay / L ^ 197) * (D * K * E ^ 2) +
          (4 * C * V / L ^ 297) * (D * K * E ^ 2) := by
    field_simp
    ring
  rw [hexpand]
  calc
    (4 / L ^ 298) * (D * D * E) +
          (64 * C * c * Fdecay / L ^ 197) * (D * K * E ^ 2) +
          (4 * C * V / L ^ 297) * (D * K * E ^ 2) ≤
        (4 / L ^ 298) * b2 +
          (64 * C * c * Fdecay / L ^ 197) * b2 +
          (4 * C * V / L ^ 297) * b2 := by
      gcongr
    _ = b2 * (4 / L ^ 298 +
        64 * C * c * Fdecay / L ^ 197 +
        4 * C * V / L ^ 297) := by ring

/-- Sharpened exponent ledger in which the purely diagonal dyadic monomial
has its own power-saving bound. -/
theorem typeIIDyadicGeometricBlockMajorant_product_mono_sharp
    {D E K L C c Fdecay V bdiag b2 : ℝ}
    (hL : 0 < L)
    (hC0 : 0 ≤ C) (hc0 : 0 ≤ c) (hF0 : 0 ≤ Fdecay) (hV0 : 0 ≤ V)
    (hDDE : D * D * E ≤ bdiag)
    (hDKEE : D * K * E ^ 2 ≤ b2) :
    4 * (D / L ^ 100) * L ^ 2 *
        ((D / L ^ 100) * (E / L ^ 100) +
          (E / L ^ 100) *
            (C * L * K *
              (4 * (2 * (c * (2 * E) * Fdecay)) +
                (E / L ^ 100) * V))) ≤
      (4 / L ^ 298) * bdiag +
        b2 * (64 * C * c * Fdecay / L ^ 197 +
          4 * C * V / L ^ 297) := by
  have hLne : L ≠ 0 := hL.ne'
  have hexpand :
      4 * (D / L ^ 100) * L ^ 2 *
          ((D / L ^ 100) * (E / L ^ 100) +
            (E / L ^ 100) *
              (C * L * K *
                (4 * (2 * (c * (2 * E) * Fdecay)) +
                  (E / L ^ 100) * V))) =
        (4 / L ^ 298) * (D * D * E) +
          (64 * C * c * Fdecay / L ^ 197) * (D * K * E ^ 2) +
          (4 * C * V / L ^ 297) * (D * K * E ^ 2) := by
    field_simp
    ring
  rw [hexpand]
  calc
    (4 / L ^ 298) * (D * D * E) +
          (64 * C * c * Fdecay / L ^ 197) * (D * K * E ^ 2) +
          (4 * C * V / L ^ 297) * (D * K * E ^ 2) ≤
        (4 / L ^ 298) * bdiag +
          (64 * C * c * Fdecay / L ^ 197) * b2 +
          (4 * C * V / L ^ 297) * b2 := by
      gcongr
    _ = (4 / L ^ 298) * bdiag +
        b2 * (64 * C * c * Fdecay / L ^ 197 +
          4 * C * V / L ^ 297) := by ring

/-- The exact canonical source majorant is bounded by its first geometric
compression on every canonical block once the cube-root cutoff contains the
subdivision budget. -/
theorem vaughanTypeIICanonicalSourceBlockMajorant_le_geometric
    {P N T : ℝ} {a b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hbudget : 2 * vaughanShortIntervalBudget b ≤
      vaughanSourceTailCutoff b)
    (hsk : sk ∈ vaughanShortIntervalIndexBox b) :
    vaughanTypeIICanonicalSourceBlockMajorant P a b N sk tl T ≤
      vaughanTypeIICanonicalGeometricBlockMajorant P b N sk tl T := by
  have hlogNonneg : 0 ≤ Real.log b := by linarith
  have hlogPNonneg : 0 ≤ Real.log P := Real.log_nonneg hP
  have hKpos : (0 : ℝ) < (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ) := by
    exact_mod_cast (by
      unfold dyadicShortIntervalLeftEndpoint
      positivity : 0 < dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk)
  have hBpos : (0 : ℝ) < (2 * 2 ^ tl.1 : ℕ) := by positivity
  have hFnonneg : 0 ≤ reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ)) :=
    reciprocalPhaseScale_nonneg N N 2 (mul_pos hKpos hBpos)
  have hFpow : 0 ≤ (reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ))) ^ (-(1 / 1024 : ℝ)) :=
    Real.rpow_nonneg hFnonneg _
  have hKpow : 0 ≤ ((1 : ℝ) /
      (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) ^ (1 / 1024 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hPpow : 0 ≤ Real.log P ^ (-T) :=
    Real.rpow_nonneg hlogPNonneg _
  have hdecayConstant : 0 ≤
      (2 : ℝ) ^ (1 - (1 / 1024 : ℝ)) /
        (1 - (1 / 1024 : ℝ)) := by positivity
  have hgeoNonneg : 0 ≤
      vaughanTypeIICanonicalGeometricBlockMajorant P b N sk tl T := by
    unfold vaughanTypeIICanonicalGeometricBlockMajorant
    dsimp only
    unfold vaughanTypeIICanonicalQConstant
    positivity
  by_cases hskCut : 2 * 2 ^ sk.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut] using hgeoNonneg
  by_cases htlCut : 2 * 2 ^ tl.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut, htlCut] using hgeoNonneg
  by_cases hsupport : vaughanTypeIIDoubleBlockProductSupport a b sk tl = ∅
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut, htlCut, hsupport] using
      hgeoNonneg
  have hskLargeNat : vaughanShortIntervalBudget b ≤ 2 ^ sk.1 := by
    omega
  have hskLarge : (vaughanShortIntervalBudget b : ℝ) ≤
      (2 ^ sk.1 : ℕ) := by exact_mod_cast hskLargeNat
  have hqlog := one_add_log_vaughanShortIntervalLength_le_two_mul_log
    hb hlog hsk hskLarge
  have hcardNat := card_dyadicShortIntervalIndexedBlock_le_length
    (vaughanShortIntervalBudget_pos b) sk
  have hcard : ((dyadicShortIntervalIndexedBlock
      (vaughanShortIntervalBudget b) sk).card : ℝ) ≤
      (dyadicShortIntervalLength (2 ^ sk.1)
        (vaughanShortIntervalBudget b) : ℝ) := by
    exact_mod_cast hcardNat
  have hQ :
      (((370 * vaughanTypeIICanonicalOrders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (dyadicShortIntervalLength (2 ^ sk.1)
                (vaughanShortIntervalBudget b) : ℝ)) *
              (dyadicShortIntervalLeftEndpoint
                (vaughanShortIntervalBudget b) sk : ℕ))) ≤
        vaughanTypeIICanonicalQConstant * Real.log b *
          (dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) := by
    rw [card_vaughanTypeIICanonicalOrders]
    rw [show 370 * 2 + 173 = 913 by norm_num]
    let C : ℝ := 913 * 480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hK : 0 ≤ (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) := by positivity
    calc
      913 * (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
            (1 + Real.log (dyadicShortIntervalLength (2 ^ sk.1)
              (vaughanShortIntervalBudget b) : ℝ)) *
            (dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ)) =
          C * (1 + Real.log (dyadicShortIntervalLength (2 ^ sk.1)
            (vaughanShortIntervalBudget b) : ℝ)) *
            (dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ) := by ring
      _ ≤ C * (2 * Real.log b) *
          (dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) := by gcongr
      _ = vaughanTypeIICanonicalQConstant * Real.log b *
          (dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) := by
        unfold C vaughanTypeIICanonicalQConstant
        ring
  have hqouterPosNat : 0 < dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget b) :=
    dyadicShortIntervalLength_pos (pow_pos (by omega) sk.1)
      (vaughanShortIntervalBudget_pos b)
  have hqinnerPosNat : 0 < dyadicShortIntervalLength (2 ^ tl.1)
      (vaughanShortIntervalBudget b) :=
    dyadicShortIntervalLength_pos (pow_pos (by omega) tl.1)
      (vaughanShortIntervalBudget_pos b)
  have hqouter0 : (0 : ℝ) ≤ dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget b) := by exact_mod_cast (Nat.zero_le _)
  have hqinner0 : (0 : ℝ) ≤ dyadicShortIntervalLength (2 ^ tl.1)
      (vaughanShortIntervalBudget b) := by exact_mod_cast (Nat.zero_le _)
  have hlogq0 : 0 ≤ Real.log (dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget b) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hqouterPosNat
  have hQ0 : 0 ≤
      (((370 * vaughanTypeIICanonicalOrders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
            (1 + Real.log (dyadicShortIntervalLength (2 ^ sk.1)
              (vaughanShortIntervalBudget b) : ℝ)) *
            (dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ))) := by
    positivity
  have hW0 : 0 ≤ 4 *
      (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
        (1 - (1 / 1024 : ℝ))) * (2 * 2 ^ tl.1 : ℕ) *
          (reciprocalPhaseScale N N 2
            ((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ) *
                (2 * 2 ^ tl.1 : ℕ))) ^ (-(1 / 1024 : ℝ)))) := by
    positivity
  have hV0 : 0 ≤
      ((1 : ℝ) / (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) ^ (1 / 1024 : ℝ) +
        3 * (Real.log P) ^ (-T) := by
    positivity
  have hS0 : 0 ≤ (Real.log (2 * b)) ^ 2 := sq_nonneg _
  simp only [vaughanTypeIICanonicalSourceBlockMajorant,
    vaughanTypeIISourceBlockMajorant,
    hskCut, htlCut, hsupport, if_false,
    vaughanTypeIICanonicalGeometricBlockMajorant]
  simpa only [mul_assoc] using
    (typeIISourceBlockMajorant_mono hcard hQ hqouter0 hqinner0
      hS0 hQ0 hW0 hV0)

/-- Replacing both canonical short-block lengths by the common source width
`b / (log b)^100` bounds the first geometric block majorant. -/
theorem vaughanTypeIICanonicalGeometricBlockMajorant_le_uniform
    {P N T : ℝ} {b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hsk : sk ∈ vaughanShortIntervalIndexBox b)
    (htl : tl ∈ vaughanShortIntervalIndexBox b)
    (hskLarge : (vaughanShortIntervalBudget b : ℝ) ≤ (2 ^ sk.1 : ℕ))
    (htlLarge : (vaughanShortIntervalBudget b : ℝ) ≤ (2 ^ tl.1 : ℕ)) :
    vaughanTypeIICanonicalGeometricBlockMajorant P b N sk tl T ≤
      vaughanTypeIICanonicalUniformGeometricBlockMajorant P b N sk tl T := by
  have hqouter := vaughanShortIntervalLength_cast_le_global_realLog
    hb hlog hsk hskLarge
  have hqinner := vaughanShortIntervalLength_cast_le_global_realLog
    hb hlog htl htlLarge
  have hqouter0 : (0 : ℝ) ≤ dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget b) := by exact_mod_cast (Nat.zero_le _)
  have hqinner0 : (0 : ℝ) ≤ dyadicShortIntervalLength (2 ^ tl.1)
      (vaughanShortIntervalBudget b) := by exact_mod_cast (Nat.zero_le _)
  have hq0 : (0 : ℝ) ≤ (b : ℝ) / (Real.log b) ^ 100 := by positivity
  have hS0 : 0 ≤ (Real.log (2 * b)) ^ 2 := sq_nonneg _
  have hKpos : (0 : ℝ) < (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ) := by
    exact_mod_cast (by
      unfold dyadicShortIntervalLeftEndpoint
      positivity : 0 < dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk)
  have hBpos : (0 : ℝ) < (2 * 2 ^ tl.1 : ℕ) := by positivity
  have hF0 : 0 ≤ reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ)) :=
    reciprocalPhaseScale_nonneg N N 2 (mul_pos hKpos hBpos)
  have hlogP0 : 0 ≤ Real.log P := Real.log_nonneg hP
  have hQ0 : 0 ≤ vaughanTypeIICanonicalQConstant * Real.log b *
      (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) := by
    unfold vaughanTypeIICanonicalQConstant
    positivity
  have hW0 : 0 ≤ 4 *
      (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
        (1 - (1 / 1024 : ℝ))) * (2 * 2 ^ tl.1 : ℕ) *
          (reciprocalPhaseScale N N 2
            ((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ) *
                (2 * 2 ^ tl.1 : ℕ))) ^ (-(1 / 1024 : ℝ)))) := by
    have hFpow := Real.rpow_nonneg hF0 (-(1 / 1024 : ℝ))
    positivity
  have hV0 : 0 ≤
      ((1 : ℝ) / (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) ^ (1 / 1024 : ℝ) +
        3 * (Real.log P) ^ (-T) := by
    have hKpow := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤
      (1 : ℝ) / (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) (1 / 1024 : ℝ)
    have hPpow := Real.rpow_nonneg hlogP0 (-T)
    positivity
  unfold vaughanTypeIICanonicalGeometricBlockMajorant
    vaughanTypeIICanonicalUniformGeometricBlockMajorant
  dsimp only
  simpa only [mul_assoc] using
    (typeIIGeometricBlockMajorant_mono hqouter hqinner hqouter0 hqinner0
      hq0 hS0 hQ0 hW0 hV0)

/-- The first geometric majorant is bounded by the source-critical dyadic
majorant, retaining each block's own dyadic width. -/
theorem vaughanTypeIICanonicalGeometricBlockMajorant_le_dyadic
    {P N T : ℝ} {b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hskLarge : (vaughanShortIntervalBudget b : ℝ) ≤ (2 ^ sk.1 : ℕ))
    (htlLarge : (vaughanShortIntervalBudget b : ℝ) ≤ (2 ^ tl.1 : ℕ)) :
    vaughanTypeIICanonicalGeometricBlockMajorant P b N sk tl T ≤
      vaughanTypeIICanonicalDyadicGeometricBlockMajorant P b N sk tl T := by
  have hqouter := vaughanShortIntervalLength_cast_le_realLog
    hb hlog hskLarge
  have hqinner := vaughanShortIntervalLength_cast_le_realLog
    hb hlog htlLarge
  have hqouter0 : (0 : ℝ) ≤ dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget b) := by exact_mod_cast (Nat.zero_le _)
  have hqinner0 : (0 : ℝ) ≤ dyadicShortIntervalLength (2 ^ tl.1)
      (vaughanShortIntervalBudget b) := by exact_mod_cast (Nat.zero_le _)
  have hQouter0 : (0 : ℝ) ≤ (2 ^ sk.1 : ℕ) / (Real.log b) ^ 100 := by
    positivity
  have hQinner0 : (0 : ℝ) ≤ (2 ^ tl.1 : ℕ) / (Real.log b) ^ 100 := by
    positivity
  have hS0 : 0 ≤ (Real.log (2 * b)) ^ 2 := sq_nonneg _
  have hKpos : (0 : ℝ) < (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ) := by
    exact_mod_cast (by
      unfold dyadicShortIntervalLeftEndpoint
      positivity : 0 < dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk)
  have hBpos : (0 : ℝ) < (2 * 2 ^ tl.1 : ℕ) := by positivity
  have hF0 : 0 ≤ reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ)) :=
    reciprocalPhaseScale_nonneg N N 2 (mul_pos hKpos hBpos)
  have hQ0 : 0 ≤ vaughanTypeIICanonicalQConstant * Real.log b *
      (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) := by
    unfold vaughanTypeIICanonicalQConstant
    positivity
  have hW0 : 0 ≤ 4 *
      (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
        (1 - (1 / 1024 : ℝ))) * (2 * 2 ^ tl.1 : ℕ) *
          (reciprocalPhaseScale N N 2
            ((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ) *
                (2 * 2 ^ tl.1 : ℕ))) ^ (-(1 / 1024 : ℝ)))) := by
    have hFpow := Real.rpow_nonneg hF0 (-(1 / 1024 : ℝ))
    positivity
  have hV0 : 0 ≤
      ((1 : ℝ) / (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) ^ (1 / 1024 : ℝ) +
        3 * (Real.log P) ^ (-T) := by
    have hKpow := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤
      (1 : ℝ) / (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) (1 / 1024 : ℝ)
    have hPpow := Real.rpow_nonneg (Real.log_nonneg hP) (-T)
    positivity
  have hS := realLog_two_mul_nat_sq_le_four_mul_log_sq hb hlog
  unfold vaughanTypeIICanonicalGeometricBlockMajorant
    vaughanTypeIICanonicalDyadicGeometricBlockMajorant
  dsimp only
  simpa only [mul_assoc] using
    (typeIIGeometricBlockMajorant_dyadic_mono hqouter hqinner
      hqouter0 hqinner0 hQouter0 hQinner0 hS0 hQ0 hW0 hV0 hS)

/-- On a nonempty product-support block, the source-critical dyadic majorant
is bounded by the explicit `b²` product-compressed majorant. -/
theorem vaughanTypeIICanonicalDyadicGeometricBlockMajorant_le_productCompressed
    {P N T : ℝ} {a b : ℕ} {sk tl mn : ℕ × ℕ}
    (hP : 1 ≤ P) (hlog : 2 ≤ Real.log b)
    (hmn : mn ∈ vaughanTypeIIDoubleBlockProductSupport a b sk tl) :
    vaughanTypeIICanonicalDyadicGeometricBlockMajorant P b N sk tl T ≤
      vaughanTypeIICanonicalProductCompressedBlockMajorant P b N sk tl T := by
  have hL : 0 < Real.log b := by linarith
  have hKpos : (0 : ℝ) < (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ) := by
    exact_mod_cast (by
      unfold dyadicShortIntervalLeftEndpoint
      positivity : 0 < dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk)
  have hBpos : (0 : ℝ) < (2 * 2 ^ tl.1 : ℕ) := by positivity
  have hphase0 : 0 ≤ reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ)) :=
    reciprocalPhaseScale_nonneg N N 2 (mul_pos hKpos hBpos)
  have hFdecay0 : 0 ≤ (reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ))) ^ (-(1 / 1024 : ℝ)) :=
    Real.rpow_nonneg hphase0 _
  have hV0 : 0 ≤
      ((1 : ℝ) / (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) ^ (1 / 1024 : ℝ) +
        3 * (Real.log P) ^ (-T) := by
    have hKpow := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤
      (1 : ℝ) / (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) (1 / 1024 : ℝ)
    have hPpow := Real.rpow_nonneg (Real.log_nonneg hP) (-T)
    positivity
  have hDDE := vaughanTypeIIDoubleBlockOuterSquareInner_le_sq hmn
  have hDKEE := vaughanTypeIIDoubleBlockEndpointInnerSquare_le_sq hmn
  have hC0 : 0 ≤ vaughanTypeIICanonicalQConstant := by
    unfold vaughanTypeIICanonicalQConstant
    positivity
  have hc0 : 0 ≤
      (2 : ℝ) ^ (1 - (1 / 1024 : ℝ)) /
        (1 - (1 / 1024 : ℝ)) := by positivity
  unfold vaughanTypeIICanonicalDyadicGeometricBlockMajorant
    vaughanTypeIICanonicalProductCompressedBlockMajorant
  dsimp only
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
    (typeIIDyadicGeometricBlockMajorant_product_mono hL hC0 hc0
      hFdecay0 hV0 hDDE hDKEE)

/-- On a surviving nonempty block, the dyadic majorant is bounded by the
power-saved product compression. -/
theorem vaughanTypeIICanonicalDyadicGeometricBlockMajorant_le_powerSaved
    {P N T : ℝ} {a b : ℕ} {sk tl mn : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hquarter : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ))
    (hnotCutoff : ¬2 * 2 ^ tl.1 ≤ vaughanSourceTailCutoff b)
    (hmn : mn ∈ vaughanTypeIIDoubleBlockProductSupport a b sk tl) :
    vaughanTypeIICanonicalDyadicGeometricBlockMajorant P b N sk tl T ≤
      vaughanTypeIICanonicalPowerSavedBlockMajorant P b N sk tl T := by
  have hL : 0 < Real.log b := by linarith
  have hKpos : (0 : ℝ) < (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ) := by
    exact_mod_cast (by
      unfold dyadicShortIntervalLeftEndpoint
      positivity : 0 < dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk)
  have hBpos : (0 : ℝ) < (2 * 2 ^ tl.1 : ℕ) := by positivity
  have hphase0 : 0 ≤ reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ)) :=
    reciprocalPhaseScale_nonneg N N 2 (mul_pos hKpos hBpos)
  have hFdecay0 : 0 ≤ (reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ))) ^ (-(1 / 1024 : ℝ)) :=
    Real.rpow_nonneg hphase0 _
  have hV0 : 0 ≤
      ((1 : ℝ) / (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) ^ (1 / 1024 : ℝ) +
        3 * (Real.log P) ^ (-T) := by
    have hKpow := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤
      (1 : ℝ) / (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) (1 / 1024 : ℝ)
    have hPpow := Real.rpow_nonneg (Real.log_nonneg hP) (-T)
    positivity
  have hDDE :=
    vaughanTypeIIDoubleBlockOuterSquareInner_le_sq_div_quarter_rpow
      hb hquarter hnotCutoff hmn
  have hDKEE := vaughanTypeIIDoubleBlockEndpointInnerSquare_le_sq hmn
  have hC0 : 0 ≤ vaughanTypeIICanonicalQConstant := by
    unfold vaughanTypeIICanonicalQConstant
    positivity
  have hc0 : 0 ≤
      (2 : ℝ) ^ (1 - (1 / 1024 : ℝ)) /
        (1 - (1 / 1024 : ℝ)) := by positivity
  unfold vaughanTypeIICanonicalDyadicGeometricBlockMajorant
    vaughanTypeIICanonicalPowerSavedBlockMajorant
  dsimp only
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
    (typeIIDyadicGeometricBlockMajorant_product_mono_sharp hL hC0 hc0
      hFdecay0 hV0 hDDE hDKEE)

/-- The uniform geometric block majorant is nonnegative on the source range. -/
theorem vaughanTypeIICanonicalUniformGeometricBlockMajorant_nonneg
    {P N T : ℝ} {b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) :
    0 ≤ vaughanTypeIICanonicalUniformGeometricBlockMajorant
      P b N sk tl T := by
  have hKpos : (0 : ℝ) < (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ) := by
    exact_mod_cast (by
      unfold dyadicShortIntervalLeftEndpoint
      positivity : 0 < dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk)
  have hBpos : (0 : ℝ) < (2 * 2 ^ tl.1 : ℕ) := by positivity
  have hF0 : 0 ≤ reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ)) :=
    reciprocalPhaseScale_nonneg N N 2 (mul_pos hKpos hBpos)
  have hFpow := Real.rpow_nonneg hF0 (-(1 / 1024 : ℝ))
  have hKpow := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤
    (1 : ℝ) / (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ)) (1 / 1024 : ℝ)
  have hPpow := Real.rpow_nonneg (Real.log_nonneg hP) (-T)
  unfold vaughanTypeIICanonicalUniformGeometricBlockMajorant
    vaughanTypeIICanonicalQConstant
  dsimp only
  positivity

/-- The source-critical dyadic geometric majorant is nonnegative. -/
theorem vaughanTypeIICanonicalDyadicGeometricBlockMajorant_nonneg
    {P N T : ℝ} {b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) :
    0 ≤ vaughanTypeIICanonicalDyadicGeometricBlockMajorant
      P b N sk tl T := by
  have hKpos : (0 : ℝ) < (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ) := by
    exact_mod_cast (by
      unfold dyadicShortIntervalLeftEndpoint
      positivity : 0 < dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk)
  have hBpos : (0 : ℝ) < (2 * 2 ^ tl.1 : ℕ) := by positivity
  have hF0 : 0 ≤ reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ)) :=
    reciprocalPhaseScale_nonneg N N 2 (mul_pos hKpos hBpos)
  have hFpow := Real.rpow_nonneg hF0 (-(1 / 1024 : ℝ))
  have hKpow := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤
    (1 : ℝ) / (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ)) (1 / 1024 : ℝ)
  have hPpow := Real.rpow_nonneg (Real.log_nonneg hP) (-T)
  unfold vaughanTypeIICanonicalDyadicGeometricBlockMajorant
    vaughanTypeIICanonicalQConstant
  dsimp only
  positivity

/-- The explicit product-compressed majorant is nonnegative on the source
logarithmic range. -/
theorem vaughanTypeIICanonicalProductCompressedBlockMajorant_nonneg
    {P N T : ℝ} {b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hlog : 2 ≤ Real.log b) :
    0 ≤ vaughanTypeIICanonicalProductCompressedBlockMajorant
      P b N sk tl T := by
  have hKpos : (0 : ℝ) < (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ) := by
    exact_mod_cast (by
      unfold dyadicShortIntervalLeftEndpoint
      positivity : 0 < dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk)
  have hBpos : (0 : ℝ) < (2 * 2 ^ tl.1 : ℕ) := by positivity
  have hphase0 : 0 ≤ reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ)) :=
    reciprocalPhaseScale_nonneg N N 2 (mul_pos hKpos hBpos)
  have hFpow := Real.rpow_nonneg hphase0 (-(1 / 1024 : ℝ))
  have hKpow := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤
    (1 : ℝ) / (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ)) (1 / 1024 : ℝ)
  have hPpow := Real.rpow_nonneg (Real.log_nonneg hP) (-T)
  unfold vaughanTypeIICanonicalProductCompressedBlockMajorant
    vaughanTypeIICanonicalQConstant
  dsimp only
  positivity

/-- The quarter-power-saved product majorant is nonnegative on the source
range. -/
theorem vaughanTypeIICanonicalPowerSavedBlockMajorant_nonneg
    {P N T : ℝ} {b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b) :
    0 ≤ vaughanTypeIICanonicalPowerSavedBlockMajorant
      P b N sk tl T := by
  have hKpos : (0 : ℝ) < (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ) := by
    exact_mod_cast (by
      unfold dyadicShortIntervalLeftEndpoint
      positivity : 0 < dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk)
  have hBpos : (0 : ℝ) < (2 * 2 ^ tl.1 : ℕ) := by positivity
  have hphase0 : 0 ≤ reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ)) :=
    reciprocalPhaseScale_nonneg N N 2 (mul_pos hKpos hBpos)
  have hFpow := Real.rpow_nonneg hphase0 (-(1 / 1024 : ℝ))
  have hKpow := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤
    (1 : ℝ) / (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ)) (1 / 1024 : ℝ)
  have hPpow := Real.rpow_nonneg (Real.log_nonneg hP) (-T)
  have hbpow : 0 < (b : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hb) _
  unfold vaughanTypeIICanonicalPowerSavedBlockMajorant
    vaughanTypeIICanonicalQConstant
  dsimp only
  positivity

/-- The block-independent decay-absorbed majorant is nonnegative on the
source logarithmic range. -/
theorem vaughanTypeIICanonicalDecayAbsorbedBlockMajorant_nonneg
    {P d T : ℝ} {b : ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b) :
    0 ≤ vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T := by
  have hlogpow : 0 < (Real.log b) ^ d :=
    Real.rpow_pos_of_pos (by linarith) _
  have hphasepow := Real.rpow_nonneg hlogpow.le (-(1 / 1024 : ℝ))
  have hPpow := Real.rpow_nonneg (Real.log_nonneg hP) (-T)
  have hbpow : 0 < (b : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hb) _
  have hendpointpow := Real.rpow_nonneg
    (by positivity : (0 : ℝ) ≤ 1 / (b : ℝ) ^ (1 / 4 : ℝ))
    (1 / 1024 : ℝ)
  unfold vaughanTypeIICanonicalDecayAbsorbedBlockMajorant
    vaughanTypeIICanonicalQConstant
  positivity

/-- A phase-scale lower bound and the canonical quarter-power endpoint lower
bound remove the last block-dependent quantities from the power-saved
majorant. -/
theorem vaughanTypeIICanonicalPowerSavedBlockMajorant_le_decayAbsorbed
    {P N d T : ℝ} {b : ℕ} {sk tl : ℕ × ℕ}
    (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hF : (Real.log b) ^ d ≤ reciprocalPhaseScale N N 2
      (((dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ)))
    (hK : (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) :
    vaughanTypeIICanonicalPowerSavedBlockMajorant P b N sk tl T ≤
      vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T := by
  have hlogpow : 0 < (Real.log b) ^ d :=
    Real.rpow_pos_of_pos (by linarith) _
  have hFdecay :
      (reciprocalPhaseScale N N 2
        (((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
          ((2 * 2 ^ tl.1 : ℕ) : ℝ))) ^ (-(1 / 1024 : ℝ)) ≤
        ((Real.log b) ^ d) ^ (-(1 / 1024 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hlogpow hF (by norm_num)
  have hbpow : 0 < (b : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hb) _
  have hinv :
      (1 : ℝ) /
          (dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) ≤
        1 / (b : ℝ) ^ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le hbpow hK
  have hKdecay :
      ((1 : ℝ) /
          (dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ)) ^ (1 / 1024 : ℝ) ≤
        ((1 : ℝ) / (b : ℝ) ^ (1 / 4 : ℝ)) ^ (1 / 1024 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hinv (by norm_num)
  have hC0 : 0 ≤ vaughanTypeIICanonicalQConstant := by
    unfold vaughanTypeIICanonicalQConstant
    positivity
  have hc0 : 0 ≤
      (2 : ℝ) ^ (1 - (1 / 1024 : ℝ)) /
        (1 - (1 / 1024 : ℝ)) := by positivity
  unfold vaughanTypeIICanonicalPowerSavedBlockMajorant
    vaughanTypeIICanonicalDecayAbsorbedBlockMajorant
  dsimp only
  gcongr

/-- The uniform-length majorant is bounded by its global-logarithm
compression. -/
theorem vaughanTypeIICanonicalUniformGeometricBlockMajorant_le_logCompressed
    {P N T : ℝ} {b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b) :
    vaughanTypeIICanonicalUniformGeometricBlockMajorant P b N sk tl T ≤
      vaughanTypeIICanonicalLogCompressedBlockMajorant P b N sk tl T := by
  have hq0 : (0 : ℝ) ≤ (b : ℝ) / (Real.log b) ^ 100 := by positivity
  have hKpos : (0 : ℝ) < (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget b) sk : ℕ) := by
    exact_mod_cast (by
      unfold dyadicShortIntervalLeftEndpoint
      positivity : 0 < dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk)
  have hBpos : (0 : ℝ) < (2 * 2 ^ tl.1 : ℕ) := by positivity
  have hF0 : 0 ≤ reciprocalPhaseScale N N 2
      ((dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) *
          (2 * 2 ^ tl.1 : ℕ)) :=
    reciprocalPhaseScale_nonneg N N 2 (mul_pos hKpos hBpos)
  have hQ0 : 0 ≤ vaughanTypeIICanonicalQConstant * Real.log b *
      (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) := by
    unfold vaughanTypeIICanonicalQConstant
    positivity
  have hW0 : 0 ≤ 4 *
      (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
        (1 - (1 / 1024 : ℝ))) * (2 * 2 ^ tl.1 : ℕ) *
          (reciprocalPhaseScale N N 2
            ((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ) *
                (2 * 2 ^ tl.1 : ℕ))) ^ (-(1 / 1024 : ℝ)))) := by
    have hFpow := Real.rpow_nonneg hF0 (-(1 / 1024 : ℝ))
    positivity
  have hV0 : 0 ≤
      ((1 : ℝ) / (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) ^ (1 / 1024 : ℝ) +
        3 * (Real.log P) ^ (-T) := by
    have hKpow := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤
      (1 : ℝ) / (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ)) (1 / 1024 : ℝ)
    have hPpow := Real.rpow_nonneg (Real.log_nonneg hP) (-T)
    positivity
  have hS := realLog_two_mul_nat_sq_le_four_mul_log_sq hb hlog
  unfold vaughanTypeIICanonicalUniformGeometricBlockMajorant
    vaughanTypeIICanonicalLogCompressedBlockMajorant
  dsimp only
  simpa only [mul_assoc] using
    (typeIIUniformGeometricBlockMajorant_log_mono
      hq0 hQ0 hW0 hV0 hS)

/-- Every exact canonical source block is bounded by the uniform-length
geometric majorant.  Small cutoff blocks vanish; surviving blocks acquire the
large-scale hypotheses from the canonical cutoff budget. -/
theorem vaughanTypeIICanonicalSourceBlockMajorant_le_uniformGeometric
    {P N T : ℝ} {a b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hbudget : 2 * vaughanShortIntervalBudget b ≤
      vaughanSourceTailCutoff b)
    (hsk : sk ∈ vaughanShortIntervalIndexBox b)
    (htl : tl ∈ vaughanShortIntervalIndexBox b) :
    vaughanTypeIICanonicalSourceBlockMajorant P a b N sk tl T ≤
      vaughanTypeIICanonicalUniformGeometricBlockMajorant P b N sk tl T := by
  have huniform0 :=
    vaughanTypeIICanonicalUniformGeometricBlockMajorant_nonneg
      (P := P) (N := N) (T := T) (b := b) (sk := sk) (tl := tl)
      hP
  by_cases hskCut : 2 * 2 ^ sk.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut] using huniform0
  by_cases htlCut : 2 * 2 ^ tl.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut, htlCut] using huniform0
  have hskLargeNat : vaughanShortIntervalBudget b ≤ 2 ^ sk.1 := by omega
  have htlLargeNat : vaughanShortIntervalBudget b ≤ 2 ^ tl.1 := by omega
  have hskLarge : (vaughanShortIntervalBudget b : ℝ) ≤
      (2 ^ sk.1 : ℕ) := by exact_mod_cast hskLargeNat
  have htlLarge : (vaughanShortIntervalBudget b : ℝ) ≤
      (2 ^ tl.1 : ℕ) := by exact_mod_cast htlLargeNat
  exact (vaughanTypeIICanonicalSourceBlockMajorant_le_geometric
      hP hb hlog hbudget hsk).trans
    (vaughanTypeIICanonicalGeometricBlockMajorant_le_uniform
      hP hb hlog hsk htl hskLarge htlLarge)

/-- Every exact canonical source block is bounded by the common-width,
global-logarithm compressed majorant. -/
theorem vaughanTypeIICanonicalSourceBlockMajorant_le_logCompressed
    {P N T : ℝ} {a b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hbudget : 2 * vaughanShortIntervalBudget b ≤
      vaughanSourceTailCutoff b)
    (hsk : sk ∈ vaughanShortIntervalIndexBox b)
    (htl : tl ∈ vaughanShortIntervalIndexBox b) :
    vaughanTypeIICanonicalSourceBlockMajorant P a b N sk tl T ≤
      vaughanTypeIICanonicalLogCompressedBlockMajorant P b N sk tl T :=
  (vaughanTypeIICanonicalSourceBlockMajorant_le_uniformGeometric
    hP hb hlog hbudget hsk htl).trans
      (vaughanTypeIICanonicalUniformGeometricBlockMajorant_le_logCompressed
        hP hb hlog)

/-- Every exact canonical source block is bounded by the source-critical
dyadic geometric majorant. -/
theorem vaughanTypeIICanonicalSourceBlockMajorant_le_dyadicGeometric
    {P N T : ℝ} {a b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hbudget : 2 * vaughanShortIntervalBudget b ≤
      vaughanSourceTailCutoff b)
    (hsk : sk ∈ vaughanShortIntervalIndexBox b) :
    vaughanTypeIICanonicalSourceBlockMajorant P a b N sk tl T ≤
      vaughanTypeIICanonicalDyadicGeometricBlockMajorant P b N sk tl T := by
  have hdyadic0 := vaughanTypeIICanonicalDyadicGeometricBlockMajorant_nonneg
    (P := P) (N := N) (T := T) (b := b) (sk := sk) (tl := tl) hP
  by_cases hskCut : 2 * 2 ^ sk.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut] using hdyadic0
  by_cases htlCut : 2 * 2 ^ tl.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut, htlCut] using hdyadic0
  have hskLargeNat : vaughanShortIntervalBudget b ≤ 2 ^ sk.1 := by omega
  have htlLargeNat : vaughanShortIntervalBudget b ≤ 2 ^ tl.1 := by omega
  have hskLarge : (vaughanShortIntervalBudget b : ℝ) ≤
      (2 ^ sk.1 : ℕ) := by exact_mod_cast hskLargeNat
  have htlLarge : (vaughanShortIntervalBudget b : ℝ) ≤
      (2 ^ tl.1 : ℕ) := by exact_mod_cast htlLargeNat
  exact (vaughanTypeIICanonicalSourceBlockMajorant_le_geometric
      hP hb hlog hbudget hsk).trans
    (vaughanTypeIICanonicalGeometricBlockMajorant_le_dyadic
      hP hb hlog hskLarge htlLarge)

/-- Every exact canonical source block is bounded by the explicit `b²`
product-compressed majorant. -/
theorem vaughanTypeIICanonicalSourceBlockMajorant_le_productCompressed
    {P N T : ℝ} {a b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hbudget : 2 * vaughanShortIntervalBudget b ≤
      vaughanSourceTailCutoff b)
    (hsk : sk ∈ vaughanShortIntervalIndexBox b) :
    vaughanTypeIICanonicalSourceBlockMajorant P a b N sk tl T ≤
      vaughanTypeIICanonicalProductCompressedBlockMajorant P b N sk tl T := by
  have hproduct0 :=
    vaughanTypeIICanonicalProductCompressedBlockMajorant_nonneg
      (P := P) (N := N) (T := T) (b := b) (sk := sk) (tl := tl) hP hlog
  by_cases hskCut : 2 * 2 ^ sk.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut] using hproduct0
  by_cases htlCut : 2 * 2 ^ tl.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut, htlCut] using hproduct0
  by_cases hsupport : vaughanTypeIIDoubleBlockProductSupport a b sk tl = ∅
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut, htlCut, hsupport] using
      hproduct0
  obtain ⟨mn, hmn⟩ := Finset.nonempty_iff_ne_empty.mpr hsupport
  exact (vaughanTypeIICanonicalSourceBlockMajorant_le_dyadicGeometric
      hP hb hlog hbudget hsk).trans
    (vaughanTypeIICanonicalDyadicGeometricBlockMajorant_le_productCompressed
      hP hlog hmn)

/-- Every exact canonical source block is bounded by the quarter-power-saved
product compression. -/
theorem vaughanTypeIICanonicalSourceBlockMajorant_le_powerSaved
    {P N T : ℝ} {a b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hbudget : 2 * vaughanShortIntervalBudget b ≤
      vaughanSourceTailCutoff b)
    (hquarter : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ))
    (hsk : sk ∈ vaughanShortIntervalIndexBox b) :
    vaughanTypeIICanonicalSourceBlockMajorant P a b N sk tl T ≤
      vaughanTypeIICanonicalPowerSavedBlockMajorant P b N sk tl T := by
  have hsaved0 := vaughanTypeIICanonicalPowerSavedBlockMajorant_nonneg
    (P := P) (N := N) (T := T) (b := b) (sk := sk) (tl := tl)
      hP hb hlog
  by_cases hskCut : 2 * 2 ^ sk.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut] using hsaved0
  by_cases htlCut : 2 * 2 ^ tl.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut, htlCut] using hsaved0
  by_cases hsupport : vaughanTypeIIDoubleBlockProductSupport a b sk tl = ∅
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut, htlCut, hsupport] using hsaved0
  obtain ⟨mn, hmn⟩ := Finset.nonempty_iff_ne_empty.mpr hsupport
  exact (vaughanTypeIICanonicalSourceBlockMajorant_le_dyadicGeometric
      hP hb hlog hbudget hsk).trans
    (vaughanTypeIICanonicalDyadicGeometricBlockMajorant_le_powerSaved
      hP hb hlog hquarter htlCut hmn)

/-- Every exact canonical source block is bounded by the common
block-independent decay form once the global phase lower bound is available.
-/
theorem vaughanTypeIICanonicalSourceBlockMajorant_le_decayAbsorbed
    {P N d T : ℝ} {a b : ℕ} {sk tl : ℕ × ℕ}
    (hP : 1 ≤ P) (hb : 0 < b) (hlog : 2 ≤ Real.log b)
    (hbudget : 2 * vaughanShortIntervalBudget b ≤
      vaughanSourceTailCutoff b)
    (hquarter : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ))
    (hglobal : 2 * (b : ℝ) * (Real.log b) ^ d ≤ |N|)
    (hsk : sk ∈ vaughanShortIntervalIndexBox b) :
    vaughanTypeIICanonicalSourceBlockMajorant P a b N sk tl T ≤
      vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T := by
  have hdecay0 := vaughanTypeIICanonicalDecayAbsorbedBlockMajorant_nonneg
    (P := P) (d := d) (T := T) (b := b) hP hb hlog
  by_cases hskCut : 2 * 2 ^ sk.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut] using hdecay0
  by_cases htlCut : 2 * 2 ^ tl.1 ≤ vaughanSourceTailCutoff b
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut, htlCut] using hdecay0
  by_cases hsupport : vaughanTypeIIDoubleBlockProductSupport a b sk tl = ∅
  · simpa [vaughanTypeIICanonicalSourceBlockMajorant,
      vaughanTypeIISourceBlockMajorant, hskCut, htlCut, hsupport] using
      hdecay0
  obtain ⟨mn, hmn⟩ := Finset.nonempty_iff_ne_empty.mpr hsupport
  have hFblock : (Real.log b) ^ d ≤ reciprocalPhaseScale N N 2
      (((dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ)) :=
    logPower_le_reciprocalPhaseScale_of_productSupport
      (by linarith) hglobal hmn
  have hKblock : (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget b) sk : ℕ) :=
    (quarter_rpow_lt_outerEndpoint_of_not_vaughanSourceTailCutoff
      hquarter hskCut).le
  exact (vaughanTypeIICanonicalSourceBlockMajorant_le_powerSaved
      hP hb hlog hbudget hquarter hsk).trans
    (vaughanTypeIICanonicalPowerSavedBlockMajorant_le_decayAbsorbed
      hb hlog hFblock hKblock)

/-- Complete finite source-family Type II assembly.  The two tail cutoffs
annihilate every block with a small dyadic band, and only large--large blocks
consume the source Vinogradov estimate. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b U V : ℕ) (N : ℝ) (orders : Finset ℕ) (d : ℝ),
        0 < b → 2 ≤ Real.log b →
        2 * vaughanShortIntervalBudget b ≤ U →
        2 * vaughanShortIntervalBudget b ≤ V →
        N ≠ 0 → 5 ∈ orders → 6 ∈ orders → 0 ≤ d →
        2 * (b : ℝ) * (Real.log b) ^ d ≤ |N| →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        2 * Real.exp (c * Real.log P) ≤ (U : ℝ) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient U)
            (vaughanTypeIIGammaCoefficient V)‖ ≤
          ∑ sk ∈ vaughanShortIntervalIndexBox b,
            ∑ tl ∈ vaughanShortIntervalIndexBox b,
              Real.sqrt (vaughanTypeIISourceBlockMajorant
                P a b U V N orders sk tl T) := by
  have hblock :=
    eventually_norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le_sourceVinogradov
      hVinogradov hA hA₀ hc hε ha hAT
  filter_upwards [hblock] with P hblockP
  intro a b U V N orders d hb hlog hU hV hN hrFive hrSix hd
    hFhigh hNupper hKlower
  apply norm_weightedConvolutionProductSum_le_sum_sqrt_vaughanDoubleBlocks
  intro sk hsk tl htl
  by_cases hskCut : 2 * 2 ^ sk.1 ≤ U
  · have hzero :=
      weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_outerCutoff
        (Finset.Ico a b) b U V sk tl N N 2 hskCut
    simp [vaughanTypeIISourceBlockMajorant, hskCut, hzero]
  · have hskLarge : vaughanShortIntervalBudget b ≤ 2 ^ sk.1 :=
      by omega
    by_cases htlCut : 2 * 2 ^ tl.1 ≤ V
    · have hzero :=
        weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_innerCutoff
          (Finset.Ico a b) b U V sk tl N N 2 htlCut
      simp [vaughanTypeIISourceBlockMajorant, hskCut, htlCut, hzero]
    · have htlLarge : vaughanShortIntervalBudget b ≤ 2 ^ tl.1 :=
        by omega
      by_cases hsupport :
          vaughanTypeIIDoubleBlockProductSupport a b sk tl = ∅
      · have hzero :=
          weightedConvolutionProductVaughanTypeIIDoubleBlockSum_eq_zero_of_productSupport_eq_empty
            a b U V sk tl N hsupport
        simp [vaughanTypeIISourceBlockMajorant, hskCut, htlCut,
          hsupport, hzero]
      · have hsupportNonempty :
            (vaughanTypeIIDoubleBlockProductSupport a b sk tl).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hsupport
        rcases hsupportNonempty with ⟨mn, hmn⟩
        have hskLargeReal :
            (vaughanShortIntervalBudget b : ℝ) ≤ (2 ^ sk.1 : ℕ) := by
          exact_mod_cast hskLarge
        have hFblock : (Real.log b) ^ d ≤ reciprocalPhaseScale N N 2
            (((dyadicShortIntervalLeftEndpoint
                (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
              ((2 * 2 ^ tl.1 : ℕ) : ℝ)) :=
          logPower_le_reciprocalPhaseScale_of_productSupport
            (by linarith) hFhigh hmn
        have hKblock : c * Real.log P ≤ Real.log
            ((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) :=
          log_outerEndpoint_lower_of_not_cutoff hKlower hskCut
        have hlargeBound := hblockP a b U V N orders sk tl d hb hlog hsk htl
          hskLargeReal hN hrFive hrSix hd hFblock hNupper hKblock
        simpa only [vaughanTypeIISourceBlockMajorant, hskCut, htlCut,
          hsupport, if_false] using hlargeBound

/-- Canonical-cutoff form of the complete finite source-family Type II
assembly.  With `U = V = ⌊b^(1/3)⌋₊`, both tail-budget hypotheses and the
uniform outer-scale lower bound follow automatically once the source scale
is sufficiently large and `P ≤ b`. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonicalCutoff
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ) (orders : Finset ℕ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        N ≠ 0 → 5 ∈ orders → 6 ∈ orders → 0 ≤ d →
        2 * (b : ℝ) * (Real.log b) ^ d ≤ |N| →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          ∑ sk ∈ vaughanShortIntervalIndexBox b,
            ∑ tl ∈ vaughanShortIntervalIndexBox b,
              Real.sqrt (vaughanTypeIISourceBlockMajorant
                P a b (vaughanSourceTailCutoff b)
                  (vaughanSourceTailCutoff b) N orders sk tl T) := by
  have hfamily :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov
      hVinogradov hA hA₀ (by norm_num : (0 : ℝ) < 1 / 4) hε ha hAT
  obtain ⟨Bbudget, hbudget⟩ := eventually_atTop.1
    eventually_two_mul_vaughanShortIntervalBudget_le_vaughanSourceTailCutoff
  obtain ⟨Bquarter, hquarter⟩ := eventually_atTop.1
    eventually_two_mul_quarter_rpow_le_vaughanSourceTailCutoff
  let B₀ := max Bbudget Bquarter
  filter_upwards [hfamily, eventually_ge_atTop (max (B₀ : ℝ) 1)] with
      P hfamilyP hP
  intro a b N orders d hPb hb hlog hN hrFive hrSix hd hFhigh hNupper
  have hB₀Real : (B₀ : ℝ) ≤ b :=
    (le_max_left _ _).trans hP |>.trans hPb
  have hB₀ : B₀ ≤ b := by exact_mod_cast hB₀Real
  have hbudgetB :
      2 * vaughanShortIntervalBudget b ≤ vaughanSourceTailCutoff b :=
    hbudget b ((le_max_left _ _).trans hB₀)
  have hquarterB : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ) :=
    hquarter b ((le_max_right _ _).trans hB₀)
  have hPone : (1 : ℝ) ≤ P := (le_max_right _ _).trans hP
  have hPpow : P ^ (1 / 4 : ℝ) ≤ (b : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hPb (by norm_num)
  have hexp : Real.exp ((1 / 4 : ℝ) * Real.log P) =
      P ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hPone)]
    congr 1
    ring
  have hcutoffLower : 2 * Real.exp ((1 / 4 : ℝ) * Real.log P) ≤
      (vaughanSourceTailCutoff b : ℝ) := by
    rw [hexp]
    exact (mul_le_mul_of_nonneg_left hPpow (by norm_num)).trans hquarterB
  exact hfamilyP a b (vaughanSourceTailCutoff b)
    (vaughanSourceTailCutoff b) N orders d hb hlog hbudgetB hbudgetB
      hN hrFive hrSix hd hFhigh hNupper hcutoffLower

/-- Fully canonical source-family Type II assembly: the cube-root tail
cutoffs and the minimal order set `{5,6}` are both fixed in the statement. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonical
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        N ≠ 0 → 0 ≤ d →
        2 * (b : ℝ) * (Real.log b) ^ d ≤ |N| →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          ∑ sk ∈ vaughanShortIntervalIndexBox b,
            ∑ tl ∈ vaughanShortIntervalIndexBox b,
              Real.sqrt (vaughanTypeIICanonicalSourceBlockMajorant
                P a b N sk tl T) := by
  have hcanonical :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonicalCutoff
      hVinogradov hA hA₀ hε ha hAT
  filter_upwards [hcanonical] with P hcanonicalP
  intro a b N d hPb hb hlog hN hd hFhigh hNupper
  simpa only [vaughanTypeIICanonicalSourceBlockMajorant] using
    hcanonicalP a b N vaughanTypeIICanonicalOrders d hPb hb hlog hN
      five_mem_vaughanTypeIICanonicalOrders
      six_mem_vaughanTypeIICanonicalOrders hd hFhigh hNupper

/-- Fully canonical Type II assembly with both short-block lengths replaced by
the common source width `b / (log b)^100`. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_uniformGeometric
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        N ≠ 0 → 0 ≤ d →
        2 * (b : ℝ) * (Real.log b) ^ d ≤ |N| →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          ∑ sk ∈ vaughanShortIntervalIndexBox b,
            ∑ tl ∈ vaughanShortIntervalIndexBox b,
              Real.sqrt (vaughanTypeIICanonicalUniformGeometricBlockMajorant
                P b N sk tl T) := by
  have hcanonical :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonical
      hVinogradov hA hA₀ hε ha hAT
  obtain ⟨Bbudget, hbudget⟩ := eventually_atTop.1
    eventually_two_mul_vaughanShortIntervalBudget_le_vaughanSourceTailCutoff
  filter_upwards [hcanonical,
      eventually_ge_atTop (max (Bbudget : ℝ) 1)] with P hcanonicalP hP
  intro a b N d hPb hb hlog hN hd hFhigh hNupper
  have hPone : (1 : ℝ) ≤ P := (le_max_right _ _).trans hP
  have hBbudgetReal : (Bbudget : ℝ) ≤ b :=
    (le_max_left _ _).trans hP |>.trans hPb
  have hBbudget : Bbudget ≤ b := by exact_mod_cast hBbudgetReal
  have hbudgetB :
      2 * vaughanShortIntervalBudget b ≤ vaughanSourceTailCutoff b :=
    hbudget b hBbudget
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt (vaughanTypeIICanonicalSourceBlockMajorant
              P a b N sk tl T) :=
      hcanonicalP a b N d hPb hb hlog hN hd hFhigh hNupper
    _ ≤ ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt (vaughanTypeIICanonicalUniformGeometricBlockMajorant
              P b N sk tl T) := by
      apply Finset.sum_le_sum
      intro sk hsk
      apply Finset.sum_le_sum
      intro tl htl
      exact Real.sqrt_le_sqrt
        (vaughanTypeIICanonicalSourceBlockMajorant_le_uniformGeometric
          hPone hb hlog hbudgetB hsk htl)

/-- Fully canonical Type II assembly in the common-width,
global-logarithm-compressed block normal form. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logCompressed
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        N ≠ 0 → 0 ≤ d →
        2 * (b : ℝ) * (Real.log b) ^ d ≤ |N| →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          ∑ sk ∈ vaughanShortIntervalIndexBox b,
            ∑ tl ∈ vaughanShortIntervalIndexBox b,
              Real.sqrt (vaughanTypeIICanonicalLogCompressedBlockMajorant
                P b N sk tl T) := by
  have huniform :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_uniformGeometric
      hVinogradov hA hA₀ hε ha hAT
  filter_upwards [huniform, eventually_ge_atTop 1] with P huniformP hP
  intro a b N d hPb hb hlog hN hd hFhigh hNupper
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt (vaughanTypeIICanonicalUniformGeometricBlockMajorant
              P b N sk tl T) :=
      huniformP a b N d hPb hb hlog hN hd hFhigh hNupper
    _ ≤ ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt (vaughanTypeIICanonicalLogCompressedBlockMajorant
              P b N sk tl T) := by
      apply Finset.sum_le_sum
      intro sk hsk
      apply Finset.sum_le_sum
      intro tl htl
      exact Real.sqrt_le_sqrt
        (vaughanTypeIICanonicalUniformGeometricBlockMajorant_le_logCompressed
          hP hb hlog)

/-- Fully canonical Type II assembly with every exact block reduced to the
explicit `b²` product-compressed exponent ledger. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_productCompressed
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        N ≠ 0 → 0 ≤ d →
        2 * (b : ℝ) * (Real.log b) ^ d ≤ |N| →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          ∑ sk ∈ vaughanShortIntervalIndexBox b,
            ∑ tl ∈ vaughanShortIntervalIndexBox b,
              Real.sqrt (vaughanTypeIICanonicalProductCompressedBlockMajorant
                P b N sk tl T) := by
  have hcanonical :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonical
      hVinogradov hA hA₀ hε ha hAT
  obtain ⟨Bbudget, hbudget⟩ := eventually_atTop.1
    eventually_two_mul_vaughanShortIntervalBudget_le_vaughanSourceTailCutoff
  filter_upwards [hcanonical,
      eventually_ge_atTop (max (Bbudget : ℝ) 1)] with P hcanonicalP hP
  intro a b N d hPb hb hlog hN hd hFhigh hNupper
  have hPone : (1 : ℝ) ≤ P := (le_max_right _ _).trans hP
  have hBbudgetReal : (Bbudget : ℝ) ≤ b :=
    (le_max_left _ _).trans hP |>.trans hPb
  have hBbudget : Bbudget ≤ b := by exact_mod_cast hBbudgetReal
  have hbudgetB :
      2 * vaughanShortIntervalBudget b ≤ vaughanSourceTailCutoff b :=
    hbudget b hBbudget
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt (vaughanTypeIICanonicalSourceBlockMajorant
              P a b N sk tl T) :=
      hcanonicalP a b N d hPb hb hlog hN hd hFhigh hNupper
    _ ≤ ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt (vaughanTypeIICanonicalProductCompressedBlockMajorant
              P b N sk tl T) := by
      apply Finset.sum_le_sum
      intro sk hsk
      apply Finset.sum_le_sum
      intro tl htl
      exact Real.sqrt_le_sqrt
        (vaughanTypeIICanonicalSourceBlockMajorant_le_productCompressed
          hPone hb hlog hbudgetB hsk)

/-- Fully canonical Type II assembly with the diagonal block term retaining
the canonical quarter-power saving. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_powerSaved
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        N ≠ 0 → 0 ≤ d →
        2 * (b : ℝ) * (Real.log b) ^ d ≤ |N| →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          ∑ sk ∈ vaughanShortIntervalIndexBox b,
            ∑ tl ∈ vaughanShortIntervalIndexBox b,
              Real.sqrt (vaughanTypeIICanonicalPowerSavedBlockMajorant
                P b N sk tl T) := by
  have hcanonical :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonical
      hVinogradov hA hA₀ hε ha hAT
  obtain ⟨Bbudget, hbudget⟩ := eventually_atTop.1
    eventually_two_mul_vaughanShortIntervalBudget_le_vaughanSourceTailCutoff
  obtain ⟨Bquarter, hquarter⟩ := eventually_atTop.1
    eventually_two_mul_quarter_rpow_le_vaughanSourceTailCutoff
  let B₀ := max Bbudget Bquarter
  filter_upwards [hcanonical,
      eventually_ge_atTop (max (B₀ : ℝ) 1)] with P hcanonicalP hP
  intro a b N d hPb hb hlog hN hd hFhigh hNupper
  have hPone : (1 : ℝ) ≤ P := (le_max_right _ _).trans hP
  have hB₀Real : (B₀ : ℝ) ≤ b :=
    (le_max_left _ _).trans hP |>.trans hPb
  have hB₀ : B₀ ≤ b := by exact_mod_cast hB₀Real
  have hbudgetB :
      2 * vaughanShortIntervalBudget b ≤ vaughanSourceTailCutoff b :=
    hbudget b ((le_max_left _ _).trans hB₀)
  have hquarterB : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ) :=
    hquarter b ((le_max_right _ _).trans hB₀)
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt (vaughanTypeIICanonicalSourceBlockMajorant
              P a b N sk tl T) :=
      hcanonicalP a b N d hPb hb hlog hN hd hFhigh hNupper
    _ ≤ ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt (vaughanTypeIICanonicalPowerSavedBlockMajorant
              P b N sk tl T) := by
      apply Finset.sum_le_sum
      intro sk hsk
      apply Finset.sum_le_sum
      intro tl htl
      exact Real.sqrt_le_sqrt
        (vaughanTypeIICanonicalSourceBlockMajorant_le_powerSaved
          hPone hb hlog hbudgetB hquarterB hsk)

/-- Fully canonical Type II assembly after absorbing the phase scale and
outer endpoint uniformly across the complete double-block family.  The
finite family is evaluated exactly, leaving its explicit `(log₂ b+1)^204`
loss. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_decayAbsorbed
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        N ≠ 0 → 0 ≤ d →
        2 * (b : ℝ) * (Real.log b) ^ d ≤ |N| →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          ((Nat.log 2 b + 1 : ℕ) : ℝ) ^ 204 *
            Real.sqrt
              (vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T) := by
  have hcanonical :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_canonical
      hVinogradov hA hA₀ hε ha hAT
  obtain ⟨Bbudget, hbudget⟩ := eventually_atTop.1
    eventually_two_mul_vaughanShortIntervalBudget_le_vaughanSourceTailCutoff
  obtain ⟨Bquarter, hquarter⟩ := eventually_atTop.1
    eventually_two_mul_quarter_rpow_le_vaughanSourceTailCutoff
  let B₀ := max Bbudget Bquarter
  filter_upwards [hcanonical,
      eventually_ge_atTop (max (B₀ : ℝ) 1)] with P hcanonicalP hP
  intro a b N d hPb hb hlog hN hd hFhigh hNupper
  have hPone : (1 : ℝ) ≤ P := (le_max_right _ _).trans hP
  have hB₀Real : (B₀ : ℝ) ≤ b :=
    (le_max_left _ _).trans hP |>.trans hPb
  have hB₀ : B₀ ≤ b := by exact_mod_cast hB₀Real
  have hbudgetB :
      2 * vaughanShortIntervalBudget b ≤ vaughanSourceTailCutoff b :=
    hbudget b ((le_max_left _ _).trans hB₀)
  have hquarterB : 2 * (b : ℝ) ^ (1 / 4 : ℝ) ≤
      (vaughanSourceTailCutoff b : ℝ) :=
    hquarter b ((le_max_right _ _).trans hB₀)
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt (vaughanTypeIICanonicalSourceBlockMajorant
              P a b N sk tl T) :=
      hcanonicalP a b N d hPb hb hlog hN hd hFhigh hNupper
    _ ≤ ∑ sk ∈ vaughanShortIntervalIndexBox b,
          ∑ tl ∈ vaughanShortIntervalIndexBox b,
            Real.sqrt
              (vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T) := by
      apply Finset.sum_le_sum
      intro sk hsk
      apply Finset.sum_le_sum
      intro tl htl
      exact Real.sqrt_le_sqrt
        (vaughanTypeIICanonicalSourceBlockMajorant_le_decayAbsorbed
          hPone hb hlog hbudgetB hquarterB hFhigh hsk)
    _ = ((vaughanShortIntervalIndexBox b).card : ℝ) ^ 2 *
          Real.sqrt
            (vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = ((Nat.log 2 b + 1 : ℕ) : ℝ) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalDecayAbsorbedBlockMajorant P b d T) := by
      rw [card_vaughanShortIntervalIndexBox, Nat.cast_pow]
      ring

/-- Source-facing flattened form of the preceding estimate.  The discrete
family count is also replaced by the elementary real-logarithmic bound, so
all remaining losses and savings are displayed as ordinary powers. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_explicitDecay
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ) (d : ℝ),
        P ≤ (b : ℝ) → 0 < b → 2 ≤ Real.log b →
        N ≠ 0 → 0 ≤ d →
        2 * (b : ℝ) * (Real.log b) ^ d ≤ |N| →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          (3 * Real.log b) ^ 204 *
            Real.sqrt
              (vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T) := by
  have habsorbed :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_decayAbsorbed
      hVinogradov hA hA₀ hε ha hAT
  filter_upwards [habsorbed] with P habsorbedP
  intro a b N d hPb hb hlog hN hd hFhigh hNupper
  have hbound := habsorbedP a b N d hPb hb hlog hN hd hFhigh hNupper
  rw [vaughanTypeIICanonicalDecayAbsorbedBlockMajorant_eq_explicit
    hb hlog] at hbound
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        ((Nat.log 2 b + 1 : ℕ) : ℝ) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T) :=
      hbound
    _ ≤ (3 * Real.log b) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T) := by
      gcongr
      exact source_natLogTwo_add_one_cast_le_three_mul_log hb hlog

/-- Conditional canonical Type II estimate with an arbitrary target
logarithmic saving.  The displayed inequalities on `d` and `T` are exactly
the exponent budget left after square-root extraction and the `204`-power
family loss. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logSaving
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ ε T S d : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A)
    (hS : 0 ≤ S)
    (hd : 2 * S + 408 ≤ d / 1024 + 197)
    (hTdecay : 2 * S + 408 ≤ T + 297) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ),
        P ≤ (b : ℝ) → (b : ℝ) ≤ 2 * P → 0 < b →
        2 ≤ Real.log b → N ≠ 0 →
        0 ≤ d → 2 * (b : ℝ) * (Real.log b) ^ d ≤ |N| →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          vaughanTypeIICanonicalFamilyDecayConstant * (b : ℝ) *
            (Real.log P) ^ (-S) := by
  have hfamily :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_explicitDecay
      hVinogradov hA hA₀ hε ha hAT
  have hledger :=
    eventually_vaughanTypeIICanonicalExplicitDecayBlockMajorant_le
      (E := 2 * S + 408) (by linarith) hd hTdecay
  filter_upwards [hfamily, hledger,
      eventually_ge_atTop (Real.exp 1)] with P hfamilyP hledgerP hPlarge
  intro a b N hPb hbP hb hlog hN hd0 hFhigh hNupper
  have hPpos : 0 < P := (Real.exp_pos 1).trans_le hPlarge
  have hbpos : (0 : ℝ) < b := hPpos.trans_le hPb
  have hlogPone : 1 ≤ Real.log P :=
    (Real.le_log_iff_exp_le hPpos).2 hPlarge
  have hlogbUpper : Real.log b ≤ 2 * Real.log P := by
    have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      Real.log b ≤ Real.log (2 * P) := Real.log_le_log hbpos hbP
      _ = Real.log 2 + Real.log P := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hPpos.ne']
      _ ≤ 2 * Real.log P := by linarith
  have hC0 : 0 ≤ vaughanTypeIICanonicalDecayConstant := by
    unfold vaughanTypeIICanonicalDecayConstant
      vaughanTypeIICanonicalQConstant
    positivity
  have hraw := hfamilyP a b N d hPb hb hlog hN hd0 hFhigh hNupper
  have hblock := hledgerP b hPb
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) b
          (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
          (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
          (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
        (3 * Real.log b) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalExplicitDecayBlockMajorant P b d T) :=
      hraw
    _ ≤ (3 * Real.log b) ^ 204 *
          Real.sqrt
            (vaughanTypeIICanonicalDecayConstant * (b : ℝ) ^ 2 *
              (Real.log P) ^ (-(2 * S + 408))) := by
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hblock)
        (pow_nonneg (by linarith : 0 ≤ 3 * Real.log b) _)
    _ ≤ 6 ^ (204 : ℕ) * Real.sqrt vaughanTypeIICanonicalDecayConstant *
          (b : ℝ) * (Real.log P) ^ (-S) :=
      three_mul_log_pow_mul_sqrt_decay_le hlogPone hlogbUpper hC0 rfl
    _ = vaughanTypeIICanonicalFamilyDecayConstant * (b : ℝ) *
          (Real.log P) ^ (-S) := by
      rfl

/-- Fully explicit conditional Type II logarithmic-saving theorem.  All
auxiliary exponent choices are fixed functions of the requested target `S`,
and the conclusion is written in the source's division form. -/
theorem eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logSaving_explicit
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (ha : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℝ in atTop,
      ∀ (a b : ℕ) (N : ℝ),
        P ≤ (b : ℝ) → (b : ℝ) ≤ 2 * P → 0 < b →
        2 ≤ Real.log b → N ≠ 0 →
        2 * (b : ℝ) * (Real.log b) ^
            (vaughanTypeIILogSavingPhaseExponent S) ≤ |N| →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        ‖weightedConvolutionProductSum (Finset.Ico a b) b
            (fun n => standardAdditiveCharacter (reciprocalPhase N N 2 n))
            (vaughanTypeIIBetaCoefficient (vaughanSourceTailCutoff b))
            (vaughanTypeIIGammaCoefficient (vaughanSourceTailCutoff b))‖ ≤
          vaughanTypeIICanonicalFamilyDecayConstant * (b : ℝ) /
            (Real.log P) ^ S := by
  have hA : (1 / 4 : ℝ) ≤ vaughanTypeIILogSavingVinogradovExponent S := by
    unfold vaughanTypeIILogSavingVinogradovExponent
    linarith
  have hAT : vaughanTypeIILogSavingSourceExponent S + 2 ≤
      3 * vaughanTypeIILogSavingVinogradovExponent S := by
    unfold vaughanTypeIILogSavingSourceExponent
      vaughanTypeIILogSavingVinogradovExponent
    linarith
  have hd : 2 * S + 408 ≤
      vaughanTypeIILogSavingPhaseExponent S / 1024 + 197 := by
    unfold vaughanTypeIILogSavingPhaseExponent
    ring_nf
    exact le_rfl
  have hTdecay : 2 * S + 408 ≤
      vaughanTypeIILogSavingSourceExponent S + 297 := by
    unfold vaughanTypeIILogSavingSourceExponent
    linarith
  have hd0 : 0 ≤ vaughanTypeIILogSavingPhaseExponent S := by
    unfold vaughanTypeIILogSavingPhaseExponent
    positivity
  have hgeneral :=
    eventually_norm_weightedConvolutionProductSum_vaughanTypeII_le_sourceVinogradov_logSaving
      hVinogradov hA hA₀ hε ha hAT hS hd hTdecay
  filter_upwards [hgeneral,
      eventually_ge_atTop (Real.exp 1)] with P hgeneralP hPlarge
  intro a b N hPb hbP hb hlog hN hFhigh hNupper
  have hPpos : 0 < P := (Real.exp_pos 1).trans_le hPlarge
  have hlogPpos : 0 < Real.log P :=
    (Real.log_exp 1 ▸ show (0 : ℝ) < 1 by norm_num) |>.trans_le
      (Real.log_le_log (Real.exp_pos 1) hPlarge)
  have hbound := hgeneralP a b N hPb hbP hb hlog hN hd0 hFhigh hNupper
  rw [Real.rpow_neg hlogPpos.le] at hbound
  simpa only [div_eq_mul_inv, mul_assoc] using hbound

end

end Tao2026
