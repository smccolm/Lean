import Tao2026.BadIntervalLargePrimeAdaptiveBlockSum
import Tao2026.BadIntervalBackwardLargePrime

/-!
# Backward typical intervals: adaptive finite block aggregation

The exceptional conductor and modulus-pair geometry is independent of the
chosen nonzero residue.  This module inserts the reflected residues `p-l`
into the same one-band and restricted two-band summations used for forward
typical intervals.
-/

namespace Tao2026

open scoped Classical

noncomputable section

set_option maxRecDepth 10000

private theorem sum_taoBackwardLargeAdaptiveDyadicIndex_majorant_eq
    (R H : ℕ) (hR : 0 < R) (Eset : Finset ℕ)
    (f : ℕ → ℝ) (A B : ℝ) :
    (∑ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
      (f a.2 + A + if a.2 ∈ Eset then B else 0)) =
      (H - 1 : ℕ) *
        ((∑ p ∈ taoDyadicPrimeBand R, f p) +
          ((taoDyadicPrimeBand R).card : ℝ) * A +
          (((taoDyadicPrimeBand R).filter (fun p => p ∈ Eset)).card : ℝ) * B) := by
  have hrange := taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand hR
  rw [taoLargeAntiSieveIndices, hrange]
  rw [show (∑ a ∈ (Finset.Ico 1 H).product (taoDyadicPrimeBand R),
      (f a.2 + A + if a.2 ∈ Eset then B else 0)) =
      ∑ l ∈ Finset.Ico 1 H, ∑ p ∈ taoDyadicPrimeBand R,
        (f p + A + if p ∈ Eset then B else 0) by
    exact Finset.sum_product _ _ _]
  simp only [Finset.sum_add_distrib]
  simp
  have hinter : taoDyadicPrimeBand R ∩ Eset =
      (taoDyadicPrimeBand R).filter (fun p => p ∈ Eset) := by ext; simp
  rw [hinter]
  ring

/-- Exact finite dyadic first-moment estimate for backward residues. -/
theorem sum_taoBackwardLargePrimeProbability_adaptive_dyadicBlock_le
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (R H m' : ℕ) (hR : 2 ≤ R) (hH : H ≤ R - 1)
    (A B K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hImproved : ∀ p ∈ taoDyadicPrimeBand R,
      taoLargePrimeAdaptiveImprovedError P p R ≤ A)
    (hExceptionalCard :
      (((taoDyadicPrimeBand R).filter fun p =>
        p ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
          (taoDyadicPrimeBand R) P R).card : ℝ) ≤ K)
    (hExceptional : ∀ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
      a.2 ∈ taoLargePrimeAdaptiveExceptionalConductorsFor
        (taoDyadicPrimeBand R) P R →
      taoBackwardLargePrimeProbability P hP m' a ≤ B) :
    (∑ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
      taoBackwardLargePrimeProbability P hP m' a) ≤
      (H - 1 : ℕ) *
        (((taoDyadicPrimeBand R).card : ℝ) * (2 / (R : ℝ) + A) + K * B) := by
  have hRpos : 0 < R := by omega
  have hrange := taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand hRpos
  let Eset := taoLargePrimeAdaptiveExceptionalConductorsFor
    (taoDyadicPrimeBand R) P R
  have hpointwise : ∀ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
      taoBackwardLargePrimeProbability P hP m' a ≤
        1 / (a.2.totient : ℝ) + A + if a.2 ∈ Eset then B else 0 := by
    intro a ha
    have haData := mem_taoLargeAntiSieveIndices.mp ha
    have haBand : a.2 ∈ taoDyadicPrimeBand R := by
      rw [← hrange]
      exact mem_taoLargeAntiSievePrimeRange.mpr
        ⟨haData.2.2.1, haData.2.2.2.1, haData.2.2.2.2⟩
    have halt : a.1 < a.2 := by omega
    by_cases haE : a.2 ∈ Eset
    · rw [if_pos haE]
      have hprob := hExceptional a ha (by simpa only [Eset] using haE)
      have hmain : 0 ≤ 1 / (a.2.totient : ℝ) := by positivity
      nlinarith
    · rw [if_neg haE, add_zero]
      by_cases hcop : Nat.Coprime m' a.2
      · have hprob := taoBackwardLargePrimeProbability_le_main_add_adaptiveError
          a haData.2.2.1 haBand haData.1 halt hcop P hP
            (by simpa only [Eset] using haE)
        have herr := hImproved a.2 haBand
        linarith
      · have hdvd : a.2 ∣ m' := haData.2.2.1.dvd_iff_not_coprime.mpr (by
          simpa only [Nat.coprime_comm] using hcop)
        rw [taoBackwardLargePrimeProbability_eq_zero_of_dvd_base
          P hP haData.1 halt hdvd]
        positivity
  have hmajorant := sum_taoBackwardLargeAdaptiveDyadicIndex_majorant_eq
    R H hRpos Eset (fun p => 1 / (p.totient : ℝ)) A B
  have hmain := sum_dyadicPrimeBand_one_div_totient_le hR
  have hExc :
      (((taoDyadicPrimeBand R).filter (fun p => p ∈ Eset)).card : ℝ) * B ≤ K * B :=
    mul_le_mul_of_nonneg_right (by simpa only [Eset] using hExceptionalCard) hB
  calc
    (∑ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
        taoBackwardLargePrimeProbability P hP m' a) ≤
      ∑ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
        (1 / (a.2.totient : ℝ) + A + if a.2 ∈ Eset then B else 0) :=
      Finset.sum_le_sum fun a ha => hpointwise a ha
    _ = (H - 1 : ℕ) *
        ((∑ p ∈ taoDyadicPrimeBand R, 1 / (p.totient : ℝ)) +
          ((taoDyadicPrimeBand R).card : ℝ) * A +
          (((taoDyadicPrimeBand R).filter (fun p => p ∈ Eset)).card : ℝ) * B) :=
      hmajorant
    _ ≤ (H - 1 : ℕ) *
        (((taoDyadicPrimeBand R).card : ℝ) * (2 / (R : ℝ) + A) + K * B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (∑ p ∈ taoDyadicPrimeBand R, 1 / (p.totient : ℝ)) +
              ((taoDyadicPrimeBand R).card : ℝ) * A +
              (((taoDyadicPrimeBand R).filter (fun p => p ∈ Eset)).card : ℝ) * B ≤
            ((taoDyadicPrimeBand R).card : ℝ) * (2 / (R : ℝ)) +
              ((taoDyadicPrimeBand R).card : ℝ) * A + K * B := by
          exact add_le_add (add_le_add hmain le_rfl) hExc
        _ = ((taoDyadicPrimeBand R).card : ℝ) * (2 / (R : ℝ) + A) + K * B := by
          ring

private theorem sum_taoBackwardLargePrime_adaptive_twoBand_majorant_eq
    (P : Fin 1001 → ℕ) (R S H : ℕ) (A B : ℝ) :
    (∑ a ∈ (Finset.Ico 1 H).product (taoDyadicPrimeBand R),
      ∑ b ∈ (Finset.Ico 1 H).product (taoDyadicPrimeBand S),
        (A + if (a.2, b.2) ∈ taoLargePrimeAdaptiveExceptionalModuliPairs P R S
          then B else 0)) =
      ((H - 1 : ℕ) : ℝ) ^ 2 *
        (((taoDyadicPrimeBand R).card : ℝ) *
            ((taoDyadicPrimeBand S).card : ℝ) * A +
          ((taoLargePrimeAdaptiveExceptionalModuliPairs P R S).card : ℝ) * B) := by
  let E := taoLargePrimeAdaptiveExceptionalModuliPairs P R S
  have hE : E ⊆ (taoDyadicPrimeBand R).product (taoDyadicPrimeBand S) :=
    taoLargePrimeAdaptiveExceptionalModuliPairs_subset P R S
  rw [show (∑ a ∈ (Finset.Ico 1 H).product (taoDyadicPrimeBand R),
      ∑ b ∈ (Finset.Ico 1 H).product (taoDyadicPrimeBand S),
        (A + if (a.2, b.2) ∈ E then B else 0)) =
      ∑ l ∈ Finset.Ico 1 H, ∑ p ∈ taoDyadicPrimeBand R,
        ∑ k ∈ Finset.Ico 1 H, ∑ q ∈ taoDyadicPrimeBand S,
          (A + if (p, q) ∈ E then B else 0) by
    calc
      _ = ∑ l ∈ Finset.Ico 1 H, ∑ p ∈ taoDyadicPrimeBand R,
          ∑ b ∈ (Finset.Ico 1 H).product (taoDyadicPrimeBand S),
            (A + if (p, b.2) ∈ E then B else 0) :=
        Finset.sum_product _ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_product _ _ _]
  have hIndicator :
      (∑ p ∈ taoDyadicPrimeBand R, ∑ q ∈ taoDyadicPrimeBand S,
        if (p, q) ∈ E then B else 0) = (E.card : ℝ) * B := by
    rw [show (∑ p ∈ taoDyadicPrimeBand R, ∑ q ∈ taoDyadicPrimeBand S,
        if (p, q) ∈ E then B else 0) =
        ∑ pq ∈ (taoDyadicPrimeBand R).product (taoDyadicPrimeBand S),
          if pq ∈ E then B else 0 by
      exact (Finset.sum_product (taoDyadicPrimeBand R)
        (taoDyadicPrimeBand S)
        (fun pq : ℕ × ℕ => if pq ∈ E then B else 0)).symm]
    simp
    have hinter :
        (taoDyadicPrimeBand R).product (taoDyadicPrimeBand S) ∩ E = E :=
      Finset.inter_eq_right.mpr hE
    exact Or.inl (congrArg Finset.card hinter)
  simp only [Finset.sum_add_distrib]
  simp
  rw [← Finset.mul_sum]
  rw [hIndicator]
  ring

/-- Restricted-band backward covariance aggregation. -/
theorem sum_taoBackwardLargePrimeCovariance_adaptive_twoBand_restrict_le
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (R S H m' : ℕ) (DR DS : Finset ℕ)
    (hDR : DR ⊆ taoDyadicPrimeBand R) (hDS : DS ⊆ taoDyadicPrimeBand S)
    (hR : 2 ≤ R) (hS : 2 ≤ S)
    (hHR : H ≤ R - 1) (hHS : H ≤ S - 1)
    (A B K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hImproved : ∀ p ∈ taoDyadicPrimeBand R,
      ∀ q ∈ taoDyadicPrimeBand S, p ≠ q →
      TaoLargePrimeAdaptivePairUnexceptional P R S (0, p) (0, q) →
      taoLargePrimeMixedAdaptiveCovarianceImprovedError P p q R S ≤ A)
    (hExceptionalCard :
      ((taoLargePrimeAdaptiveExceptionalModuliPairs P R S).card : ℝ) ≤ K)
    (hExceptional :
      ∀ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
      ∀ b ∈ (taoLargeAntiSieveIndices (S - 1) (2 * S - 1) H).filter
        (fun b => b.2 ≠ a.2),
      ¬TaoLargePrimeAdaptivePairUnexceptional P R S a b →
      taoBackwardLargePrimeJointProbability P hP m' a b ≤ B) :
    (∑ a ∈ (Finset.Ico 1 H).product DR,
      ∑ b ∈ ((Finset.Ico 1 H).product DS).filter (fun b => b.2 ≠ a.2),
        taoBackwardLargePrimeCovariance P hP m' a b) ≤
      ((H - 1 : ℕ) : ℝ) ^ 2 *
        (((taoDyadicPrimeBand R).card : ℝ) *
            ((taoDyadicPrimeBand S).card : ℝ) * A + K * B) := by
  have hRpos : 0 < R := by omega
  have hSpos : 0 < S := by omega
  have hrangeR := taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand hRpos
  have hrangeS := taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand hSpos
  let IR := (Finset.Ico 1 H).product DR
  let IS := (Finset.Ico 1 H).product DS
  let IRfull := (Finset.Ico 1 H).product (taoDyadicPrimeBand R)
  let ISfull := (Finset.Ico 1 H).product (taoDyadicPrimeBand S)
  let E := taoLargePrimeAdaptiveExceptionalModuliPairs P R S
  have hIR : IR ⊆ IRfull := by
    intro a ha
    have haData := Finset.mem_product.mp ha
    exact Finset.mem_product.mpr ⟨haData.1, hDR haData.2⟩
  have hIS : IS ⊆ ISfull := by
    intro b hb
    have hbData := Finset.mem_product.mp hb
    exact Finset.mem_product.mpr ⟨hbData.1, hDS hbData.2⟩
  have hpointwise : ∀ a ∈ IR, ∀ b ∈ IS.filter (fun b => b.2 ≠ a.2),
      taoBackwardLargePrimeCovariance P hP m' a b ≤
        A + if (a.2, b.2) ∈ E then B else 0 := by
    intro a ha b hb
    have haData := Finset.mem_product.mp ha
    have hbMem := (Finset.mem_filter.mp hb).1
    have hbData := Finset.mem_product.mp hbMem
    have haBand : a.2 ∈ taoDyadicPrimeBand R := hDR haData.2
    have hbBand : b.2 ∈ taoDyadicPrimeBand S := hDS hbData.2
    have hpq : a.2 ≠ b.2 := (Finset.mem_filter.mp hb).2.symm
    have haIco := Finset.mem_Ico.mp haData.1
    have hbIco := Finset.mem_Ico.mp hbData.1
    have halt : a.1 < a.2 := by
      have hpLower := (mem_taoDyadicPrimeBand.mp haBand).2.1
      omega
    have hblt : b.1 < b.2 := by
      have hpLower := (mem_taoDyadicPrimeBand.mp hbBand).2.1
      omega
    have haFull : a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H := by
      rw [taoLargeAntiSieveIndices, hrangeR]
      exact Finset.mem_product.mpr ⟨haData.1, haBand⟩
    have hbFull : b ∈ taoLargeAntiSieveIndices (S - 1) (2 * S - 1) H := by
      rw [taoLargeAntiSieveIndices, hrangeS]
      exact Finset.mem_product.mpr ⟨hbData.1, hbBand⟩
    have hbFullFiltered : b ∈
        (taoLargeAntiSieveIndices (S - 1) (2 * S - 1) H).filter
          (fun b => b.2 ≠ a.2) :=
      Finset.mem_filter.mpr ⟨hbFull, (Finset.mem_filter.mp hb).2⟩
    by_cases hpair : TaoLargePrimeAdaptivePairUnexceptional P R S a b
    · have hpairZero :
          TaoLargePrimeAdaptivePairUnexceptional P R S (0, a.2) (0, b.2) := by
        simpa only [TaoLargePrimeAdaptivePairUnexceptional] using hpair
      have hnotE : (a.2, b.2) ∉ E := by
        intro hE
        exact (Finset.mem_filter.mp hE).2.2 hpairZero
      rw [if_neg hnotE, add_zero]
      by_cases hcopA : Nat.Coprime m' a.2
      · by_cases hcopB : Nat.Coprime m' b.2
        · have hcov := taoBackwardLargePrimeCovariance_le_mixedAdaptiveErrors
            a b (mem_taoDyadicPrimeBand.mp haBand).1
              (mem_taoDyadicPrimeBand.mp hbBand).1 hpq
              haIco.1 halt hbIco.1 hblt
              (Nat.coprime_mul_iff_right.mpr ⟨hcopA, hcopB⟩)
              P hP hpair
          exact hcov.trans
            (hImproved a.2 haBand b.2 hbBand hpq hpairZero)
        · have hdvd : b.2 ∣ m' :=
            (mem_taoDyadicPrimeBand.mp hbBand).1.dvd_iff_not_coprime.mpr (by
              simpa only [Nat.coprime_comm] using hcopB)
          rw [taoBackwardLargePrimeCovariance_eq_zero_of_right_dvd_base
            P hP hbIco.1 hblt hdvd]
          exact hA
      · have hdvd : a.2 ∣ m' :=
          (mem_taoDyadicPrimeBand.mp haBand).1.dvd_iff_not_coprime.mpr (by
            simpa only [Nat.coprime_comm] using hcopA)
        rw [taoBackwardLargePrimeCovariance_eq_zero_of_left_dvd_base
          P hP haIco.1 halt hdvd]
        exact hA
    · have hE : (a.2, b.2) ∈ E := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨haBand, hbBand⟩, hpq, ?_⟩
        simpa only [TaoLargePrimeAdaptivePairUnexceptional] using hpair
      rw [if_pos hE]
      have hjoint := hExceptional a haFull b hbFullFiltered hpair
      have hcov := taoBackwardLargePrimeCovariance_le_jointProbability P hP m' a b
      nlinarith [hcov.trans hjoint]
  have hmajorantNonneg : ∀ (a b : ℕ × ℕ),
      0 ≤ A + if (a.2, b.2) ∈ E then B else 0 := by
    intro a b
    split_ifs <;> positivity
  have hfiltered :
      (∑ a ∈ IR, ∑ b ∈ IS.filter (fun b => b.2 ≠ a.2),
        taoBackwardLargePrimeCovariance P hP m' a b) ≤
      ∑ a ∈ IRfull, ∑ b ∈ ISfull,
        (A + if (a.2, b.2) ∈ E then B else 0) := by
    calc
      (∑ a ∈ IR, ∑ b ∈ IS.filter (fun b => b.2 ≠ a.2),
          taoBackwardLargePrimeCovariance P hP m' a b) ≤
        ∑ a ∈ IR, ∑ b ∈ IS.filter (fun b => b.2 ≠ a.2),
          (A + if (a.2, b.2) ∈ E then B else 0) := by
            exact Finset.sum_le_sum fun a ha =>
              Finset.sum_le_sum fun b hb => hpointwise a ha b hb
      _ ≤ ∑ a ∈ IR, ∑ b ∈ ISfull,
          (A + if (a.2, b.2) ∈ E then B else 0) := by
        apply Finset.sum_le_sum
        intro a ha
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by
            intro b hb
            exact hIS (Finset.mem_filter.mp hb).1)
          (fun b _ _ => hmajorantNonneg a b)
      _ ≤ ∑ a ∈ IRfull, ∑ b ∈ ISfull,
          (A + if (a.2, b.2) ∈ E then B else 0) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hIR
          (fun a _ _ => Finset.sum_nonneg fun b _ => hmajorantNonneg a b)
  have hmajorant := sum_taoBackwardLargePrime_adaptive_twoBand_majorant_eq
    P R S H A B
  calc
    (∑ a ∈ (Finset.Ico 1 H).product DR,
        ∑ b ∈ ((Finset.Ico 1 H).product DS).filter (fun b => b.2 ≠ a.2),
          taoBackwardLargePrimeCovariance P hP m' a b) ≤
      ∑ a ∈ IRfull, ∑ b ∈ ISfull,
        (A + if (a.2, b.2) ∈ E then B else 0) := hfiltered
    _ = ((H - 1 : ℕ) : ℝ) ^ 2 *
        (((taoDyadicPrimeBand R).card : ℝ) *
            ((taoDyadicPrimeBand S).card : ℝ) * A +
          ((taoLargePrimeAdaptiveExceptionalModuliPairs P R S).card : ℝ) * B) := by
      simpa only [IRfull, ISfull, E] using hmajorant
    _ ≤ ((H - 1 : ℕ) : ℝ) ^ 2 *
        (((taoDyadicPrimeBand R).card : ℝ) *
            ((taoDyadicPrimeBand S).card : ℝ) * A + K * B) := by
      gcongr

end

end Tao2026
