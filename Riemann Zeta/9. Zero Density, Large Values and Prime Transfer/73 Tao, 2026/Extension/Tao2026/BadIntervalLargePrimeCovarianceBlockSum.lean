import Tao2026.BadIntervalLargePrimeBlockSum

/-!
# Two-band covariance block summation

This module is the finite dyadic summation consumer for Proposition 6.8.  It
keeps both shift variables, both prime bands, the improved covariance error,
and the exceptional-pair cardinality explicit.  No asymptotic error is hidden
in the combinatorial aggregation.
-/

namespace Tao2026

open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- Ordered distinct modulus pairs in two dyadic bands for which at least one
nontrivial divisor conductor is exceptional. -/
def taoLargePrimeExceptionalModuliPairs
    (P : Fin 1001 → ℕ) (R S : ℕ) : Finset (ℕ × ℕ) :=
  ((taoDyadicPrimeBand R).product (taoDyadicPrimeBand S)).filter fun pq =>
    pq.1 ≠ pq.2 ∧
      ¬TaoLargePrimePairUnexceptional P (0, pq.1) (0, pq.2)

theorem taoLargePrimeExceptionalModuliPairs_subset
    (P : Fin 1001 → ℕ) (R S : ℕ) :
    taoLargePrimeExceptionalModuliPairs P R S ⊆
      (taoDyadicPrimeBand R).product (taoDyadicPrimeBand S) := by
  exact Finset.filter_subset _ _

private theorem sum_taoLargePrime_twoBand_majorant_eq
    (P : Fin 1001 → ℕ) (R S H : ℕ) (A B : ℝ) :
    (∑ a ∈ (Finset.Ico 1 H).product (taoDyadicPrimeBand R),
      ∑ b ∈ (Finset.Ico 1 H).product (taoDyadicPrimeBand S),
        (A + if (a.2, b.2) ∈ taoLargePrimeExceptionalModuliPairs P R S
          then B else 0)) =
      ((H - 1 : ℕ) : ℝ) ^ 2 *
        (((taoDyadicPrimeBand R).card : ℝ) *
            ((taoDyadicPrimeBand S).card : ℝ) * A +
          ((taoLargePrimeExceptionalModuliPairs P R S).card : ℝ) * B) := by
  let E := taoLargePrimeExceptionalModuliPairs P R S
  have hE : E ⊆ (taoDyadicPrimeBand R).product (taoDyadicPrimeBand S) :=
    taoLargePrimeExceptionalModuliPairs_subset P R S
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

/-- Exact two-band covariance summation.  `A` is a uniform improved error,
`B` is a uniform crude joint bound on exceptional pairs, and `K` bounds the
number of exceptional ordered modulus pairs.  The factor `(H-1)^2` is the
literal multiplicity of the two independent shift variables. -/
theorem sum_taoLargePrimeCovariance_twoBand_le
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (R S H m' : ℕ) (hR : 2 ≤ R) (hS : 2 ≤ S)
    (hHR : H ≤ R - 1) (hHS : H ≤ S - 1)
    (hmR : ∀ p ∈ taoDyadicPrimeBand R, Nat.Coprime m' p)
    (hmS : ∀ q ∈ taoDyadicPrimeBand S, Nat.Coprime m' q)
    (A B K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hImproved : ∀ p ∈ taoDyadicPrimeBand R,
      ∀ q ∈ taoDyadicPrimeBand S, p ≠ q →
      TaoLargePrimePairUnexceptional P (0, p) (0, q) →
      taoLargePrimeCovarianceImprovedError P p q ≤ A)
    (hExceptionalCard :
      ((taoLargePrimeExceptionalModuliPairs P R S).card : ℝ) ≤ K)
    (hExceptional :
      ∀ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
      ∀ b ∈ (taoLargeAntiSieveIndices (S - 1) (2 * S - 1) H).filter
        (fun b => b.2 ≠ a.2),
      ¬TaoLargePrimePairUnexceptional P a b →
      taoLargePrimeJointProbability P hP m' a b ≤ B) :
    (∑ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
      ∑ b ∈ (taoLargeAntiSieveIndices (S - 1) (2 * S - 1) H).filter
        (fun b => b.2 ≠ a.2), taoLargePrimeCovariance P hP m' a b) ≤
      ((H - 1 : ℕ) : ℝ) ^ 2 *
        (((taoDyadicPrimeBand R).card : ℝ) *
            ((taoDyadicPrimeBand S).card : ℝ) * A + K * B) := by
  have hRpos : 0 < R := by omega
  have hSpos : 0 < S := by omega
  have hrangeR := taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand hRpos
  have hrangeS := taoLargeAntiSievePrimeRange_sub_eq_dyadicPrimeBand hSpos
  let IR := taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H
  let IS := taoLargeAntiSieveIndices (S - 1) (2 * S - 1) H
  let E := taoLargePrimeExceptionalModuliPairs P R S
  have hpointwise : ∀ a ∈ IR, ∀ b ∈ IS.filter (fun b => b.2 ≠ a.2),
      taoLargePrimeCovariance P hP m' a b ≤
        A + if (a.2, b.2) ∈ E then B else 0 := by
    intro a ha b hb
    have haData := mem_taoLargeAntiSieveIndices.mp ha
    have hbMem := (Finset.mem_filter.mp hb).1
    have hbData := mem_taoLargeAntiSieveIndices.mp hbMem
    have hpq : a.2 ≠ b.2 := (Finset.mem_filter.mp hb).2.symm
    have haBand : a.2 ∈ taoDyadicPrimeBand R := by
      rw [← hrangeR]
      exact mem_taoLargeAntiSievePrimeRange.mpr
        ⟨haData.2.2.1, haData.2.2.2.1, haData.2.2.2.2⟩
    have hbBand : b.2 ∈ taoDyadicPrimeBand S := by
      rw [← hrangeS]
      exact mem_taoLargeAntiSievePrimeRange.mpr
        ⟨hbData.2.2.1, hbData.2.2.2.1, hbData.2.2.2.2⟩
    by_cases hpair : TaoLargePrimePairUnexceptional P a b
    · have hpairZero : TaoLargePrimePairUnexceptional P (0, a.2) (0, b.2) := by
        simpa only [TaoLargePrimePairUnexceptional] using hpair
      have hcov := taoLargePrimeCovariance_le_unexceptionalErrors
        a b haData.2.2.1 hbData.2.2.1 hpq
          (Nat.not_dvd_of_pos_of_lt haData.1 (by omega))
          (Nat.not_dvd_of_pos_of_lt hbData.1 (by omega))
          (Nat.coprime_mul_iff_right.mpr ⟨hmR a.2 haBand, hmS b.2 hbBand⟩)
          P hP hpair
      have himp := hImproved a.2 haBand b.2 hbBand hpq hpairZero
      have hnotE : (a.2, b.2) ∉ E := by
        intro hE
        exact (Finset.mem_filter.mp hE).2.2 hpairZero
      rw [if_neg hnotE, add_zero]
      have hcov' : taoLargePrimeCovariance P hP m' a b ≤
          taoLargePrimeCovarianceImprovedError P a.2 b.2 := by
        simpa only [taoLargePrimeCovarianceImprovedError] using hcov
      exact hcov'.trans himp
    · have hE : (a.2, b.2) ∈ E := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨haBand, hbBand⟩, hpq, ?_⟩
        simpa only [TaoLargePrimePairUnexceptional] using hpair
      rw [if_pos hE]
      have hjoint := hExceptional a ha b hb hpair
      have hcov := taoLargePrimeCovariance_le_jointProbability P hP m' a b
      nlinarith [hcov.trans hjoint]
  have hfiltered :
      (∑ a ∈ IR, ∑ b ∈ IS.filter (fun b => b.2 ≠ a.2),
        taoLargePrimeCovariance P hP m' a b) ≤
      ∑ a ∈ IR, ∑ b ∈ IS,
        (A + if (a.2, b.2) ∈ E then B else 0) := by
    apply Finset.sum_le_sum
    intro a ha
    calc
      (∑ b ∈ IS.filter (fun b => b.2 ≠ a.2),
          taoLargePrimeCovariance P hP m' a b) ≤
        ∑ b ∈ IS.filter (fun b => b.2 ≠ a.2),
          (A + if (a.2, b.2) ∈ E then B else 0) := by
            exact Finset.sum_le_sum fun b hb => hpointwise a ha b hb
      _ ≤ ∑ b ∈ IS, (A + if (a.2, b.2) ∈ E then B else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro b hbIS hbnot
        split_ifs <;> positivity
  have hmajorant := sum_taoLargePrime_twoBand_majorant_eq P R S H A B
  calc
    (∑ a ∈ taoLargeAntiSieveIndices (R - 1) (2 * R - 1) H,
        ∑ b ∈ (taoLargeAntiSieveIndices (S - 1) (2 * S - 1) H).filter
          (fun b => b.2 ≠ a.2), taoLargePrimeCovariance P hP m' a b) ≤
      ∑ a ∈ IR, ∑ b ∈ IS,
        (A + if (a.2, b.2) ∈ E then B else 0) := hfiltered
    _ = ((H - 1 : ℕ) : ℝ) ^ 2 *
        (((taoDyadicPrimeBand R).card : ℝ) *
            ((taoDyadicPrimeBand S).card : ℝ) * A +
          ((taoLargePrimeExceptionalModuliPairs P R S).card : ℝ) * B) := by
      simpa only [IR, IS, E, taoLargeAntiSieveIndices, hrangeR, hrangeS] using hmajorant
    _ ≤ ((H - 1 : ℕ) : ℝ) ^ 2 *
        (((taoDyadicPrimeBand R).card : ℝ) *
            ((taoDyadicPrimeBand S).card : ℝ) * A + K * B) := by
      gcongr

end

end Tao2026
