import Dubon2026.CharacterCoefficients
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! # Coprime Möbius identities reused from Project 73

The six elementary arithmetic proofs below are ported from the existing
Tao2026/BurgessOptimization.lean prefix, with only namespace/import adaptation.
-/

namespace Dubon2026

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The sum of the Möbius function over all divisors is the indicator of one. -/
theorem sum_moebius_divisors_int_eq_indicator (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simpa only [ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.one_apply] using h

/-- Divisors of a gcd are precisely the divisors of the first argument that
also divide the second. -/
theorem divisors_gcd_eq_filter_dvd (q a : ℕ) (hq : q ≠ 0) :
    (Nat.gcd q a).divisors = q.divisors.filter (fun d => d ∣ a) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · rintro ⟨hd, hg⟩
    exact ⟨⟨dvd_trans hd (Nat.gcd_dvd_left q a), hq⟩,
      dvd_trans hd (Nat.gcd_dvd_right q a)⟩
  · rintro ⟨⟨hdq, _⟩, hda⟩
    exact ⟨Nat.dvd_gcd hdq hda, Nat.gcd_ne_zero_left hq⟩

/-- Möbius inversion expresses the coprimality indicator through divisors of
the gcd. -/
theorem sum_moebius_gcd_eq_coprimeIndicator (q a : ℕ) :
    (∑ d ∈ (Nat.gcd q a).divisors, ArithmeticFunction.moebius d) =
      if Nat.Coprime a q then 1 else 0 := by
  rw [sum_moebius_divisors_int_eq_indicator]
  simp only [Nat.Coprime, Nat.gcd_comm]

/-- Exact integer Möbius formula for the positive coprime multiplier count. -/
theorem card_coprimeMultipliers_eq_sum_moebius_div
    (q A : ℕ) (hq : q ≠ 0) :
    (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card : ℤ) =
      ∑ d ∈ q.divisors,
        ArithmeticFunction.moebius d * ((A / d : ℕ) : ℤ) := by
  calc
    (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card : ℤ) =
        ∑ a ∈ Finset.Ioc 0 A, if Nat.Coprime a q then 1 else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ = ∑ a ∈ Finset.Ioc 0 A,
          ∑ d ∈ (Nat.gcd q a).divisors,
            ArithmeticFunction.moebius d := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (sum_moebius_gcd_eq_coprimeIndicator q a).symm
    _ = ∑ a ∈ Finset.Ioc 0 A,
          ∑ d ∈ q.divisors,
            if d ∣ a then ArithmeticFunction.moebius d else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [divisors_gcd_eq_filter_dvd q a hq, Finset.sum_filter]
    _ = ∑ d ∈ q.divisors,
          ∑ a ∈ Finset.Ioc 0 A,
            if d ∣ a then ArithmeticFunction.moebius d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ q.divisors,
        ArithmeticFunction.moebius d * ((A / d : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      push_cast
      ring

/-- A complete positive period contains exactly `φ(q)` coprime integers. -/
theorem card_coprimeMultipliers_full_period (q : ℕ) :
    ((Finset.Ioc 0 q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [show Finset.Ioc 0 q = Finset.Ico 1 (1 + q) by ext x; simp; omega]
  simpa [Nat.coprime_comm] using Nat.filter_coprime_Ico_eq_totient q 1

/-- Dividing the complete-period Möbius formula by `q` gives the exact
totient density. -/
theorem sum_moebius_div_eq_totient_div (q : ℕ) (hq : q ≠ 0) :
    (∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
        (q.totient : ℝ) / (q : ℝ) := by
  have hcount := card_coprimeMultipliers_eq_sum_moebius_div q q hq
  rw [card_coprimeMultipliers_full_period] at hcount
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hcount
  simp only [Int.cast_natCast, Int.cast_mul, Int.cast_sum] at hcast
  rw [hcast]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    simp at hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  field_simp
  rw [mul_assoc, ← Nat.cast_mul, Nat.mul_comm d (q / d),
    Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1]

end

end Dubon2026
