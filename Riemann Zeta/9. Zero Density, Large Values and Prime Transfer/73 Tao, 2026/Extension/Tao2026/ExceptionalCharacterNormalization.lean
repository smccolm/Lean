import Tao2026.ExceptionalCharacterScales
import PrimeNumberTheoremAnd.Consequences

/-!
# Prime-band normalization for Lemma 5.1

The finite Bombieri--Halász--Montgomery estimate is normalized by the exact
cardinality of the half-open band of primes `[Z,2Z)`.  This file identifies
that cardinality with `π′(2Z)-π′(Z)`, derives its prime-number-theorem
asymptotic, and records the concrete eventual lower bound needed to control
the denominator in the remaining Lemma 5.1 argument.
-/

namespace Tao2026

open Filter Asymptotics
open scoped Nat.Prime

/-- The half-open dyadic prime band is the difference of two filtered ranges. -/
theorem taoDyadicPrimeBand_eq_sdiff (Z : ℕ) :
    taoDyadicPrimeBand Z =
      (Finset.range (2 * Z)).filter Nat.Prime \
        (Finset.range Z).filter Nat.Prime := by
  ext p
  simp only [taoDyadicPrimeBand, Finset.mem_filter, Finset.mem_Ico,
    Finset.mem_sdiff, Finset.mem_range]
  constructor
  · rintro ⟨⟨hZ, h2Z⟩, hp⟩
    exact ⟨⟨h2Z, hp⟩, fun hpZ => (Nat.not_lt_of_ge hZ) hpZ.1⟩
  · rintro ⟨⟨h2Z, hp⟩, hnot⟩
    have hZ : Z ≤ p := by
      by_contra hn
      exact hnot ⟨Nat.lt_of_not_ge hn, hp⟩
    exact ⟨⟨hZ, h2Z⟩, hp⟩

/-- Exact cardinality of Tao's half-open dyadic prime band. -/
theorem card_taoDyadicPrimeBand_eq_primeCounting'_sub (Z : ℕ) :
    (taoDyadicPrimeBand Z).card =
      Nat.primeCounting' (2 * Z) - Nat.primeCounting' Z := by
  rw [taoDyadicPrimeBand_eq_sdiff, Finset.card_sdiff_of_subset]
  · rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
    rfl
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩

/-- The inclusive and strict prime-counting functions differ by the indicator
of primality at the endpoint. -/
theorem primeCounting_cast_sub_primeCounting'_cast (n : ℕ) :
    (Nat.primeCounting n : ℝ) - Nat.primeCounting' n =
      if n.Prime then 1 else 0 := by
  simp [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]

/-- The pinned PNT, restricted from real inputs to natural inputs. -/
theorem primeCounting_nat_asymptotic :
    (fun n : ℕ => (Nat.primeCounting n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) / Real.log n) := by
  have h := pi_alt'.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  convert h using 1
  · ext n
    simp

/-- The strict prime-counting function has the same PNT asymptotic. -/
theorem primeCounting'_nat_asymptotic :
    (fun n : ℕ => (Nat.primeCounting' n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) / Real.log n) := by
  let g : ℕ → ℝ := fun n => (n : ℝ) / Real.log n
  have hpi : (fun n : ℕ => (Nat.primeCounting n : ℝ)) ~[atTop] g :=
    primeCounting_nat_asymptotic
  have hpiTop : Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  have hgTop : Tendsto g atTop atTop := hpi.tendsto_atTop hpiTop
  have hnormGTop : Tendsto (norm ∘ g) atTop atTop :=
    tendsto_norm_atTop_atTop.comp hgTop
  have herrBigO :
      (fun n : ℕ => (Nat.primeCounting n : ℝ) - Nat.primeCounting' n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    rw [primeCounting_cast_sub_primeCounting'_cast]
    split <;> simp
  have herrSmall :
      (fun n : ℕ => (Nat.primeCounting n : ℝ) - Nat.primeCounting' n) =o[atTop] g :=
    herrBigO.trans_isLittleO (isLittleO_const_left.mpr (Or.inr hnormGTop))
  have h := hpi.sub_isLittleO herrSmall
  convert h using 1
  ext n
  simp only [Pi.sub_apply]
  ring

/-- PNT at the doubled natural argument, normalized at the original scale. -/
theorem primeCounting'_two_mul_asymptotic :
    (fun n : ℕ => (Nat.primeCounting' (2 * n) : ℝ)) ~[atTop]
      (fun n : ℕ => 2 * ((n : ℝ) / Real.log n)) := by
  have hprime :=
    primeCounting'_nat_asymptotic.comp_tendsto tendsto_two_mul_nat_atTop
  have hlog :
      (fun n : ℕ => Real.log (2 * n : ℕ)) ~[atTop]
        (fun n : ℕ => Real.log n) :=
    isEquivalent_of_tendsto_one tendsto_log_two_mul_div_log_nat
  have hnum :
      (fun n : ℕ => ((2 * n : ℕ) : ℝ)) ~[atTop]
        (fun n : ℕ => ((2 * n : ℕ) : ℝ)) := IsEquivalent.refl
  have hscale := hnum.div hlog
  apply hprime.trans
  convert hscale using 1
  ext n
  norm_num
  ring

/-- The real-valued difference `π′(2Z)-π′(Z)` is asymptotic to `Z/log Z`. -/
theorem primeCounting'_dyadicDifference_asymptotic :
    (fun n : ℕ =>
      (Nat.primeCounting' (2 * n) : ℝ) - Nat.primeCounting' n) ~[atTop]
      (fun n : ℕ => (n : ℝ) / Real.log n) := by
  let g : ℕ → ℝ := fun n => (n : ℝ) / Real.log n
  have htwo :
      (fun n : ℕ => (Nat.primeCounting' (2 * n) : ℝ)) ~[atTop]
        (fun n : ℕ => 2 * g n) := by
    simpa [g] using primeCounting'_two_mul_asymptotic
  have hone :
      (fun n : ℕ => (Nat.primeCounting' n : ℝ)) ~[atTop] g := by
    simpa [g] using primeCounting'_nat_asymptotic
  have htwoError :
      (fun n : ℕ => (Nat.primeCounting' (2 * n) : ℝ) - 2 * g n) =o[atTop] g :=
    htwo.isLittleO.of_const_mul_right
  have herror := htwoError.sub hone.isLittleO
  rw [IsEquivalent]
  convert herror using 1
  ext n
  simp only [Pi.sub_apply]
  ring

/-- Tao's exact dyadic-prime cardinality is asymptotic to `Z/log Z`. -/
theorem card_taoDyadicPrimeBand_asymptotic :
    (fun n : ℕ => ((taoDyadicPrimeBand n).card : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) / Real.log n) := by
  apply primeCounting'_dyadicDifference_asymptotic.congr_left
  filter_upwards with n
  rw [card_taoDyadicPrimeBand_eq_primeCounting'_sub, Nat.cast_sub]
  exact Nat.monotone_primeCounting' (by omega)

/-- A concrete eventual lower bound for the exact denominator in the
normalized BHM estimate. -/
theorem eventually_nat_div_two_log_le_card_taoDyadicPrimeBand :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / (2 * Real.log n) ≤ ((taoDyadicPrimeBand n).card : ℝ) := by
  let g : ℕ → ℝ := fun n => (n : ℝ) / Real.log n
  rcases card_taoDyadicPrimeBand_asymptotic.exists_eq_mul with ⟨φ, hφ, heq⟩
  have hφLower : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) < φ n :=
    hφ.eventually (Ioi_mem_nhds (by norm_num))
  filter_upwards [heq, hφLower, eventually_ge_atTop (2 : ℕ)] with n hn hφn hnTwo
  have hg : 0 ≤ g n := by
    dsimp [g]
    positivity
  calc
    (n : ℝ) / (2 * Real.log n) = (1 / 2 : ℝ) * g n := by
      dsimp [g]
      ring
    _ ≤ φ n * g n := mul_le_mul_of_nonneg_right hφn.le hg
    _ = ((taoDyadicPrimeBand n).card : ℝ) := hn.symm

end Tao2026
