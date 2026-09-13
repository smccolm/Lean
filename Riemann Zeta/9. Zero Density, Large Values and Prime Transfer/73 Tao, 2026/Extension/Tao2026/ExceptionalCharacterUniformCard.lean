import Tao2026.ExceptionalCharacterCofactorAggregate

/-!
# Uniform cardinality form of Tao's Lemma 5.1

The self-improving truncation argument has an absolute output constant: it
does not depend on the common conductor factor or on the selected separated
exceptional family.  This module exposes that quantifier order explicitly,
which is required when Proposition 6.8 sums over a growing set of fixed
primes.
-/

namespace Tao2026

open Filter
open scoped Classical Topology

noncomputable section

/-- One cardinality constant works for every eventually squarefree common
factor and every eventually separated family consisting of exceptional
characters. -/
theorem exists_uniform_eventually_exceptionalFamily_card_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (q₁ : ℕ → ℕ)
        (W : ∀ Z, Finset (TaoExceptionalCharacterDatum (q₁ Z) Z)),
        (∀ᶠ Z : ℕ in atTop, Squarefree (q₁ Z)) →
        (∀ᶠ Z : ℕ in atTop, IsSeparatedTaoExceptionalFamily (W Z)) →
        (∀ᶠ Z : ℕ in atTop,
          ∀ a ∈ W Z, taoExceptionalPrimeCharacterThreshold Z ≤
            ‖finiteNormalizedPrimeBandSum Z a.value‖) →
        ∀ᶠ Z : ℕ in atTop,
          ((W Z).card : ℝ) ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ) := by
  classical
  obtain ⟨M, hMpos, hMoment⟩ :=
    exists_uniform_eventually_exceptionalFamily_secondMoment_le_of_explicitBurgess
      hC hburgess
  let A : ℝ := M + 2
  have hApos : 0 < A := by dsimp [A]; linarith
  refine ⟨A, hApos, ?_⟩
  intro q₁ W hq₁ hsep hexceptional
  let N : ℕ → ℕ := fun Z =>
    Nat.floor (A * (Z : ℝ) ^ (2 / 125 : ℝ))
  let V : ∀ Z, Finset (TaoExceptionalCharacterDatum (q₁ Z) Z) := fun Z =>
    taoTruncateFinset (N Z) (W Z)
  have hVsubset : ∀ Z, V Z ⊆ W Z := fun Z => by
    dsimp [V]
    exact taoTruncateFinset_subset _ _
  have hVcardEq : ∀ Z, (V Z).card = min (N Z) (W Z).card := fun Z => by
    dsimp [V]
    exact card_taoTruncateFinset _ _
  have hVcard : ∀ᶠ Z : ℕ in atTop,
      ((V Z).card : ℝ) ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ) := by
    filter_upwards [] with Z
    have harg : 0 ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ) := by positivity
    calc
      ((V Z).card : ℝ) ≤ (N Z : ℝ) := by
        exact_mod_cast (hVcardEq Z ▸ Nat.min_le_left (N Z) (W Z).card)
      _ ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ) := by
        dsimp [N]
        exact Nat.floor_le harg
  have hVsep : ∀ᶠ Z : ℕ in atTop,
      IsSeparatedTaoExceptionalFamily (V Z) := by
    filter_upwards [hsep] with Z hsepZ
    intro a ha b hb hba
    exact hsepZ a (hVsubset Z ha) b (hVsubset Z hb) hba
  have hVMoment := hMoment q₁ V hq₁ hVsep hVcard
  filter_upwards [hVMoment, hexceptional,
    eventually_ge_atTop (1 : ℕ)] with Z hVMomentZ hexceptionalZ hZ
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hxpos : 0 < (Z : ℝ) ^ (2 / 125 : ℝ) :=
    Real.rpow_pos_of_pos hZpos _
  have hxone : 1 ≤ (Z : ℝ) ^ (2 / 125 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hZ) (by norm_num)
  by_contra hnot
  push Not at hnot
  have harg : 0 ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ) := by positivity
  have hNlt : N Z < (W Z).card := by
    apply_mod_cast lt_of_le_of_lt (Nat.floor_le harg) hnot
  have hVcardN : (V Z).card = N Z := by
    rw [hVcardEq, Nat.min_eq_left hNlt.le]
  have hmarkov : ((V Z).card : ℝ) *
      taoExceptionalPrimeCharacterThreshold Z ^ (2 : ℕ) ≤
        ∑ a ∈ V Z, ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 := by
    calc
      ((V Z).card : ℝ) *
          taoExceptionalPrimeCharacterThreshold Z ^ (2 : ℕ) =
        ∑ _a ∈ V Z,
          taoExceptionalPrimeCharacterThreshold Z ^ (2 : ℕ) := by simp
      _ ≤ ∑ a ∈ V Z,
          ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        have haExceptional := hexceptionalZ a (hVsubset Z ha)
        nlinarith [taoExceptionalPrimeCharacterThreshold_nonneg Z,
          norm_nonneg (finiteNormalizedPrimeBandSum Z a.value)]
  have hscaled : ((V Z).card : ℝ) *
      (Z : ℝ) ^ (-(2 : ℝ) / 125) ≤ M := by
    rw [← taoExceptionalPrimeCharacterThreshold_pow_two]
    exact hmarkov.trans hVMomentZ
  have hVbound : ((V Z).card : ℝ) ≤
      M * (Z : ℝ) ^ (2 / 125 : ℝ) := by
    calc
      ((V Z).card : ℝ) =
          (((V Z).card : ℝ) * (Z : ℝ) ^ (-(2 : ℝ) / 125)) *
            (Z : ℝ) ^ (2 / 125 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hZpos]
        norm_num
      _ ≤ M * (Z : ℝ) ^ (2 / 125 : ℝ) :=
        mul_le_mul_of_nonneg_right hscaled hxpos.le
  have hfloorLower : (M + 1) * (Z : ℝ) ^ (2 / 125 : ℝ) ≤ N Z := by
    have hfloor := Nat.sub_one_lt_floor
      (A * (Z : ℝ) ^ (2 / 125 : ℝ))
    change A * (Z : ℝ) ^ (2 / 125 : ℝ) - 1 < (N Z : ℝ) at hfloor
    apply le_of_lt
    calc
      (M + 1) * (Z : ℝ) ^ (2 / 125 : ℝ) ≤
          A * (Z : ℝ) ^ (2 / 125 : ℝ) - 1 := by
        dsimp [A]
        nlinarith
      _ < (N Z : ℝ) := hfloor
  rw [hVcardN] at hVbound
  have : (M + 1) * (Z : ℝ) ^ (2 / 125 : ℝ) ≤
      M * (Z : ℝ) ^ (2 / 125 : ℝ) := hfloorLower.trans hVbound
  nlinarith

end

end Tao2026
