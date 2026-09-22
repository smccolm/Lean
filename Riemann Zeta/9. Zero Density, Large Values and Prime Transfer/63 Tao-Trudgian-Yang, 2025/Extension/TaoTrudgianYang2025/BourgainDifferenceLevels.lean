import TaoTrudgianYang2025.BourgainDifferenceCounts
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Max

/-!
# Genuine dyadic selection for Bourgain's difference multiplicities

The selected set consists of actual integer differences with positive
count in a single dyadic band. The loss is explicitly `log₂ |W| + 1`.
No zeta superlevel selection or analytic Bourgain dichotomy is asserted.
-/

open Finset
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The positive difference counts of a fixed dyadic size. -/
def bourgainDifferenceLevel (W : Finset ℝ) (j : ℕ) : Finset ℤ :=
  (bourgainDifferenceSupport W).filter fun ℓ =>
    0 < bourgainDifferenceCount W ℓ ∧ Nat.log 2 (bourgainDifferenceCount W ℓ) = j

/-- Exact dyadic inequalities on the selected, actual count. -/
theorem bourgainDifferenceLevel_bounds {W : Finset ℝ} {j : ℕ} {ℓ : ℤ}
    (hℓ : ℓ ∈ bourgainDifferenceLevel W j) :
    2 ^ j ≤ bourgainDifferenceCount W ℓ ∧
      bourgainDifferenceCount W ℓ < 2 ^ (j + 1) := by
  have hc := (Finset.mem_filter.mp hℓ).2
  rw [← hc.2]
  exact ⟨Nat.pow_log_le_self 2 (Nat.ne_of_gt hc.1),
    Nat.lt_pow_succ_log_self (by norm_num) _⟩

/-- The dyadic definition is equivalent to the literal half-open count band. -/
theorem mem_bourgainDifferenceLevel_iff (W : Finset ℝ) (j : ℕ) (ℓ : ℤ) :
    ℓ ∈ bourgainDifferenceLevel W j ↔
      ℓ ∈ bourgainDifferenceSupport W ∧
        2 ^ j ≤ bourgainDifferenceCount W ℓ ∧
        bourgainDifferenceCount W ℓ < 2 ^ (j + 1) := by
  constructor
  · intro h
    exact ⟨(Finset.mem_filter.mp h).1, bourgainDifferenceLevel_bounds h⟩
  · rintro ⟨hs, hlo, hhi⟩
    apply Finset.mem_filter.mpr
    exact ⟨hs, lt_of_lt_of_le (Nat.pow_pos (by norm_num)) hlo,
      Nat.log_eq_of_pow_le_of_lt_pow hlo hhi⟩

/-- The occupied levels fit into the asserted logarithmic range. -/
theorem bourgainDifferenceLevel_index_le {W : Finset ℝ}
    (hsep : IsSeparated 2 W) {j : ℕ}
    (hne : (bourgainDifferenceLevel W j).Nonempty) :
    j ≤ Nat.log 2 W.card := by
  obtain ⟨ℓ, hℓ⟩ := hne
  have hc := (Finset.mem_filter.mp hℓ).2
  rw [← hc.2]
  exact Nat.log_mono_right (bourgainDifferenceCount_le_card hsep ℓ)

/-- Each genuine dyadic level has the sharp cardinality bound supplied
by the total pair count. -/
theorem bourgainDifferenceLevel_card_le (W : Finset ℝ) (j : ℕ) :
    2 ^ j * (bourgainDifferenceLevel W j).card ≤ 2 * W.card ^ 2 := by
  calc
    _ = ∑ _ℓ ∈ bourgainDifferenceLevel W j, 2 ^ j := by simp [mul_comm]
    _ ≤ ∑ ℓ ∈ bourgainDifferenceLevel W j, bourgainDifferenceCount W ℓ :=
      Finset.sum_le_sum fun _ hℓ => (bourgainDifferenceLevel_bounds hℓ).1
    _ ≤ _ := bourgainDifferenceCount_sum_le W _

/-- Exact weighted decomposition. Zero-count cover points contribute zero;
they are not assigned to a fake positive level. -/
theorem bourgainDifferenceLevel_sum_eq {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (f : ℤ → ℝ) :
    (∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
      ∑ ℓ ∈ bourgainDifferenceLevel W j,
        (bourgainDifferenceCount W ℓ : ℝ) * f ℓ) =
      ∑ ℓ ∈ bourgainDifferenceSupport W,
        (bourgainDifferenceCount W ℓ : ℝ) * f ℓ := by
  classical
  let S := (bourgainDifferenceSupport W).filter fun ℓ => 0 < bourgainDifferenceCount W ℓ
  have hmap : ∀ ℓ ∈ S,
      Nat.log 2 (bourgainDifferenceCount W ℓ) ∈ Finset.range (Nat.log 2 W.card + 1) := by
    intro ℓ hℓ
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.log_mono_right (bourgainDifferenceCount_le_card hsep ℓ)))
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap
    (fun ℓ => (bourgainDifferenceCount W ℓ : ℝ) * f ℓ)
  have hlevels : ∀ j,
      S.filter (fun ℓ => Nat.log 2 (bourgainDifferenceCount W ℓ) = j) =
        bourgainDifferenceLevel W j := by
    intro j
    ext ℓ
    simp [S, bourgainDifferenceLevel, and_assoc]
  simp_rw [hlevels] at hfiber
  rw [hfiber]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro ℓ hℓ hn
  have hz : bourgainDifferenceCount W ℓ = 0 := by
    have : ¬ 0 < bourgainDifferenceCount W ℓ := by
      intro hp
      exact hn (Finset.mem_filter.mpr ⟨hℓ, hp⟩)
    omega
  simp [hz]

/-- A real weighted mass selects a genuine dyadic level with an explicit
logarithmic loss. This is finite pigeonholing, not an assumed selector. -/
theorem bourgainDifferenceLevel_exists_heavy {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (f : ℤ → ℝ) :
    ∃ j ∈ Finset.range (Nat.log 2 W.card + 1),
      (∑ ℓ ∈ bourgainDifferenceSupport W,
        (bourgainDifferenceCount W ℓ : ℝ) * f ℓ) ≤
          (Nat.log 2 W.card + 1 : ℕ) *
            ∑ ℓ ∈ bourgainDifferenceLevel W j,
              (bourgainDifferenceCount W ℓ : ℝ) * f ℓ := by
  classical
  let mass := fun j => ∑ ℓ ∈ bourgainDifferenceLevel W j,
    (bourgainDifferenceCount W ℓ : ℝ) * f ℓ
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image
    (Finset.range (Nat.log 2 W.card + 1)) mass (by simp)
  refine ⟨j, hj, ?_⟩
  rw [← bourgainDifferenceLevel_sum_eq hsep f]
  calc
    _ ≤ ∑ _i ∈ Finset.range (Nat.log 2 W.card + 1), mass j :=
      Finset.sum_le_sum fun i hi => hmax i hi
    _ = _ := by simp [mass]

/-- Positive nonnegative weighted mass produces a nonempty actual integer
level, its size control, and the unweighted mass lower bound needed before
zeta superlevel pigeonholing. All losses remain finite and explicit. -/
theorem bourgainDifferenceLevel_select {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (f : ℤ → ℝ)
    (hf : ∀ ℓ ∈ bourgainDifferenceSupport W, 0 ≤ f ℓ)
    (hmass : 0 < ∑ ℓ ∈ bourgainDifferenceSupport W,
      (bourgainDifferenceCount W ℓ : ℝ) * f ℓ) :
    ∃ j ∈ Finset.range (Nat.log 2 W.card + 1),
      (bourgainDifferenceLevel W j).Nonempty ∧
      2 ^ j ≤ W.card ∧
      2 ^ j * (bourgainDifferenceLevel W j).card ≤ 2 * W.card ^ 2 ∧
      (∑ ℓ ∈ bourgainDifferenceSupport W,
        (bourgainDifferenceCount W ℓ : ℝ) * f ℓ) ≤
        (Nat.log 2 W.card + 1 : ℕ) * (2 : ℝ) ^ (j + 1) *
          ∑ ℓ ∈ bourgainDifferenceLevel W j, f ℓ := by
  obtain ⟨j, hj, hheavy⟩ := bourgainDifferenceLevel_exists_heavy hsep f
  have hne : (bourgainDifferenceLevel W j).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty, mul_zero] at hheavy
    linarith
  have hpow : 2 ^ j ≤ W.card := by
    obtain ⟨ℓ, hℓ⟩ := hne
    exact (bourgainDifferenceLevel_bounds hℓ).1.trans (bourgainDifferenceCount_le_card hsep ℓ)
  refine ⟨j, hj, hne, hpow, bourgainDifferenceLevel_card_le W j, hheavy.trans ?_⟩
  have hsum :
      (∑ ℓ ∈ bourgainDifferenceLevel W j,
        (bourgainDifferenceCount W ℓ : ℝ) * f ℓ) ≤
        (2 : ℝ) ^ (j + 1) * ∑ ℓ ∈ bourgainDifferenceLevel W j, f ℓ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ℓ hℓ
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast (bourgainDifferenceLevel_bounds hℓ).2.le
    · exact hf ℓ (Finset.mem_filter.mp hℓ).1
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum
    (by positivity : (0 : ℝ) ≤ (Nat.log 2 W.card + 1 : ℕ))

end TaoTrudgianYang2025
