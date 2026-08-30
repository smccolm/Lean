import RiemannZeta.GuthMaynard.HughesYoungIntegratedConsumer
import RiemannZeta.GuthMaynard.HughesYoungGCD

open Complex Finset MeasureTheory Set
open scoped BigOperators Interval
open Classical

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young near and far shift ranges

This is the exact finite range split preceding Hughes--Young (65).  The
predicate records every hypothesis needed by the source-facing DFI consumer;
the complementary range is retained for integration-by-parts estimates.
-/

/-- The complete finite shift interval after the coprime reduction. -/
def hughesYoungShiftInterval (a b M N : ℕ) : Finset ℤ :=
  Finset.Icc (-(b * N : ℤ)) (a * M : ℤ)

/-- The shifts on which Hughes--Young apply DFI after the height transform
has restricted `T |r| / Y` to the smoothing parameter `P`. -/
def hughesYoungNearShifts
    (T P X Y : ℝ) (a b M N : ℕ) : Finset ℤ :=
  (hughesYoungShiftInterval a b M N).filter fun r =>
    r ≠ 0 ∧
      |(r : ℝ)| ≤ Y / 2 ∧
      T * (|(r : ℝ)| / Y) ≤ P ∧
      (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
      (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y)

/-- All nonzero shifts in the finite box not belonging to the DFI near
range.  These are estimated from the Fourier decay of the height weight. -/
def hughesYoungFarShifts
    (T P X Y : ℝ) (a b M N : ℕ) : Finset ℤ :=
  (hughesYoungShiftInterval a b M N).filter fun r =>
    r ≠ 0 ∧ r ∉ hughesYoungNearShifts T P X Y a b M N

theorem mem_hughesYoungNearShifts_iff
    {T P X Y : ℝ} {a b M N : ℕ} {r : ℤ} :
    r ∈ hughesYoungNearShifts T P X Y a b M N ↔
      r ∈ hughesYoungShiftInterval a b M N ∧
      r ≠ 0 ∧
      |(r : ℝ)| ≤ Y / 2 ∧
      T * (|(r : ℝ)| / Y) ≤ P ∧
      (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
      (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y) := by
  simp only [hughesYoungNearShifts, Finset.mem_filter]

theorem hughesYoungNearShifts_dfi_conditions
    {T P X Y : ℝ} {a b M N : ℕ} :
    ∀ r ∈ hughesYoungNearShifts T P X Y a b M N,
      r ≠ 0 ∧
      |(r : ℝ)| ≤ Y / 2 ∧
      T * (|(r : ℝ)| / Y) ≤ P ∧
      (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) ∧
      (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y) := by
  intro r hr
  exact (mem_hughesYoungNearShifts_iff.mp hr).2

theorem mem_hughesYoungFarShifts_iff
    {T P X Y : ℝ} {a b M N : ℕ} {r : ℤ} :
    r ∈ hughesYoungFarShifts T P X Y a b M N ↔
      r ∈ hughesYoungShiftInterval a b M N ∧ r ≠ 0 ∧
        r ∉ hughesYoungNearShifts T P X Y a b M N := by
  simp only [hughesYoungFarShifts, Finset.mem_filter]

/-- The DFI near range contains at most the integers in the symmetric
interval determined by the height cutoff `T * |r| / Y ≤ P`.  This is the
source-level counting input used when summing the pointwise DFI error. -/
theorem card_hughesYoungNearShifts_le
    {T P X Y : ℝ} {a b M N : ℕ}
    (hT : 0 < T) (hY : 0 < Y) (hP : 0 ≤ P) :
    (hughesYoungNearShifts T P X Y a b M N).card ≤
      2 * ⌊P * Y / T⌋₊ + 1 := by
  let K : ℕ := ⌊P * Y / T⌋₊
  have hR : 0 ≤ P * Y / T := by positivity
  have hsub : hughesYoungNearShifts T P X Y a b M N ⊆
      Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro r hr
    have hrange := (mem_hughesYoungNearShifts_iff.mp hr).2.2.2.1
    have habs : |(r : ℝ)| ≤ P * Y / T := by
      calc
        |(r : ℝ)| = T * (|(r : ℝ)| / Y) * Y / T := by field_simp
        _ ≤ P * Y / T := by gcongr
    have hnat : r.natAbs ≤ K := by
      dsimp only [K]
      exact Nat.le_floor (by simpa using habs)
    simp only [Finset.mem_Icc]
    constructor <;> omega
  calc
    _ ≤ (Finset.Icc (-(K : ℤ)) (K : ℤ)).card := Finset.card_le_card hsub
    _ = 2 * K + 1 := by
      rw [Int.card_Icc]
      have hform : (K : ℤ) + 1 - -(K : ℤ) = (K : ℤ) + 1 + (K : ℤ) := by ring
      rw [hform]
      have hnonneg : (0 : ℤ) ≤ (K : ℤ) + 1 + (K : ℤ) := by omega
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg hnonneg]
      norm_num
      ring
    _ = _ := rfl

/-- Because the near-shift family excludes zero, the sharp symmetric-interval
count has no extraneous central point.  This factor is what cancels the
physical height in the global DFI-error summation. -/
theorem card_hughesYoungNearShifts_le_two_mul_floor
    {T P X Y : ℝ} {a b M N : ℕ}
    (hT : 0 < T) (hY : 0 < Y) :
    (hughesYoungNearShifts T P X Y a b M N).card ≤
      2 * ⌊P * Y / T⌋₊ := by
  let K : ℕ := ⌊P * Y / T⌋₊
  have hsub : hughesYoungNearShifts T P X Y a b M N ⊆
      (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0 := by
    intro r hr
    rw [Finset.mem_erase]
    refine ⟨(mem_hughesYoungNearShifts_iff.mp hr).2.1, ?_⟩
    have hrange := (mem_hughesYoungNearShifts_iff.mp hr).2.2.2.1
    have habs : |(r : ℝ)| ≤ P * Y / T := by
      calc
        |(r : ℝ)| = T * (|(r : ℝ)| / Y) * Y / T := by field_simp
        _ ≤ P * Y / T := by gcongr
    have hnat : r.natAbs ≤ K := by
      dsimp only [K]
      exact Nat.le_floor (by simpa using habs)
    simp only [Finset.mem_Icc]
    constructor <;> omega
  calc
    _ ≤ ((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0).card :=
      Finset.card_le_card hsub
    _ = (Finset.Icc (-(K : ℤ)) (K : ℤ)).card - 1 :=
      Finset.card_erase_of_mem (by simp)
    _ = (2 * K + 1) - 1 := by
      congr 1
      rw [Int.card_Icc]
      have hform : (K : ℤ) + 1 - -(K : ℤ) = (K : ℤ) + 1 + (K : ℤ) := by ring
      rw [hform]
      have hnonneg : (0 : ℤ) ≤ (K : ℤ) + 1 + (K : ℤ) := by omega
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg hnonneg]
      norm_num
      ring
    _ = 2 * K := by omega
    _ = _ := rfl

/-- Exact disjoint partition of every nonzero finite-box shift into the
near and far families. -/
theorem sum_shiftInterval_eq_near_add_far
    {α : Type*} [AddCommMonoid α]
    (F : ℤ → α) (T P X Y : ℝ) (a b M N : ℕ) :
    (∑ r ∈ hughesYoungShiftInterval a b M N,
        if r = 0 then 0 else F r) =
      (∑ r ∈ hughesYoungNearShifts T P X Y a b M N, F r) +
      (∑ r ∈ hughesYoungFarShifts T P X Y a b M N, F r) := by
  classical
  let nonzero := (hughesYoungShiftInterval a b M N).filter fun r => r ≠ 0
  have hleft :
      (∑ r ∈ hughesYoungShiftInterval a b M N,
          if r = 0 then 0 else F r) = ∑ r ∈ nonzero, F r := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _hr
    by_cases hr0 : r = 0 <;> simp [hr0]
  have hsplit : nonzero =
      hughesYoungNearShifts T P X Y a b M N ∪
        hughesYoungFarShifts T P X Y a b M N := by
    ext r
    simp only [nonzero, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hr
      by_cases hn : r ∈ hughesYoungNearShifts T P X Y a b M N
      · exact Or.inl hn
      · exact Or.inr (mem_hughesYoungFarShifts_iff.mpr ⟨hr.1, hr.2, hn⟩)
    · intro hr
      rcases hr with hn | hf
      · exact ⟨(mem_hughesYoungNearShifts_iff.mp hn).1,
          (mem_hughesYoungNearShifts_iff.mp hn).2.1⟩
      · exact ⟨(mem_hughesYoungFarShifts_iff.mp hf).1,
          (mem_hughesYoungFarShifts_iff.mp hf).2.1⟩
  have hdisjoint : Disjoint
      (hughesYoungNearShifts T P X Y a b M N)
      (hughesYoungFarShifts T P X Y a b M N) := by
    rw [Finset.disjoint_left]
    intro r hn hf
    exact (mem_hughesYoungFarShifts_iff.mp hf).2.2 hn
  rw [hleft]
  rw [hsplit, Finset.sum_union hdisjoint]

end RiemannZeta.GuthMaynard
