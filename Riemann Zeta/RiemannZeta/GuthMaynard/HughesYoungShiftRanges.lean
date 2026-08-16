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
