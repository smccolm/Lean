import Dubon2026.SourceReductionRegularComparison
import Dubon2026.SourceValuationResidueApproximationR2

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera inequality ->
simultaneous residue dimension. The existing finite valuation approximation
gives separately supported residue lifts. Existing single-reduction frame
independence and native product independence give the joint frame.
Adapted from frozen Apache-2.0 FLT source, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
open IsLocalRing
variable {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
variable {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

theorem residue_eq_zero_of_mem_nonunits {Fbar : Type*} [Field Fbar]
    [Algebra (ResidueField A) Fbar] (R : RegularProlongation A F Fbar)
    {w : F} (hw : w ∈ R.integers) (hn : w ∈ R.integers.nonunits) :
    R.residue ⟨w, hw⟩ = 0 :=
  (residue_eq_zero_iff R _).mpr
    ((R.integers.valuation_lt_one_iff ⟨w, hw⟩).mpr
      ((R.integers.mem_nonunits_iff).mp hn))

variable [Fintype ι] (R : ∀ i, RegularProlongation A F (Fb i))
  (hR : Function.Injective fun i => (R i).integers)
include hR

theorem exists_lift (i : ι) (x : Fb i) :
    ∃ z : F, ∃ hz : ∀ l, z ∈ (R l).integers,
      (R i).residue ⟨z, hz i⟩ = x ∧ ∀ l, l ≠ i → (R l).residue ⟨z, hz l⟩ = 0 := by
  classical
  obtain ⟨y, hy⟩ := (R i).residue_surjective x
  let a : ι → F := fun l => if l = i then (y : F) else 0
  have ha : ∀ l, a l ∈ (R l).integers := by
    intro l; by_cases hl : l = i
    · subst hl; simp only [a, if_pos rfl]; exact y.2
    · simp only [a, if_neg hl]; exact zero_mem _
  obtain ⟨z, hz⟩ := ValuationApproximation.exists_forall_mem_and_sub_mem_nonunits'
    (fun l => (R l).integers) (fun l l' hle => hR (integers_eq_of_le (R l) (R l') hle)) a ha
  refine ⟨z, fun l => (hz l).1, ?_, ?_⟩
  · have h0 := residue_eq_zero_of_mem_nonunits (R i) (sub_mem (hz i).1 (ha i)) (hz i).2
    have e : (⟨z - a i, sub_mem (hz i).1 (ha i)⟩ : (R i).integers) = ⟨z, (hz i).1⟩ - y := by
      apply Subtype.ext; simp [a, if_pos rfl]
    rw [e, map_sub, sub_eq_zero] at h0; rw [h0, hy]
  · intro l hl
    have h0 := residue_eq_zero_of_mem_nonunits (R l) (sub_mem (hz l).1 (ha l)) (hz l).2
    have e : (⟨z - a l, sub_mem (hz l).1 (ha l)⟩ : (R l).integers) = ⟨z, (hz l).1⟩ := by
      apply Subtype.ext; simp [a, if_neg hl]
    rwa [e] at h0


end
end Dubon2026.SourceCurve.RegularProlongation.Joint
