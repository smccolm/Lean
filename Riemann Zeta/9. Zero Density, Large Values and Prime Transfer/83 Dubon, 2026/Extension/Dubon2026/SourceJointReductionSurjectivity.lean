import Dubon2026.SourceJointReductionLifts

/-! DUB-17/18 -> Kummer power lifting -> genus inequality -> monic torsion
of residue chart quotients. Arbitrary simultaneous residue vectors lift to
the common integral ring by the already proved finite valuation approximation.
This is the actual lifting input to clearing their coordinate denominators. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
open IsLocalRing

theorem exists_joint_residue_lift
    {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers) (h : ∀ i, Fb i) :
    ∃ z : F, ∃ hz : ∀ i, z ∈ (R i).integers, ∀ i, (R i).residue ⟨z, hz i⟩ = h i := by
  classical
  choose a ha using fun i => (R i).residue_surjective (h i)
  obtain ⟨z, hz⟩ := ValuationApproximation.exists_forall_mem_and_sub_mem_nonunits'
    (fun i => (R i).integers) (fun i j hle => hR (integers_eq_of_le (R i) (R j) hle))
    (fun i => (a i : F)) (fun i => (a i).2)
  refine ⟨z, fun i => (hz i).1, fun i => ?_⟩
  have h0 := residue_eq_zero_of_mem_nonunits (R i)
    (sub_mem (hz i).1 (a i).2) (hz i).2
  have he : (⟨z - a i, sub_mem (hz i).1 (a i).2⟩ : (R i).integers) =
      ⟨z, (hz i).1⟩ - a i := rfl
  rw [he, map_sub, sub_eq_zero] at h0
  exact h0.trans (ha i)

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
