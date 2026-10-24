import Dubon2026.SourceJointReductionIntegralCoordinates
import Dubon2026.SourceJointReductionLifts

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera inequality ->
joint chart integrality. The simultaneous integral ring is finite over
its intersection with the coordinate field. This extends the repository's
single-reduction finite-coordinate argument and avoids classification of
all valuation extensions. Degree equality and residue coordinate finiteness
are explicit upstream inputs, derived for the modular Kummer cover. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
open IsLocalRing

theorem isIntegral_joint_coordinate_intersection
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [∀ i, FiniteDimensional (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) =
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (u : F) (hu : ∀ i, u ∈ (R i).integers) :
    IsIntegral ↥((IntermediateField.adjoin L ({f} : Set F)).toSubfield.toSubring ⊓
      ⨅ i, (R i).integers.toSubring : Subring F) u := by
  classical
  let d : ι → ℕ := fun i => Module.finrank
    (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
  let yb : ∀ i, Fin (d i) → Fb i := fun i => (Module.finBasis _ (Fb i) : _)
  have hyb : ∀ i, LinearIndependent _ (yb i) := fun i => (Module.finBasis _ (Fb i)).linearIndependent
  choose z hzmem hzi hzl using fun τ : Σ i, Fin (d i) => exists_lift R hR τ.1 (yb τ.1 τ.2)
  let Oints : Subring F := ⨅ i, (R i).integers.toSubring
  let S : Subring F := (IntermediateField.adjoin L ({f} : Set F)).toSubfield.toSubring ⊓ Oints
  let O : Subalgebra S F := { Oints with algebraMap_mem' := fun c => c.2.2 }
  have hspan : O.toSubmodule = Submodule.span S (Set.range z) := by
    apply le_antisymm
    · intro v hv
      have hvR : ∀ i, v ∈ (R i).integers := Subring.mem_iInf.mp hv
      obtain ⟨r, hr, hsum⟩ := exists_joint_integral_coordinate_repr R f hf htr yb hyb z
        hzmem hzi hzl heq v hvR
      rw [hsum]
      refine Submodule.sum_mem _ fun τ _ => ?_
      exact Submodule.smul_mem _
        (⟨r τ, (hr τ).2, Subring.mem_iInf.mpr (hr τ).1⟩ : S)
        (Submodule.subset_span ⟨τ, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨τ, rfl⟩
      exact Subring.mem_iInf.mpr (hzmem τ)
  have hfg : O.toSubmodule.FG := by
    rw [hspan]
    exact Submodule.fg_span (Set.finite_range _)
  exact IsIntegral.of_mem_of_fg O hfg u (Subring.mem_iInf.mpr hu)

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
