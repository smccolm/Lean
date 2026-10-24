import Dubon2026.SourceJointReductionCoordinateBasis

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera inequality ->
simultaneous residue dimension. The actual joint residue span preserves
finite-space dimension when the coordinate degrees sum to the original
degree. Existing constant normalizers, adapted bases, coordinate powers
and native fraction-ring independence are reused. Finite residue coordinate
degrees are explicit upstream inputs, supplied by the actual modular fields.
Adapted from frozen Apache-2.0 FLT source, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
open IsLocalRing

variable {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

variable (R : ∀ i, RegularProlongation A F (Fb i))
  [DecidableEq ι]
  (f : F) (hf : ∀ i, f ∈ (R i).integers)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  {d : ι → ℕ} (yb : ∀ i, Fin (d i) → Fb i)
  (hyb : ∀ i, LinearIndependent
    (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
    (yb i))
  (z : (Σ i, Fin (d i)) → F) (hzmem : ∀ τ l, z τ ∈ (R l).integers)
  (hzi : ∀ τ : Σ i, Fin (d i), (R τ.1).residue ⟨z τ, hzmem τ τ.1⟩ = yb τ.1 τ.2)
  (hzl : ∀ (τ : Σ i, Fin (d i)) l, l ≠ τ.1 → (R l).residue ⟨z τ, hzmem τ l⟩ = 0)
  [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
  (heq : ∑ i, d i = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)

include htr hyb hzi hzl in

omit [Fintype ι] [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F] in
theorem linearIndependent_adjoinField_z :
    LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z := by
  exact linearIndependent_adjoinField_of_powers f z
    (linearIndependent_coe_joint R
      (fun p : ℕ × (Σ i, Fin (d i)) => f ^ p.1 * z p.2)
      (fun p l => mul_mem (pow_mem (hf l) _) (hzmem p.2 l))
      (linearIndependent_jointRes_jointFrame R f hf htr yb hyb z hzmem hzi hzl))

include htr hyb hzi hzl heq in

theorem exists_repr_adjoinField_z (v : F) :
    ∃ r : (Σ i, Fin (d i)) → IntermediateField.adjoin L ({f} : Set F),
      v = ∑ τ, (r τ : F) * z τ := by
  set E := IntermediateField.adjoin L ({f} : Set F)
  have hcard : Fintype.card (Σ i, Fin (d i)) = Module.finrank E F := by
    rw [Fintype.card_sigma]; simp [heq]
  let B : Module.Basis (Σ i, Fin (d i)) E F :=
    basisOfLinearIndependentOfCardEqFinrank' _
      (linearIndependent_adjoinField_z R f hf htr yb hyb z hzmem hzi hzl) hcard
  refine ⟨fun τ => B.repr v τ, ?_⟩
  conv_lhs => rw [← B.sum_repr v]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', IntermediateField.smul_def, smul_eq_mul]


end
end Dubon2026.SourceCurve.RegularProlongation.Joint
