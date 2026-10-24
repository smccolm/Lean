import Dubon2026.SourceJointReductionIndependent
import Dubon2026.SourceReductionFrame

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

variable (R : ∀ i, RegularProlongation A F (Fb i))
variable [DecidableEq ι]
variable (f : F) (hf : ∀ i, f ∈ (R i).integers)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))

include htr in

omit [DecidableEq ι] in
theorem linearIndependent_residue_perFrame (i : ι) {n : ℕ} (y : Fin n → Fb i)
    (hy : LinearIndependent
      (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) y) :
    LinearIndependent (ResidueField A)
      (fun p : ℕ × Fin n => ((R i).residue ⟨f, hf i⟩) ^ p.1 * y p.2) := by
  choose z hz using fun j => (R i).residue_surjective (y j)
  have hzind : LinearIndependent
      (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
      (fun j => (R i).residue (z j)) := by simpa only [hz] using hy
  have h := linearIndependent_residue_frame (R i) ⟨f, hf i⟩ (htr i) z hzind
  simpa only [frame, map_mul, map_pow, hz] using h

variable {d : ι → ℕ} (yb : ∀ i, Fin (d i) → Fb i)
  (hyb : ∀ i, LinearIndependent
    (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
    (yb i))
  (z : (Σ i, Fin (d i)) → F) (hzmem : ∀ τ l, z τ ∈ (R l).integers)
  (hzi : ∀ τ : Σ i, Fin (d i), (R τ.1).residue ⟨z τ, hzmem τ τ.1⟩ = yb τ.1 τ.2)
  (hzl : ∀ (τ : Σ i, Fin (d i)) l, l ≠ τ.1 → (R l).residue ⟨z τ, hzmem τ l⟩ = 0)

include hzi hzl in

theorem jointRes_jointFrame_eq_single (p : ℕ × (Σ i, Fin (d i))) :
    jointRes R (fun p : ℕ × (Σ i, Fin (d i)) => f ^ p.1 * z p.2)
        (fun p l => mul_mem (pow_mem (hf l) _) (hzmem p.2 l)) p =
      Pi.single p.2.1 (((R p.2.1).residue ⟨f, hf p.2.1⟩) ^ p.1 * yb p.2.1 p.2.2) := by
  funext l
  simp only [jointRes]
  have e : (⟨f ^ p.1 * z p.2, mul_mem (pow_mem (hf l) _) (hzmem p.2 l)⟩ : (R l).integers)
      = ⟨f, hf l⟩ ^ p.1 * ⟨z p.2, hzmem p.2 l⟩ := by apply Subtype.ext; push_cast; ring
  rw [e, map_mul, map_pow]
  by_cases hl : l = p.2.1
  · subst hl; rw [Pi.single_eq_same, hzi p.2]
  · rw [Pi.single_eq_of_ne hl, hzl p.2 l hl, mul_zero]

include htr hyb hzi hzl in

theorem linearIndependent_jointRes_jointFrame :
    LinearIndependent (ResidueField A)
      (jointRes R (fun p : ℕ × (Σ i, Fin (d i)) => f ^ p.1 * z p.2)
        (fun p l => mul_mem (pow_mem (hf l) _) (hzmem p.2 l))) := by
  classical

  set k := ResidueField A
  let e : (ℕ × (Σ i, Fin (d i))) ≃ (Σ i, ℕ × Fin (d i)) :=
    { toFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      invFun := fun σ => (σ.2.1, ⟨σ.1, σ.2.2⟩)
      left_inv := fun p => rfl
      right_inv := fun σ => rfl }
  have hper : ∀ i, LinearIndependent k
      (fun q : ℕ × Fin (d i) => ((R i).residue ⟨f, hf i⟩) ^ q.1 * yb i q.2) :=
    fun i => linearIndependent_residue_perFrame R f hf htr i (yb i) (hyb i)
  have hpi : LinearIndependent k (fun σ : Σ i, ℕ × Fin (d i) =>
      Pi.single (M := Fb) σ.1 (((R σ.1).residue ⟨f, hf σ.1⟩) ^ σ.2.1 * yb σ.1 σ.2.2)) :=
    Pi.linearIndependent_single (R := k) (Ms := Fb)
      (fun i (q : ℕ × Fin (d i)) => ((R i).residue ⟨f, hf i⟩) ^ q.1 * yb i q.2) hper
  have hfam : jointRes R (fun p : ℕ × (Σ i, Fin (d i)) => f ^ p.1 * z p.2)
      (fun p l => mul_mem (pow_mem (hf l) _) (hzmem p.2 l)) =
      (fun σ : Σ i, ℕ × Fin (d i) =>
        Pi.single (M := Fb) σ.1 (((R σ.1).residue ⟨f, hf σ.1⟩) ^ σ.2.1 * yb σ.1 σ.2.2)) ∘ e :=
    funext fun p => jointRes_jointFrame_eq_single R f hf yb z hzmem hzi hzl p
  rw [hfam]; exact hpi.comp e e.injective


end
end Dubon2026.SourceCurve.RegularProlongation.Joint
