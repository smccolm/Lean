import Dubon2026.SourceJointReductionCoordinateCover

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera inequality ->
joint chart integrality. This strengthening records that the common unit
denominator belongs to the rational coordinate field, as required by the
finite integral-coordinate argument. It reuses the already checked joint
basis and normalization proofs. The earlier audited existential remains
frozen; only its necessary coordinate-membership refinement is added.


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

include htr hyb hzi hzl heq in

theorem exists_joint_integral_coordinate_repr (u : F) (hu : ∀ i, u ∈ (R i).integers) :
    ∃ r : (Σ i, Fin (d i)) → F,
      (∀ τ, (∀ i, r τ ∈ (R i).integers) ∧
        r τ ∈ IntermediateField.adjoin L ({f} : Set F)) ∧
      u = ∑ τ, r τ * z τ := by
  classical
  set Lf := IntermediateField.adjoin L ({f} : Set F)
  obtain ⟨U, hU, hUres, hULf, T, hT⟩ :=
    exists_joint_unit_mul_mem_span_in_coordinate R f hf htr yb hyb z hzmem hzi hzl heq (L ∙ u)
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp
    (hT u (Submodule.mem_span_singleton_self u))
  let E : T → F := fun p => f ^ p.1.1 * z p.1.2
  have hEmem : ∀ p i, E p ∈ (R i).integers :=
    fun p i => mul_mem (pow_mem (hf i) _) (hzmem p.1.2 i)
  have hEind : LinearIndependent (ResidueField A) (jointRes R E hEmem) :=
    (linearIndependent_jointRes_jointFrame R f hf htr yb hyb z hzmem hzi hzl).comp _
      Subtype.val_injective
  have hgO : ∀ i, ∑ p ∈ (Finset.univ : Finset T), g p • E p ∈ (R i).integers := by
    intro i
    change ∑ p, g p • (f ^ p.1.1 * z p.1.2) ∈ (R i).integers
    rw [hg]
    exact mul_mem (hU i) (hu i)
  have hgA : ∀ p : T, g p ∈ A := fun p =>
    mem_of_sum_smul_mem_joint R E hEmem hEind Finset.univ g hgO p (Finset.mem_univ p)
  have hUinv : ∀ i, U⁻¹ ∈ (R i).integers := by
    intro i
    obtain ⟨v, hv⟩ := (R i).isUnit_of_residue_ne_zero (hUres i)
    have hi : ((↑v⁻¹ : (R i).integers) : F) * U = 1 := by
      rw [← show ((↑v : (R i).integers) : F) = U from congrArg Subtype.val hv,
        ← Subring.coe_mul, Units.inv_mul]
      rfl
    rw [← eq_inv_of_mul_eq_one_left hi]
    exact (↑v⁻¹ : (R i).integers).2
  have hU0 : U ≠ 0 := by
    by_contra h0
    rcases isEmpty_or_nonempty ι with hι | hι
    · have hdim : Module.finrank Lf F = 0 := by simpa using heq.symm
      exact (Module.finrank_pos (R := Lf) (M := F)).ne' hdim
    · let i : ι := Classical.choice hι
      have hz : (⟨U, hU i⟩ : (R i).integers) = 0 := Subtype.ext h0
      exact hUres i (by rw [hz, map_zero])
  refine ⟨fun τ => ∑ p ∈ Finset.univ.filter (fun p : T => p.1.2 = τ),
      U⁻¹ * (algebraMap L F (g p) * f ^ p.1.1), fun τ => ⟨?_, ?_⟩, ?_⟩
  · intro i
    exact sum_mem fun p _ => mul_mem (hUinv i)
      (mul_mem ((R i).algebraMap_mem_iff (g p) |>.mpr (hgA p)) (pow_mem (hf i) _))
  · exact sum_mem fun p _ => mul_mem (inv_mem hULf)
      (mul_mem (Lf.algebraMap_mem _) (pow_mem (IntermediateField.mem_adjoin_simple_self L f) _))
  · have he : u = U⁻¹ * (U * u) := by rw [← mul_assoc, inv_mul_cancel₀ hU0, one_mul]
    rw [he, ← hg, Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : T => p.1.2) (t := Finset.univ)
      (fun p _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [← hp.2, Algebra.smul_def]
    ring

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
