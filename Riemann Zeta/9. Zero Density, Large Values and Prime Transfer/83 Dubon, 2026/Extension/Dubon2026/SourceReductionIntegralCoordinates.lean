import Dubon2026.SourceReductionPolynomialCover

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> genus
comparison -> preservation of pole bounds -> integrality over the intersection
with the rational coordinate field. Reuse the finite-space reduction frame
and denominator normalization. The integral coordinate expansion supplies a
finite spanning family, avoiding the general valuation-uniqueness argument.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
section uniqueness

variable (R : RegularProlongation A F Fbar) (x : R.integers)
  (hx : Transcendental (ResidueField A) (R.residue x))
  {n : ℕ} (y : Fin n → R.integers)
  (hy : LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
    (fun i => R.residue (y i)))

include hx hy in

theorem exists_repr_mem_inf
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    (hcard : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F = n)
    (f : R.integers) :
    ∃ r : Fin n → F, (∀ i, r i ∈ R.integers ∧ r i ∈ IntermediateField.adjoin L ({(x : F)} : Set F)) ∧
      (f : F) = ∑ i, r i * (y i : F) := by
  classical
  set Lx := IntermediateField.adjoin L ({(x : F)} : Set F) with hLx
  obtain ⟨U, hU, hULx, T, hT⟩ :=
    exists_unit_mul_mem_span R x hx y hy hcard (L ∙ (f : F))
  have hmem := hT (f : F) (Submodule.mem_span_singleton_self _)
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hmem

  have hgO : ∑ p ∈ (Finset.univ : Finset T), g p • ((frame R x y p.1 : R.integers) : F) ∈
      R.integers := by
    have : ∑ p ∈ (Finset.univ : Finset T), g p • ((frame R x y p.1 : R.integers) : F) =
        (U : F) * (f : F) := by
      rw [← hg]
      exact Finset.sum_congr rfl fun p _ => by rw [coe_frame]
    rw [this]
    exact (U * f).2
  have hEind : LinearIndependent (ResidueField A)
      (fun p : T => R.residue (frame R x y p.1)) :=
    (linearIndependent_residue_frame R x hx y hy).comp _ Subtype.val_injective
  have hgA : ∀ p : T, g p ∈ A := fun p =>
    mem_of_sum_smul_mem R (fun p : T => frame R x y p.1) hEind Finset.univ g hgO p
      (Finset.mem_univ p)

  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hU
  have huinv : ((↑u⁻¹ : R.integers) : F) * (U : F) = 1 := by
    rw [← hu, ← Subring.coe_mul, Units.inv_mul]; rfl
  have hU0 : (U : F) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at huinv; exact zero_ne_one huinv
  have huinv' : ((↑u⁻¹ : R.integers) : F) = (U : F)⁻¹ :=
    eq_inv_of_mul_eq_one_left huinv

  refine ⟨fun i => ∑ p ∈ Finset.univ.filter (fun p : T => p.1.2 = i),
      (U : F)⁻¹ * (algebraMap L F (g p) * (x : F) ^ p.1.1), fun i => ⟨?_, ?_⟩, ?_⟩
  · refine sum_mem fun p _ => mul_mem ?_ (mul_mem ?_ (pow_mem x.2 _))
    · rw [← huinv']; exact (↑u⁻¹ : R.integers).2
    · exact (R.algebraMap_mem_iff (g p)).mpr (hgA p)
  · refine sum_mem fun p _ => mul_mem (inv_mem hULx) (mul_mem (Lx.algebraMap_mem _) ?_)
    exact pow_mem (IntermediateField.mem_adjoin_simple_self L (x : F)) _
  ·
    have hf : (f : F) = (U : F)⁻¹ * ((U : F) * (f : F)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hU0, one_mul]
    rw [hf, ← hg, Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : T => p.1.2) (t := Finset.univ)
      (fun p _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [← hp.2, Algebra.smul_def]
    ring


end uniqueness

end
end Dubon2026.SourceCurve.RegularProlongation
