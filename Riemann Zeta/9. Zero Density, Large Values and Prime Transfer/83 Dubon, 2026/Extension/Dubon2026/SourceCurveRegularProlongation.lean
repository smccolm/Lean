import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> genus
comparison. A regular prolongation records the actual coefficient valuation
and its residue map. It does not assert genus preservation or a place map.
The modular consumer constructs every field of this structure. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Def_AlgebraicCurve_RegularProlongation. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

/-- A coefficient valuation and its residue field, before any genus or place comparison. -/
structure RegularProlongation where
  /-- The valuation ring in the original function field. -/
  integers : ValuationSubring F
  /-- The actual residue homomorphism. -/
  residue : integers →+* Fbar
  /-- The restriction of the valuation to the constant field. -/
  algebraMap_mem_iff : ∀ c : L, algebraMap L F c ∈ integers ↔ c ∈ A
  /-- Every residue-field function has an integral lift. -/
  residue_surjective : Function.Surjective residue
  /-- The residue kernel is exactly the maximal ideal. -/
  ker_residue : RingHom.ker residue = maximalIdeal integers
  /-- Constant reduction agrees with the given constant-field residue map. -/
  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a)
  /-- Each nonzero function admits a constant scaling with nonzero residue. -/
  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers,
    residue ⟨c • f, h⟩ ≠ 0

variable {A F Fbar}

theorem RegularProlongation.isUnit_of_residue_ne_zero
    (R : RegularProlongation A F Fbar) {f : R.integers} (hf : R.residue f ≠ 0) : IsUnit f := by
  by_contra h
  apply hf
  have hmem : f ∈ maximalIdeal R.integers := (IsLocalRing.mem_maximalIdeal f).mpr h
  rw [← R.ker_residue] at hmem
  exact hmem

theorem RegularProlongation.residue_ne_zero_of_isUnit
    (R : RegularProlongation A F Fbar) {f : R.integers} (hf : IsUnit f) : R.residue f ≠ 0 :=
  hf.map R.residue |>.ne_zero

end
end Dubon2026.SourceCurve
