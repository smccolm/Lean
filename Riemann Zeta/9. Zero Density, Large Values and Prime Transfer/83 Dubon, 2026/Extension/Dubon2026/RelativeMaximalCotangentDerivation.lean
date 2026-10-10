import Dubon2026.RelativeMaximalCotangent
import Mathlib.RingTheory.Derivation.Basic

/-! # The actual universal first-order map to the relative maximal-ideal quotient -/

namespace Dubon2026

noncomputable section

variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Choose an original coefficient with the same genuine residue as the original ring element. -/
def originalResidueRepresentative
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) (r : R) : O :=
  (IsLocalRing.residue_surjective (localCoefficientReduction eR r)).choose

/-- The chosen original coefficient has exactly the original element's residue. -/
theorem originalResidueRepresentative_residue
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) (r : R) :
    IsLocalRing.residue O (originalResidueRepresentative eR r) =
      localCoefficientReduction eR r :=
  (IsLocalRing.residue_surjective (localCoefficientReduction eR r)).choose_spec

/-- Subtracting any original coefficient with the same residue puts the difference in the actual maximal ideal. -/
theorem originalResidueDifference_mem
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (r : R) (o : O) (ho : IsLocalRing.residue O o = localCoefficientReduction eR r) :
    r - algebraMap O R o ∈ IsLocalRing.maximalIdeal R := by
  apply (localCoefficientReduction_eq_zero_iff eR _).mp
  rw [map_sub, AlgHom.commutes]
  exact sub_eq_zero.mpr ho.symm

/-- The genuine relative maximal-ideal cotangent class of an original ring element. -/
def relativeMaximalCotangentValue
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (r : R) : RelativeMaximalCotangent O R :=
  relativeMaximalCotangentMk O R
    ⟨r - algebraMap O R (originalResidueRepresentative eR r),
      originalResidueDifference_mem eR r _ (originalResidueRepresentative_residue eR r)⟩

/-- The relative cotangent value is independent of the choice of original coefficient representative. -/
theorem relativeMaximalCotangentValue_eq
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (r : R) (o : O) (ho : IsLocalRing.residue O o = localCoefficientReduction eR r) :
    relativeMaximalCotangentValue eR r =
      relativeMaximalCotangentMk O R ⟨r - algebraMap O R o,
        originalResidueDifference_mem eR r o ho⟩ := by
  apply (relativeMaximalCotangentMk_eq_iff O R _ _).mpr
  have hm : o - originalResidueRepresentative eR r ∈ IsLocalRing.maximalIdeal O := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, ho, originalResidueRepresentative_residue, sub_self]
  have hi := Ideal.mem_map_of_mem (algebraMap O R) hm
  apply Ideal.mem_sup_right
  convert hi using 1
  rw [map_sub]
  ring

/-- Original addition gives addition of the actual relative cotangent classes. -/
theorem relativeMaximalCotangentValue_add
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) (r s : R) :
    relativeMaximalCotangentValue eR (r + s) =
      relativeMaximalCotangentValue eR r + relativeMaximalCotangentValue eR s := by
  let a := originalResidueRepresentative eR r
  let b := originalResidueRepresentative eR s
  have ha := originalResidueRepresentative_residue eR r
  have hb := originalResidueRepresentative_residue eR s
  have hab : IsLocalRing.residue O (a + b) = localCoefficientReduction eR (r + s) := by
    rw [map_add, map_add, ha, hb]
  rw [relativeMaximalCotangentValue_eq eR (r + s) (a + b) hab,
    relativeMaximalCotangentValue_eq eR r a ha,
    relativeMaximalCotangentValue_eq eR s b hb, ← map_add]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_add, map_add]
  ring

/-- Original coefficient scalars act on the genuine relative cotangent classes. -/
theorem relativeMaximalCotangentValue_smul
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) (o : O) (r : R) :
    relativeMaximalCotangentValue eR (o • r) =
      o • relativeMaximalCotangentValue eR r := by
  let a := originalResidueRepresentative eR r
  have ha := originalResidueRepresentative_residue eR r
  have hoa : IsLocalRing.residue O (o * a) = localCoefficientReduction eR (o • r) := by
    rw [Algebra.smul_def, map_mul, map_mul, AlgHom.commutes, ha]
    rfl
  rw [relativeMaximalCotangentValue_eq eR (o • r) (o * a) hoa,
    relativeMaximalCotangentValue_eq eR r a ha,
    ← LinearMap.map_smul_of_tower]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul]
  ring

/-- The genuine relative cotangent value satisfies the Leibniz identity because products of original maximal-ideal differences vanish in the actual quotient. -/
theorem relativeMaximalCotangentValue_mul
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) (r s : R) :
    relativeMaximalCotangentValue eR (r * s) =
      r • relativeMaximalCotangentValue eR s + s • relativeMaximalCotangentValue eR r := by
  let a := originalResidueRepresentative eR r
  let b := originalResidueRepresentative eR s
  have ha := originalResidueRepresentative_residue eR r
  have hb := originalResidueRepresentative_residue eR s
  have hab : IsLocalRing.residue O (a * b) = localCoefficientReduction eR (r * s) := by
    rw [map_mul, map_mul, ha, hb]
  rw [relativeMaximalCotangentValue_eq eR (r * s) (a * b) hab,
    relativeMaximalCotangentValue_eq eR r a ha,
    relativeMaximalCotangentValue_eq eR s b hb,
    ← map_smul, ← map_smul, ← map_add]
  apply (relativeMaximalCotangentMk_eq_iff O R _ _).mpr
  apply Ideal.mem_sup_left
  have hm : (r - algebraMap O R a) * (s - algebraMap O R b) ∈
      (IsLocalRing.maximalIdeal R) ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (originalResidueDifference_mem eR r a ha)
      (originalResidueDifference_mem eR s b hb)
  convert (IsLocalRing.maximalIdeal R ^ 2).neg_mem hm using 1
  simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
  ring

/-- The actual universal first-order derivation into the original relative maximal-ideal cotangent quotient. -/
def relativeMaximalCotangentDerivation
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Derivation O R (RelativeMaximalCotangent O R) :=
  Derivation.mk'
    { toFun := relativeMaximalCotangentValue eR
      map_add' := relativeMaximalCotangentValue_add eR
      map_smul' := relativeMaximalCotangentValue_smul eR }
    (relativeMaximalCotangentValue_mul eR)

/-- On the original maximal ideal the universal derivation is the actual quotient map. -/
theorem relativeMaximalCotangentDerivation_maximal
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (x : IsLocalRing.maximalIdeal R) :
    relativeMaximalCotangentDerivation eR x = relativeMaximalCotangentMk O R x := by
  have h0 : IsLocalRing.residue O 0 = localCoefficientReduction eR x := by
    rw [map_zero, (localCoefficientReduction_eq_zero_iff eR x).mpr x.property]
  change relativeMaximalCotangentValue eR x = _
  rw [relativeMaximalCotangentValue_eq eR x 0 h0]
  congr 1
  apply Subtype.ext
  simp only [map_zero, sub_zero]

/-- Every actual relative maximal-ideal cotangent class is attained by the genuine original-ring derivation. -/
theorem relativeMaximalCotangentDerivation_surjective
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Function.Surjective (relativeMaximalCotangentDerivation eR) := by
  intro y
  obtain ⟨x, rfl⟩ := relativeMaximalCotangentMk_surjective O R y
  exact ⟨x, relativeMaximalCotangentDerivation_maximal eR x⟩

end
end Dubon2026
