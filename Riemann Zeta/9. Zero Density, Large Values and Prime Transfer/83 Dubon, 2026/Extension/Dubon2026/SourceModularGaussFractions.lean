import Dubon2026.SourceResidueOriginalSpecialization

/-! DUB-17/18 -> original Frobenius/inertia -> good/place reduction ->
actual coefficient valuation on the modular function field. An integral Laurent
fraction has a denominator with nonzero literal coefficient reduction. Primitive
normalization of finite integer coefficient spans puts every actual modular
function or its inverse in this ring. This constructs the valuation ring; its
residue map and good-reduction properties still require their own consumers.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, constant-reduction construction.
Native finite-span selection replaces the external finite-subset argument. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IntermediateField
open scoped Classical

variable {L : Type*} [Field L] (A : ValuationSubring L)

/-- Literal inclusion of valuation-ring Laurent coefficients into the constant field. -/
abbrev ι : LaurentSeries A →+* LaurentSeries L := coeffMap A.subtype

/-- Literal reduction of Laurent coefficients modulo the constant valuation's maximal ideal. -/
abbrev ϖ : LaurentSeries A →+* LaurentSeries (IsLocalRing.ResidueField A) :=
  coeffMap (IsLocalRing.residue A)

theorem ι_injective : Function.Injective (ι A) :=
  coefficientMap_valuation_subtype_injective A

theorem ι_eq_zero_iff (x : LaurentSeries A) : ι A x = 0 ↔ x = 0 := by
  rw [← map_zero (ι A)]; exact (ι_injective A).eq_iff

theorem ϖ_eq_zero_iff (y : LaurentSeries A) :
    ϖ A y = 0 ↔ ∀ n, y.coeff n ∈ IsLocalRing.maximalIdeal A := by
  constructor
  · intro h n
    have h1 := congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField A) => s.coeff n) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h1
    exact (IsLocalRing.residue_eq_zero_iff _).mp h1
  · intro h
    ext n
    simp only [coeffMap_coeff, HahnSeries.coeff_zero]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (h n)

theorem ι_C (a : A) : ι A (HahnSeries.C a) = algebraMap L (LaurentSeries L) (a : L) := by
  rw [HahnSeries.C_apply, coeffMap_single, SourceDifferential.algebraMap_laurentSeries_apply_alt]; rfl

theorem ϖ_C (a : A) : ϖ A (HahnSeries.C a) =
    algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
      (IsLocalRing.residue A a) := by
  rw [HahnSeries.C_apply, coeffMap_single, SourceDifferential.algebraMap_laurentSeries_apply_alt]

/-- Integral Laurent fractions with a denominator whose coefficient reduction is nonzero. -/
def IsInt (f : LaurentSeries L) : Prop :=
  ∃ x y : LaurentSeries A, ϖ A y ≠ 0 ∧ f * ι A y = ι A x

variable {A}

theorem ϖ_ne_zero_ne_zero {y : LaurentSeries A} (hy : ϖ A y ≠ 0) : y ≠ 0 := by
  rintro rfl; exact hy (map_zero _)

theorem IsInt.zero : IsInt A (0 : LaurentSeries L) := ⟨0, 1, by simp, by simp⟩

theorem IsInt.one : IsInt A (1 : LaurentSeries L) := ⟨1, 1, by simp, by simp⟩

theorem IsInt.mul {f g : LaurentSeries L} (hf : IsInt A f) (hg : IsInt A g) : IsInt A (f * g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * x', y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
  rw [map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.add {f g : LaurentSeries L} (hf : IsInt A f) (hg : IsInt A g) : IsInt A (f + g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * y' + x' * y, y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
  rw [map_mul, map_add, map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.neg {f : LaurentSeries L} (hf : IsInt A f) : IsInt A (-f) := by
  obtain ⟨x, y, hy, h⟩ := hf
  exact ⟨-x, y, hy, by rw [map_neg, ← h]; ring⟩

theorem IsInt.cross {f : LaurentSeries L} {x y x' y' : LaurentSeries A}
    (h : f * ι A y = ι A x) (h' : f * ι A y' = ι A x') : x * y' = x' * y := by
  apply ι_injective A
  rw [map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.inv_of {f : LaurentSeries L} {x y : LaurentSeries A} (hx : ϖ A x ≠ 0)
    (h : f * ι A y = ι A x) : f⁻¹ * ι A x = ι A y := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [zero_mul, eq_comm, ι_eq_zero_iff] at h
    exact hx (by rw [h, map_zero])
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hf, one_mul]

end
end Dubon2026.SourceFunctionField.GaussReduction
