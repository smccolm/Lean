import Dubon2026.SourceResidueReversePrimeDegree
import Dubon2026.SourceModularFunctionFieldCoefficients
import Dubon2026.SourceOriginalSlotRange
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
all-divisor residue-field degree. These are the actual expanded coefficient
fields in the reverse prime tower. Membership and the expansion-range
condition are derived from their divisor generators. In particular the
reverse degree-p consumer has no supplied field-range or generator inputs. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem coefficient_field_mono {K : Type*} [Field K] {M N : ℕ} (h : M ∣ N) :
    modularFunctionFieldCoeff M K ≤ modularFunctionFieldCoeff N K := by
  apply IntermediateField.adjoin.mono
  rintro x ⟨d, hd, hdM, rfl⟩
  exact ⟨d, hd, hdM.trans h, rfl⟩

/-- The actual image of the full divisor field under literal q-expansion. -/
def expandedCoefficientField (K : Type*) [Field K] (n : ℕ) [NeZero n] (N : ℕ) :
    IntermediateField K (LaurentSeries K) :=
  (modularFunctionFieldCoeff N K).map (qExpandAlgHom K n)

theorem expandedCoefficientField_mono {K : Type*} [Field K] (n : ℕ) [NeZero n]
    {M N : ℕ} (h : M ∣ N) :
    expandedCoefficientField K n M ≤ expandedCoefficientField K n N :=
  IntermediateField.map_mono (qExpandAlgHom K n) (coefficient_field_mono h)

theorem qExpand_j_mem_expandedCoefficientField
    (K : Type*) [Field K] (n N : ℕ) [NeZero n] {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand K (n * d) (jqModC K) ∈ expandedCoefficientField K n N := by
  exact ⟨qExpand K d (jqModC K), jqd_mem_coeff_field N K hd,
    qExpand_qExpand d n (jqModC K)⟩

theorem expandedCoefficientField_range
    (K : Type*) [Field K] (n N : ℕ) [NeZero n]
    {x : LaurentSeries K} (hx : x ∈ expandedCoefficientField K n N) :
    x ∈ (qExpand K n).range := by
  obtain ⟨y, _, hy⟩ := hx
  exact ⟨y, hy⟩

theorem expandedCoefficientField_le
    (K : Type*) [Field K] (n N : ℕ) [NeZero n] :
    expandedCoefficientField K n N ≤ modularFunctionFieldCoeff (N * n) K := by
  rw [expandedCoefficientField, modularFunctionFieldCoeff, adjoin_map, adjoin_le_iff]
  rintro x ⟨y, ⟨d, hd, hdN, rfl⟩, rfl⟩
  haveI := hd
  change qExpand K n (qExpand K d (jqModC K)) ∈ _
  rw [qExpand_qExpand]
  exact jqd_mem_coeff_field (N * n) K
    ((mul_dvd_mul_left n hdN).trans (dvd_of_eq (mul_comm n N)))

theorem prime_j_mem_expandedCoefficientField
    (K : Type*) [Field K] (p N : ℕ) [NeZero p] :
    qExpand K p (jqModC K) ∈ expandedCoefficientField K p N := by
  simpa only [mul_one] using qExpand_j_mem_expandedCoefficientField K p N (one_dvd N)

theorem residue_expanded_reverse_prime_finrank_eq
    (K : Type*) [Field K] [IsAlgClosed K] (p N : ℕ) [Fact p.Prime]
    (hpK : (p : K) ≠ 0) (hpN : p ∣ N) :
    Module.finrank (expandedCoefficientField K p N)
      (IntermediateField.adjoin (expandedCoefficientField K p N)
        ({jqModC K} : Set (LaurentSeries K))) = p := by
  haveI : NeZero (p : K) := ⟨hpK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  obtain ⟨ζ, hζval⟩ := hz.isUnit (Nat.Prime.ne_zero (Fact.out : p.Prime))
  have hζ : IsPrimitiveRoot (ζ : K) p := hζval.symm ▸ hz
  exact residue_reverse_prime_finrank_eq _ p ζ hζ
    (fun _ hx => expandedCoefficientField_range K p N hx)
    (prime_j_mem_expandedCoefficientField K p N)
    (qExpand_j_mem_expandedCoefficientField K p N hpN)

end
end Dubon2026.SourceFunctionField
