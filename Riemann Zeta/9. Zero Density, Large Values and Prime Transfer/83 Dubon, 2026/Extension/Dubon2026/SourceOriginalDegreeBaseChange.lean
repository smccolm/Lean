import Dubon2026.SourceLaurentDegreeTransport
import Dubon2026.SourceOriginalDifferentialInjectivity

/-! DUB-17/18 -> numerical modular genus -> exact original j-map degree.
The degree of the actual internal j coordinate is preserved by the original
coefficient extension. Finiteness is derived from the already proved
all-divisor monic relations. Thus rational degree calculations apply to
the geometric original field without an extra base-change or finiteness
assumption. The all-level numerical degree itself remains required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem coeffEmb_rat_apply (x : LaurentSeries ℚ) : coeffEmb ℚ x = x := by
  ext n
  rw [coeffEmb_coeff]
  rfl

theorem laurentBaseChange_rat (F : IntermediateField ℚ (LaurentSeries ℚ)) :
    laurentBaseChange ℚ F = F := by
  rw [laurentBaseChange]
  have h : coeffEmb ℚ '' (F : Set (LaurentSeries ℚ)) = F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [coeffEmb_rat_apply]
    · intro hx
      exact ⟨x, hx, coeffEmb_rat_apply x⟩
  rw [h, IntermediateField.adjoin_self]

theorem original_coordinate_finrank_eq_relfinrank (N : ℕ)
    (L : Type*) [Field L] [Algebra ℚ L] :
    Module.finrank (IntermediateField.adjoin L
      ({jOver N L} : Set (modularFunctionFieldOver N L)))
      (modularFunctionFieldOver N L) =
    relfinrank (IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)))
      (modularFunctionFieldOver N L) := by
  let F := modularFunctionFieldOver N L
  let B : IntermediateField L F := IntermediateField.adjoin L {jOver N L}
  have hB : lift B = IntermediateField.adjoin L
      ({coeffEmb L jq} : Set (LaurentSeries L)) := lift_adjoin_simple L F (jOver N L)
  have ht : lift (⊤ : IntermediateField L F) = F := lift_top L F
  have h := relfinrank_map_map B (⊤ : IntermediateField L F) F.val
  change relfinrank (lift B) (lift (⊤ : IntermediateField L F)) = _ at h
  rw [hB, ht, relfinrank_top_right] at h
  exact h.symm

theorem original_coordinate_relfinrank_pos (N : ℕ) [NeZero N]
    (L : Type*) [Field L] [Algebra ℚ L] :
    0 < relfinrank (IntermediateField.adjoin L
      ({coeffEmb L jq} : Set (LaurentSeries L)))
      (modularFunctionFieldOver N L) := by
  haveI := finiteDimensional_original N L
  rw [← original_coordinate_finrank_eq_relfinrank]
  exact Module.finrank_pos

theorem finite_original_rational_coordinate (N : ℕ) [NeZero N] :
    FiniteDimensional (DegreeTransport.K₀ jq)
      (DegreeTransport.E₀ (modularFunctionFieldFull N) jq (jq_mem_full N)) := by
  have hrel := original_coordinate_relfinrank_pos N ℚ
  rw [modularFunctionFieldOver, laurentBaseChange_rat, coeffEmb_rat_apply] at hrel
  rw [relfinrank_eq_finrank_of_le (DegreeTransport.K₀_le (jq_mem_full N))] at hrel
  exact Module.finite_of_finrank_pos hrel

theorem finrank_original_over_j_baseChange (N : ℕ) [NeZero N]
    (L : Type*) [Field L] [Algebra ℚ L] :
    Module.finrank (IntermediateField.adjoin L
      ({jOver N L} : Set (modularFunctionFieldOver N L)))
      (modularFunctionFieldOver N L) =
    relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (modularFunctionFieldFull N) := by
  haveI := finite_original_rational_coordinate N
  rw [original_coordinate_finrank_eq_relfinrank]
  exact DegreeTransport.relfinrank_eq_of_finite L (jq_mem_full N) (transcendental_jqModC ℚ)

end
end Dubon2026.SourceFunctionField
