import Dubon2026.SourceOriginalDifferentialInjectivity
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! DUB-17/18 -> cusp-form lower dimension bound -> dimension of regular
differentials -> Riemann--Roch. Essential finite type is required by that
geometric theorem. The original divisor-generated field already has a finite
set of generators, so pinned Mathlib supplies the result directly; no change
of transcendence coordinate or geometric finiteness assumption is needed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem finite_divisorExpansions (N : ℕ) [NeZero N] :
    (divisorExpansions N).Finite := by
  classical
  refine ((Set.finite_Iic N).image
    (fun d : ℕ => if h : d = 0 then 0 else @qExpand ℚ _ d ⟨h⟩ jq)).subset ?_
  rintro x ⟨d, hd, hdvd, rfl⟩
  exact ⟨d, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd, dif_neg hd.ne⟩

/-- The actual original modular function field is essentially of finite type over its base. -/
theorem essFiniteType_original (N : ℕ) [NeZero N]
    (L : Type*) [Field L] [Algebra ℚ L] :
    Algebra.EssFiniteType L (modularFunctionFieldOver N L) := by
  apply IntermediateField.essFiniteType_iff.mpr
  rw [modularFunctionFieldOver, laurentBaseChange_full_eq_adjoin]
  exact IntermediateField.fg_adjoin_of_finite ((finite_divisorExpansions N).image (coeffEmb L))

end
end Dubon2026.SourceFunctionField
