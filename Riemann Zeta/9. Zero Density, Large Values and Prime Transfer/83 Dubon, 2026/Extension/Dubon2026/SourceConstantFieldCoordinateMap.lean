import Dubon2026.SourceConstantFieldRationalDescent

/-! DUB-17/18 -> original arithmetic Picard injectivity -> principal-divisor
descent -> finite-basis trace reconstruction. Adapted from
S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, coordinate-map and basis sections.
The existing original degree base change supplies independence from spanning;
the external polynomial denominator-clearing independence proof is omitted.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section
open Polynomial
variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem algebraMap_mem_adjoin_simple {x a : F}
    (ha : a ∈ IntermediateField.adjoin K ({x} : Set F)) :
    algebraMap F F' a ∈ IntermediateField.adjoin K' ({algebraMap F F' x} : Set F') := by
  rw [IntermediateField.mem_adjoin_simple_iff] at ha ⊢
  obtain ⟨r, s, rfl⟩ := ha
  refine ⟨r.map (algebraMap K K'), s.map (algebraMap K K'), ?_⟩
  rw [aeval_map_algebraMap, aeval_map_algebraMap, map_div₀, aeval_algebraMap_apply,
    aeval_algebraMap_apply]

variable (K K' F') in
/-- The induced embedding of the actual simple coordinate fields. -/
def iota (x : F) :
    IntermediateField.adjoin K ({x} : Set F) →+*
      IntermediateField.adjoin K' ({algebraMap F F' x} : Set F') where
  toFun a := ⟨algebraMap F F' a, algebraMap_mem_adjoin_simple a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem coe_iota (x : F) (a : IntermediateField.adjoin K ({x} : Set F)) :
    ((iota K K' F' x a : IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) : F') =
      algebraMap F F' a := rfl

theorem algebraMap_smul (x : F) (a : IntermediateField.adjoin K ({x} : Set F)) (f : F) :
    algebraMap F F' (a • f) = iota K K' F' x a • algebraMap F F' f := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl


end
end Dubon2026.SourceCurve.ConstantField
