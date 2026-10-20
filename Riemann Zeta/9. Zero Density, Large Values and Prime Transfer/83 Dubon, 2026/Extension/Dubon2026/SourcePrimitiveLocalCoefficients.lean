import Dubon2026.SourcePrimitiveCoefficientField
import Dubon2026.CommonCoefficientLocalField
import Dubon2026.RationalPrimeRootH2Invariant
import Mathlib.RingTheory.Valuation.Integral

/-! Actual local coefficient arithmetic for the original primitive form.
DUB-17/18 -> modular Galois association -> coefficient number field and a finite
local coefficient field with integral Fourier traces. The existing common-field
and valuation-extension constructions are instantiated with the derived original
coefficient field. This constructs coefficient arithmetic, not a Galois action.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- The actual original Fourier coefficient viewed in its literal coefficient field. -/
def sourcePrimitiveFieldCoefficient (f : PrimitiveCuspForm Q k) (n : ℕ) :
    sourcePrimitiveCoefficientField f :=
  ⟨cuspCoefficients f.toCuspForm n, IntermediateField.subset_adjoin ℚ _ ⟨n, rfl⟩⟩

/-- Embedding the field-valued coefficient into the original complex field recovers the original coefficient. -/
theorem sourcePrimitiveFieldCoefficient_coe (f : PrimitiveCuspForm Q k) (n : ℕ) :
    (sourcePrimitiveFieldCoefficient f n : ℂ) = cuspCoefficients f.toCuspForm n := rfl

/-- The coefficient in the literal original coefficient field is integral over the integers. -/
theorem sourcePrimitiveFieldCoefficient_isIntegral (f : PrimitiveCuspForm Q k)
    (hk : 2 ≤ k) (n : ℕ) : IsIntegral ℤ (sourcePrimitiveFieldCoefficient f n) := by
  exact (isIntegral_algHom_iff ((sourcePrimitiveCoefficientField f).val.restrictScalars ℤ)
    Subtype.val_injective).mp (sourcePrimitiveCoefficient_isIntegral f hk n)

/-- Every embedding of the original coefficient field into a valued field gives integral original coefficients. -/
theorem sourcePrimitiveCoefficient_valuation_le_one
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    {F : Type*} [Field F] [CharZero F] [ValuativeRel F]
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] F) (n : ℕ) :
    ValuativeRel.valuation F (τ (sourcePrimitiveFieldCoefficient f n)) ≤ 1 := by
  have hi := (sourcePrimitiveFieldCoefficient_isIntegral f hk n).map (τ.restrictScalars ℤ)
  exact (Valuation.integer.integers (ValuativeRel.valuation F)).isIntegral_iff_v_le_one.mp
    hi.tower_top

/-- A finite genuine local coefficient field exists for the original form, preserving the original prime valuation and making every embedded original coefficient integral. -/
theorem sourcePrimitiveCoefficient_exists_local_structure
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (ell : ℕ) (hell : ell.Prime) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero ell hell
    let F := rationalPrimeLocalField ell hell
    let E := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (_ : UniformSpace E) (_ : ValuativeRel E),
      IsUniformAddGroup E ∧ IsNonarchimedeanLocalField E ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation E) ∧
      FiniteDimensional F E ∧
      ∀ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] AlgebraicClosure F) (n : ℕ),
        ValuativeRel.valuation E
          (commonCoefficientEmbedding (sourcePrimitiveCoefficientField f) F τ
            (sourcePrimitiveFieldCoefficient f n)) ≤ 1 := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero ell hell
  let F := rationalPrimeLocalField ell hell
  let E := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  obtain ⟨u, v, hu, hv, hext, hfin, _⟩ :=
    commonCoefficientField_exists_local_structure (sourcePrimitiveCoefficientField f) F
  letI : UniformSpace E := u
  letI : ValuativeRel E := v
  refine ⟨u, v, hu, hv, hext, hfin, ?_⟩
  intro τ n
  exact sourcePrimitiveCoefficient_valuation_le_one f hk
    (commonCoefficientEmbedding (sourcePrimitiveCoefficientField f) F τ) n

end
end Dubon2026
