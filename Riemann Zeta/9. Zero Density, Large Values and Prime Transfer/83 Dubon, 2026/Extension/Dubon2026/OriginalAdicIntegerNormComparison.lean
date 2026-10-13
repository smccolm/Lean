import Dubon2026.OriginalAdicCompletionResidue
import Dubon2026.LocalFieldUniformizerOrder
import Dubon2026.SpectralFiniteExtensionLocalField

/-! # The original completion integer ring and its norm valuation

Both rings consist of exactly the original completed elements of norm
at most one. Their identity-on-values equivalence lets the fixed-field
local theorem consume the actual outside-support integer units in DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- The canonical valuation attached to the original norm has the same integral elements. -/
theorem normValuativeInteger_mem_iff (F : Type) [NormedField F]
    [IsUltrametricDist F] :
    letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
    ∀ x : F, x ∈ (ValuativeRel.valuation F).integer ↔ ‖x‖ ≤ 1 := by
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : (NormedField.valuation (K := F)).Compatible := Valuation.Compatible.ofValuation _
  intro x
  change ValuativeRel.valuation F x ≤ 1 ↔ ‖x‖ ≤ 1
  rw [← map_one (ValuativeRel.valuation F),
    ValuativeRel.isEquiv (ValuativeRel.valuation F) (NormedField.valuation (K := F)) x 1]
  change ‖x‖₊ ≤ ‖(1 : F)‖₊ ↔ ‖x‖ ≤ 1
  simp only [nnnorm_one, ← NNReal.coe_le_coe, NNReal.coe_one]
  rfl

variable (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))

/-- The actual original adic integer ring equals the norm-valuation ring on original values. -/
def originalAdicIntegerNormEquiv :
    letI : ValuativeRel (w.adicCompletion L) :=
      ValuativeRel.ofValuation (NormedField.valuation (K := w.adicCompletion L))
    w.adicCompletionIntegers L ≃+* (ValuativeRel.valuation (w.adicCompletion L)).integer := by
  letI : ValuativeRel (w.adicCompletion L) :=
    ValuativeRel.ofValuation (NormedField.valuation (K := w.adicCompletion L))
  refine {
    toFun := fun x => ⟨x.val, (normValuativeInteger_mem_iff _ x.val).mpr
      (Valued.toNormedField.norm_le_one_iff.mpr x.property)⟩
    invFun := fun x => ⟨x.val, Valued.toNormedField.norm_le_one_iff.mp
      ((normValuativeInteger_mem_iff _ x.val).mp x.property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- The original integer-ring comparison preserves the completed field value literally. -/
theorem originalAdicIntegerNormEquiv_val (x : w.adicCompletionIntegers L) :
    (originalAdicIntegerNormEquiv L w x).val = x.val := rfl

end
end Dubon2026
