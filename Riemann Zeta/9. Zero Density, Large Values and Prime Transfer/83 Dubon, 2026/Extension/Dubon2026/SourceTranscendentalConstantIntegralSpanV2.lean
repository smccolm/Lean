import Dubon2026.SourceTranscendentalConstantFieldRangeV2
import Dubon2026.SourceTranscendentalConstantScaledRelationV2
import Dubon2026.SourceTranscendentalConstantNormalityV2

/-! DUB-17/18 -> original all-weight arithmetic association -> actual
Gamma1 character realization -> differential/cusp comparison -> rational
Fourier spanning -> integral base change of Fricke fractions. This is the
transcendental constant-adjoining step of the finite constant-list induction.
Native integral closure and polynomial normality recover integral coefficients
after clearing scalar denominators. The original finite generator integrality
and j transcendence are explicit inputs, supplied later by the actual Fricke field.
Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental.
All source proof-limit settings are omitted; native limits are unchanged. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section
open Polynomial
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin
variable {K : Type*} [Field K] [Algebra ℂ K]
variable (F : IntermediateField ℚ ℂ) (t : K) (S : Set K)
variable {F t}

theorem mem_span_RSet_of_adjoin_simple_transcendental
    (ht : Transcendental ℂ t) (htS : t ∈ S) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F {t}) s)
    {c : ℂ} (hc : Transcendental ↥F c)
    (htc : Transcendental ↥(KFldT F t S) (algebraMap ℂ K c))
    {x : K}
    (hxK : x ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hxint : IsIntegral ↥(Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) ({t} : Set K)) x) :
    x ∈ Submodule.span ℂ (RSet F {t} S) := by
  classical
  let c' : K := algebraMap ℂ K c
  let ψ : FractionRing ((↥(RFa F t S))[X]) →+* K :=
    IsFractionRing.lift (rfPolyEval_injective F t S htc)
  have hψalg : ∀ a : (↥(RFa F t S))[X], ψ (algebraMap _ _ a) = rfPolyEval F t S c a :=
    fun a => IsFractionRing.lift_algebraMap _ _
  have hxψ : x ∈ ψ.fieldRange :=
    mem_fractionEval_fieldRange S ht htS hSfin hSint htc hxK
  obtain ⟨D, hD0, n, BB, hrel⟩ := exists_scaled_monic_relation S htS hxint
  let Dv : K := Polynomial.aeval c' D
  have hDψ : Dv ∈ ψ.fieldRange := by
    obtain ⟨a, ha⟩ := evalF_mem_range_rfPolyEval F t S htS (c := c) D
    exact ⟨algebraMap _ _ a, by rw [hψalg]; exact ha⟩
  have hyψ : Dv * x ∈ ψ.fieldRange := mul_mem hDψ hxψ
  haveI : IsIntegrallyClosed ((↥(RFa F t S))[X]) :=
    isIntegrallyClosed_RFa_polynomial F t S ht hSfin hSint
  have hyrange := mem_range_of_fraction_monic_relation (rfPolyEval F t S c)
    (rfPolyEval_injective F t S htc) hyψ n BB hrel
  have hyspan := range_rfPolyEval_subset_span F t S htS hyrange
  have hsmul : (Polynomial.aeval c D : ℂ) • x = Dv * x := by
    dsimp only [Dv, c']
    rw [Algebra.smul_def, Polynomial.aeval_algebraMap_apply]
  have hs0 : (Polynomial.aeval c D : ℂ) ≠ 0 := by
    intro h0; exact hD0 ((transcendental_iff.mp hc) D h0)
  have hsx : (Polynomial.aeval c D : ℂ) • x ∈ Submodule.span ℂ (RSet F {t} S) := by
    rw [hsmul]; exact hyspan
  have h2 := Submodule.smul_mem (Submodule.span ℂ (RSet F {t} S))
    ((Polynomial.aeval c D : ℂ))⁻¹ hsx
  rwa [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hs0, one_smul] at h2

end
end Dubon2026.SourceFricke.ConstantDescent
