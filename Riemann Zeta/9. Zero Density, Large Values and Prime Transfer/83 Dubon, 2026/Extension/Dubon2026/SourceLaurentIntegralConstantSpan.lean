import Dubon2026.SourceAlgebraicConstantIntegralSpan
import Dubon2026.SourceTranscendentalConstantIntegralSpanV2
import Dubon2026.SourceLaurentGeneratedConstants
import Dubon2026.SourceFiniteConstantIntegralCapture

/-! DUB-17/18 -> original Gamma1 character realization -> differential/cusp
comparison -> rational Fourier spanning -> integral base change of Fricke
fractions. Both simple-extension span theorems are proved, and coefficient
transcendence supplies the relative transcendence premise at each step.
Finite constant capture and induction therefore give the complex integral
span theorem for a finite family of Laurent series over the original field.
The actual Fricke generator family is a later instantiation; no characteristic
zero Hecke lift or arithmetic association is inferred here. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section
open Dubon2026.SourceFunctionField
open scoped IntermediateField
/-- The algebra-induced span uses the same scalar action as coefficientwise Laurent multiplication. -/
theorem mem_span_laurent_of_algebra_span {S : Set (LaurentSeries ℂ)} {x : LaurentSeries ℂ}
    (h : letI : Module ℂ (LaurentSeries ℂ) := Algebra.toModule
         x ∈ Submodule.span ℂ S) : x ∈ Submodule.span ℂ S := by
  let M := Submodule.span ℂ S
  have hmem : S ⊆ M := Submodule.subset_span
  have hzero : (0 : LaurentSeries ℂ) ∈ M := zero_mem M
  have hadd : ∀ {y z : LaurentSeries ℂ}, y ∈ M → z ∈ M → y + z ∈ M :=
    fun hy hz => add_mem hy hz
  have hsmul : ∀ (c : ℂ) (y : LaurentSeries ℂ), y ∈ M →
      algebraMap ℂ (LaurentSeries ℂ) c * y ∈ M := by
    intro c y hy
    rw [SourceDifferential.algebraMap_laurentSeries_apply_alt,
      HahnSeries.single_zero_mul_eq_smul]
    exact M.smul_mem c hy
  change x ∈ M
  letI : Module ℂ (LaurentSeries ℂ) := Algebra.toModule
  induction h using Submodule.span_induction with
  | mem y hy => exact hmem hy
  | zero => exact hzero
  | add y z _ _ hy hz => exact hadd hy hz
  | smul c y _ hy => exact hsmul c y hy
variable (F : IntermediateField ℚ ℂ) (t : LaurentSeries ℂ) (S : Set (LaurentSeries ℂ))

theorem integral_constantChain_step
    (ht : Transcendental ℂ t) (htS : t ∈ S) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral (TRng F {t}) s)
    (hSrange : S ⊆ (coeffMap (algebraMap F ℂ)).fieldRange) (c : ℂ) (l : List ℂ) :
    RSet (constantChain F (c :: l)) {t} S ⊆
      (Submodule.span ℂ (RSet (constantChain F l) {t} S) : Set (LaurentSeries ℂ)) := by
  rintro x ⟨hxK, hxI⟩
  have hxK' := (generated_mem_iff_closure (constantChain F (c :: l)) S x).mp hxK
  change x ∈ Subfield.closure (algebraMap ℂ (LaurentSeries ℂ) ''
    ((IntermediateField.adjoin (constantChain F l) {c}) : Set ℂ) ∪ S) at hxK'
  change IsIntegral (Algebra.adjoin (IntermediateField.adjoin (constantChain F l) {c})
    ({t} : Set (LaurentSeries ℂ))) x at hxI
  by_cases hc : IsAlgebraic (constantChain F l) c
  · apply mem_span_laurent_of_algebra_span
    exact mem_span_RSet_of_adjoin_simple (constantChain F l) {t} S
      (Set.singleton_subset_iff.mpr htS) hc.isIntegral hxK' hxI
  · apply mem_span_laurent_of_algebra_span
    exact mem_span_RSet_of_adjoin_simple_transcendental S ht htS hSfin
      (fun s hs => integral_constants_mono (le_constantChain F l) {t} (hSint s hs)) hc
      (constant_transcendental_generated (constantChain F l) htS
        (coeffMap_fieldRange_mono F (le_constantChain F l) hSrange) hc) hxK' hxI

theorem integral_constantChain_subset_span
    (ht : Transcendental ℂ t) (htS : t ∈ S) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral (TRng F {t}) s)
    (hSrange : S ⊆ (coeffMap (algebraMap F ℂ)).fieldRange) (l : List ℂ) :
    RSet (constantChain F l) {t} S ⊆
      (Submodule.span ℂ (RSet F {t} S) : Set (LaurentSeries ℂ)) := by
  induction l with
  | nil => exact Submodule.subset_span
  | cons c l ih =>
    exact (integral_constantChain_step F t S ht htS hSfin hSint hSrange c l).trans
      (Submodule.span_le.mpr ih)

theorem mem_span_integral_generated_of_complex
    (ht : Transcendental ℂ t) (htS : t ∈ S) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral (TRng F {t}) s)
    (hSrange : S ⊆ (coeffMap (algebraMap F ℂ)).fieldRange)
    {x : LaurentSeries ℂ} (hxK : x ∈ IntermediateField.adjoin ℂ S)
    (hxI : IsIntegral (Algebra.adjoin ℂ ({t} : Set (LaurentSeries ℂ))) x) :
    x ∈ Submodule.span ℂ (RSet F {t} S) := by
  obtain ⟨l, hl⟩ := exists_list_mem_integral_generated F hxK hxI
  exact integral_constantChain_subset_span F t S ht htS hSfin hSint hSrange l hl

end
end Dubon2026.SourceFricke.ConstantDescent