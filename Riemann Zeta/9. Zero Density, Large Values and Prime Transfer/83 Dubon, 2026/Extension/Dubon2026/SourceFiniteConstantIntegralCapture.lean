import Dubon2026.SourceConstantExtensionMonotonicity

/-! DUB-17/18 -> rational Fourier spanning -> integral base change of actual
Fricke fractions. A monic polynomial has finitely many coefficients. Capture
those coefficients and the generated-field expression in one finite constant
extension, so the proved simple-extension descent can be iterated. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℂ K]

theorem exists_list_integral_coordinates (F : IntermediateField ℚ ℂ)
    {T : Set K} {x : K} (hx : IsIntegral (Algebra.adjoin ℂ T) x) :
    ∃ l : List ℂ, IsIntegral (Algebra.adjoin (constantChain F l) T) x := by
  classical
  obtain ⟨P, hm, hc, hx⟩ := (isIntegral_subalgebra_iff _ x).mp hx
  choose l hl using fun n => exists_list_mem_algebra F (hc n)
  let L : List ℂ := (List.range (P.natDegree + 1)).flatMap l
  refine ⟨L, (isIntegral_subalgebra_iff _ x).mpr ⟨P, hm, ?_, hx⟩⟩
  intro n
  by_cases hn : n < P.natDegree + 1
  · have hle : constantChain F (l n) ≤ constantChain F L :=
      constantChain_le F (le_constantChain F L) fun z hz =>
        mem_constantChain_of_mem F (List.mem_flatMap.mpr ⟨n, List.mem_range.mpr hn, hz⟩)
    exact adjoin_constants_mono hle T (hl n)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact zero_mem _

theorem exists_list_mem_integral_generated (F : IntermediateField ℚ ℂ)
    {T S : Set K} {x : K} (hxK : x ∈ IntermediateField.adjoin ℂ S)
    (hxI : IsIntegral (Algebra.adjoin ℂ T) x) :
    ∃ l : List ℂ, x ∈ RSet (constantChain F l) T S := by
  obtain ⟨lK, hK⟩ := exists_list_mem_field F hxK
  obtain ⟨lI, hI⟩ := exists_list_integral_coordinates F hxI
  refine ⟨lK ++ lI, ?_, ?_⟩
  · exact generated_constants_mono (constantChain_le_append_left F lK lI) S hK
  · exact integral_constants_mono (constantChain_le_append_right F lK lI) T hI

end
end Dubon2026.SourceFricke.ConstantDescent