import Dubon2026.SourceTranscendentalConstantDenominatorsV2

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
/-- The fraction evaluation range contains the coordinate field and the new constant. -/
theorem adjoin_le_fractionPolyRange
    {A B C : Type*} [CommRing A] [IsDomain A] [Field B]
    [Algebra A B] [IsFractionRing A B] [Field C] [Algebra B C]
    (c : C) (f : FractionRing A[X] →+* C)
    (hfC : ∀ a : A, f (algebraMap A[X] (FractionRing A[X]) (Polynomial.C a)) =
      algebraMap B C (algebraMap A B a))
    (hfX : f (algebraMap A[X] (FractionRing A[X]) Polynomial.X) = c)
    {z : C} (hz : z ∈ IntermediateField.adjoin B {c}) : z ∈ f.fieldRange := by
  rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield] at hz
  refine Subfield.closure_le (t := f.fieldRange) |>.mpr ?_ hz
  rintro w (⟨w', rfl⟩ | rfl)
  · obtain ⟨r, s, _, hrs⟩ := IsFractionRing.div_surjective (A := A) w'
    rw [← hrs, map_div₀, ← hfC r, ← hfC s]
    exact div_mem (RingHom.mem_fieldRange_self f _) (RingHom.mem_fieldRange_self f _)
  · exact ⟨_, hfX⟩

variable {K : Type*} [Field K] [Algebra ℂ K]
variable (F : IntermediateField ℚ ℂ) (t : K) (S : Set K)
variable {F t}

theorem mem_fractionEval_fieldRange
    (ht : Transcendental ℂ t) (htS : t ∈ S) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F {t}) s)
    {c : ℂ}
    (htc : Transcendental ↥(KFldT F t S) (algebraMap ℂ K c))
    {x : K}
    (hxK : x ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    : x ∈ (IsFractionRing.lift (K := FractionRing ((↥(RFa F t S))[X]))
      (rfPolyEval_injective F t S htc)).fieldRange := by
  classical
  set c' : K := algebraMap ℂ K c with hc'

  set ψ : FractionRing ((↥(RFa F t S))[X]) →+* K :=
    IsFractionRing.lift (rfPolyEval_injective F t S htc) with hψ
  have hψalg : ∀ a : (↥(RFa F t S))[X], ψ (algebraMap _ _ a) = rfPolyEval F t S c a :=
    fun a => IsFractionRing.lift_algebraMap _ _
  haveI hFR : IsFractionRing ↥(RFa F t S) ↥(KFldT F t S) :=
    isFractionRing_RFa F t S ht hSfin hSint

  have hrange : ∀ z ∈ IntermediateField.adjoin ↥(KFldT F t S) {c'}, z ∈ ψ.fieldRange := by
    intro z hz
    apply adjoin_le_fractionPolyRange c' ψ (B := ↥(KFldT F t S)) (A := ↥(RFa F t S)) _ _ hz
    · intro a
      rw [hψalg]
      exact Polynomial.eval₂_C _ _
    · rw [hψalg]
      exact Polynomial.eval₂_X _ _

  have hxψ : x ∈ ψ.fieldRange := by
    refine hrange x ?_
    have h1 := closure_adjoin_le F (S := S) hxK
    have heq : (IntermediateField.adjoin ↥(KFld F S) {c'}).toSubfield =
        (IntermediateField.adjoin ↥(KFldT F t S) {c'}).toSubfield := by
      rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield]
      have hrng : Set.range ⇑(algebraMap ↥(KFld F S) K) =
          Set.range ⇑(algebraMap ↥(KFldT F t S) K) := by
        ext z
        exact ⟨fun ⟨w, hw⟩ => ⟨⟨w, (mem_KFldT_iff F t S htS w).mpr w.2⟩, hw⟩,
          fun ⟨w, hw⟩ => ⟨⟨w, (mem_KFldT_iff F t S htS w).mp w.2⟩, hw⟩⟩
      rw [hrng]
    rw [← IntermediateField.mem_toSubfield, ← heq]; exact h1

  exact hxψ

end
end Dubon2026.SourceFricke.ConstantDescent
