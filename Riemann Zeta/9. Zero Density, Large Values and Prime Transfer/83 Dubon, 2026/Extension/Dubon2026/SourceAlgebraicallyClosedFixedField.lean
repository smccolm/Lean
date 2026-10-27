import Dubon2026.SourcePureTranscendentalConstantIntersection

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> fixed-field descent of the proved twist-stable cusp image. Every
coefficient outside the original characteristic-zero field is moved by an
automorphism of the algebraically closed ambient field. Algebraic and
transcendental coefficients are separated using actual intermediate fields
and the native infinite Galois fixed-field theorem. Adapted from
anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range. -/
namespace Dubon2026.SourceFunctionField.ConstantFixedField
noncomputable section
open IntermediateField

theorem exists_algEquiv_apply_ne_of_exists_notMem {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsAlgClosed E] [CharZero F] {c : E}
    (h : ∃ K₁ : IntermediateField F E, Algebra.IsAlgebraic ↥K₁ E ∧ c ∉ K₁) :
    ∃ σ : E ≃ₐ[F] E, σ c ≠ c := by
  obtain ⟨K₁, halg, hcK₁⟩ := h
  haveI : IsAlgClosure ↥K₁ E := ⟨inferInstance, halg⟩
  haveI : CharZero ↥K₁ :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F ↥K₁)
  haveI : IsGalois ↥K₁ E := IsAlgClosure.isGalois _ _
  have hcbot : c ∉ (⊥ : IntermediateField ↥K₁ E) := by
    rw [IntermediateField.mem_bot]
    rintro ⟨a, rfl⟩
    exact hcK₁ a.2
  rw [InfiniteGalois.mem_bot_iff_fixed] at hcbot
  push Not at hcbot
  obtain ⟨σ, hσ⟩ := hcbot
  exact ⟨σ.restrictScalars F, hσ⟩

theorem exists_intermediateField_isAlgebraic_notMem_of_isAlgebraic {F E : Type*} [Field F]
    [Field E] [Algebra F E] {c : E} (halg : IsAlgebraic F c)
    (hc : c ∉ (⊥ : IntermediateField F E)) :
    ∃ K₁ : IntermediateField F E, Algebra.IsAlgebraic ↥K₁ E ∧ c ∉ K₁ := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F E
  refine ⟨IntermediateField.adjoin F (Set.range ((↑) : s → E)), hs.isAlgebraic_field, ?_⟩
  intro hmem
  exact hc (mem_bot_of_isAlgebraic_of_mem_adjoin_algebraicIndependent hs.1 hmem halg)

open Polynomial in

theorem notMem_adjoin_sq_of_transcendental {F E : Type*} [Field F] [Field E] [Algebra F E]
    {c : E} (hc : Transcendental F c) : c ∉ IntermediateField.adjoin F {c ^ 2} := by
  intro hmem
  rw [IntermediateField.mem_adjoin_simple_iff] at hmem
  obtain ⟨r, s, hrs⟩ := hmem
  have hcomp : ∀ P : F[X], (aeval (c ^ 2)) P = (aeval c) (P.comp (X ^ 2)) := fun P ↦ by
    rw [aeval_comp, map_pow, aeval_X]
  rw [hcomp r, hcomp s] at hrs
  have hc0 : c ≠ 0 := fun h ↦ hc (h ▸ isAlgebraic_zero)
  have hsc_ne : (aeval c) (s.comp (X ^ 2)) ≠ 0 := fun h0 ↦ hc0 (by rw [hrs, h0, div_zero])
  have heq : (aeval c) (X * s.comp (X ^ 2)) = (aeval c) (r.comp (X ^ 2)) := by
    rw [map_mul, aeval_X]; exact (eq_div_iff hsc_ne).mp hrs
  have hpeq : (X : F[X]) * s.comp (X ^ 2) = r.comp (X ^ 2) :=
    (transcendental_iff_injective.mp hc) heq
  have hsc2_ne : s.comp ((X : F[X]) ^ 2) ≠ 0 := fun h ↦ hsc_ne (h ▸ map_zero _)
  have hdeg := congrArg Polynomial.natDegree hpeq
  rw [natDegree_mul X_ne_zero hsc2_ne, natDegree_X, natDegree_comp, natDegree_comp,
    natDegree_X_pow] at hdeg
  omega

theorem exists_algEquiv_apply_ne_of_transcendental {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsAlgClosed E] [CharZero F] {c : E} (hc : Transcendental F c) :
    ∃ σ : E ≃ₐ[F] E, σ c ≠ c := by
  set F' := IntermediateField.adjoin F ({c ^ 2} : Set E) with hF'_def
  have halg_F' : IsAlgebraic ↥F' c :=
    ⟨Polynomial.X ^ 2 - Polynomial.C ⟨c ^ 2, IntermediateField.mem_adjoin_simple_self F (c ^ 2)⟩,
      Polynomial.X_pow_sub_C_ne_zero two_pos _, by simp⟩
  have hc_F' : c ∉ (⊥ : IntermediateField ↥F' E) := by
    rw [IntermediateField.mem_bot]; rintro ⟨a, ha⟩
    exact notMem_adjoin_sq_of_transcendental hc (hF'_def ▸ ha ▸ a.2)
  haveI : CharZero ↥F' :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F ↥F')
  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_ne_of_exists_notMem
    (exists_intermediateField_isAlgebraic_notMem_of_isAlgebraic halg_F' hc_F')
  exact ⟨σ.restrictScalars F, hσ⟩

theorem exists_algEquiv_apply_ne {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsAlgClosed E] [CharZero F] {c : E} (hc : c ∉ (⊥ : IntermediateField F E)) :
    ∃ σ : E ≃ₐ[F] E, σ c ≠ c := by
  by_cases halg : IsAlgebraic F c
  · exact exists_algEquiv_apply_ne_of_exists_notMem
      (exists_intermediateField_isAlgebraic_notMem_of_isAlgebraic halg hc)
  · exact exists_algEquiv_apply_ne_of_transcendental halg

theorem mem_range_of_fixed {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsAlgClosed E] [CharZero F] {c : E}
    (hfix : ∀ σ : E ≃ₐ[F] E, σ c = c) : ∃ a : F, algebraMap F E a = c := by
  by_contra hn
  have hc : c ∉ (⊥ : IntermediateField F E) := fun h => hn (IntermediateField.mem_bot.mp h)
  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_ne hc
  exact hσ (hfix σ)

end
end Dubon2026.SourceFunctionField.ConstantFixedField
