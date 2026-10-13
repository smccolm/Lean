import Dubon2026.NumberFieldSupportedIdeleExact
import Dubon2026.NumberFieldIdeleFiniteClassSupport

/-! # The original supported-idele quotient is the original global class group

For a constructed finite enlargement of any prescribed S, the actual
supported ideles map onto the original global idele classes. Its already
proved principal S-unit kernel gives the exact original quotient. This
closes the algebraic supported-idele sequence input to DUB-17's global
norm-index route. The actual Galois action and cohomological norm-index
calculation remain separate obligations.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- A constructed finite enlargement makes the original supported-idele map onto the original global classes. -/
theorem numberField_exists_supportedIdeleClassMap_surjective
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      Function.Surjective (numberFieldSupportedIdeleClassMap K S) := by
  obtain ⟨S, hS, hprincipal⟩ := numberField_exists_finite_principal_idele_support K S₀
  refine ⟨S, hS, ?_⟩
  intro c
  induction c using QuotientGroup.induction_on with
  | H a =>
    obtain ⟨x, hx⟩ := hprincipal a
    refine ⟨⟨a / numberFieldPrincipalIdele K x, hx⟩, ?_⟩
    change QuotientGroup.mk' (numberFieldPrincipalIdele K).range
      (a / numberFieldPrincipalIdele K x) = QuotientGroup.mk' _ a
    have hp : QuotientGroup.mk' (numberFieldPrincipalIdele K).range
        (numberFieldPrincipalIdele K x) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
    rw [map_div, hp, div_one]

/-- For a constructed finite S, the original supported-ideles modulo principal S-units are the original global idele classes. -/
theorem numberField_exists_supportedIdeleQuotientEquiv
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      Nonempty (numberFieldSupportedIdeles K S ⧸
        (numberFieldSupportedPrincipalIdele K S).range ≃* OriginalNumberFieldIdeleClassGroup K) := by
  obtain ⟨S, hS, hf⟩ := numberField_exists_supportedIdeleClassMap_surjective K S₀
  refine ⟨S, hS, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq
    (numberFieldSupportedIdeleClassMap_ker K S).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (numberFieldSupportedIdeleClassMap K S) hf)

end
end Dubon2026
