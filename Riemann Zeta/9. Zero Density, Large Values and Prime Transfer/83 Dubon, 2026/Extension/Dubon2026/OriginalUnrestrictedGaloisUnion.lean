import Dubon2026.UnramifiedGaloisStageUnion
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The auxiliary unrestricted arithmetic union

With exceptional integer zero every finite prime contains that integer,
so the defining union includes every finite Galois subfield. In a Galois
ambient field it is exactly the whole field. This auxiliary realization
allows the existing all-prime class normalization to be applied to an
actual Kummer extension. It does not change the original nonzero
exceptional integer or the required ramification of the final norm field.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

omit [NumberField K] in
/-- The union with no restriction on ramification is the entire Galois
ambient field, by the actual finite Galois closure of each element. -/
theorem originalUnramifiedGaloisUnion_zero_eq_top [IsGalois K Ω] :
    originalUnramifiedGaloisUnion (Ω := Ω) (0 : 𝓞 K) = ⊤ := by
  apply top_unique
  intro x _
  let F := FiniteGaloisIntermediateField.adjoin K ({x} : Set Ω)
  have hF : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      algebraMap (𝓞 K) (𝓞 F) 0 ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
    intro w hw
    exact (hw (by simp only [map_zero]; exact w.asIdeal.zero_mem)).elim
  exact originalUnramifiedGaloisStage_le_union (0 : 𝓞 K) ⟨F, hF⟩
    (FiniteGaloisIntermediateField.subset_adjoin K {x} (Set.mem_singleton x))

/-- The auxiliary unrestricted union has its literal ambient-field
isomorphism; no arbitrary field model is substituted. -/
def originalUnrestrictedGaloisUnionEquiv [IsGalois K Ω] :
    originalUnramifiedGaloisUnion (Ω := Ω) (0 : 𝓞 K) ≃ₐ[K] Ω :=
  (IntermediateField.equivOfEq (originalUnramifiedGaloisUnion_zero_eq_top K Ω)).trans
    IntermediateField.topEquiv

omit [NumberField K] in
/-- The actual unrestricted union in an algebraic closure is itself
algebraically closed, so the full Kummer field can be constructed there. -/
theorem originalUnrestrictedGaloisUnion_isAlgClosed [IsGalois K Ω] [IsAlgClosed Ω] :
    IsAlgClosed (originalUnramifiedGaloisUnion (Ω := Ω) (0 : 𝓞 K)) :=
  IsAlgClosed.of_ringEquiv Ω _ (originalUnrestrictedGaloisUnionEquiv K Ω).symm.toRingEquiv

end
end Dubon2026
