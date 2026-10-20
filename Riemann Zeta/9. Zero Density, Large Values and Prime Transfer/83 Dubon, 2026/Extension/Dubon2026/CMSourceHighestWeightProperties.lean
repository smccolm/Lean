import Dubon2026.CMSourceIntegralTensorIdentification

/-! The full original highest-weight coefficient identification as a named statement.
The proposition lists the genuine field-factor finiteness, irreducibility and
weight character, and the actual equivariant generic-fibre tensor comparison.
The theorem proves it from the original source constructions.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField ValuativeRel TensorProduct

variable (K E : Type) [Field K] [NumberField K] [IsCMField K] [Field E] [CharZero E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]
  (places : Set (HeightOneSpectrum (𝓞 K)))

/-- The exact original highest-weight generic-fibre conclusions for every source dominant embedding weight. This names a conclusion, and is proved below. -/
def CMSourceHighestWeightProperties : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (lam : IntegralCoefficientEmbeddingIndex K E p hp places → Fin (n + 1) → ℤ)
    (hlam : ∀ i, Antitone (lam i)),
    ∃ e : E ⊗[𝒪[E]] CMSourceIntegralWeight K E p hp places n lam ≃ₗ[E]
        IntegralInducedTensor E (n + 1) lam,
      (∀ i, Module.Finite E (generalLinearIntegralInducedSubmodule E (n + 1) (lam i)) ∧
        Representation.IsIrreducible (generalLinearIntegralInducedRepresentation E (n + 1) (lam i)) ∧
        ∀ b : generalLinearBorel E (n + 1),
          generalLinearIntegralInducedRepresentation E (n + 1) (lam i) b.val
            (integralDominantHighestVector E (lam i) (hlam i)) =
            ((∏ j : Fin (n + 1), generalLinearBorelDiagonalUnit b j ^ lam i j : Eˣ) : E) •
              integralDominantHighestVector E (lam i) (hlam i)) ∧
      e ((1 : E) ⊗ₜ[𝒪[E]] integralHighestTensor 𝒪[E] lam hlam) =
        integralHighestTensor E lam hlam ∧
      ∀ (g : cmFiniteAdelicIntegralLevel K H)
        (z : E ⊗[𝒪[E]] CMSourceIntegralWeight K E p hp places n lam),
        e ((cmSourceIntegralWeightRepresentation K E p hp places n H lam g).baseChange E z) =
          cmSourceFieldWeightRepresentation K E p hp places n H lam g (e z)

/-- Every displayed highest-weight and original generic-fibre conclusion is derived for the actual source coefficient tensor. -/
theorem cmSourceHighestWeight_properties : CMSourceHighestWeightProperties K E p hp places := by
  intro n H lam hlam
  obtain ⟨e, hirr, hhighest, haction⟩ :=
    cmSourceIntegralWeight_genericFibre_identification K E p hp places n H lam hlam
  refine ⟨e, ?_, hhighest, haction⟩
  intro i
  exact ⟨inferInstance, hirr i, integralDominantHighestVector_action E (lam i) (hlam i)⟩

end
end Dubon2026
