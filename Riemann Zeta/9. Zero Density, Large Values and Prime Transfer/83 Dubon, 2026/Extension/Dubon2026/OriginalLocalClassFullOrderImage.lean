import Dubon2026.OriginalCanonicalLocalClassNormalization

/-! # The normalized original local class has full-order class image

Injectivity of the constructed decomposition invariant identifies the
order of the actual idele-class image with the order of the normalized
reciprocal. This is an exact consumer of the local normalization, needed
before the decomposition-group class-formation comparison for DUB-17.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

/-- An actual local H2 class whose original subgroup idele-class image has order exactly the decomposition-group order. -/
def OriginalLocalClassFullOrderImage
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : Prop :=
    ∃ y : groupCohomology (originalAdicUnitRep K L w) 2,
      addOrderOf ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
        ((Rep.resFunctor (OriginalFiniteDecompositionGroup K L w).subtype).map
          (originalFullClassRepHom K L))
        ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
          (originalIdeleSingleFiniteRepHom K L w) y)) =
        Nat.card (OriginalFiniteDecompositionGroup K L w)

/-- The same original local class from canonical normalization has full-order image under the actual subgroup idele-class map. -/
theorem originalIdeleClass_local_full_order_of_canonical_normalization
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (localInvariant : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (hn : OriginalCanonicalPrimeClassNormalization K L w localInvariant) :
    OriginalLocalClassFullOrderImage K L w := by
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  obtain ⟨invD, hiD, _, y, _, hy⟩ := hn
  refine ⟨y, ?_⟩
  calc
    _ = addOrderOf (invD ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
        ((Rep.resFunctor (OriginalFiniteDecompositionGroup K L w).subtype).map
          (originalFullClassRepHom K L))
        ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
          (originalIdeleSingleFiniteRepHom K L w) y))) := (addOrderOf_injective invD hiD _).symm
    _ = Nat.card (OriginalFiniteDecompositionGroup K L w) := by
      rw [hy]
      letI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
      exact AddCircle.addOrderOf_period_div (p := (1 : ℚ)) Nat.card_pos

end
end Dubon2026
