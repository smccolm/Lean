import Dubon2026.OriginalNormalizedLocalClassChoice

/-! # One global class compatible with every normalized local choice

Keep the constructed global class and the existence of normalized local
classes. The actual local-image comparison then identifies its restrictions
with every supplied normalized local class, as required by DUB-17's local
fundamental-class compatibility clause.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

/-- One full-order original global class has normalized local witnesses and restricts to every normalized original local-class image; this proposition alone asserts no existence. -/
def OriginalUniversalNormalizedLocalRestrictions
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (localInvariant : IsDedekindDomain.HeightOneSpectrum (𝓞 L) →
      groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ)) : Prop :=
    ∃ u : groupCohomology (originalIdeleClassRep K L) 2,
      addOrderOf u = Module.finrank K L ∧
      ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
        letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
        (∃ y : groupCohomology (originalAdicUnitRep K L w) 2,
          localInvariant w (originalSinglePrimeIdeleH2Lift K L w y) =
            (↑((1 : ℚ) / Nat.card (OriginalFiniteDecompositionGroup K L w)) : AddCircle (1 : ℚ))) ∧
        ∀ y : groupCohomology (originalAdicUnitRep K L w) 2,
          localInvariant w (originalSinglePrimeIdeleH2Lift K L w y) =
            (↑((1 : ℚ) / Nat.card (OriginalFiniteDecompositionGroup K L w)) : AddCircle (1 : ℚ)) →
          (groupCohomology.map (OriginalFiniteDecompositionGroup K L w).subtype
            (𝟙 (Rep.res (OriginalFiniteDecompositionGroup K L w).subtype
              (originalIdeleClassRep K L))) 2).hom u =
            (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
              ((Rep.resFunctor (OriginalFiniteDecompositionGroup K L w).subtype).map
                (originalFullClassRepHom K L))
              ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
                (originalIdeleSingleFiniteRepHom K L w) y)

/-- The constructed common global class is compatible with every supplied normalized local class, by injectivity of the canonical class invariant on actual local images. -/
theorem originalIdeleClass_universal_local_restrictions
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (localInvariant : IsDedekindDomain.HeightOneSpectrum (𝓞 L) →
      groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (hc : OriginalCanonicalClassInvariantTraceSystem K L total)
    (hf : OriginalLocalTraceTotalFormula K L localInvariant total)
    (hn : OriginalNormalizedLocalRestrictions K L localInvariant) :
    OriginalUniversalNormalizedLocalRestrictions K L localInvariant := by
  obtain ⟨u, hu, hl⟩ := hn
  refine ⟨u, hu, fun w => ?_⟩
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  obtain ⟨y, hy, hres⟩ := hl w
  refine ⟨⟨y, hy⟩, fun z hz => ?_⟩
  exact hres.trans (originalIdeleClass_local_image_eq_of_invariant
    K L localInvariant total hc hf w y z (hy.trans hz.symm))

end
end Dubon2026
