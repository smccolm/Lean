import Dubon2026.OriginalIdeleAdicH2

/-! # Finite support of the literal original global H2 localizations

The original principal class lifts to a constructed finite stable idele
support. The proved unramified outside integer-unit H2 vanishing then
kills every literal original completion localization outside that support.
This provides the actual finite set needed by DUB-17's constructed cyclic
cyclotomic local-degree stage, with no finite-support premise.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical

/-- Every original finite global-unit H2 class has zero actual finite-prime localizations outside a constructed finite set. -/
theorem originalGlobalAdicH2_exists_finite_support
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)),
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → originalGlobalAdicH2 K L w x = 0 := by
  obtain ⟨S, hS, hu, y, hy⟩ := originalIdeleH2_exists_supported_lift K L
    ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x)
  refine ⟨S, ?_⟩
  intro w hw
  rw [← originalFullIdeleAdicH2_principal, ← hy]
  exact originalFullIdeleAdicH2_supported_outside_zero K L S hS hu ⟨w, hw⟩ y

end
end Dubon2026
