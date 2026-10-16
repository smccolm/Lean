import Dubon2026.OriginalSinglePrimeTraceCoefficients
import Dubon2026.OriginalCohomologyTraceNaturality

/-! # Lift an original local H2 class at any finite prime

Shapiro and the actual single-prime trace give a section of localization
without assuming that the decomposition subgroup is the whole Galois
group. The lift is the genuine corestriction of the single-prime insertion,
as required for DUB-17's local-fundamental-class normalization.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))
  [Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w)]

/-- Lift the actual local class by inverse Shapiro and the original single-prime coefficient trace. -/
def originalSinglePrimeIdeleH2Lift :
    groupCohomology (originalAdicUnitRep K L w) 2 ⟶
      groupCohomology (originalFullIdeleRep K L) 2 :=
    (groupCohomology.coindIso (originalAdicUnitRep K L w) 2).inv ≫
      (groupCohomology.functor ℤ Gal(L/K) 2).map (originalSinglePrimeCoinducedTrace K L w)

/-- Localizing the original single-prime lift recovers exactly the original local H2 class. -/
theorem originalSinglePrimeIdeleH2Lift_section :
    originalSinglePrimeIdeleH2Lift K L w ≫ originalFullIdeleAdicH2 K L w =
      𝟙 (groupCohomology (originalAdicUnitRep K L w) 2) := by
  exact originalShapiro_lift_section (OriginalFiniteDecompositionGroup K L w)
    (originalSinglePrimeCoinducedTrace K L w) (originalFullIdeleAdicRepHom K L w)
    (originalSinglePrimeCoinducedTrace_evaluation K L w) 2

/-- The lift is precisely single-prime insertion followed by the genuine original subgroup trace. -/
theorem originalSinglePrimeIdeleH2Lift_eq_trace :
    originalSinglePrimeIdeleH2Lift K L w =
      (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
        (originalIdeleSingleFiniteRepHom K L w) ≫
          subgroupCohomologyTrace (originalFullIdeleRep K L)
            (OriginalFiniteDecompositionGroup K L w) 2 := by
  exact originalCohomologyTrace_coinduced_lift (OriginalFiniteDecompositionGroup K L w)
    (originalIdeleSingleFiniteRepHom K L w) 2

/-- Outside the chosen original prime's Galois orbit, the actual local H2 lift has zero localization. -/
theorem originalSinglePrimeIdeleH2Lift_outside_orbit
    (v : HeightOneSpectrum (𝓞 L))
    (hv : ∀ σ : Gal(L/K), numberFieldGaloisPlaceEquiv K L σ w ≠ v)
    (x : groupCohomology (originalAdicUnitRep K L w) 2) :
    originalFullIdeleAdicH2 K L v (originalSinglePrimeIdeleH2Lift K L w x) = 0 := by
  have hz (y : groupCohomology
      (Rep.coind (OriginalFiniteDecompositionGroup K L w).subtype (originalAdicUnitRep K L w)) 2) :
      originalFullIdeleAdicH2 K L v
        ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSinglePrimeCoinducedTrace K L w) y) = 0 := by
    induction y using groupCohomology.H2_induction_on with
    | h c =>
      simp only [originalFullIdeleAdicH2, groupCohomology.functor]
      erw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply]
      rw [← map_zero (groupCohomology.H2π (originalAdicUnitRep K L v)).hom]
      apply congrArg (groupCohomology.H2π _)
      apply Subtype.ext
      funext g
      exact originalSinglePrimeCoinducedTrace_outside_orbit K L w v hv _
  exact hz ((groupCohomology.coindIso (originalAdicUnitRep K L w) 2).inv x)

end
end Dubon2026
