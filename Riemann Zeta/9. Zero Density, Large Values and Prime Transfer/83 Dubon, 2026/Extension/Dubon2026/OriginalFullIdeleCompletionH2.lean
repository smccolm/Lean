import Dubon2026.OriginalIdeleAdicH2
import Dubon2026.OriginalGlobalCompletionH2

/-! # The actual full-idele class localized at the original completion

Use the already proved decomposition/completion cohomology isomorphism
on the literal idele coordinate. Principal inclusion gives exactly the
original global completion localization. The supported-idele theorem
also supplies finite support. These are the maps needed to descend the
proved prime-invariant sum toward DUB-17's full-order idele-class class.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Every actual full-idele H2 class has finite support for its literal original finite-prime localizations. -/
theorem originalFullIdeleAdicH2_exists_finite_support
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)), ∀ w ∉ S,
      originalFullIdeleAdicH2 K L w x = 0 := by
  obtain ⟨S, hS, hu, y, hy⟩ := originalIdeleH2_exists_supported_lift K L x
  refine ⟨S, ?_⟩
  intro w hw
  exact (congrArg (originalFullIdeleAdicH2 K L w) hy).symm.trans
    (originalFullIdeleAdicH2_supported_outside_zero K L S hS hu ⟨w, hw⟩ y)

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- Actual full-idele localization expressed in the genuine finite completion Galois cohomology. -/
def originalFullIdeleCompletionH2 :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    groupCohomology (originalFullIdeleRep K L) 2 →ₗ[ℤ]
      groupCohomology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) 2 :=
  (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv.symm.toLinearMap.comp
    (originalFullIdeleAdicH2 K L w).hom

/-- The genuine full-idele completion map on a principal class is exactly the existing original global completion map. -/
theorem originalFullIdeleCompletionH2_principal
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    originalFullIdeleCompletionH2 K L v w
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) =
      originalGlobalCompletionH2 K L v w x := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  let e := (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv
  exact (congrArg e.symm (originalFullIdeleAdicH2_principal K L w x)).trans
    ((congrArg e.symm (originalGlobalCompletionH2_decomposition K L v w x)).symm.trans
      (e.symm_apply_apply (originalGlobalCompletionH2 K L v w x)))

/-- Vanishing of the original idele coordinate implies vanishing in the same original completion cohomology. -/
theorem originalFullIdeleCompletionH2_eq_zero_of_adic
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : originalFullIdeleAdicH2 K L w x = 0) :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    originalFullIdeleCompletionH2 K L v w x = 0 :=
  (congrArg (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv.symm hx).trans
    (map_zero _)

end
end Dubon2026
