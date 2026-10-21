import Dubon2026.CosetTraceOneCocycles
import Mathlib.LinearAlgebra.Isomorphisms

/-! The existing finite coset trace descended to native H1.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> residual modular Galois
association -> the original H1 Hecke eigensystem -> restriction,
conjugation and finite coset corestriction. The existing exact cocycle
and coboundary formulas supply the entire quotient descent.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  (S : Subgroup G) [Fintype (G ⧸ S)]

/-- The original finite coset sum, restricted to actual one-cocycles. -/
def sourceHeckeTraceCocycles :
    groupCohomology.cocycles₁ (restrictedCoefficientRep A S.subtype) →ₗ[R]
      groupCohomology.cocycles₁ A :=
  (cosetTraceOne A S).restrict (fun c hc => cosetTraceOne_mem_cocycles A S ⟨c, hc⟩)

private def traceQuotient :
    (groupCohomology.cocycles₁ (restrictedCoefficientRep A S.subtype) ⧸
      LinearMap.ker (groupCohomology.H1π (restrictedCoefficientRep A S.subtype)).hom) →ₗ[R]
        groupCohomology.H1 A :=
  (LinearMap.ker (groupCohomology.H1π (restrictedCoefficientRep A S.subtype)).hom).liftQ
    ((groupCohomology.H1π A).hom.comp (sourceHeckeTraceCocycles A S)) (by
      intro c hc
      obtain ⟨v, hv⟩ := (groupCohomology.H1π_eq_zero_iff c).mp hc
      apply (groupCohomology.H1π_eq_zero_iff _).mpr
      refine ⟨cosetTraceZero A S v, ?_⟩
      change groupCohomology.d₀₁ A (cosetTraceZero A S v) = cosetTraceOne A S c
      rw [← cosetTraceOne_coboundary, hv])

/-- Corestriction on the full native H1, with the actual original coset representatives. -/
def sourceHeckeH1Trace :
    groupCohomology.H1 (restrictedCoefficientRep A S.subtype) →ₗ[R]
      groupCohomology.H1 A :=
  traceQuotient A S ∘ₗ
    ((groupCohomology.H1π (restrictedCoefficientRep A S.subtype)).hom.quotKerEquivOfSurjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)).symm.toLinearMap

/-- The native H1 trace is represented by the proved literal finite cocycle sum. -/
theorem sourceHeckeH1Trace_cocycle
    (c : groupCohomology.cocycles₁ (restrictedCoefficientRep A S.subtype)) :
    sourceHeckeH1Trace A S
        (groupCohomology.H1π (restrictedCoefficientRep A S.subtype) c) =
      groupCohomology.H1π A (sourceHeckeTraceCocycles A S c) := by
  change traceQuotient A S
    (((groupCohomology.H1π (restrictedCoefficientRep A S.subtype)).hom.quotKerEquivOfSurjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)).symm
        ((groupCohomology.H1π (restrictedCoefficientRep A S.subtype)).hom c)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end
end Dubon2026
