import Dubon2026.OriginalInfiniteKernelSubgroupIdeleTotal
import Dubon2026.OriginalSinglePrimeTraceInfiniteKernel
import Dubon2026.OriginalLocalTraceTotalFormula
import Dubon2026.OriginalCanonicalClassLocalRestrictions

/-! # Choice independence of normalized original local-class images

The actual class projection and genuine cohomology trace identify the
subgroup class invariant with the local prime coordinate on every local
class. Injectivity then compares any two equally normalized local classes.
This upgrades DUB-17's constructed local restrictions to arbitrary supplied
normalized local classes without assuming their equality.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (localInvariant : IsDedekindDomain.HeightOneSpectrum (𝓞 L) →
    groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
  (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))

/-- Two original local classes with equal local prime invariant have equal actual subgroup class images, using the proved canonical trace total formula. -/
theorem originalIdeleClass_local_image_eq_of_invariant_of_infinite_kernel
    (hc : OriginalInfiniteKernelClassInvariantTraceSystem K L total)
    (hf : OriginalLocalTraceTotalFormula K L localInvariant total)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
    ∀ x y : groupCohomology (originalAdicUnitRep K L w) 2,
      localInvariant w (originalSinglePrimeIdeleH2Lift K L w x) =
        localInvariant w (originalSinglePrimeIdeleH2Lift K L w y) →
      (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
        ((Rep.resFunctor (OriginalFiniteDecompositionGroup K L w).subtype).map
          (originalFullClassRepHom K L))
        ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
          (originalIdeleSingleFiniteRepHom K L w) x) =
      (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
        ((Rep.resFunctor (OriginalFiniteDecompositionGroup K L w).subtype).map
          (originalFullClassRepHom K L))
        ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
          (originalIdeleSingleFiniteRepHom K L w) y) := by
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  intro x y hxy
  obtain ⟨invG, _, _, ht, hs⟩ := hc
  obtain ⟨invD, hiD, _, _, htrace⟩ := hs (OriginalFiniteDecompositionGroup K L w)
  have hv (z : groupCohomology (originalAdicUnitRep K L w) 2) :
      invD ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
        ((Rep.resFunctor (OriginalFiniteDecompositionGroup K L w).subtype).map
          (originalFullClassRepHom K L))
        ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
          (originalIdeleSingleFiniteRepHom K L w) z)) =
      localInvariant w (originalSinglePrimeIdeleH2Lift K L w z) := by
    have he := congrArg (fun f => f.hom z) (originalSinglePrimeIdeleH2Lift_eq_trace K L w)
    have hp := originalIdeleClass_invariant_subgroup_projection_trace_of_infinite K L
      (OriginalFiniteDecompositionGroup K L w) total invG invD ht htrace
      ((groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
        (originalIdeleSingleFiniteRepHom K L w) z)
      (fun v => (congrArg (originalFullIdeleInfiniteH2 K L v) he.symm).trans
        (originalSinglePrimeIdeleH2Lift_infinite K L w v z))
    exact hp.trans ((congrArg total he.symm).trans (hf w z))
  exact hiD ((hv x).trans (hxy.trans (hv y).symm))

end
end Dubon2026
