import Dubon2026.OriginalInfiniteKernelClassSystemTrace
import Dubon2026.OriginalSinglePrimeTraceInfiniteKernel
import Dubon2026.OriginalCanonicalLocalClassNormalization

/-! # Source normalization of local classes from the zero-infinite total

The actual local-class trace has zero infinite localization, so the
restricted total formula suffices to normalize the same decomposition
class invariant. This uses the original local witness and coefficient
trace square required for DUB-17's source completion restrictions.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))

/-- The genuine original local trace lies in the proved zero-infinite
domain, which suffices for its source-normalized class invariant. -/
theorem originalIdeleClass_local_normalization_of_infinite_kernel
    (localInvariant total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (invG : groupCohomology (originalIdeleClassRep K L) 2 →+ AddCircle (1 : ℚ))
    (invD : groupCohomology (Rep.res (OriginalFiniteDecompositionGroup K L w).subtype
      (originalIdeleClassRep K L)) 2 →+ AddCircle (1 : ℚ))
    (htotal : ∀ x : groupCohomology (originalFullIdeleRep K L) 2,
      (∀ v : NumberField.InfinitePlace L, originalFullIdeleInfiniteH2 K L v x = 0) →
      invG ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) = total x)
    (htrace : letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
      ∀ y : groupCohomology (Rep.res (OriginalFiniteDecompositionGroup K L w).subtype
        (originalIdeleClassRep K L)) 2,
        invG ((subgroupCohomologyTrace (originalIdeleClassRep K L)
          (OriginalFiniteDecompositionGroup K L w) 2).hom y) = invD y)
    (hn : OriginalLocalTraceJointNormalization K L w localInvariant total) :
    OriginalLocalClassNormalization K L w localInvariant invD := by
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  obtain ⟨y, hl, hg⟩ := hn
  refine ⟨y, hl, ?_⟩
  let z := (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
    (originalIdeleSingleFiniteRepHom K L w) y
  have hc := congrArg (fun f => f.hom z)
    (originalCohomologyTrace_coefficient_naturality (OriginalFiniteDecompositionGroup K L w)
      (originalFullClassRepHom K L) 2)
  have he := congrArg (fun f => f.hom y) (originalSinglePrimeIdeleH2Lift_eq_trace K L w)
  have ht := htotal (originalSinglePrimeIdeleH2Lift K L w y)
    (fun v => originalSinglePrimeIdeleH2Lift_infinite K L w v y)
  exact (htrace _).symm.trans ((congrArg invG hc).trans
    ((congrArg (fun z => invG ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalFullClassRepHom K L) z)) he.symm).trans (ht.trans hg)))

/-- The constructed zero-infinite invariant system gives the original
source-normalized decomposition class invariant at the same finite prime. -/
theorem originalIdeleClass_infinite_kernel_prime_normalization
    (localInvariant total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (hc : OriginalInfiniteKernelClassInvariantTraceSystem K L total)
    (hn : OriginalLocalTraceJointNormalization K L w localInvariant total) :
    OriginalCanonicalPrimeClassNormalization K L w localInvariant := by
  obtain ⟨invG, _, _, ht, hs⟩ := hc
  obtain ⟨invD, hiD, hrD, _, htr⟩ := hs (OriginalFiniteDecompositionGroup K L w)
  exact ⟨invD, hiD, hrD,
    originalIdeleClass_local_normalization_of_infinite_kernel K L w localInvariant total invG invD ht htr hn⟩

end
end Dubon2026
