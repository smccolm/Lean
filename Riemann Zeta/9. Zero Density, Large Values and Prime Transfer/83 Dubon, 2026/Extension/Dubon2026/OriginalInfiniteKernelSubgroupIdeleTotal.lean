import Dubon2026.OriginalInfiniteKernelClassSystemTrace
import Dubon2026.OriginalCohomologyTraceNaturality

/-! # The total formula for original subgroup traces in the zero-infinite part

Apply coefficient naturality to the original idele-to-class projection.
The previously constructed normalized invariants therefore evaluate a
subgroup idele class by the canonical total of its genuine trace. This
removes the class/projection comparison needed before the local
fundamental-class normalization on the DUB-17 dependency chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K E : Type) [Field K] [Field E] [NumberField E] [Algebra K E]

/-- Global canonical-total and class-trace compatibility determine the invariant of the actual subgroup idele projection. -/
theorem originalIdeleClass_invariant_subgroup_projection_trace_of_infinite
    (S : Subgroup Gal(E/K)) [Fintype (Gal(E/K) ⧸ S)]
    (total : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ))
    (invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ))
    (invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2 →+ AddCircle (1 : ℚ))
    (htotal : ∀ x : groupCohomology (originalFullIdeleRep K E) 2,
      (∀ v : NumberField.InfinitePlace E, originalFullIdeleInfiniteH2 K E v x = 0) →
      invG ((groupCohomology.functor ℤ Gal(E/K) 2).map (originalFullClassRepHom K E) x) = total x)
    (htrace : ∀ y : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2,
      invG ((subgroupCohomologyTrace (originalIdeleClassRep K E) S 2).hom y) = invS y)
    (x : groupCohomology (Rep.res S.subtype (originalFullIdeleRep K E)) 2)
    (hInf : ∀ v : NumberField.InfinitePlace E, originalFullIdeleInfiniteH2 K E v
      ((subgroupCohomologyTrace (originalFullIdeleRep K E) S 2).hom x) = 0) :
    invS ((groupCohomology.functor ℤ S 2).map
      ((Rep.resFunctor S.subtype).map (originalFullClassRepHom K E)) x) =
      total ((subgroupCohomologyTrace (originalFullIdeleRep K E) S 2).hom x) := by
  have hn := congrArg (fun f => f.hom x)
    (originalCohomologyTrace_coefficient_naturality S (originalFullClassRepHom K E) 2)
  exact (htrace _).symm.trans ((congrArg invG hn).trans (htotal _ hInf))

end
end Dubon2026
