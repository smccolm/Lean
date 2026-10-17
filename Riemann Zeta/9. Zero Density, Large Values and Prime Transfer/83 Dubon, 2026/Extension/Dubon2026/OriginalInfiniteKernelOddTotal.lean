import Dubon2026.OriginalInfiniteKernelInvariantChoice
import Dubon2026.OriginalFullIdeleOddDegreeInfinite

namespace Dubon2026
noncomputable section
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

/-- At odd degree the proved class invariant has its original idele-total
formula on all idele H2 inputs, with no infinite-coordinate premise. -/
theorem originalInfiniteKernelClassInvariant_total_of_odd
    (K E : Type) [Field K] [Field E] [NumberField E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (total : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ))
    (h : OriginalInfiniteKernelClassInvariantSystem K E total)
    (hn : Odd (Module.finrank K E))
    (x : groupCohomology (originalFullIdeleRep K E) 2) :
    originalInfiniteKernelClassInvariant K E total h
      ((groupCohomology.functor ℤ Gal(E/K) 2).map (originalFullClassRepHom K E) x) = total x :=
  originalInfiniteKernelClassInvariant_total K E total h x
    (fun w => originalFullIdeleInfiniteH2_eq_zero_of_odd_degree K E hn x w)

end
end Dubon2026
