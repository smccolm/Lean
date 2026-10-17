import Dubon2026.OriginalInfiniteKernelClassSystem

namespace Dubon2026
noncomputable section
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K E : Type) [Field K] [Field E] [NumberField E] [Algebra K E]
  (total : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ))
  (h : OriginalInfiniteKernelClassInvariantSystem K E total)

/-- Extract the global invariant from a proved original normalized system.
The actual scalar-stage theorem supplies this system without a premise. -/
def originalInfiniteKernelClassInvariant :
    groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ) :=
  Classical.choose h

/-- The extracted invariant retains the proved injectivity clause. -/
theorem originalInfiniteKernelClassInvariant_injective :
    Function.Injective (originalInfiniteKernelClassInvariant K E total h) :=
  (Classical.choose_spec h).1

/-- The extracted invariant retains the exact original total formula. -/
theorem originalInfiniteKernelClassInvariant_total
    (x : groupCohomology (originalFullIdeleRep K E) 2)
    (hx : ∀ w : NumberField.InfinitePlace E, originalFullIdeleInfiniteH2 K E w x = 0) :
    originalInfiniteKernelClassInvariant K E total h
      ((groupCohomology.functor ℤ Gal(E/K) 2).map (originalFullClassRepHom K E) x) = total x :=
  (Classical.choose_spec h).2.2.1 x hx

end
end Dubon2026
