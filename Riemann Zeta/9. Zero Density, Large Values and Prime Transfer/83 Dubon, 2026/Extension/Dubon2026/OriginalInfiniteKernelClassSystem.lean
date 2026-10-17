import Dubon2026.OriginalIdeleInfiniteH2
import Dubon2026.OriginalFullIdeleCohomologySequence

/-! # The class invariant statement on the original zero-infinite part

This proposition records the exact global and subgroup invariant system,
its images, the actual idele-total formula on the zero-infinite part and the restriction-index law.
The definition alone asserts no existence. The auxiliary-idele construction
and the arithmetic all-stage theorem below supply its proofs for DUB-17.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

/-- The original global and subgroup invariant system, with its actual total formula explicitly restricted to zero original infinite localization. This definition alone asserts no existence. -/
def OriginalInfiniteKernelClassInvariantSystem
    (K E : Type) [Field K] [Field E] [NumberField E] [Algebra K E]
    (totalE : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ)) : Prop :=
    ∃ invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ),
      Function.Injective invG ∧
      (∀ z : AddCircle (1 : ℚ), z ∈ invG.range ↔ Module.finrank K E • z = 0) ∧
      (∀ v : groupCohomology (originalFullIdeleRep K E) 2,
        (∀ w : NumberField.InfinitePlace E, originalFullIdeleInfiniteH2 K E w v = 0) →
        invG ((groupCohomology.functor ℤ Gal(E/K) 2).map (originalFullClassRepHom K E) v) = totalE v) ∧
      ∀ S : Subgroup Gal(E/K),
        ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K E)) 2 →+ AddCircle (1 : ℚ),
          Function.Injective invS ∧
          (∀ z : AddCircle (1 : ℚ), z ∈ invS.range ↔ Nat.card S • z = 0) ∧
          ∀ v : groupCohomology (originalIdeleClassRep K E) 2,
            invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K E))) 2).hom v) =
              S.index • invG v

end
end Dubon2026
