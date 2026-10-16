import Dubon2026.OriginalFullIdeleCohomologySequence

/-! # The full finite-stage canonical class invariant statement

This proposition records the exact global and subgroup invariant system,
its images, the actual idele-total formula and the restriction-index law.
The definition alone asserts no existence. The auxiliary-idele construction
and the arithmetic all-stage theorem below supply its proofs for DUB-17.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

/-- The complete original class-invariant system, with the specified actual idele total and original subgroup maps. -/
def OriginalCanonicalClassInvariantSystem
    (K E : Type) [Field K] [Field E] [NumberField E] [Algebra K E]
    (totalE : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ)) : Prop :=
    ∃ invG : groupCohomology (originalIdeleClassRep K E) 2 →+ AddCircle (1 : ℚ),
      Function.Injective invG ∧
      (∀ z : AddCircle (1 : ℚ), z ∈ invG.range ↔ Module.finrank K E • z = 0) ∧
      (∀ v : groupCohomology (originalFullIdeleRep K E) 2,
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
