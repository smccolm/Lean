import Dubon2026.OriginalInfiniteBaseChangeComparison
import Dubon2026.OriginalIdeleInfiniteH2
import Dubon2026.OriginalFullIdeleBaseChangeH2

/-! # Infinite localization commutes with the actual idele H2 base change

The original coefficient square identifies the two actual H2 maps.
Consequently zero original infinite localizations persist through the
auxiliary tower used to normalize DUB-17's constructed general-stage class.
-/
namespace Dubon2026
noncomputable section
open NumberField CategoryTheory
attribute [local instance 1100] Rep.hV2

variable (K E L M : Type) [Field K] [Field E] [Field L] [NumberField L]
  [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L]

/-- The actual infinite-completion H2 map intertwines localization and
genuine full-idele base change on every original class. -/
theorem originalFullIdeleInfiniteH2_baseChange
    (v : InfinitePlace M) (x : groupCohomology (originalFullIdeleRep K L) 2) :
    originalFullIdeleInfiniteH2 E M v (originalFullIdeleBaseChangeH2 K E L M x) =
      groupCohomology.map (originalInfiniteBaseChangeStabilizerHom K E L M v)
        (originalInfiniteBaseChangeRepHom K E L M v) 2
        (originalFullIdeleInfiniteH2 K L (v.comap (algebraMap L M)) x) := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c)) =
      groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c))
    simp only [groupCohomology.H2π_comp_map_apply]
    rfl

/-- Zero localization at all original infinite places persists under the
same genuine field base change, without a compatibility certificate. -/
theorem originalFullIdeleInfiniteH2_baseChange_zero
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : ∀ v : InfinitePlace L, originalFullIdeleInfiniteH2 K L v x = 0)
    (v : InfinitePlace M) :
    originalFullIdeleInfiniteH2 E M v (originalFullIdeleBaseChangeH2 K E L M x) = 0 := by
  rw [originalFullIdeleInfiniteH2_baseChange, hx, map_zero]

end
end Dubon2026
