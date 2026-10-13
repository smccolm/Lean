import Dubon2026.OriginalInfiniteDecompositionAction
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Literal global-unit localization at an original infinite place

These maps use the original infinite-place decomposition group and the literal
field-to-completion embedding. Their cocycle formula is the common
input for comparison with finite-support local detection and normalized
completion invariants, required to apply DUB-17's constructed cyclotomic
stage to the actual global H2 class.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [local instance] Units.mulDistribMulActionRight
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (w : InfinitePlace L)

/-- The actual infinite-place decomposition group acting on the original completion units. -/
def originalInfiniteUnitRep : Rep ℤ (OriginalInfiniteDecompositionGroup K L w) := by
  letI := originalInfiniteDecompositionAction K L w
  exact Rep.ofMulDistribMulAction (OriginalInfiniteDecompositionGroup K L w) w.Completionˣ

/-- The literal original completion embedding, equivariant for the original decomposition group. -/
def originalGlobalInfiniteUnitRepHom :
    Rep.res (OriginalInfiniteDecompositionGroup K L w).subtype (Rep.ofAlgebraAutOnUnits K L) ⟶
      originalInfiniteUnitRep K L w :=
  Rep.ofHom ⟨(Units.map (algebraMap L (w.Completion)).toMonoidHom).toAdditive.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    apply congrArg Additive.ofMul
    apply Units.ext
    exact (numberFieldGaloisArchimedeanTransport_algebraMap K L σ.val w w σ.property x.toMul.val).symm⟩

/-- Actual localization of the original global two-cocycle. -/
def originalGlobalInfiniteTwoCocycle :
    groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L) →
      groupCohomology.cocycles₂ (originalInfiniteUnitRep K L w) :=
  groupCohomology.mapCocycles₂ (OriginalInfiniteDecompositionGroup K L w).subtype
    (originalGlobalInfiniteUnitRepHom K L w)

/-- The localized cocycle is exactly subgroup restriction followed by the same original completion embedding. -/
theorem originalGlobalInfiniteTwoCocycle_apply
    (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
    (g h : OriginalInfiniteDecompositionGroup K L w) :
    originalGlobalInfiniteTwoCocycle K L w c (g, h) =
      Additive.ofMul (Units.map (algebraMap L (w.Completion)).toMonoidHom
        (c (g.val, h.val)).toMul) := rfl

/-- Actual original global-to-infinite-local H2, without a choice of finite support or orbit representative. -/
def originalGlobalInfiniteH2 :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ⟶
      groupCohomology (originalInfiniteUnitRep K L w) 2 :=
  groupCohomology.map (OriginalInfiniteDecompositionGroup K L w).subtype
    (originalGlobalInfiniteUnitRepHom K L w) 2

/-- The actual localization map takes the class of the original cocycle to the class of its literal localized cocycle. -/
theorem originalGlobalInfiniteH2_cocycle
    (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L)) :
    originalGlobalInfiniteH2 K L w (groupCohomology.H2π _ c) =
      groupCohomology.H2π _ (originalGlobalInfiniteTwoCocycle K L w c) :=
  groupCohomology.H2π_comp_map_apply _ _ c

end
end Dubon2026
