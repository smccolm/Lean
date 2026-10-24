import Dubon2026.SourceJointChartIntegralAlgebras
import Dubon2026.SourceJointChartResidueSpans

/-! DUB-17/18 -> Kummer genus inequality -> common residue-chart constants.
The actual residue span of an original integral chart is already an algebra:
every vector lifts to one chart element. Its exact equality with the existing
chart span gives the multiplication and scalar closure required for the
idempotent argument, without introducing a second chart specification. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open IsLocalRing

variable {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
  {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

/-- The simultaneous residue image of the original integral chart. -/
def residueChartAlgebra (R : ∀ i, RegularProlongation A F (Fb i)) (g : F) :
    Subalgebra (ResidueField A) (∀ i, Fb i) where
  carrier := {h | ∃ u : F, ∃ hu : u ∈ Sg R g,
    ∀ i, (R i).residue ⟨u, hu.1 i⟩ = h i}
  zero_mem' := ⟨0, zero_mem _, fun i => by
    change (R i).residue 0 = 0
    exact map_zero _⟩
  one_mem' := ⟨1, one_mem _, fun i => by
    change (R i).residue 1 = 1
    exact map_one _⟩
  add_mem' := by
    rintro x y ⟨u, hu, hx⟩ ⟨v, hv, hy⟩
    refine ⟨u + v, add_mem hu hv, fun i => ?_⟩
    change (R i).residue (⟨u, hu.1 i⟩ + ⟨v, hv.1 i⟩) = x i + y i
    rw [map_add, hx i, hy i]
  mul_mem' := by
    rintro x y ⟨u, hu, hx⟩ ⟨v, hv, hy⟩
    refine ⟨u * v, mul_mem hu hv, fun i => ?_⟩
    change (R i).residue (⟨u, hu.1 i⟩ * ⟨v, hv.1 i⟩) = x i * y i
    rw [map_mul, hx i, hy i]
  algebraMap_mem' := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨algebraMap A F a, (Sg R g).algebraMap_mem a, fun i => ?_⟩
    exact residue_constHom (R i) a

theorem residueChartAlgebra_toSubmodule (R : ∀ i, RegularProlongation A F (Fb i)) (g : F) :
    (residueChartAlgebra R g).toSubmodule = JointChartAssembly.ST R g := by
  apply le_antisymm
  · rintro h ⟨u, hu, hres⟩
    exact Submodule.subset_span ⟨u, hu.1, (mem_originalChart_iff g u).mp hu.2, hres⟩
  · apply Submodule.span_le.mpr
    rintro h ⟨u, hu, hV, hres⟩
    exact ⟨u, ⟨hu, (mem_originalChart_iff g u).mpr hV⟩, hres⟩

theorem mem_residue_chart_iff (R : ∀ i, RegularProlongation A F (Fb i)) (g : F)
    (h : ∀ i, Fb i) : h ∈ JointChartAssembly.ST R g ↔
      ∃ u : F, ∃ hu : u ∈ Sg R g, ∀ i, (R i).residue ⟨u, hu.1 i⟩ = h i := by
  rw [← residueChartAlgebra_toSubmodule]
  rfl

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
