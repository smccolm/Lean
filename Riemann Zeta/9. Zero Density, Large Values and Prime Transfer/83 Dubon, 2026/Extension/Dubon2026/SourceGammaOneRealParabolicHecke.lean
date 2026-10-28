import Dubon2026.SourceGammaOneRealParabolicH1

/-! DUB17/18 -> original all-weight arithmetic realization -> full/parabolic
Gamma1 H1 comparison. The actual native Hecke operator preserves the
literal parabolic H1 submodule because its every class is a real cusp
period. Restrict that existing operator and prove compatibility with the
actual bijective real-period map. No parabolic-stability hypothesis or
transport-defined Hecke operator is introduced. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup groupCohomology
open scoped MatrixGroups
variable (M : ℕ) [NeZero M]

theorem realParabolicH1_hecke_mem (d : ℕ) [NeZero d]
    {x : H1 (Rep.trivial ℝ (Gamma1 M) ℝ)} (hx : x ∈ realParabolicH1 M) :
    sourceGammaOneConstantHeckeH1 ℝ ℝ M d LinearMap.id x ∈ realParabolicH1 M := by
  rw [← realPeriodH1_range] at hx
  obtain ⟨f, rfl⟩ := hx
  rw [← realPeriodH1_cuspHeckeTrace]
  exact realPeriodH1_mem_parabolic M _

/-- The restriction of the actual native Hecke correspondence to parabolic real H1. -/
def realParabolicHecke (d : ℕ) [NeZero d] : Module.End ℝ (realParabolicH1 M) where
  toFun x := ⟨sourceGammaOneConstantHeckeH1 ℝ ℝ M d LinearMap.id x.val,
    realParabolicH1_hecke_mem M d x.property⟩
  map_add' x y := Subtype.ext
    ((sourceGammaOneConstantHeckeH1 ℝ ℝ M d LinearMap.id).map_add x.val y.val)
  map_smul' c x := Subtype.ext
    ((sourceGammaOneConstantHeckeH1 ℝ ℝ M d LinearMap.id).map_smul c x.val)

/-- The actual real cusp periods identify the cusp-form space with native parabolic real H1. -/
def realParabolicPeriodEquiv :
    CuspForm ((Gamma1 M).map (mapGL ℝ)) 2 ≃ₗ[ℝ] realParabolicH1 M :=
  LinearEquiv.ofBijective
    ((realPeriodH1 M).codRestrict (realParabolicH1 M) (realPeriodH1_mem_parabolic M))
    ⟨fun _ _ h => realPeriodH1_injective M (congrArg Subtype.val h), by
      intro x
      have hx : x.val ∈ LinearMap.range (realPeriodH1 M) :=
        (le_of_eq (realPeriodH1_range M).symm) x.property
      obtain ⟨f, hf⟩ := hx
      exact ⟨f, Subtype.ext hf⟩⟩

theorem realParabolicPeriodEquiv_cuspHeckeTrace (d : ℕ) [NeZero d]
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) :
    realParabolicPeriodEquiv M (cuspHeckeTrace M d f) =
      realParabolicHecke M d (realParabolicPeriodEquiv M f) := by
  apply Subtype.ext
  exact realPeriodH1_cuspHeckeTrace M d f

end
end Dubon2026.SourceFunctionField.GammaOne
