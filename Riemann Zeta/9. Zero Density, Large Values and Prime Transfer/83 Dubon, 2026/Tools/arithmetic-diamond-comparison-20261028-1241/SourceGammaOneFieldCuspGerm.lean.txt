import Dubon2026.SourceGammaOneCuspRealizationAlgebra
import Mathlib.Order.Filter.Germ.Basic

/-! DUB-17/18 -> original all-weight association -> actual Gamma1
arithmetic diamond -> original field diamond. Package the already proved
cusp realization algebra as the native punctured germ homomorphism.
Its field injectivity will identify the actual translated-ratio map.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup UpperHalfPlane Filter
open scoped MatrixGroups Topology
variable (M : ℕ) [NeZero M]

/-- The actual original Gamma1 field embedded in its translated cusp germ. -/
def fieldCuspGerm (δ : SL(2, ℤ)) :
    functionFieldOver (Gamma1 M) ℂ →+* Germ (𝓝[≠] (0 : ℂ)) ℂ := by
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  have hΓ : Gamma M ≤ Gamma1 M := by
    intro A hA
    rw [Gamma_mem] at hA
    exact (Gamma1_mem M A).mpr ⟨hA.1, hA.2.2.2, hA.2.2.1⟩
  exact
    { toFun := fun x => (cuspRealize (Gamma1 M) M δ (x : LaurentSeries ℂ) :
        Germ (𝓝[≠] (0 : ℂ)) ℂ)
      map_zero' := Germ.coe_eq.mpr (by
        simpa only [map_zero] using cuspRealize_const_eventuallyEq M hT δ 0)
      map_one' := Germ.coe_eq.mpr (by
        simpa only [map_one] using cuspRealize_const_eventuallyEq M hT δ 1)
      map_add' := fun x y => Germ.coe_eq.mpr (cuspRealize_add_eventuallyEq M hΓ hT x y δ)
      map_mul' := fun x y => Germ.coe_eq.mpr (cuspRealize_mul_eventuallyEq M hΓ hT x y δ) }

theorem fieldCuspGerm_algebraMap (δ : SL(2, ℤ)) (c : ℂ) :
    fieldCuspGerm M δ (algebraMap ℂ (functionFieldOver (Gamma1 M) ℂ) c) =
      ((fun _ : ℂ => c) : Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
  apply Germ.coe_eq.mpr
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  exact cuspRealize_const_eventuallyEq M hT δ c

end
end Dubon2026.SourceFunctionField.GammaOne
