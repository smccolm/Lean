import Dubon2026.SourceGammaOneFinitePeriodLattice
import Dubon2026.SourceGammaOneRealPeriodSurjectivity

/-! DUB17/18 -> original all-weight arithmetic realization -> finite
Gamma1 parabolic H1 -> dual of the original period lattice. Real-period
surjectivity makes every integer parabolic character kill the kernel of
the actual period map. Native surjective-hom descent supplies its unique
factor, without a new integral Poincare duality argument. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup
open scoped MatrixGroups
variable (M : ℕ) [NeZero M]

/-- The original group periods with codomain their actual integral lattice. -/
def latticePeriodHom :
    Additive (Gamma1 M) →+ sourceWeightTwoIntegralLattice (Gamma1 M) where
  toFun γ := ⟨dualPeriodHom M γ, sourceWeightTwoDualPeriod_mem (Gamma1 M) γ.toMul⟩
  map_zero' := Subtype.ext ((dualPeriodHom M).map_zero)
  map_add' γ δ := Subtype.ext ((dualPeriodHom M).map_add γ δ)

theorem latticePeriodHom_surjective : Function.Surjective (latticePeriodHom M) := by
  intro l
  have hl := (le_of_eq (integralLattice_eq_dualPeriodHom_range M)) l.property
  obtain ⟨γ, hγ⟩ := hl
  exact ⟨γ, Subtype.ext hγ⟩

theorem latticePeriodHom_parabolic (γ : Gamma1 M) (hγ : γ.val.val.trace ^ 2 = 4) :
    latticePeriodHom M (Additive.ofMul γ) = 0 := by
  apply Subtype.ext
  ext f
  simpa only [latticePeriodHom, dualPeriodHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    sourceWeightTwoDualPeriod_apply, Submodule.coe_zero, LinearMap.zero_apply] using
    sourceGamma1_period_eq_zero_of_trace M f γ hγ

theorem latticePeriodHom_finite_order (γ : Gamma1 M) (hγ : IsOfFinOrder γ) :
    latticePeriodHom M (Additive.ofMul γ) = 0 := by
  apply Subtype.ext
  ext f
  simpa only [latticePeriodHom, dualPeriodHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    sourceWeightTwoDualPeriod_apply, Submodule.coe_zero, LinearMap.zero_apply] using
    ((sourceWeightTwoPeriodHom (Gamma1 M) f).isOfFinAddOrder
      (isOfFinAddOrder_ofMul_iff.mpr hγ)).eq_zero'

theorem latticePeriodHom_ker_le_integer_character
    (φ : Additive (Gamma1 M) →+ ℤ)
    (hpar : ∀ γ : Gamma1 M, γ.val.val.trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0) :
    (latticePeriodHom M).ker ≤ φ.ker := by
  obtain ⟨f, hf⟩ := sourceGamma1_exists_cuspForm_of_real_parabolic_character M
    ((Int.castAddHom ℝ).comp φ) (fun γ hγ => by simp [hpar γ hγ])
  intro γ hγ
  have hval := congrArg (fun l : sourceWeightTwoIntegralLattice (Gamma1 M) => l.val f)
    (AddMonoidHom.mem_ker.mp hγ)
  have hval' : sourceWeightTwoPeriodValue (Gamma1 M) f γ.toMul = 0 := by
    simpa only [latticePeriodHom, dualPeriodHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      sourceWeightTwoDualPeriod_apply, Submodule.coe_zero, LinearMap.zero_apply] using hval
  have hzero : (φ γ : ℝ) = 0 := (hf γ.toMul).symm.trans (congrArg Complex.re hval')
  exact AddMonoidHom.mem_ker.mpr (Int.cast_eq_zero.mp hzero)

theorem exists_integer_lattice_factor
    (φ : Additive (Gamma1 M) →+ ℤ)
    (hpar : ∀ γ : Gamma1 M, γ.val.val.trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0) :
    ∃ ψ : sourceWeightTwoIntegralLattice (Gamma1 M) →+ ℤ,
      ψ.comp (latticePeriodHom M) = φ := by
  refine ⟨(latticePeriodHom M).liftOfSurjective (latticePeriodHom_surjective M)
    ⟨φ, latticePeriodHom_ker_le_integer_character M φ hpar⟩, ?_⟩
  exact AddMonoidHom.liftOfRightInverse_comp _ _ _ _

end
end Dubon2026.SourceFunctionField.GammaOne
