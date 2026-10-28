import Dubon2026.SourceGammaOneDiamondAnalyticDivisors
import Dubon2026.SourceGammaOneDiamondPeriodTate

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond/Picard comparison. The proved primitive identity gives the exact
endpoint diamond, including the basepoint correction. Degree zero removes
that correction and proves compatibility with the original period quotient.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup UpperHalfPlane SourceWeightTwoJacobi
open scoped MatrixGroups
variable (M : ℕ) [NeZero M] (g : Gamma0 M)

theorem analyticEndpointHom_diamond (c : ℍ →₀ ℤ) :
    analyticEndpointHom M (analyticDiamondLinear M g c) =
      periodDiamondLinear M g (analyticEndpointHom M c) +
        analyticDegree c • sourceWeightTwoAlong (Gamma1 M) UpperHalfPlane.I
          (g.val • UpperHalfPlane.I) := by
  let C := sourceWeightTwoAlong (Gamma1 M) UpperHalfPlane.I (g.val • UpperHalfPlane.I)
  let L := (analyticEndpointHom M).comp (analyticDiamondLinear M g)
  let R := ((periodDiamondLinear M g).restrictScalars ℤ).comp (analyticEndpointHom M) +
    analyticDegree.smulRight C
  have he : L.toAddMonoidHom = R.toAddMonoidHom := by
    apply Finsupp.addHom_ext'
    intro τ
    apply AddMonoidHom.ext_int
    change analyticEndpointHom M (Finsupp.mapDomain (fun z => g.val • z) (Finsupp.single τ 1)) =
      periodDiamondLinear M g (analyticEndpointHom M (Finsupp.single τ 1)) +
        analyticDegree (Finsupp.single τ 1) • C
    rw [Finsupp.mapDomain_single]
    simp only [analyticEndpointHom, analyticDegree, Finsupp.linearCombination_single, one_smul]
    rw [periodDiamondLinear_along]
    change sourceWeightTwoAlong (Gamma1 M) UpperHalfPlane.I (g.val • τ) =
      sourceWeightTwoAlong (Gamma1 M) (g.val • UpperHalfPlane.I) (g.val • τ) +
        sourceWeightTwoAlong (Gamma1 M) UpperHalfPlane.I (g.val • UpperHalfPlane.I)
    rw [sourceWeightTwoAlong_eq_sub (Gamma1 M) (g.val • UpperHalfPlane.I)]
    abel
  exact DFunLike.congr_fun he c

theorem periodQuotientDiamond_mk (v : Module.Dual ℂ (CuspForm (Gamma1 M) 2)) :
    periodQuotientDiamond M g ((sourceWeightTwoIntegralLattice (Gamma1 M)).mkQ v) =
      (sourceWeightTwoIntegralLattice (Gamma1 M)).mkQ (periodDiamondLinear M g v) := rfl

theorem analyticPeriodHom_diamond (c : analyticDegree.ker) :
    analyticPeriodHom M (analyticDiamondDegreeZero M g c) =
      periodQuotientDiamond M g (analyticPeriodHom M c) := by
  change (sourceWeightTwoIntegralLattice (Gamma1 M)).mkQ
      (analyticEndpointHom M (analyticDiamondLinear M g c.val)) =
    periodQuotientDiamond M g
      ((sourceWeightTwoIntegralLattice (Gamma1 M)).mkQ (analyticEndpointHom M c.val))
  rw [periodQuotientDiamond_mk, analyticEndpointHom_diamond,
    LinearMap.mem_ker.mp c.property, zero_smul, add_zero]

end
end Dubon2026.SourceFunctionField.GammaOne
