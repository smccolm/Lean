import Dubon2026.SourceGammaOneAnalyticHeckeDivisors
import Dubon2026.SourceGammaOnePeriodHeckeLattice

/-! DUB17/18 -> actual Gamma1 Picard/H1 Hecke comparison -> endpoint
compatibility. The literal analytic coset sum has the dual cusp Hecke
action plus one explicit basepoint term times the divisor degree.
Degree zero discharges that term; the original period quotient is used. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane CongruenceSubgroup SourceWeightTwoJacobi
open scoped MatrixGroups
variable (M d : ℕ) [NeZero M] [NeZero d]

private local instance : Fintype (Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex M d
  exact Fintype.ofFinite _

theorem analyticEndpointHom_hecke (c : ℍ →₀ ℤ) :
    analyticEndpointHom M (analyticHeckeLinear M d c) =
      periodHeckeLinear M d (analyticEndpointHom M c) +
        analyticDegree c •
          ∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
            sourceWeightTwoAlong (Gamma1 M) UpperHalfPlane.I
              (heckeCosetPoint M d UpperHalfPlane.I q) := by
  let C := ∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
    sourceWeightTwoAlong (Gamma1 M) UpperHalfPlane.I
      (heckeCosetPoint M d UpperHalfPlane.I q)
  let L := (analyticEndpointHom M).comp (analyticHeckeLinear M d)
  let R := ((periodHeckeLinear M d).restrictScalars ℤ).comp (analyticEndpointHom M) +
    analyticDegree.smulRight C
  have he : L.toAddMonoidHom = R.toAddMonoidHom := by
    apply Finsupp.addHom_ext'
    intro τ
    apply AddMonoidHom.ext_int
    change analyticEndpointHom M (analyticHeckeLinear M d (Finsupp.single τ 1)) =
      periodHeckeLinear M d (analyticEndpointHom M (Finsupp.single τ 1)) +
        analyticDegree (Finsupp.single τ 1) • C
    rw [analyticHeckeLinear_single, map_sum]
    simp only [analyticEndpointHom, analyticDegree, Finsupp.linearCombination_single,
      one_smul]
    rw [periodHeckeLinear_along]
    change (∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
      sourceWeightTwoAlong (Gamma1 M) UpperHalfPlane.I (heckeCosetPoint M d τ q)) = _ + C
    have hp (q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) :
        sourceWeightTwoAlong (Gamma1 M) UpperHalfPlane.I (heckeCosetPoint M d τ q) =
          sourceWeightTwoAlong (Gamma1 M) (heckeCosetPoint M d UpperHalfPlane.I q)
            (heckeCosetPoint M d τ q) +
          sourceWeightTwoAlong (Gamma1 M) UpperHalfPlane.I
            (heckeCosetPoint M d UpperHalfPlane.I q) := by
      rw [sourceWeightTwoAlong_eq_sub (Gamma1 M) (heckeCosetPoint M d UpperHalfPlane.I q)]
      abel
    exact (Finset.sum_congr rfl (fun q _ => hp q)).trans (Finset.sum_add_distrib)
  exact DFunLike.congr_fun he c

theorem analyticPeriodHom_hecke (c : analyticDegree.ker) :
    analyticPeriodHom M (analyticHeckeDegreeZero M d c) =
      periodQuotientHecke M d (analyticPeriodHom M c) := by
  change (sourceWeightTwoIntegralLattice (Gamma1 M)).mkQ
      (analyticEndpointHom M (analyticHeckeLinear M d c.val)) =
    periodQuotientHecke M d
      ((sourceWeightTwoIntegralLattice (Gamma1 M)).mkQ (analyticEndpointHom M c.val))
  rw [periodQuotientHecke_mk, analyticEndpointHom_hecke,
    LinearMap.mem_ker.mp c.property, zero_smul, add_zero]

end
end Dubon2026.SourceFunctionField.GammaOne
