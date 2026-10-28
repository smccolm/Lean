import Dubon2026.SourceGammaOneHeckePrimitiveDerivative
import Dubon2026.SourceGammaOnePicardPeriodKernel

/-! DUB17/18 -> actual Gamma1 Picard/H1 Hecke comparison -> finite
analytic divisors. Sum the literal inverse-dilation coset images of a
finite integer divisor. Native mapDomain and degree give an actual
endomorphism of degree-zero analytic divisors. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane CongruenceSubgroup SourceWeightTwoJacobi
open scoped MatrixGroups
variable (M d : ℕ) [NeZero d]

private local instance : Fintype (Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex M d
  exact Fintype.ofFinite _

/-- The actual sum of inverse-dilation coset images of a finite analytic divisor. -/
def analyticHeckeLinear : Module.End ℤ (ℍ →₀ ℤ) :=
  ∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
    Finsupp.lmapDomain ℤ ℤ (fun τ => heckeCosetPoint M d τ q)

theorem analyticHeckeLinear_apply (c : ℍ →₀ ℤ) :
    analyticHeckeLinear M d c =
      ∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
        Finsupp.mapDomain (fun τ => heckeCosetPoint M d τ q) c := by
  simp only [analyticHeckeLinear, LinearMap.sum_apply, Finsupp.lmapDomain_apply]

theorem analyticHeckeLinear_single (τ : ℍ) (n : ℤ) :
    analyticHeckeLinear M d (Finsupp.single τ n) =
      ∑ q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d,
        Finsupp.single (heckeCosetPoint M d τ q) n := by
  simp only [analyticHeckeLinear_apply, Finsupp.mapDomain_single]

theorem analyticDegree_mapDomain (f : ℍ → ℍ) (c : ℍ →₀ ℤ) :
    analyticDegree (Finsupp.mapDomain f c) = analyticDegree c := by
  simp only [analyticDegree, Finsupp.linearCombination_mapDomain, Function.comp_def]

theorem analyticDegree_hecke (c : ℍ →₀ ℤ) :
    analyticDegree (analyticHeckeLinear M d c) =
      (Fintype.card (Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) : ℤ) * analyticDegree c := by
  rw [analyticHeckeLinear_apply, map_sum]
  simp only [analyticDegree_mapDomain, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The actual coset Hecke endomorphism on degree-zero finite analytic divisors. -/
def analyticHeckeDegreeZero : Module.End ℤ analyticDegree.ker where
  toFun c := ⟨analyticHeckeLinear M d c.val, by
    change analyticDegree (analyticHeckeLinear M d c.val) = 0
    rw [analyticDegree_hecke, (LinearMap.mem_ker.mp c.property), mul_zero]⟩
  map_add' c e := Subtype.ext ((analyticHeckeLinear M d).map_add c.val e.val)
  map_smul' n c := Subtype.ext ((analyticHeckeLinear M d).map_smul n c.val)

end
end Dubon2026.SourceFunctionField.GammaOne
