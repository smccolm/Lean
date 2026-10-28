import Dubon2026.SourceWeightTwoEndpointImage
import Dubon2026.SourceGammaOneAnalyticDivisorMoving

/-! DUB17/18 -> actual Gamma1 Picard-period comparison. The already proved
moving lemma gives a surjective presentation of the literal original Picard
group by finite degree-zero upper-half-plane divisors. No Picard class is
replaced by an abstract period vector or by a Gamma0 divisor class. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup SourceWeightTwoJacobi
open scoped MatrixGroups
variable (N : ℕ) [NeZero N] (hT : ModularGroup.T ∈ Gamma1 N)
local notation "F" => functionFieldOver (Gamma1 N) ℂ

/-- The literal degree-zero divisor obtained by mapping points to their analytic places. -/
def analyticDivisorHom : analyticDegree.ker →+ Divisor.degZero (K := ℂ) («F» := F) where
  toFun c := ⟨Finsupp.mapDomain (analyticPlace hT) c.val, by
    change Divisor.degree (Finsupp.mapDomain (analyticPlace hT) c.val) = 0
    rw [degree_mapDomain_analyticPlace]
    simpa only [LinearMap.mem_ker, analyticDegree_apply] using c.property⟩
  map_zero' := by
    apply Subtype.ext
    change Finsupp.mapDomain (analyticPlace hT) (0 : ℍ →₀ ℤ) = 0
    exact Finsupp.mapDomain_zero
  map_add' c d := by
    apply Subtype.ext
    exact Finsupp.mapDomain_add

/-- The original Picard class of an actual degree-zero analytic divisor. -/
def analyticPicardHom : analyticDegree.ker →+ Pic0 ℂ F :=
  Pic0.mk.comp (analyticDivisorHom N hT)

theorem analyticPicardHom_surjective : Function.Surjective (analyticPicardHom N hT) := by
  intro q
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective q
  have hΓ : Gamma N ≤ Gamma1 N := by
    intro A hA
    rw [Gamma_mem] at hA
    rw [Gamma1_mem]
    exact ⟨hA.1, hA.2.2.2, hA.2.2.1⟩
  obtain ⟨E, c, hE, hE0, hc, he⟩ :=
    exists_degree_zero_analytic_representative N hΓ hT D.val D.property
  let E0 : Divisor.degZero (K := ℂ) («F» := F) := ⟨E, hE0⟩
  let c0 : analyticDegree.ker := ⟨c, by
    simpa only [LinearMap.mem_ker, analyticDegree_apply] using hc⟩
  have hD : D = E0 + analyticDivisorHom N hT c0 := Subtype.ext he
  refine ⟨c0, ?_⟩
  rw [hD, map_add, (Pic0.mk_eq_zero_iff E0).mpr hE, zero_add]
  rfl

end
end Dubon2026.SourceFunctionField.GammaOne
