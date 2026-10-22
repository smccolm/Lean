import Dubon2026.SourceOriginalRegularCoefficientOrders
import Dubon2026.SourceOriginalCanonicalFiberSupport
import Dubon2026.SourceOriginalJDegreeSums

/-! DUB-17/18 -> regular-differential cusp forms -> cusp decay -> inverse-j
integrality. These bounds concern actual original places: each cusp width
is at most the proved degree, the 1728 multiplicity is at most two, and
regularity bounds the coefficient of D(j). They discharge the local order
conditions of the inverse-j integrality criterion.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential UpperHalfPlane
open scoped MatrixGroups

theorem original_regular_coefficient_canonical_bound (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    0 ≤ v.ord x + originalCanonicalDivisor N ℂ (D_jOver_ne_zero N ℂ) v := by
  haveI := original_place_dCoordGenerates N ℂ v
  haveI : Nontrivial Ω[modularFunctionFieldOver N ℂ⁄ℂ] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N ℂ)
  have hcoeff : v.differentialCoeff (D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ)) ≠ 0 := by
    intro he
    have h := v.differentialCoeff_smul_dCoord (D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ))
    rw [he, zero_smul] at h
    exact D_jOver_ne_zero N ℂ h.symm
  have hr := (mem_original_regularDifferentials_iff_ord_nonneg N ℂ _).mp hreg v
  rw [v.ordDifferential_smul hx hcoeff] at hr
  rwa [originalCanonicalDivisor_apply]

theorem original_j_pole_order_le_psi (N : ℕ) [NeZero N]
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) (hv : v.ord (jOver N ℂ) < 0) :
    -v.ord (jOver N ℂ) ≤ (SourceLevelProjective.dedekindPsi N : ℤ) := by
  classical
  have hs : {w : Place ℂ (modularFunctionFieldOver N ℂ) | w.ord (jOver N ℂ) < 0}.Finite :=
    (finite_original_divisor_support N ℂ (jOver N ℂ)).subset fun _ hw => ne_of_lt hw
  have hsum := sum_original_j_pole_orders_finset N ℂ hs.toFinset (fun w => hs.mem_toFinset)
  rw [← hsum]
  apply Finset.single_le_sum ?_ (hs.mem_toFinset.mpr hv)
  intro w hw
  exact neg_nonneg.mpr ((hs.mem_toFinset.mp hw).le)

theorem original_j_1728_order_le_two (N : ℕ) [NeZero N]
    (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (hv : 0 < v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728)) :
    v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728) ≤ 2 := by
  obtain ⟨τ, rfl, hj⟩ := original_finite_fiber_realization N v 1728 hv
  have hjf : JMultiplicity.jf τ = 1728 := hj
  have h4 : ModularForm.E₄ τ ≠ 0 := by
    intro h4
    norm_num [h4] at hj
  have hc : Nat.card (MulAction.stabilizer SL(2, ℤ) τ) ≤ 4 := by
    by_cases h6 : ModularForm.E₆ τ = 0
    · rw [(JMultiplicity.case_E₆_eq_zero h6).2]
    · rw [(JMultiplicity.case_generic h4 h6).2]
      norm_num
  have hm := WithTop.coe_injective (original_analytic_j_multiplicity N τ)
  rw [hjf] at hm
  have hb : ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ) ≤ 2 := by
    exact_mod_cast (show Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 ≤ 2 by omega)
  have he : (1 : ℤ) ≤ originalAnalyticRamification N τ := by
    have := originalAnalyticRamification_pos N τ
    omega
  nlinarith

end
end Dubon2026.SourceFunctionField
