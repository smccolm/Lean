import Dubon2026.SourceHolomorphicDiscriminantLift
import Dubon2026.SourceOriginalQuotientIntegral

/-! DUB-17/18 -> numerical genus and regular-differential realization
-> finite analytic-place exhaustion. Every original function bounded
at all upper-half-plane points becomes the expansion of an actual
Gamma0 modular form after multiplication by a discriminant power.
The proved norm-polynomial consumer therefore gives integrality over
the literal original C[j]. Boundedness supplies holomorphic extension,
and the finite slash orbit supplies the uniform exponent; neither is
left as an additional hypothesis in the final integrality theorem.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology

theorem exists_original_discriminant_power (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ)
    (hb : ∀ τ : ℍ, IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun z : ℍ => ‖realize N (x : LaurentSeries ℂ) z‖)) :
    ∃ (m : ℕ) (G : ModularForm (CongruenceSubgroup.Gamma0 N) (12 * (m : ℤ))),
      (x : LaurentSeries ℂ) * (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) ^ m =
        (qExpansion 1 (G : ℍ → ℂ) : LaurentSeries ℂ) := by
  obtain ⟨k, g, h, F, hh, hx, hF, hFg⟩ := original_holomorphic_quotient_of_bounded N x hb
  obtain ⟨m, hm⟩ := QuotientCuspGrowth.exists_forall_cuspOrder_le N h
  let G := QuotientCuspGrowth.liftForm N g h hh F hF hFg m hm
  refine ⟨m, ModularForm.mcast (mul_comm (m : ℤ) 12) G, ?_⟩
  change (x : LaurentSeries ℂ) *
    (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) ^ m =
      (qExpansion 1 (G : ℍ → ℂ) : LaurentSeries ℂ)
  apply mul_right_cancel₀ (ModularRatios.qL_ne_zero h hh)
  have hq := QuotientCuspGrowth.qL_liftForm_mul N g h hh F hF hFg m hm
  change (qExpansion 1 (G : ℍ → ℂ) : LaurentSeries ℂ) * ModularRatios.qL h =
    ModularRatios.qL g * (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) ^ m at hq
  rw [hq, ← hx]
  ring

theorem isIntegral_original_of_bounded (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ)
    (hb : ∀ τ : ℍ, IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun z : ℍ => ‖realize N (x : LaurentSeries ℂ) z‖)) :
    IsIntegral (Algebra.adjoin ℂ {jOver N ℂ}) x := by
  obtain ⟨m, G, hx⟩ := exists_original_discriminant_power N x hb
  exact isIntegral_original_of_discriminant_power N x m G hx

theorem isIntegral_original_of_mem_all_analytic_places (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ)
    (hx : ∀ τ : ℍ, x ∈ (originalAnalyticPlace N τ).toValuationSubring) :
    IsIntegral (Algebra.adjoin ℂ {jOver N ℂ}) x :=
  isIntegral_original_of_bounded N x fun τ => (originalAnalyticPlace_mem_iff_bounded N τ x).mp (hx τ)

end
end Dubon2026.SourceFunctionField
