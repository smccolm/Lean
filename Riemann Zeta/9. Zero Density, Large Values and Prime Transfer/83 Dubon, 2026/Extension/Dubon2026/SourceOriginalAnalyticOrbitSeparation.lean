import Dubon2026.SourceOriginalOrbitFiberBijection

/-! DUB-17/18 -> numerical modular genus and regular-differential
realization -> the exact Gamma0 orbit relation on actual original places.
The positive-degree orbit/fiber bijection supplies injectivity; previously
proved analytic-place invariance supplies the converse. No abstract
place dictionary or separate point-separating family is assumed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane FiberOrbits
open scoped MatrixGroups

theorem originalAnalyticPlace_eq_iff_gamma0_orbit (N : ℕ) [NeZero N] (τ τ' : ℍ) :
    originalAnalyticPlace N τ = originalAnalyticPlace N τ' ↔
      ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ = τ' := by
  constructor
  · intro hP
    obtain ⟨g, hg⟩ := originalAnalyticPlace_eq_implies_full_orbit N τ τ' hP
    have hf : orbitToFiber N τ (Quotient.mk _ ((g⁻¹ : SL(2, ℤ)) : X N)) =
        orbitToFiber N τ (Quotient.mk _ ((1 : SL(2, ℤ)) : X N)) := by
      apply Subtype.ext
      change originalAnalyticPlace N ((g⁻¹)⁻¹ • τ) = originalAnalyticPlace N (1⁻¹ • τ)
      simpa only [inv_inv, inv_one, one_smul, hg] using hP.symm
    have hq := (orbitToFiber_bijective N τ).injective hf
    have hr := Quotient.exact hq
    change ((g⁻¹ : SL(2, ℤ)) : X N) ∈
      MulAction.orbit (MulAction.stabilizer SL(2, ℤ) τ) ((1 : SL(2, ℤ)) : X N) at hr
    obtain ⟨k, hk⟩ := hr
    have hc : ((g⁻¹ : SL(2, ℤ)) : X N) = ((k : SL(2, ℤ)) : X N) := by
      have hk' : (k : SL(2, ℤ)) • ((1 : SL(2, ℤ)) : X N) = ((g⁻¹ : SL(2, ℤ)) : X N) := hk
      simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using hk'.symm
    have hm : g * (k : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
      simpa only [inv_inv] using QuotientGroup.eq.mp hc
    refine ⟨⟨g * (k : SL(2, ℤ)), hm⟩, ?_⟩
    have hfix : (k : SL(2, ℤ)) • τ = τ := k.2
    change (g * (k : SL(2, ℤ))) • τ = τ'
    rw [mul_smul, hfix, hg]
  · rintro ⟨γ, rfl⟩
    exact (originalAnalyticPlace_smul N γ τ).symm

end
end Dubon2026.SourceFunctionField
