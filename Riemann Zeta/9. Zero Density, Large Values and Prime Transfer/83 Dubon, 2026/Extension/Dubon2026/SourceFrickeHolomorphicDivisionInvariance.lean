import Dubon2026.SourceFrickePrincipalInvariance
import Dubon2026.SourceFrickeTwistPowers

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> elliptic divisibility transport. A holomorphic quotient of two actual
span functions inherits principal-level invariance by analytic cancellation.
Together with literal meromorphic cusp germs, this will derive span
membership without a separate Eisenstein growth or coordinate-invariance
argument for each elliptic-point quotient. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold

theorem principalInvariant_holomorphic_quotient {N : ℕ} [NeZero N]
    {F G W : ℍ → ℂ} (hF : F ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (hG : G ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (hG0 : G ≠ 0) (hW : MDiff W) (hrel : W * G = F) :
    ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, W (γ • τ) = W τ := by
  intro γ hγ τ
  have hγ' := (CongruenceSubgroup.Gamma N).inv_mem hγ
  have ht := congrArg (fun g : ℍ → ℂ => γ⁻¹ • g) hrel
  dsimp only at ht
  rw [smul_mul', smul_eq_self_frickeSpan hG hγ', smul_eq_self_frickeSpan hF hγ'] at ht
  have hm : (γ⁻¹ • W - W) * G = 0 := by
    rw [sub_mul, ht, hrel, sub_self]
  have hz := ((UpperHalfPlane.mul_eq_zero_iff ((mdifferentiable_slFn hW γ⁻¹).sub hW)
    (frickeSpan_holomorphic hG)).mp hm).resolve_right hG0
  have he := congrFun (sub_eq_zero.mp hz) τ
  simpa only [sl_smul_apply, inv_inv] using he

end
end Dubon2026.SourceFricke