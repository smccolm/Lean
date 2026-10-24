import Dubon2026.SourceEllipticIntegralChangeCoordinates
import Dubon2026.SourceEllipticIntegralGoodModelChange

/-! DUB-17/18 -> wild good reduction -> integral inertia cocycles.
The existing discriminant argument proves unit scaling in every residue
characteristic. The newly adapted monic coordinate identities then prove
all translation parameters integral, removing the unit-two/three premises. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve
noncomputable section
variable {M : Type*} [Field M] (A : ValuationSubring M)

theorem exists_integral_change_of_good_models_all_characteristics
    (W W' : WeierstrassCurve A) (g : VariableChange M)
    (hg : g • W'.map A.subtype = W.map A.subtype)
    (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) :
    ∃ g₀ : VariableChange A, g₀.map A.subtype = g := by
  obtain ⟨gu, r, s, t⟩ := g
  let u : M := gu
  have hu0 : u ≠ 0 := gu.ne_zero
  have huinv : ((gu⁻¹ : Mˣ) : M) = u⁻¹ := Units.val_inv_eq_inv_val gu
  have hΔ : ((W.Δ : A) : M) = u⁻¹ ^ 12 * ((W'.Δ : A) : M) := by
    have h := congrArg WeierstrassCurve.Δ hg
    rw [variableChange_Δ, map_Δ, map_Δ] at h
    dsimp only at h
    rw [huinv] at h
    exact h.symm
  have hv : A.valuation u⁻¹ = 1 := by
    have hd := congrArg A.valuation hΔ
    rw [(A.valuation_eq_one_iff W.Δ).mp hW, Valuation.map_mul, Valuation.map_pow,
      (A.valuation_eq_one_iff W'.Δ).mp hW', mul_one] at hd
    exact (pow_eq_one_iff_of_nonneg zero_le' (by norm_num : (12 : ℕ) ≠ 0)).mp hd.symm
  have hu : A.valuation u = 1 := by
    rw [map_inv₀, inv_eq_one] at hv
    exact hv
  have huA : u ∈ A := (A.valuation_le_one_iff _).mp hu.le
  have huiA : u⁻¹ ∈ A := (A.valuation_le_one_iff _).mp hv.le
  let u₀ : Aˣ := ⟨⟨u, huA⟩, ⟨u⁻¹, huiA⟩, Subtype.ext (mul_inv_cancel₀ hu0),
    Subtype.ext (inv_mul_cancel₀ hu0)⟩
  have hr : r ∈ A := integral_change_r_mem A W W' ⟨gu, r, s, t⟩ hg ⟨u, huA⟩ rfl
  have hs : s ∈ A := integral_change_s_mem A W W' ⟨gu, r, s, t⟩ hg
    ⟨u, huA⟩ ⟨r, hr⟩ rfl rfl
  have ht : t ∈ A := integral_change_t_mem A W W' ⟨gu, r, s, t⟩ hg
    ⟨u, huA⟩ ⟨r, hr⟩ rfl rfl
  refine ⟨⟨u₀, ⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩, ?_⟩
  ext <;> rfl

end
end Dubon2026.SourceEllipticReduction
