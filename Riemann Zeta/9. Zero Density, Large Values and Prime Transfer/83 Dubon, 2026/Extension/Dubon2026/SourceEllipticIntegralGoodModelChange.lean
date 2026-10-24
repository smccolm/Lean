import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

/-! Integral coordinate changes between actual good models when 2 and 3
are units. The required Dubon exceptional-fiber application has residue
characteristic at least five. The discriminant gives a unit scaling factor;
the first three coefficient equations then give integral translation terms.
This replaces the source's longer argument covering residue characteristics
two and three, while retaining the exact coordinate-change conclusion needed
for inertia-equivariant torsion reduction in DUB-17/18.
Source comparison: anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve
noncomputable section
variable {M : Type*} [Field M] (A : ValuationSubring M)

theorem inverse_mem_of_unit (a : A) (ha : IsUnit a) : (a : M)⁻¹ ∈ A := by
  apply (A.valuation_le_one_iff _).mp
  rw [map_inv₀, (A.valuation_eq_one_iff a).mp ha, inv_one]

theorem exists_integral_change_of_good_models (h2 : IsUnit (2 : A)) (h3 : IsUnit (3 : A))
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
  have h2M : (2 : M) ≠ 0 := (h2.map A.subtype).ne_zero
  have h3M : (3 : M) ≠ 0 := (h3.map A.subtype).ne_zero
  have h2i : (2 : M)⁻¹ ∈ A := inverse_mem_of_unit A 2 h2
  have h3i : (3 : M)⁻¹ ∈ A := inverse_mem_of_unit A 3 h3
  have hsrel : s = (u * (W.a₁ : M) - (W'.a₁ : M)) * (2 : M)⁻¹ := by
    have h := congrArg WeierstrassCurve.a₁ hg
    rw [variableChange_a₁] at h
    dsimp only at h
    rw [huinv] at h
    change u⁻¹ * ((W'.a₁ : M) + 2 * s) = (W.a₁ : M) at h
    field_simp at h ⊢
    linear_combination h
  have hs : s ∈ A := by
    rw [hsrel]
    exact mul_mem (sub_mem (mul_mem huA W.a₁.2) W'.a₁.2) h2i
  have hrrel : r = (u ^ 2 * (W.a₂ : M) - (W'.a₂ : M) + s * (W'.a₁ : M) + s ^ 2) *
      (3 : M)⁻¹ := by
    have h := congrArg WeierstrassCurve.a₂ hg
    rw [variableChange_a₂] at h
    dsimp only at h
    rw [huinv] at h
    change u⁻¹ ^ 2 * ((W'.a₂ : M) - s * (W'.a₁ : M) + 3 * r - s ^ 2) = (W.a₂ : M) at h
    field_simp at h ⊢
    linear_combination h
  have hr : r ∈ A := by
    rw [hrrel]
    exact mul_mem (add_mem (add_mem (sub_mem (mul_mem (pow_mem huA 2) W.a₂.2) W'.a₂.2)
      (mul_mem hs W'.a₁.2)) (pow_mem hs 2)) h3i
  have htrel : t = (u ^ 3 * (W.a₃ : M) - (W'.a₃ : M) - r * (W'.a₁ : M)) *
      (2 : M)⁻¹ := by
    have h := congrArg WeierstrassCurve.a₃ hg
    rw [variableChange_a₃] at h
    dsimp only at h
    rw [huinv] at h
    change u⁻¹ ^ 3 * ((W'.a₃ : M) + r * (W'.a₁ : M) + 2 * t) = (W.a₃ : M) at h
    field_simp at h ⊢
    linear_combination h
  have ht : t ∈ A := by
    rw [htrel]
    exact mul_mem (sub_mem (sub_mem (mul_mem (pow_mem huA 3) W.a₃.2) W'.a₃.2)
      (mul_mem hr W'.a₁.2)) h2i
  refine ⟨⟨u₀, ⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩, ?_⟩
  ext <;> rfl

end
end Dubon2026.SourceEllipticReduction
