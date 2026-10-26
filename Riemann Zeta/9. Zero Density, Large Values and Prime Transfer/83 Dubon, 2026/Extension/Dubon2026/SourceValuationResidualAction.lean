import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.Tactic

/-! DUB-17/18 -> prescribed residual association -> compare the original
norm-local inertia and Frobenius with the exact valuation-subring source
conditions. Native residue surjectivity reduces both actions to explicit
congruences in the actual maximal ideal; pullback preserves that ideal. -/
namespace Dubon2026
noncomputable section
open scoped Pointwise
variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L]

theorem valuation_decomposition_of_mem_iff (A : ValuationSubring L)
    (σ : L ≃ₐ[K] L) (h : ∀ x : L, σ x ∈ A ↔ x ∈ A) :
    σ ∈ A.decompositionSubgroup K := by
  apply MulAction.mem_stabilizer_iff.mpr
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact (h (σ.symm x)).symm.trans (by rw [σ.apply_symm_apply])

theorem valuation_residue_power_iff (A : ValuationSubring L)
    (σ : L ≃ₐ[K] L) (hd : σ ∈ A.decompositionSubgroup K) (q : ℕ) :
    (∀ z : IsLocalRing.ResidueField A,
      (⟨σ, hd⟩ : A.decompositionSubgroup K) • z = z ^ q) ↔
    ∀ x : A, σ (x : L) - (x : L) ^ q ∈ A.nonunits := by
  let d : A.decompositionSubgroup K := ⟨σ, hd⟩
  constructor
  · intro h x
    change ((d • x - x ^ q : A) : L) ∈ A.nonunits
    rw [ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, map_pow, sub_eq_zero, IsLocalRing.ResidueField.residue_smul]
    exact h (IsLocalRing.residue A x)
  · intro h z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    have hx := h x
    change ((d • x - x ^ q : A) : L) ∈ A.nonunits at hx
    rw [ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, map_pow, sub_eq_zero, IsLocalRing.ResidueField.residue_smul] at hx
    exact hx

omit [Algebra K L] in
theorem valuation_comap_nonunits_iff (A : ValuationSubring M) (e : L →+* M) (x : L) :
    x ∈ (A.comap e).nonunits ↔ e x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    map_eq_zero, ← map_inv₀]
  rfl

end
end Dubon2026
