import Dubon2026.SourceJScalarAndLatticeRelations

/-! DUB-17/18 -> the numerical modular genus -> elliptic ramification ->
the analytic j-invariant separates full modular-group orbits. Adapted
from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.
This uses actual period lattices and the proved Weierstrass equation.
-/
namespace Dubon2026.SourceFunctionField.JOrbitSeparation
noncomputable section
open UpperHalfPlane ModularForm EisensteinSeries Complex
open scoped MatrixGroups Real Topology
open PeriodPair PeriodLattice
theorem G_ofTau_eq {k : ℕ} (hk : 3 ≤ k) (τ : ℍ) :
    (ofTau τ).G k = 2 * riemannZeta k * ModularForm.E hk τ := by
  rw [PeriodPair.G, ← (ofTau τ).latticeEquivProd.symm.toEquiv.tsum_eq]
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply, ofTau_ω₁, ofTau_ω₂, mul_one]
  have hstep : ∀ p : ℤ × ℤ,
      ((↑p.1 * (τ : ℂ) + ↑p.2) ^ k)⁻¹ = eisSummand k ((finTwoArrowEquiv ℤ).symm p) τ := by
    intro p
    simp only [eisSummand, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, zpow_neg, zpow_natCast]
  simp only [hstep]
  rw [(finTwoArrowEquiv ℤ).symm.tsum_eq (f := fun v => eisSummand (k : ℤ) v τ),
    tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ,
    show E hk τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ from rfl,
    eisensteinSeriesSIF_apply, smul_eq_mul]
  ring

theorem G_scale (L : PeriodPair) (α : ℂˣ) (k : ℕ) :
    (PeriodLattice.scale L α).G k = ((α : ℂ) ^ k)⁻¹ * L.G k := by
  rw [PeriodPair.G, PeriodPair.G, ← (PeriodLattice.scale L α).latticeEquivProd.symm.toEquiv.tsum_eq,
    ← L.latticeEquivProd.symm.toEquiv.tsum_eq, ← tsum_mul_left]
  congr 1 with p
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply, scale_ω₁, scale_ω₂]
  rw [show (p.1 : ℂ) * (α * L.ω₁) + p.2 * (α * L.ω₂) = α * (p.1 * L.ω₁ + p.2 * L.ω₂) by ring,
    mul_pow, mul_inv]

theorem g₂_scale (L : PeriodPair) (α : ℂˣ) : (PeriodLattice.scale L α).g₂ = ((α : ℂ) ^ 4)⁻¹ * L.g₂ := by
  rw [PeriodPair.g₂, PeriodPair.g₂, G_scale]; ring

theorem g₃_scale (L : PeriodPair) (α : ℂˣ) : (PeriodLattice.scale L α).g₃ = ((α : ℂ) ^ 6)⁻¹ * L.g₃ := by
  rw [PeriodPair.g₃, PeriodPair.g₃, G_scale]; ring

theorem g₂_ofTau (τ : ℍ) : (ofTau τ).g₂ = (120 * riemannZeta 4) * E₄ τ := by
  rw [PeriodPair.g₂, G_ofTau_eq (by norm_num : 3 ≤ 4)]; push_cast; ring

theorem g₃_ofTau (τ : ℍ) : (ofTau τ).g₃ = (280 * riemannZeta 6) * E₆ τ := by
  rw [PeriodPair.g₃, G_ofTau_eq (by norm_num : 3 ≤ 6)]; push_cast; ring

theorem mem_scale_lattice (L : PeriodPair) (α : ℂˣ) (x : ℂ) :
    x ∈ (PeriodLattice.scale L α).lattice ↔ ∃ m n : ℤ, (α : ℂ) * (m * L.ω₁ + n * L.ω₂) = x := by
  rw [mem_lattice]
  simp only [scale_ω₁, scale_ω₂]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩



theorem E₄_cube_sub_E₆_sq_ne_zero (z : ℍ) : E₄ z ^ 3 - E₆ z ^ 2 ≠ 0 := fun h0 => by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  rw [h0, zero_div] at h
  exact ModularForm.discriminant_ne_zero z h


end
end Dubon2026.SourceFunctionField.JOrbitSeparation
