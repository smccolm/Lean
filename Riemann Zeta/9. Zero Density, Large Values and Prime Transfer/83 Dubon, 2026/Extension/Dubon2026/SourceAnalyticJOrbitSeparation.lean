import Dubon2026.SourcePeriodEisensteinInvariants
import Dubon2026.SourcePeriodLatticeInvariants

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
theorem exists_smul_eq_of_j_eq (τ τ' : ℍ)
    (h : (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ =
      (ModularForm.E₄ : ℍ → ℂ) τ' ^ 3 / ModularForm.discriminant τ') :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by

  have R1 : E₄ τ ^ 3 * E₆ τ' ^ 2 = E₄ τ' ^ 3 * E₆ τ ^ 2 := by
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq,
      div_eq_div_iff (by simpa using E₄_cube_sub_E₆_sq_ne_zero τ)
        (by simpa using E₄_cube_sub_E₆_sq_ne_zero τ')] at h
    change E₄ τ ^ 3 * ((E₄ τ' ^ 3 - E₆ τ' ^ 2) / 1728) =
      E₄ τ' ^ 3 * ((E₄ τ ^ 3 - E₆ τ ^ 2) / 1728) at h
    linear_combination -1728 * h

  obtain ⟨w, hw, hwa, hwb⟩ := exists_scalar (E₄_cube_sub_E₆_sq_ne_zero τ)
    (E₄_cube_sub_E₆_sq_ne_zero τ') R1

  set uU : ℂˣ := (Units.mk0 w hw)⁻¹ with huU
  set u : ℂ := (uU : ℂ) with huc
  have hu : u ≠ 0 := uU.ne_zero
  have hwu : w = u⁻¹ := by simp [huc, huU]
  have hΛ : (PeriodLattice.ofTau τ').lattice = (PeriodLattice.scale (PeriodLattice.ofTau τ) uU).lattice := by
    apply LatticeInvariants.lattice_eq_of_invariants
    · rw [g₂_scale, g₂_ofTau, g₂_ofTau, hwa, ← huc, hwu, inv_pow]; ring
    · rw [g₃_scale, g₃_ofTau, g₃_ofTau, hwb, ← huc, hwu, inv_pow]; ring

  obtain ⟨a, b, h1⟩ : ∃ a b : ℤ, u * (a * τ + b) = τ' := by
    have h := (PeriodLattice.ofTau τ').ω₁_mem_lattice
    rw [hΛ, mem_scale_lattice] at h
    simpa only [PeriodLattice.ofTau_ω₁, PeriodLattice.ofTau_ω₂, mul_one, huc] using h
  obtain ⟨c, d, h2⟩ : ∃ c d : ℤ, u * (c * τ + d) = 1 := by
    have h := (PeriodLattice.ofTau τ').ω₂_mem_lattice
    rw [hΛ, mem_scale_lattice] at h
    simpa only [PeriodLattice.ofTau_ω₁, PeriodLattice.ofTau_ω₂, mul_one, huc] using h
  obtain ⟨p, q, h3⟩ : ∃ p q : ℤ, p * (τ' : ℂ) + q = u * τ := by
    have h := (PeriodLattice.scale (PeriodLattice.ofTau τ) uU).ω₁_mem_lattice
    rw [← hΛ, PeriodPair.mem_lattice] at h
    simpa only [PeriodLattice.ofTau_ω₁, PeriodLattice.ofTau_ω₂, PeriodLattice.scale_ω₁, mul_one,
      huc] using h
  obtain ⟨r, s, h4⟩ : ∃ r s : ℤ, r * (τ' : ℂ) + s = u := by
    have h := (PeriodLattice.scale (PeriodLattice.ofTau τ) uU).ω₂_mem_lattice
    rw [← hΛ, PeriodPair.mem_lattice] at h
    simpa only [PeriodLattice.ofTau_ω₁, PeriodLattice.ofTau_ω₂, PeriodLattice.scale_ω₂, mul_one,
      huc] using h
  exact exists_sl2z_of_lattice_rel τ τ' hu h1 h2 h3 h4

end
end Dubon2026.SourceFunctionField.JOrbitSeparation
