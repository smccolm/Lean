import Dubon2026.SourceFiniteLinearKernelSymmetric
import Dubon2026.ResidualSubfieldCentralScalar

/-! DUB-17/18 -> automorphy -> original auxiliary-prime detection -> a central
scalar with a prescribed squared character value. Native subfield perfection
and literal scalar descent avoid a separate finite-image H1 vanishing proof
for this detection step. All matrices below return to the original field. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix
variable (p : ℕ) [Fact p.Prime]

/-- The actual finite linear subfield bounds produce an original scalar
matrix with the square of any original abelian character value. -/
theorem finite_linear_bounds_original_scalar_character_square
    {F Γ A : Type} [Field F] [Group Γ] [CommGroup A]
    (j : F →+* K p) (ρ : Γ →* GL (Fin 2) F) (χ : Γ →* A)
    (hp3 : 3 < p) (h : HasFiniteLinearSubfieldBounds p j ρ) (g : Γ) :
    ∃ σ : Γ, ∃ u : Fˣ, χ σ = χ g ^ 2 ∧
      ρ σ = GeneralLinearGroup.scalar (Fin 2) u := by
  obtain ⟨m, _, E, _, jE, θ, B, _, _, hlo, hhi⟩ := h
  letI : NeZero (2 : GaloisField p m) := ⟨fun hzero => by
    have hle := Nat.le_of_dvd (by decide : 0 < 2)
      ((CharP.cast_eq_zero_iff (GaloisField p m) p 2).mp hzero)
    omega⟩
  letI : NeZero (3 : GaloisField p m) := ⟨fun hzero => by
    have hle := Nat.le_of_dvd (by decide : 0 < 3)
      ((CharP.cast_eq_zero_iff (GaloisField p m) p 3).mp hzero)
    omega⟩
  let ρE := (MulEquiv.toMonoidHom (MulAut.conj B)).comp
    ((GeneralLinearGroup.map jE).comp ρ)
  obtain ⟨uE, a, ha⟩ := hhi (ρE g)
    (Subgroup.mem_map.mpr ⟨((GeneralLinearGroup.map jE).comp ρ) g, ⟨g, rfl⟩, rfl⟩)
  obtain ⟨σ, v, hχ, hσ⟩ := residualSubfieldGL2_exists_scalar_character_square θ ρE χ
    (by simpa only [MonoidHom.map_range] using hlo) g uE a ha
  have hmap : GeneralLinearGroup.map jE (ρ σ) = GeneralLinearGroup.scalar (Fin 2) v := by
    apply (MulAut.conj B).injective
    change B * GeneralLinearGroup.map jE (ρ σ) * B⁻¹ =
      B * GeneralLinearGroup.scalar (Fin 2) v * B⁻¹
    change B * GeneralLinearGroup.map jE (ρ σ) * B⁻¹ =
      GeneralLinearGroup.scalar (Fin 2) v at hσ
    rw [hσ, (generalLinear_scalar_commute v B).eq.symm, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨u, hu⟩ := scalar_factor_descends jE (RingHom.id F) (ρ σ)
    (1 : GL (Fin 2) F) v (by simpa only [map_one, mul_one] using hmap)
  exact ⟨σ, u, hχ, by simpa only [map_one, mul_one] using hu⟩

end
end Dubon2026.SourceDickson
