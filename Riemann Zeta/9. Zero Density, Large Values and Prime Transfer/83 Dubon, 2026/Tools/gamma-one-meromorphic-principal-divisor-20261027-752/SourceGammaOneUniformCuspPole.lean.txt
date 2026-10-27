import Dubon2026.SourceFrickeModularOrbitV2
import Mathlib.GroupTheory.GroupAction.Quotient

/-! DUB-17/18 -> original all-weight arithmetic association -> actual finite
Gamma1 character realization -> Picard/H1 comparison -> modular periods ->
meromorphic field realization. Finite index makes the actual modular orbit
finite; the existing discriminant monotonicity then clears all cusp poles
with one exponent. No cusp enumeration or compact-pole theorem is assumed. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem finite_modular_orbit_of_invariant {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (F : ℍ → ℂ) (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) :
    Finite (MulAction.orbit SL(2, ℤ) F) := by
  have hle : Γ ≤ MulAction.stabilizer SL(2, ℤ) F := by
    intro γ hγ
    change γ • F = F
    funext τ
    exact hinv γ⁻¹ (Γ.inv_mem hγ) τ
  letI : (MulAction.stabilizer SL(2, ℤ) F).FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact Finite.of_equiv (SL(2, ℤ) ⧸ MulAction.stabilizer SL(2, ℤ) F)
    (MulAction.orbitEquivQuotientStabilizer SL(2, ℤ) F).symm

theorem exists_uniform_discriminant_pole_bound {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (F : ℍ → ℂ) (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hpb : ∀ γ : SL(2, ℤ), ∃ m : ℕ,
      IsBoundedAtImInfty ((F ∘ (γ • ·)) * ⇑CuspForm.discriminant ^ m)) :
    ∃ m : ℕ, ∀ γ : SL(2, ℤ),
      IsBoundedAtImInfty ((F ∘ (γ • ·)) * ⇑CuspForm.discriminant ^ m) := by
  classical
  letI := finite_modular_orbit_of_invariant F hinv
  letI := Fintype.ofFinite (MulAction.orbit SL(2, ℤ) F)
  have hb : ∀ W : MulAction.orbit SL(2, ℤ) F, ∃ m : ℕ,
      IsBoundedAtImInfty (W.val * ⇑CuspForm.discriminant ^ m) := by
    rintro ⟨W, γ, rfl⟩
    simpa only [sl_smul_def, Function.comp_def] using hpb γ⁻¹
  choose m hm using hb
  refine ⟨Finset.univ.sup m, ?_⟩
  intro γ
  let W : MulAction.orbit SL(2, ℤ) F := ⟨γ⁻¹ • F, γ⁻¹, rfl⟩
  have h := IsBoundedAtImInfty.mul_discPow_mono
    (Finset.le_sup (f := m) (Finset.mem_univ W)) (hm W)
  simpa only [W, sl_smul_def, inv_inv, Function.comp_def] using h

end
end Dubon2026.SourceFricke
