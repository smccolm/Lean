import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.MDifferentiable
import Mathlib.Tactic

/-! DUB-17/18 -> original all-weight association -> original Gamma1
coordinate-degree preservation -> integral Eisenstein coset separation.
These are the actual weight-four congruence lattice sums needed for that
separation. Reindex the original lattice rows to prove their exact slash
action. Mathlib's summands and SL2 transformation are reused.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.lean.
Only weight four is developed for the current dependency. -/
namespace Dubon2026.SourceFunctionField.GammaOne.IntegralEisenstein
noncomputable section
open scoped MatrixGroups CongruenceSubgroup ModularForm Topology Manifold Matrix
open UpperHalfPlane hiding I
open EisensteinSeries Filter Complex

/-- Integer lattice rows in the literal prescribed residue class. -/
def rows (N : ℕ) (a : Fin 2 → ZMod N) : Set (Fin 2 → ℤ) :=
  {v | ((↑) : ℤ → ZMod N) ∘ v = a}

/-- The original congruence lattice Eisenstein sum of weight four. -/
def series (N : ℕ) (a : Fin 2 → ZMod N) : ℍ → ℂ :=
  fun z => ∑' v : rows N a, eisSummand 4 v z

private theorem row_mul_mem {N : ℕ} {a : Fin 2 → ZMod N} {v : Fin 2 → ℤ}
    (hv : v ∈ rows N a) (γ : SL(2, ℤ)) :
    v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ) ∈ rows N (a ᵥ* γ) := by
  simp only [rows, Set.mem_setOf_eq] at hv ⊢
  have h := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at h
  simp_rw [Function.comp_def, h, ← hv]
  rfl

private def rowEquiv {N : ℕ} (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    rows N a ≃ rows N (a ᵥ* γ) where
  toFun v := ⟨v.1 ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ), row_mul_mem v.2 γ⟩
  invFun v := ⟨v.1 ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), by
    have h := row_mul_mem v.2 γ⁻¹
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul] at h
    simpa only [map_inv, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.vecMul_one] using h⟩
  left_inv v := by simp_rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  right_inv v := by simp_rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

theorem series_slash (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    series N a ∣[(4 : ℤ)] γ = series N (a ᵥ* γ) := by
  ext1 z
  simp_rw [ModularForm.SL_slash_apply, zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z), series,
    eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ (4 : ℤ))]
  congr 1
  exact (rowEquiv a γ).tsum_eq (fun v => eisSummand 4 v z)

/-- The same lattice sum with its principal-congruence invariance proved. -/
def slashInvariant (N : ℕ) (a : Fin 2 → ZMod N) : SlashInvariantForm Γ(N) 4 where
  toFun := series N a
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ Γ(N)), rfl⟩ := hA
    simp [Matrix.SpecialLinearGroup.mapGL, ← ModularForm.SL_slash, series_slash,
      CongruenceSubgroup.Gamma_mem'.mp hA]

end
end Dubon2026.SourceFunctionField.GammaOne.IntegralEisenstein
