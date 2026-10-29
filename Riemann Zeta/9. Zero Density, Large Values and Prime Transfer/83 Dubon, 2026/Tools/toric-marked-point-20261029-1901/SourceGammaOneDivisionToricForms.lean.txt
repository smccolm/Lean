import Dubon2026.SourceGammaOneDivisionForms

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> integral toric invariants. The repository already constructs
the exact normalized torsion form as GammaOne.divisionForm. Reuse that
object and its transformation theorem directly. This module only gives
the coefficient construction its required names and row-action identity;
it introduces no second modularity, holomorphy or cusp-bound proof. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ToricForms
noncomputable section
open UpperHalfPlane CongruenceSubgroup SourceFricke
open scoped MatrixGroups ModularForm Manifold Matrix
variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem vecMulSL_zero_first (c : ZMod N) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    vecMulSL N ![0, c] γ = ![0, c * (γ 1 1 : ZMod N)] := by
  have hz := Gamma0_mem.mp hγ
  ext i
  fin_cases i <;> simp [vecMulSL_apply, hz]

/-- Reuse the actual existing division form, with the identical normalization. -/
abbrev torsionWeightTwo (N : ℕ) [NeZero N] (c : ZMod N) (hc : c ≠ 0) :
    ModularForm (Gamma1 N) 2 := GammaOne.divisionForm N c hc

theorem torsionWeightTwo_slash (c : ZMod N) (hc : c ≠ 0) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 N) (hc' : c * (γ 1 1 : ZMod N) ≠ 0) :
    (torsionWeightTwo N c hc : ℍ → ℂ) ∣[(2 : ℤ)] γ =
      (torsionWeightTwo N (c * (γ 1 1 : ZMod N)) hc' : ℍ → ℂ) :=
  GammaOne.divisionForm_slash_gamma0 N c hc γ hγ

end
end Dubon2026.SourceFunctionField.GammaOne.ToricForms
