import Dubon2026.SourceSiegelFiniteProductExpansion
import Dubon2026.SourceSiegelProductTransformation
import Dubon2026.SourceSiegelHolomorphic
import Mathlib.NumberTheory.ModularForms.Discriminant

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary -> discriminant-adjusted Siegel
modular form and its exact cusp bounds. Consume actual literal products,
the proved finite-product cusp limit and native discriminant decay. The
nonnegative shifted-order hypothesis is explicit and will be discharged
when selecting the discriminant power; no auxiliary existence is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Form
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold
variable (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ)

/-- The literal finite Siegel product of the exponent family. -/
noncomputable def uFun (τ : ℍ) : ℂ :=
  ∏ r : ZMod N, ∏ s : ZMod N, siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)

/-- The exact integer Bernoulli order on a residue column. -/
def Ord (x y : ZMod N) : ℤ :=
  ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
    (6 * ((r * x + s * y).val : ℤ) ^ 2 - 6 * (N : ℤ) * ((r * x + s * y).val : ℤ) + (N : ℤ) ^ 2)

/-- The actual Siegel product times the chosen discriminant power. -/
noncomputable def thetaFun (t : ℕ) (τ : ℍ) : ℂ := uFun N m τ * ModularForm.discriminant τ ^ t

theorem discr_slash (β : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (β • τ) * UpperHalfPlane.denom β τ ^ (-(12 : ℤ)) = ModularForm.discriminant τ := by
  have h := congrFun (SlashInvariantForm.slash_action_generators_SL2Z ModularForm.discriminant_S_invariant
    ModularForm.discriminant_T_invariant β) τ
  rwa [ModularForm.SL_slash_apply] at h

theorem thetaFun_slash_apply (t : ℕ) (β : SL(2, ℤ)) (τ : ℍ) :
    ((thetaFun N m t) ∣[12 * (t : ℤ)] (β : GL (Fin 2) ℝ)) τ = uFun N m (β • τ) * ModularForm.discriminant τ ^ t := by
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, thetaFun, ← discr_slash β τ, mul_pow, mul_assoc]
  congr 2
  rw [← zpow_natCast (UpperHalfPlane.denom β τ ^ (-(12 : ℤ))) t, ← zpow_mul]
  congr 1


end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Form
