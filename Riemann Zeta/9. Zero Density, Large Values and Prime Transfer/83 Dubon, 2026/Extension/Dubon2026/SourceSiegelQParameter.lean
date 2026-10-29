import Dubon2026.SourceSiegelFunction
import Dubon2026.SourceRealizedPowerSeries
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> integral Siegel expansion.
These identities connect the literal Siegel factors to the source q
parameter and residue-selected polynomial products. Native q-parameter
norm control is reused; no unrelated parameter or limiting theory is
introduced. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion
noncomputable section
open Complex Filter Topology
open scoped Real

/-- The actual source level-N exponential parameter. -/
def qN (N : ℕ) (τ : UpperHalfPlane) : ℂ := cexp (2 * π * I * (τ : ℂ) / (N : ℂ))

theorem qN_eq_qParam (N : ℕ) (τ : UpperHalfPlane) :
    qN N τ = Function.Periodic.qParam (N : ℝ) (τ : ℂ) := by
  unfold qN Function.Periodic.qParam; push_cast; ring_nf

theorem qN_ne_zero (N : ℕ) (τ : UpperHalfPlane) : qN N τ ≠ 0 := Complex.exp_ne_zero _

theorem norm_qN_lt_one (N : ℕ) (hN : 0 < N) (τ : UpperHalfPlane) : ‖qN N τ‖ < 1 := by
  rw [qN_eq_qParam]
  exact Dubon2026.SourceFunctionField.Realized.norm_qParam_lt_one_of_pos
    (by exact_mod_cast hN) τ

theorem q_eq (N : ℕ) (hN : 0 < N) (τ : UpperHalfPlane) :
    cexp (2 * π * I * (τ : ℂ)) = qN N τ ^ N := by
  rw [qN, ← Complex.exp_nat_mul]; congr 1
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem qa_eq (N : ℕ) (hN : 0 < N) (r : ℕ) (s : ℤ) (τ : UpperHalfPlane) :
    cexp (2 * π * I * ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (N : ℂ)) =
      cexp (2 * π * I * (s : ℂ) / (N : ℂ)) * qN N τ ^ r := by
  rw [qN, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp; ring

theorem qpow_mul_qa (N : ℕ) (hN : 0 < N) (r : ℕ) (s : ℤ) (τ : UpperHalfPlane) (n : ℕ) :
    cexp (2 * π * I * (τ : ℂ)) ^ (n + 1) * cexp (2 * π * I * ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (N : ℂ)) =
      cexp (2 * π * I * (s : ℂ) / (N : ℂ)) * qN N τ ^ ((n + 1) * N + r) := by
  rw [q_eq N hN, qa_eq N hN, ← pow_mul', pow_add]; ring

theorem qpow_mul_qa_inv (N : ℕ) (hN : 0 < N) (r : ℕ) (hr : r < N) (s : ℤ) (τ : UpperHalfPlane)
    (n : ℕ) :
    cexp (2 * π * I * (τ : ℂ)) ^ (n + 1) * (cexp (2 * π * I * ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (N : ℂ)))⁻¹ =
      (cexp (2 * π * I * (s : ℂ) / (N : ℂ)))⁻¹ * qN N τ ^ (n * N + (N - r)) := by
  rw [q_eq N hN, qa_eq N hN, ← pow_mul']
  have hq : qN N τ ≠ 0 := qN_ne_zero N τ
  have hz : cexp (2 * π * I * (s : ℂ) / (N : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hsplit : (n + 1) * N = (n * N + (N - r)) + r := by
    rw [Nat.succ_mul]; omega
  rw [hsplit, pow_add]
  field_simp

theorem pref_eq (N : ℕ) (hN : 0 < N) (r : ℕ) (s : ℤ) (z : ℂ) :
    -cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
        cexp (2 * π * I * (6 * (r : ℂ) ^ 2 - 6 * (r : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) * z /
          (12 * (N : ℂ) ^ 2)) =
      -cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
        cexp (π * I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * z) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  congr 2
  field_simp
  ring


end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion
