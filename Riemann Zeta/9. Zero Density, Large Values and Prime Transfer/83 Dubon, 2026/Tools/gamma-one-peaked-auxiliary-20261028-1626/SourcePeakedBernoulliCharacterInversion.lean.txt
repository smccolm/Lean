import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree preservation -> level-power
slash integrality -> actual even-weight peaked auxiliary form -> finite
Bernoulli-order separation. Residue-class reciprocal-square weights are
diagonalized by the actual Dirichlet characters. Native character
orthogonality and nonvanishing of L(2,chi) discharge the finite convolution
kernel; no new analytic-continuation or nonvanishing hypothesis is used.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.
No upstream resource-limit option is adopted. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli
open Finset Real
open scoped Real
variable {N : ℕ} [NeZero N]
open Complex

theorem eq_zero_of_forall_sum_char_inv_mul_eq_zero (M : ℕ) [NeZero M] (a : ZMod M → ℂ)
    (h : ∀ χ : DirichletCharacter ℂ M, ∑ v : (ZMod M)ˣ, χ ((v⁻¹ : (ZMod M)ˣ) : ZMod M) * a v = 0)
    (b : (ZMod M)ˣ) : a b = 0 := by
  have hswap : ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M) * ∑ v : (ZMod M)ˣ, χ ((v⁻¹ : (ZMod M)ˣ) : ZMod M) * a v
      = ∑ v : (ZMod M)ˣ, (∑ χ : DirichletCharacter ℂ M, χ ((v : ZMod M)⁻¹) * χ (b : ZMod M)) * a v := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun χ _ => ?_
    rw [ZMod.inv_coe_unit]
    ring
  have key : ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M) * ∑ v : (ZMod M)ˣ, χ ((v⁻¹ : (ZMod M)ˣ) : ZMod M) * a v
      = (M.totient : ℂ) * a b := by
    rw [hswap]
    simp_rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit _) (b : ZMod M)]
    rw [Finset.sum_eq_single b]
    · simp
    · intro v _ hv
      rw [if_neg (fun h' => hv (Units.ext h')), zero_mul]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  have hzero : ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M) *
      ∑ v : (ZMod M)ˣ, χ ((v⁻¹ : (ZMod M)ˣ) : ZMod M) * a v = 0 :=
    Finset.sum_eq_zero fun χ _ => by rw [h χ, mul_zero]
  rw [key] at hzero
  have htot : (M.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))).ne'
  exact (mul_eq_zero.mp hzero).resolve_left htot


end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli
