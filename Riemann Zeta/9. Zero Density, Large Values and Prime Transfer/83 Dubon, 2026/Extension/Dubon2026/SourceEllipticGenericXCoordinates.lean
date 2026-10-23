import Dubon2026.SourceEllipticGenericSequence

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular good reduction ->
reverse genus -> finite exceptional fibers -> actual elliptic torsion count
-> division-polynomial point multiplication. The actual universal point is
multiplied using the native elliptic-curve group law. The identities will
descend to the integral coordinate ring and specialize to every nonsingular
point. Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, EDSEngine. -/
namespace Dubon2026.SourceEllipticUniversal.AffineFormula
open WeierstrassCurve Polynomial Dubon2026.SourceEllipticDivision
open WeierstrassCurve (ψ φ)
open Dubon2026.SourceEllipticSequence
open scoped Polynomial.Bivariate nonZeroDivisors
noncomputable section
variable {m n : ℤ}
variable (n)
/-- The actual generic division-polynomial x-coordinate. -/
def smulX : FunctionField := polyToField (curve.φ n) / (ψᵤ n) ^ 2

/-- The actual generic integral division-polynomial y-coordinate. -/
def smulY : FunctionField := polyToField ((ωe curve) n) / (ψᵤ n) ^ 3
variable {n}

@[simp] theorem smulX_zero : smulX 0 = 0 := by simp [smulX, ψᵤ]
@[simp] theorem smulY_zero : smulY 0 = 0 := by simp [smulY, ψᵤ]
@[simp] theorem smulX_one : smulX 1 = polyToField (C X) := by simp [smulX, ψᵤ]
@[simp] theorem smulY_one : smulY 1 = polyToField Y := by simp [smulY, ψᵤ]

theorem smulX_eq (hn : n ≠ 0) :
    smulX n = smulX 1 - ψᵤ (n + 1) * ψᵤ (n - 1) / (ψᵤ n) ^ 2 := by
  rw [smulX, smulX_one, φ, map_sub, sub_div, map_mul, map_pow, mul_div_cancel_right₀, map_mul]
  exact pow_ne_zero _ (ψᵤ_ne_zero hn)

theorem smulX_two : smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 := by
  simp [smulX_eq two_ne_zero, ψᵤ]

theorem smulX_sub_smulX (hm : m ≠ 0) (hn : n ≠ 0) :
    smulX m - smulX n = (ψᵤ (n + m) * ψᵤ (n - m)) / (ψᵤ n * ψᵤ m) ^ 2 := by
  rw [smulX_eq hm, smulX_eq hn, sub_sub_sub_cancel_left, div_sub_div]
  · rw [mul_pow]; congr; convert (isEllSequence_ψᵤ n m 1).symm using 1
    · ring
    · simp [ψᵤ]
  all_goals exact pow_ne_zero _ (ψᵤ_ne_zero <| by assumption)

theorem smulX_sub_sub_smulX_add (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n - m) - smulX (n + m) = (ψᵤ (2 * n) * ψᵤ (2 * m)) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 := by
  rw [smulX_sub_smulX sub_ne add_ne]; ring_nf

theorem smulX_neg : smulX (-n) = smulX n := by simp_rw [smulX, φ_neg, ψᵤ, ψ_neg, ← map_pow, neg_sq]

theorem smulX_ne_zero (h0 : n ≠ 0) : smulX n ≠ 0 :=
  div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)

theorem smulX_ne_smulX (ne : m ≠ n) (ne_neg : m ≠ -n) : smulX m ≠ smulX n := by
  obtain rfl | hm := eq_or_ne m 0
  · rw [smulX_zero]; exact (smulX_ne_zero ne.symm).symm
  obtain rfl | hn := eq_or_ne n 0
  · rw [smulX_zero]; exact smulX_ne_zero ne
  rw [← sub_ne_zero, smulX_sub_smulX hm hn]
  rw [ne_comm, ← sub_ne_zero] at ne
  rw [Ne, ← add_eq_zero_iff_eq_neg, add_comm] at ne_neg
  refine div_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero _ <| mul_ne_zero ?_ ?_) <;>
    apply ψᵤ_ne_zero <;> assumption

theorem smulX_eq_smulX_iff : smulX m = smulX n ↔ m = n ∨ m = -n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h; exact smulX_ne_smulX h.1 h.2
  · rintro (rfl|rfl); exacts [rfl, smulX_neg]


end
end Dubon2026.SourceEllipticUniversal.AffineFormula
