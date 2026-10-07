import Dubon2026.HeckeLowerCosets
import Dubon2026.HeckePrimeInvariance
import Dubon2026.PeterssonAdjugate

/-! # Exact classical Hecke traces over the genuine congruence transversals -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane Finset
open scoped MatrixGroups ModularForm

noncomputable section

/-- The p upper coset matrices give exactly the p ordinary upper Hecke representatives. -/
theorem heckeUpperMatrix_some {p Q : ℕ} [NeZero p] (hpQ : Nat.Coprime p Q)
    (x : ZMod p) :
    heckeTriangularMatrix 1 p 0 * mapGL ℝ (heckeUpperRepresentative p Q hpQ (some x)).val =
      heckeTriangularMatrix 1 p x.val := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeUpperRepresentative, heckeUpperTranslation, heckeTriangularMatrix_val,
      mapGL_coe_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The complementary upper coset gives the diagonal representative modulo actual Gamma0. -/
theorem heckeUpperMatrix_none {p Q : ℕ} [NeZero p] (hpQ : Nat.Coprime p Q) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 Q ∧
      heckeTriangularMatrix 1 p 0 * mapGL ℝ (heckeUpperRepresentative p Q hpQ none).val =
        mapGL ℝ δ * heckeTriangularMatrix p 1 0 := by
  let δ : SL(2, ℤ) := ⟨!![1, -(Int.gcdB p Q); (Q : ℤ), (p : ℤ) * Int.gcdA p Q], by
    have h := heckePrime_bezout hpQ
    simp only [Matrix.det_fin_two_of]
    nlinarith⟩
  refine ⟨δ, ?_, ?_⟩
  · rw [Gamma0_mem]
    simp [δ]
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [δ, heckeUpperRepresentative, heckeBezoutRepresentative,
        heckeTriangularMatrix_val, mapGL_coe_matrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- Summing actual upper transversal translates is the literal good-prime classical operator. -/
theorem heckeUpperTrace_eq {p Q : ℕ} [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    ∑ x : Option (ZMod p), (⇑f ∣[k] heckeTriangularMatrix 1 p 0) ∣[k]
        mapGL ℝ (heckeUpperRepresentative p Q hpQ x).val =
      classicalHeckeFunction Q k p f := by
  rw [Fintype.sum_option, classicalHeckeFunction_prime Q k hp, if_pos hpQ]
  have hn := cusp_slash_factor f (heckeUpperRepresentative p Q hpQ none).val
    (heckeUpperMatrix_none hpQ)
  rw [hn]
  have hs : (∑ x : ZMod p, (⇑f ∣[k] heckeTriangularMatrix 1 p 0) ∣[k]
      mapGL ℝ (heckeUpperRepresentative p Q hpQ (some x)).val) =
        heckeTriangularSum 1 p k f := by
    simp only [← SlashAction.slash_mul, heckeUpperMatrix_some]
    unfold heckeTriangularSum
    rw [← Fin.sum_univ_eq_sum_range, ← (ZMod.finEquiv p).toEquiv.sum_comp]
    apply Finset.sum_congr rfl
    intro x _
    have hx : ((ZMod.finEquiv p) x).val = x.val := by
      cases p with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n => rfl
    change (⇑f ∣[k] heckeTriangularMatrix 1 p ((ZMod.finEquiv p) x).val) = _
    rw [hx]
  rw [hs, add_comm]

end
end Dubon2026
