import Dubon2026.HeckePrimeOrbits

/-! DUB-17/18 -> original all-weight adic association -> arithmetic
realization of finite permutation cohomology -> cover by Gamma1 curves.
The inspected Gamma1 arithmetic construction can serve this route only
after its level is linked to the actual principal congruence kernel.
The explicit diagonal conjugation below supplies that link. Reuse the
existing integral determinant calculation and native congruence subgroups;
no arbitrary new modular-curve construction is introduced. -/
namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckePrimeReindex
open scoped MatrixGroups

/-- The actual diagonal sends Gamma1 at level Q*N^2 into Gamma0(Q)
and the principal level-N subgroup, with an integral transition matrix. -/
theorem sourceGammaOne_principal_diagonal_transition
    (Q N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma1 (Q * N ^ 2)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 Q ∧ δ ∈ Gamma N ∧
      heckeTriangularMatrix N 1 0 * mapGL ℝ γ =
        mapGL ℝ δ * heckeTriangularMatrix N 1 0 := by
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem _ _).mp hγ
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ.val 1 0) (Q * N ^ 2)).mp hc
  have hNlevel : N ∣ Q * N ^ 2 := by
    exact dvd_mul_of_dvd_right (dvd_pow_self N (by decide : 2 ≠ 0)) Q
  have haN : (γ.val 0 0 : ZMod N) = 1 := by
    simpa only [map_intCast, map_one] using congrArg (ZMod.castHom hNlevel (ZMod N)) ha
  have hdN : (γ.val 1 1 : ZMod N) = 1 := by
    simpa only [map_intCast, map_one] using congrArg (ZMod.castHom hNlevel (ZMod N)) hd
  have hcN : γ.val 1 0 = (N : ℤ) * ((Q : ℤ) * N * t) := by
    rw [ht, Nat.cast_mul, Nat.cast_pow]
    ring
  have hcR : (γ.val 1 0 : ℝ) = (N : ℝ) * ((Q : ℝ) * N * (t : ℝ)) := by
    exact_mod_cast hcN
  let δ : SL(2, ℤ) :=
    ⟨!![γ.val 0 0, N * γ.val 0 1; (Q : ℤ) * N * t, γ.val 1 1],
      lower_div_tau_det_eq_one (sl2z_fin_two_det_eq_one γ) N ((Q : ℤ) * N * t) hcN⟩
  refine ⟨δ, ?_, ?_, ?_⟩
  · rw [Gamma0_mem]
    change (((Q : ℤ) * N * t : ℤ) : ZMod Q) = 0
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  · rw [Gamma_mem]
    change (γ.val 0 0 : ZMod N) = 1 ∧
      (((N : ℤ) * γ.val 0 1 : ℤ) : ZMod N) = 0 ∧
      (((Q : ℤ) * N * t : ℤ) : ZMod N) = 0 ∧ (γ.val 1 1 : ZMod N) = 1
    exact ⟨haN, by simp, by simp, hdN⟩
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeTriangularMatrix_val, mapGL_coe_matrix,
        Matrix.mul_apply, Fin.sum_univ_two, δ] <;>
      first | ring1 | nlinarith [hcR]

/-- The same concrete Gamma1 level lies in the native rational diagonal
conjugate of the original principal congruence cover. -/
theorem sourceGammaOne_le_conj_principalLevel
    (Q N : ℕ) [NeZero N] :
    Gamma1 (Q * N ^ 2) ≤ conjGL (Gamma0 Q ⊓ Gamma N) (heckeTriangularMatrix N 1 0) := by
  intro γ hγ
  obtain ⟨δ, hδQ, hδN, he⟩ := sourceGammaOne_principal_diagonal_transition Q N γ hγ
  apply mem_conjGL.mpr
  refine ⟨δ, ⟨hδQ, hδN⟩, ?_⟩
  change mapGL ℝ δ = heckeTriangularMatrix N 1 0 * mapGL ℝ γ *
    (heckeTriangularMatrix N 1 0)⁻¹
  rw [he, mul_inv_cancel_right]

end
end Dubon2026
