import Dubon2026.HeckeLowerTrace

/-! # Actual diagonal conjugation between the two Gamma0 Hecke subgroups -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckePrimeReindex
open scoped MatrixGroups Pointwise

noncomputable section

/-- Upper congruence gives the genuine integral transition into the lower subgroup. -/
theorem heckeUpperSubgroup_transition {p Q : ℕ} [NeZero p] (hp : Nat.Prime p)
    (γ : Gamma0 Q) (hγ : γ ∈ heckeUpperSubgroup Q p) :
    ∃ δ : Gamma0 Q, δ ∈ heckeLowerSubgroup Q p ∧
      heckeTriangularMatrix 1 p 0 * mapGL ℝ γ.val =
        mapGL ℝ δ.val * heckeTriangularMatrix 1 p 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hb : ((γ.val 0 1 : ℤ) : ZMod p) = 0 := hγ
  have ha : ((γ.val 0 0 : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hd := congrArg (fun z : ℤ => (z : ZMod p)) (sl2z_fin_two_det_eq_one γ.val)
    simp [hz, hb] at hd
  have hA : ¬(p : ℤ) ∣ (γ.val 0 0 + (0 : Fin p).val * γ.val 1 0) := by
    simpa only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero] using
      fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h)
  obtain ⟨δ, hδ, he⟩ := heckePrime_upper_factor hp γ.val γ.property (0 : Fin p) hA
  have hj : (moebiusFin p hp γ.val (0 : Fin p)).val = 0 := by
    simp [moebiusFin, ha, hb]
  rw [hj] at he
  refine ⟨⟨δ, hδ⟩, ?_, he⟩
  have hv := congrArg (fun A : GL (Fin 2) ℝ => A.val 1 0) he
  have hr : (p : ℝ) * (γ.val 1 0 : ℝ) = (δ 1 0 : ℝ) := by
    simpa [heckeTriangularMatrix_val, mapGL_coe_matrix, Matrix.mul_apply, Fin.sum_univ_two] using hv
  have hi : (δ 1 0 : ℤ) = (p : ℤ) * γ.val 1 0 := by exact_mod_cast hr.symm
  change ((δ 1 0 : ℤ) : ZMod p) = 0
  simp [hi]

/-- Lower congruence gives the reverse genuine integral transition at a good prime. -/
theorem heckeLowerSubgroup_transition {p Q : ℕ} [NeZero p] (hpQ : Nat.Coprime p Q)
    (δ : Gamma0 Q) (hδ : δ ∈ heckeLowerSubgroup Q p) :
    ∃ γ : Gamma0 Q, γ ∈ heckeUpperSubgroup Q p ∧
      heckeTriangularMatrix p 1 0 * mapGL ℝ δ.val =
        mapGL ℝ γ.val * heckeTriangularMatrix p 1 0 := by
  have hC : (p : ℤ) ∣ δ.val 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hδ
  obtain ⟨γ, hγ, he⟩ := heckePrime_lower_div_factor hpQ δ.val δ.property hC
  refine ⟨⟨γ, hγ⟩, ?_, he⟩
  have hv := congrArg (fun A : GL (Fin 2) ℝ => A.val 0 1) he
  have hr : (p : ℝ) * (δ.val 0 1 : ℝ) = (γ 0 1 : ℝ) := by
    simpa [heckeTriangularMatrix_val, mapGL_coe_matrix, Matrix.mul_apply, Fin.sum_univ_two] using hv
  have hi : (γ 0 1 : ℤ) = (p : ℤ) * δ.val 0 1 := by exact_mod_cast hr.symm
  change ((γ 0 1 : ℤ) : ZMod p) = 0
  simp [hi]

/-- The two prime diagonal matrices are genuine adjugates. -/
theorem peterssonAdj_heckeDiagonal (p : ℕ) [NeZero p] :
    peterssonAdj (heckeTriangularMatrix 1 p 0) = heckeTriangularMatrix p 1 0 := by
  apply Units.ext
  rw [peterssonAdj_coe, heckeTriangularMatrix_val, heckeTriangularMatrix_val]
  simp [Matrix.adjugate_fin_two]

end
end Dubon2026
