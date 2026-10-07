import Dubon2026.HeckeCongruenceConjugation
import Dubon2026.HeckeProjectiveCosets

/-! # Actual Hecke subgroup conjugation in the real projective action -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups Pointwise

noncomputable section

/-- The two prime diagonal matrices are inverse in the actual projective group. -/
theorem heckeProjectiveDiagonal_inverse (p : ℕ) [NeZero p] :
    ProjGenLinGroup.mk (heckeTriangularMatrix p 1 0) =
      (ProjGenLinGroup.mk (heckeTriangularMatrix 1 p 0))⁻¹ := by
  have hc : heckeTriangularMatrix 1 p 0 * heckeTriangularMatrix p 1 0 ∈
      Subgroup.center (GL (Fin 2) ℝ) := by
    apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    refine ⟨(p : ℝ), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Units.val_mul, heckeTriangularMatrix_val, Matrix.scalar_apply,
        Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have h : ProjGenLinGroup.mk (heckeTriangularMatrix 1 p 0) *
      ProjGenLinGroup.mk (heckeTriangularMatrix p 1 0) = 1 := by
    rw [← map_mul]
    exact ProjGenLinGroup.mk_eq_one.mpr hc
  exact eq_inv_of_mul_eq_one_right h

/-- Upper projective membership is the image of an actual integral congruence matrix. -/
theorem mem_heckeRealUpper_iff (Q p : ℕ) (g : PGL(2, ℝ)) :
    g ∈ heckeRealUpperSubgroup Q p ↔ ∃ γ : Gamma0 Q,
      γ ∈ heckeUpperSubgroup Q p ∧ slToRealProjective γ.val = g := by
  rw [heckeRealUpperSubgroup, Subgroup.map_map]
  rfl

/-- Lower projective membership is the image of an actual integral congruence matrix. -/
theorem mem_heckeRealLower_iff (Q p : ℕ) (g : PGL(2, ℝ)) :
    g ∈ heckeRealLowerSubgroup Q p ↔ ∃ γ : Gamma0 Q,
      γ ∈ heckeLowerSubgroup Q p ∧ slToRealProjective γ.val = g := by
  rw [heckeRealLowerSubgroup, Subgroup.map_map]
  rfl

/-- Diagonal conjugation identifies the two actual real projective Hecke subgroups. -/
theorem heckeRealLower_eq_conjugate {p Q : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    heckeRealLowerSubgroup Q p =
      ConjAct.toConjAct (ProjGenLinGroup.mk (heckeTriangularMatrix 1 p 0)) •
        heckeRealUpperSubgroup Q p := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    map_inv, ConjAct.ofConjAct_toConjAct, inv_inv,
    mem_heckeRealLower_iff, mem_heckeRealUpper_iff]
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    obtain ⟨γ, hγ, he⟩ := heckeLowerSubgroup_transition hpQ δ hδ
    refine ⟨γ, hγ, ?_⟩
    have h := congrArg ProjGenLinGroup.mk he
    simp only [map_mul] at h
    rw [heckeProjectiveDiagonal_inverse] at h
    change _ * slToRealProjective δ.val = slToRealProjective γ.val * _ at h
    have hh := congrArg (fun z => z * ProjGenLinGroup.mk (heckeTriangularMatrix 1 p 0)) h
    simpa [mul_assoc] using hh.symm
  · rintro ⟨γ, hγ, heγ⟩
    obtain ⟨δ, hδ, he⟩ := heckeUpperSubgroup_transition hp γ hγ
    refine ⟨δ, hδ, ?_⟩
    have h := congrArg ProjGenLinGroup.mk he
    simp only [map_mul] at h
    change _ * slToRealProjective γ.val = slToRealProjective δ.val * _ at h
    rw [heγ] at h
    have hh := congrArg (fun z => z * (ProjGenLinGroup.mk (heckeTriangularMatrix 1 p 0))⁻¹) h
    simpa [mul_assoc] using hh.symm

/-- The transported upper domain is a genuine lower-subgroup fundamental domain. -/
theorem isFundamentalDomain_heckeUpper_translate {p Q : ℕ} [NeZero Q] [NeZero p]
    (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    IsFundamentalDomain (heckeRealLowerSubgroup Q p)
      (ProjGenLinGroup.mk (heckeTriangularMatrix 1 p 0) •
        (⋃ x : Option (ZMod p), slToRealProjective (heckeUpperRepresentative p Q hpQ x).val •
          gamma0FundamentalDomain Q)) (volume : Measure ℍ) :=
  fundamentalDomain_smul_of_eq_conjAct (isFundamentalDomain_heckeUpper hp hpQ)
    (heckeRealLower_eq_conjugate hp hpQ)

end
end Dubon2026
