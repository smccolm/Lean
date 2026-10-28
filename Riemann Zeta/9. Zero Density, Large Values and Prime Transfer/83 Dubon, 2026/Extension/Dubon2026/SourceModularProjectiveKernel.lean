import Dubon2026.SourceModularPingPongSets

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary
multiplier correction -> integral parabolic-character lifting -> the actual
PSL2(Z) free-product presentation. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularGroup_exists_mulEquiv_freeProduct_quotient_center.
Native Mathlib ping-pong, modular generators and scalar center are reused.
This module discharges only its named presentation dependency. -/
namespace Dubon2026.SourceModularFreeProduct
open Matrix MatrixGroups ModularGroup
open scoped Pointwise
open scoped IrrationalPt
theorem irrational_sqrt_three : Irrational (Real.sqrt 3) := by
  have h : Irrational (Real.sqrt ((3 : ℕ) : ℝ)) := Nat.prime_three.irrational_sqrt
  rwa [Nat.cast_ofNat] at h

theorem eq_zero_of_irrational_relation {x : ℝ} (hx : Irrational x) {p q : ℤ}
    (h : (p : ℝ) + (q : ℝ) * x = 0) : p = 0 ∧ q = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · refine ⟨?_, rfl⟩
    have hp : (p : ℝ) = 0 := by push_cast at h; linarith
    exact_mod_cast hp
  · exfalso
    refine hx ⟨-(p : ℚ) / (q : ℚ), ?_⟩
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    push_cast
    rw [div_eq_iff hq']
    have hcomm : x * (q : ℝ) = (q : ℝ) * x := mul_comm _ _
    linarith

theorem moebius_eq_self_relation (γ : SL(2, ℤ)) {x : ℝ} (hx : Irrational x)
    (h : moebius γ x = x) :
    (γ 1 0 : ℝ) * (x * x) + ((γ 1 1 : ℝ) - (γ 0 0 : ℝ)) * x - (γ 0 1 : ℝ) = 0 := by
  rw [moebius, div_eq_iff (den_ne_zero γ hx)] at h
  linear_combination -h

theorem eq_one_or_neg_one_of_toPerm_eq_one {γ : SL(2, ℤ)} (h : toPerm γ = 1) :
    γ = 1 ∨ γ = -1 := by
  have key : ∀ x : IrrationalPt, moebius γ (x : ℝ) = (x : ℝ) := by
    intro x
    have hx : toPerm γ x = x := by simp [h]
    have hval : ((γ • x : IrrationalPt) : ℝ) = (x : ℝ) := congrArg Subtype.val hx
    rwa [smul_coe] at hval
  have r2 := moebius_eq_self_relation γ irrational_sqrt_two
    (key ⟨Real.sqrt 2, irrational_sqrt_two⟩)
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at r2
  obtain ⟨h2a, hdiag⟩ := eq_zero_of_irrational_relation irrational_sqrt_two
    (p := 2 * γ 1 0 - γ 0 1) (q := γ 1 1 - γ 0 0) (by push_cast; linear_combination r2)
  have r3 := moebius_eq_self_relation γ irrational_sqrt_three
    (key ⟨Real.sqrt 3, irrational_sqrt_three⟩)
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at r3
  obtain ⟨h3a, -⟩ := eq_zero_of_irrational_relation irrational_sqrt_three
    (p := 3 * γ 1 0 - γ 0 1) (q := γ 1 1 - γ 0 0) (by push_cast; linear_combination r3)
  have hc : γ 1 0 = 0 := by omega
  have hb : γ 0 1 = 0 := by omega
  have hd : γ 1 1 = γ 0 0 := by omega
  have hdet : γ 0 0 * γ 0 0 = 1 := by
    have h0 := det_entries γ
    rw [hb, hc, hd] at h0
    linear_combination h0
  rcases mul_self_eq_one_iff.mp hdet with h00 | h00
  · left
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hb, hc, hd, h00]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hb, hc, hd, h00, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]

theorem mem_center_iff_eq (A : SL(2, ℤ)) : A ∈ Subgroup.center SL(2, ℤ) ↔ A = 1 ∨ A = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr' : r * r = 1 := by rw [← pow_two]; simpa using hr
    rcases mul_self_eq_one_iff.mp hr' with rfl | rfl
    · left
      apply Subtype.ext
      rw [← hA, map_one]
      rfl
    · right
      apply Subtype.ext
      rw [← hA, map_neg, map_one]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨-1, by simp, by simp⟩

theorem ker_toPerm_eq_center : toPerm.ker = Subgroup.center SL(2, ℤ) := by
  ext γ
  rw [MonoidHom.mem_ker, mem_center_iff_eq]
  constructor
  · exact eq_one_or_neg_one_of_toPerm_eq_one
  · rintro (rfl | rfl)
    · exact map_one _
    · exact toPerm_neg_one

end Dubon2026.SourceModularFreeProduct
