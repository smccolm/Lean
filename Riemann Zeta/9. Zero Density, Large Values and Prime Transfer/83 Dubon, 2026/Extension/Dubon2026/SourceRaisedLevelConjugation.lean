import Dubon2026.ModularDegeneracy
import Dubon2026.SourceIntegralHeckeConjugation

/-! The actual raised-level conjugation used by finite-function evaluation.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> original trivial-coefficient H1 at level Q*p.
The repository's original modular degeneracy matrix construction and exact
GL identity supply the integral homomorphism. The already proved inverse
Hecke conjugate supplies every actual upper-congruence subgroup element.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

variable (Q p : ℕ) [NeZero p]

/-- The existing integral degeneracy conjugate at the actual raised level. -/
def sourceRaisedLevelConjugate (g : Gamma0 (Q * p)) : Gamma0 Q :=
  let h : g.val ∈ Gamma0 (p * Q) := by simpa only [Nat.mul_comm p Q] using g.property
  ⟨levelRaiseConjOfDvd p g.val (Gamma0_dmul_lower_left_dvd p Q g.val h),
    levelRaiseConjOfDvd_mem_Gamma0 p Q g.val h⟩

/-- The raised-level map satisfies the original integral diagonal conjugation identity. -/
theorem sourceRaisedLevelConjugate_matrix (g : Gamma0 (Q * p)) :
    mapGL ℝ (sourceRaisedLevelConjugate Q p g).val * levelRaiseMatrix p =
      levelRaiseMatrix p * mapGL ℝ g.val :=
  levelRaiseMatrix_mul_mapGL p g.val
    (Gamma0_dmul_lower_left_dvd p Q g.val (by simpa only [Nat.mul_comm p Q] using g.property))

/-- The original raised-level conjugation is a genuine group homomorphism. -/
def sourceRaisedLevelConjugation : Gamma0 (Q * p) →* Gamma0 Q where
  toFun := sourceRaisedLevelConjugate Q p
  map_one' := by
    apply Subtype.ext
    apply mapGL_injective (S := ℝ)
    apply mul_right_cancel (b := levelRaiseMatrix p)
    rw [sourceRaisedLevelConjugate_matrix]
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply mapGL_injective (S := ℝ)
    apply mul_right_cancel (b := levelRaiseMatrix p)
    rw [sourceRaisedLevelConjugate_matrix]
    simp only [Subgroup.coe_mul, map_mul]
    change levelRaiseMatrix p * (mapGL ℝ g.val * mapGL ℝ h.val) =
      (mapGL ℝ (sourceRaisedLevelConjugate Q p g).val *
        mapGL ℝ (sourceRaisedLevelConjugate Q p h).val) * levelRaiseMatrix p
    rw [← mul_assoc, ← sourceRaisedLevelConjugate_matrix Q p g, mul_assoc,
      ← sourceRaisedLevelConjugate_matrix Q p h, mul_assoc]

/-- Every raised-level conjugate lies in the actual upper-congruence subgroup. -/
theorem sourceRaisedLevelConjugation_upper (g : Gamma0 (Q * p)) :
    (p : ℤ) ∣ (sourceRaisedLevelConjugation Q p g).val 0 1 :=
  ⟨g.val 0 1, rfl⟩

/-- The original raised-level conjugation is injective. -/
theorem sourceRaisedLevelConjugation_injective :
    Function.Injective (sourceRaisedLevelConjugation Q p) := by
  intro g h he
  have hm := congrArg (fun u : Gamma0 Q => mapGL ℝ u.val * levelRaiseMatrix p) he
  change mapGL ℝ (sourceRaisedLevelConjugate Q p g).val * levelRaiseMatrix p =
    mapGL ℝ (sourceRaisedLevelConjugate Q p h).val * levelRaiseMatrix p at hm
  rw [sourceRaisedLevelConjugate_matrix, sourceRaisedLevelConjugate_matrix] at hm
  exact Subtype.ext (mapGL_injective (mul_left_cancel hm))

/-- Every original upper-congruence element is reached from the actual level Q*p. -/
theorem sourceRaisedLevelConjugation_surjective_upper (u : heckeUpperSubgroup Q p) :
    ∃ g : Gamma0 (Q * p), sourceRaisedLevelConjugation Q p g = u.val := by
  let g0 := sourceIntegralHeckeConjugate u
  have hg : g0.val ∈ Gamma0 (Q * p) := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    change ((Q * p : ℕ) : ℤ) ∣ u.val.val 1 0 * (p : ℤ)
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ Q).mp (Gamma0_mem.mp u.val.property)
    refine ⟨a, ?_⟩
    rw [ha]
    push_cast
    ring
  refine ⟨⟨g0.val, hg⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hb : (u.val.val 0 1 / (p : ℤ)) * (p : ℤ) = u.val.val 0 1 :=
    Int.ediv_mul_cancel ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp u.property)
  have hc : (u.val.val 1 0 * (p : ℤ)) / (p : ℤ) = u.val.val 1 0 :=
    Int.mul_ediv_cancel _ (Int.natCast_ne_zero.mpr (NeZero.ne p))
  have hb' : (p : ℤ) * (u.val.val 0 1 / (p : ℤ)) = u.val.val 0 1 :=
    (mul_comm _ _).trans hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceRaisedLevelConjugation, sourceRaisedLevelConjugate, levelRaiseConjOfDvd,
      g0, sourceIntegralHeckeConjugate, hc, hb']

end
end Dubon2026
