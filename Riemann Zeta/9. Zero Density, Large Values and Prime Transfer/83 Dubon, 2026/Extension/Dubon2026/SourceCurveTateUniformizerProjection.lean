import Dubon2026.SourceCurvePoleProjection

/-! The canonical integral projection extracts precisely the simple-pole
coefficient after multiplication by the uniformizer. This is the necessary
local identification between the projected commutator and the already proved
normalized scalar residue, with no change of residue convention. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The canonical integral projection kills every pure negative power. -/
theorem tateProj_neg_pow (n : ℕ) :
    v.tateProj (v.uniformizer ^ (-(n + 1 : ℤ))) = 0 := by
  change v.uniformizer ^ (-(n + 1 : ℤ)) - v.principalPartLift (v.poleClass n) = 0
  rw [v.principalPartLift_poleClass, sub_self]

/-- The projection of a uniformizer times a pure principal part is its simple-pole coefficient. -/
theorem tateProj_uniformizer_mul_poleClass (n : ℕ) :
    v.tateProj (v.uniformizer * v.principalPartLift (v.poleClass n)) =
      if n = 0 then 1 else 0 := by
  rw [v.principalPartLift_poleClass]
  cases n with
  | zero =>
      simp only [Nat.cast_zero, zero_add, zpow_neg_one, mul_inv_cancel₀ v.uniformizer_ne_zero,
        ite_true]
      exact v.tateProj_of_mem (one_mem _)
  | succ n =>
      have h : v.uniformizer * v.uniformizer ^ (-((n + 1 : ℕ) + 1 : ℤ)) =
          v.uniformizer ^ (-(n + 1 : ℤ)) := by
        conv_lhs => lhs; rw [← zpow_one v.uniformizer]
        rw [← zpow_add₀ v.uniformizer_ne_zero]
        congr 1
      rw [h, v.tateProj_neg_pow]
      simp

/-- The full finite principal part gives the literal existing scalar residue after projection. -/
theorem tateProj_uniformizer_mul_principalPart (f : F) :
    v.tateProj (v.uniformizer * v.principalPart f) =
      algebraMap K F (v.localResidueScalar f) := by
  let c := (Finsupp.linearCombination K v.poleClass).leftInverse (v.integralFunctions.mkQ f)
  have hc : v.principalPart f = Finsupp.linearCombination K
      (fun n : ℕ => v.uniformizer ^ (-(n + 1 : ℤ))) c := rfl
  have hr : v.localResidueScalar f = c 0 := rfl
  rw [hc, hr, Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum, map_sum]
  have hterm (n : ℕ) :
      v.tateProj (v.uniformizer * (c n • v.uniformizer ^ (-(n + 1 : ℤ)))) =
      if n = 0 then algebraMap K F (c n) else 0 := by
    rw [mul_smul_comm, map_smul]
    rw [← v.principalPartLift_poleClass, v.tateProj_uniformizer_mul_poleClass]
    split_ifs <;> simp [Algebra.smul_def]
  simp_rw [hterm]
  classical
  simp
  intro hz
  rw [hz, map_zero]

end Dubon2026.SourceCurve.Place
