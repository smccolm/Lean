import Dubon2026.SourceCupThreeOrbits

/-! The explicit characteristic-three cup primitive required by the odd twist.
DUB-17/18 -> residual modular Galois association -> weight-two reduction in
every prime characteristic -> characteristic-three odd twist -> a primitive
for the actual upper-right/lower-right character cup an original homomorphism.
Adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_map_mul_eq_add_add_upperRightMulLowerRight_mul_of_three_dvd.lean.txt
(Apache-2.0; retained LICENSE and NOTICE).
Existing actual entry formulas, permutation coordinates, coset transitions
and native SL2(Z) cocycle existence replace the duplicated source foundations.
-/

namespace Dubon2026.SourceCupThree
noncomputable section
open CongruenceSubgroup groupCohomology
open scoped MatrixGroups

section Lift
variable (M : ℕ) (h3M : 3 ∣ M) (κ : Type) [CommRing κ] [CharP κ 3]

/-- The actual prime-field embedding into the coefficient ring. -/
noncomputable abbrev cst : ZMod 3 →+* κ := ZMod.castHom (dvd_refl 3) κ

/-- The actual transition character for S*T embedded in the coefficient ring. -/
noncomputable def cR (y : Q M) : κ := cst κ (cc M R y)

include h3M in

/-- The actual embedded S*T transition character has zero cyclic norm. -/
theorem cR_sum (y : Q M) : cR M κ y + cR M κ (R⁻¹ • y) + cR M κ (R⁻¹ • R⁻¹ • y) = 0 := by
  have h : cc M (R * R * R) y = cc M R y + cc M R (R⁻¹ • y) + cc M R (R⁻¹ • R⁻¹ • y) := by
    rw [cc_mul M h3M, cc_mul M h3M, mul_inv_rev, mul_smul]
  rw [R_pow_three, cc_neg_one] at h
  rw [cR, cR, cR, ← map_add, ← map_add, ← h, map_zero]

variable (u'' : Q M → κ) (hu'' : ∀ y : Q M, u'' y + u'' (R⁻¹ • y) + u'' (R⁻¹ • R⁻¹ • y) = 0)

/-- The explicit defect in lifting the original normalized S*T cocycle value. -/
noncomputable def DD (y : Q M) : κ :=
  cR M κ y * u'' (R⁻¹ • y) + (cR M κ y + cR M κ (R⁻¹ • y)) * u'' (R⁻¹ • R⁻¹ • y)

include h3M hu'' in

/-- The original lifting defect is constant on each actual cyclic orbit. -/
theorem DD_smul (y : Q M) : DD M κ u'' (R⁻¹ • y) = DD M κ u'' y := by
  have hR3 := Rinv_three_smul M y
  have hc := cR_sum M h3M κ y
  have hu := hu'' y
  simp only [DD, hR3]
  linear_combination (u'' y) * hc - cR M κ y * hu

/-- The original lifting defect vanishes at every fixed coset in characteristic three. -/
theorem DD_fixed (y : Q M) (hy : R⁻¹ • y = y) : DD M κ u'' y = 0 := by
  simp only [DD, hy]
  have h3 : (3 : κ) = 0 := by simpa using (CharP.cast_eq_zero κ 3)
  linear_combination (cR M κ y * u'' y) * h3

/-- The explicit orbit correction that cancels the original lifting defect. -/
noncomputable def kk (y : Q M) : κ := -(DD M κ u'' y * ee M κ y)

include h3M hu'' in

/-- The correction has exactly the negative of the original lifting defect as its cyclic norm. -/
theorem kk_sum (y : Q M) : kk M κ u'' y + kk M κ u'' (R⁻¹ • y) + kk M κ u'' (R⁻¹ • R⁻¹ • y) = -DD M κ u'' y := by
  by_cases hy : R⁻¹ • y = y
  · simp only [kk, hy, DD_fixed M κ u'' y hy]; ring
  · have h1 : DD M κ u'' (R⁻¹ • y) = DD M κ u'' y := DD_smul M h3M κ u'' hu'' y
    have h2 : DD M κ u'' (R⁻¹ • R⁻¹ • y) = DD M κ u'' y := by
      rw [DD_smul M h3M κ u'' hu'' (R⁻¹ • y), h1]
    have he := ee_smul_sum M κ y hy
    simp only [kk, h1, h2]
    linear_combination (-DD M κ u'' y) * he

/-- The explicit affine lift of the original normalized S*T cocycle value. -/
noncomputable def uu : ZMod 3 → Q M → κ := fun i y => cst κ i * u'' y + kk M κ u'' y

include hu'' in

/-- The corrected affine coefficient satisfies the actual S*T cocycle relation. -/
theorem norm_uu :
    uu M κ u'' + rhoX M h3M κ R (uu M κ u'')
      + rhoX M h3M κ R (rhoX M h3M κ R (uu M κ u'')) = 0 := by
  funext i y
  simp only [Pi.add_apply, rhoX_apply, Pi.zero_apply, uu, map_add]
  have hk := kk_sum M h3M κ u'' hu'' y
  have hu := hu'' y
  simp only [DD, cR] at hk ⊢
  linear_combination hk + (cst κ i) * hu

end Lift

end
end Dubon2026.SourceCupThree
