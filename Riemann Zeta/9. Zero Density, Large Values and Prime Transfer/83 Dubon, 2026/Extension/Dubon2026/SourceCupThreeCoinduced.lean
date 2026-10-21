import Dubon2026.SourceCupThreeCosets

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

section Coinduced

variable (M : ℕ) (h3M : 3 ∣ M) (κ : Type) [CommRing κ]

/-- The actual characteristic-three character of the original coset transition. -/
noncomputable def cc (g : SL(2, ℤ)) (y : Q M) : ZMod 3 := phi M (jj M g y)

include h3M in
/-- The actual transition character satisfies its crossed-addition formula. -/
theorem cc_mul (g h : SL(2, ℤ)) (y : Q M) : cc M (g * h) y = cc M g y + cc M h (g⁻¹ • y) := by
  rw [cc, jj_mul, phi_mul M h3M, cc, cc, add_comm]

/-- The original identity transition character vanishes. -/
theorem cc_one (y : Q M) : cc M 1 y = 0 := by rw [cc, jj_one, phi_one]

/-- The original central minus-one transition character vanishes. -/
theorem cc_neg_one (y : Q M) : cc M (-1) y = 0 := by rw [cc, jj_neg_one, phi_neg_one]

/-- The coupled translation and permutation action on original coefficient functions. -/
noncomputable def rhoXFun (g : SL(2, ℤ)) : (ZMod 3 → Q M → κ) →ₗ[κ] (ZMod 3 → Q M → κ) where
  toFun U i y := U (i + cc M g y) (g⁻¹ • y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coupled action is the literal character translation and inverse coset action. -/
@[scoped simp] theorem rhoXFun_apply (g : SL(2, ℤ)) (U : ZMod 3 → Q M → κ) (i : ZMod 3) (y : Q M) :
    rhoXFun M κ g U i y = U (i + cc M g y) (g⁻¹ • y) := rfl

/-- The actual coupled coefficient action is a representation of SL2(Z). -/
noncomputable def rhoX : Representation κ SL(2, ℤ) (ZMod 3 → Q M → κ) where
  toFun := rhoXFun M κ
  map_one' := by
    refine LinearMap.ext fun U => funext fun i => funext fun y => ?_
    rw [rhoXFun_apply, cc_one, add_zero, inv_one, one_smul, Module.End.one_apply]
  map_mul' g h := by
    refine LinearMap.ext fun U => funext fun i => funext fun y => ?_
    rw [Module.End.mul_apply, rhoXFun_apply, rhoXFun_apply, rhoXFun_apply, cc_mul M h3M, mul_inv_rev, mul_smul,
      add_assoc]

/-- The original coupled representation has the stated pointwise action. -/
@[scoped simp] theorem rhoX_apply (g : SL(2, ℤ)) (U : ZMod 3 → Q M → κ) (i : ZMod 3) (y : Q M) :
    rhoX M h3M κ g U i y = U (i + cc M g y) (g⁻¹ • y) := rfl

end Coinduced

end
end Dubon2026.SourceCupThree
