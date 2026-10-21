import Dubon2026.SourceCupThreeNativeCocycles

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

section FromX

variable (M : ℕ) (h3M : 3 ∣ M) (κ : Type) [CommRing κ] [CharP κ 3]
variable (x : Additive (Gamma0 M) →+ κ)

/-- The given original homomorphism evaluated at the actual inverse coset transition. -/
noncomputable def zY (g : SL(2, ℤ)) : Q M → κ := fun y => x (Additive.ofMul (jj M g y))

omit [CharP κ 3] in
/-- The original induced cocycle has the stated transition evaluation. -/
theorem zY_apply (g : SL(2, ℤ)) (y : Q M) : zY M κ x g y = x (Additive.ofMul (jj M g y)) := rfl

omit [CharP κ 3] in

/-- The actual transition evaluation defines a native permutation-coefficient cocycle. -/
theorem zY_mem : zY M κ x ∈ cocycles₁ (Rep.of (permRep M κ)) := by
  apply (mem_cocycles₁_iff _).mpr
  intro g h
  funext y
  rw [Pi.add_apply, permRep_apply, zY_apply, zY_apply, zY_apply, jj_mul, ofMul_mul, map_add, add_comm]

/-- The actual modular generator S. -/
abbrev S : SL(2, ℤ) := ModularGroup.S
/-- The actual modular generator S*T. -/
def R : SL(2, ℤ) := ModularGroup.S * ModularGroup.T

/-- The construction uses the original generator S. -/
theorem S_def : S = ModularGroup.S := rfl
/-- The construction uses the original product S*T. -/
theorem R_def : R = ModularGroup.S * ModularGroup.T := rfl

/-- The existing original generator relation S squared equals minus one. -/
theorem S_mul_S : S * S = (-1 : SL(2, ℤ)) := SourceSL2Cocycle.S_mul_S

/-- The original generator S has fourth power one. -/
theorem S_pow_four : S * S * S * S = (1 : SL(2, ℤ)) := by
  rw [S_mul_S, show (-1 : SL(2, ℤ)) * S * S = -1 * (S * S) by group, S_mul_S]
  simp

/-- The existing original relation for the cube of S*T. -/
theorem R_pow_three : R * R * R = (-1 : SL(2, ℤ)) := by
  rw [show R * R * R = R ^ 3 by rw [pow_succ, pow_two]]
  exact SourceSL2Cocycle.U_pow_three

/-- The original permutation coefficient module has characteristic three. -/
theorem three_eq_zero : (3 : Q M → κ) = 0 := by
  funext y
  change (3 : κ) = 0
  simpa using (CharP.cast_eq_zero κ 3)

/-- The explicit coboundary cancels the original induced cocycle at S. -/
theorem zY_S_eq_coboundary :
    permRep M κ S (-(zY M κ x S + zY M κ x (S * S) + zY M κ x (S * S * S)))
      - (-(zY M κ x S + zY M κ x (S * S) + zY M κ x (S * S * S))) = zY M κ x S := by
  set ρ := permRep M κ with hρ
  have hz := zY_mem M κ x
  set c₁ := zY M κ x S with hc₁
  set c₂ := zY M κ x (S * S) with hc₂
  set c₃ := zY M κ x (S * S * S) with hc₃
  have h2 : c₂ = c₁ + ρ S c₁ := cocycle_mul hz S S
  have h3 : c₃ = c₂ + ρ (S * S) c₁ := cocycle_mul hz (S * S) S
  have h4 : (0 : Q M → κ) = c₃ + ρ (S * S * S) c₁ := by
    rw [← cocycle_one hz, ← S_pow_four]; exact cocycle_mul hz (S * S * S) S
  have hS2 : ρ S c₂ = c₃ - c₁ := by
    rw [h2, map_add, ← Module.End.mul_apply, ← map_mul, h3, h2]; abel
  have hS3 : ρ S c₃ = -c₁ := by
    rw [h3, map_add, hS2, ← Module.End.mul_apply, ← map_mul, show S * (S * S) = S * S * S by group]
    have : ρ (S * S * S) c₁ = -c₃ := by rw [eq_neg_iff_add_eq_zero, add_comm, ← h4]
    rw [this]; abel
  have hS1 : ρ S c₁ = c₂ - c₁ := by rw [h2]; abel
  rw [map_neg, map_add, map_add, hS1, hS2, hS3]
  have h3z := three_eq_zero M κ
  linear_combination c₁ * h3z

/-- The explicit coefficient producing the required normalization at S. -/
noncomputable def ww : Q M → κ := -(zY M κ x S + zY M κ x (S * S) + zY M κ x (S * S * S))

/-- The native induced cocycle with its explicit S-normalizing coboundary removed. -/
noncomputable def zY' : SL(2, ℤ) → Q M → κ :=
  zY M κ x - fun g => permRep M κ g (ww M κ x) - ww M κ x

omit [CharP κ 3] in
/-- The normalized original induced cocycle remains a native cocycle. -/
theorem zY'_mem : zY' M κ x ∈ cocycles₁ (Rep.of (permRep M κ)) := by
  have h1 := zY_mem M κ x
  have h2 := coboundary_mem_cocycles (permRep M κ) (ww M κ x)
  exact (cocycles₁ (Rep.of (permRep M κ))).sub_mem h1 h2

omit [CharP κ 3] in

/-- The normalized cocycle is the exact original transition evaluation minus its coboundary. -/
theorem zY'_apply (g : SL(2, ℤ)) (y : Q M) :
    zY' M κ x g y = zY M κ x g y - (ww M κ x (g⁻¹ • y) - ww M κ x y) := rfl

/-- The normalized original cocycle vanishes at S. -/
theorem zY'_S : zY' M κ x S = 0 := by
  have h := zY_S_eq_coboundary M κ x
  change zY M κ x S - (permRep M κ S (ww M κ x) - ww M κ x) = 0
  rw [ww, h, sub_self]

/-- The normalized original cocycle vanishes at the central minus-one matrix. -/
theorem zY'_neg_one : zY' M κ x (-1) = 0 := by
  rw [← S_mul_S, cocycle_mul (zY'_mem M κ x) S S, zY'_S, map_zero, add_zero]

/-- The normalized original cocycle satisfies the required S*T norm relation. -/
theorem norm_zY'_R :
    zY' M κ x R + permRep M κ R (zY' M κ x R) + permRep M κ R (permRep M κ R (zY' M κ x R)) = 0 := by
  have hz := zY'_mem M κ x
  have h2 : zY' M κ x (R * R) = zY' M κ x R + permRep M κ R (zY' M κ x R) := cocycle_mul hz R R
  have h3 : zY' M κ x (R * R * R) = zY' M κ x (R * R) + permRep M κ (R * R) (zY' M κ x R) := cocycle_mul hz (R * R) R
  rw [R_pow_three, zY'_neg_one, h2, map_mul (permRep M κ) R R, Module.End.mul_apply] at h3
  rw [h3]

/-- The original normalized cocycle has zero sum over every S*T orbit. -/
theorem norm_zY'_R_apply (y : Q M) :
    zY' M κ x R y + zY' M κ x R (R⁻¹ • y) + zY' M κ x R (R⁻¹ • R⁻¹ • y) = 0 := by
  have h := congrFun (norm_zY'_R M κ x) y
  rw [Pi.add_apply, Pi.add_apply, permRep_apply, permRep_apply, permRep_apply, Pi.zero_apply] at h
  exact h

end FromX

end
end Dubon2026.SourceCupThree
