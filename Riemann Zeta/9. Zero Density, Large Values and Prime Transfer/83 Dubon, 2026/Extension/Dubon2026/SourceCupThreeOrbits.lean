import Dubon2026.SourceCupThreeNormalizedCocycle

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

/-- The actual inverse S*T action has period three on original cosets. -/
theorem Rinv_three_smul (y : Q M) : R⁻¹ • R⁻¹ • R⁻¹ • y = y := by
  have h : R⁻¹ * R⁻¹ * R⁻¹ = (-1 : SL(2, ℤ)) := by
    rw [← mul_inv_rev, ← mul_inv_rev, show R * (R * R) = R * R * R by group, R_pow_three, neg_inv, inv_one]
  rw [smul_smul, smul_smul, h, neg_one_smul_Q]

/-- Every multiple of three acts trivially on original cosets. -/
theorem Rinv_pow_three_mul_smul (n : ℕ) (y : Q M) : (R⁻¹) ^ (3 * n) • y = y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, pow_add, mul_smul, show (R⁻¹) ^ 3 = R⁻¹ * (R⁻¹ * R⁻¹) by rw [pow_succ, pow_two, mul_assoc],
      mul_smul, mul_smul, Rinv_three_smul, ih]

/-- The actual cyclic S*T orbit equivalence on original congruence cosets. -/
def orbitSetoid : Setoid (Q M) where
  r y y' := ∃ n : ℕ, y' = (R⁻¹) ^ n • y
  iseqv :=
    { refl := fun y => ⟨0, by simp⟩
      symm := by
        rintro y y' ⟨n, rfl⟩
        refine ⟨2 * n, ?_⟩
        rw [← mul_smul, ← pow_add, show 2 * n + n = 3 * n by ring, Rinv_pow_three_mul_smul]
      trans := by
        rintro y y' y'' ⟨n, rfl⟩ ⟨m, rfl⟩
        exact ⟨m + n, by rw [pow_add, mul_smul]⟩ }

/-- A representative of the actual three-periodic coset orbit. -/
noncomputable def rep (y : Q M) : Q M := (Quotient.mk (orbitSetoid M) y).out

/-- Every original coset is reached from its chosen cyclic orbit representative. -/
theorem rep_spec (y : Q M) : ∃ n : ℕ, y = (R⁻¹) ^ n • rep M y :=
  Quotient.mk_out (s := orbitSetoid M) y

/-- The chosen cyclic orbit representative is unchanged by the actual S*T action. -/
theorem rep_smul (y : Q M) : rep M (R⁻¹ • y) = rep M y := by
  unfold rep
  congr 1
  exact Quotient.sound (⟨2, by rw [pow_two, mul_smul, Rinv_three_smul]⟩ : (orbitSetoid M) (R⁻¹ • y) y)

/-- The chosen representative is one of the three actual orbit points. -/
theorem rep_mem (y : Q M) : rep M y = y ∨ rep M y = R⁻¹ • y ∨ rep M y = R⁻¹ • R⁻¹ • y := by
  obtain ⟨n, hn⟩ := rep_spec M y

  have h1 : rep M y = (R⁻¹) ^ (2 * n) • y := by
    symm
    conv_lhs => rw [hn]
    rw [← mul_smul, ← pow_add, show 2 * n + n = 3 * n by ring, Rinv_pow_three_mul_smul]
  have h2 : (R⁻¹) ^ (2 * n) • y = (R⁻¹) ^ ((2 * n) % 3) • y := by
    conv_lhs => rw [← Nat.mod_add_div (2 * n) 3, pow_add, mul_smul, Rinv_pow_three_mul_smul]
  rw [h1, h2]
  have h3 : (2 * n) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (2 * n) % 3
  · left; simp
  · right; left; simp
  · right; right; rw [pow_two, mul_smul]

/-- The indicator of the chosen original cyclic orbit representative. -/
noncomputable def ee (y : Q M) : κ := by
  classical
  exact if rep M y = y then 1 else 0

omit [CharP κ 3] in
/-- On each nonfixed original orbit the representative indicator sums to one. -/
theorem ee_smul_sum (y : Q M) (hy : R⁻¹ • y ≠ y) :
    ee M κ y + ee M κ (R⁻¹ • y) + ee M κ (R⁻¹ • R⁻¹ • y) = 1 := by
  classical
  have hR3 := Rinv_three_smul M y

  have h01 : R⁻¹ • y ≠ y := hy
  have h12 : R⁻¹ • R⁻¹ • y ≠ R⁻¹ • y := fun h => hy (MulAction.injective R⁻¹ h)
  have h02 : R⁻¹ • R⁻¹ • y ≠ y := by
    intro h
    apply hy
    have h' : R⁻¹ • R⁻¹ • R⁻¹ • y = R⁻¹ • y := congrArg (fun q => R⁻¹ • q) h
    rw [hR3] at h'
    exact h'.symm
  simp only [ee, rep_smul]
  rcases rep_mem M y with h | h | h
  · rw [if_pos h, if_neg (by rw [h]; exact h01.symm), if_neg (by rw [h]; exact h02.symm)]; ring
  · rw [if_neg (by rw [h]; exact h01), if_pos h, if_neg (by rw [h]; exact h12.symm)]; ring
  · rw [if_neg (by rw [h]; exact h02), if_neg (by rw [h]; exact h12), if_pos h]; ring

end Lift

end
end Dubon2026.SourceCupThree
