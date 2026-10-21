import Dubon2026.SourceAffineFunctionRepresentation

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

variable (M : ℕ)

/-- The actual reduced upper-right/lower-right product at characteristic three. -/
def phi (γ : Gamma0 M) : ZMod 3 := sourceAffineB 3 M γ * sourceAffineD 3 M γ

variable (h3M : 3 ∣ M)
include h3M

/-- The actual lower-right entry has square one modulo three. -/
theorem d3_mul_d3 (γ : Gamma0 M) : sourceAffineD 3 M γ * sourceAffineD 3 M γ = 1 := by
  have h := sourceAffine_ad 3 M h3M γ
  have hd : sourceAffineD 3 M γ ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at h
    exact zero_ne_one h
  generalize sourceAffineD 3 M γ = d at hd
  fin_cases d
  · exact absurd rfl hd
  · rfl
  · rfl

/-- The actual entry product is additive on the congruence group. -/
theorem phi_mul (γ γ' : Gamma0 M) : phi M (γ * γ') = phi M γ + phi M γ' := by
  rw [phi, phi, phi, sourceAffine_b_mul, sourceAffine_d_mul 3 M h3M]
  have h1 := sourceAffine_ad 3 M h3M γ
  have h2 := d3_mul_d3 M h3M γ'
  linear_combination (sourceAffineB 3 M γ' * sourceAffineD 3 M γ') * h1 +
    (sourceAffineB 3 M γ * sourceAffineD 3 M γ) * h2

omit h3M in
/-- The actual identity has zero upper-right character. -/
theorem phi_one : phi M 1 = 0 := by simp [phi, sourceAffineB]

/-- Inversion negates the actual upper-right character. -/
theorem phi_inv (γ : Gamma0 M) : phi M γ⁻¹ = -phi M γ := by
  have h := phi_mul M h3M γ⁻¹ γ
  rw [inv_mul_cancel, phi_one] at h
  linear_combination (-1 : ZMod 3) * h

/-- The actual upper-right character is invariant under subgroup conjugation. -/
theorem phi_conj (a γ : Gamma0 M) : phi M (a⁻¹ * (γ * a)) = phi M γ := by
  rw [phi_mul M h3M, phi_mul M h3M, phi_inv M h3M]
  ring

omit h3M in
/-- The actual central minus-one matrix has zero upper-right character. -/
theorem phi_neg_one : phi M ⟨-1, by rw [Gamma0_mem]; simp⟩ = 0 := by
  simp [phi, sourceAffineB]


end
end Dubon2026.SourceCupThree
