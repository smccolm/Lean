import Dubon2026.SourceCupThreeAffineCocycle

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

section Main

variable (M : ℕ) (h3M : 3 ∣ M) (κ : Type) [CommRing κ] [CharP κ 3]
variable (x : Additive (Gamma0 M) →+ κ)

/-- The original identity congruence coset. -/
def y0 : Q M := QuotientGroup.mk 1

/-- The actual congruence subgroup fixes its identity coset. -/
theorem smul_y0 (γ : Gamma0 M) : (γ : SL(2, ℤ)) • y0 M = y0 M := by
  change (QuotientGroup.mk ((γ : SL(2, ℤ)) * 1) : Q M) = QuotientGroup.mk 1
  rw [QuotientGroup.eq, mul_one, mul_one]
  exact (Gamma0 M).inv_mem γ.2

/-- The inverse of each actual congruence element fixes the identity coset. -/
theorem inv_smul_y0 (γ : Gamma0 M) : ((γ : SL(2, ℤ)))⁻¹ • y0 M = y0 M := by
  have := smul_y0 M γ⁻¹
  exact this

/-- The chosen representative of the original identity coset lies in the subgroup. -/
theorem out_y0_mem : (y0 M).out ∈ Gamma0 M := by
  have h : (QuotientGroup.mk (y0 M).out : Q M) = QuotientGroup.mk 1 := QuotientGroup.out_eq' _
  rw [QuotientGroup.eq, mul_one] at h
  exact (Gamma0 M).inv_mem_iff.mp h

/-- At the original identity coset, the actual transition is an inner conjugate of the inverse. -/
theorem jj_y0 (γ : Gamma0 M) :
    jj M (γ : SL(2, ℤ)) (y0 M) = ⟨(y0 M).out, out_y0_mem M⟩⁻¹ * (γ⁻¹ * ⟨(y0 M).out, out_y0_mem M⟩) := by
  refine Subtype.ext ?_
  rw [coe_jj]
  have h : ((γ : SL(2, ℤ)))⁻¹ • y0 M = y0 M := inv_smul_y0 M γ
  rw [h]
  rfl

include h3M in
/-- The original identity-coset transition character is the negative subgroup character. -/
theorem cc_y0 (γ : Gamma0 M) : cc M (γ : SL(2, ℤ)) (y0 M) = -phi M γ := by
  rw [cc, jj_y0, phi_conj M h3M, phi_inv M h3M]

omit [CharP κ 3] in
/-- At the original identity coset, the induced cocycle recovers the negative original homomorphism. -/
theorem zY_y0 (γ : Gamma0 M) : zY M κ x (γ : SL(2, ℤ)) (y0 M) = -x (Additive.ofMul γ) := by
  rw [zY_apply, jj_y0, ofMul_mul, ofMul_mul, ofMul_inv, ofMul_inv, map_add, map_add, map_neg, map_neg]
  abel

omit [CharP κ 3] in
/-- The normalization preserves the original homomorphism at the identity coset. -/
theorem zY'_y0 (γ : Gamma0 M) : zY' M κ x (γ : SL(2, ℤ)) (y0 M) = -x (Additive.ofMul γ) := by
  rw [zY'_apply, inv_smul_y0, sub_self, sub_zero, zY_y0]

/-- The actual prime-field character agrees with the original integral matrix-entry product. -/
theorem cst_phi (γ : Gamma0 M) :
    cst κ (phi M γ) = ((((γ : SL(2, ℤ)) 0 1) * ((γ : SL(2, ℤ)) 1 1) : ℤ) : κ) := by
  rw [phi, sourceAffineB, sourceAffineD, ← Int.cast_mul, map_intCast]

include h3M in

/-- The original characteristic-three entry character cup every actual homomorphism has an explicit primitive. -/
theorem exists_cup_primitive : ∃ H : Gamma0 M → κ, ∀ γ γ' : Gamma0 M,
    H (γ * γ') = H γ + H γ' + ((((γ : SL(2, ℤ)) 0 1) * ((γ : SL(2, ℤ)) 1 1) : ℤ) : κ) * x (Additive.ofMul γ') := by
  obtain ⟨z, hz, hP⟩ := exists_affine_cocycle M h3M κ x
  refine ⟨fun γ => z (γ : SL(2, ℤ)) 0 (y0 M), fun γ γ' => ?_⟩
  obtain ⟨K, hK⟩ := hP (γ' : SL(2, ℤ))
  have h1 : z ((γ * γ' : Gamma0 M) : SL(2, ℤ)) = z (γ : SL(2, ℤ)) + rhoX M h3M κ (γ : SL(2, ℤ)) (z (γ' : SL(2, ℤ))) :=
    cocycle_mul hz _ _
  simp only [h1, Pi.add_apply, rhoX_apply, inv_smul_y0, cc_y0 M h3M, zero_add, hK, zY'_y0, map_neg, map_zero,
    zero_mul, ← cst_phi M]
  ring

end Main

end
end Dubon2026.SourceCupThree
