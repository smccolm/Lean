import Dubon2026.SourceCupThreeCoinduced

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

section CocycleFacts
variable {G : Type} [Group G] {K : Type} [CommRing K]
    {V : Type} [AddCommGroup V] [Module K V]

/-- The native cocycle equation in the additive order used by the explicit construction. -/
theorem cocycle_mul {ρ : Representation K G V} {z : G → V}
    (hz : z ∈ cocycles₁ (Rep.of ρ)) (g h : G) :
    z (g * h) = z g + ρ g (z h) :=
  ((mem_cocycles₁_iff (A := Rep.of ρ) z).mp hz g h).trans (add_comm _ _)

/-- Every native original cocycle vanishes at the identity. -/
theorem cocycle_one {ρ : Representation K G V} {z : G → V}
    (hz : z ∈ cocycles₁ (Rep.of ρ)) : z 1 = 0 :=
  cocycles₁_map_one (⟨z, hz⟩ : cocycles₁ (Rep.of ρ))

/-- The native cocycle inversion formula in the explicit coefficient module. -/
theorem cocycle_inv {ρ : Representation K G V} {z : G → V}
    (hz : z ∈ cocycles₁ (Rep.of ρ)) (g : G) : z g⁻¹ = -(ρ g⁻¹ (z g)) := by
  have h := cocycle_mul hz g⁻¹ g
  rw [inv_mul_cancel, cocycle_one hz] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The actual coefficient coboundary is a native cocycle. -/
theorem coboundary_mem_cocycles (ρ : Representation K G V) (v : V) :
    (fun g => ρ g v - v) ∈ cocycles₁ (Rep.of ρ) :=
  d₀₁_apply_mem_cocycles₁ (A := Rep.of ρ) v
end CocycleFacts


end
end Dubon2026.SourceCupThree
