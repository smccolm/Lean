import Dubon2026.SourceCupThreeEntries
import Dubon2026.SourceGamma0CuspFunctional
import Dubon2026.CosetTransitionCoordinates

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

section Cosets

variable (M : ℕ) (κ : Type) [CommRing κ]

/-- The actual original congruence coset space. -/
abbrev Q : Type := SL(2, ℤ) ⧸ Gamma0 M

/-- The existing actual permutation representation on original cosets. -/
abbrev permRep : Representation κ SL(2, ℤ) (Q M → κ) :=
  (permutationCoordinateRep κ SL(2, ℤ) (Q M)).ρ

/-- The original permutation action evaluates at the inverse-translated coset. -/
@[scoped simp] theorem permRep_apply (g : SL(2, ℤ)) (f : Q M → κ) (q : Q M) : permRep M κ g f q = f (g⁻¹ • q) := rfl

/-- The actual central minus-one matrix lies in the congruence subgroup. -/
theorem neg_one_mem : (-1 : SL(2, ℤ)) ∈ Gamma0 M := by
  rw [Gamma0_mem]; simp

/-- Inversion commutes with negation in the original special linear group. -/
theorem neg_inv (g : SL(2, ℤ)) : (-g)⁻¹ = -g⁻¹ := by
  ext i j; simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- The actual central minus-one matrix fixes every original coset. -/
theorem neg_one_smul_Q (q : Q M) : (-1 : SL(2, ℤ)) • q = q :=
  sourceGamma0Coset_neg_one M q

variable {κ}

/-- The existing actual transition coordinate at the inverse group element. -/
noncomputable def jj (g : SL(2, ℤ)) (y : Q M) : Gamma0 M := cosetTransition (Gamma0 M) g⁻¹ y

/-- The transition coordinate is the literal original matrix product. -/
theorem coe_jj (g : SL(2, ℤ)) (y : Q M) : (jj M g y : SL(2, ℤ)) = (g⁻¹ • y).out⁻¹ * (g⁻¹ * y.out) := rfl

/-- The original inverse transition satisfies its crossed-product formula. -/
theorem jj_mul (g h : SL(2, ℤ)) (y : Q M) : jj M (g * h) y = jj M h (g⁻¹ • y) * jj M g y := by
  rw [jj, mul_inv_rev, cosetTransition_mul]; rfl

/-- The original identity transition is the subgroup identity. -/
theorem jj_one (y : Q M) : jj M 1 y = 1 := by
  refine Subtype.ext ?_
  rw [coe_jj]
  simp

/-- The original minus-one transition is the subgroup minus-one matrix. -/
theorem jj_neg_one (y : Q M) : jj M (-1) y = ⟨-1, neg_one_mem M⟩ := by
  refine Subtype.ext ?_
  rw [coe_jj]
  have h1 : ((-1 : SL(2, ℤ)))⁻¹ = -1 := by rw [neg_inv, inv_one]
  rw [h1, neg_one_smul_Q]
  change (y.out)⁻¹ * (-1 * y.out) = -1
  rw [neg_one_mul, mul_neg, inv_mul_cancel]

end Cosets

end
end Dubon2026.SourceCupThree
