import Dubon2026.CosetTraceRestrictionHomotopy
import Dubon2026.RepresentationCarryCocycle

/-! # Actual coset terms for the carry and norm projection formula

The existing restriction-trace homotopy applied to the literal integer
carry gives the needed scalar correction. Weighting it by the original
subgroup-fixed coefficient will identify corestriction with the carry
of its actual norm. This serves norm compatibility of local reciprocity,
needed for the ramified cyclotomic formula and DUB-17's invariant sum.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators

variable {G : Type} [Group G] (S : Subgroup G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))

/-- The literal integer correction from the existing original coset homotopy. -/
def cosetCarryCorrection (g : G) (q : G ⧸ S) : ℤ :=
  (zmodAdditionCarry (χ g).toAdd (χ q.out).toAdd : ℤ) -
    zmodAdditionCarry (χ (g • q).out).toAdd (χ (cosetTransition S g q)).toAdd

/-- The original integer carry satisfies the exact coset projection identity, by the previously proved cocycle restriction-trace homotopy. -/
theorem cosetCarryCorrection_identity (g h : G) (q : G ⧸ S) :
    (zmodAdditionCarry (χ g).toAdd (χ h).toAdd : ℤ) -
      zmodAdditionCarry (χ (cosetTransition S g (h • q))).toAdd
        (χ (cosetTransition S h q)).toAdd =
      cosetCarryCorrection S χ h q - cosetCarryCorrection S χ (g * h) q +
        cosetCarryCorrection S χ g (h • q) := by
  let T := Rep.of (1 : Representation ℤ G ℤ)
  let c := representationCarryCocycle T χ (1 : ℤ) (fun _ => rfl)
  have hc := cosetRestrictionHomotopyTerm_identity T S c g h q
  change _ - _ = _ - _ + _ at hc
  simpa only [cosetCarryCorrection, cosetRestrictionHomotopyTerm, cosetTraceTwoTerm,
    c, representationCarryCocycle_apply, T, nsmul_eq_mul, mul_one] using hc

variable (A : Rep ℤ G) (a : A) (ha : ∀ s : S, A.ρ s a = a)

include ha in
/-- Acting on a literal coset representative of an original subgroup-fixed coefficient changes only its coset. -/
theorem cosetInvariantCoefficient_action (g : G) (q : G ⧸ S) :
    A.ρ g (A.ρ q.out a) = A.ρ (g • q).out a := by
  have h := cosetTransition_action A S g q a
  rw [ha] at h
  exact h.symm

variable [Fintype (G ⧸ S)]

include ha in
/-- The actual sum of the original conjugate coefficients is invariant under the whole original group. -/
theorem cosetInvariantCoefficient_sum_fixed (g : G) :
    A.ρ g (∑ q : G ⧸ S, A.ρ q.out a) = ∑ q : G ⧸ S, A.ρ q.out a := by
  rw [map_sum]
  simp only [cosetInvariantCoefficient_action S A a ha]
  exact Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ S => A.ρ q.out a)

end
end Dubon2026
