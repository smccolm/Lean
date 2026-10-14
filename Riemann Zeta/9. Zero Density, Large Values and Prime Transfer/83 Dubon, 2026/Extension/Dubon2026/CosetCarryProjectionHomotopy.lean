import Dubon2026.CosetCarryProjectionTerms

/-! # The original carry corestriction is the carry of the coset norm

The explicit integer correction is weighted by the original conjugates
of a subgroup-fixed coefficient. Its differential proves the required
projection formula on actual cochains, before any local norm or invariant
identification. This discharges the cochain obstacle to norm compatibility
for DUB-17's ramified cyclotomic reciprocity calculation.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators

variable {G : Type} [Group G] (S : Subgroup G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))
  (A : Rep ℤ G) (a : A) (ha : ∀ s : S, A.ρ s a = a)

/-- The literal coset correction weighted by the original coefficient action. -/
def cosetCarryProjectionTerm (g : G) (q : G ⧸ S) : A :=
  cosetCarryCorrection S χ g q • A.ρ (g • q).out a

include ha in
/-- Each original carry trace summand differs from the corresponding conjugate carry by the actual weighted correction differential. -/
theorem cosetCarryProjectionTerm_identity (g h : G) (q : G ⧸ S) :
    zmodAdditionCarry (χ g).toAdd (χ h).toAdd • A.ρ (g • h • q).out a -
      cosetTraceTwoTerm A S
        (fun z => zmodAdditionCarry (χ z.1).toAdd (χ z.2).toAdd • a) g h q =
      A.ρ g (cosetCarryProjectionTerm S χ A a h q) -
        cosetCarryProjectionTerm S χ A a (g * h) q +
        cosetCarryProjectionTerm S χ A a g (h • q) := by
  have hc := congrArg (fun m : ℤ => m • A.ρ (g • h • q).out a)
    (cosetCarryCorrection_identity S χ g h q)
  simpa only [cosetCarryProjectionTerm, cosetTraceTwoTerm, map_zsmul, map_nsmul,
    cosetInvariantCoefficient_action S A a ha, mul_smul, sub_zsmul, add_zsmul,
    natCast_zsmul, sub_eq_add_neg, neg_zsmul] using hc

variable [Fintype (G ⧸ S)]

/-- The actual finite sum of the weighted original carry corrections. -/
def cosetCarryProjectionHomotopy : G → A :=
  fun g => ∑ q : G ⧸ S, cosetCarryProjectionTerm S χ A a g q

include ha in
/-- The differential of the constructed original cochain is the norm-coefficient carry minus the genuine coset trace of the original subgroup carry. -/
theorem cosetCarryProjectionHomotopy_differential :
    groupCohomology.d₁₂ A (cosetCarryProjectionHomotopy S χ A a) =
      (fun z => zmodAdditionCarry (χ z.1).toAdd (χ z.2).toAdd •
        (∑ q : G ⧸ S, A.ρ q.out a)) -
      cosetTraceTwo A S (fun z => zmodAdditionCarry (χ z.1).toAdd (χ z.2).toAdd • a) := by
  funext z
  obtain ⟨g, h⟩ := z
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun q _ => cosetCarryProjectionTerm_identity S χ A a ha g h q)
  have hr : (∑ q : G ⧸ S, cosetCarryProjectionTerm S χ A a g (h • q)) =
      ∑ q : G ⧸ S, cosetCarryProjectionTerm S χ A a g q :=
    Equiv.sum_comp (MulAction.toPerm h) _
  have hn : (∑ q : G ⧸ S, A.ρ (g • h • q).out a) = ∑ q : G ⧸ S, A.ρ q.out a := by
    have he := Equiv.sum_comp (MulAction.toPerm (g * h)) (fun q : G ⧸ S => A.ρ q.out a)
    change (∑ q : G ⧸ S, A.ρ ((g * h) • q).out a) = ∑ q : G ⧸ S, A.ρ q.out a at he
    simpa only [mul_smul] using he
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.smul_sum, ← map_sum, hr, hn] at hs
  exact hs.symm

end
end Dubon2026
