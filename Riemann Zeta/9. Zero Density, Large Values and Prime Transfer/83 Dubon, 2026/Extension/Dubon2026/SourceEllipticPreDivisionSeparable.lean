import Dubon2026.SourceEllipticSeparableCoordinates
import Dubon2026.SourceEllipticTorsionAbscissaCount
import Dubon2026.SourceEllipticTorsionDivisionRoot

/-! Direct all-order separability from actual torsion cardinality.
Removing the two-torsion for even order, or infinity for odd order, gives
enough distinct abscissae to fill the native pre-division-polynomial degree.
This discharges separability in the finite Galois torsion field needed for
the positive-characteristic exceptional-fiber census (DUB-17/18). -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open Dubon2026.SourceEllipticVelu.OddDiscriminant
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

theorem preDivision_separable (E : WeierstrassCurve F) [E.IsElliptic]
    {n : ℕ} (hn : (n : F) ≠ 0) : (E.preΨ n).Separable := by
  have hni : ((n : ℤ) : F) ≠ 0 := by exact_mod_cast hn
  let T := torsFinset E hn
  have hTc : T.card = n ^ 2 := card_torsFinset hn
  by_cases he : Even n
  · have h2 : (2 : F) ≠ 0 := by
      obtain ⟨m, hm⟩ := he
      intro hz
      apply hn
      rw [hm, Nat.cast_add, ← two_mul, hz, zero_mul]
    let T2 := torsFinset E (show ((2 : ℕ) : F) ≠ 0 from h2)
    have hT2 : T2 ⊆ T := by
      intro P hP
      have hp := (mem_torsFinset _ P).mp hP
      apply (mem_torsFinset _ P).mpr
      obtain ⟨m, hm⟩ := he
      rw [hm, ← two_mul, mul_nsmul, hp, nsmul_zero]
    let U := T \ T2
    have hUc : U.card = n ^ 2 - 4 := by
      rw [Finset.card_sdiff_of_subset hT2, hTc, card_torsFinset]
      norm_num
    have hU0 : ∀ P ∈ U, P ≠ 0 := by
      intro P hP hz
      have hP2 := (Finset.mem_sdiff.mp hP).2
      apply hP2
      rw [hz, mem_torsFinset, nsmul_zero]
    let Xs := U.image xco
    have hcount := card_le_two_mul_card_abscissae U hU0
    rw [hUc] at hcount
    apply separable_of_natDegree_le_card (E.preΨ_ne_zero hni) Xs
    · intro t ht
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ht
      have hP0 := hU0 P hP
      obtain ⟨hPT, hP2⟩ := Finset.mem_sdiff.mp hP
      rcases P with _ | ⟨x, y, h⟩
      · exact (hP0 rfl).elim
      · exact preDivision_eval_zero_of_torsion E h
          ((mem_torsFinset hn _).mp hPT)
          (fun _ hz => hP2 ((mem_torsFinset _ _).mpr hz))
    · rw [E.natDegree_preΨ hni, Int.natAbs_natCast,
        if_pos ((Int.even_coe_nat n).mpr he)]
      change n ^ 2 - 4 ≤ 2 * Xs.card at hcount
      omega
  · let U := T.erase 0
    have hzT : 0 ∈ T := (mem_torsFinset hn _).mpr (nsmul_zero _)
    have hUc : U.card = n ^ 2 - 1 := by rw [Finset.card_erase_of_mem hzT, hTc]
    have hU0 : ∀ P ∈ U, P ≠ 0 := fun _ hP => (Finset.mem_erase.mp hP).1
    let Xs := U.image xco
    have hcount := card_le_two_mul_card_abscissae U hU0
    rw [hUc] at hcount
    apply separable_of_natDegree_le_card (E.preΨ_ne_zero hni) Xs
    · intro t ht
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hP0, hPT⟩ := Finset.mem_erase.mp hP
      rcases P with _ | ⟨x, y, h⟩
      · exact (hP0 rfl).elim
      · exact preDivision_eval_zero_of_torsion E h
          ((mem_torsFinset hn _).mp hPT) (fun e => (he e).elim)
    · rw [E.natDegree_preΨ hni, Int.natAbs_natCast,
        if_neg (fun e => he ((Int.even_coe_nat n).mp e))]
      change n ^ 2 - 1 ≤ 2 * Xs.card at hcount
      omega

end
end Dubon2026.SourceEllipticDivisionField
