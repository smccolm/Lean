import Dubon2026.SourceEllipticTorsionCardinality
import Dubon2026.SourceEllipticOddOrbitDistinctness

/-! The actual torsion set and its at-most-two-to-one abscissa map.
These counts prove division-polynomial separability directly for the finite
Galois torsion field, hence the inertia census in DUB-17/18. The count reuses
the local all-order torsion theorem and actual same-abscissa point identity. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open Dubon2026.SourceEllipticTorsion
open Dubon2026.SourceEllipticVelu.OddDiscriminant
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]

theorem card_le_two_mul_card_abscissae {V : WeierstrassCurve Ω}
    (U : Finset V.toAffine.Point) (hU : ∀ P ∈ U, P ≠ 0) :
    U.card ≤ 2 * (U.image xco).card := by
  classical
  refine Finset.card_le_mul_card_image U 2 fun b hb => ?_
  obtain ⟨P₁, hP₁, rfl⟩ := Finset.mem_image.mp hb
  have hs : (U.filter fun P => xco P = xco P₁) ⊆ {P₁, -P₁} := by
    intro P hP
    obtain ⟨hPU, hx⟩ := Finset.mem_filter.mp hP
    rcases eq_or_eq_neg_of_xco_eq (hU P hPU) (hU P₁ hP₁) hx with rfl | rfl <;> simp
  exact (Finset.card_le_card hs).trans Finset.card_le_two

variable (E : WeierstrassCurve F) [E.IsElliptic] [IsAlgClosed Ω]

theorem finite_and_ncard_torsion {n : ℕ} (hn : (n : Ω) ≠ 0) :
    Set.Finite {P : (E.baseChange Ω).toAffine.Point | n • P = 0} ∧
      Set.ncard {P : (E.baseChange Ω).toAffine.Point | n • P = 0} = n ^ 2 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hc : Nat.card {P : (E.baseChange Ω).toAffine.Point // n • P = 0} = n ^ 2 :=
    card_nTorsion E hn
  haveI : Finite ({P : (E.baseChange Ω).toAffine.Point | n • P = 0} : Set _) :=
    Nat.finite_of_card_ne_zero (hc.trans_ne (pow_ne_zero 2 hn0))
  refine ⟨?_, (Nat.card_coe_set_eq _).symm.trans hc⟩
  exact Set.toFinite {P : (E.baseChange Ω).toAffine.Point | n • P = 0}

/-- All actual points killed by the given prime-to-characteristic integer. -/
def torsFinset {n : ℕ} (hn : (n : Ω) ≠ 0) : Finset (E.baseChange Ω).toAffine.Point :=
  (finite_and_ncard_torsion E hn).1.toFinset

variable {E}
theorem mem_torsFinset {n : ℕ} (hn : (n : Ω) ≠ 0)
    (P : (E.baseChange Ω).toAffine.Point) : P ∈ torsFinset E hn ↔ n • P = 0 := by
  rw [torsFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem card_torsFinset {n : ℕ} (hn : (n : Ω) ≠ 0) :
    (torsFinset E hn).card = n ^ 2 := by
  rw [torsFinset, ← Set.ncard_eq_toFinset_card _ (finite_and_ncard_torsion E hn).1]
  exact (finite_and_ncard_torsion E hn).2

end
end Dubon2026.SourceEllipticDivisionField
