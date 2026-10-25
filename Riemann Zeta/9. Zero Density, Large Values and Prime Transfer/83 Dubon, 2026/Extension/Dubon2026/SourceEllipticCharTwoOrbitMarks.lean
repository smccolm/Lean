import Dubon2026.SourceEllipticCharTwoMarkedElements
import Dubon2026.SourceEllipticCharTwoCyclicOrbits
import Dubon2026.SourceOrderTwelveTransitiveMarks

/-! DUB-17/18 -> weighted exceptional census. Instantiate the audited
order-twelve marks on the actual sign quotient and each actual cyclic-subgroup
orbit. Group order, exponent, and marked-element hypotheses are all proved. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve MulAction
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [CharP K 2] [IsAlgClosed K]
attribute [local instance] charTwoSignSubgroup_normal

theorem cyclic_orbit_marks (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    {N : ℕ} (H : CyclicSubgroup K N) :
    let O := orbit ((stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup) H
    let e := Nat.card O
    (e = 1 ∨ e = 3 ∨ e = 4 ∨ e = 6 ∨ e = 12) ∧
    Nat.card (fixedBy O (charTwoSignProjection (quarticStabilizer ω hω))) =
      (if e = 1 then 1 else 0) + (if e = 3 then 3 else 0) + (if e = 6 then 2 else 0) ∧
    Nat.card (fixedBy O (charTwoSignProjection (cubicStabilizer ω hω))) =
      (if e = 1 then 1 else 0) + (if e = 4 then 1 else 0) := by
  let G := (stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup
  have hG : Nat.card G = 12 := charTwoSignQuotient_card (K := K)
  haveI : Finite G := Nat.finite_of_card_ne_zero (hG.trans_ne (by decide))
  haveI : Nonempty (orbit G H) := ⟨⟨H, mem_orbit_self H⟩⟩
  obtain ⟨hs, ha, hb⟩ := SourceOrderTwelve.marks (G := G) (orbit G H)
    hG (charTwoSignQuotient_square_or_cube (K := K))
  obtain ⟨a1, a3, a4, a6, a12⟩ := ha _ (signProjection_quartic_ne_one ω hω)
    (signProjection_quartic_square ω hω)
  obtain ⟨b1, b3, b4, b6, b12⟩ := hb _ (signProjection_cubic_ne_one ω hω)
    (signProjection_cubic_cube ω hω)
  refine ⟨hs, ?_, ?_⟩
  · rcases hs with h | h | h | h | h
    · rw [a1 h, h]; norm_num
    · rw [a3 h, h]; norm_num
    · rw [a4 h, h]; norm_num
    · rw [a6 h, h]; norm_num
    · rw [a12 h, h]; norm_num
  · rcases hs with h | h | h | h | h
    · rw [b1 h, h]; norm_num
    · rw [b3 h, h]; norm_num
    · rw [b4 h, h]; norm_num
    · rw [b6 h, h]; norm_num
    · rw [b12 h, h]; norm_num

end
end Dubon2026.SourceEllipticCharTwo
