import Dubon2026.SourceEllipticStabilizerInvariantBounds
import Dubon2026.SourceEllipticPositiveCharacteristicCocycle

/-! The actual stabilizer bounds needed in the source genus comparison:
six at j = 0, four at j = 1728 and two elsewhere in characteristic at
least five. The units are derived from the characteristic. This closes
the stabilizer-size obligation for the DUB-17/18 inertia-image argument;
ramification orders and equality with the inertia image still remain. -/
namespace Dubon2026.SourceEllipticStabilizer
open WeierstrassCurve
noncomputable section

theorem stabilizer_bounds_of_five_le
    (K : Type*) [Field K] (p : ℕ) [CharP K p] (hp : 5 ≤ p)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Finite (MulAction.stabilizer (VariableChange K) W) ∧
      (W.j = 0 → Nat.card (MulAction.stabilizer (VariableChange K) W) ≤ 6) ∧
      (W.j = 1728 → Nat.card (MulAction.stabilizer (VariableChange K) W) ≤ 4) ∧
      (W.j ≠ 0 → W.j ≠ 1728 → Nat.card (MulAction.stabilizer (VariableChange K) W) ≤ 2) := by
  obtain ⟨h2u, h3u⟩ := SourceEllipticReduction.isUnit_two_three_of_five_le K K p hp
  have h2 : (2 : K) ≠ 0 := h2u.ne_zero
  have h3 : (3 : K) ≠ 0 := h3u.ne_zero
  have h1728 : (1728 : K) ≠ 0 := by
    rw [show (1728 : K) = 2 ^ 6 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  have hb0 (hj : W.j = 0) := stabilizer_card_le_six W h2 h3 (by rw [hj]; exact h1728.symm)
  have hb1728 (hj : W.j = 1728) := stabilizer_card_le_four W h2 h3 (by rw [hj]; exact h1728)
  have hbother := stabilizer_card_le_two W h2 h3
  refine ⟨?_, fun hj => (hb0 hj).2, fun hj => (hb1728 hj).2,
    fun hj0 hj1728 => (hbother hj0 hj1728).2⟩
  by_cases hj0 : W.j = 0
  · exact (hb0 hj0).1
  · exact (stabilizer_card_le_four W h2 h3 hj0).1

end
end Dubon2026.SourceEllipticStabilizer
