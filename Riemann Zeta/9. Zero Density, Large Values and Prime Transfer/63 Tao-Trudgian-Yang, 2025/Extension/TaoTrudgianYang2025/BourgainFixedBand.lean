import TaoTrudgianYang2025.BourgainSharedFloor

/-!
# Actual zeta-band selection on a supplied common floor

Uniform constants come from the proved zeta growth and fourth moment.
A common positive floor is retained. Its low-value mass condition is
explicit here and is derived from actual pattern bounds by the consumer.
-/

open MeasureTheory Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- Positive local zeta-square mass selects a genuine positive-measure
amplitude band. Its finite logarithmic count, both occupancy bounds, and
its genuine fourth-moment measure estimate remain explicit. -/
theorem bourgainZetaBand_fixed_floor_selection {η : ℝ} (hη : 0 < η) :
    ∃ B C T₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (D : Finset ℤ) (H T a : ℝ), 0 < H → 0 < a → T₀ ≤ T →
        (∀ ℓ ∈ D, -T+H ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ T-H) →
        let L := ∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ
        2*(2*H*a^2*(D.card : ℝ)) < L →
        let J := bourgainZetaBandCount B T a
        ∃ j ∈ Finset.range J,
          let V := a*(2 : ℝ)^j
          0 < V ∧ 0 < bourgainZetaBandMass D H T V ∧
          0 < volume.real (bourgainZetaBand T V) ∧
          L ≤ 2*(J : ℝ)*(2*V)^2*bourgainZetaBandMass D H T V ∧
          V^4*volume.real (bourgainZetaBand T V) ≤ C*T^(1+η) ∧
          bourgainZetaBandMass D H T V ≤ 2*H*(D.card : ℝ) ∧
          bourgainZetaBandMass D H T V ≤
            (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V) := by
  obtain ⟨B, hB, hterminal⟩ := exists_bourgainZetaBand_terminal
  obtain ⟨C, T₀, hC, hT₀, hfourth⟩ := bourgainZetaBand_fourth_bound hη
  refine ⟨B, C, T₀, hB, hC, hT₀, ?_⟩
  intro D H T a hH ha hT hrange L hlow
  have hL : 0 < L := lt_of_le_of_lt (by positivity) hlow
  let J := bourgainZetaBandCount B T a
  obtain ⟨j, hj, hm⟩ := bourgainZetaBand_select D hH.le
    (bourgainZetaBandCount_pos B T a) hrange (hterminal T a ha)
  let V := a*(2 : ℝ)^j
  have hV : 0 < V := mul_pos ha (by positivity)
  have hbound : L ≤ 2*(J : ℝ)*(2*V)^2*bourgainZetaBandMass D H T V := by
    change L ≤ 2*H*a^2*(D.card : ℝ)+(J : ℝ)*(2*V)^2*bourgainZetaBandMass D H T V at hm
    linarith
  have hmass : 0 < bourgainZetaBandMass D H T V := by
    by_contra h
    have hn := mul_nonpos_of_nonneg_of_nonpos
      (by positivity : 0 ≤ 2*(J : ℝ)*(2*V)^2) (le_of_not_gt h)
    linarith
  have hmeasure := bourgainZetaBandMass_le_measure D hH.le T V
  have hpositive : 0 < volume.real (bourgainZetaBand T V) := by
    by_contra h
    have hn := mul_nonpos_of_nonneg_of_nonpos
      (by positivity : (0 : ℝ) ≤ (2*Nat.ceil H+1 : ℕ)) (le_of_not_gt h)
    linarith
  exact ⟨j, hj, hV, hmass, hpositive, hbound, hfourth T V hT hV.le,
    (bourgainZetaBandMass_bounds D hH.le T V).2, hmeasure⟩

end TaoTrudgianYang2025
