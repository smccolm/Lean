import TaoTrudgianYang2025.BourgainBandSelection

/-!
# Positive actual zeta-band selection

Uniform constants come from the proved zeta growth and fourth moment.
The floor is chosen from the actual local mass, so the low contribution
is absorbed without an extra analytic assumption.
-/

open MeasureTheory Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- Positive local zeta-square mass selects a genuine positive-measure
amplitude band. Its finite logarithmic count, both occupancy bounds, and
its genuine fourth-moment measure estimate remain explicit. -/
theorem bourgainZetaBand_positive_selection {η : ℝ} (hη : 0 < η) :
    ∃ B C T₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (D : Finset ℤ) (H T : ℝ), 0 < H → T₀ ≤ T →
        (∀ ℓ ∈ D, -T+H ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ T-H) →
        let L := ∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ
        0 < L →
        let a := Real.sqrt (L/(4*H*(D.card : ℝ)))
        let J := bourgainZetaBandCount B T a
        ∃ j ∈ Finset.range J,
          let V := a*(2 : ℝ)^j
          0 < a ∧ 0 < V ∧ 0 < bourgainZetaBandMass D H T V ∧
          0 < volume.real (bourgainZetaBand T V) ∧
          L ≤ 2*(J : ℝ)*(2*V)^2*bourgainZetaBandMass D H T V ∧
          V^4*volume.real (bourgainZetaBand T V) ≤ C*T^(1+η) ∧
          bourgainZetaBandMass D H T V ≤ 2*H*(D.card : ℝ) ∧
          bourgainZetaBandMass D H T V ≤
            (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V) := by
  obtain ⟨B, hB, hterminal⟩ := exists_bourgainZetaBand_terminal
  obtain ⟨C, T₀, hC, hT₀, hfourth⟩ := bourgainZetaBand_fourth_bound hη
  refine ⟨B, C, T₀, hB, hC, hT₀, ?_⟩
  intro D H T hH hT hrange L hL
  have hD : 0 < (D.card : ℝ) := by
    have hne : D.Nonempty := by
      by_contra h
      have he : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [L, he] at hL
    exact_mod_cast Finset.card_pos.mpr hne
  let a := Real.sqrt (L/(4*H*(D.card : ℝ)))
  let J := bourgainZetaBandCount B T a
  obtain ⟨ha, hhalf⟩ := bourgainZetaBand_half_floor hL hH hD
  obtain ⟨j, hj, hm⟩ := bourgainZetaBand_select D hH.le
    (bourgainZetaBandCount_pos B T a) hrange (hterminal T a ha)
  let V := a*(2 : ℝ)^j
  have hV : 0 < V := mul_pos ha (by positivity)
  have hbound : L ≤ 2*(J : ℝ)*(2*V)^2*bourgainZetaBandMass D H T V := by
    change L ≤ 2*H*a^2*(D.card : ℝ)+(J : ℝ)*(2*V)^2*bourgainZetaBandMass D H T V at hm
    rw [hhalf] at hm
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
  exact ⟨j, hj, ha, hV, hmass, hpositive, hbound, hfourth T V hT hV.le,
    (bourgainZetaBandMass_bounds D hH.le T V).2, hmeasure⟩

end TaoTrudgianYang2025
