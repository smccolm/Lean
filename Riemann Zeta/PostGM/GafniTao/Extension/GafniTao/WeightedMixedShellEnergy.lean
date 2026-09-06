import GafniTao.WeightedSubfamilyEnergy

/-!
# Mixed multiplicity-weighted energy and shell localization

A resonant four-zero tuple need not have all four ordinates in one dyadic
shell.  This file supplies the exact four-coordinate pigeonhole used before
the shell detectors are applied.  Each coordinate may select a different
shell, and analytic multiplicities remain product weights throughout.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Tolerance-`eta` mixed quadruples from four complex subfamilies. -/
noncomputable def resonantQuadruplesOnFour
    (S0 S1 S2 S3 : Finset Complex) (eta : Real) :
    Finset ((Complex × Complex) × (Complex × Complex)) :=
  (quadrupleProductOf S0 S1 S2 S3).filter fun q =>
    |q.1.1.im + q.1.2.im - q.2.1.im - q.2.2.im| ≤ eta

/-- Product-weighted mixed approximate additive energy. -/
noncomputable def weightedMixedAdditiveEnergyOn
    (S0 S1 S2 S3 : Finset Complex) (weight : Complex → Nat)
    (eta : Real) : Nat :=
  ∑ q ∈ resonantQuadruplesOnFour S0 S1 S2 S3 eta,
    weightedQuadruple weight q

theorem mem_resonantQuadruplesOnFour
    {S0 S1 S2 S3 : Finset Complex} {eta : Real}
    {q : (Complex × Complex) × (Complex × Complex)} :
    q ∈ resonantQuadruplesOnFour S0 S1 S2 S3 eta ↔
      q.1.1 ∈ S0 ∧ q.1.2 ∈ S1 ∧ q.2.1 ∈ S2 ∧ q.2.2 ∈ S3 ∧
        |q.1.1.im + q.1.2.im - q.2.1.im - q.2.2.im| ≤ eta := by
  classical
  simp [resonantQuadruplesOnFour, quadrupleProductOf, and_assoc]

/-- Coloring the four coordinates of the literal resonant zero family
selects four possibly different subfamilies and loses exactly the fourth
power of the number of colors. -/
theorem exists_zero_energy_mixed_color_fiber
    {Kappa : Type*} [Fintype Kappa] [DecidableEq Kappa] [Nonempty Kappa]
    (sigma T : Real) (color : Complex → Kappa) :
    ∃ label : Fin 4 → Kappa,
      let S := fun i : Fin 4 =>
        (zeroSet sigma T).filter (fun rho => color rho = label i)
      zeroAdditiveEnergyCount sigma T ≤
        (Fintype.card Kappa) ^ 4 *
          weightedMixedAdditiveEnergyOn
            (S 0) (S 1) (S 2) (S 3) zeroMultiplicity 1 := by
  classical
  let colorQ : ((Complex × Complex) × (Complex × Complex)) →
      Fin 4 → Kappa := fun q i => color (complexQuadrupleCoord i q)
  obtain ⟨label, hlabel⟩ :=
    exists_four_coordinate_weighted_color_fiber_type
      (resonantZeroQuadruples sigma T) zeroQuadrupleWeight colorQ
  let S := fun i : Fin 4 =>
    (zeroSet sigma T).filter (fun rho => color rho = label i)
  refine ⟨label, ?_⟩
  dsimp only
  calc
    zeroAdditiveEnergyCount sigma T =
        ∑ q ∈ resonantZeroQuadruples sigma T,
          zeroQuadrupleWeight q := rfl
    _ ≤ (Fintype.card Kappa) ^ 4 *
        ∑ q ∈ (resonantZeroQuadruples sigma T).filter
          (fun q => colorQ q = label), zeroQuadrupleWeight q := hlabel
    _ = (Fintype.card Kappa) ^ 4 *
        weightedMixedAdditiveEnergyOn
          (S 0) (S 1) (S 2) (S 3) zeroMultiplicity 1 := by
      congr 1
      unfold weightedMixedAdditiveEnergyOn
      apply Finset.sum_congr
      · ext q
        rw [Finset.mem_filter, mem_resonantZeroQuadruples,
          mem_resonantQuadruplesOnFour]
        simp only [S, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hq0, hq1, hq2, hq3, hres⟩, hcolor⟩
          have hc0 := congrFun hcolor 0
          have hc1 := congrFun hcolor 1
          have hc2 := congrFun hcolor 2
          have hc3 := congrFun hcolor 3
          simp only [colorQ, complexQuadrupleCoord] at hc0 hc1 hc2 hc3
          exact ⟨⟨hq0, hc0⟩, ⟨hq1, hc1⟩, ⟨hq2, hc2⟩,
            ⟨hq3, hc3⟩, hres⟩
        · rintro ⟨⟨hq0, hc0⟩, ⟨hq1, hc1⟩, ⟨hq2, hc2⟩,
            ⟨hq3, hc3⟩, hres⟩
          refine ⟨⟨hq0, hq1, hq2, hq3, hres⟩, ?_⟩
          funext i
          fin_cases i
          · exact hc0
          · exact hc1
          · exact hc2
          · exact hc3
      · intro q hq
        rfl

/-- Mixed weighted energy is monotone in each of its four source families. -/
theorem weightedMixedAdditiveEnergyOn_mono
    {A0 A1 A2 A3 B0 B1 B2 B3 : Finset Complex}
    (h0 : A0 ⊆ B0) (h1 : A1 ⊆ B1) (h2 : A2 ⊆ B2) (h3 : A3 ⊆ B3)
    (weight : Complex → Nat) (eta : Real) :
    weightedMixedAdditiveEnergyOn A0 A1 A2 A3 weight eta ≤
      weightedMixedAdditiveEnergyOn B0 B1 B2 B3 weight eta := by
  unfold weightedMixedAdditiveEnergyOn
  apply Finset.sum_le_sum_of_subset
  intro q hq
  rw [mem_resonantQuadruplesOnFour] at hq ⊢
  exact ⟨h0 hq.1, h1 hq.2.1, h2 hq.2.2.1, h3 hq.2.2.2.1,
    hq.2.2.2.2⟩

/-- Exact four-coordinate localization to a finite cover of the symmetric
zero set.  The selected four cover members may differ. -/
theorem exists_zero_energy_mixed_cover
    (sigma T : Real) (m : Nat) (hm : 0 < m)
    (shell : Fin m → Finset Complex)
    (hcover : ∀ rho, rho ∈ zeroSet sigma T → ∃ i, rho ∈ shell i) :
    ∃ label : Fin 4 → Fin m,
      zeroAdditiveEnergyCount sigma T ≤ m ^ 4 *
        weightedMixedAdditiveEnergyOn
          (shell (label 0)) (shell (label 1))
          (shell (label 2)) (shell (label 3)) zeroMultiplicity 1 := by
  classical
  let color : Complex → Fin m := fun rho =>
    if h : rho ∈ zeroSet sigma T then Classical.choose (hcover rho h)
    else ⟨0, hm⟩
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨label, hlabel⟩ :=
    exists_zero_energy_mixed_color_fiber sigma T color
  let S := fun i : Fin 4 =>
    (zeroSet sigma T).filter (fun rho => color rho = label i)
  have hsub (i : Fin 4) : S i ⊆ shell (label i) := by
    intro rho hrho
    rw [Finset.mem_filter] at hrho
    have hchoice := Classical.choose_spec (hcover rho hrho.1)
    rw [← hrho.2]
    simpa only [color, dif_pos hrho.1] using hchoice
  have hmono := weightedMixedAdditiveEnergyOn_mono
    (hsub 0) (hsub 1) (hsub 2) (hsub 3) zeroMultiplicity 1
  refine ⟨label, ?_⟩
  dsimp only at hlabel ⊢
  exact hlabel.trans (by
    simpa only [Fintype.card_fin] using Nat.mul_le_mul_left (m ^ 4) hmono)

#print axioms resonantQuadruplesOnFour
#print axioms weightedMixedAdditiveEnergyOn
#print axioms mem_resonantQuadruplesOnFour
#print axioms exists_zero_energy_mixed_color_fiber
#print axioms weightedMixedAdditiveEnergyOn_mono
#print axioms exists_zero_energy_mixed_cover

end

end GafniTao
