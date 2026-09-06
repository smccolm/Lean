import GafniTao.EnergyDetectorPoweredFamily

/-!
# Four independent source families consumed by powered GM energy

This module combines four-coordinate real-energy discretization with the
already proved positive-sign powering and the frozen Guth--Maynard
Proposition 11.1.  Unlike the one-shell theorem, all four source lengths,
powers, analytic heights, and cardinality caps may differ.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact finite powered-GM bound for a mixed additive energy of four source
families. -/
theorem finite_mixed_four_symmetric_source_powered_energy_gm_bound
    (epsilon sigma D R : Real) (B : Fin 4 -> Real) (p : Fin 4 -> Nat)
    (N : Fin 4 -> Nat) (a : Fin 4 -> Nat -> Complex)
    (eta : Real) (L : Fin 4 -> Real) (W : Fin 4 -> Finset Real)
    (Z : Fin 4 -> Nat)
    (hepsilon : 0 < epsilon) (hp : forall i, 0 < p i) (heta : 0 < eta)
    (hN : forall i, 0 < N i) (hL : forall i, 0 <= L i)
    (hSep : forall i, IsSeparated 1 (W i))
    (hSymm : forall i t, t ∈ W i -> -R <= t ∧ t <= R)
    (hRB : forall i, 2 * R <= B i)
    (hCoeff : forall i n, n ∈ dyadicInterval (N i) -> ‖a i n‖ <= 1)
    (hLarge : forall i t, t ∈ W i ->
      L i <= ‖sourceDirichletPoly (N i) (a i) t‖)
    (hCard : forall i, (W i).card <= Z i) :
    exists Cp Cgm B0 : Fin 4 -> Real,
      (forall i, 0 < Cp i) ∧ (forall i, 0 < Cgm i) ∧
      (forall i, 4 <= B0 i) ∧
      ((forall i, B0 i <= B i) ->
        (forall i r, r ∈ Finset.range (p i) ->
          (2 ^ r * (N i) ^ (p i) : Real) <= B i) ->
        (forall i r, r ∈ Finset.range (p i) ->
          (B i) ^ (3 / 4 : Real) <=
            (2 ^ r * (N i) ^ (p i) : Real)) ->
        (forall i r, r ∈ Finset.range (p i) ->
          (2 ^ r * (N i) ^ (p i) : Real) ^ sigma <=
            ((L i) ^ (p i) /
              (Cp i *
                ((2 ^ (p i) * (N i) ^ (p i) : Nat) : Real) ^ eta)) /
              (p i)) ->
        exists label : (i : Fin 4) -> Fin 4 -> Fin (p i),
          exists V : Fin 4 -> Fin 4 -> Finset Real,
          (forall i : Fin 4,
            (forall j : Fin 4, V i j ⊆ gmTranslate R (W i)) ∧
            (forall j : Fin 4, (V i j).card <= Z i) ∧
            (forall j : Fin 4, IsSeparated 1 (V i j)) ∧
            (forall j : Fin 4, InBaseInterval (B i) (V i j)) ∧
            (forall j : Fin 4, forall n, n ∈ dyadicInterval
                (2 ^ (label i j).val * (N i) ^ (p i)) ->
              ‖sourceNormalizedFinitePoweredCoeffs (N i) (p i)
                (phaseShiftCoeffs R (a i)) (Cp i) eta n‖ <= 1) ∧
            (forall j : Fin 4, forall t, t ∈ V i j ->
              (2 ^ (label i j).val * (N i) ^ (p i) : Real) ^ sigma <=
                ‖sourceDirichletPoly
                  (2 ^ (label i j).val * (N i) ^ (p i))
                  (sourceNormalizedFinitePoweredCoeffs (N i) (p i)
                    (phaseShiftCoeffs R (a i)) (Cp i) eta) t‖)) ∧
          4 * (MixedApproxAddEnergy D (W 0) (W 1) (W 2) (W 3) : Real) <=
            (doubleFloorDefectWindow D).card *
              ∑ i : Fin 4,
                ((((p i) ^ 4 : Nat) : Real) *
                  (doubleFloorDefectWindow 1).card *
                  (Cgm i * (B i) ^ epsilon *
                    ∑ j : Fin 4,
                      gmEnergyShape sigma (B i)
                        (2 ^ (label i j).val * (N i) ^ (p i))
                        (V i j)))) := by
  obtain ⟨Cp, Cgm, B0, hCp, hCgm, hB0, hConsume⟩ :=
    finite_four_symmetric_source_powered_energy_gm_bound
      epsilon sigma R B p N a eta L W hepsilon hp heta hN hL
      hSep hSymm hRB hCoeff hLarge
  refine ⟨Cp, Cgm, B0, hCp, hCgm, hB0, ?_⟩
  intro hB hUpper hLower hThreshold
  obtain ⟨label, V, hInner⟩ := hConsume hB hUpper hLower hThreshold
  refine ⟨label, V, ?_, ?_⟩
  · intro i
    refine ⟨(hInner i).1, ?_, (hInner i).2.1, (hInner i).2.2.1,
      (hInner i).2.2.2.1, (hInner i).2.2.2.2.1⟩
    intro j
    calc
      (V i j).card <= (gmTranslate R (W i)).card :=
        Finset.card_le_card ((hInner i).1 j)
      _ = (W i).card := card_gmTranslate R (W i)
      _ <= Z i := hCard i
  · have hMixed := four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
      (eta := D) (hSep 0) (hSep 1) (hSep 2) (hSep 3)
    have hEach : forall i : Fin 4,
        4 * (ApproxAddEnergy 1 (W i) : Real) <=
          ((((p i) ^ 4 : Nat) : Real) *
            (doubleFloorDefectWindow 1).card *
            (Cgm i * (B i) ^ epsilon *
              ∑ j : Fin 4,
                gmEnergyShape sigma (B i)
                  (2 ^ (label i j).val * (N i) ^ (p i)) (V i j))) := by
      intro i
      simpa only [Fin.sum_univ_four] using (hInner i).2.2.2.2.2
    calc
      4 * (MixedApproxAddEnergy D (W 0) (W 1) (W 2) (W 3) : Real) <=
          (doubleFloorDefectWindow D).card *
            ∑ i : Fin 4, (ApproxAddEnergy 1 (W i) : Real) := by
        simpa only [Fin.sum_univ_four] using hMixed
      _ <= (doubleFloorDefectWindow D).card *
          ∑ i : Fin 4,
            ((((p i) ^ 4 : Nat) : Real) *
              (doubleFloorDefectWindow 1).card *
              (Cgm i * (B i) ^ epsilon *
                ∑ j : Fin 4,
                  gmEnergyShape sigma (B i)
                    (2 ^ (label i j).val * (N i) ^ (p i)) (V i j))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro i hi
        calc
          (ApproxAddEnergy 1 (W i) : Real) <=
              4 * (ApproxAddEnergy 1 (W i) : Real) := by
            have hnonneg : 0 <= (ApproxAddEnergy 1 (W i) : Real) := by
              positivity
            linarith
          _ <= _ := hEach i

#print axioms finite_mixed_four_symmetric_source_powered_energy_gm_bound

end

end GafniTao
