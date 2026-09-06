import GafniTao.EnergyDetectorPoweredTranslation

/-!
# Four outer detector classes consumed after powering

The sharp zero detector selects four possibly different source blocks. This
module applies the exact translated powered-energy theorem to all four blocks
without identifying their scales, coefficient sequences, powers, or analytic
heights.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Simultaneous finite powered-energy output for four symmetric large-value
families. All constants are selected before the eventual scale hypotheses. -/
theorem finite_four_symmetric_source_powered_energy_gm_bound
    (epsilon sigma R : Real) (B : Fin 4 → Real) (p : Fin 4 → Nat)
    (N : Fin 4 → Nat) (a : Fin 4 → Nat → Complex)
    (eta : Real) (L : Fin 4 → Real) (W : Fin 4 → Finset Real)
    (hepsilon : 0 < epsilon) (hp : ∀ i, 0 < p i) (heta : 0 < eta)
    (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 ≤ L i)
    (hSep : ∀ i, IsSeparated 1 (W i))
    (hSymm : ∀ i t, t ∈ W i → -R ≤ t ∧ t ≤ R)
    (hRB : ∀ i, 2 * R ≤ B i)
    (hCoeff : ∀ i n, n ∈ dyadicInterval (N i) → ‖a i n‖ ≤ 1)
    (hLarge : ∀ i t, t ∈ W i →
      L i ≤ ‖sourceDirichletPoly (N i) (a i) t‖) :
    ∃ Cp Cgm B0 : Fin 4 → Real,
      (∀ i, 0 < Cp i) ∧ (∀ i, 0 < Cgm i) ∧ (∀ i, 4 ≤ B0 i) ∧
      ((∀ i, B0 i ≤ B i) →
        (∀ i r, r ∈ Finset.range (p i) →
          (2 ^ r * (N i) ^ (p i) : Real) ≤ B i) →
        (∀ i r, r ∈ Finset.range (p i) →
          (B i) ^ (3 / 4 : Real) ≤
            (2 ^ r * (N i) ^ (p i) : Real)) →
        (∀ i r, r ∈ Finset.range (p i) →
          (2 ^ r * (N i) ^ (p i) : Real) ^ sigma ≤
            ((L i) ^ (p i) /
              (Cp i *
                ((2 ^ (p i) * (N i) ^ (p i) : Nat) : Real) ^ eta)) /
              (p i)) →
        ∃ label : (i : Fin 4) → Fin 4 → Fin (p i),
          ∃ V : Fin 4 → Fin 4 → Finset Real,
          ∀ i : Fin 4,
            (∀ j : Fin 4, V i j ⊆ gmTranslate R (W i)) ∧
            (∀ j : Fin 4, IsSeparated 1 (V i j)) ∧
            (∀ j : Fin 4, InBaseInterval (B i) (V i j)) ∧
            (∀ j : Fin 4, ∀ n ∈ dyadicInterval
                (2 ^ (label i j).val * (N i) ^ (p i)),
              ‖sourceNormalizedFinitePoweredCoeffs (N i) (p i)
                (phaseShiftCoeffs R (a i)) (Cp i) eta n‖ ≤ 1) ∧
            (∀ j : Fin 4, ∀ t ∈ V i j,
              (2 ^ (label i j).val * (N i) ^ (p i) : Real) ^ sigma ≤
                ‖sourceDirichletPoly
                  (2 ^ (label i j).val * (N i) ^ (p i))
                  (sourceNormalizedFinitePoweredCoeffs (N i) (p i)
                    (phaseShiftCoeffs R (a i)) (Cp i) eta) t‖) ∧
            4 * (ApproxAddEnergy 1 (W i) : Real) ≤
              (((p i) ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
                (Cgm i * (B i) ^ epsilon *
                  (gmEnergyShape sigma (B i)
                      (2 ^ (label i 0).val * (N i) ^ (p i)) (V i 0) +
                    gmEnergyShape sigma (B i)
                      (2 ^ (label i 1).val * (N i) ^ (p i)) (V i 1) +
                    gmEnergyShape sigma (B i)
                      (2 ^ (label i 2).val * (N i) ^ (p i)) (V i 2) +
                    gmEnergyShape sigma (B i)
                      (2 ^ (label i 3).val * (N i) ^ (p i)) (V i 3)))) := by
  have hOut (i : Fin 4) :=
    finite_symmetric_source_powered_energy_gm_bound
      epsilon sigma R (B i) (N i) (p i) (a i) eta (L i) (W i)
      hepsilon (hN i) (hp i) heta (hL i) (hSep i) (hSymm i)
      (hRB i) (hCoeff i) (hLarge i)
  let Cp : Fin 4 → Real := fun i => Classical.choose (hOut i)
  let Cgm : Fin 4 → Real := fun i =>
    Classical.choose (Classical.choose_spec (hOut i))
  let B0 : Fin 4 → Real := fun i =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hOut i)))
  have hSpec (i : Fin 4) :=
    Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (hOut i)))
  refine ⟨Cp, Cgm, B0, fun i => (hSpec i).1,
    fun i => (hSpec i).2.1, fun i => (hSpec i).2.2.1, ?_⟩
  intro hB hUpper hLower hThreshold
  have hSelected (i : Fin 4) :=
    (hSpec i).2.2.2 (hB i) (hUpper i) (hLower i) (hThreshold i)
  let label : (i : Fin 4) → Fin 4 → Fin (p i) := fun i =>
    Classical.choose (hSelected i)
  let V : Fin 4 → Fin 4 → Finset Real := fun i =>
    Classical.choose (Classical.choose_spec (hSelected i))
  refine ⟨label, V, ?_⟩
  intro i
  exact Classical.choose_spec (Classical.choose_spec (hSelected i))

#print axioms finite_four_symmetric_source_powered_energy_gm_bound

end

end GafniTao
