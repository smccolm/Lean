import GafniTao.EnergyDetectorPoweredGM

/-!
# Symmetric-shell translation followed by exact powered energy

This module closes the convention boundary between the signed shell detector
and the frozen Guth--Maynard energy theorem. The ordinate translation and
coefficient phase twist are exact, and approximate additive energy is
transported by equality.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- A unit-coefficient positive-sign polynomial on a symmetric interval can
be translated, exactly powered, four-coordinate colored, and consumed by
Guth--Maynard Proposition 11.1. -/
theorem finite_symmetric_source_powered_energy_gm_bound
    (epsilon sigma R B : Real) (N p : Nat) (a : Nat → Complex)
    (eta L : Real) (W : Finset Real)
    (hepsilon : 0 < epsilon) (hN : 0 < N) (hp : 0 < p)
    (heta : 0 < eta) (hL : 0 ≤ L)
    (hSep : IsSeparated 1 W)
    (hSymm : ∀ t ∈ W, -R ≤ t ∧ t ≤ R)
    (hRB : 2 * R ≤ B)
    (hCoeff : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hLarge : ∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖) :
    ∃ Cp Cgm B0 : Real, 0 < Cp ∧ 0 < Cgm ∧ 4 ≤ B0 ∧
      (B0 ≤ B →
        (∀ r ∈ Finset.range p, (2 ^ r * N ^ p : Real) ≤ B) →
        (∀ r ∈ Finset.range p,
          B ^ (3 / 4 : Real) ≤ (2 ^ r * N ^ p : Real)) →
        (∀ r ∈ Finset.range p,
          (2 ^ r * N ^ p : Real) ^ sigma ≤
            (L ^ p /
              (Cp * ((2 ^ p * N ^ p : Nat) : Real) ^ eta)) / p) →
        ∃ label : Fin 4 → Fin p, ∃ Wi : Fin 4 → Finset Real,
          (∀ i : Fin 4, Wi i ⊆ gmTranslate R W) ∧
          (∀ i : Fin 4, IsSeparated 1 (Wi i)) ∧
          (∀ i : Fin 4, InBaseInterval B (Wi i)) ∧
          (∀ i : Fin 4, ∀ n ∈ dyadicInterval
              (2 ^ (label i).val * N ^ p),
            ‖sourceNormalizedFinitePoweredCoeffs N p
              (phaseShiftCoeffs R a) Cp eta n‖ ≤ 1) ∧
          (∀ i : Fin 4, ∀ t ∈ Wi i,
            (2 ^ (label i).val * N ^ p : Real) ^ sigma ≤
              ‖sourceDirichletPoly (2 ^ (label i).val * N ^ p)
                (sourceNormalizedFinitePoweredCoeffs N p
                  (phaseShiftCoeffs R a) Cp eta) t‖) ∧
          4 * (ApproxAddEnergy 1 W : Real) ≤
            ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
              (Cgm * B ^ epsilon *
                (gmEnergyShape sigma B
                    (2 ^ (label 0).val * N ^ p) (Wi 0) +
                  gmEnergyShape sigma B
                    (2 ^ (label 1).val * N ^ p) (Wi 1) +
                  gmEnergyShape sigma B
                    (2 ^ (label 2).val * N ^ p) (Wi 2) +
                  gmEnergyShape sigma B
                    (2 ^ (label 3).val * N ^ p) (Wi 3)))) := by
  let aT : Nat → Complex := phaseShiftCoeffs R a
  have hCoeffT : ∀ n ∈ dyadicInterval N, ‖aT n‖ ≤ 1 := by
    exact norm_phaseShiftCoeffs_le_one_on N a R hCoeff
  have hCoeffConj : ∀ n ∈ dyadicInterval N,
      ‖conjugateCoeffs aT n‖ ≤ 1 := by
    intro n hn
    rw [norm_conjugateCoeffs]
    exact hCoeffT n hn
  obtain ⟨Cp, hCp, hPowAll⟩ := finitePowCoeff_bound_uniform p eta heta
  have hPow : ∀ m : Nat, 0 < m →
      ‖finitePowCoeff N p (conjugateCoeffs aT) m‖ ≤
        Cp * (m : Real) ^ eta :=
    hPowAll N (conjugateCoeffs aT) hCoeffConj
  have hSepT : IsSeparated 1 (gmTranslate R W) :=
    isSeparated_gmTranslate 1 R W hSep
  have hBaseT : InBaseInterval B (gmTranslate R W) := by
    intro t ht
    have htBase := inBaseInterval_gmTranslate_of_symmetric R W hSymm t ht
    exact ⟨htBase.1, htBase.2.trans hRB⟩
  have hLargeT : ∀ t ∈ gmTranslate R W,
      L ≤ ‖sourceDirichletPoly N aT t‖ :=
    sourceDirichletPoly_large_on_gmTranslate N a R L W hLarge
  obtain ⟨Cgm, B0, hCgm, hB0, hConsume⟩ :=
    finite_source_powered_energy_gm_bound epsilon sigma B
      N p aT Cp eta L (gmTranslate R W) hepsilon hN hp hCp heta hL
      hSepT hBaseT hPow hLargeT
  refine ⟨Cp, Cgm, B0, hCp, hCgm, hB0, ?_⟩
  intro hB hUpper hLower hThreshold
  obtain ⟨label, Wi, hSubset, hSepWi, hBaseWi, hUnit, hGMLarge, hEnergy⟩ :=
    hConsume hB hUpper hLower hThreshold
  refine ⟨label, Wi, hSubset, hSepWi, hBaseWi, hUnit, hGMLarge, ?_⟩
  rw [← approxAddEnergy_translate 1 R W]
  exact hEnergy

#print axioms finite_symmetric_source_powered_energy_gm_bound

end

end GafniTao
