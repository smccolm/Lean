import GafniTao.HeathBrownPoweredCardinality

/-!
# Symmetric-shell form of powered Heath--Brown energy

This closes the remaining convention boundary for the energy-producing
`p`-th power.  The source family is translated exactly before powering and
the resulting additive-energy estimate is transported back by equality.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact symmetric-interval powered Heath--Brown consumer. -/
theorem finite_symmetric_source_powered_energy_heathBrown_native
    (epsilon B R : Real) (N p : Nat) (a : Nat → Complex)
    (eta L : Real) (W : Finset Real)
    (hepsilon : 0 < epsilon) (hN : 0 < N) (hp : 0 < p)
    (heta : 0 < eta) (hL : 0 < L)
    (hSep : IsSeparated 1 W)
    (hSymm : ∀ t ∈ W, -R ≤ t ∧ t ≤ R)
    (hRB : 2 * R ≤ B)
    (hCoeff : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hLarge : ∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖) :
    ∃ Cp C0 C2 C4 B0 : Real,
      0 < Cp ∧ 0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 ≤ B0 ∧
      (B0 ≤ B →
        (∀ r ∈ Finset.range p, (2 ^ r * N ^ p : Real) ≤ B) →
        ∃ label : Fin 4 → Fin p, ∃ Wi : Fin 4 → Finset Real,
          (∀ i : Fin 4, Wi i ⊆ gmTranslate R W) ∧
          (∀ i : Fin 4, IsSeparated 1 (Wi i)) ∧
          (∀ i : Fin 4, InBaseInterval B (Wi i)) ∧
          (∀ i : Fin 4, ∀ n ∈ dyadicInterval
              (2 ^ (label i).val * N ^ p),
            ‖sourceNormalizedFinitePoweredCoeffs N p
              (phaseShiftCoeffs R a) Cp eta n‖ ≤ 1) ∧
          (∀ i : Fin 4, ∀ t ∈ Wi i,
            heathBrownPoweredThreshold N p L Cp eta ≤
              ‖sourceDirichletPoly (2 ^ (label i).val * N ^ p)
                (sourceNormalizedFinitePoweredCoeffs N p
                  (phaseShiftCoeffs R a) Cp eta) t‖) ∧
          4 * (ApproxAddEnergy 1 W : Real) ≤
            ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
              (∑ i : Fin 4,
                heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
                  (heathBrownPoweredThreshold N p L Cp eta)
                  (2 ^ (label i).val * N ^ p) (Wi i))) := by
  let aT : Nat → Complex := phaseShiftCoeffs R a
  have hCoeffT : ∀ n ∈ dyadicInterval N, ‖aT n‖ ≤ 1 :=
    norm_phaseShiftCoeffs_le_one_on N a R hCoeff
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
  obtain ⟨C0, C2, C4, B0, hC0, hC2, hC4, hB0, hConsume⟩ :=
    finite_source_powered_energy_heathBrown_native epsilon B
      N p aT Cp eta L (gmTranslate R W) hepsilon hN hp hCp heta hL
      hSepT hBaseT hPow hLargeT
  refine ⟨Cp, C0, C2, C4, B0, hCp, hC0, hC2, hC4, hB0, ?_⟩
  intro hB hUpper
  obtain ⟨label, Wi, hSubset, hSepWi, hBaseWi, hUnit, hPowered, hEnergy⟩ :=
    hConsume hB hUpper
  refine ⟨label, Wi, hSubset, hSepWi, hBaseWi, hUnit, hPowered, ?_⟩
  rw [← approxAddEnergy_translate 1 R W]
  exact hEnergy

#print axioms finite_symmetric_source_powered_energy_heathBrown_native

end


end GafniTao
