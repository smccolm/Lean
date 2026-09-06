import GafniTao.HeathBrownPoweredSymmetric
import GafniTao.HeathBrownFiniteMonotone

/-!
# Uniform powered Heath--Brown energy

The finite Heath--Brown relation supplies constants depending only on the
epsilon budget.  This module preserves that quantifier order through exact
powering and ordinate translation.  In particular, the returned object has
already consumed the common height cutoff; it is not a packet whose useful
conclusion remains conditional on a hidden, scale-dependent threshold.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- A symmetric powered-energy output after the uniform Heath--Brown cutoff
has been discharged. -/
structure HeathBrownUniformPoweredEnergyOutput
    (epsilon B R : Real) (N p : Nat) (eta L : Real)
    (W : Finset Real) (a : Nat → Complex) (C0 C2 C4 : Real) where
  Cp : Real
  hCp : 0 < Cp
  label : Fin 4 → Fin p
  Wi : Fin 4 → Finset Real
  hSubset : ∀ i : Fin 4, Wi i ⊆ gmTranslate R W
  hSeparated : ∀ i : Fin 4, IsSeparated 1 (Wi i)
  hBase : ∀ i : Fin 4, InBaseInterval B (Wi i)
  hUnit : ∀ i : Fin 4, ∀ n ∈ dyadicInterval
      (2 ^ (label i).val * N ^ p),
    ‖sourceNormalizedFinitePoweredCoeffs N p
      (phaseShiftCoeffs R a) Cp eta n‖ ≤ 1
  hLarge : ∀ i : Fin 4, ∀ t ∈ Wi i,
    heathBrownPoweredThreshold N p L Cp eta ≤
      ‖sourceDirichletPoly (2 ^ (label i).val * N ^ p)
        (sourceNormalizedFinitePoweredCoeffs N p
          (phaseShiftCoeffs R a) Cp eta) t‖
  hEnergy : 4 * (ApproxAddEnergy 1 W : Real) ≤
    ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
      (∑ i : Fin 4,
        heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
          (heathBrownPoweredThreshold N p L Cp eta)
          (2 ^ (label i).val * N ^ p) (Wi i))

/-- The powered-energy constants and height cutoff are uniform in every
physical parameter.  This is the quantifier order required by the eventual
zero-energy argument. -/
theorem finite_symmetric_source_powered_energy_heathBrown_uniform_native
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ C0 C2 C4 B0 : Real,
      0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 ≤ B0 ∧
      ∀ (B R : Real) (N p : Nat) (a : Nat → Complex)
          (eta L : Real) (W : Finset Real),
        0 < N → 0 < p → 0 < eta → 0 < L →
        IsSeparated 1 W →
        (∀ t ∈ W, -R ≤ t ∧ t ≤ R) →
        2 * R ≤ B →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        (∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖) →
        B0 ≤ B →
        (∀ r ∈ Finset.range p, (2 ^ r * N ^ p : Real) ≤ B) →
        Nonempty (HeathBrownUniformPoweredEnergyOutput
          epsilon B R N p eta L W a C0 C2 C4) := by
  obtain ⟨C0, C2, C4, B0, hC0, hC2, hC4, hB0, hHB⟩ :=
    heathBrownFiniteEnergyRelation_native epsilon hepsilon
  refine ⟨C0, C2, C4, B0, hC0, hC2, hC4, hB0, ?_⟩
  intro B R N p a eta L W hN hp heta hL hSep hSymm hRB
    hCoeff hLarge hCutoff hUpper
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
  obtain ⟨label, Wi, hSubset, hSepWi, hBaseWi, hUnit, hPowered,
      hEnergy⟩ :=
    finite_source_powered_energy_heathBrown_of_relation
      epsilon B N p aT Cp eta L (gmTranslate R W) C0 C2 C4 B0
      hN hp hCp heta hL hC0 hB0 hHB hSepT hBaseT hPow hLargeT
      hCutoff hUpper
  refine ⟨⟨Cp, hCp, label, Wi, hSubset, hSepWi, hBaseWi, hUnit,
    hPowered, ?_⟩⟩
  rw [← approxAddEnergy_translate 1 R W]
  exact hEnergy

/-- Common-length form of a powered output whose uniform cutoff has already
been consumed. -/
theorem HeathBrownUniformPoweredEnergyOutput.energy_le_common_power
    {epsilon B R : Real} {N p : Nat} {eta L : Real}
    {W : Finset Real} {a : Nat → Complex} {C0 C2 C4 : Real}
    (output : HeathBrownUniformPoweredEnergyOutput
      epsilon B R N p eta L W a C0 C2 C4)
    (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2) (hC4 : 0 ≤ C4) (hB : 0 ≤ B) :
    4 * (ApproxAddEnergy 1 W : Real) ≤
      ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
        (4 * heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
          (heathBrownPoweredThreshold N p L output.Cp eta)
          (2 ^ p * N ^ p) W) := by
  have hEach : ∀ i : Fin 4,
      heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
          (heathBrownPoweredThreshold N p L output.Cp eta)
          (2 ^ (output.label i).val * N ^ p) (output.Wi i) ≤
        heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
          (heathBrownPoweredThreshold N p L output.Cp eta)
          (2 ^ p * N ^ p) W := by
    intro i
    have hFactor : 2 ^ (output.label i).val ≤ 2 ^ p :=
      Nat.pow_le_pow_right (by omega) (output.label i).isLt.le
    have hLength : 2 ^ (output.label i).val * N ^ p ≤ 2 ^ p * N ^ p :=
      Nat.mul_le_mul_right (N ^ p) hFactor
    have hCardT : (output.Wi i).card ≤ (gmTranslate R W).card :=
      Finset.card_le_card (output.hSubset i)
    have hEnergyMono : ApproxAddEnergy 1 (output.Wi i) ≤
        ApproxAddEnergy 1 (gmTranslate R W) :=
      approxAddEnergy_mono_family (output.hSubset i)
    have hMono := heathBrownFiniteFamilyBound_mono
      (epsilon := epsilon)
      (V := heathBrownPoweredThreshold N p L output.Cp eta)
      hC0 hC2 hC4 hB hLength hCardT hEnergyMono
    simpa only [heathBrownFiniteFamilyBound, heathBrownSecondMomentShape,
      heathBrownFourthMomentShape, card_gmTranslate,
      approxAddEnergy_translate] using hMono
  have hSum :
      (∑ i : Fin 4,
        heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
          (heathBrownPoweredThreshold N p L output.Cp eta)
          (2 ^ (output.label i).val * N ^ p) (output.Wi i)) ≤
        4 * heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
          (heathBrownPoweredThreshold N p L output.Cp eta)
          (2 ^ p * N ^ p) W := by
    rw [Fin.sum_univ_four]
    nlinarith [hEach 0, hEach 1, hEach 2, hEach 3]
  exact output.hEnergy.trans
    (mul_le_mul_of_nonneg_left hSum (by positivity))

#print axioms HeathBrownUniformPoweredEnergyOutput
#print axioms finite_symmetric_source_powered_energy_heathBrown_uniform_native
#print axioms HeathBrownUniformPoweredEnergyOutput.energy_le_common_power

end

end GafniTao
