import GafniTao.HeathBrownUniformCardinalityPacket
import GafniTao.HeathBrownUniformPoweredEnergy

/-!
# Fully uniform consecutive-power outputs

The energy-producing power and its two cardinality powers must use constants
chosen before the height.  The equalities in the output structure make that
quantifier order visible to every downstream exponent calculation.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- A powered energy output built with already fixed factorization and
Heath--Brown constants. -/
theorem finite_symmetric_source_powered_energy_of_constants
    (epsilon C0 C2 C4 B0 Cp : Real)
    (hC0 : 0 < C0) (hB0 : 1 ≤ B0) (hCp : 0 < Cp)
    (hHB : ∀ (M : Nat) (T V : Real) (W' : Finset Real)
        (b : Nat → Complex),
      0 < M → B0 ≤ T → (M : Real) ≤ T → 0 ≤ V →
      IsSeparated 1 W' → InBaseInterval T W' →
      (∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) →
      (∀ t ∈ W', V ≤ ‖sourceDirichletPoly M b t‖) →
      (ApproxAddEnergy 1 W' : Real) * V ^ 2 ≤
        C0 * T ^ (epsilon / 2) *
          Real.sqrt (C2 * T ^ (epsilon / 2) *
            heathBrownSecondMomentShape T M W') *
          Real.sqrt (C4 * T ^ (epsilon / 2) *
            heathBrownFourthMomentShape T M W'))
    (B R : Real) (N p : Nat) (a : Nat → Complex)
    (eta L : Real) (W : Finset Real)
    (hN : 0 < N) (hp : 0 < p) (heta : 0 < eta) (hL : 0 < L)
    (hSep : IsSeparated 1 W)
    (hSymm : ∀ t ∈ W, -R ≤ t ∧ t ≤ R)
    (hRB : 2 * R ≤ B)
    (hCoeff : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1)
    (hPowAll : ∀ (N' : Nat) (a' : Nat → Complex),
      (∀ n ∈ dyadicInterval N', ‖a' n‖ ≤ 1) →
      ∀ m : Nat, 0 < m →
        ‖finitePowCoeff N' p a' m‖ ≤ Cp * (m : Real) ^ eta)
    (hLarge : ∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖)
    (hCutoff : B0 ≤ B)
    (hUpper : ∀ r ∈ Finset.range p,
      (2 ^ r * N ^ p : Real) ≤ B) :
    ∃ output : HeathBrownUniformPoweredEnergyOutput
        epsilon B R N p eta L W a C0 C2 C4,
      output.Cp = Cp := by
  let aT : Nat → Complex := phaseShiftCoeffs R a
  have hCoeffT : ∀ n ∈ dyadicInterval N, ‖aT n‖ ≤ 1 :=
    norm_phaseShiftCoeffs_le_one_on N a R hCoeff
  have hCoeffConj : ∀ n ∈ dyadicInterval N,
      ‖conjugateCoeffs aT n‖ ≤ 1 := by
    intro n hn
    rw [norm_conjugateCoeffs]
    exact hCoeffT n hn
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
  let output : HeathBrownUniformPoweredEnergyOutput
      epsilon B R N p eta L W a C0 C2 C4 :=
    ⟨Cp, hCp, label, Wi, hSubset, hSepWi, hBaseWi, hUnit, hPowered,
      by
        rw [← approxAddEnergy_translate 1 R W]
        exact hEnergy⟩
  exact ⟨output, rfl⟩

/-- Three actual packets sharing a single globally selected factorization
constant and a single mean-value constant. -/
structure HeathBrownFullyUniformOutputs
    (epsilon B R : Real) (N p : Nat) (eta L : Real)
    (W : Finset Real) (a : Nat → Complex)
    (Cp Cmv C0 C2 C4 : Real) where
  energy : HeathBrownUniformPoweredEnergyOutput
    epsilon B R N p eta L W a C0 C2 C4
  card : HeathBrownPoweredCardinalityPacket B R N p eta L W a
  next : HeathBrownPoweredCardinalityPacket B R N (p + 1) eta L W a
  energy_Cp : energy.Cp = Cp
  card_Cp : card.Cp = Cp
  next_Cp : next.Cp = Cp
  card_Cmv : card.Cmv = Cmv
  next_Cmv : next.Cmv = Cmv

/-- Fully uniform arbitrary-power theorem.  Every analytic constant is
selected before `U`, `N`, the power, coefficients, or the zero family. -/
theorem finite_source_arbitrary_power_outputs_fully_uniform_native
    (epsilon eta : Real) (P : Nat)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Cp Cmv C0 C2 C4 B0 : Real,
      1 ≤ Cp ∧ 0 < Cmv ∧ 0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 ≤ B0 ∧
      ∀ (U R L : Real) (N p : Nat) (W : Finset Real)
          (a : Nat → Complex),
        1 ≤ U → 0 < N → 0 < p → p ≤ P →
        2 * R ≤ (2 ^ P : Real) * U →
        (N : Real) ^ p ≤ U → 0 < L →
        IsSeparated 1 W →
        (∀ t ∈ W, -R ≤ t ∧ t ≤ R) →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        (∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖) →
        B0 ≤ (2 ^ P : Real) * U →
        Nonempty (HeathBrownFullyUniformOutputs epsilon
          ((2 ^ P : Real) * U) R N p eta L W a
          Cp Cmv C0 C2 C4) := by
  obtain ⟨Cp, hCp, hPow⟩ :=
    finitePowCoeff_bound_uniform_up_to (P + 1) eta heta
  have hCpPos : 0 < Cp := zero_lt_one.trans_le hCp
  obtain ⟨Cmv, hCmv, hMean⟩ :=
    finite_symmetric_source_cardinality_meanValue_native
  obtain ⟨C0, C2, C4, B0, hC0, hC2, hC4, hB0, hHB⟩ :=
    heathBrownFiniteEnergyRelation_native epsilon hepsilon
  refine ⟨Cp, Cmv, C0, C2, C4, B0, hCp, hCmv, hC0, hC2,
    hC4, hB0, ?_⟩
  intro U R L N p W a hU hN hp hpP hRB hNpU hL hSep hSymm
    hCoeff hLarge hCutoff
  let B : Real := (2 ^ P : Real) * U
  have hB : 1 ≤ B := by
    have hTwo : (1 : Real) ≤ (2 : Real) ^ P := one_le_pow₀ (by norm_num)
    dsimp only [B]
    nlinarith [mul_le_mul hTwo hU (by norm_num : (0 : Real) ≤ 1)
      (by positivity : (0 : Real) ≤ (2 : Real) ^ P)]
  have hUpper : ∀ r ∈ Finset.range p,
      (2 ^ r * N ^ p : Real) ≤ B := by
    intro r hr
    have hrP : r ≤ P := (Finset.mem_range.mp hr).le.trans hpP
    have hTwo : (2 : Real) ^ r ≤ (2 : Real) ^ P :=
      pow_le_pow_right₀ (by norm_num) hrP
    dsimp only [B]
    exact mul_le_mul hTwo hNpU (by positivity) (by positivity)
  have hPowP := hPow p (by omega : p ≤ P + 1)
  obtain ⟨energy, hEnergyCp⟩ :=
    finite_symmetric_source_powered_energy_of_constants
      epsilon C0 C2 C4 B0 Cp hC0 hB0 hCpPos
      hHB B R N p a eta L W hN hp heta hL hSep hSymm hRB
      hCoeff hPowP hLarge hCutoff hUpper
  obtain ⟨card, hCardCp, hCardCmv⟩ :=
    finite_symmetric_source_powered_cardinality_of_constants
      Cp Cmv hCpPos hCmv hMean N p B R eta L W a
      hN hp hB hRB heta hL hSep hSymm hCoeff hPowP hLarge
  have hpOne : 0 < p + 1 := Nat.add_pos_left hp 1
  have hPowNext := hPow (p + 1) (by omega : p + 1 ≤ P + 1)
  obtain ⟨next, hNextCp, hNextCmv⟩ :=
    finite_symmetric_source_powered_cardinality_of_constants
      Cp Cmv hCpPos hCmv hMean N (p + 1) B R eta L W a
      hN hpOne hB hRB heta hL hSep hSymm hCoeff hPowNext hLarge
  exact ⟨⟨energy, card, next, hEnergyCp, hCardCp, hNextCp,
    hCardCmv, hNextCmv⟩⟩

#print axioms finite_symmetric_source_powered_energy_of_constants
#print axioms HeathBrownFullyUniformOutputs
#print axioms finite_source_arbitrary_power_outputs_fully_uniform_native

end

end GafniTao
