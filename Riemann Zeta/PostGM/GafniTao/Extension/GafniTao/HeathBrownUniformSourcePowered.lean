import GafniTao.HeathBrownUniformPoweredEnergy
import GafniTao.ClassicalBinaryHeathBrownPowered

/-!
# Uniform arbitrary-power source packets

This is the source-height form of the repaired powered-energy API.  Its
cutoff is chosen before `U`, `N`, and the detector colour, and is explicitly
consumed before the returned energy output is constructed.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Uniform arbitrary-power energy output together with the two exact
mean-value packets used by the Heath--Brown exponent argument. -/
theorem finite_source_arbitrary_power_outputs_uniform_native
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ C0 C2 C4 B0 : Real,
      0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 ≤ B0 ∧
      ∀ (U R eta L : Real) (N p P : Nat)
          (W : Finset Real) (a : Nat → Complex),
        1 ≤ U → 0 < N → 0 < p → p ≤ P →
        2 * R ≤ (2 ^ P : Real) * U →
        (N : Real) ^ p ≤ U → 0 < eta → 0 < L →
        IsSeparated 1 W →
        (∀ t ∈ W, -R ≤ t ∧ t ≤ R) →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        (∀ t ∈ W, L ≤ ‖sourceDirichletPoly N a t‖) →
        B0 ≤ (2 ^ P : Real) * U →
        Nonempty (HeathBrownUniformPoweredEnergyOutput epsilon
            ((2 ^ P : Real) * U) R N p eta L W a C0 C2 C4) ∧
          Nonempty (HeathBrownPoweredCardinalityPacket
            ((2 ^ P : Real) * U) R N p eta L W a) ∧
          Nonempty (HeathBrownPoweredCardinalityPacket
            ((2 ^ P : Real) * U) R N (p + 1) eta L W a) := by
  obtain ⟨C0, C2, C4, B0, hC0, hC2, hC4, hB0, hUniform⟩ :=
    finite_symmetric_source_powered_energy_heathBrown_uniform_native
      epsilon hepsilon
  refine ⟨C0, C2, C4, B0, hC0, hC2, hC4, hB0, ?_⟩
  intro U R eta L N p P W a hU hN hp hpP hRB hNpU heta hL
    hSep hSymm hCoeff hLarge hCutoff
  let B : Real := (2 ^ P : Real) * U
  have hB : 1 ≤ B := by
    dsimp only [B]
    have hTwoPow : (1 : Real) ≤ (2 : Real) ^ P :=
      one_le_pow₀ (by norm_num)
    simpa only [one_mul] using
      mul_le_mul hTwoPow hU (by norm_num : (0 : Real) ≤ 1)
        (by positivity : (0 : Real) ≤ (2 : Real) ^ P)
  have hUpper : ∀ r ∈ Finset.range p,
      (2 ^ r * N ^ p : Real) ≤ B := by
    intro r hr
    have hrP : r ≤ P := (Finset.mem_range.mp hr).le.trans hpP
    have hTwoReal : (2 : Real) ^ r ≤ (2 : Real) ^ P :=
      pow_le_pow_right₀ (by norm_num) hrP
    dsimp only [B]
    exact mul_le_mul hTwoReal hNpU (by positivity) (by positivity)
  have hEnergy := hUniform B R N p a eta L W hN hp heta hL hSep
    hSymm hRB hCoeff hLarge hCutoff hUpper
  obtain ⟨CpBase, CmvBase, hCpBase, hCmvBase, rBase, hrBase,
      WBase, hWBase, hCardBase, hUnitBase, hPoweredBase, hMeanBase⟩ :=
    finite_symmetric_source_powered_cardinality_meanValue_native
      N p B R eta L W a hN hp hB hRB heta hL hSep hSymm hCoeff hLarge
  have hBasePacket : HeathBrownPoweredCardinalityPacket B R
      N p eta L W a :=
    ⟨CpBase, CmvBase, hCpBase, hCmvBase, rBase, hrBase,
      WBase, hWBase, hCardBase, hUnitBase, hPoweredBase, hMeanBase⟩
  have hpOne : 0 < p + 1 := Nat.add_pos_left hp 1
  obtain ⟨CpNext, CmvNext, hCpNext, hCmvNext, rNext, hrNext,
      WNext, hWNext, hCardNext, hUnitNext, hPoweredNext, hMeanNext⟩ :=
    finite_symmetric_source_powered_cardinality_meanValue_native
      N (p + 1) B R eta L W a hN hpOne hB hRB heta hL hSep hSymm
      hCoeff hLarge
  have hNextPacket : HeathBrownPoweredCardinalityPacket B R N (p + 1)
      eta L W a :=
    ⟨CpNext, CmvNext, hCpNext, hCmvNext, rNext, hrNext,
      WNext, hWNext, hCardNext, hUnitNext, hPoweredNext, hMeanNext⟩
  exact ⟨hEnergy, ⟨hBasePacket⟩, ⟨hNextPacket⟩⟩

#print axioms finite_source_arbitrary_power_outputs_uniform_native

end

end GafniTao
