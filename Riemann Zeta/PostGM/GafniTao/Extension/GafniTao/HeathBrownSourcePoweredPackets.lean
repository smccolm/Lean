import GafniTao.ClassicalBinaryHeathBrownPowered
import GafniTao.HeathBrownSourceScale

/-!
# Arbitrary-power packets at the physical source height

The source power is not restricted to two or three.  A fixed natural bound
`P` on it gives the honest ambient height `2^P * U`, which contains every
dyadic block of the `p`-th power.  This theorem packages the energy-producing
power and its two mean-value companions without referring to the obsolete
equal-cutoff prototype.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact arbitrary-power energy and cardinality packets at ambient height
`2^P * U`. -/
theorem finite_source_arbitrary_power_packets_native
    (epsilon U R eta L : Real) (N p P : Nat)
    (W : Finset Real) (a : Nat → Complex)
    (hepsilon : 0 < epsilon) (hU : 1 <= U)
    (hN : 0 < N) (hp : 0 < p) (hpP : p <= P)
    (hRB : 2 * R <= (2 ^ P : Real) * U)
    (hNpU : (N : Real) ^ p <= U)
    (heta : 0 < eta) (hL : 0 < L)
    (hSep : IsSeparated 1 W)
    (hSymm : forall t, t ∈ W -> -R <= t ∧ t <= R)
    (hCoeff : forall n, n ∈ dyadicInterval N -> ‖a n‖ <= 1)
    (hLarge : forall t, t ∈ W -> L <= ‖sourceDirichletPoly N a t‖) :
    Nonempty (HeathBrownPoweredEnergyPacket epsilon
        ((2 ^ P : Real) * U) R N p eta L W a) ∧
      Nonempty (HeathBrownPoweredCardinalityPacket
        ((2 ^ P : Real) * U) R N p eta L W a) ∧
      Nonempty (HeathBrownPoweredCardinalityPacket
        ((2 ^ P : Real) * U) R N (p + 1) eta L W a) := by
  let B : Real := (2 ^ P : Real) * U
  have hB : 1 <= B := by
    dsimp only [B]
    have hTwoPow : (1 : Real) <= (2 : Real) ^ P :=
      one_le_pow₀ (by norm_num)
    simpa only [one_mul] using
      mul_le_mul hTwoPow hU (by norm_num : (0 : Real) <= 1)
        (by positivity : (0 : Real) <= (2 : Real) ^ P)
  have hUpper : forall r, r ∈ Finset.range p ->
      (2 ^ r * N ^ p : Real) <= B := by
    intro r hr
    have hrP : r <= P := (Finset.mem_range.mp hr).le.trans hpP
    have hTwoReal : (2 : Real) ^ r <= (2 : Real) ^ P :=
      pow_le_pow_right₀ (by norm_num) hrP
    dsimp only [B]
    exact mul_le_mul hTwoReal hNpU (by positivity) (by positivity)
  obtain ⟨Cp, C0, C2, C4, B0, hCp, hC0, hC2, hC4, hB0, hEnergy⟩ :=
    finite_symmetric_source_powered_energy_heathBrown_native
      epsilon B R N p a eta L W hepsilon hN hp heta hL hSep hSymm hRB
      hCoeff hLarge
  have hEnergyPacket : HeathBrownPoweredEnergyPacket epsilon B R N p eta L W a := by
    refine ⟨Cp, C0, C2, C4, B0, hCp, hC0, hC2, hC4, hB0, ?_⟩
    intro hThreshold
    exact hEnergy hThreshold hUpper
  obtain ⟨CpBase, CmvBase, hCpBase, hCmvBase, rBase, hrBase,
      WBase, hWBase, hCardBase, hUnitBase, hPoweredBase, hMeanBase⟩ :=
    finite_symmetric_source_powered_cardinality_meanValue_native
      N p B R eta L W a hN hp hB hRB heta hL hSep hSymm hCoeff hLarge
  have hBasePacket : HeathBrownPoweredCardinalityPacket B R N p eta L W a :=
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
  exact ⟨⟨hEnergyPacket⟩, ⟨hBasePacket⟩, ⟨hNextPacket⟩⟩

#print axioms finite_source_arbitrary_power_packets_native

end

end GafniTao
