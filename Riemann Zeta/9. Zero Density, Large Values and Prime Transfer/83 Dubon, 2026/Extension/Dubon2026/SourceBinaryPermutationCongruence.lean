import Dubon2026.SourceBinaryPrimePowerPermutation

/-! DUB-17/18 -> original all-weight adic association -> finite-level
Hecke realizations -> genuine congruence-level permutation terms.
The principal congruence subgroup acts trivially on the actual binary
coefficients and their permutation linearization. This identifies the
finite action as one coming from congruence level, not an arbitrary
finite-index subgroup. Geometric and adic assembly remain required.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- A matrix congruent to the identity modulo the coefficient modulus acts
as the identity on the actual binary coefficient module in every degree. -/
theorem sourceBinaryCoefficientRep_congruence (N Q w : ℕ)
    (g : Gamma0 Q) (hg : g.val ∈ Gamma N) :
    (sourceBinaryCoefficientRep (ZMod N) Q w).ρ g = 1 := by
  have hm : mapGL (ZMod N) g.val = 1 := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    have h := congrArg (fun A : SL(2, ZMod N) => A i j) (Gamma_mem'.mp hg)
    exact h
  change homogeneousGLRepresentation w (mapGL (ZMod N) g.val) = 1
  rw [hm, map_one]

/-- The same principal congruence subgroup fixes every formal coefficient vector,
so the actual permutation representation factors through congruence level. -/
theorem sourceBinaryPermutationRep_congruence (N Q w : ℕ)
    (g : Gamma0 Q) (hg : g.val ∈ Gamma N) :
    (sourceCoefficientPermutationRep (sourceBinaryCoefficientRep (ZMod N) Q w)).ρ g = 1 := by
  change Finsupp.lmapDomain (ZMod N) (ZMod N)
    ((sourceBinaryCoefficientRep (ZMod N) Q w).ρ g) = 1
  rw [sourceBinaryCoefficientRep_congruence N Q w g hg]
  apply Finsupp.lhom_ext
  intro x r
  simp

end
end Dubon2026
