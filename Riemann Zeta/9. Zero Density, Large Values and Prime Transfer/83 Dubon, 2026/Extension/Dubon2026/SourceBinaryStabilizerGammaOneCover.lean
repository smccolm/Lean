import Dubon2026.SourceGammaOneCongruenceCover
import Dubon2026.SourceCoefficientStabilizerCohomology
import Dubon2026.SourceBinaryPermutationCongruence

/-! DUB-17/18 -> original all-weight adic association -> geometric finite
permutation Hecke realization. Apply the explicit Gamma1 cover to the
stabilizer of each actual coefficient orbit. This removes the level-
domination hypothesis for the exact stabilizers already appearing in
the Shapiro comparison. Arithmetic and Hecke comparison still remain. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups
attribute [local instance] sourceCoefficientVectorAction

/-- Every actual finite binary coefficient stabilizer is dominated by
the same explicit diagonally conjugated Gamma1 level Q*N^2. -/
theorem sourceBinaryCoefficientStabilizer_gammaOneCover
    (Q N w : ℕ) [NeZero N] :
    let A := sourceBinaryCoefficientRep (ZMod N) Q w
    letI : MulAction (Gamma0 Q) A := sourceCoefficientVectorAction A
    ∀ ω : MulAction.orbitRel.Quotient (Gamma0 Q) A,
      Gamma1 (Q * N ^ 2) ≤
        conjGL ((MulAction.stabilizer (Gamma0 Q) (sourceCoefficientOrbitPoint A ω)).map
          (Gamma0 Q).subtype) (heckeTriangularMatrix N 1 0) := by
  let A := sourceBinaryCoefficientRep (ZMod N) Q w
  letI : MulAction (Gamma0 Q) A := sourceCoefficientVectorAction A
  dsimp only
  intro ω γ hγ
  obtain ⟨δ, hδQ, hδN, he⟩ := sourceGammaOne_principal_diagonal_transition Q N γ hγ
  apply mem_conjGL.mpr
  refine ⟨δ, ?_, ?_⟩
  · apply Subgroup.mem_map.mpr
    refine ⟨⟨δ, hδQ⟩, ?_, rfl⟩
    change (⟨δ, hδQ⟩ : Gamma0 Q) • sourceCoefficientOrbitPoint A ω =
      sourceCoefficientOrbitPoint A ω
    apply Subtype.ext
    change A.ρ ⟨δ, hδQ⟩ ω.out = ω.out
    rw [sourceBinaryCoefficientRep_congruence N Q w ⟨δ, hδQ⟩ hδN]
    rfl
  · change mapGL ℝ δ = heckeTriangularMatrix N 1 0 * mapGL ℝ γ *
      (heckeTriangularMatrix N 1 0)⁻¹
    rw [he, mul_inv_cancel_right]

/-- At every actual positive source level, the native conjugated orbit
stabilizer is finite index by its explicit Gamma1 cover. -/
theorem sourceBinaryCoefficientStabilizer_conj_finiteIndex
    (Q N w : ℕ) [NeZero Q] [NeZero N] :
    let A := sourceBinaryCoefficientRep (ZMod N) Q w
    letI : MulAction (Gamma0 Q) A := sourceCoefficientVectorAction A
    ∀ ω : MulAction.orbitRel.Quotient (Gamma0 Q) A,
      (conjGL ((MulAction.stabilizer (Gamma0 Q) (sourceCoefficientOrbitPoint A ω)).map
        (Gamma0 Q).subtype) (heckeTriangularMatrix N 1 0)).FiniteIndex := by
  let A := sourceBinaryCoefficientRep (ZMod N) Q w
  letI : MulAction (Gamma0 Q) A := sourceCoefficientVectorAction A
  dsimp only
  intro ω
  exact Subgroup.finiteIndex_of_le (sourceBinaryCoefficientStabilizer_gammaOneCover Q N w ω)

end
end Dubon2026
