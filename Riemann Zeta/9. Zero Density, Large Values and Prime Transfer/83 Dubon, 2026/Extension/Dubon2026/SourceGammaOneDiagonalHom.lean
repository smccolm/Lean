import Dubon2026.SourceGammaOneCongruenceCover
import Dubon2026.SourceRaisedLevelConjugation
import Dubon2026.SourceBinaryPermutationCongruence

/-! DUB-17/18 -> original all-weight adic association -> arithmetic
finite-cohomology realization. Restrict the already proved level-raising
homomorphism to the exact Gamma1 cover. Its image fixes the original
finite binary coefficients, providing the concrete group map needed
for the subsequent constant-coefficient cohomology comparison. -/
namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The explicit Gamma1 cover lies in the domain of the existing
level-raising homomorphism. -/
theorem sourceGammaOne_le_raisedGammaZero (Q N : ℕ) :
    Gamma1 (Q * N ^ 2) ≤ Gamma0 (Q * N) :=
  (Gamma1_in_Gamma0 _).trans
    (Gamma0_le_of_dvd (Nat.mul_dvd_mul_left Q (dvd_pow_self N (by decide : 2 ≠ 0))))

/-- The actual diagonal cover map, as a restriction of the existing
integral level-raising homomorphism. -/
def sourceGammaOneDiagonalHom (Q N : ℕ) [NeZero N] :
    Gamma1 (Q * N ^ 2) →* Gamma0 Q :=
  (sourceRaisedLevelConjugation Q N).comp
    (Subgroup.inclusion (sourceGammaOne_le_raisedGammaZero Q N))

/-- The restricted map retains the exact original diagonal equation. -/
theorem sourceGammaOneDiagonalHom_matrix (Q N : ℕ) [NeZero N]
    (g : Gamma1 (Q * N ^ 2)) :
    mapGL ℝ (sourceGammaOneDiagonalHom Q N g).val * heckeTriangularMatrix N 1 0 =
      heckeTriangularMatrix N 1 0 * mapGL ℝ g.val := by
  have hd : levelRaiseMatrix N = heckeTriangularMatrix N 1 0 := by
    apply Units.ext
    rw [heckeTriangularMatrix_val]
    simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  simpa only [← hd] using sourceRaisedLevelConjugate_matrix Q N
    ((Subgroup.inclusion (sourceGammaOne_le_raisedGammaZero Q N)) g)

/-- Injectivity is inherited from the original level-raising map. -/
theorem sourceGammaOneDiagonalHom_injective (Q N : ℕ) [NeZero N] :
    Function.Injective (sourceGammaOneDiagonalHom Q N) :=
  (sourceRaisedLevelConjugation_injective Q N).comp
    (Subgroup.inclusion_injective (sourceGammaOne_le_raisedGammaZero Q N))

/-- The actual image lies in the principal kernel at precisely the
coefficient modulus used by the finite Hecke realization. -/
theorem sourceGammaOneDiagonalHom_mem_principal (Q N : ℕ) [NeZero N]
    (g : Gamma1 (Q * N ^ 2)) :
    (sourceGammaOneDiagonalHom Q N g).val ∈ Gamma N := by
  obtain ⟨δ, _, hδN, he⟩ := sourceGammaOne_principal_diagonal_transition Q N g.val g.property
  have hδ : (sourceGammaOneDiagonalHom Q N g).val = δ := by
    apply mapGL_injective (S := ℝ)
    apply mul_right_cancel (b := heckeTriangularMatrix N 1 0)
    exact (sourceGammaOneDiagonalHom_matrix Q N g).trans he
  rw [hδ]
  exact hδN

/-- The concrete Gamma1 cover acts trivially on the same original
finite binary coefficient module, at every degree. -/
theorem sourceGammaOneDiagonalHom_binary_trivial (Q N w : ℕ) [NeZero N]
    (g : Gamma1 (Q * N ^ 2)) :
    (sourceBinaryCoefficientRep (ZMod N) Q w).ρ (sourceGammaOneDiagonalHom Q N g) = 1 :=
  sourceBinaryCoefficientRep_congruence N Q w _
    (sourceGammaOneDiagonalHom_mem_principal Q N g)

end
end Dubon2026
