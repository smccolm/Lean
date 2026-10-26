import Dubon2026.SourceWeightTwoEigenLevelDescent
import Dubon2026.SourceWeightTwoNewEigenNormalization

/-! DUB-17/18 -> close the actual parabolic branch. Consume the original
nonzero parabolic H1 eigenclass, obtain its genuine cusp eigensystem,
descend to a minimal new level dividing the original, and normalize
inside the newspace. The actual primitive form keeps every original
good-prime eigenvalue. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology SourceCuspBoundary

theorem sourceTrivialParabolicEigen_exists_primitive_divisor
    (N : ℕ) [NeZero N] (θ : sourceBinaryHeckePrime N → ℂ)
    (v : H1 (Rep.trivial ℂ (Gamma0 N) ℂ)) (hv : v ≠ 0)
    (hpar : (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).hom v ∈ parabolicHoms N)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators ℂ N ell v = θ ell • v) :
    ∃ M : ℕ, ∃ hM : NeZero M,
      letI := hM
      M ∣ N ∧ ∃ f : PrimitiveCuspForm M 2,
        ∀ ell, cuspCoefficients f.toCuspForm ell.val = θ ell := by
  obtain ⟨f, hf, he⟩ := sourceTrivialParabolicEigen_exists_cuspForm N θ v hv hpar heig
  obtain ⟨M, hM, hMN, g, hg, hnew, hge⟩ :=
    sourceWeightTwoEigen_exists_new_divisor N θ f hf he
  letI := hM
  obtain ⟨f', hf'⟩ := sourceWeightTwoNewEigen_exists_primitive N M θ g hg hnew hge
  exact ⟨M, hM, hMN, f', hf'⟩

end
end Dubon2026
