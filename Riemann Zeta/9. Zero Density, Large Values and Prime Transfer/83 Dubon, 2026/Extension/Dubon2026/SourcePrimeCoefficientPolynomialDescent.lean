import Dubon2026.SourcePrimeConjugateRealization
import Dubon2026.SourcePrimeProductInvariance


/-! DUB-17/18 -> original differential realization -> finite function-field
extension -> monic relations. Identify each literal formal prime conjugate with
the actual analytic translate, using the already proved native Hecke matrices.
This retains the full upper-half-plane convergence and coefficient embeddings.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.lean; native invariance consumer.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups
local notation "𝕢" => Function.Periodic.qParam

theorem PhiGen.coeff_mem_adjoin_jq (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)
    (c : ℕ → LaurentSeries ℚ) (hc : PhiGen.PhiGenDescends ℓ ζ c) (k : ℕ) :
    c k ∈ Algebra.adjoin ℚ {jq} := by
  apply mem_adjoin_jq_of_realL_invariant (c k)
    (fun τ => ((Polynomial.X - Polynomial.C (jt (heckeTriangularMatrix ℓ 1 0 • τ))) *
      ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (jt (heckeTriangularMatrix 1 ℓ b.val • τ)))).coeff k)
  · exact hasSum_coeff_of_phiGenDescends ℓ ζ hζ c hc k
  · intro γ τ
    exact congrArg (fun P : Polynomial ℂ => P.coeff k)
      (prime_conjugate_product_invariant ℓ hℓ.out jt jt_smul γ τ)

end
end Dubon2026.SourceFunctionField
