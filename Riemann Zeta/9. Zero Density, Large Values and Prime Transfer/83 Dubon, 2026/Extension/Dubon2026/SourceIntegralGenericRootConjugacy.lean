import Dubon2026.SourceIntegralGenericIrreducibility
import Mathlib.FieldTheory.Normal.Basic

/-! Actual generic modular-polynomial roots are Galois conjugate. The
existing minimal-polynomial theory and native normal-extension root theorem
replace the longer external lift construction. This is the transitivity
input for the all-level cyclic-root bijection and DUB-17/18 inertia census. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial
noncomputable section

/-- Every two roots of the original generic modular polynomial are conjugate over the rational j-field. -/
theorem modularPolynomial_generic_roots_conjugate
    (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K] (hNK : (N : K) ≠ 0)
    {L : Type*} [Field L] [Algebra (RatFunc K) L] [IsAlgClosure (RatFunc K) L]
    {r s : L}
    (hr : (relationAtSeed (modularPolynomial N) (algebraMap (RatFunc K) L RatFunc.X)).IsRoot r)
    (hs : (relationAtSeed (modularPolynomial N) (algebraMap (RatFunc K) L RatFunc.X)).IsRoot s) :
    ∃ σ : L ≃ₐ[RatFunc K] L, σ r = s := by
  letI : IsAlgClosed L := IsAlgClosure.isAlgClosed (RatFunc K)
  letI : Normal (RatFunc K) L := ⟨fun _ => IsAlgClosed.splits _⟩
  let P := relationAtSeed (modularPolynomial N) (RatFunc.X : RatFunc K)
  have hm : P.Monic := (modularPolynomial_monic N).map _
  have hir : Irreducible P := modularPolynomial_irreducible_ratFunc N K hNK
  have hr0 : aeval r P = 0 := by
    rw [aeval_def, ← eval_map, relationAtSeed_map]
    exact hr.eq_zero
  have hs0 : aeval s P = 0 := by
    rw [aeval_def, ← eval_map, relationAtSeed_map]
    exact hs.eq_zero
  have hi : IsIntegral (RatFunc K) r := ⟨P, hm, hr0⟩
  have hmin : minpoly (RatFunc K) r = P := (minpoly.eq_of_irreducible_of_monic hir hr0 hm).symm
  apply minpoly.exists_algEquiv_of_root' hi.isAlgebraic
  rw [hmin]
  exact hs0

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
