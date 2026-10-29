import Dubon2026.SourceGammaOneHeckeNormEmbeddings
import Dubon2026.SourceOriginalHeckeEmbeddingCensus

/-! DUB-17/18 -> original Gamma1 Frobenius norm -> complete embeddings.
Reuse the native distinct prime Laurent conjugates. The forward equation
and reverse j-coordinate equation distinguish the actual candidates, and
the proved original alpha degree makes the list exhaustive. No reverse
equation on arbitrary beta inputs is used. -/
namespace Dubon2026.SourceFunctionField.GammaOne.HeckeNorm
noncomputable section
open IntermediateField
variable (L : Type*) [Field L] [Algebra ℚ L]
variable (M p : ℕ) [Fact p.Prime]
local notation "FF" => laurentBaseChange L (x1FunctionField M)
local notation "GG" => laurentBaseChange L (x1x0FunctionFieldC ℚ M (p * M))
local notation "EE" => AlgebraicClosure (LaurentSeries L)
attribute [local instance] alphaAlgebra alphaModule

theorem embedding_injective (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (w : GG ≃ₐ[L] GG)
    (hforward : ∀ x, w (heckeAlpha L M p x) = heckeBeta L M p x)
    (hjback : w (heckeBeta L M p (jCoordinateOver (CongruenceSubgroup.Gamma1 M) L)) =
      heckeAlpha L M p (jCoordinateOver (CongruenceSubgroup.Gamma1 M) L)) :
    Function.Injective (embedding L M p ζ hζ w hforward) := by
  intro i j hij
  apply SourceFunctionField.HeckeNorm.primeConjugates_injective L p ζ hζ
  apply (algebraMap (LaurentSeries L) EE).injective
  rw [← embedding_jBeta L M p ζ hζ w hforward hjback i,
    ← embedding_jBeta L M p ζ hζ w hforward hjback j, hij]

theorem embedding_bijective [NeZero M] (hcop : Nat.Coprime M p)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (w : GG ≃ₐ[L] GG)
    (hforward : ∀ x, w (heckeAlpha L M p x) = heckeBeta L M p x)
    (hjback : w (heckeBeta L M p (jCoordinateOver (CongruenceSubgroup.Gamma1 M) L)) =
      heckeAlpha L M p (jCoordinateOver (CongruenceSubgroup.Gamma1 M) L)) :
    Function.Bijective (embedding L M p ζ hζ w hforward) := by
  classical
  letI := targetAlgebra L M p
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : CharZero FF := charZero_of_injective_algebraMap (algebraMap L FF).injective
  haveI : FiniteDimensional FF GG := Module.finite_of_finrank_pos (by
    rw [heckeAlpha_finrank L M p hcop.symm]
    exact Nat.succ_pos p)
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨embedding_injective L M p ζ hζ w hforward hjback, ?_⟩
  rw [Fintype.card_fin, AlgHom.card, heckeAlpha_finrank L M p hcop.symm]

end
end Dubon2026.SourceFunctionField.GammaOne.HeckeNorm
