import Dubon2026.IntegralDominantInducedVector
import Dubon2026.CMSourceIntegralWeight

/-! Nonzeroness of the literal source integral coefficient tensor.
Each original dominant-weight factor has an explicit vector evaluating
to one. Its proved finite-free basis therefore has a nonempty index;
the native tensor basis gives nonzeroness of the original tensor module.
This is coefficient nonzeroness, not nonzero Hecke localization.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField ValuativeRel

universe u

/-- The original finite tensor of dominant induced modules is nontrivial; no nonzero coefficient representation is supplied. -/
theorem integralDominantTensor_nontrivial
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [CharZero R]
    {I : Type u} [Finite I] {n : ℕ} (lam : I → Fin (n + 1) → ℤ)
    (hlam : ∀ i, Antitone (lam i)) : Nontrivial (IntegralInducedTensor R (n + 1) lam) := by
  letI : ∀ i, Nontrivial (generalLinearIntegralInducedSubmodule R (n + 1) (lam i)) :=
    fun i => integralDominantInduced_nontrivial R (lam i) (hlam i)
  letI : ∀ i, Nonempty (Module.Free.ChooseBasisIndex R
      (generalLinearIntegralInducedSubmodule R (n + 1) (lam i))) :=
    fun i => (Module.Free.chooseBasis R
      (generalLinearIntegralInducedSubmodule R (n + 1) (lam i))).index_nonempty
  exact (integralLocalInducedTensorBasis R lam).repr.toEquiv.nontrivial

/-- The actual coefficient tensor indexed by original field embeddings is nonzero for every original dominant weight. -/
theorem cmSourceIntegralWeight_nontrivial
    (K E : Type) [Field K] [NumberField K] [Field E] [CharZero E]
    (ell : ℕ) (hell : ell.Prime) [Algebra (rationalPrimeLocalField ell hell) E]
    [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation (rationalPrimeLocalField ell hell)).HasExtension (ValuativeRel.valuation E)]
    (places : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (lam : IntegralCoefficientEmbeddingIndex K E ell hell places → Fin (n + 1) → ℤ)
    (hlam : ∀ i, Antitone (lam i)) :
    Nontrivial (CMSourceIntegralWeight K E ell hell places n lam) :=
  integralDominantTensor_nontrivial 𝒪[E] lam hlam

end
end Dubon2026
