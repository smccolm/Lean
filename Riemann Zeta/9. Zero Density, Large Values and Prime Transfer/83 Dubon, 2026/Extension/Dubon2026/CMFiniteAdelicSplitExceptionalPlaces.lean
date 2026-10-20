import Dubon2026.NumberFieldFiniteAdelicMatrixIntegralSupport
import Dubon2026.CMFiniteAdelicLocalConjugation

/-! # Finitely many original places obstruct the integral unitary section

The local integrality hypothesis in the source split-place section
holds outside a finite set determined by the original Hermitian matrix.
This is the actual exceptional set for the DUB-17 auxiliary-prime choice.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Filter
open scoped NumberField

/-- The original Hermitian matrix and its inverse are integral at the conjugate place for all but finitely many original places. -/
theorem cmFiniteAdelicHermitianUnit_eventually_integral
    (K : Type) [Field K] [NumberField K] [IsCMField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : (Matrix ι ι K)ˣ) :
    ∀ᶠ v in cofinite, numberFieldFiniteAdelicMatrixProjection K ι (cmFinitePlaceConjugation K v)
      (Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix.toMonoidHom H) ∈
        (((cmFinitePlaceConjugation K v).adicCompletionIntegers K).matrix (n := ι)).toSubmonoid.units :=
  (cmFinitePlaceConjugation K).injective.tendsto_cofinite.eventually
    (numberFieldFiniteAdelicMatrix_eventually_integral K _)

end
end Dubon2026
