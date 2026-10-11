import Dubon2026.FiniteCoefficientVectorSpanning
import Dubon2026.FiniteFreeHopfPointModelFinitePower
import Dubon2026.FiniteFreeHopfPointModelSurjection
import Mathlib.RingTheory.Flat.Localization

/-! # Genuine model extension to any finite original coefficient ring -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K ι A B : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B] [Fintype B]

/-- Every original coefficient map to a finite target ring constructs a model of the actual coefficient-changed representation. Use the genuine finite product of source models and quotient it by the kernel of the actual equivariant coefficient spanning map. -/
def finiteCoefficientExtensionHopfModel (f : A →+* B)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) :
    FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ)) := by
  letI : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  letI : Module.Flat R K := Module.Flat.trans R F K
  exact finiteFreeHopfPointModelOfSurjective (finiteFreeHopfPointModelFinitePi B m)
    (finiteCoefficientVectorSpanningMap f) (finiteCoefficientVectorSpanningMap_surjective f)
    (finiteCoefficientVectorSpanningMap_equivariant f ρ)

/-- The actual target coefficient representation has a derived finite free model for an arbitrary original ring map, without an injectivity or surjectivity hypothesis on that map. -/
theorem finiteCoefficientExtensionHopfModel_exists (f : A →+* B)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ))) := by
  exact ⟨finiteCoefficientExtensionHopfModel f ρ m⟩

end
end Dubon2026
