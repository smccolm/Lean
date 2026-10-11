import Dubon2026.OriginalUnframedHopfFlatCondition
import Dubon2026.MatrixAdicHopfFlatCoefficientChange
import Dubon2026.OriginalUnframedDeformationNaturality
import Dubon2026.CoefficientFiberProductResidueCompatibility

/-! # Original residue-preserving coefficient maps preserve the local model condition -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K ι O A B : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [IsNoetherianRing B]

/-- The existing original continuous residue-preserving coefficient change preserves the entire local model condition on actual unframed classes. Locality follows from the original residue compatibility, and target residue finiteness follows from the same original residue identification. -/
theorem originalUnframedHopfFlat_postcomp
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (j : (K ≃ₐ[F] K) →* H)
    (f : A →ₐ[O] B) (hf : Continuous f)
    (hres : (localCoefficientReduction eB).comp f = localCoefficientReduction eA)
    (q : OriginalUnframedDeformationClass eA H σ)
    (hq : originalUnframedHopfFlat R F K eA H σ j q) :
    originalUnframedHopfFlat R F K eB H σ j
      (originalUnframedPostcomp eA eB H σ f hf hres q) := by
  letI : IsLocalHom f.toRingHom := originalResiduePreserving_isLocalHom eA eB f hres
  letI : Finite (IsLocalRing.ResidueField B) := Finite.of_injective eB eB.injective
  obtain ⟨ρ, rfl⟩ := originalUnframedClass_surjective eA H σ q
  change MatrixAdicHopfFlat R F K
    ((GeneralLinearGroup.map f.toRingHom).comp (ρ.val.toMonoidHom.comp j))
  exact matrixAdicHopfFlat_coefficientChange f.toRingHom (ρ.val.toMonoidHom.comp j) hq

end
end Dubon2026
