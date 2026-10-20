import Dubon2026.OriginalPolarizedCoefficientClass
import Dubon2026.OriginalFramedFiberNaturality

/-! Original coefficient change on genuine unframed polarized classes.
The trace-ring classification map is natural in the original coefficient
algebras, as required by DUB-17's unframed deformation universal property. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {ι O A B : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B]
  (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
  (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
  (H : ProfiniteGrp.{0}) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (ν : H →* Oˣ) (k : A →ₐ[O] B) (hk : Continuous k)
  (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)

/-- Original continuous residue-preserving coefficient change carries
each genuine polarized lift to the same original residual and similitude fiber. -/
def originalPolarizedFiberPostcomp (ω : OriginalContinuousPolarizedFiber eA H σ ν) :
    OriginalContinuousPolarizedFiber eB H σ ν :=
  originalPolarizedCoefficientFramed eA eB H σ ν ω.val ω.property.1
    (fun g => DFunLike.congr_fun ω.property.2 g) ⟨k, hk, hres⟩

/-- Coefficient change on the actual strict polarized classes is
well-defined by the proved transport of the original strict conjugators. -/
def originalPolarizedUnframedPostcomp :
    OriginalPolarizedUnframedDeformationClass eA H σ ν →
      OriginalPolarizedUnframedDeformationClass eB H σ ν :=
  Quotient.map (originalPolarizedFiberPostcomp eA eB H σ ν k hk hres) (by
    intro ω η he
    exact polarizedStrictlyConjugate_map (localCoefficientReduction eA).toRingHom
      (localCoefficientReduction eB).toRingHom k.toRingHom
      (congrArg AlgHom.toRingHom hres) ω.val.toMonoidHom η.val.toMonoidHom he)

/-- On every original representative, coefficient change of the actual
unframed class is the class of its original coefficient-changed lift. -/
theorem originalPolarizedUnframedPostcomp_class (ω : OriginalContinuousPolarizedFiber eA H σ ν) :
    originalPolarizedUnframedPostcomp eA eB H σ ν k hk hres
      (originalPolarizedUnframedClass eA H σ ν ω) =
    originalPolarizedUnframedClass eB H σ ν (originalPolarizedFiberPostcomp eA eB H σ ν k hk hres ω) := rfl

variable {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
  (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
  (τ : H →ₜ* PolarizedGaloisGroup ι R)
  (hτ : (polarizedCoefficientMap (localCoefficientReduction eR).toRingHom).comp τ.toMonoidHom = σ)
  (hν : ∀ g, polarizedSimilitude (τ g) = Units.map (algebraMap O R).toMonoidHom (ν g))

/-- The actual polarized trace-coefficient classification commutes with
every original continuous residue-preserving coefficient map. -/
theorem originalPolarizedCoefficientClass_natural (f : OriginalContinuousCoefficientFiber eR eA) :
    originalPolarizedCoefficientClass eR eB H σ ν τ hτ hν
        (originalCoefficientFiberPostcomp eR eA eB k hk hres f) =
      originalPolarizedUnframedPostcomp eA eB H σ ν k hk hres
        (originalPolarizedCoefficientClass eR eA H σ ν τ hτ hν f) := by
  change originalPolarizedUnframedClass eB H σ ν _ = originalPolarizedUnframedClass eB H σ ν _
  congr 1

end
end Dubon2026
