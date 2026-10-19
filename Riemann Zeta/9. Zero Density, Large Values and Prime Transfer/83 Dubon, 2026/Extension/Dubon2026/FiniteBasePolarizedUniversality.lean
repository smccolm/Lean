import Dubon2026.FiniteBasePolarizedRepresentation
import Dubon2026.FixedResidualPolarizedNaturality

/-! Original continuous polarized deformation classification over an actual
finite arithmetic base, with its finite residual presentation derived from
arithmetic character finiteness. This is the finite-base consumer on DUB-17's
CM route; construction of the modular residual input remains required. -/

namespace Dubon2026
open Matrix
open scoped NumberField
noncomputable section

/-- Retain the original arithmetic extension algebra throughout coefficient classification. -/
local instance finiteBasePolarizedUniversalityUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable {ι O A : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
  [CharP (IsLocalRing.ResidueField O) p]
  (σ : finiteBaseArithmeticGaloisGroup a F →ₜ*
    PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (ν : finiteBaseArithmeticGaloisGroup a F →* Oˣ)
  (hν : ∀ g, polarizedSimilitude (σ g) =
    Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g))
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
  (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)

/-- The actual finite-base arithmetic coefficient ring classifies all original
continuous polarized lifts, with no separately supplied finite generators. -/
@[irreducible] def finiteBasePolarizedFiberEquiv :
    (letI := finiteBasePolarizedCoefficientRing_isLocal a F ha p hp hpa σ ν hν
     OriginalContinuousCoefficientFiber
       (finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa σ ν hν) eA ≃
       OriginalContinuousPolarizedFiber eA (finiteBaseArithmeticGaloisGroup a F) σ.toMonoidHom ν) :=
  fixedResidualPolarizedFiberEquiv hA eA p hp (finiteBaseArithmeticGaloisGroup a F) σ.toMonoidHom
    (polarizedBlockRepresentation_continuous.comp σ.continuous)
    (finiteBasePolarizedGenerators a F ha p hp hpa σ)
    (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν

/-- The arithmetic classification evaluates the same universal polarized
representation at every original group element and coefficient map. -/
theorem finiteBasePolarizedFiberEquiv_evaluation :
    (letI := finiteBasePolarizedCoefficientRing_isLocal a F ha p hp hpa σ ν hν
     ∀ (f : OriginalContinuousCoefficientFiber
       (finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa σ ν hν) eA)
       (g : finiteBaseArithmeticGaloisGroup a F),
       (finiteBasePolarizedFiberEquiv a F ha p hp hpa σ ν hν hA eA f).val g =
         polarizedCoefficientMap f.val.toRingHom
           (finiteBasePolarizedUniversalRepresentation a F ha p hp hpa σ ν hν g)) := by
  unfold finiteBasePolarizedFiberEquiv finiteBasePolarizedUniversalRepresentation
  exact fixedResidualPolarizedFiberEquiv_evaluation hA eA p hp (finiteBaseArithmeticGaloisGroup a F)
    σ.toMonoidHom (polarizedBlockRepresentation_continuous.comp σ.continuous)
    (finiteBasePolarizedGenerators a F ha p hp hpa σ)
    (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν

variable {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  [Algebra O B] [WithIdeal B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- Arithmetic polarized classification commutes with every original continuous
residue-preserving coefficient map. -/
theorem finiteBasePolarizedFiberEquiv_natural
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    (letI := finiteBasePolarizedCoefficientRing_isLocal a F ha p hp hpa σ ν hν
     ∀ (f : OriginalContinuousCoefficientFiber
       (finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa σ ν hν) eA)
       (g : finiteBaseArithmeticGaloisGroup a F),
       (finiteBasePolarizedFiberEquiv a F ha p hp hpa σ ν hν hB eB
         (originalCoefficientFiberPostcomp _ eA eB k hk hres f)).val g =
       polarizedCoefficientMap k.toRingHom
         ((finiteBasePolarizedFiberEquiv a F ha p hp hpa σ ν hν hA eA f).val g)) := by
  unfold finiteBasePolarizedFiberEquiv
  exact fixedResidualPolarizedFiberEquiv_natural hA eA p hp (finiteBaseArithmeticGaloisGroup a F)
    σ.toMonoidHom (polarizedBlockRepresentation_continuous.comp σ.continuous)
    (finiteBasePolarizedGenerators a F ha p hp hpa σ)
    (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν hB eB k hk hres

end
end Dubon2026
