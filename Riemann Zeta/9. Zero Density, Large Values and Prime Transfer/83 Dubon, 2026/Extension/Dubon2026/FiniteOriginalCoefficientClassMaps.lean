import Dubon2026.FiniteLocalCoefficientTopology
import Dubon2026.OriginalUnframedDeformationNaturality

/-! # Actual original unframed coefficient maps with continuity derived from finite maximal-adic coefficients -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {ι O A B : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [Finite A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B]

omit [IsLocalRing O] [IsLocalRing B] in
/-- An actual coefficient algebra morphism from an original finite local maximal-adic ring is continuous for the actual coefficient topologies. -/
theorem finiteOriginalCoefficientHom_continuous
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A) (f : A →ₐ[O] B) :
    Continuous f := by
  letI : DiscreteTopology A := finiteLocalCoefficient_discrete A hA
  exact continuous_of_discreteTopology

/-- The actual original unframed coefficient-change map, with its required continuity proved from the original finite maximal-adic source. -/
def finiteOriginalUnframedPostcomp
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (k : A →ₐ[O] B)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    OriginalUnframedDeformationClass eA H σ → OriginalUnframedDeformationClass eB H σ :=
  originalUnframedPostcomp eA eB H σ k (finiteOriginalCoefficientHom_continuous hA k) hres

/-- The genuine finite-source coefficient-change map sends each original class to the class of the existing actual whole framed coefficient change. -/
theorem finiteOriginalUnframedPostcomp_class
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (k : A →ₐ[O] B)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (ρ : OriginalContinuousFramedFiber eA H σ) :
    finiteOriginalUnframedPostcomp hA eA eB H σ k hres (originalUnframedClass eA H σ ρ) =
      originalUnframedClass eB H σ
        (originalFramedFiberPostcomp eA eB H σ k (finiteOriginalCoefficientHom_continuous hA k) hres ρ) :=
  originalUnframedPostcomp_class eA eB H σ k (finiteOriginalCoefficientHom_continuous hA k) hres ρ

/-- The actual finite-source original coefficient-change maps obey composition on all original deformation classes, with both continuity hypotheses derived. -/
theorem finiteOriginalUnframedPostcomp_comp [Finite B] {C : Type u}
    [CommRing C] [IsLocalRing C] [Algebra O C] [WithIdeal C]
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (k : A →ₐ[O] B)
    (hkres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (l : B →ₐ[O] C)
    (hlres : (localCoefficientReduction eC).comp l = localCoefficientReduction eB)
    (q : OriginalUnframedDeformationClass eA H σ) :
    finiteOriginalUnframedPostcomp hB eB eC H σ l hlres
      (finiteOriginalUnframedPostcomp hA eA eB H σ k hkres q) =
    finiteOriginalUnframedPostcomp hA eA eC H σ (l.comp k)
      (by
        apply AlgHom.ext
        intro x
        exact (DFunLike.congr_fun hlres (k x)).trans (DFunLike.congr_fun hkres x)) q :=
  originalUnframedPostcomp_comp eA eB eC H σ k (finiteOriginalCoefficientHom_continuous hA k)
    hkres l (finiteOriginalCoefficientHom_continuous hB l) hlres q

end
end Dubon2026
