import Dubon2026.SourceGammaOneHeckeUpperImage
import Dubon2026.SourceGammaOneSubgroupCohomologyMap
import Dubon2026.SourceGammaOneBinaryRestriction
import Dubon2026.SourceGammaOneCoverBinaryHeckeTrace

/-! DUB-17/18 -> original all-weight adic association -> actual Gamma1
surjective-transfer Hecke compatibility -> the native H1 pullback square.
The proved original upper-subgroup isomorphism and conjugation square
identify the group maps, while both actual coefficient maps retain the
same homogeneous binary matrix action. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

private theorem cohomologyMap_eq_of_group_and_coeff
    {R G H : Type} [CommRing R] [Group G] [Group H]
    {A : Rep.{0} R G} {B : Rep.{0} R H} {f g : H →* G}
    (hfg : f = g) (a : Rep.res f A ⟶ B) (b : Rep.res g A ⟶ B)
    (hab : a.hom.toLinearMap = b.hom.toLinearMap) :
    groupCohomology.map f a 1 = groupCohomology.map g b 1 := by
  subst g
  have he : a = b := by
    apply Rep.hom_ext
    ext x
    exact LinearMap.congr_fun hab x
  rw [he]

private theorem cohomologyMap_composition_square
    {R G H K L : Type} [CommRing R] [Group G] [Group H] [Group K] [Group L]
    {A : Rep.{0} R G} {B : Rep.{0} R H} {C : Rep.{0} R K} {D : Rep.{0} R L}
    (f : H →* G) (g : K →* H) (u : L →* G) (v : K →* L)
    (a : Rep.res f A ⟶ B) (b : Rep.res g B ⟶ C)
    (c : Rep.res u A ⟶ D) (d : Rep.res v D ⟶ C)
    (hfg : f.comp g = u.comp v)
    (hab : (((Rep.resFunctor g).map a) ≫ b).hom.toLinearMap =
      (((Rep.resFunctor v).map c) ≫ d).hom.toLinearMap) :
    groupCohomology.map f a 1 ≫ groupCohomology.map g b 1 =
      groupCohomology.map u c 1 ≫ groupCohomology.map v d 1 := by
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  exact cohomologyMap_eq_of_group_and_coeff hfg _ _ hab

private theorem binaryHeckeMorphism_linear
    (R : Type) [CommRing R] (Q ell w : ℕ) [NeZero ell] (hell : ell.Prime) :
    (sourceBinaryHeckeMorphism (Q := Q) R hell w).hom.toLinearMap =
      homogeneousMatrixAction w (Matrix.diagonal ![(ell : R), 1]) := rfl

private theorem binaryRestrictionCoefficient_linear (Q N w : ℕ) [NeZero N] :
    (sourceGammaOneBinaryRestrictionCoefficient Q N w).hom.toLinearMap = LinearMap.id := rfl

private theorem coefficientTrivialIso_linear (Q N w : ℕ) [NeZero N] :
    (sourceGammaOneCoefficientTrivialIso Q N w).hom.hom.toLinearMap = LinearMap.id := rfl

private theorem constantHeckeMorphism_linear
    (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    (M n : ℕ) [NeZero n] (b : Module.End R V) :
    (sourceGammaOneConstantHeckeMorphism R V M n b).hom.toLinearMap = b := rfl

/-- The original binary Hecke pullback on the actual trace subgroup
becomes the literal Gamma1 Hecke pullback under the proved group and
coefficient identifications. This concerns the actual maps on native H1. -/
theorem sourceGammaOneHeckeH1Pullback_square
    (Q N ell w : ℕ) [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N)) :
    groupCohomology.map
      (A := Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
        (sourceBinaryCoefficientRep (ZMod N) Q w))
      (sourceTracePullbackSubgroupHom (sourceHeckeConjugation hell)
        (sourceGammaOneDiagonalHom Q N).range)
      ((Rep.resFunctor
        ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)).subtype).map
          (sourceBinaryHeckeMorphism (ZMod N) hell w)) 1 ≫
      groupCohomology.map
        (A := Rep.res
          ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)).subtype
          (Rep.res (heckeUpperSubgroup Q ell).subtype (sourceBinaryCoefficientRep (ZMod N) Q w)))
        (sourceGammaOneCoverHeckeUpperEquiv Q N ell hell hcop).toMonoidHom
        ((Rep.resFunctor (sourceGammaOneHeckeUpper (Q * N ^ 2) ell).subtype).map
          (sourceGammaOneBinaryRestrictionCoefficient Q N w)) 1 =
    (sourceGammaOneSubgroupH1Iso Q N w).hom ≫
      groupCohomology.map (sourceGammaOneHeckeConjugation (Q * N ^ 2) ell)
        (sourceGammaOneConstantHeckeMorphism (ZMod N)
          (sourceBinaryCoefficientRep (ZMod N) Q w) (Q * N ^ 2) ell
          (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1]))) 1 := by
  have hsquare := cohomologyMap_composition_square
    (A := Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
      (sourceBinaryCoefficientRep (ZMod N) Q w))
    (sourceTracePullbackSubgroupHom (sourceHeckeConjugation hell)
      (sourceGammaOneDiagonalHom Q N).range)
    (sourceGammaOneCoverHeckeUpperEquiv Q N ell hell hcop).toMonoidHom
    (sourceGammaOneRangeEquiv Q N).toMonoidHom
    (sourceGammaOneHeckeConjugation (Q * N ^ 2) ell)
    ((Rep.resFunctor
      ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)).subtype).map
        (sourceBinaryHeckeMorphism (ZMod N) hell w))
    ((Rep.resFunctor (sourceGammaOneHeckeUpper (Q * N ^ 2) ell).subtype).map
      (sourceGammaOneBinaryRestrictionCoefficient Q N w))
    ((Rep.resFunctor (sourceGammaOneRangeEquiv Q N).toMonoidHom).map
      (sourceGammaOneCoefficientTrivialIso Q N w).hom)
    (sourceGammaOneConstantHeckeMorphism (ZMod N)
      (sourceBinaryCoefficientRep (ZMod N) Q w) (Q * N ^ 2) ell
      (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1])))
    (MonoidHom.ext (fun g =>
      sourceGammaOneCoverHeckeUpperEquiv_conjugation Q N ell hell hcop g)) (by
        change
          (sourceGammaOneBinaryRestrictionCoefficient Q N w).hom.toLinearMap.comp
            (sourceBinaryHeckeMorphism (Q := Q) (ZMod N) hell w).hom.toLinearMap =
          (sourceGammaOneConstantHeckeMorphism (ZMod N)
            (sourceBinaryCoefficientRep (ZMod N) Q w) (Q * N ^ 2) ell
            (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1]))).hom.toLinearMap.comp
            (sourceGammaOneCoefficientTrivialIso Q N w).hom.hom.toLinearMap
        rw [binaryHeckeMorphism_linear, binaryRestrictionCoefficient_linear,
          coefficientTrivialIso_linear, constantHeckeMorphism_linear,
          LinearMap.id_comp, LinearMap.comp_id])
  exact hsquare.trans (congrArg
    (fun z => z ≫ groupCohomology.map (sourceGammaOneHeckeConjugation (Q * N ^ 2) ell)
      (sourceGammaOneConstantHeckeMorphism (ZMod N)
        (sourceBinaryCoefficientRep (ZMod N) Q w) (Q * N ^ 2) ell
        (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1]))) 1)
    (sourceGammaOneSubgroupH1Iso_hom_eq_map Q N w).symm)

end
end Dubon2026
