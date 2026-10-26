import Dubon2026.SourceGammaOneIntersectionTraceExchange
import Dubon2026.SourceGammaOneHeckePullbackSquare

/-! DUB-17/18 -> original all-weight adic association -> genuine Gamma1
realization -> surjective-transfer Hecke compatibility. Identify the actual
native H1 map obtained by the intersection swap and upper range pullback
with the already audited upper correspondence pullback. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

private theorem cohomology_map_eq
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

private theorem trivialCoefficient_linear (Q N w : ℕ) [NeZero N] :
    (sourceGammaOneCoefficientTrivialIso Q N w).hom.hom.toLinearMap = LinearMap.id := rfl

private theorem restrictionCoefficient_linear (Q N w : ℕ) [NeZero N] :
    (sourceGammaOneBinaryRestrictionCoefficient Q N w).hom.toLinearMap = LinearMap.id := rfl

/-- The actual intersection swap and upper-range pullback compose to the
same native upper-subgroup H1 pullback used in the proved Hecke square.
Both coefficient trivializations are the identity on the original vectors. -/
theorem sourceGammaOneUpperH1Composition
    (Q N ell w : ℕ) [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N)) :
    groupCohomology.map
      (A := Rep.res
        ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)).subtype
        (Rep.res (heckeUpperSubgroup Q ell).subtype (sourceBinaryCoefficientRep (ZMod N) Q w)))
      (sourceGammaOneHeckeIntersectionSwap Q N ell hell hcop).toMonoidHom
      (𝟙 (Rep.res
        ((heckeUpperSubgroup Q ell).subgroupOf (sourceGammaOneDiagonalHom Q N).range).subtype
        (Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
          (sourceBinaryCoefficientRep (ZMod N) Q w)))) 1 ≫
    groupCohomology.map
      (sourceGammaOneUpperRangeHom Q N ell (hcop.of_dvd_right (dvd_mul_left N Q)))
      ((Rep.resFunctor (sourceGammaOneHeckeUpper (Q * N ^ 2) ell).subtype).map
        ((Rep.resFunctor (sourceGammaOneRangeEquiv Q N).toMonoidHom).map
          (sourceGammaOneCoefficientTrivialIso Q N w).hom)) 1 =
    groupCohomology.map
      (A := Rep.res
        ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)).subtype
        (Rep.res (heckeUpperSubgroup Q ell).subtype (sourceBinaryCoefficientRep (ZMod N) Q w)))
      (sourceGammaOneCoverHeckeUpperEquiv Q N ell hell hcop).toMonoidHom
      ((Rep.resFunctor (sourceGammaOneHeckeUpper (Q * N ^ 2) ell).subtype).map
        (sourceGammaOneBinaryRestrictionCoefficient Q N w)) 1 := by
  rw [← groupCohomology.map_comp]
  apply cohomology_map_eq
    (MonoidHom.ext (fun g => sourceGammaOneHeckeIntersectionSwap_cover Q N ell hell hcop g))
  change (sourceGammaOneCoefficientTrivialIso Q N w).hom.hom.toLinearMap.comp LinearMap.id =
    (sourceGammaOneBinaryRestrictionCoefficient Q N w).hom.toLinearMap
  rw [trivialCoefficient_linear, restrictionCoefficient_linear, LinearMap.id_comp]

end
end Dubon2026
