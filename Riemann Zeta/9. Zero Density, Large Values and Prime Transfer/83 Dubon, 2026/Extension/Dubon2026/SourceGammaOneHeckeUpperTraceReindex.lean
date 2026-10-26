import Dubon2026.SourceH1TraceBaseChangeCoefficient
import Dubon2026.SourceGammaOneHeckeUpperImage
import Dubon2026.SourceGammaOneSubgroupCohomologyMap

/-! DUB-17/18 -> original all-weight adic association -> actual Gamma1
surjective-transfer Hecke compatibility -> the original upper-subgroup trace
under the actual cover isomorphism. Native trace base change and the exact
preimage subgroup discharge the trace reindexing condition. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

private theorem trace_reindex_coefficient
    {R G H : Type} [CommRing R] [Group G] [Group H]
    (A : Rep.{0} R H) (e : G ≃* H) (S : Subgroup H) (T : Subgroup G)
    (hT : T = S.comap e.toMonoidHom)
    [Fintype (H ⧸ S)] [Fintype (G ⧸ T)]
    (B : Rep.{0} R G) (f : Rep.res e.toMonoidHom A ⟶ B) :
    subgroupCohomologyTrace A S 1 ≫ groupCohomology.map e.toMonoidHom f 1 =
      groupCohomology.map (A := Rep.res S.subtype A)
        ((e.toMonoidHom.comp T.subtype).codRestrict S
          (fun x => by simpa only [hT] using x.property))
        ((Rep.resFunctor T.subtype).map f) 1 ≫ subgroupCohomologyTrace B T 1 := by
  subst T
  exact sourceSubgroupH1Trace_pullback_coefficient A e.toMonoidHom S B f
    (subgroupComapCosetMap_surjective e.toMonoidHom e.surjective S)

/-- The actual Gamma1 upper subgroup is precisely the inverse image of
the original upper subgroup inside the actual cover image. -/
theorem sourceGammaOneRangeEquiv_heckeUpper_comap
    (Q N ell : ℕ) [NeZero N] (hcop : Nat.Coprime ell N) :
    sourceGammaOneHeckeUpper (Q * N ^ 2) ell =
      ((heckeUpperSubgroup Q ell).subgroupOf (sourceGammaOneDiagonalHom Q N).range).comap
        (sourceGammaOneRangeEquiv Q N).toMonoidHom := by
  ext g
  exact (sourceGammaOneDiagonalHom_heckeUpper_iff Q N ell hcop g).symm

/-- The actual range isomorphism restricted to the original upper
subgroup, keeping its genuine codomain inside the cover image. -/
def sourceGammaOneUpperRangeHom
    (Q N ell : ℕ) [NeZero N] (hcop : Nat.Coprime ell N) :
    sourceGammaOneHeckeUpper (Q * N ^ 2) ell →*
      (heckeUpperSubgroup Q ell).subgroupOf (sourceGammaOneDiagonalHom Q N).range :=
  (((sourceGammaOneRangeEquiv Q N).toMonoidHom).comp
    (sourceGammaOneHeckeUpper (Q * N ^ 2) ell).subtype).codRestrict _
      (fun x => (sourceGammaOneDiagonalHom_heckeUpper_iff Q N ell hcop x.val).mpr x.property)

private local instance upperImageCosetsFintype (Q N ell : ℕ) [NeZero N] [NeZero ell] :
    Fintype ((sourceGammaOneDiagonalHom Q N).range ⧸
      (heckeUpperSubgroup Q ell).subgroupOf (sourceGammaOneDiagonalHom Q N).range) := by
  letI := sourceHeckeUpperFintype Q ell
  exact Fintype.ofInjective
    (subgroupComapCosetMap (sourceGammaOneDiagonalHom Q N).range.subtype (heckeUpperSubgroup Q ell))
    (subgroupComapCosetMap_injective
      (sourceGammaOneDiagonalHom Q N).range.subtype (heckeUpperSubgroup Q ell))

private local instance gammaOneUpperCosetsFintype (Q N ell : ℕ) [NeZero ell] :
    Fintype (Gamma1 (Q * N ^ 2) ⧸ sourceGammaOneHeckeUpper (Q * N ^ 2) ell) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex (Q * N ^ 2) ell
  exact Fintype.ofFinite _

/-- The actual upper-subgroup trace in the original cover image becomes
the literal Gamma1 constant-coefficient trace under the existing subgroup
H1 identification. The subgroup preimage condition is proved. -/
theorem sourceGammaOneHeckeUpperTrace_reindex
    (Q N ell w : ℕ) [NeZero N] [NeZero ell] (hcop : Nat.Coprime ell N) :
    subgroupCohomologyTrace
      (Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
        (sourceBinaryCoefficientRep (ZMod N) Q w))
      ((heckeUpperSubgroup Q ell).subgroupOf (sourceGammaOneDiagonalHom Q N).range) 1 ≫
        (sourceGammaOneSubgroupH1Iso Q N w).hom =
    groupCohomology.map
      (A := Rep.res
        ((heckeUpperSubgroup Q ell).subgroupOf (sourceGammaOneDiagonalHom Q N).range).subtype
        (Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
          (sourceBinaryCoefficientRep (ZMod N) Q w)))
      (sourceGammaOneUpperRangeHom Q N ell hcop)
      ((Rep.resFunctor (sourceGammaOneHeckeUpper (Q * N ^ 2) ell).subtype).map
        ((Rep.resFunctor (sourceGammaOneRangeEquiv Q N).toMonoidHom).map
          (sourceGammaOneCoefficientTrivialIso Q N w).hom)) 1 ≫
      subgroupCohomologyTrace
        (Rep.trivial (ZMod N) (Gamma1 (Q * N ^ 2))
          (sourceBinaryCoefficientRep (ZMod N) Q w))
        (sourceGammaOneHeckeUpper (Q * N ^ 2) ell) 1 := by
  have h := trace_reindex_coefficient
    (Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
      (sourceBinaryCoefficientRep (ZMod N) Q w))
    (sourceGammaOneRangeEquiv Q N)
    ((heckeUpperSubgroup Q ell).subgroupOf (sourceGammaOneDiagonalHom Q N).range)
    (sourceGammaOneHeckeUpper (Q * N ^ 2) ell)
    (sourceGammaOneRangeEquiv_heckeUpper_comap Q N ell hcop)
    (Rep.trivial (ZMod N) (Gamma1 (Q * N ^ 2)) (sourceBinaryCoefficientRep (ZMod N) Q w))
    ((Rep.resFunctor (sourceGammaOneRangeEquiv Q N).toMonoidHom).map
      (sourceGammaOneCoefficientTrivialIso Q N w).hom)
  exact (congrArg
    (fun z => subgroupCohomologyTrace
      (Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype
        (sourceBinaryCoefficientRep (ZMod N) Q w))
      ((heckeUpperSubgroup Q ell).subgroupOf (sourceGammaOneDiagonalHom Q N).range) 1 ≫ z)
    (sourceGammaOneSubgroupH1Iso_hom_eq_map Q N w)).trans h

end
end Dubon2026
