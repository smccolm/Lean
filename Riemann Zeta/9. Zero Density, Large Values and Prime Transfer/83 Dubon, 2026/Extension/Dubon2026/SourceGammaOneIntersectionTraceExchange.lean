import Dubon2026.SourceH1TraceIntersection
import Dubon2026.SourceGammaOneHeckeUpperTraceReindex
import Dubon2026.SourceGammaOneCoverBinaryHeckeTrace

/-! DUB-17/18 -> original all-weight adic association -> genuine Gamma1
realization -> surjective-transfer Hecke compatibility. Instantiate the
proved intersection-trace exchange on the actual cover image and original
Hecke upper subgroup, retaining the exact conjugation preimage. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

private local instance subgroupQuotientFintype {G : Type} [Group G]
    (H : Subgroup G) [H.FiniteIndex] : Fintype (G ⧸ H) :=
  Subgroup.fintypeQuotientOfFiniteIndex

private theorem trace_intersection_of_eq
    {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (H U : Subgroup G)
    [H.FiniteIndex] [U.FiniteIndex] (W : Subgroup U) (hW : W = H.subgroupOf U)
    [fW : Fintype (U ⧸ W)] :
    subgroupCohomologyTrace (Rep.res U.subtype A) W 1 ≫
      subgroupCohomologyTrace A U 1 =
    groupCohomology.map (A := Rep.res W.subtype (Rep.res U.subtype A))
      ((sourceSubgroupIntersectionSwap H U).trans (MulEquiv.subgroupCongr hW.symm)).toMonoidHom
      (𝟙 (Rep.res (U.subgroupOf H).subtype (Rep.res H.subtype A))) 1 ≫
      subgroupCohomologyTrace (Rep.res H.subtype A) (U.subgroupOf H) 1 ≫
        subgroupCohomologyTrace A H 1 := by
  subst W
  have hf : fW = (Subgroup.fintypeQuotientOfFiniteIndex :
      Fintype (U ⧸ H.subgroupOf U)) := Subsingleton.elim _ _
  cases hf
  exact sourceSubgroupH1Trace_intersection_swap A H U

/-- The literal swap of intersection witnesses takes values in the actual
Hecke-conjugation preimage by the proved original congruence identity. -/
def sourceGammaOneHeckeIntersectionSwap
    (Q N ell : ℕ) [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N)) :
    (heckeUpperSubgroup Q ell).subgroupOf (sourceGammaOneDiagonalHom Q N).range ≃*
      (sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell) :=
  (sourceSubgroupIntersectionSwap (sourceGammaOneDiagonalHom Q N).range
    (heckeUpperSubgroup Q ell)).trans
      (MulEquiv.subgroupCongr (sourceGammaOneCoverHeckeTraceSubgroup_eq Q N ell hell hcop).symm)

/-- On the actual Gamma1 upper subgroup, the intersection swap is the
already constructed literal upper-subgroup isomorphism. -/
theorem sourceGammaOneHeckeIntersectionSwap_cover
    (Q N ell : ℕ) [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N))
    (g : sourceGammaOneHeckeUpper (Q * N ^ 2) ell) :
    sourceGammaOneHeckeIntersectionSwap Q N ell hell hcop
      (sourceGammaOneUpperRangeHom Q N ell
        (hcop.of_dvd_right (dvd_mul_left N Q)) g) =
      sourceGammaOneCoverHeckeUpperEquiv Q N ell hell hcop g := by
  apply Subtype.ext
  rfl

private local instance coverIndex (Q N : ℕ) [NeZero Q] [NeZero N] :
    (sourceGammaOneDiagonalHom Q N).range.FiniteIndex :=
  sourceGammaOneDiagonalHom_range_finiteIndex Q N

private local instance upperIndex (Q ell : ℕ) [NeZero ell] :
    (heckeUpperSubgroup Q ell).FiniteIndex :=
  sourceHeckeUpper_finiteIndex

/-- The two iterated native traces in the actual Gamma1/Hecke square agree
after the exact intersection swap. All subgroup and finiteness conditions
are discharged for the original congruence groups. -/
theorem sourceGammaOneCoverTrace_exchange
    {R : Type} [CommRing R] (Q N ell : ℕ)
    [NeZero Q] [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N)) (A : Rep.{0} R (Gamma0 Q)) :
    subgroupCohomologyTrace (Rep.res (heckeUpperSubgroup Q ell).subtype A)
      ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)) 1 ≫
        subgroupCohomologyTrace A (heckeUpperSubgroup Q ell) 1 =
    groupCohomology.map
      (A := Rep.res
        ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)).subtype
        (Rep.res (heckeUpperSubgroup Q ell).subtype A))
      (sourceGammaOneHeckeIntersectionSwap Q N ell hell hcop).toMonoidHom
      (𝟙 (Rep.res
        ((heckeUpperSubgroup Q ell).subgroupOf (sourceGammaOneDiagonalHom Q N).range).subtype
        (Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype A))) 1 ≫
      subgroupCohomologyTrace (Rep.res (sourceGammaOneDiagonalHom Q N).range.subtype A)
        ((heckeUpperSubgroup Q ell).subgroupOf (sourceGammaOneDiagonalHom Q N).range) 1 ≫
          subgroupCohomologyTrace A (sourceGammaOneDiagonalHom Q N).range 1 :=
  trace_intersection_of_eq A (sourceGammaOneDiagonalHom Q N).range (heckeUpperSubgroup Q ell)
    ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell))
    (sourceGammaOneCoverHeckeTraceSubgroup_eq Q N ell hell hcop)

end
end Dubon2026
