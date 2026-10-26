import Dubon2026.SourceGammaOneUpperH1Composition

/-! DUB-17/18 -> original all-weight adic association -> genuine Gamma1
realization -> actual surjective-transfer Hecke compatibility. Compose the
proved original coefficient base change, intersection trace exchange,
native upper trace reindexing and actual Hecke pullback square. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

private theorem trace_square
    {C : Type*} [Category C] {A B D E F J K : C}
    (i : A ≅ B) (h : A ⟶ D) (p : D ⟶ E) (t : E ⟶ D)
    (q : A ⟶ F) (u : F ⟶ E) (s : F ⟶ J) (v : J ⟶ A)
    (j : J ⟶ K) (e : F ⟶ K) (pp : B ⟶ K) (tt : K ⟶ B)
    (hp : h ≫ p = q ≫ u) (hu : u ≫ t = s ≫ v ≫ h)
    (hv : v ≫ i.hom = j ≫ tt) (hs : s ≫ j = e) (hq : q ≫ e = i.hom ≫ pp) :
    h ≫ p ≫ t = i.hom ≫ pp ≫ tt ≫ i.inv ≫ h := by
  calc
    h ≫ p ≫ t = q ≫ u ≫ t := by rw [← Category.assoc, hp, Category.assoc]
    _ = q ≫ s ≫ v ≫ h := by rw [hu]
    _ = q ≫ s ≫ v ≫ i.hom ≫ i.inv ≫ h := by simp only [Iso.hom_inv_id_assoc]
    _ = q ≫ s ≫ j ≫ tt ≫ i.inv ≫ h := by rw [← Category.assoc v i.hom, hv, Category.assoc]
    _ = q ≫ e ≫ tt ≫ i.inv ≫ h := by rw [← Category.assoc s j, hs]
    _ = i.hom ≫ pp ≫ tt ≫ i.inv ≫ h := by rw [← Category.assoc q e, hq, Category.assoc]

private local instance coverIndex (Q N : ℕ) [NeZero Q] [NeZero N] :
    (sourceGammaOneDiagonalHom Q N).range.FiniteIndex :=
  sourceGammaOneDiagonalHom_range_finiteIndex Q N

private local instance coverFintype (Q N : ℕ) [NeZero Q] [NeZero N] :
    Fintype (Gamma0 Q ⧸ (sourceGammaOneDiagonalHom Q N).range) :=
  Subgroup.fintypeQuotientOfFiniteIndex

private local instance upperFintype (Q ell : ℕ) [NeZero ell] :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := sourceHeckeUpperFintype Q ell

private local instance gammaUpperFintype (M ell : ℕ) [NeZero ell] :
    Fintype (Gamma1 M ⧸ sourceGammaOneHeckeUpper M ell) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex M ell
  exact Fintype.ofFinite _

/-- The full original native Hecke correspondence commutes with the
actual cover trace after the existing Gamma1 H1 isomorphism. Every
intervening square and trace identity is derived for the original maps. -/
theorem sourceGammaOneSubgroupTrace_hecke_square
    (Q N ell w : ℕ) [NeZero Q] [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N)) :
    subgroupCohomologyTrace (sourceBinaryCoefficientRep (ZMod N) Q w)
      (sourceGammaOneDiagonalHom Q N).range 1 ≫
    groupCohomology.map (sourceHeckeConjugation hell)
      (sourceBinaryHeckeMorphism (ZMod N) hell w) 1 ≫
    subgroupCohomologyTrace (sourceBinaryCoefficientRep (ZMod N) Q w)
      (heckeUpperSubgroup Q ell) 1 =
    (sourceGammaOneSubgroupH1Iso Q N w).hom ≫
    groupCohomology.map (sourceGammaOneHeckeConjugation (Q * N ^ 2) ell)
      (sourceGammaOneConstantHeckeMorphism (ZMod N)
        (sourceBinaryCoefficientRep (ZMod N) Q w) (Q * N ^ 2) ell
        (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1]))) 1 ≫
    subgroupCohomologyTrace
      (Rep.trivial (ZMod N) (Gamma1 (Q * N ^ 2)) (sourceBinaryCoefficientRep (ZMod N) Q w))
      (sourceGammaOneHeckeUpper (Q * N ^ 2) ell) 1 ≫
    (sourceGammaOneSubgroupH1Iso Q N w).inv ≫
    subgroupCohomologyTrace (sourceBinaryCoefficientRep (ZMod N) Q w)
      (sourceGammaOneDiagonalHom Q N).range 1 := by
  let A := sourceBinaryCoefficientRep (ZMod N) Q w
  let H := (sourceGammaOneDiagonalHom Q N).range
  let U := heckeUpperSubgroup Q ell
  let T := H.comap (sourceHeckeConjugation hell)
  let Y := U.subgroupOf H
  let B := Rep.trivial (ZMod N) (Gamma1 (Q * N ^ 2)) A
  let V := sourceGammaOneHeckeUpper (Q * N ^ 2) ell
  letI : Fintype (H ⧸ Y) := Fintype.ofInjective
    (subgroupComapCosetMap H.subtype U) (subgroupComapCosetMap_injective H.subtype U)
  refine trace_square (sourceGammaOneSubgroupH1Iso Q N w)
    (subgroupCohomologyTrace A H 1)
    (groupCohomology.map (sourceHeckeConjugation hell) (sourceBinaryHeckeMorphism (ZMod N) hell w) 1)
    (subgroupCohomologyTrace A U 1)
    (groupCohomology.map (A := Rep.res H.subtype A)
      (sourceTracePullbackSubgroupHom (sourceHeckeConjugation hell) H)
      ((Rep.resFunctor T.subtype).map (sourceBinaryHeckeMorphism (ZMod N) hell w)) 1)
    (subgroupCohomologyTrace (Rep.res U.subtype A) T 1)
    (groupCohomology.map (A := Rep.res T.subtype (Rep.res U.subtype A))
      (sourceGammaOneHeckeIntersectionSwap Q N ell hell hcop).toMonoidHom
      (𝟙 (Rep.res Y.subtype (Rep.res H.subtype A))) 1)
    (subgroupCohomologyTrace (Rep.res H.subtype A) Y 1)
    (groupCohomology.map (A := Rep.res Y.subtype (Rep.res H.subtype A))
      (sourceGammaOneUpperRangeHom Q N ell (hcop.of_dvd_right (dvd_mul_left N Q)))
      ((Rep.resFunctor V.subtype).map
        ((Rep.resFunctor (sourceGammaOneRangeEquiv Q N).toMonoidHom).map
          (sourceGammaOneCoefficientTrivialIso Q N w).hom)) 1)
    (groupCohomology.map (A := Rep.res T.subtype (Rep.res U.subtype A))
      (sourceGammaOneCoverHeckeUpperEquiv Q N ell hell hcop).toMonoidHom
      ((Rep.resFunctor V.subtype).map (sourceGammaOneBinaryRestrictionCoefficient Q N w)) 1)
    (groupCohomology.map (sourceGammaOneHeckeConjugation (Q * N ^ 2) ell)
      (sourceGammaOneConstantHeckeMorphism (ZMod N) A (Q * N ^ 2) ell
        (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1]))) 1)
    (subgroupCohomologyTrace B V 1) ?_ ?_ ?_ ?_ ?_
  · exact sourceGammaOneCoverBinaryHeckeTrace_pullback (ZMod N) Q N ell hell w hcop
  · convert sourceGammaOneCoverTrace_exchange Q N ell hell hcop A using 1
    congr 2
    exact congrArg
      (fun fi : Fintype (H ⧸ Y) =>
        @subgroupCohomologyTrace (ZMod N) H _ _ (Rep.res H.subtype A) Y fi 1)
      (Subsingleton.elim _ _)
  · exact sourceGammaOneHeckeUpperTrace_reindex Q N ell w
      (hcop.of_dvd_right (dvd_mul_left N Q))
  · exact sourceGammaOneUpperH1Composition Q N ell w hell hcop
  · exact sourceGammaOneHeckeH1Pullback_square Q N ell w hell hcop

end
end Dubon2026
