import Dubon2026.SourceGammaOneBinaryHeckeSum

/-! DUB-17/18 -> all-weight adic association -> geometric Gamma1 Hecke
comparison. The existing representative-change coboundary vanishes on the
actual cover, whose action on the same finite binary coefficients is proved
trivial. This gives literal Hecke compatibility of the restriction leg. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
private local instance originalHeckeFinite (Q ell : ℕ) [NeZero ell] :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := sourceHeckeUpperFintype Q ell

variable (Q N w ell : ℕ) [NeZero Q] [NeZero N] [NeZero ell]
  (hell : ell.Prime) (hcop : Nat.Coprime ell (Q * N))

include hcop

/-- The actual binary cocycle pullback intertwines the full original
Hecke sum with the actual Gamma1 diagonal correspondence. -/
theorem sourceGammaOneBinaryRestrictionCocycles_hecke
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep (ZMod N) Q w)) :
    sourceGammaOneBinaryRestrictionCocycles Q N w
      (sourceBinaryHeckeCocycle (ZMod N) hell w c) =
      sourceGammaOneConstantHeckeCocycles (ZMod N)
        (sourceBinaryCoefficientRep (ZMod N) Q w) (Q * N ^ 2) ell
        (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1]))
        (sourceGammaOneBinaryRestrictionCocycles Q N w c) := by
  apply Subtype.ext
  funext g
  obtain ⟨v, hv⟩ := sourceCorrespondenceOne_chosen_sub
    (sourceBinaryCoefficientRep (ZMod N) Q w) (heckeUpperSubgroup Q ell)
    (sourceHeckeConjugation hell)
    (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1]))
    (sourceBinaryHeckeDiagonal_intertwine (ZMod N) hell w)
    (sourceGammaOneCoverHeckeRepresentative Q N ell hell hcop)
    (sourceGammaOneCoverHeckeRepresentative_coset Q N ell hell hcop) c
  have h := congrFun hv (sourceGammaOneDiagonalHom Q N g)
  change (sourceBinaryCoefficientRep (ZMod N) Q w).ρ
      (sourceGammaOneDiagonalHom Q N g) v - v =
    (∑ x : Gamma0 Q ⧸ heckeUpperSubgroup Q ell,
      (sourceBinaryCoefficientRep (ZMod N) Q w).ρ
        (sourceGammaOneCoverHeckeRepresentative Q N ell hell hcop
          (sourceGammaOneDiagonalHom Q N g • x))
        (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1])
          (c (sourceHeckeConjugation hell
            (sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
              (sourceGammaOneCoverHeckeRepresentative Q N ell hell hcop)
              (sourceGammaOneCoverHeckeRepresentative_coset Q N ell hell hcop)
              (sourceGammaOneDiagonalHom Q N g) x))))) -
      sourceCorrespondenceOne (sourceBinaryCoefficientRep (ZMod N) Q w)
        (heckeUpperSubgroup Q ell) (sourceHeckeConjugation hell)
        (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1]))
        c (sourceGammaOneDiagonalHom Q N g) at h
  rw [sourceGammaOneDiagonalHom_binary_trivial,
    sourceGammaOneBinaryHecke_chosen_sum Q N w ell hell hcop] at h
  change v - v = _ at h
  rw [sub_self] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- The original native H1 pullback commutes with every full good-prime
binary Hecke operator and its genuine Gamma1 constant-coefficient counterpart. -/
theorem sourceGammaOneBinaryRestrictionH1_hecke
    (x : groupCohomology.H1 (sourceBinaryCoefficientRep (ZMod N) Q w)) :
    sourceGammaOneBinaryRestrictionH1 Q N w
      (sourceBinaryHeckeH1 (ZMod N) hell w x) =
      sourceGammaOneConstantHeckeH1 (ZMod N)
        (sourceBinaryCoefficientRep (ZMod N) Q w) (Q * N ^ 2) ell
        (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1]))
        (sourceGammaOneBinaryRestrictionH1 Q N w x) := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    rw [sourceBinaryHeckeH1_cocycle, sourceGammaOneBinaryRestrictionH1_cocycle,
      sourceGammaOneBinaryRestrictionH1_cocycle, sourceGammaOneConstantHeckeH1_cocycle,
      sourceGammaOneBinaryRestrictionCocycles_hecke Q N w ell hell hcop]

end
end Dubon2026
