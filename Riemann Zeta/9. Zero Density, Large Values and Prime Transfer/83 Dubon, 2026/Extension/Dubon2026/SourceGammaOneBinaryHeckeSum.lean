import Dubon2026.SourceGammaOneBinaryRestriction

/-! DUB-17/18 -> all-weight adic association -> Gamma1 geometric Hecke
comparison. Reindex every original summand using the proved actual cover
coset equivalence and its literal conjugated transitions. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup

private local instance oldHeckeFinite (Q ell : ℕ) [NeZero ell] :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := sourceHeckeUpperFintype Q ell

private local instance coverHeckeFinite (M ell : ℕ) [NeZero ell] :
    Fintype (Gamma1 M ⧸ sourceGammaOneHeckeUpper M ell) := by
  letI := sourceGammaOneHeckeUpper_finiteIndex M ell
  exact Fintype.ofFinite _

/-- The full original Hecke sum with actual cover representatives equals
the genuine constant-coefficient Gamma1 correspondence on the literal
pullback. The original binary diagonal coefficient map is retained. -/
theorem sourceGammaOneBinaryHecke_chosen_sum
    (Q N w ell : ℕ) [NeZero Q] [NeZero N] [NeZero ell]
    (hell : ell.Prime) (hcop : Nat.Coprime ell (Q * N))
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep (ZMod N) Q w))
    (g : Gamma1 (Q * N ^ 2)) :
    (∑ x : Gamma0 Q ⧸ heckeUpperSubgroup Q ell,
      (sourceBinaryCoefficientRep (ZMod N) Q w).ρ
        (sourceGammaOneCoverHeckeRepresentative Q N ell hell hcop
          (sourceGammaOneDiagonalHom Q N g • x))
        (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1])
          (c (sourceHeckeConjugation hell
            (sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
              (sourceGammaOneCoverHeckeRepresentative Q N ell hell hcop)
              (sourceGammaOneCoverHeckeRepresentative_coset Q N ell hell hcop)
              (sourceGammaOneDiagonalHom Q N g) x))))) =
      sourceGammaOneConstantHeckeCocycles (ZMod N)
        (sourceBinaryCoefficientRep (ZMod N) Q w) (Q * N ^ 2) ell
        (homogeneousMatrixAction w (Matrix.diagonal ![(ell : ZMod N), 1]))
        (sourceGammaOneBinaryRestrictionCocycles Q N w c) g := by
  rw [sourceGammaOneConstantHeckeCocycles_apply]
  rw [← Equiv.sum_comp (sourceGammaOneCoverHeckeCosetEquiv Q N ell hell hcop)]
  apply Finset.sum_congr rfl
  intro x _
  rw [sourceGammaOneCoverHeckeRepresentative_smul,
    sourceGammaOneCoverHeckeTransition_conjugation,
    sourceGammaOneDiagonalHom_binary_trivial]
  rfl

end
end Dubon2026
