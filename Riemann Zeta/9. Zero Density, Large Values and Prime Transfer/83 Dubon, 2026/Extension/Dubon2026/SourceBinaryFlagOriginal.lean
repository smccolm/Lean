import Dubon2026.SourceBinaryFlagDescent

/-! The original binary H1 eigensystem enters the actual residual coefficient flag.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> original binary coefficient descent. The top flag step is identified
with the original representation, and its native H1 isomorphism intertwines
the full original Hecke operators.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable (F : Type) [Field F] (p Q : ℕ) [CharP F p] (hpQ : p ∣ Q) (n : ℕ)

/-- The top coefficient flag is the original binary representation, with
its original action and literal inclusion as the forward map. -/
def sourceBinaryFlagZeroIso :
    sourceBinaryFlagRep F p Q hpQ n 0 ≅ sourceBinaryCoefficientRep F Q n where
  hom := Rep.ofHom {
    toLinearMap := (sourceBinaryCoefficientFlag F n 0).subtype
    isIntertwining' := fun _ => by ext; rfl }
  inv := Rep.ofHom {
    toLinearMap := {
      toFun := fun P => ⟨P, by
        change P ∈ sourceBinaryCoefficientFlag F n 0
        rw [sourceBinaryCoefficientFlag_zero]
        trivial⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    isIntertwining' := fun _ => by ext; rfl }
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

/-- Native H1 of the actual top flag is linearly isomorphic to the original
binary H1; the equivalence is induced by the literal coefficient inclusion. -/
def sourceBinaryFlagZeroH1Equiv :
    groupCohomology.H1 (sourceBinaryFlagRep F p Q hpQ n 0) ≃ₗ[F]
      groupCohomology.H1 (sourceBinaryCoefficientRep F Q n) :=
  ((groupCohomology.functor F (Gamma0 Q) 1).mapIso
    (sourceBinaryFlagZeroIso F p Q hpQ n)).toLinearEquiv

/-- The top-flag identification commutes with each full original prime
correspondence on native H1. -/
theorem sourceBinaryFlagZeroH1Equiv_hecke {ell : ℕ} [NeZero ell] (hell : ell.Prime)
    (x : groupCohomology.H1 (sourceBinaryFlagRep F p Q hpQ n 0)) :
    sourceBinaryFlagZeroH1Equiv F p Q hpQ n (sourceBinaryFlagHeckeH1 F p Q hpQ n 0 hell x) =
      sourceBinaryHeckeH1 F hell n (sourceBinaryFlagZeroH1Equiv F p Q hpQ n x) :=
  sourcePrimeHeckeH1_naturality hell _ _ (sourceBinaryFlagZeroIso F p Q hpQ n).hom
    _ _ _ _ rfl x

private local instance originalFlagPrimeNeZero (ell : sourceBinaryHeckePrime Q) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

/-- When the residue characteristic divides the actual source level, every
nonzero original binary H1 eigensystem survives on an actual one-dimensional
character piece, with all original good-prime eigenvalues unchanged.
No nonzero flag class, chosen surviving quotient, or compatibility premise
is supplied. -/
theorem sourceBinaryH1_exists_characterPiece [NeZero Q]
    (eigenvalues : sourceBinaryHeckePrime Q → F)
    (x : groupCohomology.H1 (sourceBinaryCoefficientRep F Q n)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryH1PrimeOperators F Q n ell x = eigenvalues ell • x) :
    ∃ j : ℕ, j ≤ n ∧
      ∃ y : groupCohomology.H1 (sourceBinaryFlagQuotientRep F p Q hpQ n j),
        y ≠ 0 ∧ ∀ ell, sourceBinaryFlagQuotientOperators F p Q hpQ n j ell y =
          eigenvalues ell • y := by
  let e := sourceBinaryFlagZeroH1Equiv F p Q hpQ n
  have hy : e.symm x ≠ 0 := fun h => hx (by
    have he := congrArg e h
    simpa only [e.apply_symm_apply, map_zero] using he)
  apply sourceBinaryFlag_exists_characterPiece F p Q hpQ n eigenvalues (e.symm x) hy
  intro ell
  apply e.injective
  change e (sourceBinaryFlagHeckeH1 F p Q hpQ n 0 ell.property.1 (e.symm x)) =
    e (eigenvalues ell • e.symm x)
  rw [map_smul, sourceBinaryFlagZeroH1Equiv_hecke]
  change sourceBinaryHeckeH1 F ell.property.1 n (e (e.symm x)) =
    eigenvalues ell • e (e.symm x)
  rw [e.apply_symm_apply]
  exact heig ell

end
end Dubon2026
