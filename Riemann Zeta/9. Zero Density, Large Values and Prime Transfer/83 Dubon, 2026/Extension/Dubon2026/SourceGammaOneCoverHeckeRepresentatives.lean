import Dubon2026.SourceGammaOneCoverHeckeCosets
import Dubon2026.SourceChosenCosetTraceOne

/-! DUB-17/18 -> all-weight adic association -> Gamma1 Hecke/transfer
comparison. Choose the original Hecke representatives through the proved
actual cover equivalence and identify their literal subgroup transitions.
The pattern reuses SourceRaisedHeckeRepresentatives; no compatibility is
postulated and no Hecke operator is replaced. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (Q N ell : ℕ) [NeZero Q] [NeZero N]
  (hell : ell.Prime) (hcop : Nat.Coprime ell (Q * N))

/-- Original Hecke representatives chosen on the genuine Gamma1 cover. -/
def sourceGammaOneCoverHeckeRepresentative
    (x : Gamma0 Q ⧸ heckeUpperSubgroup Q ell) : Gamma0 Q :=
  sourceGammaOneDiagonalHom Q N
    ((sourceGammaOneCoverHeckeCosetEquiv Q N ell hell hcop).symm x).out

/-- Each actual chosen matrix represents exactly the original Hecke coset. -/
theorem sourceGammaOneCoverHeckeRepresentative_coset
    (x : Gamma0 Q ⧸ heckeUpperSubgroup Q ell) :
    (sourceGammaOneCoverHeckeRepresentative Q N ell hell hcop x :
      Gamma0 Q ⧸ heckeUpperSubgroup Q ell) = x := by
  change sourceGammaOneCoverHeckeCosetMap Q N ell hcop
    ((((sourceGammaOneCoverHeckeCosetEquiv Q N ell hell hcop).symm x).out :
      Gamma1 (Q * N ^ 2)) :
        Gamma1 (Q * N ^ 2) ⧸ sourceGammaOneHeckeUpper (Q * N ^ 2) ell) = x
  rw [QuotientGroup.out_eq']
  exact (sourceGammaOneCoverHeckeCosetEquiv Q N ell hell hcop).apply_symm_apply x

/-- Under the exact coset equivalence the representative is the literal
image of the original representative on the cover. -/
theorem sourceGammaOneCoverHeckeRepresentative_equiv
    (x : Gamma1 (Q * N ^ 2) ⧸ sourceGammaOneHeckeUpper (Q * N ^ 2) ell) :
    sourceGammaOneCoverHeckeRepresentative Q N ell hell hcop
      (sourceGammaOneCoverHeckeCosetEquiv Q N ell hell hcop x) =
        sourceGammaOneDiagonalHom Q N x.out := by
  unfold sourceGammaOneCoverHeckeRepresentative
  rw [Equiv.symm_apply_apply]

/-- The same representative identity respects the actual group action. -/
theorem sourceGammaOneCoverHeckeRepresentative_smul (g : Gamma1 (Q * N ^ 2))
    (x : Gamma1 (Q * N ^ 2) ⧸ sourceGammaOneHeckeUpper (Q * N ^ 2) ell) :
    sourceGammaOneCoverHeckeRepresentative Q N ell hell hcop
      (sourceGammaOneDiagonalHom Q N g •
        sourceGammaOneCoverHeckeCosetEquiv Q N ell hell hcop x) =
      sourceGammaOneDiagonalHom Q N (g • x).out := by
  have he : sourceGammaOneDiagonalHom Q N g •
      sourceGammaOneCoverHeckeCosetEquiv Q N ell hell hcop x =
      sourceGammaOneCoverHeckeCosetEquiv Q N ell hell hcop (g • x) :=
    (sourceGammaOneCoverHeckeCosetMap_smul Q N ell hcop g x).symm
  rw [he, sourceGammaOneCoverHeckeRepresentative_equiv]

/-- The exact chosen transition lies in the image of the original cover
transition, including its full subgroup membership. -/
theorem sourceGammaOneCoverHeckeTransition (g : Gamma1 (Q * N ^ 2))
    (x : Gamma1 (Q * N ^ 2) ⧸ sourceGammaOneHeckeUpper (Q * N ^ 2) ell) :
    sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
      (sourceGammaOneCoverHeckeRepresentative Q N ell hell hcop)
      (sourceGammaOneCoverHeckeRepresentative_coset Q N ell hell hcop)
      (sourceGammaOneDiagonalHom Q N g)
      (sourceGammaOneCoverHeckeCosetEquiv Q N ell hell hcop x) =
        sourceGammaOneCoverHeckeUpperHom Q N ell
          (cosetTransition (sourceGammaOneHeckeUpper (Q * N ^ 2) ell) g x) := by
  apply Subtype.ext
  change (sourceGammaOneCoverHeckeRepresentative Q N ell hell hcop
    (sourceGammaOneDiagonalHom Q N g •
      sourceGammaOneCoverHeckeCosetEquiv Q N ell hell hcop x))⁻¹ *
    (sourceGammaOneDiagonalHom Q N g *
      sourceGammaOneCoverHeckeRepresentative Q N ell hell hcop
        (sourceGammaOneCoverHeckeCosetEquiv Q N ell hell hcop x)) = _
  rw [sourceGammaOneCoverHeckeRepresentative_smul,
    sourceGammaOneCoverHeckeRepresentative_equiv]
  change _ = sourceGammaOneDiagonalHom Q N ((g • x).out⁻¹ * (g * x.out))
  rw [map_mul, map_mul, map_inv]

/-- Original prime conjugation of each actual chosen transition is exactly
the cover image of the genuine Gamma1 Hecke transition. -/
theorem sourceGammaOneCoverHeckeTransition_conjugation [NeZero ell]
    (g : Gamma1 (Q * N ^ 2))
    (x : Gamma1 (Q * N ^ 2) ⧸ sourceGammaOneHeckeUpper (Q * N ^ 2) ell) :
    sourceHeckeConjugation hell
      (sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
        (sourceGammaOneCoverHeckeRepresentative Q N ell hell hcop)
        (sourceGammaOneCoverHeckeRepresentative_coset Q N ell hell hcop)
        (sourceGammaOneDiagonalHom Q N g)
        (sourceGammaOneCoverHeckeCosetEquiv Q N ell hell hcop x)) =
      sourceGammaOneDiagonalHom Q N
        (sourceGammaOneHeckeConjugation (Q * N ^ 2) ell
          (cosetTransition (sourceGammaOneHeckeUpper (Q * N ^ 2) ell) g x)) := by
  rw [sourceGammaOneCoverHeckeTransition, ← sourceIntegralHeckeConjugate_eq_prime]
  exact (sourceGammaOneCoverHecke_square Q N ell _).symm

end
end Dubon2026
