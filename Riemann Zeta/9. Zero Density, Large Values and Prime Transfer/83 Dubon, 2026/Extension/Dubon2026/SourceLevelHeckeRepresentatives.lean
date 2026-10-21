import Dubon2026.SourceLevelHeckeCosets
import Dubon2026.SourceChosenCosetTraceOne
import Dubon2026.SourceIntegralHeckeConjugation

/-! The original prime Hecke representatives chosen through level inclusion.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> level-raising Hecke compatibility. These exact representative and
transition identities reindex the original full finite correspondence;
the existing native coboundary comparison handles the change of choice.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (Q p ell : ℕ) (hell : ell.Prime) (hellQp : Nat.Coprime ell (Q * p))

/-- Representatives of the original Hecke cosets chosen inside the raised
level using the proved actual coset equivalence. -/
def sourceLevelHeckeRepresentative
    (x : Gamma0 Q ⧸ heckeUpperSubgroup Q ell) : Gamma0 Q :=
  sourceGamma0LevelInclusion Q p ((sourceLevelHeckeCosetEquiv Q p ell hell hellQp).symm x).out

/-- Each chosen matrix represents its original Hecke coset. -/
theorem sourceLevelHeckeRepresentative_coset
    (x : Gamma0 Q ⧸ heckeUpperSubgroup Q ell) :
    (sourceLevelHeckeRepresentative Q p ell hell hellQp x :
      Gamma0 Q ⧸ heckeUpperSubgroup Q ell) = x := by
  change sourceLevelHeckeCosetMap Q p ell
    ((((sourceLevelHeckeCosetEquiv Q p ell hell hellQp).symm x).out :
      Gamma0 (Q * p)) : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) = x
  rw [QuotientGroup.out_eq']
  exact (sourceLevelHeckeCosetEquiv Q p ell hell hellQp).apply_symm_apply x

/-- Under the actual equivalence, the chosen representative is the literal
inclusion of the original representative at the raised level. -/
theorem sourceLevelHeckeRepresentative_equiv
    (x : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) :
    sourceLevelHeckeRepresentative Q p ell hell hellQp
      (sourceLevelHeckeCosetEquiv Q p ell hell hellQp x) =
        sourceGamma0LevelInclusion Q p x.out := by
  unfold sourceLevelHeckeRepresentative
  rw [Equiv.symm_apply_apply]

/-- The same identity holds after the original group action on cosets. -/
theorem sourceLevelHeckeRepresentative_smul (g : Gamma0 (Q * p))
    (x : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) :
    sourceLevelHeckeRepresentative Q p ell hell hellQp
      (sourceGamma0LevelInclusion Q p g • sourceLevelHeckeCosetEquiv Q p ell hell hellQp x) =
        sourceGamma0LevelInclusion Q p (g • x).out := by
  have he : sourceGamma0LevelInclusion Q p g • sourceLevelHeckeCosetEquiv Q p ell hell hellQp x =
      sourceLevelHeckeCosetEquiv Q p ell hell hellQp (g • x) :=
    (sourceLevelHeckeCosetMap_smul Q p ell g x).symm
  rw [he, sourceLevelHeckeRepresentative_equiv]

/-- The chosen transition is exactly the inclusion of the original
raised-level transition, as an element of the original group. -/
theorem sourceLevelHeckeTransition_inclusion (g : Gamma0 (Q * p))
    (x : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) :
    (sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
      (sourceLevelHeckeRepresentative Q p ell hell hellQp)
      (sourceLevelHeckeRepresentative_coset Q p ell hell hellQp)
      (sourceGamma0LevelInclusion Q p g) (sourceLevelHeckeCosetEquiv Q p ell hell hellQp x) :
      Gamma0 Q) =
      sourceGamma0LevelInclusion Q p (cosetTransition (heckeUpperSubgroup (Q * p) ell) g x) := by
  change (sourceLevelHeckeRepresentative Q p ell hell hellQp
    (sourceGamma0LevelInclusion Q p g • sourceLevelHeckeCosetEquiv Q p ell hell hellQp x))⁻¹ *
      (sourceGamma0LevelInclusion Q p g *
        sourceLevelHeckeRepresentative Q p ell hell hellQp
          (sourceLevelHeckeCosetEquiv Q p ell hell hellQp x)) = _
  rw [sourceLevelHeckeRepresentative_smul, sourceLevelHeckeRepresentative_equiv]
  change _ = sourceGamma0LevelInclusion Q p ((g • x).out⁻¹ * (g * x.out))
  rw [map_mul, map_mul, map_inv]

/-- The actual prime subgroup conjugation commutes with original level inclusion. -/
theorem sourceLevelHeckeConjugation_inclusion [NeZero ell]
    (u : heckeUpperSubgroup (Q * p) ell) :
    sourceHeckeConjugation hell
      ⟨sourceGamma0LevelInclusion Q p u.val,
        (sourceLevelInclusion_mem_upper Q p ell u.val).mpr u.property⟩ =
      sourceGamma0LevelInclusion Q p (sourceHeckeConjugation hell u) := by
  rw [← sourceIntegralHeckeConjugate_eq_prime, ← sourceIntegralHeckeConjugate_eq_prime]
  rfl

end
end Dubon2026
