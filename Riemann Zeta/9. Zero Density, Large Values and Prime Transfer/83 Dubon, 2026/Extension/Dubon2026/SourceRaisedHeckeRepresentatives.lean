import Dubon2026.SourceRaisedHeckeCosets
import Dubon2026.SourceChosenCosetTraceOne
import Dubon2026.SourceIntegralHeckeConjugation

/-! The original prime Hecke representatives chosen through raised-level conjugation.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> level-raising Hecke compatibility. These exact representative and
transition identities reindex the original full finite correspondence;
the existing native coboundary comparison handles the change of choice.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (Q p ell : ℕ) [NeZero p] (hell : ell.Prime) (hellQp : Nat.Coprime ell (Q * p))

/-- Representatives of the original Hecke cosets chosen inside the raised
level using the proved actual coset equivalence. -/
def sourceRaisedHeckeRepresentative
    (x : Gamma0 Q ⧸ heckeUpperSubgroup Q ell) : Gamma0 Q :=
  sourceRaisedLevelConjugation Q p ((sourceRaisedHeckeCosetEquiv Q p ell hellQp hell).symm x).out

/-- Each chosen matrix represents its original Hecke coset. -/
theorem sourceRaisedHeckeRepresentative_coset
    (x : Gamma0 Q ⧸ heckeUpperSubgroup Q ell) :
    (sourceRaisedHeckeRepresentative Q p ell hell hellQp x :
      Gamma0 Q ⧸ heckeUpperSubgroup Q ell) = x := by
  change sourceRaisedHeckeCosetMap Q p ell hellQp
    ((((sourceRaisedHeckeCosetEquiv Q p ell hellQp hell).symm x).out :
      Gamma0 (Q * p)) : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) = x
  rw [QuotientGroup.out_eq']
  exact (sourceRaisedHeckeCosetEquiv Q p ell hellQp hell).apply_symm_apply x

/-- Under the actual equivalence, the chosen representative is the literal
conjugate of the original representative at the raised level. -/
theorem sourceRaisedHeckeRepresentative_equiv
    (x : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) :
    sourceRaisedHeckeRepresentative Q p ell hell hellQp
      (sourceRaisedHeckeCosetEquiv Q p ell hellQp hell x) =
        sourceRaisedLevelConjugation Q p x.out := by
  unfold sourceRaisedHeckeRepresentative
  rw [Equiv.symm_apply_apply]

/-- The same identity holds after the original group action on cosets. -/
theorem sourceRaisedHeckeRepresentative_smul (g : Gamma0 (Q * p))
    (x : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) :
    sourceRaisedHeckeRepresentative Q p ell hell hellQp
      (sourceRaisedLevelConjugation Q p g • sourceRaisedHeckeCosetEquiv Q p ell hellQp hell x) =
        sourceRaisedLevelConjugation Q p (g • x).out := by
  have he : sourceRaisedLevelConjugation Q p g • sourceRaisedHeckeCosetEquiv Q p ell hellQp hell x =
      sourceRaisedHeckeCosetEquiv Q p ell hellQp hell (g • x) :=
    (sourceRaisedHeckeCosetMap_smul Q p ell hellQp g x).symm
  rw [he, sourceRaisedHeckeRepresentative_equiv]

/-- The chosen transition is exactly the conjugate of the original
raised-level transition, as an element of the original group. -/
theorem sourceRaisedHeckeTransition_inclusion (g : Gamma0 (Q * p))
    (x : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) :
    (sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
      (sourceRaisedHeckeRepresentative Q p ell hell hellQp)
      (sourceRaisedHeckeRepresentative_coset Q p ell hell hellQp)
      (sourceRaisedLevelConjugation Q p g) (sourceRaisedHeckeCosetEquiv Q p ell hellQp hell x) :
      Gamma0 Q) =
      sourceRaisedLevelConjugation Q p (cosetTransition (heckeUpperSubgroup (Q * p) ell) g x) := by
  change (sourceRaisedHeckeRepresentative Q p ell hell hellQp
    (sourceRaisedLevelConjugation Q p g • sourceRaisedHeckeCosetEquiv Q p ell hellQp hell x))⁻¹ *
      (sourceRaisedLevelConjugation Q p g *
        sourceRaisedHeckeRepresentative Q p ell hell hellQp
          (sourceRaisedHeckeCosetEquiv Q p ell hellQp hell x)) = _
  rw [sourceRaisedHeckeRepresentative_smul, sourceRaisedHeckeRepresentative_equiv]
  change _ = sourceRaisedLevelConjugation Q p ((g • x).out⁻¹ * (g * x.out))
  rw [map_mul, map_mul, map_inv]

/-- The actual prime subgroup conjugation commutes with original raised-level conjugation. -/
theorem sourceRaisedHeckeConjugation_inclusion [NeZero ell]
    (u : heckeUpperSubgroup (Q * p) ell) :
    sourceHeckeConjugation hell
      ⟨sourceRaisedLevelConjugation Q p u.val,
        (sourceRaisedLevel_mem_upper Q p ell hellQp u.val).mpr u.property⟩ =
      sourceRaisedLevelConjugation Q p (sourceHeckeConjugation hell u) := by
  rw [← sourceIntegralHeckeConjugate_eq_prime, ← sourceIntegralHeckeConjugate_eq_prime]
  apply Subtype.ext
  apply Subtype.ext
  have hb : (ell : ℤ) ∣ u.val.val 0 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ ell).mp u.property
  have hc : (p : ℤ) ∣ u.val.val 1 0 :=
    Gamma0_dmul_lower_left_dvd p Q u.val.val
      (by simpa only [Nat.mul_comm p Q] using u.val.property)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceIntegralHeckeConjugate, sourceRaisedLevelConjugation,
      sourceRaisedLevelConjugate, levelRaiseConjOfDvd]
  · exact Int.mul_ediv_assoc _ hb
  · exact (Int.mul_ediv_assoc' _ hc).symm

end
end Dubon2026
