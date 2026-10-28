import Mathlib
import Definitions.Def_WeierstrassCurve_AddFormula
import Definitions.Def_NetPairing_Basic
import Theorems.Thm_WeierstrassCurve_ellipticNet_three
import Theorems.Thm_WeierstrassCurve_ellipticNet_four
import Definitions.Def_WeierstrassCurve_DivPolyMulFormula

set_option autoImplicit false

open Polynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow,
    eval_ofNat, eval_zero, eval_one, evalEval])

universe u

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] {W : WeierstrassCurve F}

section Prerequisites

end Prerequisites

section EvalLemmas

end EvalLemmas
end WeierstrassCurve.Affine

open Polynomial WeierstrassCurve

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] {W : WeierstrassCurve F}

section Prerequisites

end Prerequisites

section EvalLemmas

end EvalLemmas
end WeierstrassCurve.Affine

open Polynomial

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section ParityResolved

variable {m : ℤ}

end ParityResolved

section DoublingRewrite

variable (m : ℤ)

end DoublingRewrite

section ConsecutiveIdentities

variable (m : ℤ)

end ConsecutiveIdentities

section SmallIndex

end SmallIndex

section StarInstances

variable (t : R)

end StarInstances

end WeierstrassCurve

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

section Statement

end Statement

section BaseCases

end BaseCases

section Step

end Step

section Shell

end Shell

end WeierstrassCurve.Affine

open Polynomial

namespace WeierstrassCurve

section StarIdentityDef

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

end StarIdentityDef

section BaseSet

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

end BaseSet

namespace Affine

variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

end Affine

end WeierstrassCurve

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] {W : WeierstrassCurve F}

section AbstractCores

variable {x xa xb xg xd xs x2 Sk Sk1 Skm Sk2 Fk Fk1 Fkm Fk2 p1 p0 p2 pm Qe P2e S2 F2
  b2 b4 b6 b8 : F}

private lemma star_eval_core {xj xjm xjp Sj Sjm Sjp Fj Fjm Fjp : F}
    (hMj : xj * Sj = Fj) (hMjm : xjm * Sjm = Fjm) (hMjp : xjp * Sjp = Fjp)
    (hsum : (xjp + xjm) * (xj - x) ^ 2 =
      2 * (xj * x) * (xj + x) + b2 * (xj * x) + b4 * (xj + x) + b6)
    (hd3 : (x * Sj - Fj) ^ 2 = Sjp * Sjm) :
    2 * x * Fj * (Fj + x * Sj) + b2 * x * (Fj * Sj) + b4 * ((Fj + x * Sj) * Sj) +
        b6 * Sj ^ 2 = Fjp * Sjm + Fjm * Sjp := by
  linear_combination
    ((xjp + xjm) * (Sj * xj - 2 * x * Sj + Fj) -
      (2 * x * (Fj + xj * Sj) + 2 * x ^ 2 * Sj + b2 * x * Sj + b4 * Sj)) * hMj +
    (-Sj ^ 2) * hsum + (xjp + xjm) * hd3 + Sjm * hMjp + Sjp * hMjm

private lemma odd_step_core
    (hM0 : xa * Sk = Fk) (hMm : xg * Skm = Fkm) (hM1 : xb * Sk1 = Fk1) (hM2 : xd * Sk2 = Fk2)
    (hD1 : Fk1 * Sk - Fk * Sk1 = -p1)
    (hD2a : Fk1 * Skm - Fkm * Sk1 = -(p0 * Qe))
    (hD2b : Fk2 * Sk - Fk * Sk2 = -(p2 * Qe))
    (hD3a : (x * Sk - Fk) ^ 2 = Sk1 * Skm)
    (hD3b : (x * Sk1 - Fk1) ^ 2 = Sk2 * Sk)
    (hPsi : S2 = p1 ^ 2) (hPhi : F2 = x * S2 - p2 * p0 * Qe)
    (hg1 : (xs + x) * (xb - xa) ^ 2 =
      2 * (xb * xa) * (xb + xa) + b2 * (xb * xa) + b4 * (xb + xa) + b6)
    (hg2 : (xd + xa) * (xb - x) ^ 2 =
      2 * (xb * x) * (xb + x) + b2 * (xb * x) + b4 * (xb + x) + b6)
    (hg3 : (xb + xg) * (xa - x) ^ 2 =
      2 * (xa * x) * (xa + x) + b2 * (xa * x) + b4 * (xa + x) + b6)
    (hg3p : xb * xg * (xa - x) ^ 2 =
      (xa * x) ^ 2 - b4 * (xa * x) - b6 * (xa + x) - b8)
    (hbrel : 4 * b8 = b2 * b6 - b4 ^ 2)
    (hQv : Qe = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)
    (hSkne : Sk ≠ 0) (hSk1ne : Sk1 ≠ 0) (hbane : xb ≠ xa) :
    S2 ≠ 0 ∧ xs * S2 * Qe = F2 * Qe := by

  have hp1 : p1 = -(Sk * Sk1 * (xb - xa)) := by
    linear_combination hD1 + Sk * hM1 - Sk1 * hM0
  have hP0 : p0 * Qe = -(Sk1 * Skm * (xb - xg)) := by
    linear_combination hD2a + Skm * hM1 - Sk1 * hMm
  have hP2 : p2 * Qe = -(Sk * Sk2 * (xd - xa)) := by
    linear_combination hD2b + Sk * hM2 - Sk2 * hM0
  have hSpk : Sk1 * Skm = Sk ^ 2 * (x - xa) ^ 2 := by
    linear_combination -hD3a + (2 * x * Sk - Fk - xa * Sk) * hM0
  have hSpk1 : Sk2 * Sk = Sk1 ^ 2 * (x - xb) ^ 2 := by
    linear_combination -hD3b + (2 * x * Sk1 - Fk1 - xb * Sk1) * hM1

  have hcore : (xs - x) * (xb - xa) ^ 2 * Qe +
      (x - xa) ^ 2 * (x - xb) ^ 2 * (xd - xa) * (xb - xg) = 0 := by
    linear_combination Qe * hg1 + ((x - xa) ^ 2 * (xb - xg)) * hg2 +
      (-(2 * (xb * x) * (xb + x) + b2 * (xb * x) + b4 * (xb + x) + b6 -
        2 * xa * (xb - x) ^ 2) - 4 * xb * (x - xa) * (x - xb)) * hg3 +
      (4 * (x - xa) * (x - xb)) * hg3p + (-((x - xa) * (x - xb))) * hbrel +
      (2 * (xa * xb) * (xa + xb) + b2 * (xa * xb) + b4 * (xa + xb) + b6 -
        2 * x * (xa - xb) ^ 2) * hQv
  refine ⟨?_, ?_⟩
  · rw [hPsi, hp1]
    exact pow_ne_zero 2 (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hSkne hSk1ne)
      (sub_ne_zero.mpr hbane)))
  · linear_combination (-Qe) * hPhi + (Qe * (xs - x)) * hPsi +
      (Qe * (xs - x) * (Sk * Sk1 * xa - Sk * Sk1 * xb + p1)) * hp1 +
      (Qe * p0) * hP2 + (Sk * Sk2 * (xa - xd)) * hP0 +
      (-(Sk * Sk2 * (xa - xd) * (xb - xg))) * hSpk +
      (-(Sk ^ 2 * (x - xa) ^ 2 * (xa - xd) * (xb - xg))) * hSpk1 +
      (Sk ^ 2 * Sk1 ^ 2) * hcore

private lemma even_step_core
    (hM0 : xa * Sk = Fk) (hMm : xg * Skm = Fkm) (hM1 : xb * Sk1 = Fk1)
    (hD1 : Fk1 * Sk - Fk * Sk1 = -p1)
    (hD1m : Fk * Skm - Fkm * Sk = -pm)
    (hD2a : Fk1 * Skm - Fkm * Sk1 = -(p0 * Qe))
    (hD3a : (x * Sk - Fk) ^ 2 = Sk1 * Skm)
    (hPsi : S2 = p0 ^ 2 * Qe) (hPhi : F2 = x * S2 - p1 * pm)
    (hg4 : (xs + x2) * (xb - xg) ^ 2 =
      2 * (xb * xg) * (xb + xg) + b2 * (xb * xg) + b4 * (xb + xg) + b6)
    (hdup : x2 * Qe = P2e)
    (hg3 : (xb + xg) * (xa - x) ^ 2 =
      2 * (xa * x) * (xa + x) + b2 * (xa * x) + b4 * (xa + x) + b6)
    (hg3p : xb * xg * (xa - x) ^ 2 =
      (xa * x) ^ 2 - b4 * (xa * x) - b6 * (xa + x) - b8)
    (hbrel : 4 * b8 = b2 * b6 - b4 ^ 2)
    (hQv : Qe = 4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)
    (hP2v : P2e = x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8)
    (hQne : Qe ≠ 0) (hSk1ne : Sk1 ≠ 0) (hSkmne : Skm ≠ 0)
    (haxne : xa ≠ x) (hbgne : xb ≠ xg) :
    S2 ≠ 0 ∧ xs * S2 * Qe = F2 * Qe := by

  have hp1 : p1 = -(Sk * Sk1 * (xb - xa)) := by
    linear_combination hD1 + Sk * hM1 - Sk1 * hM0
  have hpm : pm = -(Sk * Skm * (xa - xg)) := by
    linear_combination hD1m + Skm * hM0 - Sk * hMm
  have hP0 : p0 * Qe = -(Sk1 * Skm * (xb - xg)) := by
    linear_combination hD2a + Skm * hM1 - Sk1 * hMm
  have hSpk : Sk1 * Skm = Sk ^ 2 * (x - xa) ^ 2 := by
    linear_combination -hD3a + (2 * x * Sk - Fk - xa * Sk) * hM0

  have hbig : ((xs - x) * (x - xa) ^ 2 * (xb - xg) ^ 2 + (xb - xa) * (xa - xg) * Qe) *
      (Qe * (xa - x) ^ 2) = 0 := by
    rw [hQv, hP2v] at hdup
    rw [hQv]
    linear_combination
      (b2 * x ^ 6 - 4 * b2 * x ^ 5 * xa + 6 * b2 * x ^ 4 * xa ^ 2 - 4 * b2 * x ^ 3 * xa ^ 3 +
        b2 * x ^ 2 * xa ^ 4 + 4 * x ^ 7 - 16 * x ^ 6 * xa + 24 * x ^ 5 * xa ^ 2 -
        16 * x ^ 4 * xa ^ 3 + 4 * x ^ 3 * xa ^ 4 + 2 * b4 * x ^ 5 - 8 * b4 * x ^ 4 * xa +
        12 * b4 * x ^ 3 * xa ^ 2 - 8 * b4 * x ^ 2 * xa ^ 3 + 2 * b4 * x * xa ^ 4 +
        b6 * x ^ 4 - 4 * b6 * x ^ 3 * xa + 6 * b6 * x ^ 2 * xa ^ 2 - 4 * b6 * x * xa ^ 3 +
        b6 * xa ^ 4) * hg4 +
      (-x ^ 4 * xb ^ 2 + 2 * x ^ 4 * xb * xg - x ^ 4 * xg ^ 2 + 4 * x ^ 3 * xa * xb ^ 2 -
        8 * x ^ 3 * xa * xb * xg + 4 * x ^ 3 * xa * xg ^ 2 - 6 * x ^ 2 * xa ^ 2 * xb ^ 2 +
        12 * x ^ 2 * xa ^ 2 * xb * xg - 6 * x ^ 2 * xa ^ 2 * xg ^ 2 + 4 * x * xa ^ 3 * xb ^ 2 -
        8 * x * xa ^ 3 * xb * xg + 4 * x * xa ^ 3 * xg ^ 2 - xa ^ 4 * xb ^ 2 +
        2 * xa ^ 4 * xb * xg - xa ^ 4 * xg ^ 2) * hdup +
      (b2 * x ^ 5 * xa - b2 * x ^ 5 * xb - b2 * x ^ 5 * xg - 2 * b2 * x ^ 4 * xa ^ 2 +
        2 * b2 * x ^ 4 * xa * xb + 2 * b2 * x ^ 4 * xa * xg + 2 * b2 * x ^ 4 * xb * xg -
        b2 * x ^ 3 * xa ^ 2 * xb - b2 * x ^ 3 * xa ^ 2 * xg - 4 * b2 * x ^ 3 * xa * xb * xg +
        2 * b2 * x ^ 2 * xa ^ 2 * xb * xg + 6 * x ^ 6 * xa - 5 * x ^ 6 * xb - 5 * x ^ 6 * xg -
        10 * x ^ 5 * xa ^ 2 + 10 * x ^ 5 * xa * xb + 10 * x ^ 5 * xa * xg +
        8 * x ^ 5 * xb * xg - 5 * x ^ 4 * xa ^ 2 * xb - 5 * x ^ 4 * xa ^ 2 * xg -
        16 * x ^ 4 * xa * xb * xg + 8 * x ^ 3 * xa ^ 2 * xb * xg + b2 * b4 * x ^ 2 * xa ^ 2 -
        b4 * x ^ 5 + b4 * x ^ 4 * xa - b4 * x ^ 4 * xb - b4 * x ^ 4 * xg +
        2 * b4 * x ^ 3 * xa ^ 2 + 2 * b4 * x ^ 3 * xa * xb + 2 * b4 * x ^ 3 * xa * xg +
        4 * b4 * x ^ 3 * xb * xg - b4 * x ^ 2 * xa ^ 2 * xb - b4 * x ^ 2 * xa ^ 2 * xg -
        8 * b4 * x ^ 2 * xa * xb * xg + 4 * b4 * x * xa ^ 2 * xb * xg - b2 * b6 * x ^ 3 +
        3 * b2 * b6 * x ^ 2 * xa + b4 ^ 2 * x ^ 3 - b4 ^ 2 * x ^ 2 * xa +
        2 * b4 ^ 2 * x * xa ^ 2 - 5 * b6 * x ^ 4 + 10 * b6 * x ^ 3 * xa + b6 * x ^ 3 * xb +
        b6 * x ^ 3 * xg + 2 * b6 * x ^ 2 * xa ^ 2 - 2 * b6 * x ^ 2 * xa * xb -
        2 * b6 * x ^ 2 * xa * xg + 2 * b6 * x ^ 2 * xb * xg + b6 * x * xa ^ 2 * xb +
        b6 * x * xa ^ 2 * xg - 4 * b6 * x * xa * xb * xg + 2 * b6 * xa ^ 2 * xb * xg +
        b2 * b8 * x * xa + b4 * b6 * x ^ 2 + 3 * b4 * b6 * x * xa + b4 * b6 * xa ^ 2 +
        2 * b8 * x ^ 2 * xa + b8 * x ^ 2 * xb + b8 * x ^ 2 * xg + 2 * b8 * x * xa ^ 2 -
        2 * b8 * x * xa * xb - 2 * b8 * x * xa * xg + b8 * xa ^ 2 * xb + b8 * xa ^ 2 * xg +
        b4 * b8 * x + b4 * b8 * xa + b6 ^ 2 * x + b6 ^ 2 * xa + b6 * b8) * hg3 +
      (b2 ^ 2 * x ^ 2 * xa ^ 2 - 4 * b2 * x ^ 4 * xa + 12 * b2 * x ^ 3 * xa ^ 2 + 4 * x ^ 6 -
        24 * x ^ 5 * xa + 36 * x ^ 4 * xa ^ 2 + 2 * b2 * b4 * x ^ 2 * xa +
        2 * b2 * b4 * x * xa ^ 2 - 4 * b4 * x ^ 4 + 8 * b4 * x ^ 3 * xa +
        12 * b4 * x ^ 2 * xa ^ 2 + b2 * b6 * x ^ 2 + b2 * b6 * xa ^ 2 + 4 * b4 ^ 2 * x * xa -
        4 * b6 * x ^ 3 + 12 * b6 * x ^ 2 * xa + 2 * b4 * b6 * x + 2 * b4 * b6 * xa -
        4 * b8 * x ^ 2 + 8 * b8 * x * xa - 4 * b8 * xa ^ 2 + b6 ^ 2) * hg3p +
      (b2 * x ^ 4 * xa - 2 * b2 * x ^ 3 * xa ^ 2 + b2 * x ^ 2 * xa ^ 3 - x ^ 6 +
        6 * x ^ 5 * xa - 9 * x ^ 4 * xa ^ 2 + 4 * x ^ 3 * xa ^ 3 + b4 * x ^ 4 -
        3 * b4 * x ^ 2 * xa ^ 2 + 2 * b4 * x * xa ^ 3 + 2 * b6 * x ^ 3 -
        3 * b6 * x ^ 2 * xa + b6 * xa ^ 3 + b8 * x ^ 2 - 2 * b8 * x * xa + b8 * xa ^ 2) * hbrel
  have hcoreE : (xs - x) * (x - xa) ^ 2 * (xb - xg) ^ 2 + (xb - xa) * (xa - xg) * Qe = 0 :=
    (mul_eq_zero.mp hbig).resolve_right
      (mul_ne_zero hQne (pow_ne_zero 2 (sub_ne_zero.mpr (fun hE => haxne hE))))

  have hp0ne : p0 * Qe ≠ 0 := by
    rw [hP0]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hSk1ne hSkmne) (sub_ne_zero.mpr hbgne))
  refine ⟨?_, ?_⟩
  · intro hS20
    apply hp0ne
    have h0 : p0 ^ 2 * Qe = 0 := by rw [← hPsi]; exact hS20
    rcases mul_eq_zero.mp h0 with h | h
    · rcases pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h with h'
      rw [h', zero_mul]
    · exact absurd h hQne
  · linear_combination (-Qe) * hPhi + (Qe * (xs - x)) * hPsi + (Qe * pm) * hp1 +
      (Qe * Sk * Sk1 * (xa - xb)) * hpm +
      ((xs - x) * (Qe * p0 - Sk1 * Skm * xb + Sk1 * Skm * xg)) * hP0 +
      ((xs - x) * (xb - xg) ^ 2 * (Sk ^ 2 * (xa - x) ^ 2 + Sk1 * Skm) -
        Qe * Sk ^ 2 * (xa - xb) * (xa - xg)) * hSpk +
      (Sk ^ 4 * (xa - x) ^ 2) * hcoreE

end AbstractCores

variable [DecidableEq F]

end WeierstrassCurve.Affine

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

section RootToTorsion

end RootToTorsion

section TorsionToRoot

end TorsionToRoot

section StarForm

end StarForm

end WeierstrassCurve.Affine
