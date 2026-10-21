import Dubon2026.SourceLevelGenusNumerics
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-! DUB-17/18 -> residual Galois association -> parabolic geometric realization
-> matching dimension bounds -> original elliptic fixed-point counts.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_natCard_fixedPoints_S_cosets_Gamma0_eq_nuTwo.lean.
One literal quadratic-root/coset bijection supplies both S and ST counts;
the second external file's duplicate proof is not needed.
-/
namespace Dubon2026.SourceElliptic
noncomputable section

open Matrix Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The integral companion matrix encompassing both original elliptic elements. -/
def V (s : ℤ) : SL(2, ℤ) := ⟨!![0, -1; 1, s], by norm_num [Matrix.det_fin_two_of]⟩

/-- An integral matrix representing the normalized primitive column associated to a root. -/
def gl (l : ℤ) : SL(2, ℤ) := ⟨!![l, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩

theorem V_zero : V 0 = S := by decide
theorem V_one : V 1 = S * T := by decide

@[simp] theorem V_00 (s : ℤ) : (V s) 0 0 = 0 := rfl
@[simp] theorem V_01 (s : ℤ) : (V s) 0 1 = -1 := rfl
@[simp] theorem V_10 (s : ℤ) : (V s) 1 0 = 1 := rfl
@[simp] theorem V_11 (s : ℤ) : (V s) 1 1 = s := rfl
@[simp] theorem gl_00 (l : ℤ) : (gl l) 0 0 = l := rfl
@[simp] theorem gl_01 (l : ℤ) : (gl l) 0 1 = -1 := rfl
@[simp] theorem gl_10 (l : ℤ) : (gl l) 1 0 = 1 := rfl
@[simp] theorem gl_11 (l : ℤ) : (gl l) 1 1 = 0 := rfl

theorem inv_mul_lower (g h : SL(2, ℤ)) :
    (g⁻¹ * h) 1 0 = g 0 0 * h 1 0 - g 1 0 * h 0 0 := by
  simp [coe_mul, coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem V_mul_00 (s : ℤ) (g : SL(2, ℤ)) : (V s * g) 0 0 = -g 1 0 := by
  simp [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem V_mul_10 (s : ℤ) (g : SL(2, ℤ)) : (V s * g) 1 0 = g 0 0 + s * g 1 0 := by
  simp [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

variable (N : ℕ)

/-- The original level-coset space carrying the elliptic action. -/
abbrev X : Type := SL(2, ℤ) ⧸ Gamma0 N

theorem mk_eq_mk_iff (g h : SL(2, ℤ)) :
    ((g : X N) = (h : X N)) ↔ ((g 0 0 : ℤ) : ZMod N) * (h 1 0 : ℤ) - (g 1 0 : ℤ) * (h 0 0 : ℤ) = 0 := by
  rw [QuotientGroup.eq, Gamma0_mem, inv_mul_lower]
  push_cast
  exact Iff.rfl

theorem fixed_iff (s : ℤ) (g : SL(2, ℤ)) :
    V s • (g : X N) = (g : X N) ↔
      ((g 0 0 : ℤ) : ZMod N) ^ 2 + (s : ZMod N) * (g 0 0 : ℤ) * (g 1 0 : ℤ)
        + ((g 1 0 : ℤ) : ZMod N) ^ 2 = 0 := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, eq_comm, mk_eq_mk_iff, V_mul_00, V_mul_10]
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- The literal quadratic roots over the original residue ring. -/
abbrev Roots (s : ℤ) : Type := {x : ZMod N // x ^ 2 + (s : ZMod N) * x + 1 = 0}

/-- Fixed cosets of the actual integral elliptic companion matrix. -/
abbrev Fixed (s : ℤ) : Type := {y : X N // V s • y = y}

variable [NeZero N]

theorem cast_val (x : ZMod N) : (((x.val : ℕ) : ℤ) : ZMod N) = x := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Send a literal quadratic residue root to its original fixed level coset. -/
noncomputable def toFixed (s : ℤ) (x : Roots N s) : Fixed N s :=
  ⟨(gl (x.1.val : ℤ) : X N), by
    rw [fixed_iff]
    simp only [gl_00, gl_10, cast_val, Int.cast_one, mul_one, one_pow]
    exact x.2⟩

theorem toFixed_injective (s : ℤ) : Function.Injective (toFixed N s) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  have h' := congr_arg (fun z : Fixed N s => z.1) h
  simp only [toFixed] at h'
  rw [mk_eq_mk_iff] at h'
  simp only [gl_00, gl_10, cast_val, Int.cast_one, mul_one, one_mul] at h'
  exact Subtype.ext (sub_eq_zero.mp h')

theorem toFixed_surjective (s : ℤ) : Function.Surjective (toFixed N s) := by
  rintro ⟨y, hy⟩
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [fixed_iff] at hy

    have hdet : ((g 0 0 : ℤ) : ZMod N) * ((g 1 1 : ℤ) : ZMod N)
        - ((g 0 1 : ℤ) : ZMod N) * ((g 1 0 : ℤ) : ZMod N) = 1 := by
      have h := Matrix.det_fin_two (g : Matrix (Fin 2) (Fin 2) ℤ)
      rw [g.det_coe] at h
      have h' := congrArg (Int.cast (R := ZMod N)) h
      push_cast at h'
      exact h'.symm
    set a : ZMod N := ((g 0 0 : ℤ) : ZMod N)
    set b : ZMod N := ((g 0 1 : ℤ) : ZMod N)
    set c : ZMod N := ((g 1 0 : ℤ) : ZMod N)
    set d : ZMod N := ((g 1 1 : ℤ) : ZMod N)

    set w : ZMod N := -((s : ZMod N) * a + c) * d ^ 2 - 2 * a * b * d + b ^ 2 * c
    have hcw : c * w = 1 := by
      linear_combination (a * d - b * c + 1) * hdet - d ^ 2 * hy
    refine ⟨⟨a * w, ?_⟩, ?_⟩
    · linear_combination w ^ 2 * hy - ((s : ZMod N) * a * w + 1 + c * w) * hcw
    · apply Subtype.ext
      simp only [toFixed]
      rw [mk_eq_mk_iff]
      simp only [gl_00, gl_10, cast_val, Int.cast_one, one_mul]
      linear_combination a * hcw

theorem card_fixed_eq (s : ℤ) : Nat.card (Fixed N s) = Nat.card (Roots N s) :=
  (Nat.card_congr (Equiv.ofBijective _ ⟨toFixed_injective N s, toFixed_surjective N s⟩)).symm

theorem card_fixed_S :
    Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x} =
      SourceLevelProjective.nuTwo N := by
  have h : Nat.card {y : X N // S • y = y} = Nat.card (Roots N 0) := by
    rw [← V_zero]; exact card_fixed_eq N 0
  refine h.trans ?_
  unfold SourceLevelProjective.nuTwo
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp)

theorem card_fixed_ST :
    Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N //
        (ModularGroup.S * ModularGroup.T) • x = x} =
      SourceLevelProjective.nuThree N := by
  have h : Nat.card {y : X N // (S * T) • y = y} = Nat.card (Roots N 1) := by
    rw [← V_one]; exact card_fixed_eq N 1
  refine h.trans ?_
  unfold SourceLevelProjective.nuThree
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp)

end
end Dubon2026.SourceElliptic
