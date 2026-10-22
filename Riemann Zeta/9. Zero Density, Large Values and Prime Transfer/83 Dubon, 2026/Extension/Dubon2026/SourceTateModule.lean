import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Module.ZMod

/-! DUB-17/18 -> original Jacobian Tate realization -> actual compatible torsion
sequences. Adapt the necessary additive and p-adic module core from the pinned
Apache-2.0 FLT source. Native p-adic residue homomorphisms give scalar coherence.
No finiteness, rank, Hecke, Frobenius or realization claim is built into this object.
-/
namespace Dubon2026
/-- Compatible sequences of p-power torsion points in the given additive group. -/
def TateModule (p : ℕ) (M : Type*) [AddCommGroup M] : AddSubgroup (ℕ → M) where
  carrier := {x | ∀ n, ((p ^ n : ℕ) : ℤ) • x n = 0 ∧ ((p : ℕ) : ℤ) • x (n + 1) = x n}
  add_mem' := fun {x y} hx hy n =>
    ⟨by rw [Pi.add_apply, smul_add, (hx n).1, (hy n).1, add_zero],
     by rw [Pi.add_apply, Pi.add_apply, smul_add, (hx n).2, (hy n).2]⟩
  zero_mem' := fun n => ⟨smul_zero _, by rw [Pi.zero_apply, Pi.zero_apply, smul_zero]⟩
  neg_mem' := fun {x} hx n =>
    ⟨by rw [Pi.neg_apply, smul_neg, (hx n).1, neg_zero],
     by rw [Pi.neg_apply, Pi.neg_apply, smul_neg, (hx n).2]⟩

namespace TateModule

variable {p : ℕ} {M : Type*} [AddCommGroup M]

theorem torsion (x : TateModule p M) (n : ℕ) : ((p ^ n : ℕ) : ℤ) • (x : ℕ → M) n = 0 := (x.2 n).1

theorem compat (x : TateModule p M) (n : ℕ) : ((p : ℕ) : ℤ) • (x : ℕ → M) (n + 1) = (x : ℕ → M) n :=
  (x.2 n).2

theorem compat_pow (x : TateModule p M) (n k : ℕ) :
    ((p ^ k : ℕ) : ℤ) • (x : ℕ → M) (n + k) = (x : ℕ → M) n := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_one, one_smul, Nat.add_zero]
  | succ k ih =>
    rw [pow_succ, Nat.cast_mul, mul_smul]
    show ((p ^ k : ℕ) : ℤ) • (((p : ℕ) : ℤ) • (x : ℕ → M) ((n + k) + 1)) = _
    rw [compat, ih]

@[simp] theorem coe_add (x y : TateModule p M) : ((x + y : TateModule p M) : ℕ → M) = x + y := rfl
@[simp] theorem coe_zero : ((0 : TateModule p M) : ℕ → M) = 0 := rfl
@[simp] theorem coe_neg (x : TateModule p M) : ((-x : TateModule p M) : ℕ → M) = -x := rfl
@[simp] theorem coe_sub (x y : TateModule p M) : ((x - y : TateModule p M) : ℕ → M) = x - y := rfl

theorem apply_zero (x : TateModule p M) : (x : ℕ → M) 0 = 0 := by
  have h := torsion x 0
  rwa [pow_zero, Nat.cast_one, one_smul] at h

theorem natCast_smul_eq_mod {n c : ℕ} {m : M} (hm : ((p ^ n : ℕ) : ℤ) • m = 0) :
    (c : ℤ) • m = ((c % p ^ n : ℕ) : ℤ) • m := by
  conv_lhs => rw [← Nat.div_add_mod c (p ^ n)]
  rw [Nat.cast_add, add_smul, Nat.cast_mul, mul_comm, mul_smul, hm, smul_zero, zero_add]

theorem natCast_smul_eq_of_zmod_eq {n c d : ℕ} {m : M} (hm : ((p ^ n : ℕ) : ℤ) • m = 0)
    (h : (c : ZMod (p ^ n)) = d) : (c : ℤ) • m = (d : ℤ) • m := by
  rw [natCast_smul_eq_mod hm, natCast_smul_eq_mod (c := d) hm, (ZMod.natCast_eq_natCast_iff' c d _).1 h]

variable [Fact p.Prime]

theorem toZModPow_eq_appr (n : ℕ) (a : ℤ_[p]) : PadicInt.toZModPow n a = (a.appr n : ZMod (p ^ n)) := rfl

theorem appr_succ_smul_eq (a : ℤ_[p]) (x : TateModule p M) (n : ℕ) :
    ((a.appr (n + 1) : ℕ) : ℤ) • (x : ℕ → M) n = ((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n := by
  refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
  rw [← toZModPow_eq_appr, ← PadicInt.zmod_cast_comp_toZModPow n (n + 1) n.le_succ, RingHom.comp_apply,
    toZModPow_eq_appr, ZMod.castHom_apply, ZMod.cast_natCast (pow_dvd_pow p n.le_succ)]

noncomputable instance instSMul : SMul ℤ_[p] (TateModule p M) :=
  ⟨fun a x => ⟨fun n => ((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n, fun n =>
    ⟨by rw [smul_comm, torsion, smul_zero], by rw [smul_comm, compat, appr_succ_smul_eq]⟩⟩⟩

@[simp] theorem smul_apply (a : ℤ_[p]) (x : TateModule p M) (n : ℕ) :
    ((a • x : TateModule p M) : ℕ → M) n = ((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n := rfl

noncomputable instance instModule : Module ℤ_[p] (TateModule p M) where
  one_smul x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply]
    have h : (((1 : ℤ_[p]).appr n : ℕ) : ZMod (p ^ n)) = ((1 : ℕ) : ZMod (p ^ n)) := by
      rw [← toZModPow_eq_appr, map_one, Nat.cast_one]
    rw [natCast_smul_eq_of_zmod_eq (torsion x n) h, Nat.cast_one, one_smul]
  mul_smul a b x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, smul_apply, smul_apply, smul_smul, ← Nat.cast_mul]
    refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
    rw [← toZModPow_eq_appr, map_mul, toZModPow_eq_appr, toZModPow_eq_appr, Nat.cast_mul]
  smul_zero a := Subtype.ext (funext fun n => by rw [smul_apply, coe_zero, Pi.zero_apply, smul_zero])
  smul_add a x y := Subtype.ext (funext fun n => by
    rw [smul_apply, coe_add, Pi.add_apply, smul_add, coe_add, Pi.add_apply, smul_apply, smul_apply])
  add_smul a b x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, coe_add, Pi.add_apply, smul_apply, smul_apply, ← add_smul, ← Nat.cast_add]
    refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
    rw [← toZModPow_eq_appr, map_add, toZModPow_eq_appr, toZModPow_eq_appr, Nat.cast_add]
  zero_smul x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, coe_zero, Pi.zero_apply]
    have h : (((0 : ℤ_[p]).appr n : ℕ) : ZMod (p ^ n)) = ((0 : ℕ) : ZMod (p ^ n)) := by
      rw [← toZModPow_eq_appr, map_zero, Nat.cast_zero]
    rw [natCast_smul_eq_of_zmod_eq (torsion x n) h, Nat.cast_zero, zero_smul]

theorem natCast_padicInt_smul_apply (c : ℕ) (x : TateModule p M) (n : ℕ) :
    (((c : ℤ_[p]) • x : TateModule p M) : ℕ → M) n = (c : ℤ) • (x : ℕ → M) n := by
  rw [smul_apply]
  refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
  rw [← toZModPow_eq_appr, map_natCast]


end TateModule
end Dubon2026
