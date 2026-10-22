import Dubon2026.SourceTateModule
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Module.Torsion.Basic

/-! DUB-17/18 -> actual Tate Galois continuity -> finite-level congruences.
The kernel of the n-th genuine torsion projection equals the n-th p-adic
ideal power times the Tate module. Shifting a sequence constructs division
by p^n, so no completeness or projection-surjectivity premise is supplied.
Adapt the necessary projection argument from the pinned Apache-2.0 FLT source.
-/
namespace Dubon2026.TateModule
noncomputable section
open IsLocalRing
variable {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M]

theorem smul_apply_eq_zero_of_mem_span {n : ℕ} {a : ℤ_[p]}
    (ha : a ∈ Ideal.span {(p : ℤ_[p]) ^ n}) (x : TateModule p M) :
    ((a • x : TateModule p M) : ℕ → M) n = 0 := by
  rw [smul_apply]
  have h : ((a.appr n : ℕ) : ZMod (p ^ n)) = ((0 : ℕ) : ZMod (p ^ n)) := by
    rw [← toZModPow_eq_appr, Nat.cast_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact ha
  rw [natCast_smul_eq_of_zmod_eq (torsion x n) h, Nat.cast_zero, zero_smul]

variable (p M) in

/-- The n-th torsion coordinate of a compatible sequence. -/
def proj (n : ℕ) : TateModule p M →+ M where
  toFun x := (x : ℕ → M) n
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Fact p.Prime] in
@[simp] theorem proj_apply (n : ℕ) (x : TateModule p M) : proj p M n x = (x : ℕ → M) n := rfl

omit [Fact p.Prime] in
theorem torsionBy_proj (n : ℕ) (x : TateModule p M) : ((p ^ n : ℕ) : ℤ) • proj p M n x = 0 :=
  torsion x n

omit [Fact p.Prime] in
theorem proj_mem_torsionBy (n : ℕ) (x : TateModule p M) :
    proj p M n x ∈ Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ) :=
  (Submodule.mem_torsionBy_iff _ _).2 (torsion x n)

/-- Shifting a sequence whose n-th coordinate vanishes divides it by p^n. -/
def shiftOfProjEqZero (n : ℕ) (x : TateModule p M) (hx : proj p M n x = 0) : TateModule p M :=
  ⟨fun m => (x : ℕ → M) (m + n), fun m =>
    ⟨by
      show ((p ^ m : ℕ) : ℤ) • (x : ℕ → M) (m + n) = 0
      rw [Nat.add_comm, compat_pow x n m]; exact hx,
     by
      show ((p : ℕ) : ℤ) • (x : ℕ → M) (m + 1 + n) = (x : ℕ → M) (m + n)
      rw [Nat.add_right_comm]; exact compat x (m + n)⟩⟩

theorem pow_smul_shiftOfProjEqZero (n : ℕ) (x : TateModule p M) (hx : proj p M n x = 0) :
    ((p : ℤ_[p]) ^ n) • shiftOfProjEqZero n x hx = x := by
  refine Subtype.ext (funext fun m => ?_)
  rw [← Nat.cast_pow, natCast_padicInt_smul_apply]
  exact compat_pow x m n

theorem proj_eq_zero_iff (n : ℕ) (x : TateModule p M) :
    proj p M n x = 0 ↔ x ∈ (maximalIdeal ℤ_[p] ^ n) • (⊤ : Submodule ℤ_[p] (TateModule p M)) := by
  constructor
  · intro hx
    rw [← pow_smul_shiftOfProjEqZero n x hx]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  · intro hx
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow] at hx
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y z hy hz => ?_)
    · exact smul_apply_eq_zero_of_mem_span ha y
    · rw [map_add, hy, hz, add_zero]


end
end Dubon2026.TateModule
