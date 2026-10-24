import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! For the exceptional-fiber census, an action preserving every line in
the actual rank-two prime torsion must be scalar. This is the precise
linear-algebra input to the non-scalar elliptic automorphism argument.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the exceptional fixed-vcInvFun
subgroup-count source solutions. -/
namespace Dubon2026.SourceEllipticExceptional
section Scalar

variable {V : Type*} [AddCommGroup V]

theorem exists_common_scalar {p : ℕ} [Fact p.Prime] (e : ZMod p × ZMod p ≃+ V) (σ : V →+ V)
    (heig : ∀ v : V, ∃ a : ℤ, σ v = a • v) : ∃ c : ℤ, ∀ v : V, σ v = c • v := by
  obtain ⟨a, ha⟩ := heig (e (1, 0))
  obtain ⟨b, hb⟩ := heig (e (0, 1))
  obtain ⟨c, hc⟩ := heig (e (1, 1))
  have hsum : e (1, 1) = e (1, 0) + e (0, 1) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have key : c • e (1, 0) + c • e (0, 1) = a • e (1, 0) + b • e (0, 1) := by
    rw [← smul_add, ← hsum, ← hc, hsum, map_add, ha, hb]
  have key' : ((c : ZMod p), (c : ZMod p)) = ((a : ZMod p), (b : ZMod p)) := by
    apply e.injective
    have h1 : e ((c : ZMod p), (c : ZMod p)) = c • e (1, 0) + c • e (0, 1) := by
      rw [← map_zsmul, ← map_zsmul, ← map_add]; congr 1; ext <;> simp
    have h2 : e ((a : ZMod p), (b : ZMod p)) = a • e (1, 0) + b • e (0, 1) := by
      rw [← map_zsmul, ← map_zsmul, ← map_add]; congr 1; ext <;> simp
    rw [h1, h2, key]
  have hca : (c : ZMod p) = a := congrArg Prod.fst key'
  have hcb : (c : ZMod p) = b := congrArg Prod.snd key'
  have hpV : ∀ v : V, (p : ℤ) • v = 0 := by
    intro v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [← map_zsmul, show (p : ℤ) • w = 0 from ?_, map_zero]
    ext <;> simp [zsmul_eq_mul]
  have hzs : ∀ (m n : ℤ) (v : V), (m : ZMod p) = n → m • v = n • v := by
    intro m n v hmn
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub n m p).mp hmn.symm
    have : m = n + p * k := by linarith
    rw [this, add_zsmul, mul_comm, mul_zsmul, hpV, zsmul_zero, add_zero]
  refine ⟨c, fun v => ?_⟩
  obtain ⟨⟨s, t⟩, rfl⟩ := e.surjective v
  have hv : e (s, t) = (s.val : ℤ) • e (1, 0) + (t.val : ℤ) • e (0, 1) := by
    rw [← map_zsmul, ← map_zsmul, ← map_add]; congr 1; ext <;> simp
  rw [hv, map_add, map_zsmul, map_zsmul, ha, hb, smul_add, smul_comm c (s.val : ℤ), smul_comm c (t.val : ℤ),
    hzs a c _ hca.symm, hzs b c _ hcb.symm]

end Scalar
end Dubon2026.SourceEllipticExceptional
