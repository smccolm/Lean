import Dubon2026.SourceCurveRiemannRochSpace

/-! DUB-17/18 -> function-field Riemann--Roch -> bounded global index.
Multiplication adds actual pole bounds, and multiplication by a nonzero
function shifts a divisor space by its principal divisor. These are the
selected product and shift arguments used by PoleDivisorPackage in
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem one_mem_lSpace_zero : (1 : F) ∈ LSpace (0 : Divisor K F) := by
  simpa using algebraMap_mem_lSpace_zero (K := K) (F := F) 1

theorem mul_mem_lSpace_add {D E : Divisor K F} {f g : F}
    (hf : f ∈ LSpace D) (hg : g ∈ LSpace E) :
    f * g ∈ LSpace (D + E) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul]; exact (LSpace _).zero_mem
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero]; exact (LSpace _).zero_mem
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun v => ?_
  rw [Finsupp.add_apply, neg_add, v.ord_mul hf0 hg0]
  exact add_le_add ((mem_lSpace_iff_ord.mp hf).resolve_left hf0 v)
    ((mem_lSpace_iff_ord.mp hg).resolve_left hg0 v)

theorem pow_mem_lSpace_nsmul {B : Divisor K F} {f : F} (hf : f ∈ LSpace B) (j : ℕ) :
    f ^ j ∈ LSpace (j • B) := by
  induction j with
  | zero => simpa using one_mem_lSpace_zero (K := K) (F := F)
  | succ j ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_lSpace_add ih hf

/-- Multiplication by the inverse function identifies spaces differing by its principal divisor. -/
def lSpaceShiftEquiv (D : Divisor K F) {g : F} (hg : g ≠ 0)
    {Dg : Divisor K F} (hDg : ∀ v, Dg v = v.ord g) :
    LSpace D ≃ₗ[K] LSpace (D + Dg) where
  toFun h := ⟨(h : F) * g⁻¹, by
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (h : F) 0 with hh0 | hh0
    · left; rw [hh0, zero_mul]
    · right; intro v
      rw [Finsupp.add_apply, hDg, v.ord_mul hh0 (inv_ne_zero hg), v.ord_inv]
      have := (mem_lSpace_iff_ord.mp h.2).resolve_left hh0 v
      linarith⟩
  invFun k := ⟨(k : F) * g, by
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (k : F) 0 with hk0 | hk0
    · left; rw [hk0, zero_mul]
    · right; intro v
      have := (mem_lSpace_iff_ord.mp k.2).resolve_left hk0 v
      rw [Finsupp.add_apply, hDg] at this
      rw [v.ord_mul hk0 hg]
      linarith⟩
  map_add' h₁ h₂ := by apply Subtype.ext; push_cast; ring
  map_smul' c h := by
    apply Subtype.ext
    simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
    ring
  left_inv h := by
    apply Subtype.ext
    show (h : F) * g⁻¹ * g = (h : F)
    rw [mul_assoc, inv_mul_cancel₀ hg, mul_one]
  right_inv k := by
    apply Subtype.ext
    show (k : F) * g * g⁻¹ = (k : F)
    rw [mul_assoc, mul_inv_cancel₀ hg, mul_one]


end
end Dubon2026.SourceCurve
