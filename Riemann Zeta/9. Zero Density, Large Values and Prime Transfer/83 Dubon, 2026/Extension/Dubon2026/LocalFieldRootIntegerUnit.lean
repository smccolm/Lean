import Dubon2026.LocalFieldIntegerUnitOrderKernel

/-! # Original field roots of unity come from actual integer-ring units

The proved original order homomorphism kills finite-order field units.
Its actual kernel theorem constructs the required original integer unit.
This discharges the representation premise in the unramified cyclotomic
Frobenius formula serving DUB-17's principal product.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- An original field root of nonzero order is the literal image of a constructed integer unit of the same order. -/
theorem localFieldRoot_exists_integer_unit {n : ℕ} [NeZero n] (ζ : K) (hζ : ζ ^ n = 1) :
    ∃ u : 𝒪[K]ˣ, u ^ n = 1 ∧ algebraMap 𝒪[K] K (u : 𝒪[K]) = ζ := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne n)] at hζ
    exact zero_ne_one hζ
  let v := Units.mk0 ζ hζ0
  have hv : v ^ n = 1 := by
    apply Units.ext
    simpa [v] using hζ
  have ht : n • localFieldUnitOrder K (Additive.ofMul v) = 0 := by
    rw [← map_nsmul]
    change localFieldUnitOrder K (Additive.ofMul (v ^ n)) = 0
    rw [hv]
    exact map_zero _
  have hz : localFieldUnitOrder K (Additive.ofMul v) = 0 := by
    have hm : (n : ℤ) * localFieldUnitOrder K (Additive.ofMul v) = 0 := by
      simpa only [nsmul_eq_mul] using ht
    exact (mul_eq_zero.mp hm).resolve_left (Int.natCast_ne_zero.mpr (NeZero.ne n))
  obtain ⟨u, hu⟩ := (localFieldUnitOrder_eq_zero_iff_integer_unit K v).mp hz
  have he : algebraMap 𝒪[K] K (u : 𝒪[K]) = ζ := congrArg (fun w : Kˣ => (w : K)) hu
  refine ⟨u, ?_, he⟩
  apply Units.ext
  apply Subtype.ext
  change algebraMap 𝒪[K] K ((u : 𝒪[K]) ^ n) = algebraMap 𝒪[K] K 1
  rw [map_pow, he, hζ, map_one]

end
end Dubon2026
