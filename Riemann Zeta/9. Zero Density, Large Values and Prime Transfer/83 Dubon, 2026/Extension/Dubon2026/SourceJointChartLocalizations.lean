import Dubon2026.SourceJointChartIntegralAlgebras
import Dubon2026.SourceJointChartMonomialDenominators

/-! DUB-17/18 -> original-field Kummer power lifting -> genus inequality ->
common residue-chart constants. These localizations use denominators whose
reduction is a nonzero monomial. They provide the two charts and overlap
needed by the already proved idempotent gluing theorem. Adapted from
Apache-2.0 FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2;
native integral-closure algebras replace the external chart predicate. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))

/-- The integral chart localized at polynomials reducing to nonzero constants. -/
def Pg (g : F) (hg : ∀ i, g ∈ (R i).integers) : Subalgebra A F where
  carrier := {x | ∃ t : L[X], IsGoodAt A 0 t ∧ x * aeval g t ∈ Sg R g}
  mul_mem' := by
    rintro x y ⟨t, ht, hx⟩ ⟨s, hs, hy⟩
    refine ⟨t * s, by simpa using ht.mul hs, ?_⟩
    rw [map_mul, show x * y * (aeval g t * aeval g s) = (x * aeval g t) * (y * aeval g s) by ring]
    exact mul_mem hx hy
  one_mem' := ⟨1, IsGoodAt.one, by rw [one_mul, map_one]; exact one_mem _⟩
  add_mem' := by
    rintro x y ⟨t, ht, hx⟩ ⟨s, hs, hy⟩
    refine ⟨t * s, by simpa using ht.mul hs, ?_⟩
    rw [map_mul, show (x + y) * (aeval g t * aeval g s)
        = (x * aeval g t) * aeval g s + (y * aeval g s) * aeval g t by ring]
    exact add_mem (mul_mem hx (aeval_mem_Sg R hg hs.coeff_mem))
      (mul_mem hy (aeval_mem_Sg R hg ht.coeff_mem))
  zero_mem' := ⟨1, IsGoodAt.one, by rw [zero_mul]; exact zero_mem _⟩
  algebraMap_mem' := fun a =>
    ⟨1, IsGoodAt.one, by rw [map_one, mul_one]; exact (Sg R g).algebraMap_mem a⟩

/-- The chart overlap, allowing a nonzero monomial as reduced denominator. -/
def Ppp (f : F) (hf : ∀ i, f ∈ (R i).integers) : Subalgebra A F where
  carrier := {x | ∃ (t : L[X]) (d : ℕ), IsGoodAt A d t ∧ x * aeval f t ∈ Sg R f}
  mul_mem' := by
    rintro x y ⟨t, d, ht, hx⟩ ⟨s, d', hs, hy⟩
    refine ⟨t * s, d + d', ht.mul hs, ?_⟩
    rw [map_mul, show x * y * (aeval f t * aeval f s) = (x * aeval f t) * (y * aeval f s) by ring]
    exact mul_mem hx hy
  one_mem' := ⟨1, 0, IsGoodAt.one, by rw [one_mul, map_one]; exact one_mem _⟩
  add_mem' := by
    rintro x y ⟨t, d, ht, hx⟩ ⟨s, d', hs, hy⟩
    refine ⟨t * s, d + d', ht.mul hs, ?_⟩
    rw [map_mul, show (x + y) * (aeval f t * aeval f s)
        = (x * aeval f t) * aeval f s + (y * aeval f s) * aeval f t by ring]
    exact add_mem (mul_mem hx (aeval_mem_Sg R hf hs.coeff_mem))
      (mul_mem hy (aeval_mem_Sg R hf ht.coeff_mem))
  zero_mem' := ⟨1, 0, IsGoodAt.one, by rw [zero_mul]; exact zero_mem _⟩
  algebraMap_mem' := fun a =>
    ⟨1, 0, IsGoodAt.one, by rw [map_one, mul_one]; exact (Sg R f).algebraMap_mem a⟩

theorem Sg_le_Pg {g : F} (hg : ∀ i, g ∈ (R i).integers) : Sg R g ≤ Pg R g hg := fun x hx =>
  ⟨1, IsGoodAt.one, by rw [map_one, mul_one]; exact hx⟩

theorem Pg_le_Ppp {f : F} (hf : ∀ i, f ∈ (R i).integers) : Pg R f hf ≤ Ppp R f hf := fun x hx => by
  obtain ⟨t, ht, hx⟩ := hx
  exact ⟨t, 0, ht, hx⟩

theorem mem_Ppp_of_mul_mul_pow_mem {f : F} (hf : ∀ i, f ∈ (R i).integers) {x : F} {t : L[X]} {d : ℕ}
    (ht : IsGoodAt A d t) (m : ℕ) (hx : x * aeval f t * f ^ m ∈ Sg R f) : x ∈ Ppp R f hf := by
  refine ⟨t * X ^ m, d + m, ht.mul (IsGoodAt.X_pow m), ?_⟩
  rwa [map_mul, map_pow, aeval_X, ← mul_assoc]

theorem Pinv_le_Ppp {f : F} (hf : ∀ i, f ∈ (R i).integers) (hf' : ∀ i, f⁻¹ ∈ (R i).integers)
    (hf0 : f ≠ 0) (hS' : ∀ u ∈ Sg R f⁻¹, ∃ m : ℕ, u * f ^ m ∈ Sg R f) :
    Pg R f⁻¹ hf' ≤ Ppp R f hf := by
  rintro x ⟨t, ht, hx⟩
  obtain ⟨m, hm⟩ := hS' _ hx
  refine mem_Ppp_of_mul_mul_pow_mem R hf (ht.reflect t.natDegree) m ?_
  rw [aeval_reflect_eq hf0 t le_rfl, show x * (aeval f⁻¹ t * f ^ t.natDegree) * f ^ m
      = (x * aeval f⁻¹ t * f ^ m) * f ^ t.natDegree by ring]
  exact mul_mem hm (pow_mem (self_mem_Sg R hf) _)

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
