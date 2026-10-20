import Dubon2026.CMFiniteAdelicPairing
import Dubon2026.NumberFieldAdelicLattice
import Dubon2026.NumberFieldPositiveIntegralMultiple

/-! # A uniform integral pairing on the actual CM adelic lattices

A positive rational integer clearing only the fixed source Hermitian
matrix makes its pairing integral on every actual unitary adelic lattice.
The unitary equation, not a separately supplied integrality certificate,
transports this property. This is the uniform integrality input for
DUB-17's integral trace-lattice class bound.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped NumberField

attribute [local instance] cmFiniteAdeleStarRing

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A scalar clearing the fixed matrix makes its actual adelic pairing integral on integral vectors. -/
theorem cmFiniteAdelicPairing_scaled_integral (H : Matrix ι ι K) (d : ℤ)
    (hH : ∀ i j, IsIntegral ℤ (d • H i j))
    (x y : ι → FiniteAdeleRing (𝓞 K) K)
    (hx : ∀ i, x i ∈ numberFieldIntegralFiniteAdeles K)
    (hy : ∀ i, y i ∈ numberFieldIntegralFiniteAdeles K) :
    d • dotProduct (star x)
      (((algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H).mulVec y) ∈
        numberFieldIntegralFiniteAdeles K := by
  change d • (∑ i, star (x i) * (∑ j,
    algebraMap K (FiniteAdeleRing (𝓞 K) K) (H i j) * y j)) ∈ _
  rw [zsmul_eq_mul, Finset.mul_sum]
  apply (numberFieldIntegralFiniteAdeles K).sum_mem
  intro i _
  rw [← mul_assoc, Finset.mul_sum]
  apply (numberFieldIntegralFiniteAdeles K).sum_mem
  intro j _
  have hHij : (d : FiniteAdeleRing (𝓞 K) K) *
      algebraMap K (FiniteAdeleRing (𝓞 K) K) (H i j) ∈ numberFieldIntegralFiniteAdeles K := by
    simpa only [zsmul_eq_mul, map_mul, map_intCast] using
      (numberFieldFiniteAdele_integral_iff K _).mpr (hH i j)
  have h := (numberFieldIntegralFiniteAdeles K).mul_mem
    ((numberFieldIntegralFiniteAdeles K).mul_mem (cmFiniteAdele_star_integral K (hx i)) hHij) (hy j)
  convert h using 1
  ring

/-- The actual unitary equation makes the fixed scaled pairing integral on each attached lattice. -/
theorem cmAdelicLattice_pairing_integral (H : Matrix ι ι K) (d : ℤ)
    (hH : ∀ i j, IsIntegral ℤ (d • H i j))
    (g : cmFiniteAdelicUnitaryGroup K H)
    (x y : numberFieldAdelicLattice K ι g.val) :
    IsIntegral ℤ (d • dotProduct (star x.val) (H.mulVec y.val)) := by
  let px := numberFieldAdelicVectorMap K ι x.val
  let py := numberFieldAdelicVectorMap K ι y.val
  have hx := (numberFieldAdelicLattice_mem_iff K ι g.val x.val).mp x.property
  have hy := (numberFieldAdelicLattice_mem_iff K ι g.val y.val).mp y.property
  have h := cmFiniteAdelicPairing_scaled_integral K H d hH
    ((g.val⁻¹).val.mulVec px) ((g.val⁻¹).val.mulVec py) hx hy
  have hp := cmFiniteAdelicPairing_preserved K H g⁻¹ px py
  change dotProduct (star ((g.val⁻¹).val.mulVec px))
    (((algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H).mulVec ((g.val⁻¹).val.mulVec py)) =
      dotProduct (star px) (((algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H).mulVec py) at hp
  rw [hp] at h
  change d • dotProduct (star (fun i => algebraMap K (FiniteAdeleRing (𝓞 K) K) (x.val i)))
    (((algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H).mulVec
      (fun i => algebraMap K (FiniteAdeleRing (𝓞 K) K) (y.val i))) ∈ _ at h
  rw [← cmFiniteAdelicPairing_principal K H x.val y.val] at h
  apply (numberFieldFiniteAdele_integral_iff K _).mp
  simpa only [zsmul_eq_mul, map_mul, map_intCast] using h

/-- One positive integer depending only on the fixed matrix works for every original unitary adelic lattice. -/
theorem cmAdelicLattice_exists_uniform_integral_pairing (H : Matrix ι ι K) :
    ∃ d : ℤ, 0 < d ∧ ∀ (g : cmFiniteAdelicUnitaryGroup K H)
      (x y : numberFieldAdelicLattice K ι g.val),
        IsIntegral ℤ (d • dotProduct (star x.val) (H.mulVec y.val)) := by
  obtain ⟨d, hd, hH⟩ := numberField_exists_positive_integral_multiple
    (fun ij : ι × ι => H ij.1 ij.2)
  exact ⟨d, hd, fun g x y => cmAdelicLattice_pairing_integral K H d
    (fun i j => hH (i, j)) g x y⟩

end
end Dubon2026
