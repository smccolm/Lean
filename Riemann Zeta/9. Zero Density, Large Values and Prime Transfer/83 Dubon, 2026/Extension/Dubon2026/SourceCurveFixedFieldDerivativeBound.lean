import Dubon2026.SourceCurveOrderResidue
import Dubon2026.SourceCurveCoordinateDerivation
import Dubon2026.SourceCurveIntegralDerivatives

/-! The derivative of an integral element of the inertia fixed field has
order at least that of the base parameter's derivative. The finite
induction uses the actual residue map and the fixed field's order gap.
This is hR/hR' of the FLT Galois wild different proof, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. The geometric order gap
is an explicit narrower input; its actual inertia consumer is still needed
for the DUB-17/18 wild genus comparison. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential IntermediateField
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField] [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem ordGe_coordinateDerivation_of_order_gap (Z : IntermediateField K F)
    (x : F) (hxZ : x ∈ Z) (hx : 0 < v.ord x)
    (hgap : ∀ z ∈ Z, v.ord x ∣ v.ord z)
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    {z : F} (hzZ : z ∈ Z) (hz : z ∈ v.toValuationSubring) :
    v.OrdGe (v.ord (v.coordinateDerivation x)) (v.coordinateDerivation z) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hgap' : ∀ z ∈ Z, v.OrdGe 1 z → v.OrdGe (v.ord x) z := by
    intro z hz h1
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ordGe_zero v _
    have hpos := h1.le_ord hz0
    obtain ⟨k, hk⟩ := hgap z hz
    refine Or.inr ?_
    rw [hk] at hpos ⊢
    have hkpos : 0 < k := by
      by_contra hn
      have : v.ord x * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx.le (by omega)
      omega
    nlinarith
  let d : ℤ := v.ord (v.coordinateDerivation x)
  have hregular : ∀ {f : F}, v.OrdGe 0 f → v.OrdGe 0 (v.coordinateDerivation f) := by
    intro f hf
    exact Or.inr (v.ord_nonneg_of_mem (v.differentialCoeff_D_mem_of_mem hf.mem_of_zero))
  have hd : 0 ≤ d := v.ord_nonneg_of_mem
    (v.differentialCoeff_D_mem_of_mem (v.mem_of_ord_nonneg hx.le))
  have hxge : v.OrdGe (v.ord x) x := Or.inr le_rfl
  have hxinv : v.OrdGe (-v.ord x) x⁻¹ := Or.inr (by rw [v.ord_inv])
  have hder : v.OrdGe d (v.coordinateDerivation x) := Or.inr le_rfl
  have hstep : ∀ n : ℕ, ∀ z ∈ Z, v.OrdGe 0 z →
      v.OrdGe (min (n : ℤ) d) (v.coordinateDerivation z) := by
    intro n
    induction n with
    | zero =>
      intro z _ hz
      exact (hregular hz).mono (min_le_left _ _)
    | succ n ih =>
      intro z hzZ hz
      obtain ⟨c, hc⟩ := v.exists_constant_of_ordGe_zero hres hz
      have hzcZ : z - algebraMap K F c ∈ Z := sub_mem hzZ (Z.algebraMap_mem c)
      have hzc := hgap' _ hzcZ hc
      let z' := (z - algebraMap K F c) * x⁻¹
      have hz'Z : z' ∈ Z := mul_mem hzcZ (inv_mem hxZ)
      have hz' : v.OrdGe 0 z' := by
        simpa only [add_neg_cancel] using hzc.mul hxinv
      have he : z = algebraMap K F c + x * z' := by
        dsimp [z']
        field_simp
        ring
      have heder : v.coordinateDerivation z =
          x * v.coordinateDerivation z' + z' * v.coordinateDerivation x := by
        conv_lhs => rw [he]
        rw [map_add, Derivation.map_algebraMap, zero_add, Derivation.leibniz]
        rfl
      rw [heder]
      refine OrdGe.add ?_ ?_
      · exact (hxge.mul (ih z' hz'Z hz')).mono (by
          push_cast
          rcases le_total (n : ℤ) d with hnd | hnd
          · rw [min_eq_left hnd]; omega
          · rw [min_eq_right hnd]; omega)
      · exact (hz'.mul hder).mono (by rw [zero_add]; exact min_le_right _ _)
  have h := hstep d.toNat z hzZ (Or.inr (v.ord_nonneg_of_mem hz))
  rwa [Int.toNat_of_nonneg hd, min_self] at h

end
end Dubon2026.SourceCurve.Place
