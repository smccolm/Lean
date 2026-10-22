import Dubon2026.SourceCurveDivisorPullback

/-! DUB-17/18 -> original Picard Hecke correspondence -> actual Picard
pullback. Existing finite fiber ramification sums prove the degree formula
when the actual residue fields equal the constants. The original modular
fields supply these residue identifications. No degree or principal-divisor
preservation premise is assumed in the constructed Picard map.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem Place.sum_restrictionFiber_orders (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField)) :
    ∑ w ∈ v.restrictionFiber E,
      w.ord (algebraMap F E (w.restrict F).uniformizer) = (Module.finrank F E : ℤ) := by
  classical
  have hs : (v.restrictionFiber E : Set (Place K E)) = {w | w.restrict F = v} := by
    ext w
    exact Place.mem_restrictionFiber
  rw [← finsum_mem_coe_finset, hs, ← finsum_set_coe_eq_finsum_mem]
  convert v.sum_fiber_ramification hbase htop using 1
  apply finsum_congr
  intro w
  rw [w.property]

namespace Divisor

theorem degree_finitePullback
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (D : Divisor K F) :
    degree (finitePullback E D) = (Module.finrank F E : ℤ) * degree D := by
  classical
  have hF1 (v : Place K F) : Module.finrank K v.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (hF v)
  have hE1 (w : Place K E) : Module.finrank K w.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (hE w)
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [map_add, map_add, map_add, mul_add, ih]
    congr 1
    rw [finitePullback_single, map_sum, degree_single, hF1, Nat.cast_one, mul_one]
    simp_rw [degree_single, hE1, Nat.cast_one, mul_one]
    rw [← Finset.mul_sum, v.sum_restrictionFiber_orders (hF v) hE, mul_comm]

theorem finitePullback_mem_degZero
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {D : Divisor K F} (hD : D ∈ degZero) : finitePullback E D ∈ degZero := by
  change degree (finitePullback E D) = 0
  rw [degree_finitePullback hF hE, (show degree D = 0 from hD), mul_zero]

end Divisor
namespace Pic0
variable (E)
variable (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
variable (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))

/-- The actual finite-extension pullback on degree-zero divisor classes. -/
def finitePullback : Pic0 K F →+ Pic0 K E :=
  QuotientAddGroup.map _ _
    (((Divisor.finitePullback E).comp Divisor.degZero.subtype).codRestrict Divisor.degZero
      (fun D => Divisor.finitePullback_mem_degZero hF hE D.2)) (by
        rintro ⟨D, hD0⟩ hD
        exact Divisor.isPrincipal_finitePullback E hD)

theorem finitePullback_mk (D : Divisor.degZero (K := K) (F := F)) :
    finitePullback E hF hE (mk D) =
      mk ⟨Divisor.finitePullback E D.val, Divisor.finitePullback_mem_degZero hF hE D.2⟩ := rfl

end Pic0
end
end Dubon2026.SourceCurve
