import Dubon2026.SourceCurveNormFiber
import Dubon2026.SourceCurvePicardPullback

/-! DUB-17/18 -> original Picard Hecke correspondence -> divisor norm
pushforward. The actual map of places sums coefficients over each fiber.
For the residue-degree-one original geometric fields, this is precisely
the source pushforward. The proved norm/order identity preserves principal
divisors and hence constructs the map on actual degree-zero classes.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

namespace Divisor
variable (F)

/-- Sum divisor coefficients under restriction, for residue-degree-one pushforward. -/
def geometricPushforward : Divisor K E →+ Divisor K F :=
  Finsupp.mapDomain.addMonoidHom (fun w : Place K E => w.restrict F)

omit [FiniteDimensional F E] in
theorem geometricPushforward_single (w : Place K E) (n : ℤ) :
    geometricPushforward F (Finsupp.single w n) = Finsupp.single (w.restrict F) n :=
  Finsupp.mapDomain_single

omit [FiniteDimensional F E] in
theorem geometricPushforward_apply (D : Divisor K E) (v : Place K F) :
    geometricPushforward F D v =
      ∑ᶠ w : {w : Place K E // w.restrict F = v}, D w.1 := by
  classical
  change Finsupp.mapDomain (fun w : Place K E => w.restrict F) D v = _
  simp only [Finsupp.mapDomain, Finsupp.sum, Finset.sum_apply', Finsupp.single_apply,
    Finset.sum_ite, Finset.sum_const_zero, add_zero]
  symm
  rw [finsum_subtype_eq_finsum_cond]
  apply finsum_cond_eq_sum_of_cond_iff
  intro w hw
  simp only [Finset.mem_filter, Finsupp.mem_support_iff]
  exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩

omit [FiniteDimensional F E] in
theorem degree_geometricPushforward
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (D : Divisor K E) : degree (geometricPushforward F D) = degree D := by
  have hF1 (v : Place K F) : Module.finrank K v.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (hF v)
  have hE1 (w : Place K E) : Module.finrank K w.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (hE w)
  induction D using Finsupp.induction with
  | zero => simp
  | single_add w n D _ _ ih =>
    rw [map_add, map_add, map_add, ih, geometricPushforward_single,
      degree_single, degree_single, hF1, hE1]

omit [FiniteDimensional F E] in
theorem geometricPushforward_mem_degZero
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {D : Divisor K E} (hD : D ∈ degZero) : geometricPushforward F D ∈ degZero := by
  change degree (geometricPushforward F D) = 0
  rw [degree_geometricPushforward F hF hE]
  exact hD

variable [CharZero F]

theorem isPrincipal_geometricPushforward
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {D : Divisor K E} (hD : IsPrincipal D) : IsPrincipal (geometricPushforward F D) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨Algebra.norm F f, Algebra.norm_ne_zero_iff.mpr hf, fun v => ?_⟩
  rw [geometricPushforward_apply, v.ord_norm_eq_sum_fiber (hF v) hE hf]
  exact finsum_congr fun w => hD w.1

end Divisor
namespace Pic0
variable (F) [CharZero F]
variable (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
variable (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))

/-- Pushforward of actual geometric degree-zero divisor classes via the field norm. -/
def geometricPushforward : Pic0 K E →+ Pic0 K F :=
  QuotientAddGroup.map _ _
    (((Divisor.geometricPushforward F).comp Divisor.degZero.subtype).codRestrict Divisor.degZero
      (fun D => Divisor.geometricPushforward_mem_degZero F hF hE D.2)) (by
        rintro ⟨D, hD0⟩ hD
        exact Divisor.isPrincipal_geometricPushforward F hF hE hD)

theorem geometricPushforward_mk (D : Divisor.degZero (K := K) (F := E)) :
    geometricPushforward F hF hE (mk D) =
      mk ⟨Divisor.geometricPushforward F D.val,
        Divisor.geometricPushforward_mem_degZero F hF hE D.2⟩ := rfl

end Pic0
end
end Dubon2026.SourceCurve
