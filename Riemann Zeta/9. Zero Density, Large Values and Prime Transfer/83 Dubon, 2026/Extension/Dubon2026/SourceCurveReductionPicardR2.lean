import Dubon2026.SourceCurveConstantReductionR2
import Dubon2026.SourceCurveDivisorDegree
import Dubon2026.SourceCurveTranscendence

/-! DUB-17/18 -> original Frobenius/inertia -> reduction on genuine Picard
groups. The actual principal-divisor compatibility and constant scaling in a
constant reduction make its finite-support pushforward descend to degree-zero
divisor classes. No abstract homomorphism of Picard groups is postulated.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_AlgebraicCurve_ConstantReduction. Existing place orders,
divisor degree and quotient-group definitions are reused. -/
namespace Dubon2026.SourceCurve.ConstantReduction
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (R : ConstantReduction A F Fbar)

theorem mapDomain_mem_principal {D : Divisor L F}
    (hD : D ∈ Divisor.principal (K := L) (F := F)) :
    Finsupp.mapDomain R.placeMap D ∈ Divisor.principal (K := ResidueField A) (F := Fbar) := by
  obtain ⟨f, hf0, hDf⟩ := hD
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f hf0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hres
    have hz : (⟨(0 : L) • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [hz, map_zero]
  refine ⟨R.residue ⟨c • f, hc⟩, hres, fun Q => ?_⟩
  apply R.mapDomain_placeMap ⟨c • f, hc⟩ hres D
  intro P
  change D P = P.ord (c • f)
  rw [hDf P, Algebra.smul_def, P.ord_mul ((map_ne_zero _).mpr hc0) hf0,
    P.ord_eq_zero_of_isAlgebraic (isAlgebraic_algebraMap c), zero_add]

theorem degree_mapDomain (D : Divisor L F) :
    Divisor.degree (Finsupp.mapDomain R.placeMap D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add P n D _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
      Divisor.degree_single, Divisor.degree_single, R.deg_placeMap]

theorem mapDomain_mem_degZero {D : Divisor L F}
    (hD : D ∈ Divisor.degZero (K := L) (F := F)) :
    Finsupp.mapDomain R.placeMap D ∈ Divisor.degZero (K := ResidueField A) (F := Fbar) := by
  change Divisor.degree (Finsupp.mapDomain R.placeMap D) = 0
  rw [R.degree_mapDomain]
  exact hD

/-- Literal finite-support divisor pushforward under the reduction map of places. -/
def divMap : Divisor L F →+ Divisor (ResidueField A) Fbar :=
  Finsupp.mapDomain.addMonoidHom R.placeMap

/-- The divisor pushforward restricted to degree-zero divisors. -/
def degZeroMap :
    Divisor.degZero (K := L) (F := F) →+ Divisor.degZero (K := ResidueField A) (F := Fbar) :=
  (R.divMap.comp (Divisor.degZero (K := L) (F := F)).subtype).codRestrict _ fun D =>
    R.mapDomain_mem_degZero D.2

/-- The induced additive map on actual degree-zero divisor classes. -/
def pic0Map : Pic0 L F →+ Pic0 (ResidueField A) Fbar :=
  QuotientAddGroup.map _ _ R.degZeroMap (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact R.mapDomain_mem_principal hD)

theorem pic0Map_mk (D : Divisor.degZero (K := L) (F := F)) :
    R.pic0Map (Pic0.mk D) = Pic0.mk (R.degZeroMap D) := rfl

theorem pic0Map_mem_torsion {n : ℕ} {x : Pic0 L F} (hx : x ∈ Pic0.torsion n) :
    R.pic0Map x ∈ Pic0.torsion n := by
  rw [Pic0.mem_torsion_iff] at hx ⊢
  rw [← map_nsmul, hx, map_zero]

end
end Dubon2026.SourceCurve.ConstantReduction
