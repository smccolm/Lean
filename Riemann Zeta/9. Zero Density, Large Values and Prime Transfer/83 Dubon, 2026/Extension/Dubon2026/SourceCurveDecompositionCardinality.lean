import Dubon2026.SourceCurveDecompositionCenterStabilizer
import Dubon2026.SourceCurveFiberDegrees
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The cardinality of the actual valuation-ring decomposition group is
the actual normalized ramification order when both residue fields are
the algebraically closed constant field. The proof consumes the pinned
Dedekind Galois cardinality theorem through the proved chart-center group
identification. This removes a necessary group/order comparison in the
DUB-17/18 exceptional-fiber specialization; no ramification cardinality
certificate is a premise. -/
namespace Dubon2026.SourceCurve.Place
open IsDedekindDomain IsLocalRing
open scoped Pointwise
noncomputable section
variable {K F E : Type*} [Field K] [IsAlgClosed K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [IsGalois F E]

theorem decomposition_card_eq_uniformizer_order (w : Place K E)
    (hbase : Function.Bijective (algebraMap K (w.restrict F).ResidueField))
    (htop : Function.Bijective (algebraMap K w.ResidueField)) :
    Nat.card (w.toValuationSubring.decompositionSubgroup F) =
      (w.ord (algebraMap F E (w.restrict F).uniformizer)).toNat := by
  let v := w.restrict F
  let A := v.toValuationSubring
  let R := integralClosureAt E v
  let Q := fiberCenter (F := F) E (w := w) rfl
  let P := Q.asIdeal
  let m := maximalIdeal A
  letI := IsIntegralClosure.MulSemiringAction A F E R
  letI : IsGaloisGroup (E ≃ₐ[F] E) A R := IsGaloisGroup.of_isFractionRing _ _ _ F E
  haveI : P.IsPrime := Q.isPrime
  haveI : P.LiesOver m := fiberCenter_liesOver (F := F) (E := E) (w := w) rfl
  haveI : P.IsMaximal := Q.isMaximal
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  let e : K ≃ₐ[K] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId K _) hbase
  letI : IsAlgClosed (A ⧸ m) := ⟨fun q => by
    have h := (IsAlgClosed.splits (q.map e.symm.toRingHom)).map e.toRingHom
    have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ :=
      RingHom.ext e.apply_symm_apply
    rwa [Polynomial.map_map, he, Polynomial.map_id] at h⟩
  haveI : Module.Finite (A ⧸ m) (R ⧸ P) := inferInstance
  haveI : Algebra.IsSeparable (A ⧸ m) (R ⧸ P) := inferInstance
  have hplace : fiberPrimePlace E v Q = w :=
    fiberPrimePlace_fiberCenter (F := F) (w := w) rfl
  have hi : m.inertiaDeg P = 1 := by
    apply fiberPrime_inertiaDeg_eq_one v hbase Q
    rw [hplace]
    exact htop
  have hc := Ideal.card_stabilizer_eq (G := E ≃ₐ[F] E) m v.maximalIdeal_ne_bot P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx m P (E ≃ₐ[F] E),
    Ideal.inertiaDegIn_eq_inertiaDeg m P (E ≃ₐ[F] E), hi, mul_one] at hc
  rw [decomposition_eq_center_stabilizer]
  change Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) P) = _
  rw [hc]
  have ho := fiberPrime_order_eq_ramificationIdx v Q
  rw [hplace] at ho
  simpa only [Int.toNat_natCast] using (congrArg Int.toNat ho).symm

end
end Dubon2026.SourceCurve.Place
