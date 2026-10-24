import Dubon2026.SourceCurveDecompositionCardinality
import Dubon2026.SourceRatFuncSpecializationOrder
import Dubon2026.SourceCurveClosedConstantResidue
import Dubon2026.SourceRatFuncGaloisCoordinate

/-! The actual inertia group at a finite specialization of a finite
Galois rational-function extension has cardinality equal to its positive
normalized specialization order. Native Dedekind Galois cardinality,
the proved chart-center identification and existing constant-residue
rationality discharge every group/order and residue assumption needed
for the DUB-17/18 full stabilizer-image comparison. -/
namespace Dubon2026.SourceCurve.Place
open IntermediateField
noncomputable section

theorem inertia_card_eq_rational_specialization_order
    (K : Type*) [Field K] [IsAlgClosed K] {M : Type*} [Field M]
    [Algebra (RatFunc K) M] [Algebra K M] [IsScalarTower K (RatFunc K) M]
    [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]
    (w : Place K M) (a : K)
    (hw : 0 < w.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a)) :
    Nat.card (w.toValuationSubring.inertiaSubgroup (RatFunc K)) =
      (w.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a)).toNat := by
  let t := algebraMap (RatFunc K) M RatFunc.X
  obtain ⟨hfd, hgal⟩ := SourceCurve.finite_galois_coordinateField K (M := M)
  haveI := hfd
  haveI := hgal
  obtain ⟨hfdbase, hsepbase⟩ := SourceCurve.finite_separable_of_adjoin_eq_top
    (RatFunc.X : RatFunc K) RatFunc.adjoin_X
  haveI := hfdbase
  haveI := hsepbase
  have hb := SourceCurve.place_residue_bijective_of_finite_coordinate
    (RatFunc.X : RatFunc K) (w.restrict (RatFunc K))
  have ht := SourceCurve.place_residue_bijective_of_finite_coordinate t w
  let e : w.toValuationSubring.inertiaSubgroup (RatFunc K) ≃
      w.toValuationSubring.decompositionSubgroup (RatFunc K) :=
    Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, fun σ =>
      ⟨⟨σ, mem_inertia_of_decomposition_of_finite_coordinate t w σ.property⟩, rfl⟩⟩
  rw [Nat.card_congr e, decomposition_card_eq_uniformizer_order w hb ht,
    ← rational_specialization_order_eq_uniformizer_order w a hw]

end
end Dubon2026.SourceCurve.Place
