import Dubon2026.SourceValuationIntegralCriterion
import Dubon2026.SourceCurveFiniteCoordinateValuations
import Mathlib.RingTheory.Trace.Basic

/-! DUB-17/18 -> arithmetic Picard injectivity -> principal-divisor descent
-> trace regularity. Normalize every proper extending valuation using the
proved finite transcendental coordinate. The native valuation-intersection
criterion and trace integrality then descend regularity to the coordinate field.
Adapted from S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, trace_mem.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]

theorem trace_mem_of_forall_place (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K (Set.singleton x)) F]
    (v : Place K F) (w : F)
    (hw : ∀ W : Place K F,
      (∀ g : F, g ∈ IntermediateField.adjoin K (Set.singleton x) →
        g ∈ v.toValuationSubring → g ∈ W.toValuationSubring) → w ∈ W.toValuationSubring) :
    ((Algebra.trace (IntermediateField.adjoin K (Set.singleton x)) F w :
      IntermediateField.adjoin K (Set.singleton x)) : F) ∈ v.toValuationSubring := by
  let kx : IntermediateField K F := IntermediateField.adjoin K {x}
  let R : ValuationSubring kx := v.toValuationSubring.comap (algebraMap kx F)
  have hRmem : ∀ g : kx, g ∈ R ↔ (g : F) ∈ v.toValuationSubring := fun _ =>
    ValuationSubring.mem_comap
  have hint : IsIntegral R w := by
    apply isIntegral_of_forall_mem_valuationSubring
    intro B hB
    have hB' : ∀ g : F, g ∈ kx → g ∈ v.toValuationSubring → g ∈ B := by
      intro g hg1 hg2
      exact hB ⟨⟨g, hg1⟩, (hRmem _).mpr hg2⟩
    by_contra hwB
    have hBtop : B ≠ ⊤ := fun h => hwB (h ▸ ValuationSubring.mem_top w)
    obtain ⟨W, hW⟩ := exists_place_of_finite_coordinate x hx B
      (fun a => hB' _ (kx.algebraMap_mem a) (v.algebraMap_mem' a)) hBtop
    exact hwB (hW ▸ hw W (fun g hg1 hg2 => by rw [hW]; exact hB' g hg1 hg2))
  have htr : IsIntegral R (Algebra.trace kx F w) := Algebra.isIntegral_trace hint
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := kx)).mp htr
  exact (hRmem _).mp (hy ▸ y.property)

end
end Dubon2026.SourceCurve.ConstantField
