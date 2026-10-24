import Dubon2026.SourceJointChartLocalizedIntegrality
import Dubon2026.SourceJointChartGlobalConstants

/-! DUB-17/18 -> Kummer genus inequality -> common residue-chart constants.
The two localized original charts intersect precisely in coefficient-ring
constants. The proved global-constant criterion handles all valuations;
one actual reduction ring then forces the scalar to lie in the coefficient
valuation ring. This is the equalizer input to idempotent gluing. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open IsLocalRing

theorem constant_of_mem_localized_charts
    {L F : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    [Field F] [Algebra L F] {ι : Type*} [Nonempty ι]
    {Fb : ι → Type*} [∀ i, Field (Fb i)] [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i)) (f : F)
    (hf : ∀ i, f ∈ (R i).integers) (hfi : ∀ i, f⁻¹ ∈ (R i).integers)
    (htr : Transcendental L f) (x : F)
    (hx : x ∈ Pg R f hf) (hxi : x ∈ Pg R f⁻¹ hfi) :
    ∃ c : A, x = algebraMap A F c := by
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨s, hs, hxs⟩ := hxi
  obtain ⟨c, hc⟩ := constant_of_unit_polynomial_chart_bounds A htr t s ht hs x
    ((mem_originalChart_iff f _).mp hxt.2)
    ((mem_originalChart_iff f⁻¹ _).mp hxs.2)
  let i : ι := Classical.choice ‹Nonempty ι›
  have hmem := mem_integers_of_mem_Pg R hf ⟨t, ht, hxt⟩ i
  rw [hc] at hmem
  exact ⟨⟨c, ((R i).algebraMap_mem_iff c).mp hmem⟩, hc⟩

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
