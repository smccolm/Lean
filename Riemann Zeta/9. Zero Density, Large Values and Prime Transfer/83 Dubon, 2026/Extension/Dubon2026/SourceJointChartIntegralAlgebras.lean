import Dubon2026.SourceJointReductionPoleCharts
import Dubon2026.SourceJointReductionPolynomialEvaluation
import Dubon2026.SourceValuationIntegralCriterion

/-! DUB-17/18 -> Kummer power lifting -> genus inequality -> constants in
the common residue chart. The original chart is its actual integral closure
over the coordinate polynomial ring. Native subalgebra closure operations
replace separate closure lemmas for a predicate quantified over valuations.
The proved valuation criterion identifies these two descriptions exactly. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing

/-- The original coordinate chart, realized as its integral closure. -/
def originalChart (L : Type*) [Field L] {F : Type*} [Field F] [Algebra L F] (g : F) :
    Subalgebra L F :=
  (integralClosure (Algebra.adjoin L ({g} : Set F)) F).restrictScalars L

theorem mem_originalChart_iff {L F : Type*} [Field L] [Field F] [Algebra L F] (g u : F) :
    u ∈ originalChart L g ↔
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → g ∈ V → u ∈ V := by
  constructor
  · intro h
    exact Joint.mem_valuation_of_integral_chart h
  · intro h
    apply ConstantField.isIntegral_of_forall_mem_valuationSubring
    intro V hA
    apply h V (fun a => hA (algebraMap L (Algebra.adjoin L ({g} : Set F)) a))
    exact hA ⟨g, Algebra.self_mem_adjoin_singleton L g⟩

theorem self_mem_originalChart {L F : Type*} [Field L] [Field F] [Algebra L F] (g : F) :
    g ∈ originalChart L g :=
  isIntegral_algebraMap (x := (⟨g, Algebra.self_mem_adjoin_singleton L g⟩ : Algebra.adjoin L {g}))

theorem aeval_mem_originalChart {L F : Type*} [Field L] [Field F] [Algebra L F]
    (g : F) (p : L[X]) : aeval g p ∈ originalChart L g := by
  rw [aeval_eq_sum_range]
  exact (originalChart L g).toSubmodule.sum_mem fun i _ =>
    (originalChart L g).toSubmodule.smul_mem _ (pow_mem (self_mem_originalChart g) i)

variable {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
  {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)] [∀ i, Algebra (ResidueField A) (Fb i)]

/-- The original chart elements integral in every chosen reduction ring. -/
def Sg (R : ∀ i, RegularProlongation A F (Fb i)) (g : F) : Subalgebra A F where
  carrier := {u | (∀ i, u ∈ (R i).integers) ∧ u ∈ originalChart L g}
  mul_mem' := fun ha hb => ⟨fun i => mul_mem (ha.1 i) (hb.1 i), mul_mem ha.2 hb.2⟩
  one_mem' := ⟨fun _ => one_mem _, one_mem _⟩
  add_mem' := fun ha hb => ⟨fun i => add_mem (ha.1 i) (hb.1 i), add_mem ha.2 hb.2⟩
  zero_mem' := ⟨fun _ => zero_mem _, zero_mem _⟩
  algebraMap_mem' := fun a => ⟨fun i => ((R i).algebraMap_mem_iff _).mpr a.2,
    (originalChart L g).algebraMap_mem a⟩

theorem aeval_mem_Sg (R : ∀ i, RegularProlongation A F (Fb i))
    {g : F} (hg : ∀ i, g ∈ (R i).integers) {p : L[X]} (hp : ∀ j, p.coeff j ∈ A) :
    aeval g p ∈ Sg R g := by
  refine ⟨fun i => ?_, aeval_mem_originalChart g p⟩
  rw [aeval_eq_sum_range]
  apply (R i).integers.toSubring.sum_mem
  intro j _
  rw [Algebra.smul_def]
  exact mul_mem (((R i).algebraMap_mem_iff _).mpr (hp j)) (pow_mem (hg i) j)

theorem self_mem_Sg (R : ∀ i, RegularProlongation A F (Fb i))
    {g : F} (hg : ∀ i, g ∈ (R i).integers) : g ∈ Sg R g :=
  ⟨hg, self_mem_originalChart g⟩


end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
