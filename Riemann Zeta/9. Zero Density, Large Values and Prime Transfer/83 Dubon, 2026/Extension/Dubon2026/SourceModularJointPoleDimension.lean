import Dubon2026.SourceModularKummerJointConstants
import Dubon2026.SourceModularKummerJointChartDimensionR2
import Dubon2026.SourceModularKummerJointDimension
import Dubon2026.SourceJointReductionPoleCharts
import Dubon2026.SourceCurveFiniteCoordinateGenusMaximum

/-! DUB-17/18 -> Kummer power lifting -> genus inequality. Common
residue-chart constants bound the unweighted intersection by one. The
proved joint residue dimension and pole-space chart inclusion then compare
the actual original pole-space dimension with the sum of residue dimensions. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fbar" => modularFunctionFieldCoeff N kk

/-- The actual coefficient algebra for the pole-dimension comparison. -/
local instance jointPoleDimensionResidueAlgebra : Algebra kk Fbar :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

/-- Closed residue constants for the actual coefficient valuation. -/
local instance jointPoleDimensionResidueClosed : IsAlgClosed kk := valuation_residue_isAlgClosed A

theorem joint_pole_dimension_bound_of_common_constants
    (hNk : (N : kk) ≠ 0) (q : ℕ) [NeZero q]
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [FiniteDimensional FF E] (hdegree : Module.finrank FF E = q)
    (S : Fin q → RegularProlongation A E Fbar)
    (hSinj : Function.Injective (fun i => (S i).integers))
    (hS : ∀ i, (S i).integers.comap (algebraMap FF E) = gaussRing A N ∧
      ∀ (x : (S i).integers) (y : gaussRing A N), algebraMap FF E y = x →
        (S i).residue x = modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk y)
    (hconst : ∀ h : Fin q → Fbar,
      h ∈ modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar)) →
      h ∈ modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar))⁻¹ →
      ∃ c : kk, ∀ i, h i = algebraMap kk Fbar c)
    (D : Divisor Qbar E)
    (hD : ∀ v : Place Qbar E, D v = max 0 (-v.ord (algebraMap FF E (jCoeff N Qbar)))) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ell (M • D) + q ≤ q * ell (M • modularJPole N kk) + 1 := by
  classical
  let t : E := algebraMap FF E (jCoeff N Qbar)
  letI : FiniteDimensional (IntermediateField.adjoin Qbar ({t} : Set E)) E :=
    modular_extension_finite_coordinate N E
  have htr : Transcendental Qbar t :=
    (transcendental_algebraMap_iff (algebraMap FF E).injective).mpr (transcendental_jCoeff N Qbar)
  letI := hasPrincipalDivisors_closed_of_separating_coordinate t htr
  letI : ∀ v : Place Qbar E, Module.Finite Qbar v.ResidueField := finite_coordinate_place_residue t
  obtain ⟨P⟩ := nonempty_place_of_separating_coordinate t htr
  letI := finite_lSpace_zero_of_place P
  let U := modularJointChart A N q S t ⊓ modularJointChart A N q S t⁻¹
  have hU : U ≤ Submodule.span kk {(1 : Fin q → Fbar)} := by
    intro h hh
    obtain ⟨c, hc⟩ := hconst h hh.1 hh.2
    have he : h = c • (1 : Fin q → Fbar) := by
      funext i
      simp only [Pi.smul_apply, Pi.one_apply, Algebra.smul_def, mul_one, hc i]
    rw [he]
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  have hdimU : Module.finrank kk U ≤ 1 := by
    calc Module.finrank kk U ≤ Module.finrank kk (Submodule.span kk {(1 : Fin q → Fbar)}) :=
        Submodule.finrank_mono hU
      _ ≤ 1 := by simpa using (finrank_span_le_card ({(1 : Fin q → Fbar)} : Set (Fin q → Fbar)))
  obtain ⟨M₀, hM⟩ := joint_chart_dimension_of_modular_reductions A N hNk q E hdegree S hSinj hS
  refine ⟨M₀, fun M hMM => ?_⟩
  obtain ⟨hfinite, hcount⟩ := hM M hMM
  letI := hfinite
  letI := finite_lSpace (K := Qbar) (M • D)
  have hdim := joint_dimension_of_modular_reductions A N hNk q E hdegree S hSinj hS
    (LSpace (M • D)) inferInstance
  have hlift := @RegularProlongation.Joint.span_residue_pole_space_le_chart_intersection
    Qbar inferInstance inferInstance A E inferInstance inferInstance (Fin q)
    (fun _ => (Fbar : Type)) (fun _ => inferInstance)
    (fun _ => (modularFunctionFieldCoeff N kk).toSubalgebra.algebra)
    S t htr inferInstance D hD M
  have hsmall : ell (M • D) ≤ Module.finrank kk
      ↥(modularJointChart A N q S t ⊓ modularJointWeightedChart A N q S t M) := by
    change Module.finrank Qbar (LSpace (M • D)) ≤ _
    rw [← hdim]
    exact Submodule.finrank_mono hlift
  change Module.finrank kk ↥(modularJointChart A N q S t ⊓ modularJointWeightedChart A N q S t M)
    + q ≤ q * ell (M • modularJPole N kk) + Module.finrank kk U at hcount
  omega

end
end Dubon2026.SourceFunctionField.GaussReduction
