import Dubon2026.SourceModularKummerJointChartDimensionCoreR2
import Dubon2026.SourceModularKummerJointChartSpacesR2
import Dubon2026.SourceJointChartDimensionAssembly
import Dubon2026.SourceJointChartWeightedSpans
import Dubon2026.SourceModularCoordinateChartGeneration
import Dubon2026.SourceModularKummerRegularReductionsR2
import Dubon2026.SourceCurveFiniteCoordinateExtension
import Dubon2026.SourceModularCoefficientGlobalSpaces

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
sum-of-genera inequality. The actual modular Kummer reductions satisfy the
eventual two-chart dimension inequality. Their exact degree, coordinate
separability and finite pole spaces discharge the generic chart assumptions.
The common residue-chart constants and the genus inequality remain to prove. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing SourceCurve
open SourceCurve.RegularProlongation.JointChartAssembly
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fbar" => modularFunctionFieldCoeff N kk

/-- The actual coefficient algebra on the modular residue field. -/
local instance jointDimensionResidueModularAlgebra : Algebra kk Fbar :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

/-- Closed residue constants for the arithmetic coefficient valuation. -/
local instance jointDimensionResidueClosed : IsAlgClosed kk := valuation_residue_isAlgClosed A

theorem joint_chart_dimension_of_modular_reductions
    (hNk : (N : kk) ≠ 0) (q : ℕ) [NeZero q]
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [FiniteDimensional FF E] (hdegree : Module.finrank FF E = q)
    (S : Fin q → RegularProlongation A E Fbar)
    (hSinj : Function.Injective (fun i => (S i).integers))
    (hS : ∀ i, (S i).integers.comap (algebraMap FF E) = gaussRing A N ∧
      ∀ (x : (S i).integers) (y : gaussRing A N), algebraMap FF E y = x →
        (S i).residue x =
          modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk y) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FiniteDimensional kk ↥(modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar)) ⊓
        modularJointWeightedChart A N q S (algebraMap FF E (jCoeff N Qbar)) M) ∧
      Module.finrank kk ↥(modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar)) ⊓
        modularJointWeightedChart A N q S (algebraMap FF E (jCoeff N Qbar)) M) + q ≤
      q * Module.finrank kk ↥(LSpace (M • modularJPole N kk)) +
        Module.finrank kk ↥(modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar)) ⊓
          modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar))⁻¹) := by
  classical
  let t : E := algebraMap FF E (jCoeff N Qbar)
  have ht (i : Fin q) : t ∈ (S i).integers := by
    change jCoeff N Qbar ∈ (S i).integers.comap (algebraMap FF E)
    rw [(hS i).1]
    exact jCoeff_mem_gaussRing A N
  have hres (i : Fin q) : (S i).residue ⟨t, ht i⟩ = jCoeff N kk :=
    ((hS i).2 ⟨t, ht i⟩ ⟨jCoeff N Qbar, jCoeff_mem_gaussRing A N⟩ rfl).trans
      (modularResidueHom_jCoeff A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
  obtain ⟨hbase, hpos⟩ := reduction_coordinate_degree A N
    (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk
  have htotal : Module.finrank (IntermediateField.adjoin Qbar ({t} : Set E)) E =
      Module.finrank (IntermediateField.adjoin kk ({jCoeff N kk} : Set Fbar)) Fbar * q := by
    rw [show t = algebraMap FF E (jCoeff N Qbar) from rfl,
      finrank_adjoin_algebraMap_mul, hbase, hdegree]
    rfl
  have ht0 : t ≠ 0 := by
    simpa only [map_zero] using (algebraMap FF E).injective.ne
      (ne_zero_of_transcendental (transcendental_jCoeff N Qbar))
  exact joint_chart_dimension_of_coordinate_degree A N q E S hSinj t ht hres htotal ht0 hpos


theorem modular_kummer_joint_chart_dimension
    (hNk : (N : kk) ≠ 0) {q : ℕ} [hqp : Fact q.Prime] (hq : (q : kk) ≠ 0)
    (f : gaussRing A N) (hf : ∀ g : FF, g ^ q ≠ (f : FF))
    {w : Fbar} (hw0 : w ≠ 0)
    (hw : w ^ q = modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f)
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [IsSplittingField FF E (X ^ q - C (f : FF))] :
    ∃ S : Fin q → RegularProlongation A E Fbar,
      Function.Injective (fun i => (S i).integers) ∧
      (∀ i, (S i).integers.comap (algebraMap FF E) = gaussRing A N ∧
        ∀ (x : (S i).integers) (y : gaussRing A N), algebraMap FF E y = x →
          (S i).residue x =
            modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk y) ∧
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FiniteDimensional kk ↥(modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar)) ⊓
        modularJointWeightedChart A N q S (algebraMap FF E (jCoeff N Qbar)) M) ∧
      Module.finrank kk ↥(modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar)) ⊓
        modularJointWeightedChart A N q S (algebraMap FF E (jCoeff N Qbar)) M) + q ≤
      q * Module.finrank kk ↥(LSpace (M • modularJPole N kk)) +
        Module.finrank kk ↥(modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar)) ⊓
          modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar))⁻¹) := by
  classical
  letI : NeZero q := ⟨hqp.out.ne_zero⟩
  letI : NeZero (q : Qbar) := ⟨Nat.cast_ne_zero.mpr hqp.out.ne_zero⟩
  letI : FiniteDimensional FF E := IsSplittingField.finiteDimensional E (X ^ q - C (f : FF))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qbar q
  have hroots : (primitiveRoots q FF).Nonempty :=
    ⟨algebraMap Qbar FF ζ, (mem_primitiveRoots hqp.out.pos).mpr
      (hζ.map_of_injective (algebraMap Qbar FF).injective)⟩
  have hdegree : Module.finrank FF E = q := finrank_of_isSplittingField_X_pow_sub_C hroots
    (X_pow_sub_C_irreducible_of_prime hqp.out hf) E
  obtain ⟨S, hSinj, hS⟩ := modular_kummer_regular_reductions A N hNk hq f hf hw0 hw E
  exact ⟨S, hSinj, hS,
    joint_chart_dimension_of_modular_reductions A N hNk q E hdegree S hSinj hS⟩


end
end Dubon2026.SourceFunctionField.GaussReduction
