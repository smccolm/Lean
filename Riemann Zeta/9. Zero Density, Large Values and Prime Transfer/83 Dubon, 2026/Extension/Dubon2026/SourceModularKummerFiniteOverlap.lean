import Dubon2026.SourceModularKummerGoodChartBasis
import Dubon2026.SourceJointChartFiniteOverlap
import Dubon2026.SourceModularJointOverlapSpace

/-! DUB-17/18 -> Kummer power lifting -> common residue constants. The
actual modular Kummer overlap quotient is finite over the original valuation
ring. The proof constructs its good-denominator basis, derives coordinate
finiteness and inverse integrality, and applies the finite Laurent generators.
No overlap-finiteness assumption remains in this actual-object consumer. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing SourceCurve
open RegularProlongation.JointChartAssembly RegularProlongation.JointChartConstants
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fbar" => modularFunctionFieldCoeff N kk

/-- The actual residue coefficient algebra for the finite-overlap consumer. -/
local instance jointFiniteOverlapResidueAlgebra : Algebra kk Fbar :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

theorem modular_kummer_joint_finite_overlap
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
      ∃ (ht : ∀ i, algebraMap FF E (jCoeff N Qbar) ∈ (S i).integers)
        (hti : ∀ i, (algebraMap FF E (jCoeff N Qbar))⁻¹ ∈ (S i).integers),
        Module.Finite A (modularJointOverlapQuotient A N q S
          (algebraMap FF E (jCoeff N Qbar)) ht hti) := by
  classical
  letI : FiniteDimensional FF E := IsSplittingField.finiteDimensional E (X ^ q - C (f : FF))
  obtain ⟨S, hSinj, hS, ht, d, z, hz, hchart, _, _, _, hgood⟩ :=
    modular_kummer_joint_good_denominator_basis A N hNk hq f hf hw0 hw E
  let x : E := algebraMap FF E (jCoeff N Qbar)
  letI : FiniteDimensional (IntermediateField.adjoin Qbar ({x} : Set E)) E :=
    modular_extension_finite_coordinate N E
  have hres (i : Fin q) : (S i).residue ⟨x, ht i⟩ = jCoeff N kk :=
    ((hS i).2 ⟨x, ht i⟩ ⟨jCoeff N Qbar, jCoeff_mem_gaussRing A N⟩ rfl).trans
      (modularResidueHom_jCoeff A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
  have hr0 (i : Fin q) : (S i).residue ⟨x, ht i⟩ ≠ 0 := by
    rw [hres]
    exact fun h => transcendental_jCoeff N kk (h ▸ isAlgebraic_zero)
  have hti : ∀ i, x⁻¹ ∈ (S i).integers :=
    @inv_mem_integers Qbar inferInstance A E inferInstance inferInstance
      (Fin q) (fun _ => (Fbar : Type)) (fun _ => inferInstance)
      (fun _ => (modularFunctionFieldCoeff N kk).toSubalgebra.algebra) S x ht hr0
  have htr : Transcendental Qbar x :=
    (transcendental_algebraMap_iff (algebraMap FF E).injective).mpr (transcendental_jCoeff N Qbar)
  refine ⟨S, hSinj, hS, ht, hti, ?_⟩
  exact @finite_overlap_of_good_basis Qbar inferInstance inferInstance inferInstance A
    E inferInstance inferInstance (Fin q) (Fin d) inferInstance
    (fun _ => (Fbar : Type)) (fun _ => inferInstance)
    (fun _ => (modularFunctionFieldCoeff N kk).toSubalgebra.algebra)
    S x ht hti htr inferInstance z (fun j => ⟨hz j, hchart j⟩) hgood

end
end Dubon2026.SourceFunctionField.GaussReduction
