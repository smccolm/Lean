import Dubon2026.SourceModularKummerFullChartBasis
import Dubon2026.SourceJointChartIntegralCoordinates
import Dubon2026.SourceModularKummerCurve

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap.
The actual lifted Kummer chart basis represents every jointly integral
function with jointly integral coefficients in the original coordinate
field. The basis, its full rank and coordinate integrality are constructed,
not assumed. Denominator control and finite overlap generators remain. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing SourceCurve
open RegularProlongation.JointChartAssembly RegularProlongation.JointChartConstants
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fbar" => modularFunctionFieldCoeff N kk

/-- The actual residue coefficient algebra, with no unrelated tower search. -/
local instance jointIntegralBasisResidueAlgebra : Algebra kk Fbar :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

theorem modular_kummer_joint_integral_coordinate_basis
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
      ∃ (ht : ∀ i, algebraMap FF E (jCoeff N Qbar) ∈ (S i).integers),
      ∃ (d : ℕ) (z : Fin d → E) (hz : ∀ σ i, z σ ∈ (S i).integers),
        (∀ σ, z σ ∈ originalChart (L := Qbar) (algebraMap FF E (jCoeff N Qbar))) ∧
        (∀ r r' : Fin d → kk[X],
          ∑ σ, aeval (modularJointResidueVector A N q S (algebraMap FF E (jCoeff N Qbar)) ht) (r σ) * modularJointResidueVector A N q S (z σ) (hz σ) =
            ∑ σ, aeval (modularJointResidueVector A N q S (algebraMap FF E (jCoeff N Qbar)) ht) (r' σ) * modularJointResidueVector A N q S (z σ) (hz σ) → r = r') ∧
        (∀ h ∈ modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar)), ∃ r : Fin d → kk[X],
          h = ∑ σ, aeval (modularJointResidueVector A N q S (algebraMap FF E (jCoeff N Qbar)) ht) (r σ) * modularJointResidueVector A N q S (z σ) (hz σ)) ∧
        Module.finrank (IntermediateField.adjoin Qbar ({algebraMap FF E (jCoeff N Qbar)} : Set E)) E = d ∧
        ∀ u : E, (∀ i, u ∈ (S i).integers) →
          ∃ a : Fin d → E,
            (∀ σ, (∀ i, a σ ∈ (S i).integers) ∧
              a σ ∈ IntermediateField.adjoin Qbar ({algebraMap FF E (jCoeff N Qbar)} : Set E)) ∧
            u = ∑ σ, a σ * z σ := by
  classical
  letI : FiniteDimensional FF E := IsSplittingField.finiteDimensional E (X ^ q - C (f : FF))
  obtain ⟨S, hSinj, hS, ht, d, z, hz, hchart, huniq, hgen, hd⟩ :=
    modular_kummer_joint_full_chart_basis A N hNk hq f hf hw0 hw E
  let t : E := algebraMap FF E (jCoeff N Qbar)
  letI : FiniteDimensional (IntermediateField.adjoin Qbar ({t} : Set E)) E :=
    modular_extension_finite_coordinate N E
  have hres (i : Fin q) : (S i).residue ⟨t, ht i⟩ = jCoeff N kk :=
    ((hS i).2 ⟨t, ht i⟩ ⟨jCoeff N Qbar, jCoeff_mem_gaussRing A N⟩ rfl).trans
      (modularResidueHom_jCoeff A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
  have htr (i : Fin q) : Transcendental kk ((S i).residue ⟨t, ht i⟩) := by
    rw [hres]
    exact transcendental_jCoeff N kk
  refine ⟨S, hSinj, hS, ht, d, z, hz, hchart, huniq, hgen, hd, ?_⟩
  intro u hu
  exact @exists_integral_coords_of_full_chart_basis Qbar E inferInstance A
    inferInstance inferInstance (Fin q) (fun _ => (Fbar : Type))
    (fun _ => inferInstance) (fun _ => (modularFunctionFieldCoeff N kk).toSubalgebra.algebra)
    S t ht htr inferInstance d z hz huniq hd u hu

end
end Dubon2026.SourceFunctionField.GaussReduction
