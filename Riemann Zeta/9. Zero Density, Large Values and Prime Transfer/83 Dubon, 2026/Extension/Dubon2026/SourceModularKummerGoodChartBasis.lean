import Dubon2026.SourceModularKummerIntegralChartBasis
import Dubon2026.SourceJointChartGoodDenominators

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap.
The actual Kummer chart basis represents every original joint chart function
using a common denominator reducing to a nonzero constant and polynomial
numerators with coefficients in the original valuation ring. The denominator
condition is derived by direct residue-basis cancellation. Finite overlap
generation and the genus inequality remain to be proved. -/
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
local instance jointGoodBasisResidueAlgebra : Algebra kk Fbar :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

theorem modular_kummer_joint_good_denominator_basis
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
        ∀ u : E, (∀ i, u ∈ (S i).integers) ∧
          u ∈ originalChart (L := Qbar) (algebraMap FF E (jCoeff N Qbar)) →
          ∃ (t : Qbar[X]) (p : Fin d → Qbar[X]), IsGood A t ∧
            (∀ σ k, (p σ).coeff k ∈ A) ∧
            u * aeval (algebraMap FF E (jCoeff N Qbar)) t =
              ∑ σ, aeval (algebraMap FF E (jCoeff N Qbar)) (p σ) * z σ := by
  classical
  letI : Nonempty (Fin q) := ⟨⟨0, hqp.out.pos⟩⟩
  obtain ⟨S, hSinj, hS, ht, d, z, hz, hchart, huniq, hgen, hd, hcoords⟩ :=
    modular_kummer_joint_integral_coordinate_basis A N hNk hq f hf hw0 hw E
  let x : E := algebraMap FF E (jCoeff N Qbar)
  have hres (i : Fin q) : (S i).residue ⟨x, ht i⟩ = jCoeff N kk :=
    ((hS i).2 ⟨x, ht i⟩ ⟨jCoeff N Qbar, jCoeff_mem_gaussRing A N⟩ rfl).trans
      (modularResidueHom_jCoeff A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
  have htr (i : Fin q) : Transcendental kk ((S i).residue ⟨x, ht i⟩) := by
    rw [hres]
    exact transcendental_jCoeff N kk
  refine ⟨S, hSinj, hS, ht, d, z, hz, hchart, huniq, hgen, hd, ?_⟩
  intro u hu
  obtain ⟨a, ha, hua⟩ := hcoords u hu.1
  obtain ⟨t, p, hgood, hp, he⟩ :=
    @exists_good_coordinate_denominator Qbar E inferInstance inferInstance A
      inferInstance inferInstance (Fin q) (Fin d) inferInstance inferInstance
      (fun _ => (Fbar : Type)) (fun _ => inferInstance)
      (fun _ => (modularFunctionFieldCoeff N kk).toSubalgebra.algebra)
      S x ht htr z hz hchart huniq hgen u hu.2 a ha hua
  refine ⟨t, p, hgood, hp, ?_⟩
  rw [hua, Finset.sum_mul]
  exact Finset.sum_congr rfl fun σ _ => by rw [mul_right_comm, he σ]

end
end Dubon2026.SourceFunctionField.GaussReduction
