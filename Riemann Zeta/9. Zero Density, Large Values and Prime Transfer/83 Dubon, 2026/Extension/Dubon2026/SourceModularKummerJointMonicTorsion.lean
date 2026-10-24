import Dubon2026.SourceJointChartMonicTorsion
import Dubon2026.SourceModularKummerCurve
import Dubon2026.SourceModularKummerRegularReductionsR2
import Dubon2026.SourceCurveFiniteCoordinateExtension

/-! DUB-17/18 -> Kummer power lifting -> genus inequality -> monic
torsion of residue chart quotients. The actual Kummer reductions lift every
residue vector; the existing finite modular coordinate and native integral
multiples give a monic polynomial multiple coming from the original integral
j chart. This discharges the monic-torsion input of the chart dimension
inequality for the literal modular Kummer cover. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fb" => modularFunctionFieldCoeff N kk

/-- The actual residue coefficient algebra, with no unrelated tower search. -/
local instance jointMonicResidueModularAlgebra : Algebra kk Fb :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

theorem modular_kummer_joint_monic_torsion
    (hNk : (N : kk) ≠ 0) {q : ℕ} [hqp : Fact q.Prime] (hq : (q : kk) ≠ 0)
    (f : gaussRing A N) (hf : ∀ g : FF, g ^ q ≠ (f : FF))
    {w : Fb} (hw0 : w ≠ 0)
    (hw : w ^ q = modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f)
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [IsSplittingField FF E (X ^ q - C (f : FF))] :
    ∃ S : Fin q → RegularProlongation A E Fb,
      Function.Injective (fun i => (S i).integers) ∧
      (∀ i, (S i).integers.comap (algebraMap FF E) = gaussRing A N ∧
        ∀ (x : (S i).integers) (y : gaussRing A N), algebraMap FF E y = x →
          (S i).residue x =
            modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk y) ∧
      ∀ h : Fin q → Fb, ∃ c : Polynomial kk, c.Monic ∧
        (fun i => Polynomial.aeval (jCoeff N kk) c * h i) ∈
          Submodule.span kk
            {h : Fin q → Fb | ∃ u : E, ∃ hu : ∀ i, u ∈ (S i).integers,
              (∀ V : ValuationSubring E, (∀ a : Qbar, algebraMap Qbar E a ∈ V) →
                algebraMap FF E (jCoeff N Qbar) ∈ V → u ∈ V) ∧
              ∀ i, (S i).residue ⟨u, hu i⟩ = h i} := by
  classical
  letI : FiniteDimensional FF E := IsSplittingField.finiteDimensional E (X ^ q - C (f : FF))
  let t : E := algebraMap FF E (jCoeff N Qbar)
  letI : FiniteDimensional (IntermediateField.adjoin Qbar ({t} : Set E)) E :=
    modular_extension_finite_coordinate N E
  obtain ⟨S, hSinj, hS⟩ := modular_kummer_regular_reductions A N hNk hq f hf hw0 hw E
  have ht (i : Fin q) : t ∈ (S i).integers := by
    change jCoeff N Qbar ∈ (S i).integers.comap (algebraMap FF E)
    rw [(hS i).1]
    exact jCoeff_mem_gaussRing A N
  have hres (i : Fin q) : (S i).residue ⟨t, ht i⟩ = jCoeff N kk :=
    ((hS i).2 ⟨t, ht i⟩ ⟨jCoeff N Qbar, jCoeff_mem_gaussRing A N⟩ rfl).trans
      (modularResidueHom_jCoeff A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
  refine ⟨S, hSinj, hS, fun h => ?_⟩
  obtain ⟨c, hc, hmem⟩ := @RegularProlongation.Joint.exists_monic_residue_chart_multiple
    Qbar E inferInstance A inferInstance inferInstance (Fin q) inferInstance
    (fun _ => (Fb : Type)) (fun _ => inferInstance)
    (fun _ => (modularFunctionFieldCoeff N kk).toSubalgebra.algebra)
    S hSinj t ht Module.finrank_pos h
  refine ⟨c, hc, ?_⟩
  have he : (fun i => Polynomial.aeval ((S i).residue ⟨t, ht i⟩) c * h i) =
      (fun i => Polynomial.aeval (jCoeff N kk) c * h i) := by
    funext i
    rw [hres i]
  rw [he] at hmem
  exact hmem

end
end Dubon2026.SourceFunctionField.GaussReduction
