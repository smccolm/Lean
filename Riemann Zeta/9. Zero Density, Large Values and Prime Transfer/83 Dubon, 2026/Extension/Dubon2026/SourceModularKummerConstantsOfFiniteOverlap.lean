import Dubon2026.SourceJointChartConstantsOfFiniteOverlap
import Dubon2026.SourceModularJointOverlapSpace
import Dubon2026.SourceModularKummerRegularReductionsR2
import Dubon2026.SourceCurveFiniteCoordinateExtension

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
genus inequality -> common residue-chart constants. The actual Kummer
reduction family supplies every degree, transcendence, residue-field and
Krull-dimension input. Finite generation of its displayed overlap quotient
remains explicit and unproved here. This conditional consumer preserves
the exact source objects and identifies the single remaining chart input. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fbar" => modularFunctionFieldCoeff N kk

/-- The actual residue coefficient algebra, with no unrelated tower search. -/
local instance jointConstantsResidueAlgebra : Algebra kk Fbar :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

theorem joint_chart_constants_of_modular_reductions_of_finite_overlap
    (hNk : (N : kk) ≠ 0) (q : ℕ) [NeZero q]
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [FiniteDimensional FF E] (hdegree : Module.finrank FF E = q)
    (S : Fin q → RegularProlongation A E Fbar)
    (hSinj : Function.Injective (fun i => (S i).integers))
    (hS : ∀ i, (S i).integers.comap (algebraMap FF E) = gaussRing A N ∧
      ∀ (x : (S i).integers) (y : gaussRing A N), algebraMap FF E y = x →
        (S i).residue x =
          modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk y) :
    ∀ (ht : ∀ i, algebraMap FF E (jCoeff N Qbar) ∈ (S i).integers)
      (hti : ∀ i, (algebraMap FF E (jCoeff N Qbar))⁻¹ ∈ (S i).integers),
      Module.Finite A (modularJointOverlapQuotient A N q S (algebraMap FF E (jCoeff N Qbar)) ht hti) →
      ∀ h : Fin q → Fbar,
        h ∈ modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar)) →
        h ∈ modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar))⁻¹ →
        ∃ c : kk, ∀ i, h i = algebraMap kk Fbar c := by
  classical
  let t : E := algebraMap FF E (jCoeff N Qbar)
  intro ht hti hfinite h hh hhi
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
  letI : FiniteDimensional (IntermediateField.adjoin Qbar ({t} : Set E)) E :=
    Module.finite_of_finrank_pos (by rw [htotal]; exact Nat.mul_pos hpos (Nat.pos_of_ne_zero (NeZero.ne q)))
  have htr (i : Fin q) : Transcendental kk ((S i).residue ⟨t, ht i⟩) := by
    rw [hres]
    exact transcendental_jCoeff N kk
  have hfiniteResidue : FiniteDimensional
      (IntermediateField.adjoin kk ({jCoeff N kk} : Set Fbar)) Fbar := by
    letI : Module.Free (IntermediateField.adjoin kk ({jCoeff N kk} : Set Fbar)) Fbar :=
      Module.Free.of_divisionRing _ _
    exact Module.finite_of_finrank_pos hpos
  letI (i : Fin q) : FiniteDimensional
      (IntermediateField.adjoin kk ({(S i).residue ⟨t, ht i⟩} : Set Fbar)) Fbar := by
    rw [hres]
    exact hfiniteResidue
  have heq : ∑ i : Fin q, Module.finrank
      (IntermediateField.adjoin kk ({(S i).residue ⟨t, ht i⟩} : Set Fbar)) Fbar =
      Module.finrank (IntermediateField.adjoin Qbar ({t} : Set E)) E := by
    calc
      _ = ∑ _i : Fin q, Module.finrank
          (IntermediateField.adjoin kk ({jCoeff N kk} : Set Fbar)) Fbar := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hres]
      _ = _ := by rw [htotal]; simp [Nat.mul_comm]
  letI := hfinite
  letI := algebraicClosure_rat_valuation_krullDimLE_one A
  have htrL : Transcendental Qbar t :=
    (transcendental_algebraMap_iff (algebraMap FF E).injective).mpr (transcendental_jCoeff N Qbar)
  exact @RegularProlongation.JointChartConstants.common_constants_of_finite_overlap
    Qbar E inferInstance inferInstance inferInstance A inferInstance inferInstance inferInstance
    (Fin q) inferInstance (fun _ => (Fbar : Type)) (fun _ => inferInstance)
    (fun _ => (modularFunctionFieldCoeff N kk).toSubalgebra.algebra)
    S hSinj t ht htrL htr inferInstance (fun i => inferInstance) heq hti inferInstance h hh hhi

theorem modular_kummer_joint_constants_of_finite_overlap
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
      ∀ (ht : ∀ i, algebraMap FF E (jCoeff N Qbar) ∈ (S i).integers)
        (hti : ∀ i, (algebraMap FF E (jCoeff N Qbar))⁻¹ ∈ (S i).integers),
        Module.Finite A (modularJointOverlapQuotient A N q S (algebraMap FF E (jCoeff N Qbar)) ht hti) →
        ∀ h : Fin q → Fbar,
          h ∈ modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar)) →
          h ∈ modularJointChart A N q S (algebraMap FF E (jCoeff N Qbar))⁻¹ →
          ∃ c : kk, ∀ i, h i = algebraMap kk Fbar c := by
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
    joint_chart_constants_of_modular_reductions_of_finite_overlap A N hNk q E hdegree S hSinj hS⟩

end
end Dubon2026.SourceFunctionField.GaussReduction
