import Dubon2026.SourceModularJointPoleDimension
import Dubon2026.SourceCurveRepartitionIndex
import Dubon2026.SourceModularReductionGenusBound

/-! DUB-17/18 -> Kummer power lifting -> sum-of-residue-genera inequality.
The original degree-dimension maximum and the proved eventual residue
pole-space equality cancel the common total pole degree in the joint pole
dimension bound. This reuses the actual H1 genus and existing index bridge;
no new general Riemann--Roch construction is needed. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fbar" => modularFunctionFieldCoeff N kk

/-- The actual residue coefficient algebra. -/
local instance jointGenusResidueAlgebra : Algebra kk Fbar :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

/-- Closed residue constants for the coefficient valuation. -/
local instance jointGenusResidueClosed : IsAlgClosed kk := valuation_residue_isAlgClosed A

theorem joint_genus_inequality_of_common_constants
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
      ∃ c : kk, ∀ i, h i = algebraMap kk Fbar c) :
    q * genusFF kk Fbar ≤ genusFF Qbar E := by
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
  letI := hasPrincipalDivisors_coeff_field N kk
  letI := finite_coeff_place_residue N kk
  letI := finite_coeff_lSpace N kk 0
  let D := poleDivisor t (finite_function_support_of_separating_coordinate t htr t)
  have hD : ∀ v : Place Qbar E, D v = max 0 (-v.ord t) := fun _ => max_comm _ _
  have hdeg : Divisor.degree D = (q : ℤ) * Divisor.degree (modularJPole N kk) := by
    rw [show D = poleDivisor t _ from rfl, degree_poleDivisor_eq_finrank t htr,
      modularJPole_degree_eq_finrank, show t = algebraMap FF E (jCoeff N Qbar) from rfl,
      finrank_adjoin_algebraMap_mul, hdegree,
      (reduction_coordinate_degree A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk).1]
    push_cast
    ring
  obtain ⟨γ, D₀, hmax⟩ := finite_coordinate_degree_dimension_maximum t htr
  have hγ : (genusFF Qbar E : ℤ) = γ := by
    rw [genusFF_eq_zero_index]
    have he := (indexOfSpecialty_eq_of_genusReached hmax 0).2
    rw [show ell (0 : Divisor Qbar E) = 1 from finrank_lSpace_zero_of_principalDivisors P,
      Nat.cast_one, map_zero] at he
    omega
  obtain ⟨γb, Db₀, hmaxb⟩ := coeff_degree_dimension_maximum N kk
  have hγb : (genusFF kk Fbar : ℤ) = γb := by
    rw [@genusFF_eq_zero_index kk Fbar inferInstance inferInstance
      (modularFunctionFieldCoeff N kk).toSubalgebra.algebra (hasPrincipalDivisors_coeff_field N kk)]
    exact coeff_index_zero_eq_maximum N kk hmaxb
  have hpos : 0 < Divisor.degree (modularJPole N kk) := by
    rw [modularJPole_degree_eq_finrank]
    exact_mod_cast (reduction_coordinate_degree A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk).2
  obtain ⟨M₁, hM₁⟩ := hmaxb.exists_forall_degree_nsmul_sub_ell_eq hpos
  obtain ⟨M₀, hM₀⟩ := joint_pole_dimension_bound_of_common_constants
    A N hNk q E hdegree S hSinj hS hconst D hD
  let M := max M₀ M₁
  have hcount : (ell (M • D) : ℤ) + q ≤ (q : ℤ) * ell (M • modularJPole N kk) + 1 := by
    exact_mod_cast hM₀ M (le_max_left _ _)
  have hbound := hmax.isMax (M • D)
  have hbase := hM₁ M (le_max_right _ _)
  have hdegM : Divisor.degree (M • D) = (q : ℤ) * Divisor.degree (M • modularJPole N kk) := by
    rw [map_nsmul, map_nsmul, hdeg]
    simp only [nsmul_eq_mul]
    ring
  have hbaseq := congrArg (fun z : ℤ => (q : ℤ) * z) hbase
  have hgen : (q : ℤ) * (genusFF kk Fbar : ℤ) ≤ (genusFF Qbar E : ℤ) := by
    rw [hγ, hγb]
    nlinarith
  exact_mod_cast hgen

end
end Dubon2026.SourceFunctionField.GaussReduction
