import Dubon2026.SourceModularReductionSourceGenus

/-! DUB-17/18 -> modular good reduction -> comparison of the two integral
charts. Once the actual modular genera agree, every section with a sufficiently
large j-pole bound lifts with that same bound. Existing pole preservation,
residue dimension and positive-divisor stabilization supply the argument.
The genus premise is discharged by the tame chart consumer. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L]
variable (A : ValuationSubring L) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N L
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_pole_space_lifts_of_genus_eq
    (hNL : (N : L) ≠ 0) (hNk : (N : kk) ≠ 0)
    (hgen : genusFF kk Fb = genusFF L FF) :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∀ g : Fb,
      g ∈ LSpace (m • modularJPole N kk) →
      ∃ f : gaussRing A N, (f : FF) ∈ LSpace (m • modularJPole N L) ∧
        modularResidueHom A N hNL hNk f = g := by
  haveI := hasPrincipalDivisors_coeff_field N L
  haveI := hasPrincipalDivisors_coeff_field N kk
  haveI := finite_coeff_place_residue N kk
  haveI := finite_coeff_lSpace N kk 0
  obtain ⟨γ, D₀, hmax⟩ := coeff_degree_dimension_maximum N L
  obtain ⟨γb, Db₀, hmaxb⟩ := coeff_degree_dimension_maximum N kk
  have hγ := coeff_index_zero_eq_maximum N L hmax
  have hγb := coeff_index_zero_eq_maximum N kk hmaxb
  have hindex : indexOfSpecialty (0 : Divisor kk Fb) =
      indexOfSpecialty (0 : Divisor L FF) := by
    exact (@genusFF_eq_zero_index kk Fb _ _ _
      (hasPrincipalDivisors_coeff_field N kk)).symm.trans
        (hgen.trans (@genusFF_eq_zero_index L FF _ _ _
          (hasPrincipalDivisors_coeff_field N L)))
  have hγeq : γ = γb := by
    have he := congrArg (fun n : ℕ => (n : ℤ)) hindex
    exact hγ.symm.trans (he.symm.trans hγb)
  have hdeg : Divisor.degree (modularJPole N L) =
      Divisor.degree (modularJPole N kk) := by
    rw [modularJPole_degree_eq_finrank, modularJPole_degree_eq_finrank,
      (reduction_coordinate_degree A N hNL hNk).1]
  have hpos : 0 < Divisor.degree (modularJPole N kk) := by
    rw [modularJPole_degree_eq_finrank]
    exact_mod_cast (reduction_coordinate_degree A N hNL hNk).2
  obtain ⟨m₁, hm₁⟩ := hmaxb.exists_forall_degree_nsmul_sub_ell_eq hpos
  refine ⟨m₁, fun m hm g hg => ?_⟩
  haveI := finite_coeff_lSpace N L (m • modularJPole N L)
  haveI := finite_coeff_lSpace N kk (m • modularJPole N kk)
  let S : Submodule kk Fb := Submodule.span kk
    {h : Fb | ∃ f : gaussRing A N,
      (f : FF) ∈ LSpace (m • modularJPole N L) ∧ modularResidueHom A N hNL hNk f = h}
  have hS : S ≤ LSpace (m • modularJPole N kk) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    exact modularResidueHom_mem_j_pole_space A N hNL hNk m hf
  have hdim : Module.finrank kk S = ell (m • modularJPole N L) :=
    finrank_modular_residue_span A N hNL hNk (LSpace (m • modularJPole N L))
  have hlarge := hm₁ m hm
  have hbound := hmax.isMax (m • modularJPole N L)
  have hdegm : Divisor.degree (m • modularJPole N L) =
      Divisor.degree (m • modularJPole N kk) := by rw [map_nsmul, map_nsmul, hdeg]
  have hle : ell (m • modularJPole N kk) ≤ Module.finrank kk S := by
    rw [hdim]
    omega
  have he : S = LSpace (m • modularJPole N kk) := Submodule.eq_of_le_of_finrank_le hS hle
  have hgS : g ∈ S := he ▸ hg
  exact RegularProlongation.mem_of_mem_span
    (modularRegularProlongation A N hNL hNk) (LSpace (m • modularJPole N L)) hgS

end
end Dubon2026.SourceFunctionField.GaussReduction
