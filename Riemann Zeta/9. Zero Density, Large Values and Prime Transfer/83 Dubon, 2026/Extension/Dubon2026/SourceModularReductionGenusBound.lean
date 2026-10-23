import Dubon2026.SourceModularReductionPoleSpace
import Dubon2026.SourceModularCoefficientGenusMaximum
import Dubon2026.SourceCurvePositiveDivisorStabilization

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> automorphy and residual association -> original weight-two
Frobenius/inertia -> modular good reduction. The literal Gauss reduction
cannot increase the actual adelic genus. Every finite-space, maximum,
coordinate-degree and pole-preservation input is derived for the actual
coefficient fields. The opposite inequality and the place comparison remain
necessary for good reduction; this theorem does not claim either.
The comparison follows DeuringLE in the selected Apache-2.0 FLT source,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, reusing the existing adelic
index and principal-shift theory instead of a duplicate Riemann--Roch engine. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve IntermediateField

theorem modularJPole_degree_eq_finrank (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [IsAlgClosed K] :
    Divisor.degree (modularJPole N K) =
      (Module.finrank K⟮jCoeff N K⟯ (modularFunctionFieldCoeff N K) : ℤ) := by
  haveI := finiteDimensional_coeff_field N K
  haveI := isSeparable_coeff_field N K
  exact degree_poleDivisor_eq_finrank_separating (jCoeff N K)
    (transcendental_jCoeff N K) (finite_coeff_divisor_support N K (jCoeff N K))

variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L]
variable (A : ValuationSubring L) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N L
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem ell_j_pole_le_residue (hNL : (N : L) ≠ 0) (hNk : (N : kk) ≠ 0) (m : ℕ) :
    ell (m • modularJPole N L) ≤ ell (m • modularJPole N kk) := by
  haveI := finite_coeff_lSpace N L (m • modularJPole N L)
  haveI := finite_coeff_lSpace N kk (m • modularJPole N kk)
  let S : Submodule kk Fb := Submodule.span kk
    {h : Fb | ∃ f : gaussRing A N,
      (f : FF) ∈ LSpace (m • modularJPole N L) ∧ modularResidueHom A N hNL hNk f = h}
  have hS : S ≤ LSpace (m • modularJPole N kk) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    exact modularResidueHom_mem_j_pole_space A N hNL hNk m hf
  have hd : Module.finrank kk S = Module.finrank L (LSpace (m • modularJPole N L)) :=
    finrank_modular_residue_span A N hNL hNk (LSpace (m • modularJPole N L))
  change Module.finrank L (LSpace (m • modularJPole N L)) ≤
    Module.finrank kk (LSpace (m • modularJPole N kk))
  rw [← hd]
  exact Submodule.finrank_mono hS

theorem modular_residue_index_zero_le (hNL : (N : L) ≠ 0) (hNk : (N : kk) ≠ 0) :
    indexOfSpecialty (0 : Divisor kk Fb) ≤ indexOfSpecialty (0 : Divisor L FF) := by
  haveI := hasPrincipalDivisors_coeff_field N kk
  haveI := finite_coeff_place_residue N kk
  haveI := finite_coeff_lSpace N kk 0
  obtain ⟨γ, D₀, hmax⟩ := coeff_degree_dimension_maximum N L
  obtain ⟨γb, Db₀, hmaxb⟩ := coeff_degree_dimension_maximum N kk
  have hγ := coeff_index_zero_eq_maximum N L hmax
  have hγb := coeff_index_zero_eq_maximum N kk hmaxb
  have hdeg : Divisor.degree (modularJPole N L) = Divisor.degree (modularJPole N kk) := by
    rw [modularJPole_degree_eq_finrank, modularJPole_degree_eq_finrank,
      (reduction_coordinate_degree A N hNL hNk).1]
  have hpos : 0 < Divisor.degree (modularJPole N kk) := by
    rw [modularJPole_degree_eq_finrank]
    exact_mod_cast (reduction_coordinate_degree A N hNL hNk).2
  obtain ⟨m, hm⟩ := hmaxb.exists_forall_degree_nsmul_sub_ell_eq hpos
  have he := hm m le_rfl
  have hbound := hmax.isMax (m • modularJPole N L)
  have hell : (ell (m • modularJPole N L) : ℤ) ≤ ell (m • modularJPole N kk) := by
    exact_mod_cast ell_j_pole_le_residue A N hNL hNk m
  have hdegm : Divisor.degree (m • modularJPole N L) =
      Divisor.degree (m • modularJPole N kk) := by
    rw [map_nsmul, map_nsmul, hdeg]
  have hγle : γb ≤ γ := by linarith
  have hi : (indexOfSpecialty (0 : Divisor kk Fb) : ℤ) ≤
      indexOfSpecialty (0 : Divisor L FF) := by
    exact hγb.le.trans (hγle.trans hγ.symm.le)
  exact_mod_cast hi

end
end Dubon2026.SourceFunctionField.GaussReduction
