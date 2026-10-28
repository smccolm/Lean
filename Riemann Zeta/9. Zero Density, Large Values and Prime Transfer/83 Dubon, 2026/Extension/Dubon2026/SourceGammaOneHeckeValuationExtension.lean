import Dubon2026.SourceGammaOneHeckeSpanSeparation
import Dubon2026.SourceConstantFieldValuationDomination
import Mathlib.RingTheory.Valuation.LocalSubring

/-! DUB17/18 -> original all-weight arithmetic realization -> actual
Gamma1 arithmetic Tate/Hecke comparison on the intersection curve -> extended places.
The proved Laurent span descent keeps the actual uniformizer ideal proper.
Native valuation-ring domination then constructs a complex valuation ring
with exactly the given arithmetic inverse image; no extension valuation
or proper-ideal hypothesis remains. Reuse the original local argument,
adapted from S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField.GammaOne.HeckeConstantField
noncomputable section
open CongruenceSubgroup
open SourceCurve SourceCurve.ConstantField
local notation "Qbar" => AlgebraicClosure ℚ
variable (M d : ℕ)
local notation "FQ" => functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) Qbar
local notation "FC" => functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower arithmeticFieldScalarTower

theorem exists_extending_valuation (P : Place Qbar FQ) :
    ∃ V : ValuationSubring FC, V ≠ ⊤ ∧
      (∀ c : ℂ, algebraMap ℂ FC c ∈ V) ∧
      V.comap (fieldMap M d) = P.toValuationSubring := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  have hπinv : (π : FQ)⁻¹ ∉ P.toValuationSubring := by
    intro h
    have := P.ord_nonneg_of_mem h
    rw [P.ord_inv, P.ord_coe_irreducible hπ] at this
    omega
  let B := Module.Basis.ofVectorSpace Qbar ℂ
  have hπA : algebraMap FQ FC (π : FQ) ∈ rangePsi FC B P := algebraMap_coe_mem_rangePsi FC B P π
  have hI : Ideal.span {(⟨algebraMap FQ FC (π : FQ), hπA⟩ : rangePsi FC B P)} ≠ ⊤ := by
    intro h
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_singleton'] at h
    obtain ⟨a, ha⟩ := h
    obtain ⟨w, hw⟩ := a.2
    have ha' : Psi FC B P w * algebraMap FQ FC (π : FQ) = 1 := by
      have := congrArg Subtype.val ha
      simpa [hw] using this
    have hy : (π : FQ)⁻¹ ∉ Submodule.span Qbar (Set.range fun j => ((w j : P.toValuationSubring) : FQ)) := by
      let OK : Submodule Qbar FQ :=
        { carrier := P.toValuationSubring
          add_mem' := fun ha hb => add_mem ha hb
          zero_mem' := zero_mem _
          smul_mem' := fun c x hx => by
            rw [Algebra.smul_def]
            exact mul_mem (P.algebraMap_mem' c) hx }
      have hle : Submodule.span Qbar (Set.range fun j => ((w j : P.toValuationSubring) : FQ)) ≤ OK :=
        Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (w j).2)
      exact fun h => hπinv (hle h)
    have hPsi : Psi FC B P w =
        ∑ j ∈ w.support, algebraMap ℂ FC (B j) *
          algebraMap FQ FC ((w j : P.toValuationSubring) : FQ) := by
      rw [Psi_apply]
      rfl
    refine sum_ne_of_not_mem_span M d B w.support
      (fun j => ((w j : P.toValuationSubring) : FQ)) _ hy ?_
    rw [← hPsi, map_inv₀]
    exact eq_inv_of_mul_eq_one_left ha'
  exact exists_extending_valuation_of_proper_ideal FC B P hπ hI

end
end Dubon2026.SourceFunctionField.GammaOne.HeckeConstantField
