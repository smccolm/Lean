import Dubon2026.SourceGammaOneHeckeConstantField
import Dubon2026.SourceLaurentSpanDescent

/-! DUB17/18 -> original all-weight arithmetic realization -> Gamma1
arithmetic Tate/Hecke comparison on the intersection curve -> existence of arithmetic
place extensions. The existing Laurent coefficient retraction descends
a finite complex scalar relation to the original arithmetic span. This
shorter route proves the proper-ideal separation needed for valuation
domination without rebuilding the basis-extension argument. -/
namespace Dubon2026.SourceFunctionField.GammaOne.HeckeConstantField
noncomputable section
open CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (M d : ℕ)
local notation "FQ" => functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) Qbar
local notation "FC" => functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower arithmeticFieldScalarTower

theorem sum_ne_of_not_mem_span
    {ι : Type*} (c : ι → ℂ) (s : Finset ι) (o : ι → FQ) (y : FQ)
    (hy : y ∉ Submodule.span Qbar (Set.range o)) :
    ∑ j ∈ s, algebraMap ℂ FC (c j) * algebraMap FQ FC (o j) ≠ algebraMap FQ FC y := by
  classical
  intro heq
  have hh := congrArg (laurentLinearMap M d ℂ) heq
  simp only [map_sum] at hh
  have hterm (j : ι) :
      laurentLinearMap M d ℂ (algebraMap ℂ FC (c j) * algebraMap FQ FC (o j)) =
        c j • coeffMap OriginalConstantField.sigma.toRingHom (o j).val := by
    rw [← Algebra.smul_def, map_smul]
    rfl
  simp_rw [hterm] at hh
  change (∑ j ∈ s, c j • coeffMap OriginalConstantField.sigma.toRingHom (o j).val) =
    coeffMap OriginalConstantField.sigma.toRingHom y.val at hh
  have hm : coeffMap OriginalConstantField.sigma.toRingHom y.val ∈
      Submodule.span ℂ (coeffMap OriginalConstantField.sigma.toRingHom ''
        Set.range (fun j => (o j).val)) := by
    rw [← hh]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(o j).val, ⟨j, rfl⟩, rfl⟩)
  have hd := mem_span_of_coeffMap_mem_span OriginalConstantField.sigma.toRingHom
    (Set.range (fun j => (o j).val)) y.val hm
  change laurentLinearMap M d Qbar y ∈
    Submodule.span Qbar (Set.range ((laurentLinearMap M d Qbar) ∘ o)) at hd
  rw [Set.range_comp, Submodule.span_image] at hd
  obtain ⟨z, hz, hzy⟩ := hd
  exact hy ((Subtype.ext hzy) ▸ hz)

end
end Dubon2026.SourceFunctionField.GammaOne.HeckeConstantField
