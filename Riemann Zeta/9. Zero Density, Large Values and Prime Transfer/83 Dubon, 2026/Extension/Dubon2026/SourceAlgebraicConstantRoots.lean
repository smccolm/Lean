import Dubon2026.SourceConstantExtensionIntegralAlgebra

/-! DUB-17/18 -> original all-weight arithmetic association -> actual
Gamma1 character realization -> differential/cusp comparison -> rational
Fourier spanning -> integral base change of Fricke fractions. The algebraic
constant-adjoining step expresses an integral element as a complex span of
integral elements over the original constants. Finite extension embeddings
and Lagrange interpolation discharge integrality of the actual coordinates.
Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_IsIntegral_mem_span_of_adjoin_simple_constants. No proof limit is raised.
The later consumer is the actual Fricke fraction field; constant-extension
spanning and rational Fourier realization are not assumed. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section
open Polynomial
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℂ K]
variable (F : IntermediateField ℚ ℂ) (B S : Set K)
variable {B S}

theorem root_minpoly_KFld_eq_algebraMap {c : ℂ} (hc : IsIntegral ↥F c) {r : K}
    (hr : r ∈ (minpoly ↥(KFld F S) (algebraMap ℂ K c)).aroots K) :
    ∃ a : ℂ, IsIntegral ↥F a ∧ algebraMap ℂ K a = r := by
  set ι := algebraMap ℂ K
  set q : ℂ[X] := (minpoly ↥F c).map (algebraMap ↥F ℂ) with hq
  have hqm : q.Monic := (minpoly.monic hc).map _
  have hq0 : q.map ι ≠ 0 := (hqm.map ι).ne_zero
  have hdvd : (minpoly ↥(KFld F S) (ι c)).map (algebraMap ↥(KFld F S) K) ∣ q.map ι := by
    have := Polynomial.map_dvd (algebraMap ↥(KFld F S) K) (minpoly_KFld_dvd F (S := S) c)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
    rwa [hq, Polynomial.map_map, ← IsScalarTower.algebraMap_eq ↥F ℂ K]
  have hroots : (q.map ι).roots = q.roots.map ι :=
    (IsAlgClosed.splits q).roots_map_of_injective (algebraMap ℂ K).injective
  have hr' : r ∈ (q.map ι).roots := Multiset.mem_of_le (Polynomial.roots.le_of_dvd hq0 hdvd) hr
  rw [hroots, Multiset.mem_map] at hr'
  obtain ⟨a, ha, rfl⟩ := hr'
  refine ⟨a, ?_, rfl⟩
  rw [Polynomial.mem_roots hqm.ne_zero, Polynomial.IsRoot.def, hq, Polynomial.eval_map,
    ← Polynomial.aeval_def] at ha
  exact ⟨minpoly ↥F c, minpoly.monic hc, by rwa [← Polynomial.aeval_def]⟩

attribute [local instance] Classical.propDecidable in

theorem card_rootFinset_minpoly_KFld {c : ℂ} (hc : IsIntegral ↥F c) :
    ((minpoly ↥(KFld F S) (algebraMap ℂ K c)).aroots K).toFinset.card =
      (minpoly ↥(KFld F S) (algebraMap ℂ K c)).natDegree := by
  set ι := algebraMap ℂ K
  set L₀ := KFld F S
  haveI : CharZero ↥L₀ := charZero_KFld F L₀
  have hint : IsIntegral ↥L₀ (ι c) := isIntegral_KFld_algebraMap F hc
  set m₁ := minpoly ↥L₀ (ι c)
  have hsep : (m₁.map (algebraMap ↥L₀ K)).Separable :=
    (PerfectField.separable_of_irreducible (minpoly.irreducible hint)).map
  rw [Polynomial.aroots_def, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)]
  set q : ℂ[X] := (minpoly ↥F c).map (algebraMap ↥F ℂ) with hq
  have hqm : q.Monic := (minpoly.monic hc).map _
  have hdvd : m₁.map (algebraMap ↥L₀ K) ∣ q.map ι := by
    have := Polynomial.map_dvd (algebraMap ↥L₀ K) (minpoly_KFld_dvd F (S := S) c)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
    rwa [hq, Polynomial.map_map, ← IsScalarTower.algebraMap_eq ↥F ℂ K]
  have hspl : (m₁.map (algebraMap ↥L₀ K)).Splits :=
    ((IsAlgClosed.splits q).map ι).of_dvd (hqm.map ι).ne_zero hdvd
  rw [← hspl.natDegree_eq_card_roots, Polynomial.natDegree_map]


end
end Dubon2026.SourceFricke.ConstantDescent
