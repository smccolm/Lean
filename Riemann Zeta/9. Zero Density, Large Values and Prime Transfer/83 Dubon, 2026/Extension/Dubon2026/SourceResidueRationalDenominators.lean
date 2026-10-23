import Dubon2026.SourceResiduePowerCoordinates

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> integral
coefficient specialization. Clear finitely many denominators in the literal
rational-j field. The finite power expression then becomes a polynomial
relation that can be primitively scaled and reduced. Only this finite-array
form, needed by the actual modular-field consumer, is introduced. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField
variable {K : Type*} [Field K]

theorem rational_j_clear_finite_denominators {ι : Type*} [Fintype ι]
    (g : ι → K⟮jqModC K⟯) :
    ∃ D : Polynomial K, D ≠ 0 ∧ ∃ c : ι → Polynomial K,
      ∀ i, Polynomial.aeval (jqModC K) (c i) =
        Polynomial.aeval (jqModC K) D * (g i : LaurentSeries K) := by
  classical
  have hg : ∀ i, ∃ rs : Polynomial K × Polynomial K,
      Polynomial.aeval (jqModC K) rs.2 ≠ 0 ∧
      (g i : LaurentSeries K) = Polynomial.aeval (jqModC K) rs.1 /
        Polynomial.aeval (jqModC K) rs.2 := by
    intro i
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K _).mp (g i).2
    by_cases hs : Polynomial.aeval (jqModC K) s = 0
    · refine ⟨(0, 1), by simp, ?_⟩
      rw [hrs, hs, div_zero]
      simp
    · exact ⟨(r, s), hs, hrs⟩
  choose rs hrs0 hrs using hg
  let D : Polynomial K := ∏ i, (rs i).2
  have hD : Polynomial.aeval (jqModC K) D = ∏ i, Polynomial.aeval (jqModC K) (rs i).2 :=
    map_prod _ _ _
  have hDne : Polynomial.aeval (jqModC K) D ≠ 0 := by
    rw [hD]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hrs0 i
  refine ⟨D, fun h => hDne (by rw [h, map_zero]),
    fun i => (rs i).1 * ∏ j ∈ Finset.univ.erase i, (rs j).2, ?_⟩
  intro i
  rw [map_mul, map_prod, hrs i, hD, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have hs0 := hrs0 i
  field_simp

end
end Dubon2026.SourceFunctionField
