import Dubon2026.SourceOriginalPowerResidues
import Dubon2026.SourceOriginalExactDerivativeOrder
import Dubon2026.SourceOriginalRegularOrders

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisors have zero Abel-Jacobi class -> local constancy along fibers.
At a simple zero of an original function, the residue of a regular
differential divided by that function is its coefficient relative to
the function's differential. Existing exact derivative orders and the
original logarithmic-residue formula supply the local calculation.
This replaces the longer unit-derivative construction in
S_AlgebraicCurve_sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]

theorem original_localResidue_mul_simplePole
    (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (h x : modularFunctionFieldOver N ℂ) (hh : h ∈ v.toValuationSubring)
    (hx : v.uniformizer * x ∈ v.toValuationSubring) :
    (originalCanonicalLocalResidueData N ℂ v).res (h * x) =
      IsLocalRing.residue v.toValuationSubring ⟨h, hh⟩ *
        (originalCanonicalLocalResidueData N ℂ v).res x := by
  have hm : v.uniformizer * (h * x) ∈ v.toValuationSubring := by
    rw [mul_left_comm]
    exact mul_mem hh hx
  rw [original_canonicalLocalResidue_simplePole N ℂ v _ hm,
    original_canonicalLocalResidue_simplePole N ℂ v _ hx]
  have he : (⟨v.uniformizer * (h * x), hm⟩ : v.toValuationSubring) =
      ⟨h, hh⟩ * ⟨v.uniformizer * x, hx⟩ := Subtype.ext (mul_left_comm _ _ _)
  rw [he, map_mul]

theorem original_simple_zero_residue
    (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (g h : modularFunctionFieldOver N ℂ) (hg : v.ord g = 1)
    (hω : h • D ℂ (modularFunctionFieldOver N ℂ) g ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ hh : h ∈ v.toValuationSubring,
      (originalCanonicalLocalResidueData N ℂ v).res
        (g⁻¹ * v.differentialCoeff (h • D ℂ (modularFunctionFieldOver N ℂ) g)) =
          IsLocalRing.residue v.toValuationSubring ⟨h, hh⟩ := by
  haveI := original_place_dCoordGenerates N ℂ v
  haveI : Nontrivial Ω[modularFunctionFieldOver N ℂ⁄ℂ] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N ℂ)
  have hg0 : g ≠ 0 := by
    intro he
    rw [he, v.ord_zero] at hg
    exact zero_ne_one hg
  have hlog := original_localResidue_logarithmic N ℂ v hg0
  rw [hg, Int.cast_one] at hlog
  have hd0 : v.differentialCoeff (D ℂ (modularFunctionFieldOver N ℂ) g) ≠ 0 := by
    intro he
    rw [he, zero_div, map_zero] at hlog
    exact zero_ne_one hlog
  have hord := original_ordDifferential_D_eq_ord_sub_one N ℂ v
    (by rw [hg]; exact one_ne_zero)
  rw [hg, sub_self] at hord
  have hh : h ∈ v.toValuationSubring := by
    by_cases hh0 : h = 0
    · rw [hh0]
      exact zero_mem _
    have hs := v.ordDifferential_smul hh0 hd0
    rw [hord, add_zero] at hs
    apply v.mem_of_ord_nonneg
    have hr := (mem_original_regularDifferentials_iff_ord_nonneg N ℂ _).mp hω v
    rwa [hs] at hr
  refine ⟨hh, ?_⟩
  have hx : v.uniformizer * (v.differentialCoeff (D ℂ (modularFunctionFieldOver N ℂ) g) / g) ∈
      v.toValuationSubring := by
    apply v.mem_of_ord_nonneg
    rw [div_eq_mul_inv, v.ord_mul v.uniformizer_ne_zero (mul_ne_zero hd0 (inv_ne_zero hg0)),
      v.ord_mul hd0 (inv_ne_zero hg0), v.ord_uniformizer, v.ord_inv, hg]
    change 0 ≤ 1 + (v.ordDifferential (D ℂ (modularFunctionFieldOver N ℂ) g) + -1)
    rw [hord]
    norm_num
  rw [v.differentialCoeff_smul]
  have he : g⁻¹ * (h * v.differentialCoeff (D ℂ (modularFunctionFieldOver N ℂ) g)) =
      h * (v.differentialCoeff (D ℂ (modularFunctionFieldOver N ℂ) g) / g) := by
    rw [div_eq_mul_inv]
    ring
  rw [he, original_localResidue_mul_simplePole N v h _ hh hx, hlog, mul_one]

end
end Dubon2026.SourceFunctionField
