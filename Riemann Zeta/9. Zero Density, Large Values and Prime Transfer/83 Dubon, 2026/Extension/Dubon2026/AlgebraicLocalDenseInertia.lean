import Dubon2026.AlgebraicLocalInertia
import Mathlib.Analysis.Normed.Group.Ultra

/-! Dense original field elements detect actual local inertia. This
allows the existing global inertia valuation congruence to pass to its
original completion without introducing a new valuation model. It serves
the finite-field unramifiedness step in Dubon Theorem 2.6's original-
support deformation quotient comparison. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

attribute [local instance] algebraicLocalIntegerAction

variable {K L F : Type} [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [IsGalois K L] [Field F]

/-- The residue-action kernel can be tested by norm congruence on a
dense embedded original field; original integer elements are approximated
within the unit ball, and the Galois norm is already proved invariant. -/
theorem algebraicLocal_inertia_of_dense_integer_congruence
    (e : F →+* L) (hd : DenseRange e) (g : Gal(L/K))
    (hc : ∀ y : F, ‖e y‖ ≤ 1 → ‖g (e y) - e y‖ < 1) :
    g ∈ algebraicLocalInertia K L := by
  apply (algebraicLocalInertia_mem_iff K L g).mpr
  intro z
  obtain ⟨x, rfl⟩ := residue_surjective z
  have hx : ‖x.val‖ ≤ 1 := by exact_mod_cast x.property
  obtain ⟨y, hy⟩ := hd.exists_dist_lt x.val zero_lt_one
  have hy' : ‖e y - x.val‖ < 1 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hy
  have hey : ‖e y‖ ≤ 1 := by
    have ht := IsUltrametricDist.norm_add_le_max (e y - x.val) x.val
    rw [sub_add_cancel] at ht
    exact ht.trans (max_le (le_of_lt hy') hx)
  have hfirst : ‖g x.val - g (e y)‖ < 1 := by
    rw [← map_sub, completeNonarchimedeanGalois_norm_map, norm_sub_rev]
    exact hy'
  have hmiddle := hc y hey
  have hsum := IsUltrametricDist.norm_add_le_max
    (g x.val - g (e y)) (g (e y) - e y)
  have ht : ‖(g x.val - g (e y)) + (g (e y) - e y)‖ < 1 :=
    hsum.trans_lt (max_lt hfirst hmiddle)
  have htotal := IsUltrametricDist.norm_add_le_max
    ((g x.val - g (e y)) + (g (e y) - e y)) (e y - x.val)
  have he : ((g x.val - g (e y)) + (g (e y) - e y)) + (e y - x.val) =
      g x.val - x.val := by ring
  rw [he] at htotal
  have hg : ‖g x.val - x.val‖ < 1 := htotal.trans_lt (max_lt ht hy')
  rw [← ResidueField.residue_smul]
  apply Ideal.Quotient.eq.mpr
  rw [Valuation.mem_maximalIdeal_iff]
  exact_mod_cast hg

end
end Dubon2026
