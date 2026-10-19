import Dubon2026.AlgebraicLocalInertia
import Dubon2026.LocalFieldIntegerAlgebraFinite
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Surjectivity of the actual residue inclusion makes every original
normed-field automorphism inertia. This transports the residue degree one
consequence of the cyclotomic norm identity to the original inertia used
by the auxiliary deformation characters for Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section
open IsLocalRing
open scoped ValuativeRel

attribute [local instance] algebraicLocalIntegerAction

/-- A surjective original residue inclusion kills the entire original
norm-residue action, with compatibility of the two valuations explicit. -/
theorem algebraicLocal_inertia_eq_top_of_residue_surjective
    (K L : Type) [NontriviallyNormedField K] [NormedField L]
    [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L]
    [CompleteSpace K] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L]
    [(NormedField.valuation (K := K)).Compatible]
    [(NormedField.valuation (K := L)).Compatible]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (hres : Function.Surjective (algebraMap 𝓀[K] 𝓀[L])) :
    algebraicLocalInertia K L = ⊤ := by
  apply top_unique
  intro g _
  apply (algebraicLocalInertia_mem_iff K L g).mpr
  intro x
  obtain ⟨x, rfl⟩ := residue_surjective x
  have hx : x.val ∈ (ValuativeRel.valuation L).integer := by
    change ValuativeRel.valuation L x.val ≤ 1
    rw [← (ValuativeRel.valuation L).vle_one_iff,
      (NormedField.valuation (K := L)).vle_one_iff]
    exact x.property
  let y : 𝒪[L] := ⟨x.val, hx⟩
  obtain ⟨a, ha⟩ := hres (residue 𝒪[L] y)
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [ResidueField.algebraMap_residue] at ha
  have hsmall : ‖algebraMap K L a.val - x.val‖ < 1 := by
    have hmem := Ideal.Quotient.eq.mp ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hmem
    rw [← (ValuativeRel.valuation L).vlt_one_iff,
      (NormedField.valuation (K := L)).vlt_one_iff] at hmem
    exact_mod_cast hmem
  have hgsmall : ‖g x.val - x.val‖ < 1 := by
    have hg := completeNonarchimedeanGalois_norm_map g (algebraMap K L a.val - x.val)
    rw [map_sub, AlgEquiv.commutes] at hg
    have hsum := IsUltrametricDist.norm_add_le_max
      (algebraMap K L a.val - x.val) (-(algebraMap K L a.val - g x.val))
    have he : (algebraMap K L a.val - x.val) +
        (-(algebraMap K L a.val - g x.val)) = g x.val - x.val := by ring
    rw [he, norm_neg, hg] at hsum
    exact hsum.trans_lt (max_lt hsmall hsmall)
  rw [← ResidueField.residue_smul]
  apply Ideal.Quotient.eq.mpr
  rw [Valuation.mem_maximalIdeal_iff]
  exact_mod_cast hgsmall

end
end Dubon2026
