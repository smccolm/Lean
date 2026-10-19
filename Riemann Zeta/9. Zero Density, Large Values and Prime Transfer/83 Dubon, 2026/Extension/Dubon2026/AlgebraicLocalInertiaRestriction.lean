import Dubon2026.AlgebraicLocalInertia
import Dubon2026.AlgebraicLocalResidueGalois

/-! Inertia lifts through a genuine tower of complete normed local fields.
This is the restriction-surjectivity step needed for the actual cyclotomic
tame quotient in the auxiliary deformation rings serving Dubon Theorem 2.6.
The native residue-automorphism lifting theorem supplies the correction to
an arbitrary field-automorphism lift. The same correction strategy occurs
in the reviewed Lift section of anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2, file
S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow.lean.
The global valuation-ring dictionary there is unnecessary for this native
normed-field tower. Apache-2.0; retained license:
../../Dependencies/AnthropicFLTReuse/LICENSE.
-/

namespace Dubon2026
noncomputable section
open IsLocalRing

attribute [local instance] algebraicLocalIntegerAction algebraicLocalIntegerBaseAlgebra

/-- Every actual inertia automorphism of the intermediate local field lifts
to actual inertia in the original algebraic extension, with the literal
normal restriction retained. -/
theorem algebraicLocal_inertia_exists_restriction_lift
    (K E L : Type) [NontriviallyNormedField K] [NontriviallyNormedField E] [NormedField L]
    [NormedAlgebra K E] [NormedAlgebra K L] [NormedAlgebra E L] [IsScalarTower K E L]
    [IsUltrametricDist K] [IsUltrametricDist E] [IsUltrametricDist L]
    [CompleteSpace K] [CompleteSpace E]
    [IsGalois K E] [IsGalois K L] [IsGalois E L]
    (σ : Gal(E/K)) (hσ : σ ∈ algebraicLocalInertia K E) :
    ∃ g : Gal(L/K), g ∈ algebraicLocalInertia K L ∧ AlgEquiv.restrictNormalHom E g = σ := by
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := E) L σ
  let S := algebraicLocalIntegerRing L
  let T := algebraicLocalIntegerRing E
  let Q := maximalIdeal S
  let P := Q.under T
  letI : Algebra (T ⧸ P) (ResidueField S) := Ideal.Quotient.algebraQuotientOfLEComap le_rfl
  have hfix (x : T) : residue S (g • algebraMap T S x) = residue S (algebraMap T S x) := by
    have he : g • algebraMap T S x = algebraMap T S (σ • x) := by
      apply Subtype.ext
      change g (algebraMap E L x.val) = algebraMap E L (σ x.val)
      exact (g.restrictNormal_commutes E x.val).symm.trans
        (congrArg (algebraMap E L) (DFunLike.congr_fun hg x.val))
    rw [he]
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    change σ • x - x ∈ (maximalIdeal S).under T
    rw [algebraicLocalInteger_maximalIdeal_under E L]
    apply Ideal.Quotient.eq.mp
    change residue T (σ • x) = residue T x
    rw [ResidueField.residue_smul]
    exact (algebraicLocalInertia_mem_iff K E σ).mp hσ _
  let s : ResidueField S ≃ₐ[T ⧸ P] ResidueField S :=
    { MulSemiringAction.toRingEquiv Gal(L/K) (ResidueField S) g with
      commutes' := fun x => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change g • residue S (algebraMap T S x) = residue S (algebraMap T S x)
        rw [← ResidueField.residue_smul]
        exact hfix x }
  obtain ⟨h, hh⟩ := algebraicLocal_residueAut_exists_lift E L s
  let hK := h.restrictScalars K
  have hhr : AlgEquiv.restrictNormalHom E hK = 1 := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap E L).injective
    exact (hK.restrictNormal_commutes E x).trans (h.commutes x)
  have hhres (x : ResidueField S) : hK • x = g • x := by
    obtain ⟨x, rfl⟩ := residue_surjective x
    rw [← ResidueField.residue_smul, ← ResidueField.residue_smul]
    exact hh x
  refine ⟨hK⁻¹ * g, ?_, ?_⟩
  · apply (algebraicLocalInertia_mem_iff K L _).mpr
    intro x
    rw [mul_smul, ← hhres, inv_smul_smul]
  · rw [map_mul, map_inv, hhr, inv_one, one_mul, hg]

end
end Dubon2026
