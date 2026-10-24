import Dubon2026.SourceCurvePlaceCenters
import Mathlib.FieldTheory.KummerExtension

/-! DUB-17/18 -> original Frobenius/inertia -> Picard torsion injectivity ->
power lifting -> unramified Kummer covers. The exact norm of a shifted
Kummer generator bounds its local order using the already proved norm-fiber
formula. Adapted from the Pure and OrdNorm sections of
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord.
Native prime-binomial irreducibility and power-basis norm are reused. -/
namespace Dubon2026.SourceCurve.KummerCover
noncomputable section
open Polynomial IntermediateField
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable {q : ℕ} [hq : Fact q.Prime] {f : F} {α : E}

theorem norm_root_sub_algebraMap (hf : ∀ g : F, g ^ q ≠ f)
    (hα : α ^ q = algebraMap F E f) (htop : F⟮α⟯ = ⊤) (c : F) :
    Algebra.norm F (α - algebraMap F E c) = (-1) ^ q * (c ^ q - f) := by
  have hint : IsIntegral F α := IsIntegral.of_pow hq.out.pos (hα ▸ isIntegral_algebraMap)
  have hmin : minpoly F α = X ^ q - C f :=
    (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hq.out hf)
      (by simp only [map_sub, map_pow, aeval_X, aeval_C, hα, sub_self])
      (monic_X_pow_sub_C f hq.out.ne_zero)).symm
  have hxint : IsIntegral F (α - algebraMap F E c) := hint.sub isIntegral_algebraMap
  have hminx : minpoly F (α - algebraMap F E c) = (X ^ q - C f).comp (X + C c) := by
    rw [minpoly.sub_algebraMap, hmin]
  have hxtop : F⟮α - algebraMap F E c⟯ = ⊤ := by
    rw [eq_top_iff, ← htop, adjoin_simple_le_iff]
    have h1 := mem_adjoin_simple_self F (α - algebraMap F E c)
    have h2 := IntermediateField.algebraMap_mem F⟮α - algebraMap F E c⟯ c
    simpa using add_mem h1 h2
  let pb : PowerBasis F E := (adjoin.powerBasis hxint).map ((equivOfEq hxtop).trans topEquiv)
  have hgen : pb.gen = α - algebraMap F E c := by
    simp only [pb, PowerBasis.map_gen, adjoin.powerBasis_gen, AlgEquiv.trans_apply]
    rfl
  have hdim : pb.dim = q := by
    simp only [pb, PowerBasis.map_dim, adjoin.powerBasis_dim, hminx, natDegree_comp,
      natDegree_X_pow_sub_C, natDegree_X_add_C, mul_one]
  have key := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [hgen, hdim, hminx] at key
  rw [key, coeff_zero_eq_eval_zero, eval_comp]
  simp only [eval_add, eval_X, eval_C, zero_add, eval_sub, eval_pow]

theorem ord_norm_root_sub_algebraMap {K : Type*} [Field K] [Algebra K F]
    (v : Place K F) (hf : ∀ g : F, g ^ q ≠ f)
    (hα : α ^ q = algebraMap F E f) (htop : F⟮α⟯ = ⊤) (c : F) :
    v.ord (Algebra.norm F (α - algebraMap F E c)) = v.ord (f - c ^ q) := by
  rw [norm_root_sub_algebraMap hf hα htop c]
  rcases neg_one_pow_eq_or F q with h | h <;> rw [h]
  · rw [one_mul, ← neg_sub, v.ord_neg]
  · rw [neg_one_mul, neg_sub]

end
end Dubon2026.SourceCurve.KummerCover
