import Dubon2026.SourceLaurentPolynomialRealization
import Dubon2026.SourceInvariantPowerCoefficients
import Dubon2026.SourceJPrincipalPart
import Dubon2026.SourceModularJLaurentSum

/-! DUB-17/18 -> cusp-form lower dimension bound -> regular differential
realization -> original finite function-field extension -> modular polynomial
relations -> rational coefficient descent. This selects the literal Laurent
principal-part removal and the actual analytic realization argument, reusing
pinned weight-zero constancy and q-expansion coefficient uniqueness. No
polynomial relation or coefficient descent is postulated.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups ModularForm
local notation "𝕢" => Function.Periodic.qParam

section JT

/-- The actual analytic j quotient of normalized E4 cubed by the discriminant. -/
def jt (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

/-- The original rational coefficient embedding into the complex numbers. -/
abbrev castC : ℚ →+* ℂ := Rat.castHom ℂ

/-- The complex coefficient image of the original rational j Laurent series. -/
def jqC : LaurentSeries ℂ := coeffMap castC jq

lemma jqC_coeff (m : ℤ) : jqC.coeff m = ((jq.coeff m : ℚ) : ℂ) := rfl

lemma realL_jqC : RealL 1 jqC jt := fun τ => Dubon2026.SourceFunctionField.hasSum_jq_qParam τ

end JT

section JOut

lemma jt_smul (γ : SL(2, ℤ)) (τ : ℍ) : jt (γ • τ) = jt τ :=
  Dubon2026.SourceFunctionField.E4_cube_div_discriminant_smul γ τ

lemma realL_aeval_jq (P : Polynomial ℚ) :
    RealL 1 (coeffMap castC (Polynomial.aeval jq P)) (fun τ => (P.map castC).eval (jt τ)) := by
  induction P using Polynomial.induction_on with
  | C a =>
    refine (RealL.C 1 (a : ℂ)).congr ?_ fun τ => ?_
    · rw [Polynomial.aeval_C, SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single]
      rfl
    · simp
  | add P Q hP hQ =>
    refine (hP.add hQ).congr ?_ fun τ => ?_
    · rw [map_add, map_add]
    · simp
  | monomial n a ih =>
    refine (ih.mul one_pos realL_jqC).congr ?_ fun τ => ?_
    · rw [jqC, ← map_mul]
      congr 1
      symm
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    · simp [pow_succ, mul_assoc]

theorem mem_adjoin_jq_of_realL_invariant (f : LaurentSeries ℚ) (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = F τ) : f ∈ Algebra.adjoin ℚ {jq} := by

  obtain ⟨n, hn⟩ := exists_poleOrderLE f

  obtain ⟨P, -, he⟩ := Dubon2026.SourceFunctionField.exists_aeval_jq_sub_holomorphicAtInfty n f hn
  set e : LaurentSeries ℚ := f - Polynomial.aeval jq P with he_def
  have he0 : ∀ m : ℤ, m < 0 → e.coeff m = 0 := fun m hm => he m (by simpa using hm)
  have hfR : RealL 1 (coeffMap castC f) F := hF
  have hE : RealL 1 (coeffMap castC e) (F - fun τ => (P.map castC).eval (jt τ)) := by
    rw [he_def, map_sub]
    exact hfR.sub (realL_aeval_jq P)
  have hEinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
      (F - fun τ => (P.map castC).eval (jt τ)) (γ • τ) = (F - fun τ => (P.map castC).eval (jt τ)) τ := by
    intro γ τ
    simp only [Pi.sub_apply, hinv γ τ, jt_smul γ τ]

  have hEN : ∀ τ : ℍ, HasSum (fun n : ℕ => ((e.coeff n : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ n)
      ((F - fun τ => (P.map castC).eval (jt τ)) τ) := by
    intro τ
    have h := hE τ
    rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff] at h
    · exact h
    · intro m hm
      have hm' : m < 0 := by
        by_contra hge
        push Not at hge
        exact hm ⟨m.toNat, Int.toNat_of_nonneg hge⟩
      rw [coeffMap_coeff, he0 m hm', map_zero, zero_mul]
  have hvan : ∀ n : ℕ, n ≠ 0 → e.coeff n = 0 := fun n hn => by
    have := coeff_eq_zero_of_hasSum_of_slash_invariant hEN hEinv hn
    exact_mod_cast this

  have heconst : e = HahnSeries.single 0 (e.coeff 0) := by
    ext m
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · rw [he0 m hm, HahnSeries.coeff_single_of_ne hm.ne]
    · rw [HahnSeries.coeff_single_same]
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm.le
      rw [HahnSeries.coeff_single_of_ne (by exact_mod_cast hm.ne')]
      exact hvan n (by exact_mod_cast hm.ne')
  have hck : f = algebraMap ℚ (LaurentSeries ℚ) (e.coeff 0) + Polynomial.aeval jq P := by
    rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, ← heconst, he_def, sub_add_cancel]
  rw [hck]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (Polynomial.aeval_mem_adjoin_singleton ℚ jq)

end JOut

end
end Dubon2026.SourceFunctionField
