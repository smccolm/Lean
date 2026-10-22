import Dubon2026.SourceJHeckeConjugation

/-! DUB-17/18 -> actual parabolic Hecke eigensystem realization ->
reflection commutes with the original Hecke sum. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_Period_charInvolution_heckeOperatorHom.
Use the existing original coset transitions and integral reflection.
-/
namespace Dubon2026.SourceJHecke
noncomputable section
open CongruenceSubgroup
open scoped MatrixGroups

/-- The actual reflection permutes the original finite Hecke cosets. -/
def quotientReflection (N p : ℕ) : Gamma0 N ⧸ heckeUpperSubgroup N p ≃
    Gamma0 N ⧸ heckeUpperSubgroup N p where
  toFun := Quotient.map' (sourceJConjugateGamma0Hom N) (fun x y h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    have he : sourceJConjugateGamma0Hom N (x⁻¹ * y) ∈ heckeUpperSubgroup N p :=
      sourceJConjugate_mem_heckeUpper h
    rwa [map_mul, map_inv] at he)
  invFun := Quotient.map' (sourceJConjugateGamma0Hom N) (fun x y h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    have he : sourceJConjugateGamma0Hom N (x⁻¹ * y) ∈ heckeUpperSubgroup N p :=
      sourceJConjugate_mem_heckeUpper h
    rwa [map_mul, map_inv] at he)
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h x =>
      change Quotient.mk'' (sourceJConjugateGamma0 N (sourceJConjugateGamma0 N x)) = Quotient.mk'' x
      rw [sourceJConjugateGamma0_involutive]
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h x =>
      change Quotient.mk'' (sourceJConjugateGamma0 N (sourceJConjugateGamma0 N x)) = Quotient.mk'' x
      rw [sourceJConjugateGamma0_involutive]

theorem quotientReflection_smul (N p : ℕ) (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpperSubgroup N p) :
    quotientReflection N p (g • q) = sourceJConjugateGamma0Hom N g • quotientReflection N p q := by
  induction q using Quotient.inductionOn' with
  | h x =>
    change Quotient.mk'' (sourceJConjugateGamma0Hom N (g * x)) =
      Quotient.mk'' (sourceJConjugateGamma0Hom N g * sourceJConjugateGamma0Hom N x)
    rw [map_mul]

theorem quotientReflection_eq_mk (N p : ℕ) (q : Gamma0 N ⧸ heckeUpperSubgroup N p) :
    quotientReflection N p q = Quotient.mk'' (sourceJConjugateGamma0Hom N q.out) := by
  conv_lhs => rw [← Quotient.out_eq' q]
  rfl

theorem correction_mem (N p : ℕ) (q : Gamma0 N ⧸ heckeUpperSubgroup N p) :
    (quotientReflection N p q).out⁻¹ * sourceJConjugateGamma0Hom N q.out ∈ heckeUpperSubgroup N p := by
  rw [← QuotientGroup.eq, QuotientGroup.out_eq', quotientReflection_eq_mk]

/-- The genuine upper-subgroup correction for the two reflected representatives. -/
def correction (N p : ℕ) (q : Gamma0 N ⧸ heckeUpperSubgroup N p) : heckeUpperSubgroup N p :=
  ⟨(quotientReflection N p q).out⁻¹ * sourceJConjugateGamma0Hom N q.out, correction_mem N p q⟩

theorem transition_reflection (N p : ℕ) (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpperSubgroup N p) :
    cosetTransition (heckeUpperSubgroup N p) (sourceJConjugateGamma0Hom N g) (quotientReflection N p q) =
      correction N p (g • q) * sourceJHeckeUpper N p (cosetTransition (heckeUpperSubgroup N p) g q) *
        (correction N p q)⁻¹ := by
  apply Subtype.ext
  change (sourceJConjugateGamma0Hom N g • quotientReflection N p q).out⁻¹ *
      (sourceJConjugateGamma0Hom N g * (quotientReflection N p q).out) =
    ((quotientReflection N p (g • q)).out⁻¹ * sourceJConjugateGamma0Hom N (g • q).out) *
      sourceJConjugateGamma0Hom N ((g • q).out⁻¹ * (g * q.out)) *
      ((quotientReflection N p q).out⁻¹ * sourceJConjugateGamma0Hom N q.out)⁻¹
  rw [← quotientReflection_smul]
  simp only [map_mul, map_inv]
  group

end
end Dubon2026.SourceJHecke
