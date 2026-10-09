import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Literal ideal kernels of actual adic completion evaluations -/

namespace Dubon2026

noncomputable section

variable {R : Type*} [CommRing R]

/-- The kernel of the genuine nth completion evaluation is exactly the image of the original nth ideal power. -/
theorem adicCompletion_evaluation_kernel (I : Ideal R) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext x
  have hm : x ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)) ↔
      AdicCompletion.eval I R n x = 0 := by
    change x ∈ ((I ^ n).map (algebraMap R (AdicCompletion I R))).restrictScalars R ↔ _
    rw [← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hI]
    rfl
  rw [hm]
  let e := Ideal.quotientEquivAlgOfEq R (show (I ^ n • (⊤ : Ideal R)) = I ^ n by simp)
  change e (AdicCompletion.eval I R n x) = 0 ↔ AdicCompletion.eval I R n x = 0
  exact EmbeddingLike.map_eq_zero_iff

variable {O A : Type*} [CommRing O] [CommRing A] [Algebra O R] [Algebra O A]

/-- For an actual surjective coefficient map with finitely generated kernel, the genuine completed residual projection has exactly the extended original kernel. -/
theorem adicCompletion_kerProj_kernel (f : R →ₐ[O] A) (hf : Function.Surjective f)
    (hI : (RingHom.ker f.toRingHom).FG) :
    RingHom.ker (AdicCompletion.kerProj hf).toRingHom =
      (RingHom.ker f.toRingHom).map
        (algebraMap R (AdicCompletion (RingHom.ker f.toRingHom) R)) := by
  let I := RingHom.ker f.toRingHom
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let e₁ := Ideal.quotientEquivAlgOfEq R (pow_one I)
  ext x
  change e (e₁ (AdicCompletion.evalₐ I 1 x)) = 0 ↔ _
  rw [EmbeddingLike.map_eq_zero_iff]
  have he₁ : e₁ (AdicCompletion.evalₐ I 1 x) = 0 ↔ AdicCompletion.evalₐ I 1 x = 0 := by
    constructor
    · intro h
      apply e₁.injective
      exact h.trans (map_zero e₁).symm
    · intro h
      rw [h, map_zero]
  apply he₁.trans
  change x ∈ RingHom.ker (AdicCompletion.evalₐ I 1).toRingHom ↔ _
  rw [adicCompletion_evaluation_kernel I hI 1, pow_one]
  rfl

end
end Dubon2026
