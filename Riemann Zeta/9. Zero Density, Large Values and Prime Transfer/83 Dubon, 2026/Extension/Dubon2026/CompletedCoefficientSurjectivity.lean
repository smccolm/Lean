import Dubon2026.CompletedCoefficientIdealImage
import Dubon2026.AdicCompletionEvaluationKernels
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Surjectivity of the actual map of original adic completions -/

namespace Dubon2026

noncomputable section

variable {O R A : Type*} [CommRing O] [CommRing R] [CommRing A]
  [Algebra O R] [Algebra O A]

/-- An original surjective coefficient map with the actual ideal image induces a surjection of the genuine finitely generated adic completions. -/
theorem adicCoefficientCompletionMap_surjective
    (I : Ideal R) (hI : I.FG) (J : Ideal A) (hJ : J.FG)
    (f : R →ₐ[O] A) (hf : I ≤ Ideal.comap f.toRingHom J)
    (hIJ : I.map f.toRingHom = J) (hsurj : Function.Surjective f) :
    Function.Surjective (adicCoefficientCompletionMap I J f hf) := by
  let F := (adicCoefficientCompletionMap I J f hf).toRingHom
  let K := I.map (algebraMap R (AdicCompletion I R))
  let L := J.map (algebraMap A (AdicCompletion J A))
  have hKL : K.map F = L := adicCoefficientCompletionMap_ideal_image I J f hf hIJ
  letI : IsAdicComplete K (AdicCompletion I R) :=
    (IsAdicComplete.map_algebraMap_iff (R := R) (S := AdicCompletion I R)
      (I := I) (M := AdicCompletion I R)).mpr (AdicCompletion.isAdicComplete (M := R) hI)
  letI : IsAdicComplete L (AdicCompletion J A) :=
    (IsAdicComplete.map_algebraMap_iff (R := A) (S := AdicCompletion J A)
      (I := J) (M := AdicCompletion J A)).mpr (AdicCompletion.isAdicComplete (M := A) hJ)
  letI : IsHausdorff (K.map F) (AdicCompletion J A) := by
    rw [hKL]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := K) F
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J 1 x)
  obtain ⟨r, hr⟩ := hsurj a
  refine ⟨AdicCompletion.of I R r, ?_⟩
  change Ideal.Quotient.mk (K.map F) (F (AdicCompletion.of I R r)) =
    Ideal.Quotient.mk (K.map F) x
  apply Ideal.Quotient.eq.mpr
  rw [hKL]
  change adicCoefficientCompletionMap I J f hf (AdicCompletion.of I R r) - x ∈ L
  rw [adicCoefficientCompletionMap_of, hr]
  have hker : RingHom.ker (AdicCompletion.evalₐ J 1).toRingHom = L := by
    rw [adicCompletion_evaluation_kernel J hJ 1, pow_one]
  rw [← hker]
  change AdicCompletion.evalₐ J 1 (AdicCompletion.of J A a - x) = 0
  rw [map_sub, AdicCompletion.evalₐ_of, ha, sub_self]

end
end Dubon2026
