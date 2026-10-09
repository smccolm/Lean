import Dubon2026.CompletedResidualField
import Dubon2026.CompletedLocalCoefficientEvaluation

/-! # Genuine uniqueness of original representation evaluation from the residual completion -/

namespace Dubon2026

noncomputable section
open Matrix

variable {O R A : Type*} [CommRing O] [CommRing R] [CommRing A]
  [Algebra O R] [Algebra O A]

/-- Original ideal-compatible maps from a genuine completion to an adically separated target are determined by every original base-ring element. -/
theorem adicCompletion_algHom_ext (I : Ideal R) (hI : I.FG) (J : Ideal A)
    [IsHausdorff J A] (f g : AdicCompletion I R →ₐ[O] A)
    (hf : I.map (algebraMap R (AdicCompletion I R)) ≤ Ideal.comap f.toRingHom J)
    (hg : I.map (algebraMap R (AdicCompletion I R)) ≤ Ideal.comap g.toRingHom J)
    (h : ∀ r, f (algebraMap R (AdicCompletion I R) r) =
      g (algebraMap R (AdicCompletion I R) r)) : f = g := by
  apply AlgHom.ext
  intro x
  apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
  intro n
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have hd : x - algebraMap R (AdicCompletion I R) r ∈
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
    rw [← Ideal.map_pow, ← adicCompletion_evaluation_kernel I hI n]
    change AdicCompletion.evalₐ I n (x - AdicCompletion.of I R r) = 0
    rw [map_sub, AdicCompletion.evalₐ_of, hr, sub_self]
  have hfx := adicCoefficientMap_pow
    (I.map (algebraMap R (AdicCompletion I R))) J f hf n hd
  have hgx := adicCoefficientMap_pow
    (I.map (algebraMap R (AdicCompletion I R))) J g hg n hd
  have he : f x - g x = f (x - algebraMap R (AdicCompletion I R) r) -
      g (x - algebraMap R (AdicCompletion I R) r) := by
    rw [map_sub, map_sub, h r]
    abel
  rw [SModEq.sub_mem]
  change f x - g x ∈ (J ^ n • (⊤ : Ideal A))
  rw [Ideal.smul_eq_mul, Ideal.mul_top, he]
  exact (J ^ n).sub_mem hfx hgx

/-- Every original ideal-compatible coefficient map has a unique actual extension to a complete target once its original ideal is finitely generated. -/
theorem adicCompleteCoefficientMap_unique (I : Ideal R) (hI : I.FG) (J : Ideal A)
    [IsAdicComplete J A] (f : R →ₐ[O] A) (hf : I ≤ Ideal.comap f.toRingHom J)
    (g : AdicCompletion I R →ₐ[O] A)
    (hg : ∀ r, g (algebraMap R (AdicCompletion I R) r) = f r) :
    adicCompleteCoefficientMap I J f hf = g := by
  apply adicCompletion_algHom_ext I hI J
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change adicCompleteCoefficientMap I J f hf (AdicCompletion.of I R r) ∈ J
    rw [adicCompleteCoefficientMap_of]
    exact hf hr
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change g (algebraMap R (AdicCompletion I R) r) ∈ J
    rw [hg]
    exact hf hr
  · intro r
    exact (adicCompleteCoefficientMap_of I J f hf r).trans (hg r).symm

variable {G ι : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [IsLocalRing O] [Group.FG G] [IsNoetherianRing O] [IsLocalRing A]

private theorem completedCoefficientMap_unique_originalValues
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : RepresentationCoordinateFiber ρ (localCoefficientReduction e))
    (h : ResidualRepresentationCompletion ρ →ₐ[O] A)
    (originalValues : ∀ x : ResidualRepresentationLocalRing ρ,
      h (algebraMap (ResidualRepresentationLocalRing ρ) (ResidualRepresentationCompletion ρ) x) =
        localizedCoefficientCoordinateMap ρ e f x) :
    completedLocalCoefficientCoordinateMap ρ e f = h := by
  letI := residualRepresentationLocalRing_isNoetherian ρ
  have finiteKernel : (RingHom.ker (R := ResidualRepresentationLocalRing ρ)
      (S := IsLocalRing.ResidueField O) (localizedResidualRepresentationEvaluation ρ).toRingHom).FG :=
    (isNoetherianRing_iff_ideal_fg (ResidualRepresentationLocalRing ρ)).mp inferInstance _
  let uniqueForIdeal := adicCompleteCoefficientMap_unique (O := O)
    (R := ResidualRepresentationLocalRing ρ) (A := A)
    (RingHom.ker (R := ResidualRepresentationLocalRing ρ)
      (S := IsLocalRing.ResidueField O) (localizedResidualRepresentationEvaluation ρ).toRingHom)
    finiteKernel (IsLocalRing.maximalIdeal A)
  let uniqueForMap := uniqueForIdeal (localizedCoefficientCoordinateMap ρ e f)
    (localizedCoefficientCoordinateMap_ideal ρ e f)
  let uniqueForExtension := uniqueForMap h
  let uniqueness := uniqueForExtension originalValues
  exact uniqueness

/-- Any genuine completed coefficient map giving the original matrix representation is exactly its constructed evaluation from the original residual completion. -/
theorem completedLocalCoefficientCoordinateMap_unique
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : MatrixRepresentationFiber ρ (localCoefficientReduction e))
    (h : ResidualRepresentationCompletion ρ →ₐ[O] A)
    (hh : (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ) (S := A)
      h.toRingHom).comp
      (completedUniversalMatrixRepresentation ρ) = τ.val) :
    completedLocalCoefficientCoordinateMap ρ e
      ((representationCoordinateFiberEquiv ρ (localCoefficientReduction e)).symm τ) = h := by
  let f := (representationCoordinateFiberEquiv ρ (localCoefficientReduction e)).symm τ
  let b : ResidualRepresentationLocalRing ρ →ₐ[O] A := h.comp
    (Algebra.algHom O (ResidualRepresentationLocalRing ρ) (ResidualRepresentationCompletion ρ))
  have hb : localizedCoefficientCoordinateMap ρ e f = b := by
    apply localizedCoefficientCoordinateMap_unique
    intro x
    let q := b.comp (Algebra.algHom O (RepresentationCoordinateAlgebra G ι O)
      (ResidualRepresentationLocalRing ρ))
    have hrep : representationFromCoordinates q = τ.val := by
      apply MonoidHom.ext
      intro g
      apply Units.ext
      apply Matrix.ext
      intro i j
      exact congrArg (fun u : GeneralLinearGroup ι A => u.val i j)
        (DFunLike.congr_fun hh g)
    have hq := congrArg (representationCoordinateEvaluation (R := O)) hrep
    rw [representationCoordinateEvaluation_fromCoordinates] at hq
    exact DFunLike.congr_fun hq x
  have originalValues (x : ResidualRepresentationLocalRing ρ) :
      h (algebraMap (ResidualRepresentationLocalRing ρ) (ResidualRepresentationCompletion ρ) x) =
        localizedCoefficientCoordinateMap ρ e f x :=
    (DFunLike.congr_fun hb x).symm
  exact completedCoefficientMap_unique_originalValues ρ e f h originalValues

end
end Dubon2026
