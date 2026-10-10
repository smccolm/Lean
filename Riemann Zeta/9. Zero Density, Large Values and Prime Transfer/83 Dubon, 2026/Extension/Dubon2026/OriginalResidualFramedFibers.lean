import Dubon2026.UniformResidualCoefficientFactors
import Dubon2026.ClosedProfiniteQuotients

/-! # Actual whole-group framed lifts and their fixed residual quotient -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- Every genuine continuous matrix lift of the original whole residual representation, with the fixed frame retained. -/
abbrev OriginalContinuousFramedFiber
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :=
  {f : H →ₜ* GeneralLinearGroup ι A //
    (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp
      f.toMonoidHom = σ}

/-- The original residual representation itself descends continuously to the genuine fixed residual quotient. -/
def fixedResidualOriginalRepresentation
    (p : ℕ) (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ) :
    fixedResidualProfiniteQuotient p H σ.ker
      (originalResidualMatrixKernel_isClosed H σ hσ) →ₜ*
        GeneralLinearGroup ι (IsLocalRing.ResidueField O) := by
  let N := fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)
  refine ⟨QuotientGroup.lift N σ
    (fixedResidualProPKernel_le p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)), ?_⟩
  apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
  exact hσ

omit [Finite (IsLocalRing.ResidueField O)] in
/-- The genuine quotient representation preserves each original residual matrix. -/
theorem fixedResidualOriginalRepresentation_mk
    (p : ℕ) (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (h : H) :
    fixedResidualOriginalRepresentation p H σ hσ
      (QuotientGroup.mk' (fixedResidualProPKernel p H σ.ker
        (originalResidualMatrixKernel_isClosed H σ hσ)) h) = σ h := rfl

/-- Pull back an actual continuous framed representation along the original fixed quotient map. -/
def originalFramedFiberFromFixedQuotient
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (f : OriginalContinuousFramedFiber e
      (fixedResidualProfiniteQuotient p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ))
      (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom) :
    OriginalContinuousFramedFiber e H σ := by
  let q : H →ₜ* fixedResidualProfiniteQuotient p H σ.ker
      (originalResidualMatrixKernel_isClosed H σ hσ) :=
    ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  refine ⟨f.val.comp q, ?_⟩
  apply MonoidHom.ext
  intro h
  exact DFunLike.congr_fun f.property (q h)

variable [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Every actual complete-local framed lift descends to the same original residual quotient, with its original residue condition. -/
def originalFramedFiberToFixedQuotient
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (f : OriginalContinuousFramedFiber e H σ) :
    OriginalContinuousFramedFiber e
      (fixedResidualProfiniteQuotient p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ))
      (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom := by
  refine ⟨⟨originalResidualCoefficientFactor hA e p hp H σ hσ
    f.val.toMonoidHom f.val.continuous f.property,
    originalResidualCoefficientFactor_continuous hA e p hp H σ hσ
      f.val.toMonoidHom f.val.continuous f.property⟩, ?_⟩
  apply MonoidHom.ext
  intro x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
    (fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)) x
  exact DFunLike.congr_fun f.property h

/-- The whole original framed fiber is equivalent to the actual fixed-quotient fiber; neither side identifies representations by conjugacy. -/
def originalFramedFiberFixedQuotientEquiv
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ) :
    OriginalContinuousFramedFiber e H σ ≃
      OriginalContinuousFramedFiber e
        (fixedResidualProfiniteQuotient p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ))
        (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom where
  toFun := originalFramedFiberToFixedQuotient hA e p hp H σ hσ
  invFun := originalFramedFiberFromFixedQuotient e p H σ hσ
  left_inv f := by
    apply Subtype.ext
    apply DFunLike.ext
    intro h
    rfl
  right_inv f := by
    apply Subtype.ext
    apply DFunLike.ext
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
      (fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)) x
    rfl

/-- The genuine quotient-fiber equivalence preserves every original whole matrix under the quotient projection. -/
theorem originalFramedFiberFixedQuotientEquiv_mk
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (f : OriginalContinuousFramedFiber e H σ) (h : H) :
    (originalFramedFiberFixedQuotientEquiv hA e p hp H σ hσ f).val
      (QuotientGroup.mk' (fixedResidualProPKernel p H σ.ker
        (originalResidualMatrixKernel_isClosed H σ hσ)) h) = f.val h := rfl

end
end Dubon2026
