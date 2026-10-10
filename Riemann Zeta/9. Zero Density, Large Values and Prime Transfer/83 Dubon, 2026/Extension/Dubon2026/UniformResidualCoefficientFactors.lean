import Dubon2026.CompleteLocalAdicCompactness
import Dubon2026.AdicResidualProfiniteKernel
import Dubon2026.FixedResidualRepresentationFactors
import Dubon2026.LocalCoefficientReduction

/-! # One original residual quotient for every genuine complete local coefficient ring -/

namespace Dubon2026

noncomputable section
open Matrix

universe u

/-- The kernel of an original continuous residual matrix representation is closed. -/
theorem originalResidualMatrixKernel_isClosed
    {ι K : Type u} [Fintype ι] [DecidableEq ι] [CommRing K]
    [TopologicalSpace K] [T2Space K]
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι K) (hσ : Continuous σ) :
    IsClosed (σ.ker : Set H) := isClosed_singleton.preimage hσ

variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Every actual continuous lift over any original complete Noetherian local coefficient algebra kills the same kernel determined only by the original residual representation. -/
theorem originalResidual_fixedKernel_le_every_coefficient_lift
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (f : H →* GeneralLinearGroup ι A) (hf : Continuous f)
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp f = σ) :
    fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ) ≤ f.ker := by
  letI : Finite (IsLocalRing.ResidueField A) := Finite.of_injective e e.injective
  letI : T2Space A := completeLocalAdic_t2Space hA
  letI : CompactSpace A := completeLocalAdic_compactSpace hA
  have hpI : (p : A) ∈ (WithIdeal.i : Ideal A) := by
    rw [hA]
    apply (localCoefficientReduction_eq_zero_iff e (p : A)).mp
    rw [map_natCast, CharP.cast_eq_zero]
  let r : σ.ker →* MatrixCongruenceKernel (ι := ι) (WithIdeal.i : Ideal A) :=
    (f.comp σ.ker.subtype).codRestrict _ (fun g => by
      have hresg : GeneralLinearGroup.map (n := ι)
          (localCoefficientReduction e).toRingHom (f g.val) = 1 := by
        change ((GeneralLinearGroup.map (n := ι)
          (localCoefficientReduction e).toRingHom).comp f) g.val = 1
        rw [hres]
        exact g.property
      apply Units.ext
      apply Matrix.ext
      intro i j
      have hentry := congrArg (fun v : GeneralLinearGroup ι (IsLocalRing.ResidueField O) =>
        v.val i j) hresg
      change localCoefficientReduction e ((f g.val).val i j) =
        (1 : Matrix ι ι (IsLocalRing.ResidueField O)) i j at hentry
      have hm : (f g.val).val i j - (1 : Matrix ι ι A) i j ∈ (WithIdeal.i : Ideal A) := by
        rw [hA]
        apply (localCoefficientReduction_eq_zero_iff e _).mp
        rw [map_sub, hentry]
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      have hq := Ideal.Quotient.eq.mpr hm
      change Ideal.Quotient.mk (WithIdeal.i : Ideal A) ((f g.val).val i j) =
        (1 : Matrix ι ι (A ⧸ (WithIdeal.i : Ideal A))) i j
      by_cases hij : i = j <;> simpa [Matrix.one_apply, hij] using hq)
  have hr : Continuous r := (hf.comp continuous_subtype_val).subtype_mk _
  have hkill := profiniteProPKernel_le_kernel_of_target_separation p
    (closedSubgroupProfinite H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ))
    (adicResidualProfiniteKernel (R := A) (ι := ι)) r hr
    (adicResidualProfiniteKernel_commonKernel_eq_bot p hp hpI)
  rintro _ ⟨g, hg, rfl⟩
  exact congrArg Subtype.val (hkill hg)


/-- The entire original continuous lift over each coefficient algebra descends through the one quotient fixed by the original residual representation. -/
def originalResidualCoefficientFactor
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (f : H →* GeneralLinearGroup ι A) (hf : Continuous f)
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp f = σ) :
    H ⧸ fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ) →* GeneralLinearGroup ι A :=
  QuotientGroup.lift _ f
    (originalResidual_fixedKernel_le_every_coefficient_lift hA e p hp H σ hσ f hf hres)

/-- The actual uniform residual factor preserves every original whole matrix value. -/
theorem originalResidualCoefficientFactor_mk
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (f : H →* GeneralLinearGroup ι A) (hf : Continuous f)
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp f = σ) (g : H) :
    originalResidualCoefficientFactor hA e p hp H σ hσ f hf hres
      (QuotientGroup.mk' (fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)) g) = f g := rfl

/-- The original coefficient lift descends continuously in the genuine fixed residual quotient topology. -/
theorem originalResidualCoefficientFactor_continuous
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (f : H →* GeneralLinearGroup ι A) (hf : Continuous f)
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction e).toRingHom).comp f = σ) :
    Continuous (originalResidualCoefficientFactor hA e p hp H σ hσ f hf hres) := by
  apply (QuotientGroup.isQuotientMap_mk
    (fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ))).continuous_iff.mpr
  exact hf

end
end Dubon2026
