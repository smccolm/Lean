import Dubon2026.FixedResidualRepresentationFactors
import Dubon2026.CompletedResidualProPKernel

/-! # A fixed original residual quotient factors all continuous lifts over the actual completed coefficient ring -/

namespace Dubon2026

noncomputable section
open Matrix

universe u
variable {G₀ ι O : Type u} [Group G₀] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G₀] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The original completed residue field carries the genuine maximal-ideal quotient topology. -/
instance completedResidualFieldTopology
    (ρ : G₀ →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    TopologicalSpace (IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ)) :=
  inferInstanceAs (TopologicalSpace (ResidualRepresentationCompletion ρ ⧸
    IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)))

omit [Finite (IsLocalRing.ResidueField O)] in
/-- The kernel of the original continuous residual representation is closed in its genuine profinite source. -/
theorem completedResidualLiftKernel_isClosed
    (ρ : G₀ →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ)))
    (hσ : Continuous σ) : IsClosed (σ.ker : Set H) := by
  letI : DiscreteTopology (IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ)) := by
    have h := adicPowerQuotient_discrete (R := ResidualRepresentationCompletion ρ) 1
    change DiscreteTopology (ResidualRepresentationCompletion ρ ⧸
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ 1) at h
    rw [pow_one] at h
    exact h
  exact isClosed_singleton.preimage hσ

/-- Every actual continuous matrix lift of the original residual representation kills the same original ambient residual common kernel. -/
theorem completedResidualLift_fixedKernel_le
    (ρ : G₀ →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ)))
    (hσ : Continuous σ)
    (f : H →* GeneralLinearGroup ι (ResidualRepresentationCompletion ρ))
    (hf : Continuous f)
    (hres : (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
      (S := IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ))
      (IsLocalRing.residue (ResidualRepresentationCompletion ρ))).comp f = σ) :
    fixedResidualProPKernel p H σ.ker (completedResidualLiftKernel_isClosed ρ H σ hσ) ≤ f.ker := by
  let r : σ.ker →* MatrixCongruenceKernel (ι := ι)
      (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)) :=
    (f.comp σ.ker.subtype).codRestrict _ (fun g => by
      change (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
        (S := IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ))
        (IsLocalRing.residue (ResidualRepresentationCompletion ρ))) (f g.val) = 1
      change ((GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
        (S := IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ))
        (IsLocalRing.residue (ResidualRepresentationCompletion ρ))).comp f) g.val = 1
      rw [hres]
      exact g.property)
  have hr : Continuous r := (hf.comp continuous_subtype_val).subtype_mk _
  have hkill := profiniteProPKernel_le_kernel_of_target_separation p
    (closedSubgroupProfinite H σ.ker (completedResidualLiftKernel_isClosed ρ H σ hσ))
    (completedResidualProfiniteKernel ρ) r hr
    (completedResidualProfiniteKernel_commonKernel_eq_bot ρ p hp)
  rintro _ ⟨g, hg, rfl⟩
  exact congrArg Subtype.val (hkill hg)

/-- The entire original continuous matrix lift descends through the quotient fixed by its original residual representation. -/
def completedResidualLiftFactor
    (ρ : G₀ →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ)))
    (hσ : Continuous σ)
    (f : H →* GeneralLinearGroup ι (ResidualRepresentationCompletion ρ))
    (hf : Continuous f)
    (hres : (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
      (S := IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ))
      (IsLocalRing.residue (ResidualRepresentationCompletion ρ))).comp f = σ) :
    H ⧸ fixedResidualProPKernel p H σ.ker (completedResidualLiftKernel_isClosed ρ H σ hσ) →*
      GeneralLinearGroup ι (ResidualRepresentationCompletion ρ) :=
  QuotientGroup.lift _ f (completedResidualLift_fixedKernel_le ρ p hp H σ hσ f hf hres)

/-- Every original whole matrix is preserved under the genuine fixed residual quotient factor. -/
theorem completedResidualLiftFactor_mk
    (ρ : G₀ →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ)))
    (hσ : Continuous σ)
    (f : H →* GeneralLinearGroup ι (ResidualRepresentationCompletion ρ))
    (hf : Continuous f)
    (hres : (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
      (S := IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ))
      (IsLocalRing.residue (ResidualRepresentationCompletion ρ))).comp f = σ) (g : H) :
    completedResidualLiftFactor ρ p hp H σ hσ f hf hres
      (QuotientGroup.mk' (fixedResidualProPKernel p H σ.ker
        (completedResidualLiftKernel_isClosed ρ H σ hσ)) g) = f g := rfl

/-- The actual factor of every original continuous matrix lift is continuous in the genuine fixed quotient topology. -/
theorem completedResidualLiftFactor_continuous
    (ρ : G₀ →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ)))
    (hσ : Continuous σ)
    (f : H →* GeneralLinearGroup ι (ResidualRepresentationCompletion ρ))
    (hf : Continuous f)
    (hres : (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
      (S := IsLocalRing.ResidueField (ResidualRepresentationCompletion ρ))
      (IsLocalRing.residue (ResidualRepresentationCompletion ρ))).comp f = σ) :
    Continuous (completedResidualLiftFactor ρ p hp H σ hσ f hf hres) := by
  apply (QuotientGroup.isQuotientMap_mk (fixedResidualProPKernel p H σ.ker
    (completedResidualLiftKernel_isClosed ρ H σ hσ))).continuous_iff.mpr
  exact hf

end
end Dubon2026
