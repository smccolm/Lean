import Dubon2026.OriginalResidualFramedFibers

/-! # The actual true-residue representation after an original residue-preserving coefficient change -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {ι O A B : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [CommRing B] [IsLocalRing B] [Algebra O B]

/-- Reducing the whole original framed lift after an actual residue-preserving coefficient morphism gives exactly the original residual representation transported to the target's true residue field. -/
theorem originalFramedFiber_coefficient_trueResidue
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (k : A →ₐ[O] B)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρ : OriginalContinuousFramedFiber eA H σ) :
    (GeneralLinearGroup.map (IsLocalRing.residue B)).comp
        ((GeneralLinearGroup.map k.toRingHom).comp ρ.val.toMonoidHom) =
      (GeneralLinearGroup.map eB.symm.toRingHom).comp σ := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply eB.injective
  change localCoefficientReduction eB (k ((ρ.val x).val i j)) =
    eB (eB.symm ((σ x).val i j))
  rw [eB.apply_symm_apply]
  have hk := DFunLike.congr_fun hres ((ρ.val x).val i j)
  have hρ := congrArg (fun v : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => v.val i j)
    (DFunLike.congr_fun ρ.property x)
  exact hk.trans hρ

omit [CommRing B] [IsLocalRing B] [Algebra O B] in
/-- The genuine maximal-ideal reduction of the existing original whole framed lift is its original residual representation transported through the specified true-residue equivalence. -/
theorem originalFramedFiber_trueResidue
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρ : OriginalContinuousFramedFiber eA H σ) :
    (GeneralLinearGroup.map (IsLocalRing.residue A)).comp ρ.val.toMonoidHom =
      (GeneralLinearGroup.map eA.symm.toRingHom).comp σ :=
  originalFramedFiber_coefficient_trueResidue eA eA (AlgHom.id O A) rfl H σ ρ

end
end Dubon2026
