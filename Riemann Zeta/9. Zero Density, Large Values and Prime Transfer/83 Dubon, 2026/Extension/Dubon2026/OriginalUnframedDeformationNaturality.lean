import Dubon2026.OriginalUnframedDeformationClasses
import Dubon2026.OriginalFramedFiberNaturality

/-! # Actual continuous coefficient changes on the original unframed deformation classes -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {ι O A B : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B]

/-- The existing original framed coefficient-change map carries actual strict conjugators to actual strict conjugators, using the same original residue compatibility. -/
theorem originalFramedFiberPostcomp_strictlyConjugate
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (ρ τ : OriginalContinuousFramedFiber eA H σ)
    (h : MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
      ρ.val.toMonoidHom τ.val.toMonoidHom) :
    MatrixStrictlyConjugate (localCoefficientReduction eB).toRingHom
      (originalFramedFiberPostcomp eA eB H σ k hk hres ρ).val.toMonoidHom
      (originalFramedFiberPostcomp eA eB H σ k hk hres τ).val.toMonoidHom := by
  obtain ⟨U, hU, hconj⟩ := h
  refine ⟨GeneralLinearGroup.map k.toRingHom U, ?_, ?_⟩
  · change GeneralLinearGroup.map ((localCoefficientReduction eB).comp k).toRingHom U = 1
    rw [hres]
    exact hU
  · intro x
    change GeneralLinearGroup.map k.toRingHom (τ.val x) =
      GeneralLinearGroup.map k.toRingHom U * GeneralLinearGroup.map k.toRingHom (ρ.val x) *
        (GeneralLinearGroup.map k.toRingHom U)⁻¹
    have hx : τ.val x = U * ρ.val x * U⁻¹ := hconj x
    rw [hx, map_mul, map_mul, map_inv]

/-- The actual original coefficient morphism acts on genuine unframed deformation classes by the existing framed coefficient-change map. -/
def originalUnframedPostcomp
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    OriginalUnframedDeformationClass eA H σ → OriginalUnframedDeformationClass eB H σ :=
  Quotient.map (originalFramedFiberPostcomp eA eB H σ k hk hres)
    (fun ρ τ h => originalFramedFiberPostcomp_strictlyConjugate eA eB H σ k hk hres ρ τ h)

/-- The original unframed coefficient change evaluates on each actual original framed representative. -/
theorem originalUnframedPostcomp_class
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (ρ : OriginalContinuousFramedFiber eA H σ) :
    originalUnframedPostcomp eA eB H σ k hk hres (originalUnframedClass eA H σ ρ) =
      originalUnframedClass eB H σ (originalFramedFiberPostcomp eA eB H σ k hk hres ρ) := rfl

omit [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] in
/-- The actual identity coefficient morphism acts as the identity on every original unframed deformation class. -/
theorem originalUnframedPostcomp_id
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (q : OriginalUnframedDeformationClass eA H σ) :
    originalUnframedPostcomp eA eA H σ (AlgHom.id O A) continuous_id rfl q = q := by
  refine Quotient.inductionOn q ?_
  intro ρ
  apply congrArg (originalUnframedClass eA H σ)
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro x
  apply Units.ext
  apply Matrix.ext
  intro i j
  rfl

/-- Composing the actual continuous residue-preserving original coefficient morphisms composes their maps on the whole original unframed deformation classes. -/
theorem originalUnframedPostcomp_comp {C : Type u}
    [CommRing C] [IsLocalRing C] [Algebra O C] [WithIdeal C]
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (k : A →ₐ[O] B) (hk : Continuous k)
    (hkres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA)
    (l : B →ₐ[O] C) (hl : Continuous l)
    (hlres : (localCoefficientReduction eC).comp l = localCoefficientReduction eB)
    (q : OriginalUnframedDeformationClass eA H σ) :
    originalUnframedPostcomp eB eC H σ l hl hlres
      (originalUnframedPostcomp eA eB H σ k hk hkres q) =
    originalUnframedPostcomp eA eC H σ (l.comp k) (hl.comp hk)
      (by
        apply AlgHom.ext
        intro x
        exact (DFunLike.congr_fun hlres (k x)).trans (DFunLike.congr_fun hkres x)) q := by
  refine Quotient.inductionOn q ?_
  intro ρ
  apply congrArg (originalUnframedClass eC H σ)
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro x
  apply Units.ext
  apply Matrix.ext
  intro i j
  rfl

end
end Dubon2026
