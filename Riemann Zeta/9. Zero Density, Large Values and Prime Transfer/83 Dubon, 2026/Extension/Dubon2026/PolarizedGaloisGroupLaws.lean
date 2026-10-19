import Dubon2026.PolarizedGaloisGroup

/-! Source laws for the actual polarized target group, including the distinction
between fixing the similitude and fixing the matrix determinant. The identity
component of the similitude kernel is the whole GL_n, not a special linear
group. This is required for the correct CM deformation problem in DUB-17. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The nontrivial component acts by the exact source involution. -/
theorem polarizedSwitchAction_generator :
    polarizedSwitchAction (R := R) (ι := ι) (Multiplicative.ofAdd (1 : ZMod 2)) =
      polarizedSwitchAut := by
  change (if (1 : ZMod 2) = 0 then 1 else polarizedSwitchAut) = polarizedSwitchAut
  norm_num

/-- The distinguished source element j has square one. -/
theorem polarizedComplexConjugation_sq :
    (polarizedComplexConjugation (R := R) (ι := ι)) ^ 2 = 1 := by
  change (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) :
    PolarizedGaloisGroup ι R) ^ 2 = 1
  rw [← map_pow]
  have h : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by decide
  rw [h, map_one]

/-- The exact matrix-multiplier conjugation law in CHT Section 2.1. -/
theorem polarizedComplexConjugation_conjugate (x : GeneralLinearGroup ι R × Rˣ) :
    polarizedComplexConjugation * polarizedIdentityComponent x * polarizedComplexConjugation⁻¹ =
      polarizedIdentityComponent (polarizedSwitch x) := by
  have h := SemidirectProduct.inl_aut (φ := polarizedSwitchAction (R := R) (ι := ι))
    (Multiplicative.ofAdd (1 : ZMod 2)) x
  rw [polarizedSwitchAction_generator] at h
  simpa only [polarizedComplexConjugation, polarizedIdentityComponent,
    polarizedSwitchAut, map_inv] using h.symm

/-- Both components occur in the constructed polarized group. -/
theorem polarizedComponent_surjective :
    Function.Surjective (polarizedComponent (R := R) (ι := ι)) :=
  SemidirectProduct.rightHom_surjective

/-- The source multiplier assumes every unit value in the original coefficient ring. -/
theorem polarizedSimilitude_surjective :
    Function.Surjective (polarizedSimilitude (R := R) (ι := ι)) := by
  intro u
  exact ⟨polarizedIdentityComponent (1, u), polarizedSimilitude_identityComponent (1, u)⟩

/-- The full general linear group embeds in the identity component with multiplier one. -/
def polarizedLinearInclusion : GeneralLinearGroup ι R →* PolarizedGaloisGroup ι R :=
  polarizedIdentityComponent.comp (MonoidHom.inl _ _)

/-- The original matrix inclusion is faithful. -/
theorem polarizedLinearInclusion_injective :
    Function.Injective (polarizedLinearInclusion (R := R) (ι := ι)) := by
  intro g h he
  exact congrArg (fun x : PolarizedGaloisGroup ι R => x.left.1) he

/-- Fixing the source multiplier on the identity component retains GL_n.
There is no determinant-one condition in this kernel identification. -/
theorem polarizedLinearInclusion_range :
    (polarizedLinearInclusion (R := R) (ι := ι)).range =
      polarizedSimilitude.ker ⊓ polarizedComponent.ker := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    constructor
    · change polarizedSimilitude (polarizedIdentityComponent (g, 1)) = 1
      exact polarizedSimilitude_identityComponent (g, 1)
    · rfl
  · rintro ⟨hν, hc⟩
    obtain ⟨y, rfl⟩ := (show x ∈ (polarizedIdentityComponent (R := R) (ι := ι)).range from
      (polarizedIdentityComponent_range (R := R) (ι := ι)).symm ▸ hc)
    have hy : y.2 = 1 := by
      change polarizedSimilitude (polarizedIdentityComponent y) = 1 at hν
      rwa [polarizedSimilitude_identityComponent] at hν
    refine ⟨y.1, ?_⟩
    change polarizedIdentityComponent (y.1, 1) = polarizedIdentityComponent y
    congr 1
    exact Prod.ext rfl hy.symm

end Dubon2026
