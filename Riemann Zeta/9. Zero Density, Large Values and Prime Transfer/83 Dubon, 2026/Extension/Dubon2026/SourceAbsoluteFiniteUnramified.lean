import Dubon2026.SourceNumberFieldNormInertiaLift
import Dubon2026.SourceRationalLocalValuation
import Dubon2026.NumberFieldUnramifiedOfTrivialInertia
import Dubon2026.ContinuousGaloisFaithfulFiniteFactor

/-! DUB-17/18 -> arithmetic quotient of the actual residual representation
-> unramified faithful finite factor. The already constructed norm-local
inertia lifts and faithfulness force the actual finite field inertia to
vanish. No arithmetic-union containment or field ramification is assumed. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois

private local instance (F : FiniteGaloisIntermediateField ℚ Qbar)
    (α : Algebra ℚ F) : @IsGalois ℚ _ F _ α := by
  have he : F.algebra' = α := Subsingleton.elim _ _
  exact Eq.mp (congrArg (fun β : Algebra ℚ F => @IsGalois ℚ _ F _ β) he) F.isGalois

theorem absolute_faithful_factor_unramified
    {T : Type} [Group T] (χ : Gal(Qbar/ℚ) →* T)
    (F : FiniteGaloisIntermediateField ℚ Qbar)
    (ψ : Gal(F/ℚ) →* T) (hψinj : Function.Injective ψ)
    (hψ : ∀ g, ψ (AlgEquiv.restrictNormalHom F g) = χ g)
    (p : ℕ) (hp : p.Prime)
    (hI : ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure p hp)
      (g : Gal(rationalPrimeLocalClosure p hp/rationalPrimeLocalField p hp)),
        g ∈ rationalPrimeNormInertia p hp → χ (embeddedNormalGaloisRestriction e g) = 1) :
    Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}) := by
  letI : NumberField F := NumberField.of_module_finite ℚ F
  let e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure p hp := IsAlgClosed.lift
  have hlift := numberField_embedded_inertia_exists_norm_lift F p hp (e.comp F.val)
  rcases hlift with ⟨w, hw, hs⟩
  letI := hw
  have hbot : w.asIdeal.inertia Gal(F/ℚ) = ⊥ := by
    apply le_antisymm _ bot_le
    intro σ hσ
    change σ = 1
    rcases hs σ hσ with ⟨g, hg, he⟩
    have hr : AlgEquiv.restrictNormalHom F (embeddedNormalGaloisRestriction e g) = σ := by
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      apply e.injective
      have hfirst := congrArg e ((embeddedNormalGaloisRestriction e g).restrictNormal_commutes F x)
      exact hfirst.trans ((embeddedNormalGaloisRestriction_commutes e g (x : Qbar)).trans (he x))
    apply hψinj
    have hv := hψ (embeddedNormalGaloisRestriction e g)
    rw [hr] at hv
    exact hv.trans ((hI e g hg).trans ψ.map_one.symm)
  have hu := numberField_unramifiedIn_of_inertia_eq_bot (rationalOriginalPrimePlace p hp) w hbot
  simpa only [rationalOriginalPrimePlace_eq_span] using hu

end
end Dubon2026
