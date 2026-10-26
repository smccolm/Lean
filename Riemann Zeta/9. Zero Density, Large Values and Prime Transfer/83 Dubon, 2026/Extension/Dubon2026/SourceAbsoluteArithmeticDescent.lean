import Dubon2026.SourceAbsoluteFiniteUnramified
import Dubon2026.SourceNumberFieldSupportRamification
import Dubon2026.SourceAbsoluteArithmeticRestriction
import Dubon2026.OriginalSupportRamificationTransport

/-! DUB-17/18 -> residual association -> arithmetic quotient.
Construct the faithful finite factor of the actual representation,
derive its ramification from actual norm-local inertia, and reuse the
proved original-support embedding. The result factors the same global
representation continuously through the prescribed arithmetic group. -/
namespace Dubon2026
noncomputable section
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

theorem absolute_continuous_normInertia_arithmetic_descent
    {T : Type} [Group T] [TopologicalSpace T] [DiscreteTopology T]
    (a : ℕ) (χ : Gal(Qbar/ℚ) →ₜ* T)
    (hI : ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ a →
      ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure p hp)
        (g : Gal(rationalPrimeLocalClosure p hp/rationalPrimeLocalField p hp)),
        g ∈ rationalPrimeNormInertia p hp → χ (embeddedNormalGaloisRestriction e g) = 1) :
    ∃ η : rationalArithmeticGaloisGroup (a : 𝓞 ℚ) →ₜ* T,
      ∀ g, η (sourceAbsoluteArithmeticRestriction (a : 𝓞 ℚ) g) = χ g := by
  obtain ⟨F, ψ, hψinj, hψ⟩ := continuous_galois_faithful_finite_factor χ
  letI : NumberField F := NumberField.of_module_finite ℚ F
  have hU : ∀ p : ℕ, p.Prime → ¬p ∣ a →
      Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}) := by
    intro p hp hpa
    exact absolute_faithful_factor_unramified χ.toMonoidHom F ψ hψinj hψ p hp (hI p hp hpa)
  have hF : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      algebraMap (𝓞 ℚ) (𝓞 F) (a : 𝓞 ℚ) ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1 := by
    intro w hw
    exact numberField_support_ramification_of_rational_unramified F a hU w
      (by simpa only [map_natCast] using hw)
  obtain ⟨i, hi⟩ := originalSupport_exists_embedding F.val (a : 𝓞 ℚ) hF
  let U := rationalUnramifiedExtension (a : 𝓞 ℚ)
  letI : Algebra ℚ U := U.algebra'
  let r : rationalArithmeticGaloisGroup (a : 𝓞 ℚ) →* Gal(F/ℚ) :=
    embeddedNormalGaloisRestriction (F := ℚ) i
  have hc : Continuous r := embeddedNormalGaloisRestriction_continuous i
  have hψc : Continuous ψ := continuous_of_discreteTopology
  let η : rationalArithmeticGaloisGroup (a : 𝓞 ℚ) →ₜ* T :=
    ⟨ψ.comp r, hψc.comp hc⟩
  refine ⟨η, ?_⟩
  intro g
  have hr : r (sourceAbsoluteArithmeticRestriction (a : 𝓞 ℚ) g) =
      AlgEquiv.restrictNormalHom F g := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    calc
      (r (sourceAbsoluteArithmeticRestriction (a : 𝓞 ℚ) g) x : Qbar) =
          (i (r (sourceAbsoluteArithmeticRestriction (a : 𝓞 ℚ) g) x) : Qbar) := (hi _).symm
      _ = ((show Gal(U/ℚ) from sourceAbsoluteArithmeticRestriction (a : 𝓞 ℚ) g) (i x) : Qbar) :=
        congrArg (fun y : U => (y : Qbar))
          (embeddedNormalGaloisRestriction_commutes i
            (show Gal(U/ℚ) from sourceAbsoluteArithmeticRestriction (a : 𝓞 ℚ) g) x)
      _ = g (i x) := sourceAbsoluteArithmeticRestriction_commutes (a : 𝓞 ℚ) g (i x)
      _ = g (x : Qbar) := congrArg g (hi x)
      _ = (AlgEquiv.restrictNormalHom F g x : Qbar) := (g.restrictNormal_commutes F x).symm
  change ψ (r (sourceAbsoluteArithmeticRestriction (a : 𝓞 ℚ) g)) = χ g
  rw [hr]
  exact hψ g

end
end Dubon2026
