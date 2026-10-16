import Dubon2026.OriginalAdicBaseChangeNaturality
import Dubon2026.OriginalFullIdeleCompletionCocycle
import Dubon2026.GaloisUnitBaseChange

/-! # Original completion transport over the same completed base field

Reuse the original continuous Galois transport and its proved base-field
naturality. The resulting completion algebra equivalence identifies
actual local Galois restriction with global conjugation. This is needed
to extend DUB-17's canonical-prime normalization to every upper prime.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (u w : HeightOneSpectrum (𝓞 L))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  (σ : Gal(L/K)) (hσ : numberFieldGaloisPlaceEquiv K L σ u = w)

/-- The original completed Galois transport is linear over the same actual base completion. -/
def originalAdicPrimeTransportAlgEquiv :
    letI : Algebra (v.adicCompletion K) (u.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v u).toAlgebra
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    u.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v u).toAlgebra
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  exact { numberFieldGaloisLocalTransport K L σ u w hσ with
    commutes' := originalAdicBaseChangeMap_transport K L v u w σ hσ }

/-- The same completion algebra equivalence retains the actual global Galois action on the dense original field. -/
theorem originalAdicPrimeTransportAlgEquiv_algebraMap (x : L) :
    originalAdicPrimeTransportAlgEquiv K L v u w σ hσ (algebraMap L (u.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) (σ x) :=
  numberFieldGaloisLocalTransport_algebraMap K L σ u w hσ x

variable [FiniteDimensional K L] [IsGalois K L]

/-- Pulling an actual completion automorphism through original prime transport conjugates its original global restriction by that same global automorphism. -/
theorem originalCompletionGaloisRestriction_prime_transport :
    letI : Algebra (v.adicCompletion K) (u.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v u).toAlgebra
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    let e := originalAdicPrimeTransportAlgEquiv K L v u w σ hσ
    letI : Algebra (u.adicCompletion L) (w.adicCompletion L) := e.toRingHom.toAlgebra
    letI : IsScalarTower (v.adicCompletion K) (u.adicCompletion L) (w.adicCompletion L) :=
      IsScalarTower.of_algHom e.toAlgHom
    letI : IsGalois (v.adicCompletion K) (u.adicCompletion L) :=
      (originalAdicBaseChange_finite_galois K L v u).2
    ∀ g : Gal(w.adicCompletion L/v.adicCompletion K),
      originalCompletionGaloisRestriction K L v u
        (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
          (u.adicCompletion L) (w.adicCompletion L) g) =
      (MulAut.conj σ⁻¹) (originalCompletionGaloisRestriction K L v w g) := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v u).toAlgebra
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  let e := originalAdicPrimeTransportAlgEquiv K L v u w σ hσ
  letI : Algebra (u.adicCompletion L) (w.adicCompletion L) := e.toRingHom.toAlgebra
  letI : IsScalarTower (v.adicCompletion K) (u.adicCompletion L) (w.adicCompletion L) :=
    IsScalarTower.of_algHom e.toAlgHom
  letI : IsGalois (v.adicCompletion K) (u.adicCompletion L) :=
    (originalAdicBaseChange_finite_galois K L v u).2
  change ∀ g : Gal(w.adicCompletion L/v.adicCompletion K),
    originalCompletionGaloisRestriction K L v u
      (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
        (u.adicCompletion L) (w.adicCompletion L) g) =
      (MulAut.conj σ⁻¹) (originalCompletionGaloisRestriction K L v w g)
  intro g
  let b := galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
    (u.adicCompletion L) (w.adicCompletion L) g
  apply AlgEquiv.ext
  intro x
  apply σ.injective
  change σ (originalCompletionGaloisRestriction K L v u b x) =
    σ (σ⁻¹ (originalCompletionGaloisRestriction K L v w g (σ x)))
  change σ (originalCompletionGaloisRestriction K L v u b x) =
    σ (σ.symm (originalCompletionGaloisRestriction K L v w g (σ x)))
  rw [AlgEquiv.apply_symm_apply]
  apply (algebraMap L (w.adicCompletion L)).injective
  calc
    _ = e (algebraMap L (u.adicCompletion L)
        (originalCompletionGaloisRestriction K L v u b x)) :=
      (originalAdicPrimeTransportAlgEquiv_algebraMap K L v u w σ hσ _).symm
    _ = e (b (algebraMap L (u.adicCompletion L) x)) :=
      congrArg e (originalCompletionGaloisRestriction_commutes K L v u b x)
    _ = g (e (algebraMap L (u.adicCompletion L) x)) :=
      galoisBaseChangeRestriction_commutes (v.adicCompletion K) (v.adicCompletion K)
        (u.adicCompletion L) (w.adicCompletion L) g _
    _ = g (algebraMap L (w.adicCompletion L) (σ x)) :=
      congrArg g (originalAdicPrimeTransportAlgEquiv_algebraMap K L v u w σ hσ x)
    _ = _ := (originalCompletionGaloisRestriction_commutes K L v w g (σ x)).symm

end
end Dubon2026
