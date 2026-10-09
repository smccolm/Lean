import Dubon2026.AdelicLocalClosedHeckeEigen
import Dubon2026.FinitePlaceSphericalCyclicEquiv

/-! # Completed spherical uniqueness for the actual original primitive local factor -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (σ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) W)
    (hσ : ∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y)
    (hcσ : ∀ u x, σ (GeneralLinearGroup.scalar (Fin 2) u) x = x)
    (w : W) (hw : inner ℂ w w = 1)
    (hwK : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), σ g.val w = w)
    (hzw : finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) σ w =
      ((Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p) • w)
    (hwcyclic : (Submodule.span ℂ (Set.range (fun g => σ g w))).topologicalClosure = ⊤)

/-- The actual original primitive local Hilbert factor is isometrically equivalent to every genuine cyclic unitary spherical representation with its actual Fourier Hecke eigenvalue. -/
def adelicLocalSphericalEquiv :
    adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ≃ₗᵢ[ℂ] W :=
  @finitePlaceSphericalCyclicEquiv
    (adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) W
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    p inferInstance inferInstance (adelicLocalCyclicRepresentation F.toCuspForm _) σ
    (adelicLocalCyclicRepresentation_inner F.toCuspForm _) hσ
    (adelicLocalCyclicRepresentation_scalar F.toCuspForm _) hcσ
    (adelicLocalClosedUnitReference F.toCuspForm _) w
    (adelicLocalClosedUnitReference_inner F.toCuspForm (primitiveCuspForm_ne_zero F) _) hw
    (adelicLocalClosedUnitReference_good_fixed F hpN) hwK
    (normalizedCuspCoefficients F.toCuspForm p) (adelicLocalClosedUnitReference_hecke_eigen F hpN) hzw
    (adelicLocalClosedUnitReference_cyclic F.toCuspForm (primitiveCuspForm_ne_zero F) _) hwcyclic

include hσ hcσ hw hwK hzw hwcyclic

/-- The completed equivalence preserves the exact original normalized local group orbit. -/
theorem adelicLocalSphericalEquiv_orbit
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    adelicLocalSphericalEquiv F hpN σ hσ hcσ w hw hwK hzw hwcyclic
      (adelicLocalCyclicRepresentation F.toCuspForm _ g (adelicLocalClosedUnitReference F.toCuspForm _)) = σ g w :=
  finitePlaceSphericalCyclicEquiv_orbit p _ σ _ hσ _ hcσ _ w _ hw _ hwK _ _ hzw _ hwcyclic g

/-- Every actual original local group operator intertwines on the entire original closed Hilbert factor. -/
theorem adelicLocalSphericalEquiv_intertwines
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (x : adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalSphericalEquiv F hpN σ hσ hcσ w hw hwK hzw hwcyclic
      (adelicLocalCyclicRepresentation F.toCuspForm _ g x) =
    σ g (adelicLocalSphericalEquiv F hpN σ hσ hcσ w hw hwK hzw hwcyclic x) :=
  finitePlaceSphericalCyclicEquiv_intertwines p _ σ _ hσ _ hcσ _ w _ hw _ hwK _ _ hzw _ hwcyclic g x

end
end Dubon2026
