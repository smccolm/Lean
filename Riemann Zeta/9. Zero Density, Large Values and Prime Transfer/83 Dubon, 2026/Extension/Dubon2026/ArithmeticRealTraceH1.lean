import Dubon2026.ArithmeticExceptionalLocalization
import Dubon2026.ArithmeticRealH2Restriction

/-! # Removing the actual real H1 coordinate at odd coefficient primes

The global image--kernel assertion uses all exceptional places, including the
real place. Existing finite-group averaging removes that coordinate for odd q.
The finite-prime product is therefore the genuine all-place H1 product with a
proved zero real factor. This does not prove the reverse arithmetic inclusion.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

/-- Every actual real-place continuous H1 class is zero at an odd coefficient prime. -/
theorem realPlaceFiniteCoefficientH1_eq_zero (q : ℕ) [Fact q.Prime]
    (A : Rep (ZMod q) Gal(ℂ/ℝ))
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
    (hA : Continuous (fun z : Gal(ℂ/ℝ) × A => A.ρ z.1 z.2))
    (hq2 : q ≠ 2) (x : ContinuousRepresentationH1 A hA) : x = 0 := by
  haveI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois ℝ ℂ := {}
  letI : Fintype Gal(ℂ/ℝ) := Fintype.ofFinite _
  have hc : Fintype.card Gal(ℂ/ℝ) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]
  have hq : 2 < q := by
    have := (Fact.out : q.Prime).two_le
    omega
  have hn : (Fintype.card Gal(ℂ/ℝ) : ZMod q) ≠ 0 := by
    rw [hc]
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by decide) hq ((ZMod.natCast_eq_zero_iff 2 q).mp h)
  exact continuousFiniteH1_eq_zero A hA hn x

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q)) (hσ : Continuous σ)

/-- Original trace-zero deformation H1 at the actual real arithmetic restriction. -/
def rationalArithmeticRealTraceH1Module : ModuleCat (ZMod q) :=
  ModuleCat.of (ZMod q) (ContinuousTraceZeroAdjointH1
    (σ.comp (rationalRealArithmeticRestriction a).toMonoidHom)
    (hσ.comp (rationalRealArithmeticRestriction a).continuous))

/-- Original globally twisted coefficients restricted to the actual real place. -/
def rationalArithmeticRealTraceDualH1Module : ModuleCat (ZMod q) :=
  let A := matrixTraceZeroCharacterRep σ
    (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
  let hA := matrixTraceZeroCharacterAction_continuous σ hσ
    (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
    (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous
  let j := rationalRealArithmeticRestriction a
  ModuleCat.of (ZMod q) (ContinuousRepresentationH1 (restrictedCoefficientRep A j.toMonoidHom)
    (restrictedCoefficientAction_continuous A j.toMonoidHom j.continuous hA))

/-- The real deformation factor is zero, by the original cohomology comparison and averaging. -/
theorem rationalArithmeticRealTraceH1_eq_zero (hq2 : q ≠ 2)
    (x : rationalArithmeticRealTraceH1Module a q σ hσ) : x = 0 := by
  let ρ := σ.comp (rationalRealArithmeticRestriction a).toMonoidHom
  let hρ := hσ.comp (rationalRealArithmeticRestriction a).continuous
  exact realPlaceFiniteCoefficientH1_eq_zero q (matrixTraceZeroAdjointRep ρ)
    (matrixTraceZeroAdjointAction_continuous ρ hρ) hq2 x

/-- The actual restricted global dual coefficient factor is also zero at the real place. -/
theorem rationalArithmeticRealTraceDualH1_eq_zero (hq2 : q ≠ 2)
    (x : rationalArithmeticRealTraceDualH1Module a q hqa σ hσ) : x = 0 := by
  exact realPlaceFiniteCoefficientH1_eq_zero q _ _ hq2 x

variable (ha : a ≠ 0)

/-- Forgetting the proved zero real factor identifies the full exceptional deformation product. -/
def rationalArithmeticTraceAllPlacesEquiv (hq2 : q ≠ 2) :
    (RationalArithmeticExceptionalTraceH1 a q ha σ hσ ×
      rationalArithmeticRealTraceH1Module a q σ hσ) ≃ₗ[ZMod q]
      RationalArithmeticExceptionalTraceH1 a q ha σ hσ := by
  letI : Unique (rationalArithmeticRealTraceH1Module a q σ hσ) := {
    default := 0
    uniq x := rationalArithmeticRealTraceH1_eq_zero a q σ hσ hq2 x }
  exact LinearEquiv.prodUnique

/-- Forgetting the proved zero real dual factor identifies the full exceptional dual product. -/
def rationalArithmeticTraceDualAllPlacesEquiv (hq2 : q ≠ 2) :
    (RationalArithmeticExceptionalTraceDualH1 a q ha σ hσ ×
      rationalArithmeticRealTraceDualH1Module a q hqa σ hσ) ≃ₗ[ZMod q]
      RationalArithmeticExceptionalTraceDualH1 a q ha σ hσ := by
  letI : Unique (rationalArithmeticRealTraceDualH1Module a q hqa σ hσ) := {
    default := 0
    uniq x := rationalArithmeticRealTraceDualH1_eq_zero a q hqa σ hσ hq2 x }
  exact LinearEquiv.prodUnique

/-- Simultaneous original trace-zero restriction at every exceptional finite place and the real place. -/
def rationalArithmeticTraceAllPlacesLocalization :
    ContinuousTraceZeroAdjointH1 σ hσ →ₗ[ZMod q]
      (RationalArithmeticExceptionalTraceH1 a q ha σ hσ ×
        rationalArithmeticRealTraceH1Module a q σ hσ) :=
  (rationalArithmeticTraceH1Localization a q ha σ hσ).prod
    (show ContinuousTraceZeroAdjointH1 σ hσ →ₗ[ZMod q]
      rationalArithmeticRealTraceH1Module a q σ hσ from
        continuousTraceZeroH1Restriction σ hσ
          (rationalRealArithmeticRestriction a).toMonoidHom
          (rationalRealArithmeticRestriction a).continuous)

/-- Simultaneous original dual restriction includes the actual global twist at the real place. -/
def rationalArithmeticTraceDualAllPlacesLocalization :
    RationalArithmeticTraceDualH1 a q hqa σ hσ →ₗ[ZMod q]
      (RationalArithmeticExceptionalTraceDualH1 a q ha σ hσ ×
        rationalArithmeticRealTraceDualH1Module a q hqa σ hσ) :=
  (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ).prod
    (show RationalArithmeticTraceDualH1 a q hqa σ hσ →ₗ[ZMod q]
      rationalArithmeticRealTraceDualH1Module a q hqa σ hσ from
        continuousRepresentationH1Restriction
          (matrixTraceZeroCharacterRep σ
            (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
          (matrixTraceZeroCharacterAction_continuous σ hσ
            (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
            (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)
          (rationalRealArithmeticRestriction a).toMonoidHom
          (rationalRealArithmeticRestriction a).continuous)

/-- The proved all-place equivalence carries the original full localization to its finite-prime map. -/
theorem rationalArithmeticTraceAllPlacesEquiv_localization (hq2 : q ≠ 2)
    (x : ContinuousTraceZeroAdjointH1 σ hσ) :
    rationalArithmeticTraceAllPlacesEquiv a q σ hσ ha hq2
      (rationalArithmeticTraceAllPlacesLocalization a q σ hσ ha x) =
      rationalArithmeticTraceH1Localization a q ha σ hσ x := rfl

/-- The same original-object comparison holds for the globally twisted dual restriction. -/
theorem rationalArithmeticTraceDualAllPlacesEquiv_localization (hq2 : q ≠ 2)
    (x : RationalArithmeticTraceDualH1 a q hqa σ hσ) :
    rationalArithmeticTraceDualAllPlacesEquiv a q hqa σ hσ ha hq2
      (rationalArithmeticTraceDualAllPlacesLocalization a q hqa σ hσ ha x) =
      rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ x := rfl

end
end Dubon2026
