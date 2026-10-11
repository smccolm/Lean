import Dubon2026.MatrixAdicHopfFlatCondition
import Dubon2026.FiniteCoefficientExtensionHopfModel
import Dubon2026.AdicCoefficientQuotientMaps
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! # Actual local coefficient changes preserve the full adic model condition -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

/-- The original local coefficient map induces the genuine map at each actual maximal-ideal-power quotient. This reuses the existing ideal-compatible adic quotient construction. -/
def localCoefficientAdicQuotientRingMap (f : A →+* B) [IsLocalHom f] (n : ℕ) :
    (A ⧸ IsLocalRing.maximalIdeal A ^ n) →+* (B ⧸ IsLocalRing.maximalIdeal B ^ n) :=
  (adicCoefficientQuotientMap (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
    f.toIntAlgHom (by
      change IsLocalRing.maximalIdeal A ≤ Ideal.comap f (IsLocalRing.maximalIdeal B)
      rw [IsLocalRing.maximalIdeal_comap]) n).toRingHom

/-- Original quotient classes retain precisely the original local coefficient values. -/
theorem localCoefficientAdicQuotientRingMap_mk (f : A →+* B) [IsLocalHom f]
    (n : ℕ) (a : A) :
    localCoefficientAdicQuotientRingMap f n
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n) a) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal B ^ n) (f a) := by
  rfl

variable {G ι : Type u} [Group G] [Fintype ι] [DecidableEq ι]

/-- Changing the original coefficients and reducing at the actual nth maximal-adic level commute on the entire original matrix representation. -/
theorem matrixIdealQuotientRepresentation_localCoefficient (f : A →+* B) [IsLocalHom f]
    (ρ : G →* GeneralLinearGroup ι A) (n : ℕ) :
    (GeneralLinearGroup.map (localCoefficientAdicQuotientRingMap f n)).comp
      (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A ^ n) ρ) =
    matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal B ^ n)
      ((GeneralLinearGroup.map f).comp ρ) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  ext i j
  rfl

variable {R F K : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [IsNoetherianRing B] [Finite (IsLocalRing.ResidueField B)]

/-- Every genuine local coefficient map preserves the complete all-positive-level condition. The target quotients are proved finite from their original Noetherian maximal ideal and finite residue field, and each model is constructed using the actual finite coefficient-extension map. -/
theorem matrixAdicHopfFlat_coefficientChange (f : A →+* B) [IsLocalHom f]
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (hρ : MatrixAdicHopfFlat R F K ρ) :
    MatrixAdicHopfFlat R F K ((GeneralLinearGroup.map f).comp ρ) := by
  intro n hn
  obtain ⟨m⟩ := hρ n hn
  letI : Finite (B ⧸ IsLocalRing.maximalIdeal B) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField B))
  letI : Finite (B ⧸ IsLocalRing.maximalIdeal B ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal B)) n
  letI : Fintype (B ⧸ IsLocalRing.maximalIdeal B ^ n) := Fintype.ofFinite _
  have h := finiteCoefficientExtensionHopfModel_exists (localCoefficientAdicQuotientRingMap f n)
    (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A ^ n) ρ) m
  rw [matrixIdealQuotientRepresentation_localCoefficient] at h
  exact h

end
end Dubon2026
