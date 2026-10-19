import Dubon2026.PolarizedLocalCoefficientQuotient
import Dubon2026.PolarizedQuotientRepresentation

/-! Construct the original polarized representation over the source
equation quotient using its proved residual-compatible locality. This
isolates the coefficient proof used by the native framed-ring consumer
for DUB-17 without extra hypotheses on the quotient. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {G O R ι : Type*} [Group G] [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
  (τ : G →* GeneralLinearGroup (ι ⊕ ι) R)
  (σ : G →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (hτ : ∀ g, GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom (τ g) =
    polarizedBlockRepresentation (σ g))
  (ν : G →* Oˣ)
  (hν : ∀ g, polarizedSimilitude (σ g) =
    Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g))

/-- Residual-compatible original coefficients construct the polarized representation over their quotient. -/
def representationPolarizedLocalCoefficientRepresentation :
    G →* PolarizedGaloisGroup ι (R ⧸ representationPolarizedIdeal τ
      ((polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)).comp σ)
      ((Units.map (algebraMap O R).toMonoidHom).comp ν)) := by
  let r := @representationPolarizedQuotientRepresentation G R ι _ _ _ _ _ τ
    ((polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)).comp σ)
    ((Units.map (algebraMap O R).toMonoidHom).comp ν)
    (@IsLocalRing.toNontrivial _ _
      (representationPolarizedQuotient_isLocal_of_residue eR τ σ hτ ν hν))
  exact { toFun := fun g => r g, map_one' := r.map_one, map_mul' := r.map_mul }

/-- The local coefficient construction preserves the original matrix reduction. -/
theorem representationPolarizedLocalCoefficientRepresentation_block (g : G) :
    polarizedBlockRepresentation
        (representationPolarizedLocalCoefficientRepresentation eR τ σ hτ ν hν g) =
      GeneralLinearGroup.map (Ideal.Quotient.mk _) (τ g) := by
  letI : Nontrivial (R ⧸ representationPolarizedIdeal τ (polarizedComponent.comp σ)
      ((Units.map (algebraMap O R).toMonoidHom).comp ν)) :=
    @IsLocalRing.toNontrivial _ _
      (representationPolarizedQuotient_isLocal_of_residue eR τ σ hτ ν hν)
  exact representationPolarizedQuotientRepresentation_block _ _ _ g

/-- The local coefficient construction retains the original component and base similitude. -/
theorem representationPolarizedLocalCoefficientRepresentation_characters (g : G) :
    polarizedComponent
        (representationPolarizedLocalCoefficientRepresentation eR τ σ hτ ν hν g) =
        polarizedComponent (σ g) ∧
      polarizedSimilitude
        (representationPolarizedLocalCoefficientRepresentation eR τ σ hτ ν hν g) =
        Units.map (algebraMap O (R ⧸ representationPolarizedIdeal τ (polarizedComponent.comp σ)
          ((Units.map (algebraMap O R)).comp ν))).toMonoidHom (ν g) := by
  letI : Nontrivial (R ⧸ representationPolarizedIdeal τ (polarizedComponent.comp σ)
      ((Units.map (algebraMap O R).toMonoidHom).comp ν)) :=
    @IsLocalRing.toNontrivial _ _
      (representationPolarizedQuotient_isLocal_of_residue eR τ σ hτ ν hν)
  exact representationPolarizedQuotientRepresentation_characters _ _ _ g

end
end Dubon2026
