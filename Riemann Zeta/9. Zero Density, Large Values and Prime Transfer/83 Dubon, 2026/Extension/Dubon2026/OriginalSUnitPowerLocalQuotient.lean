import Dubon2026.OriginalSupportedPowerQuotient
import Dubon2026.NumberFieldSupportedIdeleExact

/-! # The original principal S-unit term in the local-power quotient

The kernel of the actual principal map modulo original local powers is
the explicitly specified local-power condition on the original S-units.
The induced map of quotients is injective. This supplies the left term
of DUB-17's supported-idele/class cardinal exact sequence; the Kummer
selected-prime calculation of its size remains a separate obligation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K : Type) [Field K] [NumberField K]
  (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))

/-- The actual local-power condition on the original S-union-T units, pulled back along their original principal map. -/
def originalSUnitPowerLocalSubgroup :
    Subgroup ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
  (originalSupportedPowerLocalUnitSubgroup K n S T).comap
    (numberFieldSupportedPrincipalIdele K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))))

/-- The original principal S-unit quotient appearing in the actual local-power index calculation. -/
abbrev OriginalSUnitPowerLocalQuotient :=
  ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K) ⧸ originalSUnitPowerLocalSubgroup K n S T

/-- For an actual supported S-unit, the principal local-power condition retains exactly all infinite and S-finite power conditions. -/
theorem originalSUnitPowerLocalSubgroup_mem_iff
    (x : (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    x ∈ originalSUnitPowerLocalSubgroup K n S T ↔
      (∀ w : InfinitePlace K,
        numberFieldIdeleInfiniteComponent K w (numberFieldPrincipalIdele K x.val) ∈ (powMonoidHom n).range) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∈ S →
        numberFieldIdeleFiniteComponent K v (numberFieldPrincipalIdele K x.val) ∈ (powMonoidHom n).range := by
  change numberFieldPrincipalIdele K x.val ∈ originalIdelePowerLocalUnitSubgroup K n S T ↔ _
  rw [originalIdelePowerLocalUnitSubgroup_mem_iff]
  constructor
  · rintro ⟨hInf, hS, _⟩
    exact ⟨hInf, hS⟩
  · rintro ⟨hInf, hS⟩
    refine ⟨hInf, hS, ?_⟩
    have h := (numberFieldSupportedPrincipalIdele K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) x).property
    simpa only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap] using h

/-- The original principal S-unit map descends to the actual supported local-power quotient. -/
def originalSUnitPowerLocalQuotientMap :
    OriginalSUnitPowerLocalQuotient K n S T →* OriginalSupportedPowerLocalUnitQuotient K n S T :=
  QuotientGroup.map _ _
    (numberFieldSupportedPrincipalIdele K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))) le_rfl

/-- The induced map retains the actual original principal supported idele of every original S-unit. -/
theorem originalSUnitPowerLocalQuotientMap_mk
    (x : (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    originalSUnitPowerLocalQuotientMap K n S T (QuotientGroup.mk' (originalSUnitPowerLocalSubgroup K n S T) x) =
      QuotientGroup.mk' (originalSupportedPowerLocalUnitSubgroup K n S T)
        (numberFieldSupportedPrincipalIdele K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) x) := rfl

/-- The actual original principal S-unit quotient embeds in the actual supported local-power quotient. -/
theorem originalSUnitPowerLocalQuotientMap_injective :
    Function.Injective (originalSUnitPowerLocalQuotientMap K n S T) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  change (QuotientGroup.map _ _
    (numberFieldSupportedPrincipalIdele K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))) le_rfl).ker = ⊥
  rw [QuotientGroup.ker_map]
  exact QuotientGroup.map_mk'_self _

end
end Dubon2026
