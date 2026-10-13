import Dubon2026.OriginalSUnitLocalPowerMap

/-! # Actual principal correction at the selected local quotients

Surjectivity of the proved S-unit local-power map supplies a single original
S-unit correcting an arbitrary original supported idele at every selected
prime. The corrected idele stays supported on the same S. This is the
literal correction needed to prove class norm surjectivity for the simple
Kummer extension in DUB-17's principal S-union-T localization argument.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K : Type) [Field K] [NumberField K]

/-- The original selected local-power map corrects every original supported
idele by one original S-unit, retaining support and all local power conditions. -/
theorem originalSupportedIdele_sUnit_power_correction
    (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hSurj : Function.Surjective (originalSUnitLocalPowerMap K n S T hST))
    (u : numberFieldSupportedIdeles K S) :
    ∃ x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      ∀ v : T, numberFieldIdeleFiniteComponent K v.val
        (u.val / numberFieldPrincipalIdele K x.val) ∈
          (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range := by
  let uLocal (v : T) : (v.val.adicCompletionIntegers K)ˣ :=
    (numberFieldSupportedFiniteFactorEquiv K S
      (numberFieldSupportedIdeleCoordinateEquiv K S u).2).2
        ⟨v.val, fun h => Finset.disjoint_left.mp hST h v.property⟩
  let target (v : T) : (v.val.adicCompletionIntegers K)ˣ ⧸ (powMonoidHom n).range :=
    QuotientGroup.mk' _ (uLocal v)
  obtain ⟨x, hx⟩ := hSurj target
  refine ⟨x, ?_⟩
  intro v
  let sx := originalSUnitLocalIntegerMap K S v.val
    (fun h => Finset.disjoint_left.mp hST h v.property) x
  have hq : QuotientGroup.mk' (powMonoidHom (α := (v.val.adicCompletionIntegers K)ˣ) n).range sx =
      QuotientGroup.mk' _ (uLocal v) := congrFun hx v
  have hdiv : uLocal v / sx ∈ (powMonoidHom (α := (v.val.adicCompletionIntegers K)ˣ) n).range := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' _ (uLocal v / sx) = 1
    rw [map_div, ← hq, div_self']
  obtain ⟨b, hb⟩ := hdiv
  change b ^ n = uLocal v / sx at hb
  refine ⟨Units.map (v.val.adicCompletionIntegers K).subtype.toMonoidHom b, ?_⟩
  change (Units.map (v.val.adicCompletionIntegers K).subtype.toMonoidHom b) ^ n = _
  rw [← map_pow]
  change Units.map (v.val.adicCompletionIntegers K).subtype.toMonoidHom (b ^ n) = _
  rw [hb, map_div, map_div]
  rfl

end
end Dubon2026
