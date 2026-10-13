import Dubon2026.OriginalKummerClassRepresentatives

/-! # Finite original power classes detect the original radical Galois group

Evaluation uses actual roots in the constructed field. The proved equality
of ratios for equal original power classes removes representative choices.
Finite power classes therefore force the original Galois group and Galois
extension to be finite, as needed for global S-unit Kummer preparation.
-/

namespace Dubon2026
noncomputable section
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

/-- Evaluate an original automorphism on the actual radical representing each original power class. -/
def originalKummerGaloisEvaluation (n : ℕ) (hn : 0 < n) (Δ : Subgroup Kˣ) :
    Gal(originalKummerRadicalField (Ω := Ω) n Δ/K) →
      (originalKummerClassSubgroup n Δ → rootsOfUnity n (originalKummerRadicalField (Ω := Ω) n Δ)) :=
  fun σ c => ⟨σ • originalKummerClassRoot n hn Δ c / originalKummerClassRoot n hn Δ c,
    galoisRadicalRatio_pow_eq_one n (originalKummerClassRepresentative n Δ c).val
      (originalKummerClassRoot n hn Δ c) (originalKummerClassRoot_pow n hn Δ c) σ⟩

/-- Equal original radical evaluations imply equal automorphisms on every actual generating root. -/
theorem originalKummerGaloisEvaluation_injective (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ) :
    Function.Injective (originalKummerGaloisEvaluation (Ω := Ω) n hn Δ) := by
  letI : NeZero n := ⟨hn.ne'⟩
  intro σ τ h
  apply AlgEquiv.coe_algHom_injective
  apply IntermediateField.adjoin_algHom_ext K
  intro β hβ
  let b : originalKummerRootSet (Ω := Ω) n Δ := ⟨β, hβ⟩
  let a := b.property.choose
  let u := originalKummerRootUnit n Δ b
  let c : originalKummerClassSubgroup n Δ :=
    ⟨QuotientGroup.mk' _ a.val, a.val, a.property, rfl⟩
  have hc : QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range
      (originalKummerClassRepresentative n Δ c).val = QuotientGroup.mk' _ a.val :=
    originalKummerClassRepresentative_spec n Δ c
  have he (g : Gal(originalKummerRadicalField (Ω := Ω) n Δ/K)) :
      g • originalKummerClassRoot n hn Δ c / originalKummerClassRoot n hn Δ c =
        g • u / u :=
    galois_radical_ratios_eq_of_power_class n hζ
      (originalKummerClassRepresentative n Δ c).val a.val
      (originalKummerClassRoot n hn Δ c) u
      (originalKummerClassRoot_pow n hn Δ c) (originalKummerRootUnit_pow n Δ b) hc g
  have hv := congrArg Subtype.val (congrFun h c)
  have hu : σ • u / u = τ • u / u := (he σ).symm.trans (hv.trans (he τ))
  exact congrArg Units.val (div_left_inj.mp hu)

/-- Finitely many actual original power classes give a finite original radical Galois group. -/
theorem originalKummerRadicalField_galois_finite (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    [Finite (originalKummerClassSubgroup n Δ)] :
    Finite Gal(originalKummerRadicalField (Ω := Ω) n Δ/K) := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact Finite.of_injective _ (originalKummerGaloisEvaluation_injective n hn hζ Δ)

/-- The actual Galois radical field is finite over the original base, with its finiteness
derived from actual power classes rather than supplied as a field-stage hypothesis. -/
theorem originalKummerRadicalField_finiteDimensional [IsGalois K Ω]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ)
    [Finite (originalKummerClassSubgroup n Δ)] :
    FiniteDimensional K (originalKummerRadicalField (Ω := Ω) n Δ) := by
  letI := originalKummerRadicalField_isGalois (Ω := Ω) n Δ
  letI := originalKummerRadicalField_galois_finite (Ω := Ω) n hn hζ Δ
  exact IsGalois.finiteDimensional_of_finite K _

end
end Dubon2026
