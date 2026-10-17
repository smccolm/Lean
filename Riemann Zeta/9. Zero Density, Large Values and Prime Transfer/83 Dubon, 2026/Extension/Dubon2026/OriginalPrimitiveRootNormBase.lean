import Dubon2026.OriginalCyclotomicNormDegreeStage

/-! # Construct the primitive-root base needed by arithmetic norm roots

The relation-extension step may enlarge the original finite stage before
choosing its normal subgroup. Adjoin an actual primitive root of the
coefficient prime and take the finite Galois compositum with that stage.
The existing unramified-root theorem keeps the original exceptional
integer. This discharges the primitive-root input on DUB-17's enlarged
stage chain, without adding a stronger degree condition.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
variable (Ω : Type) [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]

/-- Above any original arithmetic stage there is an actual arithmetic
stage containing a constructed primitive root of an exceptional prime. -/
theorem originalUnramifiedStage_exists_primitive_root_base
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a) :
    ∃ E : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      P.val.toIntermediateField ≤ E.val.toIntermediateField ∧
      ∃ ζ : E.val, IsPrimitiveRoot ζ p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  let R := originalPrimitiveRootStage ℚ Ω hζ
  have hR : R.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a := by
    change IntermediateField.adjoin ℚ ({ζ} : Set Ω) ≤ _
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact originalQUnramifiedUnion_mem_of_powerRoot a p 1 hpa ζ (by simpa using hζ)
  have hr := originalUnramifiedUnion_ambient_finite_ramification a ha R.toIntermediateField hR
  let E : OriginalUnramifiedGaloisStage (Ω := Ω) a :=
    ⟨R ⊔ P.val, finiteGalois_sup_unramified a ha R P.val hr P.property⟩
  letI : Algebra ℚ E.val := E.val.algebra'
  have hRE : R.toIntermediateField ≤ E.val.toIntermediateField := le_sup_left
  let z : E.val := ⟨ζ, hRE (IntermediateField.mem_adjoin_simple_self ℚ ζ)⟩
  refine ⟨E, le_sup_right, z, ?_⟩
  exact hζ.of_map_of_injective (f := E.val.toIntermediateField.val)
    E.val.toIntermediateField.val.injective

end
end Dubon2026
