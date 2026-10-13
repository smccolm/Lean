import Dubon2026.OriginalKummerClassPairing

/-! # Nondegeneracy on the original radical classes and automorphisms

A radical fixed by every original automorphism is in the original base
field, so its original power class is trivial. In the other direction,
the original generating roots detect automorphisms. These two proved
injections permit finite duality to calculate the actual Kummer degree.
-/

namespace Dubon2026
noncomputable section
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

/-- The actual class pairing has trivial kernel: a fixed original radical is a base-field power. -/
theorem originalKummerClassPairing_injective [IsGalois K Ω]
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ) :
    Function.Injective (originalKummerClassPairing (Ω := Ω) n hn hζ Δ) := by
  let E := originalKummerRadicalField (Ω := Ω) n Δ
  letI := originalKummerRadicalField_isGalois (Ω := Ω) n Δ
  apply (injective_iff_map_eq_one _).mpr
  intro c hc
  let β : Eˣ := originalKummerClassRoot n hn Δ c
  have hf : ∀ g : Gal(E/K), g (β : E) = (β : E) := by
    intro g
    have he := DFunLike.congr_fun hc g
    change g • β / β = 1 at he
    exact congrArg Units.val (div_eq_one.mp he)
  obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β : E)).mpr hf
  have hb0 : b ≠ 0 := by
    intro h
    apply β.ne_zero
    rw [← hb, h, map_zero]
  let u : Kˣ := Units.mk0 b hb0
  have hu : Units.map (algebraMap K E).toMonoidHom u = β := Units.ext hb
  have hp : u ^ n = (originalKummerClassRepresentative n Δ c).val := by
    apply Units.map_injective (algebraMap K E).injective
    rw [map_pow, hu]
    exact originalKummerClassRoot_pow n hn Δ c
  apply Subtype.ext
  rw [← originalKummerClassRepresentative_spec n Δ c]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨u, hp⟩

/-- Transpose of the actual original class pairing; its values are homomorphisms on actual power classes. -/
def originalKummerTranspose (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ) :
    Gal(originalKummerRadicalField (Ω := Ω) n Δ/K) →*
      (originalKummerClassSubgroup n Δ →*
        (originalKummerRadicalField (Ω := Ω) n Δ)ˣ) where
  toFun g := {
    toFun c := originalKummerClassPairing n hn hζ Δ c g
    map_one' := by rw [map_one]; rfl
    map_mul' c d := by rw [map_mul]; rfl }
  map_one' := by
    apply MonoidHom.ext
    intro c
    exact map_one (originalKummerClassPairing n hn hζ Δ c)
  map_mul' g h := by
    apply MonoidHom.ext
    intro c
    exact map_mul (originalKummerClassPairing n hn hζ Δ c) g h

/-- The actual transpose detects automorphisms on the original generating roots. -/
theorem originalKummerTranspose_injective (n : ℕ) (hn : 0 < n)
    (hζ : (primitiveRoots n K).Nonempty) (Δ : Subgroup Kˣ) :
    Function.Injective (originalKummerTranspose (Ω := Ω) n hn hζ Δ) := by
  intro σ τ h
  apply originalKummerGaloisEvaluation_injective n hn hζ Δ
  funext c
  apply Subtype.ext
  exact DFunLike.congr_fun h c

end
end Dubon2026
