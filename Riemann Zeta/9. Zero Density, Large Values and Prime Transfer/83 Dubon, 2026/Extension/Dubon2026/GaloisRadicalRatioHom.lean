import Dubon2026.GaloisCharacterKummerInjectivity

/-! # Actual radical ratios are Galois characters

When the original base contains the nth roots of unity, every Galois ratio
of an actual radical is fixed. This supplies the original character maps
used to prove abelianity and exponent bounds for the constructed global
S-unit Kummer extension in the DUB-17 norm-index route.
-/

namespace Dubon2026
noncomputable section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The actual Galois ratio of a root of an original base unit has nth power one. -/
theorem galoisRadicalRatio_pow_eq_one (n : ℕ) (a : Kˣ) (β : Lˣ)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) (g : Gal(L/K)) :
    (g • β / β) ^ n = 1 := by
  rw [div_pow, ← smul_pow', hβ, galois_base_unit_fixed, div_self']

/-- The original Galois ratio is a genuine character when the original base contains the roots of unity. -/
def galoisRadicalRatioHom (n : ℕ) [NeZero n]
    (hζ : (primitiveRoots n K).Nonempty) (a : Kˣ) (β : Lˣ)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) : Gal(L/K) →* Lˣ where
  toFun g := g • β / β
  map_one' := by rw [one_smul, div_self']
  map_mul' g h := by
    have hf := galois_rootOfUnity_fixed n hζ (h • β / β)
      (galoisRadicalRatio_pow_eq_one n a β hβ h) g
    rw [smul_div'] at hf
    change (g * h) • β / β = (g • β / β) * (h • β / β)
    rw [mul_smul]
    calc
      g • (h • β) / β = (g • (h • β) / (g • β)) * (g • β / β) := by
        simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
      _ = _ := by rw [hf, mul_comm]

/-- An automorphism raised to the original exponent fixes the actual radical. -/
theorem galoisRadicalRatio_pow_fixes (n : ℕ) [NeZero n]
    (hζ : (primitiveRoots n K).Nonempty) (a : Kˣ) (β : Lˣ)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) (g : Gal(L/K)) :
    (g ^ n) • β = β := by
  have h := map_pow (galoisRadicalRatioHom n hζ a β hβ) g n
  change (g ^ n) • β / β = (g • β / β) ^ n at h
  rw [galoisRadicalRatio_pow_eq_one n a β hβ g] at h
  exact div_eq_one.mp h

end
end Dubon2026
