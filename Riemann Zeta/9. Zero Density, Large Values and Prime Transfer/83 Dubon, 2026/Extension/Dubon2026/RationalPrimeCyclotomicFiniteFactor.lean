import Dubon2026.RationalPrimeCyclotomicInertia

/-! The actual cyclotomic character factors through any original finite
field restriction that contains a primitive root. Thus the same finite tame
presentation can be used for both the deformation and its fixed cyclotomic
quotient, as required by the local-ring chain for Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section

/-- A finite restriction fixing an embedded primitive root is killed by
the actual cyclotomic character on the original local Galois group. -/
theorem rationalPrimeCyclotomicCharacter_kernel_of_embedded_root
    (p : ℕ) (hp : p.Prime) (n : ℕ) [NeZero n]
    {F : Type} [Field F] [Algebra ℚ F]
    (e : F →+* rationalPrimeLocalClosure p hp)
    (r : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* Gal(F/ℚ))
    (he : ∀ g x, e (r g x) = g (e x))
    (ζ : F) (hζ : IsPrimitiveRoot (e ζ) n) :
    r.ker ≤ (rationalPrimeCyclotomicCharacter p hp n).toMonoidHom.ker := by
  intro g hg
  have hr : r g = 1 := hg
  have hfix : g (e ζ) = e ζ := by
    rw [← he, hr]
    rfl
  have hc := rationalPrimeCyclotomicCharacter_apply_root p hp n g hζ
  have hone := rationalPrimeCyclotomicCharacter_apply_root p hp n 1 hζ
  apply Units.ext
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  calc
    (e ζ) ^ (rationalPrimeCyclotomicCharacter p hp n g : ZMod n).val = e ζ := hc.symm.trans hfix
    _ = (e ζ) ^ ((1 : (ZMod n)ˣ) : ZMod n).val := by simpa only [map_one] using hone

end
end Dubon2026
