import Dubon2026.FiniteAdelicSL2Continuity
import Dubon2026.RationalAdeleRealFinite

/-! # The original cusp function on Mathlib's canonical full adelic special linear group -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- The canonical principal rational matrices have exactly the original real and finite coordinates. -/
theorem rationalAdelicSL2RealFiniteEquiv_diagonal (γ : SL(2, ℚ)) :
    rationalAdelicSL2RealFiniteEquiv
      (Matrix.SpecialLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ) =
        (rationalSL2ToReal γ, rationalSL2ToFinite γ) := by
  apply Prod.ext
  · apply Subtype.ext
    funext i j
    exact congrArg Prod.fst (rationalAdeleRealFiniteRingEquiv_algebraMap (γ i j))
  · apply Subtype.ext
    funext i j
    exact congrArg Prod.snd (rationalAdeleRealFiniteRingEquiv_algebraMap (γ i j))

/-- The original cusp function defined on the actual pinned full adelic determinant-one group. -/
def canonicalAdelicCuspLift (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (g : SL(2, AdeleRing ℤ ℚ)) : ℂ :=
  finiteAdelicSL2CuspLift N k f
    (rationalAdelicSL2RealFiniteEquiv g).1 (rationalAdelicSL2RealFiniteEquiv g).2

/-- The full-adele function agrees exactly with the proved real and finite construction. -/
theorem canonicalAdelicCuspLift_coordinates (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (g : SL(2, ℝ)) (x : SL(2, FiniteAdeleRing ℤ ℚ)) :
    canonicalAdelicCuspLift N k f (rationalAdelicSL2RealFiniteEquiv.symm (g, x)) =
      finiteAdelicSL2CuspLift N k f g x := by
  simp only [canonicalAdelicCuspLift, MulEquiv.apply_symm_apply]

/-- The literal original function is continuous on the canonical full adelic group. -/
theorem canonicalAdelicCuspLift_continuous (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Continuous (canonicalAdelicCuspLift N k f) :=
  (finiteAdelicSL2CuspLift_continuous N f).comp rationalAdelicSL2RealFiniteEquiv_continuous

/-- The original full-adele function is invariant under the actual principal rational group. -/
theorem canonicalAdelicCuspLift_rational_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (γ : SL(2, ℚ)) (g : SL(2, AdeleRing ℤ ℚ)) :
    canonicalAdelicCuspLift N k f
      (Matrix.SpecialLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ * g) =
        canonicalAdelicCuspLift N k f g := by
  unfold canonicalAdelicCuspLift
  rw [map_mul, rationalAdelicSL2RealFiniteEquiv_diagonal]
  exact finiteAdelicSL2CuspLift_rational_invariant N f γ _ _

/-- The archimedean restriction recovers the whole original real-group cusp function. -/
theorem canonicalAdelicCuspLift_real_restriction (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : SL(2, ℝ)) :
    canonicalAdelicCuspLift N k f (rationalAdelicSL2RealFiniteEquiv.symm (g, 1)) =
      realWeightLift k f g := by
  rw [canonicalAdelicCuspLift_coordinates, finiteAdelicSL2CuspLift_one]

/-- The full-adele construction is right invariant under the genuine finite level subgroup. -/
theorem canonicalAdelicCuspLift_level_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (g : SL(2, AdeleRing ℤ ℚ)) (u : finiteAdeleGamma0 N) :
    canonicalAdelicCuspLift N k f (g * rationalAdelicSL2RealFiniteEquiv.symm (1, u.val)) =
      canonicalAdelicCuspLift N k f g := by
  unfold canonicalAdelicCuspLift
  rw [map_mul, MulEquiv.apply_symm_apply]
  simpa only [Prod.fst_mul, Prod.snd_mul, mul_one] using
    finiteAdelicSL2CuspLift_level_invariant N f
      (rationalAdelicSL2RealFiniteEquiv g).1 (rationalAdelicSL2RealFiniteEquiv g).2 u

/-- The actual canonical adelic lift retains the original classical cusp form injectively. -/
theorem canonicalAdelicCuspLift_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (fun f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k =>
      canonicalAdelicCuspLift N k f) := by
  intro f h he
  apply finiteAdelicSL2CuspLift_injective N k
  funext g x
  have ht := congrFun he (rationalAdelicSL2RealFiniteEquiv.symm (g, x))
  simpa only [canonicalAdelicCuspLift_coordinates] using ht

end
end Dubon2026
