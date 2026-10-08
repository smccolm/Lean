import Dubon2026.FiniteAdelicScalar

/-! # The genuine trivial full adelic central character of the original classical cusp form -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix UpperHalfPlane CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

/-- Original scalar matrices in the canonical full adele ring have their literal real and finite scalar coordinates. -/
theorem rationalAdelicGL2RealFiniteEquiv_scalar (u : (AdeleRing ℤ ℚ)ˣ) :
    rationalAdelicGL2RealFiniteEquiv (GeneralLinearGroup.scalar (Fin 2) u) =
      (GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((RingHom.fst ℝ (FiniteAdeleRing ℤ ℚ)).comp
          rationalAdeleRealFiniteRingEquiv.toRingHom).toMonoidHom u),
      GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((RingHom.snd ℝ (FiniteAdeleRing ℤ ℚ)).comp
          rationalAdeleRealFiniteRingEquiv.toRingHom).toMonoidHom u)) := by
  apply Prod.ext
  · exact gl2Scalar_map
      ((RingHom.fst ℝ (FiniteAdeleRing ℤ ℚ)).comp rationalAdeleRealFiniteRingEquiv.toRingHom) u
  · exact gl2Scalar_map
      ((RingHom.snd ℝ (FiniteAdeleRing ℤ ℚ)).comp rationalAdeleRealFiniteRingEquiv.toRingHom) u

/-- The original classical cusp form defines a genuine full adelic cusp function with trivial character under every actual adelic scalar unit. -/
theorem canonicalAdelicGL2CuspLift_scalar_mul (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (u : (AdeleRing ℤ ℚ)ˣ)
    (g : GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) :
    canonicalAdelicGL2CuspLift N k f (GeneralLinearGroup.scalar (Fin 2) u * g) =
      canonicalAdelicGL2CuspLift N k f g := by
  let r : ℝˣ := Units.map ((RingHom.fst ℝ (FiniteAdeleRing ℤ ℚ)).comp
    rationalAdeleRealFiniteRingEquiv.toRingHom).toMonoidHom u
  have hr : GeneralLinearGroup.scalar (Fin 2) r = (realPositiveScalar r.val (Units.ne_zero r)).val := by
    apply congrArg (GeneralLinearGroup.scalar (Fin 2))
    apply Units.ext
    rfl
  unfold canonicalAdelicGL2CuspLift
  rw [map_mul, rationalAdelicGL2RealFiniteEquiv_scalar]
  simp only [Prod.fst_mul, Prod.snd_mul]
  rw [show GeneralLinearGroup.scalar (Fin 2)
      (Units.map ((RingHom.fst ℝ (FiniteAdeleRing ℤ ℚ)).comp
        rationalAdeleRealFiniteRingEquiv.toRingHom).toMonoidHom u) =
      (realPositiveScalar r.val (Units.ne_zero r)).val from hr,
    fullAdelicGL2CuspLift_real_scalar, fullAdelicGL2CuspLift_finite_scalar]

end
end Dubon2026
