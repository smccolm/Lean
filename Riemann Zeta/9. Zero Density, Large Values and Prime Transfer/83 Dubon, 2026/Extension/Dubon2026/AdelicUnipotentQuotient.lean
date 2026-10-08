import Dubon2026.RationalAdelicAdditiveHaar
import Dubon2026.RationalGL2CuspPeriod

/-! # The original unipotent cusp function on the genuine additive rational adele quotient -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix.GeneralLinearGroup
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- Actual scalar-ring maps preserve the literal original upper unipotent matrix. -/
theorem gl2UpperRightHom_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : R) :
    Matrix.GeneralLinearGroup.map f (upperRightHom t) = upperRightHom (f t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperRightHom, Matrix.GeneralLinearGroup.map]

/-- The actual rational principal unipotent translations leave the original full adelic cusp function unchanged. -/
theorem canonicalAdelicGL2_unipotent_principal (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (g : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) (q : ℚ) (x : AdeleRing ℤ ℚ) :
    canonicalAdelicGL2CuspLift N k f
      (upperRightHom (algebraMap ℚ (AdeleRing ℤ ℚ) q + x) * g) =
      canonicalAdelicGL2CuspLift N k f (upperRightHom x * g) := by
  rw [AddChar.map_add_eq_mul, ← gl2UpperRightHom_map, mul_assoc]
  exact canonicalAdelicGL2CuspLift_rational_invariant N f (upperRightHom q) _

/-- Equality in the genuine principal-rational quotient gives equality of the original unipotent cusp values. -/
theorem canonicalAdelicGL2_unipotent_quotient_compatible (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (g : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ))
    (a b : AdeleRing ℤ ℚ)
    (hab : QuotientAddGroup.leftRel (AdeleRing.principalSubgroup ℤ ℚ) a b) :
    canonicalAdelicGL2CuspLift N k f (upperRightHom a * g) =
      canonicalAdelicGL2CuspLift N k f (upperRightHom b * g) := by
  have he : (QuotientAddGroup.mk a : RationalAdelicAdditiveQuotient) = QuotientAddGroup.mk b :=
    Quotient.sound hab
  obtain ⟨q, hq⟩ := QuotientAddGroup.eq_iff_sub_mem.mp he
  have ha : a = algebraMap ℚ (AdeleRing ℤ ℚ) q + b := by rw [hq]; abel
  rw [ha]
  exact canonicalAdelicGL2_unipotent_principal N f g q b

/-- The actual original unipotent cusp function descends to the canonical additive quotient by principal rationals. -/
def adelicUnipotentQuotientFunction (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (g : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) :
    RationalAdelicAdditiveQuotient → ℂ :=
  Quotient.lift (fun x => canonicalAdelicGL2CuspLift N k f (upperRightHom x * g))
    (canonicalAdelicGL2_unipotent_quotient_compatible N f g)

/-- Evaluation on the original quotient representative is precisely the original upper unipotent translate. -/
theorem adelicUnipotentQuotientFunction_mk (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (g : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) (x : AdeleRing ℤ ℚ) :
    adelicUnipotentQuotientFunction N f g (QuotientAddGroup.mk x) =
      canonicalAdelicGL2CuspLift N k f (upperRightHom x * g) := rfl

/-- The actual descended unipotent function is continuous on the genuine compact additive quotient. -/
theorem adelicUnipotentQuotientFunction_continuous (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (g : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) :
    Continuous (adelicUnipotentQuotientFunction N f g) :=
  ((canonicalAdelicGL2CuspLift_continuous N f).comp
    (continuous_upperRightHom.mul_const g)).quotient_lift _

/-- The genuine real unipotent matrix agrees with the original real special-linear embedding. -/
theorem realUpperRightHom_eq_toGL (t : ℝ) :
    upperRightHom t = toGL (realUpperUnipotent t) := by apply Units.ext; rfl

/-- Canonical group coordinates carry the original adelic upper unipotent to the two literal unipotents. -/
theorem rationalAdelicGL2RealFiniteEquiv_upperRightHom (x : AdeleRing ℤ ℚ) :
    rationalAdelicGL2RealFiniteEquiv (upperRightHom x) =
      (upperRightHom (rationalAdeleRealFiniteRingEquiv x).1,
        upperRightHom (rationalAdeleRealFiniteRingEquiv x).2) := by
  apply Prod.ext
  · exact gl2UpperRightHom_map
      ((RingHom.fst ℝ (FiniteAdeleRing ℤ ℚ)).comp rationalAdeleRealFiniteRingEquiv.toRingHom) x
  · exact gl2UpperRightHom_map
      ((RingHom.snd ℝ (FiniteAdeleRing ℤ ℚ)).comp rationalAdeleRealFiniteRingEquiv.toRingHom) x

/-- Restriction to the actual real additive line recovers the original positive-real unipotent orbit at every finite point. -/
theorem adelicUnipotentQuotientFunction_real (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : GL(2, ℝ)⁺)
    (a : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (t : ℝ) :
    adelicUnipotentQuotientFunction N f (rationalAdelicGL2RealFiniteEquiv.symm (g.val, a))
      (rationalAdelicRealQuotientMap t) =
      positiveAdelicGL2CuspLift N k f (toGLPos (realUpperUnipotent t) * g) a := by
  change canonicalAdelicGL2CuspLift N k f
    (upperRightHom (rationalAdeleRealEmbedding t) *
      rationalAdelicGL2RealFiniteEquiv.symm (g.val, a)) = _
  unfold canonicalAdelicGL2CuspLift
  rw [map_mul, rationalAdelicGL2RealFiniteEquiv_upperRightHom, MulEquiv.apply_symm_apply]
  simp only [rationalAdeleRealEmbedding, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    RingEquiv.apply_symm_apply, Prod.fst_mul, Prod.snd_mul,
    AddChar.map_zero_eq_one, one_mul, realUpperRightHom_eq_toGL]
  exact fullAdelicGL2CuspLift_positive N k f (toGLPos (realUpperUnipotent t) * g) a

end
end Dubon2026
