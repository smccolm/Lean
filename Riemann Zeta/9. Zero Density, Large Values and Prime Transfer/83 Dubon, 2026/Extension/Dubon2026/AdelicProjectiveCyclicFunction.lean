import Dubon2026.AdelicProjectiveFunction
import Dubon2026.AdelicCyclicFiniteSmooth

/-! # Faithful projective coordinates for the original algebraic adelic cusp representation -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix Matrix.SpecialLinearGroup
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- The original positive real matrix is exactly its determinant-root scalar times its genuine special-linear normalization. -/
theorem realPositiveScalar_mul_normalize (g : GL(2, ℝ)⁺) :
    GeneralLinearGroup.scalar (Fin 2)
        (Units.mk0 (realPositiveDetRoot g) (realPositiveDetRoot_pos g).ne') *
        toGL (realPositiveNormalize g) = g.val := by
  apply Units.ext
  change Matrix.scalar (Fin 2) (realPositiveDetRoot g) * (realPositiveNormalize g).val = g.val.val
  rw [realPositiveNormalize_val, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
    smul_smul, mul_inv_cancel₀ (realPositiveDetRoot_pos g).ne', one_smul]

/-- The original algebraic cyclic vector has an actual projective-coordinate function, using its proved scalar invariance. -/
def adelicCyclicProjectiveFunction (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) : AdelicProjectiveGroup → ℂ :=
  adelicProjectiveFunction v.val (adelicLiftCyclic_scalar_invariant N f v.property)

/-- The actual original cyclic projective function has exactly the original full adelic values on representatives. -/
theorem adelicCyclicProjectiveFunction_mk (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (r : SL(2, ℝ)) (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicCyclicProjectiveFunction N f v (QuotientGroup.mk r, ProjGenLinGroup.mk a) =
      v.val (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, a)) := rfl

/-- The actual original cyclic projective function is continuous by the already proved full adelic continuity. -/
theorem adelicCyclicProjectiveFunction_continuous (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    Continuous (adelicCyclicProjectiveFunction N f v) :=
  adelicProjectiveFunction_continuous v.val (adelicLiftCyclic_scalar_invariant N f v.property)
    (adelicLiftCyclic_continuous N f v.property)

/-- Original projective coordinates recover every positive-real full adelic value without a choice of scalar normalization premise. -/
theorem adelicCyclicProjectiveFunction_recover_positive (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (r : GL(2, ℝ)⁺) (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicCyclicProjectiveFunction N f v
      (QuotientGroup.mk (realPositiveNormalize r), ProjGenLinGroup.mk a) =
      v.val (rationalAdelicGL2RealFiniteEquiv.symm (r.val, a)) := by
  rw [adelicCyclicProjectiveFunction_mk]
  have h := adelicFunction_scalar_pair v.val (adelicLiftCyclic_scalar_invariant N f v.property)
    (Units.mk0 (realPositiveDetRoot r) (realPositiveDetRoot_pos r).ne')
    (1 : (FiniteAdeleRing ℤ ℚ)ˣ) (toGL (realPositiveNormalize r)) a
  rw [realPositiveScalar_mul_normalize, map_one, one_mul] at h
  exact h.symm

/-- The original projective-coordinate construction retains every original algebraic adelic cyclic vector injectively, including negative real values by proved rational reflection invariance. -/
theorem adelicCyclicProjectiveFunction_injective (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Function.Injective (adelicCyclicProjectiveFunction N f) := by
  intro v w he
  have hpos (b : RationalAdelicGL2)
      (hb : 0 < (GeneralLinearGroup.det (rationalAdelicGL2RealFiniteEquiv b).1).val) : v.val b = w.val b := by
    let r : GL(2, ℝ)⁺ := ⟨(rationalAdelicGL2RealFiniteEquiv b).1, hb⟩
    have h := congrFun he
      (QuotientGroup.mk (realPositiveNormalize r), ProjGenLinGroup.mk (rationalAdelicGL2RealFiniteEquiv b).2)
    rw [adelicCyclicProjectiveFunction_recover_positive,
      adelicCyclicProjectiveFunction_recover_positive] at h
    simpa only [r, Prod.mk.eta, MulEquiv.symm_apply_apply] using h
  apply Subtype.ext
  funext g
  by_cases hp : 0 < (GeneralLinearGroup.det (rationalAdelicGL2RealFiniteEquiv g).1).val
  · exact hpos g hp
  · let b := GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) rationalGL2Reflection * g
    have hb : 0 < (GeneralLinearGroup.det (rationalAdelicGL2RealFiniteEquiv b).1).val := by
      dsimp only [b]
      rw [map_mul, rationalAdelicGL2RealFiniteEquiv_rational]
      change 0 < (GeneralLinearGroup.det
        (rationalGL2ToReal rationalGL2Reflection * (rationalAdelicGL2RealFiniteEquiv g).1)).val
      rw [map_mul, Units.val_mul, rationalGL2Reflection_real_det, neg_one_mul]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp)
        (Units.ne_zero (GeneralLinearGroup.det (rationalAdelicGL2RealFiniteEquiv g).1)))
    calc
      v.val g = v.val b := (adelicLiftCyclic_rational_invariant N f v.property rationalGL2Reflection g).symm
      _ = w.val b := hpos b hb
      _ = w.val g := adelicLiftCyclic_rational_invariant N f w.property rationalGL2Reflection g

/-- The actual original cyclic vectors map linearly to their genuine continuous projective-coordinate functions. -/
def adelicCyclicProjectiveLinear (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (adelicLiftCyclicRepresentation N k f).toSubmodule →ₗ[ℂ] C(AdelicProjectiveGroup, ℂ) where
  toFun v := ⟨adelicCyclicProjectiveFunction N f v, adelicCyclicProjectiveFunction_continuous N f v⟩
  map_add' v w := by
    ext p
    obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective p.1
    obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_surjective p.2
    have hp : p = (QuotientGroup.mk r, ProjGenLinGroup.mk a) := Prod.ext hr.symm ha.symm
    rw [hp]
    rfl
  map_smul' c v := by
    ext p
    obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective p.1
    obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_surjective p.2
    have hp : p = (QuotientGroup.mk r, ProjGenLinGroup.mk a) := Prod.ext hr.symm ha.symm
    rw [hp]
    rfl

/-- The actual linear projective-coordinate map is injective on the original algebraic adelic cusp representation. -/
theorem adelicCyclicProjectiveLinear_injective (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    Function.Injective (adelicCyclicProjectiveLinear N f) := by
  intro v w he
  apply adelicCyclicProjectiveFunction_injective N f
  exact congrArg (fun F : C(AdelicProjectiveGroup, ℂ) => (F : AdelicProjectiveGroup → ℂ)) he

/-- The original classical cusp function as a vector of its actual algebraic adelic cyclic representation. -/
def adelicCyclicGenerator (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (adelicLiftCyclicRepresentation N k f).toSubmodule :=
  ⟨canonicalAdelicGL2CuspLift N k f, canonicalAdelicGL2CuspLift_mem_cyclic N k f⟩

/-- The actual original generator in projective coordinates recovers exactly the original real cusp lift at finite identity. -/
theorem adelicCyclicProjectiveGenerator_real (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (r : SL(2, ℝ)) :
    adelicCyclicProjectiveLinear N f (adelicCyclicGenerator N f) (QuotientGroup.mk r, 1) =
      realWeightLift k f r := by
  have h := canonicalAdelicGL2CuspLift_real_restriction N f (toGLPos r)
  rw [realPositiveUnitaryLift_toGLPos] at h
  change adelicCyclicProjectiveFunction N f (adelicCyclicGenerator N f) (QuotientGroup.mk r, 1) = _
  rw [← map_one (ProjGenLinGroup.mk :
    GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) →* RationalFiniteProjectiveGL2),
    adelicCyclicProjectiveFunction_mk]
  exact h

end
end Dubon2026
