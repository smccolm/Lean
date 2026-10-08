import Dubon2026.AdelicProjectiveCyclicFunction

/-! # The actual rational and integral arithmetic homomorphisms in projective adelic coordinates -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix Matrix.SpecialLinearGroup
open UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm

/-- The actual positive rational group maps diagonally to the genuine real and finite projective coordinates. -/
def rationalPositiveToAdelicProjective : GL(2, ℚ)⁺ →* AdelicProjectiveGroup :=
  (((QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp realPositiveNormalize).comp
    rationalPositiveGL2ToReal).prod (ProjGenLinGroup.mk.comp rationalPositiveGL2ToFinite)

/-- The genuine rational arithmetic subgroup is the actual image of original positive rational invertible matrices. -/
def adelicProjectiveArithmetic : Subgroup AdelicProjectiveGroup :=
  rationalPositiveToAdelicProjective.range

/-- Original positive rational matrices form a countable type by their literal rational entries. -/
instance rationalPositiveGL2Countable : Countable GL(2, ℚ)⁺ :=
  (show Function.Injective (fun r : GL(2, ℚ)⁺ => fun i j : Fin 2 => r.val.val i j) from
    fun _ _ h => Subtype.ext (Units.ext h)).countable

/-- The actual rational projective arithmetic subgroup is countable. -/
instance adelicProjectiveArithmeticCountable : Countable adelicProjectiveArithmetic :=
  (Set.countable_range rationalPositiveToAdelicProjective).to_subtype

/-- The actual integral special-linear group maps to the original finite projective group. -/
def integralSL2ToFiniteProjective : SL(2, ℤ) →* RationalFiniteProjectiveGL2 :=
  ProjGenLinGroup.mk.comp ((GeneralLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ))).comp toGL)

/-- The genuine integral negative identity becomes the identity in the original finite projective group. -/
theorem integralSL2ToFiniteProjective_neg_one : integralSL2ToFiniteProjective (-1) = 1 := by
  have he : GeneralLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ))
      (toGL (-1 : SL(2, ℤ))) = GeneralLinearGroup.scalar (Fin 2) (-1 : (FiniteAdeleRing ℤ ℚ)ˣ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GeneralLinearGroup.map, GeneralLinearGroup.scalar, Matrix.scalar, toGL, coe_neg]
  change ProjGenLinGroup.mk (GeneralLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ))
    (toGL (-1 : SL(2, ℤ)))) = 1
  rw [he, ProjGenLinGroup.mk_scalar]

/-- The actual integral projective group maps to its genuine finite projective matrices. -/
def integralToFiniteProjective : PSL(2, ℤ) →* RationalFiniteProjectiveGL2 :=
  QuotientGroup.lift (Subgroup.center SL(2, ℤ)) integralSL2ToFiniteProjective (by
    intro σ hσ
    change integralSL2ToFiniteProjective σ = 1
    rcases SL2_center_eq_one_or_neg_one σ hσ with rfl | rfl
    · exact map_one _
    · exact integralSL2ToFiniteProjective_neg_one)

/-- The original integral projective group acts diagonally through its actual real and finite matrices. -/
def integralToAdelicProjective : PSL(2, ℤ) →* AdelicProjectiveGroup :=
  integralToRealPSL.prod integralToFiniteProjective

/-- The actual rational diagonal homomorphism agrees exactly with the original integral projective homomorphism. -/
theorem rationalPositiveToAdelicProjective_integral (σ : SL(2, ℤ)) :
    rationalPositiveToAdelicProjective (toGLPos (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) σ)) =
      integralToAdelicProjective (QuotientGroup.mk σ) := by
  apply Prod.ext
  · change (QuotientGroup.mk (realPositiveNormalize (rationalPositiveGL2ToReal
      (toGLPos (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) σ)))) : PSL(2, ℝ)) =
      integralToRealPSL (QuotientGroup.mk σ)
    rw [rationalPositiveGL2ToReal_integral, realPositiveNormalize_toGLPos,
      integralToRealPSL_mk]
  · apply congrArg ProjGenLinGroup.mk
    apply Units.ext
    funext i j
    exact map_intCast (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) (σ i j)

/-- Every original integral projective matrix belongs to the actual rational arithmetic subgroup. -/
theorem integralToAdelicProjective_mem_arithmetic (σ : PSL(2, ℤ)) :
    integralToAdelicProjective σ ∈ adelicProjectiveArithmetic := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective σ
  exact ⟨toGLPos (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) a),
    rationalPositiveToAdelicProjective_integral a⟩

/-- The faithful projective function of every actual original cyclic vector is invariant under the genuine positive rational diagonal action. -/
theorem adelicCyclicProjectiveFunction_rational_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (γ : GL(2, ℚ)⁺) (p : AdelicProjectiveGroup) :
    adelicCyclicProjectiveFunction N f v (rationalPositiveToAdelicProjective γ * p) =
      adelicCyclicProjectiveFunction N f v p := by
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective p.1
  obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_surjective p.2
  have hp : p = (QuotientGroup.mk r, ProjGenLinGroup.mk a) := Prod.ext hr.symm ha.symm
  rw [hp]
  have he : rationalPositiveToAdelicProjective γ * (QuotientGroup.mk r, ProjGenLinGroup.mk a) =
      (QuotientGroup.mk (realPositiveNormalize (rationalPositiveGL2ToReal γ * toGLPos r)),
        ProjGenLinGroup.mk (rationalPositiveGL2ToFinite γ * a)) := by
    apply Prod.ext
    · simp only [rationalPositiveToAdelicProjective, MonoidHom.prod_apply, MonoidHom.comp_apply,
        Prod.fst_mul, map_mul, realPositiveNormalize_toGLPos, QuotientGroup.mk_mul]
      rfl
    · simp only [rationalPositiveToAdelicProjective, MonoidHom.prod_apply, MonoidHom.comp_apply,
        Prod.snd_mul, map_mul]
  rw [he, adelicCyclicProjectiveFunction_recover_positive, adelicCyclicProjectiveFunction_mk]
  have hg : rationalAdelicGL2RealFiniteEquiv.symm
      ((rationalPositiveGL2ToReal γ * toGLPos r).val, rationalPositiveGL2ToFinite γ * a) =
      GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ.val *
        rationalAdelicGL2RealFiniteEquiv.symm (toGL r, a) := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    rw [MulEquiv.apply_symm_apply, map_mul, rationalAdelicGL2RealFiniteEquiv_rational,
      MulEquiv.apply_symm_apply]
    rfl
  rw [hg]
  exact adelicLiftCyclic_rational_invariant N f v.property γ.val _

/-- Every actual original projective cyclic function is invariant under the whole genuine rational arithmetic subgroup. -/
theorem adelicCyclicProjectiveFunction_arithmetic_invariant (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (γ : adelicProjectiveArithmetic) (p : AdelicProjectiveGroup) :
    adelicCyclicProjectiveFunction N f v (γ.val * p) = adelicCyclicProjectiveFunction N f v p := by
  obtain ⟨a, ha⟩ := γ.property
  rw [← ha]
  exact adelicCyclicProjectiveFunction_rational_invariant N f v a p

end
end Dubon2026
