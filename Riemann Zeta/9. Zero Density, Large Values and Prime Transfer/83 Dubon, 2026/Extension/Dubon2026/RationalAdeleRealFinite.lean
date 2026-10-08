import Dubon2026.CanonicalAdicIntegralDensity
import Mathlib.NumberTheory.NumberField.AdeleRing

/-! # Exact real and finite coordinates for the canonical rational adele ring -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The unique actual rational infinite completion identifies the infinite adele ring with the reals. -/
def rationalInfiniteAdeleRingEquiv : InfiniteAdeleRing ℚ ≃+* ℝ :=
  (RingEquiv.piUnique (fun v : InfinitePlace ℚ => v.Completion)).trans
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)

/-- The same actual infinite-place identification is a homeomorphism. -/
def rationalInfiniteAdeleHomeomorph : InfiniteAdeleRing ℚ ≃ₜ ℝ :=
  (Homeomorph.piUnique (fun v : InfinitePlace ℚ => v.Completion)).trans
    (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).toHomeomorph

/-- The actual infinite-place ring equivalence is continuous. -/
theorem rationalInfiniteAdeleRingEquiv_continuous : Continuous rationalInfiniteAdeleRingEquiv :=
  rationalInfiniteAdeleHomeomorph.continuous

/-- Its actual inverse is continuous as well. -/
theorem rationalInfiniteAdeleRingEquiv_symm_continuous :
    Continuous rationalInfiniteAdeleRingEquiv.symm :=
  rationalInfiniteAdeleHomeomorph.symm.continuous

/-- The canonical full rational adele ring is exactly its real and finite coordinates. -/
def rationalAdeleRealFiniteRingEquiv : AdeleRing ℤ ℚ ≃+* (ℝ × FiniteAdeleRing ℤ ℚ) :=
  RingEquiv.prodCongr rationalInfiniteAdeleRingEquiv (RingEquiv.refl _)

/-- The actual full-adele coordinate map is continuous. -/
theorem rationalAdeleRealFiniteRingEquiv_continuous : Continuous rationalAdeleRealFiniteRingEquiv :=
  rationalInfiniteAdeleRingEquiv_continuous.prodMap continuous_id

/-- The inverse full-adele coordinate map is continuous. -/
theorem rationalAdeleRealFiniteRingEquiv_symm_continuous :
    Continuous rationalAdeleRealFiniteRingEquiv.symm :=
  rationalInfiniteAdeleRingEquiv_symm_continuous.prodMap continuous_id

/-- Principal rational adeles become the literal real and finite rational diagonal. -/
theorem rationalAdeleRealFiniteRingEquiv_algebraMap (q : ℚ) :
    rationalAdeleRealFiniteRingEquiv (algebraMap ℚ (AdeleRing ℤ ℚ) q) =
      ((q : ℝ), algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) := by
  apply Prod.ext
  · have he : rationalInfiniteAdeleRingEquiv.toRingHom.comp
        (algebraMap ℚ (InfiniteAdeleRing ℚ)) = Rat.castHom ℝ := Subsingleton.elim _ _
    exact RingHom.congr_fun he q
  · rfl

/-- The genuine determinant-one product-ring equivalence also preserves the product topology. -/
def sl2ProductHomeomorph (R S : Type*) [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] :
    SL(2, R × S) ≃ₜ (SL(2, R) × SL(2, S)) where
  toEquiv := (sl2ProductEquiv R S).toEquiv
  continuous_toFun :=
    (show Continuous (RingHom.fst R S) from continuous_fst).specialLinearGroup_map.prodMk
      (show Continuous (RingHom.snd R S) from continuous_snd).specialLinearGroup_map
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact ((_root_.continuous_apply j).comp
      (Matrix.SpecialLinearGroup.continuous_apply _ continuous_fst i)).prodMk
      ((_root_.continuous_apply j).comp
        (Matrix.SpecialLinearGroup.continuous_apply _ continuous_snd i))

/-- The actual canonical full adelic determinant-one group has exact real and finite group coordinates. -/
def rationalAdelicSL2RealFiniteEquiv :
    SL(2, AdeleRing ℤ ℚ) ≃* (SL(2, ℝ) × SL(2, FiniteAdeleRing ℤ ℚ)) :=
  (sl2RingEquiv rationalAdeleRealFiniteRingEquiv).trans (sl2ProductEquiv _ _)

/-- The actual canonical full adelic determinant-one group has the expected real-times-finite topology. -/
def rationalAdelicSL2RealFiniteHomeomorph :
    SL(2, AdeleRing ℤ ℚ) ≃ₜ (SL(2, ℝ) × SL(2, FiniteAdeleRing ℤ ℚ)) :=
  (sl2RingHomeomorph rationalAdeleRealFiniteRingEquiv
    rationalAdeleRealFiniteRingEquiv_continuous
    rationalAdeleRealFiniteRingEquiv_symm_continuous).trans (sl2ProductHomeomorph _ _)

/-- The actual full adelic group coordinates are continuous. -/
theorem rationalAdelicSL2RealFiniteEquiv_continuous :
    Continuous rationalAdelicSL2RealFiniteEquiv :=
  rationalAdelicSL2RealFiniteHomeomorph.continuous

/-- Their inverse is continuous for the original canonical group topology. -/
theorem rationalAdelicSL2RealFiniteEquiv_symm_continuous :
    Continuous rationalAdelicSL2RealFiniteEquiv.symm :=
  rationalAdelicSL2RealFiniteHomeomorph.symm.continuous

end
end Dubon2026
