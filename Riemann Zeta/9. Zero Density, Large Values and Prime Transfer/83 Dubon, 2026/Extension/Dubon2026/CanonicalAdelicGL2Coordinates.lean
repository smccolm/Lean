import Dubon2026.FullAdelicGL2CuspLift

/-! # Actual real and finite group coordinates for canonical full adelic GL2 -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix

/-- Actual entrywise scalar maps are continuous on the original general-linear group. -/
theorem gl2Map_continuous {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] (f : R →+* S) (hf : Continuous f) :
    Continuous (GeneralLinearGroup.map (n := Fin 2) f) := by
  apply Continuous.units_map
  exact continuous_pi fun i => continuous_pi fun j =>
    hf.comp ((_root_.continuous_apply j).comp (_root_.continuous_apply i))

/-- Actual scalar-ring equivalences give genuine invertible matrix group equivalences. -/
def gl2RingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    GeneralLinearGroup (Fin 2) R ≃* GeneralLinearGroup (Fin 2) S :=
  Units.mapEquiv (e.mapMatrix (m := Fin 2)).toMulEquiv

/-- The same original group equivalence respects the topology when both scalar directions do. -/
def gl2RingHomeomorph {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] (e : R ≃+* S)
    (he : Continuous e) (hi : Continuous e.symm) :
    GeneralLinearGroup (Fin 2) R ≃ₜ GeneralLinearGroup (Fin 2) S where
  toEquiv := (gl2RingEquiv e).toEquiv
  continuous_toFun := gl2Map_continuous e.toRingHom he
  continuous_invFun := gl2Map_continuous e.symm.toRingHom hi

/-- The literal coordinate splitting of matrices over a product ring is a ring equivalence. -/
def gl2MatrixProductRingEquiv (R S : Type*) [CommRing R] [CommRing S] :
    Matrix (Fin 2) (Fin 2) (R × S) ≃+*
      (Matrix (Fin 2) (Fin 2) R × Matrix (Fin 2) (Fin 2) S) where
  toFun a := ((RingHom.fst R S).mapMatrix a, (RingHom.snd R S).mapMatrix a)
  invFun a i j := (a.1 i j, a.2 i j)
  left_inv a := by rfl
  right_inv a := by rfl
  map_add' a b := Prod.ext (map_add _ a b) (map_add _ a b)
  map_mul' a b := Prod.ext (map_mul _ a b) (map_mul _ a b)

/-- Invertible matrices over a product ring are exactly the two original invertible coordinate matrices. -/
def gl2ProductEquiv (R S : Type*) [CommRing R] [CommRing S] :
    GeneralLinearGroup (Fin 2) (R × S) ≃*
      (GeneralLinearGroup (Fin 2) R × GeneralLinearGroup (Fin 2) S) :=
  (Units.mapEquiv (gl2MatrixProductRingEquiv R S).toMulEquiv).trans MulEquiv.prodUnits

/-- The actual invertible product-matrix equivalence preserves the original unit-group topology. -/
def gl2ProductHomeomorph (R S : Type*) [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] :
    GeneralLinearGroup (Fin 2) (R × S) ≃ₜ
      (GeneralLinearGroup (Fin 2) R × GeneralLinearGroup (Fin 2) S) where
  toEquiv := (gl2ProductEquiv R S).toEquiv
  continuous_toFun :=
    (gl2Map_continuous (RingHom.fst R S) continuous_fst).prodMk
      (gl2Map_continuous (RingHom.snd R S) continuous_snd)
  continuous_invFun := by
    apply Units.continuous_iff.mpr
    constructor
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact ((_root_.continuous_apply j).comp ((_root_.continuous_apply i).comp
        ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) R)).comp continuous_fst))).prodMk
        ((_root_.continuous_apply j).comp ((_root_.continuous_apply i).comp
          ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) S)).comp continuous_snd)))
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact ((_root_.continuous_apply j).comp ((_root_.continuous_apply i).comp
        ((Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) R)).comp continuous_fst))).prodMk
        ((_root_.continuous_apply j).comp ((_root_.continuous_apply i).comp
          ((Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) S)).comp continuous_snd)))

/-- The canonical full rational adelic GL2 group has the actual real and finite matrix coordinates. -/
def rationalAdelicGL2RealFiniteEquiv :
    GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ) ≃*
      (GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :=
  (gl2RingEquiv rationalAdeleRealFiniteRingEquiv).trans (gl2ProductEquiv _ _)

/-- The actual full adelic GL2 coordinate equivalence is a homeomorphism. -/
def rationalAdelicGL2RealFiniteHomeomorph :
    GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ) ≃ₜ
      (GeneralLinearGroup (Fin 2) ℝ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :=
  (gl2RingHomeomorph rationalAdeleRealFiniteRingEquiv
    rationalAdeleRealFiniteRingEquiv_continuous
    rationalAdeleRealFiniteRingEquiv_symm_continuous).trans (gl2ProductHomeomorph _ _)

/-- The canonical full adelic GL2 coordinates are continuous. -/
theorem rationalAdelicGL2RealFiniteEquiv_continuous :
    Continuous rationalAdelicGL2RealFiniteEquiv :=
  rationalAdelicGL2RealFiniteHomeomorph.continuous

/-- Their actual inverse is continuous. -/
theorem rationalAdelicGL2RealFiniteEquiv_symm_continuous :
    Continuous rationalAdelicGL2RealFiniteEquiv.symm :=
  rationalAdelicGL2RealFiniteHomeomorph.symm.continuous

/-- An original principal rational invertible matrix has precisely its real and finite diagonal coordinates. -/
theorem rationalAdelicGL2RealFiniteEquiv_rational (γ : GeneralLinearGroup (Fin 2) ℚ) :
    rationalAdelicGL2RealFiniteEquiv
      (GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ) =
      (rationalGL2ToReal γ, rationalGL2ToFinite γ) := by
  apply Prod.ext
  · apply Units.ext
    funext i j
    exact congrArg Prod.fst (rationalAdeleRealFiniteRingEquiv_algebraMap (γ.val i j))
  · apply Units.ext
    funext i j
    exact congrArg Prod.snd (rationalAdeleRealFiniteRingEquiv_algebraMap (γ.val i j))

/-- The actual full general-linear coordinates preserve the original determinant-one embedding. -/
theorem rationalAdelicGL2RealFiniteEquiv_toGL
    (g : Matrix.SpecialLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) :
    rationalAdelicGL2RealFiniteEquiv (Matrix.SpecialLinearGroup.toGL g) =
      (Matrix.SpecialLinearGroup.toGL (rationalAdelicSL2RealFiniteEquiv g).1,
        Matrix.SpecialLinearGroup.toGL (rationalAdelicSL2RealFiniteEquiv g).2) := by
  apply Prod.ext <;> apply Units.ext <;> rfl

end
end Dubon2026
