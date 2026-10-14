import Dubon2026.LocalFieldAmbientUniformizer
import Dubon2026.RationalPrimeChangedCyclotomicLocalField
import Dubon2026.RationalPrimeChangedAuxiliaryLocalField
import Dubon2026.WittCyclotomicChangedUniformizer
import Dubon2026.LocalFieldIntegerAlgebraFinite
import Mathlib.RingTheory.Valuation.Discrete.RankOne

/-! # The changed auxiliary uniformizer in the actual cyclotomic compositum

The explicit changed root algebra maps into the original cyclotomic DVR and
agrees there with the already constructed auxiliary field.  Integral closure
and the ambient-DVR comparison show that its auxiliary uniformizer remains a
uniformizer, hence irreducible, in the actual compositum.  This discharges the
remaining ramification premise of DUB-17's unramified local stage.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

set_option maxHeartbeats 800000

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootDVR wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra
  wittCyclotomicFieldTower rationalPrimeWittOriginalAlgebra
  rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower
  rationalPrimeWittCyclotomicModule rationalPrimeWittCyclotomicMulAction
  rationalPrimeChangedIntegralRootDomain rationalPrimeChangedIntegralRootDVR

local instance rationalPrimeCyclotomicRootIntegerAlgebra
    (p : ℕ) (hp : p.Prime) (n : ℕ) :
    Algebra 𝒪[rationalPrimeLocalField p hp]
      (wittCyclotomicRootAlgebra
        (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n) :=
  (((algebraMap
    (WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
      (AlgebraicClosure
        (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)))))
    (wittCyclotomicRootAlgebra
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)).comp
    (rationalPrimeIntegerWittMap p hp))).toAlgebra

theorem rationalPrimeChangedIntegralPolynomial_ambient_aeval
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    let v := Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u
    Polynomial.eval₂
      (algebraMap 𝒪[rationalPrimeLocalField p hp] (wittCyclotomicRootAlgebra q n))
      (wittCyclotomicChangedPoint q v n)
      (rationalPrimeChangedIntegralPolynomial p hp n u) = 0 := by
  dsimp only
  let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
  let v := Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u
  have hv : (v : WittVector q (AlgebraicClosure (ZMod q))) = a := by
    change rationalPrimeIntegerWittMap p hp u.val = a
    rw [hu, map_natCast]
  have h := wittCyclotomicChangedPoint_primitivePolynomial q v n a hv
    (by simpa only [q, rationalPrimePlace_natGenerator] using ha)
  rw [rationalPrimeChangedIntegralPolynomial]
  change Polynomial.eval₂
    ((algebraMap (WittVector q (AlgebraicClosure (ZMod q)))
      (wittCyclotomicRootAlgebra q n)).comp (rationalPrimeIntegerWittMap p hp))
    (wittCyclotomicChangedPoint q v n)
    (primeChangedPrimitivePolynomial p (u.val * p) n) = 0
  rw [← Polynomial.eval₂_map]
  rw [primeChangedPrimitivePolynomial_map]
  simpa only [q, v, map_mul, map_natCast, rationalPrimePlace_natGenerator] using h

def rationalPrimeChangedIntegralRootAmbientAlgHom
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    AdjoinRoot (rationalPrimeChangedIntegralPolynomial p hp n u) →ₐ[
      𝒪[rationalPrimeLocalField p hp]]
      wittCyclotomicRootAlgebra
        (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _)
    (wittCyclotomicChangedPoint
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
      (Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u) n)
    (rationalPrimeChangedIntegralPolynomial_ambient_aeval p hp n a u hu ha)

theorem rationalPrimeChangedIntegralRootAmbientAlgHom_field
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    let E := rationalPrimeChangedAuxiliaryField p hp n u
    let Ω := wittCyclotomicField q n
    (algebraMap (wittCyclotomicRootAlgebra q n) Ω).comp
        (rationalPrimeChangedIntegralRootAmbientAlgHom p hp n a u hu ha).toRingHom =
      E.val.toRingHom.comp
        (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha).toRingHom := by
  dsimp only
  apply AdjoinRoot.ringHom_ext
  · ext x
    simp only [RingHom.comp_apply]
    change algebraMap
        (wittCyclotomicRootAlgebra
          (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)
        (wittCyclotomicField
          (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)
        (rationalPrimeChangedIntegralRootAmbientAlgHom p hp n a u hu ha
          (AdjoinRoot.of (rationalPrimeChangedIntegralPolynomial p hp n u) x)) =
      (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha
        (AdjoinRoot.of (rationalPrimeChangedIntegralPolynomial p hp n u) x)).val
    rw [show rationalPrimeChangedIntegralRootAmbientAlgHom p hp n a u hu ha
          (AdjoinRoot.of (rationalPrimeChangedIntegralPolynomial p hp n u) x) =
        algebraMap 𝒪[rationalPrimeLocalField p hp]
          (wittCyclotomicRootAlgebra
            (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n) x from
      AdjoinRoot.liftAlgHom_of _ _ _ _ _]
    rw [show rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha
          (AdjoinRoot.of (rationalPrimeChangedIntegralPolynomial p hp n u) x) =
        algebraMap 𝒪[rationalPrimeLocalField p hp]
          (rationalPrimeChangedAuxiliaryField p hp n u) x from
      AdjoinRoot.liftAlgHom_of _ _ _ _ _]
    change algebraMap
        (wittCyclotomicRootAlgebra
          (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)
        (wittCyclotomicField
          (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)
        (algebraMap
          (WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
            (AlgebraicClosure
              (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)))))
          (wittCyclotomicRootAlgebra
            (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)
          (rationalPrimeIntegerWittMap p hp x)) =
      algebraMap (rationalPrimeLocalField p hp)
        (wittCyclotomicField
          (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)
        (algebraMap 𝒪[rationalPrimeLocalField p hp]
          (rationalPrimeLocalField p hp) x)
    rw [← IsScalarTower.algebraMap_apply
      (WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
        (AlgebraicClosure
          (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)))))
      (wittCyclotomicRootAlgebra
        (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)
      (wittCyclotomicField
        (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)]
    rw [IsScalarTower.algebraMap_apply
      (rationalPrimeLocalField p hp) (rationalPrimeWittField p hp)
      (wittCyclotomicField
        (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)]
    rw [IsScalarTower.algebraMap_apply
      (WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
        (AlgebraicClosure
          (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)))))
      (rationalPrimeWittField p hp)
      (wittCyclotomicField
        (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)]
    change algebraMap (rationalPrimeWittField p hp)
        (wittCyclotomicField
          (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)
        (algebraMap
          (WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
            (AlgebraicClosure
              (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)))))
          (rationalPrimeWittField p hp)
          (rationalPrimeIntegerWittMap p hp x)) =
      algebraMap (rationalPrimeWittField p hp)
        (wittCyclotomicField
          (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)
        (rationalPrimeWittFieldMap p hp
          (algebraMap 𝒪[rationalPrimeLocalField p hp]
            (rationalPrimeLocalField p hp) x))
    rw [rationalPrimeWittFieldMap_integer]
  · change algebraMap _ _
        (rationalPrimeChangedIntegralRootAmbientAlgHom p hp n a u hu ha
          (AdjoinRoot.root (rationalPrimeChangedIntegralPolynomial p hp n u))) =
      ((rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha
          (AdjoinRoot.root (rationalPrimeChangedIntegralPolynomial p hp n u))) :
        rationalPrimeChangedAuxiliaryField p hp n u).val
    rw [show rationalPrimeChangedIntegralRootAmbientAlgHom p hp n a u hu ha
          (AdjoinRoot.root (rationalPrimeChangedIntegralPolynomial p hp n u)) =
        wittCyclotomicChangedPoint
          (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
          (Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u) n from
      AdjoinRoot.liftAlgHom_root _ _ _ _]
    rw [rationalPrimeChangedIntegralRootAlgHom_root]
    rfl

def rationalPrimeChangedAuxiliaryIntegerAmbientMap
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u))] :
    𝒪[rationalPrimeChangedAuxiliaryField p hp n u] →+*
      wittCyclotomicRootAlgebra
        (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n := by
  let K := rationalPrimeLocalField p hp
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  let f := rationalPrimeChangedIntegralPolynomial p hp n u
  let A := AdjoinRoot f
  letI : Algebra A E :=
    (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha).toAlgebra
  haveI : IsScalarTower 𝒪[K] A E := IsScalarTower.of_algebraMap_eq fun x =>
    (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha).commutes x |>.symm
  haveI : IsFractionRing A E :=
    rationalPrimeChangedAuxiliaryField_isFractionRing p hp n a u hu ha
  let e := localFieldMonicRootIntegerEquiv K E f
    (rationalPrimeChangedIntegralPolynomial_monic p hp n u)
  exact (rationalPrimeChangedIntegralRootAmbientAlgHom p hp n a u hu ha).toRingHom.comp
    e.symm.toRingEquiv.toRingHom

theorem rationalPrimeChangedAuxiliaryIntegerAmbientMap_field
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u))] :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    let E := rationalPrimeChangedAuxiliaryField p hp n u
    let Ω := wittCyclotomicField q n
    (algebraMap (wittCyclotomicRootAlgebra q n) Ω).comp
        (rationalPrimeChangedAuxiliaryIntegerAmbientMap p hp n a u hu ha) =
      E.val.toRingHom.comp (algebraMap 𝒪[E] E) := by
  dsimp only
  let K := rationalPrimeLocalField p hp
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  let f := rationalPrimeChangedIntegralPolynomial p hp n u
  let A := AdjoinRoot f
  letI : Algebra A E :=
    (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha).toAlgebra
  haveI : IsScalarTower 𝒪[K] A E := IsScalarTower.of_algebraMap_eq fun x =>
    (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha).commutes x |>.symm
  haveI : IsFractionRing A E :=
    rationalPrimeChangedAuxiliaryField_isFractionRing p hp n a u hu ha
  let e := localFieldMonicRootIntegerEquiv K E f
    (rationalPrimeChangedIntegralPolynomial_monic p hp n u)
  ext z
  let b : A := e.symm z
  have hroot := RingHom.congr_fun
    (rationalPrimeChangedIntegralRootAmbientAlgHom_field p hp n a u hu ha) b
  have he := localFieldMonicRootIntegerEquiv_coefficient K E f
    (rationalPrimeChangedIntegralPolynomial_monic p hp n u) b
  change algebraMap _ _
      (rationalPrimeChangedIntegralRootAmbientAlgHom p hp n a u hu ha b) =
    (algebraMap 𝒪[E] E z).val
  calc
    algebraMap _ _
        (rationalPrimeChangedIntegralRootAmbientAlgHom p hp n a u hu ha b) =
      E.val (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha b) := hroot
    _ = E.val (algebraMap 𝒪[E] E z) := by
      congr 1
      simpa only [b, e, AlgEquiv.apply_symm_apply] using he.symm

theorem rationalPrimeChangedAuxiliary_exists_compositum_integer_uniformizer
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u))]
    [ValuativeRel (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicCompositum p hp n u))] :
    ∃ θE : 𝒪[rationalPrimeChangedAuxiliaryField p hp n u],
      Irreducible θE ∧
      algebraMap 𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
          (rationalPrimeChangedAuxiliaryField p hp n u) θE =
        rationalPrimeChangedAuxiliaryPoint p hp n u ∧
      Algebra.norm (rationalPrimeLocalField p hp)
          (-algebraMap 𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
            (rationalPrimeChangedAuxiliaryField p hp n u) θE) =
        (a : rationalPrimeLocalField p hp) * p ∧
      Irreducible (algebraMap
        𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
        𝒪[rationalPrimeChangedCyclotomicCompositum p hp n u] θE) := by
  let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
  let K := rationalPrimeLocalField p hp
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  let M := rationalPrimeChangedCyclotomicCompositum p hp n u
  let B := wittCyclotomicRootAlgebra q n
  let Ω := wittCyclotomicField q n
  obtain ⟨θE, hθE, hvalue, hnorm⟩ :=
    rationalPrimeChangedAuxiliary_exists_integer_uniformizer p hp n a u hu ha
  refine ⟨θE, hθE, hvalue, hnorm, ?_⟩
  let j : 𝒪[E] →+* B :=
    rationalPrimeChangedAuxiliaryIntegerAmbientMap p hp n a u hu ha
  let ι : M →+* Ω := M.val.toRingHom
  have hjfield : (algebraMap B Ω).comp j =
      E.val.toRingHom.comp (algebraMap 𝒪[E] E) :=
    rationalPrimeChangedAuxiliaryIntegerAmbientMap_field p hp n a u hu ha
  have hcomp : (algebraMap B Ω).comp j =
      ι.comp (algebraMap 𝒪[E] M) := by
    rw [hjfield]
    ext z
    rfl
  let vΩ := (IsDiscreteValuationRing.maximalIdeal B).valuation Ω
  let changedB : B := wittCyclotomicChangedPoint q
    (Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u) n
  have hchangedB : Irreducible changedB :=
    wittCyclotomicChangedPoint_irreducible q
      (Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u) n
  let changedInteger : vΩ.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring changedB
  have hchangedInteger : Irreducible changedInteger :=
    (MulEquiv.irreducible_iff
      (f := (IsDiscreteValuationRing.equivValuationSubring
        (A := B) (K := Ω)).toMulEquiv)).mpr hchangedB
  have hchangedUniformizer : vΩ.IsUniformizer (algebraMap B Ω changedB) := by
    have h := vΩ.isUniformizer_of_maximalIdeal_eq_span
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer changedInteger).mp
        hchangedInteger)
    exact h
  have hπ : vΩ.IsUniformizer
      (ι (algebraMap E M (algebraMap 𝒪[E] E θE))) := by
    convert hchangedUniformizer using 1
    change ((algebraMap 𝒪[E] E θE : E) : Ω) = algebraMap B Ω changedB
    rw [hvalue]
    rfl
  have hfieldUniformizer : (ValuativeRel.valuation M).IsUniformizer
      (algebraMap E M (algebraMap 𝒪[E] E θE)) :=
    localField_isUniformizer_of_integral_ambient_embedding
      E M B Ω j ι hcomp hπ
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  let θM : 𝒪[M] := algebraMap 𝒪[E] 𝒪[M] θE
  have hθM : (ValuativeRel.valuation M).IsUniformizer (θM : M) := by
    simpa only [θM, IsScalarTower.algebraMap_apply 𝒪[E] E M] using hfieldUniformizer
  exact hθM.is_generator

/-- The actual changed/cyclotomic compositum is formally unramified over the
changed auxiliary field.  The finite integer extension is supplied by the
proved local-field finiteness theorem, and the preceding theorem discharges
the criterion's sole ramification premise. -/
theorem rationalPrimeChangedCyclotomicCompositum_formallyUnramified
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u))]
    [ValuativeRel (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicCompositum p hp n u))] :
    Algebra.FormallyUnramified
      𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
      𝒪[rationalPrimeChangedCyclotomicCompositum p hp n u] := by
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  let M := rationalPrimeChangedCyclotomicCompositum p hp n u
  haveI : Module.Finite 𝒪[E] 𝒪[M] := localField_integer_module_finite
  obtain ⟨θE, hθE, _, _, hmap⟩ :=
    rationalPrimeChangedAuxiliary_exists_compositum_integer_uniformizer
      p hp n a u hu ha
  exact localField_integer_formallyUnramified_of_irreducible_algebraMap
    E M θE hθE hmap

end
end Dubon2026
