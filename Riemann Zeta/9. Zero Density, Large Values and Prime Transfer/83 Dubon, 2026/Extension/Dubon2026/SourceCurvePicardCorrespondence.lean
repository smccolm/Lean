import Dubon2026.SourceCurvePicardPushforward

/-! DUB-17/18 -> original Picard Hecke correspondence. The two specified
finite function-field maps determine pullback followed by pushforward.
The existing actual degree and norm identities descend that composite to
degree-zero divisor classes. Finiteness and residue identifications remain
explicit here and are derived for the original Hecke maps in the consumer.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_AlgebraicCurve_Correspondence.lean.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [CharZero F]

/-- The exact extension algebra supplied by a specified curve function-field map. -/
abbrev algebraAlong (φ : F →ₐ[K] E) : Algebra F E := φ.toRingHom.toAlgebra

omit [CharZero F] in
theorem scalarTower_along (φ : F →ₐ[K] E) :
    letI := algebraAlong φ; IsScalarTower K F E := by
  letI := algebraAlong φ
  exact IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm

namespace Divisor

/-- Divisor pullback along the specified finite function-field embedding. -/
def finitePullbackAlong (φ : F →ₐ[K] E) (hφ : φ.toRingHom.Finite) :
    Divisor K F →+ Divisor K E :=
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite F E := hφ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  finitePullback E

/-- Divisor pushforward along the specified embedding in the residue-degree-one case. -/
def geometricPushforwardAlong (ψ : F →ₐ[K] E) (hψ : ψ.toRingHom.Finite) :
    Divisor K E →+ Divisor K F :=
  letI := algebraAlong ψ
  haveI := scalarTower_along ψ
  haveI : Module.Finite F E := hψ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  geometricPushforward F

theorem finitePullbackAlong_mem_degZero (φ : F →ₐ[K] E) (hφ : φ.toRingHom.Finite)
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {D : Divisor K F} (hD : D ∈ degZero) : finitePullbackAlong φ hφ D ∈ degZero := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite F E := hφ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  exact finitePullback_mem_degZero hF hE hD

theorem geometricPushforwardAlong_mem_degZero (ψ : F →ₐ[K] E) (hψ : ψ.toRingHom.Finite)
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {D : Divisor K E} (hD : D ∈ degZero) : geometricPushforwardAlong ψ hψ D ∈ degZero := by
  letI := algebraAlong ψ
  haveI := scalarTower_along ψ
  haveI : Module.Finite F E := hψ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  exact geometricPushforward_mem_degZero F hF hE hD

theorem isPrincipal_finitePullbackAlong (φ : F →ₐ[K] E) (hφ : φ.toRingHom.Finite)
    {D : Divisor K F} (hD : IsPrincipal D) : IsPrincipal (finitePullbackAlong φ hφ D) := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite F E := hφ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  exact isPrincipal_finitePullback E hD

theorem isPrincipal_geometricPushforwardAlong (ψ : F →ₐ[K] E) (hψ : ψ.toRingHom.Finite)
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {D : Divisor K E} (hD : IsPrincipal D) : IsPrincipal (geometricPushforwardAlong ψ hψ D) := by
  letI := algebraAlong ψ
  haveI := scalarTower_along ψ
  haveI : Module.Finite F E := hψ
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  exact isPrincipal_geometricPushforward F hF hE hD

/-- The actual divisor correspondence: pull back along φ, then push forward along ψ. -/
def geometricCorrespondence (φ ψ : F →ₐ[K] E)
    (hφ : φ.toRingHom.Finite) (hψ : ψ.toRingHom.Finite) : Divisor K F →+ Divisor K F :=
  (geometricPushforwardAlong ψ hψ).comp (finitePullbackAlong φ hφ)

theorem geometricCorrespondence_mem_degZero (φ ψ : F →ₐ[K] E)
    (hφ : φ.toRingHom.Finite) (hψ : ψ.toRingHom.Finite)
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {D : Divisor K F} (hD : D ∈ degZero) : geometricCorrespondence φ ψ hφ hψ D ∈ degZero :=
  geometricPushforwardAlong_mem_degZero ψ hψ hF hE
    (finitePullbackAlong_mem_degZero φ hφ hF hE hD)

theorem isPrincipal_geometricCorrespondence (φ ψ : F →ₐ[K] E)
    (hφ : φ.toRingHom.Finite) (hψ : ψ.toRingHom.Finite)
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {D : Divisor K F} (hD : IsPrincipal D) : IsPrincipal (geometricCorrespondence φ ψ hφ hψ D) :=
  isPrincipal_geometricPushforwardAlong ψ hψ hF hE (isPrincipal_finitePullbackAlong φ hφ hD)

end Divisor
namespace Pic0

/-- The actual finite geometric correspondence on degree-zero divisor classes. -/
def geometricCorrespondence (φ ψ : F →ₐ[K] E)
    (hφ : φ.toRingHom.Finite) (hψ : ψ.toRingHom.Finite)
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField)) :
    Pic0 K F →+ Pic0 K F :=
  QuotientAddGroup.map _ _
    (((Divisor.geometricCorrespondence φ ψ hφ hψ).comp Divisor.degZero.subtype).codRestrict
      Divisor.degZero (fun D => Divisor.geometricCorrespondence_mem_degZero φ ψ hφ hψ hF hE D.2))
    (by
      rintro ⟨D, hD0⟩ hD
      exact Divisor.isPrincipal_geometricCorrespondence φ ψ hφ hψ hF hE hD)

theorem geometricCorrespondence_mk (φ ψ : F →ₐ[K] E)
    (hφ : φ.toRingHom.Finite) (hψ : ψ.toRingHom.Finite)
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (D : Divisor.degZero (K := K) (F := F)) :
    geometricCorrespondence φ ψ hφ hψ hF hE (mk D) =
      mk ⟨Divisor.geometricCorrespondence φ ψ hφ hψ D.val,
        Divisor.geometricCorrespondence_mem_degZero φ ψ hφ hψ hF hE D.2⟩ := rfl

end Pic0
end
end Dubon2026.SourceCurve
