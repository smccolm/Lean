import Dubon2026.OriginalAdicDecompositionAction
import Mathlib.FieldTheory.Galois.Basic

/-! # The actual original completion extension is finite Galois

The proved base-completion/fixed-field identity transfers finite Galois
structure to the literal original completion embedding. Its automorphisms
are the same completed original decomposition-group transports. This
identifies the local coefficient used in global H2 detection with the
finite Galois local-field input to normalized invariants, serving DUB-17's
cyclic splitting and invariant sum-zero dependency.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The original base-completion embedding gives an actual finite-dimensional Galois extension. -/
theorem originalAdicBaseChange_finite_galois :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) ∧
      IsGalois (v.adicCompletion K) (w.adicCompletion L) := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI := originalAdicDecompositionAction K L w
  letI := originalAdicDecompositionAction_faithful K L w
  let B := FixedPoints.subfield (OriginalFiniteDecompositionGroup K L w) (w.adicCompletion L)
  let e := originalAdicBaseFixedEquiv K L v w
  have he (a : B) : originalAdicBaseChangeMap K L v w (e.symm a) = a.val := by
    rw [← originalAdicBaseFixedEquiv_val]
    exact congrArg Subtype.val (e.apply_symm_apply a)
  let f : w.adicCompletion L →ₛₗ[e.symm.toRingHom] w.adicCompletion L := {
    toFun := id
    map_add' _ _ := rfl
    map_smul' a x := by
      change a.val * x = originalAdicBaseChangeMap K L v w (e.symm a) * x
      rw [he] }
  letI : RingHomSurjective e.symm.toRingHom := ⟨e.symm.surjective⟩
  have hf : FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) :=
    Module.Finite.of_surjective f Function.surjective_id
  refine ⟨hf, ?_⟩
  apply IsGalois.of_equiv_equiv (F := B) (E := w.adicCompletion L)
    (f := e.symm) (g := RingEquiv.refl (w.adicCompletion L))
  apply RingHom.ext
  intro a
  exact he a

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual original decomposition group is the actual Galois group of the original completion extension. -/
def originalAdicDecompositionGaloisEquiv :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    OriginalFiniteDecompositionGroup K L w ≃*
      Gal(w.adicCompletion L/v.adicCompletion K) := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI := originalAdicDecompositionAction K L w
  letI := originalAdicDecompositionAction_faithful K L w
  let B := FixedPoints.subfield (OriginalFiniteDecompositionGroup K L w) (w.adicCompletion L)
  let e := originalAdicBaseFixedEquiv K L v w
  have he (a : B) : originalAdicBaseChangeMap K L v w (e.symm a) = a.val := by
    rw [← originalAdicBaseFixedEquiv_val]
    exact congrArg Subtype.val (e.apply_symm_apply a)
  let f : Gal(w.adicCompletion L/B) →* Gal(w.adicCompletion L/v.adicCompletion K) := {
    toFun := fun σ => {
      __ := σ.toRingEquiv
      commutes' := fun x => by
        change σ (originalAdicBaseChangeMap K L v w x) = originalAdicBaseChangeMap K L v w x
        rw [← originalAdicBaseFixedEquiv_val]
        exact σ.commutes (e x) }
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro σ τ h
      apply AlgEquiv.ext
      intro x
      exact congrArg (fun η : Gal(w.adicCompletion L/v.adicCompletion K) => η x) h
    · intro σ
      let τ : Gal(w.adicCompletion L/B) := {
        __ := σ.toRingEquiv
        commutes' := fun a => by
          change σ a.val = a.val
          rw [← he a]
          exact σ.commutes (e.symm a) }
      exact ⟨τ, rfl⟩
  exact (FixedPoints.toAlgAutMulEquiv (OriginalFiniteDecompositionGroup K L w)
    (w.adicCompletion L)).trans (MulEquiv.ofBijective f hf)

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual completion Galois equivalence retains the original completed transport on every coefficient. -/
theorem originalAdicDecompositionGaloisEquiv_apply
    (σ : OriginalFiniteDecompositionGroup K L w) (x : w.adicCompletion L) :
    originalAdicDecompositionGaloisEquiv K L v w σ x =
      numberFieldGaloisLocalTransport K L σ.val w w σ.property x := rfl

end
end Dubon2026
