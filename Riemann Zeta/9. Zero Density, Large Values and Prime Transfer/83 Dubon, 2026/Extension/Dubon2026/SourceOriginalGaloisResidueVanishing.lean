import Dubon2026.SourceOriginalGaloisRationalResidues
import Dubon2026.SourceCurveResidueSumEquiv
import Dubon2026.SourceCurveGaloisTraceReduction

/-! DUB-17/18 -> original global residue identity -> finite Galois averaging.
The actual auxiliary functional vanishes on its rational base field and is
invariant under all of its Galois automorphisms. Native trace averaging then
proves it zero on the whole literal normal closure. The proved actual
place-fiber ramification comparison descends this identity in
SourceOriginalGaloisResidueDescent; it is not a premise of this module.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

/-- The canonical constant action on the literal rational subfield. -/
local instance originalResidueJAlgebra : Algebra L (IntermediateField.adjoin L {jOver N L}) :=
  (IntermediateField.adjoin L {jOver N L}).toSubalgebra.algebra

theorem originalGaloisResidueMap_base (b : IntermediateField.adjoin L {jOver N L}) :
    originalGaloisResidueMap N L
      (algebraMap (IntermediateField.adjoin L {jOver N L}) (originalGaloisClosure N L) b) = 0 := by
  let e := RatFunc.algEquivOfTranscendental (jOver N L) (transcendental_jOver N L)
  have h := originalGaloisResidueMap_rational N L (e.symm b)
  have he : originalGaloisRationalEmbedding N L (e.symm b) =
      algebraMap (IntermediateField.adjoin L {jOver N L}) (originalGaloisClosure N L) b := by
    change algebraMap (modularFunctionFieldOver N L) (originalGaloisClosure N L)
      ((e (e.symm b) : IntermediateField.adjoin L {jOver N L}) : modularFunctionFieldOver N L) = _
    rw [e.apply_symm_apply, IsScalarTower.algebraMap_apply
      (IntermediateField.adjoin L {jOver N L}) (modularFunctionFieldOver N L)
        (originalGaloisClosure N L)]
    rfl
  rwa [he] at h

theorem originalGaloisResidueMap_invariant
    (e : originalGaloisClosure N L ≃ₐ[L] originalGaloisClosure N L)
    (hj : e (originalGaloisJ N L) = originalGaloisJ N L) (g : originalGaloisClosure N L) :
    originalGaloisResidueMap N L (e g) = originalGaloisResidueMap N L g := by
  rw [originalGaloisResidueMap_apply, originalGaloisResidueMap_apply]
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : ∀ v : Place L (originalGaloisClosure N L),
      Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄L] :=
    finite_originalGaloisClosure_place_differentials N L
  haveI : ∀ v : Place L (originalGaloisClosure N L), Algebra.IsSeparable L v.ResidueField :=
    fun v => by
      haveI := originalGaloisClosure_place_residue_isAlgebraic N L v
      infer_instance
  haveI : ∀ v : Place L (originalGaloisClosure N L), v.DCoordGenerates :=
    originalGaloisClosure_place_dCoordGenerates N L
  haveI : Nontrivial Ω[originalGaloisClosure N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_originalGaloisClosure_differentials N L)
  have h := residueSum_equiv (K := L) (F := originalGaloisClosure N L)
    (originalGaloisCanonicalLocalResidueData N L)
    (originalGaloisClosure_place_residue_bijective N L) e g (originalGaloisJ N L)
  exact (congrArg (fun x : originalGaloisClosure N L =>
    ∑ᶠ v : Place L (originalGaloisClosure N L),
      kaehlerResidueTermKFam (originalGaloisCanonicalLocalResidueData N L)
        (D L (originalGaloisClosure N L) x)
        (diagonalHom L (originalGaloisClosure N L) (e g)) v) hj).symm.trans h

theorem originalGaloisResidueMap_eq_zero : originalGaloisResidueMap N L = 0 := by
  let B := IntermediateField.adjoin L {jOver N L}
  let F := modularFunctionFieldOver N L
  let G := originalGaloisClosure N L
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : FiniteDimensional B G := finite_originalGaloisClosure_over_j N L
  haveI : IsGalois B G := galois_originalGaloisClosure_over_j N L
  letI : IsScalarTower L B G := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply B F G, ← IsScalarTower.algebraMap_apply L B F,
      ← IsScalarTower.algebraMap_apply L F G]
  apply linearMap_eq_zero_of_galois_invariant (F := B)
  · exact originalGaloisResidueMap_base N L
  · intro σ g
    let e : G ≃ₐ[L] G := σ.restrictScalars L
    have hj : e (originalGaloisJ N L) = originalGaloisJ N L := by
      let b : B := ⟨jOver N L, IntermediateField.subset_adjoin L _ (Set.mem_singleton _)⟩
      have hb : algebraMap B G b = originalGaloisJ N L := by
        rw [IsScalarTower.algebraMap_apply B F G]
        rfl
      change σ (originalGaloisJ N L) = originalGaloisJ N L
      rw [← hb, σ.commutes]
    exact originalGaloisResidueMap_invariant N L e hj g

end
end Dubon2026.SourceFunctionField
