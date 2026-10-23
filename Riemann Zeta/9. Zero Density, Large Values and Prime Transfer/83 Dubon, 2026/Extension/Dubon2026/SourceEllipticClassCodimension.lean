import Dubon2026.SourceEllipticClassIdealFactorization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Isomorphisms

/-! The affine ideal-class route to the actual odd cyclic quotient map.
Adapted from TauCetiProject/TauCeti, Apache-2.0, commit
bfcff79b60964ba7bdb78b952828313686c327ba; the point-class argument
credits Chris Birkbeck's AINTLIB. Only the elliptic-curve consumer is
needed: omit singular-curve cotangent spaces and the general isogeny category.
Dependency: DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> continuation ->
arithmetic automorphy -> Frobenius/inertia -> modular-curve good reduction ->
reverse genus and inertia census -> cyclic modular-polynomial roots ->
explicit odd quotient homomorphism -> norm-induced map of ideal classes. -/
namespace Dubon2026.SourceEllipticClassGroup
noncomputable section
open Polynomial FractionalIdeal
open scoped nonZeroDivisors TensorProduct
theorem moduleInvertible_of_isUnit_fractionalIdeal {R : Type*} [CommRing R]
    {S : Submonoid R} {P : Type*} [CommRing P] [Algebra R P] [IsLocalization S P]
    [FaithfulSMul R P] (I : Ideal R) (hI : IsUnit (I : FractionalIdeal S P)) :
    Module.Invertible R I := by
  let U : (Submodule R P)ˣ := FractionalIdeal.unitsMulEquivSubmodule hI.unit
  have hU : (U : Submodule R P) = (I : FractionalIdeal S P).coeToSubmodule :=
    congrArg FractionalIdeal.coeToSubmodule hI.unit_spec
  have hmap : Submodule.map (Algebra.linearMap R P) I =
      (I : FractionalIdeal S P).coeToSubmodule := by
    rw [FractionalIdeal.coe_coeIdeal, IsLocalization.coeSubmodule]
  let e : I ≃ₗ[R] U :=
    (Submodule.equivMapOfInjective (Algebra.linearMap R P)
      (FaithfulSMul.algebraMap_injective R P) I).trans
      ((LinearEquiv.ofEq _ _ hmap).trans (LinearEquiv.ofEq _ _ hU.symm))
  exact Module.Invertible.congr e.symm


variable {R : Type*} [CommRing R]
theorem nonempty_quotientEquiv (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Invertible R M] (J : Ideal R) [Finite (MaximalSpectrum (R ⧸ J))] :
    Nonempty ((M ⧸ J • (⊤ : Submodule R M)) ≃ₗ[R] R ⧸ J) := by
  let A := R ⧸ J
  let e : A ⊗[R] M ≃ₗ[A] A :=
    (Module.Invertible.free_iff_linearEquiv.mp (inferInstance : Module.Free A (A ⊗[R] M))).some
  exact ⟨(TensorProduct.quotTensorEquivQuotSMul M J).symm.trans (e.restrictScalars R)⟩


theorem smul_top_eq_comap_mul (I J : Ideal R) :
    J • (⊤ : Submodule R I) = Submodule.comap I.subtype (I * J) := by
  ext x
  rw [Submodule.mem_smul_top_iff, Submodule.mem_comap, Submodule.subtype_apply]
  change (x : R) ∈ J * I ↔ (x : R) ∈ I * J
  rw [mul_comm]
theorem nonempty_quotient_comap_mul_linearEquiv_quotient (I J : Ideal R)
    [Module.Invertible R I]
    [Finite (MaximalSpectrum (R ⧸ J))] :
    Nonempty ((I ⧸ Submodule.comap I.subtype (I * J)) ≃ₗ[R] R ⧸ J) := by
  obtain ⟨e⟩ := nonempty_quotientEquiv I J
  exact ⟨(Submodule.quotEquivOfEq _ _ (smul_top_eq_comap_mul I J).symm).trans e⟩

theorem rank_quotient_submoduleOf_tower {R : Type*} {M : Type*} [Field R] [AddCommGroup M]
    [Module R M] {p q r : Submodule R M} (hpq : p ≤ q) (hqr : q ≤ r) :
    Module.rank R (↥r ⧸ p.submoduleOf r) =
      Module.rank R (↥q ⧸ p.submoduleOf q) + Module.rank R (↥r ⧸ q.submoduleOf r) := by
  have hAB : p.submoduleOf r ≤ q.submoduleOf r := Submodule.comap_mono hpq
  set A := p.submoduleOf r with hA
  set f : ↥q →ₗ[R] (↥r ⧸ A) := A.mkQ ∘ₗ Submodule.inclusion hqr with hf
  have hker : LinearMap.ker f = p.submoduleOf q := by
    ext z
    simp [hf, hA, Submodule.submoduleOf, Submodule.inclusion]
  have hrange : LinearMap.range f = (q.submoduleOf r).map A.mkQ := by
    rw [hf, LinearMap.range_comp, Submodule.range_inclusion]
    rfl
  have e₁ : (↥q ⧸ p.submoduleOf q) ≃ₗ[R] ↥((q.submoduleOf r).map A.mkQ) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      ((f.quotKerEquivRange).trans (LinearEquiv.ofEq _ _ hrange))
  have e₂ : ((↥r ⧸ A) ⧸ (q.submoduleOf r).map A.mkQ) ≃ₗ[R] (↥r ⧸ q.submoduleOf r) :=
    Submodule.quotientQuotientEquivQuotient A (q.submoduleOf r) hAB
  have key := Submodule.rank_quotient_add_rank ((q.submoduleOf r).map A.mkQ)
  rw [e₂.rank_eq, ← e₁.rank_eq] at key
  rw [← key, add_comm]

theorem finrank_quotient_mul (K : Type*) [Field K] [Algebra K R] (I J : Ideal R)
    [Module.Invertible R I] [Module.Finite K (R ⧸ I)] [Module.Finite K (R ⧸ J)]
    [Module.Finite K (R ⧸ I * J)] :
    Module.finrank K (R ⧸ I * J) =
      Module.finrank K (R ⧸ I) + Module.finrank K (R ⧸ J) := by
  let : IsArtinianRing (R ⧸ J) := IsArtinianRing.of_finite K (R ⧸ J)
  obtain ⟨eI⟩ := nonempty_quotient_comap_mul_linearEquiv_quotient I J
  let p := (I * J).restrictScalars K
  let q := I.restrictScalars K
  let eTop (L : Submodule K R) :
      ((⊤ : Submodule K R) ⧸ L.submoduleOf ⊤) ≃ₗ[K] R ⧸ L :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.ofTop ⊤ rfl) (by
      rw [LinearEquiv.toLinearMap_ofTop, Submodule.submoduleOf,
        Submodule.map_comap_subtype, top_inf_eq])
  let eIJ := (eTop p).trans (Submodule.Quotient.restrictScalarsEquiv K (I * J))
  let eQ := (eTop q).trans (Submodule.Quotient.restrictScalarsEquiv K I)
  -- The canonical scalar-restriction equivalence preserves ideal carriers and subtype maps.
  let eRestrict : q ≃ₗ[K] I := (I.restrictScalarsEquiv K).restrictScalars K
  have hsub : (p.submoduleOf q).map eRestrict.toLinearMap =
      (Submodule.comap I.subtype (I * J)).restrictScalars K := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    rfl
  let eIK : (q ⧸ p.submoduleOf q) ≃ₗ[K] R ⧸ J :=
    (Submodule.Quotient.equiv _ _ eRestrict hsub).trans
      ((Submodule.Quotient.restrictScalarsEquiv K
        (Submodule.comap I.subtype (I * J))).trans (eI.restrictScalars K))
  have h := rank_quotient_submoduleOf_tower
    (p := p) (q := q) (r := ⊤) (by exact (Ideal.mul_le_right : I * J ≤ I)) le_top
  rw [eIJ.rank_eq, eIK.rank_eq, eQ.rank_eq, add_comm] at h
  simpa only [← Module.finrank_eq_rank, ← Nat.cast_add, Nat.cast_inj] using h


end
end Dubon2026.SourceEllipticClassGroup
