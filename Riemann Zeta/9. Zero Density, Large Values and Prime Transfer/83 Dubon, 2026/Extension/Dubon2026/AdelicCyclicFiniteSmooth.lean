import Dubon2026.AdelicCyclicRepresentation
import Dubon2026.FiniteAdelicCompactLevel

/-! # Genuine finite-place smoothness of the original algebraic adelic cusp representation -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix UpperHalfPlane CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

/-- The actual finite adelic general-linear group embeds in the full canonical group with real coordinate one. -/
def rationalAdelicFiniteGL2Embedding :
    GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) →* RationalAdelicGL2 where
  toFun a := rationalAdelicGL2RealFiniteEquiv.symm (1, a)
  map_one' := map_one rationalAdelicGL2RealFiniteEquiv.symm
  map_mul' a b := by
    simpa only [Prod.mk_mul_mk, one_mul] using
      map_mul rationalAdelicGL2RealFiniteEquiv.symm (1, a) (1, b)

/-- The original finite group embedding has exactly the prescribed genuine real and finite coordinates. -/
theorem rationalAdelicFiniteGL2Embedding_coordinates
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    rationalAdelicGL2RealFiniteEquiv (rationalAdelicFiniteGL2Embedding a) = (1, a) :=
  rationalAdelicGL2RealFiniteEquiv.apply_symm_apply _

/-- Conjugating an actual finite group element through a full adelic point uses exactly the finite coordinate of that point. -/
theorem rationalAdelicFiniteGL2Embedding_mul
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (g : RationalAdelicGL2) :
    rationalAdelicFiniteGL2Embedding a * g = g * rationalAdelicFiniteGL2Embedding
      ((rationalAdelicGL2RealFiniteEquiv g).2⁻¹ * a * (rationalAdelicGL2RealFiniteEquiv g).2) := by
  apply rationalAdelicGL2RealFiniteEquiv.injective
  simp only [map_mul, rationalAdelicFiniteGL2Embedding_coordinates, Prod.mk_mul_mk]
  apply Prod.ext
  · simp
  · simp [mul_assoc]

/-- The actual conjugate of the original finite level subgroup at a genuine finite group point. -/
def finiteAdelicConjugateLevel (N : ℕ)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :=
  (finiteAdeleGL2Gamma0 N).comap (MulAut.conj a⁻¹).toMonoidHom

/-- Original conjugate-level membership is precisely the literal conjugated matrix condition. -/
theorem mem_finiteAdelicConjugateLevel (N : ℕ)
    (a b : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    b ∈ finiteAdelicConjugateLevel N a ↔ a⁻¹ * b * a ∈ finiteAdeleGL2Gamma0 N := by
  simp only [finiteAdelicConjugateLevel, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]

/-- Every actual conjugate finite level group is compact and open at nonzero level. -/
theorem finiteAdelicConjugateLevel_compact_open (N : ℕ) [NeZero N]
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    IsCompact (finiteAdelicConjugateLevel N a : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) ∧
      IsOpen (finiteAdelicConjugateLevel N a : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) := by
  let e := (Homeomorph.mulLeft a⁻¹).trans (Homeomorph.mulRight a)
  have he : (finiteAdelicConjugateLevel N a : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) =
      e ⁻¹' (finiteAdeleGL2Gamma0 N : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) := by
    ext b
    exact mem_finiteAdelicConjugateLevel N a b
  rw [he]
  exact ⟨e.isCompact_preimage.mpr (finiteAdeleGL2Gamma0_isCompact N),
    (finiteAdeleGL2Gamma0_isOpen N).preimage e.continuous⟩

/-- Each original right translate is fixed by its actual conjugate finite level group. -/
theorem canonicalAdelicGL2CuspLift_translate_finite_level (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (h g : RationalAdelicGL2)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (ha : a ∈ finiteAdelicConjugateLevel N (rationalAdelicGL2RealFiniteEquiv h).2) :
    canonicalAdelicGL2CuspLift N k f ((g * rationalAdelicFiniteGL2Embedding a) * h) =
      canonicalAdelicGL2CuspLift N k f (g * h) := by
  rw [mul_assoc, rationalAdelicFiniteGL2Embedding_mul, ← mul_assoc]
  exact canonicalAdelicGL2CuspLift_level_invariant N f (g * h)
    ⟨_, (mem_finiteAdelicConjugateLevel N _ a).mp ha⟩

/-- Every genuine algebraic adelic cyclic vector is fixed by an actual compact open finite subgroup; no smoothness is assumed. -/
theorem adelicLiftCyclic_finite_smooth (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) {v : RationalAdelicGL2 → ℂ}
    (hv : v ∈ (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    ∃ K : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)),
      IsCompact (K : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) ∧
      IsOpen (K : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) ∧
      ∀ g : RationalAdelicGL2, ∀ a ∈ K, v (g * rationalAdelicFiniteGL2Embedding a) = v g := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨hc, ho⟩ := finiteAdelicConjugateLevel_compact_open N (rationalAdelicGL2RealFiniteEquiv h).2
    refine ⟨finiteAdelicConjugateLevel N (rationalAdelicGL2RealFiniteEquiv h).2, hc, ho, ?_⟩
    intro g a ha
    exact canonicalAdelicGL2CuspLift_translate_finite_level N f h g a ha
  | zero =>
    exact ⟨finiteAdeleGL2Gamma0 N, finiteAdeleGL2Gamma0_isCompact N,
      finiteAdeleGL2Gamma0_isOpen N, fun _ _ _ => rfl⟩
  | add x y hx hy hix hiy =>
    obtain ⟨K, hKc, hKo, hK⟩ := hix
    obtain ⟨L, hLc, hLo, hL⟩ := hiy
    refine ⟨K ⊓ L, hKc.inter_right hLc.isClosed, hKo.inter hLo, ?_⟩
    intro g a ha
    simp only [Pi.add_apply, hK g a ha.1, hL g a ha.2]
  | smul c x hx hix =>
    obtain ⟨K, hKc, hKo, hK⟩ := hix
    refine ⟨K, hKc, hKo, ?_⟩
    intro g a ha
    simp only [Pi.smul_apply, hK g a ha]

end
end Dubon2026
