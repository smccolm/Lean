import Dubon2026.AdelicFullFiniteAdmissible

/-! # The actual full finite Hilbert factor has exactly the original algebraic smooth vectors -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original normalized finite orbit core equals the original unnormalized finite cyclic algebraic span. -/
theorem adelicFullFiniteUnitCore_eq_finiteSpan (hf : f ≠ 0) :
    adelicFullFiniteUnitCore f = adelicFiniteCyclicSpan f := by
  have hn : (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast norm_ne_zero_iff.mpr (adelicCyclicHilbertGenerator_ne_zero f hf)
  have he := @scaled_reindexed_orbit_span
    (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding)
    (adelicCyclicHilbertGenerator f) (MulEquiv.refl _) _ hn
  simpa only [adelicFullFiniteUnitCore, adelicFiniteCyclicSpan, adelicCyclicUnitReference, map_smul,
    MulEquiv.refl_apply, MonoidHom.comp_apply] using he

/-- Every actual full finite algebraic cyclic vector is fixed by a genuine open finite adelic subgroup. -/
theorem adelicFiniteCyclicSpan_smooth (x : AdelicCyclicHilbert f) (hx : x ∈ adelicFiniteCyclicSpan f) :
    ∃ J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)),
      IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) ∧
        ∀ g ∈ J, adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding g) x = x := by
  obtain ⟨w, _, he⟩ := adelicFiniteCyclicSpan_preimage f x hx
  obtain ⟨J, _, hJo, hJ⟩ := adelicCyclicHilbert_finite_smooth_core f w
  exact ⟨J, hJo, fun g hg => he ▸ hJ g hg⟩

/-- Every genuine full finite smooth vector in the original complete lowest-weight space already belongs to the actual finite cyclic algebraic span. -/
theorem adelicFiniteLowest_smooth_mem_core (hf : f ≠ 0) (hk : 0 < k)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicRotationWeightSpace f)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hfix : ∀ g ∈ J, adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding g) x = x) :
    x ∈ adelicFiniteCyclicSpan f := by
  let L := J.comap (finiteAdeleGL2Gamma0 N).subtype
  have hL : IsOpen (L : Set (finiteAdeleGL2Gamma0 N)) := hJ.preimage continuous_subtype_val
  have hl : x ∈ adelicSublevelFixedSpace f L := by
    intro a
    exact hfix a.val.val a.property
  have hmem : x ∈ adelicRotationWeightSpace f ⊓ adelicSublevelFixedSpace f L := ⟨hx, hl⟩
  rw [adelicSublevelFixedLowest_eq_algebraic f hf hk L hL] at hmem
  exact hmem.1

/-- In the genuine full finite Hilbert factor, actual finite adelic smoothness is equivalent to original algebraic cyclic membership. -/
theorem adelicFullFiniteHilbert_smooth_iff_core (hf : f ≠ 0) (hk : 0 < k)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicRotationWeightSpace f) :
    (∃ J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)),
      IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) ∧
        ∀ g ∈ J, adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding g) x = x) ↔
      x ∈ adelicFullFiniteUnitCore f := by
  rw [adelicFullFiniteUnitCore_eq_finiteSpan f hf]
  exact ⟨fun ⟨J, hJ, hfix⟩ => adelicFiniteLowest_smooth_mem_core f hf hk x hx J hJ hfix,
    adelicFiniteCyclicSpan_smooth f x⟩

end
end Dubon2026
