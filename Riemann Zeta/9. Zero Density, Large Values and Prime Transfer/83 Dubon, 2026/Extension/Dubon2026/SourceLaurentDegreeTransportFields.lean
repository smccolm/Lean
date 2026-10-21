import Dubon2026.SourceOriginalModularFunctionField
import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.AlgebraTower
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Tactic

/-! DUB-17/18 -> numerical modular genus -> exact all-level j-map degree
-> transport from the rational original field to its geometric coefficient
extension. Literal Laurent coefficients preserve linear independence.
Polynomial denominator clearing and the existing finite original extension
then preserve the coordinate degree, allowing rational prime-power proofs
to serve the actual algebraically closed coefficient field.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_GeometricBaseChange.lean and
P2M/Sol/S_ModularCurve_relfinrank_laurentBaseChange.lean.
Only the finite degree-transport chain is selected; external global instance
changes, proof options and the infinite-dimensional generalization are omitted.
-/
namespace Dubon2026.SourceFunctionField.DegreeTransport
noncomputable section
open IntermediateField Polynomial

variable (L : Type*) [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (t : LaurentSeries ℚ)

/-- The rational coordinate field inside the original rational Laurent field. -/
abbrev K₀ : IntermediateField ℚ (LaurentSeries ℚ) := IntermediateField.adjoin ℚ ({t} : Set (LaurentSeries ℚ))

/-- The corresponding coordinate field after coefficient extension. -/
abbrev K : IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L ({coeffEmb L t} : Set (LaurentSeries L))

variable {F₀ t}

theorem K₀_le (ht : t ∈ F₀) : K₀ t ≤ F₀ :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ht)

theorem K_le (ht : t ∈ F₀) : K L t ≤ laurentBaseChange L F₀ :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (coeffEmb_mem_laurentBaseChange L ht))

theorem coeffEmb_aeval (r : ℚ[X]) :
    coeffEmb L (aeval t r) = aeval (coeffEmb L t) (r.map (algebraMap ℚ L)) := by
  simp only [aeval_def, eval₂_map, hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

theorem coeffEmb_mem_K {x : LaurentSeries ℚ} (hx : x ∈ K₀ t) : coeffEmb L x ∈ K L t := by
  rw [mem_adjoin_simple_iff] at hx ⊢
  obtain ⟨r, s, rfl⟩ := hx
  exact ⟨r.map (algebraMap ℚ L), s.map (algebraMap ℚ L), by rw [map_div₀, coeffEmb_aeval, coeffEmb_aeval]⟩

variable (F₀ t) in

/-- The original rational field viewed over its coordinate subfield. -/
abbrev E₀ (ht : t ∈ F₀) : IntermediateField (K₀ t) (LaurentSeries ℚ) := extendScalars (K₀_le ht)

variable (F₀ t) in

/-- The coefficient-extended field viewed over its coordinate subfield. -/
abbrev E (ht : t ∈ F₀) : IntermediateField (K L t) (LaurentSeries L) := extendScalars (K_le L ht)

/-- The literal coefficient embedding on coordinate fields. -/
def φ : K₀ t →+* K L t := (coeffEmb L).restrict _ _ fun _ hx => coeffEmb_mem_K L hx

/-- The literal coefficient embedding on the original relative fields. -/
def ψ (ht : t ∈ F₀) : E₀ F₀ t ht →+* E L F₀ t ht :=
  (coeffEmb L).restrict _ _ fun _ hx => coeffEmb_mem_laurentBaseChange L ((mem_extendScalars _).mp hx)

theorem coe_φ (x : K₀ t) : (φ L x : LaurentSeries L) = coeffEmb L x := rfl
theorem coe_ψ (ht : t ∈ F₀) (x : E₀ F₀ t ht) : (ψ L ht x : LaurentSeries L) = coeffEmb L x := rfl

theorem ψ_compat (ht : t ∈ F₀) :
    (algebraMap (K L t) (E L F₀ t ht)).comp (φ L) = (ψ L ht).comp (algebraMap (K₀ t) (E₀ F₀ t ht)) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  rfl

theorem isAlgebraic_coeffEmb (ht : t ∈ F₀) [FiniteDimensional (K₀ t) (E₀ F₀ t ht)] (f : LaurentSeries ℚ) (hf : f ∈ F₀) :
    IsAlgebraic (K L t) (coeffEmb L f) := by
  have h1 : IsIntegral (K₀ t) (⟨f, (mem_extendScalars _).mpr hf⟩ : E₀ F₀ t ht) := Algebra.IsIntegral.isIntegral _
  have h2 := h1.map_of_comp_eq (φ L) (ψ L ht) (ψ_compat L ht)
  have h3 : IsIntegral (K L t) ((ψ L ht ⟨f, (mem_extendScalars _).mpr hf⟩ : E L F₀ t ht) : LaurentSeries L) := h2.algebraMap
  exact h3.isAlgebraic

theorem laurentBaseChange_eq_adjoin : laurentBaseChange L F₀ = IntermediateField.adjoin L (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ))) := rfl

theorem restrictScalars_adjoin_K (ht : t ∈ F₀) :
    (IntermediateField.adjoin (K L t) (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ)))).restrictScalars L
      = laurentBaseChange L F₀ := by
  have h1 : IntermediateField.adjoin (K L t) (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ))) ≤ E L F₀ t ht :=
    adjoin_le_iff.mpr (subset_adjoin L _)
  have h2 : laurentBaseChange L F₀ ≤
      (IntermediateField.adjoin (K L t) (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ)))).restrictScalars L :=
    adjoin_le_iff.mpr (subset_adjoin (K L t) _)
  exact le_antisymm (fun x hx => h1 hx) h2

theorem closure_image_eq :
    (Submonoid.closure (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ))) : Set (LaurentSeries L))
      = coeffEmb L '' (F₀ : Set (LaurentSeries ℚ)) := by
  have : (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ))) = ((F₀.toSubfield.map (coeffEmb L)).toSubmonoid : Set (LaurentSeries L)) := by
    ext x; simp
  rw [this, Submonoid.closure_eq]

end
end Dubon2026.SourceFunctionField.DegreeTransport
