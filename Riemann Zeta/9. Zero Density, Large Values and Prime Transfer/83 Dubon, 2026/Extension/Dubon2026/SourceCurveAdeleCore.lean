import Dubon2026.SourceCurveRiemannRochSpace
import Mathlib.LinearAlgebra.Isomorphisms

/-! DUB-17/18 -> original cusp-form lower dimension bound -> regular
differential dimension -> the unresolved function-field Riemann--Roch
theorem. This is its exact source repartition model, needed for the local
quotient dimensions, finite index formula and residue duality. Adapted
from Def_AlgebraicCurve_AdelicIndex, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Principal
repartitions are proved bounded using actual principal finite support.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Families of actual field elements satisfying the divisor bound at every place. -/
def adeleBdd (D : Divisor K F) : Submodule K (Place K F → F) where
  carrier := {α | ∀ v : Place K F, v.adicValuation (α v) ≤ WithZero.exp (D v)}
  add_mem' := fun {α β} hα hβ v =>
    (v.adicValuation.map_add (α v) (β v)).trans (max_le (hα v) (hβ v))
  zero_mem' := fun v => by rw [Pi.zero_apply, Valuation.map_zero]; exact zero_le'
  smul_mem' := fun c α hα v => by
    rw [Pi.smul_apply, Algebra.smul_def, Valuation.map_mul]
    calc v.adicValuation (algebraMap K F c) * v.adicValuation (α v)
        ≤ 1 * v.adicValuation (α v) := by gcongr; exact v.adicValuation_algebraMap_le_one c
      _ = v.adicValuation (α v) := one_mul _
      _ ≤ WithZero.exp (D v) := hα v

variable {D E : Divisor K F}

@[simp]
theorem mem_adeleBdd {α : Place K F → F} :
    α ∈ adeleBdd D ↔ ∀ v : Place K F, v.adicValuation (α v) ≤ WithZero.exp (D v) := Iff.rfl

theorem adeleBdd_mono (hDE : D ≤ E) : adeleBdd D ≤ adeleBdd E := fun _ hα v =>
  (hα v).trans (WithZero.exp_le_exp.mpr (hDE v))

variable (K F) in

/-- The global field embedded as constant families over all places. -/
def diagonalHom : F →ₗ[K] (Place K F → F) where
  toFun f := fun _ => f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem diagonalHom_apply (f : F) (v : Place K F) : diagonalHom K F f v = f := rfl

theorem diagonalHom_injective [Nonempty (Place K F)] :
    Function.Injective (diagonalHom K F) := fun f g h => by
  simpa using congrFun h (Classical.arbitrary (Place K F))

theorem diagonal_mem_adeleBdd_iff {f : F} :
    diagonalHom K F f ∈ adeleBdd D ↔ f ∈ LSpace D := by
  rfl

variable (K F) in

/-- The source repartition space: the union of all finite divisor bounds. -/
def adeleSpace : Submodule K (Place K F → F) := ⨆ D : Divisor K F, adeleBdd D

theorem adeleBdd_le_adeleSpace : adeleBdd D ≤ adeleSpace K F := le_iSup adeleBdd D

theorem diagonal_mem_adeleSpace [HasPrincipalDivisors K F] (f : F) :
    diagonalHom K F f ∈ adeleSpace K F := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero]; exact (adeleSpace K F).zero_mem
  · obtain ⟨P, hPord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
    refine adeleBdd_le_adeleSpace (D := -P) ?_
    intro v
    rw [diagonalHom_apply,
      show ((-P : Divisor K F) v) = -v.ord f by rw [Finsupp.neg_apply, hPord v]]
    exact le_of_eq (by rw [Place.ord, neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)])

variable (K F) in

/-- The subspace of global field elements inside the families of local entries. -/
def globalSub : Submodule K (Place K F → F) := LinearMap.range (diagonalHom K F)

theorem diagonal_mem_globalSub (f : F) : diagonalHom K F f ∈ globalSub K F :=
  LinearMap.mem_range_self _ f

theorem map_diagonal_lSpace (D : Divisor K F) :
    (LSpace D).map (diagonalHom K F) = adeleBdd D ⊓ globalSub K F := by
  ext α
  rw [Submodule.mem_map, Submodule.mem_inf]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨diagonal_mem_adeleBdd_iff.mpr hf, diagonal_mem_globalSub f⟩
  · rintro ⟨hbdd, hglob⟩
    obtain ⟨f, hf⟩ := LinearMap.mem_range.mp hglob
    exact ⟨f, diagonal_mem_adeleBdd_iff.mp (by rw [hf]; exact hbdd), hf⟩

/-- The literal divisor space identified with bounded global repartitions. -/
def lSpaceEquivAdeleBddInfGlobal [Nonempty (Place K F)] (D : Divisor K F) :
    LSpace D ≃ₗ[K] (adeleBdd D ⊓ globalSub K F : Submodule K (Place K F → F)) :=
  (Submodule.equivMapOfInjective (diagonalHom K F) diagonalHom_injective (LSpace D)).trans
    (LinearEquiv.ofEq _ _ (map_diagonal_lSpace D))

theorem finrank_adeleBdd_inf_global_eq_ell [Nonempty (Place K F)] (D : Divisor K F) :
    Module.finrank K (adeleBdd D ⊓ globalSub K F : Submodule K (Place K F → F)) = Module.finrank K (LSpace D) :=
  ((lSpaceEquivAdeleBddInfGlobal D).finrank_eq).symm


end
end Dubon2026.SourceCurve
