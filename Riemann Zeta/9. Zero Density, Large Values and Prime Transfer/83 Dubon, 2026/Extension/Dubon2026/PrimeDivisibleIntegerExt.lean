import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-! # Integer Ext for prime-field coefficients and prime-divisible targets

This is the underlying integer-module acyclicity needed for the arithmetic
S-unit Hom/cohomology comparison in DUB-17's global-duality sequence. It does
not itself compare arithmetic continuous cohomology with equivariant Ext.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Abelian

variable (I : Type) (q : ℕ)

/-- The original free integer module, its q-multiples, and its actual quotient. -/
def primeFreeReductionShortComplex : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.moduleCatMk
    (LinearMap.lsmul ℤ (I →₀ ℤ) q)
    (LinearMap.range (LinearMap.lsmul ℤ (I →₀ ℤ) q)).mkQ
    (LinearMap.range_mkQ_comp _)

/-- Multiplication and reduction give a genuine short exact sequence for nonzero q. -/
theorem primeFreeReductionShortComplex_shortExact (hq : q ≠ 0) :
    (primeFreeReductionShortComplex I q).ShortExact := by
  have hinj : Function.Injective (LinearMap.lsmul ℤ (I →₀ ℤ) q) := by
    intro x y h
    ext i
    have hc := congrArg (fun z : I →₀ ℤ => z i) h
    exact mul_left_cancel₀ (show (q : ℤ) ≠ 0 by exact_mod_cast hq) hc
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (Submodule.ker_mkQ _).symm
  · exact (ModuleCat.mono_iff_injective _).mpr hinj
  · exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

variable (N : Type) [AddCommGroup N] [Module ℤ N]
  (hqN : Function.Surjective (fun x : N => (q : ℤ) • x))

include hqN in
/-- q-divisibility lifts every integer-linear map from the free presentation across q-multiplication. -/
theorem primeDivisible_free_precomp_surjective
    (f : (I →₀ ℤ) →ₗ[ℤ] N) :
    ∃ g : (I →₀ ℤ) →ₗ[ℤ] N, g.comp (LinearMap.lsmul ℤ (I →₀ ℤ) q) = f := by
  classical
  choose v hv using fun i : I => hqN (f (Finsupp.single i 1))
  let g : (I →₀ ℤ) →ₗ[ℤ] N := (Finsupp.basisSingleOne : Module.Basis I ℤ (I →₀ ℤ)).constr ℕ v
  refine ⟨g, ?_⟩
  apply (Finsupp.basisSingleOne : Module.Basis I ℤ (I →₀ ℤ)).ext
  intro i
  rw [LinearMap.comp_apply, LinearMap.lsmul_apply, g.map_smul]
  rw [show g ((Finsupp.basisSingleOne : Module.Basis I ℤ (I →₀ ℤ)) i) = v i from
    Module.Basis.constr_basis _ ℕ v i]
  exact (int_smul_eq_zsmul (inferInstance : Module ℤ N) (q : ℤ) (v i)).trans (hv i)

include hqN in
/-- Positive integer Ext vanishes for the actual mod-q free quotient and a q-divisible target. -/
theorem primeDivisible_modN_ext_eq_zero (hq : q ≠ 0) (n : ℕ)
    (x : Ext (ModuleCat.of ℤ (ModN (I →₀ ℤ) q)) (ModuleCat.of ℤ N) (n + 1)) :
    x = 0 := by
  let S := primeFreeReductionShortComplex I q
  have hS := primeFreeReductionShortComplex_shortExact I q hq
  haveI : Module.Free ℤ S.X₁ := inferInstanceAs (Module.Free ℤ (I →₀ ℤ))
  haveI : Module.Free ℤ S.X₂ := inferInstanceAs (Module.Free ℤ (I →₀ ℤ))
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ hS (ModuleCat.of ℤ N) x
    (Ext.eq_zero_of_projective _) (add_comm 1 n)
  cases n with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective S.X₁ (ModuleCat.of ℤ N)).surjective y
    obtain ⟨g, hg⟩ := primeDivisible_free_precomp_surjective I q N hqN f.hom
    have hf : S.f ≫ ModuleCat.ofHom g = f := ModuleCat.hom_ext hg
    rw [← hf, ← Ext.mk₀_comp_mk₀] at hy
    exact hy.symm.trans (hS.extClass_comp_assoc (Ext.mk₀ (ModuleCat.ofHom g)))
  | succ n =>
    rw [Ext.eq_zero_of_projective y, Ext.comp_zero] at hy
    exact hy.symm

include hqN in
/-- Every positive integer Ext group from the original prime-field module to a q-divisible
target vanishes, using an explicit free mod-q presentation and its actual basis equivalence. -/
theorem primeDivisible_primeField_ext_eq_zero [Fact q.Prime]
    (A : Type) [AddCommGroup A] [Module (ZMod q) A] (n : ℕ)
    (x : Ext (ModuleCat.of ℤ A) (ModuleCat.of ℤ N) (n + 1)) : x = 0 := by
  let I := Module.Free.ChooseBasisIndex (ZMod q) A
  let b : Module.Basis I (ZMod q) A := Module.Free.chooseBasis (ZMod q) A
  let c : Module.Basis I (ZMod q) (ModN (I →₀ ℤ) q) := ModN.basis Finsupp.basisSingleOne
  let e : A ≃ₗ[ℤ] ModN (I →₀ ℤ) q := (b.repr.trans c.repr.symm).restrictScalars ℤ
  have hx : (Ext.mk₀ e.toModuleIso.inv).comp x (zero_add (n + 1)) = 0 :=
    primeDivisible_modN_ext_eq_zero I q N hqN (Fact.out : q.Prime).ne_zero n _
  have h := congrArg
    (fun y => (Ext.mk₀ e.toModuleIso.hom).comp y (zero_add (n + 1))) hx
  simpa only [Ext.mk₀_comp_mk₀_assoc, CategoryTheory.Iso.hom_inv_id,
    Ext.mk₀_id_comp, Ext.comp_zero] using h

end
end Dubon2026
