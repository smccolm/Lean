/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourceModularBinaryForms
import Dubon2026.SourceModularCuspDivisors
import Mathlib.RepresentationTheory.Coinvariants

/-! The actual finite integral module of modular symbols.
Adapted from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5.
Reuses the existing original homogeneous coefficient action and its monomial basis.
DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 -> modular Galois association ->
integral Hecke algebra finiteness through periods -> finite integral modular
symbols. Manin's cusp generation, the actual coefficient action and finite index
supply finiteness without a lattice or finite-generation hypothesis. The actual
cusp-form period map, its injectivity and Hecke compatibility are assembled in SourceOriginalIntegralHecke.
-/

open MonoidAlgebra MulOpposite MvPolynomial Representation TensorProduct
open Matrix.SpecialLinearGroup ModularGroup OnePoint
open scoped MatrixGroups MonoidAlgebra

namespace Dubon2026
namespace SourceModularSymbols
variable {R : Type*} [CommRing R] {w : ℕ}

variable (R w) in
/-- The diagonal representation of `SL(2, ℤ)` on `Div⁰(ℙ¹(ℚ)) ⊗_R Sym^w(R²)`. -/
noncomputable def symbolRep :
    Representation R SL(2, ℤ) (degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :=
  (degreeZeroRep R).tprod (sourceModularBinaryFormSLRep R w)

@[simp]
theorem symbolRep_tmul (g : SL(2, ℤ)) (D : degreeZero R)
    (P : homogeneousSubmodule (Fin 2) R w) :
    symbolRep R w g (D ⊗ₜ P) = degreeZeroRep R g D ⊗ₜ sourceModularBinaryFormSLRep R w g P := by
  simp [symbolRep]

/-- Two linear maps out of `Div⁰(ℙ¹(ℚ)) ⊗_R Sym^w(R²)` are equal as soon as they agree on the
unimodular symbols `([g∞] - [g0]) ⊗ P`, `g ∈ SL(2, ℤ)`, which span by Manin's lemma
(`Dubon2026.SourceModularSymbols.span_degreeZeroRep_eq_top`). -/
theorem hom_ext_unimodular {M : Type*} [AddCommMonoid M] [Module R M]
    {L₁ L₂ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R] M}
    (h : ∀ (g : SL(2, ℤ)) (P : homogeneousSubmodule (Fin 2) R w),
      L₁ (⟨_, single_sub_single_mem_degreeZero (mapGL ℚ g • ∞)
        (mapGL ℚ g • ((0 : ℚ) : OnePoint ℚ))⟩ ⊗ₜ P) =
      L₂ (⟨_, single_sub_single_mem_degreeZero (mapGL ℚ g • ∞)
        (mapGL ℚ g • ((0 : ℚ) : OnePoint ℚ))⟩ ⊗ₜ P)) :
    L₁ = L₂ :=
  TensorProduct.ext <| LinearMap.ext_on_range span_degreeZeroRep_eq_top fun g ↦
    LinearMap.ext fun P ↦ by
      simpa only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, degreeZeroRep_apply,
        degreeZeroGLRep_single_sub_single] using h g P

end SourceModularSymbols

variable (R : Type*) [CommRing R]

/-- The **module of modular symbols** `𝕄_w(Γ; R) = (Div⁰(ℙ¹(ℚ)) ⊗_R Sym^w(R²))_Γ` of weight
`w + 2` for a subgroup `Γ ≤ SL(2, ℤ)`, with coefficients in `R`: the `Γ`-coinvariants of the
degree-zero divisors on the cusps tensored with the binary forms of degree `w`.

This is an abbreviation for the coinvariants, so that their universal property
(`Representation.Coinvariants.lift`, `Representation.Coinvariants.hom_ext`) applies directly. -/
abbrev SourceModularSymbols (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Type _ :=
  Representation.Coinvariants
    (V := SourceModularSymbols.degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w)
    ((SourceModularSymbols.symbolRep R w).comp Γ.subtype)

namespace SourceModularSymbols

variable {R} (Γ : Subgroup SL(2, ℤ)) {w : ℕ}

/-- The modular symbol `{α, β} ⊗ P ∈ 𝕄_w(Γ; R)`, the class of `([α] - [β]) ⊗ P`, as an `R`-linear
map in the binary form `P`. -/
noncomputable def symbol (α β : OnePoint ℚ) :
    homogeneousSubmodule (Fin 2) R w →ₗ[R] SourceModularSymbols R Γ w :=
  Coinvariants.mk _ ∘ₗ TensorProduct.mk R _ _
    ⟨_, single_sub_single_mem_degreeZero α β⟩

-- Low priority, so that `symbol_mapGL_smul` fires before the symbol is unfolded.
@[simp low]
theorem symbol_apply (α β : OnePoint ℚ) (P : homogeneousSubmodule (Fin 2) R w) :
    symbol (R := R) (w := w) Γ α β P =
      Coinvariants.mk _
        (⟨_, single_sub_single_mem_degreeZero α β⟩ ⊗ₜ[R] P) := by
  simp [symbol]

@[simp]
theorem symbol_self (α : OnePoint ℚ) :
    symbol (R := R) (w := w) Γ α α = (0 : homogeneousSubmodule (Fin 2) R w →ₗ[R] SourceModularSymbols R Γ w) := by
  ext P
  have h :
      (⟨_, single_sub_single_mem_degreeZero α α⟩ : degreeZero R) = 0 := by
    ext1
    simp
  rw [symbol_apply, h, zero_tmul, map_zero, LinearMap.zero_apply]

/-- Modular symbols are additive in the pair of cusps: `{α, β} + {β, γ} = {α, γ}`. -/
@[simp]
theorem symbol_add_symbol (α β γ : OnePoint ℚ) :
    symbol (R := R) (w := w) Γ α β + symbol (R := R) (w := w) Γ β γ =
      (symbol (R := R) (w := w) Γ α γ : homogeneousSubmodule (Fin 2) R w →ₗ[R] SourceModularSymbols R Γ w) := by
  ext P
  have h : (⟨_, single_sub_single_mem_degreeZero α β⟩ : degreeZero R) +
      ⟨_, single_sub_single_mem_degreeZero β γ⟩ =
        ⟨_, single_sub_single_mem_degreeZero α γ⟩ := by
    ext1
    simp
  simp only [LinearMap.add_apply, symbol_apply, ← map_add, ← add_tmul, h]

theorem symbol_swap (α β : OnePoint ℚ) :
    symbol (R := R) (w := w) Γ β α =
      -(symbol (R := R) (w := w) Γ α β : homogeneousSubmodule (Fin 2) R w →ₗ[R] SourceModularSymbols R Γ w) := by
  rw [eq_neg_iff_add_eq_zero, add_comm, symbol_add_symbol, symbol_self]

/-- **The `Γ`-relation.** For `γ ∈ Γ`, `{γα, γβ} ⊗ P = {α, β} ⊗ (P ∣ γ)`. -/
@[simp]
theorem symbol_mapGL_smul {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    symbol (R := R) (w := w) Γ (mapGL ℚ γ • α) (mapGL ℚ γ • β) P =
      symbol (R := R) (w := w) Γ α β (sourceModularBinaryFormRep R w (op (γ : Matrix (Fin 2) (Fin 2) ℤ)) P) := by
  rw [symbol_apply, symbol_apply, ← Coinvariants.mk_self_apply _ (⟨γ, hγ⟩ : Γ)
    ((⟨_, single_sub_single_mem_degreeZero α β⟩ : degreeZero R) ⊗ₜ[R]
      sourceModularBinaryFormRep R w (op (γ : Matrix (Fin 2) (Fin 2) ℤ)) P)]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, symbolRep_tmul,
    sourceModularBinaryFormSLRep_right_cancel]
  rw [degreeZeroRep_apply, degreeZeroGLRep_single_sub_single]

/-- A translate `hD ⊗ P`, for `h ∈ Γ`, is the translate `D ⊗ (P ∣ h)` in `𝕄_w(Γ; R)`. -/
private theorem mk_degreeZeroRep_tmul {h : SL(2, ℤ)} (hh : h ∈ Γ) (D : degreeZero R)
    (P : homogeneousSubmodule (Fin 2) R w) :
    Coinvariants.mk ((symbolRep R w).comp Γ.subtype) (degreeZeroRep R h D ⊗ₜ P) =
      Coinvariants.mk _ (D ⊗ₜ sourceModularBinaryFormRep R w (op (h : Matrix (Fin 2) (Fin 2) ℤ)) P) := by
  rw [← Coinvariants.mk_self_apply _ (⟨h, hh⟩ : Γ) (D ⊗ₜ _)]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, symbolRep_tmul,
    sourceModularBinaryFormSLRep_right_cancel]

/-- The classes of the translates `g([∞] - [0]) ⊗ P` span `𝕄_w(Γ; R)`. -/
theorem span_mk_degreeZeroRep_tmul_eq_top :
    Submodule.span R (Set.image2
      (fun D P ↦ Coinvariants.mk ((symbolRep R w).comp Γ.subtype) (D ⊗ₜ[R] P))
      (Set.range fun g : SL(2, ℤ) ↦ degreeZeroRep R g
        ⟨_, single_sub_single_mem_degreeZero ∞
          ((0 : ℚ) : OnePoint ℚ)⟩)
      Set.univ) = ⊤ := by
  have h := Submodule.map₂_span_span R (TensorProduct.mk R (degreeZero R)
    (homogeneousSubmodule (Fin 2) R w)) (Set.range fun g : SL(2, ℤ) ↦ degreeZeroRep R g
      ⟨_, single_sub_single_mem_degreeZero ∞
        ((0 : ℚ) : OnePoint ℚ)⟩) Set.univ
  rw [span_degreeZeroRep_eq_top, Submodule.span_univ, TensorProduct.map₂_mk_top_top_eq_top] at h
  have himage : Set.image2
      (fun D P ↦ Coinvariants.mk ((symbolRep R w).comp Γ.subtype) (D ⊗ₜ[R] P))
      (Set.range fun g : SL(2, ℤ) ↦ degreeZeroRep R g
        ⟨_, single_sub_single_mem_degreeZero ∞
          ((0 : ℚ) : OnePoint ℚ)⟩) Set.univ =
      Coinvariants.mk _ '' Set.image2 (fun D P ↦ TensorProduct.mk R _ _ D P)
        (Set.range fun g : SL(2, ℤ) ↦ degreeZeroRep R g
          ⟨_, single_sub_single_mem_degreeZero ∞
            ((0 : ℚ) : OnePoint ℚ)⟩) Set.univ := by
    rw [Set.image_image2]
    rfl
  rw [himage, ← Submodule.map_span, ← h, Submodule.map_top, LinearMap.range_eq_top]
  exact Coinvariants.mk_surjective _

/-- The modular symbols `{α, β} ⊗ P` span `𝕄_w(Γ; R)`. -/
theorem span_symbol_eq_top :
    Submodule.span R
      (Set.range fun x : OnePoint ℚ × OnePoint ℚ × homogeneousSubmodule (Fin 2) R w ↦
        symbol (R := R) (w := w) Γ x.1 x.2.1 x.2.2) = ⊤ := by
  refine eq_top_iff.2 ((span_mk_degreeZeroRep_tmul_eq_top Γ).symm.le.trans
    (Submodule.span_mono ?_))
  rintro _ ⟨_, ⟨g, rfl⟩, P, -, rfl⟩
  refine ⟨(mapGL ℚ g • ∞, mapGL ℚ g • (0 : ℚ), P), ?_⟩
  dsimp only
  rw [symbol_apply, degreeZeroRep_apply, degreeZeroGLRep_single_sub_single]

/-- **Finiteness of modular symbols.** For a subgroup `Γ` of finite index in `SL(2, ℤ)`, the
module of modular symbols `𝕄_w(Γ; R)` is a finitely generated `R`-module. -/
instance instModuleFinite [Γ.FiniteIndex] : Module.Finite R (SourceModularSymbols R Γ w) := by
  letI : Module.Finite R (homogeneousSubmodule (Fin 2) R w) :=
    (sourceModularBinaryForm_finite_free (R := R) (w := w)).1
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := R) (M := homogeneousSubmodule (Fin 2) R w)
  let e : degreeZero R := ⟨_, single_sub_single_mem_degreeZero ∞
    ((0 : ℚ) : OnePoint ℚ)⟩
  -- The symbols `r⁻¹{∞, 0} ⊗ bᵢ`, for `r` running over representatives of `SL(2, ℤ) ⧸ Γ`.
  let f : (SL(2, ℤ) ⧸ Γ) × Fin n → SourceModularSymbols R Γ w := fun x ↦
    Coinvariants.mk _ (degreeZeroRep R x.1.out⁻¹ e ⊗ₜ b x.2)
  refine ⟨(Submodule.fg_def).2 ⟨Set.range f, Set.finite_range f, eq_top_iff.2 ?_⟩⟩
  rw [← span_mk_degreeZeroRep_tmul_eq_top Γ, Submodule.span_le]
  rintro _ ⟨_, ⟨g, rfl⟩, P, -, rfl⟩
  -- Write `g = (g * r) * r⁻¹` with `g * r ∈ Γ`, where `r` represents the coset `g⁻¹ Γ`.
  obtain ⟨h, hr⟩ := QuotientGroup.mk_out_eq_mul Γ g⁻¹
  have hgr : g * (QuotientGroup.mk g⁻¹ : SL(2, ℤ) ⧸ Γ).out ∈ Γ := by
    rw [hr, ← mul_assoc, mul_inv_cancel, one_mul]
    exact h.2
  dsimp only
  rw [← mul_inv_cancel_right g (QuotientGroup.mk g⁻¹ : SL(2, ℤ) ⧸ Γ).out, map_mul,
    Module.End.mul_apply, mk_degreeZeroRep_tmul Γ hgr]
  -- The remaining class is linear in the binary form, which lies in the span of the `bᵢ`.
  let ψ : homogeneousSubmodule (Fin 2) R w →ₗ[R] SourceModularSymbols R Γ w :=
    Coinvariants.mk _ ∘ₗ TensorProduct.mk R _ _
      (degreeZeroRep R (QuotientGroup.mk g⁻¹ : SL(2, ℤ) ⧸ Γ).out⁻¹ e)
  have hψ : ψ '' Set.range b ⊆ Set.range f := by
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨(QuotientGroup.mk g⁻¹, i), rfl⟩
  refine Submodule.span_mono hψ ?_
  rw [← Submodule.map_span, hb]
  exact Submodule.mem_map_of_mem Submodule.mem_top

/-- **Finiteness of integral modular symbols.** For a subgroup `Γ` of finite index in `SL(2, ℤ)`,
`𝕄_w(Γ; ℤ)` is a finitely generated abelian group.

This specializes the constructed finite module to the integral coefficients
required for the actual period pairing. -/
instance instModuleFiniteInt [Γ.FiniteIndex] : Module.Finite ℤ (SourceModularSymbols ℤ Γ w) := by
  exact instModuleFinite (R := ℤ) (w := w) Γ

end SourceModularSymbols

/-- The original integral modular-symbol module is finite for every finite-index source subgroup. -/
theorem sourceIntegralModularSymbols_finite (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (w : ℕ) :
    Module.Finite ℤ (SourceModularSymbols ℤ Γ w) := inferInstance

end Dubon2026
