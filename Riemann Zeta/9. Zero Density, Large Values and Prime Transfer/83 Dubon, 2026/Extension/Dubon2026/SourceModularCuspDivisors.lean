/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourceModularDivisorDegree
import Dubon2026.SourceModularRationalCusps
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-! Manin's spanning lemma for the actual degree-zero cusp divisors.
Adapted from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5.
Exact dependency: DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 -> modular
Galois association -> integral Hecke algebra finiteness through periods ->
finite integral modular symbols -> generation by the original unimodular cusp
pairs. This removes the cusp-divisor generation input; the finite-index
coinvariant tensor and actual period comparison are supplied by the later symbol and period modules.
-/

open MonoidAlgebra MulOpposite MvPolynomial Representation TensorProduct
open Matrix.SpecialLinearGroup ModularGroup OnePoint
open scoped MatrixGroups MonoidAlgebra

namespace Dubon2026

namespace SourceModularSymbols

variable (R : Type*)

/-! ### Divisors on the cusps -/

section Semiring

variable [Semiring R]

/-- The degree `∑ nₓ[x] ↦ ∑ nₓ` of an `R`-divisor on the cusps, the coefficient sum. -/
noncomputable def degree : R[OnePoint ℚ] →ₗ[R] R :=
  sourceModularDivisorDegree R (OnePoint ℚ)

/-- The degree-zero divisors `Div⁰(ℙ¹(ℚ))` on the cusps: the augmentation submodule of the
`R`-divisors `R[ℙ¹(ℚ)]`, that is, the kernel of the degree map `TauCeti.ModularSymbols.degree`
(see `TauCeti.ModularSymbols.degreeZero_eq_ker_degree`). -/
noncomputable def degreeZero : Submodule R R[OnePoint ℚ] :=
  (sourceModularDivisorAugmentation R (GL (Fin 2) ℚ) (OnePoint ℚ)).toSubmodule

variable {R} in
@[simp]
theorem degree_single (x : OnePoint ℚ) (r : R) : degree R (single x r) = r := by
  exact sourceModularDivisorDegree_single R (OnePoint ℚ) x r

theorem degreeZero_eq_ker_degree : degreeZero R = LinearMap.ker (degree R) :=
  rfl

variable {R} in
@[simp]
theorem mem_degreeZero_iff {D : R[OnePoint ℚ]} : D ∈ degreeZero R ↔ degree R D = 0 := by
  rw [degreeZero_eq_ker_degree, LinearMap.mem_ker]

/-- The permutation representation of `SL(2, ℤ)` on the `R`-divisors `R[ℙ¹(ℚ)]` on the cusps
`ℙ¹(ℚ) = OnePoint ℚ`, through the Möbius action of `GL(2, ℚ)`. -/
noncomputable def divisorRep : Representation R SL(2, ℤ) R[OnePoint ℚ] :=
  (ofMulAction R (GL (Fin 2) ℚ) (OnePoint ℚ)).comp (mapGL ℚ)

variable {R} in
@[simp]
theorem divisorRep_single (g : SL(2, ℤ)) (x : OnePoint ℚ) (r : R) :
    divisorRep R g (single x r) = single (mapGL ℚ g • x) r := by
  exact Representation.ofMulAction_single (mapGL ℚ g) x r

variable {R}

variable (R) in
/-- The representation of `GL(2, ℚ)` on the degree-zero divisors `Div⁰(ℙ¹(ℚ))`, through the
Möbius action on the cusps. Its restriction to `SL(2, ℤ)` is `TauCeti.ModularSymbols.degreeZeroRep`;
the larger group is what the Hecke operators on modular symbols act through. -/
noncomputable def degreeZeroGLRep : Representation R (GL (Fin 2) ℚ) (degreeZero R) :=
  (sourceModularDivisorAugmentation R (GL (Fin 2) ℚ) (OnePoint ℚ)).toRepresentation

@[simp]
theorem coe_degreeZeroGLRep_apply (g : GL (Fin 2) ℚ) (D : degreeZero R) :
    (degreeZeroGLRep R g D : R[OnePoint ℚ]) =
      ofMulAction R (GL (Fin 2) ℚ) (OnePoint ℚ) g D.val := by
  rfl

variable (R) in
/-- The representation of `SL(2, ℤ)` on the degree-zero divisors `Div⁰(ℙ¹(ℚ))`. -/
noncomputable def degreeZeroRep : Representation R SL(2, ℤ) (degreeZero R) :=
  (degreeZeroGLRep R).comp (mapGL ℚ)

/-- The `SL(2, ℤ)`-representation on `Div⁰(ℙ¹(ℚ))` is the `GL(2, ℚ)`-representation along
`mapGL ℚ`. -/
@[simp]
theorem degreeZeroRep_apply (g : SL(2, ℤ)) : degreeZeroRep R g = degreeZeroGLRep R (mapGL ℚ g) :=
  (rfl)

/-- On the underlying divisor, `degreeZeroRep` is the permutation representation `divisorRep`.
Not `@[simp]`: simp normalises `degreeZeroRep R g` to `degreeZeroGLRep R (mapGL ℚ g)` through
`degreeZeroRep_apply`, and this lemma is the bridge to `divisorRep` for `rw`. -/
theorem coe_degreeZeroRep_apply (g : SL(2, ℤ)) (D : degreeZero R) :
    (degreeZeroRep R g D : R[OnePoint ℚ]) = divisorRep R g D.val := by
  rfl

end Semiring

section Ring

variable {R} [Ring R]

/-- The divisor `[α] - [β]` has degree zero. -/
theorem single_sub_single_mem_degreeZero (α β : OnePoint ℚ) :
    single α (1 : R) - single β 1 ∈ degreeZero R := by
  simp

/-- A `GL(2, ℚ)` translate of `[α] - [β]` is the difference of the translated cusps. -/
theorem degreeZeroGLRep_single_sub_single (g : GL (Fin 2) ℚ) (α β : OnePoint ℚ) :
    degreeZeroGLRep R g ⟨_, single_sub_single_mem_degreeZero α β⟩ =
      ⟨_, single_sub_single_mem_degreeZero (g • α) (g • β)⟩ := by
  apply Subtype.ext
  change ofMulAction R (GL (Fin 2) ℚ) (OnePoint ℚ) g (single α 1 - single β 1) =
    single (g • α) 1 - single (g • β) 1
  exact ((ofMulAction R (GL (Fin 2) ℚ) (OnePoint ℚ) g).map_sub _ _).trans
    (by rw [ofMulAction_single, ofMulAction_single]; rfl)

/-- The span of the unimodular symbols `[g∞] - [g0]` is `SL(2, ℤ)`-stable. -/
private theorem divisorRep_mem_span_unimodular (g : SL(2, ℤ)) {D : R[OnePoint ℚ]}
    (hD : D ∈ Submodule.span R (Set.range fun h : SL(2, ℤ) ↦
      single (mapGL ℚ h • ∞) (1 : R) - single (mapGL ℚ h • ((0 : ℚ) : OnePoint ℚ)) 1)) :
    divisorRep R g D ∈ Submodule.span R (Set.range fun h : SL(2, ℤ) ↦
      single (mapGL ℚ h • ∞) (1 : R) - single (mapGL ℚ h • ((0 : ℚ) : OnePoint ℚ)) 1) := by
  rw [← Submodule.mem_comap]
  refine (Submodule.span_le.2 ?_) hD
  rintro _ ⟨h, rfl⟩
  exact Submodule.subset_span ⟨g * h, by simp [mul_smul]⟩

/-- **Manin's lemma.** The degree-zero divisors on the cusps are spanned by the unimodular
symbols `[g∞] - [g0]`, `g ∈ SL(2, ℤ)`, that is, by the `SL(2, ℤ)`-translates of `[∞] - [0]`. -/
theorem degreeZero_eq_span_unimodular :
    degreeZero R = Submodule.span R (Set.range fun g : SL(2, ℤ) ↦
      single (mapGL ℚ g • ∞) (1 : R) - single (mapGL ℚ g • ((0 : ℚ) : OnePoint ℚ)) 1) := by
  set M := Submodule.span R (Set.range fun h : SL(2, ℤ) ↦
    single (mapGL ℚ h • ∞) (1 : R) - single (mapGL ℚ h • ((0 : ℚ) : OnePoint ℚ)) 1)
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · -- The matrices `g` with `[g∞] - [∞] ∈ M` form a subgroup containing `S` and `T`.
    let H : Subgroup SL(2, ℤ) :=
      { carrier := {g | single (mapGL ℚ g • ∞) (1 : R) - single ∞ 1 ∈ M}
        one_mem' := by simp
        mul_mem' := fun {g h} hg hh ↦ by
          simpa [mul_smul] using add_mem (divisorRep_mem_span_unimodular g hh) hg
        inv_mem' := fun {g} hg ↦ by
          simpa [← mul_smul] using neg_mem (divisorRep_mem_span_unimodular g⁻¹ hg) }
    have hH : H = ⊤ := by
      refine eq_top_iff.2 (SpecialLinearGroup.SL2Z_generators ▸ (Subgroup.closure_le H).2 ?_)
      rintro g (rfl | rfl)
      · have h1 : single (mapGL ℚ (1 : SL(2, ℤ)) • ∞) (1 : R) -
            single (mapGL ℚ (1 : SL(2, ℤ)) • ((0 : ℚ) : OnePoint ℚ)) 1 ∈ M :=
          Submodule.subset_span ⟨1, rfl⟩
        simpa [H] using neg_mem h1
      · simp [H]
    rw [degreeZero_eq_ker_degree]
    change LinearMap.ker (sourceModularDivisorDegree R (OnePoint ℚ)) ≤ M
    rw [sourceModularDivisorDegree_ker_span (OnePoint ℚ) ∞, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := OnePoint.exists_mem_SL2 ℤ x
    exact (hH ▸ Subgroup.mem_top g : g ∈ H)
  · rintro _ ⟨g, rfl⟩
    exact single_sub_single_mem_degreeZero _ _

/-- **Manin's lemma**, inside `Div⁰(ℙ¹(ℚ))`: the `SL(2, ℤ)`-translates of `[∞] - [0]` span the
degree-zero divisors. -/
theorem span_degreeZeroRep_eq_top :
    Submodule.span R (Set.range fun g : SL(2, ℤ) ↦ degreeZeroRep R g
      ⟨_, single_sub_single_mem_degreeZero ∞
        ((0 : ℚ) : OnePoint ℚ)⟩) = ⊤ := by
  apply Submodule.map_injective_of_injective (degreeZero R).injective_subtype
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
  refine Eq.trans ?_ degreeZero_eq_span_unimodular.symm
  congr 2
  funext g
  exact congrArg Subtype.val
    (degreeZeroGLRep_single_sub_single (R := R) (mapGL ℚ g) ∞ ((0 : ℚ) : OnePoint ℚ))

end Ring


end SourceModularSymbols
end Dubon2026
