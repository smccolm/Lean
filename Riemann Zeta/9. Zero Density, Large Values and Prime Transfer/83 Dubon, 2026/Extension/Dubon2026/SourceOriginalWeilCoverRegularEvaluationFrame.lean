import Dubon2026.SourceOriginalWeilCoverRegularEvaluationSeparation
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! DUB-17/18 -> auxiliary point division -> cover Jacobi inversion.
Adapt the native original-curve evaluation and inverse-function arguments
to the literal Kummer cover, using actual residue readings and Abel vectors.
Finite coordinate support replaces any numerical genus assumption.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Metric KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem span_readDifferential_center_eq_top {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ (EE))) :
    Submodule.span ℂ (range fun v : Place ℂ (EE) =>
      fun i => readDifferential N n r A hr hrA v (b i) 0) = ⊤ := by
  classical
  by_contra htop
  obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr htop)
  let c : Fin kDim → ℂ := fun i => f (fun j => if i = j then 1 else 0)
  have hfx : ∀ x : Fin kDim → ℂ, f x = ∑ i, x i * c i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    rfl
  let η : regularDifferentials ℂ (EE) := ∑ i, c i • b i
  have he : (η : Ω[EE⁄ℂ]) = ∑ i, c i • (b i : Ω[EE⁄ℂ]) := by
    simp only [η, Submodule.coe_sum, Submodule.coe_smul]
  have hz : ∀ v : Place ℂ (EE), readDifferential N n r A hr hrA v η 0 = 0 := by
    intro v
    rw [he, readDifferential_sum_smul N n r A hr hrA v c _ (fun i => (b i).2)
      (mem_ball_self (place_spec N n r A hr hrA v).1)]
    have hv : f (fun i => readDifferential N n r A hr hrA v (b i) 0) = 0 :=
      hker (Submodule.subset_span ⟨v, rfl⟩)
    rw [hfx] at hv
    exact (Finset.sum_congr rfl fun i _ => mul_comm (c i) (readDifferential N n r A hr hrA v (b i) 0)).trans hv
  have hη := eq_zero_of_forall_readDifferential_center N n r A hr hrA η η.2 hz
  have hη' : η = 0 := Subtype.ext hη
  have hc : ∀ i, c i = 0 := Fintype.linearIndependent_iff.mp b.linearIndependent c hη'
  apply hf0
  ext x
  simp [hfx, hc]

theorem exists_cover_evaluation_frame {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE)) :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → Place ℂ EE)
      (β : Module.Basis κ ℂ (Fin kDim → ℂ)),
      ∀ k, β k = fun i => readDifferential N n r A hr hrA (a k) (b i) 0 := by
  classical
  let v : Place ℂ EE → (Fin kDim → ℂ) :=
    fun P i => readDifferential N n r A hr hrA P (b i) 0
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ v
  haveI : Finite κ := hli.finite
  letI : Fintype κ := Fintype.ofFinite κ
  have htop : ⊤ ≤ Submodule.span ℂ (range (v ∘ a)) := by
    rw [hspan, show Submodule.span ℂ (range v) = ⊤ from
      span_readDifferential_center_eq_top N n r A hr hrA b]
  let β : Module.Basis κ ℂ (Fin kDim → ℂ) := Module.Basis.mk hli htop
  refine ⟨κ, inferInstance, a, β, fun k => ?_⟩
  simp only [β, Module.Basis.mk_apply]
  rfl

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
