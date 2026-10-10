import Dubon2026.AlgebraIdempotentLeftIdeal
import Dubon2026.MatrixUnitLeftIdealColumns
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Genuine residual columns span the actual original idempotent left ideal -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O R : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Actual lifts of the original residual column units span the original idempotent left ideal: its zero-reduction kernel and finite generation give the precise maximal-ideal remainder required by Nakayama. -/
theorem matrixIdempotentLeftIdeal_span
    (S : Subalgebra O R) [IsLocalRing S]
    (A : Subalgebra S (Matrix ι ι R)) [Module.Finite S A]
    (e : A) (he : e ^ 2 = e) (i₀ : ι)
    (hebar : (RingHom.mapMatrix (IsLocalRing.residue R)) e.val = Matrix.single i₀ i₀ 1)
    (hscalar : Function.Surjective (fun c : S => IsLocalRing.residue R c.val))
    (hker : ∀ x : A, (∀ i j, x.val i j ∈ IsLocalRing.maximalIdeal R) →
      x ∈ IsLocalRing.maximalIdeal S • (⊤ : Submodule S A))
    (v : ι → algebraIdempotentLeftIdeal (S := S) e)
    (hv : ∀ i, (RingHom.mapMatrix (IsLocalRing.residue R)) (v i).val.val =
      Matrix.single i i₀ 1) :
    Submodule.span S (Set.range v) = ⊤ := by
  let L := algebraIdempotentLeftIdeal (S := S) e
  letI : AddCommGroup L := L.addCommGroup
  letI : Module S L := L.module
  letI : SMul S L := L.module.toSMul
  letI : Module.Finite S L := algebraIdempotentLeftIdeal_finite e
  let V := Submodule.span S (Set.range v)
  let J := IsLocalRing.maximalIdeal S
  let F : L →ₗ[S] Matrix ι ι R := A.val.toLinearMap.comp L.subtype
  let f := RingHom.mapMatrix (IsLocalRing.residue R) (m := ι)
  have htop : (⊤ : Submodule S L) ≤ V ⊔ J • ⊤ := by
    intro x _
    let Z := f (F x)
    have hxfix := (mem_algebraIdempotentLeftIdeal_iff e he x.val).mp x.property
    have hZ : Z * Matrix.single i₀ i₀ 1 = Z := by
      have h := congrArg (fun z : A => f z.val) hxfix
      change f (x.val.val * e.val) = f x.val.val at h
      rw [map_mul, hebar] at h
      exact h
    choose c hc using fun i => hscalar (Z i i₀)
    let y : L := ∑ i, @SMul.smul S L inferInstance (c i) (v i)
    have hyV : y ∈ V := by
      apply V.sum_mem
      intro i _
      exact V.smul_mem (c i) (Submodule.subset_span (Set.mem_range_self i))
    have hy : f (F y) = Z := by
      ext i j
      change IsLocalRing.residue R
        ((F (∑ k, @SMul.smul S L inferInstance (c k) (v k))) i j) = Z i j
      rw [map_sum]
      simp only [Matrix.sum_apply]
      change IsLocalRing.residue R (∑ k, (c k : R) * (v k).val.val i j) = Z i j
      rw [map_sum]
      simp only [map_mul, hc]
      have hvij (k : ι) : IsLocalRing.residue R ((v k).val.val i j) =
          Matrix.single k i₀ (1 : IsLocalRing.ResidueField R) i j :=
        congrArg (fun W : Matrix ι ι (IsLocalRing.ResidueField R) => W i j) (hv k)
      simp only [hvij]
      have hz := congrArg (fun W : Matrix ι ι (IsLocalRing.ResidueField R) => W i j)
        (matrix_eq_sum_single_column Z i₀ hZ)
      simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using hz.symm
    have hz : f (F (x - y)) = 0 := by
      change f (F x - F y) = 0
      rw [map_sub, hy]
      exact sub_self Z
    have hzA : (x - y).val ∈ J • (⊤ : Submodule S A) := by
      apply hker
      intro i j
      apply (IsLocalRing.residue_eq_zero_iff (R := R) _).mp
      exact congrArg (fun W : Matrix ι ι (IsLocalRing.ResidueField R) => W i j) hz
    have hzL : x - y ∈ J • (⊤ : Submodule S L) :=
      algebraIdempotentLeftIdeal_mem_ideal_smul J e he (x - y) hzA
    exact Submodule.mem_sup.mpr ⟨y, hyV, x - y, hzL, by rw [add_comm, sub_add_cancel]⟩
  exact top_unique (Submodule.le_of_le_smul_of_le_jacobson_bot
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson ⊥) htop)

end
end Dubon2026
