import Dubon2026.SourceCuspLaurentFunctionIdentity
import Dubon2026.SourceLaurentIntegralDescent

/-! DUB-17/18 -> rational Fourier structure -> cyclotomic monic relations.
Transport the actual finite monic equation to the already proved Laurent
coefficient-descent theorem. Polynomial and finite-sum realization uses
the existing meromorphic germ field operations. -/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section
open UpperHalfPlane
open scoped Manifold

theorem Represents.cusp_sum {h : ℝ} {ι : Type*} (s : Finset ι)
    {A : ι → LaurentSeries ℂ} {f : ι → ℍ → ℂ}
    (hf : ∀ i ∈ s, Represents (A i) (cuspFunction h (f i))) :
    Represents (∑ i ∈ s, A i) (cuspFunction h (fun τ => ∑ i ∈ s, f i τ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, map_zero] using represents_cusp_const h 0
  | @insert i s hi ih =>
    have hrep := (hf i (Finset.mem_insert_self _ _)).cusp_add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi, Pi.add_apply] using hrep

theorem Represents.cusp_aeval {h : ℝ} {A : LaurentSeries ℂ} {f : ℍ → ℂ}
    (hf : Represents A (cuspFunction h f)) (P : Polynomial ℂ) :
    Represents (Polynomial.aeval A P) (cuspFunction h (fun τ => P.eval (f τ))) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [map_add, Polynomial.eval_add, Pi.add_apply] using hP.cusp_add hQ
  | monomial n c =>
    simpa only [Polynomial.aeval_monomial, Polynomial.eval_monomial, Pi.mul_apply,
      Pi.pow_apply] using (represents_cusp_const h c).cusp_mul (hf.cusp_pow n)

theorem Represents.isIntegral_of_monic_relation {h : ℝ} {X J : LaurentSeries ℂ}
    {f j : ℍ → ℂ} (hf : Represents X (cuspFunction h f))
    (hj : Represents J (cuspFunction h j)) (d : ℕ) (p : Fin d → Polynomial ℂ)
    (hrel : ∀ τ : ℍ, f τ ^ d + ∑ i : Fin d, (p i).eval (j τ) * f τ ^ (i : ℕ) = 0) :
    IsIntegral (Algebra.adjoin ℂ ({J} : Set (LaurentSeries ℂ))) X := by
  classical
  have hsum := Represents.cusp_sum Finset.univ fun i _ =>
    (hj.cusp_aeval (p i)).cusp_mul (hf.cusp_pow i.val)
  have hr := (hf.cusp_pow d).cusp_add hsum
  have he : (fun τ : ℍ => f τ ^ d +
      ∑ i : Fin d, (p i).eval (j τ) * f τ ^ (i : ℕ)) = fun _ => 0 := funext hrel
  have hzero : X ^ d + ∑ i : Fin d, Polynomial.aeval J (p i) * X ^ (i : ℕ) = 0 := by
    apply Represents.eq_series (F := cuspFunction h (fun _ : ℍ => 0))
    · change Represents _ (cuspFunction h (fun τ => f τ ^ d +
        ∑ i : Fin d, (p i).eval (j τ) * f τ ^ (i : ℕ))) at hr
      rw [he] at hr
      exact hr
    · simpa only [map_zero] using represents_cusp_const h 0
  let R := Algebra.adjoin ℂ ({J} : Set (LaurentSeries ℂ))
  let c : Fin d → R := fun i => ⟨Polynomial.aeval J (p i),
    (Algebra.adjoin_singleton_eq_range_aeval ℂ J).ge ⟨p i, rfl⟩⟩
  let Q : Polynomial R := ∑ i : Fin d, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
  refine ⟨Polynomial.X ^ d + Q,
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c), ?_⟩
  change Polynomial.eval₂ _ X (Polynomial.X ^ d + ∑ i : Fin d,
    Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) = 0
  simpa only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] using hzero

end
end Dubon2026.SourceFunctionField.CuspTaylor