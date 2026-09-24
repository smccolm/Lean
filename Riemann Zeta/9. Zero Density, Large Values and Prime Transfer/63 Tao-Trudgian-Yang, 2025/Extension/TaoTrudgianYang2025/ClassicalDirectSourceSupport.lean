import TaoTrudgianYang2025.ClassicalGlobalSourceClassification

/-!
# The literal annular support of a direct interior source

The coefficient-one Fourier sum is restricted to the actual source
annulus, rather than the unrelated ambient sharp-cutoff length. For an
even source scale the annulus is exactly the union of two ordinary
dyadic Dirichlet-polynomial intervals.
-/

noncomputable section
open scoped BigOperators FourierTransform
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem typeISourceSmoothBlock_eq_annulus
    {Y A r : ℕ} (s t : ℝ) (hr : 2 ≤ r)
    (hUpper : 2*(2^r*Y) ≤ A) :
    typeISourceSmoothBlock Y A r s t =
      ∑ n ∈ Finset.Ioc ((2^r*Y)/2) (2*(2^r*Y)),
        (typeISourceSmoothWeight Y A r n : ℂ) *
          (n : ℂ)^(-(s : ℂ)) * (n : ℂ)^(-(t : ℂ)*Complex.I) := by
  let Q := 2^r*Y
  have hEven : 2 ∣ Q :=
    dvd_mul_of_dvd_left (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  have hTwice : 2*(Q/2) = Q := Nat.mul_div_cancel' hEven
  have hHalf : ((Q/2 : ℕ) : ℝ) = (Q : ℝ)/2 := by
    have hCast : (2 : ℝ)*(Q/2 : ℕ) = Q := by exact_mod_cast hTwice
    linarith
  have hSubset : Finset.Ioc (Q/2) (2*Q) ⊆ Finset.Icc 1 (A+1) := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega,by dsimp only [Q] at hn'; omega⟩
  unfold typeISourceSmoothBlock
  symm
  apply Finset.sum_subset hSubset
  intro n _hn hNot
  have hw : typeISourceSmoothWeight Y A r n = 0 := by
    by_contra hNonzero
    have hSupport := typeISourceSmoothWeight_support hNonzero
    have hLowReal : ((Q/2 : ℕ) : ℝ) < n := by
      rw [hHalf]
      exact hSupport.1
    have hLow : Q/2 < n := by exact_mod_cast hLowReal
    have hUp : n < 2*Q := by exact_mod_cast hSupport.2
    exact hNot (Finset.mem_Ioc.mpr ⟨hLow,hUp.le⟩)
  simp [hw]

theorem typeISourceSmoothBlock_eq_annular_fourier_deweight
    {Y A r : ℕ} {s t : ℝ} (hY : 0 < Y) (hr : 2 ≤ r)
    (hLower : ((Y+1 : ℕ) : ℝ) ≤ (((2^r*Y : ℕ) : ℝ)/2))
    (hUpper : 2*(2^r*Y) ≤ A) :
    typeISourceSmoothBlock Y A r s t =
      ((((2^r*Y : ℕ) : ℝ)^(-s) : ℝ) : ℂ) *
        ∫ ξ : ℝ, 𝓕 (typeIInteriorLogProfileSchwartz s) ξ *
          Complex.exp (-(((2*Real.pi*ξ*Real.log (2^r*Y : ℕ) : ℝ) : ℂ)*Complex.I)) *
          ∑ n ∈ Finset.Ioc ((2^r*Y)/2) (2*(2^r*Y)),
            (n : ℂ)^(-(((t-2*Real.pi*ξ : ℝ) : ℂ))*Complex.I) := by
  let Q := 2^r*Y
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hPositive : ∀ n ∈ Finset.Ioc (Q/2) (2*Q), 0 < n := by
    intro n hn
    exact Nat.zero_le (Q/2) |>.trans_lt (Finset.mem_Ioc.mp hn).1
  have hFourier := fourierDeweightFiniteBlock_logShift_native
    (typeIInteriorLogProfileSchwartz s) (Finset.Ioc (Q/2) (2*Q)) t
    (Real.log (Q : ℝ)) hPositive
  rw [typeISourceSmoothBlock_eq_annulus s t hr hUpper]
  rw [← hFourier,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [typeIInteriorLogProfileSchwartz_apply,
    typeISourceSmoothWeight_eq_dyadic_of_interior hLower hUpper]
  have hScale := typeIInteriorLogProfile_scale_identity
    (Q := Q) (n := n) (σ := s) hQ (hPositive n hn)
  simpa only [Q,mul_assoc] using congrArg
    (fun z : ℂ => z*(n : ℂ)^(-(t : ℂ)*Complex.I)) hScale.symm

theorem coefficientOne_annulus_eq_two_dyadic_polynomials
    (Q : ℕ) (t : ℝ) (hEven : 2 ∣ Q) :
    (∑ n ∈ Finset.Ioc (Q/2) (2*Q),
      (n : ℂ)^(-(t : ℂ)*Complex.I)) =
      dirichletPoly (Q/2) (fun _ => 1) t +
        dirichletPoly Q (fun _ => 1) t := by
  have hTwice : 2*(Q/2) = Q := Nat.mul_div_cancel' hEven
  simp only [dirichletPoly,dyadicInterval,one_mul,hTwice]
  exact (Finset.sum_Ioc_consecutive
    (fun n : ℕ => (n : ℂ)^(-(t : ℂ)*Complex.I))
    (Nat.div_le_self Q 2) (by omega : Q ≤ 2*Q)).symm

end TaoTrudgianYang2025
