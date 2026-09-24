import TaoTrudgianYang2025.FiniteFourierRadius

/-!
# Bounded Fourier entry from the actual direct interior source

The source annulus is unchanged. A fixed-profile Fourier shift gives one
of its two coefficient-one dyadic polynomials, with the complete radius
and threshold factor retained explicitly.
-/

noncomputable section
open scoped BigOperators FourierTransform
open Complex
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem exists_bounded_coefficientOne_shift_of_interior_source
    {Y A r : ℕ} (s V t : ℝ) (k : ℕ)
    (hY : 0 < Y) (hr : 2 ≤ r) (hV : 0 < V) (hk : 1 < k)
    (hLower : ((Y+1 : ℕ) : ℝ) ≤ (((2^r*Y : ℕ) : ℝ)/2))
    (hUpper : 2*(2^r*Y) ≤ A)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r s t‖) :
    let Q := 2^r*Y
    let f := typeIInteriorLogProfileSchwartz s
    let R := finiteFourierRadius f (Finset.Ioc (Q/2) (2*Q)) k ((Q : ℝ)^(-s)) V
    ∃ ξ ∈ Set.Icc (-R) R,
      V/(4*(Q : ℝ)^(-s)*finiteFourierMass f) ≤
        ‖∑ n ∈ Finset.Ioc (Q/2) (2*Q),
          (n : ℂ)^(-(((t-2*Real.pi*ξ : ℝ) : ℂ))*I)‖ := by
  dsimp only
  let Q := 2^r*Y
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hPositive : ∀ n ∈ Finset.Ioc (Q/2) (2*Q), 0 < n := by
    intro n hn
    exact (Nat.zero_le (Q/2)).trans_lt (Finset.mem_Ioc.mp hn).1
  apply exists_explicitly_bounded_coefficientOne_shift_of_schwartz_logShift
    (typeIInteriorLogProfileSchwartz s) (Finset.Ioc (Q/2) (2*Q)) k
    ((Q : ℝ)^(-s)) (Real.log Q) V t hPositive
    (Real.rpow_pos_of_pos (by exact_mod_cast hQ) _) hV hk
  rw [fourierDeweightFiniteBlock_logShift_native
    (typeIInteriorLogProfileSchwartz s) (Finset.Ioc (Q/2) (2*Q)) t
    (Real.log Q) hPositive]
  simpa only [Q,typeISourceSmoothBlock_eq_annular_fourier_deweight hY hr hLower hUpper]
    using hLarge

theorem exists_bounded_two_dyadic_shift_of_interior_source
    {Y A r : ℕ} (s V t : ℝ) (k : ℕ)
    (hY : 0 < Y) (hr : 2 ≤ r) (hV : 0 < V) (hk : 1 < k)
    (hLower : ((Y+1 : ℕ) : ℝ) ≤ (((2^r*Y : ℕ) : ℝ)/2))
    (hUpper : 2*(2^r*Y) ≤ A)
    (hLarge : V ≤ ‖typeISourceSmoothBlock Y A r s t‖) :
    let Q := 2^r*Y
    let f := typeIInteriorLogProfileSchwartz s
    let R := finiteFourierRadius f (Finset.Ioc (Q/2) (2*Q)) k ((Q : ℝ)^(-s)) V
    ∃ ξ ∈ Set.Icc (-R) R,
      V/(8*(Q : ℝ)^(-s)*finiteFourierMass f) ≤
        ‖dirichletPoly (Q/2) (fun _ => 1) (t-2*Real.pi*ξ)‖ ∨
      V/(8*(Q : ℝ)^(-s)*finiteFourierMass f) ≤
        ‖dirichletPoly Q (fun _ => 1) (t-2*Real.pi*ξ)‖ := by
  dsimp only
  obtain ⟨ξ,hξ,hBound⟩ :=
    exists_bounded_coefficientOne_shift_of_interior_source
      s V t k hY hr hV hk hLower hUpper hLarge
  refine ⟨ξ,hξ,?_⟩
  have hEven : 2 ∣ 2^r*Y :=
    dvd_mul_of_dvd_left (dvd_pow (dvd_refl 2) (by omega : r ≠ 0)) Y
  rw [coefficientOne_annulus_eq_two_dyadic_polynomials _ _ hEven] at hBound
  have hTri := norm_add_le
    (dirichletPoly ((2^r*Y)/2) (fun _ => 1) (t-2*Real.pi*ξ))
    (dirichletPoly (2^r*Y) (fun _ => 1) (t-2*Real.pi*ξ))
  have hThreshold :
      V/(4*((2^r*Y : ℕ) : ℝ)^(-s)*finiteFourierMass (typeIInteriorLogProfileSchwartz s)) =
        2*(V/(8*((2^r*Y : ℕ) : ℝ)^(-s)*
          finiteFourierMass (typeIInteriorLogProfileSchwartz s))) := by ring
  rw [hThreshold] at hBound
  by_contra hBoth
  push Not at hBoth
  linarith

end TaoTrudgianYang2025
