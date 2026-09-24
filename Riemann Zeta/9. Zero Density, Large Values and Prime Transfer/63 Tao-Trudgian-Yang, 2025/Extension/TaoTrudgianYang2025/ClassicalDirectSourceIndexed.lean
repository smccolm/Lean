import TaoTrudgianYang2025.ClassicalDirectSourceFourier

/-!
# All-index two-length Fourier family from the direct source

Each original index receives a Fourier ordinate and one of the two
literal dyadic lengths. The full-family energy perturbation remains
attached to the unchanged index type.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

def classicalDirectDyadicLength (Q : ℕ) (c : Fin 2) : ℕ :=
  if c = 0 then Q/2 else Q

theorem classicalDirectDyadicLength_bounds (Q : ℕ) (c : Fin 2) :
    Q/2 ≤ classicalDirectDyadicLength Q c ∧ classicalDirectDyadicLength Q c ≤ Q := by
  unfold classicalDirectDyadicLength
  split_ifs
  · exact ⟨le_rfl,Nat.div_le_self Q 2⟩
  · exact ⟨Nat.div_le_self Q 2,le_rfl⟩

theorem exists_interior_source_indexed_two_dyadic_fourier_family
    {ι : Type*} [Fintype ι] {Y A r : ℕ}
    (s V : ℝ) (k : ℕ) (W : ι → ℝ)
    (hY : 0 < Y) (hr : 2 ≤ r) (hV : 0 < V) (hk : 1 < k)
    (hLower : ((Y+1 : ℕ) : ℝ) ≤ (((2^r*Y : ℕ) : ℝ)/2))
    (hUpper : 2*(2^r*Y) ≤ A)
    (hLarge : ∀ x, V ≤ ‖typeISourceSmoothBlock Y A r s (W x)‖) :
    let Q := 2^r*Y
    let f := typeIInteriorLogProfileSchwartz s
    let R := finiteFourierRadius f (Finset.Ioc (Q/2) (2*Q)) k ((Q : ℝ)^(-s)) V
    ∃ W' : ι → ℝ, ∃ label : ι → Fin 2,
      (∀ x, |W' x-W x| ≤ 2*Real.pi*R) ∧
      (∀ x, let N := classicalDirectDyadicLength Q (label x)
        V/(8*(Q : ℝ)^(-s)*finiteFourierMass f) ≤
          ‖dirichletPoly N (fun _ => 1) (W' x)‖) ∧
      approximateAdditiveEnergyOf 1 W ≤
        (4*Nat.ceil (1+4*(2*Real.pi*R))+6)*approximateAdditiveEnergyOf 1 W' := by
  classical
  dsimp only
  let Q := 2^r*Y
  let f := typeIInteriorLogProfileSchwartz s
  let R := finiteFourierRadius f (Finset.Ioc (Q/2) (2*Q)) k ((Q : ℝ)^(-s)) V
  have hWitness : ∀ x : ι, ∃ ξ ∈ Set.Icc (-R) R, ∃ c : Fin 2,
      V/(8*(Q : ℝ)^(-s)*finiteFourierMass f) ≤
        ‖dirichletPoly (classicalDirectDyadicLength Q c) (fun _ => 1)
          (W x-2*Real.pi*ξ)‖ := by
    intro x
    obtain ⟨ξ,hξ,hLeft | hRight⟩ :=
      exists_bounded_two_dyadic_shift_of_interior_source
        s V (W x) k hY hr hV hk hLower hUpper (hLarge x)
    · refine ⟨ξ,hξ,0,?_⟩
      simpa only [classicalDirectDyadicLength,if_pos rfl,Q,f] using hLeft
    · refine ⟨ξ,hξ,1,?_⟩
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simpa only [classicalDirectDyadicLength,if_neg h10,Q,f] using hRight
  choose ξ hξ label hValue using hWitness
  let W' : ι → ℝ := fun x => W x-2*Real.pi*ξ x
  have hPert : ∀ x, |W' x-W x| ≤ 2*Real.pi*R := by
    intro x
    have hAbs : |ξ x| ≤ R := abs_le.mpr (hξ x)
    dsimp only [W']
    rw [show W x-2*Real.pi*ξ x-W x = -(2*Real.pi*ξ x) by ring,
      abs_neg,abs_mul,abs_mul,abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)),
      abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left hAbs (by positivity)
  refine ⟨W',label,hPert,hValue,?_⟩
  calc
    approximateAdditiveEnergyOf 1 W ≤
        approximateAdditiveEnergyOf (1+4*(2*Real.pi*R)) W' :=
      approximateAdditiveEnergyOf_perturbation_le hPert
    _ ≤ (4*Nat.ceil (1+4*(2*Real.pi*R))+6)*approximateAdditiveEnergyOf 1 W' :=
      approximateAdditiveEnergyOf_le_natCeil_mul_unit _ _

end TaoTrudgianYang2025
