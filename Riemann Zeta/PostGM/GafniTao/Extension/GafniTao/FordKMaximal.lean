import GafniTao.FordEquation33Source

/-!
# Ford Lemma 3.2: maximizing system and doubling closure

The source maximizes `K_s(P,Q;Ψ;q)` over all integer systems of type
`(d,T)`.  Although that system space need not be presented as a finite type,
the count takes values in a fixed finite interval.  This gives an attained
maximum without adding a compactness or choice hypothesis.  The second
construction proves that coefficient doubling remains in the same source
class by incrementing Ford's explicit power-of-two multiplicity.
-/

namespace GafniTao

noncomputable section

open Polynomial

def FordKMaximal
    {k d T : ℕ} (s P Q q : ℕ)
    (Ψ : FordIntegerPolynomialSystem k d T) : Prop :=
  ∀ Φ : FordIntegerPolynomialSystem k d T,
    fordKCount Φ s P Q q ≤ fordKCount Ψ s P Q q

theorem exists_fordKMaximal
    {k d T : ℕ} (s P Q q : ℕ)
    (Ψ₀ : FordIntegerPolynomialSystem k d T) :
    ∃ Ψ : FordIntegerPolynomialSystem k d T, FordKMaximal s P Q q Ψ := by
  classical
  let B := P ^ (2 * k) * Q ^ (2 * s)
  let values : Finset ℕ := (Finset.range (B + 1)).filter
    (fun n ↦ ∃ Ψ : FordIntegerPolynomialSystem k d T,
      fordKCount Ψ s P Q q = n)
  have hΨ₀le : fordKCount Ψ₀ s P Q q ≤ B :=
    fordKCount_le_trivial Ψ₀ s P Q q
  have hnonempty : values.Nonempty := by
    refine ⟨fordKCount Ψ₀ s P Q q, ?_⟩
    simp only [values, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Ψ₀, rfl⟩
  obtain ⟨m, hm, hmmax⟩ := Finset.exists_max_image values id hnonempty
  have hmWitness : ∃ Ψ : FordIntegerPolynomialSystem k d T,
      fordKCount Ψ s P Q q = m := (Finset.mem_filter.mp hm).2
  obtain ⟨Ψ, hΨ⟩ := hmWitness
  refine ⟨Ψ, fun Φ ↦ ?_⟩
  have hΦle : fordKCount Φ s P Q q ≤ B :=
    fordKCount_le_trivial Φ s P Q q
  have hΦmem : fordKCount Φ s P Q q ∈ values := by
    simp only [values, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Φ, rfl⟩
  rw [hΨ]
  exact hmmax _ hΦmem

def fordDoubleIntegerPolynomialSystem
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    FordIntegerPolynomialSystem k d T where
  poly j := (2 : ℤ) • Ψ.poly j
  twoMultiplicity := Ψ.twoMultiplicity + 1
  zero_below j hj := by simp [Ψ.zero_below j hj]
  degree_above j hj := by
    calc
      ((2 : ℤ) • Ψ.poly j).natDegree = (Ψ.poly j).natDegree :=
        Polynomial.natDegree_smul (Ψ.poly j) (by norm_num)
      _ = (j : ℕ) + 1 - d := Ψ.degree_above j hj
  leadingCoeff_above j hj := by
    have hreg : IsSMulRegular ℤ (2 : ℤ) :=
      IsSMulRegular.of_ne_zero (by norm_num)
    have hlead : ((2 : ℤ) • Ψ.poly j).leadingCoeff =
        (2 : ℤ) • (Ψ.poly j).leadingCoeff :=
      Polynomial.leadingCoeff_smul_of_smul_regular (Ψ.poly j) hreg
    rw [hlead]
    simp only [smul_eq_mul]
    push_cast
    rw [Ψ.leadingCoeff_above j hj]
    norm_num [pow_succ]
    ring

theorem fordDoubleIntegerPolynomialSystem_eval
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (j : Fin k) (z : ℤ) :
    ((fordDoubleIntegerPolynomialSystem Ψ).poly j).eval z =
      2 * (Ψ.poly j).eval z := by
  simp [fordDoubleIntegerPolynomialSystem]

theorem fordKMaximal_double
    {k d T s P Q q : ℕ} {Ψ : FordIntegerPolynomialSystem k d T}
    (hmax : FordKMaximal s P Q q Ψ) :
    fordKCount (fordDoubleIntegerPolynomialSystem Ψ) s P Q q ≤
      fordKCount Ψ s P Q q :=
  hmax _

#print axioms exists_fordKMaximal
#print axioms fordDoubleIntegerPolynomialSystem
#print axioms fordKMaximal_double

end

end GafniTao
