import Dubon2026.CMFiniteAdelicLocalSplitSupport

/-! # Simultaneous original local evaluation of the actual unitary level

The constructed paired-place sections have disjoint supports for the
source finite family. Inserting one correction at a time realizes every
tuple of original integral matrices inside the original unitary group.
This discharges simultaneous local realization before DUB-17's auxiliary
quotient and integral automorphic module comparison.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- Every original local tuple has a genuine integral unitary lift supported on precisely the selected CM-place pairs. -/
theorem cmFiniteAdelicIntegralLocalFamily_exists_support
    (K : Type) [Field K] [NumberField K] [IsCMField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    {S : Type*} [Fintype S] (v : S → HeightOneSpectrum (𝓞 K))
    (hv : ∀ s, v s ≠ cmFinitePlaceConjugation K (v s))
    (hlocal : ∀ s, cmFiniteAdelicFormIntegralAtConjugate K H (v s))
    (hsep : Pairwise fun s t => v s ≠ v t ∧ v s ≠ cmFinitePlaceConjugation K (v t))
    (g : ∀ s, (Matrix ι ι (Valued.integer ((v s).adicCompletion K)))ˣ) :
    ∃ M : cmFiniteAdelicIntegralLevel K H.val,
      (fun s => cmFiniteAdelicIntegralLocalMap K H.val (v s) M) = g ∧
      ∀ w, (∀ s, w ≠ v s ∧ w ≠ cmFinitePlaceConjugation K (v s)) →
        cmFiniteAdelicIntegralLocalMap K H.val w M = 1 := by
  classical
  have hfin (T : Finset S) : ∃ M : cmFiniteAdelicIntegralLevel K H.val,
      (∀ s ∈ T, cmFiniteAdelicIntegralLocalMap K H.val (v s) M = g s) ∧
      ∀ w, (∀ s ∈ T, w ≠ v s ∧ w ≠ cmFinitePlaceConjugation K (v s)) →
        cmFiniteAdelicIntegralLocalMap K H.val w M = 1 := by
    induction T using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | @insert s T hs ih =>
      obtain ⟨M, hM, hMs⟩ := ih
      let b := cmFiniteAdelicIntegralSplitHom K H hH (v s) (hv s) (hlocal s)
        ((cmFiniteAdelicIntegralLocalMap K H.val (v s) M)⁻¹ * g s)
      refine ⟨M * b, ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · rw [map_mul]
          dsimp only [b]
          rw [cmFiniteAdelicIntegralSplitHom_section]
          group
        · have hts : t ≠ s := fun he => hs (he ▸ ht)
          rw [map_mul]
          dsimp only [b]
          rw [cmFiniteAdelicIntegralSplitHom_ne K H hH (v s) (hv s) (hlocal s)
            (v t) (hsep hts).1 (hsep hts).2, mul_one]
          exact hM t ht
      · intro w hw
        rw [map_mul, hMs w (fun t ht => hw t (Finset.mem_insert_of_mem ht)), one_mul]
        dsimp only [b]
        exact cmFiniteAdelicIntegralSplitHom_ne K H hH (v s) (hv s) (hlocal s)
          w (hw s (Finset.mem_insert_self s T)).1 (hw s (Finset.mem_insert_self s T)).2 _
  obtain ⟨M, hM, hMs⟩ := hfin Finset.univ
  exact ⟨M, funext fun s => hM s (Finset.mem_univ s), fun w hw => hMs w (fun s _ => hw s)⟩

/-- At a finite family of disjoint split CM-place pairs, original integral unitary evaluation is jointly surjective. -/
theorem cmFiniteAdelicIntegralLocalFamily_surjective
    (K : Type) [Field K] [NumberField K] [IsCMField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : (Matrix ι ι K)ˣ) (hH : star H = H)
    {S : Type*} [Fintype S] (v : S → HeightOneSpectrum (𝓞 K))
    (hv : ∀ s, v s ≠ cmFinitePlaceConjugation K (v s))
    (hlocal : ∀ s, cmFiniteAdelicFormIntegralAtConjugate K H (v s))
    (hsep : Pairwise fun s t => v s ≠ v t ∧ v s ≠ cmFinitePlaceConjugation K (v t)) :
    Function.Surjective (fun M : cmFiniteAdelicIntegralLevel K H.val =>
      fun s => cmFiniteAdelicIntegralLocalMap K H.val (v s) M) := by
  intro g
  obtain ⟨M, hM, _⟩ := cmFiniteAdelicIntegralLocalFamily_exists_support K H hH v hv hlocal hsep g
  exact ⟨M, hM⟩

end
end Dubon2026
