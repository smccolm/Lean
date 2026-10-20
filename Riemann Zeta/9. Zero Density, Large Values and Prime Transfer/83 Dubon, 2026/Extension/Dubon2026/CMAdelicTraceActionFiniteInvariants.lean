import Dubon2026.CMAdelicLatticeActionMatrix

/-! # Finitely many original trace Gram and CM action invariants

For a fixed Gram matrix, the actions of the original integral basis of
the CM field have finitely many possible matrices. Combining this with
the proved finite actual trace Gram classes gives finitely many joint
invariants for all original attached unitary adelic lattices. DUB-17
still requires proving that equality of these invariants recovers the
original unitary arithmetic double coset.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix Module LinearMap.BilinForm
open scoped ComplexOrder

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The actual scalar-action matrices of the original integral basis of the CM field. -/
def cmAdelicLatticeIntegralActions (H : Matrix ι ι K)
    (g : cmFiniteAdelicUnitaryGroup K H)
    (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val)) :
    Module.Free.ChooseBasisIndex ℤ (𝓞 K) → Matrix κ κ ℤ :=
  fun i => cmAdelicLatticeActionMatrix K H g b (RingOfIntegers.basis K i)

/-- A fixed original trace Gram matrix admits only finitely many tuples of original integral CM actions. -/
theorem cmAdelicLatticeIntegralActions_finite (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (d : ℤ) (hd : 0 < d) (hIntegral : ∀ i j, IsIntegral ℤ (d • H i j))
    (A : Matrix κ κ ℤ) :
    {f : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → Matrix κ κ ℤ |
      ∃ (g : cmFiniteAdelicUnitaryGroup K H)
        (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val)),
        toMatrix b (cmAdelicLatticeIntegralTraceForm K H d hIntegral g) = A ∧
          f = cmAdelicLatticeIntegralActions K H g b}.Finite := by
  have hs (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :=
    cmAdelicLatticeActionMatrix_finite K H hH d hd hIntegral A (RingOfIntegers.basis K i)
  refine (Set.Finite.pi' hs).subset ?_
  rintro f ⟨g, b, hb, rfl⟩ i
  exact ⟨g, b, hb, rfl⟩

omit [Fintype κ] [DecidableEq κ] in
/-- All original unitary adelic lattices have joint trace Gram and integral CM action invariants in one finite set. -/
theorem cmAdelicTraceAction_finite_invariants (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef) :
    ∃ (d : ℤ) (_ : 0 < d) (hIntegral : ∀ i j, IsIntegral ℤ (d • H i j))
      (T : Finset (Matrix (Fin (Fintype.card ι * Module.finrank ℚ K))
        (Fin (Fintype.card ι * Module.finrank ℚ K)) ℤ ×
          (Module.Free.ChooseBasisIndex ℤ (𝓞 K) →
            Matrix (Fin (Fintype.card ι * Module.finrank ℚ K))
              (Fin (Fintype.card ι * Module.finrank ℚ K)) ℤ))),
      ∀ g : cmFiniteAdelicUnitaryGroup K H,
        ∃ b : Basis (Fin (Fintype.card ι * Module.finrank ℚ K)) ℤ
          (numberFieldAdelicLattice K ι g.val),
          (toMatrix b (cmAdelicLatticeIntegralTraceForm K H d hIntegral g),
            cmAdelicLatticeIntegralActions K H g b) ∈ T := by
  classical
  obtain ⟨d, hd, hIntegral, S, hS⟩ := cmAdelicTrace_finite_gram_classes K H hH
  let T := S.attach.biUnion fun A =>
    (cmAdelicLatticeIntegralActions_finite K H hH d hd hIntegral A.val).toFinset.image
      (fun f => (A.val, f))
  refine ⟨d, hd, hIntegral, T, ?_⟩
  intro g
  obtain ⟨b, hb⟩ := hS g
  refine ⟨b, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨⟨_, hb⟩, Finset.mem_attach _ _, Finset.mem_image.mpr ?_⟩
  refine ⟨cmAdelicLatticeIntegralActions K H g b, ?_, rfl⟩
  exact (Set.Finite.mem_toFinset _).mpr ⟨g, b, rfl, rfl⟩

end
end Dubon2026
