import RiemannZeta.GuthMaynard.Separated

example (S : Finset ℝ) (L : ℕ)
    (hlocal : ∀ (x : ℤ), (S.filter (fun t => (x : ℝ) ≤ t ∧ t < (x : ℝ) + 1)).card ≤ L) :
    ∃ W ⊆ S, RiemannZeta.GuthMaynard.IsSeparated 1 W ∧ S.card ≤ 2 * L * W.card := by
  exact RiemannZeta.GuthMaynard.separated_selection S L hlocal
