module

public meta import Lean

/-!
# The `weil` tag attribute

Links a declaration to the label of the corresponding item (definition, lemma
or theorem) in the blueprint of Freitag–Kiehl, *Étale Cohomology and the Weil
Conjecture*. It is written as the attribute name followed by the label as a
string literal, on the line above the declaration. The attribute has no effect
on elaboration.

The syntax is deliberately not written out literally in this docstring, so that
tools scanning the sources for tags do not mistake an example for a real one.
-/

public meta section

open Lean

/-- Links a Lean declaration to the label of a blueprint item of Freitag–Kiehl: the
attribute name, then the label as a string literal. Not written literally here — see the
module docstring. -/
syntax (name := weil) "weil " str : attr

initialize Lean.registerBuiltinAttribute {
  name  := `weil
  descr := "marks a declaration as formalizing a blueprint entity"
  add   := fun _ _ _ => pure ()
}

end
