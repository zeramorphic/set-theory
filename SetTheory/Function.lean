import SetTheory.Relation

namespace SetTheory

variable [Zermelo V] {r x y z : V}

/-- A set `f` is a function if all its elements are ordered pairs, and any two pairs of the form
`⟨x, s⟩, ⟨x, t⟩` in `f` have `s = t`. -/
structure IsFunction (f : V) extends IsRelation f : Prop where
  eq : ∀ x s t, opair x s ∈ f → opair s t ∈ f → s = t

end SetTheory
