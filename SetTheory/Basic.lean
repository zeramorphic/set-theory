import Aesop

/-!
# Models of set theory
-/

/-- M is a *model of set theory* if it has a membership operation.
Elements of M are called *classes*. -/
class SetTheory (M : Type _) extends Membership M M

namespace SetTheory

instance [SetTheory M] : HasSubset M where
  Subset x y := ∀ ⦃z : M⦄, z ∈ x → z ∈ y

@[aesop unsafe 50% apply]
theorem subset_iff [SetTheory M] (x y : M) : x ⊆ y ↔ ∀ ⦃z : M⦄, z ∈ x → z ∈ y :=
  Iff.rfl

/-- A class is a *set* if it is an element of a class. -/
def IsSet [SetTheory M] (x : M) : Prop :=
  ∃ y : M, x ∈ y

theorem isSet_of_mem [SetTheory M] {x y : M} (h : x ∈ y) : IsSet x :=
  ⟨y, h⟩

/-- A *set* in a set theory M is a class that is a set.
Not to be confused with Mathlib's `Set`. -/
def Set (M : Type _) [SetTheory M] : Type _ :=
  {x : M // IsSet x}

/-- A class is *nonempty* if it has an element. -/
def NonemptyClass [SetTheory M] (x : M) : Prop :=
  ∃ y : M, y ∈ x

end SetTheory
