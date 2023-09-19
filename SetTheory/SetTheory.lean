import Aesop

/-!
# Models of set theory
-/

/-- `V` is a *model of set theory* if it has a membership operation.
Elements of `V` are called *sets*. -/
class SetTheory (V : Type _) extends Membership V V

namespace SetTheory

instance [SetTheory V] : HasSubset V where
  Subset x y := ∀ ⦃z : V⦄, z ∈ x → z ∈ y

@[aesop unsafe 50% apply]
theorem subset_iff [SetTheory V] (x y : V) : x ⊆ y ↔ ∀ ⦃z : V⦄, z ∈ x → z ∈ y :=
  Iff.rfl

/-- A set is *nonempty* if it has an element. -/
def NonemptySet [SetTheory V] (x : V) : Prop :=
  ∃ y : V, y ∈ x

end SetTheory
