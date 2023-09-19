import SetTheory.Function

namespace SetTheory
/-- A formula with free variables in `α` is a function class for particular choices of free
variables `v : α → V` if whenever `f a b` and `f a c`, we have `b = c`. -/
def IsFunctionClass [Zermelo V] (f : BoundedFormula α 2) (v : α → V) : Prop :=
  ∀ a b c : V,
    Interpret V f v (fun k => if k = 0 then a else b) →
    Interpret V f v (fun k => if k = 0 then a else c) →
    b = c

/-- The axiom of *replacement*.
If `f` is a function-class and `s` is a set, then the image of `s` under `f` is a set. -/
class Replacement (V : Type _) [Zermelo V] where
  replace (f : BoundedFormula α 2) (v : α → V) (hf : IsFunctionClass f v) (s : V) : V
  mem_replace_iff (a s : V) :
    a ∈ replace f v hf s ↔ ∃ t ∈ s, Interpret V f v (fun k => if k = 0 then t else a)

/-- The **Zermelo-Fraenkel** axioms of set theory. -/
class ZF (V : Type _) extends Zermelo V, Replacement V

variable [ZF V]

/-- A set is *transitive* if members of members of the set are members of the set. -/
def Transitive (x : V) : Prop :=
  ⋃ x ⊆ x

end SetTheory
