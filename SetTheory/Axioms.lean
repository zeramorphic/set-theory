import SetTheory.Formula

namespace SetTheory

variable (V : Type _) [SetTheory V]

/-- A set theory `V` is *extensional* if sets with the same elements are equal. -/
class Extensionality : Prop where
  ext (x y : V) (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y

attribute [ext] Extensionality.ext

/-- The axiom of *foundation*. Every nonempty set has an `∈`-minimal element. -/
class Foundation : Prop where
  foundation (x : V) (h : NonemptySet x) : ∃ y, y ∈ x ∧ ∀ z : V, z ∈ y → z ∉ x

export Foundation (foundation)

/-- The axiom of *set comprehension*.
If `p` is a formula with free variables ranging in `α` and one additional free variable,
and `v` assigns a set to each element of `α`, then `{x ∈ y | p(v, x)}` is a set. -/
class SetComprehension where
  sep (p : BoundedFormula α 1) (v : α → V) (y : V) : V
  mem_sep_iff (y x : V) :
    x ∈ sep p v y ↔ x ∈ y ∧ Interpret V p v (fun _ => x)

export SetComprehension (sep mem_sep_iff)
attribute [simp] mem_sep_iff

/-- The axiom of *pairing*. If `x` and `y` are sets, there is a set `{x, y}`. -/
class Pairing where
  pair (x y : V) : V
  mem_pair_iff (z : V) : z ∈ pair x y ↔ z = x ∨ z = y

export Pairing (pair mem_pair_iff)
attribute [simp] mem_pair_iff

/-- The axiom of *power set*. If `x` is a set, then the set of subsets of `x` exists. -/
class PowerSet where
  power (x : V) : V
  mem_power_iff {x : V} (y : V) : y ∈ power x ↔ y ⊆ x

export PowerSet (power mem_power_iff)
attribute [simp] mem_power_iff

/-- The axiom of *union*. If `x` is a set, then the set of elements of elements of `x` is a set. -/
class Union where
  sUnion (x : V) : V
  mem_sUnion_iff {x : V} (y : V) : y ∈ sUnion x ↔ ∃ t ∈ x, y ∈ t

/-- We will use the notation `⋃` for set union in this project. -/
prefix:110 "⋃ " => Union.sUnion

export Union (mem_sUnion_iff)
attribute [simp] mem_sUnion_iff

/-- The axiom of *empty set*. There is a set with no elements. -/
class EmptySet where
  empty : V
  not_mem_empty (x : V) : x ∉ empty

export EmptySet (not_mem_empty)
attribute [simp] not_mem_empty

variable {V} [SetTheory V]

theorem ext_iff [Extensionality V] (x y : V) :
    x = y ↔ ∀ z, z ∈ x ↔ z ∈ y :=
  ⟨by aesop, Extensionality.ext x y⟩

instance [EmptySet V] : EmptyCollection V where
  emptyCollection := EmptySet.empty

@[simp]
theorem mem_empty_iff [EmptySet V] (x : V) : x ∈ (∅ : V) ↔ False :=
  ⟨not_mem_empty x, False.elim⟩

instance [Pairing V] : Singleton V V where
  singleton x := pair x x

@[simp]
theorem mem_singleton_iff [Pairing V] :
    y ∈ ({x} : V) ↔ y = x := by
  show y ∈ pair x x ↔ y = x
  simp

/-- A set `x` is a pair if it can be constructed by applying `pair` to two sets. -/
def IsPair [Pairing V] (x : V) : Prop :=
  ∃ y z : V, x = pair y z

@[simp]
theorem pair_isPair [Pairing V] : IsPair (pair x y : V) :=
  ⟨x, y, rfl⟩

/-- The union of two sets `x` and `y`. -/
instance [Union V] [Pairing V] : _root_.Union V where
  union x y := ⋃ pair x y

@[simp]
theorem mem_union_iff [Union V] [Pairing V] {x y : V} (z : V) :
    z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by
  show z ∈ ⋃ pair x y ↔ z ∈ x ∨ z ∈ y
  aesop

/-- A set is *inductive* if `∅ ∈ x` and `t ∈ x` implies `t ∪ {t} ∈ x`. -/
structure Inductive [EmptySet V] [Union V] [Pairing V] (x : V) : Prop where
  empty_mem : ∅ ∈ x
  union_singleton_mem : ∀ t, t ∈ x → t ∪ {t} ∈ x

class Infinity (V : Type _) [SetTheory V] [EmptySet V] [Union V] [Pairing V] where
  inductiveSet : V
  inductiveSet_inductive : Inductive inductiveSet

/-- `V` is a model of Zermelo set theory. -/
class Zermelo (V : Type _) extends
  SetTheory V,
  Extensionality V,
  Foundation V,
  SetComprehension V,
  Pairing V,
  PowerSet V,
  Union V,
  EmptySet V,
  Infinity V

end SetTheory
