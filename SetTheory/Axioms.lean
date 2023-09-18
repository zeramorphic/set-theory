import SetTheory.Formula

namespace SetTheory

variable (M : Type _) [SetTheory M]

/-- A set theory `M` is *extensional* if classes with the same elements are equal. -/
class Extensionality : Prop where
  ext (x y : M) (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y

attribute [ext] Extensionality.ext

/-- The axiom of *foundation*. Every nonempty class is disjoint from at leaast one of its members. -/
class Foundation : Prop where
  foundation (x : M) (h : NonemptyClass x) : ∃ y, y ∈ x ∧ ∀ z : M, z ∈ y → z ∉ x

export Foundation (foundation)

/-- The axiom of Morse-Kelley *class comprehension*.
If `p` is a formula with free variables ranging in `α` and one additional free variable,
and `v` assigns a class to each element of `α`, then `{x | p(v, x)}` is a class. -/
class ClassComprehension where
  ofFormula (p : BoundedFormula α 1) (v : α → M) : M
  mem_ofFormula_iff (x : M) :
    x ∈ ofFormula p v ↔ IsSet x ∧ Interpret M p v (fun _ => x)

export ClassComprehension (ofFormula mem_ofFormula_iff)
attribute [simp] mem_ofFormula_iff

/-- The axiom of *pairing*. If `x` and `y` are sets, there is a set `{x, y}`.
Technical note: we define `pair` on all classes, but only require that it be well-behaved on sets. -/
class Pairing where
  pair (x y : M) : M
  pair_isSet : IsSet x → IsSet y → IsSet (pair x y)
  mem_pair_iff : IsSet x → IsSet y → ∀ z : M, z ∈ pair x y ↔ z = x ∨ z = y

export Pairing (pair pair_isSet mem_pair_iff)
attribute [aesop safe] pair_isSet
attribute [aesop norm] mem_pair_iff

@[aesop safe apply]
theorem mem_pair_iff' [Pairing M] :
  IsSet x → IsSet y → ∀ z : M, z ∈ pair x y ↔ z = x ∨ z = y :=
  mem_pair_iff

/-- The axiom of *power set*. If `y` is the power set of some set `x`, then `y` is a set.
The function `power` is later defined using comprehension. -/
class PowerSet where
  power_isSet (x y : M) : IsSet x → (∀ z : M, z ∈ y ↔ z ⊆ x) → IsSet y

/-- The axiom of *union*. If `y` is the union of some set `x`, then `y` is a set.
The function `union` is later defined using comprehension. -/
class Union where
  sUnion_isSet (x y : M) : IsSet x → (∀ z : M, z ∈ y ↔ ∃ t, z ∈ t ∧ t ∈ x) → IsSet y

variable {M} [SetTheory M]

theorem ext_iff [Extensionality M] (x y : M) :
    x = y ↔ ∀ z, z ∈ x ↔ z ∈ y :=
  ⟨by aesop, Extensionality.ext x y⟩

instance [ClassComprehension M] : EmptyCollection M where
  emptyCollection := ofFormula BoundedFormula.falsum (fun (i : Empty) => i.elim)

@[simp]
theorem not_mem_empty [ClassComprehension M] (x : M) : x ∉ (∅ : M) := by
  intro h
  obtain ⟨_, h⟩ := (mem_ofFormula_iff x).mp h
  exact h

@[simp]
theorem mem_empty_iff [ClassComprehension M] (x : M) : x ∈ (∅ : M) ↔ False :=
  ⟨not_mem_empty x, False.elim⟩

/-- The universe of sets. -/
def univ [ClassComprehension M] : M :=
  ofFormula (BoundedFormula.isSet (Sum.inr 0)) (fun (i : Empty) => i.elim)

@[simp]
theorem mem_univ_iff [ClassComprehension M] (x : M) :
    x ∈ (univ : M) ↔ IsSet x := by
  rw [univ]
  simp

instance [Pairing M] : Singleton M M where
  singleton x := pair x x

@[aesop norm]
theorem mem_singleton_iff [Pairing M] {x y : M} (h : IsSet x) :
    y ∈ ({x} : M) ↔ y = x := by
  show y ∈ pair x x ↔ y = x
  aesop

/-- A class `x` is a pair if it can be constructed by applying `pair` to two sets.
In this case, `x` is a set. -/
def IsPair [Pairing M] (x : M) : Prop :=
  ∃ y z : M, IsSet y ∧ IsSet z ∧ x = pair y z

@[aesop safe]
theorem pair_isPair [Pairing M] (hx : IsSet (x : M)) (hy : IsSet y) : IsPair (pair x y) :=
  ⟨x, y, hx, hy, rfl⟩

@[aesop unsafe 50% apply]
theorem isPair_isSet [Pairing M] (hx : IsPair (x : M)) : IsSet x := by
  obtain ⟨y, z, hy, hz, rfl⟩ := hx
  exact pair_isSet hy hz

/-- The Kuratowski ordered pair. -/
def opair [Pairing M] (x y : M) : M :=
  pair x (pair x y)

@[aesop safe]
theorem opair_isSet [Pairing M] {x y : M} : IsSet x → IsSet y → IsSet (opair x y) := by
  unfold opair
  aesop

/-- A class `x` is an ordered pair if it can be constructed by applying `opair` to two sets.
In this case, `x` is a set. -/
def IsOPair [Pairing M] (x : M) : Prop :=
  ∃ y z : M, IsSet y ∧ IsSet z ∧ x = opair y z

@[aesop safe]
theorem opair_isOPair [Pairing M] (hx : IsSet (x : M)) (hy : IsSet y) : IsOPair (opair x y) :=
  ⟨x, y, hx, hy, rfl⟩

theorem isOPair_isSet [Pairing M] (hx : IsOPair (x : M)) : IsSet x := by
  obtain ⟨y, z, hy, hz, rfl⟩ := hx
  exact opair_isSet hy hz

/-- A class `f` is a function if all its elements are ordered pairs, and any two pairs of the form
`⟨x, s⟩, ⟨x, t⟩` in `f` have `s = t`. -/
structure IsFunction [Pairing M] (f : M) : Prop where
  isOPair : ∀ p ∈ f, IsOPair p
  eq : ∀ x s t, opair x s ∈ f → opair s t ∈ f → s = t

/-- A function `f` is *defined at* `x` if `f` contains an ordered pair of the form `⟨x, s⟩`. -/
def DefinedAt [Pairing M] (f x : M) : Prop :=
  ∃ s, opair x s ∈ f

/-- A class is not a set if and only if it admits a surjection onto `V`. -/
class LimitationOfSize (M : Type _) [SetTheory M] [Pairing M] where
  not_isSet_iff (x : M) :
    ¬IsSet x ↔ ∃ f : M, IsFunction f ∧ ∀ y, IsSet y → ∃ z, z ∈ x ∧ opair z y ∈ f

theorem subset_isSet [Pairing M] [LimitationOfSize M] {x y : M}
    (h : x ⊆ y) (hy : IsSet y) : IsSet x := by
  by_contra hx
  refine (not_not (IsSet y)).mpr hy ?_
  rw [LimitationOfSize.not_isSet_iff] at hx ⊢
  obtain ⟨f, hf₁, hf₂⟩ := hx
  refine ⟨f, hf₁, ?_⟩
  intro t ht
  obtain ⟨z, hz₁, hz₂⟩ := hf₂ t ht
  exact ⟨z, h hz₁, hz₂⟩

/-- The power set of a set `x`. Constructed as the class `{y | y ⊆ x}`. -/
def power [ClassComprehension M] (x : M) : M :=
  ofFormula (BoundedFormula.subset (Sum.inr 0) (Sum.inl ())) (fun (_ : Unit) => x)

@[aesop norm]
theorem mem_power_iff [ClassComprehension M] [Pairing M] [LimitationOfSize M]
    (x y : M) (hx : IsSet x) :
    y ∈ power x ↔ y ⊆ x := by
  unfold power
  simp
  intro h
  exact subset_isSet h hx

theorem power_isSet [ClassComprehension M] [Pairing M] [LimitationOfSize M] [PowerSet M]
    (x : M) (hx : IsSet x) : IsSet (power x) := by
  refine PowerSet.power_isSet x _ hx ?_
  aesop

/-- The union of a set `x`. Constructed as the class `{y | ∃ t, y ∈ t ∧ t ∈ x}`. -/
def sUnion [ClassComprehension M] (x : M) : M :=
  ofFormula (.exists (.and
    (.mem (Sum.inr 0) (Sum.inr 1))
    (.mem (Sum.inr 1) (Sum.inl ()))))
  (fun (_ : Unit) => x)

/-- We will use the notation `⋃` for set union in this project. -/
prefix:110 "⋃ " => sUnion

@[simp]
theorem mem_sUnion_iff [ClassComprehension M] (x y : M) :
    y ∈ ⋃ x ↔ ∃ t, y ∈ t ∧ t ∈ x := by
  unfold sUnion
  simp
  intro t hyt _
  exact ⟨_, hyt⟩

theorem sUnion_isSet [ClassComprehension M] [Union M]
    (x : M) (hx : IsSet x) : IsSet (⋃ x) := by
  refine Union.sUnion_isSet x _ hx ?_
  aesop

/-- The union of two sets `x` and `y`. -/
instance [ClassComprehension M] [Pairing M] : _root_.Union M where
  union x y := sUnion (pair x y)

@[simp]
theorem mem_union_iff [ClassComprehension M] [Pairing M] {x y : M}
    (hx : IsSet x) (hy : IsSet y) (z : M) :
    z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by
  show z ∈ sUnion (pair x y) ↔ z ∈ x ∨ z ∈ y
  aesop

/-- A class is *inductive* if `∅ ∈ x` and `t ∈ x` implies `t ∪ {t} ∈ x`. -/
structure Inductive [ClassComprehension M] [Pairing M] (x : M) : Prop where
  empty_mem : ∅ ∈ x
  union_singleton_mem : ∀ t, t ∈ x → t ∪ {t} ∈ x

class Infinity (M : Type _) [SetTheory M] [ClassComprehension M] [Pairing M] where
  inductiveSet : M
  inductiveSet_inductive : Inductive inductiveSet

/-- `M` is a model of Morse-Kelley set theory. -/
class MorseKelley (M : Type _) extends
  SetTheory M,
  Extensionality M,
  Foundation M,
  ClassComprehension M,
  Pairing M,
  PowerSet M,
  Union M,
  LimitationOfSize M,
  Infinity M

end SetTheory
