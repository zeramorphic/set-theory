import SetTheory.Basic

namespace SetTheory

variable [Zermelo V] {x y z : V}

/-- The Kuratowski ordered pair. -/
def opair [Pairing V] (x y : V) : V :=
  pair {x} (pair x y)

/-- A set `x` is an ordered pair if it can be constructed by applying `opair` to two sets. -/
def IsOPair [Pairing V] (x : V) : Prop :=
  ∃ y z : V, x = opair y z

@[aesop safe]
theorem opair_isOPair [Pairing V] : IsOPair (opair x y : V) :=
  ⟨x, y, rfl⟩

/-- The first projection of a Kuratowski ordered pair. -/
def π₁ (x : V) : V :=
  ⋃ ⋂ x

/-- The second projection of a Kuratowski ordered pair. -/
def π₂ (x : V) : V :=
  ⋃ sep
    (.imp
      (.ne (Sum.inl true) (Sum.inl false))
      (.not (.mem (Sum.inr 0) (Sum.inl false))))
    (fun i => if i then ⋃ x else ⋂ x) (⋃ x)

theorem mem_π₂_iff : y ∈ π₂ x ↔ ∃ z, y ∈ z ∧ z ∈ ⋃ x ∧ (⋃ x ≠ ⋂ x → z ∉ ⋂ x) := by
  unfold π₂
  aesop

@[simp]
theorem π₁_opair : π₁ (opair x y) = x := by
  unfold π₁ opair
  ext z
  aesop

@[simp]
theorem π₂_opair : π₂ (opair x y) = y := by
  unfold opair
  ext z
  rw [mem_π₂_iff]
  simp only [sUnion_pair, sInter_pair, ne_eq, union_pair_eq_inter_pair]
  constructor
  · rintro ⟨s, hzs, hsx, hs⟩
    by_cases h : s = y
    · subst h
      exact hzs
    · aesop
  · aesop

@[simp]
theorem opair_injective {x y z w : V} :
    opair x y = opair z w ↔ x = z ∧ y = w := by
  constructor
  · intro h
    have h₁ := congrArg π₁ h
    have h₂ := congrArg π₂ h
    simp at h₁ h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- `x` is the pair `{y, z}` if `∀ t, t ∈ x ↔ t = y ∨ t = z`. -/
protected def _root_.BoundedFormula.eqPair (x y z : α ⊕ Fin n) : BoundedFormula α n :=
  .all (.iff
    (.mem (Sum.inr (Fin.last n)) (termSucc x))
    (.or
      (.eq (Sum.inr (Fin.last n)) (termSucc y))
      (.eq (Sum.inr (Fin.last n)) (termSucc z)))
  )

theorem eq_pair_iff : x = pair y z ↔ ∀ t, t ∈ x ↔ t = y ∨ t = z := by
  rw [ext_iff]
  simp

@[simp]
theorem interpret_eqPair {x y z : α ⊕ Fin n} :
    Interpret V (.eqPair x y z) v l ↔
      interpretTerm V v l x = pair (interpretTerm V v l y) (interpretTerm V v l z) := by
  unfold BoundedFormula.eqPair
  rw [eq_pair_iff]
  simp

/-- `x` is the singleton `{y}` if it is the pair `{y, y}`. -/
protected def _root_.BoundedFormula.eqSingleton (x y : α ⊕ Fin n) : BoundedFormula α n :=
  .eqPair x y y

@[simp]
theorem interpret_eqSingleton {x y : α ⊕ Fin n} :
    Interpret V (.eqSingleton x y) v l ↔
      interpretTerm V v l x = {interpretTerm V v l y} := by
  unfold BoundedFormula.eqSingleton
  simp

/-- `x` is a pair if `∃ y z, ∀ t, t ∈ x ↔ t = y ∨ t = z`. -/
protected def _root_.BoundedFormula.isPair (x : α ⊕ Fin n) : BoundedFormula α n :=
  .exists (.exists (.eqPair
    (termSucc (termSucc x))
    (Sum.inr ⟨n, Nat.lt_add _⟩)
    (Sum.inr (Fin.last (n + 1)))
  ))

@[simp]
theorem interpret_isPair {x : α ⊕ Fin n} :
    Interpret V (.isPair x) v l ↔ IsPair (interpretTerm V v l x) := by
  unfold BoundedFormula.isPair IsPair
  simp

/-- `x` is the ordered pair `(y, z)` if `∃ y' z', y' = {y}, z' = {y, z}, x = {y', z'}`. -/
protected def _root_.BoundedFormula.eqOPair (x y z : α ⊕ Fin n) : BoundedFormula α n :=
  .exists (.exists (
    .and (.and
      (.eqSingleton (Sum.inr ⟨n, Nat.lt_add 1⟩) (termSucc (termSucc y)))
      (.eqPair (Sum.inr ⟨n + 1, Nat.lt_add 0⟩)
        (termSucc (termSucc y)) (termSucc (termSucc z))))
      (.eqPair (termSucc (termSucc x))
        (Sum.inr ⟨n, Nat.lt_add 1⟩) (Sum.inr ⟨n + 1, Nat.lt_add 0⟩))
  ))

@[simp]
theorem interpret_eqOPair {x y z: α ⊕ Fin n} :
    Interpret V (.eqOPair x y z) v l ↔
    interpretTerm V v l x = opair (interpretTerm V v l y) (interpretTerm V v l z) := by
  unfold BoundedFormula.eqOPair opair
  aesop

/-- `x` is a pair if `∃ y z, x = {{y}, {y, z}}`.
More formally, we will write `∃ y z y' z', y' = {y}, z' = {y, z}, x = {y', z'}`. -/
protected def _root_.BoundedFormula.isOPair (x : α ⊕ Fin n) : BoundedFormula α n :=
  .exists (.exists (.eqOPair
    (termSucc (termSucc x))
    (Sum.inr ⟨n, Nat.lt_add 1⟩)
    (Sum.inr ⟨n + 1, Nat.lt_add 0⟩)))

@[simp]
theorem interpret_isOPair {x : α ⊕ Fin n} :
    Interpret V (.isOPair x) v l ↔ IsOPair (interpretTerm V v l x) := by
  unfold BoundedFormula.isOPair IsOPair opair
  aesop

/-- `x` is an ordered pair in `y × z` if `∃ a ∈ y, ∃ b ∈ z, x = (a, b)`. -/
protected def _root_.BoundedFormula.memProd (x y z : α ⊕ Fin n) : BoundedFormula α n :=
  .exists (.exists (.and (.and
    (.mem (Sum.inr ⟨n, Nat.lt_add 1⟩) (termSucc (termSucc y)))
    (.mem (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (termSucc (termSucc z))))
    (.eqOPair (termSucc (termSucc x))
      (Sum.inr ⟨n, Nat.lt_add 1⟩) (Sum.inr ⟨n + 1, Nat.lt_add 0⟩))))

theorem interpret_memProd' {x y z : α ⊕ Fin n} :
    Interpret V (.memProd x y z) v l ↔
    ∃ a ∈ interpretTerm V v l y, ∃ b ∈ interpretTerm V v l z, interpretTerm V v l x = opair a b := by
  unfold BoundedFormula.memProd
  aesop

def prod (x y : V) : V :=
  sep
    (.memProd (Sum.inr 0) (Sum.inl true) (Sum.inl false))
    (fun (i : Bool) => if i then x else y)
    (power (power (x ∪ y)))

theorem mem_prod_iff : z ∈ prod x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = opair a b := by
  unfold prod
  simp only [mem_sep_iff, mem_power_iff, interpret_memProd', interpret_inl, ite_true,
    ite_false, interpret_inr, and_iff_right_iff_imp, forall_exists_index, and_imp]
  rintro a ha b hb rfl
  intro z hz
  rw [opair, mem_pair_iff] at hz
  obtain (rfl | rfl) := hz <;>
  · rw [mem_power_iff]
    intro t ht
    aesop

@[simp]
theorem opair_mem_prod_iff {a b : V} : opair a b ∈ prod x y ↔ a ∈ x ∧ b ∈ y := by
  rw [mem_prod_iff]
  aesop

@[simp]
theorem interpret_isOPairIn {x y z : α ⊕ Fin n} :
    Interpret V (.memProd x y z) v l ↔
    interpretTerm V v l x ∈ prod (interpretTerm V v l y) (interpretTerm V v l z) := by
  rw [mem_prod_iff, interpret_memProd']

end SetTheory
