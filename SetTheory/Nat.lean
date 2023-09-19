import SetTheory.Function

namespace SetTheory

variable [Zermelo V]

/-- `x` is the union of `y` and `z` if `∀ t, t ∈ x ↔ t ∈ y ∨ t ∈ z`. -/
protected def _root_.BoundedFormula.eqUnion (x y z : α ⊕ Fin n) : BoundedFormula α n :=
  .all (.iff
    (.mem (Sum.inr (Fin.last n)) (termSucc x))
    (.or
      (.mem (Sum.inr (Fin.last n)) (termSucc y))
      (.mem (Sum.inr (Fin.last n)) (termSucc z))))

@[simp]
theorem interpret_eqUnion {x y z : α ⊕ Fin n} :
    Interpret V (.eqUnion x y z) v l ↔
    interpretTerm V v l x = interpretTerm V v l y ∪ interpretTerm V v l z := by
  unfold BoundedFormula.eqUnion
  rw [ext_iff]
  simp

/-- `x` is the successor of `y` if `x = y ∪ {y}`. -/
protected def _root_.BoundedFormula.eqSucc (x y : α ⊕ Fin n) : BoundedFormula α n :=
  -- ∃ t
  .exists (.and
    -- t = {y}
    (.eqSingleton (Sum.inr (Fin.last n)) (termSucc y))
    -- x = y ∪ {y}
    (.eqUnion (termSucc x) (termSucc y) (Sum.inr (Fin.last n)))
  )

@[simp]
theorem interpret_eqSucc {x y : α ⊕ Fin n} :
    Interpret V (.eqSucc x y) v l ↔
    interpretTerm V v l x = succ (interpretTerm V v l y) := by
  unfold BoundedFormula.eqSucc succ
  simp

/-- `x` is the empty set if `∀ y, y ∉ x`. -/
protected def _root_.BoundedFormula.eqEmpty (x : α ⊕ Fin n) : BoundedFormula α n :=
  .all (.not (.mem (Sum.inr (Fin.last n)) (termSucc x)))

@[simp]
theorem interpret_eqEmpty {x : α ⊕ Fin n} :
    Interpret V (.eqEmpty x) v l ↔ interpretTerm V v l x = ∅ := by
  unfold BoundedFormula.eqEmpty
  rw [eq_empty_iff_forall_not_mem]
  simp

/-- `x` is successor-closed if whenever `t ∈ x`, we have `t ∪ {t} ∈ x`. -/
protected def _root_.BoundedFormula.succClosed (x : α ⊕ Fin n) : BoundedFormula α n :=
  .all (.imp
    -- ∀ t ∈ x
    (.mem (Sum.inr (Fin.last n)) (termSucc x))
    -- ∃ u
    (.exists (.and
      -- u = succ t
      (.eqSucc (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (Sum.inr ⟨n, Nat.lt_add 1⟩))
      -- u ∈ x
      (.mem (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (termSucc (termSucc x)))
    )))

@[simp]
theorem interpret_succClosed {x : α ⊕ Fin n} :
    Interpret V (.succClosed x) v l ↔
    ∀ y ∈ interpretTerm V v l x, succ y ∈ interpretTerm V v l x := by
  unfold BoundedFormula.succClosed
  simp

theorem inductive_iff (x : V) : Inductive x ↔ ∅ ∈ x ∧ ∀ y ∈ x, succ y ∈ x := by
  constructor
  · intro h
    exact ⟨h.empty_mem, h.succ_mem⟩
  · intro h
    exact ⟨h.1, h.2⟩

/-- `x` is an inductive set if it contains an empty set and is successor-closed. -/
protected def _root_.BoundedFormula.isInductive (x : α ⊕ Fin n) : BoundedFormula α n :=
  .and
    (.exists (.and
      (.eqEmpty (Sum.inr (Fin.last n)))
      (.mem (Sum.inr (Fin.last n)) (termSucc x))))
    (.succClosed x)

@[simp]
theorem interpret_isInductive {x : α ⊕ Fin n} :
    Interpret V (.isInductive x) v l ↔ Inductive (interpretTerm V v l x) := by
  unfold BoundedFormula.isInductive
  rw [inductive_iff]
  simp

/-- `x` is a natural number if it is a member of every inductive set. -/
protected def _root_.BoundedFormula.isNat (x : α ⊕ Fin n) : BoundedFormula α n :=
  .all (.imp
    (.isInductive (Sum.inr (Fin.last n)))
    (.mem (termSucc x) (Sum.inr (Fin.last n))))

theorem interpret_isNat' {x : α ⊕ Fin n} :
    Interpret V (.isNat x) v l ↔ ∀ y : V, Inductive y → interpretTerm V v l x ∈ y := by
  unfold BoundedFormula.isNat
  simp

/-- The natural numbers. -/
def ω : V :=
  sep
    (.isNat (Sum.inr 0))
    (fun (i : Empty) => i.elim)
    Infinity.inductiveSet

theorem mem_ω_iff : n ∈ (ω : V) ↔ ∀ s : V, Inductive s → n ∈ s := by
  unfold ω
  simp only [mem_sep_iff, interpret_isNat', interpret_inr, and_iff_right_iff_imp]
  intro hn
  exact hn _ Infinity.inductiveSet_inductive

@[simp]
theorem interpret_isNat {x : α ⊕ Fin n} :
    Interpret V (.isNat x) v l ↔ interpretTerm V v l x ∈ (ω : V) := by
  rw [mem_ω_iff, interpret_isNat']

theorem empty_mem_ω : ∅ ∈ (ω : V) := by
  rw [mem_ω_iff]
  intro s hs
  exact hs.empty_mem

theorem succ_mem_ω (hn : n ∈ (ω : V)) : succ n ∈ (ω : V) := by
  rw [mem_ω_iff] at hn ⊢
  intro s hs
  exact hs.succ_mem n (hn s hs)

theorem ω_inductive : Inductive (ω : V) :=
  ⟨empty_mem_ω, fun _ => succ_mem_ω⟩

def nat_to_ω : Nat → V
  | 0 => ∅
  | n + 1 => succ (nat_to_ω n)

/-- The metatheoretic naturals embed in the model `V`. -/
instance : OfNat V n where
  ofNat := nat_to_ω n

theorem zero_def : (0 : V) = ∅ := rfl

theorem one_def : (1 : V) = {∅} := by
  show ∅ ∪ {∅} = {∅}
  simp

theorem ofNat_succ {n : Nat} : (OfNat.ofNat (n + 1) : V) = succ (OfNat.ofNat n) := rfl

/-- We say that `f` is an *attempt* of the recursion scheme given by the zero case `Z`
and the successor case `S` if
* `f` is a function with domain `0 ∈ dom f ∈ ω`;
* `f 0 = Z`; and
* `f (succ n) = S (f n)`.
-/
structure IsAttempt (f Z S : V) : Prop where
  isFunction : IsFunction f
  dom_mem_ω : dom f ∈ (ω : V)
  zero_mem_dom : 0 ∈ dom f
  zero_spec : opair 0 Z ∈ f
  succ_spec (n : V) (hn₁ : n ∈ (ω : V)) (hn₂ : n ∈ dom f) (hn₃ : succ n ∈ dom f) :
    (succ n) (S (f n)) ∈ f

protected def _root_.BoundedFormula.isAttempt (f Z S : α ⊕ Fin n) : BoundedFormula α n :=
  .and (.and (.and (.and
    -- isFunction
    (.isFunction f)
    -- dom_mem_ω
    (.exists (.and
      -- ∃ d ∈ ω
      (.isNat (Sum.inr (Fin.last n)))
      -- ∀ t, t ∈ dom f ↔ t ∈ d
      (.all (.iff
        (.memDom (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (termSucc (termSucc f)))
        (.mem (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (Sum.inr ⟨n, Nat.lt_add 1⟩)))))))
    -- zero_mem_dom
    (.all (.imp
      -- ∀ x, x = ∅ → x ∈ dom f
      (.eqEmpty (Sum.inr (Fin.last n)))
      (.memDom (Sum.inr (Fin.last n)) (termSucc f)))))
    -- zero_spec
    (.all (.imp
      -- ∀ x, x = ∅ →
      (.eqEmpty (Sum.inr (Fin.last n)))
      -- ∃ t
      (.exists (.and
        -- t = (x, Z)
        _
        -- t ∈ f
        _)))))
    -- succ_spec
    _

end SetTheory
