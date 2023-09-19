import Std.Data.Fin.Basic
import SetTheory.SetTheory

/-- `BoundedFormula α n` is the type of formulas in the language of set theory,
with free variables indexed by `α` and up to `n` additional free "local" variables. -/
inductive BoundedFormula (α : Type) : Nat → Type
  | protected falsum {n} : BoundedFormula α n
  | protected eq {n} (x y : α ⊕ Fin n) : BoundedFormula α n
  | protected mem {n} (x y : α ⊕ Fin n) : BoundedFormula α n
  | protected imp {n} (p q : BoundedFormula α n) : BoundedFormula α n
  | protected all {n} (p : BoundedFormula α (n + 1)) : BoundedFormula α n

open BoundedFormula SetTheory

variable [SetTheory V]

/-- `Formula α` is the type of formulas in the language of set theory,
with all free variables indexed by `α`. -/
@[reducible]
def Formula (α : Type) :=
  BoundedFormula α 0

/-- `Sentence` is the type of formulae in the language of set theory with no free variables. -/
@[reducible]
def Sentence :=
  Formula Empty

def termSucc : α ⊕ Fin n → α ⊕ Fin (n + 1)
  | .inl a => .inl a
  | .inr k => .inr k.castSucc

@[simp]
theorem termSucc_inl :
    termSucc (Sum.inl a : α ⊕ Fin n) = Sum.inl a :=
  rfl

@[simp]
theorem termSucc_inr :
    termSucc (Sum.inr k : α ⊕ Fin n) = Sum.inr k.castSucc :=
  rfl

def termSum : α ⊕ Fin n → (α ⊕ β) ⊕ Fin n
  | .inl a => .inl (.inl a)
  | .inr k => .inr k

@[simp]
theorem termSum_inl :
    (termSum (Sum.inl a) : (α ⊕ β) ⊕ Fin n) = Sum.inl (Sum.inl a) :=
  rfl

@[simp]
theorem termSum_inr :
    (termSum (Sum.inr k) : (α ⊕ β) ⊕ Fin n) = Sum.inr k :=
  rfl

namespace BoundedFormula

def sum (β : Type _) : BoundedFormula α n → BoundedFormula (α ⊕ β) n
  | .falsum => .falsum
  | .eq x y => .eq (termSum x) (termSum y)
  | .mem x y => .mem (termSum x) (termSum y)
  | .imp p q => (p.sum β).imp (q.sum β)
  | .all p => (p.sum β).all

@[simp]
theorem sum_falsum :
    (.falsum : BoundedFormula α n).sum β = .falsum :=
  rfl

@[simp]
theorem sum_eq :
    (.eq x y : BoundedFormula α n).sum β = .eq (termSum x) (termSum y) :=
  rfl

@[simp]
theorem sum_mem :
    (.mem x y : BoundedFormula α n).sum β = .mem (termSum x) (termSum y) :=
  rfl

@[simp]
theorem sum_imp :
    (.imp p q : BoundedFormula α n).sum β = (p.sum β).imp (q.sum β) :=
  rfl

@[simp]
theorem sum_all :
    (.all p : BoundedFormula α n).sum β = (p.sum β).all :=
  rfl

end BoundedFormula

/-- Define a function on `α ⊕ β` by giving separate definitions on `α` and `β`.
TODO: Once `aesop`'s `std` is bumped, we can use the defn from `Std.Data.Sum.Basic`. -/
protected def Sum.elim {α β γ} (f : α → γ) (g : β → γ) : α ⊕ β → γ :=
  fun x => Sum.casesOn x f g

@[simp] theorem Sum.elim_inl (f : α → γ) (g : β → γ) (x : α) :
    Sum.elim f g (inl x) = f x := rfl

@[simp] theorem Sum.elim_inr (f : α → γ) (g : β → γ) (x : β) :
    Sum.elim f g (inr x) = g x := rfl

@[simp]
theorem not_not (p : Prop) : ¬¬p ↔ p := by
  by_cases p <;> aesop

@[simp]
theorem not_forall (p : α → Prop) : ¬(∀ x, p x) ↔ ∃ x, ¬p x := by
  constructor
  · by_contra
    aesop
  · aesop

theorem or_iff (p q : Prop) : p ∨ q ↔ ¬p → q := by
  by_cases p <;> aesop

theorem and_iff (p q : Prop) : p ∧ q ↔ ¬(p → ¬q) := by
  by_cases p <;> aesop

/-- Adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc` comes from
`cons` (i.e., adding an element to the left of a tuple) read in reverse order. -/
def Fin.snoc (l : Fin n → α) (x : α) : Fin (n + 1) → α :=
  fun i => if h : i.val < n then l ⟨i, h⟩ else x

theorem Fin.false_of_fin_zero (x : Fin 0) : False :=
  Nat.not_lt_zero x x.isLt

@[simp]
theorem Fin.last_val : (Fin.last n).val = n := rfl

@[simp]
theorem Fin.snoc_castSucc :
    Fin.snoc (l : Fin n → α) x k.castSucc = l k := by
  rw [Fin.snoc, dif_pos]
  rfl

@[simp]
theorem lt_add_two {n : Nat} : n < n + 2 := by
  rw [Nat.lt_succ]
  exact Nat.le_succ_of_le (Nat.le_refl n)

@[simp]
theorem lt_add_three {n : Nat} : n < n + 3 := by
  rw [Nat.lt_succ]
  exact Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_refl n))

@[simp]
theorem Fin.snoc_apply :
    Fin.snoc (l : Fin n → α) x (Fin.last n) = x := by
  simp only [snoc]
  aesop

@[simp]
theorem Fin.snoc_snoc_apply :
    Fin.snoc (Fin.snoc (l : Fin n → α) x) y ⟨n, lt_add_two⟩ = x := by
  simp only [snoc]
  aesop

@[simp]
theorem Fin.snoc_snoc_snoc_apply :
    Fin.snoc (Fin.snoc (Fin.snoc (l : Fin n → α) x) y) z ⟨n, lt_add_three⟩ = x := by
  simp only [snoc]
  aesop

@[simp]
theorem Fin.zero_snoc_zero (l : Fin 0 → α) : Fin.snoc l x 0 = x := rfl

@[simp]
theorem Fin.one_snoc_zero (l : Fin 1 → α) : Fin.snoc l x 0 = l 0 := rfl

@[simp]
theorem Fin.one_snoc_one (l : Fin 1 → α) : Fin.snoc l x 1 = x := rfl

@[simp]
theorem Fin.two_snoc_zero (l : Fin 2 → α) : Fin.snoc l x 0 = l 0 := rfl

@[simp]
theorem Fin.two_snoc_one (l : Fin 2 → α) : Fin.snoc l x 1 = l 1 := rfl

@[simp]
theorem Fin.two_snoc_two (l : Fin 2 → α) : Fin.snoc l x 2 = x := rfl

namespace SetTheory

def interpretTerm (V : Type _) (v : α → V) (l : Fin n → V) : α ⊕ Fin n → V
  | .inl a => v a
  | .inr k => l k

/-- Interpret a bounded formula in the language of set theory. -/
def Interpret (V : Type _) [SetTheory V] {α : Type} :
    {n : Nat} → BoundedFormula α n → (α → V) → (Fin n → V) → Prop
  | _, .falsum, _, _ => False
  | _, .eq x y, v, l => interpretTerm V v l x = interpretTerm V v l y
  | _, .mem x y, v, l => interpretTerm V v l x ∈ interpretTerm V v l y
  | _, .imp p q, v, l => Interpret V p v l → Interpret V q v l
  | _, .all p, v, l => ∀ x : V, Interpret V p v (Fin.snoc l x)

def InterpretFormula (V : Type _) [SetTheory V] {α : Type} (p : Formula α) (v : α → V) : Prop :=
  Interpret V p v (fun x => x.false_of_fin_zero.elim)

@[simp]
theorem interpret_inl :
    interpretTerm p v l (Sum.inl a) = v a :=
  rfl

@[simp]
theorem interpret_inr :
    interpretTerm p v l (Sum.inr k) = l k :=
  rfl

@[simp]
theorem interpret_snoc_termSucc :
    interpretTerm V v (Fin.snoc l y) (termSucc x) = interpretTerm V v l x :=
  by aesop

@[simp]
theorem interpret_falsum : Interpret V .falsum v l ↔ False :=
  Iff.rfl

@[simp]
theorem interpret_eq :
    Interpret V (.eq x y) v l ↔
    interpretTerm V v l x = interpretTerm V v l y :=
  Iff.rfl

@[simp]
theorem interpret_mem :
    Interpret V (.mem x y) v l ↔
    interpretTerm V v l x ∈ interpretTerm V v l y :=
  Iff.rfl

@[simp]
theorem interpret_imp :
    Interpret V (.imp p q) v l ↔
    Interpret V p v l → Interpret V q v l :=
  Iff.rfl

@[simp]
theorem interpret_all :
    Interpret V (.all p) v l ↔
    ∀ x : V, Interpret V p v (Fin.snoc l x) :=
  Iff.rfl

@[simp]
theorem interpret_termSum_elim {p : α ⊕ Fin n} :
    interpretTerm V (Sum.elim vα vβ) l (termSum p) =
    interpretTerm V vα l p :=
  by cases p <;> rfl

@[simp]
theorem interpret_sum_elim :
    Interpret V (.sum β p) (Sum.elim vα vβ) l ↔
    Interpret V p vα l :=
  by induction p <;> aesop

end SetTheory

protected def BoundedFormula.not (p : BoundedFormula α n) : BoundedFormula α n :=
  p.imp .falsum

@[simp]
theorem SetTheory.interpret_not :
    Interpret V (.not p) v l ↔ ¬Interpret V p v l :=
  Iff.rfl

protected def BoundedFormula.ne (x y : α ⊕ Fin n) : BoundedFormula α n :=
  .not (.eq x y)

@[simp]
theorem SetTheory.ne :
    Interpret V (.ne x y) v l ↔ interpretTerm V v l x ≠ interpretTerm V v l y :=
  Iff.rfl

protected def BoundedFormula.or (p q : BoundedFormula α n) : BoundedFormula α n :=
  p.not.imp q

@[simp]
theorem SetTheory.interpret_or :
    Interpret V (.or p q) v l ↔ Interpret V p v l ∨ Interpret V q v l := by
  rw [or_iff]
  rfl

protected def BoundedFormula.and (p q : BoundedFormula α n) : BoundedFormula α n :=
  (p.imp q.not).not

@[simp]
theorem SetTheory.interpret_and :
    Interpret V (.and p q) v l ↔ Interpret V p v l ∧ Interpret V q v l := by
  rw [and_iff]
  rfl

protected def BoundedFormula.iff (p q : BoundedFormula α n) : BoundedFormula α n :=
  (p.imp q).and (q.imp p)

@[simp]
theorem SetTheory.interpret_iff :
    Interpret V (.iff p q) v l ↔ (Interpret V p v l ↔ Interpret V q v l) := by
  unfold BoundedFormula.iff
  aesop

protected def BoundedFormula.subset (x y : α ⊕ Fin n) : BoundedFormula α n :=
  .all (.imp
    (.mem (Sum.inr (Fin.last n)) (termSucc x))
    (.mem (Sum.inr (Fin.last n)) (termSucc y)))

@[simp]
theorem SetTheory.interpret_subset :
    Interpret V (.subset x y) v l ↔
    interpretTerm V v l x ⊆ interpretTerm V v l y := by
  unfold BoundedFormula.subset
  aesop

protected def BoundedFormula.exists (p : BoundedFormula α (n + 1)) : BoundedFormula α n :=
  p.not.all.not

@[simp]
theorem SetTheory.interpret_exists :
    Interpret V (.exists p) v l ↔
    ∃ x : V, Interpret V p v (Fin.snoc l x) := by
  unfold BoundedFormula.exists
  aesop
