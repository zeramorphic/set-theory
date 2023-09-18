import Std.Data.Fin.Basic
import SetTheory.Basic

/-- `BoundedFormula α n` is the type of formulas in the language of set theory,
with free variables indexed by `α` and up to `n` additional free "local" variables. -/
inductive BoundedFormula (α : Type) : Nat → Type
  | protected falsum {n} : BoundedFormula α n
  | protected equal {n} (x y : α ⊕ Fin n) : BoundedFormula α n
  | protected mem {n} (x y : α ⊕ Fin n) : BoundedFormula α n
  | protected imp {n} (p q : BoundedFormula α n) : BoundedFormula α n
  | protected all {n} (p : BoundedFormula α (n + 1)) : BoundedFormula α n

open BoundedFormula SetTheory

variable [SetTheory M]

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
theorem Fin.snoc_last :
    Fin.snoc (l : Fin n → α) x (Fin.last n) = x := by
  rw [Fin.snoc, dif_neg]
  rw [Fin.last_val]
  intro h
  exact Nat.ne_of_lt h rfl

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

def interpretTerm (M : Type _) (v : α → M) (l : Fin n → M) : α ⊕ Fin n → M
  | .inl a => v a
  | .inr k => l k

/-- Interpret a bounded formula in the language of set theory. -/
def Interpret (M : Type _) [SetTheory M] {α : Type} :
    {n : Nat} → BoundedFormula α n → (α → M) → (Fin n → M) → Prop
  | _, .falsum, _, _ => False
  | _, .equal x y, v, l => interpretTerm M v l x = interpretTerm M v l y
  | _, .mem x y, v, l => interpretTerm M v l x ∈ interpretTerm M v l y
  | _, .imp p q, v, l => Interpret M p v l → Interpret M q v l
  | _, .all p, v, l => ∀ x : M, Interpret M p v (Fin.snoc l x)

def InterpretFormula (M : Type _) [SetTheory M] {α : Type} (p : Formula α) (v : α → M) : Prop :=
  Interpret M p v (fun x => x.false_of_fin_zero.elim)

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
    interpretTerm M v (Fin.snoc l y) (termSucc x) = interpretTerm M v l x :=
  by aesop

@[simp]
theorem interpret_falsum : Interpret M .falsum v l ↔ False :=
  Iff.rfl

@[simp]
theorem interpret_equal :
    Interpret M (.equal x y) v l ↔
    interpretTerm M v l x = interpretTerm M v l y :=
  Iff.rfl

@[simp]
theorem interpret_mem :
    Interpret M (.mem x y) v l ↔
    interpretTerm M v l x ∈ interpretTerm M v l y :=
  Iff.rfl

@[simp]
theorem interpret_imp :
    Interpret M (.imp p q) v l ↔
    Interpret M p v l → Interpret M q v l :=
  Iff.rfl

@[simp]
theorem interpret_all :
    Interpret M (.all p) v l ↔
    ∀ x : M, Interpret M p v (Fin.snoc l x) :=
  Iff.rfl

end SetTheory

protected def BoundedFormula.not (p : BoundedFormula α n) : BoundedFormula α n :=
  p.imp .falsum

@[simp]
theorem SetTheory.interpret_not :
    Interpret M (.not p) v l ↔ ¬Interpret M p v l :=
  Iff.rfl

protected def BoundedFormula.or (p q : BoundedFormula α n) : BoundedFormula α n :=
  p.not.imp q

@[simp]
theorem SetTheory.interpret_or :
    Interpret M (.or p q) v l ↔ Interpret M p v l ∨ Interpret M q v l := by
  rw [or_iff]
  rfl

protected def BoundedFormula.and (p q : BoundedFormula α n) : BoundedFormula α n :=
  (p.imp q.not).not

@[simp]
theorem SetTheory.interpret_and :
    Interpret M (.and p q) v l ↔ Interpret M p v l ∧ Interpret M q v l := by
  rw [and_iff]
  rfl

protected def BoundedFormula.iff (p q : BoundedFormula α n) : BoundedFormula α n :=
  (p.imp q).and (q.imp p)

@[simp]
theorem SetTheory.interpret_iff :
    Interpret M (.iff p q) v l ↔ (Interpret M p v l ↔ Interpret M q v l) := by
  unfold BoundedFormula.iff
  aesop

protected def BoundedFormula.subset (x y : α ⊕ Fin n) : BoundedFormula α n :=
  .all (.imp
    (.mem (Sum.inr (Fin.last n)) (termSucc x))
    (.mem (Sum.inr (Fin.last n)) (termSucc y)))

@[simp]
theorem SetTheory.interpret_subset :
    Interpret M (.subset x y) v l ↔
    interpretTerm M v l x ⊆ interpretTerm M v l y := by
  unfold BoundedFormula.subset
  aesop

protected def BoundedFormula.exists (p : BoundedFormula α (n + 1)) : BoundedFormula α n :=
  p.not.all.not

@[simp]
theorem SetTheory.interpret_exists :
    Interpret M (.exists p) v l ↔
    ∃ x : M, Interpret M p v (Fin.snoc l x) := by
  unfold BoundedFormula.exists
  aesop

protected def BoundedFormula.isSet (x : α ⊕ Fin n) : BoundedFormula α n :=
  .exists (.mem (termSucc x) (Sum.inr (Fin.last n)))

@[simp]
theorem SetTheory.interpret_isSet :
    Interpret M (.isSet x) v l ↔ IsSet (interpretTerm M v l x) := by
  unfold BoundedFormula.isSet IsSet
  aesop
