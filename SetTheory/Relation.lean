import SetTheory.OPair

namespace SetTheory

variable [Zermelo V] {r x y z : V}

def IsRelation (r : V) : Prop :=
  ∀ p ∈ r, IsOPair p

/-- `r` is a relation if all elements of `r` are ordered pairs. -/
protected def _root_.BoundedFormula.isRelation (r : α ⊕ Fin n) : BoundedFormula α n :=
  .all (.imp
    (.mem (Sum.inr (Fin.last n)) (termSucc r))
    (.isOPair (Sum.inr (Fin.last n))))

@[simp]
theorem interpret_isRelation {r : α ⊕ Fin n} :
    Interpret V (.isRelation r) v l ↔ IsRelation (interpretTerm V v l r) := by
  unfold BoundedFormula.isRelation IsRelation
  simp

theorem opair_left_mem_sUnion_sUnion (hxyr : opair x y ∈ r) :
    x ∈ ⋃ ⋃ r := by
  simp only [mem_sUnion_iff]
  refine ⟨{x}, ⟨_, hxyr, ?_⟩, ?_⟩
  · simp only [opair, mem_pair_iff, true_or]
  · rw [mem_singleton_iff]

theorem opair_right_mem_sUnion_sUnion (hxyr : opair x y ∈ r) :
    y ∈ ⋃ ⋃ r := by
  simp only [mem_sUnion_iff]
  refine ⟨pair x y, ⟨_, hxyr, ?_⟩, ?_⟩
  · simp only [opair, mem_pair_iff, or_true]
  · exact right_mem_pair

/-- `x` is in the domain of the relation `r` if `∃ z, (x, z) ∈ r`.
More formally we write `∃ z t, t = (x, z), t ∈ r`. -/
protected def _root_.BoundedFormula.memDom (x r : α ⊕ Fin n) : BoundedFormula α n :=
  .exists (.exists (.and
    (.eqOPair (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (termSucc (termSucc x)) (Sum.inr ⟨n, Nat.lt_add 1⟩))
    (.mem (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (termSucc (termSucc r)))))

theorem interpret_memDom' {x r : α ⊕ Fin n} :
    Interpret V (.memDom x r) v l ↔
    ∃ z, opair (interpretTerm V v l x) z ∈ interpretTerm V v l r := by
  unfold BoundedFormula.memDom
  simp

def dom (r : V) : V :=
  sep (.memDom (Sum.inr 0) (Sum.inl ())) (fun (_ : Unit) => r) (⋃ ⋃ r)

theorem mem_dom_iff : x ∈ dom r ↔ ∃ z, opair x z ∈ r := by
  unfold dom
  simp only [mem_sep_iff, interpret_memDom', interpret_inr, interpret_inl,
    and_iff_right_iff_imp, forall_exists_index]
  intro t
  exact opair_left_mem_sUnion_sUnion

@[simp]
theorem interpret_memDom {x r : α ⊕ Fin n} :
    Interpret V (.memDom x r) v l ↔ interpretTerm V v l x ∈ dom (interpretTerm V v l r) := by
  rw [mem_dom_iff, interpret_memDom']

/-- `x` is in the range of the relation `r` if `∃ z, (z, x) ∈ r`.
More formally we write `∃ z t, t = (z, x), t ∈ r`. -/
protected def _root_.BoundedFormula.memRan (x r : α ⊕ Fin n) : BoundedFormula α n :=
  .exists (.exists (.and
    (.eqOPair (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (Sum.inr ⟨n, Nat.lt_add 1⟩) (termSucc (termSucc x)))
    (.mem (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (termSucc (termSucc r)))))

theorem interpret_memRan' {x r : α ⊕ Fin n} :
    Interpret V (.memRan x r) v l ↔
    ∃ z, opair z (interpretTerm V v l x) ∈ interpretTerm V v l r := by
  unfold BoundedFormula.memRan
  simp

def ran (r : V) : V :=
  sep (.memRan (Sum.inr 0) (Sum.inl ())) (fun (_ : Unit) => r) (⋃ ⋃ r)

theorem mem_ran_iff : x ∈ ran r ↔ ∃ z, opair z x ∈ r := by
  unfold ran
  simp only [mem_sep_iff, interpret_memRan', interpret_inr, interpret_inl,
    and_iff_right_iff_imp, forall_exists_index]
  intro t
  exact opair_right_mem_sUnion_sUnion

@[simp]
theorem interpret_memRan {x r : α ⊕ Fin n} :
    Interpret V (.memRan x r) v l ↔ interpretTerm V v l x ∈ ran (interpretTerm V v l r) := by
  rw [mem_ran_iff, interpret_memRan']

/-- `x` is in the image of `y` under the relation `r` if `∃ z ∈ y, (z, x) ∈ r`. -/
protected def _root_.BoundedFormula.memImage (x y r : α ⊕ Fin n) : BoundedFormula α n :=
  .exists (.exists (.and (.and
    (.mem (Sum.inr ⟨n, Nat.lt_add 1⟩) (termSucc (termSucc y)))
    (.eqOPair (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (Sum.inr ⟨n, Nat.lt_add 1⟩) (termSucc (termSucc x))))
    (.mem (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (termSucc (termSucc r)))))

theorem interpret_memImage' {x y r : α ⊕ Fin n} :
    Interpret V (.memImage x y r) v l ↔
    ∃ z ∈ interpretTerm V v l y, opair z (interpretTerm V v l x) ∈ interpretTerm V v l r := by
  unfold BoundedFormula.memImage
  aesop

def image (r y : V) : V :=
  sep
    (.memImage (Sum.inr 0) (Sum.inl false) (Sum.inl true))
    (fun (i : Bool) => if i then r else y)
    (ran r)

theorem mem_image_iff : x ∈ image r y ↔ ∃ z ∈ y, opair z x ∈ r := by
  unfold image
  simp only [mem_sep_iff, mem_ran_iff, interpret_memImage']
  aesop

@[simp]
theorem interpret_memImage {x y r : α ⊕ Fin n} :
    Interpret V (.memImage x y r) v l ↔
    interpretTerm V v l x ∈ image (interpretTerm V v l r) (interpretTerm V v l y) := by
  rw [mem_image_iff, interpret_memImage']

/-- `x` is in the preimage of `y` under the relation `r` if `∃ z ∈ y, (x, z) ∈ r`. -/
protected def _root_.BoundedFormula.memPreimage (x y r : α ⊕ Fin n) : BoundedFormula α n :=
  .exists (.exists (.and (.and
    (.mem (Sum.inr ⟨n, Nat.lt_add 1⟩) (termSucc (termSucc y)))
    (.eqOPair (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (termSucc (termSucc x)) (Sum.inr ⟨n, Nat.lt_add 1⟩)))
    (.mem (Sum.inr ⟨n + 1, Nat.lt_add 0⟩) (termSucc (termSucc r)))))

theorem interpret_memPreimage' {x y r : α ⊕ Fin n} :
    Interpret V (.memPreimage x y r) v l ↔
    ∃ z ∈ interpretTerm V v l y, opair (interpretTerm V v l x) z ∈ interpretTerm V v l r := by
  unfold BoundedFormula.memPreimage
  aesop

def preimage (r y : V) : V :=
  sep
    (.memPreimage (Sum.inr 0) (Sum.inl false) (Sum.inl true))
    (fun (i : Bool) => if i then r else y)
    (dom r)

theorem mem_preimage_iff : x ∈ preimage r y ↔ ∃ z ∈ y, opair x z ∈ r := by
  unfold preimage
  simp only [mem_sep_iff, mem_dom_iff, interpret_memPreimage']
  aesop

@[simp]
theorem interpret_memPreimage {x y r : α ⊕ Fin n} :
    Interpret V (.memPreimage x y r) v l ↔
    interpretTerm V v l x ∈ preimage (interpretTerm V v l r) (interpretTerm V v l y) := by
  rw [mem_preimage_iff, interpret_memPreimage']

/-- `x` is in the inverse of the relation `r` if `x = (y, z)` and `(z, y) ∈ r`. -/
protected def _root_.BoundedFormula.memInverse (x r : α ⊕ Fin n) : BoundedFormula α n :=
  -- ∃ y z t
  .exists (.exists (.exists (.and (.and
    -- x = (y, z)
    (.eqOPair (termSucc (termSucc (termSucc x)))
      (Sum.inr ⟨n, Nat.lt_add 2⟩) (Sum.inr ⟨n + 1, Nat.lt_add 1⟩))
    -- t = (z, y)
    (.eqOPair (Sum.inr ⟨n + 2, Nat.lt_add 0⟩)
      (Sum.inr ⟨n + 1, Nat.lt_add 1⟩) (Sum.inr ⟨n, Nat.lt_add 2⟩)))
    -- t ∈ r
    (.mem (Sum.inr ⟨n + 2, Nat.lt_add 0⟩) (termSucc (termSucc (termSucc r)))))))

theorem interpret_memInverse' {x r : α ⊕ Fin n} :
    Interpret V (.memInverse x r) v l ↔
    ∃ y z, interpretTerm V v l x = opair y z ∧ opair z y ∈ interpretTerm V v l r := by
  unfold BoundedFormula.memInverse
  aesop

def inverse (r : V) : V :=
  sep
    (.memInverse (Sum.inr 0) (Sum.inl ()))
    (fun (_ : Unit) => r)
    (prod (ran r) (dom r))

theorem mem_inverse_iff : x ∈ inverse r ↔ ∃ y z, x = opair y z ∧ opair z y ∈ r := by
  unfold inverse
  simp only [mem_sep_iff, interpret_memInverse']
  constructor
  · aesop
  · rintro ⟨a, b, rfl, ha⟩
    refine ⟨?_, by aesop⟩
    rw [mem_prod_iff]
    refine ⟨a, ?_, b, ?_, rfl⟩
    · rw [mem_ran_iff]
      exact ⟨b, ha⟩
    · rw [mem_dom_iff]
      exact ⟨a, ha⟩

@[simp]
theorem interpret_memInverse {x r : α ⊕ Fin n} :
    Interpret V (.memInverse x r) v l ↔
    interpretTerm V v l x ∈ inverse (interpretTerm V v l r) := by
  rw [mem_inverse_iff, interpret_memInverse']

@[aesop norm]
theorem inverse_inverse (hr : IsRelation r) : inverse (inverse r) = r := by
  ext x
  simp only [mem_inverse_iff]
  constructor
  · aesop
  · intro h
    obtain ⟨y, z, rfl⟩ := hr x h
    exact ⟨y, z, rfl, z, y, rfl, h⟩

@[simp]
theorem image_inverse : image (inverse r) x = preimage r x := by
  ext y
  simp only [mem_image_iff, mem_preimage_iff, mem_inverse_iff]
  aesop

@[simp]
theorem preimage_inverse : preimage (inverse r) x = image r x := by
  ext y
  simp only [mem_image_iff, mem_preimage_iff, mem_inverse_iff]
  aesop

/-- `x` is in the composition of the relations `s` and `r` if
`∃ a b c, x = (a, c) ∧ (b, c) ∈ s ∧ (a, b) ∈ r`. -/
protected def _root_.BoundedFormula.memRComp (x s r : α ⊕ Fin n) : BoundedFormula α n :=
  -- ∃ a b c d e
  .exists (.exists (.exists (.exists (.exists (.and (.and (.and (.and
    -- x = (a, c)
    (.eqOPair (termSucc (termSucc (termSucc (termSucc (termSucc x)))))
      (Sum.inr ⟨n, Nat.lt_add 4⟩) (Sum.inr ⟨n + 2, Nat.lt_add 2⟩))
    -- d = (a, b)
    (.eqOPair (Sum.inr ⟨n + 3, Nat.lt_add 1⟩)
      (Sum.inr ⟨n, Nat.lt_add 4⟩) (Sum.inr ⟨n + 1, Nat.lt_add 3⟩)))
    -- e = (b, c)
    (.eqOPair (Sum.inr ⟨n + 4, Nat.lt_add 0⟩)
      (Sum.inr ⟨n + 1, Nat.lt_add 3⟩) (Sum.inr ⟨n + 2, Nat.lt_add 2⟩)))
    -- e ∈ s
    (.mem (Sum.inr ⟨n + 4, Nat.lt_add 0⟩)
      (termSucc (termSucc (termSucc (termSucc (termSucc s)))))))
    -- d ∈ r
    (.mem (Sum.inr ⟨n + 3, Nat.lt_add 1⟩)
      (termSucc (termSucc (termSucc (termSucc (termSucc r)))))))))))

theorem interpret_memRComp' {x s r : α ⊕ Fin n} :
    Interpret V (.memRComp x s r) v l ↔
    ∃ a b c,
      interpretTerm V v l x = opair a c ∧
      opair b c ∈ interpretTerm V v l s ∧
      opair a b ∈ interpretTerm V v l r := by
  unfold BoundedFormula.memRComp
  simp [and_assoc]

/-- Composition of relations. -/
def rcomp (s r : V) : V :=
  sep
    (.memRComp (Sum.inr 0) (Sum.inl true) (Sum.inl false))
    (fun (i : Bool) => if i then s else r)
    (prod (dom r) (ran s))

theorem mem_rcomp_iff : x ∈ rcomp s r ↔ ∃ a b c, x = opair a c ∧ opair b c ∈ s ∧ opair a b ∈ r := by
  unfold rcomp
  simp only [mem_sep_iff, interpret_memRComp', interpret_inr, interpret_inl, ite_true, ite_false,
    and_iff_right_iff_imp, forall_exists_index, and_imp]
  rintro a b c rfl hs hr
  rw [mem_prod_iff]
  refine ⟨a, ?_, c, ?_, rfl⟩
  · rw [mem_dom_iff]
    exact ⟨b, hr⟩
  · rw [mem_ran_iff]
    exact ⟨b, hs⟩

@[simp]
theorem opair_mem_rcomp_iff : opair a c ∈ rcomp s r ↔ ∃ b, opair b c ∈ s ∧ opair a b ∈ r := by
  rw [mem_rcomp_iff]
  aesop

theorem interpret_memRComp {x s r : α ⊕ Fin n} :
    Interpret V (.memRComp x s r) v l ↔
    interpretTerm V v l x ∈ rcomp (interpretTerm V v l s) (interpretTerm V v l r) := by
  rw [mem_rcomp_iff, interpret_memRComp']

theorem rcomp_assoc : rcomp (rcomp t s) r = rcomp t (rcomp s r) := by
  ext
  simp only [mem_rcomp_iff]
  aesop

theorem rcomp_isRelation (hr : IsRelation r) : IsRelation (rcomp s r) := by
  intro x hx
  rw [mem_rcomp_iff] at hx
  aesop

theorem dom_rcomp (h : ran r ⊆ dom s) : dom (rcomp s r) = dom r := by
  ext t
  simp only [mem_dom_iff, mem_rcomp_iff, opair_injective]
  constructor
  · rintro ⟨z, _, b, _, ⟨rfl, rfl⟩, _, hc⟩
    exact ⟨_, hc⟩
  · rintro ⟨b, hb⟩
    have : b ∈ ran r := by
      rw [mem_ran_iff]
      exact ⟨t, hb⟩
    have := h this
    rw [mem_dom_iff] at this
    obtain ⟨z, hz⟩ := this
    exact ⟨z, _, b, _, ⟨rfl, rfl⟩, hz, hb⟩

theorem ran_rcomp : ran (rcomp s r) ⊆ ran s := by
  intro t
  simp only [mem_ran_iff, mem_rcomp_iff, opair_injective]
  rintro ⟨z, _, b, _, ⟨rfl, rfl⟩, hc, _⟩
  exact ⟨_, hc⟩

/-- `x` is a member of the identity relation on `y` if `∃ z ∈ y, x = (z, z)`. -/
protected def _root_.BoundedFormula.memId (x y : α ⊕ Fin n) : BoundedFormula α n :=
  .exists (.and
    (.mem (Sum.inr (Fin.last n)) (termSucc y))
    (.eqOPair (termSucc x) (Sum.inr (Fin.last n)) (Sum.inr (Fin.last n))))

theorem interpret_memId' {x y : α ⊕ Fin n} :
    Interpret V (.memId x y) v l ↔
    ∃ z ∈ interpretTerm V v l y, interpretTerm V v l x = opair z z := by
  unfold BoundedFormula.memId
  simp

def id (x : V) : V :=
  sep
    (.memId (Sum.inr 0) (Sum.inl ()))
    (fun (_ : Unit) => x)
    (prod x x)

theorem mem_id_iff : y ∈ id x ↔ ∃ z ∈ x, y = opair z z := by
  unfold id
  simp only [mem_sep_iff, interpret_memId']
  aesop

@[simp]
theorem interpret_memId {x y : α ⊕ Fin n} :
    Interpret V (.memId x y) v l ↔
    interpretTerm V v l x ∈ id (interpretTerm V v l y) := by
  rw [mem_id_iff, interpret_memId']

end SetTheory
