import SetTheory.Axioms

namespace SetTheory

variable [Zermelo V] {x y z : V}

theorem left_mem_pair : x ∈ pair x y :=
  by simp

theorem right_mem_pair : y ∈ pair x y :=
  by simp

@[simp]
theorem pair_self : pair x x = {x} :=
  rfl

@[simp]
theorem pair_nonemptyClass : NonemptySet (pair x y) :=
  ⟨x, left_mem_pair⟩

/-- The intersection of a set `x`. Constructed as the set `{y ∈ ⋃ x | ∀ t, t ∈ x → y ∈ t}`. -/
def sInter (x : V) : V :=
  sep
  (.all (.imp
    (.mem (Sum.inr 1) (Sum.inl ()))
    (.mem (Sum.inr 0) (Sum.inr 1))))
  (fun (_ : Unit) => x)
  (⋃ x)

/-- We will use the notation `⋂` for set intersection in this project. -/
prefix:110 "⋂ " => sInter

@[simp]
theorem mem_sInter_iff :
    y ∈ ⋂ x ↔ NonemptySet x ∧ ∀ t ∈ x, y ∈ t := by
  unfold sInter NonemptySet
  aesop

theorem subset_sInter : NonemptySet x → y ∈ x → ⋂ x ⊆ y := by
  intro hx h z hz
  aesop

/-- The intersection of two sets `x` and `y`. -/
instance : Inter V where
  inter x y := ⋂ pair x y

@[simp]
theorem mem_inter_iff :
    z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y := by
  show z ∈ ⋂ pair x y ↔ z ∈ x ∧ z ∈ y
  simp

@[simp]
theorem sUnion_pair : ⋃ pair x y = x ∪ y := rfl

@[simp]
theorem sInter_pair : ⋂ pair x y = x ∩ y := rfl

@[simp]
theorem union_self : x ∪ x = x :=
  by ext; simp

@[simp]
theorem inter_self : x ∩ x = x :=
  by ext; simp

theorem union_pair_eq_inter_pair :
    {x} ∪ pair x y = {x} ∩ pair x y ↔ x = y := by
  constructor
  · intro h
    rw [ext_iff] at h
    have := (h y).mp ?_
    · rw [mem_inter_iff, mem_singleton_iff] at this
      exact this.1.symm
    · simp
  · rintro rfl
    simp

theorem forall_not_mem (h : ∀ y, y ∉ x) : x = ∅ :=
  by ext; aesop

theorem eq_empty_iff_forall_not_mem : x = ∅ ↔ ∀ y, y ∉ x :=
  ⟨by aesop, forall_not_mem⟩

@[simp]
theorem subset_rfl : x ⊆ x :=
  fun _ hz => hz

theorem subset_of_eq (h : x = y) : x ⊆ y :=
  by subst h; exact subset_rfl

theorem subset_antisymm (h₁ : x ⊆ y) (h₂ : y ⊆ x) : x = y :=
  by ext; aesop

theorem subset_trans (h₁ : x ⊆ y) (h₂ : y ⊆ z) : x ⊆ z :=
  fun _ h => h₂ (h₁ h)

/-- The Russell set of a given set `x` is `{y ∈ x | y ∉ y}`. -/
def russellSet (x : V) :=
  sep
    (.not (.mem (Sum.inr 0) (Sum.inr 0)))
    (fun (i : Empty) => i.elim)
    x

theorem russellSet_subset (x : V) :
    russellSet x ⊆ x := by
  unfold russellSet
  intro y hy
  aesop

theorem mem_russellSet_iff : y ∈ russellSet x ↔ y ∈ x ∧ y ∉ y := by
  unfold russellSet
  simp

theorem russellSet_not_mem (x : V) : russellSet x ∉ x := by
  intro h
  by_cases h' : russellSet x ∈ russellSet x
  · have := mem_russellSet_iff.mp h'
    exact this.2 h'
  · have := h'
    rw [mem_russellSet_iff, not_and, not_not] at this
    exact h' (this h)

/-- **Russell's paradox**. The universe is not a set. -/
theorem univ_not_set (x : V) : ∃ y, y ∉ x := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact russellSet_not_mem x (h _)

/-- The power set of any set is not a subset of the set. -/
theorem power_not_subset (x : V) : ¬power x ⊆ x := by
  intro h
  refine russellSet_not_mem x (h ?_)
  rw [mem_power_iff]
  exact russellSet_subset x

theorem power_ne (x : V) : power x ≠ x := by
  intro h
  exact (power_not_subset x) (subset_of_eq h)

theorem inter_comm : x ∩ y = y ∩ x :=
  by ext; aesop

theorem union_comm : x ∪ y = y ∪ x :=
  by ext; aesop

theorem inter_assoc : x ∩ y ∩ z = x ∩ (y ∩ z) :=
  by ext; aesop

theorem union_assoc : x ∪ y ∪ z = x ∪ (y ∪ z) :=
  by ext; aesop

theorem inter_distrib_left : x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z) :=
  by ext; aesop

theorem inter_distrib_right : (x ∪ y) ∩ z = (x ∩ z) ∪ (y ∩ z) :=
  by ext; aesop

theorem union_distrib_left : x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z) :=
  by ext; aesop

theorem union_distrib_right : (x ∩ y) ∪ z = (x ∪ z) ∩ (y ∪ z) :=
  by ext; aesop

@[simp]
theorem inter_empty : x ∩ ∅ = ∅ :=
  by ext; simp

@[simp]
theorem empty_inter : ∅ ∩ x = ∅ :=
  by ext; simp

@[simp]
theorem union_empty : x ∪ ∅ = x :=
  by ext; simp

@[simp]
theorem empty_union : ∅ ∪ x = x :=
  by ext; simp

end SetTheory
