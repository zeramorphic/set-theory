import SetTheory.Axioms

/-!
Development roughly follows *(Introduction to Set Theory* by Karel Hrbacek and Thomas Jech.
-/

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

theorem forall_not_mem (h : ∀ y, y ∉ x) : x = ∅ :=
  by ext; aesop

end SetTheory
