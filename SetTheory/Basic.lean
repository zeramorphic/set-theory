import SetTheory.Axioms

/-!
Development roughly follows *(Introduction to Set Theory* by Karel Hrbacek and Thomas Jech.
-/

namespace SetTheory

variable [MorseKelley M] {x y z : M}

theorem left_mem_pair : IsSet x → IsSet y → x ∈ pair x y :=
  by aesop

theorem right_mem_pair : IsSet x → IsSet y → x ∈ pair x y :=
  by aesop

@[simp]
theorem pair_self : pair x x = {x} :=
  rfl

@[aesop safe]
theorem pair_nonemptyClass : IsSet x → IsSet y → NonemptyClass (pair x y) :=
  fun hx hy => ⟨x, left_mem_pair hx hy⟩

/-- The intersection of a set `x`. Constructed as the class `{y | ∀ t, t ∈ x → y ∈ t}`. -/
def sInter (x : M) : M :=
  ofFormula (.all (.imp
    (.mem (Sum.inr 1) (Sum.inl ()))
    (.mem (Sum.inr 0) (Sum.inr 1))))
  (fun (_ : Unit) => x)

/-- We will use the notation `⋂` for set intersection in this project. -/
prefix:110 "⋂ " => sInter

@[aesop norm]
theorem mem_sInter_iff (hx : NonemptyClass x) :
    y ∈ ⋂ x ↔ ∀ t ∈ x, y ∈ t := by
  unfold sInter
  simp
  intro h
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, h z hz⟩

theorem subset_sInter : NonemptyClass x → y ∈ x → ⋂ x ⊆ y := by
  intro hx h z hz
  aesop

theorem sInter_isSet (hx : NonemptyClass x) : IsSet (⋂ x) := by
  obtain ⟨y, hy⟩ := hx
  refine subset_isSet (subset_sInter ⟨y, hy⟩ hy) ⟨x, hy⟩

/-- The intersection of two sets `x` and `y`. -/
instance : Inter M where
  inter x y := sInter (pair x y)

@[simp]
theorem mem_inter_iff (hx : IsSet x) (hy : IsSet y) :
    z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y := by
  show z ∈ sInter (pair x y) ↔ z ∈ x ∧ z ∈ y
  rw [mem_sInter_iff (pair_nonemptyClass hx hy)]
  aesop

@[simp]
theorem sUnion_pair : ⋃ pair x y = x ∪ y := rfl

@[simp]
theorem sInter_pair : ⋂ pair x y = x ∩ y := rfl

/-- The axiom scheme of *separation*. -/
def sep (p : BoundedFormula α 1) (v : α → M) (x : M) : M :=
  ofFormula (
    (p.sum Unit).and
    (.mem (Sum.inr 0) (Sum.inl (Sum.inr ()))))
  (Sum.elim v (fun _ => x))

@[simp]
theorem mem_sep_iff : x ∈ sep p v y ↔ x ∈ y ∧ Interpret M p v (fun _ => x) := by
  unfold sep
  aesop

@[simp]
theorem union_self (hx : IsSet x) : x ∪ x = x :=
  by ext; aesop

@[simp]
theorem inter_self (hx : IsSet x) : x ∩ x = x :=
  by ext; aesop

theorem union_pair_eq_inter_pair (hx : IsSet x) (hy : IsSet y) :
    {x} ∪ pair x y = {x} ∩ pair x y ↔ x = y := by
  constructor
  · intro h
    rw [ext_iff] at h
    have := (h y).mp ?_
    · rw [mem_inter_iff (singleton_isSet hx) (pair_isSet hx hy),
        mem_singleton_iff hx] at this
      exact this.1.symm
    · rw [mem_union_iff (singleton_isSet hx) (pair_isSet hx hy)]
      aesop
  · rintro rfl
    simp [union_self (singleton_isSet hx), inter_self (singleton_isSet hx)]

/-- The first projection of a Kuratowski ordered pair. -/
def π₁ (x : M) : M :=
  ⋃ ⋂ x

/-- The second projection of a Kuratowski ordered pair. -/
def π₂ (x : M) : M :=
  ⋃ sep
    (.imp
      (.ne (Sum.inl true) (Sum.inl false))
      (.not (.mem (Sum.inr 0) (Sum.inl false))))
    (fun i => if i then ⋃ x else ⋂ x) (⋃ x)

theorem mem_π₂_iff : y ∈ π₂ x ↔ ∃ z, y ∈ z ∧ z ∈ ⋃ x ∧ (⋃ x ≠ ⋂ x → z ∉ ⋂ x) := by
  unfold π₂
  aesop

@[simp]
theorem π₁_opair (hx : IsSet x) (hy : IsSet y) : π₁ (opair x y) = x := by
  unfold π₁ opair
  ext z
  simp [mem_inter_iff (singleton_isSet hx) (pair_isSet hx hy)]
  aesop

@[simp]
theorem π₂_opair (hx : IsSet x) (hy : IsSet y) : π₂ (opair x y) = y := by
  unfold opair
  ext z
  rw [mem_π₂_iff]
  simp only [sUnion_pair, sInter_pair, ne_eq, union_pair_eq_inter_pair hx hy]
  constructor
  · rintro ⟨s, hzs, hsx, hs⟩
    by_cases h : s = y
    · subst h
      exact hzs
    rw [mem_union_iff (singleton_isSet hx) (pair_isSet hx hy),
      mem_singleton_iff hx] at hsx
    cases hsx with
    | inl hsx =>
      subst hsx
      exfalso
      refine hs h ?_
      rw [mem_inter_iff (singleton_isSet hx) (pair_isSet hx hy)]
      aesop
    | inr hsx =>
      rw [mem_pair_iff hx hy] at hsx
      cases hsx with
      | inl hsx =>
        subst hsx
        exfalso
        refine hs h ?_
        rw [mem_inter_iff (singleton_isSet hx) (pair_isSet hx hy)]
        aesop
      | inr hsx =>
        subst hsx
        exact hzs
  · intro hzy
    refine ⟨y, hzy, ?_, ?_⟩
    · rw [mem_union_iff (singleton_isSet hx) (pair_isSet hx hy),
        mem_pair_iff hx hy]
      exact Or.inr (Or.inr rfl)
    · intro h
      refine (fun h' => h ?_)
      rw [mem_inter_iff (singleton_isSet hx) (pair_isSet hx hy)] at h'
      aesop

@[simp]
theorem opair_injective {x y z w : M} (hx : IsSet x) (hy : IsSet y) (hz : IsSet z) (hw : IsSet w) :
    opair x y = opair z w ↔ x = z ∧ y = w := by
  constructor
  · intro h
    have h₁ := congrArg π₁ h
    have h₂ := congrArg π₂ h
    simp [π₁_opair hx hy, π₁_opair hz hw] at h₁
    simp [π₂_opair hx hy, π₂_opair hz hw] at h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem forall_not_mem (h : ∀ y, y ∉ x) : x = ∅ :=
  by ext; aesop

theorem subset_univ : x ⊆ univ :=
  by intro; aesop

def russellClass : M :=
  ofFormula (.not (.mem (Sum.inr 0) (Sum.inr 0))) (fun (i : Empty) => i.elim)

@[simp]
theorem mem_russellClass_iff :
    x ∈ (russellClass : M) ↔ IsSet x ∧ x ∉ x := by
  unfold russellClass
  simp

theorem russellClass_not_mem (h : russellClass ∈ (russellClass : M)) :
    russellClass ∉ (russellClass : M) := by
  rw [mem_russellClass_iff] at h
  exact h.2

theorem russellClass_mem
    (h₁ : IsSet (russellClass : M)) (h₂ : russellClass ∉ (russellClass : M)) :
    russellClass ∈ (russellClass : M) := by
  rw [mem_russellClass_iff, not_and, not_not] at h₂
  exact h₂ h₁

/-- The Russell class is not a set. -/
theorem russellClass_not_isSet : ¬IsSet (russellClass : M) := by
  intro h
  by_cases h' : russellClass ∈ (russellClass : M)
  · exact russellClass_not_mem h' h'
  · exact h' (russellClass_mem h h')

/-- The universe is not a set. -/
theorem univ_not_isSet : ¬IsSet (univ : M) := by
  intro h
  exact russellClass_not_isSet (subset_isSet subset_univ h)

end SetTheory
