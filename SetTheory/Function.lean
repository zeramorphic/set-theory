import SetTheory.Relation

namespace SetTheory

variable [Zermelo V] {r x y z a b c : V}

/-- A set `f` is a function if all its elements are ordered pairs, and any two pairs of the form
`⟨x, s⟩, ⟨x, t⟩` in `f` have `s = t`. -/
structure IsFunction (f : V) extends IsRelation f : Prop where
  eq : ∀ x s t, opair x s ∈ f → opair x t ∈ f → s = t

/-- A *function* `x ⟶ y` is a relation `f` with domain equal to `x` and range contained in `y`,
such that if `(a, b), (a, c) ∈ f`, we have `b = c`. -/
structure Function (x y : V) where
  graph : V
  isFunction : IsFunction graph
  dom_eq : dom graph = x
  ran_subset : ran graph ⊆ y

infixr:10 " ⟶ " => Function

theorem mem_of_mem_dom (f : a ⟶ b) (hx : x ∈ dom f.graph) : x ∈ a :=
  by rwa [← f.dom_eq]

theorem mem_dom_of_mem (f : a ⟶ b) (hx : x ∈ a) : x ∈ dom f.graph :=
  by rwa [f.dom_eq]

def apply (f x : V) : V := ⋃ image f {x}

instance : CoeFun V (fun _ => V → V) where
  coe := apply

instance : CoeFun (a ⟶ b) (fun _ => V → V) where
  coe f := f.graph

theorem mem_apply_iff {f : V} : y ∈ f x ↔ ∃ z, opair x z ∈ f ∧ y ∈ z := by
  unfold apply
  simp [mem_image_iff]

theorem eq_of_opair_mem_graph (f : a ⟶ b) (h : opair x y ∈ f.graph) : y = f x := by
  ext z
  rw [mem_apply_iff]
  constructor
  · intro h'
    exact ⟨_, h, h'⟩
  · intro ⟨t, ht, ht'⟩
    cases f.isFunction.eq x y t h ht
    exact ht'

theorem opair_mem_graph (f : a ⟶ b) (h : x ∈ a) : opair x (f x) ∈ f.graph := by
  have := mem_dom_of_mem f h
  rw [mem_dom_iff] at this
  rcases this with ⟨y, hy⟩
  cases eq_of_opair_mem_graph f hy
  exact hy

theorem opair_mem_graph_iff (f : a ⟶ b) (h : x ∈ a) : opair x y ∈ f.graph ↔ y = f x := by
  constructor
  · exact eq_of_opair_mem_graph f
  · rintro rfl
    exact opair_mem_graph f h

/-- **Function extensionality**. Two functions are equal if they agree at all inputs in their domains. -/
@[ext]
theorem Function.ext {f g : a ⟶ b} (h : ∀ x ∈ a, f x = g x) : f = g := by
  suffices f.graph = g.graph from by
    cases f
    cases this
    rfl
  ext x
  constructor
  · intro hx
    obtain ⟨x, y, rfl⟩ := f.isFunction.isOPair x hx
    have : x ∈ a := by
      refine mem_of_mem_dom f ?_
      rw [mem_dom_iff]
      exact ⟨y, hx⟩
    rw [opair_mem_graph_iff _ this] at hx ⊢
    rw [hx]
    exact h _ this
  · intro hx
    obtain ⟨x, y, rfl⟩ := g.isFunction.isOPair x hx
    have : x ∈ a := by
      refine mem_of_mem_dom g ?_
      rw [mem_dom_iff]
      exact ⟨y, hx⟩
    rw [opair_mem_graph_iff _ this] at hx ⊢
    rw [hx]
    exact (h _ this).symm

def comp (g : b ⟶ c) (f : a ⟶ b) : a ⟶ c where
  graph := rcomp g.graph f.graph
  isFunction := {
    rcomp_isRelation f.isFunction.toIsRelation with
    eq := by
      intro x s t hs ht
      rw [opair_mem_rcomp_iff] at hs ht
      obtain ⟨u, hgu, hfu⟩ := hs
      obtain ⟨v, hgv, hfv⟩ := ht
      cases f.isFunction.eq x u v hfu hfv
      exact g.isFunction.eq u s t hgu hgv
  }
  dom_eq := by
    rw [dom_rcomp, f.dom_eq]
    rw [g.dom_eq]
    exact f.ran_subset
  ran_subset := subset_trans ran_rcomp g.ran_subset

end SetTheory
