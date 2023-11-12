import Mathlib.Tactic

open Set

variable {α : Type u}

instance : CompactSpace (CofiniteTopology α) := by
  constructor
  apply isCompact_of_finite_subcover
  intro I cover open_of_cover is_cover
  by_cases emptyCover : Set.Nonempty (⋃ i : I, (cover i))
  · obtain ⟨i, hi⟩ := nonempty_iUnion.mp emptyCover
    have : Nonempty I := Nonempty.intro i
    have : ∀ x ∈ (cover i)ᶜ, ∃ j : I, x ∈ cover j :=
      fun x _ ↦ mem_iUnion.mp (is_cover (mem_univ x))
    choose! f this using this
    let subcover := {i} ∪  (f '' ((cover i)ᶜ))
    have : Set.Finite subcover :=
      finite_union.mpr ⟨finite_singleton _, Finite.image f (open_of_cover i hi)⟩
    use (Finite.toFinset this)
    intro x _
    by_cases x ∈ (cover i) <;> aesop
  · rw [not_nonempty_iff_eq_empty] at emptyCover
    aesop

open TopologicalSpace

example {X : Type*} [T : TopologicalSpace X] {A : Set (Set X)} (hA : IsTopologicalBasis A) :
    T = sSup {S : TopologicalSpace X | A ⊆ S.IsOpen} := by
  ext O
  constructor
  intro hO
  have := (IsTopologicalBasis.isOpen_iff hA).mp hO
  apply isOpen_iff_mem_nhds.mpr
  intro x xO
  obtain ⟨S, hSA, xS, hSO⟩ := this x xO
  apply mem_nhds_iff.mpr
  use S
  constructor
  assumption
  constructor
  apply isOpen_mk.mpr
  intro K
  intro hK
  aesop
  assumption
  intro hO
  apply (IsTopologicalBasis.isOpen_iff hA).mpr
  intro x xO
  simp [setOf_isOpen_sSup] at hO
  have := isOpen_mk.mp hO
  use O
  constructor
  rw at this

  constructor
  assumption
  trivial
