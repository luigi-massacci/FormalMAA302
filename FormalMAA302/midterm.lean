import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite
import Mathlib.Topology.Basic
import Mathlib.Data.Set.Countable


-- COFINITE TOPOLOGY
section III

open Set

axiom X : Type _

def O : Set (Set X) := {∅} ∪ { U | Set.Finite (Uᶜ)}

lemma O_is_openEmpty : ∅ ∈ O := by
  rw [O]; left; rfl

lemma O_is_openX : univ ∈ O := by
  simp [O] -- worth it to have simp? [O] as example for PRL

lemma O_isOpen_sUnion : ∀ C : Set (Set X), (∀ (U : Set X), U ∈ C → U ∈ O) → (⋃₀ C) ∈ O := by
  intro C hC
  rw [O]
  by_cases emptyC : ⋃₀ C = ∅
  · rw [emptyC]
    left
    rfl
  · right
    push_neg at emptyC
    have h : Set.Finite ((⋃₀ C)ᶜ) := by
      rw [compl_sUnion]
      obtain ⟨U, hU, neU⟩ := nonempty_sUnion.mp (nmem_singleton_empty.mp emptyC)
      have : ⋂₀ (compl '' C) ⊆ Uᶜ := by
        have : Uᶜ ∈  compl '' C := mem_image_of_mem compl hU
        exact sInter_subset_of_mem this
      specialize hC U hU
      cases' hC with emptyU hU
      exfalso
      apply nmem_singleton_empty.mpr neU
      assumption
      exact Finite.subset hU this
    assumption

lemma O_is_openInter : ∀ U V : Set X, U ∈ O → V ∈ O → U ∩ V ∈ O:= by
  intro U V openU openV
  rw [O] at openU openV
  rw [O]
  simp [compl_inter, Finite.union]
  aesop


instance : TopologicalSpace X := by
  constructor
  on_goal 4 => {exact O}
  exact O_is_openX
  exact O_is_openInter
  exact O_isOpen_sUnion

example : CompactSpace X := by
  constructor
  apply isCompact_of_finite_subcover
  intro I cover open_of_cover is_cover
  by_cases emptyCover : ⋃ i : I, (cover i) = ∅
  · use ∅
    rw [emptyCover] at is_cover
    simp [is_cover]
  · obtain ⟨i, hi⟩ := nonempty_iUnion.mp (nmem_singleton_empty.mp emptyCover)
    have hfinite : Set.Finite ((cover i)ᶜ) := by
      have : (cover i) ∈ O := by exact open_of_cover i
      cases' this with empty cofinite
      exfalso
      apply nmem_singleton_empty.mpr hi
      assumption
      assumption
    have h : ∀ x ∈ (cover i)ᶜ, ∃ j : I, x ∈ cover j := by
      intro x hx
      have : x ∈ univ := by exact trivial
      have : x ∈  ⋃ (i : I), cover i := by exact is_cover this
      exact mem_iUnion.mp this
    have : Nonempty I := by exact Nonempty.intro i
    choose! f h using h
    set subcover := {i} ∪  (f '' ((cover i)ᶜ)) with hsub
    have : Set.Finite subcover := by
      rw [hsub]
      apply finite_union.mpr
      constructor
      simp only [finite_singleton]
      exact Finite.image f hfinite
    use (Finite.toFinset this)
    intro x hx
    by_cases hn : Set.Nonempty ((cover i)ᶜ)
    by_cases x ∈ (cover i)
    apply mem_iUnion.mpr
    use i
    simp [h]
    simp [h]
    aesop
    by_cases x ∈ (cover i)
    simp [h]
    have : (cover i)ᶜ = ∅ := by exact not_nonempty_iff_eq_empty.mp hn
    have : x ∉ (cover i)ᶜ := by exact not_of_eq_false (congrArg (Membership.mem x) this)
    contradiction


example (hinf : Infinite X): ¬(T2Space X) := by
  intro HaussX
  have := (t2Space_iff X).mp HaussX
  sorry








end III
