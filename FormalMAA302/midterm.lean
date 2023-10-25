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
  simp [O]

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



end III
