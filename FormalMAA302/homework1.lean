import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Basic
import Mathlib.Data.Set.Countable

open Set

-- We axiomatize the existance of some set X. This isn't stricly necessary,
-- but otherwise the definition of O would quantify over an arbitrary X and I
-- would have to write O(X) everywhere.

-- Lean is based on a flavour of type theory, but in practice it doesn;t make much difference
-- just note that x : X ("x is a term of type X") is essentially the same as
-- x ∈ X (pretending X is a set) for our purposes. Set(X) then denotes the type of Sets with elements in X,
-- so S : Set(X) is the same as S ⊆ X, and finally Set(Set(X)) are sets of sets of elements of X,
-- so O : Set(Set(X)) is the same as O ∈ P(X)

-- if P is a proposition (something like ∀x, Q(x)) then p : P means that p is a proof of P


-- Click with your cursor before / after a line to see the state of the proof
-- before / after the instruction is executed
-- You can also move using the up/down arrows

axiom X : Type _

 -- The predicate that a Set is countable is called Set.Countable
 -- (to distinguish it from just "Countable", which is a notion of countability for Types)

def O : Set (Set X) := {∅} ∪ { U | Set.Countable (Uᶜ)}

lemma O_is_openEmpty : ∅ ∈ O := by
  rw [O] -- Can be commented, not necessary. Replace O with its definition
  left -- (To prove x ∈ A ∪ B I can prove x ∈ A or x ∈ B. "left" says I want to prove the left side :)
  rfl -- ≈ "hey, this is true by definition" (there are some subtleties that don't matter here)

-- The logicians turnstyle symbol "⊢" denotes what we have to prove.
-- Everything above (the "local context") are the hypothesis we have assumed / proved

-- For a given type A, univ A corresponds to A (as a set) inside Set(A)
-- it is usually not necessary to specify A since lean can infer it on its own from the context
#check univ

lemma O_is_openX : univ ∈ O := by
  rw [O]
  --The theorem that the complement of the universe is empty is called compl_univ
  -- you can hover over any theorem name to get information about it
  -- Here I need to specify X (with the @ notation) since lean cannot infer it
  have h₁ : (@univ X)ᶜ = ∅ := by exact compl_univ
  have h₂ : Set.Countable (∅ : Set X) := by exact countable_empty

  right
  -- More rewriting of equalities. This means "replace the expression in h₂ matching the right side of h₁
  -- left side of h₁." The default (without the arrow) is to match on the left and replace with the right.
  rw [← h₁] at h₂
  rw [mem_setOf_eq] -- the stament that a ∈ {x | P(x)} iff P(a)
  assumption



-- There is a shorter proof without spelling out the intermediate steps:
lemma O_is_openX_short : univ ∈ O := by
  simp only [O, mem_union, Or.inr, mem_setOf_eq, compl_univ, countable_empty]

-- The automation in lean is actually good enough to find all those lemmas on its own,
-- after being supplied the definition of O
lemma O_is_openX_auto : univ ∈ O := by
  simp [O]

-- if C is a set of sets, ⋃₀C  is the union of it's elements. (That is we avoid indexing C
-- and going through an indexed union, though the proof would work just as fine like that too)

-- Arbitrary unions of open sets are open:
lemma O_isOpen_sUnion : ∀ C : Set (Set X), (∀ (U : Set X), U ∈ C → U ∈ O) → (⋃₀ C) ∈ O := by
  -- Before a statement of the form ∀x, P(x),
  -- "intro x" creates a variable x in the hypothesis in the style "let x be arbitrary, ..."
  intro C
  -- Before a statement of the kind "P → Q", intro p moves P to the hypothesis
  -- note that we will get a new term p : P in the context, that is *a proof* of P
  intro hC
  rw [O]
  by_cases emptyC : ⋃₀ C = ∅ -- We very rapidly to away with case of an empty union
  · rw [emptyC]
    left
    rfl
  · right
    push_neg at emptyC --this is just for aestetic purposes

    have h : Set.Countable ((⋃₀ C)ᶜ) := by
      rw [compl_sUnion] -- De Morgan's law

    -- This bit is essentially the proof that arbitrary intersections
    -- of countables are countable, unfortunately I couldn't liquidate it in one line
    -- In any case we walk through the various consequences of a nonempty intersection, etc
      obtain ⟨U, hU, neU⟩ := nonempty_sUnion.mp (nmem_singleton_empty.mp emptyC)
      -- note I don't actually need to always name intermediate lemmas
      -- have : Prop will add a new lemma called "this"
      have : ⋂₀ (compl '' C) ⊆ Uᶜ := by
        have : Uᶜ ∈  compl '' C := mem_image_of_mem compl hU
        exact sInter_subset_of_mem this
      apply Set.Countable.mono this
      specialize hC U hU
      rcases hC with emptyU | hC
      exfalso
      apply nmem_singleton_empty.mpr neU
      assumption
      assumption

    -- Now that we know the complement is countable, we're done.
    assumption

lemma O_is_openInter : ∀ U V : Set X, U ∈ O → V ∈ O → U ∩ V ∈ O:= by
  intro U V openU openV
  apply (mem_union _ _ _).mpr
  -- From now on the proof is rather boring. We go thorugh all the cases considering
  -- What happens if either one of U or V is empty,
  rw [O] at openU openV
  rcases openU with emptyU | openU
  · rw [emptyU, empty_inter]
    left
    rfl
  · rcases openV with emptyV | openV
    · rw [emptyV, inter_empty]
      left
      rfl
    right
    -- Countable unions of countables are countable
    · have : Set.Countable (Uᶜ ∪ Vᶜ) := by
        exact countable_union.mpr ⟨(mem_setOf.mp openU), (mem_setOf.mp openV)⟩

    -- More De Morgan
      have h : (U ∩ V)ᶜ = (Uᶜ ∪ Vᶜ) := by exact compl_inter U V
      rw [← h] at this
      assumption

instance : TopologicalSpace X := by
  constructor
  on_goal 4 => {exact O}
  exact O_is_openX
  exact O_is_openInter
  exact O_isOpen_sUnion

example : Nat.Prime 5 := by
  sorry
-- ... and we are done!
