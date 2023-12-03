import Mathlib.Tactic


def S (a b : ℤ ) := {n | n % a = b}

def O : Set (Set ℤ) := {∅} ∪ { U | ∀n ∈ U, ∃ m : ℤ, 1 ≤ m ∧ S m n ⊆ U }

open Int


lemma O_is_openEmpty : ∅ ∈ O := by
  simp [O]

lemma O_is_openX : Set.univ ∈ O := by
  simp [O]
  use 1


lemma O_isOpen_sUnion : ∀ C : Set (Set ℤ), (∀ (U : Set ℤ), U ∈ C → U ∈ O) → (⋃₀ C) ∈ O := by
  intro C hC
  simp [O]
  intro n S S_inC n_inS
  specialize hC _ S_inC
  simp [O] at hC
  rcases hC n n_inS with ⟨m, hm, h_sub⟩
  use m
  refine ⟨hm, ?_⟩
  intro k hk
  rw [Set.mem_sUnion]
  use S
  refine ⟨S_inC, ?_⟩
  apply subset_trans h_sub
  rfl
  assumption

lemma O_is_openInter : ∀ U V : Set ℤ , U ∈ O → V ∈ O → U ∩ V ∈ O:= by
  simp [O]
  intro U V hU hV n nU nV
  rcases hU n nU with ⟨u, hu⟩
  rcases hV n nV with ⟨v, hv⟩
  use u*v
  constructor
  apply mul_le_mul (hu.1) (hv.1) (by linarith) (by linarith [hu.1])
  constructor
  simp [S]
  simp [S] at hu
  refine subset_trans ?_ hu.2
  simp
  intro a ha
