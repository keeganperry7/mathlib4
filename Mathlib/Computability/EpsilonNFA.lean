/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Yaël Dillies
-/
import Mathlib.Computability.NFA

#align_import computability.epsilon_NFA from "leanprover-community/mathlib"@"28aa996fc6fb4317f0083c4e6daf79878d81be33"

/-!
# Epsilon Nondeterministic Finite Automata

This file contains the definition of an epsilon Nondeterministic Finite Automaton (`εNFA`), a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in a
regular set by evaluating the string over every possible path, also having access to ε-transitions,
which can be followed without reading a character.
Since this definition allows for automata with infinite states, a `Fintype` instance must be
supplied for true `εNFA`'s.
-/


open Set

open Computability

-- "ε_NFA"
set_option linter.uppercaseLean3 false

universe u v

/-- An `εNFA` is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `Set` of states and can make ε-transitions by
  inputing `none`.
  Since this definition allows for Automata with infinite states, a `Fintype` instance must be
  supplied for true `εNFA`'s. -/
structure εNFA (α : Type u) (σ : Type v) where
  /-- Transition function. The automaton is rendered non-deterministic by this transition function
  returning `Set σ` (rather than `σ`), and ε-transitions are made possible by taking `Option α`
  (rather than `α`). -/
  step : σ → Option α → Set σ
  /-- Starting states. -/
  start : Set σ
  /-- Set of acceptance states. -/
  accept : Set σ
#align ε_NFA εNFA

variable {α : Type u} {σ σ' : Type v} (M : εNFA α σ) {S : Set σ} {x : List α} {s : σ} {a : α}

namespace εNFA

/-- The `εClosure` of a set is the set of states which can be reached by taking a finite string of
ε-transitions from an element of the set. -/
inductive εClosure (S : Set σ) : Set σ
  | base : ∀ s ∈ S, εClosure S s
  | step : ∀ (s), ∀ t ∈ M.step s none, εClosure S s → εClosure S t
#align ε_NFA.ε_closure εNFA.εClosure

@[simp]
theorem subset_εClosure (S : Set σ) : S ⊆ M.εClosure S :=
  εClosure.base
#align ε_NFA.subset_ε_closure εNFA.subset_εClosure

@[simp]
theorem εClosure_empty : M.εClosure ∅ = ∅ :=
  eq_empty_of_forall_not_mem fun s hs ↦ by induction hs <;> assumption
#align ε_NFA.ε_closure_empty εNFA.εClosure_empty

@[simp]
theorem εClosure_univ : M.εClosure univ = univ :=
  eq_univ_of_univ_subset <| subset_εClosure _ _
#align ε_NFA.ε_closure_univ εNFA.εClosure_univ

/-- `M.stepSet S a` is the union of the ε-closure of `M.step s a` for all `s ∈ S`. -/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.εClosure (M.step s a)
#align ε_NFA.step_set εNFA.stepSet

variable {M}

@[simp]
theorem mem_stepSet_iff : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.εClosure (M.step t a) := by
  simp_rw [stepSet, mem_iUnion₂, exists_prop]
#align ε_NFA.mem_step_set_iff εNFA.mem_stepSet_iff

@[simp]
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by
  simp_rw [stepSet, mem_empty_iff_false, iUnion_false, iUnion_empty]
#align ε_NFA.step_set_empty εNFA.stepSet_empty

variable (M)

/-- `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element
of `S`. -/
def evalFrom (start : Set σ) : List α → Set σ :=
  List.foldl M.stepSet (M.εClosure start)
#align ε_NFA.eval_from εNFA.evalFrom

@[simp]
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = M.εClosure S :=
  rfl
#align ε_NFA.eval_from_nil εNFA.evalFrom_nil

@[simp]
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet (M.εClosure S) a :=
  rfl
#align ε_NFA.eval_from_singleton εNFA.evalFrom_singleton

@[simp]
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  rw [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]
#align ε_NFA.eval_from_append_singleton εNFA.evalFrom_append_singleton

@[simp]
theorem evalFrom_empty (x : List α) : M.evalFrom ∅ x = ∅ := by
  induction' x using List.reverseRecOn with x a ih
  · rw [evalFrom_nil, εClosure_empty]
  · rw [evalFrom_append_singleton, ih, stepSet_empty]
#align ε_NFA.eval_from_empty εNFA.evalFrom_empty

/-- `M.eval x` computes all possible paths through `M` with input `x` starting at an element of
`M.start`. -/
def eval :=
  M.evalFrom M.start
#align ε_NFA.eval εNFA.eval

@[simp]
theorem eval_nil : M.eval [] = M.εClosure M.start :=
  rfl
#align ε_NFA.eval_nil εNFA.eval_nil

@[simp]
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet (M.εClosure M.start) a :=
  rfl
#align ε_NFA.eval_singleton εNFA.eval_singleton

@[simp]
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _
#align ε_NFA.eval_append_singleton εNFA.eval_append_singleton

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : Language α :=
  { x | ∃ S ∈ M.accept, S ∈ M.eval x }
#align ε_NFA.accepts εNFA.accepts

@[simp]
theorem mem_accepts (x : List α) : x ∈ M.accepts ↔ ∃ S ∈ M.accept, S ∈ M.evalFrom M.start x := by rfl

/-! ### Conversions between `εNFA` and `NFA` -/


/-- `M.toNFA` is an `NFA` constructed from an `εNFA` `M`. -/
def toNFA : NFA α σ where
  step S a := M.εClosure (M.step S a)
  start := M.εClosure M.start
  accept := M.accept
#align ε_NFA.to_NFA εNFA.toNFA

@[simp]
theorem toNFA_evalFrom_match (start : Set σ) :
    M.toNFA.evalFrom (M.εClosure start) = M.evalFrom start :=
  rfl
#align ε_NFA.to_NFA_eval_from_match εNFA.toNFA_evalFrom_match

@[simp]
theorem toNFA_correct : M.toNFA.accepts = M.accepts :=
  rfl
#align ε_NFA.to_NFA_correct εNFA.toNFA_correct

theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card (Set σ) ≤ List.length x) :
    ∃ a b c, x = a ++ b ++ c ∧
      a.length + b.length ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts :=
  M.toNFA.pumping_lemma hx hlen
#align ε_NFA.pumping_lemma εNFA.pumping_lemma

end εNFA

namespace NFA

/-- `M.toεNFA` is an `εNFA` constructed from an `NFA` `M` by using the same start and accept
  states and transition functions. -/
def toεNFA (M : NFA α σ) : εNFA α σ where
  step s a := a.casesOn' ∅ fun a ↦ M.step s a
  start := M.start
  accept := M.accept
#align NFA.to_ε_NFA NFA.toεNFA

@[simp]
theorem toεNFA_εClosure (M : NFA α σ) (S : Set σ) : M.toεNFA.εClosure S = S := by
  ext a
  refine' ⟨_, εNFA.εClosure.base _⟩
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩)
  · exact h
  · cases h
#align NFA.to_ε_NFA_ε_closure NFA.toεNFA_εClosure

@[simp]
theorem toεNFA_evalFrom_match (M : NFA α σ) (start : Set σ) :
    M.toεNFA.evalFrom start = M.evalFrom start := by
  rw [evalFrom, εNFA.evalFrom, toεNFA_εClosure]
  suffices εNFA.stepSet (toεNFA M) = stepSet M by rw [this]
  ext S s
  simp only [stepSet, εNFA.stepSet, exists_prop, Set.mem_iUnion]
  apply exists_congr
  simp only [and_congr_right_iff]
  intro _ _
  rw [M.toεNFA_εClosure]
  rfl
#align NFA.to_ε_NFA_eval_from_match NFA.toεNFA_evalFrom_match

@[simp]
theorem toεNFA_correct (M : NFA α σ) : M.toεNFA.accepts = M.accepts := by
  rw [εNFA.accepts, εNFA.eval, toεNFA_evalFrom_match]
  rfl
#align NFA.to_ε_NFA_correct NFA.toεNFA_correct

end NFA

/-! ### Regex-like operations -/


namespace εNFA

instance : Zero (εNFA α σ) :=
  ⟨⟨fun _ _ ↦ ∅, ∅, ∅⟩⟩

instance : One (εNFA α σ) :=
  ⟨⟨fun _ _ ↦ ∅, univ, univ⟩⟩

instance : Inhabited (εNFA α σ) :=
  ⟨0⟩

variable (P : εNFA α σ) (Q : εNFA α σ')

def char [DecidableEq α] (a : α) : εNFA α (Option Unit) :=
  {
    step := fun s =>
      match s with
      | none => fun b => if a ∈ b then { some () } else ∅
      | some _ => fun _ => ∅
    start := { none }
    accept := { some () }
  }

def add : εNFA α (Set σ × Set σ') := (P.toNFA.toDFA.add Q.toNFA.toDFA).toNFA.toεNFA

def mul : εNFA α (σ ⊕ σ') :=
{
  step := fun p c q =>
    match c with
    | none => match (p, q) with
      | (Sum.inl p, Sum.inl q) => P.step p none q
      | (Sum.inl p, Sum.inr q) => P.accept p ∧ Q.start q
      | (Sum.inr _, Sum.inl _) => False
      | (Sum.inr p, Sum.inr q) => Q.step p none q
    | some c => match (p, q) with
      | (Sum.inl p, Sum.inl q) => P.step p c q
      | (Sum.inr p, Sum.inr q) => Q.step p c q
      | (_, _) => False
  start := Sum.inl '' P.start
  accept := Sum.inr '' Q.accept
}

def star [DecidablePred (· ∈ P.accept)] : εNFA α (Option σ) :=
{
  step := fun s a =>
    match s with
    | none => match a with
      | none => some '' P.start
      | some _ => ∅
    | some s => match a with
      | none => if s ∈ P.accept
        then insert none (some '' P.step s none)
        else some '' P.step s none
      | some a => some '' P.step s a
  start := { none }
  accept := { none }
}

@[simp]
theorem step_zero (s a) : (0 : εNFA α σ).step s a = ∅ :=
  rfl
#align ε_NFA.step_zero εNFA.step_zero

@[simp]
theorem step_one (s a) : (1 : εNFA α σ).step s a = ∅ :=
  rfl
#align ε_NFA.step_one εNFA.step_one

@[simp]
theorem step_char_none_left [DecidableEq α] (a : α) (b : Option α) :
  (char a).step none b = if a ∈ b then { some () } else ∅ :=
  rfl

@[simp]
theorem step_char_some [DecidableEq α] (a : α) (b : Option α) (s : Unit) :
  (char a).step (some s) b = ∅ := rfl

@[simp]
theorem step_char_none_some [DecidableEq α] (a : α) :
  (char a).step none (some a) = { some () } := if_pos rfl

@[simp]
theorem step_char_none_some_ne [DecidableEq α] (a : α) :
  ∀ b, a ∉ b → (char a).step none b = ∅ := by
  intros b h
  dsimp
  rw [if_neg]
  exact h

@[simp]
theorem step_char_none_right [DecidableEq α] (a : α) (s : Option Unit) :
  (char a).step s none = ∅ := by
  match s with
  | none => simp
  | some s => rfl

@[simp]
theorem step_mul_left_not_accept (a : α) :
  ∀s ∉ P.accept, (P.mul Q).step (Sum.inl s) a = (Sum.inl '' P.step s a) := by
  intros _ _
  ext x
  unfold mul
  cases' x with p q
  . simp at *
    rfl
  . simp at *
    intro h
    exact h

@[simp]
theorem step_mul_left_some :
  (P.mul Q).step (Sum.inl s) (some a) = (Sum.inl '' P.step s (some a)) := by
  ext x
  unfold mul
  cases' x with p q
  . simp at *
    rfl
  . simp at *
    intro h
    exact h

@[simp]
theorem step_mul_left_none_accept :
  ∀s ∈ P.accept, (P.mul Q).step (Sum.inl s) none = (Sum.inl '' P.step s none) ∪ (Sum.inr '' Q.start) := by
  intros _ h
  unfold mul
  ext x
  constructor
  . cases' x with p q
    . simp at *
      intro h1
      exact h1
    . simp at *
      intro h1
      exact h1.2
  . cases' x with p q
    . simp at *
      intro h1
      exact h1
    . simp at *
      intro h1
      exact ⟨h, h1⟩

@[simp]
theorem step_mul_right (s : σ') (a : Option α) :
  (P.mul Q).step (Sum.inr s) a = (Sum.inr '' Q.step s a) := by
  ext x
  cases' x with p q
  . unfold mul
    simp at *
    intro h
    cases a
    . exact h
    . exact h
  . unfold mul
    simp at *
    cases a
    . rfl
    . rfl

@[simp]
theorem stepSet_one (s : Set σ) (a : α) : (1 : εNFA α σ).stepSet s a = ∅ := by
  rw [stepSet]
  simp

@[simp]
theorem start_zero : (0 : εNFA α σ).start = ∅ :=
  rfl
#align ε_NFA.start_zero εNFA.start_zero

@[simp]
theorem start_one : (1 : εNFA α σ).start = univ :=
  rfl
#align ε_NFA.start_one εNFA.start_one

@[simp]
theorem start_char [DecidableEq α] (a : α) : (char a).start = { none } := rfl

@[simp]
theorem start_mul [DecidablePred (· ∈ P.accept)] : (P.mul Q).start = (Sum.inl '' P.start) := rfl

@[simp]
theorem accept_zero : (0 : εNFA α σ).accept = ∅ :=
  rfl
#align ε_NFA.accept_zero εNFA.accept_zero

@[simp]
theorem accept_one : (1 : εNFA α σ).accept = univ :=
  rfl
#align ε_NFA.accept_one εNFA.accept_one

@[simp]
theorem accept_char [DecidableEq α] (a : α) : (char a).accept = { some () } := rfl

@[simp]
theorem accept_mul [DecidablePred (· ∈ P.accept)] :
  (P.mul Q).accept = (Sum.inr '' Q.accept) :=
  rfl

@[simp]
theorem evalFrom_one_cons (s : Set σ) (x : List α) (a : α) :
  (1 : εNFA α σ).evalFrom s (a :: x) = ∅ := by
    induction x using List.reverseRecOn with
    | nil => simp
    | append_singleton xs x _ =>
      rw [←List.cons_append, evalFrom_append_singleton, stepSet_one]

@[simp]
theorem accepts_zero : (0 : εNFA α σ).accepts = 0 := by
  rw [accepts, accept]
  simp
  rw [Language.zero_def]

@[simp]
theorem accepts_one [Nonempty σ] : (1 : εNFA α σ).accepts = 1 := by
  ext x
  rw [Language.mem_one]
  simp
  cases x
  . simp
  . simp

@[simp]
theorem εClosure_char [DecidableEq α] (s : Set (Option Unit)) (a : α) :
  (char a).εClosure s = s := by
  ext x
  constructor
  . intro h
    cases' h with _ h1
    . exact h1
    . simp at *
  . intro h
    have h1 : s ⊆ εClosure (char a) s := subset_εClosure _ _
    exact h1 h

@[simp]
theorem stepSet_char_none [DecidableEq α] (a : α) : (char a).stepSet { none } a = { some () } := by
  unfold stepSet
  simp

@[simp]
theorem stepSet_char_none_ne [DecidableEq α] (a : α) :
  ∀ b ≠ a, (char a).stepSet { none } b = ∅ := by
  unfold stepSet
  simp

@[simp]
theorem stepSet_char_some [DecidableEq α] (a b : α) : (char a).stepSet { some () } b = ∅ := by
  unfold stepSet
  simp

@[simp]
theorem foldl_stepSet_char_empty [DecidableEq α] (x : List α) (a : α) :
  List.foldl (char a).stepSet ∅ x = ∅ := by
  induction x with
  | nil =>
    rw [List.foldl_nil]
  | cons x xs ih =>
    rw [List.foldl_cons]
    simp
    exact ih

@[simp]
theorem evalFrom_char_cons_cons [DecidableEq α] (x : List α) (a b c : α) :
  (char a).evalFrom { none } (b :: c :: x) = ∅ := by
  by_cases h : b = a
  . rw [h]
    unfold evalFrom
    simp
  . unfold evalFrom
    simp
    rw [stepSet_char_none_ne, stepSet_empty]
    simp
    exact h

@[simp]
theorem accepts_char [DecidableEq α] : (char a).accepts = {[a]} := by
  ext x
  rw [mem_singleton_iff]
  simp
  cases' x with _ xs
  . simp
  . cases xs
    . simp
    . simp

@[simp]
theorem accepts_add : (P.add Q).accepts = P.accepts + Q.accepts := by
  rw [add, NFA.toεNFA_correct, DFA.toNFA_correct]
  repeat rw [←toNFA_correct, ←NFA.toDFA_correct]
  rw [←DFA.accepts_add P.toNFA.toDFA Q.toNFA.toDFA]

@[simp]
theorem accepts_mul : (P.mul Q).accepts = P.accepts * Q.accepts := by
  ext x
  simp
  rw [Language.mem_mul]
  sorry

@[simp]
theorem accepts_star [DecidablePred (· ∈ P.accept)] : P.star.accepts = P.accepts∗ := by
  ext x
  rw [Language.mem_kstar]
  sorry

end εNFA
