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

def star : εNFA α (Option σ) :=
{
  step := fun p c q =>
    match c with
    | none => match (p, q) with
      | (some p, some q) => P.step p c q ∨ (P.accept p ∧ P.start q)
      | (none, some q) => P.start q
      | (_, _) => false
    | some c => match (p, q) with
      | (some p, some q) => P.step p c q
      | (_, _) => False
  start := { none } ∪ (some '' P.start)
  accept := { none } ∪ (some '' P.accept)
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
theorem step_mul_left_not_accept_some (a : α) :
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
theorem step_mul_left_not_accept_none :
  ∀ s ∉ P.accept, (P.mul Q).step (Sum.inl s) none = (Sum.inl '' P.step s none) := by
  intros s hs
  ext x
  unfold mul
  match x with
  | Sum.inl p =>
    simp at *
    rfl
  | Sum.inr q =>
    simp at *
    intro h
    absurd hs
    exact h.left

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
theorem step_mul_left_none_right (s : σ) (q : σ') :
  Sum.inr q ∈ (P.mul Q).step (Sum.inl s) none ↔ s ∈ P.accept ∧ q ∈ Q.start := by
  rfl

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
theorem step_mul_right_left (s : σ') (p : σ) (a : Option α) :
  Sum.inl p ∉ (P.mul Q).step (Sum.inr s) a := by
  simp

@[simp]
theorem step_mul_left_right_none (p : σ) (q : σ') :
  Sum.inr q ∈ (P.mul Q).step (Sum.inl p) none ↔ p ∈ P.accept ∧ q ∈ Q.start := by
  simp

@[simp]
theorem step_mul_left_none (x : σ):
  x ∈ P.step s none ↔ Sum.inl x ∈ (P.mul Q).step (Sum.inl s) none := by
  constructor
  . intro h
    have hh : Sum.inl x ∈ (Sum.inl '' P.step s none) := by
      exact @mem_image_of_mem _ (σ ⊕ σ') Sum.inl _ _ h
    by_cases hs : s ∈ P.accept
    . rw [step_mul_left_none_accept _ _ _ hs]
      left
      exact hh
    . rw [step_mul_left_not_accept_none _ _ _ hs]
      exact hh
  . intro h
    unfold mul at h
    simp at h
    exact h

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
theorem start_mul : (P.mul Q).start = (Sum.inl '' P.start) := rfl

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
    tauto

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
theorem εClosure_mul_left_not_accept (p : Set σ) :
  (∀ x ∈ P.accept, x ∉ P.εClosure p) →
  (P.mul Q).εClosure (Sum.inl '' p) = Sum.inl '' P.εClosure p := by
  intro h
  ext x
  constructor
  . intro h1
    induction h1 with
    | base y hy =>
      simp at *
      tauto
    | step s t ht hs ih =>
      simp at ih
      match ih with
      | ⟨y, hy, hs'⟩ =>
        rw [←hs'] at ht hs
        have hy' : y ∉ P.accept := by
          contrapose h
          simp at *
          exact ⟨y, ⟨h, hy⟩⟩
        cases t with
        | inl t =>
          rw [step_mul_left_not_accept_none _ _ y hy'] at ht
          simp at ht
          simp at *
          exact εClosure.step y t ht hy
        | inr t =>
          simp at ht
          absurd hy'
          exact ht.left
  . intro h1
    match h1 with
    | ⟨y, hy, hx⟩ =>
      induction hy generalizing x with
      | base k hk =>
        have hk' : Sum.inl k ∈ Sum.inl '' p := by
          exact @mem_image_of_mem _ (σ ⊕ σ') Sum.inl _ _ hk
        rw [hx] at hk'
        exact εClosure.base x hk'
      | step s t ht hs ih =>
      simp at ih
      have ih : Sum.inl s ∈ (P.mul Q).εClosure (Sum.inl '' p) := ih s hs rfl
      rw [step_mul_left_none _ Q] at ht
      rw [hx] at ht
      exact εClosure.step (Sum.inl s) x ht ih

@[simp]
theorem εClosure_mul_left (S : Set σ) (p : σ) :
  p ∈ P.εClosure S ↔ Sum.inl p ∈ (P.mul Q).εClosure (Sum.inl '' S) := by
  constructor
  . intro h
    induction h with
    | base s hs =>
      exact εClosure.base (Sum.inl s) (mem_image_of_mem Sum.inl hs)
    | step s t ht _ ih =>
      rw [step_mul_left_none] at ht
      exact εClosure.step (Sum.inl s) (Sum.inl t) ht ih
  . intro h
    have h : ∃ x ∈ (P.mul Q).εClosure (Sum.inl '' S), Sum.inl p = x := by
      exact ⟨Sum.inl p, ⟨h, rfl⟩⟩
    match h with
    | ⟨x, ⟨hx, hp⟩⟩ =>
      induction hx generalizing p with
      | base s hs =>
        rw [←hp] at hs
        simp at hs
        exact εClosure.base _ hs
      | step s t ht hs ih =>
        simp at ih
        match s with
        | Sum.inl s =>
          have ih := ih s hs hs rfl
          rw [←hp] at ht
          rw [←step_mul_left_none] at ht
          exact εClosure.step s p ht ih
        | Sum.inr s =>
          rw [←hp] at ht
          simp at *

theorem εClosure_mul_left_accept'' (p : Set σ) (q : σ') :
  Sum.inr q ∈ (P.mul Q).εClosure (Sum.inl '' p) → q ∈ Q.εClosure Q.start := by
  intro h
  have h : ∃ x ∈ (P.mul Q).εClosure (Sum.inl '' p), Sum.inr q = x := by
    exact ⟨Sum.inr q, ⟨h, rfl⟩⟩

  match h with
  | ⟨x, ⟨hx, hq⟩⟩ =>
    induction hx generalizing q with
    | base s hs =>
      rw [←hq] at hs
      simp at *
    | step s t ht hs ih =>
      simp at ih
      match s with
      | Sum.inl s =>
        rw [←hq] at ht
        simp at ht
        exact εClosure.base _ ht.right
      | Sum.inr s =>
        have ih := ih s hs hs rfl
        rw [←hq] at ht
        simp at ht
        exact εClosure.step s q ht ih

theorem εClosure_mul_left_accept' (S : Set σ) (q : σ') :
  Sum.inr q ∈ (P.mul Q).εClosure (Sum.inl '' S) →
  ∃ p ∈ P.accept, Sum.inl p ∈ (P.mul Q).εClosure (Sum.inl '' S) := by
  intro hq

  have hq : ∃ x ∈ (P.mul Q).εClosure (Sum.inl '' S), Sum.inr q = x := by
    exact ⟨Sum.inr q, ⟨hq, rfl⟩⟩

  match hq with
  | ⟨x, ⟨hx, hq⟩⟩ =>
    induction hx generalizing q with
    | base s hs =>
      rw [←hq] at hs
      simp at *
    | step s t ht hs ih =>
      simp at ih
      match s with
      | Sum.inl s =>
        rw [←hq] at ht
        simp at ht
        simp at ih
        exact ⟨s, ⟨ht.left, hs⟩⟩
      | Sum.inr s =>
        have ih := ih s hs hs rfl
        exact ih

theorem εClosure_mul_left_accept (p : Set σ) (q : σ') :
  (∃ x ∈ P.accept, x ∈ P.εClosure p) →
  (q ∈ Q.εClosure Q.start ↔ Sum.inr q ∈ (P.mul Q).εClosure (Sum.inl '' p)) := by
  intro h
  constructor
  . intro h1
    induction h1 with
    | base s hs =>
      match h with
      | ⟨x, hx⟩ =>
          have hs : Sum.inr s ∈ (P.mul Q).step (Sum.inl x) none := by
            simp
            exact ⟨hx.left, hs⟩
          rw [εClosure_mul_left _ Q] at hx
          exact εClosure.step _ _ hs hx.right
    | step s t ht _ ih =>
      have ht : Sum.inr t ∈ (Sum.inr '' Q.step s none) := by
        exact @mem_image_of_mem _ (σ ⊕ σ') Sum.inr _ _ ht
      rw [←step_mul_right P _] at ht
      exact εClosure.step _ _ ht ih
  . intro h1
    have h1 : ∃ x ∈ (P.mul Q).εClosure (Sum.inl '' p), Sum.inr q = x := by
      exact ⟨Sum.inr q, ⟨h1, rfl⟩⟩
    match h1 with
    | ⟨x, ⟨hx, hq⟩⟩ =>
      induction hx generalizing q with
      | base s hs =>
        rw [←hq] at hs
        simp at *
      | step s t ht hs ih =>
        simp at ih
        match s with
        | Sum.inl s =>
          rw [←hq] at ht
          simp at ht
          exact εClosure.base _ ht.right
        | Sum.inr s =>
          have ih := ih s hs hs rfl
          rw [←hq] at ht
          simp at ht
          exact εClosure.step s q ht ih

-- theorem εClosure_mul_left_accept [h'' : Nonempty P.accept] :
--   (P.mul Q).εClosure (Sum.inl '' P.accept) = Sum.inl '' P.εClosure P.accept ∪ Sum.inr '' Q.εClosure Q.start := by
--   ext x
--   constructor
--   . intro h
--     induction h with
--     | base y h =>
--       simp at *
--       left
--       match h with
--       | ⟨x, hx⟩ =>
--         have hx' : x ∈ P.εClosure P.accept := (subset_εClosure _ P.accept) hx.left
--         exact ⟨x, ⟨hx', hx.right⟩⟩
--     | step s t hs ht ih =>
--       simp at ih
--       match ih with
--       | Or.inl ⟨x, ⟨hx, hs'⟩⟩ =>
--         rw [←hs'] at hs
--         by_cases hx' : x ∈ P.accept
--         . rw [step_mul_left_none_accept _ _ _ hx'] at hs
--           match hs with
--           | Or.inl hs =>
--             match hs with
--             | ⟨y, hs⟩ =>
--               have hhh : y ∈ P.εClosure P.accept := by
--                 exact εClosure.step x y hs.left hx

--               have hh : Sum.inl y ∈ Sum.inl '' P.εClosure P.accept := by
--                 exact @mem_image_of_mem _ (σ ⊕ σ') Sum.inl _ _ hhh
--               rw [hs.right] at hh
--               left
--               exact hh
--           | Or.inr hs =>
--             right
--             have hh : Sum.inr '' Q.start ⊆ Sum.inr '' Q.εClosure Q.start := @image_subset _ (σ ⊕ σ') _ _ (Sum.inr) (subset_εClosure _ Q.start)
--             exact hh hs
--         . rw [step_mul_left_not_accept_none _ _ _ hx'] at hs
--           match hs with
--           | ⟨y, hs⟩ =>
--             have hhh : y ∈ P.εClosure P.accept := by
--               exact εClosure.step x y hs.left hx

--             have hh : Sum.inl y ∈ Sum.inl '' P.εClosure P.accept := by
--               exact @mem_image_of_mem _ (σ ⊕ σ') Sum.inl _ _ hhh
--             rw [hs.right] at hh
--             left
--             exact hh
--       | Or.inr ⟨x, h'⟩ =>
--         match s with
--         | Sum.inl s =>
--           simp at h'
--         | Sum.inr s =>
--           simp at hs
--           match hs with
--           | ⟨y, hs⟩ =>
--             simp at h'
--             rw [h'.right] at h'
--             have hh : Sum.inr y ∈ Sum.inr '' Q.εClosure Q.start :=
--               @mem_image_of_mem _ (σ ⊕ σ') Sum.inr _ _ (εClosure.step s y hs.left h'.left)
--             rw [hs.right] at hh
--             right
--             exact hh
--   . intro h
--     simp at *
--     match h with
--     | Or.inl ⟨p, hp⟩ =>
--       cases hp.left with
--       | base _ h' =>
--         have hh : Sum.inl p ∈ Sum.inl '' P.accept :=
--           @mem_image_of_mem _ (σ ⊕ σ') Sum.inl _ _ h'
--         have hhh : Sum.inl p ∈ (P.mul Q).εClosure (Sum.inl '' P.accept) := εClosure.base _ hh
--         rw [hp.right] at hhh
--         exact hhh
--       | step s _ hp' hs =>
--         rw [step_mul_left_none] at hp'
--         apply (εClosure_mul_left _ Q _ _).mp at hs
--         rw [hp.right] at hp'
--         exact εClosure.step (Sum.inl s) x hp' hs
--     | Or.inr ⟨q, hq⟩ =>
--       induction hq.left generalizing x with
--       | base q hq' =>
--         match h'' with
--         |⟨p, hp⟩ =>
--           have hp' : Sum.inl p ∈ Sum.inl '' P.accept :=
--             @mem_image_of_mem _ (σ ⊕ σ') Sum.inl _ _ hp

--           have hh : Sum.inr q ∈ (P.mul Q).step (Sum.inl p) none := by
--             simp
--             exact ⟨hp, hq'⟩

--           have hhh : Sum.inl p ∈ (P.mul Q).εClosure (Sum.inl '' P.accept) :=
--             εClosure.base (Sum.inl p) hp'

--           rw [hq.right] at hh

--           exact εClosure.step (Sum.inl p) x hh hhh
--       | step s t ht hs ih =>
--         simp at ih
--         have ih : Sum.inr s ∈ (P.mul Q).εClosure (Sum.inl '' P.accept) := ih s hs hs rfl

--         have hh : Sum.inr t ∈ (P.mul Q).step (Sum.inr s) none := by
--           simp
--           exact ht

--         rw [hq.right] at hh

--         exact εClosure.step (Sum.inr s) x hh ih

@[simp]
theorem εClosure_mul_right (q : Set σ') :
  (P.mul Q).εClosure (Sum.inr '' q) = Sum.inr '' Q.εClosure q := by
  ext x
  constructor
  . intro h
    induction h with
    | base =>
      simp at *
      tauto
    | step s t ht hs ih =>
      simp at ih
      match ih with
      | ⟨y, ⟨hy, hs'⟩⟩ =>
        rw [←hs'] at ht hs
        rw [step_mul_right] at ht
        simp at ht
        match ht with
        | ⟨k, ⟨hk, ht'⟩⟩ =>
          have hk' : k ∈ Q.εClosure q := by
            exact εClosure.step y k hk hy
          simp
          exact ⟨k, ⟨hk', ht'⟩⟩
  . intro h
    match h with
    | ⟨y, ⟨hy, hx⟩⟩ =>
      induction hy generalizing x with
      | base k hk =>
        have hk : Sum.inr k ∈ Sum.inr '' q := by
          exact @mem_image_of_mem _ (σ ⊕ σ') Sum.inr _ _ hk
        rw [hx] at hk
        exact εClosure.base x hk
       | step s t ht hs ih =>
        simp at ih
        have ih : Sum.inr s ∈ (P.mul Q).εClosure (Sum.inr '' q) := ih s hs rfl
        have ht : Sum.inr t ∈ (P.mul Q).step (Sum.inr s) none := by
          simp
          exact ht
        rw [hx] at ht
        exact εClosure.step (Sum.inr s) x ht ih

@[simp]
theorem stepSet_mul_right (a : α) (q : Set σ') :
  (P.mul Q).stepSet (Sum.inr '' q) a = Sum.inr '' Q.stepSet q a := by
  unfold stepSet
  ext x
  simp
  tauto

theorem stepSet_mul_left_left (a : α) (S : Set σ) (p : σ) :
  Sum.inl p ∈ (P.mul Q).stepSet (Sum.inl '' S) a ↔ p ∈ P.stepSet S a := by
  constructor
  . intro h
    simp at *
    match h with
    | ⟨t, ⟨ht, hp⟩⟩ =>
      apply (εClosure_mul_left _ Q _ _).mpr at hp
      exact ⟨t, ⟨ht, hp⟩⟩
  . intro h
    simp at *
    match h with
    | ⟨t, ⟨ht, hp⟩⟩ =>
      apply (εClosure_mul_left _ Q _ _).mp at hp
      exact ⟨t, ⟨ht, hp⟩⟩

theorem stepSet_mul_left_not_accept (a : α) (S : Set σ) :
  (∀ s ∈ S, (∀ p ∈ P.accept, p ∉ P.εClosure (P.step s a))) →
  (P.mul Q).stepSet (Sum.inl '' S) a = Sum.inl '' P.stepSet S a := by
  intro h
  ext x
  cases x with
  | inl x =>
    have h := stepSet_mul_left_left P Q a S x
    simp at *
    exact h
  | inr x =>
    simp
    intro k hk h'
    have h := εClosure_mul_left_not_accept P Q (P.step k a) (h k hk)
    rw [h] at h'
    simp at h'

theorem stepSet_mul_left_right (a : α) (S : Set σ) (q : σ') :
  Sum.inr q ∈ (P.mul Q).stepSet (Sum.inl '' S) a → q ∈ Q.εClosure Q.start := by
  intro h
  simp at *
  match h with
  | ⟨k, ⟨hk, hq⟩⟩ =>
    have hq : ∃ x ∈ (P.mul Q).εClosure (Sum.inl '' P.step k (some a)), Sum.inr q = x := by
      exact ⟨Sum.inr q, ⟨hq, rfl⟩⟩
    match hq with
    | ⟨x, ⟨hq, hx⟩⟩ =>
      induction hq generalizing q with
      | base s hs =>
        rw [←hx] at hs
        simp at *
      | step s t ht hs ih =>
        simp at *
        match s with
        | Sum.inl s =>
          rw [←hx] at ht
          simp at ht
          exact εClosure.base _ ht.right
        | Sum.inr s =>
          have ih := ih s k hk hs hs hs rfl
          rw [←hx] at ht
          simp at ht
          exact εClosure.step _ _ ht ih

@[simp]
theorem eval_mul_right (x : List α) :
  (P.mul Q).evalFrom (Sum.inr '' Q.start) x = Sum.inr '' Q.eval x := by
  induction x using List.reverseRecOn with
  | nil =>
    simp
  | append_singleton xs x ih =>
    simp
    rw [ih]
    simp

theorem εClosure_εClosure (S : Set σ) :
  P.εClosure S = P.εClosure (P.εClosure S) := by
  ext x
  constructor
  . intro h
    induction h with
    | base s hs =>
      exact (subset_trans (subset_εClosure P S) (subset_εClosure P (εClosure P S))) hs
    | step s t ht _ ih =>
      exact εClosure.step s t ht ih
  . intro h
    induction h with
    | base _ hs => exact hs
    | step s t ht _ ih => exact εClosure.step s t ht ih

theorem stepSet_εClosure (S : Set σ) (a : α) :
  P.stepSet S a = P.εClosure (P.stepSet S a) := by
  ext x
  constructor
  . intro h
    simp at h
    rw [←mem_stepSet_iff] at h
    exact εClosure.base x h
  . intro h
    induction h with
    | base _ hs => exact hs
    | step s t ht hs ih =>
      simp at *
      match ih with
      | ⟨k, ⟨hk, hs⟩⟩ => exact ⟨k, ⟨hk, εClosure.step s t ht hs⟩⟩

theorem eval_mul (a b : List α) :
  (P.mul Q).eval (a ++ b) = (P.mul Q).evalFrom ((P.mul Q).eval a) b := by
  induction b using List.reverseRecOn with
  | nil =>
    simp
    induction a using List.reverseRecOn with
    | nil =>
      simp [←εClosure_εClosure]
    | append_singleton as a ih =>
      simp
      rw [ih, ←stepSet_εClosure]
  | append_singleton bs b ih =>
    rw [←List.append_assoc]
    rw [eval_append_singleton]
    simp [ih]

@[simp]
theorem eval_mul_left_left (x : List α) (s : σ) :
  s ∈ P.eval x ↔ Sum.inl s ∈ (P.mul Q).eval x := by
  constructor
  . induction x using List.reverseRecOn generalizing s with
    | nil =>
      intro h
      simp at *
      exact (εClosure_mul_left _ _ _ _).mp h
    | append_singleton xs x ih =>
      intro h
      simp at h
      match h with
      | ⟨t, ⟨ht, hs⟩⟩ =>
        apply ih at ht
        simp
        apply (εClosure_mul_left _ _ _ _).mp at hs
        exact ⟨t, ⟨ht, hs⟩⟩
  . induction x using List.reverseRecOn generalizing s with
    | nil =>
      intro h
      simp at *
      rw [←εClosure_mul_left] at h
      exact h
    | append_singleton xs x ih =>
      intro h
      simp at h
      match h with
      | ⟨t, ⟨ht, hs⟩⟩ =>
        apply ih t at ht
        rw [←εClosure_mul_left] at hs
        simp
        exact ⟨t, ⟨ht, hs⟩⟩

theorem eval_mul_left_right (x : List α) (p : σ) (q : σ') :
  p ∈ P.accept ∧ q ∈ Q.εClosure Q.start ∧ Sum.inl p ∈ (P.mul Q).eval x → Sum.inr q ∈ (P.mul Q).eval x := by
  intro ⟨hp, hq, hx⟩
  cases x using List.reverseRecOn with
  | nil =>
    simp at *
    rw [←εClosure_mul_left] at hx
    exact (εClosure_mul_left_accept P Q P.start q ⟨p, ⟨hp, hx⟩⟩).mp hq
  | append_singleton xs x _ =>
    simp at hx
    match hx with
    | ⟨t, ⟨ht, hp'⟩⟩ =>
      rw [←εClosure_mul_left] at hp'
      rw [εClosure_mul_left_accept _ _ _ _ ⟨p, ⟨hp, hp'⟩⟩] at hq
      simp
      left
      use t

theorem eval_mul_left_right_split (a b : List α) (p : σ) (q : σ') :
  p ∈ P.accept ∧ p ∈ P.eval a ∧ q ∈ Q.eval b → Sum.inr q ∈ (P.mul Q).eval (a ++ b) := by
  intro ⟨hp, ha, hq⟩
  induction b using List.reverseRecOn generalizing q with
  | nil =>
    simp at *
    rw [eval_mul_left_left _ Q] at ha
    exact eval_mul_left_right _ _ _ _ _ ⟨hp, hq, ha⟩
  | append_singleton bs b ih =>
    simp at *
    match hq with
    | ⟨t, ⟨ht, hq⟩⟩ =>
      have ih := ih t ht
      rw [←List.append_assoc]
      rw [eval_append_singleton]
      simp
      right
      exact ⟨t, ⟨ih, hq⟩⟩

theorem eval_mul_left_right' (x : List α) (q : σ') :
  Sum.inr q ∈ (P.mul Q).eval x →
  ∃ a b, x = a ++ b ∧ a ∈ P.accepts := by
  intro h
  induction x using List.reverseRecOn generalizing q with
  | nil =>
    simp at *
    have h := εClosure_mul_left_accept' _ _ _ q h
    match h with
    | ⟨p, hp⟩ =>
      rw [←εClosure_mul_left] at hp
      use p
  | append_singleton xs x ih =>
    simp at h
    cases h with
    | inl h =>
      match h with
      | ⟨p, hp, hq'⟩ =>
        have h := εClosure_mul_left_accept' _ _ _ _ hq'
        rw [←eval_mul_left_left] at hp
        match h with
        | ⟨p', hp', hx⟩ =>
          rw [←εClosure_mul_left] at hx
          use (xs ++ [x]), []
          simp
          exact ⟨p', hp', p, hp, hx⟩
    | inr h =>
      match h with
      | ⟨q', hq, _⟩ =>
        have ih := ih q' hq
        match ih with
        | ⟨a, b, hxs, ha⟩ =>
          use a, b ++ [x]
          rw [←List.append_assoc, hxs]
          exact ⟨rfl, ha⟩


theorem eval_mul_left_right'' (x : List α) (q : σ') :
  Sum.inr q ∈ (P.mul Q).eval x →
  ∃ a b, x = a ++ b ∧ q ∈ Q.eval b := by
  intro h
  induction x using List.reverseRecOn generalizing q with
  | nil =>
    use [], []
    refine' ⟨rfl, _⟩
    simp at *
    apply εClosure_mul_left_accept'' at h
    exact h
  | append_singleton xs x ih =>
    simp at h
    cases h with
    | inl h =>
      match h with
      | ⟨p, _, hq'⟩ =>
        apply εClosure_mul_left_accept'' at hq'
        use (xs ++ [x]), []
        simp
        exact hq'
    | inr h =>
      match h with
      | ⟨q', hq, hq'⟩ =>
        have ih := ih q' hq
        match ih with
        | ⟨a, b, hxs, hb⟩ =>
          use a, b ++ [x]
          rw [←List.append_assoc, hxs]
          refine' ⟨rfl, _⟩
          simp
          exact ⟨q', hb, hq'⟩

theorem eval_mul_left_righ (x : List α) (q : σ') :
  Sum.inr q ∈ (P.mul Q).eval x →
  ∃ a b, x = a ++ b ∧ a ∈ P.accepts ∧ q ∈ Q.eval b := by
  intro h
  induction x using List.reverseRecOn generalizing q with
  | nil =>
    use [], []
    simp at *
    have hq := εClosure_mul_left_accept'' _ _ _ _ h
    have hp := εClosure_mul_left_accept' _ _ _ _ h
    refine' ⟨_, hq⟩
    match hp with
    | ⟨p, hp⟩ =>
      rw [←εClosure_mul_left] at hp
      use p
  | append_singleton xs x ih =>
    simp at h
    cases h with
    | inl h =>
      match h with
      | ⟨p, hp, hq'⟩ =>
        have h := εClosure_mul_left_accept' _ _ _ _ hq'
        have hq'' := εClosure_mul_left_accept'' _ _ _ _ hq'
        rw [←eval_mul_left_left] at hp
        match h with
        | ⟨p', hp', hx⟩ =>
          rw [←εClosure_mul_left] at hx
          use (xs ++ [x]), []
          simp
          refine' ⟨⟨p', hp', p, hp, hx⟩, hq''⟩
    | inr h =>
      match h with
      | ⟨q', hq, hq'⟩ =>
        have ih := ih q' hq
        match ih with
        | ⟨a, b, hxs, ha⟩ =>
          use a, b ++ [x]
          rw [←List.append_assoc, hxs]
          refine' ⟨rfl, ha.left, _⟩
          simp
          refine' ⟨q', ha.right, hq'⟩

theorem split'' (n : Nat) (s : List α) (P1 P2 : List α → Prop) :
  n ≤ s.length →
 (∃ s1 s2, s1.length ≤ n ∧ s1 ++ s2 = s ∧ P1 s1 ∧ P2 s2) ∨
 ¬(∃ s1 s2, s1.length ≤ n ∧ s1 ++ s2 = s ∧ P1 s1 ∧ P2 s2) := by
  intro
  tauto

theorem split' (n : Nat) (s : List α) (P1 P2 : List α → Prop) :
  n ≤ s.length →
 (∃ s1 s2, s1.length ≤ n ∧ s1 ++ s2 = s ∧ P1 s1 ∧ P2 s2) ∨
 (∀ s1 s2, s1.length ≤ n → s1 ++ s2 = s → ¬P1 s1 ∨ ¬P2 s2) := by
  intro h
  have h := split'' n s P1 P2 h
  simp at *
  cases h with
  | inl h =>
    left
    exact h
  | inr h =>
    intros
    tauto

theorem split (s : List α) (P1 P2 : List α → Prop) : (∃ s1 s2, s = s1 ++ s2 ∧ P1 s1 ∧ P2 s2) ∨
  (∀ s1 s2, s = s1 ++ s2 → ¬P1 s1 ∨ ¬P2 s2) := by
  have h := ((split' (s.length) s P1 P2) (le_refl s.length))
  aesop

theorem accepts_mul' : x ∈ (P.mul Q).accepts → ∃ a ∈ P.accepts, ∃ b ∈ Q.accepts, a ++ b = x := by
  intro h
  match x with
  | [] =>
    simp at *
    match h with
    | ⟨q, ⟨hq, h⟩⟩ =>
      have hq' := εClosure_mul_left_accept'' _ _ _ _ h
      have hp := εClosure_mul_left_accept' _ _ _ _ h
      match hp with
      | ⟨p, ⟨hp, hp'⟩⟩ =>
        rw [←εClosure_mul_left] at hp'
        exact ⟨⟨p, ⟨hp, hp'⟩⟩, ⟨q, ⟨hq, hq'⟩⟩⟩
  | x =>
    simp at h
    match h with
    | ⟨q, hq, h⟩ =>
      have h' := eval_mul_left_righ _ _ _ _ h
      match h' with
      | ⟨a, b, hx, ha, hb⟩ =>
        rw [hx]
        simp
        exact ⟨a, ha, b, ⟨q, hq, hb⟩, rfl⟩

@[simp]
theorem accepts_mul : (P.mul Q).accepts = P.accepts * Q.accepts := by
  ext x
  rw [Language.mem_mul]
  constructor
  . intro h
    match x with
    | [] =>
      simp at *
      match h with
      | ⟨q, ⟨hq, h⟩⟩ =>
        have hq' := εClosure_mul_left_accept'' _ _ _ _ h
        have hp := εClosure_mul_left_accept' _ _ _ _ h
        match hp with
        | ⟨p, ⟨hp, hp'⟩⟩ =>
          rw [←εClosure_mul_left] at hp'
          exact ⟨⟨p, ⟨hp, hp'⟩⟩, ⟨q, ⟨hq, hq'⟩⟩⟩
    | x =>
      simp at h
      match h with
      | ⟨q, hq, h⟩ =>
        have h' := eval_mul_left_righ _ _ _ _ h
        match h' with
        | ⟨a, b, hx, ha, hb⟩ =>
          rw [hx]
          simp
          exact ⟨a, ha, b, ⟨q, hq, hb⟩, rfl⟩
  . intro h
    match h with
    | ⟨a, ⟨ha, ⟨b, ⟨hb, hx⟩⟩⟩⟩ =>
      rw [←hx]
      cases b using List.reverseRecOn with
      | nil =>
        simp at *
        rw [←eval] at ha
        match ha with
        | ⟨p, ⟨hp, ha⟩⟩ =>
          rw [eval_mul_left_left _ Q] at ha
          match hb with
          | ⟨q, ⟨hq, hb⟩⟩ =>
            exact ⟨q, ⟨hq, eval_mul_left_right _ _ _ _ _ ⟨hp, hb, ha⟩⟩⟩
      | append_singleton bs b =>
        simp at *
        rw [←List.append_assoc]
        rw [evalFrom_append_singleton]
        simp
        match hb with
        | ⟨q, ⟨hq, ⟨t, ht⟩⟩⟩ =>
          use q
          constructor
          . exact hq
          . right
            use t
            constructor
            . match ha with
              | ⟨s, hs⟩ =>
                rw [←eval] at hs ht
                exact eval_mul_left_right_split _ _ _ _ _ _ ⟨hs.left, hs.right, ht.left⟩
            . exact ht.right

@[simp]
theorem accepts_star : P.star.accepts = P.accepts∗ := by
  ext x
  rw [Language.mem_kstar]
  sorry

end εNFA
