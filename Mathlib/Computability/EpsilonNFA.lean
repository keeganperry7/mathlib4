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
      | (_, _) => False
    | some c => match (p, q) with
      | (some p, some q) => P.step p c q
      | (_, _) => False
  start := { none }
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

-- @[simp]
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

-- @[simp]
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

-- @[simp]
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
    apply mem_image_of_mem Sum.inl at h
    by_cases hs : s ∈ P.accept
    . rw [step_mul_left_none_accept _ _ _ hs]
      left
      exact h
    . rw [step_mul_left_not_accept_none _ _ _ hs]
      exact h
  . intro h
    unfold mul at h
    simp at h
    exact h

@[simp]
theorem step_star_none_none :
  P.star.step none none = some '' P.start := by
  ext x
  unfold star
  simp
  cases x with
  | none =>
    simp
    intro h
    exact h
  | some x =>
    simp
    rfl

@[simp]
theorem step_star_some_some (a : α) (x : σ)  :
  P.star.step (some x) (some a) = some '' P.step x (some a) := by
  ext y
  unfold star
  simp
  cases y with
  | none =>
    simp
    intro h
    exact h
  | some y =>
    simp
    rfl

@[simp]
theorem step_star_none_some (a : α) :
  P.star.step none (some a) = ∅ := by
  unfold star
  simp
  rfl

theorem step_star_some_none_not_accept :
  ∀ s ∉ P.accept, P.star.step (some s) none = some '' P.step s none := by
  intro s hs
  ext x
  cases x with
  | none =>
    simp
    intro h
    exact h
  | some x =>
    unfold star
    simp at *
    constructor
    . intro h
      cases h with
      | inl h => exact h
      | inr h => tauto
    . tauto

theorem step_star_some_none_accept :
  ∀ s ∈ P.accept, P.star.step (some s) none = some '' P.step s none ∪ some '' P.start := by
  intro s hs
  ext x
  cases x with
  | none =>
    simp
    intro h
    exact h
  | some x =>
    unfold star
    simp
    constructor
    . intro h
      cases h with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr h.right
    . intro h
      cases h with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr ⟨hs, h⟩

theorem step_star_some_none (s t : σ) :
  s ∈ P.step t none → some s ∈ P.star.step (some t) none := by
  by_cases h : t ∈ P.accept
  . rw [step_star_some_none_accept _ _ h]
    simp
    tauto
  . rw [step_star_some_none_not_accept _ _ h]
    simp

theorem step_star_some_none_none (s : σ) :
  none ∉ P.star.step (some s) none := by
  intro h
  unfold star at h
  simp at h
  exact h

@[simp]
theorem step_star_to_none (s : Option σ) (a : Option α) :
  none ∉ P.star.step s a := by
  intro h
  unfold star at h
  match a with
  | none =>
    match s with
    | none =>
      simp at h
      exact h
    | some _ =>
      simp at h
      exact h
  | some _ =>
    match s with
    | none =>
      simp at h
      exact h
    | some _ =>
      simp at h
      exact h

theorem step_star_accept_start (s t : σ) :
  s ∈ P.accept ∧ t ∈ P.start →
  some t ∈ P.star.step (some s) none := by
  intro h
  rw [step_star_some_none_accept _ _ h.left]
  simp
  exact Or.inr h.right

theorem step_star_start (s : σ) :
  s ∈ P.start →
  some s ∈ P.star.step none none := by
  simp

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
theorem start_star : P.star.start = { none } := rfl

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
theorem accept_mul :
  (P.mul Q).accept = (Sum.inr '' Q.accept) :=
  rfl

@[simp]
theorem accept_star :
  P.star.accept = { none } ∪ some '' P.accept :=
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

theorem mem_fun (f : σ → σ') (p : σ) (S : Set σ') :
  f p ∈ S → ∃ x ∈ S, f p = x := by
  intro h
  exact ⟨f p, h, rfl⟩

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
          exact ⟨y, h, hy⟩
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
        apply mem_image_of_mem Sum.inl at hk
        rw [hx] at hk
        exact εClosure.base x hk
      | step s t ht hs ih =>
      simp at ih
      rw [step_mul_left_none _ Q] at ht
      rw [hx] at ht
      exact εClosure.step (Sum.inl s) x ht (ih s hs rfl)

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
    apply mem_fun at h
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
          rw [←hp] at ht
          rw [←step_mul_left_none] at ht
          exact εClosure.step s p ht (ih s hs rfl)
        | Sum.inr s =>
          rw [←hp] at ht
          simp at *

theorem εClosure_mul_left_accept'' (p : Set σ) (q : σ') :
  Sum.inr q ∈ (P.mul Q).εClosure (Sum.inl '' p) → q ∈ Q.εClosure Q.start := by
  intro h
  apply mem_fun at h
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
        rw [←hq] at ht
        simp at ht
        exact εClosure.step s q ht (ih s hs rfl)

theorem εClosure_mul_left_accept' (S : Set σ) (q : σ') :
  Sum.inr q ∈ (P.mul Q).εClosure (Sum.inl '' S) →
  ∃ p ∈ P.accept, Sum.inl p ∈ (P.mul Q).εClosure (Sum.inl '' S) := by
  intro hq
  apply mem_fun at hq
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
        exact ⟨s, ht.left, hs⟩
      | Sum.inr s =>
        have ih := ih s hs rfl
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
      apply mem_image_of_mem Sum.inr at ht
      rw [←step_mul_right P _] at ht
      exact εClosure.step _ _ ht ih
  . intro h1
    apply mem_fun at h1
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
          exact εClosure.base q ht.right
        | Sum.inr s =>
          have ih := ih s hs rfl
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
        apply mem_image_of_mem Sum.inr at hk
        rw [hx] at hk
        exact εClosure.base x hk
       | step s t ht hs ih =>
        simp at ih
        apply mem_image_of_mem Sum.inr at ht
        rw [←step_mul_right P Q s none] at ht
        rw [hx] at ht
        exact εClosure.step (Sum.inr s) x ht (ih s hs rfl)

-- @[simp]
-- theorem stepSet_mul_right (a : α) (q : Set σ') :
--   (P.mul Q).stepSet (Sum.inr '' q) a = Sum.inr '' Q.stepSet q a := by
--   unfold stepSet
--   ext x
--   simp
--   tauto

-- theorem stepSet_mul_left_left (a : α) (S : Set σ) (p : σ) :
--   Sum.inl p ∈ (P.mul Q).stepSet (Sum.inl '' S) a ↔ p ∈ P.stepSet S a := by
--   constructor
--   . intro h
--     simp at *
--     match h with
--     | ⟨t, ⟨ht, hp⟩⟩ =>
--       apply (εClosure_mul_left _ Q _ _).mpr at hp
--       exact ⟨t, ⟨ht, hp⟩⟩
--   . intro h
--     simp at *
--     match h with
--     | ⟨t, ⟨ht, hp⟩⟩ =>
--       apply (εClosure_mul_left _ Q _ _).mp at hp
--       exact ⟨t, ⟨ht, hp⟩⟩

-- theorem stepSet_mul_left_not_accept (a : α) (S : Set σ) :
--   (∀ s ∈ S, (∀ p ∈ P.accept, p ∉ P.εClosure (P.step s a))) →
--   (P.mul Q).stepSet (Sum.inl '' S) a = Sum.inl '' P.stepSet S a := by
--   intro h
--   ext x
--   cases x with
--   | inl x =>
--     have h := stepSet_mul_left_left P Q a S x
--     simp at *
--     exact h
--   | inr x =>
--     simp
--     intro k hk h'
--     have h := εClosure_mul_left_not_accept P Q (P.step k a) (h k hk)
--     rw [h] at h'
--     simp at h'

-- theorem stepSet_mul_left_right (a : α) (S : Set σ) (q : σ') :
--   Sum.inr q ∈ (P.mul Q).stepSet (Sum.inl '' S) a → q ∈ Q.εClosure Q.start := by
--   intro h
--   simp at *
--   match h with
--   | ⟨k, ⟨hk, hq⟩⟩ =>
--     have hq : ∃ x ∈ (P.mul Q).εClosure (Sum.inl '' P.step k (some a)), Sum.inr q = x := by
--       exact ⟨Sum.inr q, ⟨hq, rfl⟩⟩
--     match hq with
--     | ⟨x, ⟨hq, hx⟩⟩ =>
--       induction hq generalizing q with
--       | base s hs =>
--         rw [←hx] at hs
--         simp at *
--       | step s t ht hs ih =>
--         simp at *
--         match s with
--         | Sum.inl s =>
--           rw [←hx] at ht
--           simp at ht
--           exact εClosure.base _ ht.right
--         | Sum.inr s =>
--           have ih := ih s k hk hs hs hs rfl
--           rw [←hx] at ht
--           simp at ht
--           exact εClosure.step _ _ ht ih

-- @[simp]
-- theorem eval_mul_right (x : List α) :
--   (P.mul Q).evalFrom (Sum.inr '' Q.start) x = Sum.inr '' Q.eval x := by
--   induction x using List.reverseRecOn with
--   | nil =>
--     simp
--   | append_singleton xs x ih =>
--     simp
--     rw [ih]
--     simp

-- theorem εClosure_εClosure (S : Set σ) :
--   P.εClosure S = P.εClosure (P.εClosure S) := by
--   ext x
--   constructor
--   . intro h
--     induction h with
--     | base s hs =>
--       exact (subset_trans (subset_εClosure P S) (subset_εClosure P (εClosure P S))) hs
--     | step s t ht _ ih =>
--       exact εClosure.step s t ht ih
--   . intro h
--     induction h with
--     | base _ hs => exact hs
--     | step s t ht _ ih => exact εClosure.step s t ht ih

-- theorem stepSet_εClosure (S : Set σ) (a : α) :
--   P.stepSet S a = P.εClosure (P.stepSet S a) := by
--   ext x
--   constructor
--   . intro h
--     simp at h
--     rw [←mem_stepSet_iff] at h
--     exact εClosure.base x h
--   . intro h
--     induction h with
--     | base _ hs => exact hs
--     | step s t ht hs ih =>
--       simp at *
--       match ih with
--       | ⟨k, ⟨hk, hs⟩⟩ => exact ⟨k, ⟨hk, εClosure.step s t ht hs⟩⟩

-- theorem eval_mul (a b : List α) :
--   (P.mul Q).eval (a ++ b) = (P.mul Q).evalFrom ((P.mul Q).eval a) b := by
--   induction b using List.reverseRecOn with
--   | nil =>
--     simp
--     induction a using List.reverseRecOn with
--     | nil =>
--       simp [←εClosure_εClosure]
--     | append_singleton as a ih =>
--       simp
--       rw [ih, ←stepSet_εClosure]
--   | append_singleton bs b ih =>
--     rw [←List.append_assoc]
--     rw [eval_append_singleton]
--     simp [ih]

theorem eval_mul_left_left (x : List α) (s : σ) :
  s ∈ P.eval x ↔ Sum.inl s ∈ (P.mul Q).eval x := by
  induction x using List.reverseRecOn generalizing s with
  | nil =>
    simp
    rw [εClosure_mul_left]
  | append_singleton xs x ih =>
    constructor
    . intro h
      simp at h
      match h with
      | ⟨t, ht, hs⟩ =>
        rw [ih] at ht
        simp
        rw [εClosure_mul_left] at hs
        exact ⟨t, ht, hs⟩
    . intro h
      simp at h
      match h with
      | ⟨t, ht, hs⟩ =>
        rw [←ih t] at ht
        rw [←εClosure_mul_left] at hs
        simp
        exact ⟨t, ht, hs⟩

theorem eval_mul_left_right (x : List α) (p : σ) (q : σ') :
  p ∈ P.accept ∧ q ∈ Q.εClosure Q.start ∧ Sum.inl p ∈ (P.mul Q).eval x → Sum.inr q ∈ (P.mul Q).eval x := by
  intro ⟨hp, hq, hx⟩
  cases x using List.reverseRecOn with
  | nil =>
    simp at *
    rw [←εClosure_mul_left] at hx
    rw [εClosure_mul_left_accept _ _ _ _ ⟨p, hp, hx⟩] at hq
    exact hq
  | append_singleton xs x _ =>
    simp at hx
    match hx with
    | ⟨t, ht, hp'⟩ =>
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
    apply eval_mul_left_right
    exact ⟨hp, hq, ha⟩
  | append_singleton bs b ih =>
    simp at *
    match hq with
    | ⟨t, ht, hq⟩ =>
      have ih := ih t ht
      rw [←List.append_assoc]
      rw [eval_append_singleton]
      simp
      right
      exact ⟨t, ih, hq⟩

-- theorem eval_mul_left_right' (x : List α) (q : σ') :
--   Sum.inr q ∈ (P.mul Q).eval x →
--   ∃ a b, x = a ++ b ∧ a ∈ P.accepts := by
--   intro h
--   induction x using List.reverseRecOn generalizing q with
--   | nil =>
--     simp at *
--     have h := εClosure_mul_left_accept' _ _ _ q h
--     match h with
--     | ⟨p, hp⟩ =>
--       rw [←εClosure_mul_left] at hp
--       use p
--   | append_singleton xs x ih =>
--     simp at h
--     cases h with
--     | inl h =>
--       match h with
--       | ⟨p, hp, hq'⟩ =>
--         have h := εClosure_mul_left_accept' _ _ _ _ hq'
--         rw [←eval_mul_left_left] at hp
--         match h with
--         | ⟨p', hp', hx⟩ =>
--           rw [←εClosure_mul_left] at hx
--           use (xs ++ [x]), []
--           simp
--           exact ⟨p', hp', p, hp, hx⟩
--     | inr h =>
--       match h with
--       | ⟨q', hq, _⟩ =>
--         have ih := ih q' hq
--         match ih with
--         | ⟨a, b, hxs, ha⟩ =>
--           use a, b ++ [x]
--           rw [←List.append_assoc, hxs]
--           exact ⟨rfl, ha⟩


-- theorem eval_mul_left_right'' (x : List α) (q : σ') :
--   Sum.inr q ∈ (P.mul Q).eval x →
--   ∃ a b, x = a ++ b ∧ q ∈ Q.eval b := by
--   intro h
--   induction x using List.reverseRecOn generalizing q with
--   | nil =>
--     use [], []
--     refine' ⟨rfl, _⟩
--     simp at *
--     apply εClosure_mul_left_accept'' at h
--     exact h
--   | append_singleton xs x ih =>
--     simp at h
--     cases h with
--     | inl h =>
--       match h with
--       | ⟨p, _, hq'⟩ =>
--         apply εClosure_mul_left_accept'' at hq'
--         use (xs ++ [x]), []
--         simp
--         exact hq'
--     | inr h =>
--       match h with
--       | ⟨q', hq, hq'⟩ =>
--         have ih := ih q' hq
--         match ih with
--         | ⟨a, b, hxs, hb⟩ =>
--           use a, b ++ [x]
--           rw [←List.append_assoc, hxs]
--           refine' ⟨rfl, _⟩
--           simp
--           exact ⟨q', hb, hq'⟩

theorem eval_mul_left_right' (x : List α) (q : σ') :
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
          exact ⟨⟨p', hp', p, hp, hx⟩, hq''⟩
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
          exact ⟨q', ha.right, hq'⟩

-- theorem eval_mul_left_right_iff (x : List α) (q : σ') :
--   Sum.inr q ∈ (P.mul Q).eval x ↔
--   ∃ a b, x = a ++ b ∧ a ∈ P.accepts ∧ q ∈ Q.eval b := by
--   constructor
--   . apply eval_mul_left_right'
--   . intro h
--     simp at h
--     match h with
--     | ⟨a, b, hx, ⟨p, hp, ha⟩, hb⟩ =>
--       rw [←eval] at ha
--       rw [hx]
--       apply eval_mul_left_right_split
--       exact ⟨hp, ha, hb⟩

-- theorem split'' (n : Nat) (s : List α) (P1 P2 : List α → Prop) :
--   n ≤ s.length →
--  (∃ s1 s2, s1.length ≤ n ∧ s1 ++ s2 = s ∧ P1 s1 ∧ P2 s2) ∨
--  ¬(∃ s1 s2, s1.length ≤ n ∧ s1 ++ s2 = s ∧ P1 s1 ∧ P2 s2) := by
--   intro
--   tauto

-- theorem split' (n : Nat) (s : List α) (P1 P2 : List α → Prop) :
--   n ≤ s.length →
--  (∃ s1 s2, s1.length ≤ n ∧ s1 ++ s2 = s ∧ P1 s1 ∧ P2 s2) ∨
--  (∀ s1 s2, s1.length ≤ n → s1 ++ s2 = s → ¬P1 s1 ∨ ¬P2 s2) := by
--   intro h
--   have h := split'' n s P1 P2 h
--   simp at *
--   cases h with
--   | inl h =>
--     left
--     exact h
--   | inr h =>
--     intros
--     tauto

-- theorem split (s : List α) (P1 P2 : List α → Prop) : (∃ s1 s2, s = s1 ++ s2 ∧ P1 s1 ∧ P2 s2) ∨
--   (∀ s1 s2, s = s1 ++ s2 → ¬P1 s1 ∨ ¬P2 s2) := by
--   have h := ((split' (s.length) s P1 P2) (le_refl s.length))
--   aesop

-- theorem accepts_mul' : x ∈ (P.mul Q).accepts → ∃ a ∈ P.accepts, ∃ b ∈ Q.accepts, a ++ b = x := by
--   intro h
--   match x with
--   | [] =>
--     simp at *
--     match h with
--     | ⟨q, ⟨hq, h⟩⟩ =>
--       have hq' := εClosure_mul_left_accept'' _ _ _ _ h
--       have hp := εClosure_mul_left_accept' _ _ _ _ h
--       match hp with
--       | ⟨p, ⟨hp, hp'⟩⟩ =>
--         rw [←εClosure_mul_left] at hp'
--         exact ⟨⟨p, ⟨hp, hp'⟩⟩, ⟨q, ⟨hq, hq'⟩⟩⟩
--   | x =>
--     simp at h
--     match h with
--     | ⟨q, hq, h⟩ =>
--       have h' := eval_mul_left_righ _ _ _ _ h
--       match h' with
--       | ⟨a, b, hx, ha, hb⟩ =>
--         rw [hx]
--         simp
--         exact ⟨a, ha, b, ⟨q, hq, hb⟩, rfl⟩

@[simp]
theorem accepts_mul : (P.mul Q).accepts = P.accepts * Q.accepts := by
  ext x
  rw [Language.mem_mul]
  constructor
  . intro h
    simp at h
    match h with
    | ⟨q, hq, h⟩ =>
      apply eval_mul_left_right' at h
      match h with
      | ⟨a, b, hx, ha, hb⟩ =>
        rw [hx]
        simp
        exact ⟨a, ha, b, ⟨q, hq, hb⟩, rfl⟩
  . intro h
    simp at h
    match h with
    | ⟨a, ⟨p, hp, ha⟩, b, ⟨q, hq, hb⟩, hx⟩ =>
      simp
      rw [←eval] at ha
      rw [←hx]
      refine' ⟨q, hq, _⟩
      apply eval_mul_left_right_split
      exact ⟨hp, ha, hb⟩

@[simp]
theorem εClosure_star_none (S : Set (Option σ)) :
  none ∈ P.star.εClosure S ↔ none ∈ S := by
  constructor
  . intro h
    cases h with
    | base _ hs => exact hs
    | step s _ h hs =>
      match s with
      | none => simp at h
      | some s =>
        absurd h
        apply step_star_some_none_none
  . intro h
    simp at *
    exact εClosure.base none h

-- theorem εClosure_star_none' (S : Set σ) :
--   none ∉ P.star.εClosure (some '' S) := by
--   rw [εClosure_star_none]
--   simp

-- theorem εClosure_star_not_accept (S : Set σ) :
--   (∀ p ∈ P.accept, p ∉ P.εClosure S) → P.star.εClosure (some '' S) = some '' P.εClosure S := by
--   intro h
--   ext x
--   constructor
--   . intro h
--     induction h with
--     | base s hs =>
--       simp at *
--       match hs with
--       | ⟨x, hx, hs⟩ =>
--         exact ⟨x, εClosure.base _ hx, hs⟩
--     | step s t ht hs ih =>
--       simp at *
--       match ih with
--       | ⟨k, ih, hs⟩ =>
--         rw [←hs] at ht
--         have hk' : k ∉ P.accept := by
--           contrapose h
--           simp at *
--           exact ⟨k, h, ih⟩
--         rw [step_star_some_none_not_accept P k hk'] at ht
--         simp at ht
--         match ht with
--         | ⟨x, hx, ht⟩ =>
--           exact ⟨x, εClosure.step k x hx ih, ht⟩
--   . intro h
--     simp at h
--     match h with
--     | ⟨k, hk, hx⟩ =>
--       induction hk generalizing x with
--       | base s hs =>
--         apply mem_image_of_mem some at hs
--         rw [hx] at hs
--         exact εClosure.base _ hs
--       | step s t ht hs ih =>
--         have hs := ih (some s) ⟨s, hs, rfl⟩ rfl
--         apply step_star_some_none at ht
--         rw [hx] at ht
--         exact εClosure.step _ _ ht hs

theorem εClosure_star_some (s : σ) (S : Set σ) :
  s ∈ P.εClosure S → some s ∈ P.star.εClosure (some '' S) := by
  intro h
  induction h with
  | base _ hs =>
    apply mem_image_of_mem some at hs
    exact εClosure.base _ hs
  | step t k hs _ ih =>
    apply step_star_some_none at hs
    exact εClosure.step _ _ hs ih

-- theorem εClosure_star_accept (s : σ) (S : Set σ) :
--   (∃ p ∈ P.accept, p ∈ P.εClosure S) →
--   (s ∈ P.εClosure P.start → some s ∈ P.star.εClosure (some '' S)) := by
--   intro h hs
--   induction hs with
--   | base s hs =>
--     match h with
--     | ⟨x, hx, hx'⟩ =>
--       have hs := step_star_accept_start _ _ _ ⟨hx, hs⟩
--       apply εClosure_star_some at hx'
--       exact εClosure.step _ _ hs hx'
--   | step s t ht _ ih =>
--     apply step_star_some_none at ht
--     exact εClosure.step _ _ ht ih

theorem εClosure_star_accept' (p q : σ) (S : Set (Option σ)) :
  p ∈ P.accept ∧ q ∈ P.εClosure P.start ∧ some p ∈ P.star.εClosure S → some q ∈ P.star.εClosure S := by
  intro ⟨hp, hq, h⟩
  induction hq with
  | base q hq =>
    have hq := step_star_accept_start _ _ _ ⟨hp, hq⟩
    exact εClosure.step (some p) (some q) hq h
  | step s t ht _ ih =>
    apply step_star_some_none at ht
    exact εClosure.step (some s) (some t) ht ih

theorem εClosure_star_some'' (p : σ) (S : Set σ) :
  some p ∈ P.star.εClosure (some '' S) →
  (∃ t ∈ P.εClosure S, t ∈ P.accept) ∧ p ∈ P.εClosure P.start ∨ p ∈ P.εClosure S := by
  intro h
  apply mem_fun at h
  match h with
  | ⟨x, h, hp⟩ =>
    induction h generalizing p with
    | base s hs =>
      rw [←hp] at hs
      simp at *
      right
      exact εClosure.base _ hs
    | step s t ht hs ih =>
      rw [←hp] at ht
      cases s with
      | none =>
        rw [←@mem_def _ _ (P.star.εClosure (some '' S)), εClosure_star_none] at hs
        simp at hs
      | some s =>
        have ih := ih s ⟨some s, hs, rfl⟩ rfl
        cases ih with
        | inl ih =>
          left
          simp at ih
          by_cases h' : s ∈ P.accept
          . rw [step_star_some_none_accept _ _ h'] at ht
            simp at ht
            cases ht with
            | inl ht => exact ⟨ih.left, εClosure.step s p ht ih.right⟩
            | inr ht => exact ⟨ih.left, εClosure.base _ ht⟩
          . rw [step_star_some_none_not_accept _ _ h'] at ht
            simp at ht
            exact ⟨ih.left, εClosure.step s p ht ih.right⟩
        | inr ih =>
          by_cases h' : s ∈ P.accept
          . rw [step_star_some_none_accept _ _ h'] at ht
            simp at ht
            cases ht with
            | inl ht =>
              right
              exact εClosure.step s p ht ih
            | inr ht =>
              left
              exact ⟨⟨s, ih, h'⟩, εClosure.base _ ht⟩
          . rw [step_star_some_none_not_accept _ _ h'] at ht
            simp at ht
            right
            exact εClosure.step s p ht ih

@[simp]
theorem εClosure_star_start (x : σ) :
  x ∈ P.εClosure P.start ↔ some x ∈ P.star.εClosure P.star.start := by
  constructor
  . intro h
    induction h with
    | base s hs =>
      simp
      apply step_star_start at hs
      exact εClosure.step none (some s) hs ((subset_εClosure _ { none }) (mem_singleton none))
    | step s t ht hs ih =>
      simp at *
      apply step_star_some_none at ht
      exact εClosure.step (some s) (some t) ht ih
  . intro h
    apply mem_fun at h
    match h with
    | ⟨y, h, hy⟩ =>
      induction h generalizing x with
      | base s hs =>
        rw [←hy] at hs
        simp at hs
      | step s t ht hs ih =>
        rw [←hy] at ht
        cases s with
        | none =>
          simp at ht
          exact εClosure.base _ ht
        | some s =>
          by_cases h : s ∈ P.accept
          . rw [step_star_some_none_accept _ _ h] at ht
            simp at ht
            cases ht with
            | inl ht =>
              have ih := ih s ⟨s, hs, rfl⟩ rfl
              exact εClosure.step s x ht ih
            | inr ht => exact εClosure.base _ ht
          . rw [step_star_some_none_not_accept _ _ h] at ht
            simp at ht
            have ih := ih s ⟨s, hs, rfl⟩ rfl
            exact εClosure.step s x ht ih

theorem eval_star (s : σ) (x : List α) :
  s ∈ P.eval x → some s ∈ P.star.eval x := by
  intro h
  induction x using List.reverseRecOn generalizing s with
  | nil =>
    simp at *
    exact h
  | append_singleton xs x ih =>
    simp at h
    match h with
    | ⟨t, ht, hs⟩ =>
      have ih := ih t ht
      simp
      apply εClosure_star_some at hs
      refine' ⟨some t, ih, _⟩
      rw [step_star_some_some]
      exact hs

@[simp]
theorem eval_star_none (x : List α) :
  none ∈ P.star.eval x ↔ x = [] := by
  cases x using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x => simp

theorem eval_star_accept (x : List α) (p : σ) (q : σ) :
  p ∈ P.accept ∧ q ∈ P.εClosure P.start ∧ some p ∈ P.star.eval x → some q ∈ P.star.eval x := by
  intro ⟨hp, hq, hx⟩
  cases x using List.reverseRecOn with
  | nil =>
    simp at *
    exact hq
  | append_singleton xs x =>
    simp at hx
    match hx with
    | ⟨t, ht, hx⟩ =>
      have hq := εClosure_star_accept' _ _ _ _ ⟨hp, hq, hx⟩
      simp
      refine' ⟨t, ht, hq⟩

-- theorem eval_star_split (a b : List α) (p q : σ) :
--   p ∈ P.accept ∧ p ∈ P.eval a ∧ q ∈ P.eval b → some q ∈ P.star.eval (a ++ b) := by
--   intro ⟨hp, ha, hb⟩
--   induction b using List.reverseRecOn generalizing q with
--   | nil =>
--     simp at *
--     apply eval_star at ha
--     apply eval_star_accept
--     simp
--     exact ⟨hp, hb, ha⟩
--   | append_singleton bs b ih =>
--     simp at *
--     match hb with
--     | ⟨t, ht, hq⟩ =>
--       have ih := ih t ht
--       apply εClosure_star_some at hq
--       rw [←step_star_some_some] at hq
--       rw [←List.append_assoc]
--       rw [eval_append_singleton]
--       simp
--       exact ⟨t, ih, hq⟩

theorem eval_star_split (a b : List α) (p : Option σ) (q : σ) :
  p ∈ P.star.accept ∧ p ∈ P.star.eval a ∧ some q ∈ P.star.eval b → some q ∈ P.star.eval (a ++ b) := by
  intro ⟨hp, ha, hb⟩
  induction b using List.reverseRecOn generalizing q with
  | nil =>
    simp at *
    cases hp with
    | inl hp =>
      rw [hp] at ha
      simp at ha
      rw [ha]
      simp
      exact hb
    | inr hp =>
      rw [←start_star] at hb
      rw [←εClosure_star_start] at hb
      match hp with
      | ⟨p', hp', hp⟩ =>
        rw [←hp] at ha
        apply eval_star_accept
        exact ⟨hp', hb, ha⟩
  | append_singleton as a' ih =>
    simp at hp
    cases hp with
    | inl hp =>
      rw [hp] at ha
      simp at ha
      rw [ha, List.nil_append]
      exact hb
    | inr hp =>
      simp at hb
      match hb with
      | ⟨t, ht, hq⟩ =>
        cases t with
        | none => simp at *
        | some t =>
          have ih := ih t ht
          rw [←List.append_assoc, eval_append_singleton]
          simp
          exact ⟨t, ih, hq⟩

-- theorem accepts_star_empty :
--   [] ∈ P.star.accepts := by
--   simp

theorem accepts_star_accepts (x : List α) :
  x ∈ P.accepts → x ∈ P.star.accepts := by
  intro h
  simp at *
  match h with
  | ⟨s, hs, hx⟩ =>
    rw [←eval] at hx
    apply eval_star at hx
    right
    refine' ⟨s, hs, hx⟩

-- theorem accepts_star_accepts_split (a b : List α) :
--   a ∈ P.accepts ∧ b ∈ P.accepts → a ++ b ∈ P.star.accepts := by
--   intro h
--   simp at *
--   match h with
--   | ⟨⟨p, hp, ha⟩, q, hq, hb⟩ =>
--     right
--     refine' ⟨q, hq, _⟩
--     apply eval_star_split
--     exact ⟨hp, ha, hb⟩

theorem accepts_star_split (a b : List α) :
  a ∈ P.star.accepts ∧ b ∈ P.star.accepts → a ++ b ∈ P.star.accepts := by
  intro h
  cases a using List.reverseRecOn with
  | nil =>
    rw [List.nil_append]
    exact h.right
  | append_singleton as a =>
    cases b using List.reverseRecOn with
    | nil =>
      rw [List.append_nil]
      exact h.left
    | append_singleton bs b =>
      simp at *
      match h with
      | ⟨⟨p, hp, ha⟩, q, hq, hb⟩ =>
        right
        refine' ⟨q, hq, _⟩
        rw [List.append_cons]
        apply eval_star_split _ _ _ (some p)
        rw [←mem_stepSet_iff, ←evalFrom_append_singleton, ←start_star, ←eval] at ha hb
        refine' ⟨_, ha, hb⟩
        simp
        exact hp

theorem eval_star' (x : List α) (q : σ) :
  some q ∈ P.star.eval x →
  ∃ (ys : List (List α)) (z : List α),
  x = ys.join ++ z ∧ q ∈ P.eval z ∧ ∀ y ∈ ys, y ∈ P.accepts := by
  intro h
  induction x using List.reverseRecOn generalizing q with
  | nil =>
    use [], []
    simp
    exact h
  | append_singleton xs x ih =>
    simp at h
    match h with
    | ⟨t, ht, hq⟩ =>
      cases t with
      | none => simp at *
      | some t =>
        simp at hq
        apply εClosure_star_some'' at hq
        have ih := ih t ht
        match ih with
        | ⟨ys, z, hxs, ht, hys⟩ =>
          cases hq with
          | inl hq =>
            rw [hxs]
            refine' ⟨ys ++ [z ++ [x]], [], by simp, hq.right, _⟩
            refine' List.forall_mem_append.mpr ⟨hys, List.forall_mem_singleton.mpr _⟩
            simp
            match hq.left with
            | ⟨k, hk, hk'⟩ =>
              refine' ⟨k, hk', t, ht, hk⟩
          | inr hq =>
            use ys, (z ++ [x])
            rw [←List.append_assoc, hxs]
            refine' ⟨rfl, _, hys⟩
            simp
            exact ⟨t, ht, hq⟩

@[simp]
theorem accepts_star : P.star.accepts = P.accepts∗ := by
  ext x
  rw [Language.mem_kstar]
  constructor
  . intro h
    simp at h
    cases h with
    | inl h =>
      refine' ⟨[], _⟩
      rw [←start_star, ←eval, eval_star_none] at h
      simp
      exact h
    | inr h =>
      match h with
      | ⟨p, hp, hx⟩ =>
        apply eval_star' at hx
        match hx with
        | ⟨ys, z, hx, hp', hys⟩ =>
          have hz := (mem_accepts _ z).mpr ⟨p, hp, hp'⟩
          refine' ⟨ys ++ [z], _⟩
          rw [List.join_append, List.join_singleton]
          refine' ⟨hx, _⟩
          rw [List.forall_mem_append, List.forall_mem_singleton]
          exact ⟨hys, hz⟩
  . intro ⟨L, hx, hy⟩
    induction L generalizing x with
    | nil =>
      simp at hx
      rw [hx]
      simp
    | cons l ls ih =>
      unfold List.join at hx
      rw [List.forall_mem_cons] at hy
      have ih := ih (List.join ls) rfl hy.right
      have hl := accepts_star_accepts _ _ hy.left
      rw [hx]
      apply accepts_star_split
      exact ⟨hl, ih⟩

end εNFA
