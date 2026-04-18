/-
  # TAPL Chapter 3 — Untyped Boolean Terms

  A Lean 4 formalisation of the untyped boolean language from
  *Types and Programming Languages* (Pierce, 2002), Chapter 3.
-/

import Mathlib



inductive Term : Type where
  | tru   : Term
  | fls   : Term
  | ite    : Term → Term → Term → Term   -- if t₁ then t₂ else t₃
deriving Repr, DecidableEq

namespace Term

inductive BoolVal : Term → Prop where
  | tru  : BoolVal tru
  | fls : BoolVal fls

/-- Values = boolean values ∪ numeric values -/
inductive Val : Term → Prop where
  | bool (t : Term) : BoolVal t → Val t

inductive Step : Term → Term → Prop where
  -- E-IfTrue
  | ite_true  (t₂ t₃ : Term) :
      Step (ite tru t₂ t₃) t₂
  -- E-IfFalse
  | ite_false (t₂ t₃ : Term) :
      Step (ite fls t₂ t₃) t₃
  -- E-If  (congruence)
  | ite_cong  (t₁ t₁' t₂ t₃ : Term) :
      Step t₁ t₁' →
      Step (ite t₁ t₂ t₃) (ite t₁' t₂ t₃)

notation:50 t " ⟶ " t' => Step t t'

/-- Number of constants in a term (p. 29) -/
def consts (t : Term) : Finset Term :=
  match t with
  | tru => {tru}
  | fls => {fls}
  | ite t₁ t₂ t₃ => consts t₁ ∪ consts t₂ ∪ consts t₃

/-- Size of an term (number of nodes
    in the syntax graph) (p. 29) -/
def size (t : Term) : ℕ :=
  match t with
  | tru => 1
  | fls => 1
  | ite t₁ t₂ t₃ => size t₁ + size t₂ + size t₃ + 1

lemma size_gt_zero (t : Term) : size t > 0 := by
  induction t <;> simp [size]

/-- Depth of a term (p. 30) -/
def depth (t : Term) : ℕ :=
  match t with
  | tru => 1
  | fls => 1
  | ite t₁ t₂ t₃ => max (max (depth t₁) (depth t₂)) (depth t₃) + 1

lemma depth_gt_zero (t : Term) : depth t > 0 := by
  induction t <;> simp [depth]

/- THEOREM 3.3.4.
  This theorem captures the idea that if
  we can label each term with a natural number,
  then we can prove it by an induction on the
  assigned numbers.

  We go a step more general than the book, as we
  allow any indexing function `i`, but this is
  largely a cosmetic change.
-/
theorem induction_principle (P : Term → Prop) (i : Term → ℕ) :
  (∀ t : Term, P t) ↔ (∀ n : ℕ, ∀ t : Term, i t ≤ n → P t) := by
  constructor
  · intro h n t h'
    exact h t
  · intro h t
    let n : ℕ := i t
    apply h n t
    exact refl n

/-- LEMMA 3.3.3. The number of distinct
    constants in a term t is no greater
    than the size of t
    (i.e., |Consts(t)| ≤ size(t)) (p. 30) -/
lemma const_le_size (t : Term) :  Finset.card (consts t) ≤ (size t) := by
  have one_nonneg : 0 ≤ 1 := by linarith
  induction t with
  | tru | fls => simp [consts, size]
  | ite t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    simp? [consts, size]
    rw [← Finset.union_assoc]
    calc (consts t₁ ∪ consts t₂ ∪ consts t₃).card
    ≤ (consts t₁ ∪ consts t₂).card + (consts t₃).card := Finset.card_union_le _ _
    _ ≤ (consts t₁).card + (consts t₂).card + (consts t₃).card := by
      linarith [Finset.card_union_le (consts t₁) (consts t₂)]
    _ ≤ (size t₁) + (size t₂) + (size t₃) + 1 := by linarith [ih₁, ih₂, ih₃]

theorem depth_induction (P : Term → Prop) :
  (∀ t : Term, (∀ s : Term, depth s < depth t → P s) → P t)
    → ∀ s : Term, P s  := by
  intro h
  rw [induction_principle P depth]
  intro n
  induction n with
  | zero =>
    intro t dep_le_zero
    linarith [depth_gt_zero t]
  | succ n ih =>
    intro t dep_le
    have : (∀ (s : Term), s.depth < t.depth → P s) := by
      intro s ineq
      have := lt_of_lt_of_le ineq dep_le
      have :=  Nat.le_of_lt_add_one this
      exact ih s this
    exact h t this


theorem determinacy_of_step (t t' t'' : Term) (h : Step t t') (h' : Step t t'') : t' = t'' := by
  induction h generalizing t'' with
  | ite_true t₁ t₂ =>
    cases h' with
    | ite_true => exact refl t₁
    | ite_cong _ _ _ _ h => cases h
  | ite_false t₁ t₂ =>
    cases h' with
    | ite_false => exact refl t₂
    | ite_cong _ _ _ _ h => cases h
  | ite_cong t₁ t₁' t₂ t₃ h ih =>
    cases h' with
    | ite_cong _ t₁'' _ _ h' =>
      rw[ih t₁'' h']
    | ite_true | ite_false => cases h

def isNormal (t : Term) : Prop := ¬ ∃ t' : Term, Step t t'

lemma value_normal (v : Term) (h : Val v) : isNormal v := by
  rw [isNormal]
  by_contra
  rcases this with ⟨t', h'⟩
  cases h with
  | bool u =>
    cases u with
    | tru | fls  => cases h'

/- From this we can prove that we cannot make
  any steps on a value. -/
lemma val_step_fls (t t' : Term) (h : Val t) : Step t t' → false := by
  have : isNormal t := value_normal t h
  rw [isNormal] at this
  intro s
  exact absurd ⟨t', s⟩ this

lemma normal_value (t : Term) (h : isNormal t) : Val t := by
  rw [isNormal] at h
  induction t with
  -- `tru` and `fls` are values by construction
  | tru => exact Val.bool tru (BoolVal.tru)
  | fls => exact Val.bool fls (BoolVal.fls)
  | ite t₁ t₂ t₃ ih =>
    by_cases h' : isNormal t₁
    -- if t₁ is normal, then by ih it is a value
    -- in which case we can simplify
    · have := ih h'
      cases this with
      | bool v => cases v with
        | tru =>
          exact absurd ⟨t₂, Step.ite_true t₂ t₃⟩ h
        | fls =>
          exact absurd ⟨t₃, Step.ite_false t₂ t₃⟩ h
    -- otherwise, we can simplify t₁, and use that
    -- step in ite_cong
    · simp?[isNormal] at h'
      rcases h' with ⟨t', h''⟩
      exact absurd ⟨Term.ite t' t₂ t₃, Step.ite_cong t₁ t' t₂ t₃ h''⟩ h

/- We define the multi-step closure of 3.5.9.
  as another relation between terms.

  I chose to have Steps wrap at least one step,
  which implies that Steps t t is always false.
  this is convenient, because it makes the Steps
  relation strictly monotonic on the size of the
  terms involved.
  -/
inductive Steps : Term → Term → Prop where
| refl (t t' : Term) : Step t t' →  Steps t t'
| trans (t t' t'' : Term) : Step t t' → Steps t' t'' → Steps t t''

lemma back_extend_steps (t t' t'' : Term) (h : Steps t t') (s : Step t' t'') : Steps t t'' := by
  induction h with
  | refl t t' s₁ =>
    exact Steps.trans t t' t'' s₁ (Steps.refl t' t'' s)
  | trans t t₁ t' s₁ steps ih =>
    exact Steps.trans t t₁ t'' s₁ (ih s)

/- This trivial lemma wraps the statement
  of isNormal for Steps.
-/
lemma normal_steps_fls (t t' : Term) (h : isNormal t) : Steps t t' → False := by
  intro h'
  cases h' with
  | refl _ _ s   => exact absurd ⟨t', s⟩ h
  | trans _ t'' _ s _ => exact absurd ⟨t'', s⟩ h

/- THEOREM 3.5.11., p. 39-/
theorem unique_normal_form (t t' t'' : Term)
    (e' : Steps t t') (e'' : Steps t t'')
    (h' : isNormal t') (h'' : isNormal t'') : t' = t'' := by
  induction e' generalizing t'' with
  -- First, assume that e' is a single step
  | refl t t' s =>
    cases e'' with
    -- If e'' is also, we simply apply `determinacy_of_step`
    | refl t t' s' =>
      exact determinacy_of_step t t' t'' s s'
    /- otherwise, we can use the single step of
      e' and determinacy of step to find that
      t' →* t'', where t' is normal -- absurd -/
    | trans t₁ t₁' t₁''' s'₁ s'₂ =>
      have := determinacy_of_step t t' t₁' s s'₁
      rw [this] at h'
      exact (normal_steps_fls t₁' t'' h' s'₂).elim
  | trans t t₁ t' s s' ih =>
    cases e'' with
    -- same idea as in the previous case
    | refl t t'' s₁' =>
      have := determinacy_of_step t t₁ t'' s s₁'
      rw [this] at s'
      exact (normal_steps_fls t'' t' h'' s').elim
    /- by determinacy of step, we prove that
      t₁ = t₂, use the two Steps on t₁ and
      t₂ and use the induction hypothesis. -/
    | trans t t₂ t'' s₁' s₁'' =>
      have := determinacy_of_step t t₁ t₂ s s₁'
      rw [← this] at s₁''
      exact ih t'' s₁'' h' h''

/- We now prove 3.5.12. We start by proving
  that each step decreases the size of a
  term
-/
lemma step_decreases_size (t t' : Term) : Step t t' → size t' < size t := by
  intro s
  induction s with
  | ite_true | ite_false | ite_cong =>
    simp [size]
    linarith

/- An artifact of our choice to define Steps
  to wrap at least one step is that
  normalisability of us can mean one of two things
  1. the term is already normal, or
  2. there is t' with Steps t t' and
    t' normal
-/
def isNormalisable (t : Term) := isNormal t ∨ ∃ t' : Term, Steps t t' ∧ isNormal t'

/- THEOREM 3.5.12., p.39
  Proving the theorem in this
  from makes it easier to do induction
  on the size of terms. Since every
  term has finite size, this is of
  course equivalent to the more direct
  phrasing
  `∀ t : Term, isNormalisable t`
  but we avoid some extra boilerplate by
  omitting the application of
  `induction_principle`
-/
theorem evaluation_term : ∀ n : ℕ, ∀ t : Term, size t ≤ n → isNormalisable t := by
  intro n
  induction n with
  -- Terms cannot have size 0
  | zero =>
    intro t t_le_zero
    have := size_gt_zero t
    linarith
  -- Inductions step
  | succ n ih =>
    intro t size_t_le_n
    by_cases h : isNormal t
    -- if t is already normal, we are done
    · exact Or.inl h
    -- otherwise, we analyse what t steps to
    · simp? [isNormal] at h
      rcases h with ⟨t', s⟩
      -- since t → t', t' must have smaller size
      have := step_decreases_size t t' s
      have size_t'_le_n : t'.size ≤ n := by linarith
      -- and by ih it is normalisable
      have := ih t' size_t'_le_n
      rcases this with h'|h'
      -- If it is normal, we are again done
      · exact Or.inr ⟨t', ⟨Steps.refl t t' s, h'⟩⟩
      /- If not, then we chain the normalising Steps
        of t' with s to get a normalising chain for t -/
      · rcases h' with ⟨t₁', steps, t₁'_normal⟩
        exact Or.inr ⟨t₁', Steps.trans t t' t₁' s steps, t₁'_normal⟩

end Term
