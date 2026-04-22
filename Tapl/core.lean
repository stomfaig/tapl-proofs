import Mathlib

inductive BoolF (α : Type)
  | tru
  | fls
  | ite : α → α → α → BoolF α

instance : Functor BoolF where
  map := fun {α β} (f : α → β) (b : BoolF α) =>
    match b with
    | BoolF.tru           => BoolF.tru
    | BoolF.fls           => BoolF.fls
    | BoolF.ite t₁ t₂ t₃ => BoolF.ite (f t₁) (f t₂) (f t₃)

def BoolF.All : BoolF Prop → Prop
  | BoolF.tru           => True
  | BoolF.fls           => True
  | BoolF.ite p₁ p₂ p₃ => p₁ ∧ p₂ ∧ p₃

def BoolF.children (t : BoolF Term) : List Term :=
  match t with
  | BoolF.tru | BoolF.fls => []
  | BoolF.ite t₁ t₂ t₃ => [t₁, t₂, t₃]

inductive Term where
  | node : BoolF Term → Term

namespace Term

def fold {α : Type} (alg : BoolF α → α) (t : Term) : α :=
  match t with
  | Term.node b => match b with
    | BoolF.tru           => alg BoolF.tru
    | BoolF.fls           => alg BoolF.fls
    | BoolF.ite t₁ t₂ t₃ => alg (BoolF.ite
        (Term.fold alg t₁)
        (Term.fold alg t₂)
        (Term.fold alg t₃))


def induction (P : Term → Prop)
  (alg : ∀ b : BoolF Term, (Functor.map P b).All → P (Term.node b)) : ∀ t : Term, P t := by
  intro t
  match t with
  | node bt =>
    have := alg bt
    match bt with
    | BoolF.tru | BoolF.fls =>
      simp [BoolF.All] at this
      exact this
    | BoolF.ite t₁ t₂ t₃ =>
      have h := Term.induction P alg t₁
      have h' := Term.induction P alg t₂
      have h'' := Term.induction P alg t₃
      simp [BoolF.All, h, h', h''] at this
      exact this

inductive Children (P : Term → Prop) (t : BoolF Term) : Prop where
  | tru
  | fls
  | ite (c t₁ t₂ : Term)
    (hc : P c) (h₁ : P t₁) (h₂ : P t₂)

def children_induction (P : Term → Prop)
  (alg : ∀ b : BoolF Term, (Children P b) → P (Term.node b)) : ∀ t : Term, P t := by
  intro t
  match t with
  | node bt =>
    have := alg bt
    match bt with
    | BoolF.tru | BoolF.fls =>
      exact this Children.tru
    | BoolF.ite t₁ t₂ t₃ =>
      have h := Term.children_induction P alg t₁
      have h' := Term.children_induction P alg t₂
      have h'' := Term.children_induction P alg t₃
      exact this (Children.ite t₁ t₂ t₃ h h' h'')

@[match_pattern]
def tru : Term :=
  Term.node BoolF.tru

@[match_pattern]
def fls : Term :=
  Term.node BoolF.fls

@[match_pattern]
def ite (c t₁ t₂ : Term) : Term :=
  Term.node (BoolF.ite c t₁ t₂)

end Term
