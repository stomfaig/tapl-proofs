import Mathlib

/-
  Formalisation of the simply typed lambda calculus with booleans.

  The formalisation largely follows chapter 9 of Pierce's TAPL book,
  except for the changes that are needed for the case of de Brujin
  indices.

  Also, instead of using the more usual insert_at type maps to
  manipulate contexts, we use somewhat different ideas, which
  seem to be conceptually cleaner: (1) the swap function on
  contexts, which swaps two type annotations in the context,
  (2) the drop function on contexts, which removes a single
  type annotation from the context, shifting all other annotations
  down.
-/

inductive Ty : Type where
| Bool : Ty
| Fn : Ty → Ty → Ty
deriving Repr, DecidableEq

inductive Term : Type where
  | True : Term
  | False : Term
  | Ite : Term → Term → Term → Term
  | Var : ℕ → Term
  -- we require type annotations for the bound var.
  | Abs : Term → Ty → Term
  | App : Term → Term → Term
deriving Repr, DecidableEq

namespace  Term

def FV (t : Term) : Finset ℕ :=
  match t with
  | True => {}
  | False => {}
  | Ite t₁ t₂ t₃ => FV t₁ ∪ FV t₂ ∪ FV t₃
  | Var n => {n}
  | Abs t _ => FV t \ {0}
  | App t t' => FV t ∪ FV t'

def shift (cutoff : ℕ) (amount : ℕ) (t : Term) : Term :=
  match t with
  | True => True
  | False => False
  | Ite t₁ t₂ t₃ => Ite
    (shift cutoff amount t₁)
    (shift cutoff amount t₂)
    (shift cutoff amount t₃)
  | Var n => if n ≥ cutoff then Var (n + amount) else Var n
  | Abs t ty => Abs (shift (cutoff + 1) amount t) ty
  | App t t' => App (shift cutoff amount t) (shift cutoff amount t')

-- idea: [j ↦ s]t
def subsitute (j : ℕ) (s t : Term) : Term :=
  match t with
  | True => True
  | False => False
  | Ite t₁ t₂ t₃ => Ite
    (subsitute j s t₁)
    (subsitute j s t₂)
    (subsitute j s t₃)
  | Term.Var n => if n = j then s else if n > j then Term.Var (n - 1) else Term.Var n
  | Term.Abs t ty => Term.Abs (subsitute (j + 1) (shift 0 1 s) t) ty
  | Term.App t t' => Term.App (subsitute j s t) (subsitute j s t')

def isValue (t : Term) : Bool :=
  match t with
  | True | False | Abs _ _ => true
  | _ => false

inductive Step : Term → Term → Prop where
  | ite_true (t₁ t₂ : Term) :
    Step (Ite True t₁ t₂) t₁
  | ite_false (t₁ t₂ : Term) :
    Step (Ite False t₁ t₂) t₂
  | ite_step (t₁ t₁' t₂ t₃ : Term) : Step t₁ t₁' →
    Step (Ite t₁ t₂ t₃) (Ite t₁' t₂ t₃)
  | app_fun (t₁ t₁' t₂ : Term) : Step t₁ t₁' →
    Step (App t₁ t₂) (App t₁' t₂)
  | app_arg (t₁ t₂ t₂' : Term) : isValue t₁ → Step t₂ t₂' →
    Step (App t₁ t₂) (App t₁ t₂')
  | app (t₁ t₂ : Term) (ty : Ty): (isValue t₂) →
    Step (App (Abs t₁ ty) t₂) (subsitute 0 t₂ t₁)

abbrev Ctx := ℕ → Option Ty

def Ctx.extend (T : Ty) (Γ : Ctx) : Ctx := fun n ↦
  match n with
  | 0 => T
  | n + 1 => Γ n

def Ctx.shrink (Γ : Ctx) : Ctx := fun n ↦ Γ (n + 1)

def empty : Ctx := fun _n ↦ none

inductive HasType : Ctx → Term → Ty → Prop where
| t_true (Γ : Ctx) : HasType Γ True Ty.Bool
| t_false (Γ : Ctx) : HasType Γ False Ty.Bool
| t_var (Γ : Ctx) (n : ℕ) (T : Ty) :
  Γ n = some T → HasType Γ (Var n) T
| t_abs (t: Term) (Γ : Ctx) (T₁ T₂ : Ty) :
  HasType (Γ.extend T₁) t T₂ → HasType Γ (Abs t T₁) (Ty.Fn T₁ T₂)
| t_app (t₁ t₂ : Term) (Γ : Ctx) (T₁ T₂ : Ty):
  HasType Γ t₁ (Ty.Fn T₂ T₁) → HasType Γ t₂ T₂ → HasType Γ (App t₁ t₂) T₁
| t_if (t₁ t₂ t₃ : Term) (Γ : Ctx) (T : Ty):
  HasType Γ t₁ Ty.Bool → HasType Γ t₂ T → HasType Γ t₃ T
    → HasType Γ (Ite t₁ t₂ t₃) T

open Ty

abbrev Bool := Ty.Bool

-- 9.3.1. -- Inversion lemmas
lemma ty_inv_true {Γ : Ctx} {ty : Ty} : HasType Γ True ty -> ty = Bool := by
  intro h
  match h with
  | HasType.t_true Γ => exact refl Bool

lemma ty_inv_false {Γ : Ctx} {ty : Ty} : HasType Γ False ty -> ty = Bool := by
  intro h
  match h with
  | HasType.t_false Γ => exact refl Bool

lemma ty_inv_var {n : ℕ} {Γ : Ctx} {ty : Ty} :
    HasType Γ (Var n) ty -> Γ n = Option.some ty := by
  intro h
  match h with
  | HasType.t_var Γ n ty th => exact th

-- Typing of a compound expression
lemma ty_inv_if {t₁ t₂ t₃ : Term} {ty : Ty} {Γ : Ctx} : HasType Γ (Ite t₁ t₂ t₃) ty → HasType Γ t₁ Bool ∧ HasType Γ t₂ ty ∧ HasType Γ t₃ ty := by
  intro h
  match h with
  | HasType.t_if t₁ t₂ t₃ Γ ty h₁ h₂ h₃ =>
    exact ⟨h₁, ⟨h₂, h₃⟩⟩

lemma ty_inv_app {t₁ t₂ : Term} {ty₁ : Ty} {Γ : Ctx} :
  HasType Γ (App t₁ t₂) ty₁ → ∃ ty₂ : Ty, HasType Γ t₁ (Fn ty₂ ty₁) ∧ HasType Γ t₂ ty₂ := by
  intro h
  match h with
  | HasType.t_app t₁ t₂ Γ ty₁ ty₂ h₁ h₂ => use ty₂

lemma ty_inv_abs {t : Term} {ty ty₁ : Ty} {Γ : Ctx}: HasType Γ (Abs t ty₁) ty -> ∃ ty₂ : Ty, ty = Fn ty₁ ty₂ ∧ HasType (Γ.extend ty₁) t ty₂ := by
  intro h
  match h with
  | HasType.t_abs t Γ ty₁ ty₂ h =>
    use ty₂

-- THEOREM 9.3.3.
theorem type_uniqueness {t : Term} (Γ : Ctx) (ty₁ ty₂ : Ty) :
  HasType Γ t ty₁ → HasType Γ t ty₂ → ty₁ = ty₂ := by
  intro th₁ th₂
  induction t generalizing Γ ty₁ ty₂ with
  | True =>
    rw [ty_inv_true th₁, ty_inv_true th₂]
  | False =>
    rw [ty_inv_false th₁, ty_inv_false th₂]
  | Var n =>
    have has_type₁ := ty_inv_var th₁
    have := ty_inv_var th₂
    rw [this] at has_type₁
    cases has_type₁
    exact refl ty₁
  | Ite t₁ t₂ t₃ _ h _ =>
    exact h Γ ty₁ ty₂ (ty_inv_if th₁).2.1 (ty_inv_if th₂).2.1
  | App t₁ t₂ h₁ h₂ =>
    have ⟨ty₁', appth₁⟩ := ty_inv_app th₁
    have ⟨ty₂', appth₂⟩ := ty_inv_app th₂
    have := h₁ Γ (Fn ty₁' ty₁) (Fn ty₂' ty₂) appth₁.1 appth₂.1
    cases this
    exact refl ty₁
  | Abs t ty h =>
    have ⟨ty₁', th₁'⟩ := ty_inv_abs th₁
    have ⟨ty₂', th₂'⟩ := ty_inv_abs th₂
    have := h (Ctx.extend ty Γ) ty₁' ty₂' th₁'.2 th₂'.2
    have k := th₁'.1
    rw [this, ← th₂'.1] at k
    exact k

-- LEMMA 9.3.4. -- canonical forms
/- Note that while isVal is not used explicitly,
  it is instrumental for the lemma, as the runtime
  excludes some of the other cases based on the fact
  that they would fail isValue -/

lemma canonical_bool {t : Term} {Γ : Ctx} :
    isValue t → HasType Γ t Bool → t = True ∨ t = False := by
  intro _ isBool
  match t with | True | False => simp

-- LEMMA 9.3.4. -- 2
lemma canonical_map {t : Term} {Γ : Ctx} {ty₁ ty₂ : Ty}:
  isValue t → HasType Γ t (Fn ty₁ ty₂) → ∃ t₁ : Term, t = (Abs t₁ ty₁) := by
    intro _ isFn
    match t with
    | Abs t₁ k =>
      use t₁
      have ⟨_, ⟨h, _⟩⟩:= ty_inv_abs isFn
      cases h
      exact refl (Abs t₁ ty₁)

-- THEOREM 9.3.5.
theorem progress {t : Term} {ty : Ty} :
    HasType empty t ty -> isValue t ∨ ∃ t' : Term, Step t t' := by
  intro th
  induction t generalizing ty with
  | True | False => simp [isValue]
  | Var n =>
    have := ty_inv_var th
    simp [empty] at this
  | Ite t₁ t₂ t₃ ih₁ _ _ =>
    -- we prove that we can make progress
    apply Or.inr
    -- t₁ is a subterm, so it is well-typed
    have t₁_typed := (ty_inv_if th).1
    -- therefore either a value or can be stepped
    cases (ih₁ t₁_typed) with
    | inl h' =>
      -- if a value, we use that it is a bool,
      -- so either true or false
      cases (canonical_bool h' t₁_typed) with
      | inl t =>
        rw [t]
        use t₂
        exact Step.ite_true t₂ t₃
      | inr f =>
        rw [f]
        use t₃
        exact Step.ite_false t₂ t₃
    | inr h' =>
      -- if can be stepped, wrap it in ite_step
      let ⟨t₁', step⟩ := h'
      use Term.Ite t₁' t₂ t₃
      exact Step.ite_step t₁ t₁' t₂ t₃ step
  | App t₁ t₂ ih₁ ih₂ =>
    -- for applications, we can always
    -- make a step
    apply Or.inr
    have ⟨ty₂, ⟨t₁_typ, t₂_typ⟩⟩:= ty_inv_app th
    cases (ih₁ t₁_typ) with
    | inl v₁ =>
      -- if the function is a value, we can either
      -- substitute, or simply the argument
      have ⟨t₃, fnh⟩ := canonical_map v₁ t₁_typ
      cases (ih₂ t₂_typ) with
      | inl v₂ =>
        have := Step.app t₃ t₂ ty₂ v₂
        rw [fnh]
        use (subsitute 0 t₂ t₃)
      | inr h₂ =>
        have ⟨t₄, step⟩ := h₂
        have := Step.app_arg t₁ t₂ t₄ v₁ step
        use (t₁.App t₄)
    | inr h₁ =>
      -- if the function is not yet a value,
      -- we just simplify it
      have ⟨t₁', step⟩ := h₁
      have := Step.app_fun t₁ t₁' t₂ step
      use (t₁'.App t₂)
  | Abs t₁ ty₁ =>
    apply Or.inl
    simp [isValue]

/- Basic lemma expressing that a shift will
  just move a type up by 1 index.
-/
lemma context_extension {Γ : Ctx} {ty ty' : Ty} {n : ℕ}:
    (Γ n = some ty) -> ((Γ.extend ty') (n+1)) = some ty := by
  intro h
  simp [Ctx.extend]
  assumption

/- The fact that we are using de Brujin indices means that some
    structural changes are needed when proving the substitution
    lemma.

  We want to prove weakening: inserting a new type at position 0
    in the context preserves typing, provided we shift all free
    variables up by 1. Every case in the induction on the typing
    derivation is straightforward except Abs. When the term is
    λ:T₁. t', the inductive hypothesis (applied inside the binder)
    gives
    `ty', T₁, Γ ⊢ ↑₀ t' : T₂`
    but what we actually need is
    `T₁, ty', Γ ⊢ ↑₁ t' : T₂`   — ty' is behind T₁, cutoff has advanced to 1
    We therefore need to build the machinery to swap the types and
    advance the cutoff. What makes it complicated is that when proving
    `swap_typing` by induction, its own Abs case gets caught in the
    same situation one level deeper:
    `T, ty', T₁, Γ ⊢ ↑ₖ t' : T₂` -- as induction hypothesis
    `T, T₁, ty', Γ ⊢ ↑ₖ₊₁ t' : T₂` -- as goal
    Thus, to "work under extensions" at any depth, we introduce swap
    and prove `swap_typing` with a general cutoff parameter k, rather
    than fixing it to a specific value.
-/

/- The swap operation, that will encapsulate all
    the permutation behaviour that we will need.
-/
def Ctx.swap (Γ: Ctx) (k : ℕ) : Ctx := fun n ↦
  if n = k then Γ (k + 1)
  else if n = k+1 then Γ k
  else Γ n

/- Algebraic identity about interchanging the
    extension and swap operations.
-/
def Ctx.swap_comm_ext {Γ: Ctx} {k : ℕ}:
  HasType ((Γ.extend ty).swap (k+1)) t ty'
  ↔ HasType ((Γ.swap k).extend ty) t ty' := by
  suffices h : (Γ.extend ty).swap (k+1) = (Γ.swap k).extend ty by rw [h]
  funext n
  rcases n with _ | m
  · simp [Ctx.swap, Ctx.extend]
  · simp only [Ctx.swap, Ctx.extend]
    split_ifs <;> first | rfl | (exfalso; omega)

/- Another trivial lemma about the fact
  that two can be interchanged using the swap
  operation.
-/
lemma Ctx.swap_ext {Γ: Ctx}:
    (((Γ.extend ty).extend ty').swap 0) = ((Γ.extend ty').extend ty) := by
  funext n
  simp [Ctx.swap, Ctx.extend]
  cases n with
  | zero => simp
  | succ n =>
      cases n <;> simp

/- The key lemma for weakening.
    If ↑ₖ t is well-typed in Γ, then ↑ₖ₊₁ t is well-typed in Γ.swap k.
    This repairs both problems in weakening's Abs case simultaneously: (1)
    advances the shift cutoff from k to k+1 and (2) transposes the newly
    inserted type past the binder's type.

  The Abs case of this lemma's own induction is the only non-trivial one.
    It uses swap_comm_ext to handle the next level of binder nesting.
-/
lemma swap_typing {Γ : Ctx} {t : Term} :
    HasType Γ (shift k 1 t) ty'' ->
    HasType (Γ.swap k) (shift (k+1) 1 t) ty'' := by
  intro typing
  induction t generalizing Γ ty'' k with
  | True =>
    have th := ty_inv_true typing
    simp [th, shift]
    exact HasType.t_true (Γ.swap k)
  | False =>
    have th := ty_inv_false typing
    simp [th, shift]
    exact HasType.t_false (Γ.swap k)
  | Var n =>
    simp [shift]
    simp [shift] at typing
    by_cases h: k ≤ n
    · simp [h] at typing
      have th := ty_inv_var typing
      by_cases h': k < n
      · simp [h']
        apply HasType.t_var
        simp only [Ctx.swap, if_neg (show n + 1 ≠ k from by omega),
                   if_neg (show n + 1 ≠ k + 1 from by omega)]
        exact th
      · push Not at h'
        have : n = k := Nat.le_antisymm h' h
        subst this
        simp
        apply HasType.t_var
        simp [Ctx.swap]
        exact th
    · push Not at h
      simp [show ¬(n ≥ k) from by omega] at typing
      have th := ty_inv_var typing
      have := not_lt_iff_eq_or_lt.mpr (Or.inr h)
      simp [this]
      apply HasType.t_var
      simp [Ctx.swap, show n ≠ k from by omega, show n ≠ k + 1 from by omega]
      exact th
  | App t₁ t₂ ih₁ ih₂ =>
    simp [shift]
    have ⟨ty₂, ⟨th₁, th₂⟩⟩ := ty_inv_app typing
    exact HasType.t_app _ _ _ _ _ (ih₁ th₁) (ih₂ th₂)
  | Abs t₁ t₂ ih =>
    simp [shift]
    have ⟨ty₂, ⟨ty_eq, fn_typ⟩⟩ := ty_inv_abs typing
    have := ih fn_typ
    rw [Ctx.swap_comm_ext] at this
    rw [ty_eq]
    exact HasType.t_abs _ _ _ _ this
  | Ite t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    have ⟨th₁, ⟨th₂, th₃⟩⟩ := ty_inv_if typing
    exact HasType.t_if _ _ _ _ _ (ih₁ th₁) (ih₂ th₂) (ih₃ th₃)

/- LEMMA
    With the tools developed, this proof
    becomes quite friendly. -/
lemma weakening {Γ : Ctx} {t : Term} {ty ty': Ty} {typing: HasType Γ t ty}
  : (HasType (Γ.extend ty') (shift 0 1 t) ty) := by
  induction typing with
  | t_true Γ =>
    simp [shift]
    exact HasType.t_true (Ctx.extend ty' Γ)
  | t_false Γ =>
    simp [shift]
    exact HasType.t_false (Ctx.extend ty' Γ)
  | t_if t' t'' t''' Γ T th' th'' th''' ih' ih'' ih''' =>
    exact HasType.t_if _ _ _ _ _ ih' ih'' ih'''
  | t_var Γ n ty₁ h =>
    simp [shift]
    apply HasType.t_var
    simp [Ctx.extend]
    assumption
  | t_app t₁ t₂ Γ ty₁ ty₂ th₁ th₂ ih₁ ih₂ =>
    simp [shift]
    exact HasType.t_app _ _ _ ty₁ ty₂ ih₁ ih₂
  | t_abs t' Γ T₁ T₂ th ih =>
    simp [shift]
    apply HasType.t_abs
    have := swap_typing ih
    rw [Ctx.swap_ext] at this
    exact this

/- The final ingredient to prove safety is to prove
    the that substitutions preserve types. This again
    requires some extra machinery, since when substituting
    for a variable n, all variables > n will be shifted
    down by one.

    This element of context management is captured in
    the drop function in the context, for which we again
    need to develop some auxiliary lemmas. -/

def Ctx.drop (Γ : Ctx) (n : ℕ) : Ctx := fun k => if k < n then Γ k else Γ (k + 1)

lemma Ctx.drop_zero_extend (T : Ty) (Γ : Ctx) : (Γ.extend T).drop 0 = Γ := by
  funext k; simp [Ctx.drop, Ctx.extend]

lemma Ctx.drop_succ_extend {n : ℕ} {T : Ty} {Γ : Ctx} :
    (Γ.extend T).drop (n + 1) = (Γ.drop n).extend T := by
  funext k; rcases k with _ | m
  · simp [Ctx.drop, Ctx.extend]
  · simp only [Ctx.drop, Ctx.extend]
    split_ifs <;> first | rfl | (exfalso; omega)

/- Substitution preservation.
    Rather than proving this using the usual
    `insert_at` type function, we use the drop
    function on contexts, to keep everything as
    close to the operational semantics of the
    lambda calculus as possible.
-/
lemma substitution_preservation (n : ℕ) {Γ : Ctx} {t t' : Term} {ty ty' : Ty} :
    HasType (Γ.drop n) t' ty
    → Γ n = some ty
    → HasType Γ t ty'
    → HasType (Γ.drop n) (subsitute n t' t) ty' := by
  intro h_s hΓn bodytyp
  induction t generalizing n Γ ty ty' t' with
  | True  => simp [subsitute]; rw [ty_inv_true bodytyp];  exact HasType.t_true _
  | False => simp [subsitute]; rw [ty_inv_false bodytyp]; exact HasType.t_false _
  | Var m =>
    have hm := ty_inv_var bodytyp
    by_cases heq : m = n
    · subst heq; simp only [subsitute, ite_true]
      have hST : ty' = ty := Option.some.inj (hm.symm.trans hΓn)
      subst hST; exact h_s
    · by_cases hgt : m > n
      · simp only [subsitute, heq, ↓reduceIte, hgt]
        apply HasType.t_var
        have : (Γ.drop n) (m - 1) = Γ m := by
          simp only [Ctx.drop, if_neg (show ¬(m - 1 < n) by omega)]
          congr 1; exact Nat.sub_add_cancel (by omega)
        rw [this]; exact hm
      · have hlt : m < n := by omega
        simp only [subsitute, heq, ↓reduceIte, show ¬m > n from by omega]
        apply HasType.t_var
        simp only [Ctx.drop, if_pos hlt]; exact hm
  | Abs body' T' ih =>
    simp only [subsitute]
    have ⟨T'', ⟨hTeq, hbody⟩⟩ := ty_inv_abs bodytyp
    rw [hTeq]; apply HasType.t_abs
    rw [← Ctx.drop_succ_extend]
    have := weakening (typing := h_s) (ty' := T')
    rw [← Ctx.drop_succ_extend] at this
    have Γext : (Ctx.extend T' Γ) (n + 1) = some ty := context_extension hΓn
    exact ih (n+1) this Γext hbody
  | App body' body'' ih' ih'' =>
    simp only [subsitute]
    have ⟨T'', ⟨hfn, harg⟩⟩ := ty_inv_app bodytyp
    have := ih' n h_s hΓn hfn
    exact HasType.t_app _ _ _ _ _
      (ih' n h_s hΓn hfn)
      (ih'' n h_s hΓn harg)
  | Ite b₁ b₂ b₃ ih₁ ih₂ ih₃ =>
    simp only [subsitute]
    have ⟨hb₁, hb₂, hb₃⟩ := ty_inv_if bodytyp
    exact HasType.t_if _ _ _ _ _
      (ih₁ n h_s hΓn hb₁)
      (ih₂ n h_s hΓn hb₂)
      (ih₃ n h_s hΓn hb₃)

/- Finally, we prove safety. This again is
  quite straight forward given the substitution
  lemma. -/
theorem safety {Γ : Ctx} {t t' : Term} {ty : Ty}
    {step : Step t t'} {typing : HasType Γ t ty} :
    HasType Γ t' ty := by
  induction step generalizing ty with
  | ite_step t₁ t₁' t₂ t₃ step' ih =>
    have ⟨ty₁, ⟨ty₂, ty₃⟩⟩ := ty_inv_if typing
    have := ih (typing := ty₁)
    exact HasType.t_if _ _ _ _ _ this ty₂ ty₃
  | app_arg t₁ t₂ t₂' val₁ step ih =>
    have ⟨ty₂, ⟨typ₁, typ₂⟩⟩  := ty_inv_app typing
    have := ih (typing := typ₂)
    exact HasType.t_app _ _ _ _ _ typ₁ this
  | app_fun t₁ t₁' t₂ step ih =>
    have ⟨ty₂, ⟨typ₁, typ₂⟩⟩ := ty_inv_app typing
    have := ih (typing := typ₁)
    exact HasType.t_app _ _ _ _ _ this typ₂
  | app t₁ t₂ ty₁ val =>
    have ⟨ty₂, ⟨typ₁, typ₂⟩⟩ := ty_inv_app typing
    have ⟨ty₃, ⟨a₁, a₂⟩⟩ := ty_inv_abs typ₁
    simp only [Ty.Fn.injEq] at a₁
    have ⟨rfl, rfl⟩ := a₁
    rw [← Ctx.drop_zero_extend ty₂ Γ] at typ₂
    have result := substitution_preservation 0 typ₂ (by simp [Ctx.extend]) a₂
    rwa [Ctx.drop_zero_extend] at result
  | ite_true t₁ t₂ =>
    have := ty_inv_if typing
    exact this.2.1
  | ite_false t₁ t₂ =>
    have := ty_inv_if typing
    exact this.2.2

end Term
