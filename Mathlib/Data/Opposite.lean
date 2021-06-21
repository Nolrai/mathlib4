/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton, Simon Hudon, Kenny Lau
-/
import Mathlib.Data.Equiv.Basic

/-!
# opposites
In this file we define a type synonym `opposite α := α`, denoted by `αᵒᵖ` and two synonyms for the
identity map, `op : α → αᵒᵖ` and `unop : αᵒᵖ → α`. The type tag `αᵒᵖ` is used with two different
meanings:
- if `α` is a category, then `αᵒᵖ` is the opposite category, with all arrows reversed;
- if `α` is a monoid (group, etc), then `αᵒᵖ` is the opposite monoid (group, etc) with
  `op (x * y) = op x * op y`.
-/

universes v u -- morphism levels before object levels. See note [categoryTheory universes].

variable (α : Sort u)

/-- The type of objects of the opposite of `α`; used to define the opposite category or group.
  In order to avoid confusion between `α` and its opposite type, we
  set up the type of objects `opposite α` using the following pattern,
  which will be repeated later for the morphisms.
  1. Define `opposite α := α`.
  2. Define the isomorphisms `op : α → opposite α`, `unop : opposite α → α`.
  3. Make the definition `opposite` irreducible.
  This has the following consequences.
  * `opposite α` and `α` are distinct types in the elaborator, so you
    must use `op` and `unop` explicitly to convert between them.
  * Both `unop (op X) = X` and `op (unop X) = X` are definitional
    equalities. Notably, every object of the opposite category is
    definitionally of the form `op X`, which greatly simplifies the
    definition of the structure of the opposite category, for example.
  (If Lean supported definitional eta equality for records, we could
  achieve the same goals using a structure with one field.)
-/
def opposite : Sort u := α

-- Use a high right binding power (like that of postfix ⁻¹) so that, for example,
-- `presheaf Cᵒᵖ` parses as `presheaf (Cᵒᵖ)` and not `(presheaf C)ᵒᵖ`.
postfix "ᵒᵖ" => opposite

namespace opposite

variable {α}
/-- The canonical map `α → αᵒᵖ`. -/
def op : α → αᵒᵖ := id
/-- The canonical map `αᵒᵖ → α`. -/
def unop : αᵒᵖ → α := id

lemma opInjective : Function.injective (op : α → αᵒᵖ) := id
lemma unopInjective : Function.injective (unop : αᵒᵖ → α) := id

@[simp] lemma opInjIff (x y : α) : op x = op y ↔ x = y := ⟨id, id⟩
@[simp] lemma unopInjIff (x y : αᵒᵖ) : unop x = unop y ↔ x = y := ⟨id, id⟩

@[simp] lemma opUnop (x : αᵒᵖ) : op (unop x) = x := rfl
@[simp] lemma unopOp (x : α) : unop (op x) = x := rfl

attribute [irreducible] opposite

/-- The type-level equivalence between a type and its opposite. -/
def equivToOpposite : α ≃ αᵒᵖ :=
{ to_fun := op,
  inv_fun := unop,
  left_inv := unopOp,
  right_inv := opUnop }

@[simp]
lemma equivTooppositeApply (a : α) : equivToOpposite a = op a := rfl
@[simp]
lemma equivTooppositeSymmApply (a : αᵒᵖ) : equivToOpposite.symm a = unop a := rfl

lemma opEqIffEqUnop {x : α} {y} : op x = y ↔ x = unop y :=
  ⟨(λ h => by rw [← h]; rfl),
   λ h => by rw [h]; rfl⟩

lemma unopEqIffEqop {x} {y : α} : unop x = y ↔ x = op y := opEqIffEqUnop.symm

instance [Inhabited α] : Inhabited αᵒᵖ := ⟨op Inhabited.default⟩

@[simp]
def opInduction {F : ∀ (X : αᵒᵖ), Sort v} (h : ∀ X, F (op X)) : ∀ X, F X :=
λ X => h (unop X)

end opposite
