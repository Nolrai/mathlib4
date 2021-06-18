/-
COpyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton, Simon Hudon, Kenny Lau
-/
import Mathlib.Data.Equiv.Basic

/-!
# Opposites
In this file we define a type synonym `Opposite α := α`, denoted by `αᵒᵖ` and two synonyms for the
identity map, `Op : α → αᵒᵖ` and `Unop : αᵒᵖ → α`. The type tag `αᵒᵖ` is used with two different
meanings:
- if `α` is a category, then `αᵒᵖ` is the Opposite category, with all arrows reversed;
- if `α` is a monoid (group, etc), then `αᵒᵖ` is the Opposite monoid (group, etc) with
  `Op (x * y) = Op x * Op y`.
-/

universes v u -- morphism levels before object levels. See note [categoryTheory universes].

variable (α : Sort u)

/-- The type of objects of the Opposite of `α`; used to define the Opposite category or group.
  In order to avoid confusion between `α` and its Opposite type, we
  set up the type of objects `Opposite α` using the following pattern,
  which will be repeated later for the morphisms.
  1. Define `Opposite α := α`.
  2. Define the isomorphisms `Op : α → Opposite α`, `Unop : Opposite α → α`.
  3. Make the definition `Opposite` irreducible.
  This has the following consequences.
  * `Opposite α` and `α` are distinct types in the elaborator, so you
    must use `Op` and `Unop` explicitly to convert between them.
  * Both `Unop (Op X) = X` and `Op (Unop X) = X` are definitional
    equalities. Notably, every object of the Opposite category is
    definitionally of the form `Op X`, which greatly simplifies the
    definition of the structure of the Opposite category, for example.
  (If Lean supported definitional eta equality for records, we could
  achieve the same goals using a structure with one field.)
-/
def Opposite : Sort u := α

-- Use a high right binding power (like that of postfix ⁻¹) so that, for example,
-- `presheaf Cᵒᵖ` parses as `presheaf (Cᵒᵖ)` and not `(presheaf C)ᵒᵖ`.
postfix:100 "ᵒᵖ" => Opposite

namespace Opposite

variable {α}
/-- The canonical map `α → αᵒᵖ`. -/
def Op : α → αᵒᵖ := id
/-- The canonical map `αᵒᵖ → α`. -/
def Unop : αᵒᵖ → α := id

lemma OpInjective : Function.injective (Op : α → αᵒᵖ) := id
lemma UnopInjective : Function.injective (Unop : αᵒᵖ → α) := id

@[simp] lemma OpInjIff (x y : α) : Op x = Op y ↔ x = y := ⟨id, id⟩
@[simp] lemma UnopInjIff (x y : αᵒᵖ) : Unop x = Unop y ↔ x = y := ⟨id, id⟩

@[simp] lemma OpUnop (x : αᵒᵖ) : Op (Unop x) = x := rfl
@[simp] lemma UnopOp (x : α) : Unop (Op x) = x := rfl

attribute [irreducible] Opposite

/-- The type-level equivalence between a type and its Opposite. -/
def equivToOpposite : α ≃ αᵒᵖ :=
{ to_fun := Op,
  inv_fun := Unop,
  left_inv := UnopOp,
  right_inv := OpUnop }

@[simp]
lemma equivToOppositeApply (a : α) : equivToOpposite a = Op a := rfl
@[simp]
lemma equivToOppositeSymmApply (a : αᵒᵖ) : equivToOpposite.symm a = Unop a := rfl

lemma OpEqIffEqUnop {x : α} {y} : Op x = y ↔ x = Unop y :=
  ⟨(λ h => by rw [← h]; rfl),
   λ h => by rw [h]; rfl⟩

lemma UnopEqIffEqOp {x} {y : α} : Unop x = y ↔ x = Op y := OpEqIffEqUnop.symm

instance [Inhabited α] : Inhabited αᵒᵖ := ⟨Op Inhabited.default⟩

@[simp]
def OpInduction {F : ∀ (X : αᵒᵖ), Sort v} (h : ∀ X, F (Op X)) : ∀ X, F X :=
λ X => h (Unop X)

end Opposite
