/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton
-/
import Mathlib.Combinatorics.Quiver

namespace Category

universes v u

/-!
# Categories
Defines a category, as a type class parametrised by the type of objects.
## Notations
Introduces notations
* `X ⟶ Y` for the morphism spaces,
* `f ≫ g` for composition in the 'arrows' convention.

Users may like to add `f ⊚ g` for composition in the standard convention, using
```lean
local notation f ` ⊚ `:80 g:80 := category.comp g f    -- type as \oo
```
-/

-- /--
-- The typeclass `category C` describes morphisms associated to objects of type `C : Type u`.
-- The universe levels of the objects and morphisms are independent, and will often need to be
-- specified explicitly, as `category.{v} C`.
-- Typically any concrete example will either be a `small_category`, where `v = u`,
-- which can be introduced as
-- ```
-- universes u
-- variables {C : Type u} [small_category C]
-- ```
-- or a `large_category`, where `u = v+1`, which can be introduced as
-- ```
-- universes u
-- variables {C : Type (u+1)} [large_category C]
-- ```
-- In order for the library to handle these cases uniformly,
-- we generally work with the unconstrained `category.{v u}`,
-- for which objects live in `Type u` and morphisms live in `Type v`.
-- Because the universe parameter `u` for the objects can be inferred from `C`
-- when we write `category C`, while the universe parameter `v` for the morphisms
-- can not be automatically inferred, through the category theory library
-- we introduce universe parameters with morphism levels listed first,
-- as in
-- ```
-- universes v u
-- ```
-- or
-- ```
-- universes v₁ v₂ u₁ u₂
-- ```
-- when multiple independent universes are needed.
-- This has the effect that we can simply write `category.{v} C`
-- (that is, only specifying a single parameter) while `u` will be inferred.
-- Often, however, it's not even necessary to include the `.{v}`.
-- (Although it was in earlier versions of Lean.)
-- If it is omitted a "free" universe will be used.
-- -/
-- -- library_note "category_theory universes"

/-- A preliminary structure on the way to defining a category,
containing the data, but none of the axioms. -/
class CategoryStruct (obj : Type u)
 extends Quiver.{v+1} obj : Type (max u (v+2)) :=
(id       : ∀ X : obj, X ⟶ X)
(comp     : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z))

notation "𝟙" => CategoryStruct.id -- type as \b1
infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

/--
The typeclass `category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `category.{v} C`. (See also `large_category` and `small_category`.)
See https://stacks.math.columbia.edu/tag/0014.
-/
class Category (obj : Type u) extends CategoryStruct.{v} obj : Type (max u (v+2)) :=
(id_comp' : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f)
(comp_id' : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f)
(assoc'   : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
  (f ≫ g) ≫ h = f ≫ (g ≫ h))

variable (obj : Type u)

@[simp]
theorem id_comp [c : Category obj] {X Y : obj} (f : X ⟶ Y) : 𝟙 X ≫ f = f := c.id_comp' f

@[simp]
theorem comp_id [c : Category obj] {X Y : obj} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := c.comp_id' f

@[simp]
theorem comp_assoc [c : Category obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
  (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  c.assoc' f g h


/--
A `LargeCategory` has objects in one universe level higher than the universe level of
the morphisms. It is useful for examples such as the category of types, or the category
of groups, etc.
-/
abbrev LargeCategory (C : Type (u+1)) : Type _ := Category.{u} C

/--
A `SmallCategory` has objects and morphisms in the same universe level.
-/
abbrev SmallCategory (C : Type u) : Type _ := Category.{u} C

section
variable {C : Type u} [Category.{v} C] {X Y Z : C}


/-- postcompose an equation between morphisms by another morphism -/
lemma eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : f ≫ h = g ≫ h :=
by rw [w]
/-- precompose an equation between morphisms by another morphism -/
lemma whisker_eq (f : X ⟶ Y) {g h : Y ⟶ Z} (w : g = h) : f ≫ g = f ≫ h :=
by rw [w]

infixr:80 " =≫ " => eq_whisker
infixr:80 " ≫= " => whisker_eq



lemma eq_of_comp_left_eq {f g : X ⟶ Y} (w : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) : f = g :=
by { convert w (𝟙 Y), tidy }
lemma eq_of_comp_right_eq {f g : Y ⟶ Z} (w : ∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) : f = g :=
by { convert w (𝟙 Y), tidy }

lemma eq_of_comp_left_eq' (f g : X ⟶ Y)
  (w : (λ {Z : C} (h : Y ⟶ Z), f ≫ h) = (λ {Z : C} (h : Y ⟶ Z), g ≫ h)) : f = g :=
eq_of_comp_left_eq (λ Z h, by convert congr_fun (congr_fun w Z) h)
lemma eq_of_comp_right_eq' (f g : Y ⟶ Z)
  (w : (λ {X : C} (h : X ⟶ Y), h ≫ f) = (λ {X : C} (h : X ⟶ Y), h ≫ g)) : f = g :=
eq_of_comp_right_eq (λ X h, by convert congr_fun (congr_fun w X) h)

lemma id_of_comp_left_id (f : X ⟶ X) (w : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 X :=
by { convert w (𝟙 X), tidy }
lemma id_of_comp_right_id (f : X ⟶ X) (w : ∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) : f = 𝟙 X :=
by { convert w (𝟙 X), tidy }

lemma comp_dite {P : Prop} [decidable P]
  {X Y Z : C} (f : X ⟶ Y) (g : P → (Y ⟶ Z)) (g' : ¬P → (Y ⟶ Z)) :
  (f ≫ if h : P then g h else g' h) = (if h : P then f ≫ g h else f ≫ g' h) :=
by { split_ifs; refl }

lemma dite_comp {P : Prop} [decidable P]
  {X Y Z : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (g : Y ⟶ Z) :
  (if h : P then f h else f' h) ≫ g = (if h : P then f h ≫ g else f' h ≫ g) :=
by { split_ifs; refl }

/--
A morphism `f` is an epimorphism if it can be "cancelled" when precomposed:
`f ≫ g = f ≫ h` implies `g = h`.
See https://stacks.math.columbia.edu/tag/003B.
-/
class epi (f : X ⟶ Y) : Prop :=
(left_cancellation : Π {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h)

/--
A morphism `f` is a monomorphism if it can be "cancelled" when postcomposed:
`g ≫ f = h ≫ f` implies `g = h`.
See https://stacks.math.columbia.edu/tag/003B.
-/
class mono (f : X ⟶ Y) : Prop :=
(right_cancellation : Π {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h)

instance (X : C) : epi (𝟙 X) :=
⟨λ Z g h w, by simpa using w⟩
instance (X : C) : mono (𝟙 X) :=
⟨λ Z g h w, by simpa using w⟩

lemma cancel_epi (f : X ⟶ Y) [epi f]  {g h : Y ⟶ Z} : (f ≫ g = f ≫ h) ↔ g = h :=
⟨ λ p, epi.left_cancellation g h p, begin intro a, subst a end ⟩
lemma cancel_mono (f : X ⟶ Y) [mono f] {g h : Z ⟶ X} : (g ≫ f = h ≫ f) ↔ g = h :=
⟨ λ p, mono.right_cancellation g h p, begin intro a, subst a end ⟩

lemma cancel_epi_id (f : X ⟶ Y) [epi f] {h : Y ⟶ Y} : (f ≫ h = f) ↔ h = 𝟙 Y :=
by { convert cancel_epi f, simp, }
lemma cancel_mono_id (f : X ⟶ Y) [mono f] {g : X ⟶ X} : (g ≫ f = f) ↔ g = 𝟙 X :=
by { convert cancel_mono f, simp, }

lemma epi_comp {X Y Z : C} (f : X ⟶ Y) [epi f] (g : Y ⟶ Z) [epi g] : epi (f ≫ g) :=
begin
  split, intros Z a b w,
  apply (cancel_epi g).1,
  apply (cancel_epi f).1,
  simpa using w,
end
lemma mono_comp {X Y Z : C} (f : X ⟶ Y) [mono f] (g : Y ⟶ Z) [mono g] : mono (f ≫ g) :=
begin
  split, intros Z a b w,
  apply (cancel_mono f).1,
  apply (cancel_mono g).1,
  simpa using w,
end

lemma mono_of_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [mono (f ≫ g)] : mono f :=
begin
  split, intros Z a b w,
  replace w := congr_arg (λ k, k ≫ g) w,
  dsimp at w,
  rw [category.assoc, category.assoc] at w,
  exact (cancel_mono _).1 w,
end

lemma mono_of_mono_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [mono h] (w : f ≫ g = h) :
  mono f :=
by { substI h, exact mono_of_mono f g, }

lemma epi_of_epi {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [epi (f ≫ g)] : epi g :=
begin
  split, intros Z a b w,
  replace w := congr_arg (λ k, f ≫ k) w,
  dsimp at w,
  rw [←category.assoc, ←category.assoc] at w,
  exact (cancel_epi _).1 w,
end

lemma epi_of_epi_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [epi h] (w : f ≫ g = h) :
  epi g :=
by substI h; exact epi_of_epi f g
end

section
variable (C : Type u)
variable [category.{v} C]

universe u'

instance ulift_category : category.{v} (ulift.{u'} C) :=
{ hom  := λ X Y, (X.down ⟶ Y.down),
  id   := λ X, 𝟙 X.down,
  comp := λ _ _ _ f g, f ≫ g }

-- We verify that this previous instance can lift small categories to large categories.
example (D : Type u) [small_category D] : large_category (ulift.{u+1} D) := by apply_instance
end

end category_theory

open category_theory

/-!
We now put a category instance on any preorder.
Because we do not allow the morphisms of a category to live in `Prop`,
unfortunately we need to use `plift` and `ulift` when defining the morphisms.
As convenience functions, we provide `hom_of_le` and `le_of_hom` to wrap and unwrap inequalities.
We also provide aliases `has_le.le.hom` and `quiver.hom.le` to use with dot notation.
-/
namespace preorder

variables (α : Type u)

/--
The category structure coming from a preorder. There is a morphism `X ⟶ Y` if and only if `X ≤ Y`.
Because we don't allow morphisms to live in `Prop`,
we have to define `X ⟶ Y` as `ulift (plift (X ≤ Y))`.
See `category_theory.hom_of_le` and `category_theory.le_of_hom`.
See https://stacks.math.columbia.edu/tag/00D3.
-/
@[priority 100] -- see Note [lower instance priority]
instance small_category [preorder α] : small_category α :=
{ hom  := λ U V, ulift (plift (U ≤ V)),
  id   := λ X, ⟨ ⟨ le_refl X ⟩ ⟩,
  comp := λ X Y Z f g, ⟨ ⟨ le_trans _ _ _ f.down.down g.down.down ⟩ ⟩ }

end preorder

namespace category_theory

variables {α : Type u} [preorder α]

/--
Express an inequality as a morphism in the corresponding preorder category.
-/
def hom_of_le {U V : α} (h : U ≤ V) : U ⟶ V := ulift.up (plift.up h)

alias hom_of_le ← has_le.le.hom

@[simp] lemma hom_of_le_refl {U : α} : (le_refl U).hom = 𝟙 U := rfl
@[simp] lemma hom_of_le_comp {U V W : α} (h : U ≤ V) (k : V ≤ W) :
  h.hom ≫ k.hom = (h.trans k).hom := rfl

/--
Extract the underlying inequality from a morphism in a preorder category.
-/
lemma le_of_hom {U V : α} (h : U ⟶ V) : U ≤ V := h.down.down

alias le_of_hom ← quiver.hom.le

@[simp] lemma le_of_hom_hom_of_le {a b : α} (h : a ≤ b) : h.hom.le = h := rfl
@[simp] lemma hom_of_le_le_of_hom {a b : α} (h : a ⟶ b) : h.le.hom = h :=
by { cases h, cases h, refl, }

end category_theory
