/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.Data.Equiv.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Opposite

/-!
# Quivers
This module defines quivers. A quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a very permissive notion of directed graph.
## Implementation notes
Currently `quiver` is defined with `arrow : V → V → Sort v`.
This is different from the category theory setup,
where we insist that morphisms live in some `Type`.
There's some balance here: it's nice to allow `Prop` to ensure there are no multiple arrows,
but it is also results in error-prone universe signatures when constraints require a `Type`.
-/

open Opposite

-- We use the same universe order as in category theory.
-- See note [category_theory universes]
universes v v₁ v₂ u u₁ u₂

/--
A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`.
For graphs with no repeated edges, one can use `quiver.{0} V`, which ensures
`a ⟶ b : Prop`. For multigraphs, one can use `quiver.{v+1} V`, which ensures
`a ⟶ b : Type v`.
Because `category` will later extend this class, we call the field `hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
class quiver (V : Type u) :=
(hom : V → V → Sort v)

infixr:10 " ⟶ " => quiver.hom -- type as \h

/--
A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `prefunctor`.
-/
structure Prefunctor (V : Type u₁) [quiver.{v₁} V] (W : Type u₂) [quiver.{v₂} W] :=
(obj : V → W)
(map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y))

namespace Prefunctor

-- This is a bit hacky but I can't figure out how to specify the general "id" instead of
-- the Prefunctor one if we are _in_ the Prefunctor namespace.
local notation "id'" => id

/--
The identity morphism between quivers.
-/
@[simp]
def id (V : Type u) [quiver V] : Prefunctor V V :=
{ obj := id',
  map := λ f => f, }

instance (V : Type u) [quiver V] : Inhabited (Prefunctor V V) := ⟨id V⟩

/--
Composition of morphisms between quivers.
-/
@[simp]
def comp {U : Type u} [quiver U] {V : Type v} [quiver V] {W : Type w} [quiver W]
  (F : Prefunctor U V) (G : Prefunctor V W) : Prefunctor U W :=
{ obj := G.obj ∘ F.obj,
  map := λ f => G.map (F.map f), }

end Prefunctor

