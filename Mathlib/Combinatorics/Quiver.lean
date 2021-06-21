/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.Data.Equiv.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Opposite
import Mathlib.Set
import Mathlib.Logic.Basic

/-!
# Quivers
This module defines quivers. A Quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a very permissive notion of directed graph.
-/

open opposite

-- We use the same universe order as in category theory.
-- See note [category_theory universes]
universes v v₁ v₂ u u₁ u₂

/--
A Quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`.
For graphs with no repeated edges, one can use `Quiver.{0} V`, which ensures
`a ⟶ b : Prop`. For multigraphs, one can use `Quiver.{v+1} V`, which ensures
`a ⟶ b : Type v`.
Because `category` will later extend this class, we call the field `hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
class Quiver (V : Type u) :=
(hom : V → V → Type v)

infixr:10 " ⟶ " => Quiver.hom -- type as \h

/--
A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `prefunctor`.
-/
structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] :=
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
def id (V : Type u) [Quiver V] : Prefunctor V V :=
{ obj := id',
  map := λ f => f, }

instance (V : Type u) [Quiver V] : Inhabited (Prefunctor V V) := ⟨id V⟩

/--
Composition of morphisms between quivers.
-/
@[simp]
def comp {U : Type u} [Quiver U] {V : Type v} [Quiver V] {W : Type w} [Quiver W]
  (F : Prefunctor U V) (G : Prefunctor V W) : Prefunctor U W :=
{ obj := G.obj ∘ F.obj,
  map := λ f => G.map (F.map f), }

end Prefunctor

/-- A wide subquiver `H` of `G` picks out a set `H a b` of arrows from `a` to `b`
    for every pair of vertices `a b`. -/
def WideSubquiver (V) [Quiver V] :=
∀ a b : V, Set (a ⟶ b)

/-- A type synonym for `V`, when thought of as a Quiver having only the arrows from
some `WideSubquiver`. -/
def WideSubquiver.toType (V) [Quiver V] (H : WideSubquiver V) : Type u := V

lemma WideSubquiver.toTypeDef (V) [Quiver V] (H : WideSubquiver V) : H.toType = V := rfl

instance WideSubquiverCoeSort {V} [Quiver V] : CoeSort (WideSubquiver V) (Type u) :=
{coe := λ H => WideSubquiver.toType V H}

/-- A wide subquiver viewed as a Quiver on its own. -/
/- Not sure why the CoeSort instance defined above doesn't trigger here.-/
instance WideSubquiver.ToQuiver {V : Type u} [q : Quiver V] (H : WideSubquiver V) : Quiver (H.toType) :=
⟨λ a b => Subtype (H a b)⟩

namespace Quiver

/-- A type synonym for a Quiver with no arrows. -/
def empty (V : Type u) : Type u := V
instance empty_quiver (V : Type (u)) : Quiver.{u} (empty V) := ⟨λ a b => ulift Empty⟩

@[simp] lemma empty_arrow {V : Type u} (a b : empty V) : (a ⟶ b) = ulift Empty := rfl

-- instance {V} [Quiver V] : Bot (WideSubquiver V) := ⟨λ a b => ∅⟩
-- instance {V} [Quiver V] : Top (WideSubquiver V) := ⟨λ a b => Set.univ⟩
instance {V} [Quiver V] : Inhabited (WideSubquiver V) := ⟨λ a b => Set.univ⟩


/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance opposite {V : Type u} [Quiver V] : Quiver (Vᵒᵖ) :=
⟨λ a b => (unop b) ⟶ (unop a)⟩

/--
The opposite of an arrow in `V`.
-/
def hom.op {V: Type u} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X := f
/--
Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`.
-/
def hom.unop {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := f

attribute [irreducible] Quiver.opposite

/-- A type synonym for the symmetrized Quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[Quiver.{v+1} V]`. -/
def symmetrify (V : Type u) : Type u := V

instance symmetrify_quiver (V : Type u) [Quiver V] : Quiver (symmetrify V) :=
⟨λ a b : V => Sum (a ⟶ b) (b ⟶ a)⟩

/-- `total V` is the type of _all_ arrows of `V`. -/
-- TODO Unify with `category_theory.arrow`? (The fields have been named to match.)
structure total (V : Type u) [Quiver.{v} V] : Sort (max (u+1) (v+1)) :=
(left : V)
(right : V)
(hom : left ⟶ right)

/-- A wide subquiver `H` of `G.symmetrify` determines a wide subquiver of `G`, containing an
    an arrow `e` if either `e` or its reversal is in `H`. -/
-- Without the explicit universe level in `Quiver.{v+1}` Lean comes up with
-- `Quiver.{max u_2 u_3 + 1}`. This causes problems elsewhere, so we write `Quiver.{v+1}`.
def WideSubquiverSymmetrify {V} [Quiver.{v+1} V] :
  WideSubquiver (symmetrify V) → WideSubquiver V :=
λ H a b => { e | Sum.inl e ∈ H a b ∨ Sum.inr e ∈ H b a }

/-- A wide subquiver of `G` can equivalently be viewed as a total set of arrows. -/
def WideSubquiver_equivSet_total {V : Type v} [Quiver V] :
  WideSubquiver V ≃ Set (total V) :=
{ to_fun := λ H => { e | e.hom ∈ H e.left e.right },
  inv_fun := λ S a b => { e | total.mk a b e ∈ S },
  left_inv := λ H => rfl,
  right_inv := λ S => by {
    funext x;
    simp;
    rw [setOfExt, Set.memSetOf, Set.memDef];
    cases x;
    simp;
  }
}

/-- `G.Path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive Path {V : Type u} [Quiver.{v} V] (a : V) : V → Sort (max (u+1) (v+1))
| Nil  : Path a a
| Cons : {b c : V} -> Path a b → (b ⟶ c) → Path a c

/-- An arrow viewed as a Path of length one. -/
def hom.to_path {V} [Quiver V] {a b : V} (e : a ⟶ b) : Path a b :=
Path.Nil.Cons e

namespace Path

variable {V : Type u} [Quiver V]

/-- The length of a Path is the number of arrows it uses. -/
def length {a : V} {b : V} : Path a b → ℕ
| (Path.Nil)        => 0
| (Path.Cons p _) => p.length + 1

@[simp] lemma length_Nil {a : V} :
  (Path.Nil : Path a a).length = 0 := rfl

@[simp] lemma length_cons (a b c : V) (p : Path a b)
  (e : b ⟶ c) : (p.Cons e).length = p.length + 1 := rfl

/-- Composition of paths. -/
def comp {a b c : V} (p : Path a b) : Path b c → Path a c
| (Path.Nil) => p
| (Path.Cons q e) => (p.comp q).Cons e

@[simp] lemma comp_cons {a b c d : V} (p : Path a b) (q : Path b c) (e : c ⟶ d) :
  p.comp (q.Cons e) = (p.comp q).Cons e := rfl
@[simp] lemma comp_Nil {a b : V} (p : Path a b) : p.comp Path.Nil = p := rfl
@[simp] lemma Nil_comp {a : V} {b} : (p : Path a b) -> Path.Nil.comp p = p
| Path.Nil => rfl
| (Path.Cons p e) => by rw [comp_cons, Nil_comp]
@[simp] lemma comp_assoc {a b c d : V}
  (p : Path a b) (q : Path b c) :
    (r : Path c d) →
    (p.comp q).comp r = p.comp (q.comp r)
| Path.Nil => rfl
| (Path.Cons r e) => by rw [comp_cons, comp_cons, comp_cons, comp_assoc]

end Path

end Quiver

namespace prefunctor

open Quiver

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] (F : Prefunctor V W)

/-- The image of a Path under a prefunctor. -/
def map_path {a b : V} : Path a b → Path (F.obj a) (F.obj b)
| Path.Nil => Path.Nil
| (Path.Cons p e) => Path.Cons (map_path p) (F.map e)

@[simp] lemma map_path_Nil (a : V) :
  map_path F (Path.Nil : Path a a) = (Path.Nil : Path (F.obj a) (F.obj a)) := rfl
@[simp] lemma map_path_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  map_path F (Path.Cons p e) = Path.Cons (map_path F p) (F.map e) := rfl

@[simp] lemma map_path_comp {a b : V} (p : Path a b) {c : V} :
  (q : Path b c) →
  map_path F (p.comp q) = (map_path F p).comp (map_path F q)
| Path.Nil => rfl
| (Path.Cons p e) => by {
  simp;
  rw [map_path_comp];
  split;
  apply HEq.rfl;
  apply HEq.rfl;
}

end prefunctor

/-- CSPAM should be moved somewhere more basic -/
class Unique (α : Type u) extends Inhabited α :=
 (onlyDefault {y : α} : y = default)

namespace Quiver

/-- A Quiver is an Arborescence when there is a unique Path from the default vertex
    to every other vertex. -/
class Arborescence (V : Type u) [Quiver.{v} V] : Type (max u v) :=
(root : V)
(uniquePath (b : V) : Unique (Path root b))

/-- The root of an Arborescence. -/
def root (V : Type u) [Quiver V] [Arborescence V] : V :=
Arborescence.root

instance {V : Type u} [Quiver V] [Arborescence V] (b : V) : Unique (Path (root V) b) :=
Arborescence.uniquePath b

/-- An `L`-labelling of a Quiver assigns to every arrow an element of `L`. -/
def labelling (V : Type u) [Quiver V] (L : Sort*) := Π ⦃a b : V⦄, (a ⟶ b) → L

instance {V : Type u} [Quiver V] (L) [inhabited L] : inhabited (labelling V L) :=
⟨λ a b e, default L⟩

/-- To show that `[Quiver V]` is an Arborescence with root `r : V`, it suffices to
  - provide a height function `V → ℕ` such that every arrow goes from a
    lower vertex to a higher vertex,
  - show that every vertex has at most one arrow to it, and
  - show that every vertex other than `r` has an arrow to it. -/
noncomputable def arborescence_mk {V : Type u} [Quiver V] (r : V)
  (height : V → ℕ)
  (height_lt : ∀ ⦃a b⦄, (a ⟶ b) → height a < height b)
  (unique_arrow : ∀ ⦃a b c : V⦄ (e : a ⟶ c) (f : b ⟶ c), a = b ∧ e == f)
  (root_or_arrow : ∀ b, b = r ∨ ∃ a, nonempty (a ⟶ b)) : Arborescence V :=
{ root := r,
  unique_path := λ b, ⟨classical.inhabited_of_nonempty
    begin
      rcases (show ∃ n, height b < n, from ⟨_, lt_add_one _⟩) with ⟨n, hn⟩,
      induction n with n ih generalizing b,
      { exact false.elim (nat.not_lt_zero _ hn) },
      rcases root_or_arrow b with ⟨⟨⟩⟩ | ⟨a, ⟨e⟩⟩,
      { exact ⟨path.Nil⟩ },
      { rcases ih a (lt_of_lt_of_le (height_lt e) (nat.ltSucc_iff.mp hn)) with ⟨p⟩,
        exact ⟨p.Cons e⟩ }
    end,
    begin
      have height_le : ∀ {a b}, Path a b → height a ≤ height b,
      { intros a b p, induction p with b c p e ih, refl,
        exact le_of_lt (lt_of_le_of_lt ih (height_lt e)) },
      suffices : ∀ p q : Path r b, p = q,
      { intro p, apply this },
      intros p q, induction p with a c p e ih; cases q with b _ q f,
      { refl },
      { exact false.elim (lt_irrefl _ (lt_of_le_of_lt (height_le q) (height_lt f))) },
      { exact false.elim (lt_irrefl _ (lt_of_le_of_lt (height_le p) (height_lt e))) },
      { rcases unique_arrow e f with ⟨⟨⟩, ⟨⟩⟩, rw ih },
    end ⟩ }

/-- `rooted_connected r` means that there is a Path from `r` to any other vertex. -/
class rooted_connected {V : Type u} [Quiver V] (r : V) : Prop :=
(nonempty_path : ∀ b : V, nonempty (Path r b))

attribute [instance] rooted_connected.nonempty_path

section geodesicSubtree

variables {V : Type u} [Quiver.{v+1} V] (r : V) [rooted_connected r]

/-- A Path from `r` of minimal length. -/
noncomputable def shortest_path (b : V) : Path r b :=
well_founded.min (measure_wf Path.length) Set.univ Set.univ_nonempty

/-- The length of a Path is at least the length of the shortest Path -/
lemma shortest_pathSpec {a : V} (p : Path r a) :
  (shortest_path r a).length ≤ p.length :=
not_lt.mp (well_founded.not_lt_min (measure_wf _) Set.univ _ trivial)

/-- A subquiver which by construction is an Arborescence. -/
def geodesicSubtree : WideSubquiver V :=
λ a b, { e | ∃ p : Path r a, shortest_path r b = p.Cons e }

noncomputable instance geodesic_arborescence : Arborescence (geodesicSubtree r) :=
arborescence_mk r (λ a, (shortest_path r a).length)
(by { rintros a b ⟨e, p, h⟩,
  rw [h, Path.length_cons, nat.ltSucc_iff], apply shortest_pathSpec })
(by { rintros a b c ⟨e, p, h⟩ ⟨f, q, j⟩, cases h.symm.trans j, split; refl })
(by { intro b, have : ∃ p, shortest_path r b = p := ⟨_, rfl⟩,
  rcases this with ⟨p, hp⟩, cases p with a _ p e,
  { exact or.inl rfl }, { exact or.inr ⟨a, ⟨⟨e, p, hp⟩⟩⟩ } })

end geodesicSubtree

variables (V : Type u) [Quiver.{v+1} V]

/-- A Quiver `has_reverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class has_reverse :=
(reverse' : Π {a b : V}, (a ⟶ b) → (b ⟶ a))

instance : has_reverse (symmetrify V) := ⟨λ a b e, e.swap⟩

variables {V} [has_reverse V]

/-- Reverse the direction of an arrow. -/
def reverse {a b : V} : (a ⟶ b) → (b ⟶ a) := has_reverse.reverse'

/-- Reverse the direction of a Path. -/
def Path.reverse {a : V} : Π {b}, Path a b → Path b a
| a Path.Nil := Path.Nil
| b (Path.Cons p e) := (reverse e).to_path.comp p.reverse

variables (V)

/-- Two vertices are related in the zigzag setoid if there is a
    zigzag of arrows from one to the other. -/
def zigzagSetoid : Setoid V :=
⟨λ a b, nonempty (Path (a : symmetrify V) (b : symmetrify V)),
 λ a, ⟨path.Nil⟩,
 λ a b ⟨p⟩, ⟨p.reverse⟩,
 λ a b c ⟨p⟩ ⟨q⟩, ⟨p.comp q⟩⟩

/-- The type of weakly connected components of a directed graph. Two vertices are
    in the same weakly connected component if there is a zigzag of arrows from one
    to the other. -/
def weakly_connected_component : Type* := quotient (zigzagSetoid V)

namespace weakly_connected_component
variable {V}

/-- The weakly connected component corresponding to a vertex. -/
protected def mk : V → weakly_connected_component V := quotient.mk'

instance : has_coe_t V (weakly_connected_component V) := ⟨weakly_connected_component.mk⟩
instance [inhabited V] : inhabited (weakly_connected_component V) := ⟨↑(default V)⟩

protected lemma eq (a b : V) :
  (a : weakly_connected_component V) = b ↔ nonempty (Path (a : symmetrify V) (b : symmetrify V)) :=
quotient.eq'

end weakly_connected_component

end Quiver
