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

/--
The identity morphism between quivers.
-/
@[simp]
def id (V : Type u) [Quiver V] : Prefunctor V V :=
{ obj := _root_.id,
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
| Cons : Path a b → (b ⟶ c) → Path a c

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

namespace Quiver

/-- A Quiver is an Arborescence when there is a unique Path from the default vertex
    to every other vertex. -/
class Arborescence (V : Type u) [Quiver.{v} V] : Type (max u v) :=
(root : V)
(unique_path (b : V) : ∃ p : Path root b, ∀ q, q = p)

/-- The root of an Arborescence. -/
def root (V : Type u) [Quiver V] [Arborescence V] : V :=
Arborescence.root

/-- An `L`-labelling of a Quiver assigns to every arrow an element of `L`. -/
def labelling (V : Type u) [Quiver V] (L : Sort v) := ∀ {a b : V}, (a ⟶ b) → L

instance {V : Type u} [Quiver V] (L) [Inhabited L] : Inhabited (labelling V L) :=
⟨λ _ => Inhabited.default⟩

section arborescence

/- CSPAM - I gave up on getting strong induction to work for now -/
/-- To show that `[Quiver V]` is an Arborescence with root `r : V`, it suffices to
  - provide a height function `V → ℕ` such that every arrow goes from a
    lower vertex to a higher vertex,
  - show that every vertex has at most one arrow to it, and
  - show that every vertex other than `r` has an arrow to it. -/

lemma Nat.lt_add_one (n : ℕ) : n < n + 1 :=
  by {
    rw [Nat.add_one];
    apply Nat.ltSuccSelf
  }

variable {V : Type v} [q : Quiver V] (r : V) [DecidableEq V]
variable (height : V → ℕ)
variable (height_lt : ∀ {a b}, (a ⟶ b) → height a < height b)
variable (unique_arrow : ∀ {a b c : V} (e : a ⟶ c) (f : b ⟶ c), a = b ∧ (e ≅ f))
variable (root_or_arrow : {b : V} -> (b ≠ r) → (Σ (a : V), a ⟶ b))

def height_path_le {a c} (p : Path a c) : height a ≤ height c :=
  by
    induction p with
      | Nil => apply Nat.le_refl _
      | Cons p arr ih =>
        apply Nat.le_trans ih
        apply Nat.le_of_lt
        exact height_lt arr

def mk_path_for_height : ∀ (n : ℕ) (b : V), height b ≤ n -> Path r b
 | 0, b, b_height_le  =>
  if h : b = r
    then by
      rw [← h]
      exact Path.Nil
    else by
      let ⟨a, arr⟩ := root_or_arrow h
      have : ∀ n, ¬ n < 0 := by {intros; simp; apply Nat.zero_le}
      exfalso
      apply this (height a)
      apply Nat.lt_of_lt_of_le
      apply height_lt arr
      exact b_height_le

 | (n+1), b, b_height_eq =>
  if h : b = r
    then by
      rw [← h]
      exact Path.Nil
    else
      let ⟨a, arr⟩ := root_or_arrow h
      let a_height_le : height a ≤ n :=
        by
        have : height a < n+1 :=
          Nat.lt_of_lt_of_le (height_lt arr) b_height_eq
        simp
        apply this
      Path.Cons (mk_path_for_height n a a_height_le) arr

instance mk_path (b : V) : (Path r b) :=
  mk_path_for_height r height height_lt root_or_arrow (height b) b (Nat.le_refl _)

def path_self_nil {a : V} (p : Path a a) : p = Path.Nil :=
  match p with
  | Path.Nil => rfl
  | Path.Cons p arr =>
    have : ∀ n : Nat, ¬ n < n := by
      intros n
      simp
      apply Nat.le_refl
    by
      exfalso
      apply this (height a)
      apply Nat.lt_of_le_of_lt
      apply (height_path_le height height_lt p)
      apply (height_lt arr)

theorem path_unique {a c : V} (p q : Path a c) : p = q := by
  induction p with
  | Nil => apply (path_self_nil height height_lt q).symm
  | Cons p_path p_arrow ih =>
    cases q with
    | Nil => apply (path_self_nil height height_lt _)
    | Cons q_path q_arrow =>
      let ⟨b_eq, arrow_heq⟩ := unique_arrow p_arrow q_arrow
      cases b_eq
      cases arrow_heq
      rw [← ih q_path]

def arborescence_mk : Arborescence V :=
{ root := r,
  unique_path := λ b =>
    let path : Path r b := mk_path r height height_lt root_or_arrow b
    let is_unique (q : Path r b) : q = path :=
      path_unique height height_lt unique_arrow q path
    ⟨path, is_unique⟩
}

inductive nonempty (T : Type u) : Prop :=
  | Some : T -> nonempty T

open nonempty

/-- `rooted_connected r` means that there is a Path from `r` to any other vertex. -/
class rooted_connected {V : Type u} [Quiver V] (r : V) : Prop :=
  (nonempty_path : (b : V) -> nonempty (Path r b))

attribute [instance] rooted_connected.nonempty_path

-- Requires well_founded.min which hasn't been ported yet - CSPAM
-- section geodesicSubtree

-- variables {V : Type u} [Quiver.{v+1} V] (r : V) [rooted_connected r]

-- /-- A Path from `r` of minimal length. -/
-- noncomputable def shortest_path (b : V) : Path r b :=
-- well_founded.min (measure_wf Path.length) Set.univ Set.univ_nonempty

-- /-- The length of a Path is at least the length of the shortest Path -/
-- lemma shortest_pathSpec {a : V} (p : Path r a) :
--   (shortest_path r a).length ≤ p.length :=
-- not_lt.mp (well_founded.not_lt_min (measure_wf _) Set.univ _ trivial)

-- /-- A subquiver which by construction is an Arborescence. -/
-- def geodesicSubtree : WideSubquiver V :=
-- λ a b, { e | ∃ p : Path r a, shortest_path r b = p.Cons e }

-- noncomputable instance geodesic_arborescence : Arborescence (geodesicSubtree r) :=
-- arborescence_mk r (λ a, (shortest_path r a).length)
-- (by { rintros a b ⟨e, p, h⟩,
--   rw [h, Path.length_cons, nat.ltSucc_iff], apply shortest_pathSpec })
-- (by { rintros a b c ⟨e, p, h⟩ ⟨f, q, j⟩, cases h.symm.trans j, split; refl })
-- (by { intro b, have : ∃ p, shortest_path r b = p := ⟨_, rfl⟩,
--   rcases this with ⟨p, hp⟩, cases p with a _ p e,
--   { exact or.inl rfl }, { exact or.inr ⟨a, ⟨⟨e, p, hp⟩⟩⟩ } })

-- end geodesicSubtree

end arborescence


section has_reverse
variable (V : Type u) [Quiver.{v+1} V]

/-- A Quiver `has_reverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class has_reverse :=
(reverse' : {a b : V} → (a ⟶ b) → (b ⟶ a))

instance : has_reverse (symmetrify V) :=
  ⟨λ e =>
    match e with
    | Sum.inl a => Sum.inr a
    | Sum.inr a => Sum.inl a
  ⟩
end has_reverse

section reverse
variable {V : Type u} [Quiver.{v+1} V] [has_reverse V]

/-- Reverse the direction of an arrow. -/
def Hom.reverse {a b : V} : (a ⟶ b) → (b ⟶ a) := has_reverse.reverse'

/-- Reverse the direction of a Path. -/
def Path.reverse {a :V} : {b : V} → Path a b → Path b a
| .(a), Path.Nil => Path.Nil
| b, (Path.Cons p e) => (Hom.reverse e).to_path.comp p.reverse
end reverse

section zigzag
variable (V : Type u) [Quiver.{v+1} V] [has_reverse V]

open nonempty

/-- Two vertices are related in the zigzag setoid if there is a
    zigzag of arrows from one to the other. -/
def zigzagSetoid : Setoid V :=
  ⟨λ a b => nonempty (Path (a : symmetrify V) (b : symmetrify V)),
    λ a => ⟨Path.Nil⟩,
    by
      intros x y p
      cases p with | Some p =>
      split
      apply Path.reverse p,
    by
      intros x y z xy yz
      cases xy with | Some xy =>
      cases yz with | Some yz =>
      apply Some (xy.comp yz)
 ⟩

/-- The type of weakly connected components of a directed graph. Two vertices are
    in the same weakly connected component if there is a zigzag of arrows from one
    to the other. -/
def weakly_connected_component : Type u := Quotient (zigzagSetoid V)

end zigzag

namespace weakly_connected_component
variable {V} [Quiver.{v+1} V] [has_reverse V]

/-- The weakly connected component corresponding to a vertex. -/
protected def mk : V → weakly_connected_component V := Quotient.mk V

instance : has_coe_t V (weakly_connected_component V) := ⟨weakly_connected_component.mk⟩
instance [Inhabited V] : Inhabited (weakly_connected_component V) := ⟨↑(default V)⟩

protected lemma eq (a b : V) :
  (a : weakly_connected_component V) = b ↔ nonempty (Path (a : symmetrify V) (b : symmetrify V)) :=
quotient.eq'

end weakly_connected_component

end Quiver
