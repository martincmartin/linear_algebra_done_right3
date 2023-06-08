-- Now that you've had a taste for how complex numbers and tuples are defined,
-- from now on we won't use our definitions from the last section, but rather
-- the definitions that come with Lean.

import algebra.field.basic
import init.data.fin.basic
import group_theory.group_action.pi

-- 1.19  Definition  vector space

-- In LADR, a vector space is a set V and field F, along with two functions,
-- addition and scalar multiplication of vectors.  It also requries that certain
-- properties hold.  Some of those properties include "there exists," for
-- example "∀ v : V, ∃ w : V, v + w = 0."  Lean prefers an alternate approach,
-- where instead of "there exists" properties, we provide a function which,
-- given v, returns w.

-- Lean has a vary useful ability to take *implicit arguments*.  For example,
-- when you want to apply the theorem "0 + v = v" to a particular v, you don't
-- need to explicitly specify the vector_space, it can usually infer it.  Not
-- having to explicitly write the vector_space everywhere saves a lot of reading
-- & generally focuses on what's important, rather than what's understood.  For
-- example, in Linear Algebra Done Right, Axler says "from now on, V is a vector
-- space" and then doesn't need to repeat it over and over for each theorm.

-- Some theorems don't depend on the field of scalars and will work with any
-- field, e.g. the theorm that the negative (addative inverse) of a vector is
-- unique.  In this case, Lean can go looking for the field, but since any field
-- will do, it won't have a lot of guideance and can get stuck.  And anyway this
-- work is useless, since the field isn't even used in the proof.

-- So, we separate out the parts that involve only addition, including the zero
-- and negation, into a class of their own that doesn't even mention field.  In
-- abstract algebra, this is an additive commutative group, so we call it
-- add_comm_group.

-- Put this in its own namespace, since there is already an add_comm_group in
-- mathlib, and it gets included when we include field.
namespace LADR

-- "extends has_add" adds a function 'add' to vector_space that uses infix
-- notation, e.g. 'u + v'.  Similarly with the other "extends" clauses.
@[ext]
class add_comm_group (V : Type*) extends has_add V, has_zero V, has_neg V :=
(add_comm : ∀ u v : V, u + v = v + u)
(add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w))
(add_zero : ∀ v : V, v + 0 = v)
(add_right_inv : ∀ v : V, v + -v = 0)


@[ext]
class vector_space (F : Type*) (V : Type*) [field F] [add_comm_group V]
  extends has_smul F V :=
(smul_assoc : ∀ a b : F, ∀ v : V, (a * b) • v = a • (b • v))
(mul_ident : ∀ v : V, (1 : F) • v = v)
(left_distrib : ∀ a : F, ∀ u v : V, a • (u + v) = (a • u) + (a • v))
(right_distrib : ∀ a b :F, ∀ v : V, (a + b) • v = (a • v) + (b • v))

-- "F^n is a vector space over F, as you should verify."

variables {F : Type*} [field F] {n : ℕ}

instance n_tuple_add_comm_group : add_comm_group (fin n → F) :=
{ add := λ u v, u + v,
  zero := 0,
  neg := λ v, - v,
  add_comm := add_comm,
  add_assoc := add_assoc,
  add_zero := add_zero,
  add_right_inv := add_neg_self
}

-- Should this use instance or def?
def n_tuple_vector_space : vector_space F (fin n → F) :=
{ smul := λ a v, a • v,
  smul_assoc := smul_assoc,
  mul_ident := one_smul F,
  left_distrib := 
  begin
    intros a u v,
    funext,
    simp,
    apply field.left_distrib
  end,
  right_distrib :=
  begin
    intros a b v,
    funext,
    simp,
    apply field.right_distrib
  end}


-- 1.22  Example  F^∞ 

-- We defined an n-tuple as a map from `fin n` to F, so a natural definition of
-- an infinite tuple is just a map from ℕ to F.

instance inf_tuple_add_comm_group : add_comm_group (ℕ → F) :=
{ add := λ u v, u + v,
  zero := 0,
  neg := λ v, - v,
  add_comm := add_comm,
  add_assoc := add_assoc,
  add_zero := add_zero,
  add_right_inv := add_neg_self
}

def inf_tuple_vector_space : vector_space F (ℕ → F) :=
{ smul := λ a v, a • v,
  smul_assoc := smul_assoc,
  mul_ident := one_smul F,
  left_distrib := 
  begin
    intros a u v,
    funext,
    simp,
    apply field.left_distrib
  end,
  right_distrib :=
  begin
    intros a b v,
    funext,
    simp,
    apply field.right_distrib
  end}


-- 1.23  Notation  F^S
-- In Lean, we generally use types where most mathematicians use sets.  Also in
-- Lean, the type of functions from S to F is 'S → F'.

-- 1.24  Example  F^S is a vector space
variable S : Type*
instance fun_add_comm_group : add_comm_group (S → F) :=
{ add := λ u v, u + v,
  zero := 0,
  neg := λ v, - v,
  add_comm := add_comm,
  add_assoc := add_assoc,
  add_zero := add_zero,
  add_right_inv := add_neg_self
}

def fun_vector_space : vector_space F (S → F) :=
{ smul := λ a v x, a * v x,
  smul_assoc := smul_assoc,
  mul_ident := one_smul F,
  left_distrib := 
  begin
    intros a u v,
    funext,
    apply field.left_distrib
  end,
  right_distrib :=
  begin
    intros a b v,
    funext,
    apply field.right_distrib
  end}


namespace vector_space

-- 1.25  Unique additive identity
-- "A vector space has a unique additive identity"

theorem unique_add_ident {V : Type*} [add_comm_group V] {z : V} (h: ∀ v : V, v + z = v):
  z = 0 :=
  calc z = z + 0 : by rw add_comm_group.add_zero
  ...    = 0 + z : by rw add_comm_group.add_comm
  ...    = 0     : by rw h


-- 1.26  Unique additive inverse
-- "Every element in a vector space has a unique additive inverse"

lemma zero_add {V : Type*} [add_comm_group V] {v : V} : 0 + v = v :=
begin
  rw add_comm_group.add_comm,
  apply add_comm_group.add_zero
end

theorem unique_add_inv {V : Type*} [add_comm_group V] {v w : V} (h : v + w = 0):
  w = -v :=
  calc w = w + 0 : by rw add_comm_group.add_zero
  ...    = w + (v + -v) : by rw ← add_comm_group.add_right_inv
  ...    = (w + v) + -v : by rw add_comm_group.add_assoc
  ...    = (v + w) + -v : by rw add_comm_group.add_comm w v
  ...    = 0 + -v : by rw h
  ...    = -v : by rw zero_add


-- 1.27  Notation  -v, w - v
-- We started with -v, before proving it was unique.

-- Notation for 'w - v'
instance {V : Type*} [add_comm_group V] : has_sub V := ⟨λ w v, w + (-v)⟩
@[simp] lemma sub_add_neg {V : Type*} [add_comm_group V] (u v : V) :
  u - v = u + (-v) := rfl


-- 1.28  Notation  V
variables {V : Type*} [add_comm_group V] [vector_space F V]


-- 1.29  The number 0 times a vector

-- Lean proofs are very explicit, so we tend to use lots of helper lemmas for
-- things that most mathematicians wouldn't even mention in their proofs.

theorem sub_self {v : V} : v - v = 0 :=
  by {simp, apply add_comm_group.add_right_inv}

theorem add_sub_cancel {u v : V} : (u + v) - v = u :=
begin
  simp,
  rw [add_comm_group.add_assoc, add_comm_group.add_right_inv, add_comm_group.add_zero]
end

-- All the (0 : F) here is really distracting.  Is there a way to get Lean to
-- understand that in 0 • v, the zero is not a natural number but from the
-- field?
theorem zero_vec_eq_zero {v : V} : (0 : F) • v = 0 :=
begin
  apply eq.symm,
  calc 0 = (0 : F) • v - (0 : F) • v : by rw sub_self
  ...    = ((0 : F) + (0 : F)) • v - (0 : F) • v : by simp
  ...    = (0 : F) • v + (0 : F) • v - (0 : F) • v : by rw right_distrib
  ...    = (0 : F) • v : by apply add_sub_cancel
end


-- 1.30  A number times the vector 0

theorem field_zero_eq_zero {a : F} : a • (0 : V) = 0 :=
begin
  calc
    a • (0 : V) = a • 0 + a • 0 - a • 0 : by rw add_sub_cancel
    ...         = a • (0 + 0) - a • 0 : by rw left_distrib
    ...         = a • 0 - a • 0 : by rw add_comm_group.add_zero
    ...         = 0 : by rw sub_self
end


-- 1.31  The number -1 times a vector

theorem neg_one_smul_is_neg {v : V} : (-1 : F) • v = - v :=
begin
  rw ← unique_add_inv,
  calc v + (-1 : F) • v = (1 : F) • v + (-1 : F) • v : by rw mul_ident
  ...                   = ((1 : F) + (-1 : F)) • v : by rw right_distrib
  ...                   = (0 : F) • v : by simp
  ...                   = 0 : zero_vec_eq_zero
  
end

end vector_space
end LADR
