-- Subgroups


import algebra.field.basic
import data.set_like.basic
import chapter1.section1B

-- import algebra.module.basic
-- import algebra.module.submodule.basic

-- Preferred method for Lean 3.  See https://arxiv.org/pdf/2306.00617.pdf
set_option old_structure_cmd true



-- Note that we don't have the problem with "extends" that we had for
-- vector_space, since this is a structure not a class, and structures can't use
-- implicit search.  We make it a structure because the carrier isn't a type but
-- a field of the structure.
--
-- How submodule is structured:
--
-- universes u'' u' u v w
-- variables {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}
--
-- structure submodule (R : Type u) (M : Type v) [semiring R]
--  [add_comm_monoid M] [module R M] extends add_submonoid M, sub_mul_action R M : Type v.
--
-- structure add_submonoid (M : Type*) [add_zero_class M] extends add_subsemigroup M :=
-- (zero_mem' : (0 : M) ∈ carrier)
--
-- Note: This is actually an additive submanga, i.e. the only constraint is that
-- we must be closed under addition.  Associativity of M would be specified
-- elsewhere, and when that's true, this is also an additive sub semigroup.  So
-- they chose the name for the (much) more common usecase of subsemigroup.
--
-- structure add_subsemigroup (M : Type*) [has_add M] :=
-- (carrier : set M)
-- (add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier)
--
-- class add_zero_class (M : Type u) extends has_zero M, has_add M :=
-- (zero_add : ∀ (a : M), 0 + a = a)
-- (add_zero : ∀ (a : M), a + 0 = a)
--
-- structure sub_mul_action (R : Type u) (M : Type v) [has_smul R M] : Type v :=
-- (carrier : set M)
-- (smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier)


-- So we could (try to) not split into two classes this time, and just have one
-- subspace structure.  But it seems natural, having introduced the concept of
-- commutative group in the last section, to create a commutative subgroup here.


namespace LADR

-- LADR defines a subspace as a subset that's also a vector space, then derives
-- the standard conditions.  Because showing the standard conditions is the most
-- common way of demonstrating that a subset is indeed a subspace, it's easier
-- to put those in the Lean definition, then derive that the result is indeed a
-- vector space.

-- Since we split the vector space into two structures, here we need a "sub" for
-- each.

structure add_comm_subgroup (V : Type*) [add_comm_group V] :=
(carrier : set V)
(add_mem' : ∀ {u v : V}, u ∈ carrier → v ∈ carrier → u + v ∈ carrier)
(zero_mem' : (0 : V) ∈ carrier)

-- Should we show that a subgroup is also a group?

namespace add_comm_subgroup

variables {V : Type*} [add_comm_group V] {v : V}

instance : set_like (add_comm_subgroup V) V :=
⟨ add_comm_subgroup.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp] lemma mem_carrier {p : add_comm_subgroup V} : v ∈ p.carrier ↔ v ∈ (p : set V) := iff.rfl

@[ext] theorem ext {p q : add_comm_subgroup V} (h : ∀ v, v ∈ p ↔ v ∈ q) : p = q := set_like.ext h

end add_comm_subgroup

-- Because this is a structure rather than a class, it's ok to extend add_comm_subgroup
structure subspace (F : Type*) (V : Type*)
  [field F] [add_comm_group V] [vector_space F V] extends add_comm_subgroup V :=
(smul_mem' : ∀ (c : F) {v : V}, v ∈ carrier → c • v ∈ carrier )

namespace subspace

variables {F : Type*} {V : Type*} [field F] [add_comm_group V] [vector_space F V]
variable {v : V}

instance : set_like (subspace F V) V :=
⟨subspace.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp] lemma mem_carrier {p : subspace F V} : v ∈ p.carrier ↔ v ∈ (p : set V) := iff.rfl

@[ext] theorem ext {p q : subspace F V} (h : ∀ v, v ∈ p ↔ v ∈ q) : p = q := set_like.ext h

variables (p : subspace F V)

-- 1.34 Conditions for a subspace
-- A subset U of V is a itself a vector space if and only if it satisfies the
-- 'subspace' conditions above.

-- First, show the reverse, i.e. when p satisfies the subspace conditions, then
-- it is a vector space.

-- Elements of ↥p are pairs: an element of the original V, plus a proof that
-- the element is in p.carrier.
-- For v: ↥p, ↑v is ... that first element, of the original V?

-- variables (p)

instance fooblah : add_comm_group p := {
  add := λ u v, ⟨ u.1 + v.1, by { apply p.add_mem', simp, simp} ⟩,
  zero := ⟨0, p.zero_mem'⟩,
  neg := λ v, ⟨-v.1, by {
     rw ← @vector_space.neg_one_smul_is_neg F _ V, apply p.smul_mem', simp
     }⟩,

  add_comm := by {intros, ext, simp, apply add_comm_group.add_comm},
  add_assoc := by {intros, ext, simp, apply add_comm_group.add_assoc},
  add_zero := by {intros, ext, simp, rw add_comm_group.add_zero},
  add_right_inv := by {intros, ext, simp, rw add_comm_group.add_right_inv},
}


--variables {FF : Type*} {VV : Type*}
--variables [field FF] {add_comm_group_VV : add_comm_group VV}
--variables [vs : vector_space FF VV]
--variables (q : subspace FF VV)


@[simp] lemma add_subspace {u v : p} : ↑(u + v) = u.1 + v.1 := rfl

instance vector_space' : vector_space F p := {
  smul := λ s v, ⟨ s • v.1, by { apply p.smul_mem', simp} ⟩,
  smul_assoc := by {intros, simp, apply vector_space.smul_assoc},
  mul_ident := by {intros, ext, simp, rw vector_space.mul_ident},
  left_distrib := by {intros, ext, simp, rw vector_space.left_distrib},
  right_distrib := by {intros, ext, simp, rw vector_space.right_distrib},
}

instance : vector_space F p := p.vector_space'

end subspace

-- Next, show that for any subset of a vector space that is itself a vector
-- space, it must satisfy the three subspace conditions.

structure subset_of_vector_space (F : Type*) (V : Type*)
  [field F] [vector_space F V] :=
(carrier : set V)

namespace subset_of_vector_space

variables (F : Type*) {V : Type*} [field F] [vector_space F V]
variable {v : V}


instance : set_like (subset_of_vector_space F V) V :=
⟨ subset_of_vector_space.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp] lemma mem_carrier {p : subset_of_vector_space F V} : v ∈ p.carrier ↔ v ∈ (p : set V) := iff.rfl

@[ext] theorem ext {p q : subset_of_vector_space F V} (h : ∀ v, v ∈ p ↔ v ∈ q) : p = q := set_like.ext h

-- So the different sets and types are confusing to me.

-- "v ∈ p" is for elements of the big vector space being in the small one.  I
-- think there's an implicit coercion in there somewhere, maybe p to p.carrier.
-- "(u : p) ∈ p" doesn't typecheck.



theorem bar {p : subset_of_vector_space F V} [hp : vector_space F p] : (0 : p) ∈ p := sorry

-- Wait, do we have the same + here?  Not neccesarily.  Hmm.
theorem foo {p : subset_of_vector_space F V} [hp : vector_space F p] : (0 : V) ∈ p :=
begin
  -- Prove that the zero vector of p is also a zero vector in V, then apply
  -- unique_add_ident.
  have  hhh : (0 : V) = (0 : p),
  { apply eq.symm,
    apply vector_space.unique_add_ident,
    intro v,
    sorry },
  simp [hhh]
end

end subset_of_vector_space 
end LADR
