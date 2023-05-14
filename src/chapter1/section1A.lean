-- This file is a translation of Linear Algebra Done Right, 3rd edition
-- (henceforth LADR) by Sheldon Alxer into Lean.  The goal is for the student
-- who is familiar with LADR, but less familiar with Lean, to see how various
-- definitions and theorems in the book are translated into canonical Lean.
--
-- This section contains two parts, the first on complex numbers, the second on
-- vectors.
--
-- Some of LADR's conventions clash with Lean's.  For example it uses λ as a
-- scalar variable, whereas Lean uses it to define anonymous functions.  Also,
-- LADR uses α as a complex variable, whereas Lean uses it as a type variable.
-- When these clashes occur, I follow the Lean convention, and so the choice of
-- variable in this file may differ from LADR's.

import data.real.basic
import algebra.field.basic


-- 1.1 Definition complex numbers
-- LADR defines it as an ordered pair; more appropriate in Lean is a structure,
-- and this is also how mathlib defines it.
structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

@[ext]
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
| ⟨zr, zi⟩ ⟨_, _⟩ rfl rfl := rfl

-- "The idea is to assume we have the square root of -1, denoted I."
@[simp] def I : ℂ := ⟨0, 1⟩

-- "If a ∈ ℝ, we identify a + 0I with the real number a.""
instance : has_coe ℝ ℂ := ⟨λ a, ⟨a, 0⟩⟩
-- These lemmas help the simplifier work with coerced real numbers.
@[simp, norm_cast] lemma of_real_re (r : ℝ) : (r : ℂ).re = r := rfl
@[simp, norm_cast] lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 := rfl

-- It can also help Lean to simplify expressions if we tell it about zero and
-- one.
instance : has_zero ℂ := ⟨(0 : ℝ)⟩
@[simp] lemma zero_re : (0 : ℂ).re = 0 := rfl
@[simp] lemma zero_im : (0 : ℂ).im = 0 := rfl

instance : has_one ℂ := ⟨(1 : ℝ)⟩
@[simp] lemma one_re : (1 : ℂ).re = 1 := rfl
@[simp] lemma one_im : (1 : ℂ).im = 0 := rfl


-- Define addition on ℂ in a way that lets use use '+' for it.
instance : has_add ℂ := ⟨λ z w, ⟨z.re + w.re, z.im + w.im⟩⟩
-- We need to repeat the definition so the simplifier will use it, and also so
-- we can refer to it by name, e.g. with `rw`.
@[simp] lemma add_re (z w : ℂ) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : ℂ) : (z + w).im = z.im + w.im := rfl

-- Define multiplication on ℂ in a way that lets use use '*' for it.
instance : has_mul ℂ := ⟨λ z w, ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩
-- We need to repeat the definition so the simplifier will use it, and also so
-- we can refer to it by name, e.g. with `rw`.
@[simp] lemma mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re := rfl

-- Using multiplication as defined above, we verify that I^2 = -1.
@[simp] lemma I_mul_I : I * I = (-1 : ℝ) := by {ext; simp}

-- In Lean, natural numbers aren't a subset of real numbers, but rather a
-- completely different set of objects.  So, the natuarl number 5 is different
-- than the real number 5.  When we write "5" without specifying the type, Lean
-- often interprets it as a natural number.  So, we provide a way to translate
-- natural number literals to complex numbers.

-- Providing these four definitions lets us work with examples containing natural
-- number literals.
@[simp] lemma bit0_re (z : ℂ) : (bit0 z).re = bit0 z.re := rfl
@[simp] lemma bit1_re (z : ℂ) : (bit1 z).re = bit1 z.re := rfl
@[simp] lemma bit0_im (z : ℂ) : (bit0 z).im = bit0 z.im := eq.refl _
@[simp] lemma bit1_im (z : ℂ) : (bit1 z).im = bit0 z.im := add_zero _


-- Example 1.2 "Evaluate (2 + 3 * I) * (4 + 5 * I)"
example : (2 + 3 * I) * (4 + 5 * I) = (-7 : ℝ) + 22 * I :=
calc
  (2 + 3 * I) * (4 + 5 * I)
      = 2 * 4 + 2 * (5 * I) + (3 * I) * 4 + (3 * I) * (5 * I) : by {ext; norm_num}
  ... = 8 + 10 * I + 12 * I + (-15 : ℝ) : by {ext; norm_num}
  ... = (-7 : ℝ) + 22 * I : by {ext; norm_num}


-- 1.3 Properties of complex arithmetic
variables z w v : ℂ

-- commutativity
theorem add_comm : z + w = w + z :=
  by {ext; simp [add_comm]}

-- 1.4 Example "Show that αβ = βα for all α, β ∈ ℂ"
theorem mul_comm : z * w = w * z :=
  by {ext; simp; ring }

-- associativity
theorem add_assoc : (z + w) + v = z + (w + v) :=
  by {ext; simp [add_assoc]}

theorem mul_assoc : (z * w) * v = z * (w * v) :=
  by {ext; simp; ring}

-- identities
theorem add_id : z + 0 = z := by {ext; simp}

theorem mul_id : z * 1 = z := by {ext; simp}


-- 1.5 -α, subtraction, 1/α, division

-- LADR takes an axiomatic approach, that is, it states that the additive
-- inverse is the complex number with given properties, then later derives a
-- formula for it.  Lean prefers us to instead define it in terms of the
-- formula, then prove the properties.

instance : has_neg ℂ := ⟨λ z, ⟨-z.re, -z.im⟩⟩
@[simp] lemma neg_re (z : ℂ) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : ℂ) : (-z).im = -z.im := rfl

instance : has_sub ℂ := ⟨λ z w, ⟨z.re - w.re, z.im - w.im⟩⟩
@[simp] lemma sub_re (z w : ℂ) : (z - w).re = z.re - w.re := rfl
@[simp] lemma sub_im (z w : ℂ) : (z - w).im = z.im - w.im := rfl

-- additive inverse
theorem add_inv : z + -z = 0 := by {ext; simp}


-- The formula for the multiplicative inverse uses the conjugate, which is why
-- we define it here before the inverse, whereas LADR doesn't even define it in
-- this section.
def conjugate : ℂ → ℂ := (λ z : ℂ, ⟨z.re, (-z.im)⟩)
@[simp] theorem conjugate_re (z : ℂ) : (conjugate z).re = z.re := rfl
@[simp] theorem conjugate_im (z : ℂ) : (conjugate z).im = -z.im := rfl

def norm_sq : ℂ → ℝ := (λ z, z.re * z.re + z.im * z.im)
@[simp] theorem norm_sq_def (z : ℂ) : norm_sq z = z.re * z.re + z.im * z.im := rfl

noncomputable instance : has_inv ℂ := ⟨λ z, conjugate z * ((norm_sq z)⁻¹:ℝ)⟩
theorem inv_def (z : ℂ) : z⁻¹ = (conjugate z) * ((norm_sq z)⁻¹:ℝ) := rfl
@[simp] lemma inv_re (z : ℂ) : (z⁻¹).re = z.re / norm_sq z := by simp [inv_def, division_def]
@[simp] lemma inv_im (z : ℂ) : (z⁻¹).im = -z.im / norm_sq z := by simp [inv_def, division_def]


-- To prove z * (z ⁻¹), we need the following theorems.
private theorem aux {x y : ℝ} (h : x * x + y * y = 0) : x = 0 :=
begin
  simp [← sq] at h,
  have h' : x^2 = 0,
  { apply le_antisymm _ (sq_nonneg x),
    rw ←h,
    apply le_add_of_nonneg_right (sq_nonneg y) },
  exact pow_eq_zero h'
end

theorem zero_of_norm_sq_zero :
  z.norm_sq = 0 → z = 0 :=
begin
  intro h,
  ext,
    { exact aux h },
    simp at h,
    rw add_comm_semigroup.add_comm at h,
    exact aux h
end

-- multiplicative inverse
theorem mul_inv (h: z ≠ 0) : z * (z ⁻¹) = 1 :=
begin
  ext,
  {
    simp [h],
    ring_nf,
    simp [← left_distrib, mul_inv],
    apply inv_mul_cancel,
    intro hsq,
    apply h,
    apply zero_of_norm_sq_zero,
    simp [← sq],
    exact hsq},
  simp [h],
  ring
end

-- distributive property
theorem distrib : v * (z + w) = v * z + v * w := by { ext; simp; ring }

end complex


-- 1.6 Notation F

namespace example_1_6
variables {F : Type*} [field F] (a b : F) (m n : ℕ)

example : (a^m)^n = a^(m*n) := (pow_mul a m n).symm

example : (a * b)^m = a ^ m * b ^ m := mul_pow a b m
end example_1_6

/-
   1.8 vector, length
   1.10 all vectors of a given length
   LADR calls them lists, but that has a different meaning in Lean, so we'll
   call them "vectors" instead.  We could also call them tuples.
 -/

universe u
-- A vector of length n
inductive vector (α : Type u) : ℕ → Type u
| nil {}                              : vector 0
| cons {n : ℕ} (a : α) (v : vector n) : vector (nat.succ n)

namespace vector
local notation (name := cons) h :: t := cons h t

-- 1.9 Example lists versus sets.
example : 3 :: 5 :: nil ≠ 5 :: 3 :: nil :=
begin
  intro h,
  have h' := (cons.inj h).1,
  linarith
end

variables {F : Type*} [field F]

example : ({3, 5} : set ℕ) = {5, 3} :=
begin
  ext n,
  simp,
  tauto
end

-- Note that these are different types, so even trying to write that they are
-- not equal produces a type error:
#check cons 4 (cons 4 (cons 4 nil))
#check cons 4 (cons 4 nil)

-- example : cons 4 (cons 4 (cons 4 nil)) ≠ cons 4 (cons 4 nil) := sorry

example : ({4, 4, 4} : set ℕ) = {4} := by simp

example : ({4, 4} : set ℕ) = {4} := by simp


-- 1.10
-- We denote F^n as vector F n.

-- 1.12  Definition  addition in F^n

-- This definition uses features that are more advanced than I would like, since
-- this conversion of LADR is intended for people new to Lean.  Is there a way
-- to simplify it?  I could try taking n out of the type signature.
-- This definition is inspired by section 8.7 of Theorem Proving in Lean, called
-- "Inaccessable Terms."
@[simp]
def add : Π { n : ℕ }, (vector F n) → (vector F n) → (vector F n)
| .(0)     nil           nil         := nil
| .(n + 1) (@cons .(F) n a₁ v₁) (cons a₂ v₂) := cons (a₁ + a₂) (add v₁ v₂)

variables {n : ℕ} (x y : vector F n)

instance : has_add (vector F n) := ⟨λ x y, add x y⟩
@[simp] lemma plus_eq_add {x y : vector F n} : x + y = add x y := rfl


example : ((2: ℝ) :: 3 :: nil) + (5 :: 7 :: nil) = (7 :: 10 :: nil) :=
begin
  simp,
  norm_num
end


-- 1.13  Commutativity of addition in F^n

theorem vector_add_comm : x + y = y + x :=
begin
  -- Whenever you see ... in math, the proof in Lean is generally by induction
  -- on the length of the ... list.
  induction n with n ih,
  { cases x,
    cases y,
    refl},
  cases x,
  cases y,
  simp,
  split,
  { apply add_comm },
  apply ih
end

-- 1.14  Definition 0

@[simp]
def zero : ∀ n : ℕ, vector F n
| 0 := nil
| (n + 1) := (0 : F) :: (zero n)

instance : has_zero (vector F n) := ⟨zero n⟩

example : vector.zero 2 = (0:F) :: (0:F) :: nil := rfl

variable v : vector F n

theorem add_zero : ∀ v : vector F n, v + (zero n) = v :=
begin
  intros v,
  induction n with n ih,
  { cases v,
    dsimp,
    refl },
  cases v with _ a v_n,
  simp,
  exact ih v_n
end

theorem zero_add : ∀ v : vector F n, (zero n) + v = v :=
begin
  intros v,
  rw vector_add_comm,
  exact add_zero v
end

-- 1.16  Definition  additive inverse in F^n

-- As with zero, we use recursion when Axler uses ...

-- Would like to make n implicit, how do we split on cases of an implicit
-- argument?
@[simp]
def neg : ∀ (n : ℕ) (v : vector F n), vector F n
| 0 nil := nil 
| (n + 1) (a :: v) := (-a :: neg n v)

instance : has_neg (vector F n) := ⟨ neg n ⟩
@[simp] lemma neg_neg {v : vector F n} : -v = neg n v := rfl

theorem add_neg : v + (- v) = zero n :=
begin
  induction n with n ih,
  { cases v with n a v_n,
    dsimp,
    refl },
  cases v with n a v_n,
  simp,
  exact ih v_n
end

theorem neg_add : (- v) + v = zero n :=
begin
  rw vector_add_comm,
  exact add_neg v
end

def mysmul : ∀ (n : ℕ) (a : F) (v : vector F n), vector F n
| 0       a nil      := nil
| (n + 1) a (h :: v) := a * h :: (mysmul n a v)

instance : has_smul F (vector F n) := ⟨ mysmul n ⟩
@[simp] lemma smul_mymul {a : F} : a • v = mysmul n a v := rfl

end vector
