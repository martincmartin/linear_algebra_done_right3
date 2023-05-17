-- This file is a translation of Linear Algebra Done Right, 3rd edition
-- (henceforth LADR) by Sheldon Alxer into Lean.  The goal is for the student
-- who is familiar with LADR, but less familiar with Lean, to see how various
-- definitions and theorems in the book are translated into canonical Lean.
--
-- This section contains two parts, the first on complex numbers, the second on
-- tuples.
--
-- Some of LADR's conventions clash with Lean's.  For example it uses λ as a
-- scalar variable, whereas Lean uses it to define anonymous functions.  Also,
-- LADR uses α as a complex variable, whereas Lean uses it as a type variable.
-- When these clashes occur, I follow the Lean convention, and so the choice of
-- variable in this file may differ from LADR's.

import data.real.basic
import algebra.field.basic
import init.data.fin.basic

import data.fin.vec_notation

import tactic


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
  1.8  Definition  tuple, length
  1.10 all tuples of a given length
  LADR calls them lists, but that has a different meaning in Lean.  LADR says
  "Many mathematicians call a list of length n an n-tuple", so we'll call them
  "tuples".
 -/

-- A tuple of length n
-- `fin n` is the subtype of `ℕ` consisting of natural numbers strictly smaller
-- than `n`.
@[reducible]
def tuple (α : Type*) (n : ℕ) := fin n → α

namespace tuple


-- 1.9 Example lists versus sets.

example : ( ![3, 5] : tuple ℕ 2) ≠ (![5, 3] : tuple ℕ 2) :=
begin
  rw function.ne_iff,
  use 0,
  simp
end

example : ({3, 5} : set ℕ) = {5, 3} :=
begin
  ext n,
  simp,
  tauto
end

-- Note that these are different types, so even trying to write that they are
-- not equal produces a type error:
#check ![4, 4, 4]
#check ![4, 4]


example : ({4, 4, 4} : set ℕ) = {4} := by simp

example : ({4, 4} : set ℕ) = {4} := by simp

variables {F : Type*} [field F]


-- 1.10
-- We denote F^n as tuple F n.

-- 1.12  Definition  addition in F^n

variables {n : ℕ} (x y : tuple F n)

instance : has_add (tuple F n) := ⟨λ x y i, x i + y i⟩
@[simp] lemma plus_eq_add : x + y = λ i, x i + y i := rfl


example : ![2, 3] + ![5, 7] = ![7, 10] := by simp


-- 1.13  Commutativity of addition in F^n

theorem tuple_add_comm : x + y = y + x :=
begin
  funext,
  simp,
  apply add_comm
end

-- 1.14  Definition 0

instance : has_zero (tuple F n) := ⟨λ i, 0⟩
@[simp] theorem zero_zero : (0 : tuple F n) = λ i, 0 := rfl

example : 0 = ![(0:ℝ), 0] :=
begin
  funext,
  cases i with val property,
  interval_cases val,
  { simp },
  simp
end

variable v : tuple F n


theorem add_zero : v + 0 = v := by simp

theorem zero_add : 0 + v = v := by simp


-- 1.16  Definition  additive inverse in F^n

instance : has_neg (tuple F n) := ⟨ λ v i, - v i⟩
@[simp] lemma neg_neg {v : tuple F n} : -v = λ i, - v i := rfl

theorem add_neg : v + (- v) = 0 := by simp

theorem neg_add : (- v) + v = 0 := by simp

instance : has_smul F (tuple F n) := ⟨ λ a v i, a * v i ⟩
@[simp] lemma smul_mul {a : F} : a • v = λ i, a * v i := rfl

end tuple
