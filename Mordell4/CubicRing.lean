import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Algebra.Order.Monoid.Lemmas



#align_import cubic_ring

open scoped Classical

--set_option profiler true
--We will be considering cubic integers of the form `x+y*θ+z*(θ^2)`, where θ is the
--only real root of the cuic equation f(x) = x^3 + 3*(x^2) + 6*x + 2.
--and `x y z : ℤ`. We shall write `ℤθ` for the Type of these integers,
--and represent them by their f- , g- and h-coordinates.
@[ext]
structure ℤθ : Type where
  f : ℤ
  g : ℤ
  h : ℤ

namespace ℤθ

-- instance : has_coe ℤ ℤθ := ⟨λ x, ⟨x,0,0⟩⟩
--We give lean a method for checking whether two such integers are equal.
noncomputable instance decEq : DecidableEq ℤθ :=
  inferInstance

-- NOTE : proof copied from quad ring, will need modification
-- λ a b,
-- begin
--   cases a with r s,
--   cases b with t u,
--   have : decidable (r=t ∧ s=u),
--   {
--     exact and.decidable,
--   },
--   apply decidable_of_decidable_of_iff this,
--   tidy,
-- end
--We give lean a way of displaying elements of `ℤθ` using the command `#eval`.
--TO DO : rewrite this using pattern matching.
def repr (a : ℤθ) : String := by
  by_cases a.f = 0
  · by_cases a.g = 0
    · by_cases a.h = 0
      · exact "0"
      · exact a.h.repr ++ " * θ^2"
    · by_cases a.h = 0
      · exact a.g.repr ++ " * θ"
      · by_cases a.h > 0
        · exact a.g.repr ++ " * θ" ++ " + " ++ a.h.repr ++ " * θ^2"
        · exact a.g.repr ++ " * θ" ++ " - " ++ (-a.h).repr ++ " * θ^2"
  · by_cases a.g = 0
    · by_cases a.h = 0
      · exact a.f.repr
      · by_cases a.h > 0
        · exact a.f.repr ++ " + " ++ a.h.repr ++ " * θ^2"
        · exact a.f.repr ++ " - " ++ (-a.h).repr ++ " * θ^2"
    · by_cases a.h = 0
      · by_cases a.g > 0
        · exact a.f.repr ++ " + " ++ a.g.repr ++ " * θ"
        · exact a.f.repr ++ " - " ++ (-a.g).repr ++ " * θ"
      · by_cases a.g > 0
        · by_cases a.h > 0
          · exact a.f.repr ++ " + " ++ a.g.repr ++ " * θ" ++ " + " ++ a.h.repr ++ " * θ^2"
          · exact a.f.repr ++ " + " ++ a.g.repr ++ " * θ" ++ " - " ++ (-a.h).repr ++ " * θ^2"
        · by_cases a.h > 0
          · exact a.f.repr ++ " - " ++ (-a.g).repr ++ " * θ" ++ " + " ++ a.h.repr ++ " * θ^2"
          · exact a.f.repr ++ " - " ++ (-a.g).repr ++ " * θ" ++ " - " ++ (-a.h).repr ++ " * θ^2"

instance ℤθRepr : Repr ℤθ where
 reprPrec := fun  a  _  => repr a

#eval (⟨0, -9, -1⟩ : ℤθ)

/-- Defining addition, multiplication and other things needed for rings-/
def zero : ℤθ :=
  ⟨0, 0, 0⟩

def one : ℤθ :=
  ⟨1, 0, 0⟩

def θ : ℤθ :=
  ⟨0, 1, 0⟩

def θSq : ℤθ :=
  ⟨0, 0, 1⟩

def add : ℤθ → ℤθ → ℤθ := fun a b => ⟨a.f + b.f, a.g + b.g, a.h + b.h⟩

def neg : ℤθ → ℤθ := fun a => ⟨-a.f, -a.g, -a.h⟩

/-- Using the fact that θ^3 + 3*(θ^2) + 6*θ + 2 = 0, we obtain the rule for multiplication-/
def mul : ℤθ → ℤθ → ℤθ := fun a b =>
  ⟨a.f * b.f + 6 * a.h * b.h - 2 * a.g * b.h - 2 * a.h * b.g,
    a.f * b.g + a.g * b.f + 16 * a.h * b.h - 6 * a.g * b.h - 6 * a.h * b.g,
    a.f * b.h + a.h * b.f + a.g * b.g + 3 * a.h * b.h - 3 * a.g * b.h - 3 * a.h * b.g⟩

variable (a b c : ℤθ)

theorem my_add_assoc : add (add a b) c = add a (add b c) :=
  by
  cases a; cases b; cases c
  simp only [add, add_assoc]


theorem my_zero_add : add zero a = a := by
  cases' a with x y
  simp only [add, zero, zero_add]

theorem my_add_zero : add a zero = a := by
  cases' a with x y
  simp only [add, zero, add_zero]

theorem my_add_left_neg : add (neg a) a = zero :=
  by
  cases a
  simp only [neg, add]
  --NOTE TO SELF: these two lines cannot be merged. Why not ????
  simp only [add_left_neg]
  tauto

theorem my_add_comm : add a b = add b a := by
  cases a; cases b
  simp only [add, add_comm]

theorem my_mul_assoc : mul (mul a b) c = mul a (mul b c) :=
  by
  cases a; cases b; cases c
  simp only [mul]
  ring


theorem my_zero_mul : mul zero a = zero := by
  cases a
  simp [mul, zero]


theorem my_mul_zero : mul a zero = zero := by
  cases a
  simp [mul, zero]


theorem my_one_mul : mul one a = a := by
  cases a
  simp [mul, one]

theorem my_mul_one : mul a one = a := by
  cases a
  simp [mul, one]

theorem my_left_distrib : mul a (add b c) = add (mul a b) (mul a c) :=
  by
  cases a; cases b; cases c
  simp only [mul, add]
  ring

theorem my_right_distrib : mul (add a b) c = add (mul a c) (mul b c) :=
  by
  cases a; cases b; cases c
  simp only [mul, add]
  ring

theorem my_mul_comm : mul a b = mul b a := by
  cases a; cases b
  simp only [mul]
  ring

def zsmul : ℤ → ℤθ → ℤθ := fun n a => ⟨n * a.f, n * a.g, n * a.h⟩

theorem my_zsmul_zero' : ∀ a : ℤθ, zsmul (0 : ℤ) a = zero :=
  by
  intro a
  unfold zsmul
  rw [MulZeroClass.zero_mul]
  rw [MulZeroClass.zero_mul]
  rw [MulZeroClass.zero_mul]
  rw [← zero]

theorem my_zsmul_succ' :
    ∀ (n : ℕ) (a : ℤθ), zsmul (Int.ofNat n.succ) a = a.add (zsmul (Int.ofNat n) a) :=
  by
  intro n a
  change
    (⟨Int.ofNat n.succ * a.f, Int.ofNat n.succ * a.g, Int.ofNat n.succ * a.h⟩ : ℤθ) =
      (⟨a.f + Int.ofNat n * a.f, a.g + Int.ofNat n * a.g, a.h + Int.ofNat n * a.h⟩ : ℤθ)
  norm_num
  constructor
  linarith
  constructor
  linarith; linarith

theorem my_zsmul_neg' : ∀ (n : ℕ) (a : ℤθ), zsmul (Int.negSucc n) a = (zsmul (↑n.succ) a).neg :=
  by
  intro n a
  simp
  change
    (⟨Int.negSucc n * a.f, Int.negSucc n * a.g, Int.negSucc n * a.h⟩ : ℤθ) =
      (⟨-(Int.ofNat n.succ * a.f), -(Int.ofNat n.succ * a.g), -(Int.ofNat n.succ * a.h)⟩ : ℤθ)
  simp
  constructor
  rw [Int.negSucc_coe]
  rw [Int.neg_mul_eq_neg_mul_symm]
  rw [Int.ofNat_add]
  rw [Int.ofNat_one]
  constructor
  rw [Int.negSucc_coe]
  rw [Int.neg_mul_eq_neg_mul_symm]
  rw [Int.ofNat_add]
  rw [Int.ofNat_one]
  rw [Int.negSucc_coe]
  rw [Int.neg_mul_eq_neg_mul_symm]
  rw [Int.ofNat_add]
  rw [Int.ofNat_one]

def intCast : ℤ → ℤθ := fun a => ⟨a, 0, 0⟩

def natCast : ℕ → ℤθ := fun a => ⟨a, 0, 0⟩

theorem my_natCast_zero : natCast 0 = zero := by rfl

theorem my_natCast_succ : ∀ n : ℕ, natCast (n + 1) = (natCast n).add one :=
  by
  intro n
  change (⟨Int.ofNat (n + 1), 0, 0⟩ : ℤθ) = (⟨Int.ofNat n + 1, 0, 0⟩ : ℤθ)
  simp

theorem my_intCast_of_nat : ∀ n : ℕ, intCast ↑n = natCast n :=
  by
  intro n
  rfl

theorem my_intCast_neg_succ_of_nat : ∀ n : ℕ, intCast (-↑(n + 1)) = (natCast (n + 1)).neg :=
  by
  intro n
  rfl

/-- Making ℤθ into a ring-/
instance isRing : CommRing ℤθ where
  zero := zero
  neg := neg
  add := add
  one := one
  mul := mul
  zero_mul := my_zero_mul
  mul_zero := my_mul_zero
  add_assoc := my_add_assoc
  zero_add := my_zero_add
  add_zero := my_add_zero
  add_left_neg := my_add_left_neg
  add_comm := my_add_comm
  mul_assoc := my_mul_assoc
  one_mul := my_one_mul
  mul_one := my_mul_one
  left_distrib := my_left_distrib
  right_distrib := my_right_distrib
  mul_comm := my_mul_comm
  zsmul := zsmul
  zsmul_zero' := my_zsmul_zero'
  zsmul_succ' := my_zsmul_succ'
  zsmul_neg' := my_zsmul_neg'
  intCast := intCast
  natCast := natCast
  natCast_zero := my_natCast_zero
  natCast_succ := my_natCast_succ
  intCast_ofNat := my_intCast_of_nat
  intCast_negSucc := my_intCast_neg_succ_of_nat

#eval θ ^ 3

#eval θ ^ 4

#eval (25 + 13 * θ + 5 * θ ^ 2) ^ 3

#eval (-1 - 3 * θ - θ ^ 2) ^ 3

#eval (-1 - 3 * θ - θ ^ 2) ^ 6

#eval (-1 - 3 * θ - θ ^ 2) ^ 9

def norm : ℤθ → ℤ := fun k =>
  |k.f ^ 3 - 2 * k.g ^ 3 + 4 * k.h ^ 3 - 3 * k.f ^ 2 * k.g - 3 * k.f ^ 2 * k.h + 6 * k.f * k.g ^ 2 +
            6 * k.g ^ 2 * k.h +
          24 * k.f * k.h ^ 2 -
        12 * k.g * k.h ^ 2 -
      12 * k.f * k.g * k.h|
@[reducible]
def unit : ℤθˣ :=
  ⟨-1 - 3 * θ - θ ^ 2, 25 + 13 * θ + 5 * θ ^ 2, by ext <;> decide, by ext <;> decide⟩

theorem unit_l : (unit : ℤθ) = ⟨-1, -3, -1⟩ := by rfl

theorem unit_neg_1 : ((unit ^ (-(1 : ℤ)) : ℤθˣ) : ℤθ) = ⟨25, 13, 5⟩ := by rfl

theorem simp_norm (a b : ℤ) :
    norm (⟨a, -b, 0⟩ : ℤθ) = |a ^ 3 + 3 * a ^ 2 * b + 6 * a * b ^ 2 + 2 * b ^ 3| :=
  by
  unfold norm
  ring_nf

theorem hMul_mule_3 (a b : ℤθ) :
    a * b =
      (⟨a.f * b.f + 6 * a.h * b.h - 2 * a.g * b.h - 2 * a.h * b.g,
          a.f * b.g + a.g * b.f + 16 * a.h * b.h - 6 * a.g * b.h - 6 * a.h * b.g,
          a.f * b.h + a.h * b.f + a.g * b.g + 3 * a.h * b.h - 3 * a.g * b.h - 3 * a.h * b.g⟩ :
        ℤθ) :=
  by rfl
set_option maxHeartbeats 1000000

theorem norm_hMul (r s : ℤθ) : norm r * norm s = norm (r * s) :=
by
  rw [norm,norm,norm,hMul_mule_3 r s,← abs_mul]
  ring_nf

theorem norm_divides {p a : ℤθ} (h : p ∣ a) : norm p ∣ norm a :=
  by
  cases' h with n hn
  use norm n
  rw [norm_hMul p n]
  rw [hn]

theorem norm_one_if_unit (k : ℤθ) : IsUnit k → norm k = 1 :=
 by
  intro h
  rw [isUnit_iff_exists_inv] at h
  have p : ∃ b : ℤθ, 1 = k * b := by tauto
  change k ∣ 1 at p
  have l := norm_divides p
  have d : norm 1 = 1 := by ring
  rw [d] at l
  refine' Int.eq_one_of_dvd_one _ l
  exact abs_nonneg _

--this is to be left for later. This is the hardest part of the proof.
theorem units_are (a : ℤθˣ) : ∃ n : ℤ, a = unit ^ n ∨ a = -unit ^ n := by sorry

--The usual maths definition for y % 3 = s
theorem y_mod_three (y : ℤ) (s : ℤ) (h : y % 3 = s) : ∃ k : ℤ, y = 3 * k + s :=
  by
  have q := Int.dvd_sub_of_emod_eq h
  cases' q with l lh
  use l
  exact eq_add_of_sub_eq lh

theorem unit_sq : ((unit ^ 2 : ℤθˣ) : ℤθ) = ⟨-5, -14, -4⟩ :=
  by
  rw [pow_two]
  have h1 : ((unit * unit : ℤθˣ) : ℤθ) = ((unit : ℤθˣ) : ℤθ) * ((unit : ℤθˣ) : ℤθ) := by rfl
  rw [h1]
  rw [unit_l]
  rw [hMul_mule_3]; dsimp; norm_num

theorem unit_cubed : (unit : ℤθ) ^ 3 = ⟨-23, -63, -15⟩ :=
  by
  rw [unit_l, pow_three, hMul_mule_3]
  norm_num

theorem unit_inv_cubed : ((unit ^ (-3 : ℤ) : ℤθˣ) : ℤθ) = ⟨10591, 5553, 2139⟩ :=
by
  norm_cast

theorem unit_pow_zero :
    ((unit ^ (3 * 0) : ℤθˣ) : ℤθ).f % 3 = 1 ∧
      ((unit ^ (3 * 0) : ℤθˣ) : ℤθ).g % 3 = 0 ∧ ((unit ^ (3 * 0) : ℤθˣ) : ℤθ).h % 3 = 0 :=
  by
    norm_cast

theorem unit_pow_one :
    ((unit ^ 1 : ℤθˣ) : ℤθ).f % 3 = 2 ∧
      ((unit ^ 1 : ℤθˣ) : ℤθ).g % 3 = 0 ∧ ((unit ^ 1 : ℤθˣ) : ℤθ).h % 3 = 2 :=
by
  norm_cast


theorem unit_pow_zero_mod_three :
    ∀ k : ℕ,
      (((unit ^ (3 * (k : ℤ)) : ℤθˣ) : ℤθ).f % 3 = 1 ∧
          ((unit ^ (3 * (k : ℤ)) : ℤθˣ) : ℤθ).g % 3 = 0 ∧
            ((unit ^ (3 * (k : ℤ)) : ℤθˣ) : ℤθ).h % 3 = 0) ∧
        ((unit ^ (3 * -(k : ℤ)) : ℤθˣ) : ℤθ).f % 3 = 1 ∧
          ((unit ^ (3 * -(k : ℤ)) : ℤθˣ) : ℤθ).g % 3 = 0 ∧
            ((unit ^ (3 * -(k : ℤ)) : ℤθˣ) : ℤθ).h % 3 = 0 :=
  by
  intro k
  constructor
  · induction' k with b hb
    · exact unit_pow_zero
    cases' hb with h1 h23
    cases' h23 with h2 h3
    have p : b.succ = b + 1 := by rfl
    rw [p]
    norm_cast
    have w : (unit ^ (3 * (b + 1)) : ℤθ) = (unit ^ (3 * b) : ℤθ) * ((unit:ℤθ) ^ 3 : ℤθ) :=
    by
      norm_cast
      rw [mul_add, mul_one, pow_add]
    have t1 : ((unit ) ^ (3 * b):ℤθ).f % 3 = 1 :=
      by
        norm_cast
    have t2 : ((unit) ^ (3 * b) : ℤθ).g % 3 = 0 :=
      by
        norm_cast
    have t3 : ((unit ) ^ (3 * b): ℤθ).h % 3 = 0 :=
      by
        norm_cast
    have r1 := y_mod_three (unit ^ (3 * b) : ℤθ).f 1 t1
    cases' r1 with c1 hc1
    have r2 := y_mod_three (unit ^ (3 * b) : ℤθ).g 0 t2
    cases' r2 with c2 hc2
    rw [add_zero] at hc2
    have r3 := y_mod_three (unit ^ (3 * b) : ℤθ).h 0 t3
    cases' r3 with c3 hc3
    rw [add_zero] at hc3
    have s : (unit ^ (3 * b) : ℤθ) = ⟨3 * c1 + 1, 3 * c2, 3 * c3⟩ :=
      by
      ext <;> dsimp
      exact hc1; exact hc2; exact hc3
    -- just the same as w?
    -- have s1 : (unit ^ (3 * (b + 1)) : ℤθ) = (unit ^ (3 * b) : ℤθ) * ((unit:ℤθ) ^ 3 : ℤθ) :=
    -- by
    --   norm_cast
    --   rw [← pow_add]
    --   rw [mul_add, mul_one]
    rw [s] at w ; rw [unit_cubed] at w
    rw [hMul_mule_3] at w ; dsimp at w ; ring_nf at w
    rw [ℤθ.ext_iff] at w ;
    dsimp at w
--    norm_cast at w
    have : 3 + b*3 = 3*(b+1):= by ring
    rw [this] at w
    obtain ⟨f1,f2,f3⟩:=w
    apply_fun (fun x => x%3) at f1 f2 f3
    rw [f1,f2,f3]
    constructor
    · rw [Int.add_emod,Int.add_emod _ (c3*108),Int.sub_emod, Int.mul_emod _ 69,Int.mul_emod _ 108,Int.mul_emod _ 90];
      have : (69:ℤ) %3 = 0:=by norm_num
      rw [this]
      have : (108:ℤ) %3 = 0:=by norm_num
      rw [this]
      have : (90:ℤ) %3 = 0:=by norm_num
      rw [this]
      norm_num


    · constructor
      · rw [Int.add_emod,Int.add_emod _ (c3*414),Int.sub_emod, Int.mul_emod _ 189,Int.mul_emod _ 414,Int.mul_emod _ 201]
        have : (189:ℤ) %3 = 0:=by norm_num
        rw [this]
        have : (414:ℤ) %3 = 0:=by norm_num
        rw [this]
        have : (201:ℤ) %3 = 0:=by norm_num
        rw [this]; norm_num
      · rw [Int.add_emod,Int.sub_emod,Int.sub_emod (c3*363), Int.mul_emod _ 363,Int.mul_emod _ 54,Int.mul_emod _ 45]
        have : (45:ℤ) %3 = 0:=by norm_num
        rw [this]
        have : (363:ℤ) %3 = 0:=by norm_num
        rw [this]
        have : (54:ℤ) %3 = 0:=by norm_num
        rw [this]; norm_num

    -- constructor
    -- ·
    --   norm_num
    --   rw [Int.add_emod]; --rw [← neg_mul];
    --   rw [Int.mul_emod]
    --   norm_num
    --   rw [Int.add_emod]; rw [Int.mul_emod]
    --   norm_num
    --   rw [Int.sub_emod]; rw [Int.mul_emod]
    --   norm_num
    -- constructor
    -- · norm_num
    --   use-(63 * c1) + (138 * c3 + (67 * c2 - 21))
    --   ring_nf
    -- · norm_num
    --   use-(15 * c1) + (121 * c3 + (-(18 * c2) - 5))
    --   ring_nf

  · induction' k with b hb
    · rw [Int.ofNat_zero, neg_zero, MulZeroClass.mul_zero]
      exact unit_pow_zero
    cases' hb with h1 h23
    cases' h23 with h2 h3
    have p : b.succ = b + 1 := by rfl
    rw [p]
    -- why is it auto repeating?
    --why this notation?
    have w :
      ((unit ^ ((3 : ℤ) * -(b + 1 : ℤ)) : ℤθˣ) : ℤθ) =
        ((unit ^ (3 * -(b : ℤ)) : ℤθˣ) : ℤθ) * ((unit ^ (-3 : ℤ) : ℤθˣ) : ℤθ) :=
      by
      rw [neg_add, mul_add, mul_neg_one, zpow_add]
      norm_cast
    have r1 := y_mod_three ((unit ^ ((3 : ℤ) * -(b : ℤ)) : ℤθˣ) : ℤθ).f 1 h1
    cases' r1 with c1 hc1
    have r2 := y_mod_three ((unit ^ ((3 : ℤ) * -(b : ℤ)) : ℤθˣ) : ℤθ).g 0 h2
    cases' r2 with c2 hc2
    rw [add_zero] at hc2
    have r3 := y_mod_three ((unit ^ ((3 : ℤ) * -(b : ℤ)) : ℤθˣ) : ℤθ).h 0 h3
    cases' r3 with c3 hc3
    rw [add_zero] at hc3
    have s : ((unit ^ ((3 : ℤ) * -(b : ℤ)) : ℤθˣ) : ℤθ) = ⟨3 * c1 + 1, 3 * c2, 3 * c3⟩ :=
      by
      ext <;> dsimp
      exact hc1; exact hc2; exact hc3
    rw [s] at w ; rw [unit_inv_cubed] at w
    rw [hMul_mule_3] at w ; dsimp at w ; ring_nf at w
    rw [ℤθ.ext_iff] at w ; dsimp at w
    cases' w with w1 w23
    cases' w23 with w2 w3
    have j2: -3 - (b : ℤ)*3 = 3*(-(b+1):ℤ):= by ring

    -- have j : -(3 * (b : ℤ)) - 3 = 3 * -(b + 1 : ℤ) :=
    --   by ring
    have j1 : (b : ℤ) + 1 = ((b + 1 : ℕ) : ℤ) := by norm_cast
    rw [j1] at j2
    rw [j2] at w1 ; rw [j2] at w2 ; rw [j2] at w3
    rw [w1, w2, w3]
    clear h1 h2 h3 p hc1 hc2 hc3 w1 w2 w3 s j2 j1
    constructor
    · rw [Int.add_emod ,Int.add_emod 10591, Int.sub_emod]; rw [Int.mul_emod c1];
      rw [Int.mul_emod c3,Int.mul_emod c2];
      have : (10591:ℤ) %3 = 1 :=by norm_num
      rw [this]
      have : (31773:ℤ) %3 =0 :=by norm_num
      rw [this]
      have : (5184:ℤ) %3 =0 :=by norm_num
      rw [this]
      have : (12834:ℤ) %3 =0 :=by norm_num
      rw [this]; norm_num
    constructor
    · norm_num
      use 5553 * c1 + (906 * c3 + (-(2243 * c2) + 1851))
      ring_nf
    · norm_num
      use 2139 * c1 + (349 * c3 + (-(864 * c2) + 713))
      ring_nf

theorem unit_zpow_zero_mod_three :
    ∀ k : ℤ,
      ((unit ^ (3 * k) : ℤθˣ) : ℤθ).f % 3 = 1 ∧
        ((unit ^ (3 * k) : ℤθˣ) : ℤθ).g % 3 = 0 ∧ ((unit ^ (3 * k) : ℤθˣ) : ℤθ).h % 3 = 0 :=
  by
  intro q
  have h := lt_or_le 0 q
  have p := unit_pow_zero_mod_three
  cases' h with h1 h2
  · specialize p (Int.toNat q)
    cases' p with p1 p2
    rw [Int.toNat_of_nonneg (le_of_lt h1)] at p1
    exact p1
  specialize p (Int.toNat (-q))
  cases' p with p1 p2
  have r := neg_le_neg h2
  rw [neg_zero] at r
  rw [Int.toNat_of_nonneg r] at p2
  rw [neg_neg] at p2
  exact p2

theorem unit_zpow_one_mod_three :
    ∀ k : ℤ,
      ((unit ^ (3 * k + 1) : ℤθˣ) : ℤθ).f % 3 = 2 ∧
        ((unit ^ (3 * k + 1) : ℤθˣ) : ℤθ).g % 3 = 0 ∧ ((unit ^ (3 * k + 1) : ℤθˣ) : ℤθ).h % 3 = 2 :=
  by
  intro k
  have w :
    ((unit ^ (3 * k + 1) : ℤθˣ) : ℤθ) = ((unit ^ (3 * k) : ℤθˣ) : ℤθ) * ((unit ^ 1 : ℤθˣ) : ℤθ) :=
    by
    rw [zpow_add]
    norm_cast
  have g := unit_zpow_zero_mod_three
  specialize g k
  cases' g with g1 g23
  cases' g23 with g2 g3
  have t1 := y_mod_three ((unit ^ (3 * k) : ℤθˣ) : ℤθ).f 1 g1
  cases' t1 with j1 hj1
  have t2 := y_mod_three ((unit ^ (3 * k) : ℤθˣ) : ℤθ).g 0 g2
  cases' t2 with j2 hj2
  rw [add_zero] at hj2
  have t3 := y_mod_three ((unit ^ (3 * k) : ℤθˣ) : ℤθ).h 0 g3
  cases' t3 with j3 hj3
  rw [add_zero] at hj3
  have s : ((unit ^ (3 * k) : ℤθˣ) : ℤθ) = ⟨3 * j1 + 1, 3 * j2, 3 * j3⟩ :=
    by
    ext <;> dsimp
    exact hj1; exact hj2; exact hj3
  clear g1 g2 g3 hj1 hj2 hj3
  rw [s] at w ; rw [pow_one] at w ; rw [unit_l] at w
  rw [hMul_mule_3] at w ; dsimp at w ; ring_nf at w
  rw [ℤθ.ext_iff] at w
  dsimp at w
  cases' w with w1 w23
  cases' w23 with w2 w3
  rw [add_comm, mul_comm, w1, w2, w3]
  constructor
  · rw [Int.add_emod,Int.sub_emod, Int.mul_emod j1,Int.mul_emod j2];
    norm_num
    have : (6 : ℤ)%3 = 0:=by norm_num
    rw [this]; norm_num
  constructor
  · rw [Int.add_emod,Int.add_emod _ (j3*6),Int.sub_emod,Int.mul_emod j1,Int.mul_emod j2,Int.mul_emod j3];
    have : (6 : ℤ)%3 = 0:=by norm_num
    rw [this]
    have : (9 : ℤ)%3 = 0:=by norm_num
    rw [this]
    have : (15 : ℤ)%3 = 0:=by norm_num
    rw [this]
    norm_num
  rw [Int.add_emod,Int.sub_emod,Int.mul_emod j1,Int.mul_emod j3];
  have : (3 : ℤ)%3 = 0:=by norm_num
  rw [this]
  have : (15 : ℤ)%3 = 0:=by norm_num
  rw [this]
  norm_num

theorem unit_zpow_two_mod_three :
    ∀ k : ℤ,
      ((unit ^ (3 * k + 2) : ℤθˣ) : ℤθ).f % 3 = 1 ∧
        ((unit ^ (3 * k + 2) : ℤθˣ) : ℤθ).g % 3 = 1 ∧ ((unit ^ (3 * k + 2) : ℤθˣ) : ℤθ).h % 3 = 2 :=
by
  intro k
  have w :
    ((unit ^ (3 * k + 2) : ℤθˣ) : ℤθ) = ((unit ^ (3 * k) : ℤθˣ) : ℤθ) * ((unit ^ 2 : ℤθˣ) : ℤθ) :=
    by
    rw [zpow_add]
    norm_cast
  have g := unit_zpow_zero_mod_three
  specialize g k
  cases' g with g1 g23
  cases' g23 with g2 g3
  have t1 := y_mod_three ((unit ^ (3 * k) : ℤθˣ) : ℤθ).f 1 g1
  cases' t1 with j1 hj1
  have t2 := y_mod_three ((unit ^ (3 * k) : ℤθˣ) : ℤθ).g 0 g2
  cases' t2 with j2 hj2
  rw [add_zero] at hj2
  have t3 := y_mod_three ((unit ^ (3 * k) : ℤθˣ) : ℤθ).h 0 g3
  cases' t3 with j3 hj3
  rw [add_zero] at hj3
  have s : ((unit ^ (3 * k) : ℤθˣ) : ℤθ) = ⟨3 * j1 + 1, 3 * j2, 3 * j3⟩ :=
    by
    ext <;> dsimp
    exact hj1; exact hj2; exact hj3
  clear g1 g2 g3 hj1 hj2 hj3
  rw [s] at w ; rw [unit_sq] at w
  rw [hMul_mule_3] at w ; dsimp at w ; ring_nf at w
  rw [ℤθ.ext_iff] at w
  dsimp at w
  cases' w with w1 w23
  cases' w23 with w2 w3
  rw [add_comm 2,mul_comm k] at w1 w2 w3
  rw [w1, w2, w3]
  constructor
  · rw [Int.add_emod,Int.add_emod _ (j3*12),Int.sub_emod,Int.mul_emod j1,Int.mul_emod j2,Int.mul_emod j3];
    have : (15:ℤ) %3 =0 :=by norm_num
    rw [this]
    have : (12:ℤ) %3 =0 :=by norm_num
    rw [this]
    have : (24:ℤ) %3 =0 :=by norm_num
    rw [this]; norm_num
  constructor
  · rw [Int.add_emod,Int.add_emod _ (j3*60),Int.sub_emod,Int.mul_emod j1,Int.mul_emod j2,Int.mul_emod j3];
    have : (42:ℤ) %3 =0 :=by norm_num
    rw [this]
    have : (60:ℤ) %3 =0 :=by norm_num
    rw [this]
    have : (57:ℤ) %3 =0 :=by norm_num
    rw [this]; norm_num
  · rw [Int.add_emod, Int.sub_emod,Int.sub_emod (j3*75),Int.mul_emod j1,Int.mul_emod j2,Int.mul_emod j3];
    have : (12:ℤ) %3 =0 :=by norm_num
    rw [this]
    have : (75:ℤ) %3 =0 :=by norm_num
    rw [this]
    have : (6:ℤ) %3 =0 :=by norm_num
    rw [this]; norm_num


--the below should definitely be simplified!
theorem hMul_three_pow_dvd (n : ℕ) (j : 1 ≤ n) : ∃ a : ℕ, 3 ^ a ∣ 3 * n ∧ ¬3 ^ (a + 1) ∣ 3 * n :=
  by
  by_contra h
  push_neg at h
  have r : ∀ x : ℕ, ¬3 ^ x ∣ 3 * n ∨ 3 ^ (x + 1) ∣ 3 * n :=
    by
    intro g
    specialize h g
    push_neg at h
    by_cases h2: 3 ^ g ∣ 3*n
    right; exact h h2
    left; exact h2
  clear h
  have s : ∀ x : ℕ, ¬3 ^ x ∣ 3 * n ∧ ¬3 ^ (x + 1) ∣ 3 * n ∨ 3 ^ x ∣ 3 * n ∧ 3 ^ (x + 1) ∣ 3 * n :=
    by
    intro g
    specialize r g
    cases' r with r1 r2
    · left
      constructor; exact r1
      by_contra h
      change ∃ l : ℕ, 3 * n = 3 ^ (g + 1) * l at h
      cases' h with k hk
      rw [pow_add, pow_one, mul_assoc] at hk
      have f : 3 ^ g ∣ 3 * n := by
        use 3 * k
      have s : 3 ^ g ∣ 3 * n ∧ ¬3 ^ g ∣ 3 * n := by constructor; exact f; exact r1
      simp at s ;
    right
    constructor
    change ∃ l : ℕ, 3 * n = 3 ^ (g + 1) * l at r2
    cases' r2 with k hk
    rw [pow_add, pow_one, mul_assoc] at hk
    use 3 * k
    exact r2
  clear r
  have t : ∀ f : ℕ, 3 ^ f ∣ 3 * n := by
    intro g
    induction' g with k hk
    norm_num
    specialize s k
    cases' s with s1 s2
    · exfalso
      cases' s1 with s3 s4
      have t : 3 ^ k ∣ 3 * n ∧ ¬3 ^ k ∣ 3 * n := by constructor; exact hk; exact s3
      simp at t ;
    cases' s2 with s5 s6
    exact s6
  specialize t (n + 1)
  have q : ∀ f : ℕ, 3 ^ (f + 1) > 3 * f := by
    intro g
    induction' g with k hk
    norm_num
    change 3 ^ (k + 1 + 1) > 3 * (k + 1)
    have ss : k = 0 ∨ 0 < k := Nat.eq_zero_or_pos k
    cases ss with
    | inl ss =>
    rw [ss]; norm_num
    | inr ss =>
    change 1 ≤ k at ss
    have b : k < 2 * k := by
      change 0 < k at ss
      exact lt_two_mul_self ss
    have q1 : k + 1 < 3 * k :=
      by
      have finall := add_lt_add_of_lt_of_le b ss
      nth_rw 3 [← one_mul k] at finall
      rw [← right_distrib] at finall
      norm_num at finall
      exact finall
    have q2 := lt_trans q1 hk
    rw [pow_succ]
    apply (mul_lt_mul_left zero_lt_three  ).2 q2
  specialize q n
  have r : ¬3 ^ (n + 1) ∣ 3 * n := by
    clear t; by_contra h
    change ∃ l : ℕ, 3 * n = 3 ^ (n + 1) * l at h
    cases' h with p hp
    rw [hp] at q
    have ss : p = 0 ∨ 0 < p := Nat.eq_zero_or_pos p
    cases ss with
    | inl ss =>
    rw [ss] at hp ; norm_num at hp ; rw [hp] at j ; norm_num at j
    | inr ss =>
    simp at q ; rw [q] at ss ; norm_num at ss
  have w : 3 ^ (n + 1) ∣ 3 * n ∧ ¬3 ^ (n + 1) ∣ 3 * n :=
  by constructor; exact t; exact r
  simp at w



theorem rep_mod_three (n : ℕ) : ∃ a : ℕ, n = 3 * a ∨ n = 3 * a + 1 ∨ n = 3 * a + 2 :=
  by
  induction' n with k hk
  use 0; left; rw [MulZeroClass.mul_zero]; rfl
  cases' hk with j hj; cases' hj with h1 h23
  use j; right; left
  change k + 1 = 3 * j + 1; rw [add_left_inj 1]; exact h1
  cases' h23 with h2 h3
  use j; right; right
  change k + 1 = 3 * j + 2
  rw [← one_add_one_eq_two]; rw [← add_assoc]
  rw [add_left_inj 1]; exact h2
  use j + 1; left
  change k + 1 = 3 * (j + 1)
  rw [mul_add]; rw [mul_one]
  have babymath : 3 = 2 + 1 := by norm_num
  nth_rw 2 [babymath]; rw [← add_assoc]
  rw [add_left_inj 1]; exact h3

theorem hMul_three_expansion (n : ℕ) (h : 1 ≤ n) :
    ∃ (a : ℕ) (b : ℤ),
      1 ≤ a ∧ (3 * (n : ℤ) = 3 ^ a * (3 * b + 1) ∨ 3 * (n : ℤ) = 3 ^ a * (3 * b + 2)) :=
by
  have q := hMul_three_pow_dvd n h
  cases' q with k hk; cases' hk with h1 h2
  have ss : k = 0 ∨ 0 < k := Nat.eq_zero_or_pos k
  cases' ss with s1 s2
  rw [s1, zero_add, pow_one] at h2 ; exfalso
  have p : 3 ∣ 3 * n := by use n
  have contra : 3 ∣ 3 * n ∧ ¬3 ∣ 3 * n := by constructor; exact p; exact h2
  simp at contra ;
  change 1 ≤ k at s2
  change ∃ l : ℕ, 3 * n = 3 ^ k * l at h1 ; cases' h1 with j hj
  have p := rep_mod_three j; cases' p with r hr
  cases' hr with t1 t23
  · exfalso
    rw [t1] at hj ; rw [← mul_assoc] at hj
    nth_rw 3 [← pow_one 3] at hj ; rw [← pow_add] at hj
    have g : 3 ^ (k + 1) ∣ 3 * n := by use r;
    have combine : 3 ^ (k + 1) ∣ 3 * n ∧ ¬3 ^ (k + 1) ∣ 3 * n := by constructor; exact g; exact h2
    simp at combine ;
  cases' t23 with t2 t3
  · rw [t2] at hj
    use k; use r
    constructor; exact s2
    left; exact_mod_cast hj
  rw [t3] at hj
  use k; use r
  constructor; exact s2
  right; exact_mod_cast hj

theorem zmul_three_expansion (n : ℤ) (h : n ≠ 0) :
    ∃ (a : ℕ) (b : ℤ), 1 ≤ a ∧ (3 * n = 3 ^ a * (3 * b + 1) ∨ 3 * n = 3 ^ a * (3 * b + 2)) :=
by
  have p : n ≥ 0 ∨ n < 0 := by
    have w := lt_or_le 0 n
    cases' w with w1 w2
    left; rw [ge_iff_le]; rw [le_iff_lt_or_eq]; left; exact w1
    rw [le_iff_lt_or_eq] at w2
    cases' w2 with w3 w4
    right; exact w3
    left; rw [ge_iff_le]; rw [le_iff_lt_or_eq]; right; exact Eq.symm w4
  cases' p with p1 p2
  rw [ge_iff_le] at p1 ; rw [le_iff_eq_or_lt] at p1
  cases' p1 with p3 p4
  have t : n = 0 ∧ n ≠ 0 := by constructor; exact Eq.symm p3; exact h
  exfalso
  simp at t ;
  have p5 : 1 ≤ Int.toNat n :=
    by
    have s := Nat.eq_zero_or_pos (Int.toNat n)
    cases' s with s1 s2
    exfalso
    simp at s1
    push_neg at s1
    apply lt_irrefl 0 (lt_of_lt_of_le p4 s1)
--    rw [← PushNeg.not_lt_eq] at s1
    exact s2
  have r1 := hMul_three_expansion (Int.toNat n) p5
  cases' r1 with j hj; cases' hj with g hg; cases' hg with hg0 hg12
  use j; use g
  constructor; exact hg0
  have coe_coe : (Int.toNat n : ℤ) = n :=
    haveI finale := le_of_lt p4
    Int.toNat_of_nonneg finale
  cases' hg12 with hg1 hg2
  rw [coe_coe] at hg1 ; left; exact hg1
  rw [coe_coe] at hg2 ; right; exact hg2
  have p6 : 1 ≤ Int.toNat (-n) :=
    by
    have s := Nat.eq_zero_or_pos (Int.toNat (-n))
    cases' s with s1 s2
    exfalso
    simp at s1
    push_neg at s1;
    apply lt_irrefl 0 (lt_of_le_of_lt  s1 p2)
    exact s2
  have r2 := hMul_three_expansion (Int.toNat (-n)) p6
  cases' r2 with j hj; cases' hj with g hg; cases' hg with hg0 hg12
  have coe_coe : -(Int.toNat (-n) : ℤ) = n :=
    by
    rw [← neg_inj]; rw [neg_neg]
    rw [← neg_zero] at p2 ; rw [lt_neg] at p2
    exact Int.toNat_of_nonneg (le_of_lt p2)
  use j
  cases' hg12 with hg1 hg2
  · use-(g + 1)
    constructor; exact hg0
    right
    rw [← neg_inj] at hg1 ; rw [mul_comm] at hg1
    rw [← neg_mul] at hg1 ; rw [coe_coe] at hg1 ; rw [mul_comm] at hg1
    rw [hg1]
    ring
  · use-(g + 1)
    constructor; exact hg0
    left
    rw [← neg_inj] at hg2 ; rw [mul_comm] at hg2
    rw [← neg_mul] at hg2 ; rw [coe_coe] at hg2 ; rw [mul_comm] at hg2
    rw [hg2]; ring

theorem unit_pow_six : (unit : ℤθ) ^ 6 = ⟨-1901, -4842, -336⟩ :=
  by
  have elem : 6 = 3 + 3 := by norm_num;
  rw [elem]; rw [pow_add]; rw [unit_cubed]
  rw [hMul_mule_3]; dsimp; ring_nf

theorem unit_pow_nine : (unit : ℤθ) ^ 9 = ⟨-113633, -251019, 75015⟩ :=
  by
  have elem : 9 = 3 + 3 + 3 := by norm_num;
  rw [elem]; rw [pow_add]
  have elem1 : 3 + 3 = 6 := by norm_num;
  rw [elem1]; rw [unit_cubed]; rw [unit_pow_six]
  rw [hMul_mule_3]; dsimp; ring_nf

theorem unit_pow_three_pow_1 (n : ℕ) :
    ∃ a b c : ℤ,
      ((unit ^ 3 ^ (n + 1) : ℤθˣ) : ℤθ).f = 1 + 3 ^ (n + 1) + 3 ^ (n + 2) * a ∧
        ((unit ^ 3 ^ (n + 1) : ℤθˣ) : ℤθ).g = 3 ^ (n + 2) * b ∧
          ((unit ^ 3 ^ (n + 1) : ℤθˣ) : ℤθ).h = 3 ^ (n + 1) + 3 ^ (n + 2) * c :=
  by
  induction' n with k hk
  · rw [Nat.zero_add]; rw [Nat.zero_add]
    rw [pow_one]; rw [pow_one]
    change
      ∃ a b c : ℤ,
        ((unit : ℤθ) ^ 3).f = 1 + 3 + 3 ^ 2 * a ∧
          ((unit : ℤθ) ^ 3).g = 3 ^ 2 * b ∧ ((unit : ℤθ) ^ 3).h = 3 + 3 ^ 2 * c
    rw [unit_cubed]; dsimp
    use-3; use-7; use-2; norm_num
  have l : k + 1 = k.succ := by rfl
  rw [← one_add_one_eq_two] at hk ; rw [← add_assoc] at hk ; rw [l] at hk
  cases' hk with p hp; cases' hp with q hq; cases' hq with r hr; cases' hr with h1 h23;
  cases' h23 with h2 h3
  have t :
    (unit ^ 3 ^ k.succ : ℤθ) =
      ⟨1 + 3 ^ k.succ + 3 ^ (k.succ + 1) * p, 3 ^ (k.succ + 1) * q,
        3 ^ k.succ + 3 ^ (k.succ + 1) * r⟩ :=
    by
    ext <;> dsimp
    exact_mod_cast h1; exact_mod_cast h2; exact_mod_cast h3
  have g := le_or_gt k.succ 1
  have lower : 1 ≤ k.succ := by rw [← l]; simp
  cases' g with g1 g2
  · have upper : k.succ < 2 :=
    by
      rw [← Nat.succ_le_succ_iff] at g1
      exact g1
      --really? no better way?
    have elem := eq_or_lt_of_le g1;
    cases' elem with f1 f2; rw [f1]; norm_num

    sorry
    contradiction
  · change 2 ≤ k.succ  at g2 ; clear lower

    sorry


#eval unit ^ 3

theorem unit_pow_three_pow_2 (n : ℕ) :
    ∃ φ : ℤθ, ((unit ^ 3 ^ (n + 1) : ℤθˣ) : ℤθ) = 1 + 3 ^ (n + 1) * φ :=
  by
  induction' n with n ih
  use⟨-8, -21, -5⟩
  rfl
  obtain ⟨ψ, hψ⟩ := ih
  use ψ + 3 ^ (n + 1) * ψ ^ 2 + 3 ^ (2 * n + 2) * ψ ^ 3
  sorry
