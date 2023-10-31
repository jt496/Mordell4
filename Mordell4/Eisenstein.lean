import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.EuclideanDomain.Basic

#align_import eisenstein

/-- Just checking if I can push to Github... Yay it worked
An Eisenstein integer is a number of the form `x+y*ω`, where `ω=e^(2*π*i/3)`
and `x y :ℤ`.
We shall write `ℤω` for the Type of Eisenstein integers, with an Eisenstein
integer represented by its x- and y-coordinates.
-/
@[ext]
structure ℤω : Type where
  x : ℤ
  y : ℤ

namespace ℤω

/-- We give lean a method for checking whether two Eisenstein integers are equal.
-/
instance decEq : DecidableEq ℤω := fun a b =>
  by
  cases' a with r s
  cases' b with t u
  have : Decidable (r = t ∧ s = u) := And.decidable
 -- apply decidable_of_decidable_of_iff this
  sorry
#check Nat.add

/-- We give lean a way of displaying elements of `ℤω` using the command `#eval`.
TO DO : rewrite this using pattern matching.
-/
def repr (a : ℤω) : String := by
  by_cases a.x = 0
  · by_cases a.y = 0
    · exact "0"
    · exact a.y.repr ++ " * ω"
  · by_cases a.y = 0
    · exact a.x.repr
    · by_cases a.y > 0
      · exact a.x.repr ++ " + " ++ a.y.repr ++ " * ω"
      · exact a.x.repr ++ " - " ++ (-a.y).repr ++ " * ω"

instance ℤωRepr : Repr ℤω where
 reprPrec := fun  a  _  => repr a

#eval (⟨1, 2⟩ : ℤω)

#eval (⟨0, 0⟩ : ℤω)

#eval (⟨-4, 0⟩ : ℤω)

#eval (⟨0, -5⟩ : ℤω)

#eval (⟨3, -5⟩ : ℤω)

/-
To make `ℤω` into a ring, we need to define addition and
multiplication operations, as well as zero and one elements.
Lean also requires some other operations, such as ways
to coerce a natural number or integer into ℤω.
-/
def zero : ℤω :=
  ⟨0, 0⟩

def one : ℤω :=
  ⟨1, 0⟩

def ω : ℤω :=
  ⟨0, 1⟩

def add : ℤω → ℤω → ℤω := fun a b => ⟨a.x + b.x, a.y + b.y⟩

def neg : ℤω → ℤω := fun a => ⟨-a.x, -a.y⟩

/-- Note that `ω^2 = -ω-1`, so multiplication should be given by the formula

  `(a.x + a.y*ω) * (b.x + b.y*ω) = (a.x*b.x - a.y*b.y) + (a.x*b.y + a.y*b.x -a.y*b.y) * ω`.
-/
def mul : ℤω → ℤω → ℤω := fun a b => ⟨a.x * b.x - a.y * b.y, a.x * b.y + a.y * b.x - a.y * b.y⟩

/-
In order to make lean recognize `ℤω` as a ring, we need to supply
proofs of each of the ring axioms.
-/
variable (a b c : ℤω)

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
  --constructor <;>
  ring

theorem my_zero_mul : mul zero a = zero := by
  cases a
  simp [zero,mul]

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
  --constructor <;>
  ring

theorem my_right_distrib : mul (add a b) c = add (mul a c) (mul b c) :=
  by
  cases a; cases b; cases c
  simp only [mul, add]
  --constructor <;>
  ring

theorem my_mul_comm : mul a b = mul b a := by
  cases a; cases b
  simp only [mul]
  --constructor <;>
  ring

/-- We now package all of this information together to
tell lean that `ℤω` is a ring.
-/
instance isRing : CommRing ℤω where
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

/-
We can now use lean as a calculator in the ring `ℤω`.
-/
#eval ω ^ 3

#eval ω ^ 2 + ω + 1

----------------------------------------
open Complex Int

@[reducible]
noncomputable def rt3 : ℝ :=
  Real.sqrt 3

@[simp]
theorem rt3_sq : rt3 ^ 2 = 3 := by
  have : (0 : ℝ) ≤ 3 := by norm_num
  rw [pow_two]
  rw [← Real.sqrt_mul this 3]
  rw [Real.sqrt_mul_self this]

@[simp]
theorem sqrt3_inv_hMul_self : rt3⁻¹ * rt3 = 1 :=
by
  apply inv_mul_cancel
  intro h
  have := Real.sqrt_eq_iff_mul_self_eq (by norm_num : (0:ℝ) ≤ 3) (by norm_num : (0:ℝ) ≤ 0)
  rw [this] at h
  norm_num at h

noncomputable def complexω : ℂ :=
  ⟨-1 / 2, rt3 / 2⟩

@[simp]
theorem complexω_sq : complexω ^ 2 = -complexω - 1 :=
  by
  rw [pow_two]
  ext
  · simp only [Complex.mul_re]
    simp only [complexω]
    ring_nf
    rw [rt3_sq]
    norm_num
  · rw [Complex.mul_im]
    simp only [complexω]
    ring_nf
    dsimp
    ring_nf

noncomputable def toℂ : ℤω → ℂ := fun a => a.x + a.y * complexω

theorem my_map_one : toℂ one = 1 := by
  simp only [toℂ, one]
--  dsimp
  norm_num

theorem my_map_mul : toℂ (mul a b) = toℂ a * toℂ b :=
  by
  cases a; cases b
  simp only [mul, toℂ]
  --dsimp
  norm_num
  ring_nf
  congr
  rw [complexω_sq]
  sorry

theorem my_map_zero : toℂ zero = 0 := by
  simp [toℂ, zero]
 -- dsimp

theorem my_map_add : toℂ (add a b) = toℂ a + toℂ b :=
  by
  cases a; cases b
  simp only [add, toℂ, complexω]
  ext <;> dsimp <;> norm_num <;> ring

noncomputable def inclusion : ℤω →+* ℂ where
  toFun := toℂ
  map_one' := my_map_one
  map_mul' := my_map_mul
  map_zero' := my_map_zero
  map_add' := my_map_add

noncomputable instance ℤωCoeToℂ : Coe ℤω ℂ where coe := inclusion.toFun

-- @[simp]
theorem coe_of_mk (x y : ℤ) : (ℤω.mk x y : ℂ) = Complex.mk (x - y / 2 : ℝ) (y * rt3 / 2 : ℝ) :=
  by
  change toℂ ⟨x, y⟩ = ⟨x - y / 2, y * rt3 / 2⟩
  unfold toℂ
  dsimp
  unfold complexω
  ext
  · simp only [add_re, int_cast_re, mul_re, int_cast_im, MulZeroClass.zero_mul, tsub_zero]
    ring
  · simp only [add_im, int_cast_im, mul_im, int_cast_re, MulZeroClass.zero_mul, add_zero, zero_add,
      mul_eq_mul_left_iff, cast_eq_zero]
    ring

-- @[simp]
theorem re_of_coe : (a : ℂ).re = a.x - a.y / 2 :=
  by
  change (toℂ a).re = a.x - a.y / 2
  unfold toℂ
  unfold complexω
  simp only [add_re, int_cast_re, mul_re, int_cast_im, MulZeroClass.zero_mul, tsub_zero]
  ring

-- @[simp]
theorem im_of_coe : (a : ℂ).im = a.y * rt3 / 2 :=
  by
  change (toℂ a).im = a.y * rt3 / 2
  unfold toℂ
  unfold complexω
  simp only [add_im, int_cast_im, mul_im, int_cast_re, MulZeroClass.zero_mul, add_zero, zero_add]
  ring

-- @[simp]
theorem y_from_coe : (a.y : ℝ) = 2 * rt3⁻¹ * (a : ℂ).im :=
  by
  cases' a with x y
  simp only [coe_of_mk]
  ring_nf
  rw [mul_comm rt3]
--  rw [← _root_.mul_assoc]
  simp only [sqrt3_inv_hMul_self, _root_.one_mul, Int.cast_inj, eq_self_iff_true]

-- @[simp]
theorem x_from_coe : (a.x : ℝ) = (a : ℂ).re + rt3⁻¹ * (a : ℂ).im :=
  by
  cases' a with x y
  simp only [coe_of_mk]
  ring_nf
  rw [mul_assoc,mul_assoc,mul_comm rt3]
  simp only [ofNat_eq_coe, Nat.cast_one, cast_one, Nat.cast_ofNat, one_div, cast_negOfNat, mul_neg,
    mul_one, neg_mul]
  rw [mul_comm ((rt3)⁻¹),mul_assoc]
  simp only [ne_eq, sqrt3_inv_hMul_self, mul_one, add_neg_cancel_right]


-- @[simp]
theorem coe_eq_zero {z : ℤω} : (z : ℂ) = 0 ↔ z = 0 :=
  by
  constructor
  · intro h
    ext
    · have : (z.x : ℝ) = 0
      rw [x_from_coe, h]
      norm_num
      exact_mod_cast this
    · have : (z.y : ℝ) = 0
      rw [y_from_coe, h]
      norm_num
      exact_mod_cast this
  · intro h
    rw [h]
    exact my_map_zero

#check map_add

-- @[simp]
theorem coe_neg : ((-a : ℤω) : ℂ) = -(a : ℂ) :=
  by
  change toℂ (neg a) = -toℂ a
  simp only [neg, toℂ]
--  dsimp
  norm_num
  ring

-- @[simp]
theorem coe_sub : ((a - b : ℤω) : ℂ) = (a : ℂ) - (b : ℂ) :=
  by
  change ((a + -b : ℤω) : ℂ) = a + -(b : ℂ)
  rw [← coe_neg]
  exact my_map_add a (-b)

-- @[simp]
theorem coe_hMul : ((a * b : ℤω) : ℂ) = (a : ℂ) * (b : ℂ) :=
  my_map_mul _ _

/-- This is the `ℤ`-valued norm of an Eisenstein integer.
-/
def norm : ℤω → ℤ := fun z => z.x ^ 2 - z.x * z.y + z.y ^ 2

theorem normSq_coe : normSq a = (norm a : ℤ) :=
  by
  cases' a with x y
  simp [normSq, Norm]
  ring_nf
  simp only [re_of_coe, im_of_coe]
  -- simp only [mul_inv_cancel, ne.def, bit0_eq_zero, one_ne_zero,
  -- not_false_iff, _root_.one_mul, rt3_sq, inv_pow, add_right_inj],
  ring_nf
  rw [rt3_sq]
  ring_nf

def natNorm : ℤω → ℕ := fun z => natAbs (norm z)

theorem natNorm_coe : normSq (a : ℂ) = (natNorm a : ℝ) :=
  by
  unfold natNorm
  rw [normSq_coe]
  suffices : a.norm = a.norm.natAbs
  congr
  exact this
  refine' eq_nat_abs_of_zero_le _
  suffices : 0 ≤ normSq a
  rw [normSq_coe] at this
  exact_mod_cast this
  exact normSq_nonneg _

theorem norm_hMul : norm (a * b) = norm a * norm b :=
  by
  have := normSq_mul a b
  rw [← coe_hMul] at this
  simp only [normSq_coe] at this
  exact_mod_cast this

theorem natNorm_hMul : natNorm (a * b) = natNorm a * natNorm b :=
  by
  have := normSq_mul a b
  rw [← coe_hMul] at this
  simp only [natNorm_coe] at this
  exact_mod_cast this

theorem natNorm_eq_zero_iff : natNorm a = 0 ↔ a = 0 :=
  by
  constructor
  · intro h
    have : (a.natNorm : ℝ) = 0 := by exact_mod_cast h
    rw [← natNorm_coe] at this
    rw [normSq_eq_zero] at this
    rwa [coe_eq_zero] at this
  · intro h
    rw [h]
    decide

noncomputable def nearestℤω (z : ℂ) : ℤω :=
  let y := round (2 * rt3⁻¹ * z.im)
  { y
    x := round (z.re + 2⁻¹ * y) }

/-- NOTE. This was working earlier by nlinarith, but for some reason the
automation no longer works. That's why I've used the complicated simp.
-/
theorem self_sub_round_sq (x : ℝ) : (x - round x) ^ 2 ≤ 2⁻¹ ^ 2 :=
  by
  rw [sq_le_sq]
  have bound := abs_sub_round x
  have : |(2⁻¹ : ℝ)| = 1 / 2 := by
    simp only [one_div, abs_eq_self, inv_nonneg, zero_le_bit0, zero_le_one]
  rwa [this]

/-- We will use this in the case `c = √3/2`.
-/
theorem sub_hMul_round {c : ℝ} (x : ℝ) (c_pos : c > 0) : |x - c * round (c⁻¹ * x)| ≤ 2⁻¹ * c :=
  by
  have hc : c * c⁻¹ = 1 := by
    apply mul_inv_cancel
    exact ne_of_gt c_pos
  have h_abs_c : |c| = c := abs_of_pos c_pos
  have := abs_mul (c⁻¹ * x - round (c⁻¹ * x)) c
  rw [sub_mul] at this
  rw [mul_comm] at this
  rw [← mul_assoc] at this
  rw [hc, one_mul, mul_comm] at this
  rw [this]; clear this
  have := abs_sub_round (c⁻¹ * x)
  rw [h_abs_c]
  rw [mul_le_mul_right c_pos]
  rwa [one_div] at this

theorem im_sub_nearest (z : ℂ) : (z - nearestℤω z).im ^ 2 ≤ (4⁻¹ * rt3) ^ 2 :=
  by
  rw [sq_le_sq]
  cases' z with x y
  unfold nearestℤω
  dsimp
  simp only [coe_of_mk]; clear x
  have := sub_mul_round y (_ : 2⁻¹ * rt3 > 0)
  rw [mul_comm] at this
  have arith : 2⁻¹ * (2⁻¹ * rt3) = |4⁻¹ * rt3| :=
    by
    ring_nf
    symm
    simp only [one_div, abs_eq_self, zero_le_mul_right, Real.sqrt_pos, zero_lt_three, inv_nonneg,
      zero_le_bit0, zero_le_one]
  rwa [arith] at this ; clear arith
  ring_nf at this ⊢
  have arith : (1 / 2 * rt3)⁻¹ = 2 * rt3⁻¹ := by
    simp only [mul_comm, one_div, mul_inv_rev, inv_inv]
  rwa [arith] at this
  ·
    simp only [gt_iff_lt, zero_lt_mul_right, Real.sqrt_pos, zero_lt_three, inv_pos, zero_lt_bit0,
      zero_lt_one]

theorem re_sub_nearest (z : ℂ) : (z - nearestℤω z).re ^ 2 ≤ 2⁻¹ ^ 2 :=
  by
  rw [sq_le_sq]
  cases' z with x y
  unfold nearestℤω
  dsimp
  simp only [coe_of_mk]
  ring_nf
  rw [add_sub]
  have : |(1 / 2 : ℝ)| = 1 / 2 := by
    simp only [one_div, abs_eq_self, inv_nonneg, zero_le_bit0, zero_le_one]
  rw [this]
  exact abs_sub_round _

theorem norm_sub_nearestℤω_self_lt (z : ℂ) : normSq (z - nearestℤω z) < 1 :=
  by
  have hre := re_sub_nearest z
  have him := im_sub_nearest z
  unfold normSq
  dsimp
  simp only [← pow_two]
  have arith : (2 : ℝ)⁻¹ ^ 2 + (4⁻¹ * rt3) ^ 2 < 1 :=
    by
    ring_nf
    simp only [one_div, rt3_sq]
    norm_num
  have near := add_le_add hre him
  have := lt_of_le_of_lt near arith
  clear near arith hre him
  rwa [sub_re, sub_im] at this

noncomputable def div : ℤω → ℤω → ℤω := fun a b => nearestℤω (a / b)

noncomputable def mod : ℤω → ℤω → ℤω := fun a b => a - b * div a b

noncomputable instance hasModℤω : Mod ℤω where mod := mod

noncomputable instance hasDivℤω : Div ℤω where div := div

theorem div_add_mod : b * (a / b) + a % b = a :=
  by
  change b * div a b + mod a b = a
  simp [mod]

theorem normSq_mod_lt (h : b ≠ 0) : natNorm (mod a b) < natNorm b :=
  by
  suffices Complex.normSq (mod a b) < normSq b
    by
    simp only [natNorm_coe] at this
    exact_mod_cast this
  simp [mod, div]
  have bound : Complex.normSq (a / b - nearestℤω (a / b)) < 1 :=
    norm_sub_nearestℤω_self_lt (a / b : ℂ)
  have : (a / b : ℂ) - nearestℤω (a / b) = (a - nearestℤω (a / b) * b) * b⁻¹ :=
    by
    ring_nf
    have : (b : ℂ) * (b : ℂ)⁻¹ = 1 := by
      apply mul_inv_cancel
      simpa [coe_eq_zero] using h
    congr
    rw [mul_comm (b : ℂ)]
    rw [_root_.mul_assoc]
    rw [this]
    rw [_root_.mul_one]
  rw [this] at bound ; clear this
  rw [normSq_mul] at bound
  rw [normSq_inv] at bound
  have bound2 : 0 < Complex.normSq b := by
    rw [normSq_pos]
    intro h'
    rw [coe_eq_zero] at h'
    contradiction
  rw [mul_inv_lt_iff bound2] at bound
  rw [mul_one] at bound
  rw [mul_comm] at bound
  rw [coe_sub]
  rw [coe_hMul]
  assumption

theorem my_quotient_zero : div a 0 = 0 := by
  unfold div
  have : ((0 : ℤω) : ℂ) = 0 := my_map_zero
  rw [this, div_zero]
  unfold nearestℤω
  ext <;> dsimp <;> simp only [MulZeroClass.mul_zero, round_zero, algebraMap.coe_zero, add_zero]
  simp only [cast_zero, mul_zero, add_zero, round_zero]

theorem my_hMul_left_not_lt (hb : b ≠ 0) : ¬natNorm (a * b) < natNorm a :=
  by
  rw [natNorm_mul]
  intro h
  apply hb; clear hb
  rw [← natNorm_eq_zero_iff]
  cases b.natNorm
  · rfl
  · exfalso
    rw [Nat.mul_succ] at h
    simpa only [add_lt_iff_neg_right, not_lt_zero'] using h
    sorry

noncomputable instance euclideanℤω : EuclideanDomain ℤω where
  add := add
  zero := ⟨0, 0⟩
  zero_add := zero_add
  zero_mul := zero_mul
  mul_zero := mul_zero
  add_zero := add_zero
  add_assoc := add_assoc
  neg := neg
  add_left_neg := add_left_neg
  add_comm := add_comm
  one := ⟨1, 0⟩
  mul := mul
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  mul_comm := mul_comm
  exists_pair_ne := by
    use 0
    use 1
    intro h01
    rw [ℤω.ext_iff] at h01
    cases h01; contradiction
  quotient := div
  quotient_zero := my_quotient_zero
  remainder := mod
  quotient_mul_add_remainder_eq := div_add_mod
  r a b := natNorm a < natNorm b
  r_wellFounded := by
    refine' InvImage.wf (fun a₁ : ℤω => natNorm a₁) _
    exact { apply := _ }
    exact WellFoundedLT.apply
  remainder_lt a b := by simpa using normSq_mod_lt a b
  mul_left_not_lt := my_hMul_left_not_lt

open EuclideanDomain

-- Here is Bezout's theorem for ℤω.
#check EuclideanDomain.gcd_eq_gcd_ab a b

-- Alternatively, we can prove it ourselves.
theorem Bezout (a b : ℤω) : ∃ h k : ℤω, h * a + k * b = gcd a b :=
  by
  apply gcd.induction a b
  · intro a
    use 0
    use 1
    rw [gcd_zero_left a]
    rw [_root_.mul_zero, _root_.zero_add, _root_.one_mul]
  · intro a b ha hab
    rw [gcd_val]
    rcases hab with ⟨r, s, hrs⟩
    use s - r * (b / a)
    use r
    rw [← hrs]; clear hrs
    have := div_add_mod b a
    nth_rw 2 [← this]
    ring

end ℤω
