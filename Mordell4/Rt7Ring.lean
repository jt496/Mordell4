import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.EuclideanDomain.Basic

#align_import rt_7_ring

open scoped Classical

/-- We will be considering quadratic integers of the form `x+y*α`, where `α=(1+√-7)/2`
and `x y : ℤ`. We shall write `ℤα` for the Type of these integers,
and represent them by their z- and w-coordinates.
-/
@[ext]
structure ℤα : Type where
  z : ℤ
  w : ℤ

namespace ℤα

/-- We give lean a method for checking whether two such integers are equal.
-/
noncomputable instance decEq : DecidableEq ℤα :=
  inferInstance

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
/-- We give lean a way of displaying elements of `ℤα` using the command `#eval`.
TO DO : rewrite this using pattern matching.
-/
def repr (a : ℤα) : String := by
  by_cases a.z = 0
  · by_cases a.w = 0
    · exact "0"
    · exact a.w.repr ++ " * α"
  · by_cases a.w = 0
    · exact a.z.repr
    · by_cases a.w > 0
      · exact a.z.repr ++ " + " ++ a.w.repr ++ " * α"
      · exact a.z.repr ++ " - " ++ (-a.w).repr ++ " * α"

instance ℤαRepr : Repr ℤα where
 reprPrec := fun  a  _  => repr a

#eval (⟨1, 2⟩ : ℤα)

#eval (⟨0, 0⟩ : ℤα)

#eval (⟨-4, 0⟩ : ℤα)

#eval (⟨0, -5⟩ : ℤα)

/-- Defining addition, multiplication and other things needed for rings-/
def zero : ℤα :=
  ⟨0, 0⟩

def one : ℤα :=
  ⟨1, 0⟩

def α : ℤα :=
  ⟨0, 1⟩

def αBar : ℤα :=
  ⟨1, -1⟩

def add : ℤα → ℤα → ℤα := fun a b => ⟨a.z + b.z, a.w + b.w⟩

def neg : ℤα → ℤα := fun a => ⟨-a.z, -a.w⟩

/-- Using the fact that α^2 = α - 2, we obtain the rule for multiplication-/
def mul : ℤα → ℤα → ℤα := fun a b => ⟨a.z * b.z - 2 * a.w * b.w, a.z * b.w + a.w * b.z + a.w * b.w⟩

variable (a b c : ℤα)

theorem my_add_assoc : add (add a b) c = add a (add b c) :=
  by
  cases a; cases b; cases c
  simp only [add, add_assoc]
  tauto

theorem my_zero_add : add zero a = a := by
  cases' a with x y
  simp only [add, zero, zero_add]
  tauto

theorem my_add_zero : add a zero = a := by
  cases' a with x y
  simp only [add, zero, add_zero]
  tauto

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
  tauto

theorem my_mul_assoc : mul (mul a b) c = mul a (mul b c) :=
  by
  cases a; cases b; cases c
  simp only [mul]
  constructor <;> ring

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
  constructor <;> ring

theorem my_right_distrib : mul (add a b) c = add (mul a c) (mul b c) :=
  by
  cases a; cases b; cases c
  simp only [mul, add]
  constructor <;> ring

theorem my_mul_comm : mul a b = mul b a := by
  cases a; cases b
  simp only [mul]
  constructor <;> ring

def zsmul : ℤ → ℤα → ℤα := fun n a => ⟨n * a.z, n * a.w⟩

theorem my_zsmul_zero' : ∀ a : ℤα, zsmul (0 : ℤ) a = zero :=
  by
  intro a
  unfold zsmul
  rw [MulZeroClass.zero_mul]
  rw [MulZeroClass.zero_mul]
  rw [← zero]

theorem my_zsmul_succ' :
    ∀ (n : ℕ) (a : ℤα), zsmul (Int.ofNat n.succ) a = a.add (zsmul (Int.ofNat n) a) :=
  by
  intro n a
  change
    (⟨Int.ofNat n.succ * a.z, Int.ofNat n.succ * a.w⟩ : ℤα) =
      (⟨a.z + Int.ofNat n * a.z, a.w + Int.ofNat n * a.w⟩ : ℤα)
  norm_num
  constructor
  linarith
  linarith

theorem my_zsmul_neg' : ∀ (n : ℕ) (a : ℤα), zsmul -[n+1] a = (zsmul (↑n.succ) a).neg :=
  by
  intro n a
  simp
  change
    (⟨Int.negSucc n * a.z, Int.negSucc n * a.w⟩ : ℤα) =
      (⟨-(Int.ofNat n.succ * a.z), -(Int.ofNat n.succ * a.w)⟩ : ℤα)
  simp
  constructor
  rw [Int.negSucc_coe]
  rw [Int.neg_mul_eq_neg_mul_symm]
  rw [Int.ofNat_add]
  rwa [Int.ofNat_one]
  rw [Int.negSucc_coe]
  rw [Int.neg_mul_eq_neg_mul_symm]
  rw [Int.ofNat_add]
  rwa [Int.ofNat_one]

def intCast : ℤ → ℤα := fun a => ⟨a, 0⟩

def natCast : ℕ → ℤα := fun a => ⟨a, 0⟩

theorem my_natCast_zero : natCast 0 = zero :=
  by
  unfold nat_cast
  rw [Int.ofNat_zero]
  rfl

theorem my_natCast_succ : ∀ n : ℕ, natCast (n + 1) = (natCast n).add one :=
  by
  intro n
  change (⟨Int.ofNat (n + 1), 0⟩ : ℤα) = (⟨Int.ofNat n + 1, 0⟩ : ℤα)
  simp

theorem my_intCast_of_nat : ∀ n : ℕ, intCast ↑n = natCast n :=
  by
  intro n
  rfl

theorem my_intCast_neg_succ_of_nat : ∀ n : ℕ, intCast (-↑(n + 1)) = (natCast (n + 1)).neg :=
  by
  intro n
  rfl

/-- Making ℤα into a ring-/
instance isRing : CommRing ℤα where
  zero := zero
  neg := neg
  add := add
  one := one
  mul := mul
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
  --If the below lemmas are commented out, suddenly lean can infer that
  --ℤα is a PID again.
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

#eval α ^ 3

--def R : comm_ring ℤα := {!}
open Complex Int

@[reducible]
noncomputable def rt7 : ℝ :=
  Real.sqrt 7

@[simp]
theorem rt7_sq : rt7 ^ 2 = 7 := by
  have : (0 : ℝ) ≤ 7 := by norm_num
  rw [pow_two]
  rw [← Real.sqrt_mul this 7]
  rw [Real.sqrt_mul_self this]

theorem sqrt_7_inv_hMul_self : rt7⁻¹ * rt7 = 1 :=
  by
  apply inv_mul_cancel
  intro h
  have := Real.sqrt_eq_iff_mul_self_eq (_ : 0 ≤ 7) (_ : 0 ≤ 0)
  rw [this] at h
  norm_num at h
  norm_num
  rfl

noncomputable def complexα : ℂ :=
  ⟨1 / 2, rt7 / 2⟩

@[simp]
theorem complexα_sq : complexα ^ 2 = complexα - 2 :=
  by
  rw [pow_two]
  ext
  · simp only [Complex.mul_re]
    simp only [complex_α]
    ring_nf
    rw [rt_7_sq]
    norm_num
  · rw [Complex.mul_im]
    simp only [complex_α]
    ring_nf
    dsimp
    norm_cast
    ring_nf

noncomputable def toℂ : ℤα → ℂ := fun a => a.z + a.w * complexα

theorem my_map_one : toℂ one = 1 := by
  simp only [to_ℂ, one]
  dsimp
  norm_num

theorem my_map_mul : toℂ (mul a b) = toℂ a * toℂ b :=
  by
  cases a; cases b
  simp only [mul, to_ℂ]
  dsimp
  norm_num
  ring_nf
  congr
  rw [complex_α_sq]

theorem my_map_zero : toℂ zero = 0 := by
  simp [to_ℂ, zero]
  dsimp
  norm_cast
  ring_nf

theorem my_map_add : toℂ (add a b) = toℂ a + toℂ b :=
  by
  cases a; cases b
  simp only [add, to_ℂ, complex_α]
  ext <;> dsimp <;> norm_num <;> ring

noncomputable def inclusion : ℤα →+* ℂ where
  toFun := toℂ
  map_one' := my_map_one
  map_mul' := my_map_mul
  map_zero' := my_map_zero
  map_add' := my_map_add

noncomputable instance ℤαCoeToℂ : Coe ℤα ℂ where coe := inclusion.toFun

theorem coe_of_mk (x y : ℤ) : (ℤα.mk x y : ℂ) = Complex.mk (x + y / 2 : ℝ) (y * rt7 / 2 : ℝ) :=
  by
  change to_ℂ ⟨x, y⟩ = ⟨x + y / 2, y * rt_7 / 2⟩
  unfold to_ℂ
  dsimp
  unfold complex_α
  ext
  · simp only [add_re, int_cast_re, mul_re, int_cast_im, MulZeroClass.zero_mul, tsub_zero]
    ring
  · simp only [add_im, int_cast_im, mul_im, int_cast_re, MulZeroClass.zero_mul, add_zero, zero_add,
      mul_eq_mul_left_iff, cast_eq_zero]
    ring

theorem re_of_coe : (a : ℂ).re = a.z + a.w / 2 :=
  by
  change (to_ℂ a).re = a.z + a.w / 2
  unfold to_ℂ
  unfold complex_α
  simp only [add_re, int_cast_re, mul_re, int_cast_im, MulZeroClass.zero_mul, tsub_zero]
  ring

theorem im_of_coe : (a : ℂ).im = a.w * rt7 / 2 :=
  by
  change (to_ℂ a).im = a.w * rt_7 / 2
  unfold to_ℂ
  unfold complex_α
  simp only [add_im, int_cast_im, mul_im, int_cast_re, MulZeroClass.zero_mul, add_zero, zero_add]
  ring

theorem y_from_coe : (a.w : ℝ) = 2 * rt7⁻¹ * (a : ℂ).im :=
  by
  cases' a with x y
  simp only [coe_of_mk]
  ring_nf
  rw [mul_comm]
  rw [← _root_.mul_assoc]
  simp only [sqrt_7_inv_mul_self, _root_.one_mul, Int.cast_inj, eq_self_iff_true]

theorem x_from_coe : (a.z : ℝ) = (a : ℂ).re - rt7⁻¹ * (a : ℂ).im :=
  by
  cases' a with x y
  simp only [coe_of_mk]
  ring_nf
  rw [_root_.mul_assoc]
  rw [mul_comm rt_7]
  simp only [sqrt_7_inv_mul_self, _root_.mul_one]
  ring_nf

theorem coe_eq_zero {z : ℤα} : (z : ℂ) = 0 ↔ z = 0 :=
  by
  constructor
  · intro h
    ext
    · have : (z.z : ℝ) = 0
      rw [x_from_coe, h]
      norm_num
      exact_mod_cast this
    · have : (z.w : ℝ) = 0
      rw [y_from_coe, h]
      norm_num
      exact_mod_cast this
  · intro h
    rw [h]
    exact my_map_zero

theorem coe_neg : ((-a : ℤα) : ℂ) = -(a : ℂ) :=
  by
  change to_ℂ (neg a) = -to_ℂ a
  simp only [neg, to_ℂ]
  dsimp
  norm_num
  ring

theorem coe_sub : ((a - b : ℤα) : ℂ) = (a : ℂ) - (b : ℂ) :=
  by
  change ((a + -b : ℤα) : ℂ) = a + -(b : ℂ)
  rw [← coe_neg]
  exact my_map_add a (-b)

theorem coe_hMul : ((a * b : ℤα) : ℂ) = (a : ℂ) * (b : ℂ) :=
  my_map_mul _ _

/-- This is the `ℤ`-valued norm of this type of quadratic integer.
-/
def norm : ℤα → ℤ := fun z => z.z ^ 2 + z.z * z.w + 2 * z.w ^ 2

theorem normSq_coe : normSq a = (norm a : ℝ) :=
  by
  cases' a with x y
  simp [norm_sq, Norm]
  ring_nf
  simp only [re_of_coe, im_of_coe]
  ring_nf
  rw [rt_7_sq]
  ring_nf

def natNorm : ℤα → ℕ := fun z => natAbs (norm z)

theorem natNorm_coe : normSq (a : ℂ) = (natNorm a : ℝ) :=
  by
  unfold nat_Norm
  rw [norm_sq_coe]
  suffices : a.Norm = a.Norm.nat_abs
  congr
  exact this
  refine' eq_nat_abs_of_zero_le _
  suffices : 0 ≤ norm_sq a
  rw [norm_sq_coe] at this
  exact_mod_cast this
  exact norm_sq_nonneg _

theorem equiv_norms (v : ℤα) : norm v = (natNorm v : ℤ) :=
  by
  unfold nat_Norm
  have p : 0 ≤ (Norm v : ℝ) := by
    rw [← norm_sq_coe]
    exact norm_sq_nonneg _
  have h : 0 ≤ Norm v := by exact_mod_cast p
  rw [← abs_eq_self] at h
  norm_cast
  symm
  exact h

theorem norm_hMul : norm (a * b) = norm a * norm b :=
  by
  have := norm_sq_mul a b
  rw [← coe_mul] at this
  simp only [norm_sq_coe] at this
  exact_mod_cast this

theorem natNorm_hMul : natNorm (a * b) = natNorm a * natNorm b :=
  by
  have := norm_sq_mul a b
  rw [← coe_mul] at this
  simp only [nat_Norm_coe] at this
  exact_mod_cast this

theorem natNorm_eq_zero_iff : natNorm a = 0 ↔ a = 0 :=
  by
  constructor
  · intro h
    have : (a.nat_Norm : ℝ) = 0 := by exact_mod_cast h
    rw [← nat_Norm_coe] at this
    rw [norm_sq_eq_zero] at this
    rwa [coe_eq_zero] at this
  · intro h
    rw [h]
    decide

/-- Next we work towards establishing Euclidean division in ℤα.
First we show that for any complex number, there exists an element of
ℤα less than a distance 1 away.
-/
noncomputable def nearestℤα (z : ℂ) : ℤα :=
  let y := round (2 * rt7⁻¹ * z.im)
  { w := y
    z := round (z.re - 2⁻¹ * y) }

theorem self_sub_round_sq (x : ℝ) : (x - round x) ^ 2 ≤ 2⁻¹ ^ 2 :=
  by
  rw [sq_le_sq]
  have bound := abs_sub_round x
  have : |(2⁻¹ : ℝ)| = 1 / 2 := by
    simp only [one_div, abs_eq_self, inv_nonneg, zero_le_bit0, zero_le_one]
  rwa [this]

/-- We will use this in the case `c = √7/2`.
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

theorem im_sub_nearest (z : ℂ) : (z - nearestℤα z).im ^ 2 ≤ (4⁻¹ * rt7) ^ 2 :=
  by
  rw [sq_le_sq]
  cases' z with x y
  unfold nearest_ℤα
  dsimp
  simp only [coe_of_mk]; clear x
  have := sub_mul_round y (_ : 2⁻¹ * rt_7 > 0)
  rw [mul_comm] at this
  have arith : 2⁻¹ * (2⁻¹ * rt_7) = |4⁻¹ * rt_7| :=
    by
    ring_nf
    symm
    apply abs_of_pos
    norm_num
  rwa [arith] at this ; clear arith
  ring_nf at this ⊢
  have arith : (1 / 2 * rt_7)⁻¹ = 2 * rt_7⁻¹ := by
    simp only [mul_comm, one_div, mul_inv_rev, inv_inv]
  rwa [arith] at this
  · norm_num

theorem re_sub_nearest (z : ℂ) : (z - nearestℤα z).re ^ 2 ≤ 2⁻¹ ^ 2 :=
  by
  rw [sq_le_sq]
  cases' z with x y
  unfold nearest_ℤα
  dsimp
  simp only [coe_of_mk]
  ring_nf
  rw [add_sub]
  have : |(1 / 2 : ℝ)| = 1 / 2 := by
    simp only [one_div, abs_eq_self, inv_nonneg, zero_le_bit0, zero_le_one]
  rw [this]
  exact abs_sub_round _

--This is the key lemma
theorem norm_sub_nearestℤα_self_lt (z : ℂ) : normSq (z - nearestℤα z) < 1 :=
  by
  have hre := re_sub_nearest z
  have him := im_sub_nearest z
  unfold norm_sq
  dsimp
  simp only [← pow_two]
  have arith : (2 : ℝ)⁻¹ ^ 2 + (4⁻¹ * rt_7) ^ 2 < 1 :=
    by
    ring_nf
    simp only [one_div, rt_7_sq]
    norm_num
  have near := add_le_add hre him
  have := lt_of_le_of_lt near arith
  clear near arith hre him
  rwa [sub_re, sub_im] at this

/-- We establish Euclidean division of the form a = b*q+r,
where q is div a b, and r is mod a b.
-/
noncomputable def div : ℤα → ℤα → ℤα := fun a b => nearestℤα (a / b)

noncomputable def mod : ℤα → ℤα → ℤα := fun a b => a - b * div a b

noncomputable instance hasModℤα : Mod ℤα where mod := mod

noncomputable instance hasDivℤα : Div ℤα where div := div

theorem div_add_mod : b * (a / b) + a % b = a :=
  by
  change b * div a b + mod a b = a
  simp [mod]

-- Importantly, we must have N(r) < N(q) for Euclidean division
theorem norm_sq_mod_lt (h : b ≠ 0) : natNorm (mod a b) < natNorm b :=
  by
  suffices Complex.normSq (mod a b) < norm_sq b
    by
    simp only [nat_Norm_coe] at this
    exact_mod_cast this
  simp [mod, div]
  have bound : Complex.normSq (a / b - nearest_ℤα (a / b)) < 1 :=
    norm_sub_nearest_ℤα_self_lt (a / b : ℂ)
  have : (a / b : ℂ) - nearest_ℤα (a / b) = (a - nearest_ℤα (a / b) * b) * b⁻¹ :=
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
  rw [norm_sq_mul] at bound
  rw [norm_sq_inv] at bound
  have bound2 : 0 < Complex.normSq b := by
    rw [norm_sq_pos]
    intro h'
    rw [coe_eq_zero] at h'
    contradiction
  rw [mul_inv_lt_iff bound2] at bound
  rw [mul_one] at bound
  rw [mul_comm] at bound
  rw [coe_sub]
  rw [coe_mul]
  assumption

--Ok but why are we just casually dividing by 0?
theorem my_quotient_zero : div a 0 = 0 := by
  unfold div
  have : ((0 : ℤα) : ℂ) = 0 := my_map_zero
  rw [this]
  rw [div_zero]
  unfold nearest_ℤα
  ext <;> dsimp <;> simp only [MulZeroClass.mul_zero, round_zero, algebraMap.coe_zero, sub_zero] <;>
    rfl

theorem my_hMul_left_not_lt (hb : b ≠ 0) : ¬natNorm (a * b) < natNorm a :=
  by
  rw [nat_Norm_mul]
  intro h
  apply hb; clear hb
  rw [← nat_Norm_eq_zero_iff]
  cases b.nat_Norm
  · rfl
  · exfalso
    rw [Nat.mul_succ] at h
    simpa only [add_lt_iff_neg_right, not_lt_zero'] using h

noncomputable instance euclideanℤα : EuclideanDomain ℤα
    where
  --   add := add,
  --   zero := ⟨0,0⟩,
  --   zero_add := zero_add,
  --   add_zero := add_zero,
  --   add_assoc := add_assoc,
  --   neg := neg,
  --   add_left_neg := add_left_neg,
  --   add_comm := add_comm,
  --   one := ⟨1,0⟩,
  --   mul := mul,
  --   mul_assoc := mul_assoc,
  --   one_mul := one_mul,
  --   mul_one := mul_one,
  --   left_distrib := left_distrib,
  --   right_distrib := right_distrib,
  --   mul_comm := mul_comm,
  exists_pair_ne := by
    use 0
    use 1
    intro h
    rw [ext_iff] at h
    cases' h with h1 h2
    cases h1
  Quotient := div
  quotient_zero := my_quotient_zero
  remainder := mod
  quotient_mul_add_remainder_eq := div_add_mod
  R a b := natNorm a < natNorm b
  r_wellFounded := by
    refine' InvImage.wf (fun a₁ : ℤα => nat_Norm a₁) _
    exact { apply := _ }
    exact WellFoundedLT.apply
  --What does this mean?
  remainder_lt a b := by simpa using norm_sq_mod_lt a b
  mul_left_not_lt := my_hMul_left_not_lt

open EuclideanDomain

-- Here is Bezout's theorem for ℤα.
#check EuclideanDomain.gcd_eq_gcd_ab a b

end ℤα
