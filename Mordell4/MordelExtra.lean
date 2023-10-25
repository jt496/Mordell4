import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Group.Units
import Mathlib.Data.Nat.Prime
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Nat.PrimeNormNum
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Associated
import Mordell4.Rt2Ring
import Mordell4.CubicRing

#align_import Mordel_extra

open scoped Classical

--set_option profiler true
namespace ℤα

--variables (a b : ℤα)
-- #check a+b
-- #eval (⟨1,2⟩: ℤα)
-- #print instances  euclidean_domain
section Mordell

parameter {x y : ℤ} (sol : x ^ 3 = y ^ 2 - 2)

noncomputable instance : GCDMonoid ℤα
    where
  gcd a b := EuclideanDomain.gcd a b
  lcm a b := EuclideanDomain.lcm a b
  gcd_dvd_left a b := EuclideanDomain.gcd_dvd_left a b
  gcd_dvd_right a b := EuclideanDomain.gcd_dvd_right a b
  dvd_gcd a b c hac hab := EuclideanDomain.dvd_gcd hac hab
  gcd_mul_lcm := by
    intro a b
    have h := EuclideanDomain.gcd_mul_lcm a b
    use 1
    simp
  lcm_zero_left a := EuclideanDomain.lcm_zero_left a
  lcm_zero_right a := EuclideanDomain.lcm_zero_right a

instance : IsPrincipalIdealRing ℤα :=
  inferInstance

-- #print instances is_principal_ideal_ring
-- #print instances gcd_monoid
-- #print instances is_domain
noncomputable def d :=
  EuclideanDomain.gcd ((y : ℤα) + α) ((y : ℤα) - α)

/-
We work towards showing that (y+α) and (y-α) are coprime, i.e.
their gcd (represented by d) is a unit. By considering the difference of the
two terms, we find Norm d | 8. Also, x has to be odd. We have that d | x^3
which implies Norm d | x^6 (odd). This gives Norm d = 1.
-/
theorem norm_divides {p a : ℤα} (h : p ∣ a) : norm p ∣ norm a :=
  by
  cases' h with n hn
  use Norm n
  rw [← Norm_mul p n]
  rw [hn]

--Shows that the factorization of y^2-2 is valid.
theorem my_factorization : (y : ℤα) ^ 2 - 2 = (y + α) * (y - α) :=
  by
  trans (y : ℤα) ^ 2 - α ^ 2
  congr
  rw [sq_sub_sq _ _]

/- d = gcd (y+α) (y-α) divides the difference of
   (y+α) and (y-α), which is 2*sqrt(2). -/
theorem d_dvd_2_sqrt_2 : d ∣ 2 * α := by
  change d ∣ α + α
  change ∃ k : ℤα, α + α = d * k
  have h : d ∣ y + α := EuclideanDomain.gcd_dvd_left (y + α) (y - α)
  have q : d ∣ y - α := EuclideanDomain.gcd_dvd_right (y + α) (y - α)
  cases' h with j hj
  cases' q with g hg
  use j - g
  rw [mul_sub]
  rw [← hj]
  rw [← hg]
  rw [← sub_add]
  nth_rw 3 [add_comm]
  rw [add_sub_cancel (α : ℤα) (y : ℤα)]

theorem norm_d_dvd_eight : norm d ∣ 8 :=
  by
  have h := Norm_divides d_dvd_2_sqrt_2
  have p : Norm (2 * α) = 8 := by ring_nf
  rw [p] at h
  exact h

theorem mod_equiv {n : ℤ} {k : ℤ} {s : ℤ} (h : n % k = s) : ∃ m : ℤ, n = k * m + s :=
  by
  obtain ⟨l, lh⟩ := Int.dvd_sub_of_emod_eq h
  use l
  exact eq_add_of_sub_eq lh

---------------------------------------------
-- Let the pain begin
theorem y_eq_zero_mod_eight (h : 8 ∣ y ^ 2 - 2) (p : y % 8 = 0) : False :=
  by
  have t := mod_equiv p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have r : 8 ∣ 64 * k ^ 2 := by
    use 8 * k ^ 2
    ring_nf
  rw [sub_eq_add_neg] at h
  rw [dvd_add_right r] at h
  rw [← dvd_abs] at h
  norm_num at h

theorem y_eq_one_mod_eight (h : 8 ∣ y ^ 2 - 2) (p : y % 8 = 1) : False :=
  by
  have t := mod_equiv p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have r : 8 ∣ (64 * k + 16) * k := by
    use(8 * k + 2) * k
    ring_nf
  rw [sub_eq_add_neg] at h
  rw [dvd_add_right r] at h
  rw [← dvd_abs] at h
  norm_num at h

theorem y_eq_two_mod_eight (h : 8 ∣ y ^ 2 - 2) (p : y % 8 = 2) : False :=
  by
  have t := mod_equiv p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have r : 8 ∣ (64 * k + 32) * k := by
    use(8 * k + 4) * k
    ring_nf
  rw [dvd_add_right r] at h
  norm_num at h

theorem y_eq_three_mod_eight (h : 8 ∣ y ^ 2 - 2) (p : y % 8 = 3) : False :=
  by
  have t := mod_equiv p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have r : 8 ∣ (64 * k + 48) * k := by
    use(8 * k + 6) * k
    ring_nf
  rw [dvd_add_right r] at h
  norm_num at h

theorem y_eq_four_mod_eight (h : 8 ∣ y ^ 2 - 2) (p : y % 8 = 4) : False :=
  by
  have t := mod_equiv p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have r : 8 ∣ (64 * k + 64) * k := by
    use(8 * k + 8) * k
    ring_nf
  rw [dvd_add_right r] at h
  norm_num at h

theorem y_eq_five_mod_eight (h : 8 ∣ y ^ 2 - 2) (p : y % 8 = 5) : False :=
  by
  have t := mod_equiv p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have r : 8 ∣ (64 * k + 80) * k + 16 :=
    by
    use(8 * k + 10) * k + 2
    ring_nf
  have bob : (23 : ℤ) = 16 + 7 := by decide
  rw [bob] at h
  rw [← add_assoc] at h
  rw [dvd_add_right r] at h
  norm_num at h

theorem y_eq_six_mod_eight (h : 8 ∣ y ^ 2 - 2) (p : y % 8 = 6) : False :=
  by
  have t := mod_equiv p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have r : 8 ∣ (64 * k + 96) * k + 32 :=
    by
    use(8 * k + 12) * k + 4
    ring_nf
  have bob : (34 : ℤ) = 32 + 2 := by decide
  rw [bob] at h
  rw [← add_assoc] at h
  rw [dvd_add_right r] at h
  norm_num at h

theorem y_eq_seven_mod_eight (h : 8 ∣ y ^ 2 - 2) (p : y % 8 = 7) : False :=
  by
  have t := mod_equiv p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have r : 8 ∣ (64 * k + 112) * k + 40 :=
    by
    use(8 * k + 14) * k + 5
    ring_nf
  have bob : (47 : ℤ) = 40 + 7 := by decide
  rw [bob] at h
  rw [← add_assoc] at h
  rw [dvd_add_right r] at h
  norm_num at h

-----------------------------------------------
theorem x_odd : ¬2 ∣ x :=
  by-- by_contra,
  -- have k := pow_dvd_pow_of_dvd h 3,
  -- have l : (2:ℤ)^3 = 8 := by norm_num,
  -- rw l at k,
  -- rw sol at k,
  -- have : (8:ℤ) ≠ 0 := by dec_trivial,
  -- have flop : 0 ≤ (8:ℤ)  := by dec_trivial,
  -- have dip := int.mod_lt y this,
  -- have jop := int.mod_nonneg y this,
  -- rw ← abs_eq_self at flop,
  -- rw flop at dip,
  -- clear this flop l h sol,
  -- interval_cases using jop dip,
  -- exact y_eq_zero_mod_eight k h,
  -- exact y_eq_one_mod_eight k h,
  -- exact y_eq_two_mod_eight k h,
  -- exact y_eq_three_mod_eight k h,
  -- exact y_eq_four_mod_eight k h,
  -- exact y_eq_five_mod_eight k h,
  -- exact y_eq_six_mod_eight k h,
  -- exact y_eq_seven_mod_eight k h,
  sorry

theorem d_dvd_x_cubed : d ∣ x ^ 3 :=
  by
  have h : d ∣ y + α := EuclideanDomain.gcd_dvd_left (y + α) (y - α)
  have p := dvd_mul_of_dvd_right h ((y : ℤα) - α)
  rw [mul_comm] at p
  rw [← my_factorization] at p
  norm_cast at p
  rw [← sol] at p
  norm_cast
  exact p

theorem norm_d_dvd_x_six : norm d ∣ x ^ 6 :=
  by
  have h := Norm_divides (d_dvd_x_cubed sol)
  have p : Norm x ^ 3 = x ^ 6 := by
    unfold Norm
    change |x ^ 2 - 2 * 0 ^ 2| ^ 3 = x ^ 6
    nth_rw 2 [sq]
    rw [MulZeroClass.mul_zero]
    rw [MulZeroClass.mul_zero]
    rw [sub_zero]
    rw [abs_sq]
    rw [← pow_mul]
    have : 6 = 2 * 3 := by decide
    rw [← this]
  rw [pow_three] at p
  rw [← Norm_mul] at p
  rw [← Norm_mul] at p
  rw [← pow_three] at p
  rwa [p] at h

theorem x_pow_six_odd : ¬2 ∣ x ^ 6 := by
  by_contra
  apply x_odd sol
  exact Prime.dvd_of_dvd_pow Int.prime_two h

theorem x_pow_six_really_odd : Odd (x ^ 6) :=
  by
  have h := x_pow_six_odd sol
  rw [Int.two_dvd_ne_zero] at h
  rwa [← Int.odd_iff] at h

theorem of_dvd_int {m n : ℤ} (hn : Odd n) (hm : m ∣ n) : Odd m :=
  by
  cases' hn with k hk
  cases' hm with j hj
  by_contra
  rw [← Int.even_iff_not_odd] at h
  cases' h with b hb
  rw [hj, hb, ← two_mul, add_comm] at hk
  have p := sub_eq_of_eq_add hk
  rw [mul_assoc, ← mul_sub, mul_comm] at p
  have jeff := dvd_of_mul_left_eq (b * j - k) p
  norm_num at jeff

theorem norm_d_odd : Odd (norm d) :=
  of_dvd_int (x_pow_six_really_odd sol) (Norm_d_dvd_x_six sol)

#eval Nat.divisors 8

theorem divisors_of_eight {k : ℤ} (h : k ∣ 8) (p : 0 ≤ k) : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 :=
  by
  have hl : (0 : ℤ) < 8 := by decide
  have hp := Int.le_of_dvd hl h
  clear hl
  have m : k < 9
  linarith
  clear hp
  cases' k with k' k''
  on_goal 2 =>
    exfalso
    have := Int.negSucc_lt_zero k''
    have chip := lt_of_lt_of_le this p
    exact -[k''+1].lt_irrefl chip
  change (k' : ℤ) ∣ (8 : ℕ) at h
  rw [Int.coe_nat_dvd] at h
  have := (@Nat.mem_divisors k' 8).2 ⟨h, by decide⟩
  fin_cases this <;>
    simp only [Int.ofNat_eq_coe, Int.ofNat_bit0, algebraMap.coe_one, eq_self_iff_true, true_or_iff,
      or_true_iff]

theorem norm_d_eq_one : norm d = 1 :=
  by
  have h := Norm_d_dvd_eight
  have p := Norm_d_odd sol
  have easy : 0 ≤ Norm d := abs_nonneg _
  have q := divisors_of_eight h easy
  cases q; · exact q
  cases q;
  · exfalso
    rw [q] at p
    norm_num at p
  cases q;
  · rw [q] at p
    norm_num at p
  rw [q] at p
  norm_num at p

--Quest to find units begins
theorem norm_one_iff_unit (k : ℤα) : IsUnit k ↔ norm k = 1 :=
  by
  constructor;
  · intro h
    rw [isUnit_iff_exists_inv] at h
    have p : ∃ b : ℤα, 1 = k * b := by tauto
    change k ∣ 1 at p
    have l := Norm_divides p
    have d : Norm 1 = 1 := by ring
    rw [d] at l
    refine' Int.eq_one_of_dvd_one _ l
    exact abs_nonneg _
  intro h
  unfold Norm at h
  rw [isUnit_iff_exists_inv]
  rw [abs_eq] at h
  · cases h
    use(⟨k.z, -k.w⟩ : ℤα)
    change (⟨k.z * k.z + 2 * k.w * -k.w, k.z * -k.w + k.w * k.z⟩ : ℤα) = 1
    ring_nf
    rw [h]
    rfl
    use(⟨-k.z, k.w⟩ : ℤα)
    change (⟨k.z * -k.z + 2 * k.w * k.w, k.z * k.w + k.w * -k.z⟩ : ℤα) = 1
    ring_nf
    have stu : (-1 : ℤ) ≠ 0 := by decide
    rw [← mul_right_inj' stu] at h
    ring_nf at h
    rw [h]
    rfl
  exact zero_le_one

theorem factors_coprime : IsCoprime ((y : ℤα) + α) ((y : ℤα) - α) :=
  by
  rw [← EuclideanDomain.gcd_isUnit_iff]
  rw [norm_one_iff_unit]
  exact Norm_d_eq_one sol

theorem sqrt_2_lb : (1 : ℝ) < rt2 :=
  by
  have p : (0 : ℝ) ≤ 1 := zero_le_one
  have q : (0 : ℝ) ≤ rt_2 := by
    unfold rt_2
    exact Real.sqrt_nonneg 2
  rw [← abs_of_nonneg p]
  rw [← abs_of_nonneg q]
  rw [← sq_lt_sq]
  norm_num

-- lemma sqrt_2_ub : rt_2 < 2 :=
-- begin
-- have p : (0:ℝ) ≤  2 := zero_le_two,
-- have q : (0:ℝ) ≤ rt_2,{
--   unfold rt_2,
--   exact real.sqrt_nonneg 2,
-- },
-- rw ← abs_of_nonneg p,
-- rw ← abs_of_nonneg q,
-- rw ← sq_lt_sq,
-- norm_num,
-- end
theorem norm_fac (k : ℤα) : (norm k : ℝ) = |(k.z : ℝ) + k.w * rt2| * |(k.z : ℝ) - k.w * rt2| :=
  by
  unfold Norm
  rw [← abs_mul]
  ring_nf
  rw [rt_2_sq]
  norm_cast

theorem size_of_inv {v : ℤα} (h : IsUnit v) : |(v.z : ℝ) + v.w * rt2| = |(v.z : ℝ) - v.w * rt2|⁻¹ :=
  by
  rw [norm_one_iff_unit] at h
  have q : |(v.z : ℝ) - v.w * rt_2| ≠ 0 := by
    by_contra p
    have ll : (Norm v : ℝ) = 1 := by exact_mod_cast h
    rw [norm_fac v] at ll
    rw [p] at ll
    rw [MulZeroClass.mul_zero] at ll
    norm_num at ll
  rw [← mul_right_inj' q]
  nth_rw 4 [mul_comm]
  rw [inv_mul_cancel q]
  rw [mul_comm]
  rw [← norm_fac v]
  exact_mod_cast h

theorem unit_not_mul_of_rt_2 {v : ℤα} (p : IsUnit v) : v.z ≠ 0 :=
  by
  rw [norm_one_iff_unit] at p
  unfold Norm at p
  by_contra
  rw [h, sq, MulZeroClass.zero_mul, zero_sub, abs_neg] at p
  have dory := sq_nonneg v.w
  have cherry : (0 : ℤ) < 2 := zero_lt_two
  rw [← mul_le_mul_left cherry] at dory
  rw [MulZeroClass.mul_zero] at dory
  rw [abs_of_nonneg dory] at p
  have carla : (2 : ℤ) ∣ 1 := by
    rw [dvd_iff_exists_eq_mul_left]
    use v.w ^ 2
    symm
    rwa [mul_comm]
  norm_num at carla

theorem pos_units {v : ℤα} (p : IsUnit v) (h : 1 ≤ (v.z : ℝ) + v.w * rt2) : 0 < v.z ∧ 0 ≤ v.w :=
  by
  have l : 0 ≤ (v.z : ℝ) ∨ (v.z : ℝ) < 0 := le_or_lt 0 v.z
  have m : 0 ≤ (v.w : ℝ) ∨ (v.w : ℝ) < 0 := le_or_lt 0 v.w
  cases l;
  · cases m;
    · constructor
      have josh := unit_not_mul_of_rt_2 p
      have hoop : 0 ≤ v.z := by exact_mod_cast l
      rw [LE.le.lt_iff_ne hoop]
      exact josh.symm
      exact_mod_cast m
    exfalso
    have megan := size_of_inv p
    rw [norm_one_iff_unit] at p
    unfold Norm at p
    have flo : (v.z : ℝ) + v.w * rt_2 < (v.z : ℝ) - v.w * rt_2 :=
      by
      apply add_lt_add_left
      have q : (0 : ℝ) < rt_2 := lt_trans zero_lt_one sqrt_2_lb
      rw [← neg_mul]
      rw [mul_lt_mul_right q]
      have deborah := neg_lt_neg m
      rw [neg_zero] at deborah
      exact lt_trans m deborah
    have johnny := le_trans zero_le_one h
    have mom := lt_of_lt_of_le' flo h
    rw [← abs_eq_self] at johnny
    rw [← johnny] at h
    rw [megan] at h
    --- setup
    have grandpa := lt_of_lt_of_le' mom zero_le_one
    have gran := le_of_lt (lt_of_lt_of_le' mom zero_le_one)
    rw [← abs_eq_self] at gran
    rw [← gran] at mom
    rw [← gran] at grandpa
    clear gran johnny
    --------
    rw [le_inv zero_lt_one grandpa] at h
    rw [inv_one] at h
    have terry := lt_of_lt_of_le mom h
    norm_num at terry
  cases m;
  · exfalso
    have megan := size_of_inv p
    rw [norm_one_iff_unit] at p
    unfold Norm at p
    have flo : (v.z : ℝ) + v.w * rt_2 < -(v.z : ℝ) + v.w * rt_2 :=
      by
      apply add_lt_add_right
      have q : (0 : ℝ) < rt_2 := lt_trans zero_lt_one sqrt_2_lb
      have deborah := neg_lt_neg l
      rw [neg_zero] at deborah
      exact lt_trans l deborah
    have johnny := le_trans zero_le_one h
    have mom := lt_of_lt_of_le' flo h
    rw [← abs_eq_self] at johnny
    rw [← johnny] at h
    have grandpa := lt_of_lt_of_le' mom zero_le_one
    have gran := le_of_lt (lt_of_lt_of_le' mom zero_le_one)
    rw [← abs_eq_self] at gran
    rw [← gran] at mom
    rw [← gran] at grandpa
    rw [megan] at h
    rw [← abs_neg, neg_add, ← sub_eq_add_neg, neg_neg] at grandpa
    rw [← abs_neg, neg_add, ← sub_eq_add_neg, neg_neg] at mom
    rw [le_inv zero_lt_one grandpa] at h
    rw [inv_one] at h
    have terry := lt_of_lt_of_le mom h
    norm_num at terry
  exfalso
  have q : (0 : ℝ) ≤ rt_2 := by
    unfold rt_2
    exact Real.sqrt_nonneg 2
  have mm := le_of_lt m
  clear m
  have ll := le_of_lt l
  clear l
  have nob := mul_le_mul_of_nonneg_right mm q
  rw [MulZeroClass.zero_mul] at nob
  have snob := add_le_add ll nob
  rw [zero_add] at snob
  have dobby := le_trans h snob
  norm_num at dobby

def nextUnit : ℤα → ℤα := fun v => (⟨2 * v.w - v.z, v.z - v.w⟩ : ℤα)

def fUnit :=
  (⟨1, 1⟩ : ℤα)

def fUnitInv :=
  (⟨-1, 1⟩ : ℤα)

noncomputable def nextUnitℝ : ℤα → ℝ := fun v => 2 * v.w - v.z + (v.z - v.w) * rt2

-- lemma mul_units_is_unit {u v : ℤα} (p : is_unit u) (q : is_unit v) : is_unit ((u*v):ℤα) :=
-- begin
-- rw is_unit_iff_exists_inv at p q ⊢,
-- cases q with a ha,
-- cases p with b hb,
-- use a*b,
-- rw mul_assoc,
-- nth_rewrite 1 ← mul_assoc,
-- rw ha,
-- rw one_mul,
-- exact hb,
-- end
theorem fUnit_isUnit : IsUnit fUnit :=
  by
  rw [isUnit_iff_exists_inv]
  use(⟨-1, 1⟩ : ℤα)
  ring_nf

theorem unit_expansion (v : ℤα) : v = fUnit * nextUnit v :=
  by
  unfold f_unit next_unit
  change
    v = (⟨1 * (2 * v.w - v.z) + 2 * 1 * (v.z - v.w), 1 * (v.z - v.w) + 1 * (2 * v.w - v.z)⟩ : ℤα)
  ring_nf
  ext
  dsimp
  rfl
  dsimp
  rfl

theorem nextUnit_isUnit {v : ℤα} (h : IsUnit v) : IsUnit (nextUnit v) :=
  by
  -- apply is_unit_of_mul_is_unit_left
  have q := (norm_one_iff_unit v).1 h
  unfold Norm at q
  apply (norm_one_iff_unit (next_unit v)).2
  unfold Norm next_unit
  dsimp
  ring_nf
  rwa [abs_sub_comm] at q

theorem inductive_element_ge_one {v : ℤα} (h : IsUnit v) (p : 1 + rt2 ≤ (v.z : ℝ) + v.w * rt2) :
    1 ≤ nextUnitℝ v := by
  unfold next_unit_ℝ
  have q : 0 < rt_2 - 1 := by
    rw [lt_sub_iff_add_lt']
    rw [add_zero]
    exact sqrt_2_lb
  rw [← mul_le_mul_right q] at p
  ring_nf at p
  have bob : (2 : ℝ) - 1 = 1 := by norm_num
  rw [rt_2_sq, bob, add_mul, mul_assoc, ← sq, rt_2_sq, ← sub_add_eq_add_sub, mul_comm] at p
  exact p

theorem components_ge_zero {v : ℤα} (h : IsUnit v) (p : 1 + rt2 ≤ (v.z : ℝ) + v.w * rt2) :
    0 < (nextUnit v).z ∧ 0 ≤ (nextUnit v).w :=
  by
  have mm := inductive_element_ge_one h p
  have lucy := next_unit_is_unit h
  have cindy := pos_units lucy
  unfold next_unit at cindy
  dsimp at cindy
  unfold next_unit_ℝ at mm
  norm_cast at mm
  exact cindy mm

-- lemma dissection_of_unit (v : ℤα): (1 + rt_2) * (next_unit_ℝ v) = (v.z:ℝ) + v.w*rt_2 :=
-- begin
-- unfold next_unit_ℝ,
-- rw [mul_add, mul_sub, sub_mul, mul_sub],
--   repeat {rw add_mul},
--   repeat {rw one_mul},
--   nth_rewrite 2 ← mul_assoc,
--   nth_rewrite 9 mul_comm,
--   rw [mul_assoc, ← sq, rt_2_sq],
--   ring_nf,
--   rw rt_2_sq,
--   ring_nf,
-- end
-- lemma inductive_element_smaller {v : ℤα} (h : is_unit v) (n : 1 + rt_2 ≤ (v.z:ℝ) + v.w*rt_2):
-- next_unit_ℝ v < (v.z:ℝ) + v.w*rt_2 :=
-- begin
-- have q : (0:ℝ) < rt_2 := lt_trans zero_lt_one sqrt_2_lb,
-- have p := add_lt_add_left q 1,
-- rw add_zero at p,
-- have mm := lt_of_lt_of_le zero_lt_one (inductive_element_ge_one h n),
-- rw ← mul_lt_mul_right mm at p,
-- rw one_mul at p,
-- rw dissection_of_unit at p,
-- exact p,
-- end
theorem units_ge_f_unit {a b : ℕ} (p : IsUnit (⟨a, b⟩ : ℤα)) (q : 0 < b) :
    1 + rt2 ≤ ((a : ℤ) : ℝ) + ((b : ℤ) : ℝ) * rt2 :=
  by
  have alice : 0 ≤ (a : ℤ) := by exact_mod_cast zero_le a
  have ashley := unit_not_mul_of_rt_2 p
  change (a : ℤ) ≠ 0 at ashley
  have akon := lt_iff_le_and_ne.2 ⟨alice, ashley.symm⟩
  have ben : 0 < (b : ℤ) := by exact_mod_cast q
  rw [Int.lt_iff_add_one_le] at akon ben
  rw [zero_add] at akon ben
  have ben2 : 1 ≤ ((b : ℤ) : ℝ) := by exact_mod_cast ben
  have akon2 : 1 ≤ ((a : ℤ) : ℝ) := by exact_mod_cast akon
  have jason : (0 : ℝ) < rt_2 := lt_trans zero_lt_one sqrt_2_lb
  rw [← mul_le_mul_right jason] at ben2
  rw [one_mul] at ben2
  exact add_le_add akon2 ben2

theorem inductive_step' (a b : ℕ) (h : IsUnit (⟨(a : ℤ), (b : ℤ)⟩ : ℤα)) :
    ∃ n : ℕ, (⟨(a : ℤ), (b : ℤ)⟩ : ℤα) = fUnit ^ n := by sorry

theorem inductive_step :
    ∀ b : ℕ,
      (∃ a : ℕ, IsUnit (⟨(a : ℤ), (b : ℤ)⟩ : ℤα)) →
        ∀ a' : ℕ,
          IsUnit (⟨(a' : ℤ), (b : ℤ)⟩ : ℤα) → ∃ n : ℕ, (⟨(a' : ℤ), (b : ℤ)⟩ : ℤα) = fUnit ^ n :=
  by
  intro b
  induction' b using Nat.strong_induction_on with k hk
  dsimp at hk
  have baptist := Nat.eq_zero_or_pos k
  cases baptist;
  · intro h
    rw [baptist]
    intro a ha
    rw [norm_one_iff_unit] at ha
    unfold Norm at ha
    dsimp at ha
    nth_rw 2 [sq] at ha
    norm_cast at ha
    rw [MulZeroClass.mul_zero, MulZeroClass.mul_zero, ← Nat.cast_sub (zero_le (a ^ 2)),
      Nat.sub_zero] at ha
    norm_cast at ha
    have john : 1 = 1 ^ 2 := by norm_num
    nth_rw 2 [john] at ha
    rw [sq_eq_sq (zero_le a) zero_le_one] at ha
    use 0
    rw [pow_zero]
    rw [ha]
    rfl
  intro h
  intro r hr
  have pastor := unit_expansion (⟨(r : ℤ), (k : ℤ)⟩ : ℤα)
  unfold next_unit at pastor
  dsimp at pastor
  specialize hk (r - k)
  -----inequality setup
  have gentle := components_ge_zero hr
  unfold next_unit at gentle
  dsimp at gentle
  have holy := gentle (units_ge_f_unit hr baptist)
  have devil := holy.2
  have devil2 : k ≤ r := by
    have bb := le_of_sub_nonneg devil
    exact_mod_cast bb
  have preangel : 0 < 2 * (k : ℤ) - r := holy.1
  have angel : r - k < k := by
    have bbb := lt_of_sub_pos preangel
    rw [two_mul, ← sub_lt_iff_lt_add, ← Nat.cast_sub devil2] at bbb
    exact_mod_cast bbb
  have angel2 : r ≤ 2 * k := by exact_mod_cast le_of_lt (lt_of_sub_pos preangel)
  -----
  have sin := hk angel
  clear hk angel
  have god : ∃ a : ℕ, IsUnit (⟨(a : ℤ), (r - k : ℤ)⟩ : ℤα) :=
    by
    use 2 * k - r
    have saint := next_unit_is_unit hr
    unfold next_unit at saint
    dsimp at saint
    norm_cast at saint
    rw [← Nat.cast_sub devil2]
    exact saint
  rw [← Nat.cast_sub devil2] at god
  have hell := sin god
  clear sin god
  specialize hell (2 * k - r)
  have saint := next_unit_is_unit hr
  unfold next_unit at saint
  dsimp at saint
  norm_cast at saint
  have satan := hell saint
  cases' satan with n hn
  use n + 1
  rw [pastor]
  norm_cast
  rw [hn]
  rw [pow_add f_unit n 1]
  rw [mul_comm]
  rw [pow_one]

theorem equiv_ℤα (k : ℤα) : (⟨k.z, k.w⟩ : ℤα) = k :=
  by
  ext
  dsimp
  rfl
  dsimp
  rfl

theorem inductive_fallout {v : ℤα} (p : IsUnit v) (ha : 0 ≤ v.z) (hb : 0 ≤ v.w) :
    ∃ n : ℕ, v = fUnit ^ n :=
  by
  have lady := inductive_step (Int.natAbs v.w)
  have trick1 := Int.natAbs_of_nonneg hb
  have trick2 := Int.natAbs_of_nonneg ha
  rw [trick1] at lady
  have boy : ∃ a : ℕ, IsUnit (⟨(a : ℤ), v.w⟩ : ℤα) :=
    by
    use Int.natAbs v.z
    rw [trick2]
    rw [equiv_ℤα v]
    exact p
  have logan := lady boy
  clear lady boy
  specialize logan (Int.natAbs v.z)
  rw [trick2] at logan
  rw [equiv_ℤα v] at logan
  exact logan p

theorem fUnitInv_isUnit : IsUnit fUnitInv :=
  by
  rw [isUnit_iff_exists_inv]
  use f_unit
  ring_nf

theorem fUnitInv_for_real : ∃ m n : ℤαˣ, (m : ℤα) = fUnit ∧ (n : ℤα) = fUnitInv ∧ n = m⁻¹ :=
  by
  have h := f_unit_is_unit
  have g := f_unit_inv_is_unit
  unfold IsUnit at h g
  cases' g with n hn
  cases' h with m hm
  use m
  use n
  constructor
  exact hm
  constructor
  exact hn
  apply eq_inv_of_mul_eq_one_left
  rw [Units.ext_iff]
  rw [Units.val_mul]
  rw [hn]
  rw [hm]
  ring_nf

theorem inv_of_rand_unit {v : ℤα} (p : IsUnit v) :
    (∃ m n : ℤαˣ, (m : ℤα) = v ∧ (n : ℤα) = (⟨-v.z, v.w⟩ : ℤα) ∧ n = m⁻¹) ∨
      ∃ m n : ℤαˣ, (m : ℤα) = v ∧ (n : ℤα) = (⟨v.z, -v.w⟩ : ℤα) ∧ n = m⁻¹ :=
  by
  have q := p
  unfold IsUnit at p
  cases' p with m hm
  have jane : IsUnit (⟨-v.z, v.w⟩ : ℤα) :=
    by
    rw [norm_one_iff_unit]
    unfold Norm
    dsimp
    rw [neg_sq]
    rw [norm_one_iff_unit] at q
    unfold Norm at q
    exact q
  have bane : IsUnit (⟨v.z, -v.w⟩ : ℤα) :=
    by
    rw [norm_one_iff_unit]
    unfold Norm
    dsimp
    rw [neg_sq]
    rw [norm_one_iff_unit] at q
    unfold Norm at q
    exact q
  cases' jane with r hr
  cases' bane with s hs
  rw [norm_one_iff_unit] at q
  unfold Norm at q
  have obv : (0 : ℤ) ≤ 1 := zero_le_one
  rw [abs_eq obv] at q
  clear obv
  cases q;
  · right
    use m
    use s
    constructor
    exact hm
    constructor
    exact hs
    apply eq_inv_of_mul_eq_one_left
    rw [Units.ext_iff]
    rw [Units.val_mul]
    rw [hm]
    rw [hs]
    nth_rw 3 [← equiv_ℤα v]
    change (⟨v.z * v.z + 2 * -v.w * v.w, v.z * v.w + -v.w * v.z⟩ : ℤα) = 1
    ring_nf
    rw [q]
    rfl
  left
  use m
  use r
  constructor
  exact hm
  constructor
  exact hr
  apply eq_inv_of_mul_eq_one_left
  rw [Units.ext_iff]
  rw [Units.val_mul]
  rw [hm]
  rw [hr]
  nth_rw 3 [← equiv_ℤα v]
  change (⟨-v.z * v.z + 2 * v.w * v.w, -v.z * v.w + v.w * v.z⟩ : ℤα) = 1
  ring_nf
  rw [← neg_eq_iff_eq_neg, neg_sub', sub_neg_eq_add] at q
  rw [q]
  rfl

def fUnit' : ℤαˣ :=
  ⟨fUnit, fUnitInv, by ext <;> decide, by ext <;> decide⟩

theorem units_are' (v : ℤαˣ) : ∃ n : ℤ, v = (fUnit' ^ n : ℤαˣ) ∨ v = (-fUnit' ^ n : ℤαˣ) :=
  sorry

theorem units_are {v : ℤα} (p : IsUnit v) :
    ∃ n : ℕ, v = fUnit' ^ n ∨ v = -fUnit' ^ n ∨ v = fUnitInv ^ n ∨ v = -fUnitInv ^ n :=
  by
  have hz := le_or_lt 0 v.z
  have hw := le_or_lt 0 v.w
  cases hz;
  · cases hw;
    · ---------------
      have dolphin := inductive_fallout p hz hw
      cases' dolphin with n hn
      use n
      left
      exact hn
    -----------------
    rw [← Left.neg_pos_iff] at hw
    have hq := le_of_lt hw
    clear hw
    have seal : IsUnit (⟨v.z, -v.w⟩ : ℤα) :=
      by
      rw [norm_one_iff_unit]
      unfold Norm
      dsimp
      rw [neg_sq]
      rw [norm_one_iff_unit] at p
      unfold Norm at p
      exact p
    have dolphin := inductive_fallout seal hz hq
    cases' dolphin with n hn
    use n
    right
    right
    have whale := inv_of_rand_unit p
    obtain ⟨r, s, hr, hs, hi⟩ | ⟨r, s, hr, hs, hi⟩ := whale
    rw [← neg_inj] at hn
    change (⟨-v.z, - -v.w⟩ : ℤα) = -f_unit ^ n at hn
    rw [neg_neg] at hn
    rw [← hs] at hn
    rw [hi] at hn
    have jelly := f_unit_inv_for_real
    cases' jelly with t ht
    cases' ht with l hbbb
    cases' hbbb with hx hbb
    cases' hbb with hy hb
    rw [← hx] at hn
    have wave : r⁻¹ = -t ^ n := by exact_mod_cast hn
    rw [inv_eq_iff_eq_inv] at wave
    rw [inv_neg] at wave
    rw [← inv_pow] at wave
    rw [← hb] at wave
    have storm : (r : ℤα) = -(l : ℤα) ^ n := by exact_mod_cast wave
    rw [hr] at storm
    rw [hy] at storm
    right
    exact storm
    rw [← hs] at hn
    rw [hi] at hn
    have jelly := f_unit_inv_for_real
    cases' jelly with t ht
    cases' ht with l hbbb
    cases' hbbb with hx hbb
    cases' hbb with hy hb
    rw [← hx] at hn
    have wave : r⁻¹ = t ^ n := by exact_mod_cast hn
    rw [inv_eq_iff_eq_inv] at wave
    rw [← inv_pow] at wave
    rw [← hb] at wave
    have storm : (r : ℤα) = (l : ℤα) ^ n := by exact_mod_cast wave
    rw [hr] at storm
    rw [hy] at storm
    left
    exact storm
  -------------
  cases hw;
  · rw [← Left.neg_pos_iff] at hz
    have hq := le_of_lt hz
    clear hz
    have seal : IsUnit (⟨-v.z, v.w⟩ : ℤα) :=
      by
      rw [norm_one_iff_unit]
      unfold Norm
      dsimp
      rw [neg_sq]
      rw [norm_one_iff_unit] at p
      unfold Norm at p
      exact p
    have dolphin := inductive_fallout seal hq hw
    cases' dolphin with n hn
    use n
    right
    right
    have whale := inv_of_rand_unit p
    obtain ⟨r, s, hr, hs, hi⟩ | ⟨r, s, hr, hs, hi⟩ := whale
    rw [← hs] at hn
    rw [hi] at hn
    have jelly := f_unit_inv_for_real
    cases' jelly with t ht
    cases' ht with l hbbb
    cases' hbbb with hx hbb
    cases' hbb with hy hb
    rw [← hx] at hn
    have wave : r⁻¹ = t ^ n := by exact_mod_cast hn
    rw [inv_eq_iff_eq_inv] at wave
    rw [← inv_pow] at wave
    rw [← hb] at wave
    have storm : (r : ℤα) = (l : ℤα) ^ n := by exact_mod_cast wave
    rw [hr] at storm
    rw [hy] at storm
    left
    exact storm
    rw [← neg_inj] at hn
    change (⟨- -v.z, -v.w⟩ : ℤα) = -f_unit ^ n at hn
    rw [neg_neg] at hn
    rw [← hs] at hn
    rw [hi] at hn
    have jelly := f_unit_inv_for_real
    cases' jelly with t ht
    cases' ht with l hbbb
    cases' hbbb with hx hbb
    cases' hbb with hy hb
    rw [← hx] at hn
    have wave : r⁻¹ = -t ^ n := by exact_mod_cast hn
    rw [inv_eq_iff_eq_inv] at wave
    rw [inv_neg] at wave
    rw [← inv_pow] at wave
    rw [← hb] at wave
    have storm : (r : ℤα) = -(l : ℤα) ^ n := by exact_mod_cast wave
    rw [hr] at storm
    rw [hy] at storm
    right
    exact storm
  -------------
  rw [← Left.neg_pos_iff] at hz
  have hu := le_of_lt hz
  clear hz
  rw [← Left.neg_pos_iff] at hw
  have hq := le_of_lt hw
  clear hw
  have seal : IsUnit (⟨-v.z, -v.w⟩ : ℤα) :=
    by
    rw [norm_one_iff_unit]
    unfold Norm
    dsimp
    repeat' rw [neg_sq]
    rw [norm_one_iff_unit] at p
    unfold Norm at p
    exact p
  have dolphin := inductive_fallout seal hu hq
  cases' dolphin with n hn
  use n
  right
  left
  change -(⟨v.z, v.w⟩ : ℤα) = f_unit ^ n at hn
  rw [equiv_ℤα] at hn
  rw [← neg_eq_iff_eq_neg]
  exact hn

theorem unit_assoc_cube (a : ℤαˣ) :
    ∃ b : ℤαˣ, a = b ^ 3 ∨ a = fUnit' * b ^ 3 ∨ a = fUnit'⁻¹ * b ^ 3 :=
  by
  have kettle := units_are' a
  obtain ⟨n, hn⟩ := kettle
  have stove := Int.div_add_mod n 3
  have lower := Int.emod_nonneg n (by decide : (3 : ℤ) ≠ 0)
  have upper := Int.emod_lt_of_pos n (by decide : (3 : ℤ) > 0)
  have bowl : (-1 : ℤαˣ) ^ 3 = -1 := by rw [pow_three, ← sq, neg_one_sq, mul_one]
  interval_cases using lower, upper
  cases hn;
  · use f_unit' ^ (n / 3)
    rw [h, add_zero] at stove
    left
    rw [← zpow_ofNat, ← zpow_mul, mul_comm, Int.ofNat_eq_coe, Int.ofNat_bit1, algebraMap.coe_one,
      stove, hn]
  · use-f_unit' ^ (n / 3)
    rw [h, add_zero] at stove
    left
    rw [neg_pow]
    nth_rw 2 [← zpow_ofNat]
    rw [← zpow_mul]
    nth_rw 2 [mul_comm]
    rw [Int.ofNat_eq_coe, Int.ofNat_bit1, algebraMap.coe_one, stove, hn, bowl, neg_one_mul]
  cases hn
  · use f_unit' ^ (n / 3)
    right
    left
    rw [h] at stove
    rw [← zpow_ofNat, ← zpow_mul]
    nth_rw 2 [mul_comm]
    rw [Int.ofNat_eq_coe, Int.ofNat_bit1, algebraMap.coe_one, eq_sub_of_add_eq stove, mul_comm, ←
      zpow_add_one f_unit' (n - 1), sub_add_cancel]
    exact hn
  · use-f_unit' ^ (n / 3)
    right
    left
    rw [h] at stove
    rw [neg_pow]
    nth_rw 2 [← zpow_ofNat]
    rw [← zpow_mul]
    nth_rw 3 [mul_comm]
    rw [Int.ofNat_eq_coe, Int.ofNat_bit1, algebraMap.coe_one, eq_sub_of_add_eq stove, bowl, ←
      mul_assoc]
    nth_rw 2 [mul_comm]
    rw [mul_assoc, neg_one_mul, mul_comm, ← zpow_add_one f_unit' (n - 1), sub_add_cancel]
    exact hn
  cases hn;
  · use f_unit' ^ (n / 3 + 1)
    right
    right
    rw [h] at stove
    rw [← zpow_ofNat, ← zpow_mul]
    nth_rw 2 [mul_comm]
    rw [Int.ofNat_eq_coe, Int.ofNat_bit1, algebraMap.coe_one, mul_add, mul_one,
      eq_sub_of_add_eq stove, add_comm_sub, ← zpow_neg_one, ← zpow_add]
    norm_num
    exact hn
  use-f_unit' ^ (n / 3 + 1)
  right
  right
  rw [h] at stove
  rw [neg_pow]
  nth_rw 2 [← zpow_ofNat]
  rw [← zpow_mul]
  nth_rw 3 [mul_comm]
  rw [Int.ofNat_eq_coe, Int.ofNat_bit1, algebraMap.coe_one, mul_add, mul_one,
    eq_sub_of_add_eq stove, add_comm_sub, ← zpow_neg_one, bowl, ← mul_assoc]
  nth_rw 2 [mul_comm]
  rw [mul_assoc, neg_one_mul, ← zpow_add]
  norm_num
  exact hn

theorem descent : ∃ k : ℤα, Associated (k ^ 3) ((y : ℤα) + α) :=
  haveI h : ((y : ℤα) + α) * (y - α) = x ^ 3 :=
    by
    rw [← my_factorization]
    symm
    norm_cast
    ext
    exact sol
    rfl
  exists_associated_pow_of_mul_eq_pow' (factors_coprime sol) h

theorem descent_pro :
    ∃ g : ℤα,
      ((y : ℤα) + α = g ^ 3 ∨ (y : ℤα) + α = fUnit' * g ^ 3) ∨
        (y : ℤα) + α = (fUnit'.inv : ℤα) * g ^ 3 :=
  by
  have chevy := descent sol
  have ford := unit_assoc_cube
  cases' chevy with k hk
  unfold Associated at hk
  cases' hk with t ht
  specialize ford t
  cases' ford with f hf
  cases' hf with d hd
  · rw [d] at ht
    rw [Units.val_pow_eq_pow_val] at ht
    rw [← mul_pow] at ht
    use k * (f : ℤα)
    left; left
    symm
    exact ht
  cases' hd with hj hb
  · rw [hj, Units.val_mul, Units.val_pow_eq_pow_val, mul_comm, mul_assoc, ← mul_pow] at ht
    use k * (f : ℤα)
    left; right
    rw [← ht]
    nth_rw 2 [mul_comm]
  rw [hb, Units.val_mul, Units.val_pow_eq_pow_val, mul_comm, mul_assoc, ← mul_pow] at ht
  use k * (f : ℤα)
  right
  rw [← ht]
  nth_rw 2 [mul_comm]
  rfl

--what is with the inv notation?
theorem element_cubed (g : ℤα) :
    g ^ 3 = ⟨g.z ^ 3 + 6 * g.z * g.w ^ 2, 3 * g.z ^ 2 * g.w + 2 * g.w ^ 3⟩ :=
  by
  rw [pow_three]
  rw [mul_mule_1 g g]
  nth_rw 1 [← equiv_ℤα g]
  rw [mul_mule_2]
  ext
  ring_nf; ring_nf

theorem descent_pro_1_no_sol : ¬∃ g : ℤα, (y : ℤα) + α = g ^ 3 :=
  by
  by_contra
  cases' h with g hg
  change (⟨y + 0, 0 + 1⟩ : ℤα) = g ^ 3 at hg
  rw [zero_add, add_zero] at hg
  rw [element_cubed] at hg
  ring_nf at hg
  cases' hg with hf hv
  ring_nf at hv
  have q : (1 : ℤ) ≠ 0 := by decide
  have p : g.w ∣ 1 := by
    use 2 * g.w ^ 2 + 3 * g.z ^ 2
    rw [mul_comm]
    exact hv
  have g : 0 ≤ g.w ∨ 0 ≤ -g.w := by
    by_contra
    rw [not_or] at h
    cases' h with f hf
    apply hf
    linarith
  cases' g with t ht
  have q := Int.eq_one_of_dvd_one t p
  · rw [q, mul_one, sq, mul_one, mul_one] at hv
    have k := sub_eq_of_eq_add' hv
    rw [(by decide : (1 : ℤ) - 2 = -1)] at k
    have j : (3 : ℤ) ∣ 1 := by
      use-g.z ^ 2
      rw [mul_neg]
      rw [← neg_eq_iff_eq_neg]
      exact k
    norm_num at j
  have b := Dvd.dvd.neg_left p
  have q := Int.eq_one_of_dvd_one ht b
  rw [neg_eq_iff_eq_neg] at q
  rw [q, neg_one_sq, mul_one, mul_neg_one, neg_add] at hv
  have k := sub_eq_of_eq_add' hv
  rw [sub_neg_eq_add, (by decide : (1 : ℤ) + 2 = 3), mul_comm, ← neg_mul] at k
  nth_rw 1 [← one_mul (3 : ℤ)] at k
  rw [mul_left_inj' (by decide : (3 : ℤ) ≠ 0)] at k
  rw [← neg_eq_iff_eq_neg] at k
  have d := sq_nonneg (g.z : ℤ)
  rw [← k] at d
  norm_num at d

theorem case_2_sol (g : ℤα) (h : (y : ℤα) + α = fUnit' * g ^ 3) :
    y = g.z ^ 3 + 6 * g.z ^ 2 * g.w + 6 * g.z * g.w ^ 2 + 4 * g.w ^ 3 ∧
      1 = g.z ^ 3 + 3 * g.z ^ 2 * g.w + 6 * g.z * g.w ^ 2 + 2 * g.w ^ 3 :=
  by
  change (⟨y + 0, 0 + 1⟩ : ℤα) = f_unit * g ^ 3 at h
  unfold f_unit at h
  rw [zero_add, add_zero, element_cubed, mul_mule_2] at h
  ring_nf at h
  cases' h with ha hb
  constructor;
  · ring_nf
    exact ha
  ring_nf
  exact hb

theorem case_3_sol (g : ℤα) (h : (y : ℤα) + α = fUnit'.inv * g ^ 3) :
    y = -g.z ^ 3 + 6 * g.z ^ 2 * g.w - 6 * g.z * g.w ^ 2 + 4 * g.w ^ 3 ∧
      1 = g.z ^ 3 - 3 * g.z ^ 2 * g.w + 6 * g.z * g.w ^ 2 - 2 * g.w ^ 3 :=
  by
  change (⟨y + 0, 0 + 1⟩ : ℤα) = f_unit_inv * g ^ 3 at h
  unfold f_unit_inv at h
  rw [zero_add, add_zero, element_cubed, mul_mule_2] at h
  ring_nf at h
  cases' h with ha hb
  constructor;
  · ring_nf
    exact ha
  ring_nf
  exact hb

end Mordell

end ℤα
