import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mordell4.Rt7Ring
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

#align_import mordell

open scoped Classical

--set_option profiler true
namespace ℤα

--variables (a b : ℤα)
-- #check a+b
-- #eval (⟨1,2⟩: ℤα)
-- #print instances  euclidean_domain
section Mordell

parameter {x y : ℤ} (sol : x ^ 3 = y ^ 2 - y + 2)

--Note that we have rewritten a.x and a.y for (a : ℤα) to a.z and a.w
--in rt_7_ring, to avoid confusion and potential clashes with x and y here.
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
--#print instances is_domain
noncomputable def d :=
  EuclideanDomain.gcd ((y : ℤα) - α) ((y : ℤα) - αBar)

/-
We work towards showing that (y-α) and (y-α_bar) are coprime, i.e.
their gcd (represented by d) is a unit. By considering the difference
of the two terms, we find that Norm d ∣ 7, and hence N(d) is 1 or 7.
In the case where we assume N(d) = 7, we arrive at a contradiction of the form
7^2 ∣ y^2-y+2 and ¬(7^2 ∣ y^2-y+2). Hence N(d) = 1 and d is a unit.
-/
theorem nat_norm_divides (a p : ℤα) : p ∣ a → natNorm p ∣ natNorm a :=
  by
  intro h
  cases' h with n hn
  use nat_Norm n
  rw [← nat_Norm_mul p n]
  rw [hn]

--Key lemma
theorem norm_divides (a p : ℤα) : p ∣ a → norm p ∣ norm a :=
  by
  intro h
  cases' h with n hn
  use Norm n
  rw [← Norm_mul p n]
  rw [hn]

--Shows that the factorization of y^2-y+2 is valid.
theorem my_factorization : (y : ℤα) ^ 2 - y + 2 = (y - α) * (y - αBar) :=
  by
  trans (y : ℤα) ^ 2 - (α + α_bar) * y + α * α_bar;
  · congr
    have r : α + α_bar = one := by
      unfold α
      unfold α_bar
      rfl
    rw [r]
    have q : one * (y : ℤα) = (y : ℤα) := one_mul (y : ℤα)
    rw [q]
  rw [right_distrib (α : ℤα) α_bar y]
  rw [mul_comm (α_bar : ℤα) y]
  rw [mul_sub_right_distrib (y : ℤα) α ((y : ℤα) - α_bar)]
  rw [mul_sub_left_distrib (y : ℤα) y α_bar]
  rw [mul_sub_left_distrib (α : ℤα) y α_bar]
  rw [pow_two (y : ℤα)]
  rw [add_comm ((α : ℤα) * y) (y * α_bar)]
  rw [← sub_sub ((y : ℤα) * (y : ℤα)) ((y : ℤα) * α_bar) (α * (y : ℤα))]
  nth_rw 2 [← add_zero ((y : ℤα) * α_bar)]
  rw [← sub_sub ((y : ℤα) * (y : ℤα)) ((y : ℤα) * α_bar) 0]
  rw [← neg_zero]
  --rw neg_neg (0:ℤα),
  --rw ← sub_add ((-(y:ℤα))*α_bar) (α*(y:ℤα)) (α*α_bar),
  --??rw left_distrib (-1:ℤα) (y*α_bar) (α*y),
  show_term ring_nf

/- d = gcd (y-α) (y-α_bar) divides the difference of
   (y-α_bar) and (y-α), which is sqrt(7)i. -/
theorem d_dvd_sqrt_seven_i : d ∣ α - αBar :=
  by
  change ∃ k : ℤα, α - α_bar = d * k
  have h : d ∣ y - α := EuclideanDomain.gcd_dvd_left (y - α) (y - α_bar)
  have q : d ∣ y - α_bar := EuclideanDomain.gcd_dvd_right (y - α) (y - α_bar)
  cases' h with j hj
  cases' q with g hg
  use g - j
  rw [mul_sub]
  rw [← hg]
  rw [← hj]
  ring_nf

theorem norm_seven : norm (α - αBar) = 7 :=
  by
  unfold Norm α α_bar
  ring_nf

--Applying norm_divides to d_dvd_sqrt_seven_i
theorem nd_dvd_seven : norm d ∣ 7 :=
  by
  have h := d_dvd_sqrt_seven_i
  --Why is it showing an extra goal?
  have q := norm_divides (α - α_bar) d h
  rw [norm_seven] at q
  exact q

theorem nat_nd_dvd_seven : natNorm d ∣ 7 :=
  by
  have h := nd_dvd_seven
  --new lemma added to rt_7_ring, equiv_norms
  rw [equiv_norms] at h
  exact_mod_cast h

theorem seven_prime : Nat.Prime 7 := by norm_num

theorem nat_nd_one_or_seven : natNorm d = 1 ∨ natNorm d = 7 :=
  Nat.Prime.eq_one_or_self_of_dvd seven_prime (nat_Norm d) nat_nd_dvd_seven

--After arriving at the result below, we then show that N(d)=7 leads to a contradiction.
theorem nd_one_or_seven : norm d = 1 ∨ norm d = 7 :=
  by
  have h := nat_nd_one_or_seven
  cases' h with p q
  left
  rw [equiv_norms]
  exact_mod_cast p
  right
  rw [equiv_norms]
  exact_mod_cast q

theorem norm_y_minus_α : norm (y - α) = y ^ 2 - y + 2 :=
  by
  have h : (y : ℤα) - α = (⟨y, -1⟩ : ℤα) :=
    by
    change (⟨y + 0, -1⟩ : ℤα) = (⟨y, -1⟩ : ℤα)
    rw [add_zero]
  rw [h]
  unfold Norm
  ring_nf

/- Using the fact that d divides y-α, we see that N(d) divides N(y-α).
Later we will assume that N(d) = 7 to get 7 ∣ y^2 - y + 2 (using the lemma below),
and solve this case by case to find that y % 7 = 4. This will aid us in setting up
the contradiction.
-/
theorem nd_dvd_pol : norm d ∣ y ^ 2 - y + 2 :=
  by
  rw [← norm_y_minus_α]
  apply norm_divides
  exact EuclideanDomain.gcd_dvd_left (y - α) (y - α_bar)

--The usual maths definition for y % 7 = s
theorem y_mod_seven (s : ℤ) (h : y % 7 = s) : ∃ k : ℤ, y = 7 * k + s :=
  by
  have q := Int.dvd_sub_of_emod_eq h
  cases' q with l lh
  use l
  rw [← add_right_inj (s : ℤ)] at lh
  rw [add_comm (s : ℤ) (y - s)] at lh
  rw [add_comm (s : ℤ) (7 * l)] at lh
  rw [sub_add_cancel] at lh
  exact lh

--The following lemmas show case by case that only y such that y % 7 = 4
--solves 7 ∣ y^2 - y + 2. Namely y % 7 = 0, 1, 2, 3, 5, or 6 fail.
------------------------------------------------
theorem y_eq_zero_mod_seven (h : 7 ∣ y ^ 2 - y + 2) (p : y % 7 = 0) : False :=
  by
  have t := y_mod_seven 0 p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have r : 7 ∣ (49 * k - 7) * k := by
    use 7 * k * k - k
    ring_nf
  rw [dvd_add_right r] at h
  have j : (0 : ℤ) < 2 := by decide
  have g := Int.le_of_dvd j h
  have ng : ¬7 ≤ 2 := by decide
  show_term linarith

theorem y_eq_one_mod_seven (h : 7 ∣ y ^ 2 - y + 2) (p : y % 7 = 1) : False :=
  by
  have t := y_mod_seven 1 p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have r : 7 ∣ (49 * k + 7) * k := by
    use 7 * k * k + k
    -- isn't it best to use ring_nf here?
    ring_nf
  rw [dvd_add_right r] at h
  have j : (0 : ℤ) < 2 := by decide
  have g := Int.le_of_dvd j h
  show_term linarith

theorem y_eq_two_mod_seven (h : 7 ∣ y ^ 2 - y + 2) (p : y % 7 = 2) : False :=
  by
  have t := y_mod_seven 2 p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have r : 7 ∣ (49 * k + 21) * k := by
    use 7 * k * k + 3 * k
    ring_nf
  rw [dvd_add_right r] at h
  have j : (0 : ℤ) < 4 := by linarith
  have g := Int.le_of_dvd j h
  linarith

theorem y_eq_three_mod_seven (h : 7 ∣ y ^ 2 - y + 2) (p : y % 7 = 3) : False :=
  by
  have t := y_mod_seven 3 p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have c : (8 : ℤ) = 7 * 1 + 1 := by linarith
  nth_rw 2 [c] at h
  have r : 7 ∣ (49 * k + 35) * k + 7 :=
    by
    use 7 * k * k + 5 * k + 1
    ring_nf
  rw [← add_assoc] at h
  rw [mul_one] at h
  rw [dvd_add_right r] at h
  have j : (0 : ℤ) < 1 := by linarith
  have g := Int.le_of_dvd j h
  linarith

theorem y_eq_five_mod_seven (h : 7 ∣ y ^ 2 - y + 2) (p : y % 7 = 5) : False :=
  by
  have t := y_mod_seven 5 p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have c : (22 : ℤ) = 7 * 3 + 1 := by linarith
  rw [c] at h
  have r : 7 ∣ (49 * k + 63) * k + 7 * 3 :=
    by
    use 7 * k * k + 9 * k + 3
    ring_nf
  rw [← add_assoc] at h
  rw [dvd_add_right r] at h
  have j : (0 : ℤ) < 1 := by linarith
  have g := Int.le_of_dvd j h
  show_term linarith

theorem y_eq_six_mod_seven (h : 7 ∣ y ^ 2 - y + 2) (p : y % 7 = 6) : False :=
  by
  have t := y_mod_seven 6 p
  cases' t with k hk
  rw [hk] at h
  ring_nf at h
  have c : (32 : ℤ) = 7 * 4 + 4 := by linarith
  rw [c] at h
  have r : 7 ∣ (49 * k + 77) * k + 7 * 4 :=
    by
    use 7 * k * k + 11 * k + 4
    ring_nf
  rw [← add_assoc] at h
  rw [dvd_add_right r] at h
  have j : (0 : ℤ) < 4 := by linarith
  have g := Int.le_of_dvd j h
  linarith

--------------------------------------------
--Now we put the previous lemmas together. (We are assuming N(d)=7.)
theorem seven_dvd_pol (mn : norm d = 7) : y % 7 = 4 :=
  by
  have h : 7 ∣ y ^ 2 - y + 2 := by
    rw [← mn]
    exact nd_dvd_pol
  have : (7 : ℤ) ≠ 0 := by decide
  have g : 0 ≤ (7 : ℤ) := by decide
  have k := Int.emod_lt y this
  have j := Int.emod_nonneg y this
  rw [← abs_eq_self] at g
  rw [g] at k
  interval_cases using j, k
  exfalso
  exact y_eq_zero_mod_seven h h_1
  exfalso
  exact y_eq_one_mod_seven h h_1
  exfalso
  exact y_eq_two_mod_seven h h_1
  exfalso
  exact y_eq_three_mod_seven h h_1
  exact h_1
  exfalso
  exact y_eq_five_mod_seven h h_1
  exfalso
  exact y_eq_six_mod_seven h h_1

--Using the result of the last lemma, we show that ¬(7^2 ∣ y^2 - y + 2).
theorem seven_sq_negdvd (h : y % 7 = 4) (p : 7 ^ 2 ∣ y ^ 2 - y + 2) : False :=
  by
  have q := y_mod_seven 4 h
  cases' q with r hr
  rw [hr] at p
  ring_nf at p
  have g : 49 ∣ (49 * r + 49) * r := by
    use r * r + r
    ring_nf
  rw [dvd_add_right g] at p
  have j : (0 : ℤ) < 14 := by linarith
  have t := Int.le_of_dvd j p
  linarith

--Finally we tie this back to our assumption that N(d) = 7.
theorem seven_sq_negdvd_full (h : norm d = 7) (p : 7 ^ 2 ∣ y ^ 2 - y + 2) : False :=
  haveI q := seven_dvd_pol h
  seven_sq_negdvd q p

--Now we start working towards the other side of the contradiction.
theorem stuff_bro (h : norm d = 7) : 7 ∣ x ^ 3 :=
  by
  have p : 7 ∣ y ^ 2 - y + 2 := by
    rw [← h]
    exact nd_dvd_pol
  rw [sol]
  exact p

--Since 7 is prime, it must also divide x.
theorem sev_dvd_x_cubed (h : 7 ∣ x ^ 3) : 7 ∣ x :=
  by
  have p := Int.Prime.dvd_pow' seven_prime h
  exact_mod_cast p

--It follows that 7^3 ∣ x^3, and then that 7^2 ∣ x^3.
theorem seven_sq_dvd (h : 7 ∣ x) : 7 ^ 2 ∣ x ^ 3 :=
  by
  have p := pow_dvd_pow_of_dvd h 3
  cases' p with f hf
  use 7 * f
  linarith

--Finally we use that x^3 = y^2 - y + 2 and tie this result back to
--our assumption that N(d) = 7. We have the other side of the contradiction.
theorem seven_sq_dvd_sol (h : norm d = 7) : 7 ^ 2 ∣ y ^ 2 - y + 2 :=
  by
  --The below code works if we replace y^2 - y + 2 by x^3 in the goal,
  --so we just need to get sol working. Then we will be able to rw ← sol
  --and go from there.
  rw [← sol]
  apply seven_sq_dvd sol
  apply sev_dvd_x_cubed sol
  apply stuff_bro sol
  exact h

--Shows by contradiction that N(d) must be 1.
theorem nd_eq_one : norm d = 1 := by
  have h := nd_one_or_seven
  cases' h with t f
  exact t
  exfalso
  have b := seven_sq_dvd_sol sol f
  exact seven_sq_negdvd_full f b

--If 'a' is a unit it must have norm 1
theorem norm_one_if_unit (a : ℤα) : IsUnit a → natNorm a = 1 :=
  by
  intro h
  rw [isUnit_iff_exists_inv] at h
  --seems unnecessary to use tauto but we need to get our hypothesis
  --into the right form to rewrite it using divides notation.
  have p : ∃ b : ℤα, 1 = a * b := by tauto
  change a ∣ 1 at p
  --applying norm_divides and using the fact that only 1 divides 1 in ℕ.
  have l := nat_norm_divides 1 a p
  have d : nat_Norm 1 = 1 := by ring
  rw [d] at l
  rwa [Nat.dvd_one] at l

--useful factorization of four times the norm, (multiplying by four keeps us in ℤ)
theorem fac_this (n m : ℤ) : 4 * (n ^ 2 + n * m + 2 * m ^ 2) = (2 * n + m) ^ 2 + 7 * m ^ 2 := by
  ring_nf

theorem sq_tauto (a : ℤ) : a ^ 2 = 0 ∨ a ^ 2 > 0 :=
  by
  by_contra
  rw [not_or] at h
  cases' h with p q
  apply q
  have r : a ≠ 0 := by finish
  exact sq_pos_of_ne_zero a r

--Finding the units of ℤα
theorem units_are {a : ℤα} (k : natNorm a = 1) : a = 1 ∨ a = -1 :=
  by
  have q : Norm a = 1 := by
    rw [equiv_norms]
    exact_mod_cast k
  unfold Norm at q
  have r : (4 : ℤ) ≠ 0 := by linarith
  have t := q
  rw [← mul_right_inj' r] at q
  rw [mul_one] at q
  rw [fac_this a.z a.w] at q
  --We show first that a.w must be 0.
  have hb : 0 ≤ (2 * a.z + a.w) ^ 2 := sq_nonneg (2 * a.z + a.w)
  have hbb : 7 * a.w ^ 2 ≤ 4 := by linarith
  have c : a.w ^ 2 = 0 ∨ a.w ^ 2 > 0 := sq_tauto a.w
  cases' c with wc lc;
  · have tt : a.w = 0 := pow_eq_zero wc
    rw [tt] at t
    ring_nf at t
    clear k r q hb hbb wc
    have h := sq_eq_one_iff.mp t
    --Essentially done, just clean up
    cases h
    left
    ext
    exact h
    exact tt
    right
    ext
    exact h
    exact tt
  exfalso
  --hbb and lc cause a contradiction
  change 1 ≤ a.w ^ 2 at lc
  have mt : 7 * 1 ≤ 7 * a.w ^ 2 := by linarith
  --have nt : ¬ (7 * a.w ^ 2 ≤ 4),
  linarith [hbb, lc]

#check Int

theorem units_is_bruv (a : ℤαˣ) : (a : ℤα) = 1 ∨ (a : ℤα) = -1 :=
  by
  have q := Units.isUnit a
  have p := norm_one_if_unit a q
  have l := units_are p
  exact l

--Since we now now what the units are,
--we can write the iff version of the if proof above.
--We also switch from nat_Norm to norm.
theorem unit_iff_norm_one (a : ℤα) : IsUnit a ↔ norm a = 1 :=
  by
  constructor
  intro h
  have l := norm_one_if_unit a h
  rw [equiv_norms]
  exact_mod_cast l
  intro h
  have j : nat_Norm a = 1 := by
    rw [equiv_norms] at h
    exact_mod_cast h
  have p := units_are j
  cases' p with ha hb
  use 1
  symm
  exact ha
  use-1
  symm
  exact hb

--Finally we can conclude that since N(d)=1, d must be a unit,
--and hence the factors are coprime.
theorem factors_coprime : IsCoprime ((y : ℤα) - α) ((y : ℤα) - αBar) :=
  by
  rw [← EuclideanDomain.gcd_isUnit_iff]
  rw [unit_iff_norm_one]
  exact nd_eq_one sol

theorem descent : ∃ k : ℤα, Associated (k ^ 3) ((y : ℤα) - α) :=
  haveI h : ((y : ℤα) - α) * (y - α_bar) = x ^ 3 :=
    by
    rw [← my_factorization]
    symm
    norm_cast
    ext
    exact sol
    rfl
  exists_associated_pow_of_mul_eq_pow' (factors_coprime sol) h

theorem descent_pro : ∃ k : ℤα, k ^ 3 = (y : ℤα) - α :=
  by
  have h := descent sol
  cases' h with b hb
  unfold Associated at hb
  cases' hb with c hc
  have p := units_is_bruv c
  cases' p with p1 p2;
  · rw [p1] at hc
    rw [mul_one] at hc
    use b
    exact hc
  rw [p2] at hc
  use-b
  show_term simp
  simp at hc
  exact hc

theorem alpha_rw (a : ℤ) (b : ℤ) : (a : ℤα) + b * α = (⟨a, b⟩ : ℤα) :=
  by
  change (⟨a + (b * 0 - 2 * 0 * 1), 0 + (b * 1 + 0 * 0 + 0 * 1)⟩ : ℤα) = (⟨a, b⟩ : ℤα)
  simp

theorem expanding :
    ∃ k : ℤα,
      (y : ℤα) - α =
        k.z ^ 3 - 6 * k.z * k.w ^ 2 - 2 * k.w ^ 3 +
          (3 * k.z ^ 2 * k.w + 3 * k.z * k.w ^ 2 - k.w ^ 3) * α :=
  by
  have h := descent_pro sol
  cases' h with k hk
  use k
  rw [← hk]
  have p : k = k.z + k.w * α :=
    by
    change k = (⟨k.z + (k.w * 0 - 2 * 0 * 1), 0 + (k.w * 1 + 0 * 0 + 0 * 1)⟩ : ℤα)
    simp
    ext
    simp
  nth_rw 1 [p]
  ring_nf

theorem neg_coe (a : ℤ) : -(a : ℤα) = (-a : ℤα) := by simp

theorem separating :
    ∃ k : ℤα,
      y = k.z ^ 3 - 6 * k.z * k.w ^ 2 - 2 * k.w ^ 3 ∧
        -1 = 3 * k.z ^ 2 * k.w + 3 * k.z * k.w ^ 2 - k.w ^ 3 :=
  by
  have h := expanding sol
  cases' h with k hk
  use k
  nth_rw 1 [← one_mul α] at hk
  have pp := alpha_rw y (-1)
  change (y : ℤα) - 1 * α = (⟨y, -1⟩ : ℤα) at pp
  rw [pp] at hk
  norm_cast at hk
  have ppp :=
    alpha_rw (k.z ^ 3 - 6 * k.z * k.w ^ 2 - 2 * k.w ^ 3)
      (3 * k.z ^ 2 * k.w + 3 * k.z * k.w ^ 2 - k.w ^ 3)
  rw [ppp] at hk
  clear pp ppp
  simp at hk
  constructor
  exact hk.1
  exact hk.2

theorem divides_one_trick (k : ℤα) (h : -1 = 3 * k.z ^ 2 * k.w + 3 * k.z * k.w ^ 2 - k.w ^ 3) :
    k.w = 1 ∨ k.w = -1 := by
  have q : (-1 : ℤ) ≠ 0 := by linarith
  have p : k.w ∣ 1 := by
    use-3 * k.z ^ 2 - 3 * k.z * k.w + k.w ^ 2
    rw [← mul_right_inj' q]
    ring_nf
    rw [h]
    ring_nf
  have g : 0 ≤ k.w ∨ 0 ≤ -k.w := by
    by_contra
    rw [not_or] at h
    cases' h with f hf
    apply hf
    linarith
  cases' g with t ht
  have q := Int.eq_one_of_dvd_one t p
  left
  exact q
  rw [← neg_dvd] at p
  have l := Int.eq_one_of_dvd_one ht p
  right
  rw [← mul_right_inj' q]
  simp
  exact l

theorem kw_eq_one (k : ℤα) (h : k.w = 1)
    (j : -1 = 3 * k.z ^ 2 * k.w + 3 * k.z * k.w ^ 2 - k.w ^ 3) : k.z = 0 ∨ k.z = -1 :=
  by
  rw [h] at j
  simp at j
  rw [← add_right_inj (1 : ℤ)] at j
  simp at j
  change 3 * 0 = 3 * k.z ^ 2 + 3 * k.z at j
  rw [← mul_add 3 (k.z ^ 2) k.z] at j
  have dumb : (3 : ℤ) ≠ 0 := by linarith
  rw [mul_right_inj' dumb] at j
  have u : k.z * 1 = k.z := by linarith
  nth_rw 2 [← u] at j
  have t : k.z ^ 2 = k.z * k.z := by linarith
  rw [t] at j
  rw [← mul_add k.z k.z 1] at j
  simp at j
  cases j
  left
  exact j
  right
  -- can definitely not use linarith
  linarith

theorem sol_kz_eq_zero (k : ℤα) (h : k.z = 0) (p : k.w = 1)
    (q : y = k.z ^ 3 - 6 * k.z * k.w ^ 2 - 2 * k.w ^ 3) : x = 2 ∧ y = -2 :=
  by
  rw [h] at q
  rw [p] at q
  norm_num at q
  constructor;
  · rw [q] at sol
    norm_num at sol
    have gg : (8 : ℤ) = 2 ^ 3 := by norm_num
    rw [gg] at sol
    have plop : 0 ≤ x ∨ 0 ≤ -x := by
      by_contra
      rw [not_or] at h
      cases' h with f hf
      apply hf
      linarith
    have bloop : (0 : ℤ) ≤ 2 := by linarith
    have gloop : (0 : ℕ) < 3 := by linarith
    cases plop
    rwa [pow_left_inj plop bloop gloop] at sol
    exfalso
    simp at plop
    have snoop : Odd 3 := by norm_num
    rw [← Odd.pow_nonpos_iff snoop] at plop
    rw [sol] at plop
    linarith
  exact q

theorem sol_kz_eq_neg_one (k : ℤα) (h : k.z = -1) (p : k.w = 1)
    (q : y = k.z ^ 3 - 6 * k.z * k.w ^ 2 - 2 * k.w ^ 3) : x = 2 ∧ y = 3 :=
  by
  rw [h] at q
  rw [p] at q
  norm_num at q
  constructor;
  · rw [q] at sol
    norm_num at sol
    have gg : (8 : ℤ) = 2 ^ 3 := by norm_num
    rw [gg] at sol
    have plop : 0 ≤ x ∨ 0 ≤ -x := by
      by_contra
      rw [not_or] at h
      cases' h with f hf
      apply hf
      linarith
    have bloop : (0 : ℤ) ≤ 2 := by linarith
    have gloop : (0 : ℕ) < 3 := by linarith
    cases plop
    rwa [pow_left_inj plop bloop gloop] at sol
    exfalso
    simp at plop
    have snoop : Odd 3 := by norm_num
    rw [← Odd.pow_nonpos_iff snoop] at plop
    rw [sol] at plop
    linarith
  exact q

theorem kw_eq_neg_one (k : ℤα) (h : k.w = -1)
    (j : -1 = 3 * k.z ^ 2 * k.w + 3 * k.z * k.w ^ 2 - k.w ^ 3) : False :=
  by
  rw [h] at j
  rw [← add_left_inj (1 : ℤ)] at j
  ring_nf at j
  have dumb : (-1 : ℤ) ≠ 0 := by linarith
  rw [← mul_right_inj' dumb] at j
  ring_nf at j
  have c : k.z ≤ -1 ∨ k.z = 0 ∨ k.z = 1 ∨ k.z ≥ 2 :=
    by
    by_contra p
    rw [not_or] at p
    rw [not_or] at p
    rw [not_or] at p
    cases' p with p1 g1
    cases' g1 with p2 g2
    cases' g2 with p3 p4
    nlinarith
  cases c; · nlinarith
  cases c;
  · rw [c] at j
    linarith
  cases c;
  · rw [c] at j
    linarith
  nlinarith

theorem diophantine_eq : x = 2 ∧ y = -2 ∨ x = 2 ∧ y = 3 :=
  by
  have h := separating sol
  cases' h with k hk
  cases' hk with a b
  have p := divides_one_trick sol k b
  cases' p with p1 p2
  have bam := kw_eq_one k p1 b
  cases bam
  left
  exact sol_kz_eq_zero sol k bam p1 a
  right
  exact sol_kz_eq_neg_one sol k bam p1 a
  exfalso
  exact kw_eq_neg_one sol k p2 b

end Mordell

end ℤα
