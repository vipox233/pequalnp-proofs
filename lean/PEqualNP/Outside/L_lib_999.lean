import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_999

open Finset

-- The cycle order and its lemmas follow our proof of L-lib-945.

def sig (N t k : ℕ) : ℕ := (k % (N / Nat.gcd t N)) * t + k / (N / Nat.gcd t N)

theorem L_pos {N : ℕ} (hN : 0 < N) (t : ℕ) : 0 < N / Nat.gcd t N :=
  Nat.div_pos (Nat.le_of_dvd hN (Nat.gcd_dvd_right t N)) (Nat.gcd_pos_of_pos_right t hN)

theorem NLg (N t : ℕ) : N = N / Nat.gcd t N * Nat.gcd t N :=
  (Nat.div_mul_cancel (Nat.gcd_dvd_right t N)).symm

theorem sig_inj {N : ℕ} (hN : 0 < N) (t : ℕ) (k k' : ℕ) (hk : k < N) (hk' : k' < N)
    (h : sig N t k % N = sig N t k' % N) : k = k' := by
  unfold sig at h
  have hL := L_pos hN t
  have hNL := NLg N t
  have hg : 0 < Nat.gcd t N := Nat.gcd_pos_of_pos_right t hN
  set L := N / Nat.gcd t N with hLd
  have hc : k / L < Nat.gcd t N := Nat.div_lt_of_lt_mul (by rw [← hNL]; exact hk)
  have hc' : k' / L < Nat.gcd t N := Nat.div_lt_of_lt_mul (by rw [← hNL]; exact hk')
  have hgN : (k % L) * t + k / L ≡ (k' % L) * t + k' / L [MOD Nat.gcd t N] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_right t N) h
  have ht0 : t % Nat.gcd t N = 0 := Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left t N)
  have e1 : ∀ m, (m % L) * t + m / L ≡ m / L [MOD Nat.gcd t N] := by
    intro m
    unfold Nat.ModEq
    rw [Nat.add_mod, Nat.mul_mod, ht0, mul_zero, Nat.zero_mod, zero_add, Nat.mod_mod]
  have hcc : k / L = k' / L := by
    have h2 := ((e1 k).symm.trans hgN).trans (e1 k')
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at h2
  rw [hcc] at h
  have h3 : (k % L) * t ≡ (k' % L) * t [MOD N] := Nat.ModEq.add_right_cancel' (k' / L) h
  have h4 : k % L ≡ k' % L [MOD L] := by
    have := Nat.ModEq.cancel_right_div_gcd hN h3
    rwa [Nat.gcd_comm] at this
  unfold Nat.ModEq at h4
  rw [Nat.mod_mod, Nat.mod_mod] at h4
  rw [← Nat.div_add_mod k L, ← Nat.div_add_mod k' L, hcc, h4]

theorem Lt_eq {N : ℕ} (hN : 0 < N) (t : ℕ) : N / Nat.gcd t N * t = N * (t / Nat.gcd t N) := by
  have hg : 0 < Nat.gcd t N := Nat.gcd_pos_of_pos_right t hN
  obtain ⟨L, hL⟩ := Nat.gcd_dvd_right t N
  obtain ⟨t', ht'⟩ := Nat.gcd_dvd_left t N
  generalize Nat.gcd t N = g at *
  subst hL ht'
  rw [Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg]
  ring

def G (f : ℕ → ℕ) (N t B k : ℕ) : ℕ := f (sig N t k + B + t) - f (sig N t k + B)

theorem block (f : ℕ → ℕ) (hf : Monotone f) {N : ℕ} (hN : 0 < N) (t B q j : ℕ)
    (hj : j ≤ N / Nat.gcd t N) :
    ∑ i ∈ range j, G f N t B (N / Nat.gcd t N * q + i) = f (q + j * t + B) - f (q + B) := by
  have hL := L_pos hN t
  have hs : ∀ i ∈ range j, G f N t B (N / Nat.gcd t N * q + i) =
      (fun i => f (q + i * t + B)) (i + 1) - (fun i => f (q + i * t + B)) i := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold G sig
    have e1 : (N / Nat.gcd t N * q + i) % (N / Nat.gcd t N) = i := by
      rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have e2 : (N / Nat.gcd t N * q + i) / (N / Nat.gcd t N) = q := by
      rw [add_comm, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt (by omega), zero_add]
    rw [e1, e2]
    dsimp only
    rw [show i * t + q + B + t = q + (i + 1) * t + B by ring,
      show i * t + q + B = q + i * t + B by ring]
  rw [Finset.sum_congr rfl hs, Finset.sum_range_tsub (f := fun i => f (q + i * t + B))
    (fun a b hab => hf (by nlinarith))]
  simp

theorem full (f : ℕ → ℕ) (hf : Monotone f) {N : ℕ} (hN : 0 < N)
    (hsh : ∀ j m, f (j + N * m) = f j + m) (t B q : ℕ) :
    ∑ k ∈ range (N / Nat.gcd t N * q), G f N t B k = q * (t / Nat.gcd t N) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show N / Nat.gcd t N * (q + 1) = N / Nat.gcd t N * q + N / Nat.gcd t N by ring,
      Finset.sum_range_add, ih, block f hf hN t B q _ le_rfl]
    have hLt := Lt_eq hN t
    rw [show q + N / Nat.gcd t N * t + B = q + B + N * (t / Nat.gcd t N) by rw [hLt]; ring, hsh]
    rw [Nat.add_sub_cancel_left]
    ring

theorem total (f : ℕ → ℕ) (hf : Monotone f) {N : ℕ} (hN : 0 < N)
    (hsh : ∀ j m, f (j + N * m) = f j + m) (t B r : ℕ) :
    ∑ k ∈ range r, G f N t B k = r / (N / Nat.gcd t N) * (t / Nat.gcd t N) +
      (f (r / (N / Nat.gcd t N) + r % (N / Nat.gcd t N) * t + B) -
        f (r / (N / Nat.gcd t N) + B)) := by
  have hL := L_pos hN t
  conv_lhs => rw [← Nat.div_add_mod r (N / Nat.gcd t N)]
  rw [Finset.sum_range_add, full f hf hN hsh, block f hf hN t B _ _ (Nat.mod_lt _ hL).le]

/-- number of p below M with p congruent to u -/
def C (N u M : ℕ) : ℕ := (M + N - 1 - u) / N

theorem C_mono (N u : ℕ) : Monotone (C N u) := fun a b h => Nat.div_le_div_right (by omega)

theorem C_shift {N u : ℕ} (hN : 0 < N) (hu : u < N) (j m : ℕ) :
    C N u (j + N * m) = C N u j + m := by
  unfold C
  rw [show j + N * m + N - 1 - u = (j + N - 1 - u) + N * m by omega, Nat.add_mul_div_left _ _ hN]

theorem diffmod {N u : ℕ} (hN : 0 < N) (hu : u < N) (M d : ℕ) :
    C N u (M + d) - C N u M = C N u (M % N + d) - C N u (M % N) := by
  have h := Nat.mod_add_div M N
  have e1 : C N u (M + d) = C N u (M % N + d) + M / N := by
    rw [← C_shift hN hu]; congr 1; omega
  have e2 : C N u M = C N u (M % N) + M / N := by
    rw [← C_shift hN hu]; congr 1; omega
  rw [e1, e2]; omega

theorem diffcong {N u : ℕ} (hN : 0 < N) (hu : u < N) (M M' d : ℕ) (h : M % N = M' % N) :
    C N u (M + d) - C N u M = C N u (M' + d) - C N u M' := by
  rw [diffmod hN hu M d, diffmod hN hu M' d, h]

theorem dm {N : ℕ} (_hN : 0 < N) (x : ℕ) (h : x < 3 * N) :
    (x < N ∧ x / N = 0 ∧ x % N = x) ∨ (N ≤ x ∧ x < 2 * N ∧ x / N = 1 ∧ x % N = x - N) ∨
      (2 * N ≤ x ∧ x / N = 2 ∧ x % N = x - 2 * N) := by
  rcases Nat.lt_or_ge x N with h1 | h1
  · left; exact ⟨h1, Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1⟩
  rcases Nat.lt_or_ge x (2 * N) with h2 | h2
  · right; left
    refine ⟨h1, h2, Nat.div_eq_of_lt_le (by omega) (by omega), ?_⟩
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  · right; right
    refine ⟨h2, Nat.div_eq_of_lt_le (by omega) (by omega), ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega : x ≥ N), Nat.mod_eq_sub_mod (by omega : x - N ≥ N),
      Nat.mod_eq_of_lt (by omega)]
    omega

theorem ind_eq {N : ℕ} (hN : 0 < N) {t u : ℕ} (ht : t ≤ N) (hu : u < N) (E : ℕ) :
    (if (E + N - u) % N < t then 1 else 0) = C N u (E + 1 + N - t + t) - C N u (E + 1 + N - t) := by
  have h := Nat.mod_add_div E N
  have hρ := Nat.mod_lt E hN
  have e1 : (E + N - u) % N = (E % N + N - u) % N := by
    rw [show E + N - u = (E % N + N - u) + N * (E / N) by omega, Nat.add_mul_mod_self_left]
  rw [diffcong hN hu (E + 1 + N - t) (E % N + 1 + N - t) t (by
    rw [show E + 1 + N - t = (E % N + 1 + N - t) + N * (E / N) by omega,
      Nat.add_mul_mod_self_left]), e1]
  unfold C
  generalize E % N = ρ at *
  rcases dm hN (ρ + N - u) (by omega) with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3⟩ <;>
  rcases dm hN (ρ + 1 + N - t + t + N - 1 - u) (by omega) with
    ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3⟩ <;>
  rcases dm hN (ρ + 1 + N - t + N - 1 - u) (by omega) with
    ⟨c1, c2, c3⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3⟩ <;>
  split_ifs <;> omega

theorem partB {N : ℕ} (hN : 0 < N) {u : ℕ} (hu : u < N) (P M : ℕ) :
    C N u (P + M) - C N u P = M / N + (if (u + N - P % N) % N < M % N then 1 else 0) := by
  have hP := Nat.mod_add_div P N
  have hM := Nat.mod_add_div M N
  have e1 : C N u (P + M) = C N u (P % N + M % N) + (P / N + M / N) := by
    rw [← C_shift hN hu]; congr 1; rw [mul_add]; omega
  have e2 : C N u P = C N u (P % N) + P / N := by
    rw [← C_shift hN hu]; congr 1; omega
  rw [e1, e2]
  have h1 := Nat.mod_lt P hN
  have h2 := Nat.mod_lt M hN
  unfold C
  generalize P % N = ρ at *
  generalize M % N = μ at *
  generalize P / N = a at *
  generalize M / N = b at *
  rcases dm hN (u + N - ρ) (by omega) with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3⟩ <;>
  rcases dm hN (ρ + μ + N - 1 - u) (by omega) with
    ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3⟩ <;>
  rcases dm hN (ρ + N - 1 - u) (by omega) with
    ⟨c1, c2, c3⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3⟩ <;>
  split_ifs <;> omega

theorem ceil_ge {N : ℕ} (hN : 0 < N) (c M : ℕ) :
    M / N + (if c < M % N then 1 else 0) ≤ (M + N - 1) / N := by
  have hM := Nat.mod_add_div M N
  have h2 := Nat.mod_lt M hN
  rw [show M + N - 1 = (M % N + N - 1) + N * (M / N) by omega, Nat.add_mul_div_left _ _ hN]
  rcases dm hN (M % N + N - 1) (by omega) with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3⟩ <;>
  split_ifs <;> omega

def xv (N t a : ℕ) : ℕ := (N - sig N t a % N) % N

def rowF {N : ℕ} (hN : 0 < N) (t : ℕ) : Fin N → Fin N :=
  fun k => ⟨xv N t k.val, Nat.mod_lt _ hN⟩

theorem rowF_inj {N : ℕ} (hN : 0 < N) (t : ℕ) : Function.Injective (rowF hN t) := by
  intro k k' h
  have h1 : xv N t k.val = xv N t k'.val := Fin.mk.inj_iff.mp h
  apply Fin.ext
  apply sig_inj hN t k.val k'.val k.isLt k'.isLt
  unfold xv at h1
  have a1 := Nat.mod_lt (sig N t k.val) hN
  have a2 := Nat.mod_lt (sig N t k'.val) hN
  generalize sig N t k.val % N = A at *
  generalize sig N t k'.val % N = A' at *
  rcases dm hN (N - A) (by omega) with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3⟩ <;>
  rcases dm hN (N - A') (by omega) with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3⟩ <;>
  omega

noncomputable def order {N : ℕ} (hN : 0 < N) (t : ℕ) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (rowF hN t) (Finite.injective_iff_bijective.mp (rowF_inj hN t))

def lv (N t r : ℕ) : ℕ := r % (N / Nat.gcd t N) * t

def c0 (N t r s : ℕ) : ℕ :=
  (3 * N + t - 1 - r / (N / Nat.gcd t N) - s / (N / Nat.gcd (lv N t r) N)) % N

def yv (N t r s b : ℕ) : ℕ := (sig N (lv N t r) b + c0 N t r s) % N

def cols {N : ℕ} (hN : 0 < N) (t r s : ℕ) : Finset (Fin N) :=
  (range s).image (fun b => (⟨yv N t r s b, Nat.mod_lt _ hN⟩ : Fin N))

theorem yv_inj {N : ℕ} (hN : 0 < N) (t r s : ℕ) (hs : s ≤ N) :
    Set.InjOn (fun b => (⟨yv N t r s b, Nat.mod_lt _ hN⟩ : Fin N)) (range s) := by
  intro b hb b' hb' h
  simp only [coe_range, Set.mem_Iio] at hb hb'
  have h1 : yv N t r s b = yv N t r s b' := Fin.mk.inj_iff.mp h
  unfold yv at h1
  have h2 : sig N (lv N t r) b % N = sig N (lv N t r) b' % N :=
    Nat.ModEq.add_right_cancel' (c0 N t r s) h1
  exact sig_inj hN _ b b' (by omega) (by omega) h2

theorem rowsum {N : ℕ} (hN : 0 < N) (t r : ℕ) (hr : r ≤ N) (h : ℕ → ℕ) :
    ∑ x ∈ (univ : Finset (Fin N)).filter (fun x => ((order hN t).symm x).val < r), h x.val =
      ∑ a ∈ range r, h (xv N t a) := by
  rw [sum_filter, ← Equiv.sum_comp (order hN t)]
  simp only [Equiv.symm_apply_apply]
  have ho : ∀ k : Fin N, (order hN t k).val = xv N t k.val := fun k => rfl
  simp only [ho]
  rw [Fin.sum_univ_eq_sum_range (fun a => if a < r then h (xv N t a) else 0) N, ← sum_filter]
  congr 1
  ext a
  simp only [mem_filter, mem_range]
  omega

theorem xv_cast {N : ℕ} (hN : 0 < N) (t a : ℕ) :
    ((xv N t a : ℕ) : ZMod N) = -((sig N t a : ℕ) : ZMod N) := by
  unfold xv
  rw [ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt _ hN).le, ZMod.natCast_mod, ZMod.natCast_self,
    zero_sub]

theorem termeq {N t u : ℕ} (hN : 0 < N) (ht : t ≤ N) (hu : u < N) (a y phase : ℕ) :
    (if (y + phase + N - xv N t a + N - u) % N < t then 1 else 0) =
      G (C N u) N t (y + phase + 1 + N - t) a := by
  rw [ind_eq hN ht hu]
  unfold G
  apply diffcong hN hu
  have hx : xv N t a < N := Nat.mod_lt _ hN
  rw [← ZMod.natCast_eq_natCast_iff']
  have h1 : xv N t a ≤ y + phase + N := by omega
  have h2 : t ≤ y + phase + N - xv N t a + 1 + N := by omega
  have h3 : t ≤ y + phase + 1 + N := by omega
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, xv_cast hN, ZMod.natCast_self]
  ring

theorem modA {N : ℕ} (t q σ c phase : ℕ) (ht : t ≤ N) :
    (q + ((σ + c) % N + phase + 1 + N - t)) % N = (σ + (c + q + phase + 1 + N - t)) % N := by
  rw [← ZMod.natCast_eq_natCast_iff']
  have k1 : (((σ + c) % N + phase + 1 + N - t : ℕ) : ZMod N) =
      (σ : ZMod N) + c + phase + 1 + N - t := by
    rw [Nat.cast_sub (by omega)]; push_cast [ZMod.natCast_mod]; ring
  have k2 : ((c + q + phase + 1 + N - t : ℕ) : ZMod N) = (c : ZMod N) + q + phase + 1 + N - t := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  simp only [Nat.cast_add, k1, k2]
  ring

theorem modB {N : ℕ} (hN : 0 < N) (t q q2 phase : ℕ) (ht : t ≤ N) (hq : q ≤ N) (hq2 : q2 ≤ N) :
    (q2 + ((3 * N + t - 1 - q - q2) % N + q + phase + 1 + N - t)) % N = phase % N := by
  rw [← ZMod.natCast_eq_natCast_iff']
  have k0 : (((3 * N + t - 1 - q - q2) : ℕ) : ZMod N) = 3 * (N : ZMod N) + t - 1 - q - q2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have k1 : (((3 * N + t - 1 - q - q2) % N + q + phase + 1 + N - t : ℕ) : ZMod N) =
      (((3 * N + t - 1 - q - q2) : ℕ) : ZMod N) + q + phase + 1 + N - t := by
    rw [Nat.cast_sub (by omega)]; push_cast [ZMod.natCast_mod]; ring
  simp only [Nat.cast_add, k1, k0, ZMod.natCast_self]
  ring

theorem hitsC {N t : ℕ} (hN : 0 < N) (ht : t ≤ N) (r s : ℕ) (hr : r ≤ N) (hs : s ≤ N)
    (phase : ℕ) (u : Fin N) :
    ((((univ : Finset (Fin N)).filter (fun x => ((order hN t).symm x).val < r)) ×ˢ
      cols hN t r s).filter
      (fun z => (z.2.val + phase + N - z.1.val + N - u.val) % N < t)).card =
      C N u.val (phase + r * s * t) - C N u.val phase := by
  have hu := u.isLt
  have step1 : ((((univ : Finset (Fin N)).filter (fun x => ((order hN t).symm x).val < r)) ×ˢ
      cols hN t r s).filter
      (fun z => (z.2.val + phase + N - z.1.val + N - u.val) % N < t)).card =
      ∑ b ∈ range s, ∑ a ∈ range r,
        (if (yv N t r s b + phase + N - xv N t a + N - u.val) % N < t then 1 else 0) := by
    rw [card_filter, sum_product, sum_comm, cols, sum_image (yv_inj hN t r s hs)]
    apply sum_congr rfl; intro b _
    exact rowsum hN t r hr
      (fun x0 => if (yv N t r s b + phase + N - x0 + N - u.val) % N < t then 1 else 0)
  rw [step1]
  have hq : r / (N / Nat.gcd t N) ≤ N := le_trans (Nat.div_le_self _ _) hr
  have hq2 : s / (N / Nat.gcd (lv N t r) N) ≤ N := le_trans (Nat.div_le_self _ _) hs
  have step2 : ∀ b ∈ range s, ∑ a ∈ range r,
      (if (yv N t r s b + phase + N - xv N t a + N - u.val) % N < t then 1 else 0) =
      r / (N / Nat.gcd t N) * (t / Nat.gcd t N) +
        G (C N u.val) N (lv N t r) (c0 N t r s + r / (N / Nat.gcd t N) + phase + 1 + N - t) b := by
    intro b _
    rw [sum_congr rfl (fun a _ => termeq hN ht hu a (yv N t r s b) phase),
      total (C N u.val) (C_mono N u.val) hN (C_shift hN hu)]
    congr 1
    unfold G
    rw [show r / (N / Nat.gcd t N) + r % (N / Nat.gcd t N) * t + (yv N t r s b + phase + 1 + N - t)
      = (r / (N / Nat.gcd t N) + (yv N t r s b + phase + 1 + N - t)) + lv N t r by unfold lv; ring]
    apply diffcong hN hu
    unfold yv
    exact modA t _ _ _ phase ht
  rw [sum_congr rfl step2, sum_add_distrib, sum_const, card_range, smul_eq_mul,
    total (C N u.val) (C_mono N u.val) hN (C_shift hN hu)]
  -- the arithmetic of the two cycle levels
  have hm : (s / (N / Nat.gcd (lv N t r) N) +
      (c0 N t r s + r / (N / Nat.gcd t N) + phase + 1 + N - t)) % N = phase % N := by
    unfold c0
    exact modB hN t _ _ phase ht hq hq2
  have hLt := Lt_eq hN t
  have hLt2 := Lt_eq hN (lv N t r)
  have hr' := Nat.div_add_mod r (N / Nat.gcd t N)
  have hs' := Nat.div_add_mod s (N / Nat.gcd (lv N t r) N)
  have hl : lv N t r = r % (N / Nat.gcd t N) * t := rfl
  rw [show s / (N / Nat.gcd (lv N t r) N) + s % (N / Nat.gcd (lv N t r) N) * lv N t r +
      (c0 N t r s + r / (N / Nat.gcd t N) + phase + 1 + N - t) =
      (s / (N / Nat.gcd (lv N t r) N) + (c0 N t r s + r / (N / Nat.gcd t N) + phase + 1 + N - t))
        + s % (N / Nat.gcd (lv N t r) N) * lv N t r by ring]
  rw [diffcong hN hu _ phase _ hm]
  have mono : C N u.val phase ≤ C N u.val (phase + s % (N / Nat.gcd (lv N t r) N) * lv N t r) :=
    C_mono N u.val (Nat.le_add_right _ _)
  generalize r / (N / Nat.gcd t N) = q at *
  generalize r % (N / Nat.gcd t N) = j at *
  generalize t / Nat.gcd t N = t' at *
  generalize N / Nat.gcd t N = L at *
  generalize s / (N / Nat.gcd (lv N t r) N) = q2 at *
  generalize s % (N / Nat.gcd (lv N t r) N) = j2 at *
  generalize lv N t r / Nat.gcd (lv N t r) N = l' at *
  generalize N / Nat.gcd (lv N t r) N = L2 at *
  generalize lv N t r = l at *
  have key : r * s * t = j2 * l + N * (s * (q * t') + q2 * l') := by
    have : (r : ℤ) * s * t = j2 * l + N * (s * (q * t') + q2 * l') := by
      have a1 : ((L : ℤ) * t) = N * t' := by exact_mod_cast hLt
      have a2 : ((L : ℤ) * q + j) = r := by exact_mod_cast hr'
      have a3 : ((L2 : ℤ) * l) = N * l' := by exact_mod_cast hLt2
      have a4 : ((L2 : ℤ) * q2 + j2) = s := by exact_mod_cast hs'
      have a5 : (l : ℤ) = j * t := by exact_mod_cast hl
      linear_combination (-((s : ℤ) * t)) * a2 + ((s : ℤ) * q) * a1 - (s : ℤ) * a5 -
        (l : ℤ) * a4 + (q2 : ℤ) * a3
    exact_mod_cast this
  rw [key, show phase + (j2 * l + N * (s * (q * t') + q2 * l')) =
    phase + j2 * l + N * (s * (q * t') + q2 * l') by ring, C_shift hN hu]
  omega

theorem rows_card {N : ℕ} (hN : 0 < N) (t r : ℕ) (hr : r ≤ N) :
    ((univ : Finset (Fin N)).filter (fun x => ((order hN t).symm x).val < r)).card = r := by
  rw [card_eq_sum_ones]
  exact (rowsum hN t r hr (fun _ => 1)).trans (by simp)

theorem cols_card {N : ℕ} (hN : 0 < N) (t r s : ℕ) (hs : s ≤ N) : (cols hN t r s).card = s := by
  unfold cols
  rw [card_image_of_injOn (yv_inj hN t r s hs), card_range]

end PEqualNP.Outside.L_lib_999

open PEqualNP.Outside.L_lib_999 in
theorem PEqualNP.Outside.L_lib_999 : ∀ N t : ℕ, 0 < N → t ≤ N →
  let X := Fin N
  let hits := fun (R S : Finset X) (phase : ℕ) (u : X) =>
    ((R ×ˢ S).filter (fun z =>
      (z.2.val + phase + N - z.1.val + N - u.val) % N < t)).card
  ∃ (order : Equiv.Perm X) (cols : ℕ → ℕ → Finset X),
    let rows := fun (r : ℕ) => (Finset.univ : Finset X).filter (fun x => (order.symm x).val < r)
    (∀ r s : ℕ, r ≤ N → s ≤ N →
      (rows r).card = r ∧ (cols r s).card = s ∧
      ∀ (phase : ℕ) (u : X), hits (rows r) (cols r s) phase u =
        r*s*t/N + (if (u.val + N - phase % N) % N < (r*s*t) % N then 1 else 0)) ∧
    ∀ r s : ℕ → ℕ, (∀ i, r i ≤ N ∧ s i ≤ N) →
      let mass := fun (lo len : ℕ) => ∑ j ∈ Finset.range len, r (lo+j)*s (lo+j)*t
      ∀ (lo len : ℕ) (u : X),
        let obs := ∑ j ∈ Finset.range len,
          hits (rows (r (lo+j))) (cols (r (lo+j)) (s (lo+j))) (mass 0 (lo+j)) u
        mass lo len/N ≤ obs ∧ obs ≤ (mass lo len+N-1)/N := by
  intro N t hN ht X hits
  refine ⟨order hN t, fun r s => cols hN t r s, ?_⟩
  intro rows
  have hH : ∀ r s : ℕ, r ≤ N → s ≤ N → ∀ (phase : ℕ) (u : X),
      hits (rows r) (cols hN t r s) phase u = C N u.val (phase + r * s * t) - C N u.val phase :=
    fun r s hr hs phase u => hitsC hN ht r s hr hs phase u
  refine ⟨?_, ?_⟩
  · intro r s hr hs
    refine ⟨rows_card hN t r hr, cols_card hN t r s hs, ?_⟩
    intro phase u
    rw [hH r s hr hs]
    exact partB hN u.isLt phase (r * s * t)
  · intro r s hrs mass lo len u obs
    have hu := u.isLt
    have key : ∀ n, mass 0 n = ∑ i ∈ Finset.range n, r i * s i * t := by
      intro n; simp only [mass, zero_add]
    have hmono : Monotone (fun j => C N u.val (mass 0 (lo + j))) := by
      intro a b hab
      apply C_mono
      rw [key, key]
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
    have hobs : obs = C N u.val (mass 0 lo + mass lo len) - C N u.val (mass 0 lo) := by
      have e : ∀ j ∈ Finset.range len,
          hits (rows (r (lo + j))) (cols hN t (r (lo + j)) (s (lo + j))) (mass 0 (lo + j)) u =
          (fun j => C N u.val (mass 0 (lo + j))) (j + 1) -
            (fun j => C N u.val (mass 0 (lo + j))) j := by
        intro j _
        rw [hH _ _ (hrs _).1 (hrs _).2]
        dsimp only
        rw [key, key, show lo + (j + 1) = lo + j + 1 by ring, Finset.sum_range_succ]
      show ∑ j ∈ Finset.range len,
          hits (rows (r (lo + j))) (cols hN t (r (lo + j)) (s (lo + j))) (mass 0 (lo + j)) u = _
      rw [Finset.sum_congr rfl e, Finset.sum_range_tsub hmono]
      rw [key, key, key, add_zero, Finset.sum_range_add]
    rw [hobs, partB hN hu]
    exact ⟨Nat.le_add_right _ _, ceil_ge hN _ _⟩
