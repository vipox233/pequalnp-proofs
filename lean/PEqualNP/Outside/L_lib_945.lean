import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_945

open Finset

def F (N s j : ℕ) : ℕ := j * s / N

def Sset (N s : ℕ) : Finset (Fin N) :=
  (univ : Finset (Fin N)).filter (fun y => F N s y.val < F N s (y.val + 1))

def sig (N t k : ℕ) : ℕ := (k % (N / Nat.gcd t N)) * t + k / (N / Nat.gcd t N)

theorem F_mono (N s : ℕ) : Monotone (F N s) := fun _ _ h =>
  Nat.div_le_div_right (Nat.mul_le_mul_right s h)

theorem F_shift {N : ℕ} (s : ℕ) (hN : 0 < N) (j m : ℕ) : F N s (j + N * m) = F N s j + s * m := by
  unfold F
  rw [show (j + N * m) * s = j * s + (s * m) * N by ring, Nat.add_mul_div_right _ _ hN]

theorem F_step {N s : ℕ} (hs : s ≤ N) (hN : 0 < N) (j : ℕ) : F N s (j + 1) ≤ F N s j + 1 := by
  unfold F
  calc (j + 1) * s / N ≤ (j * s + 1 * N) / N := Nat.div_le_div_right (by nlinarith)
    _ = j * s / N + 1 := Nat.add_mul_div_right _ _ hN

theorem memS {N : ℕ} (s : ℕ) (hN : 0 < N) (j : ℕ) :
    (⟨j % N, Nat.mod_lt _ hN⟩ : Fin N) ∈ Sset N s ↔ F N s j < F N s (j + 1) := by
  simp only [Sset, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 := F_shift s hN (j % N) (j / N)
  have h2 := F_shift s hN (j % N + 1) (j / N)
  have hd := Nat.mod_add_div j N
  rw [hd] at h1
  rw [show j % N + 1 + N * (j / N) = j + 1 by omega] at h2
  rw [h1, h2]
  omega

theorem back {N : ℕ} (x u y : Fin N) :
    (x.val + u.val + (y.val + N - x.val + N - u.val) % N) % N = y.val := by
  rw [Nat.add_mod_mod, show x.val + u.val + (y.val + N - x.val + N - u.val) = y.val + N * 2 by omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt]

theorem injmod {N a i j : ℕ} (hi : i < N) (hj : j < N) (h : (a + i) % N = (a + j) % N) : i = j := by
  have h2 : i ≡ j [MOD N] := Nat.ModEq.add_left_cancel' a h
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h2

theorem tele {N s : ℕ} (hs : s ≤ N) (hN : 0 < N) (a t : ℕ) :
    ((range t).filter (fun i => F N s (a + i) < F N s (a + i + 1))).card = F N s (a + t) - F N s a := by
  rw [Finset.card_filter]
  have h : ∀ i ∈ range t, (if F N s (a + i) < F N s (a + i + 1) then 1 else 0) =
      (fun i => F N s (a + i)) (i + 1) - (fun i => F N s (a + i)) i := by
    intro i _
    have := F_step hs hN (a + i)
    have := F_mono N s (Nat.le_succ (a + i))
    simp only [← add_assoc]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl h, Finset.sum_range_tsub (fun i j hij => F_mono N s (by omega))]
  simp

theorem cnt {N s : ℕ} (hs : s ≤ N) (hN : 0 < N) (x u : Fin N) (t : ℕ) (ht : t ≤ N) :
    ((univ : Finset (Fin N)).filter (fun y => y ∈ Sset N s ∧
      (y.val + N - x.val + N - u.val) % N < t)).card =
      F N s (x.val + u.val + t) - F N s (x.val + u.val) := by
  rw [← tele hs hN]
  symm
  apply Finset.card_bij (fun i _ => (⟨(x.val + u.val + i) % N, Nat.mod_lt _ hN⟩ : Fin N))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(memS s hN _).2 hi.2, ?_⟩
    have hb := back x u ⟨(x.val + u.val + i) % N, Nat.mod_lt _ hN⟩
    have h3 := injmod (Nat.mod_lt _ hN) (show i < N by omega) hb
    dsimp only at h3 ⊢
    omega
  · intro i hi j hj h
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    exact injmod (show i < N by omega) (show j < N by omega) (Fin.mk.inj_iff.mp h)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hb := back x u y
    have hy' : (⟨(x.val + u.val + (y.val + N - x.val + N - u.val) % N) % N, Nat.mod_lt _ hN⟩ : Fin N) = y :=
      Fin.ext hb
    refine ⟨(y.val + N - x.val + N - u.val) % N, ?_, hy'⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hy.2, ?_⟩
    rw [← memS s hN, hy']
    exact hy.1


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

def ordF {N : ℕ} (hN : 0 < N) (t : ℕ) : Fin N → Fin N := fun k => ⟨sig N t k.val % N, Nat.mod_lt _ hN⟩

theorem ordF_inj {N : ℕ} (hN : 0 < N) (t : ℕ) : Function.Injective (ordF hN t) := by
  intro k k' h
  exact Fin.ext (sig_inj hN t k k' k.isLt k'.isLt (Fin.mk.inj_iff.mp h))

noncomputable def order {N : ℕ} (hN : 0 < N) (t : ℕ) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (ordF hN t) (Finite.injective_iff_bijective.mp (ordF_inj hN t))

def G (N s t u k : ℕ) : ℕ := F N s (sig N t k + u + t) - F N s (sig N t k + u)

theorem block {N s : ℕ} (hN : 0 < N) (t u q j : ℕ) (hj : j ≤ N / Nat.gcd t N) :
    ∑ i ∈ range j, G N s t u (N / Nat.gcd t N * q + i) = F N s (q + j * t + u) - F N s (q + u) := by
  have hL := L_pos hN t
  have hs : ∀ i ∈ range j, G N s t u (N / Nat.gcd t N * q + i) =
      (fun i => F N s (q + i * t + u)) (i + 1) - (fun i => F N s (q + i * t + u)) i := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold G sig
    have e1 : (N / Nat.gcd t N * q + i) % (N / Nat.gcd t N) = i := by
      rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have e2 : (N / Nat.gcd t N * q + i) / (N / Nat.gcd t N) = q := by
      rw [add_comm, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt (by omega), zero_add]
    rw [e1, e2]
    dsimp only
    rw [show i * t + q + u + t = q + (i + 1) * t + u by ring, show i * t + q + u = q + i * t + u by ring]
  rw [Finset.sum_congr rfl hs, Finset.sum_range_tsub (f := fun i => F N s (q + i * t + u))
    (fun a b hab => F_mono N s (by nlinarith))]
  simp

theorem full {N s : ℕ} (hN : 0 < N) (t u q : ℕ) :
    ∑ k ∈ range (N / Nat.gcd t N * q), G N s t u k = q * (s * (t / Nat.gcd t N)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show N / Nat.gcd t N * (q + 1) = N / Nat.gcd t N * q + N / Nat.gcd t N by ring,
      Finset.sum_range_add, ih, block hN t u q _ le_rfl]
    have hLt := Lt_eq hN t
    rw [show q + N / Nat.gcd t N * t + u = q + u + N * (t / Nat.gcd t N) by rw [hLt]; ring,
      F_shift s hN]
    rw [Nat.add_sub_cancel_left]
    ring

theorem total {N s : ℕ} (hN : 0 < N) (t u r : ℕ) :
    ∑ k ∈ range r, G N s t u k = r / (N / Nat.gcd t N) * (s * (t / Nat.gcd t N)) +
      (F N s (r / (N / Nat.gcd t N) + r % (N / Nat.gcd t N) * t + u) - F N s (r / (N / Nat.gcd t N) + u)) := by
  have hL := L_pos hN t
  conv_lhs => rw [← Nat.div_add_mod r (N / Nat.gcd t N)]
  rw [Finset.sum_range_add, full hN, block hN t u _ _ (Nat.mod_lt _ hL).le]


theorem hits_eq {N s : ℕ} (hs : s ≤ N) (hN : 0 < N) (t : ℕ) (ht : t ≤ N) (r : ℕ) (hr : r ≤ N)
    (u : Fin N) :
    ((univ : Finset (Fin N × Fin N)).filter (fun z => ((order hN t).symm z.1).val < r ∧
      z.2 ∈ Sset N s ∧ (z.2.val + N - z.1.val + N - u.val) % N < t)).card =
      ∑ k ∈ range r, G N s t u.val k := by
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have h1 : ∀ x : Fin N, (∑ y : Fin N, if (((order hN t).symm x).val < r ∧ y ∈ Sset N s ∧
      (y.val + N - x.val + N - u.val) % N < t) then 1 else 0) =
      if ((order hN t).symm x).val < r then F N s (x.val + u.val + t) - F N s (x.val + u.val)
      else 0 := by
    intro x
    split_ifs with hA
    · rw [← cnt hs hN x u t ht, Finset.card_filter]
      simp [hA]
    · simp [hA]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Equiv.sum_comp (order hN t)]
  simp only [Equiv.symm_apply_apply]
  have h2 : ∀ k : Fin N, (if k.val < r then F N s ((order hN t k).val + u.val + t) -
      F N s ((order hN t k).val + u.val) else 0) =
      (fun k => if k < r then G N s t u.val k else 0) k.val := by
    intro k
    have ho : (order hN t k).val = sig N t k.val % N := rfl
    have e := Nat.mod_add_div (sig N t k.val) N
    dsimp only
    split_ifs
    · rw [ho]
      unfold G
      rw [show sig N t k.val + u.val + t = sig N t k.val % N + u.val + t + N * (sig N t k.val / N) by
          linarith,
        show sig N t k.val + u.val = sig N t k.val % N + u.val + N * (sig N t k.val / N) by linarith,
        F_shift s hN, F_shift s hN]
      omega
    · rfl
  rw [Finset.sum_congr rfl (fun k _ => h2 k),
    Fin.sum_univ_eq_sum_range (fun k => if k < r then G N s t u.val k else 0) N, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem updiv {N : ℕ} (hN : 0 < N) (x y : ℕ) : (x + y) / N ≤ x / N + (y + N - 1) / N := by
  apply Nat.lt_succ_iff.mp
  rw [Nat.div_lt_iff_lt_mul hN]
  have h1 := Nat.div_add_mod x N
  have h2 := Nat.div_add_mod (y + N - 1) N
  have h3 := Nat.mod_lt x hN
  have h4 : y + N - 1 + 1 = y + N := by omega
  have h5 := Nat.mod_lt (y + N - 1) hN
  rw [Nat.succ_mul, add_mul]
  nlinarith

theorem bounds {N s : ℕ} (hN : 0 < N) (t r u : ℕ) :
    r * s * t / N ≤ ∑ k ∈ range r, G N s t u k ∧
      ∑ k ∈ range r, G N s t u k ≤ (r * s * t + N - 1) / N := by
  rw [total hN]
  have hLt := Lt_eq hN t
  have hr' := Nat.div_add_mod r (N / Nat.gcd t N)
  generalize r / (N / Nat.gcd t N) = q at *
  generalize r % (N / Nat.gcd t N) = j at *
  generalize t / Nat.gcd t N = t' at *
  generalize N / Nat.gcd t N = L at *
  have key : r * s * t = j * t * s + N * (q * (s * t')) := by
    have : (r : ℤ) * s * t = j * t * s + N * (q * (s * t')) := by
      have a1 : ((L : ℤ) * t) = N * t' := by exact_mod_cast hLt
      have a2 : ((L : ℤ) * q + j) = r := by exact_mod_cast hr'
      linear_combination (↑q * ↑s) * a1 - (↑s * ↑t) * a2
    exact_mod_cast this
  have hF : F N s (q + j * t + u) = ((q + u) * s + j * t * s) / N := by
    unfold F
    rw [show (q + j * t + u) * s = (q + u) * s + j * t * s by ring]
  have hF0 : F N s (q + u) = (q + u) * s / N := rfl
  have lo : (q + u) * s / N + j * t * s / N ≤ ((q + u) * s + j * t * s) / N := Nat.div_add_div_le_add_div
  have hi := updiv hN ((q + u) * s) (j * t * s)
  rw [hF, hF0, key, Nat.add_mul_div_left _ _ hN,
    show j * t * s + N * (q * (s * t')) + N - 1 = j * t * s + N - 1 + N * (q * (s * t')) by omega,
    Nat.add_mul_div_left _ _ hN]
  generalize ((q + u) * s + j * t * s) / N = D at *
  generalize (q + u) * s / N = A at *
  generalize j * t * s / N = B at *
  generalize (j * t * s + N - 1) / N = C at *
  omega

end PEqualNP.Outside.L_lib_945

open PEqualNP.Outside.L_lib_945 in
theorem PEqualNP.Outside.L_lib_945 : ∀ (N : ℕ), 0 < N →
  let X := Fin N
  let inside := fun (x y u : X) (t : ℕ) =>
    (y.val + N - x.val + N - u.val) % N < t
  ∀ s : ℕ, s ≤ N → ∃ S : Finset X, S.card = s ∧
    ∀ t : ℕ, t ≤ N → ∃ order : Equiv.Perm X,
      ∀ r : ℕ, r ≤ N → ∀ u : X,
        let hits := ((Finset.univ : Finset (X × X)).filter (fun z =>
          (order.symm z.1).val < r ∧ z.2 ∈ S ∧ inside z.1 z.2 u t)).card
        r*s*t/N ≤ hits ∧ hits ≤ (r*s*t + N - 1)/N := by
  intro N hN X inside s hs
  have hcard : (Sset N s).card = s := by
    have h := cnt hs hN ⟨0, hN⟩ ⟨0, hN⟩ N le_rfl
    have hfe : ((Finset.univ : Finset (Fin N)).filter (fun y => y ∈ Sset N s ∧
        (y.val + N - (⟨0, hN⟩ : Fin N).val + N - (⟨0, hN⟩ : Fin N).val) % N < N)) = Sset N s := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
      intro _
      exact Nat.mod_lt _ hN
    rw [hfe] at h
    rw [h]
    simp only [zero_add]
    unfold F
    rw [Nat.mul_div_cancel_left _ hN]
    simp
  refine ⟨Sset N s, hcard, ?_⟩
  intro t ht
  refine ⟨order hN t, ?_⟩
  intro r hr u
  show r*s*t/N ≤ ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => ((order hN t).symm z.1).val < r ∧
      z.2 ∈ Sset N s ∧ (z.2.val + N - z.1.val + N - u.val) % N < t)).card ∧
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => ((order hN t).symm z.1).val < r ∧
      z.2 ∈ Sset N s ∧ (z.2.val + N - z.1.val + N - u.val) % N < t)).card ≤ (r*s*t + N - 1)/N
  rw [hits_eq hs hN t ht r hr u]
  exact bounds hN t r u.val
