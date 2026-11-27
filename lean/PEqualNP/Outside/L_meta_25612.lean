import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25612_aux

def bz (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bz_xor (a b : Bool) : bz (xor a b) = bz a + bz b := by
  cases a <;> cases b <;> decide

theorem bz_and (a b : Bool) : bz (a && b) = bz a * bz b := by
  cases a <;> cases b <;> decide

theorem bz_inj {a b : Bool} (h : bz a = bz b) : a = b := by
  cases a <;> cases b <;> simp_all [bz]

theorem bz_foldl (l : List Bool) (b : Bool) :
    bz (l.foldl xor b) = bz b + (l.map bz).sum := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => simp [List.foldl_cons, ih, bz_xor, add_assoc]

theorem bz_ofFn {k : ℕ} (f : Fin k → Bool) :
    bz ((List.ofFn f).foldl xor false) = ∑ t, bz (f t) := by
  rw [bz_foldl]; simp [bz, List.sum_ofFn]

theorem zsq (x : ZMod 2) : x * x = x := by revert x; decide

theorem two_eq_zero : (2 : ZMod 2) = 0 := by decide

theorem conv_self {k : ℕ} [NeZero k] (f : Fin k → ZMod 2) (hf : ∀ x, f x * f x = f x) (s : Fin k) :
    ∑ t, f t * f (s - t) = ∑ t ∈ Finset.univ.filter (fun t => t + t = s), f t := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => t + t = s)]
  have h1 : ∑ t ∈ Finset.univ.filter (fun t => t + t = s), f t * f (s - t)
      = ∑ t ∈ Finset.univ.filter (fun t => t + t = s), f t := by
    apply Finset.sum_congr rfl
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have : s - t = t := by rw [← ht]; abel
    rw [this, hf]
  have h2 : ∑ t ∈ Finset.univ.filter (fun t => ¬ t + t = s), f t * f (s - t) = 0 := by
    apply Finset.sum_involution (fun t _ => s - t)
    · intro t _
      have : s - (s - t) = t := sub_sub_cancel s t
      rw [this, mul_comm (f (s - t)), ← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]
    · intro t ht _ h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact ht (sub_eq_iff_eq_add.mp h).symm
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      intro h; apply ht
      have e : t + t = s + s - ((s - t) + (s - t)) := by abel
      rw [e, h]; abel
    · intro t _; exact sub_sub_cancel s t
  rw [h1, h2, add_zero]

def idx (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

def proj (k : ℕ) (hk : 0 < k) (tap input : Fin k → Bool) (j : Fin k) : Bool :=
  (List.ofFn (fun t : Fin k => tap t && input (idx k hk (j.val + t.val)))).foldl xor false

theorem idx_add {k : ℕ} [NeZero k] (hk : 0 < k) (j t : Fin k) : idx k hk (j.val + t.val) = j + t := by
  apply Fin.ext; simp [idx, Fin.val_add]

theorem bz_proj {k : ℕ} [NeZero k] (hk : 0 < k) (T z : Fin k → Bool) (j : Fin k) :
    bz (proj k hk T z j) = ∑ t, bz (T t) * bz (z (j + t)) := by
  unfold proj; rw [bz_ofFn]; simp only [idx_add, bz_and]

theorem bz_proj_delta {k : ℕ} [NeZero k] (hk : 0 < k) (T : Fin k → Bool) (s j : Fin k) :
    bz (proj k hk T (fun i => decide (i = s)) j) = bz (T (s - j)) := by
  rw [bz_proj, Finset.sum_eq_single (s - j)]
  · have : j + (s - j) = s := by abel
    simp [this, bz]
  · intro t _ ht
    have : ¬ j + t = s := by intro h; exact ht (eq_sub_of_add_eq' h)
    simp [this, bz]
  · simp

theorem idem_sq {k : ℕ} [NeZero k] (hk : 0 < k) (T : Fin k → Bool)
    (hI : ∀ z : Fin k → Bool, proj k hk T (proj k hk T z) = proj k hk T z) (s : Fin k) :
    bz (T s) = ∑ t ∈ Finset.univ.filter (fun t => t + t = s), bz (T t) := by
  have h := congrArg bz (congrFun (hI (fun i => decide (i = s))) 0)
  rw [bz_proj, bz_proj_delta, sub_zero] at h
  simp only [zero_add, bz_proj_delta] at h
  rw [← h, conv_self (fun t => bz (T t)) (fun x => zsq _) s]

theorem val_nsmul' {k : ℕ} [NeZero k] (n : ℕ) (r : Fin k) : (n • r).val = (n * r.val) % k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, Fin.val_add, ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    · congr 1; ring

theorem iter {k : ℕ} [NeZero k] (f : Fin k → ZMod 2)
    (hsq : ∀ s, f s = ∑ t ∈ Finset.univ.filter (fun t => t + t = s), f t) :
    ∀ n s, f s = ∑ r ∈ Finset.univ.filter (fun r => (2 ^ n) • r = s), f r := by
  intro n
  induction n with
  | zero => intro s; simp [Finset.filter_eq']
  | succ n ih =>
    intro s
    rw [hsq s]
    have hmap : ∀ x ∈ Finset.univ.filter (fun r : Fin k => (2 ^ (n+1)) • r = s),
        (2 ^ n) • x ∈ Finset.univ.filter (fun t : Fin k => t + t = s) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [← hx, pow_succ, mul_nsmul, two_nsmul]
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    apply Finset.sum_congr rfl
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [ih y]
    apply Finset.sum_congr
    · ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; refine ⟨?_, h⟩
        rw [pow_succ, mul_nsmul, two_nsmul, h, hy]
      · intro h; exact h.2
    · intro _ _; rfl

theorem supp_dvd {k : ℕ} [NeZero k] (hk : 0 < k) (a m : ℕ) (hkm : k = 2 ^ a * m) (T : Fin k → Bool)
    (hI : ∀ z : Fin k → Bool, proj k hk T (proj k hk T z) = proj k hk T z)
    (s : Fin k) (hs : T s = true) : 2 ^ a ∣ s.val := by
  have h := iter (fun t => bz (T t)) (idem_sq hk T hI) a s
  simp only [hs] at h
  obtain ⟨r, hr⟩ : ∃ r, (2 ^ a) • r = s := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero] at h
    · exact absurd h (by decide)
    · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr; exact absurd hr (hne r)
  rw [← hr, val_nsmul']
  rw [Nat.dvd_mod_iff (by rw [hkm]; exact Dvd.intro m rfl)]
  exact Dvd.intro _ rfl

theorem exists_d {k : ℕ} [NeZero k] (T : Fin k → Bool) (h0 : T ≠ (fun _ => false))
    (h1 : T ≠ (fun t => decide (t.val = 0))) : ∃ d : Fin k, d ≠ 0 ∧ T d = true := by
  by_contra hne
  push_neg at hne
  by_cases hT : T 0 = true
  · apply h1; funext t
    by_cases ht : t = 0
    · subst ht; simp [hT]
    · have : t.val ≠ 0 := by intro h; apply ht; exact Fin.ext h
      simp only [this, decide_false]
      cases hh : T t
      · rfl
      · exact absurd hh (by simp [hne t ht])
  · apply h0; funext t
    by_cases ht : t = 0
    · subst ht; simpa using hT
    · cases hh : T t
      · rfl
      · exact absurd hh (by simp [hne t ht])

theorem period_gcd {k : ℕ} [NeZero k] (mask : Fin k → Bool) (d : Fin k) (hd : ∀ i, mask i = mask (i + d)) :
    ∀ i, mask i = mask ⟨i.val % (Nat.gcd d.val k),
      Nat.lt_of_le_of_lt (Nat.mod_le _ _) i.isLt⟩ := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  set g := Nat.gcd d.val k with hg
  have hn : ∀ n : ℕ, ∀ i, mask i = mask (i + n • d) := by
    intro n; induction n with
    | zero => intro i; simp
    | succ n ih => intro i; rw [ih i, hd (i + n • d), succ_nsmul, add_assoc]
  have hgk : g ≤ k := Nat.le_of_dvd hkpos (Nat.gcd_dvd_right _ _)

  have hG : ∀ i, mask i = mask (i + ⟨g % k, Nat.mod_lt _ hkpos⟩) := by
    intro i
    rcases Nat.lt_or_ge g k with hlt | hge
    · obtain ⟨x, -, hx⟩ := Nat.exists_mul_mod_eq_gcd (k := k) (n := d.val) hlt
      have : (x • d) = ⟨g % k, Nat.mod_lt _ hkpos⟩ := by
        apply Fin.ext; rw [val_nsmul']; simp only; rw [Nat.mod_eq_of_lt hlt, mul_comm x]; exact hx
      rw [← this]; exact hn x i
    · have : g = k := le_antisymm hgk hge
      have : (⟨g % k, Nat.mod_lt _ hkpos⟩ : Fin k) = 0 := by apply Fin.ext; simp [this]
      rw [this, add_zero]
  have gpos : 0 < g := Nat.gcd_pos_of_pos_right _ hkpos
  have key : ∀ v (hvk : v < k) (i : Fin k), i.val = v →
      mask i = mask ⟨v % g, Nat.lt_of_le_of_lt (Nat.mod_le _ _) hvk⟩ := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro hvk i hi
      by_cases hv : v < g
      · congr 1; apply Fin.ext; simp [hi, Nat.mod_eq_of_lt hv]
      · have hvg : g ≤ v := Nat.le_of_not_lt hv
        have hlt : v - g < k := by omega
        have e : (⟨v - g, hlt⟩ : Fin k) + ⟨g % k, Nat.mod_lt _ hkpos⟩ = i := by
          apply Fin.ext; simp only [Fin.val_add]
          rcases Nat.lt_or_ge g k with hlt2 | hge
          · rw [Nat.mod_eq_of_lt hlt2, Nat.sub_add_cancel hvg, Nat.mod_eq_of_lt hvk, hi]
          · have : g = k := le_antisymm hgk hge
            omega
        rw [← e, ← hG ⟨v - g, hlt⟩, ih (v - g) (by omega) hlt ⟨v - g, hlt⟩ rfl]
        congr 1; apply Fin.ext; simp only
        exact (Nat.mod_eq_sub_mod hvg).symm
  intro i
  exact key i.val i.isLt i rfl

theorem gcd_le_div {k : ℕ} [NeZero k] (a m : ℕ) (hkm : k = 2 ^ a * m) (d : Fin k) (hd0 : d ≠ 0)
    (hdv : 2 ^ a ∣ d.val) : Nat.gcd d.val k ≤ k / m.minFac := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hdpos : 0 < d.val := by
    rcases Nat.eq_zero_or_pos d.val with h | h
    · exact absurd (Fin.ext h) hd0
    · exact h
  set g := Nat.gcd d.val k
  have hgk : g ∣ k := Nat.gcd_dvd_right _ _
  have hglt : g < k := lt_of_le_of_lt (Nat.gcd_le_left _ hdpos) d.isLt
  have hag : 2 ^ a ∣ g := Nat.dvd_gcd hdv (by rw [hkm]; exact Dvd.intro m rfl)
  obtain ⟨q, hq⟩ := hgk
  obtain ⟨g', hg'⟩ := hag
  have hm : m = g' * q := by
    have h2 : 2 ^ a * m = 2 ^ a * (g' * q) := by rw [← hkm, hq, hg', mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have gpos : 0 < g := Nat.gcd_pos_of_pos_right _ hkpos
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · interval_cases q
      · omega
      · omega
    · exact h
  have hp : m.minFac ≤ q := Nat.minFac_le_of_dvd hq2 ⟨g', by rw [hm, mul_comm]⟩
  have hppos : 0 < m.minFac := Nat.minFac_pos m
  calc g = k / q := by rw [hq, Nat.mul_div_cancel _ (by omega)]
    _ ≤ k / m.minFac := Nat.div_le_div_left hp hppos

theorem count_le {k : ℕ} [NeZero k] (hk : 0 < k) (T : Fin k → Bool) (a m : ℕ) (hkm : k = 2 ^ a * m)
    (d : Fin k) (hd0 : d ≠ 0) (hTd : T d = true) (hdv : 2 ^ a ∣ d.val) :
    (Finset.univ.filter (fun mask : Fin k → Bool => ∀ i t : Fin k,
      (mask i && T t) = (mask (idx k hk (i.val + t.val)) && T (idx k hk (k - t.val))))).card
      ≤ 2 ^ (k / m.minFac) := by
  by_cases hneg : T (idx k hk (k - d.val)) = true
  · set g := Nat.gcd d.val k
    have hgk : g ≤ k := Nat.le_of_dvd hk (Nat.gcd_dvd_right _ _)
    calc _ ≤ (Finset.univ : Finset (Fin g → Bool)).card := by
          apply Finset.card_le_card_of_injOn
            (fun mask => fun r : Fin g => mask ⟨r.val, lt_of_lt_of_le r.isLt hgk⟩)
          · intro _ _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
          · intro x hx y hy hxy
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
            have px : ∀ i, x i = x (i + d) := by
              intro i; have := hx i d; rw [hTd, hneg, idx_add] at this; simpa using this
            have py : ∀ i, y i = y (i + d) := by
              intro i; have := hy i d; rw [hTd, hneg, idx_add] at this; simpa using this
            funext i
            rw [period_gcd x d px i, period_gcd y d py i]
            have := congrFun hxy ⟨i.val % g, Nat.mod_lt _ (Nat.gcd_pos_of_pos_right _ hk)⟩
            simpa using this
      _ = 2 ^ g := by simp
      _ ≤ 2 ^ (k / m.minFac) := Nat.pow_le_pow_right (by norm_num) (gcd_le_div a m hkm d hd0 hdv)
  · have hf : T (idx k hk (k - d.val)) = false := by simpa using hneg
    calc _ ≤ ({fun _ => false} : Finset (Fin k → Bool)).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          simp only [Finset.mem_singleton]
          funext i; have := hx i d; rw [hTd, hf] at this; simpa using this
      _ = 1 := by simp
      _ ≤ 2 ^ (k / m.minFac) := Nat.one_le_two_pow

theorem card_mult {k : ℕ} [NeZero k] (h p : ℕ) (hkp : k = p * h) (hh : 0 < h) :
    (Finset.univ.filter (fun t : Fin k => t.val % h = 0)).card = p := by
  have : (Finset.univ.filter (fun t : Fin k => t.val % h = 0)).card
      = (Finset.univ : Finset (Fin p)).card := by
    symm
    apply Finset.card_bij (fun c _ => (⟨c.val * h, by rw [hkp]; exact Nat.mul_lt_mul_of_pos_right c.isLt hh⟩ : Fin k))
    · intro c _; simp
    · intro c _ c' _ he
      simp only [Fin.mk.injEq] at he
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right hh he)
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      refine ⟨⟨t.val / h, ?_⟩, Finset.mem_univ _, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hh, ← hkp]; exact t.isLt
      · apply Fin.ext; simp only; exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ht)
  rw [this]; simp

theorem shift_mult {k : ℕ} [NeZero k] (hk : 0 < k) (h p : ℕ) (hkp : k = p * h) (z : Fin k → Bool) (j t : Fin k)
    (ht : t.val % h = 0) :
    ∑ u, bz (decide (u.val % h = 0)) * bz (z (j + t + u)) = ∑ u, bz (decide (u.val % h = 0)) * bz (z (j + u)) := by
  have hhk : h ∣ k := ⟨p, by rw [hkp, mul_comm]⟩
  symm
  rw [← Equiv.sum_comp (Equiv.addRight t)]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Equiv.coe_addRight]
  have e1 : ((u + t).val % h = 0) ↔ (u.val % h = 0) := by
    rw [Fin.val_add, Nat.mod_mod_of_dvd _ hhk, Nat.add_mod, ht, add_zero, Nat.mod_mod]
  have e2 : j + (u + t) = j + t + u := by abel
  rw [e2]; simp only [e1]

theorem idem_H {k : ℕ} [NeZero k] (hk : 0 < k) (h p : ℕ) (hkp : k = p * h) (hh : 0 < h) (hpodd : p % 2 = 1) :
    ∀ z : Fin k → Bool, proj k hk (fun t => decide (t.val % h = 0)) (proj k hk (fun t => decide (t.val % h = 0)) z)
      = proj k hk (fun t => decide (t.val % h = 0)) z := by
  intro z; funext j
  apply bz_inj
  rw [bz_proj, bz_proj]
  simp only [bz_proj]
  have hS : ∀ t : Fin k, bz (decide (t.val % h = 0)) *
      (∑ u, bz (decide (u.val % h = 0)) * bz (z (j + t + u)))
      = bz (decide (t.val % h = 0)) * (∑ u, bz (decide (u.val % h = 0)) * bz (z (j + u))) := by
    intro t
    by_cases ht : t.val % h = 0
    · rw [shift_mult hk h p hkp z j t ht]
    · simp [ht, bz]
  simp_rw [add_assoc] at hS ⊢
  have hS' : ∀ t : Fin k, bz (decide (t.val % h = 0)) *
      (∑ u, bz (decide (u.val % h = 0)) * bz (z (j + (t + u))))
      = bz (decide (t.val % h = 0)) * (∑ u, bz (decide (u.val % h = 0)) * bz (z (j + u))) := by
    intro t; have := hS t; simpa [add_assoc] using this
  rw [Finset.sum_congr rfl (fun t _ => hS' t), ← Finset.sum_mul]
  have hc : ∑ t : Fin k, bz (decide (t.val % h = 0)) = 1 := by
    have : ∑ t : Fin k, bz (decide (t.val % h = 0))
        = ((Finset.univ.filter (fun t : Fin k => t.val % h = 0)).card : ZMod 2) := by
      rw [Finset.card_filter]; push_cast; apply Finset.sum_congr rfl; intro t _
      by_cases ht : t.val % h = 0 <;> simp [ht, bz]
    rw [this, card_mult h p hkp hh]
    rw [← Nat.mod_add_div p 2, hpodd]; push_cast
    rw [show (2 : ZMod 2) = 0 from by decide]; ring
  rw [hc, one_mul]

theorem count_H {k : ℕ} [NeZero k] (hk : 0 < k) (a m : ℕ) (hkm : k = 2 ^ a * m) (hm1 : 1 < m) :
    (Finset.univ.filter (fun mask : Fin k → Bool => ∀ i t : Fin k,
      (mask i && decide (t.val % (k / m.minFac) = 0)) =
      (mask (idx k hk (i.val + t.val)) && decide ((idx k hk (k - t.val)).val % (k / m.minFac) = 0)))).card
      = 2 ^ (k / m.minFac) := by
  set p := m.minFac with hpdef
  obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
  have hp2 : 2 ≤ p := (Nat.minFac_prime (by omega)).two_le
  set h := k / p with hhdef
  have hkp : k = p * h := by
    rw [hhdef, hkm, hm', ← hpdef]; rw [show 2 ^ a * (p * m') = p * (2 ^ a * m') by ring]
    rw [Nat.mul_div_cancel_left _ (by omega)]
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · rw [h0, mul_zero] at hkp; omega
    · exact h0
  have hhk : h ∣ k := ⟨p, by rw [hkp, mul_comm]⟩
  have hlt : h < k := by rw [hkp]; nlinarith
  have hHneg : ∀ t : Fin k, ((idx k hk (k - t.val)).val % h = 0) ↔ (t.val % h = 0) := by
    intro t
    simp only [idx]
    rw [Nat.mod_mod_of_dvd _ hhk]
    constructor
    · intro e
      have : h ∣ k - t.val := Nat.dvd_of_mod_eq_zero e
      have h2 : h ∣ (k - t.val) + t.val := by rw [Nat.sub_add_cancel (le_of_lt t.isLt)]; exact hhk
      exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_add_right this).mp h2)
    · intro e
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub hhk (Nat.dvd_of_mod_eq_zero e))
  apply le_antisymm
  · have hd : (⟨h, hlt⟩ : Fin k) ≠ 0 := by intro e; have := congrArg Fin.val e; simp at this; omega
    have hdv : 2 ^ a ∣ h := ⟨m', by
      rw [hhdef, hkm, hm', ← hpdef, show 2 ^ a * (p * m') = p * (2 ^ a * m') by ring,
        Nat.mul_div_cancel_left _ (by omega)]⟩
    exact count_le hk _ a m hkm ⟨h, hlt⟩ hd (by simp) hdv
  · calc 2 ^ h = (Finset.univ : Finset (Fin h → Bool)).card := by simp
      _ ≤ _ := by
        apply Finset.card_le_card_of_injOn
          (fun g => fun i : Fin k => g ⟨i.val % h, Nat.mod_lt _ hh⟩)
        · intro g _
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
          intro i t
          rw [show decide ((idx k hk (k - t.val)).val % h = 0) = decide (t.val % h = 0) from decide_eq_decide.mpr (hHneg t)]
          by_cases ht : t.val % h = 0
          · simp only [ht, decide_true, Bool.and_true]
            congr 2
            simp only [idx]
            rw [Nat.mod_mod_of_dvd _ hhk, Nat.add_mod, ht, add_zero, Nat.mod_mod]
          · simp [ht]
        · intro g _ g' _ he
          funext r
          have := congrFun he ⟨r.val, lt_of_lt_of_le r.isLt (le_of_lt hlt)⟩
          simpa [Nat.mod_eq_of_lt r.isLt] using this

theorem main (k : ℕ) (hk : 0 < k) (a m : ℕ) (hkm : k = 2 ^ a * m) (hm : m % 2 = 1) :
    let admissible := fun (tap : Fin k → Bool) =>
      tap ≠ (fun _ => false) ∧ tap ≠ (fun t => decide (t.val = 0)) ∧
      ∀ z : Fin k → Bool, proj k hk tap (proj k hk tap z) = proj k hk tap z
    let countMasks := fun (tap : Fin k → Bool) =>
      (Finset.univ.filter (fun mask : Fin k → Bool =>
        ∀ i t : Fin k,
          (mask i && tap t) = (mask (idx k hk (i.val + t.val)) && tap (idx k hk (k - t.val))))).card
    ((∃ tap, admissible tap) ↔ 1 < m) ∧
      (1 < m →
        (∀ tap, admissible tap → countMasks tap ≤ 2 ^ (k / m.minFac)) ∧
        ∃ tap, admissible tap ∧ countMasks tap = 2 ^ (k / m.minFac)) := by
  have : NeZero k := ⟨by omega⟩
  intro admissible countMasks

  have hwit : 1 < m → admissible (fun t => decide (t.val % (k / m.minFac) = 0)) := by
    intro hm1
    set p := m.minFac with hpdef
    obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
    have hp2 : 2 ≤ p := (Nat.minFac_prime (by omega)).two_le
    have hpodd : p % 2 = 1 := by
      rcases (Nat.minFac_prime (by omega : m ≠ 1)).eq_two_or_odd with h2 | h2
      · exfalso; have : 2 ∣ m := by rw [← hpdef] at h2; rw [← h2]; exact Nat.minFac_dvd m
        omega
      · exact h2
    set h := k / p with hhdef
    have hkp : k = p * h := by
      rw [hhdef, hkm, hm', ← hpdef]; rw [show 2 ^ a * (p * m') = p * (2 ^ a * m') by ring]
      rw [Nat.mul_div_cancel_left _ (by omega)]
    have hh : 0 < h := by
      rcases Nat.eq_zero_or_pos h with h0 | h0
      · rw [h0, mul_zero] at hkp; omega
      · exact h0
    have hlt : h < k := by rw [hkp]; nlinarith
    refine ⟨?_, ?_, idem_H hk h p hkp hh hpodd⟩
    · intro e; have := congrFun e 0; simp at this
    · intro e; have := congrFun e ⟨h, hlt⟩; simp at this; omega
  have hsupp : ∀ tap, admissible tap → ∃ d : Fin k, d ≠ 0 ∧ tap d = true ∧ 2 ^ a ∣ d.val := by
    intro tap ⟨h0, h1, hI⟩
    obtain ⟨d, hd0, hTd⟩ := exists_d tap h0 h1
    exact ⟨d, hd0, hTd, supp_dvd hk a m hkm tap hI d hTd⟩
  refine ⟨⟨?_, fun hm1 => ⟨_, hwit hm1⟩⟩, fun hm1 => ⟨?_, ⟨_, hwit hm1, count_H hk a m hkm hm1⟩⟩⟩
  · rintro ⟨tap, htap⟩
    obtain ⟨d, hd0, -, hdv⟩ := hsupp tap htap
    by_contra hle
    have hm1 : m = 1 := by omega
    have hdk : d.val < 2 ^ a := by
      have h1 : d.val < k := d.isLt
      have h2 : k = 2 ^ a := by rw [hkm, hm1, mul_one]
      omega
    have : d.val = 0 := Nat.eq_zero_of_dvd_of_lt hdv hdk
    exact hd0 (Fin.ext this)
  · intro tap htap
    obtain ⟨d, hd0, hTd, hdv⟩ := hsupp tap htap
    exact count_le hk tap a m hkm d hd0 hTd hdv

end PEqualNP.Outside.L_meta_25612_aux

theorem PEqualNP.Outside.L_meta_25612 : (∀ (k : ℕ) (hk : 0 < k) (a m : ℕ), k = 2 ^ a * m → m % 2 = 1 →
  let index := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let proj := fun (tap input : Fin k → Bool) (j : Fin k) =>
    (List.ofFn (fun t : Fin k => tap t && input (index (j.val + t.val)))).foldl xor false
  let admissible := fun (tap : Fin k → Bool) =>
    tap ≠ (fun _ => false) ∧ tap ≠ (fun t => decide (t.val = 0)) ∧
    ∀ z : Fin k → Bool, proj tap (proj tap z) = proj tap z
  let countMasks := fun (tap : Fin k → Bool) =>
    (Finset.univ.filter (fun mask : Fin k → Bool =>
      ∀ i t : Fin k,
        (mask i && tap t) = (mask (index (i.val + t.val)) && tap (index (k - t.val))))).card
  ((∃ tap, admissible tap) ↔ 1 < m) ∧
    (1 < m →
      (∀ tap, admissible tap → countMasks tap ≤ 2 ^ (k / m.minFac)) ∧
      ∃ tap, admissible tap ∧ countMasks tap = 2 ^ (k / m.minFac))) := by
  intro k hk a m hkm hm
  exact PEqualNP.Outside.L_meta_25612_aux.main k hk a m hkm hm
