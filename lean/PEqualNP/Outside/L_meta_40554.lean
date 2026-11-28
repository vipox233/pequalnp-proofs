import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40554

open Fin.CommRing

section cyc
variable {m : ℕ} [NeZero m]

abbrev Gd (v : Fin m → Bool) : Prop :=
  ∀ t : Fin m, xor (v t) (xor (v (t+1)) (v (t+1+1))) = false

theorem b3 : ∀ a b c : Bool, xor a (xor b c) = false → c = xor a b := by decide

theorem sq_step (v : Fin m → Bool) (hv : Gd v) (n : ℕ) :
    v ((n+2 : ℕ) : Fin m) = xor (v (n : Fin m)) (v ((n+1 : ℕ) : Fin m)) := by
  have h := hv (n : Fin m)
  have e1 : ((n : Fin m) + 1) = ((n+1 : ℕ) : Fin m) := by push_cast; rfl
  have e2 : ((n : Fin m) + 1 + 1) = ((n+2 : ℕ) : Fin m) := by push_cast; ring
  rw [e2, e1] at h
  exact b3 _ _ _ h

theorem s3 (v : Fin m → Bool) (hv : Gd v) (n : ℕ) :
    v ((n+3 : ℕ) : Fin m) = v (n : Fin m) := by
  have h1 := sq_step v hv (n+1)
  have h0 := sq_step v hv n
  rw [show n + 1 + 2 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega, h0] at h1
  rw [h1]; cases v (n : Fin m) <;> cases v ((n+1 : ℕ) : Fin m) <;> rfl

theorem smod (v : Fin m → Bool) (hv : Gd v) (n : ℕ) :
    v (n : Fin m) = v ((n % 3 : ℕ) : Fin m) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 3
    · rw [Nat.mod_eq_of_lt hn]
    · have e : n = (n - 3) + 3 := by omega
      rw [e, s3 v hv, ih (n-3) (by omega)]
      rw [show (n - 3 + 3) % 3 = (n - 3) % 3 by omega]

theorem sper (v : Fin m → Bool) (n : ℕ) : v ((n + m : ℕ) : Fin m) = v (n : Fin m) := by
  rw [Nat.cast_add, Fin.natCast_self, add_zero]

theorem b3z : ∀ a b c : Bool, a = b → b = c → c = xor a b → a = false ∧ b = false ∧ c = false := by
  decide

theorem gd_zero (hm : ¬ 3 ∣ m) (v : Fin m → Bool) (hv : Gd v) : v = fun _ => false := by
  have key : ∀ a : ℕ, v (a : Fin m) = v (((a + m) % 3 : ℕ) : Fin m) := fun a => by
    rw [← sper v a, smod v hv]
  have h2 := sq_step v hv 0
  rw [show (0:ℕ) + 2 = 2 from rfl, show (0:ℕ) + 1 = 1 from rfl] at h2
  have hz : v ((0 : ℕ) : Fin m) = false ∧ v ((1 : ℕ) : Fin m) = false ∧
      v ((2 : ℕ) : Fin m) = false := by
    rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with h | h
    · have q0 := key 0
      have q1 := key 1
      rw [show (0 + m) % 3 = 1 by omega] at q0
      rw [show (1 + m) % 3 = 2 by omega] at q1
      exact b3z _ _ _ q0 q1 h2
    · have q0 := key 0
      have q1 := key 1
      rw [show (0 + m) % 3 = 2 by omega] at q0
      rw [show (1 + m) % 3 = 0 by omega] at q1
      exact b3z _ _ _ q1.symm (q1.trans q0) h2
  funext t
  rw [← Fin.cast_val_eq_self t, smod v hv]
  have hr : t.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize t.val % 3 = r at hr ⊢
  interval_cases r
  · exact hz.1
  · exact hz.2.1
  · exact hz.2.2

def Pt (a b : Bool) (r : ℕ) : Bool := if r = 0 then a else if r = 1 then b else xor a b
def Ps (a b : Bool) (t : Fin m) : Bool := Pt a b (t.val % 3)

theorem vs (h3 : 3 ∣ m) (t : Fin m) : (t+1).val % 3 = (t.val % 3 + 1) % 3 := by
  have e : t + 1 = ((t.val + 1 : ℕ) : Fin m) := by simp
  rw [e, Fin.val_natCast, Nat.mod_mod_of_dvd _ h3]; omega

theorem ps_gd (h3 : 3 ∣ m) (a b : Bool) : Gd (Ps (m := m) a b) := by
  intro t
  simp only [Ps]
  rw [vs h3 (t+1), vs h3 t]
  have hr : t.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize t.val % 3 = r at hr ⊢
  interval_cases r <;> simp [Pt] <;> cases a <;> cases b <;> rfl

theorem ps0 (a b : Bool) : Ps (m := m) a b 0 = a := by
  simp [Ps, Pt]

theorem ps1 (h3 : 3 ∣ m) (a b : Bool) : Ps (m := m) a b 1 = b := by
  have := vs h3 (0 : Fin m)
  rw [zero_add] at this
  simp only [Ps, this, Fin.val_zero]
  simp [Pt]

theorem ps_eq (v : Fin m → Bool) (hv : Gd v) : Ps (v 0) (v 1) = v := by
  funext t
  have h2 := sq_step v hv 0
  rw [show (0:ℕ) + 2 = 2 from rfl, show (0:ℕ) + 1 = 1 from rfl, Nat.cast_zero, Nat.cast_one] at h2
  simp only [Ps]
  rw [← Fin.cast_val_eq_self t, smod v hv]
  simp only [Fin.cast_val_eq_self]
  have hr : t.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize t.val % 3 = r at hr ⊢
  interval_cases r
  · simp [Pt]
  · simp [Pt]
  · simp only [Nat.cast_ofNat] at h2
    simp [Pt, h2]

theorem gdCard : (Finset.univ.filter (fun v : Fin m → Bool => Gd v)).card =
    if 3 ∣ m then 4 else 1 := by
  split_ifs with h3
  · have e : Finset.univ.filter (fun v : Fin m → Bool => Gd v) =
        (Finset.univ : Finset (Bool × Bool)).image (fun p => Ps p.1 p.2) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.exists]
      constructor
      · intro hv; exact ⟨v 0, v 1, ps_eq v hv⟩
      · rintro ⟨a, b, rfl⟩; exact ps_gd h3 a b
    rw [e, Finset.card_image_of_injective]
    · rfl
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [ps0, ps1 h3] at h0 h1
      rw [h0, h1]
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => false, ?_⟩
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact gd_zero h3 v
    · rintro rfl t; rfl

end cyc

section ker
variable {k : ℕ} [NeZero k]

theorem ixN (n : ℕ) (h : n % k < k) : (⟨n % k, h⟩ : Fin k) = (n : Fin k) := by
  ext; simp [Fin.val_natCast]

theorem castA (q : Fin k) (s : ℕ) : ((q.val + s : ℕ) : Fin k) = q + (s : Fin k) := by
  push_cast; simp

theorem castS (q : Fin k) (s : ℕ) : ((q.val + k - s % k : ℕ) : Fin k) = q - (s : Fin k) := by
  have h1 : s % k ≤ q.val + k := by have := Nat.mod_lt s (NeZero.pos k); omega
  rw [Nat.cast_sub h1]
  have h2 : ((s % k : ℕ) : Fin k) = (s : Fin k) := by
    ext; simp [Fin.val_natCast]
  push_cast
  rw [h2]
  simp

abbrev Kc (c : Fin k) (w : Fin k → Bool) : Prop :=
  ∀ i : Fin k, xor (w i) (xor (w (i+c)) (w (i+c+c))) = false

theorem castEq (a b : ℕ) (h : a ≡ b [MOD k]) : (a : Fin k) = (b : Fin k) := by
  ext; rw [Fin.val_natCast, Fin.val_natCast]; exact h

theorem kerCard (n : ℕ) :
    (Finset.univ.filter (fun w : Fin k → Bool => Kc (n : Fin k) w)).card =
      2 ^ (if 3 ∣ k / Nat.gcd k n then 2 * Nat.gcd k n else 0) := by
  have hk : 0 < k := NeZero.pos k
  have hg0 : 0 < Nat.gcd k n := Nat.gcd_pos_of_pos_left n hk
  have hgk : Nat.gcd k n ∣ k := Nat.gcd_dvd_left k n
  have hgn : Nat.gcd k n ∣ n := Nat.gcd_dvd_right k n
  have hcop : Nat.gcd (k / Nat.gcd k n) (n / Nat.gcd k n) = 1 := Nat.coprime_div_gcd_div_gcd hg0
  generalize hG : Nat.gcd k n = g at hg0 hgk hgn hcop ⊢
  generalize hM : k / g = m at hcop ⊢
  generalize hN : n / g = n' at hcop
  have hkm : g * m = k := by rw [← hM]; exact Nat.mul_div_cancel' hgk
  have hnn : g * n' = n := by rw [← hN]; exact Nat.mul_div_cancel' hgn
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hkm; omega
    · exact h
  have : NeZero m := ⟨hm0.ne'⟩
  let B : Fin g × Fin m → Fin k := fun p => ((p.1.val + p.2.val * n : ℕ) : Fin k)
  have Binj : Function.Injective B := by
    rintro ⟨j, t⟩ ⟨j', t'⟩ h
    have h' : j.val + t.val * n ≡ j'.val + t'.val * n [MOD k] := by
      have := congrArg Fin.val h
      simp only [B, Fin.val_natCast] at this
      exact this
    have hj : j.val = j'.val := by
      have h2 := h'.of_dvd hgk
      have e1 : (j.val + t.val * n) % g = j.val := by
        rw [← hnn, show t.val * (g * n') = g * (t.val * n') by ring, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt j.isLt]
      have e2 : (j'.val + t'.val * n) % g = j'.val := by
        rw [← hnn, show t'.val * (g * n') = g * (t'.val * n') by ring, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt j'.isLt]
      unfold Nat.ModEq at h2
      rw [e1, e2] at h2; exact h2
    have ht : t.val = t'.val := by
      rw [hj] at h'
      have h3 := Nat.ModEq.add_left_cancel' _ h'
      rw [← hnn, ← hkm, show t.val * (g * n') = g * (t.val * n') by ring,
        show t'.val * (g * n') = g * (t'.val * n') by ring] at h3
      have h4 := Nat.ModEq.mul_left_cancel' hg0.ne' h3
      have h5 := Nat.ModEq.cancel_right_of_coprime hcop h4
      unfold Nat.ModEq at h5
      rwa [Nat.mod_eq_of_lt t.isLt, Nat.mod_eq_of_lt t'.isLt] at h5
    rw [Fin.ext hj, Fin.ext ht]
  have Bbij : Function.Bijective B := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨Binj, by simp [Fintype.card_prod, Fintype.card_fin, hkm]⟩
  have Bsucc : ∀ j t, B (j, t+1) = B (j, t) + (n : Fin k) := by
    intro j t
    simp only [B]
    rw [← Nat.cast_add]
    apply castEq
    have e : (t+1).val = (t.val + 1) % m := by
      rw [show t + 1 = ((t.val + 1 : ℕ) : Fin m) by simp, Fin.val_natCast]
    rw [e]
    have hmn : k ∣ m * n := ⟨n', by rw [← hkm, ← hnn]; ring⟩
    have h1 : (t.val + 1) % m * n ≡ (t.val + 1) * n [MOD k] :=
      ((Nat.mod_modEq (t.val+1) m).mul_right' n).of_dvd hmn
    have h2 := h1.add_left j.val
    rw [show j.val + (t.val + 1) * n = j.val + t.val * n + n by ring] at h2
    exact h2
  have hK : ∀ w : Fin k → Bool, Kc (n : Fin k) w ↔ ∀ j, Gd (fun t => w (B (j, t))) := by
    intro w; constructor
    · intro h j t
      simp only [Bsucc]
      exact h _
    · intro h i
      obtain ⟨⟨j, t⟩, rfl⟩ := Bbij.2 i
      have := h j t
      simp only [Bsucc] at this
      exact this
  let e := Equiv.ofBijective B Bbij
  have hc : (Finset.univ.filter (fun w : Fin k → Bool => Kc (n : Fin k) w)).card =
      (Fintype.piFinset (fun _ : Fin g =>
        Finset.univ.filter (fun v : Fin m → Bool => Gd v))).card := by
    apply Finset.card_bij' (fun w _ => fun j t => w (B (j, t)))
      (fun f _ => fun i => f (e.symm i).1 (e.symm i).2)
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rw [Fintype.mem_piFinset]; intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hK w).1 hw j
    · intro f hf
      rw [Fintype.mem_piFinset] at hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      rw [hK]; intro j
      have : (fun t => f (e.symm (B (j, t))).1 (e.symm (B (j, t))).2) = f j := by
        funext t
        have : e.symm (B (j, t)) = (j, t) := Equiv.ofBijective_symm_apply_apply B Bbij (j, t)
        rw [this]
      rw [this]; exact hf j
    · intro w _
      funext i
      show w (B (e.symm i)) = w i
      rw [show B (e.symm i) = i from Equiv.ofBijective_apply_symm_apply B Bbij i]
    · intro f _
      funext j t
      have : e.symm (B (j, t)) = (j, t) := Equiv.ofBijective_symm_apply_apply B Bbij (j, t)
      simp only [this]
  rw [hc, Fintype.card_piFinset_const, gdCard]
  split_ifs
  · rw [pow_mul]; norm_num
  · simp

end ker

section alg
variable {k : ℕ} [NeZero k]

def Mx (c : Fin k) (x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (x (i - c)) (xor (x i) (x (i + c)))
def Rt (a : Fin k) (x : Fin k → Bool) (i : Fin k) : Bool := x (i - a)
def Ch (z : Fin k → Bool) (i : Fin k) : Bool := xor (z i) (!(z (i + 1)) && z (i + 2))
def Vw (c A F : Fin k) (x : Fin k → Bool) (b : Bool) (i : Fin k) : Bool :=
  xor (Ch (fun t => xor (Mx c (Rt A x) t) b) i) (Rt F x i)
def Dz (z : Fin k → Bool) (i : Fin k) : Bool := !(xor (z (i + 1)) (z (i + 2)))
def Pr (c A F : Fin k) (x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (x i) (Dz (Mx c (Rt A x)) (i + F))
abbrev Cd (c A F : Fin k) (x : Fin k → Bool) : Prop :=
  ∀ i, Mx c (Rt A (Pr c A F x)) i = !(Mx c (Rt A x) i)

theorem VwAt (c A F : Fin k) (x : Fin k → Bool) (b : Bool) (i : Fin k) :
    Vw c A F x b i = xor (xor (xor (Mx c (Rt A x) i) b)
      (!(xor (Mx c (Rt A x) (i+1)) b) && xor (Mx c (Rt A x) (i+2)) b)) (x (i - F)) := rfl

theorem bV1 : ∀ a0 a1 a2 p b0 b1 b2 q : Bool,
    xor (xor (xor a0 false) (!(xor a1 false) && xor a2 false)) p =
      xor (xor (xor b0 false) (!(xor b1 false) && xor b2 false)) q →
    xor (xor (xor a0 true) (!(xor a1 true) && xor a2 true)) p =
      xor (xor (xor b0 true) (!(xor b1 true) && xor b2 true)) q →
    xor a1 b1 = xor a2 b2 := by decide

theorem bV2 : ∀ a0 a1 a2 p q : Bool,
    xor (xor (xor a0 false) (!(xor a1 false) && xor a2 false)) q =
      xor (xor (xor a0 false) (!(xor a1 false) && xor a2 false)) p → q = p := by decide

theorem bV3 : ∀ a0 a1 a2 p q : Bool,
    xor (xor (xor (!a0) false) (!(xor (!a1) false) && xor (!a2) false)) q =
      xor (xor (xor a0 false) (!(xor a1 false) && xor a2 false)) p →
    q = xor p (!(xor a1 a2)) := by decide

theorem bV4 : ∀ a0 a1 a2 p b : Bool,
    xor (xor (xor (!a0) b) (!(xor (!a1) b) && xor (!a2) b)) (xor p (!(xor a1 a2))) =
      xor (xor (xor a0 b) (!(xor a1 b) && xor a2 b)) p := by decide

theorem bxf : ∀ a b : Bool, xor a b = false → a = b := by decide
theorem bxt : ∀ a b : Bool, xor a b = true → a = !b := by decide
theorem bnn : ∀ a : Bool, a = !a → False := by decide

theorem constF (u : Fin k → Bool) (h : ∀ j, u (j+1) = u j) : ∀ j, u j = u 0 := by
  have hn : ∀ n : ℕ, u (n : Fin k) = u 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, h, ih]
  intro j; rw [← Fin.cast_val_eq_self j]; exact hn _

theorem shift12 (u : Fin k → Bool) (h : ∀ j, u (j+1) = u (j+2)) : ∀ j, u (j+1) = u j := by
  intro j
  have := h (j - 1)
  rw [show j - 1 + 1 = j by ring, show j - 1 + 2 = j + 1 by ring] at this
  exact this.symm

theorem pairIff (c A F : Fin k) (x y : Fin k → Bool) :
    Vw c A F y = Vw c A F x ↔ y = x ∨ (y = Pr c A F x ∧ Cd c A F x) := by
  constructor
  · intro h
    have e : ∀ b i, Vw c A F y b i = Vw c A F x b i := fun b i => congrFun (congrFun h b) i
    have hd : ∀ i, xor (Mx c (Rt A y) (i+1)) (Mx c (Rt A x) (i+1)) =
        xor (Mx c (Rt A y) (i+2)) (Mx c (Rt A x) (i+2)) := by
      intro i
      have h0 := e false i
      have h1 := e true i
      rw [VwAt, VwAt] at h0 h1
      exact bV1 _ _ _ _ _ _ _ _ h0 h1
    have hc := constF (fun j => xor (Mx c (Rt A y) j) (Mx c (Rt A x) j))
      (shift12 (fun j => xor (Mx c (Rt A y) j) (Mx c (Rt A x) j)) hd)
    cases hb : xor (Mx c (Rt A y) 0) (Mx c (Rt A x) 0)
    · left
      have hR : ∀ j, Mx c (Rt A y) j = Mx c (Rt A x) j := fun j => bxf _ _ ((hc j).trans hb)
      funext j
      have := e false (j + F)
      rw [VwAt, VwAt, hR (j+F), hR (j+F+1), hR (j+F+2), add_sub_cancel_right] at this
      exact bV2 _ _ _ _ _ this
    · right
      have hR : ∀ j, Mx c (Rt A y) j = !(Mx c (Rt A x) j) := fun j => bxt _ _ ((hc j).trans hb)
      have hy : y = Pr c A F x := by
        funext j
        have := e false (j + F)
        rw [VwAt, VwAt, hR (j+F), hR (j+F+1), hR (j+F+2), add_sub_cancel_right] at this
        rw [bV3 _ _ _ _ _ this]
        rfl
      refine ⟨hy, ?_⟩
      intro i; rw [← hy]; exact hR i
  · rintro (rfl | ⟨rfl, hc⟩)
    · rfl
    · funext b i
      rw [VwAt, VwAt, hc i, hc (i+1), hc (i+2)]
      have : Pr c A F x (i - F) = xor (x (i - F))
          (!(xor (Mx c (Rt A x) (i+1)) (Mx c (Rt A x) (i+2)))) := by
        simp only [Pr, Dz, sub_add_cancel]
      rw [this]; exact bV4 _ _ _ _ _

theorem bL : ∀ a b c d e f : Bool,
    xor (xor a d) (xor (xor b e) (xor c f)) = xor (xor a (xor b c)) (xor d (xor e f)) := by
  decide

theorem RLin (c A : Fin k) (x q : Fin k → Bool) (i : Fin k) :
    Mx c (Rt A (fun j => xor (x j) (q j))) i = xor (Mx c (Rt A x) i) (Mx c (Rt A q) i) := by
  simp only [Mx, Rt]; exact bL _ _ _ _ _ _

theorem bQ : ∀ a b c d e f : Bool,
    xor (!(xor a b)) (xor (!(xor c d)) (!(xor e f))) =
      !(xor (xor a (xor c e)) (xor b (xor d f))) := by decide

theorem Rq (c A F : Fin k) (z : Fin k → Bool) (i : Fin k) :
    Mx c (Rt A (fun j => Dz z (j + F))) i =
      !(xor (Mx c z (i - A + F + 1)) (Mx c z (i - A + F + 2))) := by
  simp only [Mx, Rt, Dz]
  rw [show i - c - A + F + 1 = i - A + F + 1 - c by ring,
    show i - c - A + F + 2 = i - A + F + 2 - c by ring,
    show i + c - A + F + 1 = i - A + F + 1 + c by ring,
    show i + c - A + F + 2 = i - A + F + 2 + c by ring]
  exact bQ _ _ _ _ _ _

theorem bM : ∀ a b m d e : Bool,
    xor (xor a (xor b m)) (xor (xor b (xor m d)) (xor m (xor d e))) = xor a (xor m e) := by
  decide

theorem MM (c : Fin k) (z : Fin k → Bool) : Mx c (Mx c z) = Mx (c + c) z := by
  funext i
  simp only [Mx]
  rw [show i - c + c = i by ring, show i + c - c = i by ring,
    show i - c - c = i - (c + c) by ring, show i + c + c = i + (c + c) by ring]
  exact bM _ _ _ _ _

theorem bxn : ∀ a s : Bool, (xor a s = !a) ↔ s = true := by decide
theorem bnx : ∀ p q : Bool, ((!(xor p q)) = true) ↔ p = q := by decide

theorem cdIff (c A F : Fin k) (x : Fin k → Bool) :
    Cd c A F x ↔ ∀ j, Mx (c+c) (Rt A x) j = Mx (c+c) (Rt A x) 0 := by
  have e : ∀ i, Mx c (Rt A (Pr c A F x)) i = xor (Mx c (Rt A x) i)
      (!(xor (Mx (c+c) (Rt A x) (i - A + F + 1)) (Mx (c+c) (Rt A x) (i - A + F + 2)))) := by
    intro i
    rw [show Pr c A F x = fun j => xor (x j) (Dz (Mx c (Rt A x)) (j + F)) from rfl, RLin, Rq, MM]
  have key : Cd c A F x ↔ ∀ i, Mx (c+c) (Rt A x) (i - A + F + 1) =
      Mx (c+c) (Rt A x) (i - A + F + 2) := by
    unfold Cd; apply forall_congr'; intro i; rw [e i, bxn, bnx]
  rw [key]
  constructor
  · intro h
    apply constF
    apply shift12
    intro j
    have := h (j + A - F)
    rwa [show j + A - F - A + F = j by ring] at this
  · intro h i
    rw [h, h (i - A + F + 2)]

-- The halving lemma below follows the count lemma of the merged
-- PEqualNP.Outside.L_meta_25883 (credit to its author), rewritten for Fin k to Bool words.
theorem halve {α : Type*} [DecidableEq α] (S : Finset α) (f : α → α) (hS : ∀ x ∈ S, f x ∈ S)
    (hinv : ∀ x, f (f x) = x) (p : α → Bool) (hp : ∀ x ∈ S, p (f x) = !p x) (b : Bool) :
    2 * (S.filter (fun x => p x = b)).card = S.card := by
  have e : (S.filter (fun x => p x = b)).card = (S.filter (fun x => ¬ p x = b)).card := by
    apply Finset.card_bij' (fun x _ => f x) (fun x _ => f x)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨hS x hx.1, ?_⟩
      rw [hp x hx.1, hx.2]; cases b <;> simp
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨hS x hx.1, ?_⟩
      have h2 := hx.2
      rw [hp x hx.1]; revert h2; cases b <;> cases p x <;> simp
    · intro x _; exact hinv x
    · intro x _; exact hinv x
  have := Finset.card_filter_add_card_filter_not (s := S) (fun x => p x = b)
  omega

theorem bN : ∀ a b c : Bool, xor (!a) (xor (!b) (!c)) = !(xor a (xor b c)) := by decide

theorem mxNeg (C : Fin k) (w : Fin k → Bool) (j : Fin k) :
    Mx C (fun i => !(w i)) j = !(Mx C w j) := by
  simp only [Mx]; exact bN _ _ _

theorem mxK (C : Fin k) (w : Fin k → Bool) : (∀ j, Mx C w j = false) ↔ Kc C w := by
  constructor
  · intro h i
    have := h (i + C)
    simp only [Mx, add_sub_cancel_right] at this
    exact this
  · intro h j
    have := h (j - C)
    simp only [Mx]
    rwa [show j - C + C = j by ring] at this

theorem cdCard (c A F : Fin k) (n : ℕ) (hn : c + c = (n : Fin k)) :
    (Finset.univ.filter (fun x : Fin k → Bool => Cd c A F x)).card =
      2 * 2 ^ (if 3 ∣ k / Nat.gcd k n then 2 * Nat.gcd k n else 0) := by
  rw [← kerCard n]
  have h1 : (Finset.univ.filter (fun x : Fin k → Bool => Cd c A F x)).card =
      (Finset.univ.filter (fun w : Fin k → Bool => ∀ j, Mx (c+c) w j = Mx (c+c) w 0)).card := by
    apply Finset.card_bij' (fun x _ => Rt A x) (fun w _ => fun i => w (i + A))
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (cdIff c A F x).1 hx
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [cdIff]
      have : Rt A (fun i => w (i + A)) = w := by funext i; simp [Rt]
      rw [this]; exact hw
    · intro x _; funext i; simp [Rt]
    · intro w _; funext i; simp [Rt]
  rw [h1, hn]
  have hS : ∀ w ∈ Finset.univ.filter (fun w : Fin k → Bool =>
      ∀ j, Mx (n : Fin k) w j = Mx (n : Fin k) w 0),
      (fun i => !(w i)) ∈ Finset.univ.filter (fun w : Fin k → Bool =>
      ∀ j, Mx (n : Fin k) w j = Mx (n : Fin k) w 0) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    intro j; rw [mxNeg, mxNeg, hw j]
  have hh := halve _ (fun w i => !(w i)) hS (fun w => by funext i; simp)
    (fun w => Mx (n : Fin k) w 0) (fun w _ => mxNeg _ w 0) false
  rw [← hh]
  congr 2
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← mxK]
  constructor
  · rintro ⟨h1, h2⟩ j; rw [h1 j, h2]
  · intro h; exact ⟨fun j => by rw [h j, h 0], h 0⟩

theorem fib (c A F : Fin k) (x : Fin k → Bool) :
    (Finset.univ.filter (fun y => Vw c A F y = Vw c A F x)).card =
      if Cd c A F x then 2 else 1 := by
  split_ifs with hc
  · have hne : Pr c A F x ≠ x := by
      intro h; have := hc 0; rw [h] at this; exact bnn _ this
    have : Finset.univ.filter (fun y => Vw c A F y = Vw c A F x) = {x, Pr c A F x} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, pairIff, eq_true hc, and_true]
    rw [this, Finset.card_pair hne.symm]
  · have : Finset.univ.filter (fun y => Vw c A F y = Vw c A F x) = {x} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, pairIff,
        eq_false hc, and_false, or_false]
    rw [this, Finset.card_singleton]

end alg

end PEqualNP.Outside.L_meta_40554

open Fin.CommRing PEqualNP.Outside.L_meta_40554 in
theorem PEqualNP.Outside.L_meta_40554 : ∀ (k : Nat) (hk : 0 < k) (d ini fin : Nat),
  let W := Fin k → Bool
  let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (a : Nat) (x : W) (i : Fin k) => x (ix (i.val+k-a % k))
  let mix := fun (gap : Nat) (x : W) (i : Fin k) =>
    xor (x (ix (i.val+k-gap % k))) (xor (x i) (x (ix (i.val+gap))))
  let chi := fun (x : W) (i : Fin k) =>
    xor (x i) (!(x (ix (i.val+1))) && x (ix (i.val+2)))
  let view := fun (x : W) (b : Bool) (i : Fin k) =>
    xor (chi (fun t => xor (mix d (rot ini x) t) b) i) (rot fin x i)
  let keys : Finset W := Finset.univ
  let paired := fun x : W => (keys.filter (fun y => view y = view x)).card
  let g := Nat.gcd k (2*d)
  let e := if 3 ∣ k/g then 2*g else 0
  (∀ x, paired x ≤ 2) ∧
  (keys.filter (fun x => paired x = 2)).card = 2 * 2^e ∧
  (keys.image view).card + 2^e = 2^k := by
  intro k hk d ini fin W ix rot mix chi view keys paired g e
  have : NeZero k := ⟨hk.ne'⟩
  have hview : view = Vw (d : Fin k) (ini : Fin k) (fin : Fin k) := by
    funext x b i
    simp only [view, chi, mix, rot, ix, ixN, castA, castS, Vw, Ch, Mx, Rt, Nat.cast_one,
      Nat.cast_ofNat]
  have hpaired : ∀ x, paired x = if Cd (d : Fin k) (ini : Fin k) (fin : Fin k) x then 2 else 1 := by
    intro x
    show (Finset.univ.filter (fun y => view y = view x)).card = _
    rw [hview]; exact fib _ _ _ x
  have hsame : ∀ x y, view y = view x → paired y = paired x := by
    intro x y h
    show (Finset.univ.filter (fun z => view z = view y)).card =
      (Finset.univ.filter (fun z => view z = view x)).card
    rw [h]
  have hcard : (Finset.univ.filter (fun x : Fin k → Bool =>
      Cd (d : Fin k) (ini : Fin k) (fin : Fin k) x)).card = 2 * 2 ^ e :=
    cdCard _ _ _ (2 * d) (by push_cast; ring)
  have hP : keys.filter (fun x => paired x = 2) = Finset.univ.filter (fun x : Fin k → Bool =>
      Cd (d : Fin k) (ini : Fin k) (fin : Fin k) x) := by
    ext x
    simp only [keys, Finset.mem_filter, Finset.mem_univ, true_and, hpaired]
    split_ifs with h
    · exact iff_of_true rfl h
    · exact iff_of_false (by omega) h
  refine ⟨?_, ?_, ?_⟩
  · intro x; rw [hpaired]; split_ifs <;> omega
  · rw [hP]; exact hcard
  · have hfib : ∀ v ∈ keys.image view, 2 * (keys.filter (fun x => view x = v)).card =
        2 + ((Finset.univ.filter (fun x : Fin k → Bool =>
          Cd (d : Fin k) (ini : Fin k) (fin : Fin k) x)).filter (fun x => view x = v)).card := by
      intro v hv
      obtain ⟨x0, -, rfl⟩ := Finset.mem_image.mp hv
      have h1 : (keys.filter (fun x => view x = view x0)).card = paired x0 := rfl
      rw [h1, hpaired]
      by_cases hc : Cd (d : Fin k) (ini : Fin k) (fin : Fin k) x0
      · rw [if_pos hc]
        have : (Finset.univ.filter (fun x : Fin k → Bool =>
            Cd (d : Fin k) (ini : Fin k) (fin : Fin k) x)).filter (fun x => view x = view x0) =
            keys.filter (fun x => view x = view x0) := by
          ext y
          simp only [keys, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · exact fun h => h.2
          · intro h
            refine ⟨?_, h⟩
            have hy := hsame x0 y h
            rw [hpaired, hpaired, if_pos hc] at hy
            by_contra hn
            rw [if_neg hn] at hy
            omega
        rw [this, h1, hpaired, if_pos hc]
      · rw [if_neg hc]
        have : (Finset.univ.filter (fun x : Fin k → Bool =>
            Cd (d : Fin k) (ini : Fin k) (fin : Fin k) x)).filter (fun x => view x = view x0) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro y hy h
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          have h2 := hsame x0 y h
          rw [hpaired, hpaired, if_pos hy, if_neg hc] at h2
          omega
        rw [this, Finset.card_empty]
    have hs1 := Finset.card_eq_sum_card_image view keys
    have hs2 := Finset.card_eq_sum_card_fiberwise (f := view) (s := Finset.univ.filter
      (fun x : Fin k → Bool => Cd (d : Fin k) (ini : Fin k) (fin : Fin k) x))
      (t := keys.image view) (fun x _ => Finset.mem_image_of_mem view (Finset.mem_univ x))
    have h2 : 2 * keys.card = 2 * (keys.image view).card + 2 * 2 ^ e := by
      rw [hs1, Finset.mul_sum, Finset.sum_congr rfl hfib, Finset.sum_add_distrib,
        Finset.sum_const, smul_eq_mul, ← hs2, hcard]
      ring
    have hu : keys.card = 2 ^ k := by
      simp [keys, W]
    omega
