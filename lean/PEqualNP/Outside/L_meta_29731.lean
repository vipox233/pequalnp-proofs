import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29731_aux

variable {k : ℕ}

def ix (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

def rot (hk : 0 < k) (s : ℕ) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  x (ix hk (i.val + k - (s % k)))

def mix (hk : 0 < k) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  x i + x (ix hk (i.val + 2)) + rot hk 2 x i

def Q (hk : 0 < k) (y : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  y i + (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2))

def rnd (hk : 0 < k) (key c : Fin k → ZMod 2) (j : ℕ) (state : Fin k → ZMod 2) :
    Fin k → ZMod 2 :=
  fun i => Q hk (mix hk state) i + rot hk (3 * (j + 1) + 1) key i + c i

def st (hk : 0 < k) (key name : Fin k → ZMod 2) (c : ℕ → Fin k → ZMod 2) :
    ℕ → Fin k → ZMod 2
  | 0 => rot hk 3 key + name
  | j + 1 => rnd hk key (c j) j (st hk key name c j)

lemma ix_cancel (hk : 0 < k) (n m : ℕ) : ix hk ((ix hk n).val + m) = ix hk (n + m) := by
  apply Fin.ext; simp only [ix]; exact Nat.mod_add_mod n k m

lemma ix_add_k (hk : 0 < k) (n : ℕ) : ix hk (n + k) = ix hk n := by
  apply Fin.ext; simp only [ix]; exact Nat.add_mod_right n k

lemma ix_add_mul (hk : 0 < k) (n b : ℕ) : ix hk (n + k * b) = ix hk n := by
  apply Fin.ext; simp only [ix]; exact Nat.add_mul_mod_self_left n k b

lemma ix_val (hk : 0 < k) (i : Fin k) : ix hk i.val = i := by
  apply Fin.ext; simp only [ix]; exact Nat.mod_eq_of_lt i.isLt

lemma ix_ne (hk : 0 < k) {p a b : ℕ} (hab : a < b) (hd : b < a + k) :
    ix hk (p + a) ≠ ix hk (p + b) := by
  intro h
  have h1 : (p + a) % k = (p + b) % k := congrArg Fin.val h
  have h2 := Nat.sub_mod_eq_zero_of_mod_eq h1.symm
  rw [Nat.add_sub_add_left] at h2
  have h3 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero h2)
  omega

lemma rot_ix (hk : 0 < k) (s : ℕ) (x : Fin k → ZMod 2) (n : ℕ) :
    rot hk s x (ix hk n) = x (ix hk (n + (k - s % k))) := by
  unfold rot
  rw [Nat.add_sub_assoc (Nat.le_of_lt (Nat.mod_lt s hk)), ix_cancel]

lemma mix_ix (hk : 0 < k) (h7 : 7 ≤ k) (x : Fin k → ZMod 2) (n : ℕ) :
    mix hk x (ix hk n) = x (ix hk n) + x (ix hk (n + 2)) + x (ix hk (n + (k - 2))) := by
  unfold mix
  rw [rot_ix, ix_cancel, Nat.mod_eq_of_lt (by omega : 2 < k)]

lemma Q_diff (hk : 0 < k) (y D : Fin k → ZMod 2) (n : ℕ) :
    Q hk (y + D) (ix hk n) - Q hk y (ix hk n) =
      D (ix hk n) + (1 + y (ix hk (n + 1))) * D (ix hk (n + 2))
        + D (ix hk (n + 1)) * y (ix hk (n + 2)) + D (ix hk (n + 1)) * D (ix hk (n + 2)) := by
  unfold Q
  rw [ix_cancel, ix_cancel]
  simp only [Pi.add_apply]
  ring

lemma mix_add (hk : 0 < k) (a b : Fin k → ZMod 2) : mix hk (a + b) = mix hk a + mix hk b := by
  funext i; simp only [mix, rot, Pi.add_apply]; ring

lemma mix_sub (hk : 0 < k) (a b : Fin k → ZMod 2) : mix hk (a - b) = mix hk a - mix hk b := by
  funext i; simp only [mix, rot, Pi.sub_apply]; ring

lemma sgl (hk : 0 < k) (b r s : ℕ) (h1 : r < s + k) (h2 : s < r + k) :
    (Pi.single (ix hk (b + r)) (1 : ZMod 2) : Fin k → ZMod 2) (ix hk (b + s)) =
      if r = s then 1 else 0 := by
  by_cases h : r = s
  · subst h; simp
  · rw [if_neg h, Pi.single_apply, if_neg]
    intro he
    rcases Nat.lt_or_gt_of_ne h with h' | h'
    · exact ix_ne hk h' h2 he.symm
    · exact ix_ne hk h' h1 he

lemma sgl7 (hk : 0 < k) (h7 : 7 ≤ k) (b r s : ℕ) (hr1 : 1 ≤ r) (hr : r ≤ 7) (hs1 : 1 ≤ s) (hs : s ≤ 7) :
    (Pi.single (ix hk (b + r)) (1 : ZMod 2) : Fin k → ZMod 2) (ix hk (b + s)) =
      if r = s then 1 else 0 :=
  sgl hk b r s (by omega) (by omega)

lemma two_eq (a b c : ZMod 2) (h : a + b + c = 0) : b = a + c := by
  revert a b c; decide

lemma self_eq (a : ZMod 2) (h : a = a + a) : a = 0 := by
  revert a; decide

lemma mix_ker (hk : 0 < k) (h7 : 7 ≤ k) (h3 : k % 3 ≠ 0) (z : Fin k → ZMod 2)
    (hz : mix hk z = 0) : z = 0 := by
  have rel : ∀ m, z (ix hk (m + 4)) = z (ix hk (m + 2)) + z (ix hk m) := by
    intro m
    have e := congrFun hz (ix hk (m + 2))
    rw [mix_ix hk h7, show m + 2 + 2 = m + 4 by omega, show m + 2 + (k - 2) = m + k by omega,
      ix_add_k] at e
    exact two_eq _ _ _ (by simpa using e)
  have p6 : ∀ n, z (ix hk (n + 6)) = z (ix hk n) := by
    intro n
    have a1 := rel n
    have a2 := rel (n + 2)
    rw [show n + 2 + 4 = n + 6 by omega, show n + 2 + 2 = n + 4 by omega, a1] at a2
    rw [a2]
    generalize z (ix hk (n + 2)) = u
    generalize z (ix hk n) = v
    revert u v; decide
  have p6m : ∀ a n, z (ix hk (n + 6 * a)) = z (ix hk n) := by
    intro a
    induction a with
    | zero => intro n; simp
    | succ a ih => intro n; rw [show n + 6 * (a + 1) = (n + 6 * a) + 6 by ring, p6, ih]
  have p2 : ∀ n, z (ix hk (n + 2)) = z (ix hk n) := by
    intro n
    have hc : k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 4 ∨ k % 6 = 5 := by omega
    obtain ⟨b, a, hab⟩ : ∃ b a : ℕ, 2 + k * b = 6 * a := by
      rcases hc with hc | hc | hc | hc
      · exact ⟨4, (2 + k * 4) / 6, by omega⟩
      · exact ⟨2, (2 + k * 2) / 6, by omega⟩
      · exact ⟨1, (2 + k * 1) / 6, by omega⟩
      · exact ⟨2, (2 + k * 2) / 6, by omega⟩
    rw [← ix_add_mul hk (n + 2) b, show n + 2 + k * b = n + 6 * a by omega, p6m]
  funext i
  have r := rel i.val
  rw [show i.val + 4 = i.val + 2 + 2 by omega, p2, p2] at r
  rw [ix_val] at r
  exact self_eq _ (by simpa using r)

lemma mix_inj (hk : 0 < k) (h7 : 7 ≤ k) (h3 : k % 3 ≠ 0) : Function.Injective (mix hk) := by
  intro a b hab
  have := mix_ker hk h7 h3 (a - b) (by rw [mix_sub, hab, sub_self])
  exact sub_eq_zero.mp this

lemma mix_surj (hk : 0 < k) (h7 : 7 ≤ k) (h3 : k % 3 ≠ 0) : Function.Surjective (mix hk) :=
  Finite.injective_iff_surjective.mp (mix_inj hk h7 h3)

lemma rot3_inj (hk : 0 < k) (h7 : 7 ≤ k) : Function.Injective (rot hk 3) := by
  intro a b hab
  funext i
  have e := congrFun hab (ix hk (i.val + 3))
  rw [rot_ix, rot_ix, Nat.mod_eq_of_lt (by omega : 3 < k),
    show i.val + 3 + (k - 3) = i.val + k by omega, ix_add_k, ix_val] at e
  exact e

lemma rot3_surj (hk : 0 < k) (h7 : 7 ≤ k) : Function.Surjective (rot hk 3) :=
  Finite.injective_iff_surjective.mp (rot3_inj hk h7)

lemma st_congr (hk : 0 < k) (key name : Fin k → ZMod 2) (c c' : ℕ → Fin k → ZMod 2) :
    ∀ j, (∀ i < j, c i = c' i) → st hk key name c j = st hk key name c' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    simp only [st]
    rw [ih (fun i hi => h i (by omega)), h j (by omega)]

lemma rnd_add_c (hk : 0 < k) (key c u : Fin k → ZMod 2) (j : ℕ) (s : Fin k → ZMod 2) :
    rnd hk key (c + u) j s = rnd hk key c j s + u := by
  funext i; simp only [rnd, Pi.add_apply]; ring

lemma free (hk : 0 < k) (j : ℕ) (name : Fin k → ZMod 2) (c : ℕ → Fin k → ZMod 2)
    (u : Fin k → ZMod 2) :
    ∃ name' c', ∀ K, st hk K name' c' j = st hk K name c j + u := by
  cases j with
  | zero => exact ⟨name + u, c, fun K => by simp only [st]; abel⟩
  | succ j =>
    refine ⟨name, Function.update c j (c j + u), fun K => ?_⟩
    simp only [st]
    rw [st_congr hk K name (Function.update c j (c j + u)) c j
      (fun i hi => Function.update_of_ne (by omega) _ _), Function.update_self, rnd_add_c]

lemma free_y (hk : 0 < k) (h7 : 7 ≤ k) (h3 : k % 3 ≠ 0) (K1 K2 name : Fin k → ZMod 2)
    (c : ℕ → Fin k → ZMod 2) (j : ℕ) (y : Fin k → ZMod 2) :
    ∃ name' c', mix hk (st hk K2 name' c' j) = y ∧
      st hk K1 name' c' j - st hk K2 name' c' j = st hk K1 name c j - st hk K2 name c j := by
  obtain ⟨w, hw⟩ := mix_surj hk h7 h3 y
  obtain ⟨name', c', hf⟩ := free hk j name c (w - st hk K2 name c j)
  refine ⟨name', c', ?_, ?_⟩
  · rw [hf K2, add_sub_cancel, hw]
  · rw [hf K1, hf K2]; abel

lemma rnd_diff (hk : 0 < k) (K1 K2 name : Fin k → ZMod 2) (c : ℕ → Fin k → ZMod 2) (j : ℕ) :
    st hk K1 name c (j + 1) - st hk K2 name c (j + 1) =
      fun i => (Q hk (mix hk (st hk K2 name c j) + mix hk (st hk K1 name c j - st hk K2 name c j)) i
        - Q hk (mix hk (st hk K2 name c j)) i)
        + (rot hk (3 * (j + 1) + 1) K1 i - rot hk (3 * (j + 1) + 1) K2 i) := by
  rw [← mix_add, add_sub_cancel]
  funext i
  simp only [st, rnd, Pi.sub_apply]
  ring

lemma mix_expand (hk : 0 < k) (h7 : 7 ≤ k) (b : ℕ) (y D rk : Fin k → ZMod 2) :
    mix hk (fun i => (Q hk (y + D) i - Q hk y i) + rk i) (ix hk (b + 3)) =
      (D (ix hk (b + 3)) + (1 + y (ix hk (b + 4))) * D (ix hk (b + 5))
        + D (ix hk (b + 4)) * y (ix hk (b + 5)) + D (ix hk (b + 4)) * D (ix hk (b + 5))
        + rk (ix hk (b + 3)))
      + (D (ix hk (b + 5)) + (1 + y (ix hk (b + 6))) * D (ix hk (b + 7))
        + D (ix hk (b + 6)) * y (ix hk (b + 7)) + D (ix hk (b + 6)) * D (ix hk (b + 7))
        + rk (ix hk (b + 5)))
      + (D (ix hk (b + 1)) + (1 + y (ix hk (b + 2))) * D (ix hk (b + 3))
        + D (ix hk (b + 2)) * y (ix hk (b + 3)) + D (ix hk (b + 2)) * D (ix hk (b + 3))
        + rk (ix hk (b + 1))) := by
  rw [mix_ix hk h7, show b + 3 + (k - 2) = b + 1 + k by omega, ix_add_k,
    show b + 3 + 2 = b + 5 by omega]
  simp only [Q_diff]

lemma mid_core (hk : 0 < k) (h7 : 7 ≤ k) (b : ℕ) (D rk : Fin k → ZMod 2) (C : ZMod 2)
    (H : ∀ y : Fin k → ZMod 2,
      mix hk (fun i => (Q hk (y + D) i - Q hk y i) + rk i) (ix hk (b + 3)) = C) :
    ∀ e < 6, D (ix hk (b + 2 + e)) = 0 := by
  have E : ∀ y, _ := fun y => (mix_expand hk h7 b y D rk).symm.trans (H y)
  have h0 := E 0
  have g2 := E (Pi.single (ix hk (b + 2)) 1)
  have g3 := E (Pi.single (ix hk (b + 3)) 1)
  have g4 := E (Pi.single (ix hk (b + 4)) 1)
  have g5 := E (Pi.single (ix hk (b + 5)) 1)
  have g6 := E (Pi.single (ix hk (b + 6)) 1)
  have g7 := E (Pi.single (ix hk (b + 7)) 1)
  simp only [Pi.zero_apply] at h0
  simp only [sgl7 hk h7 b, Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceLeDiff] at g2 g3 g4 g5 g6 g7
  intro e he
  interval_cases e
  · simp only [add_zero]; linear_combination g3 - h0
  · linear_combination g2 - h0
  · linear_combination g5 - h0
  · linear_combination g4 - h0
  · linear_combination g7 - h0
  · linear_combination g6 - h0

lemma fin_core (hk : 0 < k) (h7 : 7 ≤ k) (n : ℕ) (D rk : Fin k → ZMod 2) (C : ZMod 2)
    (H : ∀ y : Fin k → ZMod 2, (Q hk (y + D) (ix hk n) - Q hk y (ix hk n)) + rk (ix hk n) = C) :
    D (ix hk (n + 1)) = 0 ∧ D (ix hk (n + 2)) = 0 := by
  have E : ∀ y, _ := fun y => (congrArg (· + rk (ix hk n)) (Q_diff hk y D n)).symm.trans (H y)
  have h0 := E 0
  have g1 := E (Pi.single (ix hk (n + 1)) 1)
  have g2 := E (Pi.single (ix hk (n + 2)) 1)
  simp only [Pi.zero_apply] at h0
  simp only [sgl7 hk h7 n, Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceLeDiff] at g1 g2
  exact ⟨by linear_combination g2 - h0, by linear_combination g1 - h0⟩


lemma foldl_eq (hk : 0 < k) (key name : Fin k → ZMod 2) :
    ∀ (n : ℕ) (c : Fin n → Fin k → ZMod 2) (cN : ℕ → Fin k → ZMod 2), (∀ j : Fin n, cN j.val = c j) →
      (List.finRange n).foldl (fun state j => rnd hk key (c j) j.val state) (rot hk 3 key + name)
        = st hk key name cN n := by
  intro n
  induction n with
  | zero => intro c cN _; rfl
  | succ n ih =>
    intro c cN hc
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
    simp only [Fin.coe_castSucc]
    rw [ih (fun j => c (Fin.castSucc j)) cN (fun j => hc (Fin.castSucc j))]
    simp only [List.foldl_cons, List.foldl_nil, st]
    rw [← hc (Fin.last n)]
    rfl

lemma level (hk : 0 < k) (h7 : 7 ≤ k) (h3 : k % 3 ≠ 0) (t h start : ℕ) (hh : 0 < h)
    (K1 K2 : Fin k → ZMod 2) (Cst : ℕ → ZMod 2)
    (Htop : ∀ name c, ∀ a < h,
      (st hk K1 name c (t + 1) - st hk K2 name c (t + 1)) (ix hk (start + a)) = Cst a) :
    ∀ name c, ∀ r < h + 1 + 5 * t,
      mix hk (st hk K1 name c 0 - st hk K2 name c 0) (ix hk (start + 1 + t * (k - 1) + r)) = 0 := by
  have L0 : ∀ name c, ∀ r < h + 1,
      mix hk (st hk K1 name c t - st hk K2 name c t) (ix hk (start + 1 + r)) = 0 := by
    intro name c
    have key : ∀ a < h, mix hk (st hk K1 name c t - st hk K2 name c t) (ix hk (start + a + 1)) = 0 ∧
        mix hk (st hk K1 name c t - st hk K2 name c t) (ix hk (start + a + 2)) = 0 := by
      intro a ha
      apply fin_core hk h7 (start + a) _
        (fun i => rot hk (3 * (t + 1) + 1) K1 i - rot hk (3 * (t + 1) + 1) K2 i) (Cst a)
      intro y
      obtain ⟨name', c', hy, hD⟩ := free_y hk h7 h3 K1 K2 name c t y
      have e := Htop name' c' a ha
      rw [rnd_diff, hy, hD] at e
      exact e
    intro r hr
    rcases Nat.lt_or_ge r h with h' | h'
    · have := (key r h').1; rwa [show start + r + 1 = start + 1 + r by omega] at this
    · have := (key (h - 1) (by omega)).2
      rwa [show start + (h - 1) + 2 = start + 1 + r by omega] at this
  have ind : ∀ i j, j + i = t → ∀ name c, ∀ r < h + 1 + 5 * i,
      mix hk (st hk K1 name c j - st hk K2 name c j) (ix hk (start + 1 + i * (k - 1) + r)) = 0 := by
    intro i
    induction i with
    | zero => intro j hj name c r hr; simp only [zero_mul, add_zero] at hj ⊢; subst hj; exact L0 name c r (by omega)
    | succ i ih =>
      intro j hj name c r hr
      have IH := ih (j + 1) (by omega)
      have hr' : (r < 5 ∧ 0 < h + 1 + 5 * i) ∨ (5 ≤ r ∧ r - 5 < h + 1 + 5 * i) := by omega
      obtain ⟨r0, e, hr0, he, hre⟩ : ∃ r0 e, r0 < h + 1 + 5 * i ∧ e < 6 ∧ r = r0 + e := by
        rcases hr' with ⟨a1, a2⟩ | ⟨a1, a2⟩
        · exact ⟨0, r, a2, by omega, by omega⟩
        · exact ⟨r - 5, 5, a2, by omega, by omega⟩
      set A := start + 1 + i * (k - 1)
      have := mid_core hk h7 (A + r0 + k - 3) (mix hk (st hk K1 name c j - st hk K2 name c j))
        (fun i => rot hk (3 * (j + 1) + 1) K1 i - rot hk (3 * (j + 1) + 1) K2 i) 0 (by
          intro y
          obtain ⟨name', c', hy, hD⟩ := free_y hk h7 h3 K1 K2 name c j y
          have e := IH name' c' r0 hr0
          rw [rnd_diff, hy, hD, ← ix_add_k hk (A + r0), show A + r0 + k = A + r0 + k - 3 + 3 by omega] at e
          exact e) e he
      rw [show A + r0 + k - 3 + 2 + e = start + 1 + (i + 1) * (k - 1) + r by
        subst hre; simp only [A]; rw [Nat.add_mul, one_mul]; omega] at this
      exact this
  intro name c r hr
  exact ind t 0 (by omega) name c r hr

lemma count (hk : 0 < k) (h7 : 7 ≤ k) (h3 : k % 3 ≠ 0) (A m N : ℕ) (hm : m ≤ k)
    (tag : (Fin k → ZMod 2) → Fin N)
    (H : ∀ K1 K2, tag K1 = tag K2 → ∀ r < m,
      mix hk (rot hk 3 K1 - rot hk 3 K2) (ix hk (A + r)) = 0) : 2 ^ m ≤ N := by
  let e : Fin m → Fin k := fun r => ix hk (A + r.val)
  have he : Function.Injective e := by
    intro r1 r2 h12
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h' | h'
    · exact ix_ne hk h' (by omega) h12
    · exact ix_ne hk h' (by omega) h12.symm
  let φ : (Fin k → ZMod 2) → Fin m → ZMod 2 := fun K r => mix hk (rot hk 3 K) (e r)
  have hφ : ∀ K1 K2, tag K1 = tag K2 → φ K1 = φ K2 := by
    intro K1 K2 h12; funext r
    have := H K1 K2 h12 r.val r.isLt
    rw [mix_sub, Pi.sub_apply, sub_eq_zero] at this
    exact this
  have sφ : Function.Surjective φ := by
    intro v
    obtain ⟨w, hw⟩ := mix_surj hk h7 h3 (Function.extend e v 0)
    obtain ⟨K, hK⟩ := rot3_surj hk h7 w
    refine ⟨K, funext fun r => ?_⟩
    simp only [φ, hK, hw]
    exact he.extend_apply v 0 r
  classical
  let ψ : Fin N → Fin m → ZMod 2 := fun n => if hn : ∃ K, tag K = n then φ hn.choose else 0
  have sψ : Function.Surjective ψ := by
    intro v
    obtain ⟨K, hK⟩ := sφ v
    refine ⟨tag K, ?_⟩
    have hex : ∃ K', tag K' = tag K := ⟨K, rfl⟩
    simp only [ψ, dif_pos hex]
    rw [hφ _ _ hex.choose_spec, hK]
  have := Fintype.card_le_of_surjective ψ sψ
  simpa [Fintype.card_fun, ZMod.card, Fintype.card_fin] using this

lemma main (k t h : ℕ) (hk : 0 < k) (h7 : 7 ≤ k) (h3 : k % 3 ≠ 0) (hh : 0 < h)
    (start : Fin k) (N : ℕ) (tag : (Fin k → ZMod 2) → Fin N)
    (bias : (Fin k → ZMod 2) → Fin h → ZMod 2)
    (decode : Fin N → (Fin k → ZMod 2) → (Fin (t + 1) → Fin k → ZMod 2) → Fin h → ZMod 2)
    (H : ∀ (key name : Fin k → ZMod 2) (c : Fin (t + 1) → Fin k → ZMod 2) (a : Fin h),
      (List.finRange (t + 1)).foldl (fun state j => rnd hk key (c j) j.val state) (rot hk 3 key + name)
        (ix hk (start.val + a.val)) = bias key a + decode (tag key) name c a) :
    2 ^ (min k (h + 1 + 5 * t)) ≤ N := by
  apply count hk h7 h3 (start.val + 1 + t * (k - 1)) _ N (min_le_left _ _) tag
  intro K1 K2 h12 r hr
  let Cst : ℕ → ZMod 2 := fun a => if ha : a < h then bias K1 ⟨a, ha⟩ - bias K2 ⟨a, ha⟩ else 0
  have Htop : ∀ name (c : ℕ → Fin k → ZMod 2), ∀ a < h,
      (st hk K1 name c (t + 1) - st hk K2 name c (t + 1)) (ix hk (start.val + a)) = Cst a := by
    intro name c a ha
    have e1 := H K1 name (fun j => c j.val) ⟨a, ha⟩
    have e2 := H K2 name (fun j => c j.val) ⟨a, ha⟩
    rw [foldl_eq hk K1 name (t + 1) (fun j => c j.val) c (fun j => rfl)] at e1
    rw [foldl_eq hk K2 name (t + 1) (fun j => c j.val) c (fun j => rfl)] at e2
    simp only [Cst, dif_pos ha, Pi.sub_apply]
    rw [e1, e2, h12]
    ring
  have L := level hk h7 h3 t h start.val hh K1 K2 Cst Htop 0 (fun _ => 0) r
    (lt_of_lt_of_le hr (min_le_right _ _))
  simp only [st, add_zero] at L
  exact L

end PEqualNP.Outside.L_meta_29731_aux

theorem PEqualNP.Outside.L_meta_29731 : (∀ (k t h : ℕ) (hk : 0 < k), 7 ≤ k → k % 3 ≠ 0 → 0 < h → h ≤ k →
  let W := Fin k → ZMod 2
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val+k-(s % k)))
  let mix := fun (x : W) (i : Fin k) => x i + x (ix (i.val+2)) + rot 2 x i
  let run := fun (key name : W) (c : Fin (t+1) → W) =>
    (List.finRange (t+1)).foldl (fun (state : W) (j : Fin (t+1)) =>
      let y := mix state
      fun i : Fin k => y i + (1+y (ix (i.val+1)))*y (ix (i.val+2)) +
        rot (3*(j.val+1)+1) key i + c j i) (rot 3 key + name)
  ∀ (start : Fin k) (N : ℕ) (tag : W → Fin N) (bias : W → Fin h → ZMod 2)
    (decode : Fin N → W → (Fin (t+1) → W) → Fin h → ZMod 2),
    (∀ (key name : W) (c : Fin (t+1) → W) (a : Fin h),
      run key name c (ix (start.val+a.val)) = bias key a + decode (tag key) name c a) →
    2^(min k (h+1+5*t)) ≤ N) := by
  intro k t h hk h7 h3 hh _ W ix rot mix run start N tag bias decode H
  exact PEqualNP.Outside.L_meta_29731_aux.main k t h hk h7 h3 hh start N tag bias decode H
