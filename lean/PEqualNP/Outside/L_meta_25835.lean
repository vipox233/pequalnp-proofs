import Mathlib

namespace PEqualNP.Outside.L_meta_25835

def turn {k : ℕ} (dist : ℕ) (word : ZMod k → ZMod 2) (site : ZMod k) : ZMod 2 :=
  word (site - (dist : ZMod k))
def mix {k : ℕ} (dist : ℕ) (word : ZMod k → ZMod 2) (site : ZMod k) : ZMod 2 :=
  word (site - (dist : ZMod k)) + word site + word (site + (dist : ZMod k))
def chi {k : ℕ} (word : ZMod k → ZMod 2) (site : ZMod k) : ZMod 2 :=
  word site + (1 + word (site+1)) * word (site+2)
def row {k : ℕ} (u rc key : ZMod k → ZMod 2) : ZMod k → ZMod 2 :=
  chi (mix 1 (turn 1 key + u)) + key + rc
def col {k : ℕ} (v cc key : ZMod k → ZMod 2) : ZMod k → ZMod 2 :=
  chi (mix 2 (turn 3 key + v)) + turn 4 key + cc

theorem row_solve {k : ℕ} (u rc key key' : ZMod k → ZMod 2) (s : ZMod k)
    (hag : ∀ c : ℤ, -1 ≤ c → c ≤ 2 → key (s + (c : ZMod k)) = key' (s + (c : ZMod k)))
    (h1 : row u rc key s = 0) (h2 : row u rc key' s = 0) :
    key (s + ((-2 : ℤ) : ZMod k)) = key' (s + ((-2 : ℤ) : ZMod k)) := by
  have a1 := hag (-1) (by norm_num) (by norm_num)
  have a2 := hag 0 (by norm_num) (by norm_num)
  have a3 := hag 1 (by norm_num) (by norm_num)
  have a4 := hag 2 (by norm_num) (by norm_num)
  simp only [row, chi, mix, turn, Pi.add_apply] at h1 h2
  push_cast at a1 a2 a3 a4 ⊢
  ring_nf at a1 a2 a3 a4 h1 h2 ⊢
  rw [a1, a2, a3, a4] at h1
  linear_combination h1 - h2

theorem row_loc {k : ℕ} (u rc key key' : ZMod k → ZMod 2) (s : ZMod k)
    (hag : ∀ c : ℤ, -2 ≤ c → c ≤ 2 → key (s + (c : ZMod k)) = key' (s + (c : ZMod k))) :
    row u rc key s = row u rc key' s := by
  have a0 := hag (-2) (by norm_num) (by norm_num)
  have a1 := hag (-1) (by norm_num) (by norm_num)
  have a2 := hag 0 (by norm_num) (by norm_num)
  have a3 := hag 1 (by norm_num) (by norm_num)
  have a4 := hag 2 (by norm_num) (by norm_num)
  simp only [row, chi, mix, turn, Pi.add_apply]
  push_cast at a0 a1 a2 a3 a4
  ring_nf at a0 a1 a2 a3 a4 ⊢
  rw [a0, a1, a2, a3, a4]
  try ring

theorem col_solve {k : ℕ} (v cc key key' : ZMod k → ZMod 2) (s : ZMod k)
    (hag : ∀ c : ℤ, -4 ≤ c → c ≤ 1 → key (s + (c : ZMod k)) = key' (s + (c : ZMod k)))
    (h1 : col v cc key s = 0) (h2 : col v cc key' s = 0) :
    key (s + ((-5 : ℤ) : ZMod k)) = key' (s + ((-5 : ℤ) : ZMod k)) := by
  have a1 := hag (-4) (by norm_num) (by norm_num)
  have a2 := hag (-3) (by norm_num) (by norm_num)
  have a3 := hag (-2) (by norm_num) (by norm_num)
  have a4 := hag (-1) (by norm_num) (by norm_num)
  have a5 := hag 0 (by norm_num) (by norm_num)
  have a6 := hag 1 (by norm_num) (by norm_num)
  simp only [col, chi, mix, turn, Pi.add_apply] at h1 h2
  push_cast at a1 a2 a3 a4 a5 a6 ⊢
  ring_nf at a1 a2 a3 a4 a5 a6 h1 h2 ⊢
  rw [a1, a2, a3, a4, a5, a6] at h1
  linear_combination h1 - h2

theorem col_loc {k : ℕ} (v cc key key' : ZMod k → ZMod 2) (s : ZMod k)
    (hag : ∀ c : ℤ, -5 ≤ c → c ≤ 1 → key (s + (c : ZMod k)) = key' (s + (c : ZMod k))) :
    col v cc key s = col v cc key' s := by
  have a0 := hag (-5) (by norm_num) (by norm_num)
  have a1 := hag (-4) (by norm_num) (by norm_num)
  have a2 := hag (-3) (by norm_num) (by norm_num)
  have a3 := hag (-2) (by norm_num) (by norm_num)
  have a4 := hag (-1) (by norm_num) (by norm_num)
  have a5 := hag 0 (by norm_num) (by norm_num)
  have a6 := hag 1 (by norm_num) (by norm_num)
  simp only [col, chi, mix, turn, Pi.add_apply]
  push_cast at a0 a1 a2 a3 a4 a5 a6
  ring_nf at a0 a1 a2 a3 a4 a5 a6 ⊢
  rw [a0, a1, a2, a3, a4, a5, a6]
  try ring


theorem abstract {k : ℕ} [NeZero k] (good : (ZMod k → ZMod 2) → Prop)
    (label : (ZMod k → ZMod 2) → (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2))
    (passive : ZMod k → Prop) (N : ℕ)
    (hloc : ∀ a b : ZMod k → ZMod 2, (∀ j, ¬ passive j → a j = b j) → (good a ↔ good b))
    (hlab : ∀ a b : ZMod k → ZMod 2, (∀ j, ¬ passive j → a j = b j) → label a = label b)
    (huniq : ∀ a b : ZMod k → ZMod 2, good a → good b → label a = label b →
      ∀ j, ¬ passive j → a j = b j)
    (hbase : ∀ z, ∃ b : ZMod k → ZMod 2, label b = z ∧ ∀ j, passive j → b j = 0)
    (hcard : Nat.card {j // passive j} = N) :
    ∃ dec : (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) → (ZMod k → ZMod 2),
      (∀ z, label (dec z) = z ∧ ∀ j, passive j → dec z j = 0) ∧
      (∀ key, good key ↔ good (dec (label key)) ∧ ∀ j, ¬ passive j → key j = dec (label key) j) ∧
      ∀ z, (good (dec z) → Nat.card {raw // good raw ∧ label raw = z} = 2 ^ N) ∧
        (¬ good (dec z) → Nat.card {raw // good raw ∧ label raw = z} = 0) := by
  classical
  let zo : (ZMod k → ZMod 2) → (ZMod k → ZMod 2) := fun a j => if passive j then 0 else a j
  have zo_ag : ∀ a j, ¬ passive j → zo a j = a j := fun a j hj => if_neg hj
  let dec : (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) → (ZMod k → ZMod 2) := fun z =>
    if hz : ∃ a, good a ∧ label a = z then zo (Classical.choose hz) else Classical.choose (hbase z)
  have P1 : ∀ z, label (dec z) = z ∧ ∀ j, passive j → dec z j = 0 := by
    intro z
    by_cases hz : ∃ a, good a ∧ label a = z
    · have hd : dec z = zo (Classical.choose hz) := dif_pos hz
      rw [hd]
      refine ⟨?_, fun j hj => if_pos hj⟩
      rw [hlab _ _ (zo_ag _)]
      exact (Classical.choose_spec hz).2
    · have hd : dec z = Classical.choose (hbase z) := dif_neg hz
      rw [hd]
      exact Classical.choose_spec (hbase z)
  have P2 : ∀ key, good key ↔ good (dec (label key)) ∧ ∀ j, ¬ passive j → key j = dec (label key) j := by
    intro key
    constructor
    · intro hk
      have hz : ∃ a, good a ∧ label a = label key := ⟨key, hk, rfl⟩
      have hd : dec (label key) = zo (Classical.choose hz) := dif_pos hz
      have hs := Classical.choose_spec hz
      have hag : ∀ j, ¬ passive j → key j = dec (label key) j := by
        intro j hj
        rw [hd, zo_ag _ _ hj]
        exact huniq _ _ hk hs.1 hs.2.symm j hj
      exact ⟨(hloc _ _ hag).1 hk, hag⟩
    · rintro ⟨hg, hag⟩
      exact (hloc _ _ hag).2 hg
  refine ⟨dec, P1, P2, fun z => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · have e : {raw // good raw ∧ label raw = z} ≃ ({j // passive j} → ZMod 2) :=
      { toFun := fun r j => r.1 j.1
        invFun := fun f => ⟨fun j => if hj : passive j then f ⟨j, hj⟩ else dec z j, by
          have hag : ∀ j, ¬ passive j →
              (fun j => if hj : passive j then f ⟨j, hj⟩ else dec z j) j = dec z j :=
            fun j hj => dif_neg hj
          exact ⟨(hloc _ _ hag).2 hg, (hlab _ _ hag).trans (P1 z).1⟩⟩
        left_inv := by
          rintro ⟨r, hr1, hr2⟩
          apply Subtype.ext
          funext j
          by_cases hj : passive j
          · simp [hj]
          · simp only [hj, dite_false]
            exact (huniq _ _ hr1 hg (hr2.trans (P1 z).1.symm) j hj).symm
        right_inv := by
          intro f
          funext j
          simp [j.2] }
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, hcard]
  · rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨r, hr1, hr2⟩
    apply hg
    have := ((P2 r).1 hr1).1
    rwa [hr2] at this


theorem val_neg {k : ℕ} [NeZero k] (a : ℤ) (h0 : -(k : ℤ) ≤ a) (h1 : a < 0) :
    (((a : ZMod k)).val : ℤ) = a + k := by
  rw [ZMod.val_intCast]
  have e : (a + k) % (k : ℤ) = a % k := by simp
  rw [← e]
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem val_pos {k : ℕ} [NeZero k] (a : ℤ) (h0 : 0 ≤ a) (h1 : a < k) :
    (((a : ZMod k)).val : ℤ) = a := by
  rw [ZMod.val_intCast]
  exact Int.emod_eq_of_lt h0 h1

theorem self_cast {k : ℕ} [NeZero k] (j : ZMod k) : ((j.val : ℤ) : ZMod k) = j := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem main (k : ℕ) [NeZero k] (h : ℕ) (h5 : 5 ≤ h) (hk : h + 7 ≤ k)
    (rc cc u v : ZMod k → ZMod 2) :
    let good := fun key : ZMod k → ZMod 2 =>
      ∀ site : ZMod k, k - h ≤ site.val → row u rc key site = 0 ∧ col v cc key site = 0
    let label := fun (key : ZMod k → ZMod 2) => (key (-2), key (-1), key 0, key 1)
    let passive := fun site : ZMod k => 2 ≤ site.val ∧ site.val < k - h - 5
    ∃ dec : (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) → (ZMod k → ZMod 2),
      (∀ z, label (dec z) = z ∧ ∀ j, passive j → dec z j = 0) ∧
      (∀ key, good key ↔ good (dec (label key)) ∧ ∀ j, ¬ passive j → key j = dec (label key) j) ∧
      ∀ z, (good (dec z) → Nat.card {raw // good raw ∧ label raw = z} = 2 ^ (k - h - 7)) ∧
        (¬ good (dec z) → Nat.card {raw // good raw ∧ label raw = z} = 0) := by
  intro good label passive
  have L1 : ∀ a : ℤ, -((h : ℤ) + 5) ≤ a → a ≤ 1 → ¬ passive (a : ZMod k) := by
    intro a ha1 ha2 hp
    obtain ⟨hp1, hp2⟩ := hp
    rcases lt_or_ge a 0 with hneg | hnn
    · have := val_neg (k := k) a (by omega) hneg
      omega
    · have := val_pos (k := k) a hnn (by omega)
      omega
  have L2 : ∀ j : ZMod k, ¬ passive j → ∃ a : ℤ, -((h : ℤ) + 5) ≤ a ∧ a ≤ 1 ∧ j = (a : ZMod k) := by
    intro j hj
    have hv := ZMod.val_lt j
    by_cases h2 : j.val < 2
    · exact ⟨j.val, by omega, by omega, (self_cast j).symm⟩
    · refine ⟨(j.val : ℤ) - k, ?_, ?_, ?_⟩
      · have : ¬ (j.val < k - h - 5) := fun h' => hj ⟨by omega, h'⟩
        omega
      · omega
      · rw [Int.cast_sub, self_cast, Int.cast_natCast, ZMod.natCast_self, sub_zero]
  have L3 : ∀ s : ZMod k, k - h ≤ s.val → ∃ t : ℤ, -(h : ℤ) ≤ t ∧ t ≤ -1 ∧ s = (t : ZMod k) := by
    intro s hs
    have hv := ZMod.val_lt s
    refine ⟨(s.val : ℤ) - k, by omega, by omega, ?_⟩
    rw [Int.cast_sub, self_cast, Int.cast_natCast, ZMod.natCast_self, sub_zero]
  have L4 : ∀ t : ℤ, -(h : ℤ) ≤ t → t ≤ -1 → k - h ≤ ((t : ZMod k)).val := by
    intro t ht1 ht2
    have := val_neg (k := k) t (by omega) (by omega)
    omega
  have hloc : ∀ a b : ZMod k → ZMod 2, (∀ j, ¬ passive j → a j = b j) → (good a ↔ good b) := by
    intro a b hab
    have agS : ∀ s : ZMod k, k - h ≤ s.val → ∀ c : ℤ, -5 ≤ c → c ≤ 2 →
        a (s + (c : ZMod k)) = b (s + (c : ZMod k)) := by
      intro s hs c hc1 hc2
      obtain ⟨t, ht1, ht2, rfl⟩ := L3 s hs
      rw [← Int.cast_add]
      exact hab _ (L1 _ (by omega) (by omega))
    refine forall_congr' fun s => imp_congr_right fun hs => ?_
    rw [row_loc u rc a b s (fun c h1 h2 => agS s hs c (by omega) (by omega)),
      col_loc v cc a b s (fun c h1 h2 => agS s hs c (by omega) (by omega))]
  have em2 : ((-2 : ℤ) : ZMod k) = -2 := by push_cast; rfl
  have em1 : ((-1 : ℤ) : ZMod k) = -1 := by push_cast; rfl
  have e0 : ((0 : ℤ) : ZMod k) = 0 := by push_cast; rfl
  have e1 : ((1 : ℤ) : ZMod k) = 1 := by push_cast; rfl
  have hlab : ∀ a b : ZMod k → ZMod 2, (∀ j, ¬ passive j → a j = b j) → label a = label b := by
    intro a b hab
    have q : ∀ x : ℤ, -2 ≤ x → x ≤ 1 → a (x : ZMod k) = b (x : ZMod k) :=
      fun x h1 h2 => hab _ (L1 x (by omega) h2)
    have q2 := q (-2) (by norm_num) (by norm_num)
    have q1 := q (-1) (by norm_num) (by norm_num)
    have q0 := q 0 (by norm_num) (by norm_num)
    have q3 := q 1 (by norm_num) (by norm_num)
    rw [em2] at q2
    rw [em1] at q1
    rw [e0] at q0
    rw [e1] at q3
    simp only [label, q2, q1, q0, q3]
  have huniq : ∀ a b : ZMod k → ZMod 2, good a → good b → label a = label b →
      ∀ j, ¬ passive j → a j = b j := by
    intro a b ga gb hl
    simp only [label, Prod.mk.injEq] at hl
    obtain ⟨l2, l1, l0, l3⟩ := hl
    have key : ∀ n : ℕ, ∀ x : ℤ, (1 - x).toNat = n → -((h : ℤ) + 5) ≤ x → x ≤ 1 →
        a (x : ZMod k) = b (x : ZMod k) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro x hn hx1 hx2
        have IH : ∀ y : ℤ, x < y → y ≤ 1 → a (y : ZMod k) = b (y : ZMod k) :=
          fun y hy1 hy2 => ih (1 - y).toNat (by omega) y rfl (by omega) hy2
        by_cases c1 : -2 ≤ x
        · interval_cases x
          · rw [em2]; exact l2
          · rw [em1]; exact l1
          · rw [e0]; exact l0
          · rw [e1]; exact l3
        by_cases c2 : -((h : ℤ) + 2) ≤ x
        · have hs := L4 (x + 2) (by omega) (by omega)
          have r := row_solve u rc a b ((x + 2 : ℤ) : ZMod k)
            (fun c h1 h2 => by rw [← Int.cast_add]; exact IH _ (by omega) (by omega))
            (ga _ hs).1 (gb _ hs).1
          rw [← Int.cast_add] at r
          have : x + 2 + -2 = x := by ring
          rwa [this] at r
        · have hs := L4 (x + 5) (by omega) (by omega)
          have r := col_solve v cc a b ((x + 5 : ℤ) : ZMod k)
            (fun c h1 h2 => by rw [← Int.cast_add]; exact IH _ (by omega) (by omega))
            (ga _ hs).2 (gb _ hs).2
          rw [← Int.cast_add] at r
          have : x + 5 + -5 = x := by ring
          rwa [this] at r
    intro j hj
    obtain ⟨x, hx1, hx2, rfl⟩ := L2 j hj
    exact key _ x rfl hx1 hx2
  have vm2 := val_neg (k := k) (-2) (by omega) (by norm_num)
  have vm1 := val_neg (k := k) (-1) (by omega) (by norm_num)
  have v0 := val_pos (k := k) 0 (by norm_num) (by omega)
  have v1 := val_pos (k := k) 1 (by norm_num) (by omega)
  rw [em2] at vm2
  rw [em1] at vm1
  rw [e0] at v0
  rw [e1] at v1
  have hbase : ∀ z, ∃ b : ZMod k → ZMod 2, label b = z ∧ ∀ j, passive j → b j = 0 := by
    classical
    intro z
    have d21 : (-2 : ZMod k) ≠ -1 := fun e => by rw [e] at vm2; omega
    have d20 : (-2 : ZMod k) ≠ 0 := fun e => by rw [e] at vm2; omega
    have d23 : (-2 : ZMod k) ≠ 1 := fun e => by rw [e] at vm2; omega
    have d10 : (-1 : ZMod k) ≠ 0 := fun e => by rw [e] at vm1; omega
    have d13 : (-1 : ZMod k) ≠ 1 := fun e => by rw [e] at vm1; omega
    have d03 : (0 : ZMod k) ≠ 1 := fun e => by rw [e] at v0; omega
    refine ⟨fun j => if j = -2 then z.1 else if j = -1 then z.2.1 else if j = 0 then z.2.2.1
      else if j = 1 then z.2.2.2 else 0, ?_, ?_⟩
    · simp [label, d21, d20, d23, d10, d13, d03, d21.symm, d20.symm, d23.symm, d10.symm,
        d13.symm, d03.symm]
    · intro j hj
      obtain ⟨hp1, hp2⟩ := hj
      have n2 : j ≠ -2 := fun e => by rw [e] at hp1 hp2; omega
      have n1 : j ≠ -1 := fun e => by rw [e] at hp1 hp2; omega
      have n0 : j ≠ 0 := fun e => by rw [e] at hp1 hp2; omega
      have n3 : j ≠ 1 := fun e => by rw [e] at hp1 hp2; omega
      simp [n2, n1, n0, n3]
  have hcard : Nat.card {j // passive j} = k - h - 7 := by
    have e : {j // passive j} ≃ Fin (k - h - 7) :=
      { toFun := fun j => ⟨j.1.val - 2, by have := j.2; simp only [passive] at this; omega⟩
        invFun := fun i => ⟨((i.1 + 2 : ℕ) : ZMod k), by
          have : i.1 < k - h - 7 := i.2
          simp only [passive]
          rw [ZMod.val_natCast_of_lt (by omega)]
          omega⟩
        left_inv := by
          rintro ⟨j, hj1, hj2⟩
          apply Subtype.ext
          simp only
          rw [Nat.sub_add_cancel hj1, ZMod.natCast_zmod_val]
        right_inv := by
          intro i
          apply Fin.ext
          have : i.1 < k - h - 7 := i.2
          simp only
          rw [ZMod.val_natCast_of_lt (by omega)]
          omega }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact abstract good label passive (k - h - 7) hloc hlab huniq hbase hcard

end PEqualNP.Outside.L_meta_25835

theorem PEqualNP.Outside.L_meta_25835 : ∀ (k : ℕ) [NeZero k] (h : ℕ), 5 ≤ h → h + 7 ≤ k →
  let I := ZMod k
  let W := I → ZMod 2
  let lo := k - h
  let turn := fun (dist : ℕ) (word : W) (site : I) => word (site - (dist : I))
  let mix := fun (dist : ℕ) (word : W) (site : I) =>
    word (site - (dist : I)) + word site + word (site + (dist : I))
  let chi := fun (word : W) (site : I) =>
    word site + (1 + word (site+1)) * word (site+2)
  let tested := fun site : I => lo ≤ site.val
  ∀ (rowConst colConst : W),
    let good := fun (u v key : W) =>
      let row := chi (mix 1 (turn 1 key + u)) + key + rowConst
      let col := chi (mix 2 (turn 3 key + v)) + turn 4 key + colConst
      ∀ site : I, tested site → row site = 0 ∧ col site = 0
    let label := fun (key : W) => (key (-2), key (-1), key 0, key 1)
    let passive := fun site : I => 2 ≤ site.val ∧ site.val < lo-5
    ∀ u v : W, ∃ dec : (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) → W,
      (∀ z, label (dec z) = z ∧ ∀ j : I, passive j → dec z j = 0) ∧
      (∀ key : W, good u v key ↔ good u v (dec (label key)) ∧
        ∀ j : I, ¬ passive j → key j = dec (label key) j) ∧
      ∀ z, let num := Nat.card {raw : W // good u v raw ∧ label raw = z}
        (good u v (dec z) → num = 2^(lo-7)) ∧ (¬ good u v (dec z) → num = 0) := by
  intro k _ h h5 hk I W lo turn mix chi tested rowConst colConst good label passive u v
  exact PEqualNP.Outside.L_meta_25835.main k h h5 hk rowConst colConst u v
