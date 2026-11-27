import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25574

def mixF (x : Int → Bool) (z : Int) : Bool := xor (xor (x (z-1)) (x z)) (x (z+1))

def evolveF (x injection : Int → Bool) (z : Int) : Bool :=
  xor (xor (mixF x z) (!(mixF x (z+1)) && mixF x (z+2))) (injection z)

abbrev alF (m : Nat) (u v q r : Bool) : Bool :=
  ((m == 1) && (r == !(xor u v)) && (q == v)) || ((m == 2) && (q == v)) ||
    ((m == 3) && (r == !(xor u v)))

abbrev diF (m : Nat) (u v q r h : Bool) : Bool :=
  !h && (((m == 1) && !(r == !(xor u v)) && !(q == v)) || (m == 2) || (m == 3))

abbrev nmF (m : Nat) (u v q r h : Bool) : Nat :=
  if alF m u v q r then (if h then 0 else 2) else if diF m u v q r h then 3 else 1

abbrev KF (m : Nat) (u v q r h : Bool) : Nat := h.toNat + (alF m u v q r && h).toNat

abbrev St := (Int → Bool) × Int × Nat × Bool × Bool

def stepF (inj : Int → Bool) (st : St) : St :=
  let x := st.1
  let b := st.2.1
  let mode := st.2.2.1
  let u := st.2.2.2.1
  let v := st.2.2.2.2
  let near := x b == !(xor u v)
  let far := x (b-1) == v
  let hit := mixF x (b-1)
  let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
    ((mode == 3) && near)
  let diagonal := !hit && (((mode == 1) && !near && !far) ||
    (mode == 2) || (mode == 3))
  let nextMode : Nat := if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1
  let f := b-3+(hit.toNat : Int)+((aligned && hit).toNat : Int)
  (evolveF x inj, f, nextMode, xor (mixF x (f+1)) (inj (f+1)), inj (f+2))

def runF (initial : Int → Bool) (inject : Nat → Int → Bool) (origin : Int) (n : Nat) : St :=
  (List.range n).foldl (fun (st : St) (tick : Nat) => stepF (inject tick) st)
    (initial, origin, 0, false, false)

theorem run_succ (initial : Int → Bool) (inject : Nat → Int → Bool) (origin : Int) (n : Nat) :
    runF initial inject origin (n+1) = stepF (inject n) (runF initial inject origin n) := by
  simp only [runF, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

abbrev Qloc (m : Nat) (u v s1 s2 : Bool) : Prop :=
  (m = 1 → ¬ (s1 = !u ∧ s2 = !v)) ∧ (m = 2 → s2 = v) ∧ (m = 3 → xor s1 s2 = !(xor u v))

abbrev Qp (s : St) : Prop := Qloc s.2.2.1 s.2.2.2.1 s.2.2.2.2 (s.1 (s.2.1+1)) (s.1 (s.2.1+2))

abbrev Inv (o : Int) (sa sb : St) : Prop :=
  sa.2.1 = sb.2.1 ∧ sa.2.1 ≤ o ∧ sa.2.2.1 = sb.2.2.1 ∧ sa.2.2.1 < 4 ∧
    (∀ z ≤ sa.2.1, sa.1 z = sb.1 z) ∧
    (sa.2.2.1 ≠ 0 → sa.2.2.2.1 = sb.2.2.2.1 ∧ sa.2.2.2.2 = sb.2.2.2.2) ∧ Qp sa ∧ Qp sb

def selM (p q r s1 s2 s3 s4 : Bool) : Nat → Bool
  | 0 => xor (xor p q) r
  | 1 => xor (xor q r) s1
  | 2 => xor (xor r s1) s2
  | 3 => xor (xor s1 s2) s3
  | _ => xor (xor s2 s3) s4

abbrev Post (m : Nat) (u v p q r s1 s2 s3 s4 U V : Bool) : Prop :=
  Qloc (nmF m u v q r (selM p q r s1 s2 s3 s4 0)) U V
    (xor U (!(selM p q r s1 s2 s3 s4 (KF m u v q r (selM p q r s1 s2 s3 s4 0))) &&
      selM p q r s1 s2 s3 s4 (KF m u v q r (selM p q r s1 s2 s3 s4 0) + 1)))
    (xor (xor (selM p q r s1 s2 s3 s4 (KF m u v q r (selM p q r s1 s2 s3 s4 0))) V)
      (!(selM p q r s1 s2 s3 s4 (KF m u v q r (selM p q r s1 s2 s3 s4 0) + 1)) &&
        selM p q r s1 s2 s3 s4 (KF m u v q r (selM p q r s1 s2 s3 s4 0) + 2)))

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core1 : ∀ m, m < 4 → ∀ u v p q r s1 s2 s3 s4 U V : Bool,
    Qloc m u v s1 s2 → Post m u v p q r s1 s2 s3 s4 U V := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core2 : ∀ m, m < 4 → ∀ u v p q r s1 s2 s3 s4 : Bool,
    Qloc m u v s1 s2 → (alF m u v q r && xor (xor p q) r) = true →
    (!(selM p q r s1 s2 s3 s4 1) && selM p q r s1 s2 s3 s4 2) = false := by decide +kernel

theorem m0_indep : ∀ u v u' v' q r h : Bool,
    nmF 0 u v q r h = nmF 0 u' v' q r h ∧ KF 0 u v q r h = KF 0 u' v' q r h := by decide

theorem al0 : ∀ u v q r : Bool, alF 0 u v q r = false := by decide

theorem KF_le (m : Nat) (u v q r h : Bool) : KF m u v q r h ≤ 2 := by
  show h.toNat + (alF m u v q r && h).toNat ≤ 2
  generalize alF m u v q r = a
  cases a <;> cases h <;> decide

theorem KF_le1 (m : Nat) (u v q r h : Bool) (hal : (alF m u v q r && h) = false) :
    KF m u v q r h ≤ 1 := by
  show h.toNat + (alF m u v q r && h).toNat ≤ 1
  rw [hal]
  cases h <;> decide

theorem KF_pos (m : Nat) (u v q r h : Bool) (hk : 1 ≤ KF m u v q r h) : h = true := by
  revert hk
  show 1 ≤ h.toNat + (alF m u v q r && h).toNat → h = true
  generalize alF m u v q r = a
  cases a <;> cases h <;> decide

theorem KF_two (m : Nat) (u v q r h : Bool) (hk : KF m u v q r h = 2) :
    (alF m u v q r && h) = true := by
  revert hk
  show h.toNat + (alF m u v q r && h).toNat = 2 → (alF m u v q r && h) = true
  generalize alF m u v q r = a
  cases a <;> cases h <;> decide

theorem nm_ne (m : Nat) (u v q r h : Bool) (hne : nmF m u v q r h ≠ 0) :
    (alF m u v q r && h) = false := by
  revert hne
  unfold nmF
  generalize alF m u v q r = a
  cases a <;> cases h <;> simp

theorem nm_lt (m : Nat) (u v q r h : Bool) : nmF m u v q r h < 4 := by
  unfold nmF
  split_ifs <;> omega

theorem mix_pts (x : Int → Bool) (z a c d : Int) (ha : z - 1 = a) (hc : z = c) (hd : z + 1 = d) :
    mixF x z = xor (xor (x a) (x c)) (x d) := by
  unfold mixF
  rw [ha, hd, hc]

theorem mix_sel (x : Int → Bool) (b : Int) (j : Nat) (hj : j ≤ 4) :
    mixF x (b - 1 + (j : Int)) =
      selM (x (b-2)) (x (b-1)) (x b) (x (b+1)) (x (b+2)) (x (b+3)) (x (b+4)) j := by
  interval_cases j
  · exact mix_pts x _ (b-2) (b-1) b (by omega) (by omega) (by omega)
  · exact mix_pts x _ (b-1) b (b+1) (by omega) (by omega) (by omega)
  · exact mix_pts x _ b (b+1) (b+2) (by omega) (by omega) (by omega)
  · exact mix_pts x _ (b+1) (b+2) (b+3) (by omega) (by omega) (by omega)
  · exact mix_pts x _ (b+2) (b+3) (b+4) (by omega) (by omega) (by omega)

theorem mix_congr {x y : Int → Bool} {z : Int}
    (h : ∀ s, z - 1 ≤ s → s ≤ z + 1 → x s = y s) : mixF x z = mixF y z := by
  unfold mixF
  rw [h (z-1) (by omega) (by omega), h z (by omega) (by omega), h (z+1) (by omega) (by omega)]

theorem evolve_congr {x y inj inj' : Int → Bool} {z : Int}
    (h : ∀ s, z - 1 ≤ s → s ≤ z + 3 → x s = y s) (hi : inj z = inj' z) :
    evolveF x inj z = evolveF y inj' z := by
  unfold evolveF
  rw [mix_congr (z := z) (fun s h1 h2 => h s (by omega) (by omega)),
    mix_congr (z := z+1) (fun s h1 h2 => h s (by omega) (by omega)),
    mix_congr (z := z+2) (fun s h1 h2 => h s (by omega) (by omega)), hi]

theorem ev_split (x inj : Int → Bool) (z : Int) :
    evolveF x inj z = xor (xor (mixF x z) (inj z)) (!(mixF x (z+1)) && mixF x (z+2)) := by
  unfold evolveF
  generalize mixF x z = a
  generalize (!(mixF x (z+1)) && mixF x (z+2)) = c
  generalize inj z = k
  cases a <;> cases c <;> cases k <;> rfl

theorem step_edge (inj x : Int → Bool) (b : Int) (m : Nat) (u v : Bool) :
    (stepF inj (x, b, m, u, v)).2.1 =
      b - 3 + ((KF m u v (x (b-1)) (x b) (mixF x (b-1)) : Nat) : Int) := by
  show b - 3 + ((mixF x (b-1)).toNat : Int) +
    ((alF m u v (x (b-1)) (x b) && mixF x (b-1)).toNat : Int) = _
  rw [show ((KF m u v (x (b-1)) (x b) (mixF x (b-1)) : Nat) : Int) =
    ((mixF x (b-1)).toNat : Int) + ((alF m u v (x (b-1)) (x b) && mixF x (b-1)).toNat : Int)
    from Nat.cast_add _ _]
  ring

theorem step_u (inj x : Int → Bool) (b : Int) (m : Nat) (u v : Bool) :
    (stepF inj (x, b, m, u, v)).2.2.2.1 =
      xor (mixF x ((stepF inj (x, b, m, u, v)).2.1 + 1))
        (inj ((stepF inj (x, b, m, u, v)).2.1 + 1)) := rfl

theorem step_v (inj x : Int → Bool) (b : Int) (m : Nat) (u v : Bool) :
    (stepF inj (x, b, m, u, v)).2.2.2.2 = inj ((stepF inj (x, b, m, u, v)).2.1 + 2) := rfl

theorem stepQ (inj x : Int → Bool) (b : Int) (m : Nat) (u v : Bool) (hm : m < 4)
    (hQ : Qloc m u v (x (b+1)) (x (b+2))) : Qp (stepF inj (x, b, m, u, v)) := by
  have h0 : mixF x (b-1) =
      selM (x (b-2)) (x (b-1)) (x b) (x (b+1)) (x (b+2)) (x (b+3)) (x (b+4)) 0 :=
    mix_pts x _ (b-2) (b-1) b (by omega) rfl (by omega)
  show Qloc (nmF m u v (x (b-1)) (x b) (mixF x (b-1)))
    (xor (mixF x ((stepF inj (x, b, m, u, v)).2.1 + 1)) (inj ((stepF inj (x, b, m, u, v)).2.1 + 1)))
    (inj ((stepF inj (x, b, m, u, v)).2.1 + 2))
    (evolveF x inj ((stepF inj (x, b, m, u, v)).2.1 + 1))
    (evolveF x inj ((stepF inj (x, b, m, u, v)).2.1 + 2))
  generalize hEdef : (stepF inj (x, b, m, u, v)).2.1 = E
  rw [step_edge] at hEdef
  rw [h0] at hEdef ⊢
  rw [ev_split, ev_split]
  have hK := KF_le m u v (x (b-1)) (x b)
    (selM (x (b-2)) (x (b-1)) (x b) (x (b+1)) (x (b+2)) (x (b+3)) (x (b+4)) 0)
  set K := KF m u v (x (b-1)) (x b)
    (selM (x (b-2)) (x (b-1)) (x b) (x (b+1)) (x (b+2)) (x (b+3)) (x (b+4)) 0) with hKd
  rw [show E + 1 + 1 = b - 1 + ((K : Nat) : Int) by omega,
    show E + 1 + 2 = b - 1 + ((K + 1 : Nat) : Int) by push_cast; omega,
    show E + 2 + 1 = b - 1 + ((K + 1 : Nat) : Int) by push_cast; omega,
    show E + 2 + 2 = b - 1 + ((K + 2 : Nat) : Int) by push_cast; omega,
    show E + 2 = b - 1 + ((K : Nat) : Int) by omega]
  rw [mix_sel x b K (by omega), mix_sel x b (K+1) (by omega), mix_sel x b (K+2) (by omega)]
  generalize xor (mixF x (E + 1)) (inj (E + 1)) = U
  generalize inj (b - 1 + ((K : Nat) : Int)) = V
  exact core1 m hm u v _ _ _ _ _ _ _ U V hQ

theorem step_inv (o : Int) (x y ia ib : Int → Bool) (b : Int) (m : Nat) (u v u' v' : Bool)
    (hI : ∀ z ≤ o + 1, ia z = ib z) (hb : b ≤ o) (hm : m < 4) (hx : ∀ z ≤ b, x z = y z)
    (huv : m ≠ 0 → u = u' ∧ v = v') (hQa : Qloc m u v (x (b+1)) (x (b+2)))
    (hQb : Qloc m u' v' (y (b+1)) (y (b+2))) :
    Inv o (stepF ia (x, b, m, u, v)) (stepF ib (y, b, m, u', v')) := by
  have hq : y (b-1) = x (b-1) := (hx _ (by omega)).symm
  have hr : y b = x b := (hx _ le_rfl).symm
  have hh : mixF y (b-1) = mixF x (b-1) :=
    (mix_congr (z := b-1) (fun s h1 h2 => hx s (by omega))).symm
  have hmx : mixF x (b-1) = xor (xor (x (b-2)) (x (b-1))) (x b) :=
    mix_pts x _ (b-2) (b-1) b (by omega) rfl (by omega)
  have key : nmF m u v (x (b-1)) (x b) (mixF x (b-1)) =
      nmF m u' v' (x (b-1)) (x b) (mixF x (b-1)) ∧
      KF m u v (x (b-1)) (x b) (mixF x (b-1)) = KF m u' v' (x (b-1)) (x b) (mixF x (b-1)) := by
    by_cases h0 : m = 0
    · subst h0
      exact m0_indep _ _ _ _ _ _ _
    · obtain ⟨rfl, rfl⟩ := huv h0
      exact ⟨rfl, rfl⟩
  have hK2 := KF_le m u v (x (b-1)) (x b) (mixF x (b-1))
  have hEa := step_edge ia x b m u v
  have hEb : (stepF ib (y, b, m, u', v')).2.1 =
      b - 3 + ((KF m u v (x (b-1)) (x b) (mixF x (b-1)) : Nat) : Int) := by
    rw [step_edge, hq, hr, hh, ← key.2]
  have hMa : (stepF ia (x, b, m, u, v)).2.2.1 = nmF m u v (x (b-1)) (x b) (mixF x (b-1)) := rfl
  have hMb : (stepF ib (y, b, m, u', v')).2.2.1 = nmF m u v (x (b-1)) (x b) (mixF x (b-1)) := by
    show nmF m u' v' (y (b-1)) (y b) (mixF y (b-1)) = _
    rw [hq, hr, hh, key.1]
  refine ⟨by rw [hEa, hEb], by rw [hEa]; omega, by rw [hMa, hMb], by rw [hMa]; exact nm_lt _ _ _ _ _ _,
    ?_, ?_, stepQ ia x b m u v hm hQa, stepQ ib y b m u' v' hm hQb⟩
  · intro z hz
    rw [hEa] at hz
    show evolveF x ia z = evolveF y ib z
    by_cases hz3 : z ≤ b - 3
    · exact evolve_congr (fun s h1 h2 => hx s (by omega)) (hI z (by omega))
    · have hK1 : 1 ≤ KF m u v (x (b-1)) (x b) (mixF x (b-1)) := by omega
      have ht : mixF x (b-1) = true := KF_pos _ _ _ _ _ _ hK1
      rcases (show z = b - 2 ∨ z = b - 1 by omega) with rfl | rfl
      · rw [ev_split, ev_split, show b - 2 + 1 = b - 1 by ring, hh, ht,
          mix_congr (x := x) (y := y) (z := b - 2) (fun s h1 h2 => hx s (by omega)),
          hI (b-2) (by omega)]
        simp
      · have hKe : KF m u v (x (b-1)) (x b) (mixF x (b-1)) = 2 := by omega
        have hal := KF_two _ _ _ _ _ _ hKe
        rw [hmx] at hal
        have hm0 : m ≠ 0 := by
          intro h0
          subst h0
          rw [al0] at hal
          simp at hal
        obtain ⟨rfl, rfl⟩ := huv hm0
        rw [ev_split, ev_split, hh, hI (b-1) (by omega)]
        congr 1
        rw [show b - 1 + 1 = b - 1 + ((1 : Nat) : Int) by norm_num,
          show b - 1 + 2 = b - 1 + ((2 : Nat) : Int) by norm_num,
          mix_sel x b 1 (by norm_num), mix_sel x b 2 (by norm_num),
          mix_sel y b 1 (by norm_num), mix_sel y b 2 (by norm_num),
          ← hx (b-2) (by omega), ← hx (b-1) (by omega), ← hx b le_rfl]
        rw [core2 m hm _ _ _ _ _ _ _ _ _ hQa hal, core2 m hm _ _ _ _ _ _ _ _ _ hQb hal]
  · intro hne
    rw [hMa] at hne
    have hK1 := KF_le1 _ _ _ _ _ _ (nm_ne _ _ _ _ _ _ hne)
    rw [step_u, step_u, step_v, step_v, hEa, hEb]
    refine ⟨?_, hI _ (by omega)⟩
    rw [mix_congr (z := b - 3 + ((KF m u v (x (b-1)) (x b) (mixF x (b-1)) : Nat) : Int) + 1)
      (fun s h1 h2 => hx s (by omega)),
      hI (b - 3 + ((KF m u v (x (b-1)) (x b) (mixF x (b-1)) : Nat) : Int) + 1) (by omega)]

theorem step_inv' (o : Int) (ia ib : Int → Bool) (hI : ∀ z ≤ o + 1, ia z = ib z)
    (sa sb : St) (h : Inv o sa sb) : Inv o (stepF ia sa) (stepF ib sb) := by
  obtain ⟨x, b, m, u, v⟩ := sa
  obtain ⟨y, b', m', u', v'⟩ := sb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  change b = b' at h1
  change m = m' at h3
  subst h1 h3
  exact step_inv o x y ia ib b m u v u' v' hI h2 h4 h5 h6 h7 h8

theorem run_inv (x y : Int → Bool) (i j : Nat → Int → Bool) (o : Int)
    (hx : ∀ z ≤ o, x z = y z) : ∀ n : Nat, (∀ t < n, ∀ z ≤ o + 1, i t z = j t z) →
      Inv o (runF x i o n) (runF y j o n)
  | 0, _ => by
    show Inv o (x, o, 0, false, false) (y, o, 0, false, false)
    refine ⟨rfl, le_rfl, rfl, by norm_num, hx, fun h => absurd rfl h, ?_, ?_⟩ <;>
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by norm_num)
  | n+1, hij => by
    rw [run_succ, run_succ]
    exact step_inv' o (i n) (j n) (hij n (by omega)) _ _
      (run_inv x y i j o hx n (fun t ht => hij t (by omega)))

end PEqualNP.Outside.L_meta_25574

open PEqualNP.Outside.L_meta_25574 in
theorem PEqualNP.Outside.L_meta_25574 :
    let mix := fun (x : Int → Bool) (z : Int) => xor (xor (x (z-1)) (x z)) (x (z+1))
    let evolve := fun (x injection : Int → Bool) (z : Int) =>
      xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (injection z)
    let run := fun (initial : Int → Bool) (inject : Nat → Int → Bool) (origin : Int) (n : Nat) =>
      (List.range n).foldl (fun (st : (Int → Bool) × Int × Nat × Bool × Bool) tick =>
        let x := st.1
        let b := st.2.1
        let mode := st.2.2.1
        let u := st.2.2.2.1
        let v := st.2.2.2.2
        let near := x b == !(xor u v)
        let far := x (b-1) == v
        let hit := mix x (b-1)
        let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
          ((mode == 3) && near)
        let diagonal := !hit && (((mode == 1) && !near && !far) ||
          (mode == 2) || (mode == 3))
        let nextMode : Nat := if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1
        let f := b-3+(hit.toNat : Int)+((aligned && hit).toNat : Int)
        (evolve x (inject tick), f, nextMode,
          xor (mix x (f+1)) (inject tick (f+1)), inject tick (f+2)))
        (initial, origin, 0, false, false)
    ∀ (n : Nat) (origin : Int) (x y : Int → Bool) (i j : Nat → Int → Bool),
      (∀ z ≤ origin, x z = y z) →
      (∀ t < n, ∀ z ≤ origin+1, i t z = j t z) →
      let a := run x i origin n
      let b := run y j origin n
      let edge := a.2.1
      let mode := a.2.2.1
      let u := a.2.2.2.1
      let v := a.2.2.2.2
      edge = b.2.1 ∧ mode = b.2.2.1 ∧ (∀ z ≤ edge, a.1 z = b.1 z) ∧
        (mode ≠ 0 → u = b.2.2.2.1 ∧ v = b.2.2.2.2) ∧
        (mode = 1 → ¬ (a.1 (edge+1) = !u ∧ a.1 (edge+2) = !v)) ∧
        (mode = 2 → a.1 (edge+2) = v) ∧
        (mode = 3 → xor (a.1 (edge+1)) (a.1 (edge+2)) = !(xor u v)) := by
  intro mix evolve run n origin x y i j hx hij a b edge mode u v
  obtain ⟨h1, -, h3, -, h5, h6, h7, -⟩ := run_inv x y i j origin hx n hij
  exact ⟨h1, h3, h5, h6, h7⟩
