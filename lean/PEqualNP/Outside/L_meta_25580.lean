import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25580

abbrev ev5 (t0 t1 t2 t3 t4 k : Bool) : Bool :=
  xor (xor (xor (xor t0 t1) t2) (!(xor (xor t1 t2) t3) && xor (xor t2 t3) t4)) k

def mixF (x : Int → Bool) (z : Int) : Bool := xor (xor (x (z-1)) (x z)) (x (z+1))

def updF (x inj : Int → Bool) (z : Int) : Bool :=
  xor (xor (mixF x z) (!(mixF x (z+1)) && mixF x (z+2))) (inj z)

abbrev fitsF (mode : Nat) (u v left right : Bool) : Prop :=
  if mode = 1 then ¬ (left = !u ∧ right = !v)
  else if mode = 2 then right = v
  else if mode = 3 then xor left right = !(xor u v)
  else True

abbrev M (t : Nat → Bool) (j : Nat) : Bool := xor (xor (t (j-1)) (t j)) (t (j+1))

abbrev U (t : Nat → Bool) (k : Bool) (j : Nat) : Bool :=
  ev5 (t (j-1)) (t j) (t (j+1)) (t (j+2)) (t (j+3)) k

abbrev T6 (a0 a1 a2 a3 a4 a5 : Bool) : Nat → Bool :=
  fun n => [a0, a1, a2, a3, a4, a5].getD n false

abbrev T8 (a0 a1 a2 a3 a4 a5 a6 a7 : Bool) : Nat → Bool :=
  fun n => [a0, a1, a2, a3, a4, a5, a6, a7].getD n false

abbrev alB (m : Nat) (N F : Bool) : Bool :=
  ((m == 1) && N && F) || ((m == 2) && F) || ((m == 3) && N)

abbrev dgB (m : Nat) (N F H : Bool) : Bool :=
  (m == 3) || (!H && (((m == 1) && !N && !F) || (m == 2)))

abbrev nxB (m : Nat) (N F H : Bool) : Nat :=
  if alB m N F then (if H then 0 else 2) else if dgB m N F H then 3 else 1

abbrev KB (m : Nat) (N F H : Bool) : Nat := H.toNat + (alB m N F && H).toNat

abbrev P1 : Prop := ∀ (m : Fin 4) (u v s3 s2 s1 s0 x1 x2 c1 c2 k1 k2 N F H : Bool),
  N = (s0 == !(xor u v)) → F = (s1 == v) → H = xor (xor s2 s1) s0 →
  fitsF m.val u v x1 x2 → fitsF m.val u v c1 c2 →
  (1 ≤ KB m.val N F H → U (T6 s3 s2 s1 s0 c1 c2) k1 1 = U (T6 s3 s2 s1 s0 x1 x2) k1 1) ∧
  (2 ≤ KB m.val N F H → U (T6 s3 s2 s1 s0 c1 c2) k2 2 = U (T6 s3 s2 s1 s0 x1 x2) k2 2) ∧
  (nxB m.val N F H ≠ 0 → M (T6 s3 s2 s1 s0 c1 c2) (KB m.val N F H + 1) =
    M (T6 s3 s2 s1 s0 x1 x2) (KB m.val N F H + 1))

abbrev P2 (m : Fin 4) : Prop := ∀ (u v s3 s2 s1 s0 x1 x2 p q N F H : Bool),
  N = (s0 == !(xor u v)) → F = (s1 == v) → H = xor (xor s2 s1) s0 →
  fitsF m.val u v x1 x2 → ∀ l r : Bool,
  (fitsF (nxB m.val N F H) (xor (M (T6 s3 s2 s1 s0 x1 x2) (KB m.val N F H + 1)) p) q l r ↔
    ∃ c1 c2 c3 c4 : Bool, fitsF m.val u v c1 c2 ∧
      U (T8 s3 s2 s1 s0 c1 c2 c3 c4) p (KB m.val N F H + 1) = l ∧
      U (T8 s3 s2 s1 s0 c1 c2 c3 c4) q (KB m.val N F H + 2) = r)

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p1 : P1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p2a : P2 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p2b : P2 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p2c : P2 2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem p2d : P2 3 := by decide +kernel

theorem p2all (m : Fin 4) : P2 m := by
  match m with
  | 0 => exact p2a
  | 1 => exact p2b
  | 2 => exact p2c
  | 3 => exact p2d

def tp (y : Int → Bool) (b : Int) (n : Nat) : Bool := y (b-3+(n:Int))

theorem tp_at (y : Int → Bool) (b : Int) (n : Nat) (z : Int) (h : z = b-3+(n:Int)) :
    y z = tp y b n := by
  rw [h]; rfl

theorem ev_eq (x inj : Int → Bool) (z : Int) :
    updF x inj z = ev5 (x (z-1)) (x z) (x (z+1)) (x (z+2)) (x (z+3)) (inj z) := by
  have h1 : z + 1 - 1 = z := by ring
  have h2 : z + 1 + 1 = z + 2 := by ring
  have h3 : z + 2 - 1 = z + 1 := by ring
  have h4 : z + 2 + 1 = z + 3 := by ring
  simp only [updF, mixF, ev5, h1, h2, h3, h4]

theorem upd_congr {x x' inj : Int → Bool} {z : Int}
    (h : ∀ s, s ≤ z + 3 → x s = x' s) : updF x inj z = updF x' inj z := by
  rw [ev_eq, ev_eq, h (z-1) (by omega), h z (by omega),
    h (z+1) (by omega), h (z+2) (by omega), h (z+3) (by omega)]

theorem U_eq (y inj : Int → Bool) (b : Int) (j : Nat) (hj : 1 ≤ j) :
    updF y inj (b-3+(j:Int)) = U (tp y b) (inj (b-3+(j:Int))) j := by
  rw [ev_eq]
  simp only [U]
  rw [tp_at y b (j-1) (b-3+(j:Int)-1) (by rw [Nat.cast_sub hj]; push_cast; ring),
    tp_at y b j (b-3+(j:Int)) rfl,
    tp_at y b (j+1) (b-3+(j:Int)+1) (by push_cast; ring),
    tp_at y b (j+2) (b-3+(j:Int)+2) (by push_cast; ring),
    tp_at y b (j+3) (b-3+(j:Int)+3) (by push_cast; ring)]

theorem M_eq (y : Int → Bool) (b : Int) (j : Nat) (hj : 1 ≤ j) :
    mixF y (b-3+(j:Int)) = M (tp y b) j := by
  simp only [mixF, M]
  rw [tp_at y b (j-1) (b-3+(j:Int)-1) (by rw [Nat.cast_sub hj]; push_cast; ring),
    tp_at y b j (b-3+(j:Int)) rfl,
    tp_at y b (j+1) (b-3+(j:Int)+1) (by push_cast; ring)]

theorem U_congr {t t' : Nat → Bool} {k : Bool} {j : Nat} (h : ∀ n, n ≤ j + 3 → t n = t' n) :
    U t k j = U t' k j := by
  simp only [U]
  rw [h (j-1) (by omega), h j (by omega), h (j+1) (by omega), h (j+2) (by omega),
    h (j+3) (by omega)]

theorem M_congr {t t' : Nat → Bool} {j : Nat} (h : ∀ n, n ≤ j + 1 → t n = t' n) :
    M t j = M t' j := by
  simp only [M]
  rw [h (j-1) (by omega), h j (by omega), h (j+1) (by omega)]

theorem key (x inj : Int → Bool) (b : Int) (mode : Fin 4) (u v : Bool)
    (hfit : fitsF mode.val u v (x (b+1)) (x (b+2))) :
    let near := x b == !(xor u v)
    let far := x (b-1) == v
    let hit := mixF x (b-1)
    let aligned := ((mode.val == 1) && near && far) || ((mode.val == 2) && far) ||
      ((mode.val == 3) && near)
    let diagonal := (mode.val == 3) ||
      (!hit && (((mode.val == 1) && !near && !far) || (mode.val == 2)))
    let nextMode : Nat := if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1
    let f := b-3+(hit.toNat : Int)+((aligned && hit).toNat : Int)
    let nextU := xor (mixF x (f+1)) (inj (f+1))
    let nextV := inj (f+2)
    let completion := fun (y : Int → Bool) =>
      (∀ z ≤ b, y z = x z) ∧ fitsF mode.val u v (y (b+1)) (y (b+2))
    (∀ y : Int → Bool, completion y →
      (∀ z ≤ f, updF y inj z = updF x inj z) ∧
      (nextMode ≠ 0 → xor (mixF y (f+1)) (inj (f+1)) = nextU)) ∧
    (∀ left right : Bool, fitsF nextMode nextU nextV left right ↔
      ∃ y : Int → Bool, completion y ∧
        updF y inj (f+1) = left ∧ updF y inj (f+2) = right) := by
  intro near far hit aligned diagonal nextMode f nextU nextV completion
  have hN : near = (tp x b 3 == !(xor u v)) := by
    show (x b == !(xor u v)) = _
    rw [tp_at x b 3 b (by push_cast; ring)]
  have hF : far = (tp x b 2 == v) := by
    show (x (b-1) == v) = _
    rw [tp_at x b 2 (b-1) (by push_cast; ring)]
  have hH : hit = xor (xor (tp x b 1) (tp x b 2)) (tp x b 3) := by
    show mixF x (b-1) = _
    simp only [mixF]
    rw [tp_at x b 1 (b-1-1) (by push_cast; ring), tp_at x b 2 (b-1) (by push_cast; ring),
      tp_at x b 3 (b-1+1) (by push_cast; ring)]
  have hfit' : fitsF mode.val u v (tp x b 4) (tp x b 5) := by
    rw [← tp_at x b 4 (b+1) (by push_cast; ring), ← tp_at x b 5 (b+2) (by push_cast; ring)]
    exact hfit
  obtain ⟨K, hKdef⟩ : ∃ K : Nat, hit.toNat + (aligned && hit).toNat = K := ⟨_, rfl⟩
  have hKB : KB mode.val near far hit = K := hKdef
  have hK2 : K ≤ 2 := by
    have := Bool.toNat_le hit
    have := Bool.toNat_le (aligned && hit)
    omega
  have hK : f = b - 3 + (K : Int) := by
    show b-3+(hit.toNat : Int)+((aligned && hit).toNat : Int) = _
    rw [← hKdef]; push_cast; ring
  have hf1 : f + 1 = b - 3 + ((K+1 : Nat) : Int) := by rw [hK]; push_cast; ring
  have hf2 : f + 2 = b - 3 + ((K+2 : Nat) : Int) := by rw [hK]; push_cast; ring
  have Ax : ∀ n, n ≤ 5 → tp x b n =
      T6 (tp x b 0) (tp x b 1) (tp x b 2) (tp x b 3) (tp x b 4) (tp x b 5) n := by
    intro n hn
    interval_cases n <;> rfl
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨hyx, hyfit⟩ := hy
    have hy3 : ∀ n, n ≤ 3 → tp y b n = tp x b n := fun n hn => hyx _ (by omega)
    have hyfit' : fitsF mode.val u v (tp y b 4) (tp y b 5) := by
      rw [← tp_at y b 4 (b+1) (by push_cast; ring), ← tp_at y b 5 (b+2) (by push_cast; ring)]
      exact hyfit
    have Ay : ∀ n, n ≤ 5 → tp y b n =
        T6 (tp x b 0) (tp x b 1) (tp x b 2) (tp x b 3) (tp y b 4) (tp y b 5) n := by
      intro n hn
      interval_cases n
      · exact hy3 0 (by norm_num)
      · exact hy3 1 (by norm_num)
      · exact hy3 2 (by norm_num)
      · exact hy3 3 (by norm_num)
      · rfl
      · rfl
    obtain ⟨C1, C2, C3⟩ := p1 mode u v (tp x b 0) (tp x b 1) (tp x b 2) (tp x b 3) (tp x b 4)
      (tp x b 5) (tp y b 4) (tp y b 5) (inj (b-3+((1:Nat):Int))) (inj (b-3+((2:Nat):Int)))
      near far hit hN hF hH hfit' hyfit'
    rw [hKB] at C1 C2 C3
    refine ⟨?_, ?_⟩
    · intro z hz
      by_cases h3 : z ≤ b - 3
      · exact upd_congr (fun s hs => hyx s (by omega))
      · rcases (show z = b-3+((1:Nat):Int) ∨ z = b-3+((2:Nat):Int) by omega) with rfl | rfl
        · rw [U_eq y inj b 1 le_rfl, U_eq x inj b 1 le_rfl,
            U_congr (j := 1) (fun n hn => Ay n (by omega)),
            U_congr (j := 1) (fun n hn => Ax n (by omega))]
          exact C1 (by omega)
        · rw [U_eq y inj b 2 (by norm_num), U_eq x inj b 2 (by norm_num),
            U_congr (j := 2) (fun n hn => Ay n (by omega)),
            U_congr (j := 2) (fun n hn => Ax n (by omega))]
          exact C2 (by omega)
    · intro hnm
      show xor (mixF y (f+1)) (inj (f+1)) = xor (mixF x (f+1)) (inj (f+1))
      rw [hf1, M_eq y b (K+1) (by omega), M_eq x b (K+1) (by omega),
        M_congr (j := K+1) (fun n hn => Ay n (by omega)),
        M_congr (j := K+1) (fun n hn => Ax n (by omega)), C3 hnm]
  · intro l r
    show fitsF nextMode (xor (mixF x (f+1)) (inj (f+1))) (inj (f+2)) l r ↔
      ∃ y : Int → Bool, ((∀ z ≤ b, y z = x z) ∧ fitsF mode.val u v (y (b+1)) (y (b+2))) ∧
        updF y inj (f+1) = l ∧ updF y inj (f+2) = r
    have hU1 : ∀ y : Int → Bool, updF y inj (b-3+((K+1:Nat):Int)) =
        U (tp y b) (inj (b-3+((K+1:Nat):Int))) (K+1) := fun y => U_eq y inj b (K+1) (by omega)
    have hU2 : ∀ y : Int → Bool, updF y inj (b-3+((K+2:Nat):Int)) =
        U (tp y b) (inj (b-3+((K+2:Nat):Int))) (K+2) := fun y => U_eq y inj b (K+2) (by omega)
    rw [hf1, hf2, M_eq x b (K+1) (by omega), M_congr (j := K+1) (fun n hn => Ax n (by omega))]
    simp only [hU1, hU2]
    have C := p2all mode u v (tp x b 0) (tp x b 1) (tp x b 2) (tp x b 3) (tp x b 4)
      (tp x b 5) (inj (b-3+((K+1:Nat):Int))) (inj (b-3+((K+2:Nat):Int)))
      near far hit hN hF hH hfit' l r
    rw [hKB] at C
    refine C.trans ⟨?_, ?_⟩
    · rintro ⟨c1, c2, c3, c4, hc, h1, h2⟩
      let y : Int → Bool := fun z =>
        if z ≤ b then x z else [c1, c2, c3, c4].getD (z-b-1).toNat false
      have Ay : ∀ n, n ≤ 7 → tp y b n =
          T8 (tp x b 0) (tp x b 1) (tp x b 2) (tp x b 3) c1 c2 c3 c4 n := by
        intro n hn
        simp only [tp, y]
        interval_cases n
        · rw [if_pos (by omega)]; rfl
        · rw [if_pos (by omega)]; rfl
        · rw [if_pos (by omega)]; rfl
        · rw [if_pos (by omega)]; rfl
        · rw [if_neg (by omega), show (b-3+((4:Nat):Int)-b-1).toNat = 0 by omega]; rfl
        · rw [if_neg (by omega), show (b-3+((5:Nat):Int)-b-1).toNat = 1 by omega]; rfl
        · rw [if_neg (by omega), show (b-3+((6:Nat):Int)-b-1).toNat = 2 by omega]; rfl
        · rw [if_neg (by omega), show (b-3+((7:Nat):Int)-b-1).toNat = 3 by omega]; rfl
      refine ⟨y, ⟨fun z hz => if_pos hz, ?_⟩, ?_, ?_⟩
      · rw [tp_at y b 4 (b+1) (by push_cast; ring), tp_at y b 5 (b+2) (by push_cast; ring),
          Ay 4 (by norm_num), Ay 5 (by norm_num)]
        exact hc
      · rw [U_congr (j := K+1) (fun n hn => Ay n (by omega))]
        exact h1
      · rw [U_congr (j := K+2) (fun n hn => Ay n (by omega))]
        exact h2
    · rintro ⟨y, ⟨hyx, hyfit⟩, h1, h2⟩
      have Ay : ∀ n, n ≤ 7 → tp y b n =
          T8 (tp x b 0) (tp x b 1) (tp x b 2) (tp x b 3) (tp y b 4) (tp y b 5) (tp y b 6)
            (tp y b 7) n := by
        intro n hn
        interval_cases n
        · exact hyx _ (by omega)
        · exact hyx _ (by omega)
        · exact hyx _ (by omega)
        · exact hyx _ (by omega)
        · rfl
        · rfl
        · rfl
        · rfl
      refine ⟨tp y b 4, tp y b 5, tp y b 6, tp y b 7, ?_, ?_, ?_⟩
      · rw [tp_at y b 4 (b+1) (by push_cast; ring), tp_at y b 5 (b+2) (by push_cast; ring)]
          at hyfit
        exact hyfit
      · rw [← U_congr (j := K+1) (fun n hn => Ay n (by omega))]
        exact h1
      · rw [← U_congr (j := K+2) (fun n hn => Ay n (by omega))]
        exact h2

end PEqualNP.Outside.L_meta_25580

open PEqualNP.Outside.L_meta_25580 in
theorem PEqualNP.Outside.L_meta_25580 :
    let mix := fun (x : Int → Bool) (z : Int) => xor (xor (x (z-1)) (x z)) (x (z+1))
    let update := fun (x inj : Int → Bool) (z : Int) =>
      xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (inj z)
    let fits := fun (mode : Nat) (u v left right : Bool) =>
      if mode = 1 then ¬ (left = !u ∧ right = !v)
      else if mode = 2 then right = v
      else if mode = 3 then xor left right = !(xor u v)
      else True
    ∀ (x inj : Int → Bool) (b : Int) (mode : Fin 4) (u v : Bool),
      fits mode.val u v (x (b+1)) (x (b+2)) →
      let near := x b == !(xor u v)
      let far := x (b-1) == v
      let hit := mix x (b-1)
      let aligned := ((mode.val == 1) && near && far) || ((mode.val == 2) && far) ||
        ((mode.val == 3) && near)
      let diagonal := (mode.val == 3) ||
        (!hit && (((mode.val == 1) && !near && !far) || (mode.val == 2)))
      let nextMode : Nat := if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1
      let f := b-3+(hit.toNat : Int)+((aligned && hit).toNat : Int)
      let nextU := xor (mix x (f+1)) (inj (f+1))
      let nextV := inj (f+2)
      let completion := fun (y : Int → Bool) =>
        (∀ z ≤ b, y z = x z) ∧ fits mode.val u v (y (b+1)) (y (b+2))
      (∀ y : Int → Bool, completion y →
        (∀ z ≤ f, update y inj z = update x inj z) ∧
        (nextMode ≠ 0 → xor (mix y (f+1)) (inj (f+1)) = nextU)) ∧
      (∀ left right : Bool, fits nextMode nextU nextV left right ↔
        ∃ y : Int → Bool, completion y ∧
          update y inj (f+1) = left ∧ update y inj (f+2) = right) := by
  intro mix update fits x inj b mode u v hfit
  exact key x inj b mode u v hfit
