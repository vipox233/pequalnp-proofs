import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33658

open Fin.CommRing

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

theorem natEq (a b : ℕ) (ha : a < k) (hb : b < k) : ((a : Fin k) = (b : Fin k)) ↔ a = b := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rwa [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro h; rw [h]

theorem eqShift (X Y U V : Fin k) (h : X - Y = U - V) : (X = Y) ↔ (U = V) := by
  rw [← sub_eq_zero, h, sub_eq_zero]

def Mx (g : ℕ) (x : Fin k → Bool) (p : Fin k) : Bool :=
  xor (xor (x (p - (g : Fin k))) (x p)) (x (p + (g : Fin k)))
def St (z : Fin k → Bool) (p : Fin k) : Bool :=
  xor (z p) (!(z (p + ((1 : ℕ) : Fin k))) && z (p + ((2 : ℕ) : Fin k)))
def Rt (s : ℕ) (x : Fin k → Bool) (p : Fin k) : Bool := x (p - (s : Fin k))
def Ad (x y : Fin k → Bool) (p : Fin k) : Bool := xor (x p) (y p)
def Rd (g ini fin : ℕ) (c name x : Fin k → Bool) (p : Fin k) : Bool :=
  xor (St (Mx g (Ad (Rt ini x) name)) p) (xor (Rt fin x p) (c p))
def dl (f : Fin k) (q : Fin k) : Bool := decide (q = f)
def Dl (z1 z2 e0 e1 e2 : Bool) : Bool := xor e0 (xor ((!(xor z1 e1)) && (xor z2 e2)) (!z1 && z2))

theorem bx6 : ∀ a b c d e f : Bool,
    xor (xor (xor a d) (xor b e)) (xor c f) = xor (xor (xor a b) c) (xor (xor d e) f) := by
  decide

theorem Mx_ad (g : ℕ) (Y N : Fin k → Bool) : Mx g (Ad Y N) = Ad (Mx g Y) (Mx g N) := by
  funext q; exact bx6 _ _ _ _ _ _

theorem bst : ∀ z0 z1 z2 e0 e1 e2 : Bool, xor (xor z0 e0) (!(xor z1 e1) && xor z2 e2) =
    xor (xor z0 (!z1 && z2)) (Dl z1 z2 e0 e1 e2) := by decide

theorem St_ad (Z E : Fin k → Bool) (p : Fin k) : St (Ad Z E) p = xor (St Z p)
    (Dl (Z (p + ((1 : ℕ) : Fin k))) (Z (p + ((2 : ℕ) : Fin k))) (E p) (E (p + ((1 : ℕ) : Fin k)))
      (E (p + ((2 : ℕ) : Fin k)))) := by
  exact bst _ _ _ _ _ _

theorem bx3 : ∀ a b d : Bool, xor (xor a d) b = xor (xor a b) d := by decide

theorem Rd_flip (g ini fin : ℕ) (cv N x : Fin k → Bool) (p : Fin k) :
    Rd g ini fin cv N x p = xor (Rd g ini fin cv (fun _ => false) x p)
      (Dl (Mx g (Rt ini x) (p + ((1 : ℕ) : Fin k))) (Mx g (Rt ini x) (p + ((2 : ℕ) : Fin k)))
        (Mx g N p) (Mx g N (p + ((1 : ℕ) : Fin k))) (Mx g N (p + ((2 : ℕ) : Fin k)))) := by
  have h0 : Ad (Rt ini x) (fun _ => false) = Rt ini x := funext (fun q => Bool.xor_false _)
  simp only [Rd]
  rw [h0, Mx_ad, St_ad]
  exact bx3 _ _ _

theorem Eval (c : Fin k) (g s t r : ℕ) (q : Fin k) (hq : q = c - (t : Fin k) + (r : Fin k))
    (h1 : t + s + g < k) (h2 : r + g < k) :
    Mx g (dl (c + (s : Fin k))) q = xor (xor (decide (r = t + s + g)) (decide (r = t + s)))
      (decide (r + g = t + s)) := by
  subst hq
  simp only [Mx, dl]
  have e1 : (c - (t : Fin k) + (r : Fin k) - (g : Fin k) = c + (s : Fin k)) ↔ r = t + s + g := by
    rw [eqShift _ _ (r : Fin k) ((t + s + g : ℕ) : Fin k) (by push_cast; ring),
      natEq _ _ (by omega) (by omega)]
  have e2 : (c - (t : Fin k) + (r : Fin k) = c + (s : Fin k)) ↔ r = t + s := by
    rw [eqShift _ _ (r : Fin k) ((t + s : ℕ) : Fin k) (by push_cast; ring),
      natEq _ _ (by omega) (by omega)]
  have e3 : (c - (t : Fin k) + (r : Fin k) + (g : Fin k) = c + (s : Fin k)) ↔ r + g = t + s := by
    rw [eqShift _ _ ((r + g : ℕ) : Fin k) ((t + s : ℕ) : Fin k) (by push_cast; ring),
      natEq _ _ (by omega) (by omega)]
  simp only [e1, e2, e3]

theorem Dl_far (c : Fin k) (g s t : ℕ) (Z : Fin k → Bool) (hg : g = 1 ∨ g = 2)
    (hs : 2 ≤ s ∧ s ≤ 4) (hgs : g = 1 ∨ 3 ≤ s) (ht : 2 ≤ t) (htk : t + 8 ≤ k) :
    Dl (Z (c - (t : Fin k) + ((1 : ℕ) : Fin k))) (Z (c - (t : Fin k) + ((2 : ℕ) : Fin k)))
      (Mx g (dl (c + (s : Fin k))) (c - (t : Fin k)))
      (Mx g (dl (c + (s : Fin k))) (c - (t : Fin k) + ((1 : ℕ) : Fin k)))
      (Mx g (dl (c + (s : Fin k))) (c - (t : Fin k) + ((2 : ℕ) : Fin k))) = false := by
  rw [Eval c g s t 0 _ (by simp) (by omega) (by omega), Eval c g s t 1 _ rfl (by omega) (by omega),
    Eval c g s t 2 _ rfl (by omega) (by omega)]
  simp only [show decide (0 = t + s + g) = false from decide_eq_false (by omega),
    show decide (0 = t + s) = false from decide_eq_false (by omega),
    show decide (0 + g = t + s) = false from decide_eq_false (by omega),
    show decide (1 = t + s + g) = false from decide_eq_false (by omega),
    show decide (1 = t + s) = false from decide_eq_false (by omega),
    show decide (1 + g = t + s) = false from decide_eq_false (by omega),
    show decide (2 = t + s + g) = false from decide_eq_false (by omega),
    show decide (2 = t + s) = false from decide_eq_false (by omega),
    show decide (2 + g = t + s) = false from decide_eq_false (by omega)]
  cases Z (c - (t : Fin k) + ((1 : ℕ) : Fin k)) <;> cases Z (c - (t : Fin k) + ((2 : ℕ) : Fin k)) <;>
    rfl

theorem Dl_one (c : Fin k) (g s : ℕ) (Z : Fin k → Bool) (hg : g = 1 ∨ g = 2)
    (hs : 2 ≤ s ∧ s ≤ 4) (hgs : g = 1 ∨ 3 ≤ s) (htk : 9 ≤ k) (hZ : Z c = true) :
    Dl (Z (c - ((1 : ℕ) : Fin k) + ((1 : ℕ) : Fin k))) (Z (c - ((1 : ℕ) : Fin k) + ((2 : ℕ) : Fin k)))
      (Mx g (dl (c + (s : Fin k))) (c - ((1 : ℕ) : Fin k)))
      (Mx g (dl (c + (s : Fin k))) (c - ((1 : ℕ) : Fin k) + ((1 : ℕ) : Fin k)))
      (Mx g (dl (c + (s : Fin k))) (c - ((1 : ℕ) : Fin k) + ((2 : ℕ) : Fin k))) = false := by
  rw [Eval c g s 1 0 _ (by simp) (by omega) (by omega), Eval c g s 1 1 _ rfl (by omega) (by omega)]
  rw [show c - ((1 : ℕ) : Fin k) + ((1 : ℕ) : Fin k) = c by ring, hZ]
  simp only [show decide (0 = 1 + s + g) = false from decide_eq_false (by omega),
    show decide (0 = 1 + s) = false from decide_eq_false (by omega),
    show decide (0 + g = 1 + s) = false from decide_eq_false (by omega),
    show decide (1 = 1 + s + g) = false from decide_eq_false (by omega),
    show decide (1 = 1 + s) = false from decide_eq_false (by omega),
    show decide (1 + g = 1 + s) = false from decide_eq_false (by omega)]
  cases Z (c - ((1 : ℕ) : Fin k) + ((2 : ℕ) : Fin k)) <;>
    cases Mx g (dl (c + (s : Fin k))) (c - ((1 : ℕ) : Fin k) + ((2 : ℕ) : Fin k)) <;> rfl

/-- The flipped bank agrees with the base bank except at the last window site. -/
theorem bankCmp (c : Fin k) (h : ℕ) (hhk : h + 7 ≤ k) (g ini fin s : ℕ) (cv y : Fin k → Bool)
    (hg : g = 1 ∨ g = 2) (hs : 2 ≤ s ∧ s ≤ 4) (hgs : g = 1 ∨ 3 ≤ s)
    (hZ : Mx g (Rt ini y) c = true) (t : ℕ) (ht : t + 1 ≤ h) :
    Rd g ini fin cv (dl (c + (s : Fin k))) y (c - (t : Fin k)) =
      xor (Rd g ini fin cv (fun _ => false) y (c - (t : Fin k)))
        (if t = 0 then Dl (Mx g (Rt ini y) (c + ((1 : ℕ) : Fin k)))
          (Mx g (Rt ini y) (c + ((2 : ℕ) : Fin k))) (Mx g (dl (c + (s : Fin k))) c)
          (Mx g (dl (c + (s : Fin k))) (c + ((1 : ℕ) : Fin k)))
          (Mx g (dl (c + (s : Fin k))) (c + ((2 : ℕ) : Fin k))) else false) := by
  rw [Rd_flip]
  congr 1
  rcases Nat.lt_or_ge t 2 with h2 | h2
  · interval_cases t
    · simp
    · simp only [one_ne_zero, ↓reduceIte]
      exact Dl_one c g s _ hg hs hgs (by omega) hZ
  · simp only [show t ≠ 0 by omega, ↓reduceIte]
    exact Dl_far c g s t _ hg hs hgs h2 (by omega)

def kb (r1 r2 c1 c2 A B : Bool) : List Bool :=
  let a0 := xor (xor A true) (!r1 && r2)
  let am4 := xor (xor B true) (!c1 && c2)
  let am2 := xor (xor c1 am4) a0
  let am1 := xor (xor true am2) a0
  let a1 := xor (xor r1 am1) a0
  let a2 := xor (xor r2 a0) a1
  let am3 := xor (xor c2 am1) a1
  let am5 := xor (xor true am3) am1
  [am5, am4, am3, am2, am1, a0, a1, a2]

theorem kb_spec : ∀ r1 r2 c1 c2 A B : Bool,
    xor (xor ((kb r1 r2 c1 c2 A B).getD 3 false) ((kb r1 r2 c1 c2 A B).getD 4 false))
      ((kb r1 r2 c1 c2 A B).getD 5 false) = true ∧
    xor (xor ((kb r1 r2 c1 c2 A B).getD 4 false) ((kb r1 r2 c1 c2 A B).getD 5 false))
      ((kb r1 r2 c1 c2 A B).getD 6 false) = r1 ∧
    xor (xor ((kb r1 r2 c1 c2 A B).getD 5 false) ((kb r1 r2 c1 c2 A B).getD 6 false))
      ((kb r1 r2 c1 c2 A B).getD 7 false) = r2 ∧
    xor (xor ((kb r1 r2 c1 c2 A B).getD 0 false) ((kb r1 r2 c1 c2 A B).getD 2 false))
      ((kb r1 r2 c1 c2 A B).getD 4 false) = true ∧
    xor (xor ((kb r1 r2 c1 c2 A B).getD 1 false) ((kb r1 r2 c1 c2 A B).getD 3 false))
      ((kb r1 r2 c1 c2 A B).getD 5 false) = c1 ∧
    xor (xor ((kb r1 r2 c1 c2 A B).getD 2 false) ((kb r1 r2 c1 c2 A B).getD 4 false))
      ((kb r1 r2 c1 c2 A B).getD 6 false) = c2 ∧
    xor (xor true (!r1 && r2)) (xor ((kb r1 r2 c1 c2 A B).getD 5 false) A) = false ∧
    xor (xor true (!c1 && c2)) (xor ((kb r1 r2 c1 c2 A B).getD 1 false) B) = false := by
  decide

def key (c : Fin k) (L : List Bool) (q : Fin k) : Bool := L.getD (q - c + ((5 : ℕ) : Fin k)).val false

theorem keyAt (c : Fin k) (L : List Bool) (q : Fin k) (n : ℕ) (hn : n < k)
    (hq : q - c + ((5 : ℕ) : Fin k) = (n : Fin k)) : key c L q = L.getD n false := by
  unfold key; rw [hq, Fin.val_natCast, Nat.mod_eq_of_lt hn]

theorem ZrAt (c : Fin k) (hk : 8 ≤ k) (L : List Bool) (d : ℕ) (hd : d ≤ 2) (q : Fin k)
    (hq : q = c + (d : Fin k)) :
    Mx 1 (Rt 1 (key c L)) q = xor (xor (L.getD (d + 3) false) (L.getD (d + 4) false))
      (L.getD (d + 5) false) := by
  simp only [Mx, Rt]
  rw [keyAt c L _ (d + 3) (by omega) (by rw [hq]; push_cast; ring),
    keyAt c L _ (d + 4) (by omega) (by rw [hq]; push_cast; ring),
    keyAt c L _ (d + 5) (by omega) (by rw [hq]; push_cast; ring)]

theorem ZcAt (c : Fin k) (hk : 8 ≤ k) (L : List Bool) (d : ℕ) (hd : d ≤ 2) (q : Fin k)
    (hq : q = c + (d : Fin k)) :
    Mx 2 (Rt 3 (key c L)) q = xor (xor (L.getD d false) (L.getD (d + 2) false))
      (L.getD (d + 4) false) := by
  simp only [Mx, Rt]
  rw [keyAt c L _ d (by omega) (by rw [hq]; push_cast; ring),
    keyAt c L _ (d + 2) (by omega) (by rw [hq]; push_cast; ring),
    keyAt c L _ (d + 4) (by omega) (by rw [hq]; push_cast; ring)]


theorem keyFacts (c : Fin k) (hk : 8 ≤ k) (r1 r2 c1 c2 A B : Bool) (cr cq : Fin k → Bool)
    (hA : cr c = A) (hB : cq c = B) :
    Mx 1 (Rt 1 (key c (kb r1 r2 c1 c2 A B))) c = true ∧
    Mx 1 (Rt 1 (key c (kb r1 r2 c1 c2 A B))) (c + ((1 : ℕ) : Fin k)) = r1 ∧
    Mx 1 (Rt 1 (key c (kb r1 r2 c1 c2 A B))) (c + ((2 : ℕ) : Fin k)) = r2 ∧
    Mx 2 (Rt 3 (key c (kb r1 r2 c1 c2 A B))) c = true ∧
    Mx 2 (Rt 3 (key c (kb r1 r2 c1 c2 A B))) (c + ((1 : ℕ) : Fin k)) = c1 ∧
    Mx 2 (Rt 3 (key c (kb r1 r2 c1 c2 A B))) (c + ((2 : ℕ) : Fin k)) = c2 ∧
    Rd 1 1 0 cr (fun _ => false) (key c (kb r1 r2 c1 c2 A B)) c = false ∧
    Rd 2 3 4 cq (fun _ => false) (key c (kb r1 r2 c1 c2 A B)) c = false := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := kb_spec r1 r2 c1 c2 A B
  have f1 := (ZrAt c hk (kb r1 r2 c1 c2 A B) 0 (by omega) c (by simp)).trans s1
  have f2 := (ZrAt c hk (kb r1 r2 c1 c2 A B) 1 (by omega) _ rfl).trans s2
  have f3 := (ZrAt c hk (kb r1 r2 c1 c2 A B) 2 (by omega) _ rfl).trans s3
  have f4 := (ZcAt c hk (kb r1 r2 c1 c2 A B) 0 (by omega) c (by simp)).trans s4
  have f5 := (ZcAt c hk (kb r1 r2 c1 c2 A B) 1 (by omega) _ rfl).trans s5
  have f6 := (ZcAt c hk (kb r1 r2 c1 c2 A B) 2 (by omega) _ rfl).trans s6
  have h0 : ∀ (s : ℕ) (x : Fin k → Bool), Ad (Rt s x) (fun _ => false) = Rt s x :=
    fun s x => funext (fun q => Bool.xor_false _)
  have g5 : Rt 0 (key c (kb r1 r2 c1 c2 A B)) c = (kb r1 r2 c1 c2 A B).getD 5 false :=
    keyAt c _ _ 5 (by omega) (by push_cast; ring)
  have g1 : Rt 4 (key c (kb r1 r2 c1 c2 A B)) c = (kb r1 r2 c1 c2 A B).getD 1 false :=
    keyAt c _ _ 1 (by omega) (by push_cast; ring)
  refine ⟨f1, f2, f3, f4, f5, f6, ?_, ?_⟩
  · simp only [Rd]; rw [h0]; simp only [St]; rw [f1, f2, f3, g5, hA]; exact s7
  · simp only [Rd]; rw [h0]; simp only [St]; rw [f4, f5, f6, g1, hB]; exact s8

theorem bxd : ∀ a d : Bool, xor a d = a → d = false := by decide

end PEqualNP.Outside.L_meta_33658

open Fin.CommRing PEqualNP.Outside.L_meta_33658 in
theorem PEqualNP.Outside.L_meta_33658 : ∀ (k h start : Nat) (hk : 0 < k), 0 < h → h+7 ≤ k →
      let W := Fin k → Bool
      let ix := fun i : Nat => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
      let add := fun (x y : W) (p : Fin k) => xor (x p) (y p)
      let mix := fun (gap : Nat) (x : W) (p : Fin k) =>
        xor (xor (x (ix (p.val + k - gap % k))) (x p)) (x (ix (p.val + gap)))
      let step := fun (z : W) (p : Fin k) =>
        xor (z p) (!(z (ix (p.val+1))) && z (ix (p.val+2)))
      let rot := fun (s : Nat) (x : W) (p : Fin k) => x (ix (p.val + k - s % k))
      ∀ (rc cc : W),
        let read := fun (gap ini fin : Nat) (c name x : W) (j : Fin h) =>
          let p := ix (start+j.val)
          xor (step (mix gap (add (rot ini x) name)) p) (xor (rot fin x p) (c p))
        let reply := fun (names : W × W) (x : W) =>
          (read 1 1 0 rc names.1 x, read 2 3 4 cc names.2 x)
        ∃ (K : Finset W) (base : W × W), K.card = 4 ∧
          (h = 1 → ∀ x ∈ K, reply base x = (fun _ => false, fun _ => false)) ∧
          ∀ x ∈ K, ∃ alt : W × W,
            (∀ y ∈ K.erase x, reply alt y = reply base y) ∧ reply alt x ≠ reply base x := by
  intro k h start hk h0 hhk W ix add mix step rot rc cc read reply
  have : NeZero k := ⟨by omega⟩
  have hreply : ∀ (n : W × W) (x : W), reply n x =
      (fun j : Fin h => Rd 1 1 0 rc n.1 x ((start + j.val : ℕ) : Fin k),
       fun j : Fin h => Rd 2 3 4 cc n.2 x ((start + j.val : ℕ) : Fin k)) := by
    intro n x
    simp only [reply, read, step, mix, add, rot, ix, ixN, castA, castS, Rd, St, Mx, Ad, Rt]
  have hk8 : 8 ≤ k := by omega
  set c : Fin k := ((start + h - 1 : ℕ) : Fin k) with hc
  have hP : ∀ j : Fin h, ((start + j.val : ℕ) : Fin k) = c - ((h - 1 - j.val : ℕ) : Fin k) := by
    intro j; rw [hc, ← Nat.cast_sub (by omega)]; congr 1; omega
  have hrow : ∀ s : ℕ, 2 ≤ s ∧ s ≤ 4 → (1 = 1 ∨ 3 ≤ s) → ∀ y : W, Mx 1 (Rt 1 y) c = true →
      (reply (dl (c + (s : Fin k)), fun _ => false) y = reply (fun _ => false, fun _ => false) y ↔
        Dl (Mx 1 (Rt 1 y) (c + ((1 : ℕ) : Fin k))) (Mx 1 (Rt 1 y) (c + ((2 : ℕ) : Fin k)))
          (Mx 1 (dl (c + (s : Fin k))) c) (Mx 1 (dl (c + (s : Fin k))) (c + ((1 : ℕ) : Fin k)))
          (Mx 1 (dl (c + (s : Fin k))) (c + ((2 : ℕ) : Fin k))) = false) := by
    intro s hs hgs y hy
    rw [hreply, hreply]
    simp only [Prod.mk.injEq, and_true]
    constructor
    · intro hf
      have := congrFun hf ⟨h - 1, by omega⟩
      rw [hP ⟨h - 1, by omega⟩, bankCmp c h hhk 1 1 0 s rc y (Or.inl rfl) hs hgs hy _ (by simp only; omega)] at this
      simp only [Nat.sub_self, ↓reduceIte] at this
      exact bxd _ _ this
    · intro hD
      funext j
      rw [hP j, bankCmp c h hhk 1 1 0 s rc y (Or.inl rfl) hs hgs hy _ (by omega)]
      split_ifs
      · rw [hD, Bool.xor_false]
      · rw [Bool.xor_false]
  have hcol : ∀ s : ℕ, 2 ≤ s ∧ s ≤ 4 → (2 = 1 ∨ 3 ≤ s) → ∀ y : W, Mx 2 (Rt 3 y) c = true →
      (reply (fun _ => false, dl (c + (s : Fin k))) y = reply (fun _ => false, fun _ => false) y ↔
        Dl (Mx 2 (Rt 3 y) (c + ((1 : ℕ) : Fin k))) (Mx 2 (Rt 3 y) (c + ((2 : ℕ) : Fin k)))
          (Mx 2 (dl (c + (s : Fin k))) c) (Mx 2 (dl (c + (s : Fin k))) (c + ((1 : ℕ) : Fin k)))
          (Mx 2 (dl (c + (s : Fin k))) (c + ((2 : ℕ) : Fin k))) = false) := by
    intro s hs hgs y hy
    rw [hreply, hreply]
    simp only [Prod.mk.injEq, true_and]
    constructor
    · intro hf
      have := congrFun hf ⟨h - 1, by omega⟩
      rw [hP ⟨h - 1, by omega⟩, bankCmp c h hhk 2 3 4 s cc y (Or.inr rfl) hs hgs hy _ (by simp only; omega)] at this
      simp only [Nat.sub_self, ↓reduceIte] at this
      exact bxd _ _ this
    · intro hD
      funext j
      rw [hP j, bankCmp c h hhk 2 3 4 s cc y (Or.inr rfl) hs hgs hy _ (by omega)]
      split_ifs
      · rw [hD, Bool.xor_false]
      · rw [Bool.xor_false]
  have E0 : ∀ g s : ℕ, g ≤ 2 → s ≤ 4 →
      Mx g (dl (c + (s : Fin k))) c = xor (xor (decide (0 = 0 + s + g)) (decide (0 = 0 + s)))
        (decide (0 + g = 0 + s)) ∧
      Mx g (dl (c + (s : Fin k))) (c + ((1 : ℕ) : Fin k)) = xor (xor (decide (1 = 0 + s + g))
        (decide (1 = 0 + s))) (decide (1 + g = 0 + s)) ∧
      Mx g (dl (c + (s : Fin k))) (c + ((2 : ℕ) : Fin k)) = xor (xor (decide (2 = 0 + s + g))
        (decide (2 = 0 + s))) (decide (2 + g = 0 + s)) := by
    intro g s hg hs
    exact ⟨Eval c g s 0 0 c (by simp) (by omega) (by omega),
      Eval c g s 0 1 _ (by simp) (by omega) (by omega),
      Eval c g s 0 2 _ (by simp) (by omega) (by omega)⟩
  obtain ⟨a1, a2, a3⟩ := E0 1 3 (by omega) (by omega)
  obtain ⟨b1, b2, b3⟩ := E0 1 2 (by omega) (by omega)
  obtain ⟨d1, d2, d3⟩ := E0 2 4 (by omega) (by omega)
  obtain ⟨e1, e2, e3⟩ := E0 2 3 (by omega) (by omega)
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ :=
    keyFacts c hk8 false false true false (rc c) (cc c) rc cc rfl rfl
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ :=
    keyFacts c hk8 true false true false (rc c) (cc c) rc cc rfl rfl
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ :=
    keyFacts c hk8 true true false false (rc c) (cc c) rc cc rfl rfl
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ :=
    keyFacts c hk8 true true true true (rc c) (cc c) rc cc rfl rfl
  set x1 := key c (kb false false true false (rc c) (cc c)) with hx1
  set x2 := key c (kb true false true false (rc c) (cc c)) with hx2
  set x3 := key c (kb true true false false (rc c) (cc c)) with hx3
  set x4 := key c (kb true true true true (rc c) (cc c)) with hx4
  have n12 : x1 ≠ x2 := fun e => by
    have := congrArg (fun x => Mx 1 (Rt 1 x) (c + ((1 : ℕ) : Fin k))) e
    simp only [p2, q2] at this; exact absurd this (by decide)
  have n13 : x1 ≠ x3 := fun e => by
    have := congrArg (fun x => Mx 1 (Rt 1 x) (c + ((1 : ℕ) : Fin k))) e
    simp only [p2, u2] at this; exact absurd this (by decide)
  have n14 : x1 ≠ x4 := fun e => by
    have := congrArg (fun x => Mx 1 (Rt 1 x) (c + ((1 : ℕ) : Fin k))) e
    simp only [p2, v2] at this; exact absurd this (by decide)
  have n23 : x2 ≠ x3 := fun e => by
    have := congrArg (fun x => Mx 1 (Rt 1 x) (c + ((2 : ℕ) : Fin k))) e
    simp only [q3, u3] at this; exact absurd this (by decide)
  have n24 : x2 ≠ x4 := fun e => by
    have := congrArg (fun x => Mx 1 (Rt 1 x) (c + ((2 : ℕ) : Fin k))) e
    simp only [q3, v3] at this; exact absurd this (by decide)
  have n34 : x3 ≠ x4 := fun e => by
    have := congrArg (fun x => Mx 2 (Rt 3 x) (c + ((1 : ℕ) : Fin k))) e
    simp only [u5, v5] at this; exact absurd this (by decide)
  have hbase : ∀ y : W, Rd 1 1 0 rc (fun _ => false) y c = false →
      Rd 2 3 4 cc (fun _ => false) y c = false → h = 1 →
      reply (fun _ => false, fun _ => false) y = (fun _ => false, fun _ => false) := by
    intro y hy1 hy2 h1
    rw [hreply]
    simp only [Prod.mk.injEq]
    constructor
    · funext j
      rw [hP j, show h - 1 - j.val = 0 by omega, Nat.cast_zero, sub_zero]; exact hy1
    · funext j
      rw [hP j, show h - 1 - j.val = 0 by omega, Nat.cast_zero, sub_zero]; exact hy2
  refine ⟨{x1, x2, x3, x4}, (fun _ => false, fun _ => false),
    Finset.card_eq_four.2 ⟨x1, x2, x3, x4, n12, n13, n14, n23, n24, n34, rfl⟩, ?_, ?_⟩
  · intro h1 x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hbase _ p7 p8 h1
    · exact hbase _ q7 q8 h1
    · exact hbase _ u7 u8 h1
    · exact hbase _ v7 v8 h1
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · refine ⟨(dl (c + ((3 : ℕ) : Fin k)), fun _ => false), ?_, ?_⟩
      · intro y hy
        rw [Finset.mem_erase] at hy
        obtain ⟨hne, hy⟩ := hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact absurd rfl hne
        · rw [hrow 3 (by omega) (by omega) _ q1, q2, q3, a1, a2, a3]; decide
        · rw [hrow 3 (by omega) (by omega) _ u1, u2, u3, a1, a2, a3]; decide
        · rw [hrow 3 (by omega) (by omega) _ v1, v2, v3, a1, a2, a3]; decide
      · rw [Ne, hrow 3 (by omega) (by omega) _ p1, p2, p3, a1, a2, a3]; decide
    · refine ⟨(dl (c + ((2 : ℕ) : Fin k)), fun _ => false), ?_, ?_⟩
      · intro y hy
        rw [Finset.mem_erase] at hy
        obtain ⟨hne, hy⟩ := hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · rw [hrow 2 (by omega) (by omega) _ p1, p2, p3, b1, b2, b3]; decide
        · exact absurd rfl hne
        · rw [hrow 2 (by omega) (by omega) _ u1, u2, u3, b1, b2, b3]; decide
        · rw [hrow 2 (by omega) (by omega) _ v1, v2, v3, b1, b2, b3]; decide
      · rw [Ne, hrow 2 (by omega) (by omega) _ q1, q2, q3, b1, b2, b3]; decide
    · refine ⟨(fun _ => false, dl (c + ((4 : ℕ) : Fin k))), ?_, ?_⟩
      · intro y hy
        rw [Finset.mem_erase] at hy
        obtain ⟨hne, hy⟩ := hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · rw [hcol 4 (by omega) (by omega) _ p4, p5, p6, d1, d2, d3]; decide
        · rw [hcol 4 (by omega) (by omega) _ q4, q5, q6, d1, d2, d3]; decide
        · exact absurd rfl hne
        · rw [hcol 4 (by omega) (by omega) _ v4, v5, v6, d1, d2, d3]; decide
      · rw [Ne, hcol 4 (by omega) (by omega) _ u4, u5, u6, d1, d2, d3]; decide
    · refine ⟨(fun _ => false, dl (c + ((3 : ℕ) : Fin k))), ?_, ?_⟩
      · intro y hy
        rw [Finset.mem_erase] at hy
        obtain ⟨hne, hy⟩ := hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · rw [hcol 3 (by omega) (by omega) _ p4, p5, p6, e1, e2, e3]; decide
        · rw [hcol 3 (by omega) (by omega) _ q4, q5, q6, e1, e2, e3]; decide
        · rw [hcol 3 (by omega) (by omega) _ u4, u5, u6, e1, e2, e3]; decide
        · exact absurd rfl hne
      · rw [Ne, hcol 3 (by omega) (by omega) _ v4, v5, v6, e1, e2, e3]; decide
