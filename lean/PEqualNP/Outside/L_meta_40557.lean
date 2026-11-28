import PEqualNP.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Outside.L_meta_40557_aux

def ix {k : Nat} (hk : 0 < k) (i : Nat) : Fin k :=
  ⟨i % k, Nat.mod_lt _ hk⟩

def rot {k : Nat} (hk : 0 < k) (a : Nat) (x : Fin k → Bool) (i : Fin k) : Bool :=
  x (ix hk (i.val + k - a % k))

def mix {k : Nat} (hk : 0 < k) (gap : Nat) (x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (x (ix hk (i.val + k - gap % k))) (xor (x i) (x (ix hk (i.val + gap))))

def chi {k : Nat} (hk : 0 < k) (x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (x i) (!(x (ix hk (i.val + 1))) && x (ix hk (i.val + 2)))

def row {k : Nat} (hk : 0 < k) (x : Fin k → Bool) (b : Bool) (i : Fin k) : Bool :=
  xor (chi hk (fun t => xor (mix hk 1 (rot hk 1 x) t) b) i) (x i)

def col {k : Nat} (hk : 0 < k) (x v : Fin k → Bool) (i : Fin k) : Bool :=
  xor (chi hk (fun t => xor (mix hk 2 v t) (mix hk 2 (rot hk 3 x) t)) i) (rot hk 4 x i)

def transcript {k : Nat} (hk : 0 < k) (q : Nat) (names : Fin q → Fin k → Bool)
    (sites : Fin q → Fin k) (x : Fin k → Bool) : (Bool → Fin k → Bool) × (Fin q → Bool) :=
  (row hk x, fun a : Fin q => col hk x (names a) (sites a))

def sigs (k : Nat) : Finset (Fin 3 → Bool) :=
  (Finset.univ : Finset (Fin 3 → Bool)).filter (fun s =>
    if 6 ∣ k then xor (s 0) (xor (s 1) (s 2)) = false else ∀ j, s j = false)

def survive {k : Nat} (hk : 0 < k) (q : Nat) (names : Fin q → Fin k → Bool)
    (sites : Fin q → Fin k) : Finset (Fin 3 → Bool) :=
  (sigs k).filter (fun s => ∀ a : Fin q,
    let j := (sites a).val
    s (⟨j % 3, Nat.mod_lt j (Nat.zero_lt_succ 2)⟩ : Fin 3) =
      xor (mix hk 2 (names a) (ix hk (j + 1))) (mix hk 2 (names a) (ix hk (j + 2))))

def wxor {k : Nat} (x y : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (x i) (y i)

def wzero {k : Nat} : Fin k → Bool :=
  fun _ => false

def ones {k : Nat} : Fin k → Bool :=
  fun _ => true

def m1 {k : Nat} (hk : 0 < k) (x : Fin k → Bool) : Fin k → Bool :=
  mix hk 1 (rot hk 1 x)

def pOf {k : Nat} (hk : 0 < k) (x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (m1 hk x (ix hk (i.val + 1))) (m1 hk x (ix hk (i.val + 2)))

def dOf {k : Nat} (hk : 0 < k) (x : Fin k → Bool) (i : Fin k) : Bool :=
  !(pOf hk x i)

def mate {k : Nat} (hk : 0 < k) (x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (x i) (dOf hk x i)

def rowAmbig {k : Nat} (hk : 0 < k) (x : Fin k → Bool) : Prop :=
  m1 hk (dOf hk x) = ones

instance instDecidableRowAmbig {k : Nat} (hk : 0 < k) (x : Fin k → Bool) :
    Decidable (rowAmbig hk x) :=
  inferInstanceAs (Decidable (m1 hk (dOf hk x) = ones))

def sigOf {k : Nat} (hk : 0 < k) (x : Fin k → Bool) : Fin 3 → Bool :=
  fun c => pOf hk x (ix hk (c.val + 2))

def packBits : (k : Nat) → (Fin k → Bool) → Nat
  | 0, _ => 0
  | k + 1, v => (v 0).toNat + 2 * packBits k (fun i => v i.succ)

lemma packBits_inj : ∀ {k : Nat} {v w : Fin k → Bool}, packBits k v = packBits k w → v = w
  | 0, _, _, _ => by
    funext i
    exact Fin.elim0 i
  | k + 1, v, w, h => by
    simp only [packBits] at h
    have hv0 : (v 0).toNat = (w 0).toNat := by
      cases hv : v 0 <;> cases hw : w 0 <;> simp [hv, hw] at h ⊢ <;> omega
    have h0 : v 0 = w 0 := by
      cases hv : v 0 <;> cases hw : w 0 <;> simp [hv, hw] at hv0 ⊢
    have hrest : packBits k (fun i => v i.succ) = packBits k (fun i => w i.succ) := by omega
    have ih := packBits_inj hrest
    funext i
    refine Fin.cases h0 (fun j => congrFun ih j) i

lemma xor_swap2 (a b c d : Bool) : xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma xor_cancel_right (a b x : Bool) : xor (xor a x) (xor b x) = xor a b := by
  cases a <;> cases b <;> cases x <;> rfl

lemma chi_comp_bool (a b c : Bool) :
    xor (xor a (!b && c)) (xor (xor a true) (!(xor b true) && xor c true)) =
      xor true (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma xor_eq_of_not_xor_eq {a1 a2 b1 b2 : Bool} (h : (!(xor a1 a2)) = (!(xor b1 b2))) :
    xor a1 b1 = xor a2 b2 := by
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp at h ⊢

lemma eq_of_xor_eq_left {c x y : Bool} (h : xor c x = xor c y) : x = y := by
  cases c <;> cases x <;> cases y <;> simp at h ⊢

lemma eq_xor_of_xor_eq {c1 c2 x y d : Bool}
    (h1 : xor c1 x = xor c2 y) (h2 : xor (xor c1 x) (xor c2 x) = d) :
    y = xor x d := by
  cases c1 <;> cases c2 <;> cases x <;> cases y <;> cases d <;> simp at h1 h2 ⊢

lemma xor_c2_mate {c1 c2 x d : Bool} (h : xor (xor c1 x) (xor c2 x) = d) :
    xor c1 x = xor c2 (xor x d) := by
  cases c1 <;> cases c2 <;> cases x <;> cases d <;> simp at h ⊢

lemma xor_c1_mate {c1 c2 x d : Bool} (h : xor (xor c1 x) (xor c2 x) = d) :
    xor c2 x = xor c1 (xor x d) := by
  cases c1 <;> cases c2 <;> cases x <;> cases d <;> simp at h ⊢

lemma eq_of_not_eq {a b : Bool} (h : (!a) = (!b)) : a = b := by
  cases a <;> cases b <;> simp at h ⊢

lemma xor_not_triple_iff (a b c : Bool) :
    xor (!a) (xor (!b) (!c)) = true ↔ xor a (xor b c) = false := by
  cases a <;> cases b <;> cases c <;> decide

lemma eq_of_triple_xor {a b c d : Bool}
    (h1 : xor a (xor b c) = false) (h2 : xor b (xor c d) = false) : d = a := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp at h1 h2 ⊢

lemma xor_triple_cancel (a b c d e : Bool) :
    xor a (xor c e) =
      xor (xor a (xor b c)) (xor (xor b (xor c d)) (xor c (xor d e))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

lemma xor_telescope4 {a b c d : Bool}
    (h : xor (xor a b) (xor (xor b c) (xor c d)) = false) :
    xor (xor a (xor b c)) (xor b (xor c d)) = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp at h ⊢

lemma eq_of_adj_triple_xor {a b c d : Bool}
    (h : xor (xor a b) (xor (xor b c) (xor c d)) = false) : d = a := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp at h ⊢

lemma xor_true_not (s v : Bool) : xor (xor true (xor v false)) (!s) = xor s v := by
  cases s <;> cases v <;> rfl

lemma ne_iff_ne_of_xor_eq {a b c d : Bool} (h : xor a b = xor c d) : a ≠ b ↔ c ≠ d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp at h ⊢

lemma eq_of_xor_comm_eq {x a b : Bool} (h : xor a x = xor x b) : b = a := by
  cases x <;> cases a <;> cases b <;> simp at h ⊢

lemma xor_solve_right {a b c : Bool} (h : c = xor a b) : b = xor a c := by
  cases a <;> cases b <;> cases c <;> simp at h ⊢

lemma xor_solve_left {a b c : Bool} (h : c = xor b a) : b = xor a c := by
  cases a <;> cases b <;> cases c <;> simp at h ⊢

lemma ix_self {k : Nat} (hk : 0 < k) (i : Fin k) : ix hk i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

lemma ix_add_k {k : Nat} (hk : 0 < k) (a : Nat) : ix hk (a + k) = ix hk a := by
  apply Fin.ext
  exact Nat.add_mod_right a k

lemma ix_add_mul_k {k : Nat} (hk : 0 < k) (a m : Nat) : ix hk (a + m * k) = ix hk a := by
  apply Fin.ext
  exact Nat.add_mul_mod_self_right a m k

lemma ix_add_mod {k : Nat} (hk : 0 < k) (a b : Nat) :
    ix hk ((ix hk a).val + b) = ix hk (a + b) := by
  apply Fin.ext
  change (a % k + b) % k = (a + b) % k
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma ix_sub {k : Nat} (hk : 0 < k) (a b : Nat) (hb : b ≤ k) :
    ix hk ((ix hk a).val + k - b) = ix hk (a + (k - b)) := by
  apply Fin.ext
  have h1 : (ix hk a).val + k - b = a % k + (k - b) := by
    change a % k + k - b = a % k + (k - b)
    omega
  change ((ix hk a).val + k - b) % k = (a + (k - b)) % k
  rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma ix_sub_add_cancel {k : Nat} (hk : 0 < k) (a b : Nat) (hb : b ≤ k) :
    ix hk (a + b + (k - b)) = ix hk a := by
  have h1 : a + b + (k - b) = a + k := by omega
  rw [h1]
  exact ix_add_k hk a

lemma rot_at_add {k : Nat} (hk : 0 < k) (a : Nat) (ha : a < k) (x : Fin k → Bool) (t : Nat) :
    rot hk a x (ix hk (t + a)) = x (ix hk t) := by
  unfold rot
  rw [Nat.mod_eq_of_lt ha]
  rw [ix_sub hk (t + a) a (by omega)]
  rw [ix_sub_add_cancel hk t a (by omega)]

lemma m1_at_add2 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (x : Fin k → Bool) (t : Nat) :
    m1 hk x (ix hk (t + 2)) = xor (x (ix hk t)) (xor (x (ix hk (t + 1))) (x (ix hk (t + 2)))) := by
  unfold m1 mix
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have ha : ix hk ((ix hk (t + 2)).val + k - 1) = ix hk (t + 1) := by
    rw [ix_sub hk (t + 2) 1 (by omega)]
    have h2 : t + 2 + (k - 1) = t + 1 + k := by omega
    rw [h2, ix_add_k hk]
  have hb : ix hk ((ix hk (t + 2)).val + 1) = ix hk (t + 3) := ix_add_mod hk (t + 2) 1
  rw [ha, hb]
  have r0 : rot hk 1 x (ix hk (t + 1)) = x (ix hk t) := rot_at_add hk 1 (by omega) x t
  have r1 : rot hk 1 x (ix hk (t + 2)) = x (ix hk (t + 1)) := rot_at_add hk 1 (by omega) x (t + 1)
  have r2 : rot hk 1 x (ix hk (t + 3)) = x (ix hk (t + 2)) := rot_at_add hk 1 (by omega) x (t + 2)
  rw [r0, r1, r2]

lemma m2r3_at_add5 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (x : Fin k → Bool) (t : Nat) :
    mix hk 2 (rot hk 3 x) (ix hk (t + 5)) =
      xor (x (ix hk t)) (xor (x (ix hk (t + 2))) (x (ix hk (t + 4)))) := by
  unfold mix
  have h2 : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
  rw [h2]
  have ha : ix hk ((ix hk (t + 5)).val + k - 2) = ix hk (t + 3) := by
    rw [ix_sub hk (t + 5) 2 (by omega)]
    have h3 : t + 5 + (k - 2) = t + 3 + k := by omega
    rw [h3, ix_add_k hk]
  have hb : ix hk ((ix hk (t + 5)).val + 2) = ix hk (t + 7) := ix_add_mod hk (t + 5) 2
  rw [ha, hb]
  have r0 : rot hk 3 x (ix hk (t + 3)) = x (ix hk t) := rot_at_add hk 3 (by omega) x t
  have r1 : rot hk 3 x (ix hk (t + 5)) = x (ix hk (t + 2)) := rot_at_add hk 3 (by omega) x (t + 2)
  have r2 : rot hk 3 x (ix hk (t + 7)) = x (ix hk (t + 4)) := rot_at_add hk 3 (by omega) x (t + 4)
  rw [r0, r1, r2]

lemma wxor_assoc {k : Nat} (x y z : Fin k → Bool) : wxor (wxor x y) z = wxor x (wxor y z) := by
  funext i
  exact Bool.xor_assoc (x i) (y i) (z i)

lemma wxor_comm {k : Nat} (x y : Fin k → Bool) : wxor x y = wxor y x := by
  funext i
  exact Bool.xor_comm (x i) (y i)

lemma wxor_self {k : Nat} (x : Fin k → Bool) : wxor x x = wzero := by
  funext i
  exact Bool.xor_self (x i)

lemma wxor_wzero {k : Nat} (x : Fin k → Bool) : wxor x wzero = x := by
  funext i
  exact Bool.xor_false (x i)

lemma wzero_wxor {k : Nat} (x : Fin k → Bool) : wxor wzero x = x := by
  funext i
  exact Bool.false_xor (x i)

lemma wxor_cancel_left {k : Nat} {x y z : Fin k → Bool} (h : wxor x y = wxor x z) : y = z := by
  have h2 : wxor x (wxor x y) = wxor x (wxor x z) := congrArg (wxor x) h
  rw [← wxor_assoc, ← wxor_assoc, wxor_self, wzero_wxor, wzero_wxor] at h2
  exact h2

lemma rot_wxor {k : Nat} (hk : 0 < k) (a : Nat) (x y : Fin k → Bool) :
    rot hk a (wxor x y) = wxor (rot hk a x) (rot hk a y) := rfl

lemma mix_wxor {k : Nat} (hk : 0 < k) (g : Nat) (x y : Fin k → Bool) :
    mix hk g (wxor x y) = wxor (mix hk g x) (mix hk g y) := by
  funext i
  unfold mix wxor
  rw [xor_swap2 (x i) (y i) (x (ix hk (i.val + g))) (y (ix hk (i.val + g))), xor_swap2]

lemma m1_wxor {k : Nat} (hk : 0 < k) (x y : Fin k → Bool) :
    m1 hk (wxor x y) = wxor (m1 hk x) (m1 hk y) := by
  unfold m1
  rw [rot_wxor, mix_wxor]

lemma m2r3_wxor {k : Nat} (hk : 0 < k) (x y : Fin k → Bool) :
    mix hk 2 (rot hk 3 (wxor x y)) = wxor (mix hk 2 (rot hk 3 x)) (mix hk 2 (rot hk 3 y)) := by
  rw [rot_wxor, mix_wxor]

lemma rot_ones {k : Nat} (hk : 0 < k) (a : Nat) : rot hk a ones = ones := rfl

lemma mix_ones {k : Nat} (hk : 0 < k) (g : Nat) : mix hk g ones = ones := rfl

lemma m1_ones {k : Nat} (hk : 0 < k) : m1 hk ones = ones := rfl

lemma rot_wzero {k : Nat} (hk : 0 < k) (a : Nat) : rot hk a wzero = wzero := rfl

lemma mix_wzero {k : Nat} (hk : 0 < k) (g : Nat) : mix hk g wzero = wzero := rfl

lemma m1_wzero {k : Nat} (hk : 0 < k) : m1 hk wzero = wzero := rfl

lemma chi_wxor_ones {k : Nat} (hk : 0 < k) (z : Fin k → Bool) (i : Fin k) :
    xor (chi hk z i) (chi hk (wxor z ones) i) =
      xor true (xor (z (ix hk (i.val + 1))) (z (ix hk (i.val + 2)))) :=
  chi_comp_bool (z i) (z (ix hk (i.val + 1))) (z (ix hk (i.val + 2)))

lemma row_false_eq {k : Nat} (hk : 0 < k) (x : Fin k → Bool) (i : Fin k) :
    row hk x false i = xor (chi hk (m1 hk x) i) (x i) := by
  unfold row m1
  have hf : (fun t => xor (mix hk 1 (rot hk 1 x) t) false) = mix hk 1 (rot hk 1 x) := by
    funext t
    exact Bool.xor_false _
  rw [hf]

lemma row_true_eq {k : Nat} (hk : 0 < k) (x : Fin k → Bool) (i : Fin k) :
    row hk x true i = xor (chi hk (wxor (m1 hk x) ones) i) (x i) := rfl

lemma row_xor_false_true {k : Nat} (hk : 0 < k) (x : Fin k → Bool) (i : Fin k) :
    xor (row hk x false i) (row hk x true i) = dOf hk x i := by
  rw [row_false_eq, row_true_eq, xor_cancel_right, chi_wxor_ones]
  exact Bool.true_xor _

lemma wxor_mate {k : Nat} (hk : 0 < k) (x : Fin k → Bool) :
    wxor x (mate hk x) = dOf hk x := by
  funext i
  unfold wxor mate
  rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

lemma const_of_adj_eq {k : Nat} (hk : 0 < k) (f : Fin k → Bool)
    (h : ∀ i : Fin k, f (ix hk (i.val + 1)) = f (ix hk (i.val + 2))) :
    ∀ i : Fin k, f i = f ⟨0, hk⟩ := by
  have hstep : ∀ t : Nat, f (ix hk t) = f (ix hk (t + 1)) := by
    intro t
    have h1 := h (ix hk (t + k - 1))
    have ha : ix hk ((ix hk (t + k - 1)).val + 1) = ix hk t := by
      rw [ix_add_mod hk (t + k - 1) 1]
      have h2 : t + k - 1 + 1 = t + k := by omega
      rw [h2, ix_add_k hk]
    have hb : ix hk ((ix hk (t + k - 1)).val + 2) = ix hk (t + 1) := by
      rw [ix_add_mod hk (t + k - 1) 2]
      have h2 : t + k - 1 + 2 = t + 1 + k := by omega
      rw [h2, ix_add_k hk]
    rw [ha, hb] at h1
    exact h1
  have hind : ∀ n : Nat, f (ix hk n) = f (ix hk 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih => rw [← hstep m, ih]
  intro i
  have h0 : ix hk 0 = ⟨0, hk⟩ := Fin.ext (Nat.zero_mod k)
  rw [← ix_self hk i, hind i.val, h0]

lemma m1_eq_wzero_or_ones_of_row_eq {k : Nat} (hk : 0 < k) {x y : Fin k → Bool}
    (hrow : row hk x = row hk y) :
    m1 hk (wxor x y) = wzero ∨ m1 hk (wxor x y) = ones := by
  have hd : dOf hk x = dOf hk y := by
    funext i
    rw [← row_xor_false_true hk x i, ← row_xor_false_true hk y i, hrow]
  have hadj : ∀ i : Fin k,
      m1 hk (wxor x y) (ix hk (i.val + 1)) = m1 hk (wxor x y) (ix hk (i.val + 2)) := by
    intro i
    rw [m1_wxor hk x y]
    exact xor_eq_of_not_xor_eq (congrFun hd i)
  have hconst := const_of_adj_eq hk (m1 hk (wxor x y)) hadj
  cases h0 : m1 hk (wxor x y) ⟨0, hk⟩
  · left
    funext i
    rw [hconst i, h0]
    rfl
  · right
    funext i
    rw [hconst i, h0]
    rfl

lemma row_collision_iff {k : Nat} (hk : 0 < k) (x y : Fin k → Bool) :
    (x ≠ y ∧ row hk x = row hk y) ↔ (rowAmbig hk x ∧ y = mate hk x) := by
  constructor
  · rintro ⟨hne, hrow⟩
    rcases m1_eq_wzero_or_ones_of_row_eq hk hrow with hz | ho
    · exfalso
      apply hne
      have hm : m1 hk x = m1 hk y := by
        have h1 : wxor (m1 hk x) (m1 hk y) = wzero := by rw [← m1_wxor, hz]
        have h2 : wxor (m1 hk x) (m1 hk y) = wxor (m1 hk x) (m1 hk x) := by
          rw [h1, wxor_self]
        exact (wxor_cancel_left h2).symm
      funext i
      have hf := congrFun (congrFun hrow false) i
      rw [row_false_eq, row_false_eq, hm] at hf
      exact eq_of_xor_eq_left hf
    · have hm : m1 hk y = wxor (m1 hk x) ones := by
        have h1 : wxor (m1 hk x) (m1 hk y) = ones := by rw [← m1_wxor, ho]
        have h2 : wxor (m1 hk x) (m1 hk y) = wxor (m1 hk x) (wxor (m1 hk x) ones) := by
          rw [h1, ← wxor_assoc, wxor_self, wzero_wxor]
        exact wxor_cancel_left h2
      have hy : y = mate hk x := by
        funext i
        have hf := congrFun (congrFun hrow false) i
        rw [row_false_eq, row_false_eq, hm] at hf
        have hft := row_xor_false_true hk x i
        rw [row_false_eq, row_true_eq] at hft
        exact eq_xor_of_xor_eq hf hft
      refine ⟨?_, hy⟩
      unfold rowAmbig
      rw [← wxor_mate hk x, ← hy]
      exact ho
  · rintro ⟨hamb, rfl⟩
    have hne : x ≠ mate hk x := by
      intro heq
      have h1 : dOf hk x = wzero := by
        rw [← wxor_mate hk x, ← heq, wxor_self]
      unfold rowAmbig at hamb
      rw [h1, m1_wzero] at hamb
      exact Bool.false_ne_true (congrFun hamb ⟨0, hk⟩)
    refine ⟨hne, ?_⟩
    have hm : m1 hk (mate hk x) = wxor (m1 hk x) ones := by
      have h1 : mate hk x = wxor x (dOf hk x) := rfl
      rw [h1, m1_wxor, hamb]
    have hm1 : wxor (m1 hk (mate hk x)) ones = m1 hk x := by
      rw [hm, wxor_assoc, wxor_self, wxor_wzero]
    funext b i
    cases b
    · rw [row_false_eq, row_false_eq, hm]
      have hft := row_xor_false_true hk x i
      rw [row_false_eq, row_true_eq] at hft
      exact xor_c2_mate hft
    · rw [row_true_eq, row_true_eq, hm1]
      have hft := row_xor_false_true hk x i
      rw [row_false_eq, row_true_eq] at hft
      exact xor_c1_mate hft

lemma row_mate {k : Nat} (hk : 0 < k) {x : Fin k → Bool} (h : rowAmbig hk x) :
    row hk x = row hk (mate hk x) :=
  ((row_collision_iff hk x (mate hk x)).mpr ⟨h, rfl⟩).2

lemma mate_ne_self {k : Nat} (hk : 0 < k) {x : Fin k → Bool} (h : rowAmbig hk x) :
    mate hk x ≠ x :=
  (((row_collision_iff hk x (mate hk x)).mpr ⟨h, rfl⟩).1).symm

lemma rowAmbig_mate_and_inv {k : Nat} (hk : 0 < k) {x : Fin k → Bool} (h : rowAmbig hk x) :
    rowAmbig hk (mate hk x) ∧ mate hk (mate hk x) = x := by
  have hcol := (row_collision_iff hk x (mate hk x)).mpr ⟨h, rfl⟩
  have hcol' := (row_collision_iff hk (mate hk x) x).mp ⟨hcol.1.symm, hcol.2.symm⟩
  exact ⟨hcol'.1, hcol'.2.symm⟩

lemma pOf_mate {k : Nat} (hk : 0 < k) {x : Fin k → Bool} (h : rowAmbig hk x) :
    pOf hk (mate hk x) = pOf hk x := by
  have hrow := row_mate hk h
  have hd : dOf hk (mate hk x) = dOf hk x := by
    funext i
    rw [← row_xor_false_true hk (mate hk x) i, ← row_xor_false_true hk x i, hrow]
  funext i
  exact eq_of_not_eq (congrFun hd i)

lemma sigOf_mate {k : Nat} (hk : 0 < k) {x : Fin k → Bool} (h : rowAmbig hk x) :
    sigOf hk (mate hk x) = sigOf hk x := by
  funext c
  unfold sigOf
  rw [pOf_mate hk h]

lemma rowAmbig_iff_pOf_triple {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (x : Fin k → Bool) :
    rowAmbig hk x ↔
      ∀ t : Nat, xor (pOf hk x (ix hk t))
        (xor (pOf hk x (ix hk (t + 1))) (pOf hk x (ix hk (t + 2)))) = false := by
  constructor
  · intro hamb t
    have h1 := congrFun hamb (ix hk (t + 2))
    rw [m1_at_add2 hk hk7 (dOf hk x) t] at h1
    exact (xor_not_triple_iff _ _ _).mp h1
  · intro htr
    funext i
    have hi : i = ix hk ((i.val + k - 2) + 2) := by
      have h2 : i.val + k - 2 + 2 = i.val + k := by omega
      rw [h2, ix_add_k hk, ix_self hk i]
    rw [hi, m1_at_add2 hk hk7 (dOf hk x) (i.val + k - 2)]
    exact (xor_not_triple_iff _ _ _).mpr (htr (i.val + k - 2))

lemma periodic3_of_triple {k : Nat} (hk : 0 < k) (f : Fin k → Bool)
    (htr : ∀ t : Nat, xor (f (ix hk t)) (xor (f (ix hk (t + 1))) (f (ix hk (t + 2)))) = false) :
    ∀ t : Nat, f (ix hk (t + 3)) = f (ix hk t) := by
  intro t
  exact eq_of_triple_xor (htr t) (htr (t + 1))

lemma periodic3_mul {k : Nat} (hk : 0 < k) (f : Fin k → Bool)
    (hp : ∀ t : Nat, f (ix hk (t + 3)) = f (ix hk t)) :
    ∀ t n : Nat, f (ix hk (t + 3 * n)) = f (ix hk t) := by
  intro t n
  induction n with
  | zero => simp
  | succ m ih =>
    have h1 : t + 3 * (m + 1) = (t + 3 * m) + 3 := by omega
    rw [h1, hp, ih]

lemma periodic3_mod3 {k : Nat} (hk : 0 < k) (f : Fin k → Bool)
    (hp : ∀ t : Nat, f (ix hk (t + 3)) = f (ix hk t)) :
    ∀ t : Nat, f (ix hk t) = f (ix hk (t % 3)) := by
  intro t
  have hdiv : t = t % 3 + 3 * (t / 3) := by omega
  conv_lhs => rw [hdiv]
  exact periodic3_mul hk f hp (t % 3) (t / 3)

lemma zero_of_triple_not_dvd3 {k : Nat} (hk : 0 < k) (hnd : ¬ (3 ∣ k)) (f : Fin k → Bool)
    (htr : ∀ t : Nat, xor (f (ix hk t)) (xor (f (ix hk (t + 1))) (f (ix hk (t + 2)))) = false) :
    f = wzero := by
  have hp := periodic3_of_triple hk f htr
  have hstep : ∀ t : Nat, f (ix hk (t + 1)) = f (ix hk t) := by
    intro t
    have hm : k % 3 = 1 ∨ k % 3 = 2 := by
      have h0 : k % 3 ≠ 0 := by
        intro hz
        exact hnd (Nat.dvd_of_mod_eq_zero hz)
      omega
    rcases hm with h1 | h2
    · have hmul : 3 * (2 * (k / 3) + 1) = 2 * k + 1 := by omega
      have h3 := periodic3_mul hk f hp t (2 * (k / 3) + 1)
      rw [hmul] at h3
      have h4 : t + (2 * k + 1) = (t + 1) + 2 * k := by omega
      rw [h4, ix_add_mul_k hk (t + 1) 2] at h3
      exact h3
    · have hmul : 3 * (k / 3 + 1) = k + 1 := by omega
      have h3 := periodic3_mul hk f hp t (k / 3 + 1)
      rw [hmul] at h3
      have h4 : t + (k + 1) = (t + 1) + k := by omega
      rw [h4, ix_add_k hk (t + 1)] at h3
      exact h3
  have hind : ∀ n : Nat, f (ix hk n) = f (ix hk 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih => rw [hstep m, ih]
  have h0 : f (ix hk 0) = false := by
    have ht0 := htr 0
    rw [hind 1, hind 2] at ht0
    cases hf : f (ix hk 0) <;> simp [hf] at ht0 ⊢
  funext i
  rw [← ix_self hk i, hind i.val, h0]
  rfl

lemma pOf_shift4 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) {x : Fin k → Bool}
    (hamb : rowAmbig hk x) (j : Fin k) :
    pOf hk x (ix hk (j.val + k - 4)) =
      sigOf hk x ⟨j.val % 3, Nat.mod_lt j.val (Nat.zero_lt_succ 2)⟩ := by
  have htr := (rowAmbig_iff_pOf_triple hk hk7 x).mp hamb
  by_cases h3 : 3 ∣ k
  · have hp := periodic3_of_triple hk (pOf hk x) htr
    rw [periodic3_mod3 hk (pOf hk x) hp (j.val + k - 4)]
    unfold sigOf
    rw [periodic3_mod3 hk (pOf hk x) hp (j.val % 3 + 2)]
    rcases h3 with ⟨r, hr⟩
    have hmod : (j.val + k - 4) % 3 = (j.val % 3 + 2) % 3 := by omega
    rw [hmod]
  · have hz := zero_of_triple_not_dvd3 hk h3 (pOf hk x) htr
    unfold sigOf
    rw [hz]
    rfl

lemma m2r3_eq_m1_triple {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (x : Fin k → Bool) (t : Nat) :
    mix hk 2 (rot hk 3 x) (ix hk (t + 5)) =
      xor (m1 hk x (ix hk (t + 2)))
        (xor (m1 hk x (ix hk (t + 3))) (m1 hk x (ix hk (t + 4)))) := by
  rw [m2r3_at_add5 hk hk7 x t]
  rw [m1_at_add2 hk hk7 x t, m1_at_add2 hk hk7 x (t + 1), m1_at_add2 hk hk7 x (t + 2)]
  exact xor_triple_cancel _ _ _ _ _

lemma m2r3_dOf_eq_ones {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) {x : Fin k → Bool}
    (hamb : rowAmbig hk x) :
    mix hk 2 (rot hk 3 (dOf hk x)) = ones := by
  funext i
  have hi : i = ix hk ((i.val + k - 5) + 5) := by
    have h1 : i.val + k - 5 + 5 = i.val + k := by omega
    rw [h1, ix_add_k hk, ix_self hk i]
  rw [hi, m2r3_eq_m1_triple hk hk7 (dOf hk x) (i.val + k - 5)]
  rw [hamb]
  rfl

lemma m2r3_adj_xor_false {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) {x : Fin k → Bool}
    (hamb : rowAmbig hk x) (j : Fin k) :
    xor (mix hk 2 (rot hk 3 x) (ix hk (j.val + 1)))
        (mix hk 2 (rot hk 3 x) (ix hk (j.val + 2))) = false := by
  let t := j.val + k - 4
  have hj1 : ix hk (j.val + 1) = ix hk (t + 5) := by
    have h1 : t + 5 = j.val + 1 + k := by omega
    rw [h1, ix_add_k hk]
  have hj2 : ix hk (j.val + 2) = ix hk ((t + 1) + 5) := by
    have h1 : t + 1 + 5 = j.val + 2 + k := by omega
    rw [h1, ix_add_k hk]
  rw [hj1, hj2, m2r3_eq_m1_triple hk hk7 x t, m2r3_eq_m1_triple hk hk7 x (t + 1)]
  have htr := (rowAmbig_iff_pOf_triple hk hk7 x).mp hamb (t + 1)
  have hp1 : pOf hk x (ix hk (t + 1)) = xor (m1 hk x (ix hk (t + 2))) (m1 hk x (ix hk (t + 3))) := by
    unfold pOf
    rw [ix_add_mod hk (t + 1) 1, ix_add_mod hk (t + 1) 2]
  have hp2 : pOf hk x (ix hk (t + 2)) = xor (m1 hk x (ix hk (t + 3))) (m1 hk x (ix hk (t + 4))) := by
    unfold pOf
    rw [ix_add_mod hk (t + 2) 1, ix_add_mod hk (t + 2) 2]
  have hp3 : pOf hk x (ix hk (t + 3)) = xor (m1 hk x (ix hk (t + 4))) (m1 hk x (ix hk (t + 5))) := by
    unfold pOf
    rw [ix_add_mod hk (t + 3) 1, ix_add_mod hk (t + 3) 2]
  rw [hp1, hp2, hp3] at htr
  exact xor_telescope4 htr

lemma col_xor_mate {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) {x : Fin k → Bool}
    (hamb : rowAmbig hk x) (v : Fin k → Bool) (j : Fin k) :
    xor (col hk x v j) (col hk (mate hk x) v j) =
      xor (sigOf hk x ⟨j.val % 3, Nat.mod_lt j.val (Nat.zero_lt_succ 2)⟩)
        (xor (mix hk 2 v (ix hk (j.val + 1))) (mix hk 2 v (ix hk (j.val + 2)))) := by
  let z : Fin k → Bool := fun t => xor (mix hk 2 v t) (mix hk 2 (rot hk 3 x) t)
  have hz_mate : (fun t => xor (mix hk 2 v t) (mix hk 2 (rot hk 3 (mate hk x)) t)) =
      wxor z ones := by
    funext t
    have hm : mate hk x = wxor x (dOf hk x) := rfl
    rw [hm, m2r3_wxor hk x (dOf hk x), m2r3_dOf_eq_ones hk hk7 hamb]
    exact (Bool.xor_assoc _ _ _).symm
  have hcol1 : col hk x v j = xor (chi hk z j) (rot hk 4 x j) := rfl
  have hcol2 : col hk (mate hk x) v j = xor (chi hk (wxor z ones) j) (rot hk 4 (mate hk x) j) := by
    unfold col
    rw [hz_mate]
  have hrot : xor (rot hk 4 x j) (rot hk 4 (mate hk x) j) =
      !(sigOf hk x ⟨j.val % 3, Nat.mod_lt j.val (Nat.zero_lt_succ 2)⟩) := by
    have h4 : 4 % k = 4 := Nat.mod_eq_of_lt (by omega)
    unfold rot mate
    rw [h4, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
    unfold dOf
    rw [pOf_shift4 hk hk7 hamb j]
  rw [hcol1, hcol2, xor_swap2, chi_wxor_ones hk z j, hrot]
  change xor (xor true (xor (xor (mix hk 2 v (ix hk (j.val + 1)))
      (mix hk 2 (rot hk 3 x) (ix hk (j.val + 1))))
      (xor (mix hk 2 v (ix hk (j.val + 2)))
      (mix hk 2 (rot hk 3 x) (ix hk (j.val + 2)))))) _ = _
  rw [xor_swap2, m2r3_adj_xor_false hk hk7 hamb j, xor_true_not]

lemma col_ne_mate_iff {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) {x : Fin k → Bool}
    (hamb : rowAmbig hk x) (v : Fin k → Bool) (j : Fin k) :
    col hk x v j ≠ col hk (mate hk x) v j ↔
      sigOf hk x ⟨j.val % 3, Nat.mod_lt j.val (Nat.zero_lt_succ 2)⟩ ≠
        xor (mix hk 2 v (ix hk (j.val + 1))) (mix hk 2 v (ix hk (j.val + 2))) :=
  ne_iff_ne_of_xor_eq (col_xor_mate hk hk7 hamb v j)

def blockXor {k : Nat} (hk : 0 < k) (f : Fin k → Bool) (c : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => xor (blockXor hk f c n) (f (ix hk (3 * n + c)))

def totalXor {k : Nat} (hk : 0 < k) (x : Fin k → Bool) (c : Nat) : Nat → Bool
  | 0 => false
  | m + 1 => xor (totalXor hk x c m) (x (ix hk (c + m)))

lemma blockXor_periodic3 {k : Nat} (hk : 0 < k) (u : Fin k → Bool)
    (hp : ∀ t : Nat, u (ix hk (t + 3)) = u (ix hk t)) (c n : Nat) :
    blockXor hk u c n = if n % 2 = 0 then false else u (ix hk c) := by
  induction n with
  | zero => simp [blockXor]
  | succ m ih =>
    simp only [blockXor, ih]
    have hu : u (ix hk (3 * m + c)) = u (ix hk c) := by
      have h1 : 3 * m + c = c + 3 * m := by omega
      rw [h1]
      exact periodic3_mul hk u hp c m
    rw [hu]
    by_cases hm : m % 2 = 0
    · have hm1 : (m + 1) % 2 ≠ 0 := by omega
      simp [hm, hm1]
    · have hm1 : (m + 1) % 2 = 0 := by omega
      simp [hm, hm1]

lemma blockXor_m1 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (x : Fin k → Bool) (c n : Nat) :
    blockXor hk (m1 hk x) (c + 2) n = totalXor hk x c (3 * n) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have h3 : 3 * (m + 1) = (3 * m + 2) + 1 := by omega
    simp only [blockXor, ih]
    rw [h3]
    simp only [totalXor]
    have hidx : 3 * m + (c + 2) = (c + 3 * m) + 2 := by omega
    rw [hidx, m1_at_add2 hk hk7 x (c + 3 * m)]
    have ha : c + (3 * m + 1) = c + 3 * m + 1 := by omega
    have hb : c + (3 * m + 2) = c + 3 * m + 2 := by omega
    rw [ha, hb]
    rw [Bool.xor_assoc, Bool.xor_assoc]

lemma totalXor_succ_shift {k : Nat} (hk : 0 < k) (x : Fin k → Bool) (c m : Nat) :
    totalXor hk x c (m + 1) = xor (x (ix hk c)) (totalXor hk x (c + 1) m) := by
  induction m with
  | zero =>
    simp only [totalXor, Nat.add_zero]
    rw [Bool.false_xor, Bool.xor_false]
  | succ n ih =>
    change xor (totalXor hk x c (n + 1)) (x (ix hk (c + (n + 1)))) =
      xor (x (ix hk c)) (xor (totalXor hk x (c + 1) n) (x (ix hk (c + 1 + n))))
    have h1 : c + (n + 1) = c + 1 + n := by omega
    rw [ih, h1, Bool.xor_assoc]

lemma totalXor_shift_k {k : Nat} (hk : 0 < k) (x : Fin k → Bool) (c : Nat) :
    totalXor hk x (c + 1) k = totalXor hk x c k := by
  have h1 := totalXor_succ_shift hk x c k
  have h2 : totalXor hk x c (k + 1) = xor (totalXor hk x c k) (x (ix hk (c + k))) := rfl
  rw [ix_add_k hk c] at h2
  rw [h2] at h1
  exact eq_of_xor_comm_eq h1

lemma m1_periodic3_of_rowAmbig {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) {x : Fin k → Bool}
    (hamb : rowAmbig hk x) :
    ∀ t : Nat, m1 hk x (ix hk (t + 3)) = m1 hk x (ix hk t) := by
  have htr := (rowAmbig_iff_pOf_triple hk hk7 x).mp hamb
  intro t
  have h0 := htr (t + k - 1)
  have h1 : pOf hk x (ix hk (t + k - 1)) =
      xor (m1 hk x (ix hk t)) (m1 hk x (ix hk (t + 1))) := by
    unfold pOf
    rw [ix_add_mod hk (t + k - 1) 1, ix_add_mod hk (t + k - 1) 2]
    have ha : t + k - 1 + 1 = t + k := by omega
    have hb : t + k - 1 + 2 = t + 1 + k := by omega
    rw [ha, hb, ix_add_k hk, ix_add_k hk]
  have h2 : pOf hk x (ix hk (t + k - 1 + 1)) =
      xor (m1 hk x (ix hk (t + 1))) (m1 hk x (ix hk (t + 2))) := by
    unfold pOf
    rw [ix_add_mod hk (t + k - 1 + 1) 1, ix_add_mod hk (t + k - 1 + 1) 2]
    have ha : t + k - 1 + 1 + 1 = t + 1 + k := by omega
    have hb : t + k - 1 + 1 + 2 = t + 2 + k := by omega
    rw [ha, hb, ix_add_k hk, ix_add_k hk]
  have h3 : pOf hk x (ix hk (t + k - 1 + 2)) =
      xor (m1 hk x (ix hk (t + 2))) (m1 hk x (ix hk (t + 3))) := by
    unfold pOf
    rw [ix_add_mod hk (t + k - 1 + 2) 1, ix_add_mod hk (t + k - 1 + 2) 2]
    have ha : t + k - 1 + 2 + 1 = t + 2 + k := by omega
    have hb : t + k - 1 + 2 + 2 = t + 3 + k := by omega
    rw [ha, hb, ix_add_k hk, ix_add_k hk]
  rw [h1, h2, h3] at h0
  exact eq_of_adj_triple_xor h0

lemma pOf_eq_wzero_of_not_dvd6 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (hnd6 : ¬ (6 ∣ k))
    {x : Fin k → Bool} (hamb : rowAmbig hk x) :
    pOf hk x = wzero := by
  by_cases h3 : 3 ∣ k
  · rcases h3 with ⟨r, hr⟩
    have hrodd : r % 2 ≠ 0 := by
      intro hev
      apply hnd6
      exact ⟨r / 2, by omega⟩
    have hup := m1_periodic3_of_rowAmbig hk hk7 hamb
    have hbx : ∀ c : Nat, m1 hk x (ix hk (c + 2)) = totalXor hk x c k := by
      intro c
      have h1 := blockXor_periodic3 hk (m1 hk x) hup (c + 2) r
      simp only [hrodd, ↓reduceIte] at h1
      rw [← h1, blockXor_m1 hk hk7 x c r, ← hr]
    have h23 : m1 hk x (ix hk 2) = m1 hk x (ix hk 3) := by
      rw [hbx 0, hbx 1, totalXor_shift_k hk x 0]
    have h34 : m1 hk x (ix hk 3) = m1 hk x (ix hk 4) := by
      rw [hbx 1, hbx 2, totalXor_shift_k hk x 1]
    have h02 : m1 hk x (ix hk 0) = m1 hk x (ix hk 2) := by
      have h := hup 0
      rw [← h, h23]
    have h12 : m1 hk x (ix hk 1) = m1 hk x (ix hk 2) := by
      have h := hup 1
      rw [← h, ← h34, ← h23]
    have huconst : ∀ t : Nat, m1 hk x (ix hk t) = m1 hk x (ix hk 2) := by
      intro t
      rw [periodic3_mod3 hk (m1 hk x) hup t]
      have hm : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
      rcases hm with h | h | h <;> rw [h]
      · exact h02
      · exact h12
    funext i
    unfold pOf wzero
    rw [huconst (i.val + 1), huconst (i.val + 2), Bool.xor_self]
  · exact zero_of_triple_not_dvd3 hk h3 (pOf hk x) ((rowAmbig_iff_pOf_triple hk hk7 x).mp hamb)

lemma sigOf_mem_sigs {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) {x : Fin k → Bool}
    (hamb : rowAmbig hk x) :
    sigOf hk x ∈ sigs k := by
  unfold sigs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h6
  · exact (rowAmbig_iff_pOf_triple hk hk7 x).mp hamb 2
  · intro j
    unfold sigOf
    rw [pOf_eq_wzero_of_not_dvd6 hk hk7 h6 hamb]
    rfl

def u3 (s : Fin 3 → Bool) (b : Bool) : Fin 3 → Bool
  | ⟨0, _⟩ => b
  | ⟨1, _⟩ => xor b (s 0)
  | ⟨2, _⟩ => xor b (s 2)

def uFor {k : Nat} (s : Fin 3 → Bool) (b : Bool) : Fin k → Bool :=
  fun i => u3 s b ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩

def x6 (u0 u1 u2 : Bool) (r : Fin 6) : Bool :=
  match r.val with
  | 0 => false
  | 1 => false
  | 2 => u2
  | 3 => xor u0 u2
  | 4 => xor u0 u1
  | _ => u1

lemma x6_step (u0 u1 u2 : Bool) (r : Fin 6) :
    xor (x6 u0 u1 u2 r)
      (xor (x6 u0 u1 u2 ⟨(r.val + 1) % 6, Nat.mod_lt _ (by omega)⟩)
           (x6 u0 u1 u2 ⟨(r.val + 2) % 6, Nat.mod_lt _ (by omega)⟩)) =
      match (r.val + 2) % 3 with
      | 0 => u0
      | 1 => u1
      | _ => u2 := by
  rcases r with ⟨r, hr⟩
  have hrm : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  rcases hrm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases u0 <;> cases u1 <;> cases u2 <;> simp [x6]

def preU {k : Nat} (s : Fin 3 → Bool) (b : Bool) : Fin k → Bool :=
  if 6 ∣ k then
    fun i => x6 (u3 s b 0) (u3 s b 1) (u3 s b 2) ⟨i.val % 6, Nat.mod_lt _ (by omega)⟩
  else
    fun _ => b

lemma m1_preU {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) {s : Fin 3 → Bool} (hs : s ∈ sigs k)
    (b : Bool) :
    m1 hk (preU s b) = uFor s b := by
  unfold sigs at hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  by_cases h6 : 6 ∣ k
  · simp only [preU, h6, ↓reduceIte]
    rcases h6 with ⟨q, hq⟩
    funext i
    have hi : i = ix hk ((i.val + k - 2) + 2) := by
      have h1 : i.val + k - 2 + 2 = i.val + k := by omega
      rw [h1, ix_add_k hk, ix_self hk i]
    rw [hi, m1_at_add2 hk hk7 _ (i.val + k - 2)]
    generalize i.val + k - 2 = t
    have hm0 : (ix hk t).val % 6 = t % 6 := by
      change (t % k) % 6 = t % 6
      rw [hq]
      exact Nat.mod_mod_of_dvd t ⟨q, rfl⟩
    have hm1 : (ix hk (t + 1)).val % 6 = (t % 6 + 1) % 6 := by
      change ((t + 1) % k) % 6 = (t % 6 + 1) % 6
      rw [hq, Nat.mod_mod_of_dvd (t + 1) ⟨q, rfl⟩]
      omega
    have hm2 : (ix hk (t + 2)).val % 6 = (t % 6 + 2) % 6 := by
      change ((t + 2) % k) % 6 = (t % 6 + 2) % 6
      rw [hq, Nat.mod_mod_of_dvd (t + 2) ⟨q, rfl⟩]
      omega
    have hm3 : (ix hk (t + 2)).val % 3 = (t % 6 + 2) % 3 := by
      change ((t + 2) % k) % 3 = (t % 6 + 2) % 3
      rw [hq, Nat.mod_mod_of_dvd (t + 2) ⟨2 * q, by omega⟩]
      omega
    have h0 : (⟨(ix hk t).val % 6, Nat.mod_lt _ (by omega)⟩ : Fin 6) =
        ⟨t % 6, Nat.mod_lt _ (by omega)⟩ := Fin.ext hm0
    have h1 : (⟨(ix hk (t + 1)).val % 6, Nat.mod_lt _ (by omega)⟩ : Fin 6) =
        ⟨(t % 6 + 1) % 6, Nat.mod_lt _ (by omega)⟩ := Fin.ext hm1
    have h2 : (⟨(ix hk (t + 2)).val % 6, Nat.mod_lt _ (by omega)⟩ : Fin 6) =
        ⟨(t % 6 + 2) % 6, Nat.mod_lt _ (by omega)⟩ := Fin.ext hm2
    have h3 : (⟨(ix hk (t + 2)).val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) =
        ⟨(t % 6 + 2) % 3, Nat.mod_lt _ (by omega)⟩ := Fin.ext hm3
    unfold uFor
    rw [h0, h1, h2, h3]
    rw [x6_step (u3 s b 0) (u3 s b 1) (u3 s b 2) ⟨t % 6, Nat.mod_lt _ (by omega)⟩]
    have hrem : (t % 6 + 2) % 3 = 0 ∨ (t % 6 + 2) % 3 = 1 ∨ (t % 6 + 2) % 3 = 2 := by omega
    rcases hrem with h | h | h
    · have hf : (⟨(t % 6 + 2) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 0 := Fin.ext h
      simp [h, hf]
    · have hf : (⟨(t % 6 + 2) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 1 := Fin.ext h
      simp [h, hf]
    · have hf : (⟨(t % 6 + 2) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 2 := Fin.ext h
      simp [h, hf]
  · simp only [h6, ↓reduceIte] at hs
    simp only [preU, h6, ↓reduceIte]
    have hu : uFor s b = fun _ : Fin k => b := by
      funext i
      unfold uFor
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with h | h | h
      · have hf : (⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 0 := Fin.ext h
        rw [hf]; rfl
      · have hf : (⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 1 := Fin.ext h
        rw [hf]; simp [u3, hs 0]
      · have hf : (⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 2 := Fin.ext h
        rw [hf]; simp [u3, hs 2]
    rw [hu]
    cases b
    · exact m1_wzero hk
    · exact m1_ones hk

lemma uFor_false_ne_true {k : Nat} (hk : 0 < k) (s : Fin 3 → Bool) :
    (uFor s false : Fin k → Bool) ≠ uFor s true := by
  intro h
  exact Bool.false_ne_true (congrFun h ⟨0, hk⟩)

lemma u3_adj_xor (s : Fin 3 → Bool) (hs : xor (s 0) (xor (s 1) (s 2)) = false) (b : Bool)
    (r : Nat) :
    xor (u3 s b ⟨(r + 1) % 3, Nat.mod_lt _ (by omega)⟩)
        (u3 s b ⟨(r + 2) % 3, Nat.mod_lt _ (by omega)⟩) =
      s ⟨(r + 1) % 3, Nat.mod_lt _ (by omega)⟩ := by
  have hr : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases hr with h | h | h
  · have f1 : (⟨(r + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 1 :=
      Fin.ext (show (r + 1) % 3 = 1 by omega)
    have f2 : (⟨(r + 2) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 2 :=
      Fin.ext (show (r + 2) % 3 = 2 by omega)
    rw [f1, f2]
    simp only [u3]
    cases b <;> cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> simp [h0, h1, h2] at hs ⊢
  · have f1 : (⟨(r + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 2 :=
      Fin.ext (show (r + 1) % 3 = 2 by omega)
    have f2 : (⟨(r + 2) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 0 :=
      Fin.ext (show (r + 2) % 3 = 0 by omega)
    rw [f1, f2]
    simp only [u3]
    cases b <;> cases s 2 <;> rfl
  · have f1 : (⟨(r + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 0 :=
      Fin.ext (show (r + 1) % 3 = 0 by omega)
    have f2 : (⟨(r + 2) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 1 :=
      Fin.ext (show (r + 2) % 3 = 1 by omega)
    rw [f1, f2]
    simp only [u3]
    cases b <;> cases s 0 <;> rfl

lemma sig_triple_xor (s : Fin 3 → Bool) (hs : xor (s 0) (xor (s 1) (s 2)) = false) (t : Nat) :
    xor (s ⟨(t + 1) % 3, Nat.mod_lt _ (by omega)⟩)
      (xor (s ⟨(t + 1 + 1) % 3, Nat.mod_lt _ (by omega)⟩)
           (s ⟨(t + 2 + 1) % 3, Nat.mod_lt _ (by omega)⟩)) = false := by
  have hr : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases hr with h | h | h
  · have f0 : (⟨(t + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 1 :=
      Fin.ext (show (t + 1) % 3 = 1 by omega)
    have f1 : (⟨(t + 1 + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 2 :=
      Fin.ext (show (t + 1 + 1) % 3 = 2 by omega)
    have f2 : (⟨(t + 2 + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 0 :=
      Fin.ext (show (t + 2 + 1) % 3 = 0 by omega)
    rw [f0, f1, f2]
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> simp [h0, h1, h2] at hs ⊢
  · have f0 : (⟨(t + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 2 :=
      Fin.ext (show (t + 1) % 3 = 2 by omega)
    have f1 : (⟨(t + 1 + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 0 :=
      Fin.ext (show (t + 1 + 1) % 3 = 0 by omega)
    have f2 : (⟨(t + 2 + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 1 :=
      Fin.ext (show (t + 2 + 1) % 3 = 1 by omega)
    rw [f0, f1, f2]
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> simp [h0, h1, h2] at hs ⊢
  · have f0 : (⟨(t + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 0 :=
      Fin.ext (show (t + 1) % 3 = 0 by omega)
    have f1 : (⟨(t + 1 + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 1 :=
      Fin.ext (show (t + 1 + 1) % 3 = 1 by omega)
    have f2 : (⟨(t + 2 + 1) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 2 :=
      Fin.ext (show (t + 2 + 1) % 3 = 2 by omega)
    rw [f0, f1, f2]
    exact hs

lemma rowAmbig_sigOf_iff_m1_eq_uFor {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k)
    {s : Fin 3 → Bool} (hs : s ∈ sigs k) (x : Fin k → Bool) :
    (rowAmbig hk x ∧ sigOf hk x = s) ↔ (m1 hk x = uFor s false ∨ m1 hk x = uFor s true) := by
  have hs' := hs
  unfold sigs at hs'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs'
  constructor
  · rintro ⟨hamb, hsig⟩
    have hup := m1_periodic3_of_rowAmbig hk hk7 hamb
    suffices hm : m1 hk x = uFor s (m1 hk x (ix hk 0)) by
      cases hb : m1 hk x (ix hk 0)
      · left; rw [← hb]; exact hm
      · right; rw [← hb]; exact hm
    by_cases h6 : 6 ∣ k
    · have hs0 : s 0 = xor (m1 hk x (ix hk 0)) (m1 hk x (ix hk 1)) := by
        rw [← hsig]
        change xor (m1 hk x (ix hk ((ix hk 2).val + 1))) (m1 hk x (ix hk ((ix hk 2).val + 2))) = _
        rw [ix_add_mod hk 2 1, ix_add_mod hk 2 2]
        change xor (m1 hk x (ix hk (0 + 3))) (m1 hk x (ix hk (1 + 3))) = _
        rw [hup 0, hup 1]
      have hs2 : s 2 = xor (m1 hk x (ix hk 2)) (m1 hk x (ix hk 0)) := by
        rw [← hsig]
        change xor (m1 hk x (ix hk ((ix hk 4).val + 1))) (m1 hk x (ix hk ((ix hk 4).val + 2))) = _
        rw [ix_add_mod hk 4 1, ix_add_mod hk 4 2]
        change xor (m1 hk x (ix hk (2 + 3))) (m1 hk x (ix hk (3 + 3))) = _
        rw [hup 2, hup 3]
        change xor (m1 hk x (ix hk 2)) (m1 hk x (ix hk (0 + 3))) = _
        rw [hup 0]
      have hu1 : m1 hk x (ix hk 1) = xor (m1 hk x (ix hk 0)) (s 0) := xor_solve_right hs0
      have hu2 : m1 hk x (ix hk 2) = xor (m1 hk x (ix hk 0)) (s 2) := xor_solve_left hs2
      funext i
      conv_lhs => rw [← ix_self hk i, periodic3_mod3 hk (m1 hk x) hup i.val]
      unfold uFor
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with h | h | h
      · have hf : (⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 0 := Fin.ext h
        rw [hf, h]; rfl
      · have hf : (⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 1 := Fin.ext h
        rw [hf, h]; exact hu1
      · have hf : (⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 2 := Fin.ext h
        rw [hf, h]; exact hu2
    · simp only [h6, ↓reduceIte] at hs'
      have hp0 := pOf_eq_wzero_of_not_dvd6 hk hk7 h6 hamb
      have hadj : ∀ i : Fin k, m1 hk x (ix hk (i.val + 1)) = m1 hk x (ix hk (i.val + 2)) := by
        intro i
        have hi := congrFun hp0 i
        unfold pOf wzero at hi
        cases h1 : m1 hk x (ix hk (i.val + 1)) <;> cases h2 : m1 hk x (ix hk (i.val + 2)) <;>
          simp [h1, h2] at hi ⊢
      have hconst := const_of_adj_eq hk (m1 hk x) hadj
      funext i
      have h0eq : ix hk 0 = ⟨0, hk⟩ := Fin.ext (Nat.zero_mod k)
      rw [hconst i, h0eq]
      unfold uFor
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with h | h | h
      · have hf : (⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 0 := Fin.ext h
        rw [hf]; rfl
      · have hf : (⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 1 := Fin.ext h
        rw [hf]; simp [u3, hs' 0]
      · have hf : (⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 2 := Fin.ext h
        rw [hf]; simp [u3, hs' 2]
  · intro hdisj
    have hp_val : ∀ b : Bool, m1 hk x = uFor s b →
        ∀ t : Nat, pOf hk x (ix hk t) = s ⟨(t + 1) % 3, Nat.mod_lt _ (by omega)⟩ := by
      intro b hmx t
      unfold pOf
      rw [hmx, ix_add_mod hk t 1, ix_add_mod hk t 2]
      unfold uFor
      by_cases h6 : 6 ∣ k
      · simp only [h6, ↓reduceIte] at hs'
        rcases h6 with ⟨q, hq⟩
        have hm1 : (ix hk (t + 1)).val % 3 = (t + 1) % 3 := by
          change ((t + 1) % k) % 3 = (t + 1) % 3
          rw [hq]
          exact Nat.mod_mod_of_dvd (t + 1) ⟨2 * q, by omega⟩
        have hm2 : (ix hk (t + 2)).val % 3 = (t + 2) % 3 := by
          change ((t + 2) % k) % 3 = (t + 2) % 3
          rw [hq]
          exact Nat.mod_mod_of_dvd (t + 2) ⟨2 * q, by omega⟩
        have h1 : (⟨(ix hk (t + 1)).val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) =
            ⟨(t + 1) % 3, Nat.mod_lt _ (by omega)⟩ := Fin.ext hm1
        have h2 : (⟨(ix hk (t + 2)).val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) =
            ⟨(t + 2) % 3, Nat.mod_lt _ (by omega)⟩ := Fin.ext hm2
        rw [h1, h2]
        exact u3_adj_xor s hs' b t
      · simp only [h6, ↓reduceIte] at hs'
        have hu3 : ∀ c : Fin 3, u3 s b c = b := by
          intro c
          rcases c with ⟨c, hc⟩
          have hcm : c = 0 ∨ c = 1 ∨ c = 2 := by omega
          rcases hcm with rfl | rfl | rfl
          · rfl
          · simp [u3, hs' 0]
          · simp [u3, hs' 2]
        rw [hu3, hu3, hs', Bool.xor_self]
    have hpt : ∀ t : Nat, pOf hk x (ix hk t) = s ⟨(t + 1) % 3, Nat.mod_lt _ (by omega)⟩ := by
      rcases hdisj with h | h
      · exact hp_val false h
      · exact hp_val true h
    constructor
    · rw [rowAmbig_iff_pOf_triple hk hk7 x]
      intro t
      rw [hpt t, hpt (t + 1), hpt (t + 2)]
      by_cases h6 : 6 ∣ k
      · simp only [h6, ↓reduceIte] at hs'
        exact sig_triple_xor s hs' t
      · simp only [h6, ↓reduceIte] at hs'
        rw [hs', hs', hs']
        rfl
    · funext c
      unfold sigOf
      rw [hpt (c.val + 2)]
      congr 1
      apply Fin.ext
      change (c.val + 2 + 1) % 3 = c.val
      have hc := c.isLt
      omega

def kerMap {k : Nat} (ab : Bool × Bool) : Fin k → Bool :=
  fun i => if i.val % 3 = 0 then ab.1 else if i.val % 3 = 1 then ab.2 else xor ab.1 ab.2

lemma card_ker_m1 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) :
    ((Finset.univ : Finset (Fin k → Bool)).filter (fun z => m1 hk z = wzero)).card =
      if 3 ∣ k then 4 else 1 := by
  by_cases h3 : 3 ∣ k
  · simp only [h3, ↓reduceIte]
    rcases h3 with ⟨r, hr⟩
    have hker_eq : (Finset.univ : Finset (Fin k → Bool)).filter (fun z => m1 hk z = wzero) =
        (Finset.univ : Finset (Bool × Bool)).image (kerMap (k := k)) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hz
        have htr : ∀ t : Nat,
            xor (z (ix hk t)) (xor (z (ix hk (t + 1))) (z (ix hk (t + 2)))) = false := by
          intro t
          have h1 := congrFun hz (ix hk (t + 2))
          rw [m1_at_add2 hk hk7 z t] at h1
          exact h1
        have hp := periodic3_of_triple hk z htr
        refine ⟨(z (ix hk 0), z (ix hk 1)), ?_⟩
        have hz2 : z (ix hk 2) = xor (z (ix hk 0)) (z (ix hk 1)) := by
          have h0 := htr 0
          cases hz0 : z (ix hk 0) <;> cases hz1 : z (ix hk 1) <;> cases hz2' : z (ix hk 2) <;>
            simp [hz0, hz1, hz2'] at h0 ⊢
        funext i
        conv_rhs => rw [← ix_self hk i, periodic3_mod3 hk z hp i.val]
        unfold kerMap
        have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
        rcases hm with h | h | h
        · simp [h]
        · simp [h]
        · simp [h, hz2]
      · rintro ⟨ab, rfl⟩
        funext i
        have hi : i = ix hk ((i.val + k - 2) + 2) := by
          have h1 : i.val + k - 2 + 2 = i.val + k := by omega
          rw [h1, ix_add_k hk, ix_self hk i]
        rw [hi, m1_at_add2 hk hk7 (kerMap ab) (i.val + k - 2)]
        generalize i.val + k - 2 = t
        have hm0 : (ix hk t).val % 3 = t % 3 := by
          change (t % k) % 3 = t % 3
          rw [hr]
          exact Nat.mod_mod_of_dvd t ⟨r, rfl⟩
        have hm1 : (ix hk (t + 1)).val % 3 = (t + 1) % 3 := by
          change ((t + 1) % k) % 3 = (t + 1) % 3
          rw [hr]
          exact Nat.mod_mod_of_dvd (t + 1) ⟨r, rfl⟩
        have hm2 : (ix hk (t + 2)).val % 3 = (t + 2) % 3 := by
          change ((t + 2) % k) % 3 = (t + 2) % 3
          rw [hr]
          exact Nat.mod_mod_of_dvd (t + 2) ⟨r, rfl⟩
        unfold kerMap wzero
        rw [hm0, hm1, hm2]
        have hm : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
        rcases hm with h | h | h
        · have h1 : (t + 1) % 3 = 1 := by omega
          have h2 : (t + 2) % 3 = 2 := by omega
          simp only [h, h1, h2]
          cases ab.1 <;> cases ab.2 <;> simp
        · have h1 : (t + 1) % 3 = 2 := by omega
          have h2 : (t + 2) % 3 = 0 := by omega
          simp only [h, h1, h2]
          cases ab.1 <;> cases ab.2 <;> simp
        · have h1 : (t + 1) % 3 = 0 := by omega
          have h2 : (t + 2) % 3 = 1 := by omega
          simp only [h, h1, h2]
          cases ab.1 <;> cases ab.2 <;> simp
    have hinj : Function.Injective (kerMap (k := k)) := by
      intro p q hpq
      have h0 := congrFun hpq ⟨0, hk⟩
      have h1 := congrFun hpq ⟨1, by omega⟩
      simp only [kerMap, Nat.zero_mod, Nat.one_mod, ↓reduceIte] at h0 h1
      have hne1 : (1 : Nat) ≠ 0 := by decide
      simp only [hne1, ↓reduceIte] at h1
      exact Prod.ext h0 h1
    rw [hker_eq, Finset.card_image_of_injective _ hinj]
    decide
  · simp only [h3, ↓reduceIte]
    have hker_eq : (Finset.univ : Finset (Fin k → Bool)).filter (fun z => m1 hk z = wzero) =
        {wzero} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hz
        apply zero_of_triple_not_dvd3 hk h3 z
        intro t
        have h1 := congrFun hz (ix hk (t + 2))
        rw [m1_at_add2 hk hk7 z t] at h1
        exact h1
      · rintro rfl
        exact m1_wzero hk
    rw [hker_eq, Finset.card_singleton]

lemma card_fiber_m1 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (x0 : Fin k → Bool) :
    ((Finset.univ : Finset (Fin k → Bool)).filter (fun x => m1 hk x = m1 hk x0)).card =
      if 3 ∣ k then 4 else 1 := by
  have heq : (Finset.univ : Finset (Fin k → Bool)).filter (fun x => m1 hk x = m1 hk x0) =
      ((Finset.univ : Finset (Fin k → Bool)).filter (fun z => m1 hk z = wzero)).image
        (fun z => wxor x0 z) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      refine ⟨wxor x0 x, ?_, ?_⟩
      · rw [m1_wxor, hx, wxor_self]
      · rw [← wxor_assoc, wxor_self, wzero_wxor]
    · rintro ⟨z, hz, rfl⟩
      rw [m1_wxor, hz, wxor_wzero]
  have hinj : Function.Injective (fun z : Fin k → Bool => wxor x0 z) := by
    intro a b hab
    exact wxor_cancel_left hab
  rw [heq, Finset.card_image_of_injective _ hinj, card_ker_m1 hk hk7]

lemma card_fiber_sig {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) {s : Fin 3 → Bool} (hs : s ∈ sigs k) :
    ((Finset.univ : Finset (Fin k → Bool)).filter (fun x => rowAmbig hk x ∧ sigOf hk x = s)).card =
      2 * (if 3 ∣ k then 4 else 1) := by
  let A := (Finset.univ : Finset (Fin k → Bool)).filter (fun x => m1 hk x = uFor s false)
  let B := (Finset.univ : Finset (Fin k → Bool)).filter (fun x => m1 hk x = uFor s true)
  have hunion : (Finset.univ : Finset (Fin k → Bool)).filter
      (fun x => rowAmbig hk x ∧ sigOf hk x = s) = A ∪ B := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact rowAmbig_sigOf_iff_m1_eq_uFor hk hk7 hs x
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxa hxb
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hxa hxb
    exact uFor_false_ne_true hk s (hxa.symm.trans hxb)
  have hcA : A.card = if 3 ∣ k then 4 else 1 := by
    have hpre := m1_preU hk hk7 hs false
    have hA : A = (Finset.univ : Finset (Fin k → Bool)).filter
        (fun x => m1 hk x = m1 hk (preU s false)) := by
      ext x
      simp only [A, hpre]
    rw [hA]
    exact card_fiber_m1 hk hk7 (preU s false)
  have hcB : B.card = if 3 ∣ k then 4 else 1 := by
    have hpre := m1_preU hk hk7 hs true
    have hB : B = (Finset.univ : Finset (Fin k → Bool)).filter
        (fun x => m1 hk x = m1 hk (preU s true)) := by
      ext x
      simp only [B, hpre]
    rw [hB]
    exact card_fiber_m1 hk hk7 (preU s true)
  rw [hunion, Finset.card_union_of_disjoint hdisj, hcA, hcB]
  omega

lemma conjunct1 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (q : Nat)
    (names : Fin q → Fin k → Bool) (sites : Fin q → Fin k) :
    ((Finset.univ : Finset (Fin k → Bool)).image (transcript hk q names sites)).card +
      (if 3 ∣ k then 4 else 1) * (survive hk q names sites).card = 2 ^ k := by
  let T := transcript hk q names sites
  let S := survive hk q names sites
  let C := (Finset.univ : Finset (Fin k → Bool)).filter
      (fun x => rowAmbig hk x ∧ sigOf hk x ∈ S)
  let Clo := C.filter (fun x => packBits k x < packBits k (mate hk x))
  let Chi := C.filter (fun x => packBits k (mate hk x) < packBits k x)
  have hT_mate : ∀ x ∈ C, T (mate hk x) = T x := by
    intro x hx
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨hamb, hmem⟩
    simp only [S, survive, Finset.mem_filter] at hmem
    apply Prod.ext
    · exact (row_mate hk hamb).symm
    · funext a
      have hcond := hmem.2 a
      have hiff := col_ne_mate_iff hk hk7 hamb (names a) (sites a)
      by_cases hne : col hk (mate hk x) (names a) (sites a) = col hk x (names a) (sites a)
      · exact hne
      · exfalso
        exact (hiff.mp (Ne.symm hne)) hcond
  have hmate_mem : ∀ x ∈ C, mate hk x ∈ C := by
    intro x hx
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨(rowAmbig_mate_and_inv hk hx.1).1, by rw [sigOf_mate hk hx.1]; exact hx.2⟩
  have hT_coll : ∀ x y : Fin k → Bool, x ≠ y → T x = T y →
      x ∈ C ∧ y = mate hk x := by
    intro x y hne hT
    have hrow : row hk x = row hk y := congrArg Prod.fst hT
    have hcol : ∀ a : Fin q, col hk x (names a) (sites a) = col hk y (names a) (sites a) :=
      fun a => congrFun (congrArg Prod.snd hT) a
    have hrc := (row_collision_iff hk x y).mp ⟨hne, hrow⟩
    refine ⟨?_, hrc.2⟩
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hrc.1, ?_⟩
    simp only [S, survive, Finset.mem_filter]
    refine ⟨sigOf_mem_sigs hk hk7 hrc.1, ?_⟩
    intro a
    have hiff := col_ne_mate_iff hk hk7 hrc.1 (names a) (sites a)
    by_cases hcond : sigOf hk x ⟨(sites a).val % 3, Nat.mod_lt (sites a).val (Nat.zero_lt_succ 2)⟩ =
        xor (mix hk 2 (names a) (ix hk ((sites a).val + 1)))
            (mix hk 2 (names a) (ix hk ((sites a).val + 2)))
    · exact hcond
    · exfalso
      have hca := hcol a
      rw [hrc.2] at hca
      exact (hiff.mpr hcond) hca
  have hC_card : C.card = (2 * (if 3 ∣ k then 4 else 1)) * S.card := by
    have hpart : C = S.biUnion (fun s =>
        (Finset.univ : Finset (Fin k → Bool)).filter (fun x => rowAmbig hk x ∧ sigOf hk x = s)) := by
      ext x
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · rintro ⟨hamb, hs⟩
        exact ⟨sigOf hk x, hs, hamb, rfl⟩
      · rintro ⟨s, hs, hamb, rfl⟩
        exact ⟨hamb, hs⟩
    have hpw : (S : Set (Fin 3 → Bool)).PairwiseDisjoint (fun s =>
        (Finset.univ : Finset (Fin k → Bool)).filter (fun x => rowAmbig hk x ∧ sigOf hk x = s)) := by
      intro s1 _ s2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      exact hne (hx1.2.symm.trans hx2.2)
    rw [hpart, Finset.card_biUnion hpw]
    have hsum : ∀ s ∈ S,
        ((Finset.univ : Finset (Fin k → Bool)).filter
          (fun x => rowAmbig hk x ∧ sigOf hk x = s)).card =
          2 * (if 3 ∣ k then 4 else 1) := by
      intro s hs
      have hs' : s ∈ sigs k := (Finset.mem_filter.mp hs).1
      exact card_fiber_sig hk hk7 hs'
    rw [Finset.sum_congr rfl hsum, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hClo_Chi_union : Clo ∪ Chi = C := by
    ext x
    simp only [Clo, Chi, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      have hamb : rowAmbig hk x := (Finset.mem_filter.mp hx).2.1
      have hne : packBits k x ≠ packBits k (mate hk x) := by
        intro heq
        exact (mate_ne_self hk hamb).symm (packBits_inj heq)
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · left; exact ⟨hx, hlt⟩
      · right; exact ⟨hx, hgt⟩
  have hClo_Chi_disj : Disjoint Clo Chi := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Clo, Chi, Finset.mem_filter] at h1 h2
    omega
  have hChi_eq : Chi = Clo.image (mate hk) := by
    ext y
    simp only [Chi, Clo, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hy, hlt⟩
      have hamb : rowAmbig hk y := (Finset.mem_filter.mp hy).2.1
      have hinv := rowAmbig_mate_and_inv hk hamb
      refine ⟨mate hk y, ⟨hmate_mem y hy, ?_⟩, hinv.2⟩
      rw [hinv.2]
      exact hlt
    · rintro ⟨x, ⟨hx, hlt⟩, rfl⟩
      have hamb : rowAmbig hk x := (Finset.mem_filter.mp hx).2.1
      have hinv := rowAmbig_mate_and_inv hk hamb
      refine ⟨hmate_mem x hx, ?_⟩
      rw [hinv.2]
      exact hlt
  have hmate_injOn : Set.InjOn (mate hk) Clo := by
    intro x hx y hy hxy
    have hax : rowAmbig hk x := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2.1
    have hay : rowAmbig hk y := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2.1
    have h1 := congrArg (mate hk) hxy
    rw [(rowAmbig_mate_and_inv hk hax).2, (rowAmbig_mate_and_inv hk hay).2] at h1
    exact h1
  have hC_two : C.card = 2 * Clo.card := by
    rw [← hClo_Chi_union, Finset.card_union_of_disjoint hClo_Chi_disj,
      hChi_eq, Finset.card_image_of_injOn hmate_injOn]
    omega
  have hC_img_eq : C.image T = Clo.image T := by
    ext v
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ Clo ∪ Chi := by rw [hClo_Chi_union]; exact hx
      rcases Finset.mem_union.mp hx' with hlo | hhi
      · exact ⟨x, hlo, rfl⟩
      · rw [hChi_eq] at hhi
        rcases Finset.mem_image.mp hhi with ⟨y, hy, rfl⟩
        exact ⟨y, hy, (hT_mate y (Finset.mem_filter.mp hy).1).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩
  have hT_inj_Clo : Set.InjOn T Clo := by
    intro x hx y hy hxy
    by_cases heq : x = y
    · exact heq
    · exfalso
      have hcol := hT_coll x y heq hxy
      have hxlt : packBits k x < packBits k (mate hk x) := (Finset.mem_filter.mp hx).2
      have hylt : packBits k y < packBits k (mate hk y) := (Finset.mem_filter.mp hy).2
      have hax : rowAmbig hk x := (Finset.mem_filter.mp hcol.1).2.1
      rw [hcol.2, (rowAmbig_mate_and_inv hk hax).2] at hylt
      omega
  have hC_img_card : (C.image T).card = Clo.card := by
    rw [hC_img_eq, Finset.card_image_of_injOn hT_inj_Clo]
  let U := (Finset.univ : Finset (Fin k → Bool)) \ C
  have hU_inj : Set.InjOn T U := by
    intro x hx y _ hxy
    by_cases heq : x = y
    · exact heq
    · exfalso
      have hxC := (hT_coll x y heq hxy).1
      exact (Finset.mem_sdiff.mp hx).2 hxC
  have hU_disj : Disjoint (U.image T) (C.image T) := by
    rw [Finset.disjoint_left]
    intro v hvU hvC
    rcases Finset.mem_image.mp hvU with ⟨x, hxU, rfl⟩
    rcases Finset.mem_image.mp hvC with ⟨y, hyC, hxy⟩
    have hne : x ≠ y := by
      intro heq
      rw [heq] at hxU
      exact (Finset.mem_sdiff.mp hxU).2 hyC
    have hxC := (hT_coll x y hne hxy.symm).1
    exact (Finset.mem_sdiff.mp hxU).2 hxC
  have huniv_eq : (Finset.univ : Finset (Fin k → Bool)) = U ∪ C := by
    ext x
    simp only [U, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    by_cases hx : x ∈ C <;> simp [hx]
  have himg_card : ((Finset.univ : Finset (Fin k → Bool)).image T).card = U.card + Clo.card := by
    rw [huniv_eq, Finset.image_union, Finset.card_union_of_disjoint hU_disj,
      Finset.card_image_of_injOn hU_inj, hC_img_card]
  have htotal : U.card + C.card = 2 ^ k := by
    have hdisjUC : Disjoint U C := Finset.sdiff_disjoint
    have hsum : U.card + C.card = (Finset.univ : Finset (Fin k → Bool)).card := by
      rw [← Finset.card_union_of_disjoint hdisjUC, ← huniv_eq]
    rw [hsum, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [himg_card]
  rw [Nat.mul_assoc] at hC_card
  change U.card + Clo.card + (if 3 ∣ k then 4 else 1) * S.card = 2 ^ k
  omega

def v0 {k : Nat} : Fin k → Bool :=
  wzero

def v1 {k : Nat} : Fin k → Bool :=
  fun i => decide (i.val = 0)

lemma mix2_v0_diff {k : Nat} (hk : 0 < k) :
    xor (mix hk 2 v0 (ix hk 1)) (mix hk 2 v0 (ix hk 2)) = false := by
  unfold v0
  rw [mix_wzero hk 2]
  rfl

lemma mix2_v1_diff {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) :
    xor (mix hk 2 v1 (ix hk 1)) (mix hk 2 v1 (ix hk 2)) = true := by
  have h2m : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
  have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have h3m : 3 % k = 3 := Nat.mod_eq_of_lt (by omega)
  have h4m : 4 % k = 4 := Nat.mod_eq_of_lt (by omega)
  have hm1 : mix hk 2 v1 (ix hk 1) = false := by
    unfold mix v1 ix
    simp only [h2m, h1m]
    have ha : (1 + k - 2) % k ≠ 0 := by
      have h : 1 + k - 2 = k - 1 := by omega
      rw [h, Nat.mod_eq_of_lt (by omega)]
      omega
    have hb : (1 + 2) % k ≠ 0 := by
      rw [h3m]
      omega
    simp [ha, hb]
  have hm2 : mix hk 2 v1 (ix hk 2) = true := by
    unfold mix v1 ix
    simp only [h2m]
    have ha : (2 + k - 2) % k = 0 := by
      have h : 2 + k - 2 = k := by omega
      rw [h, Nat.mod_self]
    have hb : (2 + 2) % k ≠ 0 := by
      rw [h4m]
      omega
    simp [ha, hb]
  rw [hm1, hm2]
  rfl

def s000 : Fin 3 → Bool := fun _ => false
def s011 : Fin 3 → Bool := fun c => decide (c.val ≠ 0)
def s101 : Fin 3 → Bool := fun c => decide (c.val ≠ 1)
def s110 : Fin 3 → Bool := fun c => decide (c.val ≠ 2)

lemma s4_mem_sigs {k : Nat} (h6 : 6 ∣ k) :
    s000 ∈ sigs k ∧ s011 ∈ sigs k ∧ s101 ∈ sigs k ∧ s110 ∈ sigs k := by
  unfold sigs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, h6, ↓reduceIte]
  refine ⟨by decide, by decide, by decide, by decide⟩

lemma s4_sum_eq_two (c : Fin 3) (b : Bool) :
    (if s000 c ≠ b then 1 else 0) + (if s011 c ≠ b then 1 else 0) +
      (if s101 c ≠ b then 1 else 0) + (if s110 c ≠ b then 1 else 0) = 2 := by
  rcases c with ⟨c, hc⟩
  have hcm : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases hcm with rfl | rfl | rfl <;> cases b <;> simp [s000, s011, s101, s110]

lemma row_wzero_eq_ones {k : Nat} (hk : 0 < k) :
    row hk wzero = row hk ones := by
  funext b i
  cases b
  · rw [row_false_eq, row_false_eq, m1_wzero, m1_ones]
    rfl
  · rw [row_true_eq, row_true_eq, m1_wzero, m1_ones]
    have h1 : wxor (wzero (k := k)) ones = ones := wzero_wxor ones
    have h2 : wxor (ones (k := k)) ones = wzero := wxor_self ones
    rw [h1, h2]
    rfl

lemma conjunct2 {k : Nat} (hk : 0 < k) (hk7 : 7 ≤ k) (q D : Nat) :
    (∃ (names : Fin q → Fin k → Bool) (sites : Fin q → Fin k),
      ∀ x y : Fin k → Bool, x ≠ y → row hk x = row hk y →
        D ≤ ((Finset.univ : Finset (Fin q)).filter (fun a =>
          col hk x (names a) (sites a) ≠ col hk y (names a) (sites a))).card) ↔
      (if 6 ∣ k then 2 * D else D) ≤ q := by
  constructor
  · rintro ⟨names, sites, hD⟩
    by_cases h6 : 6 ∣ k
    · simp only [h6, ↓reduceIte]
      have hbound : ∀ s ∈ sigs k,
          D ≤ ((Finset.univ : Finset (Fin q)).filter (fun a =>
            s ⟨(sites a).val % 3, Nat.mod_lt (sites a).val (Nat.zero_lt_succ 2)⟩ ≠
              xor (mix hk 2 (names a) (ix hk ((sites a).val + 1)))
                  (mix hk 2 (names a) (ix hk ((sites a).val + 2))))).card := by
        intro s hs
        let x := preU (k := k) s false
        have hmx : m1 hk x = uFor s false := m1_preU hk hk7 hs false
        have hpair : rowAmbig hk x ∧ sigOf hk x = s :=
          (rowAmbig_sigOf_iff_m1_eq_uFor hk hk7 hs x).mpr (Or.inl hmx)
        have hcol := (row_collision_iff hk x (mate hk x)).mpr ⟨hpair.1, rfl⟩
        have hDx := hD x (mate hk x) hcol.1 hcol.2
        have hfeq : (Finset.univ : Finset (Fin q)).filter (fun a =>
            col hk x (names a) (sites a) ≠ col hk (mate hk x) (names a) (sites a)) =
          (Finset.univ : Finset (Fin q)).filter (fun a =>
            s ⟨(sites a).val % 3, Nat.mod_lt (sites a).val (Nat.zero_lt_succ 2)⟩ ≠
              xor (mix hk 2 (names a) (ix hk ((sites a).val + 1)))
                  (mix hk 2 (names a) (ix hk ((sites a).val + 2)))) := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [col_ne_mate_iff hk hk7 hpair.1 (names a) (sites a), hpair.2]
        rw [← hfeq]
        exact hDx
      rcases s4_mem_sigs h6 with ⟨h0, h1, h2, h3⟩
      have hb0 := hbound s000 h0
      have hb1 := hbound s011 h1
      have hb2 := hbound s101 h2
      have hb3 := hbound s110 h3
      let ca : Fin q → Fin 3 := fun a =>
        ⟨(sites a).val % 3, Nat.mod_lt (sites a).val (Nat.zero_lt_succ 2)⟩
      let ba : Fin q → Bool := fun a =>
        xor (mix hk 2 (names a) (ix hk ((sites a).val + 1)))
            (mix hk 2 (names a) (ix hk ((sites a).val + 2)))
      rw [Finset.card_filter] at hb0 hb1 hb2 hb3
      change D ≤ ∑ a : Fin q, if s000 (ca a) ≠ ba a then 1 else 0 at hb0
      change D ≤ ∑ a : Fin q, if s011 (ca a) ≠ ba a then 1 else 0 at hb1
      change D ≤ ∑ a : Fin q, if s101 (ca a) ≠ ba a then 1 else 0 at hb2
      change D ≤ ∑ a : Fin q, if s110 (ca a) ≠ ba a then 1 else 0 at hb3
      have htot : 4 * D ≤
          ∑ a : Fin q,
            ((if s000 (ca a) ≠ ba a then 1 else 0) +
              (if s011 (ca a) ≠ ba a then 1 else 0) +
              (if s101 (ca a) ≠ ba a then 1 else 0) +
              (if s110 (ca a) ≠ ba a then 1 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
        omega
      have hrhs : ∑ a : Fin q,
            ((if s000 (ca a) ≠ ba a then 1 else 0) +
              (if s011 (ca a) ≠ ba a then 1 else 0) +
              (if s101 (ca a) ≠ ba a then 1 else 0) +
              (if s110 (ca a) ≠ ba a then 1 else 0)) = 2 * q := by
        have hcongr : ∀ a ∈ (Finset.univ : Finset (Fin q)),
            ((if s000 (ca a) ≠ ba a then 1 else 0) +
              (if s011 (ca a) ≠ ba a then 1 else 0) +
              (if s101 (ca a) ≠ ba a then 1 else 0) +
              (if s110 (ca a) ≠ ba a then 1 else 0)) = 2 := by
          intro a _
          exact s4_sum_eq_two (ca a) (ba a)
        rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
      rw [hrhs] at htot
      omega
    · simp only [h6, ↓reduceIte]
      have hne : (wzero : Fin k → Bool) ≠ ones := by
        intro heq
        exact Bool.false_ne_true (congrFun heq ⟨0, hk⟩)
      have hDw := hD wzero ones hne (row_wzero_eq_ones hk)
      have hle : ((Finset.univ : Finset (Fin q)).filter (fun a =>
          col hk wzero (names a) (sites a) ≠ col hk ones (names a) (sites a))).card ≤ q := by
        calc
          ((Finset.univ : Finset (Fin q)).filter (fun a =>
              col hk wzero (names a) (sites a) ≠ col hk ones (names a) (sites a))).card
            ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_filter_le _ _
          _ = q := by rw [Finset.card_univ, Fintype.card_fin]
      exact le_trans hDw hle
  · intro hq
    by_cases h6 : 6 ∣ k
    · simp only [h6, ↓reduceIte] at hq
      refine ⟨fun a => if a.val < D then v0 else v1, fun _ => ⟨0, hk⟩, ?_⟩
      intro x y hne hrow
      have hrc := (row_collision_iff hk x y).mp ⟨hne, hrow⟩
      rw [hrc.2]
      cases hs0 : sigOf hk x 0
      · let f : Fin D → Fin q := fun i => ⟨D + i.val, by omega⟩
        have hfinj : Function.Injective f := by
          intro i j hij
          apply Fin.ext
          have hval := congrArg Fin.val hij
          dsimp [f] at hval
          omega
        have hsub : (Finset.univ : Finset (Fin D)).image f ⊆
            (Finset.univ : Finset (Fin q)).filter (fun a =>
              col hk x (if a.val < D then v0 else v1) ⟨0, hk⟩ ≠
                col hk (mate hk x) (if a.val < D then v0 else v1) ⟨0, hk⟩) := by
          intro a ha
          rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hge : ¬ (D + i.val < D) := by omega
          simp only [f, hge, ↓reduceIte]
          rw [col_ne_mate_iff hk hk7 hrc.1 v1 ⟨0, hk⟩]
          have h0f : (⟨0 % 3, Nat.mod_lt 0 (Nat.zero_lt_succ 2)⟩ : Fin 3) = 0 := rfl
          rw [h0f, hs0, mix2_v1_diff hk hk7]
          decide
        calc
          D = ((Finset.univ : Finset (Fin D)).image f).card := by
            rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
          _ ≤ _ := Finset.card_le_card hsub
      · let f : Fin D → Fin q := fun i => ⟨i.val, by omega⟩
        have hfinj : Function.Injective f := by
          intro i j hij
          apply Fin.ext
          exact (congrArg Fin.val hij : (f i).val = (f j).val)
        have hsub : (Finset.univ : Finset (Fin D)).image f ⊆
            (Finset.univ : Finset (Fin q)).filter (fun a =>
              col hk x (if a.val < D then v0 else v1) ⟨0, hk⟩ ≠
                col hk (mate hk x) (if a.val < D then v0 else v1) ⟨0, hk⟩) := by
          intro a ha
          rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hlt : i.val < D := i.isLt
          simp only [f, hlt, ↓reduceIte]
          rw [col_ne_mate_iff hk hk7 hrc.1 v0 ⟨0, hk⟩]
          have h0f : (⟨0 % 3, Nat.mod_lt 0 (Nat.zero_lt_succ 2)⟩ : Fin 3) = 0 := rfl
          rw [h0f, hs0, mix2_v0_diff hk]
          decide
        calc
          D = ((Finset.univ : Finset (Fin D)).image f).card := by
            rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
          _ ≤ _ := Finset.card_le_card hsub
    · simp only [h6, ↓reduceIte] at hq
      refine ⟨fun _ => v1, fun _ => ⟨0, hk⟩, ?_⟩
      intro x y hne hrow
      have hrc := (row_collision_iff hk x y).mp ⟨hne, hrow⟩
      rw [hrc.2]
      have hsm := sigOf_mem_sigs hk hk7 hrc.1
      unfold sigs at hsm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, h6, ↓reduceIte] at hsm
      have hfilt : (Finset.univ : Finset (Fin q)).filter (fun a =>
          col hk x v1 ⟨0, hk⟩ ≠ col hk (mate hk x) v1 ⟨0, hk⟩) = Finset.univ := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        rw [col_ne_mate_iff hk hk7 hrc.1 v1 ⟨0, hk⟩]
        have h0f : (⟨0 % 3, Nat.mod_lt 0 (Nat.zero_lt_succ 2)⟩ : Fin 3) = 0 := rfl
        rw [h0f, hsm 0, mix2_v1_diff hk hk7]
        decide
      rw [hfilt, Finset.card_univ, Fintype.card_fin]
      exact hq

end PEqualNP.Outside.L_meta_40557_aux

theorem PEqualNP.Outside.L_meta_40557 : (∀ (k : Nat) (hk : 0 < k), 7 ≤ k →
  let W := Fin k → Bool
  let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (a : Nat) (x : W) (i : Fin k) => x (ix (i.val+k-a % k))
  let mix := fun (gap : Nat) (x : W) (i : Fin k) =>
    xor (x (ix (i.val+k-gap % k))) (xor (x i) (x (ix (i.val+gap))))
  let chi := fun (x : W) (i : Fin k) =>
    xor (x i) (!(x (ix (i.val+1))) && x (ix (i.val+2)))
  let row := fun (x : W) (b : Bool) (i : Fin k) =>
    xor (chi (fun t => xor (mix 1 (rot 1 x) t) b) i) (x i)
  let col := fun (x v : W) (i : Fin k) =>
    xor (chi (fun t => xor (mix 2 v t) (mix 2 (rot 3 x) t)) i) (rot 4 x i)
  let transcript := fun (q : Nat) (names : Fin q → W) (sites : Fin q → Fin k) (x : W) =>
    (row x, fun a : Fin q => col x (names a) (sites a))
  let sigs := (Finset.univ : Finset (Fin 3 → Bool)).filter (fun s =>
    if 6 ∣ k then xor (s 0) (xor (s 1) (s 2)) = false else ∀ j, s j = false)
  (∀ (q : Nat) (names : Fin q → W) (sites : Fin q → Fin k),
    let survive := sigs.filter (fun s => ∀ a : Fin q,
      let j := (sites a).val
      s (⟨j % 3, Nat.mod_lt j (Nat.zero_lt_succ 2)⟩ : Fin 3) =
        xor (mix 2 (names a) (ix (j+1))) (mix 2 (names a) (ix (j+2))))
    ((Finset.univ : Finset W).image (transcript q names sites)).card +
      (if 3 ∣ k then 4 else 1) * survive.card = 2^k) ∧
  ∀ q D : Nat, (∃ (names : Fin q → W) (sites : Fin q → Fin k),
    ∀ x y : W, x ≠ y → row x = row y →
      D ≤ ((Finset.univ : Finset (Fin q)).filter (fun a =>
        col x (names a) (sites a) ≠ col y (names a) (sites a))).card) ↔
    (if 6 ∣ k then 2*D else D) ≤ q) := by
  intro k hk hk7
  refine ⟨?_, ?_⟩
  · intro q names sites
    exact PEqualNP.Outside.L_meta_40557_aux.conjunct1 hk hk7 q names sites
  · intro q D
    exact PEqualNP.Outside.L_meta_40557_aux.conjunct2 hk hk7 q D
