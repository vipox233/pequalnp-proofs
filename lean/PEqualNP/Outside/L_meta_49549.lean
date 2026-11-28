import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49549.FiveK5

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

lemma nat_land (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma nat_lor (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nat_xor (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nat_shr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma nat_add (a b : ℕ) : Nat.add a b = a + b := rfl
lemma nat_sub (a b : ℕ) : Nat.sub a b = a - b := rfl

lemma nat_beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.beq_eq.mp hb) h

lemma bv_toNat_not {n : ℕ} (w : BitVec n) : (~~~w).toNat = Nat.xor w.toNat (2 ^ n - 1) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [nat_xor, BitVec.testBit_toNat, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat]
  by_cases hk : k < n
  · simp [hk]
  · simp [hk, BitVec.getLsbD_of_ge w k (Nat.le_of_not_lt hk)]

def elemN (w : ℕ) : List ℕ → Bool
  | [] => false
  | x :: xs => Nat.beq x w || elemN w xs

lemma elemN_map_false {n : ℕ} {w : BitVec n} {r : List (BitVec n)} (h : w ∉ r) :
    elemN w.toNat (r.map BitVec.toNat) = false := by
  induction r with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.map_cons, elemN, Bool.or_eq_false_iff]
    exact ⟨nat_beq_false (fun he => h.1 (BitVec.eq_of_toNat_eq he.symm)), ih h.2⟩

abbrev W4 := BitVec 110
def M4 : ℕ := 0x7fffffffffffff
def A4 : ℕ := 0x3fffffffffffffffffffffffffff
def G4 : ℕ := 0x3fffffffffffff80000000000000
def goal4 : W4 := BitVec.ofNat 110 G4
def ops4 (x y : W4) : List W4 := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps4 (a b : W4) : Finset W4 := (ops4 a b).toFinset
def sep4 (x : W4) : BitVec 55 := ((x >>> 55) ^^^ x).setWidth 55
def cuts4 (ws : List W4) : BitVec 55 := ws.foldr (fun w v => sep4 w ||| v) 0
def k4inputs : List W4 := [BitVec.ofNat 110 0x2add5bab756ead800000003ff800, BitVec.ofNat 110 0x336e6dcdb9b736800001ffc00000, BitVec.ofNat 110 0x3c778ef1de3bc7000ffe00000000, BitVec.ofNat 110 0x3f87f0fe1fc3f87ff00000000000]

lemma hM4_pow : M4 = 2 ^ 55 - 1 := by decide
lemma hA4_pow : A4 = 2 ^ 110 - 1 := by decide

def sep4N (w : ℕ) : ℕ := Nat.land (Nat.xor (Nat.shiftRight w 55) w) 0x7fffffffffffff

lemma sep4_toNat (w : W4) : (sep4 w).toNat = sep4N w.toNat := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [sep4N, show (0x7fffffffffffff : ℕ) = 2 ^ 55 - 1 from hM4_pow, nat_land, nat_xor, nat_shr]
  rw [BitVec.testBit_toNat, Nat.testBit_land, Nat.testBit_xor, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat, BitVec.testBit_toNat]
  by_cases hk : k < 55
  · simp [sep4, hk, Nat.add_comm]
  · rw [BitVec.getLsbD_of_ge (sep4 w) k (Nat.le_of_not_lt hk)]; simp [hk]

def cuts4N : List ℕ → ℕ
  | [] => 0
  | w :: r => Nat.lor (sep4N w) (cuts4N r)

lemma cuts4N_map (ws : List W4) : cuts4N (ws.map BitVec.toNat) = (cuts4 ws).toNat := by
  induction ws with
  | nil => simp [cuts4, cuts4N]
  | cons w r ih =>
    simp only [List.map_cons, cuts4N, cuts4, List.foldr_cons, BitVec.toNat_or, sep4_toNat, ih]
    rfl

def differs4 (i : Fin 55) (w : W4) : Prop :=
  w.getLsbD (55 + i.val) ≠ w.getLsbD i.val

theorem ops4_differs (i : Fin 55) (a b z : W4) (hz : z ∈ basicOps4 a b)
    (hd : differs4 i z) : differs4 i a ∨ differs4 i b := by
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs4 at ha hb
  simp only [not_not] at ha hb
  have hi : 55 + i.val < 110 := by omega
  have hi' : i.val < 110 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts4_spec (ws : List W4) (i : Fin 55) :
    (cuts4 ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs4 i w := by
  induction ws with
  | nil => simp [cuts4]
  | cons a rest ih =>
    change (sep4 a ||| cuts4 rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep4, i.isLt, differs4, Nat.add_comm, bx]

theorem cuts4_full {g : W4} (hg : g = goal4 ∨ g = ~~~goal4) {k : ℕ} {ws : List W4}
    (h : live basicOps4 g k ws.toFinset) : cuts4N (ws.map BitVec.toNat) = M4 := by
  rw [cuts4N_map]
  have hd : ∀ i, differs4 i g := by rcases hg with rfl | rfl <;> unfold differs4 <;> decide +kernel
  have hall : cuts4 ws = -1 := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    have hw := live_separates (differs4 ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops4_differs ⟨j, hj⟩) h
    have hbit := (cuts4_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
    change (cuts4 ws)[j] = (BitVec.allOnes 55)[j]
    rw [BitVec.getElem_allOnes]
    simpa only [BitVec.getLsbD_eq_getElem hj] using hbit
  rw [hall]
  decide

theorem ops4_swap (a b : W4) : basicOps4 a b = basicOps4 b a := by
  ext z
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices4 (a b : W4) (r : List W4) : List (List W4) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept4 {ws r : List W4} {a b : W4} {needed : Finset W4}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices4 a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices4], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices4], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices4], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices4], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list4 {g : W4} {ws : List W4} (hn : ws.Nodup) (hs : ws.toFinset = {g}) : ws = [g] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def tryW4 (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (sa sb base : ℕ) (r : List ℕ) (w : ℕ) : Bool :=
  if Nat.beq w a || Nat.beq w b || elemN w r then false
  else
    let v := Nat.lor (sep4N w) base
    if Nat.beq v 0x7fffffffffffff && next extra (w :: r) then true
    else if Nat.beq extra 0 then false
    else if Nat.beq (Nat.lor v sa) 0x7fffffffffffff && next (Nat.sub extra 1) (w :: a :: r) then true
    else if Nat.beq (Nat.lor v sb) 0x7fffffffffffff && next (Nat.sub extra 1) (w :: b :: r) then true
    else if Nat.ble 2 extra && Nat.beq (Nat.lor (Nat.lor v sa) sb) 0x7fffffffffffff && next (Nat.sub extra 2) (w :: a :: b :: r) then true
    else false

def disp4 (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) : Bool :=
  let base := cuts4N r
  let sa := sep4N a
  let sb := sep4N b
  tryW4 extra next a b sa sb base r (Nat.land a b) ||
  tryW4 extra next a b sa sb base r (Nat.lor a b) ||
  tryW4 extra next a b sa sb base r (Nat.land a (Nat.xor b 0x3fffffffffffffffffffffffffff)) ||
  tryW4 extra next a b sa sb base r (Nat.land b (Nat.xor a 0x3fffffffffffffffffffffffffff))

def pickB4 (extra : ℕ) (next : ℕ → List ℕ → Bool) (a : ℕ) (pre : List ℕ) : List ℕ → Bool
  | [] => false
  | b :: rest =>
    disp4 extra next a b (pre ++ rest) || pickB4 extra next a (b :: pre) rest

def pickA4 (extra : ℕ) (next : ℕ → List ℕ → Bool) (pre : List ℕ) : List ℕ → Bool
  | [] => false
  | a :: rest =>
    pickB4 extra next a pre rest || pickA4 extra next (a :: pre) rest

def opt4 : ℕ → ℕ → List ℕ → Bool
  | 0, _, ws => match ws with | [w] => Nat.beq w 0x3fffffffffffff80000000000000 || Nat.beq w 0x7fffffffffffff | _ => false
  | k + 1, extra, ws =>
    (match ws with | [w] => Nat.beq w 0x3fffffffffffff80000000000000 || Nat.beq w 0x7fffffffffffff | _ => false) ||
    pickA4 extra (opt4 k) [] ws

lemma pickB4_exists (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : W4) (pre ys : List W4)
    (hb : b ∈ ys) :
    ∃ r : List W4, (pre ++ ys).Perm (b :: r) ∧
      (disp4 extra next a.toNat b.toNat (r.map BitVec.toNat) = true →
        pickB4 extra next a.toNat (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true) := by
  induction ys generalizing pre with
  | nil => simp at hb
  | cons y rest ih =>
    rcases List.mem_cons.mp hb with rfl | hbr
    · refine ⟨pre ++ rest, List.perm_middle, fun hd => ?_⟩
      simp only [List.map_cons, pickB4, List.map_append] at hd ⊢
      rw [hd]; rfl
    · obtain ⟨r, hp, himp⟩ := ih (y :: pre) hbr
      refine ⟨r, List.perm_middle.trans hp, fun hd => ?_⟩
      have h := himp hd
      simp only [List.map_cons] at h
      simp only [List.map_cons, pickB4, h, Bool.or_true]

lemma pickA4_exists (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : W4) (pre ys : List W4)
    (ha : a ∈ ys) (hb : b ∈ ys) (hne : a ≠ b) :
    ∃ r : List W4, (pre ++ ys).Perm (a :: b :: r) ∧
      ((disp4 extra next a.toNat b.toNat (r.map BitVec.toNat) = true →
          pickA4 extra next (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true) ∨
       (disp4 extra next b.toNat a.toNat (r.map BitVec.toNat) = true →
          pickA4 extra next (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true)) := by
  induction ys generalizing pre with
  | nil => simp at ha
  | cons y rest ih =>
    rcases List.mem_cons.mp ha with rfl | har
    · have hbr : b ∈ rest := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
      obtain ⟨r, hp, himp⟩ := pickB4_exists extra next a b pre rest hbr
      refine ⟨r, List.perm_middle.trans (hp.cons a), .inl fun hd => ?_⟩
      simp only [List.map_cons, pickA4, himp hd, Bool.true_or]
    · rcases List.mem_cons.mp hb with rfl | hbr
      · obtain ⟨r, hp, himp⟩ := pickB4_exists extra next b a pre rest har
        refine ⟨r, List.perm_middle.trans ((hp.cons b).trans (List.Perm.swap a b r)), .inr fun hd => ?_⟩
        simp only [List.map_cons, pickA4, himp hd, Bool.true_or]
      · obtain ⟨r, hp, himp⟩ := ih (y :: pre) har hbr
        refine ⟨r, List.perm_middle.trans hp, himp.imp (fun f hd => ?_) (fun f hd => ?_)⟩
        · have h := f hd; simp only [List.map_cons] at h; simp only [List.map_cons, pickA4, h, Bool.or_true]
        · have h := f hd; simp only [List.map_cons] at h; simp only [List.map_cons, pickA4, h, Bool.or_true]

theorem disp4_complete {k extra : ℕ} {a b z : W4} {r kept : List W4}
    (next : ℕ → List ℕ → Bool)
    (hz : z ∈ basicOps4 a b) (hza : z ≠ a) (hzb : z ≠ b) (hzr : z ∉ r)
    (hk : kept ∈ keepChoices4 a b r) (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts4N ((z :: kept).map BitVec.toNat) = M4)
    (ht : next (k - kept.length) ((z :: kept).map BitVec.toNat) = true) :
    disp4 extra next a.toNat b.toNat (r.map BitVec.toNat) = true := by
  have htry : tryW4 extra next a.toNat b.toNat (sep4N a.toNat) (sep4N b.toNat)
      (cuts4N (r.map BitVec.toNat)) (r.map BitVec.toNat) z.toNat = true := by
    unfold tryW4
    have hna : Nat.beq z.toNat a.toNat = false := nat_beq_false (fun heq => hza (BitVec.eq_of_toNat_eq heq))
    have hnb : Nat.beq z.toNat b.toNat = false := nat_beq_false (fun heq => hzb (BitVec.eq_of_toNat_eq heq))
    have hnr : elemN z.toNat (r.map BitVec.toNat) = false := elemN_map_false hzr
    rw [hna, hnb, hnr]; simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    have hM4v : (0x7fffffffffffff : ℕ) = M4 := rfl
    simp only [hM4v]
    simp only [keepChoices4, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with hkeq | hkeq | hkeq | hkeq
    · rw [hkeq] at hc ht hn
      simp only [List.map_cons, cuts4N] at hc
      have h1 : Nat.beq (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) M4 = true :=
        Nat.beq_eq.mpr hc
      have h2 : next extra (z.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using (show next extra ((z :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [h1, h2]; rfl
    · rw [hkeq] at hc ht hn
      simp only [List.map_cons, cuts4N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N a.toNat)) M4 = true := by
        have hcomm : Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N a.toNat) =
            Nat.lor (sep4N z.toNat) (Nat.lor (sep4N a.toNat) (cuts4N (r.map BitVec.toNat))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have h2 : next (Nat.sub extra 1) (z.toNat :: a.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 1) ((z :: a :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, h1, h2]
      split_ifs <;> simp_all
    · rw [hkeq] at hc ht hn
      simp only [List.map_cons, cuts4N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N b.toNat)) M4 = true := by
        have hcomm : Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N b.toNat) =
            Nat.lor (sep4N z.toNat) (Nat.lor (sep4N b.toNat) (cuts4N (r.map BitVec.toNat))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have h2 : next (Nat.sub extra 1) (z.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 1) ((z :: b :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, h1, h2]
      split_ifs <;> simp_all
    · rw [hkeq] at hc ht hn
      simp only [List.map_cons, cuts4N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have hge2 : Nat.ble 2 extra = true := Nat.ble_eq.mpr (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N a.toNat)) (sep4N b.toNat)) M4 = true := by
        have hcomm : Nat.lor (Nat.lor (Nat.lor (sep4N z.toNat) (cuts4N (r.map BitVec.toNat))) (sep4N a.toNat)) (sep4N b.toNat) =
            Nat.lor (sep4N z.toNat) (Nat.lor (sep4N a.toNat) (Nat.lor (sep4N b.toNat) (cuts4N (r.map BitVec.toNat)))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have h2 : next (Nat.sub extra 2) (z.toNat :: a.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 2) ((z :: a :: b :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, hge2, h1, h2]
      split_ifs <;> simp_all
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold disp4
  have hnot_b : (~~~b).toNat = Nat.xor b.toNat 0x3fffffffffffffffffffffffffff := by
    rw [show (0x3fffffffffffffffffffffffffff : ℕ) = 2 ^ 110 - 1 from hA4_pow]; exact bv_toNat_not b
  have hnot_a : (~~~a).toNat = Nat.xor a.toNat 0x3fffffffffffffffffffffffffff := by
    rw [show (0x3fffffffffffffffffffffffffff : ℕ) = 2 ^ 110 - 1 from hA4_pow]; exact bv_toNat_not a
  rcases hz with rfl | rfl | rfl | rfl
  · rw [BitVec.toNat_and, ← nat_land] at htry; simp only [htry, Bool.true_or]
  · rw [BitVec.toNat_or, ← nat_lor] at htry; simp only [htry, Bool.or_true, Bool.true_or]
  · rw [BitVec.toNat_and, ← nat_land, hnot_b] at htry; simp only [htry, Bool.or_true, Bool.true_or]
  · rw [BitVec.toNat_and, ← nat_land, hnot_a] at htry; simp only [htry, Bool.or_true]

theorem opt4_complete {g : W4} (hg : g = goal4 ∨ g = ~~~goal4) (n : ℕ) (ws : List W4) (extra : ℕ)
    (hn : ws.Nodup) (room : extra + ws.length = n + 1) (h : live basicOps4 g n ws.toFinset) :
    opt4 n extra (ws.map BitVec.toNat) = true := by
  have hdone : ∀ (u : List W4), u.Nodup → u.toFinset = {g} →
      (match u.map BitVec.toNat with | [w] => Nat.beq w 0x3fffffffffffff80000000000000 || Nat.beq w 0x7fffffffffffff | _ => false) = true := by
    intro u hun hu
    rw [singleton_list4 hun hu]
    rcases hg with rfl | rfl <;> decide
  induction n generalizing ws extra with
  | zero => exact hdone ws hn h
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp only [opt4, hdone ws hn done, Bool.true_or]
    · obtain ⟨r, hp, hpick⟩ := pickA4_exists extra (opt4 k) a b [] ws
        (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      simp only [List.nil_append] at hp
      have go {u v : W4} (perm : ws.Perm (u :: v :: r))
          (hset : ws.toFinset = insert u (insert v needed)) (hop : z ∈ basicOps4 u v) :
          disp4 extra (opt4 k) u.toNat v.toNat (r.map BitVec.toNat) = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept4 perm hn hset
        have hzu : z ≠ u := fun he => hout (hset ▸ he ▸ Finset.mem_insert_self _ _)
        have hzv : z ≠ v := fun he => hout (hset ▸ he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        have hzr : z ∉ r := fun hr => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
        have hznew : z ∉ kept := fun hu => hout (hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps4 g k (z :: kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply disp4_complete (k := k) (extra := extra) (opt4 k) hop hzu hzv hzr hk (by omega) (by omega) (cuts4_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [opt4, Bool.or_eq_true]
      right
      rcases hpick with h1 | h2
      · exact h1 (go hp hs hz)
      · exact h2 (go (hp.trans (List.Perm.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops4_swap a b ▸ hz))

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k4_exact : opt4 6 3 [0x2add5bab756ead800000003ff800, 0x336e6dcdb9b736800001ffc00000, 0x3c778ef1de3bc7000ffe00000000, 0x3f87f0fe1fc3f87ff00000000000] = false := by decide +kernel

lemma k4_nd : k4inputs.Nodup := by decide +kernel

lemma k4_sep_only : ∀ i : Fin 4, ∃ p : Fin 55,
    differs4 p (k4inputs.getD i.val 0) ∧
    ∀ j : Fin 4, j ≠ i → ¬ differs4 p (k4inputs.getD j.val 0) := by
  unfold differs4; decide +kernel

lemma k4_all_mem {g : W4} (hg : g = goal4 ∨ g = ~~~goal4) {k : ℕ} {s : Finset W4}
    (hsub : s ⊆ k4inputs.toFinset) (hl : live basicOps4 g k s) : s = k4inputs.toFinset := by
  apply Finset.Subset.antisymm hsub
  intro w hw
  have hw' : w ∈ k4inputs := List.mem_toFinset.mp hw
  have hidx : ∃ i : Fin 4, k4inputs.getD i.val 0 = w := by
    simp only [k4inputs, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  obtain ⟨i, rfl⟩ := hidx
  obtain ⟨p, hpi, hpj⟩ := k4_sep_only i
  have hdg : ∀ q : Fin 55, differs4 q g := by rcases hg with rfl | rfl <;> unfold differs4 <;> decide +kernel
  obtain ⟨u, hu, hdu⟩ := live_separates (differs4 p) (hdg p) (ops4_differs p) hl
  have hu' : u ∈ k4inputs := List.mem_toFinset.mp (hsub hu)
  have hju : ∃ j : Fin 4, k4inputs.getD j.val 0 = u := by
    simp only [k4inputs, List.mem_cons, List.not_mem_nil, or_false] at hu'
    rcases hu' with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  obtain ⟨j, rfl⟩ := hju
  by_cases hij : j = i
  · subst hij; exact hu
  · exact False.elim (hpj j hij hdu)

theorem k4_no_build6 {g : W4} (hg : g = goal4 ∨ g = ~~~goal4)
    (hb : build basicOps4 g 6 k4inputs.toFinset) : False := by
  obtain ⟨s, hsub, hl⟩ := compress hb
  have heq := k4_all_mem hg hsub hl
  rw [heq] at hl
  have hit := opt4_complete hg 6 k4inputs 3 k4_nd (by decide) hl
  have hmap : k4inputs.map BitVec.toNat = [0x2add5bab756ead800000003ff800, 0x336e6dcdb9b736800001ffc00000, 0x3c778ef1de3bc7000ffe00000000, 0x3f87f0fe1fc3f87ff00000000000] := by decide
  rw [hmap] at hit
  exact Bool.noConfusion (k4_exact.symm.trans hit)

def holds4 (av : Finset W4) (z : W4) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds4_mono {av av' : Finset W4} (sub : av ⊆ av') {x : W4} (h : holds4 av x) :
    holds4 av' x :=
  h.imp_right (Or.imp_right fun ⟨a, ha, e⟩ => ⟨a, sub ha, e⟩)

theorem holds4_not {av : Finset W4} {z : W4} (h : holds4 av z) : holds4 av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable4 (av : Finset W4) (z : W4) : Prop :=
  holds4 av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps4 a b, holds4 (insert w av) z

theorem reachable4_not {av : Finset W4} {z : W4} (h : reachable4 av z) : reachable4 av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds4_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds4_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach4 {av : Finset W4} {x y : W4} (hx : holds4 av x) (hy : holds4 av y) :
    reachable4 av (x &&& y) := by
  have const : holds4 av (0 : W4) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W4) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable4 av (BitVec.allOnes 110 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W4) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable4 av (x &&& BitVec.allOnes 110)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W4) (hw : w ∈ basicOps4 a b) (z : W4) (hz : z = w ∨ z = ~~~w) :
      reachable4 av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps4, ops4] : a &&& b ∈ basicOps4 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps4, ops4] : a &&& ~~~b ∈ basicOps4 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps4, ops4] : b &&& ~~~a ∈ basicOps4 a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps4, ops4] : a ||| b ∈ basicOps4 a b) _ (.inr BitVec.not_or.symm)

theorem or_reach4 {av : Finset W4} {x y : W4} (hx : holds4 av x) (hy : holds4 av y) :
    reachable4 av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable4_not (and_reach4 (holds4_not hx) (holds4_not hy))

theorem mem_ops_reach4 {av : Finset W4} {x y z : W4} (hx : holds4 av x) (hy : holds4 av y)
    (hz : z ∈ basicOps4 x y) : reachable4 av z := by
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact and_reach4 hx hy
  · exact or_reach4 hx hy
  · exact and_reach4 hx (holds4_not hy)
  · exact and_reach4 hy (holds4_not hx)

set_option maxRecDepth 5000 in
theorem mem_ops_const4 {av : Finset W4} {x y z : W4} (hx : holds4 av x) (hy : holds4 av y)
    (hc : (x = 0 ∨ x = ~~~0) ∨ (y = 0 ∨ y = ~~~0)) (hz : z ∈ basicOps4 x y) : holds4 av z := by
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have h0 : holds4 av (0 : W4) := .inl rfl
  have h1 : holds4 av (~~~(0 : W4)) := .inr (.inl rfl)
  have h0and (v : W4) : (0 : W4) &&& v = 0 := BitVec.zero_and
  have hand0 (v : W4) : v &&& (0 : W4) = 0 := BitVec.and_zero
  have h0or (v : W4) : (0 : W4) ||| v = v := BitVec.zero_or
  have hor0 (v : W4) : v ||| (0 : W4) = v := BitVec.or_zero
  have hand1 (v : W4) : v &&& (~~~(0 : W4)) = v :=
    (congrArg (fun u : W4 => v &&& u) (BitVec.not_zero (n := 110))).trans BitVec.and_allOnes
  have h1and (v : W4) : (~~~(0 : W4)) &&& v = v :=
    (congrArg (fun u : W4 => u &&& v) (BitVec.not_zero (n := 110))).trans BitVec.allOnes_and
  have hor1 (v : W4) : v ||| (~~~(0 : W4)) = ~~~(0 : W4) :=
    (congrArg (fun u : W4 => v ||| u) (BitVec.not_zero (n := 110))).trans (BitVec.or_allOnes.trans (BitVec.not_zero (n := 110)).symm)
  have h1or (v : W4) : (~~~(0 : W4)) ||| v = ~~~(0 : W4) :=
    (congrArg (fun u : W4 => u ||| v) (BitVec.not_zero (n := 110))).trans (BitVec.allOnes_or.trans (BitVec.not_zero (n := 110)).symm)
  rcases hc with (rfl | rfl) | (rfl | rfl) <;> rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [h0and, hand0, h0or, hor0, BitVec.not_not,
      hand1, h1and, hor1, h1or] <;>
    first | exact h0 | exact h1 | exact hx | exact hy | exact holds4_not hx | exact holds4_not hy

lemma ops4_const_both {x y z : W4} (hx : x = 0 ∨ x = ~~~0) (hy : y = 0 ∨ y = ~~~0)
    (hz : z ∈ basicOps4 x y) : z = 0 ∨ z = ~~~0 := by
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;> decide

def SignedBuild4 (k : ℕ) (av : Finset W4) (z : W4) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps4 z k av ∨ build basicOps4 (~~~z) k av

theorem sb4_not {av : Finset W4} {z : W4} {k : ℕ} (h : SignedBuild4 k av (~~~z)) :
    SignedBuild4 k av z := by
  rcases h with h | h | h | h
  · exact .inr (.inl (by rw [← BitVec.not_not (b := z), h]))
  · exact .inl (by rw [← BitVec.not_not (b := z), h, BitVec.not_not])
  · exact .inr (.inr (.inr h))
  · exact .inr (.inr (.inl (by simpa only [BitVec.not_not] using h)))

theorem sb4_zero {av : Finset W4} {z : W4} (h : holds4 av z) : SignedBuild4 0 av z := by
  rcases h with h | h | ⟨a, ha, rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not, build] using ha)))

theorem sb4_wait {av : Finset W4} {z : W4} {k : ℕ} (h : SignedBuild4 k av z) :
    SignedBuild4 (k + 1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb4_le {av : Finset W4} {z : W4} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild4 k av z) :
    SignedBuild4 l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb4_wait ih

theorem sb4_step {av : Finset W4} {t a b z : W4} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps4 a b) (h : SignedBuild4 k (insert z av) t) :
    SignedBuild4 (k + 1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩) (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩)))

theorem sb4_advance {av : Finset W4} {z t : W4} {k : ℕ} (hz : reachable4 av z)
    (next : ∀ av' : Finset W4, av ⊆ av' → holds4 av' z → SignedBuild4 k av' t) :
    SignedBuild4 (k + 1) av t := by
  rcases hz with h | ⟨a, ha, b, hb, hn, w, hw, ok⟩
  · exact sb4_wait (next av (fun _ h => h) h)
  · exact sb4_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem k4_no_signed6 : ¬ SignedBuild4 6 k4inputs.toFinset goal4 := by
  intro h
  rcases h with c | c | run | run
  · exact (by decide : goal4 ≠ 0) c
  · exact (by decide : goal4 ≠ ~~~0) c
  · exact k4_no_build6 (.inl rfl) run
  · exact k4_no_build6 (.inr rfl) run

abbrev W5 := BitVec 152
def M5 : ℕ := 0xfffffffffffffffffff
def A5 : ℕ := 0xffffffffffffffffffffffffffffffffffffff
def G5 : ℕ := 0xfffffffffffffffffff0000000000000000000
def goal5 : W5 := BitVec.ofNat 152 G5
def ops5 (x y : W5) : List W5 := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps5 (a b : W5) : Finset W5 := (ops5 a b).toFinset
def sep5 (x : W5) : BitVec 76 := ((x >>> 76) ^^^ x).setWidth 76
def cuts5 (ws : List W5) : BitVec 76 := ws.foldr (fun w v => sep5 w ||| v) 0

def x0 : W5 := BitVec.ofNat 152 0xab7712c4b12c4b12c4b00000000000000ffc00
def x1 : W5 := BitVec.ofNat 152 0xcdbb254952549525495000000000003ff00000
def x2 : W5 := BitVec.ofNat 152 0xf1dd499264992649926000000000ffc0000000
def x3 : W5 := BitVec.ofNat 152 0xfe1e8e2388e2388e2380000003ff0000000000
def x4 : W5 := BitVec.ofNat 152 0xffe0f03c0f03c0f03c00000ffc000000000000
def x01 : W5 := x0 ||| x1
def x02 : W5 := x0 ||| x2
def x23 : W5 := x2 ||| x3
def w03_or : W5 := x01 ||| x2
def w03_an : W5 := x01 &&& ~~~x2
def in5 : List W5 := [x0, x1, x2, x3, x4]
def vinput5 (i : Fin 5) : W5 := in5.getD i.val 0
def mask5 (i : Fin 5) : W5 := ~~~(vinput5 i)

lemma hM5_pow : M5 = 2 ^ 76 - 1 := by decide
lemma hA5_pow : A5 = 2 ^ 152 - 1 := by decide

def sep5N (w : ℕ) : ℕ := Nat.land (Nat.xor (Nat.shiftRight w 76) w) 0xfffffffffffffffffff

lemma sep5_toNat (w : W5) : (sep5 w).toNat = sep5N w.toNat := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [sep5N, show (0xfffffffffffffffffff : ℕ) = 2 ^ 76 - 1 from hM5_pow, nat_land, nat_xor, nat_shr]
  rw [BitVec.testBit_toNat, Nat.testBit_land, Nat.testBit_xor, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat, BitVec.testBit_toNat]
  by_cases hk : k < 76
  · simp [sep5, hk, Nat.add_comm]
  · rw [BitVec.getLsbD_of_ge (sep5 w) k (Nat.le_of_not_lt hk)]; simp [hk]

def cuts5N : List ℕ → ℕ
  | [] => 0
  | w :: r => Nat.lor (sep5N w) (cuts5N r)

lemma cuts5N_map (ws : List W5) : cuts5N (ws.map BitVec.toNat) = (cuts5 ws).toNat := by
  induction ws with
  | nil => simp [cuts5, cuts5N]
  | cons w r ih =>
    simp only [List.map_cons, cuts5N, cuts5, List.foldr_cons, BitVec.toNat_or, sep5_toNat, ih]
    rfl

def differs5 (i : Fin 76) (w : W5) : Prop :=
  w.getLsbD (76 + i.val) ≠ w.getLsbD i.val

theorem ops5_differs (i : Fin 76) (a b z : W5) (hz : z ∈ basicOps5 a b)
    (hd : differs5 i z) : differs5 i a ∨ differs5 i b := by
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs5 at ha hb
  simp only [not_not] at ha hb
  have hi : 76 + i.val < 152 := by omega
  have hi' : i.val < 152 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts5_spec (ws : List W5) (i : Fin 76) :
    (cuts5 ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs5 i w := by
  induction ws with
  | nil => simp [cuts5]
  | cons a rest ih =>
    change (sep5 a ||| cuts5 rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep5, i.isLt, differs5, Nat.add_comm, bx]

theorem cuts5_full {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k : ℕ} {ws : List W5}
    (h : live basicOps5 g k ws.toFinset) : cuts5N (ws.map BitVec.toNat) = M5 := by
  rw [cuts5N_map]
  have hd : ∀ i, differs5 i g := by rcases hg with rfl | rfl <;> unfold differs5 <;> decide +kernel
  have hall : cuts5 ws = -1 := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    have hw := live_separates (differs5 ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops5_differs ⟨j, hj⟩) h
    have hbit := (cuts5_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
    change (cuts5 ws)[j] = (BitVec.allOnes 76)[j]
    rw [BitVec.getElem_allOnes]
    simpa only [BitVec.getLsbD_eq_getElem hj] using hbit
  rw [hall]
  decide

theorem ops5_swap (a b : W5) : basicOps5 a b = basicOps5 b a := by
  ext z
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices5 (a b : W5) (r : List W5) : List (List W5) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept5 {ws r : List W5} {a b : W5} {needed : Finset W5}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices5 a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices5], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices5], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices5], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices5], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list5 {g : W5} {ws : List W5} (hn : ws.Nodup) (hs : ws.toFinset = {g}) : ws = [g] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def holds5 (av : Finset W5) (z : W5) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds5_mono {av av' : Finset W5} (sub : av ⊆ av') {x : W5} (h : holds5 av x) :
    holds5 av' x :=
  h.imp_right (Or.imp_right fun ⟨a, ha, e⟩ => ⟨a, sub ha, e⟩)

theorem holds5_not {av : Finset W5} {z : W5} (h : holds5 av z) : holds5 av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable5 (av : Finset W5) (z : W5) : Prop :=
  holds5 av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps5 a b, holds5 (insert w av) z

theorem reachable5_not {av : Finset W5} {z : W5} (h : reachable5 av z) : reachable5 av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds5_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds5_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach5 {av : Finset W5} {x y : W5} (hx : holds5 av x) (hy : holds5 av y) :
    reachable5 av (x &&& y) := by
  have const : holds5 av (0 : W5) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W5) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable5 av (BitVec.allOnes 152 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W5) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable5 av (x &&& BitVec.allOnes 152)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W5) (hw : w ∈ basicOps5 a b) (z : W5) (hz : z = w ∨ z = ~~~w) :
      reachable5 av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps5, ops5] : a &&& b ∈ basicOps5 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps5, ops5] : a &&& ~~~b ∈ basicOps5 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps5, ops5] : b &&& ~~~a ∈ basicOps5 a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps5, ops5] : a ||| b ∈ basicOps5 a b) _ (.inr BitVec.not_or.symm)

theorem or_reach5 {av : Finset W5} {x y : W5} (hx : holds5 av x) (hy : holds5 av y) :
    reachable5 av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable5_not (and_reach5 (holds5_not hx) (holds5_not hy))

private def bit (k : Fin 152) (z : W5) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W5) (i : ℕ) (k : Fin 152) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W5) (g : Gate) : W5 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W5) (g : Gate) (hg : legal g) (k : Fin 152) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W5)[k.val] = false := by change (BitVec.ofNat 152 0)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read5 {av : Finset W5} {w : List W5} (hw : ∀ u ∈ w, holds5 av u) (i : ℕ) :
    holds5 av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W5) (av : Finset W5) (hw : ∀ u ∈ w, holds5 av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable5 av (action w g) else holds5 av (action w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : W5, x ||| (0 : W5) = x from fun x => BitVec.or_zero,
    show ∀ x : W5, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read5 hw _)
    | exact holds5_not (available_read5 hw _)
    | exact and_reach5 (available_read5 hw _) (available_read5 hw _)
    | exact or_reach5 (available_read5 hw _) (available_read5 hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W5) (av : Finset W5) (hw : ∀ u ∈ w, holds5 av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal5) :
    ∃ t, (t = goal5 ∨ t = ~~~goal5) ∧ build basicOps5 t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal5 := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have h := hv ▸ available_read5 hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim ((by decide : goal5 ≠ 0) zero)
    · exact False.elim ((by decide : goal5 ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal5 := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W5) (hold : ∀ u ∈ w, holds5 A u) (new : holds5 A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds5_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

def table (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfffefee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

theorem spec_k5 : ∀ j : Fin 152,
    Nat.testBit 0xfffefee8 (∑ i : Fin 5, if (in5.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal5[j.val] := by
  intro j; rw [Fin.sum_univ_five]; revert j; decide +kernel

def src4Tbl : Fin 5 → List ℕ :=
  ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 78, 80, 81, 139, 83, 84, 143, 85, 146, 148, 150, 78, 80, 81, 139, 83, 84, 143, 85, 146, 148, 150, 78, 80, 81, 139, 83, 84, 143, 85, 146, 148, 150, 78, 80, 81, 139, 83, 84, 143, 85, 146, 148, 150, 78, 80, 81, 139, 83, 84, 143, 85, 146, 148, 150],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 77, 79, 81, 138, 82, 84, 142, 85, 145, 148, 149, 77, 79, 81, 138, 82, 84, 142, 85, 145, 148, 149, 77, 79, 81, 138, 82, 84, 142, 85, 145, 148, 149, 77, 79, 81, 138, 82, 84, 142, 85, 145, 148, 149, 77, 79, 81, 138, 82, 84, 142, 85, 145, 148, 149],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 76, 79, 80, 137, 82, 83, 141, 85, 145, 146, 147, 76, 79, 80, 137, 82, 83, 141, 85, 145, 146, 147, 76, 79, 80, 137, 82, 83, 141, 85, 145, 146, 147, 76, 79, 80, 137, 82, 83, 141, 85, 145, 146, 147, 76, 79, 80, 137, 82, 83, 141, 85, 145, 146, 147],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 76, 77, 78, 136, 82, 83, 141, 84, 142, 143, 144, 76, 77, 78, 136, 82, 83, 141, 84, 142, 143, 144, 76, 77, 78, 136, 82, 83, 141, 84, 142, 143, 144, 76, 77, 78, 136, 82, 83, 141, 84, 142, 143, 144, 76, 77, 78, 136, 82, 83, 141, 84, 142, 143, 144],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 76, 77, 78, 136, 79, 80, 137, 81, 138, 139, 140, 76, 77, 78, 136, 79, 80, 137, 81, 138, 139, 140, 76, 77, 78, 136, 79, 80, 137, 81, 138, 139, 140, 76, 77, 78, 136, 79, 80, 137, 81, 138, 139, 140, 76, 77, 78, 136, 79, 80, 137, 81, 138, 139, 140]]

def src4Ix (i : Fin 5) (b : Fin 110) : Fin 152 :=
  ⟨(src4Tbl i).getD b.val 0 % 152, Nat.mod_lt _ (by decide)⟩

def rest4 (i : Fin 5) (w : W5) : W4 :=
  (BitVec.ofBoolListLE (List.ofFn (fun b : Fin 110 => w[(src4Ix i b).val]))).cast List.length_ofFn

theorem rest4_bit (i : Fin 5) (w : W5) (b : ℕ) (hb : b < 110) :
    (rest4 i w)[b] = w[(src4Ix i ⟨b, hb⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hb]
  simp only [rest4, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hb, dite_true, Option.getD_some]

theorem rest4_not (i : Fin 5) (u : W5) : rest4 i (~~~u) = ~~~rest4 i u :=
  BitVec.eq_of_getElem_eq fun b hb => by simp only [rest4_bit, BitVec.getElem_not]

theorem rest4_ops (i : Fin 5) (a b z : W5) (hz : z ∈ basicOps5 a b) :
    rest4 i z ∈ basicOps4 (rest4 i a) (rest4 i b) := by
  have hand (u v : W5) : rest4 i (u &&& v) = rest4 i u &&& rest4 i v :=
    BitVec.eq_of_getElem_eq fun b hb => by simp only [rest4_bit, BitVec.getElem_and]
  have hor (u v : W5) : rest4 i (u ||| v) = rest4 i u ||| rest4 i v :=
    BitVec.eq_of_getElem_eq fun b hb => by simp only [rest4_bit, BitVec.getElem_or]
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  simp only [basicOps4, ops4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, rest4_not]

set_option maxRecDepth 8000 in
theorem rest4_goal : ∀ i : Fin 5, rest4 i goal5 = goal4 := by decide +kernel

set_option maxRecDepth 8000 in
theorem rest4_avail : ∀ i j : Fin 5, rest4 i (vinput5 j) = 0 ∨ rest4 i (vinput5 j) ∈ k4inputs := by
  decide +kernel

theorem rest4_holds (i j : Fin 5) : holds4 k4inputs.toFinset (rest4 i (vinput5 j)) := by
  rcases rest4_avail i j with h | h
  · exact .inl h
  · exact .inr (.inr ⟨_, List.mem_toFinset.mpr h, .inl rfl⟩)

set_option maxRecDepth 8000 in
theorem src4_mask : ∀ (i : Fin 5) (b : Fin 110), (mask5 i)[(src4Ix i b).val] = true := by
  decide +kernel

def isC (m w : ℕ) : Bool :=
  let v := Nat.land w m
  Nat.beq v 0 || Nat.beq v m

lemma isC_sound (i : Fin 5) (w : W5) (h : isC (mask5 i).toNat w.toNat = true) :
    rest4 i w = 0 ∨ rest4 i w = ~~~0 := by
  unfold isC at h
  simp only [Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h0 | hm
  · left
    apply BitVec.eq_of_getElem_eq
    intro b hb
    rw [rest4_bit]
    have hbit : (w &&& mask5 i)[(src4Ix i ⟨b, hb⟩).val] = (0 : W5)[(src4Ix i ⟨b, hb⟩).val] := by
      have heq : w &&& mask5 i = 0 := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_and]; exact h0)
      rw [heq]
    rw [BitVec.getElem_and, src4_mask i ⟨b, hb⟩, Bool.and_true] at hbit
    simpa using hbit
  · right
    apply BitVec.eq_of_getElem_eq
    intro b hb
    rw [rest4_bit]
    have hbit : (w &&& mask5 i)[(src4Ix i ⟨b, hb⟩).val] = (mask5 i)[(src4Ix i ⟨b, hb⟩).val] := by
      have heq : w &&& mask5 i = mask5 i := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_and]; exact hm)
      rw [heq]
    rw [BitVec.getElem_and, src4_mask i ⟨b, hb⟩, Bool.and_true] at hbit
    change w[(src4Ix i ⟨b, hb⟩).val] = (BitVec.allOnes 110)[b]
    rw [BitVec.getElem_allOnes]
    exact hbit

theorem live_transport_saveN {f : W5 → W4}
    (hm : ∀ a b z, z ∈ basicOps5 a b → f z ∈ basicOps4 (f a) (f b))
    {g : W5} (hg : f g ≠ 0 ∧ f g ≠ ~~~0) {k : ℕ} {s : Finset W5} {av : Finset W4}
    (run : live basicOps5 g k s) (hav : ∀ w ∈ s, holds4 av (f w))
    (P : Finset W5) (hPs : P ⊆ s) (hP0 : ∀ p ∈ P, f p = 0 ∨ f p = ~~~0) :
    P.card ≤ k ∧ SignedBuild4 (k - P.card) av (f g) := by
  classical
  induction k generalizing s av P with
  | zero =>
    change s = {g} at run
    have hPe : P = ∅ := by
      ext p
      simp only [Finset.notMem_empty, iff_false]
      intro hp
      have hpg : p = g := Finset.mem_singleton.mp (run ▸ hPs hp)
      subst hpg
      rcases hP0 p hp with h | h
      · exact hg.1 h
      · exact hg.2 h
    rw [hPe, Finset.card_empty, Nat.sub_zero]
    exact ⟨le_refl 0, sb4_zero (hav g (by simp [run]))⟩
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hab, z, hz, hout, r, hs, tail⟩
    · obtain ⟨hck, hsb⟩ := ih skip hav P hPs hP0
      exact ⟨Nat.le_succ_of_le hck, sb4_le (by omega) hsb⟩
    · have mapped := hm a b z hz
      have hrsub : ∀ u ∈ r, u ∈ s := fun u hu => hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
      have inOld : ∀ u ∈ r, holds4 av (f u) := fun u hu => hav u (hrsub u hu)
      by_cases haP : a ∈ P
      · by_cases hbP : b ∈ P
        · have hfz0 : f z = 0 ∨ f z = ~~~0 := ops4_const_both (hP0 a haP) (hP0 b hbP) mapped
          have hfzH : holds4 av (f z) := mem_ops_const4 (hav a ha) (hav b hb) (.inl (hP0 a haP)) mapped
          let P' := insert z ((P.erase a).erase b)
          have hznot : z ∉ (P.erase a).erase b := fun hm =>
            hout (hPs (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm)))
          have hbPa : b ∈ P.erase a := Finset.mem_erase.mpr ⟨hab.symm, hbP⟩
          have hcard : P'.card = P.card - 1 := by
            rw [Finset.card_insert_of_notMem hznot, Finset.card_erase_of_mem hbPa,
              Finset.card_erase_of_mem haP]
            have h2 : 2 ≤ P.card := by
              have := Finset.one_lt_card.mpr ⟨a, haP, b, hbP, hab⟩; omega
            omega
          have hP'sub : P' ⊆ insert z r := by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu'
            · exact Finset.mem_insert_self _ _
            · have h1 := Finset.mem_erase.mp hu'
              have h2 := Finset.mem_erase.mp h1.2
              have hus : u ∈ s := hPs h2.2
              rw [hs] at hus
              rcases Finset.mem_insert.mp hus with rfl | hus'
              · exact absurd rfl h2.1
              · rcases Finset.mem_insert.mp hus' with rfl | hur
                · exact absurd rfl h1.1
                · exact Finset.mem_insert_of_mem hur
          have hP'0 : ∀ p ∈ P', f p = 0 ∨ f p = ~~~0 := by
            intro p hp
            rcases Finset.mem_insert.mp hp with rfl | hp'
            · exact hfz0
            · exact hP0 p (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp'))
          obtain ⟨hck, hsb⟩ := ih tail (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hur
            · exact hfzH
            · exact inOld u hur) P' hP'sub hP'0
          rw [hcard] at hck hsb
          have h2 : 2 ≤ P.card := by
            have := Finset.one_lt_card.mpr ⟨a, haP, b, hbP, hab⟩; omega
          exact ⟨by omega, sb4_le (by omega) hsb⟩
        · have hfzH : holds4 av (f z) := mem_ops_const4 (hav a ha) (hav b hb) (.inl (hP0 a haP)) mapped
          let P' := P.erase a
          have hcard : P'.card = P.card - 1 := Finset.card_erase_of_mem haP
          have hP'sub : P' ⊆ insert z r := by
            intro u hu
            have h1 := Finset.mem_erase.mp hu
            have hus : u ∈ s := hPs h1.2
            rw [hs] at hus
            rcases Finset.mem_insert.mp hus with rfl | hus'
            · exact absurd rfl h1.1
            · rcases Finset.mem_insert.mp hus' with rfl | hur
              · exact absurd h1.2 hbP
              · exact Finset.mem_insert_of_mem hur
          have hP'0 : ∀ p ∈ P', f p = 0 ∨ f p = ~~~0 := fun p hp => hP0 p (Finset.mem_of_mem_erase hp)
          obtain ⟨hck, hsb⟩ := ih tail (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hur
            · exact hfzH
            · exact inOld u hur) P' hP'sub hP'0
          rw [hcard] at hck hsb
          have h1 : 1 ≤ P.card := Finset.card_pos.mpr ⟨a, haP⟩
          exact ⟨by omega, sb4_le (by omega) hsb⟩
      · by_cases hbP : b ∈ P
        · have hfzH : holds4 av (f z) := mem_ops_const4 (hav a ha) (hav b hb) (.inr (hP0 b hbP)) mapped
          let P' := P.erase b
          have hcard : P'.card = P.card - 1 := Finset.card_erase_of_mem hbP
          have hP'sub : P' ⊆ insert z r := by
            intro u hu
            have h1 := Finset.mem_erase.mp hu
            have hus : u ∈ s := hPs h1.2
            rw [hs] at hus
            rcases Finset.mem_insert.mp hus with rfl | hus'
            · exact absurd h1.2 haP
            · rcases Finset.mem_insert.mp hus' with rfl | hur
              · exact absurd rfl h1.1
              · exact Finset.mem_insert_of_mem hur
          have hP'0 : ∀ p ∈ P', f p = 0 ∨ f p = ~~~0 := fun p hp => hP0 p (Finset.mem_of_mem_erase hp)
          obtain ⟨hck, hsb⟩ := ih tail (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hur
            · exact hfzH
            · exact inOld u hur) P' hP'sub hP'0
          rw [hcard] at hck hsb
          have h1 : 1 ≤ P.card := Finset.card_pos.mpr ⟨b, hbP⟩
          exact ⟨by omega, sb4_le (by omega) hsb⟩
        · have hPsub : P ⊆ insert z r := by
            intro u hu
            have hus : u ∈ s := hPs hu
            rw [hs] at hus
            rcases Finset.mem_insert.mp hus with rfl | hus'
            · exact absurd hu haP
            · rcases Finset.mem_insert.mp hus' with rfl | hur
              · exact absurd hu hbP
              · exact Finset.mem_insert_of_mem hur
          have hreach := mem_ops_reach4 (hav a ha) (hav b hb) mapped
          have hck : P.card ≤ k := by
            rcases hreach with h | ⟨u, hu, v, hv, hne, w, hw, hok⟩
            · exact (ih tail (fun t ht => by
                rcases Finset.mem_insert.mp ht with rfl | htr
                · exact h
                · exact inOld t htr) P hPsub hP0).1
            · exact (ih tail (fun t ht => by
                rcases Finset.mem_insert.mp ht with rfl | htr
                · exact hok
                · exact holds4_mono (Finset.subset_insert w av) (inOld t htr)) P hPsub hP0).1
          refine ⟨Nat.le_succ_of_le hck, ?_⟩
          have hsub_eq : k + 1 - P.card = (k - P.card) + 1 := by omega
          rw [hsub_eq]
          apply sb4_advance hreach
          intro av' sub ok
          exact (ih tail (fun t ht => by
            rcases Finset.mem_insert.mp ht with rfl | htr
            · exact ok
            · exact holds4_mono sub (inOld t htr)) P hPsub hP0).2

def HasAvoid (k : ℕ) (s : Fin 5 → ℕ) (ws : Finset W5) : Prop :=
  ∀ i : Fin 5, ∃ av : Finset W4,
    (∀ w ∈ ws, holds4 av (rest4 i w)) ∧
    (3 ≤ k + s i → ¬ SignedBuild4 (k + s i - 3) av goal4)

lemma hasAvoid_init {ws : Finset W5} (hsub : ws ⊆ in5.toFinset) :
    HasAvoid 9 (fun _ => 0) ws := by
  intro i
  refine ⟨k4inputs.toFinset, ?_, fun _ => k4_no_signed6⟩
  intro w hw
  have hw' : w ∈ in5 := List.mem_toFinset.mp (hsub hw)
  simp only [in5, List.mem_cons, List.not_mem_nil, or_false] at hw'
  rcases hw' with rfl | rfl | rfl | rfl | rfl
  · exact rest4_holds i 0
  · exact rest4_holds i 1
  · exact rest4_holds i 2
  · exact rest4_holds i 3
  · exact rest4_holds i 4

lemma hasAvoid_step {k : ℕ} {s : Fin 5 → ℕ} {ws ws' : Finset W5} {a b z : W5}
    (hav : HasAvoid (k + 1) s ws) (ha : a ∈ ws) (hb : b ∈ ws)
    (hz : z ∈ basicOps5 a b) (hsub : ws' ⊆ insert z ws) :
    HasAvoid k (fun i => s i + if isC (mask5 i).toNat a.toNat || isC (mask5 i).toNat b.toNat then 1 else 0) ws' := by
  intro i
  obtain ⟨av, hhold, hno⟩ := hav i
  have mapped := rest4_ops i a b z hz
  cases hc : (isC (mask5 i).toNat a.toNat || isC (mask5 i).toNat b.toNat)
  · rcases mem_ops_reach4 (hhold a ha) (hhold b hb) mapped with hok | ⟨u, hu, v, hv, hne, w, hw, hok⟩
    · refine ⟨av, fun t ht => ?_, fun h3 hsb => ?_⟩
      · rcases Finset.mem_insert.mp (hsub ht) with rfl | htw
        · exact hok
        · exact hhold t htw
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h3 hsb
        exact hno (by omega) (sb4_le (by omega) hsb)
    · refine ⟨insert w av, fun t ht => ?_, fun h3 hsb => ?_⟩
      · rcases Finset.mem_insert.mp (hsub ht) with rfl | htw
        · exact hok
        · exact holds4_mono (Finset.subset_insert w av) (hhold t htw)
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h3 hsb
        have hsb' : SignedBuild4 (k + 1 + s i - 3) av goal4 := by
          have heq : k + 1 + s i - 3 = (k + s i - 3) + 1 := by omega
          rw [heq]
          exact sb4_step hu hv hne hw hsb
        exact hno (by omega) hsb'
  · have hconst : (rest4 i a = 0 ∨ rest4 i a = ~~~0) ∨ (rest4 i b = 0 ∨ rest4 i b = ~~~0) := by
      rcases Bool.or_eq_true_iff.mp hc with hca | hcb
      · exact .inl (isC_sound i a hca)
      · exact .inr (isC_sound i b hcb)
    have hok := mem_ops_const4 (hhold a ha) (hhold b hb) hconst mapped
    refine ⟨av, fun t ht => ?_, fun h3 hsb => ?_⟩
    · rcases Finset.mem_insert.mp (hsub ht) with rfl | htw
      · exact hok
      · exact hhold t htw
    · simp only [hc, ↓reduceIte] at h3 hsb
      exact hno (by omega) (by convert hsb using 2; omega)

def okOne (m s : ℕ) : List ℕ → Bool
  | [] => true
  | w :: rest =>
    if isC m w then
      if Nat.ble 2 s then false else okOne m (Nat.add s 1) rest
    else okOne m s rest

def okAll (s0 s1 s2 s3 s4 : ℕ) (ws : List ℕ) : Bool :=
  okOne 0x5488ed3b4ed3b4ed3b4ffffffffffffff003ff s0 ws &&
  okOne 0x3244dab6adab6adab6afffffffffffc00fffff s1 ws &&
  okOne 0xe22b66d9b66d9b66d9fffffffff003fffffff s2 ws &&
  okOne 0x1e171dc771dc771dc7ffffffc00ffffffffff s3 ws &&
  okOne 0x1f0fc3f0fc3f0fc3fffff003ffffffffffff s4 ws

lemma okOne_false_card (m s : ℕ) (ws : List W5) (hnd : ws.Nodup)
    (h : okOne m s (ws.map BitVec.toNat) = false) :
    3 ≤ s + (ws.toFinset.filter (fun w => isC m w.toNat = true)).card := by
  induction ws generalizing s with
  | nil => simp [okOne] at h
  | cons w rest ih =>
    obtain ⟨hwnot, hnd_r⟩ := List.nodup_cons.mp hnd
    have hwnot_f : w ∉ rest.toFinset := fun hm => hwnot (List.mem_toFinset.mp hm)
    simp only [List.map_cons, okOne] at h
    cases hc : isC m w.toNat
    · rw [hc] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      have hrec := ih s hnd_r h
      have hfil : ((w :: rest).toFinset.filter (fun u => isC m u.toNat = true)) =
          rest.toFinset.filter (fun u => isC m u.toNat = true) := by
        ext u; simp only [List.toFinset_cons, Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hr, hu⟩
          · rw [hc] at hu; cases hu
          · exact ⟨hr, hu⟩
        · rintro ⟨hr, hu⟩; exact ⟨.inr hr, hu⟩
      rw [hfil]; exact hrec
    · rw [hc] at h; simp only [↓reduceIte] at h
      have hfil : ((w :: rest).toFinset.filter (fun u => isC m u.toNat = true)) =
          insert w (rest.toFinset.filter (fun u => isC m u.toNat = true)) := by
        ext u; simp only [List.toFinset_cons, Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hr, hu⟩
          · exact .inl rfl
          · exact .inr ⟨hr, hu⟩
        · rintro (rfl | ⟨hr, hu⟩)
          · exact ⟨.inl rfl, hc⟩
          · exact ⟨.inr hr, hu⟩
      have hwnot_fil : w ∉ rest.toFinset.filter (fun u => isC m u.toNat = true) :=
        fun hm => hwnot_f (Finset.mem_filter.mp hm).1
      rw [hfil, Finset.card_insert_of_notMem hwnot_fil]
      cases hle : Nat.ble 2 s
      · rw [hle] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
        have hrec := ih (Nat.add s 1) hnd_r h
        rw [nat_add] at hrec
        omega
      · have h2 : 2 ≤ s := Nat.ble_eq.mp hle
        omega

lemma rest4_g_ne {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) (i : Fin 5) :
    rest4 i g ≠ 0 ∧ rest4 i g ≠ ~~~0 := by
  have hne : goal4 ≠ 0 ∧ goal4 ≠ ~~~0 ∧ ~~~goal4 ≠ 0 ∧ ~~~goal4 ≠ ~~~0 := by decide
  rcases hg with rfl | rfl
  · rw [rest4_goal]; exact ⟨hne.1, hne.2.1⟩
  · rw [rest4_not, rest4_goal]; exact ⟨hne.2.2.1, hne.2.2.2⟩

lemma sb4_of_rest4_g {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) (i : Fin 5) {k : ℕ} {av : Finset W4}
    (h : SignedBuild4 k av (rest4 i g)) : SignedBuild4 k av goal4 := by
  rcases hg with rfl | rfl
  · rwa [rest4_goal] at h
  · rw [rest4_not, rest4_goal] at h; exact sb4_not h

lemma hasAvoid_s_lt3 {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k : ℕ} {s : Fin 5 → ℕ} {ws : Finset W5}
    (hl : live basicOps5 g k ws) (hav : HasAvoid k s ws) (i : Fin 5) : s i < 3 := by
  by_contra hge
  obtain ⟨av, hhold, hno⟩ := hav i
  have ⟨_, hsb⟩ := live_transport_saveN (rest4_ops i) (rest4_g_ne hg i) hl hhold ∅
    (Finset.empty_subset _) (fun _ h => absurd h (Finset.notMem_empty _))
  rw [Finset.card_empty, Nat.sub_zero] at hsb
  exact hno (by omega) (sb4_le (by omega) (sb4_of_rest4_g hg i hsb))

lemma hasAvoid_okOne {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k : ℕ} {s : Fin 5 → ℕ} {ws : List W5}
    (hnd : ws.Nodup) (hl : live basicOps5 g k ws.toFinset) (hav : HasAvoid k s ws.toFinset) (i : Fin 5) :
    okOne (mask5 i).toNat (s i) (ws.map BitVec.toNat) = true := by
  cases h : okOne (mask5 i).toNat (s i) (ws.map BitVec.toNat)
  · exfalso
    have hcard := okOne_false_card (mask5 i).toNat (s i) ws hnd h
    obtain ⟨av, hhold, hno⟩ := hav i
    let P := ws.toFinset.filter (fun w => isC (mask5 i).toNat w.toNat = true)
    have hcard' : 3 ≤ s i + P.card := hcard
    have ⟨hPk, hsb⟩ := live_transport_saveN (rest4_ops i) (rest4_g_ne hg i) hl hhold P
      (Finset.filter_subset _ _) (fun p hp => isC_sound i p (by simpa [P] using (Finset.mem_filter.mp hp).2))
    exact hno (by omega) (sb4_le (by omega) (sb4_of_rest4_g hg i hsb))
  · rfl

lemma mask5_toNat_vals :
    (mask5 0).toNat = 0x5488ed3b4ed3b4ed3b4ffffffffffffff003ff ∧
    (mask5 1).toNat = 0x3244dab6adab6adab6afffffffffffc00fffff ∧
    (mask5 2).toNat = 0xe22b66d9b66d9b66d9fffffffff003fffffff ∧
    (mask5 3).toNat = 0x1e171dc771dc771dc7ffffffc00ffffffffff ∧
    (mask5 4).toNat = 0x1f0fc3f0fc3f0fc3fffff003ffffffffffff := by decide

lemma hasAvoid_okAll {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k : ℕ} {s : Fin 5 → ℕ} {ws : List W5}
    (hnd : ws.Nodup) (hl : live basicOps5 g k ws.toFinset) (hav : HasAvoid k s ws.toFinset) :
    okAll (s 0) (s 1) (s 2) (s 3) (s 4) (ws.map BitVec.toNat) = true := by
  unfold okAll
  have hm := mask5_toNat_vals
  rw [← hm.1, ← hm.2.1, ← hm.2.2.1, ← hm.2.2.2.1, ← hm.2.2.2.2]
  simp only [hasAvoid_okOne hg hnd hl hav 0, hasAvoid_okOne hg hnd hl hav 1,
    hasAvoid_okOne hg hnd hl hav 2, hasAvoid_okOne hg hnd hl hav 3,
    hasAvoid_okOne hg hnd hl hav 4, Bool.and_self]

def tryW5 (extra ns0 ns1 ns2 ns3 ns4 : ℕ)
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool)
    (a b sa sb base : ℕ) (r : List ℕ) (w : ℕ) : Bool :=
  if Nat.beq w a || Nat.beq w b || elemN w r then false
  else
    let v := Nat.lor (sep5N w) base
    if Nat.beq v 0xfffffffffffffffffff && okAll ns0 ns1 ns2 ns3 ns4 (w :: r) && next extra ns0 ns1 ns2 ns3 ns4 (w :: r) then true
    else if Nat.beq extra 0 then false
    else if Nat.beq (Nat.lor v sa) 0xfffffffffffffffffff && okAll ns0 ns1 ns2 ns3 ns4 (w :: a :: r) && next (Nat.sub extra 1) ns0 ns1 ns2 ns3 ns4 (w :: a :: r) then true
    else if Nat.beq (Nat.lor v sb) 0xfffffffffffffffffff && okAll ns0 ns1 ns2 ns3 ns4 (w :: b :: r) && next (Nat.sub extra 1) ns0 ns1 ns2 ns3 ns4 (w :: b :: r) then true
    else if Nat.ble 2 extra && Nat.beq (Nat.lor (Nat.lor v sa) sb) 0xfffffffffffffffffff && okAll ns0 ns1 ns2 ns3 ns4 (w :: a :: b :: r) && next (Nat.sub extra 2) ns0 ns1 ns2 ns3 ns4 (w :: a :: b :: r) then true
    else false

def disp5 (extra s0 s1 s2 s3 s4 : ℕ)
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool)
    (a b : ℕ) (r : List ℕ) : Bool :=
  let ns0 := if isC 0x5488ed3b4ed3b4ed3b4ffffffffffffff003ff a || isC 0x5488ed3b4ed3b4ed3b4ffffffffffffff003ff b then Nat.add s0 1 else s0
  if Nat.ble 3 ns0 then false else
  let ns1 := if isC 0x3244dab6adab6adab6afffffffffffc00fffff a || isC 0x3244dab6adab6adab6afffffffffffc00fffff b then Nat.add s1 1 else s1
  if Nat.ble 3 ns1 then false else
  let ns2 := if isC 0xe22b66d9b66d9b66d9fffffffff003fffffff a || isC 0xe22b66d9b66d9b66d9fffffffff003fffffff b then Nat.add s2 1 else s2
  if Nat.ble 3 ns2 then false else
  let ns3 := if isC 0x1e171dc771dc771dc7ffffffc00ffffffffff a || isC 0x1e171dc771dc771dc7ffffffc00ffffffffff b then Nat.add s3 1 else s3
  if Nat.ble 3 ns3 then false else
  let ns4 := if isC 0x1f0fc3f0fc3f0fc3fffff003ffffffffffff a || isC 0x1f0fc3f0fc3f0fc3fffff003ffffffffffff b then Nat.add s4 1 else s4
  if Nat.ble 3 ns4 then false else
    let base := cuts5N r
    let sa := sep5N a
    let sb := sep5N b
    tryW5 extra ns0 ns1 ns2 ns3 ns4 next a b sa sb base r (Nat.land a b) ||
    tryW5 extra ns0 ns1 ns2 ns3 ns4 next a b sa sb base r (Nat.lor a b) ||
    tryW5 extra ns0 ns1 ns2 ns3 ns4 next a b sa sb base r (Nat.land a (Nat.xor b 0xffffffffffffffffffffffffffffffffffffff)) ||
    tryW5 extra ns0 ns1 ns2 ns3 ns4 next a b sa sb base r (Nat.land b (Nat.xor a 0xffffffffffffffffffffffffffffffffffffff))

def pickB5 (extra s0 s1 s2 s3 s4 : ℕ)
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool)
    (a : ℕ) (pre : List ℕ) : List ℕ → Bool
  | [] => false
  | b :: rest =>
    disp5 extra s0 s1 s2 s3 s4 next a b (pre ++ rest) || pickB5 extra s0 s1 s2 s3 s4 next a (b :: pre) rest

def pickA5 (extra s0 s1 s2 s3 s4 : ℕ)
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool)
    (pre : List ℕ) : List ℕ → Bool
  | [] => false
  | a :: rest =>
    pickB5 extra s0 s1 s2 s3 s4 next a pre rest || pickA5 extra s0 s1 s2 s3 s4 next (a :: pre) rest

def opt5 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool
  | 0, _, _, _, _, _, _, ws => match ws with | [w] => Nat.beq w 0xfffffffffffffffffff0000000000000000000 || Nat.beq w 0xfffffffffffffffffff | _ => false
  | k + 1, extra, s0, s1, s2, s3, s4, ws =>
    (match ws with | [w] => Nat.beq w 0xfffffffffffffffffff0000000000000000000 || Nat.beq w 0xfffffffffffffffffff | _ => false) ||
    pickA5 extra s0 s1 s2 s3 s4 (opt5 k) [] ws

lemma pickB5_exists (extra s0 s1 s2 s3 s4 : ℕ)
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool) (a b : W5) (pre ys : List W5)
    (hb : b ∈ ys) :
    ∃ r : List W5, (pre ++ ys).Perm (b :: r) ∧
      (disp5 extra s0 s1 s2 s3 s4 next a.toNat b.toNat (r.map BitVec.toNat) = true →
        pickB5 extra s0 s1 s2 s3 s4 next a.toNat (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true) := by
  induction ys generalizing pre with
  | nil => simp at hb
  | cons y rest ih =>
    rcases List.mem_cons.mp hb with rfl | hbr
    · refine ⟨pre ++ rest, List.perm_middle, fun hd => ?_⟩
      simp only [List.map_cons, pickB5, List.map_append] at hd ⊢
      rw [hd]; rfl
    · obtain ⟨r, hp, himp⟩ := ih (y :: pre) hbr
      refine ⟨r, List.perm_middle.trans hp, fun hd => ?_⟩
      have h := himp hd
      simp only [List.map_cons] at h
      simp only [List.map_cons, pickB5, h, Bool.or_true]

lemma pickA5_exists (extra s0 s1 s2 s3 s4 : ℕ)
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool) (a b : W5) (pre ys : List W5)
    (ha : a ∈ ys) (hb : b ∈ ys) (hne : a ≠ b) :
    ∃ r : List W5, (pre ++ ys).Perm (a :: b :: r) ∧
      ((disp5 extra s0 s1 s2 s3 s4 next a.toNat b.toNat (r.map BitVec.toNat) = true →
          pickA5 extra s0 s1 s2 s3 s4 next (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true) ∨
       (disp5 extra s0 s1 s2 s3 s4 next b.toNat a.toNat (r.map BitVec.toNat) = true →
          pickA5 extra s0 s1 s2 s3 s4 next (pre.map BitVec.toNat) (ys.map BitVec.toNat) = true)) := by
  induction ys generalizing pre with
  | nil => simp at ha
  | cons y rest ih =>
    rcases List.mem_cons.mp ha with rfl | har
    · have hbr : b ∈ rest := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
      obtain ⟨r, hp, himp⟩ := pickB5_exists extra s0 s1 s2 s3 s4 next a b pre rest hbr
      refine ⟨r, List.perm_middle.trans (hp.cons a), .inl fun hd => ?_⟩
      simp only [List.map_cons, pickA5, himp hd, Bool.true_or]
    · rcases List.mem_cons.mp hb with rfl | hbr
      · obtain ⟨r, hp, himp⟩ := pickB5_exists extra s0 s1 s2 s3 s4 next b a pre rest har
        refine ⟨r, List.perm_middle.trans ((hp.cons b).trans (List.Perm.swap a b r)), .inr fun hd => ?_⟩
        simp only [List.map_cons, pickA5, himp hd, Bool.true_or]
      · obtain ⟨r, hp, himp⟩ := ih (y :: pre) har hbr
        refine ⟨r, List.perm_middle.trans hp, himp.imp (fun f hd => ?_) (fun f hd => ?_)⟩
        · have h := f hd; simp only [List.map_cons] at h; simp only [List.map_cons, pickA5, h, Bool.or_true]
        · have h := f hd; simp only [List.map_cons] at h; simp only [List.map_cons, pickA5, h, Bool.or_true]

theorem disp5_complete {k extra : ℕ} {s : Fin 5 → ℕ} {a b z : W5} {r kept : List W5}
    (next : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool)
    (hz : z ∈ basicOps5 a b) (hza : z ≠ a) (hzb : z ≠ b) (hzr : z ∉ r)
    (hk : kept ∈ keepChoices5 a b r) (he : extra + r.length = k) (hn : kept.length ≤ k)
    (ns_lt : ∀ i : Fin 5, s i + (if isC (mask5 i).toNat a.toNat || isC (mask5 i).toNat b.toNat then 1 else 0) < 3)
    (hc : cuts5N ((z :: kept).map BitVec.toNat) = M5)
    (hok : okAll
      (s 0 + if isC (mask5 0).toNat a.toNat || isC (mask5 0).toNat b.toNat then 1 else 0)
      (s 1 + if isC (mask5 1).toNat a.toNat || isC (mask5 1).toNat b.toNat then 1 else 0)
      (s 2 + if isC (mask5 2).toNat a.toNat || isC (mask5 2).toNat b.toNat then 1 else 0)
      (s 3 + if isC (mask5 3).toNat a.toNat || isC (mask5 3).toNat b.toNat then 1 else 0)
      (s 4 + if isC (mask5 4).toNat a.toNat || isC (mask5 4).toNat b.toNat then 1 else 0)
      ((z :: kept).map BitVec.toNat) = true)
    (ht : next (k - kept.length)
      (s 0 + if isC (mask5 0).toNat a.toNat || isC (mask5 0).toNat b.toNat then 1 else 0)
      (s 1 + if isC (mask5 1).toNat a.toNat || isC (mask5 1).toNat b.toNat then 1 else 0)
      (s 2 + if isC (mask5 2).toNat a.toNat || isC (mask5 2).toNat b.toNat then 1 else 0)
      (s 3 + if isC (mask5 3).toNat a.toNat || isC (mask5 3).toNat b.toNat then 1 else 0)
      (s 4 + if isC (mask5 4).toNat a.toNat || isC (mask5 4).toNat b.toNat then 1 else 0)
      ((z :: kept).map BitVec.toNat) = true) :
    disp5 extra (s 0) (s 1) (s 2) (s 3) (s 4) next a.toNat b.toNat (r.map BitVec.toNat) = true := by
  have hm := mask5_toNat_vals
  let ns : Fin 5 → ℕ := fun i => s i + if isC (mask5 i).toNat a.toNat || isC (mask5 i).toNat b.toNat then 1 else 0
  have htry : tryW5 extra (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) next a.toNat b.toNat (sep5N a.toNat) (sep5N b.toNat)
      (cuts5N (r.map BitVec.toNat)) (r.map BitVec.toNat) z.toNat = true := by
    unfold tryW5
    have hna : Nat.beq z.toNat a.toNat = false := nat_beq_false (fun heq => hza (BitVec.eq_of_toNat_eq heq))
    have hnb : Nat.beq z.toNat b.toNat = false := nat_beq_false (fun heq => hzb (BitVec.eq_of_toNat_eq heq))
    have hnr : elemN z.toNat (r.map BitVec.toNat) = false := elemN_map_false hzr
    rw [hna, hnb, hnr]; simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    have hM5v : (0xfffffffffffffffffff : ℕ) = M5 := rfl
    simp only [hM5v]
    simp only [keepChoices5, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with hkeq | hkeq | hkeq | hkeq
    · rw [hkeq] at hc hok ht hn
      simp only [List.map_cons, cuts5N] at hc
      have h1 : Nat.beq (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) M5 = true :=
        Nat.beq_eq.mpr hc
      have hok' : okAll (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using hok
      have h2 : next extra (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using (show next extra (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) ((z :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [h1, hok', h2]; rfl
    · rw [hkeq] at hc hok ht hn
      simp only [List.map_cons, cuts5N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) (sep5N a.toNat)) M5 = true := by
        have hcomm : Nat.lor (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) (sep5N a.toNat) =
            Nat.lor (sep5N z.toNat) (Nat.lor (sep5N a.toNat) (cuts5N (r.map BitVec.toNat))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have hok' : okAll (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: a.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using hok
      have h2 : next (Nat.sub extra 1) (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: a.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 1) (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) ((z :: a :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, h1, hok', h2]
      split_ifs <;> simp_all
    · rw [hkeq] at hc hok ht hn
      simp only [List.map_cons, cuts5N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) (sep5N b.toNat)) M5 = true := by
        have hcomm : Nat.lor (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) (sep5N b.toNat) =
            Nat.lor (sep5N z.toNat) (Nat.lor (sep5N b.toNat) (cuts5N (r.map BitVec.toNat))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have hok' : okAll (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using hok
      have h2 : next (Nat.sub extra 1) (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 1) (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) ((z :: b :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, h1, hok', h2]
      split_ifs <;> simp_all
    · rw [hkeq] at hc hok ht hn
      simp only [List.map_cons, cuts5N] at hc
      simp only [List.length_cons] at hn ht
      have hnz : Nat.beq extra 0 = false := nat_beq_false (by omega)
      have hge2 : Nat.ble 2 extra = true := Nat.ble_eq.mpr (by omega)
      have h1 : Nat.beq (Nat.lor (Nat.lor (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) (sep5N a.toNat)) (sep5N b.toNat)) M5 = true := by
        have hcomm : Nat.lor (Nat.lor (Nat.lor (sep5N z.toNat) (cuts5N (r.map BitVec.toNat))) (sep5N a.toNat)) (sep5N b.toNat) =
            Nat.lor (sep5N z.toNat) (Nat.lor (sep5N a.toNat) (Nat.lor (sep5N b.toNat) (cuts5N (r.map BitVec.toNat)))) := by
          apply Nat.eq_of_testBit_eq; intro t; simp only [nat_lor, Nat.testBit_lor]; grind
        rw [hcomm]; exact Nat.beq_eq.mpr hc
      have hok' : okAll (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: a.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        simpa only [List.map_cons] using hok
      have h2 : next (Nat.sub extra 2) (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) (z.toNat :: a.toNat :: b.toNat :: r.map BitVec.toNat) = true := by
        rw [nat_sub]; simpa only [List.map_cons] using (show next (extra - 2) (ns 0) (ns 1) (ns 2) (ns 3) (ns 4) ((z :: a :: b :: r).map BitVec.toNat) = true by convert ht using 2; omega)
      rw [hnz, hge2, h1, hok', h2]
      split_ifs <;> simp_all
  unfold disp5
  rw [← hm.1, ← hm.2.1, ← hm.2.2.1, ← hm.2.2.2.1, ← hm.2.2.2.2]
  have hns_eq : ∀ i : Fin 5, (if isC (mask5 i).toNat a.toNat || isC (mask5 i).toNat b.toNat then Nat.add (s i) 1 else s i) = ns i := by
    intro i; dsimp only [ns]; cases isC (mask5 i).toNat a.toNat || isC (mask5 i).toNat b.toNat <;> simp
  have hble_f : ∀ i : Fin 5, Nat.ble 3 (ns i) = false := by
    intro i
    have hlt := ns_lt i
    change ns i < 3 at hlt
    cases hb : Nat.ble 3 (ns i)
    · rfl
    · exfalso; have := Nat.ble_eq.mp hb; omega
  simp only [hns_eq 0, hns_eq 1, hns_eq 2, hns_eq 3, hns_eq 4,
    hble_f 0, hble_f 1, hble_f 2, hble_f 3, hble_f 4, Bool.false_eq_true, ↓reduceIte]
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have hnot_b : (~~~b).toNat = Nat.xor b.toNat 0xffffffffffffffffffffffffffffffffffffff := by
    rw [show (0xffffffffffffffffffffffffffffffffffffff : ℕ) = 2 ^ 152 - 1 from hA5_pow]; exact bv_toNat_not b
  have hnot_a : (~~~a).toNat = Nat.xor a.toNat 0xffffffffffffffffffffffffffffffffffffff := by
    rw [show (0xffffffffffffffffffffffffffffffffffffff : ℕ) = 2 ^ 152 - 1 from hA5_pow]; exact bv_toNat_not a
  rcases hz with rfl | rfl | rfl | rfl
  · rw [BitVec.toNat_and, ← nat_land] at htry; simp only [htry, Bool.true_or]
  · rw [BitVec.toNat_or, ← nat_lor] at htry; simp only [htry, Bool.or_true, Bool.true_or]
  · rw [BitVec.toNat_and, ← nat_land, hnot_b] at htry; simp only [htry, Bool.or_true, Bool.true_or]
  · rw [BitVec.toNat_and, ← nat_land, hnot_a] at htry; simp only [htry, Bool.or_true]

theorem opt5_complete {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) (n : ℕ) (ws : List W5) (extra : ℕ)
    (s : Fin 5 → ℕ) (hn : ws.Nodup) (room : extra + ws.length = n + 1)
    (h : live basicOps5 g n ws.toFinset) (hav : HasAvoid n s ws.toFinset) :
    opt5 n extra (s 0) (s 1) (s 2) (s 3) (s 4) (ws.map BitVec.toNat) = true := by
  have hdone : ∀ (u : List W5), u.Nodup → u.toFinset = {g} →
      (match u.map BitVec.toNat with | [w] => Nat.beq w 0xfffffffffffffffffff0000000000000000000 || Nat.beq w 0xfffffffffffffffffff | _ => false) = true := by
    intro u hun hu
    rw [singleton_list5 hun hu]
    rcases hg with rfl | rfl <;> decide
  induction n generalizing ws extra s with
  | zero => exact hdone ws hn h
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp only [opt5, hdone ws hn done, Bool.true_or]
    · obtain ⟨r, hp, hpick⟩ := pickA5_exists extra (s 0) (s 1) (s 2) (s 3) (s 4) (opt5 k) a b [] ws
        (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      simp only [List.nil_append] at hp
      have go {u v : W5} (perm : ws.Perm (u :: v :: r))
          (hset : ws.toFinset = insert u (insert v needed)) (hop : z ∈ basicOps5 u v) :
          disp5 extra (s 0) (s 1) (s 2) (s 3) (s 4) (opt5 k) u.toNat v.toNat (r.map BitVec.toNat) = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 perm hn hset
        have hzu : z ≠ u := fun he => hout (hset ▸ he ▸ Finset.mem_insert_self _ _)
        have hzv : z ≠ v := fun he => hout (hset ▸ he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        have hzr : z ∉ r := fun hr => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
        have hznew : z ∉ kept := fun hu => hout (hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps5 g k (z :: kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hsub : (z :: kept).toFinset ⊆ insert z ws.toFinset := by
          intro t ht
          rcases Finset.mem_insert.mp (by simpa [hfin] using ht) with rfl | htn
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem htn))
        have hu_mem : u ∈ ws.toFinset := hset ▸ Finset.mem_insert_self _ _
        have hv_mem : v ∈ ws.toFinset := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        have hav' := hasAvoid_step hav hu_mem hv_mem hop hsub
        have hlt3 := hasAvoid_s_lt3 hg hl hav'
        have hok := hasAvoid_okAll hg hnd hl hav'
        apply disp5_complete (k := k) (extra := extra) (s := s) (opt5 k) hop hzu hzv hzr hk
          (by omega) (by omega) hlt3 (cuts5_full hg hl) hok
        apply ih _ _ _ hnd _ hl hav'
        simp; omega
      simp only [opt5, Bool.or_eq_true]
      right
      rcases hpick with h1 | h2
      · exact h1 (go hp hs hz)
      · exact h2 (go (hp.trans (List.Perm.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops5_swap a b ▸ hz))

lemma disp5_of_step {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k extra : ℕ} {s : Fin 5 → ℕ}
    {ws r : List W5} {a b z : W5} {rest : Finset W5}
    (hn : ws.Nodup) (room : extra + ws.length = k + 2)
    (perm : ws.Perm (a :: b :: r)) (hs : ws.toFinset = insert a (insert b rest))
    (hz : z ∈ basicOps5 a b) (hzout : z ∉ ws.toFinset)
    (tail : live basicOps5 g k (insert z rest)) (hav : HasAvoid (k + 1) s ws.toFinset) :
    disp5 extra (s 0) (s 1) (s 2) (s 3) (s 4) (opt5 k) a.toNat b.toNat (r.map BitVec.toNat) = true := by
  obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 perm hn hs
  have hza : z ≠ a := fun he => hzout (hs ▸ he ▸ Finset.mem_insert_self _ _)
  have hzb : z ≠ b := fun he => hzout (hs ▸ he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hzr : z ∉ r := fun hr => hzout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
  have hznew : z ∉ kept := fun hu => hzout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
  have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
  have hl : live basicOps5 g k (z :: kept).toFinset := by simpa [hfin] using tail
  have hc := live_card hl
  rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
  have len := perm.length_eq
  simp only [List.length_cons] at len
  have hsub : (z :: kept).toFinset ⊆ insert z ws.toFinset := by
    intro t ht
    rcases Finset.mem_insert.mp (by simpa [hfin] using ht) with rfl | htn
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem htn))
  have ha_mem : a ∈ ws.toFinset := hs ▸ Finset.mem_insert_self _ _
  have hb_mem : b ∈ ws.toFinset := hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hav' := hasAvoid_step hav ha_mem hb_mem hz hsub
  have hlt3 := hasAvoid_s_lt3 hg hl hav'
  have hok := hasAvoid_okAll hg hnd hl hav'
  apply disp5_complete (k := k) (extra := extra) (s := s) (opt5 k) hz hza hzb hzr hk
    (by omega) (by omega) hlt3 (cuts5_full hg hl) hok
  apply opt5_complete hg k (z :: kept) (k - kept.length) _ hnd (by simp; omega) hl hav'

def row5Tbl : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 7, 11, 13, 14, 15, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31]
def rowPosTbl : List ℕ := [0, 10, 20, 76, 30, 77, 78, 136, 40, 79, 80, 137, 81, 138, 139, 140, 50, 82, 83, 141, 84, 142, 143, 144, 85, 145, 146, 147, 148, 149, 150, 151]

def row5 (k : Fin 152) : Fin 32 :=
  ⟨row5Tbl.getD k.val 0 % 32, Nat.mod_lt _ (by decide)⟩

def rowPos (r : Fin 32) : Fin 152 :=
  ⟨rowPosTbl.getD r.val 0 % 152, Nat.mod_lt _ (by decide)⟩

def swap (a b x : Fin 5) : Fin 5 :=
  if x = a then b else if x = b then a else x

def permRow (σ : Fin 5 → Fin 5) (r : Fin 32) : Fin 32 :=
  let b (i : Fin 5) (p : ℕ) : ℕ := if Nat.testBit r.val (σ i).val then p else 0
  ⟨(b 0 1 + b 1 2 + b 2 4 + b 3 8 + b 4 16) % 32, Nat.mod_lt _ (by decide)⟩

def permIx (σ : Fin 5 → Fin 5) (k : Fin 152) : Fin 152 :=
  rowPos (permRow σ (row5 k))

def perm5 (σ : Fin 5 → Fin 5) (w : W5) : W5 :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 152 => w[(permIx σ k).val]))).cast List.length_ofFn

theorem perm5_bit (σ : Fin 5 → Fin 5) (w : W5) (k : ℕ) (hk : k < 152) :
    (perm5 σ w)[k] = w[(permIx σ ⟨k, hk⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hk]
  simp only [perm5, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk, dite_true, Option.getD_some]

theorem perm5_not (σ : Fin 5 → Fin 5) (u : W5) : perm5 σ (~~~u) = ~~~perm5 σ u :=
  BitVec.eq_of_getElem_eq fun k hk => by simp only [perm5_bit, BitVec.getElem_not]

theorem perm5_and (σ : Fin 5 → Fin 5) (u v : W5) : perm5 σ (u &&& v) = perm5 σ u &&& perm5 σ v :=
  BitVec.eq_of_getElem_eq fun k hk => by simp only [perm5_bit, BitVec.getElem_and]

theorem perm5_or (σ : Fin 5 → Fin 5) (u v : W5) : perm5 σ (u ||| v) = perm5 σ u ||| perm5 σ v :=
  BitVec.eq_of_getElem_eq fun k hk => by simp only [perm5_bit, BitVec.getElem_or]

theorem perm5_ops (σ : Fin 5 → Fin 5) (a b z : W5) (hz : z ∈ basicOps5 a b) :
    perm5 σ z ∈ basicOps5 (perm5 σ a) (perm5 σ b) := by
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [perm5_and, perm5_or, perm5_not]

def Valid5 (w : W5) : Prop :=
  ∀ k : Fin 152, w[k.val] = w[(rowPos (row5 k)).val]

def valid5B (w : W5) : Bool := (List.finRange 152).all fun k => w[k.val] == w[(rowPos (row5 k)).val]

lemma valid5_of_valid5B {w : W5} (h : valid5B w = true) : Valid5 w := by
  intro k
  have hk := List.all_eq_true.mp h k (List.mem_finRange k)
  simpa using hk

lemma valid5_ops {a b z : W5} (ha : Valid5 a) (hb : Valid5 b) (hz : z ∈ basicOps5 a b) : Valid5 z := by
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  intro k
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, ha k, hb k]

set_option maxRecDepth 8000 in
lemma row5_rowPos : ∀ r : Fin 32, row5 (rowPos r) = r := by decide +kernel

lemma perm5_valid (a b : Fin 5) (w : W5) : Valid5 (perm5 (swap a b) w) := by
  intro k
  rw [perm5_bit, perm5_bit]
  have h1 : permIx (swap a b) ⟨k.val, k.isLt⟩ = permIx (swap a b) ⟨(rowPos (row5 k)).val, (rowPos (row5 k)).isLt⟩ := by
    simp only [permIx, Fin.eta, row5_rowPos]
  exact congrArg (fun j : Fin 152 => w[j.val]) h1

set_option maxRecDepth 8000 in
lemma permRow_swap_invol : ∀ (a b : Fin 5) (r : Fin 32),
    permRow (swap a b) (permRow (swap a b) r) = r := by decide +kernel

lemma perm5_swap_row (a b : Fin 5) (k : Fin 152) :
    row5 (permIx (swap a b) (permIx (swap a b) k)) = row5 k := by
  simp only [permIx, row5_rowPos, permRow_swap_invol]

lemma perm5_swap_invol (a b : Fin 5) {w : W5} (hw : Valid5 w) :
    perm5 (swap a b) (perm5 (swap a b) w) = w := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rw [perm5_bit, perm5_bit, hw (permIx (swap a b) (permIx (swap a b) ⟨k, hk⟩))]
  exact (congrArg (fun r : Fin 32 => w[(rowPos r).val]) (perm5_swap_row a b ⟨k, hk⟩)).trans (hw ⟨k, hk⟩).symm

lemma perm5_swap_inj (a b : Fin 5) {u v : W5} (hu : Valid5 u) (hv : Valid5 v)
    (heq : perm5 (swap a b) u = perm5 (swap a b) v) : u = v := by
  rw [← perm5_swap_invol a b hu, ← perm5_swap_invol a b hv, heq]

lemma valid5_goal : Valid5 goal5 := valid5_of_valid5B (by decide +kernel)

set_option maxRecDepth 8000 in
lemma goal5_permRow : ∀ (a b : Fin 5) (r : Fin 32),
    goal5[(rowPos (permRow (swap a b) r)).val] = goal5[(rowPos r).val] := by decide +kernel

lemma perm5_swap_goal (a b : Fin 5) : perm5 (swap a b) goal5 = goal5 := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rw [perm5_bit]
  exact (goal5_permRow a b (row5 ⟨k, hk⟩)).trans (valid5_goal ⟨k, hk⟩).symm

set_option maxRecDepth 8000 in
lemma vinput5_bit : ∀ (i : Fin 5) (k : Fin 152),
    (vinput5 i)[k.val] = Nat.testBit (row5 k).val i.val := by decide +kernel

set_option maxRecDepth 8000 in
lemma permRow_bit : ∀ (a b i : Fin 5) (r : Fin 32),
    Nat.testBit (permRow (swap a b) r).val i.val = Nat.testBit r.val (swap a b i).val := by decide +kernel

lemma perm5_swap_in (a b i : Fin 5) : perm5 (swap a b) (vinput5 i) = vinput5 (swap a b i) := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  rw [perm5_bit, vinput5_bit i (permIx (swap a b) ⟨k, hk⟩), permIx, row5_rowPos,
    permRow_bit, ← vinput5_bit (swap a b i) ⟨k, hk⟩]

lemma p_01_x0 : perm5 (swap 0 1) x0 = x1 := perm5_swap_in 0 1 0
lemma p_01_x1 : perm5 (swap 0 1) x1 = x0 := perm5_swap_in 0 1 1
lemma p_01_x2 : perm5 (swap 0 1) x2 = x2 := perm5_swap_in 0 1 2
lemma p_01_x3 : perm5 (swap 0 1) x3 = x3 := perm5_swap_in 0 1 3
lemma p_01_x4 : perm5 (swap 0 1) x4 = x4 := perm5_swap_in 0 1 4
lemma p_12_x0 : perm5 (swap 1 2) x0 = x0 := perm5_swap_in 1 2 0
lemma p_12_x1 : perm5 (swap 1 2) x1 = x2 := perm5_swap_in 1 2 1
lemma p_12_x2 : perm5 (swap 1 2) x2 = x1 := perm5_swap_in 1 2 2
lemma p_12_x3 : perm5 (swap 1 2) x3 = x3 := perm5_swap_in 1 2 3
lemma p_12_x4 : perm5 (swap 1 2) x4 = x4 := perm5_swap_in 1 2 4
lemma p_23_x0 : perm5 (swap 2 3) x0 = x0 := perm5_swap_in 2 3 0
lemma p_23_x1 : perm5 (swap 2 3) x1 = x1 := perm5_swap_in 2 3 1
lemma p_23_x2 : perm5 (swap 2 3) x2 = x3 := perm5_swap_in 2 3 2
lemma p_23_x3 : perm5 (swap 2 3) x3 = x2 := perm5_swap_in 2 3 3
lemma p_23_x4 : perm5 (swap 2 3) x4 = x4 := perm5_swap_in 2 3 4
lemma p_24_x0 : perm5 (swap 2 4) x0 = x0 := perm5_swap_in 2 4 0
lemma p_24_x1 : perm5 (swap 2 4) x1 = x1 := perm5_swap_in 2 4 1
lemma p_24_x2 : perm5 (swap 2 4) x2 = x4 := perm5_swap_in 2 4 2
lemma p_24_x3 : perm5 (swap 2 4) x3 = x3 := perm5_swap_in 2 4 3
lemma p_24_x4 : perm5 (swap 2 4) x4 = x2 := perm5_swap_in 2 4 4
lemma p_34_x0 : perm5 (swap 3 4) x0 = x0 := perm5_swap_in 3 4 0
lemma p_34_x1 : perm5 (swap 3 4) x1 = x1 := perm5_swap_in 3 4 1
lemma p_34_x2 : perm5 (swap 3 4) x2 = x2 := perm5_swap_in 3 4 2
lemma p_34_x3 : perm5 (swap 3 4) x3 = x4 := perm5_swap_in 3 4 3
lemma p_34_x4 : perm5 (swap 3 4) x4 = x3 := perm5_swap_in 3 4 4
lemma p_02_x0 : perm5 (swap 0 2) x0 = x2 := perm5_swap_in 0 2 0
lemma p_02_x1 : perm5 (swap 0 2) x1 = x1 := perm5_swap_in 0 2 1
lemma p_02_x2 : perm5 (swap 0 2) x2 = x0 := perm5_swap_in 0 2 2
lemma p_02_x3 : perm5 (swap 0 2) x3 = x3 := perm5_swap_in 0 2 3
lemma p_02_x4 : perm5 (swap 0 2) x4 = x4 := perm5_swap_in 0 2 4
lemma p_13_x0 : perm5 (swap 1 3) x0 = x0 := perm5_swap_in 1 3 0
lemma p_13_x1 : perm5 (swap 1 3) x1 = x3 := perm5_swap_in 1 3 1
lemma p_13_x2 : perm5 (swap 1 3) x2 = x2 := perm5_swap_in 1 3 2
lemma p_13_x3 : perm5 (swap 1 3) x3 = x1 := perm5_swap_in 1 3 3
lemma p_13_x4 : perm5 (swap 1 3) x4 = x4 := perm5_swap_in 1 3 4
lemma p_01_x01 : perm5 (swap 0 1) x01 = x01 := by rw [x01, perm5_or, p_01_x0, p_01_x1, BitVec.or_comm]
lemma p_12_x01 : perm5 (swap 1 2) x01 = x02 := by rw [x01, perm5_or, p_12_x0, p_12_x1]; rfl
lemma p_12_x02 : perm5 (swap 1 2) x02 = x01 := by rw [x02, perm5_or, p_12_x0, p_12_x2]; rfl
lemma p_23_x01 : perm5 (swap 2 3) x01 = x01 := by rw [x01, perm5_or, p_23_x0, p_23_x1]
lemma p_24_x01 : perm5 (swap 2 4) x01 = x01 := by rw [x01, perm5_or, p_24_x0, p_24_x1]
lemma p_34_x01 : perm5 (swap 3 4) x01 = x01 := by rw [x01, perm5_or, p_34_x0, p_34_x1]
lemma p_34_x02 : perm5 (swap 3 4) x02 = x02 := by rw [x02, perm5_or, p_34_x0, p_34_x2]
lemma p_01_x23 : perm5 (swap 0 1) x23 = x23 := by rw [x23, perm5_or, p_01_x2, p_01_x3]
lemma p_23_x23 : perm5 (swap 2 3) x23 = x23 := by rw [x23, perm5_or, p_23_x2, p_23_x3, BitVec.or_comm]
lemma p_01_w03_or : perm5 (swap 0 1) w03_or = w03_or := by rw [w03_or, perm5_or, p_01_x01, p_01_x2]
lemma p_34_w03_or : perm5 (swap 3 4) w03_or = w03_or := by rw [w03_or, perm5_or, p_34_x01, p_34_x2]
lemma p_01_w03_an : perm5 (swap 0 1) w03_an = w03_an := by rw [w03_an, perm5_and, perm5_not, p_01_x01, p_01_x2]
lemma p_34_w03_an : perm5 (swap 3 4) w03_an = w03_an := by rw [w03_an, perm5_and, perm5_not, p_34_x01, p_34_x2]
lemma p_0213_x01 : perm5 (swap 1 3) (perm5 (swap 0 2) x01) = x23 := by rw [x01, perm5_or, p_02_x0, p_02_x1, perm5_or, p_13_x2, p_13_x1]; rfl
lemma p_0213_x23 : perm5 (swap 1 3) (perm5 (swap 0 2) x23) = x01 := by rw [x23, perm5_or, p_02_x2, p_02_x3, perm5_or, p_13_x0, p_13_x3]; rfl
lemma p_0213_x0 : perm5 (swap 1 3) (perm5 (swap 0 2) x0) = x2 := by rw [p_02_x0, p_13_x2]
lemma p_0213_x1 : perm5 (swap 1 3) (perm5 (swap 0 2) x1) = x3 := by rw [p_02_x1, p_13_x1]
lemma p_0213_x2 : perm5 (swap 1 3) (perm5 (swap 0 2) x2) = x0 := by rw [p_02_x2, p_13_x0]
lemma p_0213_x3 : perm5 (swap 1 3) (perm5 (swap 0 2) x3) = x1 := by rw [p_02_x3, p_13_x3]
lemma p_0213_x4 : perm5 (swap 1 3) (perm5 (swap 0 2) x4) = x4 := by rw [p_02_x4, p_13_x4]

lemma perm5_swap_g (a b : Fin 5) {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) :
    perm5 (swap a b) g = g := by
  rcases hg with rfl | rfl
  · exact perm5_swap_goal a b
  · rw [perm5_not, perm5_swap_goal]

theorem live_swap5 (a b : Fin 5) {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k : ℕ} {s : Finset W5}
    (hval : ∀ w ∈ s, Valid5 w) (h : live basicOps5 g k s) :
    live basicOps5 g k (s.image (perm5 (swap a b))) := by
  induction k generalizing s with
  | zero =>
    change s = {g} at h
    rw [h, Finset.image_singleton, perm5_swap_g a b hg]
    rfl
  | succ k ih =>
    rcases h with skip | ⟨u, hu, v, hv, huv, z, hz, hout, r, hs, tail⟩
    · exact .inl (ih hval skip)
    · have hvu : Valid5 u := hval u hu
      have hvv : Valid5 v := hval v hv
      have hvz : Valid5 z := valid5_ops hvu hvv hz
      have hne : perm5 (swap a b) u ≠ perm5 (swap a b) v :=
        fun he => huv (perm5_swap_inj a b hvu hvv he)
      have hout' : perm5 (swap a b) z ∉ s.image (perm5 (swap a b)) := by
        intro hm
        obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hm
        exact hout (perm5_swap_inj a b (hval w hw) hvz heq ▸ hw)
      have hval' : ∀ w ∈ insert z r, Valid5 w := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwr
        · exact hvz
        · exact hval w (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwr))
      refine .inr ⟨perm5 (swap a b) u, Finset.mem_image_of_mem _ hu,
        perm5 (swap a b) v, Finset.mem_image_of_mem _ hv, hne,
        perm5 (swap a b) z, perm5_ops _ _ _ _ hz, hout', r.image (perm5 (swap a b)), ?_, ?_⟩
      · rw [hs, Finset.image_insert, Finset.image_insert]
      · simpa only [Finset.image_insert] using ih hval' tail

lemma step_swap5 (a b : Fin 5) {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {k : ℕ}
    {s rest : Finset W5} {u v z : W5}
    (hval : ∀ w ∈ s, Valid5 w) (hz : z ∈ basicOps5 u v) (hzout : z ∉ s)
    (hs : s = insert u (insert v rest)) (tail : live basicOps5 g k (insert z rest)) :
    ∃ (z' : W5) (rest' : Finset W5),
      z' ∈ basicOps5 (perm5 (swap a b) u) (perm5 (swap a b) v) ∧
      z' ∉ s.image (perm5 (swap a b)) ∧
      s.image (perm5 (swap a b)) = insert (perm5 (swap a b) u) (insert (perm5 (swap a b) v) rest') ∧
      live basicOps5 g k (insert z' rest') := by
  have hvu : Valid5 u := hval u (hs ▸ Finset.mem_insert_self _ _)
  have hvv : Valid5 v := hval v (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hvz : Valid5 z := valid5_ops hvu hvv hz
  have hout' : perm5 (swap a b) z ∉ s.image (perm5 (swap a b)) := by
    intro hm
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hm
    exact hzout (perm5_swap_inj a b (hval w hw) hvz heq ▸ hw)
  have hval' : ∀ w ∈ insert z rest, Valid5 w := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hwr
    · exact hvz
    · exact hval w (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwr))
  refine ⟨perm5 (swap a b) z, rest.image (perm5 (swap a b)), perm5_ops _ _ _ _ hz, hout', ?_, ?_⟩
  · rw [hs, Finset.image_insert, Finset.image_insert]
  · simpa only [Finset.image_insert] using live_swap5 a b hg hval' tail

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c03_or_b : (disp5 2 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xf1dd499264992649926000000000ffc0000000 [0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xfe1e8e2388e2388e2380000003ff0000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xcdbb254952549525495000000000003ff00000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xfe1e8e2388e2388e2380000003ff0000000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000]) = false := by decide +kernel

lemma ws_c03_or_b_nd : ([w03_or, x2, x0, x1, x3, x4] : List W5).Nodup := by decide +kernel
lemma ws_c03_or_b_valid : ∀ w ∈ ([w03_or, x2, x0, x1, x3, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([w03_or, x2, x0, x1, x3, x4] : List W5).all valid5B = true)) w hw)
lemma ws_c03_or_b_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws_c03_or_b_nd, Finset.card_singleton] at hc; simp at hc
lemma ws_c03_or_b_inv_01 : ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 0 1)) = ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_01_w03_or, p_01_x2, p_01_x0, p_01_x1, p_01_x3, p_01_x4]; tauto
lemma ws_c03_or_b_inv_34 : ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 3 4)) = ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_34_w03_or, p_34_x2, p_34_x0, p_34_x1, p_34_x3, p_34_x4]; tauto
lemma no_c03_or_b {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 7 ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset)
    (hav : HasAvoid 7 ![1, 1, 1, 0, 0] ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(w03_or, x2), (w03_or, x0), (w03_or, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 6 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x2 :: [x0, x1, x3, x4]) := List.Perm.refl _
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x0 :: [x2, x1, x3, x4]) := (List.perm_middle (l₁ := [x2]) (a := x0) (l₂ := [x1, x3, x4])).cons w03_or
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x3 :: [x2, x0, x1, x4]) := (List.perm_middle (l₁ := [x2, x0, x1]) (a := x3) (l₂ := [x4])).cons w03_or
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x0 :: [w03_or, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_or]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or]) (a := x0) (l₂ := [x1, x3, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x3 :: [w03_or, x0, x1, x4]) := (List.perm_middle (l₁ := [w03_or]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x0, x1]) (a := x3) (l₂ := [x4])).cons x2)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x1 :: [w03_or, x2, x3, x4]) := (List.perm_middle (l₁ := [w03_or, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x2]) (a := x1) (l₂ := [x3, x4])).cons x0)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x3 :: [w03_or, x2, x1, x4]) := (List.perm_middle (l₁ := [w03_or, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x2, x1]) (a := x3) (l₂ := [x4])).cons x0)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x2, x0, x1, x3, x4] : List W5).Perm (x3 :: x4 :: [w03_or, x2, x0, x1]) := (List.perm_middle (l₁ := [w03_or, x2, x0, x1]) (a := x3) (l₂ := [x4])).trans ((List.perm_middle (l₁ := [w03_or, x2, x0, x1]) (a := x4) (l₂ := [])).cons x3)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_or_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.2.symm.trans hdisp)
  rcases first_live (k := 6) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws_c03_or_b_not_goal g hg hend
  have hval : ∀ w ∈ ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset, Valid5 w := fun w hw => ws_c03_or_b_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([w03_or, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([w03_or, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(w03_or, x2), (w03_or, x0), (w03_or, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] ∨ (v, u) ∈ [(w03_or, x2), (w03_or, x0), (w03_or, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      z' ∈ basicOps5 u v → z' ∉ ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset →
      ([w03_or, x2, x0, x1, x3, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 6 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) w03_or) = w03_or := by rw [p_01_w03_or]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) w03_or) = w03_or := by rw [p_34_w03_or]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) w03_or) = w03_or := by rw [p_01_w03_or]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_or_b_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) w03_or) = w03_or := by rw [p_34_w03_or]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_or_b_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c03_or_ab : (disp5 1 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xefff37cdf37cdf37cdf000000000003ffffc00 [0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xf1dd499264992649926000000000ffc0000000 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xffff7fdff7fdff7fdff000000000fffffffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xefff37cdf37cdf37cdf000000000003ffffc00 0xf1dd499264992649926000000000ffc0000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xefff37cdf37cdf37cdf000000000003ffffc00 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xefff37cdf37cdf37cdf000000000003ffffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xfe1e8e2388e2388e2380000003ff0000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xcdbb254952549525495000000000003ff00000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xfe1e8e2388e2388e2380000003ff0000000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xffff7fdff7fdff7fdff000000000fffffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000]) = false := by decide +kernel

lemma ws_c03_or_ab_nd : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Nodup := by decide +kernel
lemma ws_c03_or_ab_valid : ∀ w ∈ ([w03_or, x01, x2, x0, x1, x3, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).all valid5B = true)) w hw)
lemma ws_c03_or_ab_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws_c03_or_ab_nd, Finset.card_singleton] at hc; simp at hc
lemma ws_c03_or_ab_inv_01 : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 0 1)) = ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_01_w03_or, p_01_x01, p_01_x2, p_01_x0, p_01_x1, p_01_x3, p_01_x4]; tauto
lemma ws_c03_or_ab_inv_34 : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 3 4)) = ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_34_w03_or, p_34_x01, p_34_x2, p_34_x0, p_34_x1, p_34_x3, p_34_x4]; tauto
lemma no_c03_or_ab {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 7 ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset)
    (hav : HasAvoid 7 ![1, 1, 1, 0, 0] ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(w03_or, x01), (w03_or, x2), (w03_or, x0), (w03_or, x3), (x01, x2), (x01, x0), (x01, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 6 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x01 :: [x2, x0, x1, x3, x4]) := List.Perm.refl _
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.1.1.1.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x2 :: [x01, x0, x1, x3, x4]) := (List.perm_middle (l₁ := [x01]) (a := x2) (l₂ := [x0, x1, x3, x4])).cons w03_or
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x0 :: [x01, x2, x1, x3, x4]) := (List.perm_middle (l₁ := [x01, x2]) (a := x0) (l₂ := [x1, x3, x4])).cons w03_or
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_or :: x3 :: [x01, x2, x0, x1, x4]) := (List.perm_middle (l₁ := [x01, x2, x0, x1]) (a := x3) (l₂ := [x4])).cons w03_or
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x01 :: x2 :: [w03_or, x0, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_or]) (a := x01) (l₂ := [x2, x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or]) (a := x2) (l₂ := [x0, x1, x3, x4])).cons x01)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x01 :: x0 :: [w03_or, x2, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_or]) (a := x01) (l₂ := [x2, x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x2]) (a := x0) (l₂ := [x1, x3, x4])).cons x01)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x01 :: x3 :: [w03_or, x2, x0, x1, x4]) := (List.perm_middle (l₁ := [w03_or]) (a := x01) (l₂ := [x2, x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x2, x0, x1]) (a := x3) (l₂ := [x4])).cons x01)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x0 :: [w03_or, x01, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_or, x01]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x01]) (a := x0) (l₂ := [x1, x3, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x3 :: [w03_or, x01, x0, x1, x4]) := (List.perm_middle (l₁ := [w03_or, x01]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x01, x0, x1]) (a := x3) (l₂ := [x4])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x1 :: [w03_or, x01, x2, x3, x4]) := (List.perm_middle (l₁ := [w03_or, x01, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x01, x2]) (a := x1) (l₂ := [x3, x4])).cons x0)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x3 :: [w03_or, x01, x2, x1, x4]) := (List.perm_middle (l₁ := [w03_or, x01, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_or, x01, x2, x1]) (a := x3) (l₂ := [x4])).cons x0)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.2.symm.trans hdisp)
    · have hperm : ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).Perm (x3 :: x4 :: [w03_or, x01, x2, x0, x1]) := (List.perm_middle (l₁ := [w03_or, x01, x2, x0, x1]) (a := x3) (l₂ := [x4])).trans ((List.perm_middle (l₁ := [w03_or, x01, x2, x0, x1]) (a := x4) (l₂ := [])).cons x3)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_or_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_or_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.2.symm.trans hdisp)
  rcases first_live (k := 6) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws_c03_or_ab_not_goal g hg hend
  have hval : ∀ w ∈ ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset, Valid5 w := fun w hw => ws_c03_or_ab_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([w03_or, x01, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([w03_or, x01, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(w03_or, x01), (w03_or, x2), (w03_or, x0), (w03_or, x3), (x01, x2), (x01, x0), (x01, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] ∨ (v, u) ∈ [(w03_or, x01), (w03_or, x2), (w03_or, x0), (w03_or, x3), (x01, x2), (x01, x0), (x01, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      z' ∈ basicOps5 u v → z' ∉ ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset →
      ([w03_or, x01, x2, x0, x1, x3, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 6 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) w03_or) = w03_or := by rw [p_01_w03_or]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) w03_or) = w03_or := by rw [p_34_w03_or]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x01) = x01 := by rw [p_01_x01]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x01) = x01 := by rw [p_34_x01]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) w03_or) = w03_or := by rw [p_01_w03_or]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x01) = x01 := by rw [p_01_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_or_ab_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) w03_or) = w03_or := by rw [p_34_w03_or]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x01) = x01 := by rw [p_34_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_or_ab_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_or_ab_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c03_an_b : (disp5 2 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xf1dd499264992649926000000000ffc0000000 [0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xe22364d9364d9364d9000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xfe1e8e2388e2388e2380000003ff0000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xcdbb254952549525495000000000003ff00000 [0xe22364d9364d9364d9000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 2 1 1 1 0 0 (opt5 6) 0xfe1e8e2388e2388e2380000003ff0000000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000]) = false := by decide +kernel

lemma ws_c03_an_b_nd : ([w03_an, x2, x0, x1, x3, x4] : List W5).Nodup := by decide +kernel
lemma ws_c03_an_b_valid : ∀ w ∈ ([w03_an, x2, x0, x1, x3, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([w03_an, x2, x0, x1, x3, x4] : List W5).all valid5B = true)) w hw)
lemma ws_c03_an_b_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws_c03_an_b_nd, Finset.card_singleton] at hc; simp at hc
lemma ws_c03_an_b_inv_01 : ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 0 1)) = ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_01_w03_an, p_01_x2, p_01_x0, p_01_x1, p_01_x3, p_01_x4]; tauto
lemma ws_c03_an_b_inv_34 : ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 3 4)) = ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_34_w03_an, p_34_x2, p_34_x0, p_34_x1, p_34_x3, p_34_x4]; tauto
lemma no_c03_an_b {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 7 ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset)
    (hav : HasAvoid 7 ![1, 1, 1, 0, 0] ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(w03_an, x2), (w03_an, x0), (w03_an, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 6 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x2 :: [x0, x1, x3, x4]) := List.Perm.refl _
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x0 :: [x2, x1, x3, x4]) := (List.perm_middle (l₁ := [x2]) (a := x0) (l₂ := [x1, x3, x4])).cons w03_an
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x3 :: [x2, x0, x1, x4]) := (List.perm_middle (l₁ := [x2, x0, x1]) (a := x3) (l₂ := [x4])).cons w03_an
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x0 :: [w03_an, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_an]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an]) (a := x0) (l₂ := [x1, x3, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x3 :: [w03_an, x0, x1, x4]) := (List.perm_middle (l₁ := [w03_an]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x0, x1]) (a := x3) (l₂ := [x4])).cons x2)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x1 :: [w03_an, x2, x3, x4]) := (List.perm_middle (l₁ := [w03_an, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x2]) (a := x1) (l₂ := [x3, x4])).cons x0)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x3 :: [w03_an, x2, x1, x4]) := (List.perm_middle (l₁ := [w03_an, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x2, x1]) (a := x3) (l₂ := [x4])).cons x0)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x2, x0, x1, x3, x4] : List W5).Perm (x3 :: x4 :: [w03_an, x2, x0, x1]) := (List.perm_middle (l₁ := [w03_an, x2, x0, x1]) (a := x3) (l₂ := [x4])).trans ((List.perm_middle (l₁ := [w03_an, x2, x0, x1]) (a := x4) (l₂ := [])).cons x3)
      have hdisp := disp5_of_step (extra := 2) hg ws_c03_an_b_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_b
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.2.symm.trans hdisp)
  rcases first_live (k := 6) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws_c03_an_b_not_goal g hg hend
  have hval : ∀ w ∈ ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset, Valid5 w := fun w hw => ws_c03_an_b_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([w03_an, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([w03_an, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(w03_an, x2), (w03_an, x0), (w03_an, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] ∨ (v, u) ∈ [(w03_an, x2), (w03_an, x0), (w03_an, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      z' ∈ basicOps5 u v → z' ∉ ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset →
      ([w03_an, x2, x0, x1, x3, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 6 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) w03_an) = w03_an := by rw [p_01_w03_an]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) w03_an) = w03_an := by rw [p_34_w03_an]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) w03_an) = w03_an := by rw [p_01_w03_an]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_an_b_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) w03_an) = w03_an := by rw [p_34_w03_an]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_an_b_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c03_an_ab : (disp5 1 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xefff37cdf37cdf37cdf000000000003ffffc00 [0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xf1dd499264992649926000000000ffc0000000 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xe22364d9364d9364d9000000000003ffffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xefff37cdf37cdf37cdf000000000003ffffc00 0xf1dd499264992649926000000000ffc0000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xefff37cdf37cdf37cdf000000000003ffffc00 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xe22364d9364d9364d9000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xefff37cdf37cdf37cdf000000000003ffffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xe22364d9364d9364d9000000000003ffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xfe1e8e2388e2388e2380000003ff0000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xcdbb254952549525495000000000003ff00000 [0xe22364d9364d9364d9000000000003ffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xab7712c4b12c4b12c4b00000000000000ffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] || disp5 1 1 1 1 0 0 (opt5 6) 0xfe1e8e2388e2388e2380000003ff0000000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xe22364d9364d9364d9000000000003ffffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xf1dd499264992649926000000000ffc0000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000]) = false := by decide +kernel

lemma ws_c03_an_ab_nd : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Nodup := by decide +kernel
lemma ws_c03_an_ab_valid : ∀ w ∈ ([w03_an, x01, x2, x0, x1, x3, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).all valid5B = true)) w hw)
lemma ws_c03_an_ab_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws_c03_an_ab_nd, Finset.card_singleton] at hc; simp at hc
lemma ws_c03_an_ab_inv_01 : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 0 1)) = ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_01_w03_an, p_01_x01, p_01_x2, p_01_x0, p_01_x1, p_01_x3, p_01_x4]; tauto
lemma ws_c03_an_ab_inv_34 : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 3 4)) = ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_34_w03_an, p_34_x01, p_34_x2, p_34_x0, p_34_x1, p_34_x3, p_34_x4]; tauto
lemma no_c03_an_ab {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 7 ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset)
    (hav : HasAvoid 7 ![1, 1, 1, 0, 0] ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(w03_an, x01), (w03_an, x2), (w03_an, x0), (w03_an, x3), (x01, x2), (x01, x0), (x01, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 6 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x01 :: [x2, x0, x1, x3, x4]) := List.Perm.refl _
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.1.1.1.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x2 :: [x01, x0, x1, x3, x4]) := (List.perm_middle (l₁ := [x01]) (a := x2) (l₂ := [x0, x1, x3, x4])).cons w03_an
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x0 :: [x01, x2, x1, x3, x4]) := (List.perm_middle (l₁ := [x01, x2]) (a := x0) (l₂ := [x1, x3, x4])).cons w03_an
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (w03_an :: x3 :: [x01, x2, x0, x1, x4]) := (List.perm_middle (l₁ := [x01, x2, x0, x1]) (a := x3) (l₂ := [x4])).cons w03_an
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x01 :: x2 :: [w03_an, x0, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_an]) (a := x01) (l₂ := [x2, x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an]) (a := x2) (l₂ := [x0, x1, x3, x4])).cons x01)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x01 :: x0 :: [w03_an, x2, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_an]) (a := x01) (l₂ := [x2, x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x2]) (a := x0) (l₂ := [x1, x3, x4])).cons x01)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x01 :: x3 :: [w03_an, x2, x0, x1, x4]) := (List.perm_middle (l₁ := [w03_an]) (a := x01) (l₂ := [x2, x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x2, x0, x1]) (a := x3) (l₂ := [x4])).cons x01)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x0 :: [w03_an, x01, x1, x3, x4]) := (List.perm_middle (l₁ := [w03_an, x01]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x01]) (a := x0) (l₂ := [x1, x3, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x2 :: x3 :: [w03_an, x01, x0, x1, x4]) := (List.perm_middle (l₁ := [w03_an, x01]) (a := x2) (l₂ := [x0, x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x01, x0, x1]) (a := x3) (l₂ := [x4])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x1 :: [w03_an, x01, x2, x3, x4]) := (List.perm_middle (l₁ := [w03_an, x01, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x01, x2]) (a := x1) (l₂ := [x3, x4])).cons x0)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x0 :: x3 :: [w03_an, x01, x2, x1, x4]) := (List.perm_middle (l₁ := [w03_an, x01, x2]) (a := x0) (l₂ := [x1, x3, x4])).trans ((List.perm_middle (l₁ := [w03_an, x01, x2, x1]) (a := x3) (l₂ := [x4])).cons x0)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.1.2.symm.trans hdisp)
    · have hperm : ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).Perm (x3 :: x4 :: [w03_an, x01, x2, x0, x1]) := (List.perm_middle (l₁ := [w03_an, x01, x2, x0, x1]) (a := x3) (l₂ := [x4])).trans ((List.perm_middle (l₁ := [w03_an, x01, x2, x0, x1]) (a := x4) (l₂ := [])).cons x3)
      have hdisp := disp5_of_step (extra := 1) hg ws_c03_an_ab_nd (by decide) hperm hs hz hzout tail hav
      have hchk := chk_c03_an_ab
      simp only [Bool.or_eq_false_iff] at hchk
      exact Bool.noConfusion (hchk.2.symm.trans hdisp)
  rcases first_live (k := 6) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws_c03_an_ab_not_goal g hg hend
  have hval : ∀ w ∈ ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset, Valid5 w := fun w hw => ws_c03_an_ab_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([w03_an, x01, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([w03_an, x01, x2, x0, x1, x3, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(w03_an, x01), (w03_an, x2), (w03_an, x0), (w03_an, x3), (x01, x2), (x01, x0), (x01, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] ∨ (v, u) ∈ [(w03_an, x01), (w03_an, x2), (w03_an, x0), (w03_an, x3), (x01, x2), (x01, x0), (x01, x3), (x2, x0), (x2, x3), (x0, x1), (x0, x3), (x3, x4)] →
      z' ∈ basicOps5 u v → z' ∉ ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset →
      ([w03_an, x01, x2, x0, x1, x3, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 6 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) w03_an) = w03_an := by rw [p_01_w03_an]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) w03_an) = w03_an := by rw [p_34_w03_an]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x01) = x01 := by rw [p_01_x01]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x01) = x01 := by rw [p_34_x01]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) w03_an) = w03_an := by rw [p_01_w03_an]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x01) = x01 := by rw [p_01_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_an_ab_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x3) = x3 := by rw [p_01_x3]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) w03_an) = w03_an := by rw [p_34_w03_an]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x01) = x01 := by rw [p_34_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x0) = x0 := by rw [p_34_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c03_an_ab_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c03_an_ab_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_01_x3]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 3 4) x1)) = x0 := by rw [p_34_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_0 : disp5 2 2 1 1 0 0 (opt5 6) 0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00 0xf1dd499264992649926000000000ffc0000000 [0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_1 : disp5 2 2 1 1 0 0 (opt5 6) 0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00 0xefff37cdf37cdf37cdf000000000003ffffc00 [0xf1dd499264992649926000000000ffc0000000, 0xcdbb254952549525495000000000003ff00000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_2 : disp5 2 2 1 1 0 0 (opt5 6) 0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00 0xcdbb254952549525495000000000003ff00000 [0xf1dd499264992649926000000000ffc0000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_3 : disp5 2 2 1 1 0 0 (opt5 6) 0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00 0xfe1e8e2388e2388e2380000003ff0000000000 [0xf1dd499264992649926000000000ffc0000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_4 : disp5 2 2 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xcdbb254952549525495000000000003ff00000 [0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_5 : disp5 2 2 1 1 0 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xfe1e8e2388e2388e2380000003ff0000000000 [0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c13_or_b_6 : disp5 2 2 1 1 0 0 (opt5 6) 0xfe1e8e2388e2388e2380000003ff0000000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xfbff5bd6f5bd6f5bd6f000000000ffc00ffc00, 0xf1dd499264992649926000000000ffc0000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000] = false := by decide +kernel

lemma ws_c13_or_b_nd : ([x02, x2, x01, x1, x3, x4] : List W5).Nodup := by decide +kernel
lemma ws_c13_or_b_valid : ∀ w ∈ ([x02, x2, x01, x1, x3, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([x02, x2, x01, x1, x3, x4] : List W5).all valid5B = true)) w hw)
lemma ws_c13_or_b_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([x02, x2, x01, x1, x3, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws_c13_or_b_nd, Finset.card_singleton] at hc; simp at hc
lemma ws_c13_or_b_inv_12 : ([x02, x2, x01, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 1 2)) = ([x02, x2, x01, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_12_x02, p_12_x2, p_12_x01, p_12_x1, p_12_x3, p_12_x4]; tauto
lemma ws_c13_or_b_inv_34 : ([x02, x2, x01, x1, x3, x4] : List W5).toFinset.image (perm5 (swap 3 4)) = ([x02, x2, x01, x1, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_34_x02, p_34_x2, p_34_x01, p_34_x1, p_34_x3, p_34_x4]; tauto
lemma no_c13_or_b {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 7 ([x02, x2, x01, x1, x3, x4] : List W5).toFinset)
    (hav : HasAvoid 7 ![2, 1, 1, 0, 0] ([x02, x2, x01, x1, x3, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(x02, x2), (x02, x01), (x02, x1), (x02, x3), (x2, x1), (x2, x3), (x3, x4)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([x02, x2, x01, x1, x3, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([x02, x2, x01, x1, x3, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 6 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x02 :: x2 :: [x01, x1, x3, x4]) := List.Perm.refl _
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_0.symm.trans hdisp)
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x02 :: x01 :: [x2, x1, x3, x4]) := (List.perm_middle (l₁ := [x2]) (a := x01) (l₂ := [x1, x3, x4])).cons x02
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_1.symm.trans hdisp)
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x02 :: x1 :: [x2, x01, x3, x4]) := (List.perm_middle (l₁ := [x2, x01]) (a := x1) (l₂ := [x3, x4])).cons x02
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_2.symm.trans hdisp)
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x02 :: x3 :: [x2, x01, x1, x4]) := (List.perm_middle (l₁ := [x2, x01, x1]) (a := x3) (l₂ := [x4])).cons x02
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_3.symm.trans hdisp)
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x2 :: x1 :: [x02, x01, x3, x4]) := (List.perm_middle (l₁ := [x02]) (a := x2) (l₂ := [x01, x1, x3, x4])).trans ((List.perm_middle (l₁ := [x02, x01]) (a := x1) (l₂ := [x3, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_4.symm.trans hdisp)
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x2 :: x3 :: [x02, x01, x1, x4]) := (List.perm_middle (l₁ := [x02]) (a := x2) (l₂ := [x01, x1, x3, x4])).trans ((List.perm_middle (l₁ := [x02, x01, x1]) (a := x3) (l₂ := [x4])).cons x2)
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_5.symm.trans hdisp)
    · have hperm : ([x02, x2, x01, x1, x3, x4] : List W5).Perm (x3 :: x4 :: [x02, x2, x01, x1]) := (List.perm_middle (l₁ := [x02, x2, x01, x1]) (a := x3) (l₂ := [x4])).trans ((List.perm_middle (l₁ := [x02, x2, x01, x1]) (a := x4) (l₂ := [])).cons x3)
      have hdisp := disp5_of_step (extra := 2) hg ws_c13_or_b_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c13_or_b_6.symm.trans hdisp)
  rcases first_live (k := 6) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws_c13_or_b_not_goal g hg hend
  have hval : ∀ w ∈ ([x02, x2, x01, x1, x3, x4] : List W5).toFinset, Valid5 w := fun w hw => ws_c13_or_b_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([x02, x2, x01, x1, x3, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([x02, x2, x01, x1, x3, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(x02, x2), (x02, x01), (x02, x1), (x02, x3), (x2, x1), (x2, x3), (x3, x4)] ∨ (v, u) ∈ [(x02, x2), (x02, x01), (x02, x1), (x02, x3), (x2, x1), (x2, x3), (x3, x4)] →
      z' ∈ basicOps5 u v → z' ∉ ([x02, x2, x01, x1, x3, x4] : List W5).toFinset →
      ([x02, x2, x01, x1, x3, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 6 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x02) = x02 := by rw [p_34_x02]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x2) = x1 := by rw [p_12_x2]
    have hfb : (perm5 (swap 1 2) x01) = x02 := by rw [p_12_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x01) = x02 := by rw [p_12_x01]
    have hfb : (perm5 (swap 1 2) x2) = x1 := by rw [p_12_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x01) = x02 := by rw [p_12_x01]
    have hfb : (perm5 (swap 1 2) x1) = x2 := by rw [p_12_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x01) = x02 := by rw [p_12_x01]
    have hfb : (perm5 (swap 1 2) x3) = x3 := by rw [p_12_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 2 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c13_or_b_inv_12] at hzout1 hs1
    have hfa : (perm5 (swap 1 2) (perm5 (swap 3 4) x01)) = x02 := by rw [p_34_x01, p_12_x01]
    have hfb : (perm5 (swap 1 2) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_12_x3]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x1) = x2 := by rw [p_12_x1]
    have hfb : (perm5 (swap 1 2) x01) = x02 := by rw [p_12_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x1) = x2 := by rw [p_12_x1]
    have hfb : (perm5 (swap 1 2) x3) = x3 := by rw [p_12_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 2 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c13_or_b_inv_12] at hzout1 hs1
    have hfa : (perm5 (swap 1 2) (perm5 (swap 3 4) x1)) = x2 := by rw [p_34_x1, p_12_x1]
    have hfb : (perm5 (swap 1 2) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_12_x3]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x3) = x3 := by rw [p_12_x3]
    have hfb : (perm5 (swap 1 2) x01) = x02 := by rw [p_12_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 1 2 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_12] at hzout0 hs0
    have hfa : (perm5 (swap 1 2) x3) = x3 := by rw [p_12_x3]
    have hfb : (perm5 (swap 1 2) x1) = x2 := by rw [p_12_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x02) = x02 := by rw [p_34_x02]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 2 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c13_or_b_inv_12] at hzout1 hs1
    have hfa : (perm5 (swap 1 2) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_12_x3]
    have hfb : (perm5 (swap 1 2) (perm5 (swap 3 4) x01)) = x02 := by rw [p_34_x01, p_12_x01]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws_c13_or_b_inv_34] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 2 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c13_or_b_inv_12] at hzout1 hs1
    have hfa : (perm5 (swap 1 2) (perm5 (swap 3 4) x4)) = x3 := by rw [p_34_x4, p_12_x3]
    have hfb : (perm5 (swap 1 2) (perm5 (swap 3 4) x1)) = x2 := by rw [p_34_x1, p_12_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_0 : disp5 1 1 1 1 1 0 (opt5 6) 0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000 0xf1dd499264992649926000000000ffc0000000 [0xfe1e8e2388e2388e2380000003ff0000000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_1 : disp5 1 1 1 1 1 0 (opt5 6) 0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000 0xefff37cdf37cdf37cdf000000000003ffffc00 [0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_2 : disp5 1 1 1 1 1 0 (opt5 6) 0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_3 : disp5 1 1 1 1 1 0 (opt5 6) 0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xf1dd499264992649926000000000ffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_4 : disp5 1 1 1 1 1 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xfe1e8e2388e2388e2380000003ff0000000000 [0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_5 : disp5 1 1 1 1 1 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xab7712c4b12c4b12c4b00000000000000ffc00 [0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xcdbb254952549525495000000000003ff00000, 0xffe0f03c0f03c0f03c00000ffc000000000000] = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem chk_c34_or_ab_6 : disp5 1 1 1 1 1 0 (opt5 6) 0xf1dd499264992649926000000000ffc0000000 0xffe0f03c0f03c0f03c00000ffc000000000000 [0xffdfcfb3ecfb3ecfb3e0000003ffffc0000000, 0xfe1e8e2388e2388e2380000003ff0000000000, 0xefff37cdf37cdf37cdf000000000003ffffc00, 0xab7712c4b12c4b12c4b00000000000000ffc00, 0xcdbb254952549525495000000000003ff00000] = false := by decide +kernel

lemma ws_c34_or_ab_nd : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Nodup := by decide +kernel
lemma ws_c34_or_ab_valid : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([x23, x2, x3, x01, x0, x1, x4] : List W5).all valid5B = true)) w hw)
lemma ws_c34_or_ab_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws_c34_or_ab_nd, Finset.card_singleton] at hc; simp at hc
lemma ws_c34_or_ab_inv_01 : ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 1)) = ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_01_x23, p_01_x2, p_01_x3, p_01_x01, p_01_x0, p_01_x1, p_01_x4]; tauto
lemma ws_c34_or_ab_inv_23 : ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 2 3)) = ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_23_x23, p_23_x2, p_23_x3, p_23_x01, p_23_x0, p_23_x1, p_23_x4]; tauto
lemma ws_c34_or_ab_inv_0213 : (([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2))).image (perm5 (swap 1 3)) = ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_0213_x23, p_0213_x2, p_0213_x3, p_0213_x01, p_0213_x0, p_0213_x1, p_0213_x4]; tauto
lemma no_c34_or_ab {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 7 ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset)
    (hav : HasAvoid 7 ![1, 1, 1, 1, 0] ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(x23, x2), (x23, x01), (x23, x0), (x23, x4), (x2, x3), (x2, x0), (x2, x4)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 6 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x23 :: x2 :: [x3, x01, x0, x1, x4]) := List.Perm.refl _
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_0.symm.trans hdisp)
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x23 :: x01 :: [x2, x3, x0, x1, x4]) := (List.perm_middle (l₁ := [x2, x3]) (a := x01) (l₂ := [x0, x1, x4])).cons x23
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_1.symm.trans hdisp)
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x23 :: x0 :: [x2, x3, x01, x1, x4]) := (List.perm_middle (l₁ := [x2, x3, x01]) (a := x0) (l₂ := [x1, x4])).cons x23
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_2.symm.trans hdisp)
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x23 :: x4 :: [x2, x3, x01, x0, x1]) := (List.perm_middle (l₁ := [x2, x3, x01, x0, x1]) (a := x4) (l₂ := [])).cons x23
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_3.symm.trans hdisp)
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x2 :: x3 :: [x23, x01, x0, x1, x4]) := (List.perm_middle (l₁ := [x23]) (a := x2) (l₂ := [x3, x01, x0, x1, x4])).trans ((List.perm_middle (l₁ := [x23]) (a := x3) (l₂ := [x01, x0, x1, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_4.symm.trans hdisp)
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x2 :: x0 :: [x23, x3, x01, x1, x4]) := (List.perm_middle (l₁ := [x23]) (a := x2) (l₂ := [x3, x01, x0, x1, x4])).trans ((List.perm_middle (l₁ := [x23, x3, x01]) (a := x0) (l₂ := [x1, x4])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_5.symm.trans hdisp)
    · have hperm : ([x23, x2, x3, x01, x0, x1, x4] : List W5).Perm (x2 :: x4 :: [x23, x3, x01, x0, x1]) := (List.perm_middle (l₁ := [x23]) (a := x2) (l₂ := [x3, x01, x0, x1, x4])).trans ((List.perm_middle (l₁ := [x23, x3, x01, x0, x1]) (a := x4) (l₂ := [])).cons x2)
      have hdisp := disp5_of_step (extra := 1) hg ws_c34_or_ab_nd (by decide) hperm hs hz hzout tail hav
      exact Bool.noConfusion (chk_c34_or_ab_6.symm.trans hdisp)
  rcases first_live (k := 6) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws_c34_or_ab_not_goal g hg hend
  have hval : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset, Valid5 w := fun w hw => ws_c34_or_ab_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(x23, x2), (x23, x01), (x23, x0), (x23, x4), (x2, x3), (x2, x0), (x2, x4)] ∨ (v, u) ∈ [(x23, x2), (x23, x01), (x23, x0), (x23, x4), (x2, x3), (x2, x0), (x2, x4)] →
      z' ∈ basicOps5 u v → z' ∉ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset →
      ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 6 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x23) = x23 := by rw [p_23_x23]
    have hfb : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x23) = x23 := by rw [p_01_x23]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x2)) = x0 := by rw [p_0213_x2]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x01)) = x23 := by rw [p_0213_x01]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 2 3 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_23] at hzout2 hs2
    have hfa : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x2))) = x0 := by rw [p_0213_x2, p_23_x0]
    have hfb : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x1))) = x2 := by rw [p_0213_x1, p_23_x3]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inr (by simp)) hz2 hzout2 hs2 tail2
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    have hfb : (perm5 (swap 2 3) x23) = x23 := by rw [p_23_x23]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 0 1 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_01] at hzout2 hs2
    have hfa : (perm5 (swap 0 1) (perm5 (swap 1 3) (perm5 (swap 0 2) x3))) = x0 := by rw [p_0213_x3, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 1 3) (perm5 (swap 0 2) x01))) = x23 := by rw [p_0213_x01, p_01_x23]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inr (by simp)) hz2 hzout2 hs2 tail2
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    have hfb : (perm5 (swap 2 3) x0) = x0 := by rw [p_23_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 2 3) x3)) = x2 := by rw [p_23_x3, p_01_x2]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 2 3) x1)) = x0 := by rw [p_23_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    have hfb : (perm5 (swap 2 3) x4) = x4 := by rw [p_23_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x01)) = x23 := by rw [p_0213_x01]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x2)) = x0 := by rw [p_0213_x2]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 0 1 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_01] at hzout2 hs2
    have hfa : (perm5 (swap 0 1) (perm5 (swap 1 3) (perm5 (swap 0 2) x01))) = x23 := by rw [p_0213_x01, p_01_x23]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 1 3) (perm5 (swap 0 2) x3))) = x0 := by rw [p_0213_x3, p_01_x1]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inl (by simp)) hz2 hzout2 hs2 tail2
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x01)) = x23 := by rw [p_0213_x01]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x0)) = x2 := by rw [p_0213_x0]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 2 3 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_23] at hzout2 hs2
    have hfa : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x01))) = x23 := by rw [p_0213_x01, p_23_x23]
    have hfb : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x1))) = x2 := by rw [p_0213_x1, p_23_x3]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inl (by simp)) hz2 hzout2 hs2 tail2
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x01)) = x23 := by rw [p_0213_x01]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x4)) = x4 := by rw [p_0213_x4]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x0) = x0 := by rw [p_23_x0]
    have hfb : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x0)) = x2 := by rw [p_0213_x0]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x01)) = x23 := by rw [p_0213_x01]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x0)) = x2 := by rw [p_0213_x0]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x1)) = x3 := by rw [p_0213_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x0)) = x2 := by rw [p_0213_x0]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x4)) = x4 := by rw [p_0213_x4]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x23) = x23 := by rw [p_01_x23]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 2 3 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_23] at hzout2 hs2
    have hfa : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x1))) = x2 := by rw [p_0213_x1, p_23_x3]
    have hfb : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x2))) = x0 := by rw [p_0213_x2, p_23_x0]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inl (by simp)) hz2 hzout2 hs2 tail2
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 2 3) x1)) = x0 := by rw [p_23_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 2 3) x3)) = x2 := by rw [p_23_x3, p_01_x2]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 2 3 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_23] at hzout2 hs2
    have hfa : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x1))) = x2 := by rw [p_0213_x1, p_23_x3]
    have hfb : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x01))) = x23 := by rw [p_0213_x01, p_23_x23]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inr (by simp)) hz2 hzout2 hs2 tail2
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x1)) = x3 := by rw [p_0213_x1]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x0)) = x2 := by rw [p_0213_x0]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 2 3 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_23] at hzout2 hs2
    have hfa : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x1))) = x2 := by rw [p_0213_x1, p_23_x3]
    have hfb : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x4))) = x4 := by rw [p_0213_x4, p_23_x4]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inl (by simp)) hz2 hzout2 hs2 tail2
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws_c34_or_ab_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x4) = x4 := by rw [p_23_x4]
    have hfb : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x4)) = x4 := by rw [p_0213_x4]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x01)) = x23 := by rw [p_0213_x01]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    have hfa : (perm5 (swap 1 3) (perm5 (swap 0 2) x4)) = x4 := by rw [p_0213_x4]
    have hfb : (perm5 (swap 1 3) (perm5 (swap 0 2) x0)) = x2 := by rw [p_0213_x0]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 2 hg hval hz hzout hs tail
    have hval0 : ∀ w ∈ ([x23, x2, x3, x01, x0, x1, x4] : List W5).toFinset.image (perm5 (swap 0 2)), Valid5 w := fun w hw => by obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw; exact perm5_valid 0 2 u
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 1 3 hg hval0 hz0 hzout0 hs0 tail0
    rw [ws_c34_or_ab_inv_0213] at hzout1 hs1
    obtain ⟨z2, r2, hz2, hzout2, hs2, tail2⟩ := step_swap5 2 3 hg hval hz1 hzout1 hs1 tail1
    rw [ws_c34_or_ab_inv_23] at hzout2 hs2
    have hfa : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x4))) = x4 := by rw [p_0213_x4, p_23_x4]
    have hfb : (perm5 (swap 2 3) (perm5 (swap 1 3) (perm5 (swap 0 2) x1))) = x2 := by rw [p_0213_x1, p_23_x3]
    rw [hfa, hfb] at hz2 hs2
    exact hstep_sym _ _ z2 r2 (.inr (by simp)) hz2 hzout2 hs2 tail2
  · exact hab rfl

lemma ws1_nd : ([x01, x0, x1, x2, x3, x4] : List W5).Nodup := by decide +kernel
lemma ws1_valid : ∀ w ∈ ([x01, x0, x1, x2, x3, x4] : List W5), Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : ([x01, x0, x1, x2, x3, x4] : List W5).all valid5B = true)) w hw)
lemma ws1_not_goal : ∀ g : W5, (g = goal5 ∨ g = ~~~goal5) → ([x01, x0, x1, x2, x3, x4] : List W5).toFinset ≠ {g} := by
  intro g _ heq; have hc := congrArg Finset.card heq; rw [List.toFinset_card_of_nodup ws1_nd, Finset.card_singleton] at hc; simp at hc
lemma ws1_inv_01 : ([x01, x0, x1, x2, x3, x4] : List W5).toFinset.image (perm5 (swap 0 1)) = ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_01_x01, p_01_x0, p_01_x1, p_01_x2, p_01_x3, p_01_x4]; tauto
lemma ws1_inv_23 : ([x01, x0, x1, x2, x3, x4] : List W5).toFinset.image (perm5 (swap 2 3)) = ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_23_x01, p_23_x0, p_23_x1, p_23_x2, p_23_x3, p_23_x4]; tauto
lemma ws1_inv_24 : ([x01, x0, x1, x2, x3, x4] : List W5).toFinset.image (perm5 (swap 2 4)) = ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_24_x01, p_24_x0, p_24_x1, p_24_x2, p_24_x3, p_24_x4]; tauto
lemma ws1_inv_34 : ([x01, x0, x1, x2, x3, x4] : List W5).toFinset.image (perm5 (swap 3 4)) = ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
  ext w; simp only [List.toFinset_cons, List.toFinset_nil, Finset.image_insert, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false, p_34_x01, p_34_x0, p_34_x1, p_34_x2, p_34_x3, p_34_x4]; tauto
lemma no_ws1 {g : W5} (hg : g = goal5 ∨ g = ~~~goal5)
    (hl : live basicOps5 g 8 ([x01, x0, x1, x2, x3, x4] : List W5).toFinset)
    (hav : HasAvoid 8 ![1, 1, 0, 0, 0] ([x01, x0, x1, x2, x3, x4] : List W5).toFinset) : False := by
  have hstep : ∀ a b : W5, (a, b) ∈ [(x01, x0), (x01, x2), (x0, x1), (x0, x2), (x2, x3)] →
      ∀ z ∈ basicOps5 a b, z ∉ ([x01, x0, x1, x2, x3, x4] : List W5).toFinset → ∀ rest : Finset W5,
      ([x01, x0, x1, x2, x3, x4] : List W5).toFinset = insert a (insert b rest) →
      live basicOps5 g 7 (insert z rest) → False := by
    intro a b hab z hz hzout rest hs tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hperm : ([x01, x0, x1, x2, x3, x4] : List W5).Perm (x01 :: x0 :: [x1, x2, x3, x4]) := List.Perm.refl _
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 hperm ws1_nd hs
      have hznew : z ∉ kept := fun hu => hzout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl' : live basicOps5 g 7 (z :: kept).toFinset := by simpa [hfin] using tail
      have hav' : HasAvoid 7 ![2, 1, 0, 0, 0] (z :: kept).toFinset := by
        have hsub : (z :: kept).toFinset ⊆ insert z ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
          intro u hu; rcases Finset.mem_insert.mp (by simpa [hfin] using hu) with rfl | hr
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
        have hstep_av := hasAvoid_step (k := 7) hav (List.mem_toFinset.mpr (by simp)) (List.mem_toFinset.mpr (by simp)) hz hsub
        have hseq : (fun i : Fin 5 => (![1, 1, 0, 0, 0] : Fin 5 → ℕ) i + if isC (mask5 i).toNat x01.toNat || isC (mask5 i).toNat x0.toNat then 1 else 0) = ![2, 1, 0, 0, 0] := by
          funext i; fin_cases i <;> decide +kernel
        rwa [hseq] at hstep_av
      simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [keepChoices5, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hz with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
    · have hperm : ([x01, x0, x1, x2, x3, x4] : List W5).Perm (x01 :: x2 :: [x0, x1, x3, x4]) := (List.perm_middle (l₁ := [x0, x1]) (a := x2) (l₂ := [x3, x4])).cons x01
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 hperm ws1_nd hs
      have hznew : z ∉ kept := fun hu => hzout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl' : live basicOps5 g 7 (z :: kept).toFinset := by simpa [hfin] using tail
      have hav' : HasAvoid 7 ![1, 1, 1, 0, 0] (z :: kept).toFinset := by
        have hsub : (z :: kept).toFinset ⊆ insert z ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
          intro u hu; rcases Finset.mem_insert.mp (by simpa [hfin] using hu) with rfl | hr
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
        have hstep_av := hasAvoid_step (k := 7) hav (List.mem_toFinset.mpr (by simp)) (List.mem_toFinset.mpr (by simp)) hz hsub
        have hseq : (fun i : Fin 5 => (![1, 1, 0, 0, 0] : Fin 5 → ℕ) i + if isC (mask5 i).toNat x01.toNat || isC (mask5 i).toNat x2.toNat then 1 else 0) = ![1, 1, 1, 0, 0] := by
          funext i; fin_cases i <;> decide +kernel
        rwa [hseq] at hstep_av
      simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [keepChoices5, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hz with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact no_c03_or_b hg hl' hav'
      · exact no_c03_or_ab hg hl' hav'
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact no_c03_an_b hg hl' hav'
      · exact no_c03_an_ab hg hl' hav'
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
    · have hperm : ([x01, x0, x1, x2, x3, x4] : List W5).Perm (x0 :: x1 :: [x01, x2, x3, x4]) := (List.perm_middle (l₁ := [x01]) (a := x0) (l₂ := [x1, x2, x3, x4])).trans ((List.perm_middle (l₁ := [x01]) (a := x1) (l₂ := [x2, x3, x4])).cons x0)
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 hperm ws1_nd hs
      have hznew : z ∉ kept := fun hu => hzout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl' : live basicOps5 g 7 (z :: kept).toFinset := by simpa [hfin] using tail
      have hav' : HasAvoid 7 ![2, 2, 0, 0, 0] (z :: kept).toFinset := by
        have hsub : (z :: kept).toFinset ⊆ insert z ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
          intro u hu; rcases Finset.mem_insert.mp (by simpa [hfin] using hu) with rfl | hr
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
        have hstep_av := hasAvoid_step (k := 7) hav (List.mem_toFinset.mpr (by simp)) (List.mem_toFinset.mpr (by simp)) hz hsub
        have hseq : (fun i : Fin 5 => (![1, 1, 0, 0, 0] : Fin 5 → ℕ) i + if isC (mask5 i).toNat x0.toNat || isC (mask5 i).toNat x1.toNat then 1 else 0) = ![2, 2, 0, 0, 0] := by
          funext i; fin_cases i <;> decide +kernel
        rwa [hseq] at hstep_av
      simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [keepChoices5, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hz with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact hzout (List.mem_toFinset.mpr (by decide))
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
    · have hperm : ([x01, x0, x1, x2, x3, x4] : List W5).Perm (x0 :: x2 :: [x01, x1, x3, x4]) := (List.perm_middle (l₁ := [x01]) (a := x0) (l₂ := [x1, x2, x3, x4])).trans ((List.perm_middle (l₁ := [x01, x1]) (a := x2) (l₂ := [x3, x4])).cons x0)
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 hperm ws1_nd hs
      have hznew : z ∉ kept := fun hu => hzout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl' : live basicOps5 g 7 (z :: kept).toFinset := by simpa [hfin] using tail
      have hav' : HasAvoid 7 ![2, 1, 1, 0, 0] (z :: kept).toFinset := by
        have hsub : (z :: kept).toFinset ⊆ insert z ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
          intro u hu; rcases Finset.mem_insert.mp (by simpa [hfin] using hu) with rfl | hr
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
        have hstep_av := hasAvoid_step (k := 7) hav (List.mem_toFinset.mpr (by simp)) (List.mem_toFinset.mpr (by simp)) hz hsub
        have hseq : (fun i : Fin 5 => (![1, 1, 0, 0, 0] : Fin 5 → ℕ) i + if isC (mask5 i).toNat x0.toNat || isC (mask5 i).toNat x2.toNat then 1 else 0) = ![2, 1, 1, 0, 0] := by
          funext i; fin_cases i <;> decide +kernel
        rwa [hseq] at hstep_av
      simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [keepChoices5, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hz with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact no_c13_or_b hg hl' hav'
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
    · have hperm : ([x01, x0, x1, x2, x3, x4] : List W5).Perm (x2 :: x3 :: [x01, x0, x1, x4]) := (List.perm_middle (l₁ := [x01, x0, x1]) (a := x2) (l₂ := [x3, x4])).trans ((List.perm_middle (l₁ := [x01, x0, x1]) (a := x3) (l₂ := [x4])).cons x2)
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept5 hperm ws1_nd hs
      have hznew : z ∉ kept := fun hu => hzout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl' : live basicOps5 g 7 (z :: kept).toFinset := by simpa [hfin] using tail
      have hav' : HasAvoid 7 ![1, 1, 1, 1, 0] (z :: kept).toFinset := by
        have hsub : (z :: kept).toFinset ⊆ insert z ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
          intro u hu; rcases Finset.mem_insert.mp (by simpa [hfin] using hu) with rfl | hr
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
        have hstep_av := hasAvoid_step (k := 7) hav (List.mem_toFinset.mpr (by simp)) (List.mem_toFinset.mpr (by simp)) hz hsub
        have hseq : (fun i : Fin 5 => (![1, 1, 0, 0, 0] : Fin 5 → ℕ) i + if isC (mask5 i).toNat x2.toNat || isC (mask5 i).toNat x3.toNat then 1 else 0) = ![1, 1, 1, 1, 0] := by
          funext i; fin_cases i <;> decide +kernel
        rwa [hseq] at hstep_av
      simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [keepChoices5, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hz with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact no_c34_or_ab hg hl' hav'
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (cuts5_full hg hl') (by decide +kernel)
      · exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
  rcases first_live (k := 7) hl with hend | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, hs, tail⟩
  · exact ws1_not_goal g hg hend
  have hval : ∀ w ∈ ([x01, x0, x1, x2, x3, x4] : List W5).toFinset, Valid5 w := fun w hw => ws1_valid w (List.mem_toFinset.mp hw)
  have ha' : a ∈ ([x01, x0, x1, x2, x3, x4] : List W5) := List.mem_toFinset.mp ha
  have hb' : b ∈ ([x01, x0, x1, x2, x3, x4] : List W5) := List.mem_toFinset.mp hb
  have hstep_sym : ∀ (u v : W5) (z' : W5) (rest' : Finset W5),
      (u, v) ∈ [(x01, x0), (x01, x2), (x0, x1), (x0, x2), (x2, x3)] ∨ (v, u) ∈ [(x01, x0), (x01, x2), (x0, x1), (x0, x2), (x2, x3)] →
      z' ∈ basicOps5 u v → z' ∉ ([x01, x0, x1, x2, x3, x4] : List W5).toFinset →
      ([x01, x0, x1, x2, x3, x4] : List W5).toFinset = insert u (insert v rest') →
      live basicOps5 g 7 (insert z' rest') → False := by
    intro u v z' rest' huv hz' hzout' hs' tail'
    rcases huv with h | h
    · exact hstep u v h z' hz' hzout' rest' hs' tail'
    · exact hstep v u h z' (ops5_swap u v ▸ hz') hzout' rest' (by rw [hs', Finset.insert_comm]) tail'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws1_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x01) = x01 := by rw [p_01_x01]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws1_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x01) = x01 := by rw [p_23_x01]
    have hfb : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    have hfa : (perm5 (swap 2 4) x01) = x01 := by rw [p_24_x01]
    have hfb : (perm5 (swap 2 4) x4) = x2 := by rw [p_24_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws1_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x0) = x0 := by rw [p_23_x0]
    have hfb : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    have hfa : (perm5 (swap 2 4) x0) = x0 := by rw [p_24_x0]
    have hfb : (perm5 (swap 2 4) x4) = x2 := by rw [p_24_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws1_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x01) = x01 := by rw [p_01_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws1_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    have hfb : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws1_inv_23] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws1_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 2 3) x1)) = x0 := by rw [p_23_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 2 3) x3)) = x2 := by rw [p_23_x3, p_01_x2]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws1_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 2 4) x1)) = x0 := by rw [p_24_x1, p_01_x1]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 2 4) x4)) = x2 := by rw [p_24_x4, p_01_x2]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inl (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 0 1 hg hval hz hzout hs tail
    rw [ws1_inv_01] at hzout0 hs0
    have hfa : (perm5 (swap 0 1) x2) = x2 := by rw [p_01_x2]
    have hfb : (perm5 (swap 0 1) x1) = x0 := by rw [p_01_x1]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl
  · exact hstep_sym _ _ z rest (.inl (by simp)) hz hzout hs tail
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws1_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    have hfb : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws1_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    have hfb : (perm5 (swap 2 3) x01) = x01 := by rw [p_23_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws1_inv_23] at hzout0 hs0
    have hfa : (perm5 (swap 2 3) x3) = x2 := by rw [p_23_x3]
    have hfb : (perm5 (swap 2 3) x0) = x0 := by rw [p_23_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 3 hg hval hz hzout hs tail
    rw [ws1_inv_23] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws1_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 2 3) x3)) = x2 := by rw [p_23_x3, p_01_x2]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 2 3) x1)) = x0 := by rw [p_23_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  · exact hstep_sym _ _ z rest (.inr (by simp)) hz hzout hs tail
  · exact hab rfl
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    have hfa : (perm5 (swap 2 4) x3) = x3 := by rw [p_24_x3]
    have hfb : (perm5 (swap 2 4) x4) = x2 := by rw [p_24_x4]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    have hfa : (perm5 (swap 2 4) x4) = x2 := by rw [p_24_x4]
    have hfb : (perm5 (swap 2 4) x01) = x01 := by rw [p_24_x01]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    have hfa : (perm5 (swap 2 4) x4) = x2 := by rw [p_24_x4]
    have hfb : (perm5 (swap 2 4) x0) = x0 := by rw [p_24_x0]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 0 1 hg hval hz0 hzout0 hs0 tail0
    rw [ws1_inv_01] at hzout1 hs1
    have hfa : (perm5 (swap 0 1) (perm5 (swap 2 4) x4)) = x2 := by rw [p_24_x4, p_01_x2]
    have hfb : (perm5 (swap 0 1) (perm5 (swap 2 4) x1)) = x0 := by rw [p_24_x1, p_01_x1]
    rw [hfa, hfb] at hz1 hs1
    exact hstep_sym _ _ z1 r1 (.inr (by simp)) hz1 hzout1 hs1 tail1
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 3 4 hg hval hz hzout hs tail
    rw [ws1_inv_34] at hzout0 hs0
    have hfa : (perm5 (swap 3 4) x4) = x3 := by rw [p_34_x4]
    have hfb : (perm5 (swap 3 4) x2) = x2 := by rw [p_34_x2]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inr (by simp)) hz0 hzout0 hs0 tail0
  ·
    obtain ⟨z0, r0, hz0, hzout0, hs0, tail0⟩ := step_swap5 2 4 hg hval hz hzout hs tail
    rw [ws1_inv_24] at hzout0 hs0
    have hfa : (perm5 (swap 2 4) x4) = x2 := by rw [p_24_x4]
    have hfb : (perm5 (swap 2 4) x3) = x3 := by rw [p_24_x3]
    rw [hfa, hfb] at hz0 hs0
    exact hstep_sym _ _ z0 r0 (.inl (by simp)) hz0 hzout0 hs0 tail0
  · exact hab rfl

lemma in5_valid : ∀ w ∈ in5, Valid5 w := fun w hw => valid5_of_valid5B ((List.all_eq_true.mp (by decide +kernel : in5.all valid5B = true)) w hw)

lemma in5_not_goal : ∀ i : Fin 5, vinput5 i ≠ goal5 ∧ vinput5 i ≠ ~~~goal5 := by decide +kernel

lemma in5_index : ∀ w ∈ in5, ∃ i : Fin 5, vinput5 i = w := by
  intro w hw
  simp only [in5, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

lemma sep_after_01 : ∀ (op : Fin 4) (q : Fin 5), ∃ p : Fin 76,
    ¬ differs5 p ((ops5 x0 x1).getD op.val 0) ∧
    ∀ r : Fin 5, r ≠ q → ¬ differs5 p (vinput5 r) := by
  unfold differs5; decide +kernel

lemma live_after_01 {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {z : W5}
    (hz : z ∈ basicOps5 x0 x1) {rest : Finset W5} (hsub : rest ⊆ in5.toFinset)
    (hl : live basicOps5 g 8 (insert z rest)) : ∀ q : Fin 5, vinput5 q ∈ rest := by
  intro q
  have ⟨o, ho⟩ : ∃ o : Fin 4, (ops5 x0 x1).getD o.val 0 = z := by
    simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  obtain ⟨p, hpz, hpr⟩ := sep_after_01 o q
  rw [ho] at hpz
  have hdg : ∀ r : Fin 76, differs5 r g := by rcases hg with rfl | rfl <;> unfold differs5 <;> decide +kernel
  obtain ⟨w, hw, hdw⟩ := live_separates (differs5 p) (hdg p) (ops5_differs p) hl
  rcases Finset.mem_insert.mp hw with rfl | hwr
  · exact False.elim (hpz hdw)
  · obtain ⟨r, rfl⟩ := in5_index w (List.mem_toFinset.mp (hsub hwr))
    by_cases hrq : r = q
    · subst hrq; exact hwr
    · exact False.elim (hpr r hrq hdw)

theorem no_nine_k5_01 {g : W5} (hg : g = goal5 ∨ g = ~~~goal5) {s rest : Finset W5}
    (hsub : s ⊆ in5.toFinset) {z : W5} (hz : z ∈ basicOps5 x0 x1)
    (hs : s = insert x0 (insert x1 rest)) (tail : live basicOps5 g 8 (insert z rest)) : False := by
  have hrest_sub : rest ⊆ in5.toFinset := fun u hu => hsub (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
  have hall := live_after_01 hg hz hrest_sub tail
  have hrest_eq : rest = in5.toFinset := by
    apply Finset.Subset.antisymm hrest_sub
    intro w hw
    obtain ⟨q, rfl⟩ := in5_index w (List.mem_toFinset.mp hw)
    exact hall q
  rw [hrest_eq] at tail
  have hav0 : HasAvoid 9 (fun _ => 0) in5.toFinset := hasAvoid_init (Finset.Subset.refl _)
  have hav1 := hasAvoid_step (k := 8) hav0 (List.mem_toFinset.mpr (by simp [in5])) (List.mem_toFinset.mpr (by simp [in5]))
    hz (Finset.Subset.refl _)
  have hseq : (fun i : Fin 5 => (0 : ℕ) + if isC (mask5 i).toNat x0.toNat || isC (mask5 i).toNat x1.toNat then 1 else 0) = ![1, 1, 0, 0, 0] := by
    funext i; fin_cases i <;> decide +kernel
  rw [hseq] at hav1
  simp only [basicOps5, ops5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · have hnd : ((x0 &&& x1) :: in5).Nodup := by decide +kernel
    have hl' : live basicOps5 g 8 ((x0 &&& x1) :: in5).toFinset := by simpa using tail
    have hav' : HasAvoid 8 ![1, 1, 0, 0, 0] ((x0 &&& x1) :: in5).toFinset := by simpa using hav1
    exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
  · have heq : insert (x0 ||| x1) in5.toFinset = ([x01, x0, x1, x2, x3, x4] : List W5).toFinset := by
      simp [in5, x01]
    rw [heq] at tail hav1
    exact no_ws1 hg tail hav1
  · have hnd : ((x0 &&& ~~~x1) :: in5).Nodup := by decide +kernel
    have hl' : live basicOps5 g 8 ((x0 &&& ~~~x1) :: in5).toFinset := by simpa using tail
    have hav' : HasAvoid 8 ![1, 1, 0, 0, 0] ((x0 &&& ~~~x1) :: in5).toFinset := by simpa using hav1
    exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)
  · have hnd : ((x1 &&& ~~~x0) :: in5).Nodup := by decide +kernel
    have hl' : live basicOps5 g 8 ((x1 &&& ~~~x0) :: in5).toFinset := by simpa using tail
    have hav' : HasAvoid 8 ![1, 1, 0, 0, 0] ((x1 &&& ~~~x0) :: in5).toFinset := by simpa using hav1
    exact absurd (hasAvoid_okAll hg hnd hl' hav') (by decide +kernel)

lemma in5_image_swap (a b : Fin 5) {s : Finset W5} (hsub : s ⊆ in5.toFinset) :
    s.image (perm5 (swap a b)) ⊆ in5.toFinset := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨i, rfl⟩ := in5_index u (List.mem_toFinset.mp (hsub hu))
  rw [perm5_swap_in]
  generalize swap a b i = j
  fin_cases j <;> exact List.mem_toFinset.mpr (by simp [in5, vinput5])

theorem no_nine_binary (t : W5) (ht : t = goal5 ∨ t = ~~~goal5)
    (run : build basicOps5 t 9 in5.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 8) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, he, tail⟩
  · have tx : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := in5_index _ (List.mem_toFinset.mp (hs tx))
    rcases ht with rfl | rfl
    · exact (in5_not_goal i).1 hi
    · exact (in5_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := in5_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := in5_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg vinput5 eq)
    have hval : ∀ w ∈ s, Valid5 w := fun w hw => in5_valid w (List.mem_toFinset.mp (hs hw))
    obtain ⟨z1, r1, hz1, hzout1, hs1, tail1⟩ := step_swap5 i 0 ht hval hz hzout he tail
    rw [perm5_swap_in, perm5_swap_in] at hz1 hs1
    have hsi : swap i 0 i = 0 := by simp [swap]
    rw [hsi] at hz1 hs1
    have hsub1 : s.image (perm5 (swap i 0)) ⊆ in5.toFinset := in5_image_swap i 0 hs
    have hval1 : ∀ w ∈ s.image (perm5 (swap i 0)), Valid5 w := fun w hw => in5_valid w (List.mem_toFinset.mp (hsub1 hw))
    let j1 := swap i 0 j
    have hj1_ne0 : j1 ≠ 0 := by
      intro h0
      have hinv : swap i 0 j1 = swap i 0 0 := congrArg (swap i 0) h0
      have hj1_inv : swap i 0 (swap i 0 j) = j := by simp [swap]; split_ifs <;> grind
      have h0_inv : swap i 0 0 = i := by simp [swap]
      exact hij (h0_inv.symm.trans (hinv.symm.trans hj1_inv))
    obtain ⟨z2, r2, hz2, _, hs2, tail2⟩ := step_swap5 j1 1 ht hval1 hz1 hzout1 hs1 tail1
    rw [perm5_swap_in, perm5_swap_in] at hz2 hs2
    have hs0 : swap j1 1 0 = 0 := by
      simp [swap, Ne.symm hj1_ne0]
    have hsj1 : swap j1 1 j1 = 1 := by simp [swap]
    rw [hs0, hsj1] at hz2 hs2
    exact no_nine_k5_01 ht (in5_image_swap j1 1 hsub1) hz2 hs2 tail2

theorem ten_binary (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = table x) :
    9 < binaryCost gs := by
  by_contra hlow
  have low : binaryCost gs ≤ 9 := by omega
  have init : ∀ u ∈ in5, holds5 in5.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 152) :
      (gs.foldl step (in5.map (bit k))).getD o false = bit k goal5 := by
    have same : List.ofFn (fun i : Fin 5 => bit k (in5.getD i.val 0)) =
        in5.map (bit k) := by
      apply List.ext_getElem (by simp [in5])
      intro i hi hj
      have hlt : i < in5.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (in5.map (bit k)) = bit k goal5
    rw [← same, he]
    exact spec_k5 k
  obtain ⟨t, ht, run⟩ := compile gs o hg in5 in5.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps5 t a in5.toFinset) :
      build basicOps5 t b in5.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_nine_binary t ht (lift low run)

end PEqualNP.Outside.L_meta_49549.FiveK5

namespace PEqualNP.Outside.L_meta_49549

def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

theorem zeroGate_canalizes :
    ∀ k : Fin 4,
      (∃ b c : Bool, ∀ a : Bool, zeroGate k a b = c) ∧
      (∃ a c : Bool, ∀ b : Bool, zeroGate k a b = c) := by
  decide

def singleInput {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)

def pairInput {n : Nat} (i j : Fin n) : Fin n → Bool :=
  fun k => decide (k = i ∨ k = j)

section Generic
variable {α : Type} {β : Type}

def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f

theorem UC_monoS (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS G A t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS G A t _ _ f (fun w hw => hw.imp id (h w)) hu⟩

theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩

theorem UC_map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {A : Fin 4 → Prop} (e : α → β)
    (he : ∀ k a b, e (G k a b) = G' k (e a) (e b)) :
    ∀ (t : ℕ) (S : α → Prop) (S' : β → Prop) (f : α), (∀ w, S w → S' (e w)) →
      UC G A t S f → UC G' A t S' (e f)
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_map e he t S S' f h hu)
    · refine Or.inr ⟨k, e a, e b, hk, h a ha, h b hb, UC_map e he t _ _ f ?_ hu⟩
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inl (he k a b)
      · exact Or.inr (h w hw)

def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws

section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}

theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d

theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)

theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)

theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2

theorem TR.inv {t : ℕ} {ws : List α} (h : TR G C ys t ws) :
    (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) := by
  refine TR.ind (P := fun t ws => (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r))) h
    ⟨fun _ => List.Perm.refl _, fun s hs => by omega⟩ ?_ ?_
  · intro s xs zs hp _ ih
    refine ⟨fun h0 => hp.symm.trans (ih.1 h0), fun s' hs => ?_⟩
    obtain ⟨k, u, a, b, r, hc, hq, hr⟩ := ih.2 s' hs
    exact ⟨k, u, a, b, r, hc, hp.symm.trans hq, hr⟩
  · intro s a b r k u hc hr _
    refine ⟨fun h0 => by omega, fun s' hs => ?_⟩
    have : s = s' := by omega
    subst this
    exact ⟨k, u, a, b, r, hc, List.Perm.refl _, hr⟩

theorem TR.len {t : ℕ} {ws : List α} (h : TR G C ys t ws) : ws.length ≤ t + ys.length := by
  refine TR.ind (P := fun t ws => ws.length ≤ t + ys.length) h (by simp) ?_ ?_
  · intro s xs zs hp _ ih
    rw [← hp.length_eq]; exact ih
  · intro s a b r k u _ _ ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    omega

theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)

end Run

def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z

theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h

theorem TR.map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {C : Fin 4 → α → α → Prop}
    {C' : Fin 4 → β → β → Prop} (e : α → β) (he : ∀ k a b, e (G k a b) = G' k (e a) (e b))
    (hC : ∀ k a b, C k a b → C' k (e a) (e b)) {ys : List α} {t : ℕ} {ws : List α}
    (h : TR G C ys t ws) : TR G' C' (ys.map e) t (ws.map e) := by
  refine TR.ind (P := fun t ws => TR G' C' (ys.map e) t (ws.map e)) h TR.done
    (fun _ _ _ hp _ ih => TR.perm (hp.map e) ih) ?_
  intro s a b r k u hc _ ih
  rw [List.map_append, List.map_replicate, he] at ih
  exact TR.step k u (hC _ _ _ hc) ih

theorem TR.rel {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} (R : α → α → Prop)
    (hR : ∀ k a a' b b', R a a' → R b b' → R (G k a b) (G k a' b')) {ys : List α} {t : ℕ}
    {ws : List α} (h : TR G (fun k _ _ => A k) ys t ws) :
    ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws' := by
  refine TR.ind (P := fun t ws => ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws') h
    (fun ws' hw => ⟨ws', hw, TR.done⟩) ?_ ?_
  · intro s xs zs hp _ ih zs' hz
    obtain ⟨xs', hx, hp'⟩ := List.perm_comp_forall₂ hp hz
    obtain ⟨ys', hy, hr⟩ := ih xs' hx
    exact ⟨ys', hy, TR.perm hp' hr⟩
  · intro s a b r k u hc _ ih ws' hw
    obtain ⟨a', t1, ha, ht1, rfl⟩ := List.forall₂_cons_left_iff.1 hw
    obtain ⟨b', r', hb, hr', rfl⟩ := List.forall₂_cons_left_iff.1 ht1
    have h1 : List.Forall₂ R (List.replicate (u + 1) (G k a b) ++ r)
        (List.replicate (u + 1) (G k a' b') ++ r') := by
      refine List.rel_append ?_ hr'
      generalize u + 1 = n
      induction n with
      | zero => exact List.Forall₂.nil
      | succ n ih => exact List.Forall₂.cons (hR k a a' b b' ha hb) ih
    obtain ⟨ys', hy, hrun⟩ := ih _ h1
    exact ⟨ys', hy, TR.step k u hc hrun⟩

end Generic

abbrev BF := (Fin 8 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)

def var (i : Fin 8) : BF := fun x => x i

def gM (k a b : ℕ) : ℕ :=
  match k with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)

def gN (k : Fin 4) (a b : ℕ) : ℕ := gM k.val a b

theorem gN_testBit (k : Fin 4) (a b i : ℕ) :
    (gN k a b).testBit i = zeroGate k (a.testBit i) (b.testBit i) := by
  fin_cases k <;>
    simp [gN, gM, zeroGate, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

theorem gN_zero_left (k : Fin 4) (b : ℕ) : gN k 0 b = 0 ∨ gN k 0 b = b := by
  fin_cases k <;> simp [gN, gM]

theorem gN_zero_right (k : Fin 4) (a : ℕ) : gN k a 0 = 0 ∨ gN k a 0 = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_self (k : Fin 4) (a : ℕ) : gN k a a = 0 ∨ gN k a a = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_lt (k : Fin 4) (a b : ℕ) (ha : a < 1024) (hb : b < 1024) : gN k a b < 1024 := by
  apply Nat.lt_pow_two_of_testBit (n := 10)
  intro i hi
  have hp : (1024 : ℕ) ≤ 2 ^ i :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by norm_num) hi)
  rw [gN_testBit, Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]
  fin_cases k <;> rfl

def enc {ρ : Type} (w : ρ → Bool) : List ρ → ℕ
  | [] => 0
  | p :: t => Nat.bit (w p) (enc w t)

theorem enc_testBit {ρ : Type} (w : ρ → Bool) : ∀ (l : List ρ) (j : ℕ),
    (enc w l).testBit j = (l.map w).getD j false
  | [], j => by simp [enc]
  | p :: t, 0 => by simp [enc]
  | p :: t, j + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit w t j]

theorem enc_gate {ρ : Type} (k : Fin 4) (a b : ρ → Bool) (l : List ρ) :
    enc (fun r => zeroGate k (a r) (b r)) l = gN k (enc a l) (enc b l) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [gN_testBit, enc_testBit, enc_testBit, enc_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    fin_cases k <;> rfl

theorem enc_gF (k : Fin 4) (a b : BF) (l : List (Fin 8 → Bool)) :
    enc (gF k a b) l = gN k (enc a l) (enc b l) := enc_gate k a b l

theorem enc_lt {ρ : Type} (w : ρ → Bool) (l : List ρ) : enc w l < 2 ^ l.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [enc_testBit, List.getD_eq_default _ _ (by simp; omega)]

theorem TRN_det {C : Fin 4 → ℕ → ℕ → Prop} {y : ℕ} {s : ℕ} {ws : List ℕ}
    (h : TR gN C [y] s ws) (i j : ℕ) :
    (∀ t ∈ ws, t.testBit i = t.testBit j) → y.testBit i = y.testBit j := by
  refine TR.ind (P := fun _ ws => (∀ t ∈ ws, t.testBit i = t.testBit j) →
    y.testBit i = y.testBit j) h (fun h => h y (by simp)) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht, gN_testBit, gN_testBit, hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

theorem TRN_zp {C : Fin 4 → ℕ → ℕ → Prop} {y : ℕ} {s : ℕ} {ws : List ℕ}
    (h : TR gN C [y] s ws) (i : ℕ) :
    (∀ t ∈ ws, t.testBit i = false) → y.testBit i = false := by
  refine TR.ind (P := fun _ ws => (∀ t ∈ ws, t.testBit i = false) →
    y.testBit i = false) h (fun h => h y (by simp)) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht, gN_testBit, hz a (by simp), hz b (by simp)]
      fin_cases k <;> rfl
    · exact hz t (by simp [ht])

def sg (p t : ℕ) : ℕ := if t.testBit p then t ^^^ 1023 else t

def covB (f : ℕ → ℕ) (ws : List ℕ) : Bool :=
  ws.foldl (fun acc t => acc ||| f t) 0 &&& 1008 == 1008

def cov (ws : List ℕ) : Bool :=
  covB id ws && covB (sg 0) ws && covB (sg 1) ws && covB (sg 2) ws && covB (sg 3) ws

theorem fold_bit (f : ℕ → ℕ) (i : ℕ) : ∀ (ws : List ℕ) (a : ℕ),
    (ws.foldl (fun acc t => acc ||| f t) a).testBit i =
      (a.testBit i || ws.any fun t => (f t).testBit i)
  | [], a => by simp
  | t :: ws, a => by
    rw [List.foldl_cons, fold_bit f i ws, Nat.testBit_or, List.any_cons, Bool.or_assoc]

theorem covB_iff (f : ℕ → ℕ) (ws : List ℕ) :
    covB f ws = true ↔
      ∀ i, (1008 : ℕ).testBit i = true → ∃ t ∈ ws, (f t).testBit i = true := by
  unfold covB
  rw [beq_iff_eq]
  constructor
  · intro h i hi
    have h1 := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.and_true, fold_bit, Nat.zero_testBit, Bool.false_or,
      List.any_eq_true] at h1
    exact h1
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : (1008 : ℕ).testBit i
    · simp
    · rw [Bool.and_true, fold_bit, Nat.zero_testBit, Bool.false_or, List.any_eq_true]
      exact h i hi

theorem sg_bit (p t i : ℕ) (hi : (1008 : ℕ).testBit i = true) :
    (sg p t).testBit i = (t.testBit i != t.testBit p) := by
  have h1023 : (1023 : ℕ).testBit i = true := by
    have hlt : i < 10 := by
      by_contra hc
      have h2 : (1008 : ℕ) < 2 ^ i :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hc))
      rw [Nat.testBit_lt_two_pow h2] at hi
      exact Bool.noConfusion hi
    interval_cases i <;> rfl
  have e : (sg p t).testBit i =
      if t.testBit p = true then (t.testBit i ^^ true) else t.testBit i := by
    unfold sg
    split_ifs with h
    · rw [Nat.testBit_xor, h1023]
    · rfl
  rw [e]
  cases t.testBit i <;> cases t.testBit p <;> rfl

theorem TRN_cov {C : Fin 4 → ℕ → ℕ → Prop} {s : ℕ} {ws : List ℕ}
    (h : TR gN C [1008] s ws) : cov ws = true := by
  have hd := TRN_det h
  have hz := TRN_zp h
  have k1 : ∀ i, (1008 : ℕ).testBit i = true → ∃ t ∈ ws, (id t).testBit i = true := by
    intro i hi
    by_contra hc
    have h1 : ∀ t ∈ ws, t.testBit i = false := by
      intro t ht
      by_contra h2
      exact hc ⟨t, ht, by simpa using h2⟩
    rw [hz i h1] at hi
    exact Bool.noConfusion hi
  have k2 : ∀ p, (1008 : ℕ).testBit p = false → ∀ i, (1008 : ℕ).testBit i = true →
      ∃ t ∈ ws, (sg p t).testBit i = true := by
    intro p hp i hi
    by_contra hc
    have h1 : ∀ t ∈ ws, t.testBit i = t.testBit p := by
      intro t ht
      by_contra h2
      refine hc ⟨t, ht, ?_⟩
      rw [sg_bit p t i hi]
      simpa using h2
    rw [hd i p h1, hp] at hi
    exact Bool.noConfusion hi
  simp only [cov, Bool.and_eq_true, covB_iff]
  exact ⟨⟨⟨⟨k1, k2 0 (by decide)⟩, k2 1 (by decide)⟩, k2 2 (by decide)⟩, k2 3 (by decide)⟩

def tryG (g a b : ℕ) (f : ℕ → Bool) : Bool :=
  match g with
  | 0 => false
  | g' + 1 => g' + 1 != a && g' + 1 != b && f (g' + 1)

theorem tryG_iff (g a b : ℕ) (f : ℕ → Bool) :
    tryG g a b f = true ↔ g ≠ 0 ∧ g ≠ a ∧ g ≠ b ∧ f g = true := by
  cases g <;> simp [tryG, and_assoc]

def search : ℕ → List ℕ → Bool
  | 0, ws => decide (ws = [1008])
  | s + 1, ws =>
    decide (ws.length ≤ s + 2) && cov ws &&
      ws.dedup.any fun a => ws.dedup.any fun b => decide (a < b) &&
        [0, 1, 2, 3].any fun k =>
          tryG (gM k a b) a b fun g =>
            (List.range (s + 3 - ws.length)).any fun u =>
              search s (List.replicate (u + 1) g ++ (ws.erase a).erase b)

theorem search_succ (s : ℕ) (ws : List ℕ) :
    search (s + 1) ws = true ↔ ws.length ≤ s + 2 ∧ cov ws = true ∧
      ∃ a ∈ ws, ∃ b ∈ ws, a < b ∧ ∃ k, k < 4 ∧ gM k a b ≠ 0 ∧ gM k a b ≠ a ∧ gM k a b ≠ b ∧
        ∃ u, u < s + 3 - ws.length ∧
          search s (List.replicate (u + 1) (gM k a b) ++ (ws.erase a).erase b) = true := by
  simp only [search, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_dedup,
    tryG_iff, List.mem_range, and_assoc]
  constructor
  · rintro ⟨h1, h2, a, ha, b, hb, hab, k, hk, h3⟩
    refine ⟨h1, h2, a, ha, b, hb, hab, k, ?_, h3⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  · rintro ⟨h1, h2, a, ha, b, hb, hab, k, hk, h3⟩
    refine ⟨h1, h2, a, ha, b, hb, hab, k, ?_, h3⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

theorem cov_perm {xs zs : List ℕ} (hp : xs.Perm zs) (h : cov xs = true) : cov zs = true := by
  simp only [cov, Bool.and_eq_true, covB_iff] at h ⊢
  have key : ∀ f : ℕ → ℕ,
      (∀ i, (1008 : ℕ).testBit i = true → ∃ t ∈ xs, (f t).testBit i = true) →
      ∀ i, (1008 : ℕ).testBit i = true → ∃ t ∈ zs, (f t).testBit i = true :=
    fun f hf i hi => let ⟨t, ht, h3⟩ := hf i hi; ⟨t, hp.mem_iff.1 ht, h3⟩
  exact ⟨⟨⟨⟨key _ h.1.1.1.1, key _ h.1.1.1.2⟩, key _ h.1.1.2⟩, key _ h.1.2⟩, key _ h.2⟩

theorem search_perm : ∀ (s : ℕ) (xs zs : List ℕ), xs.Perm zs → search s xs = true →
    search s zs = true
  | 0, xs, zs, hp, h => by
    simp only [search, decide_eq_true_eq] at h ⊢
    subst h
    exact List.perm_singleton.1 hp.symm
  | s + 1, xs, zs, hp, h => by
    rw [search_succ] at h ⊢
    obtain ⟨h1, h2, a, ha, b, hb, hab, k, hk, h3, h4, h5, u, hu, h6⟩ := h
    refine ⟨hp.length_eq ▸ h1, cov_perm hp h2, a, hp.mem_iff.1 ha, b, hp.mem_iff.1 hb, hab, k,
      hk, h3, h4, h5, u, hp.length_eq ▸ hu, ?_⟩
    exact search_perm s _ _ (List.Perm.append_left _ ((hp.erase a).erase b)) h6

theorem gM_swap (k a b : ℕ) (hk : k < 4) :
    ∃ k', k' < 4 ∧ gM k' b a = gM k a b := by
  interval_cases k
  · exact ⟨0, by omega, by simp [gM, Nat.and_comm]⟩
  · exact ⟨1, by omega, by simp [gM, Nat.or_comm]⟩
  · exact ⟨3, by omega, by simp [gM, Nat.and_comm]⟩
  · exact ⟨2, by omega, by simp [gM, Nat.and_comm]⟩

abbrev NR (s : ℕ) (ws : List ℕ) : Prop :=
  TR gN (strictC gN 0 (fun _ => True) fun t => t < 1024) [1008] s ws

theorem run_search {s : ℕ} {ws : List ℕ} (h : NR s ws) : search s ws = true := by
  refine TR.ind (P := fun s ws => search s ws = true) h (by simp [search]) ?_ ?_
  · intro s xs zs hp _ ih
    exact search_perm s xs zs hp ih
  · intro s a b r k u hc hr ih
    have hrun := TR.step k u hc hr
    obtain ⟨-, -, -, hab, hga, hgb, hgz⟩ := hc
    have hlen := TR.len hr
    simp only [List.length_append, List.length_replicate, List.length_singleton] at hlen
    rw [search_succ]
    refine ⟨by have := TR.len hrun; simpa using this, TRN_cov hrun, ?_⟩
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · refine ⟨a, by simp, b, by simp, hlt, k.val, k.isLt, hgz, hga, hgb, u, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · have : ((a :: b :: r).erase a).erase b = r := by simp
        rw [this]
        exact ih
    · obtain ⟨k', hk', he⟩ := gM_swap k.val a b k.isLt
      have he' : gM k' b a = gN k a b := he
      refine ⟨b, by simp, a, by simp, hlt, k', hk', by rw [he']; exact hgz, by rw [he']; exact hgb,
        by rw [he']; exact hga, u, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · rw [he']
        have : ((a :: b :: r).erase b).erase a = r := by
          rw [List.erase_cons_tail (by simpa using hab), List.erase_cons_head,
            List.erase_cons_head]
        rw [this]
        exact ih

def bperm (rho : List ℕ) (t : ℕ) : ℕ := enc (fun i => t.testBit i) rho

theorem bperm_gN (rho : List ℕ) (k : Fin 4) (a b : ℕ) :
    bperm rho (gN k a b) = gN k (bperm rho a) (bperm rho b) := by
  unfold bperm
  rw [← enc_gate]
  congr 1
  funext i
  exact gN_testBit k a b i

theorem NR_perm (rho : List ℕ) (hlen : rho.length = 10)
    (hinv : ∀ t, t < 1024 → bperm rho (bperm rho t) = t) (h0 : bperm rho 0 = 0)
    (h1008 : bperm rho 1008 = 1008) {s : ℕ} {ws : List ℕ} (h : NR s ws) :
    NR s (ws.map (bperm rho)) := by
  have hlt : ∀ t, bperm rho t < 1024 := fun t => by
    have := enc_lt (fun i => t.testBit i) rho
    rw [hlen] at this
    exact this
  have hinj : ∀ a b, a < 1024 → b < 1024 → bperm rho a = bperm rho b → a = b := by
    intro a b ha hb he
    rw [← hinv a ha, ← hinv b hb, he]
  have h1 := TR.map (C' := strictC gN 0 (fun _ => True) fun t => t < 1024) (bperm rho)
    (bperm_gN rho) (by
      rintro k a b ⟨hk, ha, hb, hab, hga, hgb, hgz⟩
      have hg := gN_lt k a b ha hb
      refine ⟨hk, hlt a, hlt b, fun e => hab (hinj a b ha hb e), ?_, ?_, ?_⟩
      · rw [← bperm_gN]; exact fun e => hga (hinj _ _ hg ha e)
      · rw [← bperm_gN]; exact fun e => hgb (hinj _ _ hg hb e)
      · rw [← bperm_gN, ← h0]; exact fun e => hgz (hinj _ _ hg (by norm_num) e)) h
  simp only [List.map_cons, List.map_nil, h1008] at h1
  exact h1

def mk (m0 m1 m2 m3 : ℕ) : List ℕ :=
  List.replicate m0 113 ++ List.replicate m1 402 ++ List.replicate m2 676 ++ List.replicate m3 840

theorem mk_perm (ws : List ℕ) (h : ∀ w ∈ ws, w = 113 ∨ w = 402 ∨ w = 676 ∨ w = 840) :
    ws.Perm (mk (ws.count 113) (ws.count 402) (ws.count 676) (ws.count 840)) := by
  rw [List.perm_iff_count]
  intro a
  simp only [mk, List.count_append, List.count_replicate]
  by_cases h0 : a = 113
  · subst h0; simp
  by_cases h1 : a = 402
  · subst h1; simp
  by_cases h2 : a = 676
  · subst h2; simp
  by_cases h3 : a = 840
  · subst h3; simp
  have : a ∉ ws := fun hm => by rcases h a hm with h | h | h | h <;> contradiction
  simp [List.count_eq_zero_of_not_mem this, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3]

def Good (s m0 m1 m2 m3 : ℕ) : Prop := ∃ ws : List ℕ, ws.Perm (mk m0 m1 m2 m3) ∧ NR s ws

def rho01 : List ℕ := [1, 0, 2, 3, 4, 7, 8, 5, 6, 9]

def rho12 : List ℕ := [0, 2, 1, 3, 5, 4, 6, 7, 9, 8]

def rho23 : List ℕ := [0, 1, 3, 2, 4, 6, 5, 8, 7, 9]

theorem inv01 : ∀ t, t < 1024 → bperm rho01 (bperm rho01 t) = t := by decide +kernel

theorem inv12 : ∀ t, t < 1024 → bperm rho12 (bperm rho12 t) = t := by decide +kernel

theorem inv23 : ∀ t, t < 1024 → bperm rho23 (bperm rho23 t) = t := by decide +kernel

theorem good01 {s m0 m1 m2 m3 : ℕ} (h : Good s m0 m1 m2 m3) : Good s m1 m0 m2 m3 := by
  obtain ⟨ws, hp, hr⟩ := h
  refine ⟨ws.map (bperm rho01), (hp.map _).trans ?_,
    NR_perm rho01 rfl inv01 (by decide) (by decide) hr⟩
  have e1 : bperm rho01 113 = 402 := by decide
  have e2 : bperm rho01 402 = 113 := by decide
  have e3 : bperm rho01 676 = 676 := by decide
  have e4 : bperm rho01 840 = 840 := by decide
  simp only [mk, List.map_append, List.map_replicate, e1, e2, e3, e4]
  rw [List.perm_iff_count]
  intro a
  simp only [List.count_append, List.count_replicate]
  omega

theorem good12 {s m0 m1 m2 m3 : ℕ} (h : Good s m0 m1 m2 m3) : Good s m0 m2 m1 m3 := by
  obtain ⟨ws, hp, hr⟩ := h
  refine ⟨ws.map (bperm rho12), (hp.map _).trans ?_,
    NR_perm rho12 rfl inv12 (by decide) (by decide) hr⟩
  have e1 : bperm rho12 113 = 113 := by decide
  have e2 : bperm rho12 402 = 676 := by decide
  have e3 : bperm rho12 676 = 402 := by decide
  have e4 : bperm rho12 840 = 840 := by decide
  simp only [mk, List.map_append, List.map_replicate, e1, e2, e3, e4]
  rw [List.perm_iff_count]
  intro a
  simp only [List.count_append, List.count_replicate]
  omega

theorem good23 {s m0 m1 m2 m3 : ℕ} (h : Good s m0 m1 m2 m3) : Good s m0 m1 m3 m2 := by
  obtain ⟨ws, hp, hr⟩ := h
  refine ⟨ws.map (bperm rho23), (hp.map _).trans ?_,
    NR_perm rho23 rfl inv23 (by decide) (by decide) hr⟩
  have e1 : bperm rho23 113 = 113 := by decide
  have e2 : bperm rho23 402 = 402 := by decide
  have e3 : bperm rho23 676 = 840 := by decide
  have e4 : bperm rho23 840 = 676 := by decide
  simp only [mk, List.map_append, List.map_replicate, e1, e2, e3, e4]
  rw [List.perm_iff_count]
  intro a
  simp only [List.count_append, List.count_replicate]
  omega

theorem good_sorted (s : ℕ) : ∀ (n m0 m1 m2 m3 : ℕ), m1 + 2 * m2 + 3 * m3 ≤ n →
    Good s m0 m1 m2 m3 →
    ∃ a b c d, d ≤ c ∧ c ≤ b ∧ b ≤ a ∧ a + b + c + d = m0 + m1 + m2 + m3 ∧ Good s a b c d
  | 0, m0, m1, m2, m3, hn, h => ⟨m0, m1, m2, m3, by omega, by omega, by omega, rfl, h⟩
  | n + 1, m0, m1, m2, m3, hn, h => by
    by_cases h1 : m1 ≤ m0
    · by_cases h2 : m2 ≤ m1
      · by_cases h3 : m3 ≤ m2
        · exact ⟨m0, m1, m2, m3, h3, h2, h1, rfl, h⟩
        · obtain ⟨a, b, c, d, q1, q2, q3, q4, q5⟩ :=
            good_sorted s n m0 m1 m3 m2 (by omega) (good23 h)
          exact ⟨a, b, c, d, q1, q2, q3, by omega, q5⟩
      · obtain ⟨a, b, c, d, q1, q2, q3, q4, q5⟩ :=
          good_sorted s n m0 m2 m1 m3 (by omega) (good12 h)
        exact ⟨a, b, c, d, q1, q2, q3, by omega, q5⟩
    · obtain ⟨a, b, c, d, q1, q2, q3, q4, q5⟩ :=
        good_sorted s n m1 m0 m2 m3 (by omega) (good01 h)
      exact ⟨a, b, c, d, q1, q2, q3, by omega, q5⟩

def searchS (s : ℕ) : Bool :=
  (List.range (s + 2)).any fun m0 => (List.range (m0 + 1)).any fun m1 =>
    (List.range (m1 + 1)).any fun m2 => (List.range (m2 + 1)).any fun m3 =>
      search s (mk m0 m1 m2 m3)

theorem run_searchS {s : ℕ} {ws : List ℕ} (h : NR s ws)
    (hw : ∀ w ∈ ws, w = 113 ∨ w = 402 ∨ w = 676 ∨ w = 840) : searchS s = true := by
  have hp := mk_perm ws hw
  have hl := TR.len h
  rw [hp.length_eq] at hl
  simp only [mk, List.length_append, List.length_replicate, List.length_singleton] at hl
  obtain ⟨a, b, c, d, q1, q2, q3, q4, ws', hp', hr'⟩ :=
    good_sorted s _ _ _ _ _ le_rfl ⟨ws, hp, h⟩
  have hs := search_perm s _ _ hp' (run_search hr')
  simp only [searchS, List.any_eq_true, List.mem_range]
  exact ⟨a, by omega, b, by omega, c, by omega, d, by omega, hs⟩

set_option maxRecDepth 100000 in
theorem searchS_false : (List.range 7).all (fun s => !searchS s) = true := by
  decide +kernel

theorem U4 (ι : Fin 4 → Fin 8) (hι : Function.Injective ι) (F : BF)
    (hs : ∀ j, F (singleInput (ι j)) = false)
    (hp : ∀ j j', j ≠ j' → F (pairInput (ι j) (ι j')) = true) :
    ¬ UC gF (fun _ => True) 6 (fun w => ∃ j, w = var (ι j)) F := by
  intro hu
  let rows : List (Fin 8 → Bool) := [singleInput (ι 0), singleInput (ι 1), singleInput (ι 2),
    singleInput (ι 3), pairInput (ι 0) (ι 1), pairInput (ι 0) (ι 2), pairInput (ι 0) (ι 3),
    pairInput (ι 1) (ι 2), pairInput (ι 1) (ι 3), pairInput (ι 2) (ι 3)]
  have hF : enc F rows = 1008 := by
    simp only [rows, enc, hs, hp 0 1 (by decide), hp 0 2 (by decide), hp 0 3 (by decide),
      hp 1 2 (by decide), hp 1 3 (by decide), hp 2 3 (by decide)]
    rfl
  have hv : ∀ j, enc (var (ι j)) rows = 113 ∨ enc (var (ι j)) rows = 402 ∨
      enc (var (ι j)) rows = 676 ∨ enc (var (ι j)) rows = 840 := by
    intro j
    fin_cases j <;>
      simp [rows, enc, var, singleInput, pairInput, hι.eq_iff, Nat.bit]
  have hu2 : UC gN (fun _ => True) 6
      (fun w => w = 113 ∨ w = 402 ∨ w = 676 ∨ w = 840) (enc F rows) :=
    UC_map (fun w => enc w rows) (fun k a b => enc_gF k a b rows) 6 _ _ F
      (by rintro w ⟨j, rfl⟩; exact hv j) hu
  rw [hF] at hu2
  obtain ⟨t', ht, ws, hws, hr⟩ := normalize gN 0 (fun _ => True) (fun t => t < 1024) gN_lt
    gN_zero_left gN_zero_right gN_self 6 _ 1008
    (by rintro w (rfl | rfl | rfl | rfl) <;> norm_num) (by decide) hu2
  have h1 := run_searchS hr fun w hw => (hws w hw).1
  have h2 := searchS_false
  rw [List.all_eq_true] at h2
  have h3 := h2 t' (List.mem_range.2 (by omega))
  rw [h1] at h3
  exact Bool.noConfusion h3

def zF : BF := fun _ => false

def rst (p : Fin 8) (a : BF) : BF := fun x => a (Function.update x p false)

def ThrL (V : Fin 8 → Prop) (F : BF) : Prop :=
  (∀ i, V i → F (singleInput i) = false) ∧
    ∀ i j, V i → V j → i ≠ j → F (pairInput i j) = true

theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_zero (k : Fin 4) : gF k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]

theorem upd_single {i p : Fin 8} (h : i ≠ p) :
    Function.update (singleInput i) p false = singleInput i := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [singleInput, Ne.symm h]
  · simp [Function.update_of_ne hm]

theorem upd_pair {i j p : Fin 8} (hi : i ≠ p) (hj : j ≠ p) :
    Function.update (pairInput i j) p false = pairInput i j := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [pairInput, Ne.symm hi, Ne.symm hj]
  · simp [Function.update_of_ne hm]

theorem rst_var_self (p : Fin 8) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]

theorem rst_var_ne {i p : Fin 8} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]

theorem var_inj {i j : Fin 8} (h : var i = var j) : i = j := by
  have := congrFun h (singleInput i)
  exact (by simpa [var, singleInput] using this : j = i).symm

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 8 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

def dcount (p : Fin 8) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)

theorem dcount_cons (p : Fin 8) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]

theorem dcount_rep (p : Fin 8) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {A : Fin 4 → Prop} (p : Fin 8) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List BF} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : BF → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2

def MonoA : Fin 4 → Prop := fun k => k.val < 2

abbrev MR (ys : List BF) (s : ℕ) (ws : List BF) : Prop := TR gF (fun k _ _ => MonoA k) ys s ws

def outF (ys : List BF) : BF := fun x => ys.any fun y => y x

def otop (x : Fin 8) : BF := fun p => decide (∃ i, i ≠ x ∧ p i = true)

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl

theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)

def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])

theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 8 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin 8 → Bool) : ∀ (gs : List Gate) (W : List BF),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]

theorem getD_mem (W : List BF) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

theorem gate_form (g : Gate) (W : List BF)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    gv g W = zF ∨ gv g W = (fun _ => true) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = a) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = fun x => !a x) ∨
    (∃ k a b, MonoA k ∧ (a ∈ W ∨ a = zF) ∧ (b ∈ W ∨ b = zF) ∧ gv g W = gF k a b) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
    · exact Or.inl (funext fun x => by simp [gv, GateOp.eval, zF])
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_and]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_or]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · simp at hl

def ori (w : BF) : BF := fun x => xor (w x) (w fun _ => false)

theorem ori_zero : ori zF = zF := funext fun x => by simp [ori, zF]

theorem ori_true : ori (fun _ => true) = zF := funext fun x => by simp [ori, zF]

theorem ori_not (a : BF) : ori (fun x => !a x) = ori a :=
  funext fun x => by
    simp only [ori]
    cases a x <;> cases a (fun _ => false) <;> rfl

theorem ori_zp {w : BF} (h : w (fun _ => false) = false) : ori w = w :=
  funext fun x => by simp [ori, h]

theorem ori_gate (k : Fin 4) (hk : MonoA k) (a b : BF) :
    ∃ k', ori (gF k a b) = gF k' (ori a) (ori b) := by
  rcases mono_cases k hk with rfl | rfl
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩

abbrev GOK (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem ori_key (g : Gate) (W : List BF) (S : BF → Prop)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    (ori (gv g W) = zF ∨ S (ori (gv g W))) ∨
      ∃ k a b, S a ∧ S b ∧ ori (gv g W) = gF k a b := by
  have hWz : ∀ a, (a ∈ W ∨ a = zF) → ori a = zF ∨ S (ori a) := by
    rintro a (h | rfl)
    · exact hW a h
    · exact Or.inl ori_zero
  rcases gate_form g W hop hl with h | h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩ | ⟨k, a, b, hk, ha, hb, h⟩
  · rw [h]; exact Or.inl (Or.inl ori_zero)
  · rw [h]; exact Or.inl (Or.inl ori_true)
  · rw [h]; exact Or.inl (hWz a ha)
  · rw [h, ori_not]; exact Or.inl (hWz a ha)
  · obtain ⟨k', hk'⟩ := ori_gate k hk a b
    rw [h, hk']
    rcases hWz a ha with ha1 | ha1
    · rw [ha1]
      rcases gF_zero_left k' (ori b) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (hWz b hb)
    rcases hWz b hb with hb1 | hb1
    · rw [hb1]
      rcases gF_zero_right k' (ori a) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (Or.inr ha1)
    exact Or.inr ⟨k', ori a, ori b, ha1, hb1, rfl⟩

def graphTable (a : ℕ) (x : Fin 8 → Bool) : Bool := a.testBit (tableIndex x)

def assignment (a : ℕ) (i : Fin 8) : Bool := a.testBit i.val

def isNot : GateOp → Bool
  | .not => true
  | _ => false

theorem isNot_true (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

def countBinary : List Gate → ℕ
  | [] => 0
  | g :: gs => countBinary gs + if isNot g.op then 0 else 1

theorem countBinary_le (gs : List Gate) : countBinary gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [countBinary, List.length_cons]
    split <;> omega

theorem countBinary_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) :
    countBinary gs < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a, ha, he⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · have hb := countBinary_le gs
      simp [countBinary, he, isNot, Nat.lt_succ_of_le hb]
    · have hb := ih ⟨a, ha, he⟩
      simp only [countBinary, List.length_cons]
      split <;> omega

theorem not_key (g : Gate) (W : List BF) (S : BF → Prop) (hop : g.op = GateOp.not)
    (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    ori (gv g W) = zF ∨ S (ori (gv g W)) := by
  obtain ⟨op, ins⟩ := g
  change op = GateOp.not at hop
  subst op
  cases ins with
  | nil => exact Or.inl ori_true
  | cons i rest =>
    have he : gv ⟨GateOp.not, i :: rest⟩ W = fun x => !(W.getD i zF) x := rfl
    rw [he, ori_not]
    rcases getD_mem W i with h | h
    · exact hW _ h
    · rw [h]; exact Or.inl ori_zero

theorem trans_binary : ∀ (gs : List Gate) (W : List BF) (S : BF → Prop), GOK gs →
    (∀ w ∈ W, ori w = zF ∨ S (ori w)) → ∀ o : ℕ,
    ori ((wiresF gs W).getD o zF) = zF ∨
      UC gF (fun _ => True) (countBinary gs) S (ori ((wiresF gs W).getD o zF))
  | [], W, S, _, hw, o => by
    rcases getD_mem W o with h | h
    · exact hw _ h
    · rw [wiresF, h]; exact Or.inl ori_zero
  | g :: gs, W, S, hg, hw, o => by
    have hg1 := hg g (by simp)
    have hg2 : GOK gs := fun g' h => hg g' (by simp [h])
    have free (h : ori (gv g W) = zF ∨ S (ori (gv g W))) :=
      trans_binary gs (W ++ [gv g W]) S hg2 (by
        intro w hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hw w hm
        · rw [List.mem_singleton.1 hm]; exact h) o
    simp only [wiresF, countBinary]
    by_cases hn : g.op = GateOp.not
    · simpa [hn, isNot] using free (not_key g W S hn hw)
    · rw [if_neg (fun ht => hn ((isNot_true g.op).1 ht))]
      rcases ori_key g W S hg1.1 hg1.2 hw with h | ⟨k, a, b, ha, hb, h⟩
      · exact (free h).imp id (UC_le (Nat.le_succ _))
      · have next := trans_binary gs (W ++ [gv g W]) (fun w => w = gF k a b ∨ S w) hg2 (by
          intro w hm
          rcases List.mem_append.1 hm with hm | hm
          · exact (hw w hm).imp id Or.inr
          · rw [List.mem_singleton.1 hm]; exact Or.inr (Or.inl h)) o
        exact next.imp id (UC_gate k a b trivial ha hb)

def sourceVars (xs : Finset (Fin 8)) (f : BF) : Prop := ∃ i ∈ xs, f = var i

theorem remove_var (F : BF) (p : Fin 8) (xs : Finset (Fin 8)) (s : ℕ)
    (hd : ∃ x, rst p F x ≠ F x) (hn : rst p F ≠ zF)
    (h : UC gF (fun _ => True) s (sourceVars xs) F) :
    ∃ t, t + 1 ≤ s ∧ UC gF (fun _ => True) t (sourceVars (xs.erase p)) (rst p F) := by
  have hf : F ≠ zF := fun e => hn (by rw [e]; rfl)
  obtain ⟨k, hk, ws, hws, run⟩ := normalize gF zF (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ => trivial) gF_zero_left gF_zero_right gF_self
    s (sourceVars xs) F (fun _ _ => trivial) hf h
  have hp : var p ∈ ws := by
    by_contra hmiss
    obtain ⟨x, hx⟩ := hd
    apply hx
    exact TRF_det run (Function.update x p false) x (by
      intro w hw
      obtain ⟨i, _, rfl⟩ := (hws w hw).1
      have hi : i ≠ p := fun e => hmiss (e ▸ hw)
      exact Function.update_of_ne hi false x) F (by simp)
  have hc : 1 ≤ dcount p ws := by
    apply Nat.succ_le_of_lt
    unfold dcount
    exact List.countP_pos_iff.2 ⟨var p, hp, by simp [rst_var_self]⟩
  have dr := pot_dead p hn (TR.monoC (fun _ _ _ _ => trivial) run)
  refine ⟨k - dcount p ws, by omega, dr.2 (sourceVars (xs.erase p)) ?_⟩
  intro w hw hz
  obtain ⟨i, hi, rfl⟩ := (hws w hw).1
  have hne : i ≠ p := fun e => hz (e ▸ rst_var_self p)
  exact ⟨i, Finset.mem_erase.2 ⟨hne, hi⟩, rst_var_ne hne⟩

namespace Cofactor
theorem UC_monoS {α : Type} {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS t _ _ f (fun w hw => hw.imp id (h w)) hu⟩

def phi (p : Fin 8) (b : Bool) (a : BF) : BF :=
  ori (fun x => a (Function.update x p b))

def Fix (p : Fin 8) (a : BF) : Prop :=
  (∀ b x, a (Function.update x p b) = a x) ∧ a (fun _ => false) = false

theorem phi_var_self (p : Fin 8) (b : Bool) : phi p b (var p) = zF :=
  funext fun x => by simp [phi, ori, var, zF]

theorem phi_fix {p : Fin 8} {a : BF} (h : Fix p a) (b : Bool) : phi p b a = a :=
  funext fun x => by simp [phi, ori, h.1, h.2]

theorem fix_var {p i : Fin 8} (h : i ≠ p) : Fix p (var i) :=
  ⟨fun b x => by simp [var, Function.update_of_ne h], rfl⟩

theorem not_fix_var (p : Fin 8) : ¬ Fix p (var p) := by
  intro h
  have h1 := h.1 true (fun _ => false)
  simp [var] at h1

theorem fix_gF {p : Fin 8} {a b : BF} (k : Fin 4) (ha : Fix p a) (hb : Fix p b) :
    Fix p (gF k a b) :=
  ⟨fun v x => by simp [gF, ha.1, hb.1], by fin_cases k <;> simp [gF, zeroGate, ha.2, hb.2]⟩

theorem phi_gF (p : Fin 8) (v : Bool) (k : Fin 4) (a b : BF) :
    ∃ k', phi p v (gF k a b) = gF k' (phi p v a) (phi p v b) := by
  fin_cases k <;> cases hca : a (Function.update (fun _ => false) p v) <;>
    cases hcb : b (Function.update (fun _ => false) p v) <;>
    first
    | (refine ⟨0, funext fun x => ?_⟩; cases hax : a (Function.update x p v) <;> cases hbx : b (Function.update x p v) <;> simp [phi, ori, gF, zeroGate, hca, hcb, hax, hbx] <;> done)
    | (refine ⟨1, funext fun x => ?_⟩; cases hax : a (Function.update x p v) <;> cases hbx : b (Function.update x p v) <;> simp [phi, ori, gF, zeroGate, hca, hcb, hax, hbx] <;> done)
    | (refine ⟨2, funext fun x => ?_⟩; cases hax : a (Function.update x p v) <;> cases hbx : b (Function.update x p v) <;> simp [phi, ori, gF, zeroGate, hca, hcb, hax, hbx] <;> done)
    | (refine ⟨3, funext fun x => ?_⟩; cases hax : a (Function.update x p v) <;> cases hbx : b (Function.update x p v) <;> simp [phi, ori, gF, zeroGate, hca, hcb, hax, hbx])

theorem UC_phi (p : Fin 8) (v : Bool) :
    ∀ (t : ℕ) (S S' : BF → Prop) (f : BF),
      (∀ w, S w → phi p v w = zF ∨ S' (phi p v w)) → phi p v f ≠ zF →
      UC gF (fun _ => True) t S f → UC gF (fun _ => True) t S' (phi p v f)
  | 0, _, _, f, hS, hf, hu => (hS f hu).resolve_left hf
  | t + 1, S, S', f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, _, ha, hb, tail⟩
    · exact Or.inl (UC_phi p v t S S' f hS hf hu)
    · obtain ⟨k', hk'⟩ := phi_gF p v k a b
      rcases hS a ha with ha0 | ha1
      · refine Or.inl (UC_phi p v t _ S' f ?_ hf tail)
        rintro w (rfl | hw)
        · rw [hk', ha0]
          rcases gF_zero_left k' (phi p v b) with e | e
          · exact Or.inl e
          · rw [e]; exact hS b hb
        · exact hS w hw
      rcases hS b hb with hb0 | hb1
      · refine Or.inl (UC_phi p v t _ S' f ?_ hf tail)
        rintro w (rfl | hw)
        · rw [hk', hb0]
          rcases gF_zero_right k' (phi p v a) with e | e
          · exact Or.inl e
          · rw [e]; exact Or.inr ha1
        · exact hS w hw
      · refine Or.inr ⟨k', phi p v a, phi p v b, trivial, ha1, hb1, UC_phi p v t _ _ f ?_ hf tail⟩
        rintro w (rfl | hw)
        · exact Or.inr (Or.inl hk')
        · exact (hS w hw).imp id Or.inr

theorem kill_left (p : Fin 8) (k : Fin 4) : ∃ b : Bool, ∀ y : BF, phi p b (gF k (var p) y) = zF := by
  fin_cases k
  · exact ⟨false, fun y => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩
  · exact ⟨true, fun y => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩
  · exact ⟨false, fun y => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩
  · exact ⟨true, fun y => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩

theorem kill_right (p : Fin 8) (k : Fin 4) : ∃ b : Bool, ∀ x : BF, phi p b (gF k x (var p)) = zF := by
  fin_cases k
  · exact ⟨false, fun a => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩
  · exact ⟨true, fun a => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩
  · exact ⟨true, fun a => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩
  · exact ⟨false, fun a => funext fun x => by simp [phi, ori, gF, var, zeroGate, zF]⟩

def Good (p : Fin 8) (S : BF → Prop) : Prop := ∀ w, S w → w = var p ∨ Fix p w

theorem phase2 (p : Fin 8) (b : Bool) (f : BF) (hf1 : phi p b f ≠ zF) (hf2 : ¬ Fix p f) :
    ∀ (t : ℕ) (S : BF → Prop) (s : BF), Good p S → phi p b s = zF →
      UC gF (fun _ => True) t (fun w => w = s ∨ S w) f →
      ∃ t', t' + 1 ≤ t ∧ UC gF (fun _ => True) t' (fun w => S w ∧ w ≠ var p) (phi p b f) := by
  have noMem : ∀ (S : BF → Prop) (s : BF), Good p S → phi p b s = zF →
      (f = s ∨ S f) → False := by
    rintro S s hG hs (rfl | hf)
    · exact hf1 hs
    · rcases hG f hf with rfl | hfx
      · exact hf1 (phi_var_self p b)
      · exact hf2 hfx
  intro t
  induction t with
  | zero => intro S s hG hs hu; exact (noMem S s hG hs hu).elim
  | succ t ih =>
    intro S s hG hs hu
    rcases hu with hu | ⟨k, a, c, _, ha, hc, tail⟩
    · obtain ⟨t', ht, hr⟩ := ih S s hG hs hu
      exact ⟨t', by omega, hr⟩
    · have cls : ∀ w, (w = s ∨ S w) → phi p b w = zF ∨ (S w ∧ Fix p w ∧ w ≠ var p) := by
        rintro w (rfl | hw)
        · exact Or.inl hs
        · rcases hG w hw with rfl | hfx
          · exact Or.inl (phi_var_self p b)
          · exact Or.inr ⟨hw, hfx, fun e => not_fix_var p (e ▸ hfx)⟩
      have drop : phi p b (gF k a c) = zF ∨
          (S (phi p b (gF k a c)) ∧ phi p b (gF k a c) ≠ var p) →
          ∃ t', t' + 1 ≤ t + 1 ∧ UC gF (fun _ => True) t' (fun w => S w ∧ w ≠ var p) (phi p b f) := by
        intro hg
        refine ⟨t, le_rfl, UC_phi p b t _ _ f ?_ hf1 tail⟩
        rintro w (rfl | hw)
        · exact hg
        · rcases cls w hw with h0 | ⟨hwS, hfx, hne⟩
          · exact Or.inl h0
          · rw [phi_fix hfx b]; exact Or.inr ⟨hwS, hne⟩
      rcases cls a ha with ha0 | ⟨haS, hafx, hane⟩
      · apply drop
        obtain ⟨k', hk'⟩ := phi_gF p b k a c
        rw [hk', ha0]
        rcases gF_zero_left k' (phi p b c) with e | e
        · exact Or.inl e
        · rw [e]
          rcases cls c hc with hc0 | ⟨hcS, hcfx, hcne⟩
          · exact Or.inl hc0
          · rw [phi_fix hcfx b]; exact Or.inr ⟨hcS, hcne⟩
      rcases cls c hc with hc0 | ⟨hcS, hcfx, hcne⟩
      · apply drop
        obtain ⟨k', hk'⟩ := phi_gF p b k a c
        rw [hk', hc0]
        rcases gF_zero_right k' (phi p b a) with e | e
        · exact Or.inl e
        · rw [e, phi_fix hafx b]; exact Or.inr ⟨haS, hane⟩
      · have hgfx : Fix p (gF k a c) := fix_gF k hafx hcfx
        have hG' : Good p (fun w => w = gF k a c ∨ S w) := by
          rintro w (rfl | hw)
          · exact Or.inr hgfx
          · exact hG w hw
        have tail' : UC gF (fun _ => True) t (fun w => w = s ∨ (w = gF k a c ∨ S w)) f :=
          UC_monoS t _ _ f (by rintro w (rfl | rfl | hw) <;> tauto) tail
        obtain ⟨t', ht, hr⟩ := ih (fun w => w = gF k a c ∨ S w) s hG' hs tail'
        refine ⟨t' + 1, by omega, UC_gate k a c trivial ⟨haS, hane⟩ ⟨hcS, hcne⟩ ?_⟩
        exact UC_monoS t' _ _ _ (by rintro w ⟨rfl | hw, hne⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hne⟩) hr

theorem two_gates (p : Fin 8) (f : BF) (h0 : phi p false f ≠ zF) (h1 : phi p true f ≠ zF)
    (hf : ¬ Fix p f) :
    ∀ (t : ℕ) (S : BF → Prop), Good p S → UC gF (fun _ => True) t S f →
      ∃ t', t' + 2 ≤ t ∧
        (UC gF (fun _ => True) t' (fun w => S w ∧ w ≠ var p) (phi p false f) ∨
         UC gF (fun _ => True) t' (fun w => S w ∧ w ≠ var p) (phi p true f)) := by
  have noMem : ∀ (S : BF → Prop), Good p S → S f → False := by
    intro S hG hSf
    rcases hG f hSf with rfl | hfx
    · exact h0 (phi_var_self p false)
    · exact hf hfx
  intro t
  induction t with
  | zero => intro S hG hu; exact (noMem S hG hu).elim
  | succ t ih =>
    intro S hG hu
    rcases hu with hu | ⟨k, a, c, _, ha, hc, tail⟩
    · obtain ⟨t', ht, hr⟩ := ih S hG hu
      exact ⟨t', by omega, hr⟩
    · have kill (b : Bool) (hkb : phi p b (gF k a c) = zF) :
          ∃ t', t' + 2 ≤ t + 1 ∧
            (UC gF (fun _ => True) t' (fun w => S w ∧ w ≠ var p) (phi p false f) ∨
             UC gF (fun _ => True) t' (fun w => S w ∧ w ≠ var p) (phi p true f)) := by
        cases b
        · obtain ⟨t', ht, hr⟩ := phase2 p false f h0 hf t S (gF k a c) hG hkb tail
          exact ⟨t', by omega, Or.inl hr⟩
        · obtain ⟨t', ht, hr⟩ := phase2 p true f h1 hf t S (gF k a c) hG hkb tail
          exact ⟨t', by omega, Or.inr hr⟩
      rcases hG a ha with rfl | hafx
      · obtain ⟨b, hb⟩ := kill_left p k
        exact kill b (hb c)
      rcases hG c hc with rfl | hcfx
      · obtain ⟨b, hb⟩ := kill_right p k
        exact kill b (hb a)
      · have hane : a ≠ var p := fun e => not_fix_var p (e ▸ hafx)
        have hcne : c ≠ var p := fun e => not_fix_var p (e ▸ hcfx)
        have hgfx : Fix p (gF k a c) := fix_gF k hafx hcfx
        have hG' : Good p (fun w => w = gF k a c ∨ S w) := by
          rintro w (rfl | hw)
          · exact Or.inr hgfx
          · exact hG w hw
        obtain ⟨t', ht, hr⟩ := ih (fun w => w = gF k a c ∨ S w) hG' tail
        refine ⟨t' + 1, by omega, ?_⟩
        rcases hr with hr | hr
        · exact Or.inl (UC_gate k a c trivial ⟨ha, hane⟩ ⟨hc, hcne⟩
            (UC_monoS t' _ _ _ (by rintro w ⟨rfl | hw, hne⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hne⟩) hr))
        · exact Or.inr (UC_gate k a c trivial ⟨ha, hane⟩ ⟨hc, hcne⟩
            (UC_monoS t' _ _ _ (by rintro w ⟨rfl | hw, hne⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hne⟩) hr))

def Lower (f : BF) (k : Nat) := ∀ t : Nat, UC gF (fun _ => True) t (sourceVars Finset.univ) f → k ≤ t

theorem zeroLower (f : BF) : Lower f 0 := fun _ _ => Nat.zero_le _

theorem payOne (f lo : BF) (p : Fin 8) (d : Nat) (bound : Lower lo d)
    (dep : ∃ x, rst p f x ≠ f x) (nz : rst p f ≠ zF) (eq : rst p f = lo) : Lower f (d+1) := by
  intro t h
  obtain ⟨q,ct,v⟩ := remove_var f p Finset.univ t dep nz h
  rw [eq] at v
  have mapped := UC_monoS q _ (sourceVars Finset.univ) _ (fun w hw => by
    obtain ⟨i, _, e⟩ := hw
    exact ⟨i,Finset.mem_univ _,e⟩) v
  have := bound q mapped
  omega

theorem payTwo (f lo hi : BF) (p : Fin 8) (d e : Nat) (below : Lower lo d) (above : Lower hi e)
    (nz0 : phi p false f ≠ zF) (nz1 : phi p true f ≠ zF) (dep : ¬ Fix p f)
    (eq0 : phi p false f = lo) (eq1 : phi p true f = hi) : Lower f (min d e + 2) := by
  intro t h
  have good : Good p (sourceVars Finset.univ) := by
    rintro w ⟨i,_,rfl⟩
    by_cases same : i = p
    · exact Or.inl (same ▸ rfl)
    · exact Or.inr (fix_var same)
  obtain ⟨q,ct,ha | hb⟩ := two_gates p f nz0 nz1 dep t _ good h
  · rw [eq0] at ha
    have b := below q (UC_monoS q _ _ _ (fun _ hw => hw.1) ha)
    omega
  · rw [eq1] at hb
    have b := above q (UC_monoS q _ _ _ (fun _ hw => hw.1) hb)
    omega

theorem cliqueFloor (f : BF) (nodes : Fin 4 → Fin 8) (onto : Fin 8 → Fin 4)
    (inj : Function.Injective nodes)
    (same : ∀ x : Fin 8 → Bool, f (x ∘ nodes ∘ onto) = f x)
    (sing : ∀ i, f (singleInput (nodes i)) = false)
    (pr : ∀ i j, i ≠ j → f (pairInput (nodes i) (nodes j)) = true) : Lower f 7 := by
  intro t h
  let trans (v : BF) : BF := fun x => v (x ∘ nodes ∘ onto)
  have hom : ∀ op a b, trans (gF op a b) = gF op (trans a) (trans b) := by intros; rfl
  have sources : ∀ v, sourceVars Finset.univ v → ∃ j, trans v = var (nodes j) := by
    rintro v ⟨i,_,rfl⟩
    exact ⟨onto i,rfl⟩
  have cut := PEqualNP.Outside.L_meta_49549.UC_map (G := gF) (G' := gF) (A := fun _ => True) trans hom t
    (sourceVars Finset.univ) (fun v => ∃ j, v = var (nodes j)) f sources h
  have e : trans f = f := funext same
  rw [e] at cut
  by_contra! small
  exact U4 nodes inj f sing pr (UC_le (by omega) cut)

end Cofactor

namespace SignedLift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev zeroGate := PEqualNP.Outside.L_meta_49549.zeroGate
abbrev UC {α : Type} := @PEqualNP.Outside.L_meta_49549.UC α
abbrev BF (n : Nat) := (Fin n → Bool) → Bool

def signed {n : Nat} (k : Fin 4) (a b : BF n) : BF n := fun x => zeroGate k (a x) (b x)

def binary (g : Gate) : Bool := match g.op with | .not => false | _ => true

def ready {n : Nat} (gs : List Gate) (j : Nat) (f : BF n) : Prop :=
  j < n + gs.length ∧ ∀ x : Fin n → Bool, Circuit.eval ⟨gs,j⟩ (List.ofFn x) = f x

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def addWire (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

theorem wireLength {n : Nat} (gs : List Gate) (x : Fin n → Bool) :
    (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).length = n + gs.length := by
  have aux (v : List Bool) (ls : List Gate) : (ls.foldl addWire v).length = v.length + ls.length := by
    induction ls generalizing v with
    | nil => simp
    | cons g ls ih => simp [List.foldl_cons,ih,addWire]; omega
  exact (aux _ _).trans (by simp)

theorem stepW (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g],0⟩ x = addWire (Circuit.wires ⟨gs,0⟩ x) g := by
  simp [Circuit.wires, addWire, List.foldl_append]

theorem keep {n j} {gs : List Gate} {f : BF n} (h : ready gs j f) (g : Gate) :
    ready (gs ++ [g]) j f := by
  refine ⟨by have := h.1; simp; omega, ?_⟩
  intro x
  change (Circuit.wires ⟨gs ++ [g],0⟩ _).getD j false = _
  rw [stepW]
  exact (List.getD_append _ _ _ _ (by rw [wireLength];exact h.1)).trans (h.2 x)

theorem nextWire {n} (gs : List Gate) (g : Gate) (f : BF n)
    (eval : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map (fun j =>
      (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD j false)) = f x) :
    ready (gs ++ [g]) (n + gs.length) f := by
  refine ⟨by simp, ?_⟩
  intro x
  change (Circuit.wires ⟨gs ++ [g],0⟩ _).getD (n + gs.length) false = _
  rw [stepW,← wireLength gs x]
  simpa [addWire] using eval x

theorem negative {n j} {gs : List Gate} {f : BF n} (h : ready gs j f) :
    ready (gs ++ [⟨.not,[j]⟩]) (n+gs.length) (fun x => !f x) := by
  apply nextWire
  intro x
  have hx : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD j false = f x := h.2 x
  simp only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,hx]

theorem conjWire {n i j} {gs : List Gate} {a b : BF n} (ha : ready gs i a) (hb : ready gs j b) :
    ready (gs ++ [⟨.and,[i,j]⟩]) (n+gs.length) (fun x => a x && b x) := by
  apply nextWire
  intro x
  have h1 : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD i false = a x := ha.2 x
  have h2 : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD j false = b x := hb.2 x
  simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,h1,h2,Bool.and_true]

theorem disjWire {n i j} {gs : List Gate} {a b : BF n} (ha : ready gs i a) (hb : ready gs j b) :
    ready (gs ++ [⟨.or,[i,j]⟩]) (n+gs.length) (fun x => a x || b x) := by
  apply nextWire
  intro x
  have h1 : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD i false = a x := ha.2 x
  have h2 : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD j false = b x := hb.2 x
  simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,h1,h2,Bool.or_false]

theorem shift {n j} {gs : List Gate} {f : BF n} (h : ready gs j f) (tail : List Gate) :
    ready (gs ++ tail) j f := by
  induction tail using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton _ g ih => simpa [List.append_assoc] using keep ih g

theorem produce {n i j} {gs : List Gate} {a b : BF n} (k : Fin 4)
    (ha : ready gs i a) (hb : ready gs j b) :
    ∃ (tail : List Gate) (r : Nat), (∀ g ∈ tail, legal g) ∧ tail.countP binary = 1 ∧
      ready (gs ++ tail) r (signed k a b) := by
  fin_cases k
  · exact ⟨[⟨.and,[i,j]⟩],_,by simp [legal],rfl,conjWire ha hb⟩
  · exact ⟨[⟨.or,[i,j]⟩],_,by simp [legal],rfl,disjWire ha hb⟩
  · let v : Gate := ⟨.not,[j]⟩
    refine ⟨[v,⟨.and,[i,n+gs.length]⟩],n+(gs++[v]).length,by simp [legal,v],rfl,?_⟩
    change ready _ _ (fun x => a x && !(b x))
    simpa only [List.append_assoc,List.singleton_append] using conjWire (keep ha v) (negative hb)
  · let v : Gate := ⟨.not,[i]⟩
    refine ⟨[v,⟨.and,[n+gs.length,j]⟩],n+(gs++[v]).length,by simp [legal,v],rfl,?_⟩
    change ready _ _ (fun x => !(a x) && b x)
    simpa only [List.append_assoc,List.singleton_append] using conjWire (negative ha) (keep hb v)

theorem realizeAux {n t} (S : BF n → Prop) (f : BF n)
    (h : UC signed (fun _ => True) t S f) (gs : List Gate)
    (fan : ∀ g ∈ gs, legal g) (pool : ∀ w, S w → ∃ i, ready gs i w) :
    ∃ C : Circuit, FanInTwo C ∧ C.gates.countP binary ≤ gs.countP binary + t ∧ circuitFun n C = f := by
  induction t generalizing gs S with
  | zero =>
    obtain ⟨i,e⟩ := pool f h
    exact ⟨⟨gs,i⟩,fan,by simp,funext e.2⟩
  | succ t ih =>
    rcases h with skip | ⟨k,a,b,_,ha,hb,more⟩
    · obtain ⟨C,fanC,lo,eq⟩ := ih S skip gs fan pool
      exact ⟨C,fanC,by omega,eq⟩
    obtain ⟨i,hi⟩ := pool a ha
    obtain ⟨j,hj⟩ := pool b hb
    obtain ⟨tail,r,ok,cost,new⟩ := produce k hi hj
    obtain ⟨C,fanC,lo,eq⟩ := ih _ more (gs++tail)
      (fun g hg => (List.mem_append.mp hg).elim (fan g) (ok g)) (by
        rintro w (rfl | hw)
        · exact ⟨r,new⟩
        · obtain ⟨v,ev⟩ := pool w hw
          exact ⟨v,shift ev tail⟩)
    rw [List.countP_append,cost] at lo
    exact ⟨C,fanC,by omega,eq⟩

theorem realize {n t} (f : BF n)
    (h : UC signed (fun _ => True) t (fun w => ∃ i : Fin n, w = fun x => x i) f) :
    ∃ C : Circuit, FanInTwo C ∧ C.gates.countP binary ≤ t ∧ circuitFun n C = f := by
  have p : ∀ w : BF n, (∃ i : Fin n, w = fun x => x i) → ∃ j, ready [] j w := by
    rintro w ⟨i,rfl⟩
    exact ⟨i.val,by simp [ready,i.isLt,Circuit.eval,Circuit.wires]⟩
  simpa using realizeAux _ f h [] (by simp) p

end SignedLift
namespace Cofactor
theorem projectedFive (f : BF) (π : Fin 8 → Fin 5) (f5 : SignedLift.BF 5) (k : Nat)
    (low : ∀ C : Circuit, FanInTwo C → circuitFun 5 C = f5 → k ≤ C.gates.countP SignedLift.binary)
    (same : ∀ y : Fin 5 → Bool, f (y ∘ π) = f5 y) : Lower f k := by
  intro t h
  let lift (w : BF) : SignedLift.BF 5 := fun y => w (y ∘ π)
  have src : ∀ w, sourceVars Finset.univ w → ∃ j : Fin 5, lift w = fun y => y j := by
    rintro w ⟨i,_,rfl⟩
    exact ⟨π i,rfl⟩
  have hom : ∀ op a b, lift (gF op a b) = SignedLift.signed op (lift a) (lift b) := by intros; rfl
  have mapped := UC_map (G := gF) (G' := SignedLift.signed) (A := fun _ => True) lift hom t
    (sourceVars Finset.univ) (fun w => ∃ i : Fin 5, w = fun y => y i) f src h
  obtain ⟨C,fan,ct,hc⟩ := SignedLift.realize _ mapped
  have bound := low C fan (hc.trans (funext same))
  omega
theorem lowerK5 (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 5 C = FiveK5.table) :
    10 ≤ C.gates.countP SignedLift.binary := by
  have cert := FiveK5.ten_binary C.gates C.output (fun g hg => fan g hg) (fun x => congrFun eq x)
  have pred : SignedLift.binary = FiveK5.isBinary := by
    funext g
    rcases g with ⟨op,ins⟩
    cases op <;> rfl
  rw [pred, List.countP_eq_length_filter]
  change 10 ≤ FiveK5.binaryCost C.gates
  omega
end Cofactor

open Cofactor
def piece0 (x : Fin 8 → Bool) : Bool := (x 1 && x 3) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)
theorem boundpiece0 : Cofactor.Lower piece0 10 := by
  let back : Fin 8 → Fin 5 := ![0, 0, 0, 1, 0, 2, 3, 4]
  apply Cofactor.projectedFive piece0 back FiveK5.table 10 Cofactor.lowerK5
  decide +kernel

def piece1 (x : Fin 8 → Bool) : Bool := (x 1 && x 3) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)
theorem boundpiece1 : Cofactor.Lower piece1 11 := by
  exact Cofactor.payOne piece1 piece0 2 10 boundpiece0 ⟨assignment 132, by decide⟩ (fun e => (by decide : (rst 2 piece1) (assignment 10) ≠ zF (assignment 10)) (congrFun e _)) (funext fun x => (by decide +kernel : ∀ y : Fin 8 → Bool, (rst 2 piece1) y = piece0 y) x)

def piece2 (x : Fin 8 → Bool) : Bool := x 2 || (x 1 && x 3) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)
theorem boundpiece2 : Cofactor.Lower piece2 11 := by
  exact Cofactor.payOne piece2 piece0 2 10 boundpiece0 ⟨assignment 4, by decide⟩ (fun e => (by decide : (rst 2 piece2) (assignment 10) ≠ zF (assignment 10)) (congrFun e _)) (funext fun x => (by decide +kernel : ∀ y : Fin 8 → Bool, (rst 2 piece2) y = piece0 y) x)

def piece3 (x : Fin 8 → Bool) : Bool := (x 1 && x 3) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 4) || (x 2 && x 7) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)
theorem boundpiece3 : Cofactor.Lower piece3 13 := by
  exact Cofactor.payTwo piece3 piece1 piece2 4 11 11 boundpiece1 boundpiece2
    (fun e => (by decide : (Cofactor.phi 4 false piece3) (assignment 10) ≠ zF (assignment 10)) (congrFun e _)) (fun e => (by decide : (Cofactor.phi 4 true piece3) (assignment 4) ≠ zF (assignment 4)) (congrFun e _))
    (fun h => (by decide : piece3 (Function.update (assignment 20) 4 false) ≠ piece3 (assignment 20)) (h.1 false (assignment 20)))
    (funext fun x => (by decide +kernel : ∀ y : Fin 8 → Bool, (Cofactor.phi 4 false piece3) y = piece1 y) x) (funext fun x => (by decide +kernel : ∀ y : Fin 8 → Bool, (Cofactor.phi 4 true piece3) y = piece2 y) x)

def piece4 (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 3) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 4) || (x 2 && x 7) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)
theorem boundpiece4 : Cofactor.Lower piece4 14 := by
  exact Cofactor.payOne piece4 piece3 0 13 boundpiece3 ⟨assignment 9, by decide⟩ (fun e => (by decide : (rst 0 piece4) (assignment 10) ≠ zF (assignment 10)) (congrFun e _)) (funext fun x => (by decide +kernel : ∀ y : Fin 8 → Bool, (rst 0 piece4) y = piece3 y) x)

def target8 (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 3) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 4) || (x 2 && x 7) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)
def witness : List Gate := [⟨.or, [5, 6]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [13, 4]⟩, ⟨.and, [12, 7]⟩, ⟨.and, [10, 9]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [20, 17]⟩, ⟨.or, [21, 18]⟩]
theorem witnessBasis : ∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness, 22⟩ (List.ofFn x) = target8 x := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 8 → Bool, target8 x = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem circuitLower (gates : List Gate) (o : ℕ) (legal : GOK gates)
    (comp : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = target8 x)
    (hasNot : ∃ g ∈ gates, g.op = GateOp.not) : 15 ≤ gates.length := by
  have hg : (wiresF gates (List.ofFn var)).getD o zF = target8 := by
    funext x
    rw [← comp x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, List.map_ofFn]
    rfl
  have start := trans_binary gates (List.ofFn var) (sourceVars Finset.univ) legal (by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
    exact Or.inr ⟨i, Finset.mem_univ i, ori_zp rfl⟩) o
  rw [hg, ori_zp (show target8 (fun _ => false) = false by decide)] at start
  rcases start with e | run
  · exact False.elim ((by decide : target8 (assignment 9) ≠ zF (assignment 9)) (congrFun e _))
  have eq : target8 = piece4 := by funext x; exact (by decide +kernel : ∀ y : Fin 8 → Bool, target8 y = piece4 y) x
  rw [eq] at run
  have lowerCount := boundpiece4 (countBinary gates) run
  have := countBinary_lt gates hasNot
  omega
end PEqualNP.Outside.L_meta_49549
open PEqualNP.Outside.L_meta_49549 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_49549 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have comp : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = target8 x := fun x => (computes x).trans (graph_correct x).symm
    have large := circuitLower gates o legal comp hnot
    have hw : witness.length ≤ 15 := by decide
    exact ⟨witness, 22, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨ops, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases ops with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hnot ⟨g,hg,h⟩)
