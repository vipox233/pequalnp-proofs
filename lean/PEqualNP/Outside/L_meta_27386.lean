import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_27386
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Sig := Nat × Nat

def top : Nat := 0x7ffffff
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (top ^^^ a.1, top ^^^ a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (allowNot : Bool) (a : Sig) : Nat :=
  if allowNot then a.1 ^^^ a.2 else a.1 &&& (top ^^^ a.2)
def cuts (allowNot : Bool) (ws : List Sig) : Nat :=
  ws.foldr (fun w v => sep allowNot w ||| v) 0

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def bounded (n : Nat) : Prop := ∀ i, 27 ≤ i → n.testBit i = false
def valid (a : Sig) : Prop := bounded a.1 ∧ bounded a.2

def rawInputs : List Sig :=
  [(0x533b800, 0x521a88a), (0x2cc05c0, 0x2980564), (0x186c63f, 0x1868e17), (0x2c8c600, 0xc07704), (0x770043f, 0x6500c3b), (0x38779c0, 0x3875180), (0x40781ff, 0x40780ec), (0x607fe00, 0x626f900), (0x7f80000, 0x3782230)]

theorem testBit_top (i : Nat) : top.testBit i = decide (i < 27) := by
  have h : top = 2 ^ 27 - 1 := by decide
  rw [h, Nat.testBit_two_pow_sub_one]

theorem bounded_of_lt {n : Nat} (h : n < 2 ^ 27) : bounded n := fun i hi =>
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hi))

theorem bounded_zero : bounded 0 := fun i _ => by simp
theorem bounded_top : bounded top := fun i hi => by rw [testBit_top]; simp [Nat.not_lt.mpr hi]
theorem bounded_and {x y : Nat} (hx : bounded x) : bounded (x &&& y) := fun i hi => by
  simp [Nat.testBit_and, hx i hi]
theorem bounded_or {x y : Nat} (hx : bounded x) (hy : bounded y) : bounded (x ||| y) := fun i hi => by
  simp [Nat.testBit_or, hx i hi, hy i hi]
theorem bounded_xor {x y : Nat} (hx : bounded x) (hy : bounded y) : bounded (x ^^^ y) := fun i hi => by
  simp [Nat.testBit_xor, hx i hi, hy i hi]

theorem nat_eq_of_testBit {x y : Nat} (hx : bounded x) (hy : bounded y)
    (h : ∀ i < 27, x.testBit i = y.testBit i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 27
  · exact h i hi
  · rw [hx i (by omega), hy i (by omega)]

theorem valid_zero : valid zero := ⟨bounded_zero, bounded_zero⟩
theorem valid_one : valid one := ⟨bounded_top, bounded_top⟩
theorem valid_target : valid target := ⟨bounded_top, bounded_zero⟩
theorem valid_neg {a : Sig} (ha : valid a) : valid (neg a) :=
  ⟨bounded_xor bounded_top ha.1, bounded_xor bounded_top ha.2⟩
theorem valid_bin {d : Bool} {a b : Sig} (ha : valid a) (hb : valid b) : valid (bin d a b) := by
  cases d
  · exact ⟨bounded_and ha.1, bounded_and ha.2⟩
  · exact ⟨bounded_or ha.1 hb.1, bounded_or ha.2 hb.2⟩

theorem valid_sep {allowNot : Bool} {a : Sig} (ha : valid a) : bounded (sep allowNot a) := by
  cases allowNot
  · exact bounded_and ha.1
  · exact bounded_xor ha.1 ha.2

theorem bounded_cuts {allowNot : Bool} {ws : List Sig} (hw : ∀ w ∈ ws, valid w) :
    bounded (cuts allowNot ws) := by
  induction ws with
  | nil => exact bounded_zero
  | cons a rest ih =>
    exact bounded_or (valid_sep (hw a (by simp))) (ih fun w h => hw w (by simp [h]))

theorem neg_neg {a : Sig} (ha : valid a) : neg (neg a) = a := by
  apply Prod.ext
  · apply nat_eq_of_testBit (bounded_xor bounded_top (bounded_xor bounded_top ha.1)) ha.1
    intro i _; simp
  · apply nat_eq_of_testBit (bounded_xor bounded_top (bounded_xor bounded_top ha.2)) ha.2
    intro i _; simp

theorem neg_zero : neg zero = one := by decide
theorem neg_one : neg one = zero := by decide

theorem proper_neg {a : Sig} (ha : valid a) (hp : proper a) : proper (neg a) := by
  constructor
  · intro h
    have := congrArg neg h
    rw [neg_neg ha, neg_zero] at this
    exact hp.2 this
  · intro h
    have := congrArg neg h
    rw [neg_neg ha, neg_one] at this
    exact hp.1 this

theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin, Nat.and_comm, Nat.or_comm]

theorem bin_zero_left (d : Bool) (a : Sig) : bin d zero a = if d then a else zero := by
  cases d <;> simp [bin, zero]

theorem bin_zero_right (d : Bool) (a : Sig) : bin d a zero = if d then a else zero := by
  rw [bin_comm, bin_zero_left]

theorem bin_one_left (d : Bool) {a : Sig} (ha : valid a) : bin d one a = if d then one else a := by
  cases d
  · apply Prod.ext
    · apply nat_eq_of_testBit (bounded_and bounded_top) ha.1
      intro i hi; simp [Nat.testBit_and, testBit_top, hi]
    · apply nat_eq_of_testBit (bounded_and bounded_top) ha.2
      intro i hi; simp [Nat.testBit_and, testBit_top, hi]
  · apply Prod.ext
    · apply nat_eq_of_testBit (bounded_or bounded_top ha.1) bounded_top
      intro i hi; simp [Nat.testBit_or, testBit_top, hi]
    · apply nat_eq_of_testBit (bounded_or bounded_top ha.2) bounded_top
      intro i hi; simp [Nat.testBit_or, testBit_top, hi]

theorem bin_one_right (d : Bool) {a : Sig} (ha : valid a) : bin d a one = if d then one else a := by
  rw [bin_comm, bin_one_left d ha]

theorem bin_self (d : Bool) (a : Sig) : bin d a a = a := by
  cases d <;> simp [bin, Nat.and_self, Nat.or_self]

def build : ℕ → Finset Sig → Prop
  | 0, av => target ∈ av
  | k+1, av =>
      build k av ∨
      (∃ a ∈ av, proper a ∧ build k (insert (neg a) av)) ∨
      (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ proper a ∧ proper b ∧
        ∃ d : Bool, proper (bin d a b) ∧ build k (insert (bin d a b) av))

def live : ℕ → ℕ → Finset Sig → Prop
  | 0, t, s => t = 0 ∧ s = {target}
  | k+1, t, s =>
      live k t s ∨
      (t > 0 ∧ ∃ a ∈ s, proper a ∧ neg a ∉ s ∧
        ∃ rest : Finset Sig, s = insert a rest ∧ live k (t - 1) (insert (neg a) rest)) ∨
      (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ proper a ∧ proper b ∧
        ∃ d : Bool, proper (bin d a b) ∧ bin d a b ∉ s ∧
          ∃ rest : Finset Sig, s = insert a (insert b rest) ∧ live k t (insert (bin d a b) rest))

theorem compress {k : ℕ} {av : Finset Sig} (h : build k av) :
    ∃ t, ∃ s ⊆ av, live k t s := by
  induction k generalizing av with
  | zero =>
    exact ⟨0, {target}, Finset.singleton_subset_iff.mpr h, rfl, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, hpa, tail⟩ | ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, tail⟩
    · obtain ⟨t, s, hs, hrun⟩ := ih skip
      exact ⟨t, s, hs, Or.inl hrun⟩
    · obtain ⟨t, s', hs', hrun⟩ := ih tail
      by_cases sub : s' ⊆ av
      · exact ⟨t, s', sub, Or.inl hrun⟩
      · have hzmem : neg a ∈ s' := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (hs' hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : neg a ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ hs')
        let rest := s'.erase (neg a)
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (hs' hu'.2)).resolve_left hu'.1
        let s := insert a rest
        have hs : s ⊆ av := Finset.insert_subset ha hrest
        refine ⟨t + 1, s, hs, Or.inr (Or.inl ⟨by omega, a, by simp [s], hpa,
          fun hm => hzout (hs hm), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun
    · obtain ⟨t, s', hs', hrun⟩ := ih tail
      by_cases sub : s' ⊆ av
      · exact ⟨t, s', sub, Or.inl hrun⟩
      · have hzmem : bin d a b ∈ s' := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (hs' hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : bin d a b ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ hs')
        let rest := s'.erase (bin d a b)
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (hs' hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ av := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨t, s, hs, Or.inr (Or.inr ⟨a, by simp [s], b, by simp [s], hab, hpa, hpb, d, hpz,
          fun hm => hzout (hs hm), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {k t : ℕ} {s : Finset Sig} (h : live k t s) : s.card + t ≤ k + 1 := by
  induction k generalizing t s with
  | zero =>
    obtain ⟨rfl, rfl⟩ := h
    simp
  | succ k ih =>
    rcases h with skip | ⟨ht, a, _, _, hout, rest, rfl, tail⟩ |
        ⟨a, _, b, _, _, _, _, d, _, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : neg a ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a rest
      omega
    · have hzrest : bin d a b ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

def differs (allowNot : Bool) (i : Fin 27) (w : Sig) : Prop :=
  if allowNot then w.1.testBit i.val ≠ w.2.testBit i.val
  else w.1.testBit i.val = true ∧ w.2.testBit i.val = false

theorem differs_mono {b : Bool} {i : Fin 27} {w : Sig} (h : differs b i w) :
    differs true i w := by
  cases b
  · simp only [differs, ite_true] at h ⊢
    rw [h.1, h.2]; decide
  · exact h

theorem differs_target (allowNot : Bool) (i : Fin 27) : differs allowNot i target := by
  cases allowNot <;> simp [differs, target, testBit_top, i.isLt]

theorem differs_neg {b : Bool} {i : Fin 27} {a : Sig} (h : differs b i (neg a)) :
    differs true i a := by
  have h' := differs_mono h
  simp only [differs, ite_true, neg, Nat.testBit_xor, testBit_top, i.isLt, decide_true] at h' ⊢
  cases ha1 : a.1.testBit i.val <;> cases ha2 : a.2.testBit i.val <;> simp_all

theorem differs_bin {b d : Bool} {i : Fin 27} {a c : Sig} (h : differs b i (bin d a c)) :
    differs b i a ∨ differs b i c := by
  cases b <;> cases d <;>
    simp only [differs, bin, Bool.false_eq_true, ite_true, ite_false] at h ⊢ <;>
    (try simp only [Nat.testBit_and] at h) <;>
    (try simp only [Nat.testBit_or] at h) <;>
    cases ha1 : a.1.testBit i.val <;> cases ha2 : a.2.testBit i.val <;>
    cases hc1 : c.1.testBit i.val <;> cases hc2 : c.2.testBit i.val <;> simp_all

theorem live_separates (i : Fin 27) {k t : ℕ} {s : Finset Sig} (h : live k t s) :
    ∃ w ∈ s, differs (decide (0 < t)) i w := by
  induction k generalizing t s with
  | zero =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨target, by simp, differs_target false i⟩
  | succ k ih =>
    rcases h with skip | ⟨ht, a, ha, _, _, rest, rfl, tail⟩ |
        ⟨a, ha, b, hb, _, _, _, d, _, _, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      have hdt : decide (0 < t) = true := by simp [ht]
      rw [hdt]
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨a, ha, differs_neg hD⟩
      · exact ⟨w, by simp [hw], differs_mono hD⟩
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases differs_bin hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {k t : ℕ} {s : Finset Sig} (h : live (k+1) t s) :
    (t = 0 ∧ s = {target}) ∨
    (t > 0 ∧ ∃ a ∈ s, proper a ∧ neg a ∉ s ∧
      ∃ rest : Finset Sig, s = insert a rest ∧ live k (t - 1) (insert (neg a) rest)) ∨
    (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ proper a ∧ proper b ∧
      ∃ d : Bool, proper (bin d a b) ∧ bin d a b ∉ s ∧
        ∃ rest : Finset Sig, s = insert a (insert b rest) ∧ live k t (insert (bin d a b) rest)) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step1 | step2
    · rcases ih skip with done | ⟨ht, a, ha, hpa, hn, r, hs, tail⟩ |
          ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, hn, r, hs, tail⟩
      · exact Or.inl done
      · exact Or.inr (Or.inl ⟨ht, a, ha, hpa, hn, r, hs, Or.inl tail⟩)
      · exact Or.inr (Or.inr ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, hn, r, hs, Or.inl tail⟩)
    · exact Or.inr (Or.inl step1)
    · exact Or.inr (Or.inr step2)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with rfl | hb'
      · obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) ha'
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha' hb'
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

theorem testBit_sep (allowNot : Bool) (w : Sig) (i : Fin 27) :
    (sep allowNot w).testBit i.val = true ↔ differs allowNot i w := by
  cases allowNot
  · simp only [sep, differs, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_xor,
      testBit_top, i.isLt, decide_true]
    cases w.1.testBit i.val <;> cases w.2.testBit i.val <;> simp
  · simp only [sep, differs, ite_true, Nat.testBit_xor]
    cases w.1.testBit i.val <;> cases w.2.testBit i.val <;> simp

theorem cuts_spec (allowNot : Bool) (ws : List Sig) (i : Fin 27) :
    (cuts allowNot ws).testBit i.val = true ↔ ∃ w ∈ ws, differs allowNot i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep allowNot a ||| cuts allowNot rest).testBit i.val = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, testBit_sep]
    simp

theorem cuts_full {k t : ℕ} {ws : List Sig} (hv : ∀ w ∈ ws, valid w)
    (h : live k t ws.toFinset) : cuts (decide (0 < t)) ws = top := by
  apply nat_eq_of_testBit (bounded_cuts hv) bounded_top
  intro j hj
  have hw := live_separates ⟨j, hj⟩ h
  have hbit := (cuts_spec (decide (0 < t)) ws ⟨j, hj⟩).mpr (by simpa using hw)
  rw [hbit, testBit_top]
  simp [hj]

theorem recover_kept1 {ws r : List Sig} {a : Sig} {needed : Finset Sig}
    (hp : ws.Perm (a :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a needed) :
    ∃ kept ∈ [r, a :: r], kept.Nodup ∧ kept.toFinset = needed := by
  have har := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a r.toFinset := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a := by
    intro v
    have he : v ∈ insert a r.toFinset ↔ v ∈ insert a needed := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons] at har
    grind
  by_cases ha : a ∈ needed
  · refine ⟨a :: r, by simp, har, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp, (List.nodup_cons.mp har).2, ?_⟩
    ext v; simp [henne]; grind

def keepChoices (a b : Sig) (r : List Sig) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept2 {ws r : List Sig} {a b : Sig} {needed : Finset Sig}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : v ∈ insert a (insert b r.toFinset) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List Sig} (hn : ws.Nodup) (hs : ws.toFinset = {target}) :
    ws = [target] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatchUnary (extra : ℕ) (tNext : ℕ) (ws : List Sig) (next : List Sig → Bool)
    (a : Sig) (rest : List Sig) : Bool :=
  let na := neg a
  if na == zero || na == one || ws.contains na then false
  else
    let allowNext := tNext != 0
    let base := cuts allowNext rest
    let v := sep allowNext na ||| base
    ((v == top) && next (na :: rest)) ||
    ((extra != 0) && (v ||| sep allowNext a == top) && next (na :: a :: rest))

def dispatchBin (extra : ℕ) (allowNot : Bool) (ws : List Sig) (next : List Sig → Bool)
    (a b : Sig) (rest : List Sig) : Bool :=
  let base := cuts allowNot rest
  let sa := sep allowNot a
  let sb := sep allowNot b
  let tryZ (z : Sig) : Bool :=
    if z == zero || z == one || ws.contains z then false
    else
      let v := sep allowNot z ||| base
      ((v == top) && next (z :: rest)) ||
      ((extra != 0) && (((v ||| sa == top) && next (z :: a :: rest)) ||
                        ((v ||| sb == top) && next (z :: b :: rest)))) ||
      ((extra ≥ 2) && (v ||| sa ||| sb == top) && next (z :: a :: b :: rest))
  tryZ (bin false a b) || tryZ (bin true a b)

def search : ℕ → ℕ → List Sig → Bool
  | 0, t, ws => (t == 0) && (ws == [target])
  | k+1, t, ws =>
      ((t == 0) && (ws == [target])) ||
      (if t == 0 then false
       else
         let extra := k + 2 - ws.length - t
         (singles ws).any (fun (a, rest) => dispatchUnary extra (t - 1) ws (search k (t - 1)) a rest)) ||
      (let extra := k + 2 - ws.length - t
       let allowNot := t != 0
       (pairs ws).any (fun (a, b, rest) => dispatchBin extra allowNot ws (search k t) a b rest))

theorem dispatchUnary_complete {k tNext : ℕ} {ws r kept : List Sig} {a : Sig}
    (next : List Sig → Bool)
    (hp : proper (neg a)) (hout : neg a ∉ ws)
    (hk : kept ∈ [r, a :: r])
    (he : k + 2 - ws.length - (tNext + 1) = k + 1 - r.length - (tNext + 1))
    (hlen : kept.length + tNext ≤ k)
    (hc : cuts (decide (0 < tNext)) (neg a :: kept) = top)
    (ht : next (neg a :: kept) = true) :
    dispatchUnary (k + 2 - ws.length - (tNext + 1)) tNext ws next a r = true := by
  have hcond : (neg a == zero || neg a == one || ws.contains (neg a)) = false := by
    simp [hp.1, hp.2, hout]
  dsimp only [dispatchUnary]
  rw [hcond]
  simp only [Bool.false_eq_true, ite_false]
  have hallow : (tNext != 0) = decide (0 < tNext) := by cases tNext <;> rfl
  rw [hallow]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · simp only [cuts, List.foldr_cons] at hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact Or.inl ⟨hc, ht⟩
  · simp only [cuts, List.foldr_cons] at hc
    simp only [List.length_cons] at hlen
    have hex : (k + 2 - ws.length - (tNext + 1) != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; omega
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    refine Or.inr ⟨⟨hex, ?_⟩, ht⟩
    calc (sep (decide (0 < tNext)) (neg a) ||| cuts (decide (0 < tNext)) r) ||| sep (decide (0 < tNext)) a
        = sep (decide (0 < tNext)) (neg a) ||| (sep (decide (0 < tNext)) a ||| cuts (decide (0 < tNext)) r) := by
          ac_rfl
      _ = top := hc

theorem dispatchBin_complete {k t : ℕ} {ws r kept : List Sig} {a b : Sig} {d : Bool}
    (next : List Sig → Bool)
    (hpz : proper (bin d a b)) (hout : bin d a b ∉ ws)
    (hk : kept ∈ keepChoices a b r)
    (he : k + 2 - ws.length - t = k - r.length - t)
    (hlen : kept.length + t ≤ k)
    (hc : cuts (decide (0 < t)) (bin d a b :: kept) = top)
    (ht : next (bin d a b :: kept) = true) :
    dispatchBin (k + 2 - ws.length - t) (t != 0) ws next a b r = true := by
  have hallow : (t != 0) = decide (0 < t) := by cases t <;> rfl
  dsimp only [dispatchBin]
  rw [hallow]
  have hcond : (bin d a b == zero || bin d a b == one || ws.contains (bin d a b)) = false := by
    simp [hpz.1, hpz.2, hout]
  have htry : (if (bin d a b == zero || bin d a b == one || ws.contains (bin d a b)) = true then false else
      let v := sep (decide (0 < t)) (bin d a b) ||| cuts (decide (0 < t)) r
      ((v == top) && next (bin d a b :: r)) ||
      ((k + 2 - ws.length - t != 0) &&
        (((v ||| sep (decide (0 < t)) a == top) && next (bin d a b :: a :: r)) ||
         ((v ||| sep (decide (0 < t)) b == top) && next (bin d a b :: b :: r)))) ||
      ((k + 2 - ws.length - t ≥ 2) &&
        (v ||| sep (decide (0 < t)) a ||| sep (decide (0 < t)) b == top) &&
        next (bin d a b :: a :: b :: r))) = true := by
    rw [hcond]
    simp only [Bool.false_eq_true, ite_false]
    simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;>
      simp only [cuts, List.foldr_cons] at hc <;>
      (try simp only [List.length_cons] at hlen) <;>
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq]
    · exact Or.inl (Or.inl ⟨hc, ht⟩)
    · refine Or.inl (Or.inr ⟨by omega, Or.inl ⟨?_, ht⟩⟩)
      calc (sep (decide (0 < t)) (bin d a b) ||| cuts (decide (0 < t)) r) ||| sep (decide (0 < t)) a
          = sep (decide (0 < t)) (bin d a b) ||| (sep (decide (0 < t)) a ||| cuts (decide (0 < t)) r) := by ac_rfl
        _ = top := hc
    · refine Or.inl (Or.inr ⟨by omega, Or.inr ⟨?_, ht⟩⟩)
      calc (sep (decide (0 < t)) (bin d a b) ||| cuts (decide (0 < t)) r) ||| sep (decide (0 < t)) b
          = sep (decide (0 < t)) (bin d a b) ||| (sep (decide (0 < t)) b ||| cuts (decide (0 < t)) r) := by ac_rfl
        _ = top := hc
    · refine Or.inr ⟨⟨by omega, ?_⟩, ht⟩
      calc ((sep (decide (0 < t)) (bin d a b) ||| cuts (decide (0 < t)) r) ||| sep (decide (0 < t)) a) ||| sep (decide (0 < t)) b
          = sep (decide (0 < t)) (bin d a b) ||| (sep (decide (0 < t)) a ||| (sep (decide (0 < t)) b ||| cuts (decide (0 < t)) r)) := by ac_rfl
        _ = top := hc
  cases d
  · exact Bool.or_eq_true _ _ |>.mpr (Or.inl htry)
  · exact Bool.or_eq_true _ _ |>.mpr (Or.inr htry)

theorem search_complete (k t : ℕ) (ws : List Sig) (hn : ws.Nodup) (hv : ∀ w ∈ ws, valid w)
    (h : live k t ws.toFinset) : search k t ws = true := by
  induction k generalizing t ws with
  | zero =>
    obtain ⟨rfl, hs⟩ := h
    simp [search, singleton_list hn hs]
  | succ k ih =>
    rcases first_live h with ⟨rfl, hs⟩ |
        ⟨ht, a, ha, hpa, hout, needed, hs, tail⟩ |
        ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, hout, needed, hs, tail⟩
    · simp [search, singleton_list hn hs]
    · obtain ⟨r, hm, hp⟩ := pick_one (List.mem_toFinset.mp ha)
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept1 hp hn hs
      have hznew : neg a ∉ kept := by
        intro hu
        apply hout
        rw [hs]
        exact Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)
      have hnd : (neg a :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl : live k (t - 1) (neg a :: kept).toFinset := by
        simpa [hfin] using tail
      have hv_kept : ∀ w ∈ neg a :: kept, valid w := by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact valid_neg (hv a (List.mem_toFinset.mp ha))
        · apply hv w
          apply List.mem_toFinset.mp
          rw [hs]
          exact Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hw)
      have hcard := live_card hl
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hcard
      have hlen_ws : ws.length = r.length + 1 := by
        have := hp.length_eq; simp at this; exact this
      cases t with
      | zero => omega
      | succ t' =>
        simp only [Nat.add_sub_cancel] at hl hcard
        have hrec := ih t' (neg a :: kept) hnd hv_kept hl
        have hcut := cuts_full hv_kept hl
        have hdisp := dispatchUnary_complete (k := k) (tNext := t') (ws := ws) (r := r) (kept := kept)
          (a := a) (search k t') (proper_neg (hv a (List.mem_toFinset.mp ha)) hpa)
          (fun hmem => hout (List.mem_toFinset.mpr hmem)) hk (by omega) (by omega) hcut hrec
        simp only [search, Bool.or_eq_true, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          beq_iff_eq, ite_false, Nat.add_sub_cancel]
        exact Or.inl (Or.inr (List.any_eq_true.mpr ⟨(a, r), hm, hdisp⟩))
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : Sig} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed))
          (ha' : a ∈ ws) (hb' : b ∈ ws)
          (hpz' : proper (bin d a b)) (hout' : bin d a b ∉ ws.toFinset)
          (htail : live k t (insert (bin d a b) needed)) :
          dispatchBin (k + 2 - ws.length - t) (t != 0) ws (search k t) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept2 perm hn hset
        have hznew : bin d a b ∉ kept := by
          intro hu
          apply hout'
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
        have hnd : (bin d a b :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live k t (bin d a b :: kept).toFinset := by
          simpa [hfin] using htail
        have hv_kept : ∀ w ∈ bin d a b :: kept, valid w := by
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact valid_bin (hv a ha') (hv b hb')
          · apply hv w
            apply List.mem_toFinset.mp
            rw [hset]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hw))
        have hcard := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hcard
        have hlen_ws : ws.length = r.length + 2 := by
          have := perm.length_eq; simp at this; exact this
        exact dispatchBin_complete (k := k) (t := t) (ws := ws) (r := r) (kept := kept)
          (a := a) (b := b) (d := d) (search k t) hpz'
          (fun hmem => hout' (List.mem_toFinset.mpr hmem)) hk (by omega) (by omega)
          (cuts_full hv_kept hl) (ih t (bin d a b :: kept) hnd hv_kept hl)
      simp only [search, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hpz hout tail⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
          (List.mem_toFinset.mp hb) (List.mem_toFinset.mp ha)
          (bin_comm d a b ▸ hpz) (bin_comm d a b ▸ hout) (bin_comm d a b ▸ tail)⟩

private def possible (w : List Sig) (z : Sig) : Bool :=
  z == zero || z == one || w.any (fun u => z == u || z == neg u ||
    w.any (fun v => z == bin false u v || z == bin true u v))

private def bit (k : Fin 54) (z : Sig) : Bool :=
  if k.val < 27 then z.2.testBit k.val else z.1.testBit (k.val - 27)

private theorem read_bit (w : List Sig) (i : ℕ) (k : Fin 54) :
    (w.map (bit k)).getD i false = bit k (w.getD i zero) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit, zero]

private theorem read_wire (w : List Sig) (i : ℕ) : w.getD i zero = zero ∨ w.getD i zero ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem bit_zero (k : Fin 54) : bit k zero = false := by
  unfold bit zero; split <;> simp

private theorem bit_one (k : Fin 54) : bit k one = true := by
  unfold bit one
  by_cases h : k.val < 27
  · simp [h, testBit_top]
  · simp [h, testBit_top, show k.val - 27 < 27 by omega]

private theorem bit_neg (k : Fin 54) (z : Sig) : bit k (neg z) = !(bit k z) := by
  unfold bit neg
  by_cases h : k.val < 27
  · simp [h, Nat.testBit_xor, testBit_top]
  · simp [h, Nat.testBit_xor, testBit_top, show k.val - 27 < 27 by omega]

private theorem bit_and (k : Fin 54) (x y : Sig) : bit k (bin false x y) = (bit k x && bit k y) := by
  unfold bit bin
  split <;> simp [Nat.testBit_and]

private theorem bit_or (k : Fin 54) (x y : Sig) : bit k (bin true x y) = (bit k x || bit k y) := by
  unfold bit bin
  split <;> simp [Nat.testBit_or]

private theorem atom {ws : List Sig} {x : Sig} (hx : x = zero ∨ x ∈ ws) :
    possible ws x ∧ possible ws (neg x) := by
  rcases hx with rfl | hx
  · simp [possible, neg_zero]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair_possible {ws : List Sig} {x y : Sig} (hx : x = zero ∨ x ∈ ws) (hy : y = zero ∨ y ∈ ws) :
    possible ws (bin false x y) ∧ possible ws (bin true x y) := by
  rcases hx with rfl | hx
  · simpa [bin_zero_left] using (show possible ws zero ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [bin_zero_right] using (show possible ws zero ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w : List Sig) (hwv : ∀ u ∈ w, valid u) (g : Gate) (hg : legal g) :
    ∃ z, valid z ∧ possible w z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i zero = zero ∨ w.getD i zero ∈ w := read_wire w i
  have vmem (i : ℕ) : valid (w.getD i zero) := by
    rcases mem i with h | h
    · rw [h]; exact valid_zero
    · exact hwv _ h
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨one, valid_one, by simp [possible], by intro k; simp [step, GateOp.eval, bit_one]⟩
    · exact ⟨zero, valid_zero, by simp [possible], by intro k; simp [step, GateOp.eval, bit_zero]⟩
    · exact ⟨one, valid_one, by simp [possible], by intro k; simp [step, GateOp.eval, bit_one]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, vmem i, (atom (mem i)).1, by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, vmem i, (atom (mem i)).1, by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, valid_neg (vmem i), (atom (mem i)).2, by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit_neg]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, valid_bin (vmem i) (vmem j), (pair_possible (mem i) (mem j)).1,
            by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit_and]⟩
        · exact ⟨_, valid_bin (vmem i) (vmem j), (pair_possible (mem i) (mem j)).2,
            by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit_or]⟩
        · exact ⟨_, valid_neg (vmem i), (atom (mem i)).2,
            by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit_neg]⟩

def represents (av : Finset Sig) (w : List Sig) : Prop :=
  ∀ u ∈ w, u = zero ∨ u = one ∨ u ∈ av

theorem classify {av : Finset Sig} {ws : List Sig}
    (hav : ∀ u ∈ av, proper u ∧ valid u)
    (hw : represents av ws) {z : Sig} (hz : possible ws z) :
    z = zero ∨ z = one ∨ z ∈ av ∨
      (∃ a ∈ av, proper a ∧ z = neg a) ∨
      (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ proper a ∧ proper b ∧ ∃ d : Bool, proper z ∧ z = bin d a b) := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((rfl | rfl) | ⟨x, hx, (rfl | rfl) | ⟨y, hy, hh⟩⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · rcases hw z hx with rfl | rfl | hxm
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl hxm))
  · rcases hw x hx with rfl | rfl | hxm
    · exact Or.inr (Or.inl neg_zero)
    · exact Or.inl neg_one
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hxm, (hav x hxm).1, rfl⟩)))
  · have binCase (d : Bool) :
        bin d x y = zero ∨ bin d x y = one ∨ bin d x y ∈ av ∨
        (∃ a ∈ av, proper a ∧ bin d x y = neg a) ∨
        (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ proper a ∧ proper b ∧ ∃ d' : Bool, proper (bin d x y) ∧ bin d x y = bin d' a b) := by
      have hvx : valid x := by
        rcases hw x hx with rfl | rfl | hxm
        · exact valid_zero
        · exact valid_one
        · exact (hav x hxm).2
      have hvy : valid y := by
        rcases hw y hy with rfl | rfl | hym
        · exact valid_zero
        · exact valid_one
        · exact (hav y hym).2
      rcases hw x hx with rfl | rfl | hxm
      · rw [bin_zero_left]; cases d
        · exact Or.inl rfl
        · rcases hw y hy with rfl | rfl | hym
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl hym))
      · rw [bin_one_left d hvy]; cases d
        · rcases hw y hy with rfl | rfl | hym
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl hym))
        · exact Or.inr (Or.inl rfl)
      rcases hw y hy with rfl | rfl | hym
      · rw [bin_zero_right]; cases d
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl hxm))
      · rw [bin_one_right d hvx]; cases d
        · exact Or.inr (Or.inr (Or.inl hxm))
        · exact Or.inr (Or.inl rfl)
      by_cases hxy : x = y
      · subst hxy; rw [bin_self]; exact Or.inr (Or.inr (Or.inl hxm))
      · by_cases hz0 : bin d x y = zero
        · exact Or.inl hz0
        · by_cases hz1 : bin d x y = one
          · exact Or.inr (Or.inl hz1)
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hxm, y, hym, hxy, (hav x hxm).1, (hav y hym).1, d, ⟨hz0, hz1⟩, rfl⟩)))
    rcases hh with rfl | rfl
    · exact binCase false
    · exact binCase true

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List Sig) (av : Finset Sig)
    (hwv : ∀ u ∈ w, valid u) (hav : ∀ u ∈ av, proper u ∧ valid u) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k target) :
    build gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hvout : valid (w.getD out zero) := by
      rcases read_wire w out with h | h
      · rw [h]; exact valid_zero
      · exact hwv _ h
    have hval : w.getD out zero = target := by
      apply Prod.ext
      · apply nat_eq_of_testBit hvout.1 valid_target.1
        intro i hi
        have hk := he ⟨27 + i, by omega⟩
        simp only [List.foldl_nil, read_bit, bit, show ¬(27 + i < 27) by omega, ite_false,
          Nat.add_sub_cancel_left] at hk
        exact hk
      · apply nat_eq_of_testBit hvout.2 valid_target.2
        intro i hi
        have hk := he ⟨i, by omega⟩
        simp only [List.foldl_nil, read_bit, bit, hi, ite_true] at hk
        exact hk
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : target ≠ zero) hz)
    · rcases hw target hm with hz | ho | hmem
      · exact False.elim ((by decide : target ≠ zero) hz)
      · exact False.elim ((by decide : target ≠ one) ho)
      · exact hmem
  | cons g gs ih =>
    obtain ⟨z, hvz, hz, hstep⟩ := gate_table w hwv g (hg g (by simp))
    have hwv' : ∀ u ∈ w ++ [z], valid u := by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hwv u h
      · rw [List.mem_singleton.mp h]; exact hvz
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k target := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = zero ∨ z = one ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw u old
      · rw [List.mem_singleton.mp fresh]; exact h
    rcases classify hav hw hz with h0 | h1 | hmem | ⟨a, ha, hpa, rfl⟩ |
        ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, rfl⟩
    · exact Or.inl (fn av hwv' hav (appendOK (.inl h0)) he')
    · exact Or.inl (fn av hwv' hav (appendOK (.inr (.inl h1))) he')
    · exact Or.inl (fn av hwv' hav (appendOK (.inr (.inr hmem))) he')
    · refine Or.inr (Or.inl ⟨a, ha, hpa, fn (insert (neg a) av) hwv' ?_ ?_ he'⟩)
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ⟨proper_neg (hav a ha).2 hpa, valid_neg (hav a ha).2⟩
        · exact hav u hu
      · intro u hu
        rcases List.mem_append.mp hu with old | fresh
        · rcases hw u old with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Finset.mem_insert_of_mem h))
        · rw [List.mem_singleton.mp fresh]; exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
    · refine Or.inr (Or.inr ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, fn (insert (bin d a b) av) hwv' ?_ ?_ he'⟩)
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ⟨hpz, valid_bin (hav a ha).2 (hav b hb).2⟩
        · exact hav u hu
      · intro u hu
        rcases List.mem_append.mp hu with old | fresh
        · rcases hw u old with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Finset.mem_insert_of_mem h))
        · rw [List.mem_singleton.mp fresh]; exact Or.inr (Or.inr (Finset.mem_insert_self _ _))

theorem rawInputs_valid : ∀ u ∈ rawInputs, valid u := by
  have h : rawInputs.all (fun u => decide (u.1 < 2 ^ 27) && decide (u.2 < 2 ^ 27)) = true := by decide
  intro u hu
  have h' := List.all_eq_true.mp h u hu
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact ⟨bounded_of_lt h'.1, bounded_of_lt h'.2⟩

theorem rawInputs_proper : ∀ u ∈ rawInputs, proper u := by
  have h : rawInputs.all (fun u => (u != zero) && (u != one)) = true := by decide
  intro u hu
  have h' := List.all_eq_true.mp h u hu
  simp only [Bool.and_eq_true, bne_iff_ne] at h'
  exact h'

def matching (x : Fin 9 → Bool) := ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

def samples : List Nat := [20, 21, 78, 81, 276, 338, 66, 97, 170, 268, 30, 149, 168, 393, 168, 197, 97, 228, 228, 258, 274, 385, 280, 46, 293, 434, 209, 84, 84, 84, 84, 84, 84, 98, 98, 98, 140, 158, 161, 161, 161, 172, 205, 225, 229, 230, 266, 273, 273, 282, 302, 309, 442, 465]

def sample (k : Fin 54) (i : Fin 9) := (samples.getD k.val 0).testBit i.val

def first : Gate := ⟨.and, [0, 1]⟩
def second : Gate := ⟨.or, [3, 9]⟩
def copied : Sig := rawInputs.getD 3 zero

theorem copied_mem : copied ∈ rawInputs := by decide

def afterPrefix := rawInputs ++ [zero, copied]

theorem sample_check : ∀ k : Fin 54,
    step (step (List.ofFn (sample k)) first) second = afterPrefix.map (bit k) ∧
    matching (sample k) = bit k target := by decide +kernel

private theorem tail_build (gs : List Gate) (out : Nat)
    (hg : FanInTwo ⟨first :: second :: gs, out⟩)
    (he : ∀ x : Fin 9 → Bool, (Circuit.eval ⟨first :: second :: gs, out⟩ (List.ofFn x)) = matching x) :
    build gs.length rawInputs.toFinset := by
  apply compile gs out (fun g h => hg g (by simp [h])) afterPrefix rawInputs.toFinset
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact rawInputs_valid w h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact valid_zero
      · exact rawInputs_valid copied copied_mem
  · intro u hu
    exact ⟨rawInputs_proper u (List.mem_toFinset.mp hu), rawInputs_valid u (List.mem_toFinset.mp hu)⟩
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact Or.inr (Or.inr (List.mem_toFinset.mpr h))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (List.mem_toFinset.mpr copied_mem))
  · intro k
    rw [← (sample_check k).1, ← (sample_check k).2]
    exact he (sample k)
theorem extend_live {m n t : ℕ} {S : Finset Sig} (le : m ≤ n) (h : live m t S) :
    live n t S := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

def inputsAt (m : Nat) : List Sig :=
  ((rawInputs.zipIdx).filter (fun p => m.testBit p.2)).map Prod.fst

def candidates : List (Nat × List Sig) := rawInputs.sublists.flatMap fun ws =>
  ((List.range (12 - ws.length)).filter fun t => cuts (decide (0 < t)) ws == top).map (fun t => (t,ws))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checked : candidates.all (fun p => !(search 10 p.1 p.2)) = true := by decide +kernel

theorem excluded (gs : List Gate) (out : Nat) (hs : gs.length ≤ 10)
    (hg : FanInTwo ⟨first :: second :: gs, out⟩)
    (he : ∀ x : Fin 9 → Bool, Circuit.eval ⟨first :: second :: gs, out⟩ (List.ofFn x) = matching x) :
    False := by
  have noCase : ∀ p ∈ candidates, search 10 p.1 p.2 = false := by
    intro p hp
    simpa using List.all_eq_true.mp checked p hp
  obtain ⟨t, S, hsub, hLive⟩ := compress (tail_build gs out hg he)
  let ws := rawInputs.filter (fun s => decide (s ∈ S))
  have hS : ws.toFinset = S := by
    ext v
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩⟩
  have hn : ws.Nodup := (by decide : rawInputs.Nodup).filter _
  have hv : ∀ x ∈ ws, valid x := fun x hx => rawInputs_valid x (List.mem_filter.mp hx).1
  have live10 : live 10 t ws.toFinset := hS ▸ extend_live hs hLive
  have hcut := cuts_full hv live10
  have hcard := live_card live10
  rw [List.toFinset_card_of_nodup hn] at hcard
  have hm : (t,ws) ∈ candidates := by
    apply List.mem_flatMap.mpr
    refine ⟨ws, List.mem_sublists.mpr List.filter_sublist, List.mem_map.mpr ⟨t, ?_, rfl⟩⟩
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simp [hcut]⟩
  exact Bool.noConfusion ((noCase _ hm).symm.trans (search_complete 10 t ws hn hv live10))

end PEqualNP.Outside.L_meta_27386

open PEqualNP.Outside.L_meta_27386

theorem PEqualNP.Outside.L_meta_27386 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩)) := by
  rintro ⟨⟨gs, out⟩, hg, hs, he, _, _, _, _, ha, hb⟩
  cases gs with
  | nil => simp at ha
  | cons a gs =>
    cases gs with
    | nil => simp at hb
    | cons b rest =>
      change some a = some first at ha
      change some b = some second at hb
      obtain rfl := Option.some.inj ha
      obtain rfl := Option.some.inj hb
      apply excluded rest out _ hg he
      change rest.length + 1 + 1 ≤ 12 at hs
      omega
