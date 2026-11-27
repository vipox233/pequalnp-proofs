import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_055

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev Signal (m : Nat) := (Fin m → Bool) → Prop

def Bank (m : Nat) := {gs : List Gate // Monotone2 ⟨gs, 0⟩ ∧ ReadsBack m ⟨gs, 0⟩}

variable {m : Nat}

def Bank.gates (B : Bank m) : List Gate := B.1

theorem Bank.mono (B : Bank m) : Monotone2 ⟨B.gates, 0⟩ := B.2.1

theorem Bank.back (B : Bank m) : ReadsBack m ⟨B.gates, 0⟩ := B.2.2

def Bank.val (B : Bank m) (i : Nat) (x : Fin m → Bool) : Bool :=
  ((⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)).getD i false

def Bank.Has (B : Bank m) (f : Signal m) : Prop :=
  ∃ i < m + B.gates.length, ∀ x, B.val i x = true ↔ f x

def Bank.Ext (B D : Bank m) : Prop := ∀ {f}, B.Has f → D.Has f

def Bank.Grow (B : Bank m) (cost : Nat) (P : Bank m → Prop) : Prop :=
  ∃ D, B.Ext D ∧ D.gates.length ≤ B.gates.length + cost ∧ P D

def Bank.empty (m : Nat) : Bank m := ⟨[], by simp [Monotone2], by simp [ReadsBack]⟩

theorem Bank.input (i : Fin m) : (Bank.empty m).Has (fun x => x i = true) := by
  refine ⟨i, i.isLt, fun x => ?_⟩
  simp [Bank.val, Bank.gates, Bank.empty, Circuit.wires, List.getD_eq_getElem?_getD, i.isLt]

theorem Bank.Has.congr {B : Bank m} {f g : Signal m} (h : B.Has f)
    (e : ∀ x, f x ↔ g x) : B.Has g := by
  obtain ⟨i, hi, hh⟩ := h
  exact ⟨i, hi, fun x => (hh x).trans (e x)⟩

theorem Bank.Grow.pure (B : Bank m) {P : Bank m → Prop} (h : P B) : B.Grow 0 P :=
  ⟨B, fun h => h, by omega, h⟩

theorem Bank.Grow.weaken {B : Bank m} {P Q : Bank m → Prop} {a b : Nat} (h : B.Grow a P)
    (hab : a ≤ b) (hPQ : ∀ D, P D → Q D) : B.Grow b Q := by
  obtain ⟨D, e, c, t⟩ := h
  exact ⟨D, e, by omega, hPQ D t⟩

theorem Bank.Grow.bind {B : Bank m} {P Q : Bank m → Prop} {a b : Nat} (h : B.Grow a P)
    (f : ∀ D, B.Ext D → P D → D.Grow b Q) : B.Grow (a + b) Q := by
  obtain ⟨D, e, c, t⟩ := h
  obtain ⟨E, e', c', t'⟩ := f D e t
  exact ⟨E, fun h => e' (e h), by omega, t'⟩

theorem wireLength (gs : List Gate) (x : List Bool) :
    ((⟨gs, 0⟩ : Circuit).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires, List.foldl_append] at ih ⊢
    omega

theorem Bank.gate (B : Bank m) (g : Gate)
    (ok : g.op ∈ ({GateOp.and, .or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (back : ∀ i ∈ g.inputs, i < m + B.gates.length) :
    B.Grow 1 (fun D => D.Has (fun x => g.op.eval (g.inputs.map fun i => B.val i x) = true)) := by
  let D : Bank m := ⟨B.gates ++ [g],
      by
        intro g' h
        change g' ∈ B.gates ++ [g] at h
        rcases List.mem_append.mp h with h | h
        · exact B.mono g' h
        · exact (List.mem_singleton.mp h) ▸ ok,
      by
        intro j hj w hw
        change j < (B.gates ++ [g]).length at hj
        change w ∈ ((B.gates ++ [g]).getD j _).inputs at hw
        by_cases h : j < B.gates.length
        · rw [List.getD_append _ _ _ _ h] at hw
          exact B.back j h w hw
        · have he : j = B.gates.length := by simp at hj; omega
          subst j
          simp at hw
          exact back w hw⟩
  have hv (x : Fin m → Bool) :
      ((⟨D.gates, 0⟩ : Circuit).wires (List.ofFn x)) =
        ((⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)) ++
          [g.op.eval (g.inputs.map fun i => B.val i x)] := by
    simp [D, Bank.gates, Bank.val, Circuit.wires, List.foldl_append]
  have hl (x : Fin m → Bool) :
      ((⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)).length = m + B.gates.length := by
    simp [wireLength]
  refine ⟨D, ?_, by simp [D, Bank.gates], m + B.gates.length, by simp [D, Bank.gates], ?_⟩
  · intro f hf
    obtain ⟨i, hi, he⟩ := hf
    refine ⟨i, by simpa only [D, Bank.gates, List.length_append, List.length_singleton] using
      (show i < m + (B.gates.length + 1) by omega), fun x => ?_⟩
    unfold Bank.val
    rw [hv, List.getD_append _ _ _ _ (by rw [hl]; exact hi)]
    exact he x
  · intro x
    unfold Bank.val
    rw [hv, ← hl x]
    simp [Bank.val, List.getD_eq_getElem?_getD]

theorem Bank.constFalse (B : Bank m) : B.Grow 1 (fun D => D.Has (fun _ => False)) := by
  simpa [GateOp.eval] using B.gate ⟨.or, []⟩ (by simp) (by simp)

theorem Bank.constTrue (B : Bank m) : B.Grow 1 (fun D => D.Has (fun _ => True)) := by
  simpa [GateOp.eval] using B.gate ⟨.and, []⟩ (by simp) (by simp)

theorem Bank.meet {B : Bank m} {f g : Signal m} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x ∧ g x)) := by
  obtain ⟨i, hi, he⟩ := a
  obtain ⟨j, hj, hf⟩ := b
  simpa [GateOp.eval, he, hf] using B.gate ⟨.and, [i, j]⟩ (by simp) (by simp [hi, hj])

theorem Bank.join {B : Bank m} {f g : Signal m} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x ∨ g x)) := by
  obtain ⟨i, hi, he⟩ := a
  obtain ⟨j, hj, hf⟩ := b
  simpa [GateOp.eval, he, hf] using B.gate ⟨.or, [i, j]⟩ (by simp) (by simp [hi, hj])

theorem Bank.collectList {α : Type} (B : Bank m) (l : List α) (cost : Nat) (P : α → Bank m → Prop)
    (mono : ∀ {U V : Bank m}, U.Ext V → ∀ i, P i U → P i V)
    (emit : ∀ D : Bank m, B.Ext D → ∀ i ∈ l, D.Grow cost (P i)) :
    B.Grow (l.length * cost) (fun D => ∀ i ∈ l, P i D) := by
  induction l with
  | nil => simpa using (Bank.Grow.pure B (P := fun D => ∀ i ∈ ([] : List α), P i D) (by simp))
  | cons a l ih =>
    have t := ih (fun D e i hi => emit D e i (by simp [hi]))
    have out := t.bind (b := cost) (Q := fun E => ∀ i ∈ a :: l, P i E) (by
      intro D e haveL
      obtain ⟨E, e', c', ha⟩ := emit D e a (by simp)
      refine ⟨E, e', c', ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | h
      · exact ha
      · exact mono e' i (haveL i h))
    simpa [Nat.succ_mul] using out

theorem Bank.collect {α : Type} [Fintype α] (B : Bank m) (f : α → Signal m) (cost : Nat)
    (h : ∀ D : Bank m, B.Ext D → ∀ i, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (Fintype.card α * cost) (fun E => ∀ i, E.Has (f i)) := by
  classical
  simpa using B.collectList (Finset.univ : Finset α).toList cost (fun i D => D.Has (f i))
    (fun e _ hi => e hi) (fun D e i _ => h D e i)

theorem Bank.anyList {α : Type} (B : Bank m) (f : α → Signal m) (l : List α)
    (hf : ∀ i, B.Has (f i)) (hz : B.Has (fun _ => False)) :
    B.Grow l.length (fun D => D.Has (fun x => ∃ i ∈ l, f i x)) := by
  induction l with
  | nil => exact Bank.Grow.pure B (hz.congr (by simp))
  | cons a l ih =>
    apply ih.bind (b := 1)
    intro D e h
    apply (Bank.join (e (hf a)) h).weaken le_rfl
    intro E out
    exact out.congr (by simp)

theorem Bank.anyOf {α : Type} [Fintype α] (B : Bank m) (f : α → Signal m)
    (hf : ∀ i, B.Has (f i)) (hz : B.Has (fun _ => False)) :
    B.Grow (Fintype.card α) (fun D => D.Has (fun x => ∃ i, f i x)) := by
  classical
  simpa using B.anyList f (Finset.univ : Finset α).toList hf hz

theorem Bank.twoWays {B : Bank m} {f g : Bool → Signal m}
    (hf : ∀ b, B.Has (f b)) (hg : ∀ b, B.Has (g b)) :
    B.Grow 3 (fun D => D.Has (fun x => ∃ b, f b x ∧ g b x)) := by
  apply (Bank.meet (hf false) (hg false)).bind (b := 2)
  intro D e h₀
  apply (Bank.meet (e (hf true)) (e (hg true))).bind (b := 1)
  intro E e' h₁
  exact (Bank.join (e' h₀) h₁).weaken le_rfl (fun _ h => h.congr (fun x => by rw [Bool.exists_bool]))

theorem Bank.dot {α : Type} [Fintype α] (B : Bank m) (f g : α → Signal m)
    (hf : ∀ i, B.Has (f i)) (hg : ∀ i, B.Has (g i)) (hz : B.Has (fun _ => False)) :
    B.Grow (2 * Fintype.card α) (fun D => D.Has (fun x => ∃ i, f i x ∧ g i x)) := by
  let terms (i : α) : Signal m := fun x => f i x ∧ g i x
  have h := B.collect terms 1 (fun _ e i => Bank.meet (e (hf i)) (e (hg i)))
  have seq := h.bind (b := Fintype.card α) (Q := fun D => D.Has (fun x => ∃ i, f i x ∧ g i x))
    (fun D e hs => D.anyOf terms hs (e hz))
  exact seq.weaken (by simp; omega) (fun _ h => h)

abbrev Bits (w : Nat) := Fin w → Bool

def front {w : Nat} (p : Bits (w + 1)) : Bits w := Fin.init p
def rear {w : Nat} (p : Bits (w + 1)) : Bits w := Fin.tail p

def incoming {w : Nat} (v : Bits w) (b : Bool) : Bits (w + 1) :=
  Fin.cons (α := fun _ => Bool) b v

def outgoing {w : Nat} (u : Bits w) (b : Bool) : Bits (w + 1) :=
  Fin.snoc (α := fun _ => Bool) u b

abbrev Rules (w : Nat) := Nat → Bits (w + 1) → Prop

def Arc {w : Nat} (A : Rules w) (k : Nat) (u v : Bits w) : Prop :=
  ∃ p, front p = u ∧ rear p = v ∧ A k p

def Path {w : Nat} (A : Rules w) (off len : Nat) (u v : Bits w) : Prop :=
  ∃ q : Nat → Bits w, q 0 = u ∧ q len = v ∧ ∀ j < len, Arc A (off + j) (q j) (q (j + 1))

theorem pathZero {w} (A : Rules w) (off : Nat) (u v : Bits w) :
    Path A off 0 u v ↔ u = v := by
  constructor
  · rintro ⟨q, hu, hv, _⟩
    exact hu.symm.trans hv
  · rintro rfl
    exact ⟨fun _ => u, rfl, rfl, by simp⟩

theorem pathOne {w} (A : Rules w) (off : Nat) (u v : Bits w) :
    Path A off 1 u v ↔ Arc A off u v := by
  constructor
  · rintro ⟨q, hu, hv, h⟩
    simpa [hu, hv] using h 0 (by decide)
  · intro h
    refine ⟨fun i => if i = 0 then u else v, by simp, by simp, ?_⟩
    intro j hj
    obtain rfl : j = 0 := by omega
    simpa using h

theorem pathAdd {w} (A : Rules w) (off a b : Nat) (u v : Bits w) :
    Path A off (a + b) u v ↔ ∃ z, Path A off a u z ∧ Path A (off + a) b z v := by
  constructor
  · rintro ⟨q, hu, hv, h⟩
    refine ⟨q a, ⟨q, hu, rfl, fun j hj => h j (by omega)⟩,
      fun j => q (a + j), by simp, hv, ?_⟩
    intro j hj
    simpa [Nat.add_assoc] using h (a + j) (by omega)
  · rintro ⟨z, ⟨p, hp, pe, hs⟩, ⟨q, hq, qe, ht⟩⟩
    let f (j : Nat) := if j < a then p j else q (j - a)
    have left (j : Nat) (hj : j ≤ a) : f j = p j := by
      by_cases small : j < a
      · simp [f, small]
      · obtain rfl : j = a := by omega
        simp [f, pe, hq]
    have right (j : Nat) (hj : a ≤ j) : f j = q (j - a) := by simp [f, Nat.not_lt.mpr hj]
    refine ⟨f, (left 0 (by omega)).trans hp, ?_, ?_⟩
    · rw [right _ (by omega), Nat.add_sub_cancel_left, qe]
    · intro j hj
      by_cases low : j < a
      · rw [left _ (by omega), left _ (by omega)]
        exact hs j low
      · rw [right _ (by omega), right _ (by omega)]
        have h := ht (j - a) (by omega)
        rwa [show off + a + (j - a) = off + j by omega, show j - a + 1 = j + 1 - a by omega] at h

theorem pathForward {w} (A : Rules w) (off len : Nat) (u v : Bits w) :
    Path A off (len + 1) u v ↔
      ∃ b, Path A off len u (front (incoming v b)) ∧ A (off + len) (incoming v b) := by
  rw [pathAdd]
  simp only [pathOne]
  constructor
  · rintro ⟨t, h, p, hf, hr, ha⟩
    have eqn : incoming v (p 0) = p := by rw [← hr]; exact Fin.cons_self_tail p
    exact ⟨p 0, by rwa [eqn, hf], by rwa [eqn]⟩
  · rintro ⟨b, h, ha⟩
    exact ⟨_, h, incoming v b, rfl, Fin.tail_cons .., ha⟩

theorem pathBackward {w} (A : Rules w) (off len : Nat) (u v : Bits w) :
    Path A off (len + 1) u v ↔
      ∃ b, A off (outgoing u b) ∧ Path A (off + 1) len (rear (outgoing u b)) v := by
  rw [show len + 1 = 1 + len by omega, pathAdd]
  simp only [pathOne]
  constructor
  · rintro ⟨t, ⟨p, hf, hr, ha⟩, h⟩
    have eqn : outgoing u (p (Fin.last w)) = p := by rw [← hf]; exact Fin.snoc_init_self p
    exact ⟨p (Fin.last w), by rwa [eqn], by rwa [eqn, hr]⟩
  · rintro ⟨b, ha, h⟩
    exact ⟨_, ⟨outgoing u b, Fin.init_snoc .., rfl, ha⟩, h⟩

theorem pathChange {w} {A B : Rules w} {off len : Nat} {u v : Bits w}
    (e : ∀ k, off ≤ k → k < off + len → ∀ p, A k p ↔ B k p) :
    Path A off len u v ↔ Path B off len u v := by
  have move {S T : Rules w} (h : ∀ k, off ≤ k → k < off + len → ∀ p, S k p → T k p) :
      Path S off len u v → Path T off len u v := by
    rintro ⟨q, h₀, h₁, each⟩
    refine ⟨q, h₀, h₁, fun j hj => ?_⟩
    obtain ⟨p, hf, hr, hp⟩ := each j hj
    exact ⟨p, hf, hr, h _ (by omega) (by omega) _ hp⟩
  exact ⟨move (fun k l r p => (e k l r p).mp), move (fun k l r p => (e k l r p).mpr)⟩

def forceRow {w} (A : Rules w) (k : Nat) (p : Bits (w + 1)) : Rules w :=
  fun t q => if t = k then q = p else A t q

theorem cutCycle {n w} (A : Rules w) (i : Fin n) (p : Bits (w + 1)) :
    (∃ s, Path (forceRow A i.val p) 0 n s s) ↔
      ∃ s, Path A 0 i.val s (front p) ∧ Path A (i.val + 1) (n - (i.val + 1)) (rear p) s := by
  let F := forceRow A i.val p
  have left (u v) : Path F 0 i.val u v ↔ Path A 0 i.val u v := by
    apply pathChange
    intro k _ hr q
    simp [F, forceRow, show k ≠ i.val by omega]
  have right (u v) : Path F (i.val + 1) (n - (i.val + 1)) u v ↔
      Path A (i.val + 1) (n - (i.val + 1)) u v := by
    apply pathChange
    intro k hl _ q
    simp [F, forceRow, show k ≠ i.val by omega]
  have middle (u v) : Arc F i.val u v ↔ front p = u ∧ rear p = v := by
    simp [Arc, F, forceRow]
  have full (s) : Path F 0 n s s ↔
      ∃ v, Path F 0 (i.val + 1) s v ∧ Path F (i.val + 1) (n - (i.val + 1)) v s := by
    simpa only [Nat.add_sub_of_le i.isLt, Nat.zero_add] using
      pathAdd F 0 (i.val + 1) (n - (i.val + 1)) s s
  have penult (s v) : Path F 0 (i.val + 1) s v ↔
      ∃ u, Path F 0 i.val s u ∧ Arc F i.val u v := by
    rw [pathAdd]
    simp only [Nat.zero_add, pathOne]
  constructor
  · rintro ⟨s, h⟩
    obtain ⟨v, h₀, h₁⟩ := (full s).mp h
    obtain ⟨u, h₂, h₃⟩ := (penult s v).mp h₀
    obtain ⟨rfl, rfl⟩ := (middle u v).mp h₃
    exact ⟨s, (left ..).mp h₂, (right ..).mp h₁⟩
  · rintro ⟨s, h₀, h₁⟩
    exact ⟨s, (full s).mpr ⟨_, (penult ..).mpr ⟨_, (left ..).mpr h₀,
      (middle ..).mpr ⟨rfl, rfl⟩⟩, (right ..).mpr h₁⟩⟩

def rowIndex {n} (hn : 0 < n) (t : Nat) : Fin n := ⟨t % n, Nat.mod_lt _ hn⟩

def windowAt {n w} (hn : 0 < n) (word : Bits n) (k : Nat) : Bits (w + 1) :=
  fun j => word (rowIndex hn (k + j.val))

theorem cycleWord {n w} (hn : 0 < n) (A : Rules w) :
    (∃ s, Path A 0 n s s) ↔ ∃ word : Bits n, ∀ i : Fin n, A i.val (windowAt hn word i.val) := by
  constructor
  · rintro ⟨s, q, first, last, steps⟩
    have h (i : Fin n) : ∃ p, front p = q i.val ∧ rear p = q (i.val + 1) ∧ A i.val p := by
      simpa only [Nat.zero_add, Arc] using steps i.val i.isLt
    choose pats inits tails oks using h
    have stateStep (t : Nat) : q ((t + 1) % n) = q (t % n + 1) := by
      rw [← Nat.mod_add_mod t n 1]
      by_cases hlt : t % n + 1 < n
      · rw [Nat.mod_eq_of_lt hlt]
      · have hm := Nat.mod_lt t hn
        rw [show t % n + 1 = n by omega, Nat.mod_self]
        exact first.trans last.symm
    have hop (t : Nat) : rear (pats (rowIndex hn t)) = front (pats (rowIndex hn (t + 1))) :=
      (tails (rowIndex hn t)).trans ((stateStep t).symm.trans (inits (rowIndex hn (t + 1))).symm)
    have shift (j : Nat) (hj : j < w + 1) (t : Nat) :
        pats (rowIndex hn t) ⟨j, hj⟩ = pats (rowIndex hn (t + j)) 0 := by
      induction j generalizing t with
      | zero => rfl
      | succ j ih =>
        let a : Fin w := ⟨j, by omega⟩
        calc
          _ = pats (rowIndex hn (t + 1)) a.castSucc := congrFun (hop t) a
          _ = pats (rowIndex hn (t + 1 + j)) 0 := ih (by omega) _
          _ = _ := by rw [show t + 1 + j = t + (j + 1) by omega]
    let word : Bits n := fun i => pats i 0
    refine ⟨word, fun i => ?_⟩
    have hi : rowIndex hn i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    have hw : windowAt hn word i.val = pats i := by
      funext j
      exact (shift j.val j.isLt i.val).symm.trans (congrFun (congrArg pats hi) j)
    rw [hw]
    exact oks i
  · rintro ⟨word, h⟩
    let q (t : Nat) := front (windowAt hn word t : Bits (w + 1))
    refine ⟨q 0, q, rfl, ?_, ?_⟩
    · funext j
      change word (rowIndex hn (n + j.val)) = word (rowIndex hn (0 + j.val))
      congr 1
      apply Fin.ext
      simp [rowIndex]
    · intro k hk
      refine ⟨windowAt hn word k, rfl, ?_, ?_⟩
      · funext j
        change word (rowIndex hn (k + (j.val + 1))) = word (rowIndex hn ((k + 1) + j.val))
        rw [show k + (j.val + 1) = k + 1 + j.val by omega]
      · simpa only [Nat.zero_add] using h ⟨k, hk⟩

abbrev inputCount (n w : Nat) := n * 2 ^ (w + 1)
abbrev Table (n w : Nat) := Fin n → Bits (w + 1) → Bool

def patternCode {w : Nat} (p : Bits (w + 1)) : Fin (2 ^ (w + 1)) :=
  ⟨(BitVec.ofBoolListLE (List.ofFn p)).toNat, by simpa using (BitVec.ofBoolListLE (List.ofFn p)).isLt⟩

theorem patternBit {w : Nat} (p : Bits (w + 1)) (j : Fin (w + 1)) :
    (patternCode p).val.testBit j.val = p j := by
  change (BitVec.ofBoolListLE (List.ofFn p)).getLsbD j.val = p j
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),
    List.getElem_ofFn]

def address {n w} (i : Fin n) (p : Bits (w + 1)) : Fin (inputCount n w) :=
  ⟨i.val * 2 ^ (w + 1) + (patternCode p).val, by
    have h := Nat.mul_le_mul_right (2 ^ (w + 1)) (show i.val + 1 ≤ n from i.isLt)
    rw [Nat.add_mul, Nat.one_mul] at h
    have hp := (patternCode p).isLt
    unfold inputCount
    omega⟩

def flatInput {n w} (table : Table n w) (j : Fin (inputCount n w)) : Bool :=
  table ⟨j.val / 2 ^ (w + 1), (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr j.isLt⟩
    (fun k => (j.val % 2 ^ (w + 1)).testBit k.val)

theorem flatLookup {n w} (table : Table n w) (i : Fin n) (p : Nat)
    (hp : p < 2 ^ (w + 1)) (ha : i.val * 2 ^ (w + 1) + p < inputCount n w) :
    flatInput table ⟨i.val * 2 ^ (w + 1) + p, ha⟩ = table i (fun j => p.testBit j.val) := by
  simp [flatInput, Nat.mul_comm i.val, Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]

theorem flatList {n w} (table : Table n w) :
    List.ofFn (flatInput table) = (List.ofFn (fun i : Fin n => List.ofFn (fun p : Fin (2 ^ (w + 1)) =>
      table i (fun j => p.val.testBit j.val)))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext p
  exact flatLookup table i p.val p.isLt _

def tableRule {n w} (hn : 0 < n) (k : Nat) (p : Bits (w + 1)) (x : Fin (inputCount n w) → Bool) : Prop :=
  x (address (rowIndex hn k) p) = true

theorem readTable {n w} (hn : 0 < n) (table : Table n w) (i : Fin n) (p : Bits (w + 1)) :
    tableRule hn i.val p (flatInput table) ↔ table i p = true := by
  have hi : rowIndex hn i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  unfold tableRule
  rw [hi]
  change flatInput table ⟨_, _⟩ = true ↔ _
  rw [flatLookup table i _ (patternCode p).isLt, show (fun j => (patternCode p).val.testBit j.val) = p
    from funext (patternBit p)]

variable {w : Nat}

theorem cardBits (w : Nat) : Fintype.card (Bits w) = 2 ^ w := by
  simp [Bits]

theorem cardPairs (w : Nat) : Fintype.card (Bits w × Bits w) = 4 ^ w := by
  rw [Fintype.card_prod, cardBits, ← mul_pow]
  rfl

def segment (R : Nat → Bits (w + 1) → Signal m) (off len : Nat) (u v : Bits w) : Signal m :=
  fun x => Path (fun k p => R k p x) off len u v

theorem Bank.initial {B : Bank m} (R : Nat → Bits (w + 1) → Signal m) (off : Nat) (u v : Bits w)
    (ht : B.Has (fun _ => True)) (hf : B.Has (fun _ => False)) : B.Has (segment R off 0 u v) := by
  classical
  by_cases h : u = v
  · exact ht.congr (by simp [segment, pathZero, h])
  · exact hf.congr (by simp [segment, pathZero, h])

theorem Bank.levels (B : Bank m) (F : Nat → Bits w × Bits w → Signal m) (n : Nat)
    (base : ∀ a, B.Has (F 0 a))
    (step : ∀ k, k < n → ∀ D : Bank m, B.Ext D → (∀ a, D.Has (F k a)) →
      ∀ a, D.Grow 3 (fun E => E.Has (F (k + 1) a))) :
    B.Grow (n * (3 * 4 ^ w)) (fun D => ∀ k, k ≤ n → ∀ a, D.Has (F k a)) := by
  have levels (z : Nat) (hz : z ≤ n) :
      B.Grow (z * (3 * 4 ^ w)) (fun D => ∀ k, k ≤ z → ∀ a, D.Has (F k a)) := by
    induction z with
    | zero =>
      simp only [Nat.zero_mul]
      exact Bank.Grow.pure B (by simpa using base)
    | succ z ih =>
      have built := ih (by omega)
      have work := built.bind (b := Fintype.card (Bits w × Bits w) * 3)
        (Q := fun D => ∀ k, k ≤ z + 1 → ∀ a, D.Has (F k a)) (by
          intro D e old
          obtain ⟨E, e', cost, fresh⟩ := D.collect (F (z + 1)) 3 (fun U eu a =>
            step z (by omega) U (fun h => eu (e h)) (fun t => eu (old z le_rfl t)) a)
          refine ⟨E, e', cost, fun k hk a => ?_⟩
          by_cases h : k ≤ z
          · exact e' (old k h a)
          · exact (show k = z + 1 by omega) ▸ fresh a)
      exact work.weaken (by rw [cardPairs]; exact le_of_eq (by ring)) (fun _ h => h)
  exact levels n le_rfl

def forwards (R : Nat → Bits (w + 1) → Signal m) (k : Nat) (a : Bits w × Bits w) : Signal m :=
  segment R 0 k a.1 a.2

def backwards (R : Nat → Bits (w + 1) → Signal m) (n k : Nat) (a : Bits w × Bits w) : Signal m :=
  segment R (n - k) k a.1 a.2

theorem Bank.forwardPass (B : Bank m) (R : Nat → Bits (w + 1) → Signal m) (n : Nat)
    (ht : B.Has (fun _ => True)) (hz : B.Has (fun _ => False))
    (raw : ∀ k p, B.Has (R k p)) :
    B.Grow (n * (3 * 4 ^ w)) (fun D => ∀ k, k ≤ n → ∀ a, D.Has (forwards R k a)) := by
  apply B.levels (forwards R) n (fun a => Bank.initial R 0 a.1 a.2 ht hz)
  intro k _ D e old a
  let f (b : Bool) := forwards R k (a.1, front (incoming a.2 b))
  let g (b : Bool) := R k (incoming a.2 b)
  apply (Bank.twoWays (f := f) (g := g) (fun b => old _) (fun b => e (raw _ _))).weaken le_rfl
  intro E out
  apply out.congr
  intro x
  simpa only [forwards, segment, f, g, Nat.zero_add] using
    (pathForward (fun t p => R t p x) 0 k a.1 a.2).symm

theorem Bank.backwardPass (B : Bank m) (R : Nat → Bits (w + 1) → Signal m) (n : Nat)
    (ht : B.Has (fun _ => True)) (hz : B.Has (fun _ => False))
    (raw : ∀ k p, B.Has (R k p)) :
    B.Grow (n * (3 * 4 ^ w)) (fun D => ∀ k, k ≤ n → ∀ a, D.Has (backwards R n k a)) := by
  apply B.levels (backwards R n) n (fun a => Bank.initial R _ a.1 a.2 ht hz)
  intro k hk D e old a
  let f (b : Bool) := R (n - (k + 1)) (outgoing a.1 b)
  let g (b : Bool) := backwards R n k (rear (outgoing a.1 b), a.2)
  apply (Bank.twoWays (f := f) (g := g) (fun b => e (raw _ _)) (fun b => old _)).weaken le_rfl
  intro E out
  apply out.congr
  intro x
  simpa only [backwards, segment, f, g, show n - (k + 1) + 1 = n - k by omega] using
    (pathBackward (fun t p => R t p x) (n - (k + 1)) k a.1 a.2).symm

def repair {n : Nat} (R : Nat → Bits (w + 1) → Signal m)
    (i : Fin n) (p : Bits (w + 1)) : Signal m :=
  fun x => ∃ s, segment R 0 i.val s (front p) x ∧
    segment R (i.val + 1) (n - (i.val + 1)) (rear p) s x

def decision (R : Nat → Bits (w + 1) → Signal m) (n : Nat) : Signal m :=
  fun x => ∃ s, segment R 0 n s s x

theorem Bank.repairs (B : Bank m) (R : Nat → Bits (w + 1) → Signal m) (n : Nat)
    (hf : ∀ k, k ≤ n → ∀ a, B.Has (forwards R k a))
    (hb : ∀ k, k ≤ n → ∀ a, B.Has (backwards R n k a))
    (hz : B.Has (fun _ => False)) :
    B.Grow (4 * n * 4 ^ w) (fun D => ∀ (i : Fin n) p, D.Has (repair R i p)) := by
  let f (a : Fin n × Bits (w + 1)) := repair R a.1 a.2
  have build := B.collect f (2 * Fintype.card (Bits w)) (by
    intro D e a
    let i := a.1
    let p := a.2
    have hi : i.val + 1 ≤ n := i.isLt
    let left (s : Bits w) := forwards R i.val (s, front p)
    let right (s : Bits w) := backwards R n (n - (i.val + 1)) (rear p, s)
    have h := D.dot left right (fun s => e (hf i.val i.isLt.le _))
      (fun s => e (hb _ (Nat.sub_le ..) _)) (e hz)
    apply h.weaken le_rfl
    intro E out
    apply out.congr
    intro x
    simp only [left, right, forwards, backwards, f, repair, i, p,
      Nat.sub_sub_self hi])
  have cost : Fintype.card (Fin n × Bits (w + 1)) * (2 * Fintype.card (Bits w)) = 4 * n * 4 ^ w := by
    rw [Fintype.card_prod, Fintype.card_fin, cardBits, cardBits, pow_succ,
      show (4 : Nat) = 2 * 2 by decide, mul_pow]
    ring
  exact build.weaken cost.le (fun _ h i p => h (i, p))

theorem buildCircuit (R : Nat → Bits (w + 1) → Signal m) (n : Nat)
    (raw : ∀ k p, (Bank.empty m).Has (R k p)) :
    ∃ (C : Circuit) (out : Fin n → Bits (w + 1) → Fin (m + C.size)),
      Monotone2 C ∧ ReadsBack m C ∧ C.output < m + C.size ∧ C.size ≤ 10 * n * 4 ^ w + 2 ^ w + 2 ∧
      ∀ x, (C.eval (List.ofFn x) = true ↔ decision R n x) ∧ ∀ i p,
        (C.wires (List.ofFn x)).getD (out i p).val false = true ↔ repair R i p x := by
  classical
  obtain ⟨B, e₀, c₀, hz⟩ := (Bank.empty m).constFalse
  obtain ⟨D, e₁, c₁, ht⟩ := B.constTrue
  have rawD (k p) := e₁ (e₀ (raw k p))
  obtain ⟨E, e₂, c₂, hf⟩ := D.forwardPass R n ht (e₁ hz) rawD
  obtain ⟨F, e₃, c₃, hb⟩ := E.backwardPass R n (e₂ ht) (e₂ (e₁ hz)) (fun k p => e₂ (rawD k p))
  have hzF := e₃ (e₂ (e₁ hz))
  obtain ⟨G, e₄, c₄, hr⟩ := F.repairs R n (fun k hk a => e₃ (hf k hk a)) hb hzF
  obtain ⟨H, e₅, c₅, hd⟩ := G.anyOf (fun s : Bits w => forwards R n (s, s))
    (fun s => e₄ (e₃ (hf n le_rfl (s, s)))) (e₄ hzF)
  obtain ⟨z, hzb, hze⟩ := hd
  let C : Circuit := ⟨H.gates, z⟩
  have hOut (i : Fin n) (p : Bits (w + 1)) : ∃ j : Fin (m + C.size), ∀ x,
      (C.wires (List.ofFn x)).getD j.val false = true ↔ repair R i p x := by
    obtain ⟨j, hj, ev⟩ := e₅ (hr i p)
    exact ⟨⟨j, hj⟩, ev⟩
  choose out get using hOut
  refine ⟨C, out, H.mono, H.back, hzb, ?_, fun x => ⟨hze x, fun i p => get i p x⟩⟩
  change H.gates.length ≤ _
  rw [cardBits] at c₅
  change B.gates.length ≤ 0 + 1 at c₀
  calc
    H.gates.length ≤ (((1 + 1) + n * (3 * 4 ^ w)) + n * (3 * 4 ^ w)) + 4 * n * 4 ^ w + 2 ^ w := by omega
    _ = _ := by ring

theorem decisionSpec {n w} (hn : 0 < n) (table : Table n w) :
    decision (tableRule hn) n (flatInput table) ↔
      ∃ word : Bits n, ∀ i : Fin n, table i (windowAt hn word i.val) = true := by
  change (∃ s, Path (fun k p => tableRule hn k p (flatInput table)) 0 n s s) ↔ _
  rw [cycleWord hn]
  simp only [readTable]

theorem repairSpec {n w} (hn : 0 < n) (table : Table n w) (i : Fin n) (p : Bits (w + 1)) :
    repair (tableRule hn) i p (flatInput table) ↔
      ∃ word : Bits n, windowAt hn word i.val = p ∧
        ∀ j : Fin n, j ≠ i → table j (windowAt hn word j.val) = true := by
  let A : Rules w := fun k q => tableRule hn k q (flatInput table)
  change (∃ s, Path A 0 i.val s (front p) ∧ Path A (i.val + 1) (n - (i.val + 1)) (rear p) s) ↔ _
  rw [← cutCycle A i p, cycleWord hn]
  constructor
  · rintro ⟨word, h⟩
    refine ⟨word, by simpa [forceRow] using h i, fun j hj => ?_⟩
    have hne : j.val ≠ i.val := fun eqn => hj (Fin.ext eqn)
    exact (readTable hn table j _).mp (by simpa only [forceRow, ite_eq_right hne] using h j)
  · rintro ⟨word, hp, h⟩
    refine ⟨word, fun j => ?_⟩
    by_cases he : j = i
    · subst j
      simpa [forceRow] using hp
    · have hne : j.val ≠ i.val := fun eqn => he (Fin.ext eqn)
      simpa only [forceRow, ite_eq_right hne] using (readTable hn table j _).mpr (h j he)

end PEqualNP.Outside.L_clb_055

theorem PEqualNP.Outside.L_clb_055 : (∀ (n w : ℕ) (hn : 0 < n),
  let Pat := Fin (w + 1) → Bool
  let I := n * 2 ^ (w + 1)
  let window := fun (word : Fin n → Bool) (i : Fin n) (j : Fin (w + 1)) =>
    word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
    (out : Fin n → Pat → Fin (I + C.size)),
    PEqualNP.MetaComplexity.Monotone2 C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧ C.output < I + C.size ∧
    C.size ≤ 10 * n * 4 ^ w + 2 ^ w + 2 ∧
    ∀ table : Fin n → Pat → Bool,
      let x := (List.ofFn (fun i : Fin n => List.ofFn (fun p : Fin (2 ^ (w + 1)) =>
        table i (fun j => p.val.testBit j.val)))).flatten
      (C.eval x = true ↔ ∃ word, ∀ i, table i (window word i) = true) ∧
      ∀ i p, ((C.wires x).getD (out i p).val false = true ↔
        ∃ word, window word i = p ∧ ∀ j, j ≠ i → table j (window word j) = true)) := by
  intros n w hn
  let R := @PEqualNP.Outside.L_clb_055.tableRule n w hn
  obtain ⟨C, out, hm, hb, ho, hs, ev⟩ := PEqualNP.Outside.L_clb_055.buildCircuit R n
    (fun k p => PEqualNP.Outside.L_clb_055.Bank.input _)
  refine ⟨C, out, hm, hb, ho, hs, fun table => ?_⟩
  dsimp only
  rw [← PEqualNP.Outside.L_clb_055.flatList table]
  obtain ⟨hd, hr⟩ := ev (PEqualNP.Outside.L_clb_055.flatInput table)
  exact ⟨hd.trans (PEqualNP.Outside.L_clb_055.decisionSpec hn table),
    fun i p => (hr i p).trans (PEqualNP.Outside.L_clb_055.repairSpec hn table i p)⟩
