import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_043_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

abbrev Sig (m : ℕ) := (Fin m → Bool) → Bool

private def Scheduled (m : ℕ) (k : ℕ) (S : Set (Sig m)) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack m ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : ℕ, i < m + k ∧
      ∀ x : Fin m → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x

private theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem startSched (m : ℕ) :
    Scheduled m 0 (Set.range (fun i : Fin m => fun x : Fin m → Bool => x i)) := by
  refine ⟨[], rfl, by simp [ReadsBack], by simp [FanInTwo], ?_⟩
  intro a ha
  obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
  refine ⟨i.val, by simp, fun x => ?_⟩
  change (List.ofFn x).getD i.val false = x i
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem realizeDeps {m k : ℕ} {S : Set (Sig m)} {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : ℕ, i < m + k ∧
      ∀ x : Fin m → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x)
    (deps : List (Sig m)) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List ℕ, is.length = deps.length ∧ (∀ i ∈ is, i < m + k) ∧
      ∀ x : Fin m → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

private theorem pushSched {m k : ℕ} {S : Set (Sig m)}
    (h : Scheduled m k S) (op : GateOp) (deps : List (Sig m)) (out : Sig m)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Scheduled m (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin m → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = m + k := by
    rw [wireLength]; simpa using congrArg (m + ·) hgs
  have hsnoc (x : Fin m → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by simp at hj; omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · rw [List.mem_singleton.mp hg']
      exact ⟨hop, by change is.length ≤ 2; simpa only [his] using hlen⟩
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨m + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

private theorem finishMulti {m k n : ℕ} {S : Set (Sig m)}
    (h : Scheduled m k S) (out : Sig m) (hout : out ∈ S)
    (bits : Fin n → Sig m) (hbits : ∀ p, bits p ∈ S) :
    ∃ (C : Circuit) (outBit : Fin n → Fin (m + C.size)),
      C.size = k ∧ ReadsBack m C ∧ FanInTwo C ∧ C.output < m + C.size ∧
      (∀ x : Fin m → Bool, C.eval (List.ofFn x) = out x) ∧
      (∀ (p : Fin n) (x : Fin m → Bool),
        (C.wires (List.ofFn x)).getD (outBit p).val false = bits p x) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨i0, hi0, hval0⟩ := hw out hout
  have hcho : ∀ p : Fin n, ∃ i : Fin (m + gs.length),
      ∀ x : Fin m → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i.val false = bits p x := by
    intro p
    obtain ⟨i, hi, hv⟩ := hw (bits p) (hbits p)
    exact ⟨⟨i, by omega⟩, hv⟩
  choose outBit houtBit using hcho
  exact ⟨⟨gs, i0⟩, outBit, hgs, hr, hf, by change i0 < m + gs.length; omega, hval0, houtBit⟩

private structure Build {m : ℕ} (A B : Set (Sig m)) (b : ℕ) : Prop where
  run : ∀ {k : ℕ} {S : Set (Sig m)}, Scheduled m k S → A ⊆ S →
    ∃ c ≤ b, Scheduled m (k + c) (S ∪ B)

private theorem idleB {m : ℕ} {A B : Set (Sig m)} (h : B ⊆ A) : Build A B 0 :=
  ⟨fun hs ha => ⟨0, le_rfl, by simpa [Set.union_eq_left.mpr (h.trans ha)] using hs⟩⟩

private theorem relaxB {m : ℕ} {A A' B B' : Set (Sig m)} {b b' : ℕ}
    (H : Build A B b) (hA : A ⊆ A') (hB : B' ⊆ A' ∪ B) (hb : b ≤ b') : Build A' B' b' :=
  ⟨fun hs ha => by
    obtain ⟨c, hc, hsc⟩ := H.run hs (hA.trans ha)
    obtain ⟨gs, hgs, hr, hf, hw⟩ := hsc
    refine ⟨c, hc.trans hb, gs, hgs, hr, hf, fun a hmem => ?_⟩
    rcases hmem with h1 | h2
    · exact hw a (Or.inl h1)
    · rcases hB h2 with h2a | h2b
      · exact hw a (Or.inl (ha h2a))
      · exact hw a (Or.inr h2b)⟩

private theorem seqB {m : ℕ} {A B C : Set (Sig m)} {b c : ℕ}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) :=
  ⟨fun hs ha => by
    obtain ⟨c1, hc1, hs1⟩ := H1.run hs ha
    obtain ⟨c2, hc2, hs2⟩ := H2.run hs1 (Set.union_subset (ha.trans Set.subset_union_left) Set.subset_union_right)
    refine ⟨c1 + c2, Nat.add_le_add hc1 hc2, ?_⟩
    simpa [Nat.add_assoc, Set.union_assoc] using hs2⟩

private theorem gateB {m : ℕ} {A : Set (Sig m)} (op : GateOp) (deps : List (Sig m)) (out : Sig m)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ A)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Build A {out} 1 :=
  ⟨fun hs ha => ⟨1, le_rfl, by
    simpa [Set.union_singleton] using pushSched hs op deps out hop hlen (fun a hm => ha (hdeps a hm)) hval⟩⟩

private theorem constB {m : ℕ} {A : Set (Sig m)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b with
  | false => exact gateB .or [] (fun _ => false) (by simp) (by simp) (by simp) (fun _ => rfl)
  | true => exact gateB .and [] (fun _ => true) (by simp) (by simp) (by simp) (fun _ => rfl)

private theorem notB {m : ℕ} {A : Set (Sig m)} {f : Sig m} (hf : f ∈ A) :
    Build A {fun x => !(f x)} 1 :=
  gateB .not [f] (fun x => !(f x)) (by simp) (by simp) (by simpa using hf) (fun _ => rfl)

private theorem andB {m : ℕ} {A : Set (Sig m)} {f g : Sig m} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x && g x} 1 :=
  gateB .and [f, g] (fun x => f x && g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

private theorem orB {m : ℕ} {A : Set (Sig m)} {f g : Sig m} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x || g x} 1 :=
  gateB .or [f, g] (fun x => f x || g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

private theorem listB {m : ℕ} {α : Type*} {A : Set (Sig m)} (F : α → Set (Sig m)) (c : ℕ)
    (xs : List α) (h : ∀ a ∈ xs, Build A (F a) c) :
    Build A (⋃ a ∈ xs, F a) (xs.length * c) := by
  induction xs with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    exact idleB (by simp)
  | cons a xs ih =>
    have h1 := h a List.mem_cons_self
    have h2 : Build (A ∪ F a) (⋃ b ∈ xs, F b) (xs.length * c) :=
      relaxB (ih (fun b hb => h b (List.mem_cons_of_mem a hb))) Set.subset_union_left Set.subset_union_right le_rfl
    have hseq := seqB h1 h2
    refine relaxB hseq le_rfl ?_ (by simp [Nat.succ_mul, Nat.add_comm])
    intro f hf
    simp only [Set.mem_iUnion, List.mem_cons] at hf
    rcases hf with ⟨b, rfl | hb, hfb⟩
    · exact Or.inr (Or.inl hfb)
    · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hfb⟩⟩))

private theorem orListB {m : ℕ} {A : Set (Sig m)} (xs : List (Sig m))
    (hxs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xs.any (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idleB (by simpa using hfalse)
  | cons f xs ih =>
    have h1 := ih (fun g hg => hxs g (List.mem_cons_of_mem f hg))
    have h2 : Build (A ∪ {fun x => xs.any (fun g => g x)})
        {fun x => (f :: xs).any (fun g => g x)} 1 := by
      have heq : (fun x => (f :: xs).any (fun g => g x)) =
          (fun x => f x || xs.any (fun g => g x)) := by
        funext x; simp [List.any_cons]
      rw [heq]
      exact orB (Or.inl (hxs f List.mem_cons_self)) (Or.inr rfl)
    exact relaxB (seqB h1 h2) le_rfl (by intro a ha; exact Or.inr (Or.inr ha)) (by simp)

private def winIdx (w : ℕ) (s : Fin (2 ^ w)) (b : Bool) : ℕ :=
  s.val + if b then 2 ^ w else 0

private theorem winIdx_lt (w : ℕ) (s : Fin (2 ^ w)) (b : Bool) :
    winIdx w s b < 2 ^ (w + 1) := by
  unfold winIdx
  have hs := s.isLt
  rw [Nat.pow_succ]
  cases b <;> simp <;> omega

private theorem winIdx_testBit (w : ℕ) (s : Fin (2 ^ w)) (b : Bool) (t : Fin (w + 1)) :
    (winIdx w s b).testBit t.val = if t.val < w then s.val.testBit t.val else b := by
  unfold winIdx
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    split_ifs with h
    · rfl
    · have ht : t.val = w := by omega
      rw [ht]
      exact Nat.testBit_lt_two_pow s.isLt
  | true =>
    simp only [↓reduceIte]
    rw [Nat.add_comm]
    split_ifs with h
    · exact Nat.testBit_two_pow_add_gt h s.val
    · have ht : t.val = w := by omega
      rw [ht, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow s.isLt]
      rfl

private def nextS {w : ℕ} (s : Fin (2 ^ w)) (b : Bool) : Fin (2 ^ w) :=
  ⟨winIdx w s b / 2, by
    have h := winIdx_lt w s b
    rw [Nat.pow_succ] at h
    omega⟩

private theorem nextS_testBit {w : ℕ} (s : Fin (2 ^ w)) (b : Bool) (t : ℕ) (ht : t < w) :
    (nextS s b).val.testBit t = if t + 1 < w then s.val.testBit (t + 1) else b := by
  change (winIdx w s b / 2).testBit t = _
  rw [Nat.testBit_div_two]
  exact winIdx_testBit w s b ⟨t + 1, by omega⟩

private def topBit {w' : ℕ} (t : Fin (2 ^ (w' + 1))) : Bool :=
  decide (2 ^ w' ≤ t.val)

private def pred0 {w' : ℕ} (t : Fin (2 ^ (w' + 1))) : Fin (2 ^ (w' + 1)) :=
  ⟨2 * (if 2 ^ w' ≤ t.val then t.val - 2 ^ w' else t.val), by
    have ht := t.isLt
    have hp : 2 ^ (w' + 1) = 2 ^ w' * 2 := Nat.pow_succ 2 w'
    split_ifs <;> omega⟩

private def pred1 {w' : ℕ} (t : Fin (2 ^ (w' + 1))) : Fin (2 ^ (w' + 1)) :=
  ⟨2 * (if 2 ^ w' ≤ t.val then t.val - 2 ^ w' else t.val) + 1, by
    have ht := t.isLt
    have hp : 2 ^ (w' + 1) = 2 ^ w' * 2 := Nat.pow_succ 2 w'
    split_ifs <;> omega⟩

private theorem nextS_eq_iff_pred {w' : ℕ} (s t : Fin (2 ^ (w' + 1))) (b : Bool) :
    nextS s b = t ↔ b = topBit t ∧ (s = pred0 t ∨ s = pred1 t) := by
  have hs := s.isLt
  have ht := t.isLt
  have hp : 2 ^ (w' + 1) = 2 ^ w' * 2 := Nat.pow_succ 2 w'
  simp only [Fin.ext_iff, nextS, winIdx, topBit, pred0, pred1]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] <;>
    split_ifs <;> simp <;> omega

private def edgeIdx (n w : ℕ) (k : Fin n) (s : Fin (2 ^ w)) (b : Bool) : Fin (n * 2 ^ (w + 1)) :=
  ⟨k.val * 2 ^ (w + 1) + winIdx w s b, by
    have hw := winIdx_lt w s b
    have h1 : (k.val + 1) * 2 ^ (w + 1) ≤ n * 2 ^ (w + 1) := Nat.mul_le_mul_right _ k.isLt
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega⟩

private def edgeSig (n w : ℕ) (k : Fin n) (s : Fin (2 ^ w)) (b : Bool) : Sig (n * 2 ^ (w + 1)) :=
  fun x => x (edgeIdx n w k s b)

private def tableInputs {n w : ℕ} (hn : 0 < n) (table : Fin n → (Fin (w + 1) → Bool) → Bool) :
    Fin (n * 2 ^ (w + 1)) → Bool :=
  fun j => table ⟨(j.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩ (fun bit => j.val.testBit bit.val)

private theorem edgeSig_tableInputs {n w : ℕ} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (k : Fin n) (s : Fin (2 ^ w)) (b : Bool) :
    edgeSig n w k s b (tableInputs hn table) =
      table k (fun bit => if bit.val < w then s.val.testBit bit.val else b) := by
  unfold edgeSig tableInputs edgeIdx
  have hpos : 0 < 2 ^ (w + 1) := Nat.two_pow_pos _
  have hw := winIdx_lt w s b
  have hdiv : (k.val * 2 ^ (w + 1) + winIdx w s b) / 2 ^ (w + 1) = k.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hw, Nat.zero_add]
  have hmod : ((k.val * 2 ^ (w + 1) + winIdx w s b) / 2 ^ (w + 1)) % n = k.val := by
    rw [hdiv, Nat.mod_eq_of_lt k.isLt]
  have hfin : (⟨((k.val * 2 ^ (w + 1) + winIdx w s b) / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩ : Fin n) = k :=
    Fin.ext hmod
  rw [hfin]
  congr 1
  funext bit
  have htb : (k.val * 2 ^ (w + 1) + winIdx w s b).testBit bit.val = (winIdx w s b).testBit bit.val := by
    rw [Nat.testBit, Nat.testBit]
    have hq : 2 ^ (w + 1) = 2 ^ bit.val * 2 ^ (w + 1 - bit.val) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
    have heven : 2 ∣ 2 ^ (w + 1 - bit.val) := dvd_pow_self 2 (by omega)
    obtain ⟨m, hm⟩ := heven
    have hmul : k.val * 2 ^ (w + 1) = (2 * (k.val * m)) * 2 ^ bit.val := by
      rw [hq, hm]; ring
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hmul,
      Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
    simp
  rw [htb, winIdx_testBit]

private def reachDown (n w : ℕ) : ℕ → Fin (2 ^ w) → Fin (2 ^ w) → Sig (n * 2 ^ (w + 1))
  | 0, s, t, _ => decide (t = s)
  | d + 1, s, t, x =>
    if h : d < n then
      let k : Fin n := ⟨n - 1 - d, by omega⟩
      (edgeSig n w k t false x && reachDown n w d s (nextS t false) x) ||
      (edgeSig n w k t true x && reachDown n w d s (nextS t true) x)
    else false

private def p0Sig (n w : ℕ) (k : Fin n) (s t : Fin (2 ^ w)) : Sig (n * 2 ^ (w + 1)) :=
  fun x => edgeSig n w k t false x && reachDown n w (n - 1 - k.val) s (nextS t false) x

private def p1Sig (n w : ℕ) (k : Fin n) (s t : Fin (2 ^ w)) : Sig (n * 2 ^ (w + 1)) :=
  fun x => edgeSig n w k t true x && reachDown n w (n - 1 - k.val) s (nextS t true) x

private theorem reachDown_succ_eq (n w : ℕ) (k : Fin n) (s t : Fin (2 ^ w)) :
    reachDown n w (n - k.val) s t = fun x => p0Sig n w k s t x || p1Sig n w k s t x := by
  have hk : n - k.val = (n - 1 - k.val) + 1 := by omega
  have hlt : n - 1 - k.val < n := by omega
  have hkf : (⟨n - 1 - (n - 1 - k.val), by omega⟩ : Fin n) = k := Fin.ext (by dsimp; omega)
  funext x
  rw [hk]
  unfold reachDown p0Sig p1Sig
  simp [hlt, hkf]

private def feasSig (n w : ℕ) (s : Fin (2 ^ w)) : Sig (n * 2 ^ (w + 1)) :=
  reachDown n w n s s

private def prefSig (n w : ℕ) : ℕ → Sig (n * 2 ^ (w + 1))
  | 0, _ => false
  | j + 1, x => prefSig n w j x || if h : j < 2 ^ w then feasSig n w ⟨j, h⟩ x else false

private def pickSig (n w : ℕ) (s : Fin (2 ^ w)) : Sig (n * 2 ^ (w + 1)) :=
  fun x => feasSig n w s x && !(prefSig n w s.val x)

private def actSig (n w : ℕ) : ℕ → Fin (2 ^ w) → Fin (2 ^ w) → Sig (n * 2 ^ (w + 1))
  | 0, s, t, x => if t = s then pickSig n w s x else false
  | k + 1, s, t', x =>
    if hk : k < n then
      match w with
      | 0 => actSig n 0 k s t' x
      | w' + 1 =>
        let b := topBit t'
        let g (t : Fin (2 ^ (w' + 1))) : Bool :=
          if b then actSig n (w' + 1) k s t x && !(p0Sig n (w' + 1) ⟨k, hk⟩ s t x)
          else actSig n (w' + 1) k s t x && p0Sig n (w' + 1) ⟨k, hk⟩ s t x
        g (pred0 t') || g (pred1 t')
    else false

private def go0Sig (n w : ℕ) (k : Fin n) (s t : Fin (2 ^ w)) : Sig (n * 2 ^ (w + 1)) :=
  fun x => actSig n w k.val s t x && p0Sig n w k s t x

private def go1Sig (n w : ℕ) (k : Fin n) (s t : Fin (2 ^ w)) : Sig (n * 2 ^ (w + 1)) :=
  fun x => actSig n w k.val s t x && !(p0Sig n w k s t x)

private def allPairs (S : ℕ) : List (Fin S × Fin S) :=
  (List.finRange S).flatMap fun s => (List.finRange S).map fun t => (s, t)

private theorem allPairs_length (S : ℕ) : (allPairs S).length = S * S := by
  unfold allPairs
  rw [List.length_flatMap]
  have hmap : (List.finRange S).map (fun s => ((List.finRange S).map fun t => (s, t)).length) =
      List.replicate S S := by
    apply List.ext_getElem (by simp)
    intro i hi1 hi2
    simp
  rw [hmap, List.sum_replicate, smul_eq_mul]

private theorem mem_allPairs {S : ℕ} (p : Fin S × Fin S) : p ∈ allPairs S := by
  unfold allPairs
  simp

private def stepBitSig (n w : ℕ) (k : Fin n) : Sig (n * 2 ^ (w + 1)) :=
  fun x => (allPairs (2 ^ w)).any fun p => go1Sig n w k p.1 p.2 x

private def wordAtState {n w : ℕ} (hn : 0 < n) (word : Fin n → Bool) (k : ℕ) : Fin (2 ^ w) :=
  ⟨∑ t : Fin w, if word ⟨(k + t.val) % n, Nat.mod_lt _ hn⟩ then 2 ^ t.val else 0, by
    induction w with
    | zero => simp
    | succ w' ih =>
      rw [Fin.sum_univ_castSucc, Nat.pow_succ]
      simp only [Fin.val_castSucc, Fin.val_last]
      have h2 : (if word ⟨(k + w') % n, Nat.mod_lt _ hn⟩ = true then 2 ^ w' else 0) ≤ 2 ^ w' := by
        split_ifs <;> omega
      omega⟩

private theorem wordAtState_testBit {n w : ℕ} (hn : 0 < n) (word : Fin n → Bool) (k : ℕ)
    (t : ℕ) (ht : t < w) :
    (wordAtState (w := w) hn word k).val.testBit t = word ⟨(k + t) % n, Nat.mod_lt _ hn⟩ := by
  induction w with
  | zero => omega
  | succ w' ih =>
    have hsplit : (wordAtState (w := w' + 1) hn word k).val =
        (wordAtState (w := w') hn word k).val +
        (if word ⟨(k + w') % n, Nat.mod_lt _ hn⟩ then 2 ^ w' else 0) := by
      unfold wordAtState
      simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [hsplit]
    have hlt := (wordAtState (w := w') hn word k).isLt
    cases hw : word ⟨(k + w') % n, Nat.mod_lt _ hn⟩ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      by_cases htw : t < w'
      · exact ih htw
      · have hteq : t = w' := by omega
        subst hteq
        rw [Nat.testBit_lt_two_pow hlt, hw]
    | true =>
      simp only [↓reduceIte]
      rw [Nat.add_comm]
      by_cases htw : t < w'
      · rw [Nat.testBit_two_pow_add_gt htw]; exact ih htw
      · have hteq : t = w' := by omega
        subst hteq
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt, hw]
        rfl

private theorem wordAtState_next {n w : ℕ} (hn : 0 < n) (word : Fin n → Bool) (k : ℕ) :
    nextS (wordAtState (w := w) hn word k) (word ⟨(k + w) % n, Nat.mod_lt _ hn⟩) =
      wordAtState (w := w) hn word (k + 1) := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < w
  · rw [nextS_testBit _ _ t ht, wordAtState_testBit hn word (k + 1) t ht]
    split_ifs with h1
    · rw [wordAtState_testBit hn word k (t + 1) h1]
      congr 1; apply Fin.ext; dsimp only; congr 1; omega
    · have hteq : t + 1 = w := by omega
      congr 1; apply Fin.ext; dsimp only; congr 1; omega
  · have hge : 2 ^ w ≤ 2 ^ t := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    rw [Nat.testBit_lt_two_pow ((nextS _ _).isLt.trans_le hge),
      Nat.testBit_lt_two_pow ((wordAtState (w := w) hn word (k + 1)).isLt.trans_le hge)]

private theorem wordAtState_add_n {n w : ℕ} (hn : 0 < n) (word : Fin n → Bool) (k : ℕ) :
    wordAtState (w := w) hn word (k + n) = wordAtState (w := w) hn word k := by
  apply Fin.ext
  unfold wordAtState
  dsimp only
  apply Finset.sum_congr rfl
  intro t _
  have hm : (k + n + t.val) % n = (k + t.val) % n := by
    rw [show k + n + t.val = (k + t.val) + n by omega, Nat.add_mod_right]
  simp only [hm]

private theorem reachDown_of_valid {n w : ℕ} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool) (word : Fin n → Bool)
    (hvalid : ∀ i : Fin n, table i (fun bit => word ⟨(i.val + bit.val) % n, Nat.mod_lt _ hn⟩) = true) :
    ∀ d (_hd : d ≤ n),
      reachDown n w d (wordAtState hn word 0) (wordAtState hn word (n - d)) (tableInputs hn table) = true := by
  intro d hd
  induction d with
  | zero =>
    have heq : wordAtState (w := w) hn word n = wordAtState (w := w) hn word 0 := by
      simpa using wordAtState_add_n (w := w) hn word 0
    simp [reachDown, heq]
  | succ d ih =>
    have hlt : d < n := by omega
    let k : Fin n := ⟨n - 1 - d, by omega⟩
    have hkd : n - (d + 1) = k.val := by dsimp [k]; omega
    have hkd1 : k.val + 1 = n - d := by dsimp [k]; omega
    have hedge : edgeSig n w k (wordAtState hn word k.val)
        (word ⟨(k.val + w) % n, Nat.mod_lt _ hn⟩) (tableInputs hn table) = true := by
      rw [edgeSig_tableInputs hn table k _ _]
      convert hvalid k using 2
      funext bit
      split_ifs with hbw
      · exact wordAtState_testBit hn word k.val bit.val hbw
      · have hbe : bit.val = w := by omega
        rw [hbe]
    have hnext : nextS (wordAtState (w := w) hn word k.val) (word ⟨(k.val + w) % n, Nat.mod_lt _ hn⟩) =
        wordAtState hn word (n - d) := by
      rw [wordAtState_next hn word k.val, hkd1]
    have hr := ih (by omega)
    rw [hkd]
    unfold reachDown
    simp only [hlt, ↓reduceDIte]
    cases hb : word ⟨(k.val + w) % n, Nat.mod_lt _ hn⟩ with
    | false =>
      rw [hb] at hedge hnext
      rw [hedge, hnext, hr]
      simp
    | true =>
      rw [hb] at hedge hnext
      rw [hedge, hnext, hr]
      simp

private theorem prefSig_iff {n w : ℕ} (x : Fin (n * 2 ^ (w + 1)) → Bool) (m : ℕ) (hm : m ≤ 2 ^ w) :
    prefSig n w m x = true ↔ ∃ s : Fin (2 ^ w), s.val < m ∧ feasSig n w s x = true := by
  induction m with
  | zero => simp [prefSig]
  | succ m ih =>
    have hmlt : m < 2 ^ w := by omega
    simp only [prefSig, hmlt, ↓reduceDIte, Bool.or_eq_true, ih (by omega)]
    constructor
    · rintro (⟨s, hs, hf⟩ | hf)
      · exact ⟨s, by omega, hf⟩
      · exact ⟨⟨m, hmlt⟩, by dsimp; omega, hf⟩
    · rintro ⟨s, hs, hf⟩
      by_cases hsm : s.val < m
      · exact Or.inl ⟨s, hsm, hf⟩
      · have hseq : s = ⟨m, hmlt⟩ := Fin.ext (by dsimp; omega)
        subst hseq
        exact Or.inr hf

private theorem pickSig_exists {n w : ℕ} (x : Fin (n * 2 ^ (w + 1)) → Bool)
    (h : prefSig n w (2 ^ w) x = true) :
    ∃ s : Fin (2 ^ w), pickSig n w s x = true := by
  have hex : ∃ m, ∃ hm : m < 2 ^ w, feasSig n w ⟨m, hm⟩ x = true := by
    obtain ⟨s, _, hf⟩ := (prefSig_iff x (2 ^ w) le_rfl).mp h
    exact ⟨s.val, s.isLt, hf⟩
  classical
  let m0 := Nat.find hex
  obtain ⟨hm0_lt, hm0_f⟩ := Nat.find_spec hex
  refine ⟨⟨m0, hm0_lt⟩, ?_⟩
  unfold pickSig
  rw [hm0_f, Bool.true_and, Bool.not_eq_true']
  cases hp : prefSig n w m0 x with
  | false => rfl
  | true =>
    obtain ⟨s, hsm, hsf⟩ := (prefSig_iff x m0 (by omega)).mp hp
    exact False.elim (Nat.find_min hex hsm ⟨s.isLt, hsf⟩)

private theorem pickSig_unique {n w : ℕ} (x : Fin (n * 2 ^ (w + 1)) → Bool)
    {s1 s2 : Fin (2 ^ w)} (h1 : pickSig n w s1 x = true) (h2 : pickSig n w s2 x = true) :
    s1 = s2 := by
  unfold pickSig at h1 h2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1 h2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
  · have hp : prefSig n w s2.val x = true :=
      (prefSig_iff x s2.val (by omega)).mpr ⟨s1, hlt, h1.1⟩
    rw [h2.2] at hp; exact Bool.false_ne_true hp
  · have hp : prefSig n w s1.val x = true :=
      (prefSig_iff x s1.val (by omega)).mpr ⟨s2, hgt, h2.1⟩
    rw [h1.2] at hp; exact Bool.false_ne_true hp

private def greedyState (n w : ℕ) (x : Fin (n * 2 ^ (w + 1)) → Bool) (s0 : Fin (2 ^ w)) :
    ℕ → Fin (2 ^ w)
  | 0 => s0
  | k + 1 =>
    if hk : k < n then
      let t := greedyState n w x s0 k
      nextS t (!(p0Sig n w ⟨k, hk⟩ s0 t x))
    else s0

private def greedyBit (n w : ℕ) (x : Fin (n * 2 ^ (w + 1)) → Bool) (s0 : Fin (2 ^ w))
    (k : Fin n) : Bool :=
  !(p0Sig n w k s0 (greedyState n w x s0 k.val) x)

private theorem greedy_inv {n w : ℕ} (x : Fin (n * 2 ^ (w + 1)) → Bool) (s0 : Fin (2 ^ w))
    (hpick : pickSig n w s0 x = true) :
    ∀ k ≤ n,
      reachDown n w (n - k) s0 (greedyState n w x s0 k) x = true ∧
      (∀ s t, actSig n w k s t x = decide (s = s0 ∧ t = greedyState n w x s0 k)) ∧
      (∀ (j : Fin n), j.val < k →
        edgeSig n w j (greedyState n w x s0 j.val) (greedyBit n w x s0 j) x = true) := by
  have hfeas : feasSig n w s0 x = true := (Bool.and_eq_true_iff.mp hpick).1
  intro k hk
  induction k with
  | zero =>
    refine ⟨by simpa [greedyState, feasSig] using hfeas, ?_, fun j hj => by omega⟩
    intro s t
    unfold actSig greedyState
    by_cases hts : t = s
    · subst t
      by_cases hs : s = s0
      · subst s; simp [hpick]
      · simp only [↓reduceIte, hs, false_and, decide_false]
        cases hp : pickSig n w s x with
        | false => rfl
        | true => exact False.elim (hs (pickSig_unique x hp hpick))
    · simp only [hts, ↓reduceIte]
      have : ¬ (s = s0 ∧ t = s0) := fun ⟨h1, h2⟩ => hts (h2.trans h1.symm)
      simp [this]
  | succ k ih =>
    obtain ⟨hreach, hact, hedges⟩ := ih (by omega)
    have hkn : k < n := by omega
    let kf : Fin n := ⟨k, hkn⟩
    let tk := greedyState n w x s0 k
    let bk := greedyBit n w x s0 kf
    have hstep_eq : greedyState n w x s0 (k + 1) = nextS tk bk := by
      simp [greedyState, hkn, tk, bk, kf, greedyBit]
    have hreach_k : (p0Sig n w kf s0 tk x || p1Sig n w kf s0 tk x) = true := by
      have := congrFun (reachDown_succ_eq n w kf s0 tk) x
      rw [← this]; exact hreach
    have hstep_ok : edgeSig n w kf tk bk x = true ∧
        reachDown n w (n - (k + 1)) s0 (nextS tk bk) x = true := by
      cases hp0 : p0Sig n w kf s0 tk x with
      | true =>
        have hbk : bk = false := by simp [bk, greedyBit, tk, kf, hp0]
        rw [hbk]
        unfold p0Sig at hp0
        have := Bool.and_eq_true_iff.mp hp0
        exact ⟨this.1, by simpa [show n - 1 - kf.val = n - (k + 1) by dsimp [kf]; omega] using this.2⟩
      | false =>
        have hbk : bk = true := by simp [bk, greedyBit, tk, kf, hp0]
        rw [hbk]
        rw [hp0, Bool.false_or] at hreach_k
        unfold p1Sig at hreach_k
        have := Bool.and_eq_true_iff.mp hreach_k
        exact ⟨this.1, by simpa [show n - 1 - kf.val = n - (k + 1) by dsimp [kf]; omega] using this.2⟩
    refine ⟨by rw [hstep_eq]; exact hstep_ok.2, ?_, ?_⟩
    · intro s t'
      rw [hstep_eq]
      cases w with
      | zero =>
        have ht1 : t' = tk := Fin.ext (by have h1 := t'.isLt; have h2 := tk.isLt; simp at h1 h2; omega)
        have ht2 : nextS tk bk = tk := Fin.ext (by have h1 := (nextS tk bk).isLt; have h2 := tk.isLt; simp at h1 h2; omega)
        rw [ht1, ht2]
        unfold actSig
        simp only [hkn, ↓reduceDIte]
        simpa [tk] using hact s tk
      | succ w' =>
        apply Bool.eq_iff_iff.mpr
        unfold actSig
        simp only [hkn, ↓reduceDIte, Bool.or_eq_true, decide_eq_true_eq]
        have hgb : ∀ (t : Fin (2 ^ (w' + 1))),
            ((if topBit t' then actSig n (w' + 1) k s t x && !(p0Sig n (w' + 1) kf s t x)
              else actSig n (w' + 1) k s t x && p0Sig n (w' + 1) kf s t x) = true) ↔
            (s = s0 ∧ t = tk ∧ topBit t' = bk) := by
          intro t
          rw [hact s t]
          cases htb : topBit t' <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
          · constructor
            · rintro ⟨⟨hs, ht⟩, hp0⟩
              rw [hs, ht] at hp0
              exact ⟨hs, ht, by simp [bk, greedyBit, kf, hp0]⟩
            · rintro ⟨hs, ht, hbk⟩
              refine ⟨⟨hs, ht⟩, ?_⟩
              rw [hs, ht]
              simpa [bk, greedyBit, tk, kf] using hbk.symm
          · constructor
            · rintro ⟨⟨hs, ht⟩, hp0⟩
              rw [hs, ht] at hp0
              exact ⟨hs, ht, by simp [bk, greedyBit, kf, hp0]⟩
            · rintro ⟨hs, ht, hbk⟩
              rw [hs, ht]
              exact ⟨⟨rfl, rfl⟩, hbk.symm⟩
        rw [hgb (pred0 t'), hgb (pred1 t')]
        have hpred := nextS_eq_iff_pred tk t' bk
        constructor
        · rintro (⟨rfl, htk, htb⟩ | ⟨rfl, htk, htb⟩)
          · exact ⟨rfl, (hpred.mpr ⟨htb.symm, Or.inl htk.symm⟩).symm⟩
          · exact ⟨rfl, (hpred.mpr ⟨htb.symm, Or.inr htk.symm⟩).symm⟩
        · rintro ⟨rfl, ht'⟩
          obtain ⟨h1, h2 | h2⟩ := hpred.mp ht'.symm
          · exact Or.inl ⟨rfl, h2.symm, h1.symm⟩
          · exact Or.inr ⟨rfl, h2.symm, h1.symm⟩
    · intro j hj
      by_cases hjk : j.val < k
      · exact hedges j hjk
      · have hjf : j = kf := Fin.ext (by dsimp [kf]; omega)
        subst hjf
        exact hstep_ok.1

private theorem cycle_to_valid {n w : ℕ} (hn : 0 < n)
    (table : Fin n → (Fin (w + 1) → Bool) → Bool)
    (st : ℕ → Fin (2 ^ w)) (bt : Fin n → Bool)
    (hnext : ∀ k : Fin n, st (k.val + 1) = nextS (st k.val) (bt k))
    (hclose : st n = st 0)
    (hedge : ∀ k : Fin n, edgeSig n w k (st k.val) (bt k) (tableInputs hn table) = true) :
    let word : Fin n → Bool := fun pos => bt ⟨(pos.val + n - w % n) % n, Nat.mod_lt _ hn⟩
    ∀ i : Fin n, table i (fun bit => word ⟨(i.val + bit.val) % n, Nat.mod_lt _ hn⟩) = true := by
  intro word
  let B (m : ℕ) : Bool := bt ⟨m % n, Nat.mod_lt _ hn⟩
  let Sseq (m : ℕ) : Fin (2 ^ w) := st (m % n)
  have hS_step : ∀ m : ℕ, Sseq (m + 1) = nextS (Sseq m) (B m) := by
    intro m
    let r : Fin n := ⟨m % n, Nat.mod_lt _ hn⟩
    have hr := hnext r
    dsimp [Sseq, B]
    by_cases hlast : m % n + 1 < n
    · have hm1 : (m + 1) % n = m % n + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < n by omega)]
        exact Nat.mod_eq_of_lt hlast
      rw [hm1]; exact hr
    · have hme : m % n + 1 = n := by have := Nat.mod_lt m hn; omega
      have hm1 : (m + 1) % n = 0 := by
        have hdiv := Nat.div_add_mod m n
        have : m + 1 = n * (m / n + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        rw [this, Nat.mul_mod_right]
      rw [hm1, ← hclose]
      exact (congrArg st hme).symm.trans hr
  have hS_bit : ∀ d (t : ℕ), t + d = w → 0 < d → ∀ m : ℕ,
      (Sseq (m + d)).val.testBit t = B m := by
    intro d
    induction d with
    | zero => intro _ _ h; omega
    | succ d ih =>
      intro t htd _ m
      cases d with
      | zero =>
        have ht : t < w := by omega
        have h1 : ¬ (t + 1 < w) := by omega
        rw [hS_step m, nextS_testBit _ _ t ht]
        simp [h1]
      | succ d' =>
        have ht : t < w := by omega
        have h1 : t + 1 < w := by omega
        rw [show m + (d' + 1 + 1) = (m + (d' + 1)) + 1 by omega, hS_step, nextS_testBit _ _ t ht]
        simp only [h1, ↓reduceIte]
        exact ih (t + 1) (by omega) (by omega) m
  have hword_eq : ∀ (k : ℕ), word ⟨k % n, Nat.mod_lt _ hn⟩ = B (k + n - w % n) := by
    intro k
    dsimp [word, B]
    congr 1
    apply Fin.ext
    have hw : w % n < n := Nat.mod_lt w hn
    have h1 : (k % n + n - w % n) % n = (k + n - w % n) % n := by
      have : k % n + n - w % n = k % n + (n - w % n) := by omega
      have : k + n - w % n = k + (n - w % n) := by omega
      rw [‹k % n + n - w % n = _›, ‹k + n - w % n = _›, Nat.mod_add_mod]
    exact h1
  intro i
  have hi := hedge i
  rw [edgeSig_tableInputs hn table i (st i.val) (bt i)] at hi
  convert hi using 2
  funext bit
  rw [hword_eq (i.val + bit.val)]
  split_ifs with hbw
  · let r := w / n + 1
    have hrn : w ≤ r * n := by
      have hdiv := Nat.div_add_mod w n
      rw [Nat.mul_comm] at hdiv
      have := Nat.mod_lt w hn
      dsimp [r]; rw [Nat.add_mul, Nat.one_mul]; omega
    let m0 := i.val + r * n - (w - bit.val)
    have hm0_add : m0 + (w - bit.val) = i.val + r * n := by dsimp [m0]; omega
    have hbit := hS_bit (w - bit.val) bit.val (by omega) (by omega) m0
    rw [hm0_add] at hbit
    have hS_i : Sseq (i.val + r * n) = st i.val := by
      dsimp [Sseq]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
    rw [hS_i] at hbit
    rw [hbit]
    dsimp [B]
    congr 1
    apply Fin.ext
    have hwlt : w % n < n := Nat.mod_lt w hn
    have hdiv := Nat.div_add_mod w n
    rw [Nat.mul_comm] at hdiv
    have hdiff : m0 + (w / n) * n + w % n = i.val + bit.val + r * n := by
      dsimp [m0]; omega
    have hA : (m0 + w % n) % n = (i.val + bit.val) % n := by
      have : (m0 + (w / n) * n + w % n) % n = (m0 + w % n) % n := by
        rw [show m0 + (w / n) * n + w % n = (m0 + w % n) + (w / n) * n by omega,
          Nat.add_mul_mod_self_right]
      rw [← this, hdiff, Nat.add_mul_mod_self_right]
    have hB : ((i.val + bit.val + n - w % n) + w % n) % n = (i.val + bit.val) % n := by
      rw [show i.val + bit.val + n - w % n + w % n = (i.val + bit.val) + n by omega,
        Nat.add_mod_right]
    have hC : ((m0 + w % n) + (n - w % n)) % n = ((i.val + bit.val + n - w % n + w % n) + (n - w % n)) % n := by
      rw [Nat.add_mod (m0 + w % n), Nat.add_mod (i.val + bit.val + n - w % n + w % n), hA, hB]
    have hL : (m0 + w % n + (n - w % n)) % n = m0 % n := by
      rw [show m0 + w % n + (n - w % n) = m0 + n by omega, Nat.add_mod_right]
    have hR : (i.val + bit.val + n - w % n + w % n + (n - w % n)) % n = (i.val + bit.val + n - w % n) % n := by
      rw [show i.val + bit.val + n - w % n + w % n + (n - w % n) = (i.val + bit.val + n - w % n) + n by omega,
        Nat.add_mod_right]
    rw [hL, hR] at hC
    exact hC.symm
  · have hbe : bit.val = w := by omega
    rw [hbe]
    dsimp [B]
    congr 1
    apply Fin.ext
    have hwlt : w % n < n := Nat.mod_lt w hn
    have hdiv := Nat.div_add_mod w n
    have hsum : i.val + w + n - w % n = i.val + n * (w / n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    simp only [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

private theorem buildBackward (n w : ℕ) (A0 : Set (Sig (n * 2 ^ (w + 1))))
    (hInp : ∀ (k : Fin n) (s : Fin (2 ^ w)) (b : Bool), edgeSig n w k s b ∈ A0)
    (hF : (fun _ => false) ∈ A0) (hT : (fun _ => true) ∈ A0) :
    ∀ d (_hd : d ≤ n),
      Build A0
        ((⋃ s : Fin (2 ^ w), ⋃ t : Fin (2 ^ w), {reachDown n w d s t}) ∪
         (⋃ k : Fin n, ⋃ (_ : n - d ≤ k.val), ⋃ s : Fin (2 ^ w), ⋃ t : Fin (2 ^ w), {p0Sig n w k s t}))
        (3 * d * 4 ^ w) := by
  intro d hd
  induction d with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_mul]
    apply idleB
    rintro f (hf | hf)
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hf
      obtain ⟨s, t, rfl⟩ := hf
      by_cases hts : t = s
      · have : reachDown n w 0 s t = (fun _ => true) := by funext x; simp [reachDown, hts]
        rw [this]; exact hT
      · have : reachDown n w 0 s t = (fun _ => false) := by funext x; simp [reachDown, hts]
        rw [this]; exact hF
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hf
      obtain ⟨k, hk, _⟩ := hf
      omega
  | succ d ih =>
    have hdn : d < n := by omega
    let k : Fin n := ⟨n - 1 - d, by omega⟩
    let Bprev : Set (Sig (n * 2 ^ (w + 1))) :=
      (⋃ s : Fin (2 ^ w), ⋃ t : Fin (2 ^ w), {reachDown n w d s t}) ∪
      (⋃ k' : Fin n, ⋃ (_ : n - d ≤ k'.val), ⋃ s : Fin (2 ^ w), ⋃ t : Fin (2 ^ w), {p0Sig n w k' s t})
    have hIH : Build A0 Bprev (3 * d * 4 ^ w) := ih (by omega)
    let Fpair (p : Fin (2 ^ w) × Fin (2 ^ w)) : Set (Sig (n * 2 ^ (w + 1))) :=
      {p0Sig n w k p.1 p.2, reachDown n w (d + 1) p.1 p.2}
    have hStep : Build (A0 ∪ Bprev) (⋃ p ∈ allPairs (2 ^ w), Fpair p) ((allPairs (2 ^ w)).length * 3) := by
      apply listB Fpair 3 (allPairs (2 ^ w))
      intro ⟨s, t⟩ _
      have hr0 : reachDown n w (n - 1 - k.val) s (nextS t false) ∈ A0 ∪ Bprev := by
        have heq : n - 1 - k.val = d := by dsimp [k]; omega
        rw [heq]
        exact Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨nextS t false, rfl⟩⟩))
      have hr1 : reachDown n w (n - 1 - k.val) s (nextS t true) ∈ A0 ∪ Bprev := by
        have heq : n - 1 - k.val = d := by dsimp [k]; omega
        rw [heq]
        exact Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨nextS t true, rfl⟩⟩))
      have hp0 : Build (A0 ∪ Bprev) {p0Sig n w k s t} 1 :=
        andB (Or.inl (hInp k t false)) hr0
      have hp1 : Build ((A0 ∪ Bprev) ∪ {p0Sig n w k s t}) {p1Sig n w k s t} 1 :=
        andB (Or.inl (Or.inl (hInp k t true))) (Or.inl hr1)
      have hre : Build (((A0 ∪ Bprev) ∪ {p0Sig n w k s t}) ∪ {p1Sig n w k s t})
          {reachDown n w (d + 1) s t} 1 := by
        have hdk : d + 1 = n - k.val := by dsimp [k]; omega
        rw [hdk, reachDown_succ_eq n w k s t]
        exact orB (Or.inl (Or.inr rfl)) (Or.inr rfl)
      have h12 := seqB hp0 hp1
      have h123 := seqB h12 (relaxB hre (by intro a ha; simp only [Set.mem_union] at ha ⊢; tauto)
        Set.subset_union_right le_rfl)
      refine relaxB h123 le_rfl ?_ (by omega)
      intro f hf
      simp only [Fpair, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl
      · exact Or.inr (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inr rfl)
    have h4w : 2 ^ w * 2 ^ w = 4 ^ w := by
      rw [← Nat.pow_add, ← Nat.two_mul, Nat.pow_mul]
    have hlen : (allPairs (2 ^ w)).length * 3 = 3 * 4 ^ w := by
      rw [allPairs_length, h4w, Nat.mul_comm]
    refine relaxB (seqB hIH hStep) le_rfl ?_ (by rw [hlen]; linarith)
    rintro f (hf | hf)
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hf
      obtain ⟨s, t, rfl⟩ := hf
      exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨(s, t), Set.mem_iUnion.mpr ⟨mem_allPairs (s, t), Or.inr rfl⟩⟩))
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hf
      obtain ⟨k', hk', s, t, rfl⟩ := hf
      by_cases hkeq : k' = k
      · subst hkeq
        exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨(s, t), Set.mem_iUnion.mpr ⟨mem_allPairs (s, t), Or.inl rfl⟩⟩))
      · have hge : n - d ≤ k'.val := by
          have hne : k'.val ≠ n - 1 - d := fun h => hkeq (Fin.ext h)
          omega
        exact Or.inr (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨k', Set.mem_iUnion.mpr ⟨hge,
          Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨t, rfl⟩⟩⟩⟩)))

private theorem buildPrefix (n w : ℕ) (A : Set (Sig (n * 2 ^ (w + 1))))
    (hFeas : ∀ s : Fin (2 ^ w), feasSig n w s ∈ A)
    (hF : (fun _ => false) ∈ A) :
    ∀ m (_hm : m ≤ 2 ^ w),
      Build A
        ({prefSig n w m} ∪ ⋃ s : Fin (2 ^ w), ⋃ (_ : s.val < m), {pickSig n w s})
        (3 * m) := by
  intro m hm
  induction m with
  | zero =>
    simp only [Nat.mul_zero]
    apply idleB
    rintro f (rfl | hf)
    · exact hF
    · simp only [Set.mem_iUnion] at hf; obtain ⟨_, h, _⟩ := hf; omega
  | succ m ih =>
    have hmlt : m < 2 ^ w := by omega
    let sm : Fin (2 ^ w) := ⟨m, hmlt⟩
    let Bprev := {prefSig n w m} ∪ ⋃ s : Fin (2 ^ w), ⋃ (_ : s.val < m), {pickSig n w s}
    have h1 := ih (by omega)
    have hnot : Build (A ∪ Bprev) {fun x => !(prefSig n w m x)} 1 :=
      notB (Or.inr (Or.inl rfl))
    have hpick : Build ((A ∪ Bprev) ∪ {fun x => !(prefSig n w m x)}) {pickSig n w sm} 1 :=
      andB (Or.inl (Or.inl (hFeas sm))) (Or.inr rfl)
    have hnextP : Build (((A ∪ Bprev) ∪ {fun x => !(prefSig n w m x)}) ∪ {pickSig n w sm})
        {prefSig n w (m + 1)} 1 := by
      have heq : prefSig n w (m + 1) = fun x => prefSig n w m x || feasSig n w sm x := by
        funext x; simp [prefSig, hmlt, sm]
      rw [heq]
      exact orB (Or.inl (Or.inl (Or.inr (Or.inl rfl)))) (Or.inl (Or.inl (Or.inl (hFeas sm))))
    have hstep := seqB (seqB hnot hpick)
      (relaxB hnextP (by intro a ha; simp only [Set.mem_union] at ha ⊢; tauto) Set.subset_union_right le_rfl)
    refine relaxB (seqB h1 hstep) le_rfl ?_ (by omega)
    rintro f (rfl | hf)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hf
      obtain ⟨s, hsm, rfl⟩ := hf
      by_cases hlt : s.val < m
      · exact Or.inr (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hlt, rfl⟩⟩)))
      · have hseq : s = sm := Fin.ext (by dsimp [sm]; omega)
        subst hseq
        exact Or.inr (Or.inr (Or.inl (Or.inr rfl)))

private theorem buildForward (n w : ℕ) (A : Set (Sig (n * 2 ^ (w + 1))))
    (hPick : ∀ s : Fin (2 ^ w), pickSig n w s ∈ A)
    (hP0 : ∀ (k : Fin n) (s t : Fin (2 ^ w)), p0Sig n w k s t ∈ A)
    (hF : (fun _ => false) ∈ A) :
    ∀ k (_hk : k ≤ n),
      Build A
        ((⋃ s : Fin (2 ^ w), ⋃ t : Fin (2 ^ w), {actSig n w k s t}) ∪
         (⋃ j : Fin n, ⋃ (_ : j.val < k), {stepBitSig n w j}))
        (5 * k * 4 ^ w) := by
  intro k hk
  induction k with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_mul]
    apply idleB
    rintro f (hf | hf)
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hf
      obtain ⟨s, t, rfl⟩ := hf
      by_cases hts : t = s
      · have : actSig n w 0 s t = pickSig n w s := by funext x; simp [actSig, hts]
        rw [this]; exact hPick s
      · have : actSig n w 0 s t = (fun _ => false) := by funext x; simp [actSig, hts]
        rw [this]; exact hF
    · simp only [Set.mem_iUnion] at hf; obtain ⟨_, h, _⟩ := hf; omega
  | succ k ih =>
    have hkn : k < n := by omega
    let kf : Fin n := ⟨k, hkn⟩
    let Bprev := (⋃ s : Fin (2 ^ w), ⋃ t : Fin (2 ^ w), {actSig n w k s t}) ∪
      (⋃ j : Fin n, ⋃ (_ : j.val < k), {stepBitSig n w j})
    have hIH := ih (by omega)
    let Gpair (p : Fin (2 ^ w) × Fin (2 ^ w)) : Set (Sig (n * 2 ^ (w + 1))) :=
      {go0Sig n w kf p.1 p.2, go1Sig n w kf p.1 p.2}
    have hGo : Build (A ∪ Bprev) (⋃ p ∈ allPairs (2 ^ w), Gpair p) ((allPairs (2 ^ w)).length * 3) := by
      apply listB Gpair 3 (allPairs (2 ^ w))
      intro ⟨s, t⟩ _
      have hact : actSig n w k s t ∈ A ∪ Bprev :=
        Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨t, rfl⟩⟩))
      have hp0 : p0Sig n w kf s t ∈ A ∪ Bprev := Or.inl (hP0 kf s t)
      have hg0 : Build (A ∪ Bprev) {go0Sig n w kf s t} 1 := andB hact hp0
      have hnp : Build ((A ∪ Bprev) ∪ {go0Sig n w kf s t}) {fun x => !(p0Sig n w kf s t x)} 1 :=
        notB (Or.inl hp0)
      have hg1 : Build (((A ∪ Bprev) ∪ {go0Sig n w kf s t}) ∪ {fun x => !(p0Sig n w kf s t x)})
          {go1Sig n w kf s t} 1 :=
        andB (Or.inl (Or.inl hact)) (Or.inr rfl)
      have h123 := seqB (seqB hg0 hnp)
        (relaxB hg1 (by intro a ha; simp only [Set.mem_union] at ha ⊢; tauto) Set.subset_union_right le_rfl)
      refine relaxB h123 le_rfl ?_ (by omega)
      intro f hf
      simp only [Gpair, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl
      · exact Or.inr (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inr rfl)
    let Bgo := ⋃ p ∈ allPairs (2 ^ w), Gpair p
    have hBit : Build ((A ∪ Bprev) ∪ Bgo) {stepBitSig n w kf} (allPairs (2 ^ w)).length := by
      let xs := (allPairs (2 ^ w)).map fun p => go1Sig n w kf p.1 p.2
      have hmem : ∀ f ∈ xs, f ∈ (A ∪ Bprev) ∪ Bgo := by
        intro f hf
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
        exact Or.inr (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, Or.inr rfl⟩⟩)
      have heq : (fun x => xs.any fun f => f x) = stepBitSig n w kf := by
        funext x; simp [xs, stepBitSig, List.any_map]; rfl
      have hor := orListB xs hmem (Or.inl (Or.inl hF))
      rw [heq] at hor
      simpa [xs] using hor
    have hAct : Build (((A ∪ Bprev) ∪ Bgo) ∪ {stepBitSig n w kf})
        (⋃ p ∈ allPairs (2 ^ w), {actSig n w (k + 1) p.1 p.2}) ((allPairs (2 ^ w)).length * 1) := by
      apply listB (fun p => {actSig n w (k + 1) p.1 p.2}) 1 (allPairs (2 ^ w))
      intro ⟨s, t'⟩ _
      cases w with
      | zero =>
        have heq : actSig n 0 (k + 1) s t' = actSig n 0 k s t' := by
          funext x; simp [actSig, hkn]
        rw [heq]
        exact relaxB (idleB (Set.singleton_subset_iff.mpr
          (Or.inl (Or.inl (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨t', rfl⟩⟩)))))))
          le_rfl Set.subset_union_right (by omega)
      | succ w' =>
        have hgo_mem : ∀ (t : Fin (2 ^ (w' + 1))),
            (if topBit t' then go1Sig n (w' + 1) kf s t else go0Sig n (w' + 1) kf s t) ∈
              ((A ∪ Bprev) ∪ Bgo) ∪ {stepBitSig n (w' + 1) kf} := by
          intro t
          split_ifs
          · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨(s, t), Set.mem_iUnion.mpr ⟨mem_allPairs (s, t), Or.inr rfl⟩⟩))
          · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨(s, t), Set.mem_iUnion.mpr ⟨mem_allPairs (s, t), Or.inl rfl⟩⟩))
        have heq : actSig n (w' + 1) (k + 1) s t' =
            fun x => (if topBit t' then go1Sig n (w' + 1) kf s (pred0 t') else go0Sig n (w' + 1) kf s (pred0 t')) x ||
                     (if topBit t' then go1Sig n (w' + 1) kf s (pred1 t') else go0Sig n (w' + 1) kf s (pred1 t')) x := by
          funext x
          unfold actSig
          simp only [hkn, ↓reduceDIte]
          cases htb : topBit t' <;> simp [go0Sig, go1Sig, kf]
        rw [heq]
        exact orB (hgo_mem (pred0 t')) (hgo_mem (pred1 t'))
    have h4w : 2 ^ w * 2 ^ w = 4 ^ w := by
      rw [← Nat.pow_add, ← Nat.two_mul, Nat.pow_mul]
    have hlen : (allPairs (2 ^ w)).length = 4 ^ w := by rw [allPairs_length, h4w]
    have hstep := seqB (seqB hGo hBit)
      (relaxB hAct (by intro a ha; simp only [Set.mem_union] at ha ⊢; tauto) Set.subset_union_right le_rfl)
    refine relaxB (seqB hIH hstep) le_rfl ?_ (by rw [hlen]; linarith)
    rintro f (hf | hf)
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hf
      obtain ⟨s, t, rfl⟩ := hf
      exact Or.inr (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨(s, t), Set.mem_iUnion.mpr ⟨mem_allPairs (s, t), rfl⟩⟩)))
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hf
      obtain ⟨j, hjk, rfl⟩ := hf
      by_cases hlt : j.val < k
      · exact Or.inr (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hlt, rfl⟩⟩)))
      · have hjeq : j = kf := Fin.ext (by dsimp [kf]; omega)
        subst hjeq
        exact Or.inr (Or.inr (Or.inl (Or.inr rfl)))

private theorem solve (n w : ℕ) (hn : 0 < n) :
    let I := n * 2 ^ (w + 1)
    ∃ (C : Circuit) (outBit : Fin n → Fin (I + C.size)),
      FanInTwo C ∧ ReadsBack I C ∧ C.output < I + C.size ∧
      C.size ≤ 8 * n * 4 ^ w + 3 * 2 ^ w + 2 ∧
      ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
        let inputs := List.ofFn (fun j : Fin I =>
          table ⟨(j.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
            (fun bit => j.val.testBit bit.val))
        let valid := fun word : Fin n → Bool =>
          ∀ i : Fin n,
            table i (fun bit => word ⟨(i.val + bit.val) % n, Nat.mod_lt _ hn⟩) = true
        let picked := fun pos : Fin n => (C.wires inputs).getD (outBit pos).val false
        (C.eval inputs = true ↔ ∃ word, valid word) ∧
        (C.eval inputs = true → valid picked) := by
  let I := n * 2 ^ (w + 1)
  let Inp : Set (Sig I) := Set.range (fun j : Fin I => fun x : Fin I → Bool => x j)
  have hC0 : Build Inp {fun _ => false, fun _ => true} 2 := by
    simpa only [Set.singleton_union] using
      seqB (constB (A := Inp) false) (constB (A := Inp ∪ {fun _ => false}) true)
  let A0 := Inp ∪ {fun _ => false, fun _ => true}
  have hF0 : (fun _ => false) ∈ A0 := Or.inr (Or.inl rfl)
  have hT0 : (fun _ => true) ∈ A0 := Or.inr (Or.inr rfl)
  have hBack := buildBackward n w A0
    (fun k s b => Or.inl ⟨edgeIdx n w k s b, rfl⟩) hF0 hT0 n le_rfl
  let Bback := (⋃ s : Fin (2 ^ w), ⋃ t : Fin (2 ^ w), {reachDown n w n s t}) ∪
    (⋃ k : Fin n, ⋃ (_ : n - n ≤ k.val), ⋃ s : Fin (2 ^ w), ⋃ t : Fin (2 ^ w), {p0Sig n w k s t})
  have hPref := buildPrefix n w (A0 ∪ Bback)
    (fun s => Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨s, rfl⟩⟩)))
    (Or.inl hF0) (2 ^ w) le_rfl
  let Bpref := {prefSig n w (2 ^ w)} ∪ ⋃ s : Fin (2 ^ w), ⋃ (_ : s.val < 2 ^ w), {pickSig n w s}
  have hFwd := buildForward n w ((A0 ∪ Bback) ∪ Bpref)
    (fun s => Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨s.isLt, rfl⟩⟩)))
    (fun k s t => Or.inl (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨by omega,
      Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨t, rfl⟩⟩⟩⟩))))
    (Or.inl (Or.inl hF0)) n le_rfl
  let Bfwd := (⋃ s : Fin (2 ^ w), ⋃ t : Fin (2 ^ w), {actSig n w n s t}) ∪
    (⋃ j : Fin n, ⋃ (_ : j.val < n), {stepBitSig n w j})
  have hAll := seqB hC0 (seqB (seqB hBack hPref)
    (relaxB hFwd (by intro a ha; simp only [A0, Bback, Bpref, Set.mem_union] at ha ⊢; tauto)
      Set.subset_union_right le_rfl))
  obtain ⟨c, hc, hS⟩ := hAll.run (startSched I) le_rfl
  let outS : Sig I := prefSig n w (2 ^ w)
  let bitS : Fin n → Sig I := fun pos => stepBitSig n w ⟨(pos.val + n - w % n) % n, Nat.mod_lt _ hn⟩
  have hout_mem : outS ∈ Inp ∪ ({fun _ => false, fun _ => true} ∪ ((Bback ∪ Bpref) ∪ Bfwd)) :=
    Or.inr (Or.inr (Or.inl (Or.inr (Or.inl rfl))))
  have hbit_mem : ∀ pos : Fin n, bitS pos ∈ Inp ∪ ({fun _ => false, fun _ => true} ∪ ((Bback ∪ Bpref) ∪ Bfwd)) := by
    intro pos
    let j : Fin n := ⟨(pos.val + n - w % n) % n, Nat.mod_lt _ hn⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨j.isLt, rfl⟩⟩))))
  obtain ⟨C, outBit, hsz, hrb, hfan, hout_lt, heval, hbits⟩ := finishMulti hS outS hout_mem bitS hbit_mem
  have hsz_bound : C.size ≤ 8 * n * 4 ^ w + 3 * 2 ^ w + 2 := by
    have hsum : 2 + (3 * n * 4 ^ w + 3 * 2 ^ w + 5 * n * 4 ^ w) = 8 * n * 4 ^ w + 3 * 2 ^ w + 2 := by ring
    omega
  refine ⟨C, outBit, hfan, hrb, hout_lt, hsz_bound, ?_⟩
  intro table
  let x := tableInputs hn table
  have hev : C.eval (List.ofFn x) = prefSig n w (2 ^ w) x := heval x
  have hpick_eq : ∀ pos : Fin n,
      (C.wires (List.ofFn x)).getD (outBit pos).val false =
        stepBitSig n w ⟨(pos.val + n - w % n) % n, Nat.mod_lt _ hn⟩ x :=
    fun pos => hbits pos x
  have hfwd_valid : prefSig n w (2 ^ w) x = true →
      ∀ i : Fin n,
        table i (fun bit =>
          (C.wires (List.ofFn x)).getD (outBit ⟨(i.val + bit.val) % n, Nat.mod_lt _ hn⟩).val false) = true := by
    intro htrue
    obtain ⟨s0, hs0⟩ := pickSig_exists x htrue
    obtain ⟨hclose_r, _, hedges⟩ := greedy_inv x s0 hs0 n le_rfl
    have hclose : greedyState n w x s0 n = greedyState n w x s0 0 := by
      have h0 : n - n = 0 := Nat.sub_self n
      rw [h0] at hclose_r
      simpa [reachDown, greedyState] using hclose_r
    have hnext : ∀ k : Fin n, greedyState n w x s0 (k.val + 1) =
        nextS (greedyState n w x s0 k.val) (greedyBit n w x s0 k) := by
      intro k
      simp [greedyState, k.isLt, greedyBit]
    have hstep_eq : ∀ k : Fin n, stepBitSig n w k x = greedyBit n w x s0 k := by
      intro k
      obtain ⟨_, hactk, _⟩ := greedy_inv x s0 hs0 k.val (by omega)
      apply Bool.eq_iff_iff.mpr
      simp only [stepBitSig, List.any_eq_true, go1Sig, Bool.and_eq_true]
      constructor
      · rintro ⟨⟨s, t⟩, _, h1, h2⟩
        rw [hactk s t, decide_eq_true_eq] at h1
        rcases h1 with ⟨rfl, rfl⟩
        exact h2
      · intro hgb
        refine ⟨(s0, greedyState n w x s0 k.val), mem_allPairs _, ?_, hgb⟩
        rw [hactk]; simp
    have hcv := cycle_to_valid hn table (greedyState n w x s0) (greedyBit n w x s0) hnext hclose
      (fun k => hedges k k.isLt)
    intro i
    convert hcv i using 2
    funext bit
    rw [hpick_eq, hstep_eq]
  refine ⟨⟨fun h => ⟨fun pos => (C.wires (List.ofFn x)).getD (outBit pos).val false, hfwd_valid (hev ▸ h)⟩, ?_⟩,
    fun h => hfwd_valid (hev ▸ h)⟩
  rintro ⟨word, hvalid⟩
  change C.eval (List.ofFn x) = true
  rw [hev]
  exact (prefSig_iff x (2 ^ w) le_rfl).mpr
    ⟨wordAtState hn word 0, (wordAtState hn word 0).isLt,
      by simpa [feasSig] using reachDown_of_valid hn table word hvalid n le_rfl⟩

end PEqualNP.Outside.L_clb_043_aux

theorem PEqualNP.Outside.L_clb_043 : (∀ (n w : ℕ) (hn : 0 < n),
  let I := n * 2 ^ (w + 1)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin n → Fin (I + C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
    C.output < I + C.size ∧
    C.size ≤ 8 * n * 4 ^ w + 3 * 2 ^ w + 2 ∧
    ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := List.ofFn (fun j : Fin I =>
        table ⟨(j.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun bit => j.val.testBit bit.val))
      let valid := fun word : Fin n → Bool =>
        ∀ i : Fin n,
          table i (fun bit => word ⟨(i.val + bit.val) % n, Nat.mod_lt _ hn⟩) = true
      let picked := fun pos : Fin n => (C.wires inputs).getD (outBit pos).val false
      (C.eval inputs = true ↔ ∃ word, valid word) ∧
      (C.eval inputs = true → valid picked)) :=
  PEqualNP.Outside.L_clb_043_aux.solve
