import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_48557
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 128
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
lemma bin_comm_flip (d : Nat) (hd : d < 4) (a b : Nat) : bin d a b = bin (flipOp d) b a := by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
lemma flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  interval_cases d <;> decide
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^128) (hb : b < 2^128) : bin d a b < 2^128 := by
  have h1 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x &&& y) < 2^128 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ||| y) < 2^128 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ^^^ y) < 2^128 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
lemma bin_bit0 (d a b : Nat) (ha : a.testBit 0 = false) (hb : b.testBit 0 = false) :
    (bin d a b).testBit 0 = false := by
  rw [testBit_bin]
  rcases d with _ | _ | _ | d <;> simp [ha, hb]
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_size {T k S} (h : Live T k S) : S.card ≤ k + 1 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; simp
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, hf, tail⟩ := h
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have ht := ih tail
    rw [Finset.card_insert_of_notMem hu] at ht
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def swZero : SWire := (false, 0)
def swFlip (a : SWire) : SWire := (!a.1, a.2)
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def swMeet (a b : SWire) : SWire := (a.1 && b.1, bin (opIdx a.1 b.1) a.2 b.2)
def swJoin (a b : SWire) : SWire := swFlip (swMeet (swFlip a) (swFlip b))
def swRead (j : Nat) (a : SWire) : Bool := a.1 != a.2.testBit j
lemma swRead_zero (j : Nat) : swRead j swZero = false := by simp [swRead, swZero]
lemma swRead_flip (j : Nat) (a : SWire) : swRead j (swFlip a) = !(swRead j a) := by
  cases a with | mk s v => cases s <;> cases h : v.testBit j <;> simp [swRead, swFlip, h]
lemma swRead_meet (j : Nat) (a b : SWire) : swRead j (swMeet a b) = (swRead j a && swRead j b) := by
  obtain ⟨s, u⟩ := a; obtain ⟨t, v⟩ := b
  cases s <;> cases t <;> cases hu : u.testBit j <;> cases hv : v.testBit j <;>
    simp [swRead, swMeet, opIdx, testBit_bin, hu, hv]
lemma swRead_join (j : Nat) (a b : SWire) : swRead j (swJoin a b) = (swRead j a || swRead j b) := by
  simp only [swJoin, swRead_flip, swRead_meet]
  cases swRead j a <;> cases swRead j b <;> rfl
def swGate (w : List SWire) (g : Gate) : SWire :=
  let arg := fun i => w.getD i swZero
  match g.op, g.inputs with
  | .not, xs => swFlip (arg (xs.headD w.length))
  | .and, [] => swFlip swZero
  | .or, [] => swZero
  | .and, [i] | .or, [i] => arg i
  | .and, i :: j :: _ => swMeet (arg i) (arg j)
  | .or, i :: j :: _ => swJoin (arg i) (arg j)
  | _, _ => swZero
def swExec (gs : List Gate) (w : List SWire) : List SWire :=
  gs.foldl (fun w g => w ++ [swGate w g]) w
def isBin (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma get_simple (w : List SWire) (i : Nat) : simple w (w.getD i swZero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
lemma swGate_priced (w : List SWire) (g : Gate) : priced w (isBin g) (swGate w g).2 := by
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | not => exact Or.inl (get_simple w _)
  | _ => exact Or.inl (Or.inl rfl)
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^128 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^128 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^128 ∧ (w.getD i swZero).2.testBit 0 = false := by
    simp only [List.getD_eq_getElem?_getD]
    cases eq : w[i]? with
    | none => exact hz
    | some a => exact hw a (List.mem_of_getElem? eq)
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | not => exact hg (xs.headD w.length)
  | _ => exact hz
lemma swExec_lt (gs : List Gate) (w : List SWire)
    (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hw u hu
    · rw [List.mem_singleton.mp hu]; exact swGate_lt w hw g
lemma swRead_get (j : Nat) (w : List SWire) (i : Nat) :
    (w.map (swRead j)).getD i false = swRead j (w.getD i swZero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [swRead_zero]
lemma swGate_read (w : List SWire) (g : Gate)
    (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (j : Nat) :
    swRead j (swGate w g) = g.op.eval (g.inputs.map fun i => (w.map (swRead j)).getD i false) := by
  simp_rw [swRead_get]
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := legal
  rcases hop with rfl | rfl | rfl <;>
    rcases xs with _ | ⟨i, _ | ⟨k, _ | ⟨h, rest⟩⟩⟩ <;>
    simp_all [swGate, GateOp.eval, swRead_flip, swRead_meet, swRead_join, swRead_zero]
lemma swExec_read (j : Nat) (gs : List Gate) (w : List SWire)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (swExec gs w).map (swRead j) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (swRead j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (swExec gs (w ++ [swGate w g])).map (swRead j) = _
    rw [ih _ (fun v hv => legal v (List.mem_cons_of_mem _ hv))]
    simp [swGate_read w g (legal g List.mem_cons_self) j]
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
lemma extract_live {T} (hT : T ≠ 0) (gs : List Gate) (w : List SWire)
    (found : T ∈ reps (swExec gs w)) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {T}, by simp, ⟨rfl, hT⟩, by simpa [swExec] using found⟩
  | cons g gs ih =>
    obtain ⟨k, S, lim, h, sub⟩ := ih (w ++ [swGate w g]) found
    have sub' : ∀ a ∈ S, a ∈ reps w ++ [(swGate w g).2] := by simpa [reps] using sub
    obtain ⟨l, V, cost, hl, raw⟩ := pull_live h (swGate_priced w g) sub'
    refine ⟨l, V, ?_, hl, raw⟩
    rw [List.countP_cons]
    cases e : isBin g <;> simp [e] at cost ⊢ <;> omega
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 128 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 128 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^128) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Impossible (T : Nat) (cap : Nat) (S : Finset Nat) : Prop :=
  ∀ k ≤ cap, ¬Live T k S
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma lower_of_impossible {roots : List Nat} {T L : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (ess : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hnz : normPack (obs T) ≠ 0 := by rwa [hnormT]
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left hnz
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha'
    exact normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have heq : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    exact ⟨fun ha' => raw_required run roots a sub (ess a ha'), sub a⟩
  by_contra! small
  exact noRun k (by omega) (heq.symm ▸ run)
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def Slice (raw : List Nat) (T d : Nat) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Nat),
    (∀ r : Row, d.testBit (f r).val = true) ∧
    (∀ a ∈ raw, Avail (roots.map obs) (restrictW f (obs a))) ∧
    ¬Constant (restrictW f (obs T)) ∧
    ∀ p bank, Reach (roots.map obs) p bank → Avail bank (restrictW f (obs T)) → L ≤ p
def isConstM (d a : Nat) : Bool := (a &&& d == 0) || (a &&& d == d)
def availM (d : Nat) (pm : List Nat) (a : Nat) : Bool :=
  let m := a &&& d
  m == 0 || m == d || pm.contains m || pm.contains (d ^^^ m)
lemma masked_eq_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (b &&& d)) : restrictW f (obs a) = restrictW f (obs b) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_zero_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = 0) : restrictW f (obs a) = fun _ => false := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_one_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = d) : restrictW f (obs a) = fun _ => true := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_comp_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (d ^^^ (b &&& d))) : restrictW f (obs a) = invW (restrictW f (obs b)) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simp only [Nat.testBit_and, Nat.testBit_xor, dom r, Bool.and_true] at h
  simp only [restrictW, obs, invW, h]
  cases b.testBit (f r).val <;> rfl
def poolSupply (f : Row → Row) (bank : List Wire) (pool : List Nat) : Prop :=
  ∀ a ∈ pool, Avail bank (restrictW f (obs a))
lemma availM_sound {f : Row → Row} {d a : Nat} {bank : List Wire} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hs : poolSupply f bank pool)
    (ok : availM d (pool.map (· &&& d)) a = true) :
    Avail bank (restrictW f (obs a)) := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at ok
  rcases ok with ((h0 | h1) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero_obs dom h0⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one_obs dom h1⟩)
  · exact (masked_eq_obs dom he.symm) ▸ hs v hv
  · have hinv := avail_inv (hs v hv)
    have hcomp : restrictW f (obs a) = invW (restrictW f (obs v)) := by
      have hx : (a &&& d) = d ^^^ (v &&& d) := by
        have := congrArg (d ^^^ ·) he
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_self] using this.symm
      exact masked_comp_obs dom hx
    exact hcomp ▸ hinv
abbrev Choice := Nat × Nat × Nat
def choiceVal (c : Choice) : Nat := bin c.1 c.2.1 c.2.2
def choiceOK (d : Nat) (pm : List Nat) (c : Choice) : Bool :=
  decide (c.1 < 4) && availM d pm c.2.1 && availM d pm c.2.2
def makePool (d : Nat) (pool : List Nat) : List Choice → Option (List Nat)
  | [] => some pool
  | c :: cs => if choiceOK d (pool.map (· &&& d)) c then makePool d (choiceVal c :: pool) cs else none
lemma pay_choice {f : Row → Row} {d : Nat} {roots bank q} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d (pool.map (· &&& d)) c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  have ha := availM_sound dom hs valid.1.2
  have hb := availM_sound dom hs valid.2
  have hprep : ∃ op x y, comb4 c.1 (restrictW f (obs c.2.1)) (restrictW f (obs c.2.2)) = comb2 op x y ∧
      Avail bank x ∧ Avail bank y := by
    have hd := valid.1.1
    interval_cases c.1
    · exact ⟨false, _, _, rfl, ha, hb⟩
    · exact ⟨true, _, _, rfl, ha, hb⟩
    · exact ⟨false, _, _, rfl, ha, avail_inv hb⟩
    · exact ⟨false, _, _, rfl, avail_inv ha, hb⟩
  obtain ⟨op, x, y, eq, hx, hy⟩ := hprep
  refine ⟨comb2 op x y :: bank, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · have hcv : restrictW f (obs (choiceVal c)) = comb2 op x y := by
      rw [← eq]; funext r; simp only [choiceVal, restrictW, obs, testBit_bin, comb4, comb2, invW]
      rcases c.1 with _ | _ | _ | d' <;> rfl
    exact hcv ▸ Or.inl (by simp)
  · exact avail_cons _ (hs v hv)
lemma makePool_sound {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {res} (ok : makePool d pool cs = some res) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next res := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction
lemma count_constM {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (ws : List Nat) : ws.countP (isConstM d) ≤ wmass ((ws.map obs).map (restrictW f)) := by
  classical
  induction ws with
  | nil => simp [wmass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, wmass, List.sum_cons] at ih ⊢
    cases h : isConstM d a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih.trans (Nat.le_add_left _ _)
    · have hc : Constant (restrictW f (obs a)) := by
        simp only [isConstM, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h0 | h1
        · exact ⟨false, masked_zero_obs dom h0⟩
        · exact ⟨true, masked_one_obs dom h1⟩
      simp only [ite_true, wcost, hc]
      omega
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  c.pm = c.wires.map (· &&& c.dom) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map fun pool => ⟨d, lb, cs.length, pool, pool.map (· &&& d)⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨rfl, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let z := choiceVal op
  let extra := !(availM c.dom c.pm z)
  decide (k + c.paid + extra.toNat < c.lb + (z :: rest).countP (isConstM c.dom)) &&
    rest.all (availM c.dom c.pm) && (!extra || choiceOK c.dom c.pm op)
lemma scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  obtain ⟨hpm, f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  intro t ht run
  have finish (n : Nat) (out : List Wire) (hr : Reach (roots.map obs) n out)
      (hsup : poolSupply f out (choiceVal op :: rest))
      (hle : n = c.paid + (!(availM c.dom c.pm (choiceVal op))).toNat) : False := by
    have hcov : Supply out (((choiceVal op :: rest).map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact hsup a ha
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction nc (restrict_run f (live_to_run run (choiceVal op :: rest) nd rfl)) (roots.map obs) hr hcov
    have hlo := lo q next hq hav
    have hcm := count_constM dom (choiceVal op :: rest)
    have hineq := cut.1.1
    omega
  cases hav : availM c.dom c.pm (choiceVal op) with
  | true =>
    apply finish c.paid bank hp _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact availM_sound dom hs (hpm ▸ hav)
    · exact availM_sound dom hs (hpm ▸ cut.1.2 a ha)
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      exact hpm ▸ h2
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (hpm ▸ cut.1.2 a ha)
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (127 ^^^ z)) ||| o) % 128, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 128
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 128 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^128) (hb : b < 2^128) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 128 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^128) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^128 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^128 := hS a (by simp)
    have hblt : b < 2^128 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^128 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^128 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^128 := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact hzlt; exact hUlt x hx
    have nr := ih tail htail_lt
    simp only [Finset.image_insert, renameW_bin] at nr ⊢
    refine ⟨U.image (renameW f), renameW f a, renameW f b, d, hd, rfl,
      fun hz => ha (renameW_inj f onto halt (by decide) (hz.trans (renameW_zero f).symm)),
      fun hz => hb (renameW_inj f onto hblt (by decide) (hz.trans (renameW_zero f).symm)),
      fun heq => hab (renameW_inj f onto halt hblt heq), ?_, nr⟩
    intro hm
    rw [← renameW_bin] at hm
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt halt heq]; simp)
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt hblt heq]; simp)
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
    exact fresh (by rw [renameW_inj f onto hzlt (hUlt x hx) heq.symm]; simp [hx])
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^128) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0
def ALL128 : Nat := 0xffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 128, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL128 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 7) (hj : j < 7) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 7 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL128 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
  | true =>
    obtain ⟨heq, h10, h01⟩ := hr.1 hms
    rw [heq]
    by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
    · simp [hd, h10 hd, h01]
    · simp [hd, h01]
  | false =>
    rcases hr.2 hms with ⟨hd, h10, heq, h01⟩ | ⟨h10, h01, heq⟩
    · simp [hd, h10, heq, h01]
    · by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
      · simp [hd, h10 hd, h01, heq]
      · simp [hd, h01, heq]
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) : swapWord i j w < 2^128 := by
  have hi : i < 7 := by omega
  have h1 : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^128 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^128 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^128 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 7)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^128) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^128 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hr⟩, testBit_renameW _ _ (swapRow p.1 p.2 ⟨r, hr⟩), testBit_renameW _ _ ⟨r, hr⟩]
      rfl
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega)))]
lemma permRow_surj (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) :
    Function.Surjective (permRow swaps) := by
  induction swaps with
  | nil => intro r; exact ⟨r, rfl⟩
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro r
    obtain ⟨q, hq⟩ := ih hv.2 r
    refine ⟨swapRow p.1 p.2 q, ?_⟩
    change permRow ps (swapRow p.1 p.2 (swapRow p.1 p.2 q)) = r
    rw [swapRow_invol p.1 p.2 (by omega) hv.1.2, hq]
lemma permRow_rev_cancel (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) (r : Row) :
    permRow swaps.reverse (permRow swaps r) = r := by
  induction swaps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
        swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
      simp [permRow, List.reverse_cons, List.foldl_append]
    rw [h1, ih hv.2, swapRow_invol p.1 p.2 (by omega) hv.1.2]
lemma rotate_impossible {T n : Nat} {ws : List Nat} (hi : Impossible T n ws.toFinset)
    (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (hT : T < 2^128) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^128) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^128 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^128 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
  have run' := live_renameW run hr (permRow swaps.reverse) (permRow_surj swaps.reverse hvr)
  have hT' : renameW (permRow swaps.reverse) T = T := by
    conv_lhs => rw [← hfix]
    exact hinv_word T hT
  have hS' : (ws.map (permWord swaps)).toFinset.image (renameW (permRow swaps.reverse)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hinv_word x (hw x hx)]
    · intro ha
      exact ⟨permWord swaps a, ⟨a, ha, rfl⟩, hinv_word a (hw a ha)⟩
  rw [hT', hS'] at run'
  exact hi k hk run'
abbrev Decor := Nat × Nat × Nat
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1, bin d x.2.1 y.2.1, bin d x.2.2 y.2.2)
def dsep (x : Decor) : Nat := x.2.1 ^^^ x.2.2
def projBits (rows : List Nat) (w : Nat) : Nat :=
  rows.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0
lemma testBit_projBits (rows : List Nat) (w i : Nat) :
    (projBits rows w).testBit i = match rows[i]? with | none => false | some r => w.testBit r := by
  induction rows generalizing i with
  | nil => simp [projBits]
  | cons r rs ih =>
    simp only [projBits, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.not_le.mpr (by decide : 0 < 1)]
      cases w.testBit r <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      have h0 : (if w.testBit r then (1 : Nat) else 0).testBit (i + 1) = false := by
        cases w.testBit r
        · simp
        · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
      rw [h0, Bool.or_false]
      exact ih i
lemma projBits_bin (rows : List Nat) (d a b : Nat) :
    projBits rows (bin d a b) = bin d (projBits rows a) (projBits rows b) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_projBits, testBit_bin, testBit_projBits, testBit_projBits]
  cases rows[i]? with
  | none => rcases d with _ | _ | _ | d <;> rfl
  | some r => exact testBit_bin d a b r
def faithful (pos neg : List Nat) (x : Decor) : Prop :=
  x.2.1 = projBits pos x.1 ∧ x.2.2 = projBits neg x.1
lemma faithful_bin {pos neg x y} (d : Nat) (hx : faithful pos neg x) (hy : faithful pos neg y) :
    faithful pos neg (dbin d x y) :=
  ⟨by rw [dbin, hx.1, hy.1, projBits_bin], by rw [dbin, hx.2, hy.2, projBits_bin]⟩
def goodPairs (T : Nat) (pos neg : List Nat) : Prop :=
  pos.length = neg.length ∧ ∀ i < pos.length,
    T.testBit (pos.getD i 0) = true ∧ T.testBit (neg.getD i 0) = false
def fullMask (n : Nat) : Nat := (1 <<< n) - 1
abbrev Cov := Nat × Nat × Nat
def addCov (z : Nat) (c : Cov) : Cov :=
  (z ||| c.1, (z ^^^ (z &&& c.1)) ||| (c.2.1 ^^^ (c.2.1 &&& z)),
   (z &&& c.2.1) ||| (c.2.2 ^^^ (c.2.2 &&& z)))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (dsep a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := c.1 ^^^ (c.1 &&& (c.2.1 &&& a))
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
lemma cov_one (c : Cov) (a : Nat) : takeOne (addCov a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOne, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
lemma cov_two (c : Cov) (a b : Nat) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwo, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma addCov_swap (c : Cov) (a b : Nat) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [addCov, Nat.testBit_or]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
      simp only [addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma cov_perm {l r : List Decor} (h : l.Perm r) : coverage l = coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (dsep a)) ih
  | swap _ _ _ => exact addCov_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
def delOne (ws : List Decor) (a : Decor) (k : Bool) : List Decor := if k then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
def restCov (c : Cov) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOne c b) else if kb then takeOne c a else takeTwo c a b
lemma cov_delOne {ws : List Decor} (a : Decor) (ha : a ∈ ws) (k : Bool) :
    (coverage (delOne ws a k)).1 = if k then (coverage ws).1 else takeOne (coverage ws) (dsep a) := by
  cases k
  · change (coverage (ws.erase a)).1 = _
    rw [cov_perm (List.perm_cons_erase ha)]
    exact (cov_one _ _).symm
  · rfl
lemma cov_delTwo {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb := by
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
    have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hbm))
    change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm hp]
    exact (cov_two _ _ _).symm
  · exact cov_delOne a ha false
  · exact cov_delOne b hb false
  · rfl
lemma cov_testBit (ws : List Decor) (i : Nat) :
    (coverage ws).1.testBit i = true ↔ ∃ x ∈ ws, (dsep x).testBit i = true := by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change (dsep a ||| (coverage ws).1).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp
lemma cov_required {T k pos neg} {ws : List Decor}
    (gp : goodPairs T pos neg) (hf : ∀ x ∈ ws, faithful pos neg x)
    (h : Live T k (ws.map Prod.fst).toFinset) :
    ((coverage ws).1 &&& fullMask pos.length) = fullMask pos.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have hfm : (fullMask pos.length).testBit i = decide (i < pos.length) := by
    simp [fullMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · have ⟨hp, hn⟩ := gp.2 i hi
    have hsep : T.testBit (pos.getD i 0) ≠ T.testBit (neg.getD i 0) := by rw [hp, hn]; decide
    obtain ⟨v, hv, hvd⟩ := live_sep h hsep
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hfx := hf x hx
    have hpi : pos[i]? = some (pos.getD i 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hni : neg[i]? = some (neg.getD i 0) := by
      have hi' : i < neg.length := gp.1 ▸ hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    have hbit : (dsep x).testBit i = true := by
      simp only [dsep, Nat.testBit_xor, hfx.1, hfx.2, testBit_projBits, hpi, hni]
      have h12 : x.1.testBit (pos.getD i 0) ≠ x.1.testBit (neg.getD i 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        exact hvd
      cases h1 : x.1.testBit (pos.getD i 0) <;> cases h2 : x.1.testBit (neg.getD i 0)
      · exact absurd (h1.trans h2.symm) h12
      · rfl
      · rfl
      · exact absurd (h1.trans h2.symm) h12
    have hc := (cov_testBit ws i).mpr ⟨x, hx, hbit⟩
    simp [hfm, hi, hc]
  · simp [hfm, hi]
def insertNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs
def sortNats : List Nat → List Nat
  | [] => []
  | a :: bs => insertNat a (sortNats bs)
lemma insertNat_perm (a : Nat) (l : List Nat) : (insertNat a l).Perm (a :: l) := by
  induction l with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp [insertNat, h]
    · exact by simpa [insertNat, h] using (List.Perm.cons b ih).trans (.swap a b bs)
lemma sortNats_perm (l : List Nat) : (sortNats l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertNat_perm a (sortNats bs)).trans (.cons a ih)
lemma sortNats_toFinset (l : List Nat) : (sortNats l).toFinset = l.toFinset := by
  ext x; simpa only [List.mem_toFinset] using (sortNats_perm l).mem_iff
def childTwo (ws : List Nat) (a b d : Nat) (ka kb : Bool) : List Nat :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma erase_toFinset {l : List Nat} (nd : l.Nodup) (a : Nat) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [nd.mem_erase_iff]
lemma enum_step {T cap : Nat} {ws : List Nat} (nd : ws.Nodup) (out : T ∉ ws)
    (stepOK : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb : Bool,
      a ≠ b → bin d a b ≠ 0 → bin d a b ∉ ws → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  cases k with
  | zero =>
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  | succ k =>
    obtain ⟨U, a, b, d, hd, he, _, _, hab, hf, tail⟩ := h
    have am : a ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_self a _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    have fresh : bin d a b ∉ ws := fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hnz : bin d a b ≠ 0 := live_nonzero tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b from rfl, erase_toFinset (nd.erase _) b, erase_toFinset nd a]
    have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
      cases c <;> simp [kept]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kf, kf, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (nd.erase _).erase _
    have ar : a ∉ rest := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (nd.erase a).not_mem_erase
    have nk := kept_nodup kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have ndc : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr hm))),
        kept_nodup ka a _ nk ax⟩
    have eqc : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := live_size tail
    have hlen : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup ndc, eqc]; omega
    exact stepOK a am b bm d hd ka kb hab hnz fresh hlen k (by omega) (eqc.symm ▸ tail)
lemma delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k; exact List.erase_sublist; exact List.Sublist.refl _
lemma delTwo_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) : (delTwo ws a b ka kb).Sublist ws :=
  (delOne_sub _ _ _).trans (delOne_sub _ _ _)
lemma delTwo_len (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
  cases ka <;> cases kb <;> simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
lemma unique_fst {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hn (eq ▸ List.mem_map_of_mem hb')).elim
    · exact (hn (eq.symm ▸ List.mem_map_of_mem ha')).elim
    · exact ih ht ha' hb'
lemma delTwo_map_toFinset {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  have wn : ws.Nodup := nd.of_map
  have dn : (delOne ws a ka).Nodup := wn.sublist (delOne_sub ws a ka)
  have m1 (l : List Decor) (hl : l.Nodup) (x y : Decor) (c : Bool) :
      y ∈ delOne l x c ↔ y ∈ l ∧ (y ≠ x ∨ c = true) := by
    cases c <;> simp [delOne, hl.mem_erase_iff, and_comm]
  have km (v : Nat) : v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
    simp only [delTwo, List.mem_map, m1 _ wn, m1 _ dn]
    constructor
    · rintro ⟨w, ⟨⟨hw, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, h1.imp (fun h e => h (unique_fst nd hw ha e)) id,
        h2.imp (fun h e => h (unique_fst nd hw hb e)) id⟩
    · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hw, h1.imp (fun h e => h (congrArg Prod.fst e)) id⟩,
        h2.imp (fun h e => h (congrArg Prod.fst e)) id⟩, rfl⟩
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (v : Nat) : v ∈ kept c x l ↔ (v = x ∧ c = true) ∨ v ∈ l := by
    cases c <;> simp [kept]
  ext v
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, km, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all
lemma childTwo_swap (v : List Nat) (nd : v.Nodup) (a b : Nat) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (y : Nat) : y ∈ kept c x l ↔ (y = x ∧ c = true) ∨ y ∈ l := by
    cases c <;> simp [kept]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm_flip d hd a b]
  tauto
def varsOf (m : Nat) : List Nat :=
  (List.range 7).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    let fr := ((r &&& (127 ^^^ z)) ||| o) % 128
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 128
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 128 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127 : ((r.val &&& (127 ^^^ z)) ||| o) < 128 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (127 ^^^ z)) < 128 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 7) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (127 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 7
    · have h7 : (127 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 128) && decide (s < 128) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL128 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL128]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 128 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^128) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^128 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^128) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^128 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def carryOK (swaps : List (Nat × Nat)) (roots1 : List Nat) (T1 : Nat) (roots2 : List Nat) (T2 : Nat) : Bool :=
  swapsValid swaps && checkProper T1 && checkRoots roots1 && checkProper T2 &&
    (permWord swaps T1 == T2) && roots1.all (fun a => freeIn roots2 (permWord swaps a))
lemma carry_of {swaps roots1 T1 roots2 T2 L} (ok : carryOK swaps roots1 T1 roots2 T2 = true)
    (hL : Lower roots2 T2 L) : Lower roots1 T1 L := by
  simp only [carryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hsv, hT1⟩, hR1⟩, hT2⟩, heq⟩, hcov⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT1
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hT2
  have hR1' := checkRoots_sound hR1
  have heq' : renameW (permRow swaps) T1 = T2 := (permWord_eq_renameW swaps hsv T1 p1b).symm.trans heq
  have hcov' : ∀ a ∈ roots1, Avail (roots2.map obs) (restrictW (permRow swaps) (obs a)) := fun a ha =>
    freeIn_sound (permWord_eq_renameW swaps hsv a (hR1' a ha).1 ▸ hcov a ha)
  simpa using lower_slice p1a p1b p1c hR1' p2a p2b p2c (permRow swaps) heq' hcov' ∅ (by simp) (by simp) L hL
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL128))
lemma lift_of {z o roots T other G essPairs L} (ok : liftCheck z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G := (fixWord_eq_renameW z o T).symm.trans heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL128]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 128 r'.val |> fun e => by simpa [this] using e⟩
def goodPairsCheck (T : Nat) (pos neg : List Nat) : Bool :=
  (pos.length == neg.length) &&
    (List.range pos.length).all fun i => T.testBit (pos.getD i 0) && !(T.testBit (neg.getD i 0))
lemma goodPairs_of {T pos neg} (ok : goodPairsCheck T pos neg = true) : goodPairs T pos neg := by
  simp only [goodPairsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at ok
  exact ok
def autosCheck (T : Nat) (autos : List (List (Nat × Nat))) : Bool :=
  autos.all fun sw => swapsValid sw && (permWord sw T == T)
lemma autos_of {T autos} (ok : autosCheck T autos = true) :
    ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T := by
  simp only [autosCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok
def baseCheck (pos neg : List Nat) (base : List Decor) : Bool :=
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^128)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := by
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  intro x hx
  have h := ok x hx
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
def forestRootCheck (roots : List Nat) (T : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    roots.all fun a => essPairs.any fun e => (e.1 == a) && checkEss1 T roots e.1 e.2.1 e.2.2
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat

def nodesWithIdentity (entries : List (List Nat × List Nat)) : List NodeSpec :=
  entries.map (fun entry => (entry.1, entry.2, [0]))

lemma var_testBit (i : Fin 7) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
def sliceDirectCheck (z o zDead : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    decide (zDead < 128) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead : Nat) (hz : z < 128) (hd : zDead < 128) (ho : o < 128)
    (hzo : ((z ||| zDead) &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true := by
  have hsub := subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n := 7) hz hd) ho hzo r
  unfold subcube at hsub ⊢
  rw [testBit_foldr_bits] at hsub ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsub ⊢
  refine ⟨hsub.1, ?_, hsub.2.2⟩
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun x => x.testBit i) hsub.2.1
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  cases hfa : (fixRow (z ||| zDead) o r).val.testBit i <;> cases hzb : z.testBit i <;> simp_all
lemma slice_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) qL := by
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, ho⟩, _hzo0⟩, hd⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  refine ⟨fixRow (z ||| zDead) o, qRoots, subcube_fixRow_sup z o zDead hz hd ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW (z ||| zDead) o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW, heq]
  exact hPrior
def evalInput6 (r : Row) : Fin 6 → Bool := fun i => r.val.testBit i.val
def packInput6 (x : Fin 6 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    omega⟩
lemma evalInput6_packInput6 (x : Fin 6 → Bool) : evalInput6 (packInput6 x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (j : Fin 6),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
  fin_cases i <;> simpa [evalInput6, packInput6] using hi
lemma sum_eq_packInput6 (x : Fin 6 → Bool) :
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = (packInput6 x).val := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two, packInput6]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide
lemma testBit_rep64 (T6 : Nat) (hT6 : T6 < 2^64) (r : Row) :
    (T6 ||| (T6 <<< 64)).testBit r.val = T6.testBit (r.val % 64) := by
  have hr := r.isLt
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h64 : r.val < 64
  · have hn : ¬(64 ≤ r.val) := by omega
    rw [Nat.mod_eq_of_lt h64]
    simp [hn]
  · have hge : 64 ≤ r.val := by omega
    have hmod : r.val % 64 = r.val - 64 := by omega
    rw [hmod]
    have hhi : T6.testBit r.val = false → (T6.testBit r.val || (decide (64 ≤ r.val) && T6.testBit (r.val - 64))) = T6.testBit (r.val - 64) := by
      intro hf; simp [hf, hge]
    have hf : T6.testBit r.val = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hT6 (Nat.pow_le_pow_right (by decide : 0 < 2) hge))
    exact hhi hf
lemma sw_extract_full_6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^128 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput6 r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi6 : i < 6 := by simpa using hi2
      have hv : (varsOf 63)[i]? = some (VAR i) := by interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput6, swRead, Bool.false_bne]
      have hget : (varsOf 63)[i]'(by simpa [seeds] using hi1) = VAR i := (List.getElem?_eq_some_iff.mp hv).2
      rw [hget]
      exact var_testBit ⟨i, by omega⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · have h := hev ⟨r, hr⟩; simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]; exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma table2_of_lower (T6 : Nat) (hT6lt : T6 < 2^64)
    (hT0 : (T6 ||| (T6 <<< 64)) ≠ 0) (hTlt : (T6 ||| (T6 <<< 64)) < 2^128) (hTb0 : (T6 ||| (T6 <<< 64)).testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 63) (T6 ||| (T6 <<< 64)) L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = (T6 ||| (T6 <<< 64)).testBit r.val)
    (s : ℕ)
    (hcs : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  let T := T6 ||| (T6 <<< 64)
  obtain ⟨C, hfan, hsize, heval⟩ := hcs
  have hlegal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have ⟨hm, hl⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    exact ⟨hm, hl⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · have hlt : C.gates.countP isBin < C.gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    have heR : ∀ r : Row, Circuit.eval ⟨C.gates, C.output⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val := by
      intro r
      have h1 := heval (evalInput6 r)
      have hsum : (∑ i : Fin 6, if evalInput6 r i then 2 ^ (i : ℕ) else 0) = r.val % 64 := by
        rw [sum_eq_packInput6]
        have h : ∀ j : Row, (packInput6 (evalInput6 j)).val = j.val % 64 := by decide +kernel
        exact h r
      dsimp only at h1
      rw [hsum] at h1
      exact h1.trans (testBit_rep64 T6 hT6lt r).symm
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full_6 T hT0 hTlt hTb0 C.gates C.output hlegal heR
    have hrun := live_to_run hlive S.toList (Finset.nodup_toList S) (by simp)
    have hsup : Supply ((varsOf 63).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 63).map obs)
        (show Reach ((varsOf 63).map obs) 0 ((varsOf 63).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    have hwEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
      intro x
      rw [← evalInput6_packInput6 x, hwEvalR (packInput6 x), testBit_rep64 T6 hT6lt (packInput6 x)]
      rw [evalInput6_packInput6 x, sum_eq_packInput6 x]
      have hlt64 : (packInput6 x).val < 64 := by
        have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
        have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
        simp only [packInput6]; omega
      rw [Nat.mod_eq_of_lt hlt64]
    have hcsz : C.size = C.gates.length := rfl
    refine ⟨⟨wit, wo⟩, hwMono, ?_, hwEval⟩
    change wit.length ≤ s
    omega
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    have ⟨hm, hl⟩ := hlegal g hg
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
inductive BT (α : Type) where
  | empty : BT α
  | leaf : α → BT α
  | node : BT α → BT α → BT α
def btGet {α : Type} (d : α) : BT α → Nat → α
  | .empty, _ => d
  | .leaf x, _ => x
  | .node l r, i => if i &&& 1 == 0 then btGet d l (i >>> 1) else btGet d r (i >>> 1)
def btSet {α : Type} : Nat → BT α → Nat → α → BT α
  | 0, _, _, v => .leaf v
  | d + 1, .empty, i, v =>
    if i &&& 1 == 0 then .node (btSet d .empty (i >>> 1) v) .empty
    else .node .empty (btSet d .empty (i >>> 1) v)
  | d + 1, .leaf x, i, v =>
    if i &&& 1 == 0 then .node (btSet d (.leaf x) (i >>> 1) v) .empty
    else .node .empty (btSet d (.leaf x) (i >>> 1) v)
  | d + 1, .node l r, i, v =>
    if i &&& 1 == 0 then .node (btSet d l (i >>> 1) v) r
    else .node l (btSet d r (i >>> 1) v)
def btUpdate {α : Type} (d0 : α) : Nat → BT α → Nat → (α → α) → BT α
  | 0, .leaf x, _, f => .leaf (f x)
  | 0, _, _, f => .leaf (f d0)
  | d + 1, .empty, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d .empty (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d .empty (i >>> 1) f)
  | d + 1, .leaf x, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d (.leaf x) (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d (.leaf x) (i >>> 1) f)
  | d + 1, .node l r, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d l (i >>> 1) f) r
    else .node l (btUpdate d0 d r (i >>> 1) f)
def btAll {α : Type} (P : α → Prop) : BT α → Prop
  | .empty => True
  | .leaf x => P x
  | .node l r => btAll P l ∧ btAll P r
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction t generalizing i with
  | empty => exact hd
  | leaf x => exact ht
  | node l r ihl ihr =>
    unfold btGet
    split
    · exact ihl ht.1 _
    · exact ihr ht.2 _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact hv
  | succ d ih =>
    cases t with
    | empty =>
      unfold btSet; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btSet; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btSet; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases t with
    | leaf x => exact hf x ht
    | empty => exact hf d0 hd0
    | node _ _ => exact hf d0 hd0
  | succ d ih =>
    cases t with
    | empty =>
      unfold btUpdate; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btUpdate; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btUpdate; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
def btOfList {α : Type} (depth : Nat) (l : List α) : BT α :=
  (l.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) (0, BT.empty)).2
lemma btAll_ofList {α : Type} {P : α → Prop} {depth : Nat} {l : List α}
    (h : ∀ x ∈ l, P x) : btAll P (btOfList depth l) := by
  unfold btOfList
  have hgo : ∀ (xs : List α) (acc : Nat × BT α),
      (∀ x ∈ xs, P x) → btAll P acc.2 →
      btAll P (xs.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) acc).2 := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; exact hacc
    | cons x xs ih =>
      intro acc hx hacc
      exact ih (acc.1 + 1, btSet depth acc.2 acc.1 x)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (btAll_set hacc (hx x (List.mem_cons_self ..)))
  exact hgo l (0, BT.empty) h trivial
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL128 ^^^ VAR i else if o.testBit i then VAR i else ALL128
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 7) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL128.testBit r.val = true := by
    simp only [ALL128]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 128 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · have hsub : (subcube z o).testBit r = ((r &&& z == 0) && (r &&& o == o)) := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and,
      fastBitMask_testBit z o 0 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 1 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 2 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 3 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 4 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 7) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 7, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 7
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 7
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 128 ≤ r := by omega
      have ha : ALL128 < 2^128 := by decide
      have hv : VAR i < 2^128 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^128; decide
      have hlt_m : fastBitMask z o i < 2^128 := by
        unfold fastBitMask; split
        · exact Nat.xor_lt_two_pow ha hv
        · split; exact hv; exact ha
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by decide : 0 < 2) hle))
    have hsub : (subcube z o).testBit r = false := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and, hlt_f]
    rfl
lemma slice_fast_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  have ok2 := ok
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1.1.1 ok2.1.1.1.1.1.1.1.2 ok2.1.1.1.1.1.1.2]
  exact slice_direct ok hPrior
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) &&& 63
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (ws.map (permWord sw)))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContainsBT at hhit
    have hmem := List.contains_iff_mem.mp hhit
    have hb : ∀ xs ∈ btGet [] prevBks (hashWs64 (sortNats ((choiceVal op :: rest).map (permWord sw)))),
        Impossible T k xs.toFinset :=
      btAll_get hPrev (fun _ hx => (List.not_mem_nil hx).elim) _
    have himp := hb _ hmem
    rw [sortNats_toFinset] at himp
    have ⟨hsv, hfix⟩ := hAutos sw hsw
    have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
    have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
        ∀ r : Row, permRow l.reverse (permRow l r) = r := by
      intro l hl
      induction l with
      | nil => intro r; rfl
      | cons p ps ih =>
        simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
        intro r
        have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
            swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
          simp [permRow, List.reverse_cons, List.foldl_append]
        rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
    have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
      simpa using hinv_row_gen sw.reverse hvr
    have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 128
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rw [permWord_eq_renameW sw hsv x (hlt x hx)]
      exact renameW_lt _ x
    have hrot := rotate_impossible himp sw.reverse hvr hT hfixr hmap_lt
    have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
      exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
    rwa [hback] at hrot
abbrev FastPool := BoundPool × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else some (c, miss, vals.countP (isConstM c.dom))
def fastPoolCut (fp : FastPool) (k : Nat) (a b d : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let totC := fp.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && isConstM c.dom a then 1 else 0
    let dropB := if !kb && isConstM c.dom b then 1 else 0
    let z := bin d a b
    let cRest := totC - dropA - dropB + (if isConstM c.dom z then 1 else 0)
    let zIn := availM c.dom c.pm z
    let extra := if zIn then 0 else 1
    decide (k + c.paid + extra < c.lb + cRest) && (zIn || choiceOK c.dom c.pm (d, a, b))
lemma countP_erase {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {x : α} (hx : x ∈ l) :
    (l.erase x).countP p + (if p x then 1 else 0) = l.countP p := by
  have hp := List.perm_cons_erase hx
  have h1 := List.Perm.countP_eq p hp
  simp only [List.countP_cons] at h1
  omega
lemma countP_delTwo_fst (p : Nat → Bool) {ws : List Decor} {a b : Decor}
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map Prod.fst).countP p =
      (ws.map Prod.fst).countP p - (if !ka && p a.1 then 1 else 0) - (if !kb && p b.1 then 1 else 0) := by
  have hne : a ≠ b := fun e => hab (congrArg Prod.fst e)
  have hmap_erase : ∀ (l : List Decor) (x : Decor), (l.map Prod.fst).Nodup → x ∈ l →
      (l.erase x).map Prod.fst = (l.map Prod.fst).erase x.1 := by
    intro l x hnd hx
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne1 : y.1 ≠ x.1 := by
          intro eq; apply hnd.1; rw [eq]
          exact List.mem_map_of_mem ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))
        have h1 : (y == x) = false := beq_false_of_ne hyx
        have h2 : (y.1 == x.1) = false := beq_false_of_ne hne1
        simp only [List.erase_cons, h1, h2, List.map_cons]
        exact congrArg (y.1 :: ·) (ih hnd.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx)))
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne hne.symm).mpr hb
    have hnd1 : ((ws.erase a).map Prod.fst).Nodup := ((List.erase_sublist).map Prod.fst).nodup nd
    change (((ws.erase a).erase b).map Prod.fst).countP p = _
    rw [hmap_erase _ b hnd1 hbm, hmap_erase ws a nd ha]
    have ha1 : a.1 ∈ ws.map Prod.fst := List.mem_map_of_mem ha
    have hb1 : b.1 ∈ (ws.map Prod.fst).erase a.1 := (List.mem_erase_of_ne hab.symm).mpr (List.mem_map_of_mem hb)
    have c1 := countP_erase p ha1
    have c2 := countP_erase p hb1
    cases hpa : p a.1 <;> cases hpb : p b.1 <;> simp [hpa, hpb] at c1 c2 ⊢ <;> omega
  · change ((ws.erase a).map Prod.fst).countP p = _
    rw [hmap_erase ws a nd ha]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) ha)
    cases hpa : p a.1 <;> simp [hpa] at c1 ⊢ <;> omega
  · change ((ws.erase b).map Prod.fst).countP p = _
    rw [hmap_erase ws b nd hb]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) hb)
    cases hpb : p b.1 <;> simp [hpb] at c1 ⊢ <;> omega
  · simp [delTwo, delOne]
lemma fastPoolCut_sound {raw T ws a b d ka kb k c fp}
    (hP : ValidPool raw T c) (hprep : prepPool (ws.map Prod.fst) c = some fp)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 d ka kb = true) :
    Impossible T k (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  unfold prepPool at hprep
  dsimp only at hprep
  split at hprep
  · simp at hprep
  · simp only [Option.some.injEq] at hprep
    subst hprep
    unfold fastPoolCut at hcut
    dsimp only at hcut
    split at hcut
    · simp at hcut
    · next hmiss =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_filter, Bool.not_eq_true'] at hmiss
      have hsub := (delTwo_sub ws a b ka kb).map Prod.fst
      have h_all_avail : ((delTwo ws a b ka kb).map Prod.fst).all (availM c.dom c.pm) = true := by
        rw [List.all_eq_true]; intro w hw
        by_contra hna
        have hnf : availM c.dom c.pm w = false := Bool.eq_false_iff.mpr hna
        have hmem_ws : w ∈ ws.map Prod.fst := hsub.subset hw
        have hm := hmiss w ⟨hmem_ws, hnf⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
        have hne_ab : a ≠ b := fun e => hab (congrArg Prod.fst e)
        have hnot_in : ∀ (x : Decor) (kx : Bool), kx = false → x ∈ ws → x.1 ∉ (delTwo ws a b ka kb).map Prod.fst → True := fun _ _ _ _ _ => trivial
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            exact List.Nodup.not_mem_erase hnd_ws hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · have hu_eq : u = a := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa)
          exact hna' hka hu_eq
        · have hu_eq : u = b := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb)
          exact hnb' hkb hu_eq
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut
      simp only [choiceVal, h_all_avail, Bool.true_and, Bool.and_true, List.countP_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hcut ⊢
      rw [hcnt]
      rcases hcut with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          cases hcz : isConstM c.dom (bin d a.1 b.1) <;>
          simp only [hz, hcz, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
            Bool.and_eq_true, Bool.false_eq_true, ite_true, ite_false] at h1 ⊢ <;> omega
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          simp only [hz, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or] at h2 ⊢ <;>
          exact h2
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
  go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^128) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hfr_b : (ws.any (fun v => v.1 == z.1)) = false := by
    rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
    have hvz : v.1 = bin d a.1 b.1 := beq_iff_eq.mp heq
    exact hfr (hvz ▸ List.mem_map_of_mem hv)
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    have hdl := delTwo_len ws a b ka kb ha hb ne
    simp only [child, rest, List.length_map, List.length_cons]
    omega
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMoveBT at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAllBT, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma nodeBT_sound {raw T pos neg ws fpools autos prevBks cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (checks : cap = 0 ∨ testAllBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0
    intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPairBT, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMoveBT_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAllBT_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
def buildWiresBT (depth : Nat) (base : List Decor) (steps : List (Nat × Nat × Nat)) : BT Decor :=
  let init := (base.length, btOfList depth base)
  (steps.foldl (fun p s =>
    let a := btGet (0, 0, 0) p.2 s.2.1
    let b := btGet (0, 0, 0) p.2 s.2.2
    (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 a b))) init).2
lemma buildWiresBT_faithful {depth pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128)
        (ss.foldl (fun p s => (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 (btGet (0, 0, 0) p.2 s.2.1) (btGet (0, 0, 0) p.2 s.2.2)))) acc).2 := by
    intro ss
    induction ss with
    | nil => intro acc hacc; exact hacc
    | cons s ss ih =>
      intro acc hacc
      have ha := btAll_get hacc hdef s.2.1
      have hb := btAll_get hacc hdef s.2.2
      exact ih _ (btAll_set hacc ⟨faithful_bin s.1 ha.1 hb.1, bin_lt s.1 _ _ ha.2 hb.2⟩)
  exact hgo steps (base.length, btOfList depth base) h0
def buildPoolsBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : List PoolSpec) : BT (Option BoundPool) :=
  btOfList pdepth (pspecs.map fun (slIdx, chIdxs) =>
    match btGet none slices slIdx with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
      materialize raw cs dom lb)
lemma buildPoolsBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))} {pspecs : List PoolSpec}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsBT pdepth W raw slices pspecs) := by
  apply btAll_ofList
  intro o ho c hc
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp ho
  dsimp only at hmat
  have hsl := btAll_get (d := none) hSlices (fun _ h => by simp at h) slIdx
  cases heq : btGet none slices slIdx with
  | none => rw [heq] at hmat; exact absurd (hmat.trans hc) (by simp)
  | some sl =>
    rw [heq] at hmat
    exact materialize_sound (hsl sl heq) (hmat.trans hc)
def checkNodeBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals := ws.map Prod.fst
  let fpools := ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos := ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^128 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun fp hfp => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hfp
      cases heq : btGet none poolTable pIdx with
      | none => simp [heq] at hmat
      | some c =>
        simp only [heq] at hmat
        have hvc := btAll_get hPoolTable (fun _ h => by simp at h) pIdx c heq
        have hfp_eq : fp.1 = c := by
          unfold prepPool at hmat
          dsimp only at hmat
          split at hmat
          · simp at hmat
          · simp only [Option.some.injEq] at hmat; rw [← hmat]
        rw [hfp_eq]
        exact ⟨hvc, hmat⟩)
    (fun sw hsw => by
      obtain ⟨aIdx, _, rfl⟩ := List.mem_map.mp hsw
      exact btAll_get hAutos ⟨rfl, rfl⟩ aIdx)
    hPrev ok.2
def nodeValsBT (W : BT Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (btGet (0, 0, 0) W idx).1)
def buildBucketsBT (W : BT Decor) (nodes : List NodeSpec) : BT (List (List Nat)) :=
  nodes.foldl (fun acc ns =>
    let xs := nodeValsBT W ns
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := fun ns hns => by
    unfold nodeValsBT; rw [sortNats_toFinset]
    exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
lemma lower_of_forestBT {roots T cap} {topBks : BT (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : btAll (fun bk => ∀ xs ∈ bk, Impossible T cap xs.toFinset) topBks)
    (hRoot : bucketContainsBT topBks roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContainsBT at hRoot
    exact btAll_get hTop (fun _ h => (List.not_mem_nil h).elim) _ _ (List.contains_iff_mem.mp hRoot)
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def h1R : List Nat := varsOf 29
def h1G : Nat := 0xfafaf000fafaf000fafaf000fafaf000
def h1Pos : List Nat := [12,13,12,13,20,17,20,25]
def h1Neg : List Nat := [8,9,4,5,4,1,16,9]
def h1Mask : Nat := fullMask 8
def h1Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,170,170),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,95,28),(0xff00ff00ff00ff00ff00ff00ff00ff00,143,131),(0xffff0000ffff0000ffff0000ffff0000,240,64)]
def h1Steps : List (Nat × Nat × Nat) := []
def h1W : BT Decor := buildWiresBT 2 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[],[(2,4),(0,3)]]
def h1Autos : BT (List (Nat × Nat)) := btOfList 1 h1AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Pairs : goodPairs h1G h1Pos h1Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1BaseOk : ∀ x ∈ h1Base, faithful h1Pos h1Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1WOk : btAll (fun x => faithful h1Pos h1Neg x ∧ x.1 < 2^128) h1W := buildWiresBT_faithful h1BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h1G = h1G) h1Autos := btAll_ofList (autos_of (by decide +kernel))
def h1SliceList : List (Option (Nat × Nat)) := []
def h1Slices : BT (Option (Nat × Nat)) := btOfList 1 h1SliceList
def h1Specs : List PoolSpec := []
def h1Pools : BT (Option BoundPool) := buildPoolsBT 1 h1W h1R h1Slices h1Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h1R h1G p.1 p.2) h1Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h1R h1G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h1R h1G c) h1Pools := buildPoolsBT_sound h1SlicesOk
def h1Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G (3 - 1) xs.toFinset) h1Empty := trivial
def h1Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test3_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 3 h1Block3_0 = true := by decide +kernel
def h1Nodes3 : List NodeSpec := h1Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check3 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 3 h1Nodes3 = true := h1Test3_0
def h1Bucket3 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 3 xs.toFinset) h1Bucket3 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1EmptyOk h1Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bound : Lower h1R h1G 4 := lower_of_forestBT (essPairs := [(VAR 0,16,17),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,1,17)]) (by decide +kernel) h1Bucket3Ok (by decide +kernel)
def h2R : List Nat := varsOf 30
def h2G : Nat := 0xffccf000ffccf000ffccf000ffccf000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 4 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h4R : List Nat := varsOf 15
def h4G : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 4 := carry_of (swaps := [(1,2),(2,3),(3,4),(2,3),(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h5R : List Nat := varsOf 23
def h5G : Nat := 0xeaeae0e0eaeae0e0eaeae0e0eaeae0e0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 4 := carry_of (swaps := [(3,4),(1,2),(2,3),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h6R : List Nat := varsOf 27
def h6G : Nat := 0xeeccee00eeccee00eeccee00eeccee00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 4 := carry_of (swaps := [(3,4),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h3R : List Nat := varsOf 31
def h3G : Nat := 0xeac8e000eac8e000eac8e000eac8e000
def h3Pos : List Nat := [13,14,22,14,13,14,13,19,22,19,22,19,22,15,25,15,14,25]
def h3Neg : List Nat := [12,12,21,10,9,6,5,3,6,18,20,17,18,11,9,7,7,17]
def h3Mask : Nat := fullMask 18
def h3Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x2ead1,0x3e8d4),(0xcccccccccccccccccccccccccccccccc,0x1bfae,0x1b3a8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1b57f,0x18567),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3e07b,0x601b),(0xffff0000ffff0000ffff0000ffff0000,0x25f84,0x21e04)]
def h3Steps : List (Nat × Nat × Nat) := [(0,0,1),(0,0,3),(2,1,6)]
def h3W : BT Decor := buildWiresBT 3 h3Base h3Steps
def h3AutoList : List (List (Nat × Nat)) := [[],[(3,4),(1,2)],[(2,3),(0,1)],[(1,4),(0,2)],[(2,4),(0,3)],[(1,3),(0,4)],[(3,4),(2,3),(1,3),(0,1)],[(3,4),(2,4),(1,2),(0,2)],[(3,4),(2,4),(1,4),(0,3)],[(3,4),(2,3),(1,2),(0,4)]]
def h3Autos : BT (List (Nat × Nat)) := btOfList 4 h3AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Pairs : goodPairs h3G h3Pos h3Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3BaseOk : ∀ x ∈ h3Base, faithful h3Pos h3Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3WOk : btAll (fun x => faithful h3Pos h3Neg x ∧ x.1 < 2^128) h3W := buildWiresBT_faithful h3BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h3G = h3G) h3Autos := btAll_ofList (autos_of (by decide +kernel))
def h3SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4),some (subcubeFast 0 16,4)]
def h3Slices : BT (Option (Nat × Nat)) := btOfList 3 h3SliceList
def h3Specs : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def h3Pools : BT (Option BoundPool) := buildPoolsBT 3 h3W h3R h3Slices h3Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice4 : Slice h3R h3G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice3 : Slice h3R h3G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice2 : Slice h3R h3G (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice1 : Slice h3R h3G (subcubeFast 0 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice0 : Slice h3R h3G (subcubeFast 0 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h3R h3G p.1 p.2) h3Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h3R h3G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h3Slice0) (forall_cons (fun _ h => by cases h; exact h3Slice1) (forall_cons (fun _ h => by cases h; exact h3Slice2) (forall_cons (fun _ h => by cases h; exact h3Slice3) (forall_cons (fun _ h => by cases h; exact h3Slice4) (fun _ h => (List.not_mem_nil h).elim))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h3R h3G c) h3Pools := buildPoolsBT_sound h3SlicesOk
def h3Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G (4 - 1) xs.toFinset) h3Empty := trivial
def h3Block4_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,7],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test4_0 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 4 h3Block4_0 = true := by decide +kernel
def h3Nodes4 : List NodeSpec := h3Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Check4 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 4 h3Nodes4 = true := h3Test4_0
def h3Bucket4 : BT (List (List Nat)) := buildBucketsBT h3W h3Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G 4 xs.toFinset) h3Bucket4 := buildBucketsBT_sound (by decide) h3Pairs h3WOk h3PoolsOk h3AutosOk h3EmptyOk h3Check4
def h3Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[]),([0,1,2,3,4,6],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test5_0 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket4 5 h3Block5_0 = true := by decide +kernel
def h3Nodes5 : List NodeSpec := h3Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Check5 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket4 5 h3Nodes5 = true := h3Test5_0
def h3Bucket5 : BT (List (List Nat)) := buildBucketsBT h3W h3Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G 5 xs.toFinset) h3Bucket5 := buildBucketsBT_sound (by decide) h3Pairs h3WOk h3PoolsOk h3AutosOk h3Bucket4Ok h3Check5
def h3Block6_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test6_0 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket5 6 h3Block6_0 = true := by decide +kernel
def h3Nodes6 : List NodeSpec := h3Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Check6 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket5 6 h3Nodes6 = true := h3Test6_0
def h3Bucket6 : BT (List (List Nat)) := buildBucketsBT h3W h3Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G 6 xs.toFinset) h3Bucket6 := buildBucketsBT_sound (by decide) h3Pairs h3WOk h3PoolsOk h3AutosOk h3Bucket5Ok h3Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 7 := lower_of_forestBT (essPairs := [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19)]) (by decide +kernel) h3Bucket6Ok (by decide +kernel)
def h7R : List Nat := varsOf 39
def h7G : Nat := 0xeaeaeaeae0e0e0e0eaeaeaeae0e0e0e0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 4 := carry_of (swaps := [(3,4),(4,5),(1,2),(2,3),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h8R : List Nat := varsOf 46
def h8G : Nat := 0xffccffccf000f000ffccffccf000f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 4 := carry_of (swaps := [(4,5),(2,3),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h9R : List Nat := varsOf 47
def h9G : Nat := 0xeac8eac8e000e000eac8eac8e000e000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 7 := carry_of (swaps := [(4,5)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h10R : List Nat := varsOf 50
def h10G : Nat := 0xffffcccccccc0000ffffcccccccc0000
def h10Pos : List Nat := [34,48,18,18,48,34]
def h10Neg : List Nat := [32,32,2,16,16,2]
def h10Mask : Nat := fullMask 6
def h10Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xffff0000ffff0000ffff0000ffff0000,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h10Steps : List (Nat × Nat × Nat) := []
def h10W : BT Decor := buildWiresBT 2 h10Base h10Steps
def h10AutoList : List (List (Nat × Nat)) := [[],[(4,5)],[(1,4)],[(1,5)],[(4,5),(1,4)],[(4,5),(1,5)]]
def h10Autos : BT (List (Nat × Nat)) := btOfList 3 h10AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Pairs : goodPairs h10G h10Pos h10Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10BaseOk : ∀ x ∈ h10Base, faithful h10Pos h10Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10WOk : btAll (fun x => faithful h10Pos h10Neg x ∧ x.1 < 2^128) h10W := buildWiresBT_faithful h10BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h10G = h10G) h10Autos := btAll_ofList (autos_of (by decide +kernel))
def h10SliceList : List (Option (Nat × Nat)) := []
def h10Slices : BT (Option (Nat × Nat)) := btOfList 1 h10SliceList
def h10Specs : List PoolSpec := []
def h10Pools : BT (Option BoundPool) := buildPoolsBT 1 h10W h10R h10Slices h10Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h10R h10G p.1 p.2) h10Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h10R h10G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h10R h10G c) h10Pools := buildPoolsBT_sound h10SlicesOk
def h10Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h10G (3 - 1) xs.toFinset) h10Empty := trivial
def h10Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Test3_0 : checkNodesBT h10W h10G h10Mask h10Pools h10Autos h10Empty 3 h10Block3_0 = true := by decide +kernel
def h10Nodes3 : List NodeSpec := h10Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Check3 : checkNodesBT h10W h10G h10Mask h10Pools h10Autos h10Empty 3 h10Nodes3 = true := h10Test3_0
def h10Bucket3 : BT (List (List Nat)) := buildBucketsBT h10W h10Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h10G 3 xs.toFinset) h10Bucket3 := buildBucketsBT_sound (by decide) h10Pairs h10WOk h10PoolsOk h10AutosOk h10EmptyOk h10Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 4 := lower_of_forestBT (essPairs := [(VAR 1,16,18),(VAR 4,2,18),(VAR 5,2,34)]) (by decide +kernel) h10Bucket3Ok (by decide +kernel)
def h11R : List Nat := varsOf 51
def h11G : Nat := 0xaaaa888888880000aaaa888888880000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,18,19)]) (by decide +kernel) h10Bound
def h12R : List Nat := varsOf 23
def h12G : Nat := 0xeaeac8c8eaeac8c8eaeac8c8eaeac8c8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 4 := carry_of (swaps := [(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h13R : List Nat := varsOf 51
def h13G : Nat := 0xeeeecccccccc0000eeeecccccccc0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,48,49)]) (by decide +kernel) h10Bound
def h15R : List Nat := varsOf 39
def h15G : Nat := 0xeaeaeaeac8c8c8c8eaeaeaeac8c8c8c8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 4 := carry_of (swaps := [(3,4),(4,5),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h14R : List Nat := varsOf 55
def h14G : Nat := 0xeaeac8c8c8c80000eaeac8c8c8c80000
def h14Pos : List Nat := [22,49,19,19,22,53,22,35,19,38,35,35,49,38,38,49,38,19,54,54]
def h14Neg : List Nat := [20,48,17,18,18,52,6,34,3,6,3,33,33,36,52,17,34,1,52,50]
def h14Mask : Nat := fullMask 20
def h14Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x29dae,0x29d04),(0xcccccccccccccccccccccccccccccccc,0xf6fdd,0x907d8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xd6271,0x46261),(0xffff0000ffff0000ffff0000ffff0000,0xe917f,0xcc03f),(0xffffffff00000000ffffffff00000000,0xdfea2,0xd78a2)]
def h14Steps : List (Nat × Nat × Nat) := [(0,1,3),(3,1,3),(0,3,4),(2,4,5)]
def h14W : BT Decor := buildWiresBT 4 h14Base h14Steps
def h14AutoList : List (List (Nat × Nat)) := [[],[(4,5)]]
def h14Autos : BT (List (Nat × Nat)) := btOfList 1 h14AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Pairs : goodPairs h14G h14Pos h14Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14BaseOk : ∀ x ∈ h14Base, faithful h14Pos h14Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14WOk : btAll (fun x => faithful h14Pos h14Neg x ∧ x.1 < 2^128) h14W := buildWiresBT_faithful h14BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h14G = h14G) h14Autos := btAll_ofList (autos_of (by decide +kernel))
def h14SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,4),some (subcubeFast 0 4,5),some (subcubeFast 0 16,4),some (subcubeFast 0 32,4),some (subcubeFast 4 0,5),some (subcubeFast 4 1,4)]
def h14Slices : BT (Option (Nat × Nat)) := btOfList 3 h14SliceList
def h14Specs : List PoolSpec := [(5,[]),(0,[]),(4,[]),(1,[]),(2,[]),(3,[])]
def h14Pools : BT (Option BoundPool) := buildPoolsBT 3 h14W h14R h14Slices h14Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice5 : Slice h14R h14G (subcubeFast 4 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice4 : Slice h14R h14G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice3 : Slice h14R h14G (subcubeFast 0 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice2 : Slice h14R h14G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice1 : Slice h14R h14G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice0 : Slice h14R h14G (subcubeFast 0 1) 4 := slice_fast_direct (zDead := 4) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h14R h14G p.1 p.2) h14Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h14R h14G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h14Slice0) (forall_cons (fun _ h => by cases h; exact h14Slice1) (forall_cons (fun _ h => by cases h; exact h14Slice2) (forall_cons (fun _ h => by cases h; exact h14Slice3) (forall_cons (fun _ h => by cases h; exact h14Slice4) (forall_cons (fun _ h => by cases h; exact h14Slice5) (fun _ h => (List.not_mem_nil h).elim)))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h14R h14G c) h14Pools := buildPoolsBT_sound h14SlicesOk
def h14Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h14G (4 - 1) xs.toFinset) h14Empty := trivial
def h14Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,8],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Test4_0 : checkNodesBT h14W h14G h14Mask h14Pools h14Autos h14Empty 4 h14Block4_0 = true := by decide +kernel
def h14Nodes4 : List NodeSpec := h14Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Check4 : checkNodesBT h14W h14G h14Mask h14Pools h14Autos h14Empty 4 h14Nodes4 = true := h14Test4_0
def h14Bucket4 : BT (List (List Nat)) := buildBucketsBT h14W h14Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h14G 4 xs.toFinset) h14Bucket4 := buildBucketsBT_sound (by decide) h14Pairs h14WOk h14PoolsOk h14AutosOk h14EmptyOk h14Check4
def h14Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[5]),([0,1,2,3,4,6],[2,3]),([0,1,2,3,4,7],[4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Test5_0 : checkNodesBT h14W h14G h14Mask h14Pools h14Autos h14Bucket4 5 h14Block5_0 = true := by decide +kernel
def h14Nodes5 : List NodeSpec := h14Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Check5 : checkNodesBT h14W h14G h14Mask h14Pools h14Autos h14Bucket4 5 h14Nodes5 = true := h14Test5_0
def h14Bucket5 : BT (List (List Nat)) := buildBucketsBT h14W h14Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h14G 5 xs.toFinset) h14Bucket5 := buildBucketsBT_sound (by decide) h14Pairs h14WOk h14PoolsOk h14AutosOk h14Bucket4Ok h14Check5
def h14Block6_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Test6_0 : checkNodesBT h14W h14G h14Mask h14Pools h14Autos h14Bucket5 6 h14Block6_0 = true := by decide +kernel
def h14Nodes6 : List NodeSpec := h14Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Check6 : checkNodesBT h14W h14G h14Mask h14Pools h14Autos h14Bucket5 6 h14Nodes6 = true := h14Test6_0
def h14Bucket6 : BT (List (List Nat)) := buildBucketsBT h14W h14Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h14G 6 xs.toFinset) h14Bucket6 := buildBucketsBT_sound (by decide) h14Pairs h14WOk h14PoolsOk h14AutosOk h14Bucket5Ok h14Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 7 := lower_of_forestBT (essPairs := [(VAR 0,18,19),(VAR 1,17,19),(VAR 2,18,22),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h14Bucket6Ok (by decide +kernel)
def h16R : List Nat := varsOf 27
def h16G : Nat := 0xeeaaaa88eeaaaa88eeaaaa88eeaaaa88
def h16Pos : List Nat := [9,26,9,17,3,9,26,17,26,3,3,11,11]
def h16Neg : List Nat := [8,24,10,16,2,1,18,1,10,1,0,10,1]
def h16Mask : Nat := fullMask 13
def h16Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7869,4768),(0xcccccccccccccccccccccccccccccccc,8018,2388),(0xff00ff00ff00ff00ff00ff00ff00ff00,6503,2311),(0xffff0000ffff0000ffff0000ffff0000,458,74)]
def h16Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,1,2),(1,1,2),(2,1,2),(1,2,4),(2,2,4),(0,2,5),(3,2,5),(1,3,10),(2,3,10)]
def h16W : BT Decor := buildWiresBT 5 h16Base h16Steps
def h16AutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(1,3)],[(1,4)],[(3,4),(1,3)],[(3,4),(1,4)]]
def h16Autos : BT (List (Nat × Nat)) := btOfList 3 h16AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Pairs : goodPairs h16G h16Pos h16Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16BaseOk : ∀ x ∈ h16Base, faithful h16Pos h16Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16WOk : btAll (fun x => faithful h16Pos h16Neg x ∧ x.1 < 2^128) h16W := buildWiresBT_faithful h16BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h16G = h16G) h16Autos := btAll_ofList (autos_of (by decide +kernel))
def h16SliceList : List (Option (Nat × Nat)) := []
def h16Slices : BT (Option (Nat × Nat)) := btOfList 1 h16SliceList
def h16Specs : List PoolSpec := []
def h16Pools : BT (Option BoundPool) := buildPoolsBT 1 h16W h16R h16Slices h16Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h16R h16G p.1 p.2) h16Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h16R h16G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h16R h16G c) h16Pools := buildPoolsBT_sound h16SlicesOk
def h16Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G (3 - 1) xs.toFinset) h16Empty := trivial
def h16Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,3,11],[]),([0,1,3,12],[]),([0,1,3,13],[]),([0,1,3,14],[]),([0,3,8,9],[]),([0,1,2,15],[]),([0,1,2,16],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test3_0 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Empty 3 h16Block3_0 = true := by decide +kernel
def h16Nodes3 : List NodeSpec := h16Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Check3 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Empty 3 h16Nodes3 = true := h16Test3_0
def h16Bucket3 : BT (List (List Nat)) := buildBucketsBT h16W h16Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G 3 xs.toFinset) h16Bucket3 := buildBucketsBT_sound (by decide) h16Pairs h16WOk h16PoolsOk h16AutosOk h16EmptyOk h16Check3
def h16Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0,1]),([0,1,2,3,5],[],[0,1]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test4_0 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket3 4 h16Block4_0 = true := by decide +kernel
def h16Nodes4 : List NodeSpec := h16Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Check4 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket3 4 h16Nodes4 = true := h16Test4_0
def h16Bucket4 : BT (List (List Nat)) := buildBucketsBT h16W h16Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G 4 xs.toFinset) h16Bucket4 := buildBucketsBT_sound (by decide) h16Pairs h16WOk h16PoolsOk h16AutosOk h16Bucket3Ok h16Check4
def h16Block5_0 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test5_0 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket4 5 h16Block5_0 = true := by decide +kernel
def h16Nodes5 : List NodeSpec := h16Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Check5 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket4 5 h16Nodes5 = true := h16Test5_0
def h16Bucket5 : BT (List (List Nat)) := buildBucketsBT h16W h16Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G 5 xs.toFinset) h16Bucket5 := buildBucketsBT_sound (by decide) h16Pairs h16WOk h16PoolsOk h16AutosOk h16Bucket4Ok h16Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h16Bucket5Ok (by decide +kernel)
def h17R : List Nat := varsOf 43
def h17G : Nat := 0xeeaaeeaaaa88aa88eeaaeeaaaa88aa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 6 := carry_of (swaps := [(4,5)]) (roots2 := h16R) (T2 := h16G) (by decide +kernel) h16Bound
def h18R : List Nat := varsOf 49
def h18G : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 4 := carry_of (swaps := [(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h19R : List Nat := varsOf 57
def h19G : Nat := 0xffaaaaaaaaaa0000ffaaaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 5 := carry_of (swaps := [(0,1),(1,2),(2,3)]) (roots2 := h13R) (T2 := h13G) (by decide +kernel) h13Bound
def h21R : List Nat := varsOf 56
def h21G : Nat := 0xffffff00ff000000ffffff00ff000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 4 := carry_of (swaps := [(1,2),(2,3)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h20R : List Nat := varsOf 58
def h20G : Nat := 0xffffffccffcc0000ffffffccffcc0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,16,18)]) (by decide +kernel) h21Bound
def h23R : List Nat := varsOf 57
def h23G : Nat := 0xaaaaaa00aa000000aaaaaa00aa000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 5 := carry_of (swaps := [(1,2),(2,3)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h24R : List Nat := varsOf 51
def h24G : Nat := 0xeeeeaaaaaaaa0000eeeeaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 5 := carry_of (swaps := [(0,1)]) (roots2 := h13R) (T2 := h13G) (by decide +kernel) h13Bound
def h22R : List Nat := varsOf 59
def h22G : Nat := 0xeeaaaa88aa880000eeaaaa88aa880000
def h22Pos : List Nat := [25,58,25,49,58,25,41,58,19,58,35,19,25,41,35,19,49,27,41,49,35,27,49,51,19,58,35,19,58,49,49,49,35,49,43,27,58,25,35,58,57]
def h22Neg : List Nat := [24,56,26,48,50,17,40,42,3,26,3,18,9,33,33,17,17,26,9,33,34,11,1,50,16,40,50,50,11,32,50,56,1,16,11,17,10,11,11,34,56]
def h22Mask : Nat := fullMask 41
def h22Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x16fedfffd6d,0x6d106df520),(0xcccccccccccccccccccccccccccccccc,0xdd1fb2cf92,0xf45cb20f94),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bc122632f7,0x174922612c7),(0xffff0000ffff0000ffff0000ffff0000,0x1bafbeb9bbf,0x10acd838a3f),(0xffffffff00000000ffffffff00000000,0x1d7f6dd66da,0x180ee9860da)]
def h22Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,3),(3,0,3),(0,0,4),(3,0,4),(0,1,2),(1,1,2),(2,1,2),(0,1,3),(3,1,3),(0,0,17),(2,0,17),(0,2,4),(1,2,5),(2,2,5),(0,3,4),(1,3,4),(2,3,5),(2,4,5),(0,3,26),(0,4,17),(2,4,17),(2,0,29),(0,3,29),(2,3,29),(3,1,4),(0,0,21),(0,0,23),(1,0,23),(2,0,23),(3,0,23),(1,1,23),(2,1,23),(1,5,23),(0,1,41),(2,4,27),(0,2,6),(3,2,6),(0,3,6),(1,1,46),(0,4,46),(2,4,46),(1,1,48),(2,6,23),(2,3,8),(0,4,52),(2,4,52),(1,8,23),(2,1,53),(1,9,11),(2,3,11),(1,4,9),(2,4,9),(2,4,58),(2,2,35),(2,3,12),(1,9,12),(0,3,34),(2,3,34),(0,3,14),(2,0,67),(0,4,67),(2,4,67),(0,4,14),(2,4,65),(3,9,14),(2,3,33),(0,0,74),(2,4,74),(1,9,33),(2,4,19),(3,1,36),(2,14,23),(2,3,20),(1,16,20),(1,2,80),(2,3,15),(1,15,23),(3,15,23),(1,2,86),(2,4,86),(3,35,36),(3,31,39),(2,2,28),(2,2,40),(0,24,83)]
def h22W : BT Decor := buildWiresBT 7 h22Base h22Steps
def h22AutoList : List (List (Nat × Nat)) := [[],[(4,5)],[(1,3)],[(4,5),(1,3)]]
def h22Autos : BT (List (Nat × Nat)) := btOfList 2 h22AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Pairs : goodPairs h22G h22Pos h22Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22BaseOk : ∀ x ∈ h22Base, faithful h22Pos h22Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22WOk : btAll (fun x => faithful h22Pos h22Neg x ∧ x.1 < 2^128) h22W := buildWiresBT_faithful h22BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h22G = h22G) h22Autos := btAll_ofList (autos_of (by decide +kernel))
def h22SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 8,5),some (subcubeFast 0 10,4),some (subcubeFast 0 16,6),some (subcubeFast 0 32,6),some (subcubeFast 2 0,5),some (subcubeFast 2 1,4),some (subcubeFast 8 0,5),some (subcubeFast 8 1,4)]
def h22Slices : BT (Option (Nat × Nat)) := btOfList 4 h22SliceList
def h22Specs : List PoolSpec := [(0,[]),(6,[]),(7,[]),(4,[(0,0,1)]),(5,[(0,0,1)]),(1,[]),(9,[]),(3,[]),(2,[(3,1,3)]),(8,[(0,0,1)]),(4,[]),(0,[(1,2,5)]),(4,[(0,0,1),(1,2,5)]),(5,[(0,0,1),(1,2,5)]),(2,[]),(1,[(1,2,5)]),(0,[(2,2,5)]),(4,[(0,0,1),(2,2,5)]),(5,[(0,0,1),(2,2,5)]),(1,[(2,2,5)]),(8,[]),(4,[(0,0,1),(1,5,23)]),(4,[(0,0,1),(2,4,5)]),(5,[(0,0,1),(2,3,5)]),(5,[]),(4,[(1,0,1)]),(5,[(1,0,1)]),(4,[(1,0,1),(0,2,6)]),(5,[(1,0,1),(0,2,6)]),(6,[(0,2,6)]),(4,[(1,0,1),(3,2,6)]),(5,[(1,0,1),(3,2,6)]),(6,[(3,2,6)]),(6,[(0,3,6)]),(4,[(1,0,1),(0,4,46)]),(4,[(1,0,1),(2,6,23)]),(5,[(1,0,1),(0,3,6)]),(4,[(2,0,1)]),(5,[(2,0,1)]),(4,[(3,0,1)]),(5,[(3,0,1)]),(4,[(0,0,4)]),(5,[(0,0,3)]),(6,[(0,0,3),(0,0,4)]),(8,[(0,0,3),(0,0,4)]),(4,[(3,0,4)]),(6,[(0,0,3)]),(8,[(0,0,3)]),(5,[(0,0,23)]),(4,[(2,4,9)]),(5,[(3,0,3)]),(5,[(2,3,11)]),(4,[(0,1,2)]),(5,[(0,1,2)]),(4,[(0,1,2),(1,1,2)]),(5,[(0,1,2),(1,1,2)]),(0,[(1,1,2)]),(4,[(1,1,2)]),(5,[(1,1,2)]),(6,[(0,0,21)]),(2,[(0,1,3)]),(4,[(2,1,2)]),(5,[(2,1,2)]),(4,[(2,1,2),(1,15,23)]),(4,[(2,1,2),(3,15,23)]),(5,[(2,1,2),(2,3,15)]),(5,[(0,1,3)]),(4,[(3,1,4)]),(2,[(3,1,4)]),(5,[(2,3,33)]),(5,[(3,1,3)]),(4,[(2,0,17)]),(6,[(2,0,17)]),(4,[(2,4,17)]),(4,[(0,0,23)]),(4,[(1,0,23),(3,1,36)]),(4,[(1,0,23)]),(4,[(2,0,23)]),(5,[(2,0,23)]),(4,[(3,0,23)]),(4,[(2,4,17),(1,1,23)]),(4,[(1,1,23)]),(4,[(2,1,23),(2,2,40)]),(4,[(2,1,23)]),(4,[(0,4,17),(2,2,28)]),(4,[(0,4,17)])]
def h22Pools : BT (Option BoundPool) := buildPoolsBT 7 h22W h22R h22Slices h22Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice9 : Slice h22R h22G (subcubeFast 8 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice8 : Slice h22R h22G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice7 : Slice h22R h22G (subcubeFast 2 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice6 : Slice h22R h22G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice5 : Slice h22R h22G (subcubeFast 0 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice4 : Slice h22R h22G (subcubeFast 0 16) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice3 : Slice h22R h22G (subcubeFast 0 10) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice2 : Slice h22R h22G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice1 : Slice h22R h22G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice0 : Slice h22R h22G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h22R h22G p.1 p.2) h22Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h22R h22G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h22Slice0) (forall_cons (fun _ h => by cases h; exact h22Slice1) (forall_cons (fun _ h => by cases h; exact h22Slice2) (forall_cons (fun _ h => by cases h; exact h22Slice3) (forall_cons (fun _ h => by cases h; exact h22Slice4) (forall_cons (fun _ h => by cases h; exact h22Slice5) (forall_cons (fun _ h => by cases h; exact h22Slice6) (forall_cons (fun _ h => by cases h; exact h22Slice7) (forall_cons (fun _ h => by cases h; exact h22Slice8) (forall_cons (fun _ h => by cases h; exact h22Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h22R h22G c) h22Pools := buildPoolsBT_sound h22SlicesOk
def h22Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G (3 - 1) xs.toFinset) h22Empty := trivial
def h22Block3_0 : List NodeSpec := nodesWithIdentity [([2,23,50,57],[]),([2,23,56,57],[]),([2,23,42,57],[]),([1,23,57,83],[]),([0,1,23,93],[]),([1,23,57,87],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test3_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Empty 3 h22Block3_0 = true := by decide +kernel
def h22Nodes3 : List NodeSpec := h22Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check3 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Empty 3 h22Nodes3 = true := h22Test3_0
def h22Bucket3 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 3 xs.toFinset) h22Bucket3 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22EmptyOk h22Check3
def h22Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,72],[]),([0,3,4,50,62],[]),([0,2,4,50,58],[]),([0,3,4,56,62],[]),([0,2,3,50,59],[]),([0,3,4,13,80],[7]),([0,4,14,16,81],[]),([1,2,3,4,89],[]),([0,2,23,24,50],[]),([0,2,23,24,56],[]),([0,2,23,24,42],[]),([0,2,3,4,90],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Block4_0 = true := by decide +kernel
def h22Block4_1 : List NodeSpec := nodesWithIdentity [([0,3,4,40,91],[7]),([0,1,23,24,83],[]),([0,1,23,24,87],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_1 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Block4_1 = true := by decide +kernel
def h22Nodes4 : List NodeSpec := h22Block4_0 ++ h22Block4_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check4 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Nodes4 = true := by
  unfold h22Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h22Test4_0,h22Test4_1⟩
def h22Bucket4 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 4 xs.toFinset) h22Bucket4 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket3Ok h22Check4
def h22Block5_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,17,26],[]),([0,2,3,4,5,29],[7]),([0,1,3,4,21,23],[1,12,15]),([0,1,3,4,22,23],[17]),([0,1,2,3,4,41],[0,21]),([0,1,2,3,4,27],[22]),([0,1,2,3,4,43],[1]),([0,1,3,4,23,44],[5,27,29]),([0,1,3,4,23,45],[30]),([0,1,2,4,23,46],[5,24,33]),([0,1,2,3,4,48],[5,34]),([0,1,2,3,4,51],[10,24,35])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_0 = true := by decide +kernel
def h22Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,2,4,46,48],[5,33,36]),([0,1,2,4,46,49],[]),([0,1,2,3,4,49],[0]),([0,1,2,4,23,52],[24]),([0,1,2,3,4,55],[]),([0,1,2,3,4,53],[1,14,20]),([0,1,2,3,4,54],[]),([1,2,9,11,23],[0,10,24,41,42,43,44]),([1,2,4,9,11,58],[0]),([0,1,2,9,11,23],[0,10,24]),([0,1,2,4,9,58],[10]),([0,1,2,3,4,35],[1,5,14,20])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_1 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_1 = true := by decide +kernel
def h22Block5_2 : List NodeSpec := nodesWithIdentity [([1,2,3,4,9,64],[]),([1,2,3,4,9,34],[2,6,10]),([0,1,2,4,9,67],[0,5,14]),([0,1,2,3,4,65],[1,5,24]),([0,1,2,3,4,73],[]),([0,1,2,4,9,74],[0]),([0,1,2,3,33,60],[1]),([0,1,2,3,4,77],[24]),([0,1,2,3,4,75],[1]),([1,2,3,4,9,19],[10]),([1,2,4,9,23,36],[10]),([1,2,4,9,23,37],[10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_2 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_2 = true := by decide +kernel
def h22Block5_3 : List NodeSpec := [([0,1,2,9,23,60],[10,24],[0]),([0,1,2,3,4,37],[],[0]),([1,2,3,4,35,37],[10],[0]),([0,2,3,4,35,50],[1,7],[0,1]),([0,2,3,4,35,56],[5],[0,2]),([0,1,2,3,4,58],[],[0]),([0,1,2,4,35,58],[10],[0,2]),([1,2,3,4,9,37],[10],[0]),([0,2,3,4,9,50],[],[0,1]),([0,3,4,13,14,23],[1,5,7,54],[0]),([0,1,2,3,4,66],[],[0]),([0,3,4,14,16,20],[1],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_3 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_3 = true := by decide +kernel
def h22Block5_4 : List NodeSpec := [([0,2,3,4,16,71],[10],[0]),([0,2,3,4,14,76],[20],[0,3]),([0,1,2,4,23,67],[24],[0]),([0,1,2,3,4,69],[],[0]),([0,1,2,3,4,80],[1,5],[0]),([0,1,2,3,4,68],[],[0]),([0,1,2,3,4,70],[],[0]),([0,1,2,3,4,85],[1,63],[0]),([0,1,2,3,4,86],[5,64],[0]),([0,1,2,3,4,88],[1],[0]),([0,1,2,4,16,81],[5],[0]),([0,1,2,3,4,82],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_4 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_4 = true := by decide +kernel
def h22Block5_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,78],[]),([0,1,2,3,4,30],[]),([1,2,3,4,35,36],[]),([0,2,3,4,23,50],[]),([0,2,3,4,23,56],[]),([0,1,2,4,23,58],[10]),([0,2,3,4,23,42],[]),([0,2,3,4,23,79],[75]),([1,2,3,4,37,38],[]),([0,1,2,4,23,63],[10]),([0,2,3,4,31,39],[80]),([0,1,2,4,23,32],[10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_5 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_5 = true := by decide +kernel
def h22Block5_6 : List NodeSpec := nodesWithIdentity [([0,2,3,4,28,40],[7]),([0,1,3,4,23,83],[1,7]),([0,1,3,4,23,92],[82]),([0,1,3,4,23,87],[]),([0,1,3,4,23,91],[5,84]),([0,1,2,4,23,74],[10,69])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_6 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_6 = true := by decide +kernel
def h22Nodes5 : List NodeSpec := h22Block5_0 ++ h22Block5_1 ++ h22Block5_2 ++ h22Block5_3 ++ h22Block5_4 ++ h22Block5_5 ++ h22Block5_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check5 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Nodes5 = true := by
  unfold h22Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h22Test5_0,h22Test5_1⟩,h22Test5_2⟩,h22Test5_3⟩,h22Test5_4⟩,h22Test5_5⟩,h22Test5_6⟩
def h22Bucket5 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 5 xs.toFinset) h22Bucket5 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket4Ok h22Check5
def h22Block6_0 : List NodeSpec := [([0,2,3,4,5,17],[0,1,3,5,7,8,9,10],[0]),([0,1,3,4,21],[1,2,7,11,12,13,14,15],[0]),([0,1,3,4,22],[1,2,16,17,18,19,20],[0]),([0,1,2,3,4,5,23],[1,3,5],[0]),([0,1,2,3,4,25],[0,1,2,3,5,10,14,20,23,24],[0,1]),([0,1,3,4,44],[0,5,20,27,28,29],[0]),([0,1,3,4,45],[0,5,14,30,31,32],[0]),([0,1,2,3,4,6,23],[0,1,5,10,24,25],[0,1]),([0,1,2,4,46],[0,2,5,6,25,33,36],[0]),([0,1,2,3,4,46],[0,2,5,6,10,14,20,24,25,33,36],[0]),([0,1,2,3,4,7,23],[1,2,5,37],[0]),([0,1,2,3,4,8,23],[0,1,5,10,24,39],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_0 = true := by decide +kernel
def h22Block6_1 : List NodeSpec := [([0,1,2,3,4,52],[0,1,6,10,14,20,24,39],[0]),([1,2,3,4,9,11],[0,2,6,10,24,41,42],[0,1]),([0,1,2,3,4,9,11],[0,10,24,41,42],[0,1]),([1,2,3,4,9,12],[0,2,6,10,24,42,45],[0]),([0,1,2,3,4,9,14],[0,1,2,5,6,10,14,20],[0]),([0,1,2,3,4,9,33],[1,2,5,10,24],[0]),([0,1,2,3,4,9,47],[0,1,2,5,10],[0]),([0,1,2,3,4,9,18],[1,2,5],[0]),([0,1,2,4,9,23],[0,10,24,42,46,47],[0]),([0,1,2,3,4,35],[1,5,14,20],[0,1,2]),([0,1,2,3,4,9,35],[2,6,24,48],[0,1,2]),([0,1,2,3,4,60],[0,1,5,10,14,20,24,42,49],[0,1,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_1 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_1 = true := by decide +kernel
def h22Block6_2 : List NodeSpec := [([0,1,2,3,4,9,60],[0,10,24,42],[0,1]),([0,1,2,3,4,61],[0,1,2,5,6,10,14,20,24,41,51],[0]),([0,3,4,13,14],[1,2,5,7,54,55,56],[0]),([0,1,2,3,4,13,23],[1,5,7,14,20,52],[0]),([0,1,2,3,4,34],[0,1,2,5,6,9,10,11,14,24,59],[0,1]),([0,2,3,4,14,16],[1,2,5,10,20,56,57,60],[0]),([0,1,2,3,4,14,23],[1,5,10,14,20,24,57],[0,1]),([0,1,2,3,4,67],[0,1,5,10,14,24,57],[0,1,3]),([0,1,2,3,4,15,23],[1,5,14,20,61],[0]),([0,1,2,3,4,84],[0,1,2,5,7,10,14,24,61,65],[0]),([0,2,3,4,16,33],[1,2,5,10,24,60,66,67,68],[0]),([0,1,2,3,4,16,20],[1,5,10,14,20,24],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_2 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_2 = true := by decide +kernel
def h22Block6_3 : List NodeSpec := [([0,1,2,3,4,76],[0,1,2,5,10,14,20,24,67,69],[0,3]),([0,1,2,3,4,19],[0,1,2,5,10,14,20,24,71,72],[0,1]),([0,1,2,3,4,29],[0,1,5,7,10,14,20,24,70,73],[0,1]),([0,1,2,3,4,23,35],[0,74],[0,1,2]),([0,1,2,3,4,23,36],[0,10,24,76],[0,1,2]),([0,1,2,3,4,37],[1,5,10,14,20,24,77,78],[0]),([0,1,2,3,4,23,37],[0,10,24,77],[0,1]),([0,1,2,3,4,23,38],[0,79],[0,1]),([0,1,2,3,4,23,31],[1,5,73],[0,1]),([0,1,2,3,4,23,39],[1,5,81],[0]),([0,1,2,3,4,23,40],[1,5,83],[0]),([0,1,2,3,4,23,28],[1,5,85],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_3 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_3 = true := by decide +kernel
def h22Nodes6 : List NodeSpec := h22Block6_0 ++ h22Block6_1 ++ h22Block6_2 ++ h22Block6_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check6 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Nodes6 = true := by
  unfold h22Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h22Test6_0,h22Test6_1⟩,h22Test6_2⟩,h22Test6_3⟩
def h22Bucket6 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 6 xs.toFinset) h22Bucket6 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket5Ok h22Check6
def h22Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,10,14,20,24],[0,1]),([0,1,2,3,4,6],[0,1,2,5,6,10,14,20,24,25,26],[0,1]),([0,1,2,3,4,7],[0,1,2,5,6,7,10,14,20,24,37,38],[0]),([0,1,2,3,4,8],[0,1,6,10,14,20,24,39,40],[0,1]),([0,1,2,3,4,9],[0,1,2,5,6,10,14,20,24,42],[0,2]),([0,1,2,3,4,10],[0,1,2,5,6,10,14,20,24,50],[0,1]),([0,1,2,3,4,13],[0,1,2,5,7,10,20,24,52,53],[0]),([0,1,2,3,4,14],[0,1,2,5,6,10,14,20,24,57,58],[0,1,2,3]),([0,1,2,3,4,15],[0,1,2,5,7,10,14,20,24,61,62],[0,1]),([0,1,2,3,4,16],[0,1,2,7,10,14,20,24,66],[0]),([0,1,2,3,4,17],[0,1,2,5,7,10,14,20,24,70],[0,1]),([0,1,2,3,4,23],[0,1,5,10,14,20,24],[0,1,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test7_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket6 7 h22Block7_0 = true := by decide +kernel
def h22Nodes7 : List NodeSpec := h22Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check7 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket6 7 h22Nodes7 = true := h22Test7_0
def h22Bucket7 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 7 xs.toFinset) h22Bucket7 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket6Ok h22Check7
def h22Block8_0 : List NodeSpec := [([0,1,2,3,4],[10,24],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test8_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket7 8 h22Block8_0 = true := by decide +kernel
def h22Nodes8 : List NodeSpec := h22Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check8 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket7 8 h22Nodes8 = true := h22Test8_0
def h22Bucket8 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 8 xs.toFinset) h22Bucket8 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket7Ok h22Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 9 := lower_of_forestBT (essPairs := [(VAR 0,18,19),(VAR 1,17,19),(VAR 3,17,25),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h22Bucket8Ok (by decide +kernel)
def h25R : List Nat := varsOf 29
def h25G : Nat := 0xfaaaaa00faaaaa00faaaaa00faaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 5 := carry_of (swaps := [(3,4),(4,5),(0,1),(1,2)]) (roots2 := h13R) (T2 := h13G) (by decide +kernel) h13Bound
def h26R : List Nat := varsOf 45
def h26G : Nat := 0xfaaafaaaaa00aa00faaafaaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 5 := carry_of (swaps := [(3,4),(0,1),(1,2)]) (roots2 := h13R) (T2 := h13G) (by decide +kernel) h13Bound
def h27R : List Nat := varsOf 53
def h27G : Nat := 0xfafaaaaaaaaaa0a0fafaaaaaaaaaa0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 6 := carry_of (swaps := [(4,5),(3,4),(1,2)]) (roots2 := h16R) (T2 := h16G) (by decide +kernel) h16Bound
def h28R : List Nat := varsOf 60
def h28G : Nat := 0xffffff00ff00f000ffffff00ff00f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,8,12)]) (by decide +kernel) h21Bound
def h30R : List Nat := varsOf 41
def h30G : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 4 := carry_of (swaps := [(3,4),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h31R : List Nat := varsOf 57
def h31G : Nat := 0xffaaaa00aa00aa00ffaaaa00aa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,33,49)]) (by decide +kernel) h30Bound
def h29R : List Nat := varsOf 61
def h29G : Nat := 0xfaaaaa00aa00a000faaaaa00aa00a000
def h29Pos : List Nat := [25,60,13,13,49,60,13,60,41,13,60,41,25,49,41,25,29,49,41,57]
def h29Neg : List Nat := [24,56,9,12,48,52,5,44,40,28,28,9,17,17,33,9,21,33,56,56]
def h29Mask : Nat := fullMask 20
def h29Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffb5d,0x3f844),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x106ee,0x106e8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xddfef,0xc8f8f),(0xffff0000ffff0000ffff0000ffff0000,0xbb4b3,0xd3633),(0xffffffff00000000ffffffff00000000,0xe6db2,0xe41b2)]
def h29Steps : List (Nat × Nat × Nat) := [(0,0,3),(0,2,5),(2,2,6),(0,3,4),(2,4,6),(0,0,8),(2,0,8),(0,2,8),(2,2,8),(2,4,5),(2,2,10)]
def h29W : BT Decor := buildWiresBT 4 h29Base h29Steps
def h29AutoList : List (List (Nat × Nat)) := [[],[(4,5)]]
def h29Autos : BT (List (Nat × Nat)) := btOfList 1 h29AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Pairs : goodPairs h29G h29Pos h29Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29BaseOk : ∀ x ∈ h29Base, faithful h29Pos h29Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29WOk : btAll (fun x => faithful h29Pos h29Neg x ∧ x.1 < 2^128) h29W := buildWiresBT_faithful h29BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h29G = h29G) h29Autos := btAll_ofList (autos_of (by decide +kernel))
def h29SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,6),some (subcubeFast 0 16,5),some (subcubeFast 0 20,4),some (subcubeFast 0 32,5),some (subcubeFast 4 0,5),some (subcubeFast 4 1,4)]
def h29Slices : BT (Option (Nat × Nat)) := btOfList 3 h29SliceList
def h29Specs : List PoolSpec := [(6,[]),(0,[]),(1,[]),(2,[]),(2,[(0,0,3)]),(3,[]),(6,[(0,0,3)]),(4,[]),(7,[]),(5,[]),(1,[(0,3,4)]),(2,[(0,3,4)])]
def h29Pools : BT (Option BoundPool) := buildPoolsBT 4 h29W h29R h29Slices h29Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice7 : Slice h29R h29G (subcubeFast 4 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice6 : Slice h29R h29G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice5 : Slice h29R h29G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice4 : Slice h29R h29G (subcubeFast 0 20) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice3 : Slice h29R h29G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice2 : Slice h29R h29G (subcubeFast 0 8) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice1 : Slice h29R h29G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice0 : Slice h29R h29G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h29R h29G p.1 p.2) h29Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h29R h29G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h29Slice0) (forall_cons (fun _ h => by cases h; exact h29Slice1) (forall_cons (fun _ h => by cases h; exact h29Slice2) (forall_cons (fun _ h => by cases h; exact h29Slice3) (forall_cons (fun _ h => by cases h; exact h29Slice4) (forall_cons (fun _ h => by cases h; exact h29Slice5) (forall_cons (fun _ h => by cases h; exact h29Slice6) (forall_cons (fun _ h => by cases h; exact h29Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h29R h29G c) h29Pools := buildPoolsBT_sound h29SlicesOk
def h29Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G (4 - 1) xs.toFinset) h29Empty := trivial
def h29Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,9],[]),([0,1,3,4,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test4_0 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Empty 4 h29Block4_0 = true := by decide +kernel
def h29Nodes4 : List NodeSpec := h29Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Check4 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Empty 4 h29Nodes4 = true := h29Test4_0
def h29Bucket4 : BT (List (List Nat)) := buildBucketsBT h29W h29Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G 4 xs.toFinset) h29Bucket4 := buildBucketsBT_sound (by decide) h29Pairs h29WOk h29PoolsOk h29AutosOk h29EmptyOk h29Check4
def h29Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,6],[0,2,9]),([0,1,2,3,4,7],[0,2]),([0,1,2,4,5,8],[1,9,10]),([0,1,2,3,4,10],[0,2,3]),([0,1,2,3,4,14],[]),([0,1,2,3,4,11],[]),([0,1,2,3,4,12],[]),([0,1,2,3,4,13],[11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test5_0 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket4 5 h29Block5_0 = true := by decide +kernel
def h29Nodes5 : List NodeSpec := h29Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Check5 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket4 5 h29Nodes5 = true := h29Test5_0
def h29Bucket5 : BT (List (List Nat)) := buildBucketsBT h29W h29Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G 5 xs.toFinset) h29Bucket5 := buildBucketsBT_sound (by decide) h29Pairs h29WOk h29PoolsOk h29AutosOk h29Bucket4Ok h29Check5
def h29Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9],[0]),([0,1,2,3,4,8],[0,1,2,3,5,9,10,11],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test6_0 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket5 6 h29Block6_0 = true := by decide +kernel
def h29Nodes6 : List NodeSpec := h29Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Check6 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket5 6 h29Nodes6 = true := h29Test6_0
def h29Bucket6 : BT (List (List Nat)) := buildBucketsBT h29W h29Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G 6 xs.toFinset) h29Bucket6 := buildBucketsBT_sound (by decide) h29Pairs h29WOk h29PoolsOk h29AutosOk h29Bucket5Ok h29Check6
def h29Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,5,9],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test7_0 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket6 7 h29Block7_0 = true := by decide +kernel
def h29Nodes7 : List NodeSpec := h29Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Check7 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket6 7 h29Nodes7 = true := h29Test7_0
def h29Bucket7 : BT (List (List Nat)) := buildBucketsBT h29W h29Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G 7 xs.toFinset) h29Bucket7 := buildBucketsBT_sound (by decide) h29Pairs h29WOk h29PoolsOk h29AutosOk h29Bucket6Ok h29Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 8 := lower_of_forestBT (essPairs := [(VAR 0,12,13),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,9,25),(VAR 5,9,41)]) (by decide +kernel) h29Bucket7Ok (by decide +kernel)
def h32R : List Nat := varsOf 14
def h32G : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 4 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h33R : List Nat := varsOf 22
def h33G : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 4 := carry_of (swaps := [(3,4),(4,5),(2,3)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h34R : List Nat := varsOf 38
def h34G : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 4 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h35R : List Nat := varsOf 46
def h35G : Nat := 0xfcc0fcc0c0c0c0c0fcc0fcc0c0c0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 5 := carry_of (swaps := [(2,3),(3,4),(0,1)]) (roots2 := h31R) (T2 := h31G) (by decide +kernel) h31Bound
def h36R : List Nat := varsOf 54
def h36G : Nat := 0xfcfcc0c0c0c0c0c0fcfcc0c0c0c0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 5 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h31R) (T2 := h31G) (by decide +kernel) h31Bound
def h37R : List Nat := varsOf 60
def h37G : Nat := 0xfff0f0f0f0f0f000fff0f0f0f0f0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 6 := carry_of (swaps := [(4,5),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h16R) (T2 := h16G) (by decide +kernel) h16Bound
def h39R : List Nat := varsOf 30
def h39G : Nat := 0xfcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(0,1)]) (roots2 := h31R) (T2 := h31G) (by decide +kernel) h31Bound
def h40R : List Nat := varsOf 58
def h40G : Nat := 0xffcccccccccccc00ffcccccccccccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 6 := carry_of (swaps := [(4,5),(3,4),(1,2),(2,3),(0,1)]) (roots2 := h16R) (T2 := h16G) (by decide +kernel) h16Bound
def h38R : List Nat := varsOf 62
def h38G : Nat := 0xfcc0c0c0c0c0c000fcc0c0c0c0c0c000
def h38Pos : List Nat := [58,60,60,22,38,58,58,38,22,14,22,60,60,22,22,58,22,14,38,58,14,30,30,38,38,14,14,14,46,14,46,30,54,58,22]
def h38Neg : List Nat := [56,56,52,6,6,26,42,34,18,6,26,28,44,28,24,50,20,10,36,34,12,28,26,44,52,4,2,8,44,26,42,20,52,40,2]
def h38Mask : Nat := fullMask 35
def h38Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x7ffffe7f9,0x4644a87f8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x5fff77f9e,0x193b53a1c),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x2fe7a9a67,0x278f27c63),(0xffff0000ffff0000ffff0000ffff0000,0x78069fd6f,0x1a161ed27),(0xffffffff00000000ffffffff00000000,0x3518c98f7,0x3518c90c7)]
def h38Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(3,0,1),(0,0,2),(0,1,2),(0,3,4),(0,3,5),(0,3,8),(2,3,12),(0,4,12),(2,4,12),(0,5,9),(2,5,9),(0,5,12),(0,4,13),(2,4,13),(1,8,9),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,5),(2,2,5),(2,1,2),(0,1,3),(0,4,22),(3,5,22),(1,8,29),(0,5,32),(2,8,29),(2,3,29),(2,1,8),(2,3,36),(2,1,25),(2,4,25),(1,8,25),(0,3,26),(3,3,26),(2,3,27),(2,1,12),(2,2,12),(1,13,35),(2,1,13),(2,0,2),(0,0,23),(2,1,49),(2,4,33),(3,5,23),(2,0,16),(1,3,16),(2,4,16),(2,2,18),(2,4,18),(2,23,27),(2,0,24),(0,1,59),(2,1,59),(1,4,24),(2,4,24),(1,5,24),(2,1,53),(3,16,26),(0,4,6),(0,6,46),(2,4,43),(2,0,17),(1,8,28),(2,0,30),(2,1,14)]
def h38W : BT Decor := buildWiresBT 7 h38Base h38Steps
def h38AutoList : List (List (Nat × Nat)) := [[],[(4,5)],[(3,4)],[(3,5)],[(1,2)],[(4,5),(3,4)],[(4,5),(3,5)],[(4,5),(1,2)],[(3,4),(1,2)],[(3,5),(1,2)],[(4,5),(3,4),(1,2)],[(4,5),(3,5),(1,2)]]
def h38Autos : BT (List (Nat × Nat)) := btOfList 4 h38AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Pairs : goodPairs h38G h38Pos h38Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38BaseOk : ∀ x ∈ h38Base, faithful h38Pos h38Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38WOk : btAll (fun x => faithful h38Pos h38Neg x ∧ x.1 < 2^128) h38W := buildWiresBT_faithful h38BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h38G = h38G) h38Autos := btAll_ofList (autos_of (by decide +kernel))
def h38SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,6),some (subcubeFast 0 4,6),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 24,4),some (subcubeFast 0 32,5),some (subcubeFast 0 40,4),some (subcubeFast 0 48,4)]
def h38Slices : BT (Option (Nat × Nat)) := btOfList 3 h38SliceList
def h38Specs : List PoolSpec := [(0,[]),(1,[]),(1,[(0,0,2)]),(2,[]),(0,[(0,1,2)]),(0,[(0,2,3)]),(0,[(0,2,3),(1,2,3)]),(4,[]),(5,[(0,2,3)]),(3,[]),(5,[]),(0,[(1,2,3)]),(0,[(2,2,3)]),(5,[(2,2,3)]),(2,[(2,4,24)]),(6,[]),(0,[(2,2,3),(1,4,24)]),(2,[(1,4,24)]),(0,[(2,2,3),(2,4,24)]),(7,[]),(0,[(0,1,2),(1,3,16)]),(0,[(1,2,5)]),(0,[(1,2,5),(0,3,26)]),(0,[(1,2,5),(3,3,26)]),(0,[(2,2,5)]),(1,[(2,2,5)]),(1,[(2,5,9)]),(0,[(2,1,2)]),(1,[(0,5,9)]),(0,[(2,1,8)]),(3,[(0,4,22)]),(0,[(3,2,3)]),(5,[(3,2,3)]),(0,[(3,2,3),(2,4,25)]),(3,[(2,4,25)]),(0,[(0,3,8)]),(1,[(2,0,2)]),(1,[(0,2,3)]),(1,[(0,2,3),(1,2,3)]),(2,[(0,4,22)]),(1,[(1,2,3)]),(1,[(2,2,3)]),(1,[(2,2,3),(1,4,24)]),(1,[(2,2,3),(2,4,24)])]
def h38Pools : BT (Option BoundPool) := buildPoolsBT 6 h38W h38R h38Slices h38Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Slice7 : Slice h38R h38G (subcubeFast 0 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Slice6 : Slice h38R h38G (subcubeFast 0 40) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Slice5 : Slice h38R h38G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Slice4 : Slice h38R h38G (subcubeFast 0 24) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Slice3 : Slice h38R h38G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Slice2 : Slice h38R h38G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Slice1 : Slice h38R h38G (subcubeFast 0 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Slice0 : Slice h38R h38G (subcubeFast 0 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h38R h38G p.1 p.2) h38Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h38R h38G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h38Slice0) (forall_cons (fun _ h => by cases h; exact h38Slice1) (forall_cons (fun _ h => by cases h; exact h38Slice2) (forall_cons (fun _ h => by cases h; exact h38Slice3) (forall_cons (fun _ h => by cases h; exact h38Slice4) (forall_cons (fun _ h => by cases h; exact h38Slice5) (forall_cons (fun _ h => by cases h; exact h38Slice6) (forall_cons (fun _ h => by cases h; exact h38Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h38R h38G c) h38Pools := buildPoolsBT_sound h38SlicesOk
def h38Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h38G (3 - 1) xs.toFinset) h38Empty := trivial
def h38Block3_0 : List NodeSpec := nodesWithIdentity [([4,5,22,32],[]),([4,5,21,46],[]),([2,5,46,67],[]),([2,4,5,68],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test3_0 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Empty 3 h38Block3_0 = true := by decide +kernel
def h38Nodes3 : List NodeSpec := h38Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Check3 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Empty 3 h38Nodes3 = true := h38Test3_0
def h38Bucket3 : BT (List (List Nat)) := buildBucketsBT h38W h38Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h38G 3 xs.toFinset) h38Bucket3 := buildBucketsBT_sound (by decide) h38Pairs h38WOk h38PoolsOk h38AutosOk h38EmptyOk h38Check3
def h38Block4_0 : List NodeSpec := nodesWithIdentity [([3,4,5,9,12],[1]),([3,4,5,9,13],[]),([4,5,8,22,29],[]),([2,3,4,5,32],[0,1]),([3,4,5,8,38],[]),([1,3,5,8,39],[]),([1,4,5,8,41],[]),([2,4,5,13,35],[]),([1,4,5,22,49],[7]),([0,1,4,23,31],[]),([0,1,4,22,33],[7,8]),([0,1,3,4,56],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test4_0 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket3 4 h38Block4_0 = true := by decide +kernel
def h38Block4_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,57],[]),([0,1,3,4,58],[]),([0,1,2,3,51],[]),([0,1,3,27,62],[]),([0,1,2,11,63],[14,15]),([0,1,4,27,54],[]),([0,1,2,54,55],[]),([0,1,2,46,55],[]),([0,1,4,16,41],[7,15]),([0,1,3,4,66],[]),([2,4,5,6,46],[]),([0,1,2,3,69],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test4_1 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket3 4 h38Block4_1 = true := by decide +kernel
def h38Block4_2 : List NodeSpec := nodesWithIdentity [([0,1,4,22,32],[]),([0,1,3,36,39],[]),([0,2,3,4,73],[]),([0,1,4,22,50],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test4_2 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket3 4 h38Block4_2 = true := by decide +kernel
def h38Nodes4 : List NodeSpec := h38Block4_0 ++ h38Block4_1 ++ h38Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Check4 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket3 4 h38Nodes4 = true := by
  unfold h38Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h38Test4_0,h38Test4_1⟩,h38Test4_2⟩
def h38Bucket4 : BT (List (List Nat)) := buildBucketsBT h38W h38Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h38G 4 xs.toFinset) h38Bucket4 := buildBucketsBT_sound (by decide) h38Pairs h38WOk h38PoolsOk h38AutosOk h38Bucket3Ok h38Check4
def h38Block5_0 : List NodeSpec := [([3,4,5,8,9],[0,1,2,3,4],[0,1,4,7]),([2,3,4,5,8,9],[0,1,3],[0]),([2,3,4,5,8,29],[],[0,2,4]),([2,3,4,5,8,36],[0,1],[0]),([1,3,4,5,8,22],[],[0,4]),([1,3,4,5,8,25],[],[0]),([1,3,4,5,8,26],[0],[0,1]),([1,3,4,5,8,27],[0],[0]),([1,2,3,4,5,12],[1],[0,2]),([1,2,3,4,5,13],[1],[0]),([0,1,4,5,22,23],[3,6,7],[0,4]),([0,1,3,4,16,22],[8,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test5_0 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket4 5 h38Block5_0 = true := by decide +kernel
def h38Block5_1 : List NodeSpec := [([0,1,2,3,4,18],[10],[0,2]),([0,1,2,3,4,31],[],[0]),([1,2,3,4,5,49],[1],[0]),([0,1,3,4,23,27],[],[0]),([0,1,2,3,4,33],[3,9,10],[0]),([0,1,2,3,4,52],[],[0]),([1,2,3,4,5,59],[1],[0,8]),([0,1,3,4,24,27],[],[0]),([0,1,2,4,11,24],[3,13],[0,2]),([0,1,2,3,5,62],[16,17],[0]),([0,1,2,3,5,63],[9,18],[0,2,8]),([0,1,2,3,4,64],[3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test5_1 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket4 5 h38Block5_1 = true := by decide +kernel
def h38Block5_2 : List NodeSpec := [([0,1,2,3,4,60],[],[0]),([0,1,2,3,4,53],[],[0]),([1,2,3,4,16,53],[0],[0]),([0,1,2,3,4,27],[],[0]),([0,1,3,4,16,27],[0],[0,1]),([0,1,2,4,16,54],[19],[0,2]),([0,1,2,4,46],[],[0]),([0,1,2,3,4,46],[],[0]),([0,1,2,4,16,46],[9],[0,1]),([1,2,3,4,5,53],[0],[0]),([0,1,3,4,16,26],[7,15],[0,1]),([0,1,2,4,5,54],[7,20],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test5_2 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket4 5 h38Block5_2 = true := by decide +kernel
def h38Block5_3 : List NodeSpec := [([0,1,2,4,5,46],[],[0]),([0,1,2,4,5,41],[3,22],[0,4]),([0,1,2,4,5,42],[23],[0]),([0,1,2,3,4,16],[9,10],[0,2,6]),([0,1,2,3,4,43],[10],[0]),([0,1,3,4,17,27],[],[0]),([1,2,3,4,5,70],[0],[0]),([1,3,4,8,9,53],[3],[0]),([0,1,3,4,9,12],[1],[0]),([0,1,3,4,9,13],[],[0]),([1,2,3,4,8,53],[0],[0]),([0,1,3,4,8,71],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test5_3 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket4 5 h38Block5_3 = true := by decide +kernel
def h38Block5_4 : List NodeSpec := [([0,1,4,8,22,29],[],[0]),([0,1,2,3,4,32],[0,1],[0]),([0,1,2,3,4,34],[],[0]),([0,1,3,4,8,27],[0],[0]),([0,1,2,4,8,46],[],[0]),([0,1,3,4,22,36],[9],[0]),([0,1,3,4,25,36],[],[0]),([0,1,2,3,4,37],[],[0]),([0,1,4,8,13,22],[9],[0]),([0,1,3,4,8,30],[0,7,8,30],[0]),([0,1,3,4,8,38],[],[0]),([0,1,3,8,39],[3,15,32,33,34],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test5_4 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket4 5 h38Block5_4 = true := by decide +kernel
def h38Block5_5 : List NodeSpec := [([0,1,3,4,8,40],[],[0]),([0,1,2,4,10,13],[10],[0]),([0,1,2,3,4,14],[1],[0]),([0,1,2,3,4,19],[],[0]),([0,1,2,3,4,44],[],[0]),([0,1,3,4,12,45],[0],[0]),([0,1,2,3,4,15],[],[0]),([0,1,3,4,8,45],[0],[0]),([1,2,3,4,7,13],[],[0]),([0,1,2,4,13,35],[],[0,2]),([0,1,2,3,4,47],[],[0,2]),([0,1,2,3,4,20],[3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test5_5 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket4 5 h38Block5_5 = true := by decide +kernel
def h38Block5_6 : List NodeSpec := nodesWithIdentity [([0,1,4,22,49],[3,6,7,8,15]),([0,1,2,3,4,72],[]),([0,1,2,3,4,50],[]),([0,1,2,3,4,61],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test5_6 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket4 5 h38Block5_6 = true := by decide +kernel
def h38Nodes5 : List NodeSpec := h38Block5_0 ++ h38Block5_1 ++ h38Block5_2 ++ h38Block5_3 ++ h38Block5_4 ++ h38Block5_5 ++ h38Block5_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Check5 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket4 5 h38Nodes5 = true := by
  unfold h38Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h38Test5_0,h38Test5_1⟩,h38Test5_2⟩,h38Test5_3⟩,h38Test5_4⟩,h38Test5_5⟩,h38Test5_6⟩
def h38Bucket5 : BT (List (List Nat)) := buildBucketsBT h38W h38Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h38G 5 xs.toFinset) h38Bucket5 := buildBucketsBT_sound (by decide) h38Pairs h38WOk h38PoolsOk h38AutosOk h38Bucket4Ok h38Check5
def h38Block6_0 : List NodeSpec := [([1,2,3,4,5,8],[0,1,2,3],[0,1]),([0,1,2,3,4,5,22],[0,1,3,5,7,9],[0,2,4,8]),([0,1,2,3,4,5,23],[0,1,3,9,11],[0,2,4]),([0,1,2,3,4,5,24],[0,1,3,9,12],[0,2,4,8]),([0,1,2,3,4,16],[9,10],[0,1,2,4,6]),([0,1,2,3,4,5,16],[3,4],[0,1,4]),([0,1,2,3,4,5,26],[0,1,3,21],[0,1,4]),([0,1,2,3,4,27],[0,1,9,10,24,25],[0,1]),([0,1,2,3,4,5,27],[0,1,3,24],[0,4]),([0,1,2,3,4,5,17],[3,26],[0,4]),([0,1,3,4,8,9],[0,1,2,3,4],[0,1,4,7]),([0,1,2,3,4,8,9],[0,1,2,3,4],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test6_0 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket5 6 h38Block6_0 = true := by decide +kernel
def h38Block6_1 : List NodeSpec := [([0,1,3,4,8,28],[0,1,2,3,7,15,27],[0]),([0,1,2,3,4,8,29],[3,9],[0,2,4,8]),([0,1,2,3,4,8,16],[1,7,15,28],[0,1,4]),([0,1,2,3,4,36],[0,1,2,3,9,10,29],[0,1,4,8,11]),([0,1,2,3,4,8,36],[0,1,2,3],[0,4]),([0,1,3,4,8,22],[0,3,5,7,8,9,15],[0,4]),([0,1,3,4,8,25],[0,3,7,9,15,31,32],[0,2]),([0,1,2,3,4,8,10],[3,7,9,10,15,19],[0,1]),([0,1,2,3,4,12],[1,7,10,35],[0,2]),([0,1,2,3,4,8,12],[7,9],[0,2]),([0,1,2,3,4,13],[0,1,3,7,10],[0,2,8]),([0,1,2,3,4,8,13],[0,3,7,9],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test6_1 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket5 6 h38Block6_1 = true := by decide +kernel
def h38Block6_2 : List NodeSpec := [([0,1,2,3,4,65],[0,1,3,4,7,9,10,15],[0]),([0,1,4,22,23],[3,6,7,8,15,38],[0,4]),([0,1,2,3,4,30],[0,1,7,8,15,19,30,39],[0,2,3,4,8,9]),([0,1,2,3,4,49],[0,1,3,9,10,11,15],[0]),([0,1,2,3,4,59],[0,1,3,7,9,10,12,19],[0,8]),([0,1,2,3,62],[7,9,10,16,17,42],[0]),([0,1,2,3,63],[7,9,14,15,18,19,43],[0,2,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test6_2 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket5 6 h38Block6_2 = true := by decide +kernel
def h38Nodes6 : List NodeSpec := h38Block6_0 ++ h38Block6_1 ++ h38Block6_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Check6 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket5 6 h38Nodes6 = true := by
  unfold h38Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h38Test6_0,h38Test6_1⟩,h38Test6_2⟩
def h38Bucket6 : BT (List (List Nat)) := buildBucketsBT h38W h38Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h38G 6 xs.toFinset) h38Bucket6 := buildBucketsBT_sound (by decide) h38Pairs h38WOk h38PoolsOk h38AutosOk h38Bucket5Ok h38Check6
def h38Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,3,9,10],[0,1,2,3,4,5,6,8,9]),([0,1,2,3,4,8],[0,1,2,3,7,9,10,15],[0,1]),([0,1,2,3,4,48],[0,1,3,7,9,10,15,36],[0,4]),([0,1,2,3,4,22],[0,1,3,5,7,9,10,15,19,37],[0,2,3,4,8,9]),([0,1,2,3,4,23],[0,1,3,9,10,11,15,40],[0,4]),([0,1,2,3,4,24],[0,1,3,7,9,10,12,15,19,41],[0,2,4,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test7_0 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket6 7 h38Block7_0 = true := by decide +kernel
def h38Nodes7 : List NodeSpec := h38Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Check7 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket6 7 h38Nodes7 = true := h38Test7_0
def h38Bucket7 : BT (List (List Nat)) := buildBucketsBT h38W h38Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h38G 7 xs.toFinset) h38Bucket7 := buildBucketsBT_sound (by decide) h38Pairs h38WOk h38PoolsOk h38AutosOk h38Bucket6Ok h38Check7
def h38Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,1],[0,1,2,3,4,5,6,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Test8_0 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket7 8 h38Block8_0 = true := by decide +kernel
def h38Nodes8 : List NodeSpec := h38Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Check8 : checkNodesBT h38W h38G h38Mask h38Pools h38Autos h38Bucket7 8 h38Nodes8 = true := h38Test8_0
def h38Bucket8 : BT (List (List Nat)) := buildBucketsBT h38W h38Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h38G 8 xs.toFinset) h38Bucket8 := buildBucketsBT_sound (by decide) h38Pairs h38WOk h38PoolsOk h38AutosOk h38Bucket7Ok h38Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 9 := lower_of_forestBT (essPairs := [(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,6,22),(VAR 5,6,38)]) (by decide +kernel) h38Bucket8Ok (by decide +kernel)
def h41R : List Nat := varsOf 15
def h41G : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h32Bound
def h42R : List Nat := varsOf 23
def h42G : Nat := 0xfefeeaeafefeeaeafefeeaeafefeeaea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bound : Lower h42R h42G 5 := carry_of (swaps := [(3,4)]) (roots2 := h41R) (T2 := h41G) (by decide +kernel) h41Bound
def h44R : List Nat := varsOf 25
def h44G : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bound : Lower h44R h44G 4 := carry_of (swaps := [(3,4),(4,5),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h45R : List Nat := varsOf 27
def h45G : Nat := 0xffeeeeccffeeeeccffeeeeccffeeeecc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bound : Lower h45R h45G 5 := carry_of (swaps := [(3,4),(2,3),(0,1)]) (roots2 := h41R) (T2 := h41G) (by decide +kernel) h41Bound
def h43R : List Nat := varsOf 31
def h43G : Nat := 0xfeeaeac8feeaeac8feeaeac8feeaeac8
def h43Pos : List Nat := [6,9,6,6,13,17,26,9,26,17,3,26,28,3,13,21,7,11,21,9,28,28,13,19,17,11,25,9,6,22,14,3,14,26,22,14,6,9,7,3,6,6,3,19,7,21,17,25,3,26,26,13,26,28]
def h43Neg : List Nat := [4,8,5,2,12,16,18,1,10,1,2,24,24,1,5,5,5,10,20,10,12,20,4,18,24,1,24,24,12,20,10,0,4,16,18,12,10,12,2,5,0,20,18,1,1,1,5,1,10,8,0,1,2,4]
def h43Mask : Nat := fullMask 54
def h43Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x9fce08fcfe6b2,0x8f8800201e284),(0xcccccccccccccccccccccccccccccccc,0x171fdff2832d4d,0x110454408a0548),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x28335d7075d01d,0x2042a93075c015),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3e802b4e7a59d2,0x300385d1a1912),(0xffff0000ffff0000ffff0000ffff0000,0x36e80625b49b60,0x6062da41860)]
def h43Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,1,4),(1,1,4),(3,1,4),(1,2,3),(3,2,3),(3,2,4),(1,2,5),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(1,3,5),(2,3,5),(1,1,31),(0,3,6),(2,3,6),(0,3,9),(0,3,37),(0,4,37),(0,6,9),(1,6,37),(0,9,37),(2,1,31),(3,1,31),(3,1,44),(0,9,44),(2,6,31),(0,9,31),(2,9,31),(1,1,38),(2,6,11),(1,0,23),(3,1,55),(0,3,55),(1,4,23),(2,4,23),(2,6,23),(1,0,31),(0,4,61),(3,0,31),(3,0,37),(0,2,37),(3,2,37),(1,2,31),(1,0,38),(1,2,7),(1,8,11),(1,8,31),(2,1,57),(1,0,47),(2,3,47),(1,0,59),(2,3,59),(2,4,40),(1,1,45),(1,2,40),(2,4,20),(1,0,80),(1,11,20),(2,3,82),(1,11,23),(1,11,31),(3,11,31),(2,4,83),(3,11,37),(0,2,53),(1,2,53),(2,2,53),(3,2,53),(0,3,17),(1,4,12),(2,4,12),(3,12,17),(2,3,18),(2,4,18),(1,12,18),(2,4,89),(2,3,16),(2,4,16),(1,1,62),(2,1,62),(1,2,62),(2,2,62),(3,4,13),(0,13,17),(1,0,108),(1,0,97),(2,13,18),(0,2,103),(3,2,103),(2,13,23),(1,0,24),(2,13,24),(1,1,74),(2,13,26),(2,3,29),(2,13,29),(1,16,62),(1,2,14),(3,14,17),(1,14,18),(1,1,63),(3,1,32),(2,17,31),(0,17,32),(3,31,32),(2,17,33),(1,18,31),(3,18,32),(1,18,33),(0,2,21),(3,2,21),(2,21,31),(1,26,31),(1,4,22),(1,23,34),(0,4,27),(1,0,28),(2,4,28),(1,0,142),(1,31,126),(3,31,126),(1,1,145)]
def h43W : BT Decor := buildWiresBT 8 h43Base h43Steps
def h43AutoList : List (List (Nat × Nat)) := [[],[(3,4)]]
def h43Autos : BT (List (Nat × Nat)) := btOfList 1 h43AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Pairs : goodPairs h43G h43Pos h43Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43BaseOk : ∀ x ∈ h43Base, faithful h43Pos h43Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43WOk : btAll (fun x => faithful h43Pos h43Neg x ∧ x.1 < 2^128) h43W := buildWiresBT_faithful h43BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h43G = h43G) h43Autos := btAll_ofList (autos_of (by decide +kernel))
def h43SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 1 0,5),some (subcubeFast 1 8,4),some (subcubeFast 1 16,4),some (subcubeFast 2 0,5),some (subcubeFast 2 4,4),some (subcubeFast 4 0,6),some (subcubeFast 8 0,4),some (subcubeFast 16 0,4)]
def h43Slices : BT (Option (Nat × Nat)) := btOfList 4 h43SliceList
def h43Specs : List PoolSpec := [(3,[]),(6,[]),(8,[(0,0,1)]),(4,[]),(5,[]),(8,[]),(0,[]),(8,[(0,0,1),(1,3,5)]),(1,[]),(8,[(0,0,1),(2,3,5)]),(9,[]),(2,[]),(8,[(1,0,1)]),(6,[(1,0,2)]),(7,[]),(0,[(1,0,1)]),(1,[(1,0,2)]),(2,[(1,0,2)]),(6,[(3,0,2)]),(1,[(3,0,2)]),(2,[(3,0,2)]),(1,[(1,0,1)]),(10,[]),(8,[(1,0,1),(0,3,6)]),(8,[(2,0,1)]),(0,[(2,0,1)]),(2,[(1,0,1)]),(6,[(1,2,7)]),(8,[(3,0,1)]),(1,[(1,0,23)]),(8,[(3,1,3)]),(2,[(1,0,2),(1,0,31)]),(0,[(3,1,3)]),(3,[(0,3,4)]),(8,[(0,3,4)]),(1,[(1,0,2),(1,0,31)]),(8,[(0,3,9)]),(8,[(0,1,3)]),(8,[(0,0,3)]),(1,[(1,4,12)]),(8,[(0,0,3),(1,4,12)]),(8,[(0,0,3),(2,4,12)]),(1,[(2,4,12)]),(8,[(1,0,3)]),(2,[(1,0,31)]),(2,[(1,0,3)]),(3,[(3,4,13)]),(8,[(1,0,3),(3,4,13)]),(8,[(2,0,3)]),(8,[(3,0,3)]),(2,[(3,0,3)]),(1,[(3,0,31)]),(2,[(3,0,31)]),(8,[(0,3,17)]),(6,[(0,3,17)]),(8,[(2,3,18)]),(8,[(1,1,3)]),(8,[(1,1,4)]),(8,[(3,1,4)]),(6,[(3,2,21)]),(0,[(1,1,3)]),(8,[(2,1,3)]),(8,[(2,1,3),(1,4,22)]),(3,[(3,3,4)]),(8,[(3,1,3),(2,4,23)]),(8,[(0,4,27)]),(8,[(1,0,28)]),(8,[(2,4,28)]),(1,[(1,0,31)]),(8,[(0,3,4),(1,3,4)]),(8,[(1,3,4),(0,3,4)]),(8,[(1,3,4)]),(8,[(2,3,4)])]
def h43Pools : BT (Option BoundPool) := buildPoolsBT 7 h43W h43R h43Slices h43Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Slice10 : Slice h43R h43G (subcubeFast 16 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Slice9 : Slice h43R h43G (subcubeFast 8 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Slice8 : Slice h43R h43G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Slice7 : Slice h43R h43G (subcubeFast 2 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Slice6 : Slice h43R h43G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Slice5 : Slice h43R h43G (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Slice4 : Slice h43R h43G (subcubeFast 1 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Slice3 : Slice h43R h43G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Slice2 : Slice h43R h43G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Slice1 : Slice h43R h43G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Slice0 : Slice h43R h43G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h43R h43G p.1 p.2) h43Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h43R h43G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h43Slice0) (forall_cons (fun _ h => by cases h; exact h43Slice1) (forall_cons (fun _ h => by cases h; exact h43Slice2) (forall_cons (fun _ h => by cases h; exact h43Slice3) (forall_cons (fun _ h => by cases h; exact h43Slice4) (forall_cons (fun _ h => by cases h; exact h43Slice5) (forall_cons (fun _ h => by cases h; exact h43Slice6) (forall_cons (fun _ h => by cases h; exact h43Slice7) (forall_cons (fun _ h => by cases h; exact h43Slice8) (forall_cons (fun _ h => by cases h; exact h43Slice9) (forall_cons (fun _ h => by cases h; exact h43Slice10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h43R h43G c) h43Pools := buildPoolsBT_sound h43SlicesOk
def h43Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h43G (3 - 1) xs.toFinset) h43Empty := trivial
def h43Block3_0 : List NodeSpec := nodesWithIdentity [([1,3,49,62],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test3_0 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Empty 3 h43Block3_0 = true := by decide +kernel
def h43Nodes3 : List NodeSpec := h43Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Check3 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Empty 3 h43Nodes3 = true := h43Test3_0
def h43Bucket3 : BT (List (List Nat)) := buildBucketsBT h43W h43Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h43G 3 xs.toFinset) h43Bucket3 := buildBucketsBT_sound (by decide) h43Pairs h43WOk h43PoolsOk h43AutosOk h43EmptyOk h43Check3
def h43Block4_0 : List NodeSpec := nodesWithIdentity [([3,4,6,9,37],[]),([1,3,4,9,44],[5]),([1,3,4,9,50],[]),([1,4,9,23,61],[31]),([1,3,4,9,73],[]),([1,3,4,9,48],[]),([1,4,9,40,61],[31]),([0,1,3,4,45],[5]),([0,3,4,9,78],[]),([0,1,3,11,87],[]),([0,1,3,4,88],[]),([2,3,4,43,53],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test4_0 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket3 4 h43Block4_0 = true := by decide +kernel
def h43Block4_1 : List NodeSpec := nodesWithIdentity [([0,2,3,53,100],[]),([0,2,3,53,102],[]),([0,1,2,62,97],[]),([0,2,23,62,103],[]),([0,2,23,62,104],[]),([2,3,4,43,56],[]),([1,2,3,43,62],[]),([0,1,2,62,101],[]),([0,1,2,3,121],[]),([0,1,3,62,112],[]),([0,1,3,62,113],[]),([0,1,2,32,127],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test4_1 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket3 4 h43Block4_1 = true := by decide +kernel
def h43Block4_2 : List NodeSpec := nodesWithIdentity [([0,1,2,31,132],[]),([0,1,4,74,134],[]),([1,3,4,37,49],[]),([0,1,31,32,66],[]),([0,2,31,37,126],[]),([0,1,2,31,145],[]),([0,2,31,46,126],[]),([0,1,2,31,144],[]),([0,1,2,31,146],[]),([2,3,4,43,117],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test4_2 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket3 4 h43Block4_2 = true := by decide +kernel
def h43Nodes4 : List NodeSpec := h43Block4_0 ++ h43Block4_1 ++ h43Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Check4 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket3 4 h43Nodes4 = true := by
  unfold h43Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h43Test4_0,h43Test4_1⟩,h43Test4_2⟩
def h43Bucket4 : BT (List (List Nat)) := buildBucketsBT h43W h43Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h43G 4 xs.toFinset) h43Bucket4 := buildBucketsBT_sound (by decide) h43Pairs h43WOk h43PoolsOk h43AutosOk h43Bucket3Ok h43Check4
def h43Block5_0 : List NodeSpec := nodesWithIdentity [([1,3,4,6,9,31],[3,4,13]),([1,3,4,6,9,38],[0,3,13]),([1,3,4,6,9,39],[3]),([0,1,3,4,11,54],[12]),([1,2,3,4,6,55],[5]),([1,2,3,4,6,61],[1,3,4]),([0,2,3,4,6,37],[0,10,22]),([0,1,2,3,4,44],[5,6,8,11]),([0,1,2,3,4,50],[]),([0,1,3,4,11,70],[28]),([0,2,3,4,8,37],[]),([0,1,2,3,4,71],[5,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test5_0 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket4 5 h43Block5_0 = true := by decide +kernel
def h43Block5_1 : List NodeSpec := [([0,1,4,9,23,31],[13,17],[0]),([0,1,3,4,9,47],[0],[0]),([0,1,3,4,9,59],[],[0]),([1,3,4,9,61],[3,4,5,31,33,35],[0,1]),([1,3,4,9,31,61],[0,3,31,35],[0]),([0,1,3,4,9,37],[0,6],[0]),([0,1,4,9,31,40],[6,17],[0]),([0,1,3,4,9,51],[0,5,13],[0]),([0,1,3,4,9,52],[0,5],[0]),([0,1,3,4,9,77],[],[0]),([1,2,3,4,9,61],[3,5],[0]),([0,1,2,3,4,52],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test5_1 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket4 5 h43Block5_1 = true := by decide +kernel
def h43Block5_2 : List NodeSpec := nodesWithIdentity [([0,1,3,4,11,80],[]),([0,1,3,4,11,82],[37]),([0,1,4,11,23,31],[18,20]),([0,1,3,4,11,47],[]),([0,1,3,4,11,59],[]),([0,1,3,4,11,84],[]),([0,1,3,4,11,83],[20]),([0,1,3,4,11,37],[5]),([0,1,3,4,11,85],[34]),([0,1,3,4,11,86],[]),([0,2,3,4,17,53],[5,10,21]),([0,1,2,3,17,94],[10,39])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test5_2 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket4 5 h43Block5_2 = true := by decide +kernel
def h43Block5_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,17,95],[]),([0,1,2,3,4,96],[0,5]),([0,2,3,4,18,53],[]),([0,1,2,3,18,94],[]),([0,1,2,3,18,95],[]),([0,1,2,3,4,99],[0,5]),([0,2,3,4,53,89],[0,4,10,21]),([0,2,3,4,53,90],[10,21]),([0,2,3,4,53,91],[]),([0,2,3,4,53,92],[]),([0,2,3,4,16,53],[0,4,10,21]),([0,2,3,4,19,53],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test5_3 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket4 5 h43Block5_3 = true := by decide +kernel
def h43Block5_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,17,62],[]),([0,1,2,3,17,107],[]),([0,1,2,3,4,108],[]),([0,1,2,4,13,97],[]),([0,1,2,3,18,62],[8]),([0,1,2,3,18,107],[]),([0,1,2,3,4,111],[]),([0,1,2,23,62],[3,4,8,33,44]),([0,1,2,4,23,62],[4,44]),([0,1,2,4,23,114],[]),([1,2,3,4,13,115],[1]),([0,1,2,4,13,76],[22])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test5_4 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket4 5 h43Block5_4 = true := by decide +kernel
def h43Block5_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,116],[8]),([0,1,2,4,13,74],[22]),([0,1,2,3,4,118],[8]),([0,2,3,4,16,56],[8]),([0,2,3,4,19,56],[6]),([0,1,2,4,13,119],[22]),([0,1,2,3,4,120],[8]),([0,1,2,3,16,62],[8,22,33]),([0,1,2,3,19,62],[]),([0,1,2,3,62,103],[8,22,44]),([0,1,2,3,62,104],[4,8]),([0,1,2,3,62,105],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test5_5 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket4 5 h43Block5_5 = true := by decide +kernel
def h43Block5_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,62,106],[]),([0,1,2,3,4,103],[5,6,8,22]),([0,1,2,4,14,93],[6]),([0,1,2,3,4,123],[5]),([0,1,2,3,4,124],[5]),([0,1,2,3,4,125],[5,6]),([0,2,3,4,17,37],[5]),([0,1,2,17,31,32],[10]),([0,1,2,3,4,127],[]),([0,1,2,4,32,93],[10]),([0,1,2,3,4,128],[]),([0,1,2,3,4,130],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test5_6 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket4 5 h43Block5_6 = true := by decide +kernel
def h43Block5_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,109],[6,11,22]),([0,2,3,4,18,37],[5]),([0,1,2,18,31,32],[8]),([0,1,2,3,4,131],[6]),([0,1,2,3,4,132],[]),([0,1,2,3,33,98],[]),([0,1,2,3,4,133],[]),([0,1,2,3,4,110],[]),([0,1,2,3,4,81],[8]),([0,1,2,21,25,31],[1,8]),([0,1,2,4,21,41],[]),([0,1,2,3,4,37],[5,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test5_7 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket4 5 h43Block5_7 = true := by decide +kernel
def h43Block5_8 : List NodeSpec := nodesWithIdentity [([0,1,2,21,26,31],[1,8]),([0,1,2,4,21,74],[]),([0,1,2,4,31,136],[8]),([0,1,2,23,26,31],[1,8]),([0,1,2,4,23,61],[8,44]),([0,1,2,4,23,139],[8]),([0,1,2,3,4,73],[]),([0,1,2,3,4,75],[8]),([0,1,2,3,4,143],[8]),([0,1,2,3,4,48],[]),([0,1,2,3,4,64],[5,6]),([0,1,3,4,37,65],[6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test5_8 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket4 5 h43Block5_8 = true := by decide +kernel
def h43Block5_9 : List NodeSpec := nodesWithIdentity [([0,1,3,4,37,66],[5]),([0,1,3,4,31,66],[]),([0,1,2,31,32,37],[8,10,69]),([0,1,2,31,32,46],[8]),([0,1,2,31,32,67],[70]),([0,1,2,31,126],[3,8,33]),([0,1,2,31,129],[3,8,33]),([0,2,3,4,16,117],[10,11]),([0,2,3,4,19,117],[6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test5_9 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket4 5 h43Block5_9 = true := by decide +kernel
def h43Nodes5 : List NodeSpec := h43Block5_0 ++ h43Block5_1 ++ h43Block5_2 ++ h43Block5_3 ++ h43Block5_4 ++ h43Block5_5 ++ h43Block5_6 ++ h43Block5_7 ++ h43Block5_8 ++ h43Block5_9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Check5 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket4 5 h43Nodes5 = true := by
  unfold h43Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h43Test5_0,h43Test5_1⟩,h43Test5_2⟩,h43Test5_3⟩,h43Test5_4⟩,h43Test5_5⟩,h43Test5_6⟩,h43Test5_7⟩,h43Test5_8⟩,h43Test5_9⟩
def h43Bucket5 : BT (List (List Nat)) := buildBucketsBT h43W h43Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h43G 5 xs.toFinset) h43Bucket5 := buildBucketsBT_sound (by decide) h43Pairs h43WOk h43PoolsOk h43AutosOk h43Bucket4Ok h43Check5
def h43Block6_0 : List NodeSpec := [([0,1,3,4,30],[0,1,2,3,5,6],[0]),([0,1,2,4,35],[0,1,4,7,8],[0]),([0,1,2,4,36],[0,1,3,4,9,10],[0]),([1,3,4,6,9],[0,3,4,5,12,13,14,15],[0,1]),([0,1,3,4,6,9],[0,3,4,5,6,12,13,14,16,17],[0]),([0,1,3,4,6,11],[0,3,4,5,6,12,14,18,19,20],[0]),([0,1,2,3,4,6,23],[0,8,10,14,21],[0]),([0,1,2,3,4,6,31],[0,1,3,4,8,10,11,22],[0]),([0,1,2,3,4,38],[0,1,3,5,6,10,11,21,22,23],[0]),([0,1,2,3,4,6,38],[0,1,3,8,10],[0]),([0,1,2,3,4,39],[3,5,6,10,11,21,22],[0]),([0,1,2,3,4,6,39],[3,8,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test6_0 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket5 6 h43Block6_0 = true := by decide +kernel
def h43Block6_1 : List NodeSpec := [([1,3,4,7,9],[0,3,4,13,14,25],[0]),([0,1,2,3,4,6],[0,1,5,6,8,10,11,12,14,21,22,26],[0]),([0,1,3,4,69],[0,3,4,5,6,24,27],[0]),([0,1,3,4,8,11],[0,3,4,5,18,19,20,28],[0]),([0,1,2,3,4,8,31],[1,3,4,8,10,11,22],[0]),([0,1,2,3,4,57],[0,1,3,5,6,10,11,22,29],[0]),([0,1,3,4,9,23],[0,3,6,13,14,16,17,30,32],[0]),([0,1,3,4,9,31],[0,3,4,6,13,16,17,33,34],[0,1]),([0,1,3,4,9,40],[0,3,5,6,13,14,16,17,36],[0]),([0,1,2,3,4,9,31],[0,3,5,6,8,10,11,22,34],[0]),([0,1,2,3,4,40],[0,1,3,5,6,10,11,14,22,36],[0]),([0,1,3,4,9],[0,3,4,5,6,13,14,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test6_1 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket5 6 h43Block6_1 = true := by decide +kernel
def h43Block6_2 : List NodeSpec := [([0,1,3,4,11,20],[0,3,5,18,19,20,37],[0]),([0,1,3,4,11,23],[0,3,5,18,19,20,30],[0]),([0,1,3,4,11,31],[0,3,4,5,18,19,20,33,34],[0,1]),([0,1,2,3,4,12,17],[0,1,5,6,8,10],[0]),([0,1,2,3,4,12,18],[0,1,5,6],[0]),([0,2,3,4,53],[0,3,4,10,21],[0]),([0,1,2,3,4,53],[0,1,3,4,5,6,10,11,21,22],[0]),([0,2,3,4,72],[0,1,4,10,29],[0]),([0,1,3,4,79],[0,4,5,6,10,16,36],[0]),([0,1,2,3,94],[0,10,11,39,40],[0]),([0,1,2,3,95],[0,4,10,22,41,42],[0]),([0,1,2,3,4,13,17],[6,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test6_2 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket5 6 h43Block6_2 = true := by decide +kernel
def h43Block6_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,13,18],[1,5,6,8]),([0,1,2,4,13,23],[0,1,3,8,10,32,45]),([0,1,2,3,4,13,24],[0,1,8,11,22]),([0,1,2,3,4,13,26],[4,8,11,22]),([0,1,2,3,4,56],[0,1,3,5,6,8,10,11,22]),([0,1,2,3,4,13,29],[6,8,11,22]),([0,1,2,3,62],[3,4,8,22,33]),([0,1,2,3,4,62],[0,1,3,4,5,6,8,10,22,33,44]),([0,1,2,3,107],[3,8,11,46,47]),([0,1,2,3,4,14,17],[0,5,6,8]),([0,1,2,3,4,14,18],[0,1,5,6]),([0,1,2,3,4,60],[0,1,4,5,6,8,11,22])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test6_3 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket5 6 h43Block6_3 = true := by decide +kernel
def h43Block6_4 : List NodeSpec := [([0,1,3,4,122],[0,4,5,6,8,48],[0]),([0,1,2,3,4,15,17],[3,6,10],[0]),([0,1,2,3,4,15,18],[1,3,5,6,8,10],[0]),([0,1,2,4,15,23],[0,1,3,8,10,32,50],[0]),([0,1,2,3,4,15,24],[1,3,8,10],[0]),([0,1,2,3,4,15,26],[3,4,8,10,11,22],[0]),([0,1,2,3,4,15,29],[3,6,8,10],[0]),([0,1,2,3,4,63],[1,3,4,5,6,10,22,33,51,52],[0]),([0,1,2,3,4,70],[0,1,5,6,8,10,11,14,18,22,28],[0]),([0,1,2,3,4,17,31],[1,5,6,10],[0]),([0,1,2,3,4,17,32],[6,8,11],[0,1]),([0,1,2,3,4,17,33],[6,8,10,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test6_4 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket5 6 h43Block6_4 = true := by decide +kernel
def h43Block6_5 : List NodeSpec := [([0,1,2,3,4,93],[0,1,5,6,10,11,14,22,53,54],[0]),([0,1,2,3,4,54],[0,1,5,6,8,10,11,12,22],[0]),([0,1,2,3,4,18,31],[1,5,6,8,10,11,22],[0]),([0,1,2,3,4,18,32],[1,5,6,8],[0]),([0,1,2,3,4,18,33],[1,5,6,11],[0]),([0,1,2,3,4,97],[0,1,5,6,10,11,22,55],[0,1]),([0,1,2,3,4,68],[0,1,3,5,6,10,11,14,21,22],[0,1]),([0,1,2,3,4,23],[0,1,3,5,6,8,10,11,22,30],[0]),([0,1,2,3,4,80],[0,1,5,6,8,10,14,22],[0,1]),([0,1,2,3,4,21,25],[1,8,11,14,56,57],[0,1]),([0,1,2,3,4,21,26],[8,10,11,14,22,58],[0]),([0,1,3,4,135],[3,6,8,14,56,59],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test6_5 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket5 6 h43Block6_5 = true := by decide +kernel
def h43Block6_6 : List NodeSpec := [([0,1,2,4,21,31],[1,3,8,10,11,33,60],[0]),([0,1,2,3,4,42],[0,1,3,5,6,8,10,22],[0,1]),([0,1,2,3,138],[1,3,8,11,62],[0]),([0,1,2,3,137],[1,3,8,14,22],[0]),([0,1,2,3,4,137],[0,1,3,5,6,8,14,22],[0]),([0,1,2,3,4,55],[0,1,3,5,6,8,10,11,22,29],[0]),([0,1,2,3,4,23,55],[0,1,8,10,29],[0]),([0,1,2,3,4,23,26],[8,10,11,22],[0]),([0,1,2,4,23,31],[1,3,8,10,11,32,33],[0,1]),([0,1,2,4,23,34],[1,3,8,10,11,32,63],[0]),([0,1,2,3,4,47],[0,5,6,10,22],[0]),([0,1,2,3,4,23,58],[1,8,10,11,22],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test6_6 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket5 6 h43Block6_6 = true := by decide +kernel
def h43Block6_7 : List NodeSpec := [([0,1,2,3,4,59],[0,1,5,6,8,10,22,64],[0,1]),([0,1,2,3,4,23,59],[1,8,10,11],[0]),([0,1,2,3,4,140],[0,1,3,5,6,8,14,22,65],[0]),([0,1,2,3,4,141],[0,1,3,5,6,10,11,14,22,66],[0]),([0,1,2,3,4,142],[0,1,5,6,8,10,14,22,67],[0,1]),([0,1,2,3,4,61],[0,1,3,4,5,6,8,10,11,22,33,44,68],[0,1]),([0,1,2,3,4,31,61],[0,3,8,10,11,22,33,44,68],[0]),([0,1,2,3,4,37],[0,1,5,6,8,10,11,22],[0]),([0,1,2,3,4,31,37],[1,8,10,11,22,34],[0]),([0,1,2,3,4,31,46],[1,8,10,11,22],[0]),([0,1,2,3,4,31,67],[5,6,34],[0]),([0,1,2,31,32],[3,8,10,33,69],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test6_7 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket5 6 h43Block6_7 = true := by decide +kernel
def h43Block6_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,126],[0,1,3,5,6,8,11]),([0,1,2,3,4,117],[0,1,4,5,6,8,10,11]),([0,1,2,3,4,31],[0,1,3,5,6,8,10,11,22,33,34])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test6_8 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket5 6 h43Block6_8 = true := by decide +kernel
def h43Nodes6 : List NodeSpec := h43Block6_0 ++ h43Block6_1 ++ h43Block6_2 ++ h43Block6_3 ++ h43Block6_4 ++ h43Block6_5 ++ h43Block6_6 ++ h43Block6_7 ++ h43Block6_8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Check6 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket5 6 h43Nodes6 = true := by
  unfold h43Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h43Test6_0,h43Test6_1⟩,h43Test6_2⟩,h43Test6_3⟩,h43Test6_4⟩,h43Test6_5⟩,h43Test6_6⟩,h43Test6_7⟩,h43Test6_8⟩
def h43Bucket6 : BT (List (List Nat)) := buildBucketsBT h43W h43Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h43G 6 xs.toFinset) h43Bucket6 := buildBucketsBT_sound (by decide) h43Pairs h43WOk h43PoolsOk h43AutosOk h43Bucket5Ok h43Check6
def h43Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,8,11],[0,1]),([0,1,2,3,4,6],[0,1,3,4,5,6,8,11,12,14],[0,1]),([0,1,2,3,4,7],[0,1,3,4,5,6,8,11,14,24],[0]),([0,1,2,3,4,8],[0,1,3,4,5,6,8,11,14,28],[0,1]),([0,1,3,4,9],[0,3,4,5,6,14],[0,1]),([0,1,2,3,4,9],[0,1,3,4,5,6,8,11,14],[0,1]),([0,1,2,3,4,10],[0,1,3,4,5,8,11,14],[0]),([0,1,3,4,11],[0,3,4,5],[0,1]),([0,1,2,3,4,12],[0,1,3,4,5,6,8,10,11,38],[0]),([0,1,2,3,4,13],[0,1,3,4,5,6,8,11,43],[0]),([0,1,2,3,4,14],[0,1,4,5,6,8,11,48],[0]),([0,1,2,3,4,15],[0,1,3,4,5,6,8,10,11,49],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test7_0 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket6 7 h43Block7_0 = true := by decide +kernel
def h43Block7_1 : List NodeSpec := [([0,1,2,3,4,17],[0,1,5,6,8,11,14],[0,1]),([0,1,2,3,4,18],[0,1,5,6,8,11],[0,1]),([0,1,2,3,4,20],[0,1,3,5,6,8,10,11,14,37],[0,1]),([0,1,2,3,4,21],[0,1,3,5,6,8,11,14,56],[0]),([0,1,2,3,4,22],[0,1,3,5,6,8,11,14,61],[0]),([0,1,2,3,4,23],[0,1,3,5,6,8,10,11,14,30],[0,1]),([0,1,2,3,4,27],[0,1,3,5,6,8,11,14],[0]),([0,1,2,3,4,28],[0,1,3,5,6,8,10,11,14],[0,1]),([0,1,2,3,4,31],[0,1,3,4,5,6,8,10,11,22,34],[0,1]),([0,1,2,3,4,32],[0,1,3,5,6,8,11,71],[0]),([0,1,2,3,4,33],[0,1,3,4,5,6,8,10,11,72],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test7_1 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket6 7 h43Block7_1 = true := by decide +kernel
def h43Nodes7 : List NodeSpec := h43Block7_0 ++ h43Block7_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Check7 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket6 7 h43Nodes7 = true := by
  unfold h43Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h43Test7_0,h43Test7_1⟩
def h43Bucket7 : BT (List (List Nat)) := buildBucketsBT h43W h43Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h43G 7 xs.toFinset) h43Bucket7 := buildBucketsBT_sound (by decide) h43Pairs h43WOk h43PoolsOk h43AutosOk h43Bucket6Ok h43Check7
def h43Block8_0 : List NodeSpec := [([0,1,2,3,4],[5],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Test8_0 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket7 8 h43Block8_0 = true := by decide +kernel
def h43Nodes8 : List NodeSpec := h43Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Check8 : checkNodesBT h43W h43G h43Mask h43Pools h43Autos h43Bucket7 8 h43Nodes8 = true := h43Test8_0
def h43Bucket8 : BT (List (List Nat)) := buildBucketsBT h43W h43Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h43G 8 xs.toFinset) h43Bucket8 := buildBucketsBT_sound (by decide) h43Pairs h43WOk h43PoolsOk h43AutosOk h43Bucket7Ok h43Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bound : Lower h43R h43G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,2,6),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h43Bucket8Ok (by decide +kernel)
def h46R : List Nat := varsOf 39
def h46G : Nat := 0xfefefefeeaeaeaeafefefefeeaeaeaea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 5 := carry_of (swaps := [(3,4),(4,5)]) (roots2 := h41R) (T2 := h41G) (by decide +kernel) h41Bound
def h47R : List Nat := varsOf 47
def h47G : Nat := 0xfeeafeeaeac8eac8feeafeeaeac8eac8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h47Bound : Lower h47R h47G 9 := carry_of (swaps := [(4,5)]) (roots2 := h43R) (T2 := h43G) (by decide +kernel) h43Bound
def h48R : List Nat := varsOf 53
def h48G : Nat := 0xfffffafafafaf0f0fffffafafafaf0f0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bound : Lower h48R h48G 5 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h41R) (T2 := h41G) (by decide +kernel) h41Bound
def h49R : List Nat := varsOf 55
def h49G : Nat := 0xfefeeaeaeaeae0e0fefeeaeaeaeae0e0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bound : Lower h49R h49G 9 := carry_of (swaps := [(4,5),(3,4),(1,2)]) (roots2 := h43R) (T2 := h43G) (by decide +kernel) h43Bound
def h50R : List Nat := varsOf 58
def h50G : Nat := 0xffffffccffccff00ffffffccffccff00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bound : Lower h50R h50G 5 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h41R) (T2 := h41G) (by decide +kernel) h41Bound
def h51R : List Nat := varsOf 59
def h51G : Nat := 0xffeeeecceeccee00ffeeeecceeccee00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bound : Lower h51R h51G 9 := carry_of (swaps := [(4,5),(3,4),(1,2),(2,3),(0,1)]) (roots2 := h43R) (T2 := h43G) (by decide +kernel) h43Bound
def h52R : List Nat := varsOf 61
def h52G : Nat := 0xfffafafafafaf000fffafafafafaf000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h52Bound : Lower h52R h52G 7 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) h37Bound
def h53R : List Nat := varsOf 62
def h53G : Nat := 0xffffffccffccf000ffffffccffccf000
def h53Pos : List Nat := [12,18,14,22,12,14,24,34,18,40,34,24,22,38,40,48,48,52,52]
def h53Neg : List Nat := [8,16,10,20,4,6,8,32,2,8,2,16,6,6,32,16,32,36,20]
def h53Mask : Nat := fullMask 19
def h53Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x35ae,0x3524),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x6303d,0x63038),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x4a75,581),(0xffff0000ffff0000ffff0000ffff0000,0x7994a,0x4880a),(0xffffffff00000000ffffffff00000000,0x7e680,0x34080)]
def h53Steps : List (Nat × Nat × Nat) := [(1,3,4),(3,0,5)]
def h53W : BT Decor := buildWiresBT 3 h53Base h53Steps
def h53AutoList : List (List (Nat × Nat)) := [[],[(4,5)]]
def h53Autos : BT (List (Nat × Nat)) := btOfList 1 h53AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Pairs : goodPairs h53G h53Pos h53Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53BaseOk : ∀ x ∈ h53Base, faithful h53Pos h53Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53WOk : btAll (fun x => faithful h53Pos h53Neg x ∧ x.1 < 2^128) h53W := buildWiresBT_faithful h53BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h53G = h53G) h53Autos := btAll_ofList (autos_of (by decide +kernel))
def h53SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,4),some (subcubeFast 12 0,4),some (subcubeFast 16 0,4),some (subcubeFast 32 0,4)]
def h53Slices : BT (Option (Nat × Nat)) := btOfList 3 h53SliceList
def h53Specs : List PoolSpec := [(1,[]),(4,[]),(2,[]),(0,[]),(3,[]),(5,[]),(6,[])]
def h53Pools : BT (Option BoundPool) := buildPoolsBT 3 h53W h53R h53Slices h53Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice6 : Slice h53R h53G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice5 : Slice h53R h53G (subcubeFast 16 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice4 : Slice h53R h53G (subcubeFast 12 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice3 : Slice h53R h53G (subcubeFast 8 0) 4 := slice_fast_direct (zDead := 4) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice2 : Slice h53R h53G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice1 : Slice h53R h53G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice0 : Slice h53R h53G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h53R h53G p.1 p.2) h53Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h53R h53G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h53Slice0) (forall_cons (fun _ h => by cases h; exact h53Slice1) (forall_cons (fun _ h => by cases h; exact h53Slice2) (forall_cons (fun _ h => by cases h; exact h53Slice3) (forall_cons (fun _ h => by cases h; exact h53Slice4) (forall_cons (fun _ h => by cases h; exact h53Slice5) (forall_cons (fun _ h => by cases h; exact h53Slice6) (fun _ h => (List.not_mem_nil h).elim))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h53R h53G c) h53Pools := buildPoolsBT_sound h53SlicesOk
def h53Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G (4 - 1) xs.toFinset) h53Empty := trivial
def h53Block4_0 : List NodeSpec := nodesWithIdentity [([1,2,3,4,6],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test4_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Empty 4 h53Block4_0 = true := by decide +kernel
def h53Nodes4 : List NodeSpec := h53Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check4 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Empty 4 h53Nodes4 = true := h53Test4_0
def h53Bucket4 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 4 xs.toFinset) h53Bucket4 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53EmptyOk h53Check4
def h53Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[0,2,3,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_0 = true := by decide +kernel
def h53Nodes5 : List NodeSpec := h53Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check5 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Nodes5 = true := h53Test5_0
def h53Bucket5 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 5 xs.toFinset) h53Bucket5 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53Bucket4Ok h53Check5
def h53Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,1,2,3,4,5,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_0 = true := by decide +kernel
def h53Nodes6 : List NodeSpec := h53Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check6 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Nodes6 = true := h53Test6_0
def h53Bucket6 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 6 xs.toFinset) h53Bucket6 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53Bucket5Ok h53Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bound : Lower h53R h53G 7 := lower_of_forestBT (essPairs := [(VAR 1,16,18),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,2,18),(VAR 5,2,34)]) (by decide +kernel) h53Bucket6Ok (by decide +kernel)
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfeeaeac8eac8e000feeaeac8eac8e000
def h0Pos : List Nat := [13,14,19,19,22,14,13,14,13,27,22,35,19,38,35,23,25,35,41,22,25,38,60,49,41,13,49,60,30,58,38,41,45,46,25,29,60,60,49,53,22,54,51,38,38,54,58,58,58,53,15,14,13,15,19,23,22,53,57,19,43,27,43,14,35,38,13,49,30,41,45]
def h0Neg : List Nat := [12,12,17,18,21,10,9,6,5,26,6,34,3,6,3,21,9,33,9,18,17,34,56,33,33,21,17,28,28,26,36,40,44,44,24,28,44,52,48,52,28,52,50,44,52,50,56,50,42,21,12,4,4,7,1,7,2,37,56,2,42,11,11,44,1,2,37,1,26,1,37]
def h0Mask : Nat := fullMask 71
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x6d7ef604cd8797db4d,0x6d62e200000797d154),(0xcccccccccccccccccccccccccccccccc,0x13f9edff02702afebe,0x1279a1a40020287ea8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x5683be3bbb5a68a5f3,0x4482be1bbb5a00a593),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x74f43dc03fbb5503e3,0x10f405491fb8450263),(0xffff0000ffff0000ffff0000ffff0000,0x182fc3e7fc3cd9961c,0x100402f7ec3e58821c),(0xffffffff00000000ffffffff00000000,0x6b5603fef3ede66800,0x449601fef3c1e20800)]
def h0Steps : List (Nat × Nat × Nat) := [(1,0,1),(3,0,1),(3,0,3),(3,0,4),(0,1,3),(3,1,3),(0,1,4),(3,1,4),(0,1,5),(3,1,5),(3,2,4),(3,2,5),(0,3,4),(1,0,18),(3,0,18),(1,1,18),(2,1,18),(3,1,18),(0,3,5),(1,3,5),(3,3,5),(0,3,6),(2,3,6),(0,4,5),(1,4,5),(2,4,5),(0,4,6),(2,4,6),(0,5,6),(0,4,34),(2,4,34),(0,5,18),(2,5,18),(1,18,34),(1,1,38),(2,6,38),(2,6,18),(1,0,27),(1,0,29),(3,0,29),(1,1,29),(2,1,29),(3,1,29),(2,3,29),(1,0,32),(2,5,32),(2,6,29),(1,0,28),(1,1,28),(1,32,34),(2,6,51),(1,0,33),(1,1,33),(2,3,7),(2,4,7),(2,5,7),(2,1,8),(2,3,12),(2,4,8),(0,5,8),(2,5,8),(2,5,12),(1,12,66),(1,8,12),(2,3,13),(1,0,65),(2,5,13),(2,3,72),(1,8,13),(1,8,29),(2,3,20),(2,1,9),(2,4,10),(2,5,9),(2,5,10),(1,9,10),(2,4,11),(2,5,11),(1,14,76),(1,9,14),(1,9,15),(1,9,24),(0,30,43),(3,31,43),(3,1,44),(0,3,44),(1,10,29),(3,10,44),(0,3,92),(1,12,24),(3,12,71),(3,13,71),(1,13,24),(3,1,19),(0,5,19),(0,5,21),(2,5,22),(2,3,47),(1,1,49)]
def h0W : BT Decor := buildWiresBT 7 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[],[(4,5)]]
def h0Autos : BT (List (Nat × Nat)) := btOfList 1 h0AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Pairs : goodPairs h0G h0Pos h0Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0BaseOk : ∀ x ∈ h0Base, faithful h0Pos h0Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0WOk : btAll (fun x => faithful h0Pos h0Neg x ∧ x.1 < 2^128) h0W := buildWiresBT_faithful h0BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h0G = h0G) h0Autos := btAll_ofList (autos_of (by decide +kernel))
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,7),some (subcubeFast 0 2,7),some (subcubeFast 0 4,9),some (subcubeFast 0 5,5),some (subcubeFast 0 8,9),some (subcubeFast 0 10,5),some (subcubeFast 0 16,9),some (subcubeFast 0 24,5),some (subcubeFast 0 32,9),some (subcubeFast 0 40,5),some (subcubeFast 0 48,5),some (subcubeFast 1 0,9),some (subcubeFast 1 2,6),some (subcubeFast 1 8,5),some (subcubeFast 1 16,5),some (subcubeFast 1 24,4),some (subcubeFast 1 40,4),some (subcubeFast 1 48,4),some (subcubeFast 2 0,8),some (subcubeFast 2 1,5),some (subcubeFast 2 8,6),some (subcubeFast 2 16,5),some (subcubeFast 2 32,5),some (subcubeFast 4 0,9),some (subcubeFast 4 1,5),some (subcubeFast 4 2,5),some (subcubeFast 4 10,4),some (subcubeFast 4 16,6),some (subcubeFast 4 32,6),some (subcubeFast 8 0,7),some (subcubeFast 8 1,4),some (subcubeFast 8 4,5),some (subcubeFast 8 32,4),some (subcubeFast 12 0,5),some (subcubeFast 12 1,4),some (subcubeFast 16 0,7),some (subcubeFast 16 1,4),some (subcubeFast 16 8,4),some (subcubeFast 16 32,4),some (subcubeFast 32 0,7),some (subcubeFast 32 1,4),some (subcubeFast 32 2,4)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 6 h0SliceList
def h0Specs : List PoolSpec := [(11,[]),(18,[]),(2,[(1,0,1)]),(23,[(1,0,1)]),(4,[(1,0,1)]),(1,[]),(6,[(1,0,1)]),(8,[(1,0,1)]),(23,[]),(2,[]),(11,[(0,3,4)]),(18,[(0,3,4)]),(2,[(1,0,1),(0,3,4)]),(0,[]),(23,[(1,0,1),(0,3,4)]),(8,[(1,0,1),(0,3,4)]),(1,[(0,3,4)]),(34,[]),(23,[(0,3,4)]),(2,[(0,3,4)]),(29,[]),(4,[]),(35,[]),(6,[]),(11,[(0,3,4),(0,5,6)]),(11,[(0,5,6)]),(8,[(0,3,4),(1,0,1)]),(18,[(0,5,6)]),(8,[(0,3,4)]),(23,[(0,3,4),(1,0,1),(0,5,6)]),(23,[(1,0,1),(0,5,6)]),(2,[(1,0,1),(0,5,6)]),(4,[(1,0,1),(0,5,6)]),(6,[(1,0,1),(0,5,6)]),(39,[]),(29,[(1,0,1),(0,5,6)]),(0,[(0,3,4)]),(7,[]),(39,[(0,3,4)]),(29,[(1,0,1)]),(11,[(0,3,4),(2,5,18)]),(18,[(0,3,4),(2,5,18)]),(2,[(1,0,1),(0,3,4),(2,5,18)]),(4,[(1,0,1),(2,5,18)]),(23,[(0,3,4),(2,5,18)]),(2,[(0,3,4),(2,5,18)]),(40,[]),(4,[(2,5,18)]),(6,[(1,0,1),(2,5,18)]),(6,[(2,5,18)]),(39,[(1,0,1)]),(11,[(0,3,4),(2,5,18),(2,6,38)]),(4,[(1,0,1),(2,5,18),(2,6,38)]),(6,[(1,0,1),(2,5,18),(2,6,38)]),(8,[]),(11,[(0,3,4),(2,6,18)]),(23,[(1,0,1),(0,3,4),(2,6,18)]),(2,[(1,0,1),(0,3,4),(2,6,18)]),(4,[(1,0,1),(2,6,18)]),(6,[(1,0,1),(2,6,18)]),(18,[(0,3,4),(2,6,18)]),(8,[(1,0,1),(0,3,4),(2,6,18)]),(30,[]),(11,[(0,3,6)]),(23,[(1,0,1),(0,3,6)]),(2,[(1,0,1),(0,3,6)]),(18,[(0,3,6)]),(6,[(1,0,1),(0,3,6)]),(8,[(1,0,1),(0,3,6)]),(11,[(0,3,6),(0,4,5)]),(11,[(0,4,5)]),(18,[(0,4,5)]),(4,[(1,0,1),(0,4,5)]),(1,[(0,4,5)]),(4,[(0,4,5)]),(23,[(1,0,1),(0,3,6),(0,4,5)]),(23,[(0,4,5)]),(2,[(0,4,5)]),(0,[(0,4,5)]),(29,[(0,4,5)]),(5,[]),(10,[]),(11,[(0,4,5),(0,4,6)]),(29,[(1,0,1),(0,4,6)]),(11,[(0,5,6),(0,4,34)]),(20,[]),(4,[(1,0,1),(0,4,5),(2,6,29)]),(11,[(0,4,5),(2,6,29)]),(35,[(1,0,1)]),(11,[(0,3,6),(0,4,6)]),(18,[(0,3,6),(0,4,6)]),(2,[(1,0,1),(0,3,6),(0,4,6)]),(11,[(0,4,6)]),(4,[(1,0,1),(0,4,6)]),(18,[(0,4,6)]),(23,[(1,0,1),(0,3,6),(0,4,6)]),(23,[(1,0,1),(0,4,6)]),(2,[(1,0,1),(0,4,6)]),(8,[(1,0,1),(0,4,6)]),(11,[(0,4,6),(2,5,32)]),(11,[(2,3,6)]),(23,[(1,0,1),(2,3,6)]),(2,[(1,0,1),(2,3,6)]),(18,[(2,3,6)]),(6,[(1,0,1),(2,3,6)]),(8,[(1,0,1),(2,3,6)]),(36,[]),(2,[(1,0,1),(0,4,5)]),(23,[(1,0,1),(0,4,5)]),(17,[]),(18,[(0,4,5),(0,4,6)]),(2,[(1,0,1),(0,4,5),(0,4,6)]),(4,[(1,0,1),(0,4,5),(0,4,6)]),(23,[(0,4,5),(1,0,1),(0,4,6)]),(2,[(0,4,5),(1,0,1),(0,4,6)]),(4,[(0,4,5),(1,0,1),(0,4,6)]),(35,[(1,0,1),(0,5,6)]),(23,[(1,0,1),(0,4,6),(0,5,6)]),(18,[(0,5,6),(0,4,34)]),(2,[(1,0,1),(0,5,6),(0,4,34)]),(4,[(1,0,1),(0,5,6),(0,4,34)]),(23,[(1,0,1),(0,5,6),(0,4,34)]),(0,[(0,4,34)]),(8,[(1,0,1),(0,4,34)]),(23,[(1,0,1),(0,4,5),(2,6,29)]),(2,[(1,0,1),(0,4,5),(2,6,29)]),(18,[(0,4,5),(2,6,29)]),(6,[(1,0,1),(2,6,29)]),(8,[(1,0,1),(2,6,29)]),(11,[(0,4,6),(0,5,6)]),(18,[(0,4,6),(2,5,32)]),(2,[(1,0,1),(0,4,6),(2,5,32)]),(4,[(1,0,1),(0,4,6),(2,5,32)]),(23,[(1,0,1),(0,4,6),(2,5,32)]),(0,[(2,5,32)]),(6,[(1,0,1),(2,5,32)]),(11,[(2,4,6)]),(23,[(1,0,1),(2,4,6)]),(2,[(1,0,1),(2,4,6)]),(18,[(2,4,6)]),(4,[(1,0,1),(2,4,6)]),(8,[(1,0,1),(2,4,6)]),(23,[(3,0,1)]),(2,[(3,0,1)]),(4,[(3,0,1)]),(6,[(3,0,1)]),(8,[(3,0,1)]),(23,[(3,0,1),(0,3,4)]),(2,[(3,0,1),(0,3,4)]),(8,[(3,0,1),(0,3,4)]),(12,[]),(11,[(0,3,4),(2,5,7)]),(11,[(2,5,7)]),(8,[(0,3,4),(3,0,1)]),(1,[(2,5,7)]),(23,[(3,0,1),(2,5,7)]),(2,[(3,0,1),(2,5,7)]),(4,[(3,0,1),(2,5,7)]),(6,[(3,0,1),(2,5,7)]),(22,[]),(29,[(3,0,1)]),(4,[(3,0,1),(2,5,18)]),(6,[(3,0,1),(2,5,18)]),(39,[(3,0,1)]),(11,[(2,3,7)]),(23,[(3,0,1),(2,3,7)]),(2,[(3,0,1),(2,3,7)]),(6,[(3,0,1),(2,3,7)]),(8,[(3,0,1),(2,3,7)]),(11,[(0,4,5),(2,3,7)]),(4,[(0,4,5),(3,0,1)]),(1,[(2,3,7)]),(20,[(0,4,5)]),(23,[(3,0,1),(0,4,5)]),(2,[(3,0,1),(0,4,5)]),(4,[(3,0,1),(0,4,5)]),(35,[(3,0,1)]),(11,[(2,4,7)]),(23,[(3,0,1),(2,4,7)]),(2,[(3,0,1),(2,4,7)]),(4,[(3,0,1),(2,4,7)]),(8,[(3,0,1),(2,4,7)]),(23,[(3,0,3)]),(2,[(3,0,3)]),(11,[(0,1,4)]),(4,[(0,1,4)]),(18,[(3,0,3)]),(23,[(3,0,3),(0,1,4)]),(2,[(3,0,3),(0,1,4)]),(6,[(3,0,3)]),(8,[(3,0,3),(0,1,4)]),(23,[(0,1,4)]),(2,[(0,1,4)]),(19,[]),(0,[(0,1,4)]),(8,[(0,1,4)]),(11,[(0,1,4),(2,5,8)]),(11,[(2,5,8)]),(18,[(3,0,3),(2,5,8)]),(6,[(3,0,3),(2,5,8)]),(23,[(3,0,3),(2,5,8)]),(2,[(3,0,3),(2,5,8)]),(4,[(0,1,4),(2,5,8)]),(4,[(2,5,8)]),(8,[(3,0,3)]),(11,[(0,1,4),(2,5,8),(1,12,66)]),(6,[(3,0,3),(2,5,8),(1,12,66)]),(4,[(0,1,4),(2,5,8),(1,12,66)]),(32,[]),(39,[(0,1,4)]),(11,[(0,1,4),(2,5,12)]),(4,[(0,1,4),(2,5,12)]),(1,[(2,5,12)]),(2,[(3,0,3),(0,1,4),(2,5,12)]),(23,[(0,1,4),(2,5,12)]),(2,[(0,1,4),(2,5,12)]),(6,[(3,0,3),(2,5,12)]),(6,[(2,5,12)]),(1,[(3,0,3)]),(35,[(3,0,3)]),(0,[(0,1,4),(2,5,12)]),(13,[]),(39,[(3,0,3)]),(11,[(0,1,4),(1,8,12)]),(23,[(3,0,3),(0,1,4),(1,8,12)]),(2,[(3,0,3),(0,1,4),(1,8,12)]),(4,[(0,1,4),(1,8,12)]),(6,[(3,0,3),(1,8,12)]),(8,[(3,0,3),(0,1,4),(1,8,12)]),(11,[(3,1,4)]),(4,[(3,1,4)]),(23,[(3,0,3),(3,1,4)]),(2,[(3,0,3),(3,1,4)]),(8,[(3,0,3),(3,1,4)]),(0,[(3,1,4)]),(23,[(3,1,4)]),(2,[(3,1,4)]),(11,[(0,5,8)]),(18,[(3,0,3),(0,5,8)]),(6,[(3,0,3),(0,5,8)]),(23,[(3,0,3),(0,5,8)]),(2,[(3,0,3),(0,5,8)]),(4,[(0,5,8)]),(29,[(3,1,4)]),(39,[(3,1,4)]),(21,[]),(12,[(0,5,8)]),(8,[(3,1,4)]),(11,[(3,1,4),(2,5,8)]),(4,[(3,1,4),(2,5,8)]),(41,[]),(12,[(2,5,8)]),(15,[]),(11,[(3,1,4),(2,5,13)]),(4,[(3,1,4),(2,5,13)]),(18,[(2,5,13)]),(23,[(3,1,4),(2,5,13)]),(2,[(3,1,4),(2,5,13)]),(6,[(3,0,3),(2,5,13)]),(6,[(2,5,13)]),(11,[(3,1,4),(1,8,13)]),(23,[(3,0,3),(3,1,4),(1,8,13)]),(2,[(3,0,3),(3,1,4),(1,8,13)]),(4,[(3,1,4),(1,8,13)]),(6,[(3,0,3),(1,8,13)]),(18,[(3,0,3),(1,8,13)]),(8,[(3,0,3),(3,1,4),(1,8,13)]),(11,[(2,3,6),(1,1,28)]),(4,[(1,0,1),(1,1,28)]),(25,[]),(2,[(1,0,1),(2,3,6),(1,1,28)]),(0,[(3,2,4)]),(11,[(3,2,4)]),(4,[(3,2,4)]),(29,[(3,2,4)]),(1,[(3,2,4)]),(23,[(1,0,1),(2,3,6),(1,1,28)]),(6,[(1,0,1),(2,3,6),(1,1,28)]),(8,[(1,0,1),(2,3,6),(1,1,28)]),(39,[(3,2,4)]),(8,[(3,2,4)]),(27,[]),(16,[]),(24,[]),(3,[]),(11,[(2,1,8)]),(4,[(2,1,8)]),(23,[(3,0,3),(2,1,8)]),(2,[(3,0,3),(2,1,8)]),(6,[(3,0,3),(2,1,8)]),(8,[(3,0,3),(2,1,8)]),(23,[(3,0,3),(0,4,5)]),(2,[(3,0,3),(0,4,5)]),(11,[(0,4,5),(1,8,29)]),(23,[(3,0,3),(0,4,5),(1,8,29)]),(2,[(3,0,3),(0,4,5),(1,8,29)]),(4,[(0,4,5),(1,8,29)]),(6,[(3,0,3),(1,8,29)]),(8,[(3,0,3),(1,8,29)]),(23,[(0,3,4),(3,0,18)]),(2,[(0,3,4),(3,0,18)]),(4,[(3,0,18)]),(6,[(3,0,18)]),(8,[(0,3,4),(3,0,18)]),(11,[(2,4,8)]),(23,[(3,0,3),(2,4,8)]),(2,[(3,0,3),(2,4,8)]),(4,[(2,4,8)]),(8,[(3,0,3),(2,4,8)]),(23,[(3,0,4)]),(2,[(3,0,4)]),(11,[(0,1,3)]),(6,[(0,1,3)]),(18,[(3,0,4)]),(23,[(3,0,4),(0,1,3)]),(2,[(3,0,4),(0,1,3)]),(4,[(3,0,4)]),(8,[(3,0,4),(0,1,3)]),(23,[(0,1,3)]),(2,[(0,1,3)]),(0,[(0,1,3)]),(8,[(0,1,3)]),(11,[(0,1,3),(2,5,9)]),(11,[(2,5,9)]),(18,[(3,0,4),(2,5,9)]),(4,[(3,0,4),(2,5,9)]),(23,[(3,0,4),(2,5,9)]),(2,[(3,0,4),(2,5,9)]),(6,[(0,1,3),(2,5,9)]),(6,[(2,5,9)]),(8,[(3,0,4)]),(38,[]),(39,[(0,1,3)]),(11,[(0,1,3),(2,5,10)]),(6,[(0,1,3),(2,5,10)]),(1,[(2,5,10)]),(2,[(3,0,4),(0,1,3),(2,5,10)]),(23,[(0,1,3),(2,5,10)]),(2,[(0,1,3),(2,5,10)]),(4,[(3,0,4),(2,5,10)]),(4,[(2,5,10)]),(1,[(3,0,4)]),(29,[(3,0,4)]),(14,[]),(39,[(3,0,4)]),(11,[(0,1,3),(1,9,10)]),(23,[(3,0,4),(0,1,3),(1,9,10)]),(2,[(3,0,4),(0,1,3),(1,9,10)]),(4,[(3,0,4),(1,9,10)]),(6,[(0,1,3),(1,9,10)]),(8,[(3,0,4),(0,1,3),(1,9,10)]),(11,[(3,1,3)]),(6,[(3,1,3)]),(23,[(3,0,4),(3,1,3)]),(2,[(3,0,4),(3,1,3)]),(8,[(3,0,4),(3,1,3)]),(0,[(3,1,3)]),(23,[(3,1,3)]),(2,[(3,1,3)]),(8,[(3,1,3)]),(11,[(3,1,3),(2,5,9)]),(39,[(3,1,3)]),(6,[(3,1,3),(2,5,9)]),(12,[(2,5,9)]),(11,[(3,1,3),(2,5,11)]),(6,[(3,1,3),(2,5,11)]),(18,[(2,5,11)]),(23,[(3,1,3),(2,5,11)]),(2,[(3,1,3),(2,5,11)]),(4,[(3,0,4),(2,5,11)]),(4,[(2,5,11)]),(11,[(0,1,5)]),(6,[(0,1,5)]),(23,[(3,0,4),(0,1,5)]),(2,[(3,0,4),(0,1,5)]),(4,[(3,0,4),(0,1,5)]),(23,[(0,1,5)]),(2,[(0,1,5)]),(0,[(0,1,5)]),(4,[(0,1,5)]),(4,[(0,1,5),(3,0,18)]),(11,[(0,3,4),(2,3,20)]),(20,[(3,0,18)]),(8,[(0,3,4),(3,0,18),(2,3,20)]),(23,[(0,3,4),(3,0,18),(2,3,20)]),(2,[(0,3,4),(3,0,18),(2,3,20)]),(29,[(0,1,5)]),(6,[(3,0,18),(2,3,20)]),(4,[(0,1,5),(3,0,18),(1,14,76)]),(0,[(0,1,5),(1,14,76)]),(37,[]),(11,[(0,1,5),(1,9,14)]),(23,[(3,0,4),(0,1,5),(1,9,14)]),(2,[(3,0,4),(0,1,5),(1,9,14)]),(4,[(3,0,4),(0,1,5),(1,9,14)]),(6,[(0,1,5),(1,9,14)]),(8,[(3,0,4),(1,9,14)]),(11,[(3,1,5)]),(6,[(3,1,5)]),(23,[(3,0,4),(3,1,5)]),(2,[(3,0,4),(3,1,5)]),(4,[(3,0,4),(3,1,5)]),(0,[(3,1,5)]),(23,[(3,1,5)]),(2,[(3,1,5)]),(4,[(3,1,5)]),(4,[(3,1,5),(3,0,18)]),(29,[(3,1,5)]),(11,[(3,1,5),(1,9,15)]),(23,[(3,0,4),(3,1,5),(1,9,15)]),(2,[(3,0,4),(3,1,5),(1,9,15)]),(18,[(3,0,4),(1,9,15)]),(4,[(3,0,4),(3,1,5),(1,9,15)]),(6,[(3,1,5),(1,9,15)]),(8,[(3,0,4),(1,9,15)]),(11,[(2,4,6),(1,1,33)]),(6,[(1,0,1),(1,1,33)]),(26,[]),(2,[(1,0,1),(2,4,6),(1,1,33)]),(0,[(3,2,5)]),(11,[(3,2,5)]),(6,[(3,2,5)]),(35,[(3,2,5)]),(1,[(3,2,5)]),(23,[(1,0,1),(2,4,6),(1,1,33)]),(8,[(1,0,1),(2,4,6),(1,1,33)]),(4,[(1,0,1),(2,4,6),(1,1,33)]),(29,[(3,2,5)]),(4,[(3,2,5)]),(28,[]),(0,[(0,3,5)]),(11,[(0,3,5)]),(6,[(0,3,5)]),(35,[(0,3,5)]),(1,[(0,3,5)]),(23,[(0,3,5)]),(2,[(0,3,5)]),(9,[]),(11,[(2,1,9)]),(6,[(2,1,9)]),(23,[(3,0,4),(2,1,9)]),(2,[(3,0,4),(2,1,9)]),(4,[(3,0,4),(2,1,9)]),(8,[(3,0,4),(2,1,9)]),(23,[(3,0,4),(0,3,5)]),(2,[(3,0,4),(0,3,5)]),(18,[(0,3,5)]),(11,[(0,3,5),(1,9,24)]),(23,[(3,0,4),(0,3,5),(1,9,24)]),(2,[(3,0,4),(0,3,5),(1,9,24)]),(4,[(3,0,4),(1,9,24)]),(6,[(0,3,5),(1,9,24)]),(8,[(3,0,4),(1,9,24)]),(33,[]),(31,[]),(23,[(0,4,5),(3,0,29)]),(2,[(0,4,5),(3,0,29)]),(4,[(0,4,5),(3,0,29)]),(6,[(3,0,29)]),(8,[(3,0,29)]),(11,[(0,4,5),(0,3,6)]),(4,[(0,4,5),(1,0,1)]),(1,[(1,0,27)]),(23,[(1,0,1),(0,3,6),(1,0,27)]),(2,[(1,0,1),(0,3,6),(1,0,27)]),(11,[(0,4,5),(1,4,5),(0,3,6)]),(18,[(0,4,5),(1,4,5)]),(0,[(0,4,5),(1,4,5)]),(4,[(0,4,5),(1,4,5),(1,0,1)]),(6,[(1,0,1),(0,3,6),(1,0,27)]),(4,[(0,4,5),(1,4,5)]),(11,[(0,4,5),(1,4,5)]),(23,[(0,4,5),(1,4,5)]),(2,[(0,4,5),(1,4,5)]),(29,[(0,4,5),(1,4,5)]),(8,[(1,0,1),(0,3,6),(1,0,27)]),(11,[(1,4,5),(0,3,6)]),(18,[(1,4,5)]),(0,[(1,4,5)]),(4,[(1,4,5),(1,0,1)]),(4,[(1,4,5)]),(11,[(1,4,5)]),(23,[(1,4,5)]),(2,[(1,4,5)]),(29,[(1,4,5)]),(11,[(1,4,5),(0,3,6),(0,30,43)]),(4,[(1,4,5),(1,0,1),(0,30,43)]),(11,[(2,4,5),(0,3,6)]),(18,[(2,4,5)]),(0,[(2,4,5)]),(4,[(2,4,5),(1,0,1)]),(4,[(2,4,5)]),(11,[(2,4,5)]),(23,[(2,4,5)]),(2,[(2,4,5)]),(29,[(2,4,5)]),(11,[(0,1,3),(0,4,5)]),(2,[(0,1,3),(0,4,5)]),(23,[(0,1,3),(0,4,5)]),(6,[(0,1,3),(1,0,29)]),(18,[(0,4,5),(1,0,29)]),(6,[(0,1,3),(1,0,29),(3,10,44)]),(35,[(0,1,3)]),(11,[(0,1,3),(0,4,5),(1,10,29)]),(2,[(0,1,3),(0,4,5),(1,10,29)]),(23,[(0,1,3),(0,4,5),(1,10,29)]),(4,[(0,4,5),(1,10,29)]),(6,[(0,1,3),(1,10,29)]),(8,[(0,1,3),(1,10,29)]),(11,[(0,1,3),(2,4,10)]),(2,[(0,1,3),(2,4,10)]),(23,[(0,1,3),(2,4,10)]),(4,[(2,4,10)]),(8,[(0,1,3),(2,4,10)]),(4,[(1,0,1),(1,0,28)]),(11,[(0,4,5),(2,3,6)]),(4,[(0,4,5),(1,0,1),(1,0,28)]),(18,[(2,3,6),(1,0,28)]),(23,[(1,0,1),(2,3,6),(1,0,28)]),(2,[(1,0,1),(2,3,6),(1,0,28)]),(6,[(1,0,1),(2,3,6),(1,0,28)]),(11,[(0,4,5),(1,4,5),(2,3,6)]),(12,[(0,4,5),(1,4,5)]),(20,[(0,4,5),(1,4,5)]),(8,[(1,0,1),(2,3,6),(1,0,28)]),(12,[(0,4,5)]),(11,[(1,4,5),(2,3,6)]),(4,[(1,4,5),(1,0,1),(1,0,28)]),(12,[(1,4,5)]),(11,[(2,4,5),(2,3,6)]),(4,[(2,4,5),(1,0,1),(1,0,28)]),(12,[(2,4,5)]),(11,[(3,1,3),(0,4,5)]),(2,[(3,1,3),(0,4,5)]),(23,[(3,1,3),(0,4,5)]),(6,[(3,1,3),(1,0,29)]),(35,[(3,1,3)]),(11,[(0,3,4),(3,1,18)]),(2,[(0,3,4),(3,1,18)]),(23,[(0,3,4),(3,1,18)]),(4,[(3,1,18)]),(6,[(3,1,18)]),(8,[(0,3,4),(3,1,18)]),(11,[(3,1,3),(2,4,11)]),(18,[(2,4,11)]),(2,[(3,1,3),(2,4,11)]),(23,[(3,1,3),(2,4,11)]),(4,[(2,4,11)]),(8,[(3,1,3),(2,4,11)]),(11,[(0,1,4),(0,3,5)]),(2,[(0,1,4),(0,3,5)]),(23,[(0,1,4),(0,3,5)]),(11,[(0,1,4),(0,5,8)]),(4,[(0,5,8),(1,0,65)]),(8,[(3,0,3),(1,0,65)]),(29,[(0,1,4)]),(11,[(0,1,4),(0,3,5),(1,12,24)]),(2,[(0,1,4),(0,3,5),(1,12,24)]),(23,[(0,1,4),(0,3,5),(1,12,24)]),(4,[(0,1,4),(1,12,24)]),(6,[(0,3,5),(1,12,24)]),(8,[(0,1,4),(1,12,24)]),(11,[(0,1,4),(2,3,12)]),(2,[(0,1,4),(2,3,12)]),(23,[(0,1,4),(2,3,12)]),(6,[(2,3,12)]),(8,[(0,1,4),(2,3,12)]),(6,[(1,0,1),(1,0,33)]),(4,[(1,0,1),(2,4,6),(1,0,33)]),(11,[(1,3,5),(2,4,6)]),(0,[(1,3,5)]),(18,[(2,4,6),(1,0,33)]),(11,[(1,3,5)]),(6,[(1,3,5)]),(23,[(1,0,1),(2,4,6),(1,0,33)]),(2,[(1,0,1),(2,4,6),(1,0,33)]),(23,[(1,3,5)]),(2,[(1,3,5)]),(8,[(1,0,1),(2,4,6),(1,0,33)]),(18,[(1,3,5)]),(12,[(1,3,5)]),(11,[(3,3,5),(2,4,6)]),(0,[(3,3,5)]),(11,[(3,3,5)]),(6,[(3,3,5)]),(23,[(3,3,5)]),(2,[(3,3,5)]),(18,[(3,3,5)]),(12,[(3,3,5)]),(11,[(3,1,4),(0,3,5)]),(2,[(3,1,4),(0,3,5)]),(23,[(3,1,4),(0,3,5)]),(12,[(0,3,5)]),(11,[(3,1,4),(0,5,8)]),(6,[(3,0,3),(0,5,8),(1,0,65)]),(23,[(3,0,3),(0,5,8),(1,0,65)]),(2,[(3,0,3),(0,5,8),(1,0,65)]),(11,[(3,1,4),(0,3,5),(1,13,24)]),(18,[(0,3,5),(1,13,24)]),(2,[(3,1,4),(0,3,5),(1,13,24)]),(23,[(3,1,4),(0,3,5),(1,13,24)]),(4,[(3,1,4),(1,13,24)]),(6,[(0,3,5),(1,13,24)]),(8,[(3,1,4),(1,13,24)]),(11,[(3,1,4),(2,3,13)]),(18,[(2,3,13)]),(2,[(3,1,4),(2,3,13)]),(23,[(3,1,4),(2,3,13)]),(6,[(2,3,13)]),(8,[(3,1,4),(2,3,13)]),(11,[(0,4,5),(3,1,29)]),(2,[(0,4,5),(3,1,29)]),(23,[(0,4,5),(3,1,29)]),(4,[(0,4,5),(3,1,29)]),(6,[(3,1,29)]),(8,[(3,1,29)]),(11,[(3,1,4),(2,5,13),(2,3,72)]),(12,[(2,3,72)]),(1,[(2,3,72)]),(18,[(2,5,13),(2,3,72)]),(6,[(2,5,13),(2,3,72)]),(23,[(3,1,4),(2,5,13),(2,3,72)]),(2,[(3,1,4),(2,5,13),(2,3,72)]),(8,[(3,1,4),(2,3,72)]),(4,[(1,0,18)]),(6,[(1,0,18)]),(23,[(0,3,4),(1,0,18)]),(2,[(0,3,4),(1,0,18)]),(8,[(0,3,4),(1,0,18)]),(11,[(0,3,4),(3,1,19)]),(23,[(0,3,4),(1,0,18),(3,1,19)]),(18,[(0,3,4),(1,0,18)]),(29,[(3,1,19)]),(2,[(0,3,4),(1,0,18),(3,1,19)]),(4,[(1,0,18),(3,1,19)]),(6,[(1,0,18),(3,1,19)]),(8,[(0,3,4),(1,0,18),(3,1,19)]),(11,[(0,3,4),(0,5,19)]),(29,[(0,5,19)]),(23,[(0,3,4),(1,0,18),(0,5,19)]),(2,[(0,3,4),(1,0,18),(0,5,19)]),(4,[(1,0,18),(0,5,19)]),(6,[(1,0,18),(0,5,19)]),(11,[(0,3,4),(1,1,18)]),(2,[(0,3,4),(1,1,18)]),(23,[(0,3,4),(1,1,18)]),(4,[(1,1,18)]),(6,[(1,1,18)]),(8,[(0,3,4),(1,1,18)]),(12,[(0,3,4)]),(11,[(0,3,4),(1,1,18),(0,5,21)]),(29,[(0,5,21)]),(18,[(0,3,4),(0,5,21)]),(4,[(1,1,18),(0,5,21)]),(23,[(0,3,4),(1,1,18),(0,5,21)]),(2,[(0,3,4),(1,1,18),(0,5,21)]),(6,[(1,1,18),(0,5,21)]),(35,[(0,5,21)]),(11,[(0,3,4),(2,1,18)]),(2,[(0,3,4),(2,1,18)]),(23,[(0,3,4),(2,1,18)]),(4,[(2,1,18)]),(6,[(2,1,18)]),(8,[(0,3,4),(2,1,18)]),(11,[(0,3,4),(2,1,18),(2,5,22)]),(29,[(2,5,22)]),(4,[(2,1,18),(2,5,22)]),(23,[(0,3,4),(2,1,18),(2,5,22)]),(2,[(0,3,4),(2,1,18),(2,5,22)]),(6,[(2,1,18),(2,5,22)]),(11,[(0,3,4),(0,5,18)]),(2,[(0,3,4),(0,5,18)]),(23,[(0,3,4),(0,5,18)]),(4,[(0,5,18)]),(6,[(0,5,18)]),(11,[(0,3,4),(2,5,18),(1,1,38)]),(29,[(1,1,38)]),(8,[(0,3,4),(1,1,38)]),(23,[(0,3,4),(2,5,18),(1,1,38)]),(2,[(0,3,4),(2,5,18),(1,1,38)]),(4,[(2,5,18),(1,1,38)]),(6,[(2,5,18),(1,1,38)]),(6,[(1,0,29)]),(8,[(1,0,29)]),(23,[(0,4,5),(1,0,29)]),(2,[(0,4,5),(1,0,29)]),(4,[(0,4,5),(1,0,29)]),(11,[(0,4,5),(3,1,44)]),(23,[(0,4,5),(1,0,29),(3,1,44)]),(35,[(3,1,44)]),(2,[(0,4,5),(1,0,29),(3,1,44)]),(4,[(0,4,5),(1,0,29),(3,1,44)]),(6,[(1,0,29),(3,1,44)]),(8,[(1,0,29),(3,1,44)]),(11,[(0,4,5),(0,3,44)]),(35,[(0,3,44)]),(23,[(0,4,5),(1,0,29),(0,3,44)]),(2,[(0,4,5),(1,0,29),(0,3,44)]),(6,[(1,0,29),(0,3,44)]),(8,[(1,0,29),(0,3,44)]),(11,[(0,4,5),(1,1,29)]),(2,[(0,4,5),(1,1,29)]),(23,[(0,4,5),(1,1,29)]),(4,[(0,4,5),(1,1,29)]),(6,[(1,1,29)]),(8,[(1,1,29)]),(18,[(0,4,5),(0,3,92)]),(4,[(0,4,5),(1,4,5),(1,10,29)]),(1,[(0,4,5),(1,4,5)]),(6,[(0,1,3),(1,10,29),(0,3,92)]),(8,[(0,1,3),(1,10,29),(0,3,92)]),(11,[(0,4,5),(2,1,29)]),(2,[(0,4,5),(2,1,29)]),(23,[(0,4,5),(2,1,29)]),(4,[(0,4,5),(2,1,29)]),(6,[(2,1,29)]),(8,[(2,1,29)]),(11,[(0,4,5),(2,1,29),(2,3,47)]),(35,[(2,3,47)]),(23,[(0,4,5),(2,1,29),(2,3,47)]),(2,[(0,4,5),(2,1,29),(2,3,47)]),(6,[(2,1,29),(2,3,47)]),(8,[(2,1,29),(2,3,47)]),(11,[(0,4,5),(2,3,29)]),(2,[(0,4,5),(2,3,29)]),(23,[(0,4,5),(2,3,29)]),(6,[(2,3,29)]),(8,[(2,3,29)]),(11,[(0,4,5),(2,3,29),(1,1,49)]),(35,[(1,1,49)]),(23,[(0,4,5),(2,3,29),(1,1,49)]),(4,[(0,4,5),(1,1,49)]),(18,[(0,4,5),(2,3,29)]),(2,[(0,4,5),(2,3,29),(1,1,49)]),(6,[(2,3,29),(1,1,49)]),(8,[(2,3,29),(1,1,49)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 10 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice41 : Slice h0R h0G (subcubeFast 32 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice40 : Slice h0R h0G (subcubeFast 32 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice39 : Slice h0R h0G (subcubeFast 32 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice38 : Slice h0R h0G (subcubeFast 16 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice37 : Slice h0R h0G (subcubeFast 16 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice36 : Slice h0R h0G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice35 : Slice h0R h0G (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 12 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 12 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 8 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 8 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 8 1) 4 := slice_fast_direct (zDead := 4) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 4 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 4 16) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 4 10) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 4 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 4 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 4 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 2 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 2 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 2 8) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 2 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 2 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 1 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 1 40) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 1 24) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 1 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 1 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 1 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 1 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 0 48) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 0 40) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 0 32) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 0 24) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 0 16) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 10) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 8) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 5) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h52Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h53Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (forall_cons (fun _ h => by cases h; exact h0Slice25) (forall_cons (fun _ h => by cases h; exact h0Slice26) (forall_cons (fun _ h => by cases h; exact h0Slice27) (forall_cons (fun _ h => by cases h; exact h0Slice28) (forall_cons (fun _ h => by cases h; exact h0Slice29) (forall_cons (fun _ h => by cases h; exact h0Slice30) (forall_cons (fun _ h => by cases h; exact h0Slice31) (forall_cons (fun _ h => by cases h; exact h0Slice32) (forall_cons (fun _ h => by cases h; exact h0Slice33) (forall_cons (fun _ h => by cases h; exact h0Slice34) (forall_cons (fun _ h => by cases h; exact h0Slice35) (forall_cons (fun _ h => by cases h; exact h0Slice36) (forall_cons (fun _ h => by cases h; exact h0Slice37) (forall_cons (fun _ h => by cases h; exact h0Slice38) (forall_cons (fun _ h => by cases h; exact h0Slice39) (forall_cons (fun _ h => by cases h; exact h0Slice40) (forall_cons (fun _ h => by cases h; exact h0Slice41) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (6 - 1) xs.toFinset) h0Empty := trivial
def h0Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,29,55],[33,81])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 6 h0Block6_0 = true := by decide +kernel
def h0Nodes6 : List NodeSpec := h0Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 6 h0Nodes6 = true := h0Test6_0
def h0Bucket6 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 6 xs.toFinset) h0Bucket6 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check6
def h0Block7_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,34,39],[7,13,20]),([0,1,2,3,4,5,41],[0,1,8,9,20,21,22,23,51,52,53,54]),([0,1,2,3,5,27,29,32],[22,68,80,82,83]),([0,1,2,3,4,5,27,35],[4,20,21,63,84,85]),([0,1,2,3,4,5,27,52],[4,20,21,85,86,87]),([0,1,2,3,4,5,27,51],[4,20,23,34,80,99]),([0,1,2,3,29,32,34],[5,6,7,13,33,62,73,98,116,117]),([0,1,2,3,5,32,34,36],[6,13,25,33,34]),([0,1,2,3,4,5,55],[0,1,8,9,13,20,21,23,33,54]),([0,1,2,3,4,5,56],[0,1,8,9,13,20,21,22,23,54,135]),([0,1,2,3,4,5,68],[0,5,8,9,13,20,21,23,54,198,205,206,207]),([0,1,2,3,4,5,84],[0,5,8,9,13,21,22,54,386,388,389])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_0 = true := by decide +kernel
def h0Block7_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,29,30,43],[22,23,81,106,245,465,466,467,468,469,470,471,472,473,474]),([0,1,2,3,4,5,88],[0,1,8,9,13,20,23,54,485,486]),([0,1,2,3,4,5,43,88],[1,23,63]),([0,1,2,3,4,5,89],[0,1,8,9,13,20,22,23]),([0,1,2,3,4,5,29,93],[0,1,22,193,501]),([0,1,2,3,29,30,53],[22,23,106,466,467,470,471,472,473,520,521,522,523]),([0,1,2,3,4,5,24,96],[0,1,20,193]),([0,1,2,3,4,5,24,97],[0,5,20,221]),([0,1,2,3,29,30,94],[23,81,466,467,470,471,472,473,474,502,707,708,709])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_1 = true := by decide +kernel
def h0Nodes7 : List NodeSpec := h0Block7_0 ++ h0Block7_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Nodes7 = true := by
  unfold h0Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h0Test7_0,h0Test7_1⟩
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket6Ok h0Check7
def h0Block8_0 : List NodeSpec := [([0,1,2,3,4,5,18,34],[5,7,10,11,13,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38],[0]),([0,1,2,3,4,5,6,38],[0,1,2,3,4,5,6,13,20,22,28,34,39,40,41,42,43,44,45,46,47,48,49,50],[0]),([0,1,2,3,4,5,42],[0,1,8,9,16,21,23,34,37,54,55,56,57,58,59,60,61],[0]),([0,1,2,3,4,5,27,29],[4,5,13,20,22,23,34,54,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81],[0]),([0,1,2,3,4,5,6,27,29],[4,5,13,39,66,67,68,70,72,74,78,80,88],[0,1]),([0,1,2,3,4,5,27,32],[4,5,6,13,17,20,21,22,23,63,64,65,66,67,68,80,85,89,90,91,92,93,94,95,96,97,98],[0]),([0,1,2,3,4,5,28,29],[4,5,13,20,22,23,34,54,72,73,76,77,78,79,81,100,101,102,103,104,105,106],[0]),([0,1,2,3,5,6,29,32],[5,6,7,13,23,62,73,78,82,88,96,98,106,110,111,112,113,114,115],[0]),([0,1,2,3,4,5,6,35],[0,1,2,3,4,33,39,50,81,84,88,106,118,119,120,121,122,123],[0]),([0,1,2,3,4,5,52],[0,1,8,9,20,21,23,54,73,81,86,87,124,125,126,127,128],[0]),([0,1,2,3,4,5,6,52],[0,1,2,3,4,6,7,22,39,78,86,87,88,124,125,126,127,128],[0]),([0,1,2,3,4,5,32,34],[5,6,7,13,17,22,23,25,27,30,31,32,33,34,54,92,93,94,96,97,98,117,129],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := [([0,1,2,3,4,5,6,51],[0,2,3,4,5,6,7,13,23,34,39,54,88,98,99,130,131,132,133,134,135],[0]),([0,1,2,3,4,5,6,32,51],[6,7,13,88,98,134,135],[0,1]),([0,1,2,3,4,5,18,61],[1,10,11,13,18,19,20,21,22,23,28,34,36,37,38,146,151,152,153,154,155,156,157,158,159],[0]),([0,1,2,3,4,5,7,38],[0,1,5,13,20,22,28,34,40,41,44,45,46,47,49,142,143,144,145,150,160,161,162,163],[0]),([0,1,2,3,4,5,29,59],[1,13,20,22,23,34,54,70,71,74,76,77,78,79,85,144,164,165,166,167,168,169,170,171,172],[0]),([0,1,2,3,4,5,12,66],[1,5,13,20,22,23,34,184,185,191,192,193,194,196,197,198,199,200,201,202,203,204,208,209],[0]),([0,1,2,3,4,5,8,67],[0,1,13,20,21,22,34,159,182,183,186,189,190,193,195,204,210,211,212,213,214,215,216,217,218,219,220,221,222],[0]),([0,1,2,3,4,5,69],[0,5,8,9,13,21,23,34,54,186,193,223,224,225,226,227,228],[0]),([0,1,2,3,4,5,13,65],[1,5,13,20,22,23,34,193,204,234,235,236,237,238,239,240,241,242,243,244,245,246],[0]),([0,1,2,3,4,5,13,66],[1,5,13,20,22,23,34,197,198,199,200,201,203,204,229,230,234,235,236,244,245,248,249,250,251],[0]),([0,1,2,3,4,5,8,72],[0,5,13,20,21,22,34,46,182,183,186,189,204,218,221,222,233,247,253,254,255,256,257,258,259],[0]),([0,1,2,3,4,5,74],[0,1,8,9,21,23,34,54,218,221,260,261,262,263,264,265,266],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
def h0Block8_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,16,54],[5,8,9,13,20,22,23,103,193,250,267,268,270,271,272,273,274,275,276,277,278,279,280,281]),([0,1,2,3,4,5,29,54],[5,13,20,22,23,34,54,70,73,74,76,77,78,79,81,103,193,252,267,268,270,276,277,278]),([0,1,2,3,4,5,75],[0,1,5,8,9,21,23,54,221,293,294,295,296,297,298]),([0,1,2,3,4,5,10,79],[1,5,13,20,21,22,34,80,193,311,312,318,319,320,322,323,324,325,326,327,328,329,330,331,332]),([0,1,2,3,4,5,9,80],[0,1,13,20,22,23,34,159,193,309,310,313,316,317,321,330,333,334,335,336,337,338,339,340,341,342,343,344]),([0,1,2,3,4,5,81],[0,5,8,9,13,21,23,34,54,193,313,345,346,347,348,349,350]),([0,1,2,3,4,5,11,79],[1,5,13,20,21,22,34,85,250,323,324,325,326,327,329,330,351,352,356,357,358,360,361,362,363]),([0,1,2,3,4,5,9,83],[0,5,13,20,22,23,34,46,309,310,313,316,330,341,343,344,355,359,364,365,366,367,368,369,370]),([0,1,2,3,4,5,14,76],[1,5,13,20,22,34,54,109,193,301,371,372,376,377,378,379,380,381,382,383,384,385,386,387,390]),([0,1,2,3,4,5,85],[0,5,8,9,13,20,21,23,54,193,313,391,392,393,394,395,396]),([0,1,2,3,4,5,15,76],[1,5,13,20,22,34,54,159,301,381,382,383,384,385,387,390,397,398,402,403,404,405,406,407]),([0,1,2,3,4,5,86],[0,1,8,9,20,21,23,54,341,343,408,409,410,411,412,413,414])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_2 = true := by decide +kernel
def h0Block8_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,17,58],[5,8,9,13,17,22,34,54,139,193,415,416,418,419,420,421,422,423,424,425,426,427,428,429]),([0,1,2,3,4,5,24,58],[5,13,20,21,22,34,54,139,193,415,416,418,424,425,426,430,431,432,433,434,435,436,437]),([0,1,2,3,4,5,87],[0,1,5,8,9,21,23,54,343,447,448,449,450,451,452]),([0,1,2,3,4,5,29,43],[1,4,13,20,22,23,34,54,63,70,71,74,76,77,78,79,81,106,460,461,462,463,464,469,475]),([0,1,2,3,4,5,30,43],[1,4,13,20,22,23,34,54,63,150,245,462,463,464,469,475,476,477,478,479,480,481,482,483,484]),([0,1,2,3,4,5,31,43],[1,4,13,20,22,23,34,54,63,106,159,462,463,464,469,475,487,488,489,490,491,492,493,494,495]),([0,1,2,3,4,5,10,29,44],[22,70,71,74,78,79,81,311,320,496,499,500]),([0,1,2,3,4,5,92],[0,5,8,9,13,21,23,54,71,80,503,504,505,506,507,508]),([0,1,2,3,4,5,29,53],[5,13,20,22,23,34,54,70,71,74,76,77,78,100,150,514,515,516,517,518,519,520,524,525]),([0,1,2,3,4,5,30,53],[5,13,20,22,23,34,54,85,100,150,477,478,480,481,482,483,514,517,518,519,520,524,526,527,528]),([0,1,2,3,4,5,31,53],[5,13,20,22,23,34,54,100,106,150,488,489,491,492,493,494,514,517,518,519,520,524,529,530,531]),([0,1,2,3,4,5,11,29,44],[22,73,78,81,172,351,356,525,532,535])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_3 = true := by decide +kernel
def h0Block8_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,12,24,71],[20,34,184,193,194,430,431,432,433,437,446,552,553,554]),([0,1,2,3,4,5,95],[0,5,8,9,13,21,23,54,437,446,556,557,558,559,560,561]),([0,1,2,3,4,5,25,57],[5,13,20,21,22,34,54,136,150,567,568,569,570,571,572,573,574,575,576,577,578,579,580]),([0,1,2,3,4,5,26,57],[5,13,20,21,22,34,54,62,136,150,567,568,571,574,575,578,581,582,583,584,585,586,587,588]),([0,1,2,3,4,5,13,71],[1,5,13,20,22,23,34,193,229,230,234,235,236,237,245,246,247,553,554,593,594,595,596]),([0,1,2,3,4,5,13,24,71],[20,229,234,246,430,434,437,593]),([0,1,2,3,4,5,98],[0,1,8,9,13,21,23,54,245,434,597,598,599,600,601,602,603]),([0,1,2,3,4,5,13,73],[5,20,21,22,23,54,229,230,234,235,236,243,245,247,254,616,617,618,619,620,621,622,623]),([0,1,2,3,4,5,18,99],[0,1,5,10,11,16,18,19,20,22,28,36,37,38,193,629,630,631,632,633,634,635,636]),([0,1,2,3,4,5,18,100],[0,10,11,16,18,19,20,22,28,34,36,37,38,54,193,628,637,638,639,640,641,642]),([0,1,2,3,4,5,18,101],[1,5,10,11,16,18,19,20,21,22,23,28,34,36,37,54,85,648,650,651,652,653,654,655,656,657]),([0,1,2,3,4,5,18,102],[1,5,10,11,16,18,19,20,21,22,23,28,34,36,37,54,85,159,193,663,664,665,666,667,668,669])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_4 = true := by decide +kernel
def h0Block8_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,18,40],[1,5,10,11,16,18,19,20,21,22,23,28,36,37,41,54,675,676,677,678,679,680,681]),([0,1,2,3,4,5,29,90],[0,1,5,22,34,70,71,73,74,76,77,78,79,81,193,500,687,688,689,690,691,692,693]),([0,1,2,3,4,5,29,91],[0,20,21,22,34,70,71,73,74,76,77,78,79,81,193,686,694,695,696,697,698,699]),([0,1,2,3,4,5,29,94],[1,5,20,21,22,23,34,54,70,71,73,74,76,77,78,79,80,81,150,269,454,502,506,706,709,710]),([0,1,2,3,4,5,29,103],[1,5,20,21,22,23,34,54,70,71,73,74,76,77,78,79,81,85,172,193,714,717,718,719,720,721,722]),([0,1,2,3,4,5,29,104],[1,5,21,22,34,70,71,73,74,76,77,78,79,81,525,728,729,730,731,732,733,734,735])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_5 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1 ++ h0Block8_2 ++ h0Block8_3 ++ h0Block8_4 ++ h0Block8_5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Nodes8 = true := by
  unfold h0Nodes8 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h0Test8_0,h0Test8_1⟩,h0Test8_2⟩,h0Test8_3⟩,h0Test8_4⟩,h0Test8_5⟩
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket7Ok h0Check8
def h0Block9_0 : List NodeSpec := [([0,1,2,3,4,5,6,18],[0,1,2,3,4,5,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23,28,36,37,39,62],[0]),([0,1,2,3,4,5,27],[0,1,4,5,8,9,13,20,21,22,23,34,54,63,64,65,66,67,68],[0]),([0,1,2,3,4,5,6,27],[0,1,2,3,4,5,6,7,13,17,21,39,63,64,65,66,67,68,80],[0,1]),([0,1,2,3,4,5,28],[4,5,8,9,13,20,22,23,34,54,100,101,102,103,104,105],[0]),([0,1,2,3,4,5,6,29],[0,1,2,3,4,5,6,7,13,17,22,23,34,54,70,71,72,73,74,76,77,78,81,88,106,107,108,109],[0,1]),([0,1,2,3,4,5,32],[0,1,5,6,8,9,13,20,21,22,23,34,54,92,93,94,96,97,98],[0,1]),([0,1,2,3,4,5,6,32],[0,1,2,3,4,5,6,7,13,17,23,88,92,93,94,96,97,98],[0]),([0,1,2,3,4,5,33],[5,6,8,9,13,17,20,21,22,34,54,136,137,138,139,140,141],[0]),([0,1,2,3,4,5,7,18],[0,1,5,10,11,13,17,18,19,20,21,22,23,28,37,142,143,144,145,146,147,148,149,150,160],[0]),([0,1,2,3,4,5,59],[0,1,8,9,13,20,21,22,23,34,54,144,164,165,166,167,168],[0]),([0,1,2,3,4,5,7,29],[0,1,5,13,17,22,23,34,54,70,71,74,76,77,81,109,142,143,144,145,146,150,173,174,175,176],[0]),([0,1,2,3,4,5,60],[0,1,8,9,13,20,21,22,23,34,54,145,177,178,179,180,181],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := [([0,1,2,3,4,5,8,12],[0,1,5,13,20,21,22,23,85,182,183,184,185,186,187,188,189,190,191,192,193,194,195,204],[0]),([0,1,2,3,4,5,8,13],[0,1,5,13,20,21,22,23,150,182,183,186,189,204,218,221,229,230,231,232,233,234,235,236,247,252],[0]),([0,1,2,3,4,5,54],[0,5,8,9,13,20,21,22,23,34,54,103,252,267,268,269,282],[0,1]),([0,1,2,3,4,5,8,54],[0,1,13,20,21,103,150,182,183,186,189,193,204,218,221,252,267,268,283,284],[0]),([0,1,2,3,4,5,8,62],[0,1,5,13,21,150,182,183,186,189,204,221,252,282,285,286,287,288,289,290],[0]),([0,1,2,3,4,5,8,29],[0,13,20,21,22,23,34,54,70,71,74,76,77,78,81,106,109,150,182,183,186,189,204,219,221,252,282,291,292],[0]),([0,1,2,3,4,5,20],[1,5,8,9,10,13,20,22,34,54,193,299,300,301,302,303],[0,1]),([0,1,2,3,4,5,64],[0,1,5,8,9,13,21,22,34,54,189,304,305,306,307,308],[0,1]),([0,1,2,3,4,5,8,64],[0,13,21,23,150,182,183,186,189,193,204,219,221,282,304,305,306,307,308],[0]),([0,1,2,3,4,5,9,10],[0,1,5,13,20,21,22,23,193,309,310,311,312,313,314,315,316,317,318,319,320,321,330],[0]),([0,1,2,3,4,5,9,11],[0,1,5,13,17,20,21,22,23,85,150,309,310,313,316,330,341,343,351,352,353,354,355,356,357,358,359],[0]),([0,1,2,3,4,5,9,14],[0,1,5,13,17,22,23,34,54,193,309,310,313,316,330,371,372,373,374,375,376,377,378,379],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Block9_2 : List NodeSpec := [([0,1,2,3,4,5,9,15],[0,1,5,13,17,22,23,34,54,109,150,309,310,313,316,330,341,343,397,398,399,400,401,402,403,404,405],[0,1]),([0,1,2,3,4,5,58],[0,5,8,9,13,20,21,22,23,34,54,80,109,139,269,415,416,417],[0]),([0,1,2,3,4,5,9,58],[0,1,13,17,22,23,139,150,193,252,283,284,309,310,313,316,330,341,343,415,416],[0]),([0,1,2,3,4,5,9,77],[0,1,5,13,17,23,109,150,309,310,313,316,330,343,438,439,440,441,442,443],[0]),([0,1,2,3,4,5,9,24],[0,13,17,20,21,22,23,34,54,62,150,309,310,313,316,330,342,343,430,431,432,435,436,437,444,445,446],[0]),([0,1,2,3,4,5,76],[0,1,5,8,9,13,20,21,22,23,34,54,109,301,381,387,453,454],[0]),([0,1,2,3,4,5,9,76],[0,13,17,21,22,23,109,150,193,283,284,301,309,310,313,316,330,342,343,381,387],[0]),([0,1,2,3,4,5,45],[1,5,8,9,13,17,20,21,22,34,70,193,455,456,457,458,459],[0]),([0,1,2,3,4,5,79],[0,1,5,8,9,13,20,21,23,34,323,325,326,327,329,330],[0]),([0,1,2,3,4,5,9,79],[0,13,17,23,54,150,193,309,310,313,316,323,325,326,327,329,330,343,344],[0]),([0,1,2,3,4,5,43],[0,1,4,8,9,13,20,21,22,23,34,54,63,283,284],[0,1]),([0,1,2,3,4,5,10,29],[1,5,20,21,22,23,34,54,70,71,74,76,77,80,81,193,311,312,318,319,321,496,497,498,502],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
def h0Block9_3 : List NodeSpec := [([0,1,2,3,4,5,78],[0,1,5,8,9,13,20,21,22,23,34,54,312,509,510,511,512,513],[0,1]),([0,1,2,3,4,5,53],[0,1,5,8,9,13,20,21,22,23,34,54,100,150,283,284,514],[0,1]),([0,1,2,3,4,5,11,29],[1,5,17,20,21,22,23,34,54,70,71,73,74,76,77,81,85,172,351,352,357,358,359,525,532,533,534,536],[0]),([0,1,2,3,4,5,23],[0,5,8,9,11,13,20,22,34,54,150,537,538,539,540,541,542],[0]),([0,1,2,3,4,5,82],[0,1,5,8,9,13,21,22,23,34,54,352,543,544,545,546,547,548],[0,1]),([0,1,2,3,4,5,50],[0,1,6,8,9,13,17,20,21,22,23,34,54,85,92,283,284],[0]),([0,1,2,3,4,5,12,24],[1,5,17,20,21,22,23,34,54,85,184,185,191,192,193,195,431,432,435,436,437,446,549,550,551,555],[0]),([0,1,2,3,4,5,63],[0,1,5,8,9,13,17,20,21,22,23,34,54,185,562,563,564,565,566],[0]),([0,1,2,3,4,5,67],[0,1,5,8,9,13,20,21,22,23,34,54,195,210,211,214,215,217],[0]),([0,1,2,3,4,5,57],[0,1,5,8,9,13,17,20,21,22,23,34,54,136,150,283,284,567],[0]),([0,1,2,3,4,5,13,24],[1,5,17,20,21,22,23,34,54,229,230,235,236,243,245,247,250,431,432,434,435,436,437,446,589,590,591,592],[0]),([0,1,2,3,4,5,70],[0,1,5,8,9,13,17,20,21,23,34,54,230,604,605,606,607,608,609],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
def h0Block9_4 : List NodeSpec := [([0,1,2,3,4,5,13,70],[1,5,21,23,80,150,229,230,235,236,243,245,247,604,605,606,607,608,609],[0]),([0,1,2,3,4,5,48],[0,5,8,9,13,20,21,22,34,71,150,610,611,612,613,614,615],[0]),([0,1,2,3,4,5,72],[0,1,5,8,9,13,20,21,23,34,54,247,253,254,255,256,257,259],[0]),([0,1,2,3,4,5,13,72],[1,5,23,54,150,229,230,235,236,244,245,247,253,254,255,256,257,259],[0]),([0,1,2,3,4,5,19],[0,1,5,8,9,10,13,21,23,34,54,193,624,625,626,627,628],[0,1]),([0,1,2,3,4,5,18,19],[0,10,11,13,18,19,20,21,23,28,36,37,193,624,625,626,627,628],[0,1]),([0,1,2,3,4,5,21],[0,5,8,9,11,13,21,23,34,54,150,643,644,645,646,647,648],[0]),([0,1,2,3,4,5,18,21],[1,5,10,11,16,17,18,19,20,21,23,28,37,643,644,645,646,647,648,649],[0]),([0,1,2,3,4,5,18,22],[1,5,10,11,17,18,19,20,21,23,28,37,85,193,658,659,660,661,662,663],[0]),([0,1,2,3,4,5,37],[0,1,5,8,9,13,17,20,22,28,34,670,671,672,673,674],[0]),([0,1,2,3,4,5,38],[0,1,5,8,9,13,20,21,23,28,34,40,44,45,47,49],[0]),([0,1,2,3,4,5,18,38],[10,11,17,18,19,20,21,23,28,37,38,40,44,45,47,49,54],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
def h0Block9_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,44],[0,1,5,8,9,13,17,20,21,23,54,70,193,682,683,684,685,686]),([0,1,2,3,4,5,29,44],[0,13,22,23,54,70,71,74,76,77,78,81,193,682,683,684,685,686]),([0,1,2,3,4,5,46],[0,5,8,9,13,20,21,23,54,71,150,700,701,702,703,704,705]),([0,1,2,3,4,5,29,46],[1,5,22,23,54,70,71,73,74,76,77,81,109,525,700,701,702,703,704,705]),([0,1,2,3,4,5,29,47],[1,5,22,23,54,70,71,74,76,77,81,109,193,711,712,713,714,715,716]),([0,1,2,3,4,5,49],[0,1,5,8,9,13,17,20,21,23,54,74,723,724,725,726,727]),([0,1,2,3,4,5,29,49],[20,21,22,23,54,70,71,74,76,77,79,81,109,723,724,725,726,727])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1 ++ h0Block9_2 ++ h0Block9_3 ++ h0Block9_4 ++ h0Block9_5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := by
  unfold h0Nodes9 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h0Test9_0,h0Test9_1⟩,h0Test9_2⟩,h0Test9_3⟩,h0Test9_4⟩,h0Test9_5⟩
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5,6,7,8,9,13,21,23,54],[0,1]),([0,1,2,3,4,5,7],[0,1,8,9,21,23,54,142,143,144,145,146],[0,1]),([0,1,2,3,4,5,8],[0,1,8,9,13,21,23,54,182,183,189,204],[0,1]),([0,1,2,3,4,5,9],[0,1,8,9,13,21,23,54,309,310,316,330],[0]),([0,1,2,3,4,5,10],[0,1,8,9,21,23,54,311,312,318,319,321],[0,1]),([0,1,2,3,4,5,11],[0,1,5,8,9,21,23,54,85,150,351,352,357,358,359],[0,1]),([0,1,2,3,4,5,12],[0,1,8,9,21,23,54,184,185,191,192,195],[0,1]),([0,1,2,3,4,5,13],[0,1,5,8,9,21,23,54,150,229,230,235,236,247],[0,1]),([0,1,2,3,4,5,18],[0,1,8,9,10,18,19,20,21,23,28,54],[0,1]),([0,1,2,3,4,5,29],[0,1,8,9,21,22,23,54,70,74,76,77],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Nodes10 : List NodeSpec := h0Block10_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Nodes10 = true := h0Test10_0
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket9Ok h0Check10
def h0Block11_0 : List NodeSpec := [([0,1,2,3,4,5],[0,8,9,21,23,54],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test11_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket10 11 h0Block11_0 = true := by decide +kernel
def h0Nodes11 : List NodeSpec := h0Block11_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket10 11 h0Nodes11 = true := h0Test11_0
def h0Bucket11 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 11 xs.toFinset) h0Bucket11 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket10Ok h0Check11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 10]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 2]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276808392 * 2 ^ 32 + 3939033088) ||| ((4276808392 * 2 ^ 32 + 3939033088) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4276808392 * 2 ^ 32 + 3939033088) ||| ((4276808392 * 2 ^ 32 + 3939033088) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_48557
theorem PEqualNP.Outside.L_meta_48557 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 3939033088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 3939033088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_48557.table2_of_lower (4276808392 * 2 ^ 32 + 3939033088) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_48557.low_root
    PEqualNP.Outside.L_meta_48557.wit PEqualNP.Outside.L_meta_48557.wo (by decide)
    PEqualNP.Outside.L_meta_48557.wit_mono PEqualNP.Outside.L_meta_48557.wit_eval s hcs
