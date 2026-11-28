import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_47933
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
def h1R : List Nat := varsOf 19
def h1G : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def h1Pos : List Nat := [17,18,3,3,18,17]
def h1Neg : List Nat := [16,16,1,2,2,1]
def h1Mask : Nat := fullMask 6
def h1Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h1Steps : List (Nat × Nat × Nat) := []
def h1W : BT Decor := buildWiresBT 2 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[],[(1,4)],[(0,1)],[(0,4)],[(1,4),(0,1)],[(1,4),(0,4)]]
def h1Autos : BT (List (Nat × Nat)) := btOfList 3 h1AutoList
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
def h1Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2],[])]
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
lemma h1Bound : Lower h1R h1G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 4,1,17)]) (by decide +kernel) h1Bucket3Ok (by decide +kernel)
namespace Cofactor12058
def G_0 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def R_0 : List Nat := varsOf 52
def pos_0 : List Nat := [20,20,36,36,48,48,20,36,48]
def neg_0 : List Nat := [16,4,32,4,32,16,32,16,4]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 2,20,16),(VAR 4,20,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_6 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_6 : List Nat := varsOf 22
lemma low_6_ok : carryOK [(3,5),(1,3),(1,4),(1,2)] R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 4 := carry_of low_6_ok low_0

def G_7 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_7 : List Nat := varsOf 38
lemma low_7_ok : carryOK [(1,3),(1,4),(1,2)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0

def G_9 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def R_9 : List Nat := varsOf 50
lemma low_9_ok : carryOK [(1,2)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0

def G_10 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def R_10 : List Nat := varsOf 54
def pos_10 : List Nat := [22,22,22,38,38,38,50,50,50,52,52,52,22,22,22,38,38,38,50,50,50,52,52,52]
def neg_10 : List Nat := [20,18,6,36,34,6,48,34,18,48,36,20,34,36,48,18,20,48,6,20,36,6,18,34]
def fmask_10 : Nat := fullMask 24
def base_10 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_10 : List (Nat × Nat × Nat) := [(0,0,1),(3,4,2),(0,0,2),(0,4,2),(0,1,2),(3,7,3)]
def W_10 : BT Decor := buildWiresBT 4 base_10 steps_10
def autosL_10 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_10 : BT (List (Nat × Nat)) := btOfList 4 autosL_10
def slicesL_10 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def slices_10 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_10
def ps_10 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_10 : BT (Option BoundPool) := buildPoolsBT 2 W_10 R_10 slices_10 ps_10
lemma gp_10 : goodPairs G_10 pos_10 neg_10 := goodPairs_of (by decide +kernel)
lemma base_10_ok : ∀ x ∈ base_10, faithful pos_10 neg_10 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_10_ok : btAll (fun x => faithful pos_10 neg_10 x ∧ x.1 < 2^128) W_10 := buildWiresBT_faithful base_10_ok
set_option maxRecDepth 500000 in
lemma autos_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_10 = G_10) autos_10 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_10_0_ok : sliceDirectCheck 0 16 0 R_10 G_10 R_7 G_7 = true := by decide +kernel
lemma sl_10_0 : Slice R_10 G_10 (subcubeFast 0 16) 4 := slice_fast_direct sl_10_0_ok low_7
lemma sl_10_1_ok : sliceDirectCheck 0 2 0 R_10 G_10 R_0 G_0 = true := by decide +kernel
lemma sl_10_1 : Slice R_10 G_10 (subcubeFast 0 2) 4 := slice_fast_direct sl_10_1_ok low_0
lemma sl_10_2_ok : sliceDirectCheck 0 4 0 R_10 G_10 R_9 G_9 = true := by decide +kernel
lemma sl_10_2 : Slice R_10 G_10 (subcubeFast 0 4) 4 := slice_fast_direct sl_10_2_ok low_9
lemma sl_10_3_ok : sliceDirectCheck 0 32 0 R_10 G_10 R_6 G_6 = true := by decide +kernel
lemma sl_10_3 : Slice R_10 G_10 (subcubeFast 0 32) 4 := slice_fast_direct sl_10_3_ok low_6
set_option maxRecDepth 500000 in
lemma slices_10_ok : btAll (fun o => ∀ p, o = some p → Slice R_10 G_10 p.1 p.2) slices_10 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_10 G_10 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_10_0) (forall_cons (fun _ h => by cases h; exact sl_10_1) (forall_cons (fun _ h => by cases h; exact sl_10_2) (forall_cons (fun _ h => by cases h; exact sl_10_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_10_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_10 G_10 c) P_10 := buildPoolsBT_sound slices_10_ok
def bk_10_init : BT (List (List Nat)) := BT.empty
lemma bk_10_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 (0 - 1) xs.toFinset) bk_10_init := trivial
def nodes_10_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_0 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_init 0 nodes_10_0 = true := by decide +kernel
def bk_10_0 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_0
set_option maxRecDepth 500000 in
lemma bk_10_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 0 xs.toFinset) bk_10_0 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_init_ok chk_10_0
def nodes_10_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_1 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_0 1 nodes_10_1 = true := by decide +kernel
def bk_10_1 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_1
set_option maxRecDepth 500000 in
lemma bk_10_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 1 xs.toFinset) bk_10_1 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_0_ok chk_10_1
def nodes_10_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_2 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_1 2 nodes_10_2 = true := by decide +kernel
def bk_10_2 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_2
set_option maxRecDepth 500000 in
lemma bk_10_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 2 xs.toFinset) bk_10_2 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_1_ok chk_10_2
def nodes_10_3 : List NodeSpec := [([4,6,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_3 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_2 3 nodes_10_3 = true := by decide +kernel
def bk_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_3
set_option maxRecDepth 500000 in
lemma bk_10_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 3 xs.toFinset) bk_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_2_ok chk_10_3
def nodes_10_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([4,6,1,2,3],[0,2],[0]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_4 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_3 4 nodes_10_4 = true := by decide +kernel
def bk_10_4 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_4
set_option maxRecDepth 500000 in
lemma bk_10_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 4 xs.toFinset) bk_10_4 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_3_ok chk_10_4
def nodes_10_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_5 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_4 5 nodes_10_5 = true := by decide +kernel
def bk_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_5
set_option maxRecDepth 500000 in
lemma bk_10_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 5 xs.toFinset) bk_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_4_ok chk_10_5
def nodes_10_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_6 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_5 6 nodes_10_6 = true := by decide +kernel
def bk_10_6 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_6
set_option maxRecDepth 500000 in
lemma bk_10_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 6 xs.toFinset) bk_10_6 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_5_ok chk_10_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck R_10 G_10 [(VAR 1,22,20),(VAR 2,22,18),(VAR 4,22,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT bk_10_6 R_10 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_10 : Lower R_10 G_10 7 := lower_of_forestBT root_10_ok bk_10_6_ok root_10_in

end Cofactor12058
def h2R : List Nat := varsOf 27
def h2G : Nat := 0xee888800ee888800ee888800ee888800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 7 := carry_of (swaps := [(3,4),(4,5),(0,1),(1,2)]) (roots2 := Cofactor12058.R_10) (T2 := Cofactor12058.G_10) (by decide +kernel) Cofactor12058.low_10
def h3R : List Nat := varsOf 21
def h3G : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 4 := carry_of (swaps := [(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h4R : List Nat := varsOf 29
def h4G : Nat := 0xfa00a000fa00a000fa00a000fa00a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,5,13)]) (by decide +kernel) h3Bound
def h6R : List Nat := varsOf 11
def h6G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 4 := carry_of (swaps := [(3,4)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h5R : List Nat := varsOf 15
def h5G : Nat := 0xfe88fe88fe88fe88fe88fe88fe88fe88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,8,12)]) (by decide +kernel) h6Bound
def h7R : List Nat := varsOf 30
def h7G : Nat := 0xffccfc00ffccfc00ffccfc00ffccfc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(2,3),(1,2),(0,1)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h8R : List Nat := varsOf 31
def h8G : Nat := 0xfe88a800fe88a800fe88a800fe88a800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 8 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,9,13)]) (by decide +kernel) h2Bound
def h10R : List Nat := varsOf 7
def h10G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 4 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h9R : List Nat := varsOf 39
def h9G : Nat := 0xe8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,6,38)]) (by decide +kernel) h10Bound
def h11R : List Nat := varsOf 41
def h11G : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 4 := carry_of (swaps := [(4,5),(1,2),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h12R : List Nat := varsOf 45
def h12G : Nat := 0xfaaafaaaaa00aa00faaafaaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(3,4),(1,2),(2,3)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h14R : List Nat := varsOf 15
def h14G : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 5 := carry_of (swaps := [(4,5),(3,4)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h15R : List Nat := varsOf 43
def h15G : Nat := 0xeeaaeeaaaa00aa00eeaaeeaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(3,4),(1,2),(2,3),(1,2)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h13R : List Nat := varsOf 47
def h13G : Nat := 0xe8a8e8a8a800a800e8a8e8a8a800a800
def h13Pos : List Nat := [13,46,13,46,13,37,11,11,13,11,46,35,46,11,37,35,13,37,35]
def h13Neg : List Nat := [12,44,14,42,9,36,8,3,5,9,14,3,38,10,33,33,7,5,42]
def h13Mask : Nat := fullMask 19
def h13Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7ebf5,0x3cb90),(0xcccccccccccccccccccccccccccccccc,0x4beca,0x53c8c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3553f,0x31527),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x137df,0x4265f),(0xffffffff00000000ffffffff00000000,0x6dc2a,0x4d02a)]
def h13Steps : List (Nat × Nat × Nat) := [(0,0,1),(3,0,1),(2,2,5),(0,3,5),(2,3,5),(0,3,6),(2,3,6),(0,1,3),(1,0,12),(2,0,12),(2,2,8),(2,4,11),(0,2,13)]
def h13W : BT Decor := buildWiresBT 5 h13Base h13Steps
def h13AutoList : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)],[(2,5),(1,3)],[(2,3),(1,5)],[(3,5),(2,5),(1,3)],[(3,5),(2,3),(1,5)]]
def h13Autos : BT (List (Nat × Nat)) := btOfList 3 h13AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Pairs : goodPairs h13G h13Pos h13Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13BaseOk : ∀ x ∈ h13Base, faithful h13Pos h13Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13WOk : btAll (fun x => faithful h13Pos h13Neg x ∧ x.1 < 2^128) h13W := buildWiresBT_faithful h13BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h13G = h13G) h13Autos := btAll_ofList (autos_of (by decide +kernel))
def h13SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 6,4),some (subcubeFast 0 8,5),some (subcubeFast 0 32,5),some (subcubeFast 0 40,4)]
def h13Slices : BT (Option (Nat × Nat)) := btOfList 3 h13SliceList
def h13Specs : List PoolSpec := [(0,[]),(1,[(3,0,1)]),(2,[]),(1,[(0,1,3)]),(3,[]),(1,[]),(4,[]),(5,[]),(4,[(0,1,3)])]
def h13Pools : BT (Option BoundPool) := buildPoolsBT 4 h13W h13R h13Slices h13Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice5 : Slice h13R h13G (subcubeFast 0 40) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice4 : Slice h13R h13G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice3 : Slice h13R h13G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice2 : Slice h13R h13G (subcubeFast 0 6) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice1 : Slice h13R h13G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice0 : Slice h13R h13G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h13R h13G p.1 p.2) h13Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h13R h13G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h13Slice0) (forall_cons (fun _ h => by cases h; exact h13Slice1) (forall_cons (fun _ h => by cases h; exact h13Slice2) (forall_cons (fun _ h => by cases h; exact h13Slice3) (forall_cons (fun _ h => by cases h; exact h13Slice4) (forall_cons (fun _ h => by cases h; exact h13Slice5) (fun _ h => (List.not_mem_nil h).elim)))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h13R h13G c) h13Pools := buildPoolsBT_sound h13SlicesOk
def h13Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h13G (4 - 1) xs.toFinset) h13Empty := trivial
def h13Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,3,4,15],[]),([0,1,2,3,16],[]),([0,1,3,4,17],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Test4_0 : checkNodesBT h13W h13G h13Mask h13Pools h13Autos h13Empty 4 h13Block4_0 = true := by decide +kernel
def h13Nodes4 : List NodeSpec := h13Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Check4 : checkNodesBT h13W h13G h13Mask h13Pools h13Autos h13Empty 4 h13Nodes4 = true := h13Test4_0
def h13Bucket4 : BT (List (List Nat)) := buildBucketsBT h13W h13Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h13G 4 xs.toFinset) h13Bucket4 := buildBucketsBT_sound (by decide) h13Pairs h13WOk h13PoolsOk h13AutosOk h13EmptyOk h13Check4
def h13Block5_0 : List NodeSpec := [([0,2,3,4,5,6],[0,1],[0]),([0,2,3,4,5,12],[3,4],[0]),([0,1,3,4,7],[],[0]),([0,1,3,4,5,7],[5],[0]),([0,1,2,3,4,8],[5,6],[0,4]),([0,1,2,3,4,9],[],[0]),([0,1,2,3,4,10],[],[0]),([0,1,2,3,4,11],[6],[0]),([0,1,2,3,4,13],[0,4,5,6],[0,4]),([0,1,2,3,4,14],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Test5_0 : checkNodesBT h13W h13G h13Mask h13Pools h13Autos h13Bucket4 5 h13Block5_0 = true := by decide +kernel
def h13Nodes5 : List NodeSpec := h13Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Check5 : checkNodesBT h13W h13G h13Mask h13Pools h13Autos h13Bucket4 5 h13Nodes5 = true := h13Test5_0
def h13Bucket5 : BT (List (List Nat)) := buildBucketsBT h13W h13Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h13G 5 xs.toFinset) h13Bucket5 := buildBucketsBT_sound (by decide) h13Pairs h13WOk h13PoolsOk h13AutosOk h13Bucket4Ok h13Check5
def h13Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,2,4,5,6],[0,1]),([0,1,2,3,4,6],[0,1,2,4,5,6],[0,1]),([0,1,2,3,4,12],[0,2,3,4,5,6,7,8],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Test6_0 : checkNodesBT h13W h13G h13Mask h13Pools h13Autos h13Bucket5 6 h13Block6_0 = true := by decide +kernel
def h13Nodes6 : List NodeSpec := h13Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Check6 : checkNodesBT h13W h13G h13Mask h13Pools h13Autos h13Bucket5 6 h13Nodes6 = true := h13Test6_0
def h13Bucket6 : BT (List (List Nat)) := buildBucketsBT h13W h13Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h13G 6 xs.toFinset) h13Bucket6 := buildBucketsBT_sound (by decide) h13Pairs h13WOk h13PoolsOk h13AutosOk h13Bucket5Ok h13Check6
def h13Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,2,4,5,6,7],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Test7_0 : checkNodesBT h13W h13G h13Mask h13Pools h13Autos h13Bucket6 7 h13Block7_0 = true := by decide +kernel
def h13Nodes7 : List NodeSpec := h13Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Check7 : checkNodesBT h13W h13G h13Mask h13Pools h13Autos h13Bucket6 7 h13Nodes7 = true := h13Test7_0
def h13Bucket7 : BT (List (List Nat)) := buildBucketsBT h13W h13Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h13G 7 xs.toFinset) h13Bucket7 := buildBucketsBT_sound (by decide) h13Pairs h13WOk h13PoolsOk h13AutosOk h13Bucket6Ok h13Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 8 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 5,3,35)]) (by decide +kernel) h13Bucket7Ok (by decide +kernel)
def h16R : List Nat := varsOf 23
def h16G : Nat := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 5 := carry_of (swaps := [(4,5)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h17R : List Nat := varsOf 35
def h17G : Nat := 0xeeeeeeee88888888eeeeeeee88888888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 4 := carry_of (swaps := [(4,5)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h18R : List Nat := varsOf 39
def h18G : Nat := 0xe8e8e8e888888888e8e8e8e888888888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,33,37)]) (by decide +kernel) h17Bound
def h19R : List Nat := varsOf 49
def h19G : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 4 := carry_of (swaps := [(4,5),(1,2),(2,3),(3,4)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h20R : List Nat := varsOf 51
def h20G : Nat := 0xeeeeaaaa88880000eeeeaaaa88880000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h21R : List Nat := varsOf 53
def h21G : Nat := 0xfafaaaaaaaaa0000fafaaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(2,3)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h22R : List Nat := varsOf 54
def h22G : Nat := 0xfcfcfcfccccc0000fcfcfcfccccc0000
def h22Pos : List Nat := [18,22,34,18,22,34,36,52]
def h22Neg : List Nat := [16,20,32,2,6,2,4,20]
def h22Mask : Nat := fullMask 8
def h22Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,63,56),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,210,210),(0xffff0000ffff0000ffff0000ffff0000,155,131),(0xffffffff00000000ffffffff00000000,228,4)]
def h22Steps : List (Nat × Nat × Nat) := []
def h22W : BT Decor := buildWiresBT 2 h22Base h22Steps
def h22AutoList : List (List (Nat × Nat)) := [[],[(2,4),(1,5)]]
def h22Autos : BT (List (Nat × Nat)) := btOfList 1 h22AutoList
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
def h22SliceList : List (Option (Nat × Nat)) := []
def h22Slices : BT (Option (Nat × Nat)) := btOfList 1 h22SliceList
def h22Specs : List PoolSpec := []
def h22Pools : BT (Option BoundPool) := buildPoolsBT 1 h22W h22R h22Slices h22Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h22R h22G p.1 p.2) h22Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h22R h22G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h22R h22G c) h22Pools := buildPoolsBT_sound h22SlicesOk
def h22Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G (3 - 1) xs.toFinset) h22Empty := trivial
def h22Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3],[])]
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
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 4 := lower_of_forestBT (essPairs := [(VAR 1,16,18),(VAR 2,32,36),(VAR 4,2,18),(VAR 5,2,34)]) (by decide +kernel) h22Bucket3Ok (by decide +kernel)
def h23R : List Nat := varsOf 55
def h23G : Nat := 0xe8e8a8a888880000e8e8a8a888880000
def h23Pos : List Nat := [37,54,19,19,54,37,54,19,54,35,35,37]
def h23Neg : List Nat := [36,52,17,18,50,33,38,3,22,3,33,5]
def h23Mask : Nat := fullMask 12
def h23Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3757,3748),(0xcccccccccccccccccccccccccccccccc,2014,984),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2419,2371),(0xffff0000ffff0000ffff0000ffff0000,478,286),(0xffffffff00000000ffffffff00000000,3955,1139)]
def h23Steps : List (Nat × Nat × Nat) := []
def h23W : BT Decor := buildWiresBT 3 h23Base h23Steps
def h23AutoList : List (List (Nat × Nat)) := [[],[(2,4),(1,5)]]
def h23Autos : BT (List (Nat × Nat)) := btOfList 1 h23AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Pairs : goodPairs h23G h23Pos h23Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23BaseOk : ∀ x ∈ h23Base, faithful h23Pos h23Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23WOk : btAll (fun x => faithful h23Pos h23Neg x ∧ x.1 < 2^128) h23W := buildWiresBT_faithful h23BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h23G = h23G) h23Autos := btAll_ofList (autos_of (by decide +kernel))
def h23SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5)]
def h23Slices : BT (Option (Nat × Nat)) := btOfList 2 h23SliceList
def h23Specs : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def h23Pools : BT (Option BoundPool) := buildPoolsBT 2 h23W h23R h23Slices h23Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Slice3 : Slice h23R h23G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Slice2 : Slice h23R h23G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Slice1 : Slice h23R h23G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Slice0 : Slice h23R h23G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h23R h23G p.1 p.2) h23Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h23R h23G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h23Slice0) (forall_cons (fun _ h => by cases h; exact h23Slice1) (forall_cons (fun _ h => by cases h; exact h23Slice2) (forall_cons (fun _ h => by cases h; exact h23Slice3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h23R h23G c) h23Pools := buildPoolsBT_sound h23SlicesOk
def h23Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h23G (6 - 1) xs.toFinset) h23Empty := trivial
def h23Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Test6_0 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Empty 6 h23Block6_0 = true := by decide +kernel
def h23Nodes6 : List NodeSpec := h23Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Check6 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Empty 6 h23Nodes6 = true := h23Test6_0
def h23Bucket6 : BT (List (List Nat)) := buildBucketsBT h23W h23Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h23G 6 xs.toFinset) h23Bucket6 := buildBucketsBT_sound (by decide) h23Pairs h23WOk h23PoolsOk h23AutosOk h23EmptyOk h23Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 7 := lower_of_forestBT (essPairs := [(VAR 0,18,19),(VAR 1,17,19),(VAR 2,33,37),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h23Bucket6Ok (by decide +kernel)
def h24R : List Nat := varsOf 57
def h24G : Nat := 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h25R : List Nat := varsOf 58
def h25G : Nat := 0xffccccccffcccc00ffccccccffcccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h26R : List Nat := varsOf 59
def h26G : Nat := 0xee888888ee888800ee888888ee888800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 8 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,3,35)]) (by decide +kernel) h2Bound
def h27R : List Nat := varsOf 29
def h27G : Nat := 0xfaa0a0a0faa0a0a0faa0a0a0faa0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 5 := carry_of (swaps := [(4,5),(2,3),(1,2)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h28R : List Nat := varsOf 45
def h28G : Nat := 0xfaa0faa0fa00fa00faa0faa0fa00fa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(1,2)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h29R : List Nat := varsOf 57
def h29G : Nat := 0xffaaaaaaff00aa00ffaaaaaaff00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 4 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1)]) (roots2 := h22R) (T2 := h22G) (by decide +kernel) h22Bound
def h30R : List Nat := varsOf 60
def h30G : Nat := 0xfff0f0f0ff00f000fff0f0f0ff00f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 4 := carry_of (swaps := [(4,5),(2,3),(3,4),(1,2)]) (roots2 := h22R) (T2 := h22G) (by decide +kernel) h22Bound
def h31R : List Nat := varsOf 61
def h31G : Nat := 0xfaa0a0a0fa00a000faa0a0a0fa00a000
def h31Pos : List Nat := [25,28,28,13,28,25,37,57,13,25,60,13,57,53,57,37,37]
def h31Neg : List Nat := [24,24,20,5,12,9,5,56,12,17,56,9,49,21,41,36,33]
def h31Mask : Nat := fullMask 17
def h31Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1fbe9,0x17a68),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1ad5e,0xa15c),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x5fbf,0x4db3),(0xffff0000ffff0000ffff0000ffff0000,0x76b7,0x3687),(0xffffffff00000000ffffffff00000000,0x1f4c0,0x1d480)]
def h31Steps : List (Nat × Nat × Nat) := [(0,0,1),(2,3,5)]
def h31W : BT Decor := buildWiresBT 3 h31Base h31Steps
def h31AutoList : List (List (Nat × Nat)) := [[],[(0,2)]]
def h31Autos : BT (List (Nat × Nat)) := btOfList 1 h31AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Pairs : goodPairs h31G h31Pos h31Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31BaseOk : ∀ x ∈ h31Base, faithful h31Pos h31Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31WOk : btAll (fun x => faithful h31Pos h31Neg x ∧ x.1 < 2^128) h31W := buildWiresBT_faithful h31BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h31G = h31G) h31Autos := btAll_ofList (autos_of (by decide +kernel))
def h31SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 32 0,5),some (subcubeFast 32 8,4)]
def h31Slices : BT (Option (Nat × Nat)) := btOfList 3 h31SliceList
def h31Specs : List PoolSpec := [(0,[]),(3,[]),(5,[]),(4,[]),(1,[]),(6,[]),(2,[])]
def h31Pools : BT (Option BoundPool) := buildPoolsBT 3 h31W h31R h31Slices h31Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice6 : Slice h31R h31G (subcubeFast 32 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice5 : Slice h31R h31G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice4 : Slice h31R h31G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice3 : Slice h31R h31G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice2 : Slice h31R h31G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 32) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice1 : Slice h31R h31G (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice0 : Slice h31R h31G (subcubeFast 0 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h31R h31G p.1 p.2) h31Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h31R h31G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h31Slice0) (forall_cons (fun _ h => by cases h; exact h31Slice1) (forall_cons (fun _ h => by cases h; exact h31Slice2) (forall_cons (fun _ h => by cases h; exact h31Slice3) (forall_cons (fun _ h => by cases h; exact h31Slice4) (forall_cons (fun _ h => by cases h; exact h31Slice5) (forall_cons (fun _ h => by cases h; exact h31Slice6) (fun _ h => (List.not_mem_nil h).elim))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h31R h31G c) h31Pools := buildPoolsBT_sound h31SlicesOk
def h31Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h31G (4 - 1) xs.toFinset) h31Empty := trivial
def h31Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,4,6],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Test4_0 : checkNodesBT h31W h31G h31Mask h31Pools h31Autos h31Empty 4 h31Block4_0 = true := by decide +kernel
def h31Nodes4 : List NodeSpec := h31Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Check4 : checkNodesBT h31W h31G h31Mask h31Pools h31Autos h31Empty 4 h31Nodes4 = true := h31Test4_0
def h31Bucket4 : BT (List (List Nat)) := buildBucketsBT h31W h31Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h31G 4 xs.toFinset) h31Bucket4 := buildBucketsBT_sound (by decide) h31Pairs h31WOk h31PoolsOk h31AutosOk h31EmptyOk h31Check4
def h31Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Test5_0 : checkNodesBT h31W h31G h31Mask h31Pools h31Autos h31Bucket4 5 h31Block5_0 = true := by decide +kernel
def h31Nodes5 : List NodeSpec := h31Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Check5 : checkNodesBT h31W h31G h31Mask h31Pools h31Autos h31Bucket4 5 h31Nodes5 = true := h31Test5_0
def h31Bucket5 : BT (List (List Nat)) := buildBucketsBT h31W h31Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h31G 5 xs.toFinset) h31Bucket5 := buildBucketsBT_sound (by decide) h31Pairs h31WOk h31PoolsOk h31AutosOk h31Bucket4Ok h31Check5
def h31Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,1,2,3,4,5,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Test6_0 : checkNodesBT h31W h31G h31Mask h31Pools h31Autos h31Bucket5 6 h31Block6_0 = true := by decide +kernel
def h31Nodes6 : List NodeSpec := h31Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Check6 : checkNodesBT h31W h31G h31Mask h31Pools h31Autos h31Bucket5 6 h31Nodes6 = true := h31Test6_0
def h31Bucket6 : BT (List (List Nat)) := buildBucketsBT h31W h31Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h31G 6 xs.toFinset) h31Bucket6 := buildBucketsBT_sound (by decide) h31Pairs h31WOk h31PoolsOk h31AutosOk h31Bucket5Ok h31Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 7 := lower_of_forestBT (essPairs := [(VAR 0,12,13),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,9,25),(VAR 5,5,37)]) (by decide +kernel) h31Bucket6Ok (by decide +kernel)
def h32R : List Nat := varsOf 30
def h32G : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 7 := carry_of (swaps := [(1,2),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h33R : List Nat := varsOf 46
def h33G : Nat := 0xfcc0fcc0fc00fc00fcc0fcc0fc00fc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(1,2),(0,1)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h34R : List Nat := varsOf 54
def h34G : Nat := 0xfcfcc0c0fcfc0000fcfcc0c0fcfc0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(1,2),(0,1)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h35R : List Nat := varsOf 56
def h35G : Nat := 0xffffff00ff000000ffffff00ff000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 4 := carry_of (swaps := [(4,5),(1,2),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h36R : List Nat := varsOf 58
def h36G : Nat := 0xffcccc00ff000000ffcccc00ff000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h37R : List Nat := varsOf 60
def h37G : Nat := 0xfff0f000ff000000fff0f000ff000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h38R : List Nat := varsOf 62
def h38G : Nat := 0xfcc0c000fc000000fcc0c000fc000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 8 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,14,46)]) (by decide +kernel) h32Bound
namespace Cofactor12058
def G_13 : Nat := 0xfffffcfcfcfcc0c0fffffcfcfcfcc0c0
def R_13 : List Nat := varsOf 54
def pos_13 : List Nat := [6,6,18,18,20,20,34,34,36,36,48,48,6,6,18,18,20,20,34,34,36,36,48,48]
def neg_13 : List Nat := [4,2,16,2,16,4,32,2,32,4,32,16,16,32,4,32,2,32,4,16,2,16,2,4]
def fmask_13 : Nat := fullMask 24
def base_13 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf0cf,0x51008a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x333333,0x844221),(0xffff0000ffff0000ffff0000ffff0000,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def steps_13 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_13 : BT Decor := buildWiresBT 4 base_13 steps_13
def autosL_13 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_13 : BT (List (Nat × Nat)) := btOfList 4 autosL_13
def slicesL_13 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,4),some (subcubeFast 2 0,4),some (subcubeFast 32 0,4),some (subcubeFast 16 0,4)]
def slices_13 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_13
def ps_13 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_13 : BT (Option BoundPool) := buildPoolsBT 2 W_13 R_13 slices_13 ps_13
lemma gp_13 : goodPairs G_13 pos_13 neg_13 := goodPairs_of (by decide +kernel)
lemma base_13_ok : ∀ x ∈ base_13, faithful pos_13 neg_13 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_13_ok : btAll (fun x => faithful pos_13 neg_13 x ∧ x.1 < 2^128) W_13 := buildWiresBT_faithful base_13_ok
set_option maxRecDepth 500000 in
lemma autos_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_13 = G_13) autos_13 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_13_0_ok : sliceDirectCheck 4 0 0 R_13 G_13 R_9 G_9 = true := by decide +kernel
lemma sl_13_0 : Slice R_13 G_13 (subcubeFast 4 0) 4 := slice_fast_direct sl_13_0_ok low_9
lemma sl_13_1_ok : sliceDirectCheck 2 0 0 R_13 G_13 R_0 G_0 = true := by decide +kernel
lemma sl_13_1 : Slice R_13 G_13 (subcubeFast 2 0) 4 := slice_fast_direct sl_13_1_ok low_0
lemma sl_13_2_ok : sliceDirectCheck 32 0 0 R_13 G_13 R_6 G_6 = true := by decide +kernel
lemma sl_13_2 : Slice R_13 G_13 (subcubeFast 32 0) 4 := slice_fast_direct sl_13_2_ok low_6
lemma sl_13_3_ok : sliceDirectCheck 16 0 0 R_13 G_13 R_7 G_7 = true := by decide +kernel
lemma sl_13_3 : Slice R_13 G_13 (subcubeFast 16 0) 4 := slice_fast_direct sl_13_3_ok low_7
set_option maxRecDepth 500000 in
lemma slices_13_ok : btAll (fun o => ∀ p, o = some p → Slice R_13 G_13 p.1 p.2) slices_13 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_13 G_13 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_13_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_13 G_13 c) P_13 := buildPoolsBT_sound slices_13_ok
def bk_13_init : BT (List (List Nat)) := BT.empty
lemma bk_13_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 (0 - 1) xs.toFinset) bk_13_init := trivial
def nodes_13_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_0 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_init 0 nodes_13_0 = true := by decide +kernel
def bk_13_0 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_0
set_option maxRecDepth 500000 in
lemma bk_13_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 0 xs.toFinset) bk_13_0 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_init_ok chk_13_0
def nodes_13_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_1 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_0 1 nodes_13_1 = true := by decide +kernel
def bk_13_1 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_1
set_option maxRecDepth 500000 in
lemma bk_13_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 1 xs.toFinset) bk_13_1 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_0_ok chk_13_1
def nodes_13_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_2 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_1 2 nodes_13_2 = true := by decide +kernel
def bk_13_2 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_2
set_option maxRecDepth 500000 in
lemma bk_13_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 2 xs.toFinset) bk_13_2 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_1_ok chk_13_2
def nodes_13_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_3 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_2 3 nodes_13_3 = true := by decide +kernel
def bk_13_3 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_3
set_option maxRecDepth 500000 in
lemma bk_13_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 3 xs.toFinset) bk_13_3 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_2_ok chk_13_3
def nodes_13_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_4 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_3 4 nodes_13_4 = true := by decide +kernel
def bk_13_4 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_4
set_option maxRecDepth 500000 in
lemma bk_13_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 4 xs.toFinset) bk_13_4 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_3_ok chk_13_4
def nodes_13_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_5 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_4 5 nodes_13_5 = true := by decide +kernel
def bk_13_5 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_5
set_option maxRecDepth 500000 in
lemma bk_13_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 5 xs.toFinset) bk_13_5 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_4_ok chk_13_5
def nodes_13_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_6 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_5 6 nodes_13_6 = true := by decide +kernel
def bk_13_6 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_6
set_option maxRecDepth 500000 in
lemma bk_13_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 6 xs.toFinset) bk_13_6 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_5_ok chk_13_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck R_13 G_13 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT bk_13_6 R_13 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_13 : Lower R_13 G_13 7 := lower_of_forestBT root_13_ok bk_13_6_ok root_13_in

end Cofactor12058
def h39R : List Nat := varsOf 15
def h39G : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 7 := carry_of (swaps := [(3,4),(4,5),(0,1),(1,2),(2,3),(3,4)]) (roots2 := Cofactor12058.R_13) (T2 := Cofactor12058.G_13) (by decide +kernel) Cofactor12058.low_13
def h40R : List Nat := varsOf 23
def h40G : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 7 := carry_of (swaps := [(3,4)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h42R : List Nat := varsOf 28
def h42G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bound : Lower h42R h42G 4 := carry_of (swaps := [(1,2),(2,3),(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h41R : List Nat := varsOf 29
def h41G : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h42Bound
namespace Cofactor12116
def G_0 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def R_0 : List Nat := varsOf 44
def pos_0 : List Nat := [12,12,36,36,40,40,12,36,40]
def neg_0 : List Nat := [8,4,32,4,32,8,32,8,4]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 2,12,8),(VAR 3,12,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_8 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def R_8 : List Nat := varsOf 14
lemma low_8_ok : carryOK [(1,4),(1,5),(1,3),(1,2)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0

def G_9 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_9 : List Nat := varsOf 22
lemma low_9_ok : carryOK [(4,5),(1,3),(1,2)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0

def G_10 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_10 : List Nat := varsOf 38
lemma low_10_ok : carryOK [(1,3),(1,2)] R_10 G_10 R_0 G_0 = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 4 := carry_of low_10_ok low_0

def G_13 : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
def R_13 : List Nat := varsOf 26
lemma low_13_ok : carryOK [(4,5),(1,2)] R_13 G_13 R_0 G_0 = true := by decide +kernel
lemma low_13 : Lower R_13 G_13 4 := carry_of low_13_ok low_0

def G_14 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def R_14 : List Nat := varsOf 42
lemma low_14_ok : carryOK [(1,2)] R_14 G_14 R_0 G_0 = true := by decide +kernel
lemma low_14 : Lower R_14 G_14 4 := carry_of low_14_ok low_0

def G_15 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def R_15 : List Nat := varsOf 28
lemma low_15_ok : carryOK [(4,5)] R_15 G_15 R_0 G_0 = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 4 := carry_of low_15_ok low_0

def G_17 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def R_17 : List Nat := varsOf 50
lemma low_17_ok : carryOK [(3,4),(1,2)] R_17 G_17 R_0 G_0 = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 4 := carry_of low_17_ok low_0

def G_18 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def R_18 : List Nat := varsOf 52
lemma low_18_ok : carryOK [(3,4)] R_18 G_18 R_0 G_0 = true := by decide +kernel
lemma low_18 : Lower R_18 G_18 4 := carry_of low_18_ok low_0

def G_20 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
def R_20 : List Nat := varsOf 46
def pos_20 : List Nat := [14,14,14,38,38,38,42,42,42,44,44,44,14,14,14,38,38,38,42,42,42,44,44,44]
def neg_20 : List Nat := [12,10,6,36,34,6,40,34,10,40,36,12,34,36,40,10,12,40,6,12,36,6,10,34]
def fmask_20 : Nat := fullMask 24
def base_20 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_20 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def W_20 : BT Decor := buildWiresBT 4 base_20 steps_20
def autosL_20 : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)],[(2,3)],[(2,5),(2,3)],[(1,2),(1,3)],[(2,5),(1,2),(1,3)],[(2,5),(1,3)]]
def autos_20 : BT (List (Nat × Nat)) := btOfList 4 autosL_20
def slicesL_20 : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def slices_20 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_20
def ps_20 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_20 : BT (Option BoundPool) := buildPoolsBT 2 W_20 R_20 slices_20 ps_20
lemma gp_20 : goodPairs G_20 pos_20 neg_20 := goodPairs_of (by decide +kernel)
lemma base_20_ok : ∀ x ∈ base_20, faithful pos_20 neg_20 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_20_ok : btAll (fun x => faithful pos_20 neg_20 x ∧ x.1 < 2^128) W_20 := buildWiresBT_faithful base_20_ok
set_option maxRecDepth 500000 in
lemma autos_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_20 = G_20) autos_20 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_20_0_ok : sliceDirectCheck 0 8 0 R_20 G_20 R_10 G_10 = true := by decide +kernel
lemma sl_20_0 : Slice R_20 G_20 (subcubeFast 0 8) 4 := slice_fast_direct sl_20_0_ok low_10
lemma sl_20_1_ok : sliceDirectCheck 0 2 0 R_20 G_20 R_0 G_0 = true := by decide +kernel
lemma sl_20_1 : Slice R_20 G_20 (subcubeFast 0 2) 4 := slice_fast_direct sl_20_1_ok low_0
lemma sl_20_2_ok : sliceDirectCheck 0 4 0 R_20 G_20 R_14 G_14 = true := by decide +kernel
lemma sl_20_2 : Slice R_20 G_20 (subcubeFast 0 4) 4 := slice_fast_direct sl_20_2_ok low_14
lemma sl_20_3_ok : sliceDirectCheck 0 32 0 R_20 G_20 R_8 G_8 = true := by decide +kernel
lemma sl_20_3 : Slice R_20 G_20 (subcubeFast 0 32) 4 := slice_fast_direct sl_20_3_ok low_8
set_option maxRecDepth 500000 in
lemma slices_20_ok : btAll (fun o => ∀ p, o = some p → Slice R_20 G_20 p.1 p.2) slices_20 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_20 G_20 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_20_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_20 G_20 c) P_20 := buildPoolsBT_sound slices_20_ok
def bk_20_init : BT (List (List Nat)) := BT.empty
lemma bk_20_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 (0 - 1) xs.toFinset) bk_20_init := trivial
def nodes_20_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_0 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_init 0 nodes_20_0 = true := by decide +kernel
def bk_20_0 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_0
set_option maxRecDepth 500000 in
lemma bk_20_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 0 xs.toFinset) bk_20_0 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_init_ok chk_20_0
def nodes_20_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_1 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_0 1 nodes_20_1 = true := by decide +kernel
def bk_20_1 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_1
set_option maxRecDepth 500000 in
lemma bk_20_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 1 xs.toFinset) bk_20_1 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_0_ok chk_20_1
def nodes_20_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_2 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_1 2 nodes_20_2 = true := by decide +kernel
def bk_20_2 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_2
set_option maxRecDepth 500000 in
lemma bk_20_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 2 xs.toFinset) bk_20_2 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_1_ok chk_20_2
def nodes_20_3 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_3 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_2 3 nodes_20_3 = true := by decide +kernel
def bk_20_3 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_3
set_option maxRecDepth 500000 in
lemma bk_20_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 3 xs.toFinset) bk_20_3 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_2_ok chk_20_3
def nodes_20_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_4 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_3 4 nodes_20_4 = true := by decide +kernel
def bk_20_4 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_4
set_option maxRecDepth 500000 in
lemma bk_20_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 4 xs.toFinset) bk_20_4 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_3_ok chk_20_4
def nodes_20_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_5 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_4 5 nodes_20_5 = true := by decide +kernel
def bk_20_5 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_5
set_option maxRecDepth 500000 in
lemma bk_20_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 5 xs.toFinset) bk_20_5 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_4_ok chk_20_5
def nodes_20_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_6 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_5 6 nodes_20_6 = true := by decide +kernel
def bk_20_6 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_6
set_option maxRecDepth 500000 in
lemma bk_20_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 6 xs.toFinset) bk_20_6 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_5_ok chk_20_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck R_20 G_20 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT bk_20_6 R_20 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_20 : Lower R_20 G_20 7 := lower_of_forestBT root_20_ok bk_20_6_ok root_20_in

def G_21 : Nat := 0xfcc0fcc0fc00fc00fcc0fcc0fc00fc00
def R_21 : List Nat := varsOf 46
lemma low_21_ok : liftCheck 0 32 R_21 G_21 R_8 G_8 [(VAR 5,38,6)] = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 5 := lift_of low_21_ok low_8

def G_22 : Nat := 0xfff0f000f000f000fff0f000f000f000
def R_22 : List Nat := varsOf 60
lemma low_22_ok : liftCheck 0 16 R_22 G_22 R_0 G_0 [(VAR 4,52,36)] = true := by decide +kernel
lemma low_22 : Lower R_22 G_22 5 := lift_of low_22_ok low_0

def G_23 : Nat := 0xfffcfffcfcc0fcc0fffcfffcfcc0fcc0
def R_23 : List Nat := varsOf 46
def pos_23 : List Nat := [6,6,10,10,12,12,34,34,36,36,40,40,6,6,10,10,12,12,34,34,36,36,40,40]
def neg_23 : List Nat := [4,2,8,2,8,4,32,2,32,4,32,8,8,32,4,32,2,32,4,8,2,8,2,4]
def fmask_23 : Nat := fullMask 24
def base_23 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf0cf,0x51008a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x333333,0x844221),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def steps_23 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_23 : BT Decor := buildWiresBT 4 base_23 steps_23
def autosL_23 : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)],[(2,3)],[(2,5),(2,3)],[(1,2),(1,3)],[(2,5),(1,2),(1,3)],[(2,5),(1,3)]]
def autos_23 : BT (List (Nat × Nat)) := btOfList 4 autosL_23
def slicesL_23 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,4),some (subcubeFast 2 0,4),some (subcubeFast 32 0,4),some (subcubeFast 8 0,4)]
def slices_23 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_23
def ps_23 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_23 : BT (Option BoundPool) := buildPoolsBT 2 W_23 R_23 slices_23 ps_23
lemma gp_23 : goodPairs G_23 pos_23 neg_23 := goodPairs_of (by decide +kernel)
lemma base_23_ok : ∀ x ∈ base_23, faithful pos_23 neg_23 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_23_ok : btAll (fun x => faithful pos_23 neg_23 x ∧ x.1 < 2^128) W_23 := buildWiresBT_faithful base_23_ok
set_option maxRecDepth 500000 in
lemma autos_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_23 = G_23) autos_23 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_23_0_ok : sliceDirectCheck 4 0 0 R_23 G_23 R_14 G_14 = true := by decide +kernel
lemma sl_23_0 : Slice R_23 G_23 (subcubeFast 4 0) 4 := slice_fast_direct sl_23_0_ok low_14
lemma sl_23_1_ok : sliceDirectCheck 2 0 0 R_23 G_23 R_0 G_0 = true := by decide +kernel
lemma sl_23_1 : Slice R_23 G_23 (subcubeFast 2 0) 4 := slice_fast_direct sl_23_1_ok low_0
lemma sl_23_2_ok : sliceDirectCheck 32 0 0 R_23 G_23 R_8 G_8 = true := by decide +kernel
lemma sl_23_2 : Slice R_23 G_23 (subcubeFast 32 0) 4 := slice_fast_direct sl_23_2_ok low_8
lemma sl_23_3_ok : sliceDirectCheck 8 0 0 R_23 G_23 R_10 G_10 = true := by decide +kernel
lemma sl_23_3 : Slice R_23 G_23 (subcubeFast 8 0) 4 := slice_fast_direct sl_23_3_ok low_10
set_option maxRecDepth 500000 in
lemma slices_23_ok : btAll (fun o => ∀ p, o = some p → Slice R_23 G_23 p.1 p.2) slices_23 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_23 G_23 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_23_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_23 G_23 c) P_23 := buildPoolsBT_sound slices_23_ok
def bk_23_init : BT (List (List Nat)) := BT.empty
lemma bk_23_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 (0 - 1) xs.toFinset) bk_23_init := trivial
def nodes_23_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_0 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_init 0 nodes_23_0 = true := by decide +kernel
def bk_23_0 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_0
set_option maxRecDepth 500000 in
lemma bk_23_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 0 xs.toFinset) bk_23_0 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_init_ok chk_23_0
def nodes_23_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_1 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_0 1 nodes_23_1 = true := by decide +kernel
def bk_23_1 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_1
set_option maxRecDepth 500000 in
lemma bk_23_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 1 xs.toFinset) bk_23_1 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_0_ok chk_23_1
def nodes_23_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_2 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_1 2 nodes_23_2 = true := by decide +kernel
def bk_23_2 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_2
set_option maxRecDepth 500000 in
lemma bk_23_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 2 xs.toFinset) bk_23_2 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_1_ok chk_23_2
def nodes_23_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_3 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_2 3 nodes_23_3 = true := by decide +kernel
def bk_23_3 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_3
set_option maxRecDepth 500000 in
lemma bk_23_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 3 xs.toFinset) bk_23_3 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_2_ok chk_23_3
def nodes_23_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_4 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_3 4 nodes_23_4 = true := by decide +kernel
def bk_23_4 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_4
set_option maxRecDepth 500000 in
lemma bk_23_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 4 xs.toFinset) bk_23_4 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_3_ok chk_23_4
def nodes_23_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_5 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_4 5 nodes_23_5 = true := by decide +kernel
def bk_23_5 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_5
set_option maxRecDepth 500000 in
lemma bk_23_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 5 xs.toFinset) bk_23_5 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_4_ok chk_23_5
def nodes_23_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_6 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_5 6 nodes_23_6 = true := by decide +kernel
def bk_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_6
set_option maxRecDepth 500000 in
lemma bk_23_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 6 xs.toFinset) bk_23_6 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_5_ok chk_23_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck R_23 G_23 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT bk_23_6 R_23 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_23 : Lower R_23 G_23 7 := lower_of_forestBT root_23_ok bk_23_6_ok root_23_in

def G_24 : Nat := 0xfffffff0fff0ff00fffffff0fff0ff00
def R_24 : List Nat := varsOf 60
lemma low_24_ok : liftCheck 8 0 R_24 G_24 R_18 G_18 [(VAR 3,8,0)] = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 5 := lift_of low_24_ok low_18

def G_41 : Nat := 0xfcc0fc00fcc0fc00fcc0fc00fcc0fc00
def R_41 : List Nat := varsOf 30
lemma low_41_ok : carryOK [(4,5)] R_41 G_41 R_21 G_21 = true := by decide +kernel
lemma low_41 : Lower R_41 G_41 5 := carry_of low_41_ok low_21

def G_42 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def R_42 : List Nat := varsOf 54
lemma low_42_ok : carryOK [(3,4)] R_42 G_42 R_20 G_20 = true := by decide +kernel
lemma low_42 : Lower R_42 G_42 7 := carry_of low_42_ok low_20

def G_48 : Nat := 0xffcccc00cc00cc00ffcccc00cc00cc00
def R_48 : List Nat := varsOf 58
lemma low_48_ok : carryOK [(1,2)] R_48 G_48 R_22 G_22 = true := by decide +kernel
lemma low_48 : Lower R_48 G_48 5 := carry_of low_48_ok low_22

def G_53 : Nat := 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0
def R_53 : List Nat := varsOf 30
lemma low_53_ok : carryOK [(4,5)] R_53 G_53 R_23 G_23 = true := by decide +kernel
lemma low_53 : Lower R_53 G_53 7 := carry_of low_53_ok low_23

def G_54 : Nat := 0xffffffccffccff00ffffffccffccff00
def R_54 : List Nat := varsOf 58
lemma low_54_ok : carryOK [(1,2)] R_54 G_54 R_24 G_24 = true := by decide +kernel
lemma low_54 : Lower R_54 G_54 5 := carry_of low_54_ok low_24

def G_60 : Nat := 0xfffcfcc0fcc0fc00fffcfcc0fcc0fc00
def R_60 : List Nat := varsOf 62
def pos_60 : List Nat := [10,10,12,12,14,22,22,22,26,26,28,28,38,38,38,42,42,44,44,50,50,50,52,52,52,56,56,56,10,10,10,10,10,10,10,10,12,12,12,12,12,12,12,12,22,22,22,22,22,38,38,38,38,38,50,50,50,50,50,52,52,52,52,52,56,56,56,56,56]
def neg_60 : List Nat := [8,2,8,4,6,20,18,6,24,18,24,20,36,34,6,40,34,40,36,48,34,18,48,36,20,48,40,24,6,18,20,24,34,36,40,48,6,18,20,24,34,36,40,48,24,34,36,40,48,18,20,24,40,48,6,20,24,36,40,6,18,24,34,40,6,18,20,34,36]
def fmask_60 : Nat := fullMask 69
def base_60 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x7fff00ff039f3f3,0xb58422131303162d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf83ffff001c67cfc,0x150ac44252518458b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f00000ffffe078f1f,0xa51894848c028505),(0xffff0000ffff0000ffff0000ffff0000,0x1fffc1f0000ff80fe0,0x631af18e8eb680f60),(0xffffffff00000000ffffffff00000000,0x1ffffe00000ffff000,0x18c631ef0f06dfb000)]
def steps_60 : List (Nat × Nat × Nat) := [(0,3,4),(3,0,3),(0,0,3),(2,0,2),(1,0,2),(0,0,1),(1,0,1),(3,2,3),(2,0,1),(1,0,5),(3,12,4),(3,12,0),(1,12,0),(3,1,4),(3,6,4),(0,6,4),(1,6,2),(3,6,1),(0,12,4),(0,1,4),(1,2,5),(3,7,1),(1,7,1),(0,8,3),(3,8,1),(3,2,4),(0,9,3),(0,1,9),(0,7,4),(0,1,3),(3,0,1),(2,13,2),(1,13,2),(3,1,3),(2,0,5),(1,7,2),(3,9,3),(3,13,3),(0,13,3),(2,10,2),(1,6,1),(3,7,4),(3,11,3),(0,11,3),(2,11,2),(1,10,2),(3,1,9),(3,8,3),(3,10,3),(1,11,2),(1,8,1),(0,10,3),(3,0,25),(2,0,25),(1,0,25),(0,0,25),(1,39,2),(1,39,1),(3,2,14),(1,1,5),(1,30,1),(1,18,2),(1,7,24),(1,33,2),(3,1,40),(0,40,4),(0,1,40),(1,26,2),(2,27,2),(2,1,5),(3,38,4),(3,34,4),(1,0,34),(2,9,5),(1,33,1),(0,9,4),(3,31,4),(0,31,4),(3,33,1),(2,1,31),(3,38,9),(3,40,4),(3,34,9),(1,34,2),(3,51,3),(3,1,14),(1,22,2),(0,32,3),(0,11,4),(3,10,11),(0,54,3),(2,11,5),(0,50,3),(1,13,34),(3,13,9),(1,34,9),(1,48,2),(3,48,4),(1,8,34),(3,50,3),(1,13,5),(0,34,4),(0,48,4),(3,56,4),(1,56,2),(2,0,34),(1,8,5),(1,10,5),(2,1,40),(3,32,3),(1,1,40),(1,11,5),(3,60,1),(1,60,1),(3,7,65),(2,67,2),(2,1,68),(0,1,68),(1,24,2),(0,115,4),(1,106,2),(3,39,9),(2,55,5),(2,1,82),(3,92,4),(0,0,88),(1,24,40),(3,71,4),(3,110,9),(3,23,11),(3,0,88),(2,49,5),(3,2,105),(1,23,13),(0,94,3),(3,24,40),(1,37,5),(0,1,59),(3,2,116),(3,39,11),(3,10,25),(1,107,2),(1,1,68),(2,54,5),(2,94,2),(3,13,25),(0,11,25),(3,1,59),(3,1,68),(2,50,5),(1,23,10),(1,51,34),(3,94,3),(1,94,2),(1,51,5),(3,44,11),(1,96,2),(3,74,9),(3,106,9),(3,2,112),(1,50,5),(3,60,59),(3,39,54),(3,157,4),(3,139,4),(1,94,5),(1,10,107),(3,71,115),(1,157,2),(3,12,94),(2,94,5),(1,12,94),(0,149,3),(1,139,2),(0,158,3),(0,157,4),(0,139,4),(3,158,3),(3,149,3),(3,174,4),(1,181,2),(0,11,165)]
def W_60 : BT Decor := buildWiresBT 8 base_60 steps_60
def autosL_60 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)]]
def autos_60 : BT (List (Nat × Nat)) := btOfList 2 autosL_60
def slicesL_60 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,7),some (subcubeFast 0 32,7),some (subcubeFast 2 32,4),some (subcubeFast 4 32,4),some (subcubeFast 4 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 16,4),some (subcubeFast 8 2,4),some (subcubeFast 2 0,5),some (subcubeFast 8 0,7),some (subcubeFast 16 0,5),some (subcubeFast 32 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 32,4),some (subcubeFast 32 16,4),some (subcubeFast 16 32,4),some (subcubeFast 8 4,4),some (subcubeFast 2 16,4),some (subcubeFast 8 16,4)]
def slices_60 : BT (Option (Nat × Nat)) := btOfList 5 slicesL_60
def ps_60 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(9,[(0,0,3),(0,7,4)]),(10,[]),(11,[]),(12,[]),(1,[(1,0,2),(1,0,5),(1,2,5)]),(13,[]),(14,[]),(15,[]),(16,[]),(1,[(1,0,1),(1,11,5),(3,2,116)]),(1,[(1,0,1),(1,0,5),(1,1,5)]),(1,[(1,0,1),(1,11,2),(2,54,5)]),(1,[(1,0,2),(1,9,5),(3,1,59)]),(1,[(1,2,5),(3,0,25)]),(9,[(0,3,4),(2,0,5)]),(1,[(1,0,5),(3,2,14)]),(1,[(1,0,5),(1,2,5)]),(1,[(1,0,5),(1,1,5)]),(17,[]),(9,[(0,0,3),(3,7,1)]),(9,[(0,3,4),(2,1,5)]),(9,[(0,1,3),(0,3,4)]),(9,[(0,1,3),(3,34,4)]),(1,[(1,0,2),(2,9,5)]),(0,[(1,0,2),(2,9,5)]),(9,[(0,3,4),(2,9,5)]),(1,[(1,0,2),(1,9,5)]),(0,[(1,0,2),(1,2,5)]),(1,[(1,0,2),(1,2,5)]),(1,[(1,0,2),(1,0,5)]),(18,[]),(1,[(1,0,1),(1,0,5)]),(0,[(1,0,2),(3,34,9)]),(0,[(1,0,2),(1,34,2)]),(0,[(1,0,2),(3,1,9)]),(1,[(1,0,2),(3,1,9)]),(1,[(1,0,5),(3,1,14)]),(1,[(1,0,1),(2,11,5)]),(9,[(0,0,3),(0,3,4)]),(1,[(1,0,1),(1,11,2)]),(9,[(0,1,3),(0,34,4)]),(9,[(0,1,3),(2,0,34)]),(1,[(1,0,1),(2,11,2)]),(0,[(1,0,1),(2,11,2)]),(1,[(1,0,1),(1,0,2)]),(1,[(1,0,1),(1,11,5)]),(1,[(1,0,5)]),(9,[(0,12,4)]),(9,[(0,3,4)]),(9,[(0,8,3)]),(0,[(1,0,2)]),(1,[(1,0,2)]),(9,[(0,1,9)]),(9,[(0,1,3)]),(9,[(0,0,3)]),(9,[(0,0,1)]),(0,[(1,0,1)]),(9,[(0,0,3),(3,7,4)]),(0,[(1,7,2)]),(1,[(1,2,5)]),(9,[(0,9,3)]),(0,[(1,0,1),(1,11,2)]),(1,[(1,0,1)]),(0,[(1,0,1),(1,0,2)])]
def P_60 : BT (Option BoundPool) := buildPoolsBT 7 W_60 R_60 slices_60 ps_60
lemma gp_60 : goodPairs G_60 pos_60 neg_60 := goodPairs_of (by decide +kernel)
lemma base_60_ok : ∀ x ∈ base_60, faithful pos_60 neg_60 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_60_ok : btAll (fun x => faithful pos_60 neg_60 x ∧ x.1 < 2^128) W_60 := buildWiresBT_faithful base_60_ok
set_option maxRecDepth 500000 in
lemma autos_60_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_60 = G_60) autos_60 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_60_0_ok : sliceDirectCheck 0 16 0 R_60 G_60 R_23 G_23 = true := by decide +kernel
lemma sl_60_0 : Slice R_60 G_60 (subcubeFast 0 16) 7 := slice_fast_direct sl_60_0_ok low_23
lemma sl_60_1_ok : sliceDirectCheck 0 32 0 R_60 G_60 R_53 G_53 = true := by decide +kernel
lemma sl_60_1 : Slice R_60 G_60 (subcubeFast 0 32) 7 := slice_fast_direct sl_60_1_ok low_53
lemma sl_60_2_ok : sliceDirectCheck 2 32 0 R_60 G_60 R_15 G_15 = true := by decide +kernel
lemma sl_60_2 : Slice R_60 G_60 (subcubeFast 2 32) 4 := slice_fast_direct sl_60_2_ok low_15
lemma sl_60_3_ok : sliceDirectCheck 4 32 0 R_60 G_60 R_13 G_13 = true := by decide +kernel
lemma sl_60_3 : Slice R_60 G_60 (subcubeFast 4 32) 4 := slice_fast_direct sl_60_3_ok low_13
lemma sl_60_4_ok : sliceDirectCheck 4 0 0 R_60 G_60 R_48 G_48 = true := by decide +kernel
lemma sl_60_4 : Slice R_60 G_60 (subcubeFast 4 0) 5 := slice_fast_direct sl_60_4_ok low_48
lemma sl_60_5_ok : sliceDirectCheck 0 2 0 R_60 G_60 R_24 G_24 = true := by decide +kernel
lemma sl_60_5 : Slice R_60 G_60 (subcubeFast 0 2) 5 := slice_fast_direct sl_60_5_ok low_24
lemma sl_60_6_ok : sliceDirectCheck 4 16 0 R_60 G_60 R_14 G_14 = true := by decide +kernel
lemma sl_60_6 : Slice R_60 G_60 (subcubeFast 4 16) 4 := slice_fast_direct sl_60_6_ok low_14
lemma sl_60_7_ok : sliceDirectCheck 8 2 0 R_60 G_60 R_18 G_18 = true := by decide +kernel
lemma sl_60_7 : Slice R_60 G_60 (subcubeFast 8 2) 4 := slice_fast_direct sl_60_7_ok low_18
lemma sl_60_8_ok : sliceDirectCheck 2 0 0 R_60 G_60 R_22 G_22 = true := by decide +kernel
lemma sl_60_8 : Slice R_60 G_60 (subcubeFast 2 0) 5 := slice_fast_direct sl_60_8_ok low_22
lemma sl_60_9_ok : sliceDirectCheck 8 0 0 R_60 G_60 R_42 G_42 = true := by decide +kernel
lemma sl_60_9 : Slice R_60 G_60 (subcubeFast 8 0) 7 := slice_fast_direct sl_60_9_ok low_42
lemma sl_60_10_ok : sliceDirectCheck 16 0 0 R_60 G_60 R_21 G_21 = true := by decide +kernel
lemma sl_60_10 : Slice R_60 G_60 (subcubeFast 16 0) 5 := slice_fast_direct sl_60_10_ok low_21
lemma sl_60_11_ok : sliceDirectCheck 32 0 0 R_60 G_60 R_41 G_41 = true := by decide +kernel
lemma sl_60_11 : Slice R_60 G_60 (subcubeFast 32 0) 5 := slice_fast_direct sl_60_11_ok low_41
lemma sl_60_12_ok : sliceDirectCheck 0 4 0 R_60 G_60 R_54 G_54 = true := by decide +kernel
lemma sl_60_12 : Slice R_60 G_60 (subcubeFast 0 4) 5 := slice_fast_direct sl_60_12_ok low_54
lemma sl_60_13_ok : sliceDirectCheck 8 32 0 R_60 G_60 R_9 G_9 = true := by decide +kernel
lemma sl_60_13 : Slice R_60 G_60 (subcubeFast 8 32) 4 := slice_fast_direct sl_60_13_ok low_9
lemma sl_60_14_ok : sliceDirectCheck 32 16 0 R_60 G_60 R_8 G_8 = true := by decide +kernel
lemma sl_60_14 : Slice R_60 G_60 (subcubeFast 32 16) 4 := slice_fast_direct sl_60_14_ok low_8
lemma sl_60_15_ok : sliceDirectCheck 16 32 0 R_60 G_60 R_8 G_8 = true := by decide +kernel
lemma sl_60_15 : Slice R_60 G_60 (subcubeFast 16 32) 4 := slice_fast_direct sl_60_15_ok low_8
lemma sl_60_16_ok : sliceDirectCheck 8 4 0 R_60 G_60 R_17 G_17 = true := by decide +kernel
lemma sl_60_16 : Slice R_60 G_60 (subcubeFast 8 4) 4 := slice_fast_direct sl_60_16_ok low_17
lemma sl_60_17_ok : sliceDirectCheck 2 16 0 R_60 G_60 R_0 G_0 = true := by decide +kernel
lemma sl_60_17 : Slice R_60 G_60 (subcubeFast 2 16) 4 := slice_fast_direct sl_60_17_ok low_0
lemma sl_60_18_ok : sliceDirectCheck 8 16 0 R_60 G_60 R_10 G_10 = true := by decide +kernel
lemma sl_60_18 : Slice R_60 G_60 (subcubeFast 8 16) 4 := slice_fast_direct sl_60_18_ok low_10
set_option maxRecDepth 500000 in
lemma slices_60_ok : btAll (fun o => ∀ p, o = some p → Slice R_60 G_60 p.1 p.2) slices_60 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_60 G_60 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_60_0) (forall_cons (fun _ h => by cases h; exact sl_60_1) (forall_cons (fun _ h => by cases h; exact sl_60_2) (forall_cons (fun _ h => by cases h; exact sl_60_3) (forall_cons (fun _ h => by cases h; exact sl_60_4) (forall_cons (fun _ h => by cases h; exact sl_60_5) (forall_cons (fun _ h => by cases h; exact sl_60_6) (forall_cons (fun _ h => by cases h; exact sl_60_7) (forall_cons (fun _ h => by cases h; exact sl_60_8) (forall_cons (fun _ h => by cases h; exact sl_60_9) (forall_cons (fun _ h => by cases h; exact sl_60_10) (forall_cons (fun _ h => by cases h; exact sl_60_11) (forall_cons (fun _ h => by cases h; exact sl_60_12) (forall_cons (fun _ h => by cases h; exact sl_60_13) (forall_cons (fun _ h => by cases h; exact sl_60_14) (forall_cons (fun _ h => by cases h; exact sl_60_15) (forall_cons (fun _ h => by cases h; exact sl_60_16) (forall_cons (fun _ h => by cases h; exact sl_60_17) (forall_cons (fun _ h => by cases h; exact sl_60_18) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))
set_option maxRecDepth 500000 in
lemma P_60_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_60 G_60 c) P_60 := buildPoolsBT_sound slices_60_ok
def bk_60_init : BT (List (List Nat)) := BT.empty
lemma bk_60_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 (0 - 1) xs.toFinset) bk_60_init := trivial
def nodes_60_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_60_0 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_init 0 nodes_60_0 = true := by decide +kernel
def bk_60_0 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_0
set_option maxRecDepth 500000 in
lemma bk_60_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 0 xs.toFinset) bk_60_0 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_init_ok chk_60_0
def nodes_60_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_60_1 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_0 1 nodes_60_1 = true := by decide +kernel
def bk_60_1 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_1
set_option maxRecDepth 500000 in
lemma bk_60_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 1 xs.toFinset) bk_60_1 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_0_ok chk_60_1
def nodes_60_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_60_2 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_1 2 nodes_60_2 = true := by decide +kernel
def bk_60_2 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_2
set_option maxRecDepth 500000 in
lemma bk_60_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 2 xs.toFinset) bk_60_2 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_1_ok chk_60_2
def nodes_60_3 : List NodeSpec := [([48,2,170,4],[],[]),([94,146,3,4],[],[]),([174,157,2,4],[],[]),([94,184,2,3],[],[]),([175,157,2,4],[],[]),([94,185,3,4],[],[]),([186,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_60_3 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_2 3 nodes_60_3 = true := by decide +kernel
def bk_60_3 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_3
set_option maxRecDepth 500000 in
lemma bk_60_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 3 xs.toFinset) bk_60_3 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_2_ok chk_60_3
def nodes_60_4 : List NodeSpec := [([60,142,2,3,4],[],[0]),([166,1,2,3,4],[],[]),([120,0,1,2,5],[],[]),([121,153,0,3,4],[],[]),([0,1,2,131,5],[0,1],[]),([0,1,40,123,5],[2,3],[]),([0,71,2,124,3],[],[]),([48,11,2,112,4],[3],[]),([51,0,125,3,4],[],[]),([1,2,167,3,4],[],[]),([102,94,2,3,4],[],[]),([1,151,9,3,4],[],[]),([118,2,3,59,4],[],[0]),([94,168,2,3,4],[],[]),([10,151,2,3,4],[],[0]),([94,169,2,3,4],[],[]),([164,11,2,3,4],[],[]),([11,2,3,170,4],[4],[0,1]),([155,11,2,3,4],[],[]),([10,11,146,3,4],[],[0]),([171,11,2,3,4],[],[]),([96,94,2,3,4],[],[]),([94,48,2,5,4],[5,3],[0]),([172,0,2,3,4],[],[]),([94,157,48,2,4],[6],[]),([94,2,3,25,4],[],[]),([94,107,2,3,4],[4,7],[0]),([94,2,3,170,4],[],[]),([94,2,173,3,4],[],[]),([12,94,2,5,4],[3,7],[]),([23,94,2,3,4],[],[]),([174,94,2,3,4],[7,3],[0]),([118,9,3,25,4],[],[]),([94,158,50,3,4],[7],[]),([154,11,2,3,4],[],[]),([94,157,2,5,4],[3],[0]),([12,94,157,2,4],[7],[0]),([175,11,2,3,4],[],[]),([94,176,2,3,4],[],[]),([78,0,1,88,4],[],[]),([175,94,2,3,4],[3,6],[0,1]),([94,2,15,3,4],[],[]),([177,94,2,3,4],[],[]),([94,2,178,3,4],[],[]),([94,2,179,3,4],[],[]),([94,180,2,3,4],[],[]),([181,94,2,3,4],[7],[0]),([149,94,158,3,4],[7],[]),([139,94,157,2,4],[6],[]),([182,94,2,3,4],[],[]),([0,1,31,80,25],[],[]),([12,11,2,112,4],[3],[]),([94,2,183,3,4],[],[]),([11,2,3,165,4],[],[0]),([11,50,3,25,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_60_4 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_3 4 nodes_60_4 = true := by decide +kernel
def bk_60_4 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_4
set_option maxRecDepth 500000 in
lemma bk_60_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 4 xs.toFinset) bk_60_4 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_3_ok chk_60_4
def nodes_60_5 : List NodeSpec := [([58,57,1,2,3,4],[],[0]),([60,1,2,3,59,4],[],[0]),([117,0,2,3,25,4],[],[]),([0,118,2,3,25,4],[8],[0]),([63,0,1,3,25,4],[9,5],[]),([119,0,1,2,3,4],[],[]),([120,0,1,2,3,4],[],[0]),([121,0,1,68,3,4],[],[0]),([0,122,1,68,3,4],[10,8,11,12],[]),([0,1,40,123,3,4],[8,4],[0]),([113,69,0,2,3,4],[],[0]),([0,1,2,40,124,3],[13],[0]),([0,1,66,40,3,4],[13],[]),([0,1,72,40,3,4],[8],[]),([8,0,1,125,3,4],[11,5],[]),([74,0,55,2,3,4],[],[]),([57,1,9,3,25,4],[],[]),([69,26,0,2,3,4],[],[]),([60,1,9,3,25,4],[],[0]),([1,2,126,9,3,4],[8],[]),([127,0,1,2,3,4],[],[]),([1,9,3,14,25,4],[11,12,14],[]),([0,1,2,31,80,5],[15,5],[0]),([78,0,1,2,3,4],[],[]),([128,0,2,9,3,4],[],[]),([78,0,34,1,2,4],[13],[0]),([0,1,9,125,3,4],[4,11,16,17],[0]),([129,0,1,2,9,3],[],[]),([130,1,9,88,3,4],[18],[]),([86,0,1,2,40,5],[17],[]),([0,1,2,131,3,4],[0,1,11,13],[0]),([0,1,50,3,25,4],[11,12],[0]),([12,0,1,2,112,4],[3,0],[0]),([110,1,9,88,3,4],[4],[]),([132,0,1,2,40,3],[],[]),([1,133,2,9,3,4],[8],[]),([74,0,62,2,3,4],[],[]),([0,1,134,2,3,4],[],[]),([84,51,0,2,3,4],[],[]),([51,0,34,2,31,4],[5],[]),([51,0,9,88,3,4],[4],[]),([135,1,9,88,3,4],[],[]),([51,0,1,3,25,4],[],[]),([96,1,2,9,3,4],[9],[]),([39,51,1,2,3,4],[],[]),([51,0,34,2,5,4],[13],[]),([136,0,1,2,3,4],[],[]),([51,76,0,2,3,4],[],[]),([51,0,106,2,3,4],[5],[2,0]),([87,0,1,2,3,4],[],[]),([137,0,1,2,3,4],[],[]),([0,1,54,3,25,4],[11,12],[]),([138,0,1,2,3,4],[],[]),([0,1,61,3,25,4],[11,12],[]),([139,94,11,2,3,4],[6],[]),([0,32,34,2,31,4],[5],[]),([12,10,11,2,5,4],[3,7],[0]),([1,2,9,3,105,4],[],[]),([0,1,9,88,5,4],[3,18],[0]),([51,26,0,2,3,4],[],[]),([1,77,9,88,3,4],[4,11],[]),([13,35,2,15,3,4],[],[0]),([13,1,9,3,25,4],[],[]),([140,0,1,2,3,4],[],[]),([23,13,35,2,3,4],[],[0]),([39,1,2,54,3,4],[11,12],[0]),([96,8,1,2,3,4],[],[]),([0,1,2,3,141,4],[5],[]),([0,142,2,3,25,4],[5],[0]),([143,0,1,5,3,4],[19],[]),([1,144,11,2,3,4],[4,8],[]),([74,11,2,3,14,4],[4,11,12],[]),([11,2,3,14,64,4],[11,20,3],[]),([74,90,0,2,3,4],[],[]),([0,1,48,93,2,5],[5,13,3],[]),([145,0,1,2,3,4],[],[]),([0,1,11,146,3,4],[],[0]),([0,1,68,147,3,4],[8,11,16,17],[2]),([0,32,9,88,3,4],[6],[]),([0,1,31,9,88,4],[],[]),([96,0,1,2,3,4],[],[]),([87,0,1,2,5,4],[1],[]),([49,12,0,1,5,4],[7,18],[]),([10,11,2,15,3,4],[],[0]),([49,0,1,15,3,4],[],[]),([96,10,11,2,3,4],[4],[0]),([49,23,0,1,3,4],[5,13],[]),([39,49,1,2,3,4],[],[]),([74,8,11,2,3,4],[4],[]),([1,11,9,3,25,4],[],[0]),([148,0,1,2,3,4],[0,1,21],[]),([149,94,10,2,3,4],[7],[]),([0,1,150,2,3,4],[4],[]),([0,1,151,2,3,4],[5,13,11,9],[0,2]),([152,0,2,5,3,4],[22],[]),([78,1,11,2,3,4],[4],[]),([74,11,2,9,3,4],[4],[]),([78,13,1,2,3,4],[],[]),([153,0,1,68,3,4],[],[0]),([10,11,2,3,25,4],[4,5],[0]),([154,0,1,2,3,4],[],[0]),([155,0,1,2,3,4],[],[0]),([39,1,9,3,25,4],[11,12],[]),([0,1,31,9,25,4],[17],[0]),([0,34,2,156,3,4],[13],[]),([11,2,3,112,4],[6,3],[0,1]),([23,10,11,2,3,4],[4],[0]),([10,48,11,2,5,4],[5,3],[0]),([0,71,2,115,3,4],[],[0]),([102,10,11,2,3,4],[],[0]),([152,0,2,3,25,4],[],[]),([94,11,2,5,3,4],[5,6,3],[0,1]),([94,48,2,3,4],[6,7,3],[0]),([1,11,2,61,3,4],[4],[]),([94,157,2,3,4],[6,7,3],[0]),([1,99,2,31,3,4],[],[]),([11,2,50,5,3,4],[7,6,3],[0]),([94,10,2,158,3,4],[7],[0]),([11,2,5,3,112,4],[3,6],[]),([39,57,1,2,3,4],[],[]),([0,24,1,2,40,5],[3],[0]),([12,94,2,3,4],[6,7,3],[0]),([10,107,11,2,3,4],[4,7],[0]),([11,2,97,50,3,4],[4,7,6],[]),([139,94,2,3,4],[6,7,3],[0]),([0,1,67,2,5],[0,17],[0]),([73,0,1,40,3,4],[9,13],[]),([94,157,11,2,3,4],[6],[0]),([0,1,2,3,159,4],[5],[]),([94,2,5,3,4],[6,3,7],[0,1]),([160,2,3,4],[7,6,3],[]),([0,1,2,161,3,4],[0,1],[]),([0,1,2,162,3,4],[11],[]),([163,0,1,2,3,4],[11],[]),([12,0,1,2,105,4],[],[]),([164,0,1,2,3,4],[],[0]),([149,94,2,3,4],[7,6,3],[0,1]),([0,1,2,3,165,4],[13,5,1,0],[0]),([13,35,2,3,25,4],[],[0]),([12,13,35,2,5,4],[3,7],[0]),([104,11,2,50,3,4],[6],[]),([94,2,50,3,4],[7,4,6,3],[0]),([39,74,11,2,3,4],[4],[]),([94,2,158,3,4],[7,6,3],[0,1]),([0,1,37,3,25,4],[13],[]),([94,2,3,4],[7,6,3],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_60_5 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_4 5 nodes_60_5 = true := by decide +kernel
def bk_60_5 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_5
set_option maxRecDepth 500000 in
lemma bk_60_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 5 xs.toFinset) bk_60_5 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_4_ok chk_60_5
def nd_60_6_0 : List NodeSpec := [([57,0,1,2,5,3,4],[11,15,12,5,23],[0]),([58,0,1,2,3,25,4],[5,8],[0]),([0,1,2,3,25,59,4],[5,11,16,8,17],[0]),([60,0,1,2,3,25,4],[11,15,5,12,8],[0]),([0,1,2,61,5,3,4],[24,5,11,0,12,1,2],[0]),([0,1,62,2,5,3,4],[13,11,0,12,1,2],[0]),([0,1,2,61,3,4],[8,4,13,11,0,12,1],[0]),([63,0,1,2,5,3,4],[11,2,12,7,25],[0]),([0,1,2,3,14,25,4],[11,2,5,12,15,7,26],[0]),([0,1,2,3,14,64,4],[11,2,5,12,3,13,27],[0]),([6,0,1,65,2,3,4],[11,13,28,16],[]),([7,0,1,2,66,3,4],[15,11,3,18,12],[0]),([7,0,24,1,2,5],[17,2,16,3],[0,3]),([0,1,67,2,3,4],[0,5,2,17,16,9],[0]),([0,1,2,68,3,4],[8,10,4,13,11,12],[2]),([6,16,1,2,4],[11,8,7,17],[]),([69,7,0,1,2,3,4],[11,7,13],[0]),([0,1,2,70,40,3,4],[11,17,12],[]),([18,0,1,2,40,3,4],[7,13,3,17,12],[0]),([0,71,1,2,40,3,4],[7,8,13,11,17,4],[0,2]),([7,0,1,2,72,3,4],[29,13,8,5,11,0],[0]),([0,1,2,72,3,4],[8,5,4,11,0,12,1,3],[]),([73,7,0,1,2,3,4],[11,18,4],[0]),([0,1,27,2,40,3,4],[6,13,7],[2,0]),([74,8,0,1,2,3,4],[4,7,8,30],[0]),([8,0,1,75,2,3,4],[8,17,12,18],[]),([8,0,34,1,2,5,4],[11,2,16,17,31,18],[]),([8,76,0,1,2,3,4],[8,17,12,32],[]),([8,34,1,77,2,3,4],[11,8],[]),([0,1,55,2,5,3,4],[7,8,13,11,0,12,1,2],[0]),([78,0,1,2,5,3,4],[5,1,0,33],[]),([0,79,2,3,4],[13,8,11,12],[]),([78,0,1,2,9,3,4],[8,9,11],[]),([0,1,68,3,4],[8,11,12],[0]),([78,0,1,2,3,4],[11,9,4,13,8,0,1,34,33,35],[0,1]),([0,1,2,5,3,59,4],[3,0,36],[0]),([74,0,1,2,3,14,4],[5,2,11,12,4],[0]),([0,1,9,3,25,4],[15,8,11,37,12,38],[0,1]),([7,0,1,65,2,3,4],[13,3,11,12],[0]),([74,0,1,2,9,3,4],[5,8,4,11,16,17],[0,2]),([39,1,2,9,3,4],[18,8,11,12],[0]),([0,1,2,31,9,5,4],[5,0,15,17],[0]),([1,2,9,5,3,14,4],[7,11,12,8,39],[0]),([0,1,2,31,80,3,4],[11,15,0,12,40],[0]),([81,0,1,2,9,3,4],[0,1,5,17,12],[]),([39,74,0,1,2,3,4],[4,13,8],[0,2]),([0,1,2,82,9,3,4],[9,8,18],[0]),([83,0,2,3,4],[4,8,11,12],[]),([84,0,1,2,9,3,4],[5,8,0,40,4],[0]),([1,11,2,5,3,14,4],[3,11,12,8,41],[0]),([0,85,1,2,9,3,4],[11],[]),([86,0,1,2,40,3,4],[17,12],[0]),([0,34,1,2,9,5,4],[2,11,3,18,16],[0]),([87,0,1,2,3,4],[11,9,0,5,8,12,1,42],[0]),([76,0,1,2,9,3,4],[12,5,17,4,16],[0]),([0,34,1,9,88,3,4],[11,9,18,4],[0]),([39,0,1,2,3,25,4],[15,5,8],[0]),([0,1,9,88,3,4],[18,8,4,11,43,17],[0]),([0,1,89,2,9,3,4],[5,8,28,9,11,44],[0]),([51,0,1,2,5,3,4],[11,13,0,1,12,5,7,45],[0,1]),([0,32,1,2,31,3,4],[5,11,18,0,40,4],[0]),([90,0,1,2,5,3,4],[11,2,12,13,46],[0]),([0,1,9,5,3,25,4],[11,12,9,38],[0]),([38,0,32,2,9,3,4],[5,13],[]),([10,0,1,2,3,25,4],[15,4,8,5,13],[0]),([0,34,1,2,31,9,4],[5,0],[0]),([39,1,2,9,5,3,4],[5,24,11,12,2],[0]),([0,32,34,2,9,3,4],[5,13,6],[0]),([0,1,2,91,3,4],[7,4,6,12,1],[]),([13,35,2,5,3,4],[2,3,7,6],[0,1]),([13,1,2,5,3,14,4],[11,12,8,2],[]),([12,10,11,2,3,4],[4,6,7,3],[0]),([0,92,1,2,9,3,4],[9,8,15],[0]),([0,1,48,93,2,3,4],[11,3,0,12,6],[0]),([13,1,2,3,14,4],[5,7,11,2,4],[]),([7,1,2,14,4],[11,7,17],[]),([10,48,11,2,3,4],[4,6,5,7,3],[0]),([12,13,0,1,2,5,4],[40,11,3,17,16,7],[0]),([94,10,2,3,4],[5,7,6,3],[0]),([0,1,2,95,4],[5,13,11,17],[]),([96,0,1,2,5,3,4],[5,1,0,47],[]),([23,13,0,1,2,3,4],[11,13,5,8,16,17],[0]),([0,1,2,97,50,3,4],[4,7,6,11],[0]),([87,0,1,2,9,3,4],[8,9,11],[]),([0,1,2,40,5,4],[2,7,11,48,3],[2,0]),([0,1,98,2,3,4],[4,18,12,1,3],[]),([13,29,2,3,4],[8,4,7,3],[0]),([51,0,34,2,3,4],[13,0,5,18,44],[0]),([13,0,1,2,15,3,4],[13,17,12,16],[0]),([10,11,2,3,4],[4,5,7,3],[0]),([13,1,2,31,9,3,4],[5],[0]),([1,99,2,9,3,4],[9,5,18,8],[0,1]),([0,1,11,2,15,3,4],[15,12,5,17],[0]),([13,35,94,2,3,4],[13,7,6,3],[]),([87,0,34,1,2,3,4],[5,0,13],[]),([0,1,2,54,5,3,4],[5,13,7,11,0,12,1,49],[0,2]),([13,94,2,3,4],[5,13,18,6,28,3,2],[]),([0,1,2,50,3,4],[7,4,6,3],[]),([69,0,1,2,40,3,4],[7,11,4,13],[2,0]),([0,1,75,2,9,3,4],[3,13,12,5,17],[]),([12,0,1,11,2,5,4],[11,40,3,7,18,16,17],[0]),([0,1,48,11,2,5,4],[5,13,0,3,17],[0]),([0,34,1,2,100,3,4],[0,13,16,17],[0]),([18,0,1,2,21,3,4],[13,3,17],[]),([0,1,2,101,3,4],[0,5,7,13,18,11,17],[]),([96,0,1,2,3,4],[11,5,13,9,0],[0,2]),([102,0,1,11,2,3,4],[0,1,5,17,12],[0]),([0,34,1,103,2,3,4],[8],[]),([104,0,1,2,50,3,4],[6,11],[0]),([0,1,2,3,105,4],[2,11,5,28,9],[0,1]),([13,1,2,9,5,3,4],[8,7,2],[0]),([0,1,11,2,3,25,4],[5,8,13,4,15],[0,2]),([34,1,77,2,9,3,4],[8,7,11,4],[0]),([8,0,106,1,2,3,4],[11,7,8,50],[0]),([0,1,2,5,3,105,4],[13,0,1,2],[]),([94,0,2,3,4],[13,5,4,7,28,2],[]),([0,106,1,2,9,3,4],[5,8,9,11,4,16,17],[0]),([0,1,107,11,2,3,4],[5,8,4,7],[0]),([0,24,1,2,40,3,4],[7,4,13,12,1],[0]),([12,13,35,2,3,4],[13,18,5,7,6,3],[0]),([8,1,11,2,5,3,4],[3,7,8,18,2],[0]),([94,11,2,3,4],[4,7,6,3],[0,1]),([108,0,1,2,3],[8,4,12,11],[]),([10,11,2,5,3,4],[3,5,6,7],[0,1]),([32,11,2,3,4],[4,5,7,3],[]),([26,0,1,2,40,3,4],[7,13,4],[0,2]),([13,0,1,2,3,25,4],[15,16,11,13,5,8,4],[0]),([0,1,2,109,3,4],[8,4,11,17],[]),([110,34,1,2,9,3,4],[5,51,11,4],[0]),([57,0,1,2,3,25,4],[15,11,8,5],[0]),([0,1,2,5,3,111,4],[8,1,0,2],[]),([39,1,11,2,3,4],[4,8,11,12],[0,2]),([49,0,1,2,5,3,4],[11,7,0,12,1,13,52],[0,2,1]),([0,1,109,3,4],[4,8,11,17],[]),([0,1,2,5,3,112,4],[3,6],[0]),([113,0,1,2,40,3,4],[13,4],[0]),([110,1,2,9,3,4],[5,8,9,4,11,17,2],[0]),([12,10,0,1,2,5,4],[11,3,16,17,7],[0]),([0,1,11,2,5,3,4],[3,5,8,13,11,0,12],[0]),([0,1,2,3,112,4],[2,3,6,9],[0,1]),([49,12,0,1,3,4],[0,5,7,13,18,53],[0]),([96,0,1,11,2,3,4],[8,5,4,11],[0]),([10,0,1,2,15,3,4],[4,17,12],[0]),([94,0,1,2,3,4],[4,5,9,7,11,0,12,1,13,8],[]),([114,0,1,2,9,3,4],[11,0,18,6],[]),([51,0,1,2,31,3,4],[11,40,13],[0]),([0,1,2,50,5,3,4],[7,6,3,11,12],[0]),([0,1,2,40,115,3,4],[8,7,13,4,40,17],[0]),([94,10,11,2,3,4],[7,6,3],[]),([0,1,2,37,5,3,4],[7,8,11,18,0,1,12,2],[0]),([39,1,11,2,5,3,4],[3,5,11,12,2],[2]),([1,11,2,9,5,3,4],[3,18,15,5,54],[0]),([0,1,99,2,3,4],[5,8,11,0,12,1],[]),([94,2,3,4],[7,6,3],[0,1]),([30,7,0,1,2,5],[15,17,2,16,6,3,48,7],[]),([0,1,2,5,3,116,4],[15,0,55],[0]),([23,10,0,1,2,3,4],[11,4],[0]),([23,0,1,11,2,3,4],[5,8,13,4,11,15],[0]),([44,11,2,3,4],[4,7,3],[0]),([10,11,2,50,3,4],[4,7,6,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_60_6_0 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_5 6 nd_60_6_0 = true := by decide +kernel
def nd_60_6_1 : List NodeSpec := [([11,2,50,3,4],[7,4,6,3],[0,1]),([51,7,0,1,2,3,4],[11,40,13],[0]),([13,35,2,3,4],[13,5,7,3],[0]),([8,1,2,5,3,14,4],[11,12,8,2],[]),([51,0,34,2,9,3,4],[4,5,44],[0]),([26,0,1,2,9,3,4],[5,8,4,40],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_60_6_1 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_5 6 nd_60_6_1 = true := by decide +kernel
def nodes_60_6 : List NodeSpec := nd_60_6_0 ++ nd_60_6_1
set_option maxRecDepth 500000 in
lemma chk_60_6 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_5 6 nodes_60_6 = true := by
  unfold nodes_60_6 checkNodesBT; simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_60_6_0, chk_60_6_1⟩
def bk_60_6 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_6
set_option maxRecDepth 500000 in
lemma bk_60_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 6 xs.toFinset) bk_60_6 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_5_ok chk_60_6
def nodes_60_7 : List NodeSpec := [([0,1,2,5,3,14,4],[11,2,12,17,16,3,7,15,56],[0]),([0,1,2,15,3,4],[15,40,5,8,12,13,4],[0,2]),([16,0,1,2,3,4],[11,4,8,13,0,9,1,12,40,2],[0]),([0,17,1,2,3,4],[11,5,7,4,13,0,12,1,40,17],[3]),([18,6,0,1,2,3,4],[11,13,3,17,8,5,7,16,15],[3,0]),([0,19,1,2,3,4],[1,12,0,2,5,13,4,17,7,16],[2]),([20,0,1,2,3,4],[11,5,13,4,7,12],[]),([0,1,2,21,3,4],[7,13,4,11,40,17,12],[3,0]),([22,0,1,2,3,4],[4,0,13,9,11,1,12,5,7,6,3],[0]),([18,7,0,1,2,3,4],[11,13,3,17,8,5,7,16,15],[0]),([23,0,1,2,3,4],[11,5,8,13,4,57,12],[0,2]),([7,0,24,1,2,3,4],[17,2,16,13,4,15,7],[0,3]),([0,1,2,3,25,4],[15,58,11,16,8,5,4,13],[0,2]),([26,7,0,1,2,3,4],[13,6,11,5,0,7,17,29,8],[0,2]),([7,0,1,27,2,3,4],[11,8,6,18,17,7],[0,2]),([8,0,1,2,5,3,4],[15,3,2,58,7,11,0,12,1,18,28],[0,1]),([28,0,1,2,3,4],[11,8,13,4,59,1,12,17],[]),([0,29,1,2,3,4],[9,4,5,8,7,0,11,1,12,3],[0]),([0,1,2,9,5,3,4],[2,15,5,28,3,18,60,61,58,11,12],[0,1]),([30,6,0,1,2,3,4],[11,12,15,17,8,5,16,6,18,3,7],[0]),([7,0,1,2,5,4],[0,11,3,1,2,48],[0,2]),([0,1,2,31,9,3,4],[5,7,18,60,15,17],[0]),([0,32,1,2,9,3,4],[5,18,7,40,15,6,3],[0,1]),([0,32,1,2,3,4],[4,9,13,5,7,6,3,62],[0]),([33,0,1,2,3,4],[11,8,13,4,9,12,10],[0,2]),([8,0,1,9,3,4],[9,8,5,28,2],[]),([8,0,34,1,2,3,4],[18,11,8,7,28,4,63,17,16,15],[0]),([13,35,2,3,4],[13,18,6,28,3,2,7],[0,2,1]),([36,0,1,2,3,4],[13,8,18,0,11,1,12,2],[]),([0,1,2,37,3,4],[8,7,13,18,0,11,1,12,2,28],[0]),([38,0,1,2,9,3,4],[8,5,18,6,60,15,28,16,17],[0]),([7,0,1,2,9,3,4],[8,18,7,40,15,2,6,11],[0]),([13,0,11,2,3,4],[13,5,9,7,2],[0]),([13,35,0,1,2,3,4],[13,5,7,6,3],[0]),([39,0,1,2,3,4],[11,4,8,13,9,0,1,12,24,16,17],[0,2]),([7,0,1,2,40,3,4],[11,8,7,17,64,6],[0,2]),([41,0,1,2,3,4],[11,5,13,4,7,1,12,17],[]),([0,1,11,2,3,4],[5,4,7,13,11,0,12,1,3,6],[0]),([6,7,0,1,2,4],[9,0,11,17,7],[]),([0,1,42,2,3,4],[8,13,6,0,11,28,17],[]),([10,0,1,2,3,4],[4,13,9,0,11,1,12,5,8,7,6,3],[0]),([43,0,1,2,3,4],[11,8,13,18,1,12],[]),([44,0,1,2,3,4],[4,8,65,0,11,1,12,3],[0]),([12,0,1,11,2,3,4],[8,5,4,13,11,7,40,6,3,18,16,17,66],[0]),([0,1,45,2,3,4],[13,5,4,7,11,6,28,18,12,1],[]),([46,0,1,2,3,4],[0,8,1,12,13,4,17,2,67],[2]),([47,0,1,2,3,4],[11,5,13,7,1,12],[]),([13,10,1,2,3,4],[9,13,4,18,3],[0]),([0,1,48,2,3,4],[6,5,13,0,11,7,17],[0]),([30,7,0,1,2,3,4],[11,12,15,17,8,5,16,6,18,3,64],[0]),([8,13,1,2,3,4],[8,9,4,18,2],[0]),([49,0,1,2,3,4],[9,7,13,11,0,12,1,18,52,53],[0,1]),([13,1,2,9,3,4],[5,9,8,18,28,2],[0,1]),([10,0,1,2,50,3,4],[18,7,4,6,3,8],[0]),([8,1,11,2,3,4],[8,4,7,18,2,28],[0]),([10,0,1,2,5,3,4],[3,2,15,11,0,12,1,7,6],[0,1]),([12,6,0,1,2,4],[11,9,8,0,18,17,7],[0]),([0,1,2,40,3,4],[8,7,64,4,13,11,40,17,12,68],[2,0]),([10,0,1,2,9,3,4],[18,5,7,8,40,28,15,2,4],[]),([51,0,1,2,3,4],[13,9,4,18,0,11,1,12,5,44,45],[0,1]),([10,0,1,11,2,3,4],[4,5,7,6,3,13],[0]),([12,10,0,1,2,3,4],[11,4,40,6,8,5,7,3,18,65,17,16],[0]),([7,0,1,11,2,3,4],[8,13,4,6,7,3,2,11],[]),([0,1,2,5,3,25,4],[58,11,16,2,17,3,69],[0,2]),([12,0,1,2,5,4],[11,2,3,0,9,1,15,58,7,17,18],[0,2,1,3]),([13,0,1,2,5,3,4],[3,2,15,11,0,1,12,13,6,7,28],[0,1]),([51,0,1,2,9,3,4],[18,9,5,4,40,15,44,45],[0,1]),([10,11,2,3,4],[4,7,6,3],[0,1]),([0,1,2,52,3,4],[8,7,13,4,11,17],[]),([0,1,2,31,3,4],[28,5,7,70,11,13,4,60,17],[]),([53,0,1,2,3,4],[11,0,8,4,6,28,17],[]),([26,0,1,2,3,4],[0,4,5,9,11,1,12,8,29,6,17,3],[0,2]),([0,1,2,54,3,4],[5,13,7,11,0,12,1,49,71],[0,1]),([0,1,11,2,5,3,4],[2,3,5,28,13,6,15,11,0,66,12,1,72,7],[0,2,1]),([39,0,1,2,5,3,4],[11,3,2,15,5,0,1,12,16,24],[0,2]),([0,1,27,2,3,4],[8,13,5,18,6,11,17,2,12],[]),([0,1,55,2,3,4],[8,13,5,7,11,0,12,1,2,28],[0]),([56,0,1,2,3,4],[11,8,4,9,1,12,17],[0]),([13,0,34,1,2,3,4],[4,13,18,0,11,17,3,5,8],[0]),([8,38,0,1,2,3,4],[11,8,7,18,28,17,16,15],[0]),([0,34,1,2,9,3,4],[8,5,18,28,63,11,15,4,0,60,16,17],[0]),([0,1,2,50,3,4],[4,7,18,8,6,65,3,11,12],[0,1]),([0,1,2,3,14,4],[5,7,11,12,16,4,13,17,1,0],[0,1]),([12,13,0,1,2,3,4],[11,13,40,18,8,5,6,3,17,16,7,28],[0]),([13,35,0,2,3,4],[8,5,7,2],[0]),([1,11,2,9,3,4],[18,5,9,54,73],[0]),([10,0,11,2,3,4],[13,8,5,7,2],[0]),([13,0,1,2,3,4],[4,5,9,13,18,0,11,1,12,8,2],[0]),([13,0,1,2,9,3,4],[8,5,7,40,28,15,2,4,13],[0]),([0,1,48,11,2,3,4],[5,13,7,0,6,3,17,66],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_60_7 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_6 7 nodes_60_7 = true := by decide +kernel
def bk_60_7 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_7
set_option maxRecDepth 500000 in
lemma bk_60_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 7 xs.toFinset) bk_60_7 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_6_ok chk_60_7
def nodes_60_8 : List NodeSpec := [([0,1,2,5,3,4],[58,11,0,1],[0,2,1,3]),([6,0,1,2,3,4],[0,11,28,9,1,5,7,17],[2,0,3]),([7,0,1,2,3,4],[0,11,9,64,1,17,8,2],[0,2]),([8,0,1,2,3,4],[9,8,7,0,1,28,2],[0,1]),([0,1,2,9,3,4],[5,9,60,61],[0,1,2]),([10,0,1,2,3,4],[8,4,9,65,0,6,1,3,28,2],[0,2,1]),([0,1,11,2,3,4],[13,5,7,66,72,18,9],[0,2,1,3]),([12,0,1,2,3,4],[11,40,0,9,1,17],[0,2,1,3]),([13,0,1,2,3,4],[8,13,9,18,0,28,1,2],[0,1,2])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_60_8 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_7 8 nodes_60_8 = true := by decide +kernel
def bk_60_8 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_8
set_option maxRecDepth 500000 in
lemma bk_60_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 8 xs.toFinset) bk_60_8 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_7_ok chk_60_8
def nodes_60_9 : List NodeSpec := [([0,1,2,3,4],[9,0,1],[0,2,1,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_60_9 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_8 9 nodes_60_9 = true := by decide +kernel
def bk_60_9 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_9
set_option maxRecDepth 500000 in
lemma bk_60_9_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 9 xs.toFinset) bk_60_9 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_8_ok chk_60_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_60_ok : forestRootCheck R_60 G_60 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 4,22,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_60_in : bucketContainsBT bk_60_9 R_60 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_60 : Lower R_60 G_60 10 := lower_of_forestBT root_60_ok bk_60_9_ok root_60_in

end Cofactor12116
def h43R : List Nat := varsOf 31
def h43G : Nat := 0xfee8e8a8fee8e8a8fee8e8a8fee8e8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bound : Lower h43R h43G 10 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(1,2),(0,1)]) (roots2 := Cofactor12116.R_60) (T2 := Cofactor12116.G_60) (by decide +kernel) Cofactor12116.low_60
def h44R : List Nat := varsOf 43
def h44G : Nat := 0xffeeffeeff88ff88ffeeffeeff88ff88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bound : Lower h44R h44G 5 := carry_of (swaps := [(4,5),(0,1),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h41R) (T2 := h41G) (by decide +kernel) h41Bound
def h45R : List Nat := varsOf 47
def h45G : Nat := 0xfee8fee8fe88fe88fee8fee8fe88fe88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bound : Lower h45R h45G 8 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,5,37)]) (by decide +kernel) h39Bound
def h46R : List Nat := varsOf 55
def h46G : Nat := 0xfefee8e8fefea8a8fefee8e8fefea8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 8 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,6,38)]) (by decide +kernel) h40Bound
def h47R : List Nat := varsOf 57
def h47G : Nat := 0xffffffaaffaaaa00ffffffaaffaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h47Bound : Lower h47R h47G 7 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(2,3)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h49R : List Nat := varsOf 27
def h49G : Nat := 0xff88aa00ff88aa00ff88aa00ff88aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bound : Lower h49R h49G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1),(1,2),(2,3),(1,2)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h50R : List Nat := varsOf 26
def h50G : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bound : Lower h50R h50G 4 := carry_of (swaps := [(1,2),(2,3),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h51R : List Nat := varsOf 27
def h51G : Nat := 0xffeeeeaaffeeeeaaffeeeeaaffeeeeaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bound : Lower h51R h51G 5 := carry_of (swaps := [(1,2)]) (roots2 := h41R) (T2 := h41G) (by decide +kernel) h41Bound
def h48R : List Nat := varsOf 59
def h48G : Nat := 0xffeeeeaaff88aa00ffeeeeaaff88aa00
def h48Pos : List Nat := [9,42,11,19,19,24,33,24,24,19,42,33,26,9,42,49,50,25,33,25,50,50,41,11,49,56,33,24,9,56,26,41,9,9,24,35,35,9,11,19,25,33,49]
def h48Neg : List Nat := [8,40,10,17,18,16,32,17,8,3,10,1,18,1,34,17,34,17,40,8,48,18,40,3,48,48,48,40,0,40,10,1,40,17,0,34,3,3,1,1,1,0,1]
def h48Mask : Nat := fullMask 43
def h48Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7fb95ceaa5d,0x5f28082aa88),(0xcccccccccccccccccccccccccccccccc,0xd840b1561e,0x3840a15614),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x167faca75a7,0x1684c0507),(0xffff0000ffff0000ffff0000ffff0000,0x5846b3b93b8,0x2073290b8),(0xffffffff00000000ffffffff00000000,0x618a775cc42,0x92f554042)]
def h48Steps : List (Nat × Nat × Nat) := [(0,0,2),(1,0,2),(2,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(2,1,5),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(3,2,4),(0,3,4),(1,3,4),(2,3,4),(1,3,5),(2,3,5),(0,1,6),(2,1,6),(1,2,11),(3,0,29),(0,3,6),(2,3,6),(1,0,22),(1,2,33),(3,2,33),(2,6,22),(1,0,31),(1,2,31),(0,1,9),(2,1,10),(0,1,18),(1,11,21),(2,1,12),(1,2,12),(0,3,44),(1,3,44),(2,3,44),(3,3,44),(2,2,12),(1,3,12),(2,3,12),(1,12,17),(1,12,41),(3,12,18),(1,12,19),(2,1,45),(0,1,46),(0,1,13),(1,2,58),(2,2,58),(1,3,58),(2,3,58),(2,18,58),(0,3,59),(3,3,59),(3,2,13),(0,13,18),(2,13,19),(1,2,14),(1,14,19),(0,1,23),(1,2,24)]
def h48W : BT Decor := buildWiresBT 7 h48Base h48Steps
def h48AutoList : List (List (Nat × Nat)) := [[],[(4,5),(0,3)]]
def h48Autos : BT (List (Nat × Nat)) := btOfList 1 h48AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Pairs : goodPairs h48G h48Pos h48Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48BaseOk : ∀ x ∈ h48Base, faithful h48Pos h48Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48WOk : btAll (fun x => faithful h48Pos h48Neg x ∧ x.1 < 2^128) h48W := buildWiresBT_faithful h48BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h48G = h48G) h48Autos := btAll_ofList (autos_of (by decide +kernel))
def h48SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,7),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 1 32,4),some (subcubeFast 2 0,4),some (subcubeFast 8 0,5),some (subcubeFast 8 16,4),some (subcubeFast 16 0,5),some (subcubeFast 16 2,4),some (subcubeFast 32 0,5)]
def h48Slices : BT (Option (Nat × Nat)) := btOfList 4 h48SliceList
def h48Specs : List PoolSpec := [(0,[]),(0,[(0,0,2)]),(3,[]),(7,[]),(5,[]),(6,[]),(4,[]),(0,[(0,0,2),(1,3,5)]),(1,[]),(0,[(0,0,2),(2,3,5)]),(9,[]),(2,[]),(11,[]),(0,[(1,0,2)]),(8,[]),(1,[(1,0,2)]),(0,[(2,0,2)]),(0,[(0,0,3)]),(0,[(1,0,2),(0,3,6),(1,2,31)]),(0,[(1,0,3)]),(0,[(2,0,3)]),(9,[(2,1,10)]),(0,[(3,0,3)]),(10,[]),(9,[(0,1,18)]),(7,[(0,1,18)]),(0,[(3,0,3),(1,2,3)]),(2,[(3,0,3)]),(0,[(0,0,4)]),(2,[(2,1,12)]),(0,[(1,0,2),(0,3,6),(1,0,31)]),(0,[(0,2,3)]),(0,[(1,2,3)]),(0,[(0,0,4),(1,2,12)]),(2,[(1,2,12)]),(0,[(2,2,3)]),(0,[(3,2,3)]),(0,[(0,0,4),(2,2,12)]),(0,[(0,0,4),(1,3,12)]),(0,[(0,0,4),(2,3,12)]),(0,[(1,0,4)]),(3,[(0,1,13)]),(11,[(0,1,13)]),(0,[(2,0,4)]),(0,[(2,0,4),(1,2,14)]),(0,[(3,0,4)]),(0,[(0,3,4)]),(0,[(0,3,4),(1,0,22)]),(0,[(1,3,4)]),(9,[(0,1,23)]),(11,[(0,1,23)]),(0,[(2,3,4)])]
def h48Pools : BT (Option BoundPool) := buildPoolsBT 6 h48W h48R h48Slices h48Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice11 : Slice h48R h48G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice10 : Slice h48R h48G (subcubeFast 16 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice9 : Slice h48R h48G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice8 : Slice h48R h48G (subcubeFast 8 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice7 : Slice h48R h48G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice6 : Slice h48R h48G (subcubeFast 2 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice5 : Slice h48R h48G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice4 : Slice h48R h48G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice3 : Slice h48R h48G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice2 : Slice h48R h48G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice1 : Slice h48R h48G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice0 : Slice h48R h48G (subcubeFast 0 2) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h48R h48G p.1 p.2) h48Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h48R h48G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h48Slice0) (forall_cons (fun _ h => by cases h; exact h48Slice1) (forall_cons (fun _ h => by cases h; exact h48Slice2) (forall_cons (fun _ h => by cases h; exact h48Slice3) (forall_cons (fun _ h => by cases h; exact h48Slice4) (forall_cons (fun _ h => by cases h; exact h48Slice5) (forall_cons (fun _ h => by cases h; exact h48Slice6) (forall_cons (fun _ h => by cases h; exact h48Slice7) (forall_cons (fun _ h => by cases h; exact h48Slice8) (forall_cons (fun _ h => by cases h; exact h48Slice9) (forall_cons (fun _ h => by cases h; exact h48Slice10) (forall_cons (fun _ h => by cases h; exact h48Slice11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h48R h48G c) h48Pools := buildPoolsBT_sound h48SlicesOk
def h48Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G (4 - 1) xs.toFinset) h48Empty := trivial
def h48Block4_0 : List NodeSpec := nodesWithIdentity [([2,3,4,37,43],[]),([1,3,4,37,44],[]),([1,3,4,30,44],[]),([0,3,4,41,44],[]),([0,2,3,4,53],[]),([0,3,4,44,56],[]),([0,3,4,44,57],[]),([0,2,3,4,63],[]),([0,2,4,58,64],[]),([0,2,4,58,65],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test4_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Empty 4 h48Block4_0 = true := by decide +kernel
def h48Nodes4 : List NodeSpec := h48Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Check4 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Empty 4 h48Nodes4 = true := h48Test4_0
def h48Bucket4 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 4 xs.toFinset) h48Bucket4 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48EmptyOk h48Check4
def h48Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,3,4,6,29],[0,10]),([1,2,3,4,6,33],[3,12]),([0,1,2,3,4,34],[0,5,8,10]),([0,1,2,3,4,36],[]),([0,2,4,11,41],[8,24,25]),([0,1,2,3,4,42],[]),([0,2,3,4,17,43],[2,5,6,12,29]),([0,2,3,4,18,43],[5,6]),([0,2,3,4,19,43],[]),([0,2,3,4,20,43],[]),([1,2,3,4,12,37],[3,10,15,30]),([0,1,2,3,4,52],[0,2,3,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test5_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Block5_0 = true := by decide +kernel
def h48Block5_1 : List NodeSpec := nodesWithIdentity [([1,2,3,4,12,30],[8]),([0,2,3,4,12,41],[5,8,24,25]),([0,1,3,4,18,44],[2,12,33,34]),([0,1,2,3,4,54],[0,2,5]),([0,1,3,4,19,44],[]),([0,1,2,3,4,55],[2]),([0,1,3,4,20,44],[2]),([0,1,3,4,44,45],[2,12,33,34]),([0,1,3,4,44,46],[2,12,33,34]),([0,1,3,4,44,47],[]),([0,1,3,4,44,48],[]),([0,2,3,4,18,58],[5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test5_1 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Block5_1 = true := by decide +kernel
def h48Block5_2 : List NodeSpec := nodesWithIdentity [([0,2,3,4,19,58],[11,42]),([0,2,3,4,20,58],[]),([0,2,3,4,58,59],[]),([0,2,3,4,58,60],[11,40]),([0,2,3,4,58,61],[5]),([0,2,3,4,58,62],[]),([0,1,2,3,4,59],[8,10,11]),([0,1,2,3,4,67],[0,5]),([0,1,2,3,4,68],[]),([0,1,3,4,20,66],[8]),([0,1,2,3,4,70],[]),([0,1,2,3,4,35],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test5_2 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Block5_2 = true := by decide +kernel
def h48Nodes5 : List NodeSpec := h48Block5_0 ++ h48Block5_1 ++ h48Block5_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Check5 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Nodes5 = true := by
  unfold h48Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h48Test5_0,h48Test5_1⟩,h48Test5_2⟩
def h48Bucket5 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 5 xs.toFinset) h48Bucket5 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket4Ok h48Check5
def h48Block6_0 : List NodeSpec := [([0,2,3,4,16],[1,2,3,4,5,6],[0]),([0,1,2,4,25],[2,3,7,8],[0]),([0,1,2,4,26],[2,3,9,10],[0]),([0,1,2,3,4,6,11],[3,8,10,15],[0]),([0,1,2,3,4,27],[0,2,3,5,8,10,11,12,13],[0]),([0,1,2,3,4,28],[5,6,8,10,11,12,13],[0]),([0,1,2,3,4,6,22],[2,3,8,10,11,12],[0,1]),([0,1,2,3,4,6,31],[2,3,8,10,14],[0]),([0,1,2,3,4,6,32],[8,10,14],[0]),([0,1,2,3,4,6],[0,2,5,8,10,11,12,13],[0]),([0,1,2,3,4,38],[0,2,3,4,5,10,11,12,18],[0]),([0,1,2,3,4,39],[0,2,3,5,8,10,11,12,14,19],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test6_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Block6_0 = true := by decide +kernel
def h48Block6_1 : List NodeSpec := [([0,2,3,4,40],[2,4,5,6,8,20,21],[0]),([0,1,2,4,11,18],[2,3,8,10,23,26,27],[0]),([0,1,2,3,4,11,21],[4,8,10,11,12],[0]),([0,1,2,3,4,29],[0,2,3,5,8,10,11,12,14],[0]),([0,2,3,4,43],[2,5,6,12,28],[0]),([0,1,2,3,4,12,17],[2,3,8,10,11,12,28,31],[0,1]),([0,1,2,3,4,12,18],[2,3,8,10,11,12,28,32],[0]),([0,1,2,3,4,12,19],[2,3,8,10,35],[0]),([0,1,2,3,4,12,20],[2,3,8,10,14,36],[0]),([0,1,3,4,44],[2,12,33],[0]),([0,1,2,3,4,44],[0,2,3,5,8,10,12,33],[0,1]),([0,1,3,4,49],[2,3,12,37],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test6_1 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Block6_1 = true := by decide +kernel
def h48Block6_2 : List NodeSpec := [([0,1,2,4,50],[2,8,12,38],[0]),([0,1,2,4,51],[2,10,12,39],[0]),([0,2,3,4,58],[4,5,11,40,41,42],[0,1]),([0,1,2,3,4,58],[0,2,3,5,8,10,11,12,40],[0]),([0,1,2,3,4,13,18],[8,11,32,40],[0,1]),([0,1,2,3,4,13,19],[3,8,10,11,12,35],[0]),([0,1,2,3,4,13,20],[3,10,11,14,36],[0]),([0,1,2,3,4,66],[0,2,3,4,5,8,10,11,12],[0,1]),([0,1,2,3,4,14,19],[2,3],[0]),([0,1,2,3,4,14,20],[2,8,10,14],[0]),([0,1,2,3,4,69],[0,2,3,5,8,10,11,44],[0]),([0,1,2,3,4,15,20],[4,10,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test6_2 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Block6_2 = true := by decide +kernel
def h48Block6_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,33],[0,2,3,4,5,8,10,12,47]),([0,2,3,4,71],[4,5,8,11,14,48,49,50]),([0,1,2,3,4,71],[0,2,3,4,5,8,10,14,48]),([0,1,2,3,4,72],[0,2,3,4,5,8,10,11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test6_3 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Block6_3 = true := by decide +kernel
def h48Nodes6 : List NodeSpec := h48Block6_0 ++ h48Block6_1 ++ h48Block6_2 ++ h48Block6_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Check6 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Nodes6 = true := by
  unfold h48Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h48Test6_0,h48Test6_1⟩,h48Test6_2⟩,h48Test6_3⟩
def h48Bucket6 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 6 xs.toFinset) h48Bucket6 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket5Ok h48Check6
def h48Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,6,8,10,11,12],[0,1]),([0,1,2,3,4,6],[0,2,3,4,8,10,11,12,13,14],[0,1]),([0,1,2,3,4,7],[0,2,3,4,6,8,10,11,12,14,16],[0]),([0,1,2,3,4,8],[0,2,3,4,6,10,11,12,17],[0]),([0,1,2,3,4,9],[0,2,3,4,8,10,11,12,14,19],[0]),([0,1,2,3,4,10],[0,2,3,4,6,8,10,11,12,14,20],[0]),([0,1,2,3,4,11],[0,2,3,4,8,10,11,12,14,22,23],[0]),([0,1,2,3,4,12],[0,2,3,6,8,10,12,28],[0]),([0,1,2,3,4,13],[0,2,3,4,8,10,11,12,40],[0,1]),([0,1,2,3,4,14],[0,2,3,6,8,10,11,12,43],[0,1]),([0,1,2,3,4,15],[0,2,3,4,8,10,11,12,45],[0,1]),([0,1,2,3,4,22],[0,2,3,4,8,10,12,14,23,46],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test7_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket6 7 h48Block7_0 = true := by decide +kernel
def h48Block7_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,23],[0,2,3,4,8,10,11,12,14,48]),([0,1,2,3,4,24],[0,2,3,4,8,10,11,12,23,51])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test7_1 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket6 7 h48Block7_1 = true := by decide +kernel
def h48Nodes7 : List NodeSpec := h48Block7_0 ++ h48Block7_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Check7 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket6 7 h48Nodes7 = true := by
  unfold h48Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h48Test7_0,h48Test7_1⟩
def h48Bucket7 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 7 xs.toFinset) h48Bucket7 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket6Ok h48Check7
def h48Block8_0 : List NodeSpec := [([0,1,2,3,4],[0],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test8_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket7 8 h48Block8_0 = true := by decide +kernel
def h48Nodes8 : List NodeSpec := h48Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Check8 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket7 8 h48Nodes8 = true := h48Test8_0
def h48Bucket8 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 8 xs.toFinset) h48Bucket8 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket7Ok h48Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bound : Lower h48R h48G 9 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 1,17,19),(VAR 3,1,9),(VAR 4,3,19),(VAR 5,1,33)]) (by decide +kernel) h48Bucket8Ok (by decide +kernel)
def h52R : List Nat := varsOf 61
def h52G : Nat := 0xfffafaaaffaaaa00fffafaaaffaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h52Bound : Lower h52R h52G 8 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h53R : List Nat := varsOf 62
def h53G : Nat := 0xfffcfcfcffccfc00fffcfcfcffccfc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bound : Lower h53R h53G 6 := lift_of (z := 36) (o := 0) (essPairs := [(VAR 2,8,12),(VAR 5,2,34)]) (by decide +kernel) h50Bound
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfee8e8a8fe88a800fee8e8a8fe88a800
def h0Pos : List Nat := [13,26,13,25,28,13,26,37,11,26,19,46,35,11,46,46,13,54,25,37,11,11,23,35,37,23,46,53,54,54,45,15,57,54,11,28,15,60,13,23,53,53,57,19,28,29,30,60,23,13,25,57,39,35,35,43,37,28,11,19,35,51,19,58,27,13,19,13,37,25,11,13,11,28,58,19,19,23,30,30,19,43,37,19,27,29,51,27,29,58,39]
def h0Neg : List Nat := [12,24,14,24,24,9,18,36,3,10,3,14,3,10,42,44,5,52,9,5,9,8,21,33,33,7,38,21,38,50,44,14,49,22,7,12,7,44,1,22,52,49,41,7,20,21,22,52,3,21,1,56,7,34,42,42,38,21,2,18,50,50,2,56,24,8,16,4,52,8,14,7,1,14,50,1,17,18,24,14,21,41,44,22,18,20,49,10,12,42,38]
def h0Mask : Nat := fullMask 91
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x5ff39ff7dff2fd5cbfd35ad,0x43198002172e550bdd1520),(0xcccccccccccccccccccccccccccccccc,0x6dbfd45fcf14896b6f2ff42,0x698a6c07df14896b6007f44),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x524e29a0313f3faff4bc8b5,0x52d82d80312f9bede4b8885),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3b2c7eb868ef47dc435eb7f,0x386c26380c80428c034ea3f),(0xffff0000ffff0000ffff0000ffff0000,0x3f9fe25ea0dffab3a46065a,0x797415ba0af3832842005a),(0xffffffff00000000ffffffff00000000,0x6460410b1f887237d8ad880,0x6460410b1e887217582c080)]
def h0Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,1,2),(1,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,1,4),(1,1,4),(2,1,4),(3,1,4),(0,2,3),(2,2,3),(0,2,4),(2,2,4),(2,2,9),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(0,3,9),(1,3,9),(2,3,9),(1,4,9),(2,4,9),(1,0,31),(0,1,45),(2,2,6),(2,3,6),(0,4,45),(3,4,45),(2,1,31),(1,6,31),(0,4,52),(1,4,52),(3,53,54),(2,4,52),(3,4,52),(1,0,32),(2,1,32),(1,6,32),(1,0,33),(0,1,61),(2,1,33),(2,3,33),(1,0,64),(1,6,64),(1,6,33),(1,0,34),(2,1,34),(2,3,34),(1,0,70),(1,6,34),(2,1,47),(1,0,36),(2,1,36),(2,5,36),(3,36,47),(3,0,37),(0,1,37),(1,0,38),(2,1,38),(1,0,39),(2,1,39),(0,1,74),(2,1,74),(3,1,74),(0,3,74),(1,9,36),(1,6,36),(0,2,89),(2,1,48),(3,6,37),(1,6,38),(1,6,39),(0,1,13),(1,0,95),(0,3,7),(0,5,7),(0,2,96),(0,4,96),(3,4,96),(1,1,15),(1,0,91),(2,2,15),(1,4,15),(2,4,15),(0,1,17),(1,0,107),(2,1,19),(1,0,109),(2,3,19),(1,0,75),(2,3,75),(1,36,98),(2,7,76),(2,7,36),(0,7,37),(1,0,117),(2,7,38),(1,0,119),(2,7,39),(1,0,121),(2,3,8),(3,8,74),(1,8,36),(1,4,79),(3,8,37),(1,8,38),(1,8,39),(2,0,123),(2,3,11),(3,9,37),(3,11,37),(1,9,39),(1,11,39),(1,0,42),(2,1,42),(2,5,42),(1,9,15),(3,9,17),(1,9,19),(1,9,31),(1,9,32),(1,9,33),(1,9,34),(1,0,35),(2,1,35),(2,3,35),(1,0,148),(0,1,148),(0,3,88),(1,9,38),(0,1,41),(0,1,43),(1,0,151),(2,1,44),(2,2,23),(2,3,10),(2,4,23),(2,5,23),(1,10,23),(0,4,161),(2,4,161),(1,10,25),(2,3,27),(1,10,27),(0,3,166),(1,3,166),(2,3,166),(3,3,166),(1,10,38),(1,27,158),(1,0,165),(3,0,165),(1,10,165),(3,167,168),(1,10,29),(1,10,36),(0,1,178),(2,1,178),(1,0,113),(1,10,79),(3,10,37),(1,10,39),(1,11,23),(1,11,25),(1,11,27),(1,11,38),(1,27,131),(0,2,189),(2,2,189),(1,11,29),(1,11,36),(2,5,12),(2,3,22),(1,12,22),(0,3,108),(3,3,108),(1,15,27),(1,12,27),(0,3,28),(3,12,28),(1,12,29),(2,3,30),(1,12,30),(1,12,33),(1,0,69),(1,12,34),(2,13,22),(2,13,27),(0,13,28),(2,13,29),(2,13,30),(1,0,213),(2,13,33),(2,13,34),(1,14,22),(3,14,108),(1,14,27),(3,14,28),(1,14,29),(1,14,30),(3,14,61),(1,14,33),(1,14,34),(1,15,22),(0,1,199),(3,15,28),(1,15,29),(1,15,30),(1,15,33),(1,15,34),(0,3,105),(2,3,106),(1,16,22),(1,16,40),(1,16,23),(0,2,237),(2,2,237),(3,16,237),(0,4,24),(3,4,24),(3,16,24),(1,16,25),(2,5,26),(1,16,26),(3,31,156),(1,0,51),(1,16,31),(0,1,249),(1,0,59),(1,16,32),(2,17,22),(2,17,23),(0,17,24),(2,17,25),(2,17,26),(1,31,107),(1,0,258),(3,0,258),(2,17,31),(2,17,32),(1,18,22),(1,18,23),(3,18,24),(1,18,25),(1,18,26),(3,18,45),(1,18,31),(1,18,32),(1,19,22),(3,0,126),(1,19,23),(3,19,24),(1,19,25),(1,19,26),(1,19,31),(1,19,32),(1,22,36),(3,22,37),(1,22,38),(1,22,39),(1,23,33),(1,23,34),(1,25,33),(1,25,34),(3,27,45),(1,27,31),(0,0,288),(2,259,289),(2,0,288),(1,27,32),(1,29,31),(1,29,32),(1,0,63)]
def h0W : BT Decor := buildWiresBT 9 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[]]
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
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,6),some (subcubeFast 0 2,8),some (subcubeFast 0 4,9),some (subcubeFast 0 6,7),some (subcubeFast 0 8,8),some (subcubeFast 0 16,8),some (subcubeFast 0 20,5),some (subcubeFast 0 32,10),some (subcubeFast 0 34,5),some (subcubeFast 0 40,7),some (subcubeFast 0 48,7),some (subcubeFast 1 0,8),some (subcubeFast 1 2,5),some (subcubeFast 1 4,5),some (subcubeFast 1 6,4),some (subcubeFast 1 8,5),some (subcubeFast 1 16,5),some (subcubeFast 1 32,7),some (subcubeFast 2 0,7),some (subcubeFast 2 1,4),some (subcubeFast 2 4,4),some (subcubeFast 2 8,4),some (subcubeFast 2 16,5),some (subcubeFast 2 32,5),some (subcubeFast 4 0,8),some (subcubeFast 4 1,5),some (subcubeFast 4 2,5),some (subcubeFast 4 8,4),some (subcubeFast 4 16,4),some (subcubeFast 8 0,7),some (subcubeFast 8 1,4),some (subcubeFast 8 2,5),some (subcubeFast 8 4,5),some (subcubeFast 8 6,4),some (subcubeFast 8 16,5),some (subcubeFast 8 20,4),some (subcubeFast 8 32,5),some (subcubeFast 16 0,8),some (subcubeFast 16 2,5),some (subcubeFast 16 6,4),some (subcubeFast 16 8,5),some (subcubeFast 32 0,8),some (subcubeFast 32 1,5),some (subcubeFast 32 16,5),some (subcubeFast 34 0,5),some (subcubeFast 34 8,4),some (subcubeFast 36 0,7),some (subcubeFast 36 8,4)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 6 h0SliceList
def h0Specs : List PoolSpec := [(11,[]),(1,[]),(2,[(0,0,1)]),(7,[(0,0,1)]),(18,[]),(7,[(3,0,1)]),(24,[]),(2,[]),(4,[]),(29,[]),(37,[]),(5,[]),(41,[]),(7,[]),(11,[(0,2,3)]),(1,[(0,2,3)]),(7,[(0,0,1),(0,2,3)]),(2,[(0,0,1),(1,0,31)]),(24,[(0,0,1)]),(2,[(1,0,31)]),(37,[(0,0,1)]),(5,[(0,0,1)]),(7,[(0,2,3),(1,0,31)]),(41,[(0,0,1)]),(26,[]),(13,[]),(18,[(0,2,3)]),(4,[(0,0,1)]),(3,[]),(29,[(0,0,1)]),(5,[(0,2,3)]),(37,[(0,2,3)]),(7,[(0,2,3)]),(41,[(0,2,3)]),(7,[(0,0,1),(0,2,3),(1,6,31)]),(2,[(0,0,1),(1,6,31)]),(1,[(0,2,3),(1,6,31)]),(4,[(0,0,1),(1,6,31)]),(2,[(0,0,1),(1,6,31),(0,4,52)]),(46,[(0,0,1)]),(2,[(0,0,1),(1,6,31),(1,4,52)]),(2,[(0,0,1),(1,6,31),(2,4,52)]),(2,[(0,0,1),(1,6,31),(3,4,52)]),(7,[(0,2,3),(0,0,1),(1,6,31)]),(11,[(2,2,3)]),(1,[(2,2,3)]),(7,[(0,0,1),(2,2,3)]),(15,[]),(18,[(2,2,3)]),(5,[(2,2,3)]),(37,[(2,2,3)]),(7,[(2,2,3)]),(41,[(2,2,3)]),(7,[(0,0,1),(2,2,3),(1,6,32)]),(2,[(0,0,1),(1,6,32)]),(1,[(2,2,3),(1,6,32)]),(11,[(0,2,4)]),(1,[(0,2,4)]),(7,[(0,0,1),(0,2,4)]),(2,[(0,0,1),(1,0,33)]),(7,[(0,0,1),(0,2,4),(1,0,33)]),(2,[(1,0,33)]),(7,[(0,2,4),(1,0,33)]),(18,[(0,2,4)]),(4,[(0,2,4)]),(35,[]),(11,[(0,2,4),(2,3,33)]),(1,[(0,2,4),(2,3,33)]),(0,[]),(3,[(2,3,33)]),(2,[(0,0,1),(2,3,33)]),(2,[(2,3,33)]),(5,[(2,3,33)]),(7,[(0,2,4),(2,3,33)]),(41,[(0,2,4),(2,3,33)]),(40,[]),(2,[(0,0,1),(2,3,33),(1,6,64)]),(31,[]),(7,[(0,2,4)]),(41,[(0,2,4)]),(7,[(0,0,1),(0,2,4),(1,6,33)]),(2,[(0,0,1),(1,6,33)]),(1,[(0,2,4),(1,6,33)]),(6,[]),(11,[(2,2,4)]),(1,[(2,2,4)]),(7,[(0,0,1),(2,2,4)]),(16,[]),(18,[(2,2,4)]),(4,[(2,2,4)]),(34,[]),(11,[(2,2,4),(2,3,34)]),(1,[(2,2,4),(2,3,34)]),(3,[(2,3,34)]),(2,[(0,0,1),(2,3,34)]),(2,[(2,3,34)]),(37,[(2,3,34)]),(7,[(2,2,4),(2,3,34)]),(41,[(2,2,4),(2,3,34)]),(7,[(0,0,1),(2,2,4),(2,3,34)]),(47,[]),(7,[(2,2,4)]),(41,[(2,2,4)]),(7,[(0,0,1),(2,2,4),(1,6,34)]),(2,[(0,0,1),(1,6,34)]),(1,[(2,2,4),(1,6,34)]),(37,[(0,0,1),(1,6,34)]),(7,[(0,0,1),(2,2,6)]),(1,[(2,2,6)]),(7,[(0,3,4),(0,0,1),(2,2,6)]),(11,[(0,3,4)]),(25,[]),(37,[(0,0,1),(2,2,6)]),(2,[(0,3,4),(0,0,1)]),(18,[(0,3,4)]),(1,[(0,3,4),(2,2,6)]),(4,[(0,0,1),(2,2,6)]),(24,[(0,3,4)]),(5,[(0,0,1),(2,2,6)]),(46,[]),(41,[(0,0,1),(2,2,6)]),(7,[(1,3,4),(0,0,1),(2,2,6)]),(11,[(1,3,4)]),(2,[(1,3,4),(0,0,1)]),(1,[(1,3,4),(2,2,6)]),(24,[(1,3,4)]),(7,[(2,3,4),(0,0,1),(2,2,6)]),(11,[(2,3,4)]),(2,[(2,3,4),(0,0,1)]),(18,[(2,3,4)]),(1,[(2,3,4),(2,2,6)]),(24,[(2,3,4)]),(7,[(3,3,4),(0,0,1),(2,2,6)]),(11,[(3,3,4)]),(2,[(3,3,4),(0,0,1)]),(1,[(3,3,4),(2,2,6)]),(24,[(3,3,4)]),(1,[(0,3,4)]),(2,[(0,0,1),(0,3,4)]),(7,[(0,0,1),(0,3,4)]),(2,[(0,0,1),(0,3,4),(1,0,36)]),(2,[(0,3,4),(1,0,36)]),(7,[(0,3,4),(1,0,36)]),(7,[(3,0,1),(0,3,4)]),(37,[(3,0,1)]),(2,[(0,3,4)]),(24,[(3,0,1)]),(2,[(3,0,1)]),(4,[(3,0,1)]),(41,[(0,3,4)]),(7,[(0,3,4)]),(12,[]),(11,[(0,3,4),(2,5,36)]),(1,[(0,3,4),(2,5,36)]),(2,[(0,0,1),(0,3,4),(2,5,36)]),(18,[(0,3,4),(2,5,36)]),(4,[(0,0,1),(2,5,36)]),(42,[]),(2,[(0,3,4),(2,5,36)]),(24,[(0,3,4),(2,5,36)]),(4,[(2,5,36)]),(5,[(0,0,1),(2,5,36)]),(5,[(2,5,36)]),(44,[]),(7,[(0,0,1),(0,3,4),(1,6,36)]),(1,[(0,3,4),(1,6,36)]),(2,[(0,0,1),(0,3,4),(1,6,36)]),(4,[(0,0,1),(1,6,36)]),(2,[(0,3,4),(0,0,1),(3,36,47)]),(5,[(0,0,1),(1,6,36)]),(7,[(0,3,4),(0,0,1),(1,6,36)]),(1,[(1,3,4)]),(2,[(0,0,1),(1,3,4)]),(7,[(0,0,1),(1,3,4)]),(18,[(1,3,4)]),(22,[]),(2,[(1,3,4)]),(7,[(1,3,4),(0,0,1),(2,3,6)]),(2,[(1,3,4),(0,0,1),(2,3,6)]),(1,[(1,3,4),(2,3,6)]),(37,[(0,0,1),(2,3,6)]),(5,[(0,0,1),(2,3,6)]),(7,[(0,0,1),(2,3,6)]),(7,[(1,3,4)]),(41,[(1,3,4)]),(7,[(0,0,1),(1,3,4),(3,6,37)]),(2,[(0,0,1),(1,3,4),(3,6,37)]),(1,[(1,3,4),(3,6,37)]),(37,[(0,0,1),(3,6,37)]),(1,[(2,3,4)]),(2,[(0,0,1),(2,3,4)]),(7,[(0,0,1),(2,3,4)]),(2,[(2,3,4)]),(7,[(2,3,4)]),(41,[(2,3,4)]),(7,[(0,0,1),(2,3,4),(1,6,38)]),(2,[(0,0,1),(2,3,4),(1,6,38)]),(1,[(2,3,4),(1,6,38)]),(4,[(0,0,1),(1,6,38)]),(37,[(0,0,1),(1,6,38)]),(1,[(3,3,4)]),(2,[(0,0,1),(3,3,4)]),(7,[(0,0,1),(3,3,4)]),(18,[(3,3,4)]),(45,[]),(2,[(3,3,4)]),(7,[(3,3,4)]),(41,[(3,3,4)]),(7,[(0,0,1),(3,3,4),(1,6,39)]),(2,[(0,0,1),(3,3,4),(1,6,39)]),(1,[(3,3,4),(1,6,39)]),(2,[(0,0,1),(2,3,6)]),(1,[(2,3,6)]),(2,[(1,0,1)]),(1,[(1,0,3)]),(2,[(1,0,1),(1,0,3)]),(4,[(1,0,1)]),(7,[(1,0,1),(1,0,3)]),(11,[(0,1,13)]),(2,[(1,0,1),(1,0,3),(0,1,13)]),(7,[(1,0,1),(1,0,3),(0,1,13)]),(3,[(1,0,3)]),(24,[(1,0,3),(0,1,13)]),(37,[(1,0,3),(0,1,13)]),(11,[(0,1,13),(0,5,7)]),(7,[(1,0,3),(0,1,13),(1,0,1)]),(4,[(1,0,1),(0,5,7)]),(18,[(0,5,7)]),(41,[(1,0,3),(0,1,13)]),(24,[(1,0,3)]),(2,[(1,0,3)]),(24,[(1,0,1)]),(11,[(0,3,7)]),(7,[(1,0,3),(1,0,1),(0,3,7)]),(2,[(1,0,3),(1,0,1),(0,3,7)]),(24,[(1,0,1),(0,3,7)]),(37,[(1,0,1),(0,3,7)]),(37,[(1,0,3)]),(5,[(1,0,3)]),(37,[(1,0,1)]),(5,[(1,0,1)]),(11,[(0,5,7)]),(7,[(1,0,3),(1,0,1)]),(2,[(1,0,3),(1,0,1),(0,5,7)]),(24,[(1,0,1),(0,5,7)]),(2,[(1,0,1),(0,5,7)]),(41,[(1,0,3)]),(37,[(1,0,1),(0,5,7)]),(5,[(1,0,1),(0,5,7)]),(7,[(1,0,3)]),(41,[(1,0,1)]),(7,[(1,0,1)]),(2,[(1,0,3),(0,1,13),(1,0,95)]),(7,[(1,0,3),(0,1,13),(1,0,95)]),(4,[(1,0,95)]),(1,[(3,0,3)]),(2,[(1,0,1),(3,0,3)]),(7,[(1,0,1),(3,0,3)]),(11,[(2,1,48)]),(29,[(1,0,1)]),(4,[(1,0,1),(0,0,1)]),(3,[(2,3,6)]),(17,[(2,1,48)]),(3,[(3,0,3)]),(24,[(3,0,3)]),(2,[(3,0,3)]),(37,[(3,0,3)]),(5,[(3,0,3)]),(7,[(3,0,3),(1,0,1)]),(2,[(3,0,3),(1,0,1),(0,5,7)]),(29,[(1,0,1),(0,5,7)]),(41,[(3,0,3)]),(9,[(1,0,1)]),(7,[(3,0,3)]),(1,[(1,0,4)]),(2,[(1,0,1),(1,0,4)]),(7,[(1,0,1),(1,0,4)]),(11,[(0,1,17)]),(2,[(1,0,1),(1,0,4),(0,1,17)]),(7,[(1,0,1),(1,0,4),(0,1,17)]),(3,[(1,0,4)]),(37,[(1,0,1),(0,1,17)]),(24,[(1,0,4),(0,1,17)]),(11,[(0,5,7),(0,1,17)]),(37,[(1,0,1),(0,5,7),(0,1,17)]),(41,[(1,0,4),(0,1,17)]),(24,[(1,0,4)]),(2,[(1,0,4)]),(4,[(1,0,4)]),(7,[(1,0,4),(1,0,1)]),(2,[(1,0,4),(1,0,1),(0,5,7)]),(41,[(1,0,4)]),(7,[(1,0,4)]),(1,[(3,0,4)]),(2,[(1,0,1),(3,0,4)]),(7,[(1,0,1),(3,0,4)]),(11,[(2,1,19)]),(2,[(1,0,1),(3,0,4),(2,1,19)]),(7,[(1,0,1),(3,0,4),(2,1,19)]),(5,[(1,0,1),(2,1,19)]),(3,[(3,0,4)]),(24,[(3,0,4)]),(2,[(3,0,4)]),(18,[(3,0,4)]),(18,[(0,3,7)]),(29,[(3,0,4)]),(2,[(1,0,1),(0,3,7)]),(7,[(1,0,1),(0,3,7)]),(41,[(1,0,1),(0,3,7)]),(41,[(3,0,4)]),(7,[(3,0,4)]),(4,[(3,0,4)]),(7,[(3,0,4),(1,0,1)]),(2,[(3,0,4),(1,0,1),(0,5,7)]),(10,[(1,0,1)]),(2,[(1,0,1),(0,3,4)]),(3,[(0,3,4)]),(7,[(1,0,1),(0,3,4)]),(1,[(0,3,4),(1,0,36)]),(2,[(1,0,1),(0,3,4),(1,0,36)]),(7,[(1,0,1),(0,3,4),(1,0,36)]),(4,[(1,0,1),(1,0,36)]),(3,[(0,3,4),(1,0,36)]),(5,[(1,0,1),(1,0,36)]),(11,[(0,3,4),(2,1,36)]),(2,[(1,0,1),(0,3,4),(2,1,36)]),(4,[(1,0,1),(2,1,36)]),(7,[(1,0,1),(0,3,4),(2,1,36)]),(2,[(0,3,4),(2,1,36)]),(5,[(1,0,1),(2,1,36)]),(11,[(0,3,4),(0,5,7)]),(7,[(0,3,4),(1,0,1)]),(2,[(0,3,4),(1,0,1),(0,5,7)]),(11,[(0,3,4),(0,5,7),(1,36,98)]),(7,[(0,3,4),(1,0,1),(1,36,98)]),(1,[(0,3,4),(1,36,98)]),(3,[(0,3,4),(1,36,98)]),(4,[(1,0,1),(0,5,7),(1,36,98)]),(8,[]),(5,[(1,0,1),(0,5,7),(1,36,98)]),(2,[(1,0,1),(0,3,4),(2,5,36)]),(3,[(0,3,4),(2,5,36)]),(4,[(1,0,1),(2,5,36)]),(5,[(1,0,1),(2,5,36)]),(11,[(0,3,4),(2,5,36),(2,7,76)]),(7,[(1,0,1),(0,3,4),(2,7,76)]),(4,[(1,0,1),(2,5,36),(2,7,76)]),(29,[(1,0,1),(2,7,76)]),(37,[(1,0,1),(2,7,76)]),(11,[(0,3,4),(2,7,36)]),(7,[(1,0,1),(0,3,4),(2,7,36)]),(2,[(1,0,1),(0,3,4),(2,7,36)]),(4,[(1,0,1),(2,7,36)]),(5,[(1,0,1),(2,7,36)]),(2,[(1,0,1),(1,3,4)]),(3,[(1,3,4)]),(7,[(1,0,1),(1,3,4)]),(11,[(1,3,4),(0,5,7)]),(7,[(1,3,4),(1,0,1)]),(2,[(1,3,4),(1,0,1),(0,5,7)]),(11,[(1,3,4),(0,7,37)]),(7,[(1,0,1),(1,3,4),(0,7,37)]),(2,[(1,0,1),(1,3,4),(0,7,37)]),(37,[(1,0,1),(0,7,37)]),(2,[(1,0,1),(2,3,4)]),(3,[(2,3,4)]),(7,[(1,0,1),(2,3,4)]),(11,[(2,3,4),(0,5,7)]),(7,[(2,3,4),(1,0,1)]),(2,[(2,3,4),(1,0,1),(0,5,7)]),(11,[(2,3,4),(2,7,38)]),(7,[(1,0,1),(2,3,4),(2,7,38)]),(2,[(1,0,1),(2,3,4),(2,7,38)]),(4,[(1,0,1),(2,7,38)]),(37,[(1,0,1),(2,7,38)]),(2,[(1,0,1),(3,3,4)]),(3,[(3,3,4)]),(7,[(1,0,1),(3,3,4)]),(11,[(3,3,4),(0,3,7)]),(7,[(3,3,4),(1,0,1),(0,3,7)]),(2,[(3,3,4),(1,0,1),(0,3,7)]),(38,[]),(11,[(3,3,4),(0,5,7)]),(7,[(3,3,4),(1,0,1)]),(2,[(3,3,4),(1,0,1),(0,5,7)]),(11,[(3,3,4),(2,7,39)]),(7,[(1,0,1),(3,3,4),(2,7,39)]),(2,[(1,0,1),(3,3,4),(2,7,39)]),(2,[(2,0,1)]),(7,[(2,0,1)]),(2,[(2,0,1),(0,3,4)]),(7,[(2,0,1),(0,3,4)]),(2,[(2,0,1),(0,3,4),(1,0,36)]),(7,[(2,0,1),(0,3,4),(1,0,36)]),(29,[(2,0,1)]),(4,[(2,0,1),(1,0,36)]),(37,[(2,0,1)]),(5,[(2,0,1),(1,0,36)]),(24,[(2,0,1)]),(5,[(2,0,1)]),(4,[(2,0,1)]),(41,[(2,0,1)]),(2,[(2,0,1),(0,3,4),(2,5,36)]),(4,[(2,0,1),(2,5,36)]),(5,[(2,0,1),(2,5,36)]),(36,[]),(7,[(2,0,1),(0,3,4),(1,8,36)]),(2,[(2,0,1),(0,3,4),(1,8,36)]),(4,[(2,0,1),(1,8,36)]),(5,[(2,0,1),(1,8,36)]),(2,[(2,0,1),(1,3,4)]),(7,[(2,0,1),(1,3,4)]),(11,[(1,3,4),(0,1,37)]),(2,[(2,0,1),(1,3,4),(0,1,37)]),(7,[(2,0,1),(1,3,4),(0,1,37)]),(37,[(2,0,1),(0,1,37)]),(2,[(1,3,4),(0,1,37)]),(41,[(1,3,4),(0,1,37)]),(7,[(2,0,1),(1,3,4),(3,8,37)]),(2,[(2,0,1),(1,3,4),(3,8,37)]),(37,[(2,0,1),(3,8,37)]),(2,[(2,0,1),(2,3,4)]),(7,[(2,0,1),(2,3,4)]),(7,[(2,0,1),(2,3,4),(1,8,38)]),(2,[(2,0,1),(2,3,4),(1,8,38)]),(4,[(2,0,1),(1,8,38)]),(37,[(2,0,1),(1,8,38)]),(2,[(2,0,1),(3,3,4)]),(7,[(2,0,1),(3,3,4)]),(7,[(2,0,1),(3,3,4),(1,8,39)]),(2,[(2,0,1),(3,3,4),(1,8,39)]),(7,[(2,0,1),(2,3,8)]),(2,[(2,0,1),(2,3,8)]),(1,[(3,0,2)]),(7,[(3,0,1),(3,0,2)]),(18,[(3,0,2)]),(30,[]),(4,[(3,0,2)]),(14,[]),(37,[(3,0,2)]),(5,[(3,0,2)]),(5,[(3,0,1)]),(41,[(3,0,2)]),(7,[(3,0,2)]),(41,[(3,0,1)]),(2,[(3,0,1),(1,0,3)]),(7,[(3,0,1),(1,0,3)]),(18,[(1,0,3)]),(11,[(2,3,9)]),(7,[(1,0,3),(3,0,1),(2,3,9)]),(2,[(1,0,3),(3,0,1),(2,3,9)]),(1,[(1,0,3),(2,3,9)]),(2,[(3,0,1),(3,0,3)]),(7,[(3,0,1),(3,0,3)]),(18,[(3,0,3)]),(29,[(3,0,1)]),(2,[(3,0,1),(1,0,4)]),(7,[(3,0,1),(1,0,4)]),(18,[(1,0,4)]),(2,[(0,3,4),(1,0,36),(0,3,74)]),(17,[(0,3,4)]),(4,[(1,0,36)]),(37,[(0,3,74)]),(7,[(0,3,4),(1,0,36),(0,3,74)]),(2,[(3,0,1),(3,0,4)]),(7,[(3,0,1),(3,0,4)]),(37,[(3,0,1),(2,3,9)]),(1,[(2,3,9)]),(24,[(3,0,1),(2,3,9)]),(2,[(3,0,1),(2,3,9)]),(7,[(3,0,1),(2,3,9)]),(41,[(3,0,1),(2,3,9)]),(7,[(3,0,4),(3,0,1),(2,3,9)]),(11,[(2,3,19)]),(1,[(3,0,4),(2,3,19)]),(24,[(3,0,4),(2,3,19)]),(2,[(3,0,4),(2,3,19)]),(5,[(2,3,19)]),(41,[(3,0,4),(2,3,19)]),(7,[(3,0,4),(2,3,19)]),(7,[(3,0,1),(0,2,3)]),(11,[(0,2,3),(1,9,31)]),(1,[(0,2,3),(1,9,31)]),(7,[(3,0,1),(0,2,3),(1,9,31)]),(2,[(3,0,1),(1,9,31)]),(4,[(3,0,1),(1,9,31)]),(7,[(3,0,1),(2,2,3)]),(11,[(2,2,3),(1,9,32)]),(1,[(2,2,3),(1,9,32)]),(7,[(3,0,1),(2,2,3),(1,9,32)]),(2,[(3,0,1),(1,9,32)]),(7,[(3,0,1),(0,2,4)]),(2,[(3,0,1),(2,3,33)]),(11,[(0,2,4),(1,9,33)]),(1,[(0,2,4),(1,9,33)]),(7,[(3,0,1),(0,2,4),(1,9,33)]),(2,[(3,0,1),(1,9,33)]),(7,[(3,0,1),(2,2,4)]),(2,[(3,0,1),(2,3,34)]),(7,[(3,0,1),(2,2,4),(2,3,34)]),(11,[(2,2,4),(1,9,34)]),(1,[(2,2,4),(1,9,34)]),(7,[(3,0,1),(2,2,4),(1,9,34)]),(2,[(3,0,1),(1,9,34)]),(37,[(3,0,1),(1,9,34)]),(11,[(2,2,9)]),(1,[(2,2,9)]),(7,[(3,0,1),(2,2,9)]),(2,[(3,0,1),(0,3,4)]),(46,[(3,0,1)]),(37,[(3,0,1),(2,2,9)]),(20,[]),(11,[(2,2,9),(2,3,35)]),(1,[(2,2,9),(2,3,35)]),(2,[(3,0,1),(2,3,35)]),(7,[(3,0,1),(2,2,9),(2,3,35)]),(4,[(3,0,1),(2,2,9)]),(18,[(2,3,35)]),(2,[(3,0,1),(0,3,4),(2,5,36)]),(4,[(3,0,1),(2,5,36)]),(5,[(3,0,1),(2,5,36)]),(11,[(0,3,4),(1,9,36)]),(1,[(0,3,4),(1,9,36)]),(7,[(3,0,1),(0,3,4),(1,9,36)]),(2,[(3,0,1),(0,3,4),(1,9,36)]),(4,[(3,0,1),(1,9,36)]),(5,[(3,0,1),(1,9,36)]),(7,[(0,3,4),(3,0,1),(1,9,36)]),(11,[(0,3,4),(2,1,74)]),(7,[(0,3,4),(1,0,36),(2,1,74)]),(37,[(2,1,74)]),(2,[(0,3,4),(1,0,36),(2,1,74)]),(4,[(1,0,36),(2,1,74)]),(2,[(3,0,1),(1,3,4)]),(7,[(3,0,1),(1,3,4)]),(11,[(1,3,4),(3,9,37)]),(1,[(1,3,4),(3,9,37)]),(7,[(3,0,1),(1,3,4),(3,9,37)]),(2,[(3,0,1),(1,3,4),(3,9,37)]),(37,[(3,0,1),(3,9,37)]),(2,[(3,0,1),(2,3,4)]),(7,[(3,0,1),(2,3,4)]),(11,[(2,3,4),(1,9,38)]),(1,[(2,3,4),(1,9,38)]),(7,[(3,0,1),(2,3,4),(1,9,38)]),(2,[(3,0,1),(2,3,4),(1,9,38)]),(4,[(3,0,1),(1,9,38)]),(37,[(3,0,1),(1,9,38)]),(2,[(3,0,1),(3,3,4)]),(7,[(3,0,1),(3,3,4)]),(11,[(3,3,4),(1,9,39)]),(1,[(3,3,4),(1,9,39)]),(7,[(3,0,1),(3,3,4),(1,9,39)]),(2,[(3,0,1),(3,3,4),(1,9,39)]),(11,[(0,3,9)]),(1,[(0,3,9)]),(7,[(3,0,1),(0,3,9)]),(2,[(3,0,1),(0,3,9)]),(11,[(1,3,9)]),(1,[(1,3,9)]),(2,[(3,0,1),(1,3,9)]),(7,[(3,0,1),(1,3,9)]),(11,[(2,3,9),(2,5,42)]),(1,[(2,3,9),(2,5,42)]),(2,[(3,0,1),(2,3,9),(2,5,42)]),(4,[(3,0,1),(2,5,42)]),(0,[(2,5,42)]),(18,[(2,5,42)]),(11,[(1,4,9)]),(1,[(1,4,9)]),(2,[(3,0,1),(1,4,9)]),(7,[(3,0,1),(1,4,9)]),(10,[(3,0,1)]),(37,[(3,0,1),(0,3,88)]),(9,[(3,0,1),(1,9,36)]),(11,[(2,4,9)]),(1,[(2,4,9)]),(2,[(3,0,1),(2,4,9)]),(7,[(3,0,1),(2,4,9)]),(7,[(0,0,2)]),(11,[(0,1,3)]),(2,[(0,1,3)]),(7,[(0,0,2),(0,1,3)]),(1,[(0,0,2)]),(4,[(0,0,2)]),(18,[(0,0,2)]),(29,[(0,0,2)]),(5,[(0,1,3)]),(37,[(0,1,3)]),(37,[(0,0,2)]),(5,[(0,0,2)]),(7,[(0,1,3)]),(41,[(0,1,3)]),(41,[(0,0,2)]),(7,[(0,0,2),(0,1,3),(1,10,23)]),(2,[(0,1,3),(1,10,23)]),(4,[(0,0,2),(1,10,23)]),(1,[(0,0,2),(1,10,23)]),(24,[(0,1,3)]),(24,[(0,1,148)]),(11,[(2,1,3)]),(2,[(2,1,3)]),(7,[(0,0,2),(2,1,3)]),(5,[(2,1,3)]),(37,[(2,1,3)]),(7,[(2,1,3)]),(41,[(2,1,3)]),(7,[(0,0,2),(2,1,3),(1,10,25)]),(2,[(2,1,3),(1,10,25)]),(1,[(0,0,2),(1,10,25)]),(11,[(0,1,4)]),(2,[(0,1,4)]),(7,[(0,0,2),(0,1,4)]),(2,[(0,1,4),(2,3,4)]),(11,[(0,1,4),(2,3,4)]),(4,[(0,1,4)]),(29,[(0,1,4)]),(7,[(0,1,4),(2,3,4)]),(41,[(0,1,4),(2,3,4)]),(37,[(0,0,2),(2,3,10)]),(1,[(0,0,2),(2,3,10)]),(5,[(0,0,2),(2,3,10)]),(2,[(0,1,4),(2,3,10)]),(2,[(2,3,10)]),(24,[(0,1,4)]),(7,[(0,1,4),(0,0,2),(2,3,10)]),(7,[(0,0,2),(2,3,10)]),(41,[(0,0,2),(2,3,10)]),(41,[(0,1,4)]),(7,[(0,1,4)]),(2,[(0,1,4),(2,3,27)]),(11,[(0,1,4),(2,3,27)]),(1,[(2,3,27)]),(5,[(2,3,27)]),(7,[(0,1,4),(2,3,27)]),(41,[(0,1,4),(2,3,27)]),(32,[]),(7,[(0,0,2),(0,1,4),(1,10,27)]),(2,[(0,1,4),(1,10,27)]),(1,[(0,0,2),(1,10,27)]),(5,[(0,0,2),(1,10,27)]),(46,[(0,1,4)]),(11,[(2,1,4)]),(2,[(2,1,4)]),(7,[(0,0,2),(2,1,4)]),(2,[(2,1,4),(0,3,4)]),(11,[(2,1,4),(0,3,4)]),(4,[(2,1,4)]),(29,[(2,1,4)]),(7,[(2,1,4),(0,3,4)]),(41,[(2,1,4),(0,3,4)]),(7,[(0,0,2),(2,1,4),(0,3,4)]),(2,[(2,1,4),(0,3,4),(1,10,36)]),(4,[(0,0,2),(1,10,36)]),(33,[]),(2,[(0,3,4),(2,1,36),(2,3,75)]),(4,[(2,1,36)]),(37,[(2,3,75)]),(7,[(0,3,4),(2,1,36),(2,3,75)]),(7,[(2,1,4)]),(41,[(2,1,4)]),(7,[(0,0,2),(2,1,4),(1,10,29)]),(2,[(2,1,4),(1,10,29)]),(1,[(0,0,2),(1,10,29)]),(37,[(0,0,2),(1,10,29)]),(7,[(3,0,1),(2,2,9),(2,1,35)]),(2,[(0,3,4),(3,0,1)]),(37,[(3,0,1),(2,2,9),(2,1,35)]),(46,[(0,3,4)]),(17,[]),(7,[(0,0,2),(0,3,4)]),(5,[(2,1,36)]),(7,[(0,3,4),(2,1,36)]),(41,[(0,3,4),(2,1,36)]),(7,[(0,0,2),(0,3,4),(1,10,36)]),(2,[(0,3,4),(1,10,36)]),(3,[(0,3,4),(1,10,36)]),(37,[(0,0,2),(2,1,178)]),(5,[(0,0,2),(1,10,36)]),(7,[(0,3,4),(0,0,2),(1,10,36)]),(7,[(0,0,2),(1,3,4)]),(7,[(0,0,2),(1,3,4),(0,1,37)]),(29,[(0,1,37)]),(37,[(0,1,37)]),(7,[(1,3,4),(0,1,37)]),(2,[(1,3,4),(0,1,37),(1,10,79)]),(4,[(0,0,2),(1,10,79)]),(7,[(0,0,2),(1,3,4),(3,10,37)]),(2,[(1,3,4),(3,10,37)]),(37,[(0,0,2),(3,10,37)]),(3,[(1,3,4),(3,10,37)]),(7,[(0,0,2),(2,3,4)]),(2,[(2,3,4),(2,1,38)]),(11,[(2,3,4),(2,1,38)]),(4,[(2,1,38)]),(37,[(2,1,38)]),(7,[(2,3,4),(2,1,38)]),(41,[(2,3,4),(2,1,38)]),(7,[(0,0,2),(2,3,4),(1,10,38)]),(2,[(2,3,4),(1,10,38)]),(4,[(0,0,2),(1,10,38)]),(37,[(0,0,2),(1,10,38)]),(3,[(2,3,4),(1,10,38)]),(7,[(0,0,2),(3,3,4)]),(2,[(3,3,4),(2,1,39)]),(11,[(3,3,4),(2,1,39)]),(29,[(2,1,39)]),(5,[(2,1,39)]),(7,[(3,3,4),(2,1,39)]),(41,[(3,3,4),(2,1,39)]),(7,[(0,0,2),(3,3,4),(1,10,39)]),(2,[(3,3,4),(1,10,39)]),(3,[(3,3,4),(1,10,39)]),(3,[(2,3,10)]),(7,[(3,0,2),(1,0,3)]),(19,[]),(2,[(1,0,3),(0,1,13)]),(1,[(3,0,2),(1,0,3)]),(7,[(3,0,2),(1,0,3),(0,1,13)]),(29,[(0,1,13)]),(5,[(1,0,3),(0,1,13)]),(7,[(1,0,3),(0,1,13)]),(11,[(2,3,11)]),(2,[(1,0,3),(2,3,11)]),(7,[(1,0,3),(3,0,2),(2,3,11)]),(3,[(1,0,3),(2,3,11)]),(7,[(3,0,2),(3,0,3)]),(29,[(3,0,2)]),(11,[(2,1,47)]),(2,[(3,0,3),(0,0,1)]),(1,[(3,0,3),(2,2,6)]),(17,[(2,1,47)]),(39,[]),(7,[(0,0,1),(2,2,6),(2,1,47)]),(2,[(0,0,1),(2,3,6),(2,1,48)]),(1,[(3,0,2),(2,3,6)]),(7,[(0,0,1),(2,3,6),(2,1,48)]),(7,[(3,0,2),(1,0,4)]),(2,[(1,0,4),(0,1,17)]),(37,[(3,0,2),(0,1,17)]),(1,[(3,0,2),(1,0,4)]),(7,[(3,0,2),(1,0,4),(0,1,17)]),(4,[(1,0,4),(0,1,17)]),(37,[(0,1,17)]),(7,[(1,0,4),(0,1,17)]),(31,[(3,0,2)]),(24,[(0,3,4),(1,0,36),(0,3,74)]),(7,[(3,0,2),(3,0,4)]),(2,[(3,0,4),(0,0,1)]),(1,[(3,0,4),(2,2,6)]),(21,[]),(2,[(3,0,4),(2,1,19)]),(1,[(3,0,2),(3,0,4)]),(24,[(3,0,4),(2,1,19)]),(4,[(3,0,4),(2,1,19)]),(5,[(2,1,19)]),(7,[(3,0,4),(2,1,19)]),(41,[(3,0,4),(2,1,19)]),(37,[(3,0,2),(2,3,11)]),(1,[(3,0,2),(2,3,11)]),(2,[(3,0,4),(2,3,11)]),(2,[(2,3,11)]),(7,[(3,0,2),(2,3,11)]),(41,[(3,0,2),(2,3,11)]),(7,[(3,0,4),(3,0,2),(2,3,11)]),(7,[(3,0,2),(0,1,3)]),(11,[(0,1,3),(1,11,23)]),(1,[(3,0,2),(1,11,23)]),(2,[(0,1,3),(1,11,23)]),(7,[(3,0,2),(0,1,3),(1,11,23)]),(4,[(3,0,2),(1,11,23)]),(7,[(3,0,2),(2,1,3)]),(24,[(2,1,3)]),(11,[(2,1,3),(1,11,25)]),(1,[(3,0,2),(1,11,25)]),(2,[(2,1,3),(1,11,25)]),(7,[(3,0,2),(2,1,3),(1,11,25)]),(7,[(3,0,2),(0,1,4)]),(1,[(3,0,2),(2,3,4)]),(24,[(0,1,4),(2,3,4)]),(5,[(3,0,2),(2,3,11)]),(2,[(0,1,4),(2,3,11)]),(7,[(0,1,4),(3,0,2),(2,3,11)]),(1,[(3,0,2),(2,3,27)]),(24,[(0,1,4),(2,3,27)]),(11,[(0,1,4),(1,11,27)]),(1,[(3,0,2),(1,11,27)]),(2,[(0,1,4),(1,11,27)]),(7,[(3,0,2),(0,1,4),(1,11,27)]),(5,[(3,0,2),(1,11,27)]),(7,[(3,0,2),(2,1,4)]),(24,[(2,1,4)]),(1,[(3,0,2),(0,3,4)]),(24,[(2,1,4),(0,3,4)]),(7,[(3,0,2),(2,1,4),(0,3,4)]),(11,[(2,1,4),(1,11,29)]),(1,[(3,0,2),(1,11,29)]),(2,[(2,1,4),(1,11,29)]),(7,[(3,0,2),(2,1,4),(1,11,29)]),(37,[(3,0,2),(1,11,29)]),(7,[(3,0,2),(0,3,4)]),(24,[(0,3,4),(2,1,36)]),(11,[(0,3,4),(1,11,36)]),(3,[(0,3,4),(1,11,36)]),(2,[(0,3,4),(1,11,36)]),(7,[(3,0,2),(0,3,4),(1,11,36)]),(4,[(3,0,2),(1,11,36)]),(5,[(3,0,2),(1,11,36)]),(7,[(0,3,4),(3,0,2),(1,11,36)]),(7,[(3,0,2),(1,3,4)]),(1,[(3,0,2),(1,3,4)]),(7,[(3,0,2),(1,3,4),(0,1,37)]),(24,[(1,3,4),(0,1,37)]),(11,[(1,3,4),(3,11,37)]),(3,[(1,3,4),(3,11,37)]),(2,[(1,3,4),(3,11,37)]),(7,[(3,0,2),(1,3,4),(3,11,37)]),(37,[(3,0,2),(3,11,37)]),(7,[(3,0,2),(2,3,4)]),(24,[(2,3,4),(2,1,38)]),(11,[(2,3,4),(1,11,38)]),(3,[(2,3,4),(1,11,38)]),(2,[(2,3,4),(1,11,38)]),(7,[(3,0,2),(2,3,4),(1,11,38)]),(4,[(3,0,2),(1,11,38)]),(37,[(3,0,2),(1,11,38)]),(7,[(3,0,2),(3,3,4)]),(1,[(3,0,2),(3,3,4)]),(24,[(3,3,4),(2,1,39)]),(11,[(3,3,4),(1,11,39)]),(3,[(3,3,4),(1,11,39)]),(2,[(3,3,4),(1,11,39)]),(7,[(3,0,2),(3,3,4),(1,11,39)]),(3,[(2,3,11)]),(2,[(0,0,3)]),(7,[(0,0,3)]),(11,[(0,1,2)]),(4,[(0,1,2)]),(7,[(0,0,3),(0,1,2)]),(3,[(0,0,3)]),(24,[(0,0,3)]),(1,[(0,0,3)]),(18,[(0,0,3)]),(29,[(0,1,2)]),(5,[(0,1,2)]),(37,[(0,1,2)]),(5,[(0,0,3)]),(37,[(0,0,3)]),(7,[(0,1,2)]),(41,[(0,1,2)]),(41,[(0,0,3)]),(11,[(3,1,2)]),(4,[(3,1,2)]),(7,[(0,0,3),(3,1,2)]),(29,[(3,1,2)]),(5,[(3,1,2)]),(37,[(3,1,2)]),(7,[(3,1,2)]),(41,[(3,1,2)]),(2,[(0,0,3),(1,12,22)]),(7,[(0,0,3),(3,1,2),(1,12,22)]),(4,[(3,1,2),(1,12,22)]),(2,[(0,0,3),(0,1,4)]),(7,[(0,0,3),(0,1,4)]),(2,[(1,0,4),(0,1,17),(1,0,107)]),(7,[(1,0,4),(0,1,17),(1,0,107)]),(7,[(3,0,3),(0,1,4)]),(2,[(0,1,4),(0,0,3),(2,5,12)]),(7,[(0,1,4),(0,0,3)]),(37,[(0,0,3),(2,5,12)]),(18,[(0,0,3),(2,5,12)]),(1,[(0,0,3),(2,5,12)]),(4,[(0,1,4),(2,5,12)]),(5,[(0,0,3),(2,5,12)]),(24,[(0,0,3),(2,5,12)]),(2,[(0,0,3),(2,5,12)]),(4,[(2,5,12)]),(2,[(0,0,3),(0,1,4),(1,12,27)]),(7,[(0,0,3),(0,1,4),(1,12,27)]),(4,[(0,1,4),(1,12,27)]),(1,[(0,0,3),(1,12,27)]),(5,[(0,0,3),(1,12,27)]),(2,[(0,1,4),(2,3,11),(1,27,131)]),(11,[(1,1,4)]),(2,[(0,0,3),(1,1,4)]),(4,[(1,1,4)]),(7,[(0,0,3),(1,1,4)]),(29,[(1,1,4)]),(4,[(1,1,4),(3,0,1)]),(3,[(2,3,9)]),(5,[(3,0,1),(2,3,9),(2,1,42)]),(17,[(1,1,4)]),(2,[(3,0,1),(2,3,9),(2,1,42)]),(2,[(1,1,4)]),(24,[(1,1,4)]),(7,[(1,1,4)]),(2,[(1,1,4),(0,0,3),(2,5,12)]),(7,[(1,1,4),(0,0,3)]),(4,[(1,1,4),(2,5,12)]),(41,[(1,1,4)]),(2,[(0,0,3),(1,1,4),(3,12,28)]),(7,[(0,0,3),(1,1,4),(3,12,28)]),(4,[(1,1,4),(3,12,28)]),(37,[(0,0,3),(3,12,28)]),(2,[(0,0,3),(2,1,4)]),(7,[(0,0,3),(2,1,4)]),(2,[(2,1,4),(0,0,3),(2,5,12)]),(7,[(2,1,4),(0,0,3)]),(4,[(2,1,4),(2,5,12)]),(2,[(0,0,3),(2,1,4),(1,12,29)]),(7,[(0,0,3),(2,1,4),(1,12,29)]),(1,[(0,0,3),(1,12,29)]),(4,[(2,1,4),(1,12,29)]),(37,[(0,0,3),(1,12,29)]),(11,[(3,1,4)]),(2,[(0,0,3),(3,1,4)]),(4,[(3,1,4)]),(7,[(0,0,3),(3,1,4)]),(29,[(3,1,4)]),(2,[(3,1,4)]),(24,[(3,1,4)]),(7,[(3,1,4)]),(2,[(3,1,4),(0,0,3),(2,5,12)]),(7,[(3,1,4),(0,0,3)]),(4,[(3,1,4),(2,5,12)]),(41,[(3,1,4)]),(2,[(0,0,3),(3,1,4),(1,12,30)]),(7,[(0,0,3),(3,1,4),(1,12,30)]),(4,[(3,1,4),(1,12,30)]),(7,[(3,0,1),(2,3,9),(2,1,42)]),(11,[(1,1,2)]),(17,[(1,1,2)]),(29,[(1,1,2)]),(4,[(1,1,2),(3,0,1)]),(29,[(0,2,4)]),(7,[(0,0,3),(0,2,4)]),(2,[(0,0,3),(1,12,33)]),(7,[(0,0,3),(0,2,4),(1,12,33)]),(4,[(0,2,4),(1,12,33)]),(3,[(0,0,3),(1,12,33)]),(7,[(0,0,3),(2,2,4)]),(29,[(2,2,4)]),(11,[(2,2,4),(2,1,34)]),(4,[(2,2,4),(2,1,34)]),(2,[(0,0,3),(2,1,34)]),(29,[(2,2,4),(2,1,34)]),(7,[(0,0,3),(2,2,4),(2,1,34)]),(2,[(2,1,34)]),(37,[(2,1,34)]),(7,[(2,2,4),(2,1,34)]),(41,[(2,2,4),(2,1,34)]),(2,[(0,0,3),(1,12,34)]),(7,[(0,0,3),(2,2,4),(1,12,34)]),(4,[(2,2,4),(1,12,34)]),(37,[(0,0,3),(1,12,34)]),(3,[(0,0,3),(1,12,34)]),(2,[(1,0,3),(1,0,4)]),(7,[(1,0,3),(1,0,4)]),(37,[(1,0,3),(0,3,74)]),(2,[(1,0,3),(3,0,4)]),(7,[(1,0,3),(3,0,4)]),(7,[(3,0,4),(1,0,3),(0,1,13)]),(2,[(1,0,3),(3,0,4),(2,3,19)]),(7,[(1,0,3),(3,0,4),(2,3,19)]),(7,[(1,0,3),(0,1,2)]),(7,[(1,0,3),(3,1,2)]),(11,[(3,1,2),(0,1,13)]),(7,[(3,1,2),(1,0,3),(0,1,13)]),(11,[(3,1,2),(2,13,22)]),(2,[(1,0,3),(2,13,22)]),(7,[(1,0,3),(3,1,2),(2,13,22)]),(2,[(1,0,3),(0,1,4)]),(7,[(1,0,3),(0,1,4)]),(1,[(1,0,3),(1,0,4)]),(4,[(1,0,4),(0,1,17),(1,0,107)]),(5,[(1,0,3),(1,0,107)]),(3,[(1,0,3),(1,0,4)]),(17,[(0,1,17)]),(9,[(1,0,4),(0,1,17),(1,0,107)]),(1,[(1,0,3),(2,3,27)]),(2,[(1,0,3),(0,1,4),(2,3,27)]),(7,[(1,0,3),(0,1,4),(2,3,27)]),(5,[(1,0,3),(2,3,27)]),(11,[(0,1,4),(2,13,27)]),(1,[(1,0,3),(2,13,27)]),(2,[(1,0,3),(0,1,4),(2,13,27)]),(7,[(1,0,3),(0,1,4),(2,13,27)]),(5,[(1,0,3),(2,13,27)]),(2,[(1,0,3),(1,1,4)]),(7,[(1,0,3),(1,1,4)]),(11,[(1,1,4),(0,13,28)]),(2,[(1,0,3),(1,1,4),(0,13,28)]),(7,[(1,0,3),(1,1,4),(0,13,28)]),(37,[(1,0,3),(0,13,28)]),(2,[(1,0,3),(2,1,4)]),(7,[(1,0,3),(2,1,4)]),(11,[(2,1,4),(2,13,29)]),(1,[(1,0,3),(2,13,29)]),(2,[(1,0,3),(2,1,4),(2,13,29)]),(7,[(1,0,3),(2,1,4),(2,13,29)]),(37,[(1,0,3),(2,13,29)]),(2,[(1,0,3),(3,1,4)]),(7,[(1,0,3),(3,1,4)]),(11,[(3,1,4),(0,1,13)]),(2,[(3,1,4),(1,0,3),(0,1,13)]),(7,[(3,1,4),(1,0,3),(0,1,13)]),(11,[(3,1,4),(2,13,30)]),(2,[(1,0,3),(3,1,4),(2,13,30)]),(7,[(1,0,3),(3,1,4),(2,13,30)]),(7,[(0,2,4),(1,0,3),(0,1,13)]),(7,[(1,0,3),(0,2,4)]),(2,[(1,0,3),(1,0,33)]),(4,[(0,2,4),(1,0,33)]),(7,[(1,0,3),(0,2,4),(1,0,33)]),(3,[(1,0,3),(1,0,33)]),(11,[(0,2,4),(2,13,33)]),(3,[(1,0,3),(2,13,33)]),(2,[(1,0,3),(2,13,33)]),(7,[(1,0,3),(0,2,4),(2,13,33)]),(7,[(1,0,3),(2,2,4)]),(11,[(2,2,4),(2,13,34)]),(3,[(1,0,3),(2,13,34)]),(2,[(1,0,3),(2,13,34)]),(7,[(1,0,3),(2,2,4),(2,13,34)]),(37,[(1,0,3),(2,13,34)]),(2,[(2,0,3)]),(7,[(2,0,3)]),(7,[(2,0,3),(0,1,2)]),(3,[(2,0,3)]),(24,[(2,0,3)]),(1,[(2,0,3)]),(18,[(2,0,3)]),(5,[(2,0,3)]),(37,[(2,0,3)]),(41,[(2,0,3)]),(7,[(2,0,3),(3,1,2)]),(2,[(2,0,3),(1,14,22)]),(7,[(2,0,3),(3,1,2),(1,14,22)]),(2,[(2,0,3),(0,1,4)]),(7,[(2,0,3),(0,1,4)]),(1,[(2,0,3),(1,0,4)]),(5,[(2,0,3),(1,0,107)]),(3,[(2,0,3),(1,0,4)]),(2,[(2,0,3),(0,1,4),(1,14,27)]),(7,[(2,0,3),(0,1,4),(1,14,27)]),(1,[(2,0,3),(1,14,27)]),(5,[(2,0,3),(1,14,27)]),(2,[(2,0,3),(1,1,4)]),(7,[(2,0,3),(1,1,4)]),(11,[(1,1,4),(0,3,28)]),(2,[(2,0,3),(1,1,4),(0,3,28)]),(7,[(2,0,3),(1,1,4),(0,3,28)]),(37,[(2,0,3),(0,3,28)]),(24,[(1,1,4),(0,3,28)]),(7,[(1,1,4),(0,3,28)]),(2,[(2,0,3),(1,1,4),(3,14,28)]),(7,[(2,0,3),(1,1,4),(3,14,28)]),(37,[(2,0,3),(3,14,28)]),(2,[(2,0,3),(2,1,4)]),(7,[(2,0,3),(2,1,4)]),(2,[(2,0,3),(2,1,4),(1,14,29)]),(7,[(2,0,3),(2,1,4),(1,14,29)]),(1,[(2,0,3),(1,14,29)]),(37,[(2,0,3),(1,14,29)]),(2,[(2,0,3),(3,1,4)]),(7,[(2,0,3),(3,1,4)]),(2,[(2,0,3),(3,1,4),(1,14,30)]),(7,[(2,0,3),(3,1,4),(1,14,30)]),(7,[(3,0,1),(1,3,9),(0,1,41)]),(2,[(3,0,1),(1,3,9),(0,1,41)]),(3,[(1,3,9)]),(7,[(2,0,3),(0,2,4)]),(2,[(2,0,3),(1,0,33)]),(7,[(2,0,3),(0,2,4),(1,0,33)]),(3,[(2,0,3),(1,0,33)]),(2,[(2,0,3),(1,0,33),(3,14,61)]),(2,[(2,0,3),(1,14,33)]),(7,[(2,0,3),(0,2,4),(1,14,33)]),(3,[(2,0,3),(1,14,33)]),(7,[(2,0,3),(2,2,4)]),(2,[(2,0,3),(1,14,34)]),(7,[(2,0,3),(2,2,4),(1,14,34)]),(37,[(2,0,3),(1,14,34)]),(3,[(2,0,3),(1,14,34)]),(2,[(3,0,3),(1,0,4)]),(7,[(3,0,3),(1,0,4)]),(29,[(1,0,4)]),(29,[(1,0,4),(0,1,17)]),(7,[(3,0,3),(1,0,4),(0,1,17)]),(2,[(3,0,3),(3,0,4)]),(7,[(3,0,3),(3,0,4)]),(7,[(3,0,3),(3,0,4),(2,1,19)]),(7,[(3,0,3),(0,1,2)]),(7,[(3,0,3),(3,1,2)]),(11,[(3,1,2),(1,15,22)]),(2,[(3,0,3),(1,15,22)]),(4,[(3,1,2),(1,15,22)]),(7,[(3,0,3),(3,1,2),(1,15,22)]),(2,[(3,0,3),(0,1,4)]),(11,[(0,1,4),(1,15,27)]),(1,[(3,0,3),(1,15,27)]),(2,[(3,0,3),(0,1,4),(1,15,27)]),(4,[(0,1,4),(1,15,27)]),(7,[(3,0,3),(0,1,4),(1,15,27)]),(5,[(3,0,3),(1,15,27)]),(4,[(0,1,4),(3,0,165)]),(37,[(3,0,165)]),(1,[(2,3,27),(3,0,165)]),(2,[(0,1,4),(2,3,27),(3,0,165)]),(7,[(0,1,4),(2,3,27),(3,0,165)]),(2,[(3,0,3),(1,1,4)]),(7,[(3,0,3),(1,1,4)]),(11,[(1,1,4),(3,15,28)]),(2,[(3,0,3),(1,1,4),(3,15,28)]),(4,[(1,1,4),(3,15,28)]),(7,[(3,0,3),(1,1,4),(3,15,28)]),(37,[(3,0,3),(3,15,28)]),(2,[(3,0,3),(2,1,4)]),(7,[(3,0,3),(2,1,4)]),(11,[(2,1,4),(1,15,29)]),(1,[(3,0,3),(1,15,29)]),(2,[(3,0,3),(2,1,4),(1,15,29)]),(4,[(2,1,4),(1,15,29)]),(7,[(3,0,3),(2,1,4),(1,15,29)]),(37,[(3,0,3),(1,15,29)]),(2,[(3,0,3),(3,1,4)]),(7,[(3,0,3),(3,1,4)]),(11,[(3,1,4),(1,15,30)]),(2,[(3,0,3),(3,1,4),(1,15,30)]),(4,[(3,1,4),(1,15,30)]),(7,[(3,0,3),(3,1,4),(1,15,30)]),(11,[(1,1,15)]),(2,[(3,0,3),(1,1,15)]),(4,[(1,1,15)]),(7,[(3,0,3),(1,1,15)]),(7,[(3,0,3),(0,2,4)]),(11,[(0,2,4),(1,15,33)]),(3,[(3,0,3),(1,15,33)]),(2,[(3,0,3),(1,15,33)]),(4,[(0,2,4),(1,15,33)]),(7,[(3,0,3),(0,2,4),(1,15,33)]),(7,[(3,0,3),(2,2,4)]),(2,[(3,0,3),(2,1,34)]),(7,[(3,0,3),(2,2,4),(2,1,34)]),(11,[(2,2,4),(1,15,34)]),(3,[(3,0,3),(1,15,34)]),(2,[(3,0,3),(1,15,34)]),(4,[(2,2,4),(1,15,34)]),(7,[(3,0,3),(2,2,4),(1,15,34)]),(37,[(3,0,3),(1,15,34)]),(11,[(2,2,15)]),(4,[(2,2,15)]),(7,[(3,0,3),(2,2,15)]),(11,[(1,4,15)]),(2,[(3,0,3),(1,4,15)]),(4,[(1,4,15)]),(7,[(3,0,3),(1,4,15)]),(3,[(3,0,3),(1,15,27)]),(37,[(3,0,3),(0,1,199)]),(10,[]),(11,[(2,4,15)]),(2,[(3,0,3),(2,4,15)]),(4,[(2,4,15)]),(7,[(3,0,3),(2,4,15)]),(2,[(0,0,4)]),(7,[(0,0,4)]),(7,[(0,0,4),(0,1,2)]),(3,[(0,0,4)]),(24,[(0,0,4)]),(1,[(0,0,4)]),(18,[(0,0,4)]),(4,[(0,0,4)]),(41,[(0,0,4)]),(7,[(0,0,4),(3,1,2)]),(11,[(3,1,2),(2,3,22)]),(37,[(3,1,2),(2,3,22)]),(29,[(0,0,4)]),(18,[(2,3,22)]),(2,[(0,0,4),(2,3,22)]),(7,[(0,0,4),(3,1,2),(2,3,22)]),(2,[(2,3,22)]),(7,[(3,1,2),(2,3,22)]),(41,[(3,1,2),(2,3,22)]),(2,[(0,0,4),(1,16,22)]),(7,[(0,0,4),(3,1,2),(1,16,22)]),(2,[(0,0,4),(0,1,3)]),(7,[(0,0,4),(0,1,3)]),(2,[(0,0,4),(0,1,3),(1,16,23)]),(7,[(0,0,4),(0,1,3),(1,16,23)]),(1,[(0,0,4),(1,16,23)]),(4,[(0,0,4),(1,16,23)]),(11,[(1,1,3)]),(2,[(0,0,4),(1,1,3)]),(37,[(1,1,3)]),(7,[(0,0,4),(1,1,3)]),(3,[(2,4,9)]),(4,[(3,0,1),(2,4,9),(2,1,44)]),(17,[(1,1,3)]),(2,[(1,1,3)]),(24,[(1,1,3)]),(3,[(3,0,3),(2,4,15),(2,3,106)]),(1,[(3,0,3),(2,4,15),(2,3,106)]),(7,[(1,1,3)]),(41,[(1,1,3)]),(2,[(0,0,4),(1,1,3),(3,16,24)]),(7,[(0,0,4),(1,1,3),(3,16,24)]),(2,[(0,0,4),(2,1,3)]),(7,[(0,0,4),(2,1,3)]),(2,[(0,0,4),(2,1,3),(1,16,25)]),(7,[(0,0,4),(2,1,3),(1,16,25)]),(1,[(0,0,4),(1,16,25)]),(11,[(3,1,3)]),(2,[(0,0,4),(3,1,3)]),(37,[(3,1,3)]),(7,[(0,0,4),(3,1,3)]),(2,[(3,1,3)]),(24,[(3,1,3)]),(7,[(3,1,3)]),(41,[(3,1,3)]),(11,[(3,1,3),(2,5,26)]),(2,[(0,0,4),(3,1,3),(2,5,26)]),(37,[(3,1,3),(2,5,26)]),(18,[(2,5,26)]),(4,[(0,0,4),(2,5,26)]),(2,[(3,1,3),(2,5,26)]),(24,[(3,1,3),(2,5,26)]),(4,[(2,5,26)]),(2,[(0,0,4),(3,1,3),(1,16,26)]),(7,[(0,0,4),(3,1,3),(1,16,26)]),(4,[(0,0,4),(1,16,26)]),(7,[(3,0,1),(2,4,9),(2,1,44)]),(2,[(3,0,1),(2,4,9),(2,1,44)]),(17,[(0,2,3)]),(7,[(0,0,4),(0,2,3)]),(2,[(0,0,4),(1,0,31)]),(11,[(0,2,3),(2,1,31)]),(37,[(0,2,3),(2,1,31)]),(2,[(0,0,4),(2,1,31)]),(7,[(0,0,4),(0,2,3),(2,1,31)]),(2,[(2,1,31)]),(4,[(2,1,31)]),(7,[(0,2,3),(2,1,31)]),(41,[(0,2,3),(2,1,31)]),(2,[(0,0,4),(1,16,31)]),(7,[(0,0,4),(0,2,3),(1,16,31)]),(4,[(0,0,4),(1,16,31)]),(3,[(0,0,4),(1,16,31)]),(3,[(2,4,9),(3,31,156)]),(7,[(0,2,3),(0,0,4),(1,16,31)]),(7,[(0,0,4),(2,2,3)]),(11,[(2,2,3),(2,1,32)]),(37,[(2,2,3),(2,1,32)]),(2,[(0,0,4),(2,1,32)]),(2,[(2,1,32)]),(29,[(2,1,32)]),(7,[(2,2,3),(2,1,32)]),(41,[(2,2,3),(2,1,32)]),(2,[(0,0,4),(1,16,32)]),(7,[(0,0,4),(2,2,3),(1,16,32)]),(3,[(0,0,4),(1,16,32)]),(7,[(3,0,3),(2,4,15),(2,3,106)]),(7,[(1,0,4),(0,1,2)]),(7,[(1,0,4),(3,1,2)]),(11,[(3,1,2),(0,1,17)]),(7,[(3,1,2),(1,0,4),(0,1,17)]),(37,[(3,1,2),(0,1,17)]),(11,[(3,1,2),(2,17,22)]),(2,[(1,0,4),(2,17,22)]),(7,[(1,0,4),(3,1,2),(2,17,22)]),(37,[(3,1,2),(2,17,22)]),(2,[(1,0,4),(0,1,3)]),(7,[(1,0,4),(0,1,3)]),(1,[(1,0,4),(1,0,3)]),(4,[(1,0,4),(1,0,95)]),(5,[(1,0,3),(0,1,13),(1,0,95)]),(3,[(1,0,4),(1,0,3)]),(17,[(0,1,13)]),(10,[(1,0,3),(0,1,13),(1,0,95)]),(11,[(0,1,3),(2,17,23)]),(1,[(1,0,4),(2,17,23)]),(2,[(1,0,4),(0,1,3),(2,17,23)]),(4,[(1,0,4),(2,17,23)]),(7,[(1,0,4),(0,1,3),(2,17,23)]),(37,[(0,1,3),(2,17,23)]),(2,[(1,0,4),(1,1,3)]),(7,[(1,0,4),(1,1,3)]),(5,[(1,1,3)]),(11,[(1,1,3),(0,17,24)]),(2,[(1,0,4),(1,1,3),(0,17,24)]),(7,[(1,0,4),(1,1,3),(0,17,24)]),(37,[(1,1,3),(0,17,24)]),(2,[(1,0,4),(2,1,3)]),(7,[(1,0,4),(2,1,3)]),(11,[(2,1,3),(0,3,4)]),(37,[(2,1,3),(0,3,74)]),(17,[(2,1,3),(0,3,4)]),(9,[(1,0,36)]),(11,[(2,1,3),(2,17,25)]),(1,[(1,0,4),(2,17,25)]),(2,[(1,0,4),(2,1,3),(2,17,25)]),(7,[(1,0,4),(2,1,3),(2,17,25)]),(37,[(2,1,3),(2,17,25)]),(2,[(1,0,4),(3,1,3)]),(7,[(1,0,4),(3,1,3)]),(11,[(3,1,3),(0,1,17)]),(2,[(3,1,3),(1,0,4),(0,1,17)]),(7,[(3,1,3),(1,0,4),(0,1,17)]),(37,[(3,1,3),(0,1,17)]),(5,[(3,1,3)]),(11,[(0,1,17),(3,1,3),(2,5,26)]),(4,[(1,0,4),(0,1,17),(2,5,26)]),(7,[(1,0,4),(0,1,17),(3,1,3)]),(37,[(0,1,17),(3,1,3),(2,5,26)]),(5,[(3,1,3),(2,5,26)]),(2,[(1,0,4),(3,1,3),(2,5,26)]),(4,[(1,0,4),(2,5,26)]),(11,[(3,1,3),(2,17,26)]),(2,[(1,0,4),(3,1,3),(2,17,26)]),(4,[(1,0,4),(2,17,26)]),(7,[(1,0,4),(3,1,3),(2,17,26)]),(37,[(3,1,3),(2,17,26)]),(7,[(0,2,3),(1,0,4),(0,1,17)]),(3,[(1,0,4),(1,31,107)]),(2,[(1,0,4),(0,1,17),(1,31,107)]),(5,[(0,2,3),(1,31,107)]),(7,[(1,0,4),(0,2,3)]),(2,[(1,0,4),(1,0,31)]),(4,[(1,0,4),(1,0,31)]),(37,[(0,2,3),(1,0,31)]),(5,[(0,2,3),(1,0,31)]),(7,[(1,0,4),(0,2,3),(1,0,31)]),(3,[(1,0,4),(1,0,31)]),(11,[(0,2,3),(2,17,31)]),(3,[(1,0,4),(2,17,31)]),(2,[(1,0,4),(2,17,31)]),(4,[(1,0,4),(2,17,31)]),(7,[(1,0,4),(0,2,3),(2,17,31)]),(37,[(0,2,3),(2,17,31)]),(7,[(1,0,4),(2,2,3)]),(11,[(2,2,3),(0,3,4)]),(37,[(2,2,3),(0,3,74)]),(17,[(2,2,3),(0,3,4)]),(46,[(0,3,4),(1,0,36),(0,3,74)]),(11,[(2,2,3),(2,17,32)]),(3,[(1,0,4),(2,17,32)]),(2,[(1,0,4),(2,17,32)]),(7,[(1,0,4),(2,2,3),(2,17,32)]),(37,[(2,2,3),(2,17,32)]),(2,[(2,0,4)]),(7,[(2,0,4)]),(7,[(2,0,4),(0,1,2)]),(3,[(2,0,4)]),(24,[(2,0,4)]),(1,[(2,0,4)]),(18,[(2,0,4)]),(4,[(2,0,4)]),(41,[(2,0,4)]),(7,[(2,0,4),(3,1,2)]),(2,[(2,0,4),(1,18,22)]),(7,[(2,0,4),(3,1,2),(1,18,22)]),(37,[(3,1,2),(1,18,22)]),(2,[(2,0,4),(0,1,3)]),(7,[(2,0,4),(0,1,3)]),(1,[(2,0,4),(1,0,3)]),(4,[(2,0,4),(1,0,95)]),(29,[(2,0,4)]),(3,[(2,0,4),(1,0,3)]),(5,[(3,0,1),(0,3,9),(1,16,40)]),(2,[(2,0,4),(0,1,3),(1,18,23)]),(7,[(2,0,4),(0,1,3),(1,18,23)]),(1,[(2,0,4),(1,18,23)]),(4,[(2,0,4),(1,18,23)]),(37,[(0,1,3),(1,18,23)]),(2,[(2,0,4),(1,1,3)]),(7,[(2,0,4),(1,1,3)]),(2,[(2,0,4),(1,1,3),(3,18,24)]),(7,[(2,0,4),(1,1,3),(3,18,24)]),(37,[(1,1,3),(3,18,24)]),(2,[(2,0,4),(2,1,3)]),(7,[(2,0,4),(2,1,3)]),(2,[(2,0,4),(2,1,3),(1,18,25)]),(7,[(2,0,4),(2,1,3),(1,18,25)]),(1,[(2,0,4),(1,18,25)]),(37,[(2,1,3),(1,18,25)]),(2,[(2,0,4),(3,1,3)]),(7,[(2,0,4),(3,1,3)]),(2,[(2,0,4),(3,1,3),(2,5,26)]),(4,[(2,0,4),(2,5,26)]),(2,[(2,0,4),(3,1,3),(1,18,26)]),(7,[(2,0,4),(3,1,3),(1,18,26)]),(4,[(2,0,4),(1,18,26)]),(37,[(3,1,3),(1,18,26)]),(7,[(3,0,1),(1,4,9),(0,1,43)]),(2,[(3,0,1),(1,4,9),(0,1,43)]),(37,[(1,1,2),(3,0,1)]),(5,[(1,1,2)]),(3,[(1,4,9)]),(7,[(2,0,4),(0,2,3)]),(2,[(2,0,4),(1,0,31)]),(4,[(2,0,4),(1,0,31)]),(7,[(2,0,4),(0,2,3),(1,0,31)]),(3,[(2,0,4),(1,0,31)]),(24,[(2,0,4),(3,18,45)]),(2,[(2,0,4),(1,0,31),(3,18,45)]),(2,[(2,0,4),(1,18,31)]),(7,[(2,0,4),(0,2,3),(1,18,31)]),(4,[(2,0,4),(1,18,31)]),(37,[(0,2,3),(1,18,31)]),(3,[(2,0,4),(1,18,31)]),(7,[(2,0,4),(2,2,3)]),(2,[(2,0,4),(1,18,32)]),(7,[(2,0,4),(2,2,3),(1,18,32)]),(37,[(2,2,3),(1,18,32)]),(3,[(2,0,4),(1,18,32)]),(7,[(3,0,3),(1,4,15),(0,3,105)]),(7,[(3,0,4),(0,1,2)]),(7,[(3,0,4),(3,1,2)]),(5,[(3,1,2),(2,3,22)]),(2,[(3,0,4),(2,3,22)]),(7,[(3,0,4),(3,1,2),(2,3,22)]),(11,[(3,1,2),(1,19,22)]),(2,[(3,0,4),(1,19,22)]),(7,[(3,0,4),(3,1,2),(1,19,22)]),(5,[(3,1,2),(1,19,22)]),(2,[(3,0,4),(0,1,3)]),(7,[(3,0,4),(0,1,3)]),(1,[(3,0,4),(1,3,4)]),(4,[(3,0,4),(1,4,79)]),(3,[(3,0,4),(1,3,4)]),(9,[(3,0,4),(1,4,79)]),(43,[]),(11,[(0,1,3),(1,19,23)]),(1,[(3,0,4),(1,19,23)]),(2,[(3,0,4),(0,1,3),(1,19,23)]),(4,[(3,0,4),(1,19,23)]),(7,[(3,0,4),(0,1,3),(1,19,23)]),(5,[(0,1,3),(1,19,23)]),(2,[(3,0,4),(1,1,3)]),(7,[(3,0,4),(1,1,3)]),(11,[(1,1,3),(3,19,24)]),(2,[(3,0,4),(1,1,3),(3,19,24)]),(7,[(3,0,4),(1,1,3),(3,19,24)]),(5,[(1,1,3),(3,19,24)]),(2,[(3,0,4),(2,1,3)]),(7,[(3,0,4),(2,1,3)]),(11,[(2,1,3),(1,19,25)]),(1,[(3,0,4),(1,19,25)]),(2,[(3,0,4),(2,1,3),(1,19,25)]),(7,[(3,0,4),(2,1,3),(1,19,25)]),(5,[(2,1,3),(1,19,25)]),(2,[(3,0,4),(3,1,3)]),(7,[(3,0,4),(3,1,3)]),(2,[(3,0,4),(3,1,3),(2,5,26)]),(4,[(3,0,4),(2,5,26)]),(11,[(3,1,3),(1,19,26)]),(2,[(3,0,4),(3,1,3),(1,19,26)]),(4,[(3,0,4),(1,19,26)]),(7,[(3,0,4),(3,1,3),(1,19,26)]),(5,[(3,1,3),(1,19,26)]),(7,[(0,2,3),(3,0,4),(2,1,19)]),(7,[(3,0,4),(0,2,3)]),(5,[(0,2,3),(2,1,31)]),(2,[(3,0,4),(2,1,31)]),(7,[(3,0,4),(0,2,3),(2,1,31)]),(11,[(0,2,3),(1,19,31)]),(3,[(3,0,4),(1,19,31)]),(2,[(3,0,4),(1,19,31)]),(4,[(3,0,4),(1,19,31)]),(7,[(3,0,4),(0,2,3),(1,19,31)]),(5,[(0,2,3),(1,19,31)]),(7,[(3,0,4),(2,2,3)]),(5,[(2,2,3),(2,1,32)]),(2,[(3,0,4),(2,1,32)]),(11,[(2,2,3),(1,19,32)]),(3,[(3,0,4),(1,19,32)]),(2,[(3,0,4),(1,19,32)]),(7,[(3,0,4),(2,2,3),(1,19,32)]),(5,[(2,2,3),(1,19,32)]),(7,[(0,1,2),(0,3,4)]),(7,[(0,1,2),(1,3,4)]),(7,[(0,1,2),(2,3,4)]),(7,[(0,1,2),(3,3,4)]),(7,[(3,0,1),(2,2,9),(1,0,35)]),(17,[(2,2,9)]),(18,[(1,0,35)]),(2,[(1,3,4),(3,0,1)]),(2,[(2,3,4),(3,0,1)]),(2,[(3,3,4),(3,0,1)]),(7,[(3,1,2),(0,3,4)]),(2,[(0,3,4),(1,22,36)]),(4,[(3,1,2),(1,22,36)]),(7,[(3,1,2),(0,3,4),(1,22,36)]),(5,[(3,1,2),(1,22,36)]),(7,[(3,1,2),(1,3,4)]),(2,[(1,3,4),(3,22,37)]),(37,[(3,1,2),(3,22,37)]),(7,[(3,1,2),(1,3,4),(3,22,37)]),(27,[]),(7,[(3,1,2),(2,3,4)]),(2,[(2,3,4),(1,22,38)]),(4,[(3,1,2),(1,22,38)]),(37,[(3,1,2),(1,22,38)]),(7,[(3,1,2),(2,3,4),(1,22,38)]),(7,[(3,1,2),(3,3,4)]),(2,[(3,3,4),(1,22,39)]),(7,[(3,1,2),(3,3,4),(1,22,39)]),(3,[(2,3,35),(1,0,148)]),(2,[(3,0,1),(2,3,35),(1,0,148)]),(24,[(1,0,148)]),(17,[(2,2,9),(2,3,35)]),(46,[(1,0,148)]),(18,[(0,4,96)]),(29,[(0,4,96)]),(1,[(1,0,3),(0,4,96)]),(4,[(1,0,95),(0,4,96)]),(11,[(0,1,13),(0,4,96)]),(3,[(1,0,3),(0,4,96)]),(17,[(0,1,13),(0,4,96)]),(18,[(3,4,96)]),(29,[(3,4,96)]),(1,[(1,0,3),(3,4,96)]),(4,[(1,0,95),(3,4,96)]),(11,[(0,1,13),(3,4,96)]),(3,[(1,0,3),(3,4,96)]),(17,[(0,1,13),(3,4,96)]),(17,[(0,1,3)]),(18,[(0,2,96)]),(11,[(0,1,13),(0,2,96)]),(1,[(1,0,3),(1,3,4)]),(4,[(1,0,95),(1,4,79)]),(4,[(1,4,79)]),(28,[]),(2,[(1,3,4),(0,1,37),(1,4,79)]),(7,[(1,3,4),(0,1,37),(1,4,79)]),(4,[(2,4,23)]),(1,[(2,4,23)]),(11,[(0,1,3),(2,4,23)]),(24,[(0,1,3),(2,4,23)]),(2,[(0,1,3),(2,4,23)]),(41,[(0,1,3),(2,4,23)]),(7,[(0,1,3),(2,4,23)]),(7,[(2,0,1),(2,3,8),(2,0,123)]),(2,[(2,0,1),(2,3,8),(2,0,123)]),(1,[(2,0,123)]),(3,[(2,0,123)]),(11,[(0,1,3),(2,2,23)]),(1,[(2,2,23)]),(4,[(2,2,23)]),(17,[(0,1,3),(2,2,23)]),(5,[(0,1,3),(2,2,23)]),(37,[(0,1,3),(2,2,23)]),(7,[(0,1,3),(2,2,23)]),(41,[(0,1,3),(2,2,23)]),(11,[(0,1,3),(2,5,23)]),(23,[]),(1,[(2,5,23)]),(4,[(2,5,23)]),(2,[(0,1,3),(2,5,23)]),(24,[(0,1,3),(2,5,23)]),(5,[(0,1,3),(2,5,23)]),(37,[(0,1,3),(2,5,23)]),(9,[]),(9,[(2,0,1)]),(7,[(0,1,3),(0,2,4)]),(1,[(0,2,4),(1,23,33)]),(2,[(0,1,3),(1,23,33)]),(4,[(0,2,4),(1,23,33)]),(7,[(0,1,3),(0,2,4),(1,23,33)]),(7,[(0,1,3),(2,2,4)]),(2,[(0,1,3),(1,0,34)]),(1,[(2,2,4),(1,0,34)]),(4,[(2,2,4),(1,0,34)]),(2,[(1,0,34)]),(37,[(1,0,34)]),(41,[(2,2,4),(1,0,34)]),(7,[(2,2,4),(1,0,34)]),(1,[(2,2,4),(1,23,34)]),(2,[(0,1,3),(1,23,34)]),(4,[(2,2,4),(1,23,34)]),(37,[(0,1,3),(1,23,34)]),(7,[(0,1,3),(2,2,4),(1,23,34)]),(10,[(0,1,3)]),(9,[(1,4,79)]),(18,[(3,0,126)]),(1,[(1,3,4),(3,0,126)]),(4,[(1,4,79),(3,0,126)]),(3,[(1,3,4),(3,0,126)]),(37,[(0,1,37),(3,0,126)]),(9,[(1,4,79),(3,0,126)]),(11,[(1,9,15)]),(7,[(3,0,1),(3,0,3),(1,9,15)]),(17,[(1,9,15)]),(2,[(1,1,3),(0,4,24)]),(7,[(1,1,3),(0,4,24)]),(2,[(1,1,3),(3,4,24)]),(7,[(1,1,3),(3,4,24)]),(7,[(2,1,3),(0,2,4)]),(2,[(2,1,3),(1,0,33)]),(1,[(0,2,4),(1,0,33)]),(3,[(1,0,33)]),(5,[(1,0,33)]),(41,[(0,2,4),(1,0,33)]),(1,[(0,2,4),(1,25,33)]),(2,[(2,1,3),(1,25,33)]),(7,[(2,1,3),(0,2,4),(1,25,33)]),(7,[(2,1,3),(2,2,4)]),(2,[(2,1,3),(1,0,34)]),(3,[(1,0,34)]),(1,[(2,2,4),(1,25,34)]),(2,[(2,1,3),(1,25,34)]),(37,[(2,1,3),(1,25,34)]),(7,[(2,1,3),(2,2,4),(1,25,34)]),(7,[(3,0,1),(2,3,9),(1,0,42)]),(17,[(2,3,9)]),(5,[(1,0,107)]),(18,[(0,3,108)]),(37,[(0,3,108)]),(1,[(1,0,4),(0,3,108)]),(5,[(1,0,107),(0,3,108)]),(11,[(0,1,17),(0,3,108)]),(3,[(1,0,4),(0,3,108)]),(17,[(0,1,17),(0,3,108)]),(18,[(3,3,108)]),(37,[(3,3,108)]),(1,[(1,0,4),(3,3,108)]),(5,[(1,0,107),(3,3,108)]),(11,[(0,1,17),(3,3,108)]),(3,[(1,0,4),(3,3,108)]),(17,[(0,1,17),(3,3,108)]),(7,[(0,1,4),(0,2,3)]),(2,[(0,1,4),(1,0,31)]),(1,[(0,2,3),(1,0,31)]),(3,[(1,0,31)]),(4,[(1,0,31)]),(41,[(0,2,3),(1,0,31)]),(1,[(0,2,3),(1,27,31)]),(2,[(0,1,4),(1,27,31)]),(4,[(0,1,4),(1,27,31)]),(7,[(0,1,4),(0,2,3),(1,27,31)]),(5,[(0,2,3),(1,27,31)]),(7,[(0,2,3),(0,1,4),(1,27,31)]),(7,[(0,1,4),(2,2,3)]),(2,[(0,1,4),(1,0,32)]),(37,[(2,2,3),(1,0,32)]),(1,[(2,2,3),(1,0,32)]),(5,[(2,2,3),(1,0,32)]),(2,[(1,0,32)]),(29,[(1,0,32)]),(7,[(2,2,3),(1,0,32)]),(41,[(2,2,3),(1,0,32)]),(1,[(2,2,3),(1,27,32)]),(2,[(0,1,4),(1,27,32)]),(7,[(0,1,4),(2,2,3),(1,27,32)]),(5,[(2,2,3),(1,27,32)]),(1,[(2,3,27),(1,0,165)]),(18,[(1,0,165)]),(2,[(0,1,4),(2,3,27),(1,0,165)]),(4,[(0,1,4),(1,0,165)]),(37,[(1,0,165)]),(7,[(0,1,4),(2,3,27),(1,0,165)]),(11,[(1,9,19)]),(7,[(3,0,1),(3,0,4),(1,9,19)]),(17,[(1,9,19)]),(2,[(1,1,4),(0,3,28)]),(37,[(0,3,28)]),(5,[(1,0,151)]),(10,[(1,0,151)]),(37,[(1,0,109)]),(7,[(3,0,4),(2,1,19),(1,0,109)]),(17,[(2,1,19)]),(7,[(2,1,4),(0,2,3)]),(2,[(2,1,4),(1,0,31)]),(1,[(0,2,3),(1,29,31)]),(2,[(2,1,4),(1,29,31)]),(4,[(2,1,4),(1,29,31)]),(37,[(0,2,3),(1,29,31)]),(7,[(2,1,4),(0,2,3),(1,29,31)]),(7,[(2,1,4),(2,2,3)]),(1,[(2,2,3),(1,29,32)]),(2,[(2,1,4),(1,29,32)]),(37,[(2,2,3),(1,29,32)]),(7,[(2,1,4),(2,2,3),(1,29,32)]),(46,[(2,1,4)]),(18,[(1,0,113)]),(1,[(0,3,4),(1,0,113)]),(3,[(0,3,4),(1,0,113)]),(4,[(2,1,36),(1,0,113)]),(37,[(2,3,75),(1,0,113)]),(5,[(1,0,113)]),(10,[(1,0,113)]),(9,[(2,1,36),(1,0,113)]),(11,[(3,9,17)]),(7,[(3,0,1),(1,0,4),(3,9,17)]),(17,[(3,9,17)]),(2,[(3,1,4),(2,3,30)]),(7,[(3,1,4),(2,3,30)]),(17,[(3,1,4),(2,13,30)]),(4,[(3,1,4),(1,0,213)]),(2,[(1,0,31),(0,1,45)]),(29,[(0,1,45)]),(24,[(0,1,45)]),(11,[(0,2,3),(0,1,45)]),(37,[(0,2,3),(1,0,31),(0,1,45)]),(2,[(1,0,31),(0,4,45)]),(7,[(0,2,3),(1,0,31),(0,1,45)]),(29,[(0,4,45)]),(24,[(0,4,45)]),(3,[(1,0,31),(0,4,45)]),(11,[(0,2,3),(0,4,45)]),(7,[(0,2,3),(1,0,31),(0,4,45)]),(2,[(1,0,31),(3,4,45)]),(29,[(3,4,45)]),(24,[(3,4,45)]),(3,[(1,0,31),(3,4,45)]),(11,[(0,2,3),(3,4,45)]),(7,[(0,2,3),(1,0,31),(3,4,45)]),(1,[(0,2,3),(1,0,51)]),(2,[(2,1,31),(1,0,51)]),(4,[(2,1,31),(1,0,51)]),(29,[(1,0,51)]),(7,[(0,2,3),(2,1,31),(1,0,51)]),(24,[(1,0,51)]),(3,[(1,0,32)]),(1,[(2,2,3),(1,0,59)]),(2,[(2,1,32),(1,0,59)]),(4,[(1,0,59)]),(7,[(2,2,3),(2,1,32),(1,0,59)]),(24,[(1,0,59)]),(2,[(1,0,33),(0,1,61)]),(37,[(0,1,61)]),(24,[(0,1,61)]),(11,[(0,2,4),(0,1,61)]),(7,[(0,2,4),(1,0,33),(0,1,61)]),(2,[(2,1,33)]),(7,[(0,2,4),(2,1,33)]),(11,[(0,2,4),(2,1,33)]),(1,[(0,2,4),(1,0,63)]),(2,[(2,1,33),(1,0,63)]),(37,[(1,0,63)]),(7,[(0,2,4),(2,1,33),(1,0,63)]),(24,[(1,0,63)]),(3,[(2,3,33),(1,0,64)]),(2,[(2,3,33),(1,0,64)]),(24,[(1,0,64)]),(37,[(1,0,64)]),(7,[(0,2,4),(2,3,33),(1,0,64)]),(4,[(0,2,4),(1,0,64)]),(1,[(2,2,4),(1,0,69)]),(2,[(2,1,34),(1,0,69)]),(5,[(1,0,69)]),(37,[(2,1,34),(1,0,69)]),(7,[(2,2,4),(2,1,34),(1,0,69)]),(24,[(1,0,69)]),(3,[(2,3,34),(1,0,70)]),(2,[(2,3,34),(1,0,70)]),(24,[(1,0,70)]),(5,[(1,0,70)]),(37,[(2,3,34),(1,0,70)]),(7,[(2,2,4),(2,3,34),(1,0,70)]),(4,[(2,2,4),(1,0,70)]),(2,[(0,3,4),(1,0,36),(0,1,74)]),(29,[(0,1,74)]),(37,[(0,1,74)]),(7,[(0,3,4),(1,0,36),(0,1,74)]),(24,[(0,3,4),(1,0,36)]),(4,[(1,0,36),(0,1,74)]),(5,[(1,0,36),(0,1,74)]),(11,[(0,3,4),(0,1,74)]),(41,[(0,3,4),(1,0,36)]),(2,[(0,3,4),(1,0,36),(3,1,74)]),(29,[(3,1,74)]),(37,[(3,1,74)]),(7,[(0,3,4),(1,0,36),(3,1,74)]),(4,[(1,0,36),(3,1,74)]),(5,[(1,0,36),(3,1,74)]),(11,[(0,3,4),(3,1,74)]),(5,[(1,0,36)]),(1,[(0,3,4),(1,0,75)]),(2,[(0,3,4),(2,1,36),(1,0,75)]),(4,[(2,1,36),(1,0,75)]),(29,[(1,0,75)]),(37,[(1,0,75)]),(7,[(0,3,4),(2,1,36),(1,0,75)]),(2,[(1,3,4),(3,0,37)]),(37,[(3,0,37)]),(7,[(1,3,4),(3,0,37)]),(1,[(1,3,4),(1,0,117)]),(3,[(1,3,4),(1,0,117)]),(17,[(1,3,4),(0,7,37)]),(2,[(2,3,4),(1,0,38)]),(4,[(1,0,38)]),(37,[(1,0,38)]),(7,[(2,3,4),(1,0,38)]),(1,[(2,3,4),(1,0,119)]),(3,[(2,3,4),(1,0,119)]),(17,[(2,3,4),(2,7,38)]),(2,[(3,3,4),(1,0,39)]),(7,[(3,3,4),(1,0,39)]),(1,[(3,3,4),(1,0,121)]),(3,[(3,3,4),(1,0,121)]),(17,[(3,3,4),(2,7,39)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 11 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice47 : Slice h0R h0G (subcubeFast 36 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice46 : Slice h0R h0G (subcubeFast 36 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice45 : Slice h0R h0G (subcubeFast 34 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice44 : Slice h0R h0G (subcubeFast 34 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice43 : Slice h0R h0G (subcubeFast 32 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice42 : Slice h0R h0G (subcubeFast 32 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice41 : Slice h0R h0G (subcubeFast 32 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice40 : Slice h0R h0G (subcubeFast 16 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice39 : Slice h0R h0G (subcubeFast 16 6) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice38 : Slice h0R h0G (subcubeFast 16 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice37 : Slice h0R h0G (subcubeFast 16 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice36 : Slice h0R h0G (subcubeFast 8 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice35 : Slice h0R h0G (subcubeFast 8 20) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 8 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 8 6) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 8 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 8 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 8 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 4 16) 4 := slice_fast_direct (zDead := 32) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 4 8) 4 := slice_fast_direct (zDead := 32) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 4 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 4 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 2 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 2 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 2 8) 4 := slice_fast_direct (zDead := 32) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 2 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 2 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 2 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 1 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 1 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 1 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 1 6) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 1 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 1 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 1 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 0 48) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 0 40) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 0 34) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 0 32) 10 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 0 20) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 16) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 8) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 6) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h52Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h53Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (forall_cons (fun _ h => by cases h; exact h0Slice25) (forall_cons (fun _ h => by cases h; exact h0Slice26) (forall_cons (fun _ h => by cases h; exact h0Slice27) (forall_cons (fun _ h => by cases h; exact h0Slice28) (forall_cons (fun _ h => by cases h; exact h0Slice29) (forall_cons (fun _ h => by cases h; exact h0Slice30) (forall_cons (fun _ h => by cases h; exact h0Slice31) (forall_cons (fun _ h => by cases h; exact h0Slice32) (forall_cons (fun _ h => by cases h; exact h0Slice33) (forall_cons (fun _ h => by cases h; exact h0Slice34) (forall_cons (fun _ h => by cases h; exact h0Slice35) (forall_cons (fun _ h => by cases h; exact h0Slice36) (forall_cons (fun _ h => by cases h; exact h0Slice37) (forall_cons (fun _ h => by cases h; exact h0Slice38) (forall_cons (fun _ h => by cases h; exact h0Slice39) (forall_cons (fun _ h => by cases h; exact h0Slice40) (forall_cons (fun _ h => by cases h; exact h0Slice41) (forall_cons (fun _ h => by cases h; exact h0Slice42) (forall_cons (fun _ h => by cases h; exact h0Slice43) (forall_cons (fun _ h => by cases h; exact h0Slice44) (forall_cons (fun _ h => by cases h; exact h0Slice45) (forall_cons (fun _ h => by cases h; exact h0Slice46) (forall_cons (fun _ h => by cases h; exact h0Slice47) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (5 - 1) xs.toFinset) h0Empty := trivial
def h0Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,5,55],[]),([0,1,2,4,5,176],[]),([1,2,3,4,5,290],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test5_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 5 h0Block5_0 = true := by decide +kernel
def h0Nodes5 : List NodeSpec := h0Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 5 h0Nodes5 = true := h0Test5_0
def h0Bucket5 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 5 xs.toFinset) h0Bucket5 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check5
def h0Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,5,53,54],[]),([0,1,2,3,5,56,57],[]),([0,1,2,4,5,167,168],[]),([0,1,2,4,5,169,170],[]),([1,2,3,4,5,259,289],[]),([1,2,3,4,5,260,291],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Block6_0 = true := by decide +kernel
def h0Nodes6 : List NodeSpec := h0Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Nodes6 = true := h0Test6_0
def h0Bucket6 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 6 xs.toFinset) h0Bucket6 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket5Ok h0Check6
def h0Block7_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,52,53],[10,11,14,18,26,29,34,35,36,38,39]),([0,1,2,3,4,5,52,54],[10,11,26,35,36,37,40]),([0,1,2,3,4,5,52,56],[10,11,41]),([0,1,2,3,4,5,52,57],[10,11,18,35,42]),([0,1,2,3,4,5,6,66],[9,66,76]),([0,1,2,3,4,5,89,90],[6,7,20,110,114,165,166]),([0,1,2,3,4,5,77,89],[6,7,168]),([0,2,3,4,95,98],[214,221,224,225,226,227,228]),([0,2,3,4,98,107],[227,248,274,279,280,283,284,285]),([0,1,2,3,4,114],[149,247,270,333,334,335,336,337,338,339]),([0,1,2,3,4,115],[153,157,250,341,344,345,346,347,348]),([1,2,3,4,5,74,124],[9,10,110,141,318,322])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_0 = true := by decide +kernel
def h0Block7_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,124],[0,1,4,6,7,9,10,12,13,110]),([0,1,2,3,4,5,161,162],[10,11,65,580,585,595,598]),([0,1,2,3,4,5,161,163],[10,11,65]),([0,1,2,3,4,5,161],[0,1,4,6,7,8,10,11,12,13,594]),([0,1,2,3,5,27,38,166],[11,75,589,614]),([0,1,2,3,4,5,27,172],[1,9,11]),([0,1,2,3,4,5,10,175],[9]),([0,1,2,3,4,5,166,167],[8,9,585,589,610,624,637,638,641]),([0,1,2,3,4,5,166,168],[8,9,624,638,639,640]),([0,1,2,3,4,5,166,169],[8,9]),([0,1,2,3,4,5,166,170],[8,9]),([0,1,2,3,5,29,178],[1,11,87,589,646,652,653])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_1 = true := by decide +kernel
def h0Block7_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,178,179],[1,4,110,117,589,675,676]),([0,1,2,3,4,5,178,180],[1,4,676,677]),([0,1,2,3,4,5,182],[0,1,4,6,7,8,11,12,13,412,685,686]),([0,1,2,3,4,5,79,182],[0,8,412]),([0,1,2,3,5,27,38,187],[]),([0,1,2,3,4,5,27,189],[9]),([0,1,2,3,4,5,190,200],[6,7,610,842,847,882]),([0,1,2,3,4,5,191,200],[6,7,882]),([1,2,3,4,5,108,218],[4,10,277,974,977]),([0,1,2,3,4,5,218],[0,4,6,7,8,9,10,12,13,277]),([0,1,2,3,4,5,223],[0,1,4,6,7,9,10,12,13,56,1075]),([0,1,2,3,4,5,236],[0,4,6,7,9,10,11,12,13,554])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_2 = true := by decide +kernel
def h0Block7_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,237,238],[6,7,1187]),([0,1,2,3,4,5,237,239],[6,7,1187]),([0,1,2,3,4,5,237],[0,1,4,6,7,8,10,11,12,13,1188]),([0,1,2,3,4,5,249,250],[1,4,14,1168,1176,1243,1246]),([0,1,2,3,4,5,247,249],[1,4,1247]),([0,2,3,4,107,245],[274,280,285,1087,1222,1309,1310,1311,1312,1313]),([0,1,2,3,4,5,258],[0,1,6,7,8,11,12,13,26,68,282,1087,1322,1323,1324]),([1,2,3,4,5,96,236],[4,9,218,554,1274,1367]),([1,2,3,4,5,18,45,46],[1352,1398,1401]),([1,2,3,4,5,45,268],[6,9,14,1329,1402,1403]),([0,1,2,3,4,5,268],[0,1,4,6,7,9,10,12,13,14,1403]),([0,1,2,3,5,96,100,126],[4,10,11,68])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_3 = true := by decide +kernel
def h0Block7_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,5,96,100,159],[4,10,68,253,587]),([0,1,2,3,4,5,100,130],[0,4,10,1515]),([0,1,2,3,4,5,287],[0,1,6,7,9,11,12,13]),([0,1,2,3,4,5,288,289],[0,26,31,68,616,624,641,1635,1636,1637,1638]),([0,1,2,3,4,5,259,288],[0,68,624,641,1635,1636,1637,1638,1639]),([0,1,2,3,4,5,288,291],[0,68]),([0,1,2,3,4,5,260,288],[0,68]),([0,1,2,3,4,5,46,49],[1,4,10,11,24,1329,1631,1700,1702,1703])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_4 = true := by decide +kernel
def h0Nodes7 : List NodeSpec := h0Block7_0 ++ h0Block7_1 ++ h0Block7_2 ++ h0Block7_3 ++ h0Block7_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Nodes7 = true := by
  unfold h0Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h0Test7_0,h0Test7_1⟩,h0Test7_2⟩,h0Test7_3⟩,h0Test7_4⟩
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket6Ok h0Check7
def h0Block8_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,6,45],[0,1,2,3,4,14,17,18,19,20,21,22,23,24,25]),([0,1,2,3,4,5,52],[0,1,4,6,7,10,11,12,13,14,18,26,29,34,35,36,37]),([0,1,2,3,4,5,6,52],[0,1,2,3,4,6,14,18,20,21,23,34,35]),([0,1,2,3,4,5,31,52],[0,6,7,14,15,18,26,30,31,32,33,34,35,36,43]),([0,1,2,3,4,5,60],[0,1,4,6,7,10,11,12,13,18,27,44,47,48,53,54,55]),([0,1,2,3,4,5,6,61],[0,1,2,3,4,18,23,24,25,27,29,56,59,60,61,62]),([0,1,2,3,4,5,6,64],[0,1,2,3,4,6,9,10,18,20,23,27,29,64,66,67,68,69,70,71,72,73,74,75,77]),([0,1,2,3,4,5,67],[0,1,4,6,7,8,9,12,13,18,20,56,63,80,81,82,83]),([0,1,2,3,4,5,6,67],[0,1,2,3,4,6,18,23,27,29,56,80,81]),([0,1,2,3,4,5,6,70],[0,1,2,3,4,6,9,11,18,21,23,27,29,68,77,87,89,91,92,93,94,95,96,97,98,99,100]),([0,1,2,3,4,5,72],[0,1,4,6,7,8,9,12,13,18,21,84,87,88,103,104,105,106]),([0,1,3,4,5,36,47],[0,4,6,25,107,108,109,110,111,112,113,114,115,116,117,118,119,120])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := nodesWithIdentity [([0,1,3,4,5,37,47],[0,4,6,25,107,108,111,112,116,118,120,121,122,123,124,125]),([0,1,3,4,5,38,47],[0,4,6,25,107,108,111,112,116,118,120,126,127,128,129,130,131]),([0,1,3,4,5,39,47],[0,4,6,25,107,108,111,112,116,120,132,133,134,135,136]),([0,1,2,3,4,5,6,74],[0,1,2,3,4,18,20,21,23,27,47,77,110,140,141,142]),([0,1,2,3,4,5,9,36],[0,1,4,5,8,9,10,11,77,110,114,117,143,144,145,146,147,148,149,150,151]),([0,1,2,3,4,6,76],[9,10,12,20,23,29,119,139,152,153,154,155,156,157,158,159,160,161,162,163]),([0,1,2,3,4,5,89],[0,1,4,6,7,8,10,11,12,13,20,29,110,114,164,165,166,167,169]),([0,1,2,3,4,5,6,89],[0,1,2,3,4,10,18,20,21,23,27,110,164,166]),([0,1,2,3,4,5,36,89],[0,8,11,20,110,114,117,137,145,149,150,164,165,166,167,170]),([0,1,2,4,5,37,48],[0,4,9,10,27,47,122,174,177,178,179,180,181,182]),([0,1,2,3,4,5,92],[0,1,4,6,7,8,11,12,13,21,27,47,122,174,185,186,187,188]),([0,1,2,3,4,5,93],[0,1,4,6,7,8,10,11,12,13,21,29,87,127,129,195,196,197,198,199])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
def h0Block8_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,94],[0,1,4,6,7,8,10,12,13,20,27,47,133,203,208,209,210]),([0,2,3,4,5,7,95],[0,4,8,68,214,216,218,219,220,221,222,223,228]),([0,1,2,4,5,13,97],[0,1,9,68,214,216,221,232,233,234,235,236]),([0,1,2,3,4,13,98],[1,12,157,214,221,226,227,241,242,243,244,245,246,247,248]),([0,1,2,3,4,5,96],[0,1,4,6,7,8,10,11,12,13,68,214,218,221,252,253,254]),([0,2,3,4,5,7,91],[0,4,9,68,212,258,259,260,261,262]),([0,1,2,3,4,15,98],[1,12,68,226,227,241,244,245,247,248,255,263,268,269,270,271,272]),([0,2,3,4,5,7,107],[0,4,11,68,90,240,274,277,278,279,280,281,282,285]),([0,1,2,3,4,17,98],[1,12,77,157,226,227,241,244,245,247,248,274,280,289,290,291]),([0,2,3,4,5,7,109],[0,4,10,68,239,293,296,297,298,299,300]),([0,1,2,3,4,5,19,97],[0,1,9,10,11,68,87,90,216,232,235,236,293,300,301,302,303,304,305,306,307,308,309,310]),([0,1,2,3,4,19,98],[1,12,77,226,227,241,244,245,247,293,300,309,312,313,314])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_2 = true := by decide +kernel
def h0Block8_3 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,7,74],[4,9,10,68,110,141,239,259,318,319,320,321,322,323]),([0,2,3,4,5,7,75],[0,4,9,10,77,137,239,259,316,324,325,326,327,328,329]),([0,1,2,3,4,36,98],[1,12,68,77,137,149,226,227,241,244,245,247,248,270,316,330,331,332,338]),([0,1,2,3,4,7,76],[9,10,12,152,153,157,158,159,160,162,239,250,259,317,340,341,342,343]),([0,1,2,3,4,5,116],[0,1,4,6,7,8,10,11,12,13,77,137,239,259,316,349,350,351,352,353]),([0,1,2,3,4,37,98],[1,12,68,171,184,226,227,241,244,245,247,248,338,355,357,358,359]),([0,1,2,3,4,5,117],[0,1,4,6,7,8,11,12,13,171,175,216,240,355,360,361,362,363]),([0,1,2,3,4,5,7,117],[0,1,4,8,171,213,216,231,240,250,251,360,361,362]),([0,1,2,3,4,5,37,117],[1,8,11,47,122,125,171,174,176,183,184,216,360,361,362]),([0,1,2,3,4,38,98],[1,12,68,189,194,226,227,241,244,245,247,248,270,338,365,367,368,369]),([0,1,2,3,4,5,119],[0,1,4,6,7,8,10,11,12,13,77,189,240,259,365,370,371,372,373,374]),([0,1,2,4,5,39,97],[1,9,11,68,200,216,235,236,376,378,379,380,381])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_3 = true := by decide +kernel
def h0Block8_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,39,98],[1,12,68,200,207,226,227,241,244,245,247,338,376,382,383,384]),([0,1,2,3,4,5,121],[0,1,4,6,7,8,10,12,13,200,216,239,376,381,385,386,387]),([1,2,3,4,5,8,74],[4,9,10,77,110,141,318,322,392,393,394,395,396,397]),([0,1,2,3,4,5,8,74],[0,1,4,47,110,141,142,388,389,392,393,396,398,399,400,401]),([0,1,2,3,4,8,76],[9,10,12,152,153,158,159,160,162,391,394,396,401,402,403,404,405]),([0,1,2,3,4,5,125],[0,1,6,7,8,10,11,12,13,110,137,316,394,396,406,407,408,409]),([0,2,3,4,5,8,79],[4,8,11,47,68,171,399,400,412,413,414,415,416,417]),([0,1,2,3,4,5,127],[0,1,6,7,8,11,12,13,122,171,355,399,400,418,419,420]),([0,1,2,3,4,5,128],[0,1,6,7,8,10,11,12,13,127,189,365,394,399,423,424,425,426]),([0,1,2,3,4,5,129],[0,1,6,7,8,10,12,13,133,200,376,396,400,429,430]),([0,1,2,3,4,5,9,11,37],[0,25,68,125,146,148,151,171,174,176,435,437]),([0,1,2,3,4,5,9,11,39],[0,25,68,136,146,148,151,200,203,205,435,437])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_4 = true := by decide +kernel
def h0Block8_5 : List NodeSpec := nodesWithIdentity [([0,1,2,4,5,13,42],[0,4,9,68,111,148,447,448,449,450,451]),([0,1,2,3,4,5,9,87],[0,1,4,5,9,10,11,68,77,110,111,144,146,147,148,151,441,444,455,459,460,461,462,463]),([0,1,2,3,4,5,19,42],[0,1,4,9,10,11,68,87,148,151,293,301,302,303,305,309,310,448,466,467,468,469,470,471,472]),([0,1,2,3,4,5,9,111],[0,1,4,5,9,10,11,68,87,144,146,147,148,151,311,441,444,455,473,474,475,476,477,478,479]),([0,1,2,3,4,5,142],[0,1,6,7,8,10,11,12,13,26,146,151,455,481,482,483,484,485]),([0,1,2,3,4,5,143],[0,1,4,6,7,10,11,12,13,48,146,148,151,487,488,489,490]),([0,1,2,3,4,5,9,64],[0,1,4,5,6,9,10,64,66,67,68,71,72,73,74,77,111,144,146,147,148,151,444,455,492]),([0,1,2,3,4,5,144],[0,1,6,7,8,9,11,12,13,63,144,146,151,493,494,495,496]),([0,1,2,3,4,5,9,70],[0,1,4,5,6,9,11,68,77,89,91,92,95,96,97,98,111,146,147,148,151,441,444,455,498,499]),([0,1,2,3,4,5,145],[0,1,6,7,8,9,10,12,13,88,146,151,441,500,501,502,503,504]),([0,1,2,3,4,5,9,35,36],[4,117,144,145,146,147,151,506,507,508,509,510,511]),([0,1,2,3,4,5,9,148],[4,5,7,8,9,28,68,144,146,147,148,151,441,444,455,512,513,514,515,516,517])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_5 = true := by decide +kernel
def h0Block8_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,9,76],[9,10,12,143,144,152,153,155,157,158,159,160,162,444,455,509,518,519,520]),([0,1,2,3,4,5,88],[0,1,6,7,8,11,12,13,114,144,151,455,521,522,523,524,525,526]),([0,1,2,3,4,5,36,88],[4,8,11,110,114,117,137,144,145,149,150,521,522,523,524,525,527]),([0,1,2,3,4,5,36,85],[8,11,77,114,117,145,149,150,151,318,528,529,530,531,532]),([0,1,2,3,4,5,132],[0,1,4,6,7,8,10,11,12,13,148,151,174,441,535,536,537,538,539]),([0,1,2,3,4,5,152],[0,1,6,7,8,10,12,13,129,151,441,455,542,543,544,545,546,547]),([0,1,2,3,4,5,134],[0,1,4,6,7,8,10,11,12,13,144,148,151,203,550,551,552,553]),([0,1,2,3,4,9,138],[119,151,444,455,470,509,562,563,564,565,566,567]),([0,1,2,3,4,5,9,151],[0,1,4,5,8,9,10,11,68,114,144,146,147,148,151,441,444,455,525,572,573,574]),([0,1,2,3,4,5,161],[0,1,4,6,7,8,10,11,12,13,65,580,585,586,594,595,596,597]),([0,1,2,3,4,5,10,161],[0,4,6,7,68,579,580,583,584,585,589,590,593,594,595]),([0,1,2,3,4,5,23,161],[0,1,8,65,580,581,585,587,588,591,592,594,595,596,597,598])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_6 = true := by decide +kernel
def h0Block8_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,10,150],[6,7,68,151,513,514,579,585,586,589,590,593,599]),([0,1,2,3,4,5,164],[0,1,4,6,7,8,10,11,12,13,47,584,585,600,607,608,609]),([0,1,2,3,5,10,27,38],[10,11,75,87,129,189,583,584,589,590,613,614,615,616,617,618]),([0,1,2,3,4,5,27,158],[0,1,4,6,9,10,11,47,111,584,610,611,616,619,620,621,622,623,624,625,626,627,628,629]),([0,1,2,3,4,5,10,165],[0,4,6,7,9,10,68,75,579,583,584,585,586,589,590,593,615,630,631,632,633,634,635,636]),([0,1,2,3,4,5,166],[0,1,6,7,8,9,10,11,12,13,585,589,610,637,638,639,640]),([0,1,2,3,4,5,10,166],[0,6,7,10,579,583,584,586,589,590,593,610,637,638]),([0,1,2,3,4,5,27,166],[0,1,11,589,610,611,615,616,624,628,629,637,638,639]),([0,1,2,3,5,10,29,36],[10,11,87,114,137,583,584,589,590,645,646,647,648,649,650,651,654]),([0,1,2,3,4,5,10,113],[0,4,6,7,9,11,68,87,137,163,204,316,579,583,584,585,586,589,590,593,636,655,656,657,658]),([0,1,2,3,4,5,177],[0,1,6,7,8,9,10,11,12,13,87,585,590,642,661,662,663,664]),([0,1,2,3,4,5,36,147],[0,4,6,8,9,10,11,47,87,110,111,114,117,119,145,147,149,150,151,316,460,506,654,665,666,667,668])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_7 = true := by decide +kernel
def h0Block8_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,10,75],[0,4,6,7,9,10,68,77,137,324,328,579,583,584,585,586,589,590,593,654,656,671,672,673]),([0,1,2,3,4,5,178],[0,1,4,6,7,8,10,11,12,13,110,586,589,653,674,675,676,678]),([0,1,2,3,4,5,10,178],[0,6,7,10,110,579,583,584,585,589,590,593,674,675]),([0,1,2,3,4,5,36,178],[0,8,11,110,114,117,137,145,149,150,589,653,674,675,679]),([0,1,2,3,4,5,10,79],[0,4,6,7,8,11,47,68,171,412,416,417,579,583,584,585,590,593,681,682,683,684]),([0,1,2,3,4,5,183],[0,1,4,6,7,8,11,12,13,47,122,584,590,687,688,689,690]),([0,1,2,3,4,5,10,81],[0,4,6,7,9,11,68,77,87,189,579,583,584,585,586,589,590,593,692,693,694,695,696,697]),([0,1,2,3,4,5,171],[0,1,4,6,7,8,10,11,12,13,75,87,127,586,590,698,699,700,701,702]),([0,1,2,3,4,5,10,83],[0,4,6,7,8,10,47,68,200,381,579,583,584,585,589,593,704,705,706,707,708,709]),([0,1,2,3,4,5,184],[0,1,4,6,7,8,10,12,13,47,133,584,589,710,711,712]),([0,1,2,3,4,5,11,95],[0,4,6,7,8,28,68,214,218,221,222,223,228,433,435,437,439,440,442,443,716,717,718,719,720,721]),([0,1,2,4,5,13,131],[0,6,9,68,90,437,715,722,723,724,725])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_8 = true := by decide +kernel
def h0Block8_9 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,15,73],[0,2,4,6,7,8,9,25,47,68,108,175,264,265,266,267,271,273,454,728,729,730,731,732,733]),([0,1,2,3,4,5,11,91],[0,4,6,7,9,27,28,68,175,212,258,261,262,433,435,437,438,439,440,442,443,727,734,735,736]),([0,1,2,3,4,5,11,107],[0,4,6,7,11,28,90,274,277,280,282,285,433,435,437,439,440,442,443,727,738,739,740,741,742,743,744]),([0,1,2,3,4,5,11,87],[0,6,7,9,11,25,68,77,110,111,175,433,435,437,439,440,442,443,459,460,461,462,463,636,715,727,745,746]),([0,1,2,3,4,5,19,73],[0,2,4,6,7,10,11,25,68,87,108,301,302,303,305,309,310,311,654,728,731,733,748,749,750]),([0,1,2,3,4,5,11,109],[0,4,6,7,10,28,293,296,300,433,435,437,438,439,440,442,443,727,751,752,753,754,755,756,757]),([0,1,2,3,4,5,19,131],[0,6,7,9,10,11,25,68,87,293,301,302,303,305,309,310,437,438,722,758,759,760,761,762,763,764]),([0,1,2,3,4,5,11,111],[0,6,7,9,10,25,68,87,311,433,435,437,439,440,442,443,473,474,475,476,477,478,479,654,727]),([0,1,2,3,4,5,185],[0,1,6,7,8,10,11,12,13,25,435,598,727,766,767,768,769,770]),([0,1,2,3,4,5,23,185],[1,6,8,65,435,580,581,587,588,591,592,598,715,766,767,768,769,770]),([0,1,2,3,4,5,186],[0,1,4,6,7,10,11,12,13,25,435,437,772,773,774,775,776]),([0,1,2,3,5,11,27,38],[10,11,75,129,189,433,437,439,440,613,614,615,616,617,618,778,779])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_9 = true := by decide +kernel
def h0Block8_10 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,27,131],[1,4,6,9,10,11,68,77,100,437,610,611,616,624,628,629,715,722,758,759,761,762,763,780,781,782]),([0,1,2,3,4,5,11,165],[0,4,6,7,9,10,25,68,433,435,437,439,440,442,443,615,630,631,632,633,634,635,636,715,727,783,784]),([0,1,2,3,4,5,187],[0,1,6,7,8,9,11,12,13,25,435,439,624,785,786,787,788,789]),([0,1,2,3,4,5,27,187],[1,6,11,439,610,611,615,616,624,628,629,785,786,787,788]),([0,1,2,3,5,11,29,36],[10,11,114,137,381,433,437,439,440,645,646,647,648,649,650,654,792,793,794]),([0,1,2,3,4,5,11,113],[0,4,6,7,9,11,25,68,87,137,163,316,433,435,437,439,440,442,443,636,655,656,657,658,727,792]),([0,1,2,3,4,5,192],[0,1,6,7,8,9,10,12,13,25,435,440,791,795,796,797,798,799]),([0,1,2,3,4,5,36,73],[2,4,6,8,9,10,11,24,68,108,110,113,114,115,117,119,145,149,150,175,316,654,668,728,733,750]),([0,1,2,3,4,5,11,75],[0,4,6,7,9,10,25,68,77,137,316,324,328,433,435,437,439,440,442,443,656,671,672,673,727,792,801]),([0,1,2,3,4,5,193],[0,1,4,6,7,8,11,12,13,25,117,439,727,802,803,804,805,806,807]),([0,1,2,3,4,5,36,193],[6,8,11,110,114,117,137,145,149,150,439,802,804,805,806,808]),([0,1,2,3,4,5,11,79],[0,4,6,7,8,11,25,68,171,412,416,417,433,435,437,440,442,443,682,683,684,715,810,811,812])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_10 = true := by decide +kernel
def h0Block8_11 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,133],[0,1,4,6,7,8,11,12,13,25,125,437,440,813,814,815,816,817]),([0,1,2,3,4,5,11,81],[0,4,6,7,9,11,25,68,77,189,433,435,437,439,440,442,443,692,693,694,695,696,697,727,778,819]),([0,1,2,3,4,5,188],[0,1,4,6,7,8,10,12,13,25,131,440,727,820,821,822,823,824,825]),([0,1,2,3,4,5,11,83],[0,4,6,7,8,10,25,68,200,381,433,435,437,439,442,443,704,705,706,707,708,709,827,828]),([0,1,2,3,4,5,135],[0,1,4,6,7,8,10,12,13,25,136,437,439,829,830,831,832]),([0,1,2,3,4,5,196],[0,1,6,7,9,10,11,12,13,151,841,851,854,859,860,861]),([0,1,2,3,4,5,12,108],[0,8,9,75,151,277,834,835,840,841,846,847,850,864,865]),([0,1,2,3,4,5,15,27],[0,1,4,8,9,10,11,47,75,255,264,265,266,273,610,611,616,624,628,629,866]),([0,1,2,3,4,27,194],[0,9,12,157,610,616,628,669,867,868,869,870,871,872,873,874,875,876]),([0,1,2,3,4,5,200],[0,1,6,7,8,9,10,11,12,13,610,616,842,847,877,878,879,880,881]),([0,1,2,3,4,5,12,200],[0,8,9,10,610,834,835,840,841,846,847,850,877,878]),([0,1,2,3,4,5,27,200],[0,1,11,610,611,615,616,624,628,629,847,877,878,879,880])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_11 = true := by decide +kernel
def h0Block8_12 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,28,137],[0,4,9,10,151,467,883,887,888,889,890,891,892]),([0,1,2,3,4,28,194],[0,9,12,151,669,869,871,873,874,875,876,883,887,896,897,898,899]),([0,1,2,3,4,5,202],[0,1,6,7,9,11,12,13,839,841,846,883,887,900,901,902,903]),([0,1,2,3,4,29,194],[0,9,12,87,642,648,660,669,869,870,871,873,874,875,876,906,907,908]),([0,1,2,3,4,5,203],[0,1,6,7,8,9,10,11,12,13,87,642,648,842,846,909,910,911,912,913]),([0,1,2,3,4,30,194],[0,9,12,151,669,869,871,874,875,876,914,918,922,923,924,925]),([0,1,2,3,4,5,205],[0,1,6,7,9,10,12,13,839,841,847,914,918,926,927,928]),([0,2,3,4,5,21,137],[0,4,6,9,87,151,467,892,930,931,932,933]),([0,1,2,3,4,5,33,137],[0,4,6,7,9,10,11,56,57,63,78,79,83,87,148,151,163,467,715,889,892,929,934]),([0,1,2,3,4,5,206],[0,1,4,6,7,9,12,13,56,83,840,847,934,936,937,938,939]),([0,1,2,3,4,5,12,69],[0,4,6,8,9,11,24,68,85,87,111,119,834,835,840,841,842,846,850,942,943,944,945,946,947,948,949,950]),([0,1,2,3,4,5,208],[0,1,4,6,7,9,12,13,84,87,840,846,941,951,952,953,954,955])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_12 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_12 = true := by decide +kernel
def h0Block8_13 : List NodeSpec := nodesWithIdentity [([0,1,2,4,5,13,87],[0,9,11,68,110,111,175,238,460,461,958]),([0,1,2,3,4,5,19,95],[0,4,8,10,11,68,87,111,175,214,218,222,223,228,293,301,302,303,309,310,311,716,719,721,961]),([0,1,2,4,5,13,111],[0,9,10,68,111,237,311,473,962,963]),([0,2,3,4,5,22,95],[4,7,8,68,111,214,222,223,228,716,852,966,967]),([0,1,2,3,4,5,209],[0,1,6,7,8,9,10,11,12,13,111,214,229,852,968,969,970]),([1,2,3,4,5,13,108],[4,9,10,68,111,237,277,447,973,974,975,976,977,978]),([0,1,2,4,5,13,165],[0,4,9,10,75,237,447,615,631,715,979,980,981,982]),([0,1,2,3,4,5,210],[0,1,6,7,8,9,10,11,12,13,75,237,447,615,715,983,984,985,986,987]),([0,1,2,3,4,5,211],[0,1,6,7,8,9,11,12,13,77,214,221,238,885,990,991,992,993]),([0,1,2,3,4,5,13,211],[0,1,8,9,214,229,230,238,246,249,885,990,991,992]),([0,1,2,3,4,5,28,211],[1,8,11,151,214,883,885,887,893,894,895,899,990,991,992]),([0,1,2,3,4,5,212],[0,1,6,7,8,9,10,11,12,13,238,381,447,647,715,996,997,998,999,1000])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_13 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_13 = true := by decide +kernel
def h0Block8_14 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,30,95],[4,8,11,68,175,214,221,222,223,228,916,1003,1004,1005]),([0,1,2,3,4,5,213],[0,1,6,7,8,9,10,12,13,77,214,221,237,916,1006,1007,1008]),([0,1,2,3,4,5,33,95],[4,6,7,8,10,11,56,57,63,64,68,78,79,83,111,175,214,218,221,222,223,228,716,719,721,1009]),([1,2,3,4,5,13,61],[6,9,10,56,68,229,237,1011,1012,1013,1014]),([0,1,2,3,4,5,215],[0,1,4,6,7,8,9,12,13,64,111,229,237,1015,1016,1017,1018]),([0,1,2,3,4,5,216],[0,1,4,6,7,8,9,12,13,89,111,229,238,1020,1021,1022,1023,1024]),([0,1,2,3,4,5,217],[0,1,6,7,8,10,11,12,13,151,851,852,1030,1036,1037]),([1,2,3,4,5,14,108],[4,9,10,68,75,111,277,974,977,1031,1033,1040,1041,1042]),([0,1,2,3,4,5,14,108],[0,8,9,151,277,864,865,1025,1026,1029,1030,1032,1033,1034]),([0,1,2,3,4,5,219],[0,1,6,7,8,10,11,12,13,75,610,615,1031,1033,1043,1044,1045,1046]),([0,1,2,4,5,14,201],[1,9,11,68,151,885,1030,1032,1049,1050,1051,1052,1053,1054]),([0,1,2,3,4,5,220],[0,1,6,7,8,11,12,13,883,885,1028,1030,1032,1055,1056,1057])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_14 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_14 = true := by decide +kernel
def h0Block8_15 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,221],[0,1,6,7,8,10,11,12,13,87,642,647,1031,1032,1060,1061,1062,1063]),([0,1,2,3,4,5,222],[0,1,6,7,8,10,12,13,914,916,1028,1030,1033,1066,1067]),([0,1,2,3,4,5,33,153],[0,4,6,7,8,10,11,56,57,63,64,75,78,79,83,87,151,163,455,559,715,1068,1069,1070]),([1,2,3,4,5,14,61],[6,9,10,56,65,68,75,1012,1029,1033,1072,1073,1074]),([0,1,2,3,4,5,14,61],[0,8,9,25,56,61,62,1025,1026,1029,1030,1031,1034,1072,1073]),([0,1,2,3,4,5,224],[0,1,4,6,7,8,12,13,56,64,83,1029,1033,1076,1077,1078]),([0,1,2,3,4,5,225],[0,1,4,6,7,8,12,13,84,87,89,1029,1032,1080,1081,1082,1083]),([0,1,2,3,4,5,15,107],[0,4,8,9,10,11,47,68,111,255,264,265,266,267,271,273,274,277,282,285,454,715,738,742,743,744,1087,1088]),([0,1,2,3,4,5,19,91],[0,4,8,9,10,11,27,47,68,87,111,212,258,262,293,301,302,303,305,309,310,311,734,736]),([0,1,2,3,4,5,15,109],[0,4,8,9,10,11,47,68,87,255,264,265,266,267,271,273,293,296,454,751,753,754,755,756,757,1091]),([0,1,2,3,4,5,226],[0,1,4,6,7,8,10,11,12,13,111,255,264,854,1094,1095,1096,1097]),([0,1,2,3,4,5,199],[0,1,6,7,8,11,12,13,47,266,454,616,1099,1100,1101,1102,1103,1104])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_15 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_15 = true := by decide +kernel
def h0Block8_16 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,27,199],[1,9,11,266,610,611,615,616,624,628,629,1099,1100,1101,1102,1103]),([0,1,2,3,4,5,27,174],[1,11,47,75,611,616,624,628,629,631,1105,1106,1107,1108,1109]),([0,1,2,3,4,5,228],[0,1,4,6,7,8,10,11,12,13,255,263,267,887,1112,1113,1114,1115,1116]),([0,1,2,3,4,5,229],[0,1,6,7,8,10,12,13,47,267,454,648,1119,1120,1121,1122,1123,1124]),([0,1,2,3,4,5,230],[0,1,4,6,7,8,10,11,12,13,255,263,266,918,1127,1128,1129,1130]),([0,1,2,3,4,5,33,91],[4,6,7,9,10,11,27,56,57,63,64,68,77,78,79,111,157,212,258,261,734,736,934]),([0,1,2,3,4,5,231],[0,1,4,6,7,8,11,12,13,111,264,266,934,1136,1137,1138,1139,1140]),([0,1,2,3,4,5,15,69],[0,4,6,8,9,11,24,47,68,85,111,255,263,264,265,267,271,273,454,942,943,945,947,948,949,950,1142,1143]),([0,1,2,3,4,5,232],[0,1,4,6,7,8,10,12,13,111,264,267,941,1144,1145,1146,1147,1148,1149]),([0,1,2,3,4,5,15,227],[0,1,4,8,9,10,11,47,68,77,255,264,265,266,267,271,273,454,616,1100,1157,1158,1159]),([0,1,2,3,4,5,16,195],[0,1,6,9,10,11,68,90,100,151,852,1164,1165,1168,1169,1172,1174,1175,1176,1177,1178,1179,1180,1181,1182]),([0,1,2,3,4,5,235],[0,1,6,7,8,9,10,12,13,151,851,856,1169,1183,1184])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_16 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_16 = true := by decide +kernel
def h0Block8_17 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,16,96],[0,10,11,151,175,218,252,253,1164,1165,1168,1169,1170,1171,1172]),([0,1,2,3,4,5,16,40],[10,11,68,151,554,556,557,1164,1165,1168,1170,1172,1176]),([0,1,2,3,4,5,237],[0,1,4,6,7,8,10,11,12,13,580,588,1170,1176,1187,1188,1189,1190]),([0,1,2,3,4,5,16,237],[0,4,10,11,68,580,1164,1165,1168,1169,1170,1171,1172,1187,1188]),([0,1,2,3,4,5,23,237],[0,1,8,65,580,581,588,591,592,598,1170,1187,1188,1189,1190]),([0,1,2,3,4,5,16,240],[0,10,11,68,151,580,1164,1165,1168,1170,1172,1176]),([0,2,3,4,5,24,156],[0,4,9,10,151,576,1191,1193,1195,1196,1197]),([0,1,2,4,5,24,234],[0,4,9,10,151,1162,1191,1193,1197,1200,1201]),([0,1,2,3,4,5,243],[0,1,6,7,8,10,12,13,1167,1169,1171,1191,1193,1204,1205]),([0,1,2,3,4,5,16,23],[0,4,10,11,68,151,580,581,591,1164,1165,1168,1169,1170,1172,1186]),([0,1,2,3,4,5,244],[0,1,4,6,7,8,10,12,13,47,600,604,1170,1171,1208,1209,1210]),([0,1,2,3,4,16,245],[1,9,12,338,1169,1172,1176,1214,1219,1220,1221,1222,1223,1224,1225,1226])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_17 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_17 = true := by decide +kernel
def h0Block8_18 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,246],[0,1,4,6,7,10,12,13,1167,1169,1176,1211,1213,1227,1228,1229]),([0,1,2,3,4,5,31,156],[0,4,6,7,8,9,10,14,15,26,31,32,33,47,151,163,438,441,576,715,1195,1230,1231,1232]),([0,1,2,3,4,5,16,45],[0,10,11,14,19,22,25,90,1164,1165,1168,1169,1170,1172,1234]),([0,1,2,3,4,5,16,51],[0,4,6,9,10,11,15,24,68,438,1164,1165,1168,1169,1170,1172,1176,1235,1236,1237,1238,1239,1240,1241,1242]),([0,1,2,3,4,5,249],[0,1,4,6,7,10,12,13,14,31,1168,1176,1243,1244,1245,1246]),([0,1,2,3,4,5,16,249],[0,6,10,14,1164,1165,1168,1169,1170,1172,1243,1244]),([0,1,2,3,4,5,31,249],[0,6,7,14,15,26,31,32,33,1168,1243,1244,1248]),([0,1,2,3,4,5,16,59],[0,4,6,8,10,11,24,45,47,68,1164,1165,1168,1169,1170,1171,1172,1250,1251,1252,1253,1254,1255,1256]),([0,1,2,3,4,5,252],[0,1,4,6,7,10,12,13,44,47,50,1168,1171,1257,1258,1259]),([0,2,3,4,5,22,107],[4,7,11,68,90,111,274,282,285,738,855,1263,1264,1265]),([0,1,2,3,4,5,253],[0,1,6,7,8,9,10,11,12,13,111,274,286,855,1266,1267,1268,1269]),([1,2,3,4,5,17,96],[4,9,10,68,111,218,458,1086,1272,1273,1274,1275,1276,1277])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_18 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_18 = true := by decide +kernel
def h0Block8_19 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,254],[0,1,6,7,8,10,12,13,175,458,587,715,1086,1278,1279,1280,1281,1282,1283]),([0,1,2,3,4,5,255],[0,1,6,7,8,10,11,12,13,274,280,288,1286,1287,1288,1289,1290]),([0,1,2,3,4,5,17,255],[0,1,10,274,286,287,288,291,292,1286,1287,1288,1289,1290]),([0,1,2,3,4,5,24,255],[1,8,11,274,1191,1193,1198,1199,1202,1203,1286,1287,1288,1289]),([0,1,2,4,5,25,87],[1,9,11,68,77,111,461,603,636,715,1293,1294,1295,1296]),([0,1,2,3,4,5,256],[0,1,4,6,7,8,10,11,12,13,77,288,458,603,715,1297,1298,1299,1300,1301]),([0,2,3,4,5,26,107],[4,8,11,68,90,274,280,282,285,742,1087,1304,1305,1306,1307,1308]),([0,1,2,3,4,17,245],[1,9,12,157,274,280,291,1086,1219,1221,1222,1224,1225,1226,1303,1313,1314,1315]),([0,1,2,3,4,5,257],[0,1,4,6,7,8,10,11,12,13,274,280,1086,1308,1316,1317,1318,1319,1320]),([0,1,2,3,4,5,31,107],[4,6,7,8,9,11,14,15,26,30,31,32,33,68,111,204,274,277,280,282,285,738,743,744,1087,1321]),([1,2,3,4,5,17,45],[6,9,10,14,68,286,1086,1326,1327,1328,1329,1330,1331]),([0,1,2,3,4,5,261],[0,1,4,6,7,8,10,12,13,30,111,286,1086,1332,1333,1334,1335,1336,1337])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_19 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_19 = true := by decide +kernel
def h0Block8_20 : List NodeSpec := nodesWithIdentity [([0,1,2,4,5,32,87],[7,9,11,49,68,111,175,459,461,746,1296,1339,1340,1341,1342]),([0,1,2,3,4,5,262],[0,1,4,6,7,10,11,12,13,49,111,286,288,1343,1344,1345,1346,1347]),([0,1,2,3,4,5,263],[0,1,6,7,8,9,11,12,13,151,851,855,1353,1358,1359,1360]),([1,2,3,4,5,18,96],[4,9,10,68,111,175,218,1274,1276,1354,1363,1364,1365,1366]),([0,1,2,3,4,5,18,96],[0,10,11,151,218,252,253,1348,1349,1352,1353,1354,1355,1356]),([0,1,2,3,4,5,264],[0,1,4,6,7,8,10,11,12,13,175,580,587,1354,1365,1368,1369,1370,1371,1372]),([0,1,2,3,4,5,265],[0,1,6,7,8,11,12,13,1191,1286,1351,1353,1355,1375,1376,1377]),([0,1,2,3,4,5,266],[0,1,4,6,7,8,11,12,13,47,600,603,1354,1355,1380,1381,1382,1383]),([0,1,2,3,4,18,245],[1,9,12,338,1219,1221,1222,1224,1225,1226,1313,1353,1356,1365,1385,1386,1387]),([0,1,2,3,4,5,267],[0,1,4,6,7,11,12,13,1211,1308,1351,1353,1365,1388,1389,1390,1391]),([0,2,3,4,5,21,154],[0,4,6,11,151,569,930,931,1393,1394,1395]),([0,1,2,3,4,5,31,154],[0,4,6,7,8,9,11,14,15,26,30,32,33,47,90,144,151,163,569,715,1232,1392,1393,1396])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_20 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_20 = true := by decide +kernel
def h0Block8_21 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,18,45],[6,9,10,14,68,90,1328,1329,1352,1365,1398,1399,1400,1401]),([0,1,2,3,4,5,18,45],[0,10,11,14,19,22,25,1348,1349,1352,1353,1354,1356,1398,1400]),([0,1,2,3,4,5,269],[0,1,4,6,7,11,12,13,14,30,90,1352,1365,1404,1405,1406,1407,1408]),([0,1,2,3,4,5,270],[0,1,4,6,7,11,12,13,44,47,49,1352,1355,1410,1411,1412,1413]),([0,1,2,3,4,5,19,195],[0,1,6,9,10,11,68,87,90,111,293,301,302,305,309,310,852,1174,1175,1177,1180,1181,1182,1417,1418,1419]),([0,1,2,3,4,5,271],[0,1,6,7,8,9,10,11,12,13,111,293,301,856,1420,1421,1422,1423]),([0,1,2,3,5,19,23,126],[4,9,10,65,87,303,580,587,588,683,715,1426,1427,1428,1429,1430]),([0,1,2,3,4,5,273],[0,1,6,7,8,11,12,13,87,303,305,588,1431,1432,1433,1434,1435,1436]),([0,1,2,3,4,5,23,273],[1,8,10,65,303,580,581,587,588,591,592,598,715,1431,1432,1433,1434,1435]),([0,1,2,3,4,5,274],[0,1,6,7,8,10,11,12,13,293,300,311,1193,1439,1440,1441,1442]),([0,1,2,3,4,5,19,23],[0,1,4,8,10,11,68,87,293,301,302,303,309,310,580,581,588,591,598,1425]),([0,1,2,3,4,5,275],[0,1,4,6,7,8,10,11,12,13,87,303,311,604,1445,1446,1447,1448,1449])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_21 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_21 = true := by decide +kernel
def h0Block8_22 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,19,245],[1,9,12,157,293,300,305,309,1219,1221,1222,1224,1225,1226,1313,1451,1452,1453]),([0,1,2,3,4,5,276],[0,1,4,6,7,8,10,11,12,13,293,300,305,1213,1454,1455,1456,1457,1458]),([0,1,2,3,4,5,31,109],[4,6,7,8,9,10,14,15,26,30,31,32,33,68,111,293,296,300,381,751,753,755,756,757,1459]),([0,1,2,3,4,5,19,51],[0,4,6,9,10,11,15,24,68,87,111,293,300,301,302,303,305,309,310,1235,1236,1239,1240,1241,1242,1461,1462,1463]),([0,1,2,3,4,5,277],[0,1,4,6,7,8,11,12,13,31,111,301,305,1464,1465,1466,1467,1468,1469]),([0,1,2,3,4,5,19,59],[0,4,6,8,10,11,24,45,68,87,111,293,301,302,303,309,310,311,1250,1251,1253,1254,1255,1256,1471,1472]),([0,1,2,3,4,5,278],[0,1,4,6,7,10,11,12,13,50,111,301,311,1473,1474,1475,1476,1477]),([0,1,2,3,4,5,36,146],[1,6,8,9,10,11,68,77,110,117,119,137,145,147,149,150,151,381,505,666,668,1482,1484]),([0,1,2,3,4,5,37,146],[1,6,8,9,10,11,68,77,100,119,122,125,147,151,171,176,183,184,381,505,1482,1484,1485]),([0,1,2,3,4,5,38,146],[1,6,8,9,10,11,68,77,100,119,127,131,147,151,189,192,193,194,381,505,1482,1484,1486]),([0,1,2,3,4,5,39,146],[1,6,8,9,10,11,68,77,100,119,133,136,147,151,200,205,206,207,381,505,1482,1484,1487]),([0,1,2,3,4,5,279],[0,1,6,7,8,10,11,12,13,68,77,117,137,854,856,1489,1490,1491,1492])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_22 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_22 = true := by decide +kernel
def h0Block8_23 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,280],[0,1,6,7,8,11,12,13,68,171,511,852,855,1494,1495,1496,1497]),([0,1,2,3,4,5,281],[0,1,6,7,8,10,11,12,13,68,77,189,854,855,1499,1500,1501,1502]),([0,1,2,3,4,5,282],[0,1,6,7,8,10,12,13,68,200,381,852,856,1504,1505]),([0,1,2,3,4,5,149],[0,1,6,7,8,9,10,11,12,13,68,90,512,715,1506,1507,1508,1509,1510]),([0,1,2,3,4,5,96,100],[4,9,10,11,68,111,157,175,218,252,253,1511,1512,1513,1514,1515,1516,1517]),([0,1,2,3,4,5,96,101],[4,9,10,11,68,111,157,175,218,252,253,1274,1518,1519,1520,1521,1522,1523,1524]),([0,1,2,3,4,5,23,96,99],[4,111,218,221,252,581,598,1526,1527]),([0,1,2,3,4,5,96,126],[0,4,9,10,11,68,111,157,163,171,175,214,218,252,253,254,683,715,1274,1528,1529,1530,1531,1532,1533]),([0,1,2,3,4,5,96,159],[0,4,9,10,11,68,111,157,175,214,218,252,253,254,587,715,1534,1535,1536,1537,1538,1539,1540]),([0,1,2,3,4,5,23,96,100],[4,175,218,580,587,588,1511,1515]),([0,1,2,3,4,5,96,130],[0,1,4,87,163,218,252,253,400,438,715,1541,1542,1543]),([0,1,2,3,4,5,130,157],[0,4,6,7,9,28,65,87,163,175,400,581,636,715,1541,1542,1543,1544,1545,1546,1547,1548,1549,1550,1551,1552])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_23 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_23 = true := by decide +kernel
def h0Block8_24 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,130,159],[0,4,9,10,65,163,175,400,587,715,1534,1535,1536,1537,1538,1539,1540,1541,1542,1543]),([0,1,2,3,4,5,130,160],[0,4,9,12,13,87,163,400,591,1525,1541,1542,1543,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562]),([0,1,2,3,4,5,283],[0,1,6,7,8,11,12,13,63,68,83,588,598,934,1564,1565,1566,1567]),([0,1,2,3,4,5,23,68],[1,4,6,8,9,11,68,84,87,175,580,581,587,591,592,598,1569,1570,1571,1572,1573,1574,1575]),([0,1,2,3,4,5,284],[0,1,6,7,8,10,12,13,68,88,175,587,598,941,1576,1577,1578,1579,1580]),([0,1,2,3,4,5,23,272],[0,1,4,8,9,10,11,68,87,111,157,580,581,587,588,591,592,598,1583,1584,1585,1586,1587,1588]),([0,1,2,3,4,5,25,61],[1,4,6,8,9,10,56,61,62,68,77,600,601,604,605,606,715,772,1012,1597,1598,1599,1600,1601]),([0,1,2,3,4,5,285],[0,1,4,6,7,8,12,13,63,64,68,77,604,772,1602,1603,1604]),([0,1,2,3,4,5,25,68],[1,4,6,8,9,11,68,77,84,87,600,601,603,605,606,772,1570,1571,1572,1573,1574,1575,1606,1607]),([0,1,2,3,4,5,286],[0,1,4,6,7,8,12,13,68,77,88,89,603,772,1608,1609,1610,1611]),([0,1,2,3,4,5,108,197],[4,8,9,10,68,75,111,157,277,436,864,865,1615,1616,1617,1618,1619,1620,1621]),([0,1,2,3,4,5,108,198],[4,8,9,10,68,75,111,157,277,864,865,974,1622,1623,1624,1625,1626,1627,1628])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_24 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_24 = true := by decide +kernel
def h0Block8_25 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,27,45],[1,4,6,9,10,11,14,19,22,68,610,611,616,624,628,629,715,1328,1329,1630,1631,1632,1633,1634]),([0,1,2,3,4,5,288],[0,1,6,7,8,11,12,13,26,31,68,616,624,1635,1636,1637,1638,1639]),([0,1,2,3,4,5,27,288],[1,6,11,31,610,611,615,624,628,629,715,1635,1636,1637,1638]),([0,1,2,3,4,5,31,288],[6,7,8,10,14,15,30,31,32,33,111,624,1635,1636,1638,1640]),([0,1,2,3,4,5,27,58],[1,4,6,8,10,11,44,47,68,75,610,611,615,624,628,629,1642,1643,1644,1645,1646,1647,1648,1649]),([0,1,2,3,4,5,292],[0,1,6,7,10,11,12,13,48,50,68,615,624,636,1650,1651,1652,1653]),([0,1,2,3,4,5,173],[0,1,4,6,7,8,9,10,12,13,68,631,1654,1655,1656,1657,1658,1659]),([0,1,2,3,4,5,155],[0,1,6,7,8,9,11,12,13,68,111,151,1665,1666]),([0,1,2,3,4,5,29,45],[1,4,6,9,10,11,14,19,22,68,381,642,643,648,659,660,715,791,1328,1329,1631,1633,1634,1671]),([0,1,2,3,4,5,293],[0,1,6,7,8,10,12,13,26,30,68,381,648,791,1672,1673,1674,1675,1676]),([0,1,2,3,4,5,294],[0,1,6,7,10,11,12,13,48,49,68,381,647,791,1678,1679,1680,1681,1682]),([0,1,2,3,4,5,181],[0,1,4,6,7,8,9,11,12,13,68,1683,1684,1685,1686,1687,1688,1689,1690])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_25 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_25 = true := by decide +kernel
def h0Block8_26 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,214],[0,1,6,7,8,9,10,12,13,68,214,221,237,1006,1696,1697]),([0,1,2,3,4,5,45,46],[1,4,6,9,14,19,22,68,175,715,1328,1329,1631,1632,1634,1698,1699,1700,1701,1704]),([0,1,2,3,4,5,45,49],[6,9,10,11,14,19,22,68,715,1328,1329,1631,1634,1703,1705,1706,1707,1708,1709]),([0,1,2,3,4,5,45,50],[6,9,10,11,14,19,22,68,175,715,1328,1329,1631,1634,1710,1711,1712,1713,1714,1715]),([0,1,2,3,4,5,248],[0,1,4,6,7,9,10,11,12,13,68,1235,1716,1717,1718,1719,1720,1721]),([0,1,2,3,4,5,251],[0,1,4,6,7,8,10,11,12,13,68,1250,1723,1724,1725,1726,1727]),([0,1,2,3,4,5,61,62],[1,4,6,10,56,61,62,65,68,436,715,750,1012,1598,1599,1601,1728,1729,1730,1731,1732]),([0,1,2,3,4,5,295],[0,1,4,6,7,8,9,10,12,13,68,1735,1736,1737,1738,1739,1740]),([0,1,2,3,4,5,65],[0,1,4,6,7,8,9,10,12,13,66,68,1741,1742,1743,1744,1745,1746]),([0,1,2,3,4,5,207],[0,1,4,6,7,8,9,11,12,13,68,942,1747,1748,1749,1750,1751,1752]),([0,1,2,3,4,5,71],[0,1,4,6,7,8,9,11,12,13,68,91,1753,1754,1755,1756,1757,1758,1759]),([0,1,2,3,4,5,74,84],[1,4,9,10,68,110,111,141,142,318,715,1760,1761,1762,1763,1764,1765,1766,1767,1768])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_26 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_26 = true := by decide +kernel
def h0Block8_27 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,74,86],[1,4,9,10,68,77,110,111,141,142,318,322,1764,1768,1769,1770,1771,1772,1773,1774,1775]),([0,1,2,3,4,5,112],[0,1,4,6,7,9,10,12,13,68,324,1777,1778,1779,1780,1781,1782]),([0,1,2,3,4,5,118],[0,1,4,6,7,8,11,12,13,68,216,240,272,360,1786,1787,1788]),([0,1,2,3,4,5,120],[0,1,4,6,7,9,11,12,13,68,77,111,240,259,314,370,1793,1794,1795]),([0,1,2,3,4,5,122],[0,1,4,6,7,8,10,12,13,68,216,239,272,385,1798,1799,1800])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_27 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_27 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1 ++ h0Block8_2 ++ h0Block8_3 ++ h0Block8_4 ++ h0Block8_5 ++ h0Block8_6 ++ h0Block8_7 ++ h0Block8_8 ++ h0Block8_9 ++ h0Block8_10 ++ h0Block8_11 ++ h0Block8_12 ++ h0Block8_13 ++ h0Block8_14 ++ h0Block8_15 ++ h0Block8_16 ++ h0Block8_17 ++ h0Block8_18 ++ h0Block8_19 ++ h0Block8_20 ++ h0Block8_21 ++ h0Block8_22 ++ h0Block8_23 ++ h0Block8_24 ++ h0Block8_25 ++ h0Block8_26 ++ h0Block8_27
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Nodes8 = true := by
  unfold h0Nodes8 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0Test8_0,h0Test8_1⟩,h0Test8_2⟩,h0Test8_3⟩,h0Test8_4⟩,h0Test8_5⟩,h0Test8_6⟩,h0Test8_7⟩,h0Test8_8⟩,h0Test8_9⟩,h0Test8_10⟩,h0Test8_11⟩,h0Test8_12⟩,h0Test8_13⟩,h0Test8_14⟩,h0Test8_15⟩,h0Test8_16⟩,h0Test8_17⟩,h0Test8_18⟩,h0Test8_19⟩,h0Test8_20⟩,h0Test8_21⟩,h0Test8_22⟩,h0Test8_23⟩,h0Test8_24⟩,h0Test8_25⟩,h0Test8_26⟩,h0Test8_27⟩
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket7Ok h0Check8
def h0Block9_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,9],[0,4,5,6,7,8,9,10,11,12,13]),([0,1,2,3,4,5,6,31],[0,1,2,3,4,6,7,8,9,14,15,16,18,20,21,23,26,27,28,29,30,31,32,33]),([0,1,2,3,4,5,6,32],[0,1,2,3,4,6,7,8,9,18,20,21,23,27,28,44,45,46,47,48,49,50,51,52]),([0,1,2,3,4,5,6,33],[0,1,2,3,4,6,7,10,11,18,20,23,27,28,56,57,58,63,64,65,78,79,83]),([0,1,2,3,4,5,6,34],[0,1,2,3,4,6,7,10,11,18,20,21,23,27,28,84,85,86,87,88,89,90,101,102]),([0,1,3,4,5,47],[0,2,4,6,107,108]),([0,1,2,3,4,5,6,36],[0,1,2,3,4,8,9,10,11,18,20,21,23,27,29,110,114,117,137,138,139,145,149,150]),([0,1,2,3,4,5,6,37],[0,1,2,3,4,8,9,10,11,18,20,21,23,27,47,122,125,171,172,173,174,175,176,183,184]),([0,1,2,3,4,5,6,38],[0,1,2,3,4,8,9,10,11,18,20,21,23,27,29,87,127,129,131,175,189,190,191,192,193,194]),([0,1,2,3,4,5,6,39],[0,1,2,3,4,8,9,10,11,18,20,23,27,47,133,136,200,201,202,203,204,205,206,207]),([0,1,2,3,4,5,48],[0,1,4,6,7,9,10,11,12,13,27,65,90,182,211,212]),([0,1,2,3,4,5,7,13],[0,1,4,8,9,68,213,214,215,216,217,221,229,230,231,237,238,239,240,246,249,250,251])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,7,15],[0,1,4,8,9,68,213,216,231,239,240,250,251,255,256,257,259,263,264,265,266,267,271,273]),([0,1,2,3,4,5,7,17],[0,1,4,10,11,68,77,90,213,216,231,239,240,250,251,274,275,276,280,286,287,288,291,292]),([0,1,2,3,4,5,7,19],[0,1,4,10,11,68,77,213,216,231,239,250,251,293,294,295,300,301,302,309,310,311]),([0,1,2,3,4,5,7,36],[0,1,4,8,9,10,11,68,77,110,117,137,145,149,150,213,216,231,239,240,250,251,259,315,316,317]),([0,1,2,3,4,5,7,37],[0,1,4,8,9,10,11,68,122,125,171,175,176,183,184,213,216,231,239,240,250,251,354,355,356]),([0,1,2,3,4,5,7,38],[0,1,4,8,9,10,11,68,77,127,131,175,189,192,193,194,213,216,231,239,240,250,251,259,364,365,366]),([0,1,2,3,4,5,7,39],[0,1,4,8,9,10,11,68,133,136,200,204,205,206,207,213,216,231,239,250,251,375,376,377,381]),([0,1,2,3,4,5,97],[0,1,4,6,7,9,10,11,12,13,28,90,216,232,306,307]),([0,1,2,3,4,98],[1,12,28,241,245,251]),([0,1,2,3,4,5,8,36],[0,1,4,8,9,10,11,77,110,117,137,145,149,150,388,389,390,391,394,396,398,399,400,401]),([0,1,2,3,4,5,8,37],[0,1,4,8,9,10,11,47,122,125,171,176,183,184,388,389,396,398,399,400,401,410,411]),([0,1,2,3,4,5,8,38],[0,1,4,8,9,10,11,87,127,131,189,192,193,194,388,389,394,396,398,399,400,401,421,422])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Block9_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,8,39],[0,1,4,8,9,10,11,47,133,136,200,205,206,207,388,389,396,398,400,401,427,428]),([0,1,2,3,4,5,123],[0,1,6,7,9,10,11,12,13,28,400,431,432]),([0,1,2,3,4,5,9,11],[0,1,4,5,6,7,68,144,146,147,148,433,434,435,436,437,438,439,440,441,442,443,444]),([0,1,2,3,4,5,9,13],[0,1,4,5,8,9,68,111,144,146,147,148,214,229,230,237,238,246,249,441,444,445,446,447]),([0,1,2,3,4,5,9,15],[0,1,4,5,8,9,68,111,144,146,147,148,255,264,265,266,267,271,273,441,444,452,453,454,455]),([0,1,2,3,4,5,9,17],[0,1,4,5,10,11,68,90,111,144,146,147,148,274,286,287,288,291,292,441,444,456,457,458]),([0,1,2,3,4,5,9,19],[0,1,4,5,10,11,68,111,144,146,147,148,293,301,302,303,309,310,311,441,444,464,465]),([0,1,2,3,4,5,9,31],[0,1,4,5,6,7,8,9,14,15,26,30,31,32,33,68,111,144,146,147,148,151,441,444,455,480]),([0,1,2,3,4,5,9,32],[0,1,4,5,6,7,8,9,44,45,48,49,50,51,52,68,111,144,146,147,148,151,441,444,486]),([0,1,2,3,4,5,9,33],[0,1,4,5,6,7,10,11,56,57,63,64,65,68,78,79,111,144,146,147,148,151,444,491]),([0,1,2,3,4,5,9,34],[0,1,4,5,6,7,10,11,68,84,85,88,89,90,101,102,111,144,146,147,148,151,441,444,497]),([0,1,2,3,4,5,9,35],[0,1,4,5,6,7,68,144,146,147,148,151,175,204,441,444,505,506,507])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
def h0Block9_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,9,36],[0,1,4,5,8,9,10,11,68,110,114,117,137,143,144,145,146,147,148,149,150,151,436,441,444,455,508]),([0,1,2,3,4,5,9,37],[0,1,4,5,8,9,10,11,68,122,125,144,146,147,148,151,171,174,175,176,183,184,441,444,533,534]),([0,1,2,3,4,5,9,38],[0,1,4,5,8,9,10,11,68,127,129,131,144,146,147,148,151,175,189,192,193,194,436,441,444,455,540,541]),([0,1,2,3,4,5,9,39],[0,1,4,5,8,9,10,11,68,90,133,136,144,146,147,148,151,200,203,204,205,206,207,444,548,549]),([0,1,2,3,4,5,40],[4,6,7,9,10,11,12,13,68,111,148,554,555,556,557]),([0,1,2,3,4,5,9,41],[0,1,4,5,8,9,68,111,144,146,147,148,151,441,444,558,559,560,561]),([0,1,2,3,4,5,42],[0,1,4,6,7,9,10,11,12,13,65,90,148,438,448,467,469,470]),([0,1,2,3,4,5,9,42],[0,1,4,5,8,68,111,144,146,147,148,151,441,444,448,455,467,469,470]),([0,1,2,3,4,5,9,43],[0,1,4,5,10,11,68,111,144,146,147,148,151,441,444,568,569,570,571]),([0,1,2,3,4,5,9,44],[0,1,4,5,10,11,68,111,144,146,147,148,151,175,441,444,575,576,577,578]),([0,1,2,3,4,5,10,23],[0,1,4,6,7,8,9,65,111,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593]),([0,1,2,3,4,5,10,25],[0,1,4,6,7,8,9,28,47,111,579,583,584,585,589,590,593,600,601,602,603,604,605,606])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
def h0Block9_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,10,27],[0,1,4,6,7,10,11,111,579,583,584,585,589,590,593,610,611,612,615,628,629]),([0,1,2,3,4,5,10,29],[0,1,4,6,7,10,11,87,90,111,579,583,584,585,589,590,593,642,643,644,647,659,660]),([0,1,2,3,4,5,147],[0,4,6,7,8,9,10,11,12,13,28,147,175,204,506,665,669]),([0,1,2,3,4,5,10,36],[0,6,7,8,9,10,11,110,111,119,137,145,149,150,579,583,584,586,589,590,593,670]),([0,1,2,3,4,5,10,37],[0,6,7,8,9,10,11,47,111,122,125,171,175,176,183,184,579,583,584,589,590,593,680]),([0,1,2,3,4,5,10,38],[0,6,7,8,9,10,11,87,111,127,175,189,192,193,194,579,583,584,586,589,590,593,691]),([0,1,2,3,4,5,10,39],[0,6,7,8,9,10,11,47,111,133,200,204,205,206,207,579,583,584,589,593,703]),([0,1,2,3,4,5,158],[0,1,4,6,7,9,10,11,12,13,90,584,623,626,713]),([0,1,2,3,4,5,11,13],[0,6,7,8,9,204,214,221,229,230,237,238,246,249,433,437,439,440,442,443,714,715]),([0,1,2,3,4,5,11,15],[0,6,7,8,9,68,255,263,264,265,266,267,271,273,433,437,439,440,442,443,715,726,727]),([0,1,2,3,4,5,11,17],[0,6,7,10,11,90,175,274,280,286,287,288,291,292,433,437,439,440,442,443,715,737]),([0,1,2,3,4,5,11,19],[0,6,7,10,11,68,293,300,301,302,309,310,311,433,437,439,442,443,715,747])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
def h0Block9_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,11,23],[0,1,4,6,7,8,9,25,65,68,433,435,437,439,440,442,443,580,581,587,588,591,592,598,715,727,765]),([0,1,2,3,4,5,11,25],[0,1,4,6,7,8,9,25,28,68,77,433,435,437,439,440,442,443,600,601,603,604,605,606,715,771,772]),([0,1,2,3,4,5,11,27],[0,1,4,6,7,10,11,25,68,433,435,437,439,440,442,443,610,611,615,624,628,629,715,777]),([0,1,2,3,4,5,11,29],[0,1,4,6,7,10,11,25,68,90,381,433,435,437,439,440,442,443,642,643,647,659,660,715,790,791]),([0,1,2,3,4,5,73],[0,2,4,6,7,8,9,10,11,12,13,28,108,119,175,204,728,731,733]),([0,1,2,3,4,5,11,36],[0,6,7,8,9,10,11,25,68,110,117,119,137,145,149,150,316,433,436,437,439,440,442,443,727,800]),([0,1,2,3,4,5,11,37],[0,6,7,8,9,10,11,25,68,100,122,125,171,175,176,183,184,355,433,437,439,440,442,443,809]),([0,1,2,3,4,5,11,38],[0,6,7,8,9,10,11,25,68,75,127,131,175,189,192,193,194,365,433,436,437,439,440,442,443,727,818]),([0,1,2,3,4,5,11,39],[0,6,7,8,9,10,11,25,68,90,133,136,200,204,205,206,207,376,433,437,439,442,443,826]),([0,1,2,3,4,5,131],[0,1,4,6,7,9,10,11,12,13,90,437,438,722,761,762,833]),([0,1,2,3,4,5,12,20],[0,1,4,6,7,8,9,28,111,119,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850]),([0,1,2,3,4,5,12,22],[0,1,4,6,7,8,9,111,119,151,834,835,841,846,847,850,851,852,853,854,855,856,857,858])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
def h0Block9_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,12,27],[0,1,4,8,9,10,11,610,611,615,616,624,628,629,834,835,840,841,842,846,847,850,862,863]),([0,1,2,3,4,5,12,28],[0,1,4,8,9,10,11,77,151,834,835,840,841,846,847,850,883,884,885,886,887,893,894,895,899]),([0,1,2,3,4,5,12,29],[0,1,4,8,9,10,11,87,90,642,643,647,648,659,660,791,834,835,840,841,842,846,847,850,904,905]),([0,1,2,3,4,5,12,30],[0,1,4,8,9,10,11,77,151,834,835,840,841,847,850,914,915,916,917,918,919,920,921,925]),([0,1,2,3,4,5,137],[0,1,4,6,7,9,10,11,12,13,148,175,467,669,889,929]),([0,1,2,3,4,5,12,33],[0,6,7,8,9,10,11,56,57,64,65,78,79,83,111,119,834,835,840,841,847,850,934,935]),([0,1,2,3,4,5,12,34],[0,6,7,8,9,10,11,84,85,87,89,101,102,111,119,175,834,835,840,841,846,847,850,940,941]),([0,1,2,3,4,5,15],[0,1,4,6,7,10,11,12,13,273]),([0,1,2,3,4,194],[0,9,12,119,835,875,876]),([0,1,2,3,4,5,13,17],[0,8,9,10,11,68,111,175,204,214,229,230,237,238,246,249,274,286,287,288,291,292,956,957]),([0,1,2,3,4,5,13,19],[0,8,9,10,11,68,111,204,214,229,230,237,246,249,293,301,302,309,310,311,959,960]),([0,1,2,3,4,5,13,20],[0,1,4,6,7,8,9,28,111,214,221,229,230,237,238,246,249,447,836,837,844,845,848,849,964])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_6 = true := by decide +kernel
def h0Block9_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,13,22],[0,1,4,6,7,8,9,68,111,214,229,230,237,238,246,249,851,852,855,856,857,858,965]),([0,1,2,3,4,5,13,27],[0,1,4,8,9,10,11,68,75,214,229,230,237,238,246,249,447,610,611,615,624,628,629,715,971,972]),([0,1,2,3,4,5,13,28],[0,1,4,8,9,10,11,68,77,214,221,229,230,237,238,246,249,883,885,893,894,895,899,988,989]),([0,1,2,3,4,5,13,29],[0,1,4,8,9,10,11,68,90,204,214,229,230,237,238,246,249,381,447,642,643,647,659,660,715,791,994,995]),([0,1,2,3,4,5,13,30],[0,1,4,8,9,10,11,68,75,77,175,214,221,229,230,237,246,249,914,916,919,920,921,925,1001,1002]),([0,1,2,3,4,5,95],[0,1,4,6,7,8,10,11,12,13,175,214,218,716,721]),([0,1,2,3,4,5,13,33],[0,6,7,8,9,10,11,56,57,64,68,78,79,111,204,214,221,229,230,237,246,249,1010]),([0,1,2,3,4,5,13,34],[0,6,7,8,9,10,11,68,84,85,89,101,102,111,175,204,214,221,229,230,237,238,246,249,1019]),([0,1,2,3,4,5,14,20],[0,1,4,6,7,8,9,28,836,837,844,845,848,849,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034]),([0,1,2,3,4,5,14,22],[0,1,4,6,7,8,9,151,851,852,855,856,857,858,1025,1026,1030,1032,1033,1034,1035]),([0,1,2,3,4,5,14,27],[0,1,4,8,9,10,11,75,610,611,615,624,628,629,1025,1026,1029,1030,1031,1032,1033,1034,1038,1039]),([0,1,2,3,4,5,14,28],[0,1,4,8,9,10,11,151,883,885,893,894,895,899,1025,1026,1029,1030,1032,1033,1034,1047,1048])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_7 = true := by decide +kernel
def h0Block9_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,14,29],[0,1,4,8,9,10,11,87,642,643,647,659,660,791,1025,1026,1029,1030,1031,1032,1033,1034,1058,1059]),([0,1,2,3,4,5,14,30],[0,1,4,8,9,10,11,151,914,916,919,920,921,925,1025,1026,1029,1030,1033,1034,1064,1065]),([0,1,2,3,4,5,153],[0,1,4,6,7,8,10,11,12,13,175,559,669,1068,1070]),([0,1,2,3,4,5,14,33],[0,6,7,8,9,10,11,56,57,64,75,78,79,83,204,1025,1026,1029,1030,1033,1034,1071]),([0,1,2,3,4,5,14,34],[0,6,7,8,9,10,11,84,85,87,89,101,102,175,204,1025,1026,1029,1030,1032,1033,1034,1079]),([0,1,2,3,4,5,15,17],[0,8,9,10,11,68,111,175,255,264,265,266,267,271,273,274,286,287,288,291,292,1084,1085,1086]),([0,1,2,3,4,5,15,19],[0,8,9,10,11,68,111,255,264,265,266,267,271,273,293,301,302,305,309,310,311,1089,1090]),([0,1,2,3,4,5,15,20],[0,1,4,6,7,8,9,28,111,255,263,264,265,266,267,271,273,454,836,837,843,844,845,848,849,1092]),([0,1,2,3,4,5,15,22],[0,1,4,6,7,8,9,68,111,255,264,265,266,267,271,273,851,852,854,855,856,857,858,1093]),([0,1,2,3,4,5,15,27],[0,1,4,8,9,10,11,47,68,255,264,265,266,267,271,273,454,610,611,615,616,624,628,629,654,715,866,1098]),([0,1,2,3,4,5,15,28],[0,1,4,8,9,10,11,47,68,77,255,263,264,265,266,267,271,273,883,885,887,893,894,895,899,1110,1111]),([0,1,2,3,4,5,15,29],[0,1,4,8,9,10,11,47,68,90,255,264,265,266,267,271,273,381,454,642,643,647,648,659,660,715,791,1117,1118])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_8 = true := by decide +kernel
def h0Block9_9 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,15,30],[0,1,4,8,9,10,11,47,68,77,255,263,264,265,266,271,273,914,916,918,919,920,921,925,1125,1126]),([0,1,2,3,4,5,15,102],[0,1,4,8,9,47,68,255,263,264,265,266,267,271,273,1131,1132,1133,1134]),([0,1,2,3,4,5,91],[0,1,4,6,7,8,9,10,11,12,13,27,163,175,212,258,261,262,736]),([0,1,2,3,4,5,15,91],[0,1,4,8,9,27,47,68,111,157,212,255,258,261,262,263,264,265,266,267,271,273,454,736]),([0,1,2,3,4,5,15,33],[0,6,7,8,9,10,11,56,57,64,65,68,78,79,111,255,263,264,265,266,271,273,934,1135]),([0,1,2,3,4,5,15,34],[0,6,7,8,9,10,11,68,84,85,89,101,102,111,175,255,263,264,265,266,267,271,273,941,1141]),([0,1,2,3,4,5,15,104],[0,6,7,9,47,68,90,255,263,264,265,266,267,271,273,636,654,1150,1151,1152]),([0,1,2,3,4,5,15,105],[0,8,9,10,11,47,68,111,255,264,265,266,267,271,273,1153,1154,1155,1156]),([0,1,2,3,4,5,15,106],[0,8,9,10,11,47,68,90,111,255,264,265,266,267,271,273,1160,1161,1162,1163]),([0,1,2,3,4,5,16,20],[0,1,4,6,7,10,11,28,654,836,837,845,848,849,1164,1165,1166,1167,1168,1169,1170,1171,1172]),([0,1,2,3,4,5,16,22],[0,1,4,6,7,10,11,77,151,851,852,856,857,858,1164,1165,1169,1171,1172,1173]),([0,1,2,3,4,5,16,23],[0,1,4,8,9,10,11,65,580,581,588,591,592,598,1164,1165,1168,1169,1170,1171,1172,1176,1185,1186])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_9 = true := by decide +kernel
def h0Block9_10 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,16,24],[0,1,4,8,9,10,11,151,1164,1165,1168,1169,1171,1172,1191,1192,1193,1194,1198,1199,1202,1203]),([0,1,2,3,4,5,16,25],[0,1,4,8,9,10,11,47,600,601,604,605,606,772,1164,1165,1168,1169,1170,1171,1172,1206,1207]),([0,1,2,3,4,5,16,26],[0,1,4,8,9,10,11,151,1164,1165,1168,1169,1171,1172,1176,1211,1212,1213,1214,1215,1216,1217,1218]),([0,1,2,3,4,5,156],[0,1,4,6,7,8,9,10,12,13,204,576,669,1195,1230]),([0,1,2,3,4,5,16,31],[0,6,7,8,9,10,11,14,15,31,32,33,1164,1165,1168,1169,1171,1172,1176,1233]),([0,1,2,3,4,5,16,32],[0,6,7,8,9,10,11,44,45,47,50,51,52,204,1164,1165,1168,1169,1171,1172,1249]),([0,1,2,3,4,5,234],[0,1,4,6,7,8,9,10,12,13,77,636,654,669,1162,1260]),([0,1,2,3,4,5,17,20],[0,1,4,6,7,10,11,28,111,274,280,286,287,288,291,292,458,654,836,837,844,845,848,849,1261]),([0,1,2,3,4,5,17,22],[0,1,4,6,7,10,11,68,77,90,111,274,286,287,288,291,292,851,852,855,856,857,858,1262]),([0,1,2,3,4,5,17,23],[0,1,4,8,9,10,11,68,175,274,286,287,288,291,292,458,580,581,587,588,591,592,598,715,1086,1270,1271]),([0,1,2,3,4,5,17,24],[0,1,4,8,9,10,11,68,274,280,286,287,288,291,292,1191,1193,1198,1199,1202,1203,1284,1285,1286]),([0,1,2,3,4,5,17,25],[0,1,4,8,9,10,11,68,77,175,274,286,287,288,291,292,458,600,601,603,604,605,606,715,772,1291,1292])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_10 = true := by decide +kernel
def h0Block9_11 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,17,26],[0,1,4,8,9,10,11,68,90,175,274,280,286,287,288,291,292,1086,1211,1213,1215,1216,1217,1218,1302,1303,1308]),([0,1,2,3,4,5,107],[0,1,4,6,7,8,9,10,11,12,13,204,274,277,738,743,744]),([0,1,2,3,4,5,17,31],[0,6,7,8,9,10,11,14,15,30,31,32,33,68,111,175,274,280,286,287,288,291,292,1086,1325]),([0,1,2,3,4,5,17,32],[0,6,7,8,9,10,11,44,45,49,50,51,52,68,111,175,204,274,280,286,287,288,291,292,1338]),([0,1,2,3,4,5,87],[0,1,4,6,7,8,9,10,11,12,13,77,110,460,461,462,463,636,654,1159]),([0,1,2,3,4,5,18,20],[0,1,4,6,7,10,11,28,654,836,837,844,845,848,849,1348,1349,1350,1351,1352,1353,1354,1355,1356]),([0,1,2,3,4,5,18,22],[0,1,4,6,7,10,11,77,90,151,851,852,855,856,857,858,1348,1349,1353,1355,1356,1357]),([0,1,2,3,4,5,18,23],[0,1,4,8,9,10,11,175,580,581,587,588,591,592,598,1348,1349,1352,1353,1354,1355,1356,1361,1362,1365]),([0,1,2,3,4,5,18,24],[0,1,4,8,9,10,11,151,1191,1193,1198,1199,1202,1203,1286,1348,1349,1352,1353,1355,1356,1373,1374]),([0,1,2,3,4,5,18,25],[0,1,4,8,9,10,11,47,175,600,601,603,604,605,606,772,1348,1349,1352,1353,1354,1355,1356,1378,1379]),([0,1,2,3,4,5,18,26],[0,1,4,8,9,10,11,151,175,1211,1213,1215,1216,1217,1218,1308,1348,1349,1352,1353,1355,1356,1365,1384,1385]),([0,1,2,3,4,5,154],[0,1,4,6,7,8,9,11,12,13,144,204,569,669,1392,1396])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_11 = true := by decide +kernel
def h0Block9_12 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,18,31],[0,6,7,8,9,10,11,14,15,30,31,32,33,90,175,1348,1349,1352,1353,1355,1356,1365,1397]),([0,1,2,3,4,5,18,32],[0,6,7,8,9,10,11,44,45,47,49,50,51,52,175,204,1348,1349,1352,1353,1355,1356,1409]),([0,1,2,3,4,5,233],[0,1,4,6,7,8,9,11,12,13,77,266,636,654,669,1155,1414]),([0,1,2,3,4,5,19,20],[0,1,4,6,7,10,11,28,111,293,300,301,302,303,309,310,311,654,836,837,844,845,848,849,1415]),([0,1,2,3,4,5,19,22],[0,1,4,6,7,10,11,68,77,111,293,301,302,309,310,311,851,852,855,856,857,858,1416]),([0,1,2,3,4,5,19,23],[0,1,4,8,9,10,11,65,68,87,293,301,302,303,305,309,310,311,580,581,587,588,591,592,598,715,1424,1425]),([0,1,2,3,4,5,19,24],[0,1,4,8,9,10,11,68,87,293,300,301,302,309,310,311,381,1191,1193,1198,1199,1202,1203,1286,1437,1438]),([0,1,2,3,4,5,19,25],[0,1,4,8,9,10,11,68,77,87,293,301,302,303,309,310,311,600,601,603,604,605,606,715,772,1443,1444]),([0,1,2,3,4,5,19,26],[0,1,4,8,9,10,11,68,87,293,300,301,302,305,309,310,311,381,1211,1213,1215,1216,1217,1218,1308,1450,1451]),([0,1,2,3,4,5,109],[0,1,4,6,7,8,9,10,11,12,13,204,293,296,751,755,756]),([0,1,2,3,4,5,19,31],[0,6,7,8,9,10,11,14,15,30,31,32,33,68,111,293,300,301,302,305,309,310,311,1460]),([0,1,2,3,4,5,19,32],[0,6,7,8,9,10,11,44,45,49,50,51,52,68,111,204,293,300,301,302,309,310,311,1470])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_12 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_12 = true := by decide +kernel
def h0Block9_13 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,111],[0,1,4,6,7,8,9,10,11,12,13,77,311,473,476,477,479,654]),([0,1,2,3,4,5,20,36],[1,4,6,7,8,9,10,11,28,110,111,114,117,119,137,145,149,150,316,836,837,843,844,845,848,849,1478]),([0,1,2,3,4,5,20,37],[1,4,6,7,8,9,10,11,28,111,122,125,171,174,176,183,184,355,836,837,844,845,848,849,1479]),([0,1,2,3,4,5,20,38],[1,4,6,7,8,9,10,11,28,111,127,129,131,189,192,193,194,365,836,837,843,844,845,848,849,1480]),([0,1,2,3,4,5,20,39],[1,4,6,7,8,9,10,11,28,111,133,136,200,203,205,206,207,376,836,837,845,848,849,1481]),([0,1,2,3,4,5,146],[0,1,6,7,8,9,10,11,12,13,68,119,147,151,505,1482,1483]),([0,1,2,3,4,5,22,36],[1,4,6,7,8,9,10,11,77,110,111,117,119,137,145,149,150,851,852,854,855,856,857,858,1488]),([0,1,2,3,4,5,22,37],[1,4,6,7,8,9,10,11,100,111,122,125,171,176,183,184,851,852,855,856,857,858,1493]),([0,1,2,3,4,5,22,38],[1,4,6,7,8,9,10,11,77,111,127,131,189,192,193,194,851,852,854,855,856,857,858,1498]),([0,1,2,3,4,5,22,39],[1,4,6,7,8,9,10,11,111,133,136,200,205,206,207,381,851,852,856,857,858,1503]),([0,1,2,3,4,5,195],[0,1,6,7,9,10,11,12,13,90,852,1180,1181]),([0,1,2,3,4,5,96],[0,1,4,6,7,8,9,10,11,12,13,68,111,157,214,218,221,253,254,1276])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_13 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_13 = true := by decide +kernel
def h0Block9_14 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,23,96],[0,1,4,8,9,65,111,157,163,175,214,218,221,253,254,580,581,587,588,591,592,598,715,1525]),([0,1,2,3,4,5,23,130],[0,1,4,8,9,65,87,175,400,580,581,587,588,591,592,598,1525,1541,1543,1544]),([0,1,2,3,4,5,23,33],[1,4,6,7,8,9,10,11,56,57,63,64,65,78,79,83,111,580,581,588,591,592,598,934,1563]),([0,1,2,3,4,5,23,34],[1,4,6,7,8,9,10,11,84,85,88,89,101,102,111,175,580,581,587,588,591,592,598,941,1568]),([0,1,2,3,4,5,23,157],[1,4,6,7,9,65,111,175,580,581,587,588,591,592,598,636,1546,1547,1551]),([0,1,2,3,4,5,23,126],[1,4,8,9,10,11,65,87,171,355,580,581,587,588,591,592,598,683,1430,1530,1533,1581,1582]),([0,1,2,3,4,5,23,159],[1,4,8,9,10,11,65,175,580,581,587,588,591,592,598,1534,1535,1538,1540]),([0,1,2,3,4,5,139],[0,1,6,7,8,10,11,12,13,28,68,151,1561,1589,1590,1591]),([0,1,2,3,5,241],[1,8,10,28,1592,1593]),([0,1,2,3,5,242],[1,8,11,28,1594,1595]),([0,1,2,3,4,5,103],[0,1,4,6,7,8,10,11,12,13,47,68,111,212,258,261,262,1561]),([0,1,2,3,4,5,23],[0,1,4,6,7,10,11,12,13,591])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_14 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_14 = true := by decide +kernel
def h0Block9_15 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,25,33],[1,4,6,7,8,9,10,11,28,56,57,63,64,77,78,79,83,111,600,601,604,605,606,772,1596]),([0,1,2,3,4,5,25,34],[1,4,6,7,8,9,10,11,28,77,84,85,88,89,101,102,111,175,600,601,603,604,605,606,772,1605]),([0,1,2,3,4,5,136],[0,1,4,6,7,9,10,11,12,13,28,68,148,151,157,448,1612,1613]),([0,1,2,3,4,245],[1,9,12,28,1217,1224,1226]),([0,1,2,3,4,5,108],[0,1,4,6,7,8,9,10,11,12,13,68,111,157,274,277,280,865,977,1614]),([0,1,2,3,4,5,27,31],[1,4,6,7,8,9,10,11,14,15,26,30,31,32,33,111,610,611,615,616,624,628,629,1629]),([0,1,2,3,4,5,27,32],[1,4,6,7,8,9,10,11,44,45,48,49,50,51,52,75,111,610,611,615,624,628,629,636,1641]),([0,1,2,3,5,27,38],[1,8,10,11,129,189,613,615,616,617]),([0,1,2,3,4,5,165],[0,1,4,6,7,8,9,10,11,12,13,615,630,632,633,634]),([0,1,2,3,4,5,141],[0,1,6,7,8,9,11,12,13,28,68,144,151,1159,1660,1661,1662]),([0,1,2,3,4,5,201],[0,1,6,7,8,9,11,12,13,28,885,1054,1663,1664]),([0,1,2,3,4,5,110],[0,1,4,6,7,8,9,10,11,12,13,68,87,111,293,296,300,1159,1667,1668,1669])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_15 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_15 = true := by decide +kernel
def h0Block9_16 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,29,31],[1,4,6,7,8,9,10,11,14,15,26,30,31,32,33,90,111,381,642,643,647,648,659,660,791,1670]),([0,1,2,3,4,5,29,32],[1,4,6,7,8,9,10,11,44,45,48,49,50,51,52,65,111,381,636,642,643,647,659,660,791,1677]),([0,1,2,3,5,29,36],[1,8,10,11,114,137,645,647,648,649]),([0,1,2,3,4,5,113],[0,1,4,6,7,8,9,10,11,12,13,137,316,656,657,658,1159]),([0,1,2,3,4,5,140],[0,1,6,7,8,9,10,12,13,28,68,151,157,1691,1692,1693]),([0,1,2,3,4,5,204],[0,1,6,7,8,9,10,12,13,28,916,1694,1695]),([0,1,2,3,4,5,45],[0,1,4,6,7,9,10,11,12,13,14,19,22,68,1632,1633]),([0,1,2,3,4,5,51],[0,1,4,6,7,9,10,11,12,13,15,28,175,1239,1240,1241]),([0,1,2,3,4,5,58],[0,1,4,6,7,8,10,11,12,13,44,47,65,68,1646,1648,1722]),([0,1,2,3,4,5,59],[0,1,4,6,7,8,10,11,12,13,28,45,175,1253,1255]),([0,1,2,3,4,5,61],[0,1,4,6,7,8,9,10,12,13,56,61,62,65,68,1599]),([0,1,2,3,4,5,63],[0,1,4,6,7,8,9,10,12,13,28,57,65,204,1733,1734])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_16 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_16 = true := by decide +kernel
def h0Block9_17 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,64],[0,1,4,6,7,8,9,10,12,13,64,69,71,73]),([0,1,2,3,4,5,68],[0,1,4,6,7,8,9,11,12,13,68,84,87,1572,1573,1575,1607]),([0,1,2,3,4,5,69],[0,1,4,6,7,8,9,11,12,13,28,85,204,947,948,949]),([0,1,2,3,4,5,70],[0,1,4,6,7,8,9,11,12,13,89,93,95,96,97]),([0,1,2,3,4,5,74],[0,1,4,6,7,8,9,10,11,12,13,68,110,111,141,142,461,1776]),([0,1,2,3,4,5,75],[0,1,4,6,7,8,9,10,11,12,13,137,328,656,671,672]),([0,1,2,3,4,76],[9,10,12,119,150,158,160,162]),([0,1,2,3,4,5,78],[0,1,4,6,7,8,11,12,13,47,68,111,122,1783,1784,1785]),([0,1,2,3,4,5,79],[0,1,4,6,7,8,11,12,13,171,416,683,684]),([0,1,2,3,4,5,80],[0,1,4,6,7,8,9,10,11,12,13,68,87,111,127,1789,1790,1791,1792]),([0,1,2,3,4,5,81],[0,1,4,6,7,8,9,10,11,12,13,189,692,694,695,696]),([0,1,2,3,4,5,82],[0,1,4,6,7,8,10,12,13,47,68,111,133,1796,1797])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_17 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_17 = true := by decide +kernel
def h0Block9_18 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,83],[0,1,4,6,7,8,10,12,13,200,704,708])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_18 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_18 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1 ++ h0Block9_2 ++ h0Block9_3 ++ h0Block9_4 ++ h0Block9_5 ++ h0Block9_6 ++ h0Block9_7 ++ h0Block9_8 ++ h0Block9_9 ++ h0Block9_10 ++ h0Block9_11 ++ h0Block9_12 ++ h0Block9_13 ++ h0Block9_14 ++ h0Block9_15 ++ h0Block9_16 ++ h0Block9_17 ++ h0Block9_18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := by
  unfold h0Nodes9 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0Test9_0,h0Test9_1⟩,h0Test9_2⟩,h0Test9_3⟩,h0Test9_4⟩,h0Test9_5⟩,h0Test9_6⟩,h0Test9_7⟩,h0Test9_8⟩,h0Test9_9⟩,h0Test9_10⟩,h0Test9_11⟩,h0Test9_12⟩,h0Test9_13⟩,h0Test9_14⟩,h0Test9_15⟩,h0Test9_16⟩,h0Test9_17⟩,h0Test9_18⟩
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,6],[0,1,2,3,4,6,7,8,10,11,12,13]),([0,1,2,3,4,5,7],[0,1,6,7,8,10,11,12,13,28,213,251]),([0,1,2,3,4,5,8],[0,1,6,7,8,10,11,12,13,28,388,389]),([0,1,2,3,4,5,9],[0,1,4,5,6,7,8,10,11,12,13,147]),([0,1,2,3,4,5,10],[0,1,7,8,10,11,12,13,28,579]),([0,1,2,3,4,5,11],[0,1,6,7,8,10,11,12,13,28,443]),([0,1,2,3,4,5,12],[0,1,6,7,8,9,10,11,12,13,834,835]),([0,1,2,3,4,5,13],[0,1,6,7,8,10,11,12,13,230,249]),([0,1,2,3,4,5,14],[0,1,6,7,8,10,11,12,13,1025,1026]),([0,1,2,3,4,5,15],[0,1,6,7,8,9,10,11,12,13,265,273]),([0,1,2,3,4,5,16],[0,1,6,7,8,10,12,13,1164,1165]),([0,1,2,3,4,5,17],[0,1,6,7,8,10,11,12,13,287,292])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Block10_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,18],[0,1,6,7,8,10,11,12,13,1348,1349]),([0,1,2,3,4,5,19],[0,1,6,7,8,10,11,12,13,302,310]),([0,1,2,3,4,5,20],[0,1,4,6,7,8,10,11,12,13,28,848]),([0,1,2,3,4,5,22],[0,1,6,7,8,10,11,12,13,857]),([0,1,2,3,4,5,23],[0,1,4,6,7,8,9,10,11,12,13,581,591]),([0,1,2,3,4,5,24],[0,1,6,7,8,10,11,12,13,28,1198,1202]),([0,1,2,3,4,5,25],[0,1,4,6,7,8,10,11,12,13,601,605]),([0,1,2,3,4,5,26],[0,1,6,7,8,9,10,11,12,13,28,1215,1217]),([0,1,2,3,4,5,27],[0,1,4,6,7,8,10,11,12,13,611,629]),([0,1,2,3,4,5,28],[0,1,6,7,8,10,11,12,13,28,893,895]),([0,1,2,3,4,5,29],[0,1,4,6,7,8,10,11,12,13,643,659]),([0,1,2,3,4,5,30],[0,1,6,7,8,10,12,13,28,919,921])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_1 = true := by decide +kernel
def h0Block10_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,31],[0,1,6,7,8,9,10,11,12,13,28,32]),([0,1,2,3,4,5,32],[0,1,6,7,8,10,11,12,13,28,51]),([0,1,2,3,4,5,33],[0,1,6,7,8,10,12,13,28,78]),([0,1,2,3,4,5,34],[0,1,6,7,8,10,11,12,13,28,101]),([0,1,2,3,4,5,36],[0,1,6,7,8,9,10,11,12,13,145,150]),([0,1,2,3,4,5,37],[0,1,6,7,8,10,11,12,13,176,183]),([0,1,2,3,4,5,38],[0,1,6,7,8,9,10,11,12,13,192,193]),([0,1,2,3,4,5,39],[0,1,6,7,8,10,12,13,205,206])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_2 = true := by decide +kernel
def h0Nodes10 : List NodeSpec := h0Block10_0 ++ h0Block10_1 ++ h0Block10_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Nodes10 = true := by
  unfold h0Nodes10 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h0Test10_0,h0Test10_1⟩,h0Test10_2⟩
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket9Ok h0Check10
def h0Block11_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[7,13])]
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
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 9]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 10]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276676776 * 2 ^ 32 + 4270368768) ||| ((4276676776 * 2 ^ 32 + 4270368768) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4276676776 * 2 ^ 32 + 4270368768) ||| ((4276676776 * 2 ^ 32 + 4270368768) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_47933
theorem PEqualNP.Outside.L_meta_47933 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 4270368768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4270368768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_47933.table2_of_lower (4276676776 * 2 ^ 32 + 4270368768) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_47933.low_root
    PEqualNP.Outside.L_meta_47933.wit PEqualNP.Outside.L_meta_47933.wo (by decide)
    PEqualNP.Outside.L_meta_47933.wit_mono PEqualNP.Outside.L_meta_47933.wit_eval s hcs
