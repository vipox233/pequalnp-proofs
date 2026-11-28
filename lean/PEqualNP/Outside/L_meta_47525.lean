import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_47525
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
def h1R : List Nat := varsOf 14
def h1G : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def h1Pos : List Nat := [10,12,6,6,12,10]
def h1Neg : List Nat := [8,8,2,4,4,2]
def h1Mask : Nat := fullMask 6
def h1Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xff00ff00ff00ff00ff00ff00ff00ff00,51,3)]
def h1Steps : List (Nat × Nat × Nat) := []
def h1W : BT Decor := buildWiresBT 2 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3)],[(2,3),(1,2)],[(2,3),(1,3)]]
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
lemma h1Bound : Lower h1R h1G 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 3,2,10)]) (by decide +kernel) h1Bucket3Ok (by decide +kernel)
def h2R : List Nat := varsOf 15
def h2G : Nat := 0xa880a880a880a880a880a880a880a880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) h1Bound
def h3R : List Nat := varsOf 19
def h3G : Nat := 0xeeee8888eeee8888eeee8888eeee8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 4 := carry_of (swaps := [(3,4),(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h4R : List Nat := varsOf 23
def h4G : Nat := 0xe0e08080e0e08080e0e08080e0e08080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 5 := carry_of (swaps := [(3,4),(0,1),(1,2)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h5R : List Nat := varsOf 28
def h5G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 4 := carry_of (swaps := [(3,4),(2,3),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h6R : List Nat := varsOf 29
def h6G : Nat := 0xaaa0a000aaa0a000aaa0a000aaa0a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 5 := carry_of (swaps := [(3,4),(2,3),(1,2)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h7R : List Nat := varsOf 15
def h7G : Nat := 0xeae0eae0eae0eae0eae0eae0eae0eae0
def h7Pos : List Nat := [5,11,5,6,6,11,9,14]
def h7Neg : List Nat := [4,10,1,2,4,3,1,10]
def h7Mask : Nat := fullMask 8
def h7Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,103,100),(0xcccccccccccccccccccccccccccccccc,186,170),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,157,17),(0xff00ff00ff00ff00ff00ff00ff00ff00,226,130)]
def h7Steps : List (Nat × Nat × Nat) := []
def h7W : BT Decor := buildWiresBT 2 h7Base h7Steps
def h7AutoList : List (List (Nat × Nat)) := [[],[(1,3),(0,2)]]
def h7Autos : BT (List (Nat × Nat)) := btOfList 1 h7AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Pairs : goodPairs h7G h7Pos h7Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7BaseOk : ∀ x ∈ h7Base, faithful h7Pos h7Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7WOk : btAll (fun x => faithful h7Pos h7Neg x ∧ x.1 < 2^128) h7W := buildWiresBT_faithful h7BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h7G = h7G) h7Autos := btAll_ofList (autos_of (by decide +kernel))
def h7SliceList : List (Option (Nat × Nat)) := []
def h7Slices : BT (Option (Nat × Nat)) := btOfList 1 h7SliceList
def h7Specs : List PoolSpec := []
def h7Pools : BT (Option BoundPool) := buildPoolsBT 1 h7W h7R h7Slices h7Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h7R h7G p.1 p.2) h7Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h7R h7G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h7R h7G c) h7Pools := buildPoolsBT_sound h7SlicesOk
def h7Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G (3 - 1) xs.toFinset) h7Empty := trivial
def h7Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test3_0 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Block3_0 = true := by decide +kernel
def h7Nodes3 : List NodeSpec := h7Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Check3 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Nodes3 = true := h7Test3_0
def h7Bucket3 : BT (List (List Nat)) := buildBucketsBT h7W h7Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G 3 xs.toFinset) h7Bucket3 := buildBucketsBT_sound (by decide) h7Pairs h7WOk h7PoolsOk h7AutosOk h7EmptyOk h7Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) h7Bucket3Ok (by decide +kernel)
def h8R : List Nat := varsOf 23
def h8G : Nat := 0xeaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8
def h8Pos : List Nat := [5,22,5,17,3,5,22,17,22,3,3,7,7]
def h8Neg : List Nat := [4,20,6,16,2,1,18,1,6,1,0,6,1]
def h8Mask : Nat := fullMask 13
def h8Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7869,4768),(0xcccccccccccccccccccccccccccccccc,8018,2388),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6503,2311),(0xffff0000ffff0000ffff0000ffff0000,458,74)]
def h8Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,1,2),(1,1,2),(2,1,2),(1,2,4),(2,2,4),(0,2,5),(3,2,5),(1,3,10),(2,3,10)]
def h8W : BT Decor := buildWiresBT 5 h8Base h8Steps
def h8AutoList : List (List (Nat × Nat)) := [[],[(2,4)],[(1,2)],[(1,4)],[(2,4),(1,2)],[(2,4),(1,4)]]
def h8Autos : BT (List (Nat × Nat)) := btOfList 3 h8AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Pairs : goodPairs h8G h8Pos h8Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8BaseOk : ∀ x ∈ h8Base, faithful h8Pos h8Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8WOk : btAll (fun x => faithful h8Pos h8Neg x ∧ x.1 < 2^128) h8W := buildWiresBT_faithful h8BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h8G = h8G) h8Autos := btAll_ofList (autos_of (by decide +kernel))
def h8SliceList : List (Option (Nat × Nat)) := []
def h8Slices : BT (Option (Nat × Nat)) := btOfList 1 h8SliceList
def h8Specs : List PoolSpec := []
def h8Pools : BT (Option BoundPool) := buildPoolsBT 1 h8W h8R h8Slices h8Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h8R h8G p.1 p.2) h8Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h8R h8G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h8R h8G c) h8Pools := buildPoolsBT_sound h8SlicesOk
def h8Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h8G (3 - 1) xs.toFinset) h8Empty := trivial
def h8Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,3,11],[]),([0,1,3,12],[]),([0,1,3,13],[]),([0,1,3,14],[]),([0,3,8,9],[]),([0,1,2,15],[]),([0,1,2,16],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Test3_0 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Empty 3 h8Block3_0 = true := by decide +kernel
def h8Nodes3 : List NodeSpec := h8Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Check3 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Empty 3 h8Nodes3 = true := h8Test3_0
def h8Bucket3 : BT (List (List Nat)) := buildBucketsBT h8W h8Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h8G 3 xs.toFinset) h8Bucket3 := buildBucketsBT_sound (by decide) h8Pairs h8WOk h8PoolsOk h8AutosOk h8EmptyOk h8Check3
def h8Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0,1]),([0,1,2,3,5],[],[0,1]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Test4_0 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Bucket3 4 h8Block4_0 = true := by decide +kernel
def h8Nodes4 : List NodeSpec := h8Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Check4 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Bucket3 4 h8Nodes4 = true := h8Test4_0
def h8Bucket4 : BT (List (List Nat)) := buildBucketsBT h8W h8Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h8G 4 xs.toFinset) h8Bucket4 := buildBucketsBT_sound (by decide) h8Pairs h8WOk h8PoolsOk h8AutosOk h8Bucket3Ok h8Check4
def h8Block5_0 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Test5_0 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Bucket4 5 h8Block5_0 = true := by decide +kernel
def h8Nodes5 : List NodeSpec := h8Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Check5 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Bucket4 5 h8Nodes5 = true := h8Test5_0
def h8Bucket5 : BT (List (List Nat)) := buildBucketsBT h8W h8Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h8G 5 xs.toFinset) h8Bucket5 := buildBucketsBT_sound (by decide) h8Pairs h8WOk h8PoolsOk h8AutosOk h8Bucket4Ok h8Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 4,1,17)]) (by decide +kernel) h8Bucket5Ok (by decide +kernel)
def h9R : List Nat := varsOf 27
def h9G : Nat := 0xeeeeaa88eeeeaa88eeeeaa88eeeeaa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,1,9)]) (by decide +kernel) h3Bound
def h10R : List Nat := varsOf 30
def h10G : Nat := 0xfff0fcc0fff0fcc0fff0fcc0fff0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,4,6)]) (by decide +kernel) h5Bound
def h12R : List Nat := varsOf 29
def h12G : Nat := 0xfaf0aaa0faf0aaa0faf0aaa0faf0aaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 4 := carry_of (swaps := [(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h11R : List Nat := varsOf 31
def h11G : Nat := 0xeae0a880eae0a880eae0a880eae0a880
def h11Pos : List Nat := [13,22,13,22,25,7,21,11,22,21,7,13,13,30,25,11,25,30,21,7,7,21,22,30,13,7,23,11,11,21,25,27,22,27,15,7,11,22,22,13,7,13,29,25,7,11,22,22,22,11,27,25]
def h11Neg : List Nat := [12,20,14,18,24,3,20,3,6,5,6,9,5,26,9,9,17,28,17,1,5,19,26,14,1,19,19,26,10,1,1,19,14,26,14,4,14,19,16,28,2,8,28,19,14,2,4,0,2,1,9,26]
def h11Mask : Nat := fullMask 52
def h11Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xe3f9eff3ddef5,0x60820e73ddaa0),(0xcccccccccccccccccccccccccccccccc,0x7f17f9edaa5aa,0x939379ee025ac),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1d7ed27fe3f6f,0x549d00921747),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xe2e96d983f895,0xc169718c2e815),(0xffff0000ffff0000ffff0000ffff0000,0xdcc63e4e7635a,0x80ce28e67205a)]
def h11Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,0,19),(2,0,19),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(0,2,4),(1,2,4),(2,2,4),(2,2,5),(2,3,4),(1,4,5),(0,0,31),(2,0,31),(0,2,31),(0,0,34),(2,0,34),(0,3,31),(2,3,34),(2,19,31),(2,31,34),(1,4,19),(2,4,19),(2,4,5),(1,5,19),(0,0,44),(0,2,44),(0,1,3),(3,1,3),(0,1,4),(1,1,4),(2,1,4),(2,0,22),(1,1,22),(1,5,22),(0,0,54),(2,0,25),(1,1,25),(0,0,57),(1,5,25),(0,0,27),(3,1,27),(3,5,27),(1,1,28),(3,4,63),(1,5,28),(1,1,30),(1,5,30),(1,1,34),(0,2,6),(1,1,69),(0,3,69),(2,3,69),(3,2,6),(0,3,6),(0,4,6),(3,4,6),(2,6,22),(2,6,25),(1,1,73),(1,1,74),(1,7,19),(2,2,33),(2,3,8),(1,8,22),(1,8,25),(0,2,50),(1,4,86),(1,9,13),(1,13,86),(3,2,50),(2,2,35),(1,13,35),(3,9,50),(1,13,50),(3,13,50),(1,3,86),(2,3,86),(0,3,50),(0,1,10),(0,3,10),(3,11,50),(2,3,12),(0,0,41),(0,2,41),(2,0,39),(3,4,80),(0,2,89),(2,0,64),(3,14,17),(3,1,109),(1,14,19),(1,14,50),(3,14,50),(1,4,110),(1,14,86),(2,3,16),(3,16,50),(3,28,50),(2,4,18),(1,19,28),(1,19,51),(1,4,47),(2,0,48),(1,4,48),(0,0,124),(1,22,49),(3,22,50),(3,49,50),(1,25,49),(3,25,50),(0,50,120),(2,50,120),(2,2,131),(1,22,51),(1,25,51)]
def h11W : BT Decor := buildWiresBT 8 h11Base h11Steps
def h11AutoList : List (List (Nat × Nat)) := [[],[(1,4)]]
def h11Autos : BT (List (Nat × Nat)) := btOfList 1 h11AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Pairs : goodPairs h11G h11Pos h11Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11BaseOk : ∀ x ∈ h11Base, faithful h11Pos h11Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11WOk : btAll (fun x => faithful h11Pos h11Neg x ∧ x.1 < 2^128) h11W := buildWiresBT_faithful h11BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h11G = h11G) h11Autos := btAll_ofList (autos_of (by decide +kernel))
def h11SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,4),some (subcubeFast 0 4,5),some (subcubeFast 0 8,6),some (subcubeFast 0 16,4),some (subcubeFast 2 0,5),some (subcubeFast 2 1,4),some (subcubeFast 8 0,5),some (subcubeFast 8 4,4),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4)]
def h11Slices : BT (Option (Nat × Nat)) := btOfList 4 h11SliceList
def h11Specs : List PoolSpec := [(0,[]),(5,[]),(6,[]),(3,[(0,0,1)]),(1,[]),(2,[]),(7,[(3,1,2)]),(0,[(1,4,5)]),(9,[(0,0,1)]),(10,[]),(7,[]),(3,[]),(4,[]),(9,[]),(3,[(0,0,1),(2,2,5)]),(3,[(0,0,1),(1,4,5)]),(0,[(2,4,5)]),(3,[(0,0,1),(2,4,5)]),(3,[(1,0,1)]),(5,[(0,2,6)]),(5,[(0,4,6)]),(3,[(1,0,1),(0,2,6)]),(3,[(1,0,1),(3,2,6)]),(5,[(3,2,6)]),(5,[(0,3,6)]),(3,[(1,0,1),(0,4,6)]),(3,[(1,0,1),(3,4,6)]),(5,[(3,4,6)]),(3,[(2,0,1)]),(9,[(2,0,1)]),(5,[(0,0,19)]),(5,[(2,0,31)]),(3,[(3,0,1)]),(2,[(0,0,3)]),(8,[]),(5,[(0,0,2),(0,0,3)]),(7,[(0,0,2)]),(3,[(0,0,2)]),(5,[(0,0,3)]),(9,[(0,0,3)]),(2,[(2,0,3)]),(5,[(2,0,3)]),(9,[(2,0,3)]),(3,[(2,0,25)]),(5,[(0,0,2)]),(3,[(1,0,2)]),(3,[(1,0,2),(0,1,10)]),(3,[(2,0,2)]),(3,[(2,0,22)]),(9,[(0,0,2)]),(7,[(3,0,2)]),(3,[(3,0,2)]),(2,[(2,3,12)]),(3,[(3,1,2)]),(9,[(0,0,3),(0,0,1)]),(0,[(1,1,4)]),(3,[(1,1,4)]),(5,[(0,0,3),(0,0,31)]),(3,[(1,1,2)]),(3,[(0,1,2)]),(7,[(0,1,2)]),(3,[(0,2,4)]),(3,[(2,2,4),(1,1,28)]),(3,[(2,2,4)]),(2,[(2,3,16)]),(5,[(0,0,44)]),(3,[(2,1,2)]),(3,[(2,1,2),(2,4,18)]),(5,[(2,0,19)]),(0,[(2,1,4)]),(3,[(3,1,2),(1,4,19)]),(3,[(1,4,47)]),(3,[(2,0,48)]),(5,[(2,0,48)]),(3,[(1,4,48)]),(3,[(0,1,4)]),(3,[(0,1,4),(1,1,4)]),(5,[(0,0,31)]),(3,[(2,1,4)]),(2,[(2,0,22)]),(3,[(1,1,22)]),(2,[(1,1,22)]),(3,[(1,1,25)])]
def h11Pools : BT (Option BoundPool) := buildPoolsBT 7 h11W h11R h11Slices h11Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice10 : Slice h11R h11G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice9 : Slice h11R h11G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice8 : Slice h11R h11G (subcubeFast 8 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice7 : Slice h11R h11G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice6 : Slice h11R h11G (subcubeFast 2 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice5 : Slice h11R h11G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice4 : Slice h11R h11G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice3 : Slice h11R h11G (subcubeFast 0 8) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice2 : Slice h11R h11G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice1 : Slice h11R h11G (subcubeFast 0 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice0 : Slice h11R h11G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h11R h11G p.1 p.2) h11Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h11R h11G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h11Slice0) (forall_cons (fun _ h => by cases h; exact h11Slice1) (forall_cons (fun _ h => by cases h; exact h11Slice2) (forall_cons (fun _ h => by cases h; exact h11Slice3) (forall_cons (fun _ h => by cases h; exact h11Slice4) (forall_cons (fun _ h => by cases h; exact h11Slice5) (forall_cons (fun _ h => by cases h; exact h11Slice6) (forall_cons (fun _ h => by cases h; exact h11Slice7) (forall_cons (fun _ h => by cases h; exact h11Slice8) (forall_cons (fun _ h => by cases h; exact h11Slice9) (forall_cons (fun _ h => by cases h; exact h11Slice10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h11R h11G c) h11Pools := buildPoolsBT_sound h11SlicesOk
def h11Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G (4 - 1) xs.toFinset) h11Empty := trivial
def h11Block4_0 : List NodeSpec := nodesWithIdentity [([0,3,19,31,34],[]),([0,3,19,31,40],[]),([0,2,3,31,57],[]),([0,1,2,31,38],[]),([1,4,9,13,86],[]),([1,2,4,13,35],[11]),([1,2,4,13,93],[]),([2,4,13,19,32],[54]),([1,2,4,13,105],[]),([2,4,13,32,80],[54]),([1,2,4,13,91],[]),([0,1,2,4,89],[11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test4_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 4 h11Block4_0 = true := by decide +kernel
def h11Block4_1 : List NodeSpec := nodesWithIdentity [([0,1,4,13,107],[]),([0,1,2,14,114],[]),([0,1,2,4,115],[]),([0,2,3,49,127],[]),([0,2,3,50,129],[]),([0,3,50,86,120],[]),([0,3,50,90,120],[]),([0,2,3,50,131],[]),([0,2,3,50,132],[]),([0,2,49,50,97],[]),([0,2,3,50,133],[]),([1,2,4,86,92],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test4_1 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 4 h11Block4_1 = true := by decide +kernel
def h11Block4_2 : List NodeSpec := nodesWithIdentity [([1,3,4,88,104],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test4_2 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 4 h11Block4_2 = true := by decide +kernel
def h11Nodes4 : List NodeSpec := h11Block4_0 ++ h11Block4_1 ++ h11Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check4 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 4 h11Nodes4 = true := by
  unfold h11Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h11Test4_0,h11Test4_1⟩,h11Test4_2⟩
def h11Bucket4 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 4 xs.toFinset) h11Bucket4 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11EmptyOk h11Check4
def h11Block5_0 : List NodeSpec := nodesWithIdentity [([0,2,3,19,31],[1,2,7,8,9]),([0,2,3,4,19,31],[8,9]),([0,2,3,4,19,44],[]),([0,1,2,3,22,31],[]),([0,1,2,3,22,43],[]),([0,1,2,3,4,54],[]),([0,2,3,4,5,57],[]),([0,1,2,3,25,31],[1]),([0,1,2,3,25,43],[]),([0,1,2,3,4,59],[]),([1,2,3,4,5,60],[5]),([0,2,3,4,5,61],[12])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_0 = true := by decide +kernel
def h11Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,62],[1]),([0,2,3,4,5,63],[12]),([0,1,2,3,4,65],[1]),([0,2,3,4,5,66],[12]),([0,1,2,3,4,67],[1]),([0,1,2,3,31,34],[1,8,12,15]),([0,1,2,3,31,40],[1,9]),([0,1,2,3,31,37],[]),([0,1,2,3,4,34],[1,10,11,12]),([0,1,3,4,22,69],[4,11,19]),([0,1,2,3,22,75],[4,20]),([0,1,2,3,22,76],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_1 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_1 = true := by decide +kernel
def h11Block5_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,77],[0,11]),([0,1,3,4,25,69],[]),([0,1,2,3,25,75],[]),([0,1,2,3,25,76],[]),([0,1,2,3,4,78],[0,11]),([0,1,3,4,69,71],[4,19]),([0,1,3,4,69,72],[]),([0,1,2,3,4,82],[10,11]),([0,2,3,4,8,53],[10]),([0,1,2,3,4,84],[11]),([0,1,2,3,4,85],[11]),([1,2,4,9,13,50],[2,9,33])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_2 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_2 = true := by decide +kernel
def h11Block5_3 : List NodeSpec := nodesWithIdentity [([1,2,4,9,13,70],[0,2,35]),([1,2,4,9,13,20],[2]),([0,1,2,4,14,56],[43]),([1,2,3,4,9,21],[11]),([1,2,3,4,9,32],[2,5,9]),([0,1,3,4,9,86],[0,4,12]),([0,1,2,3,4,35],[1,10,11,13]),([0,1,2,3,4,93],[]),([0,1,2,4,14,52],[48]),([0,1,3,4,11,86],[]),([0,1,2,3,4,101],[10,11]),([0,2,4,13,19,50],[33,39])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_3 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_3 = true := by decide +kernel
def h11Block5_4 : List NodeSpec := [([0,1,2,4,13,41],[],[0]),([0,1,2,4,13,39],[0],[0]),([1,2,4,13,32],[2,7,9,11,54,57],[0,1]),([1,2,4,13,32,50],[0,2,54,57],[0]),([0,2,4,13,50,80],[10,39],[0]),([0,1,2,4,13,86],[0,10],[0]),([0,1,2,4,13,94],[0,11,33],[0]),([0,1,2,4,13,95],[0,11],[0]),([0,1,2,4,13,106],[],[0]),([1,2,3,4,13,32],[2,11],[0]),([0,1,2,3,4,95],[0],[0]),([0,1,2,4,14,64],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_4 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_4 = true := by decide +kernel
def h11Block5_5 : List NodeSpec := nodesWithIdentity [([0,1,2,4,14,109],[58]),([0,2,4,14,19,50],[40,42]),([0,1,2,4,14,41],[]),([0,1,2,4,14,39],[]),([0,1,2,4,14,111],[]),([0,1,2,4,14,110],[42]),([0,1,2,4,14,86],[11]),([0,1,2,4,14,112],[]),([0,1,2,4,14,113],[56]),([0,2,3,16,26,50],[1,5]),([0,2,3,16,28,50],[1]),([0,2,3,4,50,117],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_5 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_5 = true := by decide +kernel
def h11Block5_6 : List NodeSpec := nodesWithIdentity [([0,2,3,4,16,68],[]),([0,1,2,3,4,86],[10,11]),([0,2,3,4,16,63],[62]),([0,1,2,3,4,108],[1]),([0,2,3,4,19,32],[1,8]),([0,2,3,19,28,50],[1,5]),([0,2,3,4,19,121],[1]),([0,1,2,3,4,103],[1]),([0,1,2,3,4,105],[]),([0,1,2,3,4,125],[1]),([0,2,3,22,49,50],[4]),([0,2,3,25,49,50],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_6 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_6 = true := by decide +kernel
def h11Block5_7 : List NodeSpec := nodesWithIdentity [([0,2,3,50,120],[1,2,55]),([0,2,3,49,50,86],[1,4,76]),([0,2,3,49,50,90],[1]),([0,2,3,49,50,98],[76]),([0,2,3,50,128],[1,2,55]),([0,2,3,4,49,53],[4]),([0,1,2,3,4,126],[]),([0,1,2,3,4,129],[]),([0,1,2,3,4,91],[]),([0,1,3,4,22,86],[11]),([0,1,2,3,4,127],[]),([0,1,3,4,25,86],[11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_7 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_7 = true := by decide +kernel
def h11Block5_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,130],[10]),([0,1,2,3,4,36],[10,11]),([0,1,2,4,86,96],[10]),([0,1,2,4,86,97],[11]),([0,1,2,4,50,97],[]),([0,1,2,3,4,134],[]),([0,2,3,4,51,57],[]),([0,1,2,3,4,135],[]),([0,1,3,4,23,104],[1,12]),([0,1,3,4,24,104],[1]),([0,1,2,3,4,55],[10,12,13]),([0,1,2,3,4,58],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_8 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_8 = true := by decide +kernel
def h11Nodes5 : List NodeSpec := h11Block5_0 ++ h11Block5_1 ++ h11Block5_2 ++ h11Block5_3 ++ h11Block5_4 ++ h11Block5_5 ++ h11Block5_6 ++ h11Block5_7 ++ h11Block5_8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check5 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Nodes5 = true := by
  unfold h11Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h11Test5_0,h11Test5_1⟩,h11Test5_2⟩,h11Test5_3⟩,h11Test5_4⟩,h11Test5_5⟩,h11Test5_6⟩,h11Test5_7⟩,h11Test5_8⟩
def h11Bucket5 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 5 xs.toFinset) h11Bucket5 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11Bucket4Ok h11Check5
def h11Block6_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,19],[0,1,2,4,5,6,8]),([0,1,2,3,4,5,22],[1,10]),([0,1,2,3,4,5,25],[1,5,10,11]),([0,1,2,3,4,5,27],[0,1,5,12,13]),([0,1,2,3,4,5,28],[1,9,12,13]),([0,1,2,3,4,29],[0,1,2,4,10,11,12,13,14]),([0,1,2,3,4,5,30],[1,10,12,13]),([0,1,2,3,31],[1,2,7,9,12,15]),([0,1,2,3,4,31],[0,1,2,4,5,7,8,9,10,11,12,15]),([0,1,2,3,43],[1,2,13,16,17]),([0,1,2,3,4,6,22],[0,1,4,5,10,11]),([0,1,2,3,4,6,25],[0,5,10,11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_0 = true := by decide +kernel
def h11Block6_1 : List NodeSpec := nodesWithIdentity [([0,1,3,4,69],[0,2,4,9,19,21]),([0,1,2,3,4,69],[0,1,2,4,9,10,11,12,13,19,21]),([0,1,3,4,73],[0,4,5,9,22,23]),([0,1,2,4,74],[0,4,9,10,11,18,24]),([0,1,2,3,75],[0,4,13,20,25]),([0,1,2,3,76],[0,4,9,12,26,27]),([0,2,3,4,7,19],[0,1,2,4,5,6,29]),([0,1,2,3,4,7,22],[2,4,10]),([0,1,2,3,4,7,25],[1,2,4,5,10,11]),([0,1,2,3,4,7,27],[1,2,4,5]),([0,1,2,3,4,7,28],[1,2,4,9,12,13]),([0,1,2,3,4,20],[2,4,10,11,12,13,30])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_1 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_1 = true := by decide +kernel
def h11Block6_2 : List NodeSpec := [([0,1,2,3,4,7,30],[1,2,4,10],[0]),([0,1,2,3,4,33],[2,4,5,7,9,10,11,12,31],[0]),([0,1,2,3,4,8,22],[0,1,10,11],[0]),([0,1,2,3,4,8,25],[0,5,10,11],[0]),([0,1,2,3,4,46],[0,1,9,10,11,12,13],[0]),([0,1,2,4,83],[0,1,9,10,11,32],[0]),([1,2,4,9,13],[0,2,9,11,33,34,36,37],[0,1]),([0,1,2,4,9,13],[0,2,9,10,11,33,34,37,38,39],[0]),([0,1,2,4,9,14],[0,2,9,10,11,34,37,40,41,42],[0]),([0,1,2,3,4,9,19],[0,1,4,34,44],[0]),([0,1,2,3,4,9,50],[0,1,2,4,5,9,12,13],[0]),([0,1,2,3,4,70],[0,1,2,4,5,10,11,12,13,19],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_2 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_2 = true := by decide +kernel
def h11Block6_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,9,70],[0,1,2,4,44]),([0,1,2,3,4,9,20],[1,2,4]),([0,2,3,4,99],[0,1,5,9,46]),([0,2,3,4,81],[0,2,4,5,9]),([0,1,2,4,100],[0,2,5,10,11,45]),([0,1,2,4,11,14],[0,2,9,11,40,41,42,47]),([0,1,2,3,4,9],[0,1,4,5,10,11,12,13,34,37,44,49]),([0,1,2,3,4,11,50],[1,2,4,5,9,12,13]),([0,1,2,3,4,79],[0,1,2,4,5,10,11,12,13,23]),([1,2,4,12,13],[0,2,9,33,34,50]),([0,1,2,4,102],[0,2,9,10,11,51,52]),([0,1,2,4,13,19],[0,2,6,10,33,34,38,39,53])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_3 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_3 = true := by decide +kernel
def h11Block6_4 : List NodeSpec := [([0,1,2,4,13,50],[0,2,9,10,33,38,39,55,56],[0,1]),([0,1,2,4,13,80],[0,2,10,11,18,24,33,34,38,39],[0]),([0,1,2,3,4,13,50],[0,1,2,4,10,11,12,13,56],[0]),([0,1,2,3,4,80],[0,2,4,5,10,11,12,13,18,24,34],[0]),([0,1,2,4,13],[0,2,9,10,11,33,34,38,39],[0]),([0,1,2,4,14,17],[0,2,11,40,41,42,58],[0]),([0,1,2,4,14,19],[0,2,11,40,41,42,53],[0]),([0,1,2,4,14,50],[0,2,9,11,40,41,42,55,56],[0,1]),([0,2,3,4,16,50],[1,2,4,5,13,55,60],[0]),([0,1,2,3,4,16,26],[1,5,13,34,59,61],[0,1]),([0,1,2,3,4,16,28],[1,4,12,13,34,63],[0]),([0,1,2,3,4,19],[0,1,2,4,5,10,11,12,13,53],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_4 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_4 = true := by decide +kernel
def h11Block6_5 : List NodeSpec := [([0,1,2,4,116],[1,2,10,34,59,64],[0]),([0,1,2,3,4,87],[0,1,2,4,5,10,11,12],[0,1]),([0,1,2,3,4,45],[0,1,2,4,5,10,11,12,13,34,65],[0,1]),([0,1,2,3,4,64],[0,1,4,5,10,11,12,34],[0,1]),([0,1,2,3,118],[1,2,5,12,34],[0]),([0,1,2,3,4,118],[0,1,2,5,10,11,12,34],[0]),([0,1,2,3,119],[1,2,5,13,67],[0]),([0,1,2,3,4,21],[0,1,2,4,5,10,11,12,13,68],[0]),([0,1,2,3,4,19,21],[0,1,4,5,68],[0]),([0,2,3,4,19,50],[1,2,4,5,6,13,55],[0,1]),([0,2,3,4,19,51],[1,2,4,5,6,13,69],[0]),([0,1,2,3,4,19,28],[1,4,12,13],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_5 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_5 = true := by decide +kernel
def h11Block6_6 : List NodeSpec := [([0,1,2,3,4,41],[0,1,4,5,10,11,12,70],[0,1]),([0,1,2,3,4,19,41],[1,4,5,13],[0]),([0,1,2,3,4,19,42],[1,4,5,12,13],[0]),([0,1,2,3,4,39],[0,4,10,11,12],[0]),([0,1,2,3,4,122],[0,1,2,5,10,11,12,34,71],[0]),([0,1,2,3,4,123],[0,1,2,4,5,10,11,12,13,34,72,73],[0]),([0,1,2,3,4,124],[0,1,4,5,10,11,12,34,74],[0,1]),([0,2,3,49,50],[1,2,4,55,76],[0]),([0,1,2,3,4,22,49],[1,10,13],[0,1]),([0,1,2,3,4,25,49],[1,5,10,11],[0]),([0,1,2,3,4,120],[0,1,2,5,10,11,13],[0]),([0,1,2,3,4,32],[0,1,2,4,5,7,8,9,10,11,12,13,77],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_6 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_6 = true := by decide +kernel
def h11Block6_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,32,50],[0,1,2,4,8,12,13,55,77]),([0,1,2,3,4,22,50],[4,5,10,11]),([0,1,2,3,4,25,50],[1,4,5,10,11,12,13]),([0,1,2,3,4,86],[0,1,4,5,10,11,12,13]),([0,1,2,3,4,50,86],[1,4,5,12,13,56]),([0,1,2,3,4,50,90],[1,4,5,12,13]),([0,1,2,3,4,50,98],[10,11,56]),([0,1,2,3,4,22,51],[1,10,12,13]),([0,1,2,3,4,25,51],[1,5,10,11]),([0,1,2,3,4,104],[0,1,2,4,5,10,11,12]),([0,1,2,3,4,50],[0,1,2,4,5,10,11,12,13,55,56]),([0,1,2,3,4,52],[0,1,4,5,10,11,12,13,34,48,79])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_7 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_7 = true := by decide +kernel
def h11Block6_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,53],[0,1,4,5,10,11,12,13,34,80,81]),([0,1,2,3,4,56],[0,1,4,5,10,11,12,13,43]),([0,1,2,3,4,57],[0,1,4,5,10,11,12,13,82])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_8 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_8 = true := by decide +kernel
def h11Nodes6 : List NodeSpec := h11Block6_0 ++ h11Block6_1 ++ h11Block6_2 ++ h11Block6_3 ++ h11Block6_4 ++ h11Block6_5 ++ h11Block6_6 ++ h11Block6_7 ++ h11Block6_8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check6 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Nodes6 = true := by
  unfold h11Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h11Test6_0,h11Test6_1⟩,h11Test6_2⟩,h11Test6_3⟩,h11Test6_4⟩,h11Test6_5⟩,h11Test6_6⟩,h11Test6_7⟩,h11Test6_8⟩
def h11Bucket6 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 6 xs.toFinset) h11Bucket6 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11Bucket5Ok h11Check6
def h11Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,5,9,10,11,13],[0]),([0,1,2,3,4,6],[0,1,2,4,5,9,10,11,13,18],[0]),([0,1,2,3,4,7],[0,1,2,4,5,9,10,11,13,28],[0]),([0,1,2,3,4,8],[0,1,5,9,10,11,13,32],[0]),([0,1,2,3,4,9],[0,1,2,5,9,10,11,13,34,37],[0,1]),([0,1,2,3,4,10],[0,1,2,5,9,10,11,13,45],[0,1]),([0,1,2,3,4,11],[0,1,2,5,9,10,11,13,34,47],[0,1]),([0,1,2,3,4,12],[0,1,2,5,9,10,11,13,34,51],[0]),([0,1,2,4,13],[0,2,9,10,11,34],[0,1]),([0,1,2,3,4,13],[0,1,2,5,9,10,11,13,34],[0,1]),([0,1,2,4,14],[0,2,9,11],[0,1]),([0,1,2,3,4,15],[0,1,2,5,9,11,13,34],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test7_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket6 7 h11Block7_0 = true := by decide +kernel
def h11Block7_1 : List NodeSpec := [([0,1,2,3,4,16],[0,1,2,5,10,11,13,34,59],[0]),([0,1,2,3,4,17],[0,1,2,4,5,10,11,13,34,58],[0,1]),([0,1,2,3,4,18],[0,1,2,5,10,11,13,34,66],[0]),([0,1,2,3,4,19],[0,1,2,4,5,10,11,13,34,53],[0,1]),([0,1,2,3,4,47],[0,1,2,5,10,11,13,34],[0]),([0,1,2,3,4,48],[0,1,2,4,5,10,11,13,34],[0,1]),([0,1,2,3,4,49],[0,1,2,5,10,11,13,75],[0]),([0,1,2,3,4,50],[0,1,2,4,5,9,10,11,12,13,56],[0,1]),([0,1,2,3,4,51],[0,1,2,5,10,11,12,13,78],[0]),([0,1,2,3,4,22],[0,1,5,10,11,13,34],[0,1]),([0,1,2,3,4,25],[0,1,5,10,11,13],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test7_1 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket6 7 h11Block7_1 = true := by decide +kernel
def h11Nodes7 : List NodeSpec := h11Block7_0 ++ h11Block7_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check7 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket6 7 h11Nodes7 = true := by
  unfold h11Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h11Test7_0,h11Test7_1⟩
def h11Bucket7 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 7 xs.toFinset) h11Bucket7 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11Bucket6Ok h11Check7
def h11Block8_0 : List NodeSpec := [([0,1,2,3,4],[11],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test8_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket7 8 h11Block8_0 = true := by decide +kernel
def h11Nodes8 : List NodeSpec := h11Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check8 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket7 8 h11Nodes8 = true := h11Test8_0
def h11Bucket8 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 8 xs.toFinset) h11Bucket8 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11Bucket7Ok h11Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 9 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,5,21)]) (by decide +kernel) h11Bucket8Ok (by decide +kernel)
def h13R : List Nat := varsOf 38
def h13G : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 4 := carry_of (swaps := [(3,4),(4,5)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h14R : List Nat := varsOf 42
def h14G : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 4 := carry_of (swaps := [(3,4),(4,5),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h15R : List Nat := varsOf 43
def h15G : Nat := 0xaa88aa8888008800aa88aa8888008800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 5 := carry_of (swaps := [(3,4),(4,5),(2,3)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h16R : List Nat := varsOf 44
def h16G : Nat := 0xfff0fff0f000f000fff0fff0f000f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 4 := carry_of (swaps := [(3,4),(4,5),(2,3),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h17R : List Nat := varsOf 45
def h17G : Nat := 0xaaa0aaa0a000a000aaa0aaa0a000a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 5 := carry_of (swaps := [(3,4),(4,5),(2,3),(1,2)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h18R : List Nat := varsOf 15
def h18G : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 6 := carry_of (swaps := [(3,4)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h19R : List Nat := varsOf 39
def h19G : Nat := 0xeaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 6 := carry_of (swaps := [(4,5)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h20R : List Nat := varsOf 43
def h20G : Nat := 0xeeaaeeaaaa88aa88eeaaeeaaaa88aa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 6 := carry_of (swaps := [(4,5),(2,3)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h21R : List Nat := varsOf 45
def h21G : Nat := 0xfaaafaaaaaa0aaa0faaafaaaaaa0aaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 6 := carry_of (swaps := [(4,5),(2,3),(1,2)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
namespace Cofactor12086
def G_0 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_0 : List Nat := varsOf 22
def pos_0 : List Nat := [6,6,18,18,20,20,6,18,20]
def neg_0 : List Nat := [4,2,16,2,16,4,16,4,2]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
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
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(0,3),(0,4),(0,2),(0,1)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0

def G_3 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def R_3 : List Nat := varsOf 19
lemma low_3_ok : carryOK [(0,2),(0,1)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0

def G_6 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def R_6 : List Nat := varsOf 21
lemma low_6_ok : carryOK [(0,1)] R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 4 := carry_of low_6_ok low_0

def G_17 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
def R_17 : List Nat := varsOf 23
def pos_17 : List Nat := [3,3,5,5,6,6,17,17,18,18,20,20,3,3,5,5,6,6,17,17,18,18,20,20]
def neg_17 : List Nat := [2,1,4,1,4,2,16,1,16,2,16,4,4,16,2,16,1,16,2,4,1,4,1,2]
def fmask_17 : Nat := fullMask 24
def base_17 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffff0000ffff0000ffff0000ffff0000,0xfc0fc0,0x2a540)]
def steps_17 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_17 : BT Decor := buildWiresBT 4 base_17 steps_17
def autosL_17 : List (List (Nat × Nat)) := [[],[(2,4)],[(0,1)],[(2,4),(0,1)],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def autos_17 : BT (List (Nat × Nat)) := btOfList 4 autosL_17
def slicesL_17 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 1 0,4),some (subcubeFast 16 0,4),some (subcubeFast 4 0,4)]
def slices_17 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_17
def ps_17 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_17 : BT (Option BoundPool) := buildPoolsBT 2 W_17 R_17 slices_17 ps_17
lemma gp_17 : goodPairs G_17 pos_17 neg_17 := goodPairs_of (by decide +kernel)
lemma base_17_ok : ∀ x ∈ base_17, faithful pos_17 neg_17 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_17_ok : btAll (fun x => faithful pos_17 neg_17 x ∧ x.1 < 2^128) W_17 := buildWiresBT_faithful base_17_ok
set_option maxRecDepth 500000 in
lemma autos_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_17 = G_17) autos_17 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_17_0_ok : sliceDirectCheck 2 0 0 R_17 G_17 R_6 G_6 = true := by decide +kernel
lemma sl_17_0 : Slice R_17 G_17 (subcubeFast 2 0) 4 := slice_fast_direct sl_17_0_ok low_6
lemma sl_17_1_ok : sliceDirectCheck 1 0 0 R_17 G_17 R_0 G_0 = true := by decide +kernel
lemma sl_17_1 : Slice R_17 G_17 (subcubeFast 1 0) 4 := slice_fast_direct sl_17_1_ok low_0
lemma sl_17_2_ok : sliceDirectCheck 16 0 0 R_17 G_17 R_1 G_1 = true := by decide +kernel
lemma sl_17_2 : Slice R_17 G_17 (subcubeFast 16 0) 4 := slice_fast_direct sl_17_2_ok low_1
lemma sl_17_3_ok : sliceDirectCheck 4 0 0 R_17 G_17 R_3 G_3 = true := by decide +kernel
lemma sl_17_3 : Slice R_17 G_17 (subcubeFast 4 0) 4 := slice_fast_direct sl_17_3_ok low_3
set_option maxRecDepth 500000 in
lemma slices_17_ok : btAll (fun o => ∀ p, o = some p → Slice R_17 G_17 p.1 p.2) slices_17 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_17 G_17 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_17_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_17 G_17 c) P_17 := buildPoolsBT_sound slices_17_ok
def bk_17_init : BT (List (List Nat)) := BT.empty
lemma bk_17_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 (0 - 1) xs.toFinset) bk_17_init := trivial
def nodes_17_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_0 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_init 0 nodes_17_0 = true := by decide +kernel
def bk_17_0 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_0
set_option maxRecDepth 500000 in
lemma bk_17_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 0 xs.toFinset) bk_17_0 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_init_ok chk_17_0
def nodes_17_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_1 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_0 1 nodes_17_1 = true := by decide +kernel
def bk_17_1 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_1
set_option maxRecDepth 500000 in
lemma bk_17_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 1 xs.toFinset) bk_17_1 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_0_ok chk_17_1
def nodes_17_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_2 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_1 2 nodes_17_2 = true := by decide +kernel
def bk_17_2 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_2
set_option maxRecDepth 500000 in
lemma bk_17_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 2 xs.toFinset) bk_17_2 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_1_ok chk_17_2
def nodes_17_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_3 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_2 3 nodes_17_3 = true := by decide +kernel
def bk_17_3 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_3
set_option maxRecDepth 500000 in
lemma bk_17_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 3 xs.toFinset) bk_17_3 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_2_ok chk_17_3
def nodes_17_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_4 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_3 4 nodes_17_4 = true := by decide +kernel
def bk_17_4 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_4
set_option maxRecDepth 500000 in
lemma bk_17_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 4 xs.toFinset) bk_17_4 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_3_ok chk_17_4
def nodes_17_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_5 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_4 5 nodes_17_5 = true := by decide +kernel
def bk_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_5
set_option maxRecDepth 500000 in
lemma bk_17_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 5 xs.toFinset) bk_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_4_ok chk_17_5
def nodes_17_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_6 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_5 6 nodes_17_6 = true := by decide +kernel
def bk_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_6
set_option maxRecDepth 500000 in
lemma bk_17_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 6 xs.toFinset) bk_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_5_ok chk_17_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck R_17 G_17 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT bk_17_6 R_17 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_17 : Lower R_17 G_17 7 := lower_of_forestBT root_17_ok bk_17_6_ok root_17_in

end Cofactor12086
def h22R : List Nat := varsOf 46
def h22G : Nat := 0xfffcfffcfcc0fcc0fffcfffcfcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 7 := carry_of (swaps := [(4,5),(2,3),(1,2),(0,1)]) (roots2 := Cofactor12086.R_17) (T2 := Cofactor12086.G_17) (by decide +kernel) Cofactor12086.low_17
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

def G_11 : Nat := 0xff00f000f0000000ff00f000f0000000
def R_11 : List Nat := varsOf 60
lemma low_11_ok : liftCheck 0 8 R_11 G_11 R_0 G_0 [(VAR 3,28,20)] = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 5 := lift_of low_11_ok low_0

def G_12 : Nat := 0xfff0ff00ff00f000fff0ff00ff00f000
def R_12 : List Nat := varsOf 60
def pos_12 : List Nat := [12,12,24,24,28,40,40,44,52,52,52,56,12,12,12,24,24,24,40,40,40,52]
def neg_12 : List Nat := [8,4,16,8,20,32,8,36,48,36,20,48,20,36,48,20,36,48,20,36,48,8]
def fmask_12 : Nat := fullMask 22
def base_12 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x207793,0xdb692),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1ff8ff,0x200049),(0xffff0000ffff0000ffff0000ffff0000,0x238f1c,0x16dd14),(0xffffffff00000000ffffffff00000000,0x3c0fe0,0x1b6ba0)]
def steps_12 : List (Nat × Nat × Nat) := [(2,0,2),(1,0,2),(2,0,1),(0,0,2),(3,0,1),(1,0,1),(0,0,1),(3,0,2),(3,4,3),(2,9,2),(0,9,2),(1,4,3),(3,10,2),(1,10,2),(3,7,5)]
def W_12 : BT Decor := buildWiresBT 5 base_12 steps_12
def autosL_12 : List (List (Nat × Nat)) := [[],[(4,5)],[(2,4)],[(2,5),(2,4)],[(2,4),(2,5)],[(2,5)]]
def autos_12 : BT (List (Nat × Nat)) := btOfList 3 autosL_12
def slicesL_12 : List (Option (Nat × Nat)) := []
def slices_12 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_12
def ps_12 : List PoolSpec := []
def P_12 : BT (Option BoundPool) := buildPoolsBT 1 W_12 R_12 slices_12 ps_12
lemma gp_12 : goodPairs G_12 pos_12 neg_12 := goodPairs_of (by decide +kernel)
lemma base_12_ok : ∀ x ∈ base_12, faithful pos_12 neg_12 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_12_ok : btAll (fun x => faithful pos_12 neg_12 x ∧ x.1 < 2^128) W_12 := buildWiresBT_faithful base_12_ok
set_option maxRecDepth 500000 in
lemma autos_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_12 = G_12) autos_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_12_ok : btAll (fun o => ∀ p, o = some p → Slice R_12 G_12 p.1 p.2) slices_12 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_12 G_12 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_12_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_12 G_12 c) P_12 := buildPoolsBT_sound slices_12_ok
def bk_12_init : BT (List (List Nat)) := BT.empty
lemma bk_12_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 (0 - 1) xs.toFinset) bk_12_init := trivial
def nodes_12_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_0 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_init 0 nodes_12_0 = true := by decide +kernel
def bk_12_0 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_0
set_option maxRecDepth 500000 in
lemma bk_12_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 0 xs.toFinset) bk_12_0 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_init_ok chk_12_0
def nodes_12_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_1 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_0 1 nodes_12_1 = true := by decide +kernel
def bk_12_1 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_1
set_option maxRecDepth 500000 in
lemma bk_12_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 1 xs.toFinset) bk_12_1 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_0_ok chk_12_1
def nodes_12_2 : List NodeSpec := [([18,1,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_2 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_1 2 nodes_12_2 = true := by decide +kernel
def bk_12_2 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_2
set_option maxRecDepth 500000 in
lemma bk_12_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 2 xs.toFinset) bk_12_2 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_1_ok chk_12_2
def nodes_12_3 : List NodeSpec := [([4,11,1,3],[],[0]),([0,1,2,12],[],[]),([7,1,5,3],[],[0]),([13,0,1,3],[],[]),([0,1,14,3],[],[]),([6,8,2,3],[],[]),([0,1,2,15],[],[]),([16,0,1,3],[],[]),([0,1,17,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_3 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_2 3 nodes_12_3 = true := by decide +kernel
def bk_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_3
set_option maxRecDepth 500000 in
lemma bk_12_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 3 xs.toFinset) bk_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_2_ok chk_12_3
def nodes_12_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([0,1,2,5,3],[],[0]),([6,0,1,2,3],[],[0]),([7,0,1,2,3],[],[0]),([8,0,1,2,3],[],[0]),([0,1,9,2,3],[],[0,1]),([10,0,1,2,3],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_4 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_3 4 nodes_12_4 = true := by decide +kernel
def bk_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_4
set_option maxRecDepth 500000 in
lemma bk_12_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 4 xs.toFinset) bk_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_3_ok chk_12_4
def nodes_12_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_5 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_4 5 nodes_12_5 = true := by decide +kernel
def bk_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_5
set_option maxRecDepth 500000 in
lemma bk_12_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 5 xs.toFinset) bk_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_4_ok chk_12_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck R_12 G_12 [(VAR 2,12,8),(VAR 3,12,4),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT bk_12_5 R_12 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_12 : Lower R_12 G_12 6 := lower_of_forestBT root_12_ok bk_12_5_ok root_12_in

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

def G_23 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
def R_23 : List Nat := varsOf 30
lemma low_23_ok : carryOK [(1,5),(1,4),(1,2)] R_23 G_23 R_11 G_11 = true := by decide +kernel
lemma low_23 : Lower R_23 G_23 5 := carry_of low_23_ok low_11

def G_24 : Nat := 0xfc00fc00c000c000fc00fc00c000c000
def R_24 : List Nat := varsOf 46
lemma low_24_ok : carryOK [(1,4),(1,2)] R_24 G_24 R_11 G_11 = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 5 := carry_of low_24_ok low_11

def G_29 : Nat := 0xff00cc00cc000000ff00cc00cc000000
def R_29 : List Nat := varsOf 58
lemma low_29_ok : carryOK [(1,2)] R_29 G_29 R_11 G_11 = true := by decide +kernel
lemma low_29 : Lower R_29 G_29 5 := carry_of low_29_ok low_11

def G_35 : Nat := 0xffc0fc00ffc0fc00ffc0fc00ffc0fc00
def R_35 : List Nat := varsOf 30
lemma low_35_ok : carryOK [(1,5),(1,4),(1,2)] R_35 G_35 R_12 G_12 = true := by decide +kernel
lemma low_35 : Lower R_35 G_35 6 := carry_of low_35_ok low_12

def G_36 : Nat := 0xffc0ffc0fc00fc00ffc0ffc0fc00fc00
def R_36 : List Nat := varsOf 46
lemma low_36_ok : carryOK [(1,4),(1,2)] R_36 G_36 R_12 G_12 = true := by decide +kernel
lemma low_36 : Lower R_36 G_36 6 := carry_of low_36_ok low_12

def G_37 : Nat := 0xffccff00ff00cc00ffccff00ff00cc00
def R_37 : List Nat := varsOf 58
lemma low_37_ok : carryOK [(1,2)] R_37 G_37 R_12 G_12 = true := by decide +kernel
lemma low_37 : Lower R_37 G_37 6 := carry_of low_37_ok low_12

def G_42 : Nat := 0xffc0fc00fc00c000ffc0fc00fc00c000
def R_42 : List Nat := varsOf 62
def pos_42 : List Nat := [14,14,14,26,26,26,28,28,28,30,42,42,42,44,44,44,46,54,54,54,54,56,56,56,58,60,14,14,14,14,14,14,26,26,26,26,26,26,28,28,28,28,28,28,42,42,42,42,42,42,44,44,44,44,44,44,54,54,54,54,56,56,56,56,56,56]
def neg_42 : List Nat := [12,10,6,24,18,10,24,20,12,22,40,34,10,40,36,12,38,52,50,38,22,48,40,24,50,52,22,24,38,40,50,52,12,22,38,40,50,52,10,22,38,40,50,52,12,22,24,38,50,52,10,22,24,38,50,52,10,12,24,40,10,12,22,38,50,52]
def fmask_42 : Nat := fullMask 66
def base_42 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xf03f03ffd1f1e3f,0x1d16da5d6551d1a36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffc0fc0fe1fe3c7,0x2e2aab9a7961bc385),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f0ffffffffe1ffff,0x3f14524928c0b56b),(0xffff0000ffff0000ffff0000ffff0000,0x3ff000fff03fe03f8,0x344db6cb2cfb602d8),(0xffffffff00000000ffffffff00000000,0x3fffff00003fffc00,0x388e38f3cf36f6c00)]
def steps_42 : List (Nat × Nat × Nat) := [(0,0,1),(0,3,4),(1,5,6)]
def W_42 : BT Decor := buildWiresBT 3 base_42 steps_42
def autosL_42 : List (List (Nat × Nat)) := [[],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_42 : BT (List (Nat × Nat)) := btOfList 3 autosL_42
def slicesL_42 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,5),some (subcubeFast 32 0,5),some (subcubeFast 0 16,6),some (subcubeFast 16 0,5),some (subcubeFast 0 32,6),some (subcubeFast 0 2,6),some (subcubeFast 2 0,5),some (subcubeFast 0 4,6),some (subcubeFast 0 8,7),some (subcubeFast 4 8,4)]
def slices_42 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_42
def ps_42 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[(0,3,4)]),(6,[]),(7,[]),(4,[(0,0,1)]),(5,[]),(8,[]),(9,[]),(2,[(0,0,1)])]
def P_42 : BT (Option BoundPool) := buildPoolsBT 4 W_42 R_42 slices_42 ps_42
lemma gp_42 : goodPairs G_42 pos_42 neg_42 := goodPairs_of (by decide +kernel)
lemma base_42_ok : ∀ x ∈ base_42, faithful pos_42 neg_42 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_42_ok : btAll (fun x => faithful pos_42 neg_42 x ∧ x.1 < 2^128) W_42 := buildWiresBT_faithful base_42_ok
set_option maxRecDepth 500000 in
lemma autos_42_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_42 = G_42) autos_42 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_42_0_ok : sliceDirectCheck 4 0 0 R_42 G_42 R_29 G_29 = true := by decide +kernel
lemma sl_42_0 : Slice R_42 G_42 (subcubeFast 4 0) 5 := slice_fast_direct sl_42_0_ok low_29
lemma sl_42_1_ok : sliceDirectCheck 32 0 0 R_42 G_42 R_23 G_23 = true := by decide +kernel
lemma sl_42_1 : Slice R_42 G_42 (subcubeFast 32 0) 5 := slice_fast_direct sl_42_1_ok low_23
lemma sl_42_2_ok : sliceDirectCheck 0 16 0 R_42 G_42 R_36 G_36 = true := by decide +kernel
lemma sl_42_2 : Slice R_42 G_42 (subcubeFast 0 16) 6 := slice_fast_direct sl_42_2_ok low_36
lemma sl_42_3_ok : sliceDirectCheck 16 0 0 R_42 G_42 R_24 G_24 = true := by decide +kernel
lemma sl_42_3 : Slice R_42 G_42 (subcubeFast 16 0) 5 := slice_fast_direct sl_42_3_ok low_24
lemma sl_42_4_ok : sliceDirectCheck 0 32 0 R_42 G_42 R_35 G_35 = true := by decide +kernel
lemma sl_42_4 : Slice R_42 G_42 (subcubeFast 0 32) 6 := slice_fast_direct sl_42_4_ok low_35
lemma sl_42_5_ok : sliceDirectCheck 0 2 0 R_42 G_42 R_12 G_12 = true := by decide +kernel
lemma sl_42_5 : Slice R_42 G_42 (subcubeFast 0 2) 6 := slice_fast_direct sl_42_5_ok low_12
lemma sl_42_6_ok : sliceDirectCheck 2 0 0 R_42 G_42 R_11 G_11 = true := by decide +kernel
lemma sl_42_6 : Slice R_42 G_42 (subcubeFast 2 0) 5 := slice_fast_direct sl_42_6_ok low_11
lemma sl_42_7_ok : sliceDirectCheck 0 4 0 R_42 G_42 R_37 G_37 = true := by decide +kernel
lemma sl_42_7 : Slice R_42 G_42 (subcubeFast 0 4) 6 := slice_fast_direct sl_42_7_ok low_37
lemma sl_42_8_ok : sliceDirectCheck 0 8 0 R_42 G_42 R_13 G_13 = true := by decide +kernel
lemma sl_42_8 : Slice R_42 G_42 (subcubeFast 0 8) 7 := slice_fast_direct sl_42_8_ok low_13
lemma sl_42_9_ok : sliceDirectCheck 4 8 0 R_42 G_42 R_9 G_9 = true := by decide +kernel
lemma sl_42_9 : Slice R_42 G_42 (subcubeFast 4 8) 4 := slice_fast_direct sl_42_9_ok low_9
set_option maxRecDepth 500000 in
lemma slices_42_ok : btAll (fun o => ∀ p, o = some p → Slice R_42 G_42 p.1 p.2) slices_42 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_42 G_42 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_42_0) (forall_cons (fun _ h => by cases h; exact sl_42_1) (forall_cons (fun _ h => by cases h; exact sl_42_2) (forall_cons (fun _ h => by cases h; exact sl_42_3) (forall_cons (fun _ h => by cases h; exact sl_42_4) (forall_cons (fun _ h => by cases h; exact sl_42_5) (forall_cons (fun _ h => by cases h; exact sl_42_6) (forall_cons (fun _ h => by cases h; exact sl_42_7) (forall_cons (fun _ h => by cases h; exact sl_42_8) (forall_cons (fun _ h => by cases h; exact sl_42_9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 500000 in
lemma P_42_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_42 G_42 c) P_42 := buildPoolsBT_sound slices_42_ok
def bk_42_init : BT (List (List Nat)) := BT.empty
lemma bk_42_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 (0 - 1) xs.toFinset) bk_42_init := trivial
def nodes_42_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_0 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_init 0 nodes_42_0 = true := by decide +kernel
def bk_42_0 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_0
set_option maxRecDepth 500000 in
lemma bk_42_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 0 xs.toFinset) bk_42_0 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_init_ok chk_42_0
def nodes_42_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_1 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_0 1 nodes_42_1 = true := by decide +kernel
def bk_42_1 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_1
set_option maxRecDepth 500000 in
lemma bk_42_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 1 xs.toFinset) bk_42_1 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_0_ok chk_42_1
def nodes_42_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_2 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_1 2 nodes_42_2 = true := by decide +kernel
def bk_42_2 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_2
set_option maxRecDepth 500000 in
lemma bk_42_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 2 xs.toFinset) bk_42_2 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_1_ok chk_42_2
def nodes_42_3 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_3 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_2 3 nodes_42_3 = true := by decide +kernel
def bk_42_3 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_3
set_option maxRecDepth 500000 in
lemma bk_42_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 3 xs.toFinset) bk_42_3 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_2_ok chk_42_3
def nodes_42_4 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_4 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_3 4 nodes_42_4 = true := by decide +kernel
def bk_42_4 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_4
set_option maxRecDepth 500000 in
lemma bk_42_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 4 xs.toFinset) bk_42_4 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_3_ok chk_42_4
def nodes_42_5 : List NodeSpec := [([0,1,2,3,7,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_5 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_4 5 nodes_42_5 = true := by decide +kernel
def bk_42_5 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_5
set_option maxRecDepth 500000 in
lemma bk_42_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 5 xs.toFinset) bk_42_5 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_4_ok chk_42_5
def nodes_42_6 : List NodeSpec := nodesWithIdentity [([5,0,1,2,6,3,4],[0,1,2,3,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_6 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_5 6 nodes_42_6 = true := by decide +kernel
def bk_42_6 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_6
set_option maxRecDepth 500000 in
lemma bk_42_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 6 xs.toFinset) bk_42_6 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_5_ok chk_42_6
def nodes_42_7 : List NodeSpec := nodesWithIdentity [([5,0,1,2,3,4],[7,9,0,10,11,2,3,4,1,8,12])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_7 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_6 7 nodes_42_7 = true := by decide +kernel
def bk_42_7 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_7
set_option maxRecDepth 500000 in
lemma bk_42_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 7 xs.toFinset) bk_42_7 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_6_ok chk_42_7
def nodes_42_8 : List NodeSpec := [([0,1,2,3,4],[9,7,10,2,4],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_8 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_7 8 nodes_42_8 = true := by decide +kernel
def bk_42_8 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_8
set_option maxRecDepth 500000 in
lemma bk_42_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 8 xs.toFinset) bk_42_8 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_7_ok chk_42_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_ok : forestRootCheck R_42 G_42 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,26,10),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_in : bucketContainsBT bk_42_8 R_42 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_42 : Lower R_42 G_42 9 := lower_of_forestBT root_42_ok bk_42_8_ok root_42_in

end Cofactor12058
def h23R : List Nat := varsOf 47
def h23G : Nat := 0xeaa8eaa8a880a880eaa8eaa8a880a880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 9 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(1,2),(0,1)]) (roots2 := Cofactor12058.R_42) (T2 := Cofactor12058.G_42) (by decide +kernel) Cofactor12058.low_42
def h24R : List Nat := varsOf 7
def h24G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 4 := carry_of (swaps := [(0,1),(1,2),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h25R : List Nat := varsOf 23
def h25G : Nat := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,6,22)]) (by decide +kernel) h24Bound
def h26R : List Nat := varsOf 39
def h26G : Nat := 0xe8e8e8e8e0e0e0e0e8e8e8e8e0e0e0e0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 5 := carry_of (swaps := [(4,5),(0,1),(1,2)]) (roots2 := h25R) (T2 := h25G) (by decide +kernel) h25Bound
def h27R : List Nat := varsOf 51
def h27G : Nat := 0xeeeeaaaaeeee8888eeeeaaaaeeee8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 5 := carry_of (swaps := [(3,4),(4,5),(3,4)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h28R : List Nat := varsOf 54
def h28G : Nat := 0xfcfcfcfcf0f0c0c0fcfcfcfcf0f0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 5 := carry_of (swaps := [(4,5),(3,4),(0,1),(1,2),(0,1)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h30R : List Nat := varsOf 39
def h30G : Nat := 0xa8a8a8a880808080a8a8a8a880808080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 5 := carry_of (swaps := [(3,4),(4,5)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h31R : List Nat := varsOf 53
def h31G : Nat := 0xfafaaaaaf0f0a0a0fafaaaaaf0f0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 4 := carry_of (swaps := [(3,4),(4,5),(1,2),(2,3),(3,4),(1,2)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h29R : List Nat := varsOf 55
def h29G : Nat := 0xe8e8a8a8e0e08080e8e8a8a8e0e08080
def h29Pos : List Nat := [21,22,37,22,21,51,35,51,35,22,37,54,21,22,35,7,51,37,21,37,54,7,23,54,7,7]
def h29Neg : List Nat := [20,20,38,18,5,19,3,49,33,6,5,50,19,19,34,3,50,36,17,33,52,5,19,38,6,4]
def h29Mask : Nat := fullMask 26
def h29Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x36fd5f5,0x6cb5f0),(0xcccccccccccccccccccccccccccccccc,0x3f1ebea,0x1c1fa6c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3febe1f,0x3b20617),(0xffff0000ffff0000ffff0000ffff0000,0xd53abb,0x5538ab),(0xffffffff00000000ffffffff00000000,0x9b4de4,0x9b4984)]
def h29Steps : List (Nat × Nat × Nat) := [(0,0,1),(2,0,1),(0,0,2),(0,1,2),(1,3,5),(0,5,7),(3,1,2),(2,1,7),(2,2,3),(2,2,5),(0,0,4),(2,0,4),(1,5,13),(2,2,6)]
def h29W : BT Decor := buildWiresBT 5 h29Base h29Steps
def h29AutoList : List (List (Nat × Nat)) := [[],[(4,5),(0,2)]]
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
def h29SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,4),some (subcubeFast 0 4,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 0 48,4),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4),some (subcubeFast 32 0,5),some (subcubeFast 32 4,4)]
def h29Slices : BT (Option (Nat × Nat)) := btOfList 4 h29SliceList
def h29Specs : List PoolSpec := [(0,[]),(1,[]),(7,[]),(2,[]),(6,[(0,0,1)]),(3,[]),(6,[]),(4,[]),(8,[]),(6,[(2,0,1)]),(9,[]),(8,[(0,0,2)]),(6,[(0,0,2)]),(2,[(0,0,4)]),(6,[(0,0,4)]),(3,[(0,0,4)]),(2,[(2,0,4)]),(6,[(2,0,4)]),(3,[(2,0,4)]),(5,[])]
def h29Pools : BT (Option BoundPool) := buildPoolsBT 5 h29W h29R h29Slices h29Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice9 : Slice h29R h29G (subcubeFast 32 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice8 : Slice h29R h29G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice7 : Slice h29R h29G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice6 : Slice h29R h29G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice5 : Slice h29R h29G (subcubeFast 0 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice4 : Slice h29R h29G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice3 : Slice h29R h29G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice2 : Slice h29R h29G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice1 : Slice h29R h29G (subcubeFast 0 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice0 : Slice h29R h29G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h29R h29G p.1 p.2) h29Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h29R h29G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h29Slice0) (forall_cons (fun _ h => by cases h; exact h29Slice1) (forall_cons (fun _ h => by cases h; exact h29Slice2) (forall_cons (fun _ h => by cases h; exact h29Slice3) (forall_cons (fun _ h => by cases h; exact h29Slice4) (forall_cons (fun _ h => by cases h; exact h29Slice5) (forall_cons (fun _ h => by cases h; exact h29Slice6) (forall_cons (fun _ h => by cases h; exact h29Slice7) (forall_cons (fun _ h => by cases h; exact h29Slice8) (forall_cons (fun _ h => by cases h; exact h29Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h29R h29G c) h29Pools := buildPoolsBT_sound h29SlicesOk
def h29Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G (4 - 1) xs.toFinset) h29Empty := trivial
def h29Block4_0 : List NodeSpec := nodesWithIdentity [([3,4,5,7,8],[]),([0,1,2,4,17],[])]
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
def h29Block5_0 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,7],[2,3]),([0,2,3,4,5,8],[0]),([0,2,3,4,5,11],[]),([0,1,2,4,5,13],[5]),([0,1,2,3,4,10],[5,6,7,8]),([0,1,2,3,4,14],[5,6]),([0,1,2,4,5,9],[6]),([0,1,2,4,6,13],[]),([0,1,2,3,4,18],[7,8]),([0,1,2,3,4,12],[])]
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
def h29Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8],[0]),([0,1,2,3,4,6],[0,1,2,3,5,6,7,8,9],[0,1]),([0,1,2,3,4,7],[0,1,2,3,5,6,7,8,10,11,12],[0,1]),([0,1,2,3,15],[0,2,8,10,13,14,15],[0]),([0,1,2,3,16],[0,2,7,8,16,17,18,19],[0,1])]
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
def h29Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,3,5,6,7,8],[0,1])]
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
lemma h29Bound : Lower h29R h29G 8 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 4,5,21),(VAR 5,3,35)]) (by decide +kernel) h29Bucket7Ok (by decide +kernel)
def h32R : List Nat := varsOf 11
def h32G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 4 := carry_of (swaps := [(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h33R : List Nat := varsOf 27
def h33G : Nat := 0xee88aa88ee88aa88ee88aa88ee88aa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 5 := carry_of (swaps := [(2,3)]) (roots2 := h25R) (T2 := h25G) (by decide +kernel) h25Bound
def h34R : List Nat := varsOf 41
def h34G : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 4 := carry_of (swaps := [(3,4),(4,5),(2,3),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h35R : List Nat := varsOf 43
def h35G : Nat := 0xee88ee88aa00aa00ee88ee88aa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,33,35)]) (by decide +kernel) h34Bound
def h36R : List Nat := varsOf 51
def h36G : Nat := 0xeeeeaaaaaaaa8888eeeeaaaaaaaa8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 6 := carry_of (swaps := [(4,5),(2,3),(3,4)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h37R : List Nat := varsOf 57
def h37G : Nat := 0xffaaaaaaaa00aa00ffaaaaaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(3,4),(1,2),(2,3)]) (roots2 := h25R) (T2 := h25G) (by decide +kernel) h25Bound
def h38R : List Nat := varsOf 58
def h38G : Nat := 0xffccffccff00cc00ffccffccff00cc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 5 := carry_of (swaps := [(4,5),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h39R : List Nat := varsOf 59
def h39G : Nat := 0xee88aa88aa008800ee88aa88aa008800
def h39Pos : List Nat := [25,58,25,58,11,41,58,25,58,35,11,25,41,41,11,41,35,35,27,43]
def h39Neg : List Nat := [24,56,26,50,3,40,42,9,26,3,10,17,9,42,9,33,34,33,19,42]
def h39Mask : Nat := fullMask 20
def h39Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffeb5,0x6da90),(0xcccccccccccccccccccccccccccccccc,0xf475a,0xd275c),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcfdff,0x875e7),(0xffff0000ffff0000ffff0000ffff0000,0x409cf,0x4090f),(0xffffffff00000000ffffffff00000000,0xbb36a,0xba06a)]
def h39Steps : List (Nat × Nat × Nat) := [(0,0,1),(0,1,4),(0,0,6),(2,0,6),(0,2,5),(2,2,5),(0,2,6),(2,2,6),(2,4,5),(2,4,9),(2,2,7)]
def h39W : BT Decor := buildWiresBT 4 h39Base h39Steps
def h39AutoList : List (List (Nat × Nat)) := [[],[(1,5)]]
def h39Autos : BT (List (Nat × Nat)) := btOfList 1 h39AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Pairs : goodPairs h39G h39Pos h39Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39BaseOk : ∀ x ∈ h39Base, faithful h39Pos h39Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39WOk : btAll (fun x => faithful h39Pos h39Neg x ∧ x.1 < 2^128) h39W := buildWiresBT_faithful h39BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h39G = h39G) h39Autos := btAll_ofList (autos_of (by decide +kernel))
def h39SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 8,6),some (subcubeFast 0 16,5),some (subcubeFast 0 18,4),some (subcubeFast 0 32,5),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4)]
def h39Slices : BT (Option (Nat × Nat)) := btOfList 3 h39SliceList
def h39Specs : List PoolSpec := [(0,[]),(1,[]),(2,[(0,0,1)]),(6,[(0,0,1)]),(3,[(0,1,4)]),(5,[]),(3,[]),(6,[]),(2,[]),(4,[]),(7,[]),(2,[(0,1,4)])]
def h39Pools : BT (Option BoundPool) := buildPoolsBT 4 h39W h39R h39Slices h39Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Slice7 : Slice h39R h39G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Slice6 : Slice h39R h39G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Slice5 : Slice h39R h39G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Slice4 : Slice h39R h39G (subcubeFast 0 18) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Slice3 : Slice h39R h39G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Slice2 : Slice h39R h39G (subcubeFast 0 8) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Slice1 : Slice h39R h39G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Slice0 : Slice h39R h39G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h39R h39G p.1 p.2) h39Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h39R h39G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h39Slice0) (forall_cons (fun _ h => by cases h; exact h39Slice1) (forall_cons (fun _ h => by cases h; exact h39Slice2) (forall_cons (fun _ h => by cases h; exact h39Slice3) (forall_cons (fun _ h => by cases h; exact h39Slice4) (forall_cons (fun _ h => by cases h; exact h39Slice5) (forall_cons (fun _ h => by cases h; exact h39Slice6) (forall_cons (fun _ h => by cases h; exact h39Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h39R h39G c) h39Pools := buildPoolsBT_sound h39SlicesOk
def h39Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h39G (4 - 1) xs.toFinset) h39Empty := trivial
def h39Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,14],[]),([0,1,3,4,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Test4_0 : checkNodesBT h39W h39G h39Mask h39Pools h39Autos h39Empty 4 h39Block4_0 = true := by decide +kernel
def h39Nodes4 : List NodeSpec := h39Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Check4 : checkNodesBT h39W h39G h39Mask h39Pools h39Autos h39Empty 4 h39Nodes4 = true := h39Test4_0
def h39Bucket4 : BT (List (List Nat)) := buildBucketsBT h39W h39Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h39G 4 xs.toFinset) h39Bucket4 := buildBucketsBT_sound (by decide) h39Pairs h39WOk h39PoolsOk h39AutosOk h39EmptyOk h39Check4
def h39Block5_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,6],[0,4,5]),([0,1,2,3,4,9],[5,6,7]),([0,1,2,3,4,10],[6,7]),([0,1,2,3,4,7],[6,7,8]),([0,1,2,3,4,13],[]),([0,1,2,3,4,8],[]),([0,1,2,3,4,11],[]),([0,1,2,3,4,12],[11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Test5_0 : checkNodesBT h39W h39G h39Mask h39Pools h39Autos h39Bucket4 5 h39Block5_0 = true := by decide +kernel
def h39Nodes5 : List NodeSpec := h39Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Check5 : checkNodesBT h39W h39G h39Mask h39Pools h39Autos h39Bucket4 5 h39Nodes5 = true := h39Test5_0
def h39Bucket5 : BT (List (List Nat)) := buildBucketsBT h39W h39Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h39G 5 xs.toFinset) h39Bucket5 := buildBucketsBT_sound (by decide) h39Pairs h39WOk h39PoolsOk h39AutosOk h39Bucket4Ok h39Check5
def h39Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,5,6,7,8,9,10],[0]),([0,1,2,3,4,6],[0,1,4,5,6,7,8,11],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Test6_0 : checkNodesBT h39W h39G h39Mask h39Pools h39Autos h39Bucket5 6 h39Block6_0 = true := by decide +kernel
def h39Nodes6 : List NodeSpec := h39Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Check6 : checkNodesBT h39W h39G h39Mask h39Pools h39Autos h39Bucket5 6 h39Nodes6 = true := h39Test6_0
def h39Bucket6 : BT (List (List Nat)) := buildBucketsBT h39W h39Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h39G 6 xs.toFinset) h39Bucket6 := buildBucketsBT_sound (by decide) h39Pairs h39WOk h39PoolsOk h39AutosOk h39Bucket5Ok h39Check6
def h39Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,5,6,7,8],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Test7_0 : checkNodesBT h39W h39G h39Mask h39Pools h39Autos h39Bucket6 7 h39Block7_0 = true := by decide +kernel
def h39Nodes7 : List NodeSpec := h39Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Check7 : checkNodesBT h39W h39G h39Mask h39Pools h39Autos h39Bucket6 7 h39Nodes7 = true := h39Test7_0
def h39Bucket7 : BT (List (List Nat)) := buildBucketsBT h39W h39Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h39G 7 xs.toFinset) h39Bucket7 := buildBucketsBT_sound (by decide) h39Pairs h39WOk h39PoolsOk h39AutosOk h39Bucket6Ok h39Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 8 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,9,11),(VAR 3,3,11),(VAR 4,9,25),(VAR 5,3,35)]) (by decide +kernel) h39Bucket7Ok (by decide +kernel)
def h40R : List Nat := varsOf 60
def h40G : Nat := 0xfff0fff0fff0f000fff0fff0fff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 5 := carry_of (swaps := [(4,5),(1,2),(2,3),(3,4),(2,3),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h41R : List Nat := varsOf 61
def h41G : Nat := 0xaaa0aaa0aaa0a000aaa0aaa0aaa0a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 6 := lift_of (z := 16) (o := 1) (essPairs := [(VAR 0,12,13),(VAR 4,5,21)]) (by decide +kernel) h16Bound
def h42R : List Nat := varsOf 30
def h42G : Nat := 0xccc0c000ccc0c000ccc0c000ccc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bound : Lower h42R h42G 5 := carry_of (swaps := [(3,4),(2,3),(1,2),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h43R : List Nat := varsOf 52
def h43G : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bound : Lower h43R h43G 4 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h44R : List Nat := varsOf 54
def h44G : Nat := 0xccccc0c0c0c00000ccccc0c0c0c00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bound : Lower h44R h44G 5 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h45R : List Nat := varsOf 60
def h45G : Nat := 0xfff0f000f0f00000fff0f000f0f00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bound : Lower h45R h45G 5 := carry_of (swaps := [(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h35R) (T2 := h35G) (by decide +kernel) h35Bound
def h46R : List Nat := varsOf 62
def h46G : Nat := 0xccc0c000c0c00000ccc0c000c0c00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 6 := lift_of (z := 0) (o := 10) (essPairs := [(VAR 1,20,22),(VAR 3,38,46)]) (by decide +kernel) h43Bound
def h47R : List Nat := varsOf 15
def h47G : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h47Bound : Lower h47R h47G 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h48R : List Nat := varsOf 29
def h48G : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bound : Lower h48R h48G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h5Bound
def h49R : List Nat := varsOf 31
def h49G : Nat := 0xeee8eaa8eee8eaa8eee8eaa8eee8eaa8
def h49Pos : List Nat := [5,14,3,3,14,5,7,3,14,9,13,22,21,19,26,26,21,25,26,22,19,25,7,22]
def h49Neg : List Nat := [4,12,1,2,10,1,6,6,6,1,12,6,20,17,24,10,17,17,18,18,18,24,1,20]
def h49Mask : Nat := fullMask 24
def h49Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7336ed,0x432224),(0xcccccccccccccccccccccccccccccccc,0xdce9de,0x1c89d8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc91d73,0x801dc3),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x26c712,0x20c412),(0xffff0000ffff0000ffff0000ffff0000,0xbff800,0xbf7000)]
def h49Steps : List (Nat × Nat × Nat) := [(1,0,2),(1,0,4),(2,1,2),(2,1,4),(1,2,3),(1,0,9),(3,0,9),(0,1,9),(2,1,9),(3,3,5),(0,1,10),(1,3,7)]
def h49W : BT Decor := buildWiresBT 5 h49Base h49Steps
def h49AutoList : List (List (Nat × Nat)) := [[],[(2,3)]]
def h49Autos : BT (List (Nat × Nat)) := btOfList 1 h49AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Pairs : goodPairs h49G h49Pos h49Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49BaseOk : ∀ x ∈ h49Base, faithful h49Pos h49Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49WOk : btAll (fun x => faithful h49Pos h49Neg x ∧ x.1 < 2^128) h49W := buildWiresBT_faithful h49BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h49G = h49G) h49Autos := btAll_ofList (autos_of (by decide +kernel))
def h49SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 16,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 4 0,5),some (subcubeFast 4 16,4),some (subcubeFast 8 0,5),some (subcubeFast 16 0,6)]
def h49Slices : BT (Option (Nat × Nat)) := btOfList 3 h49SliceList
def h49Specs : List PoolSpec := [(2,[]),(0,[]),(3,[]),(4,[]),(7,[(1,0,2)]),(0,[(1,0,2)]),(6,[]),(7,[]),(1,[]),(4,[(1,0,4)]),(0,[(1,0,4)]),(6,[(1,0,4)]),(5,[]),(2,[(2,1,2)]),(7,[(2,1,2)]),(2,[(2,1,4)]),(4,[(2,1,4)]),(6,[(2,1,4)]),(7,[(1,2,3)])]
def h49Pools : BT (Option BoundPool) := buildPoolsBT 5 h49W h49R h49Slices h49Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice7 : Slice h49R h49G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice6 : Slice h49R h49G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice5 : Slice h49R h49G (subcubeFast 4 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice4 : Slice h49R h49G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice3 : Slice h49R h49G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice2 : Slice h49R h49G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice1 : Slice h49R h49G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice0 : Slice h49R h49G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h49R h49G p.1 p.2) h49Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h49R h49G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h49Slice0) (forall_cons (fun _ h => by cases h; exact h49Slice1) (forall_cons (fun _ h => by cases h; exact h49Slice2) (forall_cons (fun _ h => by cases h; exact h49Slice3) (forall_cons (fun _ h => by cases h; exact h49Slice4) (forall_cons (fun _ h => by cases h; exact h49Slice5) (forall_cons (fun _ h => by cases h; exact h49Slice6) (forall_cons (fun _ h => by cases h; exact h49Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h49R h49G c) h49Pools := buildPoolsBT_sound h49SlicesOk
def h49Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G (4 - 1) xs.toFinset) h49Empty := trivial
def h49Block4_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test4_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Empty 4 h49Block4_0 = true := by decide +kernel
def h49Nodes4 : List NodeSpec := h49Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check4 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Empty 4 h49Nodes4 = true := h49Test4_0
def h49Bucket4 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 4 xs.toFinset) h49Bucket4 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49EmptyOk h49Check4
def h49Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,3,4,5,9],[0,6]),([0,1,2,3,4,10],[1,7,8]),([0,1,2,3,4,14],[]),([0,1,3,4,7,9],[1,6]),([0,1,2,3,4,16],[]),([0,1,2,3,4,13],[7,8]),([0,1,2,3,4,11],[7,8]),([0,1,2,3,4,12],[7,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_0 = true := by decide +kernel
def h49Nodes5 : List NodeSpec := h49Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check5 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Nodes5 = true := h49Test5_0
def h49Bucket5 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 5 xs.toFinset) h49Bucket5 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket4Ok h49Check5
def h49Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8],[0]),([0,1,2,3,6],[0,2,7,8,9,10,11,12],[0]),([0,1,2,3,4,7],[0,1,2,3,6,7,8,13,14],[0]),([0,1,2,3,8],[1,2,7,8,12,15,16,17],[0]),([0,1,2,3,4,9],[0,1,3,6,7,8,12,18],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_0 = true := by decide +kernel
def h49Nodes6 : List NodeSpec := h49Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check6 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Nodes6 = true := h49Test6_0
def h49Bucket6 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 6 xs.toFinset) h49Bucket6 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket5Ok h49Check6
def h49Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,6,7],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test7_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket6 7 h49Block7_0 = true := by decide +kernel
def h49Nodes7 : List NodeSpec := h49Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check7 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket6 7 h49Nodes7 = true := h49Test7_0
def h49Bucket7 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 7 xs.toFinset) h49Bucket7 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket6Ok h49Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bound : Lower h49R h49G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,6,22)]) (by decide +kernel) h49Bucket7Ok (by decide +kernel)
def h50R : List Nat := varsOf 45
def h50G : Nat := 0xfffafffafaf0faf0fffafffafaf0faf0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bound : Lower h50R h50G 5 := carry_of (swaps := [(4,5),(0,1),(1,2),(0,1)]) (roots2 := h48R) (T2 := h48G) (by decide +kernel) h48Bound
def h51R : List Nat := varsOf 47
def h51G : Nat := 0xeee8eee8eae0eae0eee8eee8eae0eae0
def h51Pos : List Nat := [5,6,11,35,6,5,42,9,42,35,35,14,14,37]
def h51Neg : List Nat := [4,4,10,33,2,1,34,1,10,3,34,12,10,33]
def h51Mask : Nat := fullMask 14
def h51Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,9901,8872),(0xcccccccccccccccccccccccccccccccc,8030,5972),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3833,2051),(0xff00ff00ff00ff00ff00ff00ff00ff00,6596,6404),(0xffffffff00000000ffffffff00000000,0x2748,9288)]
def h51Steps : List (Nat × Nat × Nat) := []
def h51W : BT Decor := buildWiresBT 3 h51Base h51Steps
def h51AutoList : List (List (Nat × Nat)) := [[]]
def h51Autos : BT (List (Nat × Nat)) := btOfList 1 h51AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Pairs : goodPairs h51G h51Pos h51Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51BaseOk : ∀ x ∈ h51Base, faithful h51Pos h51Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51WOk : btAll (fun x => faithful h51Pos h51Neg x ∧ x.1 < 2^128) h51W := buildWiresBT_faithful h51BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h51G = h51G) h51Autos := btAll_ofList (autos_of (by decide +kernel))
def h51SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 32,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5)]
def h51Slices : BT (Option (Nat × Nat)) := btOfList 2 h51SliceList
def h51Specs : List PoolSpec := [(0,[]),(2,[]),(3,[]),(1,[])]
def h51Pools : BT (Option BoundPool) := buildPoolsBT 2 h51W h51R h51Slices h51Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice3 : Slice h51R h51G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice2 : Slice h51R h51G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice1 : Slice h51R h51G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice0 : Slice h51R h51G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h51R h51G p.1 p.2) h51Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h51R h51G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h51Slice0) (forall_cons (fun _ h => by cases h; exact h51Slice1) (forall_cons (fun _ h => by cases h; exact h51Slice2) (forall_cons (fun _ h => by cases h; exact h51Slice3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h51R h51G c) h51Pools := buildPoolsBT_sound h51SlicesOk
def h51Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G (6 - 1) xs.toFinset) h51Empty := trivial
def h51Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 6 h51Block6_0 = true := by decide +kernel
def h51Nodes6 : List NodeSpec := h51Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check6 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 6 h51Nodes6 = true := h51Test6_0
def h51Bucket6 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 6 xs.toFinset) h51Bucket6 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51EmptyOk h51Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bound : Lower h51R h51G 7 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 3,1,9),(VAR 5,3,35)]) (by decide +kernel) h51Bucket6Ok (by decide +kernel)
def h52R : List Nat := varsOf 53
def h52G : Nat := 0xfffffafafafaaaaafffffafafafaaaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h52Bound : Lower h52R h52G 5 := carry_of (swaps := [(4,5),(3,4)]) (roots2 := h48R) (T2 := h48G) (by decide +kernel) h48Bound
def h53R : List Nat := varsOf 55
def h53G : Nat := 0xeeeeeaeaeaeaa8a8eeeeeaeaeaeaa8a8
def h53Pos : List Nat := [5,22,5,17,22,5,22,17,38,33,33,3,50,38,3,50,38,7,50,21,19,35,50,3,7,38,17,7,3,21,17,5,33,22,37,19,38,17,49,21,37,22,22,22,49,37,22]
def h53Neg : List Nat := [4,20,6,16,18,1,6,1,6,1,32,2,48,36,1,18,34,6,34,1,18,34,52,0,1,32,18,2,6,20,20,20,52,2,36,1,52,0,1,16,1,16,4,0,48,4,52]
def h53Mask : Nat := fullMask 47
def h53Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x31edfdba4ead,0x148010842a0),(0xcccccccccccccccccccccccccccccccc,0x4e1a1bf7f952,0x21c378954),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x6f96ab0b2177,0x6415f0422147),(0xffff0000ffff0000ffff0000ffff0000,0x5eea645c90da,0x5291e450901a),(0xffffffff00000000ffffffff00000000,0x31550265b700,0x501502653400)]
def h53Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(1,0,2),(2,0,2),(1,0,3),(1,1,2),(2,1,2),(0,1,3),(2,1,3),(0,2,3),(1,2,3),(0,0,17),(1,0,17),(2,0,17),(3,0,17),(0,1,17),(1,0,22),(3,0,22),(2,2,3),(1,2,4),(2,2,4),(1,2,5),(1,3,4),(2,3,4),(1,3,28),(3,3,28),(1,4,22),(1,4,5),(1,5,22),(1,3,35),(3,3,35),(1,1,17),(2,1,17),(3,1,17),(0,1,28),(2,1,28),(1,4,17),(3,4,17),(2,1,31),(3,5,17),(2,1,46),(2,1,32),(1,0,13),(1,3,13),(3,4,6),(1,4,13),(3,4,13),(2,6,13),(0,6,17),(1,13,55),(2,6,17),(3,2,6),(3,0,50),(3,2,50),(1,4,50),(3,4,50),(1,0,39),(1,2,39),(1,4,39),(2,4,39),(3,4,39),(2,6,39),(1,2,54),(1,3,58),(1,3,69),(3,3,69),(3,1,71),(3,4,71),(1,0,74),(2,1,74),(3,7,17),(3,3,49),(1,8,39),(1,3,42),(1,4,45),(1,4,9),(3,4,9),(0,9,11),(3,2,11),(0,3,9),(3,3,9),(1,3,85),(0,4,19),(1,4,19),(3,4,19),(3,3,91),(1,9,15),(2,9,15),(3,3,64),(1,2,87),(1,4,87),(1,4,18),(1,4,21),(0,1,29),(0,1,82),(0,29,82),(0,9,29),(3,9,29),(3,0,43),(0,1,43),(3,3,43),(3,2,29),(0,1,90),(0,1,108),(1,4,88),(3,4,88),(0,1,111),(3,10,29),(2,12,108),(1,4,95),(3,4,95),(0,12,29),(1,4,40),(3,13,29),(3,18,19),(1,4,16),(1,4,47),(3,4,23),(3,22,38)]
def h53W : BT Decor := buildWiresBT 7 h53Base h53Steps
def h53AutoList : List (List (Nat × Nat)) := [[],[(4,5)],[(2,4)],[(2,5)],[(4,5),(2,4)],[(4,5),(2,5)]]
def h53Autos : BT (List (Nat × Nat)) := btOfList 3 h53AutoList
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
def h53SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 4 0,6),some (subcubeFast 16 0,6),some (subcubeFast 32 0,6)]
def h53Slices : BT (Option (Nat × Nat)) := btOfList 3 h53SliceList
def h53Specs : List PoolSpec := [(1,[]),(0,[]),(3,[(0,0,1)]),(4,[(0,0,1)]),(5,[(0,0,1)]),(2,[]),(0,[(1,2,5)]),(4,[]),(3,[]),(0,[(1,4,5)]),(3,[(0,0,1),(1,4,5)]),(5,[(1,2,3)]),(3,[(0,0,1),(1,3,28)]),(3,[(0,0,1),(3,5,17)]),(4,[(0,0,1),(1,2,5)]),(5,[(0,0,1),(1,2,5)]),(5,[]),(3,[(1,0,1)]),(4,[(1,0,1)]),(5,[(1,0,1)]),(1,[(2,1,2)]),(3,[(1,0,1),(3,4,6)]),(3,[(1,0,1),(0,6,17)]),(3,[(1,0,1),(2,6,17)]),(1,[(3,2,6)]),(4,[(1,0,1),(3,2,6)]),(5,[(1,0,1),(3,2,6)]),(4,[(1,0,1),(2,6,17)]),(3,[(2,0,1)]),(4,[(2,0,1)]),(5,[(2,0,1)]),(3,[(3,0,1)]),(4,[(3,0,1)]),(5,[(3,0,1)]),(0,[(1,0,13)]),(1,[(2,1,28)]),(4,[(1,0,2)]),(5,[(1,0,2)]),(1,[(0,1,28)]),(0,[(1,0,2)]),(4,[(1,0,2),(3,4,9)]),(4,[(1,0,2),(0,9,29)]),(4,[(1,0,17),(3,4,19)]),(3,[(1,0,17)]),(5,[(1,0,3),(3,2,11)]),(4,[(1,0,17)]),(3,[(3,3,9)]),(5,[(1,0,2),(3,3,9)]),(4,[(2,0,2)]),(5,[(2,0,2)]),(3,[(1,0,3)]),(4,[(3,2,11)]),(4,[(1,1,2)]),(5,[(1,1,2)]),(3,[(2,1,17)]),(4,[(2,1,2)]),(5,[(2,1,2)]),(3,[(1,0,13)]),(4,[(2,1,2),(1,4,13)]),(4,[(2,1,2),(1,4,50)]),(4,[(2,1,2),(3,13,29)]),(3,[(1,3,13)]),(5,[(2,1,2),(1,3,13)]),(4,[(2,1,17)]),(3,[(0,1,17)]),(3,[(0,0,17)]),(3,[(0,0,17),(1,4,18)]),(3,[(1,0,17),(3,4,19)]),(3,[(2,0,17)]),(3,[(3,0,17)]),(4,[(3,0,17)]),(4,[(0,1,17)]),(3,[(0,1,17),(1,1,17)]),(3,[(1,1,17)]),(3,[(2,1,17),(1,4,39)]),(3,[(3,1,17)]),(3,[(3,1,17),(1,4,40)]),(4,[(1,2,4)]),(3,[(1,3,4)]),(3,[(1,4,17)]),(4,[(1,4,17)]),(3,[(3,4,17)]),(4,[(3,4,17)])]
def h53Pools : BT (Option BoundPool) := buildPoolsBT 7 h53W h53R h53Slices h53Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice5 : Slice h53R h53G (subcubeFast 32 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice4 : Slice h53R h53G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice3 : Slice h53R h53G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice2 : Slice h53R h53G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice1 : Slice h53R h53G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice0 : Slice h53R h53G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h52Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h53R h53G p.1 p.2) h53Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h53R h53G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h53Slice0) (forall_cons (fun _ h => by cases h; exact h53Slice1) (forall_cons (fun _ h => by cases h; exact h53Slice2) (forall_cons (fun _ h => by cases h; exact h53Slice3) (forall_cons (fun _ h => by cases h; exact h53Slice4) (forall_cons (fun _ h => by cases h; exact h53Slice5) (fun _ h => (List.not_mem_nil h).elim)))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h53R h53G c) h53Pools := buildPoolsBT_sound h53SlicesOk
def h53Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G (3 - 1) xs.toFinset) h53Empty := trivial
def h53Block3_0 : List NodeSpec := nodesWithIdentity [([0,17,29,101],[]),([0,2,35,102],[]),([4,17,56,84],[]),([0,17,56,122],[]),([0,17,79,122],[]),([0,17,35,122],[]),([0,17,73,122],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test3_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Empty 3 h53Block3_0 = true := by decide +kernel
def h53Nodes3 : List NodeSpec := h53Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check3 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Empty 3 h53Nodes3 = true := h53Test3_0
def h53Bucket3 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 3 xs.toFinset) h53Bucket3 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53EmptyOk h53Check3
def h53Block4_0 : List NodeSpec := nodesWithIdentity [([0,3,4,22,28],[]),([0,2,3,22,34],[]),([0,2,3,4,35],[]),([0,3,4,28,35],[]),([0,3,4,13,55],[]),([0,2,3,6,65],[]),([0,2,3,4,68],[]),([0,1,2,3,74],[]),([0,2,3,8,65],[]),([0,1,2,3,81],[]),([0,1,2,3,91],[]),([0,1,4,17,94],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test4_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket3 4 h53Block4_0 = true := by decide +kernel
def h53Block4_1 : List NodeSpec := nodesWithIdentity [([0,4,14,17,41],[]),([0,1,17,29,82],[7]),([0,1,4,17,103],[7]),([0,3,4,17,101],[]),([0,2,3,4,109],[]),([0,3,4,27,35],[]),([0,3,4,35,85],[]),([0,2,3,35,89],[]),([0,2,3,35,91],[]),([0,2,3,73,89],[]),([0,2,3,73,91],[]),([0,1,3,85,89],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test4_1 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket3 4 h53Block4_1 = true := by decide +kernel
def h53Block4_2 : List NodeSpec := nodesWithIdentity [([0,2,4,35,86],[]),([0,2,3,4,113],[]),([0,1,3,4,115],[]),([0,4,13,17,100],[]),([0,1,17,29,53],[7]),([0,1,4,17,120],[7]),([0,2,4,22,50],[]),([0,2,3,22,65],[]),([0,1,3,64,66],[]),([1,2,3,4,121],[]),([0,4,16,17,56],[]),([0,4,16,17,79],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test4_2 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket3 4 h53Block4_2 = true := by decide +kernel
def h53Block4_3 : List NodeSpec := nodesWithIdentity [([0,4,16,17,35],[]),([0,4,16,17,73],[]),([0,1,2,3,123],[]),([0,1,21,26,29],[]),([0,1,2,3,124],[]),([0,1,22,26,29],[]),([0,2,3,4,125],[]),([0,2,3,40,65],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test4_3 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket3 4 h53Block4_3 = true := by decide +kernel
def h53Nodes4 : List NodeSpec := h53Block4_0 ++ h53Block4_1 ++ h53Block4_2 ++ h53Block4_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check4 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket3 4 h53Nodes4 = true := by
  unfold h53Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h53Test4_0,h53Test4_1⟩,h53Test4_2⟩,h53Test4_3⟩
def h53Bucket4 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 4 xs.toFinset) h53Bucket4 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53Bucket3Ok h53Check4
def h53Block5_0 : List NodeSpec := [([0,2,3,4,5,22],[],[0,2]),([0,1,3,4,17,28],[6,7],[0]),([0,1,2,3,17,34],[9,10],[0]),([0,1,2,3,4,31],[12],[0]),([0,1,2,3,4,46],[7,8,13],[0]),([0,1,3,4,28,31],[6,14],[0]),([0,1,3,4,28,32],[],[0]),([0,1,2,3,4,32],[0],[0]),([0,3,4,6,13,17],[],[0]),([0,2,3,4,6,50],[],[0]),([0,2,3,4,6,39],[],[0]),([0,2,3,4,13,54],[8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_0 = true := by decide +kernel
def h53Block5_1 : List NodeSpec := [([0,1,3,4,17,58],[7],[0]),([0,1,2,3,17,51],[21],[0]),([0,1,2,3,4,55],[0,7,8,22],[0,2]),([0,1,2,3,4,57],[23],[0]),([0,1,3,4,58,70],[],[0]),([0,1,3,4,57,58],[27],[0]),([0,1,2,3,4,70],[1],[0]),([0,2,3,4,7,22],[],[0]),([0,1,3,4,17,69],[7],[0]),([0,1,2,3,4,71],[1,16],[0]),([0,1,2,3,4,77],[],[0]),([0,1,3,4,25,69],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_1 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_1 = true := by decide +kernel
def h53Block5_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,72],[]),([2,3,4,8,13,49],[34]),([0,3,4,8,13,17],[]),([0,2,3,4,8,50],[]),([0,2,3,4,8,39],[0]),([0,1,3,4,17,42],[7]),([0,1,2,3,4,24],[]),([0,1,2,3,4,45],[16]),([1,2,3,4,42,49],[8]),([0,2,3,4,41,42],[8]),([0,1,3,4,25,42],[]),([0,1,2,3,4,80],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_2 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_2 = true := by decide +kernel
def h53Block5_3 : List NodeSpec := nodesWithIdentity [([0,1,4,9,11,17],[7,8]),([0,1,3,4,9,85],[8]),([0,1,2,3,4,19],[1,16]),([0,1,4,9,15,17],[7,8]),([0,1,3,4,9,64],[0]),([0,1,2,4,15,87],[1]),([0,1,2,3,4,37],[0]),([0,1,2,3,4,93],[1]),([0,1,2,3,4,94],[]),([0,2,3,4,14,41],[]),([0,1,3,4,17,41],[6,7]),([0,1,2,3,4,36],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_3 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_3 = true := by decide +kernel
def h53Block5_4 : List NodeSpec := [([1,2,3,4,9,49],[8],[0]),([1,3,4,9,17,18],[],[0]),([1,3,4,9,17,21],[],[0]),([0,1,4,9,17,29],[],[0]),([0,1,4,9,17,87],[7],[0]),([0,1,3,4,17,82],[7],[0]),([0,1,3,4,17,83],[7,40],[0]),([0,1,3,4,9,43],[0],[0]),([0,1,3,4,9,44],[],[0]),([0,1,2,3,4,103],[0,7,16,41],[0,1]),([0,1,2,3,4,90],[1],[0,1,3]),([0,1,2,3,4,92],[42],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_4 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_4 = true := by decide +kernel
def h53Block5_5 : List NodeSpec := [([0,1,2,3,4,104],[],[0]),([0,1,2,3,4,21],[],[0]),([1,2,3,4,19,21],[8],[0]),([0,2,3,4,35],[],[0,1,2,4]),([0,1,2,3,4,35],[],[0]),([0,2,3,4,19,35],[1],[0,2]),([0,2,3,4,19,73],[],[0]),([0,1,2,3,4,85],[],[0]),([0,1,3,4,19,85],[8,44],[0]),([0,1,2,3,19,89],[],[0,2]),([0,1,2,3,91],[],[0]),([0,1,2,3,4,91],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_5 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_5 = true := by decide +kernel
def h53Block5_6 : List NodeSpec := [([0,1,2,3,19,91],[16],[0]),([1,2,3,4,9,21],[8],[0]),([0,2,3,4,9,35],[],[0,2]),([0,1,2,3,9,91],[],[0]),([0,1,2,3,4,48],[],[0]),([0,1,2,3,4,97],[],[0,1]),([0,1,3,4,10,108],[],[0,3]),([0,1,2,4,29,88],[16],[0]),([0,1,2,3,4,111],[1],[0,3]),([0,1,2,3,4,114],[],[0]),([0,1,2,3,4,112],[],[0]),([0,2,3,4,12,100],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_6 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_6 = true := by decide +kernel
def h53Block5_7 : List NodeSpec := [([0,1,3,4,12,108],[],[0]),([0,1,2,4,29,95],[16],[0]),([0,1,2,3,4,118],[],[0]),([0,1,2,3,4,117],[8],[0]),([0,1,2,3,4,64],[],[0]),([0,1,2,3,4,39],[16],[0,3]),([0,1,2,4,30,95],[],[0]),([0,1,2,3,4,116],[],[0]),([0,1,3,4,17,49],[7],[0]),([0,1,2,3,4,78],[],[0]),([0,2,3,4,13,41],[8],[0]),([0,1,4,13,15,17],[7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_7 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_7 = true := by decide +kernel
def h53Block5_8 : List NodeSpec := [([0,1,3,4,13,64],[8],[0]),([0,3,4,13,17,22],[],[0]),([0,3,4,13,17,40],[],[0]),([0,1,4,13,17,29],[],[0]),([0,1,4,13,17,50],[7],[0]),([0,1,3,4,17,52],[7,58],[0]),([0,1,3,4,17,53],[7],[0]),([0,1,3,4,13,43],[1],[0]),([0,1,3,4,13,44],[],[0]),([0,2,3,4,13,100],[8],[0,1]),([0,1,2,3,4,110],[],[0]),([0,1,2,3,4,61],[8,59],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_8 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_8 = true := by decide +kernel
def h53Block5_9 : List NodeSpec := [([0,1,2,3,4,67],[],[0,2,3]),([0,1,2,3,4,120],[1,7,16,60],[0,1]),([0,1,2,3,4,59],[],[0]),([0,1,2,4,39,50],[8,62],[0]),([0,1,2,3,4,62],[],[0,2]),([0,1,2,3,4,63],[],[0]),([0,1,2,3,4,22],[],[0]),([0,2,3,4,22,39],[8],[0,2]),([0,1,2,3,65],[],[0]),([0,1,2,3,4,65],[],[0]),([0,1,2,3,39,65],[16],[0]),([0,1,2,3,39,66],[],[0,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_9 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_9 = true := by decide +kernel
def h53Block5_10 : List NodeSpec := nodesWithIdentity [([0,2,3,4,13,22],[8,64]),([0,1,2,3,13,65],[]),([1,2,3,4,18,19],[]),([0,2,3,4,17,56],[]),([0,2,3,4,17,79],[]),([0,1,2,3,17,98],[66]),([0,2,3,4,17,35],[]),([0,2,3,4,17,73],[]),([0,1,3,4,17,85],[8]),([0,1,2,3,17,91],[67]),([1,2,3,4,20,21],[]),([0,1,3,4,17,96],[8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_10 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_10 = true := by decide +kernel
def h53Block5_11 : List NodeSpec := [([0,1,2,3,4,47],[7,8,16],[0]),([0,1,3,4,21,26],[16],[0]),([0,1,2,3,4,99],[],[0]),([0,1,2,3,4,23],[7,8,16],[0]),([0,1,3,4,22,26],[16],[0,5]),([0,1,2,3,4,33],[],[0]),([0,2,3,4,22,38],[72],[0]),([0,1,3,4,17,60],[8],[0]),([0,2,3,4,39,40],[],[0]),([0,1,3,4,17,64],[8],[0,2]),([0,1,2,3,17,65],[74],[0]),([0,1,2,3,17,119],[76],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_11 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_11 = true := by decide +kernel
def h53Block5_12 : List NodeSpec := [([0,1,17,26,29],[7,8,16,77,78],[0,1,2,3]),([0,1,4,17,26,107],[7,8],[0]),([0,1,2,3,4,105],[],[0]),([0,1,2,3,4,106],[],[0]),([0,1,2,3,4,108],[],[0]),([0,1,3,4,43,108],[8],[0]),([0,1,3,4,17,108],[8],[0]),([0,1,2,3,4,75],[],[0]),([0,1,2,3,4,76],[],[0,3]),([0,1,2,3,4,43],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_12 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_12 = true := by decide +kernel
def h53Nodes5 : List NodeSpec := h53Block5_0 ++ h53Block5_1 ++ h53Block5_2 ++ h53Block5_3 ++ h53Block5_4 ++ h53Block5_5 ++ h53Block5_6 ++ h53Block5_7 ++ h53Block5_8 ++ h53Block5_9 ++ h53Block5_10 ++ h53Block5_11 ++ h53Block5_12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check5 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Nodes5 = true := by
  unfold h53Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h53Test5_0,h53Test5_1⟩,h53Test5_2⟩,h53Test5_3⟩,h53Test5_4⟩,h53Test5_5⟩,h53Test5_6⟩,h53Test5_7⟩,h53Test5_8⟩,h53Test5_9⟩,h53Test5_10⟩,h53Test5_11⟩,h53Test5_12⟩
def h53Bucket5 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 5 xs.toFinset) h53Bucket5 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53Bucket4Ok h53Check5
def h53Block6_0 : List NodeSpec := [([0,1,2,3,4,5,17],[0,1,2,7,8,11],[0,2]),([0,1,3,4,28],[0,2,5,6,14,15],[0,1,3]),([0,1,2,3,4,28],[0,2,5,6,7,8,14,15,16],[0,1]),([0,2,3,4,6,13],[0,1,5,8,17,20],[0,1]),([0,1,2,3,4,6,17],[1,7,8,11,17],[0,2]),([0,1,3,4,58],[1,5,17,24,25,26],[0,1,3]),([0,1,2,3,4,58],[0,1,5,7,8,16,17,24,25,26],[0,1]),([0,1,2,3,4,7,17],[0,1,7,8,28],[0,2]),([0,1,2,3,4,69],[0,1,7,8,16],[0,1]),([0,2,3,4,8,13],[0,1,5,8,20,31],[0,1]),([0,1,2,3,4,8,17],[1,5,7,8,31],[0,2]),([0,1,2,3,4,42],[5,6,7,16,35],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_0 = true := by decide +kernel
def h53Block6_1 : List NodeSpec := [([0,1,2,3,4,9,11],[7,8],[0,2]),([0,1,2,3,4,9,15],[7,8],[0]),([0,1,2,3,4,41],[0,2,5,6,7,8,16,38],[0,1]),([0,1,2,3,4,9,41],[0,1,5,8,38],[0]),([0,1,2,3,4,9,42],[1,5,35],[0]),([0,1,3,4,9,17],[0,7,8,36,39],[0]),([0,1,2,3,4,9,29],[7,8,16,36],[0,1,3,4]),([0,1,2,3,4,19],[1,16,43,45],[0,1,2,4]),([0,1,2,3,4,9,19],[5,7,37,45],[0,2]),([0,1,2,3,4,87],[0,1,7,8,16,36,46,47],[0,1,2]),([0,1,2,3,4,9,87],[0,7,8,36],[0,2]),([0,1,2,3,4,10,29],[0,7,8,16,48],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_1 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_1 = true := by decide +kernel
def h53Block6_2 : List NodeSpec := [([0,1,2,3,4,88],[0,1,5,7,8,16,50,51],[0]),([0,1,2,3,4,12,29],[1,7,8,16,52],[0,1]),([0,1,2,3,4,95],[0,1,5,7,8,16,54],[0]),([0,1,2,3,4,49],[0,1,5,7,8,16,20,34,57],[0,1,2,5]),([0,1,2,3,4,13,49],[0,1,5,8,34],[0]),([0,1,2,3,4,13,42],[0,5,6],[0]),([0,1,2,3,4,13,15],[7,8],[0,2]),([0,1,3,4,13,17],[1,7,8,20,55],[0,2]),([0,1,2,3,4,13,29],[1,7,8,16,55],[0,1,3,4]),([0,1,2,3,4,50],[0,1,7,8,16,55,61,62],[0,1,2]),([0,1,2,3,4,13,50],[1,7,8,55],[0]),([0,1,2,3,4,39],[0,16,54,63],[0,1,2,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_2 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_2 = true := by decide +kernel
def h53Block6_3 : List NodeSpec := [([0,1,2,3,4,13,39],[7,56,63],[0]),([0,1,2,3,4,17,18],[0,7,8,11,65],[0,2]),([0,1,2,3,4,17,19],[0,11,43],[0,2]),([0,1,2,3,4,17,20],[0,68],[0,2]),([0,1,2,3,4,21],[1,7,8,16,69,70],[0,2,3]),([0,1,2,3,4,17,21],[0,7,8,69],[0,2]),([0,1,2,3,4,22],[0,7,8,16,64,71],[0,2,3]),([0,1,2,3,4,17,22],[1,7,8,64],[0,2]),([0,1,2,3,4,17,38],[1,73],[0,2]),([0,1,2,3,4,17,39],[1,11,54],[0,2]),([0,1,2,3,4,17,40],[1,7,8,11,75],[0,2]),([0,1,3,4,17,26],[7,8,11,16,77],[0,1,2,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_3 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_3 = true := by decide +kernel
def h53Block6_4 : List NodeSpec := [([0,1,2,3,4,43],[0,1,11,79,80],[0,2,3]),([0,1,2,3,4,17,43],[11,16,79],[0,2,3]),([0,1,2,3,4,44],[0,1,7,8,11,81,82],[0,2,3]),([0,1,2,3,4,17,44],[7,8,11,16,81],[0,1,3,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_4 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_4 = true := by decide +kernel
def h53Nodes6 : List NodeSpec := h53Block6_0 ++ h53Block6_1 ++ h53Block6_2 ++ h53Block6_3 ++ h53Block6_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check6 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Nodes6 = true := by
  unfold h53Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h53Test6_0,h53Test6_1⟩,h53Test6_2⟩,h53Test6_3⟩,h53Test6_4⟩
def h53Bucket6 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 6 xs.toFinset) h53Bucket6 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53Bucket5Ok h53Check6
def h53Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,7,8,16],[0,1,2,3]),([0,1,2,3,4,6],[0,1,5,7,8,16,17,18,19],[0,1,2,3]),([0,1,2,3,4,7],[0,1,7,8,16,28,29,30],[0,1,2,3]),([0,1,2,3,4,8],[0,1,5,7,8,16,31,32,33],[0,1,2,3]),([0,1,2,3,4,9],[0,1,5,7,8,16,36,37],[0,1]),([0,1,2,3,4,10],[0,1,5,7,8,16,48,49],[0,1]),([0,1,2,3,4,12],[0,1,5,7,8,16,52,53],[0,1]),([0,1,2,3,4,13],[0,1,5,7,8,16,55,56],[0,1,2,5]),([0,1,2,3,4,17],[0,1,7,8,11,16],[0,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test7_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket6 7 h53Block7_0 = true := by decide +kernel
def h53Nodes7 : List NodeSpec := h53Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check7 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket6 7 h53Nodes7 = true := h53Test7_0
def h53Bucket7 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 7 xs.toFinset) h53Bucket7 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53Bucket6Ok h53Check7
def h53Block8_0 : List NodeSpec := [([0,1,2,3,4],[7,8,16],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test8_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket7 8 h53Block8_0 = true := by decide +kernel
def h53Nodes8 : List NodeSpec := h53Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check8 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket7 8 h53Nodes8 = true := h53Test8_0
def h53Bucket8 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 8 xs.toFinset) h53Bucket8 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53Bucket7Ok h53Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bound : Lower h53R h53G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h53Bucket8Ok (by decide +kernel)
namespace Cofactor12168
def G_0 : Nat := 0xffffff00ff000000ffffff00ff000000
def R_0 : List Nat := varsOf 56
def pos_0 : List Nat := [24,24,40,40,48,48,24,40,48]
def neg_0 : List Nat := [16,8,32,8,32,16,32,16,8]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
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
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_11 : Nat := 0xffc0fc00ffc0fc00ffc0fc00ffc0fc00
def R_11 : List Nat := varsOf 30
def pos_11 : List Nat := [10,10,12,12,14,22,22,22,24,24,26,28,10,10,10,12,12,12,22,24,24,24]
def neg_11 : List Nat := [8,2,8,4,6,20,18,6,16,8,18,20,6,18,20,6,18,20,8,6,18,20]
def fmask_11 : Nat := fullMask 22
def base_11 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x474f3,0x19b4d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x788fc,0x2ad8b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3bff1f,0x40205),(0xffff0000ffff0000ffff0000ffff0000,0x3c0fe0,0x336d60)]
def steps_11 : List (Nat × Nat × Nat) := [(3,0,2),(2,0,1),(2,0,2),(1,0,2),(1,0,1),(0,0,2),(0,0,1),(0,1,7),(3,0,1),(1,5,3),(1,9,1),(3,5,3),(3,1,7),(3,9,1),(3,10,8)]
def W_11 : BT Decor := buildWiresBT 5 base_11 steps_11
def autosL_11 : List (List (Nat × Nat)) := [[],[(2,4)],[(1,2)],[(1,4),(1,2)],[(1,2),(1,4)],[(1,4)]]
def autos_11 : BT (List (Nat × Nat)) := btOfList 3 autosL_11
def slicesL_11 : List (Option (Nat × Nat)) := []
def slices_11 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_11
def ps_11 : List PoolSpec := []
def P_11 : BT (Option BoundPool) := buildPoolsBT 1 W_11 R_11 slices_11 ps_11
lemma gp_11 : goodPairs G_11 pos_11 neg_11 := goodPairs_of (by decide +kernel)
lemma base_11_ok : ∀ x ∈ base_11, faithful pos_11 neg_11 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_11_ok : btAll (fun x => faithful pos_11 neg_11 x ∧ x.1 < 2^128) W_11 := buildWiresBT_faithful base_11_ok
set_option maxRecDepth 500000 in
lemma autos_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_11 = G_11) autos_11 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_11_ok : btAll (fun o => ∀ p, o = some p → Slice R_11 G_11 p.1 p.2) slices_11 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_11 G_11 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_11_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_11 G_11 c) P_11 := buildPoolsBT_sound slices_11_ok
def bk_11_init : BT (List (List Nat)) := BT.empty
lemma bk_11_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 (0 - 1) xs.toFinset) bk_11_init := trivial
def nodes_11_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_0 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_init 0 nodes_11_0 = true := by decide +kernel
def bk_11_0 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_0
set_option maxRecDepth 500000 in
lemma bk_11_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 0 xs.toFinset) bk_11_0 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_init_ok chk_11_0
def nodes_11_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_1 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_0 1 nodes_11_1 = true := by decide +kernel
def bk_11_1 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_1
set_option maxRecDepth 500000 in
lemma bk_11_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 1 xs.toFinset) bk_11_1 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_0_ok chk_11_1
def nodes_11_2 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_2 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_1 2 nodes_11_2 = true := by decide +kernel
def bk_11_2 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_2
set_option maxRecDepth 500000 in
lemma bk_11_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 2 xs.toFinset) bk_11_2 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_1_ok chk_11_2
def nodes_11_3 : List NodeSpec := [([6,4,1,3],[],[]),([0,11,2,3],[],[]),([5,12,2,3],[],[0]),([0,1,2,13],[],[]),([0,14,2,3],[],[]),([0,1,15,2],[],[]),([16,0,2,3],[],[]),([17,0,2,3],[],[]),([10,8,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_3 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_2 3 nodes_11_3 = true := by decide +kernel
def bk_11_3 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_3
set_option maxRecDepth 500000 in
lemma bk_11_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 3 xs.toFinset) bk_11_3 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_2_ok chk_11_3
def nodes_11_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([6,0,1,2,3],[],[0]),([0,1,2,7,3],[],[0,1]),([0,1,8,2,3],[],[0]),([9,0,1,2,3],[],[0,1]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_4 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_3 4 nodes_11_4 = true := by decide +kernel
def bk_11_4 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_4
set_option maxRecDepth 500000 in
lemma bk_11_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 4 xs.toFinset) bk_11_4 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_3_ok chk_11_4
def nodes_11_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_5 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_4 5 nodes_11_5 = true := by decide +kernel
def bk_11_5 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_5
set_option maxRecDepth 500000 in
lemma bk_11_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 5 xs.toFinset) bk_11_5 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_4_ok chk_11_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck R_11 G_11 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 4,22,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT bk_11_5 R_11 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_11 : Lower R_11 G_11 6 := lower_of_forestBT root_11_ok bk_11_5_ok root_11_in

def G_12 : Nat := 0xffffff00ff00f000ffffff00ff00f000
def R_12 : List Nat := varsOf 60
lemma low_12_ok : liftCheck 4 0 R_12 G_12 R_0 G_0 [(VAR 2,12,8)] = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 5 := lift_of low_12_ok low_0

def G_30 : Nat := 0xffffff00ff00cc00ffffff00ff00cc00
def R_30 : List Nat := varsOf 58
lemma low_30_ok : carryOK [(1,2)] R_30 G_30 R_12 G_12 = true := by decide +kernel
lemma low_30 : Lower R_30 G_30 5 := carry_of low_30_ok low_12

def G_37 : Nat := 0xffffff00ffc0fc00ffffff00ffc0fc00
def R_37 : List Nat := varsOf 62
def pos_37 : List Nat := [10,10,12,12,14,22,22,22,24,24,26,28,40,40,42,44,46,48,48,50,50,52,52,54,10,10,10,12,12,12,22,22,24,24,24,40,40,40,48,48,48,48]
def neg_37 : List Nat := [8,2,8,4,6,20,18,6,16,8,18,20,32,8,34,36,38,32,16,34,18,36,20,38,18,20,38,18,20,38,8,38,18,20,38,18,20,38,8,18,20,38]
def fmask_37 : Nat := fullMask 42
def base_37 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xc79944f3,0x2adad9944d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf8e188fc,0x336b6e188b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f3f01ff1f,0x4040002205),(0xffff0000ffff0000ffff0000ffff0000,0x3c7c0fe0fe0,0x19b1b540d60),(0xffffffff00000000ffffffff00000000,0x3f800fff000,0x224a4abd000)]
def steps_37 : List (Nat × Nat × Nat) := [(3,2,3),(2,2,3),(1,2,3),(1,0,3),(0,2,3),(3,0,3),(3,0,2),(1,0,2),(1,5,0),(2,7,4),(0,11,3),(3,0,7),(0,0,7),(3,10,2),(1,9,4),(2,0,9),(1,0,9),(0,2,8),(1,10,1),(3,11,3),(1,6,0),(1,10,2),(3,1,12),(3,2,8),(3,12,3),(2,12,3),(1,11,3),(1,12,3),(2,11,3),(0,12,3),(1,6,5),(2,14,0),(2,25,1),(3,1,7),(1,0,19),(2,1,9),(1,1,9),(2,0,19),(3,1,32),(0,14,0),(1,15,1),(1,22,4),(1,1,22),(2,31,4),(3,1,31),(1,15,4),(1,29,1),(2,32,4),(2,14,1),(1,1,19)]
def W_37 : BT Decor := buildWiresBT 6 base_37 steps_37
def autosL_37 : List (List (Nat × Nat)) := [[],[(1,2)]]
def autos_37 : BT (List (Nat × Nat)) := btOfList 1 autosL_37
def slicesL_37 : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,6),some (subcubeFast 4 0,5),some (subcubeFast 6 0,4),some (subcubeFast 2 0,5)]
def slices_37 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_37
def ps_37 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(0,[(1,2,3),(3,0,7)]),(3,[]),(0,[(1,2,3),(0,0,7)]),(0,[(0,2,3),(2,0,9)]),(0,[(0,2,3),(1,0,9)]),(0,[(2,2,3),(3,2,3)]),(0,[(3,0,3),(1,10,1)]),(0,[(1,0,2),(3,1,12)]),(0,[(3,2,3)]),(0,[(2,2,3)]),(0,[(1,2,3)]),(0,[(1,0,3)]),(0,[(0,2,3)]),(0,[(3,0,3)]),(0,[(3,0,2)]),(0,[(1,0,2)])]
def P_37 : BT (Option BoundPool) := buildPoolsBT 5 W_37 R_37 slices_37 ps_37
lemma gp_37 : goodPairs G_37 pos_37 neg_37 := goodPairs_of (by decide +kernel)
lemma base_37_ok : ∀ x ∈ base_37, faithful pos_37 neg_37 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_37_ok : btAll (fun x => faithful pos_37 neg_37 x ∧ x.1 < 2^128) W_37 := buildWiresBT_faithful base_37_ok
set_option maxRecDepth 500000 in
lemma autos_37_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_37 = G_37) autos_37 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_37_0_ok : sliceDirectCheck 32 0 0 R_37 G_37 R_11 G_11 = true := by decide +kernel
lemma sl_37_0 : Slice R_37 G_37 (subcubeFast 32 0) 6 := slice_fast_direct sl_37_0_ok low_11
lemma sl_37_1_ok : sliceDirectCheck 4 0 0 R_37 G_37 R_30 G_30 = true := by decide +kernel
lemma sl_37_1 : Slice R_37 G_37 (subcubeFast 4 0) 5 := slice_fast_direct sl_37_1_ok low_30
lemma sl_37_2_ok : sliceDirectCheck 6 0 0 R_37 G_37 R_0 G_0 = true := by decide +kernel
lemma sl_37_2 : Slice R_37 G_37 (subcubeFast 6 0) 4 := slice_fast_direct sl_37_2_ok low_0
lemma sl_37_3_ok : sliceDirectCheck 2 0 0 R_37 G_37 R_12 G_12 = true := by decide +kernel
lemma sl_37_3 : Slice R_37 G_37 (subcubeFast 2 0) 5 := slice_fast_direct sl_37_3_ok low_12
set_option maxRecDepth 500000 in
lemma slices_37_ok : btAll (fun o => ∀ p, o = some p → Slice R_37 G_37 p.1 p.2) slices_37 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_37 G_37 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_37_0) (forall_cons (fun _ h => by cases h; exact sl_37_1) (forall_cons (fun _ h => by cases h; exact sl_37_2) (forall_cons (fun _ h => by cases h; exact sl_37_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_37_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_37 G_37 c) P_37 := buildPoolsBT_sound slices_37_ok
def bk_37_init : BT (List (List Nat)) := BT.empty
lemma bk_37_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 (0 - 1) xs.toFinset) bk_37_init := trivial
def nodes_37_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_0 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_init 0 nodes_37_0 = true := by decide +kernel
def bk_37_0 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_0
set_option maxRecDepth 500000 in
lemma bk_37_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 0 xs.toFinset) bk_37_0 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_init_ok chk_37_0
def nodes_37_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_1 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_0 1 nodes_37_1 = true := by decide +kernel
def bk_37_1 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_1
set_option maxRecDepth 500000 in
lemma bk_37_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 1 xs.toFinset) bk_37_1 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_0_ok chk_37_1
def nodes_37_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_2 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_1 2 nodes_37_2 = true := by decide +kernel
def bk_37_2 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_2
set_option maxRecDepth 500000 in
lemma bk_37_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 2 xs.toFinset) bk_37_2 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_1_ok chk_37_2
def nodes_37_3 : List NodeSpec := [([53,36,2,3],[],[]),([2,3,39,54],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_3 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_2 3 nodes_37_3 = true := by decide +kernel
def bk_37_3 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_3
set_option maxRecDepth 500000 in
lemma bk_37_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 3 xs.toFinset) bk_37_3 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_2_ok chk_37_3
def nodes_37_4 : List NodeSpec := [([6,35,0,1,4],[],[]),([0,1,2,3,19],[],[]),([36,14,1,2,3],[],[0]),([14,16,1,2,3],[],[]),([37,0,2,3,4],[],[]),([38,16,2,3,4],[],[]),([38,17,2,3,4],[],[]),([0,1,2,7,19],[],[]),([1,2,3,19,39],[],[0]),([35,0,1,2,4],[],[]),([0,1,3,7,19],[],[]),([5,0,1,2,19],[],[]),([6,0,1,3,19],[],[]),([20,1,2,3,19],[],[]),([40,2,21,3,4],[],[]),([14,17,1,2,3],[],[]),([35,0,1,3,4],[],[]),([2,21,41,3,4],[],[]),([5,1,2,21,4],[],[]),([1,2,21,7,4],[],[]),([14,0,1,2,3],[],[]),([42,1,2,3,19],[],[]),([43,0,2,3,4],[],[]),([5,18,0,1,4],[],[]),([44,14,1,2,3],[],[]),([16,1,2,3,4],[],[]),([0,45,2,3,4],[],[]),([0,1,2,3,46],[],[]),([5,0,23,2,4],[],[]),([10,1,2,31,4],[],[]),([0,2,47,3,4],[],[]),([5,35,0,1,4],[],[]),([11,1,26,3,4],[],[]),([48,0,1,2,3],[],[]),([6,5,0,1,4],[],[]),([49,0,2,3,4],[],[]),([0,1,2,3,50],[],[]),([0,51,2,3,4],[],[]),([1,2,34,8,4],[],[]),([52,0,1,2,3],[],[]),([1,2,21,3,19],[],[]),([1,2,21,3,4],[],[]),([0,23,2,7,4],[],[]),([1,22,12,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_4 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_3 4 nodes_37_4 = true := by decide +kernel
def bk_37_4 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_4
set_option maxRecDepth 500000 in
lemma bk_37_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 4 xs.toFinset) bk_37_4 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_3_ok chk_37_4
def nodes_37_5 : List NodeSpec := [([0,13,1,2,3,4],[],[]),([6,5,0,1,3,4],[],[0]),([6,5,0,1,2,4],[],[0]),([14,0,1,2,3,7],[0],[0,1]),([15,0,1,2,3,4],[1,0],[0]),([11,10,1,2,3,4],[2],[0]),([14,0,1,2,3],[],[0,1]),([6,0,1,2,3,4],[],[0]),([16,1,2,3,4],[3],[]),([0,1,2,3,7,4],[4,1,0],[0,1]),([17,1,2,3,7,4],[2,5],[0]),([0,1,9,3,7,4],[],[0]),([18,0,1,2,3,4],[4],[0]),([0,1,9,2,7,4],[],[0,1]),([0,1,9,2,3,19],[0],[0,1]),([11,1,2,12,3,4],[0,2],[]),([0,1,2,3,19],[],[0,1]),([5,0,1,2,3,4],[],[0]),([6,0,1,9,3,4],[0],[0]),([0,1,2,8,7,4],[4],[]),([20,1,9,2,3,4],[2,6],[0,1]),([16,0,1,2,3,4],[],[]),([0,1,2,21,3,4],[],[]),([1,2,21,3,4],[7],[0]),([6,5,0,1,4],[8],[0]),([0,1,22,2,3,4],[1,4,0],[0]),([0,1,9,2,3,4],[4,1,0],[0,1]),([10,1,2,3,8,4],[2],[]),([5,0,1,2,8,4],[4],[]),([5,10,0,1,2,4],[4],[0]),([16,1,2,3,7,4],[4,3],[1,0]),([0,23,2,3,4],[9],[0]),([5,0,1,9,2,4],[0],[0,1]),([0,24,1,2,3,4],[],[]),([0,25,1,2,3,4],[1],[0]),([10,0,23,2,3,4],[1,2],[]),([0,1,2,26,3,4],[],[0]),([27,0,2,12,3,4],[1],[]),([6,0,1,2,7,4],[0],[0]),([28,0,1,2,3,4],[],[]),([29,0,1,2,3,4],[1],[0]),([27,0,2,3,4],[10],[]),([30,0,1,2,3,4],[],[]),([10,0,1,2,7,4],[4],[0]),([0,1,2,3,31,4],[1,0],[0]),([5,0,1,3,7,4],[0],[0]),([0,1,2,3,32,4],[1,0],[0]),([1,9,2,21,3,4],[4,7],[0]),([1,2,12,3,8,4],[2],[0]),([33,0,1,2,3,4],[],[]),([0,1,2,34,3,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_5 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_4 5 nodes_37_5 = true := by decide +kernel
def bk_37_5 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_5
set_option maxRecDepth 500000 in
lemma bk_37_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 5 xs.toFinset) bk_37_5 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_4_ok chk_37_5
def nodes_37_6 : List NodeSpec := [([5,0,1,2,3,4],[4,1,0,11],[0,1]),([6,0,1,2,3,4],[4,1,0,12],[0,1]),([0,1,2,3,7,4],[4,13,1],[0,1]),([0,1,2,3,8,4],[4,2,14],[0]),([0,1,9,2,3,4],[4,15,1],[0,1]),([10,0,1,2,3,4],[4,1,2,0,16],[0]),([11,0,1,2,3,4],[4,1,2,0,17],[0]),([0,1,2,12,3,4],[2,18],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_6 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_5 6 nodes_37_6 = true := by decide +kernel
def bk_37_6 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_6
set_option maxRecDepth 500000 in
lemma bk_37_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 6 xs.toFinset) bk_37_6 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_5_ok chk_37_6
def nodes_37_7 : List NodeSpec := [([0,1,2,3,4],[4,2,0],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_7 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_6 7 nodes_37_7 = true := by decide +kernel
def bk_37_7 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_7
set_option maxRecDepth 500000 in
lemma bk_37_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 7 xs.toFinset) bk_37_7 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_6_ok chk_37_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_37_ok : forestRootCheck R_37 G_37 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 4,22,6),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_37_in : bucketContainsBT bk_37_7 R_37 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_37 : Lower R_37 G_37 8 := lower_of_forestBT root_37_ok bk_37_7_ok root_37_in

end Cofactor12168
def h54R : List Nat := varsOf 59
def h54G : Nat := 0xeeeeeeaaeeeeaa88eeeeeeaaeeeeaa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h54Bound : Lower h54R h54G 8 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(0,1),(1,2)]) (roots2 := Cofactor12168.R_37) (T2 := Cofactor12168.G_37) (by decide +kernel) Cofactor12168.low_37
def h55R : List Nat := varsOf 61
def h55G : Nat := 0xfffafaaafaf0aaa0fffafaaafaf0aaa0
def h55Pos : List Nat := [9,20,9,33,44,9,20,25,44,33,5,28,44,56,5,25,13,49,21,49,56,56,25,20,37,33,13,41,9,20,52,28,5,28,5,20,44,20,5,52,37,21,49,33,20,9,21,44,41,44,5,25,44,56]
def h55Neg : List Nat := [8,16,12,32,36,1,4,24,12,1,4,24,40,40,1,17,12,17,17,48,24,48,16,17,36,40,1,40,40,24,48,12,0,16,17,0,32,48,36,36,1,1,1,17,12,24,4,8,1,0,12,1,4,16]
def h55Mask : Nat := fullMask 54
def h55Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xd6f451f4fc6ad,0x90f040486c220),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x16d3ffe5855d52,0x1450c081010554),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ba0129c71b9b5,0x4b000ba113985),(0xffff0000ffff0000ffff0000ffff0000,0x2856aae0fea8c2,0x20282660fe8882),(0xffffffff00000000ffffffff00000000,0x338d904b3a3318,0xf05b283018)]
def h55Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,1,4),(1,1,4),(3,1,4),(1,2,3),(2,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(1,2,5),(3,3,4),(2,2,5),(1,3,5),(1,1,29),(0,2,6),(2,2,6),(0,2,13),(0,2,37),(0,4,37),(0,6,13),(1,6,37),(0,13,37),(2,1,29),(3,1,29),(3,1,44),(0,13,44),(2,6,29),(0,13,29),(2,13,29),(1,1,38),(2,6,15),(1,0,19),(3,1,55),(0,2,55),(1,4,19),(2,4,19),(2,6,19),(1,0,29),(0,4,61),(3,0,29),(3,0,37),(0,3,37),(3,3,37),(1,3,29),(1,0,38),(1,3,7),(1,8,15),(1,8,29),(2,1,57),(0,2,21),(0,3,53),(1,3,53),(2,3,53),(3,3,53),(1,3,9),(1,4,9),(2,4,9),(3,9,21),(2,2,22),(2,4,22),(1,9,22),(2,4,74),(2,2,20),(2,4,20),(1,1,62),(1,3,62),(2,3,62),(0,3,88),(3,3,88),(3,62,88),(3,4,10),(2,10,19),(0,10,21),(1,0,96),(1,0,82),(2,10,22),(1,0,24),(2,2,24),(2,10,24),(2,2,26),(1,1,103),(2,4,103),(2,10,26),(2,2,34),(2,10,34),(1,20,62),(1,3,11),(3,11,21),(1,11,22),(1,1,63),(1,0,47),(1,0,59),(2,4,40),(1,1,45),(1,0,105),(1,15,16),(2,2,119),(1,15,19),(1,15,29),(3,15,29),(2,4,120),(3,15,37),(3,3,17),(2,17,29),(1,26,29),(1,4,18),(1,19,26),(1,19,32),(2,21,29),(0,21,30),(3,29,30),(2,21,31),(1,22,29),(3,22,30),(1,22,31),(0,4,27),(1,0,28),(2,4,28),(1,0,141),(1,29,130),(3,29,130),(1,1,144)]
def h55W : BT Decor := buildWiresBT 8 h55Base h55Steps
def h55AutoList : List (List (Nat × Nat)) := [[],[(3,5)]]
def h55Autos : BT (List (Nat × Nat)) := btOfList 1 h55AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Pairs : goodPairs h55G h55Pos h55Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55BaseOk : ∀ x ∈ h55Base, faithful h55Pos h55Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55WOk : btAll (fun x => faithful h55Pos h55Neg x ∧ x.1 < 2^128) h55W := buildWiresBT_faithful h55BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h55G = h55G) h55Autos := btAll_ofList (autos_of (by decide +kernel))
def h55SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 8,4),some (subcubeFast 1 32,4),some (subcubeFast 4 0,5),some (subcubeFast 4 16,4),some (subcubeFast 8 0,4),some (subcubeFast 16 0,6),some (subcubeFast 32 0,4)]
def h55Slices : BT (Option (Nat × Nat)) := btOfList 4 h55SliceList
def h55Specs : List PoolSpec := [(3,[]),(6,[]),(9,[(0,0,1)]),(4,[]),(9,[(0,0,1),(1,2,5)]),(5,[]),(0,[]),(9,[(0,0,1),(2,2,5)]),(8,[]),(9,[]),(1,[]),(2,[]),(9,[(1,0,1)]),(6,[(1,0,3)]),(7,[]),(1,[(1,0,1)]),(0,[(1,0,3)]),(2,[(1,0,3)]),(6,[(3,0,3)]),(0,[(3,0,3)]),(2,[(3,0,3)]),(0,[(1,0,1)]),(10,[]),(9,[(1,0,1),(0,2,6)]),(9,[(2,0,1)]),(1,[(2,0,1)]),(2,[(1,0,1)]),(6,[(1,3,7)]),(9,[(3,0,1)]),(0,[(1,0,19)]),(9,[(0,0,2)]),(0,[(1,4,9)]),(0,[(1,3,9)]),(9,[(0,0,2),(1,4,9)]),(9,[(0,0,2),(2,4,9)]),(0,[(2,4,9)]),(9,[(1,0,2)]),(1,[(3,1,2)]),(3,[(0,2,4)]),(2,[(1,0,29)]),(2,[(1,0,2)]),(3,[(3,4,10)]),(9,[(1,0,2),(3,4,10)]),(9,[(2,0,2)]),(9,[(3,0,2)]),(2,[(3,0,2)]),(0,[(3,0,29)]),(2,[(3,0,29)]),(9,[(3,1,2)]),(2,[(1,0,3),(1,0,29)]),(9,[(0,2,4)]),(0,[(1,0,3),(1,0,29)]),(9,[(0,2,13)]),(9,[(0,1,2)]),(9,[(1,1,2)]),(9,[(1,1,4)]),(9,[(3,1,4),(2,2,26)]),(9,[(3,1,4)]),(1,[(1,1,2)]),(6,[(3,3,17)]),(9,[(2,1,2)]),(9,[(2,1,2),(1,4,18)]),(3,[(3,2,4)]),(9,[(3,1,2),(2,4,19)]),(9,[(0,2,21)]),(6,[(0,2,21)]),(9,[(2,2,22)]),(9,[(0,4,27)]),(9,[(1,0,28)]),(0,[(1,0,28)]),(9,[(2,4,28)]),(0,[(1,0,29)]),(9,[(0,2,4),(1,2,4)]),(9,[(1,2,4),(0,2,4)]),(9,[(1,2,4)]),(9,[(2,2,4)])]
def h55Pools : BT (Option BoundPool) := buildPoolsBT 7 h55W h55R h55Slices h55Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice10 : Slice h55R h55G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice9 : Slice h55R h55G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice8 : Slice h55R h55G (subcubeFast 8 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice7 : Slice h55R h55G (subcubeFast 4 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice6 : Slice h55R h55G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice5 : Slice h55R h55G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice4 : Slice h55R h55G (subcubeFast 1 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice3 : Slice h55R h55G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice2 : Slice h55R h55G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice1 : Slice h55R h55G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice0 : Slice h55R h55G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h52Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h55R h55G p.1 p.2) h55Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h55R h55G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h55Slice0) (forall_cons (fun _ h => by cases h; exact h55Slice1) (forall_cons (fun _ h => by cases h; exact h55Slice2) (forall_cons (fun _ h => by cases h; exact h55Slice3) (forall_cons (fun _ h => by cases h; exact h55Slice4) (forall_cons (fun _ h => by cases h; exact h55Slice5) (forall_cons (fun _ h => by cases h; exact h55Slice6) (forall_cons (fun _ h => by cases h; exact h55Slice7) (forall_cons (fun _ h => by cases h; exact h55Slice8) (forall_cons (fun _ h => by cases h; exact h55Slice9) (forall_cons (fun _ h => by cases h; exact h55Slice10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h55R h55G c) h55Pools := buildPoolsBT_sound h55SlicesOk
def h55Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h55G (3 - 1) xs.toFinset) h55Empty := trivial
def h55Block3_0 : List NodeSpec := nodesWithIdentity [([1,2,49,62],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test3_0 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Empty 3 h55Block3_0 = true := by decide +kernel
def h55Nodes3 : List NodeSpec := h55Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Check3 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Empty 3 h55Nodes3 = true := h55Test3_0
def h55Bucket3 : BT (List (List Nat)) := buildBucketsBT h55W h55Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h55G 3 xs.toFinset) h55Bucket3 := buildBucketsBT_sound (by decide) h55Pairs h55WOk h55PoolsOk h55AutosOk h55EmptyOk h55Check3
def h55Block4_0 : List NodeSpec := nodesWithIdentity [([2,4,6,13,37],[]),([1,2,4,13,44],[9]),([1,2,4,13,50],[]),([2,3,4,43,53],[]),([0,2,3,53,85],[]),([0,2,3,53,87],[]),([0,3,19,62,88],[]),([0,3,19,62,93],[]),([0,1,3,62,82],[]),([2,3,4,43,56],[]),([1,2,3,43,62],[]),([0,1,3,62,86],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test4_0 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket3 4 h55Block4_0 = true := by decide +kernel
def h55Block4_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,109],[]),([0,1,2,62,91],[]),([0,1,2,62,92],[]),([1,4,13,19,61],[49]),([1,2,4,13,114],[]),([1,2,4,13,48],[]),([1,4,13,40,61],[49]),([0,1,2,4,45],[9]),([0,2,4,13,117],[]),([0,1,2,15,124],[]),([0,1,2,4,125],[]),([0,1,3,30,132],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test4_1 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket3 4 h55Block4_1 = true := by decide +kernel
def h55Block4_2 : List NodeSpec := nodesWithIdentity [([0,1,3,29,137],[]),([1,2,4,37,49],[]),([0,3,29,37,130],[]),([0,1,29,30,66],[]),([0,1,3,29,144],[]),([0,3,29,46,130],[]),([0,1,3,29,143],[]),([0,1,3,29,145],[]),([2,3,4,43,104],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test4_2 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket3 4 h55Block4_2 = true := by decide +kernel
def h55Nodes4 : List NodeSpec := h55Block4_0 ++ h55Block4_1 ++ h55Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Check4 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket3 4 h55Nodes4 = true := by
  unfold h55Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h55Test4_0,h55Test4_1⟩,h55Test4_2⟩
def h55Bucket4 : BT (List (List Nat)) := buildBucketsBT h55W h55Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h55G 4 xs.toFinset) h55Bucket4 := buildBucketsBT_sound (by decide) h55Pairs h55WOk h55PoolsOk h55AutosOk h55Bucket3Ok h55Check4
def h55Block5_0 : List NodeSpec := nodesWithIdentity [([1,2,4,6,13,29],[3,5,13]),([1,2,4,6,13,38],[0,3,13]),([1,2,4,6,13,39],[3]),([0,1,2,4,15,54],[12]),([1,2,3,4,6,55],[9]),([1,2,3,4,6,61],[1,3,5]),([0,2,3,4,6,37],[0,8,22]),([0,1,2,3,4,44],[6,9,10,11]),([0,1,2,3,4,50],[]),([0,1,2,4,15,70],[28]),([0,2,3,4,8,37],[]),([0,1,2,3,4,71],[9,10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_0 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_0 = true := by decide +kernel
def h55Block5_1 : List NodeSpec := nodesWithIdentity [([0,2,3,4,21,53],[8,9,21]),([0,1,2,3,21,79],[8,31]),([0,1,2,3,21,80],[]),([0,1,2,3,4,81],[0,9]),([0,2,3,4,22,53],[]),([0,1,2,3,22,79],[]),([0,1,2,3,22,80],[]),([0,1,2,3,4,84],[0,9]),([0,2,3,4,53,74],[0,5,8,21]),([0,2,3,4,53,75],[8,21]),([0,2,3,4,53,76],[]),([0,2,3,4,53,77],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_1 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_1 = true := by decide +kernel
def h55Block5_2 : List NodeSpec := nodesWithIdentity [([0,2,3,4,20,53],[0,5,8,21]),([0,2,3,4,23,53],[0]),([0,1,3,19,62],[3,5,6,38,39]),([0,1,3,4,19,62],[5,39]),([0,1,3,4,19,95],[]),([0,1,2,3,21,62],[]),([0,1,2,3,21,94],[]),([0,1,2,3,4,96],[]),([0,1,3,4,10,82],[]),([0,1,2,3,22,62],[6]),([0,1,2,3,22,94],[]),([0,1,2,3,4,99],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_2 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_2 = true := by decide +kernel
def h55Block5_3 : List NodeSpec := nodesWithIdentity [([1,2,3,4,10,100],[1]),([0,1,3,4,10,101],[22]),([0,1,2,3,4,102],[6]),([0,1,3,4,10,103],[22]),([0,1,2,3,4,106],[6]),([0,2,3,4,20,56],[6]),([0,2,3,4,23,56],[6]),([0,1,3,4,10,107],[22]),([0,1,2,3,4,108],[6]),([0,1,2,3,20,62],[6,22,38]),([0,1,2,3,23,62],[]),([0,1,2,3,62,88],[6,22,39])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_3 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_3 = true := by decide +kernel
def h55Block5_4 : List NodeSpec := [([0,1,2,3,62,93],[5,6],[0]),([0,1,2,3,62,89],[],[0]),([0,1,2,3,62,90],[],[0]),([0,1,2,3,4,88],[6,9,10,22],[0]),([0,1,3,4,11,73],[10],[0]),([0,1,2,3,4,111],[9],[0]),([0,1,2,3,4,112],[9],[0]),([0,1,2,3,4,113],[9,10],[0]),([0,1,4,13,19,29],[13,17],[0]),([0,1,2,4,13,47],[0],[0]),([0,1,2,4,13,59],[],[0]),([1,2,4,13,61],[3,5,9,38,49,51],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_4 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_4 = true := by decide +kernel
def h55Block5_5 : List NodeSpec := nodesWithIdentity [([1,2,4,13,29,61],[0,3,49,51]),([0,1,2,4,13,37],[0,10]),([0,1,4,13,29,40],[10,17]),([0,1,2,4,13,51],[0,9,13]),([0,1,2,4,13,52],[0,9]),([0,1,2,4,13,116],[]),([1,2,3,4,13,61],[3,9]),([0,1,2,3,4,52],[0]),([0,1,2,4,15,105],[]),([0,1,2,4,15,119],[53]),([0,1,4,15,19,29],[18,20]),([0,1,2,4,15,47],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_5 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_5 = true := by decide +kernel
def h55Block5_6 : List NodeSpec := nodesWithIdentity [([0,1,2,4,15,59],[]),([0,1,2,4,15,121],[]),([0,1,2,4,15,120],[20]),([0,1,2,4,15,37],[9]),([0,1,2,4,15,122],[50]),([0,1,2,4,15,123],[]),([0,1,2,3,4,118],[6]),([0,1,3,17,25,29],[1,6]),([0,1,3,4,17,41],[]),([0,1,2,3,4,37],[9,10]),([0,1,3,17,26,29],[1,6]),([0,1,3,4,17,103],[56])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_6 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_6 = true := by decide +kernel
def h55Block5_7 : List NodeSpec := nodesWithIdentity [([0,1,3,4,29,127],[6]),([0,1,3,19,26,29],[1,6]),([0,1,3,4,19,61],[6,39]),([0,1,3,4,19,131],[6]),([0,1,2,3,4,114],[]),([0,1,2,3,4,115],[6]),([0,2,3,4,21,37],[9]),([0,1,3,21,29,30],[8]),([0,1,2,3,4,132],[]),([0,1,3,4,30,73],[8]),([0,1,2,3,4,133],[]),([0,1,2,3,4,135],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_7 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_7 = true := by decide +kernel
def h55Block5_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,97],[10,11,22]),([0,2,3,4,22,37],[9]),([0,1,3,22,29,30],[6]),([0,1,2,3,4,136],[10]),([0,1,2,3,4,137],[]),([0,1,2,3,31,83],[]),([0,1,2,3,4,138],[]),([0,1,2,3,4,98],[]),([0,1,2,3,4,142],[6]),([0,1,2,3,4,48],[]),([0,1,2,3,4,64],[9,10]),([0,1,2,4,37,65],[10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_8 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_8 = true := by decide +kernel
def h55Block5_9 : List NodeSpec := nodesWithIdentity [([0,1,2,4,37,66],[9]),([0,1,3,29,30,37],[6,8,72]),([0,1,2,4,29,66],[]),([0,1,3,29,30,46],[6]),([0,1,3,29,130],[3,6,38]),([0,1,3,29,30,67],[73]),([0,1,3,29,134],[3,6,38]),([0,2,3,4,20,104],[8,11]),([0,2,3,4,23,104],[10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_9 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_9 = true := by decide +kernel
def h55Nodes5 : List NodeSpec := h55Block5_0 ++ h55Block5_1 ++ h55Block5_2 ++ h55Block5_3 ++ h55Block5_4 ++ h55Block5_5 ++ h55Block5_6 ++ h55Block5_7 ++ h55Block5_8 ++ h55Block5_9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Check5 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Nodes5 = true := by
  unfold h55Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h55Test5_0,h55Test5_1⟩,h55Test5_2⟩,h55Test5_3⟩,h55Test5_4⟩,h55Test5_5⟩,h55Test5_6⟩,h55Test5_7⟩,h55Test5_8⟩,h55Test5_9⟩
def h55Bucket5 : BT (List (List Nat)) := buildBucketsBT h55W h55Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h55G 5 xs.toFinset) h55Bucket5 := buildBucketsBT_sound (by decide) h55Pairs h55WOk h55PoolsOk h55AutosOk h55Bucket4Ok h55Check5
def h55Block6_0 : List NodeSpec := [([0,1,3,4,33],[0,1,4,5,6],[0]),([0,1,3,4,35],[0,1,3,5,7,8],[0]),([0,1,2,4,36],[0,1,2,3,9,10],[0]),([1,2,4,6,13],[0,3,5,9,12,13,14,15],[0,1]),([0,1,2,4,6,13],[0,3,5,9,10,12,13,14,16,17],[0]),([0,1,2,4,6,15],[0,3,5,9,10,12,14,18,19,20],[0]),([0,1,2,3,4,6,19],[0,6,8,14,21],[0]),([0,1,2,3,4,6,29],[0,1,3,5,6,8,11,22],[0]),([0,1,2,3,4,38],[0,1,3,8,9,10,11,21,22,23],[0]),([0,1,2,3,4,6,38],[0,1,3,6,8],[0]),([0,1,2,3,4,39],[3,8,9,10,11,21,22],[0]),([0,1,2,3,4,6,39],[3,6,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_0 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_0 = true := by decide +kernel
def h55Block6_1 : List NodeSpec := nodesWithIdentity [([1,2,4,7,13],[0,3,5,13,14,25]),([0,1,2,3,4,6],[0,1,6,8,9,10,11,12,14,21,22,26]),([0,1,2,4,69],[0,3,5,9,10,24,27]),([0,1,2,4,8,15],[0,3,5,9,18,19,20,28]),([0,1,2,3,4,8,29],[1,3,5,6,8,11,22]),([0,1,2,3,4,57],[0,1,3,8,9,10,11,22,29]),([0,1,2,3,4,9,21],[0,1,6,8,9,10]),([0,1,2,3,4,9,22],[0,1,9,10]),([0,2,3,4,53],[0,3,5,8,21]),([0,1,2,3,4,53],[0,1,3,5,8,9,10,11,21,22]),([0,2,3,4,72],[0,1,5,8,29]),([0,1,2,4,78],[0,5,8,9,10,30,32])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_1 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_1 = true := by decide +kernel
def h55Block6_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,79],[0,8,11,31,33]),([0,1,2,3,80],[0,5,8,22,34,35]),([0,1,3,4,10,19],[0,1,3,6,8,37,40]),([0,1,2,3,4,10,21],[6,10]),([0,1,2,3,4,10,22],[1,6,9,10]),([0,1,2,3,4,10,24],[0,1,6,11,22]),([0,1,2,3,4,10,26],[5,6,11,22]),([0,1,2,3,4,56],[0,1,3,6,8,9,10,11,22]),([0,1,2,3,4,10,34],[6,10,11,22]),([0,1,2,3,62],[3,5,6,22,38]),([0,1,2,3,4,62],[0,1,3,5,6,8,9,10,22,38,39]),([0,1,2,3,94],[3,6,11,41,42])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_2 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_2 = true := by decide +kernel
def h55Block6_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,11,21],[0,6,9,10]),([0,1,2,3,4,11,22],[0,1,9,10]),([0,1,2,3,4,60],[0,1,5,6,9,10,11,22]),([0,1,2,4,110],[0,5,6,9,10,43]),([0,1,3,4,12,19],[0,1,3,6,8,37,45]),([0,1,2,3,4,12,21],[3,8,10]),([0,1,2,3,4,12,22],[1,3,6,8,9,10]),([0,1,2,3,4,12,24],[1,3,6,8]),([0,1,2,3,4,12,26],[3,5,6,8,11,22]),([0,1,2,3,4,12,34],[3,6,8,10]),([0,1,2,3,4,63],[1,3,5,8,9,10,22,38,46,47]),([0,1,2,4,13,19],[0,3,10,13,14,16,17,37,48])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_3 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_3 = true := by decide +kernel
def h55Block6_4 : List NodeSpec := [([0,1,2,4,13,29],[0,3,5,10,13,16,17,38,50],[0,1]),([0,1,2,4,13,40],[0,3,9,10,13,14,16,17,52],[0]),([0,1,2,3,4,13,29],[0,3,6,8,9,10,11,22,50],[0]),([0,1,2,3,4,40],[0,1,3,8,9,10,11,14,16,22,52],[0]),([0,1,2,4,13],[0,3,5,9,10,13,14,16,17],[0]),([0,1,2,4,15,16],[0,3,9,18,19,20,53],[0]),([0,1,2,4,15,19],[0,3,9,18,19,20,48],[0]),([0,1,2,4,15,29],[0,3,5,9,18,19,20,38,50],[0,1]),([0,1,2,3,4,68],[0,1,3,8,9,10,11,14,21,22],[0,1]),([0,1,2,3,4,19],[0,1,3,6,8,9,10,11,22,48],[0]),([0,1,2,3,4,105],[0,1,6,8,9,10,14,22],[0,1]),([0,1,2,3,4,17,25],[1,6,11,14,54,55],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_4 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_4 = true := by decide +kernel
def h55Block6_5 : List NodeSpec := [([0,1,2,3,4,17,26],[6,8,11,14,22,57],[0]),([0,1,3,4,17,29],[1,3,6,8,11,38,58],[0]),([0,1,2,4,126],[3,6,10,14,54,59],[0]),([0,1,2,3,4,42],[0,1,3,6,8,9,10,22],[0,1]),([0,1,2,3,129],[1,3,6,11,61],[0]),([0,1,2,3,128],[1,3,6,14,22],[0]),([0,1,2,3,4,128],[0,1,3,6,9,10,14,22],[0]),([0,1,2,3,4,55],[0,1,3,6,8,9,10,11,22,29],[0]),([0,1,2,3,4,19,55],[0,1,6,8,29],[0]),([0,1,2,3,4,19,26],[6,8,11,22],[0]),([0,1,3,4,19,29],[1,3,6,8,11,37,38],[0,1]),([0,1,3,4,19,32],[1,3,6,8,11,37,62],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_5 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_5 = true := by decide +kernel
def h55Block6_6 : List NodeSpec := [([0,1,2,3,4,47],[0,8,9,10,22],[0]),([0,1,2,3,4,19,58],[1,6,8,11,22],[0]),([0,1,2,3,4,59],[0,1,6,8,9,10,22,63],[0,1]),([0,1,2,3,4,19,59],[1,6,8,11],[0]),([0,1,2,3,4,70],[0,1,6,8,9,10,11,14,18,22,28],[0]),([0,1,2,3,4,21,29],[1,8,9,10],[0]),([0,1,2,3,4,21,30],[6,10,11],[0,1]),([0,1,2,3,4,21,31],[6,8,10,11],[0]),([0,1,2,3,4,73],[0,1,8,9,10,11,14,22,64,65],[0]),([0,1,2,3,4,54],[0,1,6,8,9,10,11,12,22],[0]),([0,1,2,3,4,22,29],[1,6,8,9,10,11,22],[0]),([0,1,2,3,4,22,30],[1,6,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_6 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_6 = true := by decide +kernel
def h55Block6_7 : List NodeSpec := [([0,1,2,3,4,22,31],[1,9,10,11],[0]),([0,1,2,3,4,82],[0,1,8,9,10,11,22,66],[0,1]),([0,1,2,3,4,139],[0,1,3,6,9,10,14,22,67],[0]),([0,1,2,3,4,140],[0,1,3,6,8,9,10,11,14,22,68,69],[0]),([0,1,2,3,4,141],[0,1,6,8,9,10,14,22,70],[0,1]),([0,1,2,3,4,61],[0,1,3,5,6,8,9,10,11,22,38,39,71],[0,1]),([0,1,2,3,4,29,61],[0,3,6,8,11,22,38,39,71],[0]),([0,1,2,3,4,37],[0,1,6,8,9,10,11,22],[0]),([0,1,2,3,4,29,37],[1,6,8,11,22,50],[0]),([0,1,2,3,4,29,46],[1,6,8,11,22],[0]),([0,1,3,29,30],[3,6,8,38,72],[0]),([0,1,2,3,4,29,67],[9,10,50],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_7 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_7 = true := by decide +kernel
def h55Block6_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,130],[0,1,3,6,9,10,11]),([0,1,2,3,4,104],[0,1,5,6,8,9,10,11]),([0,1,2,3,4,29],[0,1,3,6,8,9,10,11,22,38,50])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_8 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_8 = true := by decide +kernel
def h55Nodes6 : List NodeSpec := h55Block6_0 ++ h55Block6_1 ++ h55Block6_2 ++ h55Block6_3 ++ h55Block6_4 ++ h55Block6_5 ++ h55Block6_6 ++ h55Block6_7 ++ h55Block6_8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Check6 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Nodes6 = true := by
  unfold h55Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h55Test6_0,h55Test6_1⟩,h55Test6_2⟩,h55Test6_3⟩,h55Test6_4⟩,h55Test6_5⟩,h55Test6_6⟩,h55Test6_7⟩,h55Test6_8⟩
def h55Bucket6 : BT (List (List Nat)) := buildBucketsBT h55W h55Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h55G 6 xs.toFinset) h55Bucket6 := buildBucketsBT_sound (by decide) h55Pairs h55WOk h55PoolsOk h55AutosOk h55Bucket5Ok h55Check6
def h55Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,5,6,9,10,11],[0,1]),([0,1,2,3,4,6],[0,1,3,5,6,9,10,11,12,14],[0,1]),([0,1,2,3,4,7],[0,1,3,5,6,9,10,11,14,24],[0]),([0,1,2,3,4,8],[0,1,3,5,6,9,10,11,14,28],[0,1]),([0,1,2,3,4,9],[0,1,3,5,6,8,9,10,11,30],[0]),([0,1,2,3,4,10],[0,1,3,5,6,9,10,11,36],[0]),([0,1,2,3,4,11],[0,1,5,6,9,10,11,43],[0]),([0,1,2,3,4,12],[0,1,3,5,6,8,9,10,11,44],[0]),([0,1,2,4,13],[0,3,5,9,10,14],[0,1]),([0,1,2,3,4,13],[0,1,3,5,6,9,10,11,14],[0,1]),([0,1,2,3,4,14],[0,1,3,5,6,9,11,14],[0]),([0,1,2,4,15],[0,3,5,9],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test7_0 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket6 7 h55Block7_0 = true := by decide +kernel
def h55Block7_1 : List NodeSpec := [([0,1,2,3,4,16],[0,1,3,6,8,9,10,11,14,53],[0,1]),([0,1,2,3,4,17],[0,1,3,6,9,10,11,14,54],[0]),([0,1,2,3,4,18],[0,1,3,6,9,10,11,14,60],[0]),([0,1,2,3,4,19],[0,1,3,6,8,9,10,11,14,48],[0,1]),([0,1,2,3,4,21],[0,1,6,9,10,11,14],[0,1]),([0,1,2,3,4,22],[0,1,6,9,10,11],[0,1]),([0,1,2,3,4,27],[0,1,3,6,9,10,11,14],[0]),([0,1,2,3,4,28],[0,1,3,6,8,9,10,11,14],[0,1]),([0,1,2,3,4,29],[0,1,3,5,6,8,9,10,11,22,50],[0,1]),([0,1,2,3,4,30],[0,1,3,6,9,10,11,74],[0]),([0,1,2,3,4,31],[0,1,3,5,6,8,9,10,11,75],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test7_1 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket6 7 h55Block7_1 = true := by decide +kernel
def h55Nodes7 : List NodeSpec := h55Block7_0 ++ h55Block7_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Check7 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket6 7 h55Nodes7 = true := by
  unfold h55Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h55Test7_0,h55Test7_1⟩
def h55Bucket7 : BT (List (List Nat)) := buildBucketsBT h55W h55Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h55G 7 xs.toFinset) h55Bucket7 := buildBucketsBT_sound (by decide) h55Pairs h55WOk h55PoolsOk h55AutosOk h55Bucket6Ok h55Check7
def h55Block8_0 : List NodeSpec := [([0,1,2,3,4],[9],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test8_0 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket7 8 h55Block8_0 = true := by decide +kernel
def h55Nodes8 : List NodeSpec := h55Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Check8 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket7 8 h55Nodes8 = true := h55Test8_0
def h55Bucket8 : BT (List (List Nat)) := buildBucketsBT h55W h55Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h55G 8 xs.toFinset) h55Bucket8 := buildBucketsBT_sound (by decide) h55Pairs h55WOk h55PoolsOk h55AutosOk h55Bucket7Ok h55Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bound : Lower h55R h55G 9 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,4,20),(VAR 5,1,33)]) (by decide +kernel) h55Bucket8Ok (by decide +kernel)
def h56R : List Nat := varsOf 62
def h56G : Nat := 0xfffcfffcfff0fcc0fffcfffcfff0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h56Bound : Lower h56R h56G 8 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,4,20)]) (by decide +kernel) h22Bound
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xeee8eaa8eae0a880eee8eaa8eae0a880
def h0Pos : List Nat := [13,22,13,22,25,25,25,46,11,22,41,21,46,35,11,58,13,46,37,7,13,21,25,37,7,25,51,54,51,27,30,46,51,13,37,7,21,11,37,21,7,11,58,41,53,37,58,22,41,30,15,30,13,58,22,27,21,23,35,35,7,53,41,37,21,29,29,21,37,7,39,11,11,43,22,53,7,7,22,35,35,35,35,22,22,35,58,22,25,37,45,11,54,11,46,29,21,23,23,11,13,57]
def h0Neg : List Nat := [12,20,14,18,24,26,28,38,3,6,40,5,14,3,10,56,5,44,5,5,9,20,9,33,1,17,19,38,49,26,26,42,50,8,36,6,19,9,38,28,3,1,50,9,52,4,26,26,33,14,14,28,1,42,38,19,17,19,33,49,19,49,1,49,1,9,5,49,1,2,38,14,2,42,14,5,38,4,19,42,34,38,2,28,4,1,60,52,49,32,44,42,50,26,60,28,4,6,5,8,28,49]
def h0Mask : Nat := fullMask 102
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3faf27bbffff953bff37fd6d75,0x240120481fff910b3017dd2900),(0xcccccccccccccccccccccccccccccccc,0xe78fff7e01eeec729fd0af38a,0x23807d7e012e6c559ec0073ac),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x17d6987c7fb35eb1dec9bf1a8f,0x17c4da3cc4004e30cc082f1ac7),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x38ed40038640bf4e22e253d5f5,0x18ec488682002ec8a2e052d475),(0xffff0000ffff0000ffff0000ffff0000,0x2791d84c0f23ead4917e608a7a,0x30f1c84008bb88d4917620807a),(0xffffffff00000000ffffffff00000000,0x2056678a50ec217c459c86b480,0x205fc39248ac61144598828480)]
def h0Steps : List (Nat × Nat × Nat) := [(0,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(3,0,3),(1,0,4),(2,0,4),(0,0,5),(1,0,5),(2,0,5),(0,1,2),(2,1,2),(0,1,3),(2,1,4),(0,1,5),(2,1,5),(0,1,8),(2,1,8),(0,0,26),(2,0,26),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(2,2,4),(1,2,5),(2,2,5),(1,2,6),(2,2,6),(2,3,4),(1,3,5),(2,3,5),(0,3,6),(1,3,6),(2,3,6),(1,4,5),(1,4,6),(0,2,46),(1,2,46),(2,2,46),(3,2,46),(0,3,46),(2,3,46),(3,5,46),(2,4,6),(3,4,6),(1,5,6),(3,5,6),(0,1,46),(1,4,8),(2,1,10),(2,0,60),(1,4,10),(2,1,12),(1,4,12),(2,1,18),(1,4,18),(2,0,29),(2,1,29),(1,6,29),(1,5,69),(3,5,69),(2,6,29),(1,4,29),(0,0,73),(0,1,73),(0,1,56),(2,0,72),(2,1,72),(2,0,32),(2,1,32),(0,0,45),(0,1,45),(0,0,82),(2,0,82),(1,4,32),(1,6,32),(3,6,45),(0,0,33),(0,1,33),(0,0,89),(2,0,89),(1,4,89),(2,0,41),(2,1,41),(1,4,41),(3,6,33),(1,4,96),(2,1,44),(0,33,46),(2,1,90),(2,0,34),(2,1,34),(2,0,39),(2,1,39),(1,6,34),(1,6,39),(1,34,39),(3,4,105),(3,34,46),(0,0,35),(0,1,35),(0,0,111),(2,0,111),(3,4,35),(3,6,35),(2,1,112),(1,5,112),(2,0,36),(2,1,36),(1,4,36),(1,6,36),(2,6,36),(2,0,122),(2,1,122),(0,1,37),(2,3,25),(3,25,37),(1,25,54),(0,0,99),(0,1,99),(2,0,55),(2,0,57),(1,4,57),(2,37,57),(2,1,38),(2,0,42),(1,2,42),(2,2,42),(1,4,42),(1,5,42),(1,38,42),(1,42,54),(0,0,139),(0,1,139),(2,1,83),(2,3,47),(1,5,47),(2,46,57),(1,7,29),(3,7,35),(1,7,36),(1,4,20),(1,4,21),(1,8,21),(1,4,24),(1,8,24),(3,8,45),(1,3,125),(2,3,125),(2,9,21),(2,9,24),(1,10,21),(1,10,24),(2,0,104),(3,10,45),(1,11,21),(1,11,24),(1,12,19),(1,4,168),(3,4,168),(1,12,20),(1,12,24),(3,12,33),(2,0,102),(1,4,110),(3,12,35),(1,12,36),(3,12,45),(1,13,19),(1,13,20),(1,13,24),(1,2,98),(2,2,98),(2,35,98),(3,13,35),(1,13,36),(2,14,19),(2,14,20),(2,14,21),(2,14,24),(2,14,29),(0,14,35),(2,14,36),(0,3,17),(1,19,194),(2,17,19),(2,17,20),(2,17,21),(2,17,29),(1,18,19),(1,18,20),(1,18,21),(1,18,29),(3,18,33),(2,1,103),(2,1,93),(1,2,81),(2,2,81),(1,19,81),(3,19,45),(3,20,45),(3,21,33),(3,21,35),(1,21,36),(3,21,45),(2,1,79),(1,24,29),(3,24,33),(1,29,81),(3,29,45),(2,0,80),(2,0,94),(2,1,101)]
def h0W : BT Decor := buildWiresBT 8 h0Base h0Steps
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
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,8),some (subcubeFast 0 2,9),some (subcubeFast 0 4,8),some (subcubeFast 0 8,9),some (subcubeFast 0 10,5),some (subcubeFast 0 16,7),some (subcubeFast 0 18,5),some (subcubeFast 0 32,8),some (subcubeFast 0 34,5),some (subcubeFast 0 48,5),some (subcubeFast 1 0,6),some (subcubeFast 1 2,5),some (subcubeFast 1 8,5),some (subcubeFast 1 10,4),some (subcubeFast 1 32,5),some (subcubeFast 1 34,4),some (subcubeFast 2 0,6),some (subcubeFast 2 1,5),some (subcubeFast 4 0,8),some (subcubeFast 4 1,5),some (subcubeFast 4 2,5),some (subcubeFast 4 8,6),some (subcubeFast 4 16,5),some (subcubeFast 4 18,4),some (subcubeFast 4 32,5),some (subcubeFast 4 48,4),some (subcubeFast 8 0,8),some (subcubeFast 8 1,5),some (subcubeFast 8 4,5),some (subcubeFast 8 16,5),some (subcubeFast 8 32,5),some (subcubeFast 8 48,4),some (subcubeFast 16 0,9),some (subcubeFast 16 1,7),some (subcubeFast 16 2,6),some (subcubeFast 16 4,6),some (subcubeFast 16 8,6),some (subcubeFast 16 32,6),some (subcubeFast 18 0,5),some (subcubeFast 18 1,4),some (subcubeFast 20 0,5),some (subcubeFast 20 1,4),some (subcubeFast 24 1,4),some (subcubeFast 32 0,9),some (subcubeFast 32 1,5),some (subcubeFast 32 4,5),some (subcubeFast 32 8,6),some (subcubeFast 32 16,4),some (subcubeFast 34 0,5),some (subcubeFast 34 1,4),some (subcubeFast 40 0,5),some (subcubeFast 40 4,4),some (subcubeFast 48 0,5),some (subcubeFast 48 1,4)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 6 h0SliceList
def h0Specs : List PoolSpec := [(1,[]),(0,[]),(1,[(0,0,2)]),(18,[(0,0,1)]),(10,[]),(3,[(0,0,1),(0,0,2)]),(32,[(0,0,1),(0,0,2)]),(43,[(0,0,1),(0,0,2)]),(0,[(2,1,8)]),(3,[(0,0,1),(0,0,2),(2,1,8)]),(32,[(0,0,1),(0,0,2),(2,1,8)]),(43,[(0,0,1),(0,0,2),(2,1,8)]),(18,[]),(33,[(2,1,8)]),(12,[]),(3,[(0,0,2),(2,1,8)]),(16,[]),(1,[(0,0,2),(1,4,6)]),(0,[(2,1,8),(1,4,6)]),(32,[(0,0,2),(2,1,8),(0,0,1)]),(18,[(0,0,1),(1,4,6)]),(21,[(0,0,1),(1,4,6)]),(5,[(0,0,2),(2,1,8)]),(14,[]),(7,[(0,0,2),(2,1,8)]),(2,[]),(33,[]),(26,[(0,0,2)]),(3,[(0,0,2)]),(3,[(0,0,1)]),(26,[(0,0,1)]),(32,[(0,0,2)]),(0,[(1,4,6)]),(3,[(0,0,2),(0,0,1),(1,4,6)]),(43,[(0,0,2),(0,0,1),(1,4,6)]),(32,[(0,0,2),(0,0,1)]),(1,[(1,4,6)]),(3,[(0,0,1),(1,4,6)]),(26,[(0,0,1),(1,4,6)]),(5,[(0,0,2)]),(43,[(0,0,1),(1,4,6)]),(7,[(0,0,1),(1,4,6)]),(38,[]),(32,[(0,0,1)]),(43,[(0,0,2)]),(7,[(0,0,2)]),(43,[(0,0,1)]),(7,[(0,0,1)]),(2,[(0,0,1)]),(1,[(2,0,2)]),(3,[(0,0,1),(2,0,2)]),(32,[(0,0,1),(2,0,2)]),(43,[(0,0,1),(2,0,2)]),(0,[(2,1,10)]),(3,[(0,0,1),(2,0,2),(2,1,10)]),(32,[(0,0,1),(2,0,2),(2,1,10)]),(43,[(0,0,1),(2,0,2),(2,1,10)]),(18,[(0,0,1),(2,1,10)]),(33,[(2,1,10)]),(26,[(2,0,2)]),(3,[(2,0,2)]),(32,[(2,0,2)]),(1,[(2,0,2),(1,4,6)]),(3,[(2,0,2),(0,0,1),(1,4,6)]),(43,[(2,0,2),(0,0,1),(1,4,6)]),(32,[(2,0,2),(0,0,1)]),(2,[(0,0,1),(1,4,6)]),(5,[(2,0,2)]),(43,[(2,0,2)]),(7,[(2,0,2)]),(1,[(0,0,3)]),(32,[(0,0,1),(0,0,3)]),(43,[(0,0,1),(0,0,3)]),(0,[(2,1,12)]),(3,[(0,0,1),(2,1,12)]),(32,[(0,0,1),(0,0,3),(2,1,12)]),(43,[(0,0,1),(0,0,3),(2,1,12)]),(33,[(2,1,12)]),(2,[(0,0,3),(2,1,12)]),(26,[]),(0,[(1,4,6),(2,1,12)]),(1,[(1,4,6),(0,0,3)]),(3,[(0,0,1),(1,4,6),(2,1,12)]),(5,[(0,0,3),(2,1,12)]),(7,[(0,0,3),(2,1,12)]),(18,[(0,0,3)]),(2,[(0,0,3)]),(3,[]),(32,[(0,0,3)]),(1,[(0,0,3),(1,4,6)]),(43,[(0,0,3),(0,0,1),(1,4,6)]),(32,[(0,0,3),(0,0,1)]),(29,[]),(5,[(0,0,3)]),(43,[(0,0,3)]),(7,[(0,0,3)]),(1,[(2,0,5)]),(3,[(0,0,1),(2,0,5)]),(32,[(0,0,1),(2,0,5)]),(0,[(2,1,18)]),(3,[(0,0,1),(2,0,5),(2,1,18)]),(32,[(0,0,1),(2,0,5),(2,1,18)]),(43,[(0,0,1),(2,1,18)]),(33,[(2,1,18)]),(0,[(1,4,6),(2,1,18)]),(43,[(0,0,1),(1,4,6),(2,1,18)]),(1,[(1,4,6),(2,0,5)]),(5,[(2,0,5),(2,1,18)]),(7,[]),(18,[(2,0,5)]),(2,[(2,0,5)]),(26,[(2,0,5)]),(3,[(2,0,5)]),(32,[(2,0,5)]),(1,[(2,0,5),(1,4,6)]),(3,[(2,0,5),(0,0,1),(1,4,6)]),(32,[(2,0,5),(0,0,1)]),(9,[]),(5,[(2,0,5)]),(43,[]),(1,[(0,2,3)]),(0,[(0,2,3)]),(32,[(0,0,1),(0,2,3)]),(33,[(0,2,3)]),(43,[(0,0,1),(0,2,3)]),(23,[]),(32,[(0,2,3)]),(1,[(0,2,3),(1,4,6)]),(0,[(0,2,3),(1,4,6)]),(43,[(0,2,3),(0,0,1),(1,4,6)]),(32,[(0,2,3),(0,0,1)]),(5,[(0,2,3)]),(22,[]),(5,[]),(25,[]),(1,[(1,4,6),(0,2,3),(1,6,29)]),(0,[(1,4,6),(0,2,3),(1,6,29)]),(3,[(0,0,1),(1,4,6),(1,6,29)]),(5,[(0,0,1)]),(1,[(0,2,3),(2,4,6)]),(0,[(0,2,3),(2,4,6)]),(18,[(0,0,1),(2,4,6)]),(0,[(2,4,6)]),(1,[(2,4,6)]),(3,[(0,0,1),(2,4,6)]),(43,[(0,2,3),(0,0,1),(2,4,6)]),(37,[(0,2,3)]),(43,[(0,0,1),(2,4,6)]),(7,[(0,0,1),(2,4,6)]),(1,[(2,4,6),(0,2,3),(1,6,29)]),(0,[(2,4,6),(0,2,3),(1,6,29)]),(3,[(0,0,1),(2,4,6),(1,6,29)]),(2,[(0,0,1),(2,4,6)]),(32,[]),(41,[]),(1,[(0,2,3),(1,4,29)]),(0,[(0,2,3),(1,4,29)]),(3,[(0,0,1),(1,4,29)]),(2,[(1,4,29)]),(3,[(1,4,29)]),(43,[(0,2,3),(1,4,29)]),(7,[(0,2,3),(1,4,29)]),(6,[]),(40,[]),(43,[(0,2,3)]),(7,[(0,2,3)]),(43,[(0,2,3),(0,0,1)]),(18,[(0,0,1),(1,5,6)]),(19,[]),(48,[]),(1,[(0,2,3),(1,6,29)]),(0,[(0,2,3),(1,6,29)]),(3,[(0,0,1),(1,6,29)]),(32,[(0,0,1),(0,2,3),(1,6,29)]),(33,[(0,2,3),(1,6,29)]),(43,[(0,0,1),(0,2,3),(1,6,29)]),(1,[(0,2,3),(2,6,29)]),(0,[(0,2,3),(2,6,29)]),(3,[(0,0,1),(2,6,29)]),(32,[(0,0,1),(0,2,3),(2,6,29)]),(33,[(0,2,3),(2,6,29)]),(43,[(0,0,1),(0,2,3),(2,6,29)]),(1,[(3,2,3)]),(0,[(3,2,3)]),(32,[(0,0,1),(3,2,3)]),(33,[(3,2,3)]),(43,[(0,0,1),(3,2,3)]),(5,[(3,2,3)]),(3,[(1,4,5)]),(26,[(1,4,5)]),(32,[(3,2,3)]),(2,[(1,4,5)]),(21,[(1,4,5)]),(7,[(3,2,3)]),(21,[]),(21,[(0,0,1)]),(1,[(3,2,3),(1,4,6)]),(0,[(3,2,3),(1,4,6)]),(43,[(3,2,3),(0,0,1),(1,4,6)]),(32,[(3,2,3),(0,0,1)]),(1,[(1,4,6),(3,2,3),(1,6,32)]),(0,[(1,4,6),(3,2,3),(1,6,32)]),(3,[(0,0,1),(1,4,6),(1,6,32)]),(1,[(3,2,3),(2,4,6)]),(0,[(3,2,3),(2,4,6)]),(26,[(0,0,1),(2,4,6)]),(43,[(3,2,3),(0,0,1),(2,4,6)]),(37,[(3,2,3)]),(3,[(0,0,1),(2,4,6),(1,6,32)]),(32,[(0,0,1),(3,2,3),(1,6,32)]),(35,[(0,0,1)]),(1,[(3,2,3),(1,4,32)]),(0,[(3,2,3),(1,4,32)]),(18,[(1,4,32)]),(3,[(0,0,1),(1,4,32)]),(3,[(1,4,32)]),(43,[(3,2,3),(1,4,32)]),(7,[(3,2,3),(1,4,32)]),(35,[]),(43,[(3,2,3)]),(3,[(0,0,1),(1,5,6)]),(26,[(0,0,1),(1,5,6)]),(43,[(3,2,3),(0,0,1)]),(2,[(0,0,1),(1,5,6)]),(27,[]),(1,[(3,2,3),(1,6,32)]),(0,[(3,2,3),(1,6,32)]),(3,[(0,0,1),(1,6,32)]),(18,[(0,0,1),(1,6,32)]),(43,[(0,0,1),(3,2,3),(1,6,32)]),(1,[(1,2,4)]),(0,[(1,2,4)]),(3,[(0,0,1),(1,2,4)]),(43,[(0,0,1),(1,2,4)]),(18,[(0,0,1),(0,1,33)]),(0,[(1,2,4),(0,1,33)]),(33,[(0,1,33)]),(3,[(0,0,1),(1,2,4),(0,1,33)]),(32,[(0,0,1),(0,1,33)]),(43,[(0,0,1),(1,2,4),(0,1,33)]),(1,[(2,3,5)]),(3,[(1,2,4)]),(26,[(1,2,4)]),(5,[(2,3,5)]),(32,[(2,3,5)]),(2,[(2,3,5)]),(46,[]),(46,[(1,2,4)]),(46,[(0,0,1)]),(1,[(2,3,6)]),(3,[(1,2,4),(0,0,1)]),(32,[(0,0,1),(2,3,6)]),(2,[(0,0,1),(2,3,6)]),(1,[(1,2,4),(1,4,6)]),(0,[(1,2,4),(1,4,6)]),(3,[(1,2,4),(0,0,1),(1,4,6)]),(43,[(1,2,4),(0,0,1),(1,4,6)]),(1,[(1,4,6),(1,2,4),(3,6,33)]),(0,[(1,4,6),(1,2,4),(3,6,33)]),(18,[(0,0,1),(3,6,33)]),(32,[(0,0,1),(3,6,33)]),(43,[(1,2,4)]),(7,[(1,2,4)]),(1,[(1,5,6)]),(32,[(0,0,1),(1,5,6)]),(43,[(1,2,4),(0,0,1)]),(44,[]),(1,[(1,2,4),(0,0,89)]),(18,[(0,1,33),(0,0,89)]),(2,[(0,0,89)]),(3,[(1,2,4),(0,1,33),(0,0,89)]),(32,[(0,1,33),(0,0,89)]),(43,[(1,2,4),(0,1,33),(0,0,89)]),(1,[(1,2,4),(3,6,33)]),(0,[(1,2,4),(3,6,33)]),(33,[(3,6,33)]),(3,[(0,0,1),(1,2,4),(3,6,33)]),(43,[(0,0,1),(1,2,4),(3,6,33)]),(1,[(2,2,4)]),(0,[(2,2,4)]),(3,[(0,0,1),(2,2,4)]),(43,[(0,0,1),(2,2,4)]),(1,[(2,2,4),(2,3,4)]),(0,[(2,2,4),(2,3,4)]),(18,[(0,0,1),(2,3,4)]),(18,[(2,3,4)]),(2,[(2,3,4)]),(26,[(0,0,1),(2,2,4)]),(26,[(2,2,4)]),(3,[(2,2,4)]),(43,[(2,2,4),(2,3,4)]),(7,[(2,2,4),(2,3,4)]),(26,[(0,0,1),(2,2,4),(1,6,34)]),(36,[]),(18,[(0,0,1),(2,3,4),(1,6,39)]),(18,[(2,3,5)]),(35,[(2,3,5)]),(46,[(2,2,4)]),(3,[(2,2,4),(0,0,1)]),(18,[(0,0,1),(2,3,6)]),(32,[(0,0,1),(1,6,34)]),(1,[(2,2,4),(1,4,6)]),(0,[(2,2,4),(1,4,6)]),(3,[(2,2,4),(0,0,1),(1,4,6)]),(43,[(2,2,4),(0,0,1),(1,4,6)]),(1,[(1,4,6),(2,2,4),(1,6,34)]),(0,[(1,4,6),(2,2,4),(1,6,34)]),(2,[(0,0,1),(1,6,34)]),(43,[(2,2,4)]),(7,[(2,2,4)]),(43,[(2,2,4),(0,0,1)]),(1,[(2,2,4),(1,6,34)]),(0,[(2,2,4),(1,6,34)]),(3,[(0,0,1),(2,2,4),(1,6,34)]),(43,[(0,0,1),(2,2,4),(1,6,34)]),(1,[(1,2,5)]),(0,[(1,2,5)]),(3,[(0,0,1),(1,2,5)]),(32,[(0,0,1),(1,2,5)]),(33,[(1,2,5)]),(18,[(0,0,1),(0,1,35)]),(0,[(1,2,5),(0,1,35)]),(17,[]),(3,[(0,0,1),(1,2,5),(0,1,35)]),(32,[(0,0,1),(1,2,5),(0,1,35)]),(33,[(1,2,5),(0,1,35)]),(43,[(0,0,1),(0,1,35)]),(26,[(1,2,5),(0,1,35)]),(18,[(0,0,1),(1,4,6),(0,1,35)]),(0,[(1,4,6),(1,2,5),(0,1,35)]),(43,[(0,0,1),(1,4,6),(0,1,35)]),(1,[(1,4,6),(1,2,5)]),(5,[(1,2,5),(0,1,35)]),(1,[(2,3,4)]),(5,[(1,2,5)]),(32,[(1,2,5)]),(7,[(2,3,4)]),(43,[(2,3,4)]),(26,[(1,2,5)]),(36,[(1,2,5)]),(36,[(0,0,1)]),(3,[(1,2,5)]),(1,[(1,2,5),(1,4,6)]),(0,[(1,2,5),(1,4,6)]),(3,[(1,2,5),(0,0,1),(1,4,6)]),(32,[(1,2,5),(0,0,1)]),(1,[(1,2,5),(3,4,35)]),(0,[(1,2,5),(3,4,35)]),(18,[(3,4,35)]),(26,[(1,2,5),(3,4,35)]),(3,[(1,2,5),(3,4,35)]),(43,[(0,0,1),(3,4,35)]),(43,[(3,4,35)]),(1,[(1,2,5),(0,0,111)]),(18,[(0,1,35),(0,0,111)]),(2,[(0,0,111)]),(3,[(1,2,5),(0,1,35),(0,0,111)]),(32,[(1,2,5),(0,1,35),(0,0,111)]),(43,[(0,1,35),(0,0,111)]),(7,[(0,0,111)]),(1,[(1,2,5),(3,6,35)]),(18,[(0,0,1),(3,6,35)]),(0,[(1,2,5),(3,6,35)]),(3,[(0,0,1),(1,2,5),(3,6,35)]),(32,[(0,0,1),(1,2,5),(3,6,35)]),(33,[(1,2,5),(3,6,35)]),(43,[(0,0,1),(3,6,35)]),(1,[(2,2,5)]),(0,[(2,2,5)]),(3,[(0,0,1),(2,2,5)]),(32,[(0,0,1),(2,2,5)]),(33,[(2,2,5)]),(26,[(2,2,5)]),(3,[(2,2,5)]),(32,[(2,2,5)]),(1,[(2,2,5),(1,4,6)]),(0,[(2,2,5),(1,4,6)]),(3,[(2,2,5),(0,0,1),(1,4,6)]),(32,[(2,2,5),(0,0,1)]),(5,[(2,2,5)]),(1,[(2,2,5),(1,4,36)]),(0,[(2,2,5),(1,4,36)]),(43,[(0,0,1),(1,4,36)]),(2,[(1,4,36)]),(26,[(2,2,5),(1,4,36)]),(3,[(2,2,5),(1,4,36)]),(43,[(1,4,36)]),(37,[]),(37,[(0,0,1)]),(1,[(2,2,5),(1,6,36)]),(0,[(2,2,5),(1,6,36)]),(3,[(0,0,1),(2,2,5),(1,6,36)]),(32,[(0,0,1),(2,2,5),(1,6,36)]),(33,[(2,2,5),(1,6,36)]),(43,[(0,0,1),(1,6,36)]),(1,[(2,2,5),(2,6,36)]),(0,[(2,2,5),(2,6,36)]),(3,[(0,0,1),(2,2,5),(2,6,36)]),(32,[(0,0,1),(2,2,5),(2,6,36)]),(33,[(2,2,5),(2,6,36)]),(43,[(0,0,1),(2,6,36)]),(0,[(0,1,8)]),(33,[(0,1,8)]),(1,[(0,0,2),(1,2,6)]),(0,[(0,1,8),(1,2,6)]),(33,[(0,1,8),(1,2,6)]),(3,[(0,0,1),(1,2,6)]),(2,[(0,1,8)]),(2,[(0,0,111),(1,5,112)]),(7,[(0,0,1),(1,2,6)]),(35,[(0,0,111),(1,5,112)]),(1,[(0,0,2),(1,2,6),(3,25,37)]),(0,[(0,1,8),(1,2,6),(3,25,37)]),(33,[(0,1,8),(1,2,6),(3,25,37)]),(3,[(0,0,2),(0,1,8)]),(1,[(0,0,2),(2,3,25)]),(0,[(0,1,8),(2,3,25)]),(33,[(0,1,8),(2,3,25)]),(2,[(0,1,8),(2,3,25)]),(32,[(0,0,2),(0,1,8),(2,3,25)]),(1,[(1,4,6),(0,0,2),(2,3,25)]),(0,[(1,4,6),(0,1,8),(2,3,25)]),(1,[(2,4,6),(0,0,2),(2,3,25)]),(0,[(2,4,6),(0,1,8),(2,3,25)]),(43,[(0,0,2),(0,1,8),(2,3,25)]),(2,[(0,0,1),(2,3,25)]),(32,[(0,0,2),(0,1,8)]),(0,[(0,1,8),(1,4,6)]),(1,[(1,4,6),(2,0,2)]),(1,[(0,0,2),(2,4,6)]),(0,[(0,1,8),(2,4,6)]),(21,[(0,0,1),(2,4,6)]),(1,[(0,0,2),(2,4,6),(1,25,54)]),(0,[(0,1,8),(2,4,6),(1,25,54)]),(33,[(0,33,46)]),(1,[(1,2,4),(1,4,6),(0,33,46)]),(32,[(0,0,1),(0,33,46)]),(43,[(0,0,2),(0,1,8)]),(1,[(1,2,5),(0,0,111),(1,5,112)]),(2,[(0,0,1),(1,5,112)]),(1,[(1,2,6)]),(0,[(1,2,6)]),(32,[(0,0,1),(1,2,6)]),(33,[(1,2,6)]),(43,[(0,0,1),(1,2,6)]),(26,[(0,0,1),(1,2,6)]),(3,[(0,0,1),(1,2,6),(1,6,39)]),(32,[(0,0,1),(1,6,39)]),(28,[]),(1,[(1,2,6),(1,4,6)]),(0,[(1,2,6),(1,4,6)]),(3,[(0,0,1),(1,2,6),(1,4,6)]),(43,[(0,0,1),(1,2,6),(1,4,6)]),(1,[(1,2,6),(2,4,6)]),(0,[(1,2,6),(2,4,6)]),(3,[(0,0,1),(1,2,6),(2,4,6)]),(43,[(0,0,1),(1,2,6),(2,4,6)]),(1,[(1,2,6),(3,4,6)]),(0,[(1,2,6),(3,4,6)]),(2,[(0,0,1),(3,4,6)]),(1,[(3,4,6)]),(0,[(3,4,6)]),(3,[(0,0,1),(1,2,6),(3,4,6)]),(26,[(0,0,1),(3,4,6)]),(3,[(0,0,1),(3,4,6)]),(43,[(0,0,1),(3,4,6)]),(7,[(0,0,1),(3,4,6)]),(33,[(1,6,34)]),(1,[(2,2,4),(1,6,34),(3,4,105)]),(18,[(0,0,1),(3,4,105)]),(45,[]),(1,[(1,2,6),(1,5,6)]),(0,[(1,2,6),(1,5,6)]),(0,[(1,5,6)]),(3,[(0,0,1),(1,2,6),(1,5,6)]),(1,[(1,2,6),(3,5,6)]),(0,[(1,2,6),(3,5,6)]),(2,[(0,0,1),(3,5,6)]),(1,[(3,5,6)]),(0,[(3,5,6)]),(3,[(0,0,1),(1,2,6),(3,5,6)]),(26,[(0,0,1),(3,5,6)]),(3,[(0,0,1),(3,5,6)]),(32,[(0,0,1),(3,5,6)]),(1,[(1,2,6),(3,5,6),(1,4,57)]),(0,[(1,2,6),(3,5,6),(1,4,57)]),(2,[(0,0,1),(3,5,6),(1,4,57)]),(1,[(3,5,6),(1,4,57)]),(0,[(3,5,6),(1,4,57)]),(43,[(0,0,1),(1,2,6),(1,4,57)]),(37,[(0,0,1),(1,2,6)]),(26,[(0,0,1),(3,5,6),(1,4,57)]),(3,[(0,0,1),(3,5,6),(1,4,57)]),(43,[(0,0,1),(1,4,57)]),(1,[(1,2,6),(3,5,6),(2,37,57)]),(43,[(0,0,1),(1,2,6),(2,37,57)]),(1,[(2,2,6)]),(0,[(2,2,6)]),(3,[(0,0,1),(2,2,6)]),(32,[(0,0,1),(2,2,6)]),(33,[(2,2,6)]),(43,[(0,0,1),(2,2,6)]),(18,[(0,0,26)]),(1,[(0,0,2),(0,0,26),(2,2,6)]),(0,[(2,1,8),(2,2,6)]),(33,[(2,1,8),(2,2,6)]),(21,[(0,0,26)]),(7,[(0,0,1),(2,2,6)]),(18,[(0,0,1),(0,3,6)]),(1,[(0,3,6)]),(0,[(0,3,6)]),(26,[(0,0,1),(2,2,6)]),(1,[(2,2,6),(0,3,6)]),(32,[(0,0,1),(0,3,6)]),(43,[(0,0,1),(0,3,6)]),(7,[(0,0,1),(0,3,6)]),(24,[]),(1,[(2,2,6),(0,3,6),(1,38,42)]),(3,[(0,0,1),(2,2,6),(1,38,42)]),(0,[(2,3,6)]),(1,[(2,2,6),(2,3,6)]),(43,[(0,0,1),(2,3,6)]),(7,[(0,0,1),(2,3,6)]),(1,[(2,2,6),(1,4,6)]),(0,[(2,2,6),(1,4,6)]),(3,[(0,0,1),(2,2,6),(1,4,6)]),(43,[(0,0,1),(2,2,6),(1,4,6)]),(1,[(2,2,6),(2,4,6)]),(0,[(2,2,6),(2,4,6)]),(3,[(0,0,1),(2,2,6),(2,4,6)]),(43,[(0,0,1),(2,2,6),(2,4,6)]),(1,[(1,2,4),(3,6,33),(1,4,96)]),(2,[(0,0,1),(1,4,96)]),(47,[]),(1,[(0,0,2),(0,0,26)]),(1,[(0,0,2),(0,0,26),(1,4,6)]),(18,[(0,0,26),(1,4,6)]),(33,[(3,34,46)]),(1,[(2,2,4),(1,4,6),(3,34,46)]),(32,[(0,0,1),(3,34,46)]),(0,[(2,3,4)]),(43,[(0,0,1),(2,3,4)]),(1,[(2,3,4),(1,4,6)]),(0,[(2,3,4),(1,4,6)]),(43,[(2,3,4),(0,0,1),(1,4,6)]),(1,[(1,4,6),(2,3,4),(1,6,39)]),(0,[(1,4,6),(2,3,4),(1,6,39)]),(3,[(0,0,1),(1,4,6),(1,6,39)]),(3,[(0,0,1),(1,6,39)]),(43,[(2,3,4),(0,0,1)]),(1,[(2,3,4),(1,6,39)]),(0,[(2,3,4),(1,6,39)]),(43,[(0,0,1),(2,3,4),(1,6,39)]),(0,[(2,3,5)]),(32,[(0,0,1),(2,3,5)]),(33,[(2,3,5)]),(1,[(2,3,5),(1,4,6)]),(0,[(2,3,5),(1,4,6)]),(32,[(2,3,5),(0,0,1)]),(1,[(2,3,5),(1,4,41)]),(0,[(2,3,5),(1,4,41)]),(18,[(2,3,5),(1,4,41)]),(2,[(2,3,5),(1,4,41)]),(3,[(0,0,1),(1,4,41)]),(3,[(1,4,41)]),(43,[(0,0,1),(1,4,41)]),(43,[(1,4,41)]),(33,[(0,3,6)]),(1,[(0,3,6),(2,0,42)]),(3,[(0,0,1),(2,0,42)]),(32,[(0,0,1),(0,3,6),(2,0,42)]),(43,[(0,0,1),(0,3,6),(2,0,42)]),(1,[(0,3,6),(1,2,42)]),(0,[(0,3,6),(1,2,42)]),(3,[(0,0,1),(1,2,42)]),(32,[(0,0,1),(0,3,6),(1,2,42)]),(33,[(0,3,6),(1,2,42)]),(43,[(0,0,1),(0,3,6),(1,2,42)]),(1,[(1,4,6),(0,3,6),(1,2,42)]),(3,[(0,0,1),(1,4,6),(1,2,42)]),(0,[(1,4,6),(0,3,6),(1,2,42)]),(7,[(0,0,1),(0,3,6),(1,2,42)]),(1,[(0,3,6),(2,2,42)]),(0,[(0,3,6),(2,2,42)]),(3,[(0,0,1),(2,2,42)]),(32,[(0,0,1),(0,3,6),(2,2,42)]),(33,[(0,3,6),(2,2,42)]),(43,[(0,0,1),(0,3,6),(2,2,42)]),(1,[(1,4,6),(0,3,6),(2,2,42)]),(3,[(0,0,1),(1,4,6),(2,2,42)]),(0,[(1,4,6),(0,3,6),(2,2,42)]),(1,[(2,4,6),(0,3,6),(2,2,42)]),(3,[(0,0,1),(2,4,6),(2,2,42)]),(0,[(2,4,6),(0,3,6),(2,2,42)]),(1,[(0,3,6),(1,4,6)]),(0,[(0,3,6),(1,4,6)]),(43,[(0,0,1),(0,3,6),(1,4,6)]),(1,[(1,4,6),(0,3,6),(1,5,42)]),(0,[(1,4,6),(0,3,6),(1,5,42)]),(3,[(0,0,1),(1,4,6),(1,5,42)]),(32,[(0,0,1),(0,3,6),(1,5,42)]),(43,[(0,0,1),(1,4,6),(0,3,6)]),(1,[(0,3,6),(2,4,6)]),(0,[(0,3,6),(2,4,6)]),(43,[(0,0,1),(0,3,6),(2,4,6)]),(1,[(0,3,6),(2,4,6),(1,42,54)]),(0,[(0,3,6),(2,4,6),(1,42,54)]),(3,[(0,0,1),(2,4,6),(1,42,54)]),(1,[(0,3,6),(1,4,42)]),(0,[(0,3,6),(1,4,42)]),(3,[(0,0,1),(1,4,42)]),(43,[(0,0,1),(0,3,6),(1,4,42)]),(1,[(0,3,6),(1,5,42)]),(0,[(0,3,6),(1,5,42)]),(3,[(0,0,1),(1,5,42)]),(33,[(0,3,6),(1,5,42)]),(33,[(2,3,6)]),(1,[(2,3,6),(1,4,6)]),(0,[(2,3,6),(1,4,6)]),(43,[(0,0,1),(2,3,6),(1,4,6)]),(1,[(2,3,6),(2,4,6)]),(0,[(2,3,6),(2,4,6)]),(43,[(0,0,1),(2,3,6),(2,4,6)]),(30,[]),(1,[(1,4,5)]),(0,[(1,4,5)]),(3,[(0,0,1),(1,4,5)]),(33,[(0,1,45)]),(0,[(1,4,5),(0,1,45)]),(3,[(0,0,1),(1,4,5),(0,1,45)]),(32,[(0,0,1),(0,1,45)]),(43,[(0,0,1),(0,1,45)]),(18,[(1,4,5)]),(1,[(1,4,5),(0,0,82)]),(3,[(1,4,5),(0,1,45),(0,0,82)]),(32,[(0,1,45),(0,0,82)]),(43,[(0,1,45),(0,0,82)]),(1,[(1,4,5),(3,6,45)]),(33,[(3,6,45)]),(0,[(1,4,5),(3,6,45)]),(3,[(0,0,1),(1,4,5),(3,6,45)]),(32,[(0,0,1),(3,6,45)]),(43,[(0,0,1),(3,6,45)]),(1,[(1,4,6),(0,2,46)]),(0,[(1,4,6),(0,2,46)]),(3,[(0,0,1),(1,4,6),(0,2,46)]),(43,[(0,0,1),(1,4,6),(0,2,46)]),(32,[(0,0,1),(0,2,46)]),(1,[(1,4,6),(0,2,46),(2,3,47)]),(0,[(1,4,6),(0,2,46),(2,3,47)]),(39,[]),(9,[(2,3,47)]),(32,[(0,0,1),(0,2,46),(2,3,47)]),(5,[(2,3,47)]),(2,[(0,0,1),(1,4,6),(2,3,47)]),(1,[(1,4,6),(0,2,46),(1,5,47)]),(0,[(1,4,6),(0,2,46),(1,5,47)]),(32,[(0,0,1),(0,2,46),(1,5,47)]),(5,[(1,5,47)]),(2,[(0,0,1),(1,4,6),(1,5,47)]),(1,[(1,4,6),(3,2,46)]),(0,[(1,4,6),(3,2,46)]),(3,[(0,0,1),(1,4,6),(3,2,46)]),(43,[(0,0,1),(1,4,6),(3,2,46)]),(32,[(0,0,1),(3,2,46)]),(1,[(1,4,6),(0,3,46)]),(0,[(1,4,6),(0,3,46)]),(43,[(0,0,1),(1,4,6),(0,3,46)]),(32,[(0,0,1),(0,3,46)]),(1,[(1,4,6),(3,5,46)]),(0,[(1,4,6),(3,5,46)]),(3,[(0,0,1),(1,4,6),(3,5,46)]),(32,[(0,0,1),(3,5,46)]),(1,[(1,4,6),(1,2,46)]),(0,[(1,4,6),(1,2,46)]),(3,[(0,0,1),(1,4,6),(1,2,46)]),(43,[(0,0,1),(1,4,6),(1,2,46)]),(32,[(0,0,1),(1,2,46)]),(1,[(1,4,6),(2,2,46)]),(0,[(1,4,6),(2,2,46)]),(3,[(0,0,1),(1,4,6),(2,2,46)]),(43,[(0,0,1),(1,4,6),(2,2,46)]),(32,[(0,0,1),(2,2,46)]),(1,[(1,4,6),(2,3,46)]),(0,[(1,4,6),(2,3,46)]),(43,[(0,0,1),(1,4,6),(2,3,46)]),(32,[(0,0,1),(2,3,46)]),(1,[(1,4,6),(1,5,6)]),(0,[(1,4,6),(1,5,6)]),(3,[(0,0,1),(1,4,6),(1,5,6)]),(1,[(1,4,6),(3,5,6)]),(0,[(1,4,6),(3,5,6)]),(3,[(0,0,1),(1,4,6),(3,5,6)]),(1,[(1,4,6),(3,5,6),(2,46,57)]),(0,[(1,4,6),(3,5,6),(2,46,57)]),(43,[(0,0,1),(1,4,6),(2,46,57)]),(32,[(0,0,1),(3,5,6),(2,46,57)]),(34,[]),(33,[(1,5,6)]),(33,[(3,5,6)]),(1,[(3,5,6),(2,0,57)]),(43,[(0,0,1),(2,0,57)]),(3,[(0,0,1),(3,5,6),(2,0,57)]),(32,[(0,0,1),(3,5,6),(2,0,57)]),(3,[(3,0,1)]),(32,[(3,0,1)]),(43,[(3,0,1)]),(32,[(3,0,1),(0,2,3)]),(43,[(3,0,1),(0,2,3)]),(18,[(3,0,1)]),(11,[]),(0,[(0,2,3),(2,1,29)]),(3,[(3,0,1),(2,1,29)]),(32,[(3,0,1),(0,2,3),(2,1,29)]),(43,[(3,0,1),(0,2,3),(2,1,29)]),(33,[(0,2,3),(2,1,29)]),(7,[(3,0,1)]),(1,[(0,2,3),(1,7,29)]),(3,[(3,0,1),(1,7,29)]),(32,[(3,0,1),(0,2,3),(1,7,29)]),(43,[(3,0,1),(0,2,3),(1,7,29)]),(32,[(3,0,1),(3,2,3)]),(43,[(3,0,1),(3,2,3)]),(2,[(3,0,1)]),(26,[(3,0,1)]),(42,[]),(3,[(3,0,1),(1,2,5)]),(32,[(3,0,1),(1,2,5)]),(5,[(3,0,1)]),(43,[(3,0,1),(3,4,35)]),(35,[(3,0,1)]),(1,[(1,2,5),(3,7,35)]),(3,[(3,0,1),(1,2,5),(3,7,35)]),(32,[(3,0,1),(1,2,5),(3,7,35)]),(43,[(3,0,1),(3,7,35)]),(18,[(3,0,1),(3,7,35)]),(15,[]),(3,[(3,0,1),(2,2,5)]),(32,[(3,0,1),(2,2,5)]),(1,[(2,2,5),(1,7,36)]),(3,[(3,0,1),(2,2,5),(1,7,36)]),(32,[(3,0,1),(2,2,5),(1,7,36)]),(43,[(3,0,1),(1,7,36)]),(32,[(3,0,1),(2,3,5)]),(1,[(0,0,2),(0,0,3)]),(32,[(0,0,2),(0,0,3)]),(43,[(0,0,2),(0,0,3)]),(1,[(0,0,2),(2,0,5)]),(3,[(0,0,2),(2,0,5)]),(32,[(0,0,2),(2,0,5)]),(3,[(0,0,2),(2,1,2)]),(0,[(2,1,2)]),(32,[(0,0,2),(2,1,2)]),(33,[(2,1,2)]),(43,[(0,0,2),(2,1,2)]),(0,[(0,1,3)]),(18,[(0,1,3)]),(32,[(0,0,2),(0,1,3)]),(33,[(0,1,3)]),(43,[(0,0,2),(0,1,3)]),(2,[(0,1,3)]),(32,[(0,1,3)]),(43,[(0,1,3)]),(7,[(0,1,3)]),(1,[(0,0,2),(1,8,21)]),(0,[(0,1,3),(1,8,21)]),(3,[(0,0,2),(1,8,21)]),(32,[(0,0,2),(0,1,3),(1,8,21)]),(33,[(0,1,3),(1,8,21)]),(43,[(0,0,2),(0,1,3),(1,8,21)]),(2,[(0,1,3),(1,8,21)]),(4,[]),(0,[(2,1,4)]),(18,[(2,1,4)]),(3,[(0,0,2),(2,1,4)]),(43,[(0,0,2),(2,1,4)]),(2,[(2,1,4)]),(0,[(2,1,4),(2,1,8)]),(3,[(2,1,4),(0,0,2),(2,1,8)]),(32,[(0,0,2),(2,1,8)]),(43,[(2,1,4),(0,0,2),(2,1,8)]),(2,[(2,1,4),(2,1,8)]),(3,[(2,1,4)]),(26,[(2,1,4)]),(34,[(0,0,2)]),(43,[(2,1,4)]),(7,[(2,1,4)]),(0,[(2,1,5)]),(18,[(2,1,5)]),(3,[(0,0,2),(2,1,5)]),(32,[(0,0,2),(2,1,5)]),(33,[(2,1,5)]),(2,[(2,1,5)]),(0,[(2,1,5),(2,1,8)]),(3,[(2,1,5),(0,0,2),(2,1,8)]),(32,[(2,1,5),(0,0,2),(2,1,8)]),(33,[(2,1,5),(2,1,8)]),(43,[(0,0,2),(2,1,8)]),(2,[(2,1,5),(2,1,8)]),(3,[(2,1,5)]),(26,[(2,1,5)]),(32,[(2,1,5)]),(1,[(0,0,2),(1,8,24)]),(0,[(2,1,5),(1,8,24)]),(3,[(0,0,2),(2,1,5),(1,8,24)]),(32,[(0,0,2),(2,1,5),(1,8,24)]),(33,[(2,1,5),(1,8,24)]),(43,[(0,0,2),(1,8,24)]),(2,[(2,1,5),(1,8,24)]),(2,[(2,1,8)]),(1,[(0,0,2),(2,3,4)]),(43,[(0,0,2),(2,3,4)]),(1,[(0,0,2),(2,3,5)]),(32,[(0,0,2),(2,3,5)]),(1,[(0,0,2),(1,4,5)]),(3,[(0,0,2),(1,4,5)]),(33,[(3,8,45)]),(1,[(0,0,2),(1,4,5),(3,8,45)]),(0,[(1,4,5),(3,8,45)]),(32,[(0,0,2),(3,8,45)]),(3,[(0,0,2),(1,4,5),(3,8,45)]),(43,[(0,0,2),(3,8,45)]),(2,[(1,4,5),(3,8,45)]),(1,[(0,0,2),(1,4,8)]),(0,[(1,4,8)]),(3,[(0,0,2),(1,4,8)]),(43,[(0,0,2),(1,4,8)]),(2,[(1,4,8)]),(18,[(0,1,99)]),(21,[(0,1,99)]),(1,[(1,0,2)]),(3,[(1,0,2)]),(32,[(1,0,2)]),(43,[(1,0,2)]),(32,[(1,0,2),(0,1,3)]),(43,[(1,0,2),(0,1,3)]),(26,[(1,0,2)]),(3,[(0,0,1),(1,2,6),(0,1,37)]),(18,[(0,1,3),(0,0,1)]),(26,[(0,0,1),(1,2,6),(0,1,37)]),(32,[(0,0,1),(1,2,6),(0,1,37)]),(43,[(0,0,1),(1,2,6),(0,1,37)]),(7,[(1,0,2)]),(1,[(1,0,2),(2,9,21)]),(3,[(1,0,2),(2,9,21)]),(32,[(1,0,2),(0,1,3),(2,9,21)]),(43,[(1,0,2),(0,1,3),(2,9,21)]),(18,[(0,1,3),(2,9,21)]),(3,[(1,0,2),(2,1,5)]),(32,[(1,0,2),(2,1,5)]),(1,[(1,0,2),(2,9,24)]),(3,[(1,0,2),(2,1,5),(2,9,24)]),(32,[(1,0,2),(2,1,5),(2,9,24)]),(43,[(1,0,2),(2,9,24)]),(18,[(2,1,5),(2,9,24)]),(0,[(0,1,5)]),(18,[(0,1,5),(0,0,1)]),(2,[(0,1,5)]),(33,[(0,1,5)]),(1,[(1,3,5),(1,2,6)]),(0,[(1,3,5)]),(1,[(1,3,5)]),(2,[(1,3,5)]),(33,[(1,3,5)]),(32,[(1,3,5)]),(5,[(1,3,5)]),(50,[]),(1,[(2,3,5),(1,2,6)]),(1,[(1,2,6),(1,3,125)]),(0,[(1,3,125)]),(2,[(1,3,125)]),(33,[(1,3,125)]),(1,[(1,2,6),(2,3,125)]),(0,[(2,3,125)]),(2,[(2,3,125)]),(33,[(2,3,125)]),(1,[(1,0,2),(2,3,5)]),(32,[(1,0,2),(2,3,5)]),(1,[(2,0,2),(0,0,3)]),(32,[(2,0,2),(0,0,3)]),(43,[(2,0,2),(0,0,3)]),(1,[(2,0,2),(2,0,5)]),(3,[(2,0,2),(2,0,5)]),(32,[(2,0,2),(2,0,5)]),(3,[(2,0,2),(0,1,2)]),(0,[(0,1,2)]),(32,[(2,0,2),(0,1,2)]),(33,[(0,1,2)]),(43,[(2,0,2),(0,1,2)]),(26,[(2,0,2),(0,1,2)]),(1,[(2,0,2),(2,3,4)]),(16,[(2,0,2)]),(7,[(2,0,2),(0,1,2)]),(32,[(2,0,2),(0,1,3)]),(43,[(2,0,2),(0,1,3)]),(13,[]),(1,[(2,0,2),(1,10,21)]),(18,[(0,1,3),(1,10,21)]),(0,[(0,1,3),(1,10,21)]),(3,[(2,0,2),(1,10,21)]),(32,[(2,0,2),(0,1,3),(1,10,21)]),(33,[(0,1,3),(1,10,21)]),(43,[(2,0,2),(0,1,3),(1,10,21)]),(3,[(2,0,2),(2,1,4)]),(43,[(2,0,2),(2,1,4)]),(34,[(2,0,2)]),(3,[(2,0,2),(2,1,5)]),(32,[(2,0,2),(2,1,5)]),(51,[]),(18,[(2,1,5),(1,4,24)]),(0,[(2,1,5),(1,4,24)]),(1,[(2,0,2),(1,4,24)]),(2,[(2,1,5),(1,4,24)]),(1,[(1,4,24)]),(3,[(2,1,5),(1,4,24)]),(26,[(2,1,5),(1,4,24)]),(43,[(2,0,2),(1,4,24)]),(43,[(1,4,24)]),(37,[(2,0,2)]),(1,[(2,0,2),(1,10,24)]),(18,[(2,1,5),(1,10,24)]),(0,[(2,1,5),(1,10,24)]),(3,[(2,0,2),(2,1,5),(1,10,24)]),(32,[(2,0,2),(2,1,5),(1,10,24)]),(33,[(2,1,5),(1,10,24)]),(43,[(2,0,2),(1,10,24)]),(18,[(2,1,10)]),(3,[(2,0,2),(2,1,10)]),(32,[(2,0,2),(2,1,10)]),(43,[(2,0,2),(2,1,10)]),(1,[(2,3,4),(2,0,2)]),(26,[(2,0,2),(2,1,10)]),(18,[(2,3,4),(2,1,10)]),(7,[(2,0,2),(2,1,10)]),(43,[(2,0,2),(2,3,4)]),(18,[(2,3,4),(2,1,39)]),(0,[(2,3,4),(2,1,39)]),(3,[(2,0,2),(2,1,39)]),(32,[(2,0,2),(2,1,39)]),(2,[(2,3,4),(2,1,39)]),(3,[(2,1,39)]),(32,[(2,1,39)]),(43,[(2,3,4),(2,1,39)]),(7,[(2,3,4),(2,1,39)]),(36,[(2,0,2)]),(1,[(2,0,2),(2,3,5)]),(32,[(2,0,2),(2,3,5)]),(3,[(2,0,2),(1,4,41)]),(43,[(2,0,2),(1,4,41)]),(1,[(2,0,2),(1,4,5)]),(3,[(2,0,2),(1,4,5)]),(33,[(3,10,45)]),(1,[(2,0,2),(1,4,5),(3,10,45)]),(0,[(1,4,5),(3,10,45)]),(18,[(1,4,5),(3,10,45)]),(32,[(2,0,2),(3,10,45)]),(3,[(2,0,2),(1,4,5),(3,10,45)]),(43,[(2,0,2),(3,10,45)]),(1,[(2,0,2),(1,4,10)]),(0,[(1,4,10)]),(18,[(1,4,10)]),(3,[(2,0,2),(1,4,10)]),(43,[(2,0,2),(1,4,10)]),(1,[(3,0,2)]),(3,[(3,0,2)]),(32,[(3,0,2)]),(43,[(3,0,2)]),(32,[(3,0,2),(0,1,3)]),(43,[(3,0,2),(0,1,3)]),(26,[(3,0,2)]),(7,[(3,0,2)]),(1,[(3,0,2),(1,11,21)]),(3,[(3,0,2),(1,11,21)]),(32,[(3,0,2),(0,1,3),(1,11,21)]),(43,[(3,0,2),(0,1,3),(1,11,21)]),(3,[(3,0,2),(2,1,5)]),(32,[(3,0,2),(2,1,5)]),(1,[(3,0,2),(1,11,24)]),(3,[(3,0,2),(2,1,5),(1,11,24)]),(32,[(3,0,2),(2,1,5),(1,11,24)]),(43,[(3,0,2),(1,11,24)]),(1,[(2,3,5),(2,2,6)]),(43,[(0,0,1),(2,2,6),(2,1,38)]),(3,[(0,0,1),(2,2,6),(2,1,38)]),(32,[(0,0,1),(2,2,6),(2,1,38)]),(20,[]),(1,[(3,0,2),(2,3,5)]),(32,[(3,0,2),(2,3,5)]),(1,[(0,0,3),(2,0,5)]),(32,[(0,0,3),(2,0,5)]),(3,[(0,1,2)]),(32,[(0,0,3),(0,1,2)]),(43,[(0,0,3),(0,1,2)]),(26,[(0,1,2)]),(32,[(0,1,2)]),(43,[(0,1,2)]),(7,[(0,1,2)]),(1,[(0,0,3),(1,12,19)]),(0,[(0,1,2),(1,12,19)]),(3,[(0,1,2),(1,12,19)]),(32,[(0,0,3),(0,1,2),(1,12,19)]),(33,[(0,1,2),(1,12,19)]),(43,[(0,0,3),(0,1,2),(1,12,19)]),(3,[(2,1,2)]),(32,[(0,0,3),(2,1,2)]),(43,[(0,0,3),(2,1,2)]),(26,[(2,1,2)]),(18,[(0,0,3),(2,1,12)]),(0,[(2,1,2),(2,1,12)]),(3,[(2,1,2),(2,1,12)]),(32,[(2,1,2),(0,0,3),(2,1,12)]),(33,[(2,1,2),(2,1,12)]),(43,[(2,1,2),(0,0,3),(2,1,12)]),(32,[(2,1,2)]),(43,[(2,1,2)]),(7,[(2,1,2)]),(1,[(0,0,3),(1,12,20)]),(18,[(0,0,3),(1,12,20)]),(0,[(2,1,2),(1,12,20)]),(3,[(2,1,2),(1,12,20)]),(32,[(0,0,3),(2,1,2),(1,12,20)]),(33,[(2,1,2),(1,12,20)]),(43,[(0,0,3),(2,1,2),(1,12,20)]),(43,[(0,0,3),(2,1,4)]),(0,[(2,1,4),(2,1,12)]),(3,[(2,1,4),(2,1,12)]),(32,[(0,0,3),(2,1,12)]),(43,[(2,1,4),(0,0,3),(2,1,12)]),(34,[(0,0,3)]),(32,[(0,0,3),(2,1,5)]),(0,[(2,1,5),(2,1,12)]),(3,[(2,1,5),(2,1,12)]),(32,[(2,1,5),(0,0,3),(2,1,12)]),(33,[(2,1,5),(2,1,12)]),(43,[(0,0,3),(2,1,12)]),(31,[]),(1,[(0,0,3),(1,12,24)]),(0,[(2,1,5),(1,12,24)]),(3,[(2,1,5),(1,12,24)]),(32,[(0,0,3),(2,1,5),(1,12,24)]),(33,[(2,1,5),(1,12,24)]),(43,[(0,0,3),(1,12,24)]),(3,[(2,1,12)]),(1,[(1,2,4),(0,0,3)]),(3,[(1,2,4),(2,1,12)]),(1,[(2,2,4),(0,0,3)]),(3,[(2,2,4),(2,1,12)]),(1,[(0,0,3),(1,2,4)]),(43,[(0,0,3),(1,2,4)]),(3,[(1,2,4),(0,1,33)]),(32,[(0,0,3),(0,1,33)]),(26,[(1,2,4),(0,1,33)]),(18,[(0,1,33)]),(43,[(0,0,3),(1,2,4),(0,1,33)]),(32,[(0,1,33)]),(43,[(1,2,4),(0,1,33)]),(7,[(1,2,4),(0,1,33)]),(33,[(3,12,33)]),(1,[(0,0,3),(1,2,4),(3,12,33)]),(0,[(1,2,4),(3,12,33)]),(18,[(0,0,3),(3,12,33)]),(3,[(1,2,4),(3,12,33)]),(32,[(0,0,3),(3,12,33)]),(43,[(0,0,3),(1,2,4),(3,12,33)]),(1,[(0,0,3),(2,2,4)]),(43,[(0,0,3),(2,2,4)]),(3,[(2,2,4),(2,1,34)]),(0,[(2,2,4),(2,1,34)]),(32,[(0,0,3),(2,1,34)]),(26,[(2,2,4),(2,1,34)]),(2,[(2,1,34)]),(43,[(0,0,3),(2,2,4),(2,1,34)]),(32,[(2,1,34)]),(43,[(2,2,4),(2,1,34)]),(7,[(2,2,4),(2,1,34)]),(35,[(0,0,3)]),(1,[(0,0,3),(1,2,5)]),(32,[(0,0,3),(1,2,5)]),(18,[(0,0,3),(0,0,35)]),(1,[(0,0,3),(1,2,5),(0,0,35)]),(26,[(1,2,5),(0,0,35)]),(3,[(1,2,5),(0,0,35)]),(32,[(0,0,3),(1,2,5),(0,0,35)]),(43,[(0,0,3),(0,0,35)]),(1,[(0,0,3),(1,2,5),(3,12,35)]),(0,[(1,2,5),(3,12,35)]),(18,[(0,0,3),(3,12,35)]),(3,[(1,2,5),(3,12,35)]),(32,[(0,0,3),(1,2,5),(3,12,35)]),(33,[(1,2,5),(3,12,35)]),(43,[(0,0,3),(3,12,35)]),(1,[(0,0,3),(2,2,5)]),(32,[(0,0,3),(2,2,5)]),(1,[(0,0,3),(2,2,5),(1,12,36)]),(0,[(2,2,5),(1,12,36)]),(3,[(2,2,5),(1,12,36)]),(32,[(0,0,3),(2,2,5),(1,12,36)]),(33,[(2,2,5),(1,12,36)]),(43,[(0,0,3),(1,12,36)]),(1,[(0,0,3),(1,4,5)]),(33,[(3,12,45)]),(1,[(0,0,3),(1,4,5),(3,12,45)]),(0,[(1,4,5),(3,12,45)]),(3,[(1,4,5),(3,12,45)]),(32,[(0,0,3),(3,12,45)]),(43,[(0,0,3),(3,12,45)]),(1,[(0,0,3),(1,4,12)]),(0,[(1,4,12)]),(3,[(1,4,12)]),(43,[(0,0,3),(1,4,12)]),(3,[(0,0,1),(1,4,42),(0,1,139)]),(26,[(0,1,139)]),(1,[(3,0,3)]),(32,[(3,0,3)]),(43,[(3,0,3)]),(32,[(3,0,3),(0,1,2)]),(43,[(3,0,3),(0,1,2)]),(18,[(3,0,3)]),(7,[(3,0,3)]),(1,[(3,0,3),(1,13,19)]),(3,[(0,1,2),(1,13,19)]),(32,[(3,0,3),(0,1,2),(1,13,19)]),(43,[(3,0,3),(0,1,2),(1,13,19)]),(32,[(3,0,3),(2,1,2)]),(43,[(3,0,3),(2,1,2)]),(2,[(3,0,3)]),(1,[(3,0,3),(1,13,20)]),(3,[(2,1,2),(1,13,20)]),(32,[(3,0,3),(2,1,2),(1,13,20)]),(43,[(3,0,3),(2,1,2),(1,13,20)]),(18,[(3,0,3),(1,13,20)]),(32,[(3,0,3),(2,1,5)]),(1,[(3,0,3),(1,13,24)]),(3,[(2,1,5),(1,13,24)]),(32,[(3,0,3),(2,1,5),(1,13,24)]),(43,[(3,0,3),(1,13,24)]),(1,[(1,2,5),(2,3,6)]),(3,[(1,2,5),(0,0,1)]),(43,[(0,0,1),(2,3,6),(2,1,44)]),(32,[(0,0,1),(2,3,6),(2,1,44)]),(0,[(1,2,5),(2,35,98)]),(3,[(1,2,5),(0,0,1),(2,35,98)]),(1,[(1,2,5),(2,3,6),(2,35,98)]),(1,[(2,2,5),(2,3,6)]),(3,[(2,2,5),(0,0,1)]),(1,[(2,3,6),(1,2,98)]),(0,[(1,2,98)]),(3,[(0,0,1),(1,2,98)]),(33,[(1,2,98)]),(1,[(2,3,6),(2,2,98)]),(0,[(2,2,98)]),(3,[(0,0,1),(2,2,98)]),(33,[(2,2,98)]),(1,[(3,0,3),(1,2,5)]),(32,[(3,0,3),(1,2,5)]),(18,[(3,0,3),(0,0,35)]),(1,[(3,0,3),(1,2,5),(0,0,35)]),(32,[(3,0,3),(1,2,5),(0,0,35)]),(43,[(3,0,3),(0,0,35)]),(1,[(3,0,3),(1,2,5),(3,13,35)]),(3,[(1,2,5),(3,13,35)]),(32,[(3,0,3),(1,2,5),(3,13,35)]),(43,[(3,0,3),(3,13,35)]),(18,[(3,0,3),(3,13,35)]),(1,[(3,0,3),(2,2,5)]),(32,[(3,0,3),(2,2,5)]),(1,[(3,0,3),(2,2,5),(1,13,36)]),(3,[(2,2,5),(1,13,36)]),(32,[(3,0,3),(2,2,5),(1,13,36)]),(43,[(3,0,3),(1,13,36)]),(1,[(1,0,4)]),(3,[(1,0,4)]),(43,[(1,0,4)]),(3,[(1,0,4),(0,1,2)]),(43,[(1,0,4),(0,1,2)]),(18,[(1,0,4)]),(1,[(1,0,4),(2,0,2)]),(32,[(2,0,2),(2,1,10),(2,0,60)]),(49,[]),(21,[(1,0,4)]),(32,[(0,1,2),(0,0,1)]),(18,[(0,0,1),(1,4,6),(0,1,46)]),(43,[(0,0,1),(1,4,6),(0,1,46)]),(26,[(1,0,4)]),(7,[(1,0,4)]),(1,[(1,0,4),(2,14,19)]),(3,[(1,0,4),(0,1,2),(2,14,19)]),(32,[(0,1,2),(2,14,19)]),(43,[(1,0,4),(0,1,2),(2,14,19)]),(3,[(1,0,4),(2,1,2)]),(43,[(1,0,4),(2,1,2)]),(2,[(1,0,4)]),(1,[(1,0,4),(2,14,20)]),(3,[(1,0,4),(2,1,2),(2,14,20)]),(32,[(2,1,2),(2,14,20)]),(43,[(1,0,4),(2,1,2),(2,14,20)]),(18,[(1,0,4),(2,14,20)]),(43,[(1,0,4),(0,1,3)]),(3,[(0,0,1),(1,4,6),(0,1,46)]),(32,[(0,1,3),(0,0,1)]),(26,[(0,0,1),(1,4,6),(0,1,46)]),(1,[(1,0,4),(2,14,21)]),(3,[(1,0,4),(2,14,21)]),(32,[(0,1,3),(2,14,21)]),(43,[(1,0,4),(0,1,3),(2,14,21)]),(3,[(1,0,4),(2,1,5)]),(1,[(1,0,4),(2,14,24)]),(3,[(1,0,4),(2,1,5),(2,14,24)]),(32,[(2,1,5),(2,14,24)]),(43,[(1,0,4),(2,14,24)]),(32,[(0,1,5),(0,0,1)]),(5,[(0,1,5)]),(0,[(1,2,3)]),(0,[(0,1,5),(1,4,5)]),(1,[(1,4,5),(1,4,6)]),(22,[(0,1,5)]),(29,[(0,1,5)]),(7,[(0,0,1),(1,4,6),(0,1,46)]),(16,[(1,4,5)]),(1,[(1,2,3),(1,4,6)]),(32,[(1,2,3),(0,0,1)]),(1,[(1,2,3)]),(32,[(1,2,3)]),(6,[(1,2,3)]),(5,[(1,2,3)]),(43,[(1,2,3)]),(7,[(1,2,3)]),(6,[(3,2,3)]),(6,[(1,2,5)]),(1,[(1,3,5),(1,4,6)]),(32,[(1,3,5),(0,0,1)]),(18,[(1,3,5)]),(1,[(1,0,4),(0,2,3)]),(43,[(1,0,4),(0,2,3)]),(1,[(1,0,4),(0,2,3),(2,14,29)]),(3,[(1,0,4),(2,14,29)]),(32,[(0,2,3),(2,14,29)]),(43,[(1,0,4),(0,2,3),(2,14,29)]),(1,[(1,0,4),(3,2,3)]),(43,[(1,0,4),(3,2,3)]),(1,[(1,0,4),(1,2,5)]),(3,[(1,0,4),(1,2,5)]),(32,[(1,2,5),(0,0,35)]),(43,[(1,0,4),(0,0,35)]),(1,[(1,0,4),(1,2,5),(0,0,35)]),(1,[(1,2,5),(0,0,35)]),(43,[(0,0,35)]),(1,[(1,0,4),(1,2,5),(0,14,35)]),(3,[(1,0,4),(1,2,5),(0,14,35)]),(32,[(1,2,5),(0,14,35)]),(43,[(1,0,4),(0,14,35)]),(18,[(1,0,4),(0,14,35)]),(1,[(1,0,4),(2,2,5)]),(3,[(1,0,4),(2,2,5)]),(1,[(1,0,4),(2,2,5),(2,14,36)]),(3,[(1,0,4),(2,2,5),(2,14,36)]),(32,[(2,2,5),(2,14,36)]),(43,[(1,0,4),(2,14,36)]),(1,[(1,0,4),(2,3,5)]),(1,[(1,0,4),(1,4,5)]),(3,[(1,0,4),(1,4,5)]),(1,[(2,0,4)]),(3,[(2,0,4)]),(43,[(2,0,4)]),(18,[(2,0,4)]),(3,[(2,0,4),(0,1,2)]),(43,[(2,0,4),(0,1,2)]),(1,[(2,0,4),(2,0,2)]),(21,[(2,0,4)]),(5,[(0,1,2)]),(26,[(2,0,4)]),(7,[(2,0,4)]),(2,[(2,0,4)]),(3,[(2,0,4),(2,1,2)]),(43,[(2,0,4),(2,1,2)]),(5,[(2,1,2)]),(43,[(2,0,4),(0,1,3)]),(5,[(0,1,3)]),(3,[(2,0,4),(2,1,4)]),(43,[(2,0,4),(2,1,4)]),(3,[(2,0,4),(2,1,5)]),(5,[(2,1,5)]),(1,[(2,0,4),(0,2,3)]),(43,[(2,0,4),(0,2,3)]),(1,[(2,0,4),(3,2,3)]),(43,[(2,0,4),(3,2,3)]),(1,[(2,0,4),(1,2,5)]),(3,[(2,0,4),(1,2,5)]),(1,[(2,0,4),(2,2,5)]),(3,[(2,0,4),(2,2,5)]),(1,[(2,0,4),(2,3,5)]),(1,[(1,0,5)]),(3,[(1,0,5)]),(32,[(1,0,5)]),(3,[(1,0,5),(0,1,2)]),(32,[(1,0,5),(0,1,2)]),(18,[(1,0,5)]),(43,[(0,1,2),(0,0,1)]),(18,[(0,0,1),(1,5,6),(0,1,56)]),(32,[(0,0,1),(1,5,6),(0,1,56)]),(1,[(1,0,5),(0,3,17)]),(32,[(0,1,2),(1,0,5),(0,3,17)]),(43,[(0,1,2),(0,3,17)]),(18,[(1,0,5),(0,3,17)]),(3,[(0,1,2),(1,0,5)]),(32,[(1,0,5),(0,3,17)]),(43,[(0,3,17)]),(43,[(0,3,17),(0,1,2),(1,19,194)]),(0,[(0,1,2),(1,19,194)]),(43,[(0,1,2),(0,3,17),(1,19,194)]),(1,[(1,0,5),(0,3,17),(1,19,194)]),(2,[(1,0,5),(0,3,17)]),(5,[(1,0,5),(0,3,17)]),(3,[(0,1,2),(1,0,5),(1,19,194)]),(26,[(1,0,5)]),(1,[(1,0,5),(2,17,19)]),(3,[(1,0,5),(0,1,2),(2,17,19)]),(32,[(1,0,5),(0,1,2),(2,17,19)]),(43,[(0,1,2),(2,17,19)]),(3,[(1,0,5),(2,1,2)]),(32,[(1,0,5),(2,1,2)]),(2,[(1,0,5)]),(32,[(2,1,2),(1,0,5),(0,3,17)]),(43,[(2,1,2),(0,3,17)]),(3,[(2,1,2),(1,0,5)]),(1,[(1,0,5),(2,17,20)]),(3,[(1,0,5),(2,1,2),(2,17,20)]),(32,[(1,0,5),(2,1,2),(2,17,20)]),(43,[(2,1,2),(2,17,20)]),(18,[(1,0,5),(2,17,20)]),(32,[(1,0,5),(0,1,3)]),(1,[(1,0,5),(2,17,21)]),(3,[(1,0,5),(2,17,21)]),(32,[(1,0,5),(0,1,3),(2,17,21)]),(43,[(0,1,3),(2,17,21)]),(1,[(0,2,3),(1,5,6)]),(3,[(0,0,1),(1,5,6),(0,1,56)]),(8,[]),(1,[(1,2,3),(1,5,6)]),(43,[(1,2,3),(0,0,1)]),(33,[(1,2,3)]),(0,[(2,2,4),(2,3,4),(1,34,39)]),(33,[(1,34,39)]),(1,[(2,2,4),(2,3,4),(1,34,39)]),(43,[(2,2,4),(2,3,4),(1,34,39)]),(19,[(2,3,4)]),(7,[(2,2,4),(2,3,4),(1,34,39)]),(1,[(2,2,3),(1,5,6)]),(0,[(2,2,3)]),(43,[(2,2,3),(0,0,1)]),(1,[(2,2,3)]),(43,[(2,2,3)]),(33,[(2,2,3)]),(32,[(2,2,3)]),(5,[(2,2,3)]),(7,[(2,2,3)]),(1,[(3,2,3),(1,5,6)]),(1,[(1,0,5),(0,2,3)]),(32,[(1,0,5),(0,2,3)]),(1,[(1,0,5),(0,2,3),(2,17,29)]),(3,[(1,0,5),(2,17,29)]),(32,[(1,0,5),(0,2,3),(2,17,29)]),(43,[(0,2,3),(2,17,29)]),(2,[(1,0,5),(2,17,29)]),(1,[(1,0,5),(3,2,3)]),(32,[(1,0,5),(3,2,3)]),(3,[(2,0,5),(0,1,2)]),(32,[(2,0,5),(0,1,2)]),(1,[(2,0,5),(1,18,19)]),(0,[(0,1,2),(1,18,19)]),(3,[(2,0,5),(0,1,2),(1,18,19)]),(32,[(2,0,5),(0,1,2),(1,18,19)]),(33,[(0,1,2),(1,18,19)]),(43,[(0,1,2),(1,18,19)]),(53,[]),(3,[(2,0,5),(2,1,2)]),(32,[(2,0,5),(2,1,2)]),(1,[(2,0,5),(1,18,20)]),(18,[(2,0,5),(1,18,20)]),(0,[(2,1,2),(1,18,20)]),(3,[(2,0,5),(2,1,2),(1,18,20)]),(32,[(2,0,5),(2,1,2),(1,18,20)]),(33,[(2,1,2),(1,18,20)]),(43,[(2,1,2),(1,18,20)]),(32,[(2,0,5),(0,1,3)]),(1,[(2,0,5),(1,18,21)]),(0,[(0,1,3),(1,18,21)]),(3,[(2,0,5),(1,18,21)]),(32,[(2,0,5),(0,1,3),(1,18,21)]),(33,[(0,1,3),(1,18,21)]),(43,[(0,1,3),(1,18,21)]),(3,[(2,0,5),(2,1,4)]),(0,[(2,1,4),(2,1,18)]),(3,[(2,1,4),(2,0,5),(2,1,18)]),(32,[(2,0,5),(2,1,18)]),(43,[(2,1,4),(2,1,18)]),(34,[(2,0,5)]),(3,[(2,0,5),(2,1,18)]),(43,[(2,1,18)]),(1,[(0,2,3),(2,0,5)]),(18,[(2,0,5),(2,1,18)]),(43,[(0,2,3),(2,1,18)]),(1,[(3,2,3),(2,0,5)]),(2,[(2,0,5),(2,1,18)]),(43,[(3,2,3),(2,1,18)]),(26,[(2,0,5),(2,1,18)]),(1,[(1,2,4),(2,0,5)]),(43,[(1,2,4),(2,1,18)]),(1,[(2,2,4),(2,0,5)]),(43,[(2,2,4),(2,1,18)]),(1,[(2,3,4),(2,0,5)]),(43,[(2,3,4),(2,1,18)]),(1,[(2,0,5),(0,2,3)]),(32,[(2,0,5),(0,2,3)]),(1,[(2,0,5),(0,2,3),(1,18,29)]),(0,[(0,2,3),(1,18,29)]),(3,[(2,0,5),(1,18,29)]),(32,[(2,0,5),(0,2,3),(1,18,29)]),(33,[(0,2,3),(1,18,29)]),(43,[(0,2,3),(1,18,29)]),(1,[(2,0,5),(3,2,3)]),(32,[(2,0,5),(3,2,3)]),(1,[(2,0,5),(1,2,4)]),(3,[(2,0,5),(1,2,4)]),(33,[(3,18,33)]),(1,[(2,0,5),(1,2,4),(3,18,33)]),(0,[(1,2,4),(3,18,33)]),(18,[(2,0,5),(3,18,33)]),(3,[(2,0,5),(1,2,4),(3,18,33)]),(32,[(2,0,5),(3,18,33)]),(43,[(1,2,4),(3,18,33)]),(1,[(2,0,5),(2,2,4)]),(3,[(2,0,5),(2,2,4)]),(1,[(2,0,5),(2,3,4)]),(1,[(2,0,5),(1,4,18)]),(0,[(1,4,18)]),(3,[(2,0,5),(1,4,18)]),(43,[(1,4,18)]),(2,[(2,0,60)]),(3,[(2,0,2),(2,1,10),(2,0,60)]),(43,[(2,0,2),(2,1,10),(2,0,60)]),(43,[(0,1,2),(2,3,4)]),(18,[(2,3,4),(2,0,39)]),(3,[(0,1,2),(2,0,39)]),(32,[(0,1,2),(2,0,39)]),(1,[(2,3,4),(2,0,39)]),(3,[(2,0,39)]),(32,[(2,0,39)]),(43,[(2,3,4),(2,0,39)]),(7,[(2,3,4),(2,0,39)]),(36,[(0,1,2)]),(32,[(0,1,2),(2,3,5)]),(18,[(2,3,5),(2,0,41)]),(10,[(0,1,2)]),(3,[(0,1,2),(2,0,41)]),(43,[(0,1,2),(2,0,41)]),(1,[(2,3,5),(2,0,41)]),(3,[(2,0,41)]),(32,[(2,3,5),(2,0,41)]),(43,[(2,0,41)]),(46,[(0,1,2)]),(3,[(0,1,2),(1,4,5)]),(18,[(1,4,5),(0,0,45)]),(0,[(0,1,2),(1,4,5)]),(32,[(0,1,2),(0,0,45)]),(43,[(0,1,2),(0,0,45)]),(1,[(1,4,5),(0,0,45)]),(3,[(1,4,5),(0,0,45)]),(26,[(1,4,5),(0,0,45)]),(32,[(0,0,45)]),(43,[(0,0,45)]),(33,[(0,1,2),(1,19,81)]),(0,[(0,1,2),(1,4,5),(1,19,81)]),(32,[(0,1,2),(0,0,45),(1,19,81)]),(1,[(1,4,5),(0,0,45),(1,19,81)]),(1,[(1,4,5),(3,19,45)]),(3,[(0,1,2),(1,4,5),(3,19,45)]),(33,[(0,1,2),(3,19,45)]),(32,[(0,1,2),(3,19,45)]),(43,[(0,1,2),(3,19,45)]),(5,[(0,0,5)]),(32,[(0,0,5),(0,1,33)]),(43,[(1,2,4),(0,1,33),(1,4,89)]),(1,[(0,0,5),(1,2,4)]),(2,[(0,0,5)]),(1,[(0,0,5)]),(18,[(0,0,5)]),(2,[(1,4,89)]),(32,[(0,0,5)]),(29,[(0,0,5)]),(3,[(1,2,4),(0,1,33),(1,4,89)]),(26,[(0,0,5)]),(3,[(0,0,5)]),(18,[(0,0,99)]),(34,[(0,33,46)]),(21,[(0,0,99)]),(18,[(2,0,26)]),(43,[(2,1,2),(2,3,4)]),(2,[(2,3,4),(2,0,39)]),(3,[(2,1,2),(2,0,39)]),(32,[(2,1,2),(2,0,39)]),(36,[(2,1,2)]),(32,[(2,1,2),(2,3,5)]),(10,[(2,1,2)]),(2,[(2,3,5),(2,0,41)]),(3,[(2,1,2),(2,0,41)]),(43,[(2,1,2),(2,0,41)]),(46,[(2,1,2)]),(3,[(2,1,2),(1,4,5)]),(2,[(1,4,5),(0,0,45)]),(0,[(2,1,2),(1,4,5)]),(32,[(2,1,2),(0,0,45)]),(43,[(2,1,2),(0,0,45)]),(1,[(1,4,5),(3,20,45)]),(18,[(1,4,5),(3,20,45)]),(3,[(2,1,2),(1,4,5),(3,20,45)]),(33,[(2,1,2),(3,20,45)]),(32,[(2,1,2),(3,20,45)]),(43,[(2,1,2),(3,20,45)]),(52,[]),(1,[(1,4,20)]),(18,[(1,4,20)]),(3,[(2,1,2),(1,4,20)]),(43,[(2,1,2),(1,4,20)]),(3,[(3,0,1),(0,0,1),(2,0,42)]),(43,[(0,1,3),(1,2,4)]),(1,[(1,2,4),(3,21,33)]),(18,[(0,1,3),(3,21,33)]),(3,[(1,2,4),(3,21,33)]),(32,[(0,1,3),(3,21,33)]),(43,[(0,1,3),(1,2,4),(3,21,33)]),(33,[(0,1,3),(3,21,33)]),(43,[(0,1,3),(2,2,4)]),(32,[(0,1,3),(1,2,5)]),(18,[(0,1,3),(0,1,35)]),(3,[(1,2,5),(0,1,35)]),(32,[(0,1,3),(1,2,5),(0,1,35)]),(43,[(0,1,3),(0,1,35)]),(1,[(1,2,5),(3,21,35)]),(18,[(0,1,3),(3,21,35)]),(3,[(1,2,5),(3,21,35)]),(32,[(0,1,3),(1,2,5),(3,21,35)]),(43,[(0,1,3),(3,21,35)]),(32,[(0,1,3),(2,2,5)]),(1,[(2,2,5),(1,21,36)]),(3,[(2,2,5),(1,21,36)]),(32,[(0,1,3),(2,2,5),(1,21,36)]),(43,[(0,1,3),(1,21,36)]),(1,[(1,4,5),(3,21,45)]),(33,[(0,1,3),(3,21,45)]),(3,[(1,4,5),(3,21,45)]),(32,[(0,1,3),(3,21,45)]),(43,[(0,1,3),(3,21,45)]),(1,[(1,4,21)]),(3,[(1,4,21)]),(43,[(0,1,3),(1,4,21)]),(1,[(0,3,6),(1,4,42),(0,0,139)]),(26,[(0,0,139)]),(3,[(0,0,1),(1,4,42),(0,0,139)]),(1,[(3,4,6),(2,0,55)]),(32,[(0,0,1),(2,0,55)]),(34,[(0,2,3)]),(3,[(0,0,1),(3,4,6),(2,0,55)]),(43,[(0,0,1),(3,4,6),(2,0,55)]),(34,[(3,2,3)]),(43,[(2,1,4),(0,2,3)]),(3,[(2,1,4),(2,0,29)]),(32,[(0,2,3),(2,0,29)]),(1,[(0,2,3),(2,0,29)]),(2,[(2,0,29)]),(3,[(2,0,29)]),(14,[(2,1,4)]),(10,[(2,1,4)]),(43,[(0,2,3),(2,0,29)]),(7,[(0,2,3),(2,0,29)]),(43,[(2,1,4),(3,2,3)]),(3,[(2,1,4),(2,0,32)]),(32,[(3,2,3),(2,0,32)]),(1,[(3,2,3),(2,0,32)]),(18,[(2,0,32)]),(3,[(2,0,32)]),(43,[(3,2,3),(2,0,32)]),(7,[(3,2,3),(2,0,32)]),(3,[(2,1,4),(1,2,5)]),(34,[(1,2,5)]),(43,[(2,1,4),(0,0,35)]),(18,[(0,0,35)]),(18,[(2,1,4),(0,1,35)]),(3,[(2,1,4),(1,2,5),(0,1,35)]),(32,[(1,2,5),(0,1,35)]),(43,[(2,1,4),(0,1,35)]),(3,[(2,1,4),(2,2,5)]),(34,[(2,2,5)]),(32,[(2,2,5),(2,0,36)]),(43,[(2,1,4),(2,0,36)]),(1,[(2,2,5),(2,0,36)]),(2,[(2,0,36)]),(26,[(2,2,5),(2,0,36)]),(3,[(2,2,5),(2,0,36)]),(43,[(2,0,36)]),(34,[(2,3,5)]),(3,[(2,1,4),(2,0,41)]),(43,[(2,1,4),(2,0,41)]),(3,[(2,1,4),(1,4,5)]),(0,[(2,1,4),(1,4,5)]),(3,[(2,1,4),(1,4,5),(0,0,45)]),(43,[(2,1,4),(0,0,45)]),(43,[(3,0,1),(0,0,1),(2,0,57)]),(32,[(2,1,5),(0,2,3)]),(1,[(0,2,3),(1,24,29)]),(3,[(2,1,5),(1,24,29)]),(32,[(2,1,5),(0,2,3),(1,24,29)]),(43,[(0,2,3),(1,24,29)]),(32,[(2,1,5),(3,2,3)]),(3,[(2,1,5),(1,2,4)]),(1,[(1,2,4),(3,24,33)]),(18,[(2,1,5),(3,24,33)]),(3,[(2,1,5),(1,2,4),(3,24,33)]),(33,[(2,1,5),(3,24,33)]),(32,[(2,1,5),(3,24,33)]),(43,[(1,2,4),(3,24,33)]),(3,[(2,1,5),(2,2,4)]),(18,[(0,0,1),(2,1,72)]),(26,[(0,0,1),(2,1,72)]),(3,[(0,0,1),(2,6,29),(2,1,72)]),(3,[(2,1,29)]),(32,[(0,2,3),(2,1,29)]),(43,[(0,2,3),(2,1,29)]),(1,[(0,2,3),(2,6,29),(2,0,72)]),(18,[(0,0,1),(2,0,72)]),(26,[(0,0,1),(2,0,72)]),(3,[(0,0,1),(2,6,29),(2,0,72)]),(1,[(0,2,3),(1,4,5)]),(0,[(0,2,3),(1,4,5)]),(32,[(0,2,3),(0,0,45)]),(43,[(0,2,3),(0,0,45)]),(0,[(0,2,3),(1,4,5),(1,29,81)]),(32,[(0,2,3),(0,0,45),(1,29,81)]),(43,[(0,2,3),(0,0,45),(1,29,81)]),(7,[(0,2,3),(1,29,81)]),(3,[(1,4,5),(0,0,45),(1,29,81)]),(1,[(0,2,3),(1,4,5),(3,29,45)]),(33,[(0,2,3),(3,29,45)]),(3,[(1,4,5),(3,29,45)]),(32,[(0,2,3),(3,29,45)]),(43,[(0,2,3),(3,29,45)]),(1,[(0,2,3),(1,4,29),(0,0,73)]),(18,[(0,0,73)]),(3,[(1,4,29),(0,0,73)]),(32,[(0,2,3),(0,0,73)]),(43,[(0,2,3),(1,4,29),(0,0,73)]),(18,[(0,1,73)]),(3,[(1,4,29),(0,1,73)]),(32,[(0,2,3),(0,1,73)]),(43,[(0,2,3),(1,4,29),(0,1,73)]),(33,[(0,2,3),(0,1,73)]),(3,[(2,0,32),(2,1,79)]),(0,[(3,2,3),(2,1,79)]),(2,[(2,1,79)]),(32,[(3,2,3),(2,0,32),(2,1,79)]),(33,[(3,2,3),(2,1,79)]),(43,[(3,2,3),(2,0,32),(2,1,79)]),(18,[(2,0,32),(2,1,79)]),(18,[(2,1,32)]),(3,[(2,1,32)]),(32,[(3,2,3),(2,1,32)]),(43,[(3,2,3),(2,1,32)]),(1,[(3,2,3),(2,0,80)]),(18,[(2,1,32),(2,0,80)]),(0,[(3,2,3),(2,1,32)]),(2,[(2,0,80)]),(3,[(2,1,32),(2,0,80)]),(32,[(3,2,3),(2,1,32),(2,0,80)]),(33,[(3,2,3),(2,1,32)]),(43,[(3,2,3),(2,1,32),(2,0,80)]),(17,[(1,4,5)]),(7,[(3,2,3),(2,1,32)]),(1,[(1,4,5),(3,2,3)]),(3,[(1,4,5),(2,1,32)]),(1,[(3,2,3),(1,4,5)]),(0,[(3,2,3),(1,4,5)]),(32,[(3,2,3),(0,0,45)]),(43,[(3,2,3),(0,0,45)]),(2,[(1,4,5),(0,1,45)]),(32,[(3,2,3),(0,1,45)]),(43,[(3,2,3),(0,1,45)]),(18,[(1,4,5),(0,1,45)]),(3,[(1,4,5),(0,1,45)]),(32,[(0,1,45)]),(43,[(0,1,45)]),(1,[(1,2,4),(0,0,33)]),(32,[(0,0,33)]),(3,[(1,2,4),(0,0,33)]),(43,[(1,2,4),(0,0,33)]),(18,[(0,0,33)]),(2,[(0,0,89),(2,1,90)]),(33,[(0,1,33),(2,1,90)]),(32,[(0,1,33),(0,0,89),(2,1,90)]),(1,[(1,2,4),(2,0,89)]),(18,[(0,1,33),(2,0,89)]),(2,[(2,0,89)]),(3,[(1,2,4),(0,1,33),(2,0,89)]),(32,[(0,1,33),(2,0,89)]),(43,[(1,2,4),(0,1,33),(2,0,89)]),(1,[(2,3,5),(1,2,4)]),(32,[(2,3,5),(0,1,33)]),(1,[(1,2,4),(2,3,5)]),(3,[(1,2,4),(2,0,41)]),(43,[(1,2,4),(2,0,41)]),(43,[(1,2,4),(2,1,41)]),(0,[(2,3,5),(2,1,41)]),(2,[(2,3,5),(2,1,41)]),(3,[(1,2,4),(2,1,41)]),(32,[(2,3,5),(2,1,41)]),(18,[(2,3,5),(2,1,41)]),(3,[(2,1,41)]),(43,[(2,1,41)]),(1,[(2,2,4),(2,0,34)]),(32,[(2,0,34)]),(3,[(2,2,4),(2,0,34)]),(43,[(2,2,4),(2,0,34)]),(33,[(2,1,101)]),(18,[(2,1,101)]),(0,[(2,2,4),(2,1,101)]),(32,[(2,0,34),(2,1,101)]),(3,[(2,2,4),(2,0,34),(2,1,101)]),(43,[(2,2,4),(2,0,34),(2,1,101)]),(33,[(2,1,34)]),(1,[(2,2,4),(2,0,102)]),(18,[(2,0,102)]),(3,[(2,2,4),(2,1,34),(2,0,102)]),(32,[(2,1,34),(2,0,102)]),(43,[(2,2,4),(2,1,34),(2,0,102)]),(1,[(2,3,5),(2,2,4)]),(32,[(2,3,5),(2,1,34)]),(1,[(2,2,4),(2,3,5)]),(3,[(2,2,4),(2,0,41)]),(43,[(2,2,4),(2,0,41)]),(43,[(2,2,4),(2,1,41)]),(3,[(2,2,4),(2,1,41)]),(2,[(0,0,111),(2,1,112)]),(43,[(0,1,35),(0,0,111),(2,1,112)]),(7,[(0,0,111),(2,1,112)]),(43,[(2,3,4),(0,0,35)]),(18,[(2,3,4),(0,0,35)]),(2,[(1,4,110)]),(43,[(0,0,35),(1,4,110)]),(1,[(1,2,5),(0,0,35),(1,4,110)]),(18,[(0,0,35),(1,4,110)]),(0,[(1,2,5),(1,4,110)]),(3,[(1,2,5),(0,0,35),(1,4,110)]),(18,[(0,1,35)]),(43,[(0,1,35)]),(1,[(1,2,5),(2,0,111)]),(18,[(0,1,35),(2,0,111)]),(2,[(2,0,111)]),(3,[(1,2,5),(0,1,35),(2,0,111)]),(32,[(1,2,5),(0,1,35),(2,0,111)]),(43,[(0,1,35),(2,0,111)]),(1,[(2,3,4),(1,2,5)]),(43,[(2,3,4),(0,1,35)]),(18,[(2,3,4),(0,1,35)]),(1,[(1,2,5),(2,3,4)]),(3,[(1,2,5),(2,1,39)]),(32,[(1,2,5),(2,1,39)]),(18,[(0,0,1),(2,1,122)]),(43,[(0,0,1),(2,6,36),(2,1,122)]),(7,[(0,0,1),(2,1,122)]),(3,[(2,2,5),(2,1,36)]),(32,[(2,2,5),(2,1,36)]),(43,[(2,1,36)]),(1,[(2,2,5),(2,6,36),(2,0,122)]),(18,[(0,0,1),(2,0,122)]),(43,[(0,0,1),(2,6,36),(2,0,122)]),(7,[(0,0,1),(2,0,122)]),(1,[(2,2,5),(2,3,4)]),(33,[(2,1,103)]),(0,[(2,3,4),(2,1,103)]),(3,[(2,0,39),(2,1,103)]),(32,[(2,0,39),(2,1,103)]),(43,[(2,3,4),(2,0,39),(2,1,103)]),(26,[(2,1,103)]),(33,[(2,1,39)]),(1,[(2,3,4),(2,0,104)]),(3,[(2,1,39),(2,0,104)]),(32,[(2,1,39),(2,0,104)]),(43,[(2,3,4),(2,1,39),(2,0,104)]),(0,[(2,3,5),(2,1,93)]),(3,[(2,0,41),(2,1,93)]),(32,[(2,3,5),(2,0,41),(2,1,93)]),(33,[(2,3,5),(2,1,93)]),(43,[(2,0,41),(2,1,93)]),(26,[(2,1,93)]),(1,[(2,3,5),(2,0,94)]),(3,[(2,1,41),(2,0,94)]),(32,[(2,3,5),(2,1,41),(2,0,94)]),(33,[(2,3,5),(2,1,41)]),(43,[(2,1,41),(2,0,94)]),(33,[(0,1,45),(2,1,83)]),(32,[(0,1,45),(0,0,82),(2,1,83)]),(43,[(0,1,45),(0,0,82),(2,1,83)]),(7,[(0,0,82),(2,1,83)]),(33,[(1,2,81)]),(0,[(1,4,5),(1,2,81)]),(32,[(0,0,45),(1,2,81)]),(43,[(0,0,45),(1,2,81)]),(7,[(1,2,81)]),(1,[(1,4,5),(0,0,45),(1,2,81)]),(3,[(1,4,5),(0,0,45),(1,2,81)]),(33,[(2,2,81)]),(0,[(1,4,5),(2,2,81)]),(32,[(0,0,45),(2,2,81)]),(43,[(0,0,45),(2,2,81)]),(7,[(2,2,81)]),(1,[(1,4,5),(0,0,45),(2,2,81)]),(3,[(1,4,5),(0,0,45),(2,2,81)]),(1,[(1,4,5),(2,0,82)]),(3,[(1,4,5),(0,1,45),(2,0,82)]),(32,[(0,1,45),(2,0,82)]),(43,[(0,1,45),(2,0,82)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 11 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice53 : Slice h0R h0G (subcubeFast 48 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice52 : Slice h0R h0G (subcubeFast 48 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice51 : Slice h0R h0G (subcubeFast 40 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice50 : Slice h0R h0G (subcubeFast 40 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice49 : Slice h0R h0G (subcubeFast 34 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice48 : Slice h0R h0G (subcubeFast 34 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice47 : Slice h0R h0G (subcubeFast 32 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice46 : Slice h0R h0G (subcubeFast 32 8) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice45 : Slice h0R h0G (subcubeFast 32 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice44 : Slice h0R h0G (subcubeFast 32 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice43 : Slice h0R h0G (subcubeFast 32 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice42 : Slice h0R h0G (subcubeFast 24 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice41 : Slice h0R h0G (subcubeFast 20 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice40 : Slice h0R h0G (subcubeFast 20 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice39 : Slice h0R h0G (subcubeFast 18 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice38 : Slice h0R h0G (subcubeFast 18 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice37 : Slice h0R h0G (subcubeFast 16 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice36 : Slice h0R h0G (subcubeFast 16 8) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice35 : Slice h0R h0G (subcubeFast 16 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 16 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 16 1) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 16 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 8 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 8 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 8 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 8 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 8 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 8 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 4 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 4 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 4 18) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 4 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 4 8) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 4 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 4 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 2 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 2 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 1 34) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 1 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 1 10) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 1 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 1 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 1 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 0 48) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 0 34) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 0 32) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 0 18) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 16) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 10) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h52Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 8) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h53Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h55Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h56Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (forall_cons (fun _ h => by cases h; exact h0Slice25) (forall_cons (fun _ h => by cases h; exact h0Slice26) (forall_cons (fun _ h => by cases h; exact h0Slice27) (forall_cons (fun _ h => by cases h; exact h0Slice28) (forall_cons (fun _ h => by cases h; exact h0Slice29) (forall_cons (fun _ h => by cases h; exact h0Slice30) (forall_cons (fun _ h => by cases h; exact h0Slice31) (forall_cons (fun _ h => by cases h; exact h0Slice32) (forall_cons (fun _ h => by cases h; exact h0Slice33) (forall_cons (fun _ h => by cases h; exact h0Slice34) (forall_cons (fun _ h => by cases h; exact h0Slice35) (forall_cons (fun _ h => by cases h; exact h0Slice36) (forall_cons (fun _ h => by cases h; exact h0Slice37) (forall_cons (fun _ h => by cases h; exact h0Slice38) (forall_cons (fun _ h => by cases h; exact h0Slice39) (forall_cons (fun _ h => by cases h; exact h0Slice40) (forall_cons (fun _ h => by cases h; exact h0Slice41) (forall_cons (fun _ h => by cases h; exact h0Slice42) (forall_cons (fun _ h => by cases h; exact h0Slice43) (forall_cons (fun _ h => by cases h; exact h0Slice44) (forall_cons (fun _ h => by cases h; exact h0Slice45) (forall_cons (fun _ h => by cases h; exact h0Slice46) (forall_cons (fun _ h => by cases h; exact h0Slice47) (forall_cons (fun _ h => by cases h; exact h0Slice48) (forall_cons (fun _ h => by cases h; exact h0Slice49) (forall_cons (fun _ h => by cases h; exact h0Slice50) (forall_cons (fun _ h => by cases h; exact h0Slice51) (forall_cons (fun _ h => by cases h; exact h0Slice52) (forall_cons (fun _ h => by cases h; exact h0Slice53) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (6 - 1) xs.toFinset) h0Empty := trivial
def h0Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,5,105,106],[218])]
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
def h0Block7_0 : List NodeSpec := nodesWithIdentity [([0,2,3,5,26,46],[14,16,17,18,19,20,21,22,23]),([0,2,3,5,46,63],[16,23,42,75,80,81,82,83]),([0,2,3,5,46,65],[14,16,42,101,104,105,106,107]),([0,1,2,3,5,46,69],[20,32,36,37,40,41,43,66,135,136,137]),([0,1,2,3,5,54,69],[138,141,142,143,144,147,148,149,150,151,152,153]),([0,1,2,3,4,5,56,69],[12,46,108,119,168]),([0,1,2,3,4,5,69,70],[108,119,175]),([0,1,2,3,4,5,69,71],[108,119,175]),([0,1,2,3,4,5,69],[0,1,25,87,108,119,133,153,170]),([0,2,3,4,5,6,32,82],[183,187]),([0,1,2,3,4,5,32,87],[25,190,194]),([0,1,2,3,5,46,86],[20,32,36,37,40,41,43,66,200,201,202])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_0 = true := by decide +kernel
def h0Block7_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,46,86],[25,26,43,66,133,153]),([0,1,2,3,5,54,86],[138,141,142,143,144,147,148,152,153,208,209]),([0,1,2,3,4,5,56,86],[25,46,108,119,224]),([0,1,2,3,4,5,41,96],[79,244,246]),([0,1,2,3,4,5,44,96],[14,25,29,79,87,251]),([0,1,2,3,5,46,96],[20,32,36,37,38,40,41,43,66,138,153,257,258,259,260]),([0,1,2,3,4,5,56,96],[25,46,108,119,264,266]),([0,1,2,3,5,6,39,105],[210,285,292]),([0,1,2,3,5,6,34,106],[210,288,294]),([0,1,2,3,4,5,44,105],[12,29,79,87,168,251,292,300]),([0,1,2,3,5,46,105],[20,32,36,37,38,40,41,43,138,153,292,300,305,306,307]),([0,1,2,3,4,5,56,105],[12,46,108,119,168,264])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_1 = true := by decide +kernel
def h0Block7_2 : List NodeSpec := nodesWithIdentity [([0,2,3,5,46,111],[16,41,42,66,322,324,328,329,330,331,332]),([0,1,2,3,4,5,39,115],[79,133,153,293]),([0,1,3,4,37,117],[3,4,14,16,195,408,409,410]),([0,1,3,4,5,127],[3,4,14,23,42,195,411,412,413]),([0,1,3,4,5,37,127],[3,4,16,406,407,409,411,412]),([0,1,2,5,46,126],[4,20,23,38,420,421]),([0,1,2,5,54,126],[141,205,417,419,422,423]),([1,2,3,5,46,61],[428]),([0,1,2,3,46,117],[4,14,16,20,21,41]),([0,1,2,3,5,128],[14,23,141,402,426,431,432,433]),([0,1,2,3,4,5,37,106],[3,12,25,138,168,442,446,447]),([0,1,2,3,5,37,46],[20,32,36,37,40,43,66,449])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_2 = true := by decide +kernel
def h0Block7_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,43,108],[87,133,218,300]),([0,1,2,3,5,37,133],[4,14,108,133,483,484,485,486,487,488,489,490,491,492,493]),([0,1,2,3,4,5,134],[0,1,4,12,14,16,79,87,119,133,153,409,477,494,495]),([0,1,2,3,4,5,37,134],[3,108,444,477]),([0,1,3,4,5,38,127],[3,4,16,48,411,412,498,507]),([0,1,2,3,4,5,141],[0,1,4,16,23,25,87,108,119,133,153,508,517,518]),([0,1,2,3,4,5,38,141],[48,79,498,508]),([0,1,2,3,5,46,106],[20,32,36,37,38,40,41,43,66,153,294,545,546,547,548]),([0,1,2,3,4,5,56,106],[46,79,108,119,224,264]),([0,1,3,5,46,137],[4,23,66,575,578,579,580]),([0,1,3,4,5,38,137],[42,48,79,498,508,572,573,574,575,577,581]),([0,1,3,5,46,138],[4,20,23,585,588,589,590])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_3 = true := by decide +kernel
def h0Block7_4 : List NodeSpec := nodesWithIdentity [([0,1,3,5,54,138],[141,585,586,591,592,593]),([0,1,2,3,46,140],[4,41,42,597,598,599,600,601]),([0,1,2,3,5,142],[23,42,513,567,605,606,607]),([0,1,2,5,46,146],[20,38,645,648,649,650,651,652,653,654]),([0,1,2,3,46,147],[20,21,23,41,646,655,656,657,658,659]),([0,1,2,3,5,148],[4,14,42,693,694,695,696]),([0,1,2,3,4,5,168,169],[133,153,998,999,1000]),([0,1,2,3,4,5,168,170],[133,153,1000]),([0,1,2,3,4,5,184],[0,1,12,79,119,133,153,1140,1141,1142]),([0,2,3,4,5,23,30,58],[16,125,162,388,736,1182,1210,1211,1212]),([0,2,3,23,45,58],[42,125,697,858,1182,1210,1211,1213,1214,1215,1216,1217,1218]),([0,1,2,4,5,194,195],[1,108,993,1292,1300,1303,1305,1307,1308,1309,1310,1311,1312,1313])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_4 = true := by decide +kernel
def h0Block7_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,5,76,107],[25,87,117,133,218,285,288,1341,1342,1343,1344,1345,1346]),([0,1,2,3,4,5,209],[0,1,25,79,87,108,119,133,153,1462,1471,1472,1473,1474]),([0,1,2,3,4,5,219],[0,1,16,25,87,108,119,132,133,153,1462,1636,1637,1638,1639,1640])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_5 = true := by decide +kernel
def h0Nodes7 : List NodeSpec := h0Block7_0 ++ h0Block7_1 ++ h0Block7_2 ++ h0Block7_3 ++ h0Block7_4 ++ h0Block7_5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Nodes7 = true := by
  unfold h0Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h0Test7_0,h0Test7_1⟩,h0Test7_2⟩,h0Test7_3⟩,h0Test7_4⟩,h0Test7_5⟩
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket6Ok h0Check7
def h0Block8_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,6,26],[0,2,3,4,8,9,10,11,12,13,14,15,16,24]),([0,1,2,3,5,8,46],[14,16,17,20,23,32,33,34,35,36,37,38,39,40,41,42]),([0,2,3,4,5,6,60],[0,4,14,16,25,48,49,53,54,55,56,57,58]),([0,1,2,3,5,10,46],[14,16,20,23,32,36,37,38,40,41,42,62,63,64,65,66,67]),([0,2,3,4,5,6,63],[0,4,16,23,30,70,73,74,75,76,77,78,79,84]),([0,1,2,3,5,12,46],[16,20,23,32,36,37,38,40,41,42,66,89,90,91,92,93]),([0,2,3,4,5,6,65],[0,4,14,16,47,96,99,100,101,102,103,108]),([0,1,2,3,5,18,46],[14,16,20,32,36,37,38,40,41,42,66,114,115,116,117,118]),([0,1,2,3,5,29,46],[4,14,16,20,32,36,37,40,41,42,127,128,129,130,131,132,133]),([0,1,2,3,5,6,29,46],[4,14,16,20,32,36,37,40,41,42,122,126,127,128,129,130,134,138]),([0,1,2,3,5,6,29,54],[4,14,16,43,123,132,139,140,141,142,143,144,145,146,147,148,154]),([0,1,2,3,4,5,6,73],[0,1,3,4,12,16,29,43,46,47,48,79,122,126,133,138,154,155,156,157,158,159,160,161,162,163])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,6,29,56],[3,4,46,47,134,146,164,165,166,167,169]),([0,1,2,3,4,5,69],[0,1,3,14,25,87,108,119,125,133,153,170,171,172,173,174,175]),([0,1,2,3,4,5,6,69],[0,1,3,12,14,29,43,46,47,48,125,138,170,171,172,173,175]),([0,1,2,3,4,5,29,69],[3,4,25,87,120,121,126,131,164,165,168,170,171,172,173,175]),([0,1,2,3,4,5,72],[3,4,16,23,25,87,108,119,133,153,176,177,178,179,180,181]),([0,1,2,3,4,5,29,72],[3,25,87,126,131,132,164,165,168,176,177,178,179,181]),([0,1,2,3,4,5,6,32,45],[14,47,48,182,187,188,189,190,191,192,193,195]),([0,1,2,3,5,32,46],[4,14,16,20,32,36,37,38,40,41,42,66,92,133,187,196,197,198,199]),([0,1,2,3,5,6,32,46],[4,14,16,20,32,36,37,38,40,41,42,66,134,138,184,190,196,197,198,199]),([0,1,2,3,4,5,6,32,46],[4,29,30,37,38,43,48,66,138,187,190,195,199]),([0,1,2,3,5,6,32,54],[4,14,16,43,92,141,142,143,144,147,148,152,184,185,203,204,205,206,207,210]),([0,1,2,3,4,5,6,85],[0,1,3,4,16,25,29,43,46,47,48,79,133,138,184,190,210,211,212,213,214,215,216,217,218])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
def h0Block8_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,6,32,56],[4,46,47,48,134,193,195,207,219,220,221,222,223]),([0,1,2,3,4,5,6,86],[0,1,3,14,25,29,43,46,47,48,138,209,225,226,227,228,229]),([0,2,3,4,5,6,89],[1,16,25,48,133,169,230,234,235,236,237,238,239]),([0,1,2,3,4,5,6,33,41],[14,30,48,169,240,241,242,243,244,245,247,248]),([0,1,2,3,4,5,6,33,44],[4,14,16,30,48,92,241,242,249,250,251,252]),([0,1,2,3,5,6,33,46],[3,4,16,20,26,32,36,37,38,40,41,42,43,66,92,117,138,153,253,254,255,256]),([0,1,2,3,4,5,6,33,56],[4,16,47,48,117,169,223,261,262,263,264,265]),([0,1,2,3,4,5,90],[4,12,14,16,79,87,108,119,153,235,236,267,268,269,270,271,272]),([0,1,2,3,4,5,96],[0,1,12,48,79,87,108,119,153,163,259,260,273,274,275,276,277]),([0,1,2,3,4,5,6,96],[0,1,3,25,29,30,42,43,46,47,48,259,260,273,274,276,277]),([0,1,2,3,5,6,34,39],[29,43,48,218,280,282,283,284,285,286,287,288,289,290,291,293]),([0,1,2,3,4,5,6,34,41],[3,30,210,243,244,288,289,295,296,297])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_2 = true := by decide +kernel
def h0Block8_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,6,34,44],[3,4,29,30,43,92,210,251,287,288,289,298,299]),([0,1,2,3,5,6,34,46],[4,16,20,26,32,36,37,38,40,41,42,43,48,66,92,117,138,153,287,301,302,303,304]),([0,1,2,3,4,5,6,34,56],[3,4,46,47,117,167,210,264,308,309,310]),([0,1,2,3,4,5,6,105],[0,1,3,12,29,30,42,43,46,47,48,300,307,311,312,313,314]),([0,2,3,4,5,6,111],[1,16,25,42,47,48,108,315,320,321,322,323,324,325,326,327]),([0,1,2,3,4,5,6,35,39],[14,30,42,43,48,138,285,286,333,334,335,336,337,338,339,340]),([0,1,2,3,5,35,46],[4,16,20,23,32,36,37,38,40,41,42,66,117,133,334,342,343,344,345]),([0,1,2,3,4,5,6,114],[0,1,3,4,16,25,29,30,43,46,48,108,133,138,210,218,318,335,346,347,348,349,350,351,352]),([0,1,2,3,4,5,112],[4,12,14,16,79,87,119,133,153,321,325,353,354,355,356,357,358,359]),([0,1,2,3,4,5,115],[0,1,12,23,48,79,87,119,133,153,360,361,362,363,364,365,366]),([0,1,2,3,5,36,46],[4,16,20,23,32,36,37,38,40,42,132,133,375,376,377,378,379]),([0,1,2,3,4,5,6,120],[0,1,3,4,12,16,29,30,43,46,48,108,133,138,370,374,380,381,382,383,384,385,386,387,388])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_3 = true := by decide +kernel
def h0Block8_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,121],[0,1,3,23,25,79,87,119,125,133,153,389,390,391,392,393,394]),([0,1,2,3,4,5,122],[3,4,14,16,25,79,87,119,133,153,395,396,397,398,399,400]),([1,2,3,4,5,6,61],[0,49]),([0,1,3,4,5,25,37],[3,4,14,16,23,195,403,404,405,406,407,409]),([0,1,2,4,5,6,126],[3,4,12,23,30,42,79,414,415,416,417,418,419,424,425]),([0,1,2,3,5,25,46],[4,14,16,17,20,21,23,37,38,40,41,42,218,427]),([0,1,2,3,5,25,54],[4,14,16,42,141,144,147,148,205,387,402,426,429,430,431]),([0,1,2,3,5,6,99],[3,4,12,14,16,23,43,66,133,138,153,194,195,434,435,436]),([0,1,2,3,4,6,117],[3,4,12,14,16,42,47,108,194,195,358,387,388,408,438,439]),([0,1,2,3,4,5,6,37,39],[3,4,14,30,43,48,125,138,285,286,340,406,442,445]),([0,1,2,3,5,37,46],[4,20,23,32,36,37,38,40,41,42,43,66,125,442,449,450,451,452]),([0,1,2,3,4,5,37,46],[3,4,12,20,23,25,26,32,36,37,38,40,41,42,43,66,125,133,153,406,409,440,441,442,443,444,445,449,450,451,452])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_4 = true := by decide +kernel
def h0Block8_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,5,6,37,46],[4,14,20,23,32,36,37,38,40,41,42,43,66,442,449,450,451,452]),([0,1,2,3,5,6,37,54],[4,14,23,43,141,142,143,144,147,148,152,205,210,442,443,453,454,455,456]),([0,1,2,3,4,5,37,55],[3,4,23,25,43,133,154,163,406,409,442,443,444,445,457,458,459,460,461,462,463,464,465,466]),([0,1,2,3,4,5,6,108],[0,1,3,4,12,25,26,29,30,42,43,46,47,48,117,133,138,153,218,300,448,467,468,469,470]),([0,1,2,3,4,5,37,56],[3,4,12,25,46,108,117,119,167,169,220,221,223,263,264,406,409,440,441,442,444,445,471,472,473,474]),([0,1,2,3,4,5,37,57],[3,4,16,25,42,46,108,406,409,442,444,445,475,476,477,478,479,480,481,482,483]),([0,1,3,4,5,27,38],[4,14,16,23,48,498,502,503,504,505,506,507]),([0,1,2,3,4,5,38,42],[4,12,16,23,29,42,48,79,132,498,499,501,507,508,509,510,511,512,513,514,515,516]),([0,1,2,3,4,5,38,44],[4,12,14,23,25,29,48,79,87,92,249,251,252,299,496,497,498,499,501,507,511,519,520,521,522]),([0,1,2,3,5,38,46],[4,20,23,32,36,37,38,40,41,42,43,66,132,499,523,524,525,526]),([0,1,2,3,5,6,38,46],[4,14,20,23,32,36,37,38,40,41,42,43,66,499,523,524,525,526]),([0,1,2,3,5,38,54],[23,141,142,143,144,147,148,153,163,205,499,500,527,528,529,530])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_5 = true := by decide +kernel
def h0Block8_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,5,6,38,54],[4,14,23,42,43,132,141,142,143,144,147,148,152,205,499,500,527,528,529,530]),([0,1,2,3,4,5,6,97],[0,1,3,4,12,25,26,29,30,42,43,46,47,48,92,133,138,153,163,194,260,275,516,531,532,533]),([1,2,3,4,5,6,28],[0,2]),([0,1,2,3,5,27,46],[4,14,16,18,23,37,38,40,41,42,66,535,536]),([0,1,2,3,5,6,109],[4,14,16,20,23,25,43,48,133,138,153,210,537,538,539]),([0,1,2,3,5,6,39,46],[4,14,16,20,26,29,32,36,37,38,40,41,43,66,117,125,132,153,284,542,543,544]),([0,1,2,3,4,5,6,39,56],[4,30,46,47,117,221,264,336,337,340,549]),([0,1,2,3,4,5,6,106],[0,1,3,14,29,30,43,46,47,48,79,125,447,548,550,551,552]),([0,1,2,3,5,41,46],[4,14,16,20,32,36,37,38,40,41,42,66,92,133,243,556,557,558]),([0,1,2,3,4,5,6,95],[0,1,3,4,16,29,30,43,46,48,79,108,133,138,244,387,388,554,559,560,561,562,563,564,565,566]),([1,2,3,4,5,6,136],[0,4,23,30,42,510,568,569,570,571]),([0,1,3,4,5,6,137],[4,23,30,42,48,79,218,572,573,574,575,576,577])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_6 = true := by decide +kernel
def h0Block8_7 : List NodeSpec := nodesWithIdentity [([0,1,3,4,5,6,138],[3,4,23,42,448,582,583,584,585,586,587]),([0,1,2,3,5,42,46],[4,16,20,23,37,38,40,41,42,66,293,513,594,595,596]),([0,1,2,3,5,42,54],[4,16,23,42,141,144,147,148,152,205,218,387,513,567,602,603,604]),([0,1,2,3,5,6,139],[4,23,42,43,132,133,138,153,448,513,608,609,610,611]),([0,1,2,3,4,6,140],[4,30,42,47,79,387,448,514,516,600,612,613,614,615]),([0,1,2,3,5,44,46],[4,20,23,32,36,37,38,40,41,42,43,66,92,251,617,618,619]),([0,1,2,3,5,44,54],[23,141,142,143,144,147,148,152,205,251,616,620,621,622]),([0,2,3,4,5,6,82],[1,16,47,108,125,133,624,627,628,629,630,631]),([0,1,2,3,4,5,83],[4,12,14,16,25,79,87,119,153,627,628,633,634,635,636]),([0,1,2,3,4,5,87],[0,1,12,23,25,47,79,87,119,125,153,637,638,639,640,641,642]),([0,1,2,3,5,46,47],[4,16,20,36,37,38,40,41,42,43,66,92,117,133,643,644,645,646,647]),([0,1,2,3,5,46,50],[4,16,20,36,37,38,40,41,43,66,92,117,133,660,661,662,663,664])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_7 = true := by decide +kernel
def h0Block8_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,5,46,51],[4,14,16,20,36,37,38,40,41,42,43,66,117,132,133,665,666,667,668]),([0,1,2,3,5,46,53],[4,16,20,23,36,37,38,40,41,43,66,92,132,133,669,670,671,672]),([0,1,2,3,5,6,46,48],[20,32,36,37,38,40,41,42,66,92,117,138,673,674,675,676,677]),([0,1,2,3,5,6,46,49],[20,32,36,37,38,40,41,42,66,92,117,138,678,679,680,681,682]),([0,1,2,3,5,6,46,52],[14,20,32,36,37,38,40,41,42,66,117,125,132,138,683,684,685,686]),([0,1,2,3,5,46,56],[4,20,32,36,37,38,40,41,42,43,66,117,134,264,687,688,689]),([0,1,2,3,5,46,57],[4,14,16,20,37,38,40,41,42,66,483,690,691,692]),([0,1,2,3,5,46],[36]),([0,1,2,3,5,6,46],[36,43,153]),([1,2,3,4,5,6,132],[0,4,14,42,47,479,700,701,702,703]),([0,1,2,3,5,6,133],[4,14,43,132,133,138,153,388,483,487,488,492,493]),([0,2,3,4,5,7,68],[4,12,16,79,120,709,711,712,713,714,715])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_8 = true := by decide +kernel
def h0Block8_9 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,149],[0,1,4,12,16,25,87,108,119,121,123,133,153,709,710,717,718,719,720]),([0,1,2,3,4,5,7,114],[0,1,4,16,25,108,133,218,319,335,346,347,348,349,350,352,704,705,706,709,723,724,727,728,729,730]),([0,1,2,3,4,5,150],[0,1,4,12,16,25,79,87,119,133,153,316,319,710,723,731,732,733,734,735]),([0,1,2,3,4,5,151],[0,1,4,12,16,25,79,87,119,133,153,368,371,709,710,739,740,741,742]),([0,1,2,3,4,5,154],[0,1,25,27,87,108,119,133,153,710,736,756,764,765,766,767,768,769,770,771]),([0,2,3,4,5,22,26],[2,12,13,15,16,22,24,153,169,773,777,778,779,780,781]),([0,2,3,4,5,24,26],[2,4,12,15,16,24,42,119,710,788,793,794,795,796,797,798]),([0,1,2,3,4,5,156],[0,1,23,25,45,79,87,119,125,133,153,710,788,802,803,804,805,806,807,808]),([0,1,2,3,4,5,157],[0,1,16,23,25,45,79,87,119,153,632,736,816,817,818,819,820,821,822]),([0,1,2,3,4,5,130],[0,4,12,16,79,87,108,119,133,153,169,434,435,436,828,829]),([0,2,3,4,5,21,125],[1,16,25,87,440,755,758,760,837,838,839,840,841]),([0,1,2,3,4,5,160],[0,1,12,25,79,87,108,119,133,153,322,755,758,760,843,844,845,846,847])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_9 = true := by decide +kernel
def h0Block8_10 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,161],[0,1,12,25,79,87,108,119,133,153,322,787,791,792,850,851,852,853,854]),([0,2,3,4,5,23,125],[1,16,25,108,224,440,840,841,855,856,857,858]),([0,1,2,3,4,5,40,125],[1,3,16,25,79,87,108,119,125,169,224,440,710,837,840,841,859,860,861,862,863,864,865,866]),([0,1,2,3,4,5,41,125],[1,3,16,25,79,87,108,119,169,224,240,243,244,245,246,440,553,555,710,725,837,839,840,841,867]),([0,1,2,3,4,5,125,158],[1,16,25,42,79,87,169,224,246,440,837,840,841,868,869,870,871]),([0,1,2,3,4,5,125,159],[1,16,25,42,79,87,169,224,440,837,839,840,841,872,873,874,875]),([0,1,3,4,5,10,19,39],[12,25,49,194,218,285,286,333,540,884,885,886,887,888,889,890,891,892]),([0,1,2,3,4,5,162],[0,1,12,59,87,108,119,133,153,168,710,736,760,896,897,898,899,900,901,902]),([0,1,2,3,4,5,10,155],[1,4,12,16,25,49,59,60,61,67,68,69,108,133,387,801,907,909,910,911,912,913,914,915,916,917,918]),([0,1,2,3,4,5,163],[0,1,12,69,79,87,119,133,153,154,168,710,792,919,920,921,922,923,924,925]),([0,1,2,3,4,5,39,60],[16,25,49,53,58,79,87,133,153,285,286,293,333,336,337,540,710,926,927,928,929,930,931,932,933]),([0,1,2,3,4,5,10,104],[1,4,12,16,25,49,59,60,61,68,69,79,133,168,322,333,890,935,936,937,938,939,940,941,942,943,944])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_10 = true := by decide +kernel
def h0Block8_11 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,10,95],[1,4,12,25,49,59,60,61,67,68,79,108,132,133,244,387,559,560,561,562,564,566,736,918,946,947,948]),([0,1,2,3,4,5,165],[0,1,12,16,69,79,87,119,153,168,191,736,951,952,953,954,955,956,957]),([0,1,2,3,4,5,166],[0,1,12,25,79,87,108,119,133,153,322,755,756,758,971,972,973,974]),([0,1,2,3,4,5,167],[0,1,12,25,79,87,108,119,133,153,322,787,788,791,970,977,978,979,980]),([0,1,2,3,4,5,41,135],[1,12,16,48,79,87,108,119,132,224,240,243,244,246,295,496,553,710,981,982,983,984,985]),([0,1,2,3,4,5,168],[0,1,25,85,87,108,119,133,153,710,736,997,998,999,1000,1001,1002]),([0,1,2,3,4,5,12,168],[1,12,70,85,86,87,88,93,94,95,993,997,998,999,1000,1002]),([0,2,3,4,5,20,63],[4,12,16,42,70,78,79,84,710,1007,1008,1009,1010,1011,1012]),([0,1,2,3,4,5,171],[0,1,12,86,87,108,119,133,153,710,736,985,1016,1017,1018,1019,1020,1021,1022]),([0,2,3,4,5,22,63],[16,70,77,78,79,83,84,153,169,783,1024,1025,1026,1027]),([0,2,3,4,5,24,63],[4,16,42,70,78,79,84,119,710,800,1030,1031,1032,1033,1034]),([0,1,2,3,4,5,172],[0,1,12,23,25,87,95,119,133,153,710,908,1035,1036,1037,1038,1039,1040,1041])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_11 = true := by decide +kernel
def h0Block8_12 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,33,63],[12,16,25,42,70,73,77,78,79,84,133,153,230,231,241,242,261,262,448,710,1007,1026,1034,1042,1043,1044]),([0,1,2,3,4,5,34,63],[12,16,25,42,70,73,77,79,84,133,153,218,278,279,288,289,308,309,710,1007,1026,1034,1042,1045,1046]),([0,1,2,3,4,5,12,89],[1,4,16,25,70,79,85,86,87,88,94,95,133,162,230,235,236,322,448,1047,1049,1050,1051,1052,1053,1054,1055,1056]),([0,1,2,3,4,5,173],[0,1,12,16,86,87,108,119,153,448,908,1057,1058,1059,1060,1061,1062,1063]),([0,1,2,3,4,5,12,102],[1,4,12,16,70,79,85,86,87,88,92,94,95,133,278,322,985,1064,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075]),([1,2,3,4,5,12,110],[4,25,86,87,108,316,710,1078,1079,1080,1081,1082,1083]),([0,1,2,3,4,5,176],[0,1,12,16,23,86,87,95,119,133,153,736,1084,1085,1086,1087,1088,1089,1090]),([0,1,2,3,4,5,177],[0,1,16,23,25,85,87,119,133,153,736,1093,1094,1095,1096,1097,1098]),([0,1,2,3,4,5,178],[0,1,12,16,23,25,87,95,119,153,736,1100,1101,1102,1103,1104,1105]),([0,1,2,3,4,5,144],[0,4,12,16,25,79,87,108,119,133,153,169,513,567,608,1110,1111]),([0,1,2,3,4,5,179],[0,1,12,25,79,87,108,119,133,153,322,885,887,1117,1119,1120,1121,1122]),([0,1,2,3,4,5,180],[0,1,12,25,79,87,108,119,133,153,322,751,753,1125,1126,1127,1128,1129,1130])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_12 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_12 = true := by decide +kernel
def h0Block8_13 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,181],[0,12,25,79,87,108,119,133,153,322,787,791,1132,1133,1134,1135]),([0,1,2,3,4,5,35,98],[1,12,16,25,29,79,92,108,119,169,195,249,315,316,319,334,335,338,341,448,710,1136,1137,1138,1139]),([0,1,2,3,4,5,36,98],[1,12,16,25,29,79,92,108,119,168,169,195,249,367,368,372,373,374,379,470,710,1138,1139,1143,1144]),([0,1,2,3,4,5,98,182],[1,12,16,25,42,79,169,195,249,1138,1139,1145,1146,1147,1148]),([0,1,2,3,4,5,98,183],[1,12,16,25,42,79,168,169,195,249,1138,1139,1149,1150,1151,1152]),([1,2,3,4,5,13,110],[4,14,25,87,108,316,319,710,1081,1125,1155,1156,1157,1158]),([0,1,2,3,4,5,185],[0,1,12,14,16,25,79,87,119,133,153,316,319,1125,1159,1160,1161,1162,1163]),([0,1,2,3,4,5,186],[0,1,12,16,25,79,87,119,133,153,168,368,371,1117,1166,1167,1168,1169]),([1,2,3,4,5,14,61],[4,12,16,23,53,58,153,322,1175,1176,1177,1178,1179]),([0,2,3,4,5,19,58],[1,16,25,36,133,169,210,224,885,1180,1181,1182]),([0,1,2,3,4,5,187],[0,1,12,25,79,87,108,119,133,153,322,885,1175,1178,1185,1186,1187,1188]),([0,1,2,3,4,5,188],[0,1,12,25,79,87,108,119,133,153,322,751,1178,1191,1192,1193,1194,1195,1196])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_13 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_13 = true := by decide +kernel
def h0Block8_14 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,21,58],[1,16,36,87,133,168,169,755,1182,1198,1199,1200]),([0,1,2,3,4,5,189],[0,12,25,79,87,108,119,133,153,322,755,1178,1201,1202,1203,1204]),([0,1,2,3,4,5,190],[0,12,25,79,87,108,119,125,133,134,153,322,787,1206,1207,1208,1209]),([0,2,3,4,5,23,58],[1,16,36,108,125,133,168,224,855,1035,1182,1210]),([0,1,2,3,4,5,30,58],[1,12,14,16,25,36,43,79,87,125,133,162,210,388,710,895,1182,1198,1212,1219,1220,1221,1222,1223,1224,1225,1226]),([0,1,2,3,4,5,32,58],[1,12,16,25,36,43,79,87,92,133,162,168,182,183,187,190,193,194,196,199,210,219,224,388,710,1035,1182,1198,1200,1227]),([0,1,2,3,4,5,35,58],[1,12,16,23,25,36,43,108,117,119,133,162,169,210,224,315,316,334,335,338,341,342,345,388,710,736,1182,1198,1217,1228]),([0,1,2,3,4,5,40,58],[1,14,16,36,43,79,87,108,119,133,162,168,169,210,388,710,860,861,862,864,865,866,1182,1198,1217,1229,1230,1231]),([0,1,2,3,4,5,41,58],[1,16,23,36,43,79,87,108,119,133,162,168,169,210,240,243,244,245,246,295,388,553,556,558,710,1182,1198,1200,1217]),([0,1,2,3,5,45,58],[26,36,43,92,119,125,132,133,153,162,169,625,736,1182,1214,1217,1218]),([0,1,2,3,4,5,191],[0,1,12,16,25,87,108,119,121,125,132,133,153,168,1175,1234,1235,1236,1237]),([0,1,2,3,4,5,14,110],[1,4,133,153,218,316,710,1081,1170,1171,1172,1175,1183,1191,1242,1243,1244,1245,1246])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_14 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_14 = true := by decide +kernel
def h0Block8_15 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,192],[0,1,12,16,25,79,87,117,119,133,153,316,1178,1184,1191,1247,1248,1249,1250,1251]),([0,1,2,3,4,5,193],[0,1,12,16,25,79,87,119,133,153,168,368,1175,1178,1254,1255,1256,1257]),([1,2,3,4,5,15,61],[4,12,14,53,58,153,1177,1264,1267,1268]),([0,2,3,4,5,19,76],[1,16,25,108,168,263,885,887,996,1297,1298,1299]),([0,1,2,4,5,19,194],[1,79,92,108,322,885,993,1300,1301,1302,1303,1304,1305,1306]),([0,1,2,3,4,5,196],[0,1,12,25,79,87,108,119,133,153,322,885,887,1296,1315,1316,1317,1318]),([0,1,2,4,5,20,194],[1,79,92,108,322,448,751,1006,1300,1303,1305,1306,1311,1322,1323,1324]),([0,1,2,3,4,5,197],[0,1,12,25,79,87,108,119,133,153,322,751,753,1321,1325,1326,1327,1328,1329]),([0,1,2,3,4,5,198],[0,12,25,79,87,108,119,133,153,322,755,758,1331,1332,1333,1334]),([0,1,2,3,4,5,29,76],[1,12,16,25,46,79,87,108,117,120,121,123,126,131,164,165,166,168,224,263,710,1298,1299,1335,1336,1337]),([0,1,2,3,4,5,30,76],[1,12,16,25,26,46,79,87,108,117,168,224,263,710,895,1212,1221,1222,1224,1225,1226,1299,1336,1337,1338,1339,1340]),([0,1,2,3,4,5,31,76],[1,12,16,25,46,79,87,108,117,168,263,710,1298,1299,1336,1337,1347,1348,1349,1350,1351,1352,1353,1354,1355])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_15 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_15 = true := by decide +kernel
def h0Block8_16 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,32,76],[1,12,16,25,46,79,87,108,117,168,182,183,185,187,190,193,194,219,222,224,263,710,1299,1336,1337,1356]),([0,1,2,3,4,5,199],[0,1,12,16,25,87,108,119,121,123,133,153,168,1296,1359,1360,1361,1362,1363]),([0,1,2,3,4,5,200],[0,1,25,79,87,109,119,133,153,266,710,996,1368,1369,1370,1371,1372,1373,1374]),([0,1,2,3,4,5,201],[0,1,12,79,87,110,119,133,153,266,710,1374,1377,1378,1379,1380,1381,1382,1383]),([0,1,2,3,4,5,202],[0,1,12,25,87,111,119,133,153,266,710,1374,1385,1386,1387,1388,1389,1390]),([0,2,3,4,5,22,65],[16,96,103,107,108,134,153,786,1392,1393,1394,1395]),([0,1,2,3,4,5,29,65],[4,12,14,16,25,79,87,96,99,108,117,120,121,126,131,134,164,165,516,710,1394,1397,1398,1399,1400,1401]),([0,1,2,3,4,5,32,65],[4,12,14,16,25,79,87,96,99,108,117,134,182,183,187,190,193,194,219,710,1394,1397,1398,1400,1402,1403,1404,1405]),([0,1,2,3,4,5,33,65],[12,16,25,42,96,99,103,108,133,153,163,230,231,241,242,261,262,710,1394,1397,1398,1400,1403,1405,1406,1407]),([0,1,2,3,4,5,34,65],[12,16,25,96,99,103,108,117,133,153,218,278,279,288,289,308,309,710,1394,1397,1398,1400,1405,1408,1409]),([0,1,2,3,4,5,39,65],[16,79,87,96,99,103,108,117,133,153,285,286,293,333,336,337,540,710,1394,1397,1398,1400,1403,1405,1410,1411]),([0,1,2,3,4,5,203],[0,1,14,16,25,87,109,119,133,153,165,266,1178,1414,1415,1416,1417,1418,1419])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_16 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_16 = true := by decide +kernel
def h0Block8_17 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,204],[0,1,12,16,79,87,110,119,153,266,1178,1424,1425,1426,1427,1428,1429,1430]),([0,1,2,3,4,5,39,61],[4,12,16,23,49,53,58,79,87,133,153,285,286,293,322,333,336,337,540,930,1177,1438,1439,1440]),([0,1,2,3,4,5,19,103],[0,4,12,16,25,79,132,133,224,540,710,887,990,993,994,995,996,1442,1443,1444,1445,1446,1447,1448,1449,1450]),([0,1,2,3,4,5,19,93],[0,4,12,16,25,79,92,108,224,516,553,710,990,993,994,995,1269,1452,1453,1454,1455,1456,1457,1458,1459,1460]),([0,1,2,3,4,5,19,81],[0,4,12,16,25,108,132,133,625,710,887,990,993,994,995,996,1462,1463,1464,1465,1466,1467,1468,1469,1470]),([0,1,2,3,4,5,210],[0,1,4,25,79,87,119,132,153,632,736,1475,1476,1477,1478,1479]),([0,1,2,3,4,5,16,92],[1,4,12,16,42,92,108,119,133,169,230,236,1054,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,1492]),([0,1,2,3,4,5,129],[0,4,12,14,16,79,87,108,119,133,153,434,436,710,1493,1494,1495]),([0,1,2,3,4,5,20,103],[0,4,12,16,25,79,133,224,540,710,753,985,1003,1006,1013,1014,1015,1442,1445,1446,1447,1448,1449,1498,1499,1500,1501]),([0,1,2,3,4,5,20,93],[0,4,12,16,25,79,92,108,224,553,710,985,1003,1006,1013,1014,1275,1452,1456,1457,1458,1459,1503,1504,1505,1506,1507]),([0,1,2,3,4,5,20,81],[0,4,12,16,25,108,133,625,710,753,985,1003,1006,1013,1014,1015,1462,1466,1467,1468,1469,1470,1509,1510,1511,1512]),([0,1,2,3,4,5,211],[0,1,4,12,79,87,119,153,191,736,985,1178,1513,1514,1515,1516,1517,1518])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_17 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_17 = true := by decide +kernel
def h0Block8_18 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,7,136],[0,4,16,23,169,510,567,568,710,724,1524]),([0,1,2,3,4,5,33,136],[4,12,16,23,25,42,79,133,153,230,241,242,261,262,322,448,510,567,568,569,570,571]),([0,1,2,3,4,5,34,136],[4,12,16,23,25,42,79,133,153,218,278,288,289,308,309,322,448,510,567,568,569,570,571]),([0,1,2,3,4,5,212],[0,1,4,12,87,108,119,153,242,760,771,895,1526,1527,1528,1529,1530,1531]),([0,2,3,4,5,21,111],[16,25,42,87,108,315,322,327,760,763,1534,1535,1536,1537]),([0,1,2,3,4,5,213],[0,1,4,12,87,119,133,153,338,760,771,895,1538,1539,1540,1541,1542]),([0,1,2,3,4,5,214],[0,1,4,25,87,119,133,153,372,756,771,895,1544,1545,1546,1547]),([0,1,2,3,4,5,215],[0,1,4,12,25,87,92,119,153,189,771,895,1548,1549,1550,1551,1552]),([0,1,2,3,4,5,143],[0,4,12,16,23,25,79,87,108,119,133,153,513,567,609,710,1556,1557,1558]),([0,1,2,3,4,5,29,131],[4,12,14,16,23,25,79,87,120,123,126,131,132,133,164,165,322,461,1559,1560,1561,1562,1563]),([0,1,2,3,4,5,32,131],[4,12,14,16,23,25,79,87,132,133,182,185,187,190,193,194,219,322,461,1559,1560,1562,1563,1564]),([0,1,2,3,4,5,22,67],[0,4,12,16,79,121,123,133,153,697,710,772,773,776,782,785,786,1566,1567,1568,1569,1570,1571,1572,1573,1574])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_18 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_18 = true := by decide +kernel
def h0Block8_19 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,22,79],[0,4,16,25,79,133,153,183,185,697,710,772,773,776,782,785,786,1571,1576,1577,1578,1579,1580,1581,1582]),([0,1,2,3,4,5,22,110],[0,4,16,25,108,133,153,316,319,697,710,772,773,776,782,783,785,1080,1081,1242,1245,1246,1585,1586]),([0,2,3,4,5,22,111],[16,25,108,153,315,322,325,327,332,776,786,1587,1588,1589,1590]),([0,1,2,3,4,5,22,118],[0,4,12,16,108,133,153,368,371,697,710,772,773,776,782,783,785,1593,1594,1595,1596,1597,1598,1599]),([0,1,2,3,4,5,22,93],[0,4,16,79,108,133,153,553,555,697,710,773,776,782,783,785,1452,1456,1457,1458,1459,1504,1601,1602]),([0,1,2,3,5,22,81],[0,26,92,132,133,153,625,697,710,786,1466,1469,1572,1604,1605,1606]),([1,2,3,4,5,7,132],[0,4,14,16,479,699,700,710,716,895,1607]),([0,1,2,3,4,5,29,132],[4,12,14,16,25,79,87,108,117,120,126,131,164,165,322,479,516,700,701,702,703,895]),([0,1,2,3,4,5,32,132],[4,12,14,16,25,79,87,108,117,182,187,190,193,194,219,322,479,516,623,700,701,702,703,895]),([0,1,2,3,4,5,33,132],[4,12,16,25,42,108,133,153,163,230,241,242,261,262,322,479,516,623,699,700,701,702,703]),([0,1,2,3,4,5,34,132],[4,12,16,25,42,108,117,133,153,218,278,288,289,308,309,322,479,516,623,699,700,701,702,703]),([0,1,2,3,4,5,39,132],[4,14,16,79,87,108,117,133,134,153,285,286,293,322,333,336,337,479,516,623,699,700,701,702,703])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_19 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_19 = true := by decide +kernel
def h0Block8_20 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,217],[0,1,4,25,87,119,125,133,153,165,516,788,1609,1610,1611,1612]),([0,1,2,3,4,5,218],[0,1,4,12,79,87,119,153,154,163,262,792,1615,1616,1617,1618,1619,1620]),([0,1,2,3,4,5,78],[0,1,4,12,16,23,42,79,87,108,119,133,153,168,176,710,1622,1623,1624]),([0,1,2,3,4,5,77],[0,4,12,16,23,79,108,119,133,153,177,180,985,1628,1629,1630,1631]),([0,1,2,3,4,5,29,81],[4,12,14,25,79,87,108,120,126,132,133,164,165,625,895,1462,1466,1467,1469,1470,1633,1634,1635]),([0,1,2,3,4,5,220],[0,1,4,16,25,87,119,132,153,165,632,1374,1641,1642,1643,1644,1645]),([0,1,2,3,4,5,74],[0,4,12,16,79,87,108,119,123,133,153,156,710,1646,1647,1648,1649,1650]),([0,1,2,3,4,5,75],[0,1,4,12,16,79,87,108,119,133,153,155,322,1651,1652,1653,1654,1655]),([0,1,2,3,4,5,216],[0,1,4,16,23,25,79,87,108,119,133,153,1578,1656,1657,1658,1659,1660,1661,1662]),([0,1,2,3,4,5,221],[0,4,23,25,79,108,119,133,153,1667,1668,1669,1670,1671,1672,1673,1674]),([0,1,2,3,4,5,45,80],[16,23,25,42,79,92,108,119,133,153,182,188,191,192,624,625,632,895,1519,1663,1664,1665,1666,1669,1675,1676,1677,1678]),([0,1,2,3,4,5,32,81],[4,12,14,25,79,87,92,108,133,182,190,193,194,219,625,895,1462,1466,1467,1468,1469,1470,1509,1680,1681,1682])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_20 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_20 = true := by decide +kernel
def h0Block8_21 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,32,82],[12,14,16,23,25,79,87,108,133,162,182,183,190,193,194,219,624,628,1679,1683,1684,1685,1686,1687,1688,1689]),([0,1,2,3,4,5,100],[0,1,4,14,16,23,25,42,79,87,108,119,133,153,163,169,267,1695,1696,1697]),([0,1,2,3,4,5,91],[0,4,14,25,79,87,108,119,133,235,236,1698,1699,1700,1701,1702,1703]),([0,1,2,3,4,5,41,89],[14,16,25,79,87,108,119,133,162,169,230,235,240,244,245,246,295,553,1049,1051,1052,1054,1055,1056,1178,1704,1705]),([0,1,2,3,4,5,33,93],[4,12,25,42,79,108,133,153,224,230,241,242,247,261,448,553,555,1178,1452,1456,1457,1458,1459,1504,1707,1708]),([0,1,2,3,4,5,33,94],[12,16,23,25,42,79,108,133,153,230,231,240,241,242,247,261,262,448,650,1337,1706,1709,1710,1711,1712,1713,1714,1715,1716]),([0,1,2,3,4,5,223],[0,1,4,12,16,23,79,87,108,119,133,153,1717,1721,1722,1723,1724,1725,1726]),([0,1,2,3,4,5,174],[0,4,12,14,79,87,108,119,133,1067,1727,1728,1729,1730,1731,1732]),([0,1,2,3,4,5,41,102],[12,14,16,79,87,108,119,133,240,244,245,246,278,295,296,553,985,1066,1067,1069,1070,1072,1073,1074,1178,1733,1734]),([0,1,2,3,4,5,34,93],[4,12,25,42,79,108,133,153,218,224,278,288,289,297,308,553,555,1178,1452,1456,1457,1458,1459,1736,1737]),([0,1,2,3,4,5,34,94],[12,16,23,25,42,79,108,133,153,218,240,278,279,288,289,297,308,309,650,1710,1713,1714,1715,1716,1735,1738,1739]),([0,1,2,3,4,5,116],[0,1,4,14,16,25,42,79,87,108,119,133,153,353,710,895,1740,1741,1742])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_21 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_21 = true := by decide +kernel
def h0Block8_22 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,39,110],[4,14,25,42,79,87,108,133,153,285,286,293,316,319,333,337,540,895,1080,1081,1242,1245,1246,1586,1743,1744]),([0,1,2,3,4,5,110,175],[4,14,25,108,133,153,316,319,710,1080,1081,1242,1245,1246,1745,1746,1747,1748,1749,1750]),([0,1,2,3,4,5,113],[0,4,14,25,79,87,108,133,153,321,325,1753,1754,1755,1756,1757,1758]),([0,1,2,3,4,5,39,111],[14,16,23,25,42,79,87,108,133,153,285,286,293,315,321,327,333,337,540,1535,1589,1751,1752,1759,1760,1761]),([0,1,2,3,4,5,35,104],[12,16,23,25,79,108,119,133,162,315,316,333,335,338,339,341,448,895,935,936,939,940,941,942,943,1762,1763,1764]),([0,1,2,3,4,5,124],[0,1,4,12,14,16,42,79,87,108,119,133,153,168,395,710,1765,1766,1767]),([0,1,2,3,4,5,123],[0,4,12,14,16,79,87,108,133,153,396,399,985,1771,1772,1773,1774]),([0,1,2,3,4,5,205],[0,4,12,16,23,25,79,87,108,119,133,153,1445,1776,1777,1778,1779,1780,1781]),([0,1,2,3,4,5,164],[0,4,12,23,25,79,108,119,133,936,1782,1783,1784,1785,1786]),([0,1,2,3,4,5,206],[0,4,12,16,25,42,79,87,108,119,133,153,1456,1787,1788,1789,1790,1791,1792]),([0,1,2,3,4,5,222],[0,4,12,25,79,108,133,153,650,1710,1793,1794,1795,1796,1797]),([0,1,2,3,4,5,145],[0,4,12,14,16,25,42,79,87,108,119,133,153,633,895,1798,1799,1800,1801])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_22 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_22 = true := by decide +kernel
def h0Block8_23 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,81,207],[4,12,14,25,108,133,625,710,1462,1466,1467,1468,1469,1470,1509,1802,1803,1804,1805,1806,1807,1808]),([0,1,2,3,4,5,81,208],[4,12,14,25,108,133,625,710,1462,1466,1467,1468,1469,1470,1509,1809,1810,1811,1812,1813,1814,1815]),([0,1,2,3,4,5,84],[0,4,12,14,25,79,87,108,133,627,628,1816,1817,1818,1819])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_23 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_23 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1 ++ h0Block8_2 ++ h0Block8_3 ++ h0Block8_4 ++ h0Block8_5 ++ h0Block8_6 ++ h0Block8_7 ++ h0Block8_8 ++ h0Block8_9 ++ h0Block8_10 ++ h0Block8_11 ++ h0Block8_12 ++ h0Block8_13 ++ h0Block8_14 ++ h0Block8_15 ++ h0Block8_16 ++ h0Block8_17 ++ h0Block8_18 ++ h0Block8_19 ++ h0Block8_20 ++ h0Block8_21 ++ h0Block8_22 ++ h0Block8_23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Nodes8 = true := by
  unfold h0Nodes8 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0Test8_0,h0Test8_1⟩,h0Test8_2⟩,h0Test8_3⟩,h0Test8_4⟩,h0Test8_5⟩,h0Test8_6⟩,h0Test8_7⟩,h0Test8_8⟩,h0Test8_9⟩,h0Test8_10⟩,h0Test8_11⟩,h0Test8_12⟩,h0Test8_13⟩,h0Test8_14⟩,h0Test8_15⟩,h0Test8_16⟩,h0Test8_17⟩,h0Test8_18⟩,h0Test8_19⟩,h0Test8_20⟩,h0Test8_21⟩,h0Test8_22⟩,h0Test8_23⟩
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket7Ok h0Check8
def h0Block9_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,6,8],[0,1,2,3,4,5,6,7,12,14,16,25,26,27,28,29,30,31,43,44,45,46,47,48]),([0,1,2,3,4,5,6,10],[0,1,3,4,12,14,16,25,26,29,30,43,46,47,48,49,50,51,52,59,60,61,68,69]),([0,1,2,3,4,5,6,12],[0,1,3,4,16,23,26,29,30,43,46,47,48,70,71,72,79,85,86,87,88,94,95]),([0,1,2,3,4,5,6,18],[0,1,3,4,14,16,26,29,30,43,46,47,48,96,97,98,108,109,110,111,112,113,119]),([0,1,2,3,4,5,6,29],[0,1,3,4,12,14,16,25,29,43,46,47,79,87,120,121,122,123,124,125,126,132,164,165]),([0,1,2,3,4,5,6,32],[0,1,3,4,12,14,16,25,29,30,43,46,47,48,79,87,92,182,183,184,185,186,190,193,194,219]),([0,1,2,3,4,5,6,33],[0,1,3,4,12,16,25,26,29,30,42,43,46,47,48,133,153,163,230,231,232,233,241,242,261,262]),([0,1,2,3,4,5,6,34],[0,1,3,4,12,16,25,26,29,30,42,43,46,47,133,153,218,278,279,280,281,288,289,308,309]),([0,1,2,3,4,5,6,35],[0,1,3,4,12,16,23,25,29,30,43,46,47,48,108,117,119,315,316,317,318,319,335,338,341]),([0,1,2,3,4,5,6,36],[0,1,3,4,12,16,23,25,29,30,43,46,108,119,125,132,367,368,369,370,371,372,373,374]),([0,1,2,3,4,5,6,25],[2,3,4,12,14,16,23,25,29,30,42,43,46,47,48,195,401,402,407,414,426,437]),([0,1,2,3,4,5,6,37],[0,1,3,4,12,14,23,25,29,30,42,43,46,47,48,218,406,440,441,442,443,444,448])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,6,38],[0,1,3,4,12,14,23,25,29,30,42,43,46,47,48,125,132,496,497,498,499,500,501,516]),([0,1,2,3,4,5,6,27],[3,4,8,12,13,14,16,23,25,29,30,42,43,46,47,48,218,502,534]),([0,1,2,3,4,5,6,39],[0,1,3,4,14,16,26,29,30,43,46,47,48,79,87,125,133,153,285,286,293,333,336,337,540,541]),([0,1,2,3,4,5,6,41],[0,1,3,4,14,16,23,29,30,43,46,47,48,79,87,92,108,119,240,244,245,246,295,553,554,555]),([0,1,2,3,4,5,6,42],[3,4,16,23,29,30,42,43,46,47,48,79,87,448,509,510,513,514,567]),([0,1,2,3,4,5,6,44],[0,1,3,4,14,23,29,30,43,46,47,48,79,87,92,249,251,448,519,521,616,623]),([0,1,2,3,4,5,6,45],[0,1,3,4,16,23,26,29,30,43,46,47,48,108,119,125,133,153,188,189,191,624,625,626,632]),([0,1,2,3,5,46],[32,36,37,40,43,133]),([0,1,2,3,4,5,46],[0,1,12,25,26,32,36,37,40,43,79,87,92,108,117,119,132,133,153]),([0,1,2,3,5,6,46],[4,14,23,32,36,37,40,42,43,153]),([0,1,2,3,4,5,6,46],[0,1,3,4,14,23,26,29,30,32,36,37,40,42,43,46,47,48,92,117,125,132,133,138,153]),([0,1,2,3,5,6,54],[4,14,23,26,43,142,143,144,147,218,387])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Block9_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,55],[12,23,25,26,43,79,87,92,108,119,132,133,460,461,464,465]),([0,1,2,3,4,5,6,55],[3,4,14,23,26,29,30,43,46,47,48,132,133,138,153,460,461,464,465,697]),([0,1,2,3,4,5,6,56],[0,1,3,4,14,23,29,30,43,46,47,48,108,117,119,169,220,263,264,387,473,516,623,698]),([0,1,2,3,4,5,6,57],[3,4,14,16,29,30,42,43,46,47,48,108,119,387,478,479,482,483,516,699]),([0,1,2,3,4,5,7,29],[0,1,12,16,25,79,87,120,121,123,126,154,164,165,168,704,705,706,707,708,709,710,716]),([0,1,2,3,4,5,7,32],[0,1,12,16,25,79,87,182,183,185,190,193,194,219,704,705,706,709,710,716,721,722,723,724,725]),([0,1,2,3,4,5,7,35],[0,1,12,16,25,108,119,315,316,319,335,338,341,704,705,706,709,710,716,723,724,726,727,736]),([0,1,2,3,4,5,7,36],[0,1,12,16,25,108,119,154,168,367,368,371,372,373,374,704,705,706,709,710,724,737,738]),([0,1,2,3,4,5,7,41],[0,1,16,79,87,108,119,240,244,245,246,295,553,555,704,705,706,709,710,723,724,725,743]),([0,1,2,3,4,5,8,12],[1,2,4,12,25,26,27,28,31,44,45,70,79,85,86,87,88,94,95,710,744,745,746]),([0,1,2,3,4,5,8,18],[1,2,12,25,26,27,28,31,44,45,96,108,109,110,111,112,113,119,710,747,748,749]),([0,1,3,4,5,8,20],[0,1,2,12,25,125,710,736,750,751,752,753,754])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
def h0Block9_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,8,21],[0,1,2,4,12,16,25,27,28,31,44,45,79,87,92,132,194,710,736,755,756,757,758,759,760,761,762,763,771]),([0,1,2,3,4,5,8,22],[0,1,2,12,16,25,26,27,28,31,39,44,45,132,133,153,697,736,772,773,774,775,776,782,783,784,785,786]),([0,1,2,3,4,5,8,24],[0,1,2,4,12,16,23,25,27,28,31,44,45,108,117,119,125,132,710,787,788,789,790,791,792,799,800,801]),([0,1,2,3,4,5,26],[0,1,2,8,12,13,15,16,25,79,87,108,119,125,133,153,710,736,779,797,809]),([0,1,2,3,4,5,8,39],[1,2,12,25,26,27,28,31,44,45,79,87,125,133,153,194,285,286,293,333,336,337,540,810,811]),([0,1,2,3,4,5,8,41],[1,2,4,12,14,25,27,28,31,44,45,79,87,92,108,119,132,194,240,244,245,246,295,553,555,736,812,813]),([0,1,2,3,4,5,8,45],[1,2,12,23,25,26,27,28,31,44,45,108,119,132,133,153,188,189,191,624,625,632,736,814,815]),([0,1,2,3,4,5,59],[0,1,12,25,26,31,79,87,92,108,117,119,133,153,823,824,825,826,827]),([0,1,2,3,4,5,9,21],[0,1,12,16,25,79,87,322,650,755,756,758,760,761,762,763,830,831,832,833,834,835,836,842]),([0,1,2,3,4,5,9,24],[0,1,12,16,25,108,119,322,650,787,788,791,792,799,800,801,830,831,832,833,836,842,848,849]),([0,1,2,3,4,5,125],[0,1,3,16,25,26,79,87,108,119,133,153,169,440]),([0,1,2,3,4,5,9,41],[1,12,25,79,87,108,119,224,240,244,245,246,295,322,553,555,725,830,831,832,833,836,876,877])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
def h0Block9_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,10,12],[1,12,25,26,49,59,60,61,68,69,70,79,85,86,87,88,94,95,710,878,879,880]),([0,1,2,3,4,5,10,18],[1,12,25,26,49,59,60,61,68,69,96,108,109,110,111,112,113,119,710,881,882,883]),([0,1,3,4,5,10,19],[0,1,12,25,49,710,736,884,885,886,887,888]),([0,1,2,3,4,5,10,21],[0,1,4,12,16,25,49,59,60,61,68,69,79,87,92,168,710,736,755,756,758,760,761,762,763,771,893,894,895]),([0,1,2,3,4,5,10,22],[0,1,12,16,25,26,49,59,60,61,67,68,69,133,153,218,697,736,772,773,776,782,783,785,786,903,904,905]),([0,1,2,3,4,5,10,24],[0,1,4,12,16,23,25,49,59,60,61,68,69,108,117,119,168,710,787,788,791,792,799,800,801,906,907,908]),([0,1,2,3,4,5,60],[0,1,12,16,25,49,53,58,79,87,108,119,133,153,710,736,926,927,928,929]),([0,1,2,3,4,5,10,39],[1,12,25,26,49,59,60,61,68,69,79,87,133,153,218,285,286,293,333,336,337,540,890,908,934]),([0,1,2,3,4,5,10,41],[1,4,12,14,25,49,59,60,61,68,69,79,87,92,108,119,168,240,244,245,246,295,553,555,736,945,946]),([0,1,2,3,4,5,10,45],[1,12,23,25,26,49,59,60,61,68,69,108,119,133,153,188,189,191,218,624,625,632,736,949,950]),([0,1,2,3,4,5,62],[0,1,12,25,26,61,79,87,92,108,117,119,133,153,218,958,959,960,961,962]),([0,1,2,3,4,5,11,21],[0,1,12,16,25,79,87,132,194,322,755,756,758,761,762,763,963,964,965,966,967,968,969,970])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
def h0Block9_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,11,24],[0,1,12,16,25,108,119,132,322,787,788,791,799,800,801,963,964,965,966,969,970,975,976]),([0,1,2,3,4,5,135],[0,1,12,16,26,79,87,108,119,133,153,169,194,496,985]),([0,1,2,3,4,5,11,41],[1,12,25,79,87,108,119,132,194,224,240,244,246,295,322,553,555,963,964,965,966,969,986,987]),([0,1,2,3,4,5,12,18],[1,26,70,79,85,86,87,88,94,95,96,108,109,110,111,112,113,119,710,988,989]),([0,1,2,3,4,5,12,19],[0,1,4,12,16,25,70,79,85,87,88,92,94,95,132,194,710,736,885,887,990,991,992,993,994,995,996]),([0,1,2,3,4,5,12,20],[0,1,4,12,16,25,70,79,85,86,87,88,92,94,95,125,448,710,736,751,753,985,1003,1004,1005,1006,1013,1014,1015]),([0,1,2,3,4,5,12,22],[0,1,16,26,70,79,85,86,87,88,92,93,94,95,133,153,697,736,772,773,776,782,783,785,786,1023,1028]),([0,1,2,3,4,5,12,24],[0,1,4,16,23,70,79,85,86,87,88,92,94,95,108,117,119,710,787,788,791,792,799,800,801,908,1029,1035]),([0,1,2,3,4,5,63],[0,1,12,16,25,70,73,77,79,87,108,119,133,153,710,736,1026,1034,1042]),([0,1,2,3,4,5,12,33],[1,12,25,26,70,79,85,86,87,88,94,95,133,153,230,231,241,242,261,262,448,908,1047,1048]),([0,1,2,3,4,5,12,34],[1,12,25,26,70,79,85,87,88,92,94,95,133,153,194,218,278,279,288,289,308,309,1035,1064,1065]),([0,1,2,3,4,5,12,35],[1,4,12,23,25,70,79,85,86,87,88,92,94,95,108,117,119,315,316,319,335,338,341,736,1076,1077])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
def h0Block9_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,12,36],[1,4,12,23,25,70,79,85,87,88,92,94,108,119,132,194,367,368,371,372,373,374,736,1091,1092]),([0,1,2,3,4,5,12,45],[1,23,26,70,79,85,86,87,88,92,94,95,108,119,133,153,188,189,191,624,625,632,736,1099]),([0,1,2,3,4,5,64],[0,1,12,25,26,79,87,88,108,117,119,125,132,133,153,1106,1107,1108,1109]),([0,1,2,3,4,5,13,19],[0,1,12,16,25,79,87,92,194,322,885,887,990,994,995,996,1112,1113,1114,1115,1116,1117,1118]),([0,1,2,3,4,5,13,20],[0,1,12,16,25,79,87,92,322,751,753,1003,1013,1014,1015,1112,1113,1114,1117,1118,1123,1124,1125]),([0,1,2,3,4,5,13,24],[0,1,16,79,87,92,108,119,322,787,788,791,792,799,801,1112,1113,1114,1117,1118,1125,1131]),([0,1,2,3,4,5,98],[0,1,12,16,25,26,29,79,87,108,119,133,153,169,249]),([0,1,2,3,4,5,13,35],[1,12,14,25,79,87,92,108,119,315,316,319,322,335,341,448,1112,1113,1114,1117,1118,1125,1153,1154]),([0,1,2,3,4,5,13,36],[1,12,25,79,87,92,108,119,168,194,322,367,368,371,373,374,1112,1113,1114,1117,1164,1165]),([0,1,2,3,4,5,14,19],[0,1,12,16,25,132,133,153,322,885,990,993,994,995,996,1170,1171,1172,1173,1174,1175,1178,1183,1184]),([0,1,2,3,4,5,14,20],[0,1,12,16,25,133,153,218,322,751,1003,1006,1013,1014,1015,1170,1171,1172,1175,1178,1183,1184,1189,1190,1191]),([0,1,2,3,4,5,14,21],[0,1,16,79,87,92,133,153,322,755,756,760,761,762,763,1170,1171,1172,1175,1178,1183,1184,1191,1197])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_6 = true := by decide +kernel
def h0Block9_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,14,24],[0,1,16,108,119,125,133,134,153,322,387,787,788,792,799,800,801,1170,1171,1172,1175,1183,1184,1191,1205]),([0,1,2,3,4,5,58],[0,1,12,16,25,36,43,79,87,108,119,125,133,153,162,169]),([0,1,2,3,4,5,14,29],[1,12,25,79,87,120,121,125,126,132,133,153,164,165,168,322,1170,1171,1172,1175,1184,1232,1233]),([0,1,2,3,4,5,14,32],[1,12,25,79,87,92,133,134,153,182,183,190,193,194,219,224,322,1170,1171,1172,1175,1184,1191,1238,1239]),([0,1,2,3,4,5,14,35],[1,12,25,108,117,119,133,153,218,315,316,322,335,338,341,1170,1171,1172,1175,1178,1183,1184,1191,1240,1241]),([0,1,2,3,4,5,14,36],[1,12,25,108,119,125,133,153,168,322,367,368,372,373,374,387,1170,1171,1172,1175,1178,1183,1252,1253]),([0,1,2,3,4,5,14,41],[1,79,87,108,119,133,153,224,240,244,245,246,295,322,553,1170,1171,1172,1175,1178,1183,1191,1258]),([0,1,2,3,5,14,45],[26,92,119,132,153,625,1170,1172,1178,1184,1259,1260]),([0,1,2,3,4,5,15,19],[0,1,4,12,16,25,26,132,133,153,736,885,887,990,993,994,995,996,1261,1262,1263,1264,1265,1266,1269,1270,1271]),([0,1,2,3,4,5,15,20],[0,1,4,12,16,25,26,133,153,218,736,751,753,1003,1006,1013,1014,1015,1261,1262,1263,1264,1270,1271,1272,1273,1274,1275]),([0,1,2,3,4,5,15,21],[0,1,4,16,26,79,87,133,153,736,755,756,758,760,761,762,763,771,1261,1262,1263,1264,1270,1271,1272,1276,1277]),([0,1,2,3,5,15,22],[0,1,26,92,117,132,133,153,772,786,1261,1278,1279])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_7 = true := by decide +kernel
def h0Block9_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,15,24],[0,1,4,16,26,108,119,125,133,134,153,387,787,788,791,792,799,800,801,1261,1262,1263,1264,1270,1271,1272,1280,1281]),([0,1,2,3,4,5,15,29],[1,4,12,25,26,79,87,120,121,123,125,126,131,132,133,153,164,165,650,1261,1262,1263,1264,1271,1282,1283]),([0,1,2,3,4,5,15,32],[1,4,12,25,26,79,87,92,133,134,153,182,183,185,187,190,193,194,219,650,1261,1262,1263,1264,1271,1272,1284,1285]),([0,1,2,3,4,5,15,35],[1,4,12,23,25,26,108,117,119,133,153,218,315,316,319,334,335,338,341,650,736,1261,1262,1263,1264,1270,1272,1286,1287]),([0,1,2,3,4,5,15,36],[1,4,12,23,25,26,108,119,132,133,153,367,368,371,372,373,374,379,387,650,736,1261,1262,1263,1264,1270,1288,1289]),([0,1,2,3,4,5,15,41],[1,4,23,26,79,87,92,108,119,133,153,240,243,244,245,246,295,553,555,650,736,1261,1262,1263,1264,1270,1271,1272,1290]),([0,1,2,3,4,5,17,19],[0,1,12,16,25,108,117,119,322,885,887,990,993,994,995,1291,1292,1293,1294,1295,1296,1314]),([0,1,2,3,4,5,17,20],[0,1,12,16,25,108,117,119,322,751,753,1003,1006,1013,1014,1291,1292,1293,1296,1314,1319,1320,1321]),([0,1,2,3,4,5,17,21],[0,1,16,79,87,108,117,119,322,755,756,758,760,761,762,1291,1292,1293,1296,1314,1321,1330]),([0,1,2,3,4,5,76],[0,1,12,16,25,26,46,79,87,108,119,133,153,263,1337]),([0,1,2,3,4,5,17,29],[1,12,25,79,87,108,117,119,120,121,123,126,164,168,322,1291,1292,1293,1296,1357,1358]),([0,1,2,3,4,5,17,32],[1,12,25,79,87,108,117,119,182,183,185,190,194,219,224,322,1291,1292,1293,1296,1314,1321,1364,1365])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_8 = true := by decide +kernel
def h0Block9_9 : List NodeSpec := nodesWithIdentity [([0,1,2,4,5,194],[1,26,79,1292,1300,1305,1306]),([0,1,2,3,4,5,18,19],[0,1,4,12,16,25,96,108,109,111,112,113,117,119,132,134,266,516,710,885,887,990,993,994,995,996,1366,1367]),([0,1,2,3,4,5,18,20],[0,1,4,12,16,25,96,108,109,110,111,112,113,117,119,266,710,751,753,908,985,1003,1006,1013,1014,1015,1178,1375,1376]),([0,1,2,3,4,5,18,21],[0,1,4,16,79,87,92,96,108,109,110,111,112,113,117,119,266,710,755,756,758,760,761,762,763,771,908,1035,1384]),([0,1,2,3,4,5,18,22],[0,1,16,26,96,108,109,110,111,112,113,118,119,133,134,153,387,697,772,773,776,782,783,785,786,1391,1396]),([0,1,2,3,4,5,65],[0,1,12,16,25,79,87,96,99,103,108,119,133,153,710,1394,1397,1398]),([0,1,2,3,4,5,18,29],[1,4,12,14,25,79,87,96,108,109,112,113,117,119,120,121,123,126,132,134,164,165,266,516,1178,1412,1413]),([0,1,2,3,4,5,18,32],[1,4,12,14,25,79,87,92,96,108,109,110,111,112,113,117,119,134,182,183,185,190,193,194,219,266,1178,1420,1421]),([0,1,2,3,4,5,18,33],[1,12,25,26,96,108,109,110,111,112,113,119,133,153,163,230,231,241,242,261,262,387,908,1178,1422,1423]),([0,1,2,3,4,5,18,34],[1,12,25,26,96,108,109,111,112,113,117,119,133,153,218,278,279,288,289,308,309,387,1035,1178,1431,1432]),([0,1,2,3,4,5,18,39],[1,26,79,87,96,108,109,110,111,112,113,117,119,133,134,153,285,286,293,333,336,337,387,540,908,1178,1433]),([0,1,2,3,4,5,66],[0,1,12,25,26,79,87,92,108,113,119,132,133,153,387,1178,1434,1435,1436,1437])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_9 = true := by decide +kernel
def h0Block9_10 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,61],[0,1,4,12,23,25,49,53,58,79,87,108,119,133,153,194,322,1178]),([0,1,2,3,4,5,19,39],[0,12,16,25,79,87,133,134,153,194,285,293,333,336,337,540,885,887,990,993,994,995,996,1441]),([0,1,2,3,4,5,19,41],[0,12,16,23,25,79,87,92,108,119,132,194,240,244,246,295,553,736,885,990,993,994,995,996,1178,1451]),([0,1,2,3,4,5,19,45],[0,12,16,23,25,108,119,132,133,153,188,189,624,625,632,736,885,887,990,993,994,995,996,1461]),([0,1,2,3,4,5,92],[0,1,12,25,79,87,92,108,117,119,133,153,194,230,236,1054]),([0,1,2,3,4,5,28],[0,1,2,4,8,12,13,14,23,25,79,87,108,119,125,133,153,322,1178,1496]),([0,1,2,3,4,5,20,39],[0,12,16,25,79,87,125,133,153,218,285,286,293,333,336,337,540,751,753,908,1003,1006,1013,1014,1015,1497]),([0,1,2,3,4,5,20,41],[0,12,16,23,25,79,87,92,108,119,125,240,244,245,246,295,553,736,751,985,1003,1006,1013,1014,1015,1178,1502]),([0,1,2,3,4,5,20,45],[0,12,16,23,25,108,119,133,153,188,189,191,218,624,625,632,736,751,753,1003,1006,1013,1014,1015,1178,1508,1519]),([0,1,2,3,4,5,152],[0,1,12,25,79,87,92,108,117,119,133,153,218,753,1013,1520,1521,1522,1523]),([0,1,2,3,4,5,136],[0,4,12,23,25,79,87,108,119,133,153,322,510,567,568,569,710,1178]),([0,1,2,3,4,5,21,33],[0,12,16,25,79,87,133,153,230,231,241,242,261,262,448,755,756,758,760,761,762,763,771,895,908,1525])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_10 = true := by decide +kernel
def h0Block9_11 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,21,34],[0,12,16,25,79,87,133,153,194,218,278,279,288,289,308,309,755,756,758,761,762,763,771,895,1035,1532]),([0,1,2,3,4,5,21,35],[0,12,16,23,25,79,87,92,108,117,119,315,316,335,338,341,448,736,755,756,760,761,762,763,771,895,1178,1533]),([0,1,2,3,4,5,21,36],[0,12,16,23,25,79,87,92,108,119,132,194,367,368,372,373,374,736,755,756,761,762,771,895,1178,1543]),([0,1,2,3,4,5,21,45],[0,16,23,79,87,92,108,119,133,153,188,189,191,624,625,632,736,755,756,758,760,761,762,763,771,895]),([0,1,2,3,4,5,153],[0,1,12,25,79,87,108,117,119,132,133,758,761,895,1553,1554,1555]),([0,1,2,3,4,5,131],[0,4,12,14,23,25,26,79,87,108,119,133,153,461,697,1178,1559,1560]),([0,1,2,3,4,5,22,29],[0,12,16,25,79,87,120,121,123,126,131,132,133,134,153,164,165,697,772,773,782,785,786,1561,1565]),([0,1,2,3,4,5,22,32],[0,12,16,25,79,87,92,133,134,153,182,183,185,187,190,193,194,219,697,772,773,776,782,785,786,1564,1575]),([0,1,2,3,4,5,22,35],[0,12,16,23,25,108,117,119,133,153,218,315,316,319,334,335,338,341,697,736,772,773,776,782,783,785,786,1583,1584]),([0,1,2,3,4,5,22,36],[0,12,16,23,25,108,119,132,133,153,367,368,371,372,373,374,379,387,697,736,772,773,782,783,785,1591,1592]),([0,1,2,3,4,5,22,41],[0,16,23,79,87,92,108,119,133,153,240,243,244,245,246,295,553,555,697,736,772,773,776,782,783,785,786,1600]),([0,1,2,3,5,22,45],[0,26,92,119,132,133,153,624,625,736,785,786,1603])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_11 = true := by decide +kernel
def h0Block9_12 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,132],[0,4,12,14,25,79,87,108,119,133,153,322,479,699,700,701,710]),([0,1,2,3,4,5,24,29],[0,12,16,23,25,79,87,108,117,119,120,121,125,126,132,164,165,516,787,788,799,801,1608]),([0,1,2,3,4,5,24,32],[0,12,16,23,25,79,87,92,108,117,119,134,182,183,190,193,194,219,623,787,788,792,799,800,801,1613]),([0,1,2,3,4,5,24,33],[0,12,16,23,25,108,119,133,153,163,230,231,241,242,261,262,387,787,788,791,792,799,800,801,908,1614]),([0,1,2,3,4,5,24,34],[0,12,16,23,25,108,117,119,133,153,218,278,279,288,289,308,309,387,787,788,791,799,800,801,1035,1621]),([0,1,2,3,4,5,24,39],[0,16,23,79,87,108,117,119,125,133,153,285,286,293,333,336,337,387,540,787,788,791,792,799,800,801,908]),([0,1,2,3,4,5,155],[0,1,12,25,79,87,92,108,119,132,133,153,387,791,801,913,914,917]),([0,1,2,3,4,5,67],[0,1,4,12,23,25,87,108,119,121,123,133,153,168,710,1567,1568,1570,1573]),([0,1,2,3,4,5,68],[0,1,12,16,25,87,108,119,120,125,133,153,322,650,985,1178,1625,1626,1627]),([0,1,2,3,4,5,29,45],[12,23,25,79,87,108,119,120,121,123,125,126,132,133,153,164,165,188,624,625,632,1632]),([0,1,2,3,4,5,73],[0,1,12,25,87,108,117,119,123,126,133,153,155,159,160]),([0,1,2,3,4,5,79],[0,1,4,12,23,25,87,108,119,133,153,183,185,194,1577,1578,1579,1580,1581])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_12 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_12 = true := by decide +kernel
def h0Block9_13 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,80],[0,1,12,16,25,87,108,119,133,153,182,194,322,650,1178,1663,1664,1665,1666]),([0,1,2,3,4,5,32,45],[12,23,25,79,87,92,108,119,133,153,182,183,185,188,190,191,193,194,219,624,625,632,1679]),([0,1,2,3,4,5,85],[0,1,12,25,87,108,117,119,133,153,185,190,211,213,215,216,218]),([0,1,2,3,4,5,88],[0,1,4,12,14,23,25,26,79,87,108,119,153,231,710,895,1690,1691,1692,1693,1694]),([0,1,2,3,4,5,89],[0,1,12,16,25,79,87,108,119,153,162,230,236,322,1049,1052,1054,1055,1178]),([0,1,2,3,4,5,33,41],[12,23,25,79,87,108,119,133,153,230,231,240,241,242,244,245,246,261,262,295,448,553,555,1706]),([0,1,2,3,4,5,101],[0,1,4,12,23,25,26,79,87,108,119,153,218,279,895,1717,1718,1719,1720]),([0,1,2,3,4,5,102],[0,1,12,16,25,79,87,108,119,153,218,278,1066,1072,1073,1178,1727]),([0,1,2,3,5,34,39],[25,26,87,117,153,282,285,288,289,290]),([0,1,2,3,4,5,34,41],[12,23,25,79,87,108,119,133,153,194,218,240,244,246,278,279,288,289,295,308,309,553,555,1735]),([0,1,2,3,4,5,110],[0,1,4,12,14,25,79,87,119,133,153,316,319,710,895,1081,1242,1245,1246,1586]),([0,1,2,3,4,5,111],[0,1,12,16,25,42,79,87,108,119,133,153,315,322,650,736,1337,1535,1589,1751,1752])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_13 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_13 = true := by decide +kernel
def h0Block9_14 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,35,39],[12,23,25,79,87,108,119,133,153,218,285,286,293,315,316,319,333,335,337,338,341,540,1762]),([0,1,2,3,4,5,114],[0,1,12,25,79,87,92,119,133,153,218,319,335,346,348,350,352]),([0,1,2,3,4,5,118],[0,1,4,12,25,79,87,119,133,153,168,368,371,710,895,908,1593,1595,1598,1599]),([0,1,2,3,4,5,119],[0,1,12,16,25,79,87,119,125,133,153,322,367,650,736,985,1768,1769,1770]),([0,1,2,3,4,5,36,39],[12,23,25,79,87,108,119,125,133,153,194,285,293,333,337,367,368,371,372,373,374,540,908,1775]),([0,1,2,3,4,5,120],[0,1,12,25,79,87,92,119,133,153,371,374,380,385,386,387]),([0,1,2,3,4,5,103],[0,4,12,23,25,26,79,87,108,119,153,293,540,1445,1446,1447,1448]),([0,1,2,3,4,5,104],[0,1,12,16,25,79,87,108,119,125,153,293,333,940,941,942,1178,1782]),([0,1,2,3,4,5,93],[0,4,12,25,79,87,119,133,153,246,553,555,1456,1457,1458,1459]),([0,1,2,3,4,5,94],[0,1,12,16,25,79,87,108,119,133,153,240,246,322,650,736,1713,1715,1716]),([0,1,2,3,4,5,95],[0,1,12,25,79,87,119,125,132,133,153,244,387,555,559,564,566]),([0,1,2,3,4,5,81],[0,4,12,14,25,26,79,87,108,119,153,625,710,895,1466,1467,1469,1470])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_14 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_14 = true := by decide +kernel
def h0Block9_15 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,82],[0,1,12,16,25,79,87,108,119,125,153,162,322,624,627,736,1687,1688,1689])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_15 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_15 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1 ++ h0Block9_2 ++ h0Block9_3 ++ h0Block9_4 ++ h0Block9_5 ++ h0Block9_6 ++ h0Block9_7 ++ h0Block9_8 ++ h0Block9_9 ++ h0Block9_10 ++ h0Block9_11 ++ h0Block9_12 ++ h0Block9_13 ++ h0Block9_14 ++ h0Block9_15
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := by
  unfold h0Nodes9 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0Test9_0,h0Test9_1⟩,h0Test9_2⟩,h0Test9_3⟩,h0Test9_4⟩,h0Test9_5⟩,h0Test9_6⟩,h0Test9_7⟩,h0Test9_8⟩,h0Test9_9⟩,h0Test9_10⟩,h0Test9_11⟩,h0Test9_12⟩,h0Test9_13⟩,h0Test9_14⟩,h0Test9_15⟩
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,6],[0,1,12,25,26,29,43,46,79,87,108,119,153]),([0,1,2,3,4,5,7],[0,1,12,25,26,79,87,108,119,153,704,705,706]),([0,1,2,3,4,5,8],[0,1,2,12,25,26,28,31,44,79,87,108,119,153]),([0,1,2,3,4,5,9],[0,1,12,25,26,79,87,108,119,153,830,831,832,833]),([0,1,2,3,4,5,10],[0,1,12,25,26,49,60,61,68,79,87,108,119,153]),([0,1,2,3,4,5,11],[0,1,12,26,79,87,108,119,153,963,964,965,966]),([0,1,2,3,4,5,12],[0,1,12,25,26,70,79,87,88,94,108,119,153]),([0,1,2,3,4,5,13],[0,1,12,25,26,87,108,119,153,1112,1113,1114]),([0,1,2,3,4,5,14],[0,1,12,25,79,87,108,119,153,1170,1171,1172]),([0,1,2,3,4,5,15],[0,1,12,25,26,79,87,108,119,133,153,1261,1262,1263]),([0,1,2,3,4,5,17],[0,1,12,25,26,79,87,119,153,1291,1292,1293]),([0,1,2,3,4,5,18],[0,1,12,25,26,79,87,96,108,112,113,119,153])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Block10_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,19],[0,1,12,79,87,108,119,153,990,994,995]),([0,1,2,3,4,5,20],[0,1,12,25,79,87,108,119,153,1003,1013,1014]),([0,1,2,3,4,5,21],[0,1,12,25,79,87,108,119,153,761,762]),([0,1,2,3,4,5,22],[0,1,12,25,26,79,87,108,119,133,153,697,782,785]),([0,1,2,3,4,5,24],[0,1,12,25,79,87,108,119,153,799,801]),([0,1,2,3,4,5,29],[0,1,12,87,108,119,120,126,153,164]),([0,1,2,3,4,5,32],[0,1,12,25,79,87,108,119,153,182,190,219]),([0,1,2,3,4,5,33],[0,1,12,25,26,79,87,108,119,153,230,241,261]),([0,1,2,3,4,5,34],[0,1,12,26,79,87,108,119,153,278,289,308]),([0,1,2,3,4,5,35],[0,1,12,25,79,87,108,119,153,315,335,341]),([0,1,2,3,4,5,36],[0,1,12,79,87,119,153,367,373,374]),([0,1,2,3,4,5,39],[0,1,12,25,26,79,87,108,119,153,333,337])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_1 = true := by decide +kernel
def h0Block10_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,41],[0,1,12,25,79,87,108,119,153,240,244]),([0,1,2,3,4,5,45],[0,1,12,25,26,79,87,108,119,153,188,624])]
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
def h0Block11_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[0,87,119,153])]
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
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,5,21),(VAR 5,3,35)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 10]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4008241832 * 2 ^ 32 + 3940591744) ||| ((4008241832 * 2 ^ 32 + 3940591744) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4008241832 * 2 ^ 32 + 3940591744) ||| ((4008241832 * 2 ^ 32 + 3940591744) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_47525
theorem PEqualNP.Outside.L_meta_47525 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241832 * 2 ^ 32 + 3940591744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241832 * 2 ^ 32 + 3940591744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_47525.table2_of_lower (4008241832 * 2 ^ 32 + 3940591744) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_47525.low_root
    PEqualNP.Outside.L_meta_47525.wit PEqualNP.Outside.L_meta_47525.wo (by decide)
    PEqualNP.Outside.L_meta_47525.wit_mono PEqualNP.Outside.L_meta_47525.wit_eval s hcs
