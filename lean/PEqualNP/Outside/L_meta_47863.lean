import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_47863
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
def h1R : List Nat := varsOf 15
def h1G : Nat := 0xeea0eea0eea0eea0eea0eea0eea0eea0
def h1Pos : List Nat := [5,7,9,5,7,9,10,14]
def h1Neg : List Nat := [4,6,8,1,3,1,2,6]
def h1Mask : Nat := fullMask 8
def h1Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,63,56),(0xcccccccccccccccccccccccccccccccc,210,210),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,155,131),(0xff00ff00ff00ff00ff00ff00ff00ff00,228,4)]
def h1Steps : List (Nat × Nat × Nat) := []
def h1W : BT Decor := buildWiresBT 2 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[],[(1,2),(0,3)]]
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
lemma h1Bound : Lower h1R h1G 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) h1Bucket3Ok (by decide +kernel)
def h2R : List Nat := varsOf 27
def h2G : Nat := 0xeeaacc88eeaacc88eeaacc88eeaacc88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 4 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h3R : List Nat := varsOf 30
def h3G : Nat := 0xfff0c0c0fff0c0c0fff0c0c0fff0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 4 := carry_of (swaps := [(3,4),(1,2),(2,3),(0,1),(1,2),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h5R : List Nat := varsOf 23
def h5G : Nat := 0xeeeec0c0eeeec0c0eeeec0c0eeeec0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 4 := carry_of (swaps := [(3,4),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h6R : List Nat := varsOf 29
def h6G : Nat := 0xffa0f0a0ffa0f0a0ffa0f0a0ffa0f0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 4 := carry_of (swaps := [(1,2),(2,3),(3,4),(2,3),(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h4R : List Nat := varsOf 31
def h4G : Nat := 0xeea0c080eea0c080eea0c080eea0c080
def h4Pos : List Nat := [14,21,14,14,7,25,14,26,21,7,21,7,27,27,25,14,26]
def h4Neg : List Nat := [12,20,13,10,3,17,6,10,5,6,17,5,19,11,24,11,24]
def h4Mask : Nat := fullMask 17
def h4Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7f32,0xbd34),(0xcccccccccccccccccccccccccccccccc,0x1badd,0xb2d8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x8f5f,2887),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f0ed,0x1e08d),(0xffff0000ffff0000ffff0000ffff0000,0x175a2,0x15422)]
def h4Steps : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(2,3,6)]
def h4W : BT Decor := buildWiresBT 3 h4Base h4Steps
def h4AutoList : List (List (Nat × Nat)) := [[],[(2,4),(1,3)],[(3,4),(0,1)],[(1,4),(0,2)],[(1,2),(0,3)],[(2,3),(0,4)],[(3,4),(2,3),(1,4),(0,1)],[(3,4),(2,3),(1,3),(0,2)],[(3,4),(2,4),(1,3),(0,3)],[(3,4),(2,4),(1,2),(0,4)]]
def h4Autos : BT (List (Nat × Nat)) := btOfList 4 h4AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Pairs : goodPairs h4G h4Pos h4Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4BaseOk : ∀ x ∈ h4Base, faithful h4Pos h4Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4WOk : btAll (fun x => faithful h4Pos h4Neg x ∧ x.1 < 2^128) h4W := buildWiresBT_faithful h4BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h4G = h4G) h4Autos := btAll_ofList (autos_of (by decide +kernel))
def h4SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4),some (subcubeFast 0 16,4)]
def h4Slices : BT (Option (Nat × Nat)) := btOfList 3 h4SliceList
def h4Specs : List PoolSpec := [(0,[]),(1,[]),(3,[]),(2,[]),(4,[])]
def h4Pools : BT (Option BoundPool) := buildPoolsBT 3 h4W h4R h4Slices h4Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice4 : Slice h4R h4G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice3 : Slice h4R h4G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice2 : Slice h4R h4G (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice1 : Slice h4R h4G (subcubeFast 0 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice0 : Slice h4R h4G (subcubeFast 0 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h4R h4G p.1 p.2) h4Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h4R h4G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h4Slice0) (forall_cons (fun _ h => by cases h; exact h4Slice1) (forall_cons (fun _ h => by cases h; exact h4Slice2) (forall_cons (fun _ h => by cases h; exact h4Slice3) (forall_cons (fun _ h => by cases h; exact h4Slice4) (fun _ h => (List.not_mem_nil h).elim))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h4R h4G c) h4Pools := buildPoolsBT_sound h4SlicesOk
def h4Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h4G (4 - 1) xs.toFinset) h4Empty := trivial
def h4Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,4,7],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Test4_0 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Empty 4 h4Block4_0 = true := by decide +kernel
def h4Nodes4 : List NodeSpec := h4Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Check4 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Empty 4 h4Nodes4 = true := h4Test4_0
def h4Bucket4 : BT (List (List Nat)) := buildBucketsBT h4W h4Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h4G 4 xs.toFinset) h4Bucket4 := buildBucketsBT_sound (by decide) h4Pairs h4WOk h4PoolsOk h4AutosOk h4EmptyOk h4Check4
def h4Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[]),([0,1,2,3,4,6],[2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Test5_0 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Bucket4 5 h4Block5_0 = true := by decide +kernel
def h4Nodes5 : List NodeSpec := h4Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Check5 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Bucket4 5 h4Nodes5 = true := h4Test5_0
def h4Bucket5 : BT (List (List Nat)) := buildBucketsBT h4W h4Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h4G 5 xs.toFinset) h4Bucket5 := buildBucketsBT_sound (by decide) h4Pairs h4WOk h4PoolsOk h4AutosOk h4Bucket4Ok h4Check5
def h4Block6_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Test6_0 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Bucket5 6 h4Block6_0 = true := by decide +kernel
def h4Nodes6 : List NodeSpec := h4Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Check6 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Bucket5 6 h4Nodes6 = true := h4Test6_0
def h4Bucket6 : BT (List (List Nat)) := buildBucketsBT h4W h4Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h4G 6 xs.toFinset) h4Bucket6 := buildBucketsBT_sound (by decide) h4Pairs h4WOk h4PoolsOk h4AutosOk h4Bucket5Ok h4Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 7 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,6,14),(VAR 4,5,21)]) (by decide +kernel) h4Bucket6Ok (by decide +kernel)
def h7R : List Nat := varsOf 38
def h7G : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def h7Pos : List Nat := [34,36,6,6,36,34]
def h7Neg : List Nat := [32,32,2,4,4,2]
def h7Mask : Nat := fullMask 6
def h7Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h7Steps : List (Nat × Nat × Nat) := []
def h7W : BT Decor := buildWiresBT 2 h7Base h7Steps
def h7AutoList : List (List (Nat × Nat)) := [[],[(2,5)],[(1,2)],[(1,5)],[(2,5),(1,2)],[(2,5),(1,5)]]
def h7Autos : BT (List (Nat × Nat)) := btOfList 3 h7AutoList
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
def h7Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2],[])]
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
lemma h7Bound : Lower h7R h7G 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 5,2,34)]) (by decide +kernel) h7Bucket3Ok (by decide +kernel)
def h8R : List Nat := varsOf 39
def h8G : Nat := 0xa8a8a8a880808080a8a8a8a880808080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) h7Bound
def h10R : List Nat := varsOf 7
def h10G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 4 := carry_of (swaps := [(4,5),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h9R : List Nat := varsOf 15
def h9G : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,6,14)]) (by decide +kernel) h10Bound
def h11R : List Nat := varsOf 43
def h11G : Nat := 0xeeaaeeaacc88cc88eeaaeeaacc88cc88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h12R : List Nat := varsOf 45
def h12G : Nat := 0xfaaafaaaf0a0f0a0faaafaaaf0a0f0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h14R : List Nat := varsOf 39
def h14G : Nat := 0xe8e8e8e8c0c0c0c0e8e8e8e8c0c0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,34,35)]) (by decide +kernel) h7Bound
def h13R : List Nat := varsOf 47
def h13G : Nat := 0xe8a8e8a8c080c080e8a8e8a8c080c080
def h13Pos : List Nat := [14,37,7,7,14,35,7,14,43,35,35,37,43,37,45,43,46]
def h13Neg : List Nat := [12,36,5,6,10,34,3,6,42,3,33,33,41,5,41,11,38]
def h13Mask : Nat := fullMask 17
def h13Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff6e,0xfe44),(0xcccccccccccccccccccccccccccccccc,0x197fd,0x183f8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x168df,0x1208f),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1d191,0xd111),(0xffffffff00000000ffffffff00000000,0x1ff22,0x15d22)]
def h13Steps : List (Nat × Nat × Nat) := [(0,1,2),(2,4,5)]
def h13W : BT Decor := buildWiresBT 3 h13Base h13Steps
def h13AutoList : List (List (Nat × Nat)) := [[],[(1,2)]]
def h13Autos : BT (List (Nat × Nat)) := btOfList 1 h13AutoList
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
def h13SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,5),some (subcubeFast 0 32,5),some (subcubeFast 8 0,5),some (subcubeFast 8 1,4)]
def h13Slices : BT (Option (Nat × Nat)) := btOfList 3 h13SliceList
def h13Specs : List PoolSpec := [(6,[]),(0,[]),(1,[]),(2,[]),(5,[]),(3,[]),(4,[])]
def h13Pools : BT (Option BoundPool) := buildPoolsBT 3 h13W h13R h13Slices h13Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice6 : Slice h13R h13G (subcubeFast 8 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice5 : Slice h13R h13G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice4 : Slice h13R h13G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice3 : Slice h13R h13G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice2 : Slice h13R h13G (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice1 : Slice h13R h13G (subcubeFast 0 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Slice0 : Slice h13R h13G (subcubeFast 0 1) 4 := slice_fast_direct (zDead := 8) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h13R h13G p.1 p.2) h13Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h13R h13G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h13Slice0) (forall_cons (fun _ h => by cases h; exact h13Slice1) (forall_cons (fun _ h => by cases h; exact h13Slice2) (forall_cons (fun _ h => by cases h; exact h13Slice3) (forall_cons (fun _ h => by cases h; exact h13Slice4) (forall_cons (fun _ h => by cases h; exact h13Slice5) (forall_cons (fun _ h => by cases h; exact h13Slice6) (fun _ h => (List.not_mem_nil h).elim))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h13R h13G c) h13Pools := buildPoolsBT_sound h13SlicesOk
def h13Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h13G (4 - 1) xs.toFinset) h13Empty := trivial
def h13Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,6],[])]
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
def h13Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[2,4,5,6])]
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
def h13Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,1,2,3,4,5,6])]
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
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 7 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,6,14),(VAR 5,3,35)]) (by decide +kernel) h13Bucket6Ok (by decide +kernel)
def h15R : List Nat := varsOf 23
def h15G : Nat := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 5 := carry_of (swaps := [(3,4)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h16R : List Nat := varsOf 37
def h16G : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 4 := carry_of (swaps := [(0,1)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h17R : List Nat := varsOf 39
def h17G : Nat := 0xe8e8e8e8a0a0a0a0e8e8e8e8a0a0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 5 := carry_of (swaps := [(0,1)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h18R : List Nat := varsOf 51
def h18G : Nat := 0xeeeeaaaaaaaa8888eeeeaaaaaaaa8888
def h18Pos : List Nat := [17,50,17,33,3,17,50,33,50,3,3,19,19]
def h18Neg : List Nat := [16,48,18,32,2,1,34,1,18,1,0,18,1]
def h18Mask : Nat := fullMask 13
def h18Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7869,4768),(0xcccccccccccccccccccccccccccccccc,8018,2388),(0xffff0000ffff0000ffff0000ffff0000,6503,2311),(0xffffffff00000000ffffffff00000000,458,74)]
def h18Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,1,2),(1,1,2),(2,1,2),(1,2,4),(2,2,4),(0,2,5),(3,2,5),(1,3,10),(2,3,10)]
def h18W : BT Decor := buildWiresBT 5 h18Base h18Steps
def h18AutoList : List (List (Nat × Nat)) := [[],[(4,5)],[(1,4)],[(1,5)],[(4,5),(1,4)],[(4,5),(1,5)]]
def h18Autos : BT (List (Nat × Nat)) := btOfList 3 h18AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Pairs : goodPairs h18G h18Pos h18Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18BaseOk : ∀ x ∈ h18Base, faithful h18Pos h18Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18WOk : btAll (fun x => faithful h18Pos h18Neg x ∧ x.1 < 2^128) h18W := buildWiresBT_faithful h18BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h18G = h18G) h18Autos := btAll_ofList (autos_of (by decide +kernel))
def h18SliceList : List (Option (Nat × Nat)) := []
def h18Slices : BT (Option (Nat × Nat)) := btOfList 1 h18SliceList
def h18Specs : List PoolSpec := []
def h18Pools : BT (Option BoundPool) := buildPoolsBT 1 h18W h18R h18Slices h18Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h18R h18G p.1 p.2) h18Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h18R h18G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h18R h18G c) h18Pools := buildPoolsBT_sound h18SlicesOk
def h18Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G (3 - 1) xs.toFinset) h18Empty := trivial
def h18Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,3,11],[]),([0,1,3,12],[]),([0,1,3,13],[]),([0,1,3,14],[]),([0,3,8,9],[]),([0,1,2,15],[]),([0,1,2,16],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Test3_0 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Empty 3 h18Block3_0 = true := by decide +kernel
def h18Nodes3 : List NodeSpec := h18Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Check3 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Empty 3 h18Nodes3 = true := h18Test3_0
def h18Bucket3 : BT (List (List Nat)) := buildBucketsBT h18W h18Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G 3 xs.toFinset) h18Bucket3 := buildBucketsBT_sound (by decide) h18Pairs h18WOk h18PoolsOk h18AutosOk h18EmptyOk h18Check3
def h18Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0,1]),([0,1,2,3,5],[],[0,1]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Test4_0 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Bucket3 4 h18Block4_0 = true := by decide +kernel
def h18Nodes4 : List NodeSpec := h18Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Check4 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Bucket3 4 h18Nodes4 = true := h18Test4_0
def h18Bucket4 : BT (List (List Nat)) := buildBucketsBT h18W h18Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G 4 xs.toFinset) h18Bucket4 := buildBucketsBT_sound (by decide) h18Pairs h18WOk h18PoolsOk h18AutosOk h18Bucket3Ok h18Check4
def h18Block5_0 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Test5_0 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Bucket4 5 h18Block5_0 = true := by decide +kernel
def h18Nodes5 : List NodeSpec := h18Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Check5 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Bucket4 5 h18Nodes5 = true := h18Test5_0
def h18Bucket5 : BT (List (List Nat)) := buildBucketsBT h18W h18Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G 5 xs.toFinset) h18Bucket5 := buildBucketsBT_sound (by decide) h18Pairs h18WOk h18PoolsOk h18AutosOk h18Bucket4Ok h18Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h18Bucket5Ok (by decide +kernel)
def h19R : List Nat := varsOf 53
def h19G : Nat := 0xfafaaaaaa0a0a0a0fafaaaaaa0a0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(2,3),(3,4),(1,2)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h20R : List Nat := varsOf 54
def h20G : Nat := 0xfcfcfcfcf0f0c0c0fcfcfcfcf0f0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,4,20)]) (by decide +kernel) h7Bound
def h21R : List Nat := varsOf 55
def h21G : Nat := 0xe8e8a8a8a0a08080e8e8a8a8a0a08080
def h21Pos : List Nat := [21,54,21,54,7,37,54,21,54,35,7,21,37,37,7,37,35,35,23,39]
def h21Neg : List Nat := [20,52,22,50,3,36,38,5,22,3,6,17,5,38,5,33,34,33,19,38]
def h21Mask : Nat := fullMask 20
def h21Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffeb5,0x6da90),(0xcccccccccccccccccccccccccccccccc,0xf475a,0xd275c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcfdff,0x875e7),(0xffff0000ffff0000ffff0000ffff0000,0x409cf,0x4090f),(0xffffffff00000000ffffffff00000000,0xbb36a,0xba06a)]
def h21Steps : List (Nat × Nat × Nat) := [(0,0,1),(0,1,4),(0,0,6),(2,0,6),(0,2,5),(2,2,5),(0,2,6),(2,2,6),(2,4,5),(2,4,9),(2,2,7)]
def h21W : BT Decor := buildWiresBT 4 h21Base h21Steps
def h21AutoList : List (List (Nat × Nat)) := [[],[(1,5)]]
def h21Autos : BT (List (Nat × Nat)) := btOfList 1 h21AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Pairs : goodPairs h21G h21Pos h21Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21BaseOk : ∀ x ∈ h21Base, faithful h21Pos h21Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21WOk : btAll (fun x => faithful h21Pos h21Neg x ∧ x.1 < 2^128) h21W := buildWiresBT_faithful h21BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h21G = h21G) h21Autos := btAll_ofList (autos_of (by decide +kernel))
def h21SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,6),some (subcubeFast 0 16,5),some (subcubeFast 0 18,4),some (subcubeFast 0 32,5),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4)]
def h21Slices : BT (Option (Nat × Nat)) := btOfList 3 h21SliceList
def h21Specs : List PoolSpec := [(0,[]),(1,[]),(2,[(0,0,1)]),(6,[(0,0,1)]),(3,[(0,1,4)]),(5,[]),(3,[]),(6,[]),(2,[]),(4,[]),(7,[]),(2,[(0,1,4)])]
def h21Pools : BT (Option BoundPool) := buildPoolsBT 4 h21W h21R h21Slices h21Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice7 : Slice h21R h21G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice6 : Slice h21R h21G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice5 : Slice h21R h21G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice4 : Slice h21R h21G (subcubeFast 0 18) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice3 : Slice h21R h21G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice2 : Slice h21R h21G (subcubeFast 0 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice1 : Slice h21R h21G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice0 : Slice h21R h21G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h21R h21G p.1 p.2) h21Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h21R h21G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h21Slice0) (forall_cons (fun _ h => by cases h; exact h21Slice1) (forall_cons (fun _ h => by cases h; exact h21Slice2) (forall_cons (fun _ h => by cases h; exact h21Slice3) (forall_cons (fun _ h => by cases h; exact h21Slice4) (forall_cons (fun _ h => by cases h; exact h21Slice5) (forall_cons (fun _ h => by cases h; exact h21Slice6) (forall_cons (fun _ h => by cases h; exact h21Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h21R h21G c) h21Pools := buildPoolsBT_sound h21SlicesOk
def h21Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h21G (4 - 1) xs.toFinset) h21Empty := trivial
def h21Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,14],[]),([0,1,3,4,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Test4_0 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Empty 4 h21Block4_0 = true := by decide +kernel
def h21Nodes4 : List NodeSpec := h21Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Check4 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Empty 4 h21Nodes4 = true := h21Test4_0
def h21Bucket4 : BT (List (List Nat)) := buildBucketsBT h21W h21Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h21G 4 xs.toFinset) h21Bucket4 := buildBucketsBT_sound (by decide) h21Pairs h21WOk h21PoolsOk h21AutosOk h21EmptyOk h21Check4
def h21Block5_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,6],[0,4,5]),([0,1,2,3,4,9],[5,6,7]),([0,1,2,3,4,10],[6,7]),([0,1,2,3,4,7],[6,7,8]),([0,1,2,3,4,13],[]),([0,1,2,3,4,8],[]),([0,1,2,3,4,11],[]),([0,1,2,3,4,12],[11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Test5_0 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Bucket4 5 h21Block5_0 = true := by decide +kernel
def h21Nodes5 : List NodeSpec := h21Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Check5 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Bucket4 5 h21Nodes5 = true := h21Test5_0
def h21Bucket5 : BT (List (List Nat)) := buildBucketsBT h21W h21Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h21G 5 xs.toFinset) h21Bucket5 := buildBucketsBT_sound (by decide) h21Pairs h21WOk h21PoolsOk h21AutosOk h21Bucket4Ok h21Check5
def h21Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,5,6,7,8,9,10],[0]),([0,1,2,3,4,6],[0,1,4,5,6,7,8,11],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Test6_0 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Bucket5 6 h21Block6_0 = true := by decide +kernel
def h21Nodes6 : List NodeSpec := h21Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Check6 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Bucket5 6 h21Nodes6 = true := h21Test6_0
def h21Bucket6 : BT (List (List Nat)) := buildBucketsBT h21W h21Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h21G 6 xs.toFinset) h21Bucket6 := buildBucketsBT_sound (by decide) h21Pairs h21WOk h21PoolsOk h21AutosOk h21Bucket5Ok h21Check6
def h21Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,5,6,7,8],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Test7_0 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Bucket6 7 h21Block7_0 = true := by decide +kernel
def h21Nodes7 : List NodeSpec := h21Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Check7 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Bucket6 7 h21Nodes7 = true := h21Test7_0
def h21Bucket7 : BT (List (List Nat)) := buildBucketsBT h21W h21Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h21G 7 xs.toFinset) h21Bucket7 := buildBucketsBT_sound (by decide) h21Pairs h21WOk h21PoolsOk h21AutosOk h21Bucket6Ok h21Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 8 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 4,5,21),(VAR 5,3,35)]) (by decide +kernel) h21Bucket7Ok (by decide +kernel)
def h22R : List Nat := varsOf 11
def h22G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 4 := carry_of (swaps := [(4,5),(3,4),(0,1),(1,2)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h23R : List Nat := varsOf 19
def h23G : Nat := 0xeeee8888eeee8888eeee8888eeee8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 4 := carry_of (swaps := [(4,5),(0,1),(1,2)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h24R : List Nat := varsOf 27
def h24G : Nat := 0xee888888ee888888ee888888ee888888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 5 := carry_of (swaps := [(4,5),(0,1),(1,2),(2,3)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h25R : List Nat := varsOf 43
def h25G : Nat := 0xee88ee88ee00ee00ee88ee88ee00ee00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 5 := carry_of (swaps := [(3,4),(4,5),(0,1),(1,2),(2,3)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h26R : List Nat := varsOf 51
def h26G : Nat := 0xeeee8888eeee0000eeee8888eeee0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 5 := carry_of (swaps := [(3,4),(4,5),(0,1),(1,2),(2,3),(3,4)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h27R : List Nat := varsOf 59
def h27G : Nat := 0xee888888ee000000ee888888ee000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 6 := lift_of (z := 0) (o := 40) (essPairs := [(VAR 3,17,25),(VAR 5,3,35)]) (by decide +kernel) h23Bound
def h28R : List Nat := varsOf 13
def h28G : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 4 := carry_of (swaps := [(4,5),(3,4),(0,1)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h29R : List Nat := varsOf 21
def h29G : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 4 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h30R : List Nat := varsOf 29
def h30G : Nat := 0xfaa0a0a0faa0a0a0faa0a0a0faa0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 5 := carry_of (swaps := [(4,5),(0,1),(1,2),(2,3),(1,2)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h31R : List Nat := varsOf 45
def h31G : Nat := 0xfaa0faa0aaa0aaa0faa0faa0aaa0aaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 5 := carry_of (swaps := [(3,4),(4,5),(2,3),(1,2)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h32R : List Nat := varsOf 49
def h32G : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 4 := carry_of (swaps := [(2,3),(3,4),(0,1)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h33R : List Nat := varsOf 53
def h33G : Nat := 0xfafaa0a0aaaa0000fafaa0a0aaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 5 := carry_of (swaps := [(2,3),(3,4),(0,1),(1,2)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h34R : List Nat := varsOf 57
def h34G : Nat := 0xffaaaaaaaaaa0000ffaaaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(1,2),(2,3)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h35R : List Nat := varsOf 60
def h35G : Nat := 0xfff0f0f0fff00000fff0f0f0fff00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h36R : List Nat := varsOf 61
def h36G : Nat := 0xfaa0a0a0aaa00000faa0a0a0aaa00000
def h36Pos : List Nat := [25,60,21,21,60,25,37,60,21,60,37,25,37]
def h36Neg : List Nat := [24,56,17,20,52,17,36,44,5,28,5,9,33]
def h36Mask : Nat := fullMask 13
def h36Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7533,7460),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6110,2008),(0xff00ff00ff00ff00ff00ff00ff00ff00,2739,2691),(0xffff0000ffff0000ffff0000ffff0000,3007,575),(0xffffffff00000000ffffffff00000000,5842,4306)]
def h36Steps : List (Nat × Nat × Nat) := []
def h36W : BT Decor := buildWiresBT 3 h36Base h36Steps
def h36AutoList : List (List (Nat × Nat)) := [[],[(3,5),(2,4)]]
def h36Autos : BT (List (Nat × Nat)) := btOfList 1 h36AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Pairs : goodPairs h36G h36Pos h36Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36BaseOk : ∀ x ∈ h36Base, faithful h36Pos h36Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36WOk : btAll (fun x => faithful h36Pos h36Neg x ∧ x.1 < 2^128) h36W := buildWiresBT_faithful h36BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h36G = h36G) h36Autos := btAll_ofList (autos_of (by decide +kernel))
def h36SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5)]
def h36Slices : BT (Option (Nat × Nat)) := btOfList 2 h36SliceList
def h36Specs : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def h36Pools : BT (Option BoundPool) := buildPoolsBT 2 h36W h36R h36Slices h36Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Slice3 : Slice h36R h36G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Slice2 : Slice h36R h36G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Slice1 : Slice h36R h36G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Slice0 : Slice h36R h36G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h36R h36G p.1 p.2) h36Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h36R h36G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h36Slice0) (forall_cons (fun _ h => by cases h; exact h36Slice1) (forall_cons (fun _ h => by cases h; exact h36Slice2) (forall_cons (fun _ h => by cases h; exact h36Slice3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h36R h36G c) h36Pools := buildPoolsBT_sound h36SlicesOk
def h36Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h36G (6 - 1) xs.toFinset) h36Empty := trivial
def h36Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Test6_0 : checkNodesBT h36W h36G h36Mask h36Pools h36Autos h36Empty 6 h36Block6_0 = true := by decide +kernel
def h36Nodes6 : List NodeSpec := h36Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Check6 : checkNodesBT h36W h36G h36Mask h36Pools h36Autos h36Empty 6 h36Nodes6 = true := h36Test6_0
def h36Bucket6 : BT (List (List Nat)) := buildBucketsBT h36W h36Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h36G 6 xs.toFinset) h36Bucket6 := buildBucketsBT_sound (by decide) h36Pairs h36WOk h36PoolsOk h36AutosOk h36EmptyOk h36Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 7 := lower_of_forestBT (essPairs := [(VAR 0,20,21),(VAR 2,17,21),(VAR 3,17,25),(VAR 4,5,21),(VAR 5,5,37)]) (by decide +kernel) h36Bucket6Ok (by decide +kernel)
def h37R : List Nat := varsOf 14
def h37G : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 4 := carry_of (swaps := [(4,5),(3,4)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h38R : List Nat := varsOf 22
def h38G : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 4 := carry_of (swaps := [(4,5)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h39R : List Nat := varsOf 26
def h39G : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 4 := carry_of (swaps := [(4,5),(2,3)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h40R : List Nat := varsOf 28
def h40G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 4 := carry_of (swaps := [(4,5),(2,3),(1,2)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
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
def h41R : List Nat := varsOf 30
def h41G : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 7 := carry_of (swaps := [(3,4),(4,5)]) (roots2 := Cofactor12058.R_10) (T2 := Cofactor12058.G_10) (by decide +kernel) Cofactor12058.low_10
def h42R : List Nat := varsOf 42
def h42G : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bound : Lower h42R h42G 4 := carry_of (swaps := [(2,3)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h43R : List Nat := varsOf 46
def h43G : Nat := 0xfcc0fcc0cc00cc00fcc0fcc0cc00cc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bound : Lower h43R h43G 5 := carry_of (swaps := [(2,3),(0,1),(1,2),(0,1)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h44R : List Nat := varsOf 54
def h44G : Nat := 0xfcfcc0c0ccccc0c0fcfcc0c0ccccc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bound : Lower h44R h44G 5 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(0,1)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h45R : List Nat := varsOf 58
def h45G : Nat := 0xffcccc00cc00cc00ffcccc00cc00cc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bound : Lower h45R h45G 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(1,2),(2,3),(0,1)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h46R : List Nat := varsOf 60
def h46G : Nat := 0xfff0f000ff00f000fff0f000ff00f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 5 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h47R : List Nat := varsOf 62
def h47G : Nat := 0xfcc0c000cc00c000fcc0c000cc00c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h47Bound : Lower h47R h47G 8 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,22,54)]) (by decide +kernel) h41Bound
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
def h48R : List Nat := varsOf 15
def h48G : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bound : Lower h48R h48G 7 := carry_of (swaps := [(3,4),(4,5),(0,1),(1,2),(2,3),(3,4)]) (roots2 := Cofactor12058.R_13) (T2 := Cofactor12058.G_13) (by decide +kernel) Cofactor12058.low_13
def h49R : List Nat := varsOf 23
def h49G : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bound : Lower h49R h49G 7 := carry_of (swaps := [(3,4)]) (roots2 := h48R) (T2 := h48G) (by decide +kernel) h48Bound
def h50R : List Nat := varsOf 27
def h50G : Nat := 0xffeeeeaaffeeeeaaffeeeeaaffeeeeaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bound : Lower h50R h50G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h39Bound
def h51R : List Nat := varsOf 29
def h51G : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bound : Lower h51R h51G 5 := carry_of (swaps := [(1,2)]) (roots2 := h50R) (T2 := h50G) (by decide +kernel) h50Bound
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
def h52R : List Nat := varsOf 31
def h52G : Nat := 0xfee8e8a8fee8e8a8fee8e8a8fee8e8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h52Bound : Lower h52R h52G 10 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(1,2),(0,1)]) (roots2 := Cofactor12116.R_60) (T2 := Cofactor12116.G_60) (by decide +kernel) Cofactor12116.low_60
def h53R : List Nat := varsOf 43
def h53G : Nat := 0xffeeffeeeeaaeeaaffeeffeeeeaaeeaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bound : Lower h53R h53G 5 := carry_of (swaps := [(4,5)]) (roots2 := h50R) (T2 := h50G) (by decide +kernel) h50Bound
def h54R : List Nat := varsOf 45
def h54G : Nat := 0xfffafffaffa0ffa0fffafffaffa0ffa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h54Bound : Lower h54R h54G 5 := carry_of (swaps := [(4,5),(0,1),(1,2),(2,3)]) (roots2 := h50R) (T2 := h50G) (by decide +kernel) h50Bound
def h55R : List Nat := varsOf 47
def h55G : Nat := 0xfee8fee8eea0eea0fee8fee8eea0eea0
def h55Pos : List Nat := [5,10,5,9,38,5,10,9,38,35,37,7,14,38,44,35,14,44,7,41,11,35,44,7,11,5,42,42,41,13,9,9,10,13,11,37,35,9,41,5,5,9,7]
def h55Neg : List Nat := [4,8,6,8,34,1,2,1,6,3,36,6,12,36,12,33,6,40,3,33,3,34,36,4,8,12,34,40,40,1,12,3,0,12,1,33,1,33,1,0,3,0,1]
def h55Mask : Nat := fullMask 43
def h55Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7fef3bc8ead,0x57ca01c82a0),(0xcccccccccccccccccccccccccccccccc,0x4150db5bb52,0x10084350b54),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x58a22c77d35,0x242c17d05),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x267fd5b50ca,0x25b02500a),(0xffffffff00000000ffffffff00000000,0x581c6ae710,0x281c6aa410)]
def h55Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(0,1,2),(1,1,2),(2,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(2,2,3),(1,3,5),(0,1,24),(2,1,24),(0,4,6),(2,4,7),(1,3,8),(3,0,29),(0,4,14),(2,4,14),(0,4,20),(1,8,23),(1,0,19),(1,1,9),(2,1,9),(1,3,9),(0,1,38),(1,1,38),(2,1,38),(3,1,38),(2,3,9),(2,4,9),(1,9,19),(1,9,33),(3,9,20),(1,9,22),(2,4,39),(0,4,40),(3,3,10),(0,4,10),(1,1,52),(2,1,52),(1,3,52),(2,3,52),(2,20,52),(0,10,20),(2,10,22),(0,1,55),(3,1,55),(1,3,11),(1,11,22),(1,1,13),(2,1,13),(2,4,13),(1,0,16),(1,3,67),(3,3,67),(2,14,16),(0,4,17),(1,3,18)]
def h55W : BT Decor := buildWiresBT 7 h55Base h55Steps
def h55AutoList : List (List (Nat × Nat)) := [[],[(1,2),(0,3)]]
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
def h55SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 32,7),some (subcubeFast 1 0,5),some (subcubeFast 1 4,4),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 2 32,4),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 8 2,4),some (subcubeFast 32 0,4)]
def h55Slices : BT (Option (Nat × Nat)) := btOfList 4 h55SliceList
def h55Specs : List PoolSpec := [(3,[]),(6,[]),(2,[(0,0,1)]),(4,[]),(1,[]),(8,[]),(2,[(0,0,1),(1,3,5)]),(11,[]),(2,[]),(9,[]),(5,[]),(10,[]),(2,[(1,0,1)]),(0,[]),(2,[(2,0,1)]),(6,[(2,4,7)]),(0,[(1,0,3)]),(2,[(3,0,1)]),(1,[(3,0,1)]),(6,[(0,4,20)]),(9,[(0,4,20)]),(7,[]),(2,[(3,0,1),(1,1,3)]),(2,[(0,0,2)]),(0,[(1,0,19)]),(2,[(0,1,3),(1,0,19)]),(2,[(0,1,3)]),(1,[(2,4,9)]),(1,[(1,3,9)]),(2,[(0,0,2),(1,3,9)]),(2,[(1,1,3)]),(2,[(2,1,3)]),(2,[(3,1,3)]),(2,[(0,0,2),(1,1,9)]),(2,[(0,0,2),(2,1,9)]),(2,[(0,0,2),(2,3,9)]),(2,[(1,0,2)]),(8,[(0,4,10)]),(3,[(0,4,10)]),(2,[(2,0,2)]),(2,[(2,0,2),(1,3,11)]),(2,[(3,0,2)]),(2,[(0,0,3)]),(2,[(0,0,3),(1,1,13)]),(2,[(0,0,3),(2,1,13)]),(2,[(1,0,3)]),(2,[(2,0,3)]),(2,[(0,1,2)]),(2,[(0,1,2),(1,0,16)]),(2,[(1,1,2)]),(6,[(0,4,17)]),(8,[(0,4,17)]),(2,[(2,1,2)])]
def h55Pools : BT (Option BoundPool) := buildPoolsBT 6 h55W h55R h55Slices h55Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice11 : Slice h55R h55G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice10 : Slice h55R h55G (subcubeFast 8 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice9 : Slice h55R h55G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice8 : Slice h55R h55G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice7 : Slice h55R h55G (subcubeFast 2 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice6 : Slice h55R h55G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice5 : Slice h55R h55G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice4 : Slice h55R h55G (subcubeFast 1 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice3 : Slice h55R h55G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice2 : Slice h55R h55G (subcubeFast 0 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice1 : Slice h55R h55G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h53Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Slice0 : Slice h55R h55G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h55R h55G p.1 p.2) h55Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h55R h55G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h55Slice0) (forall_cons (fun _ h => by cases h; exact h55Slice1) (forall_cons (fun _ h => by cases h; exact h55Slice2) (forall_cons (fun _ h => by cases h; exact h55Slice3) (forall_cons (fun _ h => by cases h; exact h55Slice4) (forall_cons (fun _ h => by cases h; exact h55Slice5) (forall_cons (fun _ h => by cases h; exact h55Slice6) (forall_cons (fun _ h => by cases h; exact h55Slice7) (forall_cons (fun _ h => by cases h; exact h55Slice8) (forall_cons (fun _ h => by cases h; exact h55Slice9) (forall_cons (fun _ h => by cases h; exact h55Slice10) (forall_cons (fun _ h => by cases h; exact h55Slice11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h55R h55G c) h55Pools := buildPoolsBT_sound h55SlicesOk
def h55Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h55G (4 - 1) xs.toFinset) h55Empty := trivial
def h55Block4_0 : List NodeSpec := nodesWithIdentity [([1,2,4,35,38],[]),([1,2,3,35,44],[]),([1,2,4,30,38],[]),([0,1,2,33,38],[]),([0,1,2,3,46],[]),([0,1,2,38,49],[]),([0,1,2,38,50],[]),([0,1,2,3,57],[]),([0,2,3,52,60],[]),([0,2,3,52,61],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test4_0 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Empty 4 h55Block4_0 = true := by decide +kernel
def h55Nodes4 : List NodeSpec := h55Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Check4 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Empty 4 h55Nodes4 = true := h55Test4_0
def h55Bucket4 : BT (List (List Nat)) := buildBucketsBT h55W h55Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h55G 4 xs.toFinset) h55Bucket4 := buildBucketsBT_sound (by decide) h55Pairs h55WOk h55PoolsOk h55AutosOk h55EmptyOk h55Check4
def h55Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,4,14,29],[1,8]),([0,2,3,8,33],[13,19,20]),([0,1,2,3,4,34],[]),([1,2,3,4,9,35],[1,9,24,25]),([0,1,2,3,19,44],[0,5,7,10,27]),([0,1,2,3,4,45],[0,1,7,8]),([1,2,3,4,9,30],[13]),([0,1,2,4,20,38],[0,5,28,29]),([0,1,2,3,20,44],[7,10]),([0,1,2,3,9,33],[7,13,19,20]),([0,1,2,3,4,47],[0,7,8]),([0,1,2,4,21,38],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_0 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_0 = true := by decide +kernel
def h55Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,21,44],[]),([0,1,2,4,22,38],[]),([0,1,2,3,22,44],[]),([0,1,2,3,4,48],[0]),([0,1,2,4,38,39],[0,5,28,29]),([0,1,2,4,38,40],[0,5,28,29]),([0,1,2,4,38,41],[]),([0,1,2,4,38,42],[]),([0,1,2,3,20,52],[7]),([0,1,2,3,4,58],[7,8]),([0,1,2,4,21,51],[13]),([0,1,2,3,21,52],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_1 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_1 = true := by decide +kernel
def h55Block5_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,22,52],[4,37]),([0,1,2,3,4,59],[]),([0,1,2,3,52,53],[7]),([0,1,2,3,52,54],[]),([0,1,2,3,52,55],[]),([0,1,2,3,52,56],[4,36]),([0,1,2,3,4,55],[1,4,13]),([0,1,2,3,4,63],[]),([1,2,3,4,14,67],[1,5]),([0,1,2,3,4,68],[1,7,8,13]),([0,1,2,3,4,70],[]),([0,1,2,3,4,69],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test5_2 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Block5_2 = true := by decide +kernel
def h55Nodes5 : List NodeSpec := h55Block5_0 ++ h55Block5_1 ++ h55Block5_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Check5 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket4 5 h55Nodes5 = true := by
  unfold h55Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h55Test5_0,h55Test5_1⟩,h55Test5_2⟩
def h55Bucket5 : BT (List (List Nat)) := buildBucketsBT h55W h55Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h55G 5 xs.toFinset) h55Bucket5 := buildBucketsBT_sound (by decide) h55Pairs h55WOk h55PoolsOk h55AutosOk h55Bucket4Ok h55Check5
def h55Block6_0 : List NodeSpec := [([0,1,2,3,4,24],[0,1,3,4,5,6,7,8],[0]),([0,1,2,3,4,27],[0,1,4,5,7,8,9,11,12,13],[0]),([0,1,2,3,28],[0,3,7,10,13,14,15],[0]),([0,1,2,3,4,8,14],[1,9,13,16],[0]),([0,2,3,4,8,20],[0,1,9,13,18,21,22],[0]),([0,1,2,3,4,8,23],[1,3,4,5,13],[0]),([0,1,2,3,4,29],[0,1,4,5,7,8,11,13],[0]),([0,1,2,3,4,9,19],[0,1,4,5,9,13,23,26],[0,1]),([0,1,2,3,4,9,20],[0,1,4,5,9,13,23,30],[0]),([0,1,2,3,4,9,21],[0,1,9,11,13,31],[0]),([0,1,2,3,4,9,22],[0,1,9,13,32],[0]),([0,2,3,4,36],[0,5,13,33],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_0 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_0 = true := by decide +kernel
def h55Block6_1 : List NodeSpec := [([0,2,3,4,37],[0,1,5,34],[0]),([0,1,2,4,38],[0,5,29],[0]),([0,1,2,3,4,38],[0,1,5,7,8,13,29],[0,1]),([0,1,2,4,43],[0,5,9,35],[0]),([0,1,2,3,44],[0,5,7,10,23],[0]),([0,1,2,3,4,10,20],[4,13,30,36],[0,1]),([0,1,2,3,4,10,21],[1,4,9,11,31],[0]),([0,1,2,3,4,10,22],[1,4,5,13,32],[0]),([0,1,2,3,4,51],[0,1,3,4,5,7,8,13],[0,1]),([0,1,2,3,52],[3,4,7,36,37,38],[0,1]),([0,1,2,3,4,52],[0,1,4,5,7,8,9,13,36],[0]),([0,1,2,3,4,11,21],[0,1,11,13],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_1 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_1 = true := by decide +kernel
def h55Block6_2 : List NodeSpec := [([0,1,2,3,4,11,22],[0,13],[0]),([0,1,2,3,4,62],[0,1,4,5,7,8,13,40],[0]),([0,1,2,3,4,12,21],[1,3,5],[0]),([0,2,3,4,64],[0,9,13,43],[0]),([0,2,3,4,65],[0,1,9,44],[0]),([0,1,2,3,66],[0,3,7,9,10,42],[0]),([0,1,2,3,4,14,16],[0,1,4,5,9,13],[0,1]),([0,1,2,3,4,14,25],[0,1,9,11,13],[0]),([0,1,2,3,4,14,26],[1,11,13],[0]),([0,1,2,3,4,31],[0,1,4,5,7,8,9,13,45],[0]),([0,1,2,3,4,32],[1,4,5,7,10,13,45],[0]),([0,1,2,3,4,14],[0,1,4,5,7,8,13,45],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_2 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_2 = true := by decide +kernel
def h55Block6_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,67],[0,1,3,5,7,8,9,13,48]),([0,1,2,3,71],[3,4,7,11,13,49,50,51]),([0,1,2,3,4,71],[0,1,3,7,8,9,11,13,49]),([0,1,2,3,4,72],[0,1,3,4,5,7,8,13])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test6_3 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Block6_3 = true := by decide +kernel
def h55Nodes6 : List NodeSpec := h55Block6_0 ++ h55Block6_1 ++ h55Block6_2 ++ h55Block6_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Check6 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket5 6 h55Nodes6 = true := by
  unfold h55Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h55Test6_0,h55Test6_1⟩,h55Test6_2⟩,h55Test6_3⟩
def h55Bucket6 : BT (List (List Nat)) := buildBucketsBT h55W h55Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h55G 6 xs.toFinset) h55Bucket6 := buildBucketsBT_sound (by decide) h55Pairs h55WOk h55PoolsOk h55AutosOk h55Bucket5Ok h55Check6
def h55Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,8,9,10],[0]),([0,1,2,3,4,6],[0,1,3,4,5,8,9,11,12,13],[0]),([0,1,2,3,4,7],[0,1,3,4,5,8,9,10,11,13,14],[0]),([0,1,2,3,4,8],[0,1,3,4,5,8,9,11,13,17,21],[0]),([0,1,2,3,4,9],[0,1,5,8,9,10,13,23],[0]),([0,1,2,3,4,10],[0,1,3,4,5,8,9,13,36],[0,1]),([0,1,2,3,4,11],[0,1,4,5,8,9,10,13,39],[0,1]),([0,1,2,3,4,12],[0,1,3,4,5,8,9,13,41],[0,1]),([0,1,2,3,4,13],[0,1,3,4,5,8,9,10,13,42],[0,1]),([0,1,2,3,4,14],[0,1,3,4,5,8,9,11,13,45],[0,1]),([0,1,2,3,4,15],[0,1,3,4,5,8,9,10,11,13,46],[0]),([0,1,2,3,4,16],[0,1,3,5,8,9,11,13,21,47],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Test7_0 : checkNodesBT h55W h55G h55Mask h55Pools h55Autos h55Bucket6 7 h55Block7_0 = true := by decide +kernel
def h55Block7_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,17],[0,1,3,4,5,8,9,11,13,49]),([0,1,2,3,4,18],[0,1,3,4,5,8,9,13,21,52])]
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
def h55Block8_0 : List NodeSpec := [([0,1,2,3,4],[8],[0,1])]
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
lemma h55Bound : Lower h55R h55G 9 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,1,9),(VAR 5,3,35)]) (by decide +kernel) h55Bucket8Ok (by decide +kernel)
def h56R : List Nat := varsOf 51
def h56G : Nat := 0xffffeeeeeeeeccccffffeeeeeeeecccc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h56Bound : Lower h56R h56G 5 := carry_of (swaps := [(4,5),(3,4),(0,1)]) (roots2 := h50R) (T2 := h50G) (by decide +kernel) h50Bound
def h57R : List Nat := varsOf 54
def h57G : Nat := 0xfffffcfcffffc0c0fffffcfcffffc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Bound : Lower h57R h57G 5 := carry_of (swaps := [(4,5),(0,1),(1,2),(2,3),(3,4),(0,1)]) (roots2 := h50R) (T2 := h50G) (by decide +kernel) h50Bound
def h58R : List Nat := varsOf 55
def h58G : Nat := 0xfefee8e8eeeec0c0fefee8e8eeeec0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h58Bound : Lower h58R h58G 9 := carry_of (swaps := [(3,4),(0,1)]) (roots2 := h55R) (T2 := h55G) (by decide +kernel) h55Bound
def h59R : List Nat := varsOf 59
def h59G : Nat := 0xffeeeeaaeeaacc88ffeeeeaaeeaacc88
def h59Pos : List Nat := [10,17,10,10,25,33,50,17,50,33,3,50,56,3,25,41,11,19,41,17,56,56,25,35,33,19,49,17,10,42,26,3,26,50,42,26,10,17,11,3,10,10,3,35,11,41,33,49,3,50,50,25,50,56]
def h59Neg : List Nat := [8,16,9,2,24,32,34,1,18,1,2,48,48,1,9,9,9,18,40,18,24,40,8,34,48,1,48,48,24,40,18,0,8,32,34,24,18,24,2,9,0,40,34,1,1,1,9,1,18,16,0,1,2,8]
def h59Mask : Nat := fullMask 54
def h59Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x9fce08fcfe6b2,0x8f8800201e284),(0xcccccccccccccccccccccccccccccccc,0x171fdff2832d4d,0x110454408a0548),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x28335d7075d01d,0x2042a93075c015),(0xffff0000ffff0000ffff0000ffff0000,0x3e802b4e7a59d2,0x300385d1a1912),(0xffffffff00000000ffffffff00000000,0x36e80625b49b60,0x6062da41860)]
def h59Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,1,4),(1,1,4),(3,1,4),(1,2,3),(3,2,3),(3,2,4),(1,2,5),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(1,3,5),(2,3,5),(1,1,31),(0,3,6),(2,3,6),(0,3,9),(0,3,37),(0,4,37),(0,6,9),(1,6,37),(0,9,37),(2,1,31),(3,1,31),(3,1,44),(0,9,44),(2,6,31),(0,9,31),(2,9,31),(1,1,38),(2,6,11),(1,0,23),(3,1,55),(0,3,55),(1,4,23),(2,4,23),(2,6,23),(1,0,31),(0,4,61),(3,0,31),(3,0,37),(0,2,37),(3,2,37),(1,2,31),(1,0,38),(1,2,7),(1,8,11),(1,8,31),(2,1,57),(1,0,47),(2,3,47),(1,0,59),(2,3,59),(2,4,40),(1,1,45),(1,2,40),(2,4,20),(1,0,80),(1,11,20),(2,3,82),(1,11,23),(1,11,31),(3,11,31),(2,4,83),(3,11,37),(0,2,53),(1,2,53),(2,2,53),(3,2,53),(0,3,17),(1,4,12),(2,4,12),(3,12,17),(2,3,18),(2,4,18),(1,12,18),(2,4,89),(2,3,16),(2,4,16),(1,1,62),(2,1,62),(1,2,62),(2,2,62),(3,4,13),(0,13,17),(1,0,108),(1,0,97),(2,13,18),(0,2,103),(3,2,103),(2,13,23),(1,0,24),(2,13,24),(1,1,74),(2,13,26),(2,3,29),(2,13,29),(1,16,62),(1,2,14),(3,14,17),(1,14,18),(1,1,63),(3,1,32),(2,17,31),(0,17,32),(3,31,32),(2,17,33),(1,18,31),(3,18,32),(1,18,33),(0,2,21),(3,2,21),(2,21,31),(1,26,31),(1,4,22),(1,23,34),(0,4,27),(1,0,28),(2,4,28),(1,0,142),(1,31,126),(3,31,126),(1,1,145)]
def h59W : BT Decor := buildWiresBT 8 h59Base h59Steps
def h59AutoList : List (List (Nat × Nat)) := [[],[(4,5)]]
def h59Autos : BT (List (Nat × Nat)) := btOfList 1 h59AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Pairs : goodPairs h59G h59Pos h59Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59BaseOk : ∀ x ∈ h59Base, faithful h59Pos h59Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59WOk : btAll (fun x => faithful h59Pos h59Neg x ∧ x.1 < 2^128) h59W := buildWiresBT_faithful h59BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h59G = h59G) h59Autos := btAll_ofList (autos_of (by decide +kernel))
def h59SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 16,4),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 2 8,4),some (subcubeFast 8 0,6),some (subcubeFast 16 0,4),some (subcubeFast 32 0,4)]
def h59Slices : BT (Option (Nat × Nat)) := btOfList 4 h59SliceList
def h59Specs : List PoolSpec := [(3,[]),(6,[]),(8,[(0,0,1)]),(4,[]),(5,[]),(8,[]),(0,[]),(8,[(0,0,1),(1,3,5)]),(1,[]),(8,[(0,0,1),(2,3,5)]),(9,[]),(2,[]),(8,[(1,0,1)]),(6,[(1,0,2)]),(7,[]),(0,[(1,0,1)]),(1,[(1,0,2)]),(2,[(1,0,2)]),(6,[(3,0,2)]),(1,[(3,0,2)]),(2,[(3,0,2)]),(1,[(1,0,1)]),(10,[]),(8,[(1,0,1),(0,3,6)]),(8,[(2,0,1)]),(0,[(2,0,1)]),(2,[(1,0,1)]),(6,[(1,2,7)]),(8,[(3,0,1)]),(1,[(1,0,23)]),(8,[(3,1,3)]),(2,[(1,0,2),(1,0,31)]),(0,[(3,1,3)]),(3,[(0,3,4)]),(8,[(0,3,4)]),(1,[(1,0,2),(1,0,31)]),(8,[(0,3,9)]),(8,[(0,1,3)]),(8,[(0,0,3)]),(1,[(1,4,12)]),(8,[(0,0,3),(1,4,12)]),(8,[(0,0,3),(2,4,12)]),(1,[(2,4,12)]),(8,[(1,0,3)]),(2,[(1,0,31)]),(2,[(1,0,3)]),(3,[(3,4,13)]),(8,[(1,0,3),(3,4,13)]),(8,[(2,0,3)]),(8,[(3,0,3)]),(2,[(3,0,3)]),(1,[(3,0,31)]),(2,[(3,0,31)]),(8,[(0,3,17)]),(6,[(0,3,17)]),(8,[(2,3,18)]),(8,[(1,1,3)]),(8,[(1,1,4)]),(8,[(3,1,4)]),(6,[(3,2,21)]),(0,[(1,1,3)]),(8,[(2,1,3)]),(8,[(2,1,3),(1,4,22)]),(3,[(3,3,4)]),(8,[(3,1,3),(2,4,23)]),(8,[(0,4,27)]),(8,[(1,0,28)]),(8,[(2,4,28)]),(1,[(1,0,31)]),(8,[(0,3,4),(1,3,4)]),(8,[(1,3,4),(0,3,4)]),(8,[(1,3,4)]),(8,[(2,3,4)])]
def h59Pools : BT (Option BoundPool) := buildPoolsBT 7 h59W h59R h59Slices h59Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice10 : Slice h59R h59G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice9 : Slice h59R h59G (subcubeFast 16 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice8 : Slice h59R h59G (subcubeFast 8 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice7 : Slice h59R h59G (subcubeFast 2 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice6 : Slice h59R h59G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice5 : Slice h59R h59G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice4 : Slice h59R h59G (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice3 : Slice h59R h59G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice2 : Slice h59R h59G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice1 : Slice h59R h59G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h53Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice0 : Slice h59R h59G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h56Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h59R h59G p.1 p.2) h59Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h59R h59G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h59Slice0) (forall_cons (fun _ h => by cases h; exact h59Slice1) (forall_cons (fun _ h => by cases h; exact h59Slice2) (forall_cons (fun _ h => by cases h; exact h59Slice3) (forall_cons (fun _ h => by cases h; exact h59Slice4) (forall_cons (fun _ h => by cases h; exact h59Slice5) (forall_cons (fun _ h => by cases h; exact h59Slice6) (forall_cons (fun _ h => by cases h; exact h59Slice7) (forall_cons (fun _ h => by cases h; exact h59Slice8) (forall_cons (fun _ h => by cases h; exact h59Slice9) (forall_cons (fun _ h => by cases h; exact h59Slice10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h59R h59G c) h59Pools := buildPoolsBT_sound h59SlicesOk
def h59Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G (3 - 1) xs.toFinset) h59Empty := trivial
def h59Block3_0 : List NodeSpec := nodesWithIdentity [([1,3,49,62],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test3_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Empty 3 h59Block3_0 = true := by decide +kernel
def h59Nodes3 : List NodeSpec := h59Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check3 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Empty 3 h59Nodes3 = true := h59Test3_0
def h59Bucket3 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 3 xs.toFinset) h59Bucket3 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59EmptyOk h59Check3
def h59Block4_0 : List NodeSpec := nodesWithIdentity [([3,4,6,9,37],[]),([1,3,4,9,44],[5]),([1,3,4,9,50],[]),([1,4,9,23,61],[31]),([1,3,4,9,73],[]),([1,3,4,9,48],[]),([1,4,9,40,61],[31]),([0,1,3,4,45],[5]),([0,3,4,9,78],[]),([0,1,3,11,87],[]),([0,1,3,4,88],[]),([2,3,4,43,53],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test4_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket3 4 h59Block4_0 = true := by decide +kernel
def h59Block4_1 : List NodeSpec := nodesWithIdentity [([0,2,3,53,100],[]),([0,2,3,53,102],[]),([0,1,2,62,97],[]),([0,2,23,62,103],[]),([0,2,23,62,104],[]),([2,3,4,43,56],[]),([1,2,3,43,62],[]),([0,1,2,62,101],[]),([0,1,2,3,121],[]),([0,1,3,62,112],[]),([0,1,3,62,113],[]),([0,1,2,32,127],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test4_1 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket3 4 h59Block4_1 = true := by decide +kernel
def h59Block4_2 : List NodeSpec := nodesWithIdentity [([0,1,2,31,132],[]),([0,1,4,74,134],[]),([1,3,4,37,49],[]),([0,1,31,32,66],[]),([0,2,31,37,126],[]),([0,1,2,31,145],[]),([0,2,31,46,126],[]),([0,1,2,31,144],[]),([0,1,2,31,146],[]),([2,3,4,43,117],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test4_2 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket3 4 h59Block4_2 = true := by decide +kernel
def h59Nodes4 : List NodeSpec := h59Block4_0 ++ h59Block4_1 ++ h59Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check4 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket3 4 h59Nodes4 = true := by
  unfold h59Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h59Test4_0,h59Test4_1⟩,h59Test4_2⟩
def h59Bucket4 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 4 xs.toFinset) h59Bucket4 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59Bucket3Ok h59Check4
def h59Block5_0 : List NodeSpec := nodesWithIdentity [([1,3,4,6,9,31],[3,4,13]),([1,3,4,6,9,38],[0,3,13]),([1,3,4,6,9,39],[3]),([0,1,3,4,11,54],[12]),([1,2,3,4,6,55],[5]),([1,2,3,4,6,61],[1,3,4]),([0,2,3,4,6,37],[0,10,22]),([0,1,2,3,4,44],[5,6,8,11]),([0,1,2,3,4,50],[]),([0,1,3,4,11,70],[28]),([0,2,3,4,8,37],[]),([0,1,2,3,4,71],[5,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_0 = true := by decide +kernel
def h59Block5_1 : List NodeSpec := [([0,1,4,9,23,31],[13,17],[0]),([0,1,3,4,9,47],[0],[0]),([0,1,3,4,9,59],[],[0]),([1,3,4,9,61],[3,4,5,31,33,35],[0,1]),([1,3,4,9,31,61],[0,3,31,35],[0]),([0,1,3,4,9,37],[0,6],[0]),([0,1,4,9,31,40],[6,17],[0]),([0,1,3,4,9,51],[0,5,13],[0]),([0,1,3,4,9,52],[0,5],[0]),([0,1,3,4,9,77],[],[0]),([1,2,3,4,9,61],[3,5],[0]),([0,1,2,3,4,52],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_1 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_1 = true := by decide +kernel
def h59Block5_2 : List NodeSpec := nodesWithIdentity [([0,1,3,4,11,80],[]),([0,1,3,4,11,82],[37]),([0,1,4,11,23,31],[18,20]),([0,1,3,4,11,47],[]),([0,1,3,4,11,59],[]),([0,1,3,4,11,84],[]),([0,1,3,4,11,83],[20]),([0,1,3,4,11,37],[5]),([0,1,3,4,11,85],[34]),([0,1,3,4,11,86],[]),([0,2,3,4,17,53],[5,10,21]),([0,1,2,3,17,94],[10,39])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_2 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_2 = true := by decide +kernel
def h59Block5_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,17,95],[]),([0,1,2,3,4,96],[0,5]),([0,2,3,4,18,53],[]),([0,1,2,3,18,94],[]),([0,1,2,3,18,95],[]),([0,1,2,3,4,99],[0,5]),([0,2,3,4,53,89],[0,4,10,21]),([0,2,3,4,53,90],[10,21]),([0,2,3,4,53,91],[]),([0,2,3,4,53,92],[]),([0,2,3,4,16,53],[0,4,10,21]),([0,2,3,4,19,53],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_3 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_3 = true := by decide +kernel
def h59Block5_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,17,62],[]),([0,1,2,3,17,107],[]),([0,1,2,3,4,108],[]),([0,1,2,4,13,97],[]),([0,1,2,3,18,62],[8]),([0,1,2,3,18,107],[]),([0,1,2,3,4,111],[]),([0,1,2,23,62],[3,4,8,33,44]),([0,1,2,4,23,62],[4,44]),([0,1,2,4,23,114],[]),([1,2,3,4,13,115],[1]),([0,1,2,4,13,76],[22])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_4 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_4 = true := by decide +kernel
def h59Block5_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,116],[8]),([0,1,2,4,13,74],[22]),([0,1,2,3,4,118],[8]),([0,2,3,4,16,56],[8]),([0,2,3,4,19,56],[6]),([0,1,2,4,13,119],[22]),([0,1,2,3,4,120],[8]),([0,1,2,3,16,62],[8,22,33]),([0,1,2,3,19,62],[]),([0,1,2,3,62,103],[8,22,44]),([0,1,2,3,62,104],[4,8]),([0,1,2,3,62,105],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_5 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_5 = true := by decide +kernel
def h59Block5_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,62,106],[]),([0,1,2,3,4,103],[5,6,8,22]),([0,1,2,4,14,93],[6]),([0,1,2,3,4,123],[5]),([0,1,2,3,4,124],[5]),([0,1,2,3,4,125],[5,6]),([0,2,3,4,17,37],[5]),([0,1,2,17,31,32],[10]),([0,1,2,3,4,127],[]),([0,1,2,4,32,93],[10]),([0,1,2,3,4,128],[]),([0,1,2,3,4,130],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_6 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_6 = true := by decide +kernel
def h59Block5_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,109],[6,11,22]),([0,2,3,4,18,37],[5]),([0,1,2,18,31,32],[8]),([0,1,2,3,4,131],[6]),([0,1,2,3,4,132],[]),([0,1,2,3,33,98],[]),([0,1,2,3,4,133],[]),([0,1,2,3,4,110],[]),([0,1,2,3,4,81],[8]),([0,1,2,21,25,31],[1,8]),([0,1,2,4,21,41],[]),([0,1,2,3,4,37],[5,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_7 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_7 = true := by decide +kernel
def h59Block5_8 : List NodeSpec := nodesWithIdentity [([0,1,2,21,26,31],[1,8]),([0,1,2,4,21,74],[]),([0,1,2,4,31,136],[8]),([0,1,2,23,26,31],[1,8]),([0,1,2,4,23,61],[8,44]),([0,1,2,4,23,139],[8]),([0,1,2,3,4,73],[]),([0,1,2,3,4,75],[8]),([0,1,2,3,4,143],[8]),([0,1,2,3,4,48],[]),([0,1,2,3,4,64],[5,6]),([0,1,3,4,37,65],[6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_8 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_8 = true := by decide +kernel
def h59Block5_9 : List NodeSpec := nodesWithIdentity [([0,1,3,4,37,66],[5]),([0,1,3,4,31,66],[]),([0,1,2,31,32,37],[8,10,69]),([0,1,2,31,32,46],[8]),([0,1,2,31,32,67],[70]),([0,1,2,31,126],[3,8,33]),([0,1,2,31,129],[3,8,33]),([0,2,3,4,16,117],[10,11]),([0,2,3,4,19,117],[6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_9 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_9 = true := by decide +kernel
def h59Nodes5 : List NodeSpec := h59Block5_0 ++ h59Block5_1 ++ h59Block5_2 ++ h59Block5_3 ++ h59Block5_4 ++ h59Block5_5 ++ h59Block5_6 ++ h59Block5_7 ++ h59Block5_8 ++ h59Block5_9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check5 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Nodes5 = true := by
  unfold h59Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h59Test5_0,h59Test5_1⟩,h59Test5_2⟩,h59Test5_3⟩,h59Test5_4⟩,h59Test5_5⟩,h59Test5_6⟩,h59Test5_7⟩,h59Test5_8⟩,h59Test5_9⟩
def h59Bucket5 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 5 xs.toFinset) h59Bucket5 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59Bucket4Ok h59Check5
def h59Block6_0 : List NodeSpec := [([0,1,3,4,30],[0,1,2,3,5,6],[0]),([0,1,2,4,35],[0,1,4,7,8],[0]),([0,1,2,4,36],[0,1,3,4,9,10],[0]),([1,3,4,6,9],[0,3,4,5,12,13,14,15],[0,1]),([0,1,3,4,6,9],[0,3,4,5,6,12,13,14,16,17],[0]),([0,1,3,4,6,11],[0,3,4,5,6,12,14,18,19,20],[0]),([0,1,2,3,4,6,23],[0,8,10,14,21],[0]),([0,1,2,3,4,6,31],[0,1,3,4,8,10,11,22],[0]),([0,1,2,3,4,38],[0,1,3,5,6,10,11,21,22,23],[0]),([0,1,2,3,4,6,38],[0,1,3,8,10],[0]),([0,1,2,3,4,39],[3,5,6,10,11,21,22],[0]),([0,1,2,3,4,6,39],[3,8,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_0 = true := by decide +kernel
def h59Block6_1 : List NodeSpec := [([1,3,4,7,9],[0,3,4,13,14,25],[0]),([0,1,2,3,4,6],[0,1,5,6,8,10,11,12,14,21,22,26],[0]),([0,1,3,4,69],[0,3,4,5,6,24,27],[0]),([0,1,3,4,8,11],[0,3,4,5,18,19,20,28],[0]),([0,1,2,3,4,8,31],[1,3,4,8,10,11,22],[0]),([0,1,2,3,4,57],[0,1,3,5,6,10,11,22,29],[0]),([0,1,3,4,9,23],[0,3,6,13,14,16,17,30,32],[0]),([0,1,3,4,9,31],[0,3,4,6,13,16,17,33,34],[0,1]),([0,1,3,4,9,40],[0,3,5,6,13,14,16,17,36],[0]),([0,1,2,3,4,9,31],[0,3,5,6,8,10,11,22,34],[0]),([0,1,2,3,4,40],[0,1,3,5,6,10,11,14,22,36],[0]),([0,1,3,4,9],[0,3,4,5,6,13,14,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_1 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_1 = true := by decide +kernel
def h59Block6_2 : List NodeSpec := [([0,1,3,4,11,20],[0,3,5,18,19,20,37],[0]),([0,1,3,4,11,23],[0,3,5,18,19,20,30],[0]),([0,1,3,4,11,31],[0,3,4,5,18,19,20,33,34],[0,1]),([0,1,2,3,4,12,17],[0,1,5,6,8,10],[0]),([0,1,2,3,4,12,18],[0,1,5,6],[0]),([0,2,3,4,53],[0,3,4,10,21],[0]),([0,1,2,3,4,53],[0,1,3,4,5,6,10,11,21,22],[0]),([0,2,3,4,72],[0,1,4,10,29],[0]),([0,1,3,4,79],[0,4,5,6,10,16,36],[0]),([0,1,2,3,94],[0,10,11,39,40],[0]),([0,1,2,3,95],[0,4,10,22,41,42],[0]),([0,1,2,3,4,13,17],[6,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_2 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_2 = true := by decide +kernel
def h59Block6_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,13,18],[1,5,6,8]),([0,1,2,4,13,23],[0,1,3,8,10,32,45]),([0,1,2,3,4,13,24],[0,1,8,11,22]),([0,1,2,3,4,13,26],[4,8,11,22]),([0,1,2,3,4,56],[0,1,3,5,6,8,10,11,22]),([0,1,2,3,4,13,29],[6,8,11,22]),([0,1,2,3,62],[3,4,8,22,33]),([0,1,2,3,4,62],[0,1,3,4,5,6,8,10,22,33,44]),([0,1,2,3,107],[3,8,11,46,47]),([0,1,2,3,4,14,17],[0,5,6,8]),([0,1,2,3,4,14,18],[0,1,5,6]),([0,1,2,3,4,60],[0,1,4,5,6,8,11,22])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_3 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_3 = true := by decide +kernel
def h59Block6_4 : List NodeSpec := [([0,1,3,4,122],[0,4,5,6,8,48],[0]),([0,1,2,3,4,15,17],[3,6,10],[0]),([0,1,2,3,4,15,18],[1,3,5,6,8,10],[0]),([0,1,2,4,15,23],[0,1,3,8,10,32,50],[0]),([0,1,2,3,4,15,24],[1,3,8,10],[0]),([0,1,2,3,4,15,26],[3,4,8,10,11,22],[0]),([0,1,2,3,4,15,29],[3,6,8,10],[0]),([0,1,2,3,4,63],[1,3,4,5,6,10,22,33,51,52],[0]),([0,1,2,3,4,70],[0,1,5,6,8,10,11,14,18,22,28],[0]),([0,1,2,3,4,17,31],[1,5,6,10],[0]),([0,1,2,3,4,17,32],[6,8,11],[0,1]),([0,1,2,3,4,17,33],[6,8,10,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_4 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_4 = true := by decide +kernel
def h59Block6_5 : List NodeSpec := [([0,1,2,3,4,93],[0,1,5,6,10,11,14,22,53,54],[0]),([0,1,2,3,4,54],[0,1,5,6,8,10,11,12,22],[0]),([0,1,2,3,4,18,31],[1,5,6,8,10,11,22],[0]),([0,1,2,3,4,18,32],[1,5,6,8],[0]),([0,1,2,3,4,18,33],[1,5,6,11],[0]),([0,1,2,3,4,97],[0,1,5,6,10,11,22,55],[0,1]),([0,1,2,3,4,68],[0,1,3,5,6,10,11,14,21,22],[0,1]),([0,1,2,3,4,23],[0,1,3,5,6,8,10,11,22,30],[0]),([0,1,2,3,4,80],[0,1,5,6,8,10,14,22],[0,1]),([0,1,2,3,4,21,25],[1,8,11,14,56,57],[0,1]),([0,1,2,3,4,21,26],[8,10,11,14,22,58],[0]),([0,1,3,4,135],[3,6,8,14,56,59],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_5 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_5 = true := by decide +kernel
def h59Block6_6 : List NodeSpec := [([0,1,2,4,21,31],[1,3,8,10,11,33,60],[0]),([0,1,2,3,4,42],[0,1,3,5,6,8,10,22],[0,1]),([0,1,2,3,138],[1,3,8,11,62],[0]),([0,1,2,3,137],[1,3,8,14,22],[0]),([0,1,2,3,4,137],[0,1,3,5,6,8,14,22],[0]),([0,1,2,3,4,55],[0,1,3,5,6,8,10,11,22,29],[0]),([0,1,2,3,4,23,55],[0,1,8,10,29],[0]),([0,1,2,3,4,23,26],[8,10,11,22],[0]),([0,1,2,4,23,31],[1,3,8,10,11,32,33],[0,1]),([0,1,2,4,23,34],[1,3,8,10,11,32,63],[0]),([0,1,2,3,4,47],[0,5,6,10,22],[0]),([0,1,2,3,4,23,58],[1,8,10,11,22],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_6 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_6 = true := by decide +kernel
def h59Block6_7 : List NodeSpec := [([0,1,2,3,4,59],[0,1,5,6,8,10,22,64],[0,1]),([0,1,2,3,4,23,59],[1,8,10,11],[0]),([0,1,2,3,4,140],[0,1,3,5,6,8,14,22,65],[0]),([0,1,2,3,4,141],[0,1,3,5,6,10,11,14,22,66],[0]),([0,1,2,3,4,142],[0,1,5,6,8,10,14,22,67],[0,1]),([0,1,2,3,4,61],[0,1,3,4,5,6,8,10,11,22,33,44,68],[0,1]),([0,1,2,3,4,31,61],[0,3,8,10,11,22,33,44,68],[0]),([0,1,2,3,4,37],[0,1,5,6,8,10,11,22],[0]),([0,1,2,3,4,31,37],[1,8,10,11,22,34],[0]),([0,1,2,3,4,31,46],[1,8,10,11,22],[0]),([0,1,2,3,4,31,67],[5,6,34],[0]),([0,1,2,31,32],[3,8,10,33,69],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_7 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_7 = true := by decide +kernel
def h59Block6_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,126],[0,1,3,5,6,8,11]),([0,1,2,3,4,117],[0,1,4,5,6,8,10,11]),([0,1,2,3,4,31],[0,1,3,5,6,8,10,11,22,33,34])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_8 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_8 = true := by decide +kernel
def h59Nodes6 : List NodeSpec := h59Block6_0 ++ h59Block6_1 ++ h59Block6_2 ++ h59Block6_3 ++ h59Block6_4 ++ h59Block6_5 ++ h59Block6_6 ++ h59Block6_7 ++ h59Block6_8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check6 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Nodes6 = true := by
  unfold h59Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h59Test6_0,h59Test6_1⟩,h59Test6_2⟩,h59Test6_3⟩,h59Test6_4⟩,h59Test6_5⟩,h59Test6_6⟩,h59Test6_7⟩,h59Test6_8⟩
def h59Bucket6 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 6 xs.toFinset) h59Bucket6 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59Bucket5Ok h59Check6
def h59Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,8,11],[0,1]),([0,1,2,3,4,6],[0,1,3,4,5,6,8,11,12,14],[0,1]),([0,1,2,3,4,7],[0,1,3,4,5,6,8,11,14,24],[0]),([0,1,2,3,4,8],[0,1,3,4,5,6,8,11,14,28],[0,1]),([0,1,3,4,9],[0,3,4,5,6,14],[0,1]),([0,1,2,3,4,9],[0,1,3,4,5,6,8,11,14],[0,1]),([0,1,2,3,4,10],[0,1,3,4,5,8,11,14],[0]),([0,1,3,4,11],[0,3,4,5],[0,1]),([0,1,2,3,4,12],[0,1,3,4,5,6,8,10,11,38],[0]),([0,1,2,3,4,13],[0,1,3,4,5,6,8,11,43],[0]),([0,1,2,3,4,14],[0,1,4,5,6,8,11,48],[0]),([0,1,2,3,4,15],[0,1,3,4,5,6,8,10,11,49],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test7_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket6 7 h59Block7_0 = true := by decide +kernel
def h59Block7_1 : List NodeSpec := [([0,1,2,3,4,17],[0,1,5,6,8,11,14],[0,1]),([0,1,2,3,4,18],[0,1,5,6,8,11],[0,1]),([0,1,2,3,4,20],[0,1,3,5,6,8,10,11,14,37],[0,1]),([0,1,2,3,4,21],[0,1,3,5,6,8,11,14,56],[0]),([0,1,2,3,4,22],[0,1,3,5,6,8,11,14,61],[0]),([0,1,2,3,4,23],[0,1,3,5,6,8,10,11,14,30],[0,1]),([0,1,2,3,4,27],[0,1,3,5,6,8,11,14],[0]),([0,1,2,3,4,28],[0,1,3,5,6,8,10,11,14],[0,1]),([0,1,2,3,4,31],[0,1,3,4,5,6,8,10,11,22,34],[0,1]),([0,1,2,3,4,32],[0,1,3,5,6,8,11,71],[0]),([0,1,2,3,4,33],[0,1,3,4,5,6,8,10,11,72],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test7_1 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket6 7 h59Block7_1 = true := by decide +kernel
def h59Nodes7 : List NodeSpec := h59Block7_0 ++ h59Block7_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check7 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket6 7 h59Nodes7 = true := by
  unfold h59Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h59Test7_0,h59Test7_1⟩
def h59Bucket7 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 7 xs.toFinset) h59Bucket7 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59Bucket6Ok h59Check7
def h59Block8_0 : List NodeSpec := [([0,1,2,3,4],[5],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test8_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket7 8 h59Block8_0 = true := by decide +kernel
def h59Nodes8 : List NodeSpec := h59Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check8 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket7 8 h59Nodes8 = true := h59Test8_0
def h59Bucket8 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 8 xs.toFinset) h59Bucket8 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59Bucket7Ok h59Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bound : Lower h59R h59G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h59Bucket8Ok (by decide +kernel)
def h60R : List Nat := varsOf 61
def h60G : Nat := 0xfffafaaaffa0f0a0fffafaaaffa0f0a0
def h60Pos : List Nat := [12,33,5,5,12,12,13,21,52,33,5,24,24,41,25,21,25,33,52,24,41,37,44,52,49,24,21,28,5,44,28,56,49,52,52,56,24]
def h60Neg : List Nat := [8,32,1,4,9,4,9,17,20,1,0,8,16,9,9,20,17,36,36,17,40,36,36,48,48,20,4,8,17,40,20,40,17,32,16,48,40]
def h60Mask : Nat := fullMask 37
def h60Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x11533e6ce,0x1100962d4),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x67ce485fd,0x46668128),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x18ea597871,0x10a8106851),(0xffff0000ffff0000ffff0000ffff0000,0x1fcf8dd980,0xd53899180),(0xffffffff00000000ffffffff00000000,0xfa1f62302,0x1aa1f60002)]
def h60Steps : List (Nat × Nat × Nat) := [(1,0,1),(3,0,1),(0,1,3),(3,1,3),(1,2,5),(3,2,5),(1,2,6),(3,2,6),(0,3,4),(0,4,5),(1,0,2),(0,1,15),(3,1,15),(3,0,3),(1,1,18),(2,1,18),(1,0,7),(1,0,8),(1,1,13),(2,1,13)]
def h60W : BT Decor := buildWiresBT 5 h60Base h60Steps
def h60AutoList : List (List (Nat × Nat)) := [[],[(4,5),(0,3)]]
def h60Autos : BT (List (Nat × Nat)) := btOfList 1 h60AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Pairs : goodPairs h60G h60Pos h60Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60BaseOk : ∀ x ∈ h60Base, faithful h60Pos h60Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60WOk : btAll (fun x => faithful h60Pos h60Neg x ∧ x.1 < 2^128) h60W := buildWiresBT_faithful h60BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h60G = h60G) h60Autos := btAll_ofList (autos_of (by decide +kernel))
def h60SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 8 0,5),some (subcubeFast 8 16,4),some (subcubeFast 16 0,4),some (subcubeFast 32 0,4)]
def h60Slices : BT (Option (Nat × Nat)) := btOfList 3 h60SliceList
def h60Specs : List PoolSpec := [(2,[]),(4,[]),(1,[(1,0,1)]),(6,[]),(0,[]),(7,[]),(1,[]),(2,[(0,4,5)]),(3,[]),(1,[(3,0,1)]),(0,[(1,0,2)]),(5,[]),(1,[(1,0,2)]),(4,[(3,0,3)]),(1,[(3,0,3)]),(4,[(0,1,3)]),(2,[(0,3,4)]),(4,[(0,3,4)])]
def h60Pools : BT (Option BoundPool) := buildPoolsBT 5 h60W h60R h60Slices h60Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Slice7 : Slice h60R h60G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Slice6 : Slice h60R h60G (subcubeFast 16 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Slice5 : Slice h60R h60G (subcubeFast 8 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Slice4 : Slice h60R h60G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Slice3 : Slice h60R h60G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Slice2 : Slice h60R h60G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Slice1 : Slice h60R h60G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Slice0 : Slice h60R h60G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h60R h60G p.1 p.2) h60Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h60R h60G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h60Slice0) (forall_cons (fun _ h => by cases h; exact h60Slice1) (forall_cons (fun _ h => by cases h; exact h60Slice2) (forall_cons (fun _ h => by cases h; exact h60Slice3) (forall_cons (fun _ h => by cases h; exact h60Slice4) (forall_cons (fun _ h => by cases h; exact h60Slice5) (forall_cons (fun _ h => by cases h; exact h60Slice6) (forall_cons (fun _ h => by cases h; exact h60Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h60R h60G c) h60Pools := buildPoolsBT_sound h60SlicesOk
def h60Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h60G (4 - 1) xs.toFinset) h60Empty := trivial
def h60Block4_0 : List NodeSpec := nodesWithIdentity [([1,2,3,6,14],[]),([1,2,3,14,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test4_0 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Empty 4 h60Block4_0 = true := by decide +kernel
def h60Nodes4 : List NodeSpec := h60Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Check4 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Empty 4 h60Nodes4 = true := h60Test4_0
def h60Bucket4 : BT (List (List Nat)) := buildBucketsBT h60W h60Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h60G 4 xs.toFinset) h60Bucket4 := buildBucketsBT_sound (by decide) h60Pairs h60WOk h60PoolsOk h60AutosOk h60EmptyOk h60Check4
def h60Block5_0 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,6],[0]),([1,2,3,4,5,15],[1]),([0,1,2,3,4,9],[3,4,5,6]),([0,1,2,3,4,10],[]),([0,1,2,3,14],[2,7]),([0,1,2,3,5,14],[6]),([0,1,2,3,4,11],[3,4]),([0,1,2,3,4,12],[]),([0,1,2,3,4,16],[0,1,3,4,5,6]),([0,1,2,3,4,17],[]),([0,1,2,3,4,19],[]),([0,1,2,3,4,20],[0,5,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test5_0 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket4 5 h60Block5_0 = true := by decide +kernel
def h60Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,21],[5,6]),([0,1,2,3,4,22],[]),([0,1,2,3,4,23],[]),([0,1,2,3,4,24],[4,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test5_1 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket4 5 h60Block5_1 = true := by decide +kernel
def h60Nodes5 : List NodeSpec := h60Block5_0 ++ h60Block5_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Check5 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket4 5 h60Nodes5 = true := by
  unfold h60Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h60Test5_0,h60Test5_1⟩
def h60Bucket5 : BT (List (List Nat)) := buildBucketsBT h60W h60Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h60G 5 xs.toFinset) h60Bucket5 := buildBucketsBT_sound (by decide) h60Pairs h60WOk h60PoolsOk h60AutosOk h60Bucket4Ok h60Check5
def h60Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,8],[0]),([0,1,2,3,4,6],[0,1,3,4,5,6,8,9],[0]),([0,1,2,3,4,15],[0,1,3,4,5,6,8,10,11,12],[0,1]),([0,1,2,3,4,18],[0,1,3,4,5,6,11,13,14],[0]),([0,1,2,3,4,7],[0,1,3,4,5,6,11,15],[0]),([0,1,2,3,4,8],[0,1,3,4,5,6,11],[0]),([0,1,2,3,4,13],[0,1,3,4,5,6,8,11,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test6_0 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket5 6 h60Block6_0 = true := by decide +kernel
def h60Nodes6 : List NodeSpec := h60Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Check6 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket5 6 h60Nodes6 = true := h60Test6_0
def h60Bucket6 : BT (List (List Nat)) := buildBucketsBT h60W h60Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h60G 6 xs.toFinset) h60Bucket6 := buildBucketsBT_sound (by decide) h60Pairs h60WOk h60PoolsOk h60AutosOk h60Bucket5Ok h60Check6
def h60Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,4,6,8,11],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test7_0 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket6 7 h60Block7_0 = true := by decide +kernel
def h60Nodes7 : List NodeSpec := h60Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Check7 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket6 7 h60Nodes7 = true := h60Test7_0
def h60Bucket7 : BT (List (List Nat)) := buildBucketsBT h60W h60Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h60G 7 xs.toFinset) h60Bucket7 := buildBucketsBT_sound (by decide) h60Pairs h60WOk h60PoolsOk h60AutosOk h60Bucket6Ok h60Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Bound : Lower h60R h60G 8 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,4,12),(VAR 4,8,24),(VAR 5,1,33)]) (by decide +kernel) h60Bucket7Ok (by decide +kernel)
def h61R : List Nat := varsOf 62
def h61G : Nat := 0xfffcfcfcfff0c0c0fffcfcfcfff0c0c0
def h61Pos : List Nat := [20,34,6,6,20,14,26,20,34,36,14,42,24,26,50,24,6,50,36,56,56]
def h61Neg : List Nat := [16,32,2,4,18,12,10,4,2,4,10,10,16,18,18,8,0,48,32,48,40]
def h61Mask : Nat := fullMask 21
def h61Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x36d6e,0x6d54),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x506bd,680),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x18bc60,0x108c60),(0xffff0000ffff0000ffff0000ffff0000,0x1af0d1,0xa7011),(0xffffffff00000000ffffffff00000000,0x1e4b02,0x1e0002)]
def h61Steps : List (Nat × Nat × Nat) := [(1,0,1),(3,0,1),(1,0,4),(3,4,5)]
def h61W : BT Decor := buildWiresBT 4 h61Base h61Steps
def h61AutoList : List (List (Nat × Nat)) := [[],[(1,5)]]
def h61Autos : BT (List (Nat × Nat)) := btOfList 1 h61AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Pairs : goodPairs h61G h61Pos h61Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61BaseOk : ∀ x ∈ h61Base, faithful h61Pos h61Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61WOk : btAll (fun x => faithful h61Pos h61Neg x ∧ x.1 < 2^128) h61W := buildWiresBT_faithful h61BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h61G = h61G) h61Autos := btAll_ofList (autos_of (by decide +kernel))
def h61SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,5),some (subcubeFast 2 0,4),some (subcubeFast 8 0,5),some (subcubeFast 16 0,4),some (subcubeFast 24 0,4),some (subcubeFast 32 0,4)]
def h61Slices : BT (Option (Nat × Nat)) := btOfList 3 h61SliceList
def h61Specs : List PoolSpec := [(1,[]),(5,[]),(0,[]),(2,[]),(4,[]),(3,[])]
def h61Pools : BT (Option BoundPool) := buildPoolsBT 3 h61W h61R h61Slices h61Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice5 : Slice h61R h61G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice4 : Slice h61R h61G (subcubeFast 24 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice3 : Slice h61R h61G (subcubeFast 16 0) 4 := slice_fast_direct (zDead := 8) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice2 : Slice h61R h61G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice1 : Slice h61R h61G (subcubeFast 2 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice0 : Slice h61R h61G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h57Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h61R h61G p.1 p.2) h61Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h61R h61G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h61Slice0) (forall_cons (fun _ h => by cases h; exact h61Slice1) (forall_cons (fun _ h => by cases h; exact h61Slice2) (forall_cons (fun _ h => by cases h; exact h61Slice3) (forall_cons (fun _ h => by cases h; exact h61Slice4) (forall_cons (fun _ h => by cases h; exact h61Slice5) (fun _ h => (List.not_mem_nil h).elim)))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h61R h61G c) h61Pools := buildPoolsBT_sound h61SlicesOk
def h61Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G (4 - 1) xs.toFinset) h61Empty := trivial
def h61Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,8],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test4_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Empty 4 h61Block4_0 = true := by decide +kernel
def h61Nodes4 : List NodeSpec := h61Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Check4 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Empty 4 h61Nodes4 = true := h61Test4_0
def h61Bucket4 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 4 xs.toFinset) h61Bucket4 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61EmptyOk h61Check4
def h61Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[1]),([0,1,2,3,4,6],[2,3]),([0,1,2,3,4,7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_0 = true := by decide +kernel
def h61Nodes5 : List NodeSpec := h61Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Check5 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Nodes5 = true := h61Test5_0
def h61Bucket5 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 5 xs.toFinset) h61Bucket5 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket4Ok h61Check5
def h61Block6_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_0 = true := by decide +kernel
def h61Nodes6 : List NodeSpec := h61Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Check6 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Nodes6 = true := h61Test6_0
def h61Bucket6 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 6 xs.toFinset) h61Bucket6 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket5Ok h61Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Bound : Lower h61R h61G 7 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 3,16,24),(VAR 4,4,20),(VAR 5,2,34)]) (by decide +kernel) h61Bucket6Ok (by decide +kernel)
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfee8e8a8eea0c080fee8e8a8eea0c080
def h0Pos : List Nat := [14,21,14,14,25,7,14,25,26,37,21,54,35,7,21,26,54,37,7,7,35,15,51,37,35,54,43,46,60,54,26,29,7,57,27,27,29,45,15,25,7,25,14,57,60,23,53,51,23,60,30,21,43,25,60,26,26,30,58,45,45,57,46,7,58,14,51,14,58,23,7,21,43,39,7,15,14,14,35,7,53,46,21,14,54,51,29,37]
def h0Neg : List Nat := [12,20,13,10,24,3,6,17,10,36,5,22,3,6,17,24,52,5,5,4,33,13,49,33,34,50,11,38,52,38,18,28,11,49,19,11,13,13,11,9,19,13,22,41,28,22,52,19,19,56,28,1,42,28,44,28,22,22,56,41,44,56,42,13,42,4,50,28,50,5,2,28,41,38,1,6,2,44,1,22,49,44,4,42,34,3,17,1]
def h0Mask : Nat := fullMask 88
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xe5cfe4b839ebff85fe76b2,0xe1452088098bff04f654a4),(0xcccccccccccccccccccccccccccccccc,0x3aff7fc795a54d6f7db96d,0x389a554311a54d6f003968),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xdfbeeada4f7571baaf6e6f,0x6aaaa93e47630b82f2e47),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x4a391b7ff61efedc2081dd,0xa2189fcf61af98420811d),(0xffff0000ffff0000ffff0000ffff0000,0x7500b527effa9ef241cd92,0x41809c27a7f506d241c892),(0xffffffff00000000ffffffff00000000,0xb343157c52d8223fd31a00,0x1b23157c5248023bd10200)]
def h0Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(3,0,2),(0,0,3),(2,0,3),(3,0,3),(0,0,4),(3,0,4),(0,1,2),(1,1,2),(3,1,2),(0,1,3),(1,1,3),(3,1,3),(0,1,4),(1,1,4),(3,1,4),(0,1,5),(3,1,5),(0,2,3),(2,2,3),(0,2,4),(2,2,4),(0,2,5),(3,2,5),(0,2,9),(2,2,9),(1,0,35),(2,1,35),(0,3,4),(3,4,5),(2,3,9),(0,4,9),(2,4,9),(0,5,9),(2,5,9),(1,0,28),(2,1,28),(2,2,6),(2,4,6),(2,4,28),(2,5,28),(1,6,28),(1,0,30),(2,0,30),(3,0,30),(0,1,30),(1,1,30),(2,1,30),(1,0,38),(2,1,38),(2,2,38),(2,3,30),(0,5,30),(2,5,30),(2,5,38),(1,6,30),(0,1,65),(1,6,38),(1,6,62),(2,1,47),(3,38,47),(2,2,64),(0,2,67),(2,1,48),(2,2,48),(2,0,74),(2,1,74),(0,2,7),(1,0,77),(0,4,7),(0,5,7),(2,2,80),(2,7,28),(2,5,57),(2,2,63),(2,7,30),(1,38,77),(1,0,86),(3,0,86),(1,1,86),(3,1,86),(2,2,59),(2,7,38),(1,0,79),(2,2,79),(2,2,8),(2,4,8),(1,8,28),(1,8,30),(1,8,38),(1,8,62),(2,0,95),(1,1,95),(0,2,58),(2,0,96),(1,1,96),(2,2,96),(1,1,106),(2,2,44),(1,9,28),(1,9,30),(1,9,38),(1,0,40),(2,1,40),(2,2,41),(1,0,42),(2,1,42),(2,2,42),(1,0,117),(0,1,117),(2,2,43),(1,0,20),(2,2,20),(2,3,10),(2,4,10),(2,4,20),(2,2,125),(1,10,125),(2,5,20),(2,2,128),(1,10,20),(0,2,130),(2,2,22),(2,4,22),(2,2,133),(2,3,133),(2,5,22),(1,10,22),(0,2,137),(2,2,23),(2,2,123),(0,5,23),(2,5,23),(2,2,141),(1,10,141),(2,2,142),(1,10,23),(0,2,146),(3,10,146),(2,2,25),(2,5,25),(1,10,25),(0,2,151),(1,37,38),(3,38,153),(1,10,59),(1,10,38),(0,1,156),(0,5,89),(2,5,157),(2,89,157),(2,2,124),(2,3,11),(2,4,11),(0,5,11),(2,5,11),(1,11,20),(2,2,136),(1,11,22),(1,11,23),(2,2,150),(1,11,25),(1,38,69),(1,11,38),(2,2,162),(2,2,163),(2,3,17),(2,4,12),(2,2,177),(2,3,177),(1,4,17),(2,4,17),(0,5,17),(2,2,182),(2,5,182),(3,0,184),(3,0,181),(1,12,17),(0,3,187),(2,4,19),(2,5,19),(1,12,19),(0,2,191),(1,12,23),(1,12,25),(1,12,30),(2,1,14),(2,4,14),(2,2,197),(2,3,197),(2,5,14),(1,14,17),(2,2,200),(1,14,19),(0,2,203),(1,14,23),(1,14,25),(1,14,30),(1,15,17),(0,3,208),(2,3,208),(0,4,208),(1,15,182),(2,5,209),(2,2,119),(1,15,19),(1,15,20),(1,15,22),(0,5,18),(1,15,28),(0,5,16),(2,5,16),(1,16,17),(0,4,222),(2,2,220),(2,2,221),(1,16,19),(0,2,226),(1,20,161),(1,16,20),(1,16,22),(1,16,28),(0,5,78),(1,17,38),(0,0,233),(2,0,233),(3,38,78),(1,17,232),(3,17,58),(1,38,182),(0,5,87),(2,5,234),(2,87,234),(3,19,58),(1,19,38),(1,20,30),(1,22,30),(0,5,93),(3,32,93),(1,23,28),(1,25,28),(0,5,52),(1,1,251),(2,1,251),(0,5,56)]
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
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,7),some (subcubeFast 0 2,8),some (subcubeFast 0 4,9),some (subcubeFast 0 8,9),some (subcubeFast 0 9,5),some (subcubeFast 0 12,5),some (subcubeFast 0 16,9),some (subcubeFast 0 18,5),some (subcubeFast 0 20,5),some (subcubeFast 0 32,10),some (subcubeFast 0 34,5),some (subcubeFast 0 36,5),some (subcubeFast 0 40,7),some (subcubeFast 0 48,7),some (subcubeFast 1 0,8),some (subcubeFast 1 2,5),some (subcubeFast 1 4,5),some (subcubeFast 1 8,5),some (subcubeFast 1 16,5),some (subcubeFast 1 20,4),some (subcubeFast 1 32,7),some (subcubeFast 1 34,4),some (subcubeFast 1 36,4),some (subcubeFast 1 40,4),some (subcubeFast 1 48,4),some (subcubeFast 2 0,7),some (subcubeFast 2 1,4),some (subcubeFast 2 4,5),some (subcubeFast 2 8,5),some (subcubeFast 2 12,4),some (subcubeFast 2 16,5),some (subcubeFast 2 32,5),some (subcubeFast 2 40,4),some (subcubeFast 2 48,4),some (subcubeFast 4 0,6),some (subcubeFast 4 8,5),some (subcubeFast 4 16,5),some (subcubeFast 4 32,5),some (subcubeFast 4 40,4),some (subcubeFast 4 48,4),some (subcubeFast 8 0,8),some (subcubeFast 8 1,5),some (subcubeFast 8 2,5),some (subcubeFast 8 4,6),some (subcubeFast 8 16,5),some (subcubeFast 8 18,4),some (subcubeFast 8 32,5),some (subcubeFast 16 0,7),some (subcubeFast 16 1,4),some (subcubeFast 16 2,4),some (subcubeFast 16 4,4),some (subcubeFast 16 9,4),some (subcubeFast 16 32,5),some (subcubeFast 24 0,5),some (subcubeFast 24 1,4),some (subcubeFast 32 0,7),some (subcubeFast 32 1,4),some (subcubeFast 32 4,4),some (subcubeFast 32 16,4)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 6 h0SliceList
def h0Specs : List PoolSpec := [(14,[]),(1,[]),(2,[(0,0,1)]),(3,[(0,0,1)]),(6,[(0,0,1)]),(9,[(0,0,1)]),(25,[]),(9,[(3,0,1)]),(0,[]),(2,[]),(9,[(3,0,1),(2,2,9)]),(40,[]),(3,[]),(47,[]),(6,[]),(55,[]),(9,[]),(14,[(0,2,3)]),(1,[(0,2,3)]),(6,[(0,0,1),(0,2,3)]),(9,[(0,0,1),(0,2,3)]),(40,[(0,0,1)]),(25,[(0,2,3)]),(41,[]),(34,[]),(6,[(0,2,3)]),(53,[]),(29,[]),(9,[(0,2,3)]),(20,[(0,2,3)]),(9,[(0,0,1),(0,2,3),(1,6,28)]),(1,[(0,2,3),(1,6,28)]),(2,[(0,0,1),(1,6,28)]),(3,[(0,0,1),(1,6,28)]),(6,[(0,0,1),(0,2,3),(1,6,28)]),(5,[]),(14,[(0,2,4)]),(1,[(0,2,4)]),(3,[(0,0,1),(0,2,4)]),(9,[(0,0,1),(0,2,4)]),(25,[(0,2,4)]),(54,[]),(14,[(0,2,4),(0,3,4)]),(1,[(0,2,4),(0,3,4)]),(40,[(0,0,1),(0,2,4)]),(41,[(0,2,4)]),(2,[(0,0,1),(0,3,4)]),(2,[(0,3,4)]),(34,[(0,3,4)]),(3,[(0,2,4)]),(40,[(0,2,4)]),(9,[(0,2,4),(0,3,4)]),(20,[(0,2,4),(0,3,4)]),(14,[(0,3,4),(0,2,4)]),(3,[(0,0,1),(0,2,4),(1,6,30)]),(40,[(0,0,1),(0,2,4),(1,6,30)]),(2,[(0,3,4),(0,0,1),(1,6,30)]),(2,[(0,0,1),(1,6,30)]),(6,[(0,0,1),(1,6,30)]),(17,[]),(19,[]),(8,[]),(47,[(0,0,1)]),(9,[(0,2,4)]),(20,[(0,2,4)]),(14,[(0,2,4),(0,5,30)]),(2,[(0,5,30)]),(13,[(0,0,1)]),(3,[(0,2,4),(0,5,30)]),(40,[(0,2,4),(0,5,30)]),(6,[(0,5,30)]),(55,[(0,0,1)]),(9,[(0,0,1),(0,2,4),(1,6,62)]),(13,[]),(9,[(0,0,1),(0,2,4),(1,6,30)]),(1,[(0,2,4),(1,6,30)]),(9,[(0,0,1),(2,2,6)]),(3,[(0,0,1),(2,2,6)]),(6,[(0,0,1),(2,2,6)]),(1,[(2,2,6)]),(14,[(0,3,4)]),(2,[(0,3,4),(0,0,1)]),(0,[(2,2,6)]),(40,[(0,0,1),(2,2,6)]),(25,[(0,3,4)]),(0,[(0,3,4)]),(9,[(0,3,4),(0,0,1),(2,2,6)]),(38,[]),(55,[(0,3,4)]),(9,[(0,3,4)]),(16,[]),(35,[]),(1,[(0,3,4)]),(9,[(0,0,1),(0,3,4)]),(14,[(0,3,4),(2,2,38)]),(1,[(0,3,4),(2,2,38)]),(3,[(0,0,1),(2,2,38)]),(6,[(0,0,1),(2,2,38)]),(9,[(0,0,1),(0,3,4),(2,2,38)]),(3,[(2,2,38)]),(6,[(2,2,38)]),(9,[(0,3,4),(2,2,38)]),(20,[(0,3,4),(2,2,38)]),(43,[]),(43,[(0,0,1)]),(20,[(0,3,4)]),(14,[(0,3,4),(2,5,38)]),(2,[(0,3,4),(2,5,38)]),(20,[(0,3,4),(2,2,64)]),(57,[]),(3,[(2,5,38)]),(6,[(2,5,38)]),(46,[]),(23,[]),(9,[(0,0,1),(0,3,4),(1,6,38)]),(1,[(0,3,4),(1,6,38)]),(2,[(0,0,1),(0,3,4),(1,6,38)]),(3,[(0,0,1),(1,6,38)]),(6,[(0,0,1),(1,6,38)]),(2,[(0,3,4),(0,0,1),(3,38,47)]),(9,[(0,0,1),(2,4,6)]),(2,[(0,0,1),(2,4,6)]),(3,[(0,0,1),(2,4,6)]),(1,[(2,4,6)]),(9,[(0,0,1),(2,4,6),(2,2,48)]),(14,[(2,2,48)]),(3,[(0,0,1),(2,4,6),(2,2,48)]),(6,[(0,0,1),(2,2,48)]),(25,[(2,2,48)]),(1,[(2,4,6),(2,2,48)]),(20,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(6,[(1,0,1)]),(9,[(1,0,1)]),(6,[(1,0,1),(0,2,3)]),(0,[(0,2,3)]),(9,[(1,0,1),(0,2,3)]),(40,[(1,0,1)]),(14,[(0,2,3),(0,2,7)]),(9,[(0,2,3),(1,0,1),(0,2,7)]),(3,[(1,0,1),(0,2,7)]),(6,[(0,2,3),(1,0,1),(0,2,7)]),(40,[(1,0,1),(0,2,7)]),(36,[]),(37,[]),(9,[(0,2,3),(1,0,1)]),(14,[(0,5,7)]),(40,[(1,0,1),(0,5,7)]),(25,[(0,5,7)]),(2,[(1,0,1),(0,5,7)]),(55,[(0,2,3)]),(6,[(1,0,1),(0,5,7)]),(47,[(0,2,3)]),(10,[]),(14,[(0,2,3),(2,5,28)]),(2,[(2,5,28)]),(1,[(0,2,3),(2,5,28)]),(3,[(2,5,28)]),(6,[(0,2,3),(2,5,28)]),(47,[(1,0,1)]),(55,[(1,0,1)]),(14,[(0,2,3),(2,7,28)]),(9,[(1,0,1),(0,2,3),(2,7,28)]),(2,[(1,0,1),(2,7,28)]),(3,[(1,0,1),(2,7,28)]),(6,[(1,0,1),(0,2,3),(2,7,28)]),(3,[(1,0,1),(0,2,4)]),(0,[(0,2,4)]),(9,[(1,0,1),(0,2,4)]),(2,[(1,0,1),(2,1,30)]),(14,[(0,2,4),(2,1,30)]),(3,[(1,0,1),(0,2,4),(2,1,30)]),(0,[(0,2,4),(2,1,30)]),(6,[(1,0,1),(2,1,30)]),(9,[(1,0,1),(0,2,4),(2,1,30)]),(14,[(0,2,4),(0,2,7)]),(9,[(0,2,4),(1,0,1),(0,2,7)]),(3,[(0,2,4),(1,0,1),(0,2,7)]),(6,[(1,0,1),(0,2,7)]),(47,[(1,0,1),(0,2,7)]),(9,[(0,2,4),(1,0,1)]),(55,[(0,2,4)]),(3,[(1,0,1),(0,5,7)]),(14,[(0,2,4),(2,5,30)]),(2,[(2,5,30)]),(1,[(0,2,4),(2,5,30)]),(40,[(0,2,4),(2,5,30)]),(3,[(0,2,4),(2,5,30)]),(6,[(2,5,30)]),(56,[]),(14,[(0,2,4),(2,7,30)]),(9,[(1,0,1),(0,2,4),(2,7,30)]),(2,[(1,0,1),(2,7,30)]),(3,[(1,0,1),(0,2,4),(2,7,30)]),(6,[(1,0,1),(2,7,30)]),(14,[(0,2,7)]),(9,[(1,0,1),(0,2,7)]),(2,[(0,3,4),(1,0,1)]),(25,[(0,2,7)]),(9,[(0,3,4),(1,0,1),(0,2,7)]),(2,[(0,3,4),(1,0,1),(1,38,77)]),(0,[(0,3,4),(1,38,77)]),(3,[(1,0,1),(0,2,7),(1,38,77)]),(1,[(0,3,4),(1,38,77)]),(6,[(1,0,1),(0,2,7),(1,38,77)]),(2,[(1,0,1),(0,3,4)]),(9,[(1,0,1),(0,3,4)]),(14,[(0,3,4),(2,1,38)]),(2,[(1,0,1),(0,3,4),(2,1,38)]),(0,[(0,3,4),(2,1,38)]),(3,[(1,0,1),(2,1,38)]),(6,[(1,0,1),(2,1,38)]),(9,[(1,0,1),(0,3,4),(2,1,38)]),(0,[(0,3,4),(2,2,38)]),(3,[(1,0,1),(2,2,38)]),(6,[(1,0,1),(2,2,38)]),(9,[(1,0,1),(0,3,4),(2,2,38)]),(9,[(0,3,4),(2,2,38),(1,0,1)]),(43,[(1,0,1)]),(9,[(0,3,4),(1,0,1)]),(1,[(0,3,4),(2,5,38)]),(40,[(2,2,64)]),(3,[(2,5,38),(2,2,64)]),(47,[(2,2,64)]),(6,[(2,5,38),(2,2,64)]),(14,[(0,3,4),(2,7,38)]),(9,[(1,0,1),(0,3,4),(2,7,38)]),(2,[(1,0,1),(0,3,4),(2,7,38)]),(3,[(1,0,1),(2,7,38)]),(6,[(1,0,1),(2,7,38)]),(14,[(0,4,7)]),(9,[(1,0,1),(0,4,7)]),(2,[(1,0,1),(0,4,7)]),(3,[(1,0,1),(0,4,7)]),(14,[(0,4,7),(2,2,79)]),(9,[(1,0,1),(0,4,7),(2,2,79)]),(1,[(2,2,79)]),(3,[(1,0,1),(0,4,7),(2,2,79)]),(0,[(2,2,79)]),(6,[(1,0,1),(2,2,79)]),(9,[(1,0,1),(2,2,80)]),(2,[(2,0,1)]),(3,[(2,0,1)]),(6,[(2,0,1)]),(9,[(2,0,1)]),(6,[(2,0,1),(0,2,3)]),(9,[(2,0,1),(0,2,3)]),(2,[(2,0,1),(1,0,28)]),(3,[(2,0,1),(1,0,28)]),(1,[(0,2,3),(1,0,28)]),(6,[(2,0,1),(0,2,3),(1,0,28)]),(9,[(2,0,1),(0,2,3),(1,0,28)]),(40,[(2,0,1)]),(42,[]),(45,[]),(47,[(2,0,1)]),(55,[(2,0,1)]),(9,[(2,0,1),(0,2,3),(1,8,28)]),(2,[(2,0,1),(1,8,28)]),(3,[(2,0,1),(1,8,28)]),(6,[(2,0,1),(0,2,3),(1,8,28)]),(3,[(2,0,1),(0,2,4)]),(9,[(2,0,1),(0,2,4)]),(40,[(2,0,1),(0,2,4)]),(2,[(2,0,1),(0,3,4)]),(42,[(0,2,4)]),(1,[(0,2,4),(0,5,30)]),(13,[(2,0,1)]),(9,[(2,0,1),(0,2,4),(1,8,62)]),(26,[]),(9,[(2,0,1),(0,2,4),(1,8,30)]),(2,[(2,0,1),(1,8,30)]),(3,[(2,0,1),(0,2,4),(1,8,30)]),(6,[(2,0,1),(1,8,30)]),(9,[(2,0,1),(2,2,8)]),(3,[(2,0,1),(2,2,8)]),(6,[(2,0,1),(2,2,8)]),(2,[(0,3,4),(2,0,1)]),(0,[(2,2,8)]),(40,[(2,0,1),(2,2,8)]),(25,[(2,2,8)]),(9,[(2,0,1),(0,3,4)]),(1,[(0,3,4),(1,0,38)]),(2,[(2,0,1),(0,3,4),(1,0,38)]),(3,[(2,0,1),(1,0,38)]),(6,[(2,0,1),(1,0,38)]),(9,[(2,0,1),(0,3,4),(1,0,38)]),(3,[(2,0,1),(2,2,38)]),(6,[(2,0,1),(2,2,38)]),(9,[(2,0,1),(0,3,4),(2,2,38)]),(43,[(2,0,1)]),(9,[(0,3,4),(2,2,64)]),(9,[(2,0,1),(0,3,4),(1,8,38)]),(2,[(2,0,1),(0,3,4),(1,8,38)]),(3,[(2,0,1),(1,8,38)]),(6,[(2,0,1),(1,8,38)]),(9,[(2,0,1),(2,4,8)]),(2,[(2,0,1),(2,4,8)]),(3,[(2,0,1),(2,4,8)]),(14,[(2,2,96)]),(9,[(2,0,1),(2,4,8),(2,2,96)]),(3,[(2,0,1),(2,4,8),(2,2,96)]),(6,[(2,0,1),(2,2,96)]),(1,[(2,2,96)]),(2,[(3,0,1)]),(3,[(3,0,1)]),(6,[(3,0,1)]),(6,[(3,0,1),(0,2,3)]),(9,[(3,0,1),(0,2,3)]),(40,[(3,0,1)]),(9,[(0,2,3),(3,0,1)]),(14,[(2,5,9)]),(40,[(3,0,1),(2,5,9)]),(1,[(2,5,9)]),(2,[(3,0,1),(2,5,9)]),(6,[(3,0,1),(2,5,9)]),(31,[]),(14,[(0,2,3),(1,9,28)]),(1,[(0,2,3),(1,9,28)]),(9,[(3,0,1),(0,2,3),(1,9,28)]),(2,[(3,0,1),(1,9,28)]),(3,[(3,0,1),(1,9,28)]),(6,[(3,0,1),(0,2,3),(1,9,28)]),(15,[]),(3,[(3,0,1),(0,2,4)]),(9,[(3,0,1),(0,2,4)]),(47,[(3,0,1)]),(9,[(0,2,4),(3,0,1)]),(3,[(3,0,1),(2,5,9)]),(55,[(3,0,1)]),(14,[(0,2,4),(1,9,30)]),(1,[(0,2,4),(1,9,30)]),(9,[(3,0,1),(0,2,4),(1,9,30)]),(2,[(3,0,1),(1,9,30)]),(3,[(3,0,1),(0,2,4),(1,9,30)]),(6,[(3,0,1),(1,9,30)]),(48,[]),(14,[(0,2,9)]),(1,[(0,2,9)]),(9,[(3,0,1),(0,2,9)]),(3,[(3,0,1),(0,2,9)]),(6,[(3,0,1),(0,2,9)]),(14,[(2,2,9)]),(1,[(2,2,9)]),(3,[(3,0,1),(2,2,9)]),(6,[(3,0,1),(2,2,9)]),(2,[(3,0,1),(0,3,4)]),(40,[(3,0,1),(2,2,9)]),(27,[]),(9,[(3,0,1),(0,3,4)]),(3,[(3,0,1),(2,2,38)]),(6,[(3,0,1),(2,2,38)]),(9,[(3,0,1),(0,3,4),(2,2,38)]),(55,[(0,3,4),(2,2,38)]),(43,[(3,0,1)]),(9,[(0,3,4),(3,0,1)]),(14,[(0,3,4),(1,9,38)]),(1,[(0,3,4),(1,9,38)]),(9,[(3,0,1),(0,3,4),(1,9,38)]),(2,[(3,0,1),(0,3,4),(1,9,38)]),(3,[(3,0,1),(1,9,38)]),(6,[(3,0,1),(1,9,38)]),(14,[(2,3,9)]),(1,[(2,3,9)]),(2,[(3,0,1),(2,3,9)]),(6,[(3,0,1),(2,3,9)]),(9,[(3,0,1),(2,3,9)]),(4,[]),(14,[(0,4,9)]),(1,[(0,4,9)]),(9,[(3,0,1),(0,4,9)]),(2,[(3,0,1),(0,4,9)]),(3,[(3,0,1),(0,4,9)]),(14,[(0,4,9),(2,2,41)]),(1,[(0,4,9),(2,2,41)]),(9,[(3,0,1),(0,4,9),(2,2,41)]),(3,[(3,0,1),(0,4,9),(2,2,41)]),(6,[(3,0,1),(2,2,41)]),(14,[(2,4,9)]),(1,[(2,4,9)]),(9,[(3,0,1),(2,4,9)]),(2,[(3,0,1),(2,4,9)]),(3,[(3,0,1),(2,4,9)]),(14,[(2,4,9),(2,2,42)]),(1,[(2,4,9),(2,2,42)]),(9,[(3,0,1),(2,4,9),(2,2,42)]),(3,[(3,0,1),(2,4,9),(2,2,42)]),(0,[(2,2,42)]),(6,[(3,0,1),(2,2,42)]),(25,[(2,2,42)]),(30,[]),(9,[(3,0,1),(2,2,43)]),(9,[(3,0,1),(2,2,44)]),(3,[(0,0,2)]),(6,[(0,0,2)]),(9,[(0,0,2)]),(14,[(0,1,3)]),(2,[(0,1,3)]),(6,[(0,0,2),(0,1,3)]),(9,[(0,0,2),(0,1,3)]),(40,[(0,0,2)]),(1,[(0,0,2)]),(25,[(0,0,2)]),(6,[(0,1,3)]),(2,[(0,1,3),(2,4,20)]),(14,[(0,1,3),(2,4,20)]),(1,[(2,4,20)]),(47,[(0,0,2)]),(3,[(0,0,2),(2,4,20)]),(3,[(2,4,20)]),(9,[(0,1,3),(2,4,20)]),(20,[(0,1,3),(2,4,20)]),(55,[(0,0,2)]),(3,[(0,0,2),(2,4,20),(1,10,125)]),(9,[(0,1,3)]),(20,[(0,1,3)]),(2,[(0,1,3),(2,5,20)]),(14,[(0,1,3),(2,5,20)]),(1,[(2,5,20)]),(3,[(2,5,20)]),(6,[(0,1,3),(2,5,20)]),(21,[]),(9,[(0,0,2),(0,1,3),(1,10,20)]),(2,[(0,1,3),(1,10,20)]),(3,[(0,0,2),(1,10,20)]),(6,[(0,0,2),(0,1,3),(1,10,20)]),(1,[(0,0,2),(1,10,20)]),(14,[(3,1,3)]),(2,[(3,1,3)]),(6,[(0,0,2),(3,1,3)]),(9,[(0,0,2),(3,1,3)]),(6,[(3,1,3)]),(2,[(3,1,3),(2,4,22)]),(14,[(3,1,3),(2,4,22)]),(3,[(0,0,2),(2,4,22)]),(25,[(2,4,22)]),(3,[(2,4,22)]),(9,[(3,1,3),(2,4,22)]),(20,[(3,1,3),(2,4,22)]),(7,[]),(9,[(3,1,3)]),(20,[(3,1,3)]),(9,[(0,0,2),(3,1,3),(1,10,22)]),(2,[(3,1,3),(1,10,22)]),(3,[(0,0,2),(1,10,22)]),(6,[(0,0,2),(3,1,3),(1,10,22)]),(14,[(0,1,4)]),(2,[(0,1,4)]),(3,[(0,0,2),(0,1,4)]),(9,[(0,0,2),(0,1,4)]),(3,[(0,1,4)]),(9,[(0,1,4),(0,0,2),(2,3,10)]),(2,[(0,1,4),(2,3,10)]),(6,[(0,0,2),(2,3,10)]),(0,[(2,3,10)]),(3,[(0,1,4),(0,0,2)]),(1,[(0,0,2),(2,3,10)]),(40,[(0,1,4)]),(2,[(2,3,10)]),(9,[(0,0,2),(2,3,10)]),(9,[(0,1,4)]),(20,[(0,1,4)]),(2,[(0,1,4),(0,5,23)]),(14,[(0,1,4),(0,5,23)]),(1,[(0,5,23)]),(3,[(0,1,4),(0,5,23)]),(40,[(0,1,4),(0,5,23)]),(6,[(0,5,23)]),(9,[(0,0,2),(0,1,4),(1,10,141)]),(2,[(0,1,4),(2,5,23)]),(14,[(0,1,4),(2,5,23)]),(1,[(2,5,23)]),(3,[(0,1,4),(2,5,23)]),(40,[(0,1,4),(2,5,23)]),(6,[(2,5,23)]),(9,[(0,0,2),(0,1,4),(1,10,23)]),(2,[(0,1,4),(1,10,23)]),(3,[(0,0,2),(0,1,4),(1,10,23)]),(6,[(0,0,2),(1,10,23)]),(1,[(0,0,2),(1,10,23)]),(2,[(0,1,4),(1,10,23),(3,10,146)]),(6,[(0,0,2),(1,10,23),(3,10,146)]),(14,[(3,1,4)]),(2,[(3,1,4)]),(3,[(0,0,2),(3,1,4)]),(9,[(0,0,2),(3,1,4)]),(3,[(3,1,4)]),(9,[(3,1,4),(0,0,2),(2,3,10)]),(2,[(3,1,4),(2,3,10)]),(3,[(3,1,4),(0,0,2)]),(40,[(3,1,4)]),(9,[(3,1,4)]),(20,[(3,1,4)]),(9,[(0,0,2),(3,1,4),(1,10,25)]),(2,[(3,1,4),(1,10,25)]),(3,[(0,0,2),(3,1,4),(1,10,25)]),(6,[(0,0,2),(1,10,25)]),(9,[(3,0,1),(2,2,9),(2,1,35)]),(2,[(1,1,4),(3,0,1)]),(14,[(1,1,4)]),(6,[(3,0,1),(2,2,9),(2,1,35)]),(20,[(1,1,4)]),(0,[(2,1,35)]),(3,[(3,0,1),(2,2,9),(2,1,35)]),(32,[]),(28,[]),(9,[(0,0,2),(0,3,4)]),(2,[(0,3,4),(2,1,38)]),(3,[(0,0,2),(2,1,38)]),(6,[(0,0,2),(2,1,38)]),(3,[(2,1,38)]),(6,[(2,1,38)]),(9,[(0,3,4),(2,1,38)]),(20,[(0,3,4),(2,1,38)]),(3,[(0,0,2),(2,1,38),(1,10,59)]),(9,[(0,0,2),(0,3,4),(1,10,38)]),(2,[(0,3,4),(1,10,38)]),(3,[(0,0,2),(1,10,38)]),(6,[(0,0,2),(1,10,38)]),(3,[(0,0,2),(1,10,38),(0,1,156)]),(14,[(0,3,4),(0,1,156),(2,5,157)]),(9,[(0,0,2),(2,4,10)]),(2,[(2,4,10)]),(3,[(0,0,2),(2,4,10)]),(9,[(0,0,2),(2,4,10),(2,2,124)]),(3,[(3,0,2)]),(6,[(3,0,2)]),(9,[(3,0,2)]),(1,[(3,0,2)]),(0,[(0,1,3)]),(6,[(3,0,2),(0,1,3)]),(9,[(3,0,2),(0,1,3)]),(40,[(3,0,2)]),(25,[(3,0,2)]),(9,[(0,1,3),(3,0,2)]),(14,[(2,5,11)]),(40,[(3,0,2),(2,5,11)]),(3,[(3,0,2),(2,5,11)]),(2,[(2,5,11)]),(6,[(3,0,2),(2,5,11)]),(47,[(0,1,3)]),(55,[(0,1,3)]),(55,[(3,0,2)]),(47,[(3,0,2)]),(14,[(0,1,3),(1,11,20)]),(1,[(3,0,2),(1,11,20)]),(2,[(0,1,3),(1,11,20)]),(9,[(3,0,2),(0,1,3),(1,11,20)]),(3,[(3,0,2),(1,11,20)]),(6,[(3,0,2),(0,1,3),(1,11,20)]),(6,[(3,0,2),(3,1,3)]),(0,[(3,1,3)]),(9,[(3,0,2),(3,1,3)]),(9,[(3,1,3),(3,0,2)]),(1,[(3,0,2),(2,5,11)]),(47,[(3,1,3)]),(55,[(3,1,3)]),(2,[(3,1,3),(2,5,22)]),(25,[(2,5,22)]),(3,[(2,5,22)]),(6,[(3,1,3),(2,5,22)]),(14,[(3,1,3),(1,11,22)]),(2,[(3,1,3),(1,11,22)]),(9,[(3,0,2),(3,1,3),(1,11,22)]),(3,[(3,0,2),(1,11,22)]),(6,[(3,0,2),(3,1,3),(1,11,22)]),(0,[(0,1,4)]),(3,[(3,0,2),(0,1,4)]),(9,[(3,0,2),(0,1,4)]),(9,[(0,1,4),(3,0,2)]),(55,[(0,1,4)]),(14,[(0,1,4),(1,11,23)]),(1,[(3,0,2),(1,11,23)]),(2,[(0,1,4),(1,11,23)]),(9,[(3,0,2),(0,1,4),(1,11,23)]),(3,[(3,0,2),(0,1,4),(1,11,23)]),(6,[(3,0,2),(1,11,23)]),(3,[(3,0,2),(3,1,4)]),(0,[(3,1,4)]),(9,[(3,0,2),(3,1,4)]),(9,[(3,1,4),(3,0,2)]),(55,[(3,1,4)]),(2,[(3,1,4),(2,5,25)]),(25,[(2,5,25)]),(40,[(3,1,4),(2,5,25)]),(3,[(3,1,4),(2,5,25)]),(6,[(2,5,25)]),(14,[(3,1,4),(1,11,25)]),(2,[(3,1,4),(1,11,25)]),(9,[(3,0,2),(3,1,4),(1,11,25)]),(3,[(3,0,2),(3,1,4),(1,11,25)]),(6,[(3,0,2),(1,11,25)]),(14,[(1,1,95)]),(20,[(1,1,95)]),(9,[(2,0,1),(2,2,8),(1,1,95)]),(22,[]),(14,[(2,1,47)]),(9,[(0,0,1),(2,2,6),(2,1,47)]),(3,[(0,0,1),(2,2,6),(2,1,47)]),(6,[(0,0,1),(2,2,6),(2,1,47)]),(0,[(0,3,4),(1,38,69)]),(33,[]),(20,[(2,1,47)]),(9,[(3,0,2),(0,3,4)]),(3,[(3,0,2),(2,1,38)]),(6,[(3,0,2),(2,1,38)]),(3,[(3,0,2),(2,2,38)]),(6,[(3,0,2),(2,2,38)]),(9,[(3,0,2),(0,3,4),(2,2,38)]),(9,[(0,3,4),(3,0,2)]),(14,[(0,3,4),(1,11,38)]),(2,[(0,3,4),(1,11,38)]),(9,[(3,0,2),(0,3,4),(1,11,38)]),(3,[(3,0,2),(1,11,38)]),(6,[(3,0,2),(1,11,38)]),(14,[(2,3,11)]),(2,[(2,3,11)]),(6,[(3,0,2),(2,3,11)]),(9,[(3,0,2),(2,3,11)]),(2,[(3,0,30)]),(3,[(0,2,4),(3,0,30)]),(6,[(3,0,30)]),(9,[(0,2,4),(3,0,30)]),(14,[(2,4,11)]),(2,[(2,4,11)]),(9,[(3,0,2),(2,4,11)]),(3,[(3,0,2),(2,4,11)]),(2,[(0,0,3)]),(6,[(0,0,3)]),(9,[(0,0,3)]),(14,[(0,1,2)]),(3,[(0,1,2)]),(6,[(0,0,3),(0,1,2)]),(9,[(0,0,3),(0,1,2)]),(1,[(0,0,3)]),(25,[(0,0,3)]),(6,[(0,1,2)]),(3,[(0,1,2),(2,4,12)]),(6,[(0,1,2),(0,0,3)]),(0,[(2,4,12)]),(2,[(0,0,3),(2,4,12)]),(1,[(0,0,3),(2,4,12)]),(47,[(0,1,2)]),(3,[(2,4,12)]),(40,[(0,1,2)]),(18,[]),(9,[(0,0,3),(2,4,12)]),(9,[(0,1,2)]),(55,[(0,1,2)]),(14,[(0,1,2),(2,4,17)]),(51,[]),(20,[(0,1,2)]),(3,[(0,1,2),(0,5,17)]),(14,[(0,1,2),(0,5,17)]),(1,[(0,5,17)]),(2,[(0,5,17)]),(6,[(0,1,2),(0,5,17)]),(47,[(0,0,3)]),(55,[(0,0,3)]),(3,[(0,1,2),(0,5,17),(2,5,182)]),(1,[(0,5,17),(2,5,182)]),(2,[(0,5,17),(2,5,182)]),(6,[(0,1,2),(0,5,17),(2,5,182)]),(2,[(0,0,3),(1,12,17)]),(9,[(0,0,3),(0,1,2),(1,12,17)]),(3,[(0,1,2),(1,12,17)]),(6,[(0,0,3),(0,1,2),(1,12,17)]),(1,[(0,0,3),(1,12,17)]),(14,[(3,1,2)]),(3,[(3,1,2)]),(6,[(0,0,3),(3,1,2)]),(9,[(0,0,3),(3,1,2)]),(6,[(3,1,2)]),(9,[(3,1,2)]),(20,[(3,1,2)]),(2,[(0,0,3),(1,12,19)]),(9,[(0,0,3),(3,1,2),(1,12,19)]),(3,[(3,1,2),(1,12,19)]),(6,[(0,0,3),(3,1,2),(1,12,19)]),(2,[(0,0,3),(0,1,4)]),(9,[(0,0,3),(0,1,4)]),(2,[(0,0,3),(0,1,4),(1,12,23)]),(9,[(0,0,3),(0,1,4),(1,12,23)]),(3,[(0,1,4),(1,12,23)]),(6,[(0,0,3),(1,12,23)]),(1,[(0,0,3),(1,12,23)]),(2,[(0,0,3),(3,1,4)]),(9,[(0,0,3),(3,1,4)]),(3,[(3,1,4),(2,2,25)]),(14,[(3,1,4),(2,2,25)]),(25,[(2,2,25)]),(6,[(0,0,3),(2,2,25)]),(6,[(2,2,25)]),(9,[(3,1,4),(2,2,25)]),(20,[(3,1,4),(2,2,25)]),(2,[(0,0,3),(3,1,4),(1,12,25)]),(9,[(0,0,3),(3,1,4),(1,12,25)]),(3,[(3,1,4),(1,12,25)]),(6,[(0,0,3),(1,12,25)]),(9,[(3,0,1),(2,3,9),(2,1,40)]),(3,[(1,1,4),(3,0,1)]),(6,[(3,0,1),(2,3,9),(2,1,40)]),(3,[(3,1,2),(1,12,19),(0,2,191)]),(40,[(3,1,2)]),(1,[(0,0,3),(0,2,191)]),(9,[(0,0,3),(0,2,4)]),(2,[(0,0,3),(1,12,30)]),(9,[(0,0,3),(0,2,4),(1,12,30)]),(3,[(0,2,4),(1,12,30)]),(6,[(0,0,3),(1,12,30)]),(9,[(3,0,2),(2,3,11),(2,2,162)]),(14,[(2,2,4)]),(3,[(2,2,4),(3,0,2)]),(6,[(3,0,2),(2,3,11),(2,2,162)]),(20,[(2,2,4)]),(14,[(2,2,177)]),(9,[(0,0,3),(2,4,12),(2,2,177)]),(3,[(2,4,12),(2,2,177)]),(6,[(0,0,3),(2,2,177)]),(2,[(3,0,3)]),(6,[(3,0,3)]),(9,[(3,0,3)]),(1,[(3,0,3)]),(0,[(0,1,2)]),(6,[(3,0,3),(0,1,2)]),(9,[(3,0,3),(0,1,2)]),(25,[(3,0,3)]),(6,[(0,1,2),(3,0,3)]),(14,[(2,4,14)]),(2,[(3,0,3),(2,4,14)]),(1,[(3,0,3),(2,4,14)]),(3,[(0,1,2),(2,4,14)]),(3,[(2,4,14)]),(44,[]),(9,[(3,0,3),(2,4,14)]),(3,[(0,1,2),(2,4,17)]),(40,[(0,1,2),(2,4,17)]),(9,[(0,1,2),(3,0,3)]),(14,[(2,5,14)]),(2,[(3,0,3),(2,5,14)]),(3,[(2,5,14)]),(6,[(3,0,3),(2,5,14)]),(40,[(0,1,2),(0,5,17)]),(47,[(3,0,3)]),(55,[(3,0,3)]),(14,[(0,1,2),(1,14,17)]),(1,[(3,0,3),(1,14,17)]),(2,[(3,0,3),(1,14,17)]),(3,[(0,1,2),(1,14,17)]),(9,[(3,0,3),(0,1,2),(1,14,17)]),(6,[(3,0,3),(0,1,2),(1,14,17)]),(6,[(3,0,3),(3,1,2)]),(0,[(3,1,2)]),(9,[(3,0,3),(3,1,2)]),(9,[(3,1,2),(3,0,3)]),(1,[(3,0,3),(2,5,14)]),(55,[(3,1,2)]),(47,[(3,1,2)]),(3,[(3,1,2),(2,5,19)]),(40,[(3,1,2),(2,5,19)]),(25,[(2,5,19)]),(2,[(2,5,19)]),(6,[(3,1,2),(2,5,19)]),(14,[(3,1,2),(1,14,19)]),(2,[(3,0,3),(1,14,19)]),(3,[(3,1,2),(1,14,19)]),(9,[(3,0,3),(3,1,2),(1,14,19)]),(6,[(3,0,3),(3,1,2),(1,14,19)]),(2,[(3,0,3),(0,1,4)]),(9,[(3,0,3),(0,1,4)]),(14,[(2,2,123)]),(6,[(0,0,2),(2,3,10),(2,2,123)]),(9,[(0,0,2),(2,3,10),(2,2,123)]),(43,[(0,1,4)]),(9,[(0,1,4),(3,0,3)]),(14,[(0,1,4),(1,14,23)]),(1,[(3,0,3),(1,14,23)]),(2,[(3,0,3),(0,1,4),(1,14,23)]),(3,[(0,1,4),(1,14,23)]),(9,[(3,0,3),(0,1,4),(1,14,23)]),(6,[(3,0,3),(1,14,23)]),(2,[(3,0,3),(3,1,4)]),(9,[(3,0,3),(3,1,4)]),(39,[]),(43,[(3,1,4)]),(40,[(3,1,4),(2,2,25)]),(6,[(3,0,3),(2,2,25)]),(9,[(3,1,4),(3,0,3)]),(14,[(3,1,4),(1,14,25)]),(2,[(3,0,3),(3,1,4),(1,14,25)]),(3,[(3,1,4),(1,14,25)]),(9,[(3,0,3),(3,1,4),(1,14,25)]),(6,[(3,0,3),(1,14,25)]),(3,[(2,1,14)]),(14,[(2,1,14)]),(2,[(3,0,3),(2,1,14)]),(9,[(3,0,3),(2,1,14)]),(6,[(3,0,3),(2,1,14)]),(3,[(0,2,4),(2,1,14)]),(1,[(3,0,3),(0,2,203)]),(3,[(3,1,2),(1,14,19),(0,2,203)]),(9,[(3,0,3),(0,2,4)]),(3,[(0,2,4),(2,1,30)]),(2,[(3,0,3),(2,1,30)]),(6,[(3,0,3),(2,1,30)]),(40,[(0,2,4),(2,1,30)]),(2,[(2,1,30)]),(6,[(2,1,30)]),(9,[(0,2,4),(2,1,30)]),(9,[(0,2,4),(3,0,3)]),(14,[(0,2,4),(1,14,30)]),(2,[(3,0,3),(1,14,30)]),(3,[(0,2,4),(1,14,30)]),(9,[(3,0,3),(0,2,4),(1,14,30)]),(6,[(3,0,3),(1,14,30)]),(2,[(0,1,5),(2,3,10)]),(0,[(0,1,5)]),(2,[(0,1,5)]),(3,[(0,1,5)]),(3,[(0,1,5),(0,0,2)]),(40,[(0,1,5)]),(14,[(0,1,5)]),(47,[(0,1,5)]),(6,[(0,1,5)]),(43,[(0,1,5)]),(2,[(3,1,5),(2,3,10)]),(0,[(3,1,5)]),(2,[(3,1,5)]),(3,[(3,1,5)]),(3,[(3,1,5),(0,0,2)]),(40,[(3,1,5)]),(14,[(3,1,5)]),(47,[(3,1,5)]),(6,[(3,1,5)]),(43,[(3,1,5)]),(14,[(2,4,14),(2,2,197)]),(0,[(2,2,197)]),(3,[(2,4,14),(2,2,197)]),(9,[(3,0,3),(2,4,14),(2,2,197)]),(6,[(3,0,3),(2,2,197)]),(9,[(3,0,3),(2,2,200)]),(2,[(0,0,4)]),(3,[(0,0,4)]),(9,[(0,0,4)]),(3,[(0,0,4),(0,1,2)]),(9,[(0,0,4),(0,1,2)]),(1,[(0,0,4)]),(25,[(0,0,4)]),(40,[(0,0,4)]),(14,[(0,1,2),(2,3,17)]),(55,[(0,0,4)]),(9,[(0,0,4),(0,1,2),(1,15,182)]),(2,[(0,0,4),(1,15,17)]),(3,[(0,0,4),(0,1,2),(1,15,17)]),(9,[(0,0,4),(0,1,2),(1,15,17)]),(6,[(0,1,2),(1,15,17)]),(1,[(0,0,4),(1,15,17)]),(47,[(0,1,117)]),(2,[(3,0,1),(2,4,9),(0,1,117)]),(13,[(3,0,1),(2,2,42)]),(3,[(0,0,4),(3,1,2)]),(9,[(0,0,4),(3,1,2)]),(2,[(0,0,4),(1,15,19)]),(3,[(0,0,4),(3,1,2),(1,15,19)]),(9,[(0,0,4),(3,1,2),(1,15,19)]),(6,[(3,1,2),(1,15,19)]),(2,[(0,0,4),(0,1,3)]),(9,[(0,0,4),(0,1,3)]),(2,[(0,1,3),(2,4,11)]),(0,[(2,2,163)]),(3,[(3,0,2),(2,4,11),(2,2,163)]),(43,[(2,4,11)]),(6,[(0,1,3),(3,0,2)]),(9,[(3,0,2),(2,4,11),(2,2,163)]),(6,[(0,1,3),(2,2,20)]),(14,[(0,1,3),(2,2,20)]),(1,[(2,2,20)]),(3,[(0,0,4),(2,2,20)]),(3,[(2,2,20)]),(9,[(0,1,3),(2,2,20)]),(20,[(0,1,3),(2,2,20)]),(43,[(0,0,4)]),(2,[(0,0,4),(0,1,3),(1,15,20)]),(3,[(0,0,4),(1,15,20)]),(9,[(0,0,4),(0,1,3),(1,15,20)]),(6,[(0,1,3),(1,15,20)]),(1,[(0,0,4),(1,15,20)]),(2,[(0,0,4),(3,1,3)]),(9,[(0,0,4),(3,1,3)]),(2,[(3,1,3),(2,4,11)]),(6,[(3,1,3),(3,0,2)]),(6,[(3,1,3),(2,2,22)]),(14,[(3,1,3),(2,2,22)]),(25,[(2,2,22)]),(3,[(0,0,4),(2,2,22)]),(9,[(0,0,4),(3,1,3),(2,2,22)]),(3,[(2,2,22)]),(9,[(3,1,3),(2,2,22)]),(20,[(3,1,3),(2,2,22)]),(2,[(0,0,4),(3,1,3),(1,15,22)]),(3,[(0,0,4),(1,15,22)]),(9,[(0,0,4),(3,1,3),(1,15,22)]),(6,[(3,1,3),(1,15,22)]),(9,[(3,0,1),(2,4,9),(2,1,42)]),(2,[(3,0,1),(2,4,9),(2,1,42)]),(14,[(1,1,2)]),(6,[(1,1,2),(3,0,1)]),(20,[(1,1,2)]),(3,[(3,0,1),(2,4,9),(2,1,42)]),(14,[(1,1,2),(0,5,18)]),(6,[(3,0,1),(1,1,2),(0,5,18)]),(25,[(0,5,18)]),(28,[(0,5,18)]),(14,[(1,1,3)]),(6,[(1,1,3),(3,0,1)]),(20,[(1,1,3)]),(6,[(3,0,1),(2,2,42),(2,2,119)]),(9,[(0,0,4),(0,2,3)]),(6,[(0,2,3),(2,1,28)]),(14,[(0,2,3),(2,1,28)]),(2,[(0,0,4),(2,1,28)]),(3,[(0,0,4),(2,1,28)]),(2,[(2,1,28)]),(3,[(2,1,28)]),(9,[(0,2,3),(2,1,28)]),(20,[(0,2,3),(2,1,28)]),(2,[(0,0,4),(1,15,28)]),(3,[(0,0,4),(1,15,28)]),(9,[(0,0,4),(0,2,3),(1,15,28)]),(6,[(0,2,3),(1,15,28)]),(14,[(2,2,3)]),(6,[(2,2,3),(3,0,2)]),(20,[(2,2,3)]),(2,[(3,0,4)]),(3,[(3,0,4)]),(9,[(3,0,4)]),(1,[(3,0,4)]),(3,[(3,0,4),(0,1,2)]),(9,[(3,0,4),(0,1,2)]),(25,[(3,0,4)]),(40,[(3,0,4)]),(6,[(0,1,2),(2,3,17)]),(0,[(0,1,2),(2,4,17)]),(2,[(3,0,4),(2,4,17)]),(1,[(3,0,4),(2,4,17)]),(3,[(3,0,4),(0,1,2),(2,4,17)]),(9,[(3,0,4),(0,1,2),(2,4,17)]),(9,[(0,1,2),(3,0,4)]),(14,[(0,5,16)]),(2,[(3,0,4),(0,5,16)]),(40,[(3,0,4),(0,5,16)]),(3,[(3,0,4),(0,5,16)]),(6,[(0,5,16)]),(24,[]),(14,[(2,5,16)]),(2,[(3,0,4),(2,5,16)]),(40,[(3,0,4),(2,5,16)]),(3,[(3,0,4),(2,5,16)]),(6,[(2,5,16)]),(52,[]),(55,[(3,0,4)]),(14,[(0,1,2),(1,16,17)]),(1,[(3,0,4),(1,16,17)]),(2,[(3,0,4),(1,16,17)]),(3,[(3,0,4),(0,1,2),(1,16,17)]),(6,[(0,1,2),(1,16,17)]),(9,[(3,0,4),(0,1,2),(1,16,17)]),(6,[(0,1,2),(3,0,181)]),(2,[(2,4,17),(3,0,181)]),(1,[(2,4,17),(3,0,181)]),(25,[(3,0,181)]),(3,[(0,1,2),(2,4,17),(3,0,181)]),(9,[(0,1,2),(2,4,17),(3,0,181)]),(3,[(3,0,4),(3,1,2)]),(9,[(3,0,4),(3,1,2)]),(9,[(3,1,2),(3,0,4)]),(1,[(3,0,4),(0,5,16)]),(49,[]),(1,[(3,0,4),(2,5,16)]),(14,[(3,1,2),(1,16,19)]),(2,[(3,0,4),(1,16,19)]),(3,[(3,0,4),(3,1,2),(1,16,19)]),(6,[(3,1,2),(1,16,19)]),(9,[(3,0,4),(3,1,2),(1,16,19)]),(2,[(3,0,4),(0,1,3)]),(9,[(3,0,4),(0,1,3)]),(2,[(0,1,3),(2,4,10)]),(14,[(2,2,124)]),(3,[(0,0,2),(2,4,10),(2,2,124)]),(43,[(2,4,10)]),(6,[(0,1,3),(0,0,2)]),(3,[(3,0,4),(2,2,20)]),(43,[(3,0,4)]),(9,[(0,1,3),(3,0,4)]),(14,[(0,1,3),(1,16,20)]),(1,[(3,0,4),(1,16,20)]),(2,[(3,0,4),(0,1,3),(1,16,20)]),(3,[(3,0,4),(1,16,20)]),(6,[(0,1,3),(1,16,20)]),(9,[(3,0,4),(0,1,3),(1,16,20)]),(2,[(3,0,4),(3,1,3)]),(9,[(3,0,4),(3,1,3)]),(2,[(3,1,3),(2,4,10)]),(6,[(3,1,3),(0,0,2)]),(3,[(3,0,4),(2,2,22)]),(9,[(3,0,4),(3,1,3),(2,2,22)]),(9,[(3,1,3),(3,0,4)]),(14,[(3,1,3),(1,16,22)]),(2,[(3,0,4),(3,1,3),(1,16,22)]),(3,[(3,0,4),(1,16,22)]),(6,[(3,1,3),(1,16,22)]),(9,[(3,0,4),(3,1,3),(1,16,22)]),(14,[(1,1,96)]),(20,[(1,1,96)]),(9,[(2,0,1),(2,4,8),(1,1,96)]),(14,[(2,1,48)]),(9,[(0,0,1),(2,4,6),(2,1,48)]),(0,[(0,2,5)]),(14,[(0,2,5),(2,1,48)]),(14,[(0,2,5)]),(6,[(0,2,5)]),(6,[(0,2,5),(0,0,1)]),(25,[(0,2,5)]),(2,[(0,0,1),(2,4,6),(2,1,48)]),(3,[(0,0,1),(2,4,6),(2,1,48)]),(40,[(0,2,5)]),(3,[(0,2,5)]),(11,[]),(1,[(3,0,4),(0,2,226)]),(6,[(3,1,2),(1,16,19),(0,2,226)]),(20,[(2,1,48)]),(9,[(3,0,4),(0,2,3)]),(2,[(3,0,4),(2,1,28)]),(3,[(3,0,4),(2,1,28)]),(9,[(0,2,3),(3,0,4)]),(14,[(0,2,3),(1,16,28)]),(2,[(3,0,4),(1,16,28)]),(3,[(3,0,4),(1,16,28)]),(6,[(0,2,3),(1,16,28)]),(9,[(3,0,4),(0,2,3),(1,16,28)]),(2,[(0,1,5),(2,4,10)]),(6,[(0,1,5),(0,0,2)]),(14,[(0,2,5),(2,2,124)]),(34,[(0,1,5)]),(6,[(0,1,5),(0,2,5),(0,0,2)]),(2,[(3,1,5),(2,4,10)]),(6,[(3,1,5),(0,0,2)]),(14,[(2,2,96),(1,1,106)]),(2,[(2,0,1),(2,4,8),(1,1,106)]),(6,[(2,0,1),(2,2,96),(1,1,106)]),(50,[]),(47,[(1,1,106)]),(20,[(2,2,96),(1,1,106)]),(14,[(2,2,48),(2,1,74)]),(2,[(0,0,1),(2,4,6),(2,1,74)]),(6,[(0,0,1),(2,2,48),(2,1,74)]),(47,[(2,1,74)]),(20,[(2,2,48),(2,1,74)]),(6,[(0,2,5),(0,0,2)]),(20,[(2,2,124)]),(14,[(2,3,177)]),(20,[(2,3,177)]),(9,[(0,0,3),(2,4,12),(2,3,177)]),(9,[(3,0,4),(2,2,220)]),(9,[(3,0,4),(2,2,221)]),(2,[(2,0,3),(1,0,1)]),(3,[(1,0,1),(0,2,7),(1,0,77)]),(25,[(2,0,3)]),(1,[(2,0,3),(1,0,77)]),(20,[(0,2,7)]),(9,[(1,0,1),(0,2,7),(1,0,77)]),(1,[(1,0,77)]),(25,[(3,4,5)]),(0,[(3,4,5)]),(2,[(3,4,5),(1,0,1)]),(6,[(1,0,1),(0,2,7),(1,0,77)]),(2,[(3,4,5)]),(14,[(3,4,5)]),(1,[(3,4,5)]),(40,[(3,4,5)]),(3,[(3,4,5)]),(3,[(0,1,2),(1,17,38)]),(6,[(0,1,2),(1,17,38)]),(14,[(0,1,2),(0,3,187)]),(2,[(1,0,1),(1,4,17)]),(0,[(0,1,2),(1,4,17)]),(2,[(1,4,17)]),(1,[(1,4,17)]),(14,[(0,1,2),(1,4,17)]),(40,[(0,1,2),(1,4,17)]),(3,[(0,1,2),(1,4,17)]),(55,[(0,1,2),(1,4,17)]),(58,[]),(9,[(0,1,2),(1,4,17)]),(14,[(0,1,2),(0,4,208)]),(2,[(0,0,4),(1,15,17),(0,4,208)]),(20,[(0,1,2),(0,4,208)]),(14,[(0,2,7),(0,5,78)]),(2,[(1,0,1),(0,5,78)]),(1,[(1,0,77),(0,5,78)]),(25,[(0,5,78)]),(14,[(0,1,2),(0,5,78)]),(2,[(1,0,1),(0,5,78),(1,17,232)]),(1,[(1,0,77),(0,5,78),(1,17,232)]),(9,[(0,1,2),(3,0,184)]),(2,[(1,0,1),(2,0,1)]),(9,[(2,0,1),(2,2,8),(2,0,95)]),(1,[(2,0,95)]),(3,[(2,0,1),(2,2,8),(2,0,95)]),(6,[(2,0,1),(2,2,8),(2,0,95)]),(2,[(2,0,1),(2,3,17)]),(2,[(2,3,17)]),(1,[(2,3,17)]),(9,[(0,1,2),(2,3,17)]),(20,[(0,1,2),(2,3,17)]),(2,[(2,0,1),(2,4,17)]),(2,[(2,4,17)]),(1,[(2,4,17)]),(20,[(0,1,2),(2,4,17)]),(9,[(0,1,2),(2,4,17)]),(2,[(3,0,4),(1,16,17),(0,4,222)]),(9,[(0,1,2),(0,3,4)]),(3,[(0,1,2),(1,0,38)]),(6,[(0,1,2),(1,0,38)]),(2,[(0,3,4),(1,0,38)]),(3,[(1,0,38)]),(6,[(1,0,38)]),(9,[(0,3,4),(1,0,38)]),(9,[(0,3,4),(0,1,2)]),(9,[(0,3,4),(0,1,2),(1,38,182)]),(1,[(0,3,4),(1,17,38)]),(2,[(0,3,4),(1,17,38)]),(9,[(0,1,2),(0,3,4),(1,17,38)]),(6,[(0,1,2),(1,17,38),(0,0,233)]),(40,[(0,1,2),(0,0,233),(2,5,234)]),(43,[(1,0,1),(0,5,87)]),(6,[(0,1,2),(1,17,38),(2,0,233)]),(2,[(0,1,30)]),(3,[(0,2,4),(0,1,30)]),(6,[(0,1,30)]),(9,[(0,2,4),(0,1,30)]),(9,[(0,1,4),(2,2,23)]),(9,[(0,1,2),(2,2,182)]),(9,[(3,0,1),(2,2,9),(1,0,35)]),(2,[(3,0,1),(3,4,5)]),(6,[(3,0,1),(2,2,9),(1,0,35)]),(25,[(1,0,35)]),(3,[(3,0,1),(2,2,9),(1,0,35)]),(9,[(3,1,2),(0,3,4)]),(3,[(3,1,2),(1,0,38)]),(6,[(3,1,2),(1,0,38)]),(3,[(3,1,2),(2,2,38)]),(6,[(3,1,2),(2,2,38)]),(9,[(3,1,2),(0,3,4),(2,2,38)]),(9,[(0,3,4),(3,1,2)]),(14,[(3,1,2),(2,5,19)]),(2,[(0,3,4),(1,19,38)]),(3,[(3,1,2),(1,19,38)]),(6,[(3,1,2),(1,19,38)]),(9,[(3,1,2),(0,3,4),(1,19,38)]),(2,[(2,4,19)]),(3,[(3,1,2),(2,4,19)]),(9,[(3,1,2),(2,4,19)]),(3,[(1,0,20)]),(2,[(0,1,3),(1,0,20)]),(6,[(0,1,3),(1,0,20)]),(9,[(0,1,3),(1,0,20)]),(1,[(1,0,20)]),(14,[(0,1,3),(0,2,130)]),(3,[(0,0,2),(1,10,20),(0,2,130)]),(20,[(0,1,3),(0,2,130)]),(9,[(0,1,3),(0,2,4)]),(9,[(0,2,4),(0,1,3)]),(1,[(0,2,4),(1,20,30)]),(2,[(0,1,3),(1,20,30)]),(3,[(0,2,4),(1,20,30)]),(6,[(0,1,3),(1,20,30)]),(9,[(0,1,3),(0,2,4),(1,20,30)]),(25,[(2,2,125)]),(1,[(2,4,20),(2,2,125)]),(3,[(2,4,20),(2,2,125)]),(6,[(0,1,3),(2,2,125)]),(9,[(0,1,3),(2,4,20),(2,2,125)]),(9,[(0,1,3),(2,2,128)]),(9,[(3,0,1),(2,3,9),(1,0,40)]),(1,[(2,2,4)]),(3,[(2,2,4),(3,0,1)]),(6,[(3,0,1),(2,3,9),(1,0,40)]),(25,[(1,0,40)]),(3,[(2,2,4)]),(2,[(3,0,1),(2,3,9),(1,0,40)]),(0,[(2,2,4)]),(40,[(2,2,4)]),(55,[(2,2,4)]),(9,[(2,2,4)]),(1,[(0,2,5)]),(3,[(0,2,5),(3,0,1)]),(14,[(0,2,5),(2,3,9)]),(47,[(0,2,5)]),(14,[(3,1,3),(0,2,137)]),(3,[(0,0,2),(1,10,22),(0,2,137)]),(20,[(3,1,3),(0,2,137)]),(3,[(3,4,5),(3,0,1)]),(9,[(3,1,3),(0,2,4)]),(14,[(3,1,3),(2,5,22)]),(9,[(0,2,4),(3,1,3)]),(2,[(3,1,3),(1,22,30)]),(3,[(0,2,4),(1,22,30)]),(6,[(3,1,3),(1,22,30)]),(9,[(3,1,3),(0,2,4),(1,22,30)]),(1,[(2,2,133)]),(3,[(2,4,22),(2,2,133)]),(6,[(3,1,3),(2,2,133)]),(9,[(3,1,3),(2,4,22),(2,2,133)]),(9,[(3,1,3),(2,2,136)]),(1,[(2,0,3),(1,0,79)]),(3,[(1,0,1),(0,4,7),(1,0,79)]),(6,[(2,0,3),(1,0,1)]),(20,[(0,4,7)]),(9,[(1,0,1),(0,4,7),(1,0,79)]),(1,[(1,0,79)]),(6,[(0,2,5),(1,0,1)]),(14,[(0,2,5),(0,4,7)]),(2,[(1,0,1),(0,4,7),(1,0,79)]),(25,[(3,2,5)]),(0,[(3,2,5)]),(6,[(3,2,5),(1,0,1)]),(6,[(3,2,5)]),(14,[(3,2,5)]),(40,[(3,2,5)]),(3,[(3,2,5)]),(1,[(3,2,5)]),(14,[(0,1,4),(0,2,146)]),(6,[(0,0,2),(1,10,23),(0,2,146)]),(20,[(0,1,4),(0,2,146)]),(14,[(0,4,7),(0,5,93)]),(6,[(1,0,1),(0,5,93)]),(1,[(1,0,79),(0,5,93)]),(25,[(0,5,93)]),(1,[(2,0,96)]),(9,[(2,0,1),(2,4,8),(2,0,96)]),(9,[(0,1,4),(0,2,3)]),(1,[(0,2,3),(1,23,28)]),(2,[(0,1,4),(1,23,28)]),(3,[(0,1,4),(1,23,28)]),(6,[(0,2,3),(1,23,28)]),(9,[(0,1,4),(0,2,3),(1,23,28)]),(1,[(2,2,23)]),(3,[(0,1,4),(2,2,23)]),(6,[(2,2,23)]),(1,[(2,3,133)]),(12,[(0,1,4)]),(9,[(3,1,3),(2,4,22),(2,3,133)]),(9,[(0,1,4),(2,2,141)]),(9,[(0,1,4),(2,2,142)]),(9,[(3,0,1),(2,4,9),(1,0,42)]),(6,[(0,2,5),(3,0,1)]),(14,[(0,2,5),(2,4,9)]),(25,[(1,0,42)]),(2,[(3,0,1),(2,4,9),(1,0,42)]),(3,[(3,0,1),(2,4,9),(1,0,42)]),(6,[(3,2,5),(3,0,1)]),(47,[(3,2,5)]),(14,[(3,1,4),(0,2,151)]),(6,[(0,0,2),(1,10,25),(0,2,151)]),(20,[(3,1,4),(0,2,151)]),(9,[(3,1,4),(0,2,3)]),(9,[(0,2,3),(3,1,4)]),(14,[(3,1,4),(2,5,25)]),(2,[(3,1,4),(1,25,28)]),(3,[(3,1,4),(1,25,28)]),(6,[(0,2,3),(1,25,28)]),(9,[(3,1,4),(0,2,3),(1,25,28)]),(2,[(3,0,1),(2,4,9),(1,0,117)]),(6,[(3,0,1),(2,2,42),(1,0,117)]),(47,[(1,0,117)]),(20,[(2,4,9),(2,2,42)]),(2,[(0,0,1),(2,4,6),(2,0,74)]),(6,[(0,0,1),(2,2,48),(2,0,74)]),(47,[(2,0,74)]),(9,[(3,1,4),(2,2,150)]),(2,[(1,0,28)]),(3,[(1,0,28)]),(6,[(0,2,3),(1,0,28)]),(9,[(0,2,3),(1,0,28)]),(2,[(2,4,28)]),(3,[(2,4,28)]),(9,[(0,2,3),(2,4,28)]),(2,[(1,0,30)]),(3,[(0,2,4),(1,0,30)]),(6,[(1,0,30)]),(9,[(0,2,4),(1,0,30)]),(14,[(0,2,4),(0,5,52)]),(2,[(1,0,30),(0,5,52)]),(3,[(0,2,4),(1,0,30),(0,5,52)]),(6,[(1,0,30),(0,5,52)]),(14,[(0,2,4),(0,1,65)]),(53,[(0,0,1)]),(2,[(0,0,1),(1,6,30),(0,1,65)]),(6,[(0,0,1),(1,6,30),(0,1,65)]),(20,[(0,2,4),(0,1,65)]),(53,[(0,5,52)]),(47,[(0,5,52)]),(13,[(1,0,30)]),(1,[(0,2,4),(1,0,30),(0,5,52)]),(2,[(2,0,30)]),(3,[(0,2,4),(2,0,30)]),(6,[(2,0,30)]),(9,[(0,2,4),(2,0,30)]),(2,[(1,1,30)]),(3,[(0,2,4),(1,1,30)]),(6,[(1,1,30)]),(9,[(0,2,4),(1,1,30)]),(2,[(2,3,30)]),(6,[(2,3,30)]),(9,[(0,2,4),(2,3,30)]),(14,[(0,3,4),(0,2,58)]),(3,[(1,0,38),(0,2,58)]),(6,[(1,0,38),(0,2,58)]),(9,[(0,3,4),(1,0,38),(0,2,58)]),(40,[(0,2,58)]),(1,[(0,3,4),(2,2,59)]),(3,[(2,1,38),(2,2,59)]),(6,[(2,1,38),(2,2,59)]),(9,[(0,3,4),(2,1,38),(2,2,59)]),(40,[(2,2,59)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 11 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice58 : Slice h0R h0G (subcubeFast 32 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice57 : Slice h0R h0G (subcubeFast 32 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice56 : Slice h0R h0G (subcubeFast 32 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice55 : Slice h0R h0G (subcubeFast 32 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice54 : Slice h0R h0G (subcubeFast 24 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice53 : Slice h0R h0G (subcubeFast 24 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice52 : Slice h0R h0G (subcubeFast 16 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice51 : Slice h0R h0G (subcubeFast 16 9) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice50 : Slice h0R h0G (subcubeFast 16 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice49 : Slice h0R h0G (subcubeFast 16 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice48 : Slice h0R h0G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 8) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice47 : Slice h0R h0G (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice46 : Slice h0R h0G (subcubeFast 8 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice45 : Slice h0R h0G (subcubeFast 8 18) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice44 : Slice h0R h0G (subcubeFast 8 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice43 : Slice h0R h0G (subcubeFast 8 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice42 : Slice h0R h0G (subcubeFast 8 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice41 : Slice h0R h0G (subcubeFast 8 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice40 : Slice h0R h0G (subcubeFast 8 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice39 : Slice h0R h0G (subcubeFast 4 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice38 : Slice h0R h0G (subcubeFast 4 40) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice37 : Slice h0R h0G (subcubeFast 4 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice36 : Slice h0R h0G (subcubeFast 4 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice35 : Slice h0R h0G (subcubeFast 4 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 2 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 2 40) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 2 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 2 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 2 12) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 2 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 2 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 2 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 2 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 1 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 1 40) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 1 36) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 1 34) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 1 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 1 20) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 1 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 1 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 1 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 1 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 1 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 0 48) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 0 40) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 0 36) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 0 34) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 0 32) 10 := slice_fast_direct (zDead := 0) (by decide +kernel) h52Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 0 20) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h53Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 0 18) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 0 16) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h55Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 12) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h56Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 9) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h57Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 8) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h58Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h59Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h60Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h61Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (forall_cons (fun _ h => by cases h; exact h0Slice25) (forall_cons (fun _ h => by cases h; exact h0Slice26) (forall_cons (fun _ h => by cases h; exact h0Slice27) (forall_cons (fun _ h => by cases h; exact h0Slice28) (forall_cons (fun _ h => by cases h; exact h0Slice29) (forall_cons (fun _ h => by cases h; exact h0Slice30) (forall_cons (fun _ h => by cases h; exact h0Slice31) (forall_cons (fun _ h => by cases h; exact h0Slice32) (forall_cons (fun _ h => by cases h; exact h0Slice33) (forall_cons (fun _ h => by cases h; exact h0Slice34) (forall_cons (fun _ h => by cases h; exact h0Slice35) (forall_cons (fun _ h => by cases h; exact h0Slice36) (forall_cons (fun _ h => by cases h; exact h0Slice37) (forall_cons (fun _ h => by cases h; exact h0Slice38) (forall_cons (fun _ h => by cases h; exact h0Slice39) (forall_cons (fun _ h => by cases h; exact h0Slice40) (forall_cons (fun _ h => by cases h; exact h0Slice41) (forall_cons (fun _ h => by cases h; exact h0Slice42) (forall_cons (fun _ h => by cases h; exact h0Slice43) (forall_cons (fun _ h => by cases h; exact h0Slice44) (forall_cons (fun _ h => by cases h; exact h0Slice45) (forall_cons (fun _ h => by cases h; exact h0Slice46) (forall_cons (fun _ h => by cases h; exact h0Slice47) (forall_cons (fun _ h => by cases h; exact h0Slice48) (forall_cons (fun _ h => by cases h; exact h0Slice49) (forall_cons (fun _ h => by cases h; exact h0Slice50) (forall_cons (fun _ h => by cases h; exact h0Slice51) (forall_cons (fun _ h => by cases h; exact h0Slice52) (forall_cons (fun _ h => by cases h; exact h0Slice53) (forall_cons (fun _ h => by cases h; exact h0Slice54) (forall_cons (fun _ h => by cases h; exact h0Slice55) (forall_cons (fun _ h => by cases h; exact h0Slice56) (forall_cons (fun _ h => by cases h; exact h0Slice57) (forall_cons (fun _ h => by cases h; exact h0Slice58) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (5 - 1) xs.toFinset) h0Empty := trivial
def h0Block5_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,160],[]),([1,2,3,4,5,242],[])]
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
def h0Block6_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,89,157],[]),([0,1,2,3,4,156,159],[521]),([0,1,2,3,4,156,158],[324]),([0,2,3,4,5,90,154],[]),([0,1,2,3,4,208,213],[]),([1,2,3,4,5,87,234],[]),([0,1,2,3,4,233,241],[1135]),([0,1,2,3,4,233,240],[1136]),([1,2,3,4,5,88,235],[])]
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
def h0Block7_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,5,38,65],[12,14,53,54,55,56,57,58,59]),([0,1,2,3,4,5,68],[0,1,8,9,11,12,13,14,15,16,72,73]),([0,1,2,3,4,5,6,71],[0,24,107,108,109]),([0,1,2,3,4,5,67,72],[9,21,24,62,116,117,118]),([0,1,2,3,4,5,67,70],[9,24,119]),([0,1,2,3,4,5,86],[1,8,9,12,14,15,16,91,143,201,202,203,204,205]),([0,1,2,3,4,5,60,80],[15,24,47,103,134,218]),([0,1,2,3,4,5,7,71],[1,24,107,109,222,223,224,225]),([0,1,2,3,4,5,100],[0,1,6,8,9,11,12,13,14,15,16,73,269]),([0,1,2,3,4,5,8,71],[0,15,24,270,292]),([0,1,2,3,4,5,44,60],[7,15,24,47,103,353,354]),([0,1,2,3,4,5,9,71],[8,15,24,292,324])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_0 = true := by decide +kernel
def h0Block7_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,10,127],[13,406,414]),([0,1,2,3,4,5,144],[0,6,8,9,11,12,13,14,15,16,469]),([0,1,2,3,4,5,38,153],[6,12,14]),([0,1,2,3,4,5,10,155],[6,208,515]),([0,1,2,3,4,5,156,157],[1,6,80,91,401,408,516,517,518,519,520]),([0,1,2,3,4,5,89,156],[1,6,23,324,516,517,518,519]),([0,1,2,3,4,5,154,156],[1,6,506,518,519]),([0,1,2,3,4,5,90,156],[1,6,324,401,518]),([0,1,2,3,4,5,172],[0,1,8,9,12,14,15,16,24,84,601]),([0,1,2,3,4,5,59,165],[6,15,254]),([0,1,2,3,4,5,177,182],[6,13,629,646]),([0,1,2,3,4,5,177,184],[13,15,646,648])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_1 = true := by decide +kernel
def h0Block7_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,182,197],[6,13,721,734]),([0,1,2,3,4,5,184,197],[13,15,317,648]),([0,1,2,3,4,5,181,201],[11,13,14,103,637]),([0,1,2,3,4,5,176,208],[0,11,12,324,632]),([0,1,2,3,4,5,212],[0,6,8,9,11,12,14,15,16,24,852]),([0,1,2,3,4,5,208,209],[11,12,144,631,643,848,853,854,855,856]),([0,1,2,3,4,5,208,210],[11,12,854]),([0,1,2,3,4,5,119,199],[11,12,59,733]),([0,1,2,3,4,5,208],[0,1,8,9,11,12,14,15,16,855]),([0,2,3,4,116,218],[422,905,910,911,912,913]),([0,1,2,3,4,5,176,222],[11,12,506,632]),([0,1,2,3,4,5,179,184],[11,15,368,648])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_2 = true := by decide +kernel
def h0Block7_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,228],[1,8,9,12,13,15,16]),([0,1,2,3,4,26,27,161],[6,154,525]),([0,1,3,4,26,32,161],[16,145,154,523,525,1043,1044,1045]),([0,1,2,3,4,5,78,233],[0,8,11,103,196,506,643,645,1076,1082,1083]),([0,1,2,3,4,5,17,236],[0,6,11,324]),([0,1,2,3,5,180,211],[6,24,391,643,856,1086,1091,1092]),([0,1,2,3,5,78,180,211],[8,14,23,856]),([0,1,2,3,4,5,237],[0,1,8,9,11,12,13,14,16,649,652,1102,1103,1104]),([0,1,2,3,4,5,101,233],[0,8,103,279,506,645,1082,1110]),([0,1,2,3,4,5,238],[0,1,9,11,12,13,14,15,16]),([0,1,2,3,4,5,239],[0,1,6,8,9,12,14,15,16,24,1130]),([0,1,2,3,4,5,38,239],[6,1130])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_3 = true := by decide +kernel
def h0Block7_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,233,234],[0,8,84,91,643,645,1082,1083,1131,1132,1133,1134]),([0,1,2,3,4,5,87,233],[0,8,219,1082,1083,1131,1132,1133]),([0,1,2,3,4,5,233,235],[0,8,1082,1083,1137]),([0,1,2,3,4,5,88,233],[0,8,23,645,1082]),([0,1,2,3,4,5,58,243],[1]),([0,1,2,3,4,5,84,112],[8,24,324]),([0,1,2,3,4,5,23,248],[0,6,324]),([0,1,2,3,4,30,251,252],[61,182,1292,1294,1304,1305]),([0,1,2,3,4,30,251,253],[61,1292])]
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
def h0Block8_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,35],[0,1,8,9,10,11,12,13,14,15,16]),([0,1,2,3,4,5,51],[0,1,8,9,11,12,13,14,15,16,17,21,22,30,31,32,33,34,35]),([0,1,2,3,5,6,30,38],[2,3,4,13,38,41,42,43,44,45,46,47,48,49,50,51,52,60,61,62]),([0,1,2,3,4,5,6,62],[0,1,3,6,8,13,15,21,39,60,62,63,64,65,66,67,68,69,70,71]),([0,1,2,3,4,5,65],[0,1,8,9,11,12,14,15,16,36,40,54,57,58,61,74,75]),([0,1,2,3,4,5,38,47],[0,2,6,11,12,13,14,24,47,48,60,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91]),([0,1,2,3,4,5,6,60],[0,1,2,3,4,5,6,8,11,13,21,23,24,46,47,60,71,94,95,96,97,98,99,100,101,102,103,104]),([0,1,2,3,4,5,6,64],[0,1,2,3,4,5,6,8,11,13,15,21,71,89,93,105,106,107,110,111,112,113]),([0,1,2,3,4,5,67],[0,1,8,9,11,12,14,15,16,21,24,80,84,114,115,116,117,118]),([0,1,2,3,4,5,6,67],[0,1,2,3,4,5,8,11,21,60,71,80,114,116,117,118]),([0,1,2,3,4,5,38,67],[0,12,14,21,47,80,84,85,88,89,91,92,114,115,116,117,118]),([0,1,2,3,4,5,74],[0,6,9,11,12,13,14,15,16,24,121,124,125,126,127,128,129])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := nodesWithIdentity [([0,1,3,4,5,28,77],[1,8,12,18,24,131,136,139,140,141,142,143,144,145]),([0,1,2,3,4,5,28,80],[1,8,9,11,12,15,17,18,23,24,25,28,41,134,136,146,147,148,149,150,151,152,153,154]),([0,1,2,3,4,5,7,50],[0,1,6,8,11,15,23,24,26,28,29,131,132,133,134,137,138,145,155,156,157,158,159,160,161]),([0,1,2,3,4,5,82],[0,8,9,11,12,13,14,15,16,18,23,136,138,162,163,164,165,166]),([0,2,3,4,5,7,57],[0,6,13,24,37,41,170,171,172,173,174,175]),([0,1,3,4,5,30,77],[1,8,14,24,37,91,131,143,145,168,176,177,178,179,180]),([0,1,2,3,4,5,30,80],[1,8,9,13,14,15,24,36,37,49,50,61,63,134,147,148,149,150,154,168,181,182,183]),([0,1,2,3,4,5,7,63],[0,1,6,8,13,15,24,63,64,131,132,133,134,138,145,160,161,169,184,185,186,187,188,189,190]),([0,1,2,3,4,5,85],[0,6,8,9,11,12,14,15,16,37,41,61,168,191,192,193,194,195]),([0,1,2,3,4,5,38,77],[1,8,11,12,13,14,23,24,47,48,80,85,87,88,89,91,92,131,141,143,179,196,197,198,199,200]),([0,2,3,4,5,7,59],[0,6,11,13,23,92,138,208,209,210,211,212,213]),([0,1,2,3,4,5,7,60],[0,1,6,8,11,13,23,24,47,94,95,99,100,101,103,131,132,133,134,138,161,206,214,215,216,217,219])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
def h0Block8_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,38,80],[1,8,11,12,13,14,15,23,47,80,85,88,89,91,92,134,147,148,149,150,154,183,220]),([0,1,2,3,4,5,7,64],[0,1,6,8,11,13,15,23,87,89,105,106,107,110,111,112,131,132,133,134,138,161,207,221]),([0,1,2,3,4,5,92],[0,8,9,11,12,14,15,16,23,24,41,85,92,138,226,227,228,229,230]),([0,1,2,3,4,5,94],[1,8,9,11,12,13,14,15,16,24,233,235,236,237,238,239,240]),([0,1,2,3,4,5,81],[1,8,11,12,13,14,15,16,241]),([1,2,3,4,5,8,45],[6,8,11,17,24,248,249,250,251,252,253,254]),([0,1,2,3,4,5,8,50],[0,1,6,8,11,15,28,29,145,155,156,157,158,159,242,243,244,245,247,253,254,256,257]),([0,1,2,3,4,5,97],[0,1,9,11,12,13,14,15,16,17,18,253,254,258,259,260,261]),([0,1,2,3,5,8,30,38],[13,42,43,47,48,49,50,51,52,61,242,243,244,262,264,265,266]),([0,1,2,3,4,5,8,62],[0,1,6,8,13,15,63,64,65,66,68,69,70,243,253,256,257,263,267,268,270]),([0,1,2,3,4,5,98],[0,1,6,8,9,11,12,14,15,16,36,37,61,271,272,273,274]),([0,1,2,3,4,5,38,95],[0,1,11,12,13,14,24,47,80,87,88,89,90,92,242,254,275,276,277,278,279,280,281])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_2 = true := by decide +kernel
def h0Block8_3 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,8,58],[6,8,11,13,80,254,283,284,285,286,287]),([0,1,2,3,4,5,8,60],[0,1,6,8,11,13,24,47,94,95,99,100,101,102,103,242,243,244,245,253,254,257,265,288,289,290,291]),([0,1,2,3,4,5,8,64],[0,1,6,8,11,13,15,89,105,106,107,110,111,112,221,242,243,244,245,253,254,257,282]),([0,1,2,3,4,5,99],[0,1,9,11,12,14,15,16,24,80,92,254,293,294,295,296]),([0,1,2,3,4,5,106],[0,1,9,11,12,13,14,15,16,24,298,300,301,302,303,304]),([0,1,2,3,4,5,28,44],[6,7,8,9,11,12,15,17,18,23,24,25,28,41,136,151,153,311,312,313,314,315,316,317]),([0,1,2,3,4,5,109],[0,1,9,12,13,14,15,16,22,136,310,318,319,320,321,322,323,324]),([0,1,2,3,4,5,30,44],[6,7,8,9,13,14,15,24,36,37,49,50,61,63,168,182,312,313,314,315,317,328,329]),([0,1,2,3,4,5,9,63],[0,1,6,7,8,13,15,24,63,145,184,185,186,187,188,189,305,306,307,310,324,326,327,330]),([0,1,2,3,4,5,110],[0,1,9,11,12,14,15,16,40,168,324,331,332,333,334,335,336]),([0,1,2,3,4,5,35,38],[6,8,10,11,12,13,14,23,24,47,80,84,85,87,88,89,92,305,343,344,345,346,347,348,349]),([0,1,2,3,4,5,9,60],[0,1,6,7,8,11,13,23,24,47,94,95,99,100,101,103,214,305,306,307,310,324,330,347,351,352,353,355])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_3 = true := by decide +kernel
def h0Block8_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,38,44],[6,7,8,11,12,13,14,15,23,47,80,85,88,89,91,92,312,313,314,315,317,329,356]),([0,1,2,3,4,5,9,64],[0,1,6,7,8,11,13,15,23,87,89,106,107,110,111,112,221,305,306,307,310,324,330,350]),([0,1,2,3,4,5,111],[0,1,9,12,14,15,16,24,84,85,310,324,357,358,359,360,361,362]),([0,1,2,3,4,5,114],[6,8,9,11,12,13,15,16,24,372,374,375,376,377,378]),([0,1,2,3,4,5,117],[6,8,9,11,12,13,14,15,16,24,382,384,385,386,387,388,389,390]),([0,1,2,3,4,5,120],[6,8,9,11,12,13,14,15,16,392]),([0,1,2,3,4,5,108],[6,8,11,12,13,14,15,16,393]),([0,1,2,3,4,5,10,125],[0,6,8,9,11,13,24,391,394,395,396,399,401,402,403,404,405,406,407,408,409,410,411,412,413]),([0,1,2,3,4,5,10,128],[0,6,8,9,11,15,24,317,394,395,396,400,401,402,408,413,415,416,417,418,419,420,421,422]),([0,1,2,3,4,5,130],[0,1,8,9,11,12,13,14,15,16,41,397,401,403,423,424,425,426,427]),([0,1,2,3,4,5,10,130],[0,8,9,11,394,395,396,397,401,402,408,413,423,424,425,426]),([0,1,2,3,4,5,10,133],[0,1,8,9,11,13,24,324,394,395,396,401,402,408,413,430,432,433,434,435,436,437,438,439,440])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_4 = true := by decide +kernel
def h0Block8_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,137],[0,1,8,9,11,12,13,14,15,16,324,401,402,428,443,444,445,446]),([0,1,2,4,5,23,123],[0,11,24,26,59,255,447,452,453,454,455,456,457,458,459,460]),([0,1,2,3,4,5,10,141],[0,6,8,9,13,15,24,394,401,403,408,413,422,450,461,462,463,464,465,466,467,468]),([0,1,2,3,4,5,10,142],[0,6,8,9,13,15,24,317,394,395,396,401,402,403,413,422,450,461,462,470,471,472,473,474,475]),([0,1,2,3,4,5,146],[0,1,8,9,11,12,14,15,16,403,440,447,476,477,478,479,480]),([0,1,2,3,4,5,10,146],[0,6,8,9,394,395,396,401,402,403,413,447,476,477,478,479]),([0,1,2,3,4,5,10,148],[8,9,324,394,396,401,403,408,413,440,447,481,482]),([0,1,2,4,5,25,123],[0,11,24,59,422,454,455,457,459,460,483,488,489,490]),([0,1,2,3,4,5,151],[0,1,6,8,9,11,12,14,15,16,324,402,483,494,495,496,497]),([0,2,3,4,5,24,37],[0,6,13,24,324,498,499,500,501,502]),([0,1,2,3,4,5,37,38],[0,6,11,12,13,14,23,24,47,80,84,85,88,89,105,305,324,344,347,355,498,501,503,504,505]),([0,1,2,3,4,5,10,59],[0,6,8,9,11,13,24,92,208,254,349,394,395,396,401,403,413,508,509,510,511,512,513,514])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_5 = true := by decide +kernel
def h0Block8_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,10,64],[0,8,9,11,13,15,24,89,105,106,107,110,111,112,113,221,394,395,396,401,402,403,413,507]),([0,1,2,3,4,5,156],[1,6,8,9,11,12,14,15,16,80,401,516,517,518,519]),([0,1,2,3,4,5,10,156],[8,9,11,80,394,395,396,401,402,403,413,516,517,518,519]),([0,1,2,3,4,5,161],[0,1,6,8,9,11,12,14,15,16,523,525]),([0,1,2,3,4,5,20,165],[1,6,8,11,12,15,23,24,41,145,397,398,404,415,528,530,535,536,537,538,539,540,541,542]),([0,1,2,3,4,5,11,128],[0,6,8,9,11,15,23,24,26,90,317,415,417,419,420,421,526,527,528,529,532,533,543,544]),([0,1,2,3,4,5,166],[0,1,9,12,13,14,15,16,90,530,534,545,546,547,548,549,550]),([0,1,2,3,4,5,22,165],[1,6,8,11,12,15,23,24,41,145,428,429,432,441,506,528,536,538,539,540,552,554,555,556,557]),([0,1,2,3,4,5,11,136],[0,1,8,9,11,15,23,24,26,90,154,441,526,527,528,529,533,543,544,553,558,559,560,561]),([0,1,2,3,4,5,168],[0,8,9,11,12,13,14,15,16,90,529,552,562,563,564,565,566]),([0,1,2,3,4,5,23,165],[1,6,8,13,14,15,24,145,440,447,448,451,458,461,528,536,537,538,539,540,567,570,571]),([0,1,2,3,4,5,11,142],[0,6,8,9,13,15,24,90,317,461,470,472,473,474,475,526,527,528,529,533,534,543,569])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_6 = true := by decide +kernel
def h0Block8_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,169],[0,1,9,11,12,14,15,16,90,534,567,572,573,574,575,576,577]),([0,1,2,3,4,5,25,165],[1,6,8,13,14,15,24,145,391,483,484,487,491,492,528,536,537,538,539,540,555,579,581,582]),([0,1,2,3,4,5,11,150],[0,1,8,9,13,15,24,90,154,492,526,527,528,529,533,534,543,544,580,583,584,585,586,587]),([0,1,2,3,4,5,171],[0,6,8,9,11,12,14,15,16,90,529,579,588,589,590,591,592]),([0,1,2,3,4,5,38,69],[2,6,8,11,12,13,14,23,24,47,79,80,81,84,85,88,89,104,505,506,597,598,599,600]),([0,1,2,3,4,5,11,59],[0,6,8,9,11,13,23,24,90,92,208,210,349,508,511,512,513,526,527,528,533,534,543,605,606]),([0,1,3,4,5,11,60],[0,11,13,24,47,94,95,145,214,533,607,608,609]),([0,1,2,3,4,5,38,165],[8,11,12,13,14,15,23,24,47,80,84,85,88,89,92,145,528,536,537,538,539,555,610]),([0,1,2,3,4,5,11,64],[0,8,9,11,13,15,23,24,89,90,107,110,111,112,221,505,526,527,528,529,533,534,543,604]),([0,1,2,3,4,5,173],[0,1,6,9,12,14,15,16,85,90,533,611,612,613,614,615]),([0,1,2,3,4,5,17,177],[0,1,6,9,11,13,24,60,629,631,632,637,638,639,640,641,642,643,644,645,646,647,648,649]),([0,1,2,3,4,5,12,17,181],[6,391,629,631,633,636,637,643,650,651])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_7 = true := by decide +kernel
def h0Block8_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,12,182],[0,6,8,11,12,15,91,368,629,634,636,648,652,653,654,655,656,657,658,659]),([0,1,2,3,4,5,12,184],[0,6,8,11,12,15,368,628,629,630,634,635,636,648,652,658,659,660,661,662,663]),([0,1,2,3,4,5,187],[0,1,8,9,11,12,13,14,15,16,368,631,636,664,665,666,667,668]),([0,1,2,3,4,5,17,187],[0,1,9,631,632,636,637,643,645,648,649,651,664,665,666,667,668]),([0,1,2,3,4,5,191],[0,1,6,9,11,12,13,14,15,16,324,635,669,676,677,678,679]),([0,1,2,3,4,5,193],[0,1,8,9,11,12,14,15,16,24,368,447,636,682,683,684,685,686]),([0,1,2,3,4,5,12,149],[0,1,8,11,12,13,24,91,324,368,484,628,629,630,635,636,658,659,687,689,690,691,692,693,694,695]),([0,1,2,3,4,5,194],[0,1,6,9,11,12,14,15,16,24,324,483,635,696,697,698,699]),([0,2,3,4,5,24,113],[0,6,11,13,324,500,502,701,702]),([0,1,2,3,4,5,192],[0,1,6,9,11,12,13,14,15,16,24,669,675,676,703,704,705]),([0,1,2,3,4,5,195],[1,6,8,9,11,12,14,15,16,36,368,707,708,709,710]),([0,1,3,4,5,31,174],[0,11,13,24,617,712,713,714,715])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_8 = true := by decide +kernel
def h0Block8_9 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,178],[0,1,6,9,11,12,13,14,15,16,24,641,716,717,718,719]),([0,1,2,3,4,5,17,197],[1,6,8,9,11,13,24,255,631,632,637,643,645,648,649,721,724,728,729,730,731,732,733,734,735]),([0,1,2,3,4,5,14,17,181],[6,391,632,637,643,645,721,725,727,736,737]),([0,1,2,3,4,5,17,200],[1,6,8,9,11,15,24,26,112,505,631,632,637,643,645,648,649,722,738,739,740,741,742]),([0,1,2,3,4,5,14,182],[0,6,8,11,12,15,24,59,91,506,648,653,655,656,657,721,726,727,743,744,745]),([0,1,2,3,4,5,14,184],[0,6,8,11,12,15,24,59,190,317,648,652,660,661,662,663,720,721,722,723,726,727,744,745]),([0,1,2,3,4,5,201],[0,1,9,12,13,14,15,16,59,724,727,746,747,748,749,750,751]),([0,1,2,3,4,5,17,201],[1,9,11,631,632,637,643,645,648,649,724,727,746,747,748,749,750,751]),([0,1,2,3,4,5,19,200],[1,6,8,9,11,15,24,26,112,349,669,670,673,674,704,722,739,740,741,742,755,756,757,758]),([0,1,2,3,4,5,14,190],[0,1,8,11,12,15,24,59,91,154,255,674,720,721,722,723,727,744,745,754,759,760,761,762,763]),([0,1,2,3,4,5,203],[0,6,9,11,12,13,14,15,16,59,704,723,753,764,765,766,767,768]),([0,1,2,3,4,5,23,140],[1,6,8,11,13,14,24,26,103,144,254,255,394,440,447,448,451,453,456,458,459,461,567,571,771,772,773,774])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_9 = true := by decide +kernel
def h0Block8_10 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,23,200],[1,6,8,11,13,14,15,26,112,144,255,440,447,448,451,458,461,571,722,739,740,741,742,775]),([0,1,2,3,4,5,205],[0,1,9,12,14,15,16,24,59,567,727,776,777,778,779,780,781]),([0,1,2,3,4,5,25,140],[1,6,8,11,13,14,24,103,144,254,394,459,483,484,487,489,490,491,492,579,582,771,772,773,784,785]),([0,1,2,3,4,5,14,149],[0,1,8,11,12,13,24,59,87,91,484,689,690,691,693,694,720,721,722,723,727,744,745,782,786,787]),([0,1,2,3,4,5,25,200],[1,6,8,11,13,14,15,87,112,144,254,391,483,484,487,491,492,582,722,739,740,741,742,756,788]),([0,1,2,3,4,5,14,150],[0,1,8,11,12,13,15,59,91,154,492,583,584,585,586,587,720,721,722,723,727,744,745,783,784]),([0,1,2,3,4,5,206],[0,6,9,11,12,14,15,16,24,59,579,723,789,790,791,792,793]),([0,1,2,3,4,5,30,196],[6,8,9,11,13,14,24,26,36,40,49,50,61,63,168,182,254,349,602,723,794,795,796,797,798,799]),([0,1,2,3,4,5,204],[0,6,8,9,11,12,13,14,15,16,24,59,91,144,317,391,704,753,765,800,801]),([0,1,2,3,4,5,14,57],[0,6,8,11,12,13,24,37,59,171,173,505,506,720,721,722,727,745,803,804,805,806,807,808,809]),([0,1,2,3,4,5,30,200],[8,9,11,13,14,15,24,26,36,37,40,49,50,61,63,112,182,505,722,739,740,741,756,810]),([0,1,2,3,4,5,14,63],[0,8,11,12,13,15,24,59,63,145,185,186,187,188,189,602,720,721,722,723,727,744,745,802])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_10 = true := by decide +kernel
def h0Block8_11 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,207],[0,1,6,9,12,14,15,16,59,168,811,812,813,814,815]),([0,1,2,3,4,5,26,140],[1,6,8,11,15,16,24,26,103,154,254,394,459,771,772,773,816,817,818,819,820,821,822,823,824,825]),([0,1,2,3,4,5,27,140],[1,6,8,11,15,16,24,26,103,254,394,459,771,772,773,826,827,828,829,830,831,832,833,834,835]),([0,1,2,3,4,5,198],[1,6,8,9,11,12,13,14,15,16,24,730,836,837,838,839,840]),([0,1,2,3,4,5,202],[1,6,8,11,13,14,15,16,841]),([0,1,2,3,4,5,15,17,176],[6,506,631,632,645,843,845,849,850]),([0,1,2,3,4,5,15,182],[0,6,8,13,14,15,144,422,648,652,653,654,655,656,657,743,843,846,848,849,851]),([0,1,2,3,4,5,15,184],[0,6,8,13,14,15,317,422,648,652,660,661,662,663,842,843,844,846,847,848,849,851]),([0,1,2,3,4,5,208],[0,1,8,9,11,12,14,15,16,631,848,853,854,855,856,857]),([0,1,2,3,4,5,15,208],[0,6,8,14,631,842,843,844,847,848,849,851,853,854,855,856]),([0,1,2,3,4,5,17,208],[0,1,9,631,632,637,643,645,648,649,724,848,853,854,855,856,857]),([0,1,2,3,4,5,15,119],[6,8,14,24,324,385,389,391,422,506,843,844,848,849,851,858,859,860])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_11 = true := by decide +kernel
def h0Block8_12 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,215],[0,1,6,8,9,11,12,14,15,16,324,669,847,863,864,865,866]),([0,1,2,3,4,5,20,175],[0,1,6,11,12,13,24,26,87,90,91,324,397,398,404,415,527,530,541,542,625,869,870,871,872,873,874]),([0,1,2,3,4,5,15,122],[0,6,8,11,13,14,24,103,144,398,842,843,844,847,848,849,851,867,875,876,877,878,879,880,881,882]),([0,1,2,3,4,5,15,128],[0,6,8,11,13,14,15,26,144,317,415,416,417,418,419,420,421,842,843,844,847,849,851,868]),([0,1,2,3,4,5,216],[0,1,8,9,11,12,14,15,16,24,26,397,848,883,884,885,886,887]),([0,1,2,3,4,5,22,175],[0,1,6,11,12,13,24,90,324,422,428,429,432,441,527,552,556,557,625,870,871,872,874,890,891]),([0,1,2,3,4,5,15,132],[0,1,8,11,13,14,24,103,324,429,842,843,844,847,849,851,882,888,892,893,894,895,896,897,898,899]),([0,1,2,3,4,5,217],[0,1,8,9,11,12,14,15,16,24,324,428,847,900,901,902,903]),([0,2,3,4,5,18,116],[0,6,13,24,324,422,905,906,907,908,909]),([0,2,3,4,5,21,116],[0,6,11,13,324,422,905,909,914,915,916]),([0,1,2,3,4,5,214],[0,1,6,9,11,12,13,14,15,16,24,91,144,317,324,506,859,917]),([0,1,2,3,4,5,15,46],[0,6,8,11,13,14,18,24,26,254,842,843,844,848,849,851,919,920,921,922,923,924,925,926])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_12 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_12 = true := by decide +kernel
def h0Block8_13 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,15,50],[0,8,11,13,14,15,26,28,29,145,155,156,157,158,159,842,843,844,847,848,849,851,918]),([0,1,2,3,4,5,219],[1,6,8,9,11,12,14,15,16,17,35,927,928,929,930]),([0,1,3,4,5,29,175],[0,11,13,24,625,871,931,932,933]),([0,1,2,3,4,5,16,17,176],[6,23,26,506,645,724,935,938,941,942]),([0,1,2,3,5,16,17,181],[6,14,24,26,270,602,631,637,643,650,736,940,943,944,945,946,947]),([0,1,2,3,4,5,17,220],[1,6,8,9,13,15,24,270,632,643,645,649,724,936,948,949,950,951,952,953,954]),([0,1,2,3,4,5,17,221],[1,6,8,9,13,15,24,602,631,632,637,645,648,649,724,936,948,955,956,957,958,959,960]),([0,1,2,3,4,5,16,182],[0,6,8,13,14,15,24,144,391,646,648,653,655,656,657,743,935,939,940,941,961]),([0,1,2,3,4,5,16,184],[0,6,8,13,14,15,24,190,317,646,648,652,660,661,662,663,934,935,936,937,939,940,941,961]),([0,1,2,3,4,5,222],[0,1,9,11,12,14,15,16,646,724,940,962,963,964,965,966,967]),([0,1,2,3,4,5,17,222],[1,8,9,631,632,637,645,648,649,724,940,962,963,964,965,966,967]),([0,1,2,3,4,5,17,186],[1,8,9,23,270,391,632,643,645,646,648,649,650,724,968,969,970,971,972,973])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_13 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_13 = true := by decide +kernel
def h0Block8_14 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,19,220],[1,6,8,9,13,15,24,349,670,704,753,757,758,936,949,950,951,952,953,976,977,978]),([0,1,2,3,4,5,19,221],[1,6,8,9,13,15,24,349,669,670,673,674,704,753,757,936,955,956,957,958,959,960,976,979]),([0,1,2,3,4,5,16,190],[0,1,8,13,14,15,24,144,154,646,674,759,760,761,762,763,934,935,936,937,940,941,961,975]),([0,1,2,3,4,5,226],[0,6,8,9,11,12,14,15,16,646,753,937,980,981,982,983,984]),([0,1,2,3,4,5,20,161],[1,6,8,11,12,13,23,24,87,91,395,397,398,404,415,523,525,530,542,987,988,989,990,991]),([0,1,2,3,4,5,16,122],[0,6,8,11,13,14,23,24,103,398,784,875,876,877,879,880,934,935,936,937,940,941,961,985,992,993]),([0,1,2,3,4,5,20,221],[1,6,8,11,12,13,15,23,91,397,398,404,415,530,542,784,936,955,956,957,958,959,960,994]),([0,1,2,3,4,5,16,128],[0,6,8,11,13,14,15,23,87,144,317,415,417,419,420,421,646,934,935,936,937,941,961,986]),([0,1,2,3,4,5,229],[0,1,9,12,14,15,16,23,24,530,940,995,996,997,998,999,1000]),([0,1,2,3,4,5,22,161],[1,6,8,11,12,13,23,24,87,91,395,428,429,432,441,506,523,525,552,557,988,989,990,1003,1004]),([0,1,2,3,4,5,16,132],[0,1,8,11,13,14,23,24,103,429,784,892,893,894,897,898,934,935,936,937,941,961,993,1001,1005,1006]),([0,1,2,3,4,5,22,221],[1,6,8,11,12,13,15,23,91,428,429,432,441,506,552,557,784,936,955,956,958,959,960,979,1007])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_14 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_14 = true := by decide +kernel
def h0Block8_15 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,16,136],[0,1,8,11,13,14,15,23,87,144,154,441,558,559,560,561,646,934,935,936,937,941,961,1002]),([0,1,2,3,4,5,230],[0,8,9,11,12,14,15,16,23,24,552,937,1008,1009,1010,1011,1012]),([0,1,2,3,4,5,32,73],[4,6,8,9,13,15,16,23,24,123,349,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028]),([0,1,2,3,4,5,227],[0,6,8,9,11,12,13,14,15,16,24,91,317,506,646,753,758,981,1029,1030]),([0,1,2,3,4,5,16,46],[0,6,8,11,13,14,18,23,24,254,602,646,919,920,923,924,925,934,935,936,940,941,961,1033,1034]),([0,1,2,3,4,5,28,221],[8,9,11,12,13,15,17,18,22,23,24,25,28,35,136,151,602,936,955,956,957,959,960,979,1035]),([0,1,2,3,4,5,16,50],[0,8,11,13,14,15,23,24,27,28,145,156,157,158,159,646,934,935,936,937,940,941,961,1032]),([0,1,2,3,4,5,231],[0,1,6,9,12,14,15,16,23,136,1036,1037,1038,1039,1040]),([0,1,2,3,4,5,26,161],[1,6,8,13,15,16,24,145,154,395,523,525,817,818,819,821,822,824,988,989,990,1041,1042]),([0,1,2,3,4,5,27,161],[1,6,8,13,15,16,24,145,317,395,523,525,827,828,829,831,832,834,988,989,990,1046,1047]),([0,1,2,3,4,5,107,161],[1,6,8,13,24,91,145,254,523,525,646,989,990,1048,1049,1050,1051,1052,1053]),([0,1,2,3,4,5,76,161],[1,6,8,13,24,91,129,145,506,523,525,646,989,990,1054,1055,1056,1057,1058])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_15 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_15 = true := by decide +kernel
def h0Block8_16 : List NodeSpec := nodesWithIdentity [([0,1,3,4,5,32,161],[8,13,16,24,91,523,525,1018,1043,1059]),([0,1,2,3,4,5,16,76],[1,6,8,9,13,24,129,144,646,934,935,936,937,940,941,961,1054,1055,1056,1057,1058]),([0,1,2,3,4,5,224],[1,6,8,9,11,12,13,15,16,1064]),([0,1,2,3,4,5,225],[1,6,8,11,12,13,15,16,1065]),([1,2,3,4,5,13,78],[6,8,11,23,24,196,1066,1067,1068,1069,1070]),([0,1,2,3,4,5,39,78],[6,8,13,14,15,16,24,131,190,196,219,391,960,1067,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081]),([0,1,2,3,4,5,17,38,78],[6,80,84,85,219,506,631,632,637,643,645,724]),([0,1,2,3,4,5,17,78,188],[6,8,196,219,368,631,632,636,645,666,724,1067,1084]),([0,1,2,3,4,5,78,180],[6,8,14,23,131,190,196,219,368,391,506,602,643,1067,1071,1072,1076,1085,1086,1087,1088,1089,1090,1091,1093,1094]),([0,1,2,3,4,5,17,211],[0,6,8,9,13,14,23,24,144,368,602,631,632,637,643,645,648,649,724,848,856,1095,1096,1097]),([0,1,2,3,4,5,17,78,211],[6,8,196,337,637,724,848,856,1076,1095]),([0,1,2,3,4,5,78,184],[0,6,8,15,16,24,131,190,196,219,317,337,505,506,602,648,652,660,661,662,663,1067,1070,1071,1072,1076])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_16 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_16 = true := by decide +kernel
def h0Block8_17 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,17,232],[0,6,8,9,15,16,23,24,41,368,631,632,637,643,645,648,649,652,724,1071,1093,1098,1099,1100,1101]),([0,1,2,3,4,5,17,78,232],[6,8,190,196,648,724,1071,1098,1101]),([0,1,2,3,4,5,17,185],[1,9,130,632,637,643,645,649,652,724,1105]),([0,1,2,3,4,5,78,101],[0,6,9,60,131,196,242,279,291,422,1067,1071,1076,1106,1107,1108,1109,1110]),([0,1,2,3,4,5,17,38,101],[6,80,84,85,270,291,506,631,632,645]),([0,1,2,3,4,5,101,176],[0,6,11,12,26,242,279,291,506,632,850,942,1107,1108,1109,1110,1111,1112,1113,1114,1115]),([0,1,2,3,4,5,101,181],[0,6,8,13,14,242,279,291,391,506,602,637,650,736,737,1107,1108,1109,1110,1116,1117,1118,1119,1120]),([0,1,2,3,4,5,17,223],[0,1,6,8,9,13,14,24,26,59,130,270,324,391,602,631,632,637,643,645,646,648,649,724,940,966,1121]),([0,1,2,3,4,5,101,184],[0,6,8,15,16,242,279,291,317,602,648,652,660,661,662,663,1107,1108,1109,1110]),([0,1,2,3,4,5,17,58],[1,6,8,9,11,13,24,80,190,270,283,632,637,645,648,649,724,1123,1124,1125,1126,1127,1128]),([0,1,2,3,4,5,38,182],[6,11,12,13,14,15,24,80,84,85,88,91,270,506,648,653,654,655,656,743,1129]),([0,1,2,3,4,5,38,184],[6,11,12,13,14,15,24,47,80,84,85,88,89,92,190,317,505,648,652,660,661,662,663,1129])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_17 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_17 = true := by decide +kernel
def h0Block8_18 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,17,64],[1,6,9,11,13,15,23,24,89,106,107,110,111,112,505,631,632,637,645,648,649,724,1122]),([0,1,2,3,4,5,233],[0,1,8,9,12,14,15,16,84,645,1082,1083,1131,1132,1133]),([0,1,2,3,4,5,17,233],[1,9,11,84,631,632,637,645,648,649,724,1082,1083,1131,1132,1133]),([0,1,2,3,4,5,139],[0,1,6,8,9,11,12,14,15,16,1142]),([0,1,2,3,4,5,183],[0,1,6,8,9,11,12,13,14,16,1143]),([0,1,2,3,4,5,36,39],[1,8,13,14,15,16,24,305,324,343,355,391,440,1074,1077,1078,1079,1080,1081,1144,1145,1146,1147,1148]),([0,1,2,3,4,5,19,58],[1,6,8,9,11,13,24,80,190,283,349,670,673,674,704,753,757,1125,1126,1127,1128,1150,1151]),([0,1,3,4,5,19,60],[6,11,13,23,24,47,95,145,704,1152,1153,1154]),([0,1,2,3,4,5,38,190],[1,11,12,13,14,15,24,47,80,84,85,88,89,91,92,145,154,190,254,674,759,760,761,762,1155,1156]),([0,1,2,3,4,5,19,64],[1,6,9,11,13,15,23,24,89,106,107,110,111,112,221,349,669,670,673,674,704,753,757,1149]),([0,1,2,3,4,5,244],[0,6,8,9,11,12,14,15,16,92,349,704,1157,1158,1159,1160]),([0,1,2,3,4,5,131],[0,6,8,9,11,12,13,14,15,16,24,91,144,145,401,403,424,1169,1170,1171])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_18 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_18 = true := by decide +kernel
def h0Block8_19 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,30,128],[6,9,11,13,14,15,23,24,36,37,49,50,61,63,168,182,317,415,417,418,419,420,1173]),([0,1,2,3,4,5,20,63],[1,6,11,12,13,15,24,26,63,145,184,185,187,188,189,190,397,398,404,415,530,541,542,1172]),([0,1,2,3,4,5,245],[0,1,8,9,12,14,15,16,40,61,1174,1175,1176,1177,1178]),([0,1,2,3,4,5,126],[0,6,8,9,11,12,13,14,15,16,24,405,1179,1180,1181,1182,1183]),([0,1,2,3,4,5,129],[0,6,8,11,13,14,15,16,1184]),([0,1,2,3,4,5,31,112],[1,8,9,11,13,14,24,103,190,306,324,363,440,712,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195]),([0,1,2,3,4,5,32,112],[1,8,9,11,15,16,24,26,306,324,363,1018,1020,1021,1026,1027,1028,1185,1188,1189,1191,1196,1197,1198,1199]),([0,1,2,3,4,5,138],[0,1,8,9,11,12,13,14,15,16,24,144,401,402,444,1200,1201,1202]),([0,1,2,3,4,5,39,112],[1,8,11,13,14,15,16,144,306,324,363,440,1074,1077,1078,1079,1080,1081,1185,1188,1189,1191,1203]),([0,1,2,3,4,5,30,136],[1,9,11,13,14,15,23,24,36,37,49,50,61,63,154,168,182,441,558,559,560,1205,1206]),([0,1,2,3,4,5,22,63],[1,6,11,12,13,15,24,63,145,184,185,186,188,189,190,428,429,432,441,506,552,556,557,1204]),([0,1,2,3,4,5,246],[0,6,8,9,11,12,14,15,16,37,506,1207,1208,1209,1210])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_19 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_19 = true := by decide +kernel
def h0Block8_20 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,134],[0,1,8,9,11,12,13,14,15,16,24,433,1211,1212,1213,1214]),([0,1,2,3,4,5,167],[0,1,8,11,13,14,15,16,1215]),([1,2,3,4,5,13,93],[6,8,11,13,23,231,1068,1216,1217,1218,1219]),([0,1,2,3,4,5,32,93],[6,8,9,13,15,16,23,24,133,190,231,1018,1020,1021,1023,1026,1027,1028,1196,1217,1219,1220,1221,1222,1223,1224]),([0,1,2,3,4,5,33,93],[6,8,9,13,15,16,23,24,133,145,190,231,349,1217,1219,1220,1221,1224,1225,1226,1227,1228,1229,1230,1231,1232]),([0,1,2,3,4,5,147],[0,6,8,9,11,12,13,14,15,16,23,24,368,403,408,440,477,1233,1234,1235]),([0,1,2,3,4,5,23,32,93],[6,440,447,461,567,571,1018,1020,1023]),([0,1,2,3,4,5,23,147],[0,6,8,9,13,14,23,24,144,368,403,408,440,447,448,451,458,461,477,567,571,1233,1234,1235]),([0,1,2,3,4,5,23,247],[0,6,8,13,14,15,16,23,144,368,440,447,448,451,458,461,462,567,571,1220,1236,1237,1238,1239]),([0,1,2,3,4,5,249],[0,1,8,9,12,14,15,16,22,440,1243,1244,1245,1246,1247]),([0,1,2,3,4,5,143],[0,6,8,9,11,12,13,15,16,1254]),([0,1,2,3,4,5,145],[0,6,8,11,12,13,15,16,1255])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_20 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_20 = true := by decide +kernel
def h0Block8_21 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,32,115],[1,8,9,13,15,16,23,24,307,324,379,1018,1020,1021,1026,1027,1028,1196,1199,1256,1257,1258,1259,1260,1261]),([0,1,2,3,4,5,33,115],[1,8,9,13,15,16,23,24,145,307,324,379,1226,1228,1229,1230,1231,1232,1256,1259,1260,1261,1262,1263]),([0,1,2,3,4,5,152],[0,1,8,9,11,12,13,14,15,16,23,24,368,402,408,495,1264,1265,1266]),([0,1,2,3,4,5,28,150],[1,9,11,12,13,15,17,18,22,24,25,28,136,151,153,154,190,254,492,583,584,585,587,1268,1269]),([0,1,2,3,4,5,25,50],[1,6,11,13,14,15,23,24,28,145,155,156,157,158,159,254,391,483,484,487,491,492,579,582,1267]),([0,1,2,3,4,5,250],[0,6,8,9,11,12,14,15,16,18,254,1270,1271,1272,1273]),([0,1,2,3,4,5,118,149],[0,1,8,13,23,24,145,324,368,384,484,689,690,694,786,1274,1275,1276,1277]),([0,1,2,3,4,5,75,149],[0,1,8,13,24,59,91,130,145,324,484,689,690,694,695,786,1278,1279,1280]),([0,1,2,3,4,5,170],[0,1,8,11,12,13,15,16,1281]),([0,1,2,3,4,251],[8,15,23,1292,1293,1294,1295,1296]),([0,1,2,3,4,5,30,66],[0,1,6,8,9,13,14,23,24,36,37,40,49,50,61,62,63,75,168,182,349,368,391,1297,1298,1299,1300,1301]),([0,1,2,3,4,30,251],[8,23,61,168,182,1292,1293,1294,1295,1296,1302,1303])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_21 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_21 = true := by decide +kernel
def h0Block8_22 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,30,251],[0,9,13,14,16,36,37,40,49,50,61,63,73,168,182,1292]),([0,1,2,3,4,5,30,254],[6,9,13,14,16,36,37,40,49,50,61,63,73,154,168,182,1313]),([0,1,2,3,4,5,30,83],[1,9,13,14,16,36,37,40,49,50,63,73,168,182,317,809]),([0,1,2,3,4,5,103],[1,6,8,9,11,12,13,14,15,16,24,1125,1317,1318,1319,1320,1321]),([0,1,2,3,4,5,91],[0,6,8,9,11,12,13,14,15,16,24,508,1322,1323,1324,1325,1326]),([0,1,2,3,4,5,71],[0,1,6,8,11,13,15,16,292])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_22 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_22 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1 ++ h0Block8_2 ++ h0Block8_3 ++ h0Block8_4 ++ h0Block8_5 ++ h0Block8_6 ++ h0Block8_7 ++ h0Block8_8 ++ h0Block8_9 ++ h0Block8_10 ++ h0Block8_11 ++ h0Block8_12 ++ h0Block8_13 ++ h0Block8_14 ++ h0Block8_15 ++ h0Block8_16 ++ h0Block8_17 ++ h0Block8_18 ++ h0Block8_19 ++ h0Block8_20 ++ h0Block8_21 ++ h0Block8_22
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Nodes8 = true := by
  unfold h0Nodes8 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0Test8_0,h0Test8_1⟩,h0Test8_2⟩,h0Test8_3⟩,h0Test8_4⟩,h0Test8_5⟩,h0Test8_6⟩,h0Test8_7⟩,h0Test8_8⟩,h0Test8_9⟩,h0Test8_10⟩,h0Test8_11⟩,h0Test8_12⟩,h0Test8_13⟩,h0Test8_14⟩,h0Test8_15⟩,h0Test8_16⟩,h0Test8_17⟩,h0Test8_18⟩,h0Test8_19⟩,h0Test8_20⟩,h0Test8_21⟩,h0Test8_22⟩
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket7Ok h0Check8
def h0Block9_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,9],[0,7,8,9,11,12,13,14,15,16]),([0,1,2,3,4,5,6,28],[0,1,2,3,4,5,6,8,9,11,12,17,18,19,20,21,22,23,24,25,26,27,28,29,35]),([0,1,2,3,4,5,6,30],[0,1,2,3,4,5,6,8,9,13,14,21,24,36,37,38,39,40,41,49,50,60,61,62,63,64]),([0,1,2,3,4,5,47],[0,2,6,8,9,11,12,13,14,15,16,24,76,77,78,79,90]),([0,1,2,3,4,5,6,38],[0,1,2,3,4,5,6,8,11,12,13,14,21,23,46,47,80,84,89,92,93,105]),([0,1,2,3,4,5,48],[0,4,6,8,9,11,12,13,14,15,16,26,120,121,122,123]),([0,1,2,3,4,5,7,28],[0,1,6,8,9,11,12,17,18,23,24,25,26,28,41,131,132,133,134,135,136,137,138]),([0,1,2,3,4,5,7,30],[0,1,6,8,9,13,14,24,36,37,41,49,50,60,61,63,131,132,133,134,138,160,167,168,169]),([0,1,2,3,4,5,77],[0,1,8,9,11,12,13,14,15,16,24,91,131,141,144,179,196,197]),([0,1,2,3,4,5,7,38],[0,1,6,8,11,12,13,14,23,41,47,80,85,89,92,131,132,133,134,138,206,207]),([0,1,2,3,4,5,79],[0,1,8,9,11,12,13,14,15,16,26,133,231,232,233,234]),([0,1,2,3,4,5,80],[0,1,8,9,11,12,13,14,15,16,134])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,8,28],[0,1,6,8,9,11,12,17,18,24,25,26,28,29,242,243,244,245,246,247,253,254,255]),([0,1,2,3,4,5,8,30],[0,1,6,8,9,13,14,24,36,37,49,50,60,61,63,64,242,243,244,245,253,256,262,263]),([0,1,2,3,4,5,95],[0,1,9,11,12,13,14,15,16,24,90,242,275,276,277]),([0,1,2,3,4,5,8,38],[0,1,6,8,11,12,13,14,47,80,89,92,105,242,243,244,245,253,254,265,282]),([0,1,2,3,4,5,96],[0,1,9,11,12,13,14,15,16,26,244,297,298,299]),([0,1,2,3,4,5,9,28],[0,1,6,7,8,9,11,12,17,18,22,23,24,25,26,27,28,41,136,305,306,307,308,309,310,324]),([0,1,2,3,4,5,9,30],[0,1,6,7,8,9,13,14,24,36,37,40,41,49,50,60,61,63,168,305,306,307,310,324,325,326,327,337]),([0,1,2,3,4,5,34],[6,8,11,12,13,14,15,16,23,305,338,339,340,341,342]),([0,1,2,3,4,5,35],[0,1,6,8,9,10,11,12,13,14,15,16,24,305,343,344,345,346,349]),([0,1,2,3,4,5,9,35],[0,1,6,7,8,9,10,23,305,306,307,310,324,343,344,345,346,349]),([0,1,2,3,4,5,9,38],[0,1,6,7,8,11,12,13,14,23,41,47,80,84,85,89,92,305,306,307,310,324,347,350]),([0,1,2,3,4,5,9,40],[0,1,6,7,8,11,12,41,305,306,307,310,324,363,364,365,366,367,368])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Block9_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,41],[6,8,9,11,12,13,15,16,23,307,369,370,371,372,373]),([0,1,2,3,4,5,42],[0,1,6,8,9,11,12,13,14,15,16,26,307,379,380,381,382,383]),([0,1,2,3,4,5,9,42],[0,1,6,7,8,14,23,305,306,307,310,324,327,379,380,381,382,383,391]),([0,1,2,3,4,5,43],[6,7,8,9,11,12,13,14,15]),([0,1,2,3,4,5,44],[0,1,7,8,9,11,12,13,14,15,16]),([0,1,2,3,4,5,10,20],[0,1,6,8,9,11,12,24,26,103,394,395,396,397,398,399,400,401,402,403,404,415,416]),([0,1,2,3,4,5,10,22],[0,1,6,8,9,11,12,24,26,103,324,394,395,396,402,422,428,429,430,431,432,441,442]),([0,1,2,3,4,5,10,23],[0,1,6,8,9,13,14,24,41,394,395,396,401,402,403,440,447,448,449,450,451,458,461,462]),([0,1,2,3,4,5,10,25],[0,1,6,8,9,13,14,24,324,394,395,396,401,402,422,483,484,485,486,487,491,492,493]),([0,1,2,3,4,5,37],[0,6,8,9,11,12,13,14,15,16,130,305,344,391,498,506]),([0,1,2,3,4,5,10,38],[0,8,9,11,12,13,14,24,47,80,89,92,103,105,394,395,396,401,402,507]),([0,1,2,4,5,123],[0,11,394,454,459,460])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
def h0Block9_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,124],[0,1,6,8,9,11,12,13,14,15,16,26,395,522,523,524]),([0,1,2,3,4,5,11,20],[0,1,6,8,9,11,12,23,24,26,41,90,103,397,398,404,415,526,527,528,529,530,531,532,533,534]),([0,1,2,3,4,5,11,22],[0,1,6,8,9,11,12,23,24,26,41,90,103,428,429,432,441,526,527,528,529,551,552,553]),([0,1,2,3,4,5,11,23],[0,1,6,8,9,13,14,24,41,60,90,270,440,447,448,451,458,461,526,527,528,529,533,534,567,568,569]),([0,1,2,3,4,5,11,25],[0,1,6,8,9,13,14,24,41,60,90,391,483,484,487,491,492,526,527,528,529,533,578,579,580]),([0,1,2,3,4,5,11,102],[0,1,6,8,9,23,60,90,144,242,368,526,527,528,529,533,593,594,595,596]),([0,1,2,3,4,5,69],[0,2,6,8,9,11,12,13,14,15,16,79,391,505,506,597,598,602]),([0,1,2,3,4,5,11,69],[0,1,2,8,9,23,60,79,90,144,368,526,527,528,529,533,534,596,597,598,603]),([0,1,2,3,4,5,11,38],[0,8,9,11,12,13,14,23,24,47,80,85,89,90,92,103,526,527,528,529,533,604]),([0,1,2,3,4,5,11,162],[0,8,9,11,12,60,90,368,526,527,528,529,533,616,617,618,619]),([0,1,2,3,4,5,54],[1,6,8,11,12,13,15,16,23,36,620,621,622,623]),([0,1,2,3,4,5,163],[0,1,6,8,9,11,12,13,14,15,16,26,527,624,625,626,627])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
def h0Block9_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,11,163],[0,8,9,14,23,90,144,526,527,528,529,533,544,624,625,626,627]),([0,1,2,3,4,5,164],[1,6,8,11,12,13,14,15,130,528]),([0,1,2,3,4,5,165],[0,1,6,8,9,11,12,13,14,16,528]),([0,1,2,3,4,5,12,17],[0,1,6,8,9,11,12,24,26,103,628,629,630,631,632,633,634,635,636,637,648,652]),([0,1,2,3,4,5,12,19],[0,1,6,8,9,11,12,24,26,103,255,324,422,628,629,630,635,669,670,671,672,673,674,675]),([0,1,2,3,4,5,12,23],[0,1,6,8,11,12,13,14,26,255,368,440,447,448,451,461,462,628,629,630,635,636,651,680,681]),([0,1,2,3,4,5,12,25],[0,1,6,8,11,12,13,14,324,422,483,484,487,492,493,628,629,630,635,651,687,688]),([0,1,2,3,4,5,113],[0,6,9,11,12,13,14,15,16,103,130,306,364,391,651,700]),([0,1,2,3,4,5,12,30],[0,8,9,11,12,13,14,24,26,36,37,49,60,61,63,64,103,628,629,630,635,651,658,706]),([0,1,2,3,4,5,174],[0,1,6,9,11,12,13,14,15,16,24,103,130,144,526,617,651,711]),([0,1,2,3,4,5,177],[0,1,6,9,11,12,13,14,15,16,255,629,641,644,647]),([0,1,2,3,4,5,14,17],[0,1,6,8,9,11,12,24,26,103,631,632,637,645,648,720,721,722,723,724,725,726,727])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
def h0Block9_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,14,19],[0,1,6,8,9,11,12,24,26,103,255,349,669,670,673,674,704,720,721,722,723,752,753,754]),([0,1,2,3,4,5,14,23],[0,1,6,8,11,12,13,14,26,59,255,440,447,448,451,458,461,567,720,721,722,723,727,769,770]),([0,1,2,3,4,5,14,25],[0,1,6,8,11,12,13,14,59,254,483,484,487,491,492,579,720,721,722,723,782,783]),([0,1,2,3,4,5,196],[0,6,8,9,11,12,13,14,15,16,723,794,795,796,797,798]),([0,1,2,3,4,5,14,30],[0,8,9,11,12,13,14,24,26,36,37,49,50,61,63,103,168,720,721,722,723,744,802]),([0,1,2,3,4,5,140],[0,1,6,8,9,11,12,13,14,15,16,24,103,144,394,459,771,773,784]),([0,1,2,3,4,5,197],[0,1,6,8,9,11,12,13,14,15,16,255,721,729,730,733,735]),([0,1,2,3,4,5,200],[0,1,6,9,11,12,13,14,15,16,722]),([0,1,2,3,4,5,15,17],[0,1,6,8,9,13,14,24,631,632,637,645,648,652,842,843,844,845,846,847,848,849]),([0,1,2,3,4,5,15,19],[0,1,6,8,9,13,14,24,324,422,669,670,673,674,675,704,842,843,844,847,849,861,862]),([0,1,2,3,4,5,15,20],[0,1,6,8,11,12,13,14,26,397,398,404,415,416,842,843,844,847,848,849,867,868]),([0,1,2,3,4,5,15,22],[0,1,6,8,11,12,13,14,324,422,428,429,432,441,442,842,843,844,847,888,889])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
def h0Block9_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,116],[0,6,8,9,11,12,13,14,15,16,27,130,307,349,380,506,904]),([0,1,2,3,4,5,15,28],[0,8,9,11,12,13,14,17,18,24,25,26,27,28,29,35,842,843,844,847,849,918]),([0,1,2,3,4,5,175],[0,1,6,8,9,11,12,13,14,15,16,24,90,91,130,527,625,874]),([0,1,2,3,4,5,16,17],[0,1,6,8,9,13,14,24,60,270,631,632,637,645,646,648,724,934,935,936,937,938,939,940,941]),([0,1,2,3,4,5,16,19],[0,1,6,8,9,13,14,24,60,349,646,669,670,673,674,704,753,934,935,936,937,941,974,975]),([0,1,2,3,4,5,16,20],[0,1,6,8,11,12,13,14,23,397,398,404,415,530,934,935,936,937,940,941,985,986]),([0,1,2,3,4,5,16,22],[0,1,6,8,11,12,13,14,23,428,429,432,441,552,934,935,936,937,1001,1002]),([0,1,2,3,4,5,16,105],[0,1,6,8,14,23,60,244,368,646,934,935,936,937,941,954,1013,1014,1015]),([0,1,2,3,4,5,73],[0,4,6,8,9,11,12,14,15,16,27,123,349,505,506,1016,1017]),([0,1,2,3,4,5,16,73],[0,1,4,8,14,23,60,123,368,646,934,935,936,937,940,941,954,1016,1017,1031]),([0,1,2,3,4,5,16,28],[0,8,9,11,12,13,14,17,18,23,24,25,27,28,136,934,935,936,937,941,1032]),([0,1,2,3,4,5,161],[0,1,6,8,9,11,12,14,15,16,24,87,91,145,395,523,525,988])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_6 = true := by decide +kernel
def h0Block9_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,16,161],[0,8,9,14,23,368,395,523,525,646,934,935,936,937,941,954,988,1060]),([0,1,2,3,4,5,16,179],[0,8,11,12,14,60,103,368,629,644,646,934,935,936,937,941,954,993,1061,1062,1063]),([0,1,2,3,4,5,220],[1,6,8,9,11,12,13,15,936]),([0,1,2,3,4,5,221],[0,1,6,8,9,11,12,14,15,16,936]),([0,1,2,3,4,5,78],[0,1,6,8,9,11,12,13,14,15,16,23,41,131,196,368,1071,1072]),([0,1,2,3,4,5,17,78],[0,1,6,8,9,23,41,131,196,368,391,505,506,602,631,632,637,645,648,652,724,1071,1072]),([0,1,2,3,4,5,17,101],[0,1,6,8,9,59,242,391,506,631,632,637,645,646,648,652,1107,1108]),([0,1,2,3,4,5,17,38],[1,6,9,11,12,13,14,23,24,47,80,84,89,92,103,631,632,637,645,648,1122]),([0,1,2,3,4,5,17,176],[1,6,9,11,12,23,26,506,631,632,637,645,648,942,1112,1113,1114]),([0,1,2,3,4,5,55],[0,6,8,11,12,13,15,16,26,37,1138,1139,1140,1141]),([0,1,2,3,4,5,181],[0,1,6,8,9,11,12,13,14,15,16,26,637,736,1117,1118,1120]),([0,1,2,3,4,5,17,181],[1,6,9,14,26,41,391,602,631,632,637,643,645,648,736,1117,1118,1120])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_7 = true := by decide +kernel
def h0Block9_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,182],[0,6,8,11,12,13,14,15,648]),([0,1,2,3,4,5,184],[0,1,6,8,9,11,12,13,14,16,648]),([0,1,2,3,4,5,36],[0,1,8,9,11,12,13,14,15,16,23,41,305,343,368,1144]),([0,1,2,3,4,5,19,38],[1,6,9,11,12,13,14,23,24,47,80,89,92,103,349,669,670,673,674,704,1149]),([0,1,2,3,4,5,189],[0,1,6,8,9,11,12,13,14,15,16,26,673,1161,1162,1163]),([0,1,2,3,4,5,190],[0,1,6,8,9,11,12,13,14,16,674]),([0,1,2,3,4,5,121],[0,1,6,8,9,11,12,13,14,15,16,41,397,1164,1165,1166,1167,1168]),([0,1,2,3,4,5,20,30],[1,6,9,11,12,13,14,23,24,26,36,37,40,41,49,50,61,63,103,397,398,404,415,541,1172]),([0,1,2,3,4,5,122],[0,1,6,8,9,11,12,13,14,15,16,24,103,398,875,877,879,880]),([0,1,2,3,4,5,125],[0,1,6,8,9,11,12,13,14,15,16,41,404,405,407,410,411]),([0,1,2,3,4,5,128],[0,1,8,9,11,12,13,14,15,16,415]),([0,1,2,3,4,5,112],[0,1,8,9,11,12,13,14,15,16,41,103,306,363,1185])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_8 = true := by decide +kernel
def h0Block9_9 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,22,30],[1,6,9,11,12,13,14,23,24,26,36,37,41,49,61,63,103,428,429,432,441,556,1204]),([0,1,2,3,4,5,132],[0,1,8,9,11,12,13,14,15,16,24,103,429,892,897,898]),([0,1,2,3,4,5,133],[0,1,8,9,11,12,13,14,15,16,41,432,433,437,438]),([0,1,2,3,4,5,136],[0,1,8,9,11,12,13,14,15,16,441]),([0,1,2,3,4,5,93],[0,1,6,8,9,11,12,14,15,16,23,133,231,368,1220,1221]),([0,1,2,3,4,5,23,93],[0,1,6,8,14,23,26,133,231,349,368,440,447,448,451,458,461,462,506,567,1220,1221]),([0,1,2,3,4,5,23,104],[0,1,6,8,14,26,41,59,90,244,349,440,447,448,451,458,461,462,506,1240,1241]),([0,1,2,3,4,5,23,28],[1,6,9,11,12,13,14,17,18,22,23,24,25,26,27,28,35,41,255,440,447,448,451,458,461,1242]),([0,1,2,3,4,5,139],[0,1,6,8,9,11,12,14,15,16,24,255,349,448,1142,1248,1249,1250]),([0,1,2,3,4,5,23,139],[1,6,9,14,26,349,440,447,448,451,458,461,1142,1248,1249,1250]),([0,1,2,3,4,5,23,135],[1,6,11,12,14,23,27,41,103,432,437,440,447,448,451,458,461,506,774,1251,1252,1253]),([0,1,2,3,4,5,141],[0,6,8,9,11,12,13,15,461])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_9 = true := by decide +kernel
def h0Block9_10 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,142],[0,1,6,8,9,11,12,14,15,16,461]),([0,1,2,3,4,5,115],[0,1,8,9,11,12,13,14,15,16,23,307,368,379,1256]),([0,1,2,3,4,5,25,28],[1,6,9,11,12,13,14,17,18,23,24,25,28,41,254,483,484,487,491,492,1267]),([0,1,2,3,4,5,149],[0,1,6,8,9,11,12,13,14,15,16,24,91,484,689,693,694]),([0,1,2,3,4,5,150],[0,1,6,8,9,11,12,13,14,15,16,492]),([0,1,2,3,4,5,45],[1,6,8,9,11,12,13,14,15,16,17,41,1282,1283,1284,1285]),([0,1,2,3,4,5,46],[0,6,8,9,11,12,13,14,15,16,18,919,923,924,925]),([0,1,2,3,4,5,49],[0,1,6,8,9,11,12,13,15,16,25,27,41,255,1286,1287,1288]),([0,1,2,3,4,5,50],[0,1,6,8,9,11,12,13,14,16,28]),([0,1,2,3,4,5,52],[1,6,8,9,11,12,14,15,16,23,36,1289,1290,1291,1292]),([0,1,2,3,4,5,30,52],[0,8,9,13,14,23,26,36,37,49,50,61,63,168,1289,1290,1291,1292]),([0,1,2,3,4,5,30,53],[0,8,9,13,14,26,36,37,41,49,50,61,63,64,324,1306,1307,1308,1309])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_10 = true := by decide +kernel
def h0Block9_11 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,30,56],[1,6,9,13,14,26,36,37,49,50,60,61,63,254,324,1310,1311,1312,1313]),([0,1,2,3,4,5,57],[0,6,8,9,11,12,14,15,16,37,60,803,807,808,809]),([0,1,2,3,4,5,30,57],[1,6,9,13,14,26,36,37,40,49,50,60,61,63,803,807,808,809]),([0,1,2,3,5,30,38],[9,12,13,14,41,47,49,50,51]),([0,1,2,3,4,5,30,61],[9,11,12,13,14,23,36,37,49,50,60,61,63,91,254,1314,1315,1316]),([0,1,2,3,4,5,62],[0,1,6,8,11,12,13,15,63,73]),([0,1,2,3,4,5,63],[0,1,6,8,9,11,12,13,14,16,63]),([0,1,2,3,4,5,58],[1,6,8,9,11,12,14,15,16,80,1125,1126,1127,1128]),([0,1,2,3,4,5,59],[0,6,8,9,11,12,14,15,16,92,508,511,512,513]),([0,1,2,3,4,5,60],[0,1,6,8,9,11,12,14,15,16,24,47,99,100,101,103]),([0,1,2,3,4,5,64],[0,1,6,8,9,11,12,14,15,16,89])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_11 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1 ++ h0Block9_2 ++ h0Block9_3 ++ h0Block9_4 ++ h0Block9_5 ++ h0Block9_6 ++ h0Block9_7 ++ h0Block9_8 ++ h0Block9_9 ++ h0Block9_10 ++ h0Block9_11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := by
  unfold h0Nodes9 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0Test9_0,h0Test9_1⟩,h0Test9_2⟩,h0Test9_3⟩,h0Test9_4⟩,h0Test9_5⟩,h0Test9_6⟩,h0Test9_7⟩,h0Test9_8⟩,h0Test9_9⟩,h0Test9_10⟩,h0Test9_11⟩
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,6],[0,1,2,3,4,5,6,9,11,12,14,16,130]),([0,1,2,3,4,5,7],[0,1,8,9,11,12,14,16,131,132,133,134]),([0,1,2,3,4,5,8],[0,1,9,11,12,14,16,130,242,243,244,245]),([0,1,2,3,4,5,9],[0,1,6,7,8,9,11,12,14,16,305,306,307]),([0,1,2,3,4,5,10],[0,1,9,11,12,14,16,130,394,395,396]),([0,1,2,3,4,5,11],[0,1,8,9,11,12,14,16,526,527,528]),([0,1,2,3,4,5,12],[0,1,9,12,14,16,130,628,629,630]),([0,1,2,3,4,5,14],[0,1,8,9,11,12,14,16,720,721,722]),([0,1,2,3,4,5,15],[0,1,9,11,12,14,16,130,842,843,844]),([0,1,2,3,4,5,16],[0,1,8,9,11,12,14,16,934,935,936]),([0,1,2,3,4,5,17],[0,1,6,9,11,12,14,16,632,637,648]),([0,1,2,3,4,5,19],[0,1,9,11,12,14,16,670,673,674])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Block10_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,20],[0,1,6,9,11,12,14,16,398,404,415]),([0,1,2,3,4,5,22],[0,1,9,12,14,16,429,432,441]),([0,1,2,3,4,5,23],[0,1,6,9,11,12,14,16,448,451,461]),([0,1,2,3,4,5,25],[0,1,9,11,12,14,16,484,487,492]),([0,1,2,3,4,5,28],[0,1,9,11,12,14,16,25,28]),([0,1,2,3,4,5,30],[0,1,9,11,12,13,14,16,49,63]),([0,1,2,3,4,5,38],[0,1,9,11,12,14,16,47,89])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_1 = true := by decide +kernel
def h0Nodes10 : List NodeSpec := h0Block10_0 ++ h0Block10_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Nodes10 = true := by
  unfold h0Nodes10 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h0Test10_0,h0Test10_1⟩
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket9Ok h0Check10
def h0Block11_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[9,12,14,16])]
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
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,6,14),(VAR 4,5,21),(VAR 5,3,35)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276676776 * 2 ^ 32 + 4003512448) ||| ((4276676776 * 2 ^ 32 + 4003512448) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4276676776 * 2 ^ 32 + 4003512448) ||| ((4276676776 * 2 ^ 32 + 4003512448) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_47863
theorem PEqualNP.Outside.L_meta_47863 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 4003512448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4003512448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_47863.table2_of_lower (4276676776 * 2 ^ 32 + 4003512448) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_47863.low_root
    PEqualNP.Outside.L_meta_47863.wit PEqualNP.Outside.L_meta_47863.wo (by decide)
    PEqualNP.Outside.L_meta_47863.wit_mono PEqualNP.Outside.L_meta_47863.wit_eval s hcs
