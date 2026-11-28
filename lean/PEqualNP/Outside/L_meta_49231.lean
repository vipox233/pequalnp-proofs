import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_49231
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
lemma normPack_lt (f : Wire) : normPack f < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).isLt
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
lemma lower_count {roots : List Nat} {T : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (singles : Finset Nat) (ess : ∀ a ∈ singles, Essential T roots a) :
    Lower roots T (singles.card - 1) := by
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
  have hsub : singles ⊆ S := fun a ha' => raw_required run roots a sub (ess a ha')
  have hle := (Finset.card_le_card hsub).trans (live_size run)
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
def countCheck (roots : List Nat) (T L : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    decide (essPairs.map Prod.fst).Nodup &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2) &&
    decide (L ≤ essPairs.length - 1)
lemma count_of {roots T L essPairs} (ok : countCheck roots T L essPairs = true) :
    Lower roots T L := by
  simp only [countCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨hT, hR⟩, hnd⟩, hess⟩, hle⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hl := lower_count p1 p2 p3 hR' (essPairs.map Prod.fst).toFinset (fun a ha => by
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm))
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [hcard] at hl
  exact fun p bank hr hav => hle.trans (hl p bank hr hav)
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
def sliceCheck (z o zDrop : Nat) (raw : List Nat) (T : Nat) (freeRoots : List Nat) (qRoots : List Nat) (qGoal : Nat)
    (qL : Nat) (lEss : List (Nat × Nat × Nat)) (sliceL : Nat) : Bool :=
  let G := fixWord z o T
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    checkProper G && checkRoots freeRoots &&
    raw.all (fun a => freeIn freeRoots (fixWord z o a)) &&
    (if qGoal == 0 then
       decide (lEss.map Prod.fst).Nodup &&
       lEss.all (fun e => checkEss1 G freeRoots e.1 e.2.1 e.2.2) &&
       decide (sliceL ≤ lEss.length - 1)
     else
       liftCheck zDrop 0 freeRoots G qRoots qGoal lEss &&
       decide (sliceL ≤ qL + lEss.length))
lemma slice_of {z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL}
    (ok : sliceCheck z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL = true)
    (hPrior : qGoal ≠ 0 → Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) sliceL := by
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hz, ho⟩, hzo⟩, hGp⟩, hFR⟩, hcov⟩, htail⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  have hFR' := checkRoots_sound hFR
  refine ⟨fixRow z o, freeRoots, subcube_fixRow z o hz ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW]
  by_cases hq : qGoal = 0
  · simp only [hq, ite_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at htail
    have hl := lower_count g0 glt gb0 hFR' (lEss.map Prod.fst).toFinset (fun a ha => by
      obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact checkEss1_sound (htail.1.2 _ hm))
    have hcard : (lEss.map Prod.fst).toFinset.card = lEss.length := by
      rw [List.toFinset_card_of_nodup htail.1.1, List.length_map]
    rw [hcard] at hl
    exact fun p bank hr hav => htail.2.trans (hl p bank hr hav)
  · simp only [hq, ite_false, Bool.and_eq_true, decide_eq_true_eq] at htail
    have hl := lift_of htail.1 (hPrior hq)
    exact fun p bank hr hav => htail.2.trans (hl p bank hr hav)
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
def evalInput (r : Row) : Fin 7 → Bool := fun i => r.val.testBit i.val
def packInput (x : Fin 7 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    have h6 := Bool.toNat_le (x 6); omega⟩
lemma evalInput_packInput (x : Fin 7 → Bool) : evalInput (packInput x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 : Bool) (j : Fin 7),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
lemma var_testBit (i : Fin 7) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 127 := by
  let seeds : List SWire := (varsOf 127).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 127).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
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
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi7 : i < 7 := by simpa using hi2
      have hv : (varsOf 127)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 127)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi7⟩ r
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
    · have h := hev ⟨r, hr⟩
      simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]
    exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma replace_of_lower (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 127) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : ∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn : (Fin 7 → Bool) → Bool)
    (hEdgeT : ∀ r : Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  have hwEval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x := by
    intro x
    have hx := evalInput_packInput x
    rw [← hx]
    exact (hwEvalR (packInput x)).trans (hEdgeT (packInput x)).symm
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hlt : gates.countP isBin < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput r)).trans (hEdgeT r))
    have hnd : S.toList.Nodup := Finset.nodup_toList S
    have hrun := live_to_run hlive S.toList hnd (by simp)
    have hsup : Supply ((varsOf 127).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 127).map obs)
        (show Reach ((varsOf 127).map obs) 0 ((varsOf 127).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    refine ⟨wit, wo, hwMono, by omega, hwEval⟩
  · refine ⟨gates, o, ?_, le_rfl, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
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
lemma slice_fast_of {z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL}
    (ok : sliceCheck z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL = true)
    (hPrior : qGoal ≠ 0 → Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) sliceL := by
  have ok2 := ok
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1 ok2.1.1.1.1.1.2 ok2.1.1.1.1.2]
  exact slice_of ok hPrior
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
namespace Cofactor12080
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

def G_5 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def R_5 : List Nat := varsOf 13
lemma low_5_ok : carryOK [(3,5),(1,4),(0,1),(0,2)] R_5 G_5 R_0 G_0 = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 4 := carry_of low_5_ok low_0

def G_7 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def R_7 : List Nat := varsOf 37
lemma low_7_ok : carryOK [(1,3),(1,4),(0,1),(0,2)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0

def G_8 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def R_8 : List Nat := varsOf 14
lemma low_8_ok : carryOK [(3,5),(1,4),(1,2)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0

def G_9 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_9 : List Nat := varsOf 22
lemma low_9_ok : carryOK [(3,5),(1,3),(1,4),(1,2)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0

def G_10 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_10 : List Nat := varsOf 38
lemma low_10_ok : carryOK [(1,3),(1,4),(1,2)] R_10 G_10 R_0 G_0 = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 4 := carry_of low_10_ok low_0

def G_17 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def R_17 : List Nat := varsOf 50
lemma low_17_ok : carryOK [(1,2)] R_17 G_17 R_0 G_0 = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 4 := carry_of low_17_ok low_0

def G_18 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def R_18 : List Nat := varsOf 54
def pos_18 : List Nat := [22,22,22,38,38,38,50,50,50,52,52,52,22,22,22,38,38,38,50,50,50,52,52,52]
def neg_18 : List Nat := [20,18,6,36,34,6,48,34,18,48,36,20,34,36,48,18,20,48,6,20,36,6,18,34]
def fmask_18 : Nat := fullMask 24
def base_18 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_18 : List (Nat × Nat × Nat) := [(0,0,1),(3,4,2),(0,0,2),(0,4,2),(0,1,2),(3,7,3)]
def W_18 : BT Decor := buildWiresBT 4 base_18 steps_18
def autosL_18 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_18 : BT (List (Nat × Nat)) := btOfList 4 autosL_18
def slicesL_18 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def slices_18 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_18
def ps_18 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_18 : BT (Option BoundPool) := buildPoolsBT 2 W_18 R_18 slices_18 ps_18
lemma gp_18 : goodPairs G_18 pos_18 neg_18 := goodPairs_of (by decide +kernel)
lemma base_18_ok : ∀ x ∈ base_18, faithful pos_18 neg_18 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_18_ok : btAll (fun x => faithful pos_18 neg_18 x ∧ x.1 < 2^128) W_18 := buildWiresBT_faithful base_18_ok
set_option maxRecDepth 500000 in
lemma autos_18_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_18 = G_18) autos_18 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_18_0_ok : sliceDirectCheck 0 16 0 R_18 G_18 R_10 G_10 = true := by decide +kernel
lemma sl_18_0 : Slice R_18 G_18 (subcubeFast 0 16) 4 := slice_fast_direct sl_18_0_ok low_10
lemma sl_18_1_ok : sliceDirectCheck 0 2 0 R_18 G_18 R_0 G_0 = true := by decide +kernel
lemma sl_18_1 : Slice R_18 G_18 (subcubeFast 0 2) 4 := slice_fast_direct sl_18_1_ok low_0
lemma sl_18_2_ok : sliceDirectCheck 0 4 0 R_18 G_18 R_17 G_17 = true := by decide +kernel
lemma sl_18_2 : Slice R_18 G_18 (subcubeFast 0 4) 4 := slice_fast_direct sl_18_2_ok low_17
lemma sl_18_3_ok : sliceDirectCheck 0 32 0 R_18 G_18 R_9 G_9 = true := by decide +kernel
lemma sl_18_3 : Slice R_18 G_18 (subcubeFast 0 32) 4 := slice_fast_direct sl_18_3_ok low_9
set_option maxRecDepth 500000 in
lemma slices_18_ok : btAll (fun o => ∀ p, o = some p → Slice R_18 G_18 p.1 p.2) slices_18 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_18 G_18 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_18_0) (forall_cons (fun _ h => by cases h; exact sl_18_1) (forall_cons (fun _ h => by cases h; exact sl_18_2) (forall_cons (fun _ h => by cases h; exact sl_18_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_18_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_18 G_18 c) P_18 := buildPoolsBT_sound slices_18_ok
def bk_18_init : BT (List (List Nat)) := BT.empty
lemma bk_18_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 (0 - 1) xs.toFinset) bk_18_init := trivial
def nodes_18_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_0 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_init 0 nodes_18_0 = true := by decide +kernel
def bk_18_0 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_0
set_option maxRecDepth 500000 in
lemma bk_18_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 0 xs.toFinset) bk_18_0 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_init_ok chk_18_0
def nodes_18_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_1 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_0 1 nodes_18_1 = true := by decide +kernel
def bk_18_1 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_1
set_option maxRecDepth 500000 in
lemma bk_18_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 1 xs.toFinset) bk_18_1 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_0_ok chk_18_1
def nodes_18_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_2 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_1 2 nodes_18_2 = true := by decide +kernel
def bk_18_2 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_2
set_option maxRecDepth 500000 in
lemma bk_18_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 2 xs.toFinset) bk_18_2 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_1_ok chk_18_2
def nodes_18_3 : List NodeSpec := [([4,6,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_3 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_2 3 nodes_18_3 = true := by decide +kernel
def bk_18_3 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_3
set_option maxRecDepth 500000 in
lemma bk_18_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 3 xs.toFinset) bk_18_3 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_2_ok chk_18_3
def nodes_18_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([4,6,1,2,3],[0,2],[0]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_4 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_3 4 nodes_18_4 = true := by decide +kernel
def bk_18_4 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_4
set_option maxRecDepth 500000 in
lemma bk_18_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 4 xs.toFinset) bk_18_4 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_3_ok chk_18_4
def nodes_18_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_5 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_4 5 nodes_18_5 = true := by decide +kernel
def bk_18_5 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_5
set_option maxRecDepth 500000 in
lemma bk_18_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 5 xs.toFinset) bk_18_5 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_4_ok chk_18_5
def nodes_18_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_6 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_5 6 nodes_18_6 = true := by decide +kernel
def bk_18_6 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_6
set_option maxRecDepth 500000 in
lemma bk_18_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 6 xs.toFinset) bk_18_6 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_5_ok chk_18_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_ok : forestRootCheck R_18 G_18 [(VAR 1,22,20),(VAR 2,22,18),(VAR 4,22,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_in : bucketContainsBT bk_18_6 R_18 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_18 : Lower R_18 G_18 7 := lower_of_forestBT root_18_ok bk_18_6_ok root_18_in

def G_19 : Nat := 0xfe80fe80fe80fe80fe80fe80fe80fe80
def R_19 : List Nat := varsOf 15
def pos_19 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14,7,9,9,9,10,10,10,12,12,12]
def neg_19 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6,8,3,5,6,3,5,6,3,5,6]
def fmask_19 : Nat := fullMask 22
def base_19 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf49f,0x1b6496),(0xcccccccccccccccccccccccccccccccc,0x718e7,0x2da8c5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x381f07,0x36ce03),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3feff8,0x1128)]
def steps_19 : List (Nat × Nat × Nat) := [(3,0,3),(1,0,3),(2,0,3),(0,0,3),(2,0,1),(1,0,1),(0,0,1),(3,1,5),(3,7,1),(0,1,5),(3,0,1),(3,8,2),(1,7,1),(1,8,2),(3,10,9)]
def W_19 : BT Decor := buildWiresBT 5 base_19 steps_19
def autosL_19 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_19 : BT (List (Nat × Nat)) := btOfList 3 autosL_19
def slicesL_19 : List (Option (Nat × Nat)) := []
def slices_19 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_19
def ps_19 : List PoolSpec := []
def P_19 : BT (Option BoundPool) := buildPoolsBT 1 W_19 R_19 slices_19 ps_19
lemma gp_19 : goodPairs G_19 pos_19 neg_19 := goodPairs_of (by decide +kernel)
lemma base_19_ok : ∀ x ∈ base_19, faithful pos_19 neg_19 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_19_ok : btAll (fun x => faithful pos_19 neg_19 x ∧ x.1 < 2^128) W_19 := buildWiresBT_faithful base_19_ok
set_option maxRecDepth 500000 in
lemma autos_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_19 = G_19) autos_19 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_19_ok : btAll (fun o => ∀ p, o = some p → Slice R_19 G_19 p.1 p.2) slices_19 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_19 G_19 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_19_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_19 G_19 c) P_19 := buildPoolsBT_sound slices_19_ok
def bk_19_init : BT (List (List Nat)) := BT.empty
lemma bk_19_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 (0 - 1) xs.toFinset) bk_19_init := trivial
def nodes_19_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_0 : checkNodesBT W_19 G_19 fmask_19 P_19 autos_19 bk_19_init 0 nodes_19_0 = true := by decide +kernel
def bk_19_0 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_0
set_option maxRecDepth 500000 in
lemma bk_19_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 0 xs.toFinset) bk_19_0 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok P_19_ok autos_19_ok bk_19_init_ok chk_19_0
def nodes_19_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_1 : checkNodesBT W_19 G_19 fmask_19 P_19 autos_19 bk_19_0 1 nodes_19_1 = true := by decide +kernel
def bk_19_1 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_1
set_option maxRecDepth 500000 in
lemma bk_19_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 1 xs.toFinset) bk_19_1 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok P_19_ok autos_19_ok bk_19_0_ok chk_19_1
def nodes_19_2 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_2 : checkNodesBT W_19 G_19 fmask_19 P_19 autos_19 bk_19_1 2 nodes_19_2 = true := by decide +kernel
def bk_19_2 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_2
set_option maxRecDepth 500000 in
lemma bk_19_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 2 xs.toFinset) bk_19_2 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok P_19_ok autos_19_ok bk_19_1_ok chk_19_2
def nodes_19_3 : List NodeSpec := [([6,4,1,2],[],[]),([11,0,2,3],[],[]),([12,0,2,3],[],[]),([0,13,2,3],[],[]),([8,14,2,3],[],[0]),([0,1,15,3],[],[]),([0,16,2,3],[],[]),([0,1,17,3],[],[]),([10,9,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_3 : checkNodesBT W_19 G_19 fmask_19 P_19 autos_19 bk_19_2 3 nodes_19_3 = true := by decide +kernel
def bk_19_3 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_3
set_option maxRecDepth 500000 in
lemma bk_19_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 3 xs.toFinset) bk_19_3 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok P_19_ok autos_19_ok bk_19_2_ok chk_19_3
def nodes_19_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([0,1,2,3,5],[],[0,1]),([6,0,1,2,3],[],[0]),([7,0,1,2,3],[],[0,1]),([8,0,1,2,3],[],[0]),([0,1,9,2,3],[],[0]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_4 : checkNodesBT W_19 G_19 fmask_19 P_19 autos_19 bk_19_3 4 nodes_19_4 = true := by decide +kernel
def bk_19_4 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_4
set_option maxRecDepth 500000 in
lemma bk_19_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 4 xs.toFinset) bk_19_4 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok P_19_ok autos_19_ok bk_19_3_ok chk_19_4
def nodes_19_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_5 : checkNodesBT W_19 G_19 fmask_19 P_19 autos_19 bk_19_4 5 nodes_19_5 = true := by decide +kernel
def bk_19_5 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_5
set_option maxRecDepth 500000 in
lemma bk_19_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 5 xs.toFinset) bk_19_5 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok P_19_ok autos_19_ok bk_19_4_ok chk_19_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck R_19 G_19 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 3,9,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT bk_19_5 R_19 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_19 : Lower R_19 G_19 6 := lower_of_forestBT root_19_ok bk_19_5_ok root_19_in

def G_20 : Nat := 0xff00f000f0000000ff00f000f0000000
def R_20 : List Nat := varsOf 60
lemma low_20_ok : liftCheck 0 8 R_20 G_20 R_0 G_0 [(VAR 3,28,20)] = true := by decide +kernel
lemma low_20 : Lower R_20 G_20 5 := lift_of low_20_ok low_0

def G_21 : Nat := 0xffc0ffc0fcc0fcc0ffc0ffc0fcc0fcc0
def R_21 : List Nat := varsOf 46
lemma low_21_ok : liftCheck 32 0 R_21 G_21 R_8 G_8 [(VAR 5,40,8)] = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 5 := lift_of low_21_ok low_8

def G_23 : Nat := 0xfffffcfcfcfcc0c0fffffcfcfcfcc0c0
def R_23 : List Nat := varsOf 54
def pos_23 : List Nat := [6,6,18,18,20,20,34,34,36,36,48,48,6,6,18,18,20,20,34,34,36,36,48,48]
def neg_23 : List Nat := [4,2,16,2,16,4,32,2,32,4,32,16,16,32,4,32,2,32,4,16,2,16,2,4]
def fmask_23 : Nat := fullMask 24
def base_23 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf0cf,0x51008a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x333333,0x844221),(0xffff0000ffff0000ffff0000ffff0000,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def steps_23 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_23 : BT Decor := buildWiresBT 4 base_23 steps_23
def autosL_23 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_23 : BT (List (Nat × Nat)) := btOfList 4 autosL_23
def slicesL_23 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,4),some (subcubeFast 2 0,4),some (subcubeFast 32 0,4),some (subcubeFast 16 0,4)]
def slices_23 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_23
def ps_23 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_23 : BT (Option BoundPool) := buildPoolsBT 2 W_23 R_23 slices_23 ps_23
lemma gp_23 : goodPairs G_23 pos_23 neg_23 := goodPairs_of (by decide +kernel)
lemma base_23_ok : ∀ x ∈ base_23, faithful pos_23 neg_23 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_23_ok : btAll (fun x => faithful pos_23 neg_23 x ∧ x.1 < 2^128) W_23 := buildWiresBT_faithful base_23_ok
set_option maxRecDepth 500000 in
lemma autos_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_23 = G_23) autos_23 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_23_0_ok : sliceDirectCheck 4 0 0 R_23 G_23 R_17 G_17 = true := by decide +kernel
lemma sl_23_0 : Slice R_23 G_23 (subcubeFast 4 0) 4 := slice_fast_direct sl_23_0_ok low_17
lemma sl_23_1_ok : sliceDirectCheck 2 0 0 R_23 G_23 R_0 G_0 = true := by decide +kernel
lemma sl_23_1 : Slice R_23 G_23 (subcubeFast 2 0) 4 := slice_fast_direct sl_23_1_ok low_0
lemma sl_23_2_ok : sliceDirectCheck 32 0 0 R_23 G_23 R_9 G_9 = true := by decide +kernel
lemma sl_23_2 : Slice R_23 G_23 (subcubeFast 32 0) 4 := slice_fast_direct sl_23_2_ok low_9
lemma sl_23_3_ok : sliceDirectCheck 16 0 0 R_23 G_23 R_10 G_10 = true := by decide +kernel
lemma sl_23_3 : Slice R_23 G_23 (subcubeFast 16 0) 4 := slice_fast_direct sl_23_3_ok low_10
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
lemma root_23_ok : forestRootCheck R_23 G_23 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT bk_23_6 R_23 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_23 : Lower R_23 G_23 7 := lower_of_forestBT root_23_ok bk_23_6_ok root_23_in

def G_24 : Nat := 0xe880e880e880e880e880e880e880e880
def R_24 : List Nat := varsOf 15
lemma low_24_ok : carryOK [(3,5),(0,4),(0,2),(0,1)] R_24 G_24 R_18 G_18 = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 7 := carry_of low_24_ok low_18

def G_28 : Nat := 0xee00ee0088008800ee00ee0088008800
def R_28 : List Nat := varsOf 43
lemma low_28_ok : carryOK [(1,4),(0,2)] R_28 G_28 R_20 G_20 = true := by decide +kernel
lemma low_28 : Lower R_28 G_28 5 := carry_of low_28_ok low_20

def G_33 : Nat := 0xfa00fa00a000a000fa00fa00a000a000
def R_33 : List Nat := varsOf 45
lemma low_33_ok : carryOK [(1,4),(0,1),(0,2)] R_33 G_33 R_20 G_20 = true := by decide +kernel
lemma low_33 : Lower R_33 G_33 5 := carry_of low_33_ok low_20

def G_38 : Nat := 0xfc00fc00c000c000fc00fc00c000c000
def R_38 : List Nat := varsOf 46
lemma low_38_ok : carryOK [(1,4),(1,2)] R_38 G_38 R_20 G_20 = true := by decide +kernel
lemma low_38 : Lower R_38 G_38 5 := carry_of low_38_ok low_20

def G_42 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def R_42 : List Nat := varsOf 39
lemma low_42_ok : carryOK [(0,3),(0,4),(0,2),(0,1)] R_42 G_42 R_23 G_23 = true := by decide +kernel
lemma low_42 : Lower R_42 G_42 7 := carry_of low_42_ok low_23

def G_45 : Nat := 0xff88ff88ee88ee88ff88ff88ee88ee88
def R_45 : List Nat := varsOf 43
lemma low_45_ok : carryOK [(0,2),(0,1)] R_45 G_45 R_21 G_21 = true := by decide +kernel
lemma low_45 : Lower R_45 G_45 5 := carry_of low_45_ok low_21

def G_46 : Nat := 0xffa0ffa0faa0faa0ffa0ffa0faa0faa0
def R_46 : List Nat := varsOf 45
lemma low_46_ok : carryOK [(0,1)] R_46 G_46 R_21 G_21 = true := by decide +kernel
lemma low_46 : Lower R_46 G_46 5 := carry_of low_46_ok low_21

def G_53 : Nat := 0xfe80fe80e880e880fe80fe80e880e880
def R_53 : List Nat := varsOf 47
def pos_53 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,39,39,39,41,41,41,42,42,42,43,44,44,44,45,46,7,7,7,7,7,7,7,11,11,11,11,11,13,13,13,13,13,14,14,14,14,14,41,41,41,41,41,42,42,42,42,42,44,44,44,44,44]
def neg_53 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,38,37,35,40,33,9,40,34,10,35,40,36,12,37,38,9,10,12,35,37,38,40,12,35,37,38,40,10,35,37,38,40,9,35,37,38,40,10,12,35,37,38,9,12,35,37,38,9,10,35,37,38]
def fmask_53 : Nat := fullMask 64
def base_53 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3e0ffffa23f1ff,0x6b587318ca2361b6),(0xcccccccccccccccccccccccccccccccc,0x7c1f07ffc3c7e3f,0xb52aa5a954385c2d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf801ff83ffc07fc7,0xc6b4c635a7803b43),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffffffc07ff8ff8,0x18c718c6395686d8),(0xffffffff00000000ffffffff00000000,0xfffe000007fff000,0xe739ef7bc6edf000)]
def steps_53 : List (Nat × Nat × Nat) := [(2,0,1),(1,0,1),(0,0,1),(3,0,1),(3,7,6),(3,9,2),(2,9,2),(1,9,2),(0,9,2),(3,13,12)]
def W_53 : BT Decor := buildWiresBT 4 base_53 steps_53
def autosL_53 : List (List (Nat × Nat)) := [[],[(0,1)],[(1,2)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_53 : BT (List (Nat × Nat)) := btOfList 3 autosL_53
def slicesL_53 : List (Option (Nat × Nat)) := [some (subcubeFast 0 32,6),some (subcubeFast 32 2,4),some (subcubeFast 2 8,4),some (subcubeFast 0 2,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 4,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,7),some (subcubeFast 1 8,4),some (subcubeFast 32 0,7),some (subcubeFast 1 0,5)]
def slices_53 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_53
def ps_53 : List PoolSpec := [(0,[(0,0,1),(1,0,1),(3,7,6)]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(0,[]),(10,[]),(8,[(1,0,1)]),(11,[]),(10,[(0,0,1)])]
def P_53 : BT (Option BoundPool) := buildPoolsBT 4 W_53 R_53 slices_53 ps_53
lemma gp_53 : goodPairs G_53 pos_53 neg_53 := goodPairs_of (by decide +kernel)
lemma base_53_ok : ∀ x ∈ base_53, faithful pos_53 neg_53 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_53_ok : btAll (fun x => faithful pos_53 neg_53 x ∧ x.1 < 2^128) W_53 := buildWiresBT_faithful base_53_ok
set_option maxRecDepth 500000 in
lemma autos_53_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_53 = G_53) autos_53 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_53_0_ok : sliceDirectCheck 0 32 0 R_53 G_53 R_19 G_19 = true := by decide +kernel
lemma sl_53_0 : Slice R_53 G_53 (subcubeFast 0 32) 6 := slice_fast_direct sl_53_0_ok low_19
lemma sl_53_1_ok : sliceDirectCheck 32 2 0 R_53 G_53 R_5 G_5 = true := by decide +kernel
lemma sl_53_1 : Slice R_53 G_53 (subcubeFast 32 2) 4 := slice_fast_direct sl_53_1_ok low_5
lemma sl_53_2_ok : sliceDirectCheck 2 8 0 R_53 G_53 R_7 G_7 = true := by decide +kernel
lemma sl_53_2 : Slice R_53 G_53 (subcubeFast 2 8) 4 := slice_fast_direct sl_53_2_ok low_7
lemma sl_53_3_ok : sliceDirectCheck 0 2 0 R_53 G_53 R_46 G_46 = true := by decide +kernel
lemma sl_53_3 : Slice R_53 G_53 (subcubeFast 0 2) 5 := slice_fast_direct sl_53_3_ok low_46
lemma sl_53_4_ok : sliceDirectCheck 0 1 0 R_53 G_53 R_21 G_21 = true := by decide +kernel
lemma sl_53_4 : Slice R_53 G_53 (subcubeFast 0 1) 5 := slice_fast_direct sl_53_4_ok low_21
lemma sl_53_5_ok : sliceDirectCheck 2 0 0 R_53 G_53 R_33 G_33 = true := by decide +kernel
lemma sl_53_5 : Slice R_53 G_53 (subcubeFast 2 0) 5 := slice_fast_direct sl_53_5_ok low_33
lemma sl_53_6_ok : sliceDirectCheck 0 4 0 R_53 G_53 R_45 G_45 = true := by decide +kernel
lemma sl_53_6 : Slice R_53 G_53 (subcubeFast 0 4) 5 := slice_fast_direct sl_53_6_ok low_45
lemma sl_53_7_ok : sliceDirectCheck 4 0 0 R_53 G_53 R_28 G_28 = true := by decide +kernel
lemma sl_53_7 : Slice R_53 G_53 (subcubeFast 4 0) 5 := slice_fast_direct sl_53_7_ok low_28
lemma sl_53_8_ok : sliceDirectCheck 0 8 0 R_53 G_53 R_42 G_42 = true := by decide +kernel
lemma sl_53_8 : Slice R_53 G_53 (subcubeFast 0 8) 7 := slice_fast_direct sl_53_8_ok low_42
lemma sl_53_9_ok : sliceDirectCheck 1 8 0 R_53 G_53 R_10 G_10 = true := by decide +kernel
lemma sl_53_9 : Slice R_53 G_53 (subcubeFast 1 8) 4 := slice_fast_direct sl_53_9_ok low_10
lemma sl_53_10_ok : sliceDirectCheck 32 0 0 R_53 G_53 R_24 G_24 = true := by decide +kernel
lemma sl_53_10 : Slice R_53 G_53 (subcubeFast 32 0) 7 := slice_fast_direct sl_53_10_ok low_24
lemma sl_53_11_ok : sliceDirectCheck 1 0 0 R_53 G_53 R_38 G_38 = true := by decide +kernel
lemma sl_53_11 : Slice R_53 G_53 (subcubeFast 1 0) 5 := slice_fast_direct sl_53_11_ok low_38
set_option maxRecDepth 500000 in
lemma slices_53_ok : btAll (fun o => ∀ p, o = some p → Slice R_53 G_53 p.1 p.2) slices_53 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_53 G_53 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_53_0) (forall_cons (fun _ h => by cases h; exact sl_53_1) (forall_cons (fun _ h => by cases h; exact sl_53_2) (forall_cons (fun _ h => by cases h; exact sl_53_3) (forall_cons (fun _ h => by cases h; exact sl_53_4) (forall_cons (fun _ h => by cases h; exact sl_53_5) (forall_cons (fun _ h => by cases h; exact sl_53_6) (forall_cons (fun _ h => by cases h; exact sl_53_7) (forall_cons (fun _ h => by cases h; exact sl_53_8) (forall_cons (fun _ h => by cases h; exact sl_53_9) (forall_cons (fun _ h => by cases h; exact sl_53_10) (forall_cons (fun _ h => by cases h; exact sl_53_11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
set_option maxRecDepth 500000 in
lemma P_53_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_53 G_53 c) P_53 := buildPoolsBT_sound slices_53_ok
def bk_53_init : BT (List (List Nat)) := BT.empty
lemma bk_53_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 (0 - 1) xs.toFinset) bk_53_init := trivial
def nodes_53_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_0 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_init 0 nodes_53_0 = true := by decide +kernel
def bk_53_0 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_0
set_option maxRecDepth 500000 in
lemma bk_53_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 0 xs.toFinset) bk_53_0 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_init_ok chk_53_0
def nodes_53_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_1 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_0 1 nodes_53_1 = true := by decide +kernel
def bk_53_1 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_1
set_option maxRecDepth 500000 in
lemma bk_53_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 1 xs.toFinset) bk_53_1 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_0_ok chk_53_1
def nodes_53_2 : List NodeSpec := [([14,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_2 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_1 2 nodes_53_2 = true := by decide +kernel
def bk_53_2 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_2
set_option maxRecDepth 500000 in
lemma bk_53_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 2 xs.toFinset) bk_53_2 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_1_ok chk_53_2
def nodes_53_3 : List NodeSpec := [([11,10,3,4],[],[0]),([13,12,3,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_3 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_2 3 nodes_53_3 = true := by decide +kernel
def bk_53_3 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_3
set_option maxRecDepth 500000 in
lemma bk_53_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 3 xs.toFinset) bk_53_3 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_2_ok chk_53_3
def nodes_53_4 : List NodeSpec := [([9,10,2,3,4],[],[0]),([11,9,2,3,4],[],[0]),([9,2,12,3,4],[],[0]),([13,9,2,3,4],[0,1],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_4 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_3 4 nodes_53_4 = true := by decide +kernel
def bk_53_4 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_4
set_option maxRecDepth 500000 in
lemma bk_53_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 4 xs.toFinset) bk_53_4 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_3_ok chk_53_4
def nodes_53_5 : List NodeSpec := [([9,2,3,4],[2,1],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_5 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_4 5 nodes_53_5 = true := by decide +kernel
def bk_53_5 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_5
set_option maxRecDepth 500000 in
lemma bk_53_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 5 xs.toFinset) bk_53_5 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_4_ok chk_53_5
def nodes_53_6 : List NodeSpec := [([5,8,2,3,4],[3,4,2,1],[0]),([7,6,2,3,4],[5,4,2,1],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_6 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_5 6 nodes_53_6 = true := by decide +kernel
def bk_53_6 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_6
set_option maxRecDepth 500000 in
lemma bk_53_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 6 xs.toFinset) bk_53_6 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_5_ok chk_53_6
def nodes_53_7 : List NodeSpec := [([5,0,1,2,3,4],[5,4,3,6,7,8,9,10,11,1],[0]),([0,1,6,2,3,4],[4,5,3,7,6,12,11,10,1],[0]),([7,0,1,2,3,4],[5,3,6,7,8,2,10,11,4,13,1,14],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_7 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_6 7 nodes_53_7 = true := by decide +kernel
def bk_53_7 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_7
set_option maxRecDepth 500000 in
lemma bk_53_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 7 xs.toFinset) bk_53_7 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_6_ok chk_53_7
def nodes_53_8 : List NodeSpec := [([0,1,2,3,4],[8,11],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_8 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_7 8 nodes_53_8 = true := by decide +kernel
def bk_53_8 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_8
set_option maxRecDepth 500000 in
lemma bk_53_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 8 xs.toFinset) bk_53_8 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_7_ok chk_53_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_53_ok : forestRootCheck R_53 G_53 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 3,11,3),(VAR 5,41,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_53_in : bucketContainsBT bk_53_8 R_53 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_53 : Lower R_53 G_53 9 := lower_of_forestBT root_53_ok bk_53_8_ok root_53_in

end Cofactor12080
def h1R : List Nat := varsOf 31
def h1G : Nat := 0xeaa8e880eaa8e880eaa8e880eaa8e880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bound : Lower h1R h1G 9 := carry_of (swaps := [(4,5),(2,3),(1,2),(0,1)]) (roots2 := Cofactor12080.R_53) (T2 := Cofactor12080.G_53) (by decide +kernel) Cofactor12080.low_53
def h3R : List Nat := varsOf 38
def h3G : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def h3Pos : List Nat := [34,36,6,6,36,34]
def h3Neg : List Nat := [32,32,2,4,4,2]
def h3Mask : Nat := fullMask 6
def h3Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h3Steps : List (Nat × Nat × Nat) := []
def h3W : BT Decor := buildWiresBT 2 h3Base h3Steps
def h3AutoList : List (List (Nat × Nat)) := [[]]
def h3Autos : BT (List (Nat × Nat)) := btOfList 1 h3AutoList
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
def h3SliceList : List (Option (Nat × Nat)) := []
def h3Slices : BT (Option (Nat × Nat)) := btOfList 1 h3SliceList
def h3Specs : List PoolSpec := []
def h3Pools : BT (Option BoundPool) := buildPoolsBT 1 h3W h3R h3Slices h3Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h3R h3G p.1 p.2) h3Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h3R h3G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h3R h3G c) h3Pools := buildPoolsBT_sound h3SlicesOk
def h3Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G (3 - 1) xs.toFinset) h3Empty := trivial
def h3Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test3_0 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 3 h3Block3_0 = true := by decide +kernel
def h3Nodes3 : List NodeSpec := h3Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Check3 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 3 h3Nodes3 = true := h3Test3_0
def h3Bucket3 : BT (List (List Nat)) := buildBucketsBT h3W h3Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G 3 xs.toFinset) h3Bucket3 := buildBucketsBT_sound (by decide) h3Pairs h3WOk h3PoolsOk h3AutosOk h3EmptyOk h3Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 5,2,34)]) (by decide +kernel) h3Bucket3Ok (by decide +kernel)
def h2R : List Nat := varsOf 46
def h2G : Nat := 0xfcfcfcfcfcc0fcc0fcfcfcfcfcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,2,10)]) (by decide +kernel) h3Bound
def h5R : List Nat := varsOf 15
def h5G : Nat := 0xe880e880e880e880e880e880e880e880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 7 := carry_of (swaps := [(3,4),(4,5),(0,1),(1,2),(2,3),(3,4)]) (roots2 := Cofactor12080.R_18) (T2 := Cofactor12080.G_18) (by decide +kernel) Cofactor12080.low_18
def h4R : List Nat := varsOf 47
def h4G : Nat := 0xe8a8e8a8e880e880e8a8e8a8e880e880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 8 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,3,35)]) (by decide +kernel) h5Bound
def h6R : List Nat := varsOf 51
def h6G : Nat := 0xeeeeaaaaaaaa8888eeeeaaaaaaaa8888
def h6Pos : List Nat := [17,50,17,33,3,17,50,33,50,3,3,3,17,3,33,19,19,35,35,49,49]
def h6Neg : List Nat := [16,48,18,32,2,1,34,1,18,1,0,18,0,34,0,18,1,34,1,48,1]
def h6Mask : Nat := fullMask 21
def h6Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xcccccccccccccccccccccccccccccccc,0x7af52,0x2a954),(0xffff0000ffff0000ffff0000ffff0000,0x199167,0x88907),(0xffffffff00000000ffffffff00000000,0x1e41ca,0xa204a)]
def h6Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(0,1,28),(2,2,4),(1,3,4),(0,1,31),(2,3,4),(0,2,5),(1,1,34),(3,2,5),(0,3,5),(1,1,37),(3,3,5),(2,1,8),(1,3,8),(0,2,41),(2,3,8),(3,1,9),(0,3,9),(1,2,45),(3,3,9),(2,1,12),(2,2,12),(3,1,13),(3,2,13),(1,3,18),(0,1,52),(2,3,18),(1,2,54),(1,3,19),(0,2,56),(2,3,19),(1,1,58),(1,2,22),(0,1,60),(2,2,23),(1,1,62)]
def h6W : BT Decor := buildWiresBT 6 h6Base h6Steps
def h6AutoList : List (List (Nat × Nat)) := [[]]
def h6Autos : BT (List (Nat × Nat)) := btOfList 1 h6AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Pairs : goodPairs h6G h6Pos h6Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6BaseOk : ∀ x ∈ h6Base, faithful h6Pos h6Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6WOk : btAll (fun x => faithful h6Pos h6Neg x ∧ x.1 < 2^128) h6W := buildWiresBT_faithful h6BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h6G = h6G) h6Autos := btAll_ofList (autos_of (by decide +kernel))
def h6SliceList : List (Option (Nat × Nat)) := []
def h6Slices : BT (Option (Nat × Nat)) := btOfList 1 h6SliceList
def h6Specs : List PoolSpec := []
def h6Pools : BT (Option BoundPool) := buildPoolsBT 1 h6W h6R h6Slices h6Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h6R h6G p.1 p.2) h6Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h6R h6G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h6R h6G c) h6Pools := buildPoolsBT_sound h6SlicesOk
def h6Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h6G (3 - 1) xs.toFinset) h6Empty := trivial
def h6Block3_0 : List NodeSpec := [([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,2,31],[],[0]),([0,1,2,33],[],[0]),([0,1,3,34],[],[0]),([0,1,3,36],[],[0]),([0,1,2,37],[],[0]),([0,1,2,39],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test3_0 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Empty 3 h6Block3_0 = true := by decide +kernel
def h6Block3_1 : List NodeSpec := [([0,2,3,35],[],[0]),([0,2,3,40],[],[0]),([0,1,2,41],[],[0]),([0,1,2,43],[],[0]),([0,2,3,29],[],[0]),([0,2,3,44],[],[0]),([0,1,2,45],[],[0]),([0,1,2,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test3_1 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Empty 3 h6Block3_1 = true := by decide +kernel
def h6Block3_2 : List NodeSpec := [([0,2,3,38],[],[0]),([0,2,3,48],[],[0]),([0,1,3,46],[],[0]),([0,1,3,49],[],[0]),([0,2,3,32],[],[0]),([0,2,3,50],[],[0]),([0,1,3,42],[],[0]),([0,1,3,51],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test3_2 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Empty 3 h6Block3_2 = true := by decide +kernel
def h6Block3_3 : List NodeSpec := [([0,3,16,17],[],[0]),([0,1,2,52],[],[0]),([0,1,2,54],[],[0]),([0,1,2,56],[],[0]),([0,1,2,58],[],[0]),([0,2,20,21],[],[0]),([0,1,3,60],[],[0]),([0,1,3,57],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test3_3 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Empty 3 h6Block3_3 = true := by decide +kernel
def h6Block3_4 : List NodeSpec := [([0,1,3,55],[],[0]),([0,1,3,62],[],[0]),([0,1,24,25],[],[0]),([0,2,3,63],[],[0]),([0,2,3,53],[],[0]),([0,2,3,59],[],[0]),([0,2,3,61],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test3_4 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Empty 3 h6Block3_4 = true := by decide +kernel
def h6Nodes3 : List NodeSpec := h6Block3_0 ++ h6Block3_1 ++ h6Block3_2 ++ h6Block3_3 ++ h6Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Check3 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Empty 3 h6Nodes3 = true := by
  unfold h6Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h6Test3_0,h6Test3_1⟩,h6Test3_2⟩,h6Test3_3⟩,h6Test3_4⟩
def h6Bucket3 : BT (List (List Nat)) := buildBucketsBT h6W h6Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h6G 3 xs.toFinset) h6Bucket3 := buildBucketsBT_sound (by decide) h6Pairs h6WOk h6PoolsOk h6AutosOk h6EmptyOk h6Check3
def h6Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test4_0 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket3 4 h6Block4_0 = true := by decide +kernel
def h6Block4_1 : List NodeSpec := [([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0]),([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test4_1 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket3 4 h6Block4_1 = true := by decide +kernel
def h6Block4_2 : List NodeSpec := [([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0]),([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test4_2 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket3 4 h6Block4_2 = true := by decide +kernel
def h6Nodes4 : List NodeSpec := h6Block4_0 ++ h6Block4_1 ++ h6Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Check4 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket3 4 h6Nodes4 = true := by
  unfold h6Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h6Test4_0,h6Test4_1⟩,h6Test4_2⟩
def h6Bucket4 : BT (List (List Nat)) := buildBucketsBT h6W h6Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h6G 4 xs.toFinset) h6Bucket4 := buildBucketsBT_sound (by decide) h6Pairs h6WOk h6PoolsOk h6AutosOk h6Bucket3Ok h6Check4
def h6Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_0 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_0 = true := by decide +kernel
def h6Nodes5 : List NodeSpec := h6Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Check5 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Nodes5 = true := h6Test5_0
def h6Bucket5 : BT (List (List Nat)) := buildBucketsBT h6W h6Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h6G 5 xs.toFinset) h6Bucket5 := buildBucketsBT_sound (by decide) h6Pairs h6WOk h6PoolsOk h6AutosOk h6Bucket4Ok h6Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h6Bucket5Ok (by decide +kernel)
def h7R : List Nat := varsOf 53
def h7G : Nat := 0xfafaaaaaaaaaa0a0fafaaaaaaaaaa0a0
def h7Pos : List Nat := [17,52,17,33,5,17,52,33,52,5,5,5,17,5,33,21,21,37,37,49,49]
def h7Neg : List Nat := [16,48,20,32,4,1,36,1,20,1,0,20,0,36,0,20,1,36,1,48,1]
def h7Mask : Nat := fullMask 21
def h7Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7af52,0x2a954),(0xffff0000ffff0000ffff0000ffff0000,0x199167,0x88907),(0xffffffff00000000ffffffff00000000,0x1e41ca,0xa204a)]
def h7Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(0,1,28),(2,2,4),(1,3,4),(0,1,31),(2,3,4),(0,2,5),(1,1,34),(3,2,5),(0,3,5),(1,1,37),(3,3,5),(2,1,8),(1,3,8),(0,2,41),(2,3,8),(3,1,9),(0,3,9),(1,2,45),(3,3,9),(2,1,12),(2,2,12),(3,1,13),(3,2,13),(1,3,18),(0,1,52),(2,3,18),(1,2,54),(1,3,19),(0,2,56),(2,3,19),(1,1,58),(1,2,22),(0,1,60),(2,2,23),(1,1,62)]
def h7W : BT Decor := buildWiresBT 6 h7Base h7Steps
def h7AutoList : List (List (Nat × Nat)) := [[]]
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
def h7Block3_0 : List NodeSpec := [([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,2,31],[],[0]),([0,1,2,33],[],[0]),([0,1,3,34],[],[0]),([0,1,3,36],[],[0]),([0,1,2,37],[],[0]),([0,1,2,39],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test3_0 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Block3_0 = true := by decide +kernel
def h7Block3_1 : List NodeSpec := [([0,2,3,35],[],[0]),([0,2,3,40],[],[0]),([0,1,2,41],[],[0]),([0,1,2,43],[],[0]),([0,2,3,29],[],[0]),([0,2,3,44],[],[0]),([0,1,2,45],[],[0]),([0,1,2,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test3_1 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Block3_1 = true := by decide +kernel
def h7Block3_2 : List NodeSpec := [([0,2,3,38],[],[0]),([0,2,3,48],[],[0]),([0,1,3,46],[],[0]),([0,1,3,49],[],[0]),([0,2,3,32],[],[0]),([0,2,3,50],[],[0]),([0,1,3,42],[],[0]),([0,1,3,51],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test3_2 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Block3_2 = true := by decide +kernel
def h7Block3_3 : List NodeSpec := [([0,3,16,17],[],[0]),([0,1,2,52],[],[0]),([0,1,2,54],[],[0]),([0,1,2,56],[],[0]),([0,1,2,58],[],[0]),([0,2,20,21],[],[0]),([0,1,3,60],[],[0]),([0,1,3,57],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test3_3 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Block3_3 = true := by decide +kernel
def h7Block3_4 : List NodeSpec := [([0,1,3,55],[],[0]),([0,1,3,62],[],[0]),([0,1,24,25],[],[0]),([0,2,3,63],[],[0]),([0,2,3,53],[],[0]),([0,2,3,59],[],[0]),([0,2,3,61],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test3_4 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Block3_4 = true := by decide +kernel
def h7Nodes3 : List NodeSpec := h7Block3_0 ++ h7Block3_1 ++ h7Block3_2 ++ h7Block3_3 ++ h7Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Check3 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Nodes3 = true := by
  unfold h7Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h7Test3_0,h7Test3_1⟩,h7Test3_2⟩,h7Test3_3⟩,h7Test3_4⟩
def h7Bucket3 : BT (List (List Nat)) := buildBucketsBT h7W h7Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G 3 xs.toFinset) h7Bucket3 := buildBucketsBT_sound (by decide) h7Pairs h7WOk h7PoolsOk h7AutosOk h7EmptyOk h7Check3
def h7Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test4_0 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket3 4 h7Block4_0 = true := by decide +kernel
def h7Block4_1 : List NodeSpec := [([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0]),([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test4_1 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket3 4 h7Block4_1 = true := by decide +kernel
def h7Block4_2 : List NodeSpec := [([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0]),([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test4_2 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket3 4 h7Block4_2 = true := by decide +kernel
def h7Nodes4 : List NodeSpec := h7Block4_0 ++ h7Block4_1 ++ h7Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Check4 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket3 4 h7Nodes4 = true := by
  unfold h7Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h7Test4_0,h7Test4_1⟩,h7Test4_2⟩
def h7Bucket4 : BT (List (List Nat)) := buildBucketsBT h7W h7Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G 4 xs.toFinset) h7Bucket4 := buildBucketsBT_sound (by decide) h7Pairs h7WOk h7PoolsOk h7AutosOk h7Bucket3Ok h7Check4
def h7Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test5_0 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Block5_0 = true := by decide +kernel
def h7Nodes5 : List NodeSpec := h7Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Check5 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Nodes5 = true := h7Test5_0
def h7Bucket5 : BT (List (List Nat)) := buildBucketsBT h7W h7Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G 5 xs.toFinset) h7Bucket5 := buildBucketsBT_sound (by decide) h7Pairs h7WOk h7PoolsOk h7AutosOk h7Bucket4Ok h7Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 6 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h7Bucket5Ok (by decide +kernel)
def h8R : List Nat := varsOf 54
def h8G : Nat := 0xfcfcfcfcfcfcc0c0fcfcfcfcfcfcc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,2,18)]) (by decide +kernel) h3Bound
def h10R : List Nat := varsOf 22
def h10G : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def h10Pos : List Nat := [18,20,6,6,20,18]
def h10Neg : List Nat := [16,16,2,4,4,2]
def h10Mask : Nat := fullMask 6
def h10Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h10Steps : List (Nat × Nat × Nat) := []
def h10W : BT Decor := buildWiresBT 2 h10Base h10Steps
def h10AutoList : List (List (Nat × Nat)) := [[]]
def h10Autos : BT (List (Nat × Nat)) := btOfList 1 h10AutoList
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
def h10Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
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
lemma h10Bound : Lower h10R h10G 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 4,2,18)]) (by decide +kernel) h10Bucket3Ok (by decide +kernel)
def h11R : List Nat := varsOf 23
def h11G : Nat := 0xa8a88080a8a88080a8a88080a8a88080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) h10Bound
def h12R : List Nat := varsOf 39
def h12G : Nat := 0xa8a8a8a880808080a8a8a8a880808080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) h3Bound
def h13R : List Nat := varsOf 7
def h13G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def h13Pos : List Nat := [5,6,3,3,6,5]
def h13Neg : List Nat := [4,4,1,2,2,1]
def h13Mask : Nat := fullMask 6
def h13Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,51,3)]
def h13Steps : List (Nat × Nat × Nat) := []
def h13W : BT Decor := buildWiresBT 2 h13Base h13Steps
def h13AutoList : List (List (Nat × Nat)) := [[]]
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
def h13SliceList : List (Option (Nat × Nat)) := []
def h13Slices : BT (Option (Nat × Nat)) := btOfList 1 h13SliceList
def h13Specs : List PoolSpec := []
def h13Pools : BT (Option BoundPool) := buildPoolsBT 1 h13W h13R h13Slices h13Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h13R h13G p.1 p.2) h13Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h13R h13G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h13R h13G c) h13Pools := buildPoolsBT_sound h13SlicesOk
def h13Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h13G (3 - 1) xs.toFinset) h13Empty := trivial
def h13Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Test3_0 : checkNodesBT h13W h13G h13Mask h13Pools h13Autos h13Empty 3 h13Block3_0 = true := by decide +kernel
def h13Nodes3 : List NodeSpec := h13Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Check3 : checkNodesBT h13W h13G h13Mask h13Pools h13Autos h13Empty 3 h13Nodes3 = true := h13Test3_0
def h13Bucket3 : BT (List (List Nat)) := buildBucketsBT h13W h13Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h13G 3 xs.toFinset) h13Bucket3 := buildBucketsBT_sound (by decide) h13Pairs h13WOk h13PoolsOk h13AutosOk h13EmptyOk h13Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel) h13Bucket3Ok (by decide +kernel)
def h14R : List Nat := varsOf 23
def h14G : Nat := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,6,22)]) (by decide +kernel) h13Bound
def h15R : List Nat := varsOf 39
def h15G : Nat := 0xe8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,6,38)]) (by decide +kernel) h13Bound
def h9R : List Nat := varsOf 55
def h9G : Nat := 0xe8e8a8a8a8a88080e8e8a8a8a8a88080
def h9Pos : List Nat := [21,54,21,54,19,35,54,54,35,19,37,21,37,19,19,7,7,35,37,54,7,7,21,7,21,37,37,7,23,39,7,7,19,35,35,51,53,51,19,54,54,35,54,54,51,23,35,54,21,19,37]
def h9Neg : List Nat := [20,52,22,50,3,3,22,38,33,17,33,5,5,22,18,5,3,34,36,49,1,6,17,4,1,38,1,2,22,38,22,38,1,1,38,49,49,50,2,36,34,2,20,18,3,17,49,48,49,49,49]
def h9Mask : Nat := fullMask 51
def h9Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7727ffff7ff35,0x7701b05599f30),(0xcccccccccccccccccccccccccccccccc,0x2ffeff8bbe3fa,0x1b64fa2360fc),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x5ad90fffd9ccf,0x484f2a4b8c7),(0xffff0000ffff0000ffff0000ffff0000,0x3bdf911486adf,0x7ec385048624f),(0xffffffff00000000ffffffff00000000,0x4dfbe260e15ea,0x7c1bca20e058a)]
def h9Steps : List (Nat × Nat × Nat) := [(0,0,1),(3,0,1),(0,0,2),(0,1,2),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(1,3,5),(3,3,5),(1,3,7),(3,3,7),(0,3,8),(1,3,8),(2,3,8),(3,3,8),(1,4,5),(3,4,5),(1,4,7),(3,4,7),(0,4,8),(1,4,8),(2,4,8),(3,4,8),(0,5,7),(1,5,7),(3,5,8),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(2,1,3),(0,1,4),(2,1,4),(2,1,7),(0,2,3),(2,2,3),(0,2,4),(2,2,4),(2,2,5),(2,2,7),(2,2,39),(2,1,44),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(1,0,8),(2,0,8),(1,3,29),(2,3,29),(1,4,29),(2,4,29),(1,5,45),(0,3,56),(3,3,56),(0,4,56),(3,4,56),(2,0,41),(2,1,41),(0,0,68),(2,0,68),(2,2,68),(1,5,41),(2,1,69),(2,0,43),(2,1,43),(0,0,75),(2,0,75),(2,2,75),(1,5,43),(2,1,76),(0,0,10),(0,1,81),(2,1,81),(0,2,81),(2,2,81),(1,3,81),(1,4,81),(0,1,10),(2,0,88),(0,2,88),(2,2,88),(0,2,10),(2,2,82),(3,5,10),(0,1,13),(2,0,14),(2,1,96),(0,2,96),(2,2,96),(0,1,21),(2,0,22),(2,1,101),(0,2,101),(2,2,101),(1,6,7),(2,2,36),(2,0,106),(2,1,106),(1,7,36),(2,2,38),(2,0,110),(2,1,110),(1,7,38),(2,0,92),(2,1,92),(2,1,84),(3,7,10),(0,2,15),(2,2,67),(0,2,23),(2,2,74),(0,3,87),(0,32,87),(2,4,48),(1,8,48),(2,8,48),(2,1,126),(2,2,126),(0,2,95),(1,2,95),(2,2,95),(3,2,95),(1,1,118),(2,1,118),(3,1,118),(0,4,49),(3,4,49),(3,8,49),(2,1,51),(0,2,139),(2,2,139),(2,2,51),(2,1,142),(1,8,51),(0,32,86),(2,3,52),(1,8,52),(2,8,52),(2,1,148),(2,2,148),(0,2,100),(1,2,100),(2,2,100),(3,2,100),(1,1,120),(2,1,120),(3,1,120),(3,3,53),(3,8,53),(2,1,55),(0,2,160),(2,2,160),(2,2,55),(2,1,163),(1,8,55),(3,29,56),(3,8,10),(1,3,167),(1,4,167),(2,1,11),(2,2,11),(1,8,11),(0,3,172),(2,8,11),(2,1,174),(2,2,174),(1,4,174),(2,1,12),(2,2,12),(1,8,12),(0,4,180),(2,8,12),(2,1,182),(2,2,182),(1,3,182),(3,17,18),(2,4,20),(0,3,169),(0,32,169),(3,25,26),(0,32,168),(1,35,42),(1,37,40)]
def h9W : BT Decor := buildWiresBT 8 h9Base h9Steps
def h9AutoList : List (List (Nat × Nat)) := [[]]
def h9Autos : BT (List (Nat × Nat)) := btOfList 1 h9AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Pairs : goodPairs h9G h9Pos h9Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9BaseOk : ∀ x ∈ h9Base, faithful h9Pos h9Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9WOk : btAll (fun x => faithful h9Pos h9Neg x ∧ x.1 < 2^128) h9W := buildWiresBT_faithful h9BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h9G = h9G) h9Autos := btAll_ofList (autos_of (by decide +kernel))
def h9SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,6),some (subcubeFast 0 4,6),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 0 48,4),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4),some (subcubeFast 32 0,5),some (subcubeFast 32 1,4)]
def h9Slices : BT (Option (Nat × Nat)) := btOfList 4 h9SliceList
def h9Specs : List PoolSpec := [(1,[]),(0,[]),(6,[(0,0,1),(0,0,2)]),(8,[(0,0,1),(0,0,2)]),(1,[(0,0,2)]),(2,[]),(2,[(0,0,1)]),(7,[]),(9,[]),(3,[]),(6,[]),(4,[]),(8,[]),(6,[(0,0,1)]),(8,[(0,0,1)]),(5,[]),(2,[(0,0,1),(1,3,29)]),(2,[(0,0,1),(1,4,29)]),(1,[(2,2,5)]),(2,[(3,0,1)]),(2,[(2,1,7)]),(6,[(0,0,2)]),(8,[(0,0,2)]),(1,[(0,0,2),(1,3,29)]),(1,[(0,0,2),(1,4,29)]),(1,[(0,0,3)]),(2,[(0,0,3)]),(3,[(1,4,81)]),(1,[(0,0,3),(2,4,48)]),(1,[(0,0,3),(1,8,48)]),(1,[(0,0,3),(2,8,48)]),(8,[(0,0,3)]),(4,[(2,1,3)]),(4,[(2,2,3)]),(2,[(2,0,41)]),(0,[(1,3,4)]),(0,[(2,4,48)]),(2,[(0,0,3),(2,4,48)]),(3,[(2,4,48)]),(1,[(1,0,3)]),(2,[(1,0,3)]),(1,[(1,0,3),(0,4,49)]),(6,[(0,4,49)]),(1,[(1,0,3),(3,4,49)]),(1,[(1,3,5),(0,2,95)]),(1,[(1,0,3),(3,8,49)]),(1,[(1,3,5)]),(2,[(1,3,7)]),(2,[(1,0,3),(0,4,49)]),(2,[(1,0,3),(3,4,49)]),(6,[(3,4,49)]),(1,[(2,0,3)]),(2,[(2,0,3)]),(1,[(3,0,3)]),(2,[(3,0,3)]),(1,[(0,0,4)]),(2,[(0,0,4)]),(4,[(1,3,81)]),(1,[(0,0,4),(2,3,52)]),(1,[(0,0,4),(1,8,52)]),(1,[(0,0,4),(2,8,52)]),(6,[(0,0,4)]),(3,[(2,1,4)]),(3,[(2,2,4)]),(2,[(2,0,43)]),(0,[(2,3,52)]),(2,[(0,0,4),(2,3,52)]),(1,[(1,0,4)]),(2,[(1,0,4)]),(8,[(0,0,10)]),(1,[(1,0,4),(3,3,53)]),(1,[(1,4,5),(0,2,100)]),(1,[(1,0,4),(3,8,53)]),(1,[(1,4,5)]),(2,[(1,4,7)]),(2,[(1,0,4),(3,3,53)]),(8,[(3,3,53)]),(1,[(2,0,4)]),(2,[(2,0,4)]),(1,[(3,0,4)]),(2,[(3,0,4)]),(1,[(0,0,2),(2,3,29)]),(1,[(0,0,2),(2,4,29)]),(1,[(1,0,8)]),(1,[(1,0,8),(0,3,56)]),(1,[(1,0,8),(3,3,56)]),(1,[(1,0,8),(0,4,56)]),(1,[(1,0,8),(3,4,56)]),(1,[(2,0,8)]),(2,[(2,0,8)]),(1,[(3,5,8)]),(1,[(0,3,4)]),(1,[(0,3,4),(1,3,4)]),(1,[(1,3,4)]),(1,[(2,3,4)]),(1,[(2,3,4),(1,8,11)]),(1,[(2,3,4),(2,8,11)]),(1,[(3,3,4)]),(1,[(3,3,4),(1,8,12)]),(1,[(3,3,4),(2,8,12)]),(1,[(0,3,8)]),(1,[(0,3,8),(1,3,8)]),(1,[(1,3,8)]),(1,[(2,3,8)]),(1,[(3,3,8)]),(2,[(2,1,41)]),(1,[(2,2,36)]),(1,[(3,3,8),(2,4,20)]),(1,[(0,4,8)]),(1,[(0,4,8),(1,4,8)]),(1,[(1,4,8)]),(1,[(2,4,8)]),(1,[(3,4,8)]),(2,[(2,1,43)]),(1,[(2,2,38)]),(2,[(0,1,3)]),(1,[(2,2,3)]),(4,[(0,1,3)]),(2,[(2,1,3)]),(1,[(0,2,3)]),(4,[(0,2,3)]),(2,[(0,1,4)]),(1,[(2,2,4)]),(3,[(0,1,4)]),(2,[(2,1,4)]),(1,[(0,2,4)]),(3,[(0,2,4)]),(2,[(1,3,4)]),(6,[(2,0,41)]),(8,[(2,0,43)]),(2,[(0,3,4)]),(2,[(0,3,4),(1,3,4)]),(6,[(0,0,10)]),(2,[(2,3,4)]),(2,[(2,3,4),(2,1,11)]),(1,[(2,3,4),(2,2,11)]),(2,[(3,3,4)]),(2,[(3,3,4),(2,1,12)]),(1,[(3,3,4),(2,2,12)])]
def h9Pools : BT (Option BoundPool) := buildPoolsBT 8 h9W h9R h9Slices h9Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Slice9 : Slice h9R h9G (subcubeFast 32 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Slice8 : Slice h9R h9G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Slice7 : Slice h9R h9G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Slice6 : Slice h9R h9G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Slice5 : Slice h9R h9G (subcubeFast 0 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Slice4 : Slice h9R h9G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Slice3 : Slice h9R h9G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Slice2 : Slice h9R h9G (subcubeFast 0 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Slice1 : Slice h9R h9G (subcubeFast 0 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Slice0 : Slice h9R h9G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h9R h9G p.1 p.2) h9Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h9R h9G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h9Slice0) (forall_cons (fun _ h => by cases h; exact h9Slice1) (forall_cons (fun _ h => by cases h; exact h9Slice2) (forall_cons (fun _ h => by cases h; exact h9Slice3) (forall_cons (fun _ h => by cases h; exact h9Slice4) (forall_cons (fun _ h => by cases h; exact h9Slice5) (forall_cons (fun _ h => by cases h; exact h9Slice6) (forall_cons (fun _ h => by cases h; exact h9Slice7) (forall_cons (fun _ h => by cases h; exact h9Slice8) (forall_cons (fun _ h => by cases h; exact h9Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h9R h9G c) h9Pools := buildPoolsBT_sound h9SlicesOk
def h9Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G (3 - 1) xs.toFinset) h9Empty := trivial
def h9Block3_0 : List NodeSpec := [([3,8,30,87],[],[0]),([0,3,8,123],[],[0]),([3,4,30,126],[],[0]),([4,8,30,86],[],[0]),([0,4,8,145],[],[0]),([3,4,30,148],[],[0]),([4,8,30,122],[],[0]),([3,8,30,169],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test3_0 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Empty 3 h9Block3_0 = true := by decide +kernel
def h9Block3_1 : List NodeSpec := [([0,3,8,189],[],[0]),([3,8,30,181],[],[0]),([3,8,30,177],[],[0]),([4,8,30,168],[],[0]),([0,4,8,191],[],[0]),([4,8,30,173],[],[0]),([4,8,30,185],[],[0]),([4,8,30,188],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test3_1 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Empty 3 h9Block3_1 = true := by decide +kernel
def h9Nodes3 : List NodeSpec := h9Block3_0 ++ h9Block3_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Check3 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Empty 3 h9Nodes3 = true := by
  unfold h9Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h9Test3_0,h9Test3_1⟩
def h9Bucket3 : BT (List (List Nat)) := buildBucketsBT h9W h9Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G 3 xs.toFinset) h9Bucket3 := buildBucketsBT_sound (by decide) h9Pairs h9WOk h9PoolsOk h9AutosOk h9EmptyOk h9Check3
def h9Block4_0 : List NodeSpec := [([0,2,4,39,58],[],[0]),([0,2,3,39,60],[],[0]),([0,1,4,44,58],[],[0]),([0,1,3,44,60],[],[0]),([0,1,2,58,61],[],[0]),([0,1,2,59,60],[],[0]),([0,1,2,59,61],[],[0]),([0,1,3,4,93],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test4_0 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket3 4 h9Block4_0 = true := by decide +kernel
def h9Block4_1 : List NodeSpec := [([0,2,3,4,116],[],[0]),([0,3,8,32,87],[],[0]),([2,3,4,30,97],[],[0]),([0,3,4,32,126],[30],[0]),([1,2,3,30,87],[],[0]),([0,1,2,3,123],[],[0]),([0,3,4,129,130],[44],[0]),([0,3,4,129,133],[44],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test4_1 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket3 4 h9Block4_1 = true := by decide +kernel
def h9Block4_2 : List NodeSpec := [([0,4,8,32,86],[],[0]),([2,3,4,30,102],[],[0]),([0,3,4,32,148],[60],[0]),([1,2,4,30,86],[],[0]),([0,1,2,4,145],[],[0]),([0,4,8,32,122],[],[0]),([0,3,4,151,152],[71],[0]),([0,3,4,151,155],[71],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test4_2 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket3 4 h9Block4_2 = true := by decide +kernel
def h9Block4_3 : List NodeSpec := [([1,2,4,30,122],[],[0]),([1,2,3,4,166],[],[0]),([0,1,2,9,167],[15],[0]),([0,1,2,4,186],[],[0]),([0,1,2,19,187],[15],[0]),([0,3,8,32,169],[],[0]),([0,3,8,32,181],[],[0]),([0,3,8,32,177],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test4_3 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket3 4 h9Block4_3 = true := by decide +kernel
def h9Block4_4 : List NodeSpec := [([0,1,2,3,190],[],[0]),([0,4,8,32,168],[],[0]),([0,4,8,32,173],[],[0]),([0,1,2,27,188],[15],[0]),([0,4,8,32,185],[],[0]),([0,4,8,32,188],[],[0]),([0,2,10,35,112],[],[0]),([0,1,10,42,71],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test4_4 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket3 4 h9Block4_4 = true := by decide +kernel
def h9Block4_5 : List NodeSpec := [([0,2,10,37,108],[],[0]),([0,1,10,40,78],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test4_5 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket3 4 h9Block4_5 = true := by decide +kernel
def h9Nodes4 : List NodeSpec := h9Block4_0 ++ h9Block4_1 ++ h9Block4_2 ++ h9Block4_3 ++ h9Block4_4 ++ h9Block4_5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Check4 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket3 4 h9Nodes4 = true := by
  unfold h9Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h9Test4_0,h9Test4_1⟩,h9Test4_2⟩,h9Test4_3⟩,h9Test4_4⟩,h9Test4_5⟩
def h9Bucket4 : BT (List (List Nat)) := buildBucketsBT h9W h9Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G 4 xs.toFinset) h9Bucket4 := buildBucketsBT_sound (by decide) h9Pairs h9WOk h9PoolsOk h9AutosOk h9Bucket3Ok h9Check4
def h9Block5_0 : List NodeSpec := [([3,4,5,7,8],[0,1,2,3,4,5,6],[0]),([2,3,4,5,7,39],[1],[0]),([1,3,4,5,7,44],[1],[0]),([0,3,4,5,7,8],[0,1,5],[0]),([0,2,3,4,5,39],[0],[0]),([0,1,3,4,7,44],[0],[0]),([0,1,2,3,4,29],[9,10,11,12],[0]),([1,2,3,4,5,62],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_0 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_0 = true := by decide +kernel
def h9Block5_1 : List NodeSpec := [([2,3,4,5,8,56],[0],[0]),([2,3,4,5,8,57],[0],[0]),([0,3,4,5,8,44],[0,5],[0]),([0,2,3,4,5,68],[1],[0]),([0,1,3,4,41,44],[10],[0]),([0,1,2,3,4,72],[5],[0]),([0,1,2,3,4,69],[10],[0]),([0,2,3,4,5,75],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_1 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_1 = true := by decide +kernel
def h9Block5_2 : List NodeSpec := [([0,1,3,4,43,44],[12],[0]),([0,1,2,3,4,79],[5],[0]),([0,1,2,3,4,76],[12],[0]),([0,1,2,3,4,57],[],[0]),([1,2,3,4,29,57],[0],[0]),([0,1,2,3,4,39],[],[0]),([0,2,3,4,29,39],[0],[0]),([0,1,2,3,4,44],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_2 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_2 = true := by decide +kernel
def h9Block5_3 : List NodeSpec := [([0,1,3,4,29,44],[0],[0]),([0,1,2,4,29,58],[10,15],[0]),([0,1,2,4,29,59],[9],[0]),([0,1,2,3,29,60],[12,15],[0]),([0,1,2,3,29,61],[11],[0]),([1,2,3,4,5,57],[0],[0]),([0,1,2,4,5,58],[16],[0]),([0,1,2,3,5,60],[17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_3 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_3 = true := by decide +kernel
def h9Block5_4 : List NodeSpec := [([1,2,3,4,5,81],[0,7,8],[0]),([0,2,3,4,5,88],[1,9,11],[0]),([0,1,2,3,4,82],[5,9,10],[0]),([0,1,2,3,4,94],[],[0]),([1,2,3,4,5,96],[0],[0]),([1,2,3,4,5,101],[0],[0]),([1,2,3,4,7,105],[],[0]),([1,3,4,7,8,56],[5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_4 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_4 = true := by decide +kernel
def h9Block5_5 : List NodeSpec := [([1,3,4,7,8,57],[5],[0]),([0,3,4,7,8,39],[0,5],[0]),([0,2,3,4,36,39],[10],[0]),([0,1,3,4,7,106],[1],[0]),([0,1,2,3,4,109],[0],[0]),([0,1,2,3,4,98],[10],[0]),([0,2,3,4,38,39],[12],[0]),([0,1,3,4,7,110],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_5 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_5 = true := by decide +kernel
def h9Block5_6 : List NodeSpec := [([0,1,2,3,4,113],[0],[0]),([0,1,2,3,4,103],[12],[0]),([1,2,3,4,7,57],[0],[0]),([0,1,2,4,7,58],[23],[0]),([0,1,2,3,7,60],[24],[0]),([1,2,3,4,7,81],[5,7,8],[0]),([0,1,3,4,7,92],[1,9,11],[0]),([0,1,2,3,4,84],[0,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_6 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_6 = true := by decide +kernel
def h9Block5_7 : List NodeSpec := [([0,1,2,3,4,117],[],[0]),([1,2,3,4,7,67],[0],[0]),([1,2,3,4,7,74],[0],[0]),([0,1,2,3,8,87],[10,27],[0]),([0,1,2,3,8,124],[28],[0]),([0,1,2,3,4,125],[1,29],[0]),([0,1,2,3,4,126],[30],[0]),([0,1,2,4,48,106],[15],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_7 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_7 = true := by decide +kernel
def h9Block5_8 : List NodeSpec := [([0,1,2,4,36,119],[],[0]),([0,2,3,4,32,97],[10],[0]),([0,2,3,4,33,97],[10],[0]),([0,1,2,4,41,97],[],[0]),([0,1,2,3,4,128],[10],[0]),([0,1,2,4,48,68],[15],[0]),([0,1,3,4,34,119],[10],[0]),([0,1,2,3,4,127],[10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_8 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_8 = true := by decide +kernel
def h9Block5_9 : List NodeSpec := [([0,1,2,3,32,87],[10,11,27,35],[0]),([0,1,2,3,33,87],[10,27],[0]),([0,1,2,3,34,87],[10,27],[0]),([0,2,3,4,8,95],[5,9,13],[0]),([0,1,3,4,8,118],[0,9,21],[0]),([0,1,2,3,8,136],[9,41,42],[0]),([0,1,2,3,8,137],[43],[0]),([0,1,2,3,4,129],[9,44],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_9 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_9 = true := by decide +kernel
def h9Block5_10 : List NodeSpec := [([0,1,2,3,4,138],[0,5,45],[0]),([0,2,3,4,95,129],[9,13],[0]),([0,2,3,4,95,130],[1,8,9,15,46],[0]),([0,2,3,4,95,131],[],[0]),([0,2,3,4,95,132],[],[0]),([0,2,3,4,33,95],[1],[0]),([0,1,2,3,4,131],[1],[0]),([0,1,3,4,118,129],[9,21,44],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_10 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_10 = true := by decide +kernel
def h9Block5_11 : List NodeSpec := [([0,1,3,4,118,133],[1,8,9,15,47],[0]),([0,1,3,4,118,134],[],[0]),([0,1,3,4,118,135],[],[0]),([0,1,3,4,34,118],[1],[0]),([0,1,2,3,4,134],[1],[0]),([0,2,3,4,8,139],[5],[0]),([0,1,3,4,8,142],[0],[0]),([0,1,2,3,4,144],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_11 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_11 = true := by decide +kernel
def h9Block5_12 : List NodeSpec := [([0,1,2,3,4,140],[10,11,12],[0]),([0,1,2,3,4,141],[],[0]),([0,1,2,3,4,143],[],[0]),([0,1,2,4,8,86],[12,57],[0]),([0,1,2,4,8,146],[58],[0]),([0,1,2,3,4,147],[1,59],[0]),([0,1,2,3,4,148],[60],[0]),([0,1,2,3,52,110],[15],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_12 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_12 = true := by decide +kernel
def h9Block5_13 : List NodeSpec := [([0,1,2,3,38,121],[],[0]),([0,2,3,4,32,102],[12],[0]),([0,2,3,4,33,102],[12],[0]),([0,1,2,3,43,102],[],[0]),([0,1,2,3,4,150],[12],[0]),([0,1,2,3,52,75],[15],[0]),([0,1,3,4,34,121],[12],[0]),([0,1,2,3,4,149],[12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_13 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_13 = true := by decide +kernel
def h9Block5_14 : List NodeSpec := [([0,1,2,4,32,86],[9,12,35,57],[0]),([0,1,2,4,33,86],[12,57],[0]),([0,1,2,4,34,86],[12,57],[0]),([0,2,3,4,8,100],[5,11,14],[0]),([0,1,3,4,8,120],[0,11,22],[0]),([0,1,2,4,8,122],[11,69],[0]),([0,1,2,4,8,158],[70],[0]),([0,1,2,3,4,151],[11,71],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_14 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_14 = true := by decide +kernel
def h9Block5_15 : List NodeSpec := [([0,1,2,3,4,159],[0,5,72],[0]),([0,2,3,4,100,151],[11,14],[0]),([0,2,3,4,100,152],[1,7,11,15,73],[0]),([0,2,3,4,100,153],[],[0]),([0,2,3,4,100,154],[],[0]),([0,2,3,4,33,100],[1],[0]),([0,1,2,3,4,153],[1],[0]),([0,1,3,4,120,151],[11,22,71],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_15 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_15 = true := by decide +kernel
def h9Block5_16 : List NodeSpec := [([0,1,3,4,120,155],[1,7,11,15,74],[0]),([0,1,3,4,120,156],[],[0]),([0,1,3,4,120,157],[],[0]),([0,1,3,4,34,120],[1],[0]),([0,1,2,3,4,156],[1],[0]),([0,1,2,4,32,122],[1,10,11,15,69],[0]),([0,1,2,4,33,122],[],[0]),([0,1,2,4,34,122],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_16 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_16 = true := by decide +kernel
def h9Block5_17 : List NodeSpec := [([0,2,3,4,8,160],[5],[0]),([0,1,3,4,8,163],[0],[0]),([0,1,2,3,4,165],[],[0]),([0,1,2,3,4,161],[9,10,12],[0]),([0,1,2,3,4,162],[],[0]),([0,1,2,3,4,164],[],[0]),([1,2,3,4,29,56],[],[0]),([0,2,3,4,8,39],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_17 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_17 = true := by decide +kernel
def h9Block5_18 : List NodeSpec := [([0,1,3,4,8,44],[0],[0]),([0,1,2,4,8,58],[23],[0]),([0,1,2,4,8,59],[81],[0]),([0,1,2,3,8,60],[24],[0]),([0,1,2,3,8,61],[82],[0]),([0,1,2,4,8,63],[84],[0]),([0,1,2,4,8,64],[85],[0]),([0,1,2,3,8,65],[86],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_18 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_18 = true := by decide +kernel
def h9Block5_19 : List NodeSpec := [([0,1,2,3,8,66],[87],[0]),([1,2,3,4,31,57],[],[0]),([0,2,3,4,8,47],[0],[0]),([0,1,3,4,8,46],[0],[0]),([0,1,2,8,9,10],[9,10,15,92],[0]),([0,2,3,4,8,88],[5],[0]),([0,1,3,4,8,92],[0],[0]),([0,1,2,3,4,90],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_19 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_19 = true := by decide +kernel
def h9Block5_20 : List NodeSpec := [([0,1,2,3,4,167],[9,10],[0]),([0,1,2,3,4,172],[10,95],[0]),([0,1,2,3,4,174],[9,96],[0]),([0,1,2,3,4,180],[10,98],[0]),([0,1,2,3,4,182],[9,99],[0]),([0,2,3,4,8,108],[0],[0]),([0,1,3,4,8,71],[0],[0]),([0,1,2,4,17,18],[101],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_20 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_20 = true := by decide +kernel
def h9Block5_21 : List NodeSpec := [([0,1,2,4,19,20],[15],[0]),([0,1,2,3,8,169],[10,15],[0]),([0,1,2,3,8,181],[],[0]),([0,2,3,4,8,68],[0,105],[0]),([0,1,3,4,8,106],[0,106],[0]),([0,1,2,3,8,177],[],[0]),([0,1,2,3,8,187],[9,107],[0]),([0,2,3,4,8,112],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_21 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_21 = true := by decide +kernel
def h9Block5_22 : List NodeSpec := [([0,1,3,4,8,78],[0],[0]),([0,1,2,3,25,26],[109],[0]),([0,1,2,4,8,168],[12,15],[0]),([0,1,2,4,8,173],[],[0]),([0,1,2,3,27,28],[15],[0]),([0,2,3,4,8,75],[0,113],[0]),([0,1,3,4,8,110],[0,114],[0]),([0,1,2,4,8,185],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_22 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_22 = true := by decide +kernel
def h9Block5_23 : List NodeSpec := [([0,1,2,4,8,188],[11],[0]),([0,2,3,4,35,112],[9],[0]),([0,1,3,4,42,71],[10],[0]),([0,1,2,10,35,42],[10],[0]),([0,1,2,3,4,192],[],[0]),([0,1,2,4,10,71],[12],[0]),([0,1,2,4,35,92],[0],[0]),([0,1,2,3,4,99],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_23 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_23 = true := by decide +kernel
def h9Block5_24 : List NodeSpec := [([0,1,2,3,4,107],[],[0]),([0,2,3,4,37,108],[10],[0]),([0,1,3,4,40,78],[9],[0]),([0,1,2,10,37,40],[10],[0]),([0,1,2,3,4,193],[],[0]),([0,1,2,3,10,78],[10],[0]),([0,1,2,3,37,92],[0],[0]),([0,1,2,3,4,104],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_24 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_24 = true := by decide +kernel
def h9Block5_25 : List NodeSpec := [([0,1,2,3,4,111],[],[0]),([0,1,2,4,10,108],[12],[0]),([0,1,2,4,40,88],[5],[0]),([0,1,2,3,4,73],[],[0]),([0,1,2,3,4,70],[],[0]),([0,1,2,3,10,112],[10],[0]),([0,1,2,3,42,88],[5],[0]),([0,1,2,3,4,80],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_25 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_25 = true := by decide +kernel
def h9Block5_26 : List NodeSpec := [([0,1,2,3,4,77],[],[0]),([0,1,2,3,4,83],[],[0]),([0,1,2,3,4,85],[],[0]),([0,1,2,3,4,89],[],[0]),([0,1,2,3,4,91],[],[0]),([0,1,2,3,4,114],[],[0]),([0,1,2,3,4,115],[],[0]),([0,1,2,3,4,176],[10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_26 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_26 = true := by decide +kernel
def h9Block5_27 : List NodeSpec := [([0,1,2,3,4,175],[10],[0]),([0,1,2,3,4,184],[9],[0]),([0,1,2,3,4,183],[9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_27 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_27 = true := by decide +kernel
def h9Nodes5 : List NodeSpec := h9Block5_0 ++ h9Block5_1 ++ h9Block5_2 ++ h9Block5_3 ++ h9Block5_4 ++ h9Block5_5 ++ h9Block5_6 ++ h9Block5_7 ++ h9Block5_8 ++ h9Block5_9 ++ h9Block5_10 ++ h9Block5_11 ++ h9Block5_12 ++ h9Block5_13 ++ h9Block5_14 ++ h9Block5_15 ++ h9Block5_16 ++ h9Block5_17 ++ h9Block5_18 ++ h9Block5_19 ++ h9Block5_20 ++ h9Block5_21 ++ h9Block5_22 ++ h9Block5_23 ++ h9Block5_24 ++ h9Block5_25 ++ h9Block5_26 ++ h9Block5_27
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Check5 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Nodes5 = true := by
  unfold h9Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h9Test5_0,h9Test5_1⟩,h9Test5_2⟩,h9Test5_3⟩,h9Test5_4⟩,h9Test5_5⟩,h9Test5_6⟩,h9Test5_7⟩,h9Test5_8⟩,h9Test5_9⟩,h9Test5_10⟩,h9Test5_11⟩,h9Test5_12⟩,h9Test5_13⟩,h9Test5_14⟩,h9Test5_15⟩,h9Test5_16⟩,h9Test5_17⟩,h9Test5_18⟩,h9Test5_19⟩,h9Test5_20⟩,h9Test5_21⟩,h9Test5_22⟩,h9Test5_23⟩,h9Test5_24⟩,h9Test5_25⟩,h9Test5_26⟩,h9Test5_27⟩
def h9Bucket5 : BT (List (List Nat)) := buildBucketsBT h9W h9Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G 5 xs.toFinset) h9Bucket5 := buildBucketsBT_sound (by decide) h9Pairs h9WOk h9PoolsOk h9AutosOk h9Bucket4Ok h9Check5
def h9Block6_0 : List NodeSpec := [([1,2,3,4,5,7],[0,1,4,5,6,7,8],[0]),([0,1,2,3,4,5,7],[0,1,4,5,6],[0]),([1,2,3,4,5,45],[0,1,5,6,7,8],[0]),([0,2,3,4,5,8],[0,1,5,6,13,14],[0]),([0,1,2,3,4,5,41],[0,5,7,9,10],[0]),([0,1,2,3,4,5,43],[0,5,8,11,12],[0]),([0,1,2,3,4,29],[9,10,11,12],[0]),([0,1,2,3,4,5,29],[5,6,7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_0 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_0 = true := by decide +kernel
def h9Block6_1 : List NodeSpec := [([0,1,2,3,4,44],[0,1,5,6,9,10,11,12,18],[0]),([0,1,2,3,4,5,44],[0,1,5,6],[0]),([0,1,2,3,4,5,10],[0,1,7,8,9,10,11,12],[0]),([0,1,2,3,4,5,13],[0,1,7,9,10],[0]),([0,1,2,3,4,5,14],[7,9,10],[0]),([0,1,2,3,4,5,21],[0,1,8,11,12],[0]),([0,1,2,3,4,5,22],[8,11,12],[0]),([1,2,3,4,6,7],[0,1,4,5,7,8,19],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_1 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_1 = true := by decide +kernel
def h9Block6_2 : List NodeSpec := [([0,1,2,3,4,46],[0,1,4,5,7,8,9,10,11,12,20],[0]),([0,1,3,4,7,8],[0,1,4,5,21,22],[0]),([0,1,2,3,4,7,36],[0,5,7,9,10],[0]),([0,1,2,3,4,7,38],[0,5,8,11,12],[0]),([0,1,2,3,4,7,29],[0,4,7,8],[0]),([0,1,2,3,4,39],[0,1,4,5,9,10,11,12,20],[0]),([0,1,2,3,4,7,39],[0,1,4,5],[0]),([0,1,2,3,4,7,10],[1,5,7,8,9,10,11,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_2 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_2 = true := by decide +kernel
def h9Block6_3 : List NodeSpec := [([0,1,2,3,4,7,15],[1,5,7,9,10],[0]),([0,1,2,3,4,7,16],[7,9,10],[0]),([0,1,2,3,4,7,23],[1,5,8,11,12],[0]),([0,1,2,3,4,7,24],[8,11,12],[0]),([0,1,2,3,4,47],[0,1,5,6,7,8,9,10,11,12,18],[0]),([0,1,2,3,4,8,48],[9,10,25],[0]),([0,1,2,4,36,48],[0,1,9,10,15,25,31,32],[0]),([0,1,2,3,4,97],[0,1,5,7,9,10,11,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_3 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_3 = true := by decide +kernel
def h9Block6_4 : List NodeSpec := [([0,1,2,4,41,48],[1,5,9,10,15,26,31,33],[0]),([0,1,2,3,4,119],[0,1,5,7,9,10,11,12,34],[0]),([0,1,2,3,87],[7,10,11,15,27,35],[0]),([0,1,2,3,124],[7,10,12,28,36,37,38],[0]),([0,1,2,3,4,8,49],[0,1,5,9,10,39],[0]),([0,2,3,4,95],[1,7,8,9,13,46],[0]),([0,1,2,3,4,95],[0,1,5,7,8,9,11,12,13,46],[0]),([0,1,3,4,118],[1,7,8,9,21,47],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_4 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_4 = true := by decide +kernel
def h9Block6_5 : List NodeSpec := [([0,1,2,3,4,118],[0,1,5,7,8,9,11,12,21,47],[0]),([0,1,2,3,136],[1,9,12,41,42,48],[0]),([0,1,2,3,137],[1,9,11,43,49,50],[0]),([0,1,2,3,4,8,50],[7,9,10,51],[0]),([0,1,2,3,4,8,51],[0,1,5,9,10,53],[0]),([0,1,2,3,4,139],[0,1,5,8,10,11,12,53],[0]),([0,1,2,3,4,142],[0,1,5,8,10,11,12,54],[0]),([0,1,2,3,4,8,52],[11,12,55],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_5 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_5 = true := by decide +kernel
def h9Block6_6 : List NodeSpec := [([0,1,2,3,38,52],[0,1,11,12,15,55,61,62],[0]),([0,1,2,3,4,102],[0,1,5,8,9,10,11,12],[0]),([0,1,2,3,43,52],[1,5,11,12,15,56,61,63],[0]),([0,1,2,3,4,121],[0,1,5,8,9,10,11,12,64],[0]),([0,1,2,4,86],[8,9,12,15,35],[0]),([0,1,2,4,146],[7,10,12,58,65,66],[0]),([0,1,2,3,4,8,53],[0,1,5,11,12,67],[0]),([0,2,3,4,100],[1,7,11,14,73],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_6 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_6 = true := by decide +kernel
def h9Block6_7 : List NodeSpec := [([0,1,2,3,4,100],[0,1,5,7,9,10,11,14,73],[0]),([0,1,3,4,120],[1,7,11,22,74],[0]),([0,1,2,3,4,120],[0,1,5,7,9,10,11,22,74],[0]),([0,1,2,4,122],[1,10,11,69],[0]),([0,1,2,4,158],[1,9,11,70,75,76],[0]),([0,1,2,3,4,8,54],[8,11,12,77],[0]),([0,1,2,3,4,8,55],[0,1,5,11,12,79],[0]),([0,1,2,3,4,160],[0,1,5,7,9,10,12,79],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_7 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_7 = true := by decide +kernel
def h9Block6_8 : List NodeSpec := [([0,1,2,3,4,163],[0,1,5,7,9,10,12,80],[0]),([0,1,2,3,4,8,29],[1,4],[0]),([0,1,2,3,4,8,56],[0,1,5,83],[0]),([0,1,2,3,4,57],[0,5,9,10,11,12,88,89],[0]),([0,1,2,3,4,8,57],[0,1,5,88],[0]),([0,1,2,3,4,8,31],[1,90],[0]),([0,1,2,3,4,8,9],[9,10,11,12,15,91],[0]),([0,1,2,3,4,8,10],[0,5,9,10,11,12,93],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_8 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_8 = true := by decide +kernel
def h9Block6_9 : List NodeSpec := [([0,1,2,3,4,8,11],[9,10,11,12,94],[0]),([0,1,2,3,4,8,12],[9,10,11,12,97],[0]),([0,1,2,3,4,8,17],[9,10,100],[0]),([0,1,2,3,4,8,18],[9,10,102],[0]),([0,1,2,3,4,8,19],[9,10,103],[0]),([0,1,2,3,4,8,20],[9,10,104],[0]),([0,1,2,3,4,8,25],[11,12,108],[0]),([0,1,2,3,4,8,26],[11,12,110],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_9 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_9 = true := by decide +kernel
def h9Block6_10 : List NodeSpec := [([0,1,2,3,4,8,27],[11,12,111],[0]),([0,1,2,3,4,8,28],[11,12,112],[0]),([0,1,2,4,35,41],[0,5,7,9,10,33,115,116,117],[0]),([0,1,2,3,4,35,42],[0,5,9,10,11,12],[0]),([0,1,2,3,4,71],[0,1,5,7,9,10,11,12,105,116],[0]),([0,1,2,4,10,35],[0,7,9,10,12,35,93,117],[0]),([0,1,2,3,4,96],[0,1,5,7,9,10,11,12],[0]),([0,1,2,4,36,40],[0,5,7,9,10,32,118,119,120],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_10 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_10 = true := by decide +kernel
def h9Block6_11 : List NodeSpec := [([0,1,2,3,4,106],[0,1,5,9,10,11,12,15,106,118],[0]),([0,1,2,3,4,37,40],[0,5,9,10,11,12],[0]),([0,1,2,3,37,43],[0,5,8,11,12,63,121,122,123],[0]),([0,1,2,3,4,78],[0,1,5,8,9,10,11,12,113,122],[0]),([0,1,2,3,10,37],[0,8,10,11,12,35,93,123],[0]),([0,1,2,3,4,101],[0,1,5,8,9,10,11,12],[0]),([0,1,2,3,38,42],[0,5,8,11,12,62,124,125,126],[0]),([0,1,2,3,4,110],[0,1,5,9,10,11,12,15,114,124],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_11 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_11 = true := by decide +kernel
def h9Block6_12 : List NodeSpec := [([0,1,2,3,4,108],[0,1,5,7,9,10,11,12,106,118],[0]),([0,1,2,4,10,40],[5,7,9,10,12,35,120,127],[0]),([0,1,2,3,4,67],[0,1,5,7,9,10,11,12,34,128],[0]),([0,1,2,3,4,68],[0,1,5,9,10,11,12,15,105,116],[0]),([0,1,2,3,4,112],[0,1,5,8,9,10,11,12,114,124],[0]),([0,1,2,3,10,42],[5,8,10,11,12,35,126,127],[0]),([0,1,2,3,4,74],[0,1,5,8,9,10,11,12,64,129],[0]),([0,1,2,3,4,75],[0,1,5,9,10,11,12,15,113,122],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_12 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_12 = true := by decide +kernel
def h9Block6_13 : List NodeSpec := [([0,1,2,9,10],[7,9,10,15,35,92,131],[0]),([0,1,2,3,4,81],[0,1,5,7,8,9,10,11,35,69,132],[0]),([0,1,2,3,4,88],[0,1,5,9,10,11,93],[0]),([0,1,2,3,4,92],[0,1,5,9,10,11,127],[0]),([0,1,2,3,4,170],[0,1,5,7,9,10,11,15,94,134],[0]),([0,1,2,3,4,171],[0,1,5,7,9,10,11,15,133,135],[0]),([0,1,2,3,4,178],[0,1,5,8,9,10,12,15,97,137],[0]),([0,1,2,3,4,179],[0,1,5,8,9,10,12,15,136,138],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test6_13 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Block6_13 = true := by decide +kernel
def h9Nodes6 : List NodeSpec := h9Block6_0 ++ h9Block6_1 ++ h9Block6_2 ++ h9Block6_3 ++ h9Block6_4 ++ h9Block6_5 ++ h9Block6_6 ++ h9Block6_7 ++ h9Block6_8 ++ h9Block6_9 ++ h9Block6_10 ++ h9Block6_11 ++ h9Block6_12 ++ h9Block6_13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Check6 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket5 6 h9Nodes6 = true := by
  unfold h9Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h9Test6_0,h9Test6_1⟩,h9Test6_2⟩,h9Test6_3⟩,h9Test6_4⟩,h9Test6_5⟩,h9Test6_6⟩,h9Test6_7⟩,h9Test6_8⟩,h9Test6_9⟩,h9Test6_10⟩,h9Test6_11⟩,h9Test6_12⟩,h9Test6_13⟩
def h9Bucket6 : BT (List (List Nat)) := buildBucketsBT h9W h9Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G 6 xs.toFinset) h9Bucket6 := buildBucketsBT_sound (by decide) h9Pairs h9WOk h9PoolsOk h9AutosOk h9Bucket5Ok h9Check6
def h9Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,5,6,7,8,9,10,11,12],[0]),([0,1,2,3,4,6],[0,1,5,7,8,9,10,11,12,19],[0]),([0,1,2,3,4,7],[0,1,4,5,7,8,9,10,11,12],[0]),([0,1,2,3,4,45],[0,1,5,7,8,9,10,11,12],[0]),([0,1,2,3,4,48],[0,1,5,7,8,9,10,11,12,15,25,26],[0]),([0,1,2,3,4,49],[0,1,5,7,8,9,10,11,12,39,40],[0]),([0,1,2,3,4,50],[0,1,5,7,8,9,10,11,12,15,51,52],[0]),([0,1,2,3,4,51],[0,1,5,8,10,11,12,53,54],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test7_0 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket6 7 h9Block7_0 = true := by decide +kernel
def h9Block7_1 : List NodeSpec := [([0,1,2,3,4,52],[0,1,5,7,8,9,10,11,12,15,55,56],[0]),([0,1,2,3,4,53],[0,1,5,7,9,10,11,12,67,68],[0]),([0,1,2,3,4,54],[0,1,5,7,8,9,10,11,12,15,77,78],[0]),([0,1,2,3,4,55],[0,1,5,7,9,10,12,79,80],[0]),([0,1,2,3,4,8],[0,1,5,9,10,11,12],[0]),([0,1,2,3,4,35],[0,1,5,7,10,11,12,15,115],[0]),([0,1,2,3,4,36],[0,1,5,7,9,10,11,12,15,118],[0]),([0,1,2,3,4,37],[0,1,5,8,9,10,12,15,121],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test7_1 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket6 7 h9Block7_1 = true := by decide +kernel
def h9Block7_2 : List NodeSpec := [([0,1,2,3,4,38],[0,1,5,8,9,10,11,12,15,124],[0]),([0,1,2,3,4,40],[0,1,5,7,10,11,12,15,119],[0]),([0,1,2,3,4,41],[0,1,5,7,9,10,11,12,15,116],[0]),([0,1,2,3,4,42],[0,1,5,8,9,10,12,15,125],[0]),([0,1,2,3,4,43],[0,1,5,8,9,10,11,12,15,122],[0]),([0,1,2,3,4,9],[0,1,5,7,9,10,12,15,91,130],[0]),([0,1,2,3,4,10],[0,1,5,7,8,9,10,11,12,93,127],[0]),([0,1,2,3,4,11],[0,1,5,7,9,10,11,12,15,94,133],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test7_2 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket6 7 h9Block7_2 = true := by decide +kernel
def h9Block7_3 : List NodeSpec := [([0,1,2,3,4,12],[0,1,5,7,8,9,10,12,15,97,136],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test7_3 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket6 7 h9Block7_3 = true := by decide +kernel
def h9Nodes7 : List NodeSpec := h9Block7_0 ++ h9Block7_1 ++ h9Block7_2 ++ h9Block7_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Check7 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket6 7 h9Nodes7 = true := by
  unfold h9Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h9Test7_0,h9Test7_1⟩,h9Test7_2⟩,h9Test7_3⟩
def h9Bucket7 : BT (List (List Nat)) := buildBucketsBT h9W h9Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G 7 xs.toFinset) h9Bucket7 := buildBucketsBT_sound (by decide) h9Pairs h9WOk h9PoolsOk h9AutosOk h9Bucket6Ok h9Check7
def h9Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test8_0 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket7 8 h9Block8_0 = true := by decide +kernel
def h9Nodes8 : List NodeSpec := h9Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Check8 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket7 8 h9Nodes8 = true := h9Test8_0
def h9Bucket8 : BT (List (List Nat)) := buildBucketsBT h9W h9Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G 8 xs.toFinset) h9Bucket8 := buildBucketsBT_sound (by decide) h9Pairs h9WOk h9PoolsOk h9AutosOk h9Bucket7Ok h9Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 9 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h9Bucket8Ok (by decide +kernel)
def h16R : List Nat := varsOf 57
def h16G : Nat := 0xffaaaaaaaaaaaa00ffaaaaaaaaaaaa00
def h16Pos : List Nat := [17,56,17,33,9,17,56,33,56,9,9,9,17,9,33,25,25,41,41,49,49]
def h16Neg : List Nat := [16,48,24,32,8,1,40,1,24,1,0,24,0,40,0,24,1,40,1,48,1]
def h16Mask : Nat := fullMask 21
def h16Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x7af52,0x2a954),(0xffff0000ffff0000ffff0000ffff0000,0x199167,0x88907),(0xffffffff00000000ffffffff00000000,0x1e41ca,0xa204a)]
def h16Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(0,1,28),(2,2,4),(1,3,4),(0,1,31),(2,3,4),(0,2,5),(1,1,34),(3,2,5),(0,3,5),(1,1,37),(3,3,5),(2,1,8),(1,3,8),(0,2,41),(2,3,8),(3,1,9),(0,3,9),(1,2,45),(3,3,9),(2,1,12),(2,2,12),(3,1,13),(3,2,13),(1,3,18),(0,1,52),(2,3,18),(1,2,54),(1,3,19),(0,2,56),(2,3,19),(1,1,58),(1,2,22),(0,1,60),(2,2,23),(1,1,62)]
def h16W : BT Decor := buildWiresBT 6 h16Base h16Steps
def h16AutoList : List (List (Nat × Nat)) := [[]]
def h16Autos : BT (List (Nat × Nat)) := btOfList 1 h16AutoList
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
def h16Block3_0 : List NodeSpec := [([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,2,31],[],[0]),([0,1,2,33],[],[0]),([0,1,3,34],[],[0]),([0,1,3,36],[],[0]),([0,1,2,37],[],[0]),([0,1,2,39],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test3_0 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Empty 3 h16Block3_0 = true := by decide +kernel
def h16Block3_1 : List NodeSpec := [([0,2,3,35],[],[0]),([0,2,3,40],[],[0]),([0,1,2,41],[],[0]),([0,1,2,43],[],[0]),([0,2,3,29],[],[0]),([0,2,3,44],[],[0]),([0,1,2,45],[],[0]),([0,1,2,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test3_1 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Empty 3 h16Block3_1 = true := by decide +kernel
def h16Block3_2 : List NodeSpec := [([0,2,3,38],[],[0]),([0,2,3,48],[],[0]),([0,1,3,46],[],[0]),([0,1,3,49],[],[0]),([0,2,3,32],[],[0]),([0,2,3,50],[],[0]),([0,1,3,42],[],[0]),([0,1,3,51],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test3_2 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Empty 3 h16Block3_2 = true := by decide +kernel
def h16Block3_3 : List NodeSpec := [([0,3,16,17],[],[0]),([0,1,2,52],[],[0]),([0,1,2,54],[],[0]),([0,1,2,56],[],[0]),([0,1,2,58],[],[0]),([0,2,20,21],[],[0]),([0,1,3,60],[],[0]),([0,1,3,57],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test3_3 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Empty 3 h16Block3_3 = true := by decide +kernel
def h16Block3_4 : List NodeSpec := [([0,1,3,55],[],[0]),([0,1,3,62],[],[0]),([0,1,24,25],[],[0]),([0,2,3,63],[],[0]),([0,2,3,53],[],[0]),([0,2,3,59],[],[0]),([0,2,3,61],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test3_4 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Empty 3 h16Block3_4 = true := by decide +kernel
def h16Nodes3 : List NodeSpec := h16Block3_0 ++ h16Block3_1 ++ h16Block3_2 ++ h16Block3_3 ++ h16Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Check3 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Empty 3 h16Nodes3 = true := by
  unfold h16Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h16Test3_0,h16Test3_1⟩,h16Test3_2⟩,h16Test3_3⟩,h16Test3_4⟩
def h16Bucket3 : BT (List (List Nat)) := buildBucketsBT h16W h16Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G 3 xs.toFinset) h16Bucket3 := buildBucketsBT_sound (by decide) h16Pairs h16WOk h16PoolsOk h16AutosOk h16EmptyOk h16Check3
def h16Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test4_0 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket3 4 h16Block4_0 = true := by decide +kernel
def h16Block4_1 : List NodeSpec := [([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0]),([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test4_1 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket3 4 h16Block4_1 = true := by decide +kernel
def h16Block4_2 : List NodeSpec := [([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0]),([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test4_2 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket3 4 h16Block4_2 = true := by decide +kernel
def h16Nodes4 : List NodeSpec := h16Block4_0 ++ h16Block4_1 ++ h16Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Check4 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket3 4 h16Nodes4 = true := by
  unfold h16Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h16Test4_0,h16Test4_1⟩,h16Test4_2⟩
def h16Bucket4 : BT (List (List Nat)) := buildBucketsBT h16W h16Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G 4 xs.toFinset) h16Bucket4 := buildBucketsBT_sound (by decide) h16Pairs h16WOk h16PoolsOk h16AutosOk h16Bucket3Ok h16Check4
def h16Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
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
lemma h16Bound : Lower h16R h16G 6 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h16Bucket5Ok (by decide +kernel)
def h18R : List Nat := varsOf 26
def h18G : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
def h18Pos : List Nat := [18,24,10,10,24,18]
def h18Neg : List Nat := [16,16,2,8,8,2]
def h18Mask : Nat := fullMask 6
def h18Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h18Steps : List (Nat × Nat × Nat) := []
def h18W : BT Decor := buildWiresBT 2 h18Base h18Steps
def h18AutoList : List (List (Nat × Nat)) := [[]]
def h18Autos : BT (List (Nat × Nat)) := btOfList 1 h18AutoList
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
def h18Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
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
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 4 := lower_of_forestBT (essPairs := [(VAR 1,8,10),(VAR 3,2,10),(VAR 4,2,18)]) (by decide +kernel) h18Bucket3Ok (by decide +kernel)
def h17R : List Nat := varsOf 58
def h17G : Nat := 0xffccccccffcccc00ffccccccffcccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 5 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,2,34)]) (by decide +kernel) h18Bound
def h20R : List Nat := varsOf 27
def h20G : Nat := 0xaa888800aa888800aa888800aa888800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,10,11)]) (by decide +kernel) h18Bound
def h21R : List Nat := varsOf 11
def h21G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
def h21Pos : List Nat := [9,10,3,3,10,9]
def h21Neg : List Nat := [8,8,1,2,2,1]
def h21Mask : Nat := fullMask 6
def h21Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xff00ff00ff00ff00ff00ff00ff00ff00,51,3)]
def h21Steps : List (Nat × Nat × Nat) := []
def h21W : BT Decor := buildWiresBT 2 h21Base h21Steps
def h21AutoList : List (List (Nat × Nat)) := [[]]
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
def h21SliceList : List (Option (Nat × Nat)) := []
def h21Slices : BT (Option (Nat × Nat)) := btOfList 1 h21SliceList
def h21Specs : List PoolSpec := []
def h21Pools : BT (Option BoundPool) := buildPoolsBT 1 h21W h21R h21Slices h21Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h21R h21G p.1 p.2) h21Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h21R h21G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h21R h21G c) h21Pools := buildPoolsBT_sound h21SlicesOk
def h21Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h21G (3 - 1) xs.toFinset) h21Empty := trivial
def h21Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Test3_0 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Empty 3 h21Block3_0 = true := by decide +kernel
def h21Nodes3 : List NodeSpec := h21Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Check3 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Empty 3 h21Nodes3 = true := h21Test3_0
def h21Bucket3 : BT (List (List Nat)) := buildBucketsBT h21W h21Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h21G 3 xs.toFinset) h21Bucket3 := buildBucketsBT_sound (by decide) h21Pairs h21WOk h21PoolsOk h21AutosOk h21EmptyOk h21Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,1,9)]) (by decide +kernel) h21Bucket3Ok (by decide +kernel)
def h22R : List Nat := varsOf 19
def h22G : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def h22Pos : List Nat := [17,18,3,3,18,17]
def h22Neg : List Nat := [16,16,1,2,2,1]
def h22Mask : Nat := fullMask 6
def h22Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h22Steps : List (Nat × Nat × Nat) := []
def h22W : BT Decor := buildWiresBT 2 h22Base h22Steps
def h22AutoList : List (List (Nat × Nat)) := [[]]
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
def h22Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
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
lemma h22Bound : Lower h22R h22G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 4,1,17)]) (by decide +kernel) h22Bucket3Ok (by decide +kernel)
def h23R : List Nat := varsOf 27
def h23G : Nat := 0xee888888ee888888ee888888ee888888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,17,25)]) (by decide +kernel) h22Bound
def h24R : List Nat := varsOf 43
def h24G : Nat := 0xee88ee88aa88aa88ee88ee88aa88aa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,10,42)]) (by decide +kernel) h21Bound
def h25R : List Nat := varsOf 51
def h25G : Nat := 0xeeee8888aaaa8888eeee8888aaaa8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,18,50)]) (by decide +kernel) h22Bound
def h19R : List Nat := varsOf 59
def h19G : Nat := 0xee888888aa888800ee888888aa888800
def h19Pos : List Nat := [25,58,11,11,19,58,19,35,58,19,58,35,19,25,11,25,43,11,51,27]
def h19Neg : List Nat := [24,56,9,10,18,50,26,34,42,3,26,3,17,9,3,17,41,26,49,26]
def h19Mask : Nat := fullMask 20
def h19Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffadd,0x5fa04),(0xcccccccccccccccccccccccccccccccc,0xf5ffe,0xa4ff8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xbe52f,0xb254f),(0xffff0000ffff0000ffff0000ffff0000,0xcb773,0xe9473),(0xffffffff00000000ffffffff00000000,0x50da2,0x501a2)]
def h19Steps : List (Nat × Nat × Nat) := [(0,0,2),(0,0,3),(0,1,5),(2,1,7),(0,2,3),(2,3,7),(0,0,9),(2,0,9),(0,1,9),(2,1,9),(2,3,5),(2,1,11),(2,2,11),(0,1,6),(2,1,18),(2,2,18)]
def h19W : BT Decor := buildWiresBT 5 h19Base h19Steps
def h19AutoList : List (List (Nat × Nat)) := [[]]
def h19Autos : BT (List (Nat × Nat)) := btOfList 1 h19AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Pairs : goodPairs h19G h19Pos h19Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19BaseOk : ∀ x ∈ h19Base, faithful h19Pos h19Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19WOk : btAll (fun x => faithful h19Pos h19Neg x ∧ x.1 < 2^128) h19W := buildWiresBT_faithful h19BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h19G = h19G) h19Autos := btAll_ofList (autos_of (by decide +kernel))
def h19SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,6),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 0 40,4),some (subcubeFast 0 48,4),some (subcubeFast 32 0,5),some (subcubeFast 32 1,4)]
def h19Slices : BT (Option (Nat × Nat)) := btOfList 4 h19SliceList
def h19Specs : List PoolSpec := [(1,[]),(1,[(0,0,2)]),(0,[]),(2,[]),(3,[]),(4,[]),(7,[]),(4,[(0,2,3)]),(7,[(0,0,2)]),(5,[]),(8,[]),(1,[(0,0,3)]),(7,[(0,0,3)]),(6,[]),(1,[(0,2,3)])]
def h19Pools : BT (Option BoundPool) := buildPoolsBT 4 h19W h19R h19Slices h19Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Slice8 : Slice h19R h19G (subcubeFast 32 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Slice7 : Slice h19R h19G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Slice6 : Slice h19R h19G (subcubeFast 0 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Slice5 : Slice h19R h19G (subcubeFast 0 40) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Slice4 : Slice h19R h19G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Slice3 : Slice h19R h19G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Slice2 : Slice h19R h19G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Slice1 : Slice h19R h19G (subcubeFast 0 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Slice0 : Slice h19R h19G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h19R h19G p.1 p.2) h19Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h19R h19G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h19Slice0) (forall_cons (fun _ h => by cases h; exact h19Slice1) (forall_cons (fun _ h => by cases h; exact h19Slice2) (forall_cons (fun _ h => by cases h; exact h19Slice3) (forall_cons (fun _ h => by cases h; exact h19Slice4) (forall_cons (fun _ h => by cases h; exact h19Slice5) (forall_cons (fun _ h => by cases h; exact h19Slice6) (forall_cons (fun _ h => by cases h; exact h19Slice7) (forall_cons (fun _ h => by cases h; exact h19Slice8) (fun _ h => (List.not_mem_nil h).elim))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h19R h19G c) h19Pools := buildPoolsBT_sound h19SlicesOk
def h19Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h19G (4 - 1) xs.toFinset) h19Empty := trivial
def h19Block4_0 : List NodeSpec := [([0,1,2,4,10],[],[0]),([0,2,3,4,16],[],[0]),([0,1,3,4,20],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Test4_0 : checkNodesBT h19W h19G h19Mask h19Pools h19Autos h19Empty 4 h19Block4_0 = true := by decide +kernel
def h19Nodes4 : List NodeSpec := h19Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Check4 : checkNodesBT h19W h19G h19Mask h19Pools h19Autos h19Empty 4 h19Nodes4 = true := h19Test4_0
def h19Bucket4 : BT (List (List Nat)) := buildBucketsBT h19W h19Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h19G 4 xs.toFinset) h19Bucket4 := buildBucketsBT_sound (by decide) h19Pairs h19WOk h19PoolsOk h19AutosOk h19EmptyOk h19Check4
def h19Block5_0 : List NodeSpec := [([0,1,2,3,4,7],[4,5,6],[0]),([0,1,2,3,4,8],[5,6],[0]),([0,1,3,4,5,9],[2,4,7],[0]),([0,1,2,3,4,11],[0,5,6],[0]),([0,1,2,3,4,15],[],[0]),([0,1,2,3,4,18],[3,5,6],[0]),([0,1,2,3,4,19],[5,6],[0]),([0,1,2,4,6,9],[2,3,7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Test5_0 : checkNodesBT h19W h19G h19Mask h19Pools h19Autos h19Bucket4 5 h19Block5_0 = true := by decide +kernel
def h19Block5_1 : List NodeSpec := [([0,1,2,3,4,17],[],[0]),([0,1,2,3,4,12],[],[0]),([0,1,2,3,4,13],[],[0]),([0,1,2,3,4,14],[14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Test5_1 : checkNodesBT h19W h19G h19Mask h19Pools h19Autos h19Bucket4 5 h19Block5_1 = true := by decide +kernel
def h19Nodes5 : List NodeSpec := h19Block5_0 ++ h19Block5_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Check5 : checkNodesBT h19W h19G h19Mask h19Pools h19Autos h19Bucket4 5 h19Nodes5 = true := by
  unfold h19Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h19Test5_0,h19Test5_1⟩
def h19Bucket5 : BT (List (List Nat)) := buildBucketsBT h19W h19Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h19G 5 xs.toFinset) h19Bucket5 := buildBucketsBT_sound (by decide) h19Pairs h19WOk h19PoolsOk h19AutosOk h19Bucket4Ok h19Check5
def h19Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,8,9,10],[0]),([0,1,2,3,4,6],[0,2,3,4,5,6,10,11,12,13],[0]),([0,1,2,3,4,9],[0,2,3,4,5,6,7,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Test6_0 : checkNodesBT h19W h19G h19Mask h19Pools h19Autos h19Bucket5 6 h19Block6_0 = true := by decide +kernel
def h19Nodes6 : List NodeSpec := h19Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Check6 : checkNodesBT h19W h19G h19Mask h19Pools h19Autos h19Bucket5 6 h19Nodes6 = true := h19Test6_0
def h19Bucket6 : BT (List (List Nat)) := buildBucketsBT h19W h19Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h19G 6 xs.toFinset) h19Bucket6 := buildBucketsBT_sound (by decide) h19Pairs h19WOk h19PoolsOk h19AutosOk h19Bucket5Ok h19Check6
def h19Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,2,3,4,5,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Test7_0 : checkNodesBT h19W h19G h19Mask h19Pools h19Autos h19Bucket6 7 h19Block7_0 = true := by decide +kernel
def h19Nodes7 : List NodeSpec := h19Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Check7 : checkNodesBT h19W h19G h19Mask h19Pools h19Autos h19Bucket6 7 h19Nodes7 = true := h19Test7_0
def h19Bucket7 : BT (List (List Nat)) := buildBucketsBT h19W h19Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h19G 7 xs.toFinset) h19Bucket7 := buildBucketsBT_sound (by decide) h19Pairs h19WOk h19PoolsOk h19AutosOk h19Bucket6Ok h19Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 8 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,9,11),(VAR 3,3,11),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h19Bucket7Ok (by decide +kernel)
def h27R : List Nat := varsOf 21
def h27G : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def h27Pos : List Nat := [17,20,5,5,20,17]
def h27Neg : List Nat := [16,16,1,4,4,1]
def h27Mask : Nat := fullMask 6
def h27Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h27Steps : List (Nat × Nat × Nat) := []
def h27W : BT Decor := buildWiresBT 2 h27Base h27Steps
def h27AutoList : List (List (Nat × Nat)) := [[]]
def h27Autos : BT (List (Nat × Nat)) := btOfList 1 h27AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Pairs : goodPairs h27G h27Pos h27Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27BaseOk : ∀ x ∈ h27Base, faithful h27Pos h27Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27WOk : btAll (fun x => faithful h27Pos h27Neg x ∧ x.1 < 2^128) h27W := buildWiresBT_faithful h27BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h27G = h27G) h27Autos := btAll_ofList (autos_of (by decide +kernel))
def h27SliceList : List (Option (Nat × Nat)) := []
def h27Slices : BT (Option (Nat × Nat)) := btOfList 1 h27SliceList
def h27Specs : List PoolSpec := []
def h27Pools : BT (Option BoundPool) := buildPoolsBT 1 h27W h27R h27Slices h27Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h27R h27G p.1 p.2) h27Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h27R h27G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h27R h27G c) h27Pools := buildPoolsBT_sound h27SlicesOk
def h27Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h27G (3 - 1) xs.toFinset) h27Empty := trivial
def h27Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Test3_0 : checkNodesBT h27W h27G h27Mask h27Pools h27Autos h27Empty 3 h27Block3_0 = true := by decide +kernel
def h27Nodes3 : List NodeSpec := h27Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Check3 : checkNodesBT h27W h27G h27Mask h27Pools h27Autos h27Empty 3 h27Nodes3 = true := h27Test3_0
def h27Bucket3 : BT (List (List Nat)) := buildBucketsBT h27W h27Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h27G 3 xs.toFinset) h27Bucket3 := buildBucketsBT_sound (by decide) h27Pairs h27WOk h27PoolsOk h27AutosOk h27EmptyOk h27Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 4,1,17)]) (by decide +kernel) h27Bucket3Ok (by decide +kernel)
def h26R : List Nat := varsOf 53
def h26G : Nat := 0xfafaa0a0aaaaa0a0fafaa0a0aaaaa0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,20,52)]) (by decide +kernel) h27Bound
def h29R : List Nat := varsOf 28
def h29G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def h29Pos : List Nat := [20,24,12,12,24,20]
def h29Neg : List Nat := [16,16,4,8,8,4]
def h29Mask : Nat := fullMask 6
def h29Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h29Steps : List (Nat × Nat × Nat) := []
def h29W : BT Decor := buildWiresBT 2 h29Base h29Steps
def h29AutoList : List (List (Nat × Nat)) := [[]]
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
def h29SliceList : List (Option (Nat × Nat)) := []
def h29Slices : BT (Option (Nat × Nat)) := btOfList 1 h29SliceList
def h29Specs : List PoolSpec := []
def h29Pools : BT (Option BoundPool) := buildPoolsBT 1 h29W h29R h29Slices h29Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h29R h29G p.1 p.2) h29Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h29R h29G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h29R h29G c) h29Pools := buildPoolsBT_sound h29SlicesOk
def h29Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G (3 - 1) xs.toFinset) h29Empty := trivial
def h29Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test3_0 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Empty 3 h29Block3_0 = true := by decide +kernel
def h29Nodes3 : List NodeSpec := h29Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Check3 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Empty 3 h29Nodes3 = true := h29Test3_0
def h29Bucket3 : BT (List (List Nat)) := buildBucketsBT h29W h29Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G 3 xs.toFinset) h29Bucket3 := buildBucketsBT_sound (by decide) h29Pairs h29WOk h29PoolsOk h29AutosOk h29EmptyOk h29Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 4 := lower_of_forestBT (essPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 4,4,20)]) (by decide +kernel) h29Bucket3Ok (by decide +kernel)
def h28R : List Nat := varsOf 60
def h28G : Nat := 0xfff0f0f0fff0f000fff0f0f0fff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 5 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,4,36)]) (by decide +kernel) h29Bound
def h31R : List Nat := varsOf 29
def h31G : Nat := 0xaaa0a000aaa0a000aaa0a000aaa0a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,12,13)]) (by decide +kernel) h29Bound
def h32R : List Nat := varsOf 13
def h32G : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def h32Pos : List Nat := [9,12,5,5,12,9]
def h32Neg : List Nat := [8,8,1,4,4,1]
def h32Mask : Nat := fullMask 6
def h32Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xff00ff00ff00ff00ff00ff00ff00ff00,51,3)]
def h32Steps : List (Nat × Nat × Nat) := []
def h32W : BT Decor := buildWiresBT 2 h32Base h32Steps
def h32AutoList : List (List (Nat × Nat)) := [[]]
def h32Autos : BT (List (Nat × Nat)) := btOfList 1 h32AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Pairs : goodPairs h32G h32Pos h32Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32BaseOk : ∀ x ∈ h32Base, faithful h32Pos h32Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32WOk : btAll (fun x => faithful h32Pos h32Neg x ∧ x.1 < 2^128) h32W := buildWiresBT_faithful h32BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h32G = h32G) h32Autos := btAll_ofList (autos_of (by decide +kernel))
def h32SliceList : List (Option (Nat × Nat)) := []
def h32Slices : BT (Option (Nat × Nat)) := btOfList 1 h32SliceList
def h32Specs : List PoolSpec := []
def h32Pools : BT (Option BoundPool) := buildPoolsBT 1 h32W h32R h32Slices h32Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h32R h32G p.1 p.2) h32Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h32R h32G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h32R h32G c) h32Pools := buildPoolsBT_sound h32SlicesOk
def h32Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h32G (3 - 1) xs.toFinset) h32Empty := trivial
def h32Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test3_0 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Empty 3 h32Block3_0 = true := by decide +kernel
def h32Nodes3 : List NodeSpec := h32Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Check3 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Empty 3 h32Nodes3 = true := h32Test3_0
def h32Bucket3 : BT (List (List Nat)) := buildBucketsBT h32W h32Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h32G 3 xs.toFinset) h32Bucket3 := buildBucketsBT_sound (by decide) h32Pairs h32WOk h32PoolsOk h32AutosOk h32EmptyOk h32Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) h32Bucket3Ok (by decide +kernel)
def h33R : List Nat := varsOf 29
def h33G : Nat := 0xfaa0a0a0faa0a0a0faa0a0a0faa0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,17,25)]) (by decide +kernel) h27Bound
def h34R : List Nat := varsOf 45
def h34G : Nat := 0xfaa0faa0aaa0aaa0faa0faa0aaa0aaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,12,44)]) (by decide +kernel) h32Bound
def h30R : List Nat := varsOf 61
def h30G : Nat := 0xfaa0a0a0aaa0a000faa0a0a0aaa0a000
def h30Pos : List Nat := [25,60,13,13,21,60,21,37,60,21,60,37,21,25,13,25,45,13,53,29]
def h30Neg : List Nat := [24,56,9,12,20,52,28,36,44,5,28,5,17,9,5,17,41,28,49,28]
def h30Mask : Nat := fullMask 20
def h30Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffadd,0x5fa04),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf5ffe,0xa4ff8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xbe52f,0xb254f),(0xffff0000ffff0000ffff0000ffff0000,0xcb773,0xe9473),(0xffffffff00000000ffffffff00000000,0x50da2,0x501a2)]
def h30Steps : List (Nat × Nat × Nat) := [(0,0,2),(0,0,3),(0,1,5),(2,1,7),(0,2,3),(2,3,7),(0,0,9),(2,0,9),(0,1,9),(2,1,9),(2,3,5),(2,1,11),(2,2,11),(0,1,6),(2,1,18),(2,2,18)]
def h30W : BT Decor := buildWiresBT 5 h30Base h30Steps
def h30AutoList : List (List (Nat × Nat)) := [[]]
def h30Autos : BT (List (Nat × Nat)) := btOfList 1 h30AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Pairs : goodPairs h30G h30Pos h30Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30BaseOk : ∀ x ∈ h30Base, faithful h30Pos h30Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30WOk : btAll (fun x => faithful h30Pos h30Neg x ∧ x.1 < 2^128) h30W := buildWiresBT_faithful h30BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h30G = h30G) h30Autos := btAll_ofList (autos_of (by decide +kernel))
def h30SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 4,6),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 0 40,4),some (subcubeFast 0 48,4),some (subcubeFast 32 0,5),some (subcubeFast 32 1,4)]
def h30Slices : BT (Option (Nat × Nat)) := btOfList 4 h30SliceList
def h30Specs : List PoolSpec := [(1,[]),(1,[(0,0,2)]),(0,[]),(2,[]),(3,[]),(4,[]),(7,[]),(4,[(0,2,3)]),(7,[(0,0,2)]),(5,[]),(8,[]),(1,[(0,0,3)]),(7,[(0,0,3)]),(6,[]),(1,[(0,2,3)])]
def h30Pools : BT (Option BoundPool) := buildPoolsBT 4 h30W h30R h30Slices h30Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Slice8 : Slice h30R h30G (subcubeFast 32 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Slice7 : Slice h30R h30G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Slice6 : Slice h30R h30G (subcubeFast 0 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Slice5 : Slice h30R h30G (subcubeFast 0 40) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Slice4 : Slice h30R h30G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Slice3 : Slice h30R h30G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Slice2 : Slice h30R h30G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Slice1 : Slice h30R h30G (subcubeFast 0 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Slice0 : Slice h30R h30G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h30R h30G p.1 p.2) h30Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h30R h30G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h30Slice0) (forall_cons (fun _ h => by cases h; exact h30Slice1) (forall_cons (fun _ h => by cases h; exact h30Slice2) (forall_cons (fun _ h => by cases h; exact h30Slice3) (forall_cons (fun _ h => by cases h; exact h30Slice4) (forall_cons (fun _ h => by cases h; exact h30Slice5) (forall_cons (fun _ h => by cases h; exact h30Slice6) (forall_cons (fun _ h => by cases h; exact h30Slice7) (forall_cons (fun _ h => by cases h; exact h30Slice8) (fun _ h => (List.not_mem_nil h).elim))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h30R h30G c) h30Pools := buildPoolsBT_sound h30SlicesOk
def h30Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h30G (4 - 1) xs.toFinset) h30Empty := trivial
def h30Block4_0 : List NodeSpec := [([0,1,2,4,10],[],[0]),([0,2,3,4,16],[],[0]),([0,1,3,4,20],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Test4_0 : checkNodesBT h30W h30G h30Mask h30Pools h30Autos h30Empty 4 h30Block4_0 = true := by decide +kernel
def h30Nodes4 : List NodeSpec := h30Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Check4 : checkNodesBT h30W h30G h30Mask h30Pools h30Autos h30Empty 4 h30Nodes4 = true := h30Test4_0
def h30Bucket4 : BT (List (List Nat)) := buildBucketsBT h30W h30Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h30G 4 xs.toFinset) h30Bucket4 := buildBucketsBT_sound (by decide) h30Pairs h30WOk h30PoolsOk h30AutosOk h30EmptyOk h30Check4
def h30Block5_0 : List NodeSpec := [([0,1,2,3,4,7],[4,5,6],[0]),([0,1,2,3,4,8],[5,6],[0]),([0,1,3,4,5,9],[2,4,7],[0]),([0,1,2,3,4,11],[0,5,6],[0]),([0,1,2,3,4,15],[],[0]),([0,1,2,3,4,18],[3,5,6],[0]),([0,1,2,3,4,19],[5,6],[0]),([0,1,2,4,6,9],[2,3,7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Test5_0 : checkNodesBT h30W h30G h30Mask h30Pools h30Autos h30Bucket4 5 h30Block5_0 = true := by decide +kernel
def h30Block5_1 : List NodeSpec := [([0,1,2,3,4,17],[],[0]),([0,1,2,3,4,12],[],[0]),([0,1,2,3,4,13],[],[0]),([0,1,2,3,4,14],[14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Test5_1 : checkNodesBT h30W h30G h30Mask h30Pools h30Autos h30Bucket4 5 h30Block5_1 = true := by decide +kernel
def h30Nodes5 : List NodeSpec := h30Block5_0 ++ h30Block5_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Check5 : checkNodesBT h30W h30G h30Mask h30Pools h30Autos h30Bucket4 5 h30Nodes5 = true := by
  unfold h30Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h30Test5_0,h30Test5_1⟩
def h30Bucket5 : BT (List (List Nat)) := buildBucketsBT h30W h30Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h30G 5 xs.toFinset) h30Bucket5 := buildBucketsBT_sound (by decide) h30Pairs h30WOk h30PoolsOk h30AutosOk h30Bucket4Ok h30Check5
def h30Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,8,9,10],[0]),([0,1,2,3,4,6],[0,2,3,4,5,6,10,11,12,13],[0]),([0,1,2,3,4,9],[0,2,3,4,5,6,7,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Test6_0 : checkNodesBT h30W h30G h30Mask h30Pools h30Autos h30Bucket5 6 h30Block6_0 = true := by decide +kernel
def h30Nodes6 : List NodeSpec := h30Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Check6 : checkNodesBT h30W h30G h30Mask h30Pools h30Autos h30Bucket5 6 h30Nodes6 = true := h30Test6_0
def h30Bucket6 : BT (List (List Nat)) := buildBucketsBT h30W h30Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h30G 6 xs.toFinset) h30Bucket6 := buildBucketsBT_sound (by decide) h30Pairs h30WOk h30PoolsOk h30AutosOk h30Bucket5Ok h30Check6
def h30Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,2,3,4,5,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Test7_0 : checkNodesBT h30W h30G h30Mask h30Pools h30Autos h30Bucket6 7 h30Block7_0 = true := by decide +kernel
def h30Nodes7 : List NodeSpec := h30Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Check7 : checkNodesBT h30W h30G h30Mask h30Pools h30Autos h30Bucket6 7 h30Nodes7 = true := h30Test7_0
def h30Bucket7 : BT (List (List Nat)) := buildBucketsBT h30W h30Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h30G 7 xs.toFinset) h30Bucket7 := buildBucketsBT_sound (by decide) h30Pairs h30WOk h30PoolsOk h30AutosOk h30Bucket6Ok h30Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 8 := lower_of_forestBT (essPairs := [(VAR 0,12,13),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,5,21),(VAR 5,5,37)]) (by decide +kernel) h30Bucket7Ok (by decide +kernel)
def h35R : List Nat := varsOf 46
def h35G : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 7 := carry_of (swaps := [(3,4)]) (roots2 := Cofactor12080.R_18) (T2 := Cofactor12080.G_18) (by decide +kernel) Cofactor12080.low_18
def h36R : List Nat := varsOf 54
def h36G : Nat := 0xfcfcc0c0c0c0c0c0fcfcc0c0c0c0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,34,50)]) (by decide +kernel) h3Bound
def h38R : List Nat := varsOf 42
def h38G : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def h38Pos : List Nat := [34,40,10,10,40,34]
def h38Neg : List Nat := [32,32,2,8,8,2]
def h38Mask : Nat := fullMask 6
def h38Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h38Steps : List (Nat × Nat × Nat) := []
def h38W : BT Decor := buildWiresBT 2 h38Base h38Steps
def h38AutoList : List (List (Nat × Nat)) := [[]]
def h38Autos : BT (List (Nat × Nat)) := btOfList 1 h38AutoList
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
def h38SliceList : List (Option (Nat × Nat)) := []
def h38Slices : BT (Option (Nat × Nat)) := btOfList 1 h38SliceList
def h38Specs : List PoolSpec := []
def h38Pools : BT (Option BoundPool) := buildPoolsBT 1 h38W h38R h38Slices h38Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h38R h38G p.1 p.2) h38Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h38R h38G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h38R h38G c) h38Pools := buildPoolsBT_sound h38SlicesOk
def h38Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h38G (3 - 1) xs.toFinset) h38Empty := trivial
def h38Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
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
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 4 := lower_of_forestBT (essPairs := [(VAR 1,8,10),(VAR 3,2,10),(VAR 5,2,34)]) (by decide +kernel) h38Bucket3Ok (by decide +kernel)
def h37R : List Nat := varsOf 58
def h37G : Nat := 0xffcccc00cc00cc00ffcccc00cc00cc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,34,50)]) (by decide +kernel) h38Bound
def h40R : List Nat := varsOf 44
def h40G : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def h40Pos : List Nat := [36,40,12,12,40,36]
def h40Neg : List Nat := [32,32,4,8,8,4]
def h40Mask : Nat := fullMask 6
def h40Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h40Steps : List (Nat × Nat × Nat) := []
def h40W : BT Decor := buildWiresBT 2 h40Base h40Steps
def h40AutoList : List (List (Nat × Nat)) := [[]]
def h40Autos : BT (List (Nat × Nat)) := btOfList 1 h40AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Pairs : goodPairs h40G h40Pos h40Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40BaseOk : ∀ x ∈ h40Base, faithful h40Pos h40Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40WOk : btAll (fun x => faithful h40Pos h40Neg x ∧ x.1 < 2^128) h40W := buildWiresBT_faithful h40BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h40G = h40G) h40Autos := btAll_ofList (autos_of (by decide +kernel))
def h40SliceList : List (Option (Nat × Nat)) := []
def h40Slices : BT (Option (Nat × Nat)) := btOfList 1 h40SliceList
def h40Specs : List PoolSpec := []
def h40Pools : BT (Option BoundPool) := buildPoolsBT 1 h40W h40R h40Slices h40Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h40R h40G p.1 p.2) h40Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h40R h40G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h40R h40G c) h40Pools := buildPoolsBT_sound h40SlicesOk
def h40Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h40G (3 - 1) xs.toFinset) h40Empty := trivial
def h40Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Test3_0 : checkNodesBT h40W h40G h40Mask h40Pools h40Autos h40Empty 3 h40Block3_0 = true := by decide +kernel
def h40Nodes3 : List NodeSpec := h40Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Check3 : checkNodesBT h40W h40G h40Mask h40Pools h40Autos h40Empty 3 h40Nodes3 = true := h40Test3_0
def h40Bucket3 : BT (List (List Nat)) := buildBucketsBT h40W h40Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h40G 3 xs.toFinset) h40Bucket3 := buildBucketsBT_sound (by decide) h40Pairs h40WOk h40PoolsOk h40AutosOk h40EmptyOk h40Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 4 := lower_of_forestBT (essPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 5,4,36)]) (by decide +kernel) h40Bucket3Ok (by decide +kernel)
def h39R : List Nat := varsOf 60
def h39G : Nat := 0xfff0f000f000f000fff0f000f000f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,36,52)]) (by decide +kernel) h40Bound
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

def G_10 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_10 : List Nat := varsOf 38
lemma low_10_ok : carryOK [(1,3),(1,2)] R_10 G_10 R_0 G_0 = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 4 := carry_of low_10_ok low_0

def G_14 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def R_14 : List Nat := varsOf 42
lemma low_14_ok : carryOK [(1,2)] R_14 G_14 R_0 G_0 = true := by decide +kernel
lemma low_14 : Lower R_14 G_14 4 := carry_of low_14_ok low_0

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

def G_57 : Nat := 0xfcc0c000c000c000fcc0c000c000c000
def R_57 : List Nat := varsOf 62
lemma low_57_ok : liftCheck 0 16 R_57 G_57 R_20 G_20 [(VAR 4,54,38)] = true := by decide +kernel
lemma low_57 : Lower R_57 G_57 8 := lift_of low_57_ok low_20

end Cofactor12116
def h41R : List Nat := varsOf 62
def h41G : Nat := 0xfcc0c000c000c000fcc0c000c000c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 8 := carry_of (swaps := []) (roots2 := Cofactor12116.R_57) (T2 := Cofactor12116.G_57) (by decide +kernel) Cofactor12116.low_57
namespace Cofactor12116
def G_9 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_9 : List Nat := varsOf 22
lemma low_9_ok : carryOK [(4,5),(1,3),(1,2)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0

def G_13 : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
def R_13 : List Nat := varsOf 26
lemma low_13_ok : carryOK [(4,5),(1,2)] R_13 G_13 R_0 G_0 = true := by decide +kernel
lemma low_13 : Lower R_13 G_13 4 := carry_of low_13_ok low_0

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
def h42R : List Nat := varsOf 31
def h42G : Nat := 0xfee8e8a8fee8e8a8fee8e8a8fee8e8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bound : Lower h42R h42G 10 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(1,2),(0,1)]) (roots2 := Cofactor12116.R_60) (T2 := Cofactor12116.G_60) (by decide +kernel) Cofactor12116.low_60
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

def G_7 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def R_7 : List Nat := varsOf 37
lemma low_7_ok : carryOK [(4,5),(0,1)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0

def G_8 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def R_8 : List Nat := varsOf 14
lemma low_8_ok : carryOK [(3,4)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0

def G_9 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_9 : List Nat := varsOf 38
lemma low_9_ok : carryOK [(4,5)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0

def G_11 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def R_11 : List Nat := varsOf 42
lemma low_11_ok : carryOK [(4,5),(2,3)] R_11 G_11 R_0 G_0 = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 4 := carry_of low_11_ok low_0

def G_12 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def R_12 : List Nat := varsOf 44
lemma low_12_ok : carryOK [(4,5),(1,2),(1,3)] R_12 G_12 R_0 G_0 = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 4 := carry_of low_12_ok low_0

def G_14 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
def R_14 : List Nat := varsOf 46
def pos_14 : List Nat := [14,14,14,38,38,38,42,42,42,44,44,44,14,14,14,38,38,38,42,42,42,44,44,44]
def neg_14 : List Nat := [12,10,6,36,34,6,40,34,10,40,36,12,34,36,40,10,12,40,6,12,36,6,10,34]
def fmask_14 : Nat := fullMask 24
def base_14 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_14 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def W_14 : BT Decor := buildWiresBT 4 base_14 steps_14
def autosL_14 : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)],[(2,3)],[(2,5),(2,3)],[(1,2),(1,3)],[(2,5),(1,2),(1,3)],[(2,5),(1,3)]]
def autos_14 : BT (List (Nat × Nat)) := btOfList 4 autosL_14
def slicesL_14 : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def slices_14 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_14
def ps_14 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_14 : BT (Option BoundPool) := buildPoolsBT 2 W_14 R_14 slices_14 ps_14
lemma gp_14 : goodPairs G_14 pos_14 neg_14 := goodPairs_of (by decide +kernel)
lemma base_14_ok : ∀ x ∈ base_14, faithful pos_14 neg_14 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_14_ok : btAll (fun x => faithful pos_14 neg_14 x ∧ x.1 < 2^128) W_14 := buildWiresBT_faithful base_14_ok
set_option maxRecDepth 500000 in
lemma autos_14_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_14 = G_14) autos_14 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_14_0_ok : sliceDirectCheck 0 8 0 R_14 G_14 R_9 G_9 = true := by decide +kernel
lemma sl_14_0 : Slice R_14 G_14 (subcubeFast 0 8) 4 := slice_fast_direct sl_14_0_ok low_9
lemma sl_14_1_ok : sliceDirectCheck 0 2 0 R_14 G_14 R_12 G_12 = true := by decide +kernel
lemma sl_14_1 : Slice R_14 G_14 (subcubeFast 0 2) 4 := slice_fast_direct sl_14_1_ok low_12
lemma sl_14_2_ok : sliceDirectCheck 0 4 0 R_14 G_14 R_11 G_11 = true := by decide +kernel
lemma sl_14_2 : Slice R_14 G_14 (subcubeFast 0 4) 4 := slice_fast_direct sl_14_2_ok low_11
lemma sl_14_3_ok : sliceDirectCheck 0 32 0 R_14 G_14 R_8 G_8 = true := by decide +kernel
lemma sl_14_3 : Slice R_14 G_14 (subcubeFast 0 32) 4 := slice_fast_direct sl_14_3_ok low_8
set_option maxRecDepth 500000 in
lemma slices_14_ok : btAll (fun o => ∀ p, o = some p → Slice R_14 G_14 p.1 p.2) slices_14 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_14 G_14 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_14_0) (forall_cons (fun _ h => by cases h; exact sl_14_1) (forall_cons (fun _ h => by cases h; exact sl_14_2) (forall_cons (fun _ h => by cases h; exact sl_14_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_14_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_14 G_14 c) P_14 := buildPoolsBT_sound slices_14_ok
def bk_14_init : BT (List (List Nat)) := BT.empty
lemma bk_14_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 (0 - 1) xs.toFinset) bk_14_init := trivial
def nodes_14_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_0 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_init 0 nodes_14_0 = true := by decide +kernel
def bk_14_0 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_0
set_option maxRecDepth 500000 in
lemma bk_14_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 0 xs.toFinset) bk_14_0 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_init_ok chk_14_0
def nodes_14_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_1 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_0 1 nodes_14_1 = true := by decide +kernel
def bk_14_1 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_1
set_option maxRecDepth 500000 in
lemma bk_14_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 1 xs.toFinset) bk_14_1 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_0_ok chk_14_1
def nodes_14_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_2 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_1 2 nodes_14_2 = true := by decide +kernel
def bk_14_2 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_2
set_option maxRecDepth 500000 in
lemma bk_14_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 2 xs.toFinset) bk_14_2 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_1_ok chk_14_2
def nodes_14_3 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_3 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_2 3 nodes_14_3 = true := by decide +kernel
def bk_14_3 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_3
set_option maxRecDepth 500000 in
lemma bk_14_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 3 xs.toFinset) bk_14_3 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_2_ok chk_14_3
def nodes_14_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_4 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_3 4 nodes_14_4 = true := by decide +kernel
def bk_14_4 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_4
set_option maxRecDepth 500000 in
lemma bk_14_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 4 xs.toFinset) bk_14_4 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_3_ok chk_14_4
def nodes_14_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_5 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_4 5 nodes_14_5 = true := by decide +kernel
def bk_14_5 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_5
set_option maxRecDepth 500000 in
lemma bk_14_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 5 xs.toFinset) bk_14_5 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_4_ok chk_14_5
def nodes_14_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_6 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_5 6 nodes_14_6 = true := by decide +kernel
def bk_14_6 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_6
set_option maxRecDepth 500000 in
lemma bk_14_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 6 xs.toFinset) bk_14_6 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_5_ok chk_14_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_14_ok : forestRootCheck R_14 G_14 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_14_in : bucketContainsBT bk_14_6 R_14 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_14 : Lower R_14 G_14 7 := lower_of_forestBT root_14_ok bk_14_6_ok root_14_in

def G_15 : Nat := 0xfcfcc0c0fcfc0000fcfcc0c0fcfc0000
def R_15 : List Nat := varsOf 54
lemma low_15_ok : liftCheck 0 32 R_15 G_15 R_0 G_0 [(VAR 5,38,6)] = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 5 := lift_of low_15_ok low_0

def G_16 : Nat := 0xfefe8080fefe8080fefe8080fefe8080
def R_16 : List Nat := varsOf 23
def pos_16 : List Nat := [7,7,7,17,17,18,18,19,20,20,21,22,7,17,17,17,18,18,18,20,20,20]
def neg_16 : List Nat := [6,5,3,16,1,16,2,3,16,4,5,6,16,3,5,6,3,5,6,3,5,6]
def fmask_16 : Nat := fullMask 22
def base_16 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf49f,0x1b6496),(0xcccccccccccccccccccccccccccccccc,0x718e7,0x2da8c5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x381f07,0x36ce03),(0xffff0000ffff0000ffff0000ffff0000,0x3feff8,0x1128)]
def steps_16 : List (Nat × Nat × Nat) := [(3,0,3),(2,0,3),(1,0,3),(1,0,1),(0,0,3),(2,0,1),(0,0,1),(3,1,6),(0,1,6),(1,8,1),(3,8,1),(3,9,2),(1,9,2),(3,0,1),(3,10,7)]
def W_16 : BT Decor := buildWiresBT 5 base_16 steps_16
def autosL_16 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_16 : BT (List (Nat × Nat)) := btOfList 3 autosL_16
def slicesL_16 : List (Option (Nat × Nat)) := []
def slices_16 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_16
def ps_16 : List PoolSpec := []
def P_16 : BT (Option BoundPool) := buildPoolsBT 1 W_16 R_16 slices_16 ps_16
lemma gp_16 : goodPairs G_16 pos_16 neg_16 := goodPairs_of (by decide +kernel)
lemma base_16_ok : ∀ x ∈ base_16, faithful pos_16 neg_16 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_16_ok : btAll (fun x => faithful pos_16 neg_16 x ∧ x.1 < 2^128) W_16 := buildWiresBT_faithful base_16_ok
set_option maxRecDepth 500000 in
lemma autos_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_16 = G_16) autos_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_16_ok : btAll (fun o => ∀ p, o = some p → Slice R_16 G_16 p.1 p.2) slices_16 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_16 G_16 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_16_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_16 G_16 c) P_16 := buildPoolsBT_sound slices_16_ok
def bk_16_init : BT (List (List Nat)) := BT.empty
lemma bk_16_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 (0 - 1) xs.toFinset) bk_16_init := trivial
def nodes_16_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_0 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_init 0 nodes_16_0 = true := by decide +kernel
def bk_16_0 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_0
set_option maxRecDepth 500000 in
lemma bk_16_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 0 xs.toFinset) bk_16_0 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_init_ok chk_16_0
def nodes_16_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_1 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_0 1 nodes_16_1 = true := by decide +kernel
def bk_16_1 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_1
set_option maxRecDepth 500000 in
lemma bk_16_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 1 xs.toFinset) bk_16_1 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_0_ok chk_16_1
def nodes_16_2 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_2 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_1 2 nodes_16_2 = true := by decide +kernel
def bk_16_2 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_2
set_option maxRecDepth 500000 in
lemma bk_16_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 2 xs.toFinset) bk_16_2 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_1_ok chk_16_2
def nodes_16_3 : List NodeSpec := [([5,4,1,2],[],[]),([11,0,2,3],[],[]),([0,12,2,3],[],[]),([0,13,2,3],[],[]),([14,0,2,3],[],[]),([0,1,15,3],[],[]),([0,1,16,3],[],[]),([9,17,2,3],[],[0]),([10,7,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_3 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_2 3 nodes_16_3 = true := by decide +kernel
def bk_16_3 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_3
set_option maxRecDepth 500000 in
lemma bk_16_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 3 xs.toFinset) bk_16_3 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_2_ok chk_16_3
def nodes_16_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([0,1,2,3,6],[],[0,1]),([0,1,7,2,3],[],[0]),([8,0,1,2,3],[],[0,1]),([9,0,1,2,3],[],[0]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_4 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_3 4 nodes_16_4 = true := by decide +kernel
def bk_16_4 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_4
set_option maxRecDepth 500000 in
lemma bk_16_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 4 xs.toFinset) bk_16_4 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_3_ok chk_16_4
def nodes_16_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_5 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_4 5 nodes_16_5 = true := by decide +kernel
def bk_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_5
set_option maxRecDepth 500000 in
lemma bk_16_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 5 xs.toFinset) bk_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_4_ok chk_16_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck R_16 G_16 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT bk_16_5 R_16 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_16 : Lower R_16 G_16 6 := lower_of_forestBT root_16_ok bk_16_5_ok root_16_in

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

def G_19 : Nat := 0xfffffcfcffffc0c0fffffcfcffffc0c0
def R_19 : List Nat := varsOf 54
lemma low_19_ok : liftCheck 16 0 R_19 G_19 R_9 G_9 [(VAR 4,16,0)] = true := by decide +kernel
lemma low_19 : Lower R_19 G_19 5 := lift_of low_19_ok low_9

def G_21 : Nat := 0xe8e8e8e880808080e8e8e8e880808080
def R_21 : List Nat := varsOf 39
lemma low_21_ok : carryOK [(0,3),(0,2),(0,1)] R_21 G_21 R_14 G_14 = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 7 := carry_of low_21_ok low_14

def G_24 : Nat := 0xeeee8888eeee0000eeee8888eeee0000
def R_24 : List Nat := varsOf 51
lemma low_24_ok : carryOK [(0,2),(0,1)] R_24 G_24 R_15 G_15 = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 5 := carry_of low_24_ok low_15

def G_27 : Nat := 0xfafaa0a0fafa0000fafaa0a0fafa0000
def R_27 : List Nat := varsOf 53
lemma low_27_ok : carryOK [(0,1)] R_27 G_27 R_15 G_15 = true := by decide +kernel
lemma low_27 : Lower R_27 G_27 5 := carry_of low_27_ok low_15

def G_34 : Nat := 0xffffeeeeffff8888ffffeeeeffff8888
def R_34 : List Nat := varsOf 51
lemma low_34_ok : carryOK [(0,2),(0,1)] R_34 G_34 R_19 G_19 = true := by decide +kernel
lemma low_34 : Lower R_34 G_34 5 := carry_of low_34_ok low_19

def G_35 : Nat := 0xfffffafaffffa0a0fffffafaffffa0a0
def R_35 : List Nat := varsOf 53
lemma low_35_ok : carryOK [(0,1)] R_35 G_35 R_19 G_19 = true := by decide +kernel
lemma low_35 : Lower R_35 G_35 5 := carry_of low_35_ok low_19

def G_41 : Nat := 0xfefee8e8fefe8080fefee8e8fefe8080
def R_41 : List Nat := varsOf 55
def pos_41 : List Nat := [7,7,7,17,17,18,18,19,20,20,21,22,35,35,35,37,37,37,38,38,38,49,49,50,50,52,52,7,7,7,7,17,17,17,17,17,17,17,18,18,18,18,18,18,18,20,20,20,20,20,20,20,35,35,35,35,37,37,37,37,38,38,38,38]
def neg_41 : List Nat := [6,5,3,16,1,16,2,3,16,4,5,6,34,33,3,36,33,5,36,34,6,48,33,48,34,48,36,33,34,36,48,3,5,6,33,34,36,48,3,5,6,33,34,36,48,3,5,6,33,34,36,48,5,6,36,48,3,6,34,48,3,5,33,48]
def fmask_41 : Nat := fullMask 64
def base_41 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff0003ff863f49f,0x711162c588436496),(0xcccccccccccccccccccccccccccccccc,0xf0f01fc0799c78e7,0x1722a54a911858c5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff0fe0007e1f8f07,0x2274c99324168e03),(0xffff0000ffff0000ffff0000ffff0000,0xfffff87e00ff8,0x8888102042a00128),(0xffffffff00000000ffffffff00000000,0xfff0000007fff000,0xcccf1e3c7fedb000)]
def steps_41 : List (Nat × Nat × Nat) := [(2,0,1),(1,0,1),(0,0,1),(3,0,1),(3,7,6),(2,9,2),(1,9,2),(3,9,2),(0,9,2),(3,13,11)]
def W_41 : BT Decor := buildWiresBT 4 base_41 steps_41
def autosL_41 : List (List (Nat × Nat)) := [[],[(0,1)],[(1,2)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_41 : BT (List (Nat × Nat)) := btOfList 3 autosL_41
def slicesL_41 : List (Option (Nat × Nat)) := [some (subcubeFast 2 32,4),some (subcubeFast 32 0,6),some (subcubeFast 16 2,4),some (subcubeFast 0 2,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 4,5),some (subcubeFast 4 0,5),some (subcubeFast 0 32,7),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 16 0,7)]
def slices_41 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_41
def ps_41 : List PoolSpec := [(0,[]),(1,[(0,0,1),(1,0,1),(3,7,6)]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(1,[]),(9,[]),(10,[]),(8,[(1,0,1)]),(11,[(0,0,1)]),(11,[])]
def P_41 : BT (Option BoundPool) := buildPoolsBT 4 W_41 R_41 slices_41 ps_41
lemma gp_41 : goodPairs G_41 pos_41 neg_41 := goodPairs_of (by decide +kernel)
lemma base_41_ok : ∀ x ∈ base_41, faithful pos_41 neg_41 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_41_ok : btAll (fun x => faithful pos_41 neg_41 x ∧ x.1 < 2^128) W_41 := buildWiresBT_faithful base_41_ok
set_option maxRecDepth 500000 in
lemma autos_41_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_41 = G_41) autos_41 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_41_0_ok : sliceDirectCheck 2 32 0 R_41 G_41 R_6 G_6 = true := by decide +kernel
lemma sl_41_0 : Slice R_41 G_41 (subcubeFast 2 32) 4 := slice_fast_direct sl_41_0_ok low_6
lemma sl_41_1_ok : sliceDirectCheck 32 0 0 R_41 G_41 R_16 G_16 = true := by decide +kernel
lemma sl_41_1 : Slice R_41 G_41 (subcubeFast 32 0) 6 := slice_fast_direct sl_41_1_ok low_16
lemma sl_41_2_ok : sliceDirectCheck 16 2 0 R_41 G_41 R_7 G_7 = true := by decide +kernel
lemma sl_41_2 : Slice R_41 G_41 (subcubeFast 16 2) 4 := slice_fast_direct sl_41_2_ok low_7
lemma sl_41_3_ok : sliceDirectCheck 0 2 0 R_41 G_41 R_35 G_35 = true := by decide +kernel
lemma sl_41_3 : Slice R_41 G_41 (subcubeFast 0 2) 5 := slice_fast_direct sl_41_3_ok low_35
lemma sl_41_4_ok : sliceDirectCheck 0 1 0 R_41 G_41 R_19 G_19 = true := by decide +kernel
lemma sl_41_4 : Slice R_41 G_41 (subcubeFast 0 1) 5 := slice_fast_direct sl_41_4_ok low_19
lemma sl_41_5_ok : sliceDirectCheck 2 0 0 R_41 G_41 R_27 G_27 = true := by decide +kernel
lemma sl_41_5 : Slice R_41 G_41 (subcubeFast 2 0) 5 := slice_fast_direct sl_41_5_ok low_27
lemma sl_41_6_ok : sliceDirectCheck 0 4 0 R_41 G_41 R_34 G_34 = true := by decide +kernel
lemma sl_41_6 : Slice R_41 G_41 (subcubeFast 0 4) 5 := slice_fast_direct sl_41_6_ok low_34
lemma sl_41_7_ok : sliceDirectCheck 4 0 0 R_41 G_41 R_24 G_24 = true := by decide +kernel
lemma sl_41_7 : Slice R_41 G_41 (subcubeFast 4 0) 5 := slice_fast_direct sl_41_7_ok low_24
lemma sl_41_8_ok : sliceDirectCheck 0 32 0 R_41 G_41 R_17 G_17 = true := by decide +kernel
lemma sl_41_8 : Slice R_41 G_41 (subcubeFast 0 32) 7 := slice_fast_direct sl_41_8_ok low_17
lemma sl_41_9_ok : sliceDirectCheck 1 0 0 R_41 G_41 R_15 G_15 = true := by decide +kernel
lemma sl_41_9 : Slice R_41 G_41 (subcubeFast 1 0) 5 := slice_fast_direct sl_41_9_ok low_15
lemma sl_41_10_ok : sliceDirectCheck 1 32 0 R_41 G_41 R_0 G_0 = true := by decide +kernel
lemma sl_41_10 : Slice R_41 G_41 (subcubeFast 1 32) 4 := slice_fast_direct sl_41_10_ok low_0
lemma sl_41_11_ok : sliceDirectCheck 16 0 0 R_41 G_41 R_21 G_21 = true := by decide +kernel
lemma sl_41_11 : Slice R_41 G_41 (subcubeFast 16 0) 7 := slice_fast_direct sl_41_11_ok low_21
set_option maxRecDepth 500000 in
lemma slices_41_ok : btAll (fun o => ∀ p, o = some p → Slice R_41 G_41 p.1 p.2) slices_41 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_41 G_41 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_41_0) (forall_cons (fun _ h => by cases h; exact sl_41_1) (forall_cons (fun _ h => by cases h; exact sl_41_2) (forall_cons (fun _ h => by cases h; exact sl_41_3) (forall_cons (fun _ h => by cases h; exact sl_41_4) (forall_cons (fun _ h => by cases h; exact sl_41_5) (forall_cons (fun _ h => by cases h; exact sl_41_6) (forall_cons (fun _ h => by cases h; exact sl_41_7) (forall_cons (fun _ h => by cases h; exact sl_41_8) (forall_cons (fun _ h => by cases h; exact sl_41_9) (forall_cons (fun _ h => by cases h; exact sl_41_10) (forall_cons (fun _ h => by cases h; exact sl_41_11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
set_option maxRecDepth 500000 in
lemma P_41_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_41 G_41 c) P_41 := buildPoolsBT_sound slices_41_ok
def bk_41_init : BT (List (List Nat)) := BT.empty
lemma bk_41_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 (0 - 1) xs.toFinset) bk_41_init := trivial
def nodes_41_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_0 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_init 0 nodes_41_0 = true := by decide +kernel
def bk_41_0 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_0
set_option maxRecDepth 500000 in
lemma bk_41_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 0 xs.toFinset) bk_41_0 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_init_ok chk_41_0
def nodes_41_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_1 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_0 1 nodes_41_1 = true := by decide +kernel
def bk_41_1 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_1
set_option maxRecDepth 500000 in
lemma bk_41_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 1 xs.toFinset) bk_41_1 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_0_ok chk_41_1
def nodes_41_2 : List NodeSpec := [([14,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_2 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_1 2 nodes_41_2 = true := by decide +kernel
def bk_41_2 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_2
set_option maxRecDepth 500000 in
lemma bk_41_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 2 xs.toFinset) bk_41_2 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_1_ok chk_41_2
def nodes_41_3 : List NodeSpec := [([10,12,3,4],[],[0]),([13,11,3,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_3 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_2 3 nodes_41_3 = true := by decide +kernel
def bk_41_3 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_3
set_option maxRecDepth 500000 in
lemma bk_41_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 3 xs.toFinset) bk_41_3 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_2_ok chk_41_3
def nodes_41_4 : List NodeSpec := [([10,9,2,3,4],[0,1],[0]),([9,2,11,3,4],[],[0]),([9,12,2,3,4],[],[0]),([13,9,2,3,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_4 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_3 4 nodes_41_4 = true := by decide +kernel
def bk_41_4 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_4
set_option maxRecDepth 500000 in
lemma bk_41_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 4 xs.toFinset) bk_41_4 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_3_ok chk_41_4
def nodes_41_5 : List NodeSpec := [([9,2,3,4],[2,0],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_5 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_4 5 nodes_41_5 = true := by decide +kernel
def bk_41_5 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_5
set_option maxRecDepth 500000 in
lemma bk_41_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 5 xs.toFinset) bk_41_5 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_4_ok chk_41_5
def nodes_41_6 : List NodeSpec := [([5,8,2,3,4],[3,4,2,0],[0]),([7,6,2,3,4],[5,4,2,0],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_6 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_5 6 nodes_41_6 = true := by decide +kernel
def bk_41_6 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_6
set_option maxRecDepth 500000 in
lemma bk_41_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 6 xs.toFinset) bk_41_6 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_5_ok chk_41_6
def nodes_41_7 : List NodeSpec := [([5,0,1,2,3,4],[5,4,3,6,7,2,8,9,10,11],[0]),([0,1,6,2,3,4],[4,5,2,7,6,9,8,12],[0]),([7,0,1,2,3,4],[5,3,6,7,13,8,9,4,10,0],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_7 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_6 7 nodes_41_7 = true := by decide +kernel
def bk_41_7 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_7
set_option maxRecDepth 500000 in
lemma bk_41_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 7 xs.toFinset) bk_41_7 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_6_ok chk_41_7
def nodes_41_8 : List NodeSpec := [([0,1,2,3,4],[14,8],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_8 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_7 8 nodes_41_8 = true := by decide +kernel
def bk_41_8 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_8
set_option maxRecDepth 500000 in
lemma bk_41_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 8 xs.toFinset) bk_41_8 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_7_ok chk_41_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_41_ok : forestRootCheck R_41 G_41 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 4,17,1),(VAR 5,35,3)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_41_in : bucketContainsBT bk_41_8 R_41 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_41 : Lower R_41 G_41 9 := lower_of_forestBT root_41_ok bk_41_8_ok root_41_in

end Cofactor12086
def h43R : List Nat := varsOf 47
def h43G : Nat := 0xfee8fee8eaa8eaa8fee8fee8eaa8eaa8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bound : Lower h43R h43G 9 := carry_of (swaps := [(3,4),(2,3),(1,2),(0,1)]) (roots2 := Cofactor12086.R_41) (T2 := Cofactor12086.G_41) (by decide +kernel) Cofactor12086.low_41
def h45R : List Nat := varsOf 23
def h45G : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bound : Lower h45R h45G 7 := carry_of (swaps := [(3,4),(4,5),(0,1),(1,2),(2,3)]) (roots2 := Cofactor12080.R_23) (T2 := Cofactor12080.G_23) (by decide +kernel) Cofactor12080.low_23
def h44R : List Nat := varsOf 55
def h44G : Nat := 0xfefee8e8eaeae8e8fefee8e8eaeae8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bound : Lower h44R h44G 8 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,18,50)]) (by decide +kernel) h45Bound
def h47R : List Nat := varsOf 27
def h47G : Nat := 0xeeaaee88eeaaee88eeaaee88eeaaee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h47Bound : Lower h47R h47G 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,1,17)]) (by decide +kernel) h21Bound
def h48R : List Nat := varsOf 43
def h48G : Nat := 0xeeaaeeaaee88ee88eeaaeeaaee88ee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bound : Lower h48R h48G 5 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,1,33)]) (by decide +kernel) h21Bound
def h49R : List Nat := varsOf 27
def h49G : Nat := 0xffeeeeaaffeeeeaaffeeeeaaffeeeeaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bound : Lower h49R h49G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h18Bound
def h50R : List Nat := varsOf 43
def h50G : Nat := 0xffeeffeeeeaaeeaaffeeffeeeeaaeeaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bound : Lower h50R h50G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h38Bound
def h46R : List Nat := varsOf 59
def h46G : Nat := 0xffeeeeaaeeaaee88ffeeeeaaeeaaee88
def h46Pos : List Nat := [9,10,3,3,17,10,9,17,33,50,50,56,25,19,56,41,35,17,50,56,10,10,17,3,26,42,26,42,33,26,25,42,41,9,33,33,49,17,19,33,35,26,26,17,42,42,33,49,10,10,10,10]
def h46Neg : List Nat := [8,8,1,2,18,2,1,1,1,18,34,40,24,18,24,40,34,24,48,48,1,0,16,0,18,34,24,40,34,16,1,32,1,0,32,48,48,48,1,40,1,8,2,0,8,2,0,1,24,34,40,18]
def h46Mask : Nat := fullMask 52
def h46Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc9ff50c3b1dd,0x8141401001c4),(0xcccccccccccccccccccccccccccccccc,0xf3740afb5262e,0xa240013012638),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xf3603ef38d863,0x512800c02d803),(0xffff0000ffff0000ffff0000ffff0000,0x8e70654e7e90,0x90038254e7210),(0xffffffff00000000ffffffff00000000,0xf19d9a0dcf00,0x600bc9a0d8c00)]
def h46Steps : List (Nat × Nat × Nat) := [(1,0,1),(2,0,1),(1,0,2),(0,1,2),(1,1,2),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(0,3,5),(2,3,5),(0,3,7),(2,3,7),(0,3,9),(1,3,9),(2,3,9),(3,3,9),(0,4,5),(2,4,5),(0,4,7),(2,4,7),(0,4,9),(1,4,9),(2,4,9),(3,4,9),(0,5,7),(1,5,7),(2,5,9),(2,1,2),(3,1,2),(1,1,3),(3,1,3),(1,1,4),(3,1,4),(3,1,7),(1,2,3),(3,2,3),(1,2,4),(3,2,4),(3,2,5),(3,2,7),(1,2,39),(1,1,44),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,0,9),(3,0,9),(0,3,31),(3,3,31),(0,4,31),(3,4,31),(2,5,45),(1,3,56),(2,3,56),(1,4,56),(2,4,56),(1,0,41),(1,1,41),(1,0,68),(3,0,68),(3,2,68),(3,1,69),(2,5,41),(1,0,43),(1,1,43),(1,0,75),(3,0,75),(3,2,75),(3,1,76),(2,5,43),(1,0,10),(1,1,81),(3,1,81),(1,2,81),(3,2,81),(0,3,81),(0,4,81),(1,1,10),(3,0,88),(1,2,88),(3,2,88),(1,2,10),(3,2,82),(2,5,10),(1,1,14),(1,0,15),(3,1,96),(1,2,96),(3,2,96),(1,1,22),(1,0,23),(3,1,101),(1,2,101),(3,2,101),(3,6,7),(1,2,36),(3,0,106),(3,1,106),(2,7,36),(1,2,38),(3,0,110),(3,1,110),(2,7,38),(3,0,92),(3,1,92),(3,1,84),(2,7,10),(1,2,16),(3,2,67),(1,2,24),(3,2,74),(0,2,95),(1,2,95),(2,2,95),(3,2,95),(0,1,118),(2,1,118),(3,1,118),(1,4,48),(2,4,48),(2,9,48),(1,3,87),(1,8,87),(3,4,49),(0,9,49),(3,9,49),(1,1,136),(1,2,136),(1,1,50),(1,2,139),(3,2,139),(1,2,50),(3,1,142),(2,9,50),(0,2,100),(1,2,100),(2,2,100),(3,2,100),(0,1,120),(2,1,120),(3,1,120),(2,3,52),(2,9,52),(1,8,86),(3,3,53),(0,9,53),(3,9,53),(1,1,157),(1,2,157),(1,1,54),(1,2,160),(3,2,160),(1,2,54),(3,1,163),(2,9,54),(2,31,56),(2,9,10),(2,3,167),(2,4,167),(1,1,12),(1,2,12),(1,9,12),(3,1,172),(3,2,172),(0,3,172),(2,9,12),(1,4,176),(1,1,13),(1,2,13),(1,9,13),(3,1,180),(3,2,180),(0,4,180),(2,9,13),(1,3,184),(3,18,19),(1,4,20),(1,3,169),(1,8,169),(3,26,27),(1,8,168),(0,35,42),(0,37,40)]
def h46W : BT Decor := buildWiresBT 8 h46Base h46Steps
def h46AutoList : List (List (Nat × Nat)) := [[]]
def h46Autos : BT (List (Nat × Nat)) := btOfList 1 h46AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Pairs : goodPairs h46G h46Pos h46Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46BaseOk : ∀ x ∈ h46Base, faithful h46Pos h46Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46WOk : btAll (fun x => faithful h46Pos h46Neg x ∧ x.1 < 2^128) h46W := buildWiresBT_faithful h46BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h46G = h46G) h46Autos := btAll_ofList (autos_of (by decide +kernel))
def h46SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 16,4),some (subcubeFast 1 32,4),some (subcubeFast 2 0,6),some (subcubeFast 8 0,6),some (subcubeFast 16 0,5),some (subcubeFast 32 0,5),some (subcubeFast 48 0,4)]
def h46Slices : BT (Option (Nat × Nat)) := btOfList 4 h46SliceList
def h46Specs : List PoolSpec := [(5,[]),(2,[]),(6,[(1,0,1)]),(0,[(1,0,1),(1,0,2)]),(1,[(1,0,1),(1,0,2)]),(5,[(1,0,2)]),(6,[]),(3,[]),(4,[]),(7,[]),(0,[]),(8,[]),(1,[]),(0,[(1,0,1)]),(1,[(1,0,1)]),(9,[]),(6,[(1,0,1),(0,3,31)]),(6,[(1,0,1),(0,4,31)]),(5,[(3,2,5)]),(6,[(2,0,1)]),(6,[(3,1,7)]),(0,[(1,0,2)]),(1,[(1,0,2)]),(5,[(1,0,2),(0,3,31)]),(5,[(1,0,2),(0,4,31)]),(5,[(0,0,3)]),(6,[(0,0,3)]),(5,[(0,0,3),(1,4,48)]),(0,[(1,4,48)]),(5,[(0,0,3),(2,4,48)]),(5,[(0,3,5),(1,2,95)]),(5,[(0,0,3),(2,9,48)]),(5,[(0,3,5)]),(6,[(0,3,7)]),(6,[(0,0,3),(1,4,48)]),(6,[(0,0,3),(2,4,48)]),(5,[(1,0,3)]),(6,[(1,0,3)]),(7,[(0,4,81)]),(5,[(1,0,3),(3,4,49)]),(5,[(1,0,3),(0,9,49)]),(5,[(1,0,3),(3,9,49)]),(1,[(1,0,3)]),(8,[(3,1,3)]),(8,[(3,2,3)]),(6,[(1,0,41)]),(2,[(0,3,4)]),(2,[(3,4,49)]),(6,[(1,0,3),(3,4,49)]),(7,[(3,4,49)]),(5,[(2,0,3)]),(6,[(2,0,3)]),(5,[(3,0,3)]),(6,[(3,0,3)]),(5,[(0,0,4)]),(6,[(0,0,4)]),(1,[(1,0,10)]),(5,[(0,0,4),(2,3,52)]),(5,[(0,4,5),(1,2,100)]),(5,[(0,0,4),(2,9,52)]),(5,[(0,4,5)]),(6,[(0,4,7)]),(6,[(0,0,4),(2,3,52)]),(5,[(1,0,4)]),(6,[(1,0,4)]),(8,[(0,3,81)]),(5,[(1,0,4),(3,3,53)]),(5,[(1,0,4),(0,9,53)]),(5,[(1,0,4),(3,9,53)]),(0,[(1,0,4)]),(7,[(3,1,4)]),(7,[(3,2,4)]),(6,[(1,0,43)]),(2,[(3,3,53)]),(6,[(1,0,4),(3,3,53)]),(8,[(3,3,53)]),(5,[(2,0,4)]),(6,[(2,0,4)]),(5,[(3,0,4)]),(6,[(3,0,4)]),(5,[(0,0,9)]),(5,[(0,0,9),(1,3,56)]),(5,[(0,0,9),(2,3,56)]),(5,[(0,0,9),(1,4,56)]),(5,[(0,0,9),(2,4,56)]),(5,[(1,0,2),(3,3,31)]),(5,[(1,0,2),(3,4,31)]),(5,[(2,5,9)]),(5,[(3,0,9)]),(6,[(3,0,9)]),(5,[(0,3,4)]),(5,[(0,3,4),(1,3,4)]),(5,[(1,3,4)]),(5,[(2,3,4)]),(5,[(2,3,4),(1,9,12)]),(5,[(2,3,4),(2,9,12)]),(5,[(3,3,4)]),(5,[(3,3,4),(1,9,13)]),(5,[(3,3,4),(2,9,13)]),(5,[(0,3,9)]),(5,[(0,3,9),(1,3,9)]),(5,[(1,3,9)]),(5,[(2,3,9)]),(6,[(1,1,41)]),(5,[(1,2,36)]),(5,[(2,3,9),(1,4,20)]),(5,[(3,3,9)]),(5,[(0,4,9)]),(5,[(0,4,9),(1,4,9)]),(5,[(1,4,9)]),(5,[(2,4,9)]),(6,[(1,1,43)]),(5,[(1,2,38)]),(5,[(3,4,9)]),(6,[(1,1,3)]),(5,[(3,2,3)]),(8,[(1,1,3)]),(6,[(3,1,3)]),(5,[(1,2,3)]),(8,[(1,2,3)]),(6,[(1,1,4)]),(5,[(3,2,4)]),(7,[(1,1,4)]),(6,[(3,1,4)]),(5,[(1,2,4)]),(7,[(1,2,4)]),(6,[(0,3,4)]),(6,[(0,3,4),(1,3,4)]),(6,[(1,3,4)]),(6,[(2,3,4)]),(6,[(2,3,4),(1,1,12)]),(8,[(1,1,12)]),(5,[(2,3,4),(1,2,12)]),(8,[(1,2,12)]),(6,[(3,3,4)]),(6,[(3,3,4),(1,1,13)]),(7,[(1,1,13)]),(5,[(3,3,4),(1,2,13)]),(7,[(1,2,13)])]
def h46Pools : BT (Option BoundPool) := buildPoolsBT 8 h46W h46R h46Slices h46Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice9 : Slice h46R h46G (subcubeFast 48 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice8 : Slice h46R h46G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice7 : Slice h46R h46G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice6 : Slice h46R h46G (subcubeFast 8 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice5 : Slice h46R h46G (subcubeFast 2 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice4 : Slice h46R h46G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice3 : Slice h46R h46G (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice2 : Slice h46R h46G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice1 : Slice h46R h46G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice0 : Slice h46R h46G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h46R h46G p.1 p.2) h46Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h46R h46G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h46Slice0) (forall_cons (fun _ h => by cases h; exact h46Slice1) (forall_cons (fun _ h => by cases h; exact h46Slice2) (forall_cons (fun _ h => by cases h; exact h46Slice3) (forall_cons (fun _ h => by cases h; exact h46Slice4) (forall_cons (fun _ h => by cases h; exact h46Slice5) (forall_cons (fun _ h => by cases h; exact h46Slice6) (forall_cons (fun _ h => by cases h; exact h46Slice7) (forall_cons (fun _ h => by cases h; exact h46Slice8) (forall_cons (fun _ h => by cases h; exact h46Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h46R h46G c) h46Pools := buildPoolsBT_sound h46SlicesOk
def h46Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G (3 - 1) xs.toFinset) h46Empty := trivial
def h46Block3_0 : List NodeSpec := [([3,9,30,87],[],[0]),([0,3,9,133],[],[0]),([3,4,30,136],[],[0]),([4,9,30,132],[],[0]),([4,9,30,86],[],[0]),([0,4,9,154],[],[0]),([3,4,30,157],[],[0]),([3,9,30,183],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test3_0 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Empty 3 h46Block3_0 = true := by decide +kernel
def h46Block3_1 : List NodeSpec := [([3,9,30,177],[],[0]),([3,9,30,169],[],[0]),([0,3,9,189],[],[0]),([4,9,30,188],[],[0]),([4,9,30,175],[],[0]),([4,9,30,185],[],[0]),([4,9,30,168],[],[0]),([0,4,9,191],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test3_1 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Empty 3 h46Block3_1 = true := by decide +kernel
def h46Nodes3 : List NodeSpec := h46Block3_0 ++ h46Block3_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Check3 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Empty 3 h46Nodes3 = true := by
  unfold h46Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h46Test3_0,h46Test3_1⟩
def h46Bucket3 : BT (List (List Nat)) := buildBucketsBT h46W h46Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G 3 xs.toFinset) h46Bucket3 := buildBucketsBT_sound (by decide) h46Pairs h46WOk h46PoolsOk h46AutosOk h46EmptyOk h46Check3
def h46Block4_0 : List NodeSpec := [([0,2,4,39,58],[],[0]),([0,2,3,39,60],[],[0]),([0,1,4,44,58],[],[0]),([0,1,3,44,60],[],[0]),([0,1,2,58,61],[],[0]),([0,1,2,59,60],[],[0]),([0,1,2,59,61],[],[0]),([0,1,3,4,93],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test4_0 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket3 4 h46Block4_0 = true := by decide +kernel
def h46Block4_1 : List NodeSpec := [([0,2,3,4,116],[],[0]),([0,3,4,122,123],[30],[0]),([0,3,4,123,126],[30],[0]),([0,3,8,9,87],[],[0]),([2,3,4,30,97],[],[0]),([0,3,4,8,136],[41],[0]),([1,2,3,30,87],[],[0]),([0,1,2,3,133],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test4_1 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket3 4 h46Block4_1 = true := by decide +kernel
def h46Block4_2 : List NodeSpec := [([0,4,8,9,132],[],[0]),([0,3,4,145,146],[58],[0]),([0,3,4,146,149],[58],[0]),([1,2,4,30,132],[],[0]),([0,4,8,9,86],[],[0]),([2,3,4,30,102],[],[0]),([0,3,4,8,157],[68],[0]),([1,2,4,30,86],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test4_2 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket3 4 h46Block4_2 = true := by decide +kernel
def h46Block4_3 : List NodeSpec := [([0,1,2,4,154],[],[0]),([1,2,3,4,166],[],[0]),([0,1,2,11,167],[15],[0]),([0,1,2,4,186],[],[0]),([0,1,2,21,187],[15],[0]),([0,3,8,9,183],[],[0]),([0,3,8,9,177],[],[0]),([0,3,8,9,169],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test4_3 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket3 4 h46Block4_3 = true := by decide +kernel
def h46Block4_4 : List NodeSpec := [([0,1,2,3,190],[],[0]),([0,4,8,9,188],[],[0]),([0,1,2,29,188],[15],[0]),([0,4,8,9,175],[],[0]),([0,4,8,9,185],[],[0]),([0,4,8,9,168],[],[0]),([0,2,10,35,112],[],[0]),([0,1,10,42,71],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test4_4 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket3 4 h46Block4_4 = true := by decide +kernel
def h46Block4_5 : List NodeSpec := [([0,2,10,37,108],[],[0]),([0,1,10,40,78],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test4_5 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket3 4 h46Block4_5 = true := by decide +kernel
def h46Nodes4 : List NodeSpec := h46Block4_0 ++ h46Block4_1 ++ h46Block4_2 ++ h46Block4_3 ++ h46Block4_4 ++ h46Block4_5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Check4 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket3 4 h46Nodes4 = true := by
  unfold h46Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h46Test4_0,h46Test4_1⟩,h46Test4_2⟩,h46Test4_3⟩,h46Test4_4⟩,h46Test4_5⟩
def h46Bucket4 : BT (List (List Nat)) := buildBucketsBT h46W h46Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G 4 xs.toFinset) h46Bucket4 := buildBucketsBT_sound (by decide) h46Pairs h46WOk h46PoolsOk h46AutosOk h46Bucket3Ok h46Check4
def h46Block5_0 : List NodeSpec := [([3,4,5,7,9],[0,1,2,3,4,5,6],[0]),([2,3,4,5,7,39],[1],[0]),([1,3,4,5,7,44],[1],[0]),([0,3,4,5,7,9],[0,1,6],[0]),([0,2,3,4,5,39],[0],[0]),([0,1,3,4,7,44],[0],[0]),([0,1,2,3,4,31],[9,10,11,12],[0]),([1,2,3,4,5,62],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_0 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_0 = true := by decide +kernel
def h46Block5_1 : List NodeSpec := [([2,3,4,5,9,56],[0],[0]),([2,3,4,5,9,57],[0],[0]),([0,3,4,5,9,44],[0,6],[0]),([0,2,3,4,5,68],[1],[0]),([0,1,3,4,41,44],[10],[0]),([0,1,2,3,4,69],[10],[0]),([0,1,2,3,4,73],[6],[0]),([0,2,3,4,5,75],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_1 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_1 = true := by decide +kernel
def h46Block5_2 : List NodeSpec := [([0,1,3,4,43,44],[12],[0]),([0,1,2,3,4,76],[12],[0]),([0,1,2,3,4,80],[6],[0]),([0,1,2,3,4,57],[],[0]),([1,2,3,4,31,57],[0],[0]),([0,1,2,3,4,39],[],[0]),([0,2,3,4,31,39],[0],[0]),([0,1,2,3,4,44],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_2 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_2 = true := by decide +kernel
def h46Block5_3 : List NodeSpec := [([0,1,3,4,31,44],[0],[0]),([0,1,2,4,31,58],[10,15],[0]),([0,1,2,4,31,59],[9],[0]),([0,1,2,3,31,60],[12,15],[0]),([0,1,2,3,31,61],[11],[0]),([1,2,3,4,5,57],[0],[0]),([0,1,2,4,5,58],[16],[0]),([0,1,2,3,5,60],[17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_3 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_3 = true := by decide +kernel
def h46Block5_4 : List NodeSpec := [([1,2,3,4,5,81],[0,7,8],[0]),([0,2,3,4,5,88],[1,9,11],[0]),([0,1,2,3,4,82],[6,9,10],[0]),([0,1,2,3,4,94],[],[0]),([1,2,3,4,5,96],[0],[0]),([1,2,3,4,5,101],[0],[0]),([1,2,3,4,7,105],[],[0]),([1,3,4,7,9,56],[6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_4 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_4 = true := by decide +kernel
def h46Block5_5 : List NodeSpec := [([1,3,4,7,9,57],[6],[0]),([0,3,4,7,9,39],[0,6],[0]),([0,2,3,4,36,39],[10],[0]),([0,1,3,4,7,106],[1],[0]),([0,1,2,3,4,98],[10],[0]),([0,1,2,3,4,109],[0],[0]),([0,2,3,4,38,39],[12],[0]),([0,1,3,4,7,110],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_5 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_5 = true := by decide +kernel
def h46Block5_6 : List NodeSpec := [([0,1,2,3,4,103],[12],[0]),([0,1,2,3,4,113],[0],[0]),([1,2,3,4,7,57],[0],[0]),([0,1,2,4,7,58],[23],[0]),([0,1,2,3,7,60],[24],[0]),([1,2,3,4,7,81],[6,7,8],[0]),([0,1,3,4,7,92],[1,9,11],[0]),([0,1,2,3,4,84],[0,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_6 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_6 = true := by decide +kernel
def h46Block5_7 : List NodeSpec := [([0,1,2,3,4,117],[],[0]),([1,2,3,4,7,67],[0],[0]),([1,2,3,4,7,74],[0],[0]),([0,2,3,4,9,95],[6,9,13],[0]),([0,1,3,4,9,118],[0,9,21],[0]),([0,1,2,3,9,129],[9,27,28],[0]),([0,1,2,3,9,130],[29],[0]),([0,1,2,3,4,123],[9,30],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_7 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_7 = true := by decide +kernel
def h46Block5_8 : List NodeSpec := [([0,1,2,3,4,131],[0,6,31],[0]),([0,2,3,4,95,122],[1,8,9,15,32],[0]),([0,2,3,4,95,123],[9,13],[0]),([0,2,3,4,95,124],[],[0]),([0,2,3,4,95,125],[],[0]),([0,2,3,4,34,95],[1],[0]),([0,1,2,3,4,125],[1],[0]),([0,1,3,4,118,126],[1,8,9,15,33],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_8 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_8 = true := by decide +kernel
def h46Block5_9 : List NodeSpec := [([0,1,3,4,118,123],[9,21,30],[0]),([0,1,3,4,118,127],[],[0]),([0,1,3,4,118,128],[],[0]),([0,1,3,4,33,118],[1],[0]),([0,1,2,3,4,128],[1],[0]),([0,1,2,3,9,87],[10,38],[0]),([0,1,2,3,9,134],[39],[0]),([0,1,2,3,4,135],[1,40],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_9 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_9 = true := by decide +kernel
def h46Block5_10 : List NodeSpec := [([0,1,2,3,4,136],[41],[0]),([0,1,2,4,49,106],[15],[0]),([0,1,2,4,36,119],[],[0]),([0,2,3,4,8,97],[10],[0]),([0,2,3,4,34,97],[10],[0]),([0,1,2,4,41,97],[],[0]),([0,1,2,3,4,138],[10],[0]),([0,1,2,4,49,68],[15],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_10 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_10 = true := by decide +kernel
def h46Block5_11 : List NodeSpec := [([0,1,3,4,33,119],[10],[0]),([0,1,2,3,4,137],[10],[0]),([0,1,2,3,8,87],[10,11,38,46],[0]),([0,1,2,3,33,87],[10,38],[0]),([0,1,2,3,34,87],[10,38],[0]),([0,2,3,4,9,139],[6],[0]),([0,1,3,4,9,142],[0],[0]),([0,1,2,3,4,140],[10,11,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_11 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_11 = true := by decide +kernel
def h46Block5_12 : List NodeSpec := [([0,1,2,3,4,144],[],[0]),([0,1,2,3,4,141],[],[0]),([0,1,2,3,4,143],[],[0]),([0,2,3,4,9,100],[6,11,14],[0]),([0,1,3,4,9,120],[0,11,22],[0]),([0,1,2,4,9,132],[11,56],[0]),([0,1,2,4,9,152],[57],[0]),([0,1,2,3,4,146],[11,58],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_12 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_12 = true := by decide +kernel
def h46Block5_13 : List NodeSpec := [([0,1,2,3,4,153],[0,6,59],[0]),([0,2,3,4,100,145],[1,7,11,15,60],[0]),([0,2,3,4,100,146],[11,14],[0]),([0,2,3,4,100,147],[],[0]),([0,2,3,4,100,148],[],[0]),([0,2,3,4,34,100],[1],[0]),([0,1,2,3,4,148],[1],[0]),([0,1,3,4,120,149],[1,7,11,15,61],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_13 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_13 = true := by decide +kernel
def h46Block5_14 : List NodeSpec := [([0,1,3,4,120,146],[11,22,58],[0]),([0,1,3,4,120,150],[],[0]),([0,1,3,4,120,151],[],[0]),([0,1,3,4,33,120],[1],[0]),([0,1,2,3,4,151],[1],[0]),([0,1,2,4,8,132],[1,10,11,15,56],[0]),([0,1,2,4,33,132],[],[0]),([0,1,2,4,34,132],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_14 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_14 = true := by decide +kernel
def h46Block5_15 : List NodeSpec := [([0,1,2,4,9,86],[12,65],[0]),([0,1,2,4,9,155],[66],[0]),([0,1,2,3,4,156],[1,67],[0]),([0,1,2,3,4,157],[68],[0]),([0,1,2,3,53,110],[15],[0]),([0,1,2,3,38,121],[],[0]),([0,2,3,4,8,102],[12],[0]),([0,2,3,4,34,102],[12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_15 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_15 = true := by decide +kernel
def h46Block5_16 : List NodeSpec := [([0,1,2,3,43,102],[],[0]),([0,1,2,3,4,159],[12],[0]),([0,1,2,3,53,75],[15],[0]),([0,1,3,4,33,121],[12],[0]),([0,1,2,3,4,158],[12],[0]),([0,1,2,4,8,86],[9,12,46,65],[0]),([0,1,2,4,33,86],[12,65],[0]),([0,1,2,4,34,86],[12,65],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_16 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_16 = true := by decide +kernel
def h46Block5_17 : List NodeSpec := [([0,2,3,4,9,160],[6],[0]),([0,1,3,4,9,163],[0],[0]),([0,1,2,3,4,161],[9,10,12],[0]),([0,1,2,3,4,165],[],[0]),([0,1,2,3,4,162],[],[0]),([0,1,2,3,4,164],[],[0]),([1,2,3,4,31,56],[],[0]),([0,1,2,4,9,63],[81],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_17 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_17 = true := by decide +kernel
def h46Block5_18 : List NodeSpec := [([0,1,2,4,9,64],[82],[0]),([0,1,2,3,9,65],[83],[0]),([0,1,2,3,9,66],[84],[0]),([0,2,3,4,9,39],[0],[0]),([0,1,3,4,9,44],[0],[0]),([0,1,2,4,9,58],[23],[0]),([0,1,2,4,9,59],[85],[0]),([0,1,2,3,9,60],[24],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_18 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_18 = true := by decide +kernel
def h46Block5_19 : List NodeSpec := [([0,1,2,3,9,61],[86],[0]),([1,2,3,4,32,57],[],[0]),([0,2,3,4,9,47],[0],[0]),([0,1,3,4,9,46],[0],[0]),([0,2,3,4,9,88],[6],[0]),([0,1,3,4,9,92],[0],[0]),([0,1,2,9,10,11],[9,10,15,91],[0]),([0,1,2,3,4,90],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_19 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_19 = true := by decide +kernel
def h46Block5_20 : List NodeSpec := [([0,1,2,3,4,167],[9,10],[0]),([0,1,2,3,4,172],[9,94],[0]),([0,1,2,3,4,176],[10,95],[0]),([0,1,2,3,4,180],[9,97],[0]),([0,1,2,3,4,184],[10,98],[0]),([0,1,2,4,18,19],[100],[0]),([0,2,3,4,9,108],[0],[0]),([0,1,3,4,9,71],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_20 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_20 = true := by decide +kernel
def h46Block5_21 : List NodeSpec := [([0,2,3,4,9,68],[0,103],[0]),([0,1,3,4,9,106],[0,104],[0]),([0,1,2,4,20,21],[15],[0]),([0,1,2,3,9,187],[9,105],[0]),([0,1,2,3,9,183],[],[0]),([0,1,2,3,9,177],[],[0]),([0,1,2,3,9,169],[10,15],[0]),([0,1,2,3,26,27],[108],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_21 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_21 = true := by decide +kernel
def h46Block5_22 : List NodeSpec := [([0,2,3,4,9,112],[0],[0]),([0,1,3,4,9,78],[0],[0]),([0,2,3,4,9,75],[0,111],[0]),([0,1,3,4,9,110],[0,112],[0]),([0,1,2,4,9,188],[11],[0]),([0,1,2,4,9,175],[],[0]),([0,1,2,3,28,29],[15],[0]),([0,1,2,4,9,185],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_22 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_22 = true := by decide +kernel
def h46Block5_23 : List NodeSpec := [([0,1,2,4,9,168],[12,15],[0]),([0,2,3,4,35,112],[9],[0]),([0,1,3,4,42,71],[10],[0]),([0,1,2,10,35,42],[10],[0]),([0,1,2,3,4,192],[],[0]),([0,1,2,4,10,71],[12],[0]),([0,1,2,4,35,92],[0],[0]),([0,1,2,3,4,99],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_23 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_23 = true := by decide +kernel
def h46Block5_24 : List NodeSpec := [([0,1,2,3,4,107],[],[0]),([0,2,3,4,37,108],[10],[0]),([0,1,3,4,40,78],[9],[0]),([0,1,2,10,37,40],[10],[0]),([0,1,2,3,4,193],[],[0]),([0,1,2,3,10,78],[10],[0]),([0,1,2,3,37,92],[0],[0]),([0,1,2,3,4,104],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_24 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_24 = true := by decide +kernel
def h46Block5_25 : List NodeSpec := [([0,1,2,3,4,111],[],[0]),([0,1,2,4,10,108],[12],[0]),([0,1,2,4,40,88],[6],[0]),([0,1,2,3,4,72],[],[0]),([0,1,2,3,4,70],[],[0]),([0,1,2,3,10,112],[10],[0]),([0,1,2,3,42,88],[6],[0]),([0,1,2,3,4,79],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_25 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_25 = true := by decide +kernel
def h46Block5_26 : List NodeSpec := [([0,1,2,3,4,77],[],[0]),([0,1,2,3,4,83],[],[0]),([0,1,2,3,4,85],[],[0]),([0,1,2,3,4,89],[],[0]),([0,1,2,3,4,91],[],[0]),([0,1,2,3,4,114],[],[0]),([0,1,2,3,4,115],[],[0]),([0,1,2,3,4,174],[9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_26 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_26 = true := by decide +kernel
def h46Block5_27 : List NodeSpec := [([0,1,2,3,4,173],[9],[0]),([0,1,2,3,4,182],[10],[0]),([0,1,2,3,4,181],[10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_27 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_27 = true := by decide +kernel
def h46Nodes5 : List NodeSpec := h46Block5_0 ++ h46Block5_1 ++ h46Block5_2 ++ h46Block5_3 ++ h46Block5_4 ++ h46Block5_5 ++ h46Block5_6 ++ h46Block5_7 ++ h46Block5_8 ++ h46Block5_9 ++ h46Block5_10 ++ h46Block5_11 ++ h46Block5_12 ++ h46Block5_13 ++ h46Block5_14 ++ h46Block5_15 ++ h46Block5_16 ++ h46Block5_17 ++ h46Block5_18 ++ h46Block5_19 ++ h46Block5_20 ++ h46Block5_21 ++ h46Block5_22 ++ h46Block5_23 ++ h46Block5_24 ++ h46Block5_25 ++ h46Block5_26 ++ h46Block5_27
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Check5 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Nodes5 = true := by
  unfold h46Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h46Test5_0,h46Test5_1⟩,h46Test5_2⟩,h46Test5_3⟩,h46Test5_4⟩,h46Test5_5⟩,h46Test5_6⟩,h46Test5_7⟩,h46Test5_8⟩,h46Test5_9⟩,h46Test5_10⟩,h46Test5_11⟩,h46Test5_12⟩,h46Test5_13⟩,h46Test5_14⟩,h46Test5_15⟩,h46Test5_16⟩,h46Test5_17⟩,h46Test5_18⟩,h46Test5_19⟩,h46Test5_20⟩,h46Test5_21⟩,h46Test5_22⟩,h46Test5_23⟩,h46Test5_24⟩,h46Test5_25⟩,h46Test5_26⟩,h46Test5_27⟩
def h46Bucket5 : BT (List (List Nat)) := buildBucketsBT h46W h46Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G 5 xs.toFinset) h46Bucket5 := buildBucketsBT_sound (by decide) h46Pairs h46WOk h46PoolsOk h46AutosOk h46Bucket4Ok h46Check5
def h46Block6_0 : List NodeSpec := [([1,2,3,4,5,7],[0,1,2,5,6,7,8],[0]),([0,1,2,3,4,5,7],[0,1,2,5,6],[0]),([1,2,3,4,5,45],[0,1,2,6,7,8],[0]),([0,2,3,4,5,9],[0,1,2,6,13,14],[0]),([0,1,2,3,4,5,41],[0,6,7,9,10],[0]),([0,1,2,3,4,5,43],[0,6,8,11,12],[0]),([0,1,2,3,4,31],[9,10,11,12],[0]),([0,1,2,3,4,5,31],[2,6,7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_0 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_0 = true := by decide +kernel
def h46Block6_1 : List NodeSpec := [([0,1,2,3,4,44],[0,1,2,6,9,10,11,12,18],[0]),([0,1,2,3,4,5,44],[0,1,2,6],[0]),([0,1,2,3,4,5,10],[0,1,7,8,9,10,11,12],[0]),([0,1,2,3,4,5,14],[0,1,7,9,10],[0]),([0,1,2,3,4,5,15],[7,9,10],[0]),([0,1,2,3,4,5,22],[0,1,8,11,12],[0]),([0,1,2,3,4,5,23],[8,11,12],[0]),([1,2,3,4,6,7],[0,1,5,6,7,8,19],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_1 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_1 = true := by decide +kernel
def h46Block6_2 : List NodeSpec := [([0,1,2,3,4,46],[0,1,5,6,7,8,9,10,11,12,20],[0]),([0,1,3,4,7,9],[0,1,5,6,21,22],[0]),([0,1,2,3,4,7,36],[0,6,7,9,10],[0]),([0,1,2,3,4,7,38],[0,6,8,11,12],[0]),([0,1,2,3,4,7,31],[0,5,7,8],[0]),([0,1,2,3,4,39],[0,1,5,6,9,10,11,12,20],[0]),([0,1,2,3,4,7,39],[0,1,5,6],[0]),([0,1,2,3,4,7,10],[1,6,7,8,9,10,11,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_2 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_2 = true := by decide +kernel
def h46Block6_3 : List NodeSpec := [([0,1,2,3,4,7,16],[1,6,7,9,10],[0]),([0,1,2,3,4,7,17],[7,9,10],[0]),([0,1,2,3,4,7,24],[1,6,8,11,12],[0]),([0,1,2,3,4,7,25],[8,11,12],[0]),([0,1,2,3,4,47],[0,1,2,6,7,8,9,10,11,12,18],[0]),([0,1,2,3,4,9,48],[0,1,6,9,10,25],[0]),([0,2,3,4,95],[1,7,8,9,32],[0]),([0,1,2,3,4,95],[0,1,6,7,8,9,11,12,32],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_3 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_3 = true := by decide +kernel
def h46Block6_4 : List NodeSpec := [([0,1,3,4,118],[1,7,8,9,33],[0]),([0,1,2,3,4,118],[0,1,6,7,8,9,11,12,33],[0]),([0,1,2,3,129],[1,9,12,27,34],[0]),([0,1,2,3,130],[1,9,11,29,35],[0]),([0,1,2,3,4,9,49],[9,10,36],[0]),([0,1,2,4,36,49],[0,1,9,10,15,36,42,43],[0]),([0,1,2,3,4,97],[0,1,6,7,9,10,11,12],[0]),([0,1,2,4,41,49],[1,6,9,10,15,37,42,44],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_4 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_4 = true := by decide +kernel
def h46Block6_5 : List NodeSpec := [([0,1,2,3,4,119],[0,1,6,7,9,10,11,12,45],[0]),([0,1,2,3,87],[7,10,11,15,38,46],[0]),([0,1,2,3,134],[7,10,12,39,47,48,49],[0]),([0,1,2,3,4,9,50],[0,1,6,9,10,50],[0]),([0,1,2,3,4,139],[0,1,6,8,10,11,12,50],[0]),([0,1,2,3,4,142],[0,1,6,8,10,11,12,51],[0]),([0,1,2,3,4,9,51],[7,9,10,52],[0]),([0,1,2,3,4,9,52],[0,1,6,11,12,54],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_5 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_5 = true := by decide +kernel
def h46Block6_6 : List NodeSpec := [([0,2,3,4,100],[1,7,11,60],[0]),([0,1,2,3,4,100],[0,1,6,7,9,10,11,60],[0]),([0,1,3,4,120],[1,7,11,61],[0]),([0,1,2,3,4,120],[0,1,6,7,9,10,11,61],[0]),([0,1,2,4,132],[1,10,11],[0]),([0,1,2,4,152],[1,9,11,57,62],[0]),([0,1,2,3,4,9,53],[11,12,63],[0]),([0,1,2,3,38,53],[0,1,11,12,15,63,69,70],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_6 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_6 = true := by decide +kernel
def h46Block6_7 : List NodeSpec := [([0,1,2,3,4,102],[0,1,6,8,9,10,11,12],[0]),([0,1,2,3,43,53],[1,6,11,12,15,64,69,71],[0]),([0,1,2,3,4,121],[0,1,6,8,9,10,11,12,72],[0]),([0,1,2,4,86],[8,9,12,15,46,65],[0]),([0,1,2,4,155],[7,10,12,66,73,74,75],[0]),([0,1,2,3,4,9,54],[0,1,6,11,12,76],[0]),([0,1,2,3,4,160],[0,1,6,7,9,10,12,76],[0]),([0,1,2,3,4,163],[0,1,6,7,9,10,12,77],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_7 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_7 = true := by decide +kernel
def h46Block6_8 : List NodeSpec := [([0,1,2,3,4,9,55],[8,11,12,78],[0]),([0,1,2,3,4,9,56],[0,1,6,80],[0]),([0,1,2,3,4,9,31],[1,5],[0]),([0,1,2,3,4,9,32],[1,87],[0]),([0,1,2,3,4,57],[0,6,9,10,11,12,88,89],[0]),([0,1,2,3,4,9,57],[0,1,6,88],[0]),([0,1,2,3,4,9,10],[0,6,9,10,11,12,90],[0]),([0,1,2,3,4,9,11],[9,10,11,12,15,92],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_8 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_8 = true := by decide +kernel
def h46Block6_9 : List NodeSpec := [([0,1,2,3,4,9,12],[9,10,11,12,93],[0]),([0,1,2,3,4,9,13],[9,10,11,12,96],[0]),([0,1,2,3,4,9,18],[9,10,99],[0]),([0,1,2,3,4,9,19],[9,10,101],[0]),([0,1,2,3,4,9,20],[9,10,102],[0]),([0,1,2,3,4,9,21],[9,10,106],[0]),([0,1,2,3,4,9,26],[11,12,107],[0]),([0,1,2,3,4,9,27],[11,12,109],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_9 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_9 = true := by decide +kernel
def h46Block6_10 : List NodeSpec := [([0,1,2,3,4,9,28],[11,12,110],[0]),([0,1,2,3,4,9,29],[11,12,113],[0]),([0,1,2,4,35,41],[0,6,7,9,10,44,114,115,116],[0]),([0,1,2,3,4,35,42],[0,6,9,10,11,12],[0]),([0,1,2,3,4,71],[0,1,6,7,9,10,11,12,103,115],[0]),([0,1,2,4,10,35],[0,7,9,10,12,46,90,116],[0]),([0,1,2,3,4,96],[0,1,6,7,9,10,11,12],[0]),([0,1,2,4,36,40],[0,6,7,9,10,43,117,118,119],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_10 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_10 = true := by decide +kernel
def h46Block6_11 : List NodeSpec := [([0,1,2,3,4,106],[0,1,6,9,10,11,12,15,104,117],[0]),([0,1,2,3,4,37,40],[0,6,9,10,11,12],[0]),([0,1,2,3,37,43],[0,6,8,11,12,71,120,121,122],[0]),([0,1,2,3,4,78],[0,1,6,8,9,10,11,12,111,121],[0]),([0,1,2,3,10,37],[0,8,10,11,12,46,90,122],[0]),([0,1,2,3,4,101],[0,1,6,8,9,10,11,12],[0]),([0,1,2,3,38,42],[0,6,8,11,12,70,123,124,125],[0]),([0,1,2,3,4,110],[0,1,6,9,10,11,12,15,112,123],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_11 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_11 = true := by decide +kernel
def h46Block6_12 : List NodeSpec := [([0,1,2,3,4,108],[0,1,6,7,9,10,11,12,104,117],[0]),([0,1,2,4,10,40],[6,7,9,10,12,46,119,126],[0]),([0,1,2,3,4,67],[0,1,6,7,9,10,11,12,45],[0]),([0,1,2,3,4,68],[0,1,6,9,10,11,12,15,103,115],[0]),([0,1,2,3,4,112],[0,1,6,8,9,10,11,12,112,123],[0]),([0,1,2,3,10,42],[6,8,10,11,12,46,125,126],[0]),([0,1,2,3,4,74],[0,1,6,8,9,10,11,12,72],[0]),([0,1,2,3,4,75],[0,1,6,9,10,11,12,15,111,121],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_12 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_12 = true := by decide +kernel
def h46Block6_13 : List NodeSpec := [([0,1,2,3,4,81],[0,1,6,7,8,9,10,11,46],[0]),([0,1,2,3,4,88],[0,1,6,9,10,11,90],[0]),([0,1,2,3,4,92],[0,1,6,9,10,11,126],[0]),([0,1,2,10,11],[7,9,10,15,46,91,127],[0]),([0,1,2,3,4,170],[0,1,6,8,9,10,12,15,93,130,131],[0]),([0,1,2,3,4,171],[0,1,6,8,9,10,12,15,129,132,133],[0]),([0,1,2,3,4,178],[0,1,6,7,9,10,11,15,96,135,136],[0]),([0,1,2,3,4,179],[0,1,6,7,9,10,11,15,134,137,138],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_13 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_13 = true := by decide +kernel
def h46Nodes6 : List NodeSpec := h46Block6_0 ++ h46Block6_1 ++ h46Block6_2 ++ h46Block6_3 ++ h46Block6_4 ++ h46Block6_5 ++ h46Block6_6 ++ h46Block6_7 ++ h46Block6_8 ++ h46Block6_9 ++ h46Block6_10 ++ h46Block6_11 ++ h46Block6_12 ++ h46Block6_13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Check6 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Nodes6 = true := by
  unfold h46Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h46Test6_0,h46Test6_1⟩,h46Test6_2⟩,h46Test6_3⟩,h46Test6_4⟩,h46Test6_5⟩,h46Test6_6⟩,h46Test6_7⟩,h46Test6_8⟩,h46Test6_9⟩,h46Test6_10⟩,h46Test6_11⟩,h46Test6_12⟩,h46Test6_13⟩
def h46Bucket6 : BT (List (List Nat)) := buildBucketsBT h46W h46Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G 6 xs.toFinset) h46Bucket6 := buildBucketsBT_sound (by decide) h46Pairs h46WOk h46PoolsOk h46AutosOk h46Bucket5Ok h46Check6
def h46Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,6,7,8,9,10,11,12],[0]),([0,1,2,3,4,6],[0,1,6,7,8,9,10,11,12,19],[0]),([0,1,2,3,4,7],[0,1,5,6,7,8,9,10,11,12],[0]),([0,1,2,3,4,45],[0,1,6,7,8,9,10,11,12],[0]),([0,1,2,3,4,48],[0,1,6,7,8,9,11,12,25,26],[0]),([0,1,2,3,4,49],[0,1,6,7,8,9,10,11,12,15,36,37],[0]),([0,1,2,3,4,50],[0,1,6,8,9,10,11,12,50,51],[0]),([0,1,2,3,4,51],[0,1,6,7,8,9,10,11,12,15,52,53],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test7_0 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket6 7 h46Block7_0 = true := by decide +kernel
def h46Block7_1 : List NodeSpec := [([0,1,2,3,4,52],[0,1,6,7,9,10,11,54,55],[0]),([0,1,2,3,4,53],[0,1,6,7,8,9,10,11,12,15,63,64],[0]),([0,1,2,3,4,54],[0,1,6,7,9,10,11,12,76,77],[0]),([0,1,2,3,4,55],[0,1,6,7,8,9,10,11,12,15,78,79],[0]),([0,1,2,3,4,9],[0,1,6,9,10,11,12],[0]),([0,1,2,3,4,35],[0,1,6,7,9,10,11,12,15,114],[0]),([0,1,2,3,4,36],[0,1,6,7,9,11,12,15,117],[0]),([0,1,2,3,4,37],[0,1,6,8,9,10,11,12,15,120],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test7_1 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket6 7 h46Block7_1 = true := by decide +kernel
def h46Block7_2 : List NodeSpec := [([0,1,2,3,4,38],[0,1,6,8,9,10,11,15,123],[0]),([0,1,2,3,4,40],[0,1,6,7,9,10,11,12,15,118],[0]),([0,1,2,3,4,41],[0,1,6,7,9,11,12,15,115],[0]),([0,1,2,3,4,42],[0,1,6,8,9,10,11,12,15,124],[0]),([0,1,2,3,4,43],[0,1,6,8,9,10,11,15,121],[0]),([0,1,2,3,4,10],[0,1,6,7,8,9,10,11,90,126],[0]),([0,1,2,3,4,11],[0,1,6,7,9,10,11,12,15,92,128],[0]),([0,1,2,3,4,12],[0,1,6,7,8,9,10,11,12,15,93,129],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test7_2 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket6 7 h46Block7_2 = true := by decide +kernel
def h46Block7_3 : List NodeSpec := [([0,1,2,3,4,13],[0,1,6,7,9,10,11,15,96,134],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test7_3 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket6 7 h46Block7_3 = true := by decide +kernel
def h46Nodes7 : List NodeSpec := h46Block7_0 ++ h46Block7_1 ++ h46Block7_2 ++ h46Block7_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Check7 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket6 7 h46Nodes7 = true := by
  unfold h46Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h46Test7_0,h46Test7_1⟩,h46Test7_2⟩,h46Test7_3⟩
def h46Bucket7 : BT (List (List Nat)) := buildBucketsBT h46W h46Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G 7 xs.toFinset) h46Bucket7 := buildBucketsBT_sound (by decide) h46Pairs h46WOk h46PoolsOk h46AutosOk h46Bucket6Ok h46Check7
def h46Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test8_0 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket7 8 h46Block8_0 = true := by decide +kernel
def h46Nodes8 : List NodeSpec := h46Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Check8 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket7 8 h46Nodes8 = true := h46Test8_0
def h46Bucket8 : BT (List (List Nat)) := buildBucketsBT h46W h46Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G 8 xs.toFinset) h46Bucket8 := buildBucketsBT_sound (by decide) h46Pairs h46WOk h46PoolsOk h46AutosOk h46Bucket7Ok h46Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h46Bucket8Ok (by decide +kernel)
def h52R : List Nat := varsOf 29
def h52G : Nat := 0xfaaafaa0faaafaa0faaafaa0faaafaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h52Bound : Lower h52R h52G 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,1,17)]) (by decide +kernel) h32Bound
def h53R : List Nat := varsOf 45
def h53G : Nat := 0xfaaafaaafaa0faa0faaafaaafaa0faa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bound : Lower h53R h53G 5 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,1,33)]) (by decide +kernel) h32Bound
def h54R : List Nat := varsOf 29
def h54G : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h54Bound : Lower h54R h54G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h29Bound
def h55R : List Nat := varsOf 45
def h55G : Nat := 0xfffafffafaaafaaafffafffafaaafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bound : Lower h55R h55G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h40Bound
def h51R : List Nat := varsOf 61
def h51G : Nat := 0xfffafaaafaaafaa0fffafaaafaaafaa0
def h51Pos : List Nat := [9,12,5,5,17,12,9,17,33,52,52,56,25,21,56,41,37,17,52,56,12,12,17,5,28,44,28,44,33,28,25,44,41,9,33,33,49,17,21,33,37,28,28,17,44,44,33,49,12,12,12,12]
def h51Neg : List Nat := [8,8,1,4,20,4,1,1,1,20,36,40,24,20,24,40,36,24,48,48,1,0,16,0,20,36,24,40,36,16,1,32,1,0,32,48,48,48,1,40,1,8,4,0,8,4,0,1,24,36,40,20]
def h51Mask : Nat := fullMask 52
def h51Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc9ff50c3b1dd,0x8141401001c4),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf3740afb5262e,0xa240013012638),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xf3603ef38d863,0x512800c02d803),(0xffff0000ffff0000ffff0000ffff0000,0x8e70654e7e90,0x90038254e7210),(0xffffffff00000000ffffffff00000000,0xf19d9a0dcf00,0x600bc9a0d8c00)]
def h51Steps : List (Nat × Nat × Nat) := [(1,0,1),(2,0,1),(1,0,2),(0,1,2),(1,1,2),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(0,3,5),(2,3,5),(0,3,7),(2,3,7),(0,3,9),(1,3,9),(2,3,9),(3,3,9),(0,4,5),(2,4,5),(0,4,7),(2,4,7),(0,4,9),(1,4,9),(2,4,9),(3,4,9),(0,5,7),(1,5,7),(2,5,9),(2,1,2),(3,1,2),(1,1,3),(3,1,3),(1,1,4),(3,1,4),(3,1,7),(1,2,3),(3,2,3),(1,2,4),(3,2,4),(3,2,5),(3,2,7),(1,2,39),(1,1,44),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,0,9),(3,0,9),(0,3,31),(3,3,31),(0,4,31),(3,4,31),(2,5,45),(1,3,56),(2,3,56),(1,4,56),(2,4,56),(1,0,41),(1,1,41),(1,0,68),(3,0,68),(3,2,68),(3,1,69),(2,5,41),(1,0,43),(1,1,43),(1,0,75),(3,0,75),(3,2,75),(3,1,76),(2,5,43),(1,0,10),(1,1,81),(3,1,81),(1,2,81),(3,2,81),(0,3,81),(0,4,81),(1,1,10),(3,0,88),(1,2,88),(3,2,88),(1,2,10),(3,2,82),(2,5,10),(1,1,14),(1,0,15),(3,1,96),(1,2,96),(3,2,96),(1,1,22),(1,0,23),(3,1,101),(1,2,101),(3,2,101),(3,6,7),(1,2,36),(3,0,106),(3,1,106),(2,7,36),(1,2,38),(3,0,110),(3,1,110),(2,7,38),(3,0,92),(3,1,92),(3,1,84),(2,7,10),(1,2,16),(3,2,67),(1,2,24),(3,2,74),(0,2,95),(1,2,95),(2,2,95),(3,2,95),(0,1,118),(2,1,118),(3,1,118),(1,4,48),(2,4,48),(2,9,48),(1,3,87),(1,8,87),(3,4,49),(0,9,49),(3,9,49),(1,1,136),(1,2,136),(1,1,50),(1,2,139),(3,2,139),(1,2,50),(3,1,142),(2,9,50),(0,2,100),(1,2,100),(2,2,100),(3,2,100),(0,1,120),(2,1,120),(3,1,120),(2,3,52),(2,9,52),(1,8,86),(3,3,53),(0,9,53),(3,9,53),(1,1,157),(1,2,157),(1,1,54),(1,2,160),(3,2,160),(1,2,54),(3,1,163),(2,9,54),(2,31,56),(2,9,10),(2,3,167),(2,4,167),(1,1,12),(1,2,12),(1,9,12),(3,1,172),(3,2,172),(0,3,172),(2,9,12),(1,4,176),(1,1,13),(1,2,13),(1,9,13),(3,1,180),(3,2,180),(0,4,180),(2,9,13),(1,3,184),(3,18,19),(1,4,20),(1,3,169),(1,8,169),(3,26,27),(1,8,168),(0,35,42),(0,37,40)]
def h51W : BT Decor := buildWiresBT 8 h51Base h51Steps
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
def h51SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 16,4),some (subcubeFast 1 32,4),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 16 0,5),some (subcubeFast 32 0,5),some (subcubeFast 48 0,4)]
def h51Slices : BT (Option (Nat × Nat)) := btOfList 4 h51SliceList
def h51Specs : List PoolSpec := [(5,[]),(2,[]),(6,[(1,0,1)]),(0,[(1,0,1),(1,0,2)]),(1,[(1,0,1),(1,0,2)]),(5,[(1,0,2)]),(6,[]),(3,[]),(4,[]),(7,[]),(0,[]),(8,[]),(1,[]),(0,[(1,0,1)]),(1,[(1,0,1)]),(9,[]),(6,[(1,0,1),(0,3,31)]),(6,[(1,0,1),(0,4,31)]),(5,[(3,2,5)]),(6,[(2,0,1)]),(6,[(3,1,7)]),(0,[(1,0,2)]),(1,[(1,0,2)]),(5,[(1,0,2),(0,3,31)]),(5,[(1,0,2),(0,4,31)]),(5,[(0,0,3)]),(6,[(0,0,3)]),(5,[(0,0,3),(1,4,48)]),(0,[(1,4,48)]),(5,[(0,0,3),(2,4,48)]),(5,[(0,3,5),(1,2,95)]),(5,[(0,0,3),(2,9,48)]),(5,[(0,3,5)]),(6,[(0,3,7)]),(6,[(0,0,3),(1,4,48)]),(6,[(0,0,3),(2,4,48)]),(5,[(1,0,3)]),(6,[(1,0,3)]),(7,[(0,4,81)]),(5,[(1,0,3),(3,4,49)]),(5,[(1,0,3),(0,9,49)]),(5,[(1,0,3),(3,9,49)]),(1,[(1,0,3)]),(8,[(3,1,3)]),(8,[(3,2,3)]),(6,[(1,0,41)]),(2,[(0,3,4)]),(2,[(3,4,49)]),(6,[(1,0,3),(3,4,49)]),(7,[(3,4,49)]),(5,[(2,0,3)]),(6,[(2,0,3)]),(5,[(3,0,3)]),(6,[(3,0,3)]),(5,[(0,0,4)]),(6,[(0,0,4)]),(1,[(1,0,10)]),(5,[(0,0,4),(2,3,52)]),(5,[(0,4,5),(1,2,100)]),(5,[(0,0,4),(2,9,52)]),(5,[(0,4,5)]),(6,[(0,4,7)]),(6,[(0,0,4),(2,3,52)]),(5,[(1,0,4)]),(6,[(1,0,4)]),(8,[(0,3,81)]),(5,[(1,0,4),(3,3,53)]),(5,[(1,0,4),(0,9,53)]),(5,[(1,0,4),(3,9,53)]),(0,[(1,0,4)]),(7,[(3,1,4)]),(7,[(3,2,4)]),(6,[(1,0,43)]),(2,[(3,3,53)]),(6,[(1,0,4),(3,3,53)]),(8,[(3,3,53)]),(5,[(2,0,4)]),(6,[(2,0,4)]),(5,[(3,0,4)]),(6,[(3,0,4)]),(5,[(0,0,9)]),(5,[(0,0,9),(1,3,56)]),(5,[(0,0,9),(2,3,56)]),(5,[(0,0,9),(1,4,56)]),(5,[(0,0,9),(2,4,56)]),(5,[(1,0,2),(3,3,31)]),(5,[(1,0,2),(3,4,31)]),(5,[(2,5,9)]),(5,[(3,0,9)]),(6,[(3,0,9)]),(5,[(0,3,4)]),(5,[(0,3,4),(1,3,4)]),(5,[(1,3,4)]),(5,[(2,3,4)]),(5,[(2,3,4),(1,9,12)]),(5,[(2,3,4),(2,9,12)]),(5,[(3,3,4)]),(5,[(3,3,4),(1,9,13)]),(5,[(3,3,4),(2,9,13)]),(5,[(0,3,9)]),(5,[(0,3,9),(1,3,9)]),(5,[(1,3,9)]),(5,[(2,3,9)]),(6,[(1,1,41)]),(5,[(1,2,36)]),(5,[(2,3,9),(1,4,20)]),(5,[(3,3,9)]),(5,[(0,4,9)]),(5,[(0,4,9),(1,4,9)]),(5,[(1,4,9)]),(5,[(2,4,9)]),(6,[(1,1,43)]),(5,[(1,2,38)]),(5,[(3,4,9)]),(6,[(1,1,3)]),(5,[(3,2,3)]),(8,[(1,1,3)]),(6,[(3,1,3)]),(5,[(1,2,3)]),(8,[(1,2,3)]),(6,[(1,1,4)]),(5,[(3,2,4)]),(7,[(1,1,4)]),(6,[(3,1,4)]),(5,[(1,2,4)]),(7,[(1,2,4)]),(6,[(0,3,4)]),(6,[(0,3,4),(1,3,4)]),(6,[(1,3,4)]),(6,[(2,3,4)]),(6,[(2,3,4),(1,1,12)]),(8,[(1,1,12)]),(5,[(2,3,4),(1,2,12)]),(8,[(1,2,12)]),(6,[(3,3,4)]),(6,[(3,3,4),(1,1,13)]),(7,[(1,1,13)]),(5,[(3,3,4),(1,2,13)]),(7,[(1,2,13)])]
def h51Pools : BT (Option BoundPool) := buildPoolsBT 8 h51W h51R h51Slices h51Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice9 : Slice h51R h51G (subcubeFast 48 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice8 : Slice h51R h51G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h52Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice7 : Slice h51R h51G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h53Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice6 : Slice h51R h51G (subcubeFast 8 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice5 : Slice h51R h51G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice4 : Slice h51R h51G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice3 : Slice h51R h51G (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice2 : Slice h51R h51G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice1 : Slice h51R h51G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice0 : Slice h51R h51G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h55Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h51R h51G p.1 p.2) h51Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h51R h51G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h51Slice0) (forall_cons (fun _ h => by cases h; exact h51Slice1) (forall_cons (fun _ h => by cases h; exact h51Slice2) (forall_cons (fun _ h => by cases h; exact h51Slice3) (forall_cons (fun _ h => by cases h; exact h51Slice4) (forall_cons (fun _ h => by cases h; exact h51Slice5) (forall_cons (fun _ h => by cases h; exact h51Slice6) (forall_cons (fun _ h => by cases h; exact h51Slice7) (forall_cons (fun _ h => by cases h; exact h51Slice8) (forall_cons (fun _ h => by cases h; exact h51Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h51R h51G c) h51Pools := buildPoolsBT_sound h51SlicesOk
def h51Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G (3 - 1) xs.toFinset) h51Empty := trivial
def h51Block3_0 : List NodeSpec := [([3,9,30,87],[],[0]),([0,3,9,133],[],[0]),([3,4,30,136],[],[0]),([4,9,30,132],[],[0]),([4,9,30,86],[],[0]),([0,4,9,154],[],[0]),([3,4,30,157],[],[0]),([3,9,30,183],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test3_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 3 h51Block3_0 = true := by decide +kernel
def h51Block3_1 : List NodeSpec := [([3,9,30,177],[],[0]),([3,9,30,169],[],[0]),([0,3,9,189],[],[0]),([4,9,30,188],[],[0]),([4,9,30,175],[],[0]),([4,9,30,185],[],[0]),([4,9,30,168],[],[0]),([0,4,9,191],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test3_1 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 3 h51Block3_1 = true := by decide +kernel
def h51Nodes3 : List NodeSpec := h51Block3_0 ++ h51Block3_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check3 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 3 h51Nodes3 = true := by
  unfold h51Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h51Test3_0,h51Test3_1⟩
def h51Bucket3 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 3 xs.toFinset) h51Bucket3 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51EmptyOk h51Check3
def h51Block4_0 : List NodeSpec := [([0,2,4,39,58],[],[0]),([0,2,3,39,60],[],[0]),([0,1,4,44,58],[],[0]),([0,1,3,44,60],[],[0]),([0,1,2,58,61],[],[0]),([0,1,2,59,60],[],[0]),([0,1,2,59,61],[],[0]),([0,1,3,4,93],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test4_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket3 4 h51Block4_0 = true := by decide +kernel
def h51Block4_1 : List NodeSpec := [([0,2,3,4,116],[],[0]),([0,3,4,122,123],[30],[0]),([0,3,4,123,126],[30],[0]),([0,3,8,9,87],[],[0]),([2,3,4,30,97],[],[0]),([0,3,4,8,136],[41],[0]),([1,2,3,30,87],[],[0]),([0,1,2,3,133],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test4_1 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket3 4 h51Block4_1 = true := by decide +kernel
def h51Block4_2 : List NodeSpec := [([0,4,8,9,132],[],[0]),([0,3,4,145,146],[58],[0]),([0,3,4,146,149],[58],[0]),([1,2,4,30,132],[],[0]),([0,4,8,9,86],[],[0]),([2,3,4,30,102],[],[0]),([0,3,4,8,157],[68],[0]),([1,2,4,30,86],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test4_2 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket3 4 h51Block4_2 = true := by decide +kernel
def h51Block4_3 : List NodeSpec := [([0,1,2,4,154],[],[0]),([1,2,3,4,166],[],[0]),([0,1,2,11,167],[15],[0]),([0,1,2,4,186],[],[0]),([0,1,2,21,187],[15],[0]),([0,3,8,9,183],[],[0]),([0,3,8,9,177],[],[0]),([0,3,8,9,169],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test4_3 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket3 4 h51Block4_3 = true := by decide +kernel
def h51Block4_4 : List NodeSpec := [([0,1,2,3,190],[],[0]),([0,4,8,9,188],[],[0]),([0,1,2,29,188],[15],[0]),([0,4,8,9,175],[],[0]),([0,4,8,9,185],[],[0]),([0,4,8,9,168],[],[0]),([0,2,10,35,112],[],[0]),([0,1,10,42,71],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test4_4 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket3 4 h51Block4_4 = true := by decide +kernel
def h51Block4_5 : List NodeSpec := [([0,2,10,37,108],[],[0]),([0,1,10,40,78],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test4_5 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket3 4 h51Block4_5 = true := by decide +kernel
def h51Nodes4 : List NodeSpec := h51Block4_0 ++ h51Block4_1 ++ h51Block4_2 ++ h51Block4_3 ++ h51Block4_4 ++ h51Block4_5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check4 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket3 4 h51Nodes4 = true := by
  unfold h51Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h51Test4_0,h51Test4_1⟩,h51Test4_2⟩,h51Test4_3⟩,h51Test4_4⟩,h51Test4_5⟩
def h51Bucket4 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 4 xs.toFinset) h51Bucket4 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51Bucket3Ok h51Check4
def h51Block5_0 : List NodeSpec := [([3,4,5,7,9],[0,1,2,3,4,5,6],[0]),([2,3,4,5,7,39],[1],[0]),([1,3,4,5,7,44],[1],[0]),([0,3,4,5,7,9],[0,1,6],[0]),([0,2,3,4,5,39],[0],[0]),([0,1,3,4,7,44],[0],[0]),([0,1,2,3,4,31],[9,10,11,12],[0]),([1,2,3,4,5,62],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_0 = true := by decide +kernel
def h51Block5_1 : List NodeSpec := [([2,3,4,5,9,56],[0],[0]),([2,3,4,5,9,57],[0],[0]),([0,3,4,5,9,44],[0,6],[0]),([0,2,3,4,5,68],[1],[0]),([0,1,3,4,41,44],[10],[0]),([0,1,2,3,4,69],[10],[0]),([0,1,2,3,4,73],[6],[0]),([0,2,3,4,5,75],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_1 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_1 = true := by decide +kernel
def h51Block5_2 : List NodeSpec := [([0,1,3,4,43,44],[12],[0]),([0,1,2,3,4,76],[12],[0]),([0,1,2,3,4,80],[6],[0]),([0,1,2,3,4,57],[],[0]),([1,2,3,4,31,57],[0],[0]),([0,1,2,3,4,39],[],[0]),([0,2,3,4,31,39],[0],[0]),([0,1,2,3,4,44],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_2 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_2 = true := by decide +kernel
def h51Block5_3 : List NodeSpec := [([0,1,3,4,31,44],[0],[0]),([0,1,2,4,31,58],[10,15],[0]),([0,1,2,4,31,59],[9],[0]),([0,1,2,3,31,60],[12,15],[0]),([0,1,2,3,31,61],[11],[0]),([1,2,3,4,5,57],[0],[0]),([0,1,2,4,5,58],[16],[0]),([0,1,2,3,5,60],[17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_3 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_3 = true := by decide +kernel
def h51Block5_4 : List NodeSpec := [([1,2,3,4,5,81],[0,7,8],[0]),([0,2,3,4,5,88],[1,9,11],[0]),([0,1,2,3,4,82],[6,9,10],[0]),([0,1,2,3,4,94],[],[0]),([1,2,3,4,5,96],[0],[0]),([1,2,3,4,5,101],[0],[0]),([1,2,3,4,7,105],[],[0]),([1,3,4,7,9,56],[6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_4 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_4 = true := by decide +kernel
def h51Block5_5 : List NodeSpec := [([1,3,4,7,9,57],[6],[0]),([0,3,4,7,9,39],[0,6],[0]),([0,2,3,4,36,39],[10],[0]),([0,1,3,4,7,106],[1],[0]),([0,1,2,3,4,98],[10],[0]),([0,1,2,3,4,109],[0],[0]),([0,2,3,4,38,39],[12],[0]),([0,1,3,4,7,110],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_5 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_5 = true := by decide +kernel
def h51Block5_6 : List NodeSpec := [([0,1,2,3,4,103],[12],[0]),([0,1,2,3,4,113],[0],[0]),([1,2,3,4,7,57],[0],[0]),([0,1,2,4,7,58],[23],[0]),([0,1,2,3,7,60],[24],[0]),([1,2,3,4,7,81],[6,7,8],[0]),([0,1,3,4,7,92],[1,9,11],[0]),([0,1,2,3,4,84],[0,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_6 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_6 = true := by decide +kernel
def h51Block5_7 : List NodeSpec := [([0,1,2,3,4,117],[],[0]),([1,2,3,4,7,67],[0],[0]),([1,2,3,4,7,74],[0],[0]),([0,2,3,4,9,95],[6,9,13],[0]),([0,1,3,4,9,118],[0,9,21],[0]),([0,1,2,3,9,129],[9,27,28],[0]),([0,1,2,3,9,130],[29],[0]),([0,1,2,3,4,123],[9,30],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_7 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_7 = true := by decide +kernel
def h51Block5_8 : List NodeSpec := [([0,1,2,3,4,131],[0,6,31],[0]),([0,2,3,4,95,122],[1,8,9,15,32],[0]),([0,2,3,4,95,123],[9,13],[0]),([0,2,3,4,95,124],[],[0]),([0,2,3,4,95,125],[],[0]),([0,2,3,4,34,95],[1],[0]),([0,1,2,3,4,125],[1],[0]),([0,1,3,4,118,126],[1,8,9,15,33],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_8 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_8 = true := by decide +kernel
def h51Block5_9 : List NodeSpec := [([0,1,3,4,118,123],[9,21,30],[0]),([0,1,3,4,118,127],[],[0]),([0,1,3,4,118,128],[],[0]),([0,1,3,4,33,118],[1],[0]),([0,1,2,3,4,128],[1],[0]),([0,1,2,3,9,87],[10,38],[0]),([0,1,2,3,9,134],[39],[0]),([0,1,2,3,4,135],[1,40],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_9 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_9 = true := by decide +kernel
def h51Block5_10 : List NodeSpec := [([0,1,2,3,4,136],[41],[0]),([0,1,2,4,49,106],[15],[0]),([0,1,2,4,36,119],[],[0]),([0,2,3,4,8,97],[10],[0]),([0,2,3,4,34,97],[10],[0]),([0,1,2,4,41,97],[],[0]),([0,1,2,3,4,138],[10],[0]),([0,1,2,4,49,68],[15],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_10 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_10 = true := by decide +kernel
def h51Block5_11 : List NodeSpec := [([0,1,3,4,33,119],[10],[0]),([0,1,2,3,4,137],[10],[0]),([0,1,2,3,8,87],[10,11,38,46],[0]),([0,1,2,3,33,87],[10,38],[0]),([0,1,2,3,34,87],[10,38],[0]),([0,2,3,4,9,139],[6],[0]),([0,1,3,4,9,142],[0],[0]),([0,1,2,3,4,140],[10,11,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_11 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_11 = true := by decide +kernel
def h51Block5_12 : List NodeSpec := [([0,1,2,3,4,144],[],[0]),([0,1,2,3,4,141],[],[0]),([0,1,2,3,4,143],[],[0]),([0,2,3,4,9,100],[6,11,14],[0]),([0,1,3,4,9,120],[0,11,22],[0]),([0,1,2,4,9,132],[11,56],[0]),([0,1,2,4,9,152],[57],[0]),([0,1,2,3,4,146],[11,58],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_12 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_12 = true := by decide +kernel
def h51Block5_13 : List NodeSpec := [([0,1,2,3,4,153],[0,6,59],[0]),([0,2,3,4,100,145],[1,7,11,15,60],[0]),([0,2,3,4,100,146],[11,14],[0]),([0,2,3,4,100,147],[],[0]),([0,2,3,4,100,148],[],[0]),([0,2,3,4,34,100],[1],[0]),([0,1,2,3,4,148],[1],[0]),([0,1,3,4,120,149],[1,7,11,15,61],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_13 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_13 = true := by decide +kernel
def h51Block5_14 : List NodeSpec := [([0,1,3,4,120,146],[11,22,58],[0]),([0,1,3,4,120,150],[],[0]),([0,1,3,4,120,151],[],[0]),([0,1,3,4,33,120],[1],[0]),([0,1,2,3,4,151],[1],[0]),([0,1,2,4,8,132],[1,10,11,15,56],[0]),([0,1,2,4,33,132],[],[0]),([0,1,2,4,34,132],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_14 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_14 = true := by decide +kernel
def h51Block5_15 : List NodeSpec := [([0,1,2,4,9,86],[12,65],[0]),([0,1,2,4,9,155],[66],[0]),([0,1,2,3,4,156],[1,67],[0]),([0,1,2,3,4,157],[68],[0]),([0,1,2,3,53,110],[15],[0]),([0,1,2,3,38,121],[],[0]),([0,2,3,4,8,102],[12],[0]),([0,2,3,4,34,102],[12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_15 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_15 = true := by decide +kernel
def h51Block5_16 : List NodeSpec := [([0,1,2,3,43,102],[],[0]),([0,1,2,3,4,159],[12],[0]),([0,1,2,3,53,75],[15],[0]),([0,1,3,4,33,121],[12],[0]),([0,1,2,3,4,158],[12],[0]),([0,1,2,4,8,86],[9,12,46,65],[0]),([0,1,2,4,33,86],[12,65],[0]),([0,1,2,4,34,86],[12,65],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_16 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_16 = true := by decide +kernel
def h51Block5_17 : List NodeSpec := [([0,2,3,4,9,160],[6],[0]),([0,1,3,4,9,163],[0],[0]),([0,1,2,3,4,161],[9,10,12],[0]),([0,1,2,3,4,165],[],[0]),([0,1,2,3,4,162],[],[0]),([0,1,2,3,4,164],[],[0]),([1,2,3,4,31,56],[],[0]),([0,1,2,4,9,63],[81],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_17 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_17 = true := by decide +kernel
def h51Block5_18 : List NodeSpec := [([0,1,2,4,9,64],[82],[0]),([0,1,2,3,9,65],[83],[0]),([0,1,2,3,9,66],[84],[0]),([0,2,3,4,9,39],[0],[0]),([0,1,3,4,9,44],[0],[0]),([0,1,2,4,9,58],[23],[0]),([0,1,2,4,9,59],[85],[0]),([0,1,2,3,9,60],[24],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_18 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_18 = true := by decide +kernel
def h51Block5_19 : List NodeSpec := [([0,1,2,3,9,61],[86],[0]),([1,2,3,4,32,57],[],[0]),([0,2,3,4,9,47],[0],[0]),([0,1,3,4,9,46],[0],[0]),([0,2,3,4,9,88],[6],[0]),([0,1,3,4,9,92],[0],[0]),([0,1,2,9,10,11],[9,10,15,91],[0]),([0,1,2,3,4,90],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_19 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_19 = true := by decide +kernel
def h51Block5_20 : List NodeSpec := [([0,1,2,3,4,167],[9,10],[0]),([0,1,2,3,4,172],[9,94],[0]),([0,1,2,3,4,176],[10,95],[0]),([0,1,2,3,4,180],[9,97],[0]),([0,1,2,3,4,184],[10,98],[0]),([0,1,2,4,18,19],[100],[0]),([0,2,3,4,9,108],[0],[0]),([0,1,3,4,9,71],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_20 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_20 = true := by decide +kernel
def h51Block5_21 : List NodeSpec := [([0,2,3,4,9,68],[0,103],[0]),([0,1,3,4,9,106],[0,104],[0]),([0,1,2,4,20,21],[15],[0]),([0,1,2,3,9,187],[9,105],[0]),([0,1,2,3,9,183],[],[0]),([0,1,2,3,9,177],[],[0]),([0,1,2,3,9,169],[10,15],[0]),([0,1,2,3,26,27],[108],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_21 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_21 = true := by decide +kernel
def h51Block5_22 : List NodeSpec := [([0,2,3,4,9,112],[0],[0]),([0,1,3,4,9,78],[0],[0]),([0,2,3,4,9,75],[0,111],[0]),([0,1,3,4,9,110],[0,112],[0]),([0,1,2,4,9,188],[11],[0]),([0,1,2,4,9,175],[],[0]),([0,1,2,3,28,29],[15],[0]),([0,1,2,4,9,185],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_22 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_22 = true := by decide +kernel
def h51Block5_23 : List NodeSpec := [([0,1,2,4,9,168],[12,15],[0]),([0,2,3,4,35,112],[9],[0]),([0,1,3,4,42,71],[10],[0]),([0,1,2,10,35,42],[10],[0]),([0,1,2,3,4,192],[],[0]),([0,1,2,4,10,71],[12],[0]),([0,1,2,4,35,92],[0],[0]),([0,1,2,3,4,99],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_23 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_23 = true := by decide +kernel
def h51Block5_24 : List NodeSpec := [([0,1,2,3,4,107],[],[0]),([0,2,3,4,37,108],[10],[0]),([0,1,3,4,40,78],[9],[0]),([0,1,2,10,37,40],[10],[0]),([0,1,2,3,4,193],[],[0]),([0,1,2,3,10,78],[10],[0]),([0,1,2,3,37,92],[0],[0]),([0,1,2,3,4,104],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_24 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_24 = true := by decide +kernel
def h51Block5_25 : List NodeSpec := [([0,1,2,3,4,111],[],[0]),([0,1,2,4,10,108],[12],[0]),([0,1,2,4,40,88],[6],[0]),([0,1,2,3,4,72],[],[0]),([0,1,2,3,4,70],[],[0]),([0,1,2,3,10,112],[10],[0]),([0,1,2,3,42,88],[6],[0]),([0,1,2,3,4,79],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_25 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_25 = true := by decide +kernel
def h51Block5_26 : List NodeSpec := [([0,1,2,3,4,77],[],[0]),([0,1,2,3,4,83],[],[0]),([0,1,2,3,4,85],[],[0]),([0,1,2,3,4,89],[],[0]),([0,1,2,3,4,91],[],[0]),([0,1,2,3,4,114],[],[0]),([0,1,2,3,4,115],[],[0]),([0,1,2,3,4,174],[9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_26 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_26 = true := by decide +kernel
def h51Block5_27 : List NodeSpec := [([0,1,2,3,4,173],[9],[0]),([0,1,2,3,4,182],[10],[0]),([0,1,2,3,4,181],[10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_27 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_27 = true := by decide +kernel
def h51Nodes5 : List NodeSpec := h51Block5_0 ++ h51Block5_1 ++ h51Block5_2 ++ h51Block5_3 ++ h51Block5_4 ++ h51Block5_5 ++ h51Block5_6 ++ h51Block5_7 ++ h51Block5_8 ++ h51Block5_9 ++ h51Block5_10 ++ h51Block5_11 ++ h51Block5_12 ++ h51Block5_13 ++ h51Block5_14 ++ h51Block5_15 ++ h51Block5_16 ++ h51Block5_17 ++ h51Block5_18 ++ h51Block5_19 ++ h51Block5_20 ++ h51Block5_21 ++ h51Block5_22 ++ h51Block5_23 ++ h51Block5_24 ++ h51Block5_25 ++ h51Block5_26 ++ h51Block5_27
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check5 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Nodes5 = true := by
  unfold h51Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h51Test5_0,h51Test5_1⟩,h51Test5_2⟩,h51Test5_3⟩,h51Test5_4⟩,h51Test5_5⟩,h51Test5_6⟩,h51Test5_7⟩,h51Test5_8⟩,h51Test5_9⟩,h51Test5_10⟩,h51Test5_11⟩,h51Test5_12⟩,h51Test5_13⟩,h51Test5_14⟩,h51Test5_15⟩,h51Test5_16⟩,h51Test5_17⟩,h51Test5_18⟩,h51Test5_19⟩,h51Test5_20⟩,h51Test5_21⟩,h51Test5_22⟩,h51Test5_23⟩,h51Test5_24⟩,h51Test5_25⟩,h51Test5_26⟩,h51Test5_27⟩
def h51Bucket5 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 5 xs.toFinset) h51Bucket5 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51Bucket4Ok h51Check5
def h51Block6_0 : List NodeSpec := [([1,2,3,4,5,7],[0,1,2,5,6,7,8],[0]),([0,1,2,3,4,5,7],[0,1,2,5,6],[0]),([1,2,3,4,5,45],[0,1,2,6,7,8],[0]),([0,2,3,4,5,9],[0,1,2,6,13,14],[0]),([0,1,2,3,4,5,41],[0,6,7,9,10],[0]),([0,1,2,3,4,5,43],[0,6,8,11,12],[0]),([0,1,2,3,4,31],[9,10,11,12],[0]),([0,1,2,3,4,5,31],[2,6,7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_0 = true := by decide +kernel
def h51Block6_1 : List NodeSpec := [([0,1,2,3,4,44],[0,1,2,6,9,10,11,12,18],[0]),([0,1,2,3,4,5,44],[0,1,2,6],[0]),([0,1,2,3,4,5,10],[0,1,7,8,9,10,11,12],[0]),([0,1,2,3,4,5,14],[0,1,7,9,10],[0]),([0,1,2,3,4,5,15],[7,9,10],[0]),([0,1,2,3,4,5,22],[0,1,8,11,12],[0]),([0,1,2,3,4,5,23],[8,11,12],[0]),([1,2,3,4,6,7],[0,1,5,6,7,8,19],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_1 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_1 = true := by decide +kernel
def h51Block6_2 : List NodeSpec := [([0,1,2,3,4,46],[0,1,5,6,7,8,9,10,11,12,20],[0]),([0,1,3,4,7,9],[0,1,5,6,21,22],[0]),([0,1,2,3,4,7,36],[0,6,7,9,10],[0]),([0,1,2,3,4,7,38],[0,6,8,11,12],[0]),([0,1,2,3,4,7,31],[0,5,7,8],[0]),([0,1,2,3,4,39],[0,1,5,6,9,10,11,12,20],[0]),([0,1,2,3,4,7,39],[0,1,5,6],[0]),([0,1,2,3,4,7,10],[1,6,7,8,9,10,11,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_2 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_2 = true := by decide +kernel
def h51Block6_3 : List NodeSpec := [([0,1,2,3,4,7,16],[1,6,7,9,10],[0]),([0,1,2,3,4,7,17],[7,9,10],[0]),([0,1,2,3,4,7,24],[1,6,8,11,12],[0]),([0,1,2,3,4,7,25],[8,11,12],[0]),([0,1,2,3,4,47],[0,1,2,6,7,8,9,10,11,12,18],[0]),([0,1,2,3,4,9,48],[0,1,6,9,10,25],[0]),([0,2,3,4,95],[1,7,8,9,32],[0]),([0,1,2,3,4,95],[0,1,6,7,8,9,11,12,32],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_3 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_3 = true := by decide +kernel
def h51Block6_4 : List NodeSpec := [([0,1,3,4,118],[1,7,8,9,33],[0]),([0,1,2,3,4,118],[0,1,6,7,8,9,11,12,33],[0]),([0,1,2,3,129],[1,9,12,27,34],[0]),([0,1,2,3,130],[1,9,11,29,35],[0]),([0,1,2,3,4,9,49],[9,10,36],[0]),([0,1,2,4,36,49],[0,1,9,10,15,36,42,43],[0]),([0,1,2,3,4,97],[0,1,6,7,9,10,11,12],[0]),([0,1,2,4,41,49],[1,6,9,10,15,37,42,44],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_4 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_4 = true := by decide +kernel
def h51Block6_5 : List NodeSpec := [([0,1,2,3,4,119],[0,1,6,7,9,10,11,12,45],[0]),([0,1,2,3,87],[7,10,11,15,38,46],[0]),([0,1,2,3,134],[7,10,12,39,47,48,49],[0]),([0,1,2,3,4,9,50],[0,1,6,9,10,50],[0]),([0,1,2,3,4,139],[0,1,6,8,10,11,12,50],[0]),([0,1,2,3,4,142],[0,1,6,8,10,11,12,51],[0]),([0,1,2,3,4,9,51],[7,9,10,52],[0]),([0,1,2,3,4,9,52],[0,1,6,11,12,54],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_5 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_5 = true := by decide +kernel
def h51Block6_6 : List NodeSpec := [([0,2,3,4,100],[1,7,11,60],[0]),([0,1,2,3,4,100],[0,1,6,7,9,10,11,60],[0]),([0,1,3,4,120],[1,7,11,61],[0]),([0,1,2,3,4,120],[0,1,6,7,9,10,11,61],[0]),([0,1,2,4,132],[1,10,11],[0]),([0,1,2,4,152],[1,9,11,57,62],[0]),([0,1,2,3,4,9,53],[11,12,63],[0]),([0,1,2,3,38,53],[0,1,11,12,15,63,69,70],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_6 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_6 = true := by decide +kernel
def h51Block6_7 : List NodeSpec := [([0,1,2,3,4,102],[0,1,6,8,9,10,11,12],[0]),([0,1,2,3,43,53],[1,6,11,12,15,64,69,71],[0]),([0,1,2,3,4,121],[0,1,6,8,9,10,11,12,72],[0]),([0,1,2,4,86],[8,9,12,15,46,65],[0]),([0,1,2,4,155],[7,10,12,66,73,74,75],[0]),([0,1,2,3,4,9,54],[0,1,6,11,12,76],[0]),([0,1,2,3,4,160],[0,1,6,7,9,10,12,76],[0]),([0,1,2,3,4,163],[0,1,6,7,9,10,12,77],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_7 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_7 = true := by decide +kernel
def h51Block6_8 : List NodeSpec := [([0,1,2,3,4,9,55],[8,11,12,78],[0]),([0,1,2,3,4,9,56],[0,1,6,80],[0]),([0,1,2,3,4,9,31],[1,5],[0]),([0,1,2,3,4,9,32],[1,87],[0]),([0,1,2,3,4,57],[0,6,9,10,11,12,88,89],[0]),([0,1,2,3,4,9,57],[0,1,6,88],[0]),([0,1,2,3,4,9,10],[0,6,9,10,11,12,90],[0]),([0,1,2,3,4,9,11],[9,10,11,12,15,92],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_8 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_8 = true := by decide +kernel
def h51Block6_9 : List NodeSpec := [([0,1,2,3,4,9,12],[9,10,11,12,93],[0]),([0,1,2,3,4,9,13],[9,10,11,12,96],[0]),([0,1,2,3,4,9,18],[9,10,99],[0]),([0,1,2,3,4,9,19],[9,10,101],[0]),([0,1,2,3,4,9,20],[9,10,102],[0]),([0,1,2,3,4,9,21],[9,10,106],[0]),([0,1,2,3,4,9,26],[11,12,107],[0]),([0,1,2,3,4,9,27],[11,12,109],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_9 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_9 = true := by decide +kernel
def h51Block6_10 : List NodeSpec := [([0,1,2,3,4,9,28],[11,12,110],[0]),([0,1,2,3,4,9,29],[11,12,113],[0]),([0,1,2,4,35,41],[0,6,7,9,10,44,114,115,116],[0]),([0,1,2,3,4,35,42],[0,6,9,10,11,12],[0]),([0,1,2,3,4,71],[0,1,6,7,9,10,11,12,103,115],[0]),([0,1,2,4,10,35],[0,7,9,10,12,46,90,116],[0]),([0,1,2,3,4,96],[0,1,6,7,9,10,11,12],[0]),([0,1,2,4,36,40],[0,6,7,9,10,43,117,118,119],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_10 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_10 = true := by decide +kernel
def h51Block6_11 : List NodeSpec := [([0,1,2,3,4,106],[0,1,6,9,10,11,12,15,104,117],[0]),([0,1,2,3,4,37,40],[0,6,9,10,11,12],[0]),([0,1,2,3,37,43],[0,6,8,11,12,71,120,121,122],[0]),([0,1,2,3,4,78],[0,1,6,8,9,10,11,12,111,121],[0]),([0,1,2,3,10,37],[0,8,10,11,12,46,90,122],[0]),([0,1,2,3,4,101],[0,1,6,8,9,10,11,12],[0]),([0,1,2,3,38,42],[0,6,8,11,12,70,123,124,125],[0]),([0,1,2,3,4,110],[0,1,6,9,10,11,12,15,112,123],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_11 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_11 = true := by decide +kernel
def h51Block6_12 : List NodeSpec := [([0,1,2,3,4,108],[0,1,6,7,9,10,11,12,104,117],[0]),([0,1,2,4,10,40],[6,7,9,10,12,46,119,126],[0]),([0,1,2,3,4,67],[0,1,6,7,9,10,11,12,45],[0]),([0,1,2,3,4,68],[0,1,6,9,10,11,12,15,103,115],[0]),([0,1,2,3,4,112],[0,1,6,8,9,10,11,12,112,123],[0]),([0,1,2,3,10,42],[6,8,10,11,12,46,125,126],[0]),([0,1,2,3,4,74],[0,1,6,8,9,10,11,12,72],[0]),([0,1,2,3,4,75],[0,1,6,9,10,11,12,15,111,121],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_12 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_12 = true := by decide +kernel
def h51Block6_13 : List NodeSpec := [([0,1,2,3,4,81],[0,1,6,7,8,9,10,11,46],[0]),([0,1,2,3,4,88],[0,1,6,9,10,11,90],[0]),([0,1,2,3,4,92],[0,1,6,9,10,11,126],[0]),([0,1,2,10,11],[7,9,10,15,46,91,127],[0]),([0,1,2,3,4,170],[0,1,6,8,9,10,12,15,93,130,131],[0]),([0,1,2,3,4,171],[0,1,6,8,9,10,12,15,129,132,133],[0]),([0,1,2,3,4,178],[0,1,6,7,9,10,11,15,96,135,136],[0]),([0,1,2,3,4,179],[0,1,6,7,9,10,11,15,134,137,138],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_13 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_13 = true := by decide +kernel
def h51Nodes6 : List NodeSpec := h51Block6_0 ++ h51Block6_1 ++ h51Block6_2 ++ h51Block6_3 ++ h51Block6_4 ++ h51Block6_5 ++ h51Block6_6 ++ h51Block6_7 ++ h51Block6_8 ++ h51Block6_9 ++ h51Block6_10 ++ h51Block6_11 ++ h51Block6_12 ++ h51Block6_13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check6 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Nodes6 = true := by
  unfold h51Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h51Test6_0,h51Test6_1⟩,h51Test6_2⟩,h51Test6_3⟩,h51Test6_4⟩,h51Test6_5⟩,h51Test6_6⟩,h51Test6_7⟩,h51Test6_8⟩,h51Test6_9⟩,h51Test6_10⟩,h51Test6_11⟩,h51Test6_12⟩,h51Test6_13⟩
def h51Bucket6 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 6 xs.toFinset) h51Bucket6 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51Bucket5Ok h51Check6
def h51Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,6,7,8,9,10,11,12],[0]),([0,1,2,3,4,6],[0,1,6,7,8,9,10,11,12,19],[0]),([0,1,2,3,4,7],[0,1,5,6,7,8,9,10,11,12],[0]),([0,1,2,3,4,45],[0,1,6,7,8,9,10,11,12],[0]),([0,1,2,3,4,48],[0,1,6,7,8,9,11,12,25,26],[0]),([0,1,2,3,4,49],[0,1,6,7,8,9,10,11,12,15,36,37],[0]),([0,1,2,3,4,50],[0,1,6,8,9,10,11,12,50,51],[0]),([0,1,2,3,4,51],[0,1,6,7,8,9,10,11,12,15,52,53],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test7_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket6 7 h51Block7_0 = true := by decide +kernel
def h51Block7_1 : List NodeSpec := [([0,1,2,3,4,52],[0,1,6,7,9,10,11,54,55],[0]),([0,1,2,3,4,53],[0,1,6,7,8,9,10,11,12,15,63,64],[0]),([0,1,2,3,4,54],[0,1,6,7,9,10,11,12,76,77],[0]),([0,1,2,3,4,55],[0,1,6,7,8,9,10,11,12,15,78,79],[0]),([0,1,2,3,4,9],[0,1,6,9,10,11,12],[0]),([0,1,2,3,4,35],[0,1,6,7,9,10,11,12,15,114],[0]),([0,1,2,3,4,36],[0,1,6,7,9,11,12,15,117],[0]),([0,1,2,3,4,37],[0,1,6,8,9,10,11,12,15,120],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test7_1 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket6 7 h51Block7_1 = true := by decide +kernel
def h51Block7_2 : List NodeSpec := [([0,1,2,3,4,38],[0,1,6,8,9,10,11,15,123],[0]),([0,1,2,3,4,40],[0,1,6,7,9,10,11,12,15,118],[0]),([0,1,2,3,4,41],[0,1,6,7,9,11,12,15,115],[0]),([0,1,2,3,4,42],[0,1,6,8,9,10,11,12,15,124],[0]),([0,1,2,3,4,43],[0,1,6,8,9,10,11,15,121],[0]),([0,1,2,3,4,10],[0,1,6,7,8,9,10,11,90,126],[0]),([0,1,2,3,4,11],[0,1,6,7,9,10,11,12,15,92,128],[0]),([0,1,2,3,4,12],[0,1,6,7,8,9,10,11,12,15,93,129],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test7_2 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket6 7 h51Block7_2 = true := by decide +kernel
def h51Block7_3 : List NodeSpec := [([0,1,2,3,4,13],[0,1,6,7,9,10,11,15,96,134],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test7_3 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket6 7 h51Block7_3 = true := by decide +kernel
def h51Nodes7 : List NodeSpec := h51Block7_0 ++ h51Block7_1 ++ h51Block7_2 ++ h51Block7_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check7 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket6 7 h51Nodes7 = true := by
  unfold h51Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h51Test7_0,h51Test7_1⟩,h51Test7_2⟩,h51Test7_3⟩
def h51Bucket7 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 7 xs.toFinset) h51Bucket7 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51Bucket6Ok h51Check7
def h51Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test8_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket7 8 h51Block8_0 = true := by decide +kernel
def h51Nodes8 : List NodeSpec := h51Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check8 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket7 8 h51Nodes8 = true := h51Test8_0
def h51Bucket8 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 8 xs.toFinset) h51Bucket8 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51Bucket7Ok h51Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bound : Lower h51R h51G 9 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h51Bucket8Ok (by decide +kernel)
def h57R : List Nat := varsOf 30
def h57G : Nat := 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Bound : Lower h57R h57G 7 := carry_of (swaps := [(3,4),(4,5)]) (roots2 := Cofactor12080.R_23) (T2 := Cofactor12080.G_23) (by decide +kernel) Cofactor12080.low_23
def h56R : List Nat := varsOf 62
def h56G : Nat := 0xfffcfcfcfffcfcc0fffcfcfcfffcfcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h56Bound : Lower h56R h56G 8 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,2,34)]) (by decide +kernel) h57Bound
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfee8e8a8eaa8e880fee8e8a8eaa8e880
def h0Pos : List Nat := [13,14,21,14,25,7,14,21,11,54,19,54,35,37,7,13,58,13,54,21,37,7,58,25,13,30,45,25,58,7,11,19,35,58,14,30,23,60,21,25,46,11,19,19,35,60,60,11,54,7,14,19,43,57,27,29,11,7,37,19,57,30]
def h0Neg : List Nat := [12,12,22,10,24,3,6,20,3,38,3,22,3,36,6,9,56,5,52,5,5,5,50,17,1,26,41,9,26,4,9,17,33,42,26,22,22,44,17,1,38,10,22,18,34,56,52,1,50,2,28,26,42,49,26,28,2,22,33,2,41,28]
def h0Mask : Nat := fullMask 62
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffa9ed1edbaf5b5,0x142080c1cdba9520),(0xcccccccccccccccccccccccccccccccc,0x2b5f9f1ff2655f6a,0xb5b1f1e12405f6c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x2687617c273eeaef,0x22844538203e6ac7),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x31f4e3ae5fc3815b,0x30dc22265e01801b),(0xffff0000ffff0000ffff0000ffff0000,0x38e96cfa9acd0e94,0x22ed6c5c92c50894),(0xffffffff00000000ffffffff00000000,0x1431712314553a00,0x1431712304452200)]
def h0Steps : List (Nat × Nat × Nat) := [(0,0,1),(3,0,1),(0,0,2),(3,0,2),(1,0,3),(2,0,3),(0,0,4),(3,0,4),(0,1,2),(2,1,3),(0,1,4),(2,2,3),(0,2,4),(3,3,4),(1,7,18),(1,7,19),(1,9,16),(1,9,19),(2,10,14),(2,10,16),(2,10,18),(1,11,14),(1,12,14),(1,3,28),(3,3,28),(1,14,19)]
def h0W : BT Decor := buildWiresBT 5 h0Base h0Steps
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
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,8),some (subcubeFast 0 2,9),some (subcubeFast 0 4,9),some (subcubeFast 0 8,8),some (subcubeFast 0 16,9),some (subcubeFast 0 32,10),some (subcubeFast 1 0,8),some (subcubeFast 1 2,5),some (subcubeFast 1 4,5),some (subcubeFast 1 8,5),some (subcubeFast 1 16,7),some (subcubeFast 2 0,8),some (subcubeFast 2 1,5),some (subcubeFast 2 4,6),some (subcubeFast 2 8,5),some (subcubeFast 4 0,8),some (subcubeFast 4 1,5),some (subcubeFast 4 2,6),some (subcubeFast 8 0,9),some (subcubeFast 8 1,5),some (subcubeFast 8 2,6),some (subcubeFast 8 4,6),some (subcubeFast 16 0,8),some (subcubeFast 16 1,5),some (subcubeFast 32 0,9)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 5 h0SliceList
def h0Specs : List PoolSpec := [(1,[]),(6,[]),(2,[(0,0,1)]),(18,[(0,0,1)]),(4,[(0,0,1)]),(5,[(0,0,1)]),(1,[(2,2,3)]),(6,[(2,2,3)]),(4,[(0,0,1),(2,2,3)]),(5,[(0,0,1),(2,2,3)]),(0,[]),(11,[]),(2,[]),(15,[]),(18,[]),(3,[]),(4,[(2,2,3)]),(22,[(2,2,3)]),(15,[(0,0,1)]),(22,[(0,0,1)]),(24,[(2,2,3)]),(5,[(2,2,3)]),(24,[(0,0,1)]),(21,[]),(13,[]),(17,[]),(10,[]),(4,[]),(22,[]),(24,[]),(5,[]),(2,[(3,0,1)]),(18,[(3,0,1)]),(4,[(3,0,1)]),(5,[(3,0,1)]),(4,[(3,0,1),(2,2,3)]),(0,[(2,2,3)]),(5,[(3,0,1),(2,2,3)]),(15,[(3,0,1)]),(22,[(3,0,1)]),(24,[(3,0,1)]),(6,[(0,2,4)]),(1,[(0,2,4)]),(18,[(3,0,1),(0,2,4)]),(0,[(0,2,4)]),(5,[(3,0,1),(0,2,4)]),(11,[(0,2,4)]),(18,[(0,2,4)]),(3,[(0,2,4)]),(3,[(3,0,1)]),(24,[(0,2,4)]),(5,[(0,2,4)]),(1,[(0,2,4),(1,7,18)]),(5,[(3,0,1),(0,2,4),(1,7,18)]),(2,[(3,0,1),(1,7,18)]),(18,[(3,0,1),(0,2,4),(1,7,18)]),(6,[(0,2,4),(1,7,18)]),(4,[(3,0,1),(1,7,18)]),(7,[]),(6,[(3,3,4)]),(1,[(3,3,4)]),(2,[(3,0,1),(3,3,4)]),(0,[(3,3,4)]),(5,[(3,0,1),(3,3,4)]),(2,[(3,3,4)]),(15,[(3,3,4)]),(24,[(3,3,4)]),(5,[(3,3,4)]),(1,[(3,3,4),(1,7,19)]),(5,[(3,0,1),(3,3,4),(1,7,19)]),(6,[(3,3,4),(1,7,19)]),(2,[(3,0,1),(3,3,4),(1,7,19)]),(18,[(3,0,1),(1,7,19)]),(4,[(3,0,1),(1,7,19)]),(23,[]),(1,[(0,0,2)]),(18,[(0,0,2)]),(4,[(0,0,2)]),(5,[(0,0,2)]),(2,[(2,1,3)]),(6,[(2,1,3)]),(4,[(0,0,2),(2,1,3)]),(5,[(0,0,2),(2,1,3)]),(11,[(0,0,2)]),(4,[(2,1,3)]),(22,[(2,1,3)]),(22,[(0,0,2)]),(24,[(2,1,3)]),(5,[(2,1,3)]),(24,[(0,0,2)]),(20,[]),(1,[(3,0,2)]),(18,[(3,0,2)]),(4,[(3,0,2)]),(5,[(3,0,2)]),(4,[(3,0,2),(2,1,3)]),(0,[(2,1,3)]),(5,[(3,0,2),(2,1,3)]),(11,[(3,0,2)]),(22,[(3,0,2)]),(24,[(3,0,2)]),(6,[(0,1,4)]),(2,[(0,1,4)]),(18,[(3,0,2),(0,1,4)]),(0,[(0,1,4)]),(5,[(3,0,2),(0,1,4)]),(18,[(0,1,4)]),(3,[(0,1,4)]),(3,[(3,0,2)]),(24,[(0,1,4)]),(5,[(0,1,4)]),(1,[(3,0,2),(1,9,16)]),(2,[(0,1,4),(1,9,16)]),(5,[(3,0,2),(0,1,4),(1,9,16)]),(18,[(3,0,2),(0,1,4),(1,9,16)]),(6,[(0,1,4),(1,9,16)]),(4,[(3,0,2),(1,9,16)]),(12,[]),(1,[(3,0,2),(3,3,4)]),(5,[(3,0,2),(3,3,4)]),(11,[(3,3,4)]),(6,[(3,3,4),(1,9,19)]),(1,[(3,0,2),(3,3,4),(1,9,19)]),(2,[(3,3,4),(1,9,19)]),(5,[(3,0,2),(3,3,4),(1,9,19)]),(18,[(3,0,2),(1,9,19)]),(4,[(3,0,2),(1,9,19)]),(8,[]),(1,[(1,0,3)]),(2,[(1,0,3)]),(4,[(1,0,3)]),(5,[(1,0,3)]),(18,[(0,1,2)]),(6,[(0,1,2)]),(4,[(1,0,3),(0,1,2)]),(0,[(0,1,2)]),(5,[(1,0,3),(0,1,2)]),(11,[(1,0,3)]),(22,[(0,1,2)]),(4,[(0,1,2)]),(22,[(1,0,3)]),(24,[(0,1,2)]),(5,[(0,1,2)]),(24,[(1,0,3)]),(1,[(1,0,3),(2,10,14)]),(2,[(1,0,3),(2,10,14)]),(18,[(0,1,2),(2,10,14)]),(5,[(1,0,3),(0,1,2),(2,10,14)]),(6,[(0,1,2),(2,10,14)]),(4,[(1,0,3),(0,1,2),(2,10,14)]),(2,[(1,0,3),(0,1,4)]),(5,[(1,0,3),(0,1,4)]),(15,[(0,1,4)]),(15,[(1,0,3)]),(1,[(1,0,3),(2,10,16)]),(6,[(0,1,4),(2,10,16)]),(2,[(1,0,3),(0,1,4),(2,10,16)]),(18,[(0,1,4),(2,10,16)]),(5,[(1,0,3),(0,1,4),(2,10,16)]),(4,[(1,0,3),(2,10,16)]),(1,[(1,0,3),(0,2,4)]),(5,[(1,0,3),(0,2,4)]),(6,[(0,2,4),(2,10,18)]),(1,[(1,0,3),(0,2,4),(2,10,18)]),(2,[(1,0,3),(2,10,18)]),(18,[(0,2,4),(2,10,18)]),(5,[(1,0,3),(0,2,4),(2,10,18)]),(4,[(1,0,3),(2,10,18)]),(16,[]),(1,[(2,0,3)]),(2,[(2,0,3)]),(4,[(2,0,3)]),(5,[(2,0,3)]),(4,[(2,0,3),(0,1,2)]),(5,[(2,0,3),(0,1,2)]),(11,[(2,0,3)]),(22,[(2,0,3)]),(24,[(2,0,3)]),(1,[(2,0,3),(1,11,14)]),(2,[(2,0,3),(1,11,14)]),(18,[(0,1,2),(1,11,14)]),(5,[(2,0,3),(0,1,2),(1,11,14)]),(4,[(2,0,3),(0,1,2),(1,11,14)]),(10,[(0,1,2)]),(19,[]),(14,[]),(1,[(0,0,4)]),(2,[(0,0,4)]),(18,[(0,0,4)]),(5,[(0,0,4)]),(18,[(0,0,4),(0,1,2)]),(5,[(0,0,4),(0,1,2)]),(3,[(0,1,2)]),(3,[(0,0,4)]),(11,[(0,0,4)]),(24,[(0,0,4)]),(1,[(0,0,4),(1,12,14)]),(2,[(0,0,4),(1,12,14)]),(18,[(0,0,4),(0,1,2),(1,12,14)]),(5,[(0,0,4),(0,1,2),(1,12,14)]),(4,[(0,1,2),(1,12,14)]),(1,[(0,0,4),(1,12,14),(1,3,28)]),(0,[(0,1,2),(1,12,14)]),(1,[(0,0,4),(1,12,14),(3,3,28)]),(5,[(0,1,2),(0,0,4),(1,12,14)]),(2,[(0,0,4),(2,1,3)]),(5,[(0,0,4),(2,1,3)]),(15,[(2,1,3)]),(15,[(0,0,4)]),(9,[]),(1,[(0,0,4),(2,2,3)]),(5,[(0,0,4),(2,2,3)]),(11,[(2,2,3)]),(1,[(3,0,4)]),(2,[(3,0,4)]),(18,[(3,0,4)]),(5,[(3,0,4)]),(18,[(3,0,4),(0,1,2)]),(5,[(3,0,4),(0,1,2)]),(3,[(3,0,4)]),(11,[(3,0,4)]),(24,[(3,0,4)]),(2,[(3,0,4),(2,1,3)]),(5,[(3,0,4),(2,1,3)]),(15,[(3,0,4)]),(10,[(2,1,3)]),(1,[(3,0,4),(2,2,3)]),(5,[(3,0,4),(2,2,3)]),(10,[(2,2,3)]),(5,[(0,1,2),(3,3,4)]),(1,[(3,3,4),(1,14,19)]),(2,[(3,3,4),(1,14,19)]),(18,[(0,1,2),(1,14,19)]),(4,[(0,1,2),(1,14,19)]),(5,[(0,1,2),(3,3,4),(1,14,19)]),(10,[(0,1,2),(1,14,19)]),(5,[(2,1,3),(0,2,4)]),(5,[(0,1,4),(2,2,3)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 8 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 32 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 16 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 16 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 8 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 8 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 8 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 8 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 4 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 4 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 2 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 2 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 2 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 2 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 1 16) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 1 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 1 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 1 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 1 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 32) 10 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 16) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 8) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h56Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (7 - 1) xs.toFinset) h0Empty := trivial
def h0Block7_0 : List NodeSpec := [([0,1,2,3,4,5,28,29],[14,15,198,200,201,202],[0]),([0,1,2,3,4,5,28,30],[14,15,198,203],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 7 h0Block7_0 = true := by decide +kernel
def h0Nodes7 : List NodeSpec := h0Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 7 h0Nodes7 = true := h0Test7_0
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check7
def h0Block8_0 : List NodeSpec := [([0,1,2,3,4,5,20],[0,1,12,14,15,27,29,30,44,52,53,54,55,56,57,58],[0]),([0,1,2,3,4,5,21],[0,1,12,13,14,27,29,30,58,62,68,69,70,71,72,73],[0]),([0,1,2,3,4,5,22],[0,1,12,14,15,27,29,30,104,111,112,113,114,115,116,117],[0]),([0,1,2,3,4,5,23],[0,1,11,12,14,27,29,30,62,121,122,123,124,125,126,127],[0]),([0,1,2,3,4,5,24],[0,1,12,14,27,28,29,30,117,135,144,145,146,147,148,149],[0]),([0,1,2,3,4,5,25],[0,1,12,13,14,27,29,30,104,117,154,155,156,157,158,159],[0]),([0,1,2,3,4,5,26],[0,1,11,12,14,27,29,30,44,162,163,164,165,166,167,168],[0]),([0,1,2,3,4,5,27],[0,10,12,14,27,28,29,30,133,178,179,180,181,182,183],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := [([0,1,2,3,4,5,28],[0,10,12,14,15,27,29,30,133,196,197,198,199,200],[0]),([0,1,2,3,4,5,12,28],[10,11,27,133,186,187,188,189,193,194,195,196,197,198,199,200],[0]),([0,1,2,3,4,5,14,28],[0,1,12,132,133,135,139,141,142,192,194,196,197,198,199,200,204],[0]),([0,1,2,3,4,5,31],[0,1,10,12,14,27,29,30,185,230,231,232,233,234,235],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Nodes8 = true := by
  unfold h0Nodes8 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h0Test8_0,h0Test8_1⟩
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket7Ok h0Check8
def h0Block9_0 : List NodeSpec := [([0,1,2,3,4,5,6,17],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25],[0]),([0,1,2,3,4,5,7,17],[0,1,6,7,10,11,12,13,14,15,16,17,20,21,23,24,25,31,32,33,34,35,36,37,38,39,40],[0]),([0,1,2,3,4,5,7,18],[0,1,10,11,12,13,24,25,27,28,31,32,33,34,38,40,41,42,43,44,45,46,47,48,49,50,51],[0]),([0,1,2,3,4,5,7,19],[0,1,10,11,14,15,27,28,31,32,33,34,38,40,49,58,59,60,61,62,63,64,65,66,67,74],[0]),([0,1,2,3,4,5,8,15],[0,1,10,11,12,13,14,15,24,25,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90],[0]),([0,1,2,3,4,5,9,15],[0,1,10,11,12,13,14,15,24,25,79,80,84,85,87,88,90,91,92,93,94,95,96,97,98,99,100],[0]),([0,1,2,3,4,5,9,16],[0,1,10,11,12,13,24,25,27,28,91,92,93,94,98,100,101,102,103,104,105,106,107,108,109,110],[0]),([0,1,2,3,4,5,9,19],[1,10,12,13,14,15,27,28,59,60,62,64,66,67,74,91,92,93,94,98,100,108,118,119,120,127],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := [([0,1,2,3,4,5,10,14],[0,1,10,11,12,13,14,15,117,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143],[0]),([0,1,2,3,4,5,10,16],[0,1,10,11,14,15,27,28,101,102,104,106,109,110,117,128,129,130,131,137,143,150,151,152,153],[0]),([0,1,2,3,4,5,10,18],[1,10,12,13,14,15,27,28,41,42,44,46,47,50,51,128,129,130,131,137,143,153,160,161,168],[0]),([0,1,2,3,4,5,11,14],[0,1,10,11,12,13,14,15,132,133,138,139,141,142,169,170,171,172,173,174,175,176,177,184,185],[0]),([0,1,2,3,4,5,12,14],[0,1,10,11,12,13,27,28,132,133,139,141,142,186,187,188,189,190,191,192,193,194,195],[0]),([0,1,2,3,4,5,12,15],[0,1,10,11,14,15,27,28,79,80,84,87,88,90,186,187,188,189,194,195,205,206,207,208,209],[0]),([0,1,2,3,4,5,12,17],[1,6,7,10,12,13,14,15,16,20,21,23,27,28,186,187,188,189,194,195,208,209,210,211,212],[0]),([0,1,2,3,4,5,13,14],[0,1,10,11,12,13,26,27,28,132,133,135,139,141,142,183,192,213,214,215,216,217,218,219,220,221],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Block9_2 : List NodeSpec := [([0,1,2,3,4,5,13,15],[0,1,10,11,14,15,26,27,28,79,80,84,87,88,96,207,213,214,215,216,220,221,222,223,224,225],[0]),([0,1,2,3,4,5,13,17],[1,6,7,10,12,13,14,15,16,20,21,26,27,28,36,212,213,214,215,216,220,221,224,226,227,228],[0]),([0,1,2,3,4,5,14,19],[0,11,12,13,14,15,27,28,59,60,62,64,66,67,120,132,133,135,139,141,142,185,192,229],[0]),([0,1,2,3,4,5,15,18],[0,11,12,13,14,15,24,25,27,28,41,42,44,46,47,50,51,79,80,84,87,88,90,96,207,236],[0]),([0,1,2,3,4,5,16,17],[0,6,7,11,12,13,14,15,16,20,21,23,24,25,27,28,36,101,102,104,106,109,110,152,212,237],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1 ++ h0Block9_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := by
  unfold h0Nodes9 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h0Test9_0,h0Test9_1⟩,h0Test9_2⟩
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5,12,13,14,15,26,27,28,29,30],[0]),([0,1,2,3,4,5,7],[0,1,10,12,13,14,15,27,28,29,30,31,32,33,34],[0]),([0,1,2,3,4,5,8],[0,1,11,12,14,15,26,27,28,29,30,75,76,77,78],[0]),([0,1,2,3,4,5,9],[0,1,10,11,12,14,15,27,28,29,30,91,92,93,94],[0]),([0,1,2,3,4,5,10],[0,1,10,11,12,13,14,27,28,29,30,128,129,130,131],[0]),([0,1,2,3,4,5,11],[0,1,11,12,13,14,26,27,28,29,30,169,170,171,172],[0]),([0,1,2,3,4,5,12],[0,1,11,12,13,14,15,27,29,30,186,187,188,189],[0]),([0,1,2,3,4,5,13],[0,1,10,11,12,13,14,15,27,29,30,213,214,215,216],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Block10_1 : List NodeSpec := [([0,1,2,3,4,5,14],[0,1,10,11,12,14,15,27,28,29,30,132,139,142],[0]),([0,1,2,3,4,5,15],[0,1,10,11,12,13,14,27,28,29,30,79,84,88],[0]),([0,1,2,3,4,5,16],[0,1,10,11,12,13,14,15,26,27,29,30,102,106,110],[0]),([0,1,2,3,4,5,17],[0,1,6,10,11,12,13,14,16,21,27,28,29,30],[0]),([0,1,2,3,4,5,18],[0,1,10,11,12,13,14,15,26,27,29,30,42,47,51],[0]),([0,1,2,3,4,5,19],[0,1,10,11,12,13,14,15,26,27,29,30,60,64,67],[0])]
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
def h0Block11_0 : List NodeSpec := [([0,1,2,3,4,5],[0,12,14,27,30],[0])]
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
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 13]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276676776 * 2 ^ 32 + 3936938112) ||| ((4276676776 * 2 ^ 32 + 3936938112) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4276676776 * 2 ^ 32 + 3936938112) ||| ((4276676776 * 2 ^ 32 + 3936938112) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_49231
theorem PEqualNP.Outside.L_meta_49231 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3936938112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3936938112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_49231.table2_of_lower (4276676776 * 2 ^ 32 + 3936938112) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_49231.low_root
    PEqualNP.Outside.L_meta_49231.wit PEqualNP.Outside.L_meta_49231.wo (by decide)
    PEqualNP.Outside.L_meta_49231.wit_mono PEqualNP.Outside.L_meta_49231.wit_eval s hcs
