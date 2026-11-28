import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_42056
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
def h3R : List Nat := varsOf 14
def h3G : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def h3Pos : List Nat := [10,12,6,6,12,10]
def h3Neg : List Nat := [8,8,2,4,4,2]
def h3Mask : Nat := fullMask 6
def h3Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xff00ff00ff00ff00ff00ff00ff00ff00,51,3)]
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
lemma h3Bound : Lower h3R h3G 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 3,2,10)]) (by decide +kernel) h3Bucket3Ok (by decide +kernel)
def h2R : List Nat := varsOf 15
def h2G : Nat := 0xe8c0e8c0e8c0e8c0e8c0e8c0e8c0e8c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,10,11)]) (by decide +kernel) h3Bound
def h5R : List Nat := varsOf 22
def h5G : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def h5Pos : List Nat := [18,20,6,6,20,18]
def h5Neg : List Nat := [16,16,2,4,4,2]
def h5Mask : Nat := fullMask 6
def h5Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h5Steps : List (Nat × Nat × Nat) := []
def h5W : BT Decor := buildWiresBT 2 h5Base h5Steps
def h5AutoList : List (List (Nat × Nat)) := [[]]
def h5Autos : BT (List (Nat × Nat)) := btOfList 1 h5AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Pairs : goodPairs h5G h5Pos h5Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5BaseOk : ∀ x ∈ h5Base, faithful h5Pos h5Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5WOk : btAll (fun x => faithful h5Pos h5Neg x ∧ x.1 < 2^128) h5W := buildWiresBT_faithful h5BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h5G = h5G) h5Autos := btAll_ofList (autos_of (by decide +kernel))
def h5SliceList : List (Option (Nat × Nat)) := []
def h5Slices : BT (Option (Nat × Nat)) := btOfList 1 h5SliceList
def h5Specs : List PoolSpec := []
def h5Pools : BT (Option BoundPool) := buildPoolsBT 1 h5W h5R h5Slices h5Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h5R h5G p.1 p.2) h5Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h5R h5G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h5R h5G c) h5Pools := buildPoolsBT_sound h5SlicesOk
def h5Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h5G (3 - 1) xs.toFinset) h5Empty := trivial
def h5Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test3_0 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Empty 3 h5Block3_0 = true := by decide +kernel
def h5Nodes3 : List NodeSpec := h5Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Check3 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Empty 3 h5Nodes3 = true := h5Test3_0
def h5Bucket3 : BT (List (List Nat)) := buildBucketsBT h5W h5Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h5G 3 xs.toFinset) h5Bucket3 := buildBucketsBT_sound (by decide) h5Pairs h5WOk h5PoolsOk h5AutosOk h5EmptyOk h5Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 4,2,18)]) (by decide +kernel) h5Bucket3Ok (by decide +kernel)
def h4R : List Nat := varsOf 23
def h4G : Nat := 0xe8e8c0c0e8e8c0c0e8e8c0c0e8e8c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,18,19)]) (by decide +kernel) h5Bound
def h6R : List Nat := varsOf 25
def h6G : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00
def h6Pos : List Nat := [17,24,9,9,24,17]
def h6Neg : List Nat := [16,16,1,8,8,1]
def h6Mask : Nat := fullMask 6
def h6Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h6Steps : List (Nat × Nat × Nat) := []
def h6W : BT Decor := buildWiresBT 2 h6Base h6Steps
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
def h6Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test3_0 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Empty 3 h6Block3_0 = true := by decide +kernel
def h6Nodes3 : List NodeSpec := h6Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Check3 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Empty 3 h6Nodes3 = true := h6Test3_0
def h6Bucket3 : BT (List (List Nat)) := buildBucketsBT h6W h6Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h6G 3 xs.toFinset) h6Bucket3 := buildBucketsBT_sound (by decide) h6Pairs h6WOk h6PoolsOk h6AutosOk h6EmptyOk h6Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 4 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h6Bucket3Ok (by decide +kernel)
def h7R : List Nat := varsOf 27
def h7G : Nat := 0xcc888800cc888800cc888800cc888800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,9,11)]) (by decide +kernel) h6Bound
def h9R : List Nat := varsOf 7
def h9G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def h9Pos : List Nat := [5,6,3,3,6,5]
def h9Neg : List Nat := [4,4,1,2,2,1]
def h9Mask : Nat := fullMask 6
def h9Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,51,3)]
def h9Steps : List (Nat × Nat × Nat) := []
def h9W : BT Decor := buildWiresBT 2 h9Base h9Steps
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
def h9SliceList : List (Option (Nat × Nat)) := []
def h9Slices : BT (Option (Nat × Nat)) := btOfList 1 h9SliceList
def h9Specs : List PoolSpec := []
def h9Pools : BT (Option BoundPool) := buildPoolsBT 1 h9W h9R h9Slices h9Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h9R h9G p.1 p.2) h9Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h9R h9G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h9R h9G c) h9Pools := buildPoolsBT_sound h9SlicesOk
def h9Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G (3 - 1) xs.toFinset) h9Empty := trivial
def h9Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test3_0 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Empty 3 h9Block3_0 = true := by decide +kernel
def h9Nodes3 : List NodeSpec := h9Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Check3 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Empty 3 h9Nodes3 = true := h9Test3_0
def h9Bucket3 : BT (List (List Nat)) := buildBucketsBT h9W h9Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G 3 xs.toFinset) h9Bucket3 := buildBucketsBT_sound (by decide) h9Pairs h9WOk h9PoolsOk h9AutosOk h9EmptyOk h9Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel) h9Bucket3Ok (by decide +kernel)
def h8R : List Nat := varsOf 15
def h8G : Nat := 0xece8ece8ece8ece8ece8ece8ece8ece8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,2,10)]) (by decide +kernel) h9Bound
def h10R : List Nat := varsOf 23
def h10G : Nat := 0xecece8e8ecece8e8ecece8e8ecece8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,2,18)]) (by decide +kernel) h9Bound
def h11R : List Nat := varsOf 29
def h11G : Nat := 0xfffafaf0fffafaf0fffafaf0fffafaf0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,0,4)]) (by decide +kernel) h6Bound
def h12R : List Nat := varsOf 30
def h12G : Nat := 0xfcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,2,10)]) (by decide +kernel) h5Bound
def h1R : List Nat := varsOf 31
def h1G : Nat := 0xece8e8c0ece8e8c0ece8e8c0ece8e8c0
def h1Pos : List Nat := [6,13,6,6,7,21,26,11,26,19,11,13,26,13,21,7,21,7,11,14,22]
def h1Neg : List Nat := [4,12,5,2,3,20,18,3,10,3,10,9,24,5,5,5,17,2,9,10,18]
def h1Mask : Nat := fullMask 21
def h1Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7eeb2,0x5ea94),(0xcccccccccccccccccccccccccccccccc,0x1e97dd,0x1a07d8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1be83f,0xe027),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xc3dc2,0xc1d02),(0xffff0000ffff0000ffff0000ffff0000,0x115360,0x111060)]
def h1Steps : List (Nat × Nat × Nat) := [(0,0,1),(2,0,2)]
def h1W : BT Decor := buildWiresBT 3 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[]]
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
def h1SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 4 0,5),some (subcubeFast 4 2,4),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5)]
def h1Slices : BT (Option (Nat × Nat)) := btOfList 3 h1SliceList
def h1Specs : List PoolSpec := [(0,[]),(1,[]),(4,[(0,0,1)]),(4,[]),(5,[]),(6,[]),(2,[]),(7,[]),(3,[]),(1,[(2,0,2)])]
def h1Pools : BT (Option BoundPool) := buildPoolsBT 4 h1W h1R h1Slices h1Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice7 : Slice h1R h1G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice6 : Slice h1R h1G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice5 : Slice h1R h1G (subcubeFast 4 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice4 : Slice h1R h1G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice3 : Slice h1R h1G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice2 : Slice h1R h1G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice1 : Slice h1R h1G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice0 : Slice h1R h1G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h1R h1G p.1 p.2) h1Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h1R h1G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h1Slice0) (forall_cons (fun _ h => by cases h; exact h1Slice1) (forall_cons (fun _ h => by cases h; exact h1Slice2) (forall_cons (fun _ h => by cases h; exact h1Slice3) (forall_cons (fun _ h => by cases h; exact h1Slice4) (forall_cons (fun _ h => by cases h; exact h1Slice5) (forall_cons (fun _ h => by cases h; exact h1Slice6) (forall_cons (fun _ h => by cases h; exact h1Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h1R h1G c) h1Pools := buildPoolsBT_sound h1SlicesOk
def h1Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G (6 - 1) xs.toFinset) h1Empty := trivial
def h1Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8],[0]),([0,1,2,3,4,6],[0,1,3,4,5,6,7,8,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 6 h1Block6_0 = true := by decide +kernel
def h1Nodes6 : List NodeSpec := h1Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check6 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 6 h1Nodes6 = true := h1Test6_0
def h1Bucket6 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 6 xs.toFinset) h1Bucket6 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1EmptyOk h1Check6
def h1Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,3,4,5,6,7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test7_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket6 7 h1Block7_0 = true := by decide +kernel
def h1Nodes7 : List NodeSpec := h1Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check7 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket6 7 h1Nodes7 = true := h1Test7_0
def h1Bucket7 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 7 xs.toFinset) h1Bucket7 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket6Ok h1Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bound : Lower h1R h1G 8 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,3,11),(VAR 4,3,19)]) (by decide +kernel) h1Bucket7Ok (by decide +kernel)
def h13R : List Nat := varsOf 42
def h13G : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def h13Pos : List Nat := [34,40,10,10,40,34]
def h13Neg : List Nat := [32,32,2,8,8,2]
def h13Mask : Nat := fullMask 6
def h13Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
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
lemma h13Bound : Lower h13R h13G 4 := lower_of_forestBT (essPairs := [(VAR 1,8,10),(VAR 3,2,10),(VAR 5,2,34)]) (by decide +kernel) h13Bucket3Ok (by decide +kernel)
def h14R : List Nat := varsOf 46
def h14G : Nat := 0xffccffccfcc0fcc0ffccffccfcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,2,6)]) (by decide +kernel) h13Bound
def h16R : List Nat := varsOf 43
def h16G : Nat := 0xaa88aa8888008800aa88aa8888008800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,10,11)]) (by decide +kernel) h13Bound
def h17R : List Nat := varsOf 39
def h17G : Nat := 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 5 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,1,33)]) (by decide +kernel) h9Bound
def h15R : List Nat := varsOf 47
def h15G : Nat := 0xeac8eac8e8c0e8c0eac8eac8e8c0e8c0
def h15Pos : List Nat := [6,13,7,11,6,7,35,11,35,11,13,13,41,35,38,41]
def h15Neg : List Nat := [4,12,5,10,2,3,34,3,3,9,9,5,9,33,34,33]
def h15Mask : Nat := fullMask 16
def h15Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xbfee,0xbfa4),(0xcccccccccccccccccccccccccccccccc,0x63fd,0x41f8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x4c37,2055),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x9e8a,5642),(0xffffffff00000000ffffffff00000000,0xf140,0xe040)]
def h15Steps : List (Nat × Nat × Nat) := []
def h15W : BT Decor := buildWiresBT 3 h15Base h15Steps
def h15AutoList : List (List (Nat × Nat)) := [[]]
def h15Autos : BT (List (Nat × Nat)) := btOfList 1 h15AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Pairs : goodPairs h15G h15Pos h15Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15BaseOk : ∀ x ∈ h15Base, faithful h15Pos h15Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15WOk : btAll (fun x => faithful h15Pos h15Neg x ∧ x.1 < 2^128) h15W := buildWiresBT_faithful h15BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h15G = h15G) h15Autos := btAll_ofList (autos_of (by decide +kernel))
def h15SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 8,5),some (subcubeFast 4 0,5),some (subcubeFast 32 0,5)]
def h15Slices : BT (Option (Nat × Nat)) := btOfList 2 h15SliceList
def h15Specs : List PoolSpec := [(0,[]),(2,[]),(1,[]),(3,[])]
def h15Pools : BT (Option BoundPool) := buildPoolsBT 2 h15W h15R h15Slices h15Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice3 : Slice h15R h15G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice2 : Slice h15R h15G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice1 : Slice h15R h15G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice0 : Slice h15R h15G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h15R h15G p.1 p.2) h15Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h15R h15G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h15Slice0) (forall_cons (fun _ h => by cases h; exact h15Slice1) (forall_cons (fun _ h => by cases h; exact h15Slice2) (forall_cons (fun _ h => by cases h; exact h15Slice3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h15R h15G c) h15Pools := buildPoolsBT_sound h15SlicesOk
def h15Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G (6 - 1) xs.toFinset) h15Empty := trivial
def h15Block6_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test6_0 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Empty 6 h15Block6_0 = true := by decide +kernel
def h15Nodes6 : List NodeSpec := h15Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Check6 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Empty 6 h15Nodes6 = true := h15Test6_0
def h15Bucket6 : BT (List (List Nat)) := buildBucketsBT h15W h15Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G 6 xs.toFinset) h15Bucket6 := buildBucketsBT_sound (by decide) h15Pairs h15WOk h15PoolsOk h15AutosOk h15EmptyOk h15Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 7 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,3,11),(VAR 5,3,35)]) (by decide +kernel) h15Bucket6Ok (by decide +kernel)
def h18R : List Nat := varsOf 50
def h18G : Nat := 0xffffcccccccc0000ffffcccccccc0000
def h18Pos : List Nat := [34,48,18,18,48,34]
def h18Neg : List Nat := [32,32,2,16,16,2]
def h18Mask : Nat := fullMask 6
def h18Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xffff0000ffff0000ffff0000ffff0000,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
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
lemma h18Bound : Lower h18R h18G 4 := lower_of_forestBT (essPairs := [(VAR 1,16,18),(VAR 4,2,18),(VAR 5,2,34)]) (by decide +kernel) h18Bucket3Ok (by decide +kernel)
def h19R : List Nat := varsOf 54
def h19G : Nat := 0xffffccccfcfcc0c0ffffccccfcfcc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,2,6)]) (by decide +kernel) h18Bound
def h21R : List Nat := varsOf 51
def h21G : Nat := 0xaaaa888888880000aaaa888888880000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,18,19)]) (by decide +kernel) h18Bound
def h20R : List Nat := varsOf 55
def h20G : Nat := 0xeaeac8c8e8e8c0c0eaeac8c8e8e8c0c0
def h20Pos : List Nat := [6,21,7,19,6,7,35,19,35,19,21,21,49,35,38,49]
def h20Neg : List Nat := [4,20,5,18,2,3,34,3,3,17,17,5,17,33,34,33]
def h20Mask : Nat := fullMask 16
def h20Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xbfee,0xbfa4),(0xcccccccccccccccccccccccccccccccc,0x63fd,0x41f8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x4c37,2055),(0xffff0000ffff0000ffff0000ffff0000,0x9e8a,5642),(0xffffffff00000000ffffffff00000000,0xf140,0xe040)]
def h20Steps : List (Nat × Nat × Nat) := []
def h20W : BT Decor := buildWiresBT 3 h20Base h20Steps
def h20AutoList : List (List (Nat × Nat)) := [[]]
def h20Autos : BT (List (Nat × Nat)) := btOfList 1 h20AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Pairs : goodPairs h20G h20Pos h20Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20BaseOk : ∀ x ∈ h20Base, faithful h20Pos h20Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20WOk : btAll (fun x => faithful h20Pos h20Neg x ∧ x.1 < 2^128) h20W := buildWiresBT_faithful h20BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h20G = h20G) h20Autos := btAll_ofList (autos_of (by decide +kernel))
def h20SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 16,5),some (subcubeFast 4 0,5),some (subcubeFast 32 0,5)]
def h20Slices : BT (Option (Nat × Nat)) := btOfList 2 h20SliceList
def h20Specs : List PoolSpec := [(0,[]),(2,[]),(1,[]),(3,[])]
def h20Pools : BT (Option BoundPool) := buildPoolsBT 2 h20W h20R h20Slices h20Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Slice3 : Slice h20R h20G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Slice2 : Slice h20R h20G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Slice1 : Slice h20R h20G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Slice0 : Slice h20R h20G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h20R h20G p.1 p.2) h20Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h20R h20G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h20Slice0) (forall_cons (fun _ h => by cases h; exact h20Slice1) (forall_cons (fun _ h => by cases h; exact h20Slice2) (forall_cons (fun _ h => by cases h; exact h20Slice3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h20R h20G c) h20Pools := buildPoolsBT_sound h20SlicesOk
def h20Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h20G (6 - 1) xs.toFinset) h20Empty := trivial
def h20Block6_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Test6_0 : checkNodesBT h20W h20G h20Mask h20Pools h20Autos h20Empty 6 h20Block6_0 = true := by decide +kernel
def h20Nodes6 : List NodeSpec := h20Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Check6 : checkNodesBT h20W h20G h20Mask h20Pools h20Autos h20Empty 6 h20Nodes6 = true := h20Test6_0
def h20Bucket6 : BT (List (List Nat)) := buildBucketsBT h20W h20Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h20G 6 xs.toFinset) h20Bucket6 := buildBucketsBT_sound (by decide) h20Pairs h20WOk h20PoolsOk h20AutosOk h20EmptyOk h20Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 7 := lower_of_forestBT (essPairs := [(VAR 0,18,19),(VAR 1,4,6),(VAR 2,2,6),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h20Bucket6Ok (by decide +kernel)
def h23R : List Nat := varsOf 27
def h23G : Nat := 0xeeaaaa88eeaaaa88eeaaaa88eeaaaa88
def h23Pos : List Nat := [9,26,9,17,3,9,26,17,26,3,3,3,9,3,17,11,11,19,19,25,25]
def h23Neg : List Nat := [8,24,10,16,2,1,18,1,10,1,0,10,0,18,0,10,1,18,1,24,1]
def h23Mask : Nat := fullMask 21
def h23Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xcccccccccccccccccccccccccccccccc,0x7af52,0x2a954),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x199167,0x88907),(0xffff0000ffff0000ffff0000ffff0000,0x1e41ca,0xa204a)]
def h23Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(0,1,28),(2,2,4),(1,3,4),(0,1,31),(2,3,4),(0,2,5),(1,1,34),(3,2,5),(0,3,5),(1,1,37),(3,3,5),(2,1,8),(1,3,8),(0,2,41),(2,3,8),(3,1,9),(0,3,9),(1,2,45),(3,3,9),(2,1,12),(2,2,12),(3,1,13),(3,2,13),(1,3,18),(0,1,52),(2,3,18),(1,2,54),(1,3,19),(0,2,56),(2,3,19),(1,1,58),(1,2,22),(0,1,60),(2,2,23),(1,1,62)]
def h23W : BT Decor := buildWiresBT 6 h23Base h23Steps
def h23AutoList : List (List (Nat × Nat)) := [[]]
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
def h23SliceList : List (Option (Nat × Nat)) := []
def h23Slices : BT (Option (Nat × Nat)) := btOfList 1 h23SliceList
def h23Specs : List PoolSpec := []
def h23Pools : BT (Option BoundPool) := buildPoolsBT 1 h23W h23R h23Slices h23Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h23R h23G p.1 p.2) h23Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h23R h23G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h23R h23G c) h23Pools := buildPoolsBT_sound h23SlicesOk
def h23Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h23G (3 - 1) xs.toFinset) h23Empty := trivial
def h23Block3_0 : List NodeSpec := [([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,2,31],[],[0]),([0,1,2,33],[],[0]),([0,1,3,34],[],[0]),([0,1,3,36],[],[0]),([0,1,2,37],[],[0]),([0,1,2,39],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Test3_0 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Empty 3 h23Block3_0 = true := by decide +kernel
def h23Block3_1 : List NodeSpec := [([0,2,3,35],[],[0]),([0,2,3,40],[],[0]),([0,1,2,41],[],[0]),([0,1,2,43],[],[0]),([0,2,3,29],[],[0]),([0,2,3,44],[],[0]),([0,1,2,45],[],[0]),([0,1,2,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Test3_1 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Empty 3 h23Block3_1 = true := by decide +kernel
def h23Block3_2 : List NodeSpec := [([0,2,3,38],[],[0]),([0,2,3,48],[],[0]),([0,1,3,46],[],[0]),([0,1,3,49],[],[0]),([0,2,3,32],[],[0]),([0,2,3,50],[],[0]),([0,1,3,42],[],[0]),([0,1,3,51],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Test3_2 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Empty 3 h23Block3_2 = true := by decide +kernel
def h23Block3_3 : List NodeSpec := [([0,3,16,17],[],[0]),([0,1,2,52],[],[0]),([0,1,2,54],[],[0]),([0,1,2,56],[],[0]),([0,1,2,58],[],[0]),([0,2,20,21],[],[0]),([0,1,3,60],[],[0]),([0,1,3,57],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Test3_3 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Empty 3 h23Block3_3 = true := by decide +kernel
def h23Block3_4 : List NodeSpec := [([0,1,3,55],[],[0]),([0,1,3,62],[],[0]),([0,1,24,25],[],[0]),([0,2,3,63],[],[0]),([0,2,3,53],[],[0]),([0,2,3,59],[],[0]),([0,2,3,61],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Test3_4 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Empty 3 h23Block3_4 = true := by decide +kernel
def h23Nodes3 : List NodeSpec := h23Block3_0 ++ h23Block3_1 ++ h23Block3_2 ++ h23Block3_3 ++ h23Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Check3 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Empty 3 h23Nodes3 = true := by
  unfold h23Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h23Test3_0,h23Test3_1⟩,h23Test3_2⟩,h23Test3_3⟩,h23Test3_4⟩
def h23Bucket3 : BT (List (List Nat)) := buildBucketsBT h23W h23Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h23G 3 xs.toFinset) h23Bucket3 := buildBucketsBT_sound (by decide) h23Pairs h23WOk h23PoolsOk h23AutosOk h23EmptyOk h23Check3
def h23Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Test4_0 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Bucket3 4 h23Block4_0 = true := by decide +kernel
def h23Block4_1 : List NodeSpec := [([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0]),([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Test4_1 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Bucket3 4 h23Block4_1 = true := by decide +kernel
def h23Block4_2 : List NodeSpec := [([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0]),([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Test4_2 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Bucket3 4 h23Block4_2 = true := by decide +kernel
def h23Nodes4 : List NodeSpec := h23Block4_0 ++ h23Block4_1 ++ h23Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Check4 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Bucket3 4 h23Nodes4 = true := by
  unfold h23Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h23Test4_0,h23Test4_1⟩,h23Test4_2⟩
def h23Bucket4 : BT (List (List Nat)) := buildBucketsBT h23W h23Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h23G 4 xs.toFinset) h23Bucket4 := buildBucketsBT_sound (by decide) h23Pairs h23WOk h23PoolsOk h23AutosOk h23Bucket3Ok h23Check4
def h23Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Test5_0 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Bucket4 5 h23Block5_0 = true := by decide +kernel
def h23Nodes5 : List NodeSpec := h23Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Check5 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Bucket4 5 h23Nodes5 = true := h23Test5_0
def h23Bucket5 : BT (List (List Nat)) := buildBucketsBT h23W h23Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h23G 5 xs.toFinset) h23Bucket5 := buildBucketsBT_sound (by decide) h23Pairs h23WOk h23PoolsOk h23AutosOk h23Bucket4Ok h23Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h23Bucket5Ok (by decide +kernel)
def h24R : List Nat := varsOf 43
def h24G : Nat := 0xeeaaeeaacc88cc88eeaaeeaacc88cc88
def h24Pos : List Nat := [10,3,3,41,42,10,41,33]
def h24Neg : List Nat := [8,1,2,40,40,2,9,1]
def h24Mask : Nat := fullMask 8
def h24Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,206,194),(0xcccccccccccccccccccccccccccccccc,55,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,121,89),(0xffffffff00000000ffffffff00000000,216,24)]
def h24Steps : List (Nat × Nat × Nat) := []
def h24W : BT Decor := buildWiresBT 2 h24Base h24Steps
def h24AutoList : List (List (Nat × Nat)) := [[]]
def h24Autos : BT (List (Nat × Nat)) := btOfList 1 h24AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Pairs : goodPairs h24G h24Pos h24Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24BaseOk : ∀ x ∈ h24Base, faithful h24Pos h24Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24WOk : btAll (fun x => faithful h24Pos h24Neg x ∧ x.1 < 2^128) h24W := buildWiresBT_faithful h24BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h24G = h24G) h24Autos := btAll_ofList (autos_of (by decide +kernel))
def h24SliceList : List (Option (Nat × Nat)) := []
def h24Slices : BT (Option (Nat × Nat)) := btOfList 1 h24SliceList
def h24Specs : List PoolSpec := []
def h24Pools : BT (Option BoundPool) := buildPoolsBT 1 h24W h24R h24Slices h24Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h24R h24G p.1 p.2) h24Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h24R h24G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h24R h24G c) h24Pools := buildPoolsBT_sound h24SlicesOk
def h24Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h24G (3 - 1) xs.toFinset) h24Empty := trivial
def h24Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Test3_0 : checkNodesBT h24W h24G h24Mask h24Pools h24Autos h24Empty 3 h24Block3_0 = true := by decide +kernel
def h24Nodes3 : List NodeSpec := h24Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Check3 : checkNodesBT h24W h24G h24Mask h24Pools h24Autos h24Empty 3 h24Nodes3 = true := h24Test3_0
def h24Bucket3 : BT (List (List Nat)) := buildBucketsBT h24W h24Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h24G 3 xs.toFinset) h24Bucket3 := buildBucketsBT_sound (by decide) h24Pairs h24WOk h24PoolsOk h24AutosOk h24EmptyOk h24Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,2,10),(VAR 5,1,33)]) (by decide +kernel) h24Bucket3Ok (by decide +kernel)
def h25R : List Nat := varsOf 51
def h25G : Nat := 0xeeeeaaaacccc8888eeeeaaaacccc8888
def h25Pos : List Nat := [18,3,3,49,50,18,49,33]
def h25Neg : List Nat := [16,1,2,48,48,2,17,1]
def h25Mask : Nat := fullMask 8
def h25Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,206,194),(0xcccccccccccccccccccccccccccccccc,55,36),(0xffff0000ffff0000ffff0000ffff0000,121,89),(0xffffffff00000000ffffffff00000000,216,24)]
def h25Steps : List (Nat × Nat × Nat) := []
def h25W : BT Decor := buildWiresBT 2 h25Base h25Steps
def h25AutoList : List (List (Nat × Nat)) := [[]]
def h25Autos : BT (List (Nat × Nat)) := btOfList 1 h25AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Pairs : goodPairs h25G h25Pos h25Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25BaseOk : ∀ x ∈ h25Base, faithful h25Pos h25Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25WOk : btAll (fun x => faithful h25Pos h25Neg x ∧ x.1 < 2^128) h25W := buildWiresBT_faithful h25BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h25G = h25G) h25Autos := btAll_ofList (autos_of (by decide +kernel))
def h25SliceList : List (Option (Nat × Nat)) := []
def h25Slices : BT (Option (Nat × Nat)) := btOfList 1 h25SliceList
def h25Specs : List PoolSpec := []
def h25Pools : BT (Option BoundPool) := buildPoolsBT 1 h25W h25R h25Slices h25Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h25R h25G p.1 p.2) h25Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h25R h25G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h25R h25G c) h25Pools := buildPoolsBT_sound h25SlicesOk
def h25Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h25G (3 - 1) xs.toFinset) h25Empty := trivial
def h25Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Test3_0 : checkNodesBT h25W h25G h25Mask h25Pools h25Autos h25Empty 3 h25Block3_0 = true := by decide +kernel
def h25Nodes3 : List NodeSpec := h25Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Check3 : checkNodesBT h25W h25G h25Mask h25Pools h25Autos h25Empty 3 h25Nodes3 = true := h25Test3_0
def h25Bucket3 : BT (List (List Nat)) := buildBucketsBT h25W h25Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h25G 3 xs.toFinset) h25Bucket3 := buildBucketsBT_sound (by decide) h25Pairs h25WOk h25PoolsOk h25AutosOk h25EmptyOk h25Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 4,2,18),(VAR 5,1,33)]) (by decide +kernel) h25Bucket3Ok (by decide +kernel)
def h26R : List Nat := varsOf 57
def h26G : Nat := 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 5 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,1,33)]) (by decide +kernel) h6Bound
def h27R : List Nat := varsOf 58
def h27G : Nat := 0xffffffcccccccc00ffffffcccccccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,2,10)]) (by decide +kernel) h18Bound
def h22R : List Nat := varsOf 59
def h22G : Nat := 0xeeaaaa88cc888800eeaaaa88cc888800
def h22Pos : List Nat := [26,41,26,26,49,11,26,19,41,49,11,35,11,19,41,35,11,19,19,41,49,35,35,26,35,26,58,19,11,11,35,43,51,11,19,58,41,27,26,58,35,49,57,26,57,49,41,26,49,41,11,35,26,26,57]
def h22Neg : List Nat := [24,40,25,18,48,3,10,3,33,33,9,3,10,18,42,33,2,17,2,9,17,34,42,16,50,8,56,25,25,8,32,42,50,1,1,50,56,25,56,42,1,1,25,42,56,56,1,50,25,25,42,2,2,0,33]
def h22Mask : Nat := fullMask 55
def h22Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x4f7737f97fffb2,0x434726181a8fa4),(0xcccccccccccccccccccccccccccccccc,0x3c89efffe7bced,0x1c8889816578e8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x76dcfab689556f,0x73cf0be485447),(0xffff0000ffff0000ffff0000ffff0000,0x71beed0e9622dd,0x3b4791d92201d),(0xffffffff00000000ffffffff00000000,0x4b7799c578cb12,0x44b8d9c560c312)]
def h22Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(0,1,27),(2,2,3),(3,2,3),(1,2,5),(3,2,5),(1,2,17),(1,2,28),(1,3,5),(3,3,5),(1,3,17),(1,3,28),(1,5,17),(0,5,28),(1,17,28),(2,1,27),(3,1,27),(2,1,40),(1,17,40),(3,5,27),(1,17,27),(3,17,27),(0,1,31),(0,1,35),(2,0,17),(1,5,51),(3,0,4),(2,0,20),(0,1,4),(1,1,4),(2,1,4),(3,1,4),(2,1,54),(0,2,4),(3,2,4),(1,2,54),(0,3,4),(3,3,4),(1,3,20),(2,3,20),(1,5,20),(2,0,24),(2,1,68),(1,3,68),(1,2,24),(2,2,24),(1,5,24),(0,0,27),(1,2,74),(1,3,74),(2,0,27),(2,0,28),(1,4,28),(2,4,28),(0,4,27),(0,0,31),(0,0,35),(0,2,6),(3,2,6),(0,3,6),(3,3,6),(0,4,6),(1,7,51),(3,7,27),(3,1,62),(3,1,70),(2,4,8),(0,1,76),(0,4,76),(3,4,76),(1,4,94),(2,4,94),(2,76,94),(2,3,9),(1,9,20),(3,2,23),(2,0,102),(3,9,23),(0,0,71),(0,1,71),(3,3,71),(1,9,24),(1,2,55),(0,2,76),(1,3,55),(1,9,55),(0,0,112),(1,2,58),(0,0,114),(1,3,58),(1,9,58),(3,2,56),(3,3,56),(2,0,64),(1,2,64),(0,0,121),(1,9,64),(0,56,76),(1,2,99),(1,2,95),(0,4,49),(1,4,49),(2,4,49),(3,4,49),(0,3,10),(3,3,10),(0,4,10),(2,10,55),(2,10,58),(3,3,128),(2,1,77),(2,4,12),(1,12,55),(1,12,58),(2,2,13),(2,0,107),(3,13,19),(0,0,65),(0,1,65),(1,13,20),(0,1,75),(0,4,75),(3,4,75),(1,4,147),(2,4,147),(2,75,147),(1,13,24),(1,13,55),(0,0,154),(0,0,116),(1,13,58),(2,0,61),(1,3,61),(0,0,159),(1,13,61),(0,56,75),(1,3,152),(1,3,148),(0,4,50),(1,4,50),(2,4,50),(3,4,50),(3,2,14),(0,4,14),(2,14,55),(2,14,58),(3,2,166),(2,56,110),(2,4,16),(1,16,55),(1,16,58),(2,0,42),(3,3,33),(3,2,37),(0,1,41),(2,19,51),(3,2,182),(1,20,51),(1,27,51),(2,27,51),(1,3,183),(2,23,51),(3,3,188),(1,24,51),(1,2,189),(1,28,51),(2,4,18),(2,4,22),(3,18,27),(3,22,27),(1,20,24),(1,20,29),(2,3,21),(1,24,30),(2,2,25),(3,26,27),(1,26,55),(2,27,55),(1,29,55),(1,30,55),(1,26,58),(2,27,58),(1,29,58),(1,30,58),(0,27,197),(2,27,197),(2,1,211)]
def h22W : BT Decor := buildWiresBT 8 h22Base h22Steps
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
def h22SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 8,4),some (subcubeFast 0 16,4),some (subcubeFast 0 32,6),some (subcubeFast 8 0,5),some (subcubeFast 8 1,4),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4),some (subcubeFast 32 0,5),some (subcubeFast 32 2,4)]
def h22Slices : BT (Option (Nat × Nat)) := btOfList 4 h22SliceList
def h22Specs : List PoolSpec := [(0,[]),(1,[]),(6,[]),(8,[]),(1,[(0,0,4)]),(10,[]),(9,[(0,0,1)]),(4,[]),(4,[(0,0,1)]),(5,[(0,0,4)]),(7,[(0,0,4)]),(9,[]),(5,[(0,0,1)]),(2,[]),(5,[]),(7,[(0,0,1)]),(3,[]),(7,[]),(4,[(0,0,1),(1,2,5)]),(4,[(0,0,1),(1,3,5)]),(4,[(1,0,1)]),(4,[(1,0,1),(0,2,6)]),(4,[(1,0,1),(3,2,6)]),(4,[(1,0,1),(0,3,6)]),(4,[(1,0,1),(3,3,6)]),(4,[(2,0,1)]),(5,[(2,0,20)]),(7,[(2,0,24)]),(9,[(3,0,1)]),(4,[(3,0,1)]),(1,[(2,4,8)]),(4,[(0,0,2)]),(0,[(1,2,3)]),(7,[(0,0,27)]),(7,[(0,0,2)]),(9,[(2,1,2)]),(0,[(2,3,9)]),(4,[(0,0,2),(2,3,9)]),(4,[(1,0,2)]),(5,[(0,3,10)]),(4,[(1,0,2),(0,3,10)]),(4,[(1,0,2),(3,3,10)]),(5,[(3,3,10)]),(5,[(0,4,10)]),(4,[(2,0,2)]),(7,[(2,0,2)]),(5,[(2,0,27)]),(7,[(2,0,27)]),(4,[(3,0,2)]),(4,[(0,0,3)]),(5,[(0,0,27)]),(5,[(0,0,3)]),(9,[(2,1,3)]),(0,[(2,2,13)]),(4,[(0,0,3),(2,2,13)]),(4,[(1,0,3)]),(4,[(1,0,3),(3,2,14)]),(7,[(3,2,14)]),(7,[(0,4,14)]),(4,[(2,0,3)]),(5,[(2,0,3)]),(4,[(3,0,3)]),(4,[(2,1,2)]),(7,[(0,0,4),(0,0,27)]),(4,[(2,1,3)]),(5,[(0,0,4),(0,0,27)]),(4,[(1,2,3)]),(4,[(1,2,17)]),(4,[(1,3,17)]),(4,[(1,1,2)]),(4,[(1,1,3)]),(4,[(0,1,2)]),(4,[(0,1,3)]),(4,[(2,1,3),(1,2,24)]),(9,[(0,1,2)]),(1,[(2,4,18)]),(4,[(2,1,2),(1,3,20)]),(0,[(2,2,3)]),(4,[(3,1,2)]),(4,[(3,1,2),(2,3,21)]),(9,[(0,1,3)]),(1,[(2,4,22)]),(0,[(3,2,3)]),(4,[(3,1,3)]),(4,[(3,1,3),(2,2,25)]),(4,[(1,2,55)]),(1,[(1,2,55)]),(4,[(1,3,55)]),(1,[(1,3,55)]),(4,[(1,2,58)]),(4,[(1,3,58)]),(4,[(0,2,3)]),(4,[(0,2,3),(1,2,3)]),(4,[(2,2,3)]),(4,[(3,2,3)]),(4,[(2,0,61)]),(5,[(2,0,61)]),(4,[(1,3,61)]),(4,[(2,0,64)]),(7,[(2,0,64)]),(4,[(1,2,64)])]
def h22Pools : BT (Option BoundPool) := buildPoolsBT 7 h22W h22R h22Slices h22Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice10 : Slice h22R h22G (subcubeFast 32 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice9 : Slice h22R h22G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice8 : Slice h22R h22G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice7 : Slice h22R h22G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice6 : Slice h22R h22G (subcubeFast 8 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice5 : Slice h22R h22G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice4 : Slice h22R h22G (subcubeFast 0 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice3 : Slice h22R h22G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice2 : Slice h22R h22G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice1 : Slice h22R h22G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice0 : Slice h22R h22G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h22R h22G p.1 p.2) h22Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h22R h22G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h22Slice0) (forall_cons (fun _ h => by cases h; exact h22Slice1) (forall_cons (fun _ h => by cases h; exact h22Slice2) (forall_cons (fun _ h => by cases h; exact h22Slice3) (forall_cons (fun _ h => by cases h; exact h22Slice4) (forall_cons (fun _ h => by cases h; exact h22Slice5) (forall_cons (fun _ h => by cases h; exact h22Slice6) (forall_cons (fun _ h => by cases h; exact h22Slice7) (forall_cons (fun _ h => by cases h; exact h22Slice8) (forall_cons (fun _ h => by cases h; exact h22Slice9) (forall_cons (fun _ h => by cases h; exact h22Slice10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h22R h22G c) h22Pools := buildPoolsBT_sound h22SlicesOk
def h22Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G (3 - 1) xs.toFinset) h22Empty := trivial
def h22Block3_0 : List NodeSpec := [([1,2,45,76],[],[0]),([1,3,45,75],[],[0])]
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
def h22Block4_0 : List NodeSpec := [([2,3,5,17,28],[],[0]),([1,2,3,17,40],[7],[0]),([1,2,3,17,46],[],[0]),([0,4,20,76,94],[],[0]),([0,4,20,76,99],[],[0]),([0,1,4,76,114],[],[0]),([2,3,4,39,59],[],[0]),([1,2,4,39,76],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Block4_0 = true := by decide +kernel
def h22Block4_1 : List NodeSpec := [([0,1,4,76,118],[],[0]),([0,1,2,4,124],[],[0]),([0,1,2,76,97],[],[0]),([0,1,2,76,98],[],[0]),([2,3,4,39,49],[],[0]),([0,2,4,49,136],[],[0]),([0,2,4,49,119],[],[0]),([0,4,24,75,147],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_1 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Block4_1 = true := by decide +kernel
def h22Block4_2 : List NodeSpec := [([0,4,24,75,152],[],[0]),([0,1,4,75,116],[],[0]),([2,3,4,39,69],[],[0]),([1,3,4,39,75],[],[0]),([0,1,4,75,119],[],[0]),([0,1,3,4,162],[],[0]),([0,1,3,75,150],[],[0]),([0,1,3,75,151],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_2 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Block4_2 = true := by decide +kernel
def h22Block4_3 : List NodeSpec := [([2,3,4,39,50],[],[0]),([0,3,4,50,173],[],[0]),([0,3,4,50,118],[],[0]),([1,3,4,39,110],[],[0]),([0,1,3,4,174],[],[0]),([1,3,17,20,74],[63],[0]),([1,2,3,17,178],[],[0]),([1,2,17,24,74],[65],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_3 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Block4_3 = true := by decide +kernel
def h22Block4_4 : List NodeSpec := [([1,2,3,17,44],[],[0]),([1,3,17,33,74],[63],[0]),([1,2,17,37,74],[65],[0]),([0,1,2,3,41],[7],[0]),([0,2,3,17,181],[],[0]),([0,1,2,51,187],[],[0]),([0,1,3,51,191],[],[0]),([0,1,2,3,192],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_4 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Block4_4 = true := by decide +kernel
def h22Block4_5 : List NodeSpec := [([0,1,4,26,204],[],[0]),([0,1,4,27,207],[],[0]),([0,4,27,28,197],[],[0]),([0,4,27,43,197],[],[0]),([0,1,4,27,211],[],[0]),([0,1,4,27,212],[],[0]),([0,1,26,27,80],[],[0]),([0,1,4,27,213],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_5 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Block4_5 = true := by decide +kernel
def h22Block4_6 : List NodeSpec := [([1,2,3,28,45],[],[0]),([2,3,4,39,145],[],[0]),([2,3,4,39,106],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_6 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Block4_6 = true := by decide +kernel
def h22Nodes4 : List NodeSpec := h22Block4_0 ++ h22Block4_1 ++ h22Block4_2 ++ h22Block4_3 ++ h22Block4_4 ++ h22Block4_5 ++ h22Block4_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check4 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Nodes4 = true := by
  unfold h22Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h22Test4_0,h22Test4_1⟩,h22Test4_2⟩,h22Test4_3⟩,h22Test4_4⟩,h22Test4_5⟩,h22Test4_6⟩
def h22Bucket4 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 4 xs.toFinset) h22Bucket4 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket3Ok h22Check4
def h22Block5_0 : List NodeSpec := [([1,2,3,5,17,27],[2,3,4],[0]),([1,2,3,5,17,31],[0,2,4],[0]),([1,2,3,5,17,32],[2],[0]),([1,2,3,5,17,35],[0,3,4],[0]),([1,2,3,5,17,36],[3],[0]),([0,1,2,3,51,52],[8],[0]),([1,2,3,4,5,54],[7],[0]),([1,2,3,4,5,68],[7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_0 = true := by decide +kernel
def h22Block5_1 : List NodeSpec := [([1,2,3,4,5,74],[1,2,3],[0]),([0,2,3,4,5,28],[0,13,16],[0]),([0,1,2,3,4,40],[7,11,14,17],[0]),([0,1,2,3,4,46],[],[0]),([0,1,2,3,51,89],[25],[0]),([0,2,3,4,7,28],[],[0]),([0,1,2,3,4,90],[7,11],[0]),([0,1,4,20,76],[2,3,14,32,33],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_1 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_1 = true := by decide +kernel
def h22Block5_2 : List NodeSpec := [([0,1,3,4,20,76],[3,33],[0]),([0,1,3,4,20,101],[],[0]),([1,2,3,4,9,83],[1],[0]),([0,1,3,4,9,102],[16],[0]),([0,1,2,3,4,104],[14],[0]),([0,1,3,4,9,71],[16],[0]),([0,1,2,3,4,108],[14],[0]),([0,1,2,4,55,76],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_2 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_2 = true := by decide +kernel
def h22Block5_3 : List NodeSpec := [([0,1,2,4,55,100],[],[0]),([0,1,2,3,4,112],[],[0]),([0,1,3,4,9,114],[],[0]),([0,1,2,4,58,76],[14],[0]),([0,1,2,4,58,100],[],[0]),([0,1,2,3,4,117],[],[0]),([0,2,3,4,56,59],[14],[0]),([0,2,3,4,57,59],[14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_3 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_3 = true := by decide +kernel
def h22Block5_4 : List NodeSpec := [([0,1,3,4,9,121],[16],[0]),([0,1,2,3,4,123],[14],[0]),([0,1,2,4,56,76],[14,16,32],[0]),([0,1,2,4,57,76],[],[0]),([0,1,2,4,76,94],[14,16,33],[0]),([0,1,2,4,76,99],[3,14],[0]),([0,1,2,4,76,95],[],[0]),([0,1,2,4,76,96],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_4 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_4 = true := by decide +kernel
def h22Block5_5 : List NodeSpec := [([0,1,2,3,4,94],[7,11,14,16],[0]),([0,2,3,4,49,55],[7,12,13],[0]),([0,1,2,4,55,131],[13,39],[0]),([0,1,2,4,55,132],[],[0]),([0,1,2,3,4,134],[0,7],[0]),([0,2,3,4,49,58],[],[0]),([0,1,2,4,58,131],[],[0]),([0,1,2,4,58,132],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_5 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_5 = true := by decide +kernel
def h22Block5_6 : List NodeSpec := [([0,1,2,3,4,135],[0,7],[0]),([0,2,3,4,49,127],[12,13],[0]),([0,2,3,4,49,128],[0,3,12,13],[0]),([0,2,3,4,49,129],[],[0]),([0,2,3,4,49,130],[],[0]),([0,2,3,4,49,56],[0,3,12,13],[0]),([0,2,3,4,49,57],[0],[0]),([0,1,2,3,4,137],[7,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_6 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_6 = true := by decide +kernel
def h22Block5_7 : List NodeSpec := [([0,1,3,4,12,109],[11],[0]),([0,1,2,3,4,139],[7],[0]),([0,1,2,3,4,140],[7],[0]),([1,2,3,4,13,82],[1],[0]),([0,1,2,4,13,107],[13],[0]),([0,1,2,3,4,143],[14],[0]),([0,1,2,4,13,65],[13],[0]),([0,1,2,3,4,146],[14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_7 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_7 = true := by decide +kernel
def h22Block5_8 : List NodeSpec := [([0,1,4,24,75],[2,3,17,32,50],[0]),([0,1,2,4,24,75],[2,50],[0]),([0,1,2,4,24,153],[],[0]),([0,1,3,4,55,75],[],[0]),([0,1,3,4,55,141],[],[0]),([0,1,2,3,4,154],[],[0]),([0,1,3,4,58,75],[17],[0]),([0,1,3,4,58,141],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_8 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_8 = true := by decide +kernel
def h22Block5_9 : List NodeSpec := [([0,1,2,4,13,116],[],[0]),([0,1,2,3,4,157],[],[0]),([0,2,3,4,56,69],[17],[0]),([0,2,3,4,57,69],[17],[0]),([0,1,2,4,13,159],[13],[0]),([0,1,2,3,4,161],[14],[0]),([0,1,3,4,56,75],[13,17,32],[0]),([0,1,3,4,57,75],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_9 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_9 = true := by decide +kernel
def h22Block5_10 : List NodeSpec := [([0,1,3,4,75,147],[13,17,50],[0]),([0,1,3,4,75,152],[2,17],[0]),([0,1,3,4,75,148],[],[0]),([0,1,3,4,75,149],[],[0]),([0,1,2,3,4,147],[7,11,13,17],[0]),([0,2,3,4,50,55],[7,15,16],[0]),([0,1,3,4,55,110],[16,33],[0]),([0,1,3,4,55,169],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_10 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_10 = true := by decide +kernel
def h22Block5_11 : List NodeSpec := [([0,1,2,3,4,171],[0,7],[0]),([0,2,3,4,50,58],[],[0]),([0,1,3,4,58,110],[],[0]),([0,1,3,4,58,169],[],[0]),([0,1,2,3,4,172],[0,7],[0]),([0,2,3,4,50,165],[15,16],[0]),([0,2,3,4,50,166],[0,2,15,16],[0]),([0,2,3,4,50,167],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_11 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_11 = true := by decide +kernel
def h22Block5_12 : List NodeSpec := [([0,2,3,4,50,168],[],[0]),([0,2,3,4,50,56],[0,2,15,16],[0]),([0,2,3,4,50,57],[0],[0]),([0,1,3,4,56,110],[0,14,16,33],[0]),([0,1,3,4,57,110],[],[0]),([0,1,2,4,16,111],[11],[0]),([0,1,2,3,4,176],[7],[0]),([0,1,2,3,4,177],[7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_12 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_12 = true := by decide +kernel
def h22Block5_13 : List NodeSpec := [([0,1,3,17,20,27],[4,10],[0]),([0,1,2,3,17,65],[],[0]),([0,1,2,3,17,42],[0],[0]),([0,1,2,17,24,27],[4,9],[0]),([0,1,2,3,17,71],[],[0]),([1,2,3,17,74],[2,3,7,32,63,65],[0]),([1,2,3,17,27,74],[0,2,63,65],[0]),([0,1,2,3,17,28],[0,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_13 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_13 = true := by decide +kernel
def h22Block5_14 : List NodeSpec := [([0,1,3,17,27,33],[10,11],[0]),([0,1,2,17,27,37],[9,11],[0]),([0,1,2,3,17,47],[0,4,7],[0]),([0,1,2,3,17,48],[0,7],[0]),([0,1,2,3,17,179],[],[0]),([0,1,2,3,17,180],[],[0]),([1,2,3,4,17,74],[2,7],[0]),([0,1,2,3,4,48],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_14 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_14 = true := by decide +kernel
def h22Block5_15 : List NodeSpec := [([0,1,2,3,51,107],[],[0]),([0,1,2,3,51,182],[69],[0]),([0,1,3,20,27,51],[3],[0]),([0,1,2,3,51,65],[],[0]),([0,1,2,3,42,51],[],[0]),([0,1,2,3,51,184],[],[0]),([0,1,2,3,51,183],[3],[0]),([0,1,2,3,51,102],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_15 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_15 = true := by decide +kernel
def h22Block5_16 : List NodeSpec := [([0,1,2,3,51,188],[70],[0]),([0,1,2,24,27,51],[2],[0]),([0,1,2,3,51,71],[],[0]),([0,1,2,3,51,190],[],[0]),([0,1,2,3,51,189],[2],[0]),([0,1,2,3,28,51],[7],[0]),([0,1,2,3,51,185],[],[0]),([0,1,2,3,51,186],[66],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_16 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_16 = true := by decide +kernel
def h22Block5_17 : List NodeSpec := [([0,1,4,18,22,27],[1,14],[0]),([0,1,3,4,18,34],[],[0]),([0,1,2,4,22,38],[],[0]),([0,1,2,3,4,28],[7,11],[0]),([0,1,4,18,24,27],[1,14],[0]),([0,1,3,4,18,71],[73],[0]),([0,1,3,4,27,195],[14],[0]),([0,1,2,3,4,142],[14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_17 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_17 = true := by decide +kernel
def h22Block5_18 : List NodeSpec := [([0,1,4,20,22,27],[1,14],[0]),([0,1,2,4,22,65],[76],[0]),([0,1,4,20,24,27],[1,14],[0]),([0,1,3,4,20,74],[14,33],[0]),([0,1,3,4,20,198],[14],[0]),([0,1,2,3,4,144],[14],[0]),([0,1,2,3,4,178],[],[0]),([0,1,2,4,27,196],[14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_18 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_18 = true := by decide +kernel
def h22Block5_19 : List NodeSpec := [([0,1,2,3,4,103],[14],[0]),([0,1,2,4,24,74],[17,50],[0]),([0,1,2,4,24,200],[17],[0]),([0,1,2,3,4,105],[14],[0]),([0,1,4,26,27,55],[13],[0]),([0,1,3,4,26,109],[13],[0]),([0,1,2,4,26,111],[13],[0]),([0,1,2,3,4,203],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_19 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_19 = true := by decide +kernel
def h22Block5_20 : List NodeSpec := [([0,2,3,4,28,55],[7],[0]),([0,1,2,3,4,204],[],[0]),([0,1,2,3,4,205],[],[0]),([0,1,2,3,4,206],[],[0]),([0,1,2,3,4,113],[11,16,17],[0]),([0,1,2,3,4,155],[11,13,14],[0]),([0,1,4,26,27,58],[14],[0]),([0,1,2,3,4,207],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_20 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_20 = true := by decide +kernel
def h22Block5_21 : List NodeSpec := [([0,2,3,4,28,58],[7],[0]),([0,1,2,3,4,208],[11],[0]),([0,1,3,4,29,114],[],[0]),([0,1,2,3,4,209],[],[0]),([0,1,2,4,30,116],[],[0]),([0,1,2,3,4,210],[],[0]),([0,1,2,3,4,115],[],[0]),([0,1,2,3,4,156],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_21 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_21 = true := by decide +kernel
def h22Block5_22 : List NodeSpec := [([0,1,4,27,197],[2,14,32],[0]),([0,1,4,26,27,28],[13,14,92],[0]),([0,1,4,26,27,43],[14],[0]),([0,1,4,26,27,81],[92],[0]),([0,1,4,27,202],[2,14,32],[0]),([0,1,2,3,4,44],[],[0]),([0,1,2,3,4,78],[7,11],[0]),([0,1,2,3,28,79],[11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_22 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_22 = true := by decide +kernel
def h22Block5_23 : List NodeSpec := [([0,1,2,3,28,80],[7],[0]),([0,1,2,3,27,80],[],[0]),([0,2,3,4,56,145],[14,16],[0]),([0,2,3,4,57,145],[14],[0]),([0,2,3,4,56,106],[13,17],[0]),([0,2,3,4,57,106],[17],[0]),([0,1,2,3,4,160],[14],[0]),([0,1,2,3,4,122],[14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_23 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_23 = true := by decide +kernel
def h22Nodes5 : List NodeSpec := h22Block5_0 ++ h22Block5_1 ++ h22Block5_2 ++ h22Block5_3 ++ h22Block5_4 ++ h22Block5_5 ++ h22Block5_6 ++ h22Block5_7 ++ h22Block5_8 ++ h22Block5_9 ++ h22Block5_10 ++ h22Block5_11 ++ h22Block5_12 ++ h22Block5_13 ++ h22Block5_14 ++ h22Block5_15 ++ h22Block5_16 ++ h22Block5_17 ++ h22Block5_18 ++ h22Block5_19 ++ h22Block5_20 ++ h22Block5_21 ++ h22Block5_22 ++ h22Block5_23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check5 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Nodes5 = true := by
  unfold h22Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h22Test5_0,h22Test5_1⟩,h22Test5_2⟩,h22Test5_3⟩,h22Test5_4⟩,h22Test5_5⟩,h22Test5_6⟩,h22Test5_7⟩,h22Test5_8⟩,h22Test5_9⟩,h22Test5_10⟩,h22Test5_11⟩,h22Test5_12⟩,h22Test5_13⟩,h22Test5_14⟩,h22Test5_15⟩,h22Test5_16⟩,h22Test5_17⟩,h22Test5_18⟩,h22Test5_19⟩,h22Test5_20⟩,h22Test5_21⟩,h22Test5_22⟩,h22Test5_23⟩
def h22Bucket5 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 5 xs.toFinset) h22Bucket5 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket4Ok h22Check5
def h22Block6_0 : List NodeSpec := [([1,2,3,5,17],[0,2,3,4,5,6,7,8],[0]),([0,1,2,3,5,17],[0,2,3,4,5,7,8,9,10,11],[0]),([0,1,2,3,5,51],[0,2,3,5,7,8,11],[0]),([0,1,2,3,4,5,20],[0,5,12,13,14],[0]),([0,1,2,3,4,5,24],[0,5,15,16,17],[0]),([0,1,2,3,4,5,27],[0,1,2,3,13,14,16,17],[0]),([0,1,2,3,4,31],[0,1,2,7,11,12,13,16,17,18],[0]),([0,1,2,3,4,5,31],[0,1,2,13,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_0 = true := by decide +kernel
def h22Block6_1 : List NodeSpec := [([0,1,2,3,4,32],[2,7,11,12,13,16,17],[0]),([0,1,2,3,4,5,32],[2,13,14],[0]),([0,1,2,3,4,35],[0,1,3,7,11,13,14,15,16,19],[0]),([0,1,2,3,4,5,35],[0,1,3,16,17],[0]),([0,1,2,3,4,36],[3,7,11,13,14,15,16],[0]),([0,1,2,3,4,5,36],[3,16,17],[0]),([0,1,3,4,84],[0,1,3,14,21],[0]),([0,1,3,4,85],[0,1,2,3,13,22],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_1 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_1 = true := by decide +kernel
def h22Block6_2 : List NodeSpec := [([0,1,2,4,86],[0,1,2,17,23],[0]),([0,1,2,4,87],[0,1,2,3,16,24],[0]),([0,1,2,3,88],[0,1,2,7,11,20],[0]),([0,1,2,3,7,51],[0,2,3,5,7,11,25],[0]),([0,1,2,3,4,5],[0,1,5,7,8,11,12,13,14,15,16,17],[0]),([0,1,2,3,4,7,27],[1,2,3,13,14,16,17],[0]),([0,1,2,3,4,62],[0,1,2,7,11,13,16,17,26],[0]),([0,1,2,3,4,70],[0,1,3,7,11,13,14,16,27],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_2 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_2 = true := by decide +kernel
def h22Block6_3 : List NodeSpec := [([1,2,3,8,17],[0,2,3,4,5,28],[0]),([0,1,2,3,93],[0,2,3,7,11,29,30],[0]),([0,1,3,4,9,20],[0,1,2,13,14,34,35],[0]),([0,1,2,3,4,9,23],[0,1,14,16,17],[0]),([0,1,2,3,4,9,24],[3,14,16,17],[0]),([0,1,2,3,4,9,55],[11,14],[0]),([0,1,2,3,4,9,58],[1,7,11,14],[0]),([0,1,2,3,4,59],[0,1,2,7,11,13,14,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_3 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_3 = true := by decide +kernel
def h22Block6_4 : List NodeSpec := [([0,1,2,3,4,9,64],[11,14,16,17],[0]),([0,1,2,4,76],[2,3,14,16,32],[0]),([0,1,2,3,4,76],[0,1,2,3,7,11,13,14,16,32,33],[0]),([0,1,2,4,100],[2,14,17,36,37],[0]),([0,1,2,3,4,10,55],[0,1,7,11,13,14],[0]),([0,1,2,3,4,10,58],[0,1,7,11],[0]),([0,2,3,4,49],[0,2,3,12,13],[0]),([0,1,2,3,4,49],[0,1,2,3,7,11,12,13,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_4 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_4 = true := by decide +kernel
def h22Block6_5 : List NodeSpec := [([0,2,3,4,91],[0,1,3,13,26],[0]),([0,1,2,4,131],[0,13,17,39,40],[0]),([0,1,2,4,132],[0,3,13,16,41,42],[0]),([0,1,2,3,133],[0,3,7,11,13,38,43],[0]),([0,1,3,4,11,20],[0,1,2,13,14,35,45],[0]),([0,1,2,3,4,11,23],[1,2,13,14],[0]),([0,1,2,3,4,11,24],[2,3,13,14,16,17],[0]),([0,1,2,3,4,11,55],[2,11,13],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_5 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_5 = true := by decide +kernel
def h22Block6_6 : List NodeSpec := [([0,1,2,3,4,11,58],[1,2,7,11,13,14],[0]),([0,1,2,3,4,11,64],[2,11,13,14],[0]),([0,1,2,3,4,77],[1,2,3,7,11,13,16,32,46,47],[0]),([0,1,2,3,4,12,55],[0,7,11,14],[0]),([0,1,2,3,4,12,58],[0,1,7,11],[0]),([0,1,2,3,4,67],[0,1,3,7,11,14,16,17],[0]),([0,1,2,3,138],[0,3,7,11,14,48],[0]),([0,1,2,3,4,13,19],[0,1,13,14,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_6 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_6 = true := by decide +kernel
def h22Block6_7 : List NodeSpec := [([0,1,2,3,4,13,20],[2,13,14,17],[0]),([0,1,2,4,13,24],[0,1,3,16,17,51,52],[0]),([0,1,2,3,4,13,55],[11,17],[0]),([0,1,2,3,4,13,58],[1,7,11,17],[0]),([0,1,2,3,4,69],[0,1,3,7,11,13,14,16,17],[0]),([0,1,2,3,4,13,61],[11,13,14,17],[0]),([0,1,3,4,75],[2,3,13,17,32],[0]),([0,1,2,3,4,75],[0,1,2,7,11,13,14,17,32,50],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_7 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_7 = true := by decide +kernel
def h22Block6_8 : List NodeSpec := [([0,1,3,4,141],[2,14,17,53,54],[0]),([0,1,2,3,4,14,55],[0,1,7,11,16,17],[0]),([0,1,2,3,4,14,58],[0,1,7,11],[0]),([0,2,3,4,50],[0,2,15,16],[0]),([0,1,2,3,4,50],[0,1,2,7,11,13,14,15,16],[0]),([0,2,3,4,92],[0,1,2,16,27],[0]),([0,1,3,4,110],[0,14,16,33],[0]),([0,1,3,4,169],[0,2,13,16,56,57],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_8 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_8 = true := by decide +kernel
def h22Block6_9 : List NodeSpec := [([0,1,2,3,170],[0,2,7,11,16,55,58],[0]),([0,1,2,3,4,15,19],[1,3,16,17],[0]),([0,1,2,3,4,15,20],[2,3,13,14,16,17],[0]),([0,1,2,4,15,24],[0,1,3,16,17,52,60],[0]),([0,1,2,3,4,15,55],[3,11,16],[0]),([0,1,2,3,4,15,58],[1,3,7,11,16,17],[0]),([0,1,2,3,4,15,61],[3,11,16,17],[0]),([0,1,2,3,4,16,55],[0,7,11,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_9 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_9 = true := by decide +kernel
def h22Block6_10 : List NodeSpec := [([0,1,2,3,4,16,58],[0,1,7,11],[0]),([0,1,2,3,4,73],[0,1,2,7,11,13,14,17],[0]),([0,1,2,3,175],[0,2,7,11,17,61],[0]),([0,1,2,3,17,20],[0,2,4,5,9,10,11,35,62],[0]),([0,1,2,3,17,24],[0,3,4,5,9,10,11,52,64],[0]),([0,1,2,3,17,27],[0,2,3,4,9,10,11,32,66],[0]),([0,1,2,3,17,33],[0,2,4,5,7,9,10,11,67],[0]),([0,1,2,3,17,37],[0,3,4,5,7,9,10,11,68],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_10 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_10 = true := by decide +kernel
def h22Block6_11 : List NodeSpec := [([0,1,2,3,4,17,27],[0,2,7,11,13,14,16,17,66],[0]),([0,1,2,3,4,33],[0,1,2,5,7,9,11,13,16,17,67],[0]),([0,1,2,3,4,37],[0,1,3,5,7,10,11,13,14,16,68],[0]),([0,1,2,3,17],[0,2,3,4,5,7,9,10,11],[0]),([0,1,2,3,19,51],[0,2,3,5,7,69],[0]),([0,1,2,3,20,51],[0,2,3,5,7,62],[0]),([0,1,2,3,23,51],[0,2,3,5,7,70],[0]),([0,1,2,3,24,51],[0,2,3,5,7,64],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_11 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_11 = true := by decide +kernel
def h22Block6_12 : List NodeSpec := [([0,1,2,3,27,51],[0,2,3,5,7,32,66],[0]),([0,1,2,3,4,18,22],[1,5,14,17,71,72],[0]),([0,1,2,3,4,18,24],[5,13,14,16,17,64],[0]),([0,1,2,3,4,20],[0,1,2,7,11,13,14,16,17,62],[0]),([0,1,3,4,18,27],[1,2,13,14,17,32,74],[0]),([0,1,2,3,4,38],[0,1,2,7,11,13,14,16],[0]),([0,1,2,3,193],[2,5,11,14,71,75],[0]),([0,1,2,3,4,82],[0,1,2,5,7,11,12,13,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_12 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_12 = true := by decide +kernel
def h22Block6_13 : List NodeSpec := [([0,1,2,3,4,107],[0,1,5,7,11,13,14,16],[0]),([0,1,2,3,4,54],[0,1,2,7,11,13,14,16,17,26],[0]),([0,1,2,3,4,20,54],[0,1,13,14,26],[0]),([0,1,2,3,4,20,22],[5,13,14,17,62],[0]),([0,1,2,3,4,20,24],[13,14,16,17],[0]),([0,1,3,4,20,27],[1,2,13,14,17,32,35],[0]),([0,1,3,4,20,29],[1,2,13,14,17,35,77],[0]),([0,1,2,3,4,65],[0,1,7,11,13,14,16,76],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_13 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_13 = true := by decide +kernel
def h22Block6_14 : List NodeSpec := [([0,1,2,3,4,20,65],[1,13,14,17],[0]),([0,1,2,3,4,20,66],[1,13,14,16,17],[0]),([0,1,2,3,4,42],[0,7,11,13,16],[0]),([0,1,2,4,163],[1,2,5,14,16],[0]),([0,1,2,3,4,163],[0,1,2,5,7,11,14,16],[0]),([0,1,2,4,199],[1,2,14,17,79],[0]),([0,1,2,3,4,24],[0,1,3,7,11,13,14,16,17,64],[0]),([0,1,2,4,22,27],[1,3,14,16,17,32,80],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_14 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_14 = true := by decide +kernel
def h22Block6_15 : List NodeSpec := [([0,1,2,3,4,34],[0,1,3,7,11,13,14,17],[0]),([0,1,2,3,194],[3,5,11,17,72,81],[0]),([0,1,2,3,4,83],[0,1,3,5,7,11,13,14,15,16],[0]),([0,1,2,3,4,102],[0,1,5,7,11,13,14,16],[0]),([0,1,2,3,4,68],[0,1,3,7,11,13,14,16,17,27],[0]),([0,1,2,3,4,24,68],[0,1,16,17,27],[0]),([0,1,2,4,24,27],[1,3,14,16,17,32,52],[0]),([0,1,2,4,24,30],[1,3,14,16,17,52,82],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_15 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_15 = true := by decide +kernel
def h22Block6_16 : List NodeSpec := [([0,1,2,3,4,71],[0,1,7,11,13,14,16,17,73],[0]),([0,1,2,3,4,24,71],[1,13,14,16,17],[0]),([0,1,2,3,4,24,72],[1,13,14,16,17],[0]),([0,1,3,4,125],[1,3,5,13,17],[0]),([0,1,2,3,4,125],[0,1,3,5,7,11,13,14,17],[0]),([0,1,3,4,201],[1,2,14,17,84],[0]),([0,1,2,3,4,89],[0,1,5,7,11,13,14,16,17,25],[0]),([0,1,2,3,4,26,55],[11,14,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_16 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_16 = true := by decide +kernel
def h22Block6_17 : List NodeSpec := [([0,1,2,3,4,27,55],[1,7,11,13],[0]),([0,1,2,3,4,29,55],[11,14,16,17],[0]),([0,1,2,3,4,30,55],[11,13,14,17],[0]),([0,1,2,3,4,109],[0,1,5,7,11,13,16,17,85,86],[0]),([0,1,2,3,4,111],[0,1,5,7,11,13,14,16,87,88],[0]),([0,1,2,3,4,52],[0,1,7,8,11,13,14,16,17],[0]),([0,1,2,3,4,26,58],[1,7,11,14],[0]),([0,1,2,3,4,27,58],[1,7,11,13,14,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_17 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_17 = true := by decide +kernel
def h22Block6_18 : List NodeSpec := [([0,1,2,3,4,29,58],[1,7,11,14],[0]),([0,1,2,3,4,30,58],[1,7,11,17],[0]),([0,1,2,3,4,114],[0,1,7,11,13,16,17,89],[0]),([0,1,2,3,4,116],[0,1,7,11,13,14,16,90],[0]),([0,1,2,3,4,197],[0,1,2,7,11,14,17],[0]),([0,1,4,26,27],[2,13,14,32,92],[0]),([0,1,2,3,4,74],[0,1,2,3,7,11,13,14,16,17,32,33,50],[0]),([0,1,2,3,4,27,74],[0,2,13,14,16,17,32,33,50],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_18 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_18 = true := by decide +kernel
def h22Block6_19 : List NodeSpec := [([0,1,2,3,4,28],[0,1,7,11,13,14,16,17],[0]),([0,1,2,3,4,27,28],[1,13,14,16,17,66],[0]),([0,1,2,3,4,27,43],[1,13,14,16,17],[0]),([0,1,2,3,4,27,81],[7,11,66],[0]),([0,1,2,3,4,145],[0,1,2,7,11,13,14,16],[0]),([0,1,2,3,4,27],[0,1,2,7,11,13,14,16,17,32,66],[0]),([0,1,2,3,4,106],[0,1,3,7,11,13,14,17],[0]),([0,1,2,3,4,164],[0,1,2,5,7,11,14,16],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_19 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_19 = true := by decide +kernel
def h22Block6_20 : List NodeSpec := [([0,1,2,3,4,158],[0,1,2,5,7,11,13,14,16,17,95,96],[0]),([0,1,2,3,4,159],[0,1,5,7,11,13,14,16,97],[0]),([0,1,2,3,4,126],[0,1,3,5,7,11,13,14,17],[0]),([0,1,2,3,4,120],[0,1,3,5,7,11,13,14,16,17,98,99],[0]),([0,1,2,3,4,121],[0,1,5,7,11,13,14,16,17,100],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_20 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_20 = true := by decide +kernel
def h22Nodes6 : List NodeSpec := h22Block6_0 ++ h22Block6_1 ++ h22Block6_2 ++ h22Block6_3 ++ h22Block6_4 ++ h22Block6_5 ++ h22Block6_6 ++ h22Block6_7 ++ h22Block6_8 ++ h22Block6_9 ++ h22Block6_10 ++ h22Block6_11 ++ h22Block6_12 ++ h22Block6_13 ++ h22Block6_14 ++ h22Block6_15 ++ h22Block6_16 ++ h22Block6_17 ++ h22Block6_18 ++ h22Block6_19 ++ h22Block6_20
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check6 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Nodes6 = true := by
  unfold h22Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h22Test6_0,h22Test6_1⟩,h22Test6_2⟩,h22Test6_3⟩,h22Test6_4⟩,h22Test6_5⟩,h22Test6_6⟩,h22Test6_7⟩,h22Test6_8⟩,h22Test6_9⟩,h22Test6_10⟩,h22Test6_11⟩,h22Test6_12⟩,h22Test6_13⟩,h22Test6_14⟩,h22Test6_15⟩,h22Test6_16⟩,h22Test6_17⟩,h22Test6_18⟩,h22Test6_19⟩,h22Test6_20⟩
def h22Bucket6 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 6 xs.toFinset) h22Bucket6 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket5Ok h22Check6
def h22Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,5,7,8,11,14,17],[0]),([0,1,2,3,4,6],[0,1,2,3,7,11,14,17,20],[0]),([0,1,2,3,4,7],[0,1,2,3,5,7,11,14,17,25],[0]),([0,1,2,3,4,8],[0,1,2,3,5,7,11,14,17,29],[0]),([0,1,2,3,4,9],[0,1,2,3,7,11,14,17,31],[0]),([0,1,2,3,4,10],[0,1,2,3,7,11,13,14,17,38],[0]),([0,1,2,3,4,11],[0,1,2,3,7,11,13,14,17,44],[0]),([0,1,2,3,4,12],[0,1,3,7,11,14,17,48],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test7_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket6 7 h22Block7_0 = true := by decide +kernel
def h22Block7_1 : List NodeSpec := [([0,1,2,3,4,13],[0,1,2,3,7,11,14,17,49],[0]),([0,1,2,3,4,14],[0,1,2,3,7,11,14,16,17,55],[0]),([0,1,2,3,4,15],[0,1,2,3,7,11,14,16,17,59],[0]),([0,1,2,3,4,16],[0,1,2,7,11,14,17,61],[0]),([0,1,2,3,17],[0,2,3,5,7,11],[0]),([0,1,2,3,4,17],[0,1,2,3,5,7,11,14,17],[0]),([0,1,2,3,51],[0,2,3,7],[0]),([0,1,2,3,4,53],[0,1,2,3,5,7,14,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test7_1 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket6 7 h22Block7_1 = true := by decide +kernel
def h22Block7_2 : List NodeSpec := [([0,1,2,3,4,18],[0,1,2,5,7,11,14,17,71],[0]),([0,1,2,3,4,19],[0,1,2,5,7,11,13,14,17,69],[0]),([0,1,2,3,4,20],[0,1,2,5,7,11,13,14,17,62],[0]),([0,1,2,3,4,21],[0,1,2,5,7,11,14,17,78],[0]),([0,1,2,3,4,22],[0,1,3,5,7,11,14,17,72],[0]),([0,1,2,3,4,23],[0,1,3,5,7,11,14,16,17,70],[0]),([0,1,2,3,4,24],[0,1,3,5,7,11,14,16,17,64],[0]),([0,1,2,3,4,25],[0,1,3,5,7,11,14,17,83],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test7_2 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket6 7 h22Block7_2 = true := by decide +kernel
def h22Block7_3 : List NodeSpec := [([0,1,2,3,4,55],[0,1,5,7,11,14,17],[0]),([0,1,2,3,4,58],[0,1,7,11,14,17],[0]),([0,1,2,3,4,26],[0,1,2,7,11,14,17,91],[0]),([0,1,2,3,4,27],[0,1,2,3,7,11,13,14,16,17,66],[0]),([0,1,2,3,4,29],[0,1,2,7,11,14,16,17,93],[0]),([0,1,2,3,4,30],[0,1,2,3,7,11,13,14,17,94],[0]),([0,1,2,3,4,60],[0,1,2,5,7,11,14,17],[0]),([0,1,2,3,4,61],[0,1,2,5,7,11,13,14,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test7_3 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket6 7 h22Block7_3 = true := by decide +kernel
def h22Block7_4 : List NodeSpec := [([0,1,2,3,4,63],[0,1,3,5,7,11,14,17],[0]),([0,1,2,3,4,64],[0,1,3,5,7,11,14,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test7_4 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket6 7 h22Block7_4 = true := by decide +kernel
def h22Nodes7 : List NodeSpec := h22Block7_0 ++ h22Block7_1 ++ h22Block7_2 ++ h22Block7_3 ++ h22Block7_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check7 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket6 7 h22Nodes7 = true := by
  unfold h22Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h22Test7_0,h22Test7_1⟩,h22Test7_2⟩,h22Test7_3⟩,h22Test7_4⟩
def h22Bucket7 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 7 xs.toFinset) h22Bucket7 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket6Ok h22Check7
def h22Block8_0 : List NodeSpec := [([0,1,2,3,4],[7],[0])]
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
lemma h22Bound : Lower h22R h22G 9 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,9,11),(VAR 3,3,11),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h22Bucket8Ok (by decide +kernel)
def h28R : List Nat := varsOf 37
def h28G : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def h28Pos : List Nat := [33,36,5,5,36,33]
def h28Neg : List Nat := [32,32,1,4,4,1]
def h28Mask : Nat := fullMask 6
def h28Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h28Steps : List (Nat × Nat × Nat) := []
def h28W : BT Decor := buildWiresBT 2 h28Base h28Steps
def h28AutoList : List (List (Nat × Nat)) := [[]]
def h28Autos : BT (List (Nat × Nat)) := btOfList 1 h28AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Pairs : goodPairs h28G h28Pos h28Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28BaseOk : ∀ x ∈ h28Base, faithful h28Pos h28Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28WOk : btAll (fun x => faithful h28Pos h28Neg x ∧ x.1 < 2^128) h28W := buildWiresBT_faithful h28BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h28G = h28G) h28Autos := btAll_ofList (autos_of (by decide +kernel))
def h28SliceList : List (Option (Nat × Nat)) := []
def h28Slices : BT (Option (Nat × Nat)) := btOfList 1 h28SliceList
def h28Specs : List PoolSpec := []
def h28Pools : BT (Option BoundPool) := buildPoolsBT 1 h28W h28R h28Slices h28Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h28R h28G p.1 p.2) h28Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h28R h28G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h28R h28G c) h28Pools := buildPoolsBT_sound h28SlicesOk
def h28Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h28G (3 - 1) xs.toFinset) h28Empty := trivial
def h28Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Test3_0 : checkNodesBT h28W h28G h28Mask h28Pools h28Autos h28Empty 3 h28Block3_0 = true := by decide +kernel
def h28Nodes3 : List NodeSpec := h28Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Check3 : checkNodesBT h28W h28G h28Mask h28Pools h28Autos h28Empty 3 h28Nodes3 = true := h28Test3_0
def h28Bucket3 : BT (List (List Nat)) := buildBucketsBT h28W h28Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h28G 3 xs.toFinset) h28Bucket3 := buildBucketsBT_sound (by decide) h28Pairs h28WOk h28PoolsOk h28AutosOk h28EmptyOk h28Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 5,1,33)]) (by decide +kernel) h28Bucket3Ok (by decide +kernel)
def h29R : List Nat := varsOf 45
def h29G : Nat := 0xfaaafaaaa0a0a0a0faaafaaaa0a0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,36,44)]) (by decide +kernel) h28Bound
def h30R : List Nat := varsOf 53
def h30G : Nat := 0xfafaaaaaa0a0a0a0fafaaaaaa0a0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,36,52)]) (by decide +kernel) h28Bound
def h31R : List Nat := varsOf 57
def h31G : Nat := 0xffaaaa00aaaaaa00ffaaaa00aaaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,24,56)]) (by decide +kernel) h6Bound
def h33R : List Nat := varsOf 29
def h33G : Nat := 0xfaaaaa00faaaaa00faaaaa00faaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,24,28)]) (by decide +kernel) h6Bound
def h32R : List Nat := varsOf 61
def h32G : Nat := 0xfaaaaa00a0a0a000faaaaa00a0a0a000
def h32Pos : List Nat := [41,60,41,49,60,41,13,13,60,21,41,60,13,13,49,21,21,49,49,13,21,21,13,49,13,13,21,41,21,13,41,21]
def h32Neg : List Nat := [40,56,44,48,28,9,8,5,44,5,33,52,9,12,17,25,17,33,52,25,20,28,4,56,37,28,4,56,37,44,8,52]
def h32Mask : Nat := fullMask 32
def h32Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffff6ed,0x110bd6a0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xb779bbd2,0xb7742b94),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x6b483df7,0x6aa8b177),(0xffff0000ffff0000ffff0000ffff0000,0x94b7cb1a,0x8abdc81a),(0xffffffff00000000ffffffff00000000,0x48864d3f,0xb9860d0f)]
def h32Steps : List (Nat × Nat × Nat) := [(0,0,1),(3,0,1),(0,0,2),(3,0,2),(0,0,3),(3,0,3),(0,0,4),(3,0,4),(0,2,4),(0,2,5),(2,2,5),(0,2,6),(2,2,6),(0,3,4),(0,3,5),(2,3,5),(0,3,6),(2,3,6),(2,4,5),(0,1,2),(1,0,24),(2,0,24),(0,1,3),(1,0,27),(2,0,27),(2,1,14),(2,3,14),(2,4,14),(2,1,15),(2,1,19),(2,2,19),(2,4,19),(2,1,20),(2,3,17),(2,2,22),(2,3,7),(0,4,7),(2,4,7),(0,4,8),(2,4,8),(1,0,13),(2,0,13),(2,1,41),(2,2,41),(2,3,41),(2,2,42),(2,4,33),(2,1,44),(2,2,9),(0,4,9),(2,4,9),(0,4,10),(2,4,10),(1,0,18),(2,0,18),(2,1,54),(2,2,54),(2,3,54),(2,3,55),(2,4,37),(2,1,57),(2,1,11),(2,3,50),(2,2,63),(0,3,25),(0,4,25),(0,2,28),(0,4,28),(0,1,45),(0,3,45),(0,1,58),(0,2,58)]
def h32W : BT Decor := buildWiresBT 7 h32Base h32Steps
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
def h32SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 24,4),some (subcubeFast 0 32,5),some (subcubeFast 0 36,4)]
def h32Slices : BT (Option (Nat × Nat)) := btOfList 3 h32SliceList
def h32Specs : List PoolSpec := [(0,[]),(4,[(3,0,1)]),(5,[]),(4,[(0,1,2)]),(1,[]),(4,[(0,1,3)]),(2,[]),(4,[]),(2,[(3,0,2)]),(3,[]),(2,[(0,1,2)]),(2,[(0,2,4)]),(1,[(3,0,3)]),(1,[(0,1,3)]),(1,[(0,3,4)]),(0,[(3,0,4)]),(0,[(0,2,4)]),(0,[(0,3,4)])]
def h32Pools : BT (Option BoundPool) := buildPoolsBT 5 h32W h32R h32Slices h32Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Slice5 : Slice h32R h32G (subcubeFast 0 36) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Slice4 : Slice h32R h32G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Slice3 : Slice h32R h32G (subcubeFast 0 24) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Slice2 : Slice h32R h32G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Slice1 : Slice h32R h32G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Slice0 : Slice h32R h32G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h32R h32G p.1 p.2) h32Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h32R h32G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h32Slice0) (forall_cons (fun _ h => by cases h; exact h32Slice1) (forall_cons (fun _ h => by cases h; exact h32Slice2) (forall_cons (fun _ h => by cases h; exact h32Slice3) (forall_cons (fun _ h => by cases h; exact h32Slice4) (forall_cons (fun _ h => by cases h; exact h32Slice5) (fun _ h => (List.not_mem_nil h).elim)))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h32R h32G c) h32Pools := buildPoolsBT_sound h32SlicesOk
def h32Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h32G (4 - 1) xs.toFinset) h32Empty := trivial
def h32Block4_0 : List NodeSpec := [([0,1,2,4,31],[],[0]),([0,1,2,3,32],[],[0]),([0,1,3,4,35],[],[0]),([0,1,2,3,36],[],[0]),([0,1,2,4,38],[],[0]),([0,1,3,4,39],[],[0]),([0,2,3,4,47],[],[0]),([0,1,2,4,49],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test4_0 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Empty 4 h32Block4_0 = true := by decide +kernel
def h32Block4_1 : List NodeSpec := [([0,1,2,3,51],[],[0]),([0,2,3,4,52],[],[0]),([0,2,3,4,60],[],[0]),([0,1,3,4,61],[],[0]),([0,1,2,3,64],[],[0]),([0,2,3,4,65],[],[0]),([0,1,2,4,67],[],[0]),([0,1,3,4,68],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test4_1 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Empty 4 h32Block4_1 = true := by decide +kernel
def h32Block4_2 : List NodeSpec := [([0,1,2,4,69],[],[0]),([0,1,2,3,70],[],[0]),([0,1,3,4,71],[],[0]),([0,1,2,3,72],[],[0]),([0,2,3,4,73],[],[0]),([0,1,2,4,74],[],[0]),([0,2,3,4,75],[],[0]),([0,1,3,4,76],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test4_2 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Empty 4 h32Block4_2 = true := by decide +kernel
def h32Nodes4 : List NodeSpec := h32Block4_0 ++ h32Block4_1 ++ h32Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Check4 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Empty 4 h32Nodes4 = true := by
  unfold h32Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h32Test4_0,h32Test4_1⟩,h32Test4_2⟩
def h32Bucket4 : BT (List (List Nat)) := buildBucketsBT h32W h32Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h32G 4 xs.toFinset) h32Bucket4 := buildBucketsBT_sound (by decide) h32Pairs h32WOk h32PoolsOk h32AutosOk h32EmptyOk h32Check4
def h32Block5_0 : List NodeSpec := [([0,2,3,4,5,6],[0,1],[0]),([0,2,3,4,5,24],[3,4],[0]),([0,2,3,4,5,27],[5,6],[0]),([0,1,2,3,4,14],[6,7],[0]),([0,1,2,3,4,15],[],[0]),([0,1,2,3,4,19],[4,7],[0]),([0,1,2,3,4,20],[],[0]),([0,1,2,3,23],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test5_0 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket4 5 h32Block5_0 = true := by decide +kernel
def h32Block5_1 : List NodeSpec := [([0,1,2,3,5,23],[7],[0]),([0,1,2,3,4,16],[],[0]),([0,1,2,3,4,17],[6],[0]),([0,1,2,3,4,21],[],[0]),([0,1,2,3,4,22],[4],[0]),([0,1,3,4,7,8],[0,8],[0]),([0,1,3,4,7,24],[0,10],[0]),([0,1,2,3,4,30],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test5_1 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket4 5 h32Block5_1 = true := by decide +kernel
def h32Block5_2 : List NodeSpec := [([0,1,3,4,7,13],[7,11],[0]),([0,1,2,4,40],[],[0]),([0,1,2,4,7,40],[6],[0]),([0,1,2,3,4,41],[0,6],[0]),([0,1,2,3,4,42],[],[0]),([0,1,2,3,4,33],[7],[0]),([0,1,2,3,4,43],[],[0]),([0,1,2,3,4,44],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test5_2 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket4 5 h32Block5_2 = true := by decide +kernel
def h32Block5_3 : List NodeSpec := [([0,1,2,4,9,10],[0,12],[0]),([0,1,2,4,9,27],[0,13],[0]),([0,1,2,3,4,34],[],[0]),([0,1,3,4,53],[],[0]),([0,1,3,4,9,53],[4],[0]),([0,1,2,4,9,18],[7,14],[0]),([0,1,2,3,4,54],[0,4],[0]),([0,1,2,3,4,55],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test5_3 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket4 5 h32Block5_3 = true := by decide +kernel
def h32Block5_4 : List NodeSpec := [([0,1,2,3,4,37],[7],[0]),([0,1,2,3,4,56],[],[0]),([0,1,2,3,4,57],[0],[0]),([0,1,2,3,11,12],[0,15],[0]),([0,2,3,4,66],[],[0]),([0,2,3,4,11,66],[0],[0]),([0,1,2,3,11,13],[4,16],[0]),([0,1,2,3,4,48],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test5_4 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket4 5 h32Block5_4 = true := by decide +kernel
def h32Block5_5 : List NodeSpec := [([0,1,2,3,11,18],[6,17],[0]),([0,1,2,3,4,62],[],[0]),([0,1,2,3,4,50],[6],[0]),([0,1,2,3,4,63],[4],[0]),([0,1,2,3,4,25],[0,4,6,7],[0]),([0,1,2,3,4,26],[],[0]),([0,1,2,3,4,28],[0,4,6,7],[0]),([0,1,2,3,4,29],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test5_5 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket4 5 h32Block5_5 = true := by decide +kernel
def h32Block5_6 : List NodeSpec := [([0,1,2,3,4,45],[0,4,6,7],[0]),([0,1,2,3,4,46],[],[0]),([0,1,2,3,4,58],[0,4,6,7],[0]),([0,1,2,3,4,59],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test5_6 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket4 5 h32Block5_6 = true := by decide +kernel
def h32Nodes5 : List NodeSpec := h32Block5_0 ++ h32Block5_1 ++ h32Block5_2 ++ h32Block5_3 ++ h32Block5_4 ++ h32Block5_5 ++ h32Block5_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Check5 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket4 5 h32Nodes5 = true := by
  unfold h32Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h32Test5_0,h32Test5_1⟩,h32Test5_2⟩,h32Test5_3⟩,h32Test5_4⟩,h32Test5_5⟩,h32Test5_6⟩
def h32Bucket5 : BT (List (List Nat)) := buildBucketsBT h32W h32Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h32G 5 xs.toFinset) h32Bucket5 := buildBucketsBT_sound (by decide) h32Pairs h32WOk h32PoolsOk h32AutosOk h32Bucket4Ok h32Check5
def h32Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,2,4,6,7],[0]),([0,1,2,3,4,6],[0,1,2,4,6,7],[0]),([0,1,2,3,4,7],[0,4,6,7,9],[0]),([0,1,2,3,4,8],[0,4,6,7,8,9],[0]),([0,1,2,3,4,9],[0,4,6,7,9],[0]),([0,1,2,3,4,10],[0,4,6,7,9,12],[0]),([0,1,2,3,4,11],[0,2,4,6,7],[0]),([0,1,2,3,4,12],[0,2,4,6,7,15],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test6_0 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket5 6 h32Block6_0 = true := by decide +kernel
def h32Block6_1 : List NodeSpec := [([0,1,2,3,4,24],[0,2,3,4,6,7,9,10],[0]),([0,1,2,3,4,27],[0,2,4,5,6,7,9,13],[0]),([0,1,2,3,4,13],[0,2,4,6,7,9,11,16],[0]),([0,1,2,3,4,18],[0,2,4,6,7,9,14,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test6_1 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket5 6 h32Block6_1 = true := by decide +kernel
def h32Nodes6 : List NodeSpec := h32Block6_0 ++ h32Block6_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Check6 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket5 6 h32Nodes6 = true := by
  unfold h32Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h32Test6_0,h32Test6_1⟩
def h32Bucket6 : BT (List (List Nat)) := buildBucketsBT h32W h32Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h32G 6 xs.toFinset) h32Bucket6 := buildBucketsBT_sound (by decide) h32Pairs h32WOk h32PoolsOk h32AutosOk h32Bucket5Ok h32Check6
def h32Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,2,4,6,7,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Test7_0 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket6 7 h32Block7_0 = true := by decide +kernel
def h32Nodes7 : List NodeSpec := h32Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Check7 : checkNodesBT h32W h32G h32Mask h32Pools h32Autos h32Bucket6 7 h32Nodes7 = true := h32Test7_0
def h32Bucket7 : BT (List (List Nat)) := buildBucketsBT h32W h32Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h32G 7 xs.toFinset) h32Bucket7 := buildBucketsBT_sound (by decide) h32Pairs h32WOk h32PoolsOk h32AutosOk h32Bucket6Ok h32Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 8 := lower_of_forestBT (essPairs := [(VAR 0,12,13),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,5,21),(VAR 5,9,41)]) (by decide +kernel) h32Bucket7Ok (by decide +kernel)
def h34R : List Nat := varsOf 46
def h34G : Nat := 0xfcc0fcc0ccc0ccc0fcc0fcc0ccc0ccc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,12,44)]) (by decide +kernel) h3Bound
def h35R : List Nat := varsOf 54
def h35G : Nat := 0xfcfcc0c0ccccc0c0fcfcc0c0ccccc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,20,52)]) (by decide +kernel) h5Bound
def h36R : List Nat := varsOf 62
def h36G : Nat := 0xfcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 6 := lift_of (z := 0) (o := 40) (essPairs := [(VAR 3,18,26),(VAR 5,28,60)]) (by decide +kernel) h5Bound
def h38R : List Nat := varsOf 15
def h38G : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8
def h38Pos : List Nat := [6,3,3,13,14,6,13,9]
def h38Neg : List Nat := [4,1,2,12,12,2,5,1]
def h38Mask : Nat := fullMask 8
def h38Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,206,194),(0xcccccccccccccccccccccccccccccccc,55,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,121,89),(0xff00ff00ff00ff00ff00ff00ff00ff00,216,24)]
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
def h38Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
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
lemma h38Bound : Lower h38R h38G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,2,6),(VAR 3,1,9)]) (by decide +kernel) h38Bucket3Ok (by decide +kernel)
def h39R : List Nat := varsOf 23
def h39G : Nat := 0xeaeac8c8eaeac8c8eaeac8c8eaeac8c8
def h39Pos : List Nat := [6,3,3,21,22,6,21,17]
def h39Neg : List Nat := [4,1,2,20,20,2,5,1]
def h39Mask : Nat := fullMask 8
def h39Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,206,194),(0xcccccccccccccccccccccccccccccccc,55,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,121,89),(0xffff0000ffff0000ffff0000ffff0000,216,24)]
def h39Steps : List (Nat × Nat × Nat) := []
def h39W : BT Decor := buildWiresBT 2 h39Base h39Steps
def h39AutoList : List (List (Nat × Nat)) := [[]]
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
def h39SliceList : List (Option (Nat × Nat)) := []
def h39Slices : BT (Option (Nat × Nat)) := btOfList 1 h39SliceList
def h39Specs : List PoolSpec := []
def h39Pools : BT (Option BoundPool) := buildPoolsBT 1 h39W h39R h39Slices h39Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h39R h39G p.1 p.2) h39Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h39R h39G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h39R h39G c) h39Pools := buildPoolsBT_sound h39SlicesOk
def h39Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h39G (3 - 1) xs.toFinset) h39Empty := trivial
def h39Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Test3_0 : checkNodesBT h39W h39G h39Mask h39Pools h39Autos h39Empty 3 h39Block3_0 = true := by decide +kernel
def h39Nodes3 : List NodeSpec := h39Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Check3 : checkNodesBT h39W h39G h39Mask h39Pools h39Autos h39Empty 3 h39Nodes3 = true := h39Test3_0
def h39Bucket3 : BT (List (List Nat)) := buildBucketsBT h39W h39Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h39G 3 xs.toFinset) h39Bucket3 := buildBucketsBT_sound (by decide) h39Pairs h39WOk h39PoolsOk h39AutosOk h39EmptyOk h39Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,2,6),(VAR 4,1,17)]) (by decide +kernel) h39Bucket3Ok (by decide +kernel)
def h40R : List Nat := varsOf 30
def h40G : Nat := 0xfcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,18,26)]) (by decide +kernel) h5Bound
def h41R : List Nat := varsOf 15
def h41G : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h3Bound
def h42R : List Nat := varsOf 23
def h42G : Nat := 0xfefeeaeafefeeaeafefeeaeafefeeaea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bound : Lower h42R h42G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h5Bound
def h43R : List Nat := varsOf 27
def h43G : Nat := 0xffeeeeccffeeeeccffeeeeccffeeeecc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bound : Lower h43R h43G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,0,2)]) (by decide +kernel) h6Bound
def h37R : List Nat := varsOf 31
def h37G : Nat := 0xfeeaeac8feeaeac8feeaeac8feeaeac8
def h37Pos : List Nat := [6,9,6,6,13,17,26,9,26,17,3,26,28,3,13,21,7,11,19,21,9,28,28,13,21,17,11,9,19,25,6,22,14,14,6,22,3,14,22,26,26,6,6,9,7,3,6,3,7,21,17,3,13,9,25,26,26,28]
def h37Neg : List Nat := [4,8,5,2,12,16,18,1,10,1,2,24,24,1,5,5,5,10,18,20,10,12,20,4,4,24,1,24,1,24,12,20,10,12,20,18,0,4,4,16,8,10,18,12,2,5,0,18,1,1,5,10,1,5,1,0,2,4]
def h37Mask : Nat := fullMask 58
def h37Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7fb8103f9fe6b2,0x7720001401e284),(0xcccccccccccccccccccccccccccccccc,0x189f7ffd4072d4d,0x108960900160548),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x213566fc1e9d01d,0x2242866c1e9c015),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f009a32cf259d2,0x80b036a321912),(0xffff0000ffff0000ffff0000ffff0000,0x3c601c8b36c9b60,0x848caa4c1860)]
def h37Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,1,4),(1,1,4),(2,1,4),(3,1,4),(1,2,3),(3,2,3),(1,2,4),(3,2,4),(1,2,5),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(1,3,5),(2,3,5),(1,4,5),(2,4,5),(1,1,37),(0,3,6),(2,3,6),(0,3,9),(0,3,45),(0,4,6),(2,4,6),(0,4,9),(0,4,45),(0,6,9),(1,6,45),(0,9,45),(2,1,37),(3,1,37),(3,1,55),(0,9,55),(2,6,37),(0,9,37),(2,9,37),(1,1,46),(1,1,50),(2,6,11),(1,0,27),(3,1,67),(0,3,67),(1,4,27),(2,4,27),(2,6,27),(1,0,31),(3,1,73),(0,4,73),(1,3,31),(2,3,31),(2,6,31),(1,0,37),(0,3,79),(0,4,79),(3,0,37),(3,0,45),(0,2,45),(3,2,45),(1,2,37),(1,0,46),(1,0,50),(1,2,7),(1,8,11),(1,8,37),(2,1,69),(2,1,75),(1,27,37),(1,0,58),(1,0,71),(1,1,71),(2,3,71),(1,31,37),(1,0,77),(1,1,77),(2,4,77),(2,4,48),(2,3,52),(1,1,56),(1,2,48),(1,2,52),(1,0,102),(1,11,24),(2,3,109),(1,11,27),(1,11,37),(3,11,37),(2,4,110),(1,0,98),(1,11,28),(2,4,116),(1,11,31),(2,3,117),(3,11,45),(0,2,64),(1,2,64),(2,2,64),(3,2,64),(0,3,21),(0,4,21),(1,4,12),(2,4,12),(3,12,21),(2,3,22),(2,4,22),(1,12,22),(2,4,121),(2,3,20),(2,4,20),(1,1,81),(2,1,81),(1,2,81),(2,2,81),(1,3,81),(3,4,13),(0,13,21),(1,0,142),(1,0,130),(2,13,22),(0,2,136),(3,2,136),(2,13,27),(2,13,28),(2,13,31),(1,0,35),(2,3,35),(1,0,152),(2,13,35),(1,20,81),(0,3,138),(1,2,14),(3,14,21),(1,14,22),(1,1,82),(0,2,65),(1,2,65),(2,2,65),(3,2,65),(2,3,16),(3,16,21),(1,16,22),(2,3,161),(3,20,140),(1,1,80),(2,1,80),(1,2,80),(2,2,80),(3,3,17),(0,17,21),(1,0,175),(1,0,131),(2,17,22),(2,17,24),(2,17,27),(0,2,170),(3,2,170),(2,17,31),(1,0,33),(2,4,33),(1,0,185),(2,17,33),(1,20,80),(0,4,172),(1,2,18),(3,18,21),(1,18,22),(3,1,38),(2,21,37),(0,21,38),(3,37,38),(2,21,39),(2,21,40),(1,22,37),(3,22,38),(1,22,39),(1,22,40),(3,2,25),(3,2,29),(2,25,37),(2,29,37),(1,4,26),(1,27,40),(1,3,30),(1,31,39),(1,37,193),(3,37,193),(1,1,212)]
def h37W : BT Decor := buildWiresBT 8 h37Base h37Steps
def h37AutoList : List (List (Nat × Nat)) := [[]]
def h37Autos : BT (List (Nat × Nat)) := btOfList 1 h37AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Pairs : goodPairs h37G h37Pos h37Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37BaseOk : ∀ x ∈ h37Base, faithful h37Pos h37Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37WOk : btAll (fun x => faithful h37Pos h37Neg x ∧ x.1 < 2^128) h37W := buildWiresBT_faithful h37BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h37G = h37G) h37Autos := btAll_ofList (autos_of (by decide +kernel))
def h37SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 1 0,5),some (subcubeFast 1 8,4),some (subcubeFast 1 16,4),some (subcubeFast 2 0,5),some (subcubeFast 2 4,4),some (subcubeFast 4 0,6),some (subcubeFast 8 0,4),some (subcubeFast 16 0,4)]
def h37Slices : BT (Option (Nat × Nat)) := btOfList 4 h37SliceList
def h37Specs : List PoolSpec := [(3,[]),(6,[]),(8,[(0,0,1)]),(4,[]),(5,[]),(8,[]),(0,[]),(8,[(0,0,1),(1,3,5)]),(1,[]),(8,[(0,0,1),(2,3,5)]),(9,[]),(8,[(0,0,1),(1,4,5)]),(2,[]),(8,[(0,0,1),(2,4,5)]),(10,[]),(8,[(1,0,1)]),(6,[(1,0,2)]),(7,[]),(0,[(1,0,1)]),(1,[(1,0,2)]),(2,[(1,0,2)]),(6,[(3,0,2)]),(1,[(3,0,2)]),(2,[(3,0,2)]),(1,[(1,0,1)]),(2,[(1,0,1)]),(8,[(1,0,1),(0,3,6)]),(8,[(1,0,1),(0,4,6)]),(8,[(2,0,1)]),(0,[(2,0,1)]),(6,[(1,2,7)]),(8,[(3,0,1)]),(1,[(1,0,27)]),(2,[(1,0,31)]),(8,[(3,1,3)]),(2,[(1,0,2),(1,0,37)]),(0,[(3,1,3)]),(8,[(3,1,4)]),(1,[(1,0,2),(1,0,37)]),(0,[(3,1,4)]),(3,[(0,3,4)]),(8,[(0,3,4)]),(8,[(0,3,9)]),(8,[(0,4,9)]),(8,[(0,1,3)]),(8,[(0,1,4)]),(8,[(0,0,3)]),(1,[(1,4,12)]),(8,[(0,0,3),(1,4,12)]),(8,[(0,0,3),(2,4,12)]),(1,[(2,4,12)]),(8,[(1,0,3)]),(2,[(1,0,37)]),(2,[(1,0,3)]),(3,[(3,4,13)]),(8,[(1,0,3),(3,4,13)]),(8,[(2,0,3)]),(8,[(3,0,3)]),(2,[(3,0,3)]),(1,[(3,0,37)]),(2,[(3,0,37)]),(8,[(0,0,4)]),(8,[(0,0,4),(2,3,16)]),(2,[(2,3,16)]),(8,[(1,0,4)]),(1,[(1,0,37)]),(1,[(1,0,4)]),(3,[(3,3,17)]),(8,[(1,0,4),(3,3,17)]),(8,[(2,0,4)]),(8,[(3,0,4)]),(1,[(3,0,4)]),(8,[(0,3,21)]),(6,[(0,3,21)]),(8,[(0,4,21)]),(6,[(0,4,21)]),(8,[(2,3,22)]),(8,[(2,4,22)]),(8,[(1,1,3)]),(8,[(1,1,4)]),(8,[(3,1,4),(2,3,31)]),(6,[(3,2,25)]),(0,[(1,1,3)]),(8,[(2,1,3)]),(8,[(2,1,3),(1,4,26)]),(8,[(3,1,3),(2,4,27)]),(3,[(3,3,4)]),(6,[(3,2,29)]),(0,[(1,1,4)]),(8,[(2,1,4)]),(8,[(2,1,4),(1,3,30)]),(3,[(2,3,4)]),(8,[(1,0,33)]),(8,[(2,4,33)]),(8,[(1,0,35)]),(8,[(2,3,35)]),(8,[(0,3,4),(1,3,4)]),(8,[(1,3,4),(0,3,4)]),(8,[(1,3,4)]),(8,[(2,3,4)]),(8,[(3,3,4)])]
def h37Pools : BT (Option BoundPool) := buildPoolsBT 7 h37W h37R h37Slices h37Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice10 : Slice h37R h37G (subcubeFast 16 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice9 : Slice h37R h37G (subcubeFast 8 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice8 : Slice h37R h37G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice7 : Slice h37R h37G (subcubeFast 2 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice6 : Slice h37R h37G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice5 : Slice h37R h37G (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice4 : Slice h37R h37G (subcubeFast 1 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice3 : Slice h37R h37G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice2 : Slice h37R h37G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice1 : Slice h37R h37G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice0 : Slice h37R h37G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h37R h37G p.1 p.2) h37Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h37R h37G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h37Slice0) (forall_cons (fun _ h => by cases h; exact h37Slice1) (forall_cons (fun _ h => by cases h; exact h37Slice2) (forall_cons (fun _ h => by cases h; exact h37Slice3) (forall_cons (fun _ h => by cases h; exact h37Slice4) (forall_cons (fun _ h => by cases h; exact h37Slice5) (forall_cons (fun _ h => by cases h; exact h37Slice6) (forall_cons (fun _ h => by cases h; exact h37Slice7) (forall_cons (fun _ h => by cases h; exact h37Slice8) (forall_cons (fun _ h => by cases h; exact h37Slice9) (forall_cons (fun _ h => by cases h; exact h37Slice10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h37R h37G c) h37Pools := buildPoolsBT_sound h37SlicesOk
def h37Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G (3 - 1) xs.toFinset) h37Empty := trivial
def h37Block3_0 : List NodeSpec := [([1,3,60,81],[],[0]),([1,4,60,80],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test3_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Empty 3 h37Block3_0 = true := by decide +kernel
def h37Nodes3 : List NodeSpec := h37Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check3 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Empty 3 h37Nodes3 = true := h37Test3_0
def h37Bucket3 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 3 xs.toFinset) h37Bucket3 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37EmptyOk h37Check3
def h37Block4_0 : List NodeSpec := [([3,4,6,9,45],[],[0]),([1,3,4,9,55],[5],[0]),([1,3,4,9,61],[],[0]),([1,4,9,27,79],[35],[0]),([1,3,4,9,95],[],[0]),([1,3,9,31,79],[38],[0]),([1,3,4,9,59],[],[0]),([1,4,9,48,79],[35],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test4_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket3 4 h37Block4_0 = true := by decide +kernel
def h37Block4_1 : List NodeSpec := [([1,3,9,52,79],[38],[0]),([0,1,3,4,56],[5],[0]),([0,3,4,9,105],[],[0]),([0,1,3,11,114],[],[0]),([0,1,4,11,119],[],[0]),([0,1,3,4,120],[],[0]),([2,3,4,54,64],[],[0]),([0,2,3,64,133],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test4_1 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket3 4 h37Block4_1 = true := by decide +kernel
def h37Block4_2 : List NodeSpec := [([0,2,3,64,135],[],[0]),([0,1,2,81,130],[],[0]),([0,2,27,81,136],[],[0]),([0,2,27,81,137],[],[0]),([2,3,4,54,68],[],[0]),([1,2,3,54,81],[],[0]),([0,1,2,81,134],[],[0]),([0,1,2,3,155],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test4_2 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket3 4 h37Block4_2 = true := by decide +kernel
def h37Block4_3 : List NodeSpec := [([0,1,3,81,146],[],[0]),([0,1,3,81,147],[],[0]),([2,3,4,54,65],[],[0]),([0,2,4,65,168],[],[0]),([0,2,4,65,134],[],[0]),([1,2,4,54,140],[],[0]),([0,1,2,4,169],[],[0]),([0,1,2,80,131],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test4_3 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket3 4 h37Block4_3 = true := by decide +kernel
def h37Block4_4 : List NodeSpec := [([0,2,31,80,170],[],[0]),([0,2,31,80,171],[],[0]),([2,3,4,54,74],[],[0]),([1,2,4,54,80],[],[0]),([0,1,2,80,135],[],[0]),([0,1,2,4,188],[],[0]),([0,1,4,80,181],[],[0]),([0,1,4,80,182],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test4_4 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket3 4 h37Block4_4 = true := by decide +kernel
def h37Block4_5 : List NodeSpec := [([0,1,2,38,194],[],[0]),([0,1,2,37,200],[],[0]),([1,3,4,45,60],[],[0]),([0,1,37,38,85],[],[0]),([0,2,37,45,193],[],[0]),([0,1,2,37,212],[],[0]),([0,2,37,57,193],[],[0]),([0,1,2,37,211],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test4_5 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket3 4 h37Block4_5 = true := by decide +kernel
def h37Block4_6 : List NodeSpec := [([0,1,2,37,213],[],[0]),([2,3,4,54,101],[],[0]),([2,3,4,54,97],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test4_6 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket3 4 h37Block4_6 = true := by decide +kernel
def h37Nodes4 : List NodeSpec := h37Block4_0 ++ h37Block4_1 ++ h37Block4_2 ++ h37Block4_3 ++ h37Block4_4 ++ h37Block4_5 ++ h37Block4_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check4 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket3 4 h37Nodes4 = true := by
  unfold h37Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h37Test4_0,h37Test4_1⟩,h37Test4_2⟩,h37Test4_3⟩,h37Test4_4⟩,h37Test4_5⟩,h37Test4_6⟩
def h37Bucket4 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 4 xs.toFinset) h37Bucket4 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket3Ok h37Check4
def h37Block5_0 : List NodeSpec := [([1,3,4,6,9,37],[3,4,16],[0]),([1,3,4,6,9,46],[0,3,16],[0]),([1,3,4,6,9,47],[3],[0]),([1,3,4,6,9,50],[0,4,16],[0]),([1,3,4,6,9,51],[4],[0]),([0,1,3,4,11,66],[15],[0]),([1,2,3,4,6,67],[5],[0]),([1,2,3,4,6,73],[5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_0 = true := by decide +kernel
def h37Block5_1 : List NodeSpec := [([1,2,3,4,6,79],[1,3,4],[0]),([0,2,3,4,6,45],[0,10,14],[0]),([0,1,2,3,4,55],[5,6,8,12],[0]),([0,1,2,3,4,61],[],[0]),([0,1,3,4,11,90],[31],[0]),([0,2,3,4,8,45],[],[0]),([0,1,2,3,4,91],[5,6],[0]),([0,1,4,9,27,37],[16,20],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_1 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_1 = true := by decide +kernel
def h37Block5_2 : List NodeSpec := [([0,1,3,4,9,58],[0],[0]),([0,1,3,4,9,71],[],[0]),([0,1,3,9,31,37],[16,19],[0]),([0,1,3,4,9,77],[],[0]),([1,3,4,9,79],[3,4,5,35,38,40],[0]),([1,3,4,9,37,79],[0,3,35,38],[0]),([0,1,3,4,9,45],[0,6],[0]),([0,1,4,9,37,48],[6,20],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_2 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_2 = true := by decide +kernel
def h37Block5_3 : List NodeSpec := [([0,1,3,9,37,52],[6,19],[0]),([0,1,3,4,9,62],[0,5,16],[0]),([0,1,3,4,9,63],[0,5],[0]),([0,1,3,4,9,103],[],[0]),([0,1,3,4,9,104],[],[0]),([1,2,3,4,9,79],[3,5],[0]),([0,1,2,3,4,63],[0],[0]),([0,1,3,4,11,102],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_3 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_3 = true := by decide +kernel
def h37Block5_4 : List NodeSpec := [([0,1,3,4,11,109],[44],[0]),([0,1,4,11,27,37],[21,23],[0]),([0,1,3,4,11,58],[],[0]),([0,1,3,4,11,71],[],[0]),([0,1,3,4,11,111],[],[0]),([0,1,3,4,11,110],[23],[0]),([0,1,3,4,11,98],[],[0]),([0,1,3,4,11,116],[45],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_4 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_4 = true := by decide +kernel
def h37Block5_5 : List NodeSpec := [([0,1,3,11,31,37],[21,22],[0]),([0,1,3,4,11,77],[],[0]),([0,1,3,4,11,118],[],[0]),([0,1,3,4,11,117],[22],[0]),([0,1,3,4,11,45],[5],[0]),([0,1,3,4,11,112],[41],[0]),([0,1,3,4,11,113],[],[0]),([0,2,3,4,21,64],[5,10,24],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_5 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_5 = true := by decide +kernel
def h37Block5_6 : List NodeSpec := [([0,1,2,3,21,127],[10,47],[0]),([0,1,2,3,21,128],[],[0]),([0,1,2,3,4,129],[0,5],[0]),([0,2,3,4,22,64],[],[0]),([0,1,2,3,22,127],[],[0]),([0,1,2,3,22,128],[],[0]),([0,1,2,3,4,132],[0,5],[0]),([0,2,3,4,64,121],[0,4,10,24],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_6 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_6 = true := by decide +kernel
def h37Block5_7 : List NodeSpec := [([0,2,3,4,64,122],[10,24],[0]),([0,2,3,4,64,123],[],[0]),([0,2,3,4,64,124],[],[0]),([0,2,3,4,20,64],[0,4,10,24],[0]),([0,2,3,4,23,64],[0],[0]),([0,1,2,3,21,81],[],[0]),([0,1,2,3,21,141],[],[0]),([0,1,2,3,4,142],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_7 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_7 = true := by decide +kernel
def h37Block5_8 : List NodeSpec := [([0,1,2,4,13,130],[],[0]),([0,1,2,3,22,81],[8],[0]),([0,1,2,3,22,141],[],[0]),([0,1,2,3,4,145],[],[0]),([0,1,2,27,81],[3,4,8,40,52],[0]),([0,1,2,4,27,81],[4,52],[0]),([0,1,2,4,27,148],[],[0]),([1,2,3,4,13,88],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_8 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_8 = true := by decide +kernel
def h37Block5_9 : List NodeSpec := [([0,1,2,4,13,98],[14],[0]),([0,1,2,3,4,149],[8],[0]),([0,1,2,4,13,77],[14],[0]),([0,1,2,3,4,150],[8],[0]),([0,2,3,4,20,68],[8],[0]),([0,2,3,4,23,68],[6],[0]),([0,1,2,4,13,152],[14],[0]),([0,1,2,3,4,154],[8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_9 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_9 = true := by decide +kernel
def h37Block5_10 : List NodeSpec := [([0,1,2,3,20,81],[8,14,40],[0]),([0,1,2,3,23,81],[],[0]),([0,1,2,3,81,136],[8,14,52],[0]),([0,1,2,3,81,137],[4,8],[0]),([0,1,2,3,81,138],[],[0]),([0,1,2,3,81,139],[],[0]),([0,1,2,3,4,136],[5,6,8,14],[0]),([0,1,2,4,14,125],[6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_10 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_10 = true := by decide +kernel
def h37Block5_11 : List NodeSpec := [([0,1,2,3,4,158],[5],[0]),([0,1,2,3,4,159],[5],[0]),([0,1,2,3,4,160],[5,6],[0]),([0,2,3,4,21,65],[5,14,25],[0]),([0,1,2,4,21,140],[14,52],[0]),([0,1,2,4,21,165],[],[0]),([0,1,2,3,4,166],[0,5],[0]),([0,2,3,4,22,65],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_11 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_11 = true := by decide +kernel
def h37Block5_12 : List NodeSpec := [([0,1,2,4,22,140],[],[0]),([0,1,2,4,22,165],[],[0]),([0,1,2,3,4,167],[0,5],[0]),([0,2,3,4,65,161],[0,3,14,25],[0]),([0,2,3,4,65,162],[14,25],[0]),([0,2,3,4,65,163],[],[0]),([0,2,3,4,65,164],[],[0]),([0,2,3,4,20,65],[0,3,14,25],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_12 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_12 = true := by decide +kernel
def h37Block5_13 : List NodeSpec := [([0,2,3,4,23,65],[0],[0]),([0,1,2,4,20,140],[0,8,14,52],[0]),([0,1,2,4,23,140],[],[0]),([0,1,2,4,21,80],[],[0]),([0,1,2,4,21,174],[],[0]),([0,1,2,3,4,175],[],[0]),([0,1,2,4,22,80],[12],[0]),([0,1,2,4,22,174],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_13 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_13 = true := by decide +kernel
def h37Block5_14 : List NodeSpec := [([0,1,2,3,17,131],[],[0]),([0,1,2,3,4,178],[],[0]),([1,2,3,4,17,87],[1],[0]),([0,1,2,3,17,102],[10],[0]),([0,1,2,3,4,179],[8],[0]),([0,1,2,3,17,71],[10],[0]),([0,1,2,3,4,180],[8],[0]),([0,1,2,31,80],[3,4,12,40,65],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_14 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_14 = true := by decide +kernel
def h37Block5_15 : List NodeSpec := [([0,1,2,3,31,80],[3,65],[0]),([0,1,2,3,31,183],[],[0]),([0,2,3,4,20,74],[12],[0]),([0,2,3,4,23,74],[6],[0]),([0,1,2,3,17,185],[10],[0]),([0,1,2,3,4,187],[8],[0]),([0,1,2,4,20,80],[10,12,40],[0]),([0,1,2,4,23,80],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_15 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_15 = true := by decide +kernel
def h37Block5_16 : List NodeSpec := [([0,1,2,4,80,170],[10,12,65],[0]),([0,1,2,4,80,171],[3,12],[0]),([0,1,2,4,80,172],[],[0]),([0,1,2,4,80,173],[],[0]),([0,1,2,3,4,170],[5,6,10,12],[0]),([0,1,2,3,18,126],[6],[0]),([0,1,2,3,4,191],[5],[0]),([0,1,2,3,4,192],[5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_16 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_16 = true := by decide +kernel
def h37Block5_17 : List NodeSpec := [([0,2,3,4,21,45],[5],[0]),([0,1,2,21,37,38],[10],[0]),([0,1,2,3,4,194],[],[0]),([0,1,2,4,38,125],[10],[0]),([0,1,2,3,38,126],[10],[0]),([0,1,2,3,4,195],[],[0]),([0,1,2,3,4,197],[],[0]),([0,1,2,3,4,198],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_17 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_17 = true := by decide +kernel
def h37Block5_18 : List NodeSpec := [([0,1,2,3,4,143],[6,12,14],[0]),([0,1,2,3,4,176],[6,8,10],[0]),([0,2,3,4,22,45],[5],[0]),([0,1,2,22,37,38],[8],[0]),([0,1,2,3,4,199],[6],[0]),([0,1,2,3,4,200],[],[0]),([0,1,2,3,39,131],[],[0]),([0,1,2,3,4,201],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_18 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_18 = true := by decide +kernel
def h37Block5_19 : List NodeSpec := [([0,1,2,4,40,130],[],[0]),([0,1,2,3,4,202],[],[0]),([0,1,2,3,4,144],[],[0]),([0,1,2,3,4,177],[],[0]),([0,1,2,3,4,108],[8],[0]),([0,1,2,25,29,37],[1,8],[0]),([0,1,2,4,25,49],[],[0]),([0,1,2,3,29,53],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_19 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_19 = true := by decide +kernel
def h37Block5_20 : List NodeSpec := [([0,1,2,3,4,45],[5,6],[0]),([0,1,2,25,31,37],[1,8],[0]),([0,1,2,4,25,77],[80],[0]),([0,1,2,4,37,205],[8],[0]),([0,1,2,27,29,37],[1,8],[0]),([0,1,2,3,29,71],[85],[0]),([0,1,2,27,31,37],[1,8],[0]),([0,1,2,4,27,79],[8,52],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_20 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_20 = true := by decide +kernel
def h37Block5_21 : List NodeSpec := [([0,1,2,4,27,208],[8],[0]),([0,1,2,3,4,95],[],[0]),([0,1,2,3,4,96],[8],[0]),([0,1,2,3,4,115],[8],[0]),([0,1,2,3,37,206],[8],[0]),([0,1,2,3,31,79],[12,65],[0]),([0,1,2,3,31,210],[12],[0]),([0,1,2,3,4,100],[8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_21 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_21 = true := by decide +kernel
def h37Block5_22 : List NodeSpec := [([0,1,2,3,4,186],[8],[0]),([0,1,2,3,4,153],[8],[0]),([0,1,2,3,4,59],[],[0]),([0,1,2,3,4,83],[5,6],[0]),([0,1,3,4,45,84],[6],[0]),([0,1,3,4,45,85],[5],[0]),([0,1,3,4,37,85],[],[0]),([0,1,2,37,38,45],[8,10,96],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_22 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_22 = true := by decide +kernel
def h37Block5_23 : List NodeSpec := [([0,1,2,37,38,57],[8],[0]),([0,1,2,37,38,86],[97],[0]),([0,1,2,37,193],[3,8,40],[0]),([0,1,2,37,196],[3,8,40],[0]),([0,2,3,4,20,101],[10,12],[0]),([0,2,3,4,23,101],[6],[0]),([0,2,3,4,20,97],[8,14],[0]),([0,2,3,4,23,97],[6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_23 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_23 = true := by decide +kernel
def h37Nodes5 : List NodeSpec := h37Block5_0 ++ h37Block5_1 ++ h37Block5_2 ++ h37Block5_3 ++ h37Block5_4 ++ h37Block5_5 ++ h37Block5_6 ++ h37Block5_7 ++ h37Block5_8 ++ h37Block5_9 ++ h37Block5_10 ++ h37Block5_11 ++ h37Block5_12 ++ h37Block5_13 ++ h37Block5_14 ++ h37Block5_15 ++ h37Block5_16 ++ h37Block5_17 ++ h37Block5_18 ++ h37Block5_19 ++ h37Block5_20 ++ h37Block5_21 ++ h37Block5_22 ++ h37Block5_23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check5 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Nodes5 = true := by
  unfold h37Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h37Test5_0,h37Test5_1⟩,h37Test5_2⟩,h37Test5_3⟩,h37Test5_4⟩,h37Test5_5⟩,h37Test5_6⟩,h37Test5_7⟩,h37Test5_8⟩,h37Test5_9⟩,h37Test5_10⟩,h37Test5_11⟩,h37Test5_12⟩,h37Test5_13⟩,h37Test5_14⟩,h37Test5_15⟩,h37Test5_16⟩,h37Test5_17⟩,h37Test5_18⟩,h37Test5_19⟩,h37Test5_20⟩,h37Test5_21⟩,h37Test5_22⟩,h37Test5_23⟩
def h37Bucket5 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 5 xs.toFinset) h37Bucket5 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket4Ok h37Check5
def h37Block6_0 : List NodeSpec := [([0,1,3,4,36],[0,1,2,3,5,6],[0]),([0,1,2,4,41],[0,1,4,7,8],[0]),([0,1,2,4,42],[0,1,3,4,9,10],[0]),([0,1,2,3,43],[0,1,3,11,12],[0]),([0,1,2,3,44],[0,1,3,4,13,14],[0]),([1,3,4,6,9],[0,3,4,5,15,16,17,18],[0]),([0,1,3,4,6,9],[0,3,4,5,6,15,16,17,19,20],[0]),([0,1,3,4,6,11],[0,3,4,5,6,15,17,21,22,23],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_0 = true := by decide +kernel
def h37Block6_1 : List NodeSpec := [([0,1,2,3,4,6,27],[0,8,10,17,24],[0]),([0,1,2,3,4,6,31],[0,12,14,17,25],[0]),([0,1,2,3,4,6,37],[0,1,3,4,8,10,12,14],[0]),([0,1,2,3,4,46],[0,1,3,5,6,10,12,14,24,26],[0]),([0,1,2,3,4,6,46],[0,1,3,8,10],[0]),([0,1,2,3,4,47],[3,5,6,10,12,14,24],[0]),([0,1,2,3,4,6,47],[3,8,10],[0]),([0,1,2,3,4,50],[0,1,4,5,6,8,10,14,25,27],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_1 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_1 = true := by decide +kernel
def h37Block6_2 : List NodeSpec := [([0,1,2,3,4,6,50],[0,1,4,12,14],[0]),([0,1,2,3,4,51],[4,5,6,8,10,14,25],[0]),([0,1,2,3,4,6,51],[4,12,14],[0]),([1,3,4,7,9],[0,3,4,16,17,29],[0]),([0,1,2,3,4,6],[0,1,5,6,8,10,12,14,15,17,24,25],[0]),([0,1,3,4,89],[0,3,4,5,6,28,30],[0]),([0,1,3,4,8,11],[0,3,4,5,21,22,23,31],[0]),([0,1,2,3,4,8,37],[1,3,4,8,10,12,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_2 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_2 = true := by decide +kernel
def h37Block6_3 : List NodeSpec := [([0,1,2,3,4,69],[0,1,3,5,6,10,12,14,32],[0]),([0,1,2,3,4,75],[0,1,4,5,6,8,10,14,33],[0]),([0,1,3,4,9,27],[0,3,6,16,17,19,20,34,36],[0]),([0,1,3,4,9,31],[0,4,6,16,17,19,20,37,39],[0]),([0,1,3,4,9,37],[0,3,4,6,16,19,20,40,41],[0]),([0,1,3,4,9,48],[0,3,5,6,16,17,19,20,42],[0]),([0,1,3,4,9,52],[0,4,5,6,16,17,19,20,43],[0]),([0,1,2,3,4,9,37],[0,3,5,6,8,10,12,14,41],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_3 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_3 = true := by decide +kernel
def h37Block6_4 : List NodeSpec := [([0,1,2,3,4,48],[0,1,3,5,6,10,12,14,17,42],[0]),([0,1,2,3,4,52],[0,1,4,5,6,8,10,14,17,43],[0]),([0,1,3,4,9],[0,3,4,5,6,16,17,19,20],[0]),([0,1,3,4,11,24],[0,3,5,21,22,23,44],[0]),([0,1,3,4,11,27],[0,3,5,21,22,23,34],[0]),([0,1,3,4,11,28],[0,4,5,21,22,23,45],[0]),([0,1,3,4,11,31],[0,4,5,21,22,23,37],[0]),([0,1,3,4,11,37],[0,3,4,5,21,22,23,40,41],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_4 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_4 = true := by decide +kernel
def h37Block6_5 : List NodeSpec := [([0,1,2,3,4,12,21],[0,1,5,6,8,10],[0]),([0,1,2,3,4,12,22],[0,1,5,6],[0]),([0,2,3,4,64],[0,3,4,10,24],[0]),([0,1,2,3,4,64],[0,1,3,4,5,6,10,12,14,24],[0]),([0,2,3,4,92],[0,1,4,10,32],[0]),([0,1,3,4,106],[0,4,5,6,10,19,42],[0]),([0,1,2,3,127],[0,10,12,47,48],[0]),([0,1,2,3,128],[0,4,10,14,49,50],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_5 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_5 = true := by decide +kernel
def h37Block6_6 : List NodeSpec := [([0,1,2,3,4,13,21],[6,8],[0]),([0,1,2,3,4,13,22],[1,5,6,8],[0]),([0,1,2,4,13,27],[0,1,3,8,10,36,53],[0]),([0,1,2,3,4,13,28],[0,1,8,12,14],[0]),([0,1,2,3,4,13,31],[4,8,12,14],[0]),([0,1,2,3,4,68],[0,1,3,5,6,8,10,12,14],[0]),([0,1,2,3,4,13,35],[6,8,12,14],[0]),([0,1,2,3,81],[3,4,8,14,40],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_6 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_6 = true := by decide +kernel
def h37Block6_7 : List NodeSpec := [([0,1,2,3,4,81],[0,1,3,4,5,6,8,10,14,40,52],[0]),([0,1,2,3,141],[3,8,12,54,55],[0]),([0,1,2,3,4,14,21],[0,5,6,8],[0]),([0,1,2,3,4,14,22],[0,1,5,6],[0]),([0,1,2,3,4,72],[0,1,4,5,6,8,12,14],[0]),([0,1,3,4,157],[0,4,5,6,8,56],[0]),([0,1,2,3,4,15,21],[3,6,10],[0]),([0,1,2,3,4,15,22],[1,3,5,6,8,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_7 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_7 = true := by decide +kernel
def h37Block6_8 : List NodeSpec := [([0,1,2,4,15,27],[0,1,3,8,10,36,58],[0]),([0,1,2,3,4,15,28],[1,3,8,10],[0]),([0,1,2,3,4,15,31],[3,4,8,10,12,14],[0]),([0,1,2,3,4,15,35],[3,6,8,10],[0]),([0,1,2,3,4,82],[1,3,4,5,6,10,14,40,59,60],[0]),([0,1,2,3,4,16,21],[0,1,5,6,12,14],[0]),([0,1,2,3,4,16,22],[0,1,5,6],[0]),([0,2,3,4,65],[0,3,14,25],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_8 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_8 = true := by decide +kernel
def h37Block6_9 : List NodeSpec := [([0,1,2,3,4,65],[0,1,3,5,6,8,10,14,25],[0]),([0,2,3,4,93],[0,1,3,14,33],[0]),([0,1,3,4,107],[0,3,5,6,14,20,43],[0]),([0,1,2,4,140],[0,8,14,52],[0]),([0,1,2,4,165],[0,3,10,14,62,63],[0]),([0,1,2,3,4,17,21],[6,12],[0]),([0,1,2,3,4,17,22],[1,5,6,12],[0]),([0,1,2,3,4,17,24],[0,1,8,10,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_9 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_9 = true := by decide +kernel
def h37Block6_10 : List NodeSpec := [([0,1,2,3,4,17,27],[3,8,10,12],[0]),([0,1,2,3,17,31],[0,1,4,12,14,39,66],[0]),([0,1,2,3,4,74],[0,1,4,5,6,8,10,12,14],[0]),([0,1,2,3,4,17,33],[6,8,10,12],[0]),([0,1,2,4,80],[3,4,10,12,40],[0]),([0,1,2,3,4,80],[0,1,3,5,6,8,10,12,40,65],[0]),([0,1,2,4,174],[3,8,12,67,68],[0]),([0,1,2,3,4,18,21],[0,5,6,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_10 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_10 = true := by decide +kernel
def h37Block6_11 : List NodeSpec := [([0,1,2,3,4,18,22],[0,1,5,6],[0]),([0,1,2,3,4,78],[0,1,3,5,6,8,10,12],[0]),([0,1,3,4,190],[0,3,5,6,12,69],[0]),([0,1,2,3,4,19,21],[4,6,14],[0]),([0,1,2,3,4,19,22],[1,4,5,6,12,14],[0]),([0,1,2,3,4,19,24],[1,4,12,14],[0]),([0,1,2,3,4,19,27],[3,4,8,10,12,14],[0]),([0,1,2,3,19,31],[0,1,4,12,14,39,71],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_11 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_11 = true := by decide +kernel
def h37Block6_12 : List NodeSpec := [([0,1,2,3,4,19,33],[4,6,12,14],[0]),([0,1,2,3,4,90],[0,1,5,6,8,10,12,14,17,21,31],[0]),([0,1,2,3,4,21,37],[1,5,6,10],[0]),([0,1,2,3,4,21,38],[6,8,12],[0]),([0,1,2,3,4,21,39],[6,8,10,12],[0]),([0,1,2,3,4,21,40],[6,8,12,14],[0]),([0,1,2,3,4,125],[0,1,5,6,10,12,14,17,72,73],[0]),([0,1,2,3,4,126],[0,1,5,6,8,10,14,17,74,75],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_12 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_12 = true := by decide +kernel
def h37Block6_13 : List NodeSpec := [([0,1,2,3,4,66],[0,1,5,6,8,10,12,14,15],[0]),([0,1,2,3,4,22,37],[1,5,6,8,10,12,14],[0]),([0,1,2,3,4,22,38],[1,5,6,8],[0]),([0,1,2,3,4,22,39],[1,5,6,12],[0]),([0,1,2,3,4,22,40],[1,5,6,8],[0]),([0,1,2,3,4,130],[0,1,5,6,10,12,14,76],[0]),([0,1,2,3,4,131],[0,1,5,6,8,10,14,77],[0]),([0,1,2,3,4,87],[0,1,3,5,6,10,12,14,17,24],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_13 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_13 = true := by decide +kernel
def h37Block6_14 : List NodeSpec := [([0,1,2,3,4,27],[0,1,3,5,6,8,10,12,14,34],[0]),([0,1,2,3,4,102],[0,1,5,6,8,10,14,17],[0]),([0,1,2,3,4,25,29],[1,8,12,17,78,79],[0]),([0,1,2,3,4,25,31],[8,10,12,14,17,37],[0]),([0,1,3,4,203],[3,6,8,17,78,81],[0]),([0,1,2,4,25,37],[1,3,8,10,12,40,82],[0]),([0,1,2,3,4,53],[0,1,3,5,6,8,10,14],[0]),([0,1,2,3,207],[1,3,8,12,84],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_14 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_14 = true := by decide +kernel
def h37Block6_15 : List NodeSpec := [([0,1,2,3,99],[1,3,8,14,17],[0]),([0,1,2,3,4,99],[0,1,3,5,6,8,14,17],[0]),([0,1,2,3,4,67],[0,1,3,5,6,8,10,12,14,32],[0]),([0,1,2,3,4,27,67],[0,1,8,10,32],[0]),([0,1,2,3,4,27,29],[8,10,12,17,34],[0]),([0,1,2,3,4,27,31],[8,10,12,14],[0]),([0,1,2,4,27,37],[1,3,8,10,12,36,40],[0]),([0,1,2,4,27,40],[1,3,8,10,12,36,86],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_15 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_15 = true := by decide +kernel
def h37Block6_16 : List NodeSpec := [([0,1,2,3,4,58],[0,5,6,10,14],[0]),([0,1,2,3,4,27,70],[1,8,10,12,14],[0]),([0,1,2,3,4,71],[0,1,5,6,8,10,14,85],[0]),([0,1,2,3,4,27,71],[1,8,10,12],[0]),([0,1,2,3,4,88],[0,1,4,5,6,8,10,14,17,25],[0]),([0,1,2,3,4,98],[0,1,5,6,8,10,14,17],[0]),([0,1,2,3,4,31],[0,1,4,5,6,8,10,12,14,37],[0]),([0,1,3,4,204],[4,6,12,17,79,87],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_16 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_16 = true := by decide +kernel
def h37Block6_17 : List NodeSpec := [([0,1,2,3,29,37],[1,4,8,12,14,40,88],[0]),([0,1,2,3,4,49],[0,1,4,5,6,8,10,12],[0]),([0,1,2,4,209],[1,3,8,12,90],[0]),([0,1,2,4,94],[1,4,10,12,17],[0]),([0,1,2,3,4,94],[0,1,4,5,6,8,10,12,17],[0]),([0,1,2,3,4,73],[0,1,4,5,6,8,10,12,14,33],[0]),([0,1,2,3,4,31,73],[0,1,12,14,33],[0]),([0,1,2,3,31,37],[1,4,8,12,14,39,40],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_17 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_17 = true := by decide +kernel
def h37Block6_18 : List NodeSpec := [([0,1,2,3,31,39],[1,4,8,12,14,39,91],[0]),([0,1,2,3,4,31,76],[1,8,10,12,14],[0]),([0,1,2,3,4,77],[0,1,5,6,8,10,12,14,80],[0]),([0,1,2,3,4,31,77],[1,8,10,12,14],[0]),([0,1,2,3,4,189],[0,1,3,5,6,8,14,17],[0]),([0,1,2,3,4,184],[0,1,3,5,6,10,12,14,17,92],[0]),([0,1,2,3,4,185],[0,1,5,6,8,10,14,17,93],[0]),([0,1,2,3,4,156],[0,1,4,5,6,8,10,12,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_18 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_18 = true := by decide +kernel
def h37Block6_19 : List NodeSpec := [([0,1,2,3,4,151],[0,1,4,5,6,8,10,14,17,94],[0]),([0,1,2,3,4,152],[0,1,5,6,8,10,14,17,95],[0]),([0,1,2,3,4,79],[0,1,3,4,5,6,8,10,12,14,40,52,65],[0]),([0,1,2,3,4,37,79],[0,3,8,10,12,14,40,52,65],[0]),([0,1,2,3,4,45],[0,1,5,6,8,10,12,14],[0]),([0,1,2,3,4,37,45],[1,8,10,12,14,41],[0]),([0,1,2,3,4,37,57],[1,8,10,12,14],[0]),([0,1,2,3,4,37,86],[5,6,41],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_19 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_19 = true := by decide +kernel
def h37Block6_20 : List NodeSpec := [([0,1,2,37,38],[3,8,10,40,96],[0]),([0,1,2,3,4,193],[0,1,3,5,6,8,12],[0]),([0,1,2,3,4,101],[0,1,4,5,6,8,10,12],[0]),([0,1,2,3,4,37],[0,1,3,5,6,8,10,12,14,40,41],[0]),([0,1,2,3,4,97],[0,1,3,5,6,8,10,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_20 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_20 = true := by decide +kernel
def h37Nodes6 : List NodeSpec := h37Block6_0 ++ h37Block6_1 ++ h37Block6_2 ++ h37Block6_3 ++ h37Block6_4 ++ h37Block6_5 ++ h37Block6_6 ++ h37Block6_7 ++ h37Block6_8 ++ h37Block6_9 ++ h37Block6_10 ++ h37Block6_11 ++ h37Block6_12 ++ h37Block6_13 ++ h37Block6_14 ++ h37Block6_15 ++ h37Block6_16 ++ h37Block6_17 ++ h37Block6_18 ++ h37Block6_19 ++ h37Block6_20
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check6 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Nodes6 = true := by
  unfold h37Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h37Test6_0,h37Test6_1⟩,h37Test6_2⟩,h37Test6_3⟩,h37Test6_4⟩,h37Test6_5⟩,h37Test6_6⟩,h37Test6_7⟩,h37Test6_8⟩,h37Test6_9⟩,h37Test6_10⟩,h37Test6_11⟩,h37Test6_12⟩,h37Test6_13⟩,h37Test6_14⟩,h37Test6_15⟩,h37Test6_16⟩,h37Test6_17⟩,h37Test6_18⟩,h37Test6_19⟩,h37Test6_20⟩
def h37Bucket6 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 6 xs.toFinset) h37Bucket6 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket5Ok h37Check6
def h37Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,8,12],[0]),([0,1,2,3,4,6],[0,1,3,4,5,6,8,12,15,17],[0]),([0,1,2,3,4,7],[0,1,3,4,5,6,8,12,17,28],[0]),([0,1,2,3,4,8],[0,1,3,4,5,6,8,12,17,31],[0]),([0,1,3,4,9],[0,3,4,5,6,17],[0]),([0,1,2,3,4,9],[0,1,3,4,5,6,8,12,17],[0]),([0,1,2,3,4,10],[0,1,3,4,5,8,12,17],[0]),([0,1,3,4,11],[0,3,4,5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test7_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket6 7 h37Block7_0 = true := by decide +kernel
def h37Block7_1 : List NodeSpec := [([0,1,2,3,4,12],[0,1,3,4,5,6,8,10,12,46],[0]),([0,1,2,3,4,13],[0,1,3,4,5,6,8,12,51],[0]),([0,1,2,3,4,14],[0,1,4,5,6,8,12,56],[0]),([0,1,2,3,4,15],[0,1,3,4,5,6,8,10,12,57],[0]),([0,1,2,3,4,16],[0,1,3,4,5,6,8,12,14,61],[0]),([0,1,2,3,4,17],[0,1,3,4,5,6,8,12,64],[0]),([0,1,2,3,4,18],[0,1,3,5,6,8,12,69],[0]),([0,1,2,3,4,19],[0,1,3,4,5,6,8,12,14,70],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test7_1 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket6 7 h37Block7_1 = true := by decide +kernel
def h37Block7_2 : List NodeSpec := [([0,1,2,3,4,21],[0,1,5,6,8,12,17],[0]),([0,1,2,3,4,22],[0,1,5,6,8,12],[0]),([0,1,2,3,4,24],[0,1,3,5,6,8,10,12,17,44],[0]),([0,1,2,3,4,25],[0,1,3,5,6,8,12,17,78],[0]),([0,1,2,3,4,26],[0,1,3,5,6,8,12,17,83],[0]),([0,1,2,3,4,27],[0,1,3,5,6,8,10,12,17,34],[0]),([0,1,2,3,4,28],[0,1,4,5,6,8,12,14,17,45],[0]),([0,1,2,3,4,29],[0,1,4,5,6,8,12,17,79],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test7_2 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket6 7 h37Block7_2 = true := by decide +kernel
def h37Block7_3 : List NodeSpec := [([0,1,2,3,4,30],[0,1,4,5,6,8,12,17,89],[0]),([0,1,2,3,4,31],[0,1,4,5,6,8,12,14,17,37],[0]),([0,1,2,3,4,32],[0,1,3,5,6,8,12,17],[0]),([0,1,2,3,4,33],[0,1,3,5,6,8,10,12,17],[0]),([0,1,2,3,4,34],[0,1,4,5,6,8,12,17],[0]),([0,1,2,3,4,35],[0,1,4,5,6,8,12,14,17],[0]),([0,1,2,3,4,37],[0,1,3,4,5,6,8,10,12,14,41],[0]),([0,1,2,3,4,38],[0,1,3,5,6,8,12,98],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test7_3 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket6 7 h37Block7_3 = true := by decide +kernel
def h37Block7_4 : List NodeSpec := [([0,1,2,3,4,39],[0,1,3,4,5,6,8,10,12,99],[0]),([0,1,2,3,4,40],[0,1,3,5,6,8,12,14,100],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test7_4 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket6 7 h37Block7_4 = true := by decide +kernel
def h37Nodes7 : List NodeSpec := h37Block7_0 ++ h37Block7_1 ++ h37Block7_2 ++ h37Block7_3 ++ h37Block7_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check7 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket6 7 h37Nodes7 = true := by
  unfold h37Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h37Test7_0,h37Test7_1⟩,h37Test7_2⟩,h37Test7_3⟩,h37Test7_4⟩
def h37Bucket7 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 7 xs.toFinset) h37Bucket7 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket6Ok h37Check7
def h37Block8_0 : List NodeSpec := [([0,1,2,3,4],[5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test8_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket7 8 h37Block8_0 = true := by decide +kernel
def h37Nodes8 : List NodeSpec := h37Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check8 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket7 8 h37Nodes8 = true := h37Test8_0
def h37Bucket8 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 8 xs.toFinset) h37Bucket8 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket7Ok h37Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,2,6),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h37Bucket8Ok (by decide +kernel)
def h44R : List Nat := varsOf 39
def h44G : Nat := 0xfefefefeececececfefefefeecececec
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bound : Lower h44R h44G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,0,2)]) (by decide +kernel) h28Bound
def h45R : List Nat := varsOf 47
def h45G : Nat := 0xfeeafeeaece8ece8feeafeeaece8ece8
def h45Pos : List Nat := [5,6,3,3,10,6,5,10,41,33,13,44,11,37,35,44,10,33,13,38,44,33,38,10,42,5,41,6,14]
def h45Neg : List Nat := [4,4,1,2,9,2,1,2,9,1,12,36,9,36,34,12,12,36,9,34,40,32,36,8,40,0,40,0,12]
def h45Mask : Nat := fullMask 29
def h45Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x626774d,0x41354),(0xcccccccccccccccccccccccccccccccc,0x19c950be,0x840a8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1a5cac63,0x1043ac03),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x15959d90,0x15959510),(0xffffffff00000000ffffffff00000000,0x57aeb00,0x57a6800)]
def h45Steps : List (Nat × Nat × Nat) := [(1,0,1),(1,0,2),(1,1,2),(0,3,7),(0,4,6),(1,5,6),(3,1,2),(1,1,4),(3,1,4),(3,1,6),(3,2,5),(3,0,2),(1,0,3),(3,0,3),(3,0,7),(1,0,11),(2,6,13),(1,1,16),(2,7,18)]
def h45W : BT Decor := buildWiresBT 5 h45Base h45Steps
def h45AutoList : List (List (Nat × Nat)) := [[]]
def h45Autos : BT (List (Nat × Nat)) := btOfList 1 h45AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Pairs : goodPairs h45G h45Pos h45Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45BaseOk : ∀ x ∈ h45Base, faithful h45Pos h45Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45WOk : btAll (fun x => faithful h45Pos h45Neg x ∧ x.1 < 2^128) h45W := buildWiresBT_faithful h45BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h45G = h45G) h45Autos := btAll_ofList (autos_of (by decide +kernel))
def h45SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 2 8,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,5),some (subcubeFast 32 0,5),some (subcubeFast 40 0,4)]
def h45Slices : BT (Option (Nat × Nat)) := btOfList 4 h45SliceList
def h45Specs : List PoolSpec := [(2,[]),(4,[]),(3,[]),(5,[]),(0,[(1,0,1)]),(1,[(1,0,1)]),(6,[]),(7,[]),(0,[]),(8,[]),(1,[]),(1,[(1,0,2)]),(1,[(3,0,2)]),(4,[(1,0,3)]),(1,[(1,0,3)]),(8,[(1,0,3)]),(4,[(3,0,3)]),(1,[(3,0,3)]),(9,[]),(8,[(3,0,3)]),(0,[(1,1,2)]),(0,[(3,1,2)]),(2,[(1,1,4)]),(0,[(1,1,4)]),(7,[(1,1,4)]),(2,[(3,1,4)]),(0,[(3,1,4)]),(7,[(3,1,4)])]
def h45Pools : BT (Option BoundPool) := buildPoolsBT 5 h45W h45R h45Slices h45Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice9 : Slice h45R h45G (subcubeFast 40 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice8 : Slice h45R h45G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice7 : Slice h45R h45G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice6 : Slice h45R h45G (subcubeFast 4 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice5 : Slice h45R h45G (subcubeFast 2 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice4 : Slice h45R h45G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice3 : Slice h45R h45G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice2 : Slice h45R h45G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice1 : Slice h45R h45G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice0 : Slice h45R h45G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h45R h45G p.1 p.2) h45Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h45R h45G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h45Slice0) (forall_cons (fun _ h => by cases h; exact h45Slice1) (forall_cons (fun _ h => by cases h; exact h45Slice2) (forall_cons (fun _ h => by cases h; exact h45Slice3) (forall_cons (fun _ h => by cases h; exact h45Slice4) (forall_cons (fun _ h => by cases h; exact h45Slice5) (forall_cons (fun _ h => by cases h; exact h45Slice6) (forall_cons (fun _ h => by cases h; exact h45Slice7) (forall_cons (fun _ h => by cases h; exact h45Slice8) (forall_cons (fun _ h => by cases h; exact h45Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h45R h45G c) h45Pools := buildPoolsBT_sound h45SlicesOk
def h45Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h45G (4 - 1) xs.toFinset) h45Empty := trivial
def h45Block4_0 : List NodeSpec := [([3,4,5,6,7],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,4,23],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Test4_0 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Empty 4 h45Block4_0 = true := by decide +kernel
def h45Nodes4 : List NodeSpec := h45Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Check4 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Empty 4 h45Nodes4 = true := h45Test4_0
def h45Bucket4 : BT (List (List Nat)) := buildBucketsBT h45W h45Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h45G 4 xs.toFinset) h45Bucket4 := buildBucketsBT_sound (by decide) h45Pairs h45WOk h45PoolsOk h45AutosOk h45EmptyOk h45Check4
def h45Block5_0 : List NodeSpec := [([1,2,3,4,5,6],[1,2],[0]),([0,2,3,4,5,7],[0,3],[0]),([0,1,2,3,4,10],[7,8,9,10],[0]),([0,1,2,3,4,15],[],[0]),([0,1,3,4,6,7],[0],[0]),([0,1,3,4,6,11],[],[0]),([0,1,2,3,6,13],[9],[0]),([0,1,2,3,4,14],[9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Test5_0 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Bucket4 5 h45Block5_0 = true := by decide +kernel
def h45Block5_1 : List NodeSpec := [([0,1,2,3,6,9],[10],[0]),([0,1,3,4,7,16],[],[0]),([0,1,2,3,13,16],[],[0]),([0,1,2,3,4,22],[7,8],[0]),([0,1,2,4,7,18],[7],[0]),([0,1,2,4,11,18],[],[0]),([0,1,2,3,4,19],[7,8],[0]),([0,1,2,4,7,8],[8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Test5_1 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Bucket4 5 h45Block5_1 = true := by decide +kernel
def h45Block5_2 : List NodeSpec := [([0,1,2,3,4,20],[9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Test5_2 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Bucket4 5 h45Block5_2 = true := by decide +kernel
def h45Nodes5 : List NodeSpec := h45Block5_0 ++ h45Block5_1 ++ h45Block5_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Check5 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Bucket4 5 h45Nodes5 = true := by
  unfold h45Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h45Test5_0,h45Test5_1⟩,h45Test5_2⟩
def h45Bucket5 : BT (List (List Nat)) := buildBucketsBT h45W h45Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h45G 5 xs.toFinset) h45Bucket5 := buildBucketsBT_sound (by decide) h45Pairs h45WOk h45PoolsOk h45AutosOk h45Bucket4Ok h45Check5
def h45Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9,10],[0]),([0,1,2,3,4,6],[0,1,2,6,7,8,9,10,11],[0]),([0,1,2,3,4,16],[0,1,2,6,7,8,9,10,12],[0]),([0,1,2,4,17],[0,2,3,7,8,13,14,15],[0]),([0,1,2,4,18],[0,2,7,16,17,18,19],[0]),([0,1,2,3,4,7],[0,1,3,6,7,8,9,10,20],[0]),([0,1,2,3,4,11],[0,1,3,6,7,8,9,10,21],[0]),([0,1,2,3,12],[1,2,9,10,22,23,24],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Test6_0 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Bucket5 6 h45Block6_0 = true := by decide +kernel
def h45Block6_1 : List NodeSpec := [([0,1,2,3,13],[1,3,9,18,25,26,27],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Test6_1 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Bucket5 6 h45Block6_1 = true := by decide +kernel
def h45Nodes6 : List NodeSpec := h45Block6_0 ++ h45Block6_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Check6 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Bucket5 6 h45Nodes6 = true := by
  unfold h45Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h45Test6_0,h45Test6_1⟩
def h45Bucket6 : BT (List (List Nat)) := buildBucketsBT h45W h45Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h45G 6 xs.toFinset) h45Bucket6 := buildBucketsBT_sound (by decide) h45Pairs h45WOk h45PoolsOk h45AutosOk h45Bucket5Ok h45Check6
def h45Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,7,8,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Test7_0 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Bucket6 7 h45Block7_0 = true := by decide +kernel
def h45Nodes7 : List NodeSpec := h45Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Check7 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Bucket6 7 h45Nodes7 = true := h45Test7_0
def h45Bucket7 : BT (List (List Nat)) := buildBucketsBT h45W h45Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h45G 7 xs.toFinset) h45Bucket7 := buildBucketsBT_sound (by decide) h45Pairs h45WOk h45PoolsOk h45AutosOk h45Bucket6Ok h45Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bound : Lower h45R h45G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,2,10),(VAR 5,1,33)]) (by decide +kernel) h45Bucket7Ok (by decide +kernel)
def h46R : List Nat := varsOf 55
def h46G : Nat := 0xfefeeaeaecece8e8fefeeaeaecece8e8
def h46Pos : List Nat := [5,6,3,3,18,6,5,18,49,33,21,52,19,37,35,52,18,33,21,38,52,33,38,18,50,5,49,6,22]
def h46Neg : List Nat := [4,4,1,2,17,2,1,2,17,1,20,36,17,36,34,20,20,36,17,34,48,32,36,16,48,0,48,0,20]
def h46Mask : Nat := fullMask 29
def h46Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x626774d,0x41354),(0xcccccccccccccccccccccccccccccccc,0x19c950be,0x840a8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1a5cac63,0x1043ac03),(0xffff0000ffff0000ffff0000ffff0000,0x15959d90,0x15959510),(0xffffffff00000000ffffffff00000000,0x57aeb00,0x57a6800)]
def h46Steps : List (Nat × Nat × Nat) := [(1,0,1),(1,0,2),(1,1,2),(0,3,7),(0,4,6),(1,5,6),(3,1,2),(1,1,4),(3,1,4),(3,1,6),(3,2,5),(3,0,2),(1,0,3),(3,0,3),(3,0,7),(1,0,11),(2,6,13),(1,1,16),(2,7,18)]
def h46W : BT Decor := buildWiresBT 5 h46Base h46Steps
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
def h46SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 2 16,4),some (subcubeFast 4 0,4),some (subcubeFast 16 0,5),some (subcubeFast 32 0,5),some (subcubeFast 48 0,4)]
def h46Slices : BT (Option (Nat × Nat)) := btOfList 4 h46SliceList
def h46Specs : List PoolSpec := [(2,[]),(4,[]),(3,[]),(5,[]),(0,[(1,0,1)]),(1,[(1,0,1)]),(6,[]),(7,[]),(0,[]),(8,[]),(1,[]),(1,[(1,0,2)]),(1,[(3,0,2)]),(4,[(1,0,3)]),(1,[(1,0,3)]),(8,[(1,0,3)]),(4,[(3,0,3)]),(1,[(3,0,3)]),(9,[]),(8,[(3,0,3)]),(0,[(1,1,2)]),(0,[(3,1,2)]),(2,[(1,1,4)]),(0,[(1,1,4)]),(7,[(1,1,4)]),(2,[(3,1,4)]),(0,[(3,1,4)]),(7,[(3,1,4)])]
def h46Pools : BT (Option BoundPool) := buildPoolsBT 5 h46W h46R h46Slices h46Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice9 : Slice h46R h46G (subcubeFast 48 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice8 : Slice h46R h46G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice7 : Slice h46R h46G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice6 : Slice h46R h46G (subcubeFast 4 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice5 : Slice h46R h46G (subcubeFast 2 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice4 : Slice h46R h46G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice3 : Slice h46R h46G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice2 : Slice h46R h46G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice1 : Slice h46R h46G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice0 : Slice h46R h46G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h46R h46G p.1 p.2) h46Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h46R h46G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h46Slice0) (forall_cons (fun _ h => by cases h; exact h46Slice1) (forall_cons (fun _ h => by cases h; exact h46Slice2) (forall_cons (fun _ h => by cases h; exact h46Slice3) (forall_cons (fun _ h => by cases h; exact h46Slice4) (forall_cons (fun _ h => by cases h; exact h46Slice5) (forall_cons (fun _ h => by cases h; exact h46Slice6) (forall_cons (fun _ h => by cases h; exact h46Slice7) (forall_cons (fun _ h => by cases h; exact h46Slice8) (forall_cons (fun _ h => by cases h; exact h46Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h46R h46G c) h46Pools := buildPoolsBT_sound h46SlicesOk
def h46Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G (4 - 1) xs.toFinset) h46Empty := trivial
def h46Block4_0 : List NodeSpec := [([3,4,5,6,7],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,4,23],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test4_0 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Empty 4 h46Block4_0 = true := by decide +kernel
def h46Nodes4 : List NodeSpec := h46Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Check4 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Empty 4 h46Nodes4 = true := h46Test4_0
def h46Bucket4 : BT (List (List Nat)) := buildBucketsBT h46W h46Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G 4 xs.toFinset) h46Bucket4 := buildBucketsBT_sound (by decide) h46Pairs h46WOk h46PoolsOk h46AutosOk h46EmptyOk h46Check4
def h46Block5_0 : List NodeSpec := [([1,2,3,4,5,6],[1,2],[0]),([0,2,3,4,5,7],[0,3],[0]),([0,1,2,3,4,10],[7,8,9,10],[0]),([0,1,2,3,4,15],[],[0]),([0,1,3,4,6,7],[0],[0]),([0,1,3,4,6,11],[],[0]),([0,1,2,3,6,13],[9],[0]),([0,1,2,3,4,14],[9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_0 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_0 = true := by decide +kernel
def h46Block5_1 : List NodeSpec := [([0,1,2,3,6,9],[10],[0]),([0,1,3,4,7,16],[],[0]),([0,1,2,3,13,16],[],[0]),([0,1,2,3,4,22],[7,8],[0]),([0,1,2,4,7,18],[7],[0]),([0,1,2,4,11,18],[],[0]),([0,1,2,3,4,19],[7,8],[0]),([0,1,2,4,7,8],[8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_1 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_1 = true := by decide +kernel
def h46Block5_2 : List NodeSpec := [([0,1,2,3,4,20],[9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test5_2 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Block5_2 = true := by decide +kernel
def h46Nodes5 : List NodeSpec := h46Block5_0 ++ h46Block5_1 ++ h46Block5_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Check5 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket4 5 h46Nodes5 = true := by
  unfold h46Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h46Test5_0,h46Test5_1⟩,h46Test5_2⟩
def h46Bucket5 : BT (List (List Nat)) := buildBucketsBT h46W h46Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G 5 xs.toFinset) h46Bucket5 := buildBucketsBT_sound (by decide) h46Pairs h46WOk h46PoolsOk h46AutosOk h46Bucket4Ok h46Check5
def h46Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9,10],[0]),([0,1,2,3,4,6],[0,1,2,6,7,8,9,10,11],[0]),([0,1,2,3,4,16],[0,1,2,6,7,8,9,10,12],[0]),([0,1,2,4,17],[0,2,3,7,8,13,14,15],[0]),([0,1,2,4,18],[0,2,7,16,17,18,19],[0]),([0,1,2,3,4,7],[0,1,3,6,7,8,9,10,20],[0]),([0,1,2,3,4,11],[0,1,3,6,7,8,9,10,21],[0]),([0,1,2,3,12],[1,2,9,10,22,23,24],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_0 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_0 = true := by decide +kernel
def h46Block6_1 : List NodeSpec := [([0,1,2,3,13],[1,3,9,18,25,26,27],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_1 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Block6_1 = true := by decide +kernel
def h46Nodes6 : List NodeSpec := h46Block6_0 ++ h46Block6_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Check6 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket5 6 h46Nodes6 = true := by
  unfold h46Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h46Test6_0,h46Test6_1⟩
def h46Bucket6 : BT (List (List Nat)) := buildBucketsBT h46W h46Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G 6 xs.toFinset) h46Bucket6 := buildBucketsBT_sound (by decide) h46Pairs h46WOk h46PoolsOk h46AutosOk h46Bucket5Ok h46Check6
def h46Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,7,8,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test7_0 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket6 7 h46Block7_0 = true := by decide +kernel
def h46Nodes7 : List NodeSpec := h46Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Check7 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Bucket6 7 h46Nodes7 = true := h46Test7_0
def h46Bucket7 : BT (List (List Nat)) := buildBucketsBT h46W h46Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G 7 xs.toFinset) h46Bucket7 := buildBucketsBT_sound (by decide) h46Pairs h46WOk h46PoolsOk h46AutosOk h46Bucket6Ok h46Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 4,2,18),(VAR 5,1,33)]) (by decide +kernel) h46Bucket7Ok (by decide +kernel)
def h47R : List Nat := varsOf 59
def h47G : Nat := 0xffeeeecceeeeeeccffeeeecceeeeeecc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h47Bound : Lower h47R h47G 6 := lift_of (z := 2) (o := 32) (essPairs := [(VAR 1,0,2),(VAR 5,24,56)]) (by decide +kernel) h6Bound
def h48R : List Nat := varsOf 61
def h48G : Nat := 0xfffafafafffafaf0fffafafafffafaf0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bound : Lower h48R h48G 6 := lift_of (z := 36) (o := 0) (essPairs := [(VAR 2,0,4),(VAR 5,1,33)]) (by decide +kernel) h6Bound
def h49R : List Nat := varsOf 62
def h49G : Nat := 0xffffffccfcfcfcc0ffffffccfcfcfcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bound : Lower h49R h49G 6 := lift_of (z := 12) (o := 0) (essPairs := [(VAR 2,2,6),(VAR 3,2,10)]) (by decide +kernel) h18Bound
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfeeaeac8ece8e8c0feeaeac8ece8e8c0
def h0Pos : List Nat := [6,13,7,11,6,6,7,19,26,11,26,19,60,35,35,7,13,13,21,21,38,26,60,11,41,60,49,60,19,38,35,41,41,21,21,19,58,27,29,11,14,46,14,13,11,58,49,19,22,54,22,29,49,57,30,58]
def h0Neg : List Nat := [4,12,5,10,5,2,3,18,18,3,10,3,28,3,34,4,5,9,5,17,34,24,56,9,33,52,33,44,17,36,33,9,40,20,28,1,42,25,25,2,12,44,10,28,1,50,17,2,20,52,18,28,48,56,28,56]
def h0Mask : Nat := fullMask 56
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x38d8efd58feace,0x5068d58f2a54),(0xcccccccccccccccccccccccccccccccc,0xc7b7b870b0effd,0x4a49000106fe8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x4f0f462a5f9077,0x4b0b062a059017),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xe83ff18be3170a,0xe80f7588e2140a),(0xffff0000ffff0000ffff0000ffff0000,0xffe07e1e6c1d80,0xff686612681180),(0xffffffff00000000ffffffff00000000,0xb26211ef507000,0xb222116f504000)]
def h0Steps : List (Nat × Nat × Nat) := [(1,0,1),(2,0,1),(0,0,3),(3,0,3),(0,0,4),(3,0,4),(1,2,6),(3,2,6),(1,2,7),(3,2,7),(0,3,4),(3,1,3),(3,1,4),(1,0,16),(2,0,16),(1,1,16),(1,2,16),(1,0,18),(2,0,18),(1,1,8),(1,2,8),(1,2,18),(2,4,8),(1,1,9),(1,2,9),(1,0,17),(2,0,17),(1,1,10),(1,2,10),(1,2,17),(2,3,10),(1,1,11),(1,2,11)]
def h0W : BT Decor := buildWiresBT 6 h0Base h0Steps
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
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,6),some (subcubeFast 0 2,6),some (subcubeFast 0 4,6),some (subcubeFast 0 8,8),some (subcubeFast 0 16,8),some (subcubeFast 0 24,5),some (subcubeFast 0 32,9),some (subcubeFast 1 0,6),some (subcubeFast 1 8,5),some (subcubeFast 1 16,5),some (subcubeFast 2 0,8),some (subcubeFast 2 4,5),some (subcubeFast 2 8,5),some (subcubeFast 2 16,5),some (subcubeFast 2 24,4),some (subcubeFast 4 0,9),some (subcubeFast 8 0,7),some (subcubeFast 8 1,5),some (subcubeFast 12 1,4),some (subcubeFast 16 0,7),some (subcubeFast 16 1,5),some (subcubeFast 20 1,4),some (subcubeFast 32 0,8)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 5 h0SliceList
def h0Specs : List PoolSpec := [(10,[]),(15,[(1,0,1),(2,0,1)]),(7,[]),(3,[(1,0,1),(2,0,1)]),(4,[(1,0,1),(2,0,1)]),(6,[(1,0,1),(2,0,1)]),(8,[]),(0,[]),(15,[]),(15,[(1,0,1)]),(15,[(2,0,1)]),(17,[]),(3,[(1,0,1)]),(20,[]),(4,[(1,0,1)]),(6,[(1,0,1)]),(1,[]),(2,[]),(16,[]),(3,[]),(19,[]),(4,[]),(22,[]),(6,[]),(3,[(2,0,1)]),(4,[(2,0,1)]),(9,[]),(6,[(2,0,1)]),(10,[(0,3,4)]),(15,[(2,0,1),(0,3,4)]),(16,[(2,0,1)]),(19,[(2,0,1)]),(14,[]),(15,[(0,3,4)]),(18,[]),(11,[]),(22,[(0,3,4)]),(6,[(0,3,4)]),(22,[(2,0,1)]),(5,[]),(10,[(0,0,3)]),(15,[(0,0,3)]),(4,[(0,0,3)]),(6,[(0,0,3)]),(3,[(3,1,4)]),(16,[(3,1,4)]),(19,[(0,0,3)]),(15,[(0,0,3),(3,1,4)]),(15,[(3,1,4)]),(21,[]),(22,[(3,1,4)]),(6,[(3,1,4)]),(22,[(0,0,3)]),(13,[]),(15,[(0,0,3),(1,1,8)]),(3,[(1,1,8)]),(4,[(0,0,3),(1,1,8)]),(6,[(0,0,3),(1,1,8)]),(10,[(0,0,3),(2,4,8)]),(15,[(0,0,3),(2,4,8)]),(3,[(2,4,8)]),(6,[(0,0,3),(2,4,8)]),(10,[(3,0,3)]),(15,[(3,0,3)]),(4,[(3,0,3)]),(6,[(3,0,3)]),(15,[(3,0,3),(1,1,9)]),(3,[(1,1,9)]),(4,[(3,0,3),(1,1,9)]),(6,[(3,0,3),(1,1,9)]),(10,[(0,0,4)]),(15,[(0,0,4)]),(3,[(0,0,4)]),(6,[(0,0,4)]),(4,[(3,1,3)]),(19,[(3,1,3)]),(16,[(0,0,4)]),(15,[(0,0,4),(3,1,3)]),(15,[(3,1,3)]),(22,[(3,1,3)]),(6,[(3,1,3)]),(22,[(0,0,4)]),(12,[]),(15,[(0,0,4),(1,1,10)]),(3,[(0,0,4),(1,1,10)]),(4,[(1,1,10)]),(6,[(0,0,4),(1,1,10)]),(10,[(0,0,4),(2,3,10)]),(15,[(0,0,4),(2,3,10)]),(4,[(2,3,10)]),(6,[(0,0,4),(2,3,10)]),(10,[(3,0,4)]),(15,[(3,0,4)]),(3,[(3,0,4)]),(6,[(3,0,4)]),(15,[(3,0,4),(1,1,11)]),(3,[(3,0,4),(1,1,11)]),(4,[(1,1,11)]),(6,[(3,0,4),(1,1,11)]),(10,[(1,0,17)]),(15,[(3,1,3),(1,0,17)]),(3,[(1,0,17)]),(4,[(3,1,3),(1,0,17)]),(6,[(3,1,3),(1,0,17)]),(10,[(2,0,17)]),(15,[(3,1,3),(2,0,17)]),(3,[(2,0,17)]),(4,[(3,1,3),(2,0,17)]),(6,[(3,1,3),(2,0,17)]),(10,[(1,0,18)]),(15,[(3,1,4),(1,0,18)]),(3,[(3,1,4),(1,0,18)]),(4,[(1,0,18)]),(6,[(3,1,4),(1,0,18)]),(10,[(2,0,18)]),(15,[(3,1,4),(2,0,18)]),(3,[(3,1,4),(2,0,18)]),(4,[(2,0,18)]),(6,[(3,1,4),(2,0,18)]),(10,[(0,3,4),(1,0,16)]),(15,[(0,3,4),(1,0,16)]),(3,[(1,0,16)]),(4,[(1,0,16)]),(6,[(0,3,4),(1,0,16)]),(10,[(0,3,4),(2,0,16)]),(15,[(0,3,4),(2,0,16)]),(3,[(2,0,16)]),(4,[(2,0,16)]),(6,[(0,3,4),(2,0,16)]),(15,[(0,3,4),(1,1,16)]),(3,[(1,1,16)]),(4,[(1,1,16)]),(6,[(0,3,4),(1,1,16)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 8 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 32 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 20 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 16 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 12 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 8 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 4 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 2 24) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 2 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 2 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 2 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 2 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 1 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 1 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 1 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 0 32) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 24) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 16) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 8) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (8 - 1) xs.toFinset) h0Empty := trivial
def h0Block8_0 : List NodeSpec := [([0,2,3,4,5,6,7],[0,1,2,3,4,5,6,7,8,9,10],[0]),([0,1,2,3,4,5,12],[7,9,16,17,18,19,20,21,22,23],[0]),([0,1,2,3,4,5,13],[0,2,7,8,9,16,18,19,20,21,22,23],[0]),([0,1,2,3,4,5,14],[0,2,7,8,10,16,18,19,20,21,22,23],[0]),([0,1,2,3,4,5,15],[2,10,16,17,18,19,20,21,22,23],[0]),([0,1,2,3,4,5,7,16],[0,2,6,7,10,11,16,18,19,20,21,24,25,27,28,29,30,31,32,33,34,35,36,37,38,39],[0]),([0,1,2,3,4,5,8,18],[0,2,7,13,16,18,19,20,21,26,35,40,41,42,43,44,45,46,47,48,49,50,51,52,53],[0]),([0,1,2,3,4,5,25],[0,2,8,11,16,17,18,19,20,21,22,23,40,54,55,56,57],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := [([0,1,2,3,4,5,26],[0,8,16,18,19,20,21,22,23,41],[0]),([0,1,2,3,5,28],[2,11,20,42,58,59,60,61],[0]),([0,1,2,3,4,5,29],[0,6,7,8,16,17,18,19,20,21,22,23,62,66,67,68,69],[0]),([0,1,2,3,4,5,30],[0,8,16,18,19,20,21,22,23,63],[0]),([0,1,2,3,4,5,10,17],[0,2,6,7,11,16,18,19,20,21,34,35,70,71,72,73,74,75,76,77,78,79,80,81,82],[0]),([0,1,2,3,4,5,33],[0,2,6,8,16,17,18,19,20,21,22,23,70,83,84,85,86],[0]),([0,1,2,3,4,5,34],[0,8,16,18,19,20,21,22,23,71],[0]),([0,1,2,4,5,36],[2,11,18,72,87,88,89,90],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 8 h0Block8_1 = true := by decide +kernel
def h0Block8_2 : List NodeSpec := [([0,1,2,3,4,5,37],[0,7,8,11,16,17,18,19,20,21,22,23,91,95,96,97,98],[0]),([0,1,2,3,4,5,38],[0,8,16,18,19,20,21,22,23,92],[0]),([0,1,2,3,4,5,31],[0,7,8,17,18,19,20,21,22,23,99,100,101,102,103],[0]),([0,1,2,3,4,5,32],[0,2,8,17,18,19,20,21,22,23,104,105,106,107,108],[0]),([0,1,2,3,4,5,35],[0,2,7,8,18,19,20,21,22,23,78],[0]),([0,1,2,3,4,5,23],[0,7,8,17,18,19,20,21,22,23,109,110,111,112,113],[0]),([0,1,2,3,4,5,24],[0,2,8,17,18,19,20,21,22,23,114,115,116,117,118],[0]),([0,1,2,3,4,5,27],[0,2,7,8,18,19,20,21,22,23,48],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 8 h0Block8_2 = true := by decide +kernel
def h0Block8_3 : List NodeSpec := [([0,1,2,3,4,5,19],[0,7,8,16,17,18,19,20,21,22,23,32,119,120,121,122,123],[0]),([0,1,2,3,4,5,20],[0,2,8,11,16,17,18,19,21,22,23,124,125,126,127,128],[0]),([0,1,2,3,4,5,21],[0,2,7,8,16,17,18,19,21,22,23,28,129,130,131,132],[0]),([0,1,2,3,4,5,22],[0,2,7,8,16,18,19,21,22,23,33],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 8 h0Block8_3 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1 ++ h0Block8_2 ++ h0Block8_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 8 h0Nodes8 = true := by
  unfold h0Nodes8 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h0Test8_0,h0Test8_1⟩,h0Test8_2⟩,h0Test8_3⟩
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check8
def h0Block9_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,7,8,9,11,12,13,14,15,18,19,20,21,22,23],[0]),([0,1,2,3,4,5,7],[0,2,6,8,10,18,19,20,21,22,23,24,25,26,27],[0]),([0,1,2,3,4,5,8],[0,2,8,11,18,19,20,21,22,23,40,41,42,43],[0]),([0,1,2,3,4,5,9],[0,6,7,8,13,18,19,20,21,22,23,62,63,64,65],[0]),([0,1,2,3,4,5,10],[0,2,6,8,13,18,19,20,21,22,23,70,71,72,73],[0]),([0,1,2,3,4,5,11],[0,7,8,11,18,19,20,21,22,23,26,91,92,93,94],[0]),([0,1,2,3,4,5,17],[0,8,11,18,19,20,21,22,23,74,78,80],[0]),([0,1,2,3,4,5,18],[0,8,13,18,19,20,21,22,23,44,48,51],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := [([0,1,2,3,4,5,16],[0,8,11,18,19,20,21,22,23,28,33,37],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := by
  unfold h0Nodes9 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h0Test9_0,h0Test9_1⟩
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := [([0,1,2,3,4,5],[0,8,19,21,23],[0])]
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
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bound : Lower h0R h0G 11 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,3,11),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h0Bucket10Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 13]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 16]⟩]
def wo : Nat := 17
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276808392 * 2 ^ 32 + 3974686912) ||| ((4276808392 * 2 ^ 32 + 3974686912) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4276808392 * 2 ^ 32 + 3974686912) ||| ((4276808392 * 2 ^ 32 + 3974686912) <<< 64)) 11 := h0Bound
end PEqualNP.Outside.L_meta_42056
theorem PEqualNP.Outside.L_meta_42056 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 3974686912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 3974686912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_42056.table2_of_lower (4276808392 * 2 ^ 32 + 3974686912) (by decide) (by decide) (by decide) (by decide)
    11 PEqualNP.Outside.L_meta_42056.low_root
    PEqualNP.Outside.L_meta_42056.wit PEqualNP.Outside.L_meta_42056.wo (by decide)
    PEqualNP.Outside.L_meta_42056.wit_mono PEqualNP.Outside.L_meta_42056.wit_eval s hcs
