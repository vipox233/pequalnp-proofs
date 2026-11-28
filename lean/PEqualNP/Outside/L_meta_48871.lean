import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_48871
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
def h1R : List Nat := varsOf 23
def h1G : Nat := 0xeaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8
def h1Pos : List Nat := [5,22,5,17,3,5,22,17,22,3,3,3,5,3,17,7,7,19,19,21,21]
def h1Neg : List Nat := [4,20,6,16,2,1,18,1,6,1,0,6,0,18,0,6,1,18,1,20,1]
def h1Mask : Nat := fullMask 21
def h1Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xcccccccccccccccccccccccccccccccc,0x7af52,0x2a954),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x199167,0x88907),(0xffff0000ffff0000ffff0000ffff0000,0x1e41ca,0xa204a)]
def h1Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(0,1,28),(2,2,4),(1,3,4),(0,1,31),(2,3,4),(0,2,5),(1,1,34),(3,2,5),(0,3,5),(1,1,37),(3,3,5),(2,1,8),(1,3,8),(0,2,41),(2,3,8),(3,1,9),(0,3,9),(1,2,45),(3,3,9),(2,1,12),(2,2,12),(3,1,13),(3,2,13),(1,3,18),(0,1,52),(2,3,18),(1,2,54),(1,3,19),(0,2,56),(2,3,19),(1,1,58),(1,2,22),(0,1,60),(2,2,23),(1,1,62)]
def h1W : BT Decor := buildWiresBT 6 h1Base h1Steps
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
def h1Block3_0 : List NodeSpec := [([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,2,31],[],[0]),([0,1,2,33],[],[0]),([0,1,3,34],[],[0]),([0,1,3,36],[],[0]),([0,1,2,37],[],[0]),([0,1,2,39],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test3_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 3 h1Block3_0 = true := by decide +kernel
def h1Block3_1 : List NodeSpec := [([0,2,3,35],[],[0]),([0,2,3,40],[],[0]),([0,1,2,41],[],[0]),([0,1,2,43],[],[0]),([0,2,3,29],[],[0]),([0,2,3,44],[],[0]),([0,1,2,45],[],[0]),([0,1,2,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test3_1 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 3 h1Block3_1 = true := by decide +kernel
def h1Block3_2 : List NodeSpec := [([0,2,3,38],[],[0]),([0,2,3,48],[],[0]),([0,1,3,46],[],[0]),([0,1,3,49],[],[0]),([0,2,3,32],[],[0]),([0,2,3,50],[],[0]),([0,1,3,42],[],[0]),([0,1,3,51],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test3_2 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 3 h1Block3_2 = true := by decide +kernel
def h1Block3_3 : List NodeSpec := [([0,3,16,17],[],[0]),([0,1,2,52],[],[0]),([0,1,2,54],[],[0]),([0,1,2,56],[],[0]),([0,1,2,58],[],[0]),([0,2,20,21],[],[0]),([0,1,3,60],[],[0]),([0,1,3,57],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test3_3 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 3 h1Block3_3 = true := by decide +kernel
def h1Block3_4 : List NodeSpec := [([0,1,3,55],[],[0]),([0,1,3,62],[],[0]),([0,1,24,25],[],[0]),([0,2,3,63],[],[0]),([0,2,3,53],[],[0]),([0,2,3,59],[],[0]),([0,2,3,61],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test3_4 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 3 h1Block3_4 = true := by decide +kernel
def h1Nodes3 : List NodeSpec := h1Block3_0 ++ h1Block3_1 ++ h1Block3_2 ++ h1Block3_3 ++ h1Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check3 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 3 h1Nodes3 = true := by
  unfold h1Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h1Test3_0,h1Test3_1⟩,h1Test3_2⟩,h1Test3_3⟩,h1Test3_4⟩
def h1Bucket3 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 3 xs.toFinset) h1Bucket3 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1EmptyOk h1Check3
def h1Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test4_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket3 4 h1Block4_0 = true := by decide +kernel
def h1Block4_1 : List NodeSpec := [([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0]),([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test4_1 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket3 4 h1Block4_1 = true := by decide +kernel
def h1Block4_2 : List NodeSpec := [([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0]),([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test4_2 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket3 4 h1Block4_2 = true := by decide +kernel
def h1Nodes4 : List NodeSpec := h1Block4_0 ++ h1Block4_1 ++ h1Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check4 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket3 4 h1Nodes4 = true := by
  unfold h1Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h1Test4_0,h1Test4_1⟩,h1Test4_2⟩
def h1Bucket4 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 4 xs.toFinset) h1Bucket4 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket3Ok h1Check4
def h1Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_0 = true := by decide +kernel
def h1Nodes5 : List NodeSpec := h1Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check5 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Nodes5 = true := h1Test5_0
def h1Bucket5 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 5 xs.toFinset) h1Bucket5 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket4Ok h1Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bound : Lower h1R h1G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 4,1,17)]) (by decide +kernel) h1Bucket5Ok (by decide +kernel)
def h3R : List Nat := varsOf 54
def h3G : Nat := 0xfffffcfcc0c00000fffffcfcc0c00000
def h3Pos : List Nat := [34,36,22,48,34,48,38,22,22,22,36,50,22,36,34,52,22,34,36,34,48]
def h3Neg : List Nat := [32,32,6,16,2,32,6,16,20,18,4,18,4,6,0,20,2,6,0,18,0]
def h3Mask : Nat := fullMask 21
def h3Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xb5bd5,0xb2a54),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x5b7c6,0x2b544),(0xffff0000ffff0000ffff0000ffff0000,0x119bac,0x88b88),(0xffffffff00000000ffffffff00000000,0x1eec7b,35)]
def h3Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(1,2,10),(0,0,28),(2,2,10),(1,1,30),(1,2,11),(0,1,32),(2,2,11),(1,0,34),(1,1,14),(0,0,36),(2,1,15),(1,0,38),(1,1,16),(0,0,40),(2,1,16),(1,2,16),(0,0,43),(2,2,16),(0,1,17),(1,0,46),(3,1,17),(0,2,17),(1,0,49),(3,2,17),(2,0,24),(1,2,24),(0,1,53),(2,2,24),(3,0,25),(0,2,25),(1,1,57),(3,2,25),(2,0,6),(2,1,6),(3,0,7),(3,1,7)]
def h3W : BT Decor := buildWiresBT 6 h3Base h3Steps
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
def h3Block3_0 : List NodeSpec := [([2,3,4,5],[],[0]),([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,3,32],[],[0]),([0,1,3,34],[],[0]),([1,3,12,13],[],[0]),([0,2,3,36],[],[0]),([0,2,3,33],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test3_0 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 3 h3Block3_0 = true := by decide +kernel
def h3Block3_1 : List NodeSpec := [([0,2,3,31],[],[0]),([0,2,3,38],[],[0]),([0,2,3,40],[],[0]),([0,2,3,42],[],[0]),([0,1,3,43],[],[0]),([0,1,3,45],[],[0]),([0,2,3,46],[],[0]),([0,2,3,48],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test3_1 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 3 h3Block3_1 = true := by decide +kernel
def h3Block3_2 : List NodeSpec := [([0,1,3,49],[],[0]),([0,1,3,51],[],[0]),([0,3,20,21],[],[0]),([1,2,3,39],[],[0]),([1,2,3,29],[],[0]),([1,2,3,35],[],[0]),([1,2,3,37],[],[0]),([1,2,3,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test3_2 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 3 h3Block3_2 = true := by decide +kernel
def h3Block3_3 : List NodeSpec := [([1,2,3,52],[],[0]),([0,1,3,53],[],[0]),([0,1,3,55],[],[0]),([1,2,3,41],[],[0]),([1,2,3,56],[],[0]),([0,1,3,57],[],[0]),([0,1,3,59],[],[0]),([1,2,3,50],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test3_3 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 3 h3Block3_3 = true := by decide +kernel
def h3Block3_4 : List NodeSpec := [([1,2,3,60],[],[0]),([0,2,3,58],[],[0]),([0,2,3,61],[],[0]),([1,2,3,44],[],[0]),([1,2,3,62],[],[0]),([0,2,3,54],[],[0]),([0,2,3,63],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test3_4 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 3 h3Block3_4 = true := by decide +kernel
def h3Nodes3 : List NodeSpec := h3Block3_0 ++ h3Block3_1 ++ h3Block3_2 ++ h3Block3_3 ++ h3Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Check3 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 3 h3Nodes3 = true := by
  unfold h3Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h3Test3_0,h3Test3_1⟩,h3Test3_2⟩,h3Test3_3⟩,h3Test3_4⟩
def h3Bucket3 : BT (List (List Nat)) := buildBucketsBT h3W h3Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G 3 xs.toFinset) h3Bucket3 := buildBucketsBT_sound (by decide) h3Pairs h3WOk h3PoolsOk h3AutosOk h3EmptyOk h3Check3
def h3Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0]),([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test4_0 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket3 4 h3Block4_0 = true := by decide +kernel
def h3Block4_1 : List NodeSpec := [([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0]),([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test4_1 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket3 4 h3Block4_1 = true := by decide +kernel
def h3Block4_2 : List NodeSpec := [([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test4_2 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket3 4 h3Block4_2 = true := by decide +kernel
def h3Nodes4 : List NodeSpec := h3Block4_0 ++ h3Block4_1 ++ h3Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Check4 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket3 4 h3Nodes4 = true := by
  unfold h3Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h3Test4_0,h3Test4_1⟩,h3Test4_2⟩
def h3Bucket4 : BT (List (List Nat)) := buildBucketsBT h3W h3Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G 4 xs.toFinset) h3Bucket4 := buildBucketsBT_sound (by decide) h3Pairs h3WOk h3PoolsOk h3AutosOk h3Bucket3Ok h3Check4
def h3Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
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
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 6 := lower_of_forestBT (essPairs := [(VAR 1,20,22),(VAR 2,18,22),(VAR 4,6,22),(VAR 5,2,34)]) (by decide +kernel) h3Bucket5Ok (by decide +kernel)
def h2R : List Nat := varsOf 55
def h2G : Nat := 0xeaeaa8a8c0c00000eaeaa8a8c0c00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 7 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,34,35)]) (by decide +kernel) h3Bound
def h5R : List Nat := varsOf 56
def h5G : Nat := 0xffffff00ff000000ffffff00ff000000
def h5Pos : List Nat := [40,48,24,24,48,40]
def h5Neg : List Nat := [32,32,8,16,16,8]
def h5Mask : Nat := fullMask 6
def h5Base : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,45,36),(0xffff0000ffff0000ffff0000ffff0000,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
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
lemma h5Bound : Lower h5R h5G 4 := lower_of_forestBT (essPairs := [(VAR 3,16,24),(VAR 4,8,24),(VAR 5,8,40)]) (by decide +kernel) h5Bucket3Ok (by decide +kernel)
def h6R : List Nat := varsOf 57
def h6G : Nat := 0xaaaaaa00aa000000aaaaaa00aa000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,24,25)]) (by decide +kernel) h5Bound
def h7R : List Nat := varsOf 27
def h7G : Nat := 0xeeaaaa88eeaaaa88eeaaaa88eeaaaa88
def h7Pos : List Nat := [9,26,9,17,3,9,26,17,26,3,3,3,9,3,17,11,11,19,19,25,25]
def h7Neg : List Nat := [8,24,10,16,2,1,18,1,10,1,0,10,0,18,0,10,1,18,1,24,1]
def h7Mask : Nat := fullMask 21
def h7Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xcccccccccccccccccccccccccccccccc,0x7af52,0x2a954),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x199167,0x88907),(0xffff0000ffff0000ffff0000ffff0000,0x1e41ca,0xa204a)]
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
lemma h7Bound : Lower h7R h7G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h7Bucket5Ok (by decide +kernel)
def h8R : List Nat := varsOf 41
def h8G : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
def h8Pos : List Nat := [33,40,9,9,40,33]
def h8Neg : List Nat := [32,32,1,8,8,1]
def h8Mask : Nat := fullMask 6
def h8Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h8Steps : List (Nat × Nat × Nat) := []
def h8W : BT Decor := buildWiresBT 2 h8Base h8Steps
def h8AutoList : List (List (Nat × Nat)) := [[]]
def h8Autos : BT (List (Nat × Nat)) := btOfList 1 h8AutoList
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
def h8Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
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
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 4 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 3,1,9),(VAR 5,1,33)]) (by decide +kernel) h8Bucket3Ok (by decide +kernel)
def h9R : List Nat := varsOf 43
def h9G : Nat := 0xeeaaeeaaaa00aa00eeaaeeaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,40,42)]) (by decide +kernel) h8Bound
def h10R : List Nat := varsOf 49
def h10G : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000
def h10Pos : List Nat := [33,48,17,17,48,33]
def h10Neg : List Nat := [32,32,1,16,16,1]
def h10Mask : Nat := fullMask 6
def h10Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xffff0000ffff0000ffff0000ffff0000,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
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
lemma h10Bound : Lower h10R h10G 4 := lower_of_forestBT (essPairs := [(VAR 0,16,17),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h10Bucket3Ok (by decide +kernel)
def h11R : List Nat := varsOf 51
def h11G : Nat := 0xeeeeaaaaaaaa0000eeeeaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,48,50)]) (by decide +kernel) h10Bound
def h12R : List Nat := varsOf 57
def h12G : Nat := 0xffaaaaaaaa000000ffaaaaaaaa000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,17,25)]) (by decide +kernel) h10Bound
def h13R : List Nat := varsOf 58
def h13G : Nat := 0xffffffccff000000ffffffccff000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,32,34)]) (by decide +kernel) h5Bound
def h4R : List Nat := varsOf 59
def h4G : Nat := 0xeeaaaa88aa000000eeaaaa88aa000000
def h4Pos : List Nat := [25,58,27,35,35,58,49,35,58,25,58,35,41,49,49,41,25,41,49,43,35,41,51,57]
def h4Neg : List Nat := [24,56,26,33,34,50,48,42,42,9,26,3,9,33,56,33,17,40,17,11,50,56,19,56]
def h4Mask : Nat := fullMask 24
def h4Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffadd,0x4dba08),(0xcccccccccccccccccccccccccccccccc,0x580dbe,0x580db4),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xab9727,0xaa5787),(0xffff0000ffff0000ffff0000ffff0000,0xc56767,0xf54467),(0xffffffff00000000ffffffff00000000,0xfefdfa,0xb2e1fa)]
def h4Steps : List (Nat × Nat × Nat) := [(0,0,2),(0,0,3),(0,2,3),(0,0,7),(2,0,7),(2,3,5),(0,4,5),(2,4,5),(0,4,7),(2,4,7),(2,2,8),(2,4,8),(2,3,11),(0,4,6),(2,4,6),(2,2,18)]
def h4W : BT Decor := buildWiresBT 5 h4Base h4Steps
def h4AutoList : List (List (Nat × Nat)) := [[]]
def h4Autos : BT (List (Nat × Nat)) := btOfList 1 h4AutoList
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
def h4SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 8,5),some (subcubeFast 0 10,4),some (subcubeFast 0 16,5),some (subcubeFast 0 18,4),some (subcubeFast 0 32,6),some (subcubeFast 2 0,5),some (subcubeFast 2 1,4)]
def h4Slices : BT (Option (Nat × Nat)) := btOfList 4 h4SliceList
def h4Specs : List PoolSpec := [(7,[]),(0,[]),(1,[]),(2,[]),(6,[(0,0,2)]),(7,[(0,0,2)]),(3,[]),(8,[]),(1,[(0,2,3)]),(4,[]),(6,[]),(6,[(0,0,3)]),(7,[(0,0,3)]),(5,[]),(6,[(0,2,3)])]
def h4Pools : BT (Option BoundPool) := buildPoolsBT 4 h4W h4R h4Slices h4Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice8 : Slice h4R h4G (subcubeFast 2 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice7 : Slice h4R h4G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice6 : Slice h4R h4G (subcubeFast 0 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice5 : Slice h4R h4G (subcubeFast 0 18) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice4 : Slice h4R h4G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice3 : Slice h4R h4G (subcubeFast 0 10) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice2 : Slice h4R h4G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice1 : Slice h4R h4G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Slice0 : Slice h4R h4G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h4R h4G p.1 p.2) h4Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h4R h4G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h4Slice0) (forall_cons (fun _ h => by cases h; exact h4Slice1) (forall_cons (fun _ h => by cases h; exact h4Slice2) (forall_cons (fun _ h => by cases h; exact h4Slice3) (forall_cons (fun _ h => by cases h; exact h4Slice4) (forall_cons (fun _ h => by cases h; exact h4Slice5) (forall_cons (fun _ h => by cases h; exact h4Slice6) (forall_cons (fun _ h => by cases h; exact h4Slice7) (forall_cons (fun _ h => by cases h; exact h4Slice8) (fun _ h => (List.not_mem_nil h).elim))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h4R h4G c) h4Pools := buildPoolsBT_sound h4SlicesOk
def h4Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h4G (4 - 1) xs.toFinset) h4Empty := trivial
def h4Block4_0 : List NodeSpec := [([0,1,2,3,16],[],[0]),([0,1,2,4,17],[],[0]),([0,1,3,4,20],[],[0])]
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
def h4Block5_0 : List NodeSpec := [([0,1,3,4,5,7],[1,8,9],[0]),([0,1,2,3,4,8],[0,2,10],[0]),([0,1,2,3,4,10],[],[0]),([0,1,2,3,4,11],[0,2,9],[0]),([0,1,2,3,4,12],[0,2],[0]),([0,1,2,4,6,7],[1,3,8],[0]),([0,1,2,3,4,15],[],[0]),([0,1,2,3,4,18],[0,2,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Test5_0 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Bucket4 5 h4Block5_0 = true := by decide +kernel
def h4Block5_1 : List NodeSpec := [([0,1,2,3,4,19],[0,2],[0]),([0,1,2,3,4,9],[],[0]),([0,1,2,3,4,13],[],[0]),([0,1,2,3,4,14],[14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Test5_1 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Bucket4 5 h4Block5_1 = true := by decide +kernel
def h4Nodes5 : List NodeSpec := h4Block5_0 ++ h4Block5_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Check5 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Bucket4 5 h4Nodes5 = true := by
  unfold h4Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h4Test5_0,h4Test5_1⟩
def h4Bucket5 : BT (List (List Nat)) := buildBucketsBT h4W h4Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h4G 5 xs.toFinset) h4Bucket5 := buildBucketsBT_sound (by decide) h4Pairs h4WOk h4PoolsOk h4AutosOk h4Bucket4Ok h4Check5
def h4Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,9,10],[0]),([0,1,2,3,4,6],[0,1,2,3,7,9,10,11,12,13],[0]),([0,1,2,3,4,7],[0,1,2,3,8,9,10,14],[0])]
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
def h4Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Test7_0 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Bucket6 7 h4Block7_0 = true := by decide +kernel
def h4Nodes7 : List NodeSpec := h4Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Check7 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Bucket6 7 h4Nodes7 = true := h4Test7_0
def h4Bucket7 : BT (List (List Nat)) := buildBucketsBT h4W h4Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h4G 7 xs.toFinset) h4Bucket7 := buildBucketsBT_sound (by decide) h4Pairs h4WOk h4PoolsOk h4AutosOk h4Bucket6Ok h4Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 8 := lower_of_forestBT (essPairs := [(VAR 0,24,25),(VAR 1,33,35),(VAR 3,17,25),(VAR 4,9,25),(VAR 5,3,35)]) (by decide +kernel) h4Bucket7Ok (by decide +kernel)
def h15R : List Nat := varsOf 29
def h15G : Nat := 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0
def h15Pos : List Nat := [9,28,9,17,5,9,28,17,28,5,5,5,9,5,17,13,13,21,21,25,25]
def h15Neg : List Nat := [8,24,12,16,4,1,20,1,12,1,0,12,0,20,0,12,1,20,1,24,1]
def h15Mask : Nat := fullMask 21
def h15Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7af52,0x2a954),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x199167,0x88907),(0xffff0000ffff0000ffff0000ffff0000,0x1e41ca,0xa204a)]
def h15Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(0,1,28),(2,2,4),(1,3,4),(0,1,31),(2,3,4),(0,2,5),(1,1,34),(3,2,5),(0,3,5),(1,1,37),(3,3,5),(2,1,8),(1,3,8),(0,2,41),(2,3,8),(3,1,9),(0,3,9),(1,2,45),(3,3,9),(2,1,12),(2,2,12),(3,1,13),(3,2,13),(1,3,18),(0,1,52),(2,3,18),(1,2,54),(1,3,19),(0,2,56),(2,3,19),(1,1,58),(1,2,22),(0,1,60),(2,2,23),(1,1,62)]
def h15W : BT Decor := buildWiresBT 6 h15Base h15Steps
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
def h15SliceList : List (Option (Nat × Nat)) := []
def h15Slices : BT (Option (Nat × Nat)) := btOfList 1 h15SliceList
def h15Specs : List PoolSpec := []
def h15Pools : BT (Option BoundPool) := buildPoolsBT 1 h15W h15R h15Slices h15Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h15R h15G p.1 p.2) h15Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h15R h15G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h15R h15G c) h15Pools := buildPoolsBT_sound h15SlicesOk
def h15Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G (3 - 1) xs.toFinset) h15Empty := trivial
def h15Block3_0 : List NodeSpec := [([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,2,31],[],[0]),([0,1,2,33],[],[0]),([0,1,3,34],[],[0]),([0,1,3,36],[],[0]),([0,1,2,37],[],[0]),([0,1,2,39],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test3_0 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Empty 3 h15Block3_0 = true := by decide +kernel
def h15Block3_1 : List NodeSpec := [([0,2,3,35],[],[0]),([0,2,3,40],[],[0]),([0,1,2,41],[],[0]),([0,1,2,43],[],[0]),([0,2,3,29],[],[0]),([0,2,3,44],[],[0]),([0,1,2,45],[],[0]),([0,1,2,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test3_1 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Empty 3 h15Block3_1 = true := by decide +kernel
def h15Block3_2 : List NodeSpec := [([0,2,3,38],[],[0]),([0,2,3,48],[],[0]),([0,1,3,46],[],[0]),([0,1,3,49],[],[0]),([0,2,3,32],[],[0]),([0,2,3,50],[],[0]),([0,1,3,42],[],[0]),([0,1,3,51],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test3_2 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Empty 3 h15Block3_2 = true := by decide +kernel
def h15Block3_3 : List NodeSpec := [([0,3,16,17],[],[0]),([0,1,2,52],[],[0]),([0,1,2,54],[],[0]),([0,1,2,56],[],[0]),([0,1,2,58],[],[0]),([0,2,20,21],[],[0]),([0,1,3,60],[],[0]),([0,1,3,57],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test3_3 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Empty 3 h15Block3_3 = true := by decide +kernel
def h15Block3_4 : List NodeSpec := [([0,1,3,55],[],[0]),([0,1,3,62],[],[0]),([0,1,24,25],[],[0]),([0,2,3,63],[],[0]),([0,2,3,53],[],[0]),([0,2,3,59],[],[0]),([0,2,3,61],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test3_4 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Empty 3 h15Block3_4 = true := by decide +kernel
def h15Nodes3 : List NodeSpec := h15Block3_0 ++ h15Block3_1 ++ h15Block3_2 ++ h15Block3_3 ++ h15Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Check3 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Empty 3 h15Nodes3 = true := by
  unfold h15Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h15Test3_0,h15Test3_1⟩,h15Test3_2⟩,h15Test3_3⟩,h15Test3_4⟩
def h15Bucket3 : BT (List (List Nat)) := buildBucketsBT h15W h15Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G 3 xs.toFinset) h15Bucket3 := buildBucketsBT_sound (by decide) h15Pairs h15WOk h15PoolsOk h15AutosOk h15EmptyOk h15Check3
def h15Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test4_0 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket3 4 h15Block4_0 = true := by decide +kernel
def h15Block4_1 : List NodeSpec := [([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0]),([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test4_1 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket3 4 h15Block4_1 = true := by decide +kernel
def h15Block4_2 : List NodeSpec := [([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0]),([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test4_2 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket3 4 h15Block4_2 = true := by decide +kernel
def h15Nodes4 : List NodeSpec := h15Block4_0 ++ h15Block4_1 ++ h15Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Check4 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket3 4 h15Nodes4 = true := by
  unfold h15Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h15Test4_0,h15Test4_1⟩,h15Test4_2⟩
def h15Bucket4 : BT (List (List Nat)) := buildBucketsBT h15W h15Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G 4 xs.toFinset) h15Bucket4 := buildBucketsBT_sound (by decide) h15Pairs h15WOk h15PoolsOk h15AutosOk h15Bucket3Ok h15Check4
def h15Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test5_0 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket4 5 h15Block5_0 = true := by decide +kernel
def h15Nodes5 : List NodeSpec := h15Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Check5 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket4 5 h15Nodes5 = true := h15Test5_0
def h15Bucket5 : BT (List (List Nat)) := buildBucketsBT h15W h15Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G 5 xs.toFinset) h15Bucket5 := buildBucketsBT_sound (by decide) h15Pairs h15WOk h15PoolsOk h15AutosOk h15Bucket4Ok h15Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 6 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h15Bucket5Ok (by decide +kernel)
def h16R : List Nat := varsOf 45
def h16G : Nat := 0xfaaafaaaaa00aa00faaafaaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,40,44)]) (by decide +kernel) h8Bound
def h17R : List Nat := varsOf 53
def h17G : Nat := 0xfafaaaaaaaaa0000fafaaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,48,52)]) (by decide +kernel) h10Bound
def h18R : List Nat := varsOf 60
def h18G : Nat := 0xfffffff0ff000000fffffff0ff000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,32,36)]) (by decide +kernel) h5Bound
def h14R : List Nat := varsOf 61
def h14G : Nat := 0xfaaaaaa0aa000000faaaaaa0aa000000
def h14Pos : List Nat := [25,60,29,37,37,60,49,37,60,25,60,37,41,49,49,41,25,41,49,45,37,41,53,57]
def h14Neg : List Nat := [24,56,28,33,36,52,48,44,44,9,28,5,9,33,56,33,17,40,17,13,52,56,21,56]
def h14Mask : Nat := fullMask 24
def h14Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffadd,0x4dba08),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x580dbe,0x580db4),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xab9727,0xaa5787),(0xffff0000ffff0000ffff0000ffff0000,0xc56767,0xf54467),(0xffffffff00000000ffffffff00000000,0xfefdfa,0xb2e1fa)]
def h14Steps : List (Nat × Nat × Nat) := [(0,0,2),(0,0,3),(0,2,3),(0,0,7),(2,0,7),(2,3,5),(0,4,5),(2,4,5),(0,4,7),(2,4,7),(2,2,8),(2,4,8),(2,3,11),(0,4,6),(2,4,6),(2,2,18)]
def h14W : BT Decor := buildWiresBT 5 h14Base h14Steps
def h14AutoList : List (List (Nat × Nat)) := [[]]
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
def h14SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 0 12,4),some (subcubeFast 0 16,5),some (subcubeFast 0 20,4),some (subcubeFast 0 32,6),some (subcubeFast 4 0,5),some (subcubeFast 4 1,4)]
def h14Slices : BT (Option (Nat × Nat)) := btOfList 4 h14SliceList
def h14Specs : List PoolSpec := [(7,[]),(0,[]),(1,[]),(2,[]),(6,[(0,0,2)]),(7,[(0,0,2)]),(3,[]),(8,[]),(1,[(0,2,3)]),(4,[]),(6,[]),(6,[(0,0,3)]),(7,[(0,0,3)]),(5,[]),(6,[(0,2,3)])]
def h14Pools : BT (Option BoundPool) := buildPoolsBT 4 h14W h14R h14Slices h14Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice8 : Slice h14R h14G (subcubeFast 4 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice7 : Slice h14R h14G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice6 : Slice h14R h14G (subcubeFast 0 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice5 : Slice h14R h14G (subcubeFast 0 20) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice4 : Slice h14R h14G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice3 : Slice h14R h14G (subcubeFast 0 12) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice2 : Slice h14R h14G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice1 : Slice h14R h14G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Slice0 : Slice h14R h14G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h14R h14G p.1 p.2) h14Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h14R h14G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h14Slice0) (forall_cons (fun _ h => by cases h; exact h14Slice1) (forall_cons (fun _ h => by cases h; exact h14Slice2) (forall_cons (fun _ h => by cases h; exact h14Slice3) (forall_cons (fun _ h => by cases h; exact h14Slice4) (forall_cons (fun _ h => by cases h; exact h14Slice5) (forall_cons (fun _ h => by cases h; exact h14Slice6) (forall_cons (fun _ h => by cases h; exact h14Slice7) (forall_cons (fun _ h => by cases h; exact h14Slice8) (fun _ h => (List.not_mem_nil h).elim))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h14R h14G c) h14Pools := buildPoolsBT_sound h14SlicesOk
def h14Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h14G (4 - 1) xs.toFinset) h14Empty := trivial
def h14Block4_0 : List NodeSpec := [([0,1,2,3,16],[],[0]),([0,1,2,4,17],[],[0]),([0,1,3,4,20],[],[0])]
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
def h14Block5_0 : List NodeSpec := [([0,1,3,4,5,7],[1,8,9],[0]),([0,1,2,3,4,8],[0,2,10],[0]),([0,1,2,3,4,10],[],[0]),([0,1,2,3,4,11],[0,2,9],[0]),([0,1,2,3,4,12],[0,2],[0]),([0,1,2,4,6,7],[1,3,8],[0]),([0,1,2,3,4,15],[],[0]),([0,1,2,3,4,18],[0,2,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Test5_0 : checkNodesBT h14W h14G h14Mask h14Pools h14Autos h14Bucket4 5 h14Block5_0 = true := by decide +kernel
def h14Block5_1 : List NodeSpec := [([0,1,2,3,4,19],[0,2],[0]),([0,1,2,3,4,9],[],[0]),([0,1,2,3,4,13],[],[0]),([0,1,2,3,4,14],[14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Test5_1 : checkNodesBT h14W h14G h14Mask h14Pools h14Autos h14Bucket4 5 h14Block5_1 = true := by decide +kernel
def h14Nodes5 : List NodeSpec := h14Block5_0 ++ h14Block5_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Check5 : checkNodesBT h14W h14G h14Mask h14Pools h14Autos h14Bucket4 5 h14Nodes5 = true := by
  unfold h14Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h14Test5_0,h14Test5_1⟩
def h14Bucket5 : BT (List (List Nat)) := buildBucketsBT h14W h14Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h14G 5 xs.toFinset) h14Bucket5 := buildBucketsBT_sound (by decide) h14Pairs h14WOk h14PoolsOk h14AutosOk h14Bucket4Ok h14Check5
def h14Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,9,10],[0]),([0,1,2,3,4,6],[0,1,2,3,7,9,10,11,12,13],[0]),([0,1,2,3,4,7],[0,1,2,3,8,9,10,14],[0])]
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
def h14Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Test7_0 : checkNodesBT h14W h14G h14Mask h14Pools h14Autos h14Bucket6 7 h14Block7_0 = true := by decide +kernel
def h14Nodes7 : List NodeSpec := h14Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Check7 : checkNodesBT h14W h14G h14Mask h14Pools h14Autos h14Bucket6 7 h14Nodes7 = true := h14Test7_0
def h14Bucket7 : BT (List (List Nat)) := buildBucketsBT h14W h14Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h14G 7 xs.toFinset) h14Bucket7 := buildBucketsBT_sound (by decide) h14Pairs h14WOk h14PoolsOk h14AutosOk h14Bucket6Ok h14Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 8 := lower_of_forestBT (essPairs := [(VAR 0,24,25),(VAR 2,33,37),(VAR 3,17,25),(VAR 4,9,25),(VAR 5,5,37)]) (by decide +kernel) h14Bucket7Ok (by decide +kernel)
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
def h20R : List Nat := varsOf 30
def h20G : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 7 := carry_of (swaps := [(3,4),(4,5)]) (roots2 := Cofactor12058.R_10) (T2 := Cofactor12058.G_10) (by decide +kernel) Cofactor12058.low_10
def h19R : List Nat := varsOf 62
def h19G : Nat := 0xfcc0c000c0c0c000fcc0c000c0c0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 8 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,26,58)]) (by decide +kernel) h20Bound
def h22R : List Nat := varsOf 15
def h22G : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def h22Pos : List Nat := [5,14,5,9,3,5,14,9,14,3,3,3,5,3,9,7,7,11,11,13,13]
def h22Neg : List Nat := [4,12,6,8,2,1,10,1,6,1,0,6,0,10,0,6,1,10,1,12,1]
def h22Mask : Nat := fullMask 21
def h22Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xcccccccccccccccccccccccccccccccc,0x7af52,0x2a954),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x199167,0x88907),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1e41ca,0xa204a)]
def h22Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(0,1,28),(2,2,4),(1,3,4),(0,1,31),(2,3,4),(0,2,5),(1,1,34),(3,2,5),(0,3,5),(1,1,37),(3,3,5),(2,1,8),(1,3,8),(0,2,41),(2,3,8),(3,1,9),(0,3,9),(1,2,45),(3,3,9),(2,1,12),(2,2,12),(3,1,13),(3,2,13),(1,3,18),(0,1,52),(2,3,18),(1,2,54),(1,3,19),(0,2,56),(2,3,19),(1,1,58),(1,2,22),(0,1,60),(2,2,23),(1,1,62)]
def h22W : BT Decor := buildWiresBT 6 h22Base h22Steps
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
def h22Block3_0 : List NodeSpec := [([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,2,31],[],[0]),([0,1,2,33],[],[0]),([0,1,3,34],[],[0]),([0,1,3,36],[],[0]),([0,1,2,37],[],[0]),([0,1,2,39],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test3_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Empty 3 h22Block3_0 = true := by decide +kernel
def h22Block3_1 : List NodeSpec := [([0,2,3,35],[],[0]),([0,2,3,40],[],[0]),([0,1,2,41],[],[0]),([0,1,2,43],[],[0]),([0,2,3,29],[],[0]),([0,2,3,44],[],[0]),([0,1,2,45],[],[0]),([0,1,2,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test3_1 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Empty 3 h22Block3_1 = true := by decide +kernel
def h22Block3_2 : List NodeSpec := [([0,2,3,38],[],[0]),([0,2,3,48],[],[0]),([0,1,3,46],[],[0]),([0,1,3,49],[],[0]),([0,2,3,32],[],[0]),([0,2,3,50],[],[0]),([0,1,3,42],[],[0]),([0,1,3,51],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test3_2 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Empty 3 h22Block3_2 = true := by decide +kernel
def h22Block3_3 : List NodeSpec := [([0,3,16,17],[],[0]),([0,1,2,52],[],[0]),([0,1,2,54],[],[0]),([0,1,2,56],[],[0]),([0,1,2,58],[],[0]),([0,2,20,21],[],[0]),([0,1,3,60],[],[0]),([0,1,3,57],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test3_3 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Empty 3 h22Block3_3 = true := by decide +kernel
def h22Block3_4 : List NodeSpec := [([0,1,3,55],[],[0]),([0,1,3,62],[],[0]),([0,1,24,25],[],[0]),([0,2,3,63],[],[0]),([0,2,3,53],[],[0]),([0,2,3,59],[],[0]),([0,2,3,61],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test3_4 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Empty 3 h22Block3_4 = true := by decide +kernel
def h22Nodes3 : List NodeSpec := h22Block3_0 ++ h22Block3_1 ++ h22Block3_2 ++ h22Block3_3 ++ h22Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check3 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Empty 3 h22Nodes3 = true := by
  unfold h22Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h22Test3_0,h22Test3_1⟩,h22Test3_2⟩,h22Test3_3⟩,h22Test3_4⟩
def h22Bucket3 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 3 xs.toFinset) h22Bucket3 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22EmptyOk h22Check3
def h22Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Block4_0 = true := by decide +kernel
def h22Block4_1 : List NodeSpec := [([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0]),([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_1 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Block4_1 = true := by decide +kernel
def h22Block4_2 : List NodeSpec := [([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0]),([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_2 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Block4_2 = true := by decide +kernel
def h22Nodes4 : List NodeSpec := h22Block4_0 ++ h22Block4_1 ++ h22Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check4 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket3 4 h22Nodes4 = true := by
  unfold h22Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h22Test4_0,h22Test4_1⟩,h22Test4_2⟩
def h22Bucket4 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 4 xs.toFinset) h22Bucket4 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket3Ok h22Check4
def h22Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_0 = true := by decide +kernel
def h22Nodes5 : List NodeSpec := h22Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check5 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Nodes5 = true := h22Test5_0
def h22Bucket5 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 5 xs.toFinset) h22Bucket5 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket4Ok h22Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) h22Bucket5Ok (by decide +kernel)
def h23R : List Nat := varsOf 22
def h23G : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def h23Pos : List Nat := [18,20,6,6,20,18]
def h23Neg : List Nat := [16,16,2,4,4,2]
def h23Mask : Nat := fullMask 6
def h23Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h23Steps : List (Nat × Nat × Nat) := []
def h23W : BT Decor := buildWiresBT 2 h23Base h23Steps
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
def h23Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Test3_0 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Empty 3 h23Block3_0 = true := by decide +kernel
def h23Nodes3 : List NodeSpec := h23Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Check3 : checkNodesBT h23W h23G h23Mask h23Pools h23Autos h23Empty 3 h23Nodes3 = true := h23Test3_0
def h23Bucket3 : BT (List (List Nat)) := buildBucketsBT h23W h23Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h23G 3 xs.toFinset) h23Bucket3 := buildBucketsBT_sound (by decide) h23Pairs h23WOk h23PoolsOk h23AutosOk h23EmptyOk h23Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 4,2,18)]) (by decide +kernel) h23Bucket3Ok (by decide +kernel)
def h24R : List Nat := varsOf 26
def h24G : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
def h24Pos : List Nat := [18,24,10,10,24,18]
def h24Neg : List Nat := [16,16,2,8,8,2]
def h24Mask : Nat := fullMask 6
def h24Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
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
def h24Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
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
lemma h24Bound : Lower h24R h24G 4 := lower_of_forestBT (essPairs := [(VAR 1,8,10),(VAR 3,2,10),(VAR 4,2,18)]) (by decide +kernel) h24Bucket3Ok (by decide +kernel)
def h25R : List Nat := varsOf 28
def h25G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def h25Pos : List Nat := [20,24,12,12,24,20]
def h25Neg : List Nat := [16,16,4,8,8,4]
def h25Mask : Nat := fullMask 6
def h25Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
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
def h25Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
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
lemma h25Bound : Lower h25R h25G 4 := lower_of_forestBT (essPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 4,4,20)]) (by decide +kernel) h25Bucket3Ok (by decide +kernel)
def h27R : List Nat := varsOf 14
def h27G : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def h27Pos : List Nat := [10,12,6,6,12,10]
def h27Neg : List Nat := [8,8,2,4,4,2]
def h27Mask : Nat := fullMask 6
def h27Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xff00ff00ff00ff00ff00ff00ff00ff00,51,3)]
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
lemma h27Bound : Lower h27R h27G 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 3,2,10)]) (by decide +kernel) h27Bucket3Ok (by decide +kernel)
def h26R : List Nat := varsOf 15
def h26G : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h27Bound
def h28R : List Nat := varsOf 23
def h28G : Nat := 0xfefeeaeafefeeaeafefeeaeafefeeaea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h23Bound
def h29R : List Nat := varsOf 27
def h29G : Nat := 0xffeeeeaaffeeeeaaffeeeeaaffeeeeaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h24Bound
def h30R : List Nat := varsOf 29
def h30G : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h25Bound
def h21R : List Nat := varsOf 31
def h21G : Nat := 0xfeeaeaa8feeaeaa8feeaeaa8feeaeaa8
def h21Pos : List Nat := [5,14,3,3,14,5,14,9,9,22,17,17,22,22,26,26,11,26,7,28,28,28]
def h21Neg : List Nat := [4,12,1,2,10,1,6,1,8,6,1,16,20,18,10,18,10,24,6,24,20,12]
def h21Mask : Nat := fullMask 22
def h21Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x50dad,1188),(0xcccccccccccccccccccccccccccccccc,0x7f25e,0x5e258),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3c3273,0x341243),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3bc1d2,0x2b4112),(0xffff0000ffff0000ffff0000ffff0000,0x3afe00,0x1ab800)]
def h21Steps : List (Nat × Nat × Nat) := [(1,1,2),(1,1,3),(1,1,4),(1,2,3),(1,2,4),(1,3,4),(0,5,10),(0,6,9),(0,7,8)]
def h21W : BT Decor := buildWiresBT 4 h21Base h21Steps
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
def h21SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 1 0,7),some (subcubeFast 1 2,4),some (subcubeFast 1 4,4),some (subcubeFast 1 8,4),some (subcubeFast 2 0,6),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 16 0,6)]
def h21Slices : BT (Option (Nat × Nat)) := btOfList 4 h21SliceList
def h21Specs : List PoolSpec := [(4,[]),(8,[]),(4,[(1,1,2)]),(0,[]),(5,[]),(9,[]),(10,[(1,1,2)]),(8,[(1,3,4)]),(1,[]),(10,[]),(2,[]),(11,[]),(3,[]),(11,[(1,1,2)]),(4,[(1,1,3)]),(9,[(1,1,3)]),(8,[(1,2,4)]),(11,[(1,1,3)]),(4,[(1,1,4)]),(9,[(1,1,4)]),(8,[(1,2,3)]),(10,[(1,1,4)]),(4,[(1,2,3)]),(6,[]),(11,[(1,2,3)]),(4,[(1,2,4)]),(10,[(1,2,4)]),(4,[(1,3,4)]),(7,[]),(9,[(1,3,4)])]
def h21Pools : BT (Option BoundPool) := buildPoolsBT 5 h21W h21R h21Slices h21Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice11 : Slice h21R h21G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice10 : Slice h21R h21G (subcubeFast 8 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice9 : Slice h21R h21G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice8 : Slice h21R h21G (subcubeFast 2 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice7 : Slice h21R h21G (subcubeFast 1 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice6 : Slice h21R h21G (subcubeFast 1 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice5 : Slice h21R h21G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice4 : Slice h21R h21G (subcubeFast 1 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice3 : Slice h21R h21G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice2 : Slice h21R h21G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice1 : Slice h21R h21G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Slice0 : Slice h21R h21G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h21R h21G p.1 p.2) h21Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h21R h21G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h21Slice0) (forall_cons (fun _ h => by cases h; exact h21Slice1) (forall_cons (fun _ h => by cases h; exact h21Slice2) (forall_cons (fun _ h => by cases h; exact h21Slice3) (forall_cons (fun _ h => by cases h; exact h21Slice4) (forall_cons (fun _ h => by cases h; exact h21Slice5) (forall_cons (fun _ h => by cases h; exact h21Slice6) (forall_cons (fun _ h => by cases h; exact h21Slice7) (forall_cons (fun _ h => by cases h; exact h21Slice8) (forall_cons (fun _ h => by cases h; exact h21Slice9) (forall_cons (fun _ h => by cases h; exact h21Slice10) (forall_cons (fun _ h => by cases h; exact h21Slice11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h21R h21G c) h21Pools := buildPoolsBT_sound h21SlicesOk
def h21Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h21G (5 - 1) xs.toFinset) h21Empty := trivial
def h21Block5_0 : List NodeSpec := [([0,1,2,3,4,11],[],[0]),([0,1,2,3,4,12],[],[0]),([0,1,2,3,4,13],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Test5_0 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Empty 5 h21Block5_0 = true := by decide +kernel
def h21Nodes5 : List NodeSpec := h21Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Check5 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Empty 5 h21Nodes5 = true := h21Test5_0
def h21Bucket5 : BT (List (List Nat)) := buildBucketsBT h21W h21Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h21G 5 xs.toFinset) h21Bucket5 := buildBucketsBT_sound (by decide) h21Pairs h21WOk h21PoolsOk h21AutosOk h21EmptyOk h21Check5
def h21Block6_0 : List NodeSpec := [([0,1,2,3,4,5,10],[1,3,5,6,7,8,9,10,11,12],[0]),([0,1,2,3,4,6,9],[1,3,5,8,9,10,11,12,15,16],[0]),([0,1,2,3,4,7,8],[1,3,5,8,9,10,11,12,19,20],[0])]
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
def h21Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,9,10,11,12,13],[0]),([0,1,2,3,4,6],[0,1,3,4,5,8,9,11,12,14,15,17],[0]),([0,1,2,3,4,7],[0,1,3,4,5,8,9,10,11,18,19,21],[0]),([0,1,2,3,4,8],[0,1,3,5,8,9,11,12,20,22,23,24],[0]),([0,1,2,3,4,9],[0,1,3,5,8,9,10,11,16,23,25,26],[0]),([0,1,2,3,4,10],[0,1,3,5,7,8,9,10,11,27,28,29],[0])]
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
def h21Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,1,5,9,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Test8_0 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Bucket7 8 h21Block8_0 = true := by decide +kernel
def h21Nodes8 : List NodeSpec := h21Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Check8 : checkNodesBT h21W h21G h21Mask h21Pools h21Autos h21Bucket7 8 h21Nodes8 = true := h21Test8_0
def h21Bucket8 : BT (List (List Nat)) := buildBucketsBT h21W h21Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h21G 8 xs.toFinset) h21Bucket8 := buildBucketsBT_sound (by decide) h21Pairs h21WOk h21PoolsOk h21AutosOk h21Bucket7Ok h21Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h21Bucket8Ok (by decide +kernel)
def h32R : List Nat := varsOf 38
def h32G : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def h32Pos : List Nat := [34,36,6,6,36,34]
def h32Neg : List Nat := [32,32,2,4,4,2]
def h32Mask : Nat := fullMask 6
def h32Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
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
lemma h32Bound : Lower h32R h32G 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 5,2,34)]) (by decide +kernel) h32Bucket3Ok (by decide +kernel)
def h33R : List Nat := varsOf 46
def h33G : Nat := 0xfcc0fcc0c0c0c0c0fcc0fcc0c0c0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,34,42)]) (by decide +kernel) h32Bound
def h34R : List Nat := varsOf 39
def h34G : Nat := 0xfefefefeeaeaeaeafefefefeeaeaeaea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h32Bound
def h35R : List Nat := varsOf 43
def h35G : Nat := 0xffeeffeeeecceeccffeeffeeeecceecc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,0,2)]) (by decide +kernel) h8Bound
def h36R : List Nat := varsOf 45
def h36G : Nat := 0xfffafffafaf0faf0fffafffafaf0faf0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,0,4)]) (by decide +kernel) h8Bound
def h31R : List Nat := varsOf 47
def h31G : Nat := 0xfeeafeeaeac0eac0feeafeeaeac0eac0
def h31Pos : List Nat := [6,9,7,11,6,7,13,33,42,9,42,33,42,44,13,37,41,11,35]
def h31Neg : List Nat := [4,8,5,10,2,3,12,32,34,1,10,1,40,40,5,5,40,3,3]
def h31Mask : Nat := fullMask 19
def h31Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7caee,0x6ca24),(0xcccccccccccccccccccccccccccccccc,0x6153d,0x60538),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe075,0xc045),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3774a,0x1344a),(0xffffffff00000000ffffffff00000000,0x5bd80,0x13180)]
def h31Steps : List (Nat × Nat × Nat) := [(0,3,4)]
def h31W : BT Decor := buildWiresBT 3 h31Base h31Steps
def h31AutoList : List (List (Nat × Nat)) := [[]]
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
def h31SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 8,4),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5)]
def h31Slices : BT (Option (Nat × Nat)) := btOfList 4 h31SliceList
def h31Specs : List PoolSpec := [(4,[]),(0,[]),(7,[]),(1,[]),(8,[]),(2,[]),(5,[]),(3,[]),(6,[]),(4,[(0,3,4)])]
def h31Pools : BT (Option BoundPool) := buildPoolsBT 4 h31W h31R h31Slices h31Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice8 : Slice h31R h31G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice7 : Slice h31R h31G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice6 : Slice h31R h31G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice5 : Slice h31R h31G (subcubeFast 1 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice4 : Slice h31R h31G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice3 : Slice h31R h31G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice2 : Slice h31R h31G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice1 : Slice h31R h31G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice0 : Slice h31R h31G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h31R h31G p.1 p.2) h31Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h31R h31G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h31Slice0) (forall_cons (fun _ h => by cases h; exact h31Slice1) (forall_cons (fun _ h => by cases h; exact h31Slice2) (forall_cons (fun _ h => by cases h; exact h31Slice3) (forall_cons (fun _ h => by cases h; exact h31Slice4) (forall_cons (fun _ h => by cases h; exact h31Slice5) (forall_cons (fun _ h => by cases h; exact h31Slice6) (forall_cons (fun _ h => by cases h; exact h31Slice7) (forall_cons (fun _ h => by cases h; exact h31Slice8) (fun _ h => (List.not_mem_nil h).elim))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h31R h31G c) h31Pools := buildPoolsBT_sound h31SlicesOk
def h31Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h31G (6 - 1) xs.toFinset) h31Empty := trivial
def h31Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Test6_0 : checkNodesBT h31W h31G h31Mask h31Pools h31Autos h31Empty 6 h31Block6_0 = true := by decide +kernel
def h31Nodes6 : List NodeSpec := h31Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Check6 : checkNodesBT h31W h31G h31Mask h31Pools h31Autos h31Empty 6 h31Nodes6 = true := h31Test6_0
def h31Bucket6 : BT (List (List Nat)) := buildBucketsBT h31W h31Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h31G 6 xs.toFinset) h31Bucket6 := buildBucketsBT_sound (by decide) h31Pairs h31WOk h31PoolsOk h31AutosOk h31EmptyOk h31Check6
def h31Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5,6,7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Test7_0 : checkNodesBT h31W h31G h31Mask h31Pools h31Autos h31Bucket6 7 h31Block7_0 = true := by decide +kernel
def h31Nodes7 : List NodeSpec := h31Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Check7 : checkNodesBT h31W h31G h31Mask h31Pools h31Autos h31Bucket6 7 h31Nodes7 = true := h31Test7_0
def h31Bucket7 : BT (List (List Nat)) := buildBucketsBT h31W h31Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h31G 7 xs.toFinset) h31Bucket7 := buildBucketsBT_sound (by decide) h31Pairs h31WOk h31PoolsOk h31AutosOk h31Bucket6Ok h31Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 8 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9),(VAR 5,1,33)]) (by decide +kernel) h31Bucket7Ok (by decide +kernel)
def h38R : List Nat := varsOf 54
def h38G : Nat := 0xfcfcc0c0c0c0c0c0fcfcc0c0c0c0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,34,50)]) (by decide +kernel) h32Bound
def h39R : List Nat := varsOf 51
def h39G : Nat := 0xffffeeeeeeeeccccffffeeeeeeeecccc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,0,2)]) (by decide +kernel) h10Bound
def h40R : List Nat := varsOf 53
def h40G : Nat := 0xfffffafafafaf0f0fffffafafafaf0f0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,0,4)]) (by decide +kernel) h10Bound
def h37R : List Nat := varsOf 55
def h37G : Nat := 0xfefeeaeaeaeac0c0fefeeaeaeaeac0c0
def h37Pos : List Nat := [6,17,7,19,6,7,21,33,50,17,50,33,50,52,21,37,49,19,35]
def h37Neg : List Nat := [4,16,5,18,2,3,20,32,34,1,18,1,48,48,5,5,48,3,3]
def h37Mask : Nat := fullMask 19
def h37Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7caee,0x6ca24),(0xcccccccccccccccccccccccccccccccc,0x6153d,0x60538),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe075,0xc045),(0xffff0000ffff0000ffff0000ffff0000,0x3774a,0x1344a),(0xffffffff00000000ffffffff00000000,0x5bd80,0x13180)]
def h37Steps : List (Nat × Nat × Nat) := [(0,3,4)]
def h37W : BT Decor := buildWiresBT 3 h37Base h37Steps
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
def h37SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 16,4),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5)]
def h37Slices : BT (Option (Nat × Nat)) := btOfList 4 h37SliceList
def h37Specs : List PoolSpec := [(4,[]),(0,[]),(7,[]),(1,[]),(8,[]),(2,[]),(5,[]),(3,[]),(6,[]),(4,[(0,3,4)])]
def h37Pools : BT (Option BoundPool) := buildPoolsBT 4 h37W h37R h37Slices h37Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice8 : Slice h37R h37G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice7 : Slice h37R h37G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice6 : Slice h37R h37G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice5 : Slice h37R h37G (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice4 : Slice h37R h37G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice3 : Slice h37R h37G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice2 : Slice h37R h37G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice1 : Slice h37R h37G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice0 : Slice h37R h37G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h37R h37G p.1 p.2) h37Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h37R h37G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h37Slice0) (forall_cons (fun _ h => by cases h; exact h37Slice1) (forall_cons (fun _ h => by cases h; exact h37Slice2) (forall_cons (fun _ h => by cases h; exact h37Slice3) (forall_cons (fun _ h => by cases h; exact h37Slice4) (forall_cons (fun _ h => by cases h; exact h37Slice5) (forall_cons (fun _ h => by cases h; exact h37Slice6) (forall_cons (fun _ h => by cases h; exact h37Slice7) (forall_cons (fun _ h => by cases h; exact h37Slice8) (fun _ h => (List.not_mem_nil h).elim))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h37R h37G c) h37Pools := buildPoolsBT_sound h37SlicesOk
def h37Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G (6 - 1) xs.toFinset) h37Empty := trivial
def h37Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Empty 6 h37Block6_0 = true := by decide +kernel
def h37Nodes6 : List NodeSpec := h37Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check6 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Empty 6 h37Nodes6 = true := h37Test6_0
def h37Bucket6 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 6 xs.toFinset) h37Bucket6 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37EmptyOk h37Check6
def h37Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5,6,7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test7_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket6 7 h37Block7_0 = true := by decide +kernel
def h37Nodes7 : List NodeSpec := h37Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check7 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket6 7 h37Nodes7 = true := h37Test7_0
def h37Bucket7 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 7 xs.toFinset) h37Bucket7 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket6Ok h37Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 8 := lower_of_forestBT (essPairs := [(VAR 0,16,17),(VAR 1,4,6),(VAR 2,2,6),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h37Bucket7Ok (by decide +kernel)
def h42R : List Nat := varsOf 27
def h42G : Nat := 0xeecccc00eecccc00eecccc00eecccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bound : Lower h42R h42G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,24,25)]) (by decide +kernel) h24Bound
def h43R : List Nat := varsOf 58
def h43G : Nat := 0xffcccc00cccccc00ffcccc00cccccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bound : Lower h43R h43G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,24,56)]) (by decide +kernel) h24Bound
def h44R : List Nat := varsOf 58
def h44G : Nat := 0xffffffffffcccc00ffffffffffcccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bound : Lower h44R h44G 5 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,0,32)]) (by decide +kernel) h24Bound
def h41R : List Nat := varsOf 59
def h41G : Nat := 0xffeeeeaaeecccc00ffeeeeaaeecccc00
def h41Pos : List Nat := [10,25,11,35,10,11,18,19,56,33,18,25,25,35,42,26,42,50]
def h41Neg : List Nat := [8,24,9,34,2,3,2,3,24,1,16,17,9,3,40,24,34,34]
def h41Mask : Nat := fullMask 18
def h41Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3aae,0x3aa4),(0xcccccccccccccccccccccccccccccccc,0x3e4fd,0x320f8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1d937,0xd107),(0xffff0000ffff0000ffff0000ffff0000,0x29dc2,0x8d02),(0xffffffff00000000ffffffff00000000,0x36308,0x34008)]
def h41Steps : List (Nat × Nat × Nat) := [(0,2,3)]
def h41W : BT Decor := buildWiresBT 3 h41Base h41Steps
def h41AutoList : List (List (Nat × Nat)) := [[]]
def h41Autos : BT (List (Nat × Nat)) := btOfList 1 h41AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Pairs : goodPairs h41G h41Pos h41Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41BaseOk : ∀ x ∈ h41Base, faithful h41Pos h41Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41WOk : btAll (fun x => faithful h41Pos h41Neg x ∧ x.1 < 2^128) h41W := buildWiresBT_faithful h41BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h41G = h41G) h41Autos := btAll_ofList (autos_of (by decide +kernel))
def h41SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 2 8,4),some (subcubeFast 2 16,4),some (subcubeFast 32 0,5)]
def h41Slices : BT (Option (Nat × Nat)) := btOfList 4 h41SliceList
def h41Specs : List PoolSpec := [(4,[]),(0,[]),(5,[]),(1,[]),(6,[]),(2,[]),(7,[]),(3,[]),(8,[]),(5,[(0,2,3)])]
def h41Pools : BT (Option BoundPool) := buildPoolsBT 4 h41W h41R h41Slices h41Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Slice8 : Slice h41R h41G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Slice7 : Slice h41R h41G (subcubeFast 2 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Slice6 : Slice h41R h41G (subcubeFast 2 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Slice5 : Slice h41R h41G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Slice4 : Slice h41R h41G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Slice3 : Slice h41R h41G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Slice2 : Slice h41R h41G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Slice1 : Slice h41R h41G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Slice0 : Slice h41R h41G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h41R h41G p.1 p.2) h41Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h41R h41G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h41Slice0) (forall_cons (fun _ h => by cases h; exact h41Slice1) (forall_cons (fun _ h => by cases h; exact h41Slice2) (forall_cons (fun _ h => by cases h; exact h41Slice3) (forall_cons (fun _ h => by cases h; exact h41Slice4) (forall_cons (fun _ h => by cases h; exact h41Slice5) (forall_cons (fun _ h => by cases h; exact h41Slice6) (forall_cons (fun _ h => by cases h; exact h41Slice7) (forall_cons (fun _ h => by cases h; exact h41Slice8) (fun _ h => (List.not_mem_nil h).elim))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h41R h41G c) h41Pools := buildPoolsBT_sound h41SlicesOk
def h41Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h41G (6 - 1) xs.toFinset) h41Empty := trivial
def h41Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,7,8,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Test6_0 : checkNodesBT h41W h41G h41Mask h41Pools h41Autos h41Empty 6 h41Block6_0 = true := by decide +kernel
def h41Nodes6 : List NodeSpec := h41Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Check6 : checkNodesBT h41W h41G h41Mask h41Pools h41Autos h41Empty 6 h41Nodes6 = true := h41Test6_0
def h41Bucket6 : BT (List (List Nat)) := buildBucketsBT h41W h41Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h41G 6 xs.toFinset) h41Bucket6 := buildBucketsBT_sound (by decide) h41Pairs h41WOk h41PoolsOk h41AutosOk h41EmptyOk h41Check6
def h41Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5,6,7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Test7_0 : checkNodesBT h41W h41G h41Mask h41Pools h41Autos h41Bucket6 7 h41Block7_0 = true := by decide +kernel
def h41Nodes7 : List NodeSpec := h41Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Check7 : checkNodesBT h41W h41G h41Mask h41Pools h41Autos h41Bucket6 7 h41Nodes7 = true := h41Test7_0
def h41Bucket7 : BT (List (List Nat)) := buildBucketsBT h41W h41Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h41G 7 xs.toFinset) h41Bucket7 := buildBucketsBT_sound (by decide) h41Pairs h41WOk h41PoolsOk h41AutosOk h41Bucket6Ok h41Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 8 := lower_of_forestBT (essPairs := [(VAR 0,24,25),(VAR 1,8,10),(VAR 3,2,10),(VAR 4,2,18),(VAR 5,1,33)]) (by decide +kernel) h41Bucket7Ok (by decide +kernel)
def h46R : List Nat := varsOf 29
def h46G : Nat := 0xfaf0f000faf0f000faf0f000faf0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,24,25)]) (by decide +kernel) h25Bound
def h47R : List Nat := varsOf 60
def h47G : Nat := 0xfff0f000f0f0f000fff0f000f0f0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h47Bound : Lower h47R h47G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,24,56)]) (by decide +kernel) h25Bound
def h48R : List Nat := varsOf 60
def h48G : Nat := 0xfffffffffff0f000fffffffffff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bound : Lower h48R h48G 5 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,0,32)]) (by decide +kernel) h25Bound
def h45R : List Nat := varsOf 61
def h45G : Nat := 0xfffafaaafaf0f000fffafaaafaf0f000
def h45Pos : List Nat := [12,25,13,37,12,13,20,21,56,33,20,25,25,37,44,28,44,52]
def h45Neg : List Nat := [8,24,9,36,4,5,4,5,24,1,16,17,9,5,40,24,36,36]
def h45Mask : Nat := fullMask 18
def h45Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3aae,0x3aa4),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3e4fd,0x320f8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1d937,0xd107),(0xffff0000ffff0000ffff0000ffff0000,0x29dc2,0x8d02),(0xffffffff00000000ffffffff00000000,0x36308,0x34008)]
def h45Steps : List (Nat × Nat × Nat) := [(0,2,3)]
def h45W : BT Decor := buildWiresBT 3 h45Base h45Steps
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
def h45SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 4 0,5),some (subcubeFast 4 8,4),some (subcubeFast 4 16,4),some (subcubeFast 32 0,5)]
def h45Slices : BT (Option (Nat × Nat)) := btOfList 4 h45SliceList
def h45Specs : List PoolSpec := [(4,[]),(0,[]),(5,[]),(1,[]),(6,[]),(2,[]),(7,[]),(3,[]),(8,[]),(5,[(0,2,3)])]
def h45Pools : BT (Option BoundPool) := buildPoolsBT 4 h45W h45R h45Slices h45Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice8 : Slice h45R h45G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice7 : Slice h45R h45G (subcubeFast 4 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice6 : Slice h45R h45G (subcubeFast 4 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice5 : Slice h45R h45G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice4 : Slice h45R h45G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice3 : Slice h45R h45G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice2 : Slice h45R h45G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice1 : Slice h45R h45G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Slice0 : Slice h45R h45G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h45R h45G p.1 p.2) h45Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h45R h45G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h45Slice0) (forall_cons (fun _ h => by cases h; exact h45Slice1) (forall_cons (fun _ h => by cases h; exact h45Slice2) (forall_cons (fun _ h => by cases h; exact h45Slice3) (forall_cons (fun _ h => by cases h; exact h45Slice4) (forall_cons (fun _ h => by cases h; exact h45Slice5) (forall_cons (fun _ h => by cases h; exact h45Slice6) (forall_cons (fun _ h => by cases h; exact h45Slice7) (forall_cons (fun _ h => by cases h; exact h45Slice8) (fun _ h => (List.not_mem_nil h).elim))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h45R h45G c) h45Pools := buildPoolsBT_sound h45SlicesOk
def h45Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h45G (6 - 1) xs.toFinset) h45Empty := trivial
def h45Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,7,8,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Test6_0 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Empty 6 h45Block6_0 = true := by decide +kernel
def h45Nodes6 : List NodeSpec := h45Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Check6 : checkNodesBT h45W h45G h45Mask h45Pools h45Autos h45Empty 6 h45Nodes6 = true := h45Test6_0
def h45Bucket6 : BT (List (List Nat)) := buildBucketsBT h45W h45Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h45G 6 xs.toFinset) h45Bucket6 := buildBucketsBT_sound (by decide) h45Pairs h45WOk h45PoolsOk h45AutosOk h45EmptyOk h45Check6
def h45Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5,6,7,8],[0])]
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
lemma h45Bound : Lower h45R h45G 8 := lower_of_forestBT (essPairs := [(VAR 0,24,25),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,4,20),(VAR 5,1,33)]) (by decide +kernel) h45Bucket7Ok (by decide +kernel)
def h50R : List Nat := varsOf 30
def h50G : Nat := 0xffc0c000ffc0c000ffc0c000ffc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bound : Lower h50R h50G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,12,14)]) (by decide +kernel) h25Bound
def h51R : List Nat := varsOf 46
def h51G : Nat := 0xfffcfffcc000c000fffcfffcc000c000
def h51Pos : List Nat := [34,36,14,40,34,40,38,14,14,14,36,42,14,36,34,44,14,34,36,34,40]
def h51Neg : List Nat := [32,32,6,8,2,32,6,8,12,10,4,10,4,6,0,12,2,6,0,10,0]
def h51Mask : Nat := fullMask 21
def h51Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xb5bd5,0xb2a54),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x5b7c6,0x2b544),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x119bac,0x88b88),(0xffffffff00000000ffffffff00000000,0x1eec7b,35)]
def h51Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(1,2,10),(0,0,28),(2,2,10),(1,1,30),(1,2,11),(0,1,32),(2,2,11),(1,0,34),(1,1,14),(0,0,36),(2,1,15),(1,0,38),(1,1,16),(0,0,40),(2,1,16),(1,2,16),(0,0,43),(2,2,16),(0,1,17),(1,0,46),(3,1,17),(0,2,17),(1,0,49),(3,2,17),(2,0,24),(1,2,24),(0,1,53),(2,2,24),(3,0,25),(0,2,25),(1,1,57),(3,2,25),(2,0,6),(2,1,6),(3,0,7),(3,1,7)]
def h51W : BT Decor := buildWiresBT 6 h51Base h51Steps
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
def h51SliceList : List (Option (Nat × Nat)) := []
def h51Slices : BT (Option (Nat × Nat)) := btOfList 1 h51SliceList
def h51Specs : List PoolSpec := []
def h51Pools : BT (Option BoundPool) := buildPoolsBT 1 h51W h51R h51Slices h51Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h51R h51G p.1 p.2) h51Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h51R h51G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h51R h51G c) h51Pools := buildPoolsBT_sound h51SlicesOk
def h51Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G (3 - 1) xs.toFinset) h51Empty := trivial
def h51Block3_0 : List NodeSpec := [([2,3,4,5],[],[0]),([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,3,32],[],[0]),([0,1,3,34],[],[0]),([1,3,12,13],[],[0]),([0,2,3,36],[],[0]),([0,2,3,33],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test3_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 3 h51Block3_0 = true := by decide +kernel
def h51Block3_1 : List NodeSpec := [([0,2,3,31],[],[0]),([0,2,3,38],[],[0]),([0,2,3,40],[],[0]),([0,2,3,42],[],[0]),([0,1,3,43],[],[0]),([0,1,3,45],[],[0]),([0,2,3,46],[],[0]),([0,2,3,48],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test3_1 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 3 h51Block3_1 = true := by decide +kernel
def h51Block3_2 : List NodeSpec := [([0,1,3,49],[],[0]),([0,1,3,51],[],[0]),([0,3,20,21],[],[0]),([1,2,3,39],[],[0]),([1,2,3,29],[],[0]),([1,2,3,35],[],[0]),([1,2,3,37],[],[0]),([1,2,3,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test3_2 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 3 h51Block3_2 = true := by decide +kernel
def h51Block3_3 : List NodeSpec := [([1,2,3,52],[],[0]),([0,1,3,53],[],[0]),([0,1,3,55],[],[0]),([1,2,3,41],[],[0]),([1,2,3,56],[],[0]),([0,1,3,57],[],[0]),([0,1,3,59],[],[0]),([1,2,3,50],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test3_3 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 3 h51Block3_3 = true := by decide +kernel
def h51Block3_4 : List NodeSpec := [([1,2,3,60],[],[0]),([0,2,3,58],[],[0]),([0,2,3,61],[],[0]),([1,2,3,44],[],[0]),([1,2,3,62],[],[0]),([0,2,3,54],[],[0]),([0,2,3,63],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test3_4 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 3 h51Block3_4 = true := by decide +kernel
def h51Nodes3 : List NodeSpec := h51Block3_0 ++ h51Block3_1 ++ h51Block3_2 ++ h51Block3_3 ++ h51Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check3 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 3 h51Nodes3 = true := by
  unfold h51Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h51Test3_0,h51Test3_1⟩,h51Test3_2⟩,h51Test3_3⟩,h51Test3_4⟩
def h51Bucket3 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 3 xs.toFinset) h51Bucket3 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51EmptyOk h51Check3
def h51Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0]),([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test4_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket3 4 h51Block4_0 = true := by decide +kernel
def h51Block4_1 : List NodeSpec := [([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0]),([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test4_1 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket3 4 h51Block4_1 = true := by decide +kernel
def h51Block4_2 : List NodeSpec := [([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test4_2 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket3 4 h51Block4_2 = true := by decide +kernel
def h51Nodes4 : List NodeSpec := h51Block4_0 ++ h51Block4_1 ++ h51Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check4 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket3 4 h51Nodes4 = true := by
  unfold h51Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h51Test4_0,h51Test4_1⟩,h51Test4_2⟩
def h51Bucket4 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 4 xs.toFinset) h51Bucket4 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51Bucket3Ok h51Check4
def h51Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_0 = true := by decide +kernel
def h51Nodes5 : List NodeSpec := h51Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check5 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Nodes5 = true := h51Test5_0
def h51Bucket5 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 5 xs.toFinset) h51Bucket5 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51Bucket4Ok h51Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bound : Lower h51R h51G 6 := lower_of_forestBT (essPairs := [(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 5,2,34)]) (by decide +kernel) h51Bucket5Ok (by decide +kernel)
def h49R : List Nat := varsOf 62
def h49G : Nat := 0xfffffffcffc0c000fffffffcffc0c000
def h49Pos : List Nat := [34,36,14,22,24,24,40,34,14,22,26,48,26,38,14,40,48,24,22,14,28,28,42,44,34,36,34,50,52,34,24,24,44,50,14,26,26,36,48,24,24,42,52,36,40,36,34,28,36,24]
def h49Neg : List Nat := [32,32,6,6,8,16,8,2,10,18,18,16,10,6,8,32,32,0,20,12,20,12,10,12,10,6,6,18,20,18,18,12,32,32,4,16,2,20,0,10,20,32,32,12,0,4,0,4,0,32]
def h49Mask : Nat := fullMask 50
def h49Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x421e2d4c778d,0x906f40378c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1ac2512bc630e,0xa92496bc200c),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x2939dc0fad574,0x88081e85150),(0xffff0000ffff0000ffff0000ffff0000,0x285dad8371e38,0x12878140e20),(0xffffffff00000000ffffffff00000000,0x17e633fc1a8c3,0x2060300018003)]
def h49Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(2,2,4),(3,2,4),(1,2,5),(1,3,4),(2,3,4),(3,3,4),(1,3,5),(1,4,5),(0,4,8),(1,4,8),(2,4,8),(3,4,8),(1,5,8),(3,5,8),(2,0,1),(3,0,1),(1,0,2),(1,1,2),(2,1,2),(1,1,3),(3,2,28),(1,2,31),(3,2,31),(1,3,28),(3,3,28),(1,3,34),(3,3,34),(1,2,36),(3,2,36),(3,3,31),(0,28,31),(0,1,4),(1,1,4),(2,1,4),(3,1,4),(3,2,18),(1,4,18),(3,4,18),(1,0,3),(3,2,50),(3,3,29),(1,3,51),(1,2,52),(3,3,50),(0,29,50),(3,3,14),(1,4,14),(3,4,14),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,0,8),(3,0,8),(0,1,8),(3,1,8),(2,0,25),(2,1,25),(0,0,11),(2,0,11),(0,1,11),(2,1,11),(0,3,11),(3,3,11),(0,0,19),(0,1,19),(3,2,19),(3,3,19),(3,3,58),(3,5,11),(0,0,15),(2,0,15),(0,1,15),(2,1,15),(0,2,15),(3,2,15),(3,2,48),(3,5,15),(1,2,26),(1,3,26),(1,8,26),(0,0,92),(3,2,92),(3,3,92),(2,8,26),(1,1,96),(1,2,27),(1,3,27),(1,8,27),(0,1,100),(3,2,100),(3,3,100),(2,8,27),(1,0,104),(1,4,55),(1,4,32),(3,1,61),(3,2,61),(3,3,61),(1,4,53),(3,4,53),(1,2,110),(3,2,110),(1,3,87),(3,3,111),(2,15,32),(1,16,32),(1,4,39),(3,4,39),(1,3,109),(1,2,75),(3,2,119),(2,11,55),(1,12,55),(1,1,60),(2,1,60),(1,2,60),(1,3,128),(3,3,128),(1,3,60),(3,2,131),(0,0,129),(2,8,60),(1,0,77),(1,4,7),(1,7,77),(0,8,61),(1,0,138),(1,2,63),(1,3,140),(3,3,140),(1,3,63),(3,2,143),(3,0,141),(2,8,63),(1,4,41),(1,4,30),(3,0,44),(3,2,44),(3,3,44),(1,4,37),(3,4,37),(1,2,151),(3,2,151),(3,3,152),(2,15,30),(1,4,54),(3,4,54),(1,3,150),(3,2,158),(2,11,41),(1,12,41),(2,0,43),(1,2,43),(1,3,165),(3,3,165),(1,3,43),(3,2,168),(0,1,166),(2,8,43),(1,7,76),(0,8,44),(1,1,173),(1,2,46),(1,3,175),(3,3,175),(1,3,46),(3,2,178),(3,1,176),(2,8,46),(2,35,64),(1,1,40),(1,0,69),(1,7,69),(2,33,66),(1,7,68),(2,0,20),(2,1,20),(3,20,21),(2,11,17),(3,13,15)]
def h49W : BT Decor := buildWiresBT 8 h49Base h49Steps
def h49AutoList : List (List (Nat × Nat)) := [[]]
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
def h49SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 6 0,4),some (subcubeFast 8 0,6),some (subcubeFast 16 0,6),some (subcubeFast 32 0,5),some (subcubeFast 32 2,4),some (subcubeFast 32 4,4)]
def h49Slices : BT (Option (Nat × Nat)) := btOfList 4 h49SliceList
def h49Specs : List PoolSpec := [(5,[(0,0,1),(1,0,1)]),(2,[]),(4,[]),(0,[]),(6,[(0,0,1),(1,0,1)]),(8,[]),(7,[(0,0,1)]),(3,[]),(5,[(0,0,1)]),(3,[(1,0,2)]),(1,[]),(5,[]),(6,[(0,0,1)]),(3,[(1,0,3)]),(6,[]),(9,[]),(2,[(1,1,2)]),(2,[(1,1,3)]),(7,[]),(5,[(1,0,1)]),(6,[(1,0,1)]),(5,[(2,0,1)]),(6,[(2,0,1)]),(5,[(2,0,1),(1,8,26)]),(5,[(2,0,1),(2,8,26)]),(3,[(1,2,26)]),(6,[(2,0,1),(1,2,26)]),(3,[(1,3,26)]),(5,[(2,0,1),(1,3,26)]),(5,[(3,0,1)]),(6,[(3,0,1)]),(5,[(3,0,1),(1,8,27)]),(5,[(3,0,1),(2,8,27)]),(2,[(1,2,27)]),(6,[(3,0,1),(1,2,27)]),(2,[(1,3,27)]),(5,[(3,0,1),(1,3,27)]),(6,[(1,0,2)]),(5,[(3,3,28)]),(5,[(1,0,3)]),(1,[(1,0,4)]),(5,[(1,0,4)]),(6,[(3,2,50)]),(5,[(1,4,32)]),(6,[(1,0,4)]),(6,[(1,4,55)]),(5,[(0,0,4)]),(6,[(0,0,4)]),(5,[(0,0,4),(1,1,60)]),(6,[(0,0,4),(1,1,60)]),(0,[(1,1,60)]),(5,[(0,0,4),(2,1,60)]),(6,[(0,0,4),(2,1,60)]),(0,[(2,1,60)]),(0,[(1,2,60)]),(0,[(1,3,60)]),(5,[(0,0,4),(1,3,128)]),(5,[(0,0,4),(2,8,60)]),(6,[(0,0,4),(1,2,60)]),(5,[(0,0,4),(1,3,60)]),(2,[(0,1,19)]),(5,[(1,0,4),(3,1,61)]),(2,[(3,1,61)]),(6,[(1,0,4),(3,1,61)]),(7,[(3,1,61)]),(5,[(1,0,4),(0,8,61)]),(5,[(1,0,4),(3,3,61)]),(6,[(1,0,4),(3,2,61)]),(5,[(2,0,4)]),(6,[(2,0,4)]),(5,[(3,0,4)]),(6,[(3,0,4)]),(6,[(1,1,2)]),(5,[(3,3,29)]),(6,[(2,1,2)]),(2,[(2,1,2)]),(5,[(1,1,3)]),(0,[(1,1,4)]),(5,[(1,1,4)]),(6,[(3,2,31)]),(5,[(1,4,30)]),(6,[(1,1,4)]),(6,[(1,4,41)]),(5,[(0,1,4)]),(6,[(0,1,4)]),(1,[(1,4,5)]),(5,[(0,1,4),(2,0,43)]),(6,[(0,1,4),(2,0,43)]),(1,[(1,2,43)]),(1,[(1,3,43)]),(5,[(0,1,4),(1,3,165)]),(5,[(0,1,4),(2,8,43)]),(6,[(0,1,4),(1,2,43)]),(5,[(0,1,4),(1,3,43)]),(3,[(0,0,19)]),(5,[(1,1,4),(3,0,44)]),(3,[(3,0,44)]),(6,[(1,1,4),(3,0,44)]),(7,[(3,0,44)]),(5,[(1,1,4),(0,8,44)]),(5,[(1,1,4),(3,3,44)]),(6,[(1,1,4),(3,2,44)]),(5,[(2,1,4)]),(6,[(2,1,4)]),(5,[(3,1,4)]),(6,[(3,1,4)]),(5,[(1,3,28),(0,0,8)]),(5,[(0,0,8)]),(5,[(1,3,28)]),(5,[(3,3,28),(1,1,40)]),(5,[(3,0,8)]),(5,[(1,1,3),(0,1,8)]),(5,[(0,1,8)]),(5,[(3,1,8)]),(0,[(1,2,4)]),(1,[(1,2,4)]),(0,[(1,2,4),(1,3,4)]),(1,[(1,2,4),(1,3,4)]),(6,[(1,2,4)]),(5,[(1,3,4)]),(0,[(1,3,4)]),(1,[(1,3,4)]),(5,[(0,4,8),(2,0,20)]),(5,[(0,4,8),(2,1,20)]),(5,[(0,4,8)]),(5,[(1,4,8)]),(5,[(2,4,8)]),(5,[(3,4,8)]),(6,[(3,4,8)]),(5,[(3,3,4)]),(6,[(1,4,8)]),(5,[(3,3,11)]),(6,[(3,2,4)]),(6,[(3,2,15)])]
def h49Pools : BT (Option BoundPool) := buildPoolsBT 8 h49W h49R h49Slices h49Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice9 : Slice h49R h49G (subcubeFast 32 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice8 : Slice h49R h49G (subcubeFast 32 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice7 : Slice h49R h49G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice6 : Slice h49R h49G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice5 : Slice h49R h49G (subcubeFast 8 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice4 : Slice h49R h49G (subcubeFast 6 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice3 : Slice h49R h49G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice2 : Slice h49R h49G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice1 : Slice h49R h49G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice0 : Slice h49R h49G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h49R h49G p.1 p.2) h49Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h49R h49G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h49Slice0) (forall_cons (fun _ h => by cases h; exact h49Slice1) (forall_cons (fun _ h => by cases h; exact h49Slice2) (forall_cons (fun _ h => by cases h; exact h49Slice3) (forall_cons (fun _ h => by cases h; exact h49Slice4) (forall_cons (fun _ h => by cases h; exact h49Slice5) (forall_cons (fun _ h => by cases h; exact h49Slice6) (forall_cons (fun _ h => by cases h; exact h49Slice7) (forall_cons (fun _ h => by cases h; exact h49Slice8) (forall_cons (fun _ h => by cases h; exact h49Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h49R h49G c) h49Pools := buildPoolsBT_sound h49SlicesOk
def h49Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G (3 - 1) xs.toFinset) h49Empty := trivial
def h49Block3_0 : List NodeSpec := [([0,8,77,136],[],[0]),([0,4,8,137],[],[0]),([1,8,135,136],[],[0]),([1,8,76,136],[],[0]),([1,4,8,172],[],[0]),([0,8,101,136],[],[0]),([0,8,97,136],[],[0]),([0,8,69,136],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test3_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Empty 3 h49Block3_0 = true := by decide +kernel
def h49Block3_1 : List NodeSpec := [([0,4,8,185],[],[0]),([1,8,136,184],[],[0]),([1,8,93,136],[],[0]),([1,8,105,136],[],[0]),([1,8,68,136],[],[0]),([1,4,8,187],[],[0]),([1,8,136,139],[],[0]),([0,8,136,174],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test3_1 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Empty 3 h49Block3_1 = true := by decide +kernel
def h49Block3_2 : List NodeSpec := [([1,8,133,136],[],[0]),([1,8,136,145],[],[0]),([0,8,136,170],[],[0]),([0,8,136,180],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test3_2 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Empty 3 h49Block3_2 = true := by decide +kernel
def h49Nodes3 : List NodeSpec := h49Block3_0 ++ h49Block3_1 ++ h49Block3_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check3 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Empty 3 h49Nodes3 = true := by
  unfold h49Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h49Test3_0,h49Test3_1⟩,h49Test3_2⟩
def h49Bucket3 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 3 xs.toFinset) h49Bucket3 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49EmptyOk h49Check3
def h49Block4_0 : List NodeSpec := [([2,3,4,6,25],[2],[0]),([3,4,5,28,34],[],[0]),([2,4,5,31,36],[],[0]),([3,4,5,29,51],[],[0]),([2,4,5,50,52],[],[0]),([0,1,2,4,80],[],[0]),([0,1,3,4,88],[],[0]),([0,4,7,8,77],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test4_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket3 4 h49Block4_0 = true := by decide +kernel
def h49Block4_1 : List NodeSpec := [([0,2,3,77,136],[],[0]),([0,2,3,4,137],[],[0]),([1,4,7,8,135],[],[0]),([1,2,3,135,136],[],[0]),([1,4,7,8,76],[],[0]),([1,2,3,76,136],[],[0]),([1,2,3,4,172],[],[0]),([1,2,3,4,182],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test4_1 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket3 4 h49Block4_1 = true := by decide +kernel
def h49Block4_2 : List NodeSpec := [([2,3,4,65,183],[2],[0]),([0,4,7,8,101],[],[0]),([0,4,7,8,97],[],[0]),([0,4,7,8,69],[],[0]),([0,2,3,4,186],[],[0]),([2,3,4,67,184],[2],[0]),([1,4,7,8,184],[],[0]),([1,4,7,8,93],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test4_2 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket3 4 h49Block4_2 = true := by decide +kernel
def h49Block4_3 : List NodeSpec := [([1,4,7,8,105],[],[0]),([1,4,7,8,68],[],[0]),([1,4,7,8,139],[],[0]),([0,4,7,8,174],[],[0]),([0,1,2,3,190],[],[0]),([2,3,4,133,180],[],[0]),([1,3,4,87,133],[],[0]),([1,2,4,75,133],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test4_3 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket3 4 h49Block4_3 = true := by decide +kernel
def h49Block4_4 : List NodeSpec := [([2,3,4,145,170],[],[0]),([2,3,4,145,180],[],[0]),([0,3,4,87,170],[],[0]),([0,2,4,75,170],[],[0]),([1,4,7,8,133],[],[0]),([1,4,7,8,145],[],[0]),([0,4,7,8,170],[],[0]),([0,4,7,8,180],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test4_4 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket3 4 h49Block4_4 = true := by decide +kernel
def h49Block4_5 : List NodeSpec := [([1,2,4,74,133],[],[0]),([0,2,4,74,170],[],[0]),([1,3,4,86,133],[],[0]),([0,3,4,86,170],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test4_5 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket3 4 h49Block4_5 = true := by decide +kernel
def h49Nodes4 : List NodeSpec := h49Block4_0 ++ h49Block4_1 ++ h49Block4_2 ++ h49Block4_3 ++ h49Block4_4 ++ h49Block4_5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check4 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket3 4 h49Nodes4 = true := by
  unfold h49Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h49Test4_0,h49Test4_1⟩,h49Test4_2⟩,h49Test4_3⟩,h49Test4_4⟩,h49Test4_5⟩
def h49Bucket4 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 4 xs.toFinset) h49Bucket4 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket3Ok h49Check4
def h49Block5_0 : List NodeSpec := [([2,3,4,5,6,8],[0,1,2,3],[0]),([2,3,4,5,28,31],[3],[0]),([1,2,3,4,18,28],[11],[0]),([1,2,3,4,5,36],[10],[0]),([2,3,4,5,29,50],[3],[0]),([1,2,3,4,14,50],[14],[0]),([1,2,3,4,5,51],[10],[0]),([0,2,3,4,18,29],[11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_0 = true := by decide +kernel
def h49Block5_1 : List NodeSpec := [([0,2,3,4,5,52],[3],[0]),([0,2,3,4,14,31],[14],[0]),([0,2,3,4,5,34],[3],[0]),([0,1,3,4,8,14],[14],[0]),([0,1,2,4,8,18],[11],[0]),([0,1,2,3,4,24],[],[0]),([0,1,2,3,4,25],[1,3],[0]),([0,1,3,4,11,14],[1,7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_1 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_1 = true := by decide +kernel
def h49Block5_2 : List NodeSpec := [([0,1,2,3,11,19],[5,11,15],[0]),([0,1,2,3,4,58],[1,3,14],[0]),([0,1,2,3,4,81],[],[0]),([0,1,2,3,4,57],[],[0]),([0,1,2,3,4,59],[],[0]),([0,1,2,4,15,18],[1,7],[0]),([0,1,2,3,15,19],[5,14,15],[0]),([0,1,2,3,4,48],[1,3,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_2 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_2 = true := by decide +kernel
def h49Block5_3 : List NodeSpec := [([0,1,2,3,4,89],[],[0]),([0,1,2,3,4,47],[],[0]),([0,1,2,3,4,49],[],[0]),([0,1,2,3,4,78],[],[0]),([0,1,2,3,4,79],[],[0]),([0,1,2,3,4,92],[1,23],[0]),([0,1,2,3,4,96],[3,24],[0]),([0,1,2,3,4,95],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_3 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_3 = true := by decide +kernel
def h49Block5_4 : List NodeSpec := [([0,1,2,3,4,94],[1],[0]),([0,1,2,3,4,100],[1,31],[0]),([0,1,2,3,4,104],[3,32],[0]),([0,1,2,3,4,103],[3],[0]),([0,1,2,3,4,102],[3],[0]),([0,1,3,4,28,34],[1],[0]),([0,1,2,4,31,36],[3],[0]),([0,1,2,3,4,42],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_4 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_4 = true := by decide +kernel
def h49Block5_5 : List NodeSpec := [([1,2,3,4,53,61],[2],[0]),([1,2,3,4,32,110],[],[0]),([0,1,3,4,32,87],[3],[0]),([0,1,2,4,15,53],[1],[0]),([0,1,2,3,4,111],[3],[0]),([0,1,2,3,4,117],[11],[0]),([0,1,2,4,16,53],[],[0]),([0,1,2,3,4,118],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_5 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_5 = true := by decide +kernel
def h49Block5_6 : List NodeSpec := [([0,1,2,3,4,112],[],[0]),([0,1,2,3,4,116],[],[0]),([0,1,3,4,29,51],[3],[0]),([0,1,2,4,50,52],[1],[0]),([0,1,2,3,4,56],[],[0]),([1,2,3,4,39,61],[2],[0]),([1,2,3,4,55,109],[],[0]),([0,1,3,4,11,39],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_6 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_6 = true := by decide +kernel
def h49Block5_7 : List NodeSpec := [([0,1,2,4,55,75],[3],[0]),([0,1,2,3,4,119],[3],[0]),([0,1,2,3,4,124],[14],[0]),([0,1,3,4,12,39],[],[0]),([0,1,2,3,4,125],[],[0]),([0,1,2,3,4,120],[],[0]),([0,1,2,3,4,123],[],[0]),([0,2,3,4,8,126],[1,48,50],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_7 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_7 = true := by decide +kernel
def h49Block5_8 : List NodeSpec := [([0,2,3,4,8,127],[51],[0]),([0,1,3,4,8,128],[1,14,54],[0]),([0,1,2,4,8,131],[1,11,55],[0]),([0,1,2,3,4,129],[1,56],[0]),([0,1,2,3,4,134],[11,14,57],[0]),([0,1,3,4,128,129],[1,54,58],[0]),([0,1,3,4,128,130],[],[0]),([0,1,2,3,4,130],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_8 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_8 = true := by decide +kernel
def h49Block5_9 : List NodeSpec := [([0,1,2,4,129,131],[1,55,56],[0]),([0,1,2,4,131,132],[],[0]),([0,1,2,3,4,132],[1],[0]),([0,2,3,4,7,77],[3,6,7,60],[0]),([0,2,3,4,8,77],[3,60],[0]),([0,2,3,4,9,77],[3,60],[0]),([0,2,3,4,10,77],[3,60],[0]),([0,2,3,4,8,108],[61],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_9 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_9 = true := by decide +kernel
def h49Block5_10 : List NodeSpec := [([0,1,2,3,4,138],[3,65],[0]),([0,1,2,3,4,114],[66],[0]),([0,1,2,3,4,121],[3],[0]),([0,1,2,3,4,113],[3],[0]),([0,1,3,4,8,140],[14],[0]),([0,1,2,4,8,143],[11],[0]),([0,1,2,3,4,141],[3,7,10],[0]),([0,1,2,3,4,146],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_10 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_10 = true := by decide +kernel
def h49Block5_11 : List NodeSpec := [([0,1,2,3,4,142],[],[0]),([0,1,2,3,4,144],[],[0]),([0,2,3,4,37,44],[2],[0]),([0,2,3,4,30,151],[],[0]),([0,1,3,4,30,87],[10],[0]),([0,1,2,4,15,37],[7],[0]),([0,1,2,3,4,152],[10],[0]),([0,1,2,3,4,157],[11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_11 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_11 = true := by decide +kernel
def h49Block5_12 : List NodeSpec := [([0,1,2,3,4,153],[],[0]),([0,1,2,3,4,156],[],[0]),([0,2,3,4,44,54],[2],[0]),([0,2,3,4,41,150],[],[0]),([0,1,3,4,11,54],[7],[0]),([0,1,2,4,41,75],[10],[0]),([0,1,2,3,4,158],[10],[0]),([0,1,2,3,4,162],[14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_12 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_12 = true := by decide +kernel
def h49Block5_13 : List NodeSpec := [([0,1,3,4,12,54],[],[0]),([0,1,2,3,4,163],[],[0]),([0,1,2,3,4,159],[],[0]),([0,1,2,3,4,161],[],[0]),([1,2,3,4,7,135],[2,3,7,18,85],[0]),([1,2,3,4,8,135],[7,85],[0]),([1,2,3,4,9,135],[],[0]),([1,2,3,4,10,135],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_13 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_13 = true := by decide +kernel
def h49Block5_14 : List NodeSpec := [([1,2,3,4,8,164],[86],[0]),([0,1,3,4,8,165],[7,14,88],[0]),([0,1,2,4,8,168],[7,11,89],[0]),([0,1,2,3,4,166],[7,90],[0]),([0,1,2,3,4,171],[11,14,91],[0]),([0,1,3,4,165,166],[7,88,92],[0]),([0,1,3,4,165,167],[],[0]),([0,1,2,3,4,167],[7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_14 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_14 = true := by decide +kernel
def h49Block5_15 : List NodeSpec := [([0,1,2,4,166,168],[7,89,90],[0]),([0,1,2,4,168,169],[],[0]),([0,1,2,3,4,169],[7],[0]),([1,2,3,4,7,76],[1,6,10,94],[0]),([1,2,3,4,8,76],[10,94],[0]),([1,2,3,4,9,76],[10,94],[0]),([1,2,3,4,10,76],[10,94],[0]),([1,2,3,4,8,149],[95],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_15 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_15 = true := by decide +kernel
def h49Block5_16 : List NodeSpec := [([0,1,2,3,4,173],[10,99],[0]),([0,1,2,3,4,155],[100],[0]),([0,1,2,3,4,160],[10],[0]),([0,1,2,3,4,154],[10],[0]),([0,1,3,4,8,175],[14],[0]),([0,1,2,4,8,178],[11],[0]),([0,1,2,3,4,176],[1,3,10],[0]),([0,1,2,3,4,181],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_16 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_16 = true := by decide +kernel
def h49Block5_17 : List NodeSpec := [([0,1,2,3,4,177],[],[0]),([0,1,2,3,4,179],[],[0]),([1,2,3,4,35,64],[106],[0]),([0,1,3,4,8,51],[11],[0]),([0,1,2,4,8,36],[11],[0]),([1,2,3,4,40,65],[2],[0]),([0,2,3,4,8,183],[1,109],[0]),([0,2,3,4,8,101],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_17 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_17 = true := by decide +kernel
def h49Block5_18 : List NodeSpec := [([0,1,3,4,8,39],[11,37],[0]),([0,1,2,4,8,53],[11,39],[0]),([0,2,3,4,8,97],[],[0]),([0,2,3,4,8,69],[2,3],[0]),([0,2,3,4,33,66],[111],[0]),([0,1,3,4,8,34],[11],[0]),([0,1,2,4,8,52],[11],[0]),([1,2,3,4,8,184],[7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_18 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_18 = true := by decide +kernel
def h49Block5_19 : List NodeSpec := [([1,2,3,4,8,93],[],[0]),([0,2,3,4,38,67],[2],[0]),([0,1,3,4,8,54],[11,72],[0]),([0,1,2,4,8,37],[11,76],[0]),([1,2,3,4,8,105],[],[0]),([1,2,3,4,8,68],[2,10],[0]),([0,1,8,11,15],[11,14,18,116,117,118,119],[0]),([0,1,4,8,11,15],[11,14,18],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_19 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_19 = true := by decide +kernel
def h49Block5_20 : List NodeSpec := [([0,1,4,8,11,75],[11,14],[0]),([0,1,3,8,11,20],[11],[0]),([0,1,3,8,11,23],[11],[0]),([0,1,4,8,15,87],[11,14],[0]),([0,1,2,8,15,20],[14],[0]),([0,1,2,8,15,23],[14],[0]),([1,2,3,4,8,139],[],[0]),([1,2,3,4,8,188],[122],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_20 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_20 = true := by decide +kernel
def h49Block5_21 : List NodeSpec := [([0,2,3,4,8,174],[],[0]),([0,2,3,4,8,189],[123],[0]),([0,1,2,3,20,21],[],[0]),([0,1,2,3,4,23],[],[0]),([1,2,3,4,21,133],[2,3],[0]),([1,2,3,4,21,145],[1],[0]),([0,2,3,4,21,170],[2,10],[0]),([0,2,3,4,21,180],[7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_21 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_21 = true := by decide +kernel
def h49Block5_22 : List NodeSpec := [([0,1,2,3,4,87],[],[0]),([0,1,3,4,21,87],[11],[0]),([0,1,2,3,4,75],[],[0]),([0,1,2,4,21,75],[11],[0]),([0,1,2,3,21,23],[11],[0]),([1,2,3,4,8,133],[],[0]),([1,2,3,4,8,145],[],[0]),([0,2,3,4,8,170],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_22 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_22 = true := by decide +kernel
def h49Block5_23 : List NodeSpec := [([0,2,3,4,8,180],[],[0]),([0,1,3,4,8,87],[11],[0]),([0,1,2,4,8,75],[11],[0]),([0,1,3,4,8,122],[11],[0]),([0,1,2,4,8,115],[11],[0]),([0,1,2,3,22,23],[],[0]),([0,1,2,3,4,21],[1,3,7,10],[0]),([0,1,2,3,11,107],[11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_23 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_23 = true := by decide +kernel
def h49Block5_24 : List NodeSpec := [([0,1,2,3,11,148],[11],[0]),([0,1,3,11,15,87],[18],[0]),([0,1,2,11,15,75],[18],[0]),([0,1,3,4,11,87],[11],[0]),([0,1,2,4,15,75],[11],[0]),([0,1,2,3,11,191],[],[0]),([1,2,3,4,11,133],[],[0]),([0,2,3,4,11,170],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_24 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_24 = true := by decide +kernel
def h49Block5_25 : List NodeSpec := [([0,1,2,3,11,23],[11],[0]),([0,1,2,3,15,192],[],[0]),([0,1,2,3,15,106],[11],[0]),([0,1,2,3,15,147],[11],[0]),([1,2,3,4,15,133],[],[0]),([0,2,3,4,15,170],[],[0]),([0,1,2,3,15,23],[11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_25 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_25 = true := by decide +kernel
def h49Nodes5 : List NodeSpec := h49Block5_0 ++ h49Block5_1 ++ h49Block5_2 ++ h49Block5_3 ++ h49Block5_4 ++ h49Block5_5 ++ h49Block5_6 ++ h49Block5_7 ++ h49Block5_8 ++ h49Block5_9 ++ h49Block5_10 ++ h49Block5_11 ++ h49Block5_12 ++ h49Block5_13 ++ h49Block5_14 ++ h49Block5_15 ++ h49Block5_16 ++ h49Block5_17 ++ h49Block5_18 ++ h49Block5_19 ++ h49Block5_20 ++ h49Block5_21 ++ h49Block5_22 ++ h49Block5_23 ++ h49Block5_24 ++ h49Block5_25
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check5 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Nodes5 = true := by
  unfold h49Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h49Test5_0,h49Test5_1⟩,h49Test5_2⟩,h49Test5_3⟩,h49Test5_4⟩,h49Test5_5⟩,h49Test5_6⟩,h49Test5_7⟩,h49Test5_8⟩,h49Test5_9⟩,h49Test5_10⟩,h49Test5_11⟩,h49Test5_12⟩,h49Test5_13⟩,h49Test5_14⟩,h49Test5_15⟩,h49Test5_16⟩,h49Test5_17⟩,h49Test5_18⟩,h49Test5_19⟩,h49Test5_20⟩,h49Test5_21⟩,h49Test5_22⟩,h49Test5_23⟩,h49Test5_24⟩,h49Test5_25⟩
def h49Bucket5 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 5 xs.toFinset) h49Bucket5 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket4Ok h49Check5
def h49Block6_0 : List NodeSpec := [([2,3,4,5,6],[0,1,2,3,4,5,6],[0]),([1,2,3,4,5,28],[1,3,5,6,8,9,10,11],[0]),([1,2,3,4,5,50],[1,3,5,6,10,12,13,14],[0]),([0,2,3,4,5,29],[3,6,7,8,10,11,15,16],[0]),([0,2,3,4,5,31],[3,6,7,10,12,14,15,17],[0]),([0,1,2,3,4,5,8],[1,3,7,8,10,11,14],[0]),([0,1,2,3,4,5,11],[1,3,5,7,10,11,15,18],[0]),([0,1,2,3,4,14],[1,3,7,8,11,14,18],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_0 = true := by decide +kernel
def h49Block6_1 : List NodeSpec := [([0,1,2,3,4,5,15],[1,3,5,7,10,14,15,18],[0]),([0,1,2,3,4,18],[1,3,7,11,12,14,18],[0]),([0,1,2,3,4,19],[1,3,5,6,7,11,14,15],[0]),([0,1,2,3,4,6,8],[1,2,3,7,10,19],[0]),([0,1,2,3,4,8,26],[1,3,7,10,21],[0]),([0,1,2,3,4,90],[1,2,3,10,11,14,15,18,21,25,26],[0]),([0,1,2,3,4,91],[1,2,3,10,11,14,15,18,22,27,28],[0]),([0,1,2,3,4,8,27],[1,3,7,10,29],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_1 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_1 = true := by decide +kernel
def h49Block6_2 : List NodeSpec := [([0,1,2,3,4,98],[1,2,3,5,7,11,14,18,29,33,34],[0]),([0,1,2,3,4,99],[1,2,3,5,7,11,14,18,30,35,36],[0]),([1,2,3,4,28,55],[1,2,3,5,9,11,14,37],[0]),([0,1,2,3,4,28,31],[1,3,7,10,11,14],[0]),([0,1,2,3,4,36],[1,3,5,7,10,11,14,18,37,38],[0]),([1,2,3,4,32,50],[1,2,3,5,11,13,14,39],[0]),([1,2,3,4,32,61],[1,2,3,11,18,40,41],[0]),([0,1,2,3,4,15,32],[1,3,5,11,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_2 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_2 = true := by decide +kernel
def h49Block6_3 : List NodeSpec := [([0,1,2,3,4,16,32],[1,3,5,14],[0]),([0,1,2,3,4,53],[1,2,3,7,10,11,14,18,39,42],[0]),([0,1,2,3,4,107],[1,3,5,7,10,11,14,43],[0]),([0,1,2,3,4,29,50],[1,3,7,10,11,14],[0]),([0,1,2,3,4,51],[1,3,5,7,10,11,14,18,39,42],[0]),([1,2,3,4,55,61],[1,2,3,14,18,40,44],[0]),([0,1,2,3,4,11,55],[1,3,5,11,14],[0]),([0,1,2,3,4,12,55],[1,3,5,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_3 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_3 = true := by decide +kernel
def h49Block6_4 : List NodeSpec := [([0,1,2,3,4,39],[1,2,3,7,10,11,14,18,37,38],[0]),([0,1,2,3,4,106],[1,3,5,7,10,11,14,45],[0]),([0,2,3,4,126],[1,10,18,48,49,50],[0]),([0,2,3,4,127],[1,7,18,51,52,53],[0]),([0,1,2,3,4,8,60],[1,3,11,14,46],[0]),([0,1,3,4,128],[1,2,18,46,54,58],[0]),([0,1,2,3,4,128],[1,2,3,7,10,11,14,18,46,58],[0]),([0,1,2,4,131],[1,2,18,47,55,59],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_4 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_4 = true := by decide +kernel
def h49Block6_5 : List NodeSpec := [([0,1,2,3,4,131],[1,2,3,7,10,11,14,18,47,59],[0]),([0,2,3,4,77],[2,3,5,6,7,60],[0]),([0,2,3,4,108],[3,5,10,61,62,63,64],[0]),([0,1,2,3,4,8,61],[1,3,41],[0]),([0,1,2,3,4,109],[1,3,5,7,10,11,14,41,67],[0]),([0,1,2,3,4,110],[1,3,5,7,10,11,14,44,66],[0]),([0,1,2,3,4,8,62],[1,3,5,68],[0]),([0,1,2,3,4,8,63],[1,3,11,14,70],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_5 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_5 = true := by decide +kernel
def h49Block6_6 : List NodeSpec := [([0,1,2,3,4,140],[1,3,7,10,11,14,15,18,70],[0]),([0,1,2,3,4,143],[1,3,7,10,11,14,15,18,71],[0]),([0,2,3,4,29,41],[2,7,10,11,14,15,16,72],[0]),([0,1,2,3,4,52],[1,3,7,10,11,14,15,18,72,73],[0]),([0,2,3,4,30,31],[7,10,11,14,15,17,74,75,76],[0]),([0,2,3,4,30,44],[2,7,10,11,18,75,77,78],[0]),([0,1,2,3,4,15,30],[7,10,11,14,15],[0]),([0,1,2,3,4,37],[1,2,3,7,10,11,14,18,76,79],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_6 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_6 = true := by decide +kernel
def h49Block6_7 : List NodeSpec := [([0,1,2,3,4,148],[1,3,7,10,11,14,15,80],[0]),([0,1,2,3,4,34],[1,3,7,10,11,14,15,18,76,79],[0]),([0,2,3,4,41,44],[2,7,10,14,18,77,81],[0]),([0,1,2,3,4,11,41],[7,10,11,14,15],[0]),([0,1,2,3,4,12,41],[7,10,11,15],[0]),([0,1,2,3,4,54],[1,2,3,7,10,11,14,18,72,73],[0]),([0,1,2,3,4,147],[1,3,7,10,11,14,15,82],[0]),([1,2,3,4,135],[3,7,18],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_7 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_7 = true := by decide +kernel
def h49Block6_8 : List NodeSpec := [([1,2,3,4,164],[1,7,18,86,87],[0]),([0,1,2,3,4,8,43],[7,10,11,14,83],[0]),([0,1,3,4,165],[2,7,18,83,88,92],[0]),([0,1,2,3,4,165],[1,2,3,7,10,11,14,18,83,92],[0]),([0,1,2,4,168],[2,7,18,84,89,93],[0]),([0,1,2,3,4,168],[1,2,3,7,10,11,14,18,84,93],[0]),([1,2,3,4,76],[1,2,6,10,15,94],[0]),([1,2,3,4,149],[3,5,10,95,96,97,98],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_8 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_8 = true := by decide +kernel
def h49Block6_9 : List NodeSpec := [([0,1,2,3,4,8,44],[7,10,78],[0]),([0,1,2,3,4,150],[1,3,7,10,11,14,15,78,101],[0]),([0,1,2,3,4,151],[1,3,7,10,11,14,15,81,100],[0]),([0,1,2,3,4,8,45],[7,10,15,102],[0]),([0,1,2,3,4,8,46],[7,10,11,14,104],[0]),([0,1,2,3,4,175],[1,3,5,7,10,11,14,18,104],[0]),([0,1,2,3,4,178],[1,3,5,7,10,11,14,18,105],[0]),([0,1,2,3,4,8,64],[1,3,107],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_9 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_9 = true := by decide +kernel
def h49Block6_10 : List NodeSpec := [([0,1,2,3,4,8,35],[1,3,108],[0]),([0,1,2,3,4,8,40],[1,3,38],[0]),([0,1,2,3,4,8,65],[1,3,110],[0]),([0,1,2,3,4,8,66],[7,10,112],[0]),([0,1,2,3,4,8,33],[7,10,76],[0]),([0,1,2,3,4,8,38],[7,10,79],[0]),([0,1,2,3,4,8,67],[7,10,113],[0]),([0,1,3,4,8,11],[11,14,18,114,115,118],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_10 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_10 = true := by decide +kernel
def h49Block6_11 : List NodeSpec := [([0,1,2,4,8,15],[11,14,18,119,120,121],[0]),([0,1,2,3,4,8,20],[11,14,18,124],[0]),([0,1,2,3,4,21],[1,3,7,10],[0]),([0,1,2,3,4,8,21],[18,125],[0]),([0,1,2,3,4,8,22],[18,126],[0]),([0,1,2,3,4,23],[1,3,7,10,11,14,127,128],[0]),([0,1,2,3,4,8,23],[11,14,18,127],[0]),([0,1,2,3,4,11,70],[1,3,5,11,18],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_11 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_11 = true := by decide +kernel
def h49Block6_12 : List NodeSpec := [([0,1,2,3,4,11,71],[1,3,5],[0]),([0,1,2,3,4,11,72],[7,10,11,15,18],[0]),([0,1,2,3,4,11,73],[7,10,15],[0]),([0,1,2,3,11,15],[5,11,14,15,18,118,119],[0]),([0,1,2,3,4,11,15],[11,14,18,118,119],[0]),([0,1,2,3,11,17],[5,11,14,15,18,118,129],[0]),([0,1,2,3,4,11,21],[5,14,15,130],[0]),([0,1,2,3,4,75],[1,3,7,10,11,14,18,118,131],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_12 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_12 = true := by decide +kernel
def h49Block6_13 : List NodeSpec := [([0,1,2,3,4,11,75],[11,14,18,118],[0]),([0,1,2,3,13,15],[5,11,14,15,18,119,132],[0]),([0,1,2,3,4,115],[1,3,5,7,10,11,14,15,18,119,133],[0]),([0,1,2,3,4,15,82],[1,3,5,14,18],[0]),([0,1,2,3,4,15,83],[1,3,5],[0]),([0,1,2,3,4,15,84],[7,10,14,15,18],[0]),([0,1,2,3,4,15,85],[7,10,15],[0]),([0,1,2,3,4,15,21],[5,11,15,125],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_13 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_13 = true := by decide +kernel
def h49Block6_14 : List NodeSpec := [([0,1,2,3,4,87],[1,3,7,10,11,14,18,119,133],[0]),([0,1,2,3,4,15,87],[11,14,18,119],[0]),([0,1,2,3,4,122],[1,3,5,7,10,11,14,15,18,118,131],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_14 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_14 = true := by decide +kernel
def h49Nodes6 : List NodeSpec := h49Block6_0 ++ h49Block6_1 ++ h49Block6_2 ++ h49Block6_3 ++ h49Block6_4 ++ h49Block6_5 ++ h49Block6_6 ++ h49Block6_7 ++ h49Block6_8 ++ h49Block6_9 ++ h49Block6_10 ++ h49Block6_11 ++ h49Block6_12 ++ h49Block6_13 ++ h49Block6_14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check6 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Nodes6 = true := by
  unfold h49Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h49Test6_0,h49Test6_1⟩,h49Test6_2⟩,h49Test6_3⟩,h49Test6_4⟩,h49Test6_5⟩,h49Test6_6⟩,h49Test6_7⟩,h49Test6_8⟩,h49Test6_9⟩,h49Test6_10⟩,h49Test6_11⟩,h49Test6_12⟩,h49Test6_13⟩,h49Test6_14⟩
def h49Bucket6 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 6 xs.toFinset) h49Bucket6 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket5Ok h49Check6
def h49Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[1,3,5,7,8,11,12,14,15,18],[0]),([0,1,2,3,4,6],[1,2,3,5,7,10,11,14,18,19,20],[0]),([0,1,2,3,4,26],[1,2,3,5,7,10,11,14,15,18,21,22],[0]),([0,1,2,3,4,27],[1,2,3,5,7,11,14,18,29,30],[0]),([0,1,2,3,4,28],[1,2,3,5,7,10,11,14,18,37],[0]),([0,1,2,3,4,32],[1,2,5,7,10,11,14,18],[0]),([0,1,2,3,4,50],[1,2,3,5,7,10,11,14,18,39],[0]),([0,1,2,3,4,55],[1,2,5,7,10,11,14,18],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test7_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket6 7 h49Block7_0 = true := by decide +kernel
def h49Block7_1 : List NodeSpec := [([0,1,2,3,4,60],[1,2,3,7,10,11,14,18,46,47],[0]),([0,1,2,3,4,61],[1,2,3,5,7,10,11,14,15,18,41,44],[0]),([0,1,2,3,4,62],[1,2,3,5,7,10,11,14,18,68,69],[0]),([0,1,2,3,4,63],[1,2,3,7,10,11,14,15,18,70,71],[0]),([0,1,2,3,4,29],[1,2,3,7,10,11,14,15,18,72],[0]),([0,1,2,3,4,30],[1,2,3,7,11,14,15,18,74],[0]),([0,1,2,3,4,31],[1,2,3,7,10,11,14,15,18,76],[0]),([0,1,2,3,4,41],[1,2,3,7,11,14,15,18],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test7_1 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket6 7 h49Block7_1 = true := by decide +kernel
def h49Block7_2 : List NodeSpec := [([0,1,2,3,4,43],[1,2,3,7,10,11,14,18,83,84],[0]),([0,1,2,3,4,44],[1,2,3,5,7,10,11,14,15,18,78,81],[0]),([0,1,2,3,4,45],[1,2,3,7,10,11,14,15,18,102,103],[0]),([0,1,2,3,4,46],[1,2,3,5,7,10,11,14,18,104,105],[0]),([0,1,2,3,4,8],[1,3,7,10,11,14,18],[0]),([0,1,2,3,4,11],[1,3,5,7,10,11,14,15,18,118],[0]),([0,1,2,3,4,13],[1,3,5,7,10,11,14,15,18,132],[0]),([0,1,2,3,4,15],[1,3,5,7,10,11,14,15,18,119],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test7_2 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket6 7 h49Block7_2 = true := by decide +kernel
def h49Block7_3 : List NodeSpec := [([0,1,2,3,4,17],[1,3,5,7,10,11,14,15,18,129],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test7_3 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket6 7 h49Block7_3 = true := by decide +kernel
def h49Nodes7 : List NodeSpec := h49Block7_0 ++ h49Block7_1 ++ h49Block7_2 ++ h49Block7_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check7 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket6 7 h49Nodes7 = true := by
  unfold h49Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h49Test7_0,h49Test7_1⟩,h49Test7_2⟩,h49Test7_3⟩
def h49Bucket7 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 7 xs.toFinset) h49Bucket7 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket6Ok h49Check7
def h49Block8_0 : List NodeSpec := [([0,1,2,3,4],[11,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test8_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket7 8 h49Block8_0 = true := by decide +kernel
def h49Nodes8 : List NodeSpec := h49Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check8 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket7 8 h49Nodes8 = true := h49Test8_0
def h49Bucket8 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 8 xs.toFinset) h49Bucket8 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket7Ok h49Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bound : Lower h49R h49G 9 := lower_of_forestBT (essPairs := [(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,6,22),(VAR 5,2,34)]) (by decide +kernel) h49Bucket8Ok (by decide +kernel)
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfeeaeaa8eac0c000feeaeaa8eac0c000
def h0Pos : List Nat := [14,25,15,27,14,15,29,14,35,15,22,23,58,35,35,37,25,25,22,37,22,41,49,30,30]
def h0Neg : List Nat := [12,24,13,26,10,11,28,6,34,7,6,7,26,3,33,33,17,9,20,5,18,33,33,28,26]
def h0Mask : Nat := fullMask 25
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x6beb6e,0x6bea24),(0xcccccccccccccccccccccccccccccccc,0x1947fbd,0x1103fb8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x19c8ef5,0x8c0ec5),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1a312ff,0x182107f),(0xffff0000ffff0000ffff0000ffff0000,0x1d71c4a,0x195104a),(0xffffffff00000000ffffffff00000000,0x68f100,0x60c100)]
def h0Steps : List (Nat × Nat × Nat) := [(0,3,4)]
def h0W : BT Decor := buildWiresBT 3 h0Base h0Steps
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
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,9),some (subcubeFast 0 2,8),some (subcubeFast 0 4,8),some (subcubeFast 0 8,8),some (subcubeFast 0 16,8),some (subcubeFast 0 32,9),some (subcubeFast 1 0,8),some (subcubeFast 2 0,8),some (subcubeFast 4 0,8),some (subcubeFast 8 0,7),some (subcubeFast 8 32,6)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 4 h0SliceList
def h0Specs : List PoolSpec := [(0,[]),(7,[]),(1,[]),(5,[]),(8,[]),(2,[]),(0,[(0,3,4)]),(6,[]),(7,[(0,3,4)]),(1,[(0,3,4)]),(5,[(0,3,4)]),(8,[(0,3,4)]),(2,[(0,3,4)]),(3,[]),(4,[]),(9,[]),(10,[])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 8 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 2 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 1 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 32) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 16) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 8) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (9 - 1) xs.toFinset) h0Empty := trivial
def h0Block9_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 9 h0Block9_0 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 9 h0Nodes9 = true := h0Test9_0
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check9
def h0Block10_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,13,14],[0])]
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
lemma h0Bound : Lower h0R h0G 11 := lower_of_forestBT (essPairs := [(VAR 0,24,25),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,6,22),(VAR 5,3,35)]) (by decide +kernel) h0Bucket10Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 0]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 16]⟩]
def wo : Nat := 17
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276808360 * 2 ^ 32 + 3938500608) ||| ((4276808360 * 2 ^ 32 + 3938500608) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4276808360 * 2 ^ 32 + 3938500608) ||| ((4276808360 * 2 ^ 32 + 3938500608) <<< 64)) 11 := h0Bound
end PEqualNP.Outside.L_meta_48871
theorem PEqualNP.Outside.L_meta_48871 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808360 * 2 ^ 32 + 3938500608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 3938500608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_48871.table2_of_lower (4276808360 * 2 ^ 32 + 3938500608) (by decide) (by decide) (by decide) (by decide)
    11 PEqualNP.Outside.L_meta_48871.low_root
    PEqualNP.Outside.L_meta_48871.wit PEqualNP.Outside.L_meta_48871.wo (by decide)
    PEqualNP.Outside.L_meta_48871.wit_mono PEqualNP.Outside.L_meta_48871.wit_eval s hcs
