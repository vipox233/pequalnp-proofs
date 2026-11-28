import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_47471
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
def h1R : List Nat := varsOf 26
def h1G : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
def h1Pos : List Nat := [18,24,10,10,24,18]
def h1Neg : List Nat := [16,16,2,8,8,2]
def h1Mask : Nat := fullMask 6
def h1Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h1Steps : List (Nat × Nat × Nat) := []
def h1W : BT Decor := buildWiresBT 2 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(1,3)],[(1,4)],[(3,4),(1,3)],[(3,4),(1,4)]]
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
lemma h1Bound : Lower h1R h1G 4 := lower_of_forestBT (essPairs := [(VAR 1,8,10),(VAR 3,2,10),(VAR 4,2,18)]) (by decide +kernel) h1Bucket3Ok (by decide +kernel)
def h2R : List Nat := varsOf 27
def h2G : Nat := 0xaa888800aa888800aa888800aa888800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,10,11)]) (by decide +kernel) h1Bound
def h3R : List Nat := varsOf 28
def h3G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 4 := carry_of (swaps := [(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h4R : List Nat := varsOf 29
def h4G : Nat := 0xaaa0a000aaa0a000aaa0a000aaa0a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 5 := carry_of (swaps := [(1,2)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h5R : List Nat := varsOf 15
def h5G : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def h5Pos : List Nat := [5,14,5,9,3,5,14,9,14,3,3,7,7]
def h5Neg : List Nat := [4,12,6,8,2,1,10,1,6,1,0,6,1]
def h5Mask : Nat := fullMask 13
def h5Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7869,4768),(0xcccccccccccccccccccccccccccccccc,8018,2388),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6503,2311),(0xff00ff00ff00ff00ff00ff00ff00ff00,458,74)]
def h5Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,1,2),(1,1,2),(2,1,2),(1,2,4),(2,2,4),(0,2,5),(3,2,5),(1,3,10),(2,3,10)]
def h5W : BT Decor := buildWiresBT 5 h5Base h5Steps
def h5AutoList : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3)],[(2,3),(1,2)],[(2,3),(1,3)]]
def h5Autos : BT (List (Nat × Nat)) := btOfList 3 h5AutoList
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
def h5Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,3,11],[]),([0,1,3,12],[]),([0,1,3,13],[]),([0,1,3,14],[]),([0,3,8,9],[]),([0,1,2,15],[]),([0,1,2,16],[])]
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
def h5Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0,1]),([0,1,2,3,5],[],[0,1]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test4_0 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket3 4 h5Block4_0 = true := by decide +kernel
def h5Nodes4 : List NodeSpec := h5Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Check4 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket3 4 h5Nodes4 = true := h5Test4_0
def h5Bucket4 : BT (List (List Nat)) := buildBucketsBT h5W h5Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h5G 4 xs.toFinset) h5Bucket4 := buildBucketsBT_sound (by decide) h5Pairs h5WOk h5PoolsOk h5AutosOk h5Bucket3Ok h5Check4
def h5Block5_0 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test5_0 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket4 5 h5Block5_0 = true := by decide +kernel
def h5Nodes5 : List NodeSpec := h5Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Check5 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket4 5 h5Nodes5 = true := h5Test5_0
def h5Bucket5 : BT (List (List Nat)) := buildBucketsBT h5W h5Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h5G 5 xs.toFinset) h5Bucket5 := buildBucketsBT_sound (by decide) h5Pairs h5WOk h5PoolsOk h5AutosOk h5Bucket4Ok h5Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) h5Bucket5Ok (by decide +kernel)
def h6R : List Nat := varsOf 23
def h6G : Nat := 0xeaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 6 := carry_of (swaps := [(3,4)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h7R : List Nat := varsOf 25
def h7G : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 4 := carry_of (swaps := [(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h8R : List Nat := varsOf 27
def h8G : Nat := 0xeeaaaa00eeaaaa00eeaaaa00eeaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,24,26)]) (by decide +kernel) h7Bound
def h9R : List Nat := varsOf 29
def h9G : Nat := 0xfaaaaa00faaaaa00faaaaa00faaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 5 := carry_of (swaps := [(1,2)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h10R : List Nat := varsOf 30
def h10G : Nat := 0xfffcfc00fffcfc00fffcfc00fffcfc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,8,10)]) (by decide +kernel) h3Bound
def h11R : List Nat := varsOf 31
def h11G : Nat := 0xeaa8a800eaa8a800eaa8a800eaa8a800
def h11Pos : List Nat := [13,30,13,25,30,13,21,30,11,30,19,11,13,21,19,11,25,15,21,25,19,15,25,27,11,30,19,11,30,25,25,25,19,25,23,15,30,13,19,30,29]
def h11Neg : List Nat := [12,28,14,24,26,9,20,22,3,14,3,10,5,17,17,9,9,14,5,17,18,7,1,26,8,20,26,26,7,16,26,28,1,8,7,9,6,7,7,18,28]
def h11Mask : Nat := fullMask 41
def h11Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x16fedfffd6d,0x6d106df520),(0xcccccccccccccccccccccccccccccccc,0xdd1fb2cf92,0xf45cb20f94),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1bc122632f7,0x174922612c7),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bafbeb9bbf,0x10acd838a3f),(0xffff0000ffff0000ffff0000ffff0000,0x1d7f6dd66da,0x180ee9860da)]
def h11Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,3),(3,0,3),(0,0,4),(3,0,4),(0,1,2),(1,1,2),(2,1,2),(0,1,3),(3,1,3),(0,0,17),(2,0,17),(0,2,4),(1,2,5),(2,2,5),(0,3,4),(1,3,4),(2,3,5),(2,4,5),(0,3,26),(0,4,17),(2,4,17),(2,0,29),(0,3,29),(2,3,29),(3,1,4),(0,0,21),(0,0,23),(1,0,23),(2,0,23),(3,0,23),(1,1,23),(2,1,23),(1,5,23),(0,1,41),(2,4,27),(0,2,6),(3,2,6),(0,3,6),(1,1,46),(0,4,46),(2,4,46),(1,1,48),(2,6,23),(2,3,8),(0,4,52),(2,4,52),(1,8,23),(2,1,53),(1,9,11),(2,3,11),(1,4,9),(2,4,9),(2,4,58),(2,2,35),(2,3,12),(1,9,12),(0,3,34),(2,3,34),(0,3,14),(2,0,67),(0,4,67),(2,4,67),(0,4,14),(2,4,65),(3,9,14),(2,3,33),(0,0,74),(2,4,74),(1,9,33),(2,4,19),(3,1,36),(2,14,23),(2,3,20),(1,16,20),(1,2,80),(2,3,15),(1,15,23),(3,15,23),(1,2,86),(2,4,86),(3,35,36),(3,31,39),(2,2,28),(2,2,40),(0,24,83)]
def h11W : BT Decor := buildWiresBT 7 h11Base h11Steps
def h11AutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(1,2)],[(3,4),(1,2)]]
def h11Autos : BT (List (Nat × Nat)) := btOfList 2 h11AutoList
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
def h11SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 6,4),some (subcubeFast 0 8,6),some (subcubeFast 0 16,6),some (subcubeFast 2 0,5),some (subcubeFast 2 1,4),some (subcubeFast 4 0,5),some (subcubeFast 4 1,4)]
def h11Slices : BT (Option (Nat × Nat)) := btOfList 4 h11SliceList
def h11Specs : List PoolSpec := [(0,[]),(6,[]),(7,[]),(4,[(0,0,1)]),(5,[(0,0,1)]),(1,[]),(9,[]),(3,[]),(2,[(3,1,3)]),(8,[(0,0,1)]),(4,[]),(0,[(1,2,5)]),(4,[(0,0,1),(1,2,5)]),(5,[(0,0,1),(1,2,5)]),(2,[]),(1,[(1,2,5)]),(0,[(2,2,5)]),(4,[(0,0,1),(2,2,5)]),(5,[(0,0,1),(2,2,5)]),(1,[(2,2,5)]),(8,[]),(4,[(0,0,1),(1,5,23)]),(4,[(0,0,1),(2,4,5)]),(5,[(0,0,1),(2,3,5)]),(5,[]),(4,[(1,0,1)]),(5,[(1,0,1)]),(4,[(1,0,1),(0,2,6)]),(5,[(1,0,1),(0,2,6)]),(6,[(0,2,6)]),(4,[(1,0,1),(3,2,6)]),(5,[(1,0,1),(3,2,6)]),(6,[(3,2,6)]),(6,[(0,3,6)]),(4,[(1,0,1),(0,4,46)]),(4,[(1,0,1),(2,6,23)]),(5,[(1,0,1),(0,3,6)]),(4,[(2,0,1)]),(5,[(2,0,1)]),(4,[(3,0,1)]),(5,[(3,0,1)]),(4,[(0,0,4)]),(5,[(0,0,3)]),(6,[(0,0,3),(0,0,4)]),(8,[(0,0,3),(0,0,4)]),(4,[(3,0,4)]),(6,[(0,0,3)]),(8,[(0,0,3)]),(5,[(0,0,23)]),(4,[(2,4,9)]),(5,[(3,0,3)]),(5,[(2,3,11)]),(4,[(0,1,2)]),(5,[(0,1,2)]),(4,[(0,1,2),(1,1,2)]),(5,[(0,1,2),(1,1,2)]),(0,[(1,1,2)]),(4,[(1,1,2)]),(5,[(1,1,2)]),(6,[(0,0,21)]),(2,[(0,1,3)]),(4,[(2,1,2)]),(5,[(2,1,2)]),(4,[(2,1,2),(1,15,23)]),(4,[(2,1,2),(3,15,23)]),(5,[(2,1,2),(2,3,15)]),(5,[(0,1,3)]),(4,[(3,1,4)]),(2,[(3,1,4)]),(5,[(2,3,33)]),(5,[(3,1,3)]),(4,[(2,0,17)]),(6,[(2,0,17)]),(4,[(2,4,17)]),(4,[(0,0,23)]),(4,[(1,0,23),(3,1,36)]),(4,[(1,0,23)]),(4,[(2,0,23)]),(5,[(2,0,23)]),(4,[(3,0,23)]),(4,[(2,4,17),(1,1,23)]),(4,[(1,1,23)]),(4,[(2,1,23),(2,2,40)]),(4,[(2,1,23)]),(4,[(0,4,17),(2,2,28)]),(4,[(0,4,17)])]
def h11Pools : BT (Option BoundPool) := buildPoolsBT 7 h11W h11R h11Slices h11Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice9 : Slice h11R h11G (subcubeFast 4 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice8 : Slice h11R h11G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice7 : Slice h11R h11G (subcubeFast 2 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice6 : Slice h11R h11G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice5 : Slice h11R h11G (subcubeFast 0 16) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice4 : Slice h11R h11G (subcubeFast 0 8) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice3 : Slice h11R h11G (subcubeFast 0 6) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice2 : Slice h11R h11G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice1 : Slice h11R h11G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Slice0 : Slice h11R h11G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h11R h11G p.1 p.2) h11Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h11R h11G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h11Slice0) (forall_cons (fun _ h => by cases h; exact h11Slice1) (forall_cons (fun _ h => by cases h; exact h11Slice2) (forall_cons (fun _ h => by cases h; exact h11Slice3) (forall_cons (fun _ h => by cases h; exact h11Slice4) (forall_cons (fun _ h => by cases h; exact h11Slice5) (forall_cons (fun _ h => by cases h; exact h11Slice6) (forall_cons (fun _ h => by cases h; exact h11Slice7) (forall_cons (fun _ h => by cases h; exact h11Slice8) (forall_cons (fun _ h => by cases h; exact h11Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h11R h11G c) h11Pools := buildPoolsBT_sound h11SlicesOk
def h11Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G (3 - 1) xs.toFinset) h11Empty := trivial
def h11Block3_0 : List NodeSpec := nodesWithIdentity [([2,23,50,57],[]),([2,23,56,57],[]),([2,23,42,57],[]),([1,23,57,83],[]),([0,1,23,93],[]),([1,23,57,87],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test3_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 3 h11Block3_0 = true := by decide +kernel
def h11Nodes3 : List NodeSpec := h11Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check3 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 3 h11Nodes3 = true := h11Test3_0
def h11Bucket3 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 3 xs.toFinset) h11Bucket3 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11EmptyOk h11Check3
def h11Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,72],[]),([0,3,4,50,62],[]),([0,2,4,50,58],[]),([0,3,4,56,62],[]),([0,2,3,50,59],[]),([0,3,4,13,80],[7]),([0,4,14,16,81],[]),([1,2,3,4,89],[]),([0,2,23,24,50],[]),([0,2,23,24,56],[]),([0,2,23,24,42],[]),([0,2,3,4,90],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test4_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket3 4 h11Block4_0 = true := by decide +kernel
def h11Block4_1 : List NodeSpec := nodesWithIdentity [([0,3,4,40,91],[7]),([0,1,23,24,83],[]),([0,1,23,24,87],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test4_1 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket3 4 h11Block4_1 = true := by decide +kernel
def h11Nodes4 : List NodeSpec := h11Block4_0 ++ h11Block4_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check4 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket3 4 h11Nodes4 = true := by
  unfold h11Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h11Test4_0,h11Test4_1⟩
def h11Bucket4 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 4 xs.toFinset) h11Bucket4 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11Bucket3Ok h11Check4
def h11Block5_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,17,26],[]),([0,2,3,4,5,29],[7]),([0,1,3,4,21,23],[1,12,15]),([0,1,3,4,22,23],[17]),([0,1,2,3,4,41],[0,21]),([0,1,2,3,4,27],[22]),([0,1,2,3,4,43],[1]),([0,1,3,4,23,44],[5,27,29]),([0,1,3,4,23,45],[30]),([0,1,2,4,23,46],[5,24,33]),([0,1,2,3,4,48],[5,34]),([0,1,2,3,4,51],[10,24,35])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_0 = true := by decide +kernel
def h11Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,2,4,46,48],[5,33,36]),([0,1,2,4,46,49],[]),([0,1,2,3,4,49],[0]),([0,1,2,4,23,52],[24]),([0,1,2,3,4,55],[]),([0,1,2,3,4,53],[1,14,20]),([0,1,2,3,4,54],[]),([1,2,9,11,23],[0,10,24,41,42,43,44]),([1,2,4,9,11,58],[0]),([0,1,2,9,11,23],[0,10,24]),([0,1,2,4,9,58],[10]),([0,1,2,3,4,35],[1,5,14,20])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_1 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_1 = true := by decide +kernel
def h11Block5_2 : List NodeSpec := nodesWithIdentity [([1,2,3,4,9,64],[]),([1,2,3,4,9,34],[2,6,10]),([0,1,2,4,9,67],[0,5,14]),([0,1,2,3,4,65],[1,5,24]),([0,1,2,3,4,73],[]),([0,1,2,4,9,74],[0]),([0,1,2,3,33,60],[1]),([0,1,2,3,4,77],[24]),([0,1,2,3,4,75],[1]),([1,2,3,4,9,19],[10]),([1,2,4,9,23,36],[10]),([1,2,4,9,23,37],[10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_2 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_2 = true := by decide +kernel
def h11Block5_3 : List NodeSpec := [([0,1,2,9,23,60],[10,24],[0]),([0,1,2,3,4,37],[],[0]),([1,2,3,4,35,37],[10],[0]),([0,2,3,4,35,50],[1,7],[0,1]),([0,2,3,4,35,56],[5],[0,2]),([0,1,2,3,4,58],[],[0]),([0,1,2,4,35,58],[10],[0,2]),([1,2,3,4,9,37],[10],[0]),([0,2,3,4,9,50],[],[0,1]),([0,3,4,13,14,23],[1,5,7,54],[0]),([0,1,2,3,4,66],[],[0]),([0,3,4,14,16,20],[1],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_3 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_3 = true := by decide +kernel
def h11Block5_4 : List NodeSpec := [([0,2,3,4,16,71],[10],[0]),([0,2,3,4,14,76],[20],[0,3]),([0,1,2,4,23,67],[24],[0]),([0,1,2,3,4,69],[],[0]),([0,1,2,3,4,80],[1,5],[0]),([0,1,2,3,4,68],[],[0]),([0,1,2,3,4,70],[],[0]),([0,1,2,3,4,85],[1,63],[0]),([0,1,2,3,4,86],[5,64],[0]),([0,1,2,3,4,88],[1],[0]),([0,1,2,4,16,81],[5],[0]),([0,1,2,3,4,82],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_4 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_4 = true := by decide +kernel
def h11Block5_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,78],[]),([0,1,2,3,4,30],[]),([1,2,3,4,35,36],[]),([0,2,3,4,23,50],[]),([0,2,3,4,23,56],[]),([0,1,2,4,23,58],[10]),([0,2,3,4,23,42],[]),([0,2,3,4,23,79],[75]),([1,2,3,4,37,38],[]),([0,1,2,4,23,63],[10]),([0,2,3,4,31,39],[80]),([0,1,2,4,23,32],[10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_5 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_5 = true := by decide +kernel
def h11Block5_6 : List NodeSpec := nodesWithIdentity [([0,2,3,4,28,40],[7]),([0,1,3,4,23,83],[1,7]),([0,1,3,4,23,92],[82]),([0,1,3,4,23,87],[]),([0,1,3,4,23,91],[5,84]),([0,1,2,4,23,74],[10,69])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_6 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_6 = true := by decide +kernel
def h11Nodes5 : List NodeSpec := h11Block5_0 ++ h11Block5_1 ++ h11Block5_2 ++ h11Block5_3 ++ h11Block5_4 ++ h11Block5_5 ++ h11Block5_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check5 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Nodes5 = true := by
  unfold h11Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h11Test5_0,h11Test5_1⟩,h11Test5_2⟩,h11Test5_3⟩,h11Test5_4⟩,h11Test5_5⟩,h11Test5_6⟩
def h11Bucket5 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 5 xs.toFinset) h11Bucket5 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11Bucket4Ok h11Check5
def h11Block6_0 : List NodeSpec := [([0,2,3,4,5,17],[0,1,3,5,7,8,9,10],[0]),([0,1,3,4,21],[1,2,7,11,12,13,14,15],[0]),([0,1,3,4,22],[1,2,16,17,18,19,20],[0]),([0,1,2,3,4,5,23],[1,3,5],[0]),([0,1,2,3,4,25],[0,1,2,3,5,10,14,20,23,24],[0,1]),([0,1,3,4,44],[0,5,20,27,28,29],[0]),([0,1,3,4,45],[0,5,14,30,31,32],[0]),([0,1,2,3,4,6,23],[0,1,5,10,24,25],[0,1]),([0,1,2,4,46],[0,2,5,6,25,33,36],[0]),([0,1,2,3,4,46],[0,2,5,6,10,14,20,24,25,33,36],[0]),([0,1,2,3,4,7,23],[1,2,5,37],[0]),([0,1,2,3,4,8,23],[0,1,5,10,24,39],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_0 = true := by decide +kernel
def h11Block6_1 : List NodeSpec := [([0,1,2,3,4,52],[0,1,6,10,14,20,24,39],[0]),([1,2,3,4,9,11],[0,2,6,10,24,41,42],[0,1]),([0,1,2,3,4,9,11],[0,10,24,41,42],[0,1]),([1,2,3,4,9,12],[0,2,6,10,24,42,45],[0]),([0,1,2,3,4,9,14],[0,1,2,5,6,10,14,20],[0]),([0,1,2,3,4,9,33],[1,2,5,10,24],[0]),([0,1,2,3,4,9,47],[0,1,2,5,10],[0]),([0,1,2,3,4,9,18],[1,2,5],[0]),([0,1,2,4,9,23],[0,10,24,42,46,47],[0]),([0,1,2,3,4,35],[1,5,14,20],[0,1,2]),([0,1,2,3,4,9,35],[2,6,24,48],[0,1,2]),([0,1,2,3,4,60],[0,1,5,10,14,20,24,42,49],[0,1,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_1 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_1 = true := by decide +kernel
def h11Block6_2 : List NodeSpec := [([0,1,2,3,4,9,60],[0,10,24,42],[0,1]),([0,1,2,3,4,61],[0,1,2,5,6,10,14,20,24,41,51],[0]),([0,3,4,13,14],[1,2,5,7,54,55,56],[0]),([0,1,2,3,4,13,23],[1,5,7,14,20,52],[0]),([0,1,2,3,4,34],[0,1,2,5,6,9,10,11,14,24,59],[0,1]),([0,2,3,4,14,16],[1,2,5,10,20,56,57,60],[0]),([0,1,2,3,4,14,23],[1,5,10,14,20,24,57],[0,1]),([0,1,2,3,4,67],[0,1,5,10,14,24,57],[0,1,3]),([0,1,2,3,4,15,23],[1,5,14,20,61],[0]),([0,1,2,3,4,84],[0,1,2,5,7,10,14,24,61,65],[0]),([0,2,3,4,16,33],[1,2,5,10,24,60,66,67,68],[0]),([0,1,2,3,4,16,20],[1,5,10,14,20,24],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_2 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_2 = true := by decide +kernel
def h11Block6_3 : List NodeSpec := [([0,1,2,3,4,76],[0,1,2,5,10,14,20,24,67,69],[0,3]),([0,1,2,3,4,19],[0,1,2,5,10,14,20,24,71,72],[0,1]),([0,1,2,3,4,29],[0,1,5,7,10,14,20,24,70,73],[0,1]),([0,1,2,3,4,23,35],[0,74],[0,1,2]),([0,1,2,3,4,23,36],[0,10,24,76],[0,1,2]),([0,1,2,3,4,37],[1,5,10,14,20,24,77,78],[0]),([0,1,2,3,4,23,37],[0,10,24,77],[0,1]),([0,1,2,3,4,23,38],[0,79],[0,1]),([0,1,2,3,4,23,31],[1,5,73],[0,1]),([0,1,2,3,4,23,39],[1,5,81],[0]),([0,1,2,3,4,23,40],[1,5,83],[0]),([0,1,2,3,4,23,28],[1,5,85],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test6_3 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Block6_3 = true := by decide +kernel
def h11Nodes6 : List NodeSpec := h11Block6_0 ++ h11Block6_1 ++ h11Block6_2 ++ h11Block6_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check6 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket5 6 h11Nodes6 = true := by
  unfold h11Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h11Test6_0,h11Test6_1⟩,h11Test6_2⟩,h11Test6_3⟩
def h11Bucket6 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 6 xs.toFinset) h11Bucket6 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11Bucket5Ok h11Check6
def h11Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,10,14,20,24],[0,1]),([0,1,2,3,4,6],[0,1,2,5,6,10,14,20,24,25,26],[0,1]),([0,1,2,3,4,7],[0,1,2,5,6,7,10,14,20,24,37,38],[0]),([0,1,2,3,4,8],[0,1,6,10,14,20,24,39,40],[0,1]),([0,1,2,3,4,9],[0,1,2,5,6,10,14,20,24,42],[0,2]),([0,1,2,3,4,10],[0,1,2,5,6,10,14,20,24,50],[0,1]),([0,1,2,3,4,13],[0,1,2,5,7,10,20,24,52,53],[0]),([0,1,2,3,4,14],[0,1,2,5,6,10,14,20,24,57,58],[0,1,2,3]),([0,1,2,3,4,15],[0,1,2,5,7,10,14,20,24,61,62],[0,1]),([0,1,2,3,4,16],[0,1,2,7,10,14,20,24,66],[0]),([0,1,2,3,4,17],[0,1,2,5,7,10,14,20,24,70],[0,1]),([0,1,2,3,4,23],[0,1,5,10,14,20,24],[0,1,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test7_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket6 7 h11Block7_0 = true := by decide +kernel
def h11Nodes7 : List NodeSpec := h11Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check7 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket6 7 h11Nodes7 = true := h11Test7_0
def h11Bucket7 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 7 xs.toFinset) h11Bucket7 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11Bucket6Ok h11Check7
def h11Block8_0 : List NodeSpec := [([0,1,2,3,4],[10,24],[0,1,2,3])]
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
lemma h11Bound : Lower h11R h11G 9 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,3,19)]) (by decide +kernel) h11Bucket8Ok (by decide +kernel)
def h12R : List Nat := varsOf 7
def h12G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 4 := carry_of (swaps := [(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h13R : List Nat := varsOf 15
def h13G : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 5 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h14R : List Nat := varsOf 39
def h14G : Nat := 0xe8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(1,2),(2,3)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h15R : List Nat := varsOf 41
def h15G : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 4 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h16R : List Nat := varsOf 43
def h16G : Nat := 0xeeaaeeaaaa00aa00eeaaeeaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 5 := carry_of (swaps := [(4,5)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h17R : List Nat := varsOf 45
def h17G : Nat := 0xfaaafaaaaa00aa00faaafaaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 5 := carry_of (swaps := [(4,5),(1,2)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h18R : List Nat := varsOf 47
def h18G : Nat := 0xe8a8e8a8a800a800e8a8e8a8a800a800
def h18Pos : List Nat := [13,46,13,46,13,37,11,11,13,11,46,35,46,11,37,35,13,37,35]
def h18Neg : List Nat := [12,44,14,42,9,36,8,3,5,9,14,3,38,10,33,33,7,5,42]
def h18Mask : Nat := fullMask 19
def h18Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7ebf5,0x3cb90),(0xcccccccccccccccccccccccccccccccc,0x4beca,0x53c8c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3553f,0x31527),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x137df,0x4265f),(0xffffffff00000000ffffffff00000000,0x6dc2a,0x4d02a)]
def h18Steps : List (Nat × Nat × Nat) := [(0,0,1),(3,0,1),(2,2,5),(0,3,5),(2,3,5),(0,3,6),(2,3,6),(0,1,3),(1,0,12),(2,0,12),(2,2,8),(2,4,11),(0,2,13)]
def h18W : BT Decor := buildWiresBT 5 h18Base h18Steps
def h18AutoList : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)],[(2,5),(1,3)],[(2,3),(1,5)],[(3,5),(2,5),(1,3)],[(3,5),(2,3),(1,5)]]
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
def h18SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 6,4),some (subcubeFast 0 8,5),some (subcubeFast 0 32,5),some (subcubeFast 0 40,4)]
def h18Slices : BT (Option (Nat × Nat)) := btOfList 3 h18SliceList
def h18Specs : List PoolSpec := [(0,[]),(1,[(3,0,1)]),(2,[]),(1,[(0,1,3)]),(3,[]),(1,[]),(4,[]),(5,[]),(4,[(0,1,3)])]
def h18Pools : BT (Option BoundPool) := buildPoolsBT 4 h18W h18R h18Slices h18Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Slice5 : Slice h18R h18G (subcubeFast 0 40) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Slice4 : Slice h18R h18G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Slice3 : Slice h18R h18G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Slice2 : Slice h18R h18G (subcubeFast 0 6) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Slice1 : Slice h18R h18G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Slice0 : Slice h18R h18G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h18R h18G p.1 p.2) h18Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h18R h18G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h18Slice0) (forall_cons (fun _ h => by cases h; exact h18Slice1) (forall_cons (fun _ h => by cases h; exact h18Slice2) (forall_cons (fun _ h => by cases h; exact h18Slice3) (forall_cons (fun _ h => by cases h; exact h18Slice4) (forall_cons (fun _ h => by cases h; exact h18Slice5) (fun _ h => (List.not_mem_nil h).elim)))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h18R h18G c) h18Pools := buildPoolsBT_sound h18SlicesOk
def h18Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G (4 - 1) xs.toFinset) h18Empty := trivial
def h18Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,3,4,15],[]),([0,1,2,3,16],[]),([0,1,3,4,17],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Test4_0 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Empty 4 h18Block4_0 = true := by decide +kernel
def h18Nodes4 : List NodeSpec := h18Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Check4 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Empty 4 h18Nodes4 = true := h18Test4_0
def h18Bucket4 : BT (List (List Nat)) := buildBucketsBT h18W h18Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G 4 xs.toFinset) h18Bucket4 := buildBucketsBT_sound (by decide) h18Pairs h18WOk h18PoolsOk h18AutosOk h18EmptyOk h18Check4
def h18Block5_0 : List NodeSpec := [([0,2,3,4,5,6],[0,1],[0]),([0,2,3,4,5,12],[3,4],[0]),([0,1,3,4,7],[],[0]),([0,1,3,4,5,7],[5],[0]),([0,1,2,3,4,8],[5,6],[0,4]),([0,1,2,3,4,9],[],[0]),([0,1,2,3,4,10],[],[0]),([0,1,2,3,4,11],[6],[0]),([0,1,2,3,4,13],[0,4,5,6],[0,4]),([0,1,2,3,4,14],[],[0])]
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
def h18Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,2,4,5,6],[0,1]),([0,1,2,3,4,6],[0,1,2,4,5,6],[0,1]),([0,1,2,3,4,12],[0,2,3,4,5,6,7,8],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Test6_0 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Bucket5 6 h18Block6_0 = true := by decide +kernel
def h18Nodes6 : List NodeSpec := h18Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Check6 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Bucket5 6 h18Nodes6 = true := h18Test6_0
def h18Bucket6 : BT (List (List Nat)) := buildBucketsBT h18W h18Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G 6 xs.toFinset) h18Bucket6 := buildBucketsBT_sound (by decide) h18Pairs h18WOk h18PoolsOk h18AutosOk h18Bucket5Ok h18Check6
def h18Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,2,4,5,6,7],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Test7_0 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Bucket6 7 h18Block7_0 = true := by decide +kernel
def h18Nodes7 : List NodeSpec := h18Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Check7 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Bucket6 7 h18Nodes7 = true := h18Test7_0
def h18Bucket7 : BT (List (List Nat)) := buildBucketsBT h18W h18Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G 7 xs.toFinset) h18Bucket7 := buildBucketsBT_sound (by decide) h18Pairs h18WOk h18PoolsOk h18AutosOk h18Bucket6Ok h18Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 8 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 5,3,35)]) (by decide +kernel) h18Bucket7Ok (by decide +kernel)
def h19R : List Nat := varsOf 23
def h19G : Nat := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(1,2),(2,3)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h20R : List Nat := varsOf 49
def h20G : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 4 := carry_of (swaps := [(4,5),(3,4),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h21R : List Nat := varsOf 51
def h21G : Nat := 0xeeeeaaaaaaaa0000eeeeaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 5 := carry_of (swaps := [(4,5),(3,4)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h22R : List Nat := varsOf 53
def h22G : Nat := 0xfafaaaaaaaaa0000fafaaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 5 := carry_of (swaps := [(4,5),(3,4),(1,2)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h23R : List Nat := varsOf 55
def h23G : Nat := 0xe8e8a8a8a8a80000e8e8a8a8a8a80000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 8 := carry_of (swaps := [(3,4)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h24R : List Nat := varsOf 11
def h24G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 4 := carry_of (swaps := [(2,3),(3,4),(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h25R : List Nat := varsOf 19
def h25G : Nat := 0xeeee8888eeee8888eeee8888eeee8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 4 := carry_of (swaps := [(2,3),(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h26R : List Nat := varsOf 27
def h26G : Nat := 0xee888888ee888888ee888888ee888888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,17,25)]) (by decide +kernel) h25Bound
def h27R : List Nat := varsOf 43
def h27G : Nat := 0xee88ee88aa88aa88ee88ee88aa88aa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(1,2)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h28R : List Nat := varsOf 51
def h28G : Nat := 0xeeee8888aaaa8888eeee8888aaaa8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(3,4),(1,2)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h29R : List Nat := varsOf 57
def h29G : Nat := 0xffaaaaaaaaaaaa00ffaaaaaaaaaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 6 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(2,3)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h30R : List Nat := varsOf 58
def h30G : Nat := 0xffccccccffcccc00ffccccccffcccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 5 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,2,34)]) (by decide +kernel) h1Bound
def h31R : List Nat := varsOf 59
def h31G : Nat := 0xee888888aa888800ee888888aa888800
def h31Pos : List Nat := [25,58,11,11,19,58,19,35,58,19,58,35,19,25,11,25,43,27]
def h31Neg : List Nat := [24,56,9,10,18,50,26,34,42,3,26,3,17,9,3,17,41,26]
def h31Mask : Nat := fullMask 18
def h31Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3fadd,0x1fa04),(0xcccccccccccccccccccccccccccccccc,0x35ffe,0x24ff8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3e52f,0x3254f),(0xffff0000ffff0000ffff0000ffff0000,0x2b773,0x29473),(0xffffffff00000000ffffffff00000000,0x10da2,0x101a2)]
def h31Steps : List (Nat × Nat × Nat) := [(0,0,2),(0,1,5),(2,1,6),(0,2,3),(2,3,6),(0,0,8),(2,0,8),(0,1,8),(2,1,8),(2,3,5),(2,1,10)]
def h31W : BT Decor := buildWiresBT 4 h31Base h31Steps
def h31AutoList : List (List (Nat × Nat)) := [[],[(3,4)]]
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
def h31SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,6),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 0 40,4),some (subcubeFast 32 0,5),some (subcubeFast 32 1,4)]
def h31Slices : BT (Option (Nat × Nat)) := btOfList 3 h31SliceList
def h31Specs : List PoolSpec := [(1,[]),(1,[(0,0,2)]),(0,[]),(2,[]),(3,[]),(4,[]),(6,[]),(4,[(0,2,3)]),(6,[(0,0,2)]),(5,[]),(7,[]),(1,[(0,2,3)])]
def h31Pools : BT (Option BoundPool) := buildPoolsBT 4 h31W h31R h31Slices h31Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice7 : Slice h31R h31G (subcubeFast 32 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice6 : Slice h31R h31G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice5 : Slice h31R h31G (subcubeFast 0 40) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice4 : Slice h31R h31G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice3 : Slice h31R h31G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice2 : Slice h31R h31G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice1 : Slice h31R h31G (subcubeFast 0 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Slice0 : Slice h31R h31G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h31R h31G p.1 p.2) h31Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h31R h31G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h31Slice0) (forall_cons (fun _ h => by cases h; exact h31Slice1) (forall_cons (fun _ h => by cases h; exact h31Slice2) (forall_cons (fun _ h => by cases h; exact h31Slice3) (forall_cons (fun _ h => by cases h; exact h31Slice4) (forall_cons (fun _ h => by cases h; exact h31Slice5) (forall_cons (fun _ h => by cases h; exact h31Slice6) (forall_cons (fun _ h => by cases h; exact h31Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h31R h31G c) h31Pools := buildPoolsBT_sound h31SlicesOk
def h31Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h31G (4 - 1) xs.toFinset) h31Empty := trivial
def h31Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,4,9],[]),([0,2,3,4,15],[])]
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
def h31Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,6],[4,5,6]),([0,1,2,3,4,7],[5,6]),([0,1,3,4,5,8],[2,4,7]),([0,1,2,3,4,10],[0,5,6]),([0,1,2,3,4,14],[]),([0,1,2,3,4,11],[]),([0,1,2,3,4,12],[]),([0,1,2,3,4,13],[11])]
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
def h31Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,8,9,10],[0]),([0,1,2,3,4,8],[0,2,3,4,5,6,7,11],[0,1])]
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
def h31Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,2,3,4,5,6],[0,1])]
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
lemma h31Bound : Lower h31R h31G 8 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,9,11),(VAR 3,3,11),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h31Bucket7Ok (by decide +kernel)
def h32R : List Nat := varsOf 60
def h32G : Nat := 0xfff0f0f0fff0f000fff0f0f0fff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 5 := carry_of (swaps := [(1,2)]) (roots2 := h30R) (T2 := h30G) (by decide +kernel) h30Bound
def h33R : List Nat := varsOf 61
def h33G : Nat := 0xaaa0a0a0aaa0a000aaa0a0a0aaa0a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 6 := lift_of (z := 32) (o := 1) (essPairs := [(VAR 0,12,13),(VAR 5,5,37)]) (by decide +kernel) h3Bound
def h34R : List Nat := varsOf 30
def h34G : Nat := 0xccc0c000ccc0c000ccc0c000ccc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 5 := carry_of (swaps := [(1,2),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h35R : List Nat := varsOf 44
def h35G : Nat := 0xfff0fff0f000f000fff0fff0f000f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 4 := carry_of (swaps := [(4,5),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h36R : List Nat := varsOf 46
def h36G : Nat := 0xccc0ccc0c000c000ccc0ccc0c000c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 5 := carry_of (swaps := [(4,5),(1,2),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h37R : List Nat := varsOf 52
def h37G : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 4 := carry_of (swaps := [(4,5),(3,4),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h38R : List Nat := varsOf 54
def h38G : Nat := 0xccccc0c0c0c00000ccccc0c0c0c00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 5 := carry_of (swaps := [(4,5),(3,4),(1,2),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h39R : List Nat := varsOf 56
def h39G : Nat := 0xffffff00ff000000ffffff00ff000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 4 := carry_of (swaps := [(4,5),(3,4),(1,2),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h40R : List Nat := varsOf 58
def h40G : Nat := 0xcccccc00cc000000cccccc00cc000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 5 := carry_of (swaps := [(4,5),(3,4),(1,2),(2,3),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
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
def h41R : List Nat := varsOf 60
def h41G : Nat := 0xfff0f000f0000000fff0f000f0000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 7 := carry_of (swaps := [(2,3),(1,2)]) (roots2 := Cofactor12058.R_10) (T2 := Cofactor12058.G_10) (by decide +kernel) Cofactor12058.low_10
namespace Cofactor12058
def G_40 : Nat := 0xfc00c000c0000000fc00c000c0000000
def R_40 : List Nat := varsOf 62
lemma low_40_ok : liftCheck 0 8 R_40 G_40 R_10 G_10 [(VAR 3,30,22)] = true := by decide +kernel
lemma low_40 : Lower R_40 G_40 8 := lift_of low_40_ok low_10

end Cofactor12058
def h42R : List Nat := varsOf 62
def h42G : Nat := 0xccc0c000c0000000ccc0c000c0000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bound : Lower h42R h42G 8 := carry_of (swaps := [(2,3),(1,2)]) (roots2 := Cofactor12058.R_40) (T2 := Cofactor12058.G_40) (by decide +kernel) Cofactor12058.low_40
def h43R : List Nat := varsOf 15
def h43G : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bound : Lower h43R h43G 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h44R : List Nat := varsOf 23
def h44G : Nat := 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bound : Lower h44R h44G 5 := carry_of (swaps := [(2,3),(3,4),(0,1),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h45R : List Nat := varsOf 29
def h45G : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bound : Lower h45R h45G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h3Bound
def h46R : List Nat := varsOf 31
def h46G : Nat := 0xeee8e8a8eee8e8a8eee8e8a8eee8e8a8
def h46Pos : List Nat := [5,14,3,3,14,5,7,3,14,13,25,22,21,25,19,26,13,21,26,26,7,22]
def h46Neg : List Nat := [4,12,1,2,10,1,6,6,6,12,17,6,20,9,17,24,9,17,18,10,1,20]
def h46Mask : Nat := fullMask 22
def h46Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1376ed,0x136424),(0xcccccccccccccccccccccccccccccccc,0x3cc9de,0xc09d8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x331b73,0x201bc3),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xda712,0x9a212),(0xffff0000ffff0000ffff0000ffff0000,0x2efc00,0x26d400)]
def h46Steps : List (Nat × Nat × Nat) := [(1,0,2),(2,1,2)]
def h46W : BT Decor := buildWiresBT 3 h46Base h46Steps
def h46AutoList : List (List (Nat × Nat)) := [[],[(3,4)]]
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
def h46SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5)]
def h46Slices : BT (Option (Nat × Nat)) := btOfList 3 h46SliceList
def h46Specs : List PoolSpec := [(3,[]),(0,[]),(4,[]),(5,[]),(0,[(1,0,2)]),(6,[]),(1,[]),(7,[]),(2,[]),(3,[(2,1,2)])]
def h46Pools : BT (Option BoundPool) := buildPoolsBT 4 h46W h46R h46Slices h46Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice7 : Slice h46R h46G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice6 : Slice h46R h46G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice5 : Slice h46R h46G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice4 : Slice h46R h46G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice3 : Slice h46R h46G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice2 : Slice h46R h46G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice1 : Slice h46R h46G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Slice0 : Slice h46R h46G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h46R h46G p.1 p.2) h46Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h46R h46G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h46Slice0) (forall_cons (fun _ h => by cases h; exact h46Slice1) (forall_cons (fun _ h => by cases h; exact h46Slice2) (forall_cons (fun _ h => by cases h; exact h46Slice3) (forall_cons (fun _ h => by cases h; exact h46Slice4) (forall_cons (fun _ h => by cases h; exact h46Slice5) (forall_cons (fun _ h => by cases h; exact h46Slice6) (forall_cons (fun _ h => by cases h; exact h46Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h46R h46G c) h46Pools := buildPoolsBT_sound h46SlicesOk
def h46Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G (6 - 1) xs.toFinset) h46Empty := trivial
def h46Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8]),([0,1,2,3,4,6],[0,1,2,3,5,6,7,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Test6_0 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Empty 6 h46Block6_0 = true := by decide +kernel
def h46Nodes6 : List NodeSpec := h46Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Check6 : checkNodesBT h46W h46G h46Mask h46Pools h46Autos h46Empty 6 h46Nodes6 = true := h46Test6_0
def h46Bucket6 : BT (List (List Nat)) := buildBucketsBT h46W h46Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h46G 6 xs.toFinset) h46Bucket6 := buildBucketsBT_sound (by decide) h46Pairs h46WOk h46PoolsOk h46AutosOk h46EmptyOk h46Check6
def h46Block7_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,1,2,3,5,6,7,8])]
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
lemma h46Bound : Lower h46R h46G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,6,14),(VAR 4,6,22)]) (by decide +kernel) h46Bucket7Ok (by decide +kernel)
def h47R : List Nat := varsOf 45
def h47G : Nat := 0xfffafffafaaafaaafffafffafaaafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h47Bound : Lower h47R h47G 5 := carry_of (swaps := [(4,5)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h48R : List Nat := varsOf 47
def h48G : Nat := 0xeee8eee8eaa8eaa8eee8eee8eaa8eaa8
def h48Pos : List Nat := [5,14,3,3,14,5,7,3,14,9,13,38,37,35,42,42,37,41,42,38,35,41,7,38]
def h48Neg : List Nat := [4,12,1,2,10,1,6,6,6,1,12,6,36,33,40,10,33,33,34,34,34,40,1,36]
def h48Mask : Nat := fullMask 24
def h48Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7336ed,0x432224),(0xcccccccccccccccccccccccccccccccc,0xdce9de,0x1c89d8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc91d73,0x801dc3),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x26c712,0x20c412),(0xffffffff00000000ffffffff00000000,0xbff800,0xbf7000)]
def h48Steps : List (Nat × Nat × Nat) := [(1,0,2),(1,0,4),(2,1,2),(2,1,4),(1,2,3),(1,0,9),(3,0,9),(0,1,9),(2,1,9),(3,3,5),(0,1,10),(1,3,7)]
def h48W : BT Decor := buildWiresBT 5 h48Base h48Steps
def h48AutoList : List (List (Nat × Nat)) := [[],[(2,3)]]
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
def h48SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 4 0,5),some (subcubeFast 4 32,4),some (subcubeFast 8 0,5),some (subcubeFast 32 0,6)]
def h48Slices : BT (Option (Nat × Nat)) := btOfList 3 h48SliceList
def h48Specs : List PoolSpec := [(2,[]),(0,[]),(3,[]),(4,[]),(7,[(1,0,2)]),(0,[(1,0,2)]),(6,[]),(7,[]),(1,[]),(4,[(1,0,4)]),(0,[(1,0,4)]),(6,[(1,0,4)]),(5,[]),(2,[(2,1,2)]),(7,[(2,1,2)]),(2,[(2,1,4)]),(4,[(2,1,4)]),(6,[(2,1,4)]),(7,[(1,2,3)])]
def h48Pools : BT (Option BoundPool) := buildPoolsBT 5 h48W h48R h48Slices h48Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice7 : Slice h48R h48G (subcubeFast 32 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice6 : Slice h48R h48G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice5 : Slice h48R h48G (subcubeFast 4 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice4 : Slice h48R h48G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice3 : Slice h48R h48G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice2 : Slice h48R h48G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice1 : Slice h48R h48G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Slice0 : Slice h48R h48G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h48R h48G p.1 p.2) h48Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h48R h48G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h48Slice0) (forall_cons (fun _ h => by cases h; exact h48Slice1) (forall_cons (fun _ h => by cases h; exact h48Slice2) (forall_cons (fun _ h => by cases h; exact h48Slice3) (forall_cons (fun _ h => by cases h; exact h48Slice4) (forall_cons (fun _ h => by cases h; exact h48Slice5) (forall_cons (fun _ h => by cases h; exact h48Slice6) (forall_cons (fun _ h => by cases h; exact h48Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h48R h48G c) h48Pools := buildPoolsBT_sound h48SlicesOk
def h48Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G (4 - 1) xs.toFinset) h48Empty := trivial
def h48Block4_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,15],[])]
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
def h48Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,3,4,5,9],[0,6]),([0,1,2,3,4,10],[1,7,8]),([0,1,2,3,4,14],[]),([0,1,3,4,7,9],[1,6]),([0,1,2,3,4,16],[]),([0,1,2,3,4,13],[7,8]),([0,1,2,3,4,11],[7,8]),([0,1,2,3,4,12],[7,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test5_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Block5_0 = true := by decide +kernel
def h48Nodes5 : List NodeSpec := h48Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Check5 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Nodes5 = true := h48Test5_0
def h48Bucket5 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 5 xs.toFinset) h48Bucket5 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket4Ok h48Check5
def h48Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8],[0]),([0,1,2,3,6],[0,2,7,8,9,10,11,12],[0]),([0,1,2,3,4,7],[0,1,2,3,6,7,8,13,14],[0]),([0,1,2,3,8],[1,2,7,8,12,15,16,17],[0]),([0,1,2,3,4,9],[0,1,3,6,7,8,12,18],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test6_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Block6_0 = true := by decide +kernel
def h48Nodes6 : List NodeSpec := h48Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Check6 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Nodes6 = true := h48Test6_0
def h48Bucket6 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 6 xs.toFinset) h48Bucket6 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket5Ok h48Check6
def h48Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,6,7],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test7_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket6 7 h48Block7_0 = true := by decide +kernel
def h48Nodes7 : List NodeSpec := h48Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Check7 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket6 7 h48Nodes7 = true := h48Test7_0
def h48Bucket7 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 7 xs.toFinset) h48Bucket7 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket6Ok h48Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bound : Lower h48R h48G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 5,6,38)]) (by decide +kernel) h48Bucket7Ok (by decide +kernel)
def h49R : List Nat := varsOf 53
def h49G : Nat := 0xfffffafafafaaaaafffffafafafaaaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bound : Lower h49R h49G 5 := carry_of (swaps := [(4,5),(3,4)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h50R : List Nat := varsOf 55
def h50G : Nat := 0xeeeee8e8eaeaa8a8eeeee8e8eaeaa8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bound : Lower h50R h50G 8 := carry_of (swaps := [(3,4)]) (roots2 := h48R) (T2 := h48G) (by decide +kernel) h48Bound
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
def h51R : List Nat := varsOf 57
def h51G : Nat := 0xffffffaaffaaaa00ffffffaaffaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bound : Lower h51R h51G 7 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := Cofactor12058.R_13) (T2 := Cofactor12058.G_13) (by decide +kernel) Cofactor12058.low_13
def h52R : List Nat := varsOf 59
def h52G : Nat := 0xeeeeeeaaeeaaaa00eeeeeeaaeeaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h52Bound : Lower h52R h52G 8 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,24,26)]) (by decide +kernel) h51Bound
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
def nodes_41_3 : List NodeSpec := nodesWithIdentity [([10,12,3,4],[]),([13,11,3,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_3 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_2 3 nodes_41_3 = true := by decide +kernel
def bk_41_3 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_3
set_option maxRecDepth 500000 in
lemma bk_41_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 3 xs.toFinset) bk_41_3 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_2_ok chk_41_3
def nodes_41_4 : List NodeSpec := nodesWithIdentity [([10,9,2,3,4],[0,1]),([9,2,11,3,4],[]),([9,12,2,3,4],[]),([13,9,2,3,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_4 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_3 4 nodes_41_4 = true := by decide +kernel
def bk_41_4 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_4
set_option maxRecDepth 500000 in
lemma bk_41_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 4 xs.toFinset) bk_41_4 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_3_ok chk_41_4
def nodes_41_5 : List NodeSpec := nodesWithIdentity [([9,2,3,4],[2,0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_5 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_4 5 nodes_41_5 = true := by decide +kernel
def bk_41_5 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_5
set_option maxRecDepth 500000 in
lemma bk_41_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 5 xs.toFinset) bk_41_5 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_4_ok chk_41_5
def nodes_41_6 : List NodeSpec := nodesWithIdentity [([5,8,2,3,4],[3,4,2,0]),([7,6,2,3,4],[5,4,2,0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_6 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_5 6 nodes_41_6 = true := by decide +kernel
def bk_41_6 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_6
set_option maxRecDepth 500000 in
lemma bk_41_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 6 xs.toFinset) bk_41_6 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_5_ok chk_41_6
def nodes_41_7 : List NodeSpec := nodesWithIdentity [([5,0,1,2,3,4],[5,4,3,6,7,2,8,9,10,11]),([0,1,6,2,3,4],[4,5,2,7,6,9,8,12]),([7,0,1,2,3,4],[5,3,6,7,13,8,9,4,10,0])]
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
def h53R : List Nat := varsOf 61
def h53G : Nat := 0xfffafaaafaaaaa00fffafaaafaaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bound : Lower h53R h53G 9 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := Cofactor12086.R_41) (T2 := Cofactor12086.G_41) (by decide +kernel) Cofactor12086.low_41
def h54R : List Nat := varsOf 62
def h54G : Nat := 0xfffcfcfcfffcfc00fffcfcfcfffcfc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h54Bound : Lower h54R h54G 6 := lift_of (z := 34) (o := 0) (essPairs := [(VAR 1,8,10),(VAR 5,2,34)]) (by decide +kernel) h3Bound
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xeee8e8a8eaa8a800eee8e8a8eaa8a800
def h0Pos : List Nat := [13,30,13,25,30,13,21,30,11,30,19,46,35,37,11,58,13,54,21,46,37,11,21,54,58,25,11,37,54,54,21,21,11,25,29,51,15,15,45,13,25,58,57,23,37,25,46,35,39,57,25,43,19,27,29,57,27,23,13,35,19,11,30,58,11,30,57,43,46,29,19,21,45,19,13,39,35,53,13,61,58,53,13,19,21,11,57,37,11,11,35,19,13,11,35,25,58,54,19,29,19,43,19,30,35,15]
def h0Neg : List Nat := [12,28,14,24,26,9,20,22,3,14,3,14,3,36,10,56,5,52,5,44,5,9,17,50,50,17,7,33,22,38,22,7,41,41,28,3,14,7,41,1,9,26,41,22,1,1,38,33,7,49,49,3,17,26,9,9,3,7,7,34,49,8,24,42,14,6,33,42,42,5,18,28,44,22,4,38,38,52,44,60,34,49,8,26,16,2,56,32,42,1,1,7,41,26,42,8,60,60,1,20,2,34,50,60,2,10]
def h0Mask : Nat := fullMask 106
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x37cfffeffed3fffbdffce75756d,0x41e02002417dfb5eb8e751520),(0xcccccccccccccccccccccccccccccccc,0x3f76f291a5bfb39ca3935aadf92,0x37069291a5b8f294a38f5805f94),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x28a1096edb2464158f4f8df2af7,0x8b0800ffa306014834f41f2ac7),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x2a9b365c53fe5ee67f70729cbbf,0x283f14cc199e0e007570028ca3f),(0xffff0000ffff0000ffff0000ffff0000,0xdf885ba2e6d3f62f0ef3c686da,0xcb205aa2c050360a0453c280da),(0xffffffff00000000ffffffff00000000,0x12344c3b91c888bd648399ab800,0xe351c3f91c9806c443298aa000)]
def h0Steps : List (Nat × Nat × Nat) := [(0,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(1,0,4),(3,0,4),(1,0,5),(2,0,5),(0,1,2),(2,1,2),(0,1,3),(2,1,3),(0,1,4),(2,1,4),(2,1,5),(0,2,3),(1,0,27),(2,1,27),(1,2,3),(2,2,3),(3,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(1,2,5),(2,2,5),(1,2,6),(2,2,6),(0,3,4),(1,3,4),(2,3,4),(0,3,5),(1,3,5),(2,3,5),(3,3,5),(1,4,5),(3,0,48),(0,1,48),(2,4,5),(1,6,27),(0,4,52),(1,4,52),(2,4,52),(3,4,52),(1,5,52),(3,5,52),(0,1,52),(2,1,52),(0,48,52),(1,5,61),(2,48,52),(3,6,48),(2,1,64),(3,27,48),(1,0,51),(2,1,51),(3,53,54),(1,0,31),(2,1,31),(1,6,31),(0,1,72),(2,1,72),(3,31,48),(1,0,38),(2,1,38),(1,0,41),(2,1,41),(3,0,42),(0,1,42),(1,5,41),(2,5,41),(1,6,38),(0,1,84),(2,1,84),(3,41,42),(1,6,41),(0,1,88),(2,1,88),(0,2,88),(2,2,88),(1,5,88),(3,5,88),(3,38,42),(3,6,42),(1,38,41),(0,1,96),(2,1,96),(1,0,43),(2,1,43),(1,6,43),(1,38,43),(0,39,42),(1,0,81),(3,0,45),(0,1,45),(1,0,107),(3,0,107),(0,39,45),(1,0,46),(2,1,46),(2,1,40),(0,1,93),(0,1,102),(2,1,102),(3,6,45),(2,1,117),(1,0,21),(1,7,21),(3,21,42),(3,21,45),(1,0,79),(1,0,116),(2,4,83),(1,8,41),(3,8,42),(1,8,43),(3,8,45),(0,1,13),(2,1,15),(0,1,18),(2,9,41),(0,18,133),(2,18,41),(0,9,42),(2,9,43),(0,9,45),(0,4,138),(2,4,138),(1,10,41),(3,10,42),(1,10,43),(3,10,45),(3,11,13),(1,11,15),(1,0,22),(1,11,22),(1,0,23),(1,11,23),(1,0,26),(1,11,26),(1,11,41),(3,11,42),(1,11,43),(3,11,45),(1,0,33),(1,5,12),(2,1,33),(1,12,33),(3,12,34),(2,1,35),(1,12,35),(1,12,36),(3,0,37),(3,12,37),(1,12,38),(3,12,48),(2,13,24),(2,13,25),(2,13,26),(2,13,33),(0,13,34),(2,13,35),(2,13,36),(0,13,37),(2,13,38),(0,13,48),(3,14,157),(1,14,33),(3,14,34),(1,14,35),(1,14,36),(3,14,37),(1,14,38),(3,14,48),(1,15,24),(1,15,25),(1,15,26),(1,15,33),(3,15,34),(1,15,35),(1,15,36),(3,15,37),(1,15,38),(3,15,48),(2,18,22),(2,18,23),(2,18,27),(0,18,30),(2,18,31),(2,18,32),(0,18,42),(2,18,43),(1,19,27),(3,19,30),(1,19,31),(1,19,32),(1,19,41),(3,19,42),(1,19,43),(0,4,147),(3,4,147),(0,48,147),(1,22,33),(1,22,35),(1,22,38),(3,22,48),(1,23,33),(1,23,35),(1,23,38),(3,23,48),(1,26,27),(1,26,31),(1,26,41),(3,26,42),(1,26,43),(0,4,28),(3,4,28),(0,28,48),(1,5,230),(2,30,65),(0,30,48),(3,32,48),(2,37,41),(0,37,42),(2,37,43),(0,1,111),(1,0,112)]
def h0W : BT Decor := buildWiresBT 8 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[],[(3,4)]]
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
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,6),some (subcubeFast 0 2,9),some (subcubeFast 0 4,8),some (subcubeFast 0 6,7),some (subcubeFast 0 8,8),some (subcubeFast 0 10,5),some (subcubeFast 0 16,8),some (subcubeFast 0 18,5),some (subcubeFast 0 32,8),some (subcubeFast 0 34,5),some (subcubeFast 0 40,5),some (subcubeFast 0 48,5),some (subcubeFast 1 0,8),some (subcubeFast 1 2,7),some (subcubeFast 1 4,5),some (subcubeFast 1 6,4),some (subcubeFast 1 8,5),some (subcubeFast 1 10,4),some (subcubeFast 1 16,5),some (subcubeFast 1 18,4),some (subcubeFast 1 32,5),some (subcubeFast 1 34,4),some (subcubeFast 2 0,6),some (subcubeFast 2 1,5),some (subcubeFast 4 0,8),some (subcubeFast 4 1,5),some (subcubeFast 4 2,6),some (subcubeFast 4 8,5),some (subcubeFast 4 16,5),some (subcubeFast 4 32,5),some (subcubeFast 4 40,4),some (subcubeFast 4 48,4),some (subcubeFast 8 0,8),some (subcubeFast 8 2,5),some (subcubeFast 8 4,5),some (subcubeFast 8 6,4),some (subcubeFast 8 16,5),some (subcubeFast 8 32,5),some (subcubeFast 16 0,8),some (subcubeFast 16 2,5),some (subcubeFast 16 4,5),some (subcubeFast 16 6,4),some (subcubeFast 16 8,5),some (subcubeFast 16 32,5),some (subcubeFast 16 40,4),some (subcubeFast 32 0,9),some (subcubeFast 32 1,5),some (subcubeFast 32 2,5),some (subcubeFast 32 4,5),some (subcubeFast 32 6,4),some (subcubeFast 32 8,6),some (subcubeFast 32 16,6),some (subcubeFast 34 0,5),some (subcubeFast 34 1,4),some (subcubeFast 36 0,5),some (subcubeFast 36 1,4)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 6 h0SliceList
def h0Specs : List PoolSpec := [(1,[]),(12,[]),(45,[(0,0,1)]),(1,[(0,2,3)]),(12,[(0,2,3)]),(45,[(0,0,1),(0,2,3)]),(23,[]),(24,[(0,0,1)]),(3,[]),(32,[(0,0,1)]),(2,[]),(24,[]),(4,[]),(32,[]),(2,[(0,0,1)]),(2,[(1,4,5),(0,1,48)]),(6,[(0,0,1)]),(38,[(0,0,1),(0,1,48)]),(8,[(0,0,1)]),(45,[(0,0,1),(0,1,48)]),(12,[(1,4,5),(0,1,48)]),(6,[(0,2,3)]),(2,[(1,4,5)]),(24,[(1,4,5)]),(38,[(0,2,3)]),(38,[(0,0,1)]),(8,[(0,2,3)]),(45,[(0,2,3)]),(12,[(1,4,5)]),(1,[(0,2,3),(1,6,27)]),(2,[(0,0,1),(1,6,27)]),(6,[]),(38,[]),(8,[]),(45,[]),(38,[(0,0,1),(3,6,48)]),(45,[(0,0,1),(3,6,48)]),(18,[]),(2,[(1,4,5),(3,27,48)]),(38,[(0,2,3),(3,27,48)]),(45,[(0,2,3),(3,27,48)]),(28,[]),(2,[(2,4,5)]),(24,[(2,4,5)]),(12,[(2,4,5)]),(51,[]),(51,[(0,2,3)]),(51,[(0,0,1)]),(45,[(0,0,1),(0,2,3),(1,6,27)]),(22,[]),(0,[]),(12,[(0,2,3),(0,4,52)]),(11,[]),(20,[]),(25,[]),(12,[(0,2,3),(1,4,52)]),(4,[(0,0,1),(1,6,27)]),(12,[(0,2,3),(2,4,52)]),(12,[(0,2,3),(3,4,52)]),(12,[(0,2,3),(1,5,52)]),(12,[(0,2,3),(3,5,52)]),(26,[]),(1,[(2,2,3)]),(12,[(2,2,3)]),(45,[(0,0,1),(2,2,3)]),(4,[(0,0,1)]),(6,[(2,2,3)]),(38,[(2,2,3)]),(8,[(2,2,3)]),(45,[(2,2,3)]),(1,[(2,2,3),(1,6,31)]),(16,[]),(34,[]),(35,[]),(51,[(2,2,3)]),(45,[(0,0,1),(2,2,3),(1,6,31)]),(32,[(0,0,1),(1,6,31)]),(2,[(0,0,1),(1,6,31)]),(1,[(2,2,5)]),(12,[(2,2,5)]),(2,[(0,3,4)]),(24,[(0,3,4)]),(2,[(0,3,4),(1,3,4)]),(24,[(0,3,4),(1,3,4)]),(12,[(0,3,4),(1,3,4)]),(32,[(2,2,5)]),(12,[(0,3,4)]),(2,[(0,0,1),(1,6,38)]),(48,[]),(49,[]),(52,[]),(2,[(1,3,4)]),(24,[(1,3,4)]),(4,[(2,2,5)]),(6,[(2,2,5)]),(38,[(2,2,5)]),(12,[(1,3,4)]),(1,[(2,2,5),(1,6,38)]),(2,[(2,3,4)]),(24,[(2,3,4)]),(12,[(2,3,4)]),(45,[(0,0,1),(1,6,38)]),(44,[]),(1,[(1,2,6)]),(45,[(0,0,1),(1,2,6)]),(1,[(1,2,6),(0,3,4)]),(45,[(0,0,1),(1,2,6),(0,3,4)]),(32,[(0,0,1),(1,2,6)]),(1,[(1,2,6),(0,3,4),(1,3,4)]),(4,[(0,0,1),(1,2,6)]),(38,[(0,0,1),(1,2,6)]),(8,[(0,0,1),(1,2,6)]),(1,[(1,2,6),(1,3,4)]),(45,[(0,0,1),(1,2,6),(1,3,4)]),(12,[(1,3,4),(0,1,42)]),(0,[(1,2,6)]),(32,[(0,0,1),(1,2,6),(0,1,42)]),(2,[(1,3,4),(0,1,42)]),(38,[(0,0,1),(1,2,6),(0,1,42)]),(6,[(0,0,1),(1,2,6)]),(1,[(1,2,6),(1,3,4),(0,39,42)]),(12,[(1,3,4),(0,39,42)]),(1,[(1,2,6),(2,3,4)]),(45,[(0,0,1),(1,2,6),(2,3,4)]),(1,[(1,2,6),(1,3,5)]),(12,[(1,3,5)]),(12,[(1,3,5),(0,1,45)]),(45,[(0,0,1),(1,2,6),(0,1,45)]),(32,[(0,0,1),(1,2,6),(0,1,45)]),(2,[(1,3,5),(0,1,45)]),(2,[(1,3,5)]),(1,[(1,2,6),(1,3,5),(0,39,45)]),(12,[(1,3,5),(0,39,45)]),(45,[(0,0,1),(1,2,6),(0,39,45)]),(1,[(1,2,6),(2,3,5)]),(12,[(2,3,5)]),(2,[(2,3,5)]),(1,[(2,2,6)]),(45,[(0,0,1),(2,2,6)]),(1,[(2,2,6),(0,3,4)]),(45,[(0,0,1),(2,2,6),(0,3,4)]),(32,[(0,0,1),(2,2,6)]),(1,[(2,2,6),(0,3,4),(1,3,4)]),(4,[(0,0,1),(2,2,6)]),(38,[(0,0,1),(2,2,6)]),(8,[(0,0,1),(2,2,6)]),(14,[]),(1,[(2,2,6),(1,3,4)]),(45,[(0,0,1),(2,2,6),(1,3,4)]),(6,[(0,0,1),(2,2,6)]),(1,[(2,2,6),(2,3,4)]),(45,[(0,0,1),(2,2,6),(2,3,4)]),(1,[(2,2,6),(1,3,5)]),(24,[(1,3,5)]),(1,[(2,2,6),(2,3,5)]),(24,[(2,3,5)]),(1,[(0,3,4)]),(45,[(0,0,1),(0,3,4)]),(3,[(0,3,4)]),(1,[(0,3,4),(1,3,4)]),(45,[(0,0,1),(0,3,4),(1,3,4)]),(3,[(0,3,4),(1,3,4)]),(45,[(0,3,4),(1,3,4)]),(8,[(0,3,4),(1,3,4)]),(1,[(1,3,4),(0,3,4),(1,6,41)]),(12,[(1,3,4),(0,3,4)]),(4,[(0,0,1),(1,6,41)]),(50,[(0,0,1),(1,6,41)]),(3,[(1,3,4),(0,3,4),(1,6,41)]),(1,[(0,3,4),(1,3,4),(1,6,41)]),(13,[(0,3,4),(1,3,4)]),(45,[(0,3,4)]),(8,[(0,3,4)]),(1,[(0,3,4),(1,6,41)]),(45,[(0,0,1),(0,3,4),(1,6,41)]),(3,[(0,3,4),(1,6,41)]),(13,[(0,3,4)]),(1,[(1,3,4)]),(45,[(0,0,1),(1,3,4)]),(45,[(0,0,1),(1,3,4),(0,1,42)]),(32,[(0,0,1),(0,1,42)]),(38,[(0,0,1),(0,1,42)]),(3,[(1,3,4)]),(45,[(1,3,4),(0,1,42)]),(45,[(1,3,4)]),(8,[(1,3,4)]),(1,[(1,3,4),(3,6,42)]),(45,[(0,0,1),(1,3,4),(3,6,42)]),(32,[(0,0,1),(3,6,42)]),(38,[(0,0,1),(3,6,42)]),(3,[(1,3,4),(3,6,42)]),(1,[(2,3,4)]),(45,[(0,0,1),(2,3,4)]),(3,[(2,3,4)]),(45,[(2,3,4)]),(8,[(2,3,4)]),(1,[(2,3,4),(1,6,43)]),(45,[(0,0,1),(2,3,4),(1,6,43)]),(38,[(0,0,1),(1,6,43)]),(3,[(2,3,4),(1,6,43)]),(4,[(0,0,1),(1,6,43)]),(1,[(1,3,5)]),(45,[(0,0,1),(0,1,45)]),(32,[(0,0,1),(0,1,45)]),(3,[(1,3,5)]),(38,[(1,3,5),(0,1,45)]),(6,[(1,3,5)]),(38,[(1,3,5)]),(1,[(1,3,5),(3,6,45)]),(45,[(0,0,1),(3,6,45)]),(32,[(0,0,1),(3,6,45)]),(3,[(1,3,5),(3,6,45)]),(1,[(2,3,5)]),(3,[(2,3,5)]),(6,[(2,3,5)]),(38,[(2,3,5)]),(50,[]),(13,[]),(45,[(3,0,1)]),(12,[(2,1,2)]),(2,[(3,0,1)]),(24,[(3,0,1)]),(45,[(3,0,1),(2,1,2)]),(12,[(2,1,2),(0,3,4)]),(2,[(3,0,1),(0,3,4)]),(0,[(2,1,2)]),(32,[(3,0,1),(2,1,2)]),(12,[(2,1,2),(0,3,4),(1,3,4)]),(2,[(3,0,1),(0,3,4),(1,3,4)]),(17,[]),(34,[(3,0,1)]),(4,[(3,0,1),(2,1,2)]),(38,[(3,0,1),(2,1,2)]),(8,[(3,0,1),(2,1,2)]),(12,[(2,1,2),(1,3,4)]),(2,[(3,0,1),(1,3,4)]),(13,[(1,3,4)]),(12,[(2,1,2),(2,3,4)]),(2,[(3,0,1),(2,3,4)]),(13,[(2,3,4)]),(12,[(2,1,2),(1,3,5)]),(2,[(3,0,1),(1,3,5)]),(13,[(1,3,5)]),(6,[(3,0,1),(2,1,2)]),(12,[(2,1,2),(2,3,5)]),(2,[(3,0,1),(2,3,5)]),(13,[(2,3,5)]),(32,[(3,0,1)]),(13,[(0,2,3)]),(45,[(3,0,1),(0,2,3)]),(12,[(0,2,3),(2,1,27)]),(45,[(3,0,1),(0,2,3),(2,1,27)]),(2,[(3,0,1),(2,1,27)]),(55,[]),(6,[(3,0,1)]),(38,[(3,0,1)]),(8,[(3,0,1)]),(12,[(0,2,3),(2,1,52)]),(24,[(0,0,1),(2,1,52)]),(32,[(0,0,1),(2,1,52)]),(3,[(1,6,27)]),(46,[]),(4,[(3,0,1)]),(13,[(2,2,3)]),(45,[(3,0,1),(2,2,3)]),(12,[(2,2,3),(2,1,31)]),(32,[(3,0,1),(2,1,31)]),(45,[(3,0,1),(2,2,3),(2,1,31)]),(2,[(3,0,1),(2,1,31)]),(38,[(2,2,3),(2,1,31)]),(45,[(2,2,3),(2,1,31)]),(12,[(2,2,3),(2,1,72)]),(24,[(0,0,1),(2,1,72)]),(4,[(0,0,1),(2,1,72)]),(3,[(1,6,31)]),(13,[(2,2,5)]),(12,[(2,2,5),(2,1,38)]),(45,[(3,0,1),(2,1,38)]),(2,[(3,0,1),(2,1,38)]),(32,[(2,2,5),(2,1,38)]),(38,[(2,2,5),(2,1,38)]),(3,[(1,6,38)]),(24,[(0,0,1),(2,1,84)]),(21,[]),(8,[(0,0,1),(2,1,84)]),(45,[(0,0,1),(1,6,38),(2,1,84)]),(42,[]),(12,[(2,2,5),(2,1,84)]),(45,[(3,0,1),(0,3,4)]),(12,[(0,3,4),(2,1,41)]),(45,[(3,0,1),(0,3,4),(2,1,41)]),(4,[(3,0,1),(2,1,41)]),(45,[(3,0,1),(0,3,4),(1,3,4)]),(12,[(1,3,4),(0,3,4),(2,1,88)]),(33,[]),(32,[(0,0,1),(2,1,88)]),(13,[(1,3,4),(0,3,4)]),(12,[(0,3,4),(2,1,88)]),(38,[(0,0,1),(2,1,88)]),(45,[(3,0,1),(1,3,4)]),(12,[(1,3,4),(0,1,96)]),(4,[(0,0,1),(0,1,96)]),(6,[(0,0,1),(0,1,96)]),(45,[(3,0,1),(2,3,4)]),(12,[(2,3,4),(2,1,102)]),(32,[(0,0,1),(2,1,102)]),(6,[(0,0,1),(2,1,102)]),(1,[(1,3,5),(3,0,107)]),(4,[(3,0,107)]),(32,[(0,1,45),(3,0,107)]),(45,[(0,1,45),(3,0,107)]),(3,[(1,3,5),(3,0,107)]),(1,[(0,0,2)]),(45,[(0,0,2)]),(1,[(1,7,21)]),(1,[(0,3,4),(1,7,21)]),(1,[(0,3,4),(1,3,4),(1,7,21)]),(32,[(3,0,1),(2,1,2),(1,7,21)]),(30,[]),(4,[(3,0,1),(2,1,2),(1,7,21)]),(12,[(0,3,4),(1,3,4),(3,41,42)]),(38,[(3,0,1),(2,1,2),(1,7,21)]),(45,[(3,0,1),(2,1,2),(1,7,21)]),(8,[(3,0,1),(2,1,2),(1,7,21)]),(1,[(1,3,4),(1,7,21)]),(6,[(3,0,1),(2,1,2),(1,7,21)]),(1,[(2,3,4),(1,7,21)]),(12,[(0,3,5)]),(1,[(0,3,5),(1,7,21)]),(24,[(0,3,5)]),(13,[(0,3,5)]),(1,[(1,3,5),(1,7,21)]),(31,[]),(1,[(2,3,5),(1,7,21)]),(12,[(3,3,5)]),(1,[(3,3,5),(1,7,21)]),(24,[(3,3,5)]),(13,[(3,3,5)]),(24,[(0,3,4),(2,5,41),(2,4,83)]),(1,[(0,0,2),(0,3,4)]),(45,[(0,0,2),(0,3,4)]),(32,[(0,0,2)]),(38,[(0,0,2)]),(24,[(0,3,4),(2,1,41)]),(4,[(2,1,41)]),(6,[(2,1,41)]),(4,[(0,0,2)]),(45,[(0,3,4),(2,1,41)]),(8,[(0,3,4),(2,1,41)]),(8,[(0,0,2)]),(1,[(0,0,2),(0,3,4),(1,3,4)]),(45,[(0,0,2),(0,3,4),(1,3,4)]),(24,[(1,3,4),(0,3,4)]),(4,[(0,0,2),(1,8,41)]),(50,[(0,0,2),(1,8,41)]),(1,[(0,0,2),(0,3,4),(1,8,41)]),(45,[(0,0,2),(0,3,4),(1,8,41)]),(1,[(0,0,2),(1,3,4)]),(45,[(0,0,2),(1,3,4)]),(6,[(0,0,2)]),(1,[(0,0,2),(1,3,4),(3,8,42)]),(45,[(0,0,2),(1,3,4),(3,8,42)]),(32,[(0,0,2),(3,8,42)]),(38,[(0,0,2),(3,8,42)]),(1,[(0,0,2),(2,3,4)]),(45,[(0,0,2),(2,3,4)]),(19,[]),(1,[(0,0,2),(2,3,4),(1,8,43)]),(45,[(0,0,2),(2,3,4),(1,8,43)]),(38,[(0,0,2),(1,8,43)]),(4,[(0,0,2),(1,8,43)]),(1,[(0,0,2),(1,3,5)]),(1,[(0,0,2),(1,3,5),(3,8,45)]),(45,[(0,0,2),(3,8,45)]),(32,[(0,0,2),(3,8,45)]),(1,[(0,0,2),(2,3,5)]),(1,[(1,0,2)]),(1,[(1,0,2),(1,0,3)]),(24,[(1,0,3)]),(32,[(1,0,2)]),(45,[(1,0,2),(1,0,3)]),(2,[(1,0,3)]),(4,[(1,0,2)]),(1,[(1,0,3)]),(38,[(1,0,3)]),(6,[(1,0,3)]),(38,[(1,0,2)]),(6,[(1,0,2)]),(45,[(1,0,3)]),(8,[(1,0,3)]),(45,[(1,0,2)]),(8,[(1,0,2)]),(1,[(1,0,2),(3,0,3)]),(24,[(3,0,3)]),(45,[(1,0,2),(3,0,3)]),(2,[(3,0,3)]),(1,[(3,0,3)]),(38,[(3,0,3)]),(6,[(3,0,3)]),(45,[(3,0,3)]),(8,[(3,0,3)]),(1,[(1,0,2),(1,0,5)]),(24,[(1,0,5)]),(2,[(1,0,5)]),(1,[(1,0,5)]),(32,[(1,0,5)]),(4,[(1,0,5)]),(38,[(1,0,5)]),(6,[(1,0,5)]),(4,[(1,0,2),(2,9,41)]),(6,[(1,0,2),(2,9,41)]),(4,[(1,0,5),(2,18,41)]),(6,[(1,0,5),(2,18,41)]),(37,[]),(1,[(1,0,2),(0,3,4)]),(45,[(1,0,2),(0,3,4)]),(1,[(1,0,2),(0,3,4),(1,3,4)]),(45,[(1,0,2),(0,3,4),(1,3,4)]),(12,[(0,3,4),(1,3,4),(0,9,42)]),(13,[(0,3,4),(1,3,4),(0,9,42)]),(24,[(0,3,4),(1,3,4),(0,9,42)]),(50,[(1,0,2)]),(32,[(1,0,2),(0,9,42)]),(12,[(0,3,4),(2,9,41)]),(1,[(1,0,2),(0,3,4),(2,9,41)]),(13,[(0,3,4),(2,9,41)]),(24,[(0,3,4),(2,9,41)]),(45,[(1,0,2),(0,3,4),(2,9,41)]),(1,[(1,0,2),(1,3,4)]),(45,[(1,0,2),(1,3,4)]),(12,[(1,3,4),(0,9,42)]),(1,[(1,0,2),(1,3,4),(0,9,42)]),(13,[(1,3,4),(0,9,42)]),(24,[(1,3,4),(0,9,42)]),(38,[(1,0,2),(0,9,42)]),(45,[(1,0,2),(1,3,4),(0,9,42)]),(1,[(1,3,4),(1,0,2),(0,9,42)]),(1,[(1,0,2),(2,3,4)]),(45,[(1,0,2),(2,3,4)]),(12,[(2,3,4),(2,9,43)]),(1,[(1,0,2),(2,3,4),(2,9,43)]),(13,[(2,3,4),(2,9,43)]),(24,[(2,3,4),(2,9,43)]),(38,[(1,0,2),(2,9,43)]),(45,[(1,0,2),(2,3,4),(2,9,43)]),(4,[(1,0,2),(2,9,43)]),(1,[(1,0,2),(1,3,5)]),(12,[(1,3,5),(0,9,45)]),(1,[(1,0,2),(1,3,5),(0,9,45)]),(13,[(1,3,5),(0,9,45)]),(45,[(1,0,2),(0,9,45)]),(24,[(1,3,5),(0,9,45)]),(32,[(1,0,2),(0,9,45)]),(1,[(1,3,5),(1,0,2),(0,9,45)]),(1,[(1,0,2),(2,3,5)]),(1,[(2,0,2)]),(45,[(2,0,2)]),(1,[(2,0,2),(0,3,4)]),(45,[(2,0,2),(0,3,4)]),(32,[(2,0,2)]),(38,[(2,0,2)]),(1,[(2,0,2),(0,3,4),(1,3,4)]),(45,[(2,0,2),(0,3,4),(1,3,4)]),(4,[(2,0,2)]),(8,[(2,0,2)]),(1,[(2,0,2),(0,3,4),(1,10,41)]),(45,[(2,0,2),(0,3,4),(1,10,41)]),(24,[(0,3,4),(1,10,41)]),(4,[(2,0,2),(1,10,41)]),(1,[(2,0,2),(1,3,4)]),(45,[(2,0,2),(1,3,4)]),(6,[(2,0,2)]),(1,[(2,0,2),(1,3,4),(3,10,42)]),(45,[(2,0,2),(1,3,4),(3,10,42)]),(24,[(1,3,4),(3,10,42)]),(32,[(2,0,2),(3,10,42)]),(38,[(2,0,2),(3,10,42)]),(1,[(2,0,2),(2,3,4)]),(45,[(2,0,2),(2,3,4)]),(1,[(2,0,2),(2,3,4),(1,10,43)]),(45,[(2,0,2),(2,3,4),(1,10,43)]),(24,[(2,3,4),(1,10,43)]),(38,[(2,0,2),(1,10,43)]),(4,[(2,0,2),(1,10,43)]),(1,[(2,0,2),(1,3,5)]),(1,[(2,0,2),(1,3,5),(3,10,45)]),(45,[(2,0,2),(3,10,45)]),(24,[(1,3,5),(3,10,45)]),(32,[(2,0,2),(3,10,45)]),(1,[(2,0,2),(2,3,5)]),(1,[(3,0,2)]),(1,[(3,0,2),(1,0,3)]),(32,[(3,0,2)]),(45,[(3,0,2),(1,0,3)]),(4,[(3,0,2)]),(38,[(3,0,2)]),(6,[(3,0,2)]),(45,[(3,0,2)]),(8,[(3,0,2)]),(1,[(3,0,2),(3,0,3)]),(45,[(3,0,2),(3,0,3)]),(1,[(3,0,2),(1,0,5)]),(12,[(0,1,3)]),(24,[(0,1,3)]),(45,[(3,0,2),(0,1,3)]),(2,[(0,1,3)]),(53,[]),(6,[(0,1,3)]),(38,[(0,1,3)]),(45,[(0,1,3)]),(8,[(0,1,3)]),(1,[(3,0,2),(1,11,22)]),(12,[(0,1,3),(1,11,22)]),(13,[(1,11,22)]),(45,[(3,0,2),(0,1,3),(1,11,22)]),(2,[(0,1,3),(1,11,22)]),(12,[(2,1,3)]),(24,[(2,1,3)]),(45,[(3,0,2),(2,1,3)]),(2,[(2,1,3)]),(6,[(2,1,3)]),(38,[(2,1,3)]),(45,[(2,1,3)]),(8,[(2,1,3)]),(1,[(3,0,2),(1,11,23)]),(12,[(2,1,3),(1,11,23)]),(32,[(3,0,2),(1,11,23)]),(13,[(1,11,23)]),(45,[(3,0,2),(2,1,3),(1,11,23)]),(2,[(2,1,3),(1,11,23)]),(12,[(2,1,5)]),(24,[(2,1,5)]),(2,[(2,1,5)]),(4,[(2,1,5)]),(32,[(2,1,5)]),(6,[(2,1,5)]),(38,[(2,1,5)]),(1,[(3,0,2),(1,11,26)]),(12,[(2,1,5),(1,11,26)]),(13,[(1,11,26)]),(45,[(3,0,2),(1,11,26)]),(2,[(2,1,5),(1,11,26)]),(12,[(2,1,40)]),(1,[(0,3,4),(2,2,6)]),(12,[(0,3,4),(2,1,40)]),(1,[(0,3,4),(1,3,4),(2,2,6)]),(12,[(0,3,4),(1,3,4),(2,1,40)]),(27,[]),(26,[(0,3,4),(1,3,4)]),(45,[(0,0,1),(2,2,6),(2,1,40)]),(29,[]),(26,[(0,3,4)]),(1,[(1,3,4),(2,2,6)]),(12,[(1,3,4),(2,1,40)]),(26,[(1,3,4)]),(1,[(2,3,4),(2,2,6)]),(12,[(2,3,4),(2,1,40)]),(26,[(2,3,4)]),(1,[(1,3,5),(2,2,6)]),(12,[(1,3,5),(2,1,40)]),(41,[]),(26,[(1,3,5)]),(1,[(2,3,5),(2,2,6)]),(12,[(2,3,5),(2,1,40)]),(26,[(2,3,5)]),(1,[(3,0,2),(0,3,4)]),(45,[(3,0,2),(0,3,4)]),(1,[(3,0,2),(0,3,4),(1,3,4)]),(45,[(3,0,2),(0,3,4),(1,3,4)]),(12,[(0,3,4),(1,11,41)]),(1,[(3,0,2),(0,3,4),(1,11,41)]),(13,[(0,3,4),(1,11,41)]),(45,[(3,0,2),(0,3,4),(1,11,41)]),(2,[(0,3,4),(1,11,41)]),(15,[]),(4,[(3,0,2),(1,11,41)]),(1,[(3,0,2),(1,3,4)]),(45,[(3,0,2),(1,3,4)]),(12,[(1,3,4),(3,11,42)]),(1,[(3,0,2),(1,3,4),(3,11,42)]),(13,[(1,3,4),(3,11,42)]),(32,[(3,0,2),(3,11,42)]),(38,[(3,0,2),(3,11,42)]),(45,[(3,0,2),(1,3,4),(3,11,42)]),(2,[(1,3,4),(3,11,42)]),(1,[(3,0,2),(2,3,4)]),(45,[(3,0,2),(2,3,4)]),(12,[(2,3,4),(1,11,43)]),(1,[(3,0,2),(2,3,4),(1,11,43)]),(13,[(2,3,4),(1,11,43)]),(38,[(3,0,2),(1,11,43)]),(45,[(3,0,2),(2,3,4),(1,11,43)]),(2,[(2,3,4),(1,11,43)]),(4,[(3,0,2),(1,11,43)]),(1,[(3,0,2),(1,3,5)]),(12,[(1,3,5),(3,11,45)]),(1,[(3,0,2),(1,3,5),(3,11,45)]),(13,[(1,3,5),(3,11,45)]),(45,[(3,0,2),(3,11,45)]),(32,[(3,0,2),(3,11,45)]),(2,[(1,3,5),(3,11,45)]),(1,[(3,0,2),(2,3,5)]),(1,[(0,0,3)]),(45,[(0,0,3)]),(12,[(0,2,4)]),(1,[(0,0,3),(0,2,4)]),(32,[(0,2,4)]),(45,[(0,0,3),(0,2,4)]),(24,[(0,0,3)]),(1,[(0,2,4),(1,0,33)]),(2,[(0,0,3)]),(45,[(0,2,4),(1,0,33)]),(8,[(0,0,3)]),(13,[(0,2,4)]),(38,[(0,0,3)]),(1,[(0,2,4)]),(12,[(0,2,4),(2,1,33)]),(32,[(0,2,4),(2,1,33)]),(2,[(2,1,33)]),(6,[(2,1,33)]),(45,[(0,2,4),(2,1,33)]),(8,[(0,2,4),(2,1,33)]),(26,[(0,0,3)]),(45,[(0,2,4)]),(1,[(0,2,4),(0,0,3),(1,5,12)]),(24,[(0,0,3),(1,5,12)]),(23,[(1,5,12)]),(1,[(0,0,3),(1,5,12)]),(0,[(1,5,12)]),(4,[(1,5,12)]),(2,[(0,0,3),(1,5,12)]),(45,[(0,2,4),(0,0,3)]),(38,[(0,0,3),(1,5,12)]),(1,[(0,0,3),(1,5,12),(0,2,4)]),(26,[(0,0,3),(1,5,12)]),(8,[(0,2,4)]),(1,[(0,0,3),(0,2,4),(1,12,33)]),(45,[(0,0,3),(0,2,4),(1,12,33)]),(2,[(0,0,3),(1,12,33)]),(12,[(1,2,4)]),(1,[(0,0,3),(1,2,4)]),(32,[(1,2,4)]),(45,[(0,0,3),(1,2,4)]),(13,[(1,2,4)]),(6,[(0,0,3)]),(1,[(1,2,4)]),(3,[(0,0,3)]),(45,[(1,2,4)]),(1,[(1,2,4),(0,0,3),(1,5,12)]),(45,[(1,2,4),(0,0,3)]),(6,[(0,0,3),(1,5,12)]),(3,[(0,0,3),(1,5,12)]),(8,[(1,2,4)]),(1,[(0,0,3),(1,2,4),(3,12,34)]),(45,[(0,0,3),(1,2,4),(3,12,34)]),(24,[(0,0,3),(3,12,34)]),(38,[(0,0,3),(3,12,34)]),(12,[(2,2,4)]),(1,[(0,0,3),(2,2,4)]),(32,[(2,2,4)]),(45,[(0,0,3),(2,2,4)]),(13,[(2,2,4)]),(1,[(2,2,4)]),(45,[(2,2,4)]),(1,[(2,2,4),(0,0,3),(1,5,12)]),(45,[(2,2,4),(0,0,3)]),(8,[(2,2,4)]),(1,[(0,0,3),(2,2,4),(1,12,35)]),(45,[(0,0,3),(2,2,4),(1,12,35)]),(38,[(0,0,3),(1,12,35)]),(2,[(0,0,3),(1,12,35)]),(12,[(3,2,4)]),(1,[(0,0,3),(3,2,4)]),(32,[(3,2,4)]),(45,[(0,0,3),(3,2,4)]),(13,[(3,2,4)]),(1,[(3,2,4)]),(45,[(3,2,4)]),(1,[(3,2,4),(0,0,3),(1,5,12)]),(45,[(3,2,4),(0,0,3)]),(8,[(3,2,4)]),(43,[]),(1,[(0,0,3),(3,2,4),(1,12,36)]),(45,[(0,0,3),(3,2,4),(1,12,36)]),(24,[(0,0,3),(1,12,36)]),(12,[(1,2,5)]),(1,[(0,0,3),(1,2,5)]),(32,[(1,2,5)]),(13,[(1,2,5)]),(1,[(1,2,5)]),(6,[(1,2,5)]),(38,[(1,2,5)]),(1,[(0,0,3),(1,2,5),(3,12,37)]),(45,[(0,0,3),(3,12,37)]),(24,[(0,0,3),(3,12,37)]),(1,[(0,0,3),(2,2,5)]),(1,[(0,0,3),(2,2,5),(1,12,38)]),(45,[(0,0,3),(1,12,38)]),(2,[(0,0,3),(1,12,38)]),(1,[(0,0,3),(1,4,5)]),(32,[(1,4,5)]),(13,[(1,4,5)]),(1,[(0,0,3),(1,4,5),(3,0,48)]),(32,[(1,4,5),(3,0,48)]),(38,[(0,0,3),(3,0,48)]),(45,[(0,0,3),(3,0,48)]),(1,[(1,4,5)]),(1,[(0,0,3),(1,4,5),(3,12,48)]),(45,[(0,0,3),(3,12,48)]),(38,[(0,0,3),(3,12,48)]),(1,[(0,0,3),(2,4,5)]),(32,[(2,4,5)]),(13,[(2,4,5)]),(1,[(2,4,5)]),(1,[(1,0,3),(1,0,4)]),(32,[(1,0,4)]),(45,[(1,0,3),(1,0,4)]),(4,[(1,0,4)]),(1,[(1,0,4)]),(24,[(1,0,4)]),(2,[(1,0,4)]),(45,[(1,0,4)]),(8,[(1,0,4)]),(1,[(1,0,3),(3,0,4)]),(32,[(3,0,4)]),(45,[(1,0,3),(3,0,4)]),(4,[(3,0,4)]),(1,[(3,0,4)]),(24,[(3,0,4)]),(2,[(3,0,4)]),(45,[(3,0,4)]),(8,[(3,0,4)]),(1,[(1,0,3),(1,0,5)]),(12,[(0,1,2)]),(32,[(0,1,2)]),(45,[(1,0,3),(0,1,2)]),(12,[(0,1,2),(0,1,13)]),(24,[(1,0,3),(0,1,13)]),(32,[(0,1,2),(0,1,13)]),(45,[(0,1,2),(1,0,3),(0,1,13)]),(3,[(1,0,3)]),(4,[(0,1,2)]),(38,[(1,0,3),(0,1,13)]),(45,[(1,0,3),(0,1,13)]),(38,[(0,1,2)]),(6,[(0,1,2)]),(45,[(0,1,2)]),(8,[(0,1,2)]),(32,[(2,1,2)]),(45,[(1,0,3),(2,1,2)]),(4,[(2,1,2)]),(38,[(2,1,2)]),(6,[(2,1,2)]),(45,[(2,1,2)]),(8,[(2,1,2)]),(12,[(0,1,4)]),(32,[(0,1,4)]),(45,[(1,0,3),(0,1,4)]),(12,[(0,1,4),(0,1,13)]),(32,[(0,1,4),(0,1,13)]),(45,[(0,1,4),(1,0,3),(0,1,13)]),(4,[(0,1,4)]),(24,[(0,1,4)]),(2,[(0,1,4)]),(45,[(0,1,4)]),(8,[(0,1,4)]),(1,[(1,0,3),(2,13,24)]),(12,[(0,1,4),(2,13,24)]),(13,[(2,13,24)]),(32,[(0,1,4),(2,13,24)]),(45,[(1,0,3),(0,1,4),(2,13,24)]),(3,[(1,0,3),(2,13,24)]),(12,[(2,1,4)]),(32,[(2,1,4)]),(45,[(1,0,3),(2,1,4)]),(4,[(2,1,4)]),(24,[(2,1,4)]),(2,[(2,1,4)]),(45,[(2,1,4)]),(8,[(2,1,4)]),(1,[(1,0,3),(2,13,25)]),(12,[(2,1,4),(2,13,25)]),(13,[(2,13,25)]),(32,[(2,1,4),(2,13,25)]),(38,[(1,0,3),(2,13,25)]),(45,[(1,0,3),(2,1,4),(2,13,25)]),(3,[(1,0,3),(2,13,25)]),(1,[(1,0,3),(2,13,26)]),(12,[(2,1,5),(2,13,26)]),(13,[(2,13,26)]),(32,[(2,1,5),(2,13,26)]),(45,[(1,0,3),(2,13,26)]),(3,[(1,0,3),(2,13,26)]),(12,[(0,1,13)]),(32,[(0,1,13)]),(1,[(0,2,4),(1,0,3)]),(12,[(0,2,4),(0,1,13)]),(4,[(0,2,4)]),(45,[(0,2,4),(1,0,3),(0,1,13)]),(2,[(1,0,3),(0,1,13)]),(8,[(1,0,3),(0,1,13)]),(5,[]),(1,[(2,2,4),(1,0,3)]),(12,[(2,2,4),(0,1,13)]),(4,[(2,2,4)]),(45,[(2,2,4),(1,0,3),(0,1,13)]),(1,[(2,2,5),(1,0,3)]),(12,[(2,2,5),(0,1,13)]),(6,[(1,0,3),(0,1,13)]),(1,[(1,4,5),(1,0,3)]),(12,[(1,4,5),(0,1,13)]),(4,[(1,4,5)]),(10,[]),(1,[(2,4,5),(1,0,3)]),(12,[(2,4,5),(0,1,13)]),(4,[(2,4,5)]),(1,[(1,0,3),(0,2,4)]),(45,[(1,0,3),(0,2,4)]),(12,[(0,2,4),(2,13,33)]),(1,[(1,0,3),(0,2,4),(2,13,33)]),(13,[(0,2,4),(2,13,33)]),(32,[(0,2,4),(2,13,33)]),(45,[(1,0,3),(0,2,4),(2,13,33)]),(2,[(1,0,3),(2,13,33)]),(1,[(1,0,3),(1,2,4)]),(45,[(1,0,3),(1,2,4)]),(4,[(1,2,4)]),(1,[(1,2,4),(1,0,3)]),(12,[(1,2,4),(0,1,13)]),(45,[(1,2,4),(1,0,3),(0,1,13)]),(12,[(1,2,4),(0,13,34)]),(1,[(1,0,3),(1,2,4),(0,13,34)]),(13,[(1,2,4),(0,13,34)]),(24,[(1,0,3),(0,13,34)]),(32,[(1,2,4),(0,13,34)]),(38,[(1,0,3),(0,13,34)]),(45,[(1,0,3),(1,2,4),(0,13,34)]),(1,[(1,0,3),(2,2,4)]),(45,[(1,0,3),(2,2,4)]),(12,[(2,2,4),(2,13,35)]),(1,[(1,0,3),(2,2,4),(2,13,35)]),(13,[(2,2,4),(2,13,35)]),(32,[(2,2,4),(2,13,35)]),(38,[(1,0,3),(2,13,35)]),(45,[(1,0,3),(2,2,4),(2,13,35)]),(2,[(1,0,3),(2,13,35)]),(1,[(1,0,3),(3,2,4)]),(45,[(1,0,3),(3,2,4)]),(4,[(3,2,4)]),(1,[(3,2,4),(1,0,3)]),(12,[(3,2,4),(0,1,13)]),(45,[(3,2,4),(1,0,3),(0,1,13)]),(12,[(3,2,4),(2,13,36)]),(1,[(1,0,3),(3,2,4),(2,13,36)]),(13,[(3,2,4),(2,13,36)]),(24,[(1,0,3),(2,13,36)]),(32,[(3,2,4),(2,13,36)]),(45,[(1,0,3),(3,2,4),(2,13,36)]),(1,[(1,0,3),(1,2,5)]),(4,[(1,2,5)]),(1,[(1,2,5),(1,0,3)]),(12,[(1,2,5),(0,1,13)]),(54,[]),(12,[(1,2,5),(0,13,37)]),(1,[(1,0,3),(1,2,5),(0,13,37)]),(13,[(1,2,5),(0,13,37)]),(24,[(1,0,3),(0,13,37)]),(45,[(1,0,3),(0,13,37)]),(32,[(1,2,5),(0,13,37)]),(1,[(1,0,3),(2,2,5)]),(12,[(2,2,5),(2,13,38)]),(1,[(1,0,3),(2,2,5),(2,13,38)]),(13,[(2,2,5),(2,13,38)]),(45,[(1,0,3),(2,13,38)]),(32,[(2,2,5),(2,13,38)]),(1,[(1,0,3),(1,4,5)]),(12,[(1,4,5),(0,13,48)]),(1,[(1,0,3),(1,4,5),(0,13,48)]),(13,[(1,4,5),(0,13,48)]),(32,[(1,4,5),(0,13,48)]),(45,[(1,0,3),(0,13,48)]),(38,[(1,0,3),(0,13,48)]),(1,[(1,0,3),(2,4,5)]),(1,[(2,0,3)]),(45,[(2,0,3)]),(1,[(2,0,3),(0,2,4)]),(45,[(2,0,3),(0,2,4)]),(1,[(2,0,3),(0,2,4),(1,0,33)]),(24,[(2,0,3)]),(2,[(2,0,3)]),(8,[(2,0,3)]),(38,[(2,0,3)]),(4,[(0,2,4),(2,1,33)]),(26,[(2,0,3)]),(1,[(2,0,3),(0,2,4),(1,14,33)]),(45,[(2,0,3),(0,2,4),(1,14,33)]),(32,[(0,2,4),(1,14,33)]),(2,[(2,0,3),(1,14,33)]),(1,[(2,0,3),(1,2,4)]),(45,[(2,0,3),(1,2,4)]),(6,[(2,0,3)]),(3,[(2,0,3)]),(1,[(2,0,3),(1,2,4),(3,14,34)]),(45,[(2,0,3),(1,2,4),(3,14,34)]),(24,[(2,0,3),(3,14,34)]),(32,[(1,2,4),(3,14,34)]),(38,[(2,0,3),(3,14,34)]),(1,[(2,0,3),(2,2,4)]),(45,[(2,0,3),(2,2,4)]),(1,[(2,0,3),(2,2,4),(1,14,35)]),(45,[(2,0,3),(2,2,4),(1,14,35)]),(32,[(2,2,4),(1,14,35)]),(38,[(2,0,3),(1,14,35)]),(2,[(2,0,3),(1,14,35)]),(1,[(2,0,3),(3,2,4)]),(45,[(2,0,3),(3,2,4)]),(1,[(2,0,3),(3,2,4),(1,14,36)]),(45,[(2,0,3),(3,2,4),(1,14,36)]),(24,[(2,0,3),(1,14,36)]),(32,[(3,2,4),(1,14,36)]),(1,[(2,0,3),(1,2,5)]),(1,[(2,0,3),(1,2,5),(3,14,37)]),(45,[(2,0,3),(3,14,37)]),(24,[(2,0,3),(3,14,37)]),(32,[(1,2,5),(3,14,37)]),(1,[(2,0,3),(2,2,5)]),(1,[(2,0,3),(2,2,5),(1,14,38)]),(45,[(2,0,3),(1,14,38)]),(32,[(2,2,5),(1,14,38)]),(1,[(2,0,3),(1,4,5)]),(1,[(2,0,3),(1,4,5),(3,14,48)]),(45,[(2,0,3),(3,14,48)]),(32,[(1,4,5),(3,14,48)]),(38,[(2,0,3),(3,14,48)]),(1,[(2,0,3),(2,4,5)]),(1,[(3,0,3),(3,0,4)]),(45,[(3,0,3),(3,0,4)]),(1,[(3,0,3),(1,0,5)]),(45,[(3,0,3),(0,1,2)]),(3,[(3,0,3)]),(45,[(3,0,3),(2,1,2)]),(45,[(3,0,3),(0,1,4)]),(1,[(3,0,3),(1,15,24)]),(12,[(0,1,4),(1,15,24)]),(13,[(1,15,24)]),(45,[(3,0,3),(0,1,4),(1,15,24)]),(4,[(0,1,4),(1,15,24)]),(3,[(3,0,3),(1,15,24)]),(45,[(3,0,3),(2,1,4)]),(1,[(3,0,3),(1,15,25)]),(12,[(2,1,4),(1,15,25)]),(13,[(1,15,25)]),(38,[(3,0,3),(1,15,25)]),(45,[(3,0,3),(2,1,4),(1,15,25)]),(4,[(2,1,4),(1,15,25)]),(3,[(3,0,3),(1,15,25)]),(1,[(3,0,3),(1,15,26)]),(12,[(2,1,5),(1,15,26)]),(13,[(1,15,26)]),(45,[(3,0,3),(1,15,26)]),(4,[(2,1,5),(1,15,26)]),(3,[(3,0,3),(1,15,26)]),(12,[(2,1,15)]),(45,[(3,0,3),(2,1,15)]),(4,[(2,1,15)]),(1,[(0,2,4),(3,0,3)]),(12,[(0,2,4),(2,1,15)]),(24,[(3,0,3),(2,1,15)]),(38,[(3,0,3),(2,1,15)]),(2,[(3,0,3),(2,1,15)]),(8,[(3,0,3),(2,1,15)]),(1,[(2,2,4),(3,0,3)]),(12,[(2,2,4),(2,1,15)]),(1,[(2,2,5),(3,0,3)]),(12,[(2,2,5),(2,1,15)]),(6,[(3,0,3),(2,1,15)]),(1,[(1,4,5),(3,0,3)]),(12,[(1,4,5),(2,1,15)]),(36,[]),(1,[(2,4,5),(3,0,3)]),(12,[(2,4,5),(2,1,15)]),(1,[(3,0,3),(0,2,4)]),(45,[(3,0,3),(0,2,4)]),(12,[(0,2,4),(1,15,33)]),(1,[(3,0,3),(0,2,4),(1,15,33)]),(13,[(0,2,4),(1,15,33)]),(45,[(3,0,3),(0,2,4),(1,15,33)]),(4,[(0,2,4),(1,15,33)]),(2,[(3,0,3),(1,15,33)]),(1,[(3,0,3),(1,2,4)]),(45,[(3,0,3),(1,2,4)]),(12,[(1,2,4),(3,15,34)]),(1,[(3,0,3),(1,2,4),(3,15,34)]),(13,[(1,2,4),(3,15,34)]),(24,[(3,0,3),(3,15,34)]),(38,[(3,0,3),(3,15,34)]),(45,[(3,0,3),(1,2,4),(3,15,34)]),(4,[(1,2,4),(3,15,34)]),(1,[(3,0,3),(2,2,4)]),(45,[(3,0,3),(2,2,4)]),(12,[(2,2,4),(1,15,35)]),(1,[(3,0,3),(2,2,4),(1,15,35)]),(13,[(2,2,4),(1,15,35)]),(38,[(3,0,3),(1,15,35)]),(45,[(3,0,3),(2,2,4),(1,15,35)]),(4,[(2,2,4),(1,15,35)]),(2,[(3,0,3),(1,15,35)]),(1,[(3,0,3),(3,2,4)]),(45,[(3,0,3),(3,2,4)]),(12,[(3,2,4),(1,15,36)]),(1,[(3,0,3),(3,2,4),(1,15,36)]),(13,[(3,2,4),(1,15,36)]),(24,[(3,0,3),(1,15,36)]),(45,[(3,0,3),(3,2,4),(1,15,36)]),(4,[(3,2,4),(1,15,36)]),(1,[(3,0,3),(1,2,5)]),(12,[(1,2,5),(3,15,37)]),(1,[(3,0,3),(1,2,5),(3,15,37)]),(13,[(1,2,5),(3,15,37)]),(24,[(3,0,3),(3,15,37)]),(45,[(3,0,3),(3,15,37)]),(4,[(1,2,5),(3,15,37)]),(1,[(3,0,3),(2,2,5)]),(12,[(2,2,5),(1,15,38)]),(1,[(3,0,3),(2,2,5),(1,15,38)]),(13,[(2,2,5),(1,15,38)]),(45,[(3,0,3),(1,15,38)]),(4,[(2,2,5),(1,15,38)]),(1,[(3,0,3),(1,4,5)]),(1,[(3,0,3),(1,4,5),(3,0,48)]),(38,[(3,0,3),(3,0,48)]),(45,[(3,0,3),(3,0,48)]),(12,[(1,4,5),(3,15,48)]),(1,[(3,0,3),(1,4,5),(3,15,48)]),(13,[(1,4,5),(3,15,48)]),(45,[(3,0,3),(3,15,48)]),(38,[(3,0,3),(3,15,48)]),(4,[(1,4,5),(3,15,48)]),(1,[(3,0,3),(2,4,5)]),(12,[(0,1,2),(0,1,18)]),(24,[(1,0,5),(0,1,18)]),(45,[(0,1,2),(0,1,18)]),(3,[(1,0,5)]),(32,[(1,0,5),(0,1,18)]),(38,[(1,0,5),(0,1,18)]),(26,[(1,0,5)]),(12,[(0,1,3),(0,1,18)]),(45,[(0,1,3),(0,1,18)]),(1,[(1,0,5),(2,18,22)]),(12,[(0,1,3),(2,18,22)]),(13,[(2,18,22)]),(45,[(0,1,3),(2,18,22)]),(3,[(1,0,5),(2,18,22)]),(1,[(1,0,5),(2,18,23)]),(12,[(2,1,3),(2,18,23)]),(13,[(2,18,23)]),(32,[(1,0,5),(2,18,23)]),(45,[(2,1,3),(2,18,23)]),(3,[(1,0,5),(2,18,23)]),(12,[(0,1,18)]),(45,[(0,1,18)]),(1,[(0,2,3),(1,0,5)]),(45,[(0,2,3),(0,1,18)]),(12,[(0,2,3),(0,1,18)]),(2,[(1,0,5),(0,1,18)]),(6,[(1,0,5),(0,1,18)]),(9,[]),(1,[(2,2,3),(1,0,5)]),(45,[(2,2,3),(0,1,18)]),(12,[(2,2,3),(0,1,18)]),(4,[(1,0,5),(0,1,18)]),(1,[(0,3,4),(1,0,5)]),(45,[(0,3,4),(0,1,18)]),(12,[(0,3,4),(0,1,18)]),(1,[(0,3,4),(1,3,4),(1,0,5)]),(45,[(0,3,4),(1,3,4),(0,1,18)]),(12,[(0,3,4),(1,3,4),(0,1,18)]),(1,[(1,3,4),(1,0,5)]),(45,[(1,3,4),(0,1,18)]),(12,[(1,3,4),(0,1,18)]),(1,[(2,3,4),(1,0,5)]),(45,[(2,3,4),(0,1,18)]),(12,[(2,3,4),(0,1,18)]),(1,[(1,0,5),(0,2,3)]),(12,[(0,2,3),(2,18,27)]),(1,[(1,0,5),(0,2,3),(2,18,27)]),(13,[(0,2,3),(2,18,27)]),(45,[(0,2,3),(2,18,27)]),(2,[(1,0,5),(2,18,27)]),(12,[(1,2,3)]),(1,[(1,0,5),(1,2,3)]),(13,[(1,2,3)]),(45,[(1,2,3)]),(1,[(1,2,3),(1,0,5)]),(45,[(1,2,3),(0,1,18)]),(12,[(1,2,3),(0,1,18)]),(1,[(1,2,3)]),(8,[(1,2,3)]),(38,[(1,2,3)]),(6,[(1,2,3)]),(12,[(1,2,3),(0,18,30)]),(1,[(1,0,5),(1,2,3),(0,18,30)]),(13,[(1,2,3),(0,18,30)]),(24,[(1,0,5),(0,18,30)]),(32,[(1,0,5),(0,18,30)]),(45,[(1,2,3),(0,18,30)]),(1,[(1,0,5),(2,2,3)]),(12,[(2,2,3),(2,18,31)]),(1,[(1,0,5),(2,2,3),(2,18,31)]),(13,[(2,2,3),(2,18,31)]),(32,[(1,0,5),(2,18,31)]),(45,[(2,2,3),(2,18,31)]),(2,[(1,0,5),(2,18,31)]),(12,[(3,2,3)]),(1,[(1,0,5),(3,2,3)]),(13,[(3,2,3)]),(45,[(3,2,3)]),(1,[(3,2,3),(1,0,5)]),(45,[(3,2,3),(0,1,18)]),(12,[(3,2,3),(0,1,18)]),(1,[(3,2,3)]),(8,[(3,2,3)]),(38,[(3,2,3)]),(6,[(3,2,3)]),(12,[(3,2,3),(2,18,32)]),(1,[(1,0,5),(3,2,3),(2,18,32)]),(13,[(3,2,3),(2,18,32)]),(24,[(1,0,5),(2,18,32)]),(45,[(3,2,3),(2,18,32)]),(1,[(1,0,5),(0,3,4)]),(1,[(1,0,5),(0,3,4),(1,3,4)]),(12,[(0,3,4),(1,3,4),(0,18,42)]),(13,[(0,3,4),(1,3,4),(0,18,42)]),(45,[(0,3,4),(1,3,4),(0,18,42)]),(32,[(1,0,5),(0,18,42)]),(12,[(0,3,4),(2,18,41)]),(1,[(1,0,5),(0,3,4),(2,18,41)]),(13,[(0,3,4),(2,18,41)]),(45,[(0,3,4),(2,18,41)]),(1,[(1,0,5),(1,3,4)]),(12,[(1,3,4),(0,18,42)]),(1,[(1,0,5),(1,3,4),(0,18,42)]),(13,[(1,3,4),(0,18,42)]),(38,[(1,0,5),(0,18,42)]),(45,[(1,3,4),(0,18,42)]),(1,[(1,0,5),(2,3,4)]),(12,[(2,3,4),(2,18,43)]),(1,[(1,0,5),(2,3,4),(2,18,43)]),(13,[(2,3,4),(2,18,43)]),(38,[(1,0,5),(2,18,43)]),(45,[(2,3,4),(2,18,43)]),(4,[(1,0,5),(2,18,43)]),(1,[(2,0,5)]),(1,[(2,0,5),(0,2,3)]),(24,[(2,0,5)]),(32,[(2,0,5)]),(2,[(2,0,5)]),(6,[(2,0,5)]),(38,[(2,0,5)]),(1,[(2,0,5),(0,2,3),(1,19,27)]),(45,[(0,2,3),(1,19,27)]),(2,[(2,0,5),(1,19,27)]),(1,[(2,0,5),(1,2,3)]),(4,[(2,0,5)]),(3,[(2,0,5)]),(1,[(2,0,5),(1,2,3),(3,19,30)]),(45,[(1,2,3),(3,19,30)]),(24,[(2,0,5),(3,19,30)]),(32,[(2,0,5),(3,19,30)]),(1,[(2,0,5),(2,2,3)]),(1,[(2,0,5),(2,2,3),(1,19,31)]),(45,[(2,2,3),(1,19,31)]),(32,[(2,0,5),(1,19,31)]),(2,[(2,0,5),(1,19,31)]),(1,[(2,0,5),(3,2,3)]),(1,[(2,0,5),(3,2,3),(1,19,32)]),(45,[(3,2,3),(1,19,32)]),(24,[(2,0,5),(1,19,32)]),(1,[(2,0,5),(0,3,4)]),(1,[(2,0,5),(0,3,4),(1,3,4)]),(1,[(2,0,5),(0,3,4),(1,19,41)]),(45,[(0,3,4),(1,19,41)]),(4,[(2,0,5),(1,19,41)]),(1,[(2,0,5),(1,3,4)]),(1,[(2,0,5),(1,3,4),(3,19,42)]),(45,[(1,3,4),(3,19,42)]),(32,[(2,0,5),(3,19,42)]),(38,[(2,0,5),(3,19,42)]),(1,[(2,0,5),(2,3,4)]),(1,[(2,0,5),(2,3,4),(1,19,43)]),(45,[(2,3,4),(1,19,43)]),(38,[(2,0,5),(1,19,43)]),(4,[(2,0,5),(1,19,43)]),(45,[(0,1,2),(0,3,4)]),(45,[(0,1,2),(0,3,4),(1,3,4)]),(45,[(0,1,2),(1,3,4)]),(45,[(0,1,2),(2,3,4)]),(1,[(1,0,21)]),(45,[(2,1,2),(1,0,21)]),(24,[(1,0,21)]),(1,[(0,3,4),(1,0,21)]),(12,[(0,3,4),(2,1,2)]),(32,[(2,1,2),(1,0,21)]),(1,[(0,3,4),(1,3,4),(1,0,21)]),(12,[(0,3,4),(1,3,4),(2,1,2)]),(4,[(2,1,2),(1,0,21)]),(38,[(2,1,2),(1,0,21)]),(8,[(2,1,2),(1,0,21)]),(1,[(1,3,4),(1,0,21)]),(12,[(1,3,4),(2,1,2)]),(1,[(2,3,4),(1,0,21)]),(12,[(2,3,4),(2,1,2)]),(1,[(1,3,5),(1,0,21)]),(12,[(1,3,5),(2,1,2)]),(6,[(2,1,2),(1,0,21)]),(1,[(2,3,5),(1,0,21)]),(12,[(2,3,5),(2,1,2)]),(45,[(2,1,2),(0,3,4)]),(45,[(2,1,2),(0,3,4),(1,3,4)]),(1,[(0,3,4),(1,3,4),(3,21,42)]),(32,[(2,1,2),(3,21,42)]),(45,[(2,1,2),(1,3,4)]),(24,[(1,3,4),(0,1,42)]),(32,[(2,1,2),(0,1,42)]),(38,[(2,1,2),(0,1,42)]),(45,[(2,1,2),(1,3,4),(0,1,42)]),(1,[(1,3,4),(3,21,42)]),(24,[(1,3,4),(3,21,42)]),(45,[(2,1,2),(1,3,4),(3,21,42)]),(45,[(2,1,2),(2,3,4)]),(24,[(1,3,5),(0,1,45)]),(32,[(2,1,2),(0,1,45)]),(45,[(2,1,2),(0,1,45)]),(45,[(2,1,2),(3,21,45)]),(1,[(1,3,5),(3,21,45)]),(24,[(1,3,5),(3,21,45)]),(32,[(2,1,2),(3,21,45)]),(1,[(1,0,22)]),(45,[(0,1,3),(1,0,22)]),(3,[(1,0,22)]),(1,[(1,4,5),(1,0,22)]),(12,[(1,4,5),(0,1,3)]),(8,[(0,1,3),(1,0,22)]),(6,[(0,1,3),(1,0,22)]),(24,[(0,1,3),(1,0,22)]),(2,[(0,1,3),(1,0,22)]),(4,[(1,0,22)]),(38,[(0,1,3),(1,0,22)]),(12,[(1,4,5),(0,1,3),(0,48,147)]),(32,[(1,4,5),(0,48,147)]),(45,[(0,1,3),(1,0,22),(0,48,147)]),(1,[(1,4,5),(1,0,22),(0,48,147)]),(38,[(0,1,3),(1,0,22),(0,48,147)]),(1,[(2,4,5),(1,0,22)]),(12,[(2,4,5),(0,1,3)]),(1,[(1,0,22),(0,4,147)]),(12,[(0,1,3),(0,4,147)]),(32,[(0,4,147)]),(13,[(0,4,147)]),(3,[(1,0,22),(0,4,147)]),(45,[(0,1,3),(1,0,22),(0,4,147)]),(1,[(1,0,22),(3,4,147)]),(12,[(0,1,3),(3,4,147)]),(32,[(3,4,147)]),(13,[(3,4,147)]),(3,[(1,0,22),(3,4,147)]),(45,[(0,1,3),(1,0,22),(3,4,147)]),(45,[(0,1,3),(0,2,4)]),(1,[(0,2,4),(1,22,33)]),(45,[(0,1,3),(0,2,4),(1,22,33)]),(13,[(0,2,4),(1,22,33)]),(2,[(0,1,3),(1,22,33)]),(45,[(0,1,3),(2,2,4)]),(32,[(2,2,4),(2,1,35)]),(38,[(0,1,3),(2,1,35)]),(45,[(0,1,3),(2,2,4),(2,1,35)]),(2,[(0,1,3),(2,1,35)]),(45,[(2,2,4),(2,1,35)]),(1,[(2,2,4),(1,22,35)]),(38,[(0,1,3),(1,22,35)]),(45,[(0,1,3),(2,2,4),(1,22,35)]),(13,[(2,2,4),(1,22,35)]),(2,[(0,1,3),(1,22,35)]),(45,[(0,1,3),(2,1,38)]),(1,[(2,2,5),(1,22,38)]),(13,[(2,2,5),(1,22,38)]),(45,[(0,1,3),(1,22,38)]),(3,[(1,4,5)]),(32,[(1,4,5),(0,1,48)]),(38,[(0,1,3),(0,1,48)]),(45,[(0,1,3),(0,1,48)]),(1,[(1,4,5),(3,22,48)]),(13,[(1,4,5),(3,22,48)]),(3,[(1,4,5),(3,22,48)]),(38,[(0,1,3),(3,22,48)]),(45,[(0,1,3),(3,22,48)]),(3,[(2,4,5)]),(1,[(1,0,23)]),(45,[(2,1,3),(1,0,23)]),(32,[(1,0,23)]),(3,[(1,0,23)]),(1,[(1,4,5),(1,0,23)]),(12,[(1,4,5),(2,1,3)]),(8,[(2,1,3),(1,0,23)]),(6,[(2,1,3),(1,0,23)]),(24,[(2,1,3),(1,0,23)]),(2,[(2,1,3),(1,0,23)]),(38,[(2,1,3),(1,0,23)]),(1,[(2,4,5),(1,0,23)]),(12,[(2,4,5),(2,1,3)]),(45,[(2,1,3),(0,2,4)]),(1,[(0,2,4),(1,23,33)]),(32,[(0,2,4),(1,23,33)]),(45,[(2,1,3),(0,2,4),(1,23,33)]),(13,[(0,2,4),(1,23,33)]),(2,[(2,1,3),(1,23,33)]),(45,[(2,1,3),(2,2,4)]),(1,[(2,2,4),(1,23,35)]),(32,[(2,2,4),(1,23,35)]),(38,[(2,1,3),(1,23,35)]),(45,[(2,1,3),(2,2,4),(1,23,35)]),(13,[(2,2,4),(1,23,35)]),(2,[(2,1,3),(1,23,35)]),(1,[(2,2,5),(1,23,38)]),(32,[(2,2,5),(1,23,38)]),(13,[(2,2,5),(1,23,38)]),(45,[(2,1,3),(1,23,38)]),(1,[(1,4,5),(3,23,48)]),(13,[(1,4,5),(3,23,48)]),(3,[(1,4,5),(3,23,48)]),(32,[(1,4,5),(3,23,48)]),(38,[(2,1,3),(3,23,48)]),(45,[(2,1,3),(3,23,48)]),(1,[(1,0,26)]),(45,[(1,0,26)]),(3,[(1,0,26)]),(1,[(0,3,4),(1,0,26)]),(45,[(0,3,4),(1,0,26)]),(12,[(0,3,4),(2,1,5)]),(32,[(2,1,5),(1,0,26)]),(24,[(2,1,5),(1,0,26)]),(2,[(2,1,5),(1,0,26)]),(1,[(0,3,4),(1,3,4),(1,0,26)]),(45,[(0,3,4),(1,3,4),(1,0,26)]),(12,[(0,3,4),(1,3,4),(2,1,5)]),(4,[(2,1,5),(1,0,26)]),(38,[(2,1,5),(1,0,26)]),(1,[(1,3,4),(1,0,26)]),(45,[(1,3,4),(1,0,26)]),(12,[(1,3,4),(2,1,5)]),(6,[(2,1,5),(1,0,26)]),(1,[(2,3,4),(1,0,26)]),(45,[(2,3,4),(1,0,26)]),(12,[(2,3,4),(2,1,5)]),(1,[(0,2,3),(1,26,27)]),(13,[(0,2,3),(1,26,27)]),(45,[(0,2,3),(1,26,27)]),(47,[]),(2,[(2,1,5),(1,26,27)]),(1,[(2,2,3),(1,26,31)]),(32,[(2,1,5),(1,26,31)]),(13,[(2,2,3),(1,26,31)]),(45,[(2,2,3),(1,26,31)]),(2,[(2,1,5),(1,26,31)]),(1,[(0,3,4),(1,26,41)]),(13,[(0,3,4),(1,26,41)]),(3,[(0,3,4),(1,26,41)]),(45,[(0,3,4),(1,26,41)]),(4,[(2,1,5),(1,26,41)]),(1,[(1,3,4),(3,26,42)]),(13,[(1,3,4),(3,26,42)]),(3,[(1,3,4),(3,26,42)]),(32,[(2,1,5),(3,26,42)]),(38,[(2,1,5),(3,26,42)]),(45,[(1,3,4),(3,26,42)]),(1,[(2,3,4),(1,26,43)]),(13,[(2,3,4),(1,26,43)]),(3,[(2,3,4),(1,26,43)]),(38,[(2,1,5),(1,26,43)]),(45,[(2,3,4),(1,26,43)]),(4,[(2,1,5),(1,26,43)]),(1,[(0,2,3),(1,0,27)]),(45,[(0,2,3),(1,0,27)]),(12,[(0,2,3),(0,1,52)]),(2,[(1,0,27)]),(8,[(0,2,3),(1,0,27)]),(6,[(0,2,3),(1,0,27)]),(4,[(1,0,27)]),(38,[(0,2,3),(1,0,27)]),(32,[(1,4,5),(0,28,48)]),(45,[(0,2,3),(1,0,27),(0,28,48)]),(38,[(0,2,3),(1,0,27),(0,28,48)]),(24,[(0,4,28)]),(32,[(0,4,28)]),(1,[(0,2,3),(1,0,27),(0,4,28)]),(12,[(0,2,3),(0,4,28)]),(2,[(1,0,27),(0,4,28)]),(45,[(0,2,3),(1,0,27),(0,4,28)]),(24,[(1,4,5),(0,28,48),(1,5,230)]),(32,[(1,4,5),(0,28,48),(1,5,230)]),(23,[(1,4,5)]),(0,[(1,4,5)]),(25,[(1,4,5)]),(6,[(0,2,3),(1,0,27),(1,5,230)]),(24,[(3,4,28)]),(32,[(3,4,28)]),(1,[(0,2,3),(1,0,27),(3,4,28)]),(12,[(0,2,3),(3,4,28)]),(2,[(1,0,27),(3,4,28)]),(45,[(0,2,3),(1,0,27),(3,4,28)]),(45,[(0,2,3),(2,1,27)]),(2,[(2,1,27)]),(1,[(0,2,3),(1,4,5)]),(8,[(0,2,3),(2,1,27)]),(26,[(1,4,5)]),(6,[(0,2,3),(2,1,27)]),(4,[(2,1,27)]),(38,[(0,2,3),(2,1,27)]),(1,[(0,2,3),(2,4,5)]),(26,[(2,4,5)]),(24,[(1,4,5),(0,1,48)]),(45,[(0,2,3),(0,1,48)]),(38,[(0,1,48)]),(45,[(0,1,48)]),(7,[]),(1,[(0,2,3),(1,4,5),(3,27,48)]),(12,[(2,4,5),(2,1,51)]),(24,[(2,4,5),(2,1,51)]),(45,[(0,2,3),(2,1,51)]),(32,[(2,4,5),(2,1,51)]),(2,[(2,4,5),(2,1,51)]),(6,[(2,1,51)]),(45,[(2,1,51)]),(39,[]),(12,[(1,11,15)]),(13,[(1,11,15)]),(1,[(3,0,2),(3,0,3),(1,11,15)]),(45,[(3,0,2),(3,0,3),(1,11,15)]),(40,[]),(1,[(1,2,3),(1,4,5)]),(45,[(1,2,3),(3,0,48)]),(2,[(1,4,5),(3,0,48)]),(3,[(1,4,5),(3,0,48)]),(1,[(1,4,5),(3,0,48)]),(12,[(1,4,5),(2,1,64)]),(3,[(1,4,5),(3,6,48)]),(1,[(1,4,5),(3,6,48)]),(24,[(1,4,5),(3,0,48)]),(38,[(3,0,48)]),(45,[(3,0,48)]),(45,[(1,2,3),(0,1,48)]),(1,[(1,2,3),(1,4,5),(0,30,48)]),(24,[(1,4,5),(0,30,48)]),(32,[(1,4,5),(0,30,48)]),(38,[(1,2,3),(0,30,48)]),(45,[(1,2,3),(0,30,48)]),(1,[(1,2,3),(2,4,5)]),(45,[(1,2,3),(1,0,51)]),(2,[(2,4,5),(1,0,51)]),(3,[(2,4,5),(1,0,51)]),(1,[(2,4,5),(1,0,51)]),(51,[(1,2,3)]),(24,[(2,4,5),(1,0,51)]),(32,[(2,4,5),(1,0,51)]),(6,[(1,0,51)]),(45,[(1,0,51)]),(1,[(2,2,3),(1,0,31)]),(32,[(1,0,31)]),(45,[(2,2,3),(1,0,31)]),(12,[(2,2,3),(0,1,72)]),(50,[(0,0,1)]),(2,[(1,0,31)]),(8,[(2,2,3),(1,0,31)]),(6,[(2,2,3),(1,0,31)]),(38,[(2,2,3),(1,0,31)]),(32,[(2,1,31)]),(2,[(2,1,31)]),(1,[(1,4,5),(2,2,3)]),(8,[(2,2,3),(2,1,31)]),(6,[(2,2,3),(2,1,31)]),(1,[(2,4,5),(2,2,3)]),(1,[(2,2,3),(1,4,5)]),(45,[(2,2,3),(0,1,48)]),(1,[(2,2,3),(1,4,5),(3,31,48)]),(32,[(1,4,5),(3,31,48)]),(38,[(2,2,3),(3,31,48)]),(45,[(2,2,3),(3,31,48)]),(2,[(1,4,5),(3,31,48)]),(1,[(2,2,3),(2,4,5)]),(45,[(2,2,3),(2,1,51)]),(12,[(3,11,13)]),(13,[(3,11,13)]),(1,[(3,2,3),(1,4,5)]),(45,[(3,2,3),(3,0,48)]),(45,[(3,2,3),(0,1,48)]),(1,[(3,2,3),(1,4,5),(3,32,48)]),(24,[(1,4,5),(3,32,48)]),(38,[(3,2,3),(3,32,48)]),(45,[(3,2,3),(3,32,48)]),(1,[(3,2,3),(2,4,5)]),(45,[(3,2,3),(1,0,51)]),(51,[(3,2,3)]),(1,[(1,2,5),(3,0,37)]),(45,[(3,0,37)]),(24,[(3,0,37)]),(45,[(0,3,4),(3,0,37)]),(32,[(1,2,5),(3,0,37)]),(45,[(0,3,4),(1,3,4),(3,0,37)]),(4,[(1,2,5),(3,0,37)]),(38,[(1,2,5),(3,0,37)]),(45,[(1,3,4),(3,0,37)]),(45,[(2,3,4),(3,0,37)]),(1,[(1,2,5),(0,3,4)]),(1,[(1,2,5),(0,3,4),(1,3,4)]),(1,[(1,2,5),(0,3,4),(2,37,41)]),(24,[(0,3,4),(2,37,41)]),(45,[(0,3,4),(2,37,41)]),(4,[(1,2,5),(2,37,41)]),(1,[(1,2,5),(1,3,4)]),(32,[(0,1,42)]),(38,[(0,1,42)]),(1,[(1,2,5),(1,3,4),(0,37,42)]),(24,[(1,3,4),(0,37,42)]),(32,[(1,2,5),(0,37,42)]),(38,[(1,2,5),(0,37,42)]),(45,[(1,3,4),(0,37,42)]),(1,[(1,2,5),(2,3,4)]),(1,[(1,2,5),(2,3,4),(2,37,43)]),(24,[(2,3,4),(2,37,43)]),(38,[(1,2,5),(2,37,43)]),(45,[(2,3,4),(2,37,43)]),(4,[(1,2,5),(2,37,43)]),(1,[(2,2,5),(1,0,38)]),(45,[(1,0,38)]),(12,[(2,2,5),(0,1,84)]),(45,[(0,0,1),(1,6,38),(0,1,84)]),(45,[(0,3,4),(1,0,38)]),(32,[(2,2,5),(1,0,38)]),(2,[(1,0,38)]),(45,[(0,3,4),(1,3,4),(1,0,38)]),(4,[(2,2,5),(1,0,38)]),(38,[(2,2,5),(1,0,38)]),(45,[(1,3,4),(1,0,38)]),(45,[(2,3,4),(1,0,38)]),(45,[(2,1,38)]),(1,[(0,3,4),(2,2,5)]),(45,[(0,3,4),(2,1,38)]),(2,[(2,1,38)]),(1,[(0,3,4),(1,3,4),(2,2,5)]),(45,[(0,3,4),(1,3,4),(2,1,38)]),(4,[(2,2,5),(2,1,38)]),(1,[(1,3,4),(2,2,5)]),(45,[(1,3,4),(2,1,38)]),(1,[(2,3,4),(2,2,5)]),(45,[(2,3,4),(2,1,38)]),(1,[(2,2,5),(0,3,4)]),(1,[(2,2,5),(0,3,4),(1,3,4)]),(1,[(2,2,5),(0,3,4),(1,38,41)]),(45,[(0,3,4),(1,38,41)]),(4,[(2,2,5),(1,38,41)]),(1,[(2,2,5),(1,3,4)]),(1,[(2,2,5),(1,3,4),(3,38,42)]),(32,[(2,2,5),(3,38,42)]),(38,[(2,2,5),(3,38,42)]),(45,[(1,3,4),(3,38,42)]),(1,[(2,2,5),(2,3,4)]),(1,[(2,2,5),(2,3,4),(1,38,43)]),(38,[(2,2,5),(1,38,43)]),(45,[(2,3,4),(1,38,43)]),(4,[(2,2,5),(1,38,43)]),(1,[(0,3,4),(1,0,41)]),(45,[(0,3,4),(1,0,41)]),(12,[(0,3,4),(0,1,88)]),(4,[(1,0,41)]),(1,[(0,3,4),(1,0,79)]),(32,[(1,0,79)]),(38,[(1,0,79)]),(45,[(0,3,4),(2,1,41),(1,0,79)]),(3,[(0,3,4),(1,0,79)]),(1,[(1,3,4),(3,0,42)]),(32,[(3,0,42)]),(38,[(3,0,42)]),(45,[(1,3,4),(3,0,42)]),(12,[(1,3,4),(2,1,96)]),(1,[(1,3,4),(1,0,81)]),(4,[(1,0,81)]),(32,[(0,1,42),(1,0,81)]),(6,[(1,0,81)]),(38,[(0,1,42),(1,0,81)]),(45,[(1,3,4),(0,1,42),(1,0,81)]),(3,[(1,3,4),(1,0,81)]),(1,[(2,3,4),(1,0,43)]),(38,[(1,0,43)]),(45,[(2,3,4),(1,0,43)]),(12,[(2,3,4),(0,1,102)]),(4,[(1,0,43)]),(38,[(2,1,43)]),(45,[(2,3,4),(2,1,43)]),(1,[(2,3,4),(1,6,43),(1,0,116)]),(4,[(2,1,43)]),(1,[(1,3,5),(3,0,45)]),(45,[(3,0,45)]),(32,[(3,0,45)]),(12,[(1,3,5),(2,1,117)]),(45,[(0,0,1),(3,6,45),(2,1,117)]),(32,[(0,1,45)]),(45,[(0,1,45)]),(1,[(1,3,5),(1,0,107)]),(4,[(1,0,107)]),(32,[(0,1,45),(1,0,107)]),(45,[(0,1,45),(1,0,107)]),(3,[(1,3,5),(1,0,107)]),(8,[(1,0,107)]),(1,[(2,3,5),(1,0,46)]),(45,[(1,0,46)]),(12,[(2,3,5),(0,1,111)]),(45,[(1,0,46),(0,1,111)]),(32,[(0,1,111)]),(3,[(2,3,5),(1,0,46)]),(45,[(2,1,46)]),(1,[(2,3,5),(1,0,112)]),(12,[(2,3,5),(2,1,46)]),(32,[(1,0,112)]),(45,[(2,1,46),(1,0,112)]),(3,[(2,3,5),(1,0,112)]),(8,[(1,0,112)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 11 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice55 : Slice h0R h0G (subcubeFast 36 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice54 : Slice h0R h0G (subcubeFast 36 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice53 : Slice h0R h0G (subcubeFast 34 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice52 : Slice h0R h0G (subcubeFast 34 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice51 : Slice h0R h0G (subcubeFast 32 16) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice50 : Slice h0R h0G (subcubeFast 32 8) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice49 : Slice h0R h0G (subcubeFast 32 6) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice48 : Slice h0R h0G (subcubeFast 32 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice47 : Slice h0R h0G (subcubeFast 32 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice46 : Slice h0R h0G (subcubeFast 32 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice45 : Slice h0R h0G (subcubeFast 32 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice44 : Slice h0R h0G (subcubeFast 16 40) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice43 : Slice h0R h0G (subcubeFast 16 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice42 : Slice h0R h0G (subcubeFast 16 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice41 : Slice h0R h0G (subcubeFast 16 6) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice40 : Slice h0R h0G (subcubeFast 16 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice39 : Slice h0R h0G (subcubeFast 16 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice38 : Slice h0R h0G (subcubeFast 16 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice37 : Slice h0R h0G (subcubeFast 8 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice36 : Slice h0R h0G (subcubeFast 8 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice35 : Slice h0R h0G (subcubeFast 8 6) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 8 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 8 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 8 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 4 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 4 40) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 4 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 4 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 4 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 4 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 4 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 2 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 2 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 1 34) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 1 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 1 18) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 1 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 1 10) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 1 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 1 6) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 1 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 1 2) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 1 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 0 48) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 0 40) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 0 34) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 0 32) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 0 18) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 0 16) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 10) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 8) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 6) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h52Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h53Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (forall_cons (fun _ h => by cases h; exact h0Slice25) (forall_cons (fun _ h => by cases h; exact h0Slice26) (forall_cons (fun _ h => by cases h; exact h0Slice27) (forall_cons (fun _ h => by cases h; exact h0Slice28) (forall_cons (fun _ h => by cases h; exact h0Slice29) (forall_cons (fun _ h => by cases h; exact h0Slice30) (forall_cons (fun _ h => by cases h; exact h0Slice31) (forall_cons (fun _ h => by cases h; exact h0Slice32) (forall_cons (fun _ h => by cases h; exact h0Slice33) (forall_cons (fun _ h => by cases h; exact h0Slice34) (forall_cons (fun _ h => by cases h; exact h0Slice35) (forall_cons (fun _ h => by cases h; exact h0Slice36) (forall_cons (fun _ h => by cases h; exact h0Slice37) (forall_cons (fun _ h => by cases h; exact h0Slice38) (forall_cons (fun _ h => by cases h; exact h0Slice39) (forall_cons (fun _ h => by cases h; exact h0Slice40) (forall_cons (fun _ h => by cases h; exact h0Slice41) (forall_cons (fun _ h => by cases h; exact h0Slice42) (forall_cons (fun _ h => by cases h; exact h0Slice43) (forall_cons (fun _ h => by cases h; exact h0Slice44) (forall_cons (fun _ h => by cases h; exact h0Slice45) (forall_cons (fun _ h => by cases h; exact h0Slice46) (forall_cons (fun _ h => by cases h; exact h0Slice47) (forall_cons (fun _ h => by cases h; exact h0Slice48) (forall_cons (fun _ h => by cases h; exact h0Slice49) (forall_cons (fun _ h => by cases h; exact h0Slice50) (forall_cons (fun _ h => by cases h; exact h0Slice51) (forall_cons (fun _ h => by cases h; exact h0Slice52) (forall_cons (fun _ h => by cases h; exact h0Slice53) (forall_cons (fun _ h => by cases h; exact h0Slice54) (forall_cons (fun _ h => by cases h; exact h0Slice55) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (5 - 1) xs.toFinset) h0Empty := trivial
def h0Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,5,69],[]),([0,2,5,42,88,114],[])]
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
def h0Block6_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,50,52],[20]),([0,1,2,3,4,5,61],[1,32,34]),([0,1,2,3,4,5,63],[]),([0,1,2,3,5,53,54],[52]),([0,1,2,3,4,52,62],[32,52,53]),([0,1,2,3,5,55,56],[]),([0,2,3,4,5,50,72],[20]),([0,1,2,5,41,42,84],[84]),([0,1,2,5,38,42,88],[]),([0,1,2,5,42,88,91],[168]),([0,1,2,5,42,88,92],[]),([0,1,2,5,42,88,93],[164])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Block6_0 = true := by decide +kernel
def h0Block6_1 : List NodeSpec := nodesWithIdentity [([0,1,2,5,42,88,94],[]),([0,2,3,4,5,88,114],[]),([0,2,5,7,41,42,77],[84]),([0,1,2,5,41,42,86],[]),([0,2,5,41,87,120],[317,320]),([0,1,2,3,4,5,134],[]),([0,1,2,3,4,5,232],[11]),([0,1,2,5,41,42,85],[84])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Block6_1 = true := by decide +kernel
def h0Nodes6 : List NodeSpec := h0Block6_0 ++ h0Block6_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Nodes6 = true := by
  unfold h0Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h0Test6_0,h0Test6_1⟩
def h0Bucket6 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 6 xs.toFinset) h0Bucket6 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket5Ok h0Check6
def h0Block7_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,6,27,50],[15,16,17,18,19,20,21]),([0,1,2,3,4,5,48,52],[7,28,29,30,31,32,33,34]),([0,1,2,3,4,5,27,64],[10,11,16,18,35,36,37]),([0,1,2,3,4,5,6,66],[1,21,23,26,38,39,40,41]),([0,1,2,3,4,5,51,52],[31,32,44,45]),([0,1,2,3,4,5,52,53],[4,7,9,31,32,48,51]),([0,1,2,3,4,5,52,54],[29,30,31,32,54,55,56]),([0,1,2,3,4,5,52,55],[31,32,57]),([0,1,2,3,4,5,52,56],[4,7,31,32,58]),([0,1,2,3,4,5,52,57],[29,33,34,48,54,59]),([0,1,2,3,4,5,52,58],[4,7,33,34,48,60]),([0,2,3,4,5,6,31,50],[15,20,66])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_0 = true := by decide +kernel
def h0Block7_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,48,72],[28,31,70,71,72]),([0,1,2,3,4,5,31,64],[11,37,72]),([0,1,2,3,4,5,51,72],[32,44,45]),([0,1,2,5,6,38,41,42],[82,83,84,85]),([0,1,2,3,4,5,41,84],[7,13,53,86,87,88]),([0,1,2,3,4,5,38,88],[10,11,33,34,88]),([0,1,2,3,4,5,42,84],[12,53,88,90,96,97]),([0,1,2,3,4,5,38,96],[11,71,88]),([0,1,2,3,4,5,43,84],[13,18,53,88,100,101]),([0,1,5,39,41,42],[72,82,84,107,108,109]),([0,3,4,5,39,81],[49,109,112,114,115,116,117,118,119]),([0,1,3,4,5,39,104],[1,7,10,49,91,103,104,107,109,111,120,121])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_1 = true := by decide +kernel
def h0Block7_2 : List NodeSpec := nodesWithIdentity [([0,3,4,5,39,107],[49,109,115,124,126,127,128,129]),([0,1,3,4,5,39,110],[1,7,10,49,103,104,107,109,110,119,130,131,132,133]),([0,1,5,40,41,42],[83,84,141,142,143]),([0,1,2,5,42,88],[71,164,165,166,167,168]),([0,1,2,5,41,42,88],[9,71,82,83,84,159,162,163,164,165,169,170]),([0,1,2,3,4,5,88,91],[10,11,175]),([0,1,2,3,4,5,88,92],[10,11,175]),([0,1,2,3,4,5,88,93],[33,34,173,174]),([0,1,2,3,4,5,88,94],[33,34,174]),([0,2,5,7,21,41,42],[83,84,159,170,226,227,228,229,230,231]),([0,2,3,4,5,7,41,77],[49,61,86,221,278,279]),([0,2,3,4,5,7,42,77],[49,96,275])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_2 = true := by decide +kernel
def h0Block7_3 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,7,43,77],[49,100,256,275,277]),([0,1,2,5,7,38,41,42],[83,159,170]),([0,1,2,3,4,5,41,86],[13,50,281,282,283]),([0,1,2,3,4,5,42,86],[12,50,283]),([0,1,2,3,4,5,43,86],[13,50,284,285,286]),([0,1,2,5,41,42,90],[12,82,83,162,163,164,168,170,229,293,294,295,296]),([0,1,2,3,4,5,82,90],[33,34,171,216]),([0,2,5,41,42,120],[71,83,84,170,316,317,318,319]),([0,2,3,4,5,41,83,120],[317,318,322,323]),([0,2,3,4,5,41,120],[1,11,49,86,217,220,225,317,319,322,323]),([0,2,3,4,5,120,125],[1,11,49,71,90,217,220,225,317,319,321,322,338]),([0,1,2,5,42,126],[71,165,296,318,352,353,354])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_3 = true := by decide +kernel
def h0Block7_4 : List NodeSpec := nodesWithIdentity [([0,1,2,5,41,42,126],[71,83,84,159,162,163,165,170,341,352]),([0,1,2,3,4,5,18,133],[11,33,34,72,379,386,409,410]),([0,1,2,3,4,5,9,135],[10,11,34,405,407,411,412,413]),([0,1,2,5,41,136],[72,82,161,318,382,418,419,420,421,422]),([0,1,2,5,41,42,136],[72,82,83,84,159,161,162,163,382,418,420,422]),([0,1,2,3,4,5,138,139],[31,32,332,450,452]),([0,1,2,3,4,5,138,140],[31,32,332]),([0,1,2,5,41,42,113],[12,13,73,82,83,84,159,161,162,163,170,545,546,547,548]),([0,1,2,5,41,42,153],[73,82,83,84,159,162,163,352,492,547]),([0,1,2,3,4,157,158],[1,13,33,603,604,625,626,627,628,629,630]),([0,1,2,3,4,158,159],[1,13,33,616,625,626,627,628,629,630,632,633,634]),([0,1,2,3,4,5,179],[0,1,11,13,32,33,34,49,604])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_4 = true := by decide +kernel
def h0Block7_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,21,135],[10,11,61]),([0,1,2,5,41,42,132],[12,13,82,83,84,159,162,163,170,318,413,812,1043,1070,1074,1075,1076]),([0,1,2,5,41,203],[318,406,413,812,1131,1132,1133,1134]),([0,1,2,5,41,42,119],[12,13,72,82,83,84,159,162,163,229,548,1202,1203,1204,1205]),([0,1,2,5,41,42,121],[82,83,84,159,162,163,229,548,750,1219,1220]),([0,1,2,3,4,5,214],[0,1,10,11,13,32,34,49,1242,1248,1249,1250,1251,1252]),([0,1,2,5,41,42,151],[12,13,82,83,159,162,163,413,812,1339,1342,1343,1344,1345]),([0,1,2,3,4,5,230],[0,1,11,13,32,34,49,1385,1389,1390,1391]),([0,1,2,3,4,28,231],[32,33,53,550,1388,1390,1398,1399,1400,1401,1402,1403]),([0,1,2,3,4,5,30,65],[10,11,49,1444,1445,1446]),([0,1,2,3,4,5,32,65],[10,11,49,547]),([0,1,2,5,41,42,165],[12,13,72,82,83,84,159,161,162,812,1506,1507,1508])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_5 = true := by decide +kernel
def h0Block7_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,41,85],[7,13,49,86,89,281]),([0,1,2,3,4,5,42,85],[12,49,89,96,97]),([0,1,2,3,4,5,43,85],[13,18,49,100,286,1535]),([0,1,2,5,41,42,76],[12,13,82,83,84,159,162,413,547,1537,1539,1540]),([0,1,2,5,41,42,77],[12,13,82,83,84,159,162,279,413,547,548,1548,1549,1550])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_6 = true := by decide +kernel
def h0Nodes7 : List NodeSpec := h0Block7_0 ++ h0Block7_1 ++ h0Block7_2 ++ h0Block7_3 ++ h0Block7_4 ++ h0Block7_5 ++ h0Block7_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Nodes7 = true := by
  unfold h0Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h0Test7_0,h0Test7_1⟩,h0Test7_2⟩,h0Test7_3⟩,h0Test7_4⟩,h0Test7_5⟩,h0Test7_6⟩
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket6Ok h0Check7
def h0Block8_0 : List NodeSpec := [([0,1,2,3,4,5,6,27,48],[2,3,4,7,14,16,18,21,22,23,24,25,26,27,28],[0]),([0,1,2,3,4,5,6,27,51],[4,7,16,21,24,25,42,43,44,46,47],[0]),([0,1,2,3,4,5,52],[0,1,4,7,9,10,11,29,30,31,32,33,34,48,49,50],[0]),([0,1,2,3,4,5,6,52],[0,1,2,4,7,11,14,16,18,25,29,48,50],[0]),([0,1,2,3,4,5,6,31,48],[7,16,22,23,28,62,63,66,67,68,69,73],[0]),([0,1,2,3,4,5,6,31,51],[7,25,42,43,44,47,63,66,67,74],[0]),([0,1,2,3,4,5,72],[0,1,7,10,11,31,32,33,34,49,50,63,65,70,71,75,76,77],[0]),([0,1,2,3,4,5,6,38,41],[7,9,14,79,80,81,85,86,89],[0]),([0,1,2,3,4,5,6,38,42],[7,65,78,79,85,89,90,91,92,93,94,95,96],[0]),([0,1,2,3,4,5,6,38,43],[2,7,9,18,79,85,89,93,98,99,100,102],[0]),([0,1,2,3,4,5,84],[0,1,7,10,11,12,13,31,32,34,49,50,53,79,97,101],[0,1]),([0,1,3,4,5,39,41],[1,6,10,49,72,80,86,103,104,105,106,107,109,110,111],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := nodesWithIdentity [([0,1,3,4,5,39,42],[1,6,10,49,91,96,103,104,107,109,110,111,112,113,119]),([0,1,3,4,5,39,43],[1,6,10,49,72,98,100,103,104,107,109,110,111,119,122,123]),([0,1,3,4,5,39,45],[1,6,10,49,103,104,107,109,110,119,124,125,130]),([0,1,3,4,5,39,46],[1,6,10,49,72,103,104,107,110,119,134,135,136]),([0,1,3,4,5,40,41],[1,6,11,49,81,86,137,138,139,140,141,143,144,145,146]),([0,1,3,4,5,40,42],[1,6,11,49,92,96,137,138,141,143,144,145,146,147,148,149]),([0,1,3,4,5,40,43],[1,6,11,49,99,100,137,138,141,143,144,145,146,149,150,151]),([0,1,3,4,5,40,45],[1,6,11,49,125,137,138,141,143,144,146,149,152,153]),([0,1,3,4,5,40,46],[1,6,11,49,135,137,138,141,144,146,149,154,155]),([0,1,2,5,6,41,42],[9,12,13,65,71,82,83,84,159,160,161,162,163]),([0,1,2,3,4,5,88],[0,1,9,10,11,12,13,25,33,34,49,50,86,166,173,174,175]),([0,1,2,3,4,5,6,88],[0,1,2,7,9,13,14,18,50,65,86,173,174])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
def h0Block8_2 : List NodeSpec := [([0,1,2,3,4,5,41,88],[1,9,12,13,80,81,86,156,171,172,173,174,176],[0]),([0,2,3,4,5,6,81],[12,16,31,49,50,65,90,114,117,177,179,180,181,182,183],[0]),([0,1,2,3,4,5,96],[0,1,10,11,12,13,16,33,34,49,50,65,71,96,186,187,188,189,190],[0]),([0,1,2,3,4,5,102],[0,1,9,10,11,12,13,16,33,34,37,49,50,100,102,196,197,198,199,200],[0]),([0,2,3,4,5,6,107],[12,33,49,50,65,126,129,201,202,203,204,205],[0,1]),([0,1,2,3,4,5,117],[0,1,10,11,12,13,31,32,34,49,50,65,71,125,208,209,210,211],[0,1]),([0,2,3,4,5,7,21,41],[61,81,86,156,176,217,219,220,221,222,223,224,225,226,230,231,232,233],[0]),([0,2,3,4,5,7,21,42],[49,61,92,96,177,217,219,220,221,222,225,226,229,231,232,233,234,235,236],[0]),([0,2,3,4,5,7,21,43],[61,99,100,191,217,219,220,221,222,225,226,231,232,233,237,238,239],[0]),([0,2,3,4,5,7,21,45],[49,61,90,125,153,201,217,219,220,221,222,225,226,231,232,233,240,241,242,243],[0]),([0,2,3,4,5,7,21,46],[61,135,155,212,217,219,220,221,222,225,226,232,243,244,245,246],[0]),([0,2,3,4,5,7,29],[0,1,3,11,13,49,90,221,247,248,250,251,252],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_2 = true := by decide +kernel
def h0Block8_3 : List NodeSpec := [([0,1,2,3,4,5,60],[10,11,12,29,31,32,33,34,49,50,229,248,257,258,259,260,261],[0]),([0,2,3,4,5,7,71],[0,1,11,12,49,62,90,221,262,263,265,266,267,268,269,270],[0]),([0,1,2,3,4,5,74],[10,11,13,31,32,33,34,49,50,70,72,261,263,271,272,273,274],[0]),([0,2,3,4,5,7,77],[0,1,11,33,49,78,221,275,276,277,279,280],[0,1]),([0,1,2,3,4,5,7,38,41],[54,78,81,85,89,90,156,176,220,221,247,275],[0]),([0,1,2,3,4,5,7,38,42],[54,89,92,93,177,221,236,262,275],[0]),([0,1,2,3,4,5,7,38,43],[54,85,89,99,191,218,221,239,247,256,275],[0]),([0,1,2,3,4,5,86],[10,12,13,31,32,34,49,50,97,275,281,282,284,285,287],[0,1]),([0,2,3,4,5,7,79],[1,13,32,49,90,156,158,176,220,247,255,289,290,291],[0]),([0,1,2,5,7,41,42],[12,13,82,83,84,159,161,162,163,170,229,247,262,292],[0]),([0,1,2,3,4,5,90],[10,11,12,13,31,33,34,49,50,54,173,175,176,229,261,295,297,298],[0]),([0,1,2,3,4,5,41,90],[12,13,31,54,80,81,171,172,173,175,176,217,261,294,295,297,298],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_3 = true := by decide +kernel
def h0Block8_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,98],[10,11,12,13,32,33,34,49,50,54,186,190,229,236,261,300,301,302]),([0,1,2,3,4,5,116],[10,11,12,13,32,33,34,49,50,54,196,199,239,261,286,304,305,306]),([0,1,2,3,4,5,109],[10,11,13,31,32,34,49,50,54,126,242,307,308,309,310,311]),([0,2,3,4,5,41,120],[1,6,11,37,49,53,71,81,86,176,217,220,315,317,318,321,322]),([0,2,3,4,5,42,120],[1,6,11,37,49,53,71,92,96,217,220,236,319,322,324,325]),([0,2,3,4,5,43,120],[1,6,11,37,49,53,71,99,100,217,220,239,317,322,325,326]),([0,2,3,4,5,44,120],[1,6,11,37,49,53,71,217,220,317,318,322,327,328,329,330]),([0,2,3,4,5,45,120],[1,6,11,37,49,53,71,125,153,217,220,242,319,322,323,331,332]),([0,2,3,4,5,46,120],[1,6,11,37,49,53,71,135,155,217,220,246,317,322,323,332,333]),([0,2,3,4,5,47,120],[1,6,11,37,49,71,217,220,319,322,334,335,336,337]),([0,1,2,3,4,5,8,79],[1,6,10,11,13,32,49,50,156,176,229,289,294,312,313,339,341,342,343,344,345,346,347,348,349]),([0,1,2,5,8,41,42],[12,13,71,83,84,159,162,163,170,341,346,350,351])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_4 = true := by decide +kernel
def h0Block8_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,126],[0,1,10,11,12,13,33,34,49,81,86,176,318,341,342,353,355,356]),([0,1,2,3,4,5,8,126],[1,6,10,11,13,86,312,313,341,346,349,355,356]),([0,1,2,3,4,5,41,126],[1,12,13,81,86,156,171,172,176,341,355,356]),([0,1,2,3,4,5,127],[0,1,10,11,12,13,33,34,49,71,92,96,236,346,359,360,361,362,363]),([0,1,2,3,4,5,128],[0,1,10,11,12,13,33,34,37,49,99,100,239,341,359,367,368,369,370]),([0,1,2,3,4,5,129],[0,1,10,11,12,13,31,32,34,49,71,125,153,242,346,372,373,374]),([0,1,2,3,4,5,9,18,41],[80,81,171,172,318,379,382,386,387,390,391,402,403,405,406,407,408]),([0,1,2,5,9,41,42],[12,13,72,82,83,84,159,161,162,163,170,318,379,382,416,417]),([0,1,2,3,4,5,133],[0,1,10,11,12,13,33,34,49,72,80,158,379,386,409,423,424,425,426,427]),([0,1,2,3,4,5,136],[0,1,10,11,12,13,33,34,49,91,182,318,382,387,422,430,431,432,433,434,435]),([0,1,2,3,4,5,9,136],[1,6,10,11,12,91,376,379,382,390,391,430,431,433,435]),([0,1,2,3,4,5,42,136],[10,12,13,91,92,96,177,182,184,185,382,422,430,431,433,435,436])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_5 = true := by decide +kernel
def h0Block8_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,137],[0,1,10,11,12,13,33,34,49,72,98,193,332,379,387,439,440,441,442,443,444,445]),([0,1,2,3,4,5,138],[0,1,10,11,13,31,32,34,49,130,204,261,332,382,391,447,448,449,450,451,452]),([0,1,2,3,4,5,9,138],[1,6,10,11,12,130,376,379,382,386,387,390,447,448,450,451]),([0,1,2,3,4,5,45,138],[10,13,34,125,130,153,201,204,206,207,382,447,448,450,451,452,453]),([0,1,2,5,10,41,42],[12,13,71,72,82,83,84,159,162,163,170,459,461,462,463]),([0,1,2,3,4,5,141],[0,1,10,11,12,13,33,34,49,54,80,86,176,459,460,465,466,467,468]),([0,1,2,3,4,5,142],[0,1,10,11,12,13,33,34,49,54,91,96,236,463,471,472,473,474,475,476]),([0,1,2,3,4,5,143],[0,1,10,11,12,13,33,34,49,54,98,100,239,459,471,479,480,481,482,483]),([0,1,2,3,4,5,144],[0,1,10,11,12,13,31,32,34,49,54,125,130,242,463,464,485,486,487,488]),([0,1,2,3,4,5,148],[0,1,6,10,11,12,31,32,33,34,492,503,506,511,512,513,514,515]),([0,1,2,3,4,5,150],[0,1,6,10,11,13,31,32,33,34,494,506,517,524,525,526,527,528,529]),([0,1,2,3,4,5,152],[0,1,6,10,12,13,31,32,34,318,498,531,537,538,539,540,541])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_6 = true := by decide +kernel
def h0Block8_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,41,113],[11,12,13,14,31,32,41,49,50,61,73,80,81,86,137,156,158,171,172,176,542,543,544,547,549,550,551]),([0,1,2,3,4,5,42,113],[11,12,13,14,31,32,41,49,50,61,91,92,96,137,177,184,185,236,542,547,549,550,552,553,554]),([0,1,2,3,4,5,43,113],[11,12,13,14,31,32,41,49,50,61,73,98,99,100,137,191,194,195,239,542,547,549,550,555,556,557]),([0,1,2,3,4,5,45,113],[11,12,13,14,33,34,41,49,50,61,90,125,130,137,153,201,206,207,242,542,547,549,558,559,560,561]),([0,1,2,3,4,5,46,113],[11,12,13,14,33,34,41,49,50,61,90,135,136,137,155,212,214,215,216,246,542,547,549,550,560,562,563,564]),([0,1,2,5,11,41,42],[12,13,82,83,84,159,162,163,170,318,492,494,547,567,568]),([0,1,2,3,4,5,153],[0,1,10,11,12,13,33,34,49,81,146,492,495,569,570,571,572,573,574,575]),([0,1,2,3,4,5,41,153],[11,12,13,73,80,81,86,156,171,172,492,569,570,572]),([0,1,2,3,4,5,154],[0,1,10,11,12,13,33,34,49,92,146,494,496,574,578,579,580,581,582,583,584]),([0,1,2,3,4,5,155],[0,1,10,11,12,13,33,34,49,99,146,492,496,574,587,588,589,590,591,592,593]),([0,1,2,3,4,5,156],[0,1,10,11,13,31,32,34,49,146,153,494,498,574,595,596,597,598,599,600]),([0,1,2,3,4,5,12,157],[1,6,12,13,50,146,547,602,603,604,608,609,610,611,612])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_7 = true := by decide +kernel
def h0Block8_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,12,159],[1,6,11,12,13,32,49,50,61,602,603,605,608,610,612,613,614,615,616,617,618,619,620,621,622]),([0,1,2,3,4,33,158],[1,13,33,550,604,606,624,625,627,629,630,631,632,635]),([0,1,2,3,4,5,160],[0,1,10,11,13,33,34,49,318,604,606,608,613,614,636,637,638]),([0,1,2,3,4,5,12,160],[1,6,11,13,602,603,604,608,610,612,636,637]),([0,1,2,3,4,5,33,160],[1,10,11,604,606,608,613,615,623,635,636,637]),([0,1,2,3,4,34,158],[1,13,33,52,146,625,627,629,630,632,639,641,648,649,650,651,652]),([0,1,2,3,4,5,161],[0,1,10,11,13,33,34,49,146,610,639,641,643,644,653,654,655,656]),([0,1,2,3,4,35,158],[1,13,33,37,366,550,625,627,629,630,632,650,657,659,664,665,666]),([0,1,2,3,4,5,163],[0,1,10,11,13,33,34,37,49,608,644,657,659,661,667,668,669,670]),([0,1,2,3,4,36,158],[1,13,33,146,625,627,629,630,632,651,671,673,678,679,680,681]),([0,1,2,3,4,5,164],[0,1,10,11,13,33,34,49,146,610,614,671,673,675,682,683,684]),([0,1,2,3,4,5,166],[0,1,10,11,13,31,32,34,49,146,610,685,687,688,692,693,694])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_8 = true := by decide +kernel
def h0Block8_9 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,167],[0,1,10,11,13,31,32,34,49,53,79,85,275,608,612,696,697,698]),([1,2,3,4,5,12,49],[12,28,31,33,37,50,54,644,701,702,703,704,705]),([0,1,2,3,4,5,168],[0,1,10,11,12,13,28,31,32,34,37,49,612,644,700,701,707,708,709]),([0,2,3,4,5,20,130],[10,12,49,90,217,383,736,737,738,739,740,741,742,743]),([0,2,3,4,5,24,130],[12,31,49,90,217,383,737,740,742,743,758,759,760,761]),([0,1,2,3,4,5,169],[0,1,6,10,11,12,13,31,33,34,384,506,761,766,767,768,769,770,771]),([0,1,2,3,4,5,170],[0,1,6,10,11,12,13,32,33,34,385,506,775,780,781,782,783,784,785,786]),([0,1,2,3,4,5,171],[0,1,6,10,11,13,31,32,34,253,389,533,787,788,789,790,791,792]),([0,1,2,3,4,5,33,130],[10,11,12,31,32,49,50,54,383,604,606,613,615,623,635,737,740,742,743,793,794,795,796,797,798,799,800,801]),([0,1,2,3,4,5,35,130],[10,11,12,31,32,49,50,54,383,657,659,661,662,663,666,737,740,742,743,793,794,799,800,801,802,803,804,805]),([0,1,2,3,4,5,38,130],[10,11,12,33,34,49,50,54,78,79,85,90,93,94,95,275,383,737,740,742,743,793,794,800,801,806,807,808]),([0,1,2,3,4,5,48,130],[12,22,23,28,31,32,33,34,49,50,90,383,700,701,706,737,742,743,793,794,799,800,801,808,809,810,811,812])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_9 = true := by decide +kernel
def h0Block8_10 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,51,130],[12,31,32,33,34,42,43,44,45,49,50,90,383,711,712,713,737,742,743,793,794,799,801,813,814,815]),([0,1,2,3,4,5,172],[0,1,10,11,12,13,33,34,49,54,253,378,384,797,818,819,820,821,822,823]),([0,1,2,3,4,5,34,130],[10,11,12,31,32,49,383,574,639,641,643,645,647,652,737,740,742,743,793,794,799,800,801,826,827,828,829]),([0,1,2,3,4,5,173],[0,1,10,11,12,13,33,34,49,54,318,381,385,740,826,830,831,832,833,834,835,836]),([0,1,2,3,4,5,13,173],[1,10,12,13,378,381,383,388,389,740,826,830,831,833,834,836]),([0,1,2,3,4,5,34,173],[10,11,12,381,574,639,641,645,647,652,826,830,831,833,836]),([0,1,2,3,4,5,174],[0,1,10,11,12,13,33,34,49,54,253,378,385,804,839,840,841,842,843,844,845]),([0,1,2,3,4,5,36,130],[10,11,12,31,32,41,49,383,671,673,675,676,677,680,737,740,742,743,793,794,799,800,801,848,849,850,851]),([0,1,2,3,4,5,175],[0,1,10,11,12,13,33,34,41,49,54,381,384,740,848,852,853,854,855,856,857]),([0,1,2,3,4,5,37,130],[10,11,12,33,34,49,90,383,685,687,688,689,690,691,737,740,742,743,793,794,799,801,808,859,860,861,862]),([0,1,2,3,4,5,176],[0,1,10,11,13,31,32,34,49,54,381,740,859,862,863,864,865,866,867,868]),([0,1,2,3,4,5,177],[0,1,10,11,13,31,32,34,49,54,93,378,389,506,870,871,872,873,874])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_10 = true := by decide +kernel
def h0Block8_11 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,178],[0,1,10,11,12,13,32,34,49,261,385,389,506,811,812,876,877,878,879,880,881]),([0,1,2,3,4,5,14,157],[1,6,12,13,50,146,604,609,611,883,884,887,888,889,890]),([0,1,2,3,4,5,14,159],[1,6,11,12,13,32,49,50,61,613,615,616,617,618,619,620,621,883,884,885,888,889,890,891,892,893]),([0,1,2,3,4,5,180],[0,1,10,11,12,33,34,49,547,604,613,797,888,891,894,895,896,897]),([0,1,2,3,4,5,181],[0,1,10,11,12,33,34,49,146,639,643,826,889,900,902,903,904,905,906]),([0,1,2,3,4,5,182],[0,1,10,11,12,33,34,37,49,657,661,804,888,900,909,910,911,912,913]),([0,1,2,3,4,5,183],[0,1,10,11,12,33,34,49,146,671,675,848,889,891,916,917,918,919]),([0,1,2,3,4,5,184],[0,1,10,11,12,31,32,34,49,146,685,688,859,889,921,922,923,924]),([0,1,2,3,4,5,185],[0,1,10,11,12,31,32,34,49,53,79,93,275,888,926,927,928]),([0,1,2,3,4,5,186],[0,1,10,11,12,13,28,31,32,34,37,49,701,811,900,930,931,932,933]),([0,1,2,3,4,5,187],[0,1,6,10,11,12,13,31,33,34,397,506,756,942,943,944,945,946,947]),([0,1,2,3,4,5,188],[0,1,6,10,11,12,13,32,33,34,398,506,773,949,950,951,952,953,954,955])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_11 = true := by decide +kernel
def h0Block8_12 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,189],[0,1,6,10,11,12,31,32,34,253,400,534,956,957,958,959,960,961]),([0,1,2,3,4,5,33,131],[10,11,13,31,32,49,50,54,294,396,604,606,613,615,623,635,797,939,962,963,964,965,966,967,968,969,970]),([0,1,2,3,4,5,35,131],[10,11,13,31,32,49,50,54,294,396,657,659,661,662,663,666,804,939,962,963,964,967,968,969,970,971,972]),([0,1,2,3,4,5,38,131],[10,11,13,33,34,49,50,54,78,79,85,93,94,95,275,294,396,939,962,963,964,967,968,973,974,975]),([0,1,2,3,4,5,48,131],[13,22,23,28,31,32,33,34,49,50,90,294,396,700,701,706,811,962,963,964,967,968,969,970,975,976,977,978]),([0,1,2,3,4,5,51,131],[13,31,32,33,34,42,43,44,45,49,50,294,396,711,712,713,815,962,963,964,967,968,969,979,980]),([0,1,2,3,4,5,190],[0,1,10,11,12,13,33,34,49,54,229,393,397,606,983,984,985,986,987,988]),([0,1,2,3,4,5,191],[0,1,10,11,12,13,33,34,49,54,71,395,398,641,939,991,992,993,994,995,996,997]),([0,1,2,3,4,5,192],[0,1,10,11,12,13,33,34,49,54,229,393,398,659,1000,1001,1002,1003,1004,1005,1006]),([0,1,2,3,4,5,193],[0,1,10,11,12,13,33,34,49,54,71,395,397,673,939,1009,1010,1011,1012,1013,1014]),([0,1,2,3,4,5,194],[0,1,10,11,12,31,32,34,49,54,71,395,687,939,1016,1017,1018,1019,1020,1021]),([0,1,2,3,4,5,195],[0,1,10,11,12,31,32,34,49,54,85,229,393,400,1023,1024,1025,1026,1027])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_12 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_12 = true := by decide +kernel
def h0Block8_13 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,15,49],[6,12,28,31,33,50,398,703,1029,1030,1031]),([0,1,2,3,4,5,196],[0,1,10,11,12,13,32,34,49,71,229,398,400,700,1032,1033,1034,1035,1036,1037]),([0,2,3,4,5,20,132],[10,33,49,217,318,404,747,1039,1040,1041,1042,1043,1044]),([0,1,2,3,4,5,18,21,41],[80,81,172,318,402,403,405,551,748,750,751,752,753,754,1045]),([0,2,3,4,5,22,132],[12,33,49,217,318,404,510,1040,1042,1043,1044,1046,1047]),([0,1,2,3,4,5,197],[0,1,6,10,11,12,31,32,34,318,405,1048,1049,1050,1051,1052]),([0,1,2,3,4,5,198],[0,1,6,10,11,13,31,32,34,73,406,1053,1054,1055,1056,1057,1058]),([0,1,2,3,4,5,27,132],[3,4,10,11,12,13,21,24,26,27,33,49,50,54,248,332,404,1040,1042,1043,1044,1059,1060,1061,1062,1063,1064,1065,1066]),([0,1,2,3,4,5,31,132],[10,11,12,13,33,49,50,54,62,63,66,67,68,69,263,332,404,1040,1042,1043,1044,1059,1060,1064,1065,1066,1067,1068,1069,1070]),([0,1,2,3,4,5,41,132],[12,13,31,32,33,49,50,80,81,86,156,171,172,176,318,404,413,1040,1043,1044,1059,1060,1064,1066,1070,1071,1072,1073]),([0,1,2,3,4,5,42,132],[12,13,31,32,33,49,50,91,92,96,177,184,185,236,318,404,812,1040,1043,1044,1059,1060,1064,1065,1066,1070,1077,1078,1079]),([0,1,2,3,4,5,43,132],[12,13,31,32,33,49,50,98,99,100,191,194,195,239,286,318,404,1040,1043,1044,1059,1060,1064,1065,1066,1070,1080,1081,1082])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_13 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_13 = true := by decide +kernel
def h0Block8_14 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,199],[0,1,10,11,12,26,31,32,34,49,54,332,402,405,1084,1085,1086,1087,1088]),([0,1,2,3,4,5,30,132],[10,11,12,13,33,49,404,812,1040,1042,1043,1044,1059,1060,1064,1065,1066,1070,1089,1091,1092,1093,1094,1095,1096,1097,1098,1099]),([0,1,2,3,4,5,200],[0,1,10,11,13,31,32,34,49,54,403,406,812,1042,1097,1100,1101,1102,1103,1104,1105]),([0,1,2,3,4,5,201],[0,1,10,11,13,31,32,34,49,54,73,402,406,1107,1108,1109,1110,1111,1112]),([0,1,2,3,4,5,32,132],[10,11,12,13,33,49,404,547,1040,1042,1043,1044,1059,1060,1064,1065,1066,1113,1115,1116,1117,1118,1119,1120,1121,1122,1123]),([0,1,2,3,4,5,202],[0,1,10,11,12,31,32,34,49,54,403,405,547,1042,1124,1125,1126,1127,1128]),([0,1,2,5,18,41,42],[12,13,82,83,84,159,162,163,170,216,318,405,406,413,1130]),([0,1,2,3,4,5,135],[0,1,10,11,12,13,31,34,49,318,405,407,411,413,1135,1136,1137,1138]),([0,1,2,3,4,5,203],[0,1,10,11,12,13,32,34,49,318,406,408,812,1134,1140,1141,1142,1143,1144]),([0,1,2,3,4,5,204],[0,1,10,11,12,13,32,34,49,286,318,332,405,408,1146,1147,1148,1149,1150,1151]),([0,1,2,3,4,5,205],[0,1,4,10,11,26,31,32,33,34,49,248,261,1154,1155,1159,1160,1161]),([0,1,2,3,4,5,206],[0,1,10,11,31,32,33,34,49,146,1089,1091,1097,1156,1163,1165,1166,1167,1168])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_14 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_14 = true := by decide +kernel
def h0Block8_15 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,207],[0,1,10,11,31,32,33,34,49,63,71,263,1154,1163,1170,1171,1172,1173]),([0,1,2,3,4,5,208],[0,1,10,11,31,32,33,34,49,146,1113,1115,1121,1155,1156,1175,1176,1177]),([0,1,2,5,19,41,42],[12,13,82,83,84,159,162,163,170,216,413,1155,1163,1179]),([0,1,2,3,4,5,209],[0,1,10,11,12,13,33,34,49,86,172,176,261,1155,1158,1180,1181,1182]),([0,1,2,3,4,5,210],[0,1,10,11,12,13,33,34,49,71,96,236,1157,1163,1184,1185,1186,1187]),([0,1,2,3,4,5,211],[0,1,10,11,12,13,33,34,37,49,100,195,239,1155,1157,1189,1190,1191,1192]),([0,1,2,5,20,41,42],[12,13,83,84,159,161,162,163,170,318,734,741,1194]),([0,1,2,3,4,5,41,119],[10,12,13,31,32,49,50,72,80,81,86,146,156,171,172,219,551,1197,1198,1199,1200,1201,1202,1205,1206,1207]),([0,1,2,3,4,5,42,119],[10,12,13,31,32,49,50,91,92,96,146,177,184,185,219,229,554,1197,1198,1199,1202,1205,1206,1207,1208,1209]),([0,1,2,3,4,5,43,119],[10,12,13,31,32,49,50,72,98,99,100,146,191,194,195,219,557,1197,1198,1199,1202,1205,1206,1207,1210,1211]),([0,1,2,3,4,5,45,119],[10,12,13,33,34,49,50,125,130,146,153,201,206,207,219,229,561,1197,1198,1199,1202,1205,1206,1207,1212,1213,1214]),([0,1,2,3,4,5,46,119],[10,12,13,33,34,49,50,135,136,146,155,212,214,215,216,219,564,1197,1198,1199,1202,1206,1214,1215,1216])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_15 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_15 = true := by decide +kernel
def h0Block8_16 : List NodeSpec := nodesWithIdentity [([0,1,2,5,21,41,42],[12,13,72,82,83,84,159,162,163,170,318,748,750,1218]),([0,2,3,4,5,21,81],[6,11,12,31,49,114,117,177,183,236,750,752,1222,1223,1224,1225]),([0,1,2,3,4,5,42,121],[10,12,13,91,92,96,177,184,185,229,554,750,1220,1226,1227,1228]),([0,2,3,4,5,21,107],[6,11,12,33,49,126,129,201,205,242,750,1230,1231,1232]),([0,1,2,3,4,5,45,122],[10,13,34,125,130,153,201,206,207,261,561,750,1233,1234,1235,1236]),([0,1,2,3,4,5,48,147],[13,22,23,28,31,32,33,34,49,50,261,502,700,706,811,978,1237,1238,1240,1241,1242,1243,1244,1245,1246,1247]),([0,1,2,3,4,5,51,147],[13,31,32,33,34,42,43,44,45,49,50,261,502,711,713,815,1237,1238,1242,1244,1245,1246,1247,1253,1254]),([0,1,2,3,4,5,147,212],[13,31,32,49,50,54,261,502,1237,1238,1242,1243,1244,1245,1247,1255,1256,1257,1258,1259,1260]),([0,1,2,3,4,5,147,213],[13,31,32,49,50,54,261,502,1237,1238,1242,1243,1244,1245,1247,1261,1262,1263,1264,1265,1266]),([0,1,2,3,4,5,215],[0,1,10,11,12,13,33,34,50,229,503,508,606,801,1268,1269,1270,1271]),([0,2,3,4,5,22,162],[6,11,12,31,49,503,507,661,662,1273,1274,1275,1276,1277]),([0,1,2,3,4,5,216],[0,1,10,11,12,13,33,34,50,229,503,507,659,801,1278,1279,1280,1281,1282])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_16 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_16 = true := by decide +kernel
def h0Block8_17 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,22,77],[6,11,12,33,49,78,275,279,280,503,1283]),([0,1,2,3,4,5,217],[0,1,10,11,12,31,32,34,50,85,229,503,801,1284,1285,1286]),([0,2,3,4,5,22,50],[6,12,15,20,31,33,49,507,701,706,1287,1288,1289,1290]),([0,1,2,3,4,5,218],[0,1,10,11,12,13,32,34,50,229,507,510,700,801,1291,1292,1293,1294,1295]),([0,1,2,3,4,5,48,149],[12,22,23,28,31,32,33,34,49,50,71,261,516,700,706,811,812,1297,1298,1299,1301,1302,1303,1304,1305,1306,1307]),([0,1,2,3,4,5,51,149],[12,31,32,33,34,42,43,44,45,49,50,71,516,711,713,815,1297,1298,1299,1305,1306,1307,1308,1309]),([0,1,2,3,4,5,219],[0,1,10,11,12,13,33,34,50,294,318,517,521,797,1311,1312,1313,1314,1315]),([0,1,2,3,4,5,220],[0,1,10,11,12,13,33,34,50,294,318,517,520,804,1317,1318,1319,1320,1321,1322]),([0,1,2,3,4,5,221],[0,1,10,11,13,31,32,34,50,93,294,506,517,1323,1324,1325,1326]),([0,1,2,3,4,5,222],[0,1,10,11,12,13,32,34,50,294,506,520,811,1327,1328,1329,1330,1331,1332]),([0,1,2,3,4,5,41,151],[12,13,31,32,33,49,50,53,80,81,156,171,172,413,530,1333,1334,1336,1337,1338,1339,1340,1341,1345,1346]),([0,1,2,3,4,5,42,151],[12,13,31,32,33,49,50,53,91,92,177,184,185,530,812,1333,1334,1339,1340,1341,1345,1346,1347,1348,1349,1350])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_17 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_17 = true := by decide +kernel
def h0Block8_18 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,43,151],[12,13,31,32,33,49,50,53,98,99,191,194,195,286,530,1333,1334,1339,1340,1341,1345,1346,1350,1351,1352,1353]),([0,1,2,3,4,5,223],[0,1,10,11,12,26,31,32,34,50,253,531,534,1354,1355,1356,1357,1358]),([0,1,2,3,4,5,224],[0,1,10,11,13,31,32,34,50,253,531,533,1357,1359,1360,1361,1362,1363]),([0,1,2,5,26,41,42],[12,13,82,83,84,159,161,162,163,170,216,318,413,533,534]),([0,1,2,3,4,5,225],[0,1,10,11,12,13,31,34,50,89,534,536,1357,1364,1365,1366,1367,1368]),([0,1,2,3,4,5,226],[0,1,10,11,12,13,32,34,50,89,185,533,535,1357,1369,1370,1371,1372,1373,1374]),([0,1,2,3,4,5,227],[0,1,10,11,12,13,32,34,50,89,195,534,535,1357,1375,1376,1377,1378,1379,1380]),([0,1,2,3,4,5,59],[0,1,7,9,11,13,29,31,32,33,34,49,50,90,248,261,1383]),([0,1,2,3,4,5,28,48],[4,6,11,13,22,23,28,31,32,33,34,41,50,90,261,700,706,1381,1382,1384,1385,1386,1387,1388]),([0,1,2,3,4,5,28,51],[4,6,11,13,31,32,33,34,42,43,44,45,50,90,261,711,713,1381,1382,1384,1385,1387,1388]),([0,1,2,3,4,5,28,228],[4,6,11,13,31,32,50,261,1381,1382,1385,1386,1388,1392,1393,1394,1395,1396,1397]),([0,1,2,3,4,5,28,229],[4,6,11,13,31,32,50,261,1381,1382,1385,1386,1388,1404,1405,1406,1407,1408,1409])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_18 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_18 = true := by decide +kernel
def h0Block8_19 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,29,48],[3,6,11,13,22,23,28,31,32,33,34,49,61,90,250,261,700,706,1410,1411,1412,1413,1414,1415,1416,1417]),([0,1,2,3,4,5,29,51],[3,6,11,13,31,32,33,34,42,43,44,45,49,61,90,250,261,711,713,1410,1411,1416,1417,1418,1419]),([0,1,2,3,4,5,27,50],[3,4,6,10,11,12,13,15,20,21,24,27,31,33,41,49,54,706,1287,1288,1412,1420,1421,1422,1423,1424]),([0,1,2,3,4,5,66],[0,1,10,11,12,21,23,26,32,34,38,39,40,41,49,50,253,700,1425]),([0,1,2,3,4,5,27,68],[3,4,6,10,11,12,13,21,24,27,32,33,46,49,54,550,713,1296,1418,1426,1427,1428,1429,1430,1431,1432,1433]),([0,1,2,3,4,5,48,146],[6,10,12,22,23,28,31,32,33,34,50,146,216,261,393,492,706,811,812,1287,1401,1434,1436,1437,1438]),([0,1,2,3,4,5,51,146],[6,10,12,31,32,33,34,42,43,44,45,50,146,216,393,492,713,815,1296,1434,1436,1437,1438]),([0,1,2,3,4,5,30,49],[10,11,12,13,28,31,33,37,50,54,703,812,1089,1092,1096,1098,1099,1440,1441,1442,1443,1447,1448,1449]),([0,1,2,3,4,5,30,50],[10,11,12,13,15,20,31,33,49,54,706,812,1089,1092,1096,1098,1099,1287,1288,1420,1422,1423,1424,1439,1450]),([0,1,2,3,4,5,233],[0,1,10,11,13,22,32,34,49,50,811,812,1097,1099,1287,1451,1452,1453,1454,1455]),([0,1,2,3,4,5,30,67],[10,11,12,13,32,33,44,50,53,54,560,1089,1092,1096,1098,1099,1438,1457,1458,1459,1460,1461,1462,1463,1464,1465]),([0,1,2,3,4,5,73],[0,1,7,11,12,31,32,33,34,49,50,65,70,90,263,1469,1470])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_19 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_19 = true := by decide +kernel
def h0Block8_20 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,48,70],[6,11,12,22,23,28,31,32,33,34,41,50,63,71,90,261,706,811,1466,1467,1468,1471,1472,1473,1474]),([0,1,2,3,4,5,51,70],[6,11,12,31,32,33,34,42,43,44,45,50,63,71,90,261,713,815,1466,1467,1468,1471,1474]),([0,1,2,3,4,5,48,71],[6,11,12,22,23,28,31,32,33,34,49,61,62,90,261,265,269,270,706,811,1414,1475,1476,1477,1478,1479]),([0,1,2,3,4,5,51,71],[6,11,12,31,32,33,34,42,43,44,45,49,61,62,90,261,265,269,270,713,815,1419,1475,1476,1480]),([0,1,2,3,4,5,31,50],[6,10,11,12,13,15,20,31,33,49,54,62,63,66,67,69,72,706,1287,1288,1420,1422,1423,1424,1481,1482]),([0,1,2,3,4,5,75],[0,1,10,11,13,23,32,34,49,50,66,72,73,253,811,1483,1484,1485,1486,1487]),([0,1,2,3,4,5,31,68],[6,10,11,12,13,32,33,49,54,62,63,66,67,69,72,74,713,1296,1426,1427,1429,1430,1431,1432,1433,1488,1489]),([0,1,2,3,4,5,32,49],[10,11,12,13,28,31,33,37,50,54,547,703,1113,1116,1120,1122,1123,1441,1442,1443,1447,1448,1449,1493]),([0,1,2,3,4,5,32,50],[10,11,12,13,15,20,31,33,49,54,547,706,1113,1116,1120,1122,1123,1287,1288,1420,1422,1423,1424,1492,1494]),([0,1,2,3,4,5,234],[0,1,10,11,12,22,32,34,49,50,547,700,1121,1123,1287,1495,1496,1497,1498]),([0,1,2,3,4,5,32,67],[10,11,12,13,32,33,44,50,53,54,547,560,1113,1116,1120,1122,1123,1458,1459,1460,1462,1463,1464,1465,1500,1501]),([0,1,2,3,4,5,41,165],[6,10,12,13,31,32,33,50,72,80,81,86,146,156,158,171,685,1502,1503,1504,1505,1506,1508,1509])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_20 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_20 = true := by decide +kernel
def h0Block8_21 : List NodeSpec := [([0,1,2,3,4,5,42,165],[6,10,12,13,31,32,33,50,91,92,96,146,177,182,184,685,812,1502,1503,1504,1506,1508,1509,1510],[0]),([0,1,2,3,4,5,43,165],[6,10,12,13,31,32,33,50,72,98,99,100,146,191,193,194,685,1502,1503,1504,1506,1508,1509,1511],[0]),([0,1,2,5,37,41,42],[12,13,72,82,83,84,159,161,162,216,687,859,1513],[0]),([0,1,2,3,4,5,235],[0,1,10,11,12,13,34,49,50,72,80,158,687,691,1514,1515,1516,1517],[0]),([0,1,2,3,4,5,37,81],[10,11,12,31,33,34,49,54,90,114,117,177,182,183,685,687,689,690,801,859,862,1222,1518,1519,1520],[0]),([0,1,2,3,4,5,236],[0,1,10,11,12,13,34,49,50,91,182,690,859,862,1521,1522,1523,1524,1525],[0]),([0,1,2,3,4,5,237],[0,1,10,11,12,13,34,49,50,72,98,193,687,690,1527,1528,1529,1530,1531],[0]),([0,1,2,3,4,5,85],[0,1,7,11,12,13,18,31,32,33,34,49,50,97,275,1534,1535],[0,1]),([0,1,2,3,4,5,41,76],[6,11,12,13,31,32,33,50,53,79,80,81,86,156,171,413,1532,1533,1536,1537,1538,1540,1541],[0]),([0,1,2,3,4,5,42,76],[6,11,12,13,31,32,33,50,53,79,91,92,96,177,184,547,1532,1533,1537,1538,1540,1541,1542],[0]),([0,1,2,3,4,5,43,76],[6,11,12,13,31,32,33,41,50,53,79,98,99,100,191,194,1532,1533,1537,1538,1540,1541,1543],[0]),([0,1,2,3,4,5,41,77],[6,11,12,13,31,32,33,49,61,78,80,81,86,156,171,276,279,280,413,551,1544,1545,1546,1547,1550],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_21 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_21 = true := by decide +kernel
def h0Block8_22 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,42,77],[6,11,12,13,31,32,33,49,61,78,91,92,96,177,184,276,279,280,547,554,1544,1547,1550,1551,1552]),([0,1,2,3,4,5,43,77],[6,11,12,13,31,32,33,41,49,61,78,98,99,100,191,194,276,279,280,557,1544,1547,1550,1553,1554]),([0,1,2,3,4,5,38,79],[6,10,11,13,32,33,34,49,54,78,79,85,88,90,93,95,156,158,289,294,343,344,345,347,1555]),([0,1,2,5,38,41,42],[12,13,83,84,85,93,159,162,163,216,413,1556]),([0,1,2,3,4,5,97],[0,1,10,11,12,13,34,49,50,81,85,88,89,95,172,1557,1558,1559]),([0,1,2,3,4,5,38,81],[6,10,11,12,31,33,34,49,54,78,79,85,90,93,94,114,177,182,183,547,801,1222,1519,1520,1560]),([0,1,2,3,4,5,95],[0,1,10,11,12,13,34,49,50,89,92,93,94,547,1561,1562,1563,1564]),([0,1,2,3,4,5,103],[0,1,10,11,12,13,34,41,49,50,85,89,94,99,195,1566,1567,1568,1569]),([0,1,2,3,4,5,89],[0,1,9,10,11,13,25,32,33,34,49,50,54,173,175,176,1572]),([0,1,2,3,4,5,123],[0,10,11,13,32,33,34,50,54,176,289,1574,1575,1576,1577,1578]),([0,1,2,3,4,5,99],[0,1,10,11,12,16,31,33,34,49,50,54,65,186,190,236,1470,1583]),([0,1,2,3,4,5,105],[0,6,10,11,12,31,33,34,50,54,114,236,1584,1585,1586,1587,1588,1589,1590])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_22 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_22 = true := by decide +kernel
def h0Block8_23 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,115],[0,1,9,10,11,13,16,31,33,34,47,49,50,54,196,199,239,1594]),([0,1,2,3,4,5,124],[0,10,11,13,31,33,34,37,50,54,239,261,294,304,1598]),([0,1,2,3,4,5,118],[0,1,10,11,12,18,31,32,33,34,49,50,54,65,208,211,242,1603,1604]),([0,1,2,3,4,5,108],[0,6,10,11,12,31,32,33,50,54,126,242,1607,1608,1609,1610,1611,1612]),([0,1,2,3,4,5,238],[0,1,10,11,13,31,32,33,34,49,50,54,246,1613,1615,1616,1617,1618]),([0,1,2,3,4,5,239],[0,10,11,13,31,32,33,50,54,246,1620,1621,1622,1623,1624,1625])]
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
def h0Block9_0 : List NodeSpec := [([0,1,2,3,4,5,6,27],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,18,21,24,25,26,27,61],[0]),([0,1,2,3,4,5,6,31],[0,1,2,6,7,8,9,10,11,12,13,14,16,18,25,61,62,63,64,65,66,67,68,69,71],[0]),([0,1,2,3,4,5,6,38],[0,1,2,6,7,8,9,10,11,16,25,33,34,53,61,65,78,79,85,93,94,95],[0,1]),([0,1,3,4,5,39],[1,10,103,104],[0,1]),([0,1,3,4,5,40],[1,11,137,138],[0,1]),([0,1,2,3,4,5,6,41],[0,1,2,6,7,9,12,13,14,18,25,31,32,49,65,80,81,86,156,157,158,171,172],[0]),([0,1,2,3,4,5,6,42],[0,1,2,6,7,9,12,13,14,16,18,25,31,32,49,65,71,91,92,96,177,178,182,184,185],[0]),([0,1,2,3,4,5,6,43],[0,1,2,6,7,9,12,13,14,16,18,25,31,32,37,49,65,98,99,100,191,192,193,194,195],[0]),([0,1,2,3,4,5,6,45],[0,1,2,6,7,9,12,13,14,16,25,33,34,49,65,71,125,130,153,201,204,206,207],[0,1]),([0,1,2,3,4,5,6,46],[0,1,2,6,7,9,12,13,14,16,25,33,34,49,53,135,136,155,212,213,214,215,216],[0,1]),([0,2,3,4,5,7,21],[0,1,11,217,219,220,221,222],[0,1]),([0,1,2,3,4,5,7,27],[0,1,3,4,8,10,11,12,13,21,24,26,27,50,61,217,218,220,221,247,248,249,253,254,255,256],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := [([0,1,2,3,4,5,7,31],[0,1,8,10,11,12,13,50,61,62,63,66,67,68,69,217,218,220,221,247,253,254,255,256,262,263,264],[0]),([0,1,2,3,4,5,7,38],[0,1,8,10,11,33,34,50,61,78,79,85,93,94,95,217,218,221,247,254,255,262,275],[0,1]),([0,1,2,3,4,5,7,41],[0,1,12,13,31,32,49,50,80,81,86,156,158,171,172,176,217,218,220,221,247,255,256,262,288],[0]),([0,1,2,3,4,5,7,42],[0,1,12,13,31,32,49,50,91,92,96,177,182,184,185,217,218,220,221,229,236,247,254,255,256,262,299],[0]),([0,1,2,3,4,5,7,43],[0,1,12,13,31,32,49,50,98,99,100,191,193,194,195,217,218,220,221,239,247,254,255,256,262,286,303],[0]),([0,1,2,3,4,5,7,45],[0,1,12,13,33,34,49,50,125,130,153,201,204,206,207,217,218,220,221,229,242,247,253,254,255,256,262],[0]),([0,1,2,3,4,5,7,46],[0,1,12,13,33,34,49,50,135,136,155,212,213,214,215,216,217,218,220,221,246,247,253,254,255],[0]),([0,2,3,4,5,120],[1,11,217,314],[0,1]),([0,1,2,3,4,5,8,41],[1,10,11,12,13,31,32,54,81,86,156,171,172,176,312,313,339,340,341,342,346,349],[0]),([0,1,2,3,4,5,8,42],[1,10,11,12,13,31,32,54,71,92,96,177,184,185,229,236,312,313,341,342,346,349,357,358,359],[0]),([0,1,2,3,4,5,8,43],[1,10,11,12,13,31,32,37,54,99,100,191,194,195,239,312,313,341,342,346,349,359,364,365,366],[0]),([0,1,2,3,4,5,8,45],[1,10,11,12,13,33,34,54,71,125,153,201,206,207,229,242,312,313,341,342,346,349,359,371],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Block9_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,8,46],[1,10,11,12,13,33,34,53,54,135,155,212,214,215,216,246,283,312,313,341,342,359,375]),([0,1,2,3,4,5,9,13],[1,10,11,12,13,217,261,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391]),([0,1,2,3,4,5,9,15],[1,10,11,12,13,217,261,376,379,386,387,390,391,392,393,394,395,396,397,398,399,400]),([0,1,2,3,4,5,9,18],[1,10,11,33,34,217,318,332,376,379,382,386,387,390,391,401,402,403,404,405,406,407,408]),([0,1,2,3,4,5,9,41],[1,6,10,11,12,13,31,32,50,72,80,81,86,156,158,171,172,176,376,379,382,386,390,391,414,415]),([0,1,2,3,4,5,9,42],[1,6,10,11,12,13,31,32,50,91,92,96,177,182,184,185,236,318,376,379,382,386,387,390,391,428,429]),([0,1,2,3,4,5,9,43],[1,6,10,11,12,13,31,32,50,72,98,99,100,191,193,194,195,239,332,376,379,382,386,387,390,391,437,438]),([0,1,2,3,4,5,9,45],[1,6,10,11,12,13,33,34,50,125,130,153,201,204,206,207,242,261,376,379,382,386,387,390,391,446]),([0,1,2,3,4,5,9,46],[1,6,10,11,12,13,33,34,50,72,135,136,155,212,213,214,215,216,246,261,376,379,386,387,390,454]),([0,1,2,3,4,5,10,41],[1,10,11,12,13,31,32,54,72,73,80,81,86,156,171,172,176,455,456,457,458,459,460,463,464]),([0,1,2,3,4,5,10,42],[1,10,11,12,13,31,32,54,71,91,92,96,177,184,185,229,236,455,456,459,460,463,464,469,470,471]),([0,1,2,3,4,5,10,43],[1,10,11,12,13,31,32,37,54,98,99,100,191,194,195,239,366,455,456,459,460,463,464,471,477,478])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
def h0Block9_3 : List NodeSpec := [([0,1,2,3,4,5,10,45],[1,10,11,12,13,33,34,54,71,125,130,153,201,206,207,229,242,455,456,459,460,463,464,471,484],[0]),([0,1,2,3,4,5,10,46],[1,10,11,12,13,33,34,54,135,136,155,212,214,215,216,246,283,455,456,459,460,471,489],[0]),([0,1,2,3,4,5,11,13],[1,10,11,12,13,217,261,378,381,383,384,385,388,389,490,491,492,493,494,495,496,497,498],[0]),([0,1,2,3,4,5,11,15],[1,10,11,12,13,217,261,393,395,396,397,398,399,400,490,492,495,496,497,498,499,500],[0]),([0,1,2,3,4,5,11,18],[1,10,11,33,34,217,318,402,403,404,405,406,407,408,490,492,494,495,496,497,498,501],[0]),([0,1,2,3,4,5,11,22],[0,1,6,10,11,12,13,61,217,490,492,495,496,497,498,502,503,504,505,506,507,508,509,510],[0]),([0,1,2,3,4,5,11,23],[0,1,6,10,11,12,13,61,217,490,492,494,495,496,497,498,506,516,517,518,519,520,521,522,523],[0]),([0,1,2,3,4,5,11,26],[0,1,6,10,11,33,34,61,217,318,490,492,494,495,496,497,498,530,531,532,533,534,535,536],[0]),([0,1,2,3,4,5,113],[0,1,10,11,12,13,14,31,32,33,34,49,61,90,137,217,542],[0,1]),([0,1,2,3,4,5,11,41],[1,6,10,11,12,13,31,32,50,80,81,86,146,156,171,172,176,318,490,492,494,495,497,498,565,566],[0]),([0,1,2,3,4,5,11,42],[1,6,10,11,12,13,31,32,50,91,92,96,146,177,184,185,236,318,490,492,494,495,496,497,498,547,576,577],[0]),([0,1,2,3,4,5,11,43],[1,6,10,11,12,13,31,32,41,50,98,99,100,146,191,194,195,239,318,490,492,494,495,496,497,498,585,586],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
def h0Block9_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,11,45],[1,6,10,11,12,13,33,34,50,125,130,146,153,201,206,207,242,261,490,492,494,495,496,497,498,506,547,594]),([0,1,2,3,4,5,11,46],[1,6,10,11,12,13,33,34,50,135,136,146,155,212,214,215,216,246,261,490,492,495,496,497,506,601]),([0,1,2,3,4,5,12,33],[1,10,11,12,13,31,32,602,603,604,605,606,607,608,610,612,613,614,615,623,635]),([0,1,2,3,4,5,12,34],[1,10,11,12,13,31,32,146,602,603,608,610,612,614,639,640,641,642,643,644,645,646,647,652]),([0,1,2,3,4,5,12,35],[1,10,11,12,13,31,32,37,366,602,603,608,610,612,614,644,657,658,659,660,661,662,663,666]),([0,1,2,3,4,5,12,36],[1,10,11,12,13,31,32,146,602,603,608,610,612,614,646,671,672,673,674,675,676,677,680]),([0,1,2,3,4,5,12,37],[1,10,11,12,13,33,34,146,602,603,608,610,614,644,646,685,686,687,688,689,690,691]),([0,1,2,3,4,5,12,38],[1,10,11,12,13,33,34,53,78,79,85,94,95,275,283,602,603,608,612,614,644,695]),([0,1,2,3,4,5,12,48],[1,12,13,22,23,28,31,32,33,34,37,366,602,603,608,610,612,614,644,699,700,701,706]),([0,1,2,3,4,5,12,51],[1,12,13,31,32,33,34,42,43,44,45,53,283,602,603,608,610,614,710,711,712,713]),([0,1,2,3,4,158],[1,13,33,217,603,627]),([0,1,2,3,4,5,13,16],[1,12,13,31,32,54,217,378,381,383,384,385,388,389,714,715,716,717,718,719,720,721,722])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
def h0Block9_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,13,17],[1,12,13,31,32,54,217,378,381,383,384,388,389,723,724,725,726,727,728,729,730,731]),([0,1,2,3,4,5,13,18],[1,12,13,33,34,54,217,378,381,383,384,385,388,389,402,403,404,405,406,407,408,732]),([0,1,2,3,4,5,13,20],[0,1,8,10,11,12,13,217,378,383,384,385,388,389,506,733,734,735,740,741,744,745,746,747]),([0,1,2,3,4,5,13,21],[0,1,6,10,11,12,13,61,217,219,378,381,383,384,385,388,389,506,748,749,750,751,752,753,754]),([0,1,2,3,4,5,13,24],[0,1,6,12,13,31,32,217,378,381,383,384,388,389,506,740,755,756,757,761,762,763,764,765]),([0,1,2,3,4,5,13,25],[0,1,6,12,13,31,32,217,378,381,383,384,385,388,389,506,740,772,773,774,775,776,777,778,779]),([0,1,2,3,4,5,13,26],[0,1,6,12,13,33,34,216,217,253,378,381,383,384,385,388,389,530,531,532,533,534,535,536,740]),([0,1,2,3,4,5,130],[0,1,10,11,12,13,31,32,33,34,49,217,383,740,743,793,794,801]),([0,1,2,3,4,5,13,33],[1,6,10,11,12,13,31,32,50,54,253,378,381,383,384,388,389,604,606,613,615,623,635,797,816,817]),([0,1,2,3,4,5,13,34],[1,10,11,12,13,31,32,50,54,378,381,383,384,385,388,389,639,641,643,645,647,652,740,824,825,826]),([0,1,2,3,4,5,13,35],[1,6,10,11,12,13,31,32,50,54,253,378,381,383,384,385,388,389,657,659,661,662,663,666,804,837,838]),([0,1,2,3,4,5,13,36],[1,10,11,12,13,31,32,41,50,54,286,378,381,383,384,388,389,671,673,675,676,677,680,740,846,847,848])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
def h0Block9_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,13,37],[1,10,11,12,13,33,34,50,54,216,378,381,383,384,385,388,685,687,688,689,690,691,740,858,859,862]),([0,1,2,3,4,5,13,38],[1,6,10,11,12,13,33,34,50,54,78,79,85,93,94,95,216,275,378,383,384,385,388,389,506,869]),([0,1,2,3,4,5,13,48],[1,6,12,13,22,23,28,31,32,33,34,50,216,261,378,381,383,384,385,388,389,506,700,701,706,811,812,875]),([0,1,2,3,4,5,13,51],[1,6,12,13,31,32,33,34,42,43,44,45,50,216,261,378,381,383,384,388,506,711,712,713,815,882]),([0,1,2,3,4,5,14,33],[1,10,11,12,13,31,32,547,604,606,613,615,623,635,797,883,884,885,886,888,889,890,891]),([0,1,2,3,4,5,14,34],[1,10,11,12,13,31,32,146,639,641,643,645,647,652,826,883,884,888,889,890,891,898,899,900,901]),([0,1,2,3,4,5,14,35],[1,10,11,12,13,31,32,37,366,657,659,661,662,663,666,804,883,884,888,889,890,891,900,907,908]),([0,1,2,3,4,5,14,36],[1,10,11,12,13,31,32,146,671,673,675,676,677,680,848,883,884,888,889,890,891,901,914,915]),([0,1,2,3,4,5,14,37],[1,10,11,12,13,33,34,146,216,685,687,688,689,690,691,859,883,884,888,889,891,900,901,920]),([0,1,2,3,4,5,14,38],[1,10,11,12,13,33,34,53,78,79,85,93,94,95,216,275,283,883,884,888,890,891,900,925]),([0,1,2,3,4,5,14,48],[1,12,13,22,23,28,31,32,33,34,37,216,366,700,701,706,811,883,884,888,889,890,891,900,929]),([0,1,2,3,4,5,14,51],[1,12,13,31,32,33,34,42,43,44,45,53,216,283,711,712,713,815,883,884,888,889,891,934])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_6 = true := by decide +kernel
def h0Block9_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,15,17],[1,12,13,31,32,54,217,393,395,396,397,399,400,724,726,727,728,729,730,731,935,936]),([0,1,2,3,4,5,15,18],[1,12,13,33,34,54,217,393,395,396,397,398,399,400,402,403,404,405,406,407,408,937]),([0,1,2,3,4,5,15,20],[0,1,8,10,11,12,13,217,393,396,397,398,399,400,506,733,734,741,744,745,746,747,938,939]),([0,1,2,3,4,5,15,21],[0,1,6,10,11,12,13,61,217,219,393,395,396,397,398,399,400,506,748,750,751,752,753,754,940]),([0,1,2,3,4,5,15,24],[0,1,6,12,13,31,32,217,393,395,396,397,399,400,506,755,756,761,762,763,764,765,939,941]),([0,1,2,3,4,5,15,25],[0,1,6,12,13,31,32,217,393,395,396,397,398,399,400,506,772,773,775,776,777,778,779,939,948]),([0,1,2,3,4,5,15,26],[0,1,6,12,13,33,34,217,253,393,395,396,397,398,399,400,530,531,532,533,534,535,536,939]),([0,1,2,3,4,5,131],[0,1,10,11,12,13,31,32,33,34,49,217,294,396,939,962,963,964]),([0,1,2,3,4,5,15,33],[1,6,10,11,12,13,31,32,50,54,253,393,395,396,397,399,400,604,606,613,615,623,635,797,981,982]),([0,1,2,3,4,5,15,34],[1,10,11,12,13,31,32,50,54,71,72,73,393,395,396,397,398,399,400,639,641,643,645,647,652,826,939,989,990]),([0,1,2,3,4,5,15,35],[1,6,10,11,12,13,31,32,50,54,253,393,395,396,397,398,399,400,657,659,661,662,663,666,804,998,999]),([0,1,2,3,4,5,15,36],[1,10,11,12,13,31,32,50,54,71,72,73,393,395,396,397,399,400,671,673,675,676,677,680,848,939,1007,1008])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_7 = true := by decide +kernel
def h0Block9_8 : List NodeSpec := [([0,1,2,3,4,5,15,37],[1,10,11,12,13,33,34,50,54,71,72,73,393,395,396,397,398,399,685,687,688,689,690,691,859,939,1015],[0]),([0,1,2,3,4,5,15,38],[1,6,10,11,12,13,33,34,50,54,78,79,85,93,94,95,275,393,396,397,398,399,400,506,1022],[0]),([0,1,2,3,4,5,15,48],[1,6,12,13,22,23,28,31,32,33,34,50,71,261,393,395,396,397,398,399,400,506,700,701,706,811,978,1028],[0]),([0,1,2,3,4,5,15,51],[1,6,12,13,31,32,33,34,42,43,44,45,50,71,261,393,395,396,397,399,506,711,712,713,815,1038],[0]),([0,1,2,3,4,5,18,20],[0,1,8,10,11,33,34,217,318,402,404,405,406,407,408,733,734,741,744,745,746,747,1042],[0]),([0,1,2,3,4,5,18,21],[0,1,6,10,11,33,34,61,217,219,318,332,402,403,404,405,406,407,408,748,750,751,752,753,754],[0]),([0,1,2,3,4,5,18,22],[0,1,6,12,13,33,34,217,318,402,403,404,405,407,408,502,503,505,507,508,509,510,1042],[0]),([0,1,2,3,4,5,18,23],[0,1,6,12,13,33,34,216,217,318,402,403,404,405,406,407,408,516,517,519,520,521,522,523,1042],[0]),([0,1,2,3,4,5,132],[0,1,10,11,12,13,31,32,33,34,49,217,404,1042,1059,1060,1066],[0,1]),([0,1,2,3,4,5,18,27],[1,3,4,6,10,11,12,13,21,24,26,27,33,34,50,54,248,332,402,403,404,405,407,408,1083],[0]),([0,1,2,3,4,5,18,30],[1,10,11,12,13,33,34,50,54,216,402,403,404,405,406,407,408,812,1042,1089,1090,1091,1092,1096,1097,1098,1099],[0]),([0,1,2,3,4,5,18,31],[1,6,10,11,12,13,33,34,50,54,62,63,66,67,68,69,216,263,332,402,403,404,405,406,407,408,1106],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_8 = true := by decide +kernel
def h0Block9_9 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,18,32],[1,10,11,12,13,33,34,50,54,402,403,404,405,407,408,413,547,1042,1113,1114,1115,1116,1120,1121,1122,1123]),([0,1,2,3,4,5,18,41],[1,6,12,13,31,32,33,34,50,80,81,86,156,171,172,176,318,402,403,404,405,406,407,413,1129]),([0,1,2,3,4,5,18,42],[1,6,12,13,31,32,33,34,50,91,92,96,177,184,185,216,236,318,402,403,404,405,406,407,408,812,1139]),([0,1,2,3,4,5,18,43],[1,6,12,13,31,32,33,34,45,50,98,99,100,191,194,195,239,318,332,402,403,404,405,406,407,408,413,1145]),([0,1,2,3,4,5,19,27],[1,3,4,10,11,12,13,21,24,26,27,33,34,248,261,506,550,1152,1153,1154,1155,1156,1157,1158]),([0,1,2,3,4,5,19,30],[1,10,11,12,13,33,34,146,216,1089,1091,1092,1096,1097,1098,1099,1152,1154,1155,1156,1157,1158,1162,1163,1164]),([0,1,2,3,4,5,19,31],[1,10,11,12,13,33,34,62,63,66,67,68,69,71,216,229,263,1152,1154,1155,1156,1157,1158,1163,1169]),([0,1,2,3,4,5,19,32],[1,10,11,12,13,33,34,146,1113,1115,1116,1120,1121,1122,1123,1152,1154,1155,1156,1157,1158,1164,1174]),([0,1,2,3,4,5,19,41],[1,12,13,31,32,33,34,80,81,86,156,171,172,176,261,413,506,1152,1154,1155,1156,1158,1163,1178]),([0,1,2,3,4,5,19,42],[1,12,13,31,32,33,34,71,91,92,96,177,184,185,216,229,236,1152,1154,1155,1156,1157,1158,1163,1183]),([0,1,2,3,4,5,19,43],[1,12,13,31,32,33,34,37,45,98,99,100,191,194,195,239,366,1152,1154,1155,1156,1157,1158,1163,1188]),([0,1,2,3,4,5,20,41],[0,6,8,10,11,12,13,31,32,49,81,86,156,158,171,172,176,318,733,734,741,744,746,747,1193])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_9 = true := by decide +kernel
def h0Block9_10 : List NodeSpec := [([0,1,2,3,4,5,20,42],[0,6,8,10,11,12,13,31,32,49,92,96,177,182,184,185,236,318,733,734,741,744,745,746,747,1195],[0]),([0,1,2,3,4,5,20,43],[0,6,8,10,11,12,13,31,32,49,99,100,191,193,194,195,239,318,733,734,741,744,745,746,747,1196],[0]),([0,1,2,3,4,5,20,45],[0,6,8,10,11,12,13,33,34,49,125,153,201,204,206,207,242,506,733,734,741,744,745,746,747],[0]),([0,1,2,3,4,5,20,46],[0,6,8,10,11,12,13,33,34,49,135,155,212,213,214,215,246,506,733,734,744,745,746],[0]),([0,1,2,3,4,5,119],[0,1,10,11,12,13,31,32,33,34,50,61,217,219,1197,1198,1199],[0,1]),([0,1,2,3,4,5,21,41],[0,6,10,11,12,13,31,32,49,61,72,80,81,86,156,171,172,176,219,748,750,751,753,754,1217],[0]),([0,1,2,3,4,5,21,42],[0,6,10,11,12,13,31,32,49,61,91,92,96,177,184,185,219,236,318,748,750,751,752,753,754,1221],[0]),([0,1,2,3,4,5,21,43],[0,6,10,11,12,13,31,32,49,61,72,98,99,100,191,194,195,219,239,332,748,750,751,752,753,754,1229],[0]),([0,1,2,3,4,5,21,45],[0,6,10,11,12,13,33,34,49,61,125,130,153,201,206,207,219,242,506,748,750,751,752,753,754],[0]),([0,1,2,3,4,5,21,46],[0,6,10,11,12,13,33,34,49,61,135,136,155,212,214,215,216,219,246,506,748,751,752,753],[0]),([0,1,2,3,4,5,147],[0,1,10,11,12,13,31,32,33,34,50,54,217,261,502,1237,1238,1239],[0]),([0,1,2,3,4,5,22,33],[0,6,8,10,11,12,13,31,32,54,61,318,502,503,505,508,509,510,604,606,613,615,623,635,801,1267],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_10 = true := by decide +kernel
def h0Block9_11 : List NodeSpec := [([0,1,2,3,4,5,22,35],[0,6,8,10,11,12,13,31,32,54,61,318,502,503,505,507,508,509,510,657,659,661,662,663,666,801,1272],[0]),([0,1,2,3,4,5,22,38],[0,6,8,10,11,12,13,33,34,54,61,78,79,85,94,95,275,502,503,506,507,508,509,801],[0]),([0,1,2,3,4,5,22,48],[0,6,12,13,22,23,28,31,32,33,34,49,502,503,505,506,507,508,509,510,700,701,706,801,978,1287],[0]),([0,1,2,3,4,5,22,51],[0,6,12,13,31,32,33,34,42,43,44,45,49,502,503,505,506,508,509,711,712,713,801,1296],[0]),([0,1,2,3,4,5,149],[0,1,10,11,12,13,31,32,33,34,50,54,71,217,516,1297,1298,1299,1300],[0]),([0,1,2,3,4,5,23,33],[0,6,8,10,11,12,13,31,32,54,61,294,318,516,517,519,521,522,523,604,606,613,615,623,635,797,1310],[0]),([0,1,2,3,4,5,23,35],[0,6,8,10,11,12,13,31,32,54,61,294,318,516,517,519,520,521,522,523,657,659,661,662,663,666,804,1316],[0]),([0,1,2,3,4,5,23,38],[0,6,8,10,11,12,13,33,34,54,61,78,79,85,93,94,95,216,275,506,516,517,520,521,522],[0]),([0,1,2,3,4,5,23,48],[0,6,12,13,22,23,28,31,32,33,34,49,216,506,516,517,519,520,521,522,523,700,701,706,811,812,1287],[0]),([0,1,2,3,4,5,23,51],[0,6,12,13,31,32,33,34,42,43,44,45,49,216,506,516,517,519,521,522,711,712,713,815,1296],[0]),([0,1,2,3,4,5,151],[0,10,11,12,13,31,32,33,34,50,53,54,217,530,1333,1334,1335],[0,1]),([0,1,2,3,4,5,26,27],[0,3,4,6,8,10,11,12,13,21,24,26,27,33,34,54,61,248,253,530,531,532,534,535,536,1357],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_11 = true := by decide +kernel
def h0Block9_12 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,26,31],[0,6,8,10,11,12,13,33,34,54,61,62,63,66,67,68,69,253,263,530,531,532,533,534,535,536,1357]),([0,1,2,3,4,5,26,41],[0,6,12,13,31,32,33,34,49,80,81,86,156,158,171,172,176,318,413,530,531,532,533,534,536,1357]),([0,1,2,3,4,5,26,42],[0,6,12,13,31,32,33,34,49,91,92,96,177,182,184,185,216,236,318,530,531,532,533,534,535,536,1357]),([0,1,2,3,4,5,26,43],[0,6,12,13,31,32,33,34,45,49,98,99,100,191,193,194,195,239,318,530,531,532,533,534,535,536,1357]),([0,1,2,3,4,5,28],[0,1,4,6,10,11,13,31,32,33,34,50,248,261,1381,1382,1384]),([0,1,2,3,4,5,29],[0,1,3,6,10,11,13,31,32,33,34,49,61,248,1410,1411]),([0,1,2,3,4,5,27,48],[3,4,10,11,12,13,21,22,23,24,26,27,28,31,32,33,34,41,54,253,700,706,1412]),([0,1,2,3,4,5,27,51],[3,4,10,11,12,13,24,27,31,32,33,34,42,43,44,45,54,253,550,711,713,1418]),([0,1,2,3,4,5,146],[0,1,8,10,11,12,31,32,33,34,50,146,216,393,492,1434,1435]),([0,1,2,3,4,5,30,48],[10,11,12,13,22,23,28,31,32,33,34,216,700,706,811,812,1089,1092,1096,1097,1098,1099,1287,1439]),([0,1,2,3,4,5,30,51],[10,11,12,13,31,32,33,34,42,43,44,45,216,560,711,713,815,1089,1092,1096,1098,1296,1456]),([0,1,2,3,4,5,70],[0,1,6,10,11,12,31,32,33,34,50,63,71,263,1466,1467,1468,1471])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_12 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_12 = true := by decide +kernel
def h0Block9_13 : List NodeSpec := [([0,1,2,3,4,5,71],[0,1,6,10,11,12,31,32,33,34,49,61,62,263,270,1475,1476],[0,1]),([0,1,2,3,4,5,31,48],[10,11,12,13,22,23,28,31,32,33,34,41,54,62,63,66,67,68,69,216,253,700,706,811,1481],[0]),([0,1,2,3,4,5,31,51],[10,11,12,13,31,32,33,34,42,43,44,45,54,62,63,67,69,216,253,711,713,815,1488],[0]),([0,1,2,3,4,5,145],[0,1,8,10,11,13,31,32,33,34,50,146,261,318,378,1490,1491],[0]),([0,1,2,3,4,5,32,48],[10,11,12,13,22,23,28,31,32,33,34,318,547,700,706,978,1113,1116,1120,1121,1122,1123,1287,1492],[0]),([0,1,2,3,4,5,32,51],[10,11,12,13,31,32,33,34,42,43,44,45,318,547,560,711,713,1113,1116,1120,1122,1296,1499],[0]),([0,1,2,3,4,5,165],[0,1,8,10,11,12,13,31,32,34,50,146,685,688,1502,1503,1504],[0,1]),([0,1,2,3,4,5,37,41],[10,11,12,13,31,32,33,34,72,73,80,81,86,156,158,171,253,685,687,689,691,859,1512],[0]),([0,1,2,3,4,5,37,42],[10,11,12,13,31,32,33,34,91,92,96,177,182,184,216,253,685,687,689,690,691,859,862,1518],[0]),([0,1,2,3,4,5,37,43],[10,11,12,13,31,32,33,34,45,72,73,98,99,100,191,193,194,253,685,687,689,690,691,859,1526],[0]),([0,1,2,3,4,5,76],[0,1,6,10,11,12,13,31,32,34,50,53,79,275,1532,1533],[0,1]),([0,1,2,3,4,5,77],[0,1,6,10,11,12,13,31,32,34,49,61,78,275,1544],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_13 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_13 = true := by decide +kernel
def h0Block9_14 : List NodeSpec := [([0,1,2,3,4,5,38,41],[10,11,12,13,31,32,33,34,54,78,79,81,85,86,88,93,95,156,171,172,413,1555],[0]),([0,1,2,3,4,5,38,42],[10,11,12,13,31,32,33,34,54,78,79,85,92,93,94,95,96,177,184,185,216,547,1560],[0]),([0,1,2,3,4,5,38,43],[10,11,12,13,31,32,33,34,41,45,54,78,79,85,93,94,95,99,100,102,191,194,195,1565],[0]),([0,1,2,3,4,5,78],[0,1,6,10,11,12,13,32,33,34,50,54,86,176,253,261,1570,1571,1573],[0]),([0,1,2,3,4,5,79],[0,1,6,10,11,12,13,32,33,34,49,156,158,176,294,344,347],[0]),([0,1,2,5,41,42],[12,13,159,162],[0]),([0,1,2,3,4,5,80],[0,1,6,10,11,12,13,31,33,34,50,54,71,96,236,253,1579,1580,1581,1582],[0]),([0,1,2,3,4,5,81],[0,1,6,10,11,12,13,31,33,34,49,177,182,183,236,801,1519,1520],[0]),([0,1,2,3,4,5,100],[0,1,6,10,11,12,13,31,33,34,37,50,54,100,239,253,1591,1592,1593,1595],[0]),([0,1,2,3,4,5,101],[0,1,6,10,11,12,13,31,33,34,49,102,191,193,239,294,1596,1597,1599],[0]),([0,1,2,3,4,5,106],[0,1,6,10,11,12,13,31,32,34,50,54,71,125,242,1600,1601,1602],[0,1]),([0,1,2,3,4,5,107],[0,1,6,10,11,12,13,31,32,34,49,201,204,242,801,1605,1606],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_14 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_14 = true := by decide +kernel
def h0Block9_15 : List NodeSpec := [([0,1,2,3,4,5,111],[0,1,6,10,11,12,13,31,32,34,50,54,135,216,246,1613,1614],[0,1]),([0,1,2,3,4,5,112],[0,1,6,10,11,12,13,31,32,34,49,212,213,216,246,1619],[0,1])]
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
def h0Block10_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,8,10,11,12,13,31,32,33,34],[0,1]),([0,1,2,3,4,5,7],[0,1,8,10,11,12,13,31,32,33,34,217,218],[0,1]),([0,1,2,3,4,5,8],[0,1,11,12,13,31,32,33,34,217,312,313],[0,1]),([0,1,2,3,4,5,9],[0,1,8,10,11,12,13,31,32,33,34,217,376,390],[0,1]),([0,1,2,3,4,5,10],[0,1,10,11,12,13,31,32,33,34,217,455,456],[0,1]),([0,1,2,3,4,5,11],[0,1,10,11,12,13,31,32,33,34,217,490,497],[0,1]),([0,1,2,3,4,5,12],[0,1,10,11,13,31,32,33,34,217,602,603],[0]),([0,1,2,3,4,5,13],[0,1,10,11,12,13,31,32,33,34,217,383,388],[0]),([0,1,2,3,4,5,14],[0,1,10,11,12,13,31,32,33,34,217,883,884],[0]),([0,1,2,3,4,5,15],[0,1,10,11,12,13,31,32,33,34,217,396,399],[0,1]),([0,1,2,3,4,5,18],[0,1,10,11,12,13,31,32,33,34,217,404],[0,1]),([0,1,2,3,4,5,19],[0,1,10,11,12,13,31,32,33,34,217,1152],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Block10_1 : List NodeSpec := [([0,1,2,3,4,5,20],[0,1,8,11,12,13,31,32,33,34,217,746],[0,1]),([0,1,2,3,4,5,21],[0,1,10,11,12,13,31,32,33,34,217,753],[0,1]),([0,1,2,3,4,5,22],[0,1,8,10,11,13,31,32,33,34,217,509],[0,1]),([0,1,2,3,4,5,23],[0,1,8,10,11,12,13,31,32,33,34,217,522],[0,1]),([0,1,2,3,4,5,26],[0,1,8,10,11,12,13,31,32,33,34,217],[0,1]),([0,1,2,3,4,5,27],[0,1,3,10,11,13,27,31,32,33,34],[0,1]),([0,1,2,3,4,5,30],[0,1,8,10,11,12,13,31,32,33,34,1092,1096],[0,1]),([0,1,2,3,4,5,31],[0,1,10,11,12,13,31,32,33,34,62,69],[0,1]),([0,1,2,3,4,5,32],[0,1,8,10,11,13,31,32,33,34,1116,1120],[0,1]),([0,1,2,3,4,5,37],[0,1,8,10,11,12,13,31,32,34,689],[0,1]),([0,1,2,3,4,5,38],[0,1,11,12,13,31,32,33,34,78],[0,1]),([0,1,2,3,4,5,41],[0,1,10,11,12,13,32,33,34,156,171],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_1 = true := by decide +kernel
def h0Block10_2 : List NodeSpec := [([0,1,2,3,4,5,42],[0,1,10,11,12,13,31,32,33,34,177,184],[0]),([0,1,2,3,4,5,43],[0,1,10,11,12,13,31,32,33,34,191,194],[0]),([0,1,2,3,4,5,45],[0,1,10,11,12,13,31,32,33,34,201],[0,1]),([0,1,2,3,4,5,46],[0,1,10,11,13,31,32,34,212],[0,1])]
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
def h0Block11_0 : List NodeSpec := [([0,1,2,3,4,5],[0,34],[0,1])]
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
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 10]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 13]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4008241320 * 2 ^ 32 + 3936921600) ||| ((4008241320 * 2 ^ 32 + 3936921600) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4008241320 * 2 ^ 32 + 3936921600) ||| ((4008241320 * 2 ^ 32 + 3936921600) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_47471
theorem PEqualNP.Outside.L_meta_47471 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241320 * 2 ^ 32 + 3936921600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241320 * 2 ^ 32 + 3936921600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_47471.table2_of_lower (4008241320 * 2 ^ 32 + 3936921600) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_47471.low_root
    PEqualNP.Outside.L_meta_47471.wit PEqualNP.Outside.L_meta_47471.wo (by decide)
    PEqualNP.Outside.L_meta_47471.wit_mono PEqualNP.Outside.L_meta_47471.wit_eval s hcs
