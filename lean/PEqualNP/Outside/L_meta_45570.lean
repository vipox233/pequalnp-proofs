import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45570
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 64
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
lemma bin_lt (d a b : Nat) (ha : a < 2^64) (hb : b < 2^64) : bin d a b < 2^64 := by
  have h1 : ∀ x y : Nat, x < 2^64 → y < 2^64 → (x &&& y) < 2^64 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^64 → y < 2^64 → (x ||| y) < 2^64 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^64 → y < 2^64 → (x ^^^ y) < 2^64 := fun x y hx hy =>
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
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^64 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^64 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^64 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^64 ∧ (w.getD i swZero).2.testBit 0 = false := by
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
    (hw : ∀ u ∈ w, u.2 < 2^64 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^64 ∧ u.2.testBit 0 = false := by
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
lemma normPack_lt (f : Wire) : normPack f < 2^64 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).isLt
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 64 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 64 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^64) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 64
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 64
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 64 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 64
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
set_option maxRecDepth 4000 in
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
      have ha1 : simple w (normPack a) := (avail_normPack ha).imp id (fun hm => hreps.symm ▸ hm)
      have hb1 : simple w (normPack b) := (avail_normPack hb).imp id (fun hm => hreps.symm ▸ hm)
      exact made_priced w d (false, normPack a) (false, normPack b) hd ha1 hb1
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
    (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^64 ∧ a.testBit 0 = false)
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
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false) :
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
def makePoolAux (d : Nat) (pool pm : List Nat) : List Choice → Option (List Nat × List Nat)
  | [] => some (pool, pm)
  | c :: cs =>
    if choiceOK d pm c then
      let v := choiceVal c
      makePoolAux d (v :: pool) ((v &&& d) :: pm) cs
    else none
lemma makePoolAux_eq (d : Nat) (pool : List Nat) (cs : List Choice) :
    makePoolAux d pool (pool.map (· &&& d)) cs = (makePool d pool cs).map (fun p => (p, p.map (· &&& d))) := by
  induction cs generalizing pool with
  | nil => rfl
  | cons c cs ih =>
    unfold makePoolAux makePool
    split
    · exact ih (choiceVal c :: pool)
    · rfl
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
lemma availM_sub {d a : Nat} {pm1 pm2 : List Nat} (hsub : ∀ m ∈ pm1, m ∈ pm2)
    (ok : availM d pm1 a = true) : availM d pm2 a = true := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok ⊢
  rcases ok with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr (hsub _ h))
  · exact Or.inr (hsub _ h)
def cleanPM (d : Nat) : List Nat → List Nat
  | [] => []
  | m :: ms =>
    let r := cleanPM d ms
    if m == 0 || m == d || r.contains m || r.contains (d ^^^ m) then r else m :: r
lemma cleanPM_sub (d : Nat) (l : List Nat) : ∀ m ∈ cleanPM d l, m ∈ l := by
  induction l with
  | nil => intro m hm; simp [cleanPM] at hm
  | cons x xs ih =>
    intro m hm; unfold cleanPM at hm; dsimp only at hm
    split at hm
    · exact List.mem_cons_of_mem x (ih m hm)
    · rcases List.mem_cons.mp hm with rfl | hm'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem x (ih m hm')
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  (∀ m ∈ c.pm, m ∈ c.wires.map (· &&& c.dom)) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePoolAux d raw (raw.map (· &&& d)) cs).map fun p => ⟨d, lb, cs.length, p.1, cleanPM d p.2⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  rw [makePoolAux_eq] at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨cleanPM_sub d _, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
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
    · exact availM_sound dom hs (availM_sub hpm hav)
    · exact availM_sound dom hs (availM_sub hpm (cut.1.2 a ha))
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      simp only [choiceOK, Bool.and_eq_true] at h2 ⊢
      exact ⟨⟨h2.1.1, availM_sub hpm h2.1.2⟩, availM_sub hpm h2.2⟩
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (availM_sub hpm (cut.1.2 a ha))
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (63 ^^^ z)) ||| o) % 64, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^64 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 64
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 64
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 64 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^64) (hb : b < 2^64) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 64
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 64 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^64) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^64 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^64 := hS a (by simp)
    have hblt : b < 2^64 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^64 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^64 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^64 := by
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
    (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^64 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^64) (hGb0 : G.testBit 0 = false)
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
    (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^64 ∧ a.testBit 0 = false)
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
  | 0 => 0xaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000
  | 5 => 0xffffffff00000000
  | _ => 0
def ALL64 : Nat := 0xffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 64, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL64 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 6) (hj : j < 6) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 6) (w : Nat) (hw : w < 2^64) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 6 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL64 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL64 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
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
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 6) (w : Nat) : swapWord i j w < 2^64 := by
  have hi : i < 6 := by omega
  have h1 : (ALL64 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^64 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^64 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^64 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL64 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^64 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^64 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^64 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^64 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^64 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 6) (w : Nat) (hw : w < 2^64) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 64
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 6)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^64) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 64
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^64 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 64
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
    (hT : T < 2^64) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^64) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^64 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^64 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 64
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
  (List.range 6).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 64).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 64).foldr (fun r acc =>
    let fr := ((r &&& (63 ^^^ z)) ||| o) % 64
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
  by_cases hr : r < 64
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 64) (ho : o < 64) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 64 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h63 : ((r.val &&& (63 ^^^ z)) ||| o) < 64 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (63 ^^^ z)) < 64 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 6) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (63 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h63
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 6
    · have h7 : (63 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 64) && decide (s < 64) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL64 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL64]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 64 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^64) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^64 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^64) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^64 ∧ a.testBit 0 = false := by
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
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^64)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^64 := by
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
lemma var_testBit (i : Fin 6) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by revert i r; decide +kernel
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
inductive btAll {α : Type} (P : α → Prop) : BT α → Prop where
  | empty : btAll P .empty
  | leaf {x : α} : P x → btAll P (.leaf x)
  | node {l r : BT α} : btAll P l → btAll P r → btAll P (.node l r)
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction ht generalizing i with
  | empty => exact hd
  | leaf hx => exact hx
  | node _ _ ihl ihr =>
    unfold btGet
    split
    · exact ihl _
    · exact ihr _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact .leaf hv
  | succ d ih =>
    cases ht with
    | empty =>
      unfold btSet; split
      · exact .node (ih .empty) .empty
      · exact .node .empty (ih .empty)
    | leaf hx =>
      unfold btSet; split
      · exact .node (ih (.leaf hx)) .empty
      · exact .node .empty (ih (.leaf hx))
    | node hl hr =>
      unfold btSet; split
      · exact .node (ih hl) hr
      · exact .node hl (ih hr)
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases ht with
    | leaf hx => exact .leaf (hf _ hx)
    | empty => exact .leaf (hf d0 hd0)
    | node _ _ => exact .leaf (hf d0 hd0)
  | succ d ih =>
    cases ht with
    | empty =>
      unfold btUpdate; split
      · exact .node (ih .empty) .empty
      · exact .node .empty (ih .empty)
    | leaf hx =>
      unfold btUpdate; split
      · exact .node (ih (.leaf hx)) .empty
      · exact .node .empty (ih (.leaf hx))
    | node hl hr =>
      unfold btUpdate; split
      · exact .node (ih hl) hr
      · exact .node hl (ih hr)
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
  exact hgo l (0, BT.empty) h .empty
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL64 ^^^ VAR i else if o.testBit i then VAR i else ALL64
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 6) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL64.testBit r.val = true := by
    simp only [ALL64]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 64 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 64) (ho : o < 64) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 64
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
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 6) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 6, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 6
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 6
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 64 ≤ r := by omega
      have ha : ALL64 < 2^64 := by decide
      have hv : VAR i < 2^64 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^64; decide
      have hlt_m : fastBitMask z o i < 2^64 := by
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
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h * 31 + (w &&& 255) + ((w >>> 8) &&& 255) * 3 + ((w >>> 16) &&& 255) * 7 + ((w >>> 32) &&& 255) * 13 + ((w >>> 48) &&& 255) * 29) 0) &&& 255
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def mapPermWord (sw : List (Nat × Nat)) (ws : List Nat) : List Nat :=
  match sw with
  | [] => ws
  | _ => ws.map (permWord sw)
lemma mapPermWord_eq (sw : List (Nat × Nat)) (ws : List Nat) :
    mapPermWord sw ws = ws.map (permWord sw) := by
  cases sw with
  | nil =>
    change ws = ws.map (fun w => w)
    simp
  | cons p ps => rfl
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (mapPermWord sw ws))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^64)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^64)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · rw [mapPermWord_eq] at hhit; unfold bucketContainsBT at hhit
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
    have hinv_w : ∀ x : Nat, x < 2^64 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 64
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^64 := by
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
abbrev FastPool := BoundPool × List Nat × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else
    let consts := vals.filter (isConstM c.dom)
    some (c, miss, consts, consts.length)
def fastPoolCut (fp : FastPool) (k a b z : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let consts := fp.2.2.1
  let totC := fp.2.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && consts.contains a then 1 else 0
    let dropB := if !kb && consts.contains b then 1 else 0
    let base := c.lb + (totC - dropA - dropB)
    if k + c.paid >= base + 1 then false
    else
      let m := z &&& c.dom
      if m == 0 || m == c.dom then true
      else if k + c.paid >= base then false
      else
        if k + c.paid + 1 < base && (!miss.contains a && !miss.contains b) then true
        else c.pm.contains m || c.pm.contains (c.dom ^^^ m)
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
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (hd : d < 4)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 (bin d a.1 b.1) ka kb = true) :
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
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            exact List.Nodup.not_mem_erase (List.Nodup.of_map Prod.fst nd) hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · exact hna' hka (unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa))
        · exact hnb' hkb (unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb))
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      have hlen_f : ((ws.map Prod.fst).filter (isConstM c.dom)).length = (ws.map Prod.fst).countP (isConstM c.dom) := by
        rw [List.countP_eq_length_filter]
      have hca : ((ws.map Prod.fst).filter (isConstM c.dom)).contains a.1 = isConstM c.dom a.1 := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map_of_mem ha, h⟩⟩
      have hcb : ((ws.map Prod.fst).filter (isConstM c.dom)).contains b.1 = isConstM c.dom b.1 := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map_of_mem hb, h⟩⟩
      have hma : (!((ws.map Prod.fst).filter (fun w => !availM c.dom c.pm w)).contains a.1) = availM c.dom c.pm a.1 := by
        cases h : availM c.dom c.pm a.1 <;> simp [List.contains_iff_mem, List.mem_filter, List.mem_map_of_mem ha, h]
      have hmb : (!((ws.map Prod.fst).filter (fun w => !availM c.dom c.pm w)).contains b.1) = availM c.dom c.pm b.1 := by
        cases h : availM c.dom c.pm b.1 <;> simp [List.contains_iff_mem, List.mem_filter, List.mem_map_of_mem hb, h]
      rw [hlen_f, hca, hcb, hma, hmb] at hcut
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut choiceOK
      simp only [choiceVal, h_all_avail, Bool.and_true, List.countP_cons, Bool.and_eq_true, decide_eq_true_eq, hd, true_and]
      rw [hcnt]
      set z := bin d a.1 b.1
      set m := z &&& c.dom
      set restC := (ws.map Prod.fst).countP (isConstM c.dom) - (if !ka && isConstM c.dom a.1 then 1 else 0) - (if !kb && isConstM c.dom b.1 then 1 else 0)
      change (k + c.paid + (!availM c.dom c.pm z).toNat < c.lb + (restC + if isConstM c.dom z then 1 else 0)) ∧
        ((!(!availM c.dom c.pm z)) || (availM c.dom c.pm a.1 && availM c.dom c.pm b.1)) = true
      have hbase_le : ¬(k + c.paid ≥ c.lb + restC + 1) := by
        intro hge; simp only [hge, ↓reduceIte, Bool.false_eq_true] at hcut
      simp only [hbase_le, ↓reduceIte] at hcut
      by_cases hzc : (m == 0 || m == c.dom) = true
      · have hisc : isConstM c.dom z = true := hzc
        have havz : availM c.dom c.pm z = true := by
          unfold availM; dsimp only; rw [show (z &&& c.dom == 0 || z &&& c.dom == c.dom) = true from hzc]; simp
        simp only [hisc, havz, Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or, ite_true, and_true]
        omega
      · have hzc_f : (m == 0 || m == c.dom) = false := Bool.eq_false_iff.mpr hzc
        have hisc : isConstM c.dom z = false := hzc_f
        have hav_eq : availM c.dom c.pm z = (c.pm.contains m || c.pm.contains (c.dom ^^^ m)) := by
          unfold availM; dsimp only
          have hm0 : (m == 0) = false := by cases h1 : (m == 0) <;> simp [h1] at hzc_f ⊢
          have hmd : (m == c.dom) = false := by cases h1 : (m == c.dom) <;> simp [h1] at hzc_f ⊢
          change (m == 0 || m == c.dom || c.pm.contains m || c.pm.contains (c.dom ^^^ m)) = _
          simp [hm0, hmd]
        simp only [hzc_f, Bool.false_eq_true, ↓reduceIte] at hcut
        have hlt_b : ¬(k + c.paid ≥ c.lb + restC) := by
          intro hge; simp only [hge, ↓reduceIte, Bool.false_eq_true] at hcut
        simp only [hlt_b, ↓reduceIte] at hcut
        rw [hav_eq, hisc]
        simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
        by_cases hfast : (k + c.paid + 1 < c.lb + restC ∧ (availM c.dom c.pm a.1 && availM c.dom c.pm b.1) = true)
        · cases hpm : (c.pm.contains m || c.pm.contains (c.dom ^^^ m)) <;>
            simp only [Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false, Bool.true_or, Bool.false_or, hfast.2] <;>
            exact ⟨by omega, trivial⟩
        · have hfast_b : (decide (k + c.paid + 1 < c.lb + restC) && (availM c.dom c.pm a.1 && availM c.dom c.pm b.1)) = false := by
            rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact hfast ⟨h.1, (Bool.and_eq_true _ _).mpr h.2⟩
          simp only [hfast_b, Bool.false_eq_true, ↓reduceIte] at hcut
          simp only [hcut, Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or]
          exact ⟨by omega, trivial⟩
def evalMoveBT (cap n fmask : Nat) (ws : List Decor)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b : Decor) (z1 sz rs : Nat) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    if ((rs ||| sz) &&& fmask) != fmask then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 z1 ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (r00 r10 r01 r11 : Nat)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  if n > cap + 1 then true else
  let z1 := bin d a.1 b.1
  if z1 == 0 || ws.any (fun v => v.1 == z1) then true else
    let sz := bin d a.2.1 b.2.1 ^^^ bin d a.2.2 b.2.2
    let go := evalMoveBT cap n fmask ws fpools autos prevBks d a b z1 sz
    if n > cap then go r00 false false
    else if n == cap then go r00 false false && go r10 true false && go r01 false true
    else go r00 false false && go r10 true false && go r01 false true && go r11 true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    let sa := dsep a
    let r01 := takeOne cov sa
    bs.all (fun b =>
      let sb := dsep b
      let r00 := takeTwo cov sa sb
      let r10 := takeOne cov sb
      [0, 1, 2, 3].all (testPairBT cap n fmask ws r00 r10 r01 cov.1 fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^64) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^64)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (_hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws fpools autos prevBks d a b (bin d a.1 b.1) (dsep (dbin d a b)) (restCov (coverage ws) (dsep a) (dsep b) ka kb) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^64 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
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
  dsimp only [z] at hcov_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, Bool.false_eq_true] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 (bin d a.1 b.1) ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 _hd ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 (bin d a.1 b.1) ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws (takeTwo cov (dsep a) (dsep b)) (takeOne cov (dsep b)) (takeOne cov (dsep a)) cov.1 fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws (takeTwo cov (dsep b) (dsep a)) (takeOne cov (dsep a)) (takeOne cov (dsep b)) cov.1 fpools autos prevBks b a d = true) := by
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
    (hT : T < 2^64) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^64) (out : T ∉ ws.map Prod.fst)
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
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (takeTwo (coverage ws) (dsep x) (dsep y)) (takeOne (coverage ws) (dsep y)) (takeOne (coverage ws) (dsep x)) (coverage ws).1 fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws fpools autos prevBks d' x y (bin d' x.1 y.1) (dsep (dbin d' x y)) (restCov (coverage ws) (dsep x) (dsep y) k1 k2) k1 k2 = true := by
      have hnz_b : (bin d' x.1 y.1 == 0) = false := beq_false_of_ne hnz'
      have hfr_b : (ws.any (fun v => v.1 == bin d' x.1 y.1)) = false := by
        rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
        exact hfr' ((beq_iff_eq.mp heq) ▸ List.mem_map_of_mem hv)
      by_cases hlen : 1 + (ws.length - (if k1 then 0 else 1) - (if k2 then 0 else 1)) > cap
      · unfold evalMoveBT; simp [hlen]
      · unfold testPairBT at ht
        have hnot1 : ¬(ws.length > cap + 1) := by cases k1 <;> cases k2 <;> simp at hlen <;> omega
        simp only [hnot1, ↓reduceIte, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at ht
        by_cases hgt : ws.length > cap
        · simp only [hgt, ↓reduceIte] at ht
          cases k1 <;> cases k2
          · exact ht
          · simp at hlen; omega
          · simp at hlen; omega
          · simp at hlen; omega
        · simp only [hgt, ↓reduceIte] at ht
          by_cases heq : ws.length = cap
          · simp only [heq, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at ht ⊢
            cases k1 <;> cases k2
            · exact ht.1.1
            · exact ht.2
            · exact ht.1.2
            · simp at hlen; omega
          · have hneq : (ws.length == cap) = false := beq_false_of_ne heq
            simp only [hneq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at ht
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
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^64) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^64) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^64 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^64) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^64) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^64)
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
def nodupNats : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupNats xs
lemma nodupNats_sound : ∀ {l : List Nat}, nodupNats l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupNats, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, nodupNats_sound h.2⟩
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
  nodupNats vals && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^64) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^64) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^64 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^64 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    (nodupNats_sound ok.1.1)
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
    btUpdate [] 8 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^64) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^64) W)
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
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := .empty
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
def buildPoolsSubBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : BT (Option PoolSpec)) (used : List Nat) : BT (Option BoundPool) :=
  used.foldl (fun acc pIdx =>
    match btGet none pspecs pIdx with
    | none => acc
    | some (slIdx, chIdxs) =>
      match btGet none slices slIdx with
      | none => acc
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
        btSet pdepth acc pIdx (materialize raw cs dom lb)) BT.empty
lemma buildPoolsSubBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))}
    {pspecs : BT (Option PoolSpec)} {used : List Nat}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsSubBT pdepth W raw slices pspecs used) := by
  unfold buildPoolsSubBT
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := .empty
  generalize (BT.empty : BT (Option BoundPool)) = acc at hinit ⊢
  induction used generalizing acc with
  | nil => exact hinit
  | cons pIdx rest ih =>
    apply ih
    dsimp only
    cases hps : btGet none pspecs pIdx with
    | none => simp only [hps]; exact hinit
    | some spec =>
      cases hsl : btGet none slices spec.1 with
      | none => simp only [hps, hsl]; exact hinit
      | some sl =>
        simp only [hps, hsl]
        apply btAll_set hinit
        intro c hc
        exact materialize_sound (btAll_get (d := none) hSlices (fun _ h => by simp at h) spec.1 sl hsl) hc
lemma checkNodesBT_mem {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT : T < 2^64) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^64) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := by
  intro ns hns
  unfold nodeValsBT; rw [sortNats_toFinset]
  exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
lemma forall_append {α : Type} {P : α → Prop} {l1 l2 : List α}
    (h1 : ∀ x ∈ l1, P x) (h2 : ∀ x ∈ l2, P x) : ∀ x ∈ l1 ++ l2, P x := by
  intro x hx; rcases List.mem_append.mp hx with h | h; exact h1 x h; exact h2 x h
lemma buildBucketsBT_of_mem {W : BT Decor} {T k nodes}
    (hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := .empty
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
lemma obs_all64_xor (G : Nat) : obs (ALL64 ^^^ G) = invW (obs G) := by
  funext r
  have hall : ALL64.testBit r.val = true := by
    simp only [ALL64]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 64 r.val
  simp only [obs, invW, Nat.testBit_xor, hall, Bool.true_xor]
lemma lower_slice_flip {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^64 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^64) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G ∨ renameW f T = ALL64 ^^^ G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  rcases eq with heq | heq
  · exact lower_slice hT0 hTlt hTb0 hR hG0 hGlt hGb0 f heq covered singles necessary constant L prior
  · classical
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
    have gc : restrictW f (obs T) = invW (obs G) :=
      (obs_renameW f T).symm.trans ((congrArg obs heq).trans (obs_all64_xor G))
    have hnc : ¬Constant (invW (obs G)) := fun hc => obs_not_const hG0 hGlt hGb0 (invW_inv (obs G) ▸ invW_const hc)
    have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (gc ▸ hnc) (restrict_run f (live_to_run run front nd fe))
        (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
    have havG : Avail next (obs G) := by
      rw [gc] at hav; simpa [invW_inv] using avail_inv hav
    have hlo := prior q next hq havG
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
    omega
def liftCheckF (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G || fixWord z o T == ALL64 ^^^ G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL64))
lemma lift_of_f {z o roots T other G essPairs L} (ok : liftCheckF z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheckF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G ∨ renameW (fixRow z o) T = ALL64 ^^^ G := by
    rw [← fixWord_eq_renameW]; exact heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice_flip p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL64]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 64 r'.val |> fun e => by simpa [this] using e⟩
def sliceDirectCheckF (z o : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 64) && decide (o < 64) && ((z &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord z o T == qGoal || fixWord z o T == ALL64 ^^^ qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord z o a))
lemma slice_fast_direct_f {z o raw T qRoots qGoal qL}
    (ok : sliceDirectCheckF z o raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  simp only [sliceDirectCheckF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hz, ho⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  rw [subcubeFast_eq_subcube z o hz ho hzo]
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  rcases heq with heq | heq
  · refine ⟨fixRow z o, qRoots, subcube_fixRow z o hz ho hzo,
      fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
    rw [← obs_renameW, ← fixWord_eq_renameW, heq]
    exact hPrior
  · refine ⟨fixRow z o, qRoots, subcube_fixRow z o hz ho hzo,
      fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← fixWord_eq_renameW, heq, obs_all64_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← fixWord_eq_renameW, heq, obs_all64_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)
def identRow (u v : Nat) (r : Row) : Row :=
  if r.val.testBit u == r.val.testBit v then r
  else ⟨(r.val ^^^ (1 <<< v)) % 64, Nat.mod_lt _ (by decide)⟩
def identDom (u v : Nat) : Nat := ALL64 ^^^ (VAR u ^^^ VAR v)
def identWord (u v w : Nat) : Nat :=
  (List.range 64).foldr (fun r acc =>
    let fr := if r.testBit u == r.testBit v then r else (r ^^^ (1 <<< v)) % 64
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma identWord_eq_renameW (u v w : Nat) : identWord u v w = renameW (identRow u v) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold identWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 64
  · rw [testBit_renameW (identRow u v) w ⟨r, hr⟩]
    simp only [List.mem_range, hr, decide_true, Bool.true_and, identRow]
    split <;> rfl
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma identDom_identRow (u v : Nat) (hu : u < 6) (hv : v < 6) (r : Row) :
    (identDom u v).testBit (identRow u v r).val = true := by
  revert r
  interval_cases u <;> interval_cases v <;> decide +kernel
def sliceIdentCheck (u v : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (u < 6) && decide (v < 6) &&
    checkProper qGoal && checkRoots qRoots &&
    (identWord u v T == qGoal || identWord u v T == ALL64 ^^^ qGoal) &&
    raw.all (fun a => freeIn qRoots (identWord u v a))
lemma slice_ident {u v raw T qRoots qGoal qL}
    (ok : sliceIdentCheck u v raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (identDom u v) qL := by
  simp only [sliceIdentCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hu, hv⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  rcases heq with heq | heq
  · refine ⟨identRow u v, qRoots, identDom_identRow u v hu hv,
      fun a ha => freeIn_sound ((identWord_eq_renameW u v a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← identWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
    rw [← obs_renameW, ← identWord_eq_renameW, heq]
    exact hPrior
  · refine ⟨identRow u v, qRoots, identDom_identRow u v hu hv,
      fun a ha => freeIn_sound ((identWord_eq_renameW u v a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← identWord_eq_renameW, heq, obs_all64_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← identWord_eq_renameW, heq, obs_all64_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)

def freeInFlip (other : List Nat) (w : Nat) : Bool :=
  w == 0 || w == ALL64 || other.contains w || other.contains (ALL64 ^^^ w)
lemma freeInFlip_sound {other : List Nat} {f : Row → Row} {a : Nat}
    (ok : freeInFlip other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeInFlip, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with ((h0 | h1) | hm) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL64]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 64 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
  · have hmem : obs (ALL64 ^^^ renameW f a) ∈ other.map obs := List.mem_map_of_mem hm
    rw [obs_all64_xor] at hmem
    exact Or.inr (Or.inr hmem)
def fiRowVal (z o u v : Nat) (fl : Bool) (r : Nat) : Nat :=
  let r1 := ((r &&& (63 ^^^ z)) ||| o) % 64
  let want := if fl then !r1.testBit u else r1.testBit u
  if r1.testBit v == want then r1 else (r1 ^^^ (1 <<< v)) % 64
lemma fiRowVal_lt (z o u v : Nat) (fl : Bool) (r : Nat) : fiRowVal z o u v fl r < 64 := by
  unfold fiRowVal; dsimp only; split <;> split <;> exact Nat.mod_lt _ (by decide : 0 < 64)
def fiRow (z o u v : Nat) (fl : Bool) (r : Row) : Row := ⟨fiRowVal z o u v fl r.val, fiRowVal_lt z o u v fl r.val⟩
def fiDom (z o u v : Nat) (fl : Bool) : Nat :=
  subcubeFast z o &&& (if fl then VAR u ^^^ VAR v else ALL64 ^^^ (VAR u ^^^ VAR v))
def fiWord (z o u v : Nat) (fl : Bool) (w : Nat) : Nat :=
  (List.range 64).foldr (fun r acc => if w.testBit (fiRowVal z o u v fl r) then acc ||| (1 <<< r) else acc) 0
lemma fiWord_eq_renameW (z o u v : Nat) (fl : Bool) (w : Nat) : fiWord z o u v fl w = renameW (fiRow z o u v fl) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fiWord; rw [testBit_foldr_bits]
  by_cases hr : r < 64
  · rw [testBit_renameW (fiRow z o u v fl) w ⟨r, hr⟩]
    simp [hr, fiRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
def sliceFICheck (z o u v : Nat) (fl : Bool) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  (List.range 64).all (fun r => (fiDom z o u v fl).testBit (fiRowVal z o u v fl r)) &&
    checkProper qGoal && checkRoots qRoots &&
    (fiWord z o u v fl T == qGoal || fiWord z o u v fl T == ALL64 ^^^ qGoal) &&
    raw.all (fun a => freeInFlip qRoots (fiWord z o u v fl a))
lemma slice_fi {z o u v fl raw T qRoots qGoal qL}
    (ok : sliceFICheck z o u v fl raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (fiDom z o u v fl) qL := by
  simp only [sliceFICheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at ok
  obtain ⟨⟨⟨⟨hdom, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have hdom' : ∀ r : Row, (fiDom z o u v fl).testBit (fiRow z o u v fl r).val = true := fun r => hdom r.val r.isLt
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  rcases heq with heq | heq
  · refine ⟨fiRow z o u v fl, qRoots, hdom',
      fun a ha => freeInFlip_sound ((fiWord_eq_renameW z o u v fl a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← fiWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
    rw [← obs_renameW, ← fiWord_eq_renameW, heq]; exact hPrior
  · refine ⟨fiRow z o u v fl, qRoots, hdom',
      fun a ha => freeInFlip_sound ((fiWord_eq_renameW z o u v fl a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← fiWord_eq_renameW, heq, obs_all64_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← fiWord_eq_renameW, heq, obs_all64_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)

def mkBase (pos neg : List Nat) (rs : List Nat) : List Decor :=
  rs.map fun w => (w, projBits pos w, projBits neg w)
lemma mkBase_ok {pos neg rs} (hR : checkRoots rs = true) :
    ∀ x ∈ mkBase pos neg rs, faithful pos neg x ∧ x.1 < 2^64 := by
  have hr := checkRoots_sound hR
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact ⟨⟨rfl, rfl⟩, (hr w hw).1⟩
def evalInput6 (r : Row) : Fin 6 → Bool := fun i => r.val.testBit i.val
def packInput6 (x : Fin 6 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
   16 * (x 4).toNat + 32 * (x 5).toNat, by
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide⟩
lemma evalInput6_packInput6 (x : Fin 6 → Bool) : evalInput6 (packInput6 x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (j : Fin 6),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
  fin_cases i <;> simpa [evalInput6, packInput6] using hi
lemma var_testBit6 (i : Fin 6) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^64 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^64) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^64 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput6 r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi6 : i < 6 := by simpa using hi2
      have hv : (varsOf 63)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput6, swRead, Bool.false_bne]
      have hget : (varsOf 63)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit6 ⟨i, hi6⟩ r
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
    by_cases hr : r < 64
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
lemma replace_of_lower6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 63) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩)
    (tgt : (Fin 6 → Bool) → Bool)
    (hTgtT : ∀ r : Row, tgt (evalInput6 r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val)
    (s : Nat) (hs : PEqualNP.MetaComplexity.HasCircuitSize 6 tgt s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = tgt x := by
  obtain ⟨⟨gates, o⟩, hfan, hsize, spec⟩ := hs
  have legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop, hlen⟩
  have hwEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = tgt x := by
    intro x
    have hx := evalInput6_packInput6 x
    rw [← hx]
    exact (hwEvalR (packInput6 x)).trans (hTgtT (packInput6 x)).symm
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hlt : gates.countP isBin < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full6 T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput6 r)).trans (hTgtT r))
    have hnd : S.toList.Nodup := Finset.nodup_toList S
    have hrun := live_to_run hlive S.toList hnd (by simp)
    have hsup : Supply ((varsOf 63).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 63).map obs)
        (show Reach ((varsOf 63).map obs) 0 ((varsOf 63).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    have hcsz : (⟨wit, wo⟩ : Circuit).size = wit.length := rfl
    have hgsz : (⟨gates, o⟩ : Circuit).size = gates.length := rfl
    refine ⟨⟨wit, wo⟩, hwMono, ?_, hwEval⟩
    omega
  · refine ⟨⟨gates, o⟩, ?_, hsize, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
def q (sl : Nat) (cs : List Nat) : Option PoolSpec :=
  some (sl, cs.map fun x => (x % 4, (x / 4) % 1024, x / 4096))
def r (a n : Nat) : List Nat := List.range' a n
def b6 : List Nat := [0,1,2,3,4,5]
def b5 : List Nat := [0,1,2,3,4]
def u6 (w p : List Nat) : NodeSpec := (b6 ++ w, p, [0])
def e6 (w p : List Nat) : NodeSpec := (b6 ++ w, p, [])
def a6 (w p a : List Nat) : NodeSpec := (b6 ++ w, p, a)
def u5 (w p : List Nat) : NodeSpec := (b5 ++ w, p, [0])
def e5 (w p : List Nat) : NodeSpec := (b5 ++ w, p, [])
def a5 (w p a : List Nat) : NodeSpec := (b5 ++ w, p, a)

def g_0 := 0xe8e8e8e8e8e8e8e8
def r_0 : List Nat := varsOf 7
def p_0 : List Nat := [3,3,5,5,6,6]
def q_0 : List Nat := [2,1,4,1,4,2]
def F_0 : Nat := fullMask 6
set_option maxHeartbeats 0 in
lemma gp_0 : goodPairs g_0 p_0 q_0 := goodPairs_of (by decide +kernel)
def W_0 : BT Decor := buildWiresBT 2 (mkBase p_0 q_0 r_0) []
lemma W_0_ok : btAll (fun x => faithful p_0 q_0 x ∧ x.1 < 2^64) W_0 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_0 : List (List (Nat × Nat)) := [[]]
def A_0 : BT (List (Nat × Nat)) := btOfList 1 al_0
set_option maxHeartbeats 0 in
lemma A_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_0 = g_0) A_0 := btAll_ofList (autos_of (by decide +kernel))
def S_0 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_0_ok : btAll (fun o => ∀ p, o = some p → Slice r_0 g_0 p.1 p.2) S_0 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_0 : BT (Option PoolSpec) := btOfList 1 []
def B_0_2 : BT (List (List Nat)) := BT.empty
lemma B_0_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 2 xs.toFinset) B_0_2 := .empty
def U_0_3 : List Nat := []
def P_0_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 r_0 S_0 ps_0 U_0_3
def N_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_0_3 : checkNodesBT W_0 g_0 F_0 P_0_3 A_0 B_0_2 3 N_0_3 = true := by decide +kernel
def B_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 N_0_3
set_option maxRecDepth 500000 in
lemma B_0_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 3 xs.toFinset) B_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound S_0_ok) A_0_ok B_0_2_ok C_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck r_0 g_0 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT B_0_3 r_0 = true := by decide +kernel
lemma low_0 : Lower r_0 g_0 4 := lower_of_forestBT root_0_ok B_0_3_ok root_0_in
def g_1 := 0xfee8fee8fee8fee8
def r_1 : List Nat := varsOf 15
def p_1 : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12]
def q_1 : List Nat := [2,1,4,1,4,2,8,1,8,2,8,4]
def F_1 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_1 : goodPairs g_1 p_1 q_1 := goodPairs_of (by decide +kernel)
def W_1 : BT Decor := buildWiresBT 4 (mkBase p_1 q_1 r_1) [(1,0,1),(1,4,2),(2,5,3),(1,1,2),(1,3,1),(1,3,2),(2,4,3),(1,3,0)]
lemma W_1_ok : btAll (fun x => faithful p_1 q_1 x ∧ x.1 < 2^64) W_1 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_1 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2),(1,3)]]
def A_1 : BT (List (Nat × Nat)) := btOfList 4 al_1
set_option maxHeartbeats 0 in
lemma A_1_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_1 = g_1) A_1 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_1_0 : Slice r_1 g_1 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_1 : Slice r_1 g_1 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_2 : Slice r_1 g_1 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_3 : Slice r_1 g_1 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
def S_1 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4)]
lemma S_1_ok : btAll (fun o => ∀ p, o = some p → Slice r_1 g_1 p.1 p.2) S_1 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_1_0) (forall_cons (fun _ h => by cases h; exact sl_1_1) (forall_cons (fun _ h => by cases h; exact sl_1_2) (forall_cons (fun _ h => by cases h; exact sl_1_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_1 : BT (Option PoolSpec) := btOfList 2 [q 2 [],q 1 [],q 3 [],q 0 []]
def B_1_2 : BT (List (List Nat)) := BT.empty
lemma B_1_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 2 xs.toFinset) B_1_2 := .empty
def U_1_3 : List Nat := [0,1]
def P_1_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_3
def N_1_3 : List NodeSpec := [([0,7,8,9],[0,1],[]),([6,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_3 : checkNodesBT W_1 g_1 F_1 P_1_3 A_1 B_1_2 3 N_1_3 = true := by decide +kernel
def B_1_3 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_3
set_option maxRecDepth 500000 in
lemma B_1_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 3 xs.toFinset) B_1_3 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_2_ok C_1_3
def U_1_4 : List Nat := [1,2,3]
def P_1_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_4
def N_1_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([0,1,2,11,8],[3,1],[10]),([10,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_4 : checkNodesBT W_1 g_1 F_1 P_1_4 A_1 B_1_3 4 N_1_4 = true := by decide +kernel
def B_1_4 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_4
set_option maxRecDepth 500000 in
lemma B_1_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 4 xs.toFinset) B_1_4 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_3_ok C_1_4
def U_1_5 : List Nat := (r 0 4)
def P_1_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_5
def N_1_5 : List NodeSpec := [([0,1,4,2,3],[3,1,0,2],[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_5 : checkNodesBT W_1 g_1 F_1 P_1_5 A_1 B_1_4 5 N_1_5 = true := by decide +kernel
def B_1_5 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_5
set_option maxRecDepth 500000 in
lemma B_1_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 5 xs.toFinset) B_1_5 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_4_ok C_1_5
def U_1_6 : List Nat := (r 0 4)
def P_1_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_6
def N_1_6 : List NodeSpec := [([0,1,2,3],[3,1,0,2],[0,2,4,6,8,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_6 : checkNodesBT W_1 g_1 F_1 P_1_6 A_1 B_1_5 6 N_1_6 = true := by decide +kernel
def B_1_6 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_6
set_option maxRecDepth 500000 in
lemma B_1_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 6 xs.toFinset) B_1_6 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_5_ok C_1_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_1_ok : forestRootCheck r_1 g_1 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_1_in : bucketContainsBT B_1_6 r_1 = true := by decide +kernel
lemma low_1 : Lower r_1 g_1 7 := lower_of_forestBT root_1_ok B_1_6_ok root_1_in
def g_2 := 0xfe80fe80fe80fe80
def r_2 : List Nat := varsOf 15
def p_2 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14]
def q_2 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6]
def F_2 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_2 : goodPairs g_2 p_2 q_2 := goodPairs_of (by decide +kernel)
def W_2 : BT Decor := buildWiresBT 5 (mkBase p_2 q_2 r_2) [(0,2,3),(1,2,3),(3,4,5),(0,1,2),(1,1,2),(3,7,8),(2,0,3),(3,0,3),(1,1,3),(0,0,12),(0,0,3),(1,0,3),(3,4,0),(1,14,2),(2,0,2),(3,0,2),(3,2,15),(2,2,1),(3,21,0),(2,0,1),(1,23,2),(0,0,1),(1,0,1),(3,2,3)]
lemma W_2_ok : btAll (fun x => faithful p_2 q_2 x ∧ x.1 < 2^64) W_2 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_2 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_2 : BT (List (Nat × Nat)) := btOfList 3 al_2
set_option maxHeartbeats 0 in
lemma A_2_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_2 = g_2) A_2 := btAll_ofList (autos_of (by decide +kernel))
def S_2 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_2_ok : btAll (fun o => ∀ p, o = some p → Slice r_2 g_2 p.1 p.2) S_2 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_2 : BT (Option PoolSpec) := btOfList 1 []
def B_2_1 : BT (List (List Nat)) := BT.empty
lemma B_2_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 1 xs.toFinset) B_2_1 := .empty
def U_2_2 : List Nat := []
def P_2_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_2
def N_2_2 : List NodeSpec := [([6,0,1],[],[]),([9,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_2 : checkNodesBT W_2 g_2 F_2 P_2_2 A_2 B_2_1 2 N_2_2 = true := by decide +kernel
def B_2_2 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_2
set_option maxRecDepth 500000 in
lemma B_2_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 2 xs.toFinset) B_2_2 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_1_ok C_2_2
def U_2_3 : List Nat := []
def P_2_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_3
def N_2_3 : List NodeSpec := [([10,11,1,2],[],[3]),([13,1,2,3],[],[]),([14,1,2,15],[],[3]),([16,1,2,3],[],[]),([0,1,17,3],[],[]),([18,19,1,3],[],[2]),([20,0,1,3],[],[]),([22,1,2,3],[],[]),([0,1,24,3],[],[]),([25,26,2,3],[],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_3 : checkNodesBT W_2 g_2 F_2 P_2_3 A_2 B_2_2 3 N_2_3 = true := by decide +kernel
def B_2_3 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_3
set_option maxRecDepth 500000 in
lemma B_2_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 3 xs.toFinset) B_2_3 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_2_ok C_2_3
def U_2_4 : List Nat := []
def P_2_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_4
def N_2_4 : List NodeSpec := [([10,0,1,2,3],[],[0]),([14,0,1,2,3],[],[0,1,3,5]),([18,0,1,2,3],[],[0,1,3]),([27,0,1,2,3],[],[4]),([0,1,2,3,15],[],[0,1,2,4]),([0,1,26,2,3],[],[0]),([25,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_4 : checkNodesBT W_2 g_2 F_2 P_2_4 A_2 B_2_3 4 N_2_4 = true := by decide +kernel
def B_2_4 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_4
set_option maxRecDepth 500000 in
lemma B_2_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 4 xs.toFinset) B_2_4 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_3_ok C_2_4
def U_2_5 : List Nat := []
def P_2_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_5
def N_2_5 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_5 : checkNodesBT W_2 g_2 F_2 P_2_5 A_2 B_2_4 5 N_2_5 = true := by decide +kernel
def B_2_5 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_5
set_option maxRecDepth 500000 in
lemma B_2_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 5 xs.toFinset) B_2_5 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_4_ok C_2_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_ok : forestRootCheck r_2 g_2 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_in : bucketContainsBT B_2_5 r_2 = true := by decide +kernel
lemma low_2 : Lower r_2 g_2 6 := lower_of_forestBT root_2_ok B_2_5_ok root_2_in
def g_3 := 0xfec0fec0fec0fec0
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_4 := 0xf880f880f880f880
def r_4 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_4 : Lower r_4 g_4 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_5 := 0xfffef880fffef880
def r_5 : List Nat := varsOf 31
def p_5 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,17,17,18,18,19,20,20,21,22,24,24,25,26]
def q_5 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,1,16,2,3,16,4,5,6,16,8,9,10]
def F_5 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_5 : goodPairs g_5 p_5 q_5 := goodPairs_of (by decide +kernel)
def W_5 : BT Decor := buildWiresBT 7 (mkBase p_5 q_5 r_5) [(1,0,2),(3,3,5),(1,1,3),(3,2,7),(0,0,1),(1,2,3),(2,10,4),(1,2,4),(3,3,12),(1,3,4),(3,2,14),(1,10,4),(3,1,16),(3,0,16),(0,0,16),(0,10,4),(3,20,16),(0,1,10),(1,1,10),(3,22,23),(0,1,4),(1,1,4),(3,25,26),(2,0,3),(1,28,2),(1,9,2),(1,30,4),(3,3,31),(3,10,4),(0,0,4),(1,34,3),(1,34,2),(3,3,36),(2,0,10),(3,0,10),(2,0,20),(1,2,35),(1,29,4),(3,2,4),(3,43,14),(3,25,0),(3,9,12),(2,1,3),(1,47,2),(3,1,4),(1,49,2),(1,50,3),(0,5,7),(2,0,2),(1,53,4),(3,3,54),(1,53,3),(2,1,2),(3,57,14),(1,9,3),(2,30,3),(2,30,4),(1,30,3),(1,9,4),(1,0,4),(3,2,64),(3,3,63),(2,50,3),(3,9,10),(3,10,64),(0,10,64),(1,33,3),(1,28,4),(3,1,64),(2,0,4),(3,0,4),(1,49,3),(3,75,10),(0,0,10),(1,0,10),(2,1,10),(3,80,0),(3,25,10),(1,39,1),(2,29,4),(3,3,64),(1,85,2),(1,1,20),(0,0,12),(3,3,4),(1,0,1),(1,33,2),(1,1,2),(3,1,10),(2,0,14)]
lemma W_5_ok : btAll (fun x => faithful p_5 q_5 x ∧ x.1 < 2^64) W_5 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_5 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_5 : BT (List (Nat × Nat)) := btOfList 2 al_5
set_option maxHeartbeats 0 in
lemma A_5_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_5 = g_5) A_5 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_5_0 : Slice r_5 g_5 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) 0xfffafaa0fffafaa0 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_1 : Slice r_5 g_5 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_2 : Slice r_5 g_5 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) 0xfefe8080fefe8080 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_3 : Slice r_5 g_5 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcf000fffcf000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_4 : Slice r_5 g_5 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_5 : Slice r_5 g_5 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_4
set_option maxHeartbeats 0 in
lemma sl_5_6 : Slice r_5 g_5 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_7 : Slice r_5 g_5 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_8 : Slice r_5 g_5 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
def S_5 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,7),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 16 0,5),some (subcubeFast 3 0,4),some (subcubeFast 16 1,4),some (subcubeFast 16 2,4)]
lemma S_5_ok : btAll (fun o => ∀ p, o = some p → Slice r_5 g_5 p.1 p.2) S_5 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_5_0) (forall_cons (fun _ h => by cases h; exact sl_5_1) (forall_cons (fun _ h => by cases h; exact sl_5_2) (forall_cons (fun _ h => by cases h; exact sl_5_3) (forall_cons (fun _ h => by cases h; exact sl_5_4) (forall_cons (fun _ h => by cases h; exact sl_5_5) (forall_cons (fun _ h => by cases h; exact sl_5_6) (forall_cons (fun _ h => by cases h; exact sl_5_7) (forall_cons (fun _ h => by cases h; exact sl_5_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_5 : BT (Option PoolSpec) := btOfList 7 [q 1 [16424,16425,65619],q 1 [40964,40965,94299],q 1 [16388,16389,106599],q 1 [],q 2 [],q 1 [16426,16427],q 3 [],q 7 [],q 4 [],q 8 [],q 1 [16425,65543],q 0 [],q 5 [],q 2 [16384,8329],q 0 [12297,40963],q 6 [],q 1 [40962,40963],q 1 [16424,81922],q 1 [16384,12425],q 1 [16388,103],q 1 [49165,65536],q 2 [16393,65536],q 2 [16388,16389,106599],q 1 [16425,65536],q 0 [12297,40999],q 1 [16385,262187],q 1 [16385,262184],q 1 [16384,16385],q 1 [16385,262151],q 1 [16386,16387],q 1 [40960,40961],q 1 [40966,323],q 1 [16388,41063],q 1 [40963,4253],q 1 [16385,262159],q 1 [16424,81925],q 1 [16424,16425],q 2 [16393],q 1 [49167],q 1 [49165],q 1 [16427],q 1 [16425],q 1 [16424],q 1 [16397],q 2 [8305],q 1 [12290],q 2 [8193],q 1 [12310],q 0 [12297],q 1 [16385],q 2 [16497],q 1 [4097],q 2 [16385,262151],q 1 [4096],q 2 [16386,16387],q 1 [16384],q 1 [16391],q 2 [16425],q 2 [8549],q 0 [8197],q 1 [40967],q 1 [16426],q 2 [16388,103],q 2 [16384,16385],q 1 [16386],q 1 [40962],q 2 [16426],q 1 [40961],q 1 [40960],q 2 [16386],q 2 [16385],q 2 [16391],q 2 [4097],q 2 [16384],q 2 [4096]]
def B_5_2 : BT (List (List Nat)) := BT.empty
lemma B_5_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 2 xs.toFinset) B_5_2 := .empty
def U_5_3 : List Nat := []
def P_5_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_3
def N_5_3 : List NodeSpec := [([6,8,9,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_3 : checkNodesBT W_5 g_5 F_5 P_5_3 A_5 B_5_2 3 N_5_3 = true := by decide +kernel
def B_5_3 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_3
set_option maxRecDepth 500000 in
lemma B_5_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 3 xs.toFinset) B_5_3 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_2_ok C_5_3
def U_5_4 : List Nat := [0,1,2]
def P_5_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_4
def N_5_4 : List NodeSpec := [([21,0,1,2,3],[0],[]),([24,0,2,3,4],[1],[]),([27,0,2,3,10],[2],[]),([11,13,0,1,2],[],[]),([13,15,0,1,4],[],[]),([17,18,2,3,4],[],[]),([17,19,2,3,4],[],[]),([13,19,1,2,4],[],[]),([13,0,1,29,4],[],[]),([6,8,0,1,4],[],[0]),([6,9,2,7,4],[],[0]),([32,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_4 : checkNodesBT W_5 g_5 F_5 P_5_4 A_5 B_5_3 4 N_5_4 = true := by decide +kernel
def B_5_4 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_4
set_option maxRecDepth 500000 in
lemma B_5_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 4 xs.toFinset) B_5_4 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_3_ok C_5_4
def U_5_5 : List Nat := (r 2 35)
def P_5_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_5
def N_5_5 : List NodeSpec := [([13,0,1,2,10,4],[3],[0]),([11,0,1,2,3,12],[3],[0]),([0,1,2,59,10,4],[3],[]),e5 [58] [3],([13,0,1,10,4,12],[3,4],[]),([13,0,1,2,4,14],[4],[0]),([0,1,2,20,10,14],[4],[]),([0,2,30,3,7,4],[4],[]),([11,33,0,1,2,3],[5],[0]),([0,1,2,56,10,4],[6,3],[]),([0,1,2,3,72,14],[6,4],[]),([6,0,1,2,10,4],[3,7],[]),([0,1,2,35,10,4],[6,7,3],[]),([28,13,0,1,2,4],[7],[0]),e5 [42] [7],([9,2,5,3,7,4],[7],[0,3]),u5 [31] [6,8,4],([17,0,2,3,4,16],[8],[0]),([6,0,1,2,7,4],[8,7],[0]),e5 [16] (r 6 4),e5 [51] [6,7,9],([0,1,2,3,63,12],[7,6,9,8,3],[]),([0,1,10,12,14],[7,9,4,3],[]),([6,9,1,2,3,4],[9],[0]),([0,1,2,76,10,4],[9,3],[]),([17,0,2,3,10,4],[10],[]),([13,0,1,2,4,16],[11],[0,2]),([11,0,1,2,3,16],[11],[0,1]),([0,1,2,71,10,4],[3,12],[]),([11,0,1,2,10,14],[4,12],[]),([0,1,2,59,4,14],[6,8,12],[]),([0,1,2,56,4,14],[12],[1]),([0,1,2,44,3,14],[12],[]),([0,1,10,4,12,14],[12,3],[]),([13,0,1,2,12,14],[12,4],[]),e5 [41] [6,13],([37,0,1,36,3,4],[13],[]),e5 [37] [13],([19,1,2,3,4,16],[7,15],[0,1]),([0,2,48,3,4,26],[15],[]),([38,39,1,2,3,4],[14,15,16],[2]),([40,1,2,3,10,4],[17],[]),([0,1,2,35,41,4],[6,7,18],[]),([45,1,2,3,10,4],[19],[]),([19,1,2,3,4,12],[20,21],[0]),([27,0,2,3],[15,9,2,22],[0]),([19,1,2,3,10,4],[23],[]),e5 [68] [24],e5 [69] [25],e5 [70] [12,26],([34,1,2,3,10,64],[27],[2]),([73,0,2,3,10,4],[28],[]),([74,75,1,2,3,10],[29],[2]),([78,1,2,3,79,4],[30],[2]),([81,1,2,3,10,4],[31],[]),e5 [82] [32],([0,83,2,3,10,4],[33],[]),e5 [86] [34],([0,2,3,10,87,4],[35],[]),([0,1,2,3,20,16],[36],[0]),e5 [55] [],e5 [52] [],e5 [46] [],e5 [77] [],e5 [84] [],e5 [60] [],e5 [67] [],e5 [61] [],e5 [62] [],([28,65,1,2,3,4],[],[]),e5 [66] [],e5 [11] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_5 : checkNodesBT W_5 g_5 F_5 P_5_5 A_5 B_5_4 5 N_5_5 = true := by decide +kernel
def B_5_5 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_5
set_option maxRecDepth 500000 in
lemma B_5_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 5 xs.toFinset) B_5_5 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_4_ok C_5_5
def U_5_6 : List Nat := ([3,4]++r 6 4++[12,13,15,18,19,27,28,29,34]++r 37 32)
def P_5_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_6
def N_5_6 : List NodeSpec := [a5 [28,12] [3,6,7,4] [0,1,3],e5 [88,12] [7,6],u5 [94,14] [7,6],a5 [9,12] [3,6,7,9,8] [0,1],a5 [63] [7,6,9,8,3,4] [0,1],([28,1,2,3,4,64],[7,15,4],[0,2]),([28,1,2,5,3,4],[15,3,7,4],[]),a5 [5,7] [15,7,9,3,4] [0,3],([0,1,2,35,4],[15,12,18],[0,1]),a5 [85] [7,8,9,34] [0,1],([89,0,1,2,3,12],[3,37,7,9],[1]),a5 [13] (r 6 4++[37,38]) [0,2],u5 [13,12] [12,38,37],a5 [12,16] [7,9,39,37] [0,1,2],a5 [33,10] [40,12] [0,1],a5 [10,16] [41,12] [0,1,2],a5 [20,10] [42,4,12] [0,1,2],([0,1,2,10,4,14],[7,9,4,43],[0,1]),([0,1,2,3,12,14],[7,9,43,37],[0,1]),a5 [12,14] [12,4,43] [0,1],a5 [29] [15,44,45,12] [0,1,2],u5 [6] [8,9,7,46,47],u5 [10,64] [7,6,48,49],a5 [72] [7,6,8,9,3,50] [0,1],e5 [90,10] [48,15,7,9,51],([73,0,2,3,4],[9,7,28,52],[0]),a5 [9,10] [4,6,48,7,9,8,53] [0,1],a5 [30] [6,8,53,4,12] [0,1,2],([74,75,1,2,3],[12,15,29,54],[0,2]),a5 [36] [15,12,13,55] [0,1],a5 [34,10] [48,4,6,7,55] [0,1,2],a5 [49,10] [4,8,9,56] [0,1,2],a5 [50] [7,9,56,4] [0,1],a5 [16] (r 6 4++[41,57]) [0,1,2],e5 [91] [7,9,58],([9,0,2,92,3,4],[9,3,59,15],[1,2]),a5 [93,10] [48,8,9,60] [2],a5 [11,10] [4,12,61] [0,1],([45,1,2,3,4],[6,8,19,62,12],[0]),([34,1,2,3,64],[7,15,27,63],[0,2]),u5 [74,10] [6,7,64],a5 [38,10] [48,7,6,65] [0,1,2],u5 [11] (r 6 4++[61,66]),a5 [10,79] [7,67,6] [0,1],u5 [78,10] [7,6,68]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_6 : checkNodesBT W_5 g_5 F_5 P_5_6 A_5 B_5_5 6 N_5_6 = true := by decide +kernel
def B_5_6 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_6
set_option maxRecDepth 500000 in
lemma B_5_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 6 xs.toFinset) B_5_6 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_5_ok C_5_6
def U_5_7 : List Nat := ([3,4]++r 6 4++[11,12,15,37,45,46,48,49,51,53,55,56,64]++r 69 6)
def P_5_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_7
def N_5_7 : List NodeSpec := [u5 [89] [7,9,3,4],a5 [12] [7,9,3,37,6,8] [0,1,2,3],u5 [28] [4,15,7,45],a5 [5] [7,3,9,15,46] [0,2],a5 [10] ([48,3,4]++r 6 4) [0,1,2],u5 [74] [7,15,64,69],a5 [64] [7,9,15,11,49,70] [0,1],a5 [49] [7,9,56,71] [0,1,2],u5 [90] [11,15,7,51,72],a5 [34] [11,3,4,12,15,55,73] [0,1,2],a5 [9] [11,6,9,8,7,53,74] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_7 : checkNodesBT W_5 g_5 F_5 P_5_7 A_5 B_5_6 7 N_5_7 = true := by decide +kernel
def B_5_7 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_7
set_option maxRecDepth 500000 in
lemma B_5_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 7 xs.toFinset) B_5_7 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_6_ok C_5_7
def U_5_8 : List Nat := [3,4,11]
def P_5_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_8
def N_5_8 : List NodeSpec := [a5 [] [11,3,4] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_8 : checkNodesBT W_5 g_5 F_5 P_5_8 A_5 B_5_7 8 N_5_8 = true := by decide +kernel
def B_5_8 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_8
set_option maxRecDepth 500000 in
lemma B_5_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 8 xs.toFinset) B_5_8 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_7_ok C_5_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_5_ok : forestRootCheck r_5 g_5 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_5_in : bucketContainsBT B_5_8 r_5 = true := by decide +kernel
lemma low_5 : Lower r_5 g_5 9 := lower_of_forestBT root_5_ok B_5_8_ok root_5_in
def g_6 := 0xe800e800e800e800
def r_6 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_6 : Lower r_6 g_6 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_7 := 0xffe8ffe8ffe8ffe8
def r_7 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_7 : Lower r_7 g_7 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_8 := 0xffe88000ffe88000
def r_8 : List Nat := varsOf 31
def p_8 : List Nat := [15,15,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,29,30]
def q_8 : List Nat := [14,13,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,13,14]
def F_8 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_8 : goodPairs g_8 p_8 q_8 := goodPairs_of (by decide +kernel)
def W_8 : BT Decor := buildWiresBT 8 (mkBase p_8 q_8 r_8) [(0,0,1),(0,0,2),(0,1,2),(0,7,4),(1,8,3),(1,3,4),(0,0,10),(1,7,3),(0,12,4),(0,6,4),(3,14,0),(2,0,3),(3,16,2),(2,3,4),(3,18,7),(3,19,0),(0,3,4),(3,21,10),(1,5,3),(0,23,4),(2,0,13),(3,14,4),(1,14,3),(1,5,21),(2,5,3),(0,5,2),(3,30,0),(2,0,4),(3,32,1),(3,31,4),(0,2,3),(3,35,0),(3,5,2),(3,18,23),(0,30,4),(3,39,0),(0,5,4),(2,7,3),(3,42,0),(1,41,2),(1,41,3),(3,3,4),(1,7,4),(3,8,47),(3,30,1),(3,7,3),(0,0,4),(1,7,51),(3,8,4),(1,14,1),(3,14,2),(0,7,3),(3,56,12),(3,8,3),(1,8,0),(2,1,3),(1,60,51),(1,60,6),(0,2,10),(3,63,0),(1,5,4),(3,3,65),(3,18,2),(3,67,0),(0,3,65),(2,5,4),(3,41,4),(0,1,4),(3,50,0),(0,5,3),(2,0,21),(3,75,1),(0,2,65),(0,0,3),(1,53,3),(3,42,4),(1,16,21),(1,31,3),(0,31,4),(3,29,0),(3,70,0),(3,6,3),(3,30,4),(2,5,35),(3,60,2),(3,89,0),(1,18,5),(1,72,3),(0,0,92),(1,30,3),(2,2,3),(0,95,4),(3,96,0),(3,18,0),(3,60,4),(2,0,99),(3,95,0),(3,72,2),(3,102,0),(0,2,4),(3,16,1),(3,53,0),(3,37,4),(2,2,4),(1,108,5),(3,7,10),(0,16,4),(3,5,3),(3,17,4),(0,5,10),(1,7,78),(1,95,5),(2,2,21),(3,117,0),(2,5,21),(2,5,104),(3,95,5),(3,108,5),(3,108,0),(0,101,4),(1,15,3),(3,29,2),(3,18,5),(0,1,3),(3,128,2),(3,129,0),(2,1,4),(3,131,2),(3,132,0),(3,16,4),(3,12,4),(0,0,12),(1,51,3),(3,95,4)]
lemma W_8_ok : btAll (fun x => faithful p_8 q_8 x ∧ x.1 < 2^64) W_8 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_8 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_8 : BT (List (Nat × Nat)) := btOfList 3 al_8
set_option maxHeartbeats 0 in
lemma A_8_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_8 = g_8) A_8 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_8_0 : Slice r_8 g_8 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_1 : Slice r_8 g_8 (subcubeFast 0 2) 6 := by
  have hc : Lower (varsOf 29) 0xfffaa000fffaa000 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_2 : Slice r_8 g_8 (subcubeFast 0 4) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_3 : Slice r_8 g_8 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xe8e80000e8e80000 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_4 : Slice r_8 g_8 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_7
set_option maxHeartbeats 0 in
lemma sl_8_5 : Slice r_8 g_8 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_8_6 : Slice r_8 g_8 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xeaea8080eaea8080 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_4
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_7 : Slice r_8 g_8 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xecec8080ecec8080 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_4
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_8 : Slice r_8 g_8 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) 0xf8f88080f8f88080 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_4
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_8 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 0 2,6),some (subcubeFast 0 4,6),some (subcubeFast 8 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4),some (identDom 0 3,5),some (identDom 1 3,5),some (identDom 2 3,5)]
lemma S_8_ok : btAll (fun o => ∀ p, o = some p → Slice r_8 g_8 p.1 p.2) S_8 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_8_0) (forall_cons (fun _ h => by cases h; exact sl_8_1) (forall_cons (fun _ h => by cases h; exact sl_8_2) (forall_cons (fun _ h => by cases h; exact sl_8_3) (forall_cons (fun _ h => by cases h; exact sl_8_4) (forall_cons (fun _ h => by cases h; exact sl_8_5) (forall_cons (fun _ h => by cases h; exact sl_8_6) (forall_cons (fun _ h => by cases h; exact sl_8_7) (forall_cons (fun _ h => by cases h; exact sl_8_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_8 : BT (Option PoolSpec) := btOfList 7 [q 0 [16396,16397,41047],q 2 [],q 1 [16412,16413,192547],q 1 [],q 1 [12316,12317,49379],q 0 [],q 0 [16397,40968],q 5 [],q 1 [16396,16397,41047],q 2 [16396,16397,41047],q 0 [16405,266255],q 0 [16405,266252],q 0 [16406,16407],q 7 [],q 0 [16404,12453],q 1 [16404,12453],q 0 [16404,16405],q 1 [8480,35],q 0 [16398,16399],q 1 [12319,203],q 4 [],q 0 [12308,12309],q 1 [16396,86018],q 3 [],q 6 [],q 0 [16405,266248],q 0 [16396,86037],q 0 [12294,8435],q 0 [16388,8483],q 1 [16397,40991],q 0 [12310,12311],q 1 [16412,12323],q 0 [16388,12577],q 1 [16392,419],q 1 [16397,40960],q 0 [12298,20861],q 0 [16396,86026],q 0 [16392,426006],q 0 [12298,20863],q 0 [16396,86038],q 1 [16412,35],q 0 [12310,8311],q 0 [16396,16397],q 1 [16384,208925],q 0 [16397,40980],q 1 [16384,12453],q 0 [4300,12453],q 1 [16398,16399],q 2 [16398,16399],q 2 [16396,86018],q 0 [16398],q 0 [16392],q 2 [419],q 2 [16384],q 1 [16384],q 0 [4300],q 0 [16399],q 2 [16767],q 8 [],q 2 [4096],q 0 [16404],q 0 [16396],q 1 [16404],q 0 [16397],q 1 [16396,16397],q 2 [16396,16397],q 0 [16448],q 0 [12309],q 0 [16405],q 1 [8192],q 0 [8196],q 1 [16386],q 1 [16415],q 0 [12308],q 1 [31],q 2 [31],q 1 [12319],q 0 [12298],q 1 [12298,383],q 2 [383],q 1 [12309],q 0 [12296],q 0 [8212],q 1 [8212],q 2 [435],q 0 [16394],q 0 [16406],q 2 [16415],q 0 [12310],q 1 [12290],q 0 [12493],q 1 [16384,12493],q 2 [16384,12493],q 2 [16397,40960],q 1 [12310],q 2 [143],q 1 [16399],q 2 [16399],q 1 [16398],q 2 [16398],q 1 [16397],q 2 [16397],q 1 [16396],q 2 [16396],q 2 [16386],q 2 [12290],q 1 [12288],q 2 [12288]]
def B_8_2 : BT (List (List Nat)) := BT.empty
lemma B_8_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 2 xs.toFinset) B_8_2 := .empty
def U_8_3 : List Nat := []
def P_8_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_3
def N_8_3 : List NodeSpec := [([5,6,9,4],[],[]),([11,1,2,13],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_3 : checkNodesBT W_8 g_8 F_8 P_8_3 A_8 B_8_2 3 N_8_3 = true := by decide +kernel
def B_8_3 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_3
set_option maxRecDepth 500000 in
lemma B_8_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 3 xs.toFinset) B_8_3 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_2_ok C_8_3
def U_8_4 : List Nat := (r 0 6)
def P_8_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_4
def N_8_4 : List NodeSpec := [([22,5,0,1,2],[0],[]),([41,6,7,3,4],[1],[4]),([29,6,7,3,4],[1],[]),([48,0,1,2,3],[2],[]),([5,52,2,3,4],[3],[]),([57,0,1,2,4],[4],[]),([5,62,2,3,4],[5],[]),([40,58,1,2,4],[],[]),([40,1,2,9,4],[],[]),([5,61,2,3,4],[],[]),([58,1,59,2,4],[],[]),([5,0,2,9,4],[],[0]),([15,55,1,3,4],[],[]),([11,1,2,12,4],[],[0]),([15,54,2,3,4],[],[]),([53,5,6,3,4],[],[]),([50,43,1,2,4],[],[]),([31,49,2,3,4],[],[]),([0,1,44,45,4],[],[]),([5,6,3,12,4],[],[]),([46,43,1,2,4],[],[]),([15,1,17,3,4],[],[]),([43,1,2,21,4],[],[]),([40,1,2,3,4],[],[]),([0,1,2,38,4],[],[]),([36,37,1,3,4],[],[]),([32,1,34,2,3],[],[]),([31,33,2,3,4],[],[]),([16,5,2,12,4],[],[]),([16,1,2,28,4],[],[]),([15,1,2,27,4],[],[]),([15,26,1,2,3],[],[]),([25,1,2,3,4],[],[]),([0,1,2,24,10],[],[4]),([20,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_4 : checkNodesBT W_8 g_8 F_8 P_8_4 A_8 B_8_3 4 N_8_4 = true := by decide +kernel
def B_8_4 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_4
set_option maxRecDepth 500000 in
lemma B_8_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 4 xs.toFinset) B_8_4 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_3_ok C_8_4
def U_8_5_0 : List Nat := ([0,1,3]++r 5 42)
def P_8_5_0 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_5_0
def N_8_5_0 : List NodeSpec := [([41,6,1,2,3,4],[1],[0,4]),([29,6,1,2,3,4],[1],[0]),([53,0,72,1,2,3],[3],[4]),([75,5,1,2,3,4],[3],[]),([5,123,1,2,3,4],[3],[4]),([16,5,105,2,3,4],[3],[]),([111,5,1,2,3,4],[3],[]),([5,6,7,3,4],[3,1,5],[0,1,2,3,4]),([78,0,1,2,12,4],[5],[]),([16,0,1,2,12,4],[5],[0,1]),([31,30,1,2,3,4],[5],[0,1]),([15,6,1,104,3,4],[5],[]),([31,5,1,2,3,4],[5],[1]),([15,6,1,2,3,4],[5],[0]),([15,14,1,2,3,4],[5],[0]),([5,0,2,3,12,4],[5],[0]),([40,8,1,2,3,4],[5],[0]),([5,0,2,3,99,4],[5],[]),([53,5,0,2,3,4],[5],[0]),([53,0,8,1,2,3],[5],[2,4]),([15,51,1,2,3,4],[5],[0]),([31,5,7,2,3,4],[5,3],[]),e5 [64] [6],([64,0,1,63,3,4],[6],[]),([16,5,72,2,3,4],[7],[2]),([16,46,5,1,2,4],[7],[]),([16,46,0,1,2,134],[7],[]),([5,0,1,63,3,4],[7,6],[4]),([22,0,1,2],[7,0,8,9],[0,1,3]),([66,5,0,1,2,4],[10],[]),([5,0,1,2,69,4],[11],[]),([70,71,0,1,2,3],[12],[4]),([58,0,8,1,2,4],[13],[0]),([5,0,1,2,45,4],[14],[]),([0,1,2,45,4],[14,15],[4,5]),([41,0,1,2,3,65],[16],[4]),([40,72,1,2,3,4],[17],[]),([18,46,5,0,1,2],[18],[0]),([73,7,1,2,3,4],[19],[]),([5,51,72,2,3,4],[3,20],[]),([5,85,1,2,3,4],[5,20],[]),([101,51,1,2,3,4],[20],[5]),([53,0,7,72,2,3],[20],[]),([29,46,0,1,2,4],[20],[4]),([30,51,1,2,3,4],[20],[]),([74,0,1,2,23,4],[21],[4]),([75,76,1,2,3,4],[22],[]),([75,7,1,2,3,4],[22],[]),([119,75,1,2,3,4],[22],[]),a5 [127] [1,23] [4],([5,98,1,2,3,4],[3,23],[]),([36,5,1,2,3,4],[3,23],[0]),([16,60,5,2,3,4],[5,23],[]),([36,6,1,2,3,4],[5,23],[]),([16,30,1,2,3,4],[23],[]),([41,0,1,2,45,4],[23],[0,1,3,4]),e5 [124] [23],([16,5,1,2,23,4],[23],[]),([16,15,1,2,3,4],[23],[0]),([16,0,1,2,81,4],[23],[]),a5 [41] [1,24,23] [4],a5 [24] [3,1,24] [0,4],([5,11,1,2,3,4],[3,24,7],[]),([5,84,1,2,3,4],[5,24],[]),([51,0,1,2,3,134],[7,24],[]),e5 [93] [24],e5 [82] [24],([31,78,1,2,3,4],[24],[3,5]),e5 [88] [24,1],e5 [79] [24,5,3,1],([0,1,2,23,4,10],[24,13],[0,4]),a5 [39] [24,23] [0,2,4],a5 [122] [24,23] [4],([5,0,1,77,3,4],[25],[]),a5 [28] [26,23] [0,2],e5 [90] [27],([5,0,89,2,3,4],[27],[]),e5 [103] [28],e5 [110] [29],([29,112,0,1,2,4],[30],[4]),([58,0,7,1,2,4],[31],[]),([5,0,2,3,92,4],[7,32],[]),([15,0,7,1,3,4],[33],[]),([114,11,1,2,3,4],[24,7,34],[]),a5 [116] [3,23,35] [1,3],e5 [118] [36],e5 [120] [37],e5 [121] [1,38],e5 [119] [39],([40,7,1,2,3,4],[40],[]),([5,0,1,126,3,4],[24,41],[4]),([5,0,1,2,21,10],[42],[0]),a5 [52] [20,1,43] [0,1],e5 [114] [24,44],([51,0,1,2,45,4],[45,46],[3]),e5 [87] [],e5 [125] [],e5 [83] [],([16,86,6,1,2,4],[],[]),e5 [80] [],e5 [130] [],([46,101,0,1,2,4],[],[]),e5 [133] [],e5 [68] [],u5 [61] [],e5 [135] [],([32,31,1,2,3,4],[],[0,1]),([5,51,1,2,3,65],[],[]),e5 [136] [],([43,1,2,3,4],[],[0]),e5 [109] [],([18,0,1,2,23,4],[],[0]),e5 [45] [],([40,1,2,3,4],[],[]),e5 [40] [],e5 [43] [],([41,0,1,44,3,4],[],[0,1,3,4]),e5 [106] [],([16,5,7,2,3,4],[],[0,1,2]),([16,49,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_5_0 : checkNodesBT W_8 g_8 F_8 P_8_5_0 A_8 B_8_4 5 N_8_5_0 = true := by decide +kernel
def U_8_5_1 : List Nat := []
def P_8_5_1 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_5_1
def N_8_5_1 : List NodeSpec := [([5,6,72,2,3,4],[],[2,3]),a5 [107] [] [4],e5 [53] [],([31,0,72,2,3,4],[],[]),e5 [100] [],e5 [97] [],([101,0,1,2,21,4],[],[]),([16,5,1,2,21,4],[],[0]),e5 [113] [],e5 [115] [],([29,0,1,2,21,4],[],[0,4]),e5 [23] [],e5 [94] [],e5 [91] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_5_1 : checkNodesBT W_8 g_8 F_8 P_8_5_1 A_8 B_8_4 5 N_8_5_1 = true := by decide +kernel
def N_8_5 := N_8_5_0 ++ N_8_5_1
def B_8_5 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_5
set_option maxRecDepth 500000 in
lemma B_8_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 5 xs.toFinset) B_8_5 := by
  have hm0 := checkNodesBT_mem (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_4_ok C_8_5_0
  have hm1 := checkNodesBT_mem (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_4_ok C_8_5_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_8_6 : List Nat := ([1,3,5,7,13,18,20,22,23,24,33,34,42]++r 47 49)
def P_8_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_6
def N_8_6 : List NodeSpec := [u5 [16,105] [3,24,23,5],u5 [111,51] [7,24],e5 [51,137] [7,24],u5 [16,134] [7,24,5],a5 [16,72] [24,3,5,7] [0,1,2,3],u5 [16,60] [24,5,3,13,23],([18,46,0,1,2],[7,18,47,48],[0,1,3]),([75,1,2,3,4],[22,49,7],[0,1]),a5 [98] [23,3,1,20,50] [0,1,3,5],a5 [18,5] [23,3,50] [0,2],u5 [15,104] [20,51,52],a5 [15] [51,23,24,33,52] [0,3],([5,51,1,2,3,4],[5,7,54],[0,1,2,3,4,5]),a5 [51,72] [54,5,20] [0,1,3],a5 [41,51] [53,7,54,55] [0,1,3,4],([16,46,0,1,2,4],[7,56],[0,1,3,5]),a5 [46,5] [24,7,3,56] [0,2,4],a5 [138] [57,5,3,7,58] [0,1,2,3],a5 [5,104] [51,3,59] [0,1,3,4],a5 [41,5] [20,59,60] [0,1,3,4],a5 [75] [7,61,22,49] [0,1,3,5],a5 [5,21] [23,61,3,59] [0,2,4],([16,0,1,2,21,4],[61,7],[0,1,3,5]),a5 [41] [60,62,1,23,24] [0,1,2,3,4],a5 [5,10] [7,63,3,59] [0,2,4],([0,1,2,21,10],[42,64,65,23,20],[0,1,3]),a5 [111] [7,24,3,1,66] [0,1,3,5],a5 [5,23] [24,23,67,3] [0,2],a5 [5,65] [20,68,3,59] [0,2,4],([5,6,1,2,3,4],[5,59,69],[0,1,2,4]),a5 [32,7] [20,1,70,71] [0,3,5],a5 [53,7] [20,1,72] [0,1,3],a5 [74,5] [24,23,73] [0,1,3],a5 [31,7] [1,70,74] [0,1],a5 [31] [70,23,24,20,74,75] [0,1,2,3,4],a5 [50,7] [70,1,23,76] [0,2,3,4],a5 [101] [24,20,77,78,79] [0,3,5],a5 [23] [67,80,1,58,24,20] [0,4,5],a5 [5,35] [23,81,3,59] [0,2,4],a5 [30,5] [59,82] [0,2,4],a5 [30] [82,83,59,23,24,20] [0,2,4],a5 [123] [3,84,7,85] [0,3],a5 [70,5] [20,86] [0,2],a5 [53] [5,23,72,87] [0,1,3],a5 [29,5] [23,59,24,88] [0,2],a5 [16,7] [24,1,70,23,89] [0,1,2,3,4],([16,5,1,2,3,4],[89,5,7],[0,1,2]),a5 [137] [90,7,91,13,92,58,24] [2,4],a5 [11] [7,63,34,93] [0,1,3,5],([11,1,2,3,4],[34,93,7],[0,1,3,5]),a5 [29] [24,88,94,1,20] [0,2,4],a5 [36] [3,81,7,95] [0,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_6 : checkNodesBT W_8 g_8 F_8 P_8_6 A_8 B_8_5 6 N_8_6 = true := by decide +kernel
def B_8_6 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_6
set_option maxRecDepth 500000 in
lemma B_8_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 6 xs.toFinset) B_8_6 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_5_ok C_8_6
def U_8_7 : List Nat := ([1,3,5,7,20,23,24,50,53,54,56,59,61,63,71,89]++r 96 12)
def P_8_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_7
def N_8_7 : List NodeSpec := [a5 [51] [54,53,7,5] [0,1,2,3,4,5],a5 [5] [3,5,59,23,20] [0,2,4],a5 [46] [7,56,96,97] [0,1,2,3,4],a5 [18] [23,20,50,98,99] [0,1,2,3,4],a5 [10] [63,100,101,7,5,3,1] [0,1,2,3,4],a5 [21] [61,102,103,5,7,3,1] [0,1,2,3,4],a5 [32] [5,7,71,104] [0,3,5],a5 [16] [24,89,105,5,7] [0,1,3,5],a5 [78] [5,7,106,107] [3,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_7 : checkNodesBT W_8 g_8 F_8 P_8_7 A_8 B_8_6 7 N_8_7 = true := by decide +kernel
def B_8_7 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_7
set_option maxRecDepth 500000 in
lemma B_8_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 7 xs.toFinset) B_8_7 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_6_ok C_8_7
def U_8_8 : List Nat := [1,3,5]
def P_8_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_8
def N_8_8 : List NodeSpec := [a5 [] [5,3,1] [0,1,2,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_8 : checkNodesBT W_8 g_8 F_8 P_8_8 A_8 B_8_7 8 N_8_8 = true := by decide +kernel
def B_8_8 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_8
set_option maxRecDepth 500000 in
lemma B_8_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 8 xs.toFinset) B_8_8 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_7_ok C_8_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_8_ok : forestRootCheck r_8 g_8 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_8_in : bucketContainsBT B_8_8 r_8 = true := by decide +kernel
lemma low_8 : Lower r_8 g_8 9 := lower_of_forestBT root_8_ok B_8_8_ok root_8_in
def g_9 := 0xfc80fc80fc80fc80
def r_9 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_9 : Lower r_9 g_9 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_10 := 0xfac0fac0fac0fac0
def r_10 : List Nat := varsOf 15
def p_10 : List Nat := [6,6,7,7,9,9,11,11,12,12,13,14]
def q_10 : List Nat := [4,2,5,3,8,1,10,3,8,4,5,10]
def F_10 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_10 : goodPairs g_10 p_10 q_10 := goodPairs_of (by decide +kernel)
def W_10 : BT Decor := buildWiresBT 2 (mkBase p_10 q_10 r_10) []
lemma W_10_ok : btAll (fun x => faithful p_10 q_10 x ∧ x.1 < 2^64) W_10 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_10 : List (List (Nat × Nat)) := [[]]
def A_10 : BT (List (Nat × Nat)) := btOfList 1 al_10
set_option maxHeartbeats 0 in
lemma A_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_10 = g_10) A_10 := btAll_ofList (autos_of (by decide +kernel))
def S_10 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_10_ok : btAll (fun o => ∀ p, o = some p → Slice r_10 g_10 p.1 p.2) S_10 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_10 : BT (Option PoolSpec) := btOfList 1 []
def B_10_2 : BT (List (List Nat)) := BT.empty
lemma B_10_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 2 xs.toFinset) B_10_2 := .empty
def U_10_3 : List Nat := []
def P_10_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_10 r_10 S_10 ps_10 U_10_3
def N_10_3 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_3 : checkNodesBT W_10 g_10 F_10 P_10_3 A_10 B_10_2 3 N_10_3 = true := by decide +kernel
def B_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_3
set_option maxRecDepth 500000 in
lemma B_10_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 3 xs.toFinset) B_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_2_ok C_10_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck r_10 g_10 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT B_10_3 r_10 = true := by decide +kernel
lemma low_10 : Lower r_10 g_10 4 := lower_of_forestBT root_10_ok B_10_3_ok root_10_in
def g_11 := 0xfea8c000fea8c000
def r_11 : List Nat := varsOf 31
def p_11 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,23,23,25,25,25,26,26,26,27,28,28,28,29,30]
def q_11 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,22,7,24,17,9,24,18,10,11,24,20,12,13,22]
def F_11 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_11 : goodPairs g_11 p_11 q_11 := goodPairs_of (by decide +kernel)
def W_11 : BT Decor := buildWiresBT 8 (mkBase p_11 q_11 r_11) [(0,0,4),(1,1,2),(0,6,3),(1,5,7),(0,3,4),(0,2,4),(1,1,10),(2,11,3),(3,2,3),(1,0,7),(0,14,4),(2,6,3),(0,1,2),(3,17,3),(3,0,4),(1,19,7),(2,6,9),(1,2,4),(3,10,22),(0,0,3),(2,0,3),(1,25,1),(0,1,4),(1,27,2),(2,0,7),(1,5,2),(0,6,4),(1,25,17),(0,7,4),(1,5,1),(1,34,2),(0,35,3),(0,28,3),(2,0,37),(3,6,3),(3,39,4),(0,11,3),(3,24,6),(3,31,3),(1,3,4),(3,9,44),(1,1,4),(0,3,46),(0,0,47),(0,0,11),(1,13,10),(3,1,3),(3,51,4),(1,13,1),(0,53,4),(1,1,3),(3,10,55),(1,2,3),(3,1,57),(3,58,4),(0,1,3),(0,2,3),(1,61,1),(3,3,4),(3,7,4),(0,3,22),(2,0,65),(2,0,2),(1,67,1),(0,26,4),(0,0,6),(2,1,4),(3,1,4),(3,2,46),(0,68,4),(1,71,24),(3,24,46),(1,67,27),(1,24,2),(2,1,2),(2,2,1),(1,80,13),(1,24,27),(3,63,6),(3,10,1),(0,1,22),(1,24,1),(3,61,6),(0,86,4),(3,2,9),(1,24,17),(3,2,55),(1,71,25),(1,79,24),(0,57,4),(1,25,27),(3,25,46),(1,25,79),(3,6,4),(3,98,3),(1,13,27),(3,25,6),(2,34,2),(3,5,6),(1,1,9),(1,63,1),(2,3,4),(3,106,0),(0,1,44),(0,0,44),(2,2,4),(3,110,3),(3,110,0),(0,0,46),(3,13,4),(2,2,3),(3,115,1),(1,115,1),(2,1,3),(1,118,2),(3,2,4),(3,2,44),(3,13,1),(3,3,46),(2,0,1),(3,124,4),(3,24,4),(3,10,3),(3,25,4),(0,55,4),(3,80,3),(2,0,61),(0,0,2),(1,132,1),(0,0,1),(2,0,4)]
lemma W_11_ok : btAll (fun x => faithful p_11 q_11 x ∧ x.1 < 2^64) W_11 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_11 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_11 : BT (List (Nat × Nat)) := btOfList 1 al_11
set_option maxHeartbeats 0 in
lemma A_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_11 = g_11) A_11 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_11_0 : Slice r_11 g_11 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_1 : Slice r_11 g_11 (subcubeFast 4 16) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_2 : Slice r_11 g_11 (subcubeFast 2 16) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_3 : Slice r_11 g_11 (subcubeFast 1 8) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_4 : Slice r_11 g_11 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) 0xee88cc00ee88cc00 5 := carry_of (swaps := [(1,2),(2,4)]) (by decide +kernel) low_4
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_5 : Slice r_11 g_11 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xececc0c0ececc0c0 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_9
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_6 : Slice r_11 g_11 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) 0xf8f8c0c0f8f8c0c0 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_9
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_7 : Slice r_11 g_11 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 27) 0xffaacc00ffaacc00 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_8 : Slice r_11 g_11 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 29) 0xffaaf000ffaaf000 4 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
def S_11 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 4 16,4),some (subcubeFast 2 16,4),some (subcubeFast 1 8,4),some (identDom 1 2,5),some (identDom 1 3,5),some (identDom 2 3,5),some (subcubeFast 0 4,4),some (subcubeFast 0 2,4)]
lemma S_11_ok : btAll (fun o => ∀ p, o = some p → Slice r_11 g_11 p.1 p.2) S_11 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_11_0) (forall_cons (fun _ h => by cases h; exact sl_11_1) (forall_cons (fun _ h => by cases h; exact sl_11_2) (forall_cons (fun _ h => by cases h; exact sl_11_3) (forall_cons (fun _ h => by cases h; exact sl_11_4) (forall_cons (fun _ h => by cases h; exact sl_11_5) (forall_cons (fun _ h => by cases h; exact sl_11_6) (forall_cons (fun _ h => by cases h; exact sl_11_7) (forall_cons (fun _ h => by cases h; exact sl_11_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_11 : BT (Option PoolSpec) := btOfList 6 [q 0 [16392,16393,90155],q 4 [12312,28674],q 2 [],q 0 [],q 1 [],q 3 [],q 5 [],q 0 [16389,188428],q 8 [],q 0 [16388,8301],q 7 [],q 0 [16393,90124],q 0 [8196,8197],q 4 [12312],q 4 [24576],q 0 [16390,16391],q 0 [16388,16389],q 0 [16389,188427],q 4 [],q 4 [12314],q 0 [16389,188515],q 0 [16388,110689],q 0 [16392,4139],q 0 [16393,90116],q 0 [8198,98621],q 4 [12288],q 0 [16389,188519],q 4 [12290],q 0 [12299,4149],q 6 [],q 0 [8197],q 0 [4365],q 0 [8196],q 0 [4193],q 0 [8198],q 0 [16399],q 0 [16390],q 0 [16395],q 0 [16483],q 0 [16389],q 0 [16392,12331],q 0 [12299],q 0 [16388],q 0 [4197],q 0 [12293],q 0 [16487],q 0 [16396],q 0 [12296],q 0 [12292],q 0 [4106,12611]]
def B_11_2 : BT (List (List Nat)) := BT.empty
lemma B_11_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 2 xs.toFinset) B_11_2 := .empty
def U_11_3 : List Nat := []
def P_11_3 : BT (Option BoundPool) := buildPoolsSubBT 6 W_11 r_11 S_11 ps_11 U_11_3
def N_11_3 : List NodeSpec := [([1,2,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_3 : checkNodesBT W_11 g_11 F_11 P_11_3 A_11 B_11_2 3 N_11_3 = true := by decide +kernel
def B_11_3 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_3
set_option maxRecDepth 500000 in
lemma B_11_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 3 xs.toFinset) B_11_3 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_2_ok C_11_3
def U_11_4 : List Nat := (r 0 4)
def P_11_4 : BT (Option BoundPool) := buildPoolsSubBT 6 W_11 r_11 S_11 ps_11 U_11_4
def N_11_4 : List NodeSpec := [([23,24,0,1,3],[0],[]),([25,23,0,1,3],[0],[]),([29,17,6,3,4],[1],[]),([5,1,30,31,3],[2],[]),([13,5,1,31,3],[2],[]),([1,2,8,3,4],[3],[0]),([5,1,2,33,3],[3],[]),([0,32,6,3,4],[],[]),([43,5,1,2,3],[],[]),([42,0,17,3,4],[],[]),([18,0,7,6,4],[],[]),([13,0,41,11,4],[],[]),([5,1,2,40,3],[],[]),([38,1,28,3,4],[],[]),([5,1,2,7,9],[],[0]),([5,1,2,36,4],[],[]),([12,13,0,11,4],[],[]),([0,26,28,3,4],[],[]),([21,5,1,2,3],[],[]),([1,2,20,3,4],[],[]),([16,18,0,6,4],[],[]),([1,2,7,15,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_4 : checkNodesBT W_11 g_11 F_11 P_11_4 A_11 B_11_3 4 N_11_4 = true := by decide +kernel
def B_11_4 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_4
set_option maxRecDepth 500000 in
lemma B_11_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 4 xs.toFinset) B_11_4 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_3_ok C_11_4
def U_11_5 : List Nat := ([0]++r 2 27)
def P_11_5 : BT (Option BoundPool) := buildPoolsSubBT 6 W_11 r_11 S_11 ps_11 U_11_5
def N_11_5 : List NodeSpec := [([5,1,2,9,3,104],[2],[]),([0,60,2,62,3,4],[2],[]),([24,0,1,2,7,4],[3],[]),e5 [92] [3],([25,0,1,2,47,4],[3],[]),([29,1,2,7,3,4],[3],[]),([25,0,1,2,7,4],[3],[]),e5 [75] [3],([19,1,2,7,3,4],[3],[0]),([13,0,1,31,3,4],[2,4],[0]),([13,0,11,3,4],[2,4],[0]),([5,1,2,31,3],[2,4,3],[0,1]),([103,5,1,2,3,4],[3,4],[]),([39,5,1,2,3,4],[4],[0]),([89,5,1,2,9,3],[4],[]),e5 [103] [4],([13,81,0,1,3,4],[4],[]),e5 [100] [4],e5 [74] [4],([13,0,1,3,50,4],[4],[]),([87,0,1,6,3,4],[4],[]),e5 [77] [4],e5 [54] [4],e5 [56] [4],e5 [59] [4],([5,1,2,31,6,3],[4,2],[]),([23,0,1,3],[4,2,0],[0]),([13,0,1,11,3,4],[2,5],[]),([13,0,60,6,3,4],[2,5],[]),([13,5,1,6,3,4],[2,5],[0]),([13,19,1,6,3,4],[2,5],[]),e5 [7] [3,5],e5 [83] [3,5],e5 [99] [3,5],u5 [33] [3,5,4,2],([5,1,2,6,9,3],[4,2,5],[0]),([13,51,0,6,3,4],[4,5],[]),([0,60,61,6,3,4],[4,5],[]),([45,0,1,2,9],[4,5,2],[]),e5 [101] [5],([1,2,7,14,3,4],[5],[0]),([71,0,86,2,3,4],[5],[]),([5,1,30,6,3,4],[5,2],[0]),([45,0,1,2],[5,2,4],[]),e5 [64] [5,3],([5,1,2,35,3,4],[5,3,4],[0]),([5,1,2,7,3,4],[5,4],[0]),e5 [41] [3,5,6],([0,1,52,2,9,3],[6,4],[]),([48,0,1,2,47,4],[6,2,7],[]),([12,0,2,11,3,4],[2,4,8],[0]),([91,0,1,10,3,4],[4,8],[]),([49,0,2,11,3,4],[8],[]),([24,0,1,2,47,4],[8,2,3],[]),([25,0,1,28,3,4],[2,9],[0]),([24,0,1,28,3,4],[9],[]),([0,1,2,31,9,3],[4,8,2,10,5],[]),([5,0,1,2,31,3],[8,10,3,4],[]),e5 [88] [8,10,4],([0,1,2,7,9,4],[8,10,4],[0]),([0,1,37,28,3,4],[9,2,4,10],[0,1]),([0,27,68,2,3,4],[10],[]),([0,17,1,78,3,4],[10],[]),([0,27,53,2,3,4],[10],[]),([0,27,1,2,3,94],[10,8,4],[]),([66,0,1,2,65,4],[11],[]),([0,17,7,6,3,4],[12,4,13,10],[0]),([70,0,17,6,3,4],[10,14],[]),([71,25,72,0,2,3],[15],[1]),([71,72,24,0,2,3],[15],[1]),([24,0,27,2,3,46],[16],[1]),([25,0,27,2,3,46],[16],[1]),([73,24,0,1,3,4],[17],[]),([25,73,0,1,3,4],[17],[]),([18,0,6,3,4],[18,4],[0]),([16,0,17,6,3,4],[18,4,19,10],[0]),e5 [76] [20],e5 [82] [21],([84,24,0,2,3,4],[22],[]),([25,84,0,2,3,4],[22],[]),([24,0,85,2,3,4],[10,4,23],[]),([25,0,85,2,3,4],[23],[]),e5 [93] [24],([24,0,17,6,3,4],[10,12,25],[0]),e5 [96] [26],([25,0,17,6,3,4],[4,12,27],[0]),([0,60,53,2,3,4],[28,2],[]),([79,0,26,2,3,4],[],[]),([39,19,1,2,3,4],[],[]),e5 [97] [],([19,1,53,2,3,4],[],[]),([5,1,53,2,3,4],[],[]),([91,19,1,2,3,4],[],[]),e5 [90] [],u5 [40] [],([63,0,1,2,7,4],[],[]),([0,27,26,2,3,4],[],[0]),u5 [43] [],([102,5,1,2,3,4],[],[]),u5 [42] [],e5 [95] [],([29,1,2,6,3,4],[],[0]),u5 [21] [],u5 [32] [],e5 [69] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_5 : checkNodesBT W_11 g_11 F_11 P_11_5 A_11 B_11_4 5 N_11_5 = true := by decide +kernel
def B_11_5 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_5
set_option maxRecDepth 500000 in
lemma B_11_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 5 xs.toFinset) B_11_5 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_4_ok C_11_5
def U_11_6 : List Nat := (r 2 9++[12]++r 15 4++[22,23,25]++r 27 23)
def P_11_6 : BT (Option BoundPool) := buildPoolsSubBT 6 W_11 r_11 S_11 ps_11 U_11_6
def N_11_6 : List NodeSpec := [([0,1,2,9,44],[2,4,5],[0]),([13,0,1,10,3,4],[2,4,5],[0]),([0,1,119,3,4],[2,5],[]),([0,116,2,3,4],[2,5],[]),([107,1,2,3,4],[2,5],[]),([0,108,2,3,4],[2,5],[]),([109,1,2,3,4],[2,5],[]),([113,1,2,3,4],[2,5],[]),([112,1,2,3,4],[2,5],[]),([5,1,2,3,4],[2,5],[]),([5,1,34,2,3,4],[2,5,4],[0,1]),([106,5,1,2,3],[4,5],[]),e5 [133] [4,5],([106,63,0,1,2],[4,5],[0]),([121,0,1,3,4],[5,2],[]),([13,5,1,2,3,4],[5,2,4],[0]),u5 [18] [5,3,2,4],e5 [111] [5,3,4,2],([123,0,1,2,4],[5,4],[]),([131,1,2,3,4],[5,4],[]),e5 [117] [5,4],([5,1,2,9,3,4],[5,4,2],[]),([5,1,2,9,3],[5,4,2],[0,1]),e5 [9] [5,4,2],([0,60,2,55,4],[2,5,6],[]),u5 [9,104] [2,6],([0,1,2,47,4],[2,4,7],[0,1]),u5 [47] [5,7,4,2],([0,60,2,6,3,4],[2,5,4,8],[0,1]),([79,51,0,2,3,4],[2,5,8,4],[1]),e5 [67,72] [2,8,4],u5 [11] [2,8,5,3,4],u5 [62] [5,3,4,8],u5 [67,27] [2,4,10],e5 [125] [2,5,4,10],e5 [34] [2,5,8,4,10],e5 [13,72] [2,8,4,10],u5 [13,27] [2,10,4],([13,0,1,6,3,4],[2,10,4,5],[0]),([0,1,28,3,4],[2,10,9,4],[0,1]),u5 [70,6] [3,10],u5 [16,6] [4,2,8,10],u5 [31,6] [4,2,10],([13,120,0,1,3,4],[4,2,10],[]),u5 [6,9] [4,8,2,10,5],e5 [13,114] [4,10],a5 [129] [5,2,4,10] [1],e5 [13] [5,2,8,4,10],e5 [105] [5,2,8,4,10],a5 [91] [5,2,8,10] [0,1],u5 [52] [5,3,2,4,10,6],u5 [6] [5,3,4,2,8,10],a5 [31] [5,3,4,2,10] [0,1],u5 [98] [5,3,4,2,10,8],u5 [7] [5,3,8,2,10],u5 [39] [5,3,10,8,4],e5 [104] [8,2,5,3,4,10],u5 [63,6] [8,2,10,4,5],a5 [27,57] [10,4,2] [0,1],e5 [120,55] [10,4,2],([71,72,0,2,3],[4,2,15],[0,1]),([0,27,2,3,46],[2,4,16],[0,1]),([73,0,1,3,4],[4,2,17],[0]),([0,17,6,3,4],[4,10,12,18],[0]),([84,0,2,3,4],[2,4,22],[0]),([0,85,2,3,4],[2,4,23],[0]),u5 [53] [8,28,5,10,4],a5 [13,9] [4,5,29] [1],a5 [89,9] [4,29] [0,1],e5 [89] [5,3,2,8,29,4],u5 [13,51] [6,4,2,29,5],e5 [13,122] [8,29,4,10],e5 [13,53] [10,2,4,29],([5,1,2,6,3,4],[2,4,5,30],[0,1]),u5 [24,6] [5,10,30],u5 [25,6] [8,2,10,4,5,30],u5 [5,6] [8,2,10,4,5,30],u5 [7,6] [30,2,4,8,10,5],([19,1,2,6,3,4],[30,4,2,5],[0,1]),u5 [68] [5,31,10,8,4],a5 [24,17] [4,5,2,32] [0,1],u5 [25,17] [4,5,32],a5 [86] [5,33,8,4,10] [0,1],u5 [25,79] [2,5,34,27],u5 [79,24] [5,10,4,34,25],([63,19,1,2,3,4],[35,2,4,5],[]),u5 [71,25] [4,5,36],u5 [71,24] [5,2,36],a5 [120,24] [5,4,10,37] [1],a5 [25,120] [5,4,10,37] [1],e5 [126] [5,38,2,8,4,10],a5 [25,46] [5,4,39] [0,1],a5 [24,46] [8,2,5,39] [0,1],e5 [127] [5,2,8,4,40],u5 [13,60] [2,4,41,5,10],([13,19,1,2,3,4],[41,2,5,4],[0]),a5 [25,27] [2,5,42] [0,1],a5 [24,27] [2,5,42] [0,1],u5 [26] [5,43,8,4,10],([19,1,2,3,55,4],[5,44,2,4],[0]),e5 [128] [45,5,2,8,4,10],([19,1,2,9,3,4],[46,5,2,4],[]),a5 [60,61] [47,5,48,4,2] [0,1],e5 [130] [5,49,4,8]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_6 : checkNodesBT W_11 g_11 F_11 P_11_6 A_11 B_11_5 6 N_11_6 = true := by decide +kernel
def B_11_6 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_6
set_option maxRecDepth 500000 in
lemma B_11_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 6 xs.toFinset) B_11_6 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_5_ok C_11_6
def U_11_7 : List Nat := (r 2 5++[8,10,18,29,30,32,34,36,37,39,41,42,46,48])
def P_11_7 : BT (Option BoundPool) := buildPoolsSubBT 6 W_11 r_11 S_11 ps_11 U_11_7
def N_11_7 : List NodeSpec := [([19,1,2,3,4],[3,4,2],[0,1]),a5 [44] [2,4,5,3] [0,1],([5,1,2,3,4],[2,5,4,3],[0,1]),a5 [134] [3,4,5,2] [1],a5 [5] [4,2,5,3] [0,1],u5 [135] [4,3,2,5],u5 [106] [4,3,5,2],a5 [63] [5,2,4] [0,1],a5 [25] [5,2,4,3] [0,1],a5 [24] [5,2,4,3] [0,1],a5 [118] [2,5,4,6] [0,1],a5 [55] [5,2,8,4] [0,1],a5 [67] [4,2,5,3,10] [0,1],a5 [6] [2,8,4,10,5,30] [0,1],u5 [17] [4,5,2,32],a5 [79] [2,5,4,10,34,18] [0,1],a5 [71] [4,3,5,2,36] [0,1],a5 [120] [5,4,2,37] [0,1],a5 [46] [2,4,39,5,3] [0,1],a5 [13] [5,41,2,10,4,29] [0,1],a5 [27] [2,5,4,42] [0,1],a5 [9] [2,46,5,4] [0,1],a5 [60] [2,3,5,48,4] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_7 : checkNodesBT W_11 g_11 F_11 P_11_7 A_11 B_11_6 7 N_11_7 = true := by decide +kernel
def B_11_7 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_7
set_option maxRecDepth 500000 in
lemma B_11_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 7 xs.toFinset) B_11_7 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_6_ok C_11_7
def U_11_8 : List Nat := [3]
def P_11_8 : BT (Option BoundPool) := buildPoolsSubBT 6 W_11 r_11 S_11 ps_11 U_11_8
def N_11_8 : List NodeSpec := [a5 [] [3] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_8 : checkNodesBT W_11 g_11 F_11 P_11_8 A_11 B_11_7 8 N_11_8 = true := by decide +kernel
def B_11_8 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_8
set_option maxRecDepth 500000 in
lemma B_11_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 8 xs.toFinset) B_11_8 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_7_ok C_11_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck r_11 g_11 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT B_11_8 r_11 = true := by decide +kernel
lemma low_11 : Lower r_11 g_11 9 := lower_of_forestBT root_11_ok B_11_8_ok root_11_in
def g_12 := 0x2222222222222222
def r_12 : List Nat := varsOf 3
set_option maxHeartbeats 0 in
lemma low_12 : Lower r_12 g_12 1 := count_of (essPairs := [(VAR 0,0,1),(VAR 1,1,3)]) (by decide +kernel)
def g_13 := 0x8e8e8e8e8e8e8e8e
def r_13 : List Nat := varsOf 7
def p_13 : List Nat := [1,2,7,7]
def q_13 : List Nat := [0,0,6,5]
def F_13 : Nat := fullMask 4
set_option maxHeartbeats 0 in
lemma gp_13 : goodPairs g_13 p_13 q_13 := goodPairs_of (by decide +kernel)
def W_13 : BT Decor := buildWiresBT 2 (mkBase p_13 q_13 r_13) []
lemma W_13_ok : btAll (fun x => faithful p_13 q_13 x ∧ x.1 < 2^64) W_13 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_13 : List (List (Nat × Nat)) := [[]]
def A_13 : BT (List (Nat × Nat)) := btOfList 1 al_13
set_option maxHeartbeats 0 in
lemma A_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_13 = g_13) A_13 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_13_0 : Slice r_13 g_13 (subcubeFast 1 0) 1 := by
  have hc : Lower (varsOf 6) 0xc0c0c0c0c0c0c0c 1 := carry_of (swaps := [(0,2),(1,2)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_1 : Slice r_13 g_13 (subcubeFast 0 1) 1 := by
  have hc : Lower (varsOf 6) 0x3030303030303030 1 := carry_of (swaps := [(0,2)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_2 : Slice r_13 g_13 (subcubeFast 2 0) 1 := by
  have hc : Lower (varsOf 5) 0xa0a0a0a0a0a0a0a 1 := carry_of (swaps := [(1,2)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_3 : Slice r_13 g_13 (subcubeFast 0 2) 1 := by
  have hc : Lower (varsOf 5) 0x5050505050505050 1 := carry_of (swaps := [(0,1),(1,2)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
def S_13 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,1),some (subcubeFast 0 1,1),some (subcubeFast 2 0,1),some (subcubeFast 0 2,1)]
lemma S_13_ok : btAll (fun o => ∀ p, o = some p → Slice r_13 g_13 p.1 p.2) S_13 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_13 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 1 [],q 2 [],q 3 []]
def B_13_2 : BT (List (List Nat)) := BT.empty
lemma B_13_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 2 xs.toFinset) B_13_2 := .empty
def U_13_3 : List Nat := (r 0 4)
def P_13_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_13 r_13 S_13 ps_13 U_13_3
def N_13_3 : List NodeSpec := [([0,1,2],(r 0 4),[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_3 : checkNodesBT W_13 g_13 F_13 P_13_3 A_13 B_13_2 3 N_13_3 = true := by decide +kernel
def B_13_3 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_3
set_option maxRecDepth 500000 in
lemma B_13_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 3 xs.toFinset) B_13_3 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_2_ok C_13_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck r_13 g_13 [(VAR 0,0,1),(VAR 1,0,2),(VAR 2,1,5)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT B_13_3 r_13 = true := by decide +kernel
lemma low_13 : Lower r_13 g_13 4 := lower_of_forestBT root_13_ok B_13_3_ok root_13_in
def g_14 := 0x202020202020202
def r_14 : List Nat := varsOf 7
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 2 := count_of (essPairs := [(VAR 0,0,1),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel)
def g_15 := 0xe8fee8fee8fee8fe
def r_15 : List Nat := varsOf 15
def p_15 : List Nat := [1,2,4,11,11,13,13,14,14]
def q_15 : List Nat := [0,0,0,10,9,12,9,12,10]
def F_15 : Nat := fullMask 9
set_option maxHeartbeats 0 in
lemma gp_15 : goodPairs g_15 p_15 q_15 := goodPairs_of (by decide +kernel)
def W_15 : BT Decor := buildWiresBT 5 (mkBase p_15 q_15 r_15) [(3,0,3),(1,2,1),(3,4,5),(1,0,2),(1,0,1),(0,8,3),(2,5,0),(3,10,3),(3,2,3),(3,8,3),(1,13,2),(1,2,3),(0,8,15),(0,7,3),(2,8,3),(1,18,2),(1,12,0),(3,2,8),(3,1,3),(1,8,2),(0,23,3),(1,0,3),(3,2,25),(3,5,3)]
lemma W_15_ok : btAll (fun x => faithful p_15 q_15 x ∧ x.1 < 2^64) W_15 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_15 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)]]
def A_15 : BT (List (Nat × Nat)) := btOfList 3 al_15
set_option maxHeartbeats 0 in
lemma A_15_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_15 = g_15) A_15 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_15_0 : Slice r_15 g_15 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) 0xc0fcc0fcc0fcc0fc 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_1 : Slice r_15 g_15 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) 0xa0faa0faa0faa0fa 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_2 : Slice r_15 g_15 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) 0x88ee88ee88ee88ee 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_3 : Slice r_15 g_15 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_15_4 : Slice r_15 g_15 (subcubeFast 0 1) 2 := by
  have hc : Lower (varsOf 14) 0x300030003000300 2 := carry_of (swaps := [(0,3)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_5 : Slice r_15 g_15 (subcubeFast 0 2) 2 := by
  have hc : Lower (varsOf 13) 0x500050005000500 2 := carry_of (swaps := [(0,1),(1,3)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_6 : Slice r_15 g_15 (subcubeFast 0 4) 2 := by
  have hc : Lower (varsOf 11) 0x1100110011001100 2 := carry_of (swaps := [(0,1),(1,2),(2,3)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
def S_15 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 0 8,4),some (subcubeFast 0 1,2),some (subcubeFast 0 2,2),some (subcubeFast 0 4,2)]
lemma S_15_ok : btAll (fun o => ∀ p, o = some p → Slice r_15 g_15 p.1 p.2) S_15 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_15_0) (forall_cons (fun _ h => by cases h; exact sl_15_1) (forall_cons (fun _ h => by cases h; exact sl_15_2) (forall_cons (fun _ h => by cases h; exact sl_15_3) (forall_cons (fun _ h => by cases h; exact sl_15_4) (forall_cons (fun _ h => by cases h; exact sl_15_5) (forall_cons (fun _ h => by cases h; exact sl_15_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_15 : BT (Option PoolSpec) := btOfList 5 [q 4 [4105],q 4 [],q 4 [8197],q 1 [],q 0 [12322,8265],q 0 [],q 5 [9],q 3 [],q 2 [],q 1 [12291,20499],q 5 [],q 6 [],q 0 [12299],q 2 [12289],q 0 [4105],q 1 [9],q 0 [8226],q 1 [8226],q 2 [4097],q 2 [49],q 0 [8225],q 1 [8225],q 1 [12311],q 2 [12311],q 0 [12320],q 1 [12320],q 0 [12322],q 0 [12297],q 1 [12299],q 1 [12289]]
def B_15_1 : BT (List (List Nat)) := BT.empty
lemma B_15_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 1 xs.toFinset) B_15_1 := .empty
def U_15_2 : List Nat := [0]
def P_15_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_15 r_15 S_15 ps_15 U_15_2
def N_15_2 : List NodeSpec := [([6,1,7],[0],[]),([9,7,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_2 : checkNodesBT W_15 g_15 F_15 P_15_2 A_15 B_15_1 2 N_15_2 = true := by decide +kernel
def B_15_2 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_2
set_option maxRecDepth 500000 in
lemma B_15_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 2 xs.toFinset) B_15_2 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_1_ok C_15_2
def U_15_3 : List Nat := (r 0 10)
def P_15_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_15 r_15 S_15 ps_15 U_15_3
def N_15_3 : List NodeSpec := [([0,20,1,5],[0],[]),([0,11,1,2],[1],[]),([12,0,8,5],[2],[4]),([0,1,17,5],[3],[1]),([0,1,8,19],[4],[]),([8,7,5,3],[3,5,0,6],[0,1,3]),([12,22,0,5],[3,8],[]),([6,0,1,2],[7,8,9],[0,1]),([0,1,14,3],[],[]),([0,1,16,2],[],[]),([21,22,0,2],[],[]),([0,1,14],[],[]),([0,1,2,24],[],[]),([0,1,9,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_3 : checkNodesBT W_15 g_15 F_15 P_15_3 A_15 B_15_2 3 N_15_3 = true := by decide +kernel
def B_15_3 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_3
set_option maxRecDepth 500000 in
lemma B_15_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 3 xs.toFinset) B_15_3 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_2_ok C_15_3
def U_15_4 : List Nat := ([1,3,5,7,8]++r 10 18)
def P_15_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_15 r_15 S_15 ps_15 U_15_4
def N_15_4 : List NodeSpec := [([0,1,9,2,3],[1],[]),([27,0,1,2,3],[5],[3]),([12,22,0,1,2],[10,3,11,8],[0]),([12,0,20,1,2],[11,5,8],[]),([12,0,1,8,2],[1,3,10,11,12,8],[0,2,4]),([12,0,1,7,3],[8,12,7],[2]),([12,0,1,7],[11,12],[1,2]),([0,20,1,2,3],[12,1],[]),([26,0,1,2],[3,10,11,13],[]),([0,1,7,5,3],[14,15,11],[0,1,2,3]),([21,0,1,2,3],[11,7,16,17,18],[0,2,4]),([0,20,1,2],[1,12,3,10,19],[0]),([0,1,2,23,3],[20,1,21,10,18,11,7],[0]),([27,0,1,2],[5,10,1,11,22,23],[3]),([0,1,9,8,2],[24,3,7],[]),([0,1,9,2],[24,25,8,11],[1,3]),([18,0,1,8,2],[3,18,26],[0]),([0,1,8,2,15],[27,1,3,10,8,11],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_4 : checkNodesBT W_15 g_15 F_15 P_15_4 A_15 B_15_3 4 N_15_4 = true := by decide +kernel
def B_15_4 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_4
set_option maxRecDepth 500000 in
lemma B_15_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 4 xs.toFinset) B_15_4 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_3_ok C_15_4
def U_15_5 : List Nat := [1,3,5,7,8,11,12,13,18,28,29]
def P_15_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_15 r_15 S_15 ps_15 U_15_5
def N_15_5 : List NodeSpec := [([0,1,8,2,3],[5,3,7,1,18],[0,1,3,4]),([12,0,1,2,3],[7,8,12,28],[0,2]),([12,0,1,2],[11,12,28,7,8],[0,2]),([0,1,2,25],[5,7,29,13],[0,1,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_5 : checkNodesBT W_15 g_15 F_15 P_15_5 A_15 B_15_4 5 N_15_5 = true := by decide +kernel
def B_15_5 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_5
set_option maxRecDepth 500000 in
lemma B_15_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 5 xs.toFinset) B_15_5 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_4_ok C_15_5
def U_15_6 : List Nat := [3,5,7,8]
def P_15_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_15 r_15 S_15 ps_15 U_15_6
def N_15_6 : List NodeSpec := [([0,1,2,3],[5,3,8,7],[0,1,2,3,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_6 : checkNodesBT W_15 g_15 F_15 P_15_6 A_15 B_15_5 6 N_15_6 = true := by decide +kernel
def B_15_6 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_6
set_option maxRecDepth 500000 in
lemma B_15_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 6 xs.toFinset) B_15_6 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_5_ok C_15_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_15_ok : forestRootCheck r_15 g_15 [(VAR 0,0,1),(VAR 1,0,2),(VAR 2,0,4),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_15_in : bucketContainsBT B_15_6 r_15 = true := by decide +kernel
lemma low_15 : Lower r_15 g_15 7 := lower_of_forestBT root_15_ok B_15_6_ok root_15_in
def g_16 := 0x808080808080808
def r_16 : List Nat := varsOf 7
set_option maxHeartbeats 0 in
lemma low_16 : Lower r_16 g_16 2 := count_of (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,3,7)]) (by decide +kernel)
def g_17 := 0x80e880e880e880e8
def r_17 : List Nat := varsOf 15
def p_17 : List Nat := [3,3,5,5,6,6,15,15,15]
def q_17 : List Nat := [2,1,4,1,4,2,14,13,11]
def F_17 : Nat := fullMask 9
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 5 (mkBase p_17 q_17 r_17) [(0,0,1),(2,1,3),(0,0,2),(1,5,6),(0,1,2),(1,8,3),(2,2,3),(1,10,4),(2,0,3),(3,6,1),(3,8,0),(1,14,3),(2,8,3),(3,16,0),(0,0,3),(1,8,18),(0,4,2),(1,20,3),(1,4,3),(3,8,3),(3,23,0),(3,5,2),(3,10,0),(0,2,3),(3,27,0),(3,12,1),(2,4,3)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^64) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_17 : BT (List (Nat × Nat)) := btOfList 3 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) 0xc0fcc0fcc0fcc0fc 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) 0xa0faa0faa0faa0fa 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) 0x88ee88ee88ee88ee 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 1 0) 2 := by
  have hc : Lower (varsOf 14) 0xc000c000c000c0 2 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 2 0) 2 := by
  have hc : Lower (varsOf 13) 0xa000a000a000a0 2 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (subcubeFast 4 0) 2 := by
  have hc : Lower (varsOf 11) 0x88008800880088 2 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
def S_17 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 8 0,4),some (subcubeFast 1 0,2),some (subcubeFast 2 0,2),some (subcubeFast 4 0,2)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_17 : BT (Option PoolSpec) := btOfList 5 [q 0 [],q 1 [],q 3 [],q 0 [12298,16425],q 4 [],q 2 [],q 4 [8196],q 5 [8192],q 1 [12323,95],q 6 [4],q 5 [],q 0 [12298],q 2 [43],q 0 [12296],q 0 [8208],q 1 [8208],q 2 [4096],q 6 [],q 0 [8196],q 1 [12323],q 0 [12305],q 1 [12305],q 1 [35],q 2 [35],q 1 [12290],q 0 [12306],q 1 [12306],q 1 [8192],q 2 [12290],q 1 [12288],q 2 [12288]]
def B_17_1 : BT (List (List Nat)) := BT.empty
lemma B_17_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 1 xs.toFinset) B_17_1 := .empty
def U_17_2 : List Nat := [0]
def P_17_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_17 r_17 S_17 ps_17 U_17_2
def N_17_2 : List NodeSpec := [([4,7,2],[0],[]),([4,6,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_2 : checkNodesBT W_17 g_17 F_17 P_17_2 A_17 B_17_1 2 N_17_2 = true := by decide +kernel
def B_17_2 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_2
set_option maxRecDepth 500000 in
lemma B_17_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 2 xs.toFinset) B_17_2 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_1_ok C_17_2
def U_17_3 : List Nat := (r 0 10)
def P_17_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_17 r_17 S_17 ps_17 U_17_3
def N_17_3 : List NodeSpec := [([4,0,2,9],[0],[0]),([12,5,4,2],[0,2],[]),([11,0,1,2],[1,2,3],[1,3]),([0,1,2,15],[4],[]),([12,4,8,2],[6],[2]),([4,6,8,3],[5,6,0,7],[0,2,4]),([24,8,1,2],[8],[]),([4,0,25,2],[9],[]),([12,13,1,2],[],[]),([17,1,2],[],[]),([0,1,19,2],[],[]),([0,1,2,21],[],[]),([17,1,2,3],[],[]),([0,1,2,22],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_3 : checkNodesBT W_17 g_17 F_17 P_17_3 A_17 B_17_2 3 N_17_3 = true := by decide +kernel
def B_17_3 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_3
set_option maxRecDepth 500000 in
lemma B_17_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 3 xs.toFinset) B_17_3 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_2_ok C_17_3
def U_17_4 : List Nat := ([0,1,2,4,5]++r 10 18)
def P_17_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_17 r_17 S_17 ps_17 U_17_4
def N_17_4 : List NodeSpec := [([12,0,29,1,2],[1,4,0],[]),([0,1,2,3,22],[4],[]),([30,0,1,2,3],[5],[0,4]),([12,5,0,1,2],[4,0,1,10],[0]),([26,0,1,2,3],[11,4],[]),([26,0,1,2],[4,1,10,11,12],[3]),([28,0,1,2],[4,1,10,13],[]),([20,0,1,2,3],[2,4,14,15,10,16,17],[0]),([4,0,1,27,2],[4,5,17,13,1,10],[4]),([23,0,8,1,2],[18,5,19],[0,3]),([4,0,1,2,22],[2,20,4],[]),([0,1,2,22],[20,21,17,5],[4,5]),([14,0,1,2,3],[2,4,18,22,23],[0,2,4]),([12,4,1,2,3],[2,0,24],[0]),([12,0,8,1,2],[4,10,17,5,0,24],[0,1,3]),([12,4,1,2],[4,24],[0,1,2]),([30,0,1,2],[4,10,5,17,25,26],[4]),([4,6,1,2,3],[4,27,16],[0,2,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_4 : checkNodesBT W_17 g_17 F_17 P_17_4 A_17 B_17_3 4 N_17_4 = true := by decide +kernel
def B_17_4 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_4
set_option maxRecDepth 500000 in
lemma B_17_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 4 xs.toFinset) B_17_4 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_3_ok C_17_4
def U_17_5 : List Nat := [0,1,2,4,16,24,28,29,30]
def P_17_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_17 r_17 S_17 ps_17 U_17_5
def N_17_5 : List NodeSpec := [([4,0,1,2,3],[1,0,2,4,16],[0,2,4]),([12,0,1,2,3],[2,0,24,28],[0,1,3,5]),([12,0,1,2],[2,4,24,28,0],[0,1,3,5]),([18,0,1,2],[2,0,29,30],[3,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_5 : checkNodesBT W_17 g_17 F_17 P_17_5 A_17 B_17_4 5 N_17_5 = true := by decide +kernel
def B_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_5
set_option maxRecDepth 500000 in
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_4_ok C_17_5
def U_17_6 : List Nat := [0,1,2,5]
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_17 r_17 S_17 ps_17 U_17_6
def N_17_6 : List NodeSpec := [([0,1,2,3],[0,1,5,2],[0,1,2,3,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6 = true := by decide +kernel
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_5_ok C_17_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_6 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 7 := lower_of_forestBT root_17_ok B_17_6_ok root_17_in
def g_18 := 0xacacacacacacacac
def r_18 : List Nat := varsOf 7
def p_18 : List Nat := [2,3,5,5,7]
def q_18 : List Nat := [0,1,4,1,6]
def F_18 : Nat := fullMask 5
set_option maxHeartbeats 0 in
lemma gp_18 : goodPairs g_18 p_18 q_18 := goodPairs_of (by decide +kernel)
def W_18 : BT Decor := buildWiresBT 2 (mkBase p_18 q_18 r_18) []
lemma W_18_ok : btAll (fun x => faithful p_18 q_18 x ∧ x.1 < 2^64) W_18 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_18 : List (List (Nat × Nat)) := [[]]
def A_18 : BT (List (Nat × Nat)) := btOfList 1 al_18
set_option maxHeartbeats 0 in
lemma A_18_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_18 = g_18) A_18 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_18_0 : Slice r_18 g_18 (subcubeFast 1 0) 1 := by
  have hc : Lower (varsOf 6) 0xc0c0c0c0c0c0c0c 1 := carry_of (swaps := [(0,2),(1,2)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_1 : Slice r_18 g_18 (subcubeFast 0 2) 1 := by
  have hc : Lower (varsOf 5) 0x5050505050505050 1 := carry_of (swaps := [(0,1),(1,2)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
def S_18 : BT (Option (Nat × Nat)) := btOfList 1 [some (subcubeFast 1 0,1),some (subcubeFast 0 2,1)]
lemma S_18_ok : btAll (fun o => ∀ p, o = some p → Slice r_18 g_18 p.1 p.2) S_18 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_18_0) (forall_cons (fun _ h => by cases h; exact sl_18_1) (fun _ h => (List.not_mem_nil h).elim)))
def ps_18 : BT (Option PoolSpec) := btOfList 1 [q 0 [],q 1 []]
def B_18_1 : BT (List (List Nat)) := BT.empty
lemma B_18_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 1 xs.toFinset) B_18_1 := .empty
def U_18_2 : List Nat := [0,1]
def P_18_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_18 r_18 S_18 ps_18 U_18_2
def N_18_2 : List NodeSpec := [([0,1,2],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_2 : checkNodesBT W_18 g_18 F_18 P_18_2 A_18 B_18_1 2 N_18_2 = true := by decide +kernel
def B_18_2 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_2
set_option maxRecDepth 500000 in
lemma B_18_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 2 xs.toFinset) B_18_2 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_1_ok C_18_2
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_ok : forestRootCheck r_18 g_18 [(VAR 0,4,5),(VAR 1,0,2),(VAR 2,1,5)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_in : bucketContainsBT B_18_2 r_18 = true := by decide +kernel
lemma low_18 : Lower r_18 g_18 3 := lower_of_forestBT root_18_ok B_18_2_ok root_18_in
def g_19 := 0xeafceafceafceafc
def r_19 : List Nat := varsOf 15
def p_19 : List Nat := [2,3,4,5,9,9,11,13,14,14]
def q_19 : List Nat := [0,1,0,1,8,1,10,12,12,10]
def F_19 : Nat := fullMask 10
set_option maxHeartbeats 0 in
lemma gp_19 : goodPairs g_19 p_19 q_19 := goodPairs_of (by decide +kernel)
def W_19 : BT Decor := buildWiresBT 4 (mkBase p_19 q_19 r_19) [(3,0,3),(3,1,3),(1,5,2),(1,1,3),(3,4,7),(3,0,7),(3,2,3),(1,1,2)]
lemma W_19_ok : btAll (fun x => faithful p_19 q_19 x ∧ x.1 < 2^64) W_19 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_19 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_19 : BT (List (Nat × Nat)) := btOfList 1 al_19
set_option maxHeartbeats 0 in
lemma A_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_19 = g_19) A_19 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_19_0 : Slice r_19 g_19 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) 0xc0fcc0fcc0fcc0fc 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_1 : Slice r_19 g_19 (subcubeFast 2 0) 3 := by
  have hc : Lower (varsOf 13) 0xaaf0aaf0aaf0aaf0 3 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_2 : Slice r_19 g_19 (subcubeFast 4 0) 3 := by
  have hc : Lower (varsOf 11) 0xaaccaaccaaccaacc 3 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_3 : Slice r_19 g_19 (subcubeFast 0 2) 2 := by
  have hc : Lower (varsOf 13) 0x500050005000500 2 := carry_of (swaps := [(0,1),(1,3)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_4 : Slice r_19 g_19 (subcubeFast 0 4) 2 := by
  have hc : Lower (varsOf 11) 0x1100110011001100 2 := carry_of (swaps := [(0,1),(1,2),(2,3)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
def S_19 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,3),some (subcubeFast 4 0,3),some (subcubeFast 0 2,2),some (subcubeFast 0 4,2)]
lemma S_19_ok : btAll (fun o => ∀ p, o = some p → Slice r_19 g_19 p.1 p.2) S_19 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_19_0) (forall_cons (fun _ h => by cases h; exact sl_19_1) (forall_cons (fun _ h => by cases h; exact sl_19_2) (forall_cons (fun _ h => by cases h; exact sl_19_3) (forall_cons (fun _ h => by cases h; exact sl_19_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_19 : BT (Option PoolSpec) := btOfList 4 [q 0 [12295,8213],q 0 [],q 1 [],q 0 [12299],q 4 [],q 2 [],q 3 [],q 0 [12293],q 0 [8197]]
def B_19_1 : BT (List (List Nat)) := BT.empty
lemma B_19_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 1 xs.toFinset) B_19_1 := .empty
def U_19_2 : List Nat := []
def P_19_2 : BT (Option BoundPool) := buildPoolsSubBT 4 W_19 r_19 S_19 ps_19 U_19_2
def N_19_2 : List NodeSpec := [([4,1,6],[],[]),([8,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_2 : checkNodesBT W_19 g_19 F_19 P_19_2 A_19 B_19_1 2 N_19_2 = true := by decide +kernel
def B_19_2 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_2
set_option maxRecDepth 500000 in
lemma B_19_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 2 xs.toFinset) B_19_2 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_1_ok C_19_2
def U_19_3 : List Nat := [0,1]
def P_19_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_19 r_19 S_19 ps_19 U_19_3
def N_19_3 : List NodeSpec := [([0,1,6,3],[0],[0]),([9,1,2,3],[1],[]),([0,1,6],[],[]),([10,4,1,2],[],[1]),([4,1,2,7],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_3 : checkNodesBT W_19 g_19 F_19 P_19_3 A_19 B_19_2 3 N_19_3 = true := by decide +kernel
def B_19_3 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_3
set_option maxRecDepth 500000 in
lemma B_19_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 3 xs.toFinset) B_19_3 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_2_ok C_19_3
def U_19_4 : List Nat := (r 1 8)
def P_19_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_19 r_19 S_19 ps_19 U_19_4
def N_19_4 : List NodeSpec := [([4,1,2,3],[1],[0,1]),([10,0,1,2,3],(r 2 4),[0,1]),([10,0,1,2],[1,4,6,5],[1]),([0,1,2,7],[6,2,1,4],[]),([0,1,2,3,7],[7,2,6],[0]),([0,1,2,11,3],[8,2,6,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_4 : checkNodesBT W_19 g_19 F_19 P_19_4 A_19 B_19_3 4 N_19_4 = true := by decide +kernel
def B_19_4 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_4
set_option maxRecDepth 500000 in
lemma B_19_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 4 xs.toFinset) B_19_4 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_3_ok C_19_4
def U_19_5 : List Nat := [1,2,5]
def P_19_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_19 r_19 S_19 ps_19 U_19_5
def N_19_5 : List NodeSpec := [([0,1,2,3],[1,2,5],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_5 : checkNodesBT W_19 g_19 F_19 P_19_5 A_19 B_19_4 5 N_19_5 = true := by decide +kernel
def B_19_5 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_5
set_option maxRecDepth 500000 in
lemma B_19_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 5 xs.toFinset) B_19_5 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_4_ok C_19_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck r_19 g_19 [(VAR 0,8,9),(VAR 1,0,2),(VAR 2,0,4),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT B_19_5 r_19 = true := by decide +kernel
lemma low_19 : Lower r_19 g_19 6 := lower_of_forestBT root_19_ok B_19_5_ok root_19_in
def g_20 := 0x88e088e088e088e0
def r_20 : List Nat := varsOf 15
def p_20 : List Nat := [5,5,6,6,7,11,11,11,15,15]
def q_20 : List Nat := [4,1,4,2,3,10,9,3,14,13]
def F_20 : Nat := fullMask 10
set_option maxHeartbeats 0 in
lemma gp_20 : goodPairs g_20 p_20 q_20 := goodPairs_of (by decide +kernel)
def W_20 : BT Decor := buildWiresBT 4 (mkBase p_20 q_20 r_20) [(2,2,3),(2,1,3),(3,5,0),(0,0,3),(1,4,7),(2,0,3),(0,1,3),(3,10,2),(0,0,1)]
lemma W_20_ok : btAll (fun x => faithful p_20 q_20 x ∧ x.1 < 2^64) W_20 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_20 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_20 : BT (List (Nat × Nat)) := btOfList 1 al_20
set_option maxHeartbeats 0 in
lemma A_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_20 = g_20) A_20 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_20_0 : Slice r_20 g_20 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) 0x88ee88ee88ee88ee 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_1 : Slice r_20 g_20 (subcubeFast 0 1) 3 := by
  have hc : Lower (varsOf 14) 0xccf0ccf0ccf0ccf0 3 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_2 : Slice r_20 g_20 (subcubeFast 0 2) 3 := by
  have hc : Lower (varsOf 13) 0xaaf0aaf0aaf0aaf0 3 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_3 : Slice r_20 g_20 (subcubeFast 1 0) 2 := by
  have hc : Lower (varsOf 14) 0xc000c000c000c0 2 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_4 : Slice r_20 g_20 (subcubeFast 2 0) 2 := by
  have hc : Lower (varsOf 13) 0xa000a000a000a0 2 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
def S_20 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 4,4),some (subcubeFast 0 1,3),some (subcubeFast 0 2,3),some (subcubeFast 1 0,2),some (subcubeFast 2 0,2)]
lemma S_20_ok : btAll (fun o => ∀ p, o = some p → Slice r_20 g_20 p.1 p.2) S_20 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (forall_cons (fun _ h => by cases h; exact sl_20_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_20 : BT (Option PoolSpec) := btOfList 4 [q 0 [12294,23],q 0 [],q 2 [],q 3 [],q 1 [],q 0 [12290],q 4 [],q 0 [12288],q 0 [4096]]
def B_20_1 : BT (List (List Nat)) := BT.empty
lemma B_20_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 1 xs.toFinset) B_20_1 := .empty
def U_20_2 : List Nat := []
def P_20_2 : BT (Option BoundPool) := buildPoolsSubBT 4 W_20 r_20 S_20 ps_20 U_20_2
def N_20_2 : List NodeSpec := [([4,6,1],[],[]),([0,8,1],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_2 : checkNodesBT W_20 g_20 F_20 P_20_2 A_20 B_20_1 2 N_20_2 = true := by decide +kernel
def B_20_2 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_2
set_option maxRecDepth 500000 in
lemma B_20_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 2 xs.toFinset) B_20_2 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_1_ok C_20_2
def U_20_3 : List Nat := [0,1]
def P_20_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_20 r_20 S_20 ps_20 U_20_3
def N_20_3 : List NodeSpec := [([6,1,2,3],[0],[0]),([11,0,1,3],[1],[]),([9,4,0,1],[],[1]),([6,1,2],[],[]),([4,7,0,1],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_3 : checkNodesBT W_20 g_20 F_20 P_20_3 A_20 B_20_2 3 N_20_3 = true := by decide +kernel
def B_20_3 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_3
set_option maxRecDepth 500000 in
lemma B_20_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 3 xs.toFinset) B_20_3 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_2_ok C_20_3
def U_20_4 : List Nat := (r 1 8)
def P_20_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_20 r_20 S_20 ps_20 U_20_4
def N_20_4 : List NodeSpec := [([4,0,1,3],[1],[0,1]),([9,0,1,2,3],(r 2 4),[0,1]),([9,0,1,2],[3,6,1,4],[1]),([7,0,1,2],[3,6,1,4],[]),([7,0,1,2,3],[4,3,7],[0,1]),([12,0,1,2,3],[3,4,6,8],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_4 : checkNodesBT W_20 g_20 F_20 P_20_4 A_20 B_20_3 4 N_20_4 = true := by decide +kernel
def B_20_4 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_4
set_option maxRecDepth 500000 in
lemma B_20_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 4 xs.toFinset) B_20_4 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_3_ok C_20_4
def U_20_5 : List Nat := [1,2,4]
def P_20_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_20 r_20 S_20 ps_20 U_20_5
def N_20_5 : List NodeSpec := [([0,1,2,3],[4,2,1],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_5 : checkNodesBT W_20 g_20 F_20 P_20_5 A_20 B_20_4 5 N_20_5 = true := by decide +kernel
def B_20_5 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_5
set_option maxRecDepth 500000 in
lemma B_20_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 5 xs.toFinset) B_20_5 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_4_ok C_20_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck r_20 g_20 [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT B_20_5 r_20 = true := by decide +kernel
lemma low_20 : Lower r_20 g_20 6 := lower_of_forestBT root_20_ok B_20_5_ok root_20_in
def g_21 := 0xfee0fee0fee0fee0
def r_21 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_21 : Lower r_21 g_21 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_22 := 0xff8eff8eff8eff8e
def r_22 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_22 : Lower r_22 g_22 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_13) (G := g_13) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_13
def g_23 := 0xff8eac08ff8eac08
def r_23 : List Nat := varsOf 31
def p_23 : List Nat := [3,3,10,10,11,13,13,13,15,15,17,17,18,18,23,23,23,24,24,25,28,28,29,30,30]
def q_23 : List Nat := [2,1,8,2,9,12,9,5,14,7,16,1,16,2,22,21,7,16,8,9,20,12,21,22,14]
def F_23 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_23 : goodPairs g_23 p_23 q_23 := goodPairs_of (by decide +kernel)
def W_23 : BT Decor := buildWiresBT 4 (mkBase p_23 q_23 r_23) [(2,2,4),(3,5,1),(2,0,2),(1,7,3),(0,0,2),(1,2,4),(2,0,4)]
lemma W_23_ok : btAll (fun x => faithful p_23 q_23 x ∧ x.1 < 2^64) W_23 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_23 : List (List (Nat × Nat)) := [[]]
def A_23 : BT (List (Nat × Nat)) := btOfList 1 al_23
set_option maxHeartbeats 0 in
lemma A_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_23 = g_23) A_23 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_23_0 : Slice r_23 g_23 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 29) 0xffafaf0affafaf0a 7 := carry_of (swaps := [(1,4),(2,3),(3,4)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_1 : Slice r_23 g_23 (subcubeFast 8 0) 7 := by
  have hc : Lower (varsOf 23) 0x8e8e08088e8e0808 7 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_2 : Slice r_23 g_23 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xffcffc0cffcffc0c 6 := carry_of (swaps := [(0,4),(2,3),(3,4)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_3 : Slice r_23 g_23 (subcubeFast 16 0) 6 := by
  have hc : Lower (varsOf 15) 0xac08ac08ac08ac08 6 := carry_of (swaps := [(1,2),(2,3)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_4 : Slice r_23 g_23 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffeecc88ffeecc88 5 := carry_of (swaps := [(1,2),(2,4),(3,4)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_5 : Slice r_23 g_23 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_22
set_option maxHeartbeats 0 in
lemma sl_23_6 : Slice r_23 g_23 (subcubeFast 0 6) 4 := by
  have hc : Lower (varsOf 25) 0xffaaaa00ffaaaa00 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 6) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_7 : Slice r_23 g_23 (subcubeFast 5 0) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_8 : Slice r_23 g_23 (subcubeFast 12 0) 4 := by
  have hc : Lower (varsOf 19) 0xeeee8888eeee8888 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_9 : Slice r_23 g_23 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) 0xff0f0f00ff0f0f00 4 := carry_of (swaps := [(0,3),(1,4)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_10 : Slice r_23 g_23 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_13
set_option maxHeartbeats 0 in
lemma sl_23_11 : Slice r_23 g_23 (subcubeFast 16 8) 3 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_18
def S_23 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 2,7),some (subcubeFast 8 0,7),some (subcubeFast 0 1,6),some (subcubeFast 16 0,6),some (subcubeFast 4 0,5),some (subcubeFast 0 16,5),some (subcubeFast 0 6,4),some (subcubeFast 5 0,4),some (subcubeFast 12 0,4),some (subcubeFast 1 2,4),some (subcubeFast 8 16,4),some (subcubeFast 16 8,3)]
lemma S_23_ok : btAll (fun o => ∀ p, o = some p → Slice r_23 g_23 p.1 p.2) S_23 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (forall_cons (fun _ h => by cases h; exact sl_23_4) (forall_cons (fun _ h => by cases h; exact sl_23_5) (forall_cons (fun _ h => by cases h; exact sl_23_6) (forall_cons (fun _ h => by cases h; exact sl_23_7) (forall_cons (fun _ h => by cases h; exact sl_23_8) (forall_cons (fun _ h => by cases h; exact sl_23_9) (forall_cons (fun _ h => by cases h; exact sl_23_10) (forall_cons (fun _ h => by cases h; exact sl_23_11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
def ps_23 : BT (Option PoolSpec) := btOfList 5 [q 7 [],q 0 [16394],q 8 [],q 5 [],q 9 [],q 6 [],q 11 [],q 3 [],q 2 [],q 10 [],q 2 [16393],q 0 [16393],q 4 [],q 1 [8194],q 1 [8192],q 3 [8192],q 0 [],q 1 []]
def B_23_5 : BT (List (List Nat)) := BT.empty
lemma B_23_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 5 xs.toFinset) B_23_5 := .empty
def U_23_6 : List Nat := (r 0 9)
def P_23_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_6
def N_23_6 : List NodeSpec := [([0,6,2,3,4],(r 0 4),[]),([0,1,2,8,4],[4,5,0,6],[]),([9,0,1,3,4,10],[5,2,3,7,4,8],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_6 : checkNodesBT W_23 g_23 F_23 P_23_6 A_23 B_23_5 6 N_23_6 = true := by decide +kernel
def B_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_6
set_option maxRecDepth 500000 in
lemma B_23_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 6 xs.toFinset) B_23_6 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_5_ok C_23_6
def U_23_7 : List Nat := (r 0 6++r 7 9)
def P_23_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_7
def N_23_7 : List NodeSpec := [u5 [5] [0,1,2,7,3],([5,0,1,3,4],[4,9,1],[]),u5 [10] [5,10,9,0,7],([0,1,3,4,10],[11,9,4],[]),e5 [11] [7,5,4,12,9],([7,0,1,3,4],[4,3,13],[]),u5 [7] [5,13,3,7,4,8,0],([9,0,1,3,4],[3,4,14],[]),u5 [9] [4,8,14,3,12,15]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_7 : checkNodesBT W_23 g_23 F_23 P_23_7 A_23 B_23_6 7 N_23_7 = true := by decide +kernel
def B_23_7 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_7
set_option maxRecDepth 500000 in
lemma B_23_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 7 xs.toFinset) B_23_7 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_6_ok C_23_7
def U_23_8 : List Nat := [7,8,16,17]
def P_23_8 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_8
def N_23_8 : List NodeSpec := [u5 [] [16,8,17,7]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_8 : checkNodesBT W_23 g_23 F_23 P_23_8 A_23 B_23_7 8 N_23_8 = true := by decide +kernel
def B_23_8 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_8
set_option maxRecDepth 500000 in
lemma B_23_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 8 xs.toFinset) B_23_8 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_7_ok C_23_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck r_23 g_23 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,3,7),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT B_23_8 r_23 = true := by decide +kernel
lemma low_23 : Lower r_23 g_23 9 := lower_of_forestBT root_23_ok B_23_8_ok root_23_in
def g_24 := 0xffe8c000ffe8c000
def r_24 : List Nat := varsOf 31
def p_24 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,29]
def q_24 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,13]
def F_24 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_24 : goodPairs g_24 p_24 q_24 := goodPairs_of (by decide +kernel)
def W_24 : BT Decor := buildWiresBT 5 (mkBase p_24 q_24 r_24) [(2,2,3),(3,5,1),(0,1,2),(0,1,4),(2,1,3),(0,2,4),(3,10,1),(3,7,4),(0,7,4),(1,7,3),(0,0,4),(2,0,3)]
lemma W_24_ok : btAll (fun x => faithful p_24 q_24 x ∧ x.1 < 2^64) W_24 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_24 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_24 : BT (List (Nat × Nat)) := btOfList 1 al_24
set_option maxHeartbeats 0 in
lemma A_24_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_24 = g_24) A_24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_24_0 : Slice r_24 g_24 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_1 : Slice r_24 g_24 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_2 : Slice r_24 g_24 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_24_3 : Slice r_24 g_24 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_4 : Slice r_24 g_24 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) 0xf8f8c0c0f8f8c0c0 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_9
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_24 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,6),some (subcubeFast 0 2,5),some (subcubeFast 8 16,4),some (subcubeFast 1 4,4),some (identDom 2 3,5)]
lemma S_24_ok : btAll (fun o => ∀ p, o = some p → Slice r_24 g_24 p.1 p.2) S_24 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_24_0) (forall_cons (fun _ h => by cases h; exact sl_24_1) (forall_cons (fun _ h => by cases h; exact sl_24_2) (forall_cons (fun _ h => by cases h; exact sl_24_3) (forall_cons (fun _ h => by cases h; exact sl_24_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_24 : BT (Option PoolSpec) := btOfList 3 [q 2 [],q 3 [],q 0 [],q 4 [],q 1 [],q 0 [8196]]
def B_24_4 : BT (List (List Nat)) := BT.empty
lemma B_24_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 4 xs.toFinset) B_24_4 := .empty
def U_24_5 : List Nat := (r 0 4)
def P_24_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_24 r_24 S_24 ps_24 U_24_5
def N_24_5 : List NodeSpec := [([0,7,8,2,3,4],[0,1],[]),([9,0,7,2,3,4],[0,1],[]),e5 [12] [1,2],e5 [14] [2,1],e5 [13] [2,1,3,0],e5 [6] [],e5 [11] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_5 : checkNodesBT W_24 g_24 F_24 P_24_5 A_24 B_24_4 5 N_24_5 = true := by decide +kernel
def B_24_5 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_5
set_option maxRecDepth 500000 in
lemma B_24_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 5 xs.toFinset) B_24_5 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_4_ok C_24_5
def U_24_6 : List Nat := (r 0 6)
def P_24_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_24 r_24 S_24 ps_24 U_24_6
def N_24_6 : List NodeSpec := [([16,1,2,3,4],[0,1],[]),([15,1,2,3,4],[1,0],[]),a5 [9] [1,2,0,3,4] [0,1],a5 [8] [1,2,0,4] [0,1],a5 [7] [1,5,4,0,3] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_6 : checkNodesBT W_24 g_24 F_24 P_24_6 A_24 B_24_5 6 N_24_6 = true := by decide +kernel
def B_24_6 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_6
set_option maxRecDepth 500000 in
lemma B_24_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 6 xs.toFinset) B_24_6 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_5_ok C_24_6
def U_24_7 : List Nat := [0,1,2,4]
def P_24_7 : BT (Option BoundPool) := buildPoolsSubBT 3 W_24 r_24 S_24 ps_24 U_24_7
def N_24_7 : List NodeSpec := [a5 [] [2,4,1,0] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_7 : checkNodesBT W_24 g_24 F_24 P_24_7 A_24 B_24_6 7 N_24_7 = true := by decide +kernel
def B_24_7 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_7
set_option maxRecDepth 500000 in
lemma B_24_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 7 xs.toFinset) B_24_7 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_6_ok C_24_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_24_ok : forestRootCheck r_24 g_24 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_24_in : bucketContainsBT B_24_7 r_24 = true := by decide +kernel
lemma low_24 : Lower r_24 g_24 8 := lower_of_forestBT root_24_ok B_24_7_ok root_24_in
def g_25 := 0xffc8e000ffc8e000
def r_25 : List Nat := varsOf 31
def p_25 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,22,22,22,23,23,24,24,25,25,26,26,27,28,28,29]
def q_25 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,20,18,6,21,7,16,8,17,9,18,10,11,20,12,21]
def F_25 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_25 : goodPairs g_25 p_25 q_25 := goodPairs_of (by decide +kernel)
def W_25 : BT Decor := buildWiresBT 7 (mkBase p_25 q_25 r_25) [(0,1,3),(0,5,4),(3,6,1),(0,3,4),(1,3,4),(3,8,9),(0,0,9),(1,0,8),(2,10,0),(3,2,9),(0,1,9),(2,0,8),(0,2,4),(1,0,17),(0,2,3),(1,19,4),(1,1,8),(1,2,8),(2,10,2),(0,10,1),(0,10,0),(3,0,9),(0,2,9),(2,3,4),(0,1,4),(1,29,3),(0,17,3),(3,31,1),(3,8,4),(1,0,5),(2,2,4),(0,1,2),(3,36,4),(1,0,36),(3,1,9),(2,1,3),(3,40,4),(2,2,41),(1,0,3),(0,43,4),(2,2,44),(2,2,8),(0,36,4),(3,47,3),(3,36,3),(3,0,4),(3,50,3),(1,50,3),(0,36,3),(2,43,4),(3,17,3),(3,19,1),(0,35,3),(3,19,4),(3,33,1),(3,35,3),(3,17,1),(1,0,4),(0,62,3),(3,0,3)]
lemma W_25_ok : btAll (fun x => faithful p_25 q_25 x ∧ x.1 < 2^64) W_25 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_25 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_25 : BT (List (Nat × Nat)) := btOfList 1 al_25
set_option maxHeartbeats 0 in
lemma A_25_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_25 = g_25) A_25 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_25_0 : Slice r_25 g_25 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_1 : Slice r_25 g_25 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_2 : Slice r_25 g_25 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_3 : Slice r_25 g_25 (identDom 1 4) 6 := by
  have hc : Lower (varsOf 15) 0xecc8ecc8ecc8ecc8 6 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_4 : Slice r_25 g_25 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) 0xf8f8e0e0f8f8e0e0 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_5 : Slice r_25 g_25 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xeaeaa0a0eaeaa0a0 5 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_9
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_6 : Slice r_25 g_25 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
def S_25 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 2,5),some (subcubeFast 1 4,4),some (subcubeFast 1 2,4),some (identDom 1 4,6),some (identDom 2 3,6),some (identDom 0 3,5),some (subcubeFast 0 1,4)]
lemma S_25_ok : btAll (fun o => ∀ p, o = some p → Slice r_25 g_25 p.1 p.2) S_25 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_25_0) (forall_cons (fun _ h => by cases h; exact sl_25_1) (forall_cons (fun _ h => by cases h; exact sl_25_2) (forall_cons (fun _ h => by cases h; exact sl_25_3) (forall_cons (fun _ h => by cases h; exact sl_25_4) (forall_cons (fun _ h => by cases h; exact sl_25_5) (forall_cons (fun _ h => by cases h; exact sl_25_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_25 : BT (Option PoolSpec) := btOfList 4 [q 5 [],q 1 [],q 0 [],q 4 [],q 3 [16398],q 6 [],q 2 [],q 3 [],q 4 [16394,12431],q 3 [16396],q 4 [16396],q 4 [16394]]
def B_25_2 : BT (List (List Nat)) := BT.empty
lemma B_25_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 2 xs.toFinset) B_25_2 := .empty
def U_25_3 : List Nat := []
def P_25_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_25 r_25 S_25 ps_25 U_25_3
def N_25_3 : List NodeSpec := [([0,21,22,9],[],[]),([0,15,27,8],[],[]),([11,15,2,8],[],[]),([10,0,1,2],[],[]),([10,26,1,2],[],[]),([25,10,1,2],[],[]),([24,10,0,2],[],[]),([10,0,1,22],[],[]),([23,10,0,1],[],[]),([7,10,0,2],[],[]),([1,18,3,20],[],[]),([16,10,1,2],[],[]),([10,0,15,2],[],[]),([10,14,0,1],[],[]),([13,10,1,2],[],[]),([10,1,2,12],[],[]),([10,11,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_3 : checkNodesBT W_25 g_25 F_25 P_25_3 A_25 B_25_2 3 N_25_3 = true := by decide +kernel
def B_25_3 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_3
set_option maxRecDepth 500000 in
lemma B_25_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 3 xs.toFinset) B_25_3 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_2_ok C_25_3
def U_25_4 : List Nat := []
def P_25_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_25 r_25 S_25 ps_25 U_25_4
def N_25_4 : List NodeSpec := [([10,0,1,2],[],[0,1]),([16,7,2,3,4],[],[]),([7,46,0,3,4],[],[]),([1,2,8,12,9],[],[0]),([0,15,2,8,9],[],[0]),([35,1,38,3,4],[],[]),([7,0,3,22,4],[],[]),([7,0,2,8,9],[],[0]),([14,26,1,3,4],[],[]),([10,0,1,2,8],[],[0,1]),([45,0,1,3,4],[],[]),([11,1,2,8,9],[],[0,1]),([0,1,8,22,9],[],[0]),([0,1,2,8,9],[],[0]),([26,1,2,8,9],[],[0]),([10,0,1,2,3],[],[]),([48,0,1,2,4],[],[]),([7,2,3,12,4],[],[]),([16,1,2,8,9],[],[0]),([14,0,1,8,9],[],[0]),([28,0,15,2,3],[],[]),([14,0,15,3,4],[],[]),([0,15,27,3,4],[],[0]),([26,15,2,3,4],[],[]),([0,5,2,30,4],[],[1]),([32,0,2,3,4],[],[]),([28,33,0,1,2],[],[0]),([29,34,2,3,4],[],[1]),([10,0,1,2,9],[],[0,1]),([35,1,18,3,4],[],[]),([28,10,0,1,2],[],[]),([0,3,21,22,4],[],[0]),([0,1,2,8,30],[],[]),([11,15,2,3,4],[],[0]),([35,37,0,1,3],[],[]),([29,38,2,3,4],[],[]),([7,0,2,3,4],[],[]),([1,3,12,22,4],[],[]),([14,39,0,3,4],[],[]),([42,0,1,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_4 : checkNodesBT W_25 g_25 F_25 P_25_4 A_25 B_25_3 4 N_25_4 = true := by decide +kernel
def B_25_4 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_4
set_option maxRecDepth 500000 in
lemma B_25_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 4 xs.toFinset) B_25_4 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_3_ok C_25_4
def U_25_5 : List Nat := (r 0 10)
def P_25_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_25 r_25 S_25 ps_25 U_25_5
def N_25_5 : List NodeSpec := [a5 [6] [0,1] [0,1],([0,1,8,3,22,4],[1],[0,1]),([1,2,8,3,12,4],[1],[0,1]),([35,0,1,17,3,4],[1],[0]),([36,1,38,2,3,4],[1],[]),([26,1,2,3,4,9],[1],[0,1]),a5 [49] [1] [1],a5 [8] [0,1,2] [0,1],a5 [63] [0,2] [1],([28,0,1,2,8,4],[2],[0]),([7,0,2,8,3,4],[2],[0]),([0,29,1,2,8,3],[2],[0]),([28,0,29,1,2,3],[2],[]),([35,0,36,1,3,4],[2],[0]),([0,15,2,3,4,9],[2],[0]),([14,0,1,3,4,9],[3,1],[0]),([28,0,1,2,3,9],[4],[0]),e5 [59] [5,1],e5 [52] [5,3,1],([16,1,2,8,3,4],[0,6,1],[0,1]),([1,38,2,3,4],[1,6],[0,1]),([11,1,2,3,4,9],[5,6,1],[0,1]),([1,34,2,3,4],[6],[0,1]),([5,1,34,2,3,4],[6],[1]),a5 [53] [0,1,7] [1],u5 [9] [1,5,7,2,3],u5 [30] [1,5,7,3],([0,36,29,2,3,4],[1,7],[0]),([0,5,29,2,3,4],[7],[0]),a5 [60] [0,1,2,8] [1],([0,1,2,8,3,9],[9],[0]),([0,1,2,8,9],[],[0,1]),([26,1,2,3,4],[],[]),e5 [61] [],e5 [7] [],([7,0,2,3,4],[],[]),([1,2,3,12,4],[],[]),u5 [28] [],e5 [58] [],([28,33,0,1,2],[],[0,1]),e5 [57] [],e5 [56] [],e5 [55] [],e5 [54] [],([28,33,0,1,2,3],[],[0]),e5 [51] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_5 : checkNodesBT W_25 g_25 F_25 P_25_5 A_25 B_25_4 5 N_25_5 = true := by decide +kernel
def B_25_5 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_5
set_option maxRecDepth 500000 in
lemma B_25_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 5 xs.toFinset) B_25_5 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_4_ok C_25_5
def U_25_6 : List Nat := (r 1 7++[9,10,11])
def P_25_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_25 r_25 S_25 ps_25 U_25_6
def N_25_6 : List NodeSpec := [a5 [64] [1,6,5] [1],a5 [43] [6,1,5] [0,1],a5 [36] [1,2,3,7] [0,1],a5 [9] [1,5,7,2,3] [0,1],a5 [28] [1,5,7,2,4] [0,1],a5 [29] [1,6,7] [0,1],a5 [5] [1,6,7] [0,1],a5 [8] [1,5,2,9,10] [0,1],u5 [35] [1,7,2,3,11]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_6 : checkNodesBT W_25 g_25 F_25 P_25_6 A_25 B_25_5 6 N_25_6 = true := by decide +kernel
def B_25_6 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_6
set_option maxRecDepth 500000 in
lemma B_25_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 6 xs.toFinset) B_25_6 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_5_ok C_25_6
def U_25_7 : List Nat := [1,3,6,7]
def P_25_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_25 r_25 S_25 ps_25 U_25_7
def N_25_7 : List NodeSpec := [a5 [] [6,1,7,3] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_7 : checkNodesBT W_25 g_25 F_25 P_25_7 A_25 B_25_6 7 N_25_7 = true := by decide +kernel
def B_25_7 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_7
set_option maxRecDepth 500000 in
lemma B_25_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 7 xs.toFinset) B_25_7 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_6_ok C_25_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_25_ok : forestRootCheck r_25 g_25 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_25_in : bucketContainsBT B_25_7 r_25 = true := by decide +kernel
lemma low_25 : Lower r_25 g_25 8 := lower_of_forestBT root_25_ok B_25_7_ok root_25_in
def g_26 := 0xffecf880ffecf880
def r_26 : List Nat := varsOf 31
def p_26 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,18,18,19,19,21,21,21,22,22,24,24,25,25,26,28]
def q_26 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,2,17,3,20,17,5,20,6,16,8,17,9,10,20]
def F_26 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_26 : goodPairs g_26 p_26 q_26 := goodPairs_of (by decide +kernel)
def W_26 : BT Decor := buildWiresBT 7 (mkBase p_26 q_26 r_26) [(0,1,4),(0,2,3),(1,5,6),(1,2,3),(1,1,4),(0,8,9),(3,6,8),(3,5,9),(0,0,9),(1,13,6),(2,1,4),(3,1,4),(2,11,5),(1,5,3),(0,2,18),(1,2,18),(3,19,20),(2,0,6),(0,0,8),(1,13,3),(3,2,24),(1,23,4),(0,1,26),(1,23,5),(3,6,9),(2,2,3),(3,2,3),(1,6,4),(0,1,32),(1,1,32),(3,4,20),(2,0,19),(1,16,6),(0,0,20),(2,1,32),(3,1,32),(3,13,8),(1,31,16),(3,13,3),(3,23,1),(1,23,1),(3,16,8),(1,31,5),(0,3,4),(1,3,4),(3,48,49),(0,1,2),(1,51,3),(1,52,4),(2,2,4),(2,1,3),(1,54,55),(3,51,49),(1,51,4),(1,55,4),(3,2,18),(2,52,4),(2,1,49),(1,2,48),(2,0,48),(1,16,3),(3,1,3),(3,66,0),(0,1,49),(2,1,48),(1,5,2),(0,1,3),(1,1,3),(2,2,1),(1,73,3),(0,2,4),(1,75,3),(1,1,2),(1,54,3),(3,6,1),(0,0,77),(2,3,4),(3,3,4),(3,6,4),(2,1,2),(3,2,4)]
lemma W_26_ok : btAll (fun x => faithful p_26 q_26 x ∧ x.1 < 2^64) W_26 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_26 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_26 : BT (List (Nat × Nat)) := btOfList 1 al_26
set_option maxHeartbeats 0 in
lemma A_26_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_26 = g_26) A_26 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_26_0 : Slice r_26 g_26 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_1 : Slice r_26 g_26 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xffa0f000ffa0f000 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_2 : Slice r_26 g_26 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffffaa0fffffaa0 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_3 : Slice r_26 g_26 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffcc8800ffcc8800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_4 : Slice r_26 g_26 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xecec8080ecec8080 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_5 : Slice r_26 g_26 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_4
set_option maxHeartbeats 0 in
lemma sl_26_6 : Slice r_26 g_26 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_7 : Slice r_26 g_26 (subcubeFast 8 4) 4 := by
  have hc : Lower (varsOf 19) 0xeeee8888eeee8888 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_8 : Slice r_26 g_26 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_9 : Slice r_26 g_26 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_10 : Slice r_26 g_26 (subcubeFast 8 1) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_11 : Slice r_26 g_26 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_12 : Slice r_26 g_26 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) 0xececc8c8ececc8c8 6 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_13 : Slice r_26 g_26 (identDom 2 4) 6 := by
  have hc : Lower (varsOf 15) 0xf8e0f8e0f8e0f8e0 6 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_14 : Slice r_26 g_26 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xeeeea8a8eeeea8a8 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_15 : Slice r_26 g_26 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) 0xffcccc88ffcccc88 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_3
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_16 : Slice r_26 g_26 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_26 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 1,7),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 4 1,4),some (subcubeFast 8 4,4),some (subcubeFast 16 2,4),some (subcubeFast 16 1,4),some (subcubeFast 8 1,4),some (subcubeFast 2 1,4),some (identDom 1 3,6),some (identDom 2 4,6),some (identDom 0 3,5),some (identDom 1 2,5),some (subcubeFast 1 0,4)]
lemma S_26_ok : btAll (fun o => ∀ p, o = some p → Slice r_26 g_26 p.1 p.2) S_26 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_26_0) (forall_cons (fun _ h => by cases h; exact sl_26_1) (forall_cons (fun _ h => by cases h; exact sl_26_2) (forall_cons (fun _ h => by cases h; exact sl_26_3) (forall_cons (fun _ h => by cases h; exact sl_26_4) (forall_cons (fun _ h => by cases h; exact sl_26_5) (forall_cons (fun _ h => by cases h; exact sl_26_6) (forall_cons (fun _ h => by cases h; exact sl_26_7) (forall_cons (fun _ h => by cases h; exact sl_26_8) (forall_cons (fun _ h => by cases h; exact sl_26_9) (forall_cons (fun _ h => by cases h; exact sl_26_10) (forall_cons (fun _ h => by cases h; exact sl_26_11) (forall_cons (fun _ h => by cases h; exact sl_26_12) (forall_cons (fun _ h => by cases h; exact sl_26_13) (forall_cons (fun _ h => by cases h; exact sl_26_14) (forall_cons (fun _ h => by cases h; exact sl_26_15) (forall_cons (fun _ h => by cases h; exact sl_26_16) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))
def ps_26 : BT (Option PoolSpec) := btOfList 5 [q 8 [],q 6 [],q 7 [],q 2 [],q 9 [],q 16 [],q 0 [],q 1 [],q 14 [],q 3 [],q 11 [],q 4 [],q 5 [],q 12 [],q 15 [],q 10 [],q 0 [12297],q 0 [8197],q 0 [16397],q 13 [],q 0 [12293]]
def B_26_1 : BT (List (List Nat)) := BT.empty
lemma B_26_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 1 xs.toFinset) B_26_1 := .empty
def U_26_2 : List Nat := []
def P_26_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_26 r_26 S_26 ps_26 U_26_2
def N_26_2 : List NodeSpec := [([0,7,10],[],[]),([11,12,0],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_2 : checkNodesBT W_26 g_26 F_26 P_26_2 A_26 B_26_1 2 N_26_2 = true := by decide +kernel
def B_26_2 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_2
set_option maxRecDepth 500000 in
lemma B_26_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 2 xs.toFinset) B_26_2 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_1_ok C_26_2
def U_26_3 : List Nat := []
def P_26_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_26 r_26 S_26 ps_26 U_26_3
def N_26_3 : List NodeSpec := [([1,14,8,4],[],[]),([15,11,16,0],[],[0]),([0,7,8,9],[],[0]),([11,0,5,9],[],[0]),([17,0,1,4],[],[]),([0,5,6,10],[],[0]),([21,0,1,4],[],[]),([11,13,1,4],[],[]),([22,12,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_3 : checkNodesBT W_26 g_26 F_26 P_26_3 A_26 B_26_2 3 N_26_3 = true := by decide +kernel
def B_26_3 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_3
set_option maxRecDepth 500000 in
lemma B_26_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 3 xs.toFinset) B_26_3 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_2_ok C_26_3
def U_26_4 : List Nat := [0,1,2]
def P_26_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_26 r_26 S_26 ps_26 U_26_4
def N_26_4 : List NodeSpec := [([15,0,2,37,3],[0],[]),([11,0,1,4,9],[1],[0]),([11,0,5,1,4],[2,1],[0,1]),([15,11,0,1,4],[],[0]),([15,16,23,2,3],[],[1]),([23,5,2,3,9],[],[1]),([23,1,2,18,4],[],[]),([22,5,2,3,9],[],[0]),([0,5,6,8,9],[],[0,1]),([41,1,2,3,4],[],[]),([39,40,0,2,3],[],[1]),([22,1,2,18,4],[],[]),([38,1,2,18,4],[],[]),([0,1,2,18,32],[],[]),([31,12,0,2,3],[],[1]),([36,1,2,18,4],[],[]),([35,0,1,2,18],[],[]),([0,33,2,3,34],[],[1]),([15,22,16,2,3],[],[0]),([0,1,7,8,4],[],[0]),([15,16,0,6,8],[],[0,1]),([15,30,31,16,0],[],[0,1]),([29,0,5,2,3],[],[1]),([0,5,2,3,10],[],[0]),([1,28,2,3,4],[],[1]),([23,27,2,3,4],[],[]),([25,13,1,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_4 : checkNodesBT W_26 g_26 F_26 P_26_4 A_26 B_26_3 4 N_26_4 = true := by decide +kernel
def B_26_4 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_4
set_option maxRecDepth 500000 in
lemma B_26_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 4 xs.toFinset) B_26_4 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_3_ok C_26_4
def U_26_5 : List Nat := (r 0 12)
def P_26_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_26 r_26 S_26 ps_26 U_26_5
def N_26_5 : List NodeSpec := [([0,1,2,3,32,34],[1,2],[0,1]),([0,5,1,6,8,4],[1,2],[0,1]),([0,33,1,2,3,32],[1,2],[0,1]),([54,23,1,3,4],[2],[]),([11,0,1,4],[2,1],[0,1]),([0,5,1,2,3,32],[1,2,3],[0,1]),([15,0,1,2,3,32],[3],[]),([15,35,0,1,2,3],[3],[]),([35,0,5,1,2,3],[3,2],[0]),([15,16,0,2,3,8],[4],[0,1]),([50,0,1,2],[4,0,2],[]),([50,0,1,2,49],[4,0,2],[]),([0,5,2,3,8,9],[4,3],[0,1]),([22,5,1,2,3,4],[1,5,2],[0]),([43,13,1,2,3,4],[3,4,5],[]),([44,23,1,2,3,4],[5],[]),([23,1,2,3,4,9],[5],[0,1]),([23,1,45,2,3,4],[5],[]),([23,1,2,3,4,26],[5],[0,1]),([22,1,2,3,4,9],[5,1],[0]),([23,5,1,2,3,4],[5,2,1],[0]),a5 [10] [5,6] [0,1],([15,16,0,6,2,3],[0,7,4],[0,1]),([0,1,2,3,9,32],[1,7,2],[1]),a5 [47] [7] [1],u5 [29] [5,6,9],a5 [7] [6,5,7,9] [0,1],e5 [53] [8,6,7,9],([31,0,1,2,18,4],[9],[]),([31,13,1,2,3,4],[3,10],[1]),([0,1,2,3,58,49],[7,9,11],[]),([0,1,2,3,59,49],[7,11],[]),([60,0,1,2,18,4],[],[1]),e5 [61] [],([15,0,1,6,8,4],[],[0]),([15,22,1,2,3,4],[],[0]),([31,0,5,2,3,9],[],[0,1]),e5 [57] [],([39,0,1,2,3,32],[],[0]),([22,16,1,2,3,4],[],[0]),e5 [42] [],e5 [56] [],([15,23,1,2,3,4],[],[0]),([15,31,16,0,2,3],[],[0]),e5 [46] [],([15,30,31,0,1,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_5 : checkNodesBT W_26 g_26 F_26 P_26_5 A_26 B_26_4 5 N_26_5 = true := by decide +kernel
def B_26_5 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_5
set_option maxRecDepth 500000 in
lemma B_26_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 5 xs.toFinset) B_26_5 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_4_ok C_26_5
def U_26_6 : List Nat := (r 0 8++r 9 6)
def P_26_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_26 r_26 S_26 ps_26 U_26_6
def N_26_6 : List NodeSpec := [e5 [74] [1,0],([0,1,3,63,4],[0,2],[]),([64,1,2,3,4],[0,2],[]),([81,82,0,1,2],[0,2],[0]),e5 [76] [1,0,2],([67,1,2,3,4],[2,0],[]),([80,1,2,3,4],[2,0],[]),([54,0,1,3,8,4],[2,1,0],[0]),([0,1,2,48,49],[0,2,4],[0]),e5 [49] [4,0,2],a5 [8,9] [4,1,3,2] [0,1],([0,5,2,3,9],[4,3],[0,1]),([23,1,2,3,4],[5,2],[0,1]),e5 [68,49] [0,7],u5 [62,49] [0,7],a5 [5,6] [1,4,2,0,7] [0,1],a5 [5,8] [1,4,2,7,0] [0,1],a5 [78] [1,7,3,2] [1],a5 [31,9] [3,7,1,2] [0,1],u5 [35] [5,6,7,3,2],u5 [15,31] [7,0],a5 [31,5] [7,1,2] [0,1],([15,16,0,2,3],[7,4],[0,1]),a5 [54,49] [2,9] [1],e5 [65] [4,3,9,2],a5 [15,30] [7,2,9] [0,1],a5 [18] [7,4,9,2] [0,1],u5 [54,55] [7,9,3,2],u5 [15,8] [0,10],u5 [15,6] [0,10],([0,1,2,3,32],[1,11],[0,1]),([22,1,2,3,4],[1,11],[0]),a5 [31,16] [3,11] [0,1],([79,0,2,3,4],[7,11,1],[]),a5 [52] [1,7,2,12] [0,1],([69,0,2,3,4],[7,2,12],[]),([0,1,70,3,4],[7,2,12],[]),([83,0,1,2,3],[12,1,11],[]),a5 [51,49] [12,7,2,3,9] [0,1],([0,71,2,72,4],[2,0,13],[]),([0,51,77,3,4],[2,1,14],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_6 : checkNodesBT W_26 g_26 F_26 P_26_6 A_26 B_26_5 6 N_26_6 = true := by decide +kernel
def B_26_6 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_6
set_option maxRecDepth 500000 in
lemma B_26_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 6 xs.toFinset) B_26_6 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_5_ok C_26_6
def U_26_7 : List Nat := (r 0 5++[6,7,9,10,12]++r 14 7)
def P_26_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_26 r_26 S_26 ps_26 U_26_7
def N_26_7 : List NodeSpec := [a5 [48] [0,2,6,4] [0,1],a5 [51] [7,1,2,0] [0,1],a5 [5] [7,6,4,2,9] [0,1],u5 [15] [0,10],a5 [71] [10,2,12] [0,1],a5 [84] [10,2,12,14] [1],a5 [31] [15,3,7,2,12] [0,1],u5 [81] [15,7,2,0],a5 [8] [16,2,7,3,12] [0,1],u5 [77] [2,17,0],a5 [49] [18,2,0,7,9] [0,1],u5 [54] [1,7,2,0,19],a5 [85] [6,4,3,7,2,19] [1],u5 [72] [20,7,2,0,9]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_7 : checkNodesBT W_26 g_26 F_26 P_26_7 A_26 B_26_6 7 N_26_7 = true := by decide +kernel
def B_26_7 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_7
set_option maxRecDepth 500000 in
lemma B_26_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 7 xs.toFinset) B_26_7 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_6_ok C_26_7
def U_26_8 : List Nat := [6]
def P_26_8 : BT (Option BoundPool) := buildPoolsSubBT 5 W_26 r_26 S_26 ps_26 U_26_8
def N_26_8 : List NodeSpec := [a5 [] [6] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_8 : checkNodesBT W_26 g_26 F_26 P_26_8 A_26 B_26_7 8 N_26_8 = true := by decide +kernel
def B_26_8 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_8
set_option maxRecDepth 500000 in
lemma B_26_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 8 xs.toFinset) B_26_8 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_7_ok C_26_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_26_ok : forestRootCheck r_26 g_26 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_26_in : bucketContainsBT B_26_8 r_26 = true := by decide +kernel
lemma low_26 : Lower r_26 g_26 9 := lower_of_forestBT root_26_ok B_26_8_ok root_26_in
def g_27 := 0xfefce800fefce800
def r_27 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_27 : Lower r_27 g_27 8 := by
  have hc : Lower (varsOf 23) 0xfefee8e8fefee8e8 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 8) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) hc
def g_28 := 0xff8fce08ff8fce08
def r_28 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_28 : Lower r_28 g_28 8 := by
  have hc : Lower (varsOf 30) 0xffcfcf0cffcfcf0c 7 := carry_of (swaps := [(0,4),(1,4),(2,3),(3,4)]) (by decide +kernel) low_15
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,2,3)]) (by decide +kernel) hc
def g_29 := 0xfac08000fac08000
def r_29 : List Nat := varsOf 31
def p_29 : List Nat := [15,15,15,15,22,22,22,23,23,23,25,25,25,27,27,27,28,28,28,29,29,30,30]
def q_29 : List Nat := [14,13,11,7,20,18,6,21,19,7,24,17,9,26,19,11,24,20,12,21,13,26,14]
def F_29 : Nat := fullMask 23
set_option maxHeartbeats 0 in
lemma gp_29 : goodPairs g_29 p_29 q_29 := goodPairs_of (by decide +kernel)
def W_29 : BT Decor := buildWiresBT 3 (mkBase p_29 q_29 r_29) []
lemma W_29_ok : btAll (fun x => faithful p_29 q_29 x ∧ x.1 < 2^64) W_29 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_29 : List (List (Nat × Nat)) := [[]]
def A_29 : BT (List (Nat × Nat)) := btOfList 1 al_29
set_option maxHeartbeats 0 in
lemma A_29_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_29 = g_29) A_29 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_29_0 : Slice r_29 g_29 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffcc8800ffcc8800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_29_1 : Slice r_29 g_29 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xfafa8080fafa8080 5 := carry_of (swaps := [(0,1),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_29_2 : Slice r_29 g_29 (subcubeFast 0 3) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 3) (by decide +kernel) hc
def S_29 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 0 3,4)]
lemma S_29_ok : btAll (fun o => ∀ p, o = some p → Slice r_29 g_29 p.1 p.2) S_29 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_29_0) (forall_cons (fun _ h => by cases h; exact sl_29_1) (forall_cons (fun _ h => by cases h; exact sl_29_2) (fun _ h => (List.not_mem_nil h).elim))))
def ps_29 : BT (Option PoolSpec) := btOfList 2 [q 2 [],q 1 [],q 0 []]
def B_29_5 : BT (List (List Nat)) := BT.empty
lemma B_29_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_29 5 xs.toFinset) B_29_5 := .empty
def U_29_6 : List Nat := [0,1,2]
def P_29_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_29 r_29 S_29 ps_29 U_29_6
def N_29_6 : List NodeSpec := [e5 [] [0,1,2]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_29_6 : checkNodesBT W_29 g_29 F_29 P_29_6 A_29 B_29_5 6 N_29_6 = true := by decide +kernel
def B_29_6 : BT (List (List Nat)) := buildBucketsBT W_29 N_29_6
set_option maxRecDepth 500000 in
lemma B_29_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_29 6 xs.toFinset) B_29_6 :=
  buildBucketsBT_sound (by decide) gp_29 W_29_ok (buildPoolsSubBT_sound S_29_ok) A_29_ok B_29_5_ok C_29_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_29_ok : forestRootCheck r_29 g_29 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,6,22)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_29_in : bucketContainsBT B_29_6 r_29 = true := by decide +kernel
lemma low_29 : Lower r_29 g_29 7 := lower_of_forestBT root_29_ok B_29_6_ok root_29_in
def g_30 := 0xfff8e800fff8e800
def r_30 : List Nat := varsOf 31
def p_30 : List Nat := [11,11,11,13,13,13,14,14,14,15,19,19,19,20,20,21,21,22,22,23,24,24,25,25,26,26,28]
def q_30 : List Nat := [10,9,3,12,9,5,12,10,6,7,18,17,3,16,4,17,5,18,6,7,16,8,17,9,18,10,12]
def F_30 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_30 : goodPairs g_30 p_30 q_30 := goodPairs_of (by decide +kernel)
def W_30 : BT Decor := buildWiresBT 3 (mkBase p_30 q_30 r_30) [(1,2,4)]
lemma W_30_ok : btAll (fun x => faithful p_30 q_30 x ∧ x.1 < 2^64) W_30 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_30 : List (List (Nat × Nat)) := [[]]
def A_30 : BT (List (Nat × Nat)) := btOfList 1 al_30
set_option maxHeartbeats 0 in
lemma A_30_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_30 = g_30) A_30 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_30_0 : Slice r_30 g_30 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffcfc00fffcfc00 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_1 : Slice r_30 g_30 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfff0a000fff0a000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_2 : Slice r_30 g_30 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffafa00fffafa00 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_3 : Slice r_30 g_30 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xff888800ff888800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_4 : Slice r_30 g_30 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfff0c000fff0c000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_5 : Slice r_30 g_30 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_30_6 : Slice r_30 g_30 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) 0xf8f8e0e0f8f8e0e0 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_30 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 1 0,5),some (subcubeFast 16 8,4),some (identDom 2 3,6)]
lemma S_30_ok : btAll (fun o => ∀ p, o = some p → Slice r_30 g_30 p.1 p.2) S_30 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_30_0) (forall_cons (fun _ h => by cases h; exact sl_30_1) (forall_cons (fun _ h => by cases h; exact sl_30_2) (forall_cons (fun _ h => by cases h; exact sl_30_3) (forall_cons (fun _ h => by cases h; exact sl_30_4) (forall_cons (fun _ h => by cases h; exact sl_30_5) (forall_cons (fun _ h => by cases h; exact sl_30_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_30 : BT (Option PoolSpec) := btOfList 3 [q 4 [],q 0 [],q 1 [],q 2 [],q 5 [],q 3 [],q 6 []]
def B_30_5 : BT (List (List Nat)) := BT.empty
lemma B_30_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_30 5 xs.toFinset) B_30_5 := .empty
def U_30_6 : List Nat := (r 0 6)
def P_30_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_30 r_30 S_30 ps_30 U_30_6
def N_30_6 : List NodeSpec := [e5 [5] (r 0 6)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_30_6 : checkNodesBT W_30 g_30 F_30 P_30_6 A_30 B_30_5 6 N_30_6 = true := by decide +kernel
def B_30_6 : BT (List (List Nat)) := buildBucketsBT W_30 N_30_6
set_option maxRecDepth 500000 in
lemma B_30_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_30 6 xs.toFinset) B_30_6 :=
  buildBucketsBT_sound (by decide) gp_30 W_30_ok (buildPoolsSubBT_sound S_30_ok) A_30_ok B_30_5_ok C_30_6
def U_30_7 : List Nat := (r 0 7)
def P_30_7 : BT (Option BoundPool) := buildPoolsSubBT 3 W_30 r_30 S_30 ps_30 U_30_7
def N_30_7 : List NodeSpec := [u5 [] [2,1,3,5,0,6,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_30_7 : checkNodesBT W_30 g_30 F_30 P_30_7 A_30 B_30_6 7 N_30_7 = true := by decide +kernel
def B_30_7 : BT (List (List Nat)) := buildBucketsBT W_30 N_30_7
set_option maxRecDepth 500000 in
lemma B_30_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_30 7 xs.toFinset) B_30_7 :=
  buildBucketsBT_sound (by decide) gp_30 W_30_ok (buildPoolsSubBT_sound S_30_ok) A_30_ok B_30_6_ok C_30_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_30_ok : forestRootCheck r_30 g_30 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_30_in : bucketContainsBT B_30_7 r_30 = true := by decide +kernel
lemma low_30 : Lower r_30 g_30 8 := lower_of_forestBT root_30_ok B_30_7_ok root_30_in
def g_31 := 0xe880e880e880e880
def r_31 : List Nat := varsOf 15
def p_31 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14]
def q_31 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6]
def F_31 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_31 : goodPairs g_31 p_31 q_31 := goodPairs_of (by decide +kernel)
def W_31 : BT Decor := buildWiresBT 4 (mkBase p_31 q_31 r_31) [(0,0,1),(0,0,2),(0,1,2),(0,6,3),(3,7,0),(0,2,3),(3,9,0),(0,4,2)]
lemma W_31_ok : btAll (fun x => faithful p_31 q_31 x ∧ x.1 < 2^64) W_31 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_31 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,2),(2,3)],[(0,1)],[(0,1),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)],[(0,1),(1,2),(2,3)],[(0,2),(1,3),(2,3)]]
def A_31 : BT (List (Nat × Nat)) := btOfList 4 al_31
set_option maxHeartbeats 0 in
lemma A_31_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_31 = g_31) A_31 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_31_0 : Slice r_31 g_31 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_31_1 : Slice r_31 g_31 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_31_2 : Slice r_31 g_31 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_31_3 : Slice r_31 g_31 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
def S_31 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4)]
lemma S_31_ok : btAll (fun o => ∀ p, o = some p → Slice r_31 g_31 p.1 p.2) S_31 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_31_0) (forall_cons (fun _ h => by cases h; exact sl_31_1) (forall_cons (fun _ h => by cases h; exact sl_31_2) (forall_cons (fun _ h => by cases h; exact sl_31_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_31 : BT (Option PoolSpec) := btOfList 2 [q 1 [],q 0 [],q 2 [],q 3 []]
def B_31_2 : BT (List (List Nat)) := BT.empty
lemma B_31_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_31 2 xs.toFinset) B_31_2 := .empty
def U_31_3 : List Nat := [0,1]
def P_31_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_31 r_31 S_31 ps_31 U_31_3
def N_31_3 : List NodeSpec := [([4,5,6,3],[0,1],[]),([8,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_31_3 : checkNodesBT W_31 g_31 F_31 P_31_3 A_31 B_31_2 3 N_31_3 = true := by decide +kernel
def B_31_3 : BT (List (List Nat)) := buildBucketsBT W_31 N_31_3
set_option maxRecDepth 500000 in
lemma B_31_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_31 3 xs.toFinset) B_31_3 :=
  buildBucketsBT_sound (by decide) gp_31 W_31_ok (buildPoolsSubBT_sound S_31_ok) A_31_ok B_31_2_ok C_31_3
def U_31_4 : List Nat := [0,2,3]
def P_31_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_31 r_31 S_31 ps_31 U_31_4
def N_31_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([11,0,1,2,3],[3],[9]),([10,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_31_4 : checkNodesBT W_31 g_31 F_31 P_31_4 A_31 B_31_3 4 N_31_4 = true := by decide +kernel
def B_31_4 : BT (List (List Nat)) := buildBucketsBT W_31 N_31_4
set_option maxRecDepth 500000 in
lemma B_31_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_31 4 xs.toFinset) B_31_4 :=
  buildBucketsBT_sound (by decide) gp_31 W_31_ok (buildPoolsSubBT_sound S_31_ok) A_31_ok B_31_3_ok C_31_4
def U_31_5 : List Nat := (r 0 4)
def P_31_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_31 r_31 S_31 ps_31 U_31_5
def N_31_5 : List NodeSpec := [([4,0,1,2,3],(r 0 4),[0,1,4,5,8,10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_31_5 : checkNodesBT W_31 g_31 F_31 P_31_5 A_31 B_31_4 5 N_31_5 = true := by decide +kernel
def B_31_5 : BT (List (List Nat)) := buildBucketsBT W_31 N_31_5
set_option maxRecDepth 500000 in
lemma B_31_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_31 5 xs.toFinset) B_31_5 :=
  buildBucketsBT_sound (by decide) gp_31 W_31_ok (buildPoolsSubBT_sound S_31_ok) A_31_ok B_31_4_ok C_31_5
def U_31_6 : List Nat := (r 0 4)
def P_31_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_31 r_31 S_31 ps_31 U_31_6
def N_31_6 : List NodeSpec := [([0,1,2,3],[1,0,2,3],[0,2,3,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_31_6 : checkNodesBT W_31 g_31 F_31 P_31_6 A_31 B_31_5 6 N_31_6 = true := by decide +kernel
def B_31_6 : BT (List (List Nat)) := buildBucketsBT W_31 N_31_6
set_option maxRecDepth 500000 in
lemma B_31_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_31 6 xs.toFinset) B_31_6 :=
  buildBucketsBT_sound (by decide) gp_31 W_31_ok (buildPoolsSubBT_sound S_31_ok) A_31_ok B_31_5_ok C_31_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_31_ok : forestRootCheck r_31 g_31 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_31_in : bucketContainsBT B_31_6 r_31 = true := by decide +kernel
lemma low_31 : Lower r_31 g_31 7 := lower_of_forestBT root_31_ok B_31_6_ok root_31_in
def g_32 := 0xb0b0b0b0b0b0b0b0
def r_32 : List Nat := varsOf 7
set_option maxHeartbeats 0 in
lemma low_32 : Lower r_32 g_32 2 := count_of (essPairs := [(VAR 0,6,7),(VAR 1,4,6),(VAR 2,0,4)]) (by decide +kernel)
def g_33 := 0xf2f2f2f2f2f2f2f2
def r_33 : List Nat := varsOf 7
set_option maxHeartbeats 0 in
lemma low_33 : Lower r_33 g_33 2 := count_of (essPairs := [(VAR 0,0,1),(VAR 1,1,3),(VAR 2,0,4)]) (by decide +kernel)
def g_34 := 0xef08ef08ef08ef08
def r_34 : List Nat := varsOf 15
def p_34 : List Nat := [3,3,8,9,10,13,13,14,14,15]
def q_34 : List Nat := [2,1,0,1,2,12,5,12,6,7]
def F_34 : Nat := fullMask 10
set_option maxHeartbeats 0 in
lemma gp_34 : goodPairs g_34 p_34 q_34 := goodPairs_of (by decide +kernel)
def W_34 : BT Decor := buildWiresBT 7 (mkBase p_34 q_34 r_34) [(0,1,2),(1,4,0),(1,1,3),(0,5,6),(1,0,1),(0,0,1),(1,9,2),(0,8,10),(0,2,3),(1,2,3),(3,12,13),(0,1,3),(3,15,6),(1,1,2),(0,0,17),(0,0,2),(1,0,2),(0,1,20),(3,1,2),(1,22,9),(0,8,2),(3,4,17),(1,15,0),(3,9,8),(3,4,6),(1,0,3),(0,1,29),(2,1,2),(3,31,8),(3,15,17),(3,2,3),(3,34,0),(2,2,3),(3,36,0),(1,36,1),(3,0,3),(3,39,2),(2,0,3),(3,2,29),(0,0,3),(3,15,2),(1,19,1),(2,1,3),(3,46,2),(2,8,2),(2,0,1),(2,1,0),(1,43,2),(1,34,1),(3,1,3),(1,53,2),(3,0,2),(0,2,29),(0,0,6),(3,9,2),(3,4,0),(3,1,29),(3,1,20),(3,50,2),(1,41,2),(1,49,2),(2,0,2),(3,15,0),(1,43,1)]
lemma W_34_ok : btAll (fun x => faithful p_34 q_34 x ∧ x.1 < 2^64) W_34 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_34 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_34 : BT (List (Nat × Nat)) := btOfList 1 al_34
set_option maxHeartbeats 0 in
lemma A_34_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_34 = g_34) A_34 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_34_0 : Slice r_34 g_34 (subcubeFast 1 0) 2 := by
  have hc : Lower (varsOf 14) 0xcf00cf00cf00cf00 2 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_32
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_1 : Slice r_34 g_34 (subcubeFast 0 1) 2 := by
  have hc : Lower (varsOf 14) 0xff0cff0cff0cff0c 2 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_33
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_2 : Slice r_34 g_34 (subcubeFast 2 0) 2 := by
  have hc : Lower (varsOf 13) 0xaf00af00af00af00 2 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_32
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_3 : Slice r_34 g_34 (subcubeFast 0 2) 2 := by
  have hc : Lower (varsOf 13) 0xff0aff0aff0aff0a 2 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_33
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_4 : Slice r_34 g_34 (subcubeFast 8 0) 2 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_16
set_option maxHeartbeats 0 in
lemma sl_34_5 : Slice r_34 g_34 (subcubeFast 0 8) 2 := by
  have hc : Lower (varsOf 7) 0x1010101010101010 2 := carry_of (swaps := [(0,1),(1,2)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
def S_34 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,2),some (subcubeFast 0 1,2),some (subcubeFast 2 0,2),some (subcubeFast 0 2,2),some (subcubeFast 8 0,2),some (subcubeFast 0 8,2)]
lemma S_34_ok : btAll (fun o => ∀ p, o = some p → Slice r_34 g_34 p.1 p.2) S_34 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_34_0) (forall_cons (fun _ h => by cases h; exact sl_34_1) (forall_cons (fun _ h => by cases h; exact sl_34_2) (forall_cons (fun _ h => by cases h; exact sl_34_3) (forall_cons (fun _ h => by cases h; exact sl_34_4) (forall_cons (fun _ h => by cases h; exact sl_34_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_34 : BT (Option PoolSpec) := btOfList 3 [q 1 [],q 3 [],q 2 [],q 0 [],q 4 [],q 5 []]
def B_34_0 : BT (List (List Nat)) := BT.empty
lemma B_34_0_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 0 xs.toFinset) B_34_0 := .empty
def U_34_1 : List Nat := []
def P_34_1 : BT (Option BoundPool) := buildPoolsSubBT 3 W_34 r_34 S_34 ps_34 U_34_1
def N_34_1 : List NodeSpec := [([7,3],[],[]),([11,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_1 : checkNodesBT W_34 g_34 F_34 P_34_1 A_34 B_34_0 1 N_34_1 = true := by decide +kernel
def B_34_1 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_1
set_option maxRecDepth 500000 in
lemma B_34_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 1 xs.toFinset) B_34_1 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound S_34_ok) A_34_ok B_34_0_ok C_34_1
def U_34_2 : List Nat := []
def P_34_2 : BT (Option BoundPool) := buildPoolsSubBT 3 W_34 r_34 S_34 ps_34 U_34_2
def N_34_2 : List NodeSpec := [([14,0,1],[],[]),([16,0,2],[],[]),([18,15,3],[],[1]),([8,10,3],[],[0]),([19,21,3],[],[0]),([0,23,3],[],[]),([9,24,3],[],[0]),([25,0,3],[],[]),([5,3,6],[],[0]),([26,17,3],[],[1]),([27,2,3],[],[]),([28,0,3],[],[]),([19,30,3],[],[1]),([5,17,3],[],[0]),([0,32,3],[],[]),([33,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_2 : checkNodesBT W_34 g_34 F_34 P_34_2 A_34 B_34_1 2 N_34_2 = true := by decide +kernel
def B_34_2 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_2
set_option maxRecDepth 500000 in
lemma B_34_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 2 xs.toFinset) B_34_2 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound S_34_ok) A_34_ok B_34_1_ok C_34_2
def U_34_3 : List Nat := (r 0 4)
def P_34_3 : BT (Option BoundPool) := buildPoolsSubBT 3 W_34 r_34 S_34 ps_34 U_34_3
def N_34_3 : List NodeSpec := [([49,0,4,3],[0],[0]),([22,9,0,3],[0],[0]),([42,0,1,3],[0],[]),([0,1,64,3],[0],[]),([57,1,2,3],[1],[1]),([18,1,2,3],[1],[1]),([40,0,1,3],[0,1,2],[]),([44,0,1,3],[2],[]),([49,1,20,3],[2],[1]),([0,1,24,3],[0,3],[0]),([0,67,2,3],[3],[1]),([0,45,2,3],[3],[1]),([0,62,1,3],[3],[]),([65,1,8,3],[3],[1]),([0,1,10,3],[3,0],[0]),([9,8,2,3],[3,0],[0]),([18,1,3],[3,1],[0]),([0,45,3],[3,1],[1]),([0,1,63,3],[3,2,1],[]),([66,1,2,3],[],[]),([60,0,2,3],[],[]),([59,1,3],[],[]),([61,0,2,3],[],[]),([0,1,56,3],[],[]),([65,55,1,3],[],[1]),([19,1,20,3],[],[0,1]),([65,39,1,3],[],[1]),([43,1,20,3],[],[1]),([0,52,2,3],[],[]),([61,0,3],[],[]),([37,1,3],[],[]),([49,50,2,3],[],[0]),([36,34,0,1],[],[0]),([37,1,2,3],[],[]),([0,38,3],[],[]),([0,1,12,13],[],[0]),([41,39,1,2],[],[1]),([43,1,2,29],[],[1]),([0,1,47,3],[],[]),([35,1,3],[],[]),([48,0,1,3],[],[]),([19,1,3,29],[],[0,1]),([0,1,51,3],[],[]),([0,38,2,3],[],[]),([0,52,3],[],[]),([0,1,54,3],[],[]),([41,55,1,3],[],[1]),([35,1,2,3],[],[]),([58,0,1,3],[],[]),([59,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_3 : checkNodesBT W_34 g_34 F_34 P_34_3 A_34 B_34_2 3 N_34_3 = true := by decide +kernel
def B_34_3 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_3
set_option maxRecDepth 500000 in
lemma B_34_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 3 xs.toFinset) B_34_3 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound S_34_ok) A_34_ok B_34_2_ok C_34_3
def U_34_4 : List Nat := (r 0 6)
def P_34_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_34 r_34 S_34 ps_34 U_34_4
def N_34_4 : List NodeSpec := [([0,1,2,3,29],[0],[0,1]),([0,1,8,2,3],[0,1],[0,1]),([53,0,1,2,3],[1],[0,1]),([22,0,1,2,3],[2,1],[1]),([0,1,2,20,3],[0,3],[0,1]),([65,0,1,2,3],[0,3],[0]),([19,0,1,2,3],[0,3],[0,1]),([41,0,1,2,3],[3],[0,1]),([43,0,1,2,3],[3],[0,1]),([49,0,1,2,3],[3,1],[0,1]),([9,0,1,2,3],[3,2],[0,1]),([0,1,12,3],[3,0,2,1,4],[]),([34,0,1,3],[3,4,0,1,2],[0,1]),([0,1,20,3],[0,2,1,4,5],[0,1]),([22,0,1,3],[3,0,1,5,4],[0,1]),([0,1,3,13],[3,0,2,1,5],[]),([65,0,1,3],[3,1,2,5,4],[0]),([19,0,1,3],[3,1,2,5,4],[0,1]),([36,0,1,3],[3,5,0,1,2],[0,1]),([36,0,1,2,3],[4,5],[0,1]),([34,0,1,2,3],[5,4],[0,1]),([0,1,12,2,3],[5,4],[0]),([0,1,2,3,13],[5,4],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_4 : checkNodesBT W_34 g_34 F_34 P_34_4 A_34 B_34_3 4 N_34_4 = true := by decide +kernel
def B_34_4 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_4
set_option maxRecDepth 500000 in
lemma B_34_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 4 xs.toFinset) B_34_4 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound S_34_ok) A_34_ok B_34_3_ok C_34_4
def U_34_5 : List Nat := []
def P_34_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_34 r_34 S_34 ps_34 U_34_5
def N_34_5 : List NodeSpec := [([0,1,2,3],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_5 : checkNodesBT W_34 g_34 F_34 P_34_5 A_34 B_34_4 5 N_34_5 = true := by decide +kernel
def B_34_5 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_5
set_option maxRecDepth 500000 in
lemma B_34_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 5 xs.toFinset) B_34_5 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound S_34_ok) A_34_ok B_34_4_ok C_34_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_34_ok : forestRootCheck r_34 g_34 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,3,7),(VAR 3,0,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_34_in : bucketContainsBT B_34_5 r_34 = true := by decide +kernel
lemma low_34 : Lower r_34 g_34 6 := lower_of_forestBT root_34_ok B_34_5_ok root_34_in
def g_35 := 0xcf08cf08cf08cf08
def r_35 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_35 : Lower r_35 g_35 5 := by
  have hc : Lower (varsOf 14) 0xcf0ccf0ccf0ccf0c 4 := carry_of (swaps := [(0,3),(1,3)]) (by decide +kernel) low_13
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,2,3)]) (by decide +kernel) hc
def g_36 := 0xf3a0f3a0f3a0f3a0
def r_36 : List Nat := varsOf 15
def p_36 : List Nat := [5,5,7,7,8,9,12,14,14,15]
def q_36 : List Nat := [4,1,6,3,0,1,4,10,6,11]
def F_36 : Nat := fullMask 10
set_option maxHeartbeats 0 in
lemma gp_36 : goodPairs g_36 p_36 q_36 := goodPairs_of (by decide +kernel)
def W_36 : BT Decor := buildWiresBT 2 (mkBase p_36 q_36 r_36) []
lemma W_36_ok : btAll (fun x => faithful p_36 q_36 x ∧ x.1 < 2^64) W_36 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_36 : List (List (Nat × Nat)) := [[]]
def A_36 : BT (List (Nat × Nat)) := btOfList 1 al_36
set_option maxHeartbeats 0 in
lemma A_36_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_36 = g_36) A_36 := btAll_ofList (autos_of (by decide +kernel))
def S_36 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_36_ok : btAll (fun o => ∀ p, o = some p → Slice r_36 g_36 p.1 p.2) S_36 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_36 : BT (Option PoolSpec) := btOfList 1 []
def B_36_2 : BT (List (List Nat)) := BT.empty
lemma B_36_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_36 2 xs.toFinset) B_36_2 := .empty
def U_36_3 : List Nat := []
def P_36_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_36 r_36 S_36 ps_36 U_36_3
def N_36_3 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_36_3 : checkNodesBT W_36 g_36 F_36 P_36_3 A_36 B_36_2 3 N_36_3 = true := by decide +kernel
def B_36_3 : BT (List (List Nat)) := buildBucketsBT W_36 N_36_3
set_option maxRecDepth 500000 in
lemma B_36_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_36 3 xs.toFinset) B_36_3 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok (buildPoolsSubBT_sound S_36_ok) A_36_ok B_36_2_ok C_36_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_36_ok : forestRootCheck r_36 g_36 [(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,0,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_36_in : bucketContainsBT B_36_3 r_36 = true := by decide +kernel
lemma low_36 : Lower r_36 g_36 4 := lower_of_forestBT root_36_ok B_36_3_ok root_36_in
def g_37 := 0xffafce08ffafce08
def r_37 : List Nat := varsOf 31
def p_37 : List Nat := [3,3,9,9,10,10,14,14,15,15,16,17,18,21,21,23,23,24,28,28,29,30]
def q_37 : List Nat := [2,1,8,1,8,2,12,6,13,7,0,1,2,20,5,22,7,8,20,12,13,22]
def F_37 : Nat := fullMask 22
set_option maxHeartbeats 0 in
lemma gp_37 : goodPairs g_37 p_37 q_37 := goodPairs_of (by decide +kernel)
def W_37 : BT Decor := buildWiresBT 5 (mkBase p_37 q_37 r_37) [(1,3,4),(3,2,5),(2,2,4),(3,7,0),(1,2,3),(1,9,4),(1,7,3),(2,9,4),(2,0,3),(1,13,2),(2,0,2),(1,15,3),(0,0,2),(1,17,3),(2,2,3),(1,2,4),(1,1,4)]
lemma W_37_ok : btAll (fun x => faithful p_37 q_37 x ∧ x.1 < 2^64) W_37 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_37 : List (List (Nat × Nat)) := [[]]
def A_37 : BT (List (Nat × Nat)) := btOfList 1 al_37
set_option maxHeartbeats 0 in
lemma A_37_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_37 = g_37) A_37 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_37_0 : Slice r_37 g_37 (subcubeFast 2 0) 6 := by
  have hc : Lower (varsOf 29) 0xffaf0a00ffaf0a00 6 := carry_of (swaps := [(1,4),(3,4)]) (by decide +kernel) low_34
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_1 : Slice r_37 g_37 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xffffcf0cffffcf0c 5 := carry_of (swaps := [(0,4),(1,4),(3,4)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_2 : Slice r_37 g_37 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xffafff0affafff0a 5 := carry_of (swaps := [(1,4)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_3 : Slice r_37 g_37 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xafaf0808afaf0808 5 := carry_of (swaps := [(0,1),(3,4)]) (by decide +kernel) low_35
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_4 : Slice r_37 g_37 (subcubeFast 20 0) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 20) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_5 : Slice r_37 g_37 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) 0xafaf0a0aafaf0a0a 4 := carry_of (swaps := [(1,3),(3,4)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_6 : Slice r_37 g_37 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) 0xcf0ccf0ccf0ccf0c 4 := carry_of (swaps := [(0,3),(1,3)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_7 : Slice r_37 g_37 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 27) 0xffaacc00ffaacc00 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_8 : Slice r_37 g_37 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) 0xff0fcc00ff0fcc00 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_36
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_9 : Slice r_37 g_37 (subcubeFast 16 8) 2 := by
  have hc : Lower (varsOf 7) 0xcececececececece 2 := carry_of (swaps := [(1,2)]) (by decide +kernel) low_33
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_10 : Slice r_37 g_37 (subcubeFast 24 0) 2 := by
  exact slice_fast_direct_f (z := 24) (o := 0) (by decide +kernel) low_16
set_option maxHeartbeats 0 in
lemma sl_37_11 : Slice r_37 g_37 (subcubeFast 3 0) 2 := by
  have hc : Lower (varsOf 28) 0xff0f0000ff0f0000 2 := carry_of (swaps := [(0,3),(1,4),(2,4)]) (by decide +kernel) low_32
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_12 : Slice r_37 g_37 (subcubeFast 0 18) 2 := by
  have hc : Lower (varsOf 13) 0x50005000500050 2 := carry_of (swaps := [(0,1),(1,3),(2,3)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 18) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_13 : Slice r_37 g_37 (subcubeFast 2 16) 2 := by
  have hc : Lower (varsOf 13) 0x50005000500050 2 := carry_of (swaps := [(0,1),(1,3),(2,3)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 2) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_14 : Slice r_37 g_37 (subcubeFast 1 2) 2 := by
  have hc : Lower (varsOf 28) 0xff0fff00ff0fff00 2 := carry_of (swaps := [(0,3),(1,4),(2,4),(3,4)]) (by decide +kernel) low_33
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_15 : Slice r_37 g_37 (subcubeFast 0 9) 2 := by
  have hc : Lower (varsOf 22) 0x303000003030 2 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 9) (by decide +kernel) hc
def S_37 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 2 0,6),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 8 0,5),some (subcubeFast 20 0,4),some (subcubeFast 8 2,4),some (subcubeFast 16 1,4),some (subcubeFast 0 4,4),some (subcubeFast 1 0,4),some (subcubeFast 16 8,2),some (subcubeFast 24 0,2),some (subcubeFast 3 0,2),some (subcubeFast 0 18,2),some (subcubeFast 2 16,2),some (subcubeFast 1 2,2),some (subcubeFast 0 9,2)]
lemma S_37_ok : btAll (fun o => ∀ p, o = some p → Slice r_37 g_37 p.1 p.2) S_37 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_37_0) (forall_cons (fun _ h => by cases h; exact sl_37_1) (forall_cons (fun _ h => by cases h; exact sl_37_2) (forall_cons (fun _ h => by cases h; exact sl_37_3) (forall_cons (fun _ h => by cases h; exact sl_37_4) (forall_cons (fun _ h => by cases h; exact sl_37_5) (forall_cons (fun _ h => by cases h; exact sl_37_6) (forall_cons (fun _ h => by cases h; exact sl_37_7) (forall_cons (fun _ h => by cases h; exact sl_37_8) (forall_cons (fun _ h => by cases h; exact sl_37_9) (forall_cons (fun _ h => by cases h; exact sl_37_10) (forall_cons (fun _ h => by cases h; exact sl_37_11) (forall_cons (fun _ h => by cases h; exact sl_37_12) (forall_cons (fun _ h => by cases h; exact sl_37_13) (forall_cons (fun _ h => by cases h; exact sl_37_14) (forall_cons (fun _ h => by cases h; exact sl_37_15) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))
def ps_37 : BT (Option PoolSpec) := btOfList 5 [q 8 [],q 1 [],q 0 [],q 2 [],q 4 [],q 11 [],q 12 [],q 7 [],q 13 [],q 9 [],q 5 [8245],q 6 [8245],q 3 [],q 14 [],q 6 [],q 5 [],q 10 [],q 15 [],q 6 [12297],q 0 [12297]]
def B_37_4 : BT (List (List Nat)) := BT.empty
lemma B_37_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_37 4 xs.toFinset) B_37_4 := .empty
def U_37_5 : List Nat := (r 0 14)
def P_37_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_37 r_37 S_37 ps_37 U_37_5
def N_37_5 : List NodeSpec := [([6,0,1,3,4],(r 0 5),[]),([0,1,3,18,4],[0,4,5,3],[]),([8,1,3,4],[0,5,6,4],[]),([0,1,3,4,10],[0,1,4,2,3,7],[]),([0,1,3,11,4],[0,1,8,3,4],[]),([12,0,1,3,4],(r 0 4++[9]),[]),([0,1,14,3,4],[10,11],[]),e5 [16] [2,3,7,12],([0,1,3,16,4],[0,13,2,3,9],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_37_5 : checkNodesBT W_37 g_37 F_37 P_37_5 A_37 B_37_4 5 N_37_5 = true := by decide +kernel
def B_37_5 : BT (List (List Nat)) := buildBucketsBT W_37 N_37_5
set_option maxRecDepth 500000 in
lemma B_37_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_37 5 xs.toFinset) B_37_5 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok (buildPoolsSubBT_sound S_37_ok) A_37_ok B_37_4_ok C_37_5
def U_37_6 : List Nat := (r 0 10++r 12 8)
def P_37_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_37 r_37 S_37 ps_37 U_37_6
def N_37_6 : List NodeSpec := [u5 [15] [4,2,3,1,12,7,0],e5 [9] ([4,7]++r 0 4++[12]),([17,0,1,3,4],[1,3,2,12,4,5,13],[0]),([15,0,1,3,4],[2,0,3,12,14,5,13],[0]),([7,0,1,3,4],[4,14,3,2,12,8,6],[0]),u5 [13] [12,2,3,4,0,7,14,5,13],([0,1,3,4,20],[14,8,6,2,3,12,4],[0]),([19,0,1,3,4],[4,1,0,2,15],[]),([0,2,3,4,21],[4,14,15],[]),u5 [5] [4,14,15,9,16],([0,1,3,9,4],[15,0,17,4,18,19,9],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_37_6 : checkNodesBT W_37 g_37 F_37 P_37_6 A_37 B_37_5 6 N_37_6 = true := by decide +kernel
def B_37_6 : BT (List (List Nat)) := buildBucketsBT W_37 N_37_6
set_option maxRecDepth 500000 in
lemma B_37_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_37 6 xs.toFinset) B_37_6 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok (buildPoolsSubBT_sound S_37_ok) A_37_ok B_37_5_ok C_37_6
def U_37_7 : List Nat := [2,4,12,14]
def P_37_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_37 r_37 S_37 ps_37 U_37_7
def N_37_7 : List NodeSpec := [u5 [] [2,4,12,14]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_37_7 : checkNodesBT W_37 g_37 F_37 P_37_7 A_37 B_37_6 7 N_37_7 = true := by decide +kernel
def B_37_7 : BT (List (List Nat)) := buildBucketsBT W_37 N_37_7
set_option maxRecDepth 500000 in
lemma B_37_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_37 7 xs.toFinset) B_37_7 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok (buildPoolsSubBT_sound S_37_ok) A_37_ok B_37_6_ok C_37_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_37_ok : forestRootCheck r_37 g_37 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,3,7),(VAR 3,1,9),(VAR 4,0,16)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_37_in : bucketContainsBT B_37_7 r_37 = true := by decide +kernel
lemma low_37 : Lower r_37 g_37 8 := lower_of_forestBT root_37_ok B_37_7_ok root_37_in
def g_38 := 0x80f880f880f880f8
def r_38 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_38 : Lower r_38 g_38 5 := by
  have hc : Lower (varsOf 14) 0xc0fcc0fcc0fcc0fc 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_13
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,2,3)]) (by decide +kernel) hc
def g_39 := 0x8e008e008e008e00
def r_39 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_39 : Lower r_39 g_39 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_13) (G := g_13) (essPairs := [(VAR 3,1,9)]) (by decide +kernel) low_13
def g_40 := 0xf220f220f220f220
def r_40 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_40 : Lower r_40 g_40 5 := by
  have hc : Lower (varsOf 14) 0xf330f330f330f330 4 := carry_of (swaps := [(0,3),(1,2),(2,3)]) (by decide +kernel) low_13
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_41 := 0xfc40fc40fc40fc40
def r_41 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_41 : Lower r_41 g_41 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_42 := 0xf280f280f280f280
def r_42 : List Nat := varsOf 15
def p_42 : List Nat := [7,7,7,9,9,12,12,13,14,14,15]
def q_42 : List Nat := [6,5,3,8,1,8,4,5,10,6,11]
def F_42 : Nat := fullMask 11
set_option maxHeartbeats 0 in
lemma gp_42 : goodPairs g_42 p_42 q_42 := goodPairs_of (by decide +kernel)
def W_42 : BT Decor := buildWiresBT 2 (mkBase p_42 q_42 r_42) []
lemma W_42_ok : btAll (fun x => faithful p_42 q_42 x ∧ x.1 < 2^64) W_42 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_42 : List (List (Nat × Nat)) := [[]]
def A_42 : BT (List (Nat × Nat)) := btOfList 1 al_42
set_option maxHeartbeats 0 in
lemma A_42_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_42 = g_42) A_42 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_42_0 : Slice r_42 g_42 (subcubeFast 0 1) 3 := by
  have hc : Lower (varsOf 14) 0xf3c0f3c0f3c0f3c0 3 := carry_of (swaps := [(0,3),(1,2),(2,3)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_1 : Slice r_42 g_42 (subcubeFast 4 0) 2 := by
  have hc : Lower (varsOf 11) 0x2200220022002200 2 := carry_of (swaps := [(1,2),(2,3)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_2 : Slice r_42 g_42 (subcubeFast 0 8) 2 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_33
def S_42 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,3),some (subcubeFast 4 0,2),some (subcubeFast 0 8,2)]
lemma S_42_ok : btAll (fun o => ∀ p, o = some p → Slice r_42 g_42 p.1 p.2) S_42 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_42_0) (forall_cons (fun _ h => by cases h; exact sl_42_1) (forall_cons (fun _ h => by cases h; exact sl_42_2) (fun _ h => (List.not_mem_nil h).elim))))
def ps_42 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 1 [],q 2 []]
def B_42_3 : BT (List (List Nat)) := BT.empty
lemma B_42_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_42 3 xs.toFinset) B_42_3 := .empty
def U_42_4 : List Nat := [0,1,2]
def P_42_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_42 r_42 S_42 ps_42 U_42_4
def N_42_4 : List NodeSpec := [([0,1,2,3],[0,1,2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_4 : checkNodesBT W_42 g_42 F_42 P_42_4 A_42 B_42_3 4 N_42_4 = true := by decide +kernel
def B_42_4 : BT (List (List Nat)) := buildBucketsBT W_42 N_42_4
set_option maxRecDepth 500000 in
lemma B_42_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_42 4 xs.toFinset) B_42_4 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_3_ok C_42_4
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_ok : forestRootCheck r_42 g_42 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_in : bucketContainsBT B_42_4 r_42 = true := by decide +kernel
lemma low_42 : Lower r_42 g_42 5 := lower_of_forestBT root_42_ok B_42_4_ok root_42_in
def g_43 := 0xfbe0fbe0fbe0fbe0
def r_43 : List Nat := varsOf 15
def p_43 : List Nat := [5,5,6,6,7,8,9,11,11,12,14]
def q_43 : List Nat := [4,1,4,2,3,0,1,10,3,4,10]
def F_43 : Nat := fullMask 11
set_option maxHeartbeats 0 in
lemma gp_43 : goodPairs g_43 p_43 q_43 := goodPairs_of (by decide +kernel)
def W_43 : BT Decor := buildWiresBT 2 (mkBase p_43 q_43 r_43) []
lemma W_43_ok : btAll (fun x => faithful p_43 q_43 x ∧ x.1 < 2^64) W_43 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_43 : List (List (Nat × Nat)) := [[]]
def A_43 : BT (List (Nat × Nat)) := btOfList 1 al_43
set_option maxHeartbeats 0 in
lemma A_43_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_43 = g_43) A_43 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_43_0 : Slice r_43 g_43 (subcubeFast 1 0) 3 := by
  have hc : Lower (varsOf 14) 0xf3c0f3c0f3c0f3c0 3 := carry_of (swaps := [(0,3),(1,2),(2,3)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_43_1 : Slice r_43 g_43 (subcubeFast 4 0) 2 := by
  have hc : Lower (varsOf 11) 0xbb00bb00bb00bb00 2 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_32
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_43_2 : Slice r_43 g_43 (subcubeFast 0 8) 2 := by
  have hc : Lower (varsOf 7) 0x404040404040404 2 := carry_of (swaps := [(0,1)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
def S_43 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,3),some (subcubeFast 4 0,2),some (subcubeFast 0 8,2)]
lemma S_43_ok : btAll (fun o => ∀ p, o = some p → Slice r_43 g_43 p.1 p.2) S_43 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_43_0) (forall_cons (fun _ h => by cases h; exact sl_43_1) (forall_cons (fun _ h => by cases h; exact sl_43_2) (fun _ h => (List.not_mem_nil h).elim))))
def ps_43 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 1 [],q 2 []]
def B_43_3 : BT (List (List Nat)) := BT.empty
lemma B_43_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_43 3 xs.toFinset) B_43_3 := .empty
def U_43_4 : List Nat := [0,1,2]
def P_43_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_43 r_43 S_43 ps_43 U_43_4
def N_43_4 : List NodeSpec := [([0,1,2,3],[0,1,2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_43_4 : checkNodesBT W_43 g_43 F_43 P_43_4 A_43 B_43_3 4 N_43_4 = true := by decide +kernel
def B_43_4 : BT (List (List Nat)) := buildBucketsBT W_43 N_43_4
set_option maxRecDepth 500000 in
lemma B_43_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_43 4 xs.toFinset) B_43_4 :=
  buildBucketsBT_sound (by decide) gp_43 W_43_ok (buildPoolsSubBT_sound S_43_ok) A_43_ok B_43_3_ok C_43_4
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_43_ok : forestRootCheck r_43 g_43 [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 3,0,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_43_in : bucketContainsBT B_43_4 r_43 = true := by decide +kernel
lemma low_43 : Lower r_43 g_43 5 := lower_of_forestBT root_43_ok B_43_4_ok root_43_in
def g_44 := 0xffffeee8fa80c000
def r_44 : List Nat := varsOf 63
def p_44 : List Nat := [14,14,14,15,15,15,23,23,23,23,25,25,25,27,27,27,28,28,28,29,29,30,30,35,35,35,37,37,37,38,38,38,39,41,41,41,42,42,42,43,45,45,46,48,48,49,49,50,50,51,52,52,53,54,56,56,58,60]
def q_44 : List Nat := [12,10,6,13,11,7,22,21,19,7,24,17,9,26,19,11,24,20,12,21,13,26,22,34,33,3,36,33,5,36,34,6,7,40,33,9,40,34,10,11,44,13,44,32,16,33,17,34,18,19,36,20,21,22,40,24,26,44]
def F_44 : Nat := fullMask 58
set_option maxHeartbeats 0 in
lemma gp_44 : goodPairs g_44 p_44 q_44 := goodPairs_of (by decide +kernel)
def W_44 : BT Decor := buildWiresBT 10 (mkBase p_44 q_44 r_44) [(1,4,5),(0,0,6),(0,2,5),(1,8,3),(0,7,9),(1,7,9),(3,10,11),(0,7,2),(1,7,2),(3,13,14),(2,15,3),(2,7,9),(3,7,9),(0,1,11),(1,15,3),(3,10,1),(0,7,1),(1,3,5),(3,22,23),(1,22,3),(2,0,3),(0,26,6),(2,1,3),(1,28,4),(0,0,29),(1,2,5),(3,30,31),(2,1,2),(1,33,4),(0,0,34),(3,35,23),(2,0,4),(1,2,3),(0,0,38),(0,1,38),(1,40,4),(1,7,3),(0,1,2),(3,43,42),(1,43,4),(3,22,31),(2,14,3),(3,8,42),(3,37,38),(1,43,3),(1,33,7),(2,51,3),(2,1,4),(1,53,5),(0,0,54),(3,55,38),(0,1,5),(1,57,3),(1,27,8),(0,38,6),(0,0,1),(1,61,4),(1,57,4),(0,0,63),(3,64,23),(3,57,42),(1,53,3),(0,0,67),(3,68,31),(3,22,38),(3,7,38),(0,0,9),(3,72,6),(2,26,8),(3,74,6),(3,2,42),(0,2,42),(1,13,3),(3,7,1),(0,0,23),(0,1,23),(1,81,4),(3,2,5),(1,83,4),(3,3,84),(3,85,0),(0,0,84),(2,2,5),(3,4,31),(0,1,31),(1,90,4),(2,0,2),(3,92,23),(2,26,4),(3,94,0),(1,95,8),(2,9,4),(3,97,0),(1,9,4),(3,2,99),(1,72,4),(2,2,4),(1,102,80),(3,102,31),(1,102,3),(0,0,105),(2,2,3),(3,7,2),(2,7,2),(1,109,3),(1,107,7),(2,38,4),(3,4,5),(1,113,3),(0,2,23),(1,38,4),(3,88,116),(1,112,5),(2,38,5),(2,0,40),(3,53,0),(0,0,5),(1,122,2),(1,122,4),(2,1,5),(1,125,4),(1,108,3),(3,37,9),(2,0,5),(3,129,38),(1,61,5),(0,38,131),(3,37,23),(0,0,82),(3,26,84),(0,1,42),(3,43,5),(1,137,4),(3,4,23),(3,112,0),(1,37,3),(0,141,31),(1,92,3),(1,61,3),(2,50,5),(0,0,50),(3,7,23),(1,107,5),(0,50,6),(3,61,5),(1,150,4),(1,2,4),(3,3,152),(0,26,5),(1,154,3),(1,33,3),(1,37,5),(1,7,43),(3,146,5),(1,26,4),(3,37,50),(3,43,6),(3,61,6),(2,105,5),(3,164,0),(0,0,2),(1,166,3),(0,167,6),(1,122,43),(1,169,3),(0,144,6),(3,26,5),(1,43,172),(1,53,122),(3,83,6),(0,67,31),(0,42,5),(1,95,5),(3,3,5),(1,179,4),(3,43,180),(2,0,43),(1,182,3),(3,166,6),(0,105,5),(2,0,185),(2,58,4),(1,3,4),(0,188,5),(1,92,189),(0,0,99),(1,107,122),(3,122,50),(1,121,5),(1,88,7),(3,7,31),(2,123,3),(3,122,38),(3,122,105),(3,187,0),(3,129,50),(3,2,23),(0,144,31),(2,50,4),(1,146,4),(0,50,5),(3,3,34),(3,204,0),(3,37,5),(3,204,5),(3,33,5),(1,211,4),(2,0,206),(1,206,4),(0,0,41),(3,28,0),(3,145,0),(1,43,189),(3,94,31),(1,80,43),(1,95,43),(1,43,209),(0,34,23),(0,2,188),(3,224,116),(0,29,31),(0,152,5),(1,3,227),(0,0,228),(1,28,7),(1,95,57),(1,113,2),(0,1,232),(3,179,6),(0,0,180),(1,179,2),(0,0,236),(3,202,0),(2,0,115),(0,37,23),(1,80,4),(2,80,2),(3,80,2),(2,188,5),(3,188,5),(3,244,0),(1,188,5),(0,0,247),(2,2,189),(1,2,189),(2,0,189),(1,100,5),(3,100,0),(2,2,188),(3,254,0),(0,0,116),(2,1,188),(3,257,0),(3,95,2),(1,95,2),(3,83,23),(3,83,0),(1,262,3),(1,88,113),(3,2,6),(1,83,3),(1,88,4),(3,3,267),(0,0,267),(3,139,0),(3,88,0),(1,271,4),(1,271,3),(3,179,31),(3,1,31),(3,8,188),(1,8,4),(0,0,277),(1,88,3),(0,0,279),(2,1,9),(2,0,8),(3,154,0),(3,102,23),(3,102,5),(1,3,285),(2,0,285),(1,102,5),(0,0,288),(3,102,0),(1,290,3),(3,152,5),(3,292,0),(2,152,5),(3,294,0),(3,245,0),(2,0,227),(3,179,152),(3,107,5),(1,299,4),(2,0,299),(0,0,148),(1,107,4),(0,0,303),(3,107,0),(1,305,5),(1,38,5),(0,0,307),(0,38,5),(2,0,309),(0,37,38),(0,0,114),(3,113,38),(1,39,4),(3,125,188),(1,125,102),(1,279,4),(3,125,152),(3,125,38),(3,3,126),(0,0,126),(1,125,3),(1,322,4),(3,125,0),(1,324,4),(1,57,2),(1,28,5),(1,33,5),(1,3,209),(3,129,152),(1,211,3),(1,37,2),(3,3,277),(2,26,83),(1,53,92),(0,26,2),(1,336,5),(0,188,31),(1,113,61),(3,88,188),(1,129,2),(1,43,5),(3,57,188),(3,53,26),(3,92,6),(1,172,4),(2,167,4),(2,0,57),(2,26,57),(3,57,38),(0,152,23),(1,26,5),(1,154,4),(1,216,5),(1,94,5),(2,92,3),(3,356,5),(0,129,38),(1,356,5),(3,43,23),(3,94,5),(1,167,4),(1,26,2),(2,363,4),(3,3,63),(3,3,328),(3,3,6),(2,332,5),(1,305,4),(1,144,4),(3,61,23),(3,102,26),(1,92,5),(0,0,342),(0,0,328),(3,3,54),(1,166,5),(3,3,377),(2,0,81),(3,53,38),(0,26,1),(1,381,5),(3,61,31),(3,3,342),(2,92,5),(3,385,0),(1,125,166),(3,8,6),(3,3,373),(3,61,38),(3,3,157),(3,3,62),(1,283,4),(3,38,5),(1,394,4),(1,28,2),(1,61,8),(3,61,188),(3,265,0),(1,155,4),(1,125,2),(1,113,166),(1,61,2),(2,403,5),(1,102,61),(2,144,5),(3,394,0),(3,61,152),(1,309,4),(1,89,3),(3,188,31),(2,396,5),(0,0,326),(2,144,4),(1,53,2),(2,415,5),(1,92,4),(3,3,417),(2,403,4),(2,401,4),(3,53,31),(2,341,4),(3,2,247),(1,324,3),(1,182,5),(0,26,31),(1,129,4),(3,166,188),(3,3,31),(3,92,5),(1,430,3),(3,119,0),(1,102,179),(3,336,5),(1,202,4),(3,3,124),(1,166,4),(2,167,5),(3,113,31),(0,26,152),(2,363,5),(3,122,188),(1,179,166),(1,88,61),(3,3,437),(2,2,155),(1,179,61),(1,50,4),(3,381,5),(3,3,131),(0,0,327),(1,53,166),(3,166,5),(1,453,4),(2,0,224),(2,26,5),(1,456,3),(1,121,3),(1,113,43),(1,457,4),(1,453,3),(1,53,8),(1,113,92),(2,129,53),(3,57,152),(3,53,5),(1,3,466),(3,89,0),(1,143,4),(2,155,4),(0,0,232),(1,80,2),(0,0,45),(0,1,247),(1,92,57),(3,92,188),(3,129,188),(1,125,92),(0,92,5),(1,479,4),(3,113,0),(1,481,3),(1,430,4),(1,290,5),(1,83,61),(2,67,5),(0,2,247),(0,1,9),(2,123,4),(2,326,4),(3,122,2),(1,102,57),(1,53,83),(1,150,3),(3,28,5),(1,495,4),(1,266,4),(2,0,211),(0,0,152),(1,102,122),(2,236,4),(3,122,31),(0,37,5),(1,503,3),(0,129,2),(3,385,1),(0,0,401),(3,129,2),(1,508,3),(3,3,427),(3,57,6),(2,129,4),(1,129,43),(1,166,57),(2,129,43),(2,26,43),(0,0,322),(1,137,3),(1,262,4),(1,129,53),(1,182,4),(0,129,152),(1,129,102),(2,129,102),(3,166,23),(0,129,188),(3,33,0),(2,396,4),(1,294,3),(3,113,26),(3,3,45),(3,137,0),(3,43,188),(1,179,43),(1,216,4),(3,122,152),(0,0,396),(2,0,495),(3,88,152),(1,129,8),(0,0,415),(1,499,3),(3,83,188),(0,67,5),(3,3,288),(2,0,466),(3,88,38),(1,88,53),(3,53,23),(1,179,92),(1,53,179),(0,0,58),(3,88,26),(1,356,4),(3,113,2),(3,113,1),(3,179,1),(3,83,1),(0,1,188),(2,92,4),(0,129,1),(3,92,1),(3,129,1),(0,1,152),(3,179,2)]
lemma W_44_ok : btAll (fun x => faithful p_44 q_44 x ∧ x.1 < 2^64) W_44 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_44 : List (List (Nat × Nat)) := [[]]
def A_44 : BT (List (Nat × Nat)) := btOfList 1 al_44
set_option maxHeartbeats 0 in
lemma A_44_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_44 = g_44) A_44 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_44_0 : Slice r_44 g_44 (subcubeFast 0 1) 9 := by
  have hc : Lower (varsOf 62) 0xfffffffcffc0c000 9 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_1 : Slice r_44 g_44 (subcubeFast 0 2) 9 := by
  have hc : Lower (varsOf 61) 0xfffffffafaa0f000 9 := carry_of (swaps := [(1,5),(4,5)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_2 : Slice r_44 g_44 (subcubeFast 8 0) 9 := by
  have hc : Lower (varsOf 55) 0xffffe8e880800000 9 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_3 : Slice r_44 g_44 (subcubeFast 16 0) 9 := by
  have hc : Lower (varsOf 47) 0xeee8eee8c000c000 9 := carry_of (swaps := [(1,3),(2,3),(4,5)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_4 : Slice r_44 g_44 (fiDom 0 0 4 5 true) 9 := by
  have hc : Lower (varsOf 31) 0xfa80eee8fa80eee8 9 := carry_of (swaps := [(0,4),(2,4)]) (by decide +kernel) low_23
  exact slice_fi (z := 0) (o := 0) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_5 : Slice r_44 g_44 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) 0xffffee88aa000000 8 := carry_of (swaps := [(0,1),(2,5),(3,5),(4,5)]) (by decide +kernel) low_24
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_6 : Slice r_44 g_44 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) 0xffffaaa0fa000000 8 := carry_of (swaps := [(0,1),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_25
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_7 : Slice r_44 g_44 (identDom 1 2) 9 := by
  have hc : Lower (varsOf 59) 0xffffeeccee88cc00 9 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_26
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_8 : Slice r_44 g_44 (identDom 0 4) 8 := by
  have hc : Lower (varsOf 47) 0xeeeaeeeaea80ea80 8 := carry_of (swaps := [(0,4),(1,3),(2,4),(4,5)]) (by decide +kernel) low_27
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_9 : Slice r_44 g_44 (fiDom 0 0 2 5 true) 8 := by
  exact slice_fi (z := 0) (o := 0) (u := 2) (v := 5) (fl := true) (by decide +kernel) low_28
set_option maxHeartbeats 0 in
lemma sl_44_10 : Slice r_44 g_44 (subcubeFast 32 0) 7 := by
  have hc : Lower (varsOf 31) 0xfa80c000fa80c000 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_29
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_11 : Slice r_44 g_44 (identDom 0 2) 8 := by
  have hc : Lower (varsOf 59) 0xffffeeaaaa888800 8 := carry_of (swaps := [(0,3),(1,3),(2,5),(4,5)]) (by decide +kernel) low_30
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_12 : Slice r_44 g_44 (fiDom 0 2 0 4 false) 7 := by
  have hc : Lower (varsOf 45) 0xfffafffafaa0faa0 7 := carry_of (swaps := [(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fi (z := 0) (o := 2) (u := 0) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_13 : Slice r_44 g_44 (fiDom 32 0 0 1 false) 7 := by
  have hc : Lower (varsOf 29) 0xfaa0a000faa0a000 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_31
  exact slice_fi (z := 32) (o := 0) (u := 0) (v := 1) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_14 : Slice r_44 g_44 (fiDom 0 1 1 2 false) 7 := by
  have hc : Lower (varsOf 58) 0xffffffccffcccc00 7 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fi (z := 0) (o := 1) (u := 1) (v := 2) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_15 : Slice r_44 g_44 (subcubeFast 8 4) 6 := by
  have hc : Lower (varsOf 51) 0xffffeeee88880000 6 := carry_of (swaps := [(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_16 : Slice r_44 g_44 (subcubeFast 8 2) 6 := by
  have hc : Lower (varsOf 53) 0xfffffafaa0a00000 6 := carry_of (swaps := [(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_17 : Slice r_44 g_44 (subcubeFast 4 2) 6 := by
  have hc : Lower (varsOf 57) 0xffffffaaaa000000 6 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_18 : Slice r_44 g_44 (subcubeFast 16 1) 6 := by
  have hc : Lower (varsOf 46) 0xfffcfffcc000c000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_19 : Slice r_44 g_44 (subcubeFast 8 1) 6 := by
  have hc : Lower (varsOf 54) 0xfffffcfcc0c00000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_20 : Slice r_44 g_44 (fiDom 0 0 3 5 true) 8 := by
  have hc : Lower (varsOf 31) 0xfaffc0e8faffc0e8 8 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_37
  exact slice_fi (z := 0) (o := 0) (u := 3) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_21 : Slice r_44 g_44 (fiDom 0 2 0 5 true) 7 := by
  have hc : Lower (varsOf 29) 0xfff5f550fff5f550 7 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_15
  exact slice_fi (z := 0) (o := 2) (u := 0) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_22 : Slice r_44 g_44 (fiDom 0 1 2 5 true) 7 := by
  have hc : Lower (varsOf 30) 0xffcfcf0cffcfcf0c 7 := carry_of (swaps := [(0,4),(1,4),(2,3),(3,4)]) (by decide +kernel) low_15
  exact slice_fi (z := 0) (o := 1) (u := 2) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_23 : Slice r_44 g_44 (fiDom 0 2 4 5 true) 7 := by
  have hc : Lower (varsOf 29) 0xfaa0fffafaa0fffa 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_15
  exact slice_fi (z := 0) (o := 2) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_24 : Slice r_44 g_44 (fiDom 8 0 4 5 true) 7 := by
  have hc : Lower (varsOf 23) 0x8080e8e88080e8e8 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_17
  exact slice_fi (z := 8) (o := 0) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_25 : Slice r_44 g_44 (fiDom 0 1 1 5 true) 7 := by
  have hc : Lower (varsOf 30) 0xfff3f330fff3f330 7 := carry_of (swaps := [(0,4),(1,3),(2,4)]) (by decide +kernel) low_15
  exact slice_fi (z := 0) (o := 1) (u := 1) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_26 : Slice r_44 g_44 (subcubeFast 6 1) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_27 : Slice r_44 g_44 (subcubeFast 17 2) 4 := by
  have hc : Lower (varsOf 44) 0xfff0fff0f000f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_28 : Slice r_44 g_44 (subcubeFast 32 3) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_29 : Slice r_44 g_44 (subcubeFast 32 5) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_30 : Slice r_44 g_44 (subcubeFast 6 8) 4 := by
  have hc : Lower (varsOf 49) 0xffffaaaaaaaa0000 4 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_31 : Slice r_44 g_44 (subcubeFast 32 18) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 18) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_32 : Slice r_44 g_44 (subcubeFast 20 32) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 20) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_33 : Slice r_44 g_44 (subcubeFast 24 32) 4 := by
  exact slice_fast_direct_f (z := 24) (o := 32) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_44_34 : Slice r_44 g_44 (fiDom 0 8 2 4 true) 6 := by
  have hc : Lower (varsOf 39) 0xefefefefcacacaca 6 := carry_of (swaps := [(0,1),(2,3),(3,4),(4,5)]) (by decide +kernel) low_19
  exact slice_fi (z := 0) (o := 8) (u := 2) (v := 4) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_35 : Slice r_44 g_44 (fiDom 0 4 1 5 true) 6 := by
  have hc : Lower (varsOf 27) 0xffbbee22ffbbee22 6 := carry_of (swaps := [(0,1),(1,3),(2,4)]) (by decide +kernel) low_19
  exact slice_fi (z := 0) (o := 4) (u := 1) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_36 : Slice r_44 g_44 (fiDom 16 0 1 5 true) 6 := by
  have hc : Lower (varsOf 15) 0xe220e220e220e220 6 := carry_of (swaps := [(0,2),(1,3)]) (by decide +kernel) low_20
  exact slice_fi (z := 16) (o := 0) (u := 1) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_37 : Slice r_44 g_44 (fiDom 1 0 4 5 true) 6 := by
  have hc : Lower (varsOf 30) 0xf000ccc0f000ccc0 6 := carry_of (swaps := [(0,4),(1,2),(2,4),(3,4)]) (by decide +kernel) low_20
  exact slice_fi (z := 1) (o := 0) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_38 : Slice r_44 g_44 (fiDom 0 4 4 5 true) 6 := by
  have hc : Lower (varsOf 27) 0xff88eeeeff88eeee 6 := carry_of (swaps := [(0,1),(1,2),(2,4),(3,4)]) (by decide +kernel) low_19
  exact slice_fi (z := 0) (o := 4) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_39 : Slice r_44 g_44 (fiDom 2 0 3 4 false) 6 := by
  have hc : Lower (varsOf 45) 0xffa0ffa0fa00fa00 6 := carry_of (swaps := [(1,4),(2,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fi (z := 2) (o := 0) (u := 3) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_40 : Slice r_44 g_44 (fiDom 0 4 3 5 false) 6 := by
  have hc : Lower (varsOf 27) 0xff88ee00ff88ee00 6 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_2
  exact slice_fi (z := 0) (o := 4) (u := 3) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_41 : Slice r_44 g_44 (fiDom 16 0 0 5 false) 6 := by
  have hc : Lower (varsOf 15) 0xeaa8eaa8eaa8eaa8 6 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_2
  exact slice_fi (z := 16) (o := 0) (u := 0) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_42 : Slice r_44 g_44 (fiDom 4 0 1 5 false) 6 := by
  have hc : Lower (varsOf 27) 0xeecccc88eecccc88 6 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_2
  exact slice_fi (z := 4) (o := 0) (u := 1) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_43 : Slice r_44 g_44 (fiDom 2 0 0 5 false) 6 := by
  have hc : Lower (varsOf 29) 0xfaaaaaa0faaaaaa0 6 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_fi (z := 2) (o := 0) (u := 0) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_44 : Slice r_44 g_44 (fiDom 1 0 1 5 false) 6 := by
  have hc : Lower (varsOf 30) 0xfcccccc0fcccccc0 6 := carry_of (swaps := [(0,4),(1,3),(2,4)]) (by decide +kernel) low_2
  exact slice_fi (z := 1) (o := 0) (u := 1) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_45 : Slice r_44 g_44 (fiDom 2 0 3 5 true) 6 := by
  have hc : Lower (varsOf 29) 0xfaff00a0faff00a0 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_34
  exact slice_fi (z := 2) (o := 0) (u := 3) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_46 : Slice r_44 g_44 (fiDom 2 0 0 4 true) 6 := by
  have hc : Lower (varsOf 45) 0xfff5fff550005000 6 := carry_of (swaps := [(0,2),(1,4),(3,4),(4,5)]) (by decide +kernel) low_34
  exact slice_fi (z := 2) (o := 0) (u := 0) (v := 4) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_47 : Slice r_44 g_44 (fiDom 16 0 1 2 false) 5 := by
  have hc : Lower (varsOf 43) 0xeecceecccc00cc00 5 := carry_of (swaps := [(1,3),(2,4),(4,5)]) (by decide +kernel) low_9
  exact slice_fi (z := 16) (o := 0) (u := 1) (v := 2) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_48 : Slice r_44 g_44 (fiDom 16 0 0 3 false) 5 := by
  have hc : Lower (varsOf 39) 0xeaeaeaea80808080 5 := carry_of (swaps := [(0,2),(1,2),(3,4),(4,5)]) (by decide +kernel) low_4
  exact slice_fi (z := 16) (o := 0) (u := 0) (v := 3) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_49 : Slice r_44 g_44 (fiDom 0 8 2 5 false) 5 := by
  have hc : Lower (varsOf 23) 0xfafae0e0fafae0e0 5 := carry_of (swaps := [(0,1),(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_fi (z := 0) (o := 8) (u := 2) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_50 : Slice r_44 g_44 (fiDom 0 8 0 2 false) 5 := by
  have hc : Lower (varsOf 51) 0xffffeeeeaaaa8888 5 := carry_of (swaps := [(0,2),(1,2),(2,4),(3,5)]) (by decide +kernel) low_21
  exact slice_fi (z := 0) (o := 8) (u := 0) (v := 2) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_51 : Slice r_44 g_44 (fiDom 8 0 2 5 true) 5 := by
  have hc : Lower (varsOf 23) 0x8f8f08088f8f0808 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_38
  exact slice_fi (z := 8) (o := 0) (u := 2) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_52 : Slice r_44 g_44 (fiDom 8 0 2 4 false) 5 := by
  have hc : Lower (varsOf 39) 0xf8f8f8f880808080 5 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_4
  exact slice_fi (z := 8) (o := 0) (u := 2) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_53 : Slice r_44 g_44 (fiDom 8 0 1 5 true) 5 := by
  have hc : Lower (varsOf 23) 0xb3b32020b3b32020 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_38
  exact slice_fi (z := 8) (o := 0) (u := 1) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_54 : Slice r_44 g_44 (fiDom 16 0 1 3 false) 5 := by
  have hc : Lower (varsOf 39) 0xececececc0c0c0c0 5 := carry_of (swaps := [(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_9
  exact slice_fi (z := 16) (o := 0) (u := 1) (v := 3) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_55 : Slice r_44 g_44 (fiDom 32 0 0 3 true) 5 := by
  have hc : Lower (varsOf 23) 0xd0d04040d0d04040 5 := carry_of (swaps := [(0,2),(1,2),(2,3),(3,4)]) (by decide +kernel) low_39
  exact slice_fi (z := 32) (o := 0) (u := 0) (v := 3) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_56 : Slice r_44 g_44 (fiDom 16 0 3 5 true) 5 := by
  have hc : Lower (varsOf 15) 0xc0e8c0e8c0e8c0e8 5 := carry_of (swaps := [(1,2),(2,3)]) (by decide +kernel) low_40
  exact slice_fi (z := 16) (o := 0) (u := 3) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_57 : Slice r_44 g_44 (fiDom 2 0 0 2 true) 5 := by
  have hc : Lower (varsOf 57) 0xffffaa00ff000000 5 := carry_of (swaps := [(1,4),(2,5),(3,4)]) (by decide +kernel) low_9
  exact slice_fi (z := 2) (o := 0) (u := 0) (v := 2) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_58 : Slice r_44 g_44 (fiDom 0 1 3 5 true) 5 := by
  have hc : Lower (varsOf 30) 0xffffc0fcffffc0fc 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_22
  exact slice_fi (z := 0) (o := 1) (u := 3) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_59 : Slice r_44 g_44 (fiDom 4 0 0 5 true) 5 := by
  have hc : Lower (varsOf 27) 0xff554400ff554400 5 := carry_of (swaps := [(0,2),(1,2),(2,4),(3,4)]) (by decide +kernel) low_35
  exact slice_fi (z := 4) (o := 0) (u := 0) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_60 : Slice r_44 g_44 (fiDom 4 0 0 4 false) 5 := by
  have hc : Lower (varsOf 43) 0xeeaaeeaaaa00aa00 5 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_9
  exact slice_fi (z := 4) (o := 0) (u := 0) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_61 : Slice r_44 g_44 (fiDom 0 2 2 5 true) 5 := by
  have hc : Lower (varsOf 29) 0xffafff0affafff0a 5 := carry_of (swaps := [(1,4)]) (by decide +kernel) low_22
  exact slice_fi (z := 0) (o := 2) (u := 2) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_62 : Slice r_44 g_44 (fiDom 0 1 4 5 true) 5 := by
  have hc : Lower (varsOf 30) 0xffc0fffcffc0fffc 5 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_22
  exact slice_fi (z := 0) (o := 1) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_63 : Slice r_44 g_44 (fiDom 2 0 2 5 true) 5 := by
  have hc : Lower (varsOf 29) 0xff0f0a00ff0f0a00 5 := carry_of (swaps := [(1,4),(3,4)]) (by decide +kernel) low_35
  exact slice_fi (z := 2) (o := 0) (u := 2) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_64 : Slice r_44 g_44 (fiDom 2 0 2 5 false) 5 := by
  have hc : Lower (varsOf 29) 0xfaf0a0a0faf0a0a0 5 := carry_of (swaps := [(0,1),(1,4),(2,3),(3,4)]) (by decide +kernel) low_9
  exact slice_fi (z := 2) (o := 0) (u := 2) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_65 : Slice r_44 g_44 (fiDom 2 0 2 3 true) 5 := by
  have hc : Lower (varsOf 53) 0xffffaaaa0a0a0000 5 := carry_of (swaps := [(0,1),(1,4),(2,4),(3,5)]) (by decide +kernel) low_41
  exact slice_fi (z := 2) (o := 0) (u := 2) (v := 3) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_66 : Slice r_44 g_44 (fiDom 2 0 2 3 false) 5 := by
  have hc : Lower (varsOf 53) 0xffffa0a0f0f00000 5 := carry_of (swaps := [(1,4),(2,4),(3,5),(4,5)]) (by decide +kernel) low_9
  exact slice_fi (z := 2) (o := 0) (u := 2) (v := 3) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_67 : Slice r_44 g_44 (fiDom 2 0 0 2 false) 5 := by
  have hc : Lower (varsOf 57) 0xffffaaaaaa000000 5 := carry_of (swaps := [(0,1),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_9
  exact slice_fi (z := 2) (o := 0) (u := 0) (v := 2) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_68 : Slice r_44 g_44 (fiDom 8 0 0 4 false) 5 := by
  have hc : Lower (varsOf 39) 0xeaeaeaea80808080 5 := carry_of (swaps := [(0,2),(1,2),(3,4),(4,5)]) (by decide +kernel) low_4
  exact slice_fi (z := 8) (o := 0) (u := 0) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_69 : Slice r_44 g_44 (fiDom 8 0 0 5 true) 5 := by
  have hc : Lower (varsOf 23) 0xd5d54040d5d54040 5 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_38
  exact slice_fi (z := 8) (o := 0) (u := 0) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_70 : Slice r_44 g_44 (fiDom 0 4 0 4 false) 5 := by
  have hc : Lower (varsOf 43) 0xeeeeeeeeee88ee88 5 := carry_of (swaps := [(0,2),(1,3),(2,4),(3,4),(4,5)]) (by decide +kernel) low_21
  exact slice_fi (z := 0) (o := 4) (u := 0) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_71 : Slice r_44 g_44 (fiDom 4 0 3 5 true) 5 := by
  have hc : Lower (varsOf 27) 0xaaff0088aaff0088 5 := carry_of (swaps := [(0,1),(2,4),(3,4)]) (by decide +kernel) low_35
  exact slice_fi (z := 4) (o := 0) (u := 3) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_72 : Slice r_44 g_44 (fiDom 1 0 1 2 true) 5 := by
  have hc : Lower (varsOf 58) 0xffffcc0033000000 5 := carry_of (swaps := [(0,4),(2,5),(3,4)]) (by decide +kernel) low_42
  exact slice_fi (z := 1) (o := 0) (u := 1) (v := 2) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_73 : Slice r_44 g_44 (fiDom 2 0 0 3 true) 5 := by
  have hc : Lower (varsOf 53) 0xffffa0a050500000 5 := carry_of (swaps := [(0,1),(1,4),(2,4),(3,5),(4,5)]) (by decide +kernel) low_42
  exact slice_fi (z := 2) (o := 0) (u := 0) (v := 3) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_74 : Slice r_44 g_44 (fiDom 0 4 3 4 true) 5 := by
  have hc : Lower (varsOf 43) 0xeeffeeffcc88cc88 5 := carry_of (swaps := [(1,2),(2,4),(3,4),(4,5)]) (by decide +kernel) low_43
  exact slice_fi (z := 0) (o := 4) (u := 3) (v := 4) (fl := true) (by decide +kernel) hc
def S_44 : BT (Option (Nat × Nat)) := btOfList 7 [some (subcubeFast 0 1,9),some (subcubeFast 0 2,9),some (subcubeFast 8 0,9),some (subcubeFast 16 0,9),some (fiDom 0 0 4 5 true,9),some (subcubeFast 4 0,8),some (subcubeFast 2 0,8),some (identDom 1 2,9),some (identDom 0 4,8),some (fiDom 0 0 2 5 true,8),some (subcubeFast 32 0,7),some (identDom 0 2,8),some (fiDom 0 2 0 4 false,7),some (fiDom 32 0 0 1 false,7),some (fiDom 0 1 1 2 false,7),some (subcubeFast 8 4,6),some (subcubeFast 8 2,6),some (subcubeFast 4 2,6),some (subcubeFast 16 1,6),some (subcubeFast 8 1,6),some (fiDom 0 0 3 5 true,8),some (fiDom 0 2 0 5 true,7),some (fiDom 0 1 2 5 true,7),some (fiDom 0 2 4 5 true,7),some (fiDom 8 0 4 5 true,7),some (fiDom 0 1 1 5 true,7),some (subcubeFast 6 1,4),some (subcubeFast 17 2,4),some (subcubeFast 32 3,4),some (subcubeFast 32 5,4),some (subcubeFast 6 8,4),some (subcubeFast 32 18,4),some (subcubeFast 20 32,4),some (subcubeFast 24 32,4),some (fiDom 0 8 2 4 true,6),some (fiDom 0 4 1 5 true,6),some (fiDom 16 0 1 5 true,6),some (fiDom 1 0 4 5 true,6),some (fiDom 0 4 4 5 true,6),some (fiDom 2 0 3 4 false,6),some (fiDom 0 4 3 5 false,6),some (fiDom 16 0 0 5 false,6),some (fiDom 4 0 1 5 false,6),some (fiDom 2 0 0 5 false,6),some (fiDom 1 0 1 5 false,6),some (fiDom 2 0 3 5 true,6),some (fiDom 2 0 0 4 true,6),some (fiDom 16 0 1 2 false,5),some (fiDom 16 0 0 3 false,5),some (fiDom 0 8 2 5 false,5),some (fiDom 0 8 0 2 false,5),some (fiDom 8 0 2 5 true,5),some (fiDom 8 0 2 4 false,5),some (fiDom 8 0 1 5 true,5),some (fiDom 16 0 1 3 false,5),some (fiDom 32 0 0 3 true,5),some (fiDom 16 0 3 5 true,5),some (fiDom 2 0 0 2 true,5),some (fiDom 0 1 3 5 true,5),some (fiDom 4 0 0 5 true,5),some (fiDom 4 0 0 4 false,5),some (fiDom 0 2 2 5 true,5),some (fiDom 0 1 4 5 true,5),some (fiDom 2 0 2 5 true,5),some (fiDom 2 0 2 5 false,5),some (fiDom 2 0 2 3 true,5),some (fiDom 2 0 2 3 false,5),some (fiDom 2 0 0 2 false,5),some (fiDom 8 0 0 4 false,5),some (fiDom 8 0 0 5 true,5),some (fiDom 0 4 0 4 false,5),some (fiDom 4 0 3 5 true,5),some (fiDom 1 0 1 2 true,5),some (fiDom 2 0 0 3 true,5),some (fiDom 0 4 3 4 true,5)]
lemma S_44_ok : btAll (fun o => ∀ p, o = some p → Slice r_44 g_44 p.1 p.2) S_44 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_44_0) (forall_cons (fun _ h => by cases h; exact sl_44_1) (forall_cons (fun _ h => by cases h; exact sl_44_2) (forall_cons (fun _ h => by cases h; exact sl_44_3) (forall_cons (fun _ h => by cases h; exact sl_44_4) (forall_cons (fun _ h => by cases h; exact sl_44_5) (forall_cons (fun _ h => by cases h; exact sl_44_6) (forall_cons (fun _ h => by cases h; exact sl_44_7) (forall_cons (fun _ h => by cases h; exact sl_44_8) (forall_cons (fun _ h => by cases h; exact sl_44_9) (forall_cons (fun _ h => by cases h; exact sl_44_10) (forall_cons (fun _ h => by cases h; exact sl_44_11) (forall_cons (fun _ h => by cases h; exact sl_44_12) (forall_cons (fun _ h => by cases h; exact sl_44_13) (forall_cons (fun _ h => by cases h; exact sl_44_14) (forall_cons (fun _ h => by cases h; exact sl_44_15) (forall_cons (fun _ h => by cases h; exact sl_44_16) (forall_cons (fun _ h => by cases h; exact sl_44_17) (forall_cons (fun _ h => by cases h; exact sl_44_18) (forall_cons (fun _ h => by cases h; exact sl_44_19) (forall_cons (fun _ h => by cases h; exact sl_44_20) (forall_cons (fun _ h => by cases h; exact sl_44_21) (forall_cons (fun _ h => by cases h; exact sl_44_22) (forall_cons (fun _ h => by cases h; exact sl_44_23) (forall_cons (fun _ h => by cases h; exact sl_44_24) (forall_cons (fun _ h => by cases h; exact sl_44_25) (forall_cons (fun _ h => by cases h; exact sl_44_26) (forall_cons (fun _ h => by cases h; exact sl_44_27) (forall_cons (fun _ h => by cases h; exact sl_44_28) (forall_cons (fun _ h => by cases h; exact sl_44_29) (forall_cons (fun _ h => by cases h; exact sl_44_30) (forall_cons (fun _ h => by cases h; exact sl_44_31) (forall_cons (fun _ h => by cases h; exact sl_44_32) (forall_cons (fun _ h => by cases h; exact sl_44_33) (forall_cons (fun _ h => by cases h; exact sl_44_34) (forall_cons (fun _ h => by cases h; exact sl_44_35) (forall_cons (fun _ h => by cases h; exact sl_44_36) (forall_cons (fun _ h => by cases h; exact sl_44_37) (forall_cons (fun _ h => by cases h; exact sl_44_38) (forall_cons (fun _ h => by cases h; exact sl_44_39) (forall_cons (fun _ h => by cases h; exact sl_44_40) (forall_cons (fun _ h => by cases h; exact sl_44_41) (forall_cons (fun _ h => by cases h; exact sl_44_42) (forall_cons (fun _ h => by cases h; exact sl_44_43) (forall_cons (fun _ h => by cases h; exact sl_44_44) (forall_cons (fun _ h => by cases h; exact sl_44_45) (forall_cons (fun _ h => by cases h; exact sl_44_46) (forall_cons (fun _ h => by cases h; exact sl_44_47) (forall_cons (fun _ h => by cases h; exact sl_44_48) (forall_cons (fun _ h => by cases h; exact sl_44_49) (forall_cons (fun _ h => by cases h; exact sl_44_50) (forall_cons (fun _ h => by cases h; exact sl_44_51) (forall_cons (fun _ h => by cases h; exact sl_44_52) (forall_cons (fun _ h => by cases h; exact sl_44_53) (forall_cons (fun _ h => by cases h; exact sl_44_54) (forall_cons (fun _ h => by cases h; exact sl_44_55) (forall_cons (fun _ h => by cases h; exact sl_44_56) (forall_cons (fun _ h => by cases h; exact sl_44_57) (forall_cons (fun _ h => by cases h; exact sl_44_58) (forall_cons (fun _ h => by cases h; exact sl_44_59) (forall_cons (fun _ h => by cases h; exact sl_44_60) (forall_cons (fun _ h => by cases h; exact sl_44_61) (forall_cons (fun _ h => by cases h; exact sl_44_62) (forall_cons (fun _ h => by cases h; exact sl_44_63) (forall_cons (fun _ h => by cases h; exact sl_44_64) (forall_cons (fun _ h => by cases h; exact sl_44_65) (forall_cons (fun _ h => by cases h; exact sl_44_66) (forall_cons (fun _ h => by cases h; exact sl_44_67) (forall_cons (fun _ h => by cases h; exact sl_44_68) (forall_cons (fun _ h => by cases h; exact sl_44_69) (forall_cons (fun _ h => by cases h; exact sl_44_70) (forall_cons (fun _ h => by cases h; exact sl_44_71) (forall_cons (fun _ h => by cases h; exact sl_44_72) (forall_cons (fun _ h => by cases h; exact sl_44_73) (forall_cons (fun _ h => by cases h; exact sl_44_74) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_44 : BT (Option PoolSpec) := btOfList 9 [q 15 [20497,24576],q 63 [20497,24576],q 51 [20497,24576],q 27 [],q 32 [],q 12 [],q 31 [],q 43 [],q 62 [],q 33 [],q 18 [],q 26 [],q 29 [],q 38 [16557],q 19 [],q 24 [],q 22 [20497,36894],q 65 [20497],q 21 [],q 70 [],q 22 [],q 30 [],q 22 [20497],q 22 [20497,24875],q 51 [],q 22 [20497,36893],q 24 [172040],q 38 [],q 24 [4124],q 23 [],q 28 [],q 15 [],q 0 [20491,16717,344079],q 22 [16717],q 49 [],q 6 [20489,126995],q 61 [],q 22 [16745],q 55 [],q 0 [],q 5 [],q 12 [12298],q 12 [12297],q 24 [4127],q 24 [29101],q 6 [],q 16 [],q 3 [12297,155652],q 46 [],q 12 [12461],q 18 [20486],q 37 [],q 22 [37015],q 10 [],q 2 [],q 19 [20497],q 12 [12317],q 13 [],q 17 [],q 24 [8196,16557],q 16 [16629],q 16 [215],q 45 [],q 73 [],q 72 [],q 1 [],q 24 [155679],q 8 [],q 24 [8196],q 0 [8196,16557,20497],q 6 [20497],q 52 [],q 39 [],q 24 [4096],q 60 [],q 66 [20497],q 19 [20488],q 67 [],q 16 [20497,24576],q 50 [],q 2 [155648,16538,451],q 24 [8194],q 21 [12461],q 3 [20480,8681,12782],q 21 [12297],q 25 [],q 53 [],q 15 [4096],q 3 [],q 18 [12297],q 19 [8196],q 20 [],q 0 [8196,12461,16586],q 1 [12461,20680,17209],q 12 [12421],q 0 [8196,12461,20682],q 6 [20480,16873],q 3 [24576,8221,12346],q 17 [20497,24576],q 68 [],q 3 [8645,950276],q 3 [24576,8221],q 58 [],q 0 [20493,94216],q 18 [20493],q 2 [21234,979],q 4 [],q 11 [],q 34 [],q 15 [344064],q 9 [16717],q 44 [],q 22 [20493],q 6 [20489],q 3 [20489,126980],q 14 [],q 5 [126980],q 0 [20497],q 5 [16422],q 3 [20488,12321],q 63 [],q 3 [20488,12321,36864],q 40 [411],q 3 [411,13449],q 0 [20493,20497],q 23 [12297],q 3 [12297,24728],q 3 [12297],q 0 [12297,16538],q 2 [16538,451],q 3 [12297,451],q 3 [20493,94212],q 71 [],q 5 [16538],q 35 [],q 1 [12297,20632],q 1 [12297,16538],q 3 [12297,155648],q 2 [155648,16538],q 1 [12297,155648],q 2 [94208,16705],q 1 [12297,20634],q 2 [16386,155648],q 16 [20489],q 18 [12294],q 16 [16386],q 17 [20493],q 18 [8198],q 17 [16386],q 3 [24576],q 5 [16386],q 3 [8198,20615,13133],q 15 [16386],q 6 [20499],q 3 [8196,12461],q 15 [16390],q 3 [12290,21088],q 3 [12297,155652,163842],q 1 [12297,163842],q 3 [12290,20488,12321],q 5 [20480],q 69 [],q 2 [20488],q 19 [20484],q 36 [],q 2 [16390,215],q 6 [16386],q 43 [16386],q 3 [8198],q 3 [8194,24947],q 15 [17229],q 0 [12298,20497],q 6 [20491,16717],q 6 [16386,20631],q 38 [12290],q 3 [20480],q 2 [20480,156139],q 3 [20480,12297,156139],q 19 [20499],q 22 [16390],q 47 [],q 14 [139279],q 2 [16386,94227],q 2 [94212,331778],q 2 [4096,16629],q 3 [4096,12298],q 1 [12297,20489],q 17 [20497],q 0 [20493,94579],q 40 [176130],q 24 [8198],q 16 [20497],q 16 [8194],q 50 [20497],q 0 [16629,12297],q 3 [4096,12297],q 2 [20632,17621],q 0 [8196,16557],q 6 [16393,21090],q 15 [115],q 24 [4096,16629],q 3 [12294],q 19 [20491],q 1 [12297,16545],q 65 [],q 15 [16545],q 38 [16545],q 3 [20480,12777],q 0 [8196,12461],q 6 [20480],q 24 [8192],q 56 [],q 59 [],q 2 [20480,8196,176617],q 15 [139264],q 3 [8194,12657],q 3 [20480,8198,12421],q 18 [770539],q 2 [20480,16873],q 15 [16390,215],q 15 [20480],q 0 [12294,20593],q 3 [215,12773],q 16 [8192],q 57 [20497],q 2 [16386,155796],q 3 [24576,12317],q 2 [4096,20727,16985],q 22 [16394],q 2 [4096],q 1 [12461,204800],q 2 [8196,204800],q 24 [8223],q 15 [20484],q 18 [20489,126991],q 3 [12297,24576],q 0 [8196,20497],q 22 [16629],q 3 [20480,8681],q 17 [20480],q 21 [12782],q 5 [204800],q 3 [8198,12421],q 18 [12777],q 0 [20727,12889],q 3 [20480,12297],q 16 [20480],q 2 [20480,16390,499925],q 2 [20480,16390,215],q 3 [4096,24587],q 19 [94212],q 3 [20482,2051],q 19 [8198],q 17 [12290],q 15 [16497],q 17 [16397],q 5 [430080],q 41 [12697],q 1 [176130,13017],q 22 [16394,12697],q 5 [16586],q 6 [20682],q 3 [20488,12321,36866],q 2 [8196,20655,16933],q 3 [4096,8645],q 18 [21234],q 16 [20499],q 2 [16386,155799],q 5 [126976],q 0 [12294,20497],q 0 [20495,17101],q 1 [12461,20680],q 54 [],q 57 [],q 25 [16618],q 2 [20484,16613,258048],q 66 [],q 0 [8196,20497,24751],q 3 [12741],q 0 [20499,12741],q 2 [20499],q 3 [8647],q 1 [20499],q 3 [8645],q 3 [4551],q 40 [],q 1 [20495,8909],q 0 [20493,94227],q 3 [20493],q 2 [94227],q 1 [20493,94219],q 3 [20493,94219],q 0 [20495],q 2 [719],q 1 [20493],q 0 [20493,94212],q 2 [94212],q 1 [20493,94208],q 0 [20493],q 2 [94208],q 74 [],q 2 [21235],q 0 [16397,20493],q 1 [16397,770059],q 3 [770059],q 1 [16397],q 0 [16397],q 2 [770048],q 3 [770048],q 0 [20491],q 64 [],q 3 [20490],q 0 [20490],q 2 [20490],q 3 [20490,20491],q 3 [20490,355],q 2 [20490,355],q 3 [20489],q 1 [20489,126991],q 3 [20489,126991],q 1 [20495],q 1 [20489],q 3 [20489,126983],q 2 [20488,16417],q 2 [770052],q 3 [20495],q 2 [16394],q 0 [16394,20889],q 3 [21091],q 3 [21088],q 41 [],q 0 [16393],q 0 [20586],q 2 [20586],q 2 [20480],q 0 [16754],q 3 [8194],q 0 [12777],q 0 [12805],q 2 [20482],q 18 [20489],q 15 [20482],q 2 [20480,8683],q 2 [16386],q 2 [20484],q 0 [12297],q 2 [155648],q 5 [155648],q 18 [20490],q 18 [12298],q 0 [12298],q 9 [16397],q 15 [20497],q 48 [],q 3 [20482],q 2 [16386,20631],q 0 [20628],q 3 [20628],q 2 [16386,20628],q 3 [12290],q 2 [20632],q 3 [12297,20632],q 3 [20486,503],q 2 [20486,503],q 0 [20497,24591],q 3 [24591],q 0 [16394],q 3 [411],q 2 [16394,411],q 0 [8709],q 0 [12294],q 3 [4096,20489],q 1 [20482],q 1 [20489,20493],q 3 [8194,20851],q 1 [12297],q 0 [8196],q 1 [12290],q 3 [20484],q 3 [12290,20587],q 0 [16390,20693],q 6 [16393],q 42 [],q 3 [20486],q 2 [8192],q 3 [12294,20595],q 3 [4096,20493],q 0 [12953],q 3 [8192,12953],q 1 [12297,20493],q 3 [455],q 2 [16538],q 0 [8437],q 3 [4096,8437],q 0 [20486],q 0 [20848],q 2 [4096,20499],q 3 [4096],q 0 [17049],q 2 [8192,17049],q 3 [8192],q 0 [20491,12621],q 1 [20491,12621],q 0 [12658],q 0 [16390],q 3 [215],q 6 [20491],q 1 [20491],q 1 [8194],q 0 [20849],q 1 [8194,20849],q 1 [12290,20585],q 3 [4096,20490],q 1 [12290,8297],q 3 [12290,8297],q 3 [12294,8305],q 3 [8196],q 0 [16490],q 0 [12657],q 1 [8194,12657],q 3 [20480,8198],q 0 [16753],q 3 [20493,94208],q 2 [20484,16613],q 15 [20486],q 19 [20489],q 1 [12290,20489],q 2 [20634],q 3 [12290,20491],q 2 [8196,20499],q 0 [20499],q 3 [12290,20488],q 0 [16397,21234],q 2 [21234],q 3 [20480,12294],q 0 [16629],q 0 [20491,16717],q 2 [8192,20499],q 0 [20727],q 2 [4096,20727],q 3 [4096,20727],q 2 [8196,20655],q 1 [20482,12297],q 2 [20488,32770],q 0 [20584],q 2 [20584],q 2 [20486],q 2 [16394,20891],q 3 [20891],q 7 [],q 3 [8196,176130],q 1 [176130],q 2 [8196,176130],q 1 [12461],q 2 [8196],q 0 [12294,16497],q 2 [8196,16557],q 0 [8196,20653],q 1 [20653],q 3 [8198,20615],q 0 [16394,12697],q 3 [12697],q 2 [20480,16390],q 1 [12789],q 3 [12294,20491],q 0 [16390,12501],q 3 [12501],q 3 [20489,126976],q 0 [12533],q 1 [12533],q 3 [4096,12533],q 2 [16390],q 2 [20484,233474],q 3 [24587],q 3 [20484,8421],q 3 [20484,12517],q 3 [8405],q 2 [16390,20695],q 14 [16397],q 3 [12297,20635],q 3 [622592],q 0 [21147],q 2 [8192,21147],q 5 [20632],q 1 [12297,20633],q 0 [12298,20909],q 1 [8194,20493],q 0 [12298,16813],q 22 [12298],q 0 [16397,21232],q 13 [12298],q 3 [12298],q 15 [20499],q 0 [16393,622607],q 1 [16393,622607],q 3 [622607],q 3 [20488],q 1 [16393],q 3 [20491]]
def B_44_3 : BT (List (List Nat)) := BT.empty
lemma B_44_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 3 xs.toFinset) B_44_3 := .empty
def U_44_4 : List Nat := []
def P_44_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_4
def N_44_4 : List NodeSpec := [([12,1,2,4,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_4 : checkNodesBT W_44 g_44 F_44 P_44_4 A_44 B_44_3 4 N_44_4 = true := by decide +kernel
def B_44_4 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_4
set_option maxRecDepth 500000 in
lemma B_44_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 4 xs.toFinset) B_44_4 :=
  buildBucketsBT_sound (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_3_ok C_44_4
def U_44_5 : List Nat := [0,1,2]
def P_44_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_5
def N_44_5 : List NodeSpec := [([16,15,1,3,4,5],[0],[]),([15,1,3,20,4,5],[0],[]),([7,19,2,9,4,5],[1],[]),([10,1,2,11,4,5],[2],[0]),([21,7,2,9,4,5],[2],[]),([17,18,1,2,4,5],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_5 : checkNodesBT W_44 g_44 F_44 P_44_5 A_44 B_44_4 5 N_44_5 = true := by decide +kernel
def B_44_5 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_5
set_option maxRecDepth 500000 in
lemma B_44_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 5 xs.toFinset) B_44_5 :=
  buildBucketsBT_sound (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_4_ok C_44_5
def U_44_6 : List Nat := ([0]++r 2 24)
def P_44_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_6
def N_44_6 : List NodeSpec := [([18,7,1,2,9,4,5],[2],[0]),([15,1,3,4,5],[3,0,4],[0]),([28,47,7,1,2,4,5],[5],[]),([24,7,1,2,3,4,5],[5,6],[]),([46,7,1,2,3,4,5],[5,6],[]),([7,1,2,42,58,4,5],[3,7],[]),([7,1,2,25,38,4,5],[3,7,4],[]),([7,1,2,42,50,4,5],[3,7,4],[]),([7,1,2,25,4,5,23],[3,7,6],[]),([27,7,1,2,9,4,5],[8,9],[]),([37,39,1,2,3,41,5],[10,11],[]),([7,1,2,42,9,4,5],[3,4,12,9],[]),([71,22,1,2,3,4,5],[5,12],[]),([10,7,1,2,9,4,5],[6,12,4,2],[0]),([7,1,2,3,42,45,5],[3,7,4,13],[]),([26,7,1,2,9,4,5],[10,14,9],[]),([7,1,2,59,3,4,5],[15],[]),([48,7,1,2,3,4,5],[15],[]),([17,7,1,2,9,4,5],[16],[0]),([0,1,2,3,60,62,5],[3,17,12],[]),([71,61,1,2,3,4,5],[18,19],[]),([73,0,1,2,9,4,5],[20],[]),([72,7,1,2,9,4,5],[21,6,4,22],[]),([0,1,2,9,75,4,5],[23],[]),([74,7,1,2,9,4,5],[24,22],[]),([7,1,2,9,11,4,5],[6,4,12,25],[0]),e6 [36] [],e6 [32] [],([70,7,1,2,3,4,5],[],[]),e6 [69] [],([66,7,1,2,3,4,5],[],[]),e6 [65] [],([44,7,1,2,3,4,5],[],[]),e6 [56] [],([52,7,1,2,3,4,5],[],[]),([0,1,2,3,49,41,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_6 : checkNodesBT W_44 g_44 F_44 P_44_6 A_44 B_44_5 6 N_44_6 = true := by decide +kernel
def B_44_6 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_6
set_option maxRecDepth 500000 in
lemma B_44_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 6 xs.toFinset) B_44_6 :=
  buildBucketsBT_sound (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_5_ok C_44_6
def U_44_7_0 : List Nat := ([0]++r 3 10++[14,15]++r 19 4++[24]++r 26 14)
def P_44_7_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_7_0
def N_44_7_0 : List NodeSpec := [e6 [201,50] [3],e6 [135,84] [3],([109,108,1,3,4,5],[3,4],[0]),([7,1,2,3,78,4,5],[3,4],[]),([122,1,2,3,4,178],[3,4],[]),([7,1,2,3,167,4,5],[3,4],[]),e6 [149,50] [4],e6 [50,205] [3,6],e6 [192,124] [4,6],([107,0,1,123,3,4,124,5],[6,3,4],[]),([79,7,1,2,3,4,5,31],[7,3,6],[]),([79,7,1,2,3,4,5,23],[3,6,8],[]),([88,79,7,1,2,3,4,5],[3,8,6],[]),([76,7,1,2,3,42,4,5],[4,0,8],[]),([27,83,7,1,2,3,4,5],[3,4,6,9],[]),([27,7,1,8,2,3,4,5],[3,6,9],[0]),([26,83,7,1,2,3,4,5],[4,6,9],[]),([196,7,1,2,3,4,5],[4,7,5,9],[]),([7,90,2,3,4,5],[7,4,9],[]),([7,1,2,3,9,4,5],[9,3,8,6,4],[0]),([7,1,2,3,177,42,4,5],[9,10],[]),e6 [119,121] [3,11],e6 [182,180] [3,11],e6 [174,38] [6,3,11],([37,0,1,2,3,38,41,5],[6,11],[0]),([122,1,2,3,4,194],[11,3],[]),e6 [216,84] [11,3],e6 [112,120] [11,3,6],e6 [204,146] [11,3,6,4],e6 [119,62] [3,6,12,4],([80,1,2,167,4,5],[3,12],[]),e6 [132] [4,12],([112,0,1,2,114,5],[6,12],[]),([7,1,2,3,58,4,5],[9,3,8,7,12,4],[0]),([7,1,8,2,3,42,4,5],[9,8,4,12],[0]),e6 [80,93] [11,3,12],([129,37,1,2,3,156,4,5],[12],[]),([153,0,1,2,3,124,5],[12,6],[]),([7,57,1,2,3,42,4,5],[8,3,15,7],[0]),e6 [7,127] [8,15],([7,1,2,3,127,4,5],[8,15,7,5,4],[]),([121,122,1,2,3,38,4,5],[3,11,19,21],[]),([121,1,2,123,3,4,5],[3,19,11,21],[]),([80,1,2,144,4,5],[3,21],[]),([95,1,2,155,4,5],[3,21],[]),([39,1,2,155,4,5],[3,21],[]),e6 [96] [6,21],([139,0,1,2,105,5],[6,21],[]),([0,90,2,3,4,160,5],[9,6,21],[]),e6 [142] [9,21],([106,0,1,3,105,4,5,31],[21],[]),([80,0,1,115,38,4,5],[21,4],[]),([80,0,1,2,9,4,5],[21,4],[]),([202,182,0,1,3,4,5],[21,4],[]),e6 [220] [21,4],([204,113,0,1,2,3,50,5],[21,4],[]),([191,0,1,2,9,4,5],[21,6],[]),([95,0,1,2,9,4,5],[21,6],[]),([95,0,1,2,3,45,5],[21,6],[]),e6 [231] [21,6],e6 [221] [21,6,4],([0,1,3,4,117,5],[21,9],[]),([100,0,1,9,4,5],[21,9],[]),([7,1,2,9,4,5],[6,4,22],[0]),([88,83,7,1,3,4],[22,4,6,9],[]),e6 [98,9] [20,24],([107,7,1,14,3,4,5],[3,4,27,15],[]),([7,1,2,3,156,4,5],[3,8,7,27,6,4],[]),([13,1,14,3,4,5],[3,27,4],[0]),([7,1,2,3,110,4,5],[3,27,6,4],[]),([7,1,2,3,143,4,5],[3,27,6,4],[]),([83,7,1,2,3,42,4,5],[4,9,27],[]),([7,230,1,2,3,4,5],[7,8,3,4,27],[]),([7,43,1,2,3,42,4,5],[8,3,15,4,7,27],[0]),([7,1,77,2,3,42,4,5],[26,27,8],[]),([22,7,1,2,3,4,5,31],[27,4,3,6,7],[0]),([108,7,1,3,38,4,5],[27,15,4,3],[]),([7,1,2,3,25,4,5],[3,28,4,27,6],[0]),e6 [80,82] [29,3,10,21,14],([7,1,2,3,144,4,5],[3,4,27,30],[]),e6 [26,175] [3,14,30],e6 [26,212] [3,14,30],e6 [26,138] [3,14,30],e6 [186,105] [3,30],e6 [62,148] [3,30],e6 [213,50] [3,30],([88,61,7,1,2,3,4,5],[3,30,20],[]),([37,1,2,3,130,4,5],[10,30],[]),u6 [7,9] [21,3,14,9,30],([229,0,1,2,4,228,5],[21,4,6,30],[]),([74,0,1,2,9,4,5,6],[21,6,30,22],[0]),([88,83,7,0,1,3,4],[22,4,30,9],[]),([7,0,1,2,9,4,5],[24,21,4,30,22],[0]),([61,7,1,2,3,4,5,23],[30,4,6,3,14,7],[]),e6 [218] [30,21,6],e6 [173] [30,21,6],u6 [55,38] [3,31,11],e6 [215,38] [3,31,30,11],e6 [85,87] [3,31,30,21],([98,0,1,2,9,4,5],[6,31,4,20,24],[]),([0,90,3,4,104,5],[11,31,4],[]),([0,90,1,3,4,104,5],[11,31,6],[]),e6 [47,7] [15,31,21,12],e6 [7,50] [21,31,3,8],([108,7,0,1,3,38,4,5],[31,3],[]),([28,0,1,105,4,5,31],[31,6,11],[]),e6 [107,151] [31,11,12,21],e6 [86,84] [30,31,3,32],([88,83,87,0,1,3,4],[33,12,6,31,34],[]),([89,0,90,2,3,91,5],[4,21,35,36,37,31],[]),([72,0,1,2,9,4,101,5],[4,38],[]),([72,0,1,2,9,4,5,6],[6,4,38,22],[0]),e6 [223] [3,39,4,21],e6 [226] [3,39,6,21],e6 [181] [3,39,21,6],e6 [219] [3,39,21,6],e6 [176] [3,39,21,29],([146,122,1,2,3,50,4,5],[21,39,4],[]),([37,146,1,2,3,50,4,5],[21,39,4],[]),e6 [103] [39,21,31,15]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_7_0 : checkNodesBT W_44 g_44 F_44 P_44_7_0 A_44 B_44_6 7 N_44_7_0 = true := by decide +kernel
def U_44_7_1 : List Nat := ([0]++r 3 10++[14,15,17,18,19,21]++r 27 5++r 39 61)
def P_44_7_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_7_1
def N_44_7_1 : List NodeSpec := [([107,7,0,1,14,3,4,5],[3,40],[]),e6 [199] [15,39,40,6],([107,0,1,3,4,62,5,31],[31,40],[]),([107,22,7,1,2,3,4,5],[0,4,41,28],[]),([22,7,1,2,3,38,4,5],[4,3,12,42,7,28],[0]),([79,7,1,2,3,38,4,5],[3,42,8,43],[]),([107,79,7,1,2,3,4,5],[4,3,7,41,43],[]),([7,111,1,2,3,4,5],[4,8,44,7,5],[]),e6 [168] [3,39,45,4],e6 [40,118] [6,4,45,46,12],e6 [7,58] [21,46,3,14,30],e6 [81,133] [45,46],u6 [40,49] [45,46,10],e6 [28,184] [45,46,14,3],e6 [119,41] [47,6,4,12],u6 [39,41] [48,6,21,3,11],e6 [50,124] [3,10,49,6],([61,7,1,2,3,4,5,31],[4,30,12,3,7,51],[]),u6 [30,31] [31,3,11,51],([37,0,1,2,3,38,126,5],[50,51,11],[]),([0,1,2,128,9,4,5],[4,52,31,6],[]),e6 [50,210] [4,53],e6 [193,50] [31,40,53],e6 [113,183] [53,4,3],e6 [83,68] [53,4,11,3],e6 [158] [4,8,3,54,21],u6 [35,23] [21,54,3,12,51],e6 [134,23] [21,54,3,18,11,6],u6 [64,23] [21,54,4,3,30,29],([26,7,1,8,2,3,4,5],[3,55,9],[0]),([7,136,1,2,3,42,4,5],[3,56,7],[]),e6 [156,157] [31,58],e6 [7,156] [31,58,3,10],e6 [140,40] [57,3,45,58,12,42,6],([7,1,2,3,45,5],[7,4,3,59],[0]),([26,0,1,2,3,45,5,6],[21,59,3,30],[]),([0,1,3,38,4,62,5,31],[60,6],[]),([121,0,1,3,38,4,5,31],[11,61,30],[]),e6 [50,209] [3,10,4,31,21,62],e6 [145,146] [3,11,4,62],e6 [159,50] [62],([147,7,1,2,3,4,5],[4,7,5,63,9],[]),([22,7,1,2,3,4,5,23],[15,6,4,3,63,7],[0]),e6 [169,170] [3,11,64,54,12],([7,1,158,2,3,4,5],[4,8,3,64],[]),e6 [222] [4,65,54,21],([71,7,1,2,3,4,5],[7,5,4,8,66,12],[0]),u6 [71] [45,65,12,66,19],([7,51,1,2,3,4,5],[27,7,15,8,67,6],[0]),e6 [161,50] [67],e6 [26,162] [3,14,68],([7,1,2,3,50,4,5],[68,3,8,7,4],[0]),([7,0,1,2,3,45,5],[6,21,4,3,69],[]),e6 [163,38] [12,30,51,70,17],([0,1,2,3,38,62,5,6],[51,30,19,70,17,12],[0]),e6 [165,105] [11,71],([225,0,1,3,4,5],[71,21,9],[]),e6 [149] [3,39,72,4],e6 [171] [31,30,72,11],([61,7,1,2,3,38,4,5],[3,30,19,4,46,7,73],[0]),u6 [61,60] [30,4,12,3,73],e6 [107,163] [31,11,73],([107,61,7,1,2,3,4,5],[3,30,58,74,4,73],[]),([107,0,1,2,3,62,5,6],[74,75,12],[]),([26,0,1,2,9,4,5,6],[21,76,9,30],[0]),([7,195,1,2,3,4,5],[4,77,9,7,5],[]),([88,22,7,1,2,3,4,5],[12,4,77,3,6],[]),([28,108,7,1,2,3,4,5],[4,78,7,3],[]),([28,7,1,2,14,3,4,5],[7,78,3],[0]),e6 [187,92] [11,29,72,79],([112,39,140,1,2,3,4,5],[6,14,31,80],[]),e6 [188,190] [21,81,12,11],e6 [193] [3,39,54,6,82,62],e6 [197,124] [6,3,83],e6 [53,198] [45,3,84],e6 [200,58] [85,86],e6 [203] [30,21,87,88,6],([37,39,40,1,2,3,4,5],[89,3,21,12,11],[0]),e6 [146,206] [53,11,3,4,90,21],e6 [129,207] [91,30,15,6],e6 [208,50] [11,4,3,92],e6 [50,214] [93,4,6],e6 [156,124] [94,6,10,31,58],e6 [217,50] [11,62,3,95],([0,90,2,3,4,124,5],[4,6,96,31,21],[]),([47,7,1,2,3,4,5],[15,4,7,6,8,0,97,12],[0]),([33,7,1,2,3,42,4,5],[27,98,3],[]),u6 [68,31] [31,3,11,99,21]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_7_1 : checkNodesBT W_44 g_44 F_44 P_44_7_1 A_44 B_44_6 7 N_44_7_1 = true := by decide +kernel
def N_44_7 := N_44_7_0 ++ N_44_7_1
def B_44_7 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_7
set_option maxRecDepth 500000 in
lemma B_44_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 7 xs.toFinset) B_44_7 := by
  have hm0 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_6_ok C_44_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_6_ok C_44_7_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_44_8_0 : List Nat := (r 3 10++[14,15,18,20,21])
def P_44_8_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_8_0
def N_44_8_0 : List NodeSpec := [([112,0,1,2,4,5,23],[6,4],[]),u6 [43,124] [3,5,4,9,6],([88,7,1,2,3,4,5],[4,3,7,9,6],[0]),([83,7,1,2,3,4,5],[6,4,9],[0]),([88,112,0,1,3,4,5],[6,9],[]),e6 [462] [11,3,6],e6 [273] [11,3,6,9],e6 [476] [11,9],e6 [491,124] [3,4,12,6],e6 [553] [3,11,12],e6 [269] [3,12],e6 [310] [3,12],e6 [471] [3,12],e6 [314] [3,12],e6 [297] [3,12],e6 [546] [3,12],e6 [280] [3,12],e6 [256] [3,12],([129,37,33,1,2,3,4,5],[3,12,9],[0]),u6 [33,124] [3,12,9,6,5],e6 [113,305] [4,3,12],u6 [107,122,124] [4,6,3,12],e6 [112,38,118] [4,12,6],e6 [129,112] [6,12,4],e6 [26,337] [9,11,12,3],u6 [88,7] [10,12,3,11,6,9],e6 [463] [11,12,4],e6 [502] [11,12,4,6],u6 [124,31] [12,6,9,10],u6 [129,156] [12,7,10,6],e6 [313] [12,9],e6 [234] [12,9,6],([26,0,1,2,167,4,5],[3,14,12],[]),u6 [129,34] [6,12,3,14],([26,0,1,2,457,4,5],[14,3,12],[]),([179,7,1,2,3,4,5],[6,9,4,12,15],[]),e6 [179,7] [9,12,6,15],e6 [7,42] [15,3,8,4,12],([505,0,1,341,3,4,5],[3,20,4],[]),([129,0,506,2,3,4,5],[3,20,12],[]),([129,88,83,0,1,3,4],[12,4,20,9],[]),([129,0,90,2,3,4,5],[12,4,20,9],[]),e6 [536] [20,6,4],e6 [53,352] [3,4,21],u6 [38,54] [3,11,4,6,21],u6 [83,67] [3,11,6,21,4],e6 [389] [3,12,6,21],e6 [26,434] [3,12,14,21],e6 [80,472] [3,12,14,21],e6 [26,361] [3,12,14,21],e6 [26,449] [3,12,14,21],e6 [102,283] [3,12,21],([26,95,1,2,3,4,5],[3,14,21],[]),([26,283,1,2,3,4,5],[3,14,21],[]),([26,80,1,2,3,4,5],[3,14,21],[]),([26,0,1,2,144,4,5],[3,14,21],[]),e6 [470,155] [3,14,21,6,9],e6 [88,160] [3,14,21,6,9],e6 [510] [3,15,21],e6 [551] [3,21],e6 [380] [3,21],e6 [43,160] [3,21,6],u6 [95,57] [3,21,6],e6 [486,67] [3,21,6],e6 [33,160] [3,21,6],e6 [28,437] [3,21,6],e6 [95,260] [3,21,9],e6 [347,167] [3,21,12],([61,39,1,2,3,4,5],[3,21,12,18],[]),e6 [544,67] [3,21,15,6],e6 [347] [6,3,12,21],([37,0,1,2,9,4,5],[6,20,21,11,12],[0]),e6 [26,342] [9,3,14,21],e6 [376] [9,21],e6 [343] [9,21],e6 [533] [9,21],u6 [141,31] [9,21,3,5,14],u6 [94,31] [9,21,3,14],([53,107,0,1,3,4,5,31],[11,21,4],[]),e6 [53,148] [11,21,4,3],e6 [53,31] [11,21,4,3],e6 [88,29] [11,21,6,12],e6 [61,288] [11,21,6,18],u6 [38,131] [12,4,21],e6 [61,267] [12,9,21,6],e6 [428] [12,21],e6 [443] [12,21],e6 [525] [12,21],e6 [465] [12,21,4],([100,0,1,8,3,4,5],[12,21,6],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_8_0 : checkNodesBT W_44 g_44 F_44 P_44_8_0 A_44 B_44_7 8 N_44_8_0 = true := by decide +kernel
def U_44_8_1 : List Nat := (r 3 5++r 9 4++[14,15,18,20,21,22]++r 27 4)
def P_44_8_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_8_1
def N_44_8_1 : List NodeSpec := [([88,0,1,3,4,116,5],[12,21,6],[0]),e6 [155,31] [12,21,18,6,14,4,3],([26,0,1,2,155,4,5],[14,3,21],[]),([244,245,0,1,2,3,4],[15,9,21],[]),e6 [248,188] [15,21,6,9],e6 [244,61] [18,6,3,21],([202,166,0,1,3,4,5],[20,21,12],[]),([88,202,0,1,3,4,5],[20,21,12],[]),u6 [80,43] [21,3,4],e6 [455,188] [21,3,9],e6 [271,188] [21,3,9],e6 [542] [21,3,12,6],([88,153,0,1,3,4,5],[21,4],[]),([100,0,1,2,4,5,23],[21,4],[]),([0,1,2,236,4,5,23],[21,4],[]),e6 [367,83] [21,4,9,6],([0,1,115,38,4,5,23],[21,4,11],[0]),e6 [271,23] [21,4,11,12],e6 [252] [21,4,20],e6 [282,188] [21,6,3,20],e6 [317] [21,9],e6 [433] [21,9],e6 [534] [21,9],e6 [529] [21,9],([102,0,1,236,3,4,5],[21,9],[]),e6 [501] [21,9],e6 [545] [21,9],([0,1,2,4,189,188,23],[21,9],[]),e6 [378] [21,9],e6 [384] [21,9],([179,0,1,2,3,4,342],[21,9],[]),u6 [95,8] [21,9,10,3],([249,0,1,3,4,188,5],[21,9,15],[]),([0,474,2,3,4,188,5],[21,9,15],[]),([0,1,487,3,4,188,5],[21,9,15],[]),([248,1,2,3,4,188,5],[21,9,15],[]),e6 [95,116] [21,11,9,3,10],e6 [441] [21,12],u6 [242,80,23] [21,12],e6 [202,80] [21,12,4],([0,1,2,309,38,4,23],[21,12,4,6],[]),e6 [362] [21,12,6],([26,0,90,2,3,4,5],[21,12,20,9],[0]),e6 [364] [21,14,6],([26,429,0,1,2,4,5],[21,20,9],[]),u6 [7,8] [6,10,3,21,4,9,15,22],([28,7,1,2,3,4,5],[3,7,27,4,6,5,15,9],[0]),([26,7,1,2,3,4,5],[3,27,4,6,9,15],[0]),([109,7,1,2,3,4,5],[3,27,15,4,6,12],[0]),([27,7,1,2,3,4,5],[15,3,27,4,6,9],[0]),e6 [367,122] [21,3,11,12,6,9,27,4],([22,7,1,2,3,4,5],[5,3,27,4,6,28],[0]),e6 [350] [3,12,29,21],([125,7,1,2,3,4,5],[4,6,29,9],[]),e6 [492] [11,21,29],([28,367,0,1,2,4,5],[21,6,9,29],[]),u6 [26,137] [3,4,21,6,30],e6 [113,312] [3,4,30],e6 [113,80] [3,4,30],u6 [113,182] [3,4,30,15],u6 [83,7] [3,10,4,30,21,9],u6 [26,211] [3,14,30,21,6,4],e6 [393] [3,15,30],e6 [530] [3,30,14,21],e6 [414,144] [3,30,21],e6 [88,62] [3,30,21,6],u6 [175] [4,9,30,6],e6 [113,28,166] [4,12,9,30,3],e6 [129,28,152] [4,12,30,11,3],e6 [129,9] [4,20,30],e6 [519] [4,30],e6 [92,126] [4,30,9,11,3],([129,0,1,2,9,4,5],[4,30,20],[]),e6 [61,303] [6,11,21,30],e6 [387] [11,30,4],e6 [444] [11,30,21],e6 [129,53,38] [12,4,30,3,11],([88,61,0,1,3,4,152,5],[12,21,6,30],[]),e6 [283,43] [18,3,30,21],([88,0,1,341,3,4,5],[20,30,4],[]),e6 [348,23] [21,4,30,6,3],e6 [182,188] [21,6,3,11,4,30],e6 [80,57] [21,14,3,30],e6 [447] [21,30],e6 [312,114] [21,30,4],e6 [406] [30,4],e6 [513] [30,4],e6 [540] [30,4],e6 [532] [30,4],e6 [321] [30,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_8_1 : checkNodesBT W_44 g_44 F_44 P_44_8_1 A_44 B_44_7 8 N_44_8_1 = true := by decide +kernel
def U_44_8_2 : List Nat := (r 3 4++r 9 4++[14,15,19,20,21,24,29,30,31])
def P_44_8_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_8_2
def N_44_8_2 : List NodeSpec := [e6 [523] [30,4],e6 [316] [30,4],e6 [287] [30,4],e6 [517] [30,9],e6 [296] [30,9],e6 [460] [30,15,21],e6 [323] [30,15,21],e6 [129,509] [30,20,4],e6 [315] [30,21],e6 [390] [30,21],e6 [398] [30,21],e6 [405] [30,21],e6 [371] [30,21],e6 [319] [30,21],e6 [370] [30,21,6],e6 [62,23] [30,21,6,3],u6 [43,209] [3,4,12,9,31,21],e6 [500] [3,11,31,12,6,21],u6 [102,80] [3,21,14,4,31],u6 [38,126] [3,30,4,14,19,21,31,6],e6 [304] [3,31,4],([102,0,1,123,3,4,5],[3,31,6],[]),e6 [432] [3,31,11,12],([26,39,1,2,3,4,5],[3,31,14],[]),e6 [74] [3,31,14,21],e6 [468] [3,31,21,4],e6 [493] [3,31,21,4],([166,80,1,2,3,4,5],[3,31,21,4],[0]),e6 [87] [3,31,21,4,6,12],e6 [511] [3,31,21,4,12],e6 [312] [3,31,21,4,30],u6 [55] [3,31,21,6,11,9],e6 [289] [3,31,21,6,11,12],e6 [295] [3,31,21,12],e6 [270] [3,31,30,4],e6 [414] [3,31,30,6,21],e6 [417,23] [4,6,3,11,31],([88,265,0,1,3,4,5],[4,12,31],[]),e6 [37,266] [4,21,31,10,30,3,11],u6 [83,87] [4,30,31,21],u6 [95,43] [5,3,21,31,4,10,6,9],e6 [88,124] [6,4,12,31,21],([89,275,0,2,3,4,5],[6,20,31],[]),([37,89,0,1,2,3,5],[6,20,31,4,12],[]),e6 [37,9] [6,20,31,21,10,24,11,12],([112,0,1,3,4,5,31],[6,31],[]),([112,0,1,2,3,188,5],[6,31],[]),([0,1,3,4,188,250,5],[6,31,9],[]),e6 [179,235] [9,30,21,31,15],e6 [276] [9,31,21],e6 [93] [11,6,31,4],e6 [369] [11,31,3],e6 [306] [11,31,4],e6 [419] [11,31,6],e6 [420] [11,31,6],e6 [469] [11,31,6],e6 [528] [11,31,6],e6 [416] [11,31,12],e6 [550] [11,31,12],e6 [373] [11,31,12],e6 [412] [11,31,12],e6 [478] [11,31,21,6],e6 [490] [11,31,29],([88,0,1,403,3,4,5],[11,31,30],[]),e6 [404] [11,31,30],u6 [43,172] [12,21,6,31],e6 [298] [12,31,6],([153,179,0,1,2,4,5],[12,31,6],[]),e6 [107,466] [12,31,21,4],([88,112,0,1,3,38,4,5],[12,31,21,9],[]),([88,83,262,0,1,3,4],[20,12,31,4],[]),([0,1,2,266,4,188,5],[21,4,31],[]),([179,0,90,2,3,4,5],[21,9,31],[]),([0,90,2,3,4,188,5],[21,9,31],[]),([0,1,224,3,4,116,5],[21,9,31],[0]),e6 [92,114] [21,30,11,4,3,31],e6 [251,188] [21,31,3,9,6],([153,0,1,2,4,188,5],[21,31,4],[]),([88,0,1,3,266,4,5],[21,31,4],[]),([107,367,0,1,2,4,5],[21,31,4],[]),([92,0,1,2,4,188,5,23],[21,31,4,3,12],[]),e6 [228] [21,31,4,30,6,3],([254,100,0,1,3,4,5],[21,31,9],[0]),e6 [411] [21,31,9],u6 [153,122] [21,31,12,6,4],e6 [72,9] [21,31,20,4,6,24],([102,26,0,1,3,4,5,31],[21,31,20,6,4,10],[]),u6 [43,189] [30,21,6,31],([0,43,1,341,3,4,5],[30,31,4],[]),e6 [339] [30,31,21,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_8_2 : checkNodesBT W_44 g_44 F_44 P_44_8_2 A_44 B_44_7 8 N_44_8_2 = true := by decide +kernel
def U_44_8_3 : List Nat := (r 3 10++[14,15]++r 18 4++[27,29,30,31,34]++r 39 5++[45,46])
def P_44_8_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_8_3
def N_44_8_3 : List NodeSpec := [e6 [26,359] [31,3,4,12],([308,1,2,3,4,5],[31,3,12,4],[]),e6 [26,357] [31,3,14,30],u6 [108,7] [31,4,10,3,15,8],e6 [262,188] [31,6,3,30],([26,0,1,2,143,4,5],[31,11,3],[]),([88,28,0,1,3,4,152,5],[31,11,6],[]),([102,0,90,1,3,4,5,31],[31,11,6],[0]),([102,28,0,1,3,4,5,31],[31,11,6],[0]),([88,0,1,401,3,4,5],[31,11,30],[]),u6 [107,150] [31,12,11,6,3,21,4],e6 [243,80] [31,21,3,4],e6 [386,188] [31,21,3,9],e6 [259,95] [31,21,3,9],([202,0,43,1,3,4,5],[31,21,4],[0]),([423,0,1,3,4,188,5],[31,21,9],[]),([265,0,43,1,3,4,5],[31,29,4],[]),e6 [83,80] [4,30,34],([88,37,83,0,1,3,4],[6,12,20,11,34,31],[]),e6 [88,80] [12,21,4,34],e6 [268] [3,21,39,4],e6 [360] [3,21,39,4],e6 [333] [3,21,39,4],e6 [531] [3,21,39,4],e6 [320] [3,21,39,4],e6 [85] [3,21,39,4,6,31],([129,386,1,2,3,4,5],[3,39,31,4],[]),e6 [543] [6,3,39,31],([37,0,1,2,3,126,5],[6,30,39,11,9],[0]),e6 [518] [21,3,39,4],e6 [410] [21,3,39,4,31],e6 [284] [21,4,3,39],e6 [286] [21,4,3,39],e6 [338] [21,6,31,9,39,3],e6 [255,188] [21,6,39,3],e6 [258,188] [21,6,39,3],e6 [461] [21,31,39,4],e6 [302] [31,3,39,4],([92,7,1,2,3,4,5],[3,27,9,6,40,12,4],[0]),e6 [399] [3,31,10,40],e6 [238] [3,31,14,40],([129,271,1,2,3,4,5],[3,39,40,12],[]),u6 [7,14] [3,40,8,10,15,12],e6 [346] [6,14,40,31],u6 [160,31] [9,6,3,14,40,31],([0,1,3,4,539,152,5],[12,31,6,40],[]),([0,1,2,114,38,4,5],[21,4,40],[0]),e6 [340] [21,9,40],([0,1,2,155,38,4,5],[21,12,40,6],[0]),([0,1,3,547,38,4,5],[21,12,40,9],[]),e6 [477] [30,9,31,40],u6 [130] [30,12,40,4,9,6],e6 [334] [31,3,14,40],([202,0,1,38,4,5,23],[40,21,4],[]),([107,7,1,2,3,4,5],[3,4,7,15,41],[0]),e6 [503,107] [31,12,21,4,41],u6 [7,38] [15,21,12,3,8,42,10,4,7,6],([79,7,1,2,3,4,5],[5,3,7,43,6],[0]),e6 [459] [3,4,30,9,45],e6 [28,124] [3,9,4,12,6,5,45],([129,182,1,2,3,4,5],[3,40,45,21,7,4],[]),([0,1,2,67,4,188,5],[3,45,21,15],[]),([92,348,1,2,3,4,5],[11,40,45,3,12],[]),([0,1,2,3,63,152,5],[12,6,45,40,21],[]),([0,1,2,58,38,4,5],[21,12,45,40,6],[]),e6 [28,209] [3,9,4,12,6,46,18,31,21],u6 [7,57] [3,10,12,21,46,15],u6 [30] [3,31,46,4,6,11],e6 [28,386] [3,46,11,4,12,21],e6 [28,499] [3,46,31,12,4,9,18,11],e6 [92,327] [4,46,11,21,3,31],e6 [37,327] [4,46,21,10,3,6],e6 [122,327] [4,46,21,11,30],e6 [38,157] [10,12,7,21,46,15,6],e6 [53,341] [11,3,4,21,46],e6 [28,288] [11,6,46,21],e6 [28,285] [11,6,46,21],e6 [28,267] [11,6,46,21],e6 [28,377] [11,9,46],e6 [125,332] [11,12,6,46,21],e6 [424] [11,18,3,21,6,46],e6 [535] [11,46,3],e6 [354] [11,46,4],u6 [38,118] [12,21,46,4,6],e6 [58,31] [12,46,21,9],e6 [37,396] [19,46,21,12,11],u6 [67,31] [21,3,11,9,46],e6 [125,123] [30,12,46,21,4],e6 [28,227] [30,31,6,46,21],([61,271,1,2,3,4,5],[40,21,3,4,46],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_8_3 : checkNodesBT W_44 g_44 F_44 P_44_8_3 A_44 B_44_7 8 N_44_8_3 = true := by decide +kernel
def U_44_8_4 : List Nat := ([3,4,6]++r 9 4++[14,15,18,20,21,24,27,29,30,31,39,40,45,46,51,53,54,57,58])
def P_44_8_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_8_4
def N_44_8_4 : List NodeSpec := [u6 [83,216] [46,11,4,30,21,3,6],e6 [28,453] [46,11,6,21],e6 [408] [46,30,21,4],e6 [485] [46,30,21,4],e6 [26,328] [4,6,3,12,21,51],e6 [244,92] [4,11,3,31,21,29,51,9],e6 [139,80] [6,3,4,21,15,51],e6 [139,92] [6,4,3,21,51,9],e6 [139,61] [6,30,21,51],e6 [26,126] [9,21,14,51],e6 [26,277] [21,20,6,4,30,51],([102,139,0,1,2,3,5],[21,51,6,31],[0]),u6 [88,61,6] [30,51,11,12],e6 [527,188] [31,21,6,9,3,12,51],e6 [454] [51,39,4,6,31,21],e6 [483] [51,39,6,27,31,21],e6 [253] [3,20,53,31],e6 [237] [3,20,53,31],e6 [480] [3,31,53],e6 [293] [3,31,53],([244,0,1,2,4,188,23],[4,53,21],[]),e6 [26,382] [9,3,21,53],e6 [26,355] [9,3,21,53],u6 [9,6] [9,30,51,20,6,4,31,21,53],e6 [541] [11,31,20,53,3],e6 [537] [11,31,20,53,3],e6 [413] [11,31,40,53,3],([119,0,1,2,38,4,23],[12,53,4],[]),e6 [436] [15,3,21,53],e6 [467] [21,3,39,53,6],([0,1,2,167,4,5,23],[21,4,3,40,53],[0]),([0,1,2,9,4,5,23],[21,4,20,53],[0]),([0,1,2,105,4,5,23],[21,4,53],[0]),([0,1,2,4,116,5,23],[21,4,53],[]),e6 [329] [21,10,53],([0,1,2,144,4,5,23],[30,21,45,6,53],[0]),e6 [426] [31,3,40,53],e6 [28,262] [45,3,46,31,53,4,18],e6 [88,63] [45,29,12,53,21],e6 [407] [53,3,31],e6 [262] [53,3,31],e6 [301] [53,3,31],e6 [251] [53,3,31,40,15],e6 [538] [53,3,31,40,46],([137,0,1,2,3,4,23],[53,21,4],[]),e6 [282,23] [53,21,4,3,20],e6 [129,63] [53,30,4,9],e6 [129,58] [53,30,12,9],e6 [353] [3,21,12,54,53],e6 [473] [3,21,54,4],([26,182,1,2,3,4,5],[3,54,4,21],[]),([26,271,1,2,3,4,5],[3,54,4,21],[]),([26,348,1,2,3,4,5],[3,54,12,21],[]),e6 [72] [3,54,20,12,21,24],([26,121,1,2,3,4,5],[3,54,21,6],[]),e6 [358] [3,54,40,4],e6 [124,23] [4,6,3,10,54,21],([0,1,38,4,5,31,23],[12,4,53,54],[]),([88,0,1,38,4,5,23],[12,54,21,6,53],[]),e6 [504] [21,3,18,6,54],([0,1,2,3,4,342,23],[21,4,45,40,54],[]),([0,1,2,114,4,188,5],[21,4,54,53],[]),([0,1,2,105,4,188,5],[21,6,40,54],[]),([0,1,2,3,45,188,5],[21,6,54],[0]),e6 [330] [30,4,21,54],e6 [318] [30,6,4,21,54],e6 [375] [54,3,21,12],e6 [83,95] [3,4,9,10,21,57,31],([61,80,1,2,3,4,5],[3,57,21,4],[0]),([88,0,1,3,4,84,5],[4,57,9],[]),([0,1,2,4,180,5,23],[57,4,15],[]),e6 [261] [57,4,39,3,31,45],([0,1,2,4,228,5],[57,12,4,6,21],[0]),e6 [274] [57,12,9],e6 [439] [57,12,9],e6 [257,95] [57,21,3,9],e6 [61,180] [57,21,30],([125,0,1,2,9,4,5],[57,30,4],[]),([0,1,3,4,84,5,31],[57,31,4],[]),([0,1,3,4,227,31],[57,31,4,6],[]),([0,1,3,309,4,31],[57,31,9,6],[]),([0,1,3,4,250,5],[57,31,9,30,6],[]),e6 [28,157] [3,10,15,4,12,6,46,45,14,31,58],e6 [366] [3,12,58,15,31],e6 [33,352] [3,14,4,21,58,11],e6 [28,427] [3,15,4,12,46,45,31,58],e6 [498] [3,30,58],u6 [33,7] [3,58,10,12,15,21,31],e6 [33,80] [3,58,14,12,21],e6 [33,95] [3,58,21,9,6,31,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_8_4 : checkNodesBT W_44 g_44 F_44 P_44_8_4 A_44 B_44_7 8 N_44_8_4 = true := by decide +kernel
def U_44_8_5 : List Nat := (r 3 5++r 9 4++[14,15,18,20,21,22,24,27,29,30,31,39,40,45,46,51,53,54,57,58,59,61,62,65,67,69,70,71,73,79,81,82]++r 84 4)
def P_44_8_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_8_5
def N_44_8_5 : List NodeSpec := [e6 [37,148] [4,11,58,10,3,9],e6 [122,148] [4,11,58,31,21,3,12],u6 [33,157] [4,15,12,58,31,21],([102,0,90,3,4,5,31],[4,31,11,58],[0]),e6 [122,342] [4,58,9,11,12],e6 [37,328] [4,58,31,21,12],e6 [26,267] [9,11,58,12],e6 [26,288] [9,11,58,12,3,14],e6 [37,279] [9,21,58,12],([37,0,1,3,38,4,5,31],[9,21,58,12,14,6],[]),e6 [53,377] [11,3,58,21],([28,0,1,2,105,4,5],[11,6,4,58,21],[0]),e6 [57,148] [11,21,4,58],([53,0,1,2,9,4,5],[11,21,58,6],[]),e6 [28,277] [11,58,6,4,21],([0,488,1,2,9,4,5],[11,58,6,4,24,21],[]),([88,37,0,1,3,38,4,5],[12,14,9,21,58],[]),e6 [33,180] [12,21,6,58],([107,0,57,1,3,4,5,31],[12,58,21,4],[]),([89,0,90,2,3,4,5],[20,45,4,58,31],[0]),e6 [89,90] [20,45,6,58,31,4],([88,83,0,1,3,4,6],[22,4,57,9,20,11,58],[0]),([37,107,0,1,3,4,5,31],[31,4,11,58,21,12,14],[]),([107,122,0,1,3,4,5,31],[31,12,11,4,58,21,14],[]),e6 [527,23] [31,21,4,12,6,58,3,51],e6 [28,481] [45,3,46,9,4,12,31,58],e6 [397] [58,30,21],([61,0,1,2,9,4,5],[58,30,21],[]),e6 [61,277] [58,30,21],([102,275,0,3,4,5,31],[58,31,4],[]),e6 [83,121] [3,11,6,21,61,31],e6 [121,23] [21,4,3,11,6,62,51,61],u6 [182,23] [21,4,3,11,62],([0,1,2,50,4,5,23],[21,4,45,40,62],[]),e6 [349] [3,14,65,21],e6 [368] [10,45,4,65,31],e6 [402] [12,45,65,9],e6 [359] [20,4,31,45,65],e6 [438] [20,45,4,65,9],e6 [119] [20,45,4,65,31],([53,139,0,1,2,3,5],[21,65,51,6],[]),([95,122,1,2,3,4,5],[3,67,9],[0]),e6 [272] [11,67,3,6],e6 [521] [11,67,3,6],e6 [325] [11,67,57,3],([0,1,2,3,124,152,5],[12,6,67,40],[0]),e6 [496] [12,46,6,67,40],e6 [435] [21,4,67,39,31],e6 [448] [21,6,67,39],e6 [256,188] [31,6,67,12],e6 [395] [31,6,67,39],([0,1,2,3,437,5,6],[51,67,4,6],[]),e6 [300] [57,4,31,67,39,45,65],e6 [84] [57,4,31,67,39,45,65],e6 [278] [67,3,21,54,4],e6 [422] [67,6,39,31],e6 [489] [67,6,39,31],([0,1,2,3,45,5,6],[6,4,59,69,45,40,21,53],[0]),u6 [61,31,6] [4,30,51,11,12,70,3],u6 [167,6] [14,70,29,21,58,4,12],u6 [61,23,6] [30,4,51,21,57,70,46,3],u6 [143,6] [51,14,70,3,27,21,6,4,31,12],u6 [164,105] [4,11,53,21,71],u6 [185,105] [6,11,71,21,31,15],u6 [106,105] [21,39,6,4,71],([61,7,1,2,3,4,5],[3,27,4,5,6,73],[0]),u6 [163] [18,30,31,21,70,73,3,6],u6 [61,38,6] [51,30,4,21,12,70,73],e6 [244,92,188] [6,9,12,79,4],e6 [92,29] [11,46,45,3,79,12,51],e6 [92,180] [12,6,21,9,11,81,79,58],e6 [92,322] [21,30,11,9,6,3,81],e6 [367,92] [21,51,9,6,81],u6 [92,189,188] [31,9,21,81,4],u6 [129,50] [4,82,21,31,30,3,7],e6 [324,38] [21,11,4,12,3,84,6],e6 [57,352] [3,14,85,4,21],e6 [92,63] [11,29,45,3,85,21,31,12],e6 [166,63] [12,85,21],e6 [348,188] [21,6,3,85],e6 [450] [21,6,4,85,18],([0,1,2,3,63,188,5],[21,6,85,45,54],[]),u6 [58,6] [51,6,85,12,4,21,46,53],e6 [514] [85,12,21],e6 [552] [3,31,85,12,21,86],e6 [37,58] [6,85,12,21,46,10,86,11],e6 [552,58] [21,85,9,6,86],([61,0,1,3,4,152,5,31],[6,12,87,30,3],[]),u6 [61,148] [11,21,4,12,18,87,58,3,6],u6 [144,6] [30,51,70,4,27,21,87,6]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_8_5 : checkNodesBT W_44 g_44 F_44 P_44_8_5 A_44 B_44_7 8 N_44_8_5 = true := by decide +kernel
def U_44_8_6 : List Nat := ([0]++r 3 10++[14,15]++r 18 5++[24,27,30,31,32,35,39,40,42,45,46,50,51,53,54,55,57,58,65,67,68,71,76]++r 85 7++[95]++r 99 13)
def P_44_8_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_8_6
def N_44_8_6 : List NodeSpec := [([107,61,0,1,3,4,5,31],[58,12,87,4,11],[0]),e6 [549] [3,21,88],e6 [27] [3,21,88,53],e6 [526] [3,31,88,4],e6 [235] [3,40,15,88,6,12],([129,37,1,2,3,427,5],[3,88,4],[]),([37,262,1,2,3,4,5],[3,88,4],[]),([37,283,1,2,3,4,5],[3,88,9],[]),([37,282,1,2,3,4,5],[3,88,11,12,6],[]),([37,348,1,2,3,4,5],[3,88,12,21,11,6],[]),e6 [520] [3,88,31,21,12],u6 [97,9] [6,20,31,88,21,24],u6 [187,58] [6,85,21,88,86],([139,0,1,2,188,5,23],[6,88,21],[]),e6 [507] [11,31,67,88,57],e6 [452] [11,88,3,12],e6 [548] [11,88,3,12],e6 [264] [12,45,65,88,9],([0,1,2,155,4,188,5],[21,3,88,6],[0]),([0,1,2,9,4,188,5],[21,6,20,40,88],[0]),([0,1,2,58,4,188,5],[21,6,85,45,88],[]),e6 [431] [21,20,31,88,6],e6 [482] [30,21,88,15],e6 [263] [30,31,88,6],u6 [37,40,38] [21,89,19,42,11],e6 [311,112,38] [89,12,19,71],u6 [125,37,38] [89,19,11,6,50,3,12],u6 [26,43,6] [55,21,90,68,3,31],e6 [445] [3,12,91,21],e6 [392] [3,30,91,21],e6 [515] [3,31,65,91,4],e6 [524] [3,31,91,4],e6 [464] [3,31,91,4],e6 [418] [3,31,91,53],([129,80,1,2,3,4,5],[3,39,91,4],[]),e6 [516] [3,91,53,21],e6 [372] [3,91,53,21],e6 [344] [3,91,53,21],e6 [522] [3,91,54,4],e6 [391] [10,21,91],e6 [425] [11,4,54,91],e6 [440] [31,3,91,53],u6 [145,50] [4,53,21,95],u6 [68] [3,31,15,53,21,99],([113,0,233,2,3,4,5],[12,9,100],[]),([7,1,2,14,3,4,5],[3,4,8,27,7,0,12,15,6,101],[0]),e6 [241,23] [4,6,3,102,54,21],e6 [239,23] [21,4,3,11,102],e6 [42] [21,15,3,9,102,6],u6 [80,115] [3,31,102,21,4,103],([92,0,1,115,3,4,5,23],[21,31,4,103],[]),e6 [240,23] [4,21,6,3,104],([37,139,0,1,2,3,5,23],[4,21,6,51,104],[]),e6 [240,80,23] [4,104,102],e6 [139,81] [6,4,21,104,51],e6 [139,33] [6,21,104,51,4],e6 [246] [3,31,40,6,105],u6 [178] [3,4,9,106,39,45],e6 [554] [3,31,12,106],u6 [194] [11,106,4,54,91],([112,113,0,1,2,3,5],[12,106,31,6,21],[0]),e6 [497] [21,4,67,39,106],e6 [99] [21,6,67,39,106],([367,0,1,2,4,188,5],[21,54,9,106],[]),e6 [400] [21,106,39,6],([139,0,1,2,3,188,5],[54,21,9,106],[]),([499,122,1,2,3,4,5],[3,20,107,67,4],[]),([39,122,1,2,3,4,5],[3,107,20,21,12],[0]),([129,0,1,2,3,4,373],[3,107,39,11],[]),e6 [254,95] [107,21,9,10,3],e6 [388] [3,6,39,4,9,108],e6 [294,28] [4,12,7,14,31,108,51,6],e6 [80,152] [4,31,3,108],e6 [89,26] [6,3,4,21,31,108,35,51],e6 [89,61] [6,30,3,21,20,4,108,87],e6 [61,84] [6,30,4,31,108,12,46,21],([0,1,2,4,152,228,5],[12,6,108],[]),([88,26,0,1,3,4,152,5],[12,108,31,11,4,6],[]),e6 [294,61] [18,12,46,21,6,31,108],e6 [351] [21,6,4,108,53],u6 [144,31] [30,21,87,4,6,3,108],e6 [89,28] [45,6,46,31,108,20,51,9],u6 [26,8,6] [55,51,21,76,30,108,9],u6 [85,84] [108,6,31,32],u6 [28,84] [108,57,31,6,46,5,14],u6 [87,84] [6,4,108,30,109],([88,83,0,1,3,4,84],[110,4,57,31,11,58],[0]),e6 [374,342] [4,58,9,11,111],u6 [7,31] [11,10,8,12,6,9,3,111,22,106],u6 [80,81] [46,14,111,21,6,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_8_6 : checkNodesBT W_44 g_44 F_44 P_44_8_6 A_44 B_44_7 8 N_44_8_6 = true := by decide +kernel
def U_44_8_7 : List Nat := (r 3 10++[14,15]++r 18 5++[24,27,29,30,31,34]++r 36 7++r 45 5++[51,53,54,55,57,58,65,67,68,70,72,84,85,87,88,91,92,94,102,104,106,108]++r 111 63)
def P_44_8_7 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_8_7
def N_44_8_7 : List NodeSpec := [e6 [80,31] [4,11,58,14,102,21,3,111,12,112,91],u6 [80,8] [21,14,3,4,112],e6 [421] [3,4,113,65,21,54,6],e6 [383] [46,30,21,6,88,113,87],([113,0,90,2,3,4,5],[12,9,114],[]),([0,90,2,3,4,91,5,31],[36,37,29,9,4,114,58],[0]),e6 [91,31] [113,6,37,9,40,31,114],e6 [37,326] [6,115,31,11,21,12],e6 [37,236] [9,21,57,10,12,115,5],u6 [43,180] [21,57,5,115,6,9,31],u6 [37,156] [31,21,94,12,115,6,4],([102,0,1,326,3,4,5],[115,31,6],[]),([0,90,2,3,4,5,23],[21,4,111,115,116,31],[]),([0,90,2,3,4,5,6],[70,4,9,111,115,116,31,27],[0]),([7,57,1,2,3,4,5],[3,117,6,12,4,9,27,5],[0]),([7,1,8,2,3,4,5],[6,117,3,4,9,15,22],[0]),([97,0,1,2,9,4,5],[6,20,118,24,21,119],[0]),([0,1,2,9,4,99,5],[21,6,20,40,119],[0]),e6 [97] [67,6,39,21,27,9,119],([281,0,1,2,9,4,5],[11,58,6,4,120,21],[]),([28,0,1,2,9,4,5],[11,58,6,4,120,21],[]),([72,0,1,2,9,4,5],[21,30,12,4,24,6,121,38,20],[0]),e6 [179,290] [3,11,21,6,122],e6 [291] [11,21,53,91,123],([7,1,2,3,4,5,23],[6,4,15,124,3,7],[0]),u6 [7,23] [15,21,4,14,8,6,124,3,7],u6 [60] [12,125,15,3,27,4,126,45,9],e6 [112,61] [6,30,3,21,127],e6 [140] [3,4,6,12,129],e6 [112,140] [12,6,3,129,21],u6 [112,140,38] [19,12,3,127,128,129],u6 [140,38] [21,12,130,42,3,128,129],u6 [82,23] [21,6,14,11,45,131],u6 [37,81,23] [21,104,6,46,4,131],e6 [290,23] [21,4,3,11,132,51],([80,0,1,2,38,4,5,23],[21,4,12,132],[0]),([0,1,2,309,4,23],[57,4,6,132],[]),([112,0,1,2,38,4,5,23],[12,21,4,133,6],[]),e6 [374] [3,21,134,9,11],e6 [40,309] [12,31,46,21,6,4,134,135,27,47],u6 [112,40] [42,6,127,136,21,12,27,4,31],u6 [112,39] [6,3,12,21,137,138],u6 [39,40] [3,12,48,42,11,21,139],e6 [241] [3,67,6,140],u6 [119,53] [4,3,10,21,20,141],u6 [119,61] [4,12,3,51,21,141],e6 [119,112] [4,12,6,21,141,31],e6 [119,37] [4,12,21,141,31],u6 [119,40] [4,12,47,27,21,141],([37,39,1,2,3,4,5],[3,88,12,20,142],[]),([37,39,1,2,3,38,4,5],[12,21,3,19,39,142,137],[0]),e6 [429,122] [21,12,11,18,143,9],e6 [37,28,31] [11,143,144,145,6],e6 [37,202] [31,21,4,146,12],e6 [37,33,23] [146,147,148,12,6],([166,7,1,2,3,4,5],[3,4,9,67,149,31],[0]),([13,7,1,2,3,4,5],[3,4,15,67,149],[0]),([7,43,1,2,3,4,5],[3,4,68,5,149],[0]),([7,1,2,3,4,5,31],[6,4,9,7,5,22,149,106],[0]),([37,0,1,2,38,4,5,23],[4,21,46,12,150,6],[]),([37,0,1,2,3,45,5],[6,4,21,39,11,3,150],[]),e6 [331] [21,31,3,151,30,6],e6 [83,141] [3,10,21,6,4,152],u6 [113,50] [49,11,4,21,72,3,10,153,6,154],u6 [204,50] [72,21,4,92,6,154],u6 [53,123] [11,20,3,18,155],e6 [335] [11,21,53,4,3,155],u6 [53,122,38] [12,21,3,46,155,11,84],e6 [26,227] [31,30,14,21,156],u6 [120,38] [11,19,12,3,157,158],([26,0,1,2,9,4,5],[21,6,4,20,30,159],[0]),([122,0,1,2,3,4,31,23],[4,143,14,12,160],[]),e6 [123,155] [3,14,21,18,12,34,160,161,6],([0,1,2,9,4,5,6],[57,4,30,20,6,22,162,21],[0]),e6 [26,57,6] [55,163,30,3],e6 [26,63] [3,12,6,164,4,85,21],e6 [365] [3,21,39,164,6,9],e6 [63,31] [12,11,45,29,53,9,164],u6 [63,23] [30,6,3,4,21,164],e6 [179,121] [3,11,21,6,165],u6 [121,38] [21,11,3,12,4,19,165,6],e6 [37,342] [4,9,11,10,3,166],([37,0,90,2,3,4,5],[4,166,31,12,6,21,111,115],[]),([129,37,1,2,3,38,4,5],[12,4,3,10,167],[0]),u6 [34,23] [14,6,3,115,21,168],e6 [345] [11,39,21,31,169,12,4],u6 [212] [58,170,30,6,67,21],u6 [107,7] [3,31,8,4,7,15,11,41,171],u6 [26,84] [31,108,6,172,14,3,21,9,30],e6 [107,209] [3,4,173,12,31,58,21]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_8_7 : checkNodesBT W_44 g_44 F_44 P_44_8_7 A_44 B_44_7 8 N_44_8_7 = true := by decide +kernel
def U_44_8_8 : List Nat := (r 3 10++[14,15]++r 18 4++[27,29,30,31,34]++r 39 4++[45,46,47,49,51,53,54,57,58,60,61,62,67,68]++r 70 4++[82,83,84,87,90,91,96,104,106,113,115,120,143,153,161,164,166,168]++r 174 83)
def P_44_8_8 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_8_8
def N_44_8_8 : List NodeSpec := [e6 [26,285] [21,6,4,10,31,174,30],([129,1,2,3,4,124,5],[175,4,6],[]),u6 [198] [45,12,6,84,176,177],e6 [113,26,43] [4,30,9,21,178,3],u6 [121,31] [11,31,21,4,3,179,6,61],e6 [421,31] [120,179,4,9,113,3],e6 [26,34] [31,3,6,168,14,180,4,30,51],u6 [207] [3,21,15,180,6,181],([37,139,0,1,2,3,5],[6,39,4,51,182],[]),e6 [379,23] [21,4,6,3,11,183,51],u6 [107,62] [3,11,6,184,185,12,4],e6 [113,107,61] [58,87,4,12,30,3,185],([53,0,1,3,38,4,5,31],[21,12,9,186,46,6],[0]),u6 [107,61,6] [4,30,51,87,11,187,73,21],e6 [93,23] [21,188,4,31],u6 [179,182] [3,11,30,21,6,4,189],([33,7,1,2,3,4,5],[3,27,5,6,4,190],[0]),e6 [28,92,6] [191,70,11,192,193,3,21],u6 [38,62] [3,21,194,45,184,6,195,12,27],e6 [409] [12,196,6,67,40],u6 [26,45] [3,21,6,4,197,30,51],e6 [294,26] [4,3,14,12,21,198,6,51],e6 [113,216] [11,4,3,199,21,12,30],e6 [216,31] [11,199,3,143,51],e6 [216,152] [58,11,3,199,30,51],([0,1,2,3,62,5,6],[67,6,200,51],[0]),u6 [29,31] [6,3,11,45,9,31,201],([129,37,28,1,2,3,4,5],[18,3,201,14,4,12],[]),u6 [26,83,6] [4,21,202,30,9],e6 [38,63] [12,45,21,204,6,164],u6 [38,41] [21,203,11,47,19,204,205,6,206,12,15],e6 [155,124] [3,207,18,12,4,6],e6 [155,6] [51,207,14,6,12,4,21],u6 [37,50] [4,31,21,10,49,3,208,166,14,6],u6 [50,6] [51,10,4,208,70,21,68],u6 [122,50] [4,31,21,82,3,208,209,14,6],([122,0,90,2,3,4,5],[12,21,31,4,115,209,6],[0]),u6 [184] [12,39,210,3,4],u6 [133,23] [4,104,21,6,211],([80,0,1,2,4,188,5,23],[21,4,14,3,211],[]),([0,1,2,4,189,23],[57,12,4,211],[]),([290,122,1,2,3,4,5],[3,212,40,12,6],[]),u6 [122,105] [6,4,31,21,71,3,212,12],e6 [484] [11,212,106,4,54,91],u6 [169] [18,3,4,12,209,212,21,213,6],u6 [35] [3,21,4,115,58,12,214],e6 [113,143] [3,31,21,12,153,215],u6 [122,156] [12,58,21,31,216,115,11,6],e6 [442] [3,6,40,31,217,15],e6 [107,124] [3,10,4,96,6,41,11,218],([0,1,2,3,124,188,5],[3,10,6,67,218,12],[]),([92,121,1,2,3,4,5],[11,40,45,3,219,21],[]),e6 [446,122,155] [220,12,161],e6 [451] [46,3,31,221,4],e6 [458] [11,21,53,91,222],u6 [28,166,6] [12,11,223,6,9,224,3,21],e6 [311,38] [12,10,42,225,3,6],([7,1,2,3,42,4,5],[3,8,15,7,9,4,27,226,6],[0]),u6 [151] [51,106,6,227,12,21],([102,61,0,1,3,4,5,31],[30,21,228,6],[]),([0,1,3,4,104,5,31],[228,31,4,40],[0]),([61,0,1,3,38,4,5,31],[21,12,30,9,186,229,6],[0]),u6 [146,50] [21,4,72,62,208,230,231,3],([108,7,1,2,3,4,5],[4,27,7,3,8,232],[0]),e6 [475] [11,12,3,21,233],u6 [92,58] [21,57,11,12,233,3],e6 [37,429] [21,9,143,234,20,11,5,12],([7,1,2,3,38,4,5],[42,4,27,15,3,235,12,7,9,6],[0]),u6 [7,43] [3,4,21,31,236,15],u6 [62,31] [30,45,6,31,21,60,3,237],u6 [123,124] [3,238,12,9,6],([107,122,0,1,123,3,4,5],[11,31,161,12,6,239,34,4],[0]),u6 [122,192] [12,11,239,220,4,212],u6 [197,122] [21,31,12,6,240,83],e6 [146] [3,4,53,21,208,241,90],e6 [113,156] [12,21,31,153,242],u6 [156,6] [51,27,115,70,31,21,4,12,242],e6 [470] [6,31,3,243,21],e6 [494] [21,3,244,6,31],e6 [38,124] [3,12,10,245,96,42,21,218,6],e6 [28,122,31] [143,11,246,30],u6 [174] [3,209,11,247,6],([121,122,1,2,3,4,5],[3,6,45,21,11,248],[0]),e6 [265,61] [30,4,20,21,6,29,249,87],e6 [122,81,23] [46,21,250,4,30],([129,7,1,2,3,4,5],[10,106,3,4,9,251],[]),e6 [26,33,6] [187,252,253,12,3],e6 [129,29] [6,11,254,21,3,12],e6 [129,33,188] [31,255,12,6,9,3],e6 [106] [3,15,53,21,256,71]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_8_8 : checkNodesBT W_44 g_44 F_44 P_44_8_8 A_44 B_44_7 8 N_44_8_8 = true := by decide +kernel
def U_44_8_9 : List Nat := ([3,4,6,7,9,11,12,20,21,29,30,31,39,42,45,46,51,54,57,58,62,67,68,71,85,87,88,89,91,115,153,164]++r 257 21)
def P_44_8_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_8_9
def N_44_8_9 : List NodeSpec := [e6 [129,105] [6,21,3,4,30,71,257,11],u6 [183] [11,258,3,21,6,91,51],([0,1,3,105,4,5,31],[21,58,259,9],[0]),e6 [204] [67,6,39,54,21,260,71],e6 [145] [3,4,39,261,9],([74,0,1,2,9,4,5],[21,20,6,4,30,262],[0]),u6 [138] [4,263,30,67,39,6,21],e6 [61,232] [57,30,45,264,87],e6 [244,33] [4,58,115,3,21,265,51],e6 [113,28,92] [4,11,266,153,30,3],u6 [49,38] [12,21,42,267,89],e6 [386,23] [31,21,46,4,3,20,11,268],e6 [28,7] [3,46,7,12,4,31,21,269],e6 [166,180] [12,21,270],u6 [206,50] [62,11,30,21,271,31,4,6],e6 [166,29] [21,6,3,12,272,9,273,4],u6 [187] [67,6,31,21,274,9],u6 [64] [3,21,88,85,11,12,275],e6 [107,63] [11,6,164,4,276,21],u6 [162] [3,4,21,29,68,277]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_8_9 : checkNodesBT W_44 g_44 F_44 P_44_8_9 A_44 B_44_7 8 N_44_8_9 = true := by decide +kernel
def N_44_8 := N_44_8_0 ++ N_44_8_1 ++ N_44_8_2 ++ N_44_8_3 ++ N_44_8_4 ++ N_44_8_5 ++ N_44_8_6 ++ N_44_8_7 ++ N_44_8_8 ++ N_44_8_9
def B_44_8 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_8
set_option maxRecDepth 500000 in
lemma B_44_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 8 xs.toFinset) B_44_8 := by
  have hm0 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_7_ok C_44_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_7_ok C_44_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_7_ok C_44_8_2
  have hm3 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_7_ok C_44_8_3
  have hm4 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_7_ok C_44_8_4
  have hm5 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_7_ok C_44_8_5
  have hm6 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_7_ok C_44_8_6
  have hm7 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_7_ok C_44_8_7
  have hm8 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_7_ok C_44_8_8
  have hm9 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_7_ok C_44_8_9
  exact buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (hm0) hm1) hm2) hm3) hm4) hm5) hm6) hm7) hm8) hm9)
def U_44_9_0 : List Nat := (r 3 5++r 9 4++[14,15,18,20,21,22,27,29,30,31,34,39,40,45,46,51,53,54,57,58,64,65,67,70,79,85,88,91,106,107,108]++r 111 7++[119,127,132,149,162])
def P_44_9_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_9_0
def N_44_9_0 : List NodeSpec := [u6 [129,508] [30,31,20,4,14],u6 [188,116] [6,12,10,31,40],([83,0,1,3,4,5,31],[31,20,6,40],[0]),u6 [100,188] [31,21,40,9],u6 [356,26] [40,31,14,3],u6 [157] [10,4,5,15,6,45,40,31],u6 [141] [10,21,45,5,40,31,14,53,15],u6 [332] [10,31,45,12,5,53],u6 [129,83] [20,53,4,30],u6 [83,262] [39,53,30,4],u6 [83,188] [31,10,54,6,20,40,34],u6 [8,6] [57,10,51,4,9,20,6,15,22,31,21],u6 [129,43] [18,40,3,30,4,65,45,21,31,39,7,14,64],e6 [129,563] [57,65,3,12],u6 [179,92] [53,31,12,11,3,21,6,9,79,30],u6 [57,6] [10,51,12,9,6,85,27,4,29,46,21],u6 [166,57] [58,85,12,21,3],u6 [83,84] [4,88,31,20,6],u6 [179,180] [9,88,57,12,21,46,15],([0,1,3,4,152,5,31],[12,6,31,4,40,88,53],[0]),u6 [83] [39,65,45,40,31,88,57,4,6],u6 [305] [40,45,31,65,88,53,11,3,51],([88,0,1,3,4,152,5],[40,88,31,12,4,6,53],[0]),u6 [401] [45,31,39,4,6,88,40,65],u6 [189] [57,12,15,9,6,39,65,45,31,40,88,54],u6 [299] [57,40,31,39,4,6,65,45,88],u6 [115,23] [21,14,4,11,54,31,91],u6 [202,23] [31,21,54,53,40,4,20,91],([179,0,1,2,4,5,23],[54,57,12,4,6,91],[0]),u6 [294] [12,39,45,6,65,40,31,91,4,106],u6 [160] [14,5,3,45,6,40,31,53,106],u6 [377] [20,40,9,58,12,45,31,88,106],u6 [31] [20,40,31,4,58,53,45,65,88,106],u6 [385] [20,65,45,31,106,88,3,12,4],u6 [131] [45,4,85,18,9,40,31,88,106],u6 [267] [58,12,15,4,6,39,67,45,88,106],e6 [92,562] [31,58,11,107,3],u6 [92,430] [107,11,31,51,3,12],e6 [92,373] [107,11,53,31,12],e6 [92,417] [107,11,88,31,3],e6 [564,152] [4,6,31,65,108],u6 [179,152] [12,6,31,40,53,108,54],e6 [294,152] [12,6,40,31,53,108],u6 [227,152] [12,31,6,108,40,106],e6 [499,152] [31,4,12,39,108],e6 [129,125] [45,39,65,30,4,57,7,111],u6 [125,122] [85,111,21,46,6,18,11,12],u6 [8,23] [21,14,4,54,31,112,53],u6 [89,31] [20,113,6,58,40,31,88,4],u6 [31,6] [57,9,51,10,20,70,29,113,58,22,40,27,88],u6 [216] [45,40,46,115,88,53,11,3,51],u6 [328] [58,31,115,12,9,88,106],u6 [527] [58,115,31,3,12,51],([0,90,2,3,4,5],[45,116,115,31,114],[0]),u6 [116] [21,12,6,31,127,39,45,65,53,106],u6 [88,23] [21,14,91,54,4,20,34,40,132],([7,1,2,3,4,5],[5,15,149,117],[0]),u6 [7] [45,3,40,31,15,117,5,149,111],u6 [9] [21,58,40,162,20,119,53,45],([0,1,2,9,4,5],[58,57,40,20,119,162],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_9_0 : checkNodesBT W_44 g_44 F_44 P_44_9_0 A_44 B_44_8 9 N_44_9_0 = true := by decide +kernel
def U_44_9_1 : List Nat := (r 3 4++r 9 4++[14,15,18,20,21,27,29,30,31,34,39,40,45,46,53,54,57,58,62,65,67,70,85,88,91,106,108,113,115,117,120,127,132,134,150,152,153,160,164,166,168,175,185,186,201,204,209,210,212,218,221,228,229,233,238,242,270,273,276]++r 278 17)
def P_44_9_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_9_1
def N_44_9_1 : List NodeSpec := [u6 [129,57] [18,30,12,46,21,164,6,14,85,3],u6 [57,31] [53,12,4,31,58,134,45,65,6,46,21,164],u6 [26,57] [85,14,3,12,21,6,164],u6 [37,43] [5,4,10,150,21,31,11,3,14,6,166],u6 [125,37] [5,10,3,11,6,166,21,9],u6 [37,57] [5,85,10,12,21,46,6,150,14,166,11],u6 [37,33] [5,58,168,21,12,14,115,6,152],u6 [34] [58,31,115,168,6,53,106],u6 [122,6] [4,6,27,15,10,117,175,12,160,14],([129,122,1,2,3,4,5],[39,175,18,4,12,6],[0]),([0,1,3,38,4,5,31],[12,186,31,9,54,53,40],[0]),u6 [28,8] [11,46,45,58,6,4,21,201,31,120],u6 [102,28] [45,58,46,11,21,6,4,201],u6 [88,28] [45,58,46,11,21,201,31,53,34,9],u6 [28,152] [108,10,31,6,45,46,4,11,201],u6 [57,38] [12,21,31,40,45,127,65,134,204,164,6],u6 [122,43] [18,4,160,21,31,115,3,14,6,209],u6 [122,31] [20,58,113,12,9,6,209,18,14,10],u6 [166,6] [4,29,70,88,40,117,210,3,31,21],u6 [88,122] [20,12,160,58,11,21,31,4,212,53,6],u6 [102,122] [40,53,6,39,3,14,4,31,21,212,12,175],u6 [124] [3,10,175,67,18,218,45,53,6,40,31],u6 [122,124] [3,218,175,18,12,6],u6 [327] [45,4,221,46,40,31,88,106],([102,0,1,3,4,5,31],[40,31,53,228,4,6,88],[0]),u6 [107,61] [11,31,30,4,58,229,185],u6 [61,8] [11,45,30,21,229,3,20],u6 [179,61] [45,57,30,21,3,229],u6 [92,57] [45,85,11,65,12,39,31,3,21,233],u6 [122,123] [18,40,31,238,12,6,14],u6 [123] [20,31,18,45,238,53,40,27],u6 [156] [58,31,242,115],u6 [180] [6,57,270,15,9,45,65,40,31,88],u6 [53,166] [45,58,11,3,65,21,6,273],u6 [125,166] [45,58,11,21,4,65,273],u6 [28,166] [45,58,46,11,3,4,12,21,201,273],u6 [107,57] [58,11,31,6,164,21,4,276],e6 [125,107] [58,31,11,21,4,276],u6 [113,114] [4,54,57,9,10,153,29,278],u6 [113,38] [12,46,21,31,40,53,280,153,29,127],u6 [114] [21,279,57,4,278,45,65,280,40,31],u6 [113,28] [30,46,4,9,5,14,58,31,29,153,12,280,201],e6 [113,555] [53,12,31,9,281],u6 [113,33] [12,58,21,31,15,282,168],u6 [232] [12,57,39,31,4,283,45,65,40],u6 [113,232] [53,12,40,153,282,9,283],e6 [113,556] [53,30,65,4,284],e6 [179,565] [53,12,31,9,285],u6 [179,236] [53,21,40,9,285],e6 [179,557] [53,30,65,21,6,285],u6 [236] [21,12,57,39,31,9,45,286,88,40],u6 [139,23] [6,4,21,46,54,53,88,9,287,91],u6 [113,23] [4,15,57,30,9,153,288],u6 [102,23] [21,14,54,4,40,91,10,288,132],u6 [139] [67,6,4,45,65,40,31,288,106,287,289],u6 [202] [31,45,54,21,20,290,4,12,291],u6 [179,6] [9,12,292,6,21,15],e6 [179,283] [39,53,30,9,293],u6 [283] [53,45,3,65,40,31,30,292,88,67,293,12,9],u6 [43,23] [21,14,4,115,54,40,91,294,45,62]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_9_1 : checkNodesBT W_44 g_44 F_44 P_44_9_1 A_44 B_44_8 9 N_44_9_1 = true := by decide +kernel
def U_44_9_2 : List Nat := ([3,4,6,7]++r 9 4++[14,15,18,20,21,27,29,30,31,34,39,40,45,46,51,53,54,57,58,62,65,67,70,84,85,88,91,102,106,107,108,111,113,114,116,120,124,131,150,153,160,164,168,175,179,201,209,245,282,288]++r 294 41)
def P_44_9_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_9_2
def N_44_9_2 : List NodeSpec := [u6 [53,23] [21,14,46,4,53,45,91,294,6,3,10,62,88],e6 [125,23] [21,14,57,91,54,4,111,85,294,45,62],u6 [33,23] [31,14,21,4,53,58,12,294,168],u6 [57,23] [53,14,21,4,30,6,46,294,164],u6 [81,23] [21,294,4,295,45,296,131],u6 [23,6] [6,4,15,124,51,298,70,21,46,54,91],u6 [80,23] [91,21,102,297,31,4,298,299,3],u6 [245,188] [21,9,15,300],u6 [224,188] [21,10,9,31,40,300],u6 [254,188] [21,10,31,6,11,40,300],u6 [245] [39,65,45,31,40,301,15,57,12,9,6,21],([0,1,2,4,188,5,23],[21,6,302,9,54,288,53],[0]),u6 [100] [31,39,45,53,21,12,303,304],u6 [257,188] [21,10,46,6,11,45,305,300],u6 [188,247] [21,9,306,305,15,53],e6 [94,188] [21,10,14,6,67,306,300],u6 [95,188] [21,46,3,31,9,306,67,307],u6 [95] [67,45,3,65,40,31,9,53,306,307,308],u6 [83,6] [53,4,9,30,309,6,31],u6 [262] [53,45,3,65,31,30,88,67,309,4],u6 [37,83] [67,6,10,31,20,14,12,309,150],e6 [83,558] [30,65,31,6,310],u6 [88,53] [45,58,11,65,21,6,88,4,53,310],u6 [125,88] [45,58,65,11,21,4,310],e6 [125,83] [58,57,30,4,310],u6 [88,113] [12,53,9,311],u6 [88,6] [4,10,51,29,70,9,88,12,57,312,11,58,27],u6 [88,26] [40,3,21,14,31,53,312,34,9],u6 [129,88] [40,12,107,11,4,312,30],u6 [88,188] [21,10,40,9,34,313],u6 [279] [21,58,12,39,9,45,91,313,88,15],e6 [88,179] [31,12,53,9,313],([88,0,1,3,38,4,5],[40,31,21,58,12,9,313,53],[0]),([88,83,0,1,3,4,5],[20,40,57,31,34,6,58,310,314],[0]),([88,83,0,1,3,4],[20,40,58,310,31,314,34],[0]),u6 [271] [40,45,11,65,3,67,312,107,315,316,12,51],u6 [113,31] [53,12,9,153,282,317],u6 [89] [67,6,20,4,45,65,31,106,317],u6 [429] [31,45,54,21,20,318,9,319,91],u6 [179,33] [31,58,12,168,21,6,9,320],u6 [179,31] [53,12,9,21,320,31],u6 [90,31] [20,31,4,113,321,114,58],([0,90,2,3,4,5,31],[20,31,4,113,321,114,116],[0]),u6 [28,31] [113,20,31,53,46,9,11,321,120,201],u6 [53,31] [113,31,4,53,321,11,9,21,6,3,179,46],([275,0,2,3,4,5,31],[58,20,31,321,45,4,322],[0]),u6 [277] [58,57,40,323,20,4,6,67,45,88],e6 [559,188] [21,6,9,305,45,324],u6 [102,179] [40,53,21,14,6,10,325,326],u6 [288] [58,327,40,15,4,6,45,91,106],u6 [292] [39,65,45,31,328,57],u6 [227] [57,12,31,4,6,39,65,45,40,54,329],u6 [129,6] [4,29,57,9,88,51,330,7,18],u6 [505,129] [20,3,12,330],u6 [129,341] [30,107,40,4,330],u6 [122,152] [12,6,31,40,108,53,331,175,14],e6 [456] [91,332,65,45,31,40,333,106,88,14,21,3,4],u6 [122,23] [4,46,21,31,14,57,12,6,298,334,209,160,10],u6 [122,188] [6,31,21,88,53,306,334,160,12],u6 [122,38] [12,46,21,31,40,53,39,245,334,209,84,6]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_9_2 : checkNodesBT W_44 g_44 F_44 P_44_9_2 A_44 B_44_8 9 N_44_9_2 = true := by decide +kernel
def U_44_9_3 : List Nat := (r 3 5++r 9 4++[14,15,18,20,21,27,29,30,31]++r 39 4++[45,46,51,53,57,58,65,67,70,79,81,85,87,88,89,91,104,106,107,108,111,113,115,117,125,127,135,139,150,153,160,161,162,164,166,168,171,178,187,201,207,209,239,269,280,288,292,298,305,312,321,330]++r 334 39)
def P_44_9_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_9_3
def N_44_9_3 : List NodeSpec := [u6 [92,6] [4,51,29,70,6,117,81,3,12,11,336,31],u6 [92,188] [31,21,6,9,14,3,79,11,336,12,51],e6 [560] [335,31,336,106,53,5],u6 [155] [21,57,337,18,45,334,40,31,108,207],u6 [122,155] [337,18,21,207,12,334,160,161,6],u6 [129,188] [6,21,9,31,106,3,10,330,4,7,12,339],u6 [456,129] [14,3,4,91,339,330],e6 [129,179] [14,53,12,9,339],u6 [129,23] [21,4,46,91,30,298,7,339],u6 [457] [30,12,338,21,45,65,40,31,91,339,88,9,15],u6 [129,8] [30,20,4,339],e6 [129,457] [30,339,91,9,330],u6 [37,31] [4,113,6,58,12,340,20,10,9,166,5,14,150],u6 [129,33] [115,58,3,31,12,7,14,341],u6 [491,122] [31,18,12,160,21,342,4,6],u6 [37,23] [4,21,6,46,31,104,14,53,67,10,298,343,166,150,20,288],u6 [37,8] [6,20,10,67,31,21,150,343],u6 [37,179] [67,6,10,31,21,150,343,292],u6 [57,188] [21,10,6,85,88,29,45,65,164,344],u6 [38,6] [12,125,15,51,10,4,127,345,70,27,21,46,9,53,31],u6 [37,38] [127,21,46,89,31,67,10,12,15,345,150,343,166,42,6,20],u6 [39,38] [31,21,12,39,127,3,139,346],u6 [39] [107,45,3,65,12,88,67,53,20,345,346,347,111,51],u6 [88,37] [67,11,10,12,166,20,14,150,6,58,21,348,9,312],e6 [129,107] [3,4,31,350,58,11,7,339],u6 [107,6] [4,51,29,70,15,40,31,187,171,350,11],u6 [107,122] [11,31,160,3,209,12,6,4,239,334,350],u6 [37,107] [67,11,10,4,58,41,343,349,150,166,6,350],u6 [188,31] [21,6,31,9,20,10,58,113,305,40,351],u6 [8,188] [21,10,6,20,40,351,162],u6 [33,6] [51,27,10,29,15,6,4,58,352,12,115,31,21,168],u6 [94,26] [10,3,21,14,353],u6 [336,26] [31,3,14,353,21],u6 [381,26] [46,14,3,21,353],u6 [456,26] [53,3,21,14,353],u6 [154,26] [91,3,21,14,353],u6 [129,102] [3,40,4,6,11,21,31,7,14,330,354],([129,37,1,2,3,4,5],[3,354,53,4,9,39,10,330,6],[0]),u6 [427] [3,354,67,4,12,15,45,65,40,31],u6 [512,129] [10,3,4,9,106,354,330],e6 [129,113] [10,53,12,4,9,354],u6 [129,152] [12,4,31,330,9,3,354],u6 [129,427] [30,354,106,53,330,4],u6 [209] [57,10,88,330,5,12,355,45,31,40],u6 [503] [356,31,40,357,53,5,358,12],u6 [26,6] [9,51,70,27,4,6,14,3,15,21,359,31],u6 [113,26] [67,3,14,4,9,30,21,31,15,153,12,178,280,359],u6 [309,38] [12,31,21,135,360,40,27,361,6],u6 [324] [45,40,57,115,11,3,362,18,363,6],u6 [367] [15,45,40,31,21,29,364,9,365,91],u6 [102,26] [40,14,21,6,4,366,359],u6 [290] [40,45,11,3,366,53,5,367,368],u6 [341] [30,369,31,45,65,4,88,40],u6 [37,28] [5,46,201,31,150,11,166,6,370,343],u6 [28,6] [51,70,27,4,29,6,46,269,15,9,370,58,31,201],u6 [61,31] [20,31,30,40,113,4,53,321,87,21,46,371],u6 [129,53] [3,45,21,46,10,4,7,372,9],u6 [385,129] [40,20,3,372,30,9],u6 [129,28] [45,46,30,31,7,201,12,4,370,372,339,11,9],e6 [561,129] [57,30,18,372,330,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_9_3 : checkNodesBT W_44 g_44 F_44 P_44_9_3 A_44 B_44_8 9 N_44_9_3 = true := by decide +kernel
def U_44_9_4 : List Nat := (r 3 5++r 9 4++[14,15,18,20,21,27,29,30,31,34,39,40,45,46,47,51,53,54,57,58,65,67,68,73,77,79,85,87,88,91,106,107,108,111,112,113,115,120,127,128,133,134,136,153,155,165,168,195,204,215,229,236,292,294,298,299,305,306,310,331,345,359]++r 372 51)
def P_44_9_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_9_4
def N_44_9_4 : List NodeSpec := [u6 [129,31] [58,20,12,39,9,7,372],u6 [31,23] [21,31,4,14,373,294,113,112,40,54,91],u6 [430] [57,20,11,65,45,40,31,6,374],u6 [61,38] [21,45,31,12,345,375,229,30,195],u6 [125,38] [21,45,31,127,111,85,4,12,375,204,9,6],u6 [40,38] [21,375,115,47,12,134,204,31,27],u6 [43,6] [4,51,29,68,236,376,88,40,45,65,31,21],u6 [26,33] [31,58,14,3,21,168,12,377],u6 [26,43] [40,3,14,21,4,376,377],u6 [57,152] [12,6,31,40,108,45,65,134,378,46,21],u6 [102,57] [58,85,11,21,6,378],u6 [172] [14,18,12,45,6,31,40,379],u6 [54] [45,3,380,15,4,40,31,6,91,106],u6 [152,23] [21,12,6,31,4,381,108,54,91],u6 [26,152] [31,108,381,6,14,4,3,10,21,359],e6 [125,31] [20,57,40,9,11,111,382,45,120],u6 [125,152] [4,6,45,31,9,21,382,383],e6 [125,113] [29,57,4,30,383],u6 [126] [45,4,30,15,383,39,67,40,31],u6 [125,102] [45,58,11,21,6,383],u6 [166,23] [21,4,40,91,298,384],u6 [166,188] [21,6,40,9,306,384,4,12],u6 [179,166] [40,53,12,21,3,292,384],u6 [495] [45,12,46,39,385,6,31,40],u6 [61,23] [57,21,4,45,91,298,294,229,386],u6 [167] [21,58,387,45,384,388,53,12,91],([0,1,2,38,4,5,23],[21,12,389,4,54,40,53],[0]),e6 [113,481] [39,53,30,4,390],u6 [112,38] [12,21,136,31,127,27,128,391,6],u6 [112] [67,6,128,45,65,31,127,53,106,133,391],u6 [403] [45,392,31,53,30,27,393],u6 [125,6] [4,10,57,9,111,394,29,45,65],u6 [125,26] [45,3,14,21,57,6,394,377,9],u6 [479] [53,395,31,88,18],u6 [61,152] [12,31,108,21,4,30,381,331,397,46,87,51],u6 [61,188] [21,6,45,9,306,397,229,57],u6 [102,61] [45,58,11,21,397,30,4,6],u6 [61,6] [57,4,51,27,45,29,39,397,73,46,21],u6 [113,61] [57,30,21,12,153,396,397],u6 [437] [3,40,12,398,399,45,65,4,400,53,106],u6 [266] [21,401,57,31,4,45,402,88,54],u6 [356] [403,65,45,31,88,53,3,12,21,51],u6 [53,26] [45,3,14,21,6,404,377],u6 [121] [45,40,11,115,107,3,53,404,165,405],u6 [83,23] [4,57,31,20,406,58,34],u6 [83,61] [30,20,21,46,3,406,57,310,87],u6 [53,83] [6,57,40,10,3,21,46,406,155,407,310],u6 [28,92] [45,31,46,11,3,12,79,408],u6 [53,92] [45,107,11,39,3,77,408,155,21],u6 [373] [11,31,409,410,45,40,9,91,88,106],u6 [352] [14,4,411,45,40,31,88,106,91],u6 [88,61] [45,58,11,39,21,20,4,53,310,30,412],u6 [363] [14,31,45,21,413,53,12,27,414],u6 [396] [45,31,39,415,12,53,27],u6 [43,188] [21,10,4,6,115,40,9,416,305],u6 [94] [417,31,40,10,14,106,53,5,21,6],u6 [143] [11,31,418,45,419,91,53,215],u6 [33,122] [45,58,18,14,6,12,21,31,420],u6 [417] [11,31,3,421,45,65,88,6,53,106],u6 [80] [91,45,3,65,40,31,298,67,299,422,111,51]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_9_4 : checkNodesBT W_44 g_44 F_44 P_44_9_4 A_44 B_44_8 9 N_44_9_4 = true := by decide +kernel
def U_44_9_5 : List Nat := (r 3 5++r 9 4++[14,15,18,20,21,27,29,30,31,34,39,40,45,46,51,53,54,57,58,65,67,77,85,88,91,106,107,108,111,113,115,120,127,141,154,160,168,184,197,201,202,208,209,229,268,282,298,305,309,320,326,331,334,339,344,345,360,361]++r 375 4++[397,400,406,407,408,416]++r 423 67)
def P_44_9_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_9_5
def N_44_9_5 : List NodeSpec := [u6 [63] [45,85,423,6,29,378,40,31],u6 [125,92] [45,11,31,3,46,21,4,5,53,77,408,424],u6 [26,31] [31,113,21,20,425,14,426,377,12,9,10],u6 [119,38] [12,21,40,53,127,15,141,427,31,4],u6 [119] [12,39,45,4,40,88,106,31,141,427],u6 [26,83] [31,14,3,406,21,4,6,202,30,309,34,428],u6 [113,43] [5,30,115,4,53,45,21,429,282,416],u6 [481] [67,45,3,65,40,31,30,430,53,4,12,9],u6 [26,8] [31,21,14,6,4,20,30,431],u6 [244] [4,6,45,65,40,31,106,432,433],u6 [244,188] [9,10,6,53,21,432,433,106],u6 [28,122] [18,46,3,160,11,12,6,209,7,31,434,334],u6 [62] [45,3,30,435,184,40,31,397,53,106],u6 [84] [6,57,4,31,436,67,45,65,88],u6 [113,166] [40,53,12,4,430,437,3,400],u6 [150] [53,45,31,40,12,438,439,440,6],u6 [137] [53,45,40,88,441,20,4,6],u6 [129,38] [12,21,31,127,15,345,339,7,4,442],u6 [282] [40,45,20,88,67,53,39,11,58,3,443,51],u6 [154] [53,444,31,40,445,88,18,3,12,21],u6 [125,188] [21,6,45,9,305,446],e6 [125,179] [46,57,21,30,6,446],u6 [285] [57,40,447,20,6,65,45,448],u6 [125,8] [57,449,11,21,446,6,120],u6 [88,57] [58,85,449,45,12,21,4,53],u6 [182] [40,45,3,11,67,53,376,450,451,452,51],u6 [179,43] [21,115,40,4,57,6,9,320,454],u6 [50] [45,40,31,21,208,154,453,454,53,91],u6 [29] [455,46,201,6,40,31,53,106],u6 [45] [45,40,456,197,416,4,67,6,53,106],u6 [342] [45,40,9,457,458,54,91,88,106],u6 [211] [58,31,115,459,6,53],u6 [105] [21,58,40,31,460,461,326,45,53,91,15],u6 [53,122] [18,3,39,6,65,21,209,11,462],u6 [322] [45,21,30,39,57,9,6,463,40,31,91,446,88,15],u6 [28,83] [31,46,406,6,4,464,11,30,407,34],u6 [67] [45,3,465,46,21,40,31,466,53,91,15],u6 [386] [45,20,65,39,67,31,467,268,3,12,111,51],u6 [144] [45,21,30,468,469,40,31,108,470,229,53,91],u6 [53,8] [11,45,21,58,6,65,471,120],u6 [53,38] [21,45,31,12,375,3,127,11,471,6],u6 [53,179] [45,21,57,6,10,3,320,471],u6 [53,107] [45,58,31,11,4,65,6,88,471],u6 [348] [45,40,85,107,88,67,39,53,11,12,3,472,51],u6 [265] [31,45,473,20,29,12,4],u6 [326] [45,31,115,474,53,12,40,27],u6 [58] [45,21,85,475,53,344,40,31,108,29],u6 [415] [45,31,3,115,476,53],u6 [466] [45,3,85,53,29,477,12,6,31,40,65,88],u6 [33,188] [31,10,21,6,58,9,168,478,12],u6 [394] [39,65,45,31,57,479,6],u6 [499] [45,3,65,31,12,53,20,331,4,480],u6 [453] [53,481,65,45,40,88,482,6,4],u6 [309] [57,12,31,360,39,361,6,483,65,45,40],u6 [307] [20,39,31,21,484,45,65,4,88,106],u6 [148] [58,485,31,4,45,88,106],u6 [92,23] [31,21,4,53,91,298,486,11,40,12,3,51],u6 [303] [58,487,31,4,6,45,40,53,106],([107,0,1,3,4,5,31],[40,31,58,488,4],[0]),u6 [189,188] [21,6,489,15,9,31,88,54,106]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_9_5 : checkNodesBT W_44 g_44 F_44 P_44_9_5 A_44 B_44_8 9 N_44_9_5 = true := by decide +kernel
def U_44_9_6 : List Nat := ([3,4,9,11,12,21,29,31,45,53,57,58,91,153,280,336,430]++r 490 6)
def P_44_9_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_9_6
def N_44_9_6 : List NodeSpec := [u6 [113,107] [4,31,11,58,29,153,12,490,280,491],u6 [113,92] [12,11,31,57,153,9,430,492,3,336],u6 [153] [31,45,53,91,21,493,494,4,495]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_9_6 : checkNodesBT W_44 g_44 F_44 P_44_9_6 A_44 B_44_8 9 N_44_9_6 = true := by decide +kernel
def N_44_9 := N_44_9_0 ++ N_44_9_1 ++ N_44_9_2 ++ N_44_9_3 ++ N_44_9_4 ++ N_44_9_5 ++ N_44_9_6
def B_44_9 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_9
set_option maxRecDepth 500000 in
lemma B_44_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 9 xs.toFinset) B_44_9 := by
  have hm0 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_8_ok C_44_9_0
  have hm1 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_8_ok C_44_9_1
  have hm2 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_8_ok C_44_9_2
  have hm3 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_8_ok C_44_9_3
  have hm4 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_8_ok C_44_9_4
  have hm5 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_8_ok C_44_9_5
  have hm6 := checkNodesBT_mem (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_8_ok C_44_9_6
  exact buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (hm0) hm1) hm2) hm3) hm4) hm5) hm6)
def U_44_10 : List Nat := ([5,10,14,15,18,20,29,31,39,40,45,53,54,57,58,65,85,88,91,106,115,117,127,162,168,175,201,229,280,282,288,292,294,298,305,306,309,311,312,313,317,320,321,325,326,331,334,336,339,343,344,345,350,354,359,366,370,372]++r 375 4++[383,384,394,397,400,404,407,408,416,430,446,454,471,491,496,497,498])
def P_44_10 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_10
def N_44_10 : List NodeSpec := [u6 [6] [29,117,15,88,106,39,45,65,40,54],u6 [33] [45,39,65,54,40,115,31,168],u6 [23] [298,294,54,288,91,45,40,106],u6 [188] [306,305,54,88,45,40,106],u6 [88] [40,65,45,58,312,313,311],u6 [31] [20,321,40,31,317,39,45,65,54,106],u6 [179] [53,292,45,320,40,54,325],u6 [122] [39,45,53,65,18,40,334,175],u6 [37] [88,45,65,5,40,10,39,106,343],u6 [102] [40,65,45,88,58,366,326],u6 [28] [45,40,65,370,54,201],u6 [129] [39,45,372,40,339,354,106],u6 [38] [345,375,40,31,54,127,45],u6 [26] [54,45,14,377,40,39,359],u6 [57] [45,39,85,344,378,53,40,65],u6 [61] [65,39,40,45,229,397],u6 [166] [40,39,65,45,384,58,400],u6 [92] [40,45,31,408,39,54,336],u6 [113] [53,430,45,282,40,280,106,88],u6 [125] [45,40,65,394,446,383],u6 [43] [40,45,454,376,416,65],u6 [53] [45,40,65,404,471,88],u6 [107] [40,65,45,54,58,350,491],u6 [8] [58,57,40,39,162,20,496,65,45,54],u6 [152] [331,497,40,31,88,45,54,106],u6 [83] [53,309,45,407,31,54,498,40]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_10 : checkNodesBT W_44 g_44 F_44 P_44_10 A_44 B_44_9 10 N_44_10 = true := by decide +kernel
def B_44_10 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_10
set_option maxRecDepth 500000 in
lemma B_44_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 10 xs.toFinset) B_44_10 :=
  buildBucketsBT_sound (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_9_ok C_44_10
def U_44_11 : List Nat := [39,54,65,88]
def P_44_11 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 U_44_11
def N_44_11 : List NodeSpec := [u6 [] [39,65,54,88]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_11 : checkNodesBT W_44 g_44 F_44 P_44_11 A_44 B_44_10 11 N_44_11 = true := by decide +kernel
def B_44_11 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_11
set_option maxRecDepth 500000 in
lemma B_44_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 11 xs.toFinset) B_44_11 :=
  buildBucketsBT_sound (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_10_ok C_44_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_44_ok : forestRootCheck r_44 g_44 [(VAR 0,22,23),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,7,23),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_44_in : bucketContainsBT B_44_11 r_44 = true := by decide +kernel
lemma low_44 : Lower r_44 g_44 12 := lower_of_forestBT root_44_ok B_44_11_ok root_44_in

def g_orig := 0xfeeaeae8eea8e0a0
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,3),(2,4),(3,4)]) (by decide +kernel) low_44
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808424 * 2 ^ 32 + 4004044960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.or,[3,0]⟩,⟨.or,[0,2]⟩,⟨.or,[3,2]⟩,⟨.and,[6,2]⟩,⟨.and,[5,7]⟩,⟨.and,[8,0]⟩,⟨.or,[1,11]⟩,⟨.and,[6,4]⟩,⟨.or,[9,10]⟩,⟨.and,[12,14]⟩,⟨.or,[10,12]⟩,⟨.and,[16,13]⟩,⟨.or,[15,17]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_45570

open PEqualNP.Outside.L_meta_45570 in
theorem PEqualNP.Outside.L_meta_45570 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4004044960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4004044960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
