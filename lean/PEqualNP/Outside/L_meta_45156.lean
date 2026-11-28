import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45156
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 256
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
lemma bin_lt (d a b : Nat) (ha : a < 2^256) (hb : b < 2^256) : bin d a b < 2^256 := by
  have h1 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x &&& y) < 2^256 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ||| y) < 2^256 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ^^^ y) < 2^256 := fun x y hx hy =>
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
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^256 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^256 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^256 ∧ (w.getD i swZero).2.testBit 0 = false := by
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
    (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
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
lemma normPack_lt (f : Wire) : normPack f < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).isLt
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 256 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 256 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^256) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
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
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
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
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false) :
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
  ⟨((r.val &&& (255 ^^^ z)) ||| o) % 256, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 256
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 256 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^256) (hb : b < 2^256) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 256 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^256) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^256 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^256 := hS a (by simp)
    have hblt : b < 2^256 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^256 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^256 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^256 := by
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
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^256) (hGb0 : G.testBit 0 = false)
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
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
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
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | 7 => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | _ => 0
def ALL256 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 256, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL256 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 8) (hj : j < 8) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) (hw : w < 2^256) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 8 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL256 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
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
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) : swapWord i j w < 2^256 := by
  have hi : i < 8 := by omega
  have h1 : (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^256 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^256 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^256 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^256 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^256 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) (hw : w < 2^256) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 8)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^256) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^256 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
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
    (hT : T < 2^256) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^256) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^256 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^256 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 256
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
  (List.range 8).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr := ((r &&& (255 ^^^ z)) ||| o) % 256
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
  by_cases hr : r < 256
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 256) (ho : o < 256) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 256 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h255 : ((r.val &&& (255 ^^^ z)) ||| o) < 256 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (255 ^^^ z)) < 256 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 8) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (255 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h255
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 8
    · have h7 : (255 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 256) && decide (s < 256) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL256 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL256]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 256 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^256) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^256 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^256) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^256 ∧ a.testBit 0 = false := by
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
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^256)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256 := by
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
lemma var_testBit (i : Fin 8) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by revert i r; decide +kernel
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
  if z.testBit i then ALL256 ^^^ VAR i else if o.testBit i then VAR i else ALL256
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&&
  fastBitMask z o 6 &&& fastBitMask z o 7
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 8) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL256.testBit r.val = true := by
    simp only [ALL256]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 256 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 256) (ho : o < 256) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
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
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 7 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 8) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 8, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 8
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 8
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩, (hbit 7 (by decide)).mp (h 7 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 256 ≤ r := by omega
      have ha : ALL256 < 2^256 := by decide
      have hv : VAR i < 2^256 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^256; decide
      have hlt_m : fastBitMask z o i < 2^256 := by
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
    (hT : T < 2^256)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^256)
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
    have hinv_w : ∀ x : Nat, x < 2^256 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 256
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^256 := by
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
        let okAB := !miss.contains a && !miss.contains b
        if k + c.paid + 1 < base && okAB then true
        else
          let zIn := c.pm.contains m || c.pm.contains (c.dom ^^^ m)
          if zIn then true
          else decide (k + c.paid + 1 < base) && okAB
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
          cases hpm : (c.pm.contains m || c.pm.contains (c.dom ^^^ m))
          · simp only [hpm, Bool.false_eq_true, ↓reduceIte] at hcut
          · simp only [Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or]
            exact ⟨by omega, trivial⟩
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 z.1 ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  if n > cap + 1 then true else
  let z := dbin d a b
  if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
    if n > cap then go false false
    else if n == cap then go false false && go true false && go false true
    else go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^256) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^256)
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
  have hltc : ∀ x ∈ child, x < 2^256 := by
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
  dsimp only [dbin] at test
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
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^256) (out : T ∉ ws.map Prod.fst)
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
      have hnz_b : (bin d' x.1 y.1 == 0) = false := beq_false_of_ne hnz'
      have hfr_b : (ws.any (fun v => v.1 == bin d' x.1 y.1)) = false := by
        rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
        exact hfr' ((beq_iff_eq.mp heq) ▸ List.mem_map_of_mem hv)
      by_cases hlen : 1 + (ws.length - (if k1 then 0 else 1) - (if k2 then 0 else 1)) > cap
      · unfold evalMoveBT; simp [hlen]
      · unfold testPairBT at ht
        dsimp only [dbin] at ht
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
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^256 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256)
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
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^256 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^256 :=
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
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
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
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
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
lemma obs_all256_xor (G : Nat) : obs (ALL256 ^^^ G) = invW (obs G) := by
  funext r
  have hall : ALL256.testBit r.val = true := by
    simp only [ALL256]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 256 r.val
  simp only [obs, invW, Nat.testBit_xor, hall, Bool.true_xor]
lemma lower_slice_flip {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^256) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G ∨ renameW f T = ALL256 ^^^ G)
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
      (obs_renameW f T).symm.trans ((congrArg obs heq).trans (obs_all256_xor G))
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
    (fixWord z o T == G || fixWord z o T == ALL256 ^^^ G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL256))
lemma lift_of_f {z o roots T other G essPairs L} (ok : liftCheckF z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheckF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G ∨ renameW (fixRow z o) T = ALL256 ^^^ G := by
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
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL256]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 256 r'.val |> fun e => by simpa [this] using e⟩
def sliceDirectCheckF (z o : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 256) && decide (o < 256) && ((z &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord z o T == qGoal || fixWord z o T == ALL256 ^^^ qGoal) &&
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
      by rw [← obs_renameW, ← fixWord_eq_renameW, heq, obs_all256_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← fixWord_eq_renameW, heq, obs_all256_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)
def identRow (u v : Nat) (r : Row) : Row :=
  if r.val.testBit u == r.val.testBit v then r
  else ⟨(r.val ^^^ (1 <<< v)) % 256, Nat.mod_lt _ (by decide)⟩
def identDom (u v : Nat) : Nat := ALL256 ^^^ (VAR u ^^^ VAR v)
def identWord (u v w : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr := if r.testBit u == r.testBit v then r else (r ^^^ (1 <<< v)) % 256
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma identWord_eq_renameW (u v w : Nat) : identWord u v w = renameW (identRow u v) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold identWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 256
  · rw [testBit_renameW (identRow u v) w ⟨r, hr⟩]
    simp only [List.mem_range, hr, decide_true, Bool.true_and, identRow]
    split <;> rfl
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma identDom_identRow (u v : Nat) (hu : u < 8) (hv : v < 8) (r : Row) :
    (identDom u v).testBit (identRow u v r).val = true := by
  revert r
  interval_cases u <;> interval_cases v <;> decide +kernel
def sliceIdentCheck (u v : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (u < 8) && decide (v < 8) &&
    checkProper qGoal && checkRoots qRoots &&
    (identWord u v T == qGoal || identWord u v T == ALL256 ^^^ qGoal) &&
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
      by rw [← obs_renameW, ← identWord_eq_renameW, heq, obs_all256_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← identWord_eq_renameW, heq, obs_all256_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)
def mkBase (pos neg : List Nat) (rs : List Nat) : List Decor :=
  rs.map fun w => (w, projBits pos w, projBits neg w)
lemma mkBase_ok {pos neg rs} (hR : checkRoots rs = true) :
    ∀ x ∈ mkBase pos neg rs, faithful pos neg x ∧ x.1 < 2^256 := by
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
lemma sw_extract_full6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^256) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^256 ∧ out.2.testBit 0 = false := by
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
    by_cases hr : r < 256
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
lemma replace_of_lower6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
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
def d (x : Nat) : Nat := x * 0x1000000000000000100000000000000010000000000000001
def r (a n : Nat) : List Nat := List.range' a n
def b6 : List Nat := [0,1,2,3,4,5]
def b5 : List Nat := [0,1,2,3,4]
def u6 (w p : List Nat) : NodeSpec := (b6 ++ w, p, [0])
def e6 (w p : List Nat) : NodeSpec := (b6 ++ w, p, [])
def a6 (w p a : List Nat) : NodeSpec := (b6 ++ w, p, a)
def u5 (w p : List Nat) : NodeSpec := (b5 ++ w, p, [0])
def e5 (w p : List Nat) : NodeSpec := (b5 ++ w, p, [])
def a5 (w p a : List Nat) : NodeSpec := (b5 ++ w, p, a)

def g_0 := (d 0xe8e8e8e8e8e8e8e8)
def r_0 : List Nat := varsOf 7
def p_0 : List Nat := [3,3,5,5,6,6]
def q_0 : List Nat := [2,1,4,1,4,2]
def F_0 : Nat := fullMask 6
set_option maxHeartbeats 0 in
lemma gp_0 : goodPairs g_0 p_0 q_0 := goodPairs_of (by decide +kernel)
def W_0 : BT Decor := buildWiresBT 2 (mkBase p_0 q_0 r_0) []
lemma W_0_ok : btAll (fun x => faithful p_0 q_0 x ∧ x.1 < 2^256) W_0 := buildWiresBT_faithful (mkBase_ok (by decide))
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
def g_1 := (d 0xfee8fee8fee8fee8)
def r_1 : List Nat := varsOf 15
def p_1 : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12]
def q_1 : List Nat := [2,1,4,1,4,2,8,1,8,2,8,4]
def F_1 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_1 : goodPairs g_1 p_1 q_1 := goodPairs_of (by decide +kernel)
def W_1 : BT Decor := buildWiresBT 4 (mkBase p_1 q_1 r_1) [(1,0,1),(1,4,2),(2,5,3),(1,1,2),(1,3,1),(1,3,2),(2,4,3),(1,3,0)]
lemma W_1_ok : btAll (fun x => faithful p_1 q_1 x ∧ x.1 < 2^256) W_1 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_1 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2),(1,3)]]
def A_1 : BT (List (Nat × Nat)) := btOfList 4 al_1
set_option maxHeartbeats 0 in
lemma A_1_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_1 = g_1) A_1 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_1_0 : Slice r_1 g_1 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_1 : Slice r_1 g_1 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_2 : Slice r_1 g_1 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
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
def N_1_3 : List NodeSpec := [([6,0,1,2],[],[]),([0,7,8,9],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_3 : checkNodesBT W_1 g_1 F_1 P_1_3 A_1 B_1_2 3 N_1_3 = true := by decide +kernel
def B_1_3 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_3
set_option maxRecDepth 500000 in
lemma B_1_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 3 xs.toFinset) B_1_3 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_2_ok C_1_3
def U_1_4 : List Nat := [1,2,3]
def P_1_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_4
def N_1_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([10,0,1,2,3],[],[]),([0,1,2,11,8],[1,3],[10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_4 : checkNodesBT W_1 g_1 F_1 P_1_4 A_1 B_1_3 4 N_1_4 = true := by decide +kernel
def B_1_4 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_4
set_option maxRecDepth 500000 in
lemma B_1_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 4 xs.toFinset) B_1_4 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_3_ok C_1_4
def U_1_5 : List Nat := (r 0 4)
def P_1_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_5
def N_1_5 : List NodeSpec := [([0,1,4,2,3],(r 0 4),[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_5 : checkNodesBT W_1 g_1 F_1 P_1_5 A_1 B_1_4 5 N_1_5 = true := by decide +kernel
def B_1_5 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_5
set_option maxRecDepth 500000 in
lemma B_1_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 5 xs.toFinset) B_1_5 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_4_ok C_1_5
def U_1_6 : List Nat := (r 0 4)
def P_1_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_6
def N_1_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,4,6,8,11])]
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
def g_2 := (d 0xfe80fe80fe80fe80)
def r_2 : List Nat := varsOf 15
def p_2 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14]
def q_2 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6]
def F_2 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_2 : goodPairs g_2 p_2 q_2 := goodPairs_of (by decide +kernel)
def W_2 : BT Decor := buildWiresBT 5 (mkBase p_2 q_2 r_2) [(0,2,3),(1,2,3),(3,4,5),(0,1,2),(1,1,2),(3,7,8),(2,0,3),(3,0,3),(1,0,3),(3,2,12),(1,1,3),(0,0,14),(0,0,3),(1,16,2),(3,4,0),(2,0,2),(3,0,2),(2,2,1),(3,21,0),(2,0,1),(1,23,2),(0,0,1),(1,0,1),(3,2,3)]
lemma W_2_ok : btAll (fun x => faithful p_2 q_2 x ∧ x.1 < 2^256) W_2 := buildWiresBT_faithful (mkBase_ok (by decide))
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
def N_2_3 : List NodeSpec := [([10,11,1,2],[],[3]),([13,0,1,3],[],[]),([15,1,2,3],[],[]),([16,1,2,12],[],[3]),([0,1,17,3],[],[]),([18,1,2,3],[],[]),([19,20,1,3],[],[2]),([22,1,2,3],[],[]),([0,1,24,3],[],[]),([25,26,2,3],[],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_3 : checkNodesBT W_2 g_2 F_2 P_2_3 A_2 B_2_2 3 N_2_3 = true := by decide +kernel
def B_2_3 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_3
set_option maxRecDepth 500000 in
lemma B_2_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 3 xs.toFinset) B_2_3 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_2_ok C_2_3
def U_2_4 : List Nat := []
def P_2_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_4
def N_2_4 : List NodeSpec := [([27,0,1,2,3],[],[4]),([10,0,1,2,3],[],[0]),([0,1,2,3,12],[],[0,1,2,4]),([16,0,1,2,3],[],[0,1,3,5]),([19,0,1,2,3],[],[0,1,3]),([0,1,26,2,3],[],[0]),([25,0,1,2,3],[],[0])]
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
def g_3 := (d 0xe800e800e800e800)
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_4 := (d 0xfee88000fee88000)
def r_4 : List Nat := varsOf 31
def p_4 : List Nat := [15,15,15,15,19,19,19,21,21,21,22,22,22,23,25,25,25,26,26,26,27,28,28,28,29,30]
def q_4 : List Nat := [14,13,11,7,18,17,3,20,17,5,20,18,6,7,24,17,9,24,18,10,11,24,20,12,13,14]
def F_4 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_4 : goodPairs g_4 p_4 q_4 := goodPairs_of (by decide +kernel)
def W_4 : BT Decor := buildWiresBT 4 (mkBase p_4 q_4 r_4) [(0,0,3),(0,1,2),(1,5,6),(0,0,1),(0,2,3)]
lemma W_4_ok : btAll (fun x => faithful p_4 q_4 x ∧ x.1 < 2^256) W_4 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_4 : List (List (Nat × Nat)) := [[],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)]]
def A_4 : BT (List (Nat × Nat)) := btOfList 3 al_4
set_option maxHeartbeats 0 in
lemma A_4_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_4 = g_4) A_4 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_4_0 : Slice r_4 g_4 (subcubeFast 0 16) 7 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_4_1 : Slice r_4 g_4 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_2 : Slice r_4 g_4 (subcubeFast 0 2) 6 := by
  have hc : Lower (varsOf 29) (d 0xfffaa000fffaa000) 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_3 : Slice r_4 g_4 (subcubeFast 0 4) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_4 : Slice r_4 g_4 (subcubeFast 0 8) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_5 : Slice r_4 g_4 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfaa00000faa00000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_6 : Slice r_4 g_4 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xee880000ee880000) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_7 : Slice r_4 g_4 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_8 : Slice r_4 g_4 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfcc00000fcc00000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_4 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 16,7),some (subcubeFast 0 1,6),some (subcubeFast 0 2,6),some (subcubeFast 0 4,6),some (subcubeFast 0 8,6),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 1 0,5)]
lemma S_4_ok : btAll (fun o => ∀ p, o = some p → Slice r_4 g_4 p.1 p.2) S_4 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_4_0) (forall_cons (fun _ h => by cases h; exact sl_4_1) (forall_cons (fun _ h => by cases h; exact sl_4_2) (forall_cons (fun _ h => by cases h; exact sl_4_3) (forall_cons (fun _ h => by cases h; exact sl_4_4) (forall_cons (fun _ h => by cases h; exact sl_4_5) (forall_cons (fun _ h => by cases h; exact sl_4_6) (forall_cons (fun _ h => by cases h; exact sl_4_7) (forall_cons (fun _ h => by cases h; exact sl_4_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_4 : BT (Option PoolSpec) := btOfList 4 [q 5 [],q 6 [],q 3 [],q 4 [],q 7 [],q 1 [12296],q 8 [],q 2 [],q 3 [4096],q 1 [],q 0 [],q 0 [4096],q 4 [4096]]
def B_4_4 : BT (List (List Nat)) := BT.empty
lemma B_4_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 4 xs.toFinset) B_4_4 := .empty
def U_4_5 : List Nat := []
def P_4_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_5
def N_4_5 : List NodeSpec := [e5 [7] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_5 : checkNodesBT W_4 g_4 F_4 P_4_5 A_4 B_4_4 5 N_4_5 = true := by decide +kernel
def B_4_5 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_5
set_option maxRecDepth 500000 in
lemma B_4_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 5 xs.toFinset) B_4_5 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_4_ok C_4_5
def U_4_6 : List Nat := (r 0 9)
def P_4_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_6
def N_4_6 : List NodeSpec := [a5 [8,9] (r 0 9) [2]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_6 : checkNodesBT W_4 g_4 F_4 P_4_6 A_4 B_4_5 6 N_4_6 = true := by decide +kernel
def B_4_6 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_6
set_option maxRecDepth 500000 in
lemma B_4_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 6 xs.toFinset) B_4_6 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_5_ok C_4_6
def U_4_7 : List Nat := (r 0 5++r 7 6)
def P_4_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_7
def N_4_7 : List NodeSpec := [u5 [8] (r 0 5++r 7 6)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_7 : checkNodesBT W_4 g_4 F_4 P_4_7 A_4 B_4_6 7 N_4_7 = true := by decide +kernel
def B_4_7 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_7
set_option maxRecDepth 500000 in
lemma B_4_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 7 xs.toFinset) B_4_7 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_6_ok C_4_7
def U_4_8 : List Nat := [2,3,7,9,10]
def P_4_8 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_8
def N_4_8 : List NodeSpec := [a5 [] [2,3,7,9,10] [0,1,3,4,5,6]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_8 : checkNodesBT W_4 g_4 F_4 P_4_8 A_4 B_4_7 8 N_4_8 = true := by decide +kernel
def B_4_8 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_8
set_option maxRecDepth 500000 in
lemma B_4_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 8 xs.toFinset) B_4_8 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_7_ok C_4_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_4_ok : forestRootCheck r_4 g_4 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_4_in : bucketContainsBT B_4_8 r_4 = true := by decide +kernel
lemma low_4 : Lower r_4 g_4 9 := lower_of_forestBT root_4_ok B_4_8_ok root_4_in
def g_5 := (d 0xfee0fee0fee0fee0)
def r_5 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_5 : Lower r_5 g_5 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_6 := (d 0xfffefe80fffefe80)
def r_6 : List Nat := varsOf 31
def p_6 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14,17,17,18,18,19,20,20,21,22,24,24]
def q_6 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6,16,1,16,2,3,16,4,5,6,16,8]
def F_6 : Nat := fullMask 23
set_option maxHeartbeats 0 in
lemma gp_6 : goodPairs g_6 p_6 q_6 := goodPairs_of (by decide +kernel)
def W_6 : BT Decor := buildWiresBT 7 (mkBase p_6 q_6 r_6) [(1,2,1),(1,1,3),(1,2,4),(0,6,7),(1,3,4),(3,2,9),(0,2,0),(1,10,11),(1,2,0),(1,13,3),(1,14,4),(3,2,15),(1,0,3),(1,17,4),(3,1,18),(0,2,9),(1,2,3),(1,21,4),(3,20,22),(0,0,1),(1,24,3),(1,25,4),(3,2,26),(1,1,13),(1,28,3),(2,29,4),(3,2,17),(1,0,4),(0,1,18),(1,13,4),(2,17,4),(3,3,32),(1,1,4),(0,17,37),(0,0,22),(1,0,1),(1,40,3),(1,41,4),(3,2,42),(3,1,9),(1,44,0),(2,45,2),(3,0,9),(2,6,4),(1,48,0),(1,6,4),(0,0,50),(2,0,9),(2,31,4),(1,10,0),(3,2,32),(1,55,3),(3,20,0),(3,2,6),(1,58,0),(3,5,9),(1,24,4),(2,28,4),(2,25,4),(0,1,2),(3,64,9),(2,2,3),(3,66,7),(0,0,9),(3,2,41),(1,40,4),(1,52,4),(2,41,4),(3,5,17),(2,0,4),(1,74,3)]
lemma W_6_ok : btAll (fun x => faithful p_6 q_6 x ∧ x.1 < 2^256) W_6 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_6 : List (List (Nat × Nat)) := [[],[(3,4)],[(1,2)],[(1,2),(3,4)],[(0,1)],[(0,1),(3,4)],[(0,2),(1,2)],[(0,2),(1,2),(3,4)],[(0,1),(1,2)],[(0,1),(1,2),(3,4)],[(0,2)],[(0,2),(3,4)]]
def A_6 : BT (List (Nat × Nat)) := btOfList 4 al_6
set_option maxHeartbeats 0 in
lemma A_6_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_6 = g_6) A_6 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_6_0 : Slice r_6 g_6 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_1 : Slice r_6 g_6 (identDom 0 2) 7 := by
  have hc : Lower (varsOf 27) (d 0xffeeee88ffeeee88) 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_2 : Slice r_6 g_6 (identDom 1 2) 7 := by
  have hc : Lower (varsOf 27) (d 0xffeeee88ffeeee88) 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_3 : Slice r_6 g_6 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_4 : Slice r_6 g_6 (subcubeFast 16 0) 6 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_6_5 : Slice r_6 g_6 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_6 : Slice r_6 g_6 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffafa00fffafa00) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_7 : Slice r_6 g_6 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeeee00ffeeee00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_8 : Slice r_6 g_6 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_9 : Slice r_6 g_6 (subcubeFast 5 0) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_10 : Slice r_6 g_6 (subcubeFast 6 0) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 0) (by decide +kernel) hc
def S_6 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,7),some (identDom 0 2,7),some (identDom 1 2,7),some (subcubeFast 8 0,6),some (subcubeFast 16 0,6),some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 3 0,4),some (subcubeFast 5 0,4),some (subcubeFast 6 0,4)]
lemma S_6_ok : btAll (fun o => ∀ p, o = some p → Slice r_6 g_6 p.1 p.2) S_6 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_6_0) (forall_cons (fun _ h => by cases h; exact sl_6_1) (forall_cons (fun _ h => by cases h; exact sl_6_2) (forall_cons (fun _ h => by cases h; exact sl_6_3) (forall_cons (fun _ h => by cases h; exact sl_6_4) (forall_cons (fun _ h => by cases h; exact sl_6_5) (forall_cons (fun _ h => by cases h; exact sl_6_6) (forall_cons (fun _ h => by cases h; exact sl_6_7) (forall_cons (fun _ h => by cases h; exact sl_6_8) (forall_cons (fun _ h => by cases h; exact sl_6_9) (forall_cons (fun _ h => by cases h; exact sl_6_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_6 : BT (Option PoolSpec) := btOfList 7 [q 3 [36872,36873,90195],q 3 [],q 4 [],q 10 [],q 0 [],q 1 [],q 3 [36865,73739],q 3 [16453,73739],q 9 [],q 7 [],q 3 [36866,36867],q 1 [16397,36875,41],q 3 [16385,131083],q 3 [16393],q 4 [12297],q 3 [36872,83],q 1 [16397,36875],q 2 [16397,36887],q 0 [16481,12305],q 5 [],q 6 [],q 0 [9,12297],q 1 [53253],q 2 [9],q 0 [12385,16486],q 0 [12385,16485],q 0 [16385,12305],q 1 [16385,12305],q 1 [12341,57355],q 4 [12289,69643],q 2 [],q 0 [16397,36865],q 1 [16397,36865],q 0 [16397,36864],q 1 [16397,36864],q 3 [36864,36865],q 1 [12297,57355],q 3 [36875],q 0 [16397],q 1 [16397],q 3 [36864],q 3 [16454],q 4 [12289],q 0 [12289,16454],q 1 [12289,16454],q 3 [16453],q 0 [12289],q 1 [12289],q 3 [16389],q 0 [16389],q 8 [],q 3 [4097],q 3 [16385],q 3 [4096],q 0 [12385],q 1 [12297],q 3 [9],q 0 [8353],q 1 [4097],q 0 [12297],q 1 [4097,12297],q 2 [4097,12297],q 2 [4097],q 3 [16386],q 4 [12585],q 3 [69643],q 3 [36865],q 1 [12289,69643],q 2 [16397,36875],q 4 [36875],q 3 [36866],q 0 [12289,16453],q 1 [12289,16453],q 3 [69637],q 4 [4097],q 2 [16397],q 4 [4096]]
def B_6_2 : BT (List (List Nat)) := BT.empty
lemma B_6_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 2 xs.toFinset) B_6_2 := .empty
def U_6_3 : List Nat := []
def P_6_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_6 r_6 S_6 ps_6 U_6_3
def N_6_3 : List NodeSpec := [([0,5,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_3 : checkNodesBT W_6 g_6 F_6 P_6_3 A_6 B_6_2 3 N_6_3 = true := by decide +kernel
def B_6_3 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_3
set_option maxRecDepth 500000 in
lemma B_6_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 3 xs.toFinset) B_6_3 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_2_ok C_6_3
def U_6_4 : List Nat := (r 0 4)
def P_6_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_6 r_6 S_6 ps_6 U_6_4
def N_6_4 : List NodeSpec := [([0,12,1,3,4],[],[]),([16,19,0,3,4],[],[]),([0,5,3,8,4],[],[0]),([23,0,1,3,4],[0],[]),([27,0,1,3,4],[],[]),([30,0,1,2,3],[],[]),([31,1,2,32,9],[],[]),([16,0,33,3,4],[],[]),([0,1,21,34,9],[1],[]),([35,36,0,1,2],[],[]),([0,1,2,38,9],[1,2],[8]),([10,39,1,3,4],[],[]),([16,0,1,3,4],[],[]),([0,5,6,7,9],[3],[0]),([43,0,1,3,4],[],[]),([46,0,1,3,4],[],[]),([35,47,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_4 : checkNodesBT W_6 g_6 F_6 P_6_4 A_6 B_6_3 4 N_6_4 = true := by decide +kernel
def B_6_4 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_4
set_option maxRecDepth 500000 in
lemma B_6_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 4 xs.toFinset) B_6_4 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_3_ok C_6_4
def U_6_5 : List Nat := ([1,2]++r 4 33)
def P_6_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_6 r_6 S_6 ps_6 U_6_5
def N_6_5 : List NodeSpec := [a5 [18] [4,5] [0,2],([35,0,1,2,3,9],[1],[0]),([16,0,1,3,4,9],[6],[]),e5 [49] [],([16,0,1,3,17,4],[7],[]),([10,0,1,3,21,4],[1],[8]),e5 [16] [],([16,0,1,3,4],[],[]),([51,1,2,3,4,50],[8],[2,4,6]),([10,0,1,3,4,22],[4],[0,4,8,9]),([35,0,1,2,17,9],[1,2],[]),([10,0,1,3,7,9],[2,9],[]),a5 [38] [1,2] [0,8],([52,47,1,2,3,4],[10],[6]),e5 [53] [],a5 [54] [4,11] [0,2],e5 [56] [12],([0,5,3,6,4,7],[],[0]),u5 [29] [2],([0,1,21,7,9],[1,2,9,13,14],[0,1,4,5,8,9,10,11]),([57,1,2,3,4,9],[15],[]),([31,1,13,3,17,4],[5],[]),e5 [10] [],([10,11,0,1,3,4],[16],[0]),e5 [59] [4],e5 [60] [17],([0,1,3,21,4,34],[1],[0]),([0,1,2,3,61,9],[1,18,19,20],[]),([0,1,28,3,21,4],[1,21,22,23],[]),e5 [62] [],([0,1,13,3,7,9],[8],[1,4]),e5 [63] [24],([0,1,2,17,37,9],[],[0,3,6,8]),e5 [65] [],([35,1,2,3,17,32],[2,19],[]),([0,1,13,3,4,22],[5,23],[]),([0,1,3,67,4,7],[2,9],[]),u5 [26] [9,25],([68,1,2,3,32,9],[2,26,27],[]),([31,0,1,3,14,4],[4,8,28],[]),e5 [69] [],([31,0,1,2,4,9],[2,29],[0]),([0,1,2,3,70,9],[1],[2,6]),([0,1,2,3,71,9],[1,19],[]),([16,0,1,3,4,18],[5],[0]),a5 [42] [5] [0,2,6],([35,1,40,2,3,4],[20],[]),e5 [72] [],([31,0,1,5,3,4],[30],[]),([35,0,1,2,3,32],[2],[0]),([35,0,1,2,3,18],[4],[0]),e5 [73] [],([31,1,2,3,4,32],[],[0]),([68,1,2,3,4,18],(r 31 5),[6]),([0,1,2,17,32,9],[1,19],[]),([31,0,1,3,21,4],[1,36],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_5 : checkNodesBT W_6 g_6 F_6 P_6_5 A_6 B_6_4 5 N_6_5 = true := by decide +kernel
def B_6_5 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_5
set_option maxRecDepth 500000 in
lemma B_6_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 5 xs.toFinset) B_6_5 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_4_ok C_6_5
def U_6_6 : List Nat := (r 1 5++[8,9,13,14,16,19,20,21,23,26,27,29,30]++r 37 37)
def P_6_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_6 r_6 S_6 ps_6 U_6_6
def N_6_6 : List NodeSpec := [a5 [10,9] [1,2,9,37] [0,1,8],a5 [68,9] [1,2,19,38,39,40] [0,1,6,10],a5 [35] ([2,9,20]++r 41 4) [0,2,4,8],a5 [17,18] [42,45,46,47] [0,1,2,6],a5 [17,37] [42,46,48,49] [0,2,3,6,7,8],a5 [41] [2,5,50,51] [0,1,2,3,6,7],([0,1,2,3,32,9],[2,19,26,27,52],[0,1,2,3,6,10]),a5 [24,9] [1,2,19,20,38,53] [0,1,2,6,8],a5 [17,32] [2,19,52] [0,1],a5 [25] [2,8,20,53,54] [0,1],([0,1,13,3,21,4],[1,8,21,23,55,56],[0,1,5,8,10]),a5 [28] [1,2,3,8,50,57,58] [0,1,2,3,6,7],a5 [40,21] ([50,51]++r 58 5) [0,8,10],([74,1,2,3,17,4],[1,8,19,42,46,47,50,63],[7]),e5 [75] [8,50,64],a5 [31] [1,2,5,8,29,30,65] [0,1,4],a5 [9,18] [19,38,39,66] [0,1,2,6],u5 [31,17] [1,47,65,67],u5 [35,17] [2,19,41,42],a5 [40,9] [1,2,19,20,38,50,51] [0,1,2,3,6,7,8],([0,1,3,21,4,7],[9,13,14],[0,1,4,5,8,9,10,11]),a5 [10] [1,2,5,16,30,37,68,69] [0,4,8],a5 [52,9] [19,70] [0,1],a5 [18] [4,5,42,45,71,72] [0,1,2,4,6,8,10],a5 [17,41] [46,50,73] [2,6]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_6 : checkNodesBT W_6 g_6 F_6 P_6_6 A_6 B_6_5 6 N_6_6 = true := by decide +kernel
def B_6_6 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_6
set_option maxRecDepth 500000 in
lemma B_6_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 6 xs.toFinset) B_6_6 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_5_ok C_6_6
def U_6_7 : List Nat := [1,2,4,5,8,9,19,20,38,39,42,46,47,50,51,53,58,62,74,75,76]
def P_6_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_6 r_6 S_6 ps_6 U_6_7
def N_6_7 : List NodeSpec := [u5 [74] [1,2,4,5,8,9,19,20,50],a5 [17] [1,8,19,42,46,47,50] [0,1,2,6,10],a5 [40] [1,2,4,8,50,51,58,62,74] [0,1,2,3,6,7],a5 [9] [1,2,9,19,20,38,39,75] [0,1,2,4,5,6,8,9],a5 [24] [1,2,4,5,8,9,19,20,53,76] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_7 : checkNodesBT W_6 g_6 F_6 P_6_7 A_6 B_6_6 7 N_6_7 = true := by decide +kernel
def B_6_7 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_7
set_option maxRecDepth 500000 in
lemma B_6_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 7 xs.toFinset) B_6_7 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_6_ok C_6_7
def U_6_8 : List Nat := [1,2,4,5,30]
def P_6_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_6 r_6 S_6 ps_6 U_6_8
def N_6_8 : List NodeSpec := [a5 [] [1,2,4,5,30] [0,1,2,4,5,6,8,9]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_8 : checkNodesBT W_6 g_6 F_6 P_6_8 A_6 B_6_7 8 N_6_8 = true := by decide +kernel
def B_6_8 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_8
set_option maxRecDepth 500000 in
lemma B_6_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 8 xs.toFinset) B_6_8 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_7_ok C_6_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_6_ok : forestRootCheck r_6 g_6 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_6_in : bucketContainsBT B_6_8 r_6 = true := by decide +kernel
lemma low_6 : Lower r_6 g_6 9 := lower_of_forestBT root_6_ok B_6_8_ok root_6_in
def g_7 := (d 0xfffffee8fffffee8)
def r_7 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_7 : Lower r_7 g_7 8 := by
  exact lift_of_f (z := 16) (o := 0) (other := r_1) (G := g_1) (essPairs := [(VAR 4,0,16)]) (by decide +kernel) low_1
def g_8 := (d 0xfec0fec0fec0fec0)
def r_8 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_9 := (d 0xf880f880f880f880)
def r_9 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_9 : Lower r_9 g_9 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_10 := (d 0xffe8ffe8ffe8ffe8)
def r_10 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_10 : Lower r_10 g_10 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_11 := (d 0xffe8e000ffe8e000)
def r_11 : List Nat := varsOf 31
def p_11 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28]
def q_11 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12]
def F_11 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_11 : goodPairs g_11 p_11 q_11 := goodPairs_of (by decide +kernel)
def W_11 : BT Decor := buildWiresBT 3 (mkBase p_11 q_11 r_11) [(0,2,4)]
lemma W_11_ok : btAll (fun x => faithful p_11 q_11 x ∧ x.1 < 2^256) W_11 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_11 : List (List (Nat × Nat)) := [[]]
def A_11 : BT (List (Nat × Nat)) := btOfList 1 al_11
set_option maxHeartbeats 0 in
lemma A_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_11 = g_11) A_11 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_11_0 : Slice r_11 g_11 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_1 : Slice r_11 g_11 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xffa0a000ffa0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_2 : Slice r_11 g_11 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_3 : Slice r_11 g_11 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeeee00ffeeee00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_4 : Slice r_11 g_11 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_5 : Slice r_11 g_11 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_6 : Slice r_11 g_11 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_10
set_option maxHeartbeats 0 in
lemma sl_11_7 : Slice r_11 g_11 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_11_8 : Slice r_11 g_11 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_11 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 1 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4),some (identDom 2 3,6)]
lemma S_11_ok : btAll (fun o => ∀ p, o = some p → Slice r_11 g_11 p.1 p.2) S_11 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_11_0) (forall_cons (fun _ h => by cases h; exact sl_11_1) (forall_cons (fun _ h => by cases h; exact sl_11_2) (forall_cons (fun _ h => by cases h; exact sl_11_3) (forall_cons (fun _ h => by cases h; exact sl_11_4) (forall_cons (fun _ h => by cases h; exact sl_11_5) (forall_cons (fun _ h => by cases h; exact sl_11_6) (forall_cons (fun _ h => by cases h; exact sl_11_7) (forall_cons (fun _ h => by cases h; exact sl_11_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_11 : BT (Option PoolSpec) := btOfList 4 [q 5 [],q 0 [],q 1 [],q 2 [],q 6 [],q 4 [],q 7 [],q 3 [],q 8 []]
def B_11_5 : BT (List (List Nat)) := BT.empty
lemma B_11_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 5 xs.toFinset) B_11_5 := .empty
def U_11_6 : List Nat := (r 0 8)
def P_11_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_11 r_11 S_11 ps_11 U_11_6
def N_11_6 : List NodeSpec := [e5 [5] (r 0 8)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_6 : checkNodesBT W_11 g_11 F_11 P_11_6 A_11 B_11_5 6 N_11_6 = true := by decide +kernel
def B_11_6 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_6
set_option maxRecDepth 500000 in
lemma B_11_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 6 xs.toFinset) B_11_6 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_5_ok C_11_6
def U_11_7 : List Nat := (r 0 9)
def P_11_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_11 r_11 S_11 ps_11 U_11_7
def N_11_7 : List NodeSpec := [u5 [] (r 0 9)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_7 : checkNodesBT W_11 g_11 F_11 P_11_7 A_11 B_11_6 7 N_11_7 = true := by decide +kernel
def B_11_7 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_7
set_option maxRecDepth 500000 in
lemma B_11_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 7 xs.toFinset) B_11_7 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_6_ok C_11_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck r_11 g_11 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT B_11_7 r_11 = true := by decide +kernel
lemma low_11 : Lower r_11 g_11 8 := lower_of_forestBT root_11_ok B_11_7_ok root_11_in
def g_12 := (d 0xfffef800fffef800)
def r_12 : List Nat := varsOf 31
def p_12 : List Nat := [11,11,11,12,12,13,13,14,14,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26]
def q_12 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10]
def F_12 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_12 : goodPairs g_12 p_12 q_12 := goodPairs_of (by decide +kernel)
def W_12 : BT Decor := buildWiresBT 6 (mkBase p_12 q_12 r_12) [(0,3,4),(1,2,5),(1,0,6),(1,1,6),(1,3,4),(3,6,9),(3,5,9),(2,11,1),(3,2,9),(1,1,3),(1,14,4),(3,1,15),(1,0,3),(0,17,4),(1,2,18),(2,0,5),(1,1,5),(2,13,1),(2,13,0),(1,0,5),(0,0,9),(0,11,0),(2,0,6),(3,3,4),(1,28,0),(2,29,1),(2,3,4),(0,13,0),(3,0,3),(3,33,4),(3,1,4),(3,1,3),(1,36,4),(1,35,3),(1,33,1),(3,0,4),(1,40,3),(3,1,41),(1,1,18),(1,17,4),(3,2,44),(3,1,44),(3,2,38),(3,0,44),(0,14,4),(1,1,4),(1,31,0),(3,14,4),(2,17,4),(3,40,3),(1,0,4),(3,1,55),(0,3,55),(3,3,55)]
lemma W_12_ok : btAll (fun x => faithful p_12 q_12 x ∧ x.1 < 2^256) W_12 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_12 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_12 : BT (List (Nat × Nat)) := btOfList 1 al_12
set_option maxHeartbeats 0 in
lemma A_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_12 = g_12) A_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_12_0 : Slice r_12 g_12 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_1 : Slice r_12 g_12 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_2 : Slice r_12 g_12 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_3 : Slice r_12 g_12 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_4 : Slice r_12 g_12 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec8c8fefec8c8) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_5 : Slice r_12 g_12 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefea8a8fefea8a8) 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
def S_12 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 4 0,6),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 3 0,4),some (identDom 1 3,5),some (identDom 0 3,5)]
lemma S_12_ok : btAll (fun o => ∀ p, o = some p → Slice r_12 g_12 p.1 p.2) S_12 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_12_0) (forall_cons (fun _ h => by cases h; exact sl_12_1) (forall_cons (fun _ h => by cases h; exact sl_12_2) (forall_cons (fun _ h => by cases h; exact sl_12_3) (forall_cons (fun _ h => by cases h; exact sl_12_4) (forall_cons (fun _ h => by cases h; exact sl_12_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_12 : BT (Option PoolSpec) := btOfList 5 [q 0 [16396,16397,36887],q 0 [16396,16397],q 1 [],q 0 [16398,16399],q 2 [],q 0 [],q 3 [],q 0 [16397,36864],q 5 [],q 0 [16396,20485],q 0 [16397,36871],q 2 [16391],q 0 [12291,4229],q 0 [16396,20482],q 2 [12293],q 4 [],q 0 [16385,225287],q 2 [225287],q 0 [16399],q 0 [16398],q 0 [16397],q 0 [16396],q 0 [16391],q 0 [16385],q 0 [12295],q 1 [12289],q 0 [12289]]
def B_12_1 : BT (List (List Nat)) := BT.empty
lemma B_12_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 1 xs.toFinset) B_12_1 := .empty
def U_12_2 : List Nat := []
def P_12_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_12 r_12 S_12 ps_12 U_12_2
def N_12_2 : List NodeSpec := [([7,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_2 : checkNodesBT W_12 g_12 F_12 P_12_2 A_12 B_12_1 2 N_12_2 = true := by decide +kernel
def B_12_2 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_2
set_option maxRecDepth 500000 in
lemma B_12_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 2 xs.toFinset) B_12_2 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_1_ok C_12_2
def U_12_3 : List Nat := []
def P_12_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_12 r_12 S_12 ps_12 U_12_3
def N_12_3 : List NodeSpec := [([10,11,0,1],[],[]),([12,11,0,2],[],[]),([11,13,0,1],[],[]),([11,16,0,2],[],[]),([11,0,1,2],[],[]),([0,1,19,9],[],[]),([20,11,1,2],[],[]),([0,21,6,9],[],[]),([22,23,3,4],[],[]),([2,24,21,9],[],[]),([11,0,2,21],[],[]),([11,0,1,6],[],[]),([20,1,6,9],[],[]),([11,25,1,2],[],[]),([3,7,8,4],[],[0]),([10,0,1,9],[],[]),([25,1,6,9],[],[]),([16,0,6,9],[],[]),([26,11,1,2],[],[]),([0,6,8,9],[],[0]),([27,1,6,9],[],[]),([0,1,6,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_3 : checkNodesBT W_12 g_12 F_12 P_12_3 A_12 B_12_2 3 N_12_3 = true := by decide +kernel
def B_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_3
set_option maxRecDepth 500000 in
lemma B_12_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 3 xs.toFinset) B_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_2_ok C_12_3
def U_12_4 : List Nat := [0,1]
def P_12_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_12 r_12 S_12 ps_12 U_12_4
def N_12_4 : List NodeSpec := [([13,0,1,3,4],[],[]),([0,1,3,6,4],[],[0]),([22,13,0,3,4],[],[0]),([13,16,0,3,4],[],[]),([13,25,1,3,4],[],[]),([30,0,2,3,4],[],[]),([16,25,2,3,4],[],[]),([11,0,1,2,4],[],[]),([11,0,1,2,3],[],[]),([11,0,1,2],[0],[0,1]),([13,0,1,5,9],[],[0]),([16,0,2,5,9],[],[0]),([31,28,0,1,2],[],[0]),([32,13,1,3,4],[],[]),([25,1,2,5,9],[],[0]),([0,1,2,5,9],[],[0]),([0,1,5,6,9],[],[0,1]),([0,1,6,9],[1],[0,1]),([31,0,34,1,2],[],[]),([20,1,3,6,4],[],[0]),([35,0,2,3,37],[],[]),([28,11,0,1,2],[],[]),([0,1,3,6,9],[],[]),([36,0,2,38,4],[],[]),([0,39,2,4,9],[],[]),([28,0,1,3,6],[],[0]),([31,11,0,1,2],[],[]),([42,0,2,3,4],[],[]),([16,0,2,3,4],[],[]),([0,1,3,19,4],[],[0]),([11,0,1,2,5],[0],[0,1]),([0,2,3,43,4],[],[]),([45,0,1,3,4],[],[]),([0,1,2,18,9],[],[0]),([46,0,2,3,4],[],[]),([47,0,1,3,4],[],[]),([11,0,1,2,9],[0],[0,1]),([31,0,2,21,4],[],[]),([0,2,21,4,9],[],[]),([0,3,21,6,4],[],[0]),([16,48,2,3,4],[],[]),([20,2,3,21,4],[],[]),([31,0,39,2,4],[],[]),([0,2,5,21,9],[],[0]),([20,1,2,5,9],[],[0]),([2,3,24,21,4],[],[0]),([0,3,6,8,4],[],[0]),([0,2,3,49,50],[],[]),([31,0,1,6,4],[],[0]),([27,1,3,6,4],[],[0]),([0,1,6,4,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_4 : checkNodesBT W_12 g_12 F_12 P_12_4 A_12 B_12_3 4 N_12_4 = true := by decide +kernel
def B_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_4
set_option maxRecDepth 500000 in
lemma B_12_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 4 xs.toFinset) B_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_3_ok C_12_4
def U_12_5 : List Nat := (r 1 17)
def P_12_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_12 r_12 S_12 ps_12 U_12_5
def N_12_5 : List NodeSpec := [u5 [29] [2],([31,28,0,1,2,4],[],[0]),([31,28,0,1,2],[3],[0]),a5 [9] [2,4,5] [0,1],e5 [51] [],e5 [16] [],([13,0,1,3,4],[],[0,1]),([25,1,2,3,4,9],[6,7],[0,1]),([31,28,0,1,2,3],[],[0]),([0,1,2,5,3,9],[],[0]),u5 [28] [],([31,36,0,1,2,4],[2],[1]),a5 [18] [2,5,8] [0,1],([0,2,5,3,21,4],[2,9],[0]),([0,1,3,6,4],[],[0,1]),u5 [37] [],([36,0,1,2,4,9],[2],[1]),e5 [52] [],([28,0,1,2,4,9],[5],[0]),e5 [53] [],([16,0,2,3,4],[10],[]),e5 [54] [],([36,35,0,2,3,4],[11],[0]),a5 [44] [2,5] [0,1],a5 [38] [4,5] [0,1],([31,0,1,2,3,9],[5],[0]),([0,39,2,3,4],[12],[0]),([20,1,2,5,3,4],[6,8,13],[0]),([31,0,1,2,17,4],[4],[]),([16,0,2,3,4,9],[2,10],[0]),([35,0,2,3,4,50],[2,11],[]),([0,2,3,14,4,50],[14,15],[0]),e5 [24] [],u5 [34] [4],([31,0,1,2,5,4],[5],[0,1]),([0,1,2,17,4,9],[4],[0]),([56,0,2,3,4],[16],[]),([0,1,2,5,4,9],[],[0,1]),([0,2,3,21,4],[9],[0]),([56,0,2,3,4,55],[2,17],[]),u5 [5] [2,4,5,8,15],([0,1,2,5,9],[1],[0,1]),([0,1,5,3,6,4],[5],[0,1]),e5 [57] [8],e5 [58] [],u5 [31] [],([13,0,1,3,4,9],[5],[0,1]),([28,0,1,2,5,3],[5],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_5 : checkNodesBT W_12 g_12 F_12 P_12_5 A_12 B_12_4 5 N_12_5 = true := by decide +kernel
def B_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_5
set_option maxRecDepth 500000 in
lemma B_12_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 5 xs.toFinset) B_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_4_ok C_12_5
def U_12_6 : List Nat := ([2,4,5,6,8,15]++r 18 9)
def P_12_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_12 r_12 S_12 ps_12 U_12_6
def N_12_6 : List NodeSpec := [a5 [28] [2,4,5,18] [0,1],a5 [31] [2,4,5,8,15,19] [0,1],a5 [9] [2,4,20] [0,1],a5 [5] [2,4,8,15,21] [0,1],a5 [35] [4,5,6,15,22] [0,1],a5 [55] [6,8,23] [0,1],a5 [36] [4,6,15,24] [0,1],a5 [17] [4,6,8,25,26] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_6 : checkNodesBT W_12 g_12 F_12 P_12_6 A_12 B_12_5 6 N_12_6 = true := by decide +kernel
def B_12_6 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_6
set_option maxRecDepth 500000 in
lemma B_12_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 6 xs.toFinset) B_12_6 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_5_ok C_12_6
def U_12_7 : List Nat := [2,5,6]
def P_12_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_12 r_12 S_12 ps_12 U_12_7
def N_12_7 : List NodeSpec := [a5 [] [2,5,6] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_7 : checkNodesBT W_12 g_12 F_12 P_12_7 A_12 B_12_6 7 N_12_7 = true := by decide +kernel
def B_12_7 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_7
set_option maxRecDepth 500000 in
lemma B_12_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 7 xs.toFinset) B_12_7 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_6_ok C_12_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck r_12 g_12 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT B_12_7 r_12 = true := by decide +kernel
lemma low_12 : Lower r_12 g_12 8 := lower_of_forestBT root_12_ok B_12_7_ok root_12_in
def g_13 := (d 0xfffee800fffee800)
def r_13 : List Nat := varsOf 31
def p_13 : List Nat := [11,11,11,13,13,13,14,14,14,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26,28]
def q_13 : List Nat := [10,9,3,12,9,5,12,10,6,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10,12]
def F_13 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_13 : goodPairs g_13 p_13 q_13 := goodPairs_of (by decide +kernel)
def W_13 : BT Decor := buildWiresBT 8 (mkBase p_13 q_13 r_13) [(0,3,4),(1,2,5),(1,0,1),(0,7,3),(1,8,4),(1,0,2),(1,2,1),(1,11,4),(0,3,12),(1,7,4),(3,3,14),(1,1,10),(1,16,4),(3,2,17),(0,3,14),(0,2,14),(3,3,4),(1,21,8),(3,2,4),(3,2,7),(1,24,4),(3,2,3),(1,3,4),(0,10,27),(3,1,3),(1,2,4),(3,29,30),(1,0,4),(3,2,32),(1,26,0),(0,11,4),(3,35,12),(0,0,12),(0,7,30),(3,7,3),(1,39,2),(3,0,3),(3,41,11),(2,3,4),(2,7,4),(3,1,10),(1,10,4),(0,3,46),(3,11,3),(0,1,46),(3,1,14),(3,2,9),(1,2,3),(3,1,52),(3,5,27),(1,23,1),(1,21,7),(2,56,2),(0,11,3),(1,11,3),(3,58,59),(2,7,3),(3,0,30),(3,2,27),(1,63,0),(3,11,27),(1,0,5),(3,2,66),(1,7,3),(1,48,2),(1,48,4),(3,11,4),(1,71,2),(0,16,3),(1,1,4),(2,8,4),(1,26,4),(0,10,3),(3,35,3),(2,26,4),(1,26,1),(1,48,0),(1,34,4),(2,34,4),(0,7,4),(1,84,2),(1,79,0),(0,10,4),(1,21,0),(2,88,2),(1,84,3),(1,0,3),(3,11,91),(1,1,3),(3,2,93),(1,94,0),(0,7,52),(2,11,4),(1,97,0),(1,0,6),(2,16,4),(3,1,4),(1,101,0),(2,102,2),(1,26,7),(3,0,4),(3,105,11),(1,21,2),(1,61,2),(0,7,27),(1,10,3),(3,2,110),(2,24,4),(1,7,5),(3,21,7),(1,29,4),(3,2,115),(3,97,3),(0,3,30),(3,7,4),(3,11,32),(2,7,5),(1,58,0),(3,0,11),(3,123,3),(1,29,0),(2,125,2),(1,23,7),(3,41,74),(3,26,27),(3,2,74),(1,130,0),(3,62,3),(0,3,74),(1,0,133),(0,3,32),(1,23,0)]
lemma W_13_ok : btAll (fun x => faithful p_13 q_13 x ∧ x.1 < 2^256) W_13 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_13 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_13 : BT (List (Nat × Nat)) := btOfList 3 al_13
set_option maxHeartbeats 0 in
lemma A_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_13 = g_13) A_13 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_13_0 : Slice r_13 g_13 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_1 : Slice r_13 g_13 (subcubeFast 2 0) 6 := by
  have hc : Lower (varsOf 29) (d 0xfffaa000fffaa000) 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_2 : Slice r_13 g_13 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_3 : Slice r_13 g_13 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_4 : Slice r_13 g_13 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_13_5 : Slice r_13 g_13 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_13_6 : Slice r_13 g_13 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefea8a8fefea8a8) 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_7 : Slice r_13 g_13 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec8c8fefec8c8) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_8 : Slice r_13 g_13 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefee0e0fefee0e0) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_13 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 1 0,6),some (subcubeFast 2 0,6),some (subcubeFast 4 0,6),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (identDom 0 3,5),some (identDom 1 3,5),some (identDom 2 3,5)]
lemma S_13_ok : btAll (fun o => ∀ p, o = some p → Slice r_13 g_13 p.1 p.2) S_13 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (forall_cons (fun _ h => by cases h; exact sl_13_4) (forall_cons (fun _ h => by cases h; exact sl_13_5) (forall_cons (fun _ h => by cases h; exact sl_13_6) (forall_cons (fun _ h => by cases h; exact sl_13_7) (forall_cons (fun _ h => by cases h; exact sl_13_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_13 : BT (Option PoolSpec) := btOfList 7 [q 1 [16428,16429,49295],q 1 [],q 2 [],q 0 [],q 0 [16396,16397,110615],q 1 [12332,12333,241899],q 0 [16397,110603],q 1 [16397,110603],q 2 [16396,20481],q 0 [12316,12317],q 7 [],q 4 [],q 8 [],q 0 [16413,57355],q 3 [16489],q 3 [],q 1 [16428,12431],q 6 [],q 0 [16412,8529],q 4 [122894],q 0 [16412,12625],q 1 [12299,105],q 0 [16396,20489],q 3 [20489],q 1 [16385,131083],q 0 [12319,8349],q 0 [12299,28777],q 0 [12318,12319],q 5 [],q 0 [12318,8437],q 0 [16397,110620],q 0 [16412,16413],q 0 [16396,20509],q 0 [131077,57356],q 1 [16385,57356],q 0 [16413,57356],q 1 [16413,57356],q 0 [16396,16397],q 1 [9],q 0 [16413,57359],q 0 [16393,122892],q 3 [16393],q 0 [16414,16415],q 1 [12291,45223],q 0 [16393,122908],q 1 [16385,131119],q 0 [16396,20510],q 1 [16397,110639],q 0 [16398,16399],q 2 [12295,117],q 1 [16396,16397,110615],q 2 [16396,16397,110615],q 0 [16389,303115],q 0 [131077,57355],q 3 [16389],q 4 [12299],q 0 [16389,303116],q 0 [16399],q 1 [16398,16399],q 2 [16398,16399],q 2 [16397],q 4 [110603],q 0 [16396],q 1 [16396,20481],q 3 [20481],q 1 [16396,20489],q 1 [16396,16397],q 2 [16396,16397],q 0 [131084],q 1 [16385,131084],q 2 [16385,131084],q 0 [131083],q 2 [16385],q 0 [16389],q 1 [16385],q 2 [16398],q 1 [12299],q 2 [12295],q 0 [12299],q 2 [16489],q 2 [105],q 0 [16395],q 2 [93],q 2 [4097],q 0 [12318],q 0 [12317],q 0 [8221],q 0 [16413],q 0 [16397],q 0 [8222],q 0 [12316],q 1 [12316],q 0 [16393],q 0 [8197],q 1 [12335],q 1 [8222],q 0 [131077],q 1 [8221],q 0 [4105],q 1 [16431],q 2 [12335],q 0 [16412],q 2 [16490],q 1 [16413],q 0 [16414],q 1 [16414],q 0 [12297],q 0 [16398],q 0 [372747],q 2 [12289],q 1 [16399],q 2 [16399],q 1 [16398],q 1 [16397],q 1 [16396],q 2 [16396],q 1 [16395],q 1 [12289]]
def B_13_2 : BT (List (List Nat)) := BT.empty
lemma B_13_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 2 xs.toFinset) B_13_2 := .empty
def U_13_3 : List Nat := []
def P_13_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_13 r_13 S_13 ps_13 U_13_3
def N_13_3 : List NodeSpec := [([0,1,6,9],[],[]),([7,10,13,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_3 : checkNodesBT W_13 g_13 F_13 P_13_3 A_13 B_13_2 3 N_13_3 = true := by decide +kernel
def B_13_3 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_3
set_option maxRecDepth 500000 in
lemma B_13_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 3 xs.toFinset) B_13_3 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_2_ok C_13_3
def U_13_4 : List Nat := (r 0 6)
def P_13_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_13 r_13 S_13 ps_13 U_13_4
def N_13_4 : List NodeSpec := [([15,18,0,1,4],[],[]),([18,0,1,19,4],[],[]),([15,0,1,20,4],[],[]),([0,1,22,2,4],[],[]),([23,0,1,3,25],[],[]),([26,0,1,28,4],[],[]),([0,31,11,3,4],[],[]),([33,34,1,3,4],[],[]),([0,1,10,13,4],[],[0]),([36,0,1,2,3],[0],[]),([37,1,2,13,4],[],[]),([0,38,11,3,4],[1],[]),([0,1,40,4,27],[],[]),([42,1,10,3,4],[2],[]),([26,0,8,11,4],[],[]),([43,0,1,40,4],[],[]),([44,10,11,3,4],[],[]),([24,45,0,3,4],[],[]),([33,0,1,47,4],[],[]),([48,7,10,3,4],[3],[]),([33,0,49,3,4],[],[]),([44,50,0,2,3],[],[]),([7,10,3,4,12],[3],[0]),([8,10,11,3,4],[],[]),([51,0,1,3,4],[],[]),([24,53,0,3,4],[],[]),([54,0,1,7,2],[4],[]),([24,0,55,3,4],[],[]),([57,0,1,3,4],[],[]),([18,0,1,3,4],[],[]),([0,1,2,5,9],[],[0]),([0,1,8,6,4],[],[0]),([60,0,1,2,4],[5],[]),([61,0,1,40,4],[],[]),([33,62,1,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_4 : checkNodesBT W_13 g_13 F_13 P_13_4 A_13 B_13_3 4 N_13_4 = true := by decide +kernel
def B_13_4 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_4
set_option maxRecDepth 500000 in
lemma B_13_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 4 xs.toFinset) B_13_4 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_3_ok C_13_4
def U_13_5 : List Nat := (r 1 4++r 6 51)
def P_13_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_13 r_13 S_13 ps_13 U_13_5
def N_13_5 : List NodeSpec := [e5 [64] [6],([65,63,0,1,3,4],[7],[]),([63,0,64,1,3,4],[6],[]),e5 [67] [8],e5 [44] [],([0,1,8,2,68,4],[9],[4]),([0,1,69,11,3,4],[1,10],[]),([0,1,16,3,4,30],[11],[]),e5 [70] [],([0,1,72,11,3,4],[1,11],[]),e5 [73] [],([24,23,0,1,3,4],[],[0,2]),([0,11,3,4,74,30],[1,11],[]),([67,1,2,3,66,4],[8],[]),([0,1,40,3,4],[],[0]),([61,29,0,7,2,4],[],[]),([21,0,1,8,2,4],[],[0]),([24,0,1,3,52,4],[12],[0,2]),([18,0,1,7,3,4],[13],[]),([33,0,1,3,4,30],[2],[0]),e5 [75] [],([43,26,0,1,2,76],[11,14],[]),([26,0,1,77,10,4],[15],[]),([43,48,0,1,2,4],[11],[3]),([26,0,1,8,2,4],[2],[0,2]),([78,0,1,2,11,4],[16],[]),([79,0,1,10,3,4],[3],[]),([37,1,2,3,4,12],[],[0,2,3,4]),([26,0,80,11,3,4],[1],[]),u5 [9] [1,2,3,17],([0,1,10,3,4,12],[3],[0]),e5 [81] [],e5 [82] [15],a5 [17] [15,17] [0,1,3],([48,0,1,10,3,4],[3],[0]),e5 [83] [],([0,1,7,85,3,4],[18],[]),([24,29,0,2,3,4],[],[]),e5 [86] [],([0,1,87,10,3,30],[],[]),([0,7,11,3,4,30],[],[0,2]),e5 [89] [],([26,0,7,11,3,4],[],[0,2,4]),([0,1,10,3,4,76],[3],[]),([0,1,2,3,76,30],[2,12,19],[]),([44,0,2,11,3,4],[2],[0]),([0,1,7,2,90,4],[20],[]),e5 [92] [17],([24,0,7,11,3,4],[1,2],[]),([63,0,1,10,3,4],[3],[]),([26,0,1,10,4,27],[],[0]),e5 [95] [],([48,0,1,2,4,27],[],[3]),e5 [96] [],([26,33,0,1,3,4],[15],[0]),([0,34,1,11,3,4],[21],[]),e5 [98] [],([0,1,3,6,99,4],[12,22,23],[]),e5 [100] [],([33,1,7,2,3,4],[1,24],[]),([0,1,7,40,3,4],[17,25],[0]),([0,1,8,2,5,4],[10,17],[0]),([26,29,0,11,3,4],[1,2,15],[]),e5 [103] [],e5 [104] [2,26],e5 [106] [],([61,39,0,1,2,4],[27],[0,4]),([0,1,10,3,6,4],[3,12,23],[]),([0,1,107,10,3,4],[3,15],[]),([26,0,1,16,3,4],[15],[]),([43,26,0,1,10,4],[28],[]),([44,0,7,2,3,74],[11],[]),([24,0,1,16,3,4],[3],[0,2]),([0,1,7,108,3,4],[29],[]),a5 [109] [15,30] [1,3],([0,1,84,2,3,14],[31],[4]),([111,0,1,11,3,4],[1,15],[3]),([33,0,1,3,4,46],[3],[0,1]),e5 [112] [],e5 [113] [17,32],e5 [114] [],([0,1,8,2,52,4],[2],[]),([18,0,1,3,4],[],[]),([0,1,2,19,4,32],[33,34],[1]),([24,0,2,3,4,74],[],[]),e5 [18] [],([18,0,1,3,4,14],[2],[0]),([0,1,2,19,4],[35,36],[4,5]),e5 [19] [],([0,1,7,2,5,27],[37],[0]),([7,10,11,3,4],[1,2,3,38],[0,1,2,3,4]),([0,1,2,19,4,14],[15],[0,1,3,4]),([15,0,1,2,4,14],[17],[0]),([15,0,1,7,2,4],[39],[]),([44,0,1,2,3,14],[3],[0,2]),([33,0,1,10,3,4],[3],[1]),([0,1,7,2,19,4],[35],[]),([43,0,34,1,2,4],[],[]),e5 [116] [],([33,1,10,3,4,32],[2],[]),([111,0,1,10,3,4],[3,15],[]),e5 [117] [1,2,3,17],([0,1,10,118,3,4],[3,40,41],[]),([0,1,72,10,3,4],[3],[1]),u5 [14] [2,15,17],([44,119,0,1,2,3],[42],[4]),([24,0,1,10,3,4],[3],[0]),a5 [42] [1,2,15,43] [0,1],a5 [38] [1,11,44] [0,2],e5 [120] [45],([0,1,77,11,3,4],[1],[1]),e5 [121] [3,46],e5 [122] [],([0,1,7,3,6,4],[22,23],[0]),e5 [124] [17],e5 [65] [47],([63,0,1,7,3,4],[6],[]),([43,21,0,1,7,2],[48],[0]),u5 [56] [2,15],([0,1,69,3,4,30],[11],[4]),e5 [126] [49],([0,34,1,2,4,27],[],[]),u5 [127] [15,17],a5 [128] [] [4],([54,0,1,2],[4,28,50,51],[0,1,3]),e5 [8] [],([26,0,1,2,129,4],[15],[]),e5 [131] [52],([18,0,1,3,4,32],[53],[]),([44,0,1,2,3,32],[3],[0]),u5 [25] [],([26,0,11,3,4,74],[1,54,55],[1]),e5 [132] [],e5 [134] [56]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_5 : checkNodesBT W_13 g_13 F_13 P_13_5 A_13 B_13_4 5 N_13_5 = true := by decide +kernel
def B_13_5 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_5
set_option maxRecDepth 500000 in
lemma B_13_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 5 xs.toFinset) B_13_5 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_4_ok C_13_5
def U_13_6 : List Nat := ([1,2,3,6,7,8,10,11,12,14,15,17]++r 21 4++[28,37,38,41,48,55]++r 57 53)
def P_13_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_13 r_13 S_13 ps_13 U_13_6
def N_13_6 : List NodeSpec := [a5 [88] [1,2,11,15,57] [0,1,3,5],([43,21,0,1,2],[28,48,58,59],[0,1,3]),a5 [63] [1,2,3,6,7,15,28,60] [0,2],([63,0,1,3,4],[6,7,15,28,61],[0,2]),a5 [66] [8,28,62,63,64] [0,1,3,5],([0,1,3,6,4],[22,23,28,65],[0,2,4,5]),e5 [135,32] [3,11,17,28],([0,1,2,5,27],[11,15,37,66,67],[0,1,3]),a5 [135] [1,2,10,11,12,17,28,68,69,70] [2,3,4,5],u5 [33,32] [2,3,11,71,72],a5 [33] [1,3,12,15,24,71,72] [0,2,5],a5 [32,74] [73,74] [1,3,4],([43,26,0,1,2,4],[2,11,28,75],[0,2]),([26,0,1,2,4,27],[11,15,28,55,60],[0,2]),u5 [26,29] [2,10,12,76,77],a5 [26,32] [3,12,72,78] [0,2,3,4],u5 [26,76] [2,12,14,28],a5 [76] [1,3,12,14,28,79] [0,1,2,3],a5 [26,34] [15,17,78,80] [2],a5 [136] [1,11,28,81,82] [0,1,3],u5 [79,30] [12,28],a5 [61,7] [1,3,15,83,84] [0,2],a5 [7,68] [15,17,85] [0,1,3],a5 [7,16] [83,86] [0,1,3],a5 [7,14] [11,83,87] [0,1,3],a5 [26,7] [1,2,3,12,15,78,83] [0,1,2,3,4],a5 [7,27] [1,15,83,88] [0,1,3,4],a5 [24,7] [1,2,3,83,89] [0,2],a5 [8] [1,2,3,11,12,17,90,91] [0,1,3,4],([0,1,10,3,4,30],[2,11,41,92],[0,1,2,3,4,5]),a5 [48,11] [10,15,93,94] [0,1,3],a5 [24] [1,3,11,12,15,83,89,95] [0,2,4],a5 [32,14] [28,72,74,96] [0,1,3],a5 [16] [11,15,17,83,86,97] [0,1,3],a5 [8,7] [1,15,17,90] [0,1,3],([26,0,1,10,3,4],[2,3,15,55,78],[0,1,2]),a5 [7,5] [1,11,15,62,83] [0,1,3],([0,1,10,11,3,4],[2,38,98],[0,1,2,3]),a5 [71,11] [11,99] [0,1,3],a5 [48] [3,10,11,94,100] [0,1,3],a5 [84,7] [1,11,83,101] [0,1,3,4],a5 [79] [1,3,10,12,17,28,102] [0,2],a5 [14] [2,15,17,87,103] [0,1,3,4,5],a5 [44] [1,2,3,15,104,105] [0,2,4],a5 [44,7] [1,3,11,104] [0,2],a5 [7,52] [1,2,15,83,106] [0,4,5],a5 [43,7] [1,3,17,28,107] [0,1,3,4],a5 [21,7] [1,3,15,57] [0,1,3],a5 [23,7] [1,2,3,11,81,83] [0,1,3,4],a5 [111] [1,3,11,15,28,108,109] [0,2],a5 [7,30] [1,2,83,92] [0,1,2,3,4],a5 [34] [11,17,21,78,80] [0,1,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_6 : checkNodesBT W_13 g_13 F_13 P_13_6 A_13 B_13_5 6 N_13_6 = true := by decide +kernel
def B_13_6 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_6
set_option maxRecDepth 500000 in
lemma B_13_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 6 xs.toFinset) B_13_6 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_5_ok C_13_6
def U_13_7 : List Nat := ([1,2,3,11,12,15,28,57,60,62,72,74,75,76,78,81,83,88,107]++r 109 9)
def P_13_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_13 r_13 S_13 ps_13 U_13_7
def N_13_7 : List NodeSpec := [a5 [21] [1,2,3,11,15,57,110,111] [0,1,2,3,4],a5 [43] [1,2,3,28,75,107,112] [0,1,3],a5 [27] [1,2,3,15,28,60,88,113] [0,1,3],a5 [5] [1,2,3,11,15,28,62,114,115] [0,1,2,3,4],a5 [23] [1,2,3,11,15,28,81,116] [0,2],a5 [26] [1,2,3,11,12,15,28,76,78] [0,2],a5 [91] [3,15,28,109,117] [0,1,3],a5 [32] [3,28,72,74] [0,1,3,5],a5 [7] [1,2,3,11,15,83] [0,1,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_7 : checkNodesBT W_13 g_13 F_13 P_13_7 A_13 B_13_6 7 N_13_7 = true := by decide +kernel
def B_13_7 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_7
set_option maxRecDepth 500000 in
lemma B_13_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 7 xs.toFinset) B_13_7 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_6_ok C_13_7
def U_13_8 : List Nat := [1,2,3]
def P_13_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_13 r_13 S_13 ps_13 U_13_8
def N_13_8 : List NodeSpec := [a5 [] [1,2,3] [0,1,2,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_8 : checkNodesBT W_13 g_13 F_13 P_13_8 A_13 B_13_7 8 N_13_8 = true := by decide +kernel
def B_13_8 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_8
set_option maxRecDepth 500000 in
lemma B_13_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 8 xs.toFinset) B_13_8 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_7_ok C_13_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck r_13 g_13 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT B_13_8 r_13 = true := by decide +kernel
lemma low_13 : Lower r_13 g_13 9 := lower_of_forestBT root_13_ok B_13_8_ok root_13_in
def g_14 := (d 0xfefce800fefce800)
def r_14 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 8 := by
  have hc : Lower (varsOf 23) (d 0xfefee8e8fefee8e8) 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 8) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) hc
def g_15 := (d 0xfe800000fe800000)
def r_15 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 7 := by
  exact lift_of_f (z := 0) (o := 16) (other := r_2) (G := g_2) (essPairs := [(VAR 4,7,23)]) (by decide +kernel) low_2
def g_16 := (d 0xfc80fc80fc80fc80)
def r_16 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_16 : Lower r_16 g_16 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_17 := (d 0xffe8f000ffe8f000)
def r_17 : List Nat := varsOf 31
def p_17 : List Nat := [12,12,13,13,14,14,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28]
def q_17 : List Nat := [8,4,9,5,10,6,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20]
def F_17 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 4 (mkBase p_17 q_17 r_17) [(0,2,4),(3,5,4),(2,2,3),(1,2,3),(3,1,4),(0,0,4),(2,0,3),(1,1,3)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^256) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_17 : BT (List (Nat × Nat)) := btOfList 1 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xffa0f000ffa0f000) 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0f000ffc0f000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_10
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
def S_17 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 1 0,5),some (subcubeFast 8 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_17 : BT (Option PoolSpec) := btOfList 4 [q 0 [],q 5 [],q 4 [],q 3 [],q 1 [],q 2 [],q 6 [],q 3 [16391],q 0 [16391],q 1 [16384],q 2 [16384],q 1 [12290],q 2 [12290],q 3 [12293],q 0 [12293]]
def B_17_4 : BT (List (List Nat)) := BT.empty
lemma B_17_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 4 xs.toFinset) B_17_4 := .empty
def U_17_5 : List Nat := [0,1,2]
def P_17_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_5
def N_17_5 : List NodeSpec := [([6,0,1,5,2,3],[0,1],[]),([7,0,1,2,8,4],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_5 : checkNodesBT W_17 g_17 F_17 P_17_5 A_17 B_17_4 5 N_17_5 = true := by decide +kernel
def B_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_5
set_option maxRecDepth 500000 in
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_4_ok C_17_5
def U_17_6 : List Nat := (r 0 15)
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_6
def N_17_6 : List NodeSpec := [u5 [6] (r 0 7),u5 [7] ([0]++r 2 5),u5 [8] ([0]++r 2 5),([9,0,2,3,4],(r 5 4),[]),([10,1,2,3,4],[3,6,9,10],[]),u5 [5] ([0]++r 3 4),([11,1,2,3,4],[0,3,6,11,12],[]),([0,2,3,12,4],[2,5,6,13,14],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6 = true := by decide +kernel
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_5_ok C_17_6
def U_17_7 : List Nat := (r 0 7)
def P_17_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_7
def N_17_7 : List NodeSpec := [a5 [] (r 0 7) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7 = true := by decide +kernel
def B_17_7 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_7
set_option maxRecDepth 500000 in
lemma B_17_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 7 xs.toFinset) B_17_7 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_6_ok C_17_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,18,19),(VAR 1,17,19),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_7 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 8 := lower_of_forestBT root_17_ok B_17_7_ok root_17_in
def g_18 := (d 0xfffeffe8fe800000)
def r_18 : List Nat := varsOf 63
def p_18 : List Nat := [23,23,23,23,25,25,25,26,26,26,27,27,28,28,28,29,29,30,30,31,35,35,35,37,37,37,38,38,38,39,40,40,41,41,42,42,43,44,44,45,46,47,49,49,49,50,50,50,51,52,52,52,53,54,56,56]
def q_18 : List Nat := [22,21,19,7,24,17,9,24,18,10,19,11,24,20,12,21,13,22,14,15,34,33,3,36,33,5,36,34,6,7,32,8,33,9,34,10,11,36,12,13,14,15,48,33,17,48,34,18,19,48,36,20,21,22,48,24]
def F_18 : Nat := fullMask 56
set_option maxHeartbeats 0 in
lemma gp_18 : goodPairs g_18 p_18 q_18 := goodPairs_of (by decide +kernel)
def W_18 : BT Decor := buildWiresBT 8 (mkBase p_18 q_18 r_18) [(1,1,2),(1,0,3),(0,7,4),(0,1,2),(1,9,3),(0,4,5),(1,10,11),(0,2,4),(1,0,1),(3,13,14),(0,0,1),(1,16,3),(1,3,5),(0,4,18),(1,17,11),(3,3,20),(1,3,11),(0,2,5),(1,2,5),(3,23,24),(2,25,16),(2,7,11),(0,0,4),(3,0,5),(1,29,3),(3,13,18),(3,13,5),(3,28,5),(1,33,3),(3,3,4),(3,29,4),(1,9,11),(3,25,0),(1,38,1),(0,1,5),(1,1,5),(3,40,41),(2,42,2),(3,42,2),(0,25,0),(1,25,0),(2,1,2),(1,47,28),(2,2,1),(1,49,3),(1,2,11),(0,25,4),(3,2,4),(3,53,14),(3,54,18),(2,0,1),(1,56,13),(3,2,5),(1,58,3),(3,16,18),(3,25,1),(3,61,0),(3,9,34),(3,9,18),(1,28,3),(1,2,3),(2,66,11),(1,67,16),(1,16,11),(1,0,11),(1,0,10),(0,71,4),(1,2,0),(2,2,11),(1,74,3),(1,16,13),(3,76,18),(1,32,3),(0,6,18),(2,0,2),(1,80,11),(3,3,81),(2,14,11),(1,83,3),(0,0,5),(1,85,3),(1,49,11),(0,66,4),(1,28,10),(3,10,4),(0,42,4),(3,25,4),(3,3,5),(1,53,16),(1,85,10),(0,1,4),(2,25,96),(0,7,5),(1,9,98),(1,13,3),(1,9,19),(3,3,70),(3,58,4),(1,0,37),(3,2,69),(1,0,22),(1,1,22),(1,0,19),(1,1,19),(0,4,41),(1,0,110),(1,2,110),(1,96,3),(1,85,113),(2,0,3),(1,1,11),(1,1,3),(0,117,4),(1,0,118),(1,2,118),(1,23,3),(3,29,117),(1,40,3),(1,80,3),(1,124,11),(2,2,0),(3,126,116),(3,1,5),(3,128,4),(1,0,5),(0,4,130),(1,47,131),(1,56,53),(1,80,19),(3,96,18),(3,96,5),(1,136,3),(1,47,8),(2,14,22),(2,0,22),(2,0,11),(2,6,11),(1,141,3),(2,14,19),(3,23,4),(2,14,121),(3,53,5),(1,147,3),(3,9,130),(0,4,24),(2,2,3),(3,151,5),(1,9,85),(3,0,4),(3,154,6),(1,2,69),(2,0,10),(0,66,5),(2,0,19),(1,2,17),(0,160,4),(2,117,11),(0,6,4),(1,85,163),(2,0,5),(1,128,3),(1,115,11),(1,155,3),(0,14,18),(1,9,8),(1,13,85),(1,13,17),(1,85,118),(1,16,19),(1,9,28),(2,14,3),(1,16,150),(1,9,131),(2,14,100),(3,121,4),(3,9,70),(1,0,121),(3,35,5),(1,47,3),(0,6,5),(1,185,3),(0,0,186),(2,0,186),(2,2,5),(3,189,14),(3,1,4),(1,191,58),(1,165,53),(3,40,4),(1,191,3),(1,53,85),(2,0,100),(2,0,88),(1,1,8),(3,154,41),(1,1,65),(3,154,117),(3,154,18),(1,56,58),(2,1,5),(1,205,80),(3,126,41),(1,47,85),(0,117,5),(3,126,117),(3,126,18),(3,126,5),(1,212,3),(3,126,4),(1,56,3),(3,13,7),(1,189,16),(3,9,7),(3,23,7),(1,96,85),(2,4,5),(3,9,5),(1,58,16),(3,16,4),(3,154,5),(1,225,3),(3,9,4),(2,0,150),(1,222,3),(2,0,121),(1,1,86),(3,151,4),(3,189,4),(1,1,131),(0,14,5),(1,235,3),(2,1,3),(3,237,4),(0,14,66),(3,237,5),(1,58,28),(3,23,14),(3,13,130),(1,53,3),(3,29,6),(1,205,28),(0,14,24),(0,14,4),(2,1,0),(3,249,4)]
lemma W_18_ok : btAll (fun x => faithful p_18 q_18 x ∧ x.1 < 2^256) W_18 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_18 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_18 : BT (List (Nat × Nat)) := btOfList 3 al_18
set_option maxHeartbeats 0 in
lemma A_18_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_18 = g_18) A_18 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_18_0 : Slice r_18 g_18 (subcubeFast 8 0) 9 := by
  have hc : Lower (varsOf 55) (d 0xfefee8e880800000) 9 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_1 : Slice r_18 g_18 (subcubeFast 0 16) 9 := by
  have hc : Lower (varsOf 47) (d 0xfffefffefe80fe80) 9 := carry_of (swaps := [(4,5)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_2 : Slice r_18 g_18 (subcubeFast 0 32) 8 := by
  have hc : Lower (varsOf 31) (d 0xfffeffe8fffeffe8) 8 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 0) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_3 : Slice r_18 g_18 (subcubeFast 1 0) 8 := by
  have hc : Lower (varsOf 62) (d 0xfffcffc0fc000000) 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(4,5)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_4 : Slice r_18 g_18 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffaffa0fa000000) 8 := carry_of (swaps := [(1,5),(2,5),(4,5)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_5 : Slice r_18 g_18 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) (d 0xffeeff88ee000000) 8 := carry_of (swaps := [(2,5),(4,5)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_6 : Slice r_18 g_18 (subcubeFast 8 32) 7 := by
  have hc : Lower (varsOf 23) (d 0xfefee8e8fefee8e8) 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 8) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_7 : Slice r_18 g_18 (subcubeFast 0 1) 8 := by
  have hc : Lower (varsOf 62) (d 0xfffffffcffc00000) 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_8 : Slice r_18 g_18 (subcubeFast 0 4) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffffeeff880000) 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_9 : Slice r_18 g_18 (subcubeFast 0 2) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffffffaffa00000) 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_10 : Slice r_18 g_18 (identDom 3 4) 9 := by
  have hc : Lower (varsOf 47) (d 0xffe8ffe8fe00fe00) 9 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_13
  exact slice_ident (u := 3) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_11 : Slice r_18 g_18 (identDom 0 1) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffaffaafaa00000) 8 := carry_of (swaps := [(0,1),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_12 : Slice r_18 g_18 (identDom 0 2) 8 := by
  have hc : Lower (varsOf 59) (d 0xffeeffaaee880000) 8 := carry_of (swaps := [(0,1),(2,5),(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_13 : Slice r_18 g_18 (identDom 1 2) 8 := by
  have hc : Lower (varsOf 59) (d 0xffeeffccee880000) 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_14 : Slice r_18 g_18 (subcubeFast 32 0) 7 := by
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) low_15
set_option maxHeartbeats 0 in
lemma sl_18_15 : Slice r_18 g_18 (identDom 1 3) 8 := by
  have hc : Lower (varsOf 55) (d 0xfefeececcccc0000) 8 := carry_of (swaps := [(1,3),(2,3),(3,5),(4,5)]) (by decide +kernel) low_17
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_16 : Slice r_18 g_18 (subcubeFast 8 4) 6 := by
  have hc : Lower (varsOf 51) (d 0xffffeeee88880000) 6 := carry_of (swaps := [(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_17 : Slice r_18 g_18 (subcubeFast 8 2) 6 := by
  have hc : Lower (varsOf 53) (d 0xfffffafaa0a00000) 6 := carry_of (swaps := [(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_18 : Slice r_18 g_18 (subcubeFast 8 16) 6 := by
  have hc : Lower (varsOf 39) (d 0xfefefefe80808080) 6 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_19 : Slice r_18 g_18 (subcubeFast 8 1) 6 := by
  have hc : Lower (varsOf 54) (d 0xfffffcfcc0c00000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_20 : Slice r_18 g_18 (subcubeFast 32 16) 6 := by
  exact slice_fast_direct_f (z := 32) (o := 16) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_18_21 : Slice r_18 g_18 (subcubeFast 6 1) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_22 : Slice r_18 g_18 (subcubeFast 5 2) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_23 : Slice r_18 g_18 (subcubeFast 3 4) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_24 : Slice r_18 g_18 (subcubeFast 3 16) 4 := by
  have hc : Lower (varsOf 44) (d 0xfff0fff0f000f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_25 : Slice r_18 g_18 (subcubeFast 5 16) 4 := by
  have hc : Lower (varsOf 42) (d 0xffccffcccc00cc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_26 : Slice r_18 g_18 (subcubeFast 9 32) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_27 : Slice r_18 g_18 (subcubeFast 6 16) 4 := by
  have hc : Lower (varsOf 41) (d 0xffaaffaaaa00aa00) 4 := carry_of (swaps := [(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_28 : Slice r_18 g_18 (subcubeFast 10 32) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 10) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_29 : Slice r_18 g_18 (subcubeFast 12 32) 4 := by
  have hc : Lower (varsOf 19) (d 0xeeee8888eeee8888) 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_30 : Slice r_18 g_18 (subcubeFast 24 32) 4 := by
  exact slice_fast_direct_f (z := 24) (o := 32) (by decide +kernel) low_0
def S_18 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 8 0,9),some (subcubeFast 0 16,9),some (subcubeFast 0 32,8),some (subcubeFast 1 0,8),some (subcubeFast 2 0,8),some (subcubeFast 4 0,8),some (subcubeFast 8 32,7),some (subcubeFast 0 1,8),some (subcubeFast 0 4,8),some (subcubeFast 0 2,8),some (identDom 3 4,9),some (identDom 0 1,8),some (identDom 0 2,8),some (identDom 1 2,8),some (subcubeFast 32 0,7),some (identDom 1 3,8),some (subcubeFast 8 4,6),some (subcubeFast 8 2,6),some (subcubeFast 8 16,6),some (subcubeFast 8 1,6),some (subcubeFast 32 16,6),some (subcubeFast 6 1,4),some (subcubeFast 5 2,4),some (subcubeFast 3 4,4),some (subcubeFast 3 16,4),some (subcubeFast 5 16,4),some (subcubeFast 9 32,4),some (subcubeFast 6 16,4),some (subcubeFast 10 32,4),some (subcubeFast 12 32,4),some (subcubeFast 24 32,4)]
lemma S_18_ok : btAll (fun o => ∀ p, o = some p → Slice r_18 g_18 p.1 p.2) S_18 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_18_0) (forall_cons (fun _ h => by cases h; exact sl_18_1) (forall_cons (fun _ h => by cases h; exact sl_18_2) (forall_cons (fun _ h => by cases h; exact sl_18_3) (forall_cons (fun _ h => by cases h; exact sl_18_4) (forall_cons (fun _ h => by cases h; exact sl_18_5) (forall_cons (fun _ h => by cases h; exact sl_18_6) (forall_cons (fun _ h => by cases h; exact sl_18_7) (forall_cons (fun _ h => by cases h; exact sl_18_8) (forall_cons (fun _ h => by cases h; exact sl_18_9) (forall_cons (fun _ h => by cases h; exact sl_18_10) (forall_cons (fun _ h => by cases h; exact sl_18_11) (forall_cons (fun _ h => by cases h; exact sl_18_12) (forall_cons (fun _ h => by cases h; exact sl_18_13) (forall_cons (fun _ h => by cases h; exact sl_18_14) (forall_cons (fun _ h => by cases h; exact sl_18_15) (forall_cons (fun _ h => by cases h; exact sl_18_16) (forall_cons (fun _ h => by cases h; exact sl_18_17) (forall_cons (fun _ h => by cases h; exact sl_18_18) (forall_cons (fun _ h => by cases h; exact sl_18_19) (forall_cons (fun _ h => by cases h; exact sl_18_20) (forall_cons (fun _ h => by cases h; exact sl_18_21) (forall_cons (fun _ h => by cases h; exact sl_18_22) (forall_cons (fun _ h => by cases h; exact sl_18_23) (forall_cons (fun _ h => by cases h; exact sl_18_24) (forall_cons (fun _ h => by cases h; exact sl_18_25) (forall_cons (fun _ h => by cases h; exact sl_18_26) (forall_cons (fun _ h => by cases h; exact sl_18_27) (forall_cons (fun _ h => by cases h; exact sl_18_28) (forall_cons (fun _ h => by cases h; exact sl_18_29) (forall_cons (fun _ h => by cases h; exact sl_18_30) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_18 : BT (Option PoolSpec) := btOfList 11 [q 7 [8196,12325,8197],q 2 [8196,12325,8197],q 10 [8196,12325,8197,20496],q 3 [20488,20489,98399],q 7 [20488,20489,98399,65638],q 6 [4096,4097,65638],q 23 [],q 21 [],q 2 [8196,8197,45093],q 29 [],q 9 [20488,20489,98399],q 8 [20484,20485,168099],q 13 [],q 5 [20484,20485,168099],q 0 [20484,20485,168099,8362,8363],q 6 [8362,8363],q 12 [],q 7 [20488,20489,98399],q 0 [20488,20489,98399,100,101],q 6 [100,101],q 5 [20496],q 1 [4106,12485,45065,45069],q 1 [4097,20488,20489,98399],q 25 [],q 1 [4098,53473],q 4 [20488,20489,98399],q 0 [20488,20489,98399,4199,247],q 6 [4199,247],q 3 [],q 4 [],q 0 [20488,20489,98399],q 6 [4096,65638],q 0 [4096,4097,20496,45121],q 2 [4096,4097,45121,282639],q 1 [4096,4097,45121,282639],q 1 [8196,8197,45093,45069],q 0 [8196,8197,20496,45093],q 1 [8196,8197,45093,45057],q 7 [20496,45121,282639],q 1 [8196,8197,45093],q 11 [12297,20496,45069],q 5 [4096,4097],q 10 [4096,4097],q 10 [8196,12325,20496],q 0 [8196,8197],q 10 [8196,12325,8197],q 0 [],q 2 [8196,12325,8197,45097],q 28 [],q 2 [8196,12325,8197,45069],q 1 [8196,12325,8197,45069],q 22 [],q 4 [20493,73744],q 5 [20493,73744],q 7 [8196,12325],q 7 [],q 11 [16392,20493,73783],q 8 [4096,12353,4097],q 1 [4096,12353,4097,20493],q 27 [],q 6 [],q 14 [],q 3 [8196,12325,8197],q 24 [],q 8 [12325,20480,12629],q 8 [12325,20483,12405],q 8 [12325,20496,45069],q 1 [8196,12325,8197,12289],q 8 [12325,12289,16412],q 1 [4106,12297,45253,45069],q 11 [12297,16648,20496],q 8 [4096,4097],q 2 [4096,4097],q 0 [4096,4097],q 8 [4096,12353],q 10 [4096,12353,20496],q 2 [4096,12353],q 1 [8196,12325,8197],q 8 [12325,12289],q 8 [12325,12289,16384],q 1 [20484,20485,168099,8362],q 30 [],q 0 [8196,8197,20496,45097],q 8 [12325,20496,45097],q 1 [8196,12325,8197,45097],q 6 [8196,8197,45097],q 8 [12325,16384,12401],q 0 [8196,8197,16384],q 1 [8196,12325,8197,12401],q 0 [4096,4097,16392,53306],q 1 [4096,4097,53306],q 0 [4096,4097,16395,65749],q 18 [4096,4097],q 10 [4096,12353,4097],q 6 [4096,4097],q 7 [16395,65749],q 8 [12325,20480,41301],q 8 [12325,20493],q 1 [8196,12325,8197,20493],q 13 [12289,20496,45086],q 8 [12325,20493,73744],q 20 [],q 6 [16388,393318],q 1 [20488,20489,98399,393318],q 2 [8196,45093],q 20 [8196,8197],q 8 [12289,20508,401445],q 0 [8196,8197,20508,401445],q 11 [16392,12341,20493],q 14 [4096,4097],q 11 [16392,20535,20493],q 11 [16392,20535,12417],q 0 [4096,4097,16392,57399],q 1 [4096,12353,4097,57399],q 8 [20493,73744,77861],q 0 [8196,8197,73744,77861],q 2 [8196,8197,77861],q 1 [8196,8197,20493,77861],q 11 [16392,20491,12521],q 1 [4096,4097],q 11 [16392,20493,73744],q 11 [20491,16619,16399],q 0 [4096,4097,20488,20489,98399],q 11 [20488,20489,98399],q 7 [20496,45069,90117],q 3 [20496,45069],q 4 [20496,45069],q 9 [],q 2 [45069,90117],q 2 [45069,90113],q 0 [20496,45057],q 7 [20496,45069],q 9 [20496,45069],q 8 [20496,45069],q 1 [45057,45069,286735],q 6 [45057],q 7 [20493,73744,77829],q 3 [20493,73744],q 3 [20485,167952],q 5 [20485,167952],q 8 [],q 1 [20488,20489,98399],q 0 [16384,20488,20489,98399],q 6 [16384],q 2 [12629],q 7 [12629],q 9 [20496,45057],q 3 [20496],q 19 [],q 9 [12290],q 3 [20484,20485,168099],q 7 [20484,20485,168099],q 6 [8362],q 1 [20484,20485,168099],q 7 [20496,45061,45069],q 3 [20496,45061],q 10 [20496,45061],q 26 [],q 1 [12289,45061,45069],q 3 [12293,16852],q 5 [12293,16852],q 8 [12289,12381],q 7 [16395,20488,12381],q 9 [16395,20488,12381],q 6 [16395],q 1 [12293,20483,479351],q 4 [12289,16384],q 8 [12289,20484,12449],q 3 [20484,12449],q 7 [20484,12449],q 1 [12289,20484,12449],q 2 [12289,16384,12449],q 5 [20496,45061],q 1 [10,45061,475643],q 0 [8194,20496,45377],q 1 [],q 1 [8194,45377,331791],q 0 [20496],q 1 [8194,45377,45069],q 4 [20496],q 0 [8194],q 12 [20487,16899,16399],q 0 [8194,20484,20485,168099],q 6 [8194],q 12 [20484,20485,168099],q 0 [20484],q 4 [16384,12401],q 1 [12401,20484,12449],q 8 [20484,12449],q 2 [],q 9 [16395],q 0 [4098,16395,217313],q 1 [20493],q 12 [16388,20493,74115],q 12 [16388,20867,20493],q 12 [16388,20867,12833],q 12 [16388,12673,20493],q 4 [8194],q 14 [8194],q 10 [8194],q 8 [4098,53473],q 5 [4098],q 3 [16392,20491],q 4 [16392,53473,20491],q 12 [12293,16852,20496],q 9 [8194],q 2 [8194],q 15 [],q 7 [20496,45061],q 0 [4106,20496,45253],q 5 [],q 1 [4106,12297,45253],q 1 [8194,12609,45069],q 10 [],q 0 [4106,20496,45065],q 10 [20496,45065],q 1 [4106,12485,45065],q 9 [20496,45069,90114],q 8 [20496,45058],q 7 [20496],q 0 [4097,20496,45114],q 1 [4097,45114,12621],q 9 [20496,45058,45069],q 4 [20496,45058],q 7 [20496,45066,12585],q 0 [9,20496,45066],q 1 [9,45066,12585],q 1 [45058,12853,45069],q 0 [4097,20488,20489,98399],q 6 [4097],q 0 [4097],q 7 [20488,16479],q 0 [4096,20488,20489,98399],q 6 [4096],q 1 [8194,45057,45069],q 3 [8196,8197,532519],q 4 [20481],q 7 [8196,8197],q 8 [20481,532519],q 0 [8196,8197,20481,532519],q 6 [8196,8197],q 11 [20496,45069],q 0 [4096,4097,20496],q 1 [4096,4097,45069],q 11 [20488,12381],q 3 [20488,12381],q 0 [4096,4097,20488],q 7 [20488,12381],q 2 [4096,4097,12381],q 11 [20489,98320],q 3 [20489,98320],q 7 [20489,98320],q 1 [4096,4097,20489],q 11 [12298,21087],q 0 [4096,4097,21087],q 3 [12298,21087],q 7 [12298,21087],q 2 [4096,4097,12298],q 16 [4096,4097],q 20 [4096,4097],q 1 [4096,45121,45065],q 3 [8196,8197],q 2 [8196,8197,348197],q 8 [20480,348197],q 0 [8196,8197,20480,348197],q 6 [8196,8197,348197],q 3 [12297,16648],q 4 [12297,16648],q 0 [4096],q 1 [4096,12353,12297],q 10 [4096,12353],q 8 [12325],q 8 [12325,20480],q 0 [8196,8197,20480],q 2 [8194,12609,45069],q 7 [16392,20491],q 11 [16392,20491],q 0 [4096,20496,45121],q 2 [4096,45121],q 1 [4096,45121],q 0 [8194,20496,45057],q 1 [8194,45057,286735],q 11 [16392,20493],q 7 [20493],q 7 [16392],q 1 [4096,4097,20493],q 0 [4096,4097,16392],q 3 [20496,282639],q 4 [20496,282639],q 1 [4096,45121,282639],q 6 [4096,45121],q 1 [4096,45121,45069],q 3 [20496,45086],q 11 [12297,16392],q 3 [12297,16392],q 7 [12297],q 7 [12297,16392],q 2 [4096,4097,12297],q 1 [4096,12353,45069],q 3 [20496,331791],q 6 [8194,45377],q 1 [4096,12353,20493],q 8 [12341,20493],q 5 [20493],q 5 [4096],q 14 [4096],q 10 [4096],q 3 [16392,53306],q 18 [4096],q 1 [20491],q 0 [8197],q 10 [20483,16503],q 18 [20483],q 3 [8197,25195],q 0 [8197,16387,25195],q 11 [16392,20495],q 7 [20495],q 1 [4096,4097,20495],q 0 [8196],q 10 [8196,12325],q 11 [20491,12521],q 3 [20491,12521],q 0 [4096,4097,20491],q 7 [20491,12521],q 2 [4096,4097,12521],q 3 [8196,12325],q 5 [20480,41301],q 5 [4098,217313],q 8 [4098],q 11 [20491,16619],q 3 [20491,16619],q 7 [20491,16619],q 1 [4096,4097,20491],q 3 [8198],q 7 [8198,114877],q 0 [8198,16384,114877],q 1 [8198,114877],q 11 [20491,16399],q 8 [12325,16427],q 1 [12289,45069],q 8 [12325,16399],q 8 [12325,40962],q 4 [12297,16392,53473],q 0 [4098,16392,53473],q 2 [12297],q 20 [4098,53473],q 7 [12353,20491],q 2 [4096,12353,4097],q 1 [4096,12353,4097],q 11 [12297,20496],q 3 [12297],q 1 [4096,4097,12297],q 11 [12297,20744],q 0 [4096,4097,20744],q 3 [12297,20744],q 7 [12297,20744],q 5 [4096,12353],q 3 [16388,12673],q 1 [12673,20480,463189],q 0 [8196,8197,20496],q 8 [12325,20496],q 4 [20488,12381],q 6 [4097,45114],q 18 [20491],q 10 [20491,16619],q 4 [20491,12521],q 10 [20496],q 2 [4096,12353,45069],q 0 [16392,20535],q 2 [16392],q 8 [12325,16384],q 4 [16384],q 9 [12289,20496,45069],q 8 [12289,20496,45069],q 8 [20496,45058,45069],q 10 [20496,45058],q 6 [45058],q 14 [12297,16648],q 10 [4097],q 2 [4097],q 1 [8196,12325],q 1 [12401,20491,12521],q 2 [4096,12353,45125],q 9 [20493,73744,77826],q 9 [20496,45058],q 4 [20496,45526],q 11 [20493,73744],q 0 [4096,4097,73744],q 7 [20493,73744],q 3 [8197,16408],q 1 [8197,20480,667989],q 2 [8197,16408,667989],q 9 [20480,667989],q 8 [20480,667989],q 12 [16388,20493,73744],q 7 [12353,16395],q 0 [4096,4097,16395],q 8 [20496,45093],q 14 [8196,8197],q 2 [8196,8197],q 13 [20482,20483],q 0 [8196,8197,20482,20483],q 4 [20482,20483],q 8 [20482,20483],q 3 [16395],q 4 [16395],q 14 [16395],q 11 [16392,12341],q 3 [16392,12341],q 7 [16392,12341],q 1 [4096,4097,12341],q 1 [8196,20493,73767],q 4 [12801],q 12 [16388,20487,12801],q 1 [8194],q 3 [20493],q 11 [16395,20493],q 7 [16395],q 4 [16392,12341],q 1 [4096,12353,12341],q 2 [16392,12341],q 9 [12290,20496,45517],q 7 [8197,12909],q 1 [8197,25195,12909],q 1 [4096,12353,69641],q 9 [12325,12289],q 5 [12289,16384],q 1 [8197],q 0 [16392,20491],q 16 [],q 1 [4096],q 9 [12325,20493],q 4 [20493],q 1 [8196,12325,20493],q 5 [16384],q 14 [16384],q 11 [12297,16648],q 0 [4096,4097,16648],q 7 [12297,16648],q 10 [4096,4097,20495],q 3 [16399,20495],q 11 [16399,20495],q 3 [20493,73784],q 0 [4096,4097,73784],q 5 [20496,45069],q 12 [12293,20496,45069],q 11 [20496,45065],q 3 [20496,45065],q 1 [4096,4097,45065],q 0 [8196,20496,45093],q 1 [8196,45093],q 2 [4096,4097,45069],q 0 [16395,20484,20485,168099],q 1 [8194,12609,45553],q 1 [8196,12289,32805],q 4 [12289,16412],q 5 [12289,16412],q 0 [8196,16412,32805],q 8 [20480,348213],q 1 [12297,20480,348213],q 2 [12297,16392,348213],q 9 [12297],q 0 [16392,20480,348213],q 6 [16392,348213],q 1 [12289],q 8 [20496],q 5 [16648,20496],q 0 [16648,20496],q 8 [4096],q 2 [4096],q 1 [12293,20480,483669],q 2 [8194,12289,45069],q 1 [8194,12289,45069],q 6 [8196,401445],q 20 [8196],q 4 [12289,20508],q 5 [12289,20508],q 4 [40961],q 0 [8196,8197,40961],q 8 [12325,40961],q 0 [8196,16384,114725],q 6 [100],q 0 [4096,16395,65749],q 11 [20488,20489],q 3 [20488,20489],q 7 [20488,20489],q 17 [],q 9 [16395,65749],q 1 [4096,20493,73795],q 3 [20496,45125],q 4 [20496,45125],q 0 [4096,20496,45125],q 1 [4096,12353,45125],q 6 [4096,45125],q 4 [12297,16392],q 8 [4096,53313],q 0 [4096,16392,53313],q 8 [20493,73783],q 1 [20493,73783],q 4 [20489,98320],q 6 [4096,614465],q 1 [4096,20489,614465],q 0 [4096,73744,77889],q 1 [4096,20493,77889],q 2 [4096,77889],q 2 [4096,45121,282639],q 4 [20496,45057],q 1 [8196,45057,286759],q 2 [12381,16871],q 1 [20488,12381],q 7 [12297,20496,45069],q 5 [4097],q 10 [8197],q 2 [8197],q 7 [8197],q 1 [8196,12325,41073],q 4 [16384,41073],q 5 [16384,41073],q 0 [8196,16384,41073],q 11 [16399,20623],q 0 [4096,4097,20623],q 3 [16399,20623],q 7 [16399,20623],q 1 [4096,4097,20623],q 2 [45069],q 1 [45069],q 8 [12381],q 8 [20493,73744],q 0 [16392,73744],q 10 [20488,16479],q 9 [13029],q 4 [20504,13029],q 8 [13029],q 5 [20504,13029],q 0 [8197,20504],q 3 [20495],q 11 [16395,20495],q 0 [4097,16392,57399],q 1 [4097,57399],q 1 [4096,4097,65749],q 3 [16392,20535],q 7 [16392,20535],q 1 [4096,4097,20535],q 11 [16392,20535],q 3 [20490,58103],q 14 [4097],q 0 [20496,90114],q 1 [45069,90114],q 0 [20496,45058],q 1 [45058,45069],q 5 [20496,45058],q 1 [45058,12853],q 9 [20496],q 14 [12853],q 7 [20496,12853],q 1 [45057,45061],q 8 [20496,45061],q 5 [20496,45057],q 8 [20496,45057],q 0 [20496,45061],q 0 [20483,16503],q 7 [16399],q 6 [16503],q 1 [20482,217749],q 5 [20484,16547],q 8 [20484,16547],q 7 [20484,16547],q 0 [16395,20484,16547],q 2 [16395,16547],q 6 [16395,16547],q 3 [16391,13053],q 7 [16391,13053],q 4 [13053],q 2 [16391,13053],q 0 [16391],q 0 [16391,20491],q 8 [16391,13053],q 1 [13053,20491],q 5 [16391,13053],q 3 [20491],q 7 [20491],q 9 [20491],q 6 [16391],q 0 [16384,73744],q 2 [16388],q 7 [16388],q 1 [20482,20483],q 5 [20482,20483],q 6 [16388],q 1 [20480,348373],q 0 [16395,20480,348373],q 2 [16395,348373],q 6 [16395,348373],q 1 [20484,20485],q 3 [20484,20485],q 8 [20484,20485],q 5 [20484,20485],q 2 [16384,12401],q 1 [12401,20493],q 9 [16384,12401],q 0 [16384],q 8 [16384,12401],q 0 [16384,20491],q 1 [12401],q 1 [12401,20491],q 4 [20491],q 2 [16388,12673],q 4 [20480],q 8 [16388,12673],q 5 [16388,12673],q 0 [16388,20480],q 1 [12673],q 1 [12673,20480],q 8 [20480],q 5 [20480],q 9 [20493,73744],q 0 [73744,77826],q 1 [20493,77826],q 9 [16392,12341],q 5 [409602],q 1 [12341],q 1 [12341,409602],q 20 [12341],q 4 [20480,12629],q 9 [20480,12629],q 1 [20480,12629],q 0 [20480],q 0 [16395,20480],q 8 [20480,12629],q 2 [16395,12629],q 1 [12290,45057],q 14 [12290],q 9 [12290,20496],q 8 [12290,20496],q 19 [20496],q 1 [12290,45517],q 6 [16387],q 8 [12290,16387],q 9 [12290,16387],q 1 [12290,20491],q 9 [12290,20491],q 14 [12289],q 1 [45061],q 4 [12289],q 1 [12289,45061],q 9 [12289,20496],q 8 [12289,20496],q 3 [16412,20496],q 14 [12289,16412],q 9 [12297,16648],q 1 [12297],q 0 [16648,360450],q 2 [12297,16648],q 20 [12297],q 1 [12297,360450],q 0 [20487,16899],q 3 [20487,16899],q 20 [12290],q 4 [16899],q 8 [20487,16899],q 5 [20487,16899],q 0 [16412,32773],q 1 [12289,32773],q 7 [32773],q 8 [12289,16412],q 1 [12293],q 1 [12293,20483],q 2 [12293],q 20 [12293],q 5 [12293],q 8 [12293],q 9 [20483,16503],q 5 [20483,16503],q 8 [20483,16503],q 3 [12293,479351],q 6 [479351],q 4 [20483,479351],q 9 [20483],q 1 [20485,168555],q 2 [16387],q 3 [20485,168555],q 7 [20485],q 9 [16387],q 2 [12293,16852],q 4 [16852],q 8 [12293,16852],q 0 [20480,16852],q 1 [12293,20480],q 20 [12289],q 9 [12289],q 2 [12289],q 0 [20488,16479],q 0 [16384,266245],q 3 [266245],q 1 [12401,266245],q 3 [12293],q 2 [12293,12629],q 1 [12293,20480,12629],q 8 [12289],q 5 [12289],q 7 [16395,20488],q 4 [16395,20488],q 9 [16395,20488],q 0 [16395,20488],q 1 [12293,479851],q 3 [12293,479851],q 0 [16387,479851],q 7 [12293],q 6 [16387,479851],q 1 [12289,20491],q 2 [12289,16392],q 6 [16392],q 3 [20484],q 8 [12289,20484],q 7 [20484],q 8 [12289,16384],q 0 [16384,20484],q 1 [12289,20484],q 3 [12405],q 1 [20483,12405],q 2 [12405],q 0 [16384,20483],q 12 [20496,45061],q 1 [8194,45061],q 1 [8194,45057],q 1 [8194,45377],q 2 [8194,45377],q 9 [16392,20535],q 4 [16392,20535],q 5 [12290],q 1 [20535],q 1 [12290,20535],q 4 [12290],q 1 [8194,20495],q 10 [8194,20495],q 9 [16399,20495],q 4 [16399,20495],q 7 [16399,20495],q 12 [16399,20495],q 3 [20487],q 18 [20487],q 10 [20487],q 18 [8194],q 3 [16399],q 9 [16399],q 12 [20487,16399],q 20 [8194],q 7 [20487,16899],q 12 [20487,16899],q 3 [20487,12801],q 7 [20487,12801],q 0 [8194,20487],q 17 [8194],q 1 [20487,12801],q 12 [20487,12801],q 1 [20493,74347],q 3 [20493,74347],q 0 [16387,74347],q 4 [20491,237793],q 7 [20491,237793],q 0 [4098,20491,237793],q 1 [4098,20491,237793],q 3 [20486],q 7 [20486,328501],q 0 [8194,20486,328501],q 2 [10],q 5 [20485],q 9 [10],q 0 [10,20485,168443],q 6 [10],q 7 [20484,20485],q 12 [20484,20485],q 3 [16391],q 14 [16391],q 9 [20495],q 12 [16391,20495],q 0 [8194,16391],q 9 [20493],q 2 [16391],q 12 [16391,20493],q 1 [8194,20493],q 8 [16391],q 3 [16388],q 14 [16388],q 4 [20495],q 12 [16388,20495],q 8 [20495],q 5 [20495],q 0 [8194,16388],q 3 [16388,20487],q 7 [16388,20487],q 12 [16388,20487],q 3 [16388,20867],q 1 [8194,20867],q 12 [16388,20867],q 12 [12293,20496],q 0 [8194,20496],q 1 [8194,12293],q 4 [167952],q 7 [20485,167952],q 1 [20485],q 12 [20485,167952],q 1 [8194,20485],q 0 [8198,20480,348349],q 1 [8198,20480,348349],q 2 [8198,348349],q 6 [8198,348349],q 3 [12293,20948],q 4 [20948],q 7 [12293,20948],q 0 [8194,20948],q 1 [12293,20948],q 12 [12293,20948],q 3 [12293,16388],q 7 [12293,16388],q 2 [12293,16388],q 12 [12293,16388],q 2 [8194,12293],q 1 [20535,20493],q 3 [12293,479739],q 0 [10,479739],q 8 [12290],q 9 [16392,20491],q 4 [16392,20491],q 1 [8194,12289],q 9 [8194,12289],q 7 [16391],q 2 [12289,16391],q 5 [16391],q 14 [12293],q 1 [45058],q 1 [12293,45058],q 9 [10,20987],q 3 [20987,13137],q 7 [13137],q 5 [13137],q 0 [10,20987],q 1 [10,20987,13137],q 1 [10,12297],q 0 [10,16891],q 10 [20491],q 8 [16399],q 5 [16648],q 0 [4096,16648],q 1 [4096,12297],q 4 [12297],q 7 [12297,20496],q 14 [12297],q 0 [4097,20496],q 1 [4097,12297],q 5 [16399],q 9 [20488,16479],q 6 [16479],q 1 [4096,20495],q 10 [4096,20495],q 14 [16399],q 8 [16399,20495],q 5 [16399,20495],q 2 [4096,16399],q 5 [12521],q 0 [4096,20491],q 1 [20491,12521],q 0 [4096,20496],q 9 [16399,20623],q 4 [16399,20623],q 0 [8194,20623],q 1 [20623],q 1 [8194,20623],q 12 [16399,20623],q 5 [98320],q 1 [20489],q 1 [4096,20489],q 11 [16395],q 4 [12513],q 1 [4098,12513],q 0 [4098],q 0 [4098,16395],q 8 [4098,12513],q 2 [4098,12513],q 2 [16395],q 9 [20482,20483],q 3 [8196],q 2 [8196,348197],q 0 [8196,20480,348197],q 6 [8196,348197],q 8 [20493],q 0 [16395],q 1 [4096,20493],q 0 [4096,16395],q 1 [8196,8197],q 13 [12290],q 3 [16392],q 14 [16392],q 0 [4096,16392],q 8 [4097],q 1 [4097,20495],q 0 [4097,16395],q 8 [16384],q 1 [4096,20535],q 8 [12341],q 1 [4096,12341],q 0 [4096,20488],q 11 [20493],q 1 [8196,114725],q 1 [4097,20493],q 8 [16399,20623],q 5 [16399,20623],q 0 [4096,20623],q 1 [4096,20623],q 4 [12297,20744],q 5 [20744],q 0 [4096,20744],q 1 [12297,20744],q 20 [4096],q 2 [8198],q 7 [8198],q 6 [8198],q 2 [4096,12297],q 0 [16392,28727],q 3 [16392,28727],q 1 [12289,28727],q 6 [16392,28727],q 3 [20490],q 4 [20490],q 0 [4096,20490,66293],q 4 [20491,16619],q 1 [4096,20491],q 0 [8194,73744],q 12 [20493,73744],q 0 [8196,28711],q 3 [8196,28711],q 0 [20488,28767],q 3 [20488,28767],q 2 [4096,45069],q 1 [4096,45069],q 9 [12325],q 0 [8196,16384],q 2 [16384],q 11 [20495],q 3 [20496,286735],q 1 [45057,286735],q 14 [286735],q 1 [20480,348545],q 2 [16388,348545],q 11 [20496],q 3 [8197],q 18 [8197],q 10 [20480],q 18 [20480],q 4 [16399],q 6 [8197],q 9 [12449],q 12 [20484,12449],q 2 [8194,12449],q 0 [8194,20484],q 1 [4096,12353],q 3 [20498],q 7 [20498],q 11 [20498],q 9 [20488,12381],q 2 [12381],q 5 [16871],q 10 [20488,12381],q 0 [20488,16871],q 10 [4097,12346],q 17 [20496],q 5 [4097,12346],q 2 [4097,12346],q 3 [8196,532519],q 7 [8196],q 5 [20481],q 0 [8196,20481,532519],q 6 [8196],q 1 [8197,20493],q 0 [8197,16384],q 2 [8196],q 0 [20496,45086],q 1 [12289,45086],q 4 [40962],q 5 [40962],q 2 [8196,12325],q 7 [12293,16852],q 0 [8194,16852],q 12 [12293,16852],q 7 [8196,20519],q 0 [8196,20519],q 0 [8196,20480],q 0 [4096,73744],q 1 [10,12293],q 9 [10,16891],q 20 [10],q 2 [10,16891],q 5 [4097,12290],q 8 [4097,12290],q 2 [4097,12290],q 9 [12289,16384],q 2 [12289,16384],q 9 [12289,20491],q 0 [16392],q 4 [16392],q 9 [16392],q 4 [20480,20481],q 8 [20480,20481],q 9 [20480,20481],q 1 [20480,20481],q 1 [4097],q 10 [20495],q 10 [4097,20495],q 2 [4096,65769],q 0 [4096,20491,65769],q 1 [20493,77825],q 8 [4096,16451],q 3 [21099,13189],q 7 [13189],q 0 [16387,21099],q 1 [12290,45061],q 7 [20487],q 8 [20487],q 0 [16395,20487],q 1 [12289,20487],q 4 [16395,217313],q 7 [16395,217313],q 1 [4098,217313],q 18 [4097],q 1 [45057,45069],q 4 [16427],q 5 [16427],q 1 [12289,20535],q 9 [16384],q 0 [8197,16408,16384],q 2 [8196,16423],q 5 [20498],q 0 [8196,16423,20498],q 6 [8196,16423],q 14 [8197],q 9 [20489,98320],q 6 [614402],q 4 [13177],q 5 [13177],q 1 [8197,20495],q 5 [495618],q 6 [495618],q 4 [12298,21087],q 0 [4096,21087],q 1 [12298,21087],q 3 [8196,20519],q 1 [8196,20519],q 0 [20480,352261],q 3 [352261],q 2 [12629,352261],q 1 [20480,12629,352261],q 11 [20488],q 3 [20488],q 7 [20488],q 4 [12298,16991],q 0 [4097,16991],q 7 [12298,16991],q 20 [12298],q 2 [12298,16991],q 4 [20488,20489],q 1 [20488,20489],q 4 [20482],q 8 [20482],q 13 [20482],q 1 [45069,90113],q 11 [20491],q 2 [12289,45086],q 0 [4097,20744],q 20 [4097],q 4 [20490,17143],q 1 [4096,45065],q 6 [536581],q 1 [20481,536581],q 7 [536581],q 4 [20481,532496],q 8 [20481,532496],q 0 [20487],q 8 [20487,12801],q 17 [16395],q 2 [12801],q 1 [4096,65749],q 0 [4097,16392],q 1 [4097,12346],q 2 [8197,12289],q 20 [8197],q 0 [4097,21087],q 1 [8197,20483],q 5 [12417],q 1 [20535,12417],q 0 [8197,16408],q 4 [16408],q 5 [16408],q 1 [8197,12290],q 2 [8197,16408],q 2 [12290],q 7 [16388,12673],q 12 [16388,12673],q 1 [8194,12673],q 0 [20488],q 0 [4097,20488],q 4 [20488],q 1 [20488],q 10 [20488],q 3 [20536,13229],q 0 [4097,20536],q 4 [20536,13229],q 7 [13229],q 9 [13229],q 3 [12294,17335],q 7 [12294,17335],q 2 [12294,17335],q 0 [17335],q 0 [17335,20491],q 8 [12294,17335],q 1 [12294,20491],q 5 [12294,17335],q 6 [17335],q 3 [8197,20504],q 4 [20504],q 5 [20504],q 1 [8197,20504],q 3 [12297,270392],q 0 [4097,270392],q 4 [12297,270392],q 0 [8196,16423],q 0 [4097,16648],q 19 [8197],q 0 [8197,20496],q 3 [12294,21431],q 9 [21431],q 7 [12294,21431],q 0 [8194,21431],q 12 [12294,21431],q 2 [8194,12294],q 3 [16392,57399],q 4 [16392,57399],q 1 [4097,12341],q 0 [4097,20496,45058],q 1 [4097,20535],q 1 [20491,114921],q 1 [8194,45069],q 12 [20496,45069],q 11 [16392],q 11 [20489],q 3 [20489],q 7 [20489],q 1 [8197,25195],q 4 [16387,25195],q 5 [16387,25195],q 2 [8197,12290],q 2 [12290,16387],q 1 [8197,21099],q 3 [21099],q 8 [16387,21099],q 9 [16387,21099],q 11 [16399],q 3 [20488,57439],q 4 [20488,57439],q 0 [4097,20488,57439],q 9 [20488],q 1 [4097,20488,57439],q 2 [4097,57439],q 6 [4097,57439],q 3 [16392,532535],q 1 [20481,532535],q 4 [20488,16479],q 1 [4097,20488,12381],q 1 [4097,45069],q 5 [20480,20481],q 1 [8197,20480,20481],q 4 [16395,12501],q 7 [16395,12501],q 20 [12501],q 2 [16395,12501],q 1 [8197,20482,20483],q 12 [16388,20493],q 8 [16388],q 7 [12609],q 4 [8194,12609],q 9 [8194,12609],q 16 [20496],q 1 [8194,12609],q 2 [8194,12609],q 1 [20484,12449],q 5 [20484,12449],q 2 [8194,12289],q 11 [12297],q 3 [8197,24695],q 5 [20483,24695],q 4 [20483,24695],q 0 [8197,20483,24695],q 1 [20486,115509],q 0 [4097,20491],q 2 [4097,12521],q 3 [16412],q 9 [12289,16412],q 2 [12289,16412],q 0 [16412],q 0 [20491,16412],q 0 [4097,20623],q 1 [4097,20623],q 3 [20489,98360],q 4 [20489,98360],q 1 [4097,20489,98360],q 9 [20489],q 4 [20493,73784],q 0 [4097,73784],q 0 [4097,73744],q 3 [16440],q 0 [4097,16440],q 1 [4097,12290],q 4 [12290,16440],q 3 [20496,45114],q 4 [20496,45114],q 1 [4097,45114],q 2 [4097,45114],q 9 [20491,12521],q 2 [12289,45069],q 2 [8194,45069],q 3 [69641],q 4 [69641],q 0 [4096,69641],q 4 [20490,58103],q 1 [4097,20490,58103],q 7 [20490],q 9 [20490],q 7 [20496,45065],q 9 [20496,45065],q 1 [4097,45065],q 2 [4097,45069],q 0 [4098,20491],q 6 [4098],q 1 [12293,21099],q 5 [16387,21099],q 3 [17383],q 8 [6,17383],q 0 [73744],q 0 [20491],q 0 [20482,20483],q 1 [45057],q 3 [532496],q 1 [20481],q 0 [20480,20481],q 0 [20623],q 1 [20487],q 1 [20482],q 9 [20482],q 8 [20481],q 9 [20481],q 9 [20480],q 1 [20480],q 1 [12501],q 1 [20495],q 1 [20484],q 8 [20484],q 5 [20484],q 5 [16388],q 5 [20482],q 1 [12290],q 0 [21087],q 0 [16991],q 6 [16991],q 1 [12298],q 4 [20489],q 1 [4097,20489],q 3 [20536],q 4 [20536],q 0 [8198],q 1 [8198],q 5 [12609],q 4 [12346],q 3 [12346],q 3 [20485],q 8 [20485],q 1 [8196],q 0 [16388],q 18 [],q 2 [16399],q 9 [20498],q 4 [20498],q 12 [20498],q 8 [20498],q 1 [4097,20491],q 12 [16391],q 1 [8197,20482],q 12 [12293],q 12 [20495],q 1 [21099],q 3 [20987],q 4 [16440],q 12 [20487],q 1 [8194,20487],q 11 [],q 0 [8197,20480],q 1 [8197,20480],q 1 [20483],q 2 [16503],q 3 [16503],q 12 [16399],q 1 [10],q 12 [16388],q 12 [20484],q 12 [20485],q 12 [20493],q 12 [20496],q 3 [20508],q 0 [20508]]
def B_18_3 : BT (List (List Nat)) := BT.empty
lemma B_18_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 3 xs.toFinset) B_18_3 := .empty
def U_18_4 : List Nat := []
def P_18_4 : BT (Option BoundPool) := buildPoolsSubBT 11 W_18 r_18 S_18 ps_18 U_18_4
def N_18_4 : List NodeSpec := [([0,6,8,12,5],[],[]),([15,2,17,19,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_4 : checkNodesBT W_18 g_18 F_18 P_18_4 A_18 B_18_3 4 N_18_4 = true := by decide +kernel
def B_18_4 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_4
set_option maxRecDepth 500000 in
lemma B_18_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 4 xs.toFinset) B_18_4 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_3_ok C_18_4
def U_18_5 : List Nat := (r 0 9)
def P_18_5 : BT (Option BoundPool) := buildPoolsSubBT 11 W_18 r_18 S_18 ps_18 U_18_5
def N_18_5 : List NodeSpec := [([0,6,8,10,11,5],[0,1,2],[]),([0,1,2,8,12,5],[],[0]),([21,14,2,4,22,5],[],[]),([21,14,2,4,20,5],[],[]),([26,25,14,3,4],[3,4,5],[]),([15,16,2,3,19,5],[],[0]),([27,0,6,10,4,5],[],[]),([28,6,30,10,4,5],[],[]),([0,6,7,4,12,5],[2],[]),([31,14,2,17,4,5],[6],[]),([32,14,2,17,4,18],[],[]),([15,2,17,4,5,18],[6],[0]),([0,6,34,10,4,5],[7],[]),([28,0,6,10,19,5],[0,1],[3]),([35,36,0,6,10,5],[],[]),([0,6,3,8,37,5],[8],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_5 : checkNodesBT W_18 g_18 F_18 P_18_5 A_18 B_18_4 5 N_18_5 = true := by decide +kernel
def B_18_5 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_5
set_option maxRecDepth 500000 in
lemma B_18_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 5 xs.toFinset) B_18_5 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_4_ok C_18_5
def U_18_6 : List Nat := ([0,1,3]++r 6 118)
def P_18_6 : BT (Option BoundPool) := buildPoolsSubBT 11 W_18 r_18 S_18 ps_18 U_18_6
def N_18_6 : List NodeSpec := [([25,0,39,3,4],[3,9,10],[]),([43,0,44,3,4],([7]++r 11 5),[]),([45,46,1,3,4],([3,7]++r 16 4),[]),([0,48,1,2,3,19,5],[],[]),([0,1,50,4,51,22,5],[20,21],[]),([52,25,0,1,14,3,4],[6,17,22,23],[]),e6 [55] [],([0,1,57,3,59,4,5],[24],[]),([32,60,0,1,2,3,4],[],[]),([25,62,1,3,4],[3,23,25,26,27],[]),e6 [63] [],([64,0,1,2,65,4,5],[28],[]),e6 [68] [],([0,6,3,4,22,12,5],[29],[3]),([26,25,0,1,3,4],[3,23,25,30,31],[0]),([21,14,2,3,11,4,5],[28,32,33,34],[0]),([0,6,3,4,37,22,5],[29,35,36],[3]),([0,6,3,4,70,37,5],[37],[]),([21,14,2,3,4,5],[32,33,34,38],[0]),([0,6,3,4,37,12,5],[8,36,39],[3]),([27,0,1,2,10,4,5],[],[0]),([16,14,2,66,4,22,5],[40,41,42],[4]),([0,1,2,7,4,12,5],[28,43],[0]),([0,6,3,10,72,4,5],[44,45],[]),([21,0,1,2,4,22,5],[46],[0]),([0,6,3,11,4,12,5],[47,48],[]),([0,6,10,11,4,22,5],[44,49,50],[]),([0,1,73,75,4,22,5],[51],[]),e6 [77] [],([28,0,1,2,10,19,5],[48,52,53,54],[0]),([31,16,14,2,3,4,5],[6,55,56],[0]),([0,1,2,78,17,4,5],[28,29],[4]),([36,0,6,3,10,4,5],[44,45],[0]),([53,14,2,17,4,5,18],[6,57,58],[]),([0,79,10,4,5],[1,7,59],[]),([82,0,1,2,4,22,5],[60],[]),([0,1,2,84,4,22,5],[60,61],[]),([0,6,86,10,4,5],[44,48,62,63,64],[]),([0,6,30,10,4,5],[0,1,45,48,65],[0]),([0,6,10,4,22,5],[0,29,45,49,50,66],[]),([0,6,8,10,4,5],[0,1,44,45,63,67,68],[0]),([0,1,66,4,87,22,5],[69],[]),([16,14,2,3,88,11,5],[42,70,71,72],[4]),([32,14,2,3,17,4,5],[73],[0,4]),([0,6,3,10,89,4,5],[51],[]),([28,6,3,10,71,4,5],[51,62],[]),([0,1,2,17,88,11,5],[74,75,76],[4]),([90,0,6,3,71,4,5],[62,77],[]),([28,6,7,10,4,5],[0,48,62,78,79],[]),([0,6,7,10,11,4,5],[0,48,62],[0]),([43,91,42,0,2,3,4],[11,13,59,80,81],[]),([0,6,3,4,12,5],(r 82 4),[0,3]),([25,0,1,14,92,3,4],[6,10,17,22,23,25],[]),([0,6,65,10,4,5],[1,29,44,62,86,87,88],[]),([35,0,6,10,71,4,5],[45,63,77],[]),([15,16,2,3,4,5,18],[6,7,89,90],[0]),([93,94,14,2,3,4,5],[91],[]),([15,0,1,2,3,19,5],[],[0]),([35,58,14,2,17,4,5],[92,93,94],[4]),([94,14,2,3,4,5,18],[6,91,95],[]),([93,15,16,2,3,4,5],[89],[]),([0,6,3,95,4,5],[48,62,63,96],[]),([28,0,6,10,4,5,18],[0,1,7,97,98],[0,3]),([27,0,9,6,3,4,5],[99],[0]),([90,0,6,7,10,4,5],[0,45,62,67],[]),([58,14,13,3,17,4,5],[],[4]),([0,1,2,89,4,5,18],[61],[]),([32,0,1,2,17,4,18],[61],[0]),([31,0,1,2,17,4,5],[28,29],[0]),([21,14,2,3,4,69,5],[32],[0]),([0,6,10,19,4,5],[0,1,44,45,63,98,100],[0]),([35,36,0,1,2,10,5],[101],[0]),([97,25,0,1,3,4],[3,17,25,30,102,103],[]),([28,1,2,30,10,4,5],[48],[0]),([0,1,2,3,8,37,5],[55,104],[0]),([0,6,3,99,4,5],[105,106,107],[]),([0,6,3,7,4,37,5],[36,39],[0]),([16,14,2,100,4,5,18],[41,42,108,109],[]),([32,16,14,2,3,4,18],[73,110],[0]),([16,14,2,3,78,4,5],[6,55,111],[4]),([15,2,3,17,4,5],[7,112,113],[0]),([0,6,3,4,101,5],(r 114 4),[]),([16,14,13,3,59,4,5],[118,119],[4]),([16,14,13,2,3,19,5],[42,71,72,120],[0,4]),([102,80,1,2,4,22,5],[7],[]),([0,6,3,86,95,4,5],[51],[]),([21,0,1,2,4,20,5],[46],[0]),([35,16,14,103,2,3,5],[73,121],[4]),([0,6,3,19,4,101,5],[29],[]),([25,16,14,3,4],[3,17,23,94,122,123],[0]),([0,6,3,4,37,104,5],[63],[]),([105,14,2,3,4,69,5],[23],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_6 : checkNodesBT W_18 g_18 F_18 P_18_6 A_18 B_18_5 6 N_18_6 = true := by decide +kernel
def B_18_6 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_6
set_option maxRecDepth 500000 in
lemma B_18_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 6 xs.toFinset) B_18_6 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_5_ok C_18_6
def U_18_7 : List Nat := ([0,1,3]++r 6 6++[13,17,20]++r 22 4++[28,29,36,39,41,42,45,46,48]++r 51 5++[57]++r 59 5++[67]++r 71 4++[76,77,78,80,81,87]++r 89 4++[94,95,97,98,99,101,109,119]++r 124 422)
def P_18_7 : BT (Option BoundPool) := buildPoolsSubBT 11 W_18 r_18 S_18 ps_18 U_18_7
def N_18_7_0 : List NodeSpec := [e6 [106,107] (r 124 6),([102,0,1,2,4,22,5],([81]++r 130 6),[0,1]),e6 [108,109] [52,81,127,136,137],e6 [111,112] [55,138,139,140],([25,0,46,1,3,4],[3,7,9,10,17,25,81,141],[0]),([25,28,0,1,3,4],[3,7,9,51,141,142,143],[2]),e6 [86,114] [6,144,145],([115,1,2,3,4,70,116,5],(r 146 4),[]),([43,42,0,2,3,4],([6,7,11,13,48,51,80,81]++r 150 4),[0]),([0,1,2,7,4,116,22,5],([125]++r 154 5),[]),e6 [119,120] [55,140,159,160],([53,0,1,7,121,4,5],([23]++r 161 4),[]),e6 [53,122] [23,140,165],([28,1,2,7,123,4,5],([48,143]++r 166 6),[]),u6 [22,125] [28],e6 [127,11] [6,29,172,173],u6 [82,11] [28,60,174,175,176],a6 [81,22] [28,174,177,178] [0,3],e6 [81,116] [127,179],([35,80,0,129,1,2,3,5],[180,181],[]),e6 [131,132] [29],([25,38,0,1,3,4],[3,9,10,17,23,25,141],[0,2,3]),([80,42,0,2,3,4],[7,63,150,182,183,184],[]),([0,1,2,65,123,4,5],([28,29,157]++r 185 4),[]),e6 [133,18] [6,7,189,190,191],e6 [19,134] [28,189,192],e6 [80,135] [7,28,140,193],([80,136,0,1,2,3,4,18],[180,194],[]),e6 [80,137] [7,28,140,195],([80,0,1,2,113,4,5,18],(r 196 4),[]),([58,0,1,57,3,4,5],([7,24,189]++r 200 4),[0]),([80,0,1,2,3,118,11,5],[199,204,205,206],[]),e6 [8,138] [29],e6 [102,116] [127,157,179,207,208],([0,1,3,66,11,4,87,5],[209,210,211],[0]),([80,129,1,2,3,7,4,5],[7,28],[]),([0,1,2,124,4,22,5],[125,131,132,140,183,212,213],[]),([0,1,3,50,11,4,51,5],[210,214,215,216],[0]),u6 [139,22] [55],([140,1,14,2,3,4,22,5],[6,55,125,217],[3]),e6 [141,142] [28,55,218,219],u6 [84,11] [55,60,61,175,220,221],([141,1,14,2,3,4,22,5],[6,55,125,222,223],[3]),([0,1,73,3,75,11,4,5],[51,140,147,224,225,226],[0]),([0,1,2,143,4,22,5],[81,125,132,133,227],[3,5]),e6 [144,19] [55,189,192],([25,0,1,14,3,4],[6,7,17,22,51,228,229],[0]),([35,145,0,1,14,2,3,5],[23,230,231],[]),e6 [146,121] [7],([140,0,1,2,117,4,22,5],[81,126,132,217],[]),([53,0,1,14,3,121,4,5],[6,23,162,163],[]),e6 [14,148] [6,23,55],([25,16,0,1,3,4],[3,9,23,25,232,233],[0]),e6 [27,116] [127,179,208],([80,1,2,3,4,70,22,5],[7,147,234],[0,3]),([149,0,6,3,4,5],([7]++r 235 6),[]),([16,14,2,3,4,22,5],[41,42,71,94,125,131,241,242,243],[0,4]),([16,14,2,3,121,4,5],([23,41,94]++r 244 5),[4]),([16,14,2,3,150,4,5],([71,94,119]++r 249 4),[]),([16,14,2,3,152,4,5],([28,41,72,119]++r 253 7),[]),a6 [69,51] [20,140,260] [4],([0,153,6,3,4,5],([63]++r 261 5),[0]),([0,1,2,17,88,4,5],([63,74,76]++r 266 5),[0,4]),([25,0,1,92,3,4],[9,10,17,23,59,141],[0]),([85,0,6,3,10,4,5],[1,48,62,63,77,271,272,273],[0]),([0,1,2,124,11,4,22,5],[61,125,180,212,274],[3]),([58,16,14,13,3,4,5],[41,71,72,119,202,275,276],[0]),a6 [69,20] [277,278,279] [0,4],([102,80,1,2,3,11,4,5],[28,280,281],[0]),([16,14,13,2,3,4,5,18],([6,41,72,73]++r 282 5),[0,4]),u6 [21] ([28,29,140,210,277]++r 287 4),a6 [69,22] [28,177,277,291] [0,4],([52,25,0,1,3,4],[3,9,10,17,23,25,59,81,141],[0,1,3]),e6 [27,47] [29,51,99,219,292],([16,14,13,3,66,4,5],([41,71,119,259,286]++r 293 5),[4]),([0,1,2,17,4,22,5],[74,125,126,133,213,233,270,298],[4]),e6 [82] [7,28,29,127,140,176,210,299,300],([0,1,2,17,19,4,5],[52,63,74,76,137,270,301],[4]),([16,0,1,2,100,4,5,18],([9]++r 302 5),[0,4]),([15,16,2,3,4,5],[7,41,89,90,307],[0]),([35,58,0,1,2,17,4,5],[233,270,308,309],[0,4]),([35,36,0,1,2,6,3,5],[310,311,312],[3]),a6 [155,18] [7,189,313,314] [3],([93,16,14,13,2,3,4,5],[41,71,94,109,286,315,316,317],[0]),u6 [36,10] [101,157,311,318,319],([16,14,2,3,59,4,5],([42,71,94,119]++r 320 5),[0,4]),u6 [95] [48,63,189,325,326],e6 [93,133] [60,61,191,327,328],([16,14,103,2,3,4,5],([28,41,42,71,72,73,109,119]++r 329 4),[0,4]),u6 [48,18] ([6,51,189]++r 333 4),([35,58,16,14,2,3,4,5],[42,71,92,94,337],[0]),([90,0,6,3,10,4,5],[0,1,45,48,62,63,77,338],[0]),a6 [69,156] [23,140] [4],([0,1,2,7,4,22,107,5],[51,81,124,125,339],[]),([35,0,6,10,4,5],[0,1,45,48,63,77,340],[0,3]),([157,0,6,3,10,4,5],[1,7,48,62,63,77,271,341],[]),([0,1,57,3,66,4,5],([24,200,294,295]++r 342 4),[]),([58,14,2,3,17,4,5],[57,73,157,322,346,347,348],[0,4]),([16,14,2,3,66,11,4,5],[41,71,109,119,242,349,350,351],[0,4]),([16,14,2,3,158,4,5],([28,55,72,94,109,259]++r 352 4),[4]),([0,1,2,17,66,11,4,5],[20,74,157,356],[0,4]),u6 [32,17] [9,61,268],e6 [114] [6,48,140,189,210,357,358],([0,6,3,10,11,4,5],[0,1,48,62,77,179,359,360],[0]),([0,1,2,17,121,4,5],[23,157,210,245,356,361],[4]),e6 [84] [6,28,29,55,127,140,210,220,221,362],([35,16,0,1,103,2,3,5],[268,363,364],[0,4]),([0,1,2,59,17,4,5],[74,76,140,157,270,321,365],[4]),([0,1,2,17,11,4,22,5],[61,268,298,366,367],[4]),([32,16,0,1,2,3,4,18],[268,368,369],[0]),([28,0,6,3,10,4,5],[48,62,77,87,271,370,371],[0,3]),([141,1,2,7,4,22,5],([125,131,222]++r 372 5),[]),([0,1,14,2,3,88,11,5],[6,377,378,379],[0]),u6 [90,71] [55,213,325,380],([0,1,2,59,65,4,5],[28,140,157,381],[]),a6 [11,20] [157,382] [4],([159,1,14,2,3,19,4,5],[6,55,81,137,383],[]),a6 [17,161] [175,268,270] [4],e6 [141,162] [28,55,219,384,385],([16,14,2,3,19,4,5],[41,71,72,137,285,386,387,388],[0,4]),u6 [105,69] [23,140,210],([0,6,7,10,4,5],[0,48,62,67,78],[0]),e6 [164] ([7,46,81,127,189]++r 389 5),([80,0,96,1,2,3,19,5],[52,53,199,205,206,394],[2]),([53,14,2,3,17,4,5],[23,57,73,348,395,396],[0]),([0,6,3,4,37,5],[8,36,39,63,397,398],[0,3]),([165,29,9,6,3,4],([237,240]++r 399 5),[3]),([53,0,1,2,17,4,5,18],[74,301,404,405,406],[0]),([58,0,1,13,3,17,4,5],[9,140,157],[0,4]),([16,14,2,3,100,4,5],([41,72,109,286]++r 407 4),[0,4]),u6 [27,6] [7,140,219,292],a6 [64,28] [28,48,55,411] [0,3],([90,0,1,2,7,10,4,5],[54,63,319,325],[0]),([80,0,96,2,3,166,4,5],[412,413,414],[1]),([28,1,2,3,10,71,4,5],[48,51,325],[0]),([53,16,14,2,3,4,5,18],[6,23,71,72,285,396,415,416,417],[0]),([0,1,2,17,100,4,5],[76,210,268,408,418,419,420],[4]),e6 [167,116] [179,421],e6 [168] [7,28,55,61,127,140,189,314,422,423],([35,0,1,2,17,160,4,5],[23,270,424],[4]),([80,1,2,3,19,4,108,5],[7,81,137],[]),([28,1,2,7,10,4,5],[48,54,78,166,325,425,426],[0]),([28,1,2,6,3,30,4,5],[7,148,427],[3]),([16,0,1,13,3,59,4,5],[9,428,429,430],[0,4]),([28,0,1,2,10,4,5,18],([48,54,97,303,371]++r 431 5),[0,3]),([16,14,2,3,88,4,5],[71,72,109,119,266,351,436,437,438],[0,4]),([35,93,16,14,2,4,5],[72,73,94,119,317,439,440,441],[]),u6 [83,22] [55,131,132,177,220],([16,169,2,3,4,5],[6,72,442,443],[4]),([141,0,1,2,117,4,22,5],[48,126,132,222,223,375],[]),([16,0,1,2,66,4,22,5],[9,81,133,304,306,444],[0,4]),([80,0,1,2,117,4,22,5],[48,126,132,197,199,445],[]),([16,14,2,3,11,4,51,5],[41,109,446,447,448],[4]),u6 [7,37] [28,55,157,449,450],([16,14,2,3,11,4,22,5],[42,125,241,242,243,451],[4]),([53,42,0,2,3,4],[7,11,51,59,153,164,452],[]),e6 [11,125] [429,453],e6 [170] ([29,55,61,175,189,210]++r 454 4),([0,1,171,3,66,4,5],([46,294]++r 458 6),[]),a6 [17,172] [7] [4],e6 [8,170] [29,55,464],([16,0,1,2,3,88,11,5],([306,377]++r 465 5),[0,4]),e6 [173] [48,140,159,189,210,470],([80,1,2,7,11,4,22,5],[125,180,471,472],[3]),u6 [99] ([55,189]++r 473 4),a6 [19,174] [28,189,192] [4],([0,6,3,10,71,4,5],[0,48,51,62,77,477,478,479],[0]),a6 [27,9] [29,157,219] [0,3],([0,6,3,11,4,37,5],[8,36,39,63,397,398],[0,3]),a6 [175,18] [46,51,189,480] [0,3],e6 [93,175] [60,61,480],e6 [93,155] [60,61,314],e6 [65,89] [51],([45,25,0,1,3,4],[3,7,9,10,17,23,25,51,141,481],[0]),([80,1,2,3,4,70,116,5],[7,146,147],[]),u6 [93,94] [60,61,482],a6 [16,78] [9,28,29,55,127,368] [0,4],([80,1,2,7,4,22,5],[81,125,131,372,471,472],[]),([16,14,23,3,4,24],[41,94,483,484,485],[0]),e6 [176,32] [6,61,486],u6 [31,16] [9,28,29,55,127],u6 [94,18] [6,23,95,189,482,487],([80,1,2,3,4,22,106,5],[7,125],[0]),e6 [53,60] [23,140,488],a6 [20] ([140,189,210]++r 489 5) [0,4],([0,1,76,3,66,4,5],[46,294,344,494,495,496],[]),u6 [31,14] [6,55,81,303,497,498],e6 [177] [28,29,140,175,250,499,500,501],e6 [131,178] [29],e6 [179,100] [7],u6 [14,78] [6,55],a6 [174] [46,52,137,140,210,502,503,504] [4],([180,0,1,2,7,121,4,5],[23,245,247],[]),u6 [21,69] [46,277],u6 [21,11] [28,277,289,505],([32,0,1,14,2,3,4,18],[230],[0]),e6 [181,11] [28,506,507],e6 [180,182] [55,213,245,508,509],([0,1,14,2,66,4,22,5],[378,510,511],[0]),([28,0,1,2,6,3,19,5],[7,137,388,512,513,514],[3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_7_0 : checkNodesBT W_18 g_18 F_18 P_18_7 A_18 B_18_6 7 N_18_7_0 = true := by decide +kernel
def N_18_7_1 : List NodeSpec := [u6 [89] ([29,51,61,175,189,210,325]++r 515 4),([16,14,2,3,183,4,5],([28,41,42,71,94]++r 519 5),[]),a6 [22,20] [28,524,525] [0,4],([53,0,1,3,121,182,4,5],[23,81,526],[]),([0,6,10,4,5,18],[0,48,97,98],[0,3]),([16,0,1,13,2,3,19,5],[52,53,137,306,468,469,527,528],[0,4]),e6 [176,145] [101,213,486,529],e6 [36,184] [101,213,429],e6 [187,186] ([7,28,55,61]++r 530 5),e6 [93,48] [60,61,333,334,335],e6 [188,186] [7,28],([93,53,16,14,2,3,4,5],[41,71,94,109,317,396,535,536],[0]),u6 [86,95] [51,144,145],u6 [15,18] [6,7,189,537,538],([94,14,2,3,4,5],[6,23,91,95,404,539],[0]),([32,16,14,2,3,4,5],([28,41,72,73,109,119]++r 540 4),[0]),u6 [93,15] [60,61,537],([16,190,2,3,4,5],[7,41,72,94,544],[]),([0,1,14,2,100,4,5,18],[378,511,545],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_7_1 : checkNodesBT W_18 g_18 F_18 P_18_7 A_18 B_18_6 7 N_18_7_1 = true := by decide +kernel
def N_18_7 := N_18_7_0 ++ N_18_7_1
def B_18_7 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_7
set_option maxRecDepth 500000 in
lemma B_18_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 7 xs.toFinset) B_18_7 := by
  have hP := buildPoolsSubBT_sound (pdepth := 11) (W := W_18) (raw := r_18) (pspecs := ps_18) (used := U_18_7) S_18_ok
  have hm0 := checkNodesBT_mem (by decide) gp_18 W_18_ok hP A_18_ok B_18_6_ok C_18_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_18 W_18_ok hP A_18_ok B_18_6_ok C_18_7_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_18_8 : List Nat := ([6,7,9,20,23,28,29,30,41,42,44,46,48]++r 51 5++[59,60,61,63]++r 71 4++[76,77,81,94,101,109,119,125,126,127]++r 130 4++[135,137,138,140,141,143]++r 145 5++[155,157,159,160,164,165,166,168,169,172,174,175,177,179,180,183,185,186]++r 188 5++[197,198,199,202,205,206,208,210,213,218,219,220,223,229,230,231,233,236,240,242,245,246,247,250,251,252,255,256,261]++r 266 6++[275]++r 277 4++r 283 4++[292,294,295,300,301]++r 303 4++r 308 4++[313,314,316,317,319,321,322,323,325,328,330,332,333,335,336,339,344,350,351]++r 354 4++[361,362,363,365,366,368,369,371,376,378,379,380,384,388,389,396,399,400]++r 402 5++[408,409,411,412,414,415,417,418,420,424]++r 426 5++[432,434,435,438,440,442,444,447,455,461,464,465,468,469,480,482,484,486,494,498,499,506,509]++r 511 4++[521,522]++r 524 4++[529,534,535,537,538,540,541]++r 544 692)
def P_18_8 : BT (Option BoundPool) := buildPoolsSubBT 11 W_18 r_18 S_18 ps_18 U_18_8
def N_18_8_0 : List NodeSpec := [a6 [140,22] [6,51,55,81,125,126,131,132,133,444,524,525,546,547] [0,1],a6 [141,22] [55,81,125,126,131,132,133,218,219,223,384,444,525,548,549,550] [0,1],a6 [143,11] ([6,20,51,55,60,147,179,376,465,548]++r 551 4) [0,3,5],a6 [70,116] ([61,130,146,147,172,179,208]++r 555 5) [0,2],([35,36,0,1,2,3,5],[55,101,311,560,561,562],[0,2,3,4]),([25,0,1,3,4],[30,60,141],[0,1,2,3]),e6 [192] [9,28,46,51,55,63,189],e6 [193] [6,28,29,164,404,563],([53,194,0,1,2,3,5],([6,7,59,210,405]++r 564 6),[]),e6 [58,195] ([63,127,140,486]++r 570 13),([28,0,1,2,3,19,5],[52,53,55,81,137,189,192,213,583],[0,2,3,4]),([165,29,96,1,2,3,4],([402,403]++r 584 5),[3]),e6 [196] ([6,23,29,189,404]++r 589 4),([28,0,40,2,3,4,41],([143,371]++r 593 4),[1]),([0,1,2,65,4,5,18],[61,157,213,415,597,598],[2,3,4]),u6 [58,65] ([9,28,157,186,579,581,597]++r 599 7),a6 [85,113] ([48,357]++r 606 9) [0,2],a6 [159,19] [6,51,52,53,55,81,137,189,388,527,615,616,617] [0,1],e6 [197,100] ([7,9,51,408,418,420]++r 618 5),e6 [53,86] ([23,28,51,140,164,404,405]++r 623 7),([115,1,2,3,11,4,70,5],([7,61,130,146,147,219,558]++r 630 4),[0,1]),a6 [11,167] [23,63,147,465,552,631,634,635] [0,1],([115,58,154,1,2,3,4,5],([28,63,309,579,580]++r 636 5),[]),u6 [7,11,116] ([51,81,147,157,208,559]++r 641 4),([141,1,2,3,7,11,4,5],[6,51,147,157,177,218,219,384,548,641,645,646],[0]),([0,1,2,3,8,11,5],[81,157,189,213,219,647,648],[2,3,4]),e6 [198,88] ([6,9,51,55,140,266,267,438]++r 649 6),e6 [115,129] ([28,51,101,127,148,149]++r 655 6),a6 [8,199] ([7,55,157,455]++r 661 4) [2],a6 [36,117] ([29,46,127,157,560]++r 665 9) [2],u6 [122] ([7,28,29,81,140,157,165,175,189,210]++r 674 4),e6 [200] ([7,63,127,140,189,210,636]++r 678 5),u6 [85,118] ([48,127,159,160,613,614,665]++r 683 5),e6 [145,7] ([7,28,46,55,157,231,464,643]++r 688 4),e6 [65,201] [6,51,157,186,692,693,694],([0,1,2,86,117,4,5],[29,51,60,157,624,695,696,697],[2,3]),([53,0,1,23,3,7,4,5],([23,164]++r 698 6),[0]),e6 [202] ([7,23,28,61,63,140,189,210,682]++r 704 5),([58,0,1,13,3,7,4,5],[7,157,275,428,464,698,699,709,710,711],[]),([28,40,1,2,3,7,4,5],([28,143,166,185,426,464,690]++r 712 6),[0,3]),([28,1,2,3,30,4,5],([143,148]++r 718 4),[0,2,3,4]),a6 [80,11,116] [61,155,179,197,198,552,722,723] [0,5],([80,1,2,3,11,4,70,5],[7,61,146,147,198,219,280,558,724],[0,3]),u6 [81] [7,147,174,300,725,726],e6 [115,32] ([28,51,148,149,368,540,631]++r 727 6),([35,93,80,0,1,2,4,5],([60,183,206,414,440]++r 733 6),[]),a6 [31] [9,28,29,55,127,498] [0,1,3],u6 [35,80,128] ([48,183,199,205]++r 739 7),a6 [80,129] [7,101,127,140,180,199,205,206,655,656,658,746,747,748] [0,2],u6 [80,166] ([7,81,127,140,183,199,412,414]++r 749 6),e6 [203] [29,63,140,189,210,283,679,755,756,757],e6 [204] ([6,7,9,28,29,46,55,328,579]++r 758 4),a6 [11,81] [7,147,174,179,198,465,552,725] [0,3],e6 [206] [6,7,28,29,46,55,175,183,197,206,762,763,764],e6 [207] ([6,46,51,55,127,175,189,681]++r 765 5),([80,0,40,2,3,4,41],[7,183,197,593,594,770,771],[0]),a6 [93,80,191] ([183,197,198,205,316,535,582,733]++r 772 5) [1],a6 [80,191,18] ([7,63,205,206,283,415,772]++r 776 6) [1],a6 [93,80,96] ([183,197,198,205,535,588,733]++r 782 7) [2],([80,128,0,96,2,3,4,5],[7,197,205,206,414,789,790,791],[0,1]),u6 [80,136] [7,28,180,198,414,792,793,794],a6 [80,117,11] [7,48,147,179,198,205,414,552,695,795,796,797] [0,2],a6 [80,110] ([7,81,127,138,140,183,205]++r 798 5) [2],e6 [208] ([6,29,46,51,63,140,189,333,607,613]++r 803 4),e6 [80,209] ([7,127,140,183,198,746]++r 807 6),([80,0,96,2,3,117,4,5],([127,197,205,665,668,670,746,788,797]++r 813 5),[1]),([32,0,1,2,3,4,18],[46,61,303,368,369,818],[0,1,3]),e6 [210] [6,28,46,48,51,55,175,669,707,819,820],([115,58,0,1,13,3,4,5],[51,202,309,369,428,639,711,729,821,822,823],[]),([80,1,2,3,7,11,4,5],[7,20,147,157,177,180,219,645,690,698,796,824,825],[0,3]),e6 [211] [6,9,29,55,175,189,283,765],([80,191,1,2,3,7,4,5],([28,63,180,574,689,698,699,772,776]++r 824 5),[]),u6 [141,117,11] [6,48,81,147,179,384,548,552,695,707,829,830,831],e6 [212,117] [29,48,127,665,667,668,669,707,769,829,832],e6 [213] ([6,9,29,101,127]++r 833 5),([0,214,1,3,66,4,5],[6,46,295,344,838,839],[]),u6 [35,58,16] [9,233,306,308,363,468,579,743,840,841],a6 [16,88] [9,81,140,266,267,305,430,468,469,650,653,842,843,844] [0,4],a6 [14,66,11] ([6,63,295,350,461,511,545]++r 845 5) [0,4],([35,145,0,1,2,3,5],[23,59,101,210,231,529,691,850,851,852],[0]),([35,93,16,0,1,2,4,5],([60,268,430,440,469,736]++r 853 6),[0]),u6 [16,59] [9,81,140,233,306,321,365,429,430,468,859,860,861],a6 [16,66,11] [9,20,147,177,304,305,350,430,465,468,844,847,862] [0,4],e6 [80,183] ([7,140,183,198,205,521,522]++r 863 6),a6 [16,150] [81,140,233,250,430,468,499,869,870,871] [0,4],([53,16,14,2,3,4,5],[23,28,55,71,119,396,404,417,872],[0]),a6 [64] [28,48,55,81,175,189,210,303,411] [0,3],e6 [53,215] ([7,23,28,127,140,404,406,486]++r 873 7),([165,53,29,1,2,3,4],[164,189,402,403,417,586,879,880],[2]),u6 [153] ([46,55,63,614]++r 881 4),u6 [53,16,18] ([23,190,303,405,415,417,468,469,879]++r 885 4),([115,0,9,6,3,4,5],[44,63,140,240,261,399,732,821,889,890],[3]),a6 [93,16,13] [233,304,305,316,468,535,711,774,784,786,787,853,891,892,893] [0,4],a6 [93,53,14] [164,229,316,406,511,535,545,774,784,786,787,894,895,896] [0,4],a6 [48] [6,29,46,51,140,175,333,335,336,371,897] [0,3],u6 [14,150] [6,55,127,140,229,250,251,499,869],u6 [32,16] [9,28,29,61,268,304,305,430,469,540,728,898],a6 [16,100] [9,210,304,305,408,418,469,620,622,893,899,900] [0,4],a6 [16,121] [9,23,233,245,304,361,509,901] [0,4],([16,14,2,3,4,5,18],[41,71,72,73,283,285,415,902],[0,4]),a6 [175] [29,46,51,61,189,210,371,434,480,881,903] [0,3],a6 [53,14,18] [6,23,283,303,379,415,417,432,777,879,885,894,896,904] [0,4],u6 [16,183] ([61,81,233,304,306,468,521,864,866]++r 905 4),a6 [16,158] ([140,233,305,354,469]++r 909 5) [0,4],([165,47,29,1,2,3,4],[51,189,400,402,403,586,914,915,916],[2]),a6 [69] [23,140,147,179,277,278,279,305] [0,4],([16,0,1,13,3,66,4,5],[9,140,294,295,304,461,468,494,650,653,844,893,913,917],[0,4]),e6 [216] ([7,28,29,61,157,189]++r 918 4),e6 [217] [7,23,28,29,46,175,210,233,304,469,922,923,924],a6 [16,103] [9,81,101,140,268,304,305,306,330,430,468,469,925,926] [0,4],u6 [80,19] [7,52,53,81,137,140,192,205,206,388,615,780,927,928],e6 [218] [7,28,29,157,175,210,643,699,929,930],e6 [219] [7,28,29,157,931,932],u6 [16,11,22] [61,81,125,177,306,862,933,934],a6 [28,10] [29,48,55,210,271,325,371,380,434,435,935,936,937] [0,3],([58,16,0,1,13,3,4,5],[9,140,202,304,309,430,468,469,823,892,926],[0]),([93,16,14,2,3,4,5],[28,41,42,71,73,94,119,316,317,535,938],[0]),a6 [102,11] [7,20,28,130,135,177,179,219,465,552,939,940,941] [0,1],a6 [220] [6,7,46,140,210,607,782,783,942,943] [0,1],([16,14,2,3,11,4,5],[23,42,71,72,109,119,147,219,242,944],[0,4]),a6 [35,85,6] ([59,63,512,613,743,744,841,850]++r 945 6) [3],e6 [80,123] ([7,29,63,168,169,183]++r 951 4),u6 [53,17] [23,28,29,74,268,404,405,406,879,888,955],([221,16,14,2,3,4,5],[41,55,71,72,94,119,956,957,958],[]),a6 [180,121] ([9,23,59,101,245,247,361]++r 959 5) [0,2],e6 [176,11] ([6,20,63,147,177,179,213,219,366,465,486,848]++r 964 4),u6 [149] ([7,28,46,55,81,175,210,236]++r 968 5),([0,6,3,10,4,5],[29,44,48,77,271],[0,3]),a6 [28,6,18] [7,81,283,310,415,513,514,885,897,945,973,974] [0,3],a6 [17,11] [20,61,74,76,147,157,179,356,465,862,955] [0,4],([165,29,9,1,2,3,4],[63,402,586,587,969,972,975],[0,3]),a6 [27] [28,29,127,140,157,175,210,219,292,976,977] [0,1],u6 [157,10] [7,48,63,325,380,978,979,980],a6 [80,118] [7,48,127,140,159,198,205,206,665,668,684,797,981,982,983] [0,2],e6 [222,7] [28,55,157,464,641,643,688,690,699,984,985],([0,1,2,17,4,5,18],[61,74,76,157,268,301,415,432],[0,4]),a6 [85,10] [48,63,325,380,607,614,980,986] [0,3],u6 [16,19] [52,53,81,137,192,304,468,469,527,887,987],e6 [214,117] ([6,23,29,127,665,667,707,829,839]++r 988 4),([35,0,1,2,17,4,5],[23,28,29,74,76,157,175,268,270,743,855,949,955],[0,4]),([115,1,14,2,3,11,4,5],[63,147,148,149,179,219,632,634,732,992,993,994],[]),([58,28,1,2,3,7,4,5],[9,28,143,166,426,579,580,600,602,698,709,995,996,997],[]),([53,0,1,14,23,3,4,5],[6,7,23,379,511,700,702,894],[0]),a6 [16,13,18] [268,283,284,303,304,369,415,432,468,469,777,885,887,891,893,998,999,1000] [0,4],([53,85,1,2,3,4,130],([28,164,404]++r 1001 4),[2]),([0,1,2,17,66,4,5],[74,157,210,268,269,350,356,845],[0,4]),([35,93,0,1,14,2,4,5],[229,379,440,736,737,856,857,895,1005,1006,1007],[0]),e6 [223] [6,9,28,29,46,189,579,605,1008,1009],a6 [19,108] [7,28,52,53,81,388,527,615,1010] [0,1],e6 [58,224] [9,23,63,81,140,605,1011],a6 [226] [23,63,81,127,140,1012,1013,1014] [3],u6 [115,11,116] [61,155,179,552,559,631,632,634,732,1015],a6 [53,128,7] ([23,157,164,190,405,417,698,739]++r 1016 4) [2],u6 [133] [6,7,28,29,46,55,191,328,404,1020,1021,1022],a6 [35,58,14] [63,229,363,378,561,580,840,841,894,1023] [0,4],a6 [70,22] ([81,126]++r 130 4++[146,147,444,506,557,558,1024]) [0,1,2,4],u6 [90,10] [29,48,54,63,210,319,325,380,980,1025,1026],e6 [32,7] [7,28,55,157,368,464,541,641,643,689,690,1027],([28,0,1,2,163,3,5],[7,55,81,127,140,389,427,897,1028,1029],[]),([221,227,0,1,2,3,5],([29,61,63,210]++r 1030 4),[]),u6 [141,6,11] [51,59,63,147,218,219,384,465,514,945,1034],e6 [228,150] [6,51,55,81,140,250,251,499,870,1035,1036],e6 [229] [28,48,55,101,985,1037,1038],a6 [93,28,6] [81,143,316,435,514,535,786,945,950,974,1034,1039] [3],e6 [230,121] [7,9,23,51,245,361,509,959,960,1040,1041],a6 [58,17] [9,28,29,74,76,157,268,309,579,605,840,860,955] [0,4],u6 [16,152] [9,61,255,304,913,1042,1043,1044],e6 [115,222] [28,148,631,657,729,732,985,1045,1046],a6 [86,231] ([6,51,81,145,157,624]++r 1047 4) [3],([16,14,23,2,3,4,5],[23,28,41,55,71,72,73,94,119,246,1051,1052,1053],[0,4]),e6 [14,232] ([23,28,55,127,379,429,545]++r 1054 5),([16,0,1,23,3,4,24],[23,233,304,484,1059,1060],[0]),([165,0,9,6,3,4,5],[63,140,240,261,399,889,1061,1062,1063],[0,3]),a6 [22,106] [7,28,81,126,131,132,133,444,1064] [0,1,2,4],([58,16,14,2,3,4,5],[28,41,71,72,73,94,109,119,322,332,579,580,1065],[0,4]),a6 [11,69] [23,147,179,277,278,279,305,465] [0,4],a6 [27,11] [20,55,147,157,175,179,189,219,465,552,641,976,1066] [0,1,2,4],u6 [14,158] [6,28,29,55,127,140,354,355,545,909,910,1067,1068],e6 [14,233] [6,23,28,55,127,229,1069],a6 [16,11,51] [20,61,304,305,447,465,1070] [0,4],u6 [16,22] [81,125,126,133,233,304,306,444,468,525,862,934],a6 [131,234] ([7,81]++r 1071 5) [2],e6 [53,166] ([23,127,140,164,412,417,749,750,753,1018]++r 1076 4),u6 [94] [6,23,28,29,46,175,404,405,482,1080],u6 [176,13] [6,140,175,210,369,486,891,892,966,967,998,999,1081,1082],([28,1,2,6,3,7,4,5],[7,28,157,166,310,426,427,514,689,698,715,945,974,1083,1084],[3]),u6 [14,152] [6,55,61,127,210,255,256,511,545,1042,1068,1085],a6 [36,6] [7,29,127,140,210,310,427,512,513,671,673,945,1034,1086] [0,3],a6 [78] [9,28,29,55,127,368,1087,1088] [0,1,3],e6 [115,163] ([7,127,140,148,389,427,631,1084]++r 1089 6),u6 [80,113] [7,197,198,206,357,788,1095,1096,1097],u6 [176,23] ([6,55,189,210,229,486,966,1052,1082]++r 1098 5),u6 [85,163] [7,81,127,140,389,1090,1091,1093],a6 [236] ([6,101,210]++r 1103 5) [4],e6 [58,238] ([29,63,140,486,579,580,605]++r 1108 9),e6 [115,185] ([127,140,148,149,534,631,657,821]++r 1117 4),e6 [239] [6,28,29,61,63,175,189,295,461,894,1121,1122,1123],e6 [227,7] [28,46,55,63,81,157,641,699,1033,1124],u6 [14,88] [6,55,127,140,266,267,379,438,545,842,849,1125],e6 [115,6,11] [7,63,147,149,465,631,634,729,821,945,1126,1127]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_8_0 : checkNodesBT W_18 g_18 F_18 P_18_8 A_18 B_18_7 8 N_18_8_0 = true := by decide +kernel
def N_18_8_1 : List NodeSpec := [e6 [80,240] ([7,29,414,746,752]++r 1128 6),u6 [15] [6,7,28,29,46,511,537,538,1000,1134,1135],u6 [14,100] [6,9,55,127,210,379,408,409,418,511,545,622,1081,1136],([141,1,14,2,3,11,4,5],[6,51,63,147,179,219,384,545,1137],[0,3]),u6 [32,14] [6,7,28,29,51,55,61,127,230,368,541,545,728,1005,1138],([58,0,1,14,13,3,4,5],[6,7,51,63,140,275,379,428,511,823,894],[0,4]),e6 [241] [9,29,127,175,579,1139],([0,1,2,7,4,22,5],[28,60,81,125,131,132,133,213,339],[0,1,2,3,4]),u6 [80,22] [7,81,125,126,131,132,133,183,199,205,525,796,1140,1141],([16,14,13,2,3,4,5],[28,41,55,72,73,119,284,286,891,1142],[0,4]),([16,14,2,3,4,5,24],[41,71,94,252,1143,1144,1145],[0,4]),u6 [155] [7,28,29,46,61,189,210,313,314,514,1146,1147,1148],([115,154,1,2,6,3,4,5],[63,148,149,427,514,637,657,945,1126,1149,1150],[]),a6 [225,6] ([7,29,55,61,63,127,140,210,310,513,514,1034]++r 1151 4) [3],([35,16,14,2,3,4,5],[23,28,41,42,71,72,73,94,119,561,743,1155],[0,4]),e6 [242] ([6,7,28,29,46,63,511]++r 1156 7),e6 [243] [7,28,29,46,55,284,711,970,1163,1164],u6 [145,14] [6,7,23,28,29,55,127,230,231,378,379,691,851,1068,1165],u6 [14,121] [6,7,9,28,29,51,81,229,245,247,361,378,509,1099,1166],a6 [14,22] [6,28,29,81,125,126,131,132,133,229,378,444,511,848,1167] [0,2],([85,1,2,6,3,4,130],[7,513,945,950,1001,1002,1003,1168,1169],[3]),e6 [14,244] ([23,28,55,127,379,429,545,896]++r 1170 4),([165,29,1,2,6,3,4],[7,402,403,513,514,587,880,950,1174],[0,3]),a6 [80,96,18] [7,180,205,206,303,415,432,584,780,782,788,885,1175,1176] [0,2],a6 [124,11] ([7,61,147,175,179,180,189,429,465,552,796]++r 1177 6) [0,3],a6 [28,123] [6,48,143,168,188,371,716,1183,1184] [0,2],([80,128,1,2,3,7,4,5],[7,28,180,689,739,751,824,825,1185],[0]),([16,14,2,3,66,4,5],[41,71,73,94,295,350,351,1186],[0,4]),e6 [245] ([28,29,46,59,157,175,189,210,514]++r 1187 4),e6 [246] [6,7,29,140,143,175,189,210,371,762,937,1191],a6 [14,59] [6,55,127,140,229,321,323,365,378,429,859,1005,1192,1193] [0,4],e6 [58,8] ([9,55,140,157,455,464,581,605,664,709]++r 1194 5),u6 [14,183] [6,55,61,127,229,511,521,522,545,864,905,906,1199,1200],e6 [247] ([6,63,229,379,894,1145]++r 1201 4),u6 [93,53,16] [164,233,304,305,404,406,468,535,786,787,853,888],u6 [169] [6,63,175,210,283,379,442,777,1205,1206],a6 [14,19] [6,28,29,52,53,55,81,127,137,192,379,388,511,527,615,904,1207] [0,2,4],([115,1,248,2,3,4,5],([6,51,149,821,1094]++r 1208 4),[]),u6 [83] ([6,28,29,46,210,219,220,362,552]++r 1212 4),([53,0,1,3,121,4,5],[9,23,59,164,509,526,703,960],[0,2]),u6 [28,59] [9,140,143,321,365,371,429,602,859,861,897,1028,1216],([0,1,2,7,11,4,22,5],[46,81,131,132,133,147,339,641,1217],[0,1,2,4]),u6 [80,11,22] [61,81,125,177,199,219,796,1140,1141,1218],a6 [17,160] [7,74,157,356,424,1219,1220,1221] [0,4],u6 [190] ([6,7,229,379,511,544]++r 1222 4),a6 [83,11] [6,20,55,63,147,177,179,219,220,465,545,552] [0,4],u6 [14,11,51] [6,63,511,545,1226,1227,1228],a6 [14,11,22] [61,63,131,132,147,179,378,848,1167,1229] [0,2],a6 [58,215] [7,28,127,140,309,486,579,840,873,874,875,877,878,1230,1231] [4],e6 [225,117] [29,48,63,127,667,669,670,707,829,1014,1153,1154,1232,1233],e6 [58,250] [51,55,63,81,140,1234,1235]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_8_1 : checkNodesBT W_18 g_18 F_18 P_18_8 A_18 B_18_7 8 N_18_8_1 = true := by decide +kernel
def N_18_8 := N_18_8_0 ++ N_18_8_1
def B_18_8 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_8
set_option maxRecDepth 500000 in
lemma B_18_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 8 xs.toFinset) B_18_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 11) (W := W_18) (raw := r_18) (pspecs := ps_18) (used := U_18_8) S_18_ok
  have hm0 := checkNodesBT_mem (by decide) gp_18 W_18_ok hP A_18_ok B_18_7_ok C_18_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_18 W_18_ok hP A_18_ok B_18_7_ok C_18_8_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_18_9 : List Nat := ([6,7,20,23,28,29,46,51,55,59,60,61,63,73,81,101,119,127,130,140,143,144,147,148,149,157,164,175,177,179,180,183,185,189,190,192,197,198,199,205,206,210,213,219,229,230,233,236,268,283,295]++r 303 4++[309,310,316,318,333,344,350,368,369,371,378,379,404,405,406,414,415,417]++r 427 4++[432,434,435,461,464,465,468,469,486,511,513,514,524,525,535,545,548,552,560,561,574,579,580,581,584,585,586,588,600,602,603,605,607,613,614,625,626,627,631,636,641,643,650,665,667,669,670,679,681,689,690,691,695,698,699,703,707,709,712,714,716,729,730,732,733,739,743,744,751,766,772,774,776,777,778,780,781,782,784,786,787,788,796,797,800,802,821,824,826,830,836,839,840,841,844,845,848,849,850,853]++r 859 4++[866,870,871,879,881]++r 885 4++r 890 8++[901,904,914,916,926,937,945,947,949,950]++r 954 4++[972,974,975,985,998,999,1004,1005,1006,1014,1016,1017,1018,1028,1031,1034,1052,1061,1062,1063,1076,1082,1092,1094,1098,1100,1101,1104,1124,1144,1145,1152,1176,1181,1192,1194,1197,1204,1208,1210]++r 1236 71)
def P_18_9 : BT (Option BoundPool) := buildPoolsSubBT 11 W_18 r_18 S_18 ps_18 U_18_9
def N_18_9 : List NodeSpec := [a6 [22] [28,29,55,60,81,127,140,177,210,213,525] [0,1,2,3,4,5],a6 [19] [28,29,55,81,127,140,189,192,210,1236] [0,1,2,3,4,5],a6 [59] [28,29,55,60,127,140,213,429,859,861,1237] [0,1,2,3,4],([165,29,1,2,3,4],[55,60,189,586,1238],[0,1,3]),u6 [233] [23,28,29,55,59,60,127,210],a6 [11,70] [7,20,61,130,147,179,219,465,552,1239] [0,1,2,3,4],a6 [131] [29,55,60,81,127,140,210,1240,1241] [0,1,2,3,4,5],([85,1,2,3,4,130],[28,60,189,1004,1242],[0,1,2,3,4]),a6 [86] [28,29,60,127,140,144,157,210,213,625,626] [0,1,2,3,4,5],([53,0,1,23,3,4,5],[23,59,140,175,189,210,406,703,879,1101],[0,2]),a6 [183] [28,29,55,60,61,127,140,210,866,1243] [0,1,2,3,4,5],a6 [53,128] [51,61,140,189,190,404,405,406,417,739,879,886,1016,1017,1018,1076,1244] [0,1,2,4],u6 [165,53] [164,175,189,190,210,404,405,879,1061,1062,1245,1246],a6 [53,130] [28,55,164,190,210,236,404,405,417,1241,1247,1248] [0,4],a6 [53,85] [6,23,28,51,164,175,190,404,405,417,607,613,627,879,886,1249,1250] [0,2],a6 [244] [23,28,29,55,59,61,127,140,164,429,886,1251] [0,1,3],a6 [93,28] [28,55,60,61,143,371,434,535,600,774,784,786,787,897,1028,1252] [0,2,3,4],a6 [28,18] [55,189,192,303,371,415,432,434,600,777,885,897,937,1028] [0,2,3,4],a6 [145] [23,28,29,46,55,59,101,127,175,189,210,213,691] [0,1,2,3],a6 [58,28] [6,28,51,61,175,189,309,371,434,435,579,581,600,602,605,897,937,1028,1237] [0,4],a6 [28,40] [6,28,61,185,189,371,434,435,600,712,716,897,937,1028,1253,1254,1255] [0,2],a6 [165,96] [55,127,175,584,588,782,1061,1062,1176,1245,1256,1257] [0,2],([58,0,1,13,3,4,5],[140,175,210,309,369,428,892],[0,1,2,3,4]),a6 [115,11] [20,23,61,63,147,148,149,175,177,179,189,465,552,631,821,1094,1258] [0,1],a6 [115,58] [6,28,60,148,149,189,309,579,581,605,732,821,1237,1258] [0,1,2],a6 [141,11] [6,20,23,51,55,61,63,147,177,179,219,465,548,552,830] [0,1],e6 [115,40] [6,28,60,63,148,185,189,712,732,1253,1254,1255],e6 [115,53] [6,23,28,101,148,149,164,175,190,404,405,732,821,879,886,1094,1258],a6 [152] [28,29,55,61,101,127,210,1259] [0,1,3],a6 [232] [23,28,29,55,59,61,127,175,210,429,1260,1261,1262] [0,1,3],a6 [14,11] [20,28,29,61,147,177,179,189,219,378,379,465,511,545,552,848,894,1005] [0,2,4],a6 [14,24] [6,28,29,229,894,1144,1145,1204,1263,1264] [0,4],a6 [235] [6,28,46,55,61,101,127,140,175,189,210,1104,1265,1266] [0,4],a6 [115,47] [28,51,63,140,148,210,333,732,821,890,914,916,1094,1267,1268] [2],a6 [65] [28,29,61,127,140,157,189,210,600,603] [0,1,2,3,4,5],a6 [53,14] [6,28,29,55,127,190,210,230,379,404,405,417,894,896,1005] [0,4],a6 [32] [28,29,46,55,61,127,175,189,210,368,730] [0,1,2,3],a6 [14,66] [6,229,230,295,350,461,845,849,894,1005] [0,4],a6 [124] [7,28,29,61,127,140,180,183,213,429,1181,1269] [0,1],u6 [176] [6,28,29,46,55,61,140,175,189,210,213,229,230,486,1082,1270,1271],a6 [28,41] [29,55,127,143,371,434,766,800,897,1028,1272,1273] [0,3],a6 [165,9] [55,63,127,140,210,881,972,975,1061,1257,1274] [0,3],([115,1,14,2,3,4,5],[6,28,29,51,55,149,229,230,732,821,1094,1210],[0]),([28,1,2,3,7,4,5],[28,46,55,101,143,464,600,689,690,698],[0,1,2,3,4]),a6 [58,7] [7,28,55,60,210,464,579,580,581,605,643,689,690,698,699,709,1237] [0,1,4],a6 [115,96] [6,28,101,148,175,584,588,732,782,1176,1256,1258,1275] [1],a6 [28,6] [6,29,51,55,101,127,140,210,310,371,427,434,513,600,897,937,945,974,1028] [0,3],a6 [53,7] [7,28,55,101,164,190,405,417,464,643,689,690,698,886] [0,1,4],u6 [16,11] [20,23,61,147,175,177,179,189,305,306,430,465,468,469,862],a6 [16,23] [23,61,189,233,268,304,468,469,901,1052,1098,1100,1101] [0,4],u6 [35,16] [23,28,29,101,213,233,268,304,306,430,468,469,743,841,850,949,1276,1277],a6 [16,66] [140,210,233,268,344,350,430,468,650,844,845] [0,4],a6 [35,58] [60,140,189,213,309,561,579,580,581,605,743,744,840,841,949,1237,1276] [0,1,3,4],e6 [221,80] ([101,140,183,189,197,205,206,210,414,956,957,1031]++r 1278 4),a6 [17] [28,29,61,140,157,189,210,213,268,955] [0,4],([115,154,1,2,3,4,5],[23,28,55,63,148,149,175,636,821,1094,1258],[0,1]),a6 [58,14] [6,28,29,55,127,229,230,379,511,545,579,580,581,605,894,1005,1192,1282] [0,4],a6 [16,18] [55,81,127,192,268,303,304,415,432,468,469,885,887] [0,4],a6 [7,11] [20,28,61,147,177,179,219,464,465,552,641,643,689,690,698,699] [0,1,2,3,4],u6 [222] [28,29,46,55,61,101,175,189,210,985],a6 [80,191] [28,55,63,101,140,175,205,210,414,574,772,776,778,781,826,1283] [0,1],a6 [165,6] [29,81,127,140,210,427,513,945,950,1061,1062,1246,1257,1284] [0,3],a6 [93,14] [28,29,55,61,81,127,229,230,316,378,511,535,774,784,786,787,894,895,1005,1252] [0,4],a6 [80,117] [29,127,180,183,205,414,665,667,670,695,707,797,1285] [0,5],u6 [93,80] [28,60,61,81,140,180,183,197,199,205,210,316,414,535,733,774,784,786,787,1252,1286],a6 [53,18] [189,190,192,210,283,404,405,415,417,432,777,879,885,886] [0,1,3,4],a6 [115,6] [29,127,140,148,149,210,310,427,513,821,945,950,1092,1258] [0,3],a6 [225] [23,29,46,55,61,63,127,140,189,210,679,1014,1152,1287] [0,1],u6 [212] [6,28,29,46,55,61,101,127,175,189,210,836,1288],([80,1,2,3,7,4,5],[7,28,46,55,180,183,689,690,698,699,824],[0,5]),a6 [248] [6,46,55,61,81,127,140,189,210,213,1005,1208,1289] [0,2,4],u6 [93,16] [28,29,60,61,81,233,268,304,306,430,468,535,784,786,787,853,1252],a6 [80,128] [28,29,61,140,180,183,189,197,198,205,206,210,414,739,751,1016,1017,1076,1244,1290,1291] [0,1,2,4],a6 [93,53] [61,140,164,190,210,316,404,405,417,535,774,784,786,886,1252] [0,1,3],([16,14,2,3,4,5],[28,55,73,119,1292],[0,4]),a6 [115,9] [28,63,148,318,729,732,881,972,975,1274] [0,3],a6 [227] [28,29,46,55,61,63,81,189,210,213,1124,1274] [0,3],a6 [16,13] [55,101,127,140,175,268,304,369,430,469,891,893,998,999] [0,4],a6 [14,18] [81,192,230,283,303,379,415,432,511,777,885,894,904] [0,4],a6 [85,6] [6,29,51,61,127,140,210,310,427,513,514,607,613,614,626,945,950,1034,1249,1250,1293,1294] [0,3],a6 [221,16] [101,189,233,304,430,468,469,956,1031,1279,1281] [0,4],u6 [53,16] [23,28,101,210,404,405,430,468,879,886,888],a6 [35,85] [23,28,60,63,189,213,607,613,614,626,743,744,841,850,947,949,1249,1250,1276] [0,3],a6 [8] [29,55,61,127,140,157,189,210,464,1194,1197] [0,1,2,3,4,5],a6 [16,24] [81,140,210,233,304,468,870,871,1144,1263] [0,4],a6 [36] [29,46,55,101,127,140,175,189,210,213,560,1295,1296,1297] [0,1,2,3,4],u6 [35,80] [28,63,101,140,180,183,197,199,205,206,210,213,414,561,743,744,841,850,949,1276,1277,1298],a6 [58,16] [28,61,189,233,268,304,305,309,430,468,469,579,605,860,926,1237] [0,4],a6 [11,22] [20,61,81,147,177,179,219,465,524,525,552] [0,1,2,3,4,5],u6 [221,14] [28,29,55,101,127,229,379,511,894,956,957,1005,1031,1278,1279,1281],a6 [214] [6,23,28,29,46,55,61,81,127,175,189,210,213,839,1299] [0,1],a6 [35,14] [28,29,55,101,127,213,229,230,378,379,511,561,743,744,841,850,894,949,1005,1276,1277] [0,4],a6 [80,96] [7,140,180,197,206,210,414,585,782,788,1300] [0,2],a6 [80,40] [7,55,63,127,180,183,197,205,206,414,712,714,954,1301] [0,2],a6 [165,47] [63,140,189,210,333,914,916,1061,1062,1063,1268] [0,2],a6 [80,41] [29,55,81,127,183,197,205,681,800,802,1272,1273,1302] [0,5],a6 [80,18] [81,180,192,197,205,206,210,283,303,415,432,777,780,885,1303] [0,5],u6 [80,11] [20,55,61,63,147,175,177,179,189,198,199,205,206,219,414,465,552,796,1304],a6 [28,117] [29,51,101,127,143,600,665,667,669,670,695,1028] [3],([35,93,0,1,2,4,5],[60,189,1006,1252,1277],[0,1,2,3,4,5]),a6 [85,117] [29,51,55,60,127,626,665,667,669,670,695,1249,1250] [0,2,3],a6 [98] [29,55,101,127,140,210,690,1305,1306] [2,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_9 : checkNodesBT W_18 g_18 F_18 P_18_9 A_18 B_18_8 9 N_18_9 = true := by decide +kernel
def B_18_9 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_9
set_option maxRecDepth 500000 in
lemma B_18_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 9 xs.toFinset) B_18_9 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_8_ok C_18_9
def U_18_10 : List Nat := [16,28,29,46,55,60,61,127,140,175,177,180,189,192,210,213,230,268,309,414,430,464,600,626,886,1005,1237,1241,1245,1250,1252,1258]
def P_18_10 : BT (Option BoundPool) := buildPoolsSubBT 11 W_18 r_18 S_18 ps_18 U_18_10
def N_18_10 : List NodeSpec := [a6 [221] [28,29,55,60,127,140,175,189,210] [0,1,2,3,4,5],a6 [16] [28,29,46,140,175,189,210,268,430] [0,4],a6 [28] [28,29,46,127,140,175,189,210,600] [0,1,2,3,4],a6 [80] [16,28,29,46,55,127,140,175,180,189,210,414] [0,2,5],a6 [7] [28,29,46,55,60,127,140,210,464] [0,1,2,3,4],a6 [115] [28,29,46,60,127,140,175,189,210,1258] [0,1,3],a6 [14] [28,29,46,55,127,140,175,189,210,230,1005] [0,2,4],a6 [53] [28,29,46,55,127,140,175,189,886] [0,1,2,3,4],a6 [93] [28,29,46,55,60,127,140,175,210,213,1252] [0,1,2,3,4,5],a6 [85] [28,29,46,55,61,127,140,175,189,210,626,1250] [0,1,2,3,4],a6 [130] [28,29,55,60,127,140,210,1241] [0,1,2,3,4],a6 [165] [28,29,60,127,140,175,189,210,1245] [0,1,3],a6 [58] [28,29,46,55,61,127,140,175,189,210,309,1237] [0,1,2,3,4],a6 [35] [28,29,46,55,60,127,140,175,189,210,213] [0,1,2,3,4,5],a6 [11] [28,29,55,61,127,140,175,177,189,210,213] [0,1,2,3,4,5],a6 [18] [28,29,46,55,127,140,189,192,210] [0,1,2,3,4,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_10 : checkNodesBT W_18 g_18 F_18 P_18_10 A_18 B_18_9 10 N_18_10 = true := by decide +kernel
def B_18_10 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_10
set_option maxRecDepth 500000 in
lemma B_18_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 10 xs.toFinset) B_18_10 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_9_ok C_18_10
def U_18_11 : List Nat := [46,175]
def P_18_11 : BT (Option BoundPool) := buildPoolsSubBT 11 W_18 r_18 S_18 ps_18 U_18_11
def N_18_11 : List NodeSpec := [a6 [] [46,175] [0,1,2,3,4,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_11 : checkNodesBT W_18 g_18 F_18 P_18_11 A_18 B_18_10 11 N_18_11 = true := by decide +kernel
def B_18_11 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_11
set_option maxRecDepth 500000 in
lemma B_18_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 11 xs.toFinset) B_18_11 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_10_ok C_18_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_ok : forestRootCheck r_18 g_18 [(VAR 0,22,23),(VAR 1,21,23),(VAR 2,19,23),(VAR 3,17,25),(VAR 4,7,23),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_in : bucketContainsBT B_18_11 r_18 = true := by decide +kernel
lemma low_18 : Lower r_18 g_18 12 := lower_of_forestBT root_18_ok B_18_11_ok root_18_in

def g_orig := (d 0xeeeaeae8eae8e8a0)
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,4),(2,3),(3,5)]) (by decide +kernel) low_18
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 3941132448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.and,[4,1]⟩,⟨.or,[0,6]⟩,⟨.and,[5,3]⟩,⟨.or,[1,4]⟩,⟨.or,[2,8]⟩,⟨.and,[2,1]⟩,⟨.or,[3,5]⟩,⟨.or,[11,0]⟩,⟨.or,[12,6]⟩,⟨.and,[9,13]⟩,⟨.and,[14,15]⟩,⟨.and,[7,10]⟩,⟨.or,[17,16]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_45156

open PEqualNP.Outside.L_meta_45156 in
theorem PEqualNP.Outside.L_meta_45156 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941132448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3941132448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
