import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45154
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

def g_0 := (d 0xfe80fe80fe80fe80)
def r_0 : List Nat := varsOf 15
def p_0 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14]
def q_0 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6]
def F_0 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_0 : goodPairs g_0 p_0 q_0 := goodPairs_of (by decide +kernel)
def W_0 : BT Decor := buildWiresBT 5 (mkBase p_0 q_0 r_0) [(0,2,3),(1,2,3),(3,4,5),(0,1,2),(1,1,2),(3,7,8),(2,0,3),(3,0,3),(1,0,3),(3,2,12),(1,1,3),(0,0,14),(0,0,3),(1,16,2),(3,4,0),(2,0,2),(3,0,2),(2,2,1),(3,21,0),(2,0,1),(1,23,2),(0,0,1),(1,0,1),(3,2,3)]
lemma W_0_ok : btAll (fun x => faithful p_0 q_0 x ∧ x.1 < 2^256) W_0 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_0 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_0 : BT (List (Nat × Nat)) := btOfList 3 al_0
set_option maxHeartbeats 0 in
lemma A_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_0 = g_0) A_0 := btAll_ofList (autos_of (by decide +kernel))
def S_0 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_0_ok : btAll (fun o => ∀ p, o = some p → Slice r_0 g_0 p.1 p.2) S_0 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_0 : BT (Option PoolSpec) := btOfList 1 []
def B_0_1 : BT (List (List Nat)) := BT.empty
lemma B_0_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 1 xs.toFinset) B_0_1 := .empty
def U_0_2 : List Nat := []
def P_0_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 r_0 S_0 ps_0 U_0_2
def N_0_2 : List NodeSpec := [([6,0,1],[],[]),([9,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_0_2 : checkNodesBT W_0 g_0 F_0 P_0_2 A_0 B_0_1 2 N_0_2 = true := by decide +kernel
def B_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 N_0_2
set_option maxRecDepth 500000 in
lemma B_0_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 2 xs.toFinset) B_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound S_0_ok) A_0_ok B_0_1_ok C_0_2
def U_0_3 : List Nat := []
def P_0_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 r_0 S_0 ps_0 U_0_3
def N_0_3 : List NodeSpec := [([10,11,1,2],[],[3]),([13,0,1,3],[],[]),([15,1,2,3],[],[]),([16,1,2,12],[],[3]),([0,1,17,3],[],[]),([18,1,2,3],[],[]),([19,20,1,3],[],[2]),([22,1,2,3],[],[]),([0,1,24,3],[],[]),([25,26,2,3],[],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_0_3 : checkNodesBT W_0 g_0 F_0 P_0_3 A_0 B_0_2 3 N_0_3 = true := by decide +kernel
def B_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 N_0_3
set_option maxRecDepth 500000 in
lemma B_0_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 3 xs.toFinset) B_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound S_0_ok) A_0_ok B_0_2_ok C_0_3
def U_0_4 : List Nat := []
def P_0_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 r_0 S_0 ps_0 U_0_4
def N_0_4 : List NodeSpec := [([27,0,1,2,3],[],[4]),([10,0,1,2,3],[],[0]),([0,1,2,3,12],[],[0,1,2,4]),([16,0,1,2,3],[],[0,1,3,5]),([19,0,1,2,3],[],[0,1,3]),([0,1,26,2,3],[],[0]),([25,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_0_4 : checkNodesBT W_0 g_0 F_0 P_0_4 A_0 B_0_3 4 N_0_4 = true := by decide +kernel
def B_0_4 : BT (List (List Nat)) := buildBucketsBT W_0 N_0_4
set_option maxRecDepth 500000 in
lemma B_0_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 4 xs.toFinset) B_0_4 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound S_0_ok) A_0_ok B_0_3_ok C_0_4
def U_0_5 : List Nat := []
def P_0_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 r_0 S_0 ps_0 U_0_5
def N_0_5 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_0_5 : checkNodesBT W_0 g_0 F_0 P_0_5 A_0 B_0_4 5 N_0_5 = true := by decide +kernel
def B_0_5 : BT (List (List Nat)) := buildBucketsBT W_0 N_0_5
set_option maxRecDepth 500000 in
lemma B_0_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 5 xs.toFinset) B_0_5 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound S_0_ok) A_0_ok B_0_4_ok C_0_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck r_0 g_0 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT B_0_5 r_0 = true := by decide +kernel
lemma low_0 : Lower r_0 g_0 6 := lower_of_forestBT root_0_ok B_0_5_ok root_0_in
def g_1 := (d 0xe8e8e8e8e8e8e8e8)
def r_1 : List Nat := varsOf 7
def p_1 : List Nat := [3,3,5,5,6,6]
def q_1 : List Nat := [2,1,4,1,4,2]
def F_1 : Nat := fullMask 6
set_option maxHeartbeats 0 in
lemma gp_1 : goodPairs g_1 p_1 q_1 := goodPairs_of (by decide +kernel)
def W_1 : BT Decor := buildWiresBT 2 (mkBase p_1 q_1 r_1) []
lemma W_1_ok : btAll (fun x => faithful p_1 q_1 x ∧ x.1 < 2^256) W_1 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_1 : List (List (Nat × Nat)) := [[]]
def A_1 : BT (List (Nat × Nat)) := btOfList 1 al_1
set_option maxHeartbeats 0 in
lemma A_1_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_1 = g_1) A_1 := btAll_ofList (autos_of (by decide +kernel))
def S_1 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_1_ok : btAll (fun o => ∀ p, o = some p → Slice r_1 g_1 p.1 p.2) S_1 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_1 : BT (Option PoolSpec) := btOfList 1 []
def B_1_2 : BT (List (List Nat)) := BT.empty
lemma B_1_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 2 xs.toFinset) B_1_2 := .empty
def U_1_3 : List Nat := []
def P_1_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_1 r_1 S_1 ps_1 U_1_3
def N_1_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_3 : checkNodesBT W_1 g_1 F_1 P_1_3 A_1 B_1_2 3 N_1_3 = true := by decide +kernel
def B_1_3 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_3
set_option maxRecDepth 500000 in
lemma B_1_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 3 xs.toFinset) B_1_3 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_2_ok C_1_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_1_ok : forestRootCheck r_1 g_1 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_1_in : bucketContainsBT B_1_3 r_1 = true := by decide +kernel
lemma low_1 : Lower r_1 g_1 4 := lower_of_forestBT root_1_ok B_1_3_ok root_1_in
def g_2 := (d 0xe800e800e800e800)
def r_2 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_2 : Lower r_2 g_2 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_1) (G := g_1) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_1
def g_3 := (d 0xffe8ffe8ffe8ffe8)
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_1) (G := g_1) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_1
def g_4 := (d 0xf880f880f880f880)
def r_4 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_4 : Lower r_4 g_4 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_5 := (d 0xffe88000ffe88000)
def r_5 : List Nat := varsOf 31
def p_5 : List Nat := [15,15,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,29,30]
def q_5 : List Nat := [14,13,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,13,14]
def F_5 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_5 : goodPairs g_5 p_5 q_5 := goodPairs_of (by decide +kernel)
def W_5 : BT Decor := buildWiresBT 8 (mkBase p_5 q_5 r_5) [(0,0,1),(0,0,2),(0,1,2),(0,7,4),(1,8,3),(1,3,4),(0,0,10),(1,7,3),(0,12,4),(0,6,4),(3,14,0),(2,0,3),(3,16,2),(2,3,4),(3,18,7),(3,19,0),(0,3,4),(3,21,10),(1,5,21),(0,0,4),(1,7,24),(3,8,4),(2,1,3),(1,27,24),(1,5,3),(3,18,29),(0,5,4),(1,31,2),(1,31,3),(1,7,4),(3,8,34),(2,7,3),(3,36,0),(0,29,4),(2,0,13),(2,0,4),(0,5,2),(3,41,0),(3,42,4),(0,7,3),(3,44,12),(3,40,1),(0,2,3),(3,47,0),(3,5,2),(0,41,4),(3,50,0),(3,41,1),(3,3,4),(3,14,2),(2,5,3),(3,7,3),(1,14,1),(1,14,3),(3,14,4),(3,8,3),(1,8,0),(1,27,6),(3,18,2),(3,63,0),(0,2,10),(3,65,0),(0,5,10),(2,2,21),(3,68,0),(2,0,21),(3,70,1),(1,5,4),(0,3,72),(3,18,0),(0,2,72),(3,6,3),(3,41,4),(3,17,4),(3,16,4),(2,5,47),(3,56,0),(3,5,3),(2,2,3),(3,83,0),(0,84,4),(0,83,4),(3,86,0),(3,49,4),(1,41,3),(0,2,4),(2,5,90),(1,42,3),(0,1,4),(1,93,3),(0,0,94),(3,55,2),(3,12,4),(0,5,3),(0,0,3),(0,0,12),(3,26,0),(3,83,5),(2,5,21),(2,2,4),(3,104,0),(2,5,4),(3,31,4),(1,26,3),(3,16,1),(3,27,2),(3,104,5),(0,16,4),(3,106,0),(1,7,99),(3,27,4),(1,83,5),(1,104,5),(3,55,0),(1,16,21),(3,7,10),(1,18,5),(3,36,4),(3,18,5),(0,1,3),(3,124,2),(3,125,0),(3,110,0),(2,0,115),(3,3,72),(3,93,2),(3,130,0),(1,15,3),(0,42,4),(2,1,4),(3,134,2),(3,135,0),(1,24,3),(3,83,4)]
lemma W_5_ok : btAll (fun x => faithful p_5 q_5 x ∧ x.1 < 2^256) W_5 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_5 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_5 : BT (List (Nat × Nat)) := btOfList 3 al_5
set_option maxHeartbeats 0 in
lemma A_5_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_5 = g_5) A_5 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_5_0 : Slice r_5 g_5 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_1 : Slice r_5 g_5 (subcubeFast 0 2) 6 := by
  have hc : Lower (varsOf 29) (d 0xfffaa000fffaa000) 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_2 : Slice r_5 g_5 (subcubeFast 0 4) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_3 : Slice r_5 g_5 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_4 : Slice r_5 g_5 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_5_5 : Slice r_5 g_5 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_5_6 : Slice r_5 g_5 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeaea8080eaea8080) 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_4
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_7 : Slice r_5 g_5 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xecec8080ecec8080) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_4
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_8 : Slice r_5 g_5 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f88080f8f88080) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_4
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_5 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 0 2,6),some (subcubeFast 0 4,6),some (subcubeFast 8 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4),some (identDom 0 3,5),some (identDom 1 3,5),some (identDom 2 3,5)]
lemma S_5_ok : btAll (fun o => ∀ p, o = some p → Slice r_5 g_5 p.1 p.2) S_5 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_5_0) (forall_cons (fun _ h => by cases h; exact sl_5_1) (forall_cons (fun _ h => by cases h; exact sl_5_2) (forall_cons (fun _ h => by cases h; exact sl_5_3) (forall_cons (fun _ h => by cases h; exact sl_5_4) (forall_cons (fun _ h => by cases h; exact sl_5_5) (forall_cons (fun _ h => by cases h; exact sl_5_6) (forall_cons (fun _ h => by cases h; exact sl_5_7) (forall_cons (fun _ h => by cases h; exact sl_5_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_5 : BT (Option PoolSpec) := btOfList 7 [q 0 [16396,16397,41047],q 1 [],q 1 [16412,16413,139299],q 1 [12316,12317,49331],q 2 [],q 0 [],q 0 [16397,40968],q 6 [],q 3 [40960],q 1 [16397,40960],q 5 [],q 1 [16396,16397,41047],q 2 [16396,16397,41047],q 0 [16396,86026],q 1 [16396,86018],q 0 [16405,294924],q 3 [],q 0 [16405,294920],q 0 [16396,86037],q 4 [12386],q 0 [16404,16405],q 1 [16412,12323],q 1 [16412,35],q 1 [12319,227],q 0 [12310,12311],q 4 [],q 0 [16398,16399],q 0 [16392,368662],q 0 [16388,12661],q 0 [12310,8415],q 0 [16404,12413],q 7 [],q 0 [12308,12309],q 0 [12298,20815],q 3 [16388],q 0 [16396,86038],q 4 [12290],q 0 [16406,16407],q 1 [8192],q 0 [12294,8303],q 1 [16404,12413],q 1 [16392,363],q 3 [40968],q 0 [12298,20813],q 1 [16384,98333],q 0 [16396,16397],q 0 [16397,40980],q 1 [16397,40991],q 0 [16405,294927],q 3 [16451],q 1 [8564,35],q 1 [16384,12413],q 0 [4192,12413],q 0 [16388,8567],q 0 [16398],q 0 [16396],q 2 [16396,86018],q 0 [16397],q 2 [16397,40960],q 4 [12385],q 2 [16384],q 1 [16384],q 0 [4192],q 0 [12385],q 1 [16384,12385],q 2 [16384,12385],q 8 [],q 0 [16399],q 0 [16388],q 1 [12290],q 0 [12294],q 0 [16448],q 2 [4096],q 0 [12310],q 1 [16396,16397],q 2 [16396,16397],q 0 [16404],q 0 [16392],q 2 [363],q 0 [12309],q 1 [12309],q 1 [12310],q 0 [12308],q 0 [8196],q 1 [31],q 0 [8212],q 2 [31],q 0 [16405],q 1 [12319],q 0 [16406],q 1 [16398,16399],q 2 [16398,16399],q 1 [16386],q 1 [8212],q 1 [16415],q 2 [16415],q 2 [16719],q 3 [16719],q 3 [16384],q 2 [335],q 0 [12298],q 1 [12298,335],q 0 [12296],q 2 [419],q 0 [16394],q 1 [16404],q 2 [191],q 1 [16399],q 2 [16399],q 1 [16398],q 2 [16398],q 2 [16386],q 2 [12290],q 1 [12288],q 2 [12288],q 1 [16397],q 2 [16397],q 1 [16396],q 2 [16396]]
def B_5_2 : BT (List (List Nat)) := BT.empty
lemma B_5_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 2 xs.toFinset) B_5_2 := .empty
def U_5_3 : List Nat := []
def P_5_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_3
def N_5_3 : List NodeSpec := [([5,6,9,4],[],[]),([11,1,2,13],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_3 : checkNodesBT W_5 g_5 F_5 P_5_3 A_5 B_5_2 3 N_5_3 = true := by decide +kernel
def B_5_3 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_3
set_option maxRecDepth 500000 in
lemma B_5_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 3 xs.toFinset) B_5_3 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_2_ok C_5_3
def U_5_4 : List Nat := (r 0 6)
def P_5_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_4
def N_5_4 : List NodeSpec := [([15,1,17,3,4],[],[]),([20,1,2,3,4],[],[]),([22,5,0,1,2],[0],[]),([16,1,2,23,4],[],[]),([5,25,2,3,4],[1],[]),([26,5,6,3,4],[],[]),([5,28,2,3,4],[],[]),([0,1,2,30,4],[],[]),([11,1,2,12,4],[],[0]),([0,1,32,33,4],[],[]),([35,0,1,2,3],[2],[]),([16,5,2,12,4],[],[]),([37,1,2,21,4],[],[]),([0,1,2,38,10],[],[4]),([39,1,2,3,4],[],[]),([40,1,43,2,3],[],[]),([45,0,1,2,4],[3],[]),([42,46,2,3,4],[],[]),([48,49,1,3,4],[],[]),([51,1,2,3,4],[],[]),([42,52,2,3,4],[],[]),([53,37,1,2,4],[],[]),([15,54,1,3,4],[],[]),([5,6,3,12,4],[],[]),([55,6,7,3,4],[4],[]),([56,37,1,2,4],[],[]),([15,57,2,3,4],[],[]),([15,1,2,58,4],[],[]),([15,59,1,2,3],[],[]),([60,1,61,2,4],[],[]),([51,1,2,9,4],[],[]),([51,60,1,2,4],[],[]),([31,6,7,3,4],[4],[4]),([5,62,2,3,4],[5],[]),([5,0,2,9,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_4 : checkNodesBT W_5 g_5 F_5 P_5_4 A_5 B_5_3 4 N_5_4 = true := by decide +kernel
def B_5_4 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_4
set_option maxRecDepth 500000 in
lemma B_5_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 4 xs.toFinset) B_5_4 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_3_ok C_5_4
def U_5_5 : List Nat := ([0,1]++r 4 50)
def P_5_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_5
def N_5_5 : List NodeSpec := [e5 [64] [],([66,0,1,65,3,4],[6],[]),([67,11,1,2,3,4],[7,8,9],[]),([22,0,1,2],[0,10,11,12],[0,1,3]),e5 [69] [13],([70,71,1,2,3,4],[14],[]),e5 [66] [6],([5,0,1,2,73,4],[15],[]),([5,74,1,2,3,4],[1,16],[]),([5,0,1,75,3,4],[17],[]),([16,76,6,1,2,4],[],[]),e5 [77] [],a5 [23] [16,18] [0,2],e5 [78] [],([24,0,1,2,3,79],[7,19],[]),([31,0,1,2,3,72],[20],[4]),([60,0,7,1,2,4],[21],[]),([16,5,7,2,3,4],[],[0,1,2]),([16,0,1,2,12,4],[5],[0,1]),([51,7,1,2,3,4],[22],[]),([51,8,1,2,3,4],[5],[0]),e5 [80] [4,7],([81,7,1,2,3,4],[23],[]),([55,82,0,1,2,4],[24],[4]),e5 [85] [16],a5 [50] [7,16] [0,2,4],e5 [87] [],([84,24,1,2,3,4],[25],[5]),([55,6,1,2,3,4],[4],[0]),([31,0,1,2,33,4],[16],[0,1,3,4]),([40,42,1,2,3,4],[],[0,1]),([42,5,1,2,3,4],[5],[1]),([16,41,1,2,3,4],[16],[]),([18,53,5,0,1,2],[26],[0]),e5 [37] [],a5 [88] [] [4],e5 [89] [],e5 [91] [27],([53,84,0,1,2,4],[],[]),e5 [92] [7],e5 [95] [28],([16,5,1,2,21,4],[],[0]),([5,0,1,96,3,4],[7,29],[4]),([42,41,1,2,3,4],[5],[0,1]),([16,52,1,2,3,4],[],[]),([42,0,93,2,3,4],[],[]),([5,0,1,2,33,4],[30],[]),([41,24,1,2,3,4],[25],[]),([0,1,2,29,4,10],[7,31],[0,4]),e5 [97] [],([98,0,1,2,29,4],[32],[4]),a5 [38] [1,4,5,7] [0,4],a5 [31] [4,7,16] [4],([16,53,5,1,2,4],[10],[]),([51,1,2,3,4],[],[]),([5,0,2,3,12,4],[5],[0]),([31,6,1,2,3,4],[4],[0,4]),([99,0,1,2,12,4],[5],[]),([26,0,8,1,2,3],[5],[2,4]),e5 [26] [],([5,24,1,2,3,72],[],[]),([42,5,7,2,3,4],[1,5],[]),([15,6,1,90,3,4],[5],[]),e5 [100] [],([60,0,8,1,2,4],[31],[0]),([15,14,1,2,3,4],[5],[0]),([55,0,1,2,21,4],[],[0,4]),([18,0,1,2,29,4],[],[0]),e5 [101] [],e5 [102] [4,33],([16,5,1,2,29,4],[16],[]),([31,0,1,32,3,4],[],[0,1,3,4]),([5,0,2,3,94,4],[28,34],[]),e5 [103] [35],([42,99,1,2,3,4],[7],[3,5]),e5 [29] [],([16,5,93,2,3,4],[1,5,34,36],[2]),([5,105,1,2,3,4],[1],[4]),([106,107,0,1,2,3],[37],[4]),e5 [108] [1,4,5,7],([26,5,0,2,3,4],[5],[0]),([5,6,7,3,4],[1,4,5,38],[0,1,2,3,4]),([26,0,7,93,2,3],[25],[]),([5,6,93,2,3,4],[],[2,3]),([16,5,109,2,3,4],[1],[]),([5,0,110,2,3,4],[5,39],[]),a5 [111] [7,16] [4],([55,53,0,1,2,4],[25],[4]),([15,6,1,2,3,4],[5],[0]),([112,5,1,2,3,4],[1],[]),([0,1,2,33,4],[30,40],[4,5]),([48,5,1,2,3,4],[1,16],[0]),e5 [51] [],([16,27,5,2,3,4],[1,5,16],[]),([5,113,1,2,3,4],[5,25],[]),([15,0,7,1,3,4],[1,41],[]),([5,24,93,2,3,4],[1,5,25],[]),u5 [28] [],e5 [114] [],([5,0,1,65,3,4],[6,42],[4]),([48,6,1,2,3,4],[5,16],[]),([5,0,2,3,115,4],[5],[]),a5 [116] [1,5,16,43] [1,3],a5 [25] [4,25,44] [0,1],e5 [117] [],([70,5,1,2,3,4],[1],[]),([70,7,1,2,3,4],[14],[]),([5,118,1,2,3,4],[5,7],[]),([5,0,1,2,21,10],[45],[0]),e5 [67] [7,46],([16,0,1,2,119,4],[16],[]),e5 [120] [1,47],([37,1,2,3,4],[],[0]),([5,11,1,2,3,4],[1,7,8],[]),([84,0,1,2,21,4],[],[]),e5 [121] [],e5 [33] [],e5 [122] [],a5 [123] [4,16] [4],e5 [126] [],e5 [127] [39],e5 [128] [],([129,5,0,1,2,4],[48],[]),([16,53,0,1,2,79],[25,49],[]),([51,93,1,2,3,4],[50],[]),([16,15,1,2,3,4],[16],[0]),([15,24,1,2,3,4],[5],[0]),([24,0,1,2,33,4],[51,52],[3]),([26,0,93,1,2,3],[1,5],[4]),e5 [131] [53],e5 [132] [],e5 [133] [],e5 [136] [],([103,70,1,2,3,4],[14],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_5 : checkNodesBT W_5 g_5 F_5 P_5_5 A_5 B_5_4 5 N_5_5 = true := by decide +kernel
def B_5_5 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_5
set_option maxRecDepth 500000 in
lemma B_5_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 5 xs.toFinset) B_5_5 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_4_ok C_5_5
def U_5_6 : List Nat := ([1,4,5]++r 7 4++[14,16,25,26,31,36,38,41,45,49]++r 54 53)
def P_5_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_6
def N_5_6 : List NodeSpec := [a5 [74] [1,4,5,16,25,54] [0,1,3,5],a5 [70] [1,4,10,14,16,55,56] [0,1,3,5],a5 [11] [1,4,5,9,10,25,57,58] [0,1,3,5],u5 [112,24] [7,10,16],e5 [24,137] [7,10,59],a5 [31,24] [1,10,60,61,62] [0,1,3,4],a5 [137] ([7,10,31]++r 63 4) [2,4],([16,53,0,1,2,4],[5,10,16,25,67],[0,1,3,5]),a5 [16,93] [1,5,7,68,69] [0,1,2,3],u5 [16,27] [1,7,31,69,70],u5 [16,79] [5,7,10,16,25,49],([70,1,2,3,4],[10,14,16,56],[0,1]),a5 [112] [1,4,7,10,71] [0,1,3,5],a5 [55,5] [7,16,72,73] [0,2],([0,1,2,21,10],[16,25,45,74,75],[0,1,3]),a5 [31,5] [25,72,76] [0,1,3,4],u5 [15,90] [5,25,77,78],a5 [29] [4,7,25,66,79,80] [0,4,5],([11,1,2,3,4],[8,9,10,58],[0,1,3,5]),a5 [55] [4,7,25,73,81] [0,2,4],a5 [98,5] [7,16,82] [0,1,3],a5 [42,7] [1,4,5,83,84] [0,1],a5 [41,5] [4,72,85] [0,2,4],([5,6,1,2,3,4],[1,4,5,38,72],[0,1,2,4]),a5 [42] [7,16,25,83,84,86] [0,1,2,3,4],u5 [16,109] [1,5,7,16],a5 [5,72] [1,25,72,87] [0,2,4],a5 [56,7] [1,4,16,83,88] [0,2,3,4],a5 [106,5] [25,89] [0,2],([18,53,0,1,2],[10,16,26,90,91],[0,1,3]),a5 [5,90] [1,4,72,77] [0,1,3,4],a5 [40,7] [1,4,5,25,83,92] [0,3,5],a5 [15] [1,7,16,41,77,78] [0,3],a5 [41] [7,16,25,72,85,93] [0,2,4],a5 [24,93] [1,61,68] [0,1,3],([16,0,1,2,21,4],[10,16,25,36,55],[0,1,3,5]),a5 [26] [4,5,16,94,95] [0,1,3],a5 [5,21] [1,16,55,72] [0,2,4],([16,5,1,2,3,4],[1,5,16,36,69],[0,1,2]),a5 [138] [1,5,10,16,66,96,97] [0,1,2,3],([5,24,1,2,3,4],[1,5,25,61,98],[0,1,2,3,4,5]),a5 [84] [1,7,25,99,100,101] [0,3,5],a5 [5,47] [1,4,16,72,102] [0,2,4],a5 [5,29] [1,7,16,79] [0,2],a5 [16,7] [1,4,5,7,16,69,83] [0,1,2,3,4],a5 [5,10] [1,16,25,57,72] [0,2,4],a5 [105] [1,10,16,25,103,104] [0,3],a5 [53,5] [1,5,7,10,67] [0,2,4],a5 [31] [4,7,16,76,105] [0,1,2,3,4],a5 [18,5] [1,5,16,54] [0,2],a5 [26,7] [1,4,25,94] [0,1,3],a5 [48] [1,10,16,102,106] [0,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_6 : checkNodesBT W_5 g_5 F_5 P_5_6 A_5 B_5_5 6 N_5_6 = true := by decide +kernel
def B_5_6 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_6
set_option maxRecDepth 500000 in
lemma B_5_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 6 xs.toFinset) B_5_6 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_5_ok C_5_6
def U_5_7 : List Nat := ([1,4,5,7,10,16,25,54,55,57,60,61,67,69,72,92]++r 107 12)
def P_5_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_7
def N_5_7 : List NodeSpec := [a5 [53] [1,4,5,10,67,107,108] [0,1,2,3,4],a5 [18] [1,4,5,16,25,54,109,110] [0,1,2,3,4],a5 [40] [1,4,5,10,25,92,111] [0,3,5],a5 [24] [1,4,5,10,16,25,60,61] [0,1,2,3,4,5],a5 [16] [1,4,5,7,10,16,25,69,112] [0,1,3,5],a5 [99] [1,4,5,10,16,25,113,114] [3,5],a5 [10] [1,4,5,10,16,57,115,116] [0,1,2,3,4],a5 [21] [1,4,5,10,16,55,117,118] [0,1,2,3,4],a5 [5] [1,4,5,16,25,72] [0,2,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_7 : checkNodesBT W_5 g_5 F_5 P_5_7 A_5 B_5_6 7 N_5_7 = true := by decide +kernel
def B_5_7 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_7
set_option maxRecDepth 500000 in
lemma B_5_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 7 xs.toFinset) B_5_7 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_6_ok C_5_7
def U_5_8 : List Nat := [1,4,5]
def P_5_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_8
def N_5_8 : List NodeSpec := [a5 [] [1,4,5] [0,1,2,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_8 : checkNodesBT W_5 g_5 F_5 P_5_8 A_5 B_5_7 8 N_5_8 = true := by decide +kernel
def B_5_8 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_8
set_option maxRecDepth 500000 in
lemma B_5_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 8 xs.toFinset) B_5_8 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_7_ok C_5_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_5_ok : forestRootCheck r_5 g_5 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_5_in : bucketContainsBT B_5_8 r_5 = true := by decide +kernel
lemma low_5 : Lower r_5 g_5 9 := lower_of_forestBT root_5_ok B_5_8_ok root_5_in
def g_6 := (d 0xfee8fee8fee8fee8)
def r_6 : List Nat := varsOf 15
def p_6 : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12]
def q_6 : List Nat := [2,1,4,1,4,2,8,1,8,2,8,4]
def F_6 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_6 : goodPairs g_6 p_6 q_6 := goodPairs_of (by decide +kernel)
def W_6 : BT Decor := buildWiresBT 4 (mkBase p_6 q_6 r_6) [(1,0,1),(1,4,2),(2,5,3),(1,1,2),(1,3,1),(1,3,2),(2,4,3),(1,3,0)]
lemma W_6_ok : btAll (fun x => faithful p_6 q_6 x ∧ x.1 < 2^256) W_6 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_6 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2),(1,3)]]
def A_6 : BT (List (Nat × Nat)) := btOfList 4 al_6
set_option maxHeartbeats 0 in
lemma A_6_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_6 = g_6) A_6 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_6_0 : Slice r_6 g_6 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_1 : Slice r_6 g_6 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_2 : Slice r_6 g_6 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_6_3 : Slice r_6 g_6 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_1
def S_6 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4)]
lemma S_6_ok : btAll (fun o => ∀ p, o = some p → Slice r_6 g_6 p.1 p.2) S_6 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_6_0) (forall_cons (fun _ h => by cases h; exact sl_6_1) (forall_cons (fun _ h => by cases h; exact sl_6_2) (forall_cons (fun _ h => by cases h; exact sl_6_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_6 : BT (Option PoolSpec) := btOfList 2 [q 2 [],q 1 [],q 3 [],q 0 []]
def B_6_2 : BT (List (List Nat)) := BT.empty
lemma B_6_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 2 xs.toFinset) B_6_2 := .empty
def U_6_3 : List Nat := [0,1]
def P_6_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_6 r_6 S_6 ps_6 U_6_3
def N_6_3 : List NodeSpec := [([6,0,1,2],[],[]),([0,7,8,9],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_3 : checkNodesBT W_6 g_6 F_6 P_6_3 A_6 B_6_2 3 N_6_3 = true := by decide +kernel
def B_6_3 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_3
set_option maxRecDepth 500000 in
lemma B_6_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 3 xs.toFinset) B_6_3 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_2_ok C_6_3
def U_6_4 : List Nat := [1,2,3]
def P_6_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_6 r_6 S_6 ps_6 U_6_4
def N_6_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([10,0,1,2,3],[],[]),([0,1,2,11,8],[1,3],[10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_4 : checkNodesBT W_6 g_6 F_6 P_6_4 A_6 B_6_3 4 N_6_4 = true := by decide +kernel
def B_6_4 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_4
set_option maxRecDepth 500000 in
lemma B_6_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 4 xs.toFinset) B_6_4 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_3_ok C_6_4
def U_6_5 : List Nat := (r 0 4)
def P_6_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_6 r_6 S_6 ps_6 U_6_5
def N_6_5 : List NodeSpec := [([0,1,4,2,3],(r 0 4),[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_5 : checkNodesBT W_6 g_6 F_6 P_6_5 A_6 B_6_4 5 N_6_5 = true := by decide +kernel
def B_6_5 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_5
set_option maxRecDepth 500000 in
lemma B_6_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 5 xs.toFinset) B_6_5 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_4_ok C_6_5
def U_6_6 : List Nat := (r 0 4)
def P_6_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_6 r_6 S_6 ps_6 U_6_6
def N_6_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,4,6,8,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_6 : checkNodesBT W_6 g_6 F_6 P_6_6 A_6 B_6_5 6 N_6_6 = true := by decide +kernel
def B_6_6 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_6
set_option maxRecDepth 500000 in
lemma B_6_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 6 xs.toFinset) B_6_6 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_5_ok C_6_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_6_ok : forestRootCheck r_6 g_6 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_6_in : bucketContainsBT B_6_6 r_6 = true := by decide +kernel
lemma low_6 : Lower r_6 g_6 7 := lower_of_forestBT root_6_ok B_6_6_ok root_6_in
def g_7 := (d 0xfee80000fee80000)
def r_7 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_7 : Lower r_7 g_7 8 := by
  exact lift_of_f (z := 0) (o := 16) (other := r_6) (G := g_6) (essPairs := [(VAR 4,3,19)]) (by decide +kernel) low_6
def g_8 := (d 0xfffffee8fffffee8)
def r_8 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 8 := by
  exact lift_of_f (z := 16) (o := 0) (other := r_6) (G := g_6) (essPairs := [(VAR 4,0,16)]) (by decide +kernel) low_6
def g_9 := (d 0xfec0fec0fec0fec0)
def r_9 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_9 : Lower r_9 g_9 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_10 := (d 0xfee0fee0fee0fee0)
def r_10 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_10 : Lower r_10 g_10 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
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
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_1 : Slice r_11 g_11 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xffa0a000ffa0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_2 : Slice r_11 g_11 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_3 : Slice r_11 g_11 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeeee00ffeeee00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_4 : Slice r_11 g_11 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_5 : Slice r_11 g_11 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_6 : Slice r_11 g_11 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_11_7 : Slice r_11 g_11 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_11_8 : Slice r_11 g_11 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
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
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_1 : Slice r_12 g_12 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_2 : Slice r_12 g_12 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_3 : Slice r_12 g_12 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_4 : Slice r_12 g_12 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec8c8fefec8c8) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_5 : Slice r_12 g_12 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefea8a8fefea8a8) 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_10
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
def g_13 := (d 0xfffffe80fffffe80)
def r_13 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_13 : Lower r_13 g_13 7 := by
  exact lift_of_f (z := 16) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 4,0,16)]) (by decide +kernel) low_0
def g_14 := (d 0xfe800000fe800000)
def r_14 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 7 := by
  exact lift_of_f (z := 0) (o := 16) (other := r_0) (G := g_0) (essPairs := [(VAR 4,7,23)]) (by decide +kernel) low_0
def g_15 := (d 0xfc80fc80fc80fc80)
def r_15 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_16 := (d 0xfff8e800fff8e800)
def r_16 : List Nat := varsOf 31
def p_16 : List Nat := [11,11,11,13,13,13,14,14,14,15,19,19,19,20,20,21,21,22,22,23,24,24,25,25,26,26,28]
def q_16 : List Nat := [10,9,3,12,9,5,12,10,6,7,18,17,3,16,4,17,5,18,6,7,16,8,17,9,18,10,12]
def F_16 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_16 : goodPairs g_16 p_16 q_16 := goodPairs_of (by decide +kernel)
def W_16 : BT Decor := buildWiresBT 3 (mkBase p_16 q_16 r_16) [(1,2,4)]
lemma W_16_ok : btAll (fun x => faithful p_16 q_16 x ∧ x.1 < 2^256) W_16 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_16 : List (List (Nat × Nat)) := [[]]
def A_16 : BT (List (Nat × Nat)) := btOfList 1 al_16
set_option maxHeartbeats 0 in
lemma A_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_16 = g_16) A_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_16_0 : Slice r_16 g_16 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_1 : Slice r_16 g_16 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_2 : Slice r_16 g_16 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffafa00fffafa00) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_3 : Slice r_16 g_16 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xff888800ff888800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_4 : Slice r_16 g_16 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_5 : Slice r_16 g_16 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_6 : Slice r_16 g_16 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_16_7 : Slice r_16 g_16 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_16_8 : Slice r_16 g_16 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_16 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 1 0,5),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (identDom 2 3,6)]
lemma S_16_ok : btAll (fun o => ∀ p, o = some p → Slice r_16 g_16 p.1 p.2) S_16 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_16_0) (forall_cons (fun _ h => by cases h; exact sl_16_1) (forall_cons (fun _ h => by cases h; exact sl_16_2) (forall_cons (fun _ h => by cases h; exact sl_16_3) (forall_cons (fun _ h => by cases h; exact sl_16_4) (forall_cons (fun _ h => by cases h; exact sl_16_5) (forall_cons (fun _ h => by cases h; exact sl_16_6) (forall_cons (fun _ h => by cases h; exact sl_16_7) (forall_cons (fun _ h => by cases h; exact sl_16_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_16 : BT (Option PoolSpec) := btOfList 4 [q 4 [],q 0 [],q 1 [],q 2 [],q 5 [16393],q 3 [],q 6 [],q 7 [],q 5 [],q 8 []]
def B_16_5 : BT (List (List Nat)) := BT.empty
lemma B_16_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 5 xs.toFinset) B_16_5 := .empty
def U_16_6 : List Nat := (r 0 8)
def P_16_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_6
def N_16_6 : List NodeSpec := [e5 [5] (r 0 8)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_6 : checkNodesBT W_16 g_16 F_16 P_16_6 A_16 B_16_5 6 N_16_6 = true := by decide +kernel
def B_16_6 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_6
set_option maxRecDepth 500000 in
lemma B_16_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 6 xs.toFinset) B_16_6 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_5_ok C_16_6
def U_16_7 : List Nat := (r 0 4++r 5 5)
def P_16_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_7
def N_16_7 : List NodeSpec := [u5 [] (r 0 4++r 5 5)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_7 : checkNodesBT W_16 g_16 F_16 P_16_7 A_16 B_16_6 7 N_16_7 = true := by decide +kernel
def B_16_7 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_7
set_option maxRecDepth 500000 in
lemma B_16_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 7 xs.toFinset) B_16_7 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_6_ok C_16_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck r_16 g_16 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT B_16_7 r_16 = true := by decide +kernel
lemma low_16 : Lower r_16 g_16 8 := lower_of_forestBT root_16_ok B_16_7_ok root_16_in
def g_17 := (d 0xfffffee8fe800000)
def r_17 : List Nat := varsOf 63
def p_17 : List Nat := [23,23,23,23,25,25,25,26,26,26,27,27,28,28,28,29,29,30,30,31,35,35,35,37,37,37,38,38,38,39,41,41,41,42,42,42,43,44,44,44,45,46,47,48,48,49,49,50,50,51,52,52,53,54,56,56]
def q_17 : List Nat := [22,21,19,7,24,17,9,24,18,10,19,11,24,20,12,21,13,22,14,15,34,33,3,36,33,5,36,34,6,7,40,33,9,40,34,10,11,40,36,12,13,14,15,32,16,33,17,34,18,19,36,20,21,22,40,24]
def F_17 : Nat := fullMask 56
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 9 (mkBase p_17 q_17 r_17) [(0,4,5),(1,4,5),(3,6,7),(1,1,2),(1,0,3),(0,9,10),(0,1,2),(1,12,3),(2,4,5),(3,4,5),(0,13,7),(3,11,7),(0,0,1),(1,18,3),(2,19,6),(1,0,1),(1,2,3),(0,21,22),(1,11,6),(2,0,3),(2,9,3),(3,12,10),(1,1,3),(0,28,7),(0,2,29),(1,2,29),(3,30,31),(2,2,0),(3,33,28),(1,12,6),(2,10,6),(0,2,5),(1,2,5),(3,37,38),(2,39,18),(1,23,6),(0,10,7),(2,22,6),(0,43,0),(1,43,0),(3,44,45),(3,12,7),(1,2,4),(0,48,5),(2,19,49),(3,0,5),(1,51,4),(0,13,52),(3,3,7),(0,54,0),(1,54,0),(3,55,56),(1,3,6),(0,2,58),(1,2,58),(3,59,60),(3,39,1),(3,62,0),(3,39,0),(1,64,1),(0,39,0),(1,39,0),(0,22,7),(2,0,68),(1,69,3),(1,0,29),(3,3,71),(1,1,68),(0,0,73),(3,36,1),(1,75,3),(1,36,1),(2,77,2),(1,36,2),(0,79,1),(2,28,6),(0,81,0),(1,81,0),(0,39,10),(2,1,2),(2,0,2),(3,33,68),(3,1,5),(1,88,4),(0,10,89),(2,36,2),(3,36,2),(2,10,49),(2,0,1),(2,1,3),(3,95,39),(1,86,3),(2,21,3),(2,43,33),(1,43,18),(0,1,5),(1,1,5),(3,101,102),(2,103,2),(3,103,2),(0,13,5),(1,106,4),(3,14,13),(3,0,68),(3,12,52),(2,19,4),(3,2,7),(3,2,5),(1,113,4),(0,19,114),(3,3,4),(3,116,9),(0,111,5),(3,0,4),(3,119,13),(2,77,3),(2,13,4),(3,122,5),(1,3,4),(0,124,5),(1,12,125),(3,2,71),(0,19,7),(1,2,6),(1,0,4),(0,130,5),(1,0,5),(0,13,132),(1,12,131),(1,3,5),(0,9,135),(3,3,5),(1,137,4),(3,12,138),(0,0,29),(1,12,42),(2,22,4),(1,142,18),(0,10,5),(1,12,144),(0,27,7),(2,27,6),(3,54,0),(1,148,2),(2,0,58),(3,0,58),(0,0,58),(1,152,2),(2,39,3),(1,1,42),(3,119,28),(2,156,2),(1,156,2),(0,10,114),(3,1,7),(1,0,58),(0,10,102),(3,1,4),(3,163,10),(1,1,4),(0,165,5),(0,0,5),(1,12,167),(1,94,3),(3,2,4),(1,170,18),(0,2,4),(1,18,125),(2,2,4),(3,174,5),(2,21,172),(2,10,4),(3,14,19),(0,22,5),(1,37,4),(2,2,3),(1,181,4),(1,174,18),(2,54,2),(3,54,2),(0,13,4),(1,39,3),(3,2,42),(2,0,6),(0,19,5),(1,190,4),(2,21,6),(3,185,0),(0,19,38),(2,19,5),(2,2,5),(3,196,21),(3,181,5),(2,0,5),(0,21,7),(0,2,7),(1,2,162),(3,111,5),(3,12,132),(0,21,135),(3,116,21),(3,2,162),(3,59,0),(1,1,6),(3,119,9),(2,1,4),(1,211,86),(0,21,38),(2,1,5),(1,214,86),(1,12,4),(0,28,5),(1,85,167),(0,21,5),(1,219,3),(3,211,5),(1,113,18),(1,196,18),(3,12,124),(3,12,135),(3,95,5),(3,12,5),(3,37,21),(0,21,48),(1,227,3),(3,51,9),(2,0,4),(0,0,7),(2,21,4),(1,234,3),(1,116,86),(1,95,4),(1,101,4),(1,167,3),(3,174,21),(0,0,4),(3,12,130),(1,85,4),(1,137,18),(1,18,6),(3,33,165),(1,18,4),(3,3,247),(1,85,241),(1,12,241),(3,137,21),(0,1,7),(0,19,4),(1,116,18),(3,172,10),(1,86,4),(3,3,256),(3,33,5),(1,258,3),(3,33,124),(3,33,102),(3,33,135),(0,1,4),(1,94,170),(1,137,86),(1,86,6),(3,33,7),(0,21,124),(0,10,165),(1,232,3),(3,174,10),(1,94,113),(3,37,10),(3,196,10),(3,51,28),(1,167,4),(3,3,276),(1,3,131),(1,3,175),(3,3,114),(3,2,58),(1,113,3),(1,137,0),(1,170,3),(3,3,132),(1,199,3),(3,3,130),(3,2,124),(3,137,0),(3,124,5),(0,0,124),(1,25,4),(1,241,3),(1,14,3)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^256) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_17 : BT (List (Nat × Nat)) := btOfList 3 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (subcubeFast 8 0) 9 := by
  have hc : Lower (varsOf 55) (d 0xffffe8e880800000) 9 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 16 0) 8 := by
  have hc : Lower (varsOf 47) (d 0xfee8fee800000000) 8 := carry_of (swaps := [(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 0 32) 8 := by
  exact slice_fast_direct_f (z := 0) (o := 32) (by decide +kernel) low_8
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffffaa0fa000000) 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffee88ee000000) 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 1 0) 8 := by
  have hc : Lower (varsOf 62) (d 0xfffffcc0fc000000) 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (subcubeFast 16 32) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 32) (by decide +kernel) low_6
set_option maxHeartbeats 0 in
lemma sl_17_7 : Slice r_17 g_17 (subcubeFast 0 1) 8 := by
  have hc : Lower (varsOf 62) (d 0xfffffffcffc00000) 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_8 : Slice r_17 g_17 (subcubeFast 0 2) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffffffaffa00000) 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_9 : Slice r_17 g_17 (subcubeFast 0 4) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffffeeff880000) 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_10 : Slice r_17 g_17 (subcubeFast 0 16) 7 := by
  have hc : Lower (varsOf 47) (d 0xfffffffffe80fe80) 7 := carry_of (swaps := [(4,5)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_11 : Slice r_17 g_17 (subcubeFast 32 0) 7 := by
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) low_14
set_option maxHeartbeats 0 in
lemma sl_17_12 : Slice r_17 g_17 (identDom 1 4) 8 := by
  have hc : Lower (varsOf 47) (d 0xfeecfeeccc80cc80) 8 := carry_of (swaps := [(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_16
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_13 : Slice r_17 g_17 (identDom 2 4) 8 := by
  have hc : Lower (varsOf 47) (d 0xfef8fef8f080f080) 8 := carry_of (swaps := [(2,4),(3,4),(4,5)]) (by decide +kernel) low_16
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_14 : Slice r_17 g_17 (identDom 0 4) 8 := by
  have hc : Lower (varsOf 47) (d 0xfeeafeeaaa80aa80) 8 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_16
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_15 : Slice r_17 g_17 (identDom 0 2) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffeeaaee880000) 8 := carry_of (swaps := [(0,2),(1,2),(2,5),(3,5),(4,5)]) (by decide +kernel) low_16
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_16 : Slice r_17 g_17 (identDom 0 1) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffffaaafaa00000) 8 := carry_of (swaps := [(0,2),(1,5),(3,5),(4,5)]) (by decide +kernel) low_16
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_17 : Slice r_17 g_17 (identDom 1 2) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffeeccee880000) 8 := carry_of (swaps := [(1,2),(2,5),(3,5),(4,5)]) (by decide +kernel) low_16
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_18 : Slice r_17 g_17 (subcubeFast 8 2) 6 := by
  have hc : Lower (varsOf 53) (d 0xfffffafaa0a00000) 6 := carry_of (swaps := [(1,4),(2,4),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_19 : Slice r_17 g_17 (subcubeFast 8 4) 6 := by
  have hc : Lower (varsOf 51) (d 0xffffeeee88880000) 6 := carry_of (swaps := [(2,4),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_20 : Slice r_17 g_17 (subcubeFast 8 1) 6 := by
  have hc : Lower (varsOf 54) (d 0xfffffcfcc0c00000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_21 : Slice r_17 g_17 (subcubeFast 32 16) 6 := by
  exact slice_fast_direct_f (z := 32) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_17_22 : Slice r_17 g_17 (subcubeFast 24 32) 4 := by
  exact slice_fast_direct_f (z := 24) (o := 32) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_17_23 : Slice r_17 g_17 (subcubeFast 20 32) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 20) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_24 : Slice r_17 g_17 (subcubeFast 18 32) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 18) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_25 : Slice r_17 g_17 (subcubeFast 6 8) 4 := by
  have hc : Lower (varsOf 49) (d 0xffffaaaaaaaa0000) 4 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 6) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_26 : Slice r_17 g_17 (subcubeFast 17 32) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 17) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_27 : Slice r_17 g_17 (subcubeFast 5 8) 4 := by
  have hc : Lower (varsOf 50) (d 0xffffcccccccc0000) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 5) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_28 : Slice r_17 g_17 (subcubeFast 3 8) 4 := by
  have hc : Lower (varsOf 52) (d 0xfffff0f0f0f00000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 3) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_29 : Slice r_17 g_17 (subcubeFast 3 4) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 3) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_30 : Slice r_17 g_17 (subcubeFast 5 2) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 5) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_31 : Slice r_17 g_17 (subcubeFast 6 1) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 6) (o := 1) (by decide +kernel) hc
def S_17 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 8 0,9),some (subcubeFast 16 0,8),some (subcubeFast 0 32,8),some (subcubeFast 2 0,8),some (subcubeFast 4 0,8),some (subcubeFast 1 0,8),some (subcubeFast 16 32,7),some (subcubeFast 0 1,8),some (subcubeFast 0 2,8),some (subcubeFast 0 4,8),some (subcubeFast 0 16,7),some (subcubeFast 32 0,7),some (identDom 1 4,8),some (identDom 2 4,8),some (identDom 0 4,8),some (identDom 0 2,8),some (identDom 0 1,8),some (identDom 1 2,8),some (subcubeFast 8 2,6),some (subcubeFast 8 4,6),some (subcubeFast 8 1,6),some (subcubeFast 32 16,6),some (subcubeFast 24 32,4),some (subcubeFast 20 32,4),some (subcubeFast 18 32,4),some (subcubeFast 6 8,4),some (subcubeFast 17 32,4),some (subcubeFast 5 8,4),some (subcubeFast 3 8,4),some (subcubeFast 3 4,4),some (subcubeFast 5 2,4),some (subcubeFast 6 1,4)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (forall_cons (fun _ h => by cases h; exact sl_17_7) (forall_cons (fun _ h => by cases h; exact sl_17_8) (forall_cons (fun _ h => by cases h; exact sl_17_9) (forall_cons (fun _ h => by cases h; exact sl_17_10) (forall_cons (fun _ h => by cases h; exact sl_17_11) (forall_cons (fun _ h => by cases h; exact sl_17_12) (forall_cons (fun _ h => by cases h; exact sl_17_13) (forall_cons (fun _ h => by cases h; exact sl_17_14) (forall_cons (fun _ h => by cases h; exact sl_17_15) (forall_cons (fun _ h => by cases h; exact sl_17_16) (forall_cons (fun _ h => by cases h; exact sl_17_17) (forall_cons (fun _ h => by cases h; exact sl_17_18) (forall_cons (fun _ h => by cases h; exact sl_17_19) (forall_cons (fun _ h => by cases h; exact sl_17_20) (forall_cons (fun _ h => by cases h; exact sl_17_21) (forall_cons (fun _ h => by cases h; exact sl_17_22) (forall_cons (fun _ h => by cases h; exact sl_17_23) (forall_cons (fun _ h => by cases h; exact sl_17_24) (forall_cons (fun _ h => by cases h; exact sl_17_25) (forall_cons (fun _ h => by cases h; exact sl_17_26) (forall_cons (fun _ h => by cases h; exact sl_17_27) (forall_cons (fun _ h => by cases h; exact sl_17_28) (forall_cons (fun _ h => by cases h; exact sl_17_29) (forall_cons (fun _ h => by cases h; exact sl_17_30) (forall_cons (fun _ h => by cases h; exact sl_17_31) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_17 : BT (Option PoolSpec) := btOfList 11 [q 0 [4096,4097,90196,20496,20497,28699],q 0 [20496,20497,28699],q 0 [4097,90196,20496,20497,28699],q 7 [20496,20497,28699],q 16 [12297,20496,20497,28699],q 0 [4096,4097,20496,20497,28699],q 0 [8196,8197,40996,20497,28719],q 0 [20497,28784,118792,118793,127099],q 0 [4096,4097,90196,20498,20499],q 0 [4096,4097,90196,20496,20497],q 5 [20496,20497,28699],q 3 [20496,20497,28699],q 4 [20496,20497,28699],q 0 [8196,8197,40996,20496,24625],q 25 [],q 3 [20488,20489,155799],q 7 [20488,20489,155799,73886],q 7 [8196,12337,8197],q 5 [8196,12337,8197,40996],q 0 [8196,8197,20496,20497,28699],q 17 [12290,20496,20497,28699],q 6 [8196,12337,8197],q 8 [12337,20496,20497,28699],q 0 [4096,4097,90196,20496,24669],q 0 [20496,24666,172,173,184499],q 0 [8196,8197,40996,20497,28723],q 1 [28687,216,217,229599],q 6 [216,217,229599],q 1 [237576,237577,245999],q 6 [237576,237577,245999],q 5 [20488,20489,155799],q 0 [20488,20489,155799,4255,251],q 23 [],q 0 [20488,20489,155799,159,4353],q 8 [20488,20489,155799],q 15 [],q 7 [20488,20489,155799],q 0 [20488,20489,155799,156,157],q 27 [],q 6 [156,157],q 5 [],q 4 [20497,28760],q 3 [20497,28784],q 7 [],q 28 [],q 8 [],q 0 [20497,28760,278533,299008],q 3 [],q 0 [],q 5 [20496,24618],q 0 [20496,24618,4241,8502],q 0 [20496,24618,8337,4412],q 9 [],q 0 [20496,24690,324,325],q 0 [20488,20489,155799],q 0 [20488,20489,155799,41116],q 1 [20488,20489,155799],q 6 [12289,41116],q 20 [20496,20497,28699],q 0 [8198,20496,20497,28699],q 8 [20496,20497,28699],q 15 [12293,20496,20497,28699],q 0 [8194,20496,20497,28699],q 9 [20496,20497,28699],q 6 [8194,12289],q 8 [12289,20496,20497,28699],q 0 [20496,24618,8338,8339],q 0 [20488,20489,155799,160127],q 6 [12294,160127],q 18 [20488,20489,155799],q 6 [8194,12633],q 0 [20498,20499],q 0 [4097,90196,20498,20499],q 0 [8197,40996,20497,28719],q 0 [4097,90196,20496,24669],q 7 [12297,20496,24669],q 6 [4097,12374],q 0 [4097,20496,20497,28699],q 0 [8196,20496,20497,28699],q 0 [4096,20496,20497,28699],q 4 [20496,24666],q 1 [],q 5 [20496,20497],q 3 [20496,20497],q 4 [20496,20497],q 4 [],q 3 [12297,20496,24654],q 5 [20496,24654],q 9 [20484,20485,418199],q 17 [],q 4 [20484,20485,418199],q 0 [20484,20485,418199,8606,8607],q 6 [8606,8607],q 7 [20498,20499],q 0 [8196,8197,20532,16809],q 0 [8197,20496,20497,28699],q 5 [20498,20499],q 3 [20498,20499],q 4 [20498,20499],q 1 [8196,12337,8197],q 0 [8196,8197],q 3 [20497,28724],q 0 [8196,8197,20497,28724],q 8 [12337,20497,28724],q 1 [8196,12337,8197,28724],q 2 [8196,12337,8197],q 0 [4096,4097,90196,20498],q 0 [20497,28760,278530,278531],q 0 [8196,8197,20496,20497],q 8 [12337,20496,20497],q 0 [4096,4097],q 3 [20496,24654],q 8 [20483,16589,213043],q 1 [8196,8197,20483,213043],q 2 [8196,8197,16589,213043],q 0 [4096,4097,20496,24654],q 7 [12361,20496,24654],q 1 [4096,12361,4097],q 2 [4096,12361,4097,24654],q 2 [4096,12361,4097],q 6 [4096,12361,4097],q 3 [12297,90196],q 0 [4096,4097,90196,20496],q 9 [4096,4097],q 4 [4096,4097,90196],q 0 [8196,8197,40996],q 8 [12337,12289],q 0 [4096,4097,20497,28683],q 9 [4096,12361,4097],q 7 [12361,20497,28683],q 3 [20497,28683],q 1 [4096,12361,4097,28683],q 5 [8196,12337,8197],q 7 [12297,20496,20497,28699],q 0 [8196,8197,16387,53727],q 8 [12337,16387,53727],q 16 [12297,20498,20499],q 0 [4096,4097,20498,20499],q 8 [16397,20976,512049],q 0 [8196,8197,20976,512049],q 1 [8196,8197,20976,512049],q 2 [8196,8197,16397,512049],q 0 [20497,28784,118785,290827],q 5 [20497,28748],q 3 [20497,28748],q 0 [4096,4097,20496,24585],q 7 [12361,20496,24585],q 3 [20496,24585],q 2 [4096,12361,4097,24585],q 0 [4096,4097,20488,20489,155799],q 6 [4096,4097],q 16 [20488,20489,155799],q 0 [8196,8197,20481,540724],q 8 [12337,20481,540724],q 7 [20496,20497],q 1 [8196,8197,21000,536625],q 2 [8196,8197,16385,536625],q 8 [16385,21000,536625],q 0 [8196,8197,20498,20499],q 8 [12337,20498,20499],q 8 [20495,16933,565299],q 0 [8196,8197,16933,565299],q 1 [8196,8197,20495,565299],q 2 [8196,8197,16933,565299],q 17 [12289],q 0 [8196,8197,20497,28723],q 8 [20497,28723],q 16 [12297,20497,28760],q 0 [4096,4097,20497,28760],q 0 [20496,20497],q 0 [4097,90196,20496,20497],q 6 [4096,73886],q 6 [4096,12361],q 0 [20497,28784,118784,118785],q 0 [4096,4097,90196,20497],q 2 [],q 7 [12297,16474,74297],q 0 [4096,4097,16474,74297],q 8 [12289,20520,589873],q 0 [8196,8197,20520,589873],q 0 [8196,8197,20496,24625],q 8 [20496,24625],q 1 [8196,8197],q 21 [8196,8197],q 0 [8196,8197,20496,24618],q 17 [12289,20496,24618],q 17 [12290,20498,20499],q 0 [4096,4097,90196,20499],q 16 [12297,20496,20497],q 0 [4096,4097,20496,20497],q 6 [4097,12290],q 9 [12290,20496,20497,28699],q 17 [12290,20496,20497],q 17 [12290],q 16 [20496,20497,28699],q 5 [20497,28687],q 22 [],q 9 [20497,28687],q 5 [20496,24589],q 7 [20496,24589],q 1 [237570,237571],q 9 [20496,24589],q 6 [12446],q 0 [20488,20489,155799,157],q 6 [156],q 29 [],q 0 [20488,20489,155799,156],q 6 [],q 6 [12290],q 0 [20497,28712,172037],q 2 [12289],q 7 [20497],q 0 [20497,28784],q 10 [12293],q 1 [12293,28784],q 8 [20497,118784],q 0 [20497,28784,118784],q 6 [12289],q 0 [20496,24618,4243],q 7 [20496],q 1 [12289],q 0 [20496,24618,8338],q 7 [20496,8338],q 0 [20496,24618,4241],q 0 [20496,24690],q 3 [20496,24690],q 0 [20496,24690,324],q 8 [20496,324],q 8 [16387,8818],q 7 [12293],q 0 [20488,20489,155799,159],q 5 [20484,20485,418199],q 24 [],q 31 [],q 0 [8194,20484,20485,418199],q 6 [8194],q 15 [20484,20485,418199],q 20 [20498,20499],q 0 [8198,20498,20499],q 20 [20496,20497],q 0 [8198,20496,20497],q 8 [20498,20499],q 15 [12293,20498,20499],q 0 [8194,20498,20499],q 9 [20498,20499],q 8 [20497],q 15 [12293,20497,28784],q 0 [8194,20497,28784],q 7 [20491,16837],q 0 [20491,16837,466984],q 6 [12289,466984],q 30 [],q 0 [8198],q 0 [8198,20496,24618],q 10 [],q 5 [12293,114823],q 8 [10],q 0 [10,114823],q 8 [20496,20497],q 15 [12293,20496,20497],q 0 [8194,20496,20497],q 9 [20496,20497],q 8 [12289,20497,28712],q 5 [20497,28712],q 0 [20497,28712],q 2 [8194,12289],q 5 [20497,28679],q 8 [12289],q 7 [20497,28679],q 0 [20497,28679],q 4 [20497,28679],q 1 [237568,237569],q 8 [12289,20496,20497],q 1 [8194,12289],q 0 [8194],q 5 [20485,417832],q 7 [20485],q 0 [20485,417832],q 5 [16391,41615],q 7 [16391],q 0 [16391,41615],q 3 [20480],q 2 [8196,8197,684081],q 5 [8196,8197],q 6 [8196,8197,684081],q 8 [20480,684081],q 0 [8196,8197,20480,684081],q 5 [20496,24585],q 8 [20496,24585],q 1 [4098,12665],q 9 [4098,12665],q 6 [4098,12665],q 1 [4097,12290],q 0 [4097,20498,20499],q 9 [12290,20498,20499],q 7 [20499],q 1 [4096,4097],q 7 [16395,74409],q 3 [16395],q 0 [4096,4097,16395,74409],q 5 [20499],q 3 [20499],q 4 [20499],q 8 [12289,20498,20499],q 16 [16392,16393],q 0 [4096,4097,16392,16393],q 7 [16392,16393],q 13 [4096,4097],q 5 [16397,20976],q 3 [16397,20976],q 0 [4096,20976,512073],q 1 [4096,20976,512073],q 2 [4096,16397,512073],q 6 [4096,512073],q 20 [8196,8197],q 0 [8196,8197,20498],q 17 [12290,20498],q 0 [4097,20496,20497],q 1 [4097,12374],q 2 [4097,12374],q 8 [12289,20496,24618],q 0 [20496,24618],q 16 [16394,21179],q 7 [16394,21179],q 1 [4096,4097,21179],q 2 [4096,4097,16394],q 3 [16392,704598],q 4 [4096,4097],q 0 [4096,4097,16392,704598],q 0 [8196,8197,16426],q 10 [8196,8197],q 3 [12289,16426],q 8 [12289,16426],q 2 [8196,8197],q 11 [8196,8197],q 7 [8196,8197],q 17 [12289,16426],q 21 [],q 0 [20498],q 0 [4097,90196,20498],q 1 [4096,12361],q 7 [12297,20497,28760],q 0 [4097,20497,28760],q 0 [8197,20496,20497],q 0 [4096],q 0 [4096,4097,16462],q 7 [12361,16462],q 4 [4096,12361,4097],q 3 [16462],q 16 [12297,20496],q 3 [12297],q 7 [12297],q 0 [4096,4097,20496],q 21 [4096,4097],q 16 [12297,20568],q 0 [4096,4097,20568],q 3 [12297,20568],q 11 [4096,4097],q 7 [12297,20568],q 2 [4096,4097],q 10 [4096,4097],q 0 [8197,20496,24618],q 16 [20488,16533],q 7 [20488,16533],q 1 [4096,4097,20488],q 2 [4096,4097,16533],q 16 [12298,17109],q 0 [4096,4097,17109],q 3 [12298,17109],q 7 [12298,17109],q 2 [4096,12361],q 0 [4096,20496,20497],q 5 [8196,41011],q 7 [8196],q 8 [12289,41011],q 9 [12289,41011],q 0 [8196,41011],q 16 [12297,20497],q 0 [4096,4097,20497],q 0 [4096,20496,24654],q 0 [8196,8197,20497],q 8 [12337,20497],q 3 [20497],q 7 [16394,74425],q 0 [4096,4097,16394,74425],q 1 [4096,4097,74425],q 6 [4096,4097,74425],q 7 [12361],q 7 [12361,16395],q 0 [4096,4097,16395],q 4 [20497,28687],q 1 [28687,8410,8411],q 6 [8410,8411],q 1 [8196,21000,536625],q 6 [8196,536625],q 3 [16385,21000],q 4 [16385,21000],q 16 [20488,20489],q 3 [20488,20489],q 0 [8196,8197,16436],q 8 [12337,16399],q 0 [8196,8197,20532],q 0 [20497,28712,172043],q 7 [20497,172043],q 7 [12361,20491],q 0 [4096,4097,20491],q 3 [20496,24578],q 17 [20496,24578],q 6 [8196,8197],q 0 [4096,20556,17145],q 16 [],q 16 [20496,24662],q 0 [8196,8197,20496],q 8 [12337,20496],q 3 [20496],q 16 [20495,16933],q 0 [4096,4097,16933],q 3 [20495,16933],q 7 [20495,16933],q 16 [12297,20499],q 0 [4096,4097,20499],q 5 [20498],q 3 [20498],q 4 [20498],q 0 [8196,8197,20499],q 17 [12290,20499],q 5 [20489,155724],q 3 [20489,155724],q 9 [4096,12361],q 16 [16393,20672],q 3 [16393,20672],q 7 [16393,20672],q 1 [4096,4097,20672],q 20 [8197],q 5 [8197,12326],q 18 [],q 9 [12290],q 0 [8196,8197,20481],q 8 [12337,20481],q 0 [4096,4097,20558],q 7 [12361,20558],q 8 [12337,20493],q 0 [8197,20498,20499],q 3 [20490,86803],q 4 [20495,16933],q 0 [8196,16933,565299],q 6 [8196,565299],q 16 [12298,21207],q 0 [4096,4097,21207],q 3 [12298,21207],q 7 [12298,21207],q 0 [8196,20496,24625],q 4 [20496],q 9 [20496,24625],q 1 [8196],q 21 [8196],q 8 [12337,20499],q 6 [4097],q 17 [20482,20483],q 0 [8196,8197,20482,20483],q 7 [12633],q 1 [8194,12633],q 11 [],q 19 [],q 16 [20498,20499],q 16 [20491,16837],q 3 [20491,16837],q 5 [20497],q 5 [12297],q 7 [12361,12297],q 8 [12361,12297],q 4 [20497],q 4 [4096,12361],q 16 [20497,28756],q 3 [20497,28756],q 1 [4096,4097,28756],q 15 [20496,20497,28699],q 4 [20672],q 3 [12289,20520],q 4 [12289,20520],q 0 [8196,20520,589873],q 0 [8196,16387,53727],q 1 [8196,12337],q 6 [8196,12337],q 7 [8196,12337],q 3 [16387,53727],q 4 [16387,53727],q 3 [20483,16589],q 4 [20483,16589],q 6 [8196,213043],q 0 [4096,20498,20499],q 4 [16837],q 0 [8196,20496,20497],q 5 [20496],q 0 [8196,8197,16385],q 8 [12337,16385],q 0 [4096,20488,20489,155799],q 6 [4096],q 16 [20497,28680],q 3 [20497,28680],q 1 [4096,4097,28680],q 0 [4096,20496,24585],q 2 [4096,12361,24585],q 3 [20497,28687],q 16 [20497,28687],q 1 [4096,4097,28687],q 3 [12289,417832],q 3 [20481],q 8 [20481,540723],q 0 [8196,8197,20481,540723],q 16 [16397,20976],q 0 [4096,4097,20976],q 7 [16397,20976],q 1 [4096,4097,20976],q 7 [20498],q 3 [20493,553044],q 0 [4096,4097,553044],q 16 [20496,24585],q 7 [20496,24585],q 2 [4096,4097,24585],q 16 [20496,24589],q 3 [20496,24589],q 0 [4096,20497,28683],q 5 [20497,28683],q 1 [4096,12361,28683],q 16 [20496,20497],q 17 [12290,20497],q 3 [12290],q 8 [12290],q 7 [20497,28683],q 16 [20497,28683],q 5 [12297,16474],q 3 [12297,16474],q 0 [4096,16474,74297],q 0 [4096,20497,28748],q 1 [4096,12361,28748],q 0 [8196,20497,28723],q 9 [20497,28723],q 17 [12290,20496],q 20 [],q 1 [12290],q 0 [16393,20672,200746],q 6 [12289,200746],q 2 [12290],q 0 [8196,20498,20499],q 0 [4096,4097,90196],q 3 [16399,86483],q 0 [4096,4097,86483],q 7 [12297,20498,20499],q 16 [12297,20498],q 0 [4096,4097,20498],q 2 [4097,12290],q 9 [12290,20496,20497],q 7 [20497,28687],q 1 [28687,216,217],q 2 [216,217],q 0 [8196,20496,24618],q 7 [20485,663563],q 5 [12297,90196],q 8 [12297],q 0 [20496],q 0 [4097,90196,20496],q 9 [4097],q 4 [4097,90196],q 0 [20497],q 0 [4097,90196,20497],q 4 [20496,24589],q 1 [237576,239],q 0 [20499],q 0 [4097,90196,20499],q 9 [20497],q 2 [12297],q 0 [20497,28760,278530],q 5 [20496,24581],q 7 [20496,24581],q 0 [20496,24581],q 4 [20496,24581],q 7 [12297,20496,20497],q 0 [4097,20488,20489,155799],q 8 [12337],q 8 [12337,20498],q 2 [8194,12633],q 7 [20484,20485,418199],q 0 [20484,20485,418199],q 6 [8606],q 0 [20484,20485,418199,8606],q 0 [20497,28760],q 10 [12297],q 1 [12297,28760],q 0 [4096,20497,28760],q 8 [20497,28683],q 1 [28683],q 5 [20556],q 3 [20556],q 0 [4096,20556],q 0 [4097,20976],q 11 [4097],q 4 [16397,20976],q 9 [16397,20976],q 1 [20976],q 4 [4097],q 0 [20496,24585],q 2 [24585],q 5 [20491,16837],q 8 [20491,16837],q 1 [4097,20491],q 2 [4097,16837],q 0 [4097],q 10 [4097],q 3 [20480,20481],q 5 [8197],q 2 [8197],q 4 [20480,20481],q 8 [20480,20481],q 9 [20480,20481],q 0 [20480,20481],q 1 [20480,20481],q 6 [8197],q 5 [20488,16533],q 3 [20488,16533],q 8 [20488,16533],q 0 [20488,16533],q 1 [20488],q 3 [16399],q 7 [16399],q 16 [16399],q 5 [20490,86803],q 2 [4097],q 7 [20490],q 8 [20490],q 0 [4097,20490,86803],q 5 [8197,37343],q 7 [8197],q 4 [16387,37343],q 3 [16387,37343],q 0 [8197,16387,37343],q 1 [8197],q 16 [20489],q 3 [20489],q 7 [20489],q 2 [24589],q 5 [16394,21179],q 3 [16394,21179],q 8 [16394,21179],q 0 [16394,21179],q 1 [21179],q 5 [16393,20672],q 8 [16393,20672],q 1 [4097,20672],q 2 [4097,16393],q 7 [16395],q 16 [16395],q 3 [8194],q 4 [16390,353101],q 7 [16390,353101],q 0 [8194,16390,353101],q 1 [8194,353101],q 8 [8194,353101],q 5 [16390],q 21 [8194],q 6 [8194,353101],q 5 [12298,21207],q 0 [4097,21207],q 1 [4097],q 5 [16393],q 3 [16393],q 0 [4096,16393],q 11 [16393],q 5 [12298,17109],q 0 [4097,17109],q 1 [12298],q 0 [20491,16837],q 1 [20491],q 10 [4096],q 2 [16837],q 9 [4096],q 0 [20497,28683],q 20 [20497],q 5 [8196],q 2 [8196],q 20 [8196],q 0 [8196,20497],q 10 [12290],q 4 [12290],q 8 [20497,28687],q 6 [8410],q 4 [4096],q 5 [16394],q 3 [16394],q 0 [4096,16394,74425],q 1 [4096,74425],q 6 [4096,74425],q 7 [12297,20496],q 9 [20496],q 1 [12297],q 0 [4097,20496],q 21 [4097],q 18 [20499],q 5 [12374],q 4 [4097,12374],q 9 [4097,12374],q 9 [20499],q 5 [20493,553044],q 0 [4097,553044],q 7 [20493],q 8 [20493],q 3 [20489,155732],q 5 [20489,155732],q 8 [20489],q 0 [4097,20489,155732],q 18 [20498],q 9 [20498],q 1 [4096],q 2 [8194],q 4 [20486,353113],q 7 [20486,353113],q 0 [8194,20486,353113],q 5 [20497,28680],q 3 [12289],q 4 [12289],q 0 [8196,16433],q 5 [8196,16433],q 8 [16433],q 7 [8196,16433],q 9 [16433],q 10 [12289],q 21 [12289],q 5 [16399,86483],q 0 [4097,86483],q 8 [16399],q 4 [12293,20592],q 3 [20592],q 5 [12293,20592],q 7 [12293,20592],q 0 [8194,20592],q 11 [8194],q 1 [12293,20592],q 15 [12293,20592],q 8 [8194],q 10 [8194],q 1 [8194],q 2 [8198,684373],q 4 [20480,684373],q 5 [8198],q 8 [20480,684373],q 0 [8198,20480,684373],q 6 [8198,684373],q 21 [8198],q 3 [20564,13165],q 0 [4097,20564],q 5 [20564,13165],q 7 [13165],q 8 [13165],q 6 [4097,13165],q 4 [20496,24578],q 2 [24578],q 6 [8196],q 16 [20488],q 3 [20488],q 7 [20488],q 4 [16390,21327],q 8 [21327],q 5 [16390,21327],q 7 [16390,21327],q 0 [16390,21327],q 15 [16390,21327],q 3 [16392,16393],q 5 [16392,16393],q 2 [16392,16393],q 13 [4096],q 8 [20496],q 8 [8194,12633],q 0 [4096,20497],q 2 [4096],q 9 [4097,12290],q 4 [4097,12290],q 0 [4097,20498],q 9 [12290,20498],q 5 [20491],q 3 [20491],q 2 [4096,74181],q 0 [4096,20491,74181],q 0 [4096,20491],q 10 [20491],q 3 [20482,20483],q 4 [20482,20483],q 10 [8197],q 8 [20499],q 20 [20499],q 0 [8197,20499],q 5 [20490],q 3 [20490],q 0 [4096,20490,74513],q 5 [20488,20489],q 3 [20482],q 8 [20482],q 17 [20482],q 3 [16397],q 4 [16397],q 0 [8196,553011],q 3 [20493],q 4 [12294,20863],q 8 [20863],q 5 [12294,20863],q 7 [12294,20863],q 0 [8194,20863],q 15 [12294,20863],q 3 [20496,24662],q 5 [20496,24662],q 16 [16393],q 7 [16393],q 0 [4096,4097,16393],q 0 [8196,20531],q 7 [8196,20531],q 8 [20531],q 9 [20531],q 0 [4097,20497],q 9 [12290,20497],q 5 [16395],q 3 [12665],q 0 [4098,16395],q 2 [4098,12665],q 2 [8196,16433],q 21 [12290],q 0 [4096,16395,74409],q 3 [20488,86167],q 5 [20488,86167],q 0 [4097,20488,86167],q 6 [4097,86167],q 8 [20488],q 3 [16393,196692],q 8 [16393],q 1 [4097,196692],q 0 [4097,16393,196692],q 5 [12297,20568],q 4 [20568],q 0 [4096,20568],q 11 [4096],q 1 [12297,20568],q 0 [4096,21207],q 3 [13197],q 4 [13197],q 5 [8196,20531],q 11 [12290],q 1 [8196,20531],q 1 [8198],q 20 [8198],q 20 [20498],q 0 [8198,20498],q 21 [12297],q 7 [12297,20498],q 16 [16392],q 3 [16392],q 7 [16392],q 5 [8197,37071],q 4 [20483,37071],q 3 [20483,37071],q 0 [8197,20483,37071],q 6 [8197,37071],q 16 [12297],q 0 [8197,16426],q 11 [8197],q 21 [8197],q 5 [20487],q 7 [20487],q 0 [20487],q 9 [12289],q 0 [8194,20487],q 8 [8194,12289],q 3 [8194,12289],q 3 [16386],q 8 [16386],q 14 [8196,8197],q 17 [16386],q 4 [20481],q 0 [8196,20481,540723],q 5 [20489],q 5 [16389],q 11 [16389],q 0 [4097,20499],q 9 [12290,20499],q 0 [4096,16395],q 6 [8198],q 10 [8198],q 0 [8198,20499],q 2 [8196,684081],q 4 [20480],q 0 [8196,20480,684081],q 6 [8196,684081],q 3 [20497,28672],q 5 [12293],q 8 [20497,28672],q 0 [20497,28672],q 1 [28672],q 6 [12293],q 5 [20493],q 5 [16399],q 3 [16470,13225],q 0 [4097,16470],q 5 [16470,13225],q 7 [13225],q 8 [13225],q 1 [4097,13225],q 6 [4097,13225],q 4 [16399,352721],q 26 [],q 21 [4096],q 8 [20498],q 0 [4096,20498],q 4 [12294,16765],q 8 [16765],q 5 [12294,16765],q 7 [12294,16765],q 0 [8194,16765],q 1 [12294],q 15 [12294,16765],q 5 [12293,115167],q 0 [16387,115167],q 1 [12293],q 8 [16387],q 16 [20498],q 4 [20484,16789],q 8 [16789],q 5 [20484,16789],q 7 [20484,16789],q 0 [20484,16789],q 1 [20484],q 15 [20484,16789],q 9 [20484,16789],q 0 [4096,17109],q 3 [20480,12957],q 8 [20480,12957],q 6 [12293,12957],q 3 [16394,86715],q 5 [16394,86715],q 7 [16394],q 8 [16394],q 0 [4097,16394,86715],q 9 [4097,86715],q 6 [4097,86715],q 8 [16397,20976],q 0 [8194,20976],q 15 [16397,20976],q 16 [16397],q 7 [16397],q 0 [4096,20558],q 5 [20558],q 14 [8197],q 3 [16384,16385],q 4 [16384,16385],q 8 [16384,16385],q 9 [16384,16385],q 0 [16384,16385],q 0 [8197,20497],q 8 [20496,24589],q 0 [4096,20976],q 3 [16385],q 1 [8196,532531],q 4 [16385],q 0 [8196,16385,532531],q 8 [12361],q 0 [4096,20496],q 20 [20496],q 0 [8196,20496],q 3 [20495],q 7 [20495],q 16 [20495],q 4 [20487,16737],q 3 [16737],q 5 [20487,16737],q 7 [20487,16737],q 0 [20487,16737],q 15 [20487,16737],q 7 [8198,16725],q 0 [8198,16725],q 4 [16725],q 11 [12289],q 16 [20499],q 5 [20495],q 0 [4096,20496,24649],q 5 [16389,675975],q 7 [16389],q 1 [10,675975],q 4 [16389],q 0 [10,16389,675975],q 21 [10],q 6 [10,675975],q 2 [8198],q 7 [8198],q 8 [20482,20483],q 0 [20482,20483],q 5 [20495,16933],q 9 [20495,16933],q 0 [4096,16933],q 1 [20495],q 2 [16933],q 5 [1011727],q 3 [1011727],q 0 [4096,16457],q 8 [12289,20496],q 0 [8194,20499],q 8 [12289,20499],q 0 [4096,20499],q 16 [20496],q 15 [12293,20499],q 10 [8196],q 0 [8196,20499],q 3 [16384],q 8 [16384,987477],q 0 [8198,16384,987477],q 4 [16384,987477],q 4 [16384],q 0 [8196,16384,987185],q 0 [16393,20672],q 0 [4097,90196],q 3 [20495,86567],q 0 [4097,86567],q 5 [20495,86567],q 8 [20495],q 0 [8197,20496],q 15 [20497,28687],q 0 [4097,20496,24585],q 2 [4097,24585],q 8 [20496,24578],q 9 [20496,24578],q 0 [20496,24578],q 4 [20497,28676],q 5 [20497,28676],q 7 [20497,28676],q 0 [20497,28676],q 15 [20497,28676],q 5 [16460],q 3 [16460],q 0 [4096,16460],q 15 [20496,24589],q 4 [20497,28672],q 9 [20497,28672],q 0 [4096,74193],q 0 [16392,41651],q 5 [20485],q 0 [20484,20485],q 4 [20484,20485],q 5 [20484,20485],q 9 [20484,20485],q 0 [4098],q 0 [4098,20491],q 18 [20491],q 4 [4098,12665],q 0 [16389],q 7 [12297,20497],q 4 [16389,21140],q 3 [21140],q 5 [16389,21140],q 7 [16389,21140],q 0 [16389,21140],q 15 [16389,21140],q 3 [8194,12633],q 4 [12633],q 0 [8194,20498],q 19 [20498],q 19 [20499],q 5 [1048591],q 0 [8194,16729],q 1 [8194,1048591],q 6 [8194,1048591],q 5 [20615,13321],q 7 [13321],q 4 [13321],q 0 [10,20615],q 2 [12293],q 5 [20615],q 8 [10,20615],q 4 [12293],q 5 [16397,508039],q 15 [20498,20499],q 5 [16391],q 0 [16391],q 0 [8194,16391],q 12 [8194,12289],q 4 [16391],q 2 [10],q 4 [20485],q 0 [10,20485,417927],q 0 [10,553095],q 0 [8196,16426],q 4 [12289,16426],q 11 [8196],q 5 [16426],q 2 [12289,16426],q 9 [12290,20496],q 0 [20485],q 0 [16388,16389],q 4 [16388,16389],q 5 [16388,16389],q 9 [16388,16389],q 2 [16388,16389],q 12 [12290],q 9 [20482,20483],q 1 [20482,20483],q 0 [4097,16933],q 8 [12289,20497],q 8 [12289,20498],q 0 [4097,20568],q 9 [20497,28676],q 11 [8198],q 0 [8198,16426],q 15 [12293,20496],q 0 [8194,20496],q 9 [12293],q 15 [12293,20497],q 0 [8194,20497],q 2 [12294],q 7 [12294],q 6 [12294],q 21 [12293],q 15 [12293,20498],q 0 [8198,20496],q 3 [16392,86707],q 5 [16392,86707],q 0 [4097,16392,86707],q 8 [16392],q 0 [8198,20497],q 1 [4098],q 3 [16395,696697],q 7 [16395,696697],q 4 [4098,696697],q 9 [4098],q 0 [4098,16395,696697],q 8 [16395],q 7 [20484,20485],q 15 [20484,20485],q 4 [20495,352805],q 9 [20495],q 8 [20495,16933],q 0 [8194,16933],q 15 [20495,16933],q 15 [20496],q 0 [8194,20496,24921],q 2 [8194,24921],q 6 [12297],q 2 [24581],q 15 [20496,24581],q 9 [20496,24581],q 0 [8196,20498],q 15 [20496,20497],q 15 [20497],q 0 [10,20497,28807],q 3 [16397,507988],q 0 [4097,507988],q 5 [16397,507988],q 8 [16397],q 0 [4097,20497,28683],q 15 [20497,28679],q 0 [8194,20497,28679],q 9 [20497,28679],q 16 [20497],q 14 [12293],q 3 [12289,675880],q 0 [16389,675880],q 1 [12289,21140],q 9 [16389,21140],q 7 [20491],q 16 [20491],q 3 [16386,13217],q 8 [16386,13217],q 1 [12293,13217],q 6 [12293,13217],q 5 [20497,28756],q 1 [4097,28756],q 5 [16394,41659],q 1 [12289,41659],q 6 [12289,41659],q 9 [21179],q 1 [12289,21179],q 2 [12289,16394],q 3 [20491,463225],q 7 [20491,463225],q 8 [20491],q 2 [4098,463225],q 0 [4098,20491,463225],q 0 [20488,41111],q 5 [20488,41111],q 6 [12289,41111],q 0 [4096,16462],q 5 [16462],q 5 [20490,41747],q 0 [20490,41747],q 5 [12293,114895],q 0 [20483,114895],q 3 [20483,114895],q 8 [20483],q 2 [12289,16837],q 1 [12289,28683],q 1 [12289,28712],q 2 [16789],q 5 [12294],q 5 [1130511],q 6 [1130511],q 16 [20493],q 1 [12289,20484],q 2 [12289,16789],q 7 [16388,16389],q 15 [16388,16389],q 12 [8194],q 6 [216],q 5 [21000,536589],q 7 [536589],q 0 [16385,21000],q 6 [536589],q 1 [21179,716813],q 6 [716813],q 7 [12297,20499],q 6 [466959],q 6 [237568],q 1 [237569],q 0 [8197,20498],q 1 [237570],q 6 [237570],q 6 [237579],q 0 [16933],q 0 [20976],q 6 [12741],q 4 [20495],q 0 [549],q 0 [20480],q 6 [12957],q 14 [],q 0 [20481],q 0 [20491],q 9 [12294],q 4 [12294],q 0 [20482],q 9 [20482],q 4 [20482],q 0 [20484],q 4 [20484],q 5 [20484],q 9 [20484],q 0 [16395],q 2 [16395],q 13 [12290],q 9 [16389],q 2 [16389],q 0 [21207],q 6 [12298],q 5 [20520],q 0 [20520],q 8 [20480],q 13 [12289],q 0 [16386],q 0 [16385],q 1 [532495],q 6 [532495],q 0 [16384],q 8 [16384],q 15 [20499],q 15 [20495],q 4 [20493],q 15 [20493],q 9 [20493],q 5 [16397],q 9 [16397],q 0 [507915],q 2 [16397],q 9 [20485],q 15 [16399],q 4 [16399],q 9 [16399],q 0 [551],q 1 [28687],q 0 [20979],q 0 [507904],q 5 [21000],q 1 [21000],q 2 [16385],q 3 [20564],q 15 [20498],q 5 [16470],q 3 [16470],q 3 [12374],q 0 [8196],q 0 [16388],q 4 [16388],q 5 [16388],q 9 [16388],q 2 [16388],q 0 [8197],q 9 [16384],q 2 [16386],q 14 [8198],q 9 [16386],q 0 [8198,16386],q 5 [20488],q 0 [4097,16393],q 4 [16386],q 14 [12294],q 0 [8197,16386],q 2 [16391],q 15 [16391],q 9 [16391],q 0 [16485],q 15 [16389],q 0 [8194,16389],q 1 [20480],q 2 [17053],q 0 [20480,17053],q 1 [20487],q 15 [20487],q 9 [20487],q 0 [16426],q 0 [20489],q 0 [4096,20489],q 14 [8196],q 5 [16392],q 2 [16392],q 1 [20493],q 13 [4097],q 15 [12293],q 9 [20480],q 0 [8197,20480],q 0 [16393],q 2 [16393],q 4 [16729],q 7 [16388],q 15 [16388],q 1 [13217],q 6 [13217],q 7 [20484],q 15 [20484],q 0 [8194,20484],q 15 [20485],q 15 [16397],q 13 []]
def B_17_2 : BT (List (List Nat)) := BT.empty
lemma B_17_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 2 xs.toFinset) B_17_2 := .empty
def U_17_3 : List Nat := []
def P_17_3 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 U_17_3
def N_17_3 : List NodeSpec := [([8,0,11,13],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_3 : checkNodesBT W_17 g_17 F_17 P_17_3 A_17 B_17_2 3 N_17_3 = true := by decide +kernel
def B_17_3 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_3
set_option maxRecDepth 500000 in
lemma B_17_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 3 xs.toFinset) B_17_3 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_2_ok C_17_3
def U_17_4 : List Nat := [0]
def P_17_4 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 U_17_4
def N_17_4 : List NodeSpec := [([8,0,9,10,13],[],[0]),([14,15,0,11,13],[],[0]),([0,11,16,4,5],[],[]),([17,0,13,4,5],[],[]),([0,11,13,6,7],[],[0]),([20,23,2,4,5],[],[]),([8,18,23,2,3],[0],[4]),([0,13,4,24,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_4 : checkNodesBT W_17 g_17 F_17 P_17_4 A_17 B_17_3 4 N_17_4 = true := by decide +kernel
def B_17_4 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_4
set_option maxRecDepth 500000 in
lemma B_17_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 4 xs.toFinset) B_17_4 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_3_ok C_17_4
def U_17_5 : List Nat := (r 1 25)
def P_17_5 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 U_17_5
def N_17_5 : List NodeSpec := [([8,0,1,23,2,3],[1,2],[0]),([8,25,26,0,1,2],[3],[]),([8,27,0,1,2,3],[],[]),([8,18,21,2,3,22],[3,4,5],[0,4]),([17,0,12,3,4,5],[6],[0]),([32,0,1,3,4,5],[7],[]),([14,15,18,23,2,3],[8],[0,4]),([18,23,2,3,6,7],[9],[0,4]),([8,0,34,1,2,3],[],[]),([8,0,1,2,19,22],[10,11,12],[4]),([0,11,3,4,35,5],[13,14],[]),([36,0,9,13,4,5],[14],[]),([0,9,10,13,6,7],[],[0]),([40,39,21,3,4],[14,15,16],[]),([14,15,0,9,10,13],[],[0]),([0,11,13,6,4,5],[14,17,18],[0,3]),([0,11,13,4,5,7],[14,17,18],[0]),([8,25,0,12,9,3],[19,20],[]),([14,0,11,13,4,5],[],[0]),([15,0,11,13,4,5],[],[0]),([8,0,9,3,13],[11,19,21,22],[0]),([18,2,3,4,41,5],[23],[4]),([20,21,2,22,4,5],[],[0]),([0,9,42,13,4,5],[14],[]),([0,9,10,16,4,5],[],[0]),([46,1,2,3,4,5],[24],[]),([47,0,11,3,4,5],[14,25],[]),([50,21,2,3,4,5],[],[]),([0,9,3,53,4,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_5 : checkNodesBT W_17 g_17 F_17 P_17_5 A_17 B_17_4 5 N_17_5 = true := by decide +kernel
def B_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_5
set_option maxRecDepth 500000 in
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_4_ok C_17_5
def U_17_6 : List Nat := ([1,3,5,10,11,12,14,15,17,18,20,21]++r 26 169)
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 U_17_6
def N_17_6 : List NodeSpec := [([57,1,2,4,5],[14,26,27],[]),([61,0,1,4,5],[14,28,29],[]),([39,63,1,3,4],[15,30,31,32],[]),([39,0,65,3,4],[30,32,33,34],[]),([66,67,1,3,4],([30]++r 35 5),[]),([0,1,2,70,68,4,5],[40,41],[]),([72,0,1,2,29,4,5],[42,43],[]),([74,1,2,3,68,4,5],[44,45,46],[]),([36,0,1,2,76,4,5],[47,48,49],[]),([36,78,0,1,3,4,5],[50],[]),([36,0,80,2,3,4,5],[14,51,52],[]),([82,83,1,2,3,4,5],[38,53],[1]),([84,39,0,1,3,4],([14,15,34,36]++r 54 4),[]),([8,25,85,0,1,2,3],[10,11,20,58,59],[]),([8,86,0,1,2,3,28],([10,11,12]++r 60 4),[5]),([14,15,0,34,1,2,3],[],[0]),([0,34,1,2,3,6,7],[],[0]),([0,87,1,3,68,4,5],[41],[]),([8,86,1,2,3,10],[1,3,10,12,64,65],[]),([86,1,2,3,90,4,5],[],[]),([91,0,1,92,3,4,5],[66],[5]),([93,94,1,2,3,4,5],[],[]),([96,39,0,1,3,4],[15,30,36,54,56,67,68,69],[]),([8,0,1,2,3,97],[10,11,60,63,70],[]),([14,15,0,1,23,2,3],[71,72],[0]),u6 [17] [43,73],u6 [41] [74,75],([8,98,0,1,2,3],[1,3,10,11,12,60,63,76,77],[4]),([8,25,0,12,1,2,3],[10,11,58,78],[0]),([8,18,0,1,2,3,22],[1,3,10,11,12,60,63,79],[0,4]),([99,43,0,1,3,4,5],[80],[]),e6 [100] [40,47,81],([14,15,27,0,1,2,3],[],[0]),([0,1,2,19,22,6,7],[82,83,84],[0,4]),([36,0,1,2,13,4,5],[32,47,49,85],[0]),([20,0,1,2,22,4,5],[85,86,87],[0]),([104,0,105,3,4],([14]++r 88 5),[]),([14,15,25,26,0,1,2],[93],[0]),([0,9,3,13,4,107,5],[32,94],[]),([8,25,0,1,2,9,3],[10,58,60,95],[0]),([14,15,0,1,2,19,22],[96,97,98],[0,4]),([0,9,3,108,13,4,5],[99],[]),([0,9,3,16,13,4,5],[47,100,101],[]),([0,9,3,16,4,5],(r 101 5),[0]),([15,0,9,10,13,4,5],[21],[0]),([14,18,23,2,3,4,5],[106],[0,4]),([69,109,1,2,3,4,5],[107],[3]),([0,9,3,13,6,7],[83,99,105,108,109],[0]),([20,21,2,3,19,4,5],[47,110,111],[]),([110,0,9,3,4,5],[14,112,113,114],[]),([20,21,2,3,4,5],([111]++r 115 4),[0]),([111,15,21,2,3,19,5],[119,120],[]),([18,23,2,3,6,4,5],([44]++r 121 4),[0,4]),([0,11,13,4,5],[14,17,18,125,126],[0]),([112,21,3,19,4,5],([119]++r 127 5),[]),a6 [115] [] [4],([0,9,10,13,4,5,7],[14,17,126,132],[0]),([8,0,1,21,2,3,22],[63,77,133],[0]),([0,117,13,4,5],[14,21,99],[]),([118,21,2,3,19,4,5],[47,110],[]),([120,0,9,3,4,5],[17,21,99,134,135],[]),([0,9,3,13,4,52,5],[14,21,100],[0]),([36,121,0,1,2,4,5],[45,48,49],[]),([0,9,3,13,4,123,5],[32],[]),([14,15,18,21,2,3,22],[93,136,137],[0,4]),([14,0,9,10,13,4,5],[99],[0]),([0,9,3,4,126,5],(r 138 4),[]),([127,0,1,3,29,4,5],[142],[]),([0,1,2,128,22,4,5],[85,143,144],[4]),([21,3,19,4,129,5],([117,128]++r 145 4),[]),([39,18,21,3,4],[14,15,36,149,150,151],[0]),([0,9,3,13,4,131,5],[14,21,99,100],[3]),([0,9,3,133,4,5],[17,21,152,153],[]),([25,26,0,1,2,6,7],[154],[0]),([0,9,3,4,134,5],[14,155,156,157],[]),([14,15,0,9,3,13],[21,97,99,158,159],[0]),([0,136,13,4,5],[14,21],[]),([139,0,9,3,4,5],(r 160 4),[]),([0,1,2,19,68,4,5],[40,41,47],[4]),([47,0,9,3,10,4,5],[14,164,165,166],[0]),([18,21,2,3,68,4,5],[43,44,167,168],[4]),([0,1,23,2,3,6,7],[169,170],[0]),([40,39,0,1,3,4],[14,15,30,54,56,171],[0]),([111,21,2,3,19,6,5],[14],[]),u6 [50] [],([8,0,1,2,3,19],[10,11,12,63,79,172],[0,4]),([140,1,2,3,71,4,5],[38,173],[5]),([18,23,2,3,4,5,7],[44,121,123,124,174],[0,4]),([27,0,1,2,3,6,7],[],[0]),e6 [141] [47,85,175],([143,21,2,3,4,5],[176,177],[]),([0,9,3,145,4,5],[178,179],[]),([0,9,3,10,4,35,5],([14,164]++r 180 4),[0]),e6 [146] [],([36,0,12,9,3,4,5],[14,45,184,185],[0]),([0,9,10,13,6,4,5],[14,17,99,126,132],[0,3]),([14,15,25,0,12,9,3],[158,186],[0]),([15,18,23,2,3,4,5],[187],[0,4]),([18,21,2,3,22,6,7],[154,188,189],[0,4]),([8,25,1,21,2,3],[3,10,11,77,190,191],[]),([25,0,12,9,3,6,7],[108,192],[0]),([25,0,9,3,4,35,5],[180,193],[]),([25,47,0,9,3,4,5],[165,193],[]),([8,18,21,2,3],[3,5,11,150,194],[0,4]),e6 [147] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6 = true := by decide +kernel
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_5_ok C_17_6
def U_17_7 : List Nat := ([1,3,10,11,12,14,15,17,21,30,32,34,36,38]++r 40 6++[47,48,49,52,54,60,62,63,64,70,71,76,77,79]++r 81 5++r 87 4++[93]++r 96 5++[105,110,111,117,119,120,121,123,124,126,127,128,130,132,137,143,144,145,147,150,154,165,166,169,172,175]++r 180 4++[185,186,189,190,192]++r 195 397)
def P_17_7 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 U_17_7
def N_17_7 : List NodeSpec := [([54,0,1,149,4,5],[195,196,197],[]),([150,151,1,2,4,5],[14,198,199,200],[3]),([0,1,153,4,58,5],[196,198,201],[]),([154,39,0,1,3,4],[14,30,36,38,54,202],[]),([39,0,67,1,3,4],[14,15,30,32,34,36,38,54,203],[0]),([66,39,0,1,3,4],[14,15,30,32,34,36,38,54,204,205,206],[0]),([8,25,0,1,2,3],[1,10,11,12,60,63,207,208],[0,1]),([25,39,0,1,3,4],[14,15,30,32,34,54,208],[2]),a6 [42,155] [45,47,209,210,211] [2,5],u6 [140,29] ([40,42,43]++r 212 5),([8,0,1,2,3,10],[1,3,10,11,12,60,63,217],[0,1,2,3,4]),a6 [36,75] [45,47,218,219,220] [0,1],u6 [91,36] [52,85,221,222],a6 [36,77] [45,47,219,220,223] [0,1,2],u6 [82,81] ([40,43]++r 224 4),e6 [157,156] [38,52,85,228],e6 [156,158] [38,52,229],([39,64,0,1,3,4],[14,15,30,32,34,36,38,54,230],[0,2,3]),([86,103,0,2,3,4],([14]++r 231 6),[]),([14,15,25,85,0,1,2,3],[96,97,186,237,238],[0]),([25,85,0,1,2,3,6,7],[82,83,192,239,240],[0]),([14,15,86,0,1,2,3,28],([96,97,98]++r 241 4),[0,5]),e6 [86,29] [40,42,52,233,245,246,247],a6 [159] [45,47,48,52,81,248,249,250] [1],e6 [36,85] [47,49,52,185,219,251,252,253],u6 [15,34] [207,254],u6 [34,6] [14,81,205,229,255,256,257],([86,0,1,2,3,28,6,7],([82,83,84]++r 258 4),[0,5]),([86,1,2,3,42,4,5],([85,211]++r 262 4),[5]),([86,160,2,3,10,4,5],(r 266 5),[]),([152,1,2,4,161,5],[14,198,199,271],[3]),([86,1,2,3,10,6,7],[82,84,154,169,265,272,273],[0]),([86,1,2,3,10,4,89,5],[14,40,64,233,267,274],[0]),([86,1,2,3,162,4,5],[64,85,267,275,276,277],[]),([86,164,1,2,3,4,5],[64,85,267,273,278,279,280],[]),([39,0,1,3,10,4],[14,30,32,36,54,217],[0]),([86,1,2,3,10,4,166,5],[14,40,64,233,267,273,274],[1]),([0,168,9,3,4,5],([14,38]++r 281 6),[]),([0,1,3,169,4,129,5],([81]++r 287 5),[]),([14,15,25,1,21,2,3],[93,96,97,190,292,293,294],[0]),([15,25,26,0,1,2,4,5],[295],[0]),([171,21,2,3,4,5],([14,123,150]++r 296 4),[]),([15,0,1,2,19,22,4,5],[172,300,301,302],[0,4]),([14,15,86,1,2,3,10],[64,71,93,96,98,273,303],[0]),([18,21,172,3,48,5],([14,150,296]++r 304 4),[]),a6 [173] ([52,85]++r 308 6) [4],([14,25,0,12,9,3,4,5],[182,283,314,315,316],[0]),([98,0,1,2,3,6,7],(r 81 4++[154,169,258,261,317,318,319]),[0,4]),([36,86,1,2,3,4,5],[49,85,219,273,320,321],[5]),([18,21,2,3,4,175,5],([14,150]++r 322 4),[]),([176,18,2,3,4,5],[14,150,296,326,327,328],[]),([177,0,12,9,3,4,5],([45,47,182,183]++r 329 8),[3]),u6 [14,23] [81,337,338,339],([47,0,9,3,4,5],[14,32,89,165,166],[0]),a6 [178,19] [340] [4],u6 [21,68] [44,341,342],([25,0,1,2,9,3,6,7],[82,239,258,343],[0]),a6 [128,19] [47,144,175,344] [4],u6 [14,34] [81,337],([111,21,2,3,19,4,5],([14,47,117,119,120,128]++r 345 4),[0,4]),([18,21,2,3,22,6,4,5],([44,123,219,296,327]++r 349 5),[0,4]),([18,21,2,3,179,4,5],([43,47,123,296]++r 354 7),[4]),u6 [36,9] [14,45,49,219,361],([18,21,2,3,4,180,5],([14,150]++r 362 4),[]),([18,21,2,3,4,182,5],([47,327,357,359]++r 366 4),[]),([0,1,2,3,19,6,7],[82,83,84,261,340,370,371],[0,4]),u6 [27,7] ([14,175]++r 372 5),([18,21,2,3,22,4,5,7],[44,123,211,327,350,351,359,377,378],[0,4]),u6 [20] [40,47,52,81,85,87,111,172,340,379],([0,9,3,13,4,5,7],[14,17,21,38,99,105,380,381,382],[0,3]),([183,21,2,3,4,5],([14,327]++r 383 4),[]),([170,21,2,3,19,4,5],[14,117,119,120,128,387,388,389],[4]),([184,0,1,185,4,5],[14,197,390,391,392],[4]),u6 [134] ([14,43,48,175]++r 393 4),([18,21,37,3,4,38],[14,150,327,359,397,398],[0]),([0,9,3,186,13,4,5],[14,17,21,38,99,105,132,399],[]),([116,0,9,13,4,5],[14,17,21,47,99,105,400],[0]),([0,9,3,106,13,4,5],[14,17,21,38,99,105,132,401],[0,3]),([39,0,1,3,187,4],[14,30,32,36,54],[]),a6 [188,42] [52,85,402,403] [5],([113,21,2,3,19,4,5],[14,110,117,119,128,404,405],[4]),([189,12,9,3,4,5],[38,182,283,406,407,408],[]),a6 [19,191] [232,254,409] [4],([192,18,2,3,4,5],[44,150,296,410,411],[]),u6 [14,27] [81,337],([0,9,3,13,6,4,5],[14,17,21,38,99,105,412,413,414],[0,3]),([18,21,2,3,4,138,5],([123,150,327,360]++r 415 4),[4]),([54,193,1,2,4,5],[195,196,390],[]),([15,18,21,2,3,22,4,5],[150,295,360,419,420],[0,4]),([14,0,1,2,19,22,4,5],[340,421,422,423],[0,4]),([15,25,0,12,9,3,4,5],[283,330,408,424,425],[0]),a6 [194] [172,426,427,428] [4],([18,21,2,3,4,49,5],([14,43,110,150,296,357,359]++r 429 4),[4]),([25,26,0,1,2,6,4,5],([14,219]++r 433 4),[0]),([111,0,1,2,3,19,6,5],[14,81],[0]),([0,9,3,13,4,5,132],[17,21,38,437,438],[0]),([195,21,2,3,19,4,5],[14,119,120,128,347,439,440],[]),([0,9,13,4,5,135],[14,17,21,441],[0]),([14,15,25,0,1,2,9,3],[96,237,241,442],[0]),([18,197,2,3,4,5],[14,150,359,443],[]),u6 [139] [40,43,47,48,85,417,444,445,446],([18,21,2,3,198,4,5],([47,296,327,359,360]++r 447 4),[]),u6 [20,19] [47,81,111,344],([0,9,10,13,4,5],[14,17,99,105,126,132],[0]),u6 [10,35] ([14,32,40,43,181,220,414]++r 451 5),([15,0,9,3,13,4,5],[14,17,21,100,132,301,424,456],[0,3]),([8,0,1,21,2,3],[1,3,10,11,12,60,63,77,457],[0,2,4]),([199,51,12,9,3,4],[38,333,335,408,458,459],[3]),u6 [118,19] [47,207,344],e6 [97,166] ([14,40,70,274]++r 460 4),([14,15,18,21,2,3],[93,97,137,150,296,464],[0,4]),([18,21,2,3,4,114,5],[14,110,150,248,360,465,466],[4]),([0,1,2,19,22,4,5,7],([14,350,382,428]++r 467 6),[0,4]),([18,200,2,3,4,5],[44,150,359,410,473,474,475],[]),([8,86,0,1,2,3],[1,3,10,11,12,60,62,63,207,235,476],[0,2]),u6 [34,7] [14,175,205,229,255,256,257],a6 [19,49] [14,52,172,340,344,462,477] [0,4],([18,0,1,2,3,22,6,7],[82,83,84,154,169,258,261,371],[0,4]),u6 [145] [43,81,175,254,478,479,480],u6 [120] ([40,43,47,85]++r 481 6),u6 [110] [14,43,47,48,81,85,487,488,489],([14,15,0,1,2,3,19],[96,97,98,172,244,340,490],[0,4]),a6 [19,114] [14,52,172,254,344,491] [0,4],([25,0,12,1,2,3,6,7],[82,83,239,492],[0]),([0,1,2,19,22,6,4,5],[14,340,350,414,428,452,468,469,470,472,493],[0,4]),([0,9,3,13,4,130,5],[17,38,105,494,495],[0]),([39,18,0,1,3,4],[14,15,30,32,496,497],[0]),([18,21,201,3,4,5],[14,150,498,499,500],[]),([0,1,3,19,4,129,5],[147,172,287,340,428,501,502],[0]),([54,18,21,2,4,5],[14,150,503,504,505],[]),e6 [162,202] [14,52,267,506],a6 [19,203] [232,462] [4],([204,0,9,3,4,5],[14,32,335,507,508,509],[]),([18,21,2,3,4,125,5],([43,47,123,150,296,309,327,357]++r 510 4),[4]),([14,25,26,0,1,2,4,5],[514],[0]),([18,205,2,3,4,5],[14,150,359,515,516],[4]),([0,9,3,4,35,5],[14,32,89,180,181,182],[0]),([18,21,3,4,129,5],[123,145,147,150,296,517,518,519],[0]),e6 [97,89] [14,40,70,274,460,463],u6 [27,6] ([14,81]++r 372 5),([18,21,2,4,58,5],[14,150,296,520,521],[]),([112,0,1,3,19,4,5],[130,172,370,428,522,523,524],[0]),([18,21,2,3,6,7],[83,154,189,296,359,525],[0,4]),([25,0,12,9,3,4,5,7],[14,283,314,333,380,526,527,528],[0]),([112,18,21,3,4,5],[123,127,130,150,529,530],[0]),u6 [15,27] [207,254],u6 [143] [40,47,52,81,175,462,531,532,533],a6 [128] [52,85,143,144,172,370,534,535] [0,4],u6 [47,10] [14,32,40,43,48,166,210,382,536,537],([14,15,18,0,1,2,3,22],[71,93,96,97,98,241,244,490],[0,4]),([25,0,12,9,3,6,4,5],[14,182,283,314,412,527,528,538],[0]),u6 [25,35] [40,451,539,540],u6 [93] [40,45,47,52,175,431,541,542],u6 [25,47] [40,536,539,543],([14,15,25,0,12,1,2,3],[96,97,237,544],[0]),([111,15,0,1,2,3,19,5],[81,172,254,370],[0]),([18,23,2,3,4,5],[44,121,123,124,351,545],[0,4]),([18,206,2,3,4,5],[14,150,296,546,547],[4]),([14,15,0,1,21,2,3,22],[244,293,548],[0]),([14,18,21,2,3,22,4,5],[123,296,353,514,549,550],[0,4]),([8,18,0,1,2,3],[1,10,11,12,63,79,207,497],[0,4]),([25,1,21,2,3,6,7],[82,83,154,292,317,551,552],[0]),([55,56,1,2,4,5],[14,195,553,554,555],[0]),a6 [36,12] [45,47,49,52,85,219,556] [0,3],([25,26,0,1,2,4,5,7],([14,211]++r 433 4),[0]),e6 [207,162] [14,52,85,557],u6 [23,6] ([44,81,121,351]++r 558 6),([14,15,98,0,1,2,3],[71,76,93,96,97,98,241,244,293,318],[0,4]),a6 [23,7] ([44,81,121,254,351,558,559]++r 562 4) [0,4],([208,1,2,4,58,5],[196,198,566,567],[]),u6 [15,23] [207,254,568,569],u6 [69,68] [40,43,570,571,572],([86,2,3,10,4,209,5],([267]++r 573 4),[]),([0,1,21,2,3,22,6,7],[261,317,577],[0]),([39,0,1,21,3,4],[14,34,36,205,457,578],[0]),([14,0,9,3,13,4,5],[14,17,99,105,132,315,422,579,580],[0]),([0,1,2,3,97,6,7],[82,83,258,261,461,581],[0]),([104,103,0,2,3,4],([14,88,90,205,231,232]++r 582 4),[0]),a6 [18,68] ([40,41,43,45,47,570]++r 586 4) [0,4],([112,0,1,3,169,4,5],[52,290,291,523,590,591],[]),([14,15,0,1,2,3,97],[70,96,97,241,244,461],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7 = true := by decide +kernel
def B_17_7 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_7
set_option maxRecDepth 500000 in
lemma B_17_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 7 xs.toFinset) B_17_7 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_6_ok C_17_7
def U_17_8 : List Nat := ([1,14,32,38,40,43,44,45,47,48,49,52,54,64,70,71,76]++r 81 5++[93,96,97,98,100,110,121,123,130,147,150,154,169,172,175,182,190,193]++r 195 5++[201,205,207,208,210,211,213,217,219,220,229,232,233,235,241,243,244,245,248,251,252]++r 254 5++[260,261]++r 263 7++[273,274,276,277,279,281,283]++r 287 7++[295,296,298,300,301,302,307,308,309]++r 316 4++[321,323,327,331,332,333]++r 335 4++[340,344,348,350,351,352]++r 356 5++[363]++r 368 6++[376,378,382,387,390,398]++r 405 4++[414,417,418]++r 420 4++[425,428,430,431]++r 433 4++[443,444,449,450,452,454,455,457,458]++r 460 4++[466,467,468,471,472,474,477,490,491,493,497,499,503,506,507,512,514,515,518,521,523]++r 526 4++[536,538,539,540,543,546,550,551,553,558,559,560,562,563,564,566,568,570]++r 573 4++[579,581,587,590]++r 592 627)
def P_17_8 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 U_17_8
def N_17_8_0 : List NodeSpec := [a6 [190,19] [14,172,175,337,340,344,370,592,593,594] [0,4],u6 [21,125] ([40,43,44,45,47,308,309,457,512,562]++r 595 6),([25,0,1,3,4,129,5],[52,147,205,208,287,288,436,540,601,602],[]),u6 [21,114] ([14,205,248,457,466]++r 603 6),([167,1,2,9,3,4,132],([38,44]++r 609 9),[3]),u6 [21,180] ([14,32,38,254,363,457,600,607]++r 618 5),([116,18,21,2,3,4,5],[43,110,123,150,296,327,359,623,624,625],[0,4]),u6 [197] ([14,38,48,81,443,457,600]++r 626 5),e6 [210] ([14,40,43,47,48,85,175,617]++r 631 6),([18,21,2,3,4,5,38],[14,110,123,150,327,359,637,638,639],[0,4]),([0,1,2,10,4,58,5],[14,40,81,198,199,220,337,640],[]),u6 [21,175] ([14,32,38,323,457,462,600,607]++r 641 5),u6 [21,49] ([14,205,430,431,457,600,607]++r 646 4),([170,18,21,2,3,4,5],[14,43,110,123,150,296,298,307,359,650,651],[0]),e6 [212] ([14,43,45,48,81,85,175,462]++r 652 9),u6 [21,198] [32,43,45,85,337,449,450,462,600,608,661,662,663],a6 [19,48] ([14,32,81,85,254,370,428]++r 664 4) [0,4],u6 [21,182] [32,43,45,85,254,337,368,369,596,600,627,668,669,670],a6 [18,114] ([14,52,254,344,466,491,497,603]++r 671 4) [0,4],([112,18,0,1,3,4,5],[130,497,523,675,676],[0]),u6 [25,12,7] ([14,382,436,467,527,528,540]++r 677 7),([184,54,0,1,2,4,5],[14,195,197,390,503,553,684,685],[0]),u6 [183] ([14,40,47,48,52,175,462]++r 686 6),([25,0,1,2,3,6,7],[82,83,84,169,175,258,261,540,543],[0,1]),a6 [21,22,6] ([44,350,351,468,559,562,600,663]++r 692 5) [0,4],a6 [15,98] ([43,76,207,254,295,301,302,568]++r 697 5) [0,4],u6 [47] [14,32,40,43,47,48,175,382,536],u6 [205] ([14,44,52,85,457,515,627]++r 702 4),e6 [213] ([14,44,48,52,457,562,627,639]++r 706 4),a6 [14,98] [43,81,318,319,337,338,422,423,435,514,698,699,700,710,711] [0,4],([18,0,1,3,4,129,5],[52,147,287,497,601,602,675,712],[0]),e6 [215] ([14,43,47,48,81,85,235,652]++r 713 4),([18,0,1,201,3,4,5],[14,497,499,686,717],[0]),e6 [10,216] ([32,43,254,337,454]++r 718 9),u6 [206] [14,44,52,85,175,457,546,624,663,727,728,729],([18,0,1,2,4,58,5],[14,198,201,497,521,566,640,712],[0]),e6 [86,217] ([45,52,233,337]++r 730 11),e6 [218] ([14,38,45,48,81,175,254,281]++r 741 7),e6 [220] ([14,81,254]++r 748 6),([189,12,1,2,3,4,5],[38,406,454,678,754,755,756],[0]),([18,21,37,2,3,4,5],[14,43,47,123,150,296,327,757,758,759],[0,4]),e6 [86,221] ([14,47,52,232,235,274,462]++r 760 6),([18,0,1,172,3,48,5],([14,52,497,675,712]++r 766 4),[0]),a6 [36] [45,47,49,52,81,85,217,219,220,321] [0,1,2,4],a6 [97,6] [14,70,274,414,460,461,463,493,693,770,771] [0,1],a6 [18,22,7] [14,211,245,350,351,382,467,468,471,559,564,570,587,675,686,694,772,773] [0,4],([14,25,1,21,2,3,4,5],([292,421,422,514,527,528,551]++r 774 4),[0]),e6 [222] ([14,32,40,47,48,175]++r 778 4),([54,18,0,1,2,4,5],[14,195,196,497,503],[0]),u6 [113,19] [14,32,40,47,52,340,344,370,428,462,778,779,782,783],([199,51,12,1,2,3,4],[38,373,679,756,784,785],[0,3]),u6 [15,25,9] ([208,300,610,617,682]++r 786 4),e6 [223] [14,40,47,48,85,497,686,773,790,791,792],([18,0,1,37,3,4,38],[14,398,497,686,793],[0]),([199,0,12,9,3,4,5],[14,38,45,100,283,333,408,794,795,796],[0,3]),e6 [224] [40,43,196,797,798],e6 [225] [32,40,43,47,175,799,800],e6 [86,226] ([47,52,232,337,462,652,713,739,740]++r 801 6),u6 [192] [44,52,81,85,175,457,663,807,808],([18,21,2,3,4,48,5],[14,110,123,150,296,327,360,665,809,810,811],[0,4]),e6 [227,10] ([32,40,43,48,220,337,462,718,719,725]++r 812 4),([25,1,21,2,3,4,5,7],[14,44,190,205,211,292,382,467,527,528,539,551,816,817],[0]),e6 [170,169] ([14,45,289,290,291,435]++r 818 4),e6 [25,216] [47,85,254,337,454,527,539,682,683,720,721,822,823],u6 [171] [14,40,47,48,52,298,497,675,712,818,824],a6 [97,7] [14,70,81,245,274,382,460,463,467,570,581,771] [0,1],a6 [98,7] [14,76,81,205,211,245,382,435,467,471,564,570,698,816] [0,4],e6 [228] ([14,38,40,47,48,81,85,254,600,696]++r 825 5),e6 [229] ([14,32,40,48,81,810]++r 830 4),a6 [18,179] ([52,337,356,673,675,712,773]++r 834 5) [0,4],u6 [18,198] [32,337,449,462,661,673,686,712,839],e6 [230] [32,40,43,812,840,841],e6 [25,227] [40,337,527,539,540,682,683,812,842,843,844],u6 [14,25,85] ([316,421,422,540,743,823]++r 845 4),u6 [14,21,22] [351,562,663,694,696,711,776,849,850],([18,21,172,2,3,4,5],[14,43,150,296,359,851,852,853],[0]),e6 [231] ([14,40,47,48,81,85,175,254,632]++r 854 5),([18,21,2,3,22,4,5],[110,123,296,327,350,351,359,859],[0,4]),u6 [177,9] [14,45,47,52,85,332,611,632,636,786,860,861,862],([86,88,1,2,3,10,4,5],([14,40,64,265,267,273,274,719]++r 863 7),[0]),([232,0,12,9,3,4,5],([14,38,45,47,100,182,283,333,335,408]++r 870 4),[3]),([0,1,2,19,22,4,5],[14,85,340,344,350,370,428,468],[0,4]),u6 [204] [14,32,43,47,48,85,373,507,874,875],([0,9,3,13,4,5],[38,47,100,579],[0,3]),a6 [19,38] [14,172,428,638,876] [0,4],u6 [97,165] [14,45,47,70,254,461,463,771,877,878],([15,25,1,21,2,3,4,5],[40,190,295,300,301,527,528,607,774,775,879,880],[0]),a6 [170,19] [14,172,298,340,370,428,818,881] [0,4],u6 [15,25,85] [208,300,301,425,527,682,743,788,882,883,884],u6 [168] ([14,38,43,175,254,281,678]++r 885 4),u6 [18,175] [14,32,462,497,641,642,686],([25,0,12,9,3,4,5],[45,47,100,182,193,283,333,527,528],[0,3]),([233,1,2,3,28,4,5],([38]++r 889 6),[]),([0,1,2,19,4,5,135],[14,172,344,370,462,800,895],[4]),e6 [25,114] [52,205,208,254,466,491,539,603,604,671,682],([116,0,1,2,19,4,5],[14,40,47,172,254,340,370,428,623,896],[4]),e6 [235] ([14,175,462]++r 897 7),e6 [236] [14,43,45,47,48,85,740,904,905],a6 [14,18,22] [338,421,422,423,514,675,694,711,712,849,906,907,908] [0,4],e6 [86,237] ([47,52,232,254,337,652,713,735]++r 909 7),a6 [156] ([38,40,43,48,52,85,229,894]++r 916 4) [0,2],([54,0,1,21,2,4,5],[14,38,196,197,457,553],[0]),([14,18,21,2,3,4,5],[14,43,110,123,296,327,359,422,514,550,920],[0,4]),e6 [86,238] ([14,47,232,235,254,274]++r 921 8),u6 [18,182] [32,254,337,368,668,670,686,773,837,929],([0,1,2,239,28,4,5],[14,47,337,890,930,931,932],[]),e6 [240] ([14,38,48,52,175,462,600,696]++r 933 7),e6 [86,125] [52,233,235,308,309,512,597,735,738,940,941,942],([18,21,2,3,4,124,5],[14,110,296,327,359,360,797,943,944],[0]),u6 [195,19] [14,40,47,172,370,428,462,472,945,946],([241,1,2,9,3,130,5],([38,44,617,632,636]++r 947 6),[3]),u6 [25,9,7] [14,245,433,436,467,527,528,610,611,677,683,953],([18,0,1,2,3,6,7],[82,83,84,169,175,261,371,712,773],[0,4]),([0,1,21,2,4,58,5],[14,38,196,198,199,201,457,521,663,954],[0]),u6 [18,125] [308,309,497,597,598,675,686,837,955],e6 [242] ([14,47,48,81,85,905]++r 956 4),a6 [19,6] [14,172,254,340,370,387,414,428,452,493,693,960,961] [0,4],a6 [19,7] [14,172,340,370,382,387,428,467,471,570,772,960] [0,4],u6 [25,12,6] [14,414,436,454,493,527,528,540,678,680,683,962,963],([14,15,0,1,21,2,3],[71,93,96,97,98,241,244,293,457,663],[0,2,4]),([137,18,21,2,3,4,5],[14,47,110,123,296,327,357,359,964,965,966],[0]),u6 [86,89] ([14,45,52,233,235,254,274,739]++r 967 6),e6 [10,243] ([210,232,254,337,718,845,866]++r 973 4),([14,15,18,0,1,2,3],[71,96,97,98,244,490,497,712],[0,4]),([15,18,21,2,3,4,5],[14,47,110,123,150,295,301,327,420,977],[0,4]),e6 [244] [40,47,52,85,196,964,978],a6 [245] [14,52,85,232,414,493,712,979] [4],a6 [14,19] [14,337,340,370,421,422,423,428,472,711,908] [0,4],e6 [246] ([14,40,43,48,81,175,462]++r 980 7),([199,85,51,1,2,3,4],([38,175,458,784,882]++r 987 4),[2]),a6 [18,138] ([254,417,444,497,673,675,686]++r 991 5) [0,4],e6 [248] [40,47,52,85,232,996,997,998],([86,1,2,3,10,6,4,5],[14,64,219,233,273,274,452,493,560,866,868,999],[0]),([15,86,1,2,3,10,4,5],[40,64,274,295,300,302,719,866,868,869,1000,1001],[0]),a6 [18,22,6] [14,219,350,351,414,452,468,493,559,560,675,686,693,694,712,770,906,961] [0,4],a6 [15,19] [14,40,47,172,254,300,301,302,344,428,472,701,1002] [0,4],([18,21,2,3,6,4,5],[14,110,123,150,219,296,327,352,414,1003],[0,4]),a6 [15,86,28] [213,235,300,301,302,701,739,787,890,894,1000,1004] [0,5],u6 [15,25,12] [208,300,301,527,678,682,756,788,1005,1006],e6 [249] ([14,38,40,45,48,232,743,845,882]++r 1007 4),e6 [250] [14,32,40,48,85,678,1007,1011,1012],a6 [18,49] [14,52,344,430,477,497,646,837,1013] [0,4],u6 [23] [40,44,47,81,121,175,254,351,462,558,559,562,563,1014],e6 [251] ([40,47,52,85,196,965]++r 1015 4),u6 [25,9,6] [14,433,436,493,527,528,540,610,636,683,770,962,1019],([54,86,0,1,2,4,5],[14,195,196,235,553,684,1020],[]),([0,1,21,3,4,129,5],[147,205,287,288,457,518,663,1021,1022],[0]),([189,1,2,9,3,4,5],[38,44,81,406,610,617,636,754,1023,1024,1025],[0]),([86,0,252,2,3,4,5],([14,47,235,652]++r 1026 5),[]),([0,1,21,2,3,6,7],[82,83,84,154,169,258,261,317,627,663],[0,2,4]),a6 [253,19] [14,172,254,340,370,1031,1032,1033] [4],([86,0,1,2,4,58,5],[14,196,198,199,235,521,566,740,954,1034],[]),([25,0,1,2,4,58,5],[14,43,198,199,201,208,521,540,560,566,640,954],[]),([233,1,2,9,3,4,5],[38,44,610,617,889,891,892,893,1035,1036],[3]),e6 [254] [40,47,52,85,232,623,712,896,1037],e6 [255] [14,47,81,217,220,1038],e6 [97,102] [14,45,47,70,463,1039],([25,0,101,2,3,4,102],([14,47,208,527]++r 1040 4),[1]),a6 [113,169] ([14,32,40,45,52,289,290,291,778,819,821]++r 1044 4) [1],([86,1,2,3,10,4,165,5],[14,64,267,273,868,877,981,1048],[0]),u6 [21,22,7] [44,350,351,468,559,562,570,600,627,816,1049],u6 [86,166] ([14,45,52,233,235,274,735]++r 1050 6),u6 [14,97] ([52,337,421,422,461,581,771,907]++r 1056 4),u6 [15,97] [40,52,70,254,274,300,301,463,771,787,1000,1056,1057,1060],e6 [257] ([14,40,47,48,175,462]++r 1061 4),e6 [259] ([32,45,47]++r 1065 4),e6 [258,28] ([32,48,213,229,337,462,918]++r 1068 5),e6 [260] [40,43,45,47,196,798,944,1073],([14,15,86,0,1,2,3],[71,93,96,97,98,235,241,243,244,740,1074],[0,2]),([86,163,1,2,3,10,4,5],([64,265,267,273,279,719,866,868]++r 1075 5),[0]),e6 [261] [14,32,43,45,48,175,256,276,1080,1081,1082],e6 [262] [32,43,45,47,175,704,1080,1083],([54,148,0,1,2,4,5],[14,195,196,197,390,503,553,684],[0,1,3,5]),a6 [177,12] ([43,47,220,331,337,373,454,455,679,1005]++r 1084 5) [0,3],([25,1,21,2,3,6,4,5],[14,44,190,205,219,292,414,493,527,528,539,695,1089],[0]),([86,1,2,3,10,4,5,102],[14,64,267,276,1039,1090],[0]),([25,0,263,2,3,165,5],([14,45,81,208,528,540]++r 1091 6),[]),([199,51,1,2,9,3,4],[38,44,611,617,632,784,785,989,990,1097,1098],[0,3]),a6 [98,6] [14,76,81,205,219,318,414,435,452,493,560,693,695,698,770] [0,4],u6 [21,138] [40,43,44,45,47,417,418,444,457,562,600,608,991,992,1099],([86,1,2,3,10,4,5,7],[14,64,211,233,265,273,274,467,471,564,866,868,1100],[0]),([14,86,1,2,3,10,4,5],[43,265,273,421,423,514,719,866,868,869,1058,1101],[0]),u6 [21,179] [40,43,44,45,47,52,356,358,562,596,608,627,663,834,835,1102],([25,0,252,2,3,4,5],[14,47,208,527,1026,1027,1029,1103],[]),u6 [34] [14,40,43,48,81,175,229,254,255,257,462,1072],e6 [177,85] [43,47,52,251,252,331,332,336,337,747,883,987,988,1087,1088,1104,1105],u6 [27] [14,47,81,85,175,254,372,373,376,462,718,719],a6 [86,28,6] [14,233,414,452,493,659,693,738,740,770,890,918,1106,1107,1108] [0,2,5],a6 [86,28,7] [14,233,245,382,467,471,570,713,738,890,1069,1108,1109,1110] [0,5],([199,95,51,1,2,3,4],[38,175,784,785,990,1097,1111,1112,1113],[3]),a6 [14,86,28] [421,422,423,659,711,738,740,907,918,1058,1114,1115] [0,5],u6 [25,85,6] [14,251,414,436,493,527,538,540,743,845,846,962,1116],u6 [176] ([14,38,40,47,48,81,85,457,600,663]++r 1117 4),u6 [25,85,7] [14,251,382,436,467,526,527,543,677,743,846,987,1121],e6 [264] ([14,43,47,48,52,85,905]++r 1122 7),([86,0,101,2,3,4,102],[14,47,235,652,1040,1041,1042,1129,1130],[0]),e6 [265] [43,45,47,85,196,978,1131,1132],([0,1,3,10,4,129,5],[147,217,220,287,288,518,601,866],[1]),e6 [86,138] [52,233,235,254,417,418,444,738,739,991,1133,1134,1135],e6 [266] [14,81,233,235,493,740,1136,1137,1138]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_8_0 : checkNodesBT W_17 g_17 F_17 P_17_8 A_17 B_17_7 8 N_17_8_0 = true := by decide +kernel
def N_17_8_1 : List NodeSpec := [a6 [15,18,22] [295,300,301,302,350,497,568,587,673,701,787,1002,1139] [0,4],([86,0,2,3,4,209,5],([45,235]++r 573 4++[738,740,1140,1141,1142]),[0,1]),([189,85,1,2,3,4,5],[38,406,407,743,755,845,882,1023,1025],[]),u6 [14,25,12] [421,422,454,540,678,680,823,847,1143],([86,0,1,2,3,6,7],[82,83,84,154,169,175,258,260,261,713,740,1144],[0,2]),e6 [267] [14,32,43,45,47,48,175,205,211,1080,1145,1146],e6 [268] ([40,47,52,85,196,944]++r 1147 4),([112,0,1,21,3,4,5],[52,130,205,457,523,529,562,590,1151],[0]),([54,0,56,1,2,4,5],[14,195,196,197,390,503,553,684],[0]),([86,160,0,2,3,4,5],[235,266,268,269,738,1152,1153,1154],[0,1]),([18,21,2,3,4,5,7],[14,110,123,150,211,296,327,359,378,382,1155],[0,4]),([241,1,2,3,28,130,5],[38,229,894,918,948,950,952,1156],[]),e6 [269] [52,85,232,267,981,1157,1158],a6 [10,166] [14,40,217,267,719,866,976,1050,1051,1053,1054,1159,1160] [0,1],([113,18,21,2,3,4,5],[14,47,110,123,150,296,359,405,779,1161,1162],[0,4]),([0,1,2,270,28,4,5],([14,47,254,337,890]++r 1163 4),[]),u6 [200] [44,52,85,211,457,474,627,1167,1168],e6 [271] [14,52,175,462,935,1169,1170,1171],e6 [10,175] [14,32,85,217,323,462,644,1172,1173,1174],e6 [272] ([14,32,43,47,48,175,778]++r 1175 5),e6 [273] [14,47,52,81,85,175,254,719,759,1180,1181,1182],([167,1,2,3,28,4,132],[38,609,613,615,616,890,894,1069],[3]),e6 [25,166] [45,208,251,528,539,843,1050,1051,1052,1054,1160],u6 [111,19] [14,40,47,81,172,337,340,348,370,428,472,1183,1184],u6 [162] [14,52,85,217,267,276,277,506],e6 [274] [14,47,217,628,719,1185,1186],e6 [275] ([40,48,52,85,175,229,905]++r 1187 4),a6 [10,114] [14,40,217,248,267,466,491,604,671,718,725,866,1191] [0,1],([189,1,2,3,28,4,5],[38,81,406,890,894,918,1023,1025],[]),([0,1,2,3,10,6,7],[82,83,84,154,169,210,220,258,261],[0,1,2,3,4]),([112,0,1,3,10,4,5],[130,217,523,529,590,676,866,1192],[1]),([54,0,1,2,10,4,5],[14,40,195,196,217,553],[]),a6 [42] [45,47,52,85,211,217,263,264,1193] [0,1,2,3,4,5],([8,0,1,2,3],[1,207],[0,1,2,3,4,5]),([14,15,0,1,2,3,10],[71,93,96,97,98,217,220,241,244],[0,1,2,3,4]),e6 [25,175] ([14,85,208,539]++r 641 4++[683,843]),e6 [25,238] [14,47,208,254,527,539,682,921,923,925,926,928,1194],([25,26,0,1,2,4,5],[43,45,52,434,435,436],[0]),([189,95,1,2,3,4,5],[38,406,754,755,914,1024,1025,1113,1195],[]),([25,112,0,1,3,4,5],[130,205,208,436,523,590,676],[]),e6 [277] [14,40,47,48,81,1196,1197],([18,21,2,3,4,5,135],[110,123,150,327,359,704,800,1198],[0,4]),([25,54,0,1,2,4,5],[14,43,195,196,197,208,390,503,543,553,684],[]),([14,15,25,0,1,2,3],[71,96,97,98,208,241,244,540],[0,1]),u6 [18,180] [14,32,254,497,618,619,622,686],e6 [10,238] [14,217,232,254,718,922,924,925,1199,1200],([86,0,263,2,3,165,5],[14,45,81,235,738,740,1091,1092,1093,1095,1201,1202,1203],[]),([55,54,0,1,2,4,5],[14,195,196,197,390,503,553,684,1204],[0]),e6 [278] ([14,81]++r 1205 4),([199,51,1,2,3,28,4],[38,229,784,894,989,990,1069,1098],[3]),e6 [279] [14,40,43,1209,1210],u6 [15,21,22] [457,587,608,701,879,1139,1211],([39,0,1,3,4],[54,207],[0,1,2,3]),e6 [280] [14,40,43,81,671,1212],([152,0,1,2,4,58,5],[14,81,196,198,199,201,521,560,566,954,1213],[0,1,3,5]),([0,1,2,4,58,161,5],[14,81,198,199,337,640,1214],[0]),u6 [14,25,9] [421,433,528,540,610,636,823,847,907,1215],([150,0,1,2,4,58,5],[14,198,199,201,521,566,640,954,1216,1217],[0]),([281,0,1,2,4,58,5],[14,81,198,199,201,521,560,566,954,1218],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_8_1 : checkNodesBT W_17 g_17 F_17 P_17_8 A_17 B_17_7 8 N_17_8_1 = true := by decide +kernel
def N_17_8 := N_17_8_0 ++ N_17_8_1
def B_17_8 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_8
set_option maxRecDepth 500000 in
lemma B_17_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 8 xs.toFinset) B_17_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 11) (W := W_17) (raw := r_17) (pspecs := ps_17) (used := U_17_8) S_17_ok
  have hm0 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_7_ok C_17_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_7_ok C_17_8_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_17_9 : List Nat := ([14,38,40,43,44,45,47,48,52,71,81,85,110,169,175,193,196,205,207,208,210,211,217,219,220,229,233,235,245,251,252,254,267,274,276,279,281,295,298,300,301,302,337,338,344,350,351,373,382,410,414,421,422,423,435,436,452,454,457,462,463,467,468,471,491,493,497,514,527,528,539,540,543,559,560,562,564,568,570,571,591,596,599,600,601,607,608,610,611,615,617,622,623,624,627,632,636,638,639,640,644,645,650,652,659]++r 663 4++[671,672,673,675,676,678,679,683,686]++r 693 4++[698,701,704,705,708,711,712,713,718,719,725,726,729,735,738,739,740,743,749,756,758,769,770,772,773,776,778,779,782,787]++r 794 5++[800,810,812,816,818,831,837,845,852]++r 863 5++[870,871,873,876,877,879,882,886,890]++r 892 5++[898,907,908,918,926,944,947,952,961,964,965,978,981,983,987,988,990,994,998,1000,1002,1007,1011,1018,1025,1039,1048,1057,1058,1062,1068,1069,1070,1072,1075,1076,1077,1081,1087,1090,1107,1108]++r 1110 4++[1128,1132,1136,1145,1150,1156,1161,1177,1195,1203,1207]++r 1219 113)
def P_17_9 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 U_17_9
def N_17_9 : List NodeSpec := [([14,15,0,1,2,3],[71,81,207],[0,1,2,3,4,5]),a6 [54] [14,38,40,43,44,45,47,48,52,85,175,196,207,564] [0,2,4],a6 [58] [14,38,40,43,44,45,47,52,81,85,207,560,640] [0,2,4],([0,1,2,4,58,5],[81,207],[0,1,2,3,4,5]),a6 [138] [40,43,45,47,52,85,207,254,994,1219] [0,1,2,3,4,5],a6 [125] [40,43,45,47,52,85,207,462,599,1220] [0,1,2,3,4,5],e6 [282] [14,40,43,44,45,47,52,337,1221],([199,51,1,2,3,4],[43,175,207,990],[0,1,3]),e6 [137,283] [14,196,462,964,965,978,1018,1132,1222,1223],([167,1,2,3,4,132],[40,175,207,615],[0,1,2,3,4]),a6 [239] [14,40,45,47,52,85,337,1224,1225] [0,1],([241,1,2,3,130,5],[43,81,207,952,1226],[0,1,2,3,4]),a6 [15,25] [40,48,207,208,254,300,301,302,436,527,528,568,683,701,787] [0,1],e6 [284] [14,40,43,44,45,47,52,81,207],a6 [14,25] [40,81,338,421,422,423,436,527,528,539,540,543,683,711,907] [0,1],a6 [25,6] [175,208,414,436,452,493,527,528,539,540,560,683,693,770] [0,1,2,4],e6 [285] [14,43,45,47,48,52,81,85,207,539,1227],a6 [25,113] [40,175,205,208,337,436,527,528,539,540,672,683,778,779,1177,1228] [0,4],u6 [199,95] ([38,47,175,435,794,1111,1113,1195]++r 1229 5),([233,1,2,3,4,5],[40,207,892,893],[0,1,2,3,4]),u6 [25,101] ([14,40,47,175,208,337,527,528,539,540,926]++r 1234 4),([0,1,3,4,129,5],[52,81,207,601],[0,1,2,3]),e6 [25,170] [40,52,81,85,205,208,298,436,527,528,539,540,818,1128,1238,1239,1240],e6 [286] [14,40,45,47,52,85,207],a6 [175] [40,43,45,47,85,207,462,644,645] [0,1,2,3],u6 [25,165] [45,47,81,208,251,254,337,527,528,539,540,877,983,1048,1241,1242],a6 [198] [40,43,45,47,85,337,462,1243,1244] [0,1,3],([112,0,1,3,4,5],[52,207,591,676],[0,1,2,3]),a6 [10,7] [40,210,211,217,220,245,267,382,467,471,564,570,718,719,866] [0,1,2,3,4],a6 [144] [43,45,47,52,85,217,337,462,1245,1246] [2,3,4],a6 [113,10] [40,43,85,217,220,267,718,719,726,778,779,866,1161,1177,1228] [0,1,4],a6 [167,28] [38,43,45,47,229,281,337,890,894,918,1069,1072,1108,1224,1247] [0,2,3],a6 [170,10] [40,43,210,217,220,267,298,650,718,866,1128,1238,1248] [1,4],a6 [232,28] [38,43,45,47,229,254,337,870,871,890,894,918,1069,1072,1108,1156,1249] [0,3],e6 [287] [14,40,45,47,48,52,81,85,175,254,337,462,539,1250,1251,1252],a6 [10,165] [47,217,220,267,718,719,725,726,866,981,983,1048,1241] [0,2],a6 [241,28] [38,45,47,890,894,918,1069,1072,1108,1253,1254] [0,3],a6 [15,86] [38,40,52,85,207,235,254,274,295,300,301,302,568,652,701,738,787,1000,1255] [0,2],a6 [86,7] [38,43,85,211,235,245,274,382,467,471,564,570,652,738,1110,1145] [0,2,5],u6 [137,86] [14,38,40,52,85,196,235,274,462,652,659,713,735,738,740,978,1018,1256],a6 [86,135] [85,235,274,652,704,705,738,800,895,1257,1258,1259] [5],e6 [288,124] ([14,81,85,196,337,797,798,944,1150]++r 1260 4),a6 [10,102] [217,267,276,718,719,866,1081,1090,1264] [0,2],u6 [116,86] [52,81,85,235,274,623,624,652,713,729,738,740,896,1265,1266,1267],a6 [21,22] [44,52,85,350,351,468,559,562,607,627,663,694] [0,4],a6 [97] [14,40,45,47,52,81,175,254,274,462,463,1057] [0,1],e6 [137,289] [14,40,43,196,462,964,965,978,1018,1132,1222,1268],a6 [21,38] [40,44,47,175,205,457,607,638,639,708,876] [0,4],([54,0,1,2,4,5],[207,1269],[0,1,2,3,4,5]),a6 [15,21] [40,43,44,45,47,254,295,300,301,302,457,562,568,600,607,701,787,879] [0,2,4],e6 [290] [14,38,40,43,44,45,47,52,85,207,254,1270],e6 [291,124] [14,43,81,196,337,797,798,944,1150,1260,1261,1263,1271],a6 [131] [43,45,47,52,85,207,462,1207,1272,1273,1274] [0,2,3,4],u6 [219] [40,43,44,45,48,52,81,85,254,337,457,462,749,1275],a6 [25,85] [40,47,52,85,193,251,252,527,528,539,683,743,845,987] [0,2],([189,1,2,3,4,5],[40,81,207,1025],[0,1]),u6 [25,102] [45,47,208,251,527,528,539,1039,1081,1090,1264],a6 [14,86] [38,52,81,85,274,337,338,421,422,423,514,652,711,713,738,740,907,1058,1276] [0,2],u6 [234] [40,43,44,45,47,48,52,81,85,175,254,337,462,898,1277,1278],a6 [98] [14,40,43,47,48,52,81,85,175,205,254,435,462,607,698,1279] [0,4],a6 [199,12] [14,38,43,45,52,85,678,679,756,794,1233,1280] [0,3],([0,1,2,3,6,7],[81,169,175],[0,1,2,3,4,5]),([25,1,21,2,3,4,5],[14,40,43,47,205,436,527,528,607],[0]),u6 [25,263] ([14,40,47,81,208,527,539,540]++r 1281 5),a6 [241,9] [14,38,44,45,47,52,85,610,611,617,636,1007,1011,1253,1254,1286,1287] [0,3],a6 [232,85] ([14,38,43,45,47,52,81,85,252,254,337,743,870,871,873,882,987,988,1249]++r 1288 4) [2],a6 [18,6] [14,43,45,175,344,414,452,493,497,560,675,686,693,712,961] [0,4],a6 [25,7] [208,245,382,436,467,471,527,528,539,564,570,683] [0,1],a6 [10,6] [40,217,219,220,267,337,414,452,493,560,693,718,719,770,866] [0,1,2,3,4],a6 [18,135] [43,45,344,497,675,686,800,895,1257,1259] [0,4],a6 [113,21] [40,43,44,45,47,52,205,457,562,600,607,663,696,778,779,1161,1177] [0,4],a6 [21,6] [40,44,47,219,414,452,457,493,560,562,600,607,663,693,695,770] [0,2,4],a6 [15,18] [14,40,47,207,254,300,301,302,344,497,568,675,686,701,1002] [0,4],u6 [116,18] [40,43,45,81,344,497,623,675,686,712,773,896,1266,1267],a6 [18,22] [43,45,52,85,344,350,468,571,675,694,712,773] [0,4],a6 [113,18] [14,47,175,337,344,497,672,675,712,778,779,782,1228] [0,4],a6 [18,37] [14,175,337,497,622,675,686,712,758,1292] [0,4],a6 [18,124] [14,81,196,254,337,344,673,686,712,773,797,798,1260,1261] [0,4],a6 [21,48] [44,52,205,457,600,607,608,663,664,665,696,810,831,1293] [0,4],a6 [19] [14,40,47,52,81,85,175,254,344,462] [0,4],a6 [14,10] [40,43,210,220,267,337,338,422,423,514,711,718,719,866,907] [0,1,2,3,4],u6 [227] [40,43,47,48,81,85,175,254,337,462,756,812],a6 [232,95] [38,47,81,254,337,435,870,1111,1112,1113,1195,1229,1230,1249,1288,1290,1294,1295] [3],a6 [232,9] [14,38,44,45,47,52,85,254,337,610,611,617,632,636,870,871,947,1249,1286,1290,1294,1296] [0,3],a6 [86,163] [38,43,45,47,52,81,85,235,274,279,738,740,1075,1076,1077,1203,1297,1298,1299] [0,1],a6 [25,9] [14,45,47,52,85,436,527,528,539,540,610,611,636,1286] [0,3],a6 [114] [40,43,45,47,52,207,254,491,671,672] [0,1,2,3],a6 [292] [40,45,47,52,85,254,337,540,1300] [2,3,4],u6 [258] [43,45,47,48,81,85,175,205,254,337,462,1068,1070],a6 [199,28] [38,45,47,795,890,894,1069,1072,1108,1231] [0,3],([86,1,2,3,10,4,5],[14,40,43,48,267,274,719,866],[0]),a6 [86,165] [38,45,47,81,235,254,274,337,652,659,738,739,740,877,981,983,1048,1241,1242,1301,1302] [0,5],a6 [276] [40,45,47,52,85,207,254,1303,1304,1305] [0,2,3,4],u6 [137,18] [14,40,47,196,337,344,462,675,686,712,773,837,964,978],a6 [86,88] [38,40,47,52,85,175,235,274,337,652,659,738,740,863,864,865,867,1306,1307,1308] [0,1,2],a6 [177] [43,45,47,52,81,85,175,220,254,337,462,1087,1309] [0,1],a6 [247] [40,47,52,85,254,337,712,998] [0,4],([18,21,2,3,4,5],[43,47,110,410],[0,4]),a6 [25,12] [40,47,85,454,527,539,540,543,678,679,683,1280] [0,3],a6 [18,38] [14,52,85,497,638,675,876,1310,1311] [0,4],a6 [232,12] [14,38,47,254,337,373,454,678,679,756,870,1280,1294,1312] [0,3],a6 [18,172] [14,43,45,52,85,497,712,852,1313,1314] [0,4],u6 [21,135] [457,562,600,607,704,705,800,895,1257,1259,1315],e6 [293] [14,40,45,47,52,81,85,207],a6 [15,10] [40,43,48,217,254,267,295,300,301,302,568,701,718,719,787,866] [0,1,2,3,4],a6 [170,21] [40,43,44,45,47,205,298,457,562,607,627,650,663,1128,1316] [0,4],e6 [294] [14,38,40,43,44,45,47,52,81,85,175],a6 [199,9] [14,38,44,45,47,52,85,610,611,617,794,795,1231,1232,1233,1286] [0,3],u6 [137,21] [14,40,43,44,45,47,196,457,462,562,596,600,607,627,663,696,964,965,978,1018],a6 [86,28] [45,47,85,229,274,652,713,738,740,890,918,1069,1072,1108,1317] [0,2,5],a6 [14,18] [14,81,337,338,344,421,422,423,675,686,711,712,773,908] [0,4],a6 [167,9] [14,38,44,45,47,52,85,281,337,610,611,617,632,636,886,1224,1247,1286,1318,1319] [0,3],u6 [170,18] [14,81,85,298,344,497,675,712,769,773,818,1238],u6 [21,124] [14,44,81,196,254,337,457,562,600,607,608,663,696,797,798,944,1150,1260,1261],a6 [18,48] [14,52,81,85,254,337,344,497,664,665,666,673,675,712,1320,1321] [0,4],a6 [21,7] [40,44,47,81,211,245,382,457,467,471,562,564,570,600,607,627,816] [0,2,4],a6 [14,21] [40,43,44,45,47,337,338,421,422,423,514,562,600,607,627,663,711,776,907] [0,2,4],a6 [256] [40,45,47,52,233,235,254,337,1062,1322] [0,2],u6 [116,21] [40,43,45,47,457,562,600,607,623,624,627,663,729,896,1266,1267],a6 [86,263] [14,38,52,81,85,235,274,652,740,1281,1282,1283,1285,1323,1324] [0,2],a6 [270] [14,40,45,47,52,85,254,337,1249,1325,1326] [0,1],a6 [86,101] ([14,38,43,45,47,52,175,235,274,337,652,738,740,926]++r 1234 4++[1327,1328,1329]) [0,2],a6 [199,85] [14,38,52,85,175,252,743,794,795,796,882,987,1231] [0,2],a6 [18,7] [14,43,45,81,175,254,344,382,467,471,497,564,570,675,686,712,772,773] [0,4],a6 [86,102] [38,43,45,47,235,274,276,652,738,1039,1081,1090,1264,1330] [0,5],a6 [86,6] [38,43,85,175,219,235,274,414,452,493,560,652,693,738,740,770,1107,1136] [0,2],a6 [86,124] [14,38,81,196,235,254,274,337,652,659,738,739,740,797,798,944,1150,1260,1261,1331] [0,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_9 : checkNodesBT W_17 g_17 F_17 P_17_9 A_17 B_17_8 9 N_17_9 = true := by decide +kernel
def B_17_9 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_9
set_option maxRecDepth 500000 in
lemma B_17_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 9 xs.toFinset) B_17_9 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_8_ok C_17_9
def U_17_10 : List Nat := [35,40,43,45,47,48,52,81,85,175,207,254,274,337,338,344,462,560,564,568,607,1224,1226,1227,1228,1231,1238,1249,1250,1253,1332]
def P_17_10 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 U_17_10
def N_17_10 : List NodeSpec := [a6 [14] [40,43,45,47,48,52,81,85,175,338] [0,1,2,3,4,5],a6 [116] [40,43,45,47,48,52,81,85,175,207] [0,1,2,3,4,5],a6 [124] [40,43,45,47,48,52,81,85,207,254,337] [0,1,2,3,4,5],a6 [18] [40,47,48,52,81,85,175,344] [0,4],a6 [241] [40,45,47,48,52,81,85,175,207,1253] [0,1,2,3,4],a6 [7] [40,43,45,47,48,52,81,85,207,564] [0,1,2,3,4,5],a6 [86] [35,40,43,45,47,48,52,81,85,175,274] [0,2,5],a6 [10] [40,43,45,47,48,52,81,85,175] [0,1,2,3,4],a6 [25] [40,45,47,48,52,81,85,175] [0,1,2,3,4],a6 [21] [40,43,45,47,48,52,81,85,175,607] [0,2,4],a6 [170] [40,43,45,47,48,52,81,175,207,1238,1332] [0,1,2,3],a6 [130] [40,43,45,47,52,81,85,207,254,337,1250] [0,2,3,4],a6 [199] [40,45,47,48,52,85,175,207,1231] [0,1],a6 [6] [40,43,45,47,48,52,81,85,207,560] [0,1,2,3,4,5],a6 [135] [40,43,45,47,48,52,85,207] [0,1,2,3,4,5],a6 [232] [40,43,45,47,48,52,81,85,175,207,254,337,1226,1249] [0,1,3],a6 [113] [40,43,45,47,48,52,81,85,207,337,1228] [0,1,2,3,4],a6 [15] [40,43,45,47,48,52,85,207,568] [0,1,2,3,4,5],a6 [137] [40,43,45,47,48,52,81,85,175,207,337,462] [0,1,2,3,4,5],a6 [167] [40,43,45,47,48,52,81,85,175,207,337,1224] [0,1,2,3,4],a6 [132] [40,43,45,47,52,85,207,1227] [0,2,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_10 : checkNodesBT W_17 g_17 F_17 P_17_10 A_17 B_17_9 10 N_17_10 = true := by decide +kernel
def B_17_10 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_10
set_option maxRecDepth 500000 in
lemma B_17_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 10 xs.toFinset) B_17_10 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_9_ok C_17_10
def U_17_11 : List Nat := [48]
def P_17_11 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 U_17_11
def N_17_11 : List NodeSpec := [a6 [] [48] [0,1,2,3,4,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_11 : checkNodesBT W_17 g_17 F_17 P_17_11 A_17 B_17_10 11 N_17_11 = true := by decide +kernel
def B_17_11 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_11
set_option maxRecDepth 500000 in
lemma B_17_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 11 xs.toFinset) B_17_11 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_10_ok C_17_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,22,23),(VAR 1,21,23),(VAR 2,19,23),(VAR 3,17,25),(VAR 4,7,23),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_11 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 12 := lower_of_forestBT root_17_ok B_17_11_ok root_17_in

def g_orig := (d 0xeeeaeae8eae8e888)
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,4),(2,3),(3,5)]) (by decide +kernel) low_17
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.and,[3,4]⟩,⟨.or,[6,2]⟩,⟨.or,[4,3]⟩,⟨.and,[1,7]⟩,⟨.or,[1,6]⟩,⟨.and,[0,10]⟩,⟨.or,[5,8]⟩,⟨.and,[5,8]⟩,⟨.and,[2,12]⟩,⟨.or,[0,9]⟩,⟨.or,[11,14]⟩,⟨.or,[16,13]⟩,⟨.and,[17,15]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_45154

open PEqualNP.Outside.L_meta_45154 in
theorem PEqualNP.Outside.L_meta_45154 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
