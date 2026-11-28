import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_44758
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
def evalInput (r : Row) : Fin 8 → Bool := fun i => r.val.testBit i.val
def packInput (x : Fin 8 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat + 128 * (x 7).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    have h6 := Bool.toNat_le (x 6); have h7 := Bool.toNat_le (x 7); omega⟩
lemma evalInput_packInput (x : Fin 8 → Bool) : evalInput (packInput x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (j : Fin 8),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat + 128 * b7.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6, b7].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
lemma var_testBit (i : Fin 8) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 255 := by
  let seeds : List SWire := (varsOf 255).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 255).all (fun a => decide (a < 2^256) && !a.testBit 0) = true := by decide +kernel
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
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi8 : i < 8 := by simpa using hi2
      have hv : (varsOf 255)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 255)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi8⟩ r
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
lemma replace_of_lower (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 255) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : ∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn : (Fin 8 → Bool) → Bool)
    (hEdgeT : ∀ r : Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  have hwEval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x := by
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
    have hsup : Supply ((varsOf 255).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 255).map obs)
        (show Reach ((varsOf 255).map obs) 0 ((varsOf 255).map obs) from rfl) hsup
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


def g_0 := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
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
def ps_0 : BT (Option PoolSpec) := btOfList 1 ((([] : List PoolSpec)).map some)
def B_0_2 : BT (List (List Nat)) := BT.empty
lemma B_0_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 2 xs.toFinset) B_0_2 := .empty
def P_0_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 r_0 S_0 ps_0 []
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
def g_1 := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
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
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_1 : Slice r_1 g_1 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_2 : Slice r_1 g_1 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_3 : Slice r_1 g_1 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
def S_1 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4)]
lemma S_1_ok : btAll (fun o => ∀ p, o = some p → Slice r_1 g_1 p.1 p.2) S_1 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_1_0) (forall_cons (fun _ h => by cases h; exact sl_1_1) (forall_cons (fun _ h => by cases h; exact sl_1_2) (forall_cons (fun _ h => by cases h; exact sl_1_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_1 : BT (Option PoolSpec) := btOfList 2 ((([(2,[]),(1,[]),(3,[]),(0,[])] : List PoolSpec)).map some)
def B_1_2 : BT (List (List Nat)) := BT.empty
lemma B_1_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 2 xs.toFinset) B_1_2 := .empty
def P_1_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 [0,1]
def N_1_3 : List NodeSpec := [([6,0,1,2],[],[]),([0,7,8,9],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_3 : checkNodesBT W_1 g_1 F_1 P_1_3 A_1 B_1_2 3 N_1_3 = true := by decide +kernel
def B_1_3 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_3
set_option maxRecDepth 500000 in
lemma B_1_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 3 xs.toFinset) B_1_3 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_2_ok C_1_3
def P_1_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 [1,2,3]
def N_1_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([10,0,1,2,3],[],[]),([0,1,2,11,8],[1,3],[10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_4 : checkNodesBT W_1 g_1 F_1 P_1_4 A_1 B_1_3 4 N_1_4 = true := by decide +kernel
def B_1_4 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_4
set_option maxRecDepth 500000 in
lemma B_1_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 4 xs.toFinset) B_1_4 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_3_ok C_1_4
def P_1_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 [0,1,2,3]
def N_1_5 : List NodeSpec := [([0,1,4,2,3],[0,1,2,3],[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_5 : checkNodesBT W_1 g_1 F_1 P_1_5 A_1 B_1_4 5 N_1_5 = true := by decide +kernel
def B_1_5 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_5
set_option maxRecDepth 500000 in
lemma B_1_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 5 xs.toFinset) B_1_5 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_4_ok C_1_5
def P_1_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 [0,1,2,3]
def N_1_6 : List NodeSpec := [([0,1,2,3],[0,1,2,3],[0,2,4,6,8,11])]
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
def g_2 := 0xe880e880e880e880e880e880e880e880e880e880e880e880e880e880e880e880
def r_2 : List Nat := varsOf 15
def p_2 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14]
def q_2 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6]
def F_2 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_2 : goodPairs g_2 p_2 q_2 := goodPairs_of (by decide +kernel)
def W_2 : BT Decor := buildWiresBT 4 (mkBase p_2 q_2 r_2) [(0,0,1),(0,0,2),(0,1,2),(0,6,3),(3,7,0),(0,2,3),(3,9,0),(0,4,2)]
lemma W_2_ok : btAll (fun x => faithful p_2 q_2 x ∧ x.1 < 2^256) W_2 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_2 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,2),(2,3)],[(0,1)],[(0,1),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)],[(0,1),(1,2),(2,3)],[(0,2),(1,3),(2,3)]]
def A_2 : BT (List (Nat × Nat)) := btOfList 4 al_2
set_option maxHeartbeats 0 in
lemma A_2_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_2 = g_2) A_2 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_2_0 : Slice r_2 g_2 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_1 : Slice r_2 g_2 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_2 : Slice r_2 g_2 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_3 : Slice r_2 g_2 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
def S_2 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4)]
lemma S_2_ok : btAll (fun o => ∀ p, o = some p → Slice r_2 g_2 p.1 p.2) S_2 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_2_0) (forall_cons (fun _ h => by cases h; exact sl_2_1) (forall_cons (fun _ h => by cases h; exact sl_2_2) (forall_cons (fun _ h => by cases h; exact sl_2_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_2 : BT (Option PoolSpec) := btOfList 2 ((([(1,[]),(0,[]),(2,[]),(3,[])] : List PoolSpec)).map some)
def B_2_2 : BT (List (List Nat)) := BT.empty
lemma B_2_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 2 xs.toFinset) B_2_2 := .empty
def P_2_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 [0,1]
def N_2_3 : List NodeSpec := [([4,5,6,3],[0,1],[]),([8,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_3 : checkNodesBT W_2 g_2 F_2 P_2_3 A_2 B_2_2 3 N_2_3 = true := by decide +kernel
def B_2_3 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_3
set_option maxRecDepth 500000 in
lemma B_2_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 3 xs.toFinset) B_2_3 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_2_ok C_2_3
def P_2_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 [0,2,3]
def N_2_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([10,0,1,2,3],[],[]),([11,0,1,2,3],[3],[9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_4 : checkNodesBT W_2 g_2 F_2 P_2_4 A_2 B_2_3 4 N_2_4 = true := by decide +kernel
def B_2_4 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_4
set_option maxRecDepth 500000 in
lemma B_2_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 4 xs.toFinset) B_2_4 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_3_ok C_2_4
def P_2_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 [0,1,2,3]
def N_2_5 : List NodeSpec := [([4,0,1,2,3],[0,1,2,3],[0,1,4,5,8,10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_5 : checkNodesBT W_2 g_2 F_2 P_2_5 A_2 B_2_4 5 N_2_5 = true := by decide +kernel
def B_2_5 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_5
set_option maxRecDepth 500000 in
lemma B_2_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 5 xs.toFinset) B_2_5 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_4_ok C_2_5
def P_2_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 [0,1,2,3]
def N_2_6 : List NodeSpec := [([0,1,2,3],[0,1,2,3],[0,2,3,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_6 : checkNodesBT W_2 g_2 F_2 P_2_6 A_2 B_2_5 6 N_2_6 = true := by decide +kernel
def B_2_6 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_6
set_option maxRecDepth 500000 in
lemma B_2_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 6 xs.toFinset) B_2_6 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_5_ok C_2_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_ok : forestRootCheck r_2 g_2 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_in : bucketContainsBT B_2_6 r_2 = true := by decide +kernel
lemma low_2 : Lower r_2 g_2 7 := lower_of_forestBT root_2_ok B_2_6_ok root_2_in
def g_3 := 0xfe80fe80fe80fe80fe80fe80fe80fe80fe80fe80fe80fe80fe80fe80fe80fe80
def r_3 : List Nat := varsOf 15
def p_3 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14]
def q_3 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6]
def F_3 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_3 : goodPairs g_3 p_3 q_3 := goodPairs_of (by decide +kernel)
def W_3 : BT Decor := buildWiresBT 5 (mkBase p_3 q_3 r_3) [(0,2,3),(1,2,3),(3,4,5),(0,1,2),(1,1,2),(3,7,8),(2,0,3),(3,0,3),(1,0,3),(3,2,12),(1,1,3),(0,0,14),(0,0,3),(1,16,2),(3,4,0),(2,0,2),(3,0,2),(2,2,1),(3,21,0),(2,0,1),(1,23,2),(0,0,1),(1,0,1),(3,2,3)]
lemma W_3_ok : btAll (fun x => faithful p_3 q_3 x ∧ x.1 < 2^256) W_3 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_3 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_3 : BT (List (Nat × Nat)) := btOfList 3 al_3
set_option maxHeartbeats 0 in
lemma A_3_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_3 = g_3) A_3 := btAll_ofList (autos_of (by decide +kernel))
def S_3 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_3_ok : btAll (fun o => ∀ p, o = some p → Slice r_3 g_3 p.1 p.2) S_3 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_3 : BT (Option PoolSpec) := btOfList 1 ((([] : List PoolSpec)).map some)
def B_3_1 : BT (List (List Nat)) := BT.empty
lemma B_3_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_3 1 xs.toFinset) B_3_1 := .empty
def P_3_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_3 r_3 S_3 ps_3 []
def N_3_2 : List NodeSpec := [([6,0,1],[],[]),([9,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_3_2 : checkNodesBT W_3 g_3 F_3 P_3_2 A_3 B_3_1 2 N_3_2 = true := by decide +kernel
def B_3_2 : BT (List (List Nat)) := buildBucketsBT W_3 N_3_2
set_option maxRecDepth 500000 in
lemma B_3_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_3 2 xs.toFinset) B_3_2 :=
  buildBucketsBT_sound (by decide) gp_3 W_3_ok (buildPoolsSubBT_sound S_3_ok) A_3_ok B_3_1_ok C_3_2
def P_3_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_3 r_3 S_3 ps_3 []
def N_3_3 : List NodeSpec := [([10,11,1,2],[],[3]),([13,0,1,3],[],[]),([15,1,2,3],[],[]),([16,1,2,12],[],[3]),([0,1,17,3],[],[]),([18,1,2,3],[],[]),([19,20,1,3],[],[2]),([22,1,2,3],[],[]),([0,1,24,3],[],[]),([25,26,2,3],[],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_3_3 : checkNodesBT W_3 g_3 F_3 P_3_3 A_3 B_3_2 3 N_3_3 = true := by decide +kernel
def B_3_3 : BT (List (List Nat)) := buildBucketsBT W_3 N_3_3
set_option maxRecDepth 500000 in
lemma B_3_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_3 3 xs.toFinset) B_3_3 :=
  buildBucketsBT_sound (by decide) gp_3 W_3_ok (buildPoolsSubBT_sound S_3_ok) A_3_ok B_3_2_ok C_3_3
def P_3_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_3 r_3 S_3 ps_3 []
def N_3_4 : List NodeSpec := [([27,0,1,2,3],[],[4]),([10,0,1,2,3],[],[0]),([0,1,2,3,12],[],[0,1,2,4]),([16,0,1,2,3],[],[0,1,3,5]),([19,0,1,2,3],[],[0,1,3]),([0,1,26,2,3],[],[0]),([25,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_3_4 : checkNodesBT W_3 g_3 F_3 P_3_4 A_3 B_3_3 4 N_3_4 = true := by decide +kernel
def B_3_4 : BT (List (List Nat)) := buildBucketsBT W_3 N_3_4
set_option maxRecDepth 500000 in
lemma B_3_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_3 4 xs.toFinset) B_3_4 :=
  buildBucketsBT_sound (by decide) gp_3 W_3_ok (buildPoolsSubBT_sound S_3_ok) A_3_ok B_3_3_ok C_3_4
def P_3_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_3 r_3 S_3 ps_3 []
def N_3_5 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_3_5 : checkNodesBT W_3 g_3 F_3 P_3_5 A_3 B_3_4 5 N_3_5 = true := by decide +kernel
def B_3_5 : BT (List (List Nat)) := buildBucketsBT W_3 N_3_5
set_option maxRecDepth 500000 in
lemma B_3_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_3 5 xs.toFinset) B_3_5 :=
  buildBucketsBT_sound (by decide) gp_3 W_3_ok (buildPoolsSubBT_sound S_3_ok) A_3_ok B_3_4_ok C_3_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_3_ok : forestRootCheck r_3 g_3 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_3_in : bucketContainsBT B_3_5 r_3 = true := by decide +kernel
lemma low_3 : Lower r_3 g_3 6 := lower_of_forestBT root_3_ok B_3_5_ok root_3_in
def g_4 := 0xe800e800e800e800e800e800e800e800e800e800e800e800e800e800e800e800
def r_4 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_4 : Lower r_4 g_4 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_5 := 0xfec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0
def r_5 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_5 : Lower r_5 g_5 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_6 := 0xfc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80
def r_6 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_6 : Lower r_6 g_6 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_7 := 0xfee8c000fee8c000fee8c000fee8c000fee8c000fee8c000fee8c000fee8c000
def r_7 : List Nat := varsOf 31
def p_7 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,22,22,22,23,25,25,25,26,26,26,27,28,28,28,29]
def q_7 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,20,18,6,7,24,17,9,24,18,10,11,24,20,12,13]
def F_7 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_7 : goodPairs g_7 p_7 q_7 := goodPairs_of (by decide +kernel)
def W_7 : BT Decor := buildWiresBT 3 (mkBase p_7 q_7 r_7) [(0,1,2),(1,1,2),(2,1,3)]
lemma W_7_ok : btAll (fun x => faithful p_7 q_7 x ∧ x.1 < 2^256) W_7 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_7 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)]]
def A_7 : BT (List (Nat × Nat)) := btOfList 3 al_7
set_option maxHeartbeats 0 in
lemma A_7_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_7 = g_7) A_7 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_7_0 : Slice r_7 g_7 (subcubeFast 0 16) 7 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_7_1 : Slice r_7 g_7 (subcubeFast 1 0) 7 := by
  have hc : Lower (varsOf 30) 0xfcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_2 : Slice r_7 g_7 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_3 : Slice r_7 g_7 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfaa00000faa00000faa00000faa00000faa00000faa00000faa00000faa00000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_4 : Slice r_7 g_7 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_5 : Slice r_7 g_7 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xee880000ee880000ee880000ee880000ee880000ee880000ee880000ee880000 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_6 : Slice r_7 g_7 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffeecc00ffeecc00ffeecc00ffeecc00ffeecc00ffeecc00ffeecc00ffeecc00 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_7 : Slice r_7 g_7 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xe8e80000e8e80000e8e80000e8e80000e8e80000e8e80000e8e80000e8e80000 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_8 : Slice r_7 g_7 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xfefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_9 : Slice r_7 g_7 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) 0xeecccc00eecccc00eecccc00eecccc00eecccc00eecccc00eecccc00eecccc00 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_10 : Slice r_7 g_7 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
def S_7 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 16,7),some (subcubeFast 1 0,7),some (subcubeFast 0 1,6),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (identDom 1 2,5),some (identDom 1 3,5)]
lemma S_7_ok : btAll (fun o => ∀ p, o = some p → Slice r_7 g_7 p.1 p.2) S_7 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_7_0) (forall_cons (fun _ h => by cases h; exact sl_7_1) (forall_cons (fun _ h => by cases h; exact sl_7_2) (forall_cons (fun _ h => by cases h; exact sl_7_3) (forall_cons (fun _ h => by cases h; exact sl_7_4) (forall_cons (fun _ h => by cases h; exact sl_7_5) (forall_cons (fun _ h => by cases h; exact sl_7_6) (forall_cons (fun _ h => by cases h; exact sl_7_7) (forall_cons (fun _ h => by cases h; exact sl_7_8) (forall_cons (fun _ h => by cases h; exact sl_7_9) (forall_cons (fun _ h => by cases h; exact sl_7_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_7 : BT (Option PoolSpec) := btOfList 5 ((([(1,[(0,1,2),(1,1,2)]),(3,[]),(0,[(0,1,2),(1,1,2)]),(9,[]),(4,[]),(1,[]),(1,[(2,1,3)]),(6,[]),(5,[]),(0,[]),(0,[(2,1,3)]),(10,[]),(7,[]),(8,[]),(1,[(1,1,2)]),(0,[(1,1,2)]),(1,[(0,1,2)]),(2,[]),(0,[(0,1,2)])] : List PoolSpec)).map some)
def B_7_5 : BT (List (List Nat)) := BT.empty
lemma B_7_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 5 xs.toFinset) B_7_5 := .empty
def P_7_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_7 r_7 S_7 ps_7 [0,1,2,3,4]
def N_7_6 : List NodeSpec := [([0,5,6,3,4],[0,1,2,3,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_6 : checkNodesBT W_7 g_7 F_7 P_7_6 A_7 B_7_5 6 N_7_6 = true := by decide +kernel
def B_7_6 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_6
set_option maxRecDepth 500000 in
lemma B_7_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 6 xs.toFinset) B_7_6 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_5_ok C_7_6
def P_7_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_7 r_7 S_7 ps_7 [1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]
def N_7_7 : List NodeSpec := [([7,0,1,2,3,4],[1,4,5,6,7,8,9,10,11,12,13],[]),([0,1,2,6,3,4],[1,4,7,8,12,13,14,15],[0]),([0,5,1,2,3,4],[1,4,5,8,12,13,16,17,18],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_7 : checkNodesBT W_7 g_7 F_7 P_7_7 A_7 B_7_6 7 N_7_7 = true := by decide +kernel
def B_7_7 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_7
set_option maxRecDepth 500000 in
lemma B_7_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 7 xs.toFinset) B_7_7 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_6_ok C_7_7
def P_7_8 : BT (Option BoundPool) := buildPoolsSubBT 5 W_7 r_7 S_7 ps_7 [5,9]
def N_7_8 : List NodeSpec := [([0,1,2,3,4],[5,9],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_8 : checkNodesBT W_7 g_7 F_7 P_7_8 A_7 B_7_7 8 N_7_8 = true := by decide +kernel
def B_7_8 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_8
set_option maxRecDepth 500000 in
lemma B_7_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 8 xs.toFinset) B_7_8 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_7_ok C_7_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_ok : forestRootCheck r_7 g_7 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_in : bucketContainsBT B_7_8 r_7 = true := by decide +kernel
lemma low_7 : Lower r_7 g_7 9 := lower_of_forestBT root_7_ok B_7_8_ok root_7_in
def g_8 := 0xfee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0
def r_8 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_9 := 0xfffefe80fffefe80fffefe80fffefe80fffefe80fffefe80fffefe80fffefe80
def r_9 : List Nat := varsOf 31
def p_9 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14,17,17,18,18,19,20,20,21,22,24,24]
def q_9 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6,16,1,16,2,3,16,4,5,6,16,8]
def F_9 : Nat := fullMask 23
set_option maxHeartbeats 0 in
lemma gp_9 : goodPairs g_9 p_9 q_9 := goodPairs_of (by decide +kernel)
def W_9 : BT Decor := buildWiresBT 7 (mkBase p_9 q_9 r_9) [(1,2,1),(1,1,3),(1,2,4),(0,6,7),(1,3,4),(3,2,9),(0,2,0),(1,10,11),(1,2,0),(1,13,3),(1,14,4),(3,2,15),(1,0,3),(1,17,4),(3,1,18),(0,2,9),(1,2,3),(1,21,4),(3,20,22),(0,0,1),(1,24,3),(1,25,4),(3,2,26),(1,1,13),(1,28,3),(2,29,4),(3,2,17),(1,0,4),(0,1,18),(1,13,4),(2,17,4),(3,3,32),(1,1,4),(0,17,37),(0,0,22),(1,0,1),(1,40,3),(1,41,4),(3,2,42),(3,1,9),(1,44,0),(2,45,2),(3,0,9),(2,6,4),(1,48,0),(1,6,4),(0,0,50),(2,0,9),(2,31,4),(1,10,0),(3,2,32),(1,55,3),(3,20,0),(3,2,6),(1,58,0),(3,5,9),(1,24,4),(2,28,4),(2,25,4),(0,1,2),(3,64,9),(2,2,3),(3,66,7),(0,0,9),(3,2,41),(1,40,4),(1,52,4),(2,41,4),(3,5,17),(2,0,4),(1,74,3)]
lemma W_9_ok : btAll (fun x => faithful p_9 q_9 x ∧ x.1 < 2^256) W_9 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_9 : List (List (Nat × Nat)) := [[],[(3,4)],[(1,2)],[(1,2),(3,4)],[(0,1)],[(0,1),(3,4)],[(0,2),(1,2)],[(0,2),(1,2),(3,4)],[(0,1),(1,2)],[(0,1),(1,2),(3,4)],[(0,2)],[(0,2),(3,4)]]
def A_9 : BT (List (Nat × Nat)) := btOfList 4 al_9
set_option maxHeartbeats 0 in
lemma A_9_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_9 = g_9) A_9 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_9_0 : Slice r_9 g_9 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) 0xfffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_1 : Slice r_9 g_9 (identDom 0 2) 7 := by
  have hc : Lower (varsOf 27) 0xffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_2 : Slice r_9 g_9 (identDom 1 2) 7 := by
  have hc : Lower (varsOf 27) 0xffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_3 : Slice r_9 g_9 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) 0xfefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_4 : Slice r_9 g_9 (subcubeFast 16 0) 6 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_9_5 : Slice r_9 g_9 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_6 : Slice r_9 g_9 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffafa00fffafa00fffafa00fffafa00fffafa00fffafa00fffafa00fffafa00 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_7 : Slice r_9 g_9 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffeeee00ffeeee00ffeeee00ffeeee00ffeeee00ffeeee00ffeeee00ffeeee00 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_8 : Slice r_9 g_9 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_9 : Slice r_9 g_9 (subcubeFast 5 0) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_10 : Slice r_9 g_9 (subcubeFast 6 0) 4 := by
  have hc : Lower (varsOf 25) 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 0) (by decide +kernel) hc
def S_9 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,7),some (identDom 0 2,7),some (identDom 1 2,7),some (subcubeFast 8 0,6),some (subcubeFast 16 0,6),some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 3 0,4),some (subcubeFast 5 0,4),some (subcubeFast 6 0,4)]
lemma S_9_ok : btAll (fun o => ∀ p, o = some p → Slice r_9 g_9 p.1 p.2) S_9 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_9_0) (forall_cons (fun _ h => by cases h; exact sl_9_1) (forall_cons (fun _ h => by cases h; exact sl_9_2) (forall_cons (fun _ h => by cases h; exact sl_9_3) (forall_cons (fun _ h => by cases h; exact sl_9_4) (forall_cons (fun _ h => by cases h; exact sl_9_5) (forall_cons (fun _ h => by cases h; exact sl_9_6) (forall_cons (fun _ h => by cases h; exact sl_9_7) (forall_cons (fun _ h => by cases h; exact sl_9_8) (forall_cons (fun _ h => by cases h; exact sl_9_9) (forall_cons (fun _ h => by cases h; exact sl_9_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_9 : BT (Option PoolSpec) := btOfList 7 ((([(3,[(0,2,9),(1,2,9),(3,20,22)]),(3,[]),(4,[]),(10,[]),(0,[]),(1,[]),(3,[(1,0,9),(3,2,18)]),(3,[(1,17,4),(3,2,18)]),(9,[]),(7,[]),(3,[(2,0,9),(3,0,9)]),(1,[(1,3,4),(3,2,9),(1,10,0)]),(3,[(1,0,4),(3,2,32)]),(3,[(1,2,4)]),(4,[(1,2,3)]),(3,[(0,2,9),(3,20,0)]),(1,[(1,3,4),(3,2,9)]),(2,[(1,3,4),(3,5,9)]),(0,[(1,24,4),(1,4,3)]),(5,[]),(6,[]),(0,[(1,2,0),(1,2,3)]),(1,[(1,1,13)]),(2,[(1,2,0)]),(0,[(1,24,3),(2,25,4)]),(0,[(1,24,3),(1,25,4)]),(0,[(1,0,4),(1,4,3)]),(1,[(1,0,4),(1,4,3)]),(1,[(1,13,3),(3,2,14)]),(4,[(1,0,3),(3,2,17)]),(2,[]),(0,[(1,3,4),(1,0,9)]),(1,[(1,3,4),(1,0,9)]),(0,[(1,3,4),(0,0,9)]),(1,[(1,3,4),(0,0,9)]),(3,[(0,0,9),(1,0,9)]),(1,[(1,2,3),(3,2,14)]),(3,[(3,2,9)]),(0,[(1,3,4)]),(1,[(1,3,4)]),(3,[(0,0,9)]),(3,[(2,17,4)]),(4,[(1,0,3)]),(0,[(1,0,3),(2,17,4)]),(1,[(1,0,3),(2,17,4)]),(3,[(1,17,4)]),(0,[(1,0,3)]),(1,[(1,0,3)]),(3,[(1,1,4)]),(0,[(1,1,4)]),(8,[]),(3,[(1,0,1)]),(3,[(1,0,4)]),(3,[(0,0,1)]),(0,[(1,24,3)]),(1,[(1,2,3)]),(3,[(1,2,0)]),(0,[(1,40,2)]),(1,[(1,0,1)]),(0,[(1,2,3)]),(1,[(1,0,1),(1,2,3)]),(2,[(1,0,1),(1,2,3)]),(2,[(1,0,1)]),(3,[(2,0,4)]),(4,[(1,74,3)]),(3,[(3,2,17)]),(3,[(1,0,9)]),(1,[(1,0,3),(3,2,17)]),(2,[(1,3,4),(3,2,9)]),(4,[(3,2,9)]),(3,[(2,0,9)]),(0,[(1,0,3),(1,17,4)]),(1,[(1,0,3),(1,17,4)]),(3,[(1,1,17)]),(4,[(1,0,1)]),(2,[(1,3,4)]),(4,[(0,0,1)])] : List PoolSpec)).map some)
def B_9_2 : BT (List (List Nat)) := BT.empty
lemma B_9_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 2 xs.toFinset) B_9_2 := .empty
def P_9_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_9 r_9 S_9 ps_9 []
def N_9_3 : List NodeSpec := [([0,5,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_3 : checkNodesBT W_9 g_9 F_9 P_9_3 A_9 B_9_2 3 N_9_3 = true := by decide +kernel
def B_9_3 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_3
set_option maxRecDepth 500000 in
lemma B_9_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 3 xs.toFinset) B_9_3 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_2_ok C_9_3
def P_9_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_9 r_9 S_9 ps_9 [0,1,2,3]
def N_9_4 : List NodeSpec := [([0,12,1,3,4],[],[]),([16,19,0,3,4],[],[]),([0,5,3,8,4],[],[0]),([23,0,1,3,4],[0],[]),([27,0,1,3,4],[],[]),([30,0,1,2,3],[],[]),([31,1,2,32,9],[],[]),([16,0,33,3,4],[],[]),([0,1,21,34,9],[1],[]),([35,36,0,1,2],[],[]),([0,1,2,38,9],[1,2],[8]),([10,39,1,3,4],[],[]),([16,0,1,3,4],[],[]),([0,5,6,7,9],[3],[0]),([43,0,1,3,4],[],[]),([46,0,1,3,4],[],[]),([35,47,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_4 : checkNodesBT W_9 g_9 F_9 P_9_4 A_9 B_9_3 4 N_9_4 = true := by decide +kernel
def B_9_4 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_4
set_option maxRecDepth 500000 in
lemma B_9_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 4 xs.toFinset) B_9_4 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_3_ok C_9_4
def P_9_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_9 r_9 S_9 ps_9 [1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
def N_9_5 : List NodeSpec := [([0,1,2,3,4,18],[4,5],[0,2]),([35,0,1,2,3,9],[1],[0]),([16,0,1,3,4,9],[6],[]),([0,49,1,2,3,4],[],[]),([16,0,1,3,17,4],[7],[]),([10,0,1,3,21,4],[1],[8]),([16,0,1,2,3,4],[],[]),([16,0,1,3,4],[],[]),([51,1,2,3,4,50],[8],[2,4,6]),([10,0,1,3,4,22],[4],[0,4,8,9]),([35,0,1,2,17,9],[1,2],[]),([10,0,1,3,7,9],[2,9],[]),([0,1,2,3,38,4],[1,2],[0,8]),([52,47,1,2,3,4],[10],[6]),([53,0,1,2,3,4],[],[]),([0,54,1,2,3,4],[4,11],[0,2]),([0,1,2,3,56,4],[12],[]),([0,5,3,6,4,7],[],[0]),([0,1,2,3,29,4],[2],[0]),([0,1,21,7,9],[1,2,9,13,14],[0,1,4,5,8,9,10,11]),([57,1,2,3,4,9],[15],[]),([31,1,13,3,17,4],[5],[]),([10,0,1,2,3,4],[],[]),([10,11,0,1,3,4],[16],[0]),([0,59,1,2,3,4],[4],[]),([60,0,1,2,3,4],[17],[]),([0,1,3,21,4,34],[1],[0]),([0,1,2,3,61,9],[1,18,19,20],[]),([0,1,28,3,21,4],[1,21,22,23],[]),([62,0,1,2,3,4],[],[]),([0,1,13,3,7,9],[8],[1,4]),([63,0,1,2,3,4],[24],[]),([0,1,2,17,37,9],[],[0,3,6,8]),([65,0,1,2,3,4],[],[]),([35,1,2,3,17,32],[2,19],[]),([0,1,13,3,4,22],[5,23],[]),([0,1,3,67,4,7],[2,9],[]),([0,1,2,3,4,26],[9,25],[0]),([68,1,2,3,32,9],[2,26,27],[]),([31,0,1,3,14,4],[4,8,28],[]),([69,0,1,2,3,4],[],[]),([31,0,1,2,4,9],[2,29],[0]),([0,1,2,3,70,9],[1],[2,6]),([0,1,2,3,71,9],[1,19],[]),([16,0,1,3,4,18],[5],[0]),([0,1,2,3,4,42],[5],[0,2,6]),([35,1,40,2,3,4],[20],[]),([72,0,1,2,3,4],[],[]),([31,0,1,5,3,4],[30],[]),([35,0,1,2,3,32],[2],[0]),([35,0,1,2,3,18],[4],[0]),([73,0,1,2,3,4],[],[]),([31,1,2,3,4,32],[],[0]),([68,1,2,3,4,18],[31,32,33,34,35],[6]),([0,1,2,17,32,9],[1,19],[]),([31,0,1,3,21,4],[1,36],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_5 : checkNodesBT W_9 g_9 F_9 P_9_5 A_9 B_9_4 5 N_9_5 = true := by decide +kernel
def B_9_5 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_5
set_option maxRecDepth 500000 in
lemma B_9_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 5 xs.toFinset) B_9_5 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_4_ok C_9_5
def P_9_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_9 r_9 S_9 ps_9 [1,2,3,4,5,8,9,13,14,16,19,20,21,23,26,27,29,30,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73]
def N_9_6 : List NodeSpec := [([10,0,1,2,3,4,9],[1,2,9,37],[0,1,8]),([68,0,1,2,3,4,9],[1,2,19,38,39,40],[0,1,6,10]),([35,0,1,2,3,4],[2,9,20,41,42,43,44],[0,2,4,8]),([0,1,2,3,17,4,18],[42,45,46,47],[0,1,2,6]),([0,1,2,3,17,4,37],[42,46,48,49],[0,2,3,6,7,8]),([0,1,2,3,41,4],[2,5,50,51],[0,1,2,3,6,7]),([0,1,2,3,32,9],[2,19,26,27,52],[0,1,2,3,6,10]),([24,0,1,2,3,4,9],[1,2,19,20,38,53],[0,1,2,6,8]),([0,1,2,3,17,4,32],[2,19,52],[0,1]),([0,1,2,3,25,4],[2,8,20,53,54],[0,1]),([0,1,13,3,21,4],[1,8,21,23,55,56],[0,1,5,8,10]),([0,1,2,28,3,4],[1,2,3,8,50,57,58],[0,1,2,3,6,7]),([0,1,40,2,3,21,4],[50,51,58,59,60,61,62],[0,8,10]),([74,1,2,3,17,4],[1,8,19,42,46,47,50,63],[7]),([0,1,2,3,75,4],[8,50,64],[]),([31,0,1,2,3,4],[1,2,5,8,29,30,65],[0,1,4]),([0,1,2,3,4,9,18],[19,38,39,66],[0,1,2,6]),([31,0,1,2,3,17,4],[1,47,65,67],[0]),([35,0,1,2,3,17,4],[2,19,41,42],[0]),([0,1,40,2,3,4,9],[1,2,19,20,38,50,51],[0,1,2,3,6,7,8]),([0,1,3,21,4,7],[9,13,14],[0,1,4,5,8,9,10,11]),([10,0,1,2,3,4],[1,2,5,16,30,37,68,69],[0,4,8]),([52,0,1,2,3,4,9],[19,70],[0,1]),([0,1,2,3,4,18],[4,5,42,45,71,72],[0,1,2,4,6,8,10]),([0,1,2,3,17,41,4],[46,50,73],[2,6])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_6 : checkNodesBT W_9 g_9 F_9 P_9_6 A_9 B_9_5 6 N_9_6 = true := by decide +kernel
def B_9_6 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_6
set_option maxRecDepth 500000 in
lemma B_9_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 6 xs.toFinset) B_9_6 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_5_ok C_9_6
def P_9_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_9 r_9 S_9 ps_9 [1,2,4,5,8,9,19,20,38,39,42,46,47,50,51,53,58,62,74,75,76]
def N_9_7 : List NodeSpec := [([74,0,1,2,3,4],[1,2,4,5,8,9,19,20,50],[0]),([0,1,2,3,17,4],[1,8,19,42,46,47,50],[0,1,2,6,10]),([0,1,40,2,3,4],[1,2,4,8,50,51,58,62,74],[0,1,2,3,6,7]),([0,1,2,3,4,9],[1,2,9,19,20,38,39,75],[0,1,2,4,5,6,8,9]),([24,0,1,2,3,4],[1,2,4,5,8,9,19,20,53,76],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_7 : checkNodesBT W_9 g_9 F_9 P_9_7 A_9 B_9_6 7 N_9_7 = true := by decide +kernel
def B_9_7 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_7
set_option maxRecDepth 500000 in
lemma B_9_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 7 xs.toFinset) B_9_7 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_6_ok C_9_7
def P_9_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_9 r_9 S_9 ps_9 [1,2,4,5,30]
def N_9_8 : List NodeSpec := [([0,1,2,3,4],[1,2,4,5,30],[0,1,2,4,5,6,8,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_8 : checkNodesBT W_9 g_9 F_9 P_9_8 A_9 B_9_7 8 N_9_8 = true := by decide +kernel
def B_9_8 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_8
set_option maxRecDepth 500000 in
lemma B_9_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 8 xs.toFinset) B_9_8 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_7_ok C_9_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_ok : forestRootCheck r_9 g_9 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_in : bucketContainsBT B_9_8 r_9 = true := by decide +kernel
lemma low_9 : Lower r_9 g_9 9 := lower_of_forestBT root_9_ok B_9_8_ok root_9_in
def g_10 := 0xf880f880f880f880f880f880f880f880f880f880f880f880f880f880f880f880
def r_10 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_10 : Lower r_10 g_10 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_11 := 0xfac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0
def r_11 : List Nat := varsOf 15
def p_11 : List Nat := [6,6,7,7,9,9,11,11,12,12,13,14]
def q_11 : List Nat := [4,2,5,3,8,1,10,3,8,4,5,10]
def F_11 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_11 : goodPairs g_11 p_11 q_11 := goodPairs_of (by decide +kernel)
def W_11 : BT Decor := buildWiresBT 2 (mkBase p_11 q_11 r_11) []
lemma W_11_ok : btAll (fun x => faithful p_11 q_11 x ∧ x.1 < 2^256) W_11 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_11 : List (List (Nat × Nat)) := [[]]
def A_11 : BT (List (Nat × Nat)) := btOfList 1 al_11
set_option maxHeartbeats 0 in
lemma A_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_11 = g_11) A_11 := btAll_ofList (autos_of (by decide +kernel))
def S_11 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_11_ok : btAll (fun o => ∀ p, o = some p → Slice r_11 g_11 p.1 p.2) S_11 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_11 : BT (Option PoolSpec) := btOfList 1 ((([] : List PoolSpec)).map some)
def B_11_2 : BT (List (List Nat)) := BT.empty
lemma B_11_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 2 xs.toFinset) B_11_2 := .empty
def P_11_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_11 r_11 S_11 ps_11 []
def N_11_3 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_3 : checkNodesBT W_11 g_11 F_11 P_11_3 A_11 B_11_2 3 N_11_3 = true := by decide +kernel
def B_11_3 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_3
set_option maxRecDepth 500000 in
lemma B_11_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 3 xs.toFinset) B_11_3 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_2_ok C_11_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck r_11 g_11 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT B_11_3 r_11 = true := by decide +kernel
lemma low_11 : Lower r_11 g_11 4 := lower_of_forestBT root_11_ok B_11_3_ok root_11_in
def g_12 := 0xfea8c000fea8c000fea8c000fea8c000fea8c000fea8c000fea8c000fea8c000
def r_12 : List Nat := varsOf 31
def p_12 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,23,23,25,25,25,26,26,26,27,28,28,28,29,30]
def q_12 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,22,7,24,17,9,24,18,10,11,24,20,12,13,22]
def F_12 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_12 : goodPairs g_12 p_12 q_12 := goodPairs_of (by decide +kernel)
def W_12 : BT Decor := buildWiresBT 8 (mkBase p_12 q_12 r_12) [(0,0,4),(1,1,2),(0,6,3),(1,5,7),(0,3,4),(0,2,4),(1,1,10),(2,11,3),(3,2,3),(0,11,3),(2,6,3),(0,1,2),(3,16,3),(0,0,3),(3,18,6),(1,2,4),(3,10,20),(1,0,7),(0,22,4),(2,0,3),(1,24,1),(0,1,4),(1,26,2),(2,6,9),(0,7,4),(0,27,3),(2,0,30),(1,5,2),(0,6,4),(1,5,1),(1,34,2),(0,35,3),(3,0,4),(1,37,7),(1,24,16),(3,6,3),(3,40,4),(2,0,7),(3,33,3),(1,3,4),(3,9,44),(0,3,20),(2,0,46),(1,1,4),(0,3,48),(0,0,49),(1,1,3),(3,2,51),(1,2,3),(3,1,53),(3,54,4),(0,1,3),(1,13,1),(0,2,3),(1,58,1),(3,6,4),(3,60,3),(1,13,10),(0,57,4),(3,7,4),(3,3,4),(3,65,6),(3,1,3),(3,58,6),(3,10,51),(0,0,6),(2,2,1),(1,71,13),(3,67,4),(2,34,2),(3,24,6),(0,25,4),(2,0,2),(1,77,26),(3,2,48),(0,1,20),(3,18,48),(2,1,2),(1,82,18),(1,18,26),(3,10,1),(1,77,1),(0,86,4),(1,18,1),(0,88,4),(2,1,4),(1,24,82),(1,18,2),(1,90,18),(1,18,16),(1,24,26),(3,24,48),(0,53,4),(1,90,24),(3,1,4),(0,0,11),(3,5,6),(1,13,26),(1,1,9),(3,2,9),(2,3,4),(3,105,0),(3,2,44),(0,0,44),(1,65,1),(3,2,4),(2,2,4),(3,111,0),(3,13,4),(3,111,3),(2,2,3),(1,115,1),(0,51,4),(2,0,1),(3,118,4),(0,1,44),(3,18,4),(2,0,58),(3,24,4),(3,13,1),(0,0,2),(1,125,1),(2,1,3),(1,127,2),(3,3,48),(3,115,1),(3,10,3),(0,0,48),(3,71,3),(0,0,1),(2,0,4)]
lemma W_12_ok : btAll (fun x => faithful p_12 q_12 x ∧ x.1 < 2^256) W_12 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_12 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_12 : BT (List (Nat × Nat)) := btOfList 1 al_12
set_option maxHeartbeats 0 in
lemma A_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_12 = g_12) A_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_12_0 : Slice r_12 g_12 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_1 : Slice r_12 g_12 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfaa00000faa00000faa00000faa00000faa00000faa00000faa00000faa00000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_2 : Slice r_12 g_12 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfc00c000fc00c000fc00c000fc00c000fc00c000fc00c000fc00c000fc00c000 5 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_3 : Slice r_12 g_12 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xee880000ee880000ee880000ee880000ee880000ee880000ee880000ee880000 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_4 : Slice r_12 g_12 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xfefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_5 : Slice r_12 g_12 (subcubeFast 0 16) 5 := by
  have hc : Lower (varsOf 15) 0xfea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8fea8 5 := carry_of (swaps := [(0,2),(1,2)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_6 : Slice r_12 g_12 (subcubeFast 4 16) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_7 : Slice r_12 g_12 (subcubeFast 2 16) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_8 : Slice r_12 g_12 (subcubeFast 1 8) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_9 : Slice r_12 g_12 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) 0xee88cc00ee88cc00ee88cc00ee88cc00ee88cc00ee88cc00ee88cc00ee88cc00 5 := carry_of (swaps := [(1,2),(2,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_10 : Slice r_12 g_12 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_11 : Slice r_12 g_12 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) 0xf8f8c0c0f8f8c0c0f8f8c0c0f8f8c0c0f8f8c0c0f8f8c0c0f8f8c0c0f8f8c0c0 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_12 : Slice r_12 g_12 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 27) 0xffaacc00ffaacc00ffaacc00ffaacc00ffaacc00ffaacc00ffaacc00ffaacc00 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_13 : Slice r_12 g_12 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 29) 0xffaaf000ffaaf000ffaaf000ffaaf000ffaaf000ffaaf000ffaaf000ffaaf000 4 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
def S_12 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 4 16,4),some (subcubeFast 2 16,4),some (subcubeFast 1 8,4),some (identDom 1 2,5),some (identDom 1 3,5),some (identDom 2 3,5),some (subcubeFast 0 4,4),some (subcubeFast 0 2,4)]
lemma S_12_ok : btAll (fun o => ∀ p, o = some p → Slice r_12 g_12 p.1 p.2) S_12 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_12_0) (forall_cons (fun _ h => by cases h; exact sl_12_1) (forall_cons (fun _ h => by cases h; exact sl_12_2) (forall_cons (fun _ h => by cases h; exact sl_12_3) (forall_cons (fun _ h => by cases h; exact sl_12_4) (forall_cons (fun _ h => by cases h; exact sl_12_5) (forall_cons (fun _ h => by cases h; exact sl_12_6) (forall_cons (fun _ h => by cases h; exact sl_12_7) (forall_cons (fun _ h => by cases h; exact sl_12_8) (forall_cons (fun _ h => by cases h; exact sl_12_9) (forall_cons (fun _ h => by cases h; exact sl_12_10) (forall_cons (fun _ h => by cases h; exact sl_12_11) (forall_cons (fun _ h => by cases h; exact sl_12_12) (forall_cons (fun _ h => by cases h; exact sl_12_13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
def ps_12 : BT (Option PoolSpec) := btOfList 7 ((([(0,[(0,2,4),(1,2,4),(3,10,20)]),(0,[]),(1,[(0,0,4),(0,6,4)]),(9,[(0,6,3),(2,0,7)]),(8,[]),(7,[]),(6,[]),(0,[(1,2,4),(0,3,20)]),(10,[]),(1,[(0,3,48)]),(0,[(1,1,4),(0,3,48)]),(2,[]),(3,[]),(1,[(0,2,4)]),(5,[]),(13,[]),(1,[]),(0,[(3,2,3),(1,13,1)]),(0,[(0,1,4),(1,26,2)]),(3,[(0,1,4)]),(12,[]),(4,[]),(11,[]),(9,[]),(9,[(2,6,3)]),(0,[(0,1,2),(1,1,2)]),(9,[(0,6,3)]),(9,[(0,0,6)]),(1,[(0,6,4)]),(5,[(1,2,1)]),(5,[(1,1,2)]),(9,[(2,0,3)]),(0,[(0,1,4),(1,1,4)]),(0,[(0,1,4),(1,77,26)]),(0,[(1,1,4),(3,2,48)]),(3,[(0,1,20)]),(0,[(1,2,4),(0,1,20)]),(0,[(1,1,4),(3,18,48)]),(0,[(2,1,2),(1,82,18)]),(0,[(0,1,4),(1,18,26)]),(0,[(0,2,4),(3,10,1)]),(9,[(0,0,3)]),(0,[(1,1,4),(3,24,48)]),(0,[(2,1,4),(3,1,4)]),(0,[(0,2,4),(1,10,1)]),(1,[(0,0,4)]),(4,[(0,0,4)]),(1,[(3,0,4)]),(4,[(3,0,4)]),(0,[(0,3,4),(1,1,9)]),(1,[(3,2,4)]),(3,[(3,13,4)]),(2,[(3,2,3)]),(0,[(1,1,4)]),(0,[(3,2,3)]),(0,[(0,3,4)]),(3,[(0,0,4)]),(1,[(3,118,4)]),(0,[(3,118,4)]),(0,[(0,1,2)]),(2,[(0,3,4)]),(0,[(2,1,4)]),(0,[(0,1,4)]),(0,[(1,1,2)]),(0,[(3,18,4)]),(0,[(3,24,4)]),(0,[(0,2,3)]),(0,[(0,1,3)]),(0,[(3,1,4)]),(0,[(2,1,2)]),(0,[(1,18,1)]),(0,[(1,5,1)]),(0,[(3,2,4)]),(0,[(3,3,4)]),(3,[(3,0,4)]),(0,[(1,1,3)]),(0,[(1,125,1)]),(2,[(3,1,3)]),(1,[(3,2,48)]),(1,[(3,3,48)]),(0,[(1,1,4),(3,3,48)]),(2,[(0,1,3)]),(0,[(0,2,4),(3,10,3)]),(0,[(1,24,1)]),(1,[(0,0,48)]),(0,[(2,2,1),(3,71,3)]),(0,[(1,77,1)])] : List PoolSpec)).map some)
def B_12_2 : BT (List (List Nat)) := BT.empty
lemma B_12_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 2 xs.toFinset) B_12_2 := .empty
def P_12_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 []
def N_12_3 : List NodeSpec := [([1,2,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_3 : checkNodesBT W_12 g_12 F_12 P_12_3 A_12 B_12_2 3 N_12_3 = true := by decide +kernel
def B_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_3
set_option maxRecDepth 500000 in
lemma B_12_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 3 xs.toFinset) B_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_2_ok C_12_3
def P_12_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 [0,1,2,3]
def N_12_4 : List NodeSpec := [([12,13,0,11,4],[],[]),([13,0,14,11,4],[],[]),([15,17,0,6,4],[],[]),([19,0,16,3,4],[],[]),([21,18,0,1,3],[0],[]),([1,2,7,23,3],[],[]),([0,25,27,3,4],[],[]),([28,5,1,2,3],[],[]),([5,1,2,29,3],[1],[]),([31,1,27,3,4],[],[]),([17,0,7,6,4],[],[]),([5,1,32,33,3],[2],[]),([24,21,0,1,3],[0],[]),([5,1,2,36,4],[],[]),([1,2,38,3,4],[],[]),([0,39,6,3,4],[],[]),([13,5,1,33,3],[2],[]),([1,2,8,3,4],[1],[0]),([5,1,2,7,9],[],[0]),([5,1,2,41,3],[],[]),([42,16,6,3,4],[3],[]),([43,5,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_4 : checkNodesBT W_12 g_12 F_12 P_12_4 A_12 B_12_3 4 N_12_4 = true := by decide +kernel
def B_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_4
set_option maxRecDepth 500000 in
lemma B_12_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 4 xs.toFinset) B_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_3_ok C_12_4
def P_12_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48]
def N_12_5 : List NodeSpec := [([45,0,1,2],[4,5,6],[]),([47,0,1,2,46,4],[7],[]),([50,0,1,2,49,4],[8,9,10],[]),([0,1,2,14,3,4],[1,8,11,12],[]),([13,0,11,3,4],[5,6,12,13],[0]),([52,0,1,10,3,4],[14,15],[]),([0,1,55,2,3,4],[16],[]),([0,56,57,2,3,4],[16,17],[]),([0,56,2,59,3,4],[16],[]),([0,1,30,27,3,4],[16,18,19,20],[0,1]),([0,1,2,61,3,4],[1,11],[]),([0,1,2,33,9,3],[5,6,15,20,21],[]),([43,0,1,2,3,4],[],[0]),([0,1,2,41,3,4],[],[0]),([0,1,2,7,3,4],[1,11],[]),([13,0,1,3,62,4],[12],[]),([0,1,63,2,3,4],[16],[]),([42,1,2,6,3,4],[],[0]),([0,1,2,7,9,4],[8,14,22],[0]),([64,0,1,2,3,4],[1,11],[]),([42,1,2,7,3,4],[1],[]),([1,2,7,22,3,4],[11],[0]),([0,1,2,66,3,4],[1,11],[]),([13,67,0,6,3,4],[12,16,21],[]),([0,56,58,6,3,4],[16,21],[]),([68,0,1,6,3,4],[12,16],[]),([69,0,1,2,3,4],[16],[]),([15,0,16,6,3,4],[16,20,23,24],[0]),([0,16,7,6,3,4],[16,20,23,25,26],[0]),([70,0,16,6,3,4],[25,27],[]),([13,0,1,33,3,4],[6,12,28,29],[0]),([17,0,6,3,4],[6,16,23,30],[0]),([12,0,2,11,3,4],[5,12,15],[0]),([13,72,0,1,3,4],[12],[]),([24,0,16,6,3,4],[16,25,31],[0]),([0,1,73,2,9,3],[8,21],[]),([74,5,1,2,3,4],[],[]),([0,1,2,75,3,4],[11],[]),([0,1,76,2,3,4],[],[]),([0,39,1,2,3,4],[],[0]),([40,5,1,2,3,4],[14],[0]),([24,0,1,2,7,4],[1],[]),([18,0,26,2,3,48],[32],[1]),([65,0,1,2,7,4],[],[]),([0,1,78,2,3,4],[33],[]),([18,0,1,2,49,4],[1,8,9],[]),([0,26,25,2,3,4],[],[0]),([24,0,1,2,49,4],[1],[]),([79,18,0,1,3,4],[34],[]),([18,0,80,2,3,4],[20,35,36],[]),([81,0,1,2,3,4],[1,37],[]),([0,83,1,2,3,4],[38],[]),([82,0,25,2,3,4],[],[]),([0,1,84,2,3,4],[39],[]),([85,18,0,2,3,4],[40],[]),([5,0,1,2,33,3],[1,6,15,20],[]),([0,26,86,2,3,4],[20],[]),([0,1,87,2,3,4],[16],[]),([0,1,89,2,3,4],[11,12,15,20],[]),([18,0,1,2,7,4],[1],[]),([90,0,88,2,3,4],[11],[]),([91,0,1,2,3,4],[],[]),([18,0,16,6,3,4],[20,25,41],[0]),([45,0,1,2,9],[4,5,6,21],[]),([24,79,0,1,3,4],[34],[]),([21,0,1,3],[0,5,6],[0]),([0,16,1,92,3,4],[20],[]),([5,1,2,33,6,3],[2,6],[]),([52,37,1,2,3,4],[],[]),([13,0,1,11,3,4],[13,21],[]),([18,0,1,27,3,4],[18],[]),([93,0,1,2,3,4],[1],[]),([0,1,94,2,3,4],[],[]),([19,0,1,2,3,4],[],[0]),([24,0,80,2,3,4],[36],[]),([0,1,95,2,3,4],[],[]),([0,1,2,3,96,4],[42],[]),([24,0,1,27,3,4],[16,18],[0]),([0,26,1,2,3,97],[6,15,20],[]),([37,1,2,7,3,4],[1],[0]),([24,0,26,2,3,48],[32],[1]),([0,1,2,29,3,4],[1,11,12,16],[0]),([13,0,56,6,3,4],[16,21],[]),([98,0,1,2,3,4],[1],[]),([90,24,99,0,2,3],[43],[1]),([100,0,2,11,3,4],[44],[]),([5,1,32,6,3,4],[11,45],[0]),([5,1,2,7,3,4],[11,14],[0]),([5,1,2,35,3,4],[1,14,46],[0]),([5,1,2,33,3],[1,5,6],[0,1]),([101,5,1,2,3,4],[1,14],[]),([13,5,1,6,3,4],[45,46],[0]),([0,26,57,2,3,4],[20],[]),([28,0,1,2,3,4],[],[0]),([90,99,18,0,2,3],[43],[1]),([5,1,2,6,9,3],[5,6,46],[0]),([0,1,102,2,3,4],[16],[]),([5,1,57,2,3,4],[],[]),([5,1,2,9,3,103],[5],[]),([37,1,57,2,3,4],[],[]),([104,5,1,2,9,3],[6],[]),([24,85,0,2,3,4],[40],[]),([101,0,1,2,3,4],[11],[]),([13,37,1,6,3,4],[47,48],[]),([40,37,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_5 : checkNodesBT W_12 g_12 F_12 P_12_5 A_12 B_12_4 5 N_12_5 = true := by decide +kernel
def B_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_5
set_option maxRecDepth 500000 in
lemma B_12_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 5 xs.toFinset) B_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_4_ok C_12_5
def P_12_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 [1,4,5,6,8,9,10,11,12,13,14,15,16,17,18,20,21,22,23,25,28,29,31,32,34,35,36,40,41,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86]
def N_12_6 : List NodeSpec := [([106,1,2,3,4],[1,5,6,11],[]),([107,0,1,3,4],[5,6,21],[]),([108,1,2,3,4],[1,6,11,21],[]),([104,0,1,2,9,3,4],[6,12,22],[0,1]),([0,1,109,2,3,4],[4,5,12,15,20],[]),([0,1,2,3,103,4],[5,11,12,15,20,49],[]),([90,99,0,2,3],[5,6,16,43],[0,1]),([0,1,2,49,3,4],[1,5,6,10,11,14,16],[0]),([0,1,2,49,4],[5,6,9,10],[0,1]),([85,0,2,3,4],[6,12,16,40],[0]),([0,1,2,11,3,4],[5,11,12,15,21,44],[0]),([13,0,1,2,9,3,4],[4,6,22],[1]),([13,110,0,1,3,4],[6,12,14,20,21,50],[]),([112,1,2,3,4],[1,5,11,12],[]),([13,67,0,1,2,3,4],[8,12,16,21,22],[0]),([13,0,1,2,113,3,4],[12,14,20,21,22,51],[]),([104,0,1,2,3,4],[1,6,11,15,16,22],[]),([13,0,1,57,2,3,4],[12,16,20,22],[]),([0,1,57,2,3,4],[8,11,12,14,15,16,17,20],[0]),([0,1,2,9,44],[4,5,6],[0]),([0,1,2,9,3,103,4],[5,8],[0]),([0,1,2,114,3,4],[1,5,11,12,14],[]),([0,1,116,2,3,4],[4,6],[]),([0,1,2,3,117,4],[1,4,5,11,12,20],[1]),([13,0,1,10,3,4],[6,12,13,14,21,52],[0]),([110,0,1,2,3,51,4],[5,6,20,21],[]),([24,0,1,2,3,4,48],[11,14,21,53],[0,1]),([13,0,56,1,2,3,4],[4,8,12,16,22,54],[0]),([5,1,2,9,3,4],[1,4,5,6,11,45,55,56],[]),([0,1,119,2,3,4],[1,4,5,11,12,20,57,58],[]),([24,0,16,1,2,3,4],[1,11,16,59],[0]),([13,99,0,1,2,3,4],[5,6,8,12,15,20],[]),([5,1,2,9,3],[4,5,6,60],[0,1]),([90,18,0,1,2,3,4],[1,11,16,61],[0]),([0,120,2,3,4],[6,16,21],[]),([105,5,1,2,3],[4,6,14],[]),([13,5,1,2,3,4],[4,6,11,45,56],[0]),([52,0,1,2,3,4],[1,4,11,12,14,15,16,20],[0,1]),([77,0,26,1,2,3,4],[6,11,12,16,20,62],[0]),([37,1,2,6,3,4],[5,6,47,48,63],[0,1]),([5,1,2,3,4],[1,4,5,6,11],[]),([121,0,1,2,3,4],[1,4,11,12,15,16,20,21,64],[]),([0,56,2,51,4],[4,5,8,16],[]),([122,1,2,3,4],[4,6,11],[]),([0,1,2,3,123,4],[11,12,15,16,20,21,65],[]),([24,0,1,2,6,3,4],[1,11,12,15,16,20,21,63],[0]),([0,56,1,58,2,3,4],[4,12,16,66,67],[0,1]),([0,1,27,3,4],[5,6,16,18,20],[0,1]),([77,99,0,1,2,3,4],[5,6,11,15,68],[]),([13,0,26,1,2,3,4],[6,12,16,20,22],[0]),([82,18,0,1,2,3,4],[11,12,16,20,41,69],[0]),([0,1,88,2,3,4],[4,11,12,14,15,20,70],[0,1]),([5,1,34,2,3,4],[4,5,11,45,56,71],[0,1]),([24,0,26,1,2,3,4],[1,11,16,62],[0,1]),([90,24,0,1,2,3,4],[1,11,16,61],[0]),([110,18,0,1,2,3,4],[6,11,20,72],[1]),([13,0,124,1,2,3,4],[12,15,16,20,21,22],[]),([24,110,0,1,2,3,4],[1,6,11,20,72],[1]),([105,65,0,1,2],[5,6,14,21],[0]),([65,37,1,2,3,4],[1,5,6,47,48,73,74],[]),([18,0,1,2,6,3,4],[1,11,20,21,63],[0]),([18,0,26,1,2,3,4],[11,16,62],[0,1]),([37,1,2,3,51,4],[1,5,48,74,75],[0]),([18,0,16,1,2,3,4],[11,12,16,59],[0,1]),([17,0,1,2,3,4],[1,6,11,12,16],[0]),([0,1,2,59,3,4],[1,6,8,11,16],[0]),([18,0,1,2,3,4,48],[11,15,16,21,53],[0,1]),([5,1,2,6,3,4],[5,6,11,46,63],[0,1]),([0,1,2,9,3,4],[1,4,5,6,11,12,14,16],[]),([0,26,1,2,3,53,4],[6,12,16,20],[0,1]),([24,82,0,1,2,3,4],[1,11,16,31,69],[0]),([0,1,126,2,3,4],[4,6,11,12,76],[]),([0,1,128,3,4],[4,5,16],[]),([82,67,0,2,3,4],[5,12,15,16,21,77],[1]),([0,1,34,2,3,4],[4,5,11,12,15,20,71],[]),([5,0,1,2,6,3,4],[1,6,11,12,15,16,20,63],[0]),([79,0,1,3,4],[5,6,34,78],[0]),([13,37,1,2,3,4],[1,6,47,48,54,74],[0]),([129,0,1,2,4],[5,6,21,79,80],[]),([0,80,2,3,4],[6,16,35,36],[0]),([37,1,2,9,3,4],[1,4,5,6,47,55,74],[]),([0,1,2,33,6,3,4],[5,6,16,20,28],[0]),([0,130,2,3,4],[6,12,16,21],[]),([0,16,6,3,4],[6,16,20,23,25],[0]),([70,0,1,2,6,3,4],[1,11,63],[0]),([0,1,2,7,3,4],[1,11,12,14,15,16,20],[0]),([0,1,73,2,3,4],[1,5,8,11,12,20],[0]),([0,56,2,6,3,4],[5,12,15,16,21,81],[0,1]),([131,0,1,2,3,4],[1,6,11,12,15,16,82],[]),([60,0,1,2,3,4],[1,5,6,8,11,15,20,21],[0]),([0,1,25,2,3,4],[11,12,14,15,20,21,83],[0]),([13,0,1,6,3,4],[6,12,16,20,21,29,52],[0]),([0,1,2,7,6,3,4],[12,15,16,20,21,63],[0]),([15,0,1,2,6,3,4],[12,15,16,20],[0]),([132,1,2,3,4],[1,5,6,11,84],[]),([0,1,2,33,3,4],[1,5,6,11,20,21,28],[0,1]),([40,0,1,2,3,4],[1,8,11,14,15,20],[0]),([0,1,2,6,9,3,4],[5,6,15,16,20,21],[0]),([65,0,1,2,6,3,4],[5,6,12,15,16,20,21],[0]),([0,1,2,6,3,4],[1,6,11,15,16,20,21],[0]),([0,26,2,3,48],[6,16,32],[0,1]),([0,1,133,2,3,4],[1,6,11,15,16,85],[]),([0,1,86,2,3,4],[4,11,14,15,16,20,86],[0]),([13,0,1,2,3,4],[1,4,6,11,12,15,16,20,21],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_6 : checkNodesBT W_12 g_12 F_12 P_12_6 A_12 B_12_5 6 N_12_6 = true := by decide +kernel
def B_12_6 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_6
set_option maxRecDepth 500000 in
lemma B_12_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 6 xs.toFinset) B_12_6 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_5_ok C_12_6
def P_12_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 [1,4,5,6,8,11,12,14,15,16,20,21,22,23,53,54,55,59,61,62,63,67,69,72,73,75]
def N_12_7 : List NodeSpec := [([65,0,1,2,3,4],[1,4,5,6,11,12,16,21,73],[0,1]),([0,1,2,3,4,44],[1,5,6,11,21],[0,1]),([110,0,1,2,3,4],[1,5,6,11,16,21,72],[0,1]),([0,1,2,9,3,4],[4,5,6,55],[0,1]),([90,0,1,2,3,4],[1,6,11,16,21,61],[0,1]),([0,26,1,2,3,4],[1,5,6,11,16,21,62],[0,1]),([127,0,1,2,3,4],[1,4,5,8,11,12,14,16,21],[0,1]),([134,0,1,2,3,4],[1,4,5,12,14,16,21],[1]),([5,1,2,3,4],[1,4,5,6,11],[0,1]),([105,0,1,2,3,4],[1,4,5,6,11,14],[0]),([77,0,1,2,3,4],[1,4,6,11,12,14,16,20,21],[0,1]),([18,0,1,2,3,4],[1,4,11,12,14,16],[0,1]),([24,0,1,2,3,4],[1,11,12,14,16,21],[0,1]),([135,0,1,2,3,4],[1,4,5,6,11,21],[0]),([0,1,2,3,4,48],[1,5,6,11,16,21,53],[0,1]),([13,0,1,2,3,4],[1,4,6,11,12,14,16,20,22,54],[0,1]),([82,0,1,2,3,4],[1,5,11,12,14,16,20,21,23,69],[0,1]),([37,1,2,3,4],[1,5,6],[0,1]),([0,1,2,3,51,4],[4,5,12,15,16,75],[0,1]),([5,0,1,2,3,4],[1,4,5,6,11,12,16,21],[0,1]),([0,16,1,2,3,4],[1,6,11,12,16,21,59],[0]),([0,1,2,6,3,4],[5,6,11,12,15,16,20,21,63],[0,1]),([0,56,1,2,3,4],[1,4,5,11,12,16,67],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_7 : checkNodesBT W_12 g_12 F_12 P_12_7 A_12 B_12_6 7 N_12_7 = true := by decide +kernel
def B_12_7 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_7
set_option maxRecDepth 500000 in
lemma B_12_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 7 xs.toFinset) B_12_7 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_6_ok C_12_7
def P_12_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 [1]
def N_12_8 : List NodeSpec := [([0,1,2,3,4],[1],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_8 : checkNodesBT W_12 g_12 F_12 P_12_8 A_12 B_12_7 8 N_12_8 = true := by decide +kernel
def B_12_8 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_8
set_option maxRecDepth 500000 in
lemma B_12_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 8 xs.toFinset) B_12_8 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_7_ok C_12_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck r_12 g_12 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT B_12_8 r_12 = true := by decide +kernel
lemma low_12 : Lower r_12 g_12 9 := lower_of_forestBT root_12_ok B_12_8_ok root_12_in
def g_13 := 0xfeeac000feeac000feeac000feeac000feeac000feeac000feeac000feeac000
def r_13 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_13 : Lower r_13 g_13 8 := by
  have hc : Lower (varsOf 30) 0xfcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_14 := 0xfffefec0fffefec0fffefec0fffefec0fffefec0fffefec0fffefec0fffefec0
def r_14 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 8 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_15 := 0xffc8e080ffc8e080ffc8e080ffc8e080ffc8e080ffc8e080ffc8e080ffc8e080
def r_15 : List Nat := varsOf 31
def p_15 : List Nat := [7,7,7,13,13,13,14,14,14,15,19,19,19,22,22,22,23,24,24,25,25,26,26,27,28,28,29]
def q_15 : List Nat := [6,5,3,12,9,5,12,10,6,11,18,17,3,20,18,6,21,16,8,17,9,18,10,11,20,12,21]
def F_15 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_15 : goodPairs g_15 p_15 q_15 := goodPairs_of (by decide +kernel)
def W_15 : BT Decor := buildWiresBT 4 (mkBase p_15 q_15 r_15) [(1,3,4),(3,0,5),(1,0,3),(2,7,4),(1,7,4),(1,0,4),(0,1,2)]
lemma W_15_ok : btAll (fun x => faithful p_15 q_15 x ∧ x.1 < 2^256) W_15 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_15 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_15 : BT (List (Nat × Nat)) := btOfList 1 al_15
set_option maxHeartbeats 0 in
lemma A_15_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_15 = g_15) A_15 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_15_0 : Slice r_15 g_15 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0fffaf0a0 5 := carry_of (swaps := [(1,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_1 : Slice r_15 g_15 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffccee88ffccee88ffccee88ffccee88ffccee88ffccee88ffccee88ffccee88 5 := carry_of (swaps := [(1,2),(2,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_2 : Slice r_15 g_15 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xc8c88080c8c88080c8c88080c8c88080c8c88080c8c88080c8c88080c8c88080 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_3 : Slice r_15 g_15 (subcubeFast 16 0) 5 := by
  have hc : Lower (varsOf 15) 0xe080e080e080e080e080e080e080e080e080e080e080e080e080e080e080e080 5 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_4 : Slice r_15 g_15 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xffc0c000ffc0c000ffc0c000ffc0c000ffc0c000ffc0c000ffc0c000ffc0c000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_5 : Slice r_15 g_15 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_6 : Slice r_15 g_15 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_7 : Slice r_15 g_15 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_8 : Slice r_15 g_15 (subcubeFast 16 4) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_9 : Slice r_15 g_15 (identDom 1 4) 6 := by
  have hc : Lower (varsOf 15) 0xecc8ecc8ecc8ecc8ecc8ecc8ecc8ecc8ecc8ecc8ecc8ecc8ecc8ecc8ecc8ecc8 6 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_3
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_10 : Slice r_15 g_15 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) 0xf8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_15 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 1 0,5),some (subcubeFast 8 2,4),some (subcubeFast 1 2,4),some (subcubeFast 1 4,4),some (subcubeFast 16 4,4),some (identDom 1 4,6),some (identDom 2 3,6)]
lemma S_15_ok : btAll (fun o => ∀ p, o = some p → Slice r_15 g_15 p.1 p.2) S_15 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_15_0) (forall_cons (fun _ h => by cases h; exact sl_15_1) (forall_cons (fun _ h => by cases h; exact sl_15_2) (forall_cons (fun _ h => by cases h; exact sl_15_3) (forall_cons (fun _ h => by cases h; exact sl_15_4) (forall_cons (fun _ h => by cases h; exact sl_15_5) (forall_cons (fun _ h => by cases h; exact sl_15_6) (forall_cons (fun _ h => by cases h; exact sl_15_7) (forall_cons (fun _ h => by cases h; exact sl_15_8) (forall_cons (fun _ h => by cases h; exact sl_15_9) (forall_cons (fun _ h => by cases h; exact sl_15_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_15 : BT (Option PoolSpec) := btOfList 4 ((([(9,[]),(0,[]),(10,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(8,[]),(6,[]),(0,[(1,0,3)]),(7,[])] : List PoolSpec)).map some)
def B_15_4 : BT (List (List Nat)) := BT.empty
lemma B_15_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 4 xs.toFinset) B_15_4 := .empty
def P_15_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_15 r_15 S_15 ps_15 [0,1,2,3,4,5]
def N_15_5 : List NodeSpec := [([6,0,1,2,3,4],[],[]),([8,0,1,2,3,4],[],[]),([0,1,2,3,4,9],[0,1,2,3],[]),([1,2,3,7,4,10],[4,5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_5 : checkNodesBT W_15 g_15 F_15 P_15_5 A_15 B_15_4 5 N_15_5 = true := by decide +kernel
def B_15_5 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_5
set_option maxRecDepth 500000 in
lemma B_15_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 5 xs.toFinset) B_15_5 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_4_ok C_15_5
def P_15_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_15 r_15 S_15 ps_15 [3,4,5,6,7,8,9,10,11]
def N_15_6 : List NodeSpec := [([0,1,2,3,4,5],[6,7,8],[0]),([0,11,1,2,3,4],[3,4,5,6,7,8,9],[]),([0,1,2,3,7,4],[4,5,6,7,10,11],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_6 : checkNodesBT W_15 g_15 F_15 P_15_6 A_15 B_15_5 6 N_15_6 = true := by decide +kernel
def B_15_6 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_6
set_option maxRecDepth 500000 in
lemma B_15_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 6 xs.toFinset) B_15_6 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_5_ok C_15_6
def P_15_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_15 r_15 S_15 ps_15 [0,1,2,3,4,5,6,7,8,9,11]
def N_15_7 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5,6,7,8,9,11],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_7 : checkNodesBT W_15 g_15 F_15 P_15_7 A_15 B_15_6 7 N_15_7 = true := by decide +kernel
def B_15_7 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_7
set_option maxRecDepth 500000 in
lemma B_15_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 7 xs.toFinset) B_15_7 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_6_ok C_15_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_15_ok : forestRootCheck r_15 g_15 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_15_in : bucketContainsBT B_15_7 r_15 = true := by decide +kernel
lemma low_15 : Lower r_15 g_15 8 := lower_of_forestBT root_15_ok B_15_7_ok root_15_in
def g_16 := 0xffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8
def r_16 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_16 : Lower r_16 g_16 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_17 := 0xffecf880ffecf880ffecf880ffecf880ffecf880ffecf880ffecf880ffecf880
def r_17 : List Nat := varsOf 31
def p_17 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,18,18,19,19,21,21,21,22,22,24,24,25,25,26,28]
def q_17 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,2,17,3,20,17,5,20,6,16,8,17,9,10,20]
def F_17 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 7 (mkBase p_17 q_17 r_17) [(0,1,4),(0,2,3),(1,5,6),(1,2,3),(1,1,4),(0,8,9),(3,6,8),(3,5,9),(0,0,9),(1,13,6),(2,1,4),(3,1,4),(2,11,5),(1,5,3),(0,2,18),(1,2,18),(3,19,20),(2,0,6),(2,2,3),(3,2,3),(0,0,8),(3,13,8),(1,25,4),(0,1,27),(1,16,6),(1,25,5),(3,6,9),(2,0,19),(1,6,4),(0,0,20),(1,13,3),(3,2,35),(3,4,20),(0,1,33),(1,1,33),(2,1,33),(3,1,33),(0,3,4),(1,3,4),(3,42,43),(3,16,8),(3,13,3),(1,25,1),(1,24,16),(3,25,1),(1,24,5),(2,2,4),(2,1,3),(1,52,4),(0,1,2),(3,54,43),(1,54,3),(2,56,4),(1,51,52),(1,56,4),(1,54,4),(3,2,18),(2,3,4),(3,3,4),(2,1,43),(2,0,42),(1,16,3),(3,6,1),(1,2,42),(2,1,42),(1,51,3),(0,1,3),(1,1,3),(0,2,4),(1,73,3),(1,1,2),(0,0,75),(1,5,2),(3,1,3),(3,78,0),(3,6,4),(0,1,43),(2,2,1),(1,82,3),(3,2,4),(2,1,2)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^256) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_17 : BT (List (Nat × Nat)) := btOfList 1 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xffa0f000ffa0f000ffa0f000ffa0f000ffa0f000ffa0f000ffa0f000ffa0f000 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xecec8080ecec8080ecec8080ecec8080ecec8080ecec8080ecec8080ecec8080 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_10
set_option maxHeartbeats 0 in
lemma sl_17_7 : Slice r_17 g_17 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_8 : Slice r_17 g_17 (subcubeFast 8 4) 4 := by
  have hc : Lower (varsOf 19) 0xeeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_9 : Slice r_17 g_17 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_10 : Slice r_17 g_17 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) 0xececc8c8ececc8c8ececc8c8ececc8c8ececc8c8ececc8c8ececc8c8ececc8c8 6 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_11 : Slice r_17 g_17 (identDom 2 4) 6 := by
  have hc : Lower (varsOf 15) 0xf8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0 6 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_3
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_12 : Slice r_17 g_17 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xeeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_13 : Slice r_17 g_17 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) 0xffcccc88ffcccc88ffcccc88ffcccc88ffcccc88ffcccc88ffcccc88ffcccc88 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_14 : Slice r_17 g_17 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_17 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,7),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 4 1,4),some (subcubeFast 8 4,4),some (subcubeFast 16 2,4),some (identDom 1 3,6),some (identDom 2 4,6),some (identDom 0 3,5),some (identDom 1 2,5),some (subcubeFast 1 0,4)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (forall_cons (fun _ h => by cases h; exact sl_17_7) (forall_cons (fun _ h => by cases h; exact sl_17_8) (forall_cons (fun _ h => by cases h; exact sl_17_9) (forall_cons (fun _ h => by cases h; exact sl_17_10) (forall_cons (fun _ h => by cases h; exact sl_17_11) (forall_cons (fun _ h => by cases h; exact sl_17_12) (forall_cons (fun _ h => by cases h; exact sl_17_13) (forall_cons (fun _ h => by cases h; exact sl_17_14) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))
def ps_17 : BT (Option PoolSpec) := btOfList 7 ((([(9,[]),(8,[]),(0,[(0,2,3),(1,2,3),(3,6,8)]),(0,[(0,3,4),(1,3,4),(3,42,43)]),(2,[]),(0,[(2,1,4),(3,1,4)]),(0,[(1,1,4)]),(14,[]),(0,[(0,2,3),(1,6,4)]),(4,[(1,6,4)]),(3,[]),(5,[]),(1,[]),(0,[(0,2,3),(1,2,3)]),(4,[]),(3,[(0,0,8)]),(5,[(0,0,8)]),(1,[(0,0,9)]),(12,[]),(0,[]),(7,[]),(4,[(2,0,6)]),(0,[(0,1,4),(1,1,4)]),(6,[]),(0,[(2,3,4),(3,3,4)]),(0,[(2,3,4),(1,62,4)]),(0,[(0,3,4),(1,3,4)]),(0,[(3,1,4),(1,16,3)]),(0,[(2,2,4),(1,2,3)]),(2,[(2,2,4)]),(0,[(1,2,3)]),(0,[(0,2,3),(3,6,1)]),(0,[(1,2,3),(2,8,4)]),(0,[(0,4,3),(1,2,42)]),(4,[(1,3,4)]),(0,[(0,3,4),(2,1,42)]),(0,[(2,2,4),(1,51,3)]),(0,[(0,1,3),(1,1,3)]),(10,[]),(0,[(0,2,4),(1,73,3)]),(0,[(0,1,2),(1,1,2)]),(13,[]),(0,[(1,1,2)]),(1,[(0,0,75)]),(0,[(0,1,2),(1,54,3)]),(0,[(0,1,4),(1,5,2)]),(0,[(0,1,4),(1,5,3)]),(0,[(3,1,3)]),(0,[(0,2,3),(3,6,4)]),(2,[(1,3,4)]),(0,[(0,2,3)]),(0,[(0,1,4)]),(0,[(2,2,1),(1,82,3)]),(0,[(3,2,3)]),(0,[(2,1,4)]),(0,[(2,3,4)]),(0,[(0,1,3)]),(0,[(0,1,2)]),(0,[(1,1,3)]),(0,[(3,2,4)]),(11,[]),(0,[(2,1,2)]),(0,[(0,3,4)]),(0,[(2,2,4)]),(0,[(1,3,4)])] : List PoolSpec)).map some)
def B_17_1 : BT (List (List Nat)) := BT.empty
lemma B_17_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 1 xs.toFinset) B_17_1 := .empty
def P_17_2 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 []
def N_17_2 : List NodeSpec := [([0,7,10],[],[]),([11,12,0],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_2 : checkNodesBT W_17 g_17 F_17 P_17_2 A_17 B_17_1 2 N_17_2 = true := by decide +kernel
def B_17_2 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_2
set_option maxRecDepth 500000 in
lemma B_17_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 2 xs.toFinset) B_17_2 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_1_ok C_17_2
def P_17_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 []
def N_17_3 : List NodeSpec := [([1,14,8,4],[],[]),([0,5,6,10],[],[0]),([15,11,16,0],[],[0]),([11,0,5,9],[],[0]),([17,0,1,4],[],[]),([0,7,8,9],[],[0]),([11,13,1,4],[],[]),([21,0,1,4],[],[]),([22,12,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_3 : checkNodesBT W_17 g_17 F_17 P_17_3 A_17 B_17_2 3 N_17_3 = true := by decide +kernel
def B_17_3 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_3
set_option maxRecDepth 500000 in
lemma B_17_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 3 xs.toFinset) B_17_3 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_2_ok C_17_3
def P_17_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 [0,1,2]
def N_17_4 : List NodeSpec := [([15,23,24,16,0],[],[0,1]),([15,16,25,2,3],[],[1]),([26,1,2,3,4],[],[]),([25,28,2,3,4],[],[]),([15,0,2,29,3],[0],[]),([15,16,0,6,8],[],[0,1]),([0,5,2,3,10],[],[0]),([1,30,2,3,4],[],[1]),([0,1,7,8,4],[],[0]),([22,1,2,18,4],[],[]),([22,5,2,3,9],[],[0]),([31,0,5,2,3],[],[1]),([15,22,16,2,3],[],[0]),([25,5,2,3,9],[],[1]),([0,5,6,8,9],[],[0,1]),([32,1,2,18,4],[],[]),([0,1,2,18,33],[],[]),([34,1,2,18,4],[],[]),([36,13,1,3,4],[],[]),([25,1,2,18,4],[],[]),([37,0,1,2,18],[],[]),([24,12,0,2,3],[],[1]),([11,0,5,1,4],[1,2],[0,1]),([0,38,2,3,39],[],[1]),([40,41,0,2,3],[],[1]),([11,0,1,4,9],[2],[0]),([15,11,0,1,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_4 : checkNodesBT W_17 g_17 F_17 P_17_4 A_17 B_17_3 4 N_17_4 = true := by decide +kernel
def B_17_4 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_4
set_option maxRecDepth 500000 in
lemma B_17_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 4 xs.toFinset) B_17_4 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_3_ok C_17_4
def P_17_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def N_17_5 : List NodeSpec := [([44,0,1,2],[0,1,3],[]),([0,45,1,2,3,4],[],[]),([15,37,0,1,2,3],[4],[]),([15,16,0,2,3,8],[5],[0,1]),([15,25,1,2,3,4],[],[0]),([46,13,1,2,3,4],[4,6,7],[]),([25,1,47,2,3,4],[7],[]),([22,16,1,2,3,4],[],[0]),([48,0,1,2,3,4],[],[]),([49,25,1,2,3,4],[7],[]),([0,38,1,2,3,33],[8,9,10,11],[0,1]),([0,1,50,2,3,4],[12],[1]),([40,0,1,2,3,33],[],[0]),([0,5,1,6,8,4],[10,13,14],[0,1]),([15,24,16,0,2,3],[],[0]),([51,25,1,3,4],[14,15,16],[]),([24,13,1,2,3,4],[4,17],[1]),([0,1,2,3,33,39],[8,9,10],[0,1]),([15,0,1,6,8,4],[],[0]),([25,1,2,3,4,27],[7],[0,1]),([15,22,1,2,3,4],[],[0]),([15,23,24,0,1,4],[],[0]),([0,1,2,3,53,43],[11,12],[]),([55,0,1,2,3,4],[],[]),([57,0,1,2,3,4],[],[]),([58,0,1,2,3,4],[],[]),([44,0,1,2,43],[0,1,3],[]),([0,1,2,3,4,59],[4,12,18,19],[]),([25,1,2,3,4,9],[7],[0,1]),([22,1,2,3,4,9],[7,20],[0]),([0,1,2,3,60,43],[10,11,12],[]),([0,1,2,3,10,4],[7,19],[0,1]),([22,5,1,2,3,4],[7,11,20,21],[0]),([25,5,1,2,3,4],[7,14,15,16],[0]),([61,0,1,2,18,4],[],[1]),([24,0,1,2,18,4],[10],[]),([0,5,1,2,3,33],[4,8,9,10,11],[0,1]),([0,1,2,3,9,33],[8,9,10,11,12],[1]),([11,0,1,4],[1,2],[0,1]),([15,0,1,2,3,33],[4],[]),([0,5,2,3,8,9],[4,22],[0,1]),([24,0,5,2,3,9],[],[0,1]),([0,1,2,7,3,4],[4,7,10,12,19],[0,1]),([37,0,5,1,2,3],[4,14],[0]),([31,0,1,2,3,4],[7,10,12,19],[0]),([15,16,0,6,2,3],[0,5,12],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_5 : checkNodesBT W_17 g_17 F_17 P_17_5 A_17 B_17_4 5 N_17_5 = true := by decide +kernel
def B_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_5
set_option maxRecDepth 500000 in
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_4_ok C_17_5
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 [0,1,4,5,6,7,8,10,11,12,14,15,16,20,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54]
def N_17_6 : List NodeSpec := [([62,63,0,1,2],[1,11,23,24],[0]),([0,1,2,3,4,43],[0,1,25],[]),([64,0,1,2,3,4,43],[0,12],[0]),([0,1,2,42,43],[0,1,11,26],[0]),([65,1,2,3,4],[0,1],[]),([0,1,2,3,66,4],[4,10,14,23,27],[]),([15,24,0,1,2,3,4],[0,12],[0]),([51,0,1,3,8,4],[10,11,14,23,28,29],[0]),([25,1,2,3,4],[1,7,14,15,16,30],[0,1]),([51,52,0,1,2,3,4],[1,4,10,12,14],[0]),([67,0,2,3,4],[10,11,12,31],[]),([0,1,2,3,33],[8,10,11],[0,1]),([37,0,1,2,3,4],[1,4,10,11,12,14,32],[0]),([0,1,3,68,4],[11,14,23,33],[]),([15,23,0,1,2,3,4],[1,10,12],[0,1]),([51,0,1,2,3,4,43],[10,11,14,23,34],[1]),([69,0,2,3,4],[11,12,23,35],[]),([0,1,2,3,70,4],[1,4,10,12,36],[1]),([0,71,2,72,4],[0,12,37,38],[]),([0,54,1,2,3,4,43],[1,4,10,11,12,23],[0,1]),([0,1,2,3,74,4],[0,1,10,39],[]),([22,1,2,3,4],[11,20],[0]),([0,54,75,3,4],[1,4,12,40,41],[]),([24,16,0,1,2,3,4],[4,14],[0,1]),([76,1,2,3,4],[0,1,4,42,43],[]),([0,1,2,3,56,4],[1,10,12,23,44],[0,1]),([0,1,77,3,4],[12,14,23,45],[]),([0,1,2,3,18,4],[10,12,14,23,46],[0,1]),([79,1,2,3,4],[0,1,4,47],[]),([0,1,2,3,8,4,9],[4,6,14,30],[0,1]),([80,0,1,2,3],[10,11,23,48],[]),([0,81,1,2,3,4,43],[0,12,23,49],[]),([0,5,1,6,2,3,4],[4,10,11,12,14,23,50,51],[0,1]),([0,1,2,3,83,4],[0,1,4,10,23,52],[]),([0,5,2,3,9],[4,12,22],[0,1]),([0,5,1,2,3,8,4],[4,10,11,12,14,23,30,51],[0,1]),([24,0,1,2,3,4,9],[4,10,12,14,53],[0,1]),([24,0,5,1,2,3,4],[10,11,12,14,53],[0,1]),([15,0,1,6,2,3,4],[0,12,54],[0]),([15,0,1,2,3,8,4],[0,12,14,54],[0]),([15,16,0,2,3],[4,5,12],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6 = true := by decide +kernel
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_5_ok C_17_6
def P_17_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 [0,1,4,10,11,12,14,23,30,41,42,51,53,54,55,56,57,58,59,60,61,62,63,64]
def N_17_7 : List NodeSpec := [([62,0,1,2,3,4],[0,1,4,10,11,12,14,55],[0]),([0,71,1,2,3,4],[1,4,10,11,12,14,23,56],[0,1]),([0,54,1,2,3,4],[0,1,4,10,11,12,23,57],[0,1]),([0,1,2,75,3,4],[0,1,4,10,42],[0]),([0,1,2,3,72,4],[0,1,4,10,12,58],[0]),([84,0,1,2,3,4],[1,4,10,12,14,23,59,60],[1]),([85,0,1,2,3,4],[1,4,12,23,41,61],[1]),([24,0,1,2,3,4],[4,10,11,12,14,23,53],[0,1]),([0,5,1,2,3,4],[4,10,11,12,14,23,51],[0,1]),([0,1,2,3,8,4],[1,4,11,12,14,23,30],[0,1]),([15,0,1,2,3,4],[0,10,12,14,54],[0]),([0,1,2,42,3,4],[1,4,11,12,23,62],[0,1]),([51,0,1,2,3,4],[0,1,4,10,11,12,14,60,63],[0]),([0,1,2,3,4,43],[0,1,10,12,64],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7 = true := by decide +kernel
def B_17_7 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_7
set_option maxRecDepth 500000 in
lemma B_17_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 7 xs.toFinset) B_17_7 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_6_ok C_17_7
def P_17_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 [19]
def N_17_8 : List NodeSpec := [([0,1,2,3,4],[19],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_8 : checkNodesBT W_17 g_17 F_17 P_17_8 A_17 B_17_7 8 N_17_8 = true := by decide +kernel
def B_17_8 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_8
set_option maxRecDepth 500000 in
lemma B_17_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 8 xs.toFinset) B_17_8 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_7_ok C_17_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_8 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 9 := lower_of_forestBT root_17_ok B_17_8_ok root_17_in
def g_18 := 0xfefee800fefee800fefee800fefee800fefee800fefee800fefee800fefee800
def r_18 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_18 : Lower r_18 g_18 8 := by
  have hc : Lower (varsOf 23) 0xfefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 8) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) hc
def g_19 := 0xfefce800fefce800fefce800fefce800fefce800fefce800fefce800fefce800
def r_19 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_19 : Lower r_19 g_19 8 := by
  have hc : Lower (varsOf 23) 0xfefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 8) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) hc
def g_20 := 0xffa8c000ffa8c000ffa8c000ffa8c000ffa8c000ffa8c000ffa8c000ffa8c000
def r_20 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_20 : Lower r_20 g_20 7 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,18,19)]) (by decide +kernel) hc
def g_21 := 0xfffffe80fffffe80fffffe80fffffe80fffffe80fffffe80fffffe80fffffe80
def r_21 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_21 : Lower r_21 g_21 7 := by
  exact lift_of_f (z := 16) (o := 0) (other := r_3) (G := g_3) (essPairs := [(VAR 4,0,16)]) (by decide +kernel) low_3
def g_22 := 0xfffeff88f8e8e000fffeff88f8e8e000fffeff88f8e8e000fffeff88f8e8e000
def r_22 : List Nat := varsOf 63
def p_22 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,21,21,21,22,22,22,23,27,27,27,28,28,28,29,30,35,35,35,39,39,39,40,40,41,41,42,42,43,44,44,45,46,49,49,49,50,50,50,52,52,52,53,54,56,56,57,58]
def q_22 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,20,17,5,20,18,6,7,26,25,11,24,20,12,25,26,34,33,3,38,37,7,32,8,33,9,34,10,11,36,12,37,38,48,33,17,48,34,18,48,36,20,37,38,48,24,25,26]
def F_22 : Nat := fullMask 58
set_option maxHeartbeats 0 in
lemma gp_22 : goodPairs g_22 p_22 q_22 := goodPairs_of (by decide +kernel)
def W_22 : BT Decor := buildWiresBT 9 (mkBase p_22 q_22 r_22) [(0,1,4),(1,1,4),(3,6,7),(2,8,0),(2,9,5),(3,10,8),(2,8,5),(1,12,0),(1,0,5),(0,8,2),(3,15,14),(0,0,1),(1,0,1),(1,18,3),(0,19,4),(1,20,5),(3,17,21),(3,1,2),(0,0,4),(1,0,4),(3,24,25),(2,26,5),(1,27,1),(1,18,5),(3,17,29),(0,18,4),(1,31,3),(2,26,1),(2,33,5),(3,34,26),(1,1,5),(2,4,5),(1,3,4),(3,37,38),(1,17,39),(2,2,3),(3,41,4),(1,42,5),(3,17,43),(0,8,0),(3,45,14),(0,26,2),(1,47,5),(3,1,48),(1,15,0),(1,50,5),(2,50,5),(1,15,5),(2,1,5),(1,0,42),(3,54,55),(0,4,14),(1,4,14),(3,57,58),(2,59,1),(0,4,36),(1,4,36),(3,61,62),(1,63,0),(0,1,14),(3,65,29),(3,66,4),(0,66,4),(3,1,4),(3,69,0),(1,70,5),(2,1,4),(1,41,1),(2,73,5),(1,74,24),(1,37,18),(3,17,76),(0,30,4),(1,3,5),(3,31,79),(0,0,2),(1,81,5),(3,1,82),(1,54,83),(0,0,36),(1,1,3),(1,86,5),(0,4,87),(1,0,88),(0,2,4),(1,17,90),(2,91,5),(1,91,5),(3,8,0),(1,94,5),(3,30,4),(2,18,4),(3,18,4),(1,98,17),(3,17,19),(0,100,4),(3,12,2),(0,2,14),(1,18,4),(3,31,104),(2,100,5),(2,2,36),(2,18,5),(3,17,104),(3,37,19),(2,2,5),(1,8,0),(3,18,38),(1,113,17),(3,0,2),(1,100,5),(1,6,3),(0,2,117),(1,0,118),(3,1,119),(3,100,4),(2,19,5),(3,18,2),(1,123,17),(1,31,5),(3,17,125),(3,1,125),(3,0,125),(2,1,0),(3,129,43),(1,45,5),(0,2,104),(2,112,5),(3,26,1),(1,69,0),(2,135,5),(0,12,2),(3,8,2),(1,138,5),(1,0,90),(3,54,140),(2,0,5),(3,1,140),(1,1,42),(1,41,0),(3,54,145),(1,0,61),(3,1,147),(1,90,5),(3,1,149),(3,0,149),(1,0,3),(1,152,5),(3,1,153),(0,140,36),(3,0,29),(3,156,38),(1,1,90),(3,54,158),(2,69,5),(1,160,85),(0,2,36),(3,162,4),(1,163,0),(3,65,4),(2,25,5),(1,166,1),(2,0,4),(1,168,162),(3,0,4),(3,170,1),(1,171,5),(1,111,0),(0,173,7),(3,1,14),(0,4,153),(3,162,25),(3,156,4),(3,156,7),(3,1,87),(1,180,24),(3,6,153),(1,24,162),(2,140,5),(1,8,5),(2,0,1),(1,37,186),(3,6,145),(1,37,3),(1,4,5),(3,17,190),(3,97,29),(3,129,149),(0,4,79),(1,1,103),(1,17,194),(1,23,0),(0,197,7),(3,17,149),(1,97,5),(0,18,79),(1,24,3),(0,1,2),(1,203,5),(3,6,152),(2,145,5),(2,104,5),(1,37,0),(2,208,1),(0,2,38),(3,129,158),(2,145,1),(0,1,140),(1,186,194),(0,86,4),(1,0,215),(1,41,5),(1,111,17),(1,142,1),(2,0,36),(1,0,162),(0,152,4),(1,129,5),(2,2,4),(1,224,5),(3,1,38),(3,0,190),(0,4,29),(0,0,149),(1,69,5),(0,18,2),(1,231,5),(0,18,38),(2,18,194),(1,108,3),(3,17,38),(2,38,5),(1,37,1),(3,0,238),(0,38,29),(0,18,149),(3,3,4),(2,242,5),(3,4,36),(3,244,29),(3,1,25),(1,186,215),(1,215,5),(1,23,5),(0,25,249),(3,0,204),(0,197,190),(1,222,5),(3,1,190),(3,1,152),(2,152,61),(1,54,222),(1,115,5),(0,25,258),(2,0,3),(1,260,61),(1,186,61),(1,226,0),(3,1,189),(3,37,1),(1,265,0),(1,254,0),(1,0,194),(1,180,0),(1,243,0),(1,226,5),(2,173,4),(3,1,225),(1,224,0),(2,274,1),(3,54,38),(3,54,4),(1,0,277),(1,142,3),(3,1,279),(1,54,0),(3,3,36),(1,282,0),(2,38,36),(3,90,14),(1,90,14),(2,173,1),(3,0,153),(3,170,79),(1,111,69),(1,142,69),(3,3,14),(1,160,0),(2,170,5),(3,1,58),(1,170,3),(3,1,296),(1,135,5),(1,111,168),(3,72,14),(1,170,1),(1,168,5),(3,1,302),(1,54,168),(2,7,5),(1,305,0),(3,111,25),(3,54,25),(0,25,36),(3,0,7),(2,246,5),(1,111,24),(1,244,0),(1,54,3),(1,54,24),(3,6,14),(3,180,0),(3,1,202),(0,2,202),(0,0,117),(1,6,0),(0,173,4),(2,321,5),(1,54,260),(1,6,5),(2,1,3),(1,326,24),(3,326,36),(3,326,4),(1,329,5),(1,326,0),(2,331,5),(2,152,5),(3,86,4),(1,334,0),(1,1,222),(0,152,36),(3,175,4),(1,260,5),(1,170,5),(2,255,5),(3,111,4),(1,0,342),(3,18,79),(3,170,36),(1,24,1),(1,197,5),(1,186,5),(1,72,0),(2,349,5),(2,18,90),(3,4,29),(1,349,5),(1,111,1),(1,24,5),(3,129,79),(1,175,4),(3,4,249),(1,17,5),(1,81,1),(0,18,190),(3,129,4),(1,362,5),(1,326,5),(3,18,190),(1,98,5),(1,69,81),(2,197,4),(1,246,5),(1,331,5),(3,37,152),(3,111,18),(3,4,14),(3,129,190),(1,111,18),(1,37,81),(1,115,1),(2,18,3),(3,203,4),(1,379,0),(3,17,4),(1,381,5),(3,54,152),(3,6,79),(1,321,5),(1,18,90),(1,203,0),(3,115,4),(1,388,5),(1,142,90),(1,54,81),(2,274,5),(3,1,258),(3,115,7),(2,387,5),(1,37,17),(3,129,38),(1,0,329),(1,379,5),(1,260,69),(1,37,260),(1,203,24),(1,255,5),(3,37,18),(2,197,5),(1,168,23),(1,186,90),(0,38,14),(3,0,19),(3,170,86),(0,1,79),(1,411,0),(2,1,14),(3,413,4),(3,1,340),(1,111,186),(1,37,23),(0,238,0),(1,387,5),(1,142,23),(3,203,25),(1,72,81),(0,0,158),(3,203,14),(3,203,190),(3,326,14),(3,17,79),(0,197,4),(3,23,4),(1,429,0),(0,4,249),(1,23,24),(1,115,69),(3,115,36),(3,115,190),(3,37,0),(0,0,79),(1,69,3),(1,186,3),(1,17,3),(0,0,86)]
lemma W_22_ok : btAll (fun x => faithful p_22 q_22 x ∧ x.1 < 2^256) W_22 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_22 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_22 : BT (List (Nat × Nat)) := btOfList 1 al_22
set_option maxHeartbeats 0 in
lemma A_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_22 = g_22) A_22 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_22_0 : Slice r_22 g_22 (subcubeFast 8 0) 9 := by
  have hc : Lower (varsOf 55) 0xfefe8888e8e80000fefe8888e8e80000fefe8888e8e80000fefe8888e8e80000 9 := carry_of (swaps := [(0,1),(1,2),(3,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_1 : Slice r_22 g_22 (subcubeFast 0 4) 9 := by
  have hc : Lower (varsOf 59) 0xffffff88ffeeee00ffffff88ffeeee00ffffff88ffeeee00ffffff88ffeeee00 9 := carry_of (swaps := [(2,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_2 : Slice r_22 g_22 (subcubeFast 32 0) 9 := by
  have hc : Lower (varsOf 31) 0xf8e8e000f8e8e000f8e8e000f8e8e000f8e8e000f8e8e000f8e8e000f8e8e000 9 := carry_of (swaps := [(0,1),(1,2),(2,4),(3,4)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_3 : Slice r_22 g_22 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) 0xffeeff8888880000ffeeff8888880000ffeeff8888880000ffeeff8888880000 8 := carry_of (swaps := [(0,1),(1,2),(2,5),(3,5),(4,5)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_4 : Slice r_22 g_22 (subcubeFast 0 16) 8 := by
  have hc : Lower (varsOf 47) 0xfffefffef8e8f8e8fffefffef8e8f8e8fffefffef8e8f8e8fffefffef8e8f8e8 8 := carry_of (swaps := [(0,1),(1,2),(2,3),(4,5)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_5 : Slice r_22 g_22 (subcubeFast 8 16) 7 := by
  have hc : Lower (varsOf 39) 0xfefefefee8e8e8e8fefefefee8e8e8e8fefefefee8e8e8e8fefefefee8e8e8e8 7 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_6 : Slice r_22 g_22 (subcubeFast 12 0) 7 := by
  have hc : Lower (varsOf 51) 0xeeee888888880000eeee888888880000eeee888888880000eeee888888880000 7 := carry_of (swaps := [(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 12) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_7 : Slice r_22 g_22 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) 0xfffaff00f0a0a000fffaff00f0a0a000fffaff00f0a0a000fffaff00f0a0a000 8 := carry_of (swaps := [(1,5),(2,5),(3,4),(4,5)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_8 : Slice r_22 g_22 (subcubeFast 1 0) 8 := by
  have hc : Lower (varsOf 62) 0xfffcff00f0c0c000fffcff00f0c0c000fffcff00f0c0c000fffcff00f0c0c000 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,4),(4,5)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_9 : Slice r_22 g_22 (identDom 0 1) 9 := by
  have hc : Lower (varsOf 61) 0xfffaffaafaaaa000fffaffaafaaaa000fffaffaafaaaa000fffaffaafaaaa000 9 := carry_of (swaps := [(0,3),(1,5),(2,3),(3,5),(4,5)]) (by decide +kernel) low_17
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_10 : Slice r_22 g_22 (identDom 0 5) 8 := by
  have hc : Lower (varsOf 31) 0xfaeaea88faeaea88faeaea88faeaea88faeaea88faeaea88faeaea88faeaea88 8 := carry_of (swaps := [(0,4),(1,4),(2,3),(3,4)]) (by decide +kernel) low_18
  exact slice_ident (u := 0) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_11 : Slice r_22 g_22 (identDom 1 3) 8 := by
  have hc : Lower (varsOf 55) 0xfefecccce8e8c0c0fefecccce8e8c0c0fefecccce8e8c0c0fefecccce8e8c0c0 8 := carry_of (swaps := [(1,4),(2,4),(3,5),(4,5)]) (by decide +kernel) low_19
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_12 : Slice r_22 g_22 (identDom 1 5) 8 := by
  have hc : Lower (varsOf 31) 0xfcecec88fcecec88fcecec88fcecec88fcecec88fcecec88fcecec88fcecec88 8 := carry_of (swaps := [(1,4),(2,3),(3,4)]) (by decide +kernel) low_18
  exact slice_ident (u := 1) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_13 : Slice r_22 g_22 (subcubeFast 16 0) 7 := by
  have hc : Lower (varsOf 47) 0xff88ff88e000e000ff88ff88e000e000ff88ff88e000e000ff88ff88e000e000 7 := carry_of (swaps := [(0,1),(1,2),(3,4),(4,5)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_14 : Slice r_22 g_22 (subcubeFast 0 8) 7 := by
  have hc : Lower (varsOf 55) 0xfffffffff8f8e0e0fffffffff8f8e0e0fffffffff8f8e0e0fffffffff8f8e0e0 7 := carry_of (swaps := [(2,3),(3,5),(4,5)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_15 : Slice r_22 g_22 (subcubeFast 32 8) 6 := by
  have hc : Lower (varsOf 23) 0xf8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 32) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_16 : Slice r_22 g_22 (subcubeFast 16 4) 6 := by
  have hc : Lower (varsOf 43) 0xff88ff88ee00ee00ff88ff88ee00ee00ff88ff88ee00ee00ff88ff88ee00ee00 6 := carry_of (swaps := [(2,4),(4,5)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 16) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_17 : Slice r_22 g_22 (subcubeFast 8 4) 6 := by
  have hc : Lower (varsOf 51) 0xffff8888eeee0000ffff8888eeee0000ffff8888eeee0000ffff8888eeee0000 6 := carry_of (swaps := [(2,4),(3,5),(4,5)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_18 : Slice r_22 g_22 (subcubeFast 3 4) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000ffffff00ff000000ffffff00ff000000ffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_19 : Slice r_22 g_22 (subcubeFast 3 16) 4 := by
  have hc : Lower (varsOf 44) 0xfff0fff0f000f000fff0fff0f000f000fff0fff0f000f000fff0fff0f000f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_20 : Slice r_22 g_22 (subcubeFast 12 1) 4 := by
  have hc : Lower (varsOf 50) 0xffffcccccccc0000ffffcccccccc0000ffffcccccccc0000ffffcccccccc0000 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_21 : Slice r_22 g_22 (subcubeFast 33 4) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_22 : Slice r_22 g_22 (subcubeFast 9 16) 4 := by
  have hc : Lower (varsOf 38) 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_23 : Slice r_22 g_22 (subcubeFast 12 2) 4 := by
  have hc : Lower (varsOf 49) 0xffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000 4 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_24 : Slice r_22 g_22 (subcubeFast 34 4) 4 := by
  have hc : Lower (varsOf 25) 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 34) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_25 : Slice r_22 g_22 (subcubeFast 10 16) 4 := by
  have hc : Lower (varsOf 37) 0xfafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0 4 := carry_of (swaps := [(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 10) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_26 : Slice r_22 g_22 (subcubeFast 12 16) 4 := by
  have hc : Lower (varsOf 35) 0xeeeeeeee88888888eeeeeeee88888888eeeeeeee88888888eeeeeeee88888888 4 := carry_of (swaps := [(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_27 : Slice r_22 g_22 (subcubeFast 12 32) 4 := by
  have hc : Lower (varsOf 19) 0xeeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_28 : Slice r_22 g_22 (subcubeFast 40 16) 4 := by
  exact slice_fast_direct_f (z := 40) (o := 16) (by decide +kernel) low_0
def S_22 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 8 0,9),some (subcubeFast 0 4,9),some (subcubeFast 32 0,9),some (subcubeFast 4 0,8),some (subcubeFast 0 16,8),some (subcubeFast 8 16,7),some (subcubeFast 12 0,7),some (subcubeFast 2 0,8),some (subcubeFast 1 0,8),some (identDom 0 1,9),some (identDom 0 5,8),some (identDom 1 3,8),some (identDom 1 5,8),some (subcubeFast 16 0,7),some (subcubeFast 0 8,7),some (subcubeFast 32 8,6),some (subcubeFast 16 4,6),some (subcubeFast 8 4,6),some (subcubeFast 3 4,4),some (subcubeFast 3 16,4),some (subcubeFast 12 1,4),some (subcubeFast 33 4,4),some (subcubeFast 9 16,4),some (subcubeFast 12 2,4),some (subcubeFast 34 4,4),some (subcubeFast 10 16,4),some (subcubeFast 12 16,4),some (subcubeFast 12 32,4),some (subcubeFast 40 16,4)]
lemma S_22_ok : btAll (fun o => ∀ p, o = some p → Slice r_22 g_22 p.1 p.2) S_22 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (forall_cons (fun _ h => by cases h; exact sl_22_4) (forall_cons (fun _ h => by cases h; exact sl_22_5) (forall_cons (fun _ h => by cases h; exact sl_22_6) (forall_cons (fun _ h => by cases h; exact sl_22_7) (forall_cons (fun _ h => by cases h; exact sl_22_8) (forall_cons (fun _ h => by cases h; exact sl_22_9) (forall_cons (fun _ h => by cases h; exact sl_22_10) (forall_cons (fun _ h => by cases h; exact sl_22_11) (forall_cons (fun _ h => by cases h; exact sl_22_12) (forall_cons (fun _ h => by cases h; exact sl_22_13) (forall_cons (fun _ h => by cases h; exact sl_22_14) (forall_cons (fun _ h => by cases h; exact sl_22_15) (forall_cons (fun _ h => by cases h; exact sl_22_16) (forall_cons (fun _ h => by cases h; exact sl_22_17) (forall_cons (fun _ h => by cases h; exact sl_22_18) (forall_cons (fun _ h => by cases h; exact sl_22_19) (forall_cons (fun _ h => by cases h; exact sl_22_20) (forall_cons (fun _ h => by cases h; exact sl_22_21) (forall_cons (fun _ h => by cases h; exact sl_22_22) (forall_cons (fun _ h => by cases h; exact sl_22_23) (forall_cons (fun _ h => by cases h; exact sl_22_24) (forall_cons (fun _ h => by cases h; exact sl_22_25) (forall_cons (fun _ h => by cases h; exact sl_22_26) (forall_cons (fun _ h => by cases h; exact sl_22_27) (forall_cons (fun _ h => by cases h; exact sl_22_28) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))
def ps_22 : BT (Option PoolSpec) := btOfList 12 ((([(2,[(0,1,4),(1,1,4),(3,6,7)]),(2,[(0,1,4),(1,1,4),(3,6,7),(2,12,0),(3,10,8)]),(1,[(0,1,4),(1,1,4),(3,6,7),(1,0,5),(0,8,14)]),(1,[(0,0,4),(1,0,4),(3,24,25)]),(19,[]),(4,[(0,0,1),(1,0,1),(1,17,39)]),(8,[(0,1,4),(1,1,4),(3,6,7)]),(2,[(0,0,4),(1,0,4),(3,24,25),(2,26,1),(3,34,26)]),(0,[(0,0,4),(1,0,4),(3,24,25)]),(1,[(0,1,4),(1,1,4),(3,6,7),(1,15,0),(1,50,5)]),(0,[(0,1,4),(1,1,4),(3,6,7)]),(14,[(0,1,4),(1,1,4),(3,6,7)]),(3,[(0,1,4),(1,1,4),(3,6,7)]),(20,[]),(4,[(1,0,5)]),(8,[(2,1,4),(3,1,4),(1,72,69)]),(5,[(3,69,0),(1,70,5)]),(3,[(2,1,4),(3,1,4),(1,72,69)]),(1,[(2,1,4),(3,1,4),(1,72,69)]),(13,[(0,0,1),(1,0,1),(3,17,76)]),(2,[(0,0,1),(1,0,1),(1,37,18),(3,17,76)]),(2,[(0,0,1),(1,0,1),(3,17,29),(0,30,4)]),(0,[(0,0,1),(1,0,1)]),(9,[(0,18,4),(1,3,5),(3,31,79)]),(8,[(2,1,5),(3,1,82),(1,54,83)]),(1,[(1,81,5),(2,1,5),(3,1,82),(1,54,83)]),(0,[(0,0,2),(1,81,5),(2,1,5),(3,1,82),(1,54,83)]),(6,[(2,1,5),(3,1,82),(1,54,83)]),(2,[(0,0,1),(1,0,1),(0,2,4),(1,17,90)]),(1,[(0,0,1),(1,0,1),(1,17,90)]),(4,[(0,0,1),(1,0,1),(1,17,90)]),(5,[(3,8,0),(1,94,5)]),(1,[(0,1,4),(1,1,4),(3,6,7),(3,8,0),(1,94,5)]),(2,[(0,0,1),(1,0,1),(3,17,29),(3,30,4)]),(4,[(0,0,1),(1,0,1),(1,98,17)]),(18,[]),(0,[(0,0,1),(1,0,1),(2,18,4),(3,18,4),(1,98,17)]),(5,[(0,0,1),(1,0,1),(1,98,17)]),(2,[(0,0,1),(1,0,1),(2,18,4),(3,18,4),(1,98,17)]),(4,[(0,0,1),(1,0,1)]),(9,[(1,3,4),(2,4,5),(3,37,38)]),(7,[(0,18,4),(1,18,5)]),(9,[(1,18,5),(3,17,29)]),(1,[(0,0,1),(1,0,1),(1,18,5),(3,17,29)]),(15,[(0,0,1),(1,0,1),(3,17,29)]),(0,[(0,0,1),(1,0,1),(3,17,19)]),(5,[(0,0,1),(1,0,1),(3,17,19)]),(9,[(1,18,3),(3,17,19)]),(1,[(0,1,4),(1,1,4),(3,6,7)]),(1,[(0,1,4),(1,1,4),(3,6,7),(2,8,5)]),(2,[(0,1,4),(1,1,4),(3,6,7),(3,12,2)]),(2,[(0,1,4),(1,1,4),(3,6,7),(0,2,14)]),(1,[(0,1,4),(1,1,4),(3,6,7),(1,0,5)]),(4,[(0,0,1),(1,17,39)]),(7,[(0,18,4),(1,18,4),(3,31,104)]),(0,[(0,0,1),(1,0,1),(0,18,4),(1,18,4),(3,31,104)]),(5,[(0,0,1),(1,0,1)]),(2,[(0,0,1),(1,0,1),(0,18,4),(1,18,4),(3,31,104)]),(0,[(0,0,1),(1,0,1),(3,17,19),(2,100,5)]),(2,[(0,0,1),(1,0,1),(1,18,3),(3,17,19)]),(21,[]),(3,[(0,0,4),(1,0,4),(3,24,25)]),(7,[(1,18,3),(2,18,5)]),(3,[(0,0,1),(1,0,1),(1,18,3),(3,17,19)]),(4,[(0,0,1),(1,0,1),(1,18,3),(3,17,19)]),(15,[(0,0,1),(1,0,1)]),(0,[(0,0,1),(1,0,1),(3,17,19),(2,18,5)]),(7,[(0,18,4),(1,18,4)]),(0,[(0,0,1),(1,0,1),(0,18,4),(1,18,4),(3,17,104)]),(2,[(0,0,1),(1,0,1),(0,18,4),(1,18,4),(3,17,104)]),(7,[(0,18,4),(1,31,3),(1,18,5)]),(0,[(0,0,1),(1,0,1),(0,18,4)]),(4,[(0,0,1),(1,0,1),(1,31,3)]),(2,[(0,0,1),(1,0,1),(0,18,4),(1,31,3)]),(14,[(0,0,1),(1,0,1)]),(0,[(0,0,1),(1,0,1),(3,17,19),(2,4,5)]),(9,[(1,18,3),(2,4,5),(3,37,19)]),(24,[]),(6,[(0,0,1),(1,0,1),(3,18,38),(1,113,17)]),(1,[(0,0,1),(1,0,1),(1,3,4),(3,18,38),(1,113,17)]),(0,[(0,0,1),(1,0,1),(3,18,38),(1,113,17)]),(4,[(0,0,1),(1,0,1),(1,113,17)]),(2,[(0,0,1),(1,0,1),(1,3,4),(3,18,38),(1,113,17)]),(2,[(3,0,2),(0,1,4),(1,1,4),(3,6,7)]),(0,[(0,0,1),(1,0,1),(3,17,19),(1,100,5)]),(7,[(1,18,3)]),(9,[(1,18,3),(0,19,4),(1,20,5)]),(5,[(0,0,1),(1,0,1),(1,20,5)]),(2,[(0,0,1),(1,0,1),(1,18,3),(0,19,4)]),(7,[]),(0,[(0,0,1),(1,0,1),(3,17,19),(3,100,4)]),(9,[(1,18,3),(2,19,5),(2,4,5)]),(1,[(0,0,1),(1,0,1),(1,123,17),(2,4,5)]),(2,[(0,0,1),(1,0,1),(3,18,2),(1,123,17)]),(2,[(0,0,1),(1,0,1),(0,18,4),(3,17,125)]),(9,[]),(9,[(0,18,4),(1,31,5),(3,1,125)]),(5,[(2,8,5),(1,12,0)]),(2,[(0,1,4),(1,1,4),(3,6,7),(1,12,0)]),(2,[(0,0,2),(0,1,4),(1,1,4),(3,6,7)]),(1,[(1,81,5),(0,1,4),(1,1,4),(3,6,7)]),(5,[(0,0,2),(1,81,5)]),(2,[(0,1,4),(1,1,4),(3,6,7),(0,8,0)]),(5,[(0,8,0),(1,45,5)]),(7,[(0,18,4),(1,18,4),(0,2,104)]),(3,[(0,0,1),(1,0,1),(0,18,4)]),(0,[(0,0,1),(1,0,1),(0,18,4),(1,18,4),(0,2,104)]),(9,[(0,1,4),(1,1,4),(3,6,7)]),(0,[(0,1,4),(1,1,4),(3,6,7),(0,8,0),(1,8,0)]),(5,[(0,8,0),(1,8,0)]),(2,[(0,1,4),(1,1,4),(3,6,7),(0,8,0),(1,8,0)]),(5,[(0,8,0),(1,0,5)]),(2,[(0,1,4),(1,1,4),(3,6,7),(1,8,0)]),(5,[(1,8,0),(2,112,5)]),(5,[(2,26,1),(2,33,5)]),(7,[(0,0,4),(1,0,4),(3,24,25)]),(5,[(2,26,1),(1,1,5)]),(2,[(0,0,4),(1,0,4),(3,24,25)]),(0,[(0,0,4),(1,0,4),(3,24,25),(2,26,1),(3,26,1)]),(1,[(0,0,4),(1,0,4),(3,24,25),(2,26,1),(3,26,1)]),(5,[(2,26,1),(3,26,1)]),(2,[(0,0,4),(1,0,4),(3,24,25),(2,26,1),(3,26,1)]),(0,[(2,1,4),(3,1,4),(1,72,69)]),(5,[(1,69,0),(2,135,5)]),(5,[(0,8,2),(1,15,0)]),(9,[(2,2,3),(3,41,4),(1,42,5)]),(2,[(0,1,4),(1,1,4),(3,6,7),(0,8,2)]),(1,[(0,1,4),(1,1,4),(3,6,7),(1,15,5)]),(5,[(0,8,2),(1,15,5)]),(1,[(0,1,4),(1,1,4),(3,6,7),(1,138,5)]),(0,[(0,1,4),(1,1,4),(3,6,7),(3,8,2),(1,138,5)]),(5,[(3,8,2),(1,138,5)]),(5,[(1,0,5),(0,8,14)]),(2,[(0,1,4),(1,1,4),(3,6,7),(0,8,14)]),(3,[(2,1,5),(3,54,140)]),(13,[(2,1,5),(3,54,140)]),(2,[(0,2,4),(1,0,90),(3,54,140)]),(7,[(0,2,4),(1,0,90)]),(0,[]),(6,[(2,1,5),(3,54,140)]),(4,[]),(8,[(0,2,4)]),(23,[]),(8,[]),(2,[(2,2,3),(3,41,4),(1,1,42)]),(3,[(2,1,5),(3,54,145)]),(7,[(2,2,3),(1,41,0)]),(0,[(2,1,5),(1,41,0),(3,54,145)]),(13,[]),(2,[]),(2,[(2,2,3),(1,41,0),(3,54,145)]),(2,[(0,4,36),(1,4,36),(3,61,62)]),(4,[(1,1,5)]),(2,[(0,4,36),(1,0,61)]),(13,[(1,1,5)]),(2,[(1,3,36),(0,4,87),(1,0,88)]),(7,[(0,2,4),(1,90,5)]),(5,[(1,0,5),(3,1,153)]),(7,[(1,0,5),(1,3,14)]),(3,[]),(8,[(2,2,3),(3,41,4)]),(2,[(2,2,3),(3,41,4),(1,0,42)]),(15,[]),(4,[(1,1,5),(3,0,36)]),(2,[(3,0,36),(1,3,4),(3,156,38)]),(9,[(0,2,4),(1,1,90)]),(1,[(2,1,5),(1,1,90),(3,54,158)]),(3,[(2,1,5),(3,54,158)]),(6,[(2,1,5),(3,54,158)]),(2,[(0,2,4),(1,1,90),(3,54,158)]),(8,[(1,1,5),(2,4,36)]),(2,[(0,0,36),(2,4,36),(1,160,85)]),(2,[(0,2,36),(3,162,4),(1,163,0)]),(5,[(1,1,5),(0,0,36)]),(7,[(1,0,5)]),(9,[(1,0,5),(3,65,29)]),(2,[(0,1,14),(1,1,14),(3,65,29)]),(5,[(1,0,5),(0,1,14)]),(2,[(3,1,4),(1,3,14),(3,1,153)]),(2,[(3,1,4),(1,69,0),(1,136,1)]),(4,[(1,69,0),(2,135,5)]),(2,[(2,0,4),(0,2,36),(1,168,162)]),(1,[(2,0,4),(1,1,5),(1,168,162)]),(3,[(2,0,4),(3,0,4)]),(2,[(2,0,4),(3,0,4),(0,2,36)]),(1,[(2,0,4),(3,0,4)]),(1,[(2,0,4),(3,0,4),(1,1,5)]),(4,[(3,170,1),(1,171,5)]),(13,[(1,171,5)]),(5,[(3,170,1),(1,171,5)]),(2,[(2,0,4),(3,0,4),(3,170,1)]),(7,[(2,0,4),(3,0,4)]),(2,[(2,1,4),(3,1,4)]),(2,[(2,1,4),(3,1,4),(1,69,0)]),(8,[(2,1,4),(3,1,4)]),(3,[(2,1,4),(3,1,4)]),(1,[(2,1,4),(3,1,4)]),(0,[(2,1,4),(3,1,4)]),(2,[(2,1,4),(3,1,4),(1,72,69)]),(5,[(2,8,5)]),(13,[(2,8,5)]),(4,[(3,69,0)]),(5,[(3,69,0)]),(2,[(2,1,4),(3,1,4),(1,72,69),(3,69,0)]),(1,[(2,1,4),(3,1,4),(1,72,69),(3,69,0)]),(16,[]),(3,[(1,1,4),(0,173,7)]),(5,[(2,2,5),(1,111,0)]),(2,[(1,1,4),(1,111,0),(0,173,7)]),(5,[(1,0,5),(3,1,14)]),(1,[]),(1,[(1,0,4),(1,1,5),(3,162,25)]),(2,[(1,0,4),(0,2,36),(3,162,25)]),(8,[(1,1,5),(3,156,4)]),(2,[(1,0,4),(3,0,36),(3,156,4)]),(5,[(1,1,5),(3,0,36)]),(2,[(1,1,4),(3,0,36),(3,156,7)]),(7,[(3,0,36),(3,156,7)]),(5,[(3,1,79),(1,180,24)]),(8,[(1,3,5),(3,1,79)]),(14,[]),(2,[(0,0,4),(3,1,79),(1,180,24)]),(2,[(0,1,4),(1,3,14),(3,1,153)]),(14,[(1,0,5)]),(27,[]),(22,[]),(2,[(0,1,4),(1,3,14),(3,6,153)]),(0,[(0,1,4),(1,0,5),(3,6,153)]),(14,[(0,1,4)]),(2,[(0,0,4),(0,2,36),(1,24,162)]),(1,[(0,0,4),(1,1,5),(1,24,162)]),(3,[(0,0,4)]),(3,[(0,0,4),(1,0,4)]),(0,[(0,1,4),(1,1,4),(3,6,7),(2,2,5)]),(5,[(2,2,5)]),(5,[(2,0,5)]),(0,[(0,1,4),(1,1,4),(3,6,7),(2,8,5)]),(2,[(0,2,4),(1,0,90),(3,1,140)]),(2,[(0,0,4),(1,0,4),(0,2,36)]),(1,[(0,0,4),(1,0,4)]),(1,[(0,0,4),(1,0,4),(1,1,5)]),(5,[(3,8,2)]),(0,[(0,1,4),(1,1,4),(3,6,7),(1,0,5)]),(5,[(1,0,5)]),(5,[(1,8,5)]),(2,[(1,0,1),(0,18,4)]),(4,[(0,0,1)]),(14,[(2,4,5)]),(0,[(2,4,5),(3,37,38)]),(28,[]),(2,[(1,0,1),(1,18,3),(0,18,4)]),(5,[]),(0,[(1,0,1),(2,19,5)]),(1,[(2,0,1),(2,4,5),(1,37,186)]),(7,[(1,0,3),(1,152,5)]),(5,[(1,152,5),(3,6,153)]),(2,[(1,0,3),(0,1,4),(3,6,153)]),(4,[(1,0,1)]),(14,[(1,0,1)]),(2,[(2,2,3),(3,41,4)]),(2,[(0,0,1),(0,2,4),(1,17,90)]),(3,[(0,1,4),(3,6,145)]),(0,[(0,1,4),(1,41,0),(3,6,145)]),(5,[(1,41,0),(3,6,145)]),(1,[(0,1,4),(1,41,0),(3,6,145)]),(0,[(0,0,1),(1,0,1),(2,4,5)]),(13,[(0,0,1),(1,0,1)]),(9,[(2,4,5),(1,37,3)]),(2,[(0,0,1),(1,0,1),(1,37,3)]),(9,[(1,4,5),(3,17,190)]),(0,[(0,0,1),(1,0,1),(1,4,5),(3,17,190)]),(1,[(0,0,1),(1,0,1),(1,4,5),(3,17,190)]),(2,[(0,0,1),(1,0,1),(3,17,190)]),(4,[(1,0,1),(1,18,5)]),(5,[(1,0,1),(1,18,5)]),(2,[(2,1,0),(0,2,4),(3,129,149)]),(9,[(1,3,5),(0,4,79)]),(0,[(0,0,1),(1,0,1),(0,4,79)]),(8,[(0,2,14),(1,1,103)]),(2,[(1,1,4),(0,2,14),(1,1,103)]),(3,[(1,0,5)]),(13,[(1,0,5)]),(8,[(1,3,5),(0,4,79)]),(7,[(1,3,5),(0,4,79)]),(0,[(0,0,1),(0,4,79),(1,17,194)]),(5,[(0,0,1),(1,17,194)]),(2,[(0,0,1),(0,4,79),(1,17,194)]),(5,[(0,8,2)]),(3,[(1,1,4),(0,197,7)]),(7,[(1,23,0),(0,197,7)]),(5,[(3,1,2),(1,23,0)]),(8,[(0,2,4),(1,90,5)]),(1,[(0,0,1),(1,90,5),(3,17,149)]),(6,[(0,0,1),(3,17,149)]),(2,[(0,0,1),(0,2,4),(3,17,149)]),(2,[(0,0,1),(1,0,1),(3,17,29)]),(9,[(2,18,4),(1,97,5)]),(7,[(2,18,4),(1,97,5)]),(2,[(0,0,1),(1,0,1),(2,18,4)]),(9,[(1,3,5),(0,18,79)]),(2,[(0,1,2),(0,0,4),(1,24,3)]),(8,[(0,1,2),(1,203,5)]),(1,[(1,203,5),(0,0,4),(1,24,3)]),(3,[(0,0,4),(1,24,3)]),(7,[(0,0,4),(1,24,3)]),(14,[(0,1,2),(1,203,5)]),(15,[(0,1,2)]),(4,[(0,1,2),(1,203,5),(1,24,3)]),(9,[(0,18,4),(1,31,3)]),(7,[(0,18,4),(1,31,3)]),(0,[(1,0,5),(0,1,4),(3,6,152)]),(8,[(0,1,4),(3,6,152)]),(2,[(1,0,3),(0,1,4),(3,6,152)]),(15,[(0,1,4)]),(8,[(2,2,3),(2,145,5)]),(14,[(2,145,5)]),(5,[(1,41,0),(2,145,5)]),(9,[(1,3,4),(2,4,5)]),(7,[(1,3,4),(2,4,5)]),(4,[(0,1,2),(1,203,5)]),(16,[(1,203,5)]),(2,[(0,1,2),(2,0,4),(3,0,4)]),(5,[(0,1,2),(1,203,5)]),(1,[(0,0,1),(1,0,1),(0,18,4),(1,18,4)]),(16,[(0,0,1),(1,0,1)]),(0,[(0,0,1),(1,0,1),(0,18,4),(1,18,4)]),(2,[(0,0,1),(1,0,1)]),(2,[(0,0,1),(1,0,1),(1,18,4)]),(7,[(1,18,4),(2,104,5)]),(3,[(0,0,1),(1,0,1)]),(1,[(0,0,1),(1,0,1)]),(9,[(1,18,4),(2,104,5)]),(5,[(0,0,2)]),(9,[(1,18,3),(2,4,5)]),(6,[(0,0,1),(1,0,1),(0,18,4)]),(9,[(1,3,4),(0,2,38)]),(0,[(0,0,1),(1,0,1),(0,2,38)]),(7,[(1,3,4),(0,2,38)]),(2,[(0,0,1),(1,0,1),(1,3,4),(0,2,38)]),(3,[(2,1,0),(3,129,158)]),(6,[(2,1,0),(3,129,158)]),(7,[(0,2,4)]),(1,[(2,1,0),(1,1,90),(3,129,158)]),(2,[(2,0,1),(0,2,4),(1,0,90)]),(14,[(2,145,1)]),(2,[(2,2,3),(1,41,0),(2,145,1)]),(7,[(1,18,4)]),(2,[(0,0,1),(1,0,1),(1,18,4),(3,17,104)]),(1,[(0,0,1),(1,0,1),(1,18,4),(3,17,104)]),(9,[(0,18,4),(1,31,5)]),(7,[(0,18,4),(1,31,5)]),(2,[(0,0,1),(1,0,1),(0,18,4)]),(2,[(0,0,1),(1,0,1),(1,18,3)]),(7,[(1,18,3),(2,19,5)]),(0,[(0,0,1),(1,0,1),(2,19,5)]),(9,[(1,18,3),(2,19,5)]),(9,[(1,18,3),(0,19,4)]),(7,[(1,18,3),(0,19,4)]),(6,[(0,0,1),(1,0,1),(0,19,4)]),(7,[(2,4,5),(1,37,3)]),(3,[(0,0,1),(1,0,1),(1,18,3)]),(4,[(0,0,1),(1,0,1),(1,18,3)]),(0,[(0,0,1),(1,0,1),(2,18,5)]),(9,[(0,2,4),(1,90,5)]),(2,[(0,0,1),(1,0,1),(0,2,4)]),(2,[(0,2,4),(1,0,90),(0,1,140)]),(3,[(2,140,5)]),(0,[(1,1,5),(0,4,36),(1,0,61)]),(5,[(1,1,5)]),(14,[(1,1,5)]),(6,[(0,0,1),(1,0,1),(3,17,19)]),(1,[(0,0,1),(1,0,1),(1,18,3),(3,17,19)]),(8,[(0,18,4),(1,31,5)]),(4,[(1,1,0)]),(2,[(1,1,0),(0,18,4),(3,1,125)]),(9,[(2,2,3),(3,41,4)]),(7,[(2,2,3),(3,41,4)]),(1,[(0,0,1),(1,0,1),(3,41,4)]),(0,[(2,0,1),(0,4,79),(1,186,194)]),(5,[(2,0,1),(1,186,194)]),(2,[(2,0,1),(0,4,79),(1,186,194)]),(9,[(3,18,2),(2,4,5)]),(1,[(0,0,1),(1,0,1),(2,4,5)]),(2,[(0,0,1),(1,0,1),(3,18,2)]),(9,[(2,4,5),(1,37,18)]),(2,[(0,0,1),(1,0,1),(1,37,18)]),(7,[(0,86,4),(1,0,215)]),(1,[(1,1,3),(0,86,4),(1,0,215)]),(8,[(1,1,3),(0,86,4)]),(5,[(2,0,5),(1,0,215)]),(9,[(2,2,3),(1,41,5)]),(7,[(2,2,3),(1,41,5)]),(17,[(0,0,1),(1,0,1)]),(2,[(0,0,1),(1,0,1),(2,2,3)]),(9,[(1,18,4),(0,2,104)]),(0,[(0,0,1),(1,0,1),(1,18,4),(0,2,104)]),(2,[(0,0,1),(1,0,1),(1,18,4),(0,2,104)]),(7,[(1,18,4),(0,2,104)]),(9,[(2,2,5),(1,111,17)]),(0,[(0,0,1),(1,0,1),(2,2,5),(1,111,17)]),(6,[(0,0,1),(1,0,1)]),(9,[(2,2,3),(2,4,5)]),(0,[(0,0,1),(1,0,1),(3,18,38)]),(2,[(0,0,1),(1,0,1),(1,3,4),(3,18,38)]),(1,[(0,0,1),(1,0,1),(1,3,4),(3,18,38)]),(6,[(0,0,1),(1,0,1),(3,18,38)]),(2,[(2,0,36),(1,220,1),(0,4,36)]),(7,[(2,0,36)]),(1,[(1,1,5),(2,0,36),(1,220,1)]),(2,[(1,1,0),(3,1,29),(3,0,29)]),(9,[(1,18,5),(3,1,29)]),(9,[(0,18,4),(1,3,5)]),(4,[(1,1,5),(0,2,36),(1,0,162)]),(2,[(2,0,4),(0,2,36),(1,0,162)]),(0,[(2,1,0),(1,129,5)]),(5,[(2,1,0),(1,129,5)]),(8,[(1,129,5)]),(15,[(2,1,0)]),(1,[(0,0,1),(1,17,90)]),(4,[(0,0,1),(1,17,90)]),(5,[(1,8,0)]),(1,[(0,1,4),(1,1,4),(3,6,7),(1,8,0)]),(0,[(0,0,1),(1,0,1),(2,18,4),(3,18,4)]),(1,[(0,0,1),(1,0,1),(2,18,4),(3,18,4)]),(2,[(0,0,1),(1,0,1),(2,18,4),(3,18,4)]),(0,[(1,1,5),(3,0,36),(3,156,38)]),(9,[(2,2,4),(1,224,5)]),(1,[(0,0,1),(1,0,1),(1,224,5)]),(7,[(2,2,4),(1,224,5)]),(5,[(3,8,0)]),(2,[(0,1,4),(1,1,4),(3,6,7),(3,8,0)]),(1,[(0,1,4),(1,1,4),(3,6,7),(3,8,0)]),(7,[(3,18,4)]),(8,[(1,4,14)]),(2,[(3,1,14),(1,4,14),(3,0,58)]),(2,[(0,2,4)]),(5,[(1,0,1),(3,31,79)]),(9,[(1,18,5),(0,4,29)]),(7,[(1,18,5),(0,4,29)]),(4,[(2,0,1)]),(1,[(1,90,5),(3,1,149)]),(0,[(2,1,4),(3,1,4),(1,72,69),(1,69,5)]),(1,[(2,1,4),(3,1,4),(1,72,69),(1,69,5)]),(5,[(1,69,5)]),(5,[(1,69,0)]),(2,[(2,1,4),(3,1,4),(1,72,69),(1,69,0)]),(1,[(2,1,4),(3,1,4),(1,72,69),(1,69,0)]),(9,[(0,18,2),(1,231,5)]),(1,[(0,0,1),(1,0,1),(1,231,5)]),(2,[(0,0,1),(1,0,1),(0,18,2)]),(7,[(0,18,2),(1,231,5)]),(7,[(1,3,4),(0,18,38)]),(6,[(0,0,1),(1,0,1),(0,18,38)]),(1,[(0,0,1),(1,0,1),(1,3,4),(0,18,38)]),(0,[(0,0,1),(1,0,1),(0,18,38)]),(0,[(1,0,1),(0,4,79),(2,18,194)]),(9,[(2,18,5),(1,108,3)]),(2,[(0,0,1),(1,0,1),(1,108,3)]),(7,[(2,18,5),(1,108,3)]),(2,[(1,0,3),(0,152,4)]),(8,[(3,1,14)]),(15,[(3,1,14)]),(0,[(0,0,1),(3,17,38),(2,4,5)]),(9,[(0,2,4),(1,17,90)]),(0,[(0,0,1),(1,0,1),(0,2,4),(1,17,90)]),(8,[(0,18,4),(1,31,3),(1,18,5)]),(0,[(1,0,1),(0,18,4)]),(2,[(1,0,1),(0,18,4),(1,31,3)]),(4,[(1,0,1),(1,31,3)]),(7,[(1,3,4),(2,38,5)]),(9,[(1,3,4),(2,38,5)]),(2,[(1,0,3),(0,1,4),(3,1,153)]),(7,[(2,4,5),(3,0,238)]),(9,[(2,4,5),(1,37,1),(3,0,238)]),(2,[(2,0,1),(1,37,1),(3,0,238)]),(8,[(0,18,4),(1,18,4),(0,2,104)]),(3,[(1,0,1),(0,18,4)]),(5,[(1,0,1)]),(8,[(1,1,5),(0,4,29)]),(2,[(1,0,4),(1,0,36),(0,4,29)]),(15,[(1,0,1)]),(0,[(1,0,1),(1,18,5),(0,38,29)]),(15,[(3,0,36),(3,156,4)]),(1,[(1,90,5)]),(1,[(0,0,1),(1,0,1),(1,123,17)]),(0,[(0,0,1),(1,0,1),(3,18,2),(1,123,17)]),(7,[(3,3,4),(2,242,5)]),(0,[(2,0,1),(1,186,1)]),(2,[(2,0,1),(1,186,1)]),(7,[(3,3,4),(2,4,5)]),(4,[(1,3,5)]),(1,[(1,203,5),(0,0,4),(1,0,4)]),(2,[(0,1,2),(0,0,4),(1,0,4)]),(7,[(0,0,4),(1,0,4)]),(4,[(1,1,5),(1,0,36)]),(2,[(1,0,36),(3,4,36),(3,244,29)]),(0,[(1,0,1),(2,4,5),(3,37,19)]),(2,[(0,1,4),(1,6,3),(0,2,14)]),(1,[(0,1,4),(1,6,3)]),(1,[(0,1,4),(1,6,3),(1,0,5)]),(3,[(0,1,4),(1,6,3)]),(2,[(0,0,1),(1,0,1),(3,3,4)]),(9,[(3,3,4),(2,4,5)]),(0,[(2,4,5)]),(1,[(2,1,0),(1,129,5),(1,0,4),(3,1,25)]),(3,[(1,0,4),(3,1,25)]),(7,[(0,86,4),(1,186,215)]),(26,[]),(7,[(0,86,4),(1,215,5)]),(4,[(3,1,2),(1,23,5)]),(5,[(3,1,2),(1,23,5)]),(2,[(3,1,2),(1,0,4),(0,25,249)]),(1,[(1,203,5),(1,0,4),(3,1,25)]),(7,[(2,0,5),(3,0,204)]),(2,[(1,0,1),(1,18,3),(0,19,4)]),(3,[(1,4,5),(0,197,190)]),(2,[(3,1,2),(1,23,0),(0,197,190)]),(8,[(0,152,4),(1,222,5)]),(1,[(1,23,0),(1,4,5),(3,1,190)]),(3,[(1,4,5),(3,1,190)]),(2,[(3,1,2),(1,23,0),(3,1,190)]),(0,[(1,4,5),(3,1,190)]),(2,[(3,1,2),(3,1,14)]),(7,[(1,23,5),(1,0,5)]),(1,[(1,23,5),(1,0,5),(3,1,14)]),(0,[(3,1,2),(1,23,5),(1,0,5),(3,1,14)]),(6,[(1,0,5),(3,1,14)]),(0,[(3,1,152),(3,1,4),(1,69,0)]),(5,[(3,1,152),(1,69,0)]),(2,[(1,0,3),(3,1,152),(3,1,4),(1,69,0)]),(8,[(1,1,5),(0,4,36)]),(1,[(1,23,0),(1,0,5),(3,1,14)]),(5,[(1,1,5),(2,152,61)]),(2,[(1,0,3),(0,4,36),(2,152,61)]),(5,[(2,1,5),(1,54,222)]),(2,[(1,0,3),(0,152,4),(1,54,222)]),(2,[(1,0,1),(3,1,14)]),(7,[(1,0,5),(2,18,5)]),(0,[(1,0,1),(1,0,5),(3,1,14),(2,18,5)]),(0,[(1,0,1),(0,18,4),(1,18,4),(3,31,104)]),(2,[(1,0,1),(0,18,4),(1,18,4),(3,31,104)]),(8,[(1,115,5),(0,25,258)]),(5,[(3,0,2),(1,115,5)]),(2,[(3,0,2),(1,0,4),(0,25,258)]),(0,[(3,1,2),(0,0,4),(1,0,4),(3,24,25)]),(5,[(3,1,2)]),(2,[(3,1,2),(0,0,4),(1,0,4),(3,24,25)]),(1,[(1,23,5),(1,0,4),(3,1,25)]),(0,[(1,0,4),(3,1,25)]),(2,[(3,1,2),(1,0,4),(3,1,25)]),(0,[(1,0,5)]),(2,[(0,1,14),(3,65,4)]),(0,[(1,1,5)]),(25,[]),(2,[(1,1,3)]),(0,[(1,1,5),(3,0,36),(3,156,4)]),(2,[(3,0,36),(3,156,4)]),(2,[(2,0,3),(0,4,36),(1,260,61)]),(7,[(0,4,36),(1,186,61)]),(2,[(2,0,1),(0,4,36),(1,186,61)]),(8,[(1,3,4),(3,1,38)]),(0,[(2,0,1),(3,1,38),(1,226,0)]),(2,[(2,0,1),(1,3,4),(3,1,38),(1,226,0)]),(1,[(2,0,1),(1,3,4),(3,1,38),(1,226,0)]),(6,[(2,0,1),(3,1,38),(1,226,0)]),(7,[(0,2,117),(1,0,118)]),(1,[(0,1,4),(1,6,3),(1,0,118)]),(14,[(1,0,118)]),(4,[(1,6,3),(0,2,117),(1,0,118)]),(15,[(1,0,118)]),(5,[(0,8,0)]),(1,[(0,1,4),(1,1,4),(3,6,7),(0,8,0)]),(0,[(0,0,1),(1,0,1),(2,242,5)]),(9,[(3,3,4),(2,242,5)]),(5,[(2,26,1)]),(2,[(0,0,4),(1,0,4),(3,24,25),(2,26,1)]),(1,[(0,0,4),(1,0,4),(3,24,25),(2,26,1)]),(5,[(3,1,189)]),(2,[(1,37,3),(3,1,189)]),(8,[(2,4,5),(3,37,1)]),(13,[(1,265,0)]),(7,[(2,4,5)]),(3,[(2,4,5)]),(1,[(2,4,5)]),(2,[(3,37,1),(1,265,0)]),(8,[(2,4,5)]),(7,[(2,4,5),(1,37,0)]),(2,[(1,37,0),(2,208,1)]),(13,[(2,208,1)]),(4,[(1,37,0),(2,208,1)]),(8,[(2,4,5),(2,208,1)]),(1,[(2,4,5),(1,37,0),(2,208,1)]),(5,[(1,254,0)]),(2,[(3,1,190),(1,254,0)]),(1,[(1,3,5),(0,4,79),(1,0,194)]),(5,[(1,0,194)]),(13,[(1,3,5)]),(7,[(1,3,5)]),(14,[(1,0,194)]),(2,[(0,4,79),(1,0,194)]),(5,[(3,1,79),(1,180,0)]),(8,[(3,3,4),(2,242,5)]),(2,[(3,3,4),(1,243,0)]),(7,[(1,3,4),(1,226,5)]),(0,[(3,1,38),(1,226,5)]),(2,[(1,3,4),(3,1,38)]),(3,[(2,173,4)]),(8,[(2,2,5)]),(4,[(2,2,5),(1,111,0)]),(16,[(1,111,0)]),(7,[(2,2,5),(1,111,0)]),(2,[(2,2,4),(3,1,225)]),(4,[(3,1,225)]),(3,[(2,274,1)]),(7,[(2,2,4),(1,224,0)]),(0,[(2,2,4),(1,224,0),(2,274,1)]),(5,[(2,274,1)]),(2,[(2,2,4),(1,224,0),(2,274,1)]),(2,[(0,2,4),(3,1,149)]),(13,[(3,1,149)]),(4,[(1,90,5),(3,1,149)]),(6,[(0,0,149)]),(2,[(0,2,4),(0,0,149)]),(3,[(3,1,140)]),(4,[(1,0,90)]),(2,[(0,2,4),(1,0,90)]),(13,[(3,1,140)]),(1,[(1,0,90),(3,1,140)]),(4,[(1,0,90),(3,1,140)]),(5,[(1,0,42)]),(1,[(3,41,4),(1,0,42)]),(8,[(2,2,3)]),(16,[(1,41,0)]),(17,[(2,4,5)]),(2,[(2,2,3),(1,41,0)]),(4,[(2,0,5)]),(8,[(1,3,4),(2,38,5)]),(6,[(2,0,5),(2,38,5)]),(1,[(2,0,5),(1,3,4),(2,38,5)]),(7,[(1,3,4)]),(6,[(2,1,5),(3,54,38)]),(1,[(2,1,5),(1,3,4),(3,54,38)]),(0,[(2,1,5),(3,54,38)]),(4,[(2,1,5)]),(2,[(1,3,4),(3,54,38)]),(6,[(2,0,5)]),(4,[(2,0,5),(1,0,90)]),(13,[(2,0,5)]),(7,[(1,0,277)]),(8,[(2,1,5),(3,54,4)]),(1,[(2,1,5),(3,54,4),(1,0,277)]),(2,[(3,54,4),(1,0,277)]),(0,[(2,0,5),(3,1,279)]),(8,[(3,1,279)]),(6,[(2,0,5),(3,1,279)]),(1,[(2,0,5),(1,142,3),(3,1,279)]),(2,[(1,142,3),(3,1,279)]),(8,[(2,1,5)]),(5,[(2,1,5),(1,54,0)]),(15,[(1,54,0)]),(7,[(3,3,4)]),(1,[(2,1,5),(1,54,0),(3,3,4)]),(3,[(3,3,4)]),(0,[(2,1,5),(1,54,0)]),(7,[(0,4,36),(1,0,61)]),(1,[(1,1,5),(0,4,36),(1,0,61)]),(7,[(3,3,36),(1,282,0)]),(2,[(3,3,36),(1,282,0)]),(5,[(1,1,5),(1,282,0)]),(2,[(1,3,4),(2,38,36)]),(2,[(2,4,36),(3,4,36)]),(1,[(1,0,5)]),(0,[(1,0,5),(3,1,38)]),(1,[(1,3,4),(3,1,38)]),(3,[(1,1,5)]),(8,[(2,2,4)]),(2,[(2,2,4),(1,224,0)]),(16,[(1,1,5)]),(2,[(0,2,4),(3,90,14)]),(4,[(1,0,5),(3,90,14)]),(8,[(0,2,4),(1,90,14)]),(4,[(1,0,5),(1,90,14)]),(2,[(0,2,4),(1,90,14)]),(3,[(2,173,1)]),(6,[(2,173,1)]),(2,[(1,111,0),(2,173,1)]),(8,[(2,2,5),(2,173,1)]),(1,[(1,1,5),(1,0,90)]),(0,[(1,1,5),(1,41,0)]),(17,[(1,1,5)]),(4,[(2,2,3),(1,41,0)]),(2,[(3,1,14),(1,4,14)]),(7,[(1,0,5),(1,4,14)]),(4,[(1,0,5),(3,1,14)]),(1,[(1,1,5)]),(1,[(1,1,5),(0,4,36)]),(3,[(1,1,5),(0,4,36)]),(15,[(0,4,36)]),(0,[(1,1,5),(0,4,36)]),(15,[(2,0,36)]),(0,[(1,1,5),(2,0,36)]),(8,[(1,1,5)]),(2,[(2,0,36),(3,0,36)]),(7,[(0,2,36),(1,0,162)]),(1,[(1,1,5),(1,0,162)]),(6,[(1,1,5)]),(2,[(0,2,36),(1,0,162)]),(8,[(1,1,5),(0,2,36)]),(1,[(3,3,4)]),(2,[(0,0,36),(2,4,36)]),(8,[(1,1,5),(1,3,36)]),(2,[(1,3,36)]),(7,[(1,3,36)]),(1,[(1,1,5),(1,3,36)]),(3,[(1,1,5),(1,3,36)]),(0,[(1,1,5),(0,0,36)]),(4,[(1,1,5),(1,3,36)]),(15,[(0,0,36)]),(4,[(1,1,5),(0,0,36)]),(16,[(1,0,5)]),(0,[(1,0,5),(0,1,14),(3,65,4)]),(8,[(1,3,5)]),(1,[(1,3,5),(3,0,79)]),(7,[(1,3,5),(3,0,79)]),(14,[(3,1,4)]),(1,[(3,1,4)]),(5,[(3,170,79)]),(8,[(1,3,5),(3,170,79)]),(2,[(3,0,4),(3,170,79)]),(6,[(3,1,4)]),(2,[(3,1,4)]),(2,[(3,0,36)]),(2,[(3,1,4),(3,0,36)]),(3,[(1,1,5),(3,0,36)]),(1,[(1,1,5),(3,0,36)]),(0,[(1,1,5),(3,0,36)]),(15,[(3,0,36)]),(7,[(3,0,36)]),(2,[(3,1,4),(1,142,69)]),(8,[(3,1,4)]),(4,[(2,0,5),(1,142,69)]),(0,[(3,1,4)]),(15,[(3,1,4)]),(7,[(2,69,5),(1,160,0)]),(2,[(3,1,4),(1,160,0)]),(2,[(3,0,4),(1,294,0)]),(8,[(2,170,5)]),(7,[(1,69,5)]),(2,[(1,4,14),(3,1,58)]),(0,[(3,0,4),(3,1,296)]),(2,[(3,1,4),(1,69,0)]),(8,[(3,1,4),(2,135,5)]),(13,[(2,135,5)]),(7,[(1,69,0)]),(4,[(1,69,0)]),(7,[(1,69,0),(2,135,5)]),(7,[(1,69,0),(1,135,5)]),(2,[(3,0,4),(2,2,36)]),(3,[(3,0,4)]),(3,[(2,0,4)]),(2,[(3,1,14),(1,3,14)]),(4,[(1,0,5),(1,3,14)]),(11,[]),(0,[(1,0,5),(3,1,14)]),(4,[(1,1,5),(0,2,36)]),(2,[(2,0,4),(0,2,36)]),(1,[(2,0,4)]),(1,[(2,0,4),(1,1,5)]),(8,[(2,1,4),(3,72,14)]),(1,[(2,1,4),(1,0,5),(3,72,14)]),(2,[(2,1,4),(3,72,14)]),(4,[(1,170,1)]),(1,[(2,0,4),(3,0,4),(1,170,1)]),(5,[(1,170,1)]),(2,[(2,0,4),(3,0,4)]),(2,[(2,0,4),(3,1,302)]),(8,[(3,1,302)]),(7,[(2,0,4)]),(5,[(2,1,5)]),(2,[(2,0,4),(1,54,168)]),(4,[(1,305,0)]),(2,[(1,1,4),(1,305,0)]),(8,[(2,2,5),(3,111,25)]),(4,[(2,2,5)]),(3,[(1,1,4)]),(2,[(1,1,4),(1,111,0)]),(7,[(1,0,4)]),(8,[(2,1,5),(3,54,25)]),(1,[(1,0,4),(2,1,5),(3,54,25)]),(2,[(1,0,4),(3,54,25)]),(7,[(1,0,4),(0,25,36)]),(1,[(1,0,4),(1,1,5),(0,25,36)]),(7,[(1,0,36)]),(2,[(1,0,4),(1,0,36)]),(8,[(1,1,4)]),(3,[(1,1,4),(3,0,7)]),(0,[(1,1,4),(3,0,7)]),(2,[(1,1,4),(3,0,7)]),(8,[(3,1,25),(2,246,5)]),(2,[(1,0,4),(3,1,25)]),(4,[(2,246,5)]),(2,[(1,0,4)]),(2,[(1,0,4),(3,1,14)]),(8,[(3,1,25)]),(4,[(2,2,5),(1,111,24)]),(6,[(0,0,4)]),(13,[(2,2,5)]),(2,[(1,3,14),(0,4,14)]),(7,[(1,0,5),(0,4,14)]),(4,[(2,2,3),(1,41,1)]),(7,[(2,2,3)]),(8,[(2,2,3),(1,41,1)]),(17,[(0,0,4)]),(5,[(1,41,1)]),(2,[(2,2,3),(1,41,1)]),(2,[(0,0,4)]),(7,[(3,4,36),(1,244,0)]),(2,[(3,4,36),(1,244,0)]),(4,[(2,1,5),(1,54,3)]),(7,[(0,0,4)]),(3,[(2,1,5),(1,54,3)]),(1,[(2,1,5),(1,54,3)]),(0,[(2,1,5)]),(8,[(2,1,5),(1,54,3)]),(2,[(0,0,4),(1,54,3)]),(14,[(0,0,4)]),(4,[(2,1,5),(1,54,24)]),(2,[(0,0,4),(1,54,24)]),(0,[(0,0,4),(2,1,5),(1,54,24)]),(5,[(2,1,5),(1,54,24)]),(0,[(0,1,4)]),(0,[(0,1,4),(1,0,5)]),(2,[(0,1,4)]),(7,[(1,0,5),(3,3,14)]),(3,[(0,1,4)]),(1,[(0,1,4)]),(8,[(3,3,14)]),(1,[(1,0,5),(3,3,14)]),(2,[(0,1,4),(3,3,14)]),(7,[(0,2,36)]),(2,[(0,2,36)]),(2,[(0,0,4),(0,2,36)]),(1,[(0,0,4)]),(1,[(0,0,4),(1,1,5)]),(5,[(3,1,79)]),(13,[(1,3,5),(3,1,79)]),(2,[(3,1,4),(3,1,79)]),(2,[(2,2,3)]),(2,[(0,0,4),(2,2,3)]),(2,[(0,1,4),(3,6,14)]),(0,[(0,1,4),(1,0,5),(3,6,14)]),(4,[(1,0,5),(3,6,14)]),(5,[(1,0,5),(3,6,14)]),(5,[(3,1,79),(3,180,0)]),(2,[(0,1,4),(1,1,4)]),(7,[(2,0,5)]),(3,[(0,1,4),(1,1,4)]),(8,[(0,1,4),(1,1,4)]),(1,[(0,1,4),(1,1,4)]),(2,[(0,0,4),(1,0,4)]),(0,[(0,1,4),(3,6,4),(1,69,5)]),(2,[(0,1,4),(3,6,4)]),(0,[(0,0,4),(3,1,202)]),(8,[(3,1,202)]),(6,[(0,0,4),(3,1,202)]),(1,[(0,0,4),(1,24,3),(3,1,202)]),(5,[(3,1,202)]),(2,[(0,0,4),(1,24,3),(3,1,202)]),(2,[(0,2,36),(3,162,4)]),(1,[(1,1,5),(3,162,4)]),(4,[(1,24,3),(2,2,5)]),(2,[(1,1,4),(3,1,14)]),(8,[(0,2,202)]),(13,[(0,2,202)]),(4,[(1,24,3),(0,2,202)]),(2,[(0,0,4),(1,24,3),(0,2,202)]),(1,[(3,41,4)]),(0,[(2,0,5),(3,41,4)]),(1,[(2,0,5)]),(1,[(2,0,5),(3,41,4)]),(1,[(0,0,4),(1,24,3),(1,1,5)]),(4,[(1,24,3),(1,1,5)]),(8,[(0,1,4),(1,6,3)]),(7,[(0,0,117)]),(13,[(0,0,117)]),(1,[(0,1,4),(1,6,3),(0,0,117)]),(4,[(1,6,3),(0,0,117)]),(2,[(0,0,36),(1,0,36)]),(7,[(0,0,36),(1,0,36)]),(1,[(0,1,4),(1,6,0),(1,3,5)]),(5,[(1,6,0)]),(2,[(0,1,4),(1,6,0)]),(8,[(0,1,4)]),(3,[(0,173,4)]),(6,[(0,173,4)]),(2,[(1,111,0),(0,173,4)]),(7,[(2,321,5)]),(0,[(0,1,4),(1,6,0),(2,321,5)]),(4,[(1,6,0),(2,321,5)]),(5,[(1,6,0),(2,321,5)]),(2,[(3,1,79),(1,180,0)]),(7,[(1,3,5),(1,180,0)]),(14,[(2,0,5)]),(0,[(0,1,4),(1,6,0),(2,0,5)]),(4,[(1,6,0),(2,0,5)]),(5,[(1,6,0),(2,0,5)]),(4,[(1,1,5),(1,160,1)]),(2,[(2,4,36),(1,160,1)]),(0,[(2,4,5),(1,37,1)]),(2,[(2,0,3),(1,37,1)]),(0,[(2,1,5),(1,54,260)]),(7,[(2,0,3)]),(6,[(2,1,5),(1,54,260)]),(1,[(2,0,3),(2,1,5),(1,54,260)]),(2,[(2,0,3),(1,54,260)]),(1,[(1,1,5),(1,1,90)]),(4,[(1,1,5),(1,1,90)]),(2,[(0,2,4),(1,1,90)]),(8,[(3,1,4),(2,69,5)]),(13,[(2,0,3)]),(1,[(2,0,3)]),(0,[(3,1,4),(2,69,5)]),(1,[(3,1,4),(2,69,5)]),(3,[(3,1,4),(2,69,5)]),(2,[(2,0,3),(3,1,4)]),(0,[(3,1,4),(1,69,0)]),(2,[(2,0,3),(3,1,4),(1,69,0)]),(1,[(2,0,3),(3,1,4),(1,69,0)]),(6,[(3,1,4),(1,69,0)]),(0,[(0,1,4),(1,6,5)]),(3,[(0,1,4),(1,6,5)]),(1,[(0,1,4),(1,6,5)]),(8,[(0,1,4),(1,6,5)]),(4,[(1,6,5)]),(5,[(1,6,5)]),(5,[(1,326,24)]),(6,[(0,0,4),(1,326,24)]),(1,[(2,1,3),(0,0,4),(1,326,24)]),(2,[(2,1,3),(0,0,4),(1,326,24)]),(8,[(2,1,3)]),(8,[(0,2,4),(1,1,90)]),(1,[(1,1,90)]),(4,[(1,1,90)]),(1,[(2,0,5),(1,1,90)]),(2,[(2,0,3),(0,4,36)]),(4,[(2,0,3)]),(7,[(2,0,3),(1,0,5)]),(0,[(1,0,5),(0,1,4)]),(1,[(2,0,3),(1,0,5)]),(2,[(2,0,3)]),(6,[(1,1,5),(3,326,36)]),(1,[(2,1,3),(1,1,5),(3,326,36)]),(0,[(1,1,5),(3,326,36)]),(0,[(1,0,5),(0,4,153)]),(2,[(1,3,14),(0,4,153)]),(8,[(1,3,14),(0,4,153)]),(3,[(3,1,4),(1,69,0)]),(1,[(3,1,4),(1,69,0)]),(7,[(1,329,5)]),(6,[(3,326,4),(1,329,5)]),(1,[(2,1,3),(3,326,4),(1,329,5)]),(0,[(3,326,4),(1,329,5)]),(5,[(1,329,5)]),(2,[(2,1,3),(3,326,4)]),(0,[(3,326,4),(1,0,5)]),(3,[(2,1,3),(3,326,4)]),(1,[(2,1,3),(3,326,4)]),(1,[(2,1,3),(1,326,0)]),(0,[(1,326,0),(2,4,5)]),(2,[(2,1,3),(1,326,0)]),(7,[(2,331,5)]),(6,[(1,326,0),(2,331,5)]),(1,[(2,1,3),(1,326,0),(2,331,5)]),(0,[(1,326,0),(2,331,5)]),(5,[(2,152,5)]),(13,[(1,0,3),(2,152,5)]),(2,[(1,0,3)]),(8,[(1,152,5),(3,1,153)]),(1,[(1,0,3),(1,152,5),(3,1,153)]),(0,[(1,152,5),(3,1,153)]),(2,[(1,0,3),(3,1,153)]),(0,[(3,1,4),(1,0,5)]),(4,[(1,0,5),(3,3,14)]),(2,[(3,3,14)]),(2,[(3,1,4),(3,3,14)]),(4,[(1,0,5),(1,90,5)]),(7,[(3,86,4),(1,334,0)]),(8,[(0,152,4),(1,1,222)]),(0,[(0,152,4),(1,1,222)]),(5,[(1,1,222)]),(15,[(1,1,222)]),(1,[(1,0,3),(0,152,4),(1,1,222)]),(1,[(1,0,3),(0,152,4),(1,222,5)]),(6,[(0,152,4),(1,222,5)]),(0,[(0,152,4),(1,222,5)]),(4,[(1,0,3),(1,222,5)]),(5,[(1,222,5)]),(2,[(0,0,4),(1,3,36)]),(8,[(1,3,4),(0,152,4)]),(1,[(1,0,3),(1,3,4),(0,152,4)]),(6,[(0,152,4)]),(0,[(0,152,4)]),(3,[(2,145,1)]),(17,[]),(8,[(2,2,3),(2,145,1)]),(5,[(1,41,0),(2,145,1)]),(2,[(1,1,3),(0,86,4)]),(7,[(0,86,4)]),(1,[(1,1,3),(0,86,4)]),(3,[(1,1,3),(0,86,4)]),(0,[(2,0,5),(0,86,4)]),(3,[(2,0,5)]),(0,[(2,1,5),(3,54,4)]),(13,[(1,0,3)]),(2,[(1,0,3),(3,54,4)]),(7,[(1,0,3)]),(3,[(2,1,5),(3,54,4)]),(1,[(2,1,5),(3,54,4)]),(1,[(1,0,3)]),(7,[(1,0,3),(0,152,36)]),(2,[(1,0,3),(0,152,36)]),(1,[(1,0,3),(1,1,5),(0,152,36)]),(6,[(1,1,5),(0,152,36)]),(2,[(3,1,14),(3,175,4)]),(7,[(1,0,5),(3,175,4)]),(0,[(1,1,5),(0,152,4)]),(8,[(0,152,4)]),(7,[(1,0,3),(0,152,4)]),(1,[(1,0,3),(0,152,4)]),(4,[(2,0,3),(1,260,5)]),(3,[(2,0,3),(1,260,5)]),(1,[(2,0,3),(1,260,5)]),(0,[(1,260,5)]),(0,[(1,260,5),(3,1,4)]),(7,[(2,0,3),(1,260,5)]),(5,[(1,260,5)]),(3,[(3,1,4)]),(3,[(1,0,3),(2,152,5)]),(1,[(1,0,3),(2,152,5)]),(7,[(1,0,3),(2,152,5)]),(8,[(1,152,5)]),(4,[(1,0,3),(1,152,5)]),(1,[(1,0,3),(1,152,5)]),(0,[(3,1,4),(1,152,5)]),(2,[(1,0,3),(3,1,4)]),(5,[(1,152,5)]),(4,[(1,170,5)]),(5,[(1,170,5)]),(0,[(3,1,4),(1,69,5)]),(8,[(3,1,4),(1,69,5)]),(3,[(3,1,4),(1,69,5)]),(1,[(3,1,4),(1,69,5)]),(2,[(1,0,3),(0,4,36)]),(7,[(0,4,36)]),(4,[(1,0,3)]),(0,[(0,1,4),(2,152,5)]),(2,[(1,0,3),(0,1,4)]),(4,[(1,0,3),(1,6,5)]),(1,[(1,0,3),(3,1,152)]),(0,[(3,1,152)]),(7,[(1,0,3),(1,3,4)]),(6,[(3,1,152)]),(1,[(1,0,3),(3,1,152),(1,3,4)]),(4,[(1,0,3),(3,1,152)]),(2,[(1,0,3),(3,1,152),(1,3,4)]),(0,[(3,1,152),(2,255,5)]),(8,[(3,1,152),(2,255,5)]),(6,[(3,1,152),(2,255,5)]),(1,[(1,0,3),(3,1,152),(2,255,5)]),(8,[(2,2,5),(3,111,4)]),(2,[(3,1,4),(0,2,14)]),(4,[(3,170,1)]),(5,[(3,170,1)]),(1,[(2,0,4),(3,0,4),(3,170,1)]),(8,[(1,1,3)]),(0,[(1,1,5),(0,0,4)]),(8,[(1,1,3),(1,1,5)]),(4,[(1,1,3),(1,1,5)]),(4,[(1,0,3),(1,0,5)]),(8,[(2,2,3),(1,41,5)]),(4,[(2,2,3),(1,41,5)]),(1,[(1,41,5)]),(0,[(3,1,4),(1,41,5)]),(2,[(3,1,4),(2,2,3)]),(16,[(1,41,5)]),(17,[(3,1,4)]),(5,[(1,41,5)]),(13,[(1,0,1)]),(2,[(1,1,14),(0,4,29)]),(7,[(1,0,5),(0,4,29)]),(2,[(1,0,1),(3,18,79)]),(3,[(0,0,1)]),(1,[(0,0,1)]),(13,[(0,0,1)]),(0,[(0,0,1),(2,242,5)]),(2,[(0,0,1),(3,3,4)]),(1,[(3,3,4),(2,242,5)]),(3,[(3,3,4),(2,242,5)]),(8,[(1,1,5),(3,170,36)]),(2,[(3,0,4),(3,170,36)]),(0,[(1,0,1),(2,242,5)]),(2,[(1,0,1),(3,3,4)]),(2,[(0,0,4),(1,24,1)]),(7,[(1,23,0),(1,197,5)]),(0,[(3,1,2),(1,23,0),(1,197,5)]),(6,[(1,197,5)]),(2,[(3,1,2),(1,23,0)]),(1,[(1,3,5),(3,1,79)]),(1,[(1,0,5),(3,1,4)]),(13,[(3,1,2)]),(0,[(1,0,1)]),(8,[(1,3,4),(2,4,5)]),(0,[(1,0,1),(2,4,5)]),(3,[(1,3,4),(2,4,5)]),(1,[(1,3,4),(2,4,5)]),(1,[(1,1,3),(1,1,5)]),(3,[(1,1,3),(1,1,5)]),(2,[(0,0,36)]),(9,[(1,18,5)]),(7,[(1,18,5)]),(0,[(1,0,1),(3,18,38)]),(0,[(0,1,4),(3,6,152)]),(6,[(0,1,4),(3,6,152)]),(1,[(1,0,3),(0,1,4),(3,6,152)]),(5,[(3,6,152)]),(5,[(2,0,1),(1,186,5)]),(8,[(3,3,4)]),(7,[(1,186,5)]),(15,[(2,0,1)]),(1,[(2,0,1),(1,186,5),(3,3,4)]),(0,[(2,0,1),(1,186,5)]),(7,[(2,2,5),(3,111,4)]),(2,[(1,0,1)]),(7,[(1,18,5),(3,5,29)]),(8,[(1,18,5),(3,5,29)]),(2,[(1,3,14),(3,1,153)]),(0,[(1,0,5),(3,1,153)]),(17,[(1,0,5)]),(13,[(2,2,3)]),(3,[(1,4,5)]),(0,[(1,4,5)]),(4,[(1,90,5)]),(2,[(1,0,1),(0,2,4)]),(2,[(2,1,4),(1,72,0)]),(4,[(2,349,5)]),(7,[(2,349,5)]),(5,[(2,349,5)]),(7,[(1,0,3),(2,0,5)]),(1,[(1,0,3),(2,0,5)]),(3,[(1,0,3),(2,0,5)]),(0,[(2,0,5)]),(8,[(1,3,4),(0,18,38)]),(0,[(1,0,1),(0,18,38)]),(1,[(1,0,1),(1,3,4),(0,18,38)]),(6,[(1,0,1),(0,18,38)]),(1,[(1,1,0),(1,1,90)]),(4,[(1,1,0),(1,1,90)]),(13,[(1,1,0)]),(8,[(2,18,5)]),(1,[(0,0,4),(1,24,3)]),(7,[(2,4,5),(1,37,18)]),(2,[(1,0,1),(1,37,18)]),(8,[(2,4,5),(1,37,18)]),(3,[(1,0,1)]),(17,[(1,0,1)]),(2,[(1,0,1),(2,2,3)]),(1,[(1,0,1),(0,18,4),(1,31,5)]),(1,[(1,0,1),(3,41,4)]),(8,[(1,18,5),(0,4,29)]),(1,[(1,0,1),(1,18,5),(0,4,29)]),(16,[(1,0,1)]),(7,[(0,2,4),(2,18,90)]),(8,[(0,2,4),(2,18,90)]),(0,[(1,0,1),(0,2,4),(2,18,90)]),(6,[(1,0,1)]),(1,[(1,0,1),(2,18,90)]),(4,[(1,0,1),(2,18,90)]),(2,[(1,0,1),(0,2,4),(2,18,90)]),(0,[(0,0,4),(1,0,4),(2,2,5)]),(1,[(1,0,1),(1,18,5)]),(3,[(1,0,1),(1,18,5)]),(2,[(1,0,1),(3,4,29)]),(0,[(0,4,79)]),(0,[(0,0,1),(0,4,79)]),(5,[(0,0,1)]),(6,[(2,0,1)]),(2,[(2,0,1),(0,2,4)]),(13,[(2,0,1)]),(8,[(1,18,5)]),(2,[(1,0,1),(0,4,29)]),(9,[(1,3,5)]),(1,[(0,0,1),(1,0,1),(1,3,5)]),(5,[(1,0,215)]),(6,[(0,86,4),(1,0,215)]),(2,[(1,1,3),(0,86,4),(1,0,215)]),(0,[(1,0,1),(1,18,5)]),(7,[(1,349,5)]),(8,[(2,1,4),(1,349,5)]),(1,[(2,1,4),(1,72,0),(1,349,5)]),(5,[(1,349,5)]),(2,[(1,0,1),(1,18,3)]),(1,[(3,41,4),(1,42,5)]),(0,[(3,41,4),(1,42,5)]),(5,[(1,42,5)]),(2,[(1,0,3),(3,1,14)]),(7,[(1,0,3),(1,0,5)]),(7,[(2,2,5)]),(0,[(1,1,0),(2,2,5),(1,111,1)]),(6,[(1,1,0)]),(8,[(0,18,4),(1,31,3)]),(1,[(1,0,1),(0,18,4),(1,31,3)]),(7,[(0,0,4),(1,24,5)]),(1,[(0,0,4),(1,24,5),(1,1,5)]),(4,[(1,24,5),(1,1,5)]),(8,[(1,3,5),(3,129,79)]),(1,[(2,1,0),(1,3,5),(3,129,79)]),(0,[(2,1,0),(3,129,79)]),(2,[(3,1,14),(1,175,4)]),(7,[(1,0,5),(1,175,4)]),(7,[(3,0,4)]),(4,[(1,1,3),(1,170,1)]),(6,[(3,0,4),(1,170,1)]),(1,[(1,1,3),(3,0,4),(1,170,1)]),(2,[(3,0,4)]),(1,[(3,0,4),(1,1,5)]),(2,[(1,0,1),(2,18,4)]),(2,[(3,1,2)]),(2,[(3,1,2),(3,4,249)]),(5,[(0,0,1),(1,17,5)]),(3,[(0,0,1),(1,17,5)]),(1,[(0,0,1),(1,17,5)]),(2,[(0,0,1)]),(15,[(0,0,1)]),(0,[(0,0,1),(1,17,5)]),(8,[(3,3,4),(2,4,5)]),(3,[(3,3,4),(2,4,5)]),(1,[(3,3,4),(2,4,5)]),(1,[(1,81,1),(1,1,4)]),(7,[(0,0,2)]),(0,[(0,0,2),(1,81,1),(1,1,4)]),(5,[(0,0,2),(1,81,1)]),(2,[(0,0,2),(1,81,1),(1,1,4)]),(2,[(0,0,4),(3,1,355)]),(8,[(3,1,355)]),(9,[(2,4,5)]),(7,[(1,4,5),(0,18,190)]),(2,[(1,0,1),(0,18,190)]),(8,[(1,4,5),(0,18,190)]),(1,[(1,0,1),(1,4,5),(0,18,190)]),(7,[(1,362,5)]),(8,[(3,129,4),(1,362,5)]),(1,[(2,1,0),(3,129,4),(1,362,5)]),(0,[(2,1,0),(3,129,4),(1,362,5)]),(2,[(2,1,0),(3,129,4)]),(0,[(0,0,1)]),(2,[(0,0,1),(1,3,4)]),(0,[(0,0,1),(2,4,5)]),(4,[(2,1,3),(1,326,5)]),(3,[(2,1,3),(1,326,5)]),(1,[(2,1,3),(1,326,5)]),(0,[(1,326,5)]),(8,[(2,1,3),(1,326,5)]),(5,[(1,326,5)]),(2,[(2,1,3)]),(2,[(1,1,3),(3,1,14)]),(3,[(2,1,0),(1,129,5)]),(1,[(2,1,0),(1,129,5)]),(1,[(2,1,0),(1,129,5),(1,0,4)]),(3,[(1,0,4)]),(2,[(2,1,0)]),(2,[(2,1,0),(1,0,4)]),(2,[(0,0,4),(1,54,0)]),(8,[(3,18,4)]),(2,[(1,0,1),(3,18,190)]),(3,[(1,0,3),(1,0,5)]),(1,[(1,0,3),(1,0,5)]),(0,[(1,0,5),(3,1,4)]),(8,[(0,4,14)]),(7,[(3,18,4),(1,98,5)]),(2,[(1,0,1),(3,18,4)]),(8,[(3,18,4),(1,98,5)]),(1,[(1,0,1),(3,18,4),(1,98,5)]),(1,[(3,1,4),(1,69,81)]),(4,[(0,0,2),(1,69,81)]),(0,[(0,0,2),(3,1,4),(1,69,81)]),(7,[(0,0,2),(1,69,81)]),(2,[(0,0,2),(3,1,4),(1,69,81)]),(8,[(3,1,2)]),(3,[(2,0,1)]),(1,[(2,0,1),(2,4,5)]),(4,[(3,69,0),(1,70,5)]),(13,[(1,70,5)]),(1,[(3,1,4),(3,69,0),(1,70,5)]),(16,[(1,70,5)]),(5,[(1,0,1),(2,18,5)]),(2,[(2,0,36),(1,220,1)]),(0,[(2,0,4),(3,0,4),(2,2,5)]),(8,[(0,18,4)]),(7,[(0,18,4)]),(1,[(1,3,5)]),(1,[(1,0,1),(0,18,4)]),(2,[(2,4,36),(1,160,0)]),(4,[(1,1,5),(1,160,0)]),(3,[(2,197,4)]),(4,[(3,1,2),(1,23,0)]),(16,[(1,23,0)]),(8,[(0,18,4),(1,18,4)]),(1,[(1,0,1),(0,18,4),(1,18,4)]),(0,[(1,0,1),(0,18,4),(1,18,4)]),(8,[(1,18,4),(0,2,104)]),(8,[(1,18,3),(2,19,5)]),(5,[(1,0,1),(2,19,5)]),(4,[(2,0,5),(1,142,1)]),(13,[(2,0,5),(1,142,1)]),(1,[(2,0,5),(1,142,1)]),(1,[(3,1,4),(2,0,5),(1,142,1)]),(16,[(2,0,5),(1,142,1)]),(2,[(3,1,4),(1,142,1)]),(0,[(3,1,4),(2,0,5),(1,142,1)]),(8,[(1,18,3),(0,19,4)]),(6,[(1,0,1),(0,19,4)]),(1,[(1,0,1),(1,18,3),(0,19,4)]),(8,[(1,115,5)]),(4,[(3,0,2),(1,115,5)]),(0,[(3,0,2),(1,115,5)]),(2,[(3,0,2)]),(2,[(3,0,2),(3,1,4)]),(1,[(1,0,1),(2,4,5)]),(2,[(1,0,1),(3,18,2)]),(1,[(2,0,1)]),(0,[(2,0,1),(2,242,5)]),(2,[(2,0,1),(3,3,4)]),(4,[(2,0,5),(1,142,3)]),(3,[(2,0,5),(1,142,3)]),(1,[(2,0,5),(1,142,3)]),(0,[(3,1,4),(2,0,5)]),(2,[(1,142,3)]),(2,[(3,1,4),(1,142,3)]),(7,[(1,0,4),(1,246,5)]),(0,[(1,0,4),(3,1,25),(1,246,5)]),(1,[(1,0,4),(3,1,25),(1,246,5)]),(5,[(1,246,5)]),(3,[(0,1,4),(3,6,4)]),(1,[(0,1,4),(3,6,4)]),(7,[(3,18,2)]),(9,[(3,18,2)]),(0,[(2,0,1),(1,41,5)]),(17,[(2,0,1)]),(2,[(2,0,1),(2,2,3)]),(8,[(3,1,25),(1,1,5)]),(9,[(2,2,3)]),(1,[(0,0,1),(3,41,4)]),(0,[(0,0,1),(3,41,4)]),(2,[(1,0,1),(0,4,14)]),(9,[(1,4,5)]),(7,[(1,4,5)]),(0,[(0,0,1),(1,0,1),(1,4,5)]),(1,[(0,0,1),(1,0,1),(1,4,5)]),(8,[(1,3,4),(0,2,38)]),(0,[(1,0,5),(0,2,38)]),(2,[(1,3,4),(0,2,38)]),(17,[(0,0,1)]),(14,[(0,0,1)]),(2,[(0,0,1),(2,2,3)]),(3,[(2,145,5)]),(16,[(3,1,25)]),(1,[(1,0,4),(3,1,25)]),(0,[(0,1,2),(1,0,4),(3,1,25)]),(5,[(0,1,2)]),(2,[(1,0,1),(1,37,3)]),(7,[(1,331,5)]),(6,[(1,326,0),(1,331,5)]),(1,[(2,1,3),(1,326,0),(1,331,5)]),(0,[(1,326,0),(1,331,5)]),(8,[(2,1,3),(1,331,5)]),(5,[(1,326,0),(1,331,5)]),(8,[(2,4,5),(3,37,152)]),(2,[(1,0,3),(3,37,152)]),(6,[(2,4,5),(3,37,152)]),(1,[(1,0,3),(2,4,5),(3,37,152)]),(8,[(1,18,3)]),(3,[(1,0,1),(1,18,3)]),(1,[(1,0,1),(1,18,3)]),(0,[(1,0,1),(2,18,5)]),(4,[(1,0,1),(1,18,3)]),(0,[(0,0,1),(2,38,5)]),(1,[(1,3,4),(2,38,5)]),(7,[(2,2,5),(3,111,18)]),(1,[(1,0,1),(3,111,18)]),(8,[(2,2,5),(3,111,18)]),(2,[(1,0,1),(3,111,18)]),(0,[(1,0,1),(0,4,79)]),(2,[(0,0,2),(3,1,82)]),(8,[(3,1,82)]),(5,[(3,1,152)]),(13,[(1,0,3),(3,1,152)]),(6,[(3,1,152),(3,1,4)]),(1,[(1,0,3),(3,1,152),(3,1,4)]),(8,[(1,3,4)]),(4,[(0,0,1),(1,17,5)]),(2,[(1,1,14),(3,4,14)]),(8,[(1,1,14)]),(4,[(1,0,5),(1,1,14)]),(1,[(1,0,5),(1,1,14)]),(3,[(1,0,5),(1,1,14)]),(5,[(1,0,5),(1,1,14)]),(4,[(2,1,0)]),(5,[(2,1,0)]),(2,[(2,1,0),(3,129,190)]),(9,[(1,3,4)]),(1,[(0,0,1),(1,0,1),(1,3,4)]),(9,[(2,2,5)]),(9,[(0,2,4)]),(17,[(2,0,5)]),(15,[(0,0,4)]),(0,[(2,0,1),(0,86,4)]),(6,[(2,0,1),(0,86,4)]),(5,[(2,0,1)]),(2,[(2,0,1)]),(7,[(2,18,5)]),(9,[(2,18,5)]),(0,[(1,0,5),(3,41,4)]),(3,[(1,0,1),(2,18,4)]),(0,[(1,0,1),(2,18,4),(3,18,4)]),(1,[(1,0,1),(2,18,4),(3,18,4)]),(2,[(1,0,1),(2,18,4),(3,18,4)]),(8,[(0,4,14),(1,4,14)]),(1,[(1,0,5),(0,4,14),(1,4,14)]),(2,[(0,4,14),(1,4,14)]),(1,[(0,0,1),(1,41,5)]),(0,[(1,41,5)]),(0,[(0,0,1),(1,41,5)]),(2,[(1,0,4),(2,2,36)]),(1,[(1,0,4),(1,1,5)]),(8,[(0,2,14)]),(2,[(1,1,4),(0,2,14)]),(1,[(1,1,4)]),(1,[(1,1,4),(1,0,5)]),(7,[(2,2,5),(1,111,18)]),(1,[(1,0,1),(1,111,18)]),(8,[(2,2,5),(1,111,18)]),(2,[(1,0,1),(1,111,18)]),(1,[(2,4,5),(1,37,81)]),(9,[(0,18,4)]),(1,[(0,0,1),(1,0,1),(0,18,4)]),(7,[(3,0,2)]),(1,[(1,0,1),(1,115,1)]),(0,[(1,0,1),(3,0,2),(1,115,1)]),(8,[(1,115,1)]),(2,[(1,0,1),(3,0,2),(1,115,1)]),(9,[(3,18,4)]),(6,[(1,0,5)]),(0,[(1,0,1),(0,2,38)]),(7,[(2,18,3)]),(1,[(0,0,1),(1,0,1),(2,18,3)]),(9,[(2,18,3)]),(2,[(0,1,4),(1,6,3)]),(4,[(1,6,3)]),(1,[(0,1,4),(1,6,3),(2,0,5)]),(4,[(1,6,3),(2,0,5)]),(7,[(1,379,0)]),(1,[(3,203,4),(1,379,0)]),(0,[(0,1,2),(3,203,4),(1,379,0)]),(6,[(1,379,0)]),(2,[(0,1,2),(3,203,4),(1,379,0)]),(8,[(1,4,5)]),(2,[(0,0,1),(3,17,4)]),(7,[(1,381,5)]),(8,[(1,381,5)]),(0,[(0,0,1),(3,17,4),(1,381,5)]),(1,[(0,0,1),(3,17,4),(1,381,5)]),(1,[(0,1,4),(1,3,5),(3,1,79)]),(6,[(2,1,5),(3,54,152)]),(1,[(1,0,3),(2,1,5),(3,54,152)]),(0,[(2,1,5),(3,54,152)]),(8,[(2,1,5),(3,54,152)]),(5,[(2,1,5),(3,54,152)]),(2,[(1,0,3),(3,54,152)]),(9,[(1,18,3)]),(1,[(0,0,1),(1,0,1),(1,18,3)]),(6,[(0,1,4),(3,6,79)]),(1,[(0,1,4),(1,3,5),(3,6,79)]),(7,[(1,321,5)]),(8,[(0,1,4),(1,321,5)]),(1,[(0,1,4),(1,6,0),(1,321,5)]),(7,[(0,2,4),(1,18,90)]),(1,[(1,0,1),(1,18,90)]),(8,[(0,2,4),(1,18,90)]),(2,[(1,0,1),(0,2,4),(1,18,90)]),(4,[(1,0,1),(1,18,90)]),(8,[(0,1,2)]),(16,[(1,203,0)]),(6,[(2,4,5)]),(2,[(0,1,2),(1,203,0)]),(8,[(3,115,4),(1,388,5)]),(6,[(1,388,5)]),(4,[(3,0,2),(1,388,5)]),(2,[(3,0,2),(3,115,4)]),(4,[(2,0,5),(1,142,90)]),(8,[(0,18,2),(1,231,5)]),(1,[(1,0,1),(1,231,5)]),(2,[(1,0,1),(0,18,2)]),(9,[(1,18,4)]),(3,[(1,3,5),(0,4,79)]),(1,[(1,3,5),(0,4,79)]),(2,[(0,4,79)]),(2,[(1,0,1),(0,4,79)]),(9,[(0,18,2)]),(0,[(0,0,1),(1,0,1),(0,18,2)]),(7,[(0,18,2)]),(1,[(2,1,5),(1,54,81)]),(0,[(0,0,2),(2,1,5),(1,54,81)]),(6,[(2,1,5)]),(2,[(0,0,2),(1,54,81)]),(3,[(2,274,5)]),(5,[(2,274,5)]),(4,[(1,0,1),(1,170,1)]),(8,[(1,170,1)]),(3,[(1,3,5)]),(0,[(0,0,1),(3,17,4)]),(3,[(0,0,1),(3,17,4)]),(1,[(0,0,1),(3,17,4)]),(7,[(2,18,4)]),(9,[(2,18,4)]),(2,[(3,1,4),(1,3,14)]),(2,[(0,0,2),(0,1,4),(1,1,4)]),(8,[(0,2,4),(2,140,5)]),(13,[(2,140,5)]),(4,[(1,0,90),(2,140,5)]),(9,[(3,3,4)]),(1,[(0,0,1),(1,0,1),(3,3,4)]),(3,[(2,0,3),(1,0,5)]),(1,[(0,0,1),(1,90,5)]),(6,[(0,0,1)]),(2,[(0,0,1),(0,2,4)]),(0,[(0,0,1),(2,2,5),(1,111,17)]),(8,[(2,2,4),(1,224,5)]),(2,[(1,0,1),(2,2,4)]),(2,[(1,0,1),(1,0,3)]),(7,[(1,0,3),(2,18,5)]),(3,[(1,0,3)]),(2,[(3,0,2),(3,1,258)]),(6,[(3,1,258)]),(1,[(1,1,4),(3,115,7)]),(4,[(3,0,2)]),(7,[(3,0,2),(3,115,7)]),(5,[(3,0,2)]),(0,[(0,1,0),(3,1,38)]),(2,[(0,1,0),(1,3,4),(3,1,38)]),(1,[(0,1,0),(1,3,4),(3,1,38)]),(6,[(0,1,0),(3,1,38)]),(7,[(2,2,4)]),(9,[(2,2,4)]),(7,[(1,23,5)]),(1,[(1,23,5),(1,1,5)]),(0,[(3,1,2),(1,23,5),(1,1,5)]),(3,[(1,1,0)]),(1,[(1,1,0),(2,4,5)]),(0,[(0,2,38)]),(0,[(0,0,1),(0,2,38)]),(6,[(2,140,5)]),(3,[(2,387,5)]),(7,[(2,387,5)]),(0,[(0,1,2),(1,203,0),(2,387,5)]),(6,[(2,387,5)]),(2,[(1,0,1),(1,18,4)]),(2,[(1,1,0),(3,1,29)]),(1,[(1,0,1)]),(3,[(1,3,4),(2,38,5)]),(0,[(1,0,5),(3,1,152)]),(2,[(1,0,3),(3,1,152)]),(12,[]),(8,[(2,4,5),(1,37,3)]),(1,[(2,4,5),(1,37,3)]),(3,[(2,4,5),(1,37,3)]),(4,[(1,37,3)]),(2,[(1,37,3)]),(0,[(1,0,1),(3,1,152)]),(6,[(1,0,1),(3,1,152)]),(1,[(1,0,1),(1,0,3),(3,1,152)]),(8,[(1,4,5),(3,1,190)]),(2,[(1,1,0),(3,1,190)]),(0,[(1,1,0),(1,4,5),(3,1,190)]),(1,[(1,1,0),(1,4,5),(3,1,190)]),(5,[(1,1,0)]),(1,[(1,1,0),(1,18,5),(3,1,29)]),(0,[(2,1,0),(3,129,38)]),(2,[(2,1,0),(1,3,4),(3,129,38)]),(1,[(2,1,0),(1,3,4),(3,129,38)]),(6,[(2,1,0),(3,129,38)]),(10,[]),(7,[(1,0,329)]),(6,[(3,326,4),(1,0,329)]),(1,[(2,1,3),(3,326,4),(1,0,329)]),(0,[(3,326,4),(1,0,329)]),(2,[(2,1,3),(3,326,4),(1,0,329)]),(7,[(1,379,5)]),(1,[(3,203,4),(1,379,5)]),(0,[(0,1,2),(3,203,4),(1,379,5)]),(6,[(1,379,5)]),(2,[(0,1,2),(3,203,4)]),(1,[(3,203,4),(1,0,5)]),(6,[(0,0,1),(3,17,38)]),(1,[(0,0,1),(1,3,4),(3,17,38)]),(0,[(0,0,1),(3,17,38)]),(2,[(0,0,1),(1,3,4),(3,17,38)]),(0,[(1,0,1),(2,152,5)]),(4,[(1,1,5),(1,0,61)]),(0,[(3,1,4),(1,260,69)]),(4,[(2,0,3),(1,260,69)]),(6,[(3,1,4),(1,260,69)]),(1,[(2,0,3),(3,1,4),(1,260,69)]),(5,[(1,260,69)]),(2,[(2,0,3),(3,1,4),(1,260,69)]),(3,[(1,4,5),(3,0,190)]),(0,[(1,4,5),(3,0,190)]),(2,[(2,0,1),(3,0,190)]),(0,[(2,0,1),(1,4,5),(3,0,190)]),(1,[(2,0,1),(1,4,5),(3,0,190)]),(1,[(3,115,4),(1,0,4)]),(8,[(3,115,4)]),(0,[(3,0,2),(3,115,4),(1,0,4)]),(2,[(3,0,2),(3,115,4),(1,0,4)]),(0,[(2,4,5),(1,37,260)]),(2,[(2,0,3),(1,37,260)]),(2,[(0,0,1),(3,17,190)]),(16,[(1,41,1)]),(8,[(2,18,5),(1,108,3)]),(2,[(1,0,1),(1,108,3)]),(4,[(0,1,2),(1,203,24)]),(1,[(0,0,4),(1,203,24)]),(0,[(0,1,2),(0,0,4),(1,203,24)]),(13,[(0,1,2)]),(2,[(0,1,2),(0,0,4),(1,203,24)]),(1,[(1,203,5)]),(1,[(1,203,5),(2,0,4)]),(2,[(0,1,2),(2,0,4)]),(7,[(1,0,3),(1,255,5)]),(1,[(1,0,3),(3,1,152),(1,255,5)]),(0,[(3,1,152),(1,255,5)]),(8,[(3,1,152),(1,255,5)]),(5,[(3,1,152),(1,255,5)]),(0,[(2,0,1),(0,4,79)]),(2,[(2,0,1),(0,4,79)]),(7,[(1,0,4),(0,18,4)]),(1,[(1,0,1),(1,0,4),(0,18,4)]),(7,[(2,4,5),(3,37,18)]),(2,[(1,0,1),(3,37,18)]),(8,[(2,4,5),(3,37,18)]),(0,[(1,0,1),(2,4,5),(3,37,18)]),(4,[(1,0,1),(3,37,18)]),(5,[(1,0,1),(3,37,18)]),(7,[(1,0,5),(0,18,4)]),(3,[(2,197,5)]),(7,[(1,23,0),(2,197,5)]),(6,[(2,197,5)]),(0,[(2,0,1),(1,186,1),(2,18,5)]),(1,[(2,0,4),(1,168,23)]),(0,[(3,1,2),(2,0,4),(1,168,23)]),(2,[(3,1,2),(2,0,4),(1,168,23)]),(7,[(0,2,4),(1,186,90)]),(1,[(2,0,1),(1,186,90)]),(4,[(2,0,1),(1,186,90)]),(5,[(2,0,1),(1,186,1)]),(3,[(2,0,1),(1,186,1)]),(6,[(0,1,4)]),(13,[(0,0,2)]),(2,[(0,0,2),(0,1,4),(1,6,3)]),(14,[(0,0,2)]),(15,[(0,0,2)]),(4,[(0,0,2),(1,6,3)]),(4,[(2,0,1),(1,186,1)]),(7,[(1,3,5),(0,18,79)]),(0,[(1,0,1),(0,18,79)]),(8,[(1,3,5),(0,18,79)]),(2,[(1,0,1),(0,18,79)]),(8,[(3,129,4)]),(6,[(2,1,0),(3,129,4)]),(0,[(1,0,5),(2,152,5)]),(8,[(2,152,5)]),(6,[(1,0,5),(2,152,5)]),(1,[(1,0,3),(1,0,5),(2,152,5)]),(2,[(2,1,0),(3,129,4),(1,0,4)]),(1,[(2,1,0),(3,129,4),(1,0,4)]),(8,[(1,3,4),(0,38,14)]),(1,[(1,0,5),(1,3,4),(0,38,14)]),(6,[(1,0,5),(0,38,14)]),(0,[(1,0,5),(0,38,14)]),(1,[(1,4,5),(3,1,190)]),(2,[(0,1,2),(3,1,190)]),(1,[(2,1,0),(3,129,4),(1,3,4)]),(0,[(2,1,0),(3,129,4)]),(8,[(2,18,4),(1,97,5)]),(1,[(1,23,0),(3,1,4)]),(0,[(3,1,2),(1,23,0)]),(4,[(1,1,3),(1,86,5)]),(7,[(1,86,5)]),(1,[(1,1,3),(1,86,5)]),(8,[(1,1,3),(1,86,5)]),(5,[(1,86,5)]),(2,[(1,1,3),(0,0,4)]),(1,[(2,1,0),(3,129,4)]),(1,[(1,115,1),(1,1,5)]),(0,[(3,0,2),(1,115,1),(1,1,5)]),(8,[(1,115,1),(1,1,5)]),(6,[(2,1,0),(1,129,5)]),(1,[(2,0,1),(1,186,5)]),(6,[(2,0,1),(3,0,86)]),(5,[(3,170,86)]),(8,[(1,1,3),(3,170,86)]),(7,[(3,0,4),(3,170,86)]),(6,[(3,0,4),(3,170,86)]),(1,[(1,1,3),(3,0,4),(3,170,86)]),(2,[(1,1,3),(3,0,4),(3,170,86)]),(14,[(2,0,1)]),(0,[(2,0,1),(2,4,5)]),(2,[(1,0,4),(0,4,14)]),(14,[(1,255,5)]),(6,[(3,1,152),(1,255,5)]),(0,[(2,152,5)]),(0,[(2,1,0)]),(0,[(2,1,0),(2,152,5)]),(3,[(2,1,0)]),(1,[(2,1,0)]),(13,[(2,1,0)]),(14,[(2,1,0)]),(4,[(1,0,3),(2,152,5)]),(2,[(2,1,0),(1,0,3)]),(13,[(1,1,3)]),(15,[(1,37,0)]),(4,[(1,37,0)]),(2,[(2,0,1),(1,37,3)]),(14,[(1,411,0)]),(2,[(0,1,79),(1,411,0)]),(0,[(0,0,1),(1,17,5),(1,4,5)]),(1,[(0,0,1),(1,17,5),(1,4,5)]),(2,[(2,0,1),(1,1,4),(3,0,7)]),(1,[(2,0,1),(1,1,4),(3,0,7)]),(4,[(0,1,2)]),(2,[(1,1,14),(0,4,14)]),(2,[(0,0,1),(0,4,79)]),(7,[(1,0,4),(2,25,5)]),(8,[(2,25,5)]),(1,[(1,0,4),(2,25,5)]),(0,[(0,0,1),(0,2,4),(1,17,90)]),(3,[(1,0,3),(0,152,4)]),(2,[(2,0,1),(0,4,36)]),(16,[(2,0,1)]),(0,[(2,0,1)]),(0,[(3,1,38),(1,226,0)]),(2,[(1,3,4),(3,1,38),(1,226,0)]),(1,[(1,3,4),(3,1,38),(1,226,0)]),(6,[(3,1,38),(1,226,0)]),(2,[(3,1,2),(3,1,190)]),(0,[(3,1,2),(1,4,5),(3,1,190)]),(4,[(2,0,1),(1,186,5)]),(3,[(2,0,1),(1,186,5)]),(2,[(2,0,1),(3,1,4)]),(0,[(2,0,1),(3,41,4)]),(1,[(2,0,1),(3,41,4)]),(2,[(2,1,14),(3,413,4)]),(4,[(1,0,5),(2,1,14)]),(2,[(3,0,4),(3,1,340)]),(0,[(3,0,4),(1,170,5),(3,1,340)]),(1,[(3,0,4),(1,170,5),(3,1,340)]),(4,[(2,0,1),(1,0,90)]),(1,[(2,0,1),(1,0,90)]),(1,[(1,224,5)]),(1,[(2,0,1),(1,224,5)]),(2,[(2,2,4)]),(8,[(2,4,5),(1,37,1)]),(2,[(2,0,1),(1,37,1)]),(7,[(2,2,5),(1,111,186)]),(0,[(2,0,1),(0,2,38)]),(2,[(3,1,2),(1,37,23)]),(2,[(2,0,1),(1,3,4)]),(7,[(1,23,0)]),(0,[(1,1,4)]),(7,[(2,4,5),(1,37,186)]),(0,[(2,0,1),(3,1,38)]),(2,[(2,0,1),(1,3,4),(3,1,38)]),(1,[(2,0,1),(1,3,4),(3,1,38)]),(6,[(2,0,1),(3,1,38)]),(4,[(0,1,2),(1,203,0)]),(5,[(0,1,2),(1,203,0)]),(2,[(1,37,1),(0,238,0)]),(13,[(0,238,0)]),(4,[(1,37,1),(0,238,0)]),(2,[(0,0,1),(2,2,4)]),(1,[(0,0,1),(1,224,5)]),(7,[(1,387,5)]),(1,[(1,203,0),(1,387,5)]),(0,[(0,1,2),(1,203,0),(1,387,5)]),(6,[(1,387,5)]),(8,[(0,1,2),(1,387,5)]),(0,[(1,0,1),(0,18,4),(1,31,5)]),(4,[(1,0,1),(1,31,5)]),(4,[(0,0,2),(1,81,5)]),(1,[(1,81,5),(1,4,5)]),(0,[(0,0,2),(1,81,5),(1,4,5)]),(6,[(3,1,140)]),(8,[(0,2,4),(3,1,140)]),(1,[(1,203,5),(0,0,4)]),(0,[(0,1,2),(1,203,5)]),(2,[(0,1,2)]),(2,[(1,0,1),(1,0,4)]),(1,[(1,203,5),(1,0,4)]),(1,[(1,81,5),(3,1,4)]),(0,[(0,0,2),(1,81,5)]),(7,[(0,0,2),(1,81,5)]),(2,[(0,0,2)]),(2,[(0,0,2),(3,1,4)]),(16,[(1,81,5)]),(8,[(0,18,4),(1,18,5)]),(2,[(3,1,2),(1,142,23)]),(7,[(2,0,5),(1,142,23)]),(1,[(2,0,5),(1,142,23)]),(0,[(3,1,2),(2,0,5),(1,142,23)]),(1,[(1,203,5),(2,0,5)]),(0,[(0,1,2),(1,203,5),(2,0,5)]),(16,[(3,203,25)]),(0,[(0,1,2),(1,0,4),(3,203,25)]),(2,[(0,1,2),(1,0,4),(3,203,25)]),(1,[(2,1,4),(1,72,81)]),(4,[(0,0,2)]),(3,[(2,1,4)]),(0,[(0,0,2),(2,1,4),(1,72,81)]),(2,[(0,0,2),(2,1,4),(1,72,81)]),(6,[(0,0,158)]),(13,[(0,0,158)]),(2,[(0,2,4),(1,1,90),(0,0,158)]),(2,[(0,1,2),(3,203,14)]),(1,[(1,0,5),(3,203,14)]),(0,[(0,1,2),(1,0,5),(3,203,14)]),(2,[(0,1,2),(3,1,14)]),(0,[(0,1,2),(1,0,5),(3,1,14)]),(6,[(2,4,5),(3,37,38)]),(1,[(1,3,4),(2,4,5),(3,37,38)]),(1,[(1,4,5),(3,203,190)]),(2,[(0,1,2),(3,203,190)]),(6,[(1,0,5),(3,326,14)]),(1,[(2,1,3),(1,0,5),(3,326,14)]),(0,[(1,0,5),(3,326,14)]),(2,[(2,1,3),(3,326,14)]),(8,[(2,1,3),(3,326,14)]),(5,[(1,0,5),(3,326,14)]),(6,[(0,0,1),(3,17,79)]),(1,[(0,0,1),(1,3,5),(3,17,79)]),(0,[(0,0,1),(3,17,79)]),(2,[(0,0,1),(1,37,3)]),(3,[(0,197,4)]),(0,[(1,1,0),(3,1,19)]),(6,[(1,1,0),(3,1,19)]),(1,[(1,1,0),(1,18,3),(3,1,19)]),(4,[(3,1,2)]),(7,[(3,23,4),(1,429,0)]),(6,[(1,429,0)]),(2,[(1,0,36),(3,1,29)]),(2,[(3,1,2),(0,0,4),(1,24,3)]),(14,[(3,1,2)]),(15,[(3,1,2)]),(4,[(3,1,2),(1,24,3)]),(0,[(3,1,152),(0,1,4)]),(2,[(1,0,3),(3,1,152),(0,1,4)]),(1,[(1,0,3),(3,1,152),(0,1,4)]),(6,[(3,1,152),(0,1,4)]),(1,[(3,115,4),(1,1,5)]),(4,[(1,0,3),(2,0,5)]),(0,[(2,0,5),(3,1,4)]),(0,[(3,1,2),(1,23,5)]),(2,[(3,1,2),(1,0,4)]),(2,[(1,4,36),(3,1,62)]),(1,[(1,115,5),(1,0,4)]),(7,[(3,0,2),(1,115,5)]),(2,[(3,0,2),(1,0,4)]),(8,[(3,1,2),(1,23,5)]),(2,[(3,1,2),(3,1,4)]),(1,[(1,23,5),(3,1,4)]),(6,[(0,4,249)]),(2,[(3,1,2),(0,4,249)]),(0,[(2,0,5),(0,2,38)]),(4,[(3,1,2),(1,23,24)]),(7,[(0,0,4),(1,23,24)]),(1,[(0,0,4),(1,23,24)]),(0,[(3,1,2),(0,0,4),(1,23,24)]),(2,[(3,1,2),(0,0,4),(1,23,24)]),(8,[(3,1,4),(1,115,69)]),(1,[(3,1,4),(1,115,69)]),(4,[(3,0,2),(1,115,69)]),(0,[(3,0,2),(3,1,4),(1,115,69)]),(7,[(3,0,2),(1,115,69)]),(2,[(3,0,2),(3,1,4),(1,115,69)]),(1,[(1,1,5),(3,115,36)]),(8,[(1,1,5),(3,115,36)]),(2,[(3,0,2),(3,115,36)]),(2,[(3,1,14),(1,3,4)]),(1,[(1,3,4)]),(1,[(1,0,5),(3,1,14)]),(1,[(1,0,5),(1,1,4)]),(5,[(1,41,0)]),(3,[(1,0,5),(3,1,14)]),(1,[(1,4,5),(3,115,190)]),(8,[(1,4,5),(3,115,190)]),(2,[(3,0,2),(3,115,190)]),(2,[(3,37,0)]),(2,[(1,37,0)]),(1,[(2,4,5),(1,37,0)]),(6,[(0,4,79)]),(0,[(0,0,79)]),(6,[(0,0,79)]),(1,[(1,3,5),(0,0,79)]),(0,[(3,1,79)]),(2,[(3,1,79)]),(6,[(3,1,38)]),(0,[(3,1,38)]),(6,[]),(2,[(3,111,4)]),(0,[(0,2,4),(1,90,5)]),(0,[(3,41,4)]),(0,[(1,41,0)]),(2,[(1,3,4)]),(3,[(1,3,4)]),(2,[(3,54,4)]),(1,[(2,1,5),(1,54,0)]),(2,[(1,54,0)]),(2,[(3,4,14)]),(2,[(2,4,36)]),(1,[(1,0,5),(1,4,14)]),(2,[(1,4,14)]),(2,[(0,4,14)]),(0,[(1,0,5),(0,4,14)]),(1,[(1,0,5),(0,4,14)]),(2,[(2,0,36)]),(1,[(3,1,4),(1,3,5)]),(7,[(2,69,5)]),(0,[(2,242,5)]),(2,[(3,3,4)]),(6,[(2,242,5)]),(1,[(3,1,4),(1,0,5)]),(7,[(1,69,3)]),(1,[(3,1,4),(1,69,3)]),(2,[(2,0,4)]),(1,[(2,0,4),(1,168,5)]),(2,[(1,1,4)]),(1,[(2,0,1),(1,3,5)]),(1,[(1,0,5),(3,3,4)]),(1,[(2,0,1),(1,3,4)]),(2,[(1,1,14)]),(0,[(2,2,4),(1,224,5)]),(1,[(3,203,4)]),(4,[(2,2,3)]),(2,[(2,0,1),(3,1,2)]),(7,[(3,86,4)]),(1,[(1,1,3),(3,86,4)]),(2,[(0,2,14)]),(0,[(0,0,4),(1,0,4)]),(1,[(1,0,1),(1,4,5)]),(1,[(1,0,1),(1,3,4)]),(1,[(0,0,1),(2,4,5)]),(16,[(0,0,1)]),(1,[(1,0,1),(3,3,4)]),(8,[(2,1,4)]),(1,[(2,1,4)]),(2,[(2,1,4)]),(1,[(1,0,3),(2,4,5)]),(0,[(1,1,5),(2,2,36)]),(2,[(2,2,36)]),(2,[(3,1,2),(1,1,4)]),(1,[(0,0,4),(1,24,5)]),(4,[(1,24,5)]),(1,[(2,0,1),(3,3,4)]),(1,[(1,0,1),(1,0,3)]),(1,[(1,0,90)]),(8,[(1,3,14)]),(2,[(1,3,14)]),(6,[(2,152,5)]),(0,[(0,0,4),(1,1,5)]),(1,[(1,4,5)]),(2,[(1,1,3),(3,1,4)]),(1,[(1,0,3),(3,1,4)]),(1,[(0,0,1),(3,3,4)]),(1,[(0,1,4),(1,6,0)]),(4,[(1,6,0)]),(1,[(1,1,0)]),(0,[(1,1,0)]),(3,[(2,0,3)]),(1,[(2,0,3),(2,4,5)]),(2,[(1,1,0),(3,1,2)]),(1,[(0,0,1),(1,3,4)]),(1,[(3,1,4),(2,0,5)]),(1,[(1,0,1),(1,0,4)]),(8,[(2,18,3)]),(1,[(1,0,1),(2,18,3)]),(8,[(0,18,2)]),(2,[(1,111,0)]),(2,[(2,0,1),(1,1,4)]),(1,[(2,0,1),(1,1,4)]),(1,[(1,1,3)]),(3,[(1,1,3)]),(4,[(1,1,3)]),(2,[(2,0,1),(1,1,3)]),(2,[(3,1,190)]),(0,[(0,0,4)]),(1,[(1,0,1),(3,18,4)]),(8,[(1,18,4)]),(1,[(1,0,1),(1,18,4)]),(1,[(3,1,4),(3,69,0)]),(2,[(3,1,14)]),(1,[(1,203,0)]),(0,[(0,1,2),(1,203,0)]),(1,[(1,0,4)]),(1,[(1,81,5)]),(1,[(1,23,0)]),(1,[(2,0,5),(3,3,4)]),(1,[(3,115,4)]),(6,[(3,326,4)]),(0,[(3,326,4)]),(7,[(1,186,3)]),(1,[(2,0,1),(1,186,3)]),(0,[(2,38,5)]),(6,[(2,38,5)]),(1,[(0,0,1),(1,17,3)]),(2,[(3,1,2),(3,0,4)]),(1,[(0,0,1),(1,3,5)]),(1,[(1,0,5),(1,3,4)]),(0,[(3,1,2),(1,1,5)]),(1,[(2,1,4),(1,72,0)]),(2,[(0,0,4),(1,24,3)]),(0,[(0,0,86)]),(2,[(2,0,3),(0,1,4)]),(1,[(2,0,3),(0,1,4)]),(1,[(1,1,3),(0,0,4)]),(2,[(3,1,4),(1,69,3)]),(1,[(1,0,3),(1,1,5)]),(6,[(1,260,5)]),(1,[(1,0,3),(1,3,4)]),(1,[(2,0,3),(3,1,4)]),(1,[(1,1,3),(2,0,5)]),(1,[(2,0,3),(1,1,5)]),(1,[(2,1,3)]),(3,[(2,1,3)]),(4,[(2,1,3)]),(4,[(1,24,3)]),(0,[(0,1,4),(2,0,5)]),(1,[(0,1,4),(2,0,5)]),(1,[(1,0,1),(1,3,5)]),(1,[(0,0,4),(1,3,5)]),(6,[(1,326,0)]),(0,[(1,326,0)]),(5,[(1,326,0)]),(0,[(0,2,4)])] : List PoolSpec)).map some)
def B_22_3 : BT (List (List Nat)) := BT.empty
lemma B_22_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 3 xs.toFinset) B_22_3 := .empty
def P_22_4 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 []
def N_22_4 : List NodeSpec := [([11,13,2,3,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_4 : checkNodesBT W_22 g_22 F_22 P_22_4 A_22 B_22_3 4 N_22_4 = true := by decide +kernel
def B_22_4 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_4
set_option maxRecDepth 500000 in
lemma B_22_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 4 xs.toFinset) B_22_4 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_3_ok C_22_4
def P_22_5 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [0,1,2,3,4,5,6,7,8,9,10,11,12]
def N_22_5 : List NodeSpec := [([8,13,2,3,5,14],[0],[0]),([12,11,0,2,3,5],[1],[0]),([8,0,16,2,3,5],[],[]),([15,11,0,2,3,5],[2],[]),([22,18,2,3,4,5],[],[]),([23,26,28,2,3,5],[3],[]),([30,2,32,4,5],[],[]),([33,35,2,3,5,36],[4],[]),([37,18,2,3,40,5],[5],[]),([44,18,2,3,4,5],[],[]),([8,46,2,3,5,14],[6],[]),([34,35,1,2,3,5],[4,7],[1]),([34,26,28,2,3,5],[4,8],[1]),([49,26,1,2,3,5],[],[]),([8,0,2,3,5,51],[9,10,11],[]),([52,8,0,2,3,5],[],[]),([12,8,0,2,3,53],[0,12],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_5 : checkNodesBT W_22 g_22 F_22 P_22_5 A_22 B_22_4 5 N_22_5 = true := by decide +kernel
def B_22_5 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_5
set_option maxRecDepth 500000 in
lemma B_22_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 5 xs.toFinset) B_22_5 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_4_ok C_22_5
def P_22_6 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [0,3,4,6,8,10,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133]
def N_22_6 : List NodeSpec := [([0,1,2,3,56,4,5],[],[]),([60,59,0,1,2,3,5],[4,13,14],[]),([63,0,64,1,2,3,5],[4],[]),([66,0,67,2,3,4,5],[4,13],[]),([68,66,0,2,3,4,5],[4],[]),([8,0,2,3,5,71],[4,15,16,17,18],[]),([75,0,1,2,3,4,5],[],[]),([37,77,18,2,3,4,5],[19,20],[]),([78,30,18,2,3,4,5],[4,21],[]),([80,17,18,2,3,4,5],[22,23],[]),([84,0,2,3,4],[4,24,25,26,27],[]),([85,1,2,3,4,89,5],[],[]),([92,18,2,91,3,4,5],[28],[]),([18,2,91,3,4,5,93],[28,29,30],[]),([8,0,2,3,5,95],[4,6,12,31,32],[]),([30,96,18,2,3,4,5],[4,13,33],[]),([44,0,1,2,3,4,5],[],[0]),([97,99,2,3,5],[4,34,35,36,37,38],[]),([37,17,18,2,3,39,5],[39,40],[0]),([30,31,2,3,4,5],[4,35,41,42,43,44],[0]),([101,100,18,2,3,4,5],[45,46,47],[]),([12,8,0,102,2,3,5],[12,48,49,50],[]),([8,0,103,2,3,5,14],[12,48,51,52],[]),([37,0,1,2,3,40,5],[53],[0]),([105,17,2,3,5],[4,35,39,54,55,56,57],[]),([106,100,18,2,3,4,5],[58,59],[]),([34,26,1,2,3,5,36],[4],[0,1]),([107,26,1,2,3,5,36],[35,60,61],[]),([108,100,2,3,4,5],[35,45,47,59,62,63,64,65,66],[]),([109,31,2,3,5],[4,35,39,56,67,68,69],[]),([17,2,32,4,5,29],[13,70,71,72,73],[0]),([37,100,18,2,3,4,5],[13,35,65,74,75],[]),([17,18,2,3,110,4,5],[76],[]),([111,8,0,112,2,3,5],[4,12,35,77],[]),([114,2,3,4,5],[4,78,79,80,81,82],[]),([12,8,115,0,2,3,5],[12,35,49,83],[1]),([100,18,2,3,4,5,116],[59,65,84,85],[]),([17,18,2,3,4,5,21],[86,87,88],[0]),([120,0,2,119,117,4,5],[89],[]),([100,121,18,2,3,4,5],[46,74,90],[]),([122,37,17,18,2,3,4],[13,39,74,91],[]),([37,124,18,2,3,4,5],[13,35,92,93],[]),([126,18,2,3,4,5],[35,94,95],[]),([127,128,18,2,3,4,5],[35,96],[]),([0,130,1,2,3,4,5],[],[]),([126,18,2,3,4,5,125],[89],[]),([8,0,13,2,3,5],[4,12,48,97,98],[1]),([8,0,2,3,5,82],[4,99,100,101],[]),([8,0,2,3,5,131],[4,10,12,48,102,103],[]),([17,31,132,3,5],[35,39,56,104,105,106],[]),([45,112,2,3,5],[4,6,35,95,107,108,109,110],[]),([45,8,2,3,5,14],[0,4,6,111],[0]),([133,8,0,2,3,5],[0,4,6,10,12,48,112,113],[]),([34,26,1,2,3,5],[3,4,8,61,114],[0]),([33,26,2,3,5,36],[4,115,116,117],[0]),([33,134,2,3,5],[4,35,95,118,119,120,121],[]),([136,8,0,2,3,5],[4,17,18,122,123],[]),([34,27,26,1,2,3,5],[4,115],[0,1]),([111,33,26,1,2,3,5],[4,35,60,61],[]),([8,0,50,2,3,5],[0,4,12,35,124],[0]),([17,18,2,3,4,5,43],[89,125],[0]),([8,0,2,3,5,53],[6,12,48,126,127,128],[0,1]),([137,12,8,0,2,3,5],[12,48,77],[0]),([12,15,8,0,2,3,5],[0,12,49,126],[0]),([15,8,0,2,3,5,14],[4,12,52],[0]),([8,0,2,3,5,139],[4,12,129,130,131],[]),([12,8,0,13,2,3,5],[4],[1]),([11,8,0,2,3,5],[4,10,12,48,132,133],[0,1]),([11,8,0,2,3,5,14],[4,133],[1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_6 : checkNodesBT W_22 g_22 F_22 P_22_6 A_22 B_22_5 6 N_22_6 = true := by decide +kernel
def B_22_6 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_6
set_option maxRecDepth 500000 in
lemma B_22_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 6 xs.toFinset) B_22_6 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_5_ok C_22_6
def P_22_7 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [0,3,4,6,8,10,12,13,14,15,17,18,22,28,29,30,34,35,39,40,41,45,46,48,49,52,56,59,60,61,62,65,67,70,71,72,73,74,77,89,93,95,102,104,112,115,117,122,123,125,126,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576]
def N_22_7 : List NodeSpec := [([0,1,2,141,3,4,5],[89,134,135,136,137,138,139,140],[]),([142,143,1,2,140,3,4,5],[35,141,142],[]),([142,0,1,2,3,144,4,5],[13,142,143,144],[1]),([0,146,1,2,3,4,5],[89,138,140,145,146,147,148,149,150],[]),([63,0,1,2,3,5],[4,142,151,152],[0,1]),([148,0,2,3,4,147,5,36],[13,152,153],[]),([0,1,2,3,4,89,5,36],[13,142,152,154,155],[0]),([150,151,0,1,2,3,4,5],[13,60,142,156],[]),([154,0,1,2,3,57,4,5],[89,142,157,158],[]),([0,1,2,155,140,3,4,5],[141,142,159],[]),([0,1,2,3,55,4,5,36],[13,77,89,142,160,161],[]),([157,0,1,2,3,4,5,36],[89,143,162,163,164],[]),([0,2,159,158,3,4,5],[13,148,165,166,167,168,169],[]),([0,161,1,2,3,4,5],[4,140,142,170,171],[]),([0,164,1,2,3,4,5,36],[35,89,142,172],[]),([85,0,1,2,3,88,4,5],[143,148,173],[0]),([66,0,2,3,4,5],[4,13,174,175,176],[0]),([165,0,1,2,3,4,5,153],[140,148,177],[]),([69,154,0,2,3,4,5,14],[13,14,178],[]),([136,69,0,167,2,3,4,5],[4,89,179,180],[]),([0,1,2,169,3,4,5,36],[140,181,182],[]),([107,168,170,1,2,3,5,36],[35,60,183],[0]),([168,170,1,162,2,3,5,36],[183,184,185,186],[1]),([168,170,1,2,3,5,172],[183,185,187,188,189,190,191],[1]),([136,72,69,0,2,3,5],[4,123,140,148,180,192,193,194,195,196,197],[0]),([12,69,8,0,2,3,5],[4,15,17,18,122,198,199,200],[]),([8,70,0,2,3,5],[4,17,18,140,198,201,202,203,204,205],[0]),([174,0,1,2,3,4,5],[89,138,140,142,148,149,206,207,208],[]),([175,0,1,2,3,176,4,5],[142,148,174,209],[]),([177,0,1,2,3,4,5,36],[140,210,211,212],[]),([178,0,1,2,3,25,5,36],[13,77,152,213,214],[]),([179,0,1,2,3,4,5],[4,89,138,140,142,148,149,159,163,210,215,216,217],[]),([0,181,1,2,3,4,5],[140,149,159,210,218,219,220,221],[]),([154,0,6,2,3,4,5,14],[13,14,222,223,224],[]),([182,0,1,2,3,4,5,14],[13,174,225,226,227,228],[]),([0,1,2,183,3,4,5,36],[143,229,230,231],[]),([107,24,1,2,3,25,5,36],[35,60,232],[0]),([111,8,0,2,3,5],[4,12,35,48,77,233,234],[0,1]),([142,8,0,2,3,5],[0,4,6,12,48,235],[]),([12,8,0,2,3,5],[0,4,6,10,12,48,49,199,236],[0,1]),([184,143,0,1,2,3,4,5],[89,137,142,224,237],[]),([24,1,162,2,3,25,5,36],[232,238,239,240],[1]),([8,0,138,2,3,5],[0,4,35,48,241],[0]),([8,0,2,3,5,14],[0,4,6,12,35,52,242,243],[0,1]),([8,0,2,3,5,185],[0,4,12,48,244],[]),([0,1,2,3,19,4,5,125],[224,245],[]),([37,17,0,1,2,3,39,5],[246,247,248,249],[0]),([122,0,1,31,2,3,4,5],[220,224,250,251,252],[]),([187,23,0,1,2,3,4,5],[159,205,253],[]),([182,0,1,2,3,4,5],[13,89,210,228,254,255,256],[]),([122,37,0,1,18,2,3,4],[13,257,258],[0]),([17,0,1,2,3,4,5,43],[89,224,259],[0]),([92,0,1,2,91,3,4,5],[149,224,260],[0]),([188,0,1,2,3,4,5],[89,138,146,149,224,261,262,263,264],[]),([37,17,18,2,3,189,4,5],[265,266,267,268],[]),([191,18,2,3,4,5],[4,39,56,95,269,270,271,272],[]),([0,1,2,3,4,192,5],[35,138,273,274],[]),([0,193,1,2,3,4,5],[13,143,148,156,275],[]),([17,18,2,3,194,4,5,79],[39,56,266,276,277],[]),([0,2,195,3,4,7,5,14],[60,278,279,280,281],[]),([0,1,2,3,4,196,5],[89,138,143,159,210,282,283,284,285,286],[]),([15,8,0,2,3,5],[0,4,6,12,35,48,126,287],[0]),([0,198,1,2,3,4,5],[77,138,140,288,289,290],[]),([17,18,2,3,194,4,5],[13,35,56,89,266,276,283],[]),([199,0,1,2,3,4,5],[89,138,143,148,156,291,292,293,294],[]),([30,18,2,3,4,5],[4,13,295],[0]),([17,18,2,3,4,5,200],[35,39,56,296,297,298],[]),([17,201,18,2,3,4,5,79],[13,74,299],[]),([0,1,2,202,4,5,204],[148,300,301,302,303,304,305,306,307],[]),([17,18,2,32,4,5],[35,65,71,72,73,74,266,308,309],[0]),([205,1,2,3,4,5,14],[60,149,225,310,311,312,313],[]),([206,0,6,1,2,3,4,5],[13,89,142,224,314,315,316],[1]),([37,17,18,2,3,38,5],[22,39,65,265,317,318],[0]),([168,170,1,2,3,5,204],[183,191,319,320,321,322],[1]),([17,31,2,3,104,5],[35,39,56,67,266,323,324,325],[0]),([207,17,18,2,3,4,5],[4,22,56,266,326,327,328,329,330,331],[]),([8,81,0,2,3,5],[0,4,12,48,332],[0]),([37,17,18,2,3,19,4,5],[13,35,65,74,265,266,326,333],[0]),([37,209,0,18,2,3,4,5],[4,13],[]),([17,18,2,3,32,4,5],[65,71,72,74,308,309,330,334],[]),([17,18,210,3,4,5],[4,39,329,335,336,337,338],[]),([0,211,2,158,3,4,5],[148,159,165,224,339,340,341,342],[]),([184,186,1,2,140,3,4,5],[224,343],[]),([37,212,0,1,2,3,4,5],[142,146,148,249,344,345],[]),([109,18,2,3,4,5],[4,13,39,56,89,346,347,348],[0]),([17,18,2,3,4,5,125],[22,35,74,266,349,350,351],[0]),([122,17,18,2,3,4,5],[13,22,39,74,266,326,329,330,352,353,354,355],[0]),([17,18,2,3,20,4,5],[4,13,39,56,266,326,356,357,358],[0]),([17,18,2,3,189,4,5],[13,35,74,265,267,359],[]),([108,17,2,3,19,4,5],[4,22,35,62,65,352,360,361,362],[0]),([17,18,2,3,4,5,149],[13,156,266,363,364],[]),([184,0,213,1,2,3,4,5],[13,89,142,224,365,366],[]),([0,2,3,86,4,147,5,36],[153,367,368,369],[]),([100,18,2,3,4,5],[4,13,35,45,46,59,370,371],[0]),([69,8,0,2,3,5,14],[4,15,17,18,198,243,281],[]),([127,0,18,2,3,4,5,125],[35,372,373,374],[0]),([17,18,2,3,42,4,5],[13,89,266,326,375,376,377],[0]),([0,1,2,3,4,214,5],[13,89,210,282,378,379,380],[]),([37,123,17,18,2,3,4,5],[13,35,329,381,382,383],[0]),([17,31,2,3,4,5,29],[13,35,39,41,326],[0]),([37,17,18,76,2,3,4,5],[35,266,384,385],[0]),([142,1,2,3,216,4,5],[13,149,386,387,388,389],[]),([17,18,2,3,4,5,217],[65,390,391,392,393],[]),([17,18,132,3,4,5],[4,35,56,329,394,395,396,397],[0]),([206,69,0,1,2,3,4,5],[4,142,148,316],[]),([218,18,2,3,4,5],[13,35,60,95,329,398,399,400],[]),([37,41,17,18,2,3,4,5],[74,265,329,392,393,401],[]),([113,17,2,3,4,5],[4,402,403,404,405],[0]),([37,0,1,18,2,3,39,5],[4,148,247,248],[0]),([0,219,2,3,61,4,5],[142,143,406,407,408],[]),([175,156,2,3,4,5],[13,60,409,410],[]),([17,31,18,2,3,4,5,79],[13,22,35,56,74,266,411],[0]),([168,1,2,221,3,4,5,36],[77,412,413],[]),([0,1,2,3,222,4,5,223],[77,148,224,414,415,416,417],[]),([0,1,2,91,3,4,5,93],[224,260,418,419],[0]),([8,0,112,2,3,5],[0,4,12,48,112,420,421],[0]),([97,98,17,2,3,5],[4,35,39,56,422,423,424],[0]),([157,0,1,2,3,4,5],[4,138,140,159,163,210,425],[]),([17,18,2,3,4,5,225],[4,22,35,56,89,324,329,426,427,428],[]),([226,175,0,2,3,4,5,14],[4,13,14],[]),([8,94,0,2,3,5],[0,4,12,35,48,429,430,431],[0,1]),([99,18,2,3,4,5],[4,13,34,89,432],[0]),([175,227,1,2,3,4,5],[13,140,433,434],[]),([199,0,1,2,3,4,5,149],[89,159,435],[]),([80,0,1,18,2,3,4,5],[140,220,436],[0]),([17,18,2,3,228,4,5],[4,22,39,74,266,326,329,330,437,438],[]),([0,1,2,141,140,3,4,5],[89,134],[]),([37,186,0,1,2,3,39,5],[40,247,248,439],[]),([150,229,0,1,2,3,4,5],[13,142,143,156,224,440],[]),([8,0,2,3,5,230],[4,17,198,441,442,443],[]),([8,0,135,2,3,5],[4,17,18,198,205,444,445,446],[0]),([17,18,2,3,4,5,232],[4,35,329,400,447,448,449,450],[]),([17,233,2,3,4,5],[35,39,451,452,453,454],[]),([234,0,1,2,3,4,5,79],[140,220,251,455],[]),([0,193,1,2,3,4,5,149],[89,159,435],[]),([17,18,2,3,235,4,5],[39,74,266,326,329,330,362,456,457,458],[]),([175,0,1,2,3,222,4,5],[13,142,148,174,249,459,460,461],[]),([37,236,0,1,2,3,5],[246,249,318,462],[]),([0,1,2,3,216,4,5,36],[13,225,386,388],[]),([18,2,91,3,4,5],[13,28,29,30,35,95,266,329,400,463,464],[0]),([0,1,2,32,4,5,29],[13,35,70,220,465,466,467,468],[0]),([237,17,18,2,3,4,5],[4,35,65,89,329,469,470],[]),([154,0,6,2,3,4,5],[13,140,142,220,254,471],[]),([37,186,239,1,2,3,4,5],[249,472,473,474],[]),([0,1,31,132,3,5],[35,104,257,475,476,477],[0]),([0,1,2,3,228,25,5,36],[13,142,152,478,479],[]),([0,1,2,3,4,240,5],[4,159,210,480,481],[]),([178,0,1,2,3,38,5,36],[4,77,482],[]),([0,1,241,2,3,4,5,149],[13,159,435,483],[]),([124,18,2,3,4,5],[4,13,35,93,400,484,485],[0]),([243,0,1,18,2,3,4,5],[13,35,148,486],[]),([0,1,2,3,4,196,5,79],[89,251,284,285],[]),([37,242,0,1,18,2,3,5],[487,488,489],[]),([0,1,18,2,3,194,4,5],[13,35,148,283,490],[]),([24,1,2,3,25,5,204],[232,301,319,322,491,492,493],[1]),([0,1,2,3,245,4,5],[4,140,142,148,159,210,494,495],[]),([0,1,18,2,3,110,4,5],[148,496],[0]),([0,1,103,2,117,4,5,14],[497,498,499,500],[]),([37,242,17,18,2,3,5],[22,56,265,266,326,501,502],[]),([0,1,18,2,3,189,4,5],[13,35,220,359,503],[]),([246,0,2,3,4,5,223],[4,415,504,505],[]),([0,1,2,3,247,4,5],[4,142,149,224,388,506],[]),([186,0,1,2,3,4,5,43],[13,125,143,507],[1]),([186,0,1,2,3,4,5,248],[13,143,224,249,508],[]),([0,1,2,3,4,250,5],[35,138,143,148,509,510,511],[]),([0,1,2,3,4,214,5,79],[143,251,378,379],[]),([246,0,2,3,4,5,204],[4,322,505,512],[]),([142,251,1,2,3,4],[13,301,513],[1]),([0,1,18,2,3,4,5,21],[13,142,257,514],[0]),([0,252,1,2,3,4,5],[4,138,140,290,515,516],[]),([0,1,18,2,3,4,5,253],[35,89,142,517],[]),([0,1,18,2,3,4,5,43],[13,35,89,142,143],[0]),([254,0,197,2,3,4,5],[4,518,519,520,521],[]),([175,0,2,3,4,249],[35,60,522,523,524,525,526],[]),([255,135,2,3,4,5],[13,225,527,528,529],[]),([0,1,2,3,4,147,5,87],[13,530],[]),([175,197,2,3,4,5],[13,60,531],[]),([256,0,1,2,3,4,5,36],[140,220,532,533],[]),([0,1,2,3,257,4,5],[4,140,149,159,210,534,535],[]),([108,175,0,2,3,4],[4,13,35,536,537,538],[]),([105,0,1,2,3,5],[4,35,257,477,539,540],[0]),([0,1,2,3,4,259,5],[35,89,138,541,542,543],[]),([23,26,1,2,3,5],[3,4,35,61,544,545,546],[1]),([246,0,2,3,4,5,249],[4,35,547,548,549],[]),([165,1,2,3,152,4,5,14],[177,223,550,551],[]),([178,0,2,3,86,4,5,36],[369,482,552,553,554,555,556],[]),([0,1,2,3,4,261,5,36],[152,162,557],[]),([0,1,2,3,4,262,5],[138,140,148,159,210,220,530,558,559],[]),([186,263,2,3,4,5],[4,560,561,562,563,564],[0]),([107,0,1,2,202,4,5,36],[35,60,303],[]),([178,0,1,2,3,4,5,87],[148,215,220,552],[]),([0,1,2,119,117,4,5],[148,225,500,565,566,567,568,569],[0]),([45,8,0,2,3,5],[0,4,6,12,35,48,102,570,571],[0]),([243,17,18,2,3,4,5],[13,35,89,266,486,501,572,573],[]),([33,26,1,2,3,5],[3,4,8,61,115,117,574,575,576],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7 = true := by decide +kernel
def B_22_7 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_7
set_option maxRecDepth 500000 in
lemma B_22_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 7 xs.toFinset) B_22_7 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_6_ok C_22_7
def P_22_8 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [0,4,10,13,14,18,22,35,39,41,48,56,60,67,71,74,77,85,89,101,137,138,140,141,142,143,146,148,149,152,153,154,156,157,158,159,160,161,162,170,173,174,183,185,186,190,191,192,194,195,196,198,205,207,209,210,219,220,223,224,225,228,231,232,234,235,237,239,240,243,245,246,247,248,249,251,253,254,257,258,259,260,265,266,267,273,274,276,280,281,282,283,290,291,297,301,303,304,309,311,312,313,314,316,317,318,319,320,321,322,324,326,327,329,330,332,335,337,341,343,345,346,350,351,352,353,357,359,363,364,366,368,369,372,375,376,382,383,386,387,388,390,391,393,397,400,401,407,414,415,416,417,418,419,426,428,435,438,439,443,449,450,451,458,459,460,461,466,467,468,469,470,477,480,483,486,487,488,489,490,493,498,500,501,502,503,505,507,509,510,514,517,519,521,522,523,526,530,536,537,542,545,548,549,550,551,552,553,554,556,560,573,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1198,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208,1209,1210,1211,1212,1213,1214,1215,1216,1217,1218,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248,1249,1250,1251,1252,1253,1254,1255,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1296,1297,1298,1299,1300,1301,1302,1303,1304,1305,1306,1307,1308,1309,1310,1311,1312,1313,1314,1315,1316,1317,1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1337,1338,1339,1340,1341,1342,1343,1344,1345,1346,1347,1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1367,1368,1369,1370,1371,1372,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410,1411,1412,1413,1414,1415,1416,1417,1418,1419,1420,1421,1422,1423,1424,1425,1426,1427,1428,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454,1455,1456,1457,1458,1459,1460,1461,1462,1463,1464,1465,1466,1467,1468,1469,1470,1471,1472,1473,1474,1475,1476,1477,1478,1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,1492,1493,1494,1495,1496,1497,1498,1499,1500,1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1529,1530,1531,1532,1533,1534,1535,1536,1537,1538,1539,1540,1541,1542,1543,1544,1545,1546,1547,1548,1549,1550,1551,1552,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689,1690,1691,1692,1693,1694,1695,1696,1697,1698,1699,1700,1701,1702,1703,1704,1705,1706,1707,1708,1709,1710,1711,1712,1713,1714,1715,1716,1717,1718,1719,1720,1721,1722,1723,1724,1725,1726,1727,1728,1729,1730,1731,1732,1733,1734,1735,1736,1737,1738,1739,1740,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1751,1752,1753,1754,1755,1756,1757,1758,1759,1760,1761,1762,1763,1764,1765,1766,1767,1768,1769,1770,1771,1772,1773,1774,1775,1776,1777,1778,1779,1780,1781,1782,1783,1784,1785,1786,1787,1788,1789,1790,1791,1792,1793,1794,1795,1796,1797,1798,1799,1800,1801,1802,1803,1804,1805,1806,1807,1808,1809,1810,1811,1812,1813,1814,1815,1816,1817,1818,1819,1820,1821,1822,1823,1824,1825,1826,1827,1828,1829,1830,1831,1832,1833,1834,1835,1836,1837,1838,1839,1840,1841,1842,1843,1844,1845,1846,1847,1848,1849,1850,1851,1852,1853,1854,1855,1856,1857,1858,1859,1860,1861,1862,1863,1864,1865,1866,1867,1868,1869,1870,1871,1872,1873,1874,1875,1876,1877,1878,1879,1880,1881,1882,1883,1884,1885,1886,1887,1888,1889,1890,1891,1892,1893,1894,1895,1896,1897,1898,1899,1900,1901,1902,1903]
def N_22_8_0 : List NodeSpec := [([264,0,1,2,3,4,5],[13,138,142,143,577,578],[]),([37,0,1,266,2,3,4,5],[13,35,249,579,580,581,582,583,584],[]),([209,0,208,1,2,3,4,5],[13,89,148,585,586,587,588,589],[]),([209,0,1,2,3,4,5],[13,89,140,142,148,210,220,587,590,591],[]),([0,267,1,2,3,4,5],[4,149,159,210,592,593],[]),([0,1,2,3,4,268,5,79],[13,142,249,282,594,595,596,597,598],[]),([0,1,2,3,4,268,5],[13,89,142,282,595,599],[]),([180,0,269,1,2,3,4,5],[142,219,249,600],[]),([0,270,1,2,3,4,5],[13,89,142,148,601,602],[]),([0,1,2,3,4,5,271],[4,159,210,603,604,605],[]),([272,0,173,1,2,3,4,5],[4,13,60,77,142,148,207,606,607,608,609,610],[]),([273,0,1,2,3,4,5],[4,13,142,143,149,611,612],[]),([275,0,1,2,3,4,5],[4,89,138,149,205,224,613,614,615,616,617],[]),([150,0,1,2,3,4,5,149],[13,89,142,148,156,224,291,435,618],[0]),([150,0,1,2,3,4,5],[13,142,143,148,149,618,619,620],[]),([229,0,1,2,3,4,5,149],[13,35,142,148,156,159,224,291,435,483,621,622],[0]),([143,0,1,2,140,3,4,5],[13,137,148,224,237,623,624,625,626,627,628],[0]),([0,1,2,3,55,4,5],[13,89,142,160,161,224,629,630],[0,1]),([37,0,145,1,2,3,4,5],[13,142,146,148,220,249,581,582,631,632,633,634],[0]),([142,237,0,1,2,3,4],[162,220,469,635,636,637,638],[]),([0,1,2,3,4,276,5],[4,143,639,640,641,642,643,644],[]),([142,1,2,140,3,4,5],[13,35,141,142,148,625,645,646,647],[0,1]),([0,1,2,3,4,278,5],[13,149,205,648,649,650,651],[]),([280,0,1,2,3,4,5],[143,148,159,210,220,225,652,653,654,655,656],[]),([242,0,281,1,2,3,4,5],[657,658,659,660,661,662,663],[]),([0,1,2,3,4,147,5],[4,13,60,153,205,664,665],[]),([0,283,1,2,3,4,5],[13,60,140,142,148,220,666,667,668],[]),([180,0,2,3,4,5,36],[142,149,220,249],[]),([284,0,1,2,3,4,5],[4,13,142,143,152,669],[]),([160,244,0,1,2,3,5],[142,152,670],[0]),([226,0,1,2,3,4,5,14],[4,13,60,142,143,149,280,550,605,671,672,673],[0]),([0,274,1,2,3,4,5,36],[4,152,205,368,674,675,676,677],[]),([285,0,1,2,3,4,5],[13,60,89,159,280,281,678,679],[]),([0,1,2,3,4,5,286],[13,89,142,210,281,680,681,682],[]),([287,0,1,2,3,4,5],[13,77,89,140,142,148,610,683,684,685,686],[]),([0,1,2,140,3,4,5,36],[13,77,141,142,152,154,624,625,687],[0]),([0,145,1,2,3,4,5,36],[13,77,89,142,149,152,154,631,632,634,674,688,689,690],[]),([175,0,1,2,3,4,5,58],[4,13,60,691,692,693],[0,1]),([242,175,0,1,2,3,4,5,14],[13,209,243,281,461,660],[]),([175,0,1,2,3,4,38,5,14],[13,14,60,174,461,639],[0,1]),([178,0,1,2,3,4,5,36],[4,13,77,89,142,149,152,154,369,556,694],[0]),([220,0,1,2,3,61,4,5],[4,77,530,695,696,697,698,699,700],[0]),([220,156,1,2,3,4,5],[77,142,701,702],[1]),([0,1,2,221,3,4,5,36],[77,142,152,154,674,703,704,705,706,707],[0,1]),([242,175,0,1,2,3,4,5],[13,142,148,209,251,461,660,708],[]),([160,85,0,1,2,3,4,5],[4,142,170,709],[0]),([85,0,1,2,3,4,5,87],[13,142,710,711,712,713,714,715,716,717,718],[0,1]),([165,0,1,2,3,4,5,14],[4,60,143,280,281,550,551,671,719,720],[0]),([69,288,0,1,2,3,4,5],[4,13,142,148,249,721,722,723,724,725],[]),([0,289,1,2,3,4,5],[4,143,149,159,210,726,727,728],[]),([69,0,173,1,2,3,4,5],[4,13,77,142,148,607,609,729],[]),([290,0,1,2,3,4,5],[4,138,143,149,210,729],[]),([69,156,0,1,2,3,4,5],[4,142,149,730,731,732,733,734,735,736,737],[]),([291,0,1,2,3,4,5],[4,138,140,149,159,210,220,553,738,739,740],[]),([292,69,0,1,2,3,4,5,14],[4,13,60,243,281,730,741,742],[]),([0,293,1,2,3,4,5],[13,142,148,743,744],[]),([0,208,1,2,3,4,5],[4,13,89,142,745,746],[]),([0,1,2,3,4,230,36],[4,142,148,747],[]),([295,0,1,2,3,4,5,14],[4,13,148,174,243,280,281,550,671,748],[]),([297,0,1,2,3,4,5],[4,138,149,159,162,210,749],[]),([136,69,0,1,2,3,4,5],[4,89,142,143,148,553,724,725,750,751,752],[0]),([0,135,1,2,3,4,5,79],[13,142,149,220,249,490,596,597,750,753,754],[]),([136,0,1,2,3,4,5],[4,89,140,142,148,149,224,750,752,755],[]),([0,1,2,3,4,5,298],[4,13,750,756],[]),([107,170,0,1,2,3,4,5,36],[4,35,60,77,142,154,674,677,757,758],[0]),([299,0,1,2,3,4,5],[35,60,89,142,143,234,607,759],[]),([107,168,0,1,2,3,4,5,36],[35,60,77,142,674,759],[0]),([175,0,1,2,3,4,5,153],[13,60,158,693,760,761,762,763],[0,1]),([168,0,1,162,2,3,4,5,36],[77,142,152,674,701,759,764,765,766,767],[0]),([0,1,2,3,4,300,5],[35,60,149,159,174,243,768,769,770],[]),([142,72,69,0,2,3,5],[4,140,192,194,195,196,235,635],[0]),([168,170,1,301,2,3,5],[4,148,191,205,771,772,773,774],[1]),([303,0,1,2,3,4,5],[60,140,142,143,775,776],[]),([304,0,1,2,3,4,5],[35,143,159,657,777,778,779],[]),([0,306,1,2,3,4,5],[13,142,780,781],[]),([0,1,2,3,4,307,5],[13,60,89,782,783],[]),([0,173,1,2,3,4,7,5],[13,77,142,607,608,784,785],[0]),([0,1,2,3,4,308,5],[4,35,148,159,778,786,787,788,789],[]),([0,1,2,3,4,309,5],[4,77,148,368,790,791],[]),([0,1,2,3,4,25,5,36,29],[13,35,60,77,142,152,701,792,793],[0]),([142,310,1,2,3,4,5],[4,235,794,795,796,797],[]),([311,0,1,2,3,4,5],[142,143,148,798,799,800],[]),([166,0,1,2,3,4,14],[4,14,149,224,801],[]),([175,0,1,2,3,4,25,5],[4,13,60,174,693,786,802],[1]),([246,0,1,2,3,4,5,14],[4,13,14,60,148,149,174,243,280,281,550,671,799,803],[]),([312,0,1,2,3,4,5],[35,60,89,140,142,231,804,805,806],[]),([0,1,2,3,57,4,5,153],[13,60,158,225,243,249,761,807,808],[0,1]),([69,0,1,2,3,4,5,14,29],[4,13,60,77,142,174,281],[]),([24,0,1,73,2,3,4,5],[142,220,224,231,809,810,811,812,813,814,815],[1]),([0,313,1,2,3,4,5,36],[4,13,77,152,368,816,817],[]),([24,0,1,2,3,314,4,5],[89,220,553,818,819,820,821,822,823,824,825],[]),([315,0,1,2,3,4,5],[35,138,140,148,159,220,819,826,827,828,829],[]),([292,0,6,1,2,3,4,5],[13,89,140,220,228,243,830,831,832,833,834,835,836,837,838],[]),([107,24,0,1,2,3,4,5,36],[35,60,77,142,224,231,674],[0]),([24,0,1,162,2,3,4,5,36],[77,142,224,231,701,707,839,840,841,842,843],[0,1]),([69,180,0,2,3,4,5],[142,220,844,845,846],[]),([41,24,0,1,2,3,4,5,36],[77,142,224,231,368,369,631,674,689,810,812,825,847,848],[]),([316,0,1,2,3,4,5],[60,89,138,140,148,159,174,220,849,850,851,852],[]),([180,317,0,1,2,3,4,5],[13,142,219,249,853],[]),([142,0,6,2,3,7,5],[89,235,854,855,856,857,858],[0]),([24,1,2,3,25,5,36],[35,152,232,240,368,493,701,859],[0,1]),([0,1,2,3,4,5,230],[4,143,205,443,747,860,861],[]),([318,0,1,2,3,4,5],[143,149,159,162,210,220,862,863,864,865,866,867],[]),([163,0,1,2,3,4,5,36],[77,142,154,701,868,869],[0]),([111,0,1,2,202,4,5],[60,162,303,607,806,870],[]),([175,0,1,2,3,4,7,5,14],[13,14,60,89,142,174,281,460,871],[1]),([0,1,319,2,202,4,5],[162,220,303,304,872,873,874,875],[1]),([142,0,1,2,3,42,4,5],[142,143,148,160,259,376,507,647,855,876,877,878,879],[0]),([0,1,2,202,4,5,36],[35,154,162,303,304,369,701,880,881],[0,1]),([320,0,1,2,117,4,5],[89,148,162,220,498,500,830,882,883,884,885,886],[]),([85,1,2,3,4,5,29],[142,701,887,888],[1]),([0,1,321,2,3,4,5,79],[13,35,220,249,597,889,890,891,892],[]),([322,0,173,1,2,3,4,5],[13,60,77,142,608,609,610,893,894,895],[]),([323,0,1,2,3,4,5],[35,89,138,140,148,149,159,220,891,896,897,898,899],[]),([0,269,1,2,3,4,5],[13,89,140,142,148,900,901],[]),([142,1,321,2,3,4,5],[35,89,148,855,891,892,902,903,904,905],[]),([0,238,2,3,4,5,36],[142,148,154,906,907],[]),([260,0,1,238,2,3,4,5],[4,13,142,581,908,909],[]),([324,0,1,2,3,4,5],[35,89,138,140,148,159,210,910,911,912,913,914],[]),([0,2,158,3,4,5,36],[13,142,148,154,915,916,917],[]),([160,260,0,1,2,3,4,5],[4,13,143,918,919,920,921,922,923,924],[]),([260,135,1,2,3,4,5],[4,224,739,925,926,927,928],[]),([260,0,1,2,3,4,5,325],[13,89,224,832,911,929,930,931,932,933,934],[]),([0,327,1,2,3,4,5],[35,89,140,142,819,935,936,937,938,939],[]),([142,0,1,2,158,3,4,5],[142,148,341,635,645,647,917,940,941,942,943],[1]),([260,0,1,2,3,61,4,5,36],[77,142,154,530,701,944,945],[0]),([260,6,1,2,3,4,5,14],[13,60,143,223,224,243,249,832,892,946,947,948,949],[]),([0,2,3,328,4,5,36],[89,142,249,950,951,952],[]),([0,1,2,3,176,4,5,14],[13,14,174,243,281,953,954,955],[0,1]),([136,0,135,1,2,3,4,5],[4,13,148,750,753,925,956,957],[]),([0,1,2,3,4,5,330],[4,143,958,959,960,961,962,963],[]),([0,1,2,3,329,4,5,14],[4,143,148,280,281,671,963,964,965,966],[]),([37,0,331,1,2,3,4,5],[4,13,148,249,582,583,939,967,968,969],[]),([332,0,1,2,3,4,5],[35,89,140,148,149,159,210,969,970,971,972,973],[]),([333,37,0,1,2,3,4],[13,162,220,224,225,974,975,976],[]),([154,0,1,2,3,4,5],[13,89,140,142,148,210,977,978,979,980],[0]),([292,69,0,1,2,3,4,5],[4,13,142,148,220,243,724,725,833,836,837,981,982,983,984],[]),([180,0,1,2,3,4,5],[13,138,140,142,143,148,149,249],[]),([0,1,2,3,4,14,149],[13,142,143,148,224,281,291,985],[]),([0,335,1,2,3,4,5],[13,142,148,149,162,986],[]),([0,1,2,3,152,336,4,5],[13,225,987,988,989,990,991],[]),([0,1,2,3,4,5,253],[13,89,142,224,459,517,992,993,994,995,996],[0,1]),([24,0,1,2,3,4,5,36,87],[77,142,154,224,249,368,369,553,710,711,712,825,997],[1]),([0,1,2,222,38,5],[4,148,162,998,999,1000,1001],[]),([212,0,1,2,3,4,5],[13,89,140,142,146,148,149,224,345,1002,1003,1004,1005],[0]),([142,0,1,2,3,215,4,5],[4,647,878,1006,1007,1008,1009,1010,1011],[0,1]),([0,1,2,3,152,277,4,5],[4,13,89,143,220,649,1012,1013,1014,1015,1016,1017,1018],[]),([0,1,2,3,337,4,5],[225,1019,1020,1021,1022],[]),([175,0,338,1,2,3,4,5],[60,140,142,693,1023,1024],[]),([0,1,2,3,222,4,5,36],[13,77,89,142,152,154,162,368,459,694,701,1025,1026,1027,1028],[]),([69,0,1,2,3,4,5,339],[4,143,148,162,725,739,742,924,949,1029,1030,1031,1032,1033,1034,1035,1036],[]),([333,69,0,1,2,3,4,5],[4,148,225,741,742,1037,1038,1039],[]),([69,0,1,2,3,4,5,153],[4,13,142,148,249,254,724,725,976,1040,1041,1042,1043,1044,1045],[]),([168,170,1,2,3,5,340],[4,148,191,205,774,1046,1047],[1]),([0,1,2,3,152,4,5,230],[4,13,143,225,1018,1044,1048,1049,1050,1051],[]),([0,1,2,3,152,61,4,5],[13,142,148,152,225,530,695,697,698,1013,1018,1052,1053,1054],[]),([333,0,6,1,2,3,4,5],[89,162,225,832,834,835,1037,1038,1039,1055,1056],[]),([0,1,2,3,152,4,5,325],[13,89,224,225,929,932,934,1015,1056,1057],[]),([37,255,0,1,2,3,4,5],[142,148,162,220,225,249,582,583,1015,1058],[]),([255,0,1,2,4,38,5],[4,162,220,1059,1060,1061,1062,1063,1064],[]),([341,0,1,2,3,4,5],[143,148,159,162,210,225,1065,1066,1067,1068],[]),([0,1,2,3,4,343,5],[13,60,89,148,1069],[]),([69,0,1,103,2,3,4,5,14],[4,13,60,280,281,719,1036,1070],[1]),([168,170,171,1,2,3,5],[148,183,185,190,191,205,774,1071,1072,1073],[0,1]),([24,0,1,2,3,86,4,5,36],[77,89,142,224,369,553,554,701,819,825,1074,1075],[]),([0,2,3,86,61,4,5,36],[77,142,369,1076,1077],[0]),([175,1,2,3,152,4,5,14],[13,60,461,1078],[1]),([69,0,1,2,3,4,5,217],[13,148,162,391,739,742,847,1003,1079,1080,1081,1082,1083,1084,1085,1086],[]),([37,0,208,1,18,2,3,4,5],[4,13,585,1087],[0]),([0,1,2,3,228,4,5,14],[13,14,60,142,281,1088,1089],[1]),([344,0,1,2,3,4,5],[13,138,140,142,148,149,1090],[]),([243,17,0,1,2,3,4,5],[89,143,148,249,486,601,1091,1092,1093,1094,1095,1096,1097],[0]),([0,345,1,2,3,4,5],[4,138,140,143,159,210,220,225,1098,1099],[]),([243,0,1,18,2,3,4,5],[13,35,89,142,143,148,486,601,1087,1096,1097,1100,1101],[0]),([0,346,2,3,4,5,36],[35,142,148,149,369,701,1102],[]),([0,1,2,3,4,5,347],[35,140,148,210,1103,1104,1105,1106],[]),([180,24,0,1,2,3,4,5],[142,143,219,220,231,249,597,825,842,1107],[0]),([23,69,0,1,2,3,4,5,14],[4,35,77,142,280,1036,1108,1109],[]),([37,0,1,18,2,3,38,5],[148,249,257,318,480,1110,1111,1112,1113,1114],[0]),([85,0,2,3,86,4,5,36],[142,173,554,715,717,1076,1077,1115,1116,1117],[1]),([17,18,2,3,4,5,29],[13,39,326,1118,1119],[0]),([113,0,1,2,3,4,5],[4,13,138,149,159,210,1120],[0]),([205,0,1,2,3,4,5],[89,149,159,210,224,225,311,312,1015,1121,1122,1123,1124],[0]),([242,0,1,2,3,4,5,348],[142,143,148,224,1125,1126,1127,1128,1129,1130],[]),([0,1,18,2,3,342,4,5],[35,60,142,148,783,1131],[]),([108,0,1,2,3,4,29],[13,35,1132,1133,1134],[0,1]),([154,0,1,2,3,4,5,14],[13,14,157,158,174,281,1135,1136],[0]),([41,69,0,1,2,3,4,5,14],[13,60,243,280,724,1036,1083,1085,1137,1138],[]),([0,197,1,2,3,4,5,190],[4,77,290,1106,1139,1140],[0]),([0,1,18,2,3,4,5,149],[13,35,142,148,156,224,291,435,1087,1141,1142],[0]),([350,0,1,2,3,4,5],[35,89,140,149,159,1143,1144,1145,1146],[]),([142,6,1,2,3,152,4,5],[225,313,830,892,1147,1148,1149,1150],[]),([0,1,233,2,3,4,5],[35,148,149,224,257,451,1151,1152,1153,1154],[0]),([0,18,2,158,3,4,5],[13,142,143,148,159,224,341,940,1155,1156,1157],[]),([108,0,1,2,3,4,14],[13,35,149,537,1132,1158],[0]),([318,0,1,2,202,4,5],[35,143,162,220,225,303,304,863,865,1159],[]),([0,1,76,2,3,4,5],[13,140,142,1160,1161,1162],[]),([37,41,0,1,18,2,3,4,5],[13,35,258,582,633,1112,1138,1163,1164,1165],[0]),([0,1,2,3,4,5,125],[13,60,205,224,245,350,372,1166],[]),([0,1,18,2,3,42,4,5],[13,35,142,148,160,224,259,376,1087,1132,1167],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_0 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_0 = true := by decide +kernel
def N_22_8_1 : List NodeSpec := [([0,1,18,2,3,228,4,5],[4,13,438,1168,1169,1170],[0]),([351,0,1,2,3,4,5],[13,35,89,138,140,143,149,159,210,1087,1163,1171,1172,1173,1174,1175,1176,1177],[]),([111,24,1,2,3,25,5],[60,232,234,239,607,783,1178],[1]),([352,0,1,2,3,4,5,29],[4,13,148,273,274,1179,1180,1181],[]),([17,0,1,2,3,194,4,5,79],[220,246,249,283,596,597,1093,1182,1183,1184],[0]),([186,0,1,2,3,4,5,149],[13,142,148,156,224,291,363,435,483,1141,1185,1186,1187],[1]),([0,1,2,3,228,4,5,29],[13,140,142,273,1119,1132,1188,1189],[]),([17,18,2,3,4,5,79],[13,22,35,56,74,326,400,597,1190,1191],[0]),([0,1,2,3,216,4,5],[13,148,224,225,386,387,388,1192,1193,1194],[0]),([0,1,2,3,4,38,5,29],[4,13,480,1179,1188,1195],[0]),([0,1,2,3,4,5,353],[13,35,1143,1196,1197,1198,1199],[]),([0,1,31,2,3,19,4,5],[13,35,85,220,225,245,477,553,1200],[0]),([0,1,2,3,4,5,43],[13,89,142,143,259,507,1201,1202,1203],[0,1]),([8,0,2,3,5],[0,10,48,251],[0,1]),([175,0,1,2,3,152,4,5],[13,60,142,461,693,762,1013,1054,1204,1205],[0]),([0,354,18,2,3,4,5],[13,35,60,143,1206,1207,1208],[]),([0,1,18,2,32,4,5],[35,148,220,258,309,466,467,468,480,1087,1209,1210],[0]),([0,1,2,3,4,355,36],[35,89,154,224,701,815,1211,1212,1213],[]),([0,356,1,2,3,4,5],[13,143,148,210,249,597,1214,1215,1216],[]),([175,0,1,2,3,4,357,5],[4,60,148,209,1217,1218],[]),([0,301,2,3,86,4,5],[142,224,225,773,1219,1220,1221,1222],[1]),([23,170,0,1,2,3,4,5,36],[4,35,674,758,1109,1223,1224],[]),([97,0,1,2,3,4,5,29],[13,35,273,274,1119,1179,1180,1188,1225],[0]),([358,0,1,2,3,4,5,249],[35,148,159,509,510,1226,1227],[]),([0,354,2,3,4,5,36],[60,142,149,705],[]),([160,0,1,2,3,152,4,5],[13,142,143,220,225,918,1013,1044],[]),([242,0,1,2,3,4,5,359],[89,143,148,660,662,708,1095,1126,1228,1229,1230,1231,1232,1233],[]),([37,242,0,1,18,2,3,5],[148,489,1087,1101,1110,1112,1132,1234,1235,1236],[0]),([0,360,2,3,4,7,5],[4,35,143,148,159,794,1237,1238,1239,1240,1241],[]),([127,0,1,2,3,4,5],[60,142,143,148,1242,1243],[]),([37,17,18,2,3,4,5],[4,13,35,89,265,266,324,326,382,581,1244],[0]),([0,1,361,2,3,4,5],[35,257,477,1245,1246,1247,1248],[]),([0,1,2,3,4,5,363],[4,205,220,1249,1250,1251,1252,1253],[]),([37,17,0,1,2,3,38,5],[148,246,247,249,318,1111,1113,1114,1254,1255,1256],[0]),([24,0,1,2,3,4,5,364],[89,162,220,224,231,819,842,1257,1258,1259,1260,1261,1262,1263],[]),([186,135,1,2,3,4,5],[4,142,739],[]),([175,0,1,2,3,86,4,5,14],[13,60,89,223,550,763,1264],[]),([0,1,31,18,2,3,4,5,79],[13,35,258,477,490,596,1087,1110],[0]),([0,1,2,3,4,25,5,223],[77,224,415,416,786,1265,1266,1267,1268,1269,1270],[0]),([24,281,1,2,3,4,5],[4,35,657,1271],[]),([0,135,1,2,3,4,5],[4,13,148,149,224,1272],[]),([365,0,1,2,3,4,5],[4,138,149,159,210,477,1273],[]),([69,1,2,3,152,4,5,14],[4,13,60,223,243,550,553,730,742,1078,1205,1274,1275,1276],[]),([0,1,2,3,152,57,4,5],[13,142,220,225,808,1013,1015,1277],[]),([0,1,2,3,4,5,366],[4,138,205,220,1278,1279,1280,1281],[]),([0,367,1,2,3,4,5],[4,89,138,140,142,149,210,729,739,1282,1283,1284,1285,1286],[]),([98,0,1,2,3,4,5,79],[4,13,142,220,225,249,596,1279],[]),([0,1,18,2,3,32,4,5],[35,258,309,466,468,477,480,1209],[0]),([37,186,23,0,1,2,3,4,5],[35,77,142,582,1109,1287,1288,1289],[0]),([69,0,1,2,3,4,5,71],[4,143,553,739,1290,1291,1292,1293],[1]),([108,242,0,1,2,3,4,5],[4,148,251,480,660,662,708,1126,1294],[]),([0,219,2,3,4,5,36],[142,407,701,1295],[0]),([175,0,18,2,3,4,5],[13,60,89,174,536],[0]),([160,156,0,1,2,3,4,5],[4,13,77,142,148],[]),([111,168,170,1,2,3,5],[60,183,205,234,783,1296],[1]),([0,1,31,2,3,4,5,79],[13,142,220,245,249,477,490,596,597,1297,1298,1299,1300],[]),([0,293,1,2,3,4,5,36],[13,142,152,154,170,1301,1302],[]),([368,0,197,1,2,3,4,5],[35,77,148,290,1287,1303,1304,1305],[]),([0,1,31,2,3,104,5],[35,67,257,477,1306,1307,1308],[0]),([37,209,0,1,2,3,4,5],[148,249,581,582,583,587,588],[0,1]),([0,1,2,32,4,5],[35,148,162,220,309,468],[]),([0,1,18,132,3,4,5],[4,13,397,477,1163,1309],[0]),([122,0,1,18,2,3,4,5],[13,142,225,353,1087,1132,1200,1310,1311],[0]),([69,0,219,2,3,4,5],[4,140,142,143,739,1312,1313,1314,1315,1316,1317,1318],[]),([0,1,18,2,3,20,4,5],[4,13,357,477,514,1087,1319,1320,1321],[0]),([69,0,1,2,3,4,5,258],[4,35,142,148,729,1322,1323,1324,1325,1326],[]),([37,123,0,1,18,2,3,4,5],[13,35,60,77,582,1163,1327,1328],[0]),([243,186,0,1,2,3,4,5],[89,142,143,148,249,573,601,1096,1097,1187,1329,1330,1331],[0]),([69,0,1,2,3,279,4,5],[4,143,148,220,235,724,725,739,1036,1150,1332,1333,1334,1335,1336,1337],[]),([0,1,2,3,4,5,369],[4,159,799,1338,1339,1340,1341],[]),([69,0,1,2,3,4,5,14],[4,143,148,149,243,280,281,550,671,861,1342,1343],[]),([123,17,18,2,3,4,5],[4,13,35,39,329,330,383,400,1344,1345],[0]),([186,0,1,2,3,4,5,217],[13,162,224,390,391,847,1079,1080,1081,1084,1128,1346,1347,1348],[]),([246,0,2,3,4,5,36],[4,13,142,149,799,1349],[]),([41,17,18,2,3,4,5],[13,22,39,56,326,329,330,393,810,1350],[0]),([17,0,1,2,3,42,4,5],[148,160,224,259,376,507,876,1091,1093,1231,1351,1352],[0]),([69,175,0,1,2,3,4,5,14],[4,13,14,60,142,174,281],[]),([0,1,18,2,3,57,4,5],[4,13,808,1277,1353],[]),([17,18,2,3,4,5,190],[4,39,56,326,329,1354,1355,1356,1357],[0]),([0,1,210,3,4,5,14],[4,13,14,142,280,1358,1359,1360],[]),([37,41,17,0,1,2,3,4,5],[247,249,582,633,810,1091,1138,1256,1361,1362,1363],[0]),([206,0,1,2,3,4,5],[13,89,140,142,148,149,159,224,314,316,634,1364],[0]),([246,0,203,2,3,4,5],[4,210,548,786,1365,1366,1367,1368],[0]),([37,0,1,18,2,3,189,4,5],[4,148,224,247,249,1087,1112,1369],[0]),([0,1,2,3,4,5,370],[4,13,148,162,969,1370,1371,1372,1373,1374,1375],[]),([0,1,2,3,371,4,5],[89,142,225,1376,1377,1378,1379],[]),([108,0,1,2,3,19,4,5],[4,35,85,249,480,1110,1200,1380,1381,1382,1383,1384],[0]),([237,17,0,1,2,3,4,5],[89,143,162,224,246,469,636,1091,1092,1231,1254,1385,1386],[0]),([0,1,372,2,3,4,5],[35,140,148,149,1163,1174,1387,1388,1389,1390],[]),([0,1,18,2,3,194,4,5,79],[13,220,249,257,477,490,596,1087,1391],[0]),([83,0,1,2,3,4,5],[60,140,142,143,148,1392,1393],[1]),([255,69,0,2,3,4,5],[142,220,225,1015,1394,1395,1396,1397],[0]),([0,1,2,3,4,38,5,359],[60,224,639,1230,1398,1399],[]),([373,0,1,2,3,4,5,29],[4,13,1400,1401,1402,1403,1404,1405],[1]),([260,0,1,2,3,61,4,5],[4,13,695,696,698,919,920,944,1053],[]),([0,374,1,2,3,4,5],[4,138,140,149,159,210,1406,1407,1408],[]),([17,18,2,3,4,38,5],[4,22,326,330,400,639,1409,1410],[0]),([111,17,18,2,3,4,5],[13,39,60,329,330,1206,1411],[0]),([17,18,90,2,3,4,5],[13,39,266,326,329,330,341,364,1412],[0]),([142,41,69,0,1,2,3,4,5],[142,235,553,631,724,1011,1036,1083,1085,1138,1413],[]),([24,0,2,3,86,4,5,36],[77,224,368,369,552,815,819,1076,1077,1115,1116,1414],[1]),([186,0,1,2,3,215,4,5],[4,142,388,1006,1007,1008,1009,1187,1415,1416,1417,1418],[0,1]),([108,17,18,2,3,4,5],[4,22,35,39,326,329,1419,1420],[0]),([0,1,2,3,42,4,5,14],[13,60,142,143,174,259,281,376,1421],[1]),([97,98,0,1,2,3,5],[4,35,257,477,1422,1423,1424,1425],[0]),([0,1,2,3,4,5,29],[13,140,148,488,1119,1188],[]),([0,1,2,3,57,5,58],[4,13,60,1426,1427,1428],[1]),([17,0,1,2,3,4,5,217],[162,220,246,391,1003,1079,1080,1081,1084,1091,1093,1363,1429,1430,1431],[0]),([107,0,1,2,3,4,25,5,36],[35,60,77,142,152,674,1268,1432,1433],[0]),([0,1,103,2,3,4,7,5,14],[13,14,60,174,671,784,1434,1435,1436,1437],[0,1]),([0,1,375,2,3,4,5],[13,140,142,148,149,1438,1439,1440,1441],[]),([376,0,1,2,3,4,5],[4,89,142,149,210,224,585,1442],[]),([17,31,18,2,3,4,5],[4,22,35,39,71,89,266,324,326,329,330,351,1298,1443,1444],[0]),([0,377,18,2,3,4,5],[4,13,35,60,89,1174,1445,1446,1447,1448,1449],[]),([98,17,18,2,3,4,5],[4,13,22,329,330,1450],[0]),([0,1,2,3,4,249,14],[13,35,143,523,1226,1451],[0]),([0,1,18,210,3,4,5],[4,13,257,337,1163,1358,1452],[0]),([378,17,18,2,3,4,5],[4,13,22,35,39,329,330,400,1453,1454,1455],[]),([142,0,1,2,117,4,5],[89,148,162,220,498,500,647,855,882,1456,1457,1458,1459],[]),([0,380,1,2,3,4,5],[4,148,224,1460,1461,1462,1463,1464],[]),([381,0,1,2,3,5,190],[148,149,1184,1355,1465,1466],[]),([0,1,2,3,4,5,382],[4,205,220,1466,1467,1468,1469,1470],[]),([180,0,6,2,3,4,5],[142,220,249,597,1471],[]),([0,1,2,3,383,4,5],[4,148,225,1015,1472,1473,1474,1475,1476,1477],[]),([17,18,2,3,19,4,5],[4,13,22,56,85,326,352,400,1478,1479],[0]),([384,0,1,2,3,4,5],[13,143,210,249,597,1480,1481],[]),([0,1,2,3,4,5,385],[13,35,140,148,891,1482,1483,1484],[]),([0,1,2,386,3,4,5],[13,140,142,149,159,224,1087,1485,1486,1487,1488,1489],[]),([37,0,1,18,76,2,3,4,5],[4,1087],[0,1]),([37,0,1,387,2,3,4,5],[13,35,581,1490,1491,1492,1493],[]),([0,1,2,3,4,5,389],[13,35,60,142,148,1494,1495,1496,1497],[]),([0,1,390,2,3,4,5],[35,89,141,142,224,645,647,1498],[]),([0,1,18,2,3,4,5,232],[4,35,450,1163,1174,1499,1500,1501],[0]),([17,18,2,3,4,104,5],[4,13,35,39,56,327,329,330,346,1502],[0]),([0,1,18,2,3,194,4,5],[13,35,142,148,282,283,477,490,1087,1182,1391,1503,1504,1505,1506],[0]),([17,231,18,2,3,4,5],[4,39,326,329,330,400,449,1507,1508,1509],[0]),([69,8,0,2,3,5],[4,18,140,148,198,205,251],[0]),([391,0,1,2,3,4,5],[35,89,138,140,148,210,1238,1510,1511,1512,1513],[]),([392,0,1,2,3,4,5],[4,89,149,159,676,1514,1515],[]),([0,301,18,2,3,4,5],[4,13,89,148,1219,1516,1517],[]),([381,0,1,2,3,4,5,79],[4,138,148,149,220,225,596,597,721,1299,1466,1518,1519,1520,1521],[]),([97,17,18,2,3,4,5],[35,39,56,326,1522,1523],[0]),([69,0,1,2,3,4,5,14,153],[4,13,60,225,243,249,281,724,1524],[0]),([81,0,6,2,3,7,5],[332,854,856,857,858,1238,1525],[0,1]),([184,0,1,2,3,4,5],[13,89,140,142,148,149,159,224,366,625,1526,1527,1528],[]),([242,17,18,2,3,4,5],[4,13,22,35,56,89,326,501,660,1529,1530],[0]),([260,69,1,2,3,4,5,14],[4,13,60,143,243,249,730,739,924,946,948,1276,1531],[]),([17,0,1,2,3,4,5,149],[148,156,224,291,435,483,1093,1141,1532,1533,1534],[0]),([218,0,1,2,3,4,5],[60,89,138,140,143,148,607,1091,1206,1533,1535],[0]),([0,1,18,2,3,4,5,225],[4,13,428,477,1170,1536,1537],[0]),([108,0,1,2,3,152,4,5],[4,13,35,138,143,220,225,976,1013,1018,1383,1538,1539,1540],[]),([393,0,1,2,3,4,5],[35,138,140,142,148,149,1541,1542],[]),([0,394,1,2,3,4,5],[35,60,140,1543,1544,1545,1546],[]),([226,17,0,2,3,4,5],[4,605,1547,1548,1549,1550],[0]),([0,269,1,2,3,4,5,79],[13,142,143,249,597,901],[]),([224,17,18,2,3,4,5],[4,56,326,329,330,1551,1552],[0]),([0,1,2,3,4,249,36],[35,142,705,1226,1553,1554,1555],[]),([37,23,0,1,18,2,3,4,5],[13,35,77,582,1556,1557],[]),([17,0,1,210,3,4,5],[140,220,224,246,337,1091,1358,1360,1558,1559],[0]),([184,0,1,2,140,3,4,5],[13,137,142,148,159,366,624,625,1527,1528,1560],[0]),([395,0,1,2,3,4,5],[35,89,138,140,148,149,159,1493,1561,1562,1563,1564],[]),([207,0,1,18,2,3,4,5],[4,13,148,1132,1565],[0]),([396,0,1,2,3,4,5],[89,143,159,210,249,581,585],[]),([175,0,2,3,4,5,29],[13,60,1119,1566],[0]),([237,0,1,18,2,3,4,5],[4,13,143,480,1386,1567,1568],[0]),([255,0,1,2,3,4,5,14],[13,14,142,149,223,225,280,281,671,1205,1569,1570,1571],[]),([37,242,17,0,1,2,3,5],[251,489,1093,1095,1231,1234,1235,1236,1254,1256],[0]),([17,0,1,2,3,189,4,5],[220,224,359,503,1091,1092,1184,1362,1572,1573,1574,1575,1576],[0]),([255,0,18,2,3,4,5],[13,35,89,220,225,1015,1577,1578,1579],[]),([292,0,6,1,2,3,4,5,14],[13,60,174,223,224,243,313,831,832,833,836],[]),([254,0,18,2,3,4,5],[4,143,519,521,1580,1581,1582,1583,1584],[]),([0,1,18,2,3,4,5,217],[391,480,1079,1080,1084,1164,1165],[0]),([175,0,1,2,3,4,5],[4,13,60,89,140,142,148,159,210,220,1119,1566,1585],[]),([0,397,1,2,3,4,5],[4,138,140,149,159,210,224,1406,1586,1587,1588,1589],[]),([0,135,1,2,3,4,5,36],[4,142,149,154,739,750,753,1590],[]),([168,170,1,2,3,5,36],[4,35,152,154,183,186,191,368,774],[0,1]),([24,0,1,2,3,4,5,217],[142,162,220,224,391,812,819,847,848,1079,1080,1081,1086,1414,1430],[]),([0,1,2,3,398,4,5],[4,148,224,1591,1592,1593,1594,1595],[]),([0,1,31,2,3,152,4,5],[13,220,224,225,477,976,1013,1015,1054,1297,1298],[]),([0,1,2,3,4,5,399],[4,143,148,1596,1597,1598,1599,1600],[]),([379,0,1,2,3,4,5,14],[4,143,148,149,281,550,1451,1600,1601],[]),([236,0,1,2,3,4,5],[4,89,143,149,159,210,224,639,1398,1602,1603,1604,1605],[0]),([333,0,1,18,2,3,4,5],[89,225,480,1037,1038,1039,1132,1606],[]),([0,1,2,3,4,147,5,36],[13,60,77,152,153,154,369,530,552,665,1607],[0]),([400,0,1,2,3,4,5],[4,138,140,149,159,210,224,739,1608,1609,1610,1611,1612,1613],[]),([186,227,1,2,3,4,5],[4,1417,1465,1614,1615,1616,1617,1618],[]),([0,388,1,2,3,25,5],[35,140,148,1268,1544,1546,1619,1620,1621,1622],[]),([401,0,1,2,3,4,5],[4,13,89,138,142,585,1623,1624],[]),([191,0,1,2,3,4,5],[4,89,138,143,159,210,1184,1355,1465,1625],[0]),([142,0,1,73,2,3,4,5],[142,635,647,809,810,811,814,1011,1413,1626],[1]),([0,1,18,2,3,235,4,5],[4,35,458,1294,1383,1627,1628],[0]),([0,1,402,2,3,4,5],[35,140,148,149,224,805,819,1490,1629,1630,1631,1632,1633],[]),([0,1,2,3,222,4,5,14],[13,60,162,174,281,1026,1027],[0,1]),([242,0,1,2,3,4,5,29],[13,142,274,480,1188],[]),([168,0,1,2,3,4,5,204],[77,224,301,319,322,777,1634,1635,1636],[0]),([0,1,2,3,4,5,403],[13,142,148,224,225,1570,1637,1638,1639,1640,1641],[]),([186,0,1,2,3,194,4,5],[142,276,282,283,1187,1329,1503,1504,1642,1643],[0]),([0,1,31,2,3,25,5],[13,35,257,1297,1644,1645],[]),([0,1,404,2,3,4,5],[35,89,138,140,220,1646,1647,1648,1649,1650,1651],[]),([186,173,1,2,3,4,5],[13,60,89,142,607,610,1185],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_1 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_1 = true := by decide +kernel
def N_22_8_2 : List NodeSpec := [([0,1,18,2,3,189,4,5],[13,35,142,258,359,477,1112,1369,1572,1573,1574,1576],[0]),([0,1,31,2,3,4,5,14],[13,14,35,60,143,162,174,245,281,1652],[]),([405,0,1,2,3,4,5],[13,60,77,89,140,142,148,149,159,1106,1653,1654,1655],[]),([108,0,1,2,3,4,5],[4,35,89,138,140,148,149,159,220,488,1419,1656],[]),([406,0,1,2,3,4,5],[35,77,138,143,149,210,545,759,1287,1657,1658,1659],[]),([246,0,18,2,3,4,5],[4,13,89,140,505,548,803],[]),([0,1,2,407,3,4,5],[13,141,142,149,224,1185,1187,1288,1660,1661,1662],[]),([242,0,1,18,2,3,4,5],[4,13,35,89,143,148,488,660,662,708,1126,1663,1664],[0]),([81,0,1,2,117,4,5],[148,220,498,500,553,882,1238,1456,1665,1666,1667,1668,1669,1670],[1]),([0,1,18,2,3,4,5,79],[13,35,143,149,220,249,487,488,490,596,597,721,1299,1518,1671],[0]),([0,1,201,2,3,4,5],[35,89,140,148,149,1672,1673,1674,1675],[]),([0,362,1,2,3,152,4,5],[4,13,220,225,1013,1015,1054,1407,1676,1677],[]),([0,1,2,3,152,61,4,5,36],[77,142,152,154,369,697,698,1052,1054],[0]),([333,0,1,2,3,4,14],[13,149,162,225,976,1678,1679,1680,1681],[]),([0,362,1,2,3,25,5],[140,148,205,786,1406,1407,1676,1682,1683],[]),([0,1,2,3,4,408,5],[4,14,60,142,162,1684,1685,1686,1687],[]),([0,362,1,2,3,4,5,14],[4,13,14,148,149,1253,1676],[]),([254,0,203,2,3,4,5],[4,210,521,1688,1689],[]),([0,362,1,2,3,38,5],[4,148,639,1406,1677,1690,1691],[]),([0,1,18,2,3,4,5,200],[35,297,477,1225,1692],[0]),([69,0,197,1,2,3,4,5],[4,35,77,142,729,1106,1287,1305,1693,1694],[]),([24,0,1,2,3,4,5,87],[142,148,220,231,249,825,842,1695,1696,1697,1698,1699,1700],[1]),([69,0,1,2,3,152,4,5,14],[4,13,143,223,225,281,724,1013],[]),([0,362,1,2,3,4,5,79],[4,13,220,490,553,596,1253,1299,1407,1676,1701],[]),([0,377,2,3,4,5,36],[60,142,149,705,1445,1702,1703,1704],[1]),([0,1,2,3,152,4,5,223],[13,77,224,225,414,415,416,417,1013,1015,1705],[0]),([0,1,2,3,4,348,36],[4,60,142,224,701,1127],[]),([0,1,2,3,4,38,5,348],[4,60,224,1127,1128,1130,1398,1418,1706],[]),([186,197,1,2,3,4,5],[35,77,142,1185,1287],[]),([186,409,1,2,3,4,5],[142,553,1074,1707],[]),([410,0,1,2,3,4,5],[4,89,143,149,159,210,224,1708,1709,1710,1711,1712,1713],[]),([37,41,186,0,1,2,3,4,5],[249,401,582,631,633,1138,1288,1347,1348,1714,1715],[]),([0,1,2,3,57,25,5],[13,148,1277,1716],[]),([255,0,1,2,3,4,5,403],[142,225,1570,1637,1638,1639,1717,1718],[]),([333,129,0,1,2,3,4,5],[138,162,225,1037,1038,1039,1269,1406,1679,1719,1720,1721,1722,1723,1724,1725,1726,1727],[]),([0,208,1,2,3,86,4,5],[13,89,142,553,585,1728,1729,1730],[]),([37,186,0,1,2,3,189,4,5],[148,224,247,249,267,1187,1572,1715,1731],[]),([0,1,412,2,3,4,5,79],[13,35,149,249,490,596,597,1732,1733],[]),([0,1,2,3,4,359,190],[60,148,1228,1231,1355,1465,1734,1735],[]),([186,310,1,2,3,4,5],[4,13,794,795,796,1417,1736,1737],[1]),([242,85,0,1,2,3,4,5,36],[13,142,154,173,368,701,717],[]),([168,170,203,1,2,3,5],[183,191,205,321,774,1368,1738],[0,1]),([0,1,2,3,57,4,5,29],[4,13,60,142,148,174,1739],[]),([17,0,1,2,3,194,4,5],[282,283,1091,1092,1093,1183,1503,1504,1740],[0]),([166,129,0,1,2,3,4,5],[89,224,249,1269,1270,1407,1720,1722,1723,1741,1742,1743],[]),([0,1,2,91,3,4,5],[141,149,224,260,341,418,419,1091,1093,1533,1744],[0]),([186,156,1,2,3,4,5],[77,142,701],[]),([0,1,18,2,3,222,4,5],[4,13,35,459,477,1026,1027,1028,1087,1132,1745],[0]),([23,0,1,2,3,4,25,5,36],[35,77,142,152,674,801,1268,1433],[]),([186,0,1,2,3,61,4,5],[530,695,696,697,698,1053,1187,1288,1329,1714,1746,1747,1748],[0]),([0,263,1,2,3,4,5],[4,138,140,149,159,210,224,1749,1750,1751,1752],[0]),([23,254,0,2,3,4,5],[4,140,519,521,545,1688,1753,1754],[0]),([69,0,1,2,3,4,5,348],[4,60,142,143,148,739,1127,1128,1130,1706,1755,1756,1757],[]),([186,0,1,2,3,42,4,5],[13,142,148,160,224,259,375,376,507,876,1187,1418,1758,1759],[0]),([0,1,2,3,414,4,5,14],[13,140,148,174,1760,1761],[]),([415,0,1,2,3,4,5],[4,138,142,149,159,210,220,1762,1763,1764],[]),([186,1,2,140,3,4,5],[13,89,137,141,142,148,224,343,1185,1187,1765,1766],[0,1]),([186,0,1,2,3,4,5,225],[4,224,249,426,428,1417,1536,1767,1768,1769],[]),([0,1,201,18,2,3,4,5,79],[13,220,258],[0]),([37,186,0,1,238,2,3,4,5],[148,249,581,1187,1770,1771],[0]),([416,0,1,2,3,4,5],[13,60,89,140,142,148,1185,1288,1772],[]),([186,0,1,210,3,4,5],[4,224,335,337,1288,1358,1360,1773],[]),([417,0,1,2,3,4,5],[35,138,143,1492,1774],[]),([37,186,0,1,2,3,38,5],[4,148,247,249,317,439,1111,1113,1114,1715,1748,1775],[0]),([237,186,0,1,2,3,4,5],[4,89,143,162,224,470,636,1128,1288,1329,1386],[]),([0,197,1,2,3,4,7,5],[35,77,290,784,1287,1304,1776,1777],[0]),([37,0,1,18,2,3,19,4,5],[13,35,225,247,258,480,553,1087,1112,1132],[0]),([37,242,186,0,1,2,3,5],[148,249,502,1187,1234,1235,1236,1331,1418,1715,1748],[0]),([187,0,1,2,3,4,5],[13,89,142,210,249,253,585,1778],[0]),([186,0,1,2,3,189,4,5],[142,220,224,267,359,503,1329,1417,1572,1573,1574,1575,1576,1714],[0]),([186,226,0,2,3,4,5],[4,220,439,560,605,1779,1780,1781,1782],[0]),([37,186,0,1,2,3,86,4,5],[89,142,247,249,553,1074,1128,1187,1714,1715,1728],[]),([168,1,387,2,3,4,5],[35,89,1493,1783,1784],[]),([418,0,1,238,2,3,4,5],[13,142,148,581,1770,1785,1786,1787],[]),([17,0,1,2,3,4,5,225],[159,205,249,428,1184,1536,1767,1788,1789],[0]),([0,1,2,3,4,5,419],[4,13,148,1493,1790,1791,1792,1793,1794],[]),([0,1,18,2,3,4,5,125],[13,35,60,148,245,257,258,350,372,1087,1795,1796],[0,1]),([186,0,1,2,3,194,4,5,79],[220,249,276,282,439,596,721,1187,1417,1642],[0]),([0,1,2,3,4,82,190],[4,60,101,148,1465,1797,1798,1799],[]),([143,0,1,2,3,4,5],[13,89,137,140,142,148,149,224,237,623,626,627,628,1800,1801],[]),([24,0,1,2,3,4,5,204],[77,89,224,301,319,320,805,819,1802,1803,1804],[0]),([166,0,1,18,2,3,4,5],[4,13,89,1132,1742,1805],[]),([0,1,2,3,4,25,5,204],[4,77,89,159,224,301,319,320,322,1634,1803,1804,1806],[0]),([69,0,1,2,3,4,5,82],[4,143,148,729,739,1797,1807,1808,1809,1810,1811,1812],[1]),([0,1,31,2,3,4,5,29],[13,35,41,245,249,257,1119,1813],[0]),([420,0,1,2,3,4,5],[35,89,138,140,148,149,159,210,645,1011,1814,1815,1816,1817],[]),([142,0,1,2,3,4,204],[4,77,89,301,319,645,855,1804,1818,1819],[0]),([421,0,1,2,3,4,5],[4,138,140,148,149,159,224,1268,1368,1738,1820,1821,1822],[]),([422,0,1,2,3,4,5],[35,89,138,140,149,210,224,332,1238,1823,1824,1825,1826,1827],[]),([423,0,1,2,158,3,4,5],[13,35,142,148,159,224,341,917,940,1828,1829,1830],[1]),([424,0,1,2,3,4,5],[13,138,140,148,159,174,210,280,1451,1831,1832,1833],[]),([175,0,203,2,3,4,5],[60,174,526,1834,1835],[]),([37,0,1,2,3,39,5],[140,148,162,248,249,1836,1837],[0,1]),([425,0,1,2,3,4,5],[4,138,143,149,1368,1838,1839],[]),([0,1,2,3,426,4,5],[4,60,148,149,174,1840,1841,1842,1843,1844,1845],[]),([427,0,1,2,3,4,5],[89,143,148,159,210,249,597,721,1846,1847,1848],[]),([142,197,1,2,3,4,5],[35,645,1106,1287],[]),([37,0,1,18,2,3,4,5],[4,13,35,89,143,148,247,249,488,581,582,583,585,1671],[0]),([37,17,0,1,2,3,189,4,5],[148,224,247,249,359,1093,1256,1849],[0]),([0,428,197,1,2,3,4,5],[13,35,77,1106,1304,1850],[]),([255,0,1,2,3,4,5],[85,89,148,159,162,210,225,1851,1852,1853],[]),([168,23,170,1,2,3,5],[35,183,205,545,1854],[0]),([0,1,430,2,3,4,5],[13,35,148,1855,1856],[]),([175,0,2,3,4,5,36],[60,142,369,792,1857],[0]),([23,0,1,2,202,4,5],[35,220,303,805,1109,1159,1287,1858,1859,1860,1861],[]),([255,0,6,2,3,4,5],[220,225,1015,1862,1863,1864,1865],[]),([0,388,1,2,3,4,5,36],[35,77,142,148,152,705,1497,1544,1866],[]),([142,69,1,2,3,152,4,5],[143,235,553,739,742,1147,1148,1149,1150,1867,1868],[]),([0,1,2,3,4,25,5,249],[35,509,510,1226,1869,1870],[0]),([254,0,2,3,4,5,36],[4,140,142,149,1871],[1]),([0,1,2,3,4,25,5,258],[35,159,542,1322,1323,1324,1325,1872,1873,1874],[0]),([69,0,1,2,3,4,5,249],[4,35,148,509,729,1226,1869,1875,1876,1877],[]),([0,1,2,3,431,4,5,249],[35,140,509,1226,1869,1875,1878,1879],[]),([142,0,1,210,3,4,5],[4,220,337,1011,1358,1360,1558,1880],[]),([37,0,1,18,2,3,152,4,5],[13,35,143,225,247,258,480,1013,1087,1112],[]),([0,432,1,2,3,4,5],[35,77,138,140,148,149,210,231,805,1109,1287,1881,1882,1883,1884,1885],[]),([37,0,197,1,2,3,4,5],[13,77,148,249,1287,1305,1492],[]),([23,24,1,2,3,25,5],[35,232,239,545,1287],[0]),([23,246,0,2,3,4,5],[4,13,140,142,505,549,1366,1854],[0]),([433,0,1,2,3,4,5],[35,60,89,138,140,143,149,159,210,729,1036,1886,1887,1888,1889,1890,1891],[]),([0,434,1,2,3,4,5],[35,140,143,148,705,1892,1893,1894],[]),([175,0,1,2,3,4,38,5],[13,142,148,174,460,461,639,693,763,1895,1896,1897],[1]),([23,0,1,2,3,4,7,5,14],[13,35,60,77,142,280,784,1898],[]),([69,0,145,1,2,3,4,5],[4,13,142,148,224,631,632,634,690,730,1036,1085,1899],[0]),([23,175,0,2,3,4,5],[13,60,522,1897,1900],[0]),([0,435,1,2,3,4,5],[35,140,1544,1546,1901,1902,1903],[]),([69,0,1,2,3,86,4,5,14],[4,142,223,243,281,550,553,1728],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_2 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_2 = true := by decide +kernel
def N_22_8 := N_22_8_0 ++ N_22_8_1 ++ N_22_8_2
def B_22_8 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_8
set_option maxRecDepth 500000 in
lemma B_22_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 8 xs.toFinset) B_22_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_22) (raw := r_22) (pspecs := ps_22) (used := [0,4,10,13,14,18,22,35,39,41,48,56,60,67,71,74,77,85,89,101,137,138,140,141,142,143,146,148,149,152,153,154,156,157,158,159,160,161,162,170,173,174,183,185,186,190,191,192,194,195,196,198,205,207,209,210,219,220,223,224,225,228,231,232,234,235,237,239,240,243,245,246,247,248,249,251,253,254,257,258,259,260,265,266,267,273,274,276,280,281,282,283,290,291,297,301,303,304,309,311,312,313,314,316,317,318,319,320,321,322,324,326,327,329,330,332,335,337,341,343,345,346,350,351,352,353,357,359,363,364,366,368,369,372,375,376,382,383,386,387,388,390,391,393,397,400,401,407,414,415,416,417,418,419,426,428,435,438,439,443,449,450,451,458,459,460,461,466,467,468,469,470,477,480,483,486,487,488,489,490,493,498,500,501,502,503,505,507,509,510,514,517,519,521,522,523,526,530,536,537,542,545,548,549,550,551,552,553,554,556,560,573,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1198,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208,1209,1210,1211,1212,1213,1214,1215,1216,1217,1218,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248,1249,1250,1251,1252,1253,1254,1255,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1296,1297,1298,1299,1300,1301,1302,1303,1304,1305,1306,1307,1308,1309,1310,1311,1312,1313,1314,1315,1316,1317,1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1337,1338,1339,1340,1341,1342,1343,1344,1345,1346,1347,1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1367,1368,1369,1370,1371,1372,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410,1411,1412,1413,1414,1415,1416,1417,1418,1419,1420,1421,1422,1423,1424,1425,1426,1427,1428,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454,1455,1456,1457,1458,1459,1460,1461,1462,1463,1464,1465,1466,1467,1468,1469,1470,1471,1472,1473,1474,1475,1476,1477,1478,1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,1492,1493,1494,1495,1496,1497,1498,1499,1500,1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1529,1530,1531,1532,1533,1534,1535,1536,1537,1538,1539,1540,1541,1542,1543,1544,1545,1546,1547,1548,1549,1550,1551,1552,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689,1690,1691,1692,1693,1694,1695,1696,1697,1698,1699,1700,1701,1702,1703,1704,1705,1706,1707,1708,1709,1710,1711,1712,1713,1714,1715,1716,1717,1718,1719,1720,1721,1722,1723,1724,1725,1726,1727,1728,1729,1730,1731,1732,1733,1734,1735,1736,1737,1738,1739,1740,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1751,1752,1753,1754,1755,1756,1757,1758,1759,1760,1761,1762,1763,1764,1765,1766,1767,1768,1769,1770,1771,1772,1773,1774,1775,1776,1777,1778,1779,1780,1781,1782,1783,1784,1785,1786,1787,1788,1789,1790,1791,1792,1793,1794,1795,1796,1797,1798,1799,1800,1801,1802,1803,1804,1805,1806,1807,1808,1809,1810,1811,1812,1813,1814,1815,1816,1817,1818,1819,1820,1821,1822,1823,1824,1825,1826,1827,1828,1829,1830,1831,1832,1833,1834,1835,1836,1837,1838,1839,1840,1841,1842,1843,1844,1845,1846,1847,1848,1849,1850,1851,1852,1853,1854,1855,1856,1857,1858,1859,1860,1861,1862,1863,1864,1865,1866,1867,1868,1869,1870,1871,1872,1873,1874,1875,1876,1877,1878,1879,1880,1881,1882,1883,1884,1885,1886,1887,1888,1889,1890,1891,1892,1893,1894,1895,1896,1897,1898,1899,1900,1901,1902,1903]) S_22_ok
  have hm0 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def P_22_9 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [4,13,14,22,35,60,77,85,89,95,138,140,141,142,143,148,149,152,154,159,162,174,185,201,205,210,220,223,224,225,231,234,235,239,243,245,246,249,251,257,258,259,280,281,326,330,332,341,346,368,432,433,435,439,459,460,466,477,483,488,490,503,545,550,552,553,554,581,582,583,585,596,597,605,607,624,625,631,634,635,639,645,647,657,660,662,671,673,674,675,676,694,701,705,708,715,721,724,725,729,730,739,741,747,750,753,754,758,759,766,767,774,777,783,784,786,794,799,801,803,805,810,815,819,825,830,832,834,835,836,837,842,843,844,847,848,855,859,861,876,878,891,892,911,919,920,922,924,939,945,948,949,957,963,966,967,969,974,976,981,983,1000,1001,1003,1011,1012,1013,1015,1018,1026,1028,1031,1032,1035,1036,1038,1040,1042,1044,1045,1048,1051,1054,1058,1059,1061,1074,1081,1083,1086,1087,1091,1092,1093,1095,1096,1101,1106,1107,1109,1110,1112,1114,1115,1117,1119,1126,1127,1132,1139,1141,1142,1143,1148,1150,1158,1159,1163,1165,1170,1174,1179,1182,1184,1185,1186,1187,1188,1190,1200,1206,1208,1219,1223,1225,1226,1230,1231,1233,1236,1238,1244,1253,1254,1255,1256,1263,1268,1277,1279,1287,1288,1289,1297,1298,1299,1327,1328,1329,1331,1334,1335,1336,1348,1350,1354,1355,1360,1362,1363,1366,1368,1380,1382,1383,1386,1398,1401,1403,1409,1411,1412,1417,1418,1419,1430,1433,1434,1436,1451,1453,1465,1466,1490,1492,1493,1504,1505,1509,1518,1519,1521,1529,1533,1534,1538,1540,1544,1551,1552,1553,1556,1558,1567,1570,1573,1576,1600,1620,1665,1676,1679,1688,1691,1700,1701,1706,1714,1715,1719,1728,1730,1738,1742,1743,1747,1748,1767,1769,1775,1776,1804,1808,1810,1824,1825,1854,1870,1876,1896,1897,1899,1904,1905,1906,1907,1908,1909,1910,1911,1912,1913,1914,1915,1916,1917,1918,1919,1920,1921,1922,1923,1924,1925,1926,1927,1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944,1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,1955,1956,1957,1958,1959,1960,1961,1962,1963,1964,1965,1966,1967,1968,1969,1970,1971,1972,1973,1974,1975,1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031,2032,2033,2034,2035,2036,2037,2038,2039,2040,2041,2042,2043,2044,2045,2046,2047,2048,2049]
def N_22_9_0 : List NodeSpec := [([37,436,0,1,2,3,4,5],[148,205,249,581,582,583,585,1904],[0,1]),([37,0,1,2,3,189,4,5],[138,148,162,224,249,585,1492,1573],[0,1]),([0,208,1,2,3,4,5],[13,89,138,148,159,210,220,585,1730,1905,1906],[0,1]),([0,1,2,3,194,4,5],[89,143,148,1182,1504,1505,1907],[0,1]),([437,0,1,2,3,4,5,79],[220,249,490,597,721,1299,1518,1908,1909,1910],[1]),([37,0,1,2,3,38,5],[138,140,148,162,249,503,1114,1492],[0,1]),([180,0,1,2,3,4,5],[138,140,142,143,148,149,159,210,220,249,597,844,1107,1911,1912],[0,1]),([226,0,1,2,3,4,5],[4,140,142,143,149,159,210,605,673,1913,1914],[0]),([0,1,2,3,342,4,5],[60,77,89,143,148,149,210,1915,1916],[0,1]),([0,274,1,2,3,4,5],[4,13,89,149,159,205,251,675,676],[0]),([0,1,2,3,4,5,149],[89,143,148,224,435,483,1141,1915,1917],[0,1]),([0,1,2,3,4,5,217],[143,162,847,1003,1081,1086,1430],[0,1]),([0,1,2,3,42,4,5],[89,143,148,159,259,876,1918],[0,1]),([0,145,1,2,3,4,5],[13,89,140,148,149,159,631,634,1003,1899,1919],[0,1]),([142,0,1,2,3,4,38,5],[4,138,162,220,639,878,1011,1150,1398,1896,1920,1921],[0,1]),([142,224,0,1,2,3,4,5],[4,159,205,235,675,878,1011,1769],[]),([0,1,2,3,277,4,5],[4,89,143,205,220,1012,1922],[0]),([0,281,1,2,3,4,5],[4,13,35,89,138,140,148,159,220,657,1923,1924],[0,1]),([373,0,1,2,3,4,5,14],[4,14,60,143,148,174,243,280,671,1925],[0,1]),([160,0,1,2,3,4,5,36],[77,140,142,148,152,154,701,1926],[0]),([0,1,2,3,4,5,14,58],[4,13,14,148,174,433,1927,1928],[0,1]),([0,1,2,3,57,4,5,14],[13,14,60,148,162,174,281,1277,1929,1930],[0,1]),([0,1,2,3,57,4,5],[89,149,205,220,1277,1929,1930,1931],[0,1]),([292,0,1,2,3,4,5,14],[13,60,149,162,174,223,243,550,983],[0]),([292,0,1,2,3,4,5],[13,89,138,140,148,149,159,210,220,243,550,836,837,983],[0,1]),([0,1,90,2,3,4,5,14],[13,14,140,141,142,143,148,159,174,281,341,435,671],[0,1]),([41,0,1,2,3,4,5,14],[13,14,142,174,205,220,243,280,550,810,847,1003],[0,1]),([220,0,1,2,3,4,5,36],[4,142,152,701,1932],[0,1]),([85,0,1,2,3,4,5,36],[4,77,89,149,152,162,552,674,694,701,715,1117],[0,1]),([69,0,1,2,3,4,5,79],[89,138,142,148,149,220,249,251,490,553,596,597,721,724,730,739,741,1299,1518,1933],[0,1]),([69,0,1,2,3,4,5,36],[4,89,140,142,148,154,701,730],[0]),([160,0,1,2,3,4,5],[138,142,143,148,159,210,220,730,922,1934],[0,1]),([0,1,2,3,4,5,230],[4,138,140,143,148,159,220,224,553,730,747,1051],[0,1]),([243,0,1,2,3,4,5],[89,143,148,159,210,1096,1935,1936,1937],[0,1]),([69,0,1,2,3,4,5,14],[4,13,14,60,142,143,148,162,174,281,671,730,739,981,1938],[0,1]),([0,1,2,3,438,4,5],[4,143,162,220,729,741,1939,1940],[1]),([69,0,135,1,2,3,4,5],[4,148,205,553,730,739,754,957],[0,1]),([111,168,0,1,2,3,4,5],[60,142,159,210,234,607,759,766,783,1206],[0]),([168,0,1,2,3,4,5,36],[35,77,89,142,152,368,694,701,759,767,777,1941],[0,1]),([0,1,2,3,4,5,302],[60,89,143,159,224,251,1941,1942],[0,1]),([166,0,1,2,3,4,5],[89,138,148,149,159,210,224,249,251,801,1742,1743],[0,1]),([142,0,1,2,3,4,7,5],[4,89,143,235,784,855,878,1011,1436,1943],[0,1]),([186,0,1,2,3,4,5,79],[142,220,249,490,597,721,1185,1190,1299,1417,1418,1518,1714,1748,1944],[0,1]),([242,0,1,2,3,4,5,14],[13,143,162,243,550,660,662,1126,1945],[0,1]),([224,0,1,2,3,4,5,14],[13,14,142,174,205,280,671,1551,1769],[1]),([186,0,1,2,3,4,38,5],[4,89,138,140,220,639,1185,1288,1329,1398,1409,1748,1775,1896,1920,1921,1946],[0,1]),([37,242,0,1,2,3,5],[148,149,503,1236,1492,1936],[0,1]),([0,1,2,3,4,5,14,29],[13,14,60,142,174,1401,1403,1947],[0,1]),([111,186,0,1,2,3,4,5],[13,60,142,159,205,210,607,783,1185,1206,1288,1329,1411],[0]),([0,1,2,3,4,5,225],[89,143,205,251,1767,1769,1948],[0,1]),([379,0,1,2,3,4,5],[4,89,140,143,148,149,210,1600,1915,1949],[0]),([41,186,0,1,2,3,4,5],[142,159,205,224,439,631,847,1003,1288,1329,1348,1350,1417,1418,1748,1950],[0]),([142,23,0,1,2,3,4,5],[35,159,205,645,878,1011,1226,1287,1854],[0]),([37,41,0,1,2,3,4,5],[13,142,159,205,220,503,581,582,585,631,810,847,1003],[0,1]),([186,23,0,1,2,3,4,5],[4,35,89,142,159,205,224,439,1185,1226,1287,1288,1329,1854,1951],[0]),([0,1,2,3,4,5,348],[60,138,140,143,148,159,220,224,1127,1418,1706],[0,1]),([0,362,1,2,3,4,5],[89,140,148,205,220,1253,1676,1691,1701],[0]),([0,1,2,3,194,4,5,79],[140,220,249,596,597,721,1182,1504,1907],[0,1]),([334,0,1,2,3,4,5],[142,143,148,159,162,210,251,1952,1953],[0]),([0,1,103,2,3,4,5,14],[13,14,60,159,174,210,671,1434,1954],[0,1]),([0,1,18,2,3,4,5],[4,13,35,89,138,140,143,148,149,159,210,220,488],[0]),([0,1,2,3,222,152,4,5],[13,140,162,225,1001,1013,1015,1026,1028],[0]),([37,0,1,18,2,3,4,5],[4,13,35,89,142,143,148,162,249,581,582,585,1087,1112,1132,1170,1327],[0,1]),([24,1,2,3,25,5],[140,143,239,251,859,1955],[0,1]),([0,1,18,2,3,4,5,190],[4,89,143,477,1132,1139,1163,1355,1465,1956],[0,1]),([0,1,18,2,3,4,38,5],[4,138,220,639,1110,1132,1174,1398,1567,1920,1957],[0]),([37,17,0,1,2,3,4,5],[89,140,143,148,162,246,249,581,582,585,1091,1092,1093,1231,1254,1256,1958,1959],[0]),([246,0,1,2,3,4,5],[4,89,138,140,142,148,149,159,210,251,799,803,1366],[0,1]),([224,0,1,18,2,3,4,5],[4,13,205,477,1132,1163,1567],[0]),([242,0,1,18,2,3,4,5],[4,13,35,89,142,143,148,477,660,662,708,1101,1110,1126,1132,1936,1960],[0]),([0,1,2,3,4,5,249],[35,140,143,148,210,1226,1553,1915],[0,1]),([0,1,18,90,2,3,4,5],[13,89,140,141,142,143,148,159,210,224,257,341,435,1087,1132,1142,1567],[0,1]),([108,0,1,2,3,4,5],[4,35,89,138,140,143,148,149,159,210,220,224,1132,1158,1419],[0,1]),([142,72,0,1,2,3,4,5],[140,235,635,855,878,1011,1825,1961,1962,1963],[0,1]),([37,0,1,2,3,152,4,5],[13,138,143,148,149,162,220,249,503,581,585,1013,1015,1018,1054,1492,1964],[0,1]),([98,0,1,18,2,3,4,5],[4,13,140,148,1110,1163,1567],[0,1]),([107,0,1,2,3,4,5,36],[13,77,142,210,674,694,705,1965,1966],[0]),([23,0,1,2,3,4,7,5],[13,35,89,224,545,784,794,1287,1436,1943,1967],[0,1]),([0,1,2,3,4,5,355],[60,89,138,143,148,159,220,224,815,1968,1969],[0,1]),([37,0,208,1,2,3,4,5],[148,205,249,581,585,1905,1906],[0,1]),([242,186,0,1,2,3,4,5],[89,142,143,148,660,662,708,1126,1329,1331,1417,1418,1529,1748,1936,1970],[0]),([0,1,18,2,3,152,4,5],[4,13,89,142,143,220,976,1015,1054,1110,1132,1538,1971],[0]),([0,1,31,2,3,4,5],[35,89,138,140,143,148,159,205,210,220,245,257,466,1298],[0,1]),([0,1,2,140,3,4,5],[13,89,141,148,159,624,625,1915,1972],[0,1]),([0,1,2,3,4,5,14,153],[13,174,220,243,550,1973,1974],[0,1]),([333,0,1,2,3,4,5],[89,140,148,149,159,162,210,225,974,976,1038,1679,1719,1975],[0]),([186,0,1,90,2,3,4,5],[13,140,141,142,148,224,341,435,439,1185,1186,1187,1288,1329,1412,1418],[0]),([255,0,1,2,3,152,4,5],[162,220,225,1015,1018,1058,1059,1061,1540],[]),([186,0,1,2,3,4,5,36],[89,142,152,162,439,552,674,694,701,1418],[0,1]),([142,0,203,1,2,3,4,5],[4,159,205,635,645,855,878,1011,1490,1738,1804],[0,1]),([24,0,1,2,3,4,5,36],[35,77,89,142,152,154,162,231,552,694,701,815,819,843,1976],[0,1]),([17,0,1,2,3,4,5,190],[1091,1092,1139,1184,1231,1355,1465,1977],[0]),([69,0,1,2,3,86,4,5],[4,138,142,148,220,251,553,741,1074,1728,1978],[0]),([224,17,0,1,2,3,4,5],[159,205,224,675,1091,1092,1184,1231,1551,1769],[0]),([108,0,1,18,2,3,4,5],[4,35,89,143,257,1110,1132,1158,1163,1383,1419],[0]),([17,0,1,90,2,3,4,5],[140,141,148,224,246,341,435,1091,1092,1093,1231,1533,1534],[0]),([168,0,203,1,2,3,4,5],[224,759,766,777,1368,1490,1738,1804,1941],[0,1]),([0,1,2,3,19,4,5],[13,85,142,148,149,162,220,477,1110,1174,1380,1382],[0,1]),([17,18,2,3,4,5],[22,89,95,326,330],[0]),([0,1,18,2,3,19,4,5],[4,13,85,142,220,477,1110,1174,1200,1380,1382],[0,1]),([69,0,1,2,3,152,4,5],[4,13,89,138,142,143,148,220,225,251,553,724,729,739,741,976,1013,1015,1018,1044,1054,1979],[0,1]),([242,17,0,1,2,3,4,5],[89,143,148,660,662,708,1091,1092,1095,1126,1184,1231,1254,1533,1936,1980],[0]),([0,1,321,2,3,4,5],[13,35,89,138,140,148,149,159,220,891,892,1981,1982],[0,1]),([97,0,1,18,2,3,4,5],[35,89,143,148,257,477,1132,1225],[0]),([111,17,0,1,2,3,4,5],[60,159,205,210,246,607,783,1091,1092,1206,1533],[0]),([381,0,1,2,3,4,5],[89,138,143,148,149,159,205,210,220,1466,1519,1521],[0]),([69,0,1,18,2,3,4,5],[4,89,140,142,143,148,739,1556,1983,1984],[1]),([142,41,0,1,2,3,4,5],[35,142,159,205,220,235,631,635,810,847,855,1003,1011,1150,1950],[0]),([186,69,0,1,2,3,4,5],[4,89,140,142,143,148,725,730,739,1036],[0]),([69,0,1,2,3,4,5,230],[4,148,149,205,553,730,1048,1051],[1]),([37,260,0,1,2,3,4,5],[138,143,148,249,503,581,582,583,585,911,919,920,945,949,1492,1985,1986],[0,1]),([23,0,1,18,2,3,4,5],[4,13,35,89,143,205,210,1208,1556,1854,1987],[0,1]),([17,0,1,2,3,4,38,5],[138,140,220,246,639,1091,1092,1254,1255,1398,1533,1896,1920,1921,1988],[0,1]),([41,0,1,18,2,3,4,5],[13,142,205,224,257,477,847,1003,1110,1132,1163,1165,1567,1950],[0]),([0,1,2,3,4,5,359],[60,89,140,143,148,159,220,224,1230,1231,1233],[0]),([142,69,0,1,2,3,4,5],[4,89,143,148,162,725,730,739,741,878,1011,1036,1150,1335,1989],[0]),([0,1,18,2,3,4,25,5],[4,13,89,143,148,257,786,1132,1990],[0]),([378,0,1,2,3,4,5],[4,89,138,140,143,148,159,162,210,220,477,1110,1174,1453,1991,1992],[]),([0,1,18,2,3,4,5,14],[4,13,14,89,142,143,174,1132],[0]),([0,1,2,3,4,5,29],[13,138,140,142,148,159,220,1119,1132,1179,1188],[0,1]),([224,186,0,1,2,3,4,5],[4,159,205,224,675,1288,1329,1417,1418,1552,1769],[0]),([0,1,231,18,2,3,4,5],[4,13,35,257,1132,1163,1174,1509,1567,1993],[0]),([180,0,1,2,3,4,5,79],[89,142,220,249,597,721,1107,1299,1518,1911],[0]),([0,173,1,2,3,4,5],[13,77,89,138,140,148,159,607,1915,1994],[0,1]),([142,0,1,90,2,3,4,5],[140,141,142,148,341,435,635,645,647,855,878,1011],[0]),([186,0,1,2,3,4,7,5],[89,142,784,794,1288,1329,1417,1436,1943,1995,1996],[0,1]),([255,0,1,2,3,4,5],[89,140,142,148,149,159,210,220,225,1015,1058,1059,1061,1570],[0,1]),([378,0,1,18,2,3,4,5],[4,13,35,89,143,220,257,1110,1163,1174,1453,1567,1991,1992],[0]),([186,0,1,2,3,86,4,5],[4,89,138,142,220,554,1074,1418,1997,1998,1999,2000],[0,1]),([254,0,1,2,3,4,5],[4,138,140,142,143,149,159,210,251,1688,2001],[0,1]),([41,24,0,1,2,3,4,5],[35,140,142,159,220,224,231,251,631,810,815,819,842,847,848,1003,2002],[0]),([98,0,1,2,3,4,5],[4,13,138,142,148,149,159,205,210,220,432,1279,2003],[0,1]),([168,170,1,2,3,5],[140,148,185,205,251,774],[0,1]),([0,1,18,2,3,4,104,5],[4,13,35,148,346,477,1132,1567,2004,2005],[0,1]),([186,0,1,2,3,4,5,190],[4,1139,1288,1329,1354,1355,1417,1418,1465,1977],[0,1]),([69,70,0,1,2,3,4,5],[4,148,201,205,553,730,739,2006],[0,1]),([37,186,0,1,2,3,4,5],[89,142,143,148,162,249,439,581,582,585,1187,1244,1289,1329,1418,1715,1747],[0]),([175,0,1,2,3,4,5],[89,138,140,142,148,159,174,210,220,460,1897,2007],[0,1]),([0,1,387,2,3,4,5],[4,13,89,140,148,1490,1493,1915,2008,2009],[0,1]),([23,0,1,2,3,4,25,5],[13,89,140,142,224,786,801,1268,1854,1870,2010],[0,1]),([23,0,1,2,3,4,5,14],[13,14,89,142,143,174,205,280,671,1226,1854],[0,1]),([0,1,210,3,4,5],[140,159,1360,1558],[0,1]),([81,0,6,1,2,3,4,5],[140,148,159,205,224,832,834,835,892,1238,1665,1810],[0,1]),([81,0,1,2,3,4,7,5],[4,89,143,224,332,784,1436,1810,1943],[0,1]),([0,1,18,2,3,4,5,29],[4,13,35,142,1119,1132,1179,1188],[0,1]),([0,1,31,18,2,3,4,5],[4,35,89,140,148,245,466,1110,1132,1297,1298],[0]),([0,1,2,3,222,4,5],[89,143,148,251,459,1000,1001,1026,1028],[0,1]),([0,1,2,3,4,5,82],[60,89,140,143,148,224,1808,1810,1915,2011],[0,1]),([69,81,0,1,2,3,4,5],[4,159,205,729,730,739,1036,1824],[0,1]),([81,0,1,2,3,4,5,36],[142,152,205,674,694,701,1810,1824],[1]),([81,0,1,2,3,4,5,190],[4,143,332,1139,1810,1977],[0,1]),([0,197,1,2,3,4,5],[13,35,77,140,148,149,159,210,1106,1776,1915,2012],[0,1]),([142,242,0,1,2,3,4,5],[143,148,162,235,645,660,662,708,855,1126,1150,1936,2013],[1]),([0,388,1,2,3,4,5],[35,60,89,140,148,149,1544,1620,1915,2014],[0,1]),([0,1,2,3,329,4,5],[4,89,143,148,963,966,2015,2016],[0]),([23,24,0,1,2,3,4,5],[35,140,148,159,205,224,231,805,842,1226,1287],[0]),([0,1,2,3,439,4,5],[142,143,148,149,162,220,1185,1417,1748,2017,2018],[]),([168,23,0,1,2,3,4,5],[35,159,224,545,759,766,1226,1287,1854],[0]),([237,0,1,2,3,4,5],[89,140,143,159,162,210,1386,2019,2020],[0,1]),([0,135,1,2,3,4,5],[4,13,138,140,148,149,159,220,553,750,753,957],[0,1]),([0,1,2,3,440,4,5],[89,140,143,148,149,162,220,1254,1533,2021],[]),([23,170,0,1,2,3,4,5],[13,89,142,159,205,224,758,1219,1223,1226,2022],[0,1]),([111,0,1,18,2,3,4,5],[13,89,142,143,149,205,257,783,1132,1163,1567],[0,1]),([142,1,2,3,152,4,5],[138,143,162,235,645,1148,1150],[0]),([17,0,1,2,3,4,5,79],[138,220,246,249,490,597,721,1184,1231,1254,1299,1362,1518,1533,2023],[0]),([23,69,0,1,2,3,4,5],[13,35,89,140,142,148,159,205,224,725,729,730,739,1036,1109,1226,1287,1854,1876],[0]),([0,1,2,3,4,38,5,14],[4,13,14,60,162,174,550,671,1398,1451,2024],[0,1]),([111,69,0,1,2,3,4,5],[13,142,159,205,210,607,730,739,1036],[0,1]),([23,0,1,2,3,4,5,36],[13,35,77,149,205,210,674,694,705,1226,1854,2025],[0]),([23,0,1,2,3,4,5,190],[4,13,89,142,545,1139,1226,1287,1355,1465,1977],[0,1]),([0,349,1,2,3,4,5],[13,35,89,140,159,251,1143,1961,2026],[0]),([37,23,0,1,2,3,4,5],[13,89,142,159,205,581,582,585,1226,1287,1492],[0]),([0,1,2,3,202,4,5],[89,143,162,220,251,805,1159,2002,2027],[0]),([0,1,2,3,189,4,5],[89,143,220,251,503,1492,1573,1576],[0,1]),([0,2,3,86,4,5,36],[89,142,149,162,368,552,705,1115],[0,1]),([175,0,1,2,3,4,5,14],[13,14,60,142,162,174,671,1897,2007],[0,1]),([0,1,2,3,152,4,5,14],[13,138,143,162,174,243,976,1015],[0,1]),([111,24,0,1,2,3,4,5],[60,142,159,205,210,231,607,805,1206],[0]),([441,0,1,2,3,86,4,5],[89,138,162,220,553,1074,1997,1998,1999,2028],[1]),([260,0,6,1,2,3,4,5],[89,140,220,251,830,832,834,835,892,911,920,949,1665,1985,2029,2030],[0,1]),([24,0,1,2,3,86,4,5],[89,138,142,220,251,553,554,805,819,825,1074,1700,1997,1999,2031],[0,1]),([69,0,1,2,3,438,4,5],[4,138,142,148,251,725,729,1036,1940,2032],[]),([0,1,2,3,152,4,5,36],[13,77,142,162,368,552,701,976,1015,2033],[0,1]),([123,0,1,18,2,3,4,5],[4,13,35,210,1163,1174,1328,1567],[0,1]),([0,1,2,3,4,5,153],[13,89,148,159,220,976,1040,1042,1045],[0,1]),([41,69,0,1,2,3,4,5],[13,142,159,205,224,251,631,730,739,847,1003,1036,1083],[0]),([111,0,1,2,3,4,25,5],[13,140,142,783,786,801,1206,1268,2010],[0,1]),([37,81,0,1,2,3,4,5],[142,159,205,581,582,585,1238,1492,1810],[0,1]),([0,1,2,3,4,5,339],[89,143,148,162,949,1031,1032,1035,2034],[0,1]),([0,1,2,152,4,38,5],[4,143,162,1054,1398,1915,2035],[0]),([260,1,2,3,4,5,14],[13,60,143,149,243,550,948,949,1451],[0,1]),([260,69,0,1,2,3,4,5],[4,143,148,251,725,729,730,739,741,920,924,949,1036,1985,2036],[0]),([142,0,1,2,3,86,4,5],[4,89,142,162,220,235,554,645,855,1074,1150,1997,1999,2037],[0,1]),([260,0,1,2,3,4,5,36],[77,89,142,152,368,552,694,701,911,945,949,1985,2038],[0,1]),([0,1,2,3,4,25,5,14],[13,14,143,148,174,786,801],[0]),([69,0,1,2,3,4,5],[4,89,140,143,148,149,159,205,210,251,861],[0]),([142,326,0,1,2,3,4,5],[4,89,855,878,939,1011,1150,1263,2039,2040,2041],[1]),([0,1,2,202,4,5],[143,148,162,220,1159,2027,2042],[0,1]),([142,0,6,1,2,3,4,5],[4,35,89,140,148,162,830,832,834,835,855,878,892,1011,1150,2043,2044],[0,1]),([0,1,18,2,3,4,5,79],[13,35,142,149,220,249,258,477,597,721,1110,1132,1174,2045],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_9_0 : checkNodesBT W_22 g_22 F_22 P_22_9 A_22 B_22_8 9 N_22_9_0 = true := by decide +kernel
def N_22_9_1 : List NodeSpec := [([41,17,0,1,2,3,4,5],[159,205,220,224,246,631,810,847,1003,1091,1092,1184,1231,1254,1363,1950],[0]),([24,0,1,2,3,4,5,79],[138,220,249,251,490,597,721,805,815,819,825,1299,1518,2046],[0,1]),([0,1,2,3,279,4,5],[89,143,148,220,235,645,1150,1334,1336],[0,1]),([0,331,1,2,3,4,5],[4,13,89,148,149,939,967,969,2047,2048,2049],[0]),([0,1,2,3,4,25,5,36],[4,13,77,89,142,368,701,786,801,1433],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_9_1 : checkNodesBT W_22 g_22 F_22 P_22_9 A_22 B_22_8 9 N_22_9_1 = true := by decide +kernel
def N_22_9 := N_22_9_0 ++ N_22_9_1
def B_22_9 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_9
set_option maxRecDepth 500000 in
lemma B_22_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 9 xs.toFinset) B_22_9 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_22) (raw := r_22) (pspecs := ps_22) (used := [4,13,14,22,35,60,77,85,89,95,138,140,141,142,143,148,149,152,154,159,162,174,185,201,205,210,220,223,224,225,231,234,235,239,243,245,246,249,251,257,258,259,280,281,326,330,332,341,346,368,432,433,435,439,459,460,466,477,483,488,490,503,545,550,552,553,554,581,582,583,585,596,597,605,607,624,625,631,634,635,639,645,647,657,660,662,671,673,674,675,676,694,701,705,708,715,721,724,725,729,730,739,741,747,750,753,754,758,759,766,767,774,777,783,784,786,794,799,801,803,805,810,815,819,825,830,832,834,835,836,837,842,843,844,847,848,855,859,861,876,878,891,892,911,919,920,922,924,939,945,948,949,957,963,966,967,969,974,976,981,983,1000,1001,1003,1011,1012,1013,1015,1018,1026,1028,1031,1032,1035,1036,1038,1040,1042,1044,1045,1048,1051,1054,1058,1059,1061,1074,1081,1083,1086,1087,1091,1092,1093,1095,1096,1101,1106,1107,1109,1110,1112,1114,1115,1117,1119,1126,1127,1132,1139,1141,1142,1143,1148,1150,1158,1159,1163,1165,1170,1174,1179,1182,1184,1185,1186,1187,1188,1190,1200,1206,1208,1219,1223,1225,1226,1230,1231,1233,1236,1238,1244,1253,1254,1255,1256,1263,1268,1277,1279,1287,1288,1289,1297,1298,1299,1327,1328,1329,1331,1334,1335,1336,1348,1350,1354,1355,1360,1362,1363,1366,1368,1380,1382,1383,1386,1398,1401,1403,1409,1411,1412,1417,1418,1419,1430,1433,1434,1436,1451,1453,1465,1466,1490,1492,1493,1504,1505,1509,1518,1519,1521,1529,1533,1534,1538,1540,1544,1551,1552,1553,1556,1558,1567,1570,1573,1576,1600,1620,1665,1676,1679,1688,1691,1700,1701,1706,1714,1715,1719,1728,1730,1738,1742,1743,1747,1748,1767,1769,1775,1776,1804,1808,1810,1824,1825,1854,1870,1876,1896,1897,1899,1904,1905,1906,1907,1908,1909,1910,1911,1912,1913,1914,1915,1916,1917,1918,1919,1920,1921,1922,1923,1924,1925,1926,1927,1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944,1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,1955,1956,1957,1958,1959,1960,1961,1962,1963,1964,1965,1966,1967,1968,1969,1970,1971,1972,1973,1974,1975,1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031,2032,2033,2034,2035,2036,2037,2038,2039,2040,2041,2042,2043,2044,2045,2046,2047,2048,2049]) S_22_ok
  have hm0 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_8_ok C_22_9_0
  have hm1 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_8_ok C_22_9_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def P_22_10 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [89,95,138,140,143,148,149,159,162,205,210,220,251,435,503,550,583,671,708,725,730,741,766,801,815,842,847,878,920,949,976,1018,1092,1110,1132,1140,1150,1226,1231,1254,1299,1329,1418,1567,1748,1769,1810,1896,1915,1920,1936,1941,1977,2002,2010,2050]
def N_22_10 : List NodeSpec := [([37,0,1,2,3,4,5],[89,138,140,143,148,149,159,205,210,503,583],[0,1]),([242,0,1,2,3,4,5],[89,138,143,149,159,210,251,708,1915,1936],[0,1]),([0,1,2,3,4,38,5],[89,138,140,143,210,1896,1915,1920],[0,1]),([0,1,2,3,4,5,190],[89,143,149,159,251,1140,1977],[0,1]),([111,0,1,2,3,4,5],[89,140,143,149,159,210,1915],[0,1]),([0,1,90,2,3,4,5],[89,140,143,148,159,210,435,1915,2050],[0,1]),([17,0,1,2,3,4,5],[89,138,140,143,149,159,210,1092,1231,1254],[0]),([0,1,18,2,3,4,5],[89,140,143,159,1110,1132,1567],[0,1]),([186,0,1,2,3,4,5],[89,95,138,140,143,149,159,210,1329,1418,1748],[0,1]),([41,0,1,2,3,4,5],[89,138,140,143,149,159,210,251,847],[0,1]),([24,0,1,2,3,4,5],[89,138,140,143,148,149,159,210,815,842,2002],[0,1]),([81,0,1,2,3,4,5],[89,140,143,149,159,210,1810,1915],[0,1]),([260,0,1,2,3,4,5],[89,138,140,143,149,159,210,251,920,949,1915],[0,1]),([23,0,1,2,3,4,5],[89,140,143,149,159,210,1226,1915],[0,1]),([0,1,2,3,4,5,79],[89,138,143,149,220,251,1299,1915],[0,1]),([168,0,1,2,3,4,5],[89,140,143,149,159,210,251,766,1941],[0,1]),([0,1,2,3,4,25,5],[89,143,159,251,801,2010],[0,1]),([142,0,1,2,3,4,5],[89,138,140,143,149,159,210,878,1150],[0,1]),([224,0,1,2,3,4,5],[89,143,149,159,210,251,1769],[0,1]),([0,1,2,3,152,4,5],[89,138,143,162,220,251,976,1018,1915],[0,1]),([69,0,1,2,3,4,5],[89,138,140,143,148,149,159,205,210,725,730,741],[0,1]),([0,1,2,3,4,5,14],[89,140,143,149,159,550,671],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_10 : checkNodesBT W_22 g_22 F_22 P_22_10 A_22 B_22_9 10 N_22_10 = true := by decide +kernel
def B_22_10 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_10
set_option maxRecDepth 500000 in
lemma B_22_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 10 xs.toFinset) B_22_10 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_9_ok C_22_10
def P_22_11 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [138,149,210]
def N_22_11 : List NodeSpec := [([0,1,2,3,4,5],[138,149,210],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_11 : checkNodesBT W_22 g_22 F_22 P_22_11 A_22 B_22_10 11 N_22_11 = true := by decide +kernel
def B_22_11 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_11
set_option maxRecDepth 500000 in
lemma B_22_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 11 xs.toFinset) B_22_11 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_10_ok C_22_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck r_22 g_22 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT B_22_11 r_22 = true := by decide +kernel
lemma low_22 : Lower r_22 g_22 12 := lower_of_forestBT root_22_ok B_22_11_ok root_22_in

def g_orig := 0xfeeeeee8fae0e0c0feeeeee8fae0e0c0feeeeee8fae0e0c0feeeeee8fae0e0c0
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,4),(1,3),(2,5),(3,4)]) (by decide +kernel) low_22
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071592 * 2 ^ 32 + 4209041600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.or,[4,3]⟩,⟨.or,[2,0]⟩,⟨.and,[4,3]⟩,⟨.or,[1,0]⟩,⟨.or,[5,2]⟩,⟨.and,[8,7]⟩,⟨.and,[2,5]⟩,⟨.and,[7,1]⟩,⟨.or,[12,13]⟩,⟨.and,[9,10]⟩,⟨.or,[11,15]⟩,⟨.or,[6,14]⟩,⟨.and,[16,17]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_44758

open PEqualNP.Outside.L_meta_44758 in
theorem PEqualNP.Outside.L_meta_44758 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4209041600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4209041600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
