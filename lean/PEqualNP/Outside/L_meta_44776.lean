import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_44776
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
def g_4 := 0xfc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80
def r_4 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_4 : Lower r_4 g_4 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_5 := 0xffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8
def r_5 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_5 : Lower r_5 g_5 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_6 := 0xfec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0
def r_6 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_6 : Lower r_6 g_6 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_7 := 0xfffce880fffce880fffce880fffce880fffce880fffce880fffce880fffce880
def r_7 : List Nat := varsOf 31
def p_7 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,18,18,19,19,20,20,21,21,22,24,24,25,25,26,28]
def q_7 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,16,2,17,3,16,4,17,5,6,16,8,17,9,10,12]
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
lemma sl_7_0 : Slice r_7 g_7 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_1 : Slice r_7 g_7 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_7_2 : Slice r_7 g_7 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_3 : Slice r_7 g_7 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfff0a000fff0a000fff0a000fff0a000fff0a000fff0a000fff0a000fff0a000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_4 : Slice r_7 g_7 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_5 : Slice r_7 g_7 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_6 : Slice r_7 g_7 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffffee88ffffee88ffffee88ffffee88ffffee88ffffee88ffffee88ffffee88 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_7 : Slice r_7 g_7 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xfcfc8080fcfc8080fcfc8080fcfc8080fcfc8080fcfc8080fcfc8080fcfc8080 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_8 : Slice r_7 g_7 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_9 : Slice r_7 g_7 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) 0xffcccc88ffcccc88ffcccc88ffcccc88ffcccc88ffcccc88ffcccc88ffcccc88 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_10 : Slice r_7 g_7 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xfcfcc8c8fcfcc8c8fcfcc8c8fcfcc8c8fcfcc8c8fcfcc8c8fcfcc8c8fcfcc8c8 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
def S_7 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,7),some (subcubeFast 16 0,7),some (subcubeFast 1 0,6),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (identDom 1 2,5),some (identDom 1 3,5)]
lemma S_7_ok : btAll (fun o => ∀ p, o = some p → Slice r_7 g_7 p.1 p.2) S_7 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_7_0) (forall_cons (fun _ h => by cases h; exact sl_7_1) (forall_cons (fun _ h => by cases h; exact sl_7_2) (forall_cons (fun _ h => by cases h; exact sl_7_3) (forall_cons (fun _ h => by cases h; exact sl_7_4) (forall_cons (fun _ h => by cases h; exact sl_7_5) (forall_cons (fun _ h => by cases h; exact sl_7_6) (forall_cons (fun _ h => by cases h; exact sl_7_7) (forall_cons (fun _ h => by cases h; exact sl_7_8) (forall_cons (fun _ h => by cases h; exact sl_7_9) (forall_cons (fun _ h => by cases h; exact sl_7_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_7 : BT (Option PoolSpec) := btOfList 5 ((([(0,[(0,1,2),(1,1,2)]),(4,[]),(1,[(0,1,2),(1,1,2)]),(9,[]),(3,[]),(0,[(2,1,3)]),(6,[]),(5,[]),(1,[(2,1,3)]),(10,[]),(7,[]),(8,[]),(0,[(1,1,2)]),(2,[]),(1,[(1,1,2)]),(0,[(0,1,2)]),(1,[(0,1,2)]),(0,[]),(1,[])] : List PoolSpec)).map some)
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
def P_7_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_7 r_7 S_7 ps_7 [1,4,5,6,7,8,9,10,11,12,13,14,15,16]
def N_7_7 : List NodeSpec := [([7,0,1,2,3,4],[1,4,5,6,7,8,9,10,11],[]),([0,1,2,6,3,4],[1,4,6,7,10,11,12,13,14],[0]),([0,5,1,2,3,4],[1,4,7,10,11,15,16],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_7 : checkNodesBT W_7 g_7 F_7 P_7_7 A_7 B_7_6 7 N_7_7 = true := by decide +kernel
def B_7_7 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_7
set_option maxRecDepth 500000 in
lemma B_7_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 7 xs.toFinset) B_7_7 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_6_ok C_7_7
def P_7_8 : BT (Option BoundPool) := buildPoolsSubBT 5 W_7 r_7 S_7 ps_7 [17,18]
def N_7_8 : List NodeSpec := [([0,1,2,3,4],[17,18],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_8 : checkNodesBT W_7 g_7 F_7 P_7_8 A_7 B_7_7 8 N_7_8 = true := by decide +kernel
def B_7_8 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_8
set_option maxRecDepth 500000 in
lemma B_7_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 8 xs.toFinset) B_7_8 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_7_ok C_7_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_ok : forestRootCheck r_7 g_7 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_in : bucketContainsBT B_7_8 r_7 = true := by decide +kernel
lemma low_7 : Lower r_7 g_7 9 := lower_of_forestBT root_7_ok B_7_8_ok root_7_in
def g_8 := 0xe800e800e800e800e800e800e800e800e800e800e800e800e800e800e800e800
def r_8 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_9 := 0xfee8c000fee8c000fee8c000fee8c000fee8c000fee8c000fee8c000fee8c000
def r_9 : List Nat := varsOf 31
def p_9 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,22,22,22,23,25,25,25,26,26,26,27,28,28,28,29]
def q_9 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,20,18,6,7,24,17,9,24,18,10,11,24,20,12,13]
def F_9 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_9 : goodPairs g_9 p_9 q_9 := goodPairs_of (by decide +kernel)
def W_9 : BT Decor := buildWiresBT 3 (mkBase p_9 q_9 r_9) [(0,1,2),(1,1,2),(2,1,3)]
lemma W_9_ok : btAll (fun x => faithful p_9 q_9 x ∧ x.1 < 2^256) W_9 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_9 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)]]
def A_9 : BT (List (Nat × Nat)) := btOfList 3 al_9
set_option maxHeartbeats 0 in
lemma A_9_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_9 = g_9) A_9 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_9_0 : Slice r_9 g_9 (subcubeFast 0 16) 7 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_9_1 : Slice r_9 g_9 (subcubeFast 1 0) 7 := by
  have hc : Lower (varsOf 30) 0xfcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_2 : Slice r_9 g_9 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_3 : Slice r_9 g_9 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfaa00000faa00000faa00000faa00000faa00000faa00000faa00000faa00000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_4 : Slice r_9 g_9 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_5 : Slice r_9 g_9 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xee880000ee880000ee880000ee880000ee880000ee880000ee880000ee880000 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_6 : Slice r_9 g_9 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffeecc00ffeecc00ffeecc00ffeecc00ffeecc00ffeecc00ffeecc00ffeecc00 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_7 : Slice r_9 g_9 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xe8e80000e8e80000e8e80000e8e80000e8e80000e8e80000e8e80000e8e80000 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_8 : Slice r_9 g_9 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xfefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_9 : Slice r_9 g_9 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) 0xeecccc00eecccc00eecccc00eecccc00eecccc00eecccc00eecccc00eecccc00 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_4
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_10 : Slice r_9 g_9 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0ececc0c0 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_4
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
def S_9 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 16,7),some (subcubeFast 1 0,7),some (subcubeFast 0 1,6),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (identDom 1 2,5),some (identDom 1 3,5)]
lemma S_9_ok : btAll (fun o => ∀ p, o = some p → Slice r_9 g_9 p.1 p.2) S_9 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_9_0) (forall_cons (fun _ h => by cases h; exact sl_9_1) (forall_cons (fun _ h => by cases h; exact sl_9_2) (forall_cons (fun _ h => by cases h; exact sl_9_3) (forall_cons (fun _ h => by cases h; exact sl_9_4) (forall_cons (fun _ h => by cases h; exact sl_9_5) (forall_cons (fun _ h => by cases h; exact sl_9_6) (forall_cons (fun _ h => by cases h; exact sl_9_7) (forall_cons (fun _ h => by cases h; exact sl_9_8) (forall_cons (fun _ h => by cases h; exact sl_9_9) (forall_cons (fun _ h => by cases h; exact sl_9_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_9 : BT (Option PoolSpec) := btOfList 5 ((([(1,[(0,1,2),(1,1,2)]),(3,[]),(0,[(0,1,2),(1,1,2)]),(9,[]),(4,[]),(1,[]),(1,[(2,1,3)]),(6,[]),(5,[]),(0,[]),(0,[(2,1,3)]),(10,[]),(7,[]),(8,[]),(1,[(1,1,2)]),(0,[(1,1,2)]),(1,[(0,1,2)]),(2,[]),(0,[(0,1,2)])] : List PoolSpec)).map some)
def B_9_5 : BT (List (List Nat)) := BT.empty
lemma B_9_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 5 xs.toFinset) B_9_5 := .empty
def P_9_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_9 r_9 S_9 ps_9 [0,1,2,3,4]
def N_9_6 : List NodeSpec := [([0,5,6,3,4],[0,1,2,3,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_6 : checkNodesBT W_9 g_9 F_9 P_9_6 A_9 B_9_5 6 N_9_6 = true := by decide +kernel
def B_9_6 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_6
set_option maxRecDepth 500000 in
lemma B_9_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 6 xs.toFinset) B_9_6 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_5_ok C_9_6
def P_9_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_9 r_9 S_9 ps_9 [1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]
def N_9_7 : List NodeSpec := [([7,0,1,2,3,4],[1,4,5,6,7,8,9,10,11,12,13],[]),([0,1,2,6,3,4],[1,4,7,8,12,13,14,15],[0]),([0,5,1,2,3,4],[1,4,5,8,12,13,16,17,18],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_7 : checkNodesBT W_9 g_9 F_9 P_9_7 A_9 B_9_6 7 N_9_7 = true := by decide +kernel
def B_9_7 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_7
set_option maxRecDepth 500000 in
lemma B_9_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 7 xs.toFinset) B_9_7 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_6_ok C_9_7
def P_9_8 : BT (Option BoundPool) := buildPoolsSubBT 5 W_9 r_9 S_9 ps_9 [5,9]
def N_9_8 : List NodeSpec := [([0,1,2,3,4],[5,9],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_8 : checkNodesBT W_9 g_9 F_9 P_9_8 A_9 B_9_7 8 N_9_8 = true := by decide +kernel
def B_9_8 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_8
set_option maxRecDepth 500000 in
lemma B_9_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 8 xs.toFinset) B_9_8 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_7_ok C_9_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_ok : forestRootCheck r_9 g_9 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_in : bucketContainsBT B_9_8 r_9 = true := by decide +kernel
lemma low_9 : Lower r_9 g_9 9 := lower_of_forestBT root_9_ok B_9_8_ok root_9_in
def g_10 := 0xfee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0
def r_10 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_10 : Lower r_10 g_10 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_11 := 0xfffefe80fffefe80fffefe80fffefe80fffefe80fffefe80fffefe80fffefe80
def r_11 : List Nat := varsOf 31
def p_11 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14,17,17,18,18,19,20,20,21,22,24,24]
def q_11 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6,16,1,16,2,3,16,4,5,6,16,8]
def F_11 : Nat := fullMask 23
set_option maxHeartbeats 0 in
lemma gp_11 : goodPairs g_11 p_11 q_11 := goodPairs_of (by decide +kernel)
def W_11 : BT Decor := buildWiresBT 7 (mkBase p_11 q_11 r_11) [(1,2,1),(1,1,3),(1,2,4),(0,6,7),(1,3,4),(3,2,9),(0,2,0),(1,10,11),(1,2,0),(1,13,3),(1,14,4),(3,2,15),(1,0,3),(1,17,4),(3,1,18),(0,2,9),(1,2,3),(1,21,4),(3,20,22),(0,0,1),(1,24,3),(1,25,4),(3,2,26),(1,1,13),(1,28,3),(2,29,4),(3,2,17),(1,0,4),(0,1,18),(1,13,4),(2,17,4),(3,3,32),(1,1,4),(0,17,37),(0,0,22),(1,0,1),(1,40,3),(1,41,4),(3,2,42),(3,1,9),(1,44,0),(2,45,2),(3,0,9),(2,6,4),(1,48,0),(1,6,4),(0,0,50),(2,0,9),(2,31,4),(1,10,0),(3,2,32),(1,55,3),(3,20,0),(3,2,6),(1,58,0),(3,5,9),(1,24,4),(2,28,4),(2,25,4),(0,1,2),(3,64,9),(2,2,3),(3,66,7),(0,0,9),(3,2,41),(1,40,4),(1,52,4),(2,41,4),(3,5,17),(2,0,4),(1,74,3)]
lemma W_11_ok : btAll (fun x => faithful p_11 q_11 x ∧ x.1 < 2^256) W_11 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_11 : List (List (Nat × Nat)) := [[],[(3,4)],[(1,2)],[(1,2),(3,4)],[(0,1)],[(0,1),(3,4)],[(0,2),(1,2)],[(0,2),(1,2),(3,4)],[(0,1),(1,2)],[(0,1),(1,2),(3,4)],[(0,2)],[(0,2),(3,4)]]
def A_11 : BT (List (Nat × Nat)) := btOfList 4 al_11
set_option maxHeartbeats 0 in
lemma A_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_11 = g_11) A_11 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_11_0 : Slice r_11 g_11 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) 0xfffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_1 : Slice r_11 g_11 (identDom 0 2) 7 := by
  have hc : Lower (varsOf 27) 0xffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_2 : Slice r_11 g_11 (identDom 1 2) 7 := by
  have hc : Lower (varsOf 27) 0xffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_3 : Slice r_11 g_11 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) 0xfefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_4 : Slice r_11 g_11 (subcubeFast 16 0) 6 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_11_5 : Slice r_11 g_11 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_6 : Slice r_11 g_11 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffafa00fffafa00fffafa00fffafa00fffafa00fffafa00fffafa00fffafa00 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_7 : Slice r_11 g_11 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffeeee00ffeeee00ffeeee00ffeeee00ffeeee00ffeeee00ffeeee00ffeeee00 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_8 : Slice r_11 g_11 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_9 : Slice r_11 g_11 (subcubeFast 5 0) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_10 : Slice r_11 g_11 (subcubeFast 6 0) 4 := by
  have hc : Lower (varsOf 25) 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 0) (by decide +kernel) hc
def S_11 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,7),some (identDom 0 2,7),some (identDom 1 2,7),some (subcubeFast 8 0,6),some (subcubeFast 16 0,6),some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 3 0,4),some (subcubeFast 5 0,4),some (subcubeFast 6 0,4)]
lemma S_11_ok : btAll (fun o => ∀ p, o = some p → Slice r_11 g_11 p.1 p.2) S_11 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_11_0) (forall_cons (fun _ h => by cases h; exact sl_11_1) (forall_cons (fun _ h => by cases h; exact sl_11_2) (forall_cons (fun _ h => by cases h; exact sl_11_3) (forall_cons (fun _ h => by cases h; exact sl_11_4) (forall_cons (fun _ h => by cases h; exact sl_11_5) (forall_cons (fun _ h => by cases h; exact sl_11_6) (forall_cons (fun _ h => by cases h; exact sl_11_7) (forall_cons (fun _ h => by cases h; exact sl_11_8) (forall_cons (fun _ h => by cases h; exact sl_11_9) (forall_cons (fun _ h => by cases h; exact sl_11_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_11 : BT (Option PoolSpec) := btOfList 7 ((([(3,[(0,2,9),(1,2,9),(3,20,22)]),(3,[]),(4,[]),(10,[]),(0,[]),(1,[]),(3,[(1,0,9),(3,2,18)]),(3,[(1,17,4),(3,2,18)]),(9,[]),(7,[]),(3,[(2,0,9),(3,0,9)]),(1,[(1,3,4),(3,2,9),(1,10,0)]),(3,[(1,0,4),(3,2,32)]),(3,[(1,2,4)]),(4,[(1,2,3)]),(3,[(0,2,9),(3,20,0)]),(1,[(1,3,4),(3,2,9)]),(2,[(1,3,4),(3,5,9)]),(0,[(1,24,4),(1,4,3)]),(5,[]),(6,[]),(0,[(1,2,0),(1,2,3)]),(1,[(1,1,13)]),(2,[(1,2,0)]),(0,[(1,24,3),(2,25,4)]),(0,[(1,24,3),(1,25,4)]),(0,[(1,0,4),(1,4,3)]),(1,[(1,0,4),(1,4,3)]),(1,[(1,13,3),(3,2,14)]),(4,[(1,0,3),(3,2,17)]),(2,[]),(0,[(1,3,4),(1,0,9)]),(1,[(1,3,4),(1,0,9)]),(0,[(1,3,4),(0,0,9)]),(1,[(1,3,4),(0,0,9)]),(3,[(0,0,9),(1,0,9)]),(1,[(1,2,3),(3,2,14)]),(3,[(3,2,9)]),(0,[(1,3,4)]),(1,[(1,3,4)]),(3,[(0,0,9)]),(3,[(2,17,4)]),(4,[(1,0,3)]),(0,[(1,0,3),(2,17,4)]),(1,[(1,0,3),(2,17,4)]),(3,[(1,17,4)]),(0,[(1,0,3)]),(1,[(1,0,3)]),(3,[(1,1,4)]),(0,[(1,1,4)]),(8,[]),(3,[(1,0,1)]),(3,[(1,0,4)]),(3,[(0,0,1)]),(0,[(1,24,3)]),(1,[(1,2,3)]),(3,[(1,2,0)]),(0,[(1,40,2)]),(1,[(1,0,1)]),(0,[(1,2,3)]),(1,[(1,0,1),(1,2,3)]),(2,[(1,0,1),(1,2,3)]),(2,[(1,0,1)]),(3,[(2,0,4)]),(4,[(1,74,3)]),(3,[(3,2,17)]),(3,[(1,0,9)]),(1,[(1,0,3),(3,2,17)]),(2,[(1,3,4),(3,2,9)]),(4,[(3,2,9)]),(3,[(2,0,9)]),(0,[(1,0,3),(1,17,4)]),(1,[(1,0,3),(1,17,4)]),(3,[(1,1,17)]),(4,[(1,0,1)]),(2,[(1,3,4)]),(4,[(0,0,1)])] : List PoolSpec)).map some)
def B_11_2 : BT (List (List Nat)) := BT.empty
lemma B_11_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 2 xs.toFinset) B_11_2 := .empty
def P_11_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_11 r_11 S_11 ps_11 []
def N_11_3 : List NodeSpec := [([0,5,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_3 : checkNodesBT W_11 g_11 F_11 P_11_3 A_11 B_11_2 3 N_11_3 = true := by decide +kernel
def B_11_3 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_3
set_option maxRecDepth 500000 in
lemma B_11_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 3 xs.toFinset) B_11_3 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_2_ok C_11_3
def P_11_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_11 r_11 S_11 ps_11 [0,1,2,3]
def N_11_4 : List NodeSpec := [([0,12,1,3,4],[],[]),([16,19,0,3,4],[],[]),([0,5,3,8,4],[],[0]),([23,0,1,3,4],[0],[]),([27,0,1,3,4],[],[]),([30,0,1,2,3],[],[]),([31,1,2,32,9],[],[]),([16,0,33,3,4],[],[]),([0,1,21,34,9],[1],[]),([35,36,0,1,2],[],[]),([0,1,2,38,9],[1,2],[8]),([10,39,1,3,4],[],[]),([16,0,1,3,4],[],[]),([0,5,6,7,9],[3],[0]),([43,0,1,3,4],[],[]),([46,0,1,3,4],[],[]),([35,47,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_4 : checkNodesBT W_11 g_11 F_11 P_11_4 A_11 B_11_3 4 N_11_4 = true := by decide +kernel
def B_11_4 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_4
set_option maxRecDepth 500000 in
lemma B_11_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 4 xs.toFinset) B_11_4 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_3_ok C_11_4
def P_11_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_11 r_11 S_11 ps_11 [1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
def N_11_5 : List NodeSpec := [([0,1,2,3,4,18],[4,5],[0,2]),([35,0,1,2,3,9],[1],[0]),([16,0,1,3,4,9],[6],[]),([0,49,1,2,3,4],[],[]),([16,0,1,3,17,4],[7],[]),([10,0,1,3,21,4],[1],[8]),([16,0,1,2,3,4],[],[]),([16,0,1,3,4],[],[]),([51,1,2,3,4,50],[8],[2,4,6]),([10,0,1,3,4,22],[4],[0,4,8,9]),([35,0,1,2,17,9],[1,2],[]),([10,0,1,3,7,9],[2,9],[]),([0,1,2,3,38,4],[1,2],[0,8]),([52,47,1,2,3,4],[10],[6]),([53,0,1,2,3,4],[],[]),([0,54,1,2,3,4],[4,11],[0,2]),([0,1,2,3,56,4],[12],[]),([0,5,3,6,4,7],[],[0]),([0,1,2,3,29,4],[2],[0]),([0,1,21,7,9],[1,2,9,13,14],[0,1,4,5,8,9,10,11]),([57,1,2,3,4,9],[15],[]),([31,1,13,3,17,4],[5],[]),([10,0,1,2,3,4],[],[]),([10,11,0,1,3,4],[16],[0]),([0,59,1,2,3,4],[4],[]),([60,0,1,2,3,4],[17],[]),([0,1,3,21,4,34],[1],[0]),([0,1,2,3,61,9],[1,18,19,20],[]),([0,1,28,3,21,4],[1,21,22,23],[]),([62,0,1,2,3,4],[],[]),([0,1,13,3,7,9],[8],[1,4]),([63,0,1,2,3,4],[24],[]),([0,1,2,17,37,9],[],[0,3,6,8]),([65,0,1,2,3,4],[],[]),([35,1,2,3,17,32],[2,19],[]),([0,1,13,3,4,22],[5,23],[]),([0,1,3,67,4,7],[2,9],[]),([0,1,2,3,4,26],[9,25],[0]),([68,1,2,3,32,9],[2,26,27],[]),([31,0,1,3,14,4],[4,8,28],[]),([69,0,1,2,3,4],[],[]),([31,0,1,2,4,9],[2,29],[0]),([0,1,2,3,70,9],[1],[2,6]),([0,1,2,3,71,9],[1,19],[]),([16,0,1,3,4,18],[5],[0]),([0,1,2,3,4,42],[5],[0,2,6]),([35,1,40,2,3,4],[20],[]),([72,0,1,2,3,4],[],[]),([31,0,1,5,3,4],[30],[]),([35,0,1,2,3,32],[2],[0]),([35,0,1,2,3,18],[4],[0]),([73,0,1,2,3,4],[],[]),([31,1,2,3,4,32],[],[0]),([68,1,2,3,4,18],[31,32,33,34,35],[6]),([0,1,2,17,32,9],[1,19],[]),([31,0,1,3,21,4],[1,36],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_5 : checkNodesBT W_11 g_11 F_11 P_11_5 A_11 B_11_4 5 N_11_5 = true := by decide +kernel
def B_11_5 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_5
set_option maxRecDepth 500000 in
lemma B_11_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 5 xs.toFinset) B_11_5 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_4_ok C_11_5
def P_11_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_11 r_11 S_11 ps_11 [1,2,3,4,5,8,9,13,14,16,19,20,21,23,26,27,29,30,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73]
def N_11_6 : List NodeSpec := [([10,0,1,2,3,4,9],[1,2,9,37],[0,1,8]),([68,0,1,2,3,4,9],[1,2,19,38,39,40],[0,1,6,10]),([35,0,1,2,3,4],[2,9,20,41,42,43,44],[0,2,4,8]),([0,1,2,3,17,4,18],[42,45,46,47],[0,1,2,6]),([0,1,2,3,17,4,37],[42,46,48,49],[0,2,3,6,7,8]),([0,1,2,3,41,4],[2,5,50,51],[0,1,2,3,6,7]),([0,1,2,3,32,9],[2,19,26,27,52],[0,1,2,3,6,10]),([24,0,1,2,3,4,9],[1,2,19,20,38,53],[0,1,2,6,8]),([0,1,2,3,17,4,32],[2,19,52],[0,1]),([0,1,2,3,25,4],[2,8,20,53,54],[0,1]),([0,1,13,3,21,4],[1,8,21,23,55,56],[0,1,5,8,10]),([0,1,2,28,3,4],[1,2,3,8,50,57,58],[0,1,2,3,6,7]),([0,1,40,2,3,21,4],[50,51,58,59,60,61,62],[0,8,10]),([74,1,2,3,17,4],[1,8,19,42,46,47,50,63],[7]),([0,1,2,3,75,4],[8,50,64],[]),([31,0,1,2,3,4],[1,2,5,8,29,30,65],[0,1,4]),([0,1,2,3,4,9,18],[19,38,39,66],[0,1,2,6]),([31,0,1,2,3,17,4],[1,47,65,67],[0]),([35,0,1,2,3,17,4],[2,19,41,42],[0]),([0,1,40,2,3,4,9],[1,2,19,20,38,50,51],[0,1,2,3,6,7,8]),([0,1,3,21,4,7],[9,13,14],[0,1,4,5,8,9,10,11]),([10,0,1,2,3,4],[1,2,5,16,30,37,68,69],[0,4,8]),([52,0,1,2,3,4,9],[19,70],[0,1]),([0,1,2,3,4,18],[4,5,42,45,71,72],[0,1,2,4,6,8,10]),([0,1,2,3,17,41,4],[46,50,73],[2,6])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_6 : checkNodesBT W_11 g_11 F_11 P_11_6 A_11 B_11_5 6 N_11_6 = true := by decide +kernel
def B_11_6 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_6
set_option maxRecDepth 500000 in
lemma B_11_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 6 xs.toFinset) B_11_6 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_5_ok C_11_6
def P_11_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_11 r_11 S_11 ps_11 [1,2,4,5,8,9,19,20,38,39,42,46,47,50,51,53,58,62,74,75,76]
def N_11_7 : List NodeSpec := [([74,0,1,2,3,4],[1,2,4,5,8,9,19,20,50],[0]),([0,1,2,3,17,4],[1,8,19,42,46,47,50],[0,1,2,6,10]),([0,1,40,2,3,4],[1,2,4,8,50,51,58,62,74],[0,1,2,3,6,7]),([0,1,2,3,4,9],[1,2,9,19,20,38,39,75],[0,1,2,4,5,6,8,9]),([24,0,1,2,3,4],[1,2,4,5,8,9,19,20,53,76],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_7 : checkNodesBT W_11 g_11 F_11 P_11_7 A_11 B_11_6 7 N_11_7 = true := by decide +kernel
def B_11_7 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_7
set_option maxRecDepth 500000 in
lemma B_11_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 7 xs.toFinset) B_11_7 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_6_ok C_11_7
def P_11_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_11 r_11 S_11 ps_11 [1,2,4,5,30]
def N_11_8 : List NodeSpec := [([0,1,2,3,4],[1,2,4,5,30],[0,1,2,4,5,6,8,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_8 : checkNodesBT W_11 g_11 F_11 P_11_8 A_11 B_11_7 8 N_11_8 = true := by decide +kernel
def B_11_8 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_8
set_option maxRecDepth 500000 in
lemma B_11_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 8 xs.toFinset) B_11_8 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_7_ok C_11_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck r_11 g_11 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT B_11_8 r_11 = true := by decide +kernel
lemma low_11 : Lower r_11 g_11 9 := lower_of_forestBT root_11_ok B_11_8_ok root_11_in
def g_12 := 0xfffefec0fffefec0fffefec0fffefec0fffefec0fffefec0fffefec0fffefec0
def r_12 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_12 : Lower r_12 g_12 8 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_13 := 0xfffffee8fffffee8fffffee8fffffee8fffffee8fffffee8fffffee8fffffee8
def r_13 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_13 : Lower r_13 g_13 8 := by
  exact lift_of_f (z := 16) (o := 0) (other := r_1) (G := g_1) (essPairs := [(VAR 4,0,16)]) (by decide +kernel) low_1
def g_14 := 0xf880f880f880f880f880f880f880f880f880f880f880f880f880f880f880f880
def r_14 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_15 := 0xfff8e800fff8e800fff8e800fff8e800fff8e800fff8e800fff8e800fff8e800
def r_15 : List Nat := varsOf 31
def p_15 : List Nat := [11,11,11,13,13,13,14,14,14,15,19,19,19,20,20,21,21,22,22,23,24,24,25,25,26,26,28]
def q_15 : List Nat := [10,9,3,12,9,5,12,10,6,7,18,17,3,16,4,17,5,18,6,7,16,8,17,9,18,10,12]
def F_15 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_15 : goodPairs g_15 p_15 q_15 := goodPairs_of (by decide +kernel)
def W_15 : BT Decor := buildWiresBT 3 (mkBase p_15 q_15 r_15) [(1,2,4)]
lemma W_15_ok : btAll (fun x => faithful p_15 q_15 x ∧ x.1 < 2^256) W_15 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_15 : List (List (Nat × Nat)) := [[]]
def A_15 : BT (List (Nat × Nat)) := btOfList 1 al_15
set_option maxHeartbeats 0 in
lemma A_15_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_15 = g_15) A_15 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_15_0 : Slice r_15 g_15 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_1 : Slice r_15 g_15 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfff0a000fff0a000fff0a000fff0a000fff0a000fff0a000fff0a000fff0a000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_2 : Slice r_15 g_15 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffafa00fffafa00fffafa00fffafa00fffafa00fffafa00fffafa00fffafa00 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_3 : Slice r_15 g_15 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xff888800ff888800ff888800ff888800ff888800ff888800ff888800ff888800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_4 : Slice r_15 g_15 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfff0c000fff0c000fff0c000fff0c000fff0c000fff0c000fff0c000fff0c000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_5 : Slice r_15 g_15 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_6 : Slice r_15 g_15 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_8
set_option maxHeartbeats 0 in
lemma sl_15_7 : Slice r_15 g_15 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_15_8 : Slice r_15 g_15 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) 0xf8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_15 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 1 0,5),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (identDom 2 3,6)]
lemma S_15_ok : btAll (fun o => ∀ p, o = some p → Slice r_15 g_15 p.1 p.2) S_15 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_15_0) (forall_cons (fun _ h => by cases h; exact sl_15_1) (forall_cons (fun _ h => by cases h; exact sl_15_2) (forall_cons (fun _ h => by cases h; exact sl_15_3) (forall_cons (fun _ h => by cases h; exact sl_15_4) (forall_cons (fun _ h => by cases h; exact sl_15_5) (forall_cons (fun _ h => by cases h; exact sl_15_6) (forall_cons (fun _ h => by cases h; exact sl_15_7) (forall_cons (fun _ h => by cases h; exact sl_15_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_15 : BT (Option PoolSpec) := btOfList 4 ((([(4,[]),(0,[]),(1,[]),(2,[]),(5,[(1,2,4)]),(3,[]),(6,[]),(7,[]),(5,[]),(8,[])] : List PoolSpec)).map some)
def B_15_5 : BT (List (List Nat)) := BT.empty
lemma B_15_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 5 xs.toFinset) B_15_5 := .empty
def P_15_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_15 r_15 S_15 ps_15 [0,1,2,3,4,5,6,7]
def N_15_6 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_6 : checkNodesBT W_15 g_15 F_15 P_15_6 A_15 B_15_5 6 N_15_6 = true := by decide +kernel
def B_15_6 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_6
set_option maxRecDepth 500000 in
lemma B_15_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 6 xs.toFinset) B_15_6 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_5_ok C_15_6
def P_15_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_15 r_15 S_15 ps_15 [0,1,2,3,5,6,7,8,9]
def N_15_7 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,5,6,7,8,9],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_7 : checkNodesBT W_15 g_15 F_15 P_15_7 A_15 B_15_6 7 N_15_7 = true := by decide +kernel
def B_15_7 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_7
set_option maxRecDepth 500000 in
lemma B_15_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 7 xs.toFinset) B_15_7 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_6_ok C_15_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_15_ok : forestRootCheck r_15 g_15 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_15_in : bucketContainsBT B_15_7 r_15 = true := by decide +kernel
lemma low_15 : Lower r_15 g_15 8 := lower_of_forestBT root_15_ok B_15_7_ok root_15_in
def g_16 := 0xfffce800fffce800fffce800fffce800fffce800fffce800fffce800fffce800
def r_16 : List Nat := varsOf 31
def p_16 : List Nat := [11,11,11,13,13,13,14,14,14,15,18,18,19,19,20,20,21,21,22,23,24,24,25,25,26,28]
def q_16 : List Nat := [10,9,3,12,9,5,12,10,6,7,16,2,17,3,16,4,17,5,6,7,16,8,17,9,10,12]
def F_16 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_16 : goodPairs g_16 p_16 q_16 := goodPairs_of (by decide +kernel)
def W_16 : BT Decor := buildWiresBT 4 (mkBase p_16 q_16 r_16) [(1,1,4),(3,2,5),(1,1,2),(2,7,4),(3,2,3),(1,9,1),(1,7,4),(0,7,3),(1,2,4),(1,0,4),(3,0,3)]
lemma W_16_ok : btAll (fun x => faithful p_16 q_16 x ∧ x.1 < 2^256) W_16 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_16 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_16 : BT (List (Nat × Nat)) := btOfList 1 al_16
set_option maxHeartbeats 0 in
lemma A_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_16 = g_16) A_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_16_0 : Slice r_16 g_16 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_1 : Slice r_16 g_16 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_2 : Slice r_16 g_16 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfff0a000fff0a000fff0a000fff0a000fff0a000fff0a000fff0a000fff0a000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_3 : Slice r_16 g_16 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_4 : Slice r_16 g_16 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_5 : Slice r_16 g_16 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_8
set_option maxHeartbeats 0 in
lemma sl_16_6 : Slice r_16 g_16 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_16_7 : Slice r_16 g_16 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_8 : Slice r_16 g_16 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) 0xfcfce0e0fcfce0e0fcfce0e0fcfce0e0fcfce0e0fcfce0e0fcfce0e0fcfce0e0 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_16 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 1 0,6),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (subcubeFast 4 1,4),some (identDom 2 3,5)]
lemma S_16_ok : btAll (fun o => ∀ p, o = some p → Slice r_16 g_16 p.1 p.2) S_16 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_16_0) (forall_cons (fun _ h => by cases h; exact sl_16_1) (forall_cons (fun _ h => by cases h; exact sl_16_2) (forall_cons (fun _ h => by cases h; exact sl_16_3) (forall_cons (fun _ h => by cases h; exact sl_16_4) (forall_cons (fun _ h => by cases h; exact sl_16_5) (forall_cons (fun _ h => by cases h; exact sl_16_6) (forall_cons (fun _ h => by cases h; exact sl_16_7) (forall_cons (fun _ h => by cases h; exact sl_16_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_16 : BT (Option PoolSpec) := btOfList 4 ((([(0,[]),(1,[]),(8,[]),(4,[]),(2,[]),(5,[]),(0,[(3,2,3)]),(3,[]),(6,[]),(0,[(1,1,4)]),(0,[(1,1,2)]),(7,[]),(2,[(1,0,4)]),(4,[(1,0,4)]),(2,[(3,0,3)])] : List PoolSpec)).map some)
def B_16_4 : BT (List (List Nat)) := BT.empty
lemma B_16_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 4 xs.toFinset) B_16_4 := .empty
def P_16_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 [0,1,2,3,4,5]
def N_16_5 : List NodeSpec := [([6,0,1,2,3,4],[],[]),([8,0,1,2,3,4],[0,1],[]),([0,1,10,2,3,4],[],[]),([0,1,2,3,4,11],[0,1,2,3],[]),([0,1,2,12,3,4],[0,1],[]),([0,1,7,3,4,13],[4,5],[]),([9,0,1,7,3,4],[3,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_5 : checkNodesBT W_16 g_16 F_16 P_16_5 A_16 B_16_4 5 N_16_5 = true := by decide +kernel
def B_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_5
set_option maxRecDepth 500000 in
lemma B_16_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 5 xs.toFinset) B_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_4_ok C_16_5
def P_16_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14]
def N_16_6 : List NodeSpec := [([9,0,1,2,3,4],[0,2,4,6,7,8],[0]),([0,1,2,3,4,5],[4,7,8,9],[0,1]),([0,1,2,7,3,4],[1,2,3,4,5,10,11],[0,1]),([1,2,3,4,14],[8,11,12,13],[]),([15,1,2,3,4],[0,1,8,11,14],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_6 : checkNodesBT W_16 g_16 F_16 P_16_6 A_16 B_16_5 6 N_16_6 = true := by decide +kernel
def B_16_6 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_6
set_option maxRecDepth 500000 in
lemma B_16_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 6 xs.toFinset) B_16_6 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_5_ok C_16_6
def P_16_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 [0,3,4,5,7,8]
def N_16_7 : List NodeSpec := [([0,1,2,3,4],[0,3,4,5,7,8],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_7 : checkNodesBT W_16 g_16 F_16 P_16_7 A_16 B_16_6 7 N_16_7 = true := by decide +kernel
def B_16_7 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_7
set_option maxRecDepth 500000 in
lemma B_16_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 7 xs.toFinset) B_16_7 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_6_ok C_16_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck r_16 g_16 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT B_16_7 r_16 = true := by decide +kernel
lemma low_16 : Lower r_16 g_16 8 := lower_of_forestBT root_16_ok B_16_7_ok root_16_in
def g_17 := 0xfffee800fffee800fffee800fffee800fffee800fffee800fffee800fffee800
def r_17 : List Nat := varsOf 31
def p_17 : List Nat := [11,11,11,13,13,13,14,14,14,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26,28]
def q_17 : List Nat := [10,9,3,12,9,5,12,10,6,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10,12]
def F_17 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 8 (mkBase p_17 q_17 r_17) [(0,3,4),(1,2,5),(1,0,1),(0,7,3),(1,8,4),(1,0,2),(1,2,1),(1,11,4),(0,3,12),(1,7,4),(3,3,14),(1,1,10),(1,16,4),(3,2,17),(0,3,14),(0,2,14),(3,3,4),(1,21,8),(3,2,4),(3,2,7),(1,24,4),(3,2,3),(1,3,4),(0,10,27),(3,1,3),(1,2,4),(3,29,30),(1,0,4),(3,2,32),(1,26,0),(0,11,4),(3,35,12),(0,0,12),(0,7,30),(3,7,3),(1,39,2),(3,0,3),(3,41,11),(2,3,4),(2,7,4),(3,1,10),(1,10,4),(0,3,46),(3,11,3),(0,1,46),(3,1,14),(3,2,9),(1,2,3),(3,1,52),(3,5,27),(1,23,1),(1,21,7),(2,56,2),(0,11,3),(1,11,3),(3,58,59),(2,7,3),(3,0,30),(3,2,27),(1,63,0),(3,11,27),(1,0,5),(3,2,66),(1,7,3),(1,48,2),(1,48,4),(3,11,4),(1,71,2),(0,16,3),(1,1,4),(2,8,4),(1,26,4),(0,10,3),(3,35,3),(2,26,4),(1,26,1),(1,48,0),(1,34,4),(2,34,4),(0,7,4),(1,84,2),(1,79,0),(0,10,4),(1,21,0),(2,88,2),(1,84,3),(1,0,3),(3,11,91),(1,1,3),(3,2,93),(1,94,0),(0,7,52),(2,11,4),(1,97,0),(1,0,6),(2,16,4),(3,1,4),(1,101,0),(2,102,2),(1,26,7),(3,0,4),(3,105,11),(1,21,2),(1,61,2),(0,7,27),(1,10,3),(3,2,110),(2,24,4),(1,7,5),(3,21,7),(1,29,4),(3,2,115),(3,97,3),(0,3,30),(3,7,4),(3,11,32),(2,7,5),(1,58,0),(3,0,11),(3,123,3),(1,29,0),(2,125,2),(1,23,7),(3,41,74),(3,26,27),(3,2,74),(1,130,0),(3,62,3),(0,3,74),(1,0,133),(0,3,32),(1,23,0)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^256) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_17 : BT (List (Nat × Nat)) := btOfList 3 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 2 0) 6 := by
  have hc : Lower (varsOf 29) 0xfffaa000fffaa000fffaa000fffaa000fffaa000fffaa000fffaa000fffaa000 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_8
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xfefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_7 : Slice r_17 g_17 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xfefec8c8fefec8c8fefec8c8fefec8c8fefec8c8fefec8c8fefec8c8fefec8c8 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_8 : Slice r_17 g_17 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) 0xfefee0e0fefee0e0fefee0e0fefee0e0fefee0e0fefee0e0fefee0e0fefee0e0 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_17 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 1 0,6),some (subcubeFast 2 0,6),some (subcubeFast 4 0,6),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (identDom 0 3,5),some (identDom 1 3,5),some (identDom 2 3,5)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (forall_cons (fun _ h => by cases h; exact sl_17_7) (forall_cons (fun _ h => by cases h; exact sl_17_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_17 : BT (Option PoolSpec) := btOfList 7 ((([(1,[(0,11,4),(1,11,4),(3,35,12)]),(1,[]),(2,[]),(0,[]),(0,[(0,3,4),(1,3,4),(3,5,27)]),(1,[(0,11,3),(1,11,3),(3,58,59)]),(0,[(1,3,4),(3,2,27)]),(1,[(1,3,4),(3,2,27)]),(2,[(0,3,4),(1,0,5)]),(0,[(0,7,3),(1,7,3)]),(7,[]),(4,[]),(8,[]),(0,[(1,7,4),(3,2,14)]),(3,[(1,26,4)]),(3,[]),(1,[(0,11,4),(3,35,3)]),(6,[]),(0,[(0,7,4),(1,84,2)]),(4,[(2,3,30)]),(0,[(0,7,4),(1,84,3)]),(1,[(3,2,3),(1,26,0)]),(0,[(0,3,4),(1,2,5)]),(3,[(1,2,5)]),(1,[(1,0,4),(3,2,32)]),(0,[(3,7,3),(1,39,2)]),(0,[(3,2,3),(1,26,7)]),(0,[(2,7,3),(3,7,3)]),(5,[]),(0,[(2,7,3),(1,61,2)]),(0,[(1,3,4),(0,7,27)]),(0,[(0,7,4),(1,7,4)]),(0,[(0,3,4),(1,7,5)]),(0,[(1,1,32),(0,3,14)]),(1,[(1,0,4),(0,3,14)]),(0,[(1,7,4),(0,3,14)]),(1,[(1,7,4),(0,3,14)]),(0,[(0,3,4),(1,3,4)]),(1,[(1,2,0)]),(0,[(1,7,4),(3,3,14)]),(0,[(1,2,4),(0,3,30)]),(3,[(1,2,4)]),(0,[(2,7,4),(3,7,4)]),(1,[(3,0,3),(3,41,11)]),(0,[(1,2,4),(0,7,30)]),(1,[(1,0,4),(3,11,32)]),(0,[(0,3,4),(2,7,5)]),(1,[(1,3,4),(3,11,27)]),(0,[(2,3,4),(3,3,4)]),(2,[(3,1,3),(1,29,0)]),(1,[(0,3,4),(1,3,4),(3,5,27)]),(2,[(0,3,4),(1,3,4),(3,5,27)]),(0,[(1,1,4),(3,2,74)]),(0,[(1,1,32),(3,2,14)]),(3,[(1,1,4)]),(4,[(3,2,3)]),(0,[(1,1,4),(0,3,74)]),(0,[(3,3,4)]),(1,[(2,3,4),(3,3,4)]),(2,[(2,3,4),(3,3,4)]),(2,[(1,3,4)]),(4,[(3,2,27)]),(0,[(0,3,4)]),(1,[(0,3,4),(1,0,5)]),(3,[(1,0,5)]),(1,[(0,3,4),(1,2,5)]),(1,[(0,3,4),(1,3,4)]),(2,[(0,3,4),(1,3,4)]),(0,[(0,3,32)]),(1,[(1,0,4),(0,3,32)]),(2,[(1,0,4),(0,3,32)]),(0,[(3,2,32)]),(2,[(1,0,4)]),(0,[(1,1,4)]),(1,[(1,0,4)]),(2,[(2,3,4)]),(1,[(3,2,3)]),(2,[(3,1,3)]),(0,[(3,2,3)]),(2,[(1,26,4)]),(2,[(1,26,0)]),(0,[(3,2,4)]),(2,[(1,23,0)]),(2,[(1,0,1)]),(0,[(2,7,3)]),(0,[(1,7,3)]),(0,[(1,7,2)]),(0,[(1,7,4)]),(0,[(1,3,4)]),(0,[(2,7,2)]),(0,[(0,7,3)]),(1,[(0,7,3)]),(0,[(1,2,4)]),(0,[(1,1,2)]),(1,[(3,11,3)]),(1,[(2,7,2)]),(0,[(1,1,32)]),(1,[(1,7,2)]),(0,[(1,2,1)]),(1,[(3,11,4)]),(2,[(3,11,3)]),(0,[(0,7,4)]),(2,[(2,26,4)]),(1,[(1,7,4)]),(0,[(2,7,4)]),(1,[(2,7,4)]),(0,[(1,2,3)]),(0,[(2,3,4)]),(0,[(3,2,91)]),(2,[(1,0,3)]),(1,[(3,3,4)]),(2,[(3,3,4)]),(1,[(2,3,4)]),(1,[(1,3,4)]),(1,[(0,3,4)]),(2,[(0,3,4)]),(1,[(3,2,4)]),(1,[(1,0,3)])] : List PoolSpec)).map some)
def B_17_2 : BT (List (List Nat)) := BT.empty
lemma B_17_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 2 xs.toFinset) B_17_2 := .empty
def P_17_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 []
def N_17_3 : List NodeSpec := [([0,1,6,9],[],[]),([7,10,13,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_3 : checkNodesBT W_17 g_17 F_17 P_17_3 A_17 B_17_2 3 N_17_3 = true := by decide +kernel
def B_17_3 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_3
set_option maxRecDepth 500000 in
lemma B_17_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 3 xs.toFinset) B_17_3 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_2_ok C_17_3
def P_17_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 [0,1,2,3,4,5]
def N_17_4 : List NodeSpec := [([15,18,0,1,4],[],[]),([18,0,1,19,4],[],[]),([15,0,1,20,4],[],[]),([0,1,22,2,4],[],[]),([23,0,1,3,25],[],[]),([26,0,1,28,4],[],[]),([0,31,11,3,4],[],[]),([33,34,1,3,4],[],[]),([0,1,10,13,4],[],[0]),([36,0,1,2,3],[0],[]),([37,1,2,13,4],[],[]),([0,38,11,3,4],[1],[]),([0,1,40,4,27],[],[]),([42,1,10,3,4],[2],[]),([26,0,8,11,4],[],[]),([43,0,1,40,4],[],[]),([44,10,11,3,4],[],[]),([24,45,0,3,4],[],[]),([33,0,1,47,4],[],[]),([48,7,10,3,4],[3],[]),([33,0,49,3,4],[],[]),([44,50,0,2,3],[],[]),([7,10,3,4,12],[3],[0]),([8,10,11,3,4],[],[]),([51,0,1,3,4],[],[]),([24,53,0,3,4],[],[]),([54,0,1,7,2],[4],[]),([24,0,55,3,4],[],[]),([57,0,1,3,4],[],[]),([18,0,1,3,4],[],[]),([0,1,2,5,9],[],[0]),([0,1,8,6,4],[],[0]),([60,0,1,2,4],[5],[]),([61,0,1,40,4],[],[]),([33,62,1,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_4 : checkNodesBT W_17 g_17 F_17 P_17_4 A_17 B_17_3 4 N_17_4 = true := by decide +kernel
def B_17_4 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_4
set_option maxRecDepth 500000 in
lemma B_17_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 4 xs.toFinset) B_17_4 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_3_ok C_17_4
def P_17_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 [1,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56]
def N_17_5 : List NodeSpec := [([0,64,1,2,3,4],[6],[]),([65,63,0,1,3,4],[7],[]),([63,0,64,1,3,4],[6],[]),([67,0,1,2,3,4],[8],[]),([44,0,1,2,3,4],[],[]),([0,1,8,2,68,4],[9],[4]),([0,1,69,11,3,4],[1,10],[]),([0,1,16,3,4,30],[11],[]),([0,1,2,3,4,70],[],[]),([0,1,72,11,3,4],[1,11],[]),([0,1,2,73,3,4],[],[]),([24,23,0,1,3,4],[],[0,2]),([0,11,3,4,74,30],[1,11],[]),([67,1,2,3,66,4],[8],[]),([0,1,40,3,4],[],[0]),([61,29,0,7,2,4],[],[]),([21,0,1,8,2,4],[],[0]),([24,0,1,3,52,4],[12],[0,2]),([18,0,1,7,3,4],[13],[]),([33,0,1,3,4,30],[2],[0]),([75,0,1,2,3,4],[],[]),([43,26,0,1,2,76],[11,14],[]),([26,0,1,77,10,4],[15],[]),([43,48,0,1,2,4],[11],[3]),([26,0,1,8,2,4],[2],[0,2]),([78,0,1,2,11,4],[16],[]),([79,0,1,10,3,4],[3],[]),([37,1,2,3,4,12],[],[0,2,3,4]),([26,0,80,11,3,4],[1],[]),([0,1,2,3,4,9],[1,2,3,17],[0]),([0,1,10,3,4,12],[3],[0]),([0,81,1,2,3,4],[],[]),([0,1,2,3,4,82],[15],[]),([0,1,2,3,4,17],[15,17],[0,1,3]),([48,0,1,10,3,4],[3],[0]),([83,0,1,2,3,4],[],[]),([0,1,7,85,3,4],[18],[]),([24,29,0,2,3,4],[],[]),([0,86,1,2,3,4],[],[]),([0,1,87,10,3,30],[],[]),([0,7,11,3,4,30],[],[0,2]),([89,0,1,2,3,4],[],[]),([26,0,7,11,3,4],[],[0,2,4]),([0,1,10,3,4,76],[3],[]),([0,1,2,3,76,30],[2,12,19],[]),([44,0,2,11,3,4],[2],[0]),([0,1,7,2,90,4],[20],[]),([92,0,1,2,3,4],[17],[]),([24,0,7,11,3,4],[1,2],[]),([63,0,1,10,3,4],[3],[]),([26,0,1,10,4,27],[],[0]),([0,95,1,2,3,4],[],[]),([48,0,1,2,4,27],[],[3]),([0,1,96,2,3,4],[],[]),([26,33,0,1,3,4],[15],[0]),([0,34,1,11,3,4],[21],[]),([0,98,1,2,3,4],[],[]),([0,1,3,6,99,4],[12,22,23],[]),([100,0,1,2,3,4],[],[]),([33,1,7,2,3,4],[1,24],[]),([0,1,7,40,3,4],[17,25],[0]),([0,1,8,2,5,4],[10,17],[0]),([26,29,0,11,3,4],[1,2,15],[]),([103,0,1,2,3,4],[],[]),([0,1,104,2,3,4],[2,26],[]),([106,0,1,2,3,4],[],[]),([61,39,0,1,2,4],[27],[0,4]),([0,1,10,3,6,4],[3,12,23],[]),([0,1,107,10,3,4],[3,15],[]),([26,0,1,16,3,4],[15],[]),([43,26,0,1,10,4],[28],[]),([44,0,7,2,3,74],[11],[]),([24,0,1,16,3,4],[3],[0,2]),([0,1,7,108,3,4],[29],[]),([0,1,109,2,3,4],[15,30],[1,3]),([0,1,84,2,3,14],[31],[4]),([111,0,1,11,3,4],[1,15],[3]),([33,0,1,3,4,46],[3],[0,1]),([112,0,1,2,3,4],[],[]),([0,1,2,3,113,4],[17,32],[]),([0,1,114,2,3,4],[],[]),([0,1,8,2,52,4],[2],[]),([18,0,1,3,4],[],[]),([0,1,2,19,4,32],[33,34],[1]),([24,0,2,3,4,74],[],[]),([18,0,1,2,3,4],[],[]),([18,0,1,3,4,14],[2],[0]),([0,1,2,19,4],[35,36],[4,5]),([0,1,2,19,3,4],[],[]),([0,1,7,2,5,27],[37],[0]),([7,10,11,3,4],[1,2,3,38],[0,1,2,3,4]),([0,1,2,19,4,14],[15],[0,1,3,4]),([15,0,1,2,4,14],[17],[0]),([15,0,1,7,2,4],[39],[]),([44,0,1,2,3,14],[3],[0,2]),([33,0,1,10,3,4],[3],[1]),([0,1,7,2,19,4],[35],[]),([43,0,34,1,2,4],[],[]),([116,0,1,2,3,4],[],[]),([33,1,10,3,4,32],[2],[]),([111,0,1,10,3,4],[3,15],[]),([0,1,2,117,3,4],[1,2,3,17],[]),([0,1,10,118,3,4],[3,40,41],[]),([0,1,72,10,3,4],[3],[1]),([0,1,2,3,4,14],[2,15,17],[0]),([44,119,0,1,2,3],[42],[4]),([24,0,1,10,3,4],[3],[0]),([42,0,1,2,3,4],[1,2,15,43],[0,1]),([0,1,38,2,3,4],[1,11,44],[0,2]),([120,0,1,2,3,4],[45],[]),([0,1,77,11,3,4],[1],[1]),([121,0,1,2,3,4],[3,46],[]),([0,1,2,122,3,4],[],[]),([0,1,7,3,6,4],[22,23],[0]),([0,124,1,2,3,4],[17],[]),([65,0,1,2,3,4],[47],[]),([63,0,1,7,3,4],[6],[]),([43,21,0,1,7,2],[48],[0]),([0,1,56,2,3,4],[2,15],[0]),([0,1,69,3,4,30],[11],[4]),([126,0,1,2,3,4],[49],[]),([0,34,1,2,4,27],[],[]),([0,1,127,2,3,4],[15,17],[0]),([0,128,1,2,3,4],[],[4]),([54,0,1,2],[4,28,50,51],[0,1,3]),([0,1,8,2,3,4],[],[]),([26,0,1,2,129,4],[15],[]),([0,131,1,2,3,4],[52],[]),([18,0,1,3,4,32],[53],[]),([44,0,1,2,3,32],[3],[0]),([0,1,2,3,4,25],[],[0]),([26,0,11,3,4,74],[1,54,55],[1]),([132,0,1,2,3,4],[],[]),([0,1,2,3,134,4],[56],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_5 : checkNodesBT W_17 g_17 F_17 P_17_5 A_17 B_17_4 5 N_17_5 = true := by decide +kernel
def B_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_5
set_option maxRecDepth 500000 in
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_4_ok C_17_5
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 [1,2,3,6,7,8,10,11,12,14,15,17,21,22,23,24,28,37,38,41,48,55,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109]
def N_17_6 : List NodeSpec := [([0,88,1,2,3,4],[1,2,11,15,57],[0,1,3,5]),([43,21,0,1,2],[28,48,58,59],[0,1,3]),([63,0,1,2,3,4],[1,2,3,6,7,15,28,60],[0,2]),([63,0,1,3,4],[6,7,15,28,61],[0,2]),([0,1,2,3,66,4],[8,28,62,63,64],[0,1,3,5]),([0,1,3,6,4],[22,23,28,65],[0,2,4,5]),([0,1,2,135,3,4,32],[3,11,17,28],[]),([0,1,2,5,27],[11,15,37,66,67],[0,1,3]),([0,1,2,135,3,4],[1,2,10,11,12,17,28,68,69,70],[2,3,4,5]),([33,0,1,2,3,4,32],[2,3,11,71,72],[0]),([33,0,1,2,3,4],[1,3,12,15,24,71,72],[0,2,5]),([0,1,2,3,4,32,74],[73,74],[1,3,4]),([43,26,0,1,2,4],[2,11,28,75],[0,2]),([26,0,1,2,4,27],[11,15,28,55,60],[0,2]),([26,29,0,1,2,3,4],[2,10,12,76,77],[0]),([26,0,1,2,3,4,32],[3,12,72,78],[0,2,3,4]),([26,0,1,2,3,4,76],[2,12,14,28],[0]),([0,1,2,3,4,76],[1,3,12,14,28,79],[0,1,2,3]),([26,0,34,1,2,3,4],[15,17,78,80],[2]),([0,136,1,2,3,4],[1,11,28,81,82],[0,1,3]),([79,0,1,2,3,4,30],[12,28],[0]),([61,0,1,7,2,3,4],[1,3,15,83,84],[0,2]),([0,1,7,2,3,68,4],[15,17,85],[0,1,3]),([0,1,7,2,16,3,4],[83,86],[0,1,3]),([0,1,7,2,3,4,14],[11,83,87],[0,1,3]),([26,0,1,7,2,3,4],[1,2,3,12,15,78,83],[0,1,2,3,4]),([0,1,7,2,3,4,27],[1,15,83,88],[0,1,3,4]),([24,0,1,7,2,3,4],[1,2,3,83,89],[0,2]),([0,1,8,2,3,4],[1,2,3,11,12,17,90,91],[0,1,3,4]),([0,1,10,3,4,30],[2,11,41,92],[0,1,2,3,4,5]),([48,0,1,2,11,3,4],[10,15,93,94],[0,1,3]),([24,0,1,2,3,4],[1,3,11,12,15,83,89,95],[0,2,4]),([0,1,2,3,4,32,14],[28,72,74,96],[0,1,3]),([0,1,2,16,3,4],[11,15,17,83,86,97],[0,1,3]),([0,1,8,7,2,3,4],[1,15,17,90],[0,1,3]),([26,0,1,10,3,4],[2,3,15,55,78],[0,1,2]),([0,1,7,2,5,3,4],[1,11,15,62,83],[0,1,3]),([0,1,10,11,3,4],[2,38,98],[0,1,2,3]),([71,0,1,2,11,3,4],[11,99],[0,1,3]),([48,0,1,2,3,4],[3,10,11,94,100],[0,1,3]),([0,1,84,7,2,3,4],[1,11,83,101],[0,1,3,4]),([79,0,1,2,3,4],[1,3,10,12,17,28,102],[0,2]),([0,1,2,3,4,14],[2,15,17,87,103],[0,1,3,4,5]),([44,0,1,2,3,4],[1,2,3,15,104,105],[0,2,4]),([44,0,1,7,2,3,4],[1,3,11,104],[0,2]),([0,1,7,2,3,52,4],[1,2,15,83,106],[0,4,5]),([43,0,1,7,2,3,4],[1,3,17,28,107],[0,1,3,4]),([21,0,1,7,2,3,4],[1,3,15,57],[0,1,3]),([23,0,1,7,2,3,4],[1,2,3,11,81,83],[0,1,3,4]),([111,0,1,2,3,4],[1,3,11,15,28,108,109],[0,2]),([0,1,7,2,3,4,30],[1,2,83,92],[0,1,2,3,4]),([0,34,1,2,3,4],[11,17,21,78,80],[0,1,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6 = true := by decide +kernel
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_5_ok C_17_6
def P_17_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 [1,2,3,11,12,15,28,57,60,62,72,74,75,76,78,81,83,88,107,109,110,111,112,113,114,115,116,117]
def N_17_7 : List NodeSpec := [([21,0,1,2,3,4],[1,2,3,11,15,57,110,111],[0,1,2,3,4]),([43,0,1,2,3,4],[1,2,3,28,75,107,112],[0,1,3]),([0,1,2,3,4,27],[1,2,3,15,28,60,88,113],[0,1,3]),([0,1,2,5,3,4],[1,2,3,11,15,28,62,114,115],[0,1,2,3,4]),([23,0,1,2,3,4],[1,2,3,11,15,28,81,116],[0,2]),([26,0,1,2,3,4],[1,2,3,11,12,15,28,76,78],[0,2]),([0,1,2,3,91,4],[3,15,28,109,117],[0,1,3]),([0,1,2,3,4,32],[3,28,72,74],[0,1,3,5]),([0,1,7,2,3,4],[1,2,3,11,15,83],[0,1,3,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7 = true := by decide +kernel
def B_17_7 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_7
set_option maxRecDepth 500000 in
lemma B_17_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 7 xs.toFinset) B_17_7 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_6_ok C_17_7
def P_17_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_17 r_17 S_17 ps_17 [1,2,3]
def N_17_8 : List NodeSpec := [([0,1,2,3,4],[1,2,3],[0,1,2,3,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_8 : checkNodesBT W_17 g_17 F_17 P_17_8 A_17 B_17_7 8 N_17_8 = true := by decide +kernel
def B_17_8 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_8
set_option maxRecDepth 500000 in
lemma B_17_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 8 xs.toFinset) B_17_8 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_7_ok C_17_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_8 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 9 := lower_of_forestBT root_17_ok B_17_8_ok root_17_in
def g_18 := 0xfffcf880fffcf880fffcf880fffcf880fffcf880fffcf880fffcf880fffcf880
def r_18 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_18 : Lower r_18 g_18 8 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_19 := 0xfffcfc80fffcfc80fffcfc80fffcfc80fffcfc80fffcfc80fffcfc80fffcfc80
def r_19 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_19 : Lower r_19 g_19 8 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_20 := 0xfff8c000fff8c000fff8c000fff8c000fff8c000fff8c000fff8c000fff8c000
def r_20 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_20 : Lower r_20 g_20 7 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,18,19)]) (by decide +kernel) hc
def g_21 := 0xfffef800fffef800fffef800fffef800fffef800fffef800fffef800fffef800
def r_21 : List Nat := varsOf 31
def p_21 : List Nat := [11,11,11,12,12,13,13,14,14,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26]
def q_21 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10]
def F_21 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_21 : goodPairs g_21 p_21 q_21 := goodPairs_of (by decide +kernel)
def W_21 : BT Decor := buildWiresBT 6 (mkBase p_21 q_21 r_21) [(0,3,4),(1,2,5),(1,0,6),(1,1,6),(1,3,4),(3,6,9),(3,5,9),(2,11,1),(3,2,9),(1,1,3),(1,14,4),(3,1,15),(1,0,3),(0,17,4),(1,2,18),(2,0,5),(1,1,5),(2,13,1),(2,13,0),(1,0,5),(0,0,9),(0,11,0),(2,0,6),(3,3,4),(1,28,0),(2,29,1),(2,3,4),(0,13,0),(3,0,3),(3,33,4),(3,1,4),(3,1,3),(1,36,4),(1,35,3),(1,33,1),(3,0,4),(1,40,3),(3,1,41),(1,1,18),(1,17,4),(3,2,44),(3,1,44),(3,2,38),(3,0,44),(0,14,4),(1,1,4),(1,31,0),(3,14,4),(2,17,4),(3,40,3),(1,0,4),(3,1,55),(0,3,55),(3,3,55)]
lemma W_21_ok : btAll (fun x => faithful p_21 q_21 x ∧ x.1 < 2^256) W_21 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_21 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_21 : BT (List (Nat × Nat)) := btOfList 1 al_21
set_option maxHeartbeats 0 in
lemma A_21_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_21 = g_21) A_21 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_21_0 : Slice r_21 g_21 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_1 : Slice r_21 g_21 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_2 : Slice r_21 g_21 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcf000fffcf000fffcf000fffcf000fffcf000fffcf000fffcf000fffcf000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_3 : Slice r_21 g_21 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_4 : Slice r_21 g_21 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xfefec8c8fefec8c8fefec8c8fefec8c8fefec8c8fefec8c8fefec8c8fefec8c8 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_5 : Slice r_21 g_21 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xfefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_10
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
def S_21 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 4 0,6),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 3 0,4),some (identDom 1 3,5),some (identDom 0 3,5)]
lemma S_21_ok : btAll (fun o => ∀ p, o = some p → Slice r_21 g_21 p.1 p.2) S_21 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_21_0) (forall_cons (fun _ h => by cases h; exact sl_21_1) (forall_cons (fun _ h => by cases h; exact sl_21_2) (forall_cons (fun _ h => by cases h; exact sl_21_3) (forall_cons (fun _ h => by cases h; exact sl_21_4) (forall_cons (fun _ h => by cases h; exact sl_21_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_21 : BT (Option PoolSpec) := btOfList 5 ((([(0,[(0,3,4),(1,3,4),(3,5,9)]),(0,[(0,3,4),(1,3,4)]),(1,[]),(0,[(2,3,4),(3,3,4)]),(2,[]),(0,[]),(3,[]),(0,[(1,3,4),(0,0,9)]),(5,[]),(0,[(0,3,4),(1,1,5)]),(0,[(1,3,4),(3,1,9)]),(2,[(3,1,4)]),(0,[(3,0,3),(1,33,1)]),(0,[(0,3,4),(2,0,5)]),(2,[(1,1,3)]),(4,[]),(0,[(1,0,4),(3,1,55)]),(2,[(3,1,55)]),(0,[(3,3,4)]),(0,[(2,3,4)]),(0,[(1,3,4)]),(0,[(0,3,4)]),(0,[(3,1,4)]),(0,[(1,0,4)]),(0,[(3,1,3)]),(1,[(1,0,3)]),(0,[(1,0,3)])] : List PoolSpec)).map some)
def B_21_1 : BT (List (List Nat)) := BT.empty
lemma B_21_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 1 xs.toFinset) B_21_1 := .empty
def P_21_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 []
def N_21_2 : List NodeSpec := [([7,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_2 : checkNodesBT W_21 g_21 F_21 P_21_2 A_21 B_21_1 2 N_21_2 = true := by decide +kernel
def B_21_2 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_2
set_option maxRecDepth 500000 in
lemma B_21_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 2 xs.toFinset) B_21_2 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_1_ok C_21_2
def P_21_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 []
def N_21_3 : List NodeSpec := [([10,11,0,1],[],[]),([12,11,0,2],[],[]),([11,13,0,1],[],[]),([11,16,0,2],[],[]),([11,0,1,2],[],[]),([0,1,19,9],[],[]),([20,11,1,2],[],[]),([0,21,6,9],[],[]),([22,23,3,4],[],[]),([2,24,21,9],[],[]),([11,0,2,21],[],[]),([11,0,1,6],[],[]),([20,1,6,9],[],[]),([11,25,1,2],[],[]),([3,7,8,4],[],[0]),([10,0,1,9],[],[]),([25,1,6,9],[],[]),([16,0,6,9],[],[]),([26,11,1,2],[],[]),([0,6,8,9],[],[0]),([27,1,6,9],[],[]),([0,1,6,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_3 : checkNodesBT W_21 g_21 F_21 P_21_3 A_21 B_21_2 3 N_21_3 = true := by decide +kernel
def B_21_3 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_3
set_option maxRecDepth 500000 in
lemma B_21_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 3 xs.toFinset) B_21_3 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_2_ok C_21_3
def P_21_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 [0,1]
def N_21_4 : List NodeSpec := [([13,0,1,3,4],[],[]),([0,1,3,6,4],[],[0]),([22,13,0,3,4],[],[0]),([13,16,0,3,4],[],[]),([13,25,1,3,4],[],[]),([30,0,2,3,4],[],[]),([16,25,2,3,4],[],[]),([11,0,1,2,4],[],[]),([11,0,1,2,3],[],[]),([11,0,1,2],[0],[0,1]),([13,0,1,5,9],[],[0]),([16,0,2,5,9],[],[0]),([31,28,0,1,2],[],[0]),([32,13,1,3,4],[],[]),([25,1,2,5,9],[],[0]),([0,1,2,5,9],[],[0]),([0,1,5,6,9],[],[0,1]),([0,1,6,9],[1],[0,1]),([31,0,34,1,2],[],[]),([20,1,3,6,4],[],[0]),([35,0,2,3,37],[],[]),([28,11,0,1,2],[],[]),([0,1,3,6,9],[],[]),([36,0,2,38,4],[],[]),([0,39,2,4,9],[],[]),([28,0,1,3,6],[],[0]),([31,11,0,1,2],[],[]),([42,0,2,3,4],[],[]),([16,0,2,3,4],[],[]),([0,1,3,19,4],[],[0]),([11,0,1,2,5],[0],[0,1]),([0,2,3,43,4],[],[]),([45,0,1,3,4],[],[]),([0,1,2,18,9],[],[0]),([46,0,2,3,4],[],[]),([47,0,1,3,4],[],[]),([11,0,1,2,9],[0],[0,1]),([31,0,2,21,4],[],[]),([0,2,21,4,9],[],[]),([0,3,21,6,4],[],[0]),([16,48,2,3,4],[],[]),([20,2,3,21,4],[],[]),([31,0,39,2,4],[],[]),([0,2,5,21,9],[],[0]),([20,1,2,5,9],[],[0]),([2,3,24,21,4],[],[0]),([0,3,6,8,4],[],[0]),([0,2,3,49,50],[],[]),([31,0,1,6,4],[],[0]),([27,1,3,6,4],[],[0]),([0,1,6,4,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_4 : checkNodesBT W_21 g_21 F_21 P_21_4 A_21 B_21_3 4 N_21_4 = true := by decide +kernel
def B_21_4 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_4
set_option maxRecDepth 500000 in
lemma B_21_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 4 xs.toFinset) B_21_4 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_3_ok C_21_4
def P_21_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]
def N_21_5 : List NodeSpec := [([0,29,1,2,3,4],[2],[0]),([31,28,0,1,2,4],[],[0]),([31,28,0,1,2],[3],[0]),([0,1,2,3,4,9],[2,4,5],[0,1]),([0,51,1,2,3,4],[],[]),([16,0,1,2,3,4],[],[]),([13,0,1,3,4],[],[0,1]),([25,1,2,3,4,9],[6,7],[0,1]),([31,28,0,1,2,3],[],[0]),([0,1,2,5,3,9],[],[0]),([28,0,1,2,3,4],[],[0]),([31,36,0,1,2,4],[2],[1]),([0,1,2,3,18,4],[2,5,8],[0,1]),([0,2,5,3,21,4],[2,9],[0]),([0,1,3,6,4],[],[0,1]),([0,1,2,3,4,37],[],[0]),([36,0,1,2,4,9],[2],[1]),([52,0,1,2,3,4],[],[]),([28,0,1,2,4,9],[5],[0]),([53,0,1,2,3,4],[],[]),([16,0,2,3,4],[10],[]),([54,0,1,2,3,4],[],[]),([36,35,0,2,3,4],[11],[0]),([0,1,2,3,4,44],[2,5],[0,1]),([0,1,2,3,38,4],[4,5],[0,1]),([31,0,1,2,3,9],[5],[0]),([0,39,2,3,4],[12],[0]),([20,1,2,5,3,4],[6,8,13],[0]),([31,0,1,2,17,4],[4],[]),([16,0,2,3,4,9],[2,10],[0]),([35,0,2,3,4,50],[2,11],[]),([0,2,3,14,4,50],[14,15],[0]),([0,1,2,3,24,4],[],[]),([0,34,1,2,3,4],[4],[0]),([31,0,1,2,5,4],[5],[0,1]),([0,1,2,17,4,9],[4],[0]),([56,0,2,3,4],[16],[]),([0,1,2,5,4,9],[],[0,1]),([0,2,3,21,4],[9],[0]),([56,0,2,3,4,55],[2,17],[]),([0,1,2,5,3,4],[2,4,5,8,15],[0]),([0,1,2,5,9],[1],[0,1]),([0,1,5,3,6,4],[5],[0,1]),([0,1,2,57,3,4],[8],[]),([58,0,1,2,3,4],[],[]),([31,0,1,2,3,4],[],[0]),([13,0,1,3,4,9],[5],[0,1]),([28,0,1,2,5,3],[5],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_5 : checkNodesBT W_21 g_21 F_21 P_21_5 A_21 B_21_4 5 N_21_5 = true := by decide +kernel
def B_21_5 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_5
set_option maxRecDepth 500000 in
lemma B_21_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 5 xs.toFinset) B_21_5 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_4_ok C_21_5
def P_21_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 [2,4,5,6,8,15,18,19,20,21,22,23,24,25,26]
def N_21_6 : List NodeSpec := [([28,0,1,2,3,4],[2,4,5,18],[0,1]),([31,0,1,2,3,4],[2,4,5,8,15,19],[0,1]),([0,1,2,3,4,9],[2,4,20],[0,1]),([0,1,2,5,3,4],[2,4,8,15,21],[0,1]),([35,0,1,2,3,4],[4,5,6,15,22],[0,1]),([0,1,2,3,4,55],[6,8,23],[0,1]),([36,0,1,2,3,4],[4,6,15,24],[0,1]),([0,1,2,3,17,4],[4,6,8,25,26],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_6 : checkNodesBT W_21 g_21 F_21 P_21_6 A_21 B_21_5 6 N_21_6 = true := by decide +kernel
def B_21_6 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_6
set_option maxRecDepth 500000 in
lemma B_21_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 6 xs.toFinset) B_21_6 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_5_ok C_21_6
def P_21_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 [2,5,6]
def N_21_7 : List NodeSpec := [([0,1,2,3,4],[2,5,6],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_7 : checkNodesBT W_21 g_21 F_21 P_21_7 A_21 B_21_6 7 N_21_7 = true := by decide +kernel
def B_21_7 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_7
set_option maxRecDepth 500000 in
lemma B_21_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 7 xs.toFinset) B_21_7 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_6_ok C_21_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_ok : forestRootCheck r_21 g_21 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_in : bucketContainsBT B_21_7 r_21 = true := by decide +kernel
lemma low_21 : Lower r_21 g_21 8 := lower_of_forestBT root_21_ok B_21_7_ok root_21_in
def g_22 := 0xfffffff8fee8c000fffffff8fee8c000fffffff8fee8c000fffffff8fee8c000
def r_22 : List Nat := varsOf 63
def p_22 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,22,22,22,23,25,25,25,26,26,26,27,28,28,28,29,35,35,35,36,36,37,37,38,38,39,40,40,41,41,42,42,43,44,45,48,48,49,49,50,50,52,56]
def q_22 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,20,18,6,7,24,17,9,24,18,10,11,24,20,12,13,34,33,3,32,4,33,5,34,6,7,32,8,33,9,34,10,11,12,13,32,16,33,17,34,18,20,24]
def F_22 : Nat := fullMask 54
set_option maxHeartbeats 0 in
lemma gp_22 : goodPairs g_22 p_22 q_22 := goodPairs_of (by decide +kernel)
def W_22 : BT Decor := buildWiresBT 9 (mkBase p_22 q_22 r_22) [(1,2,3),(1,4,5),(3,6,7),(0,2,3),(1,8,9),(0,1,10),(1,1,10),(3,11,12),(2,1,10),(3,1,10),(0,1,4),(1,1,4),(3,16,17),(0,18,3),(3,19,18),(1,20,2),(0,18,2),(3,22,18),(1,23,3),(3,1,6),(3,25,4),(1,26,9),(2,27,5),(1,9,5),(1,26,29),(1,26,5),(0,1,6),(3,32,7),(1,6,5),(3,9,34),(3,35,4),(1,36,5),(1,1,2),(0,38,4),(1,39,5),(0,3,40),(1,3,40),(3,41,42),(3,2,21),(3,32,4),(1,45,5),(1,16,5),(1,16,9),(3,48,34),(1,35,16),(3,18,3),(1,20,51),(3,25,7),(1,53,9),(3,2,3),(1,20,55),(2,18,9),(1,2,5),(0,3,58),(3,59,34),(0,60,1),(1,3,5),(0,1,62),(1,1,62),(3,63,64),(1,65,2),(3,35,1),(0,35,1),(3,6,4),(1,69,9),(0,1,70),(0,6,4),(1,6,4),(3,72,73),(3,9,73),(1,1,6),(3,9,76),(3,32,76),(0,6,7),(1,72,5),(2,1,5),(1,81,3),(0,2,4),(1,83,5),(2,1,62),(1,16,2),(1,86,5),(3,3,87),(0,1,3),(1,89,83),(1,1,3),(1,2,4),(3,3,2),(1,93,47),(0,4,58),(1,89,95),(2,6,47),(1,97,5),(2,6,4),(0,4,34),(1,3,47),(2,1,84),(1,102,3),(1,9,47),(3,3,4),(3,105,7),(0,1,2),(1,107,5),(3,60,1),(1,18,2),(1,6,47),(3,5,111),(2,1,70),(1,105,5),(2,2,47),(3,1,34),(0,91,4),(1,117,5),(0,2,118),(2,2,118),(3,2,118),(3,3,40),(3,16,34),(2,1,58),(1,124,3),(0,3,4),(1,126,5),(2,3,47),(1,128,5),(1,2,118),(1,107,106),(1,120,5),(3,5,130),(0,1,58),(1,1,58),(3,134,135),(2,136,3),(1,16,3),(1,55,5),(1,115,3),(1,128,58),(2,2,62),(1,142,3),(3,2,101),(2,110,3),(1,32,5),(3,51,2),(3,18,2),(1,148,3),(0,35,4),(3,55,18),(1,1,5),(0,4,152),(1,9,153),(2,1,6),(1,155,9),(3,1,4),(1,157,5),(1,124,95),(2,2,127),(1,160,5),(3,3,7),(1,162,2),(3,55,64),(0,1,34),(0,1,80),(2,4,5),(1,85,2),(1,25,5),(0,76,4),(2,6,5),(2,1,29),(1,1,29),(3,81,4),(3,3,58),(3,2,62),(3,1,2),(1,177,5),(1,83,3),(3,1,3),(1,180,5),(1,177,3),(0,4,62),(2,38,183),(2,1,3),(3,2,4),(1,186,5),(1,2,183),(2,1,127),(3,16,6),(3,116,4),(2,38,5),(2,38,127),(1,3,4),(1,89,5),(2,2,195),(1,196,5),(1,83,195),(2,1,80),(2,3,178),(1,200,5),(1,177,183),(1,83,181),(1,115,5),(0,38,7),(1,107,126),(1,93,5),(3,186,7),(3,165,4),(3,107,4),(1,107,183),(2,4,62),(1,2,126),(1,213,5),(1,105,2),(1,69,32),(3,107,7),(1,175,16),(1,185,2),(1,81,2),(1,189,2),(1,128,2),(3,16,58),(1,142,16),(1,93,16),(3,9,17),(2,1,4),(1,124,93),(3,157,34),(1,85,83),(1,93,153),(2,3,4),(3,232,38),(1,2,153),(0,2,62),(3,1,58),(0,4,135),(3,3,135),(1,63,2),(2,215,5),(1,215,5),(1,186,3),(0,1,215),(1,186,1),(2,244,3),(1,1,84),(3,55,7),(2,1,139),(1,1,207),(3,55,4),(2,3,58),(3,251,4),(1,250,5),(3,3,84),(1,69,5),(3,3,187),(2,3,5),(1,257,83),(3,55,62),(3,9,7),(1,212,2),(3,9,4),(1,262,5),(1,81,83),(1,81,105),(1,81,93),(3,81,6),(1,81,9),(1,2,174),(1,220,3),(3,3,152),(1,271,2),(1,175,1),(3,2,152),(3,186,152),(3,126,152),(3,3,92),(3,55,152),(3,6,152),(0,6,152),(1,185,5),(2,1,2),(1,282,5),(3,282,4),(2,38,3),(1,285,5),(2,2,5),(1,287,157),(2,2,4),(1,289,185),(1,284,5),(2,213,5),(1,89,2),(1,180,2),(1,289,3),(3,282,194),(2,91,5),(1,297,2),(2,219,5),(2,86,3),(1,232,177),(3,3,283),(3,89,4),(0,38,62),(2,285,5),(3,257,4),(1,2,306),(1,287,16),(2,293,5),(1,3,108),(3,180,7),(3,180,4),(1,282,105),(1,257,2),(1,282,3),(3,1,62),(1,316,2),(1,105,177),(3,126,58),(1,117,2),(1,107,3),(3,287,4),(3,186,91),(3,282,7),(1,303,2),(1,105,107),(3,1,215),(3,3,108),(3,126,38),(1,303,5),(1,232,107),(1,232,2),(3,89,7),(3,3,17),(1,334,2),(3,124,4),(3,186,62),(3,89,58),(1,93,157),(3,2,91),(1,257,107),(1,157,9),(1,219,5),(3,282,62),(1,287,185),(3,93,4),(3,2,194),(2,220,3),(2,86,5),(3,2,7),(1,3,84),(3,157,58),(2,294,5),(1,312,5),(1,3,178),(3,175,1),(1,294,5),(2,2,181),(3,3,178),(1,180,83),(3,180,58),(1,257,177),(1,86,3),(1,185,83),(3,3,47),(3,257,38),(1,157,2),(1,367,5),(3,89,92),(3,257,6),(3,9,152),(1,287,105),(1,157,3),(0,38,194),(0,6,17),(3,6,17),(2,367,3),(3,55,17),(3,2,17),(1,227,2),(1,380,3),(2,380,3),(1,293,5),(1,227,9),(3,227,6),(3,180,92),(1,227,93),(3,3,158),(1,367,3),(2,367,5),(1,312,2),(3,185,4),(1,392,2),(3,157,6),(1,105,1),(3,105,1),(3,105,2)]
lemma W_22_ok : btAll (fun x => faithful p_22 q_22 x ∧ x.1 < 2^256) W_22 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_22 : List (List (Nat × Nat)) := [[],[(2,3)]]
def A_22 : BT (List (Nat × Nat)) := btOfList 1 al_22
set_option maxHeartbeats 0 in
lemma A_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_22 = g_22) A_22 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_22_0 : Slice r_22 g_22 (subcubeFast 1 0) 9 := by
  have hc : Lower (varsOf 62) 0xfffffff0fcc0c000fffffff0fcc0c000fffffff0fcc0c000fffffff0fcc0c000 9 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_1 : Slice r_22 g_22 (subcubeFast 32 0) 9 := by
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) low_9
set_option maxHeartbeats 0 in
lemma sl_22_2 : Slice r_22 g_22 (subcubeFast 0 1) 9 := by
  have hc : Lower (varsOf 62) 0xfffffffcfffcc000fffffffcfffcc000fffffffcfffcc000fffffffcfffcc000 9 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_3 : Slice r_22 g_22 (subcubeFast 0 2) 8 := by
  have hc : Lower (varsOf 61) 0xfffffffafffaf000fffffffafffaf000fffffffafffaf000fffffffafffaf000 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_4 : Slice r_22 g_22 (subcubeFast 0 16) 8 := by
  have hc : Lower (varsOf 47) 0xfffffffffee8fee8fffffffffee8fee8fffffffffee8fee8fffffffffee8fee8 8 := carry_of (swaps := [(4,5)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_5 : Slice r_22 g_22 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) 0xffffff88ee880000ffffff88ee880000ffffff88ee880000ffffff88ee880000 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_6 : Slice r_22 g_22 (subcubeFast 8 0) 8 := by
  have hc : Lower (varsOf 55) 0xfffff8f8e8e80000fffff8f8e8e80000fffff8f8e8e80000fffff8f8e8e80000 8 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_7 : Slice r_22 g_22 (subcubeFast 32 16) 7 := by
  exact slice_fast_direct_f (z := 32) (o := 16) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_22_8 : Slice r_22 g_22 (subcubeFast 1 2) 7 := by
  have hc : Lower (varsOf 60) 0xfffffff0fff0f000fffffff0fff0f000fffffff0fff0f000fffffff0fff0f000 7 := carry_of (swaps := [(0,4),(1,5),(2,4),(3,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_9 : Slice r_22 g_22 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) 0xfffffff0faa00000fffffff0faa00000fffffff0faa00000fffffff0faa00000 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_10 : Slice r_22 g_22 (identDom 1 5) 9 := by
  have hc : Lower (varsOf 31) 0xfeecccc8feecccc8feecccc8feecccc8feecccc8feecccc8feecccc8feecccc8 9 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_17
  exact slice_ident (u := 1) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_11 : Slice r_22 g_22 (identDom 2 3) 8 := by
  have hc : Lower (varsOf 55) 0xfffff8f8f8f8c0c0fffff8f8f8f8c0c0fffff8f8f8f8c0c0fffff8f8f8f8c0c0 8 := carry_of (swaps := [(2,4),(3,5)]) (by decide +kernel) low_18
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_12 : Slice r_22 g_22 (identDom 1 3) 8 := by
  have hc : Lower (varsOf 55) 0xfffffcfcececc0c0fffffcfcececc0c0fffffcfcececc0c0fffffcfcececc0c0 8 := carry_of (swaps := [(1,3),(2,3),(3,5),(4,5)]) (by decide +kernel) low_19
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_13 : Slice r_22 g_22 (identDom 1 2) 8 := by
  have hc : Lower (varsOf 59) 0xffffffcceecccc00ffffffcceecccc00ffffffcceecccc00ffffffcceecccc00 8 := carry_of (swaps := [(1,3),(2,5),(4,5)]) (by decide +kernel) low_19
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_14 : Slice r_22 g_22 (subcubeFast 16 0) 7 := by
  have hc : Lower (varsOf 47) 0xfff8fff8c000c000fff8fff8c000c000fff8fff8c000c000fff8fff8c000c000 7 := carry_of (swaps := [(4,5)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_15 : Slice r_22 g_22 (identDom 2 4) 8 := by
  have hc : Lower (varsOf 47) 0xfff8fff8f0e0f0e0fff8fff8f0e0f0e0fff8fff8f0e0f0e0fff8fff8f0e0f0e0 8 := carry_of (swaps := [(2,4),(3,4),(4,5)]) (by decide +kernel) low_21
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_16 : Slice r_22 g_22 (identDom 3 4) 8 := by
  have hc : Lower (varsOf 47) 0xfff8fff8fe00fe00fff8fff8fe00fe00fff8fff8fe00fe00fff8fff8fe00fe00 8 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_21
  exact slice_ident (u := 3) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_17 : Slice r_22 g_22 (subcubeFast 40 16) 4 := by
  exact slice_fast_direct_f (z := 40) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_22_18 : Slice r_22 g_22 (subcubeFast 36 16) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 36) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_19 : Slice r_22 g_22 (subcubeFast 34 16) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 34) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_20 : Slice r_22 g_22 (subcubeFast 12 2) 4 := by
  have hc : Lower (varsOf 49) 0xffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000 4 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_21 : Slice r_22 g_22 (subcubeFast 33 8) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_22 : Slice r_22 g_22 (subcubeFast 33 4) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_23 : Slice r_22 g_22 (subcubeFast 33 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_24 : Slice r_22 g_22 (subcubeFast 17 2) 4 := by
  have hc : Lower (varsOf 44) 0xfff0fff0f000f000fff0fff0f000f000fff0fff0f000f000fff0fff0f000f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_25 : Slice r_22 g_22 (subcubeFast 10 1) 4 := by
  have hc : Lower (varsOf 52) 0xfffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 10) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_26 : Slice r_22 g_22 (subcubeFast 6 1) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000ffffff00ff000000ffffff00ff000000ffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 1) (by decide +kernel) hc
def S_22 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 1 0,9),some (subcubeFast 32 0,9),some (subcubeFast 0 1,9),some (subcubeFast 0 2,8),some (subcubeFast 0 16,8),some (subcubeFast 4 0,8),some (subcubeFast 8 0,8),some (subcubeFast 32 16,7),some (subcubeFast 1 2,7),some (subcubeFast 2 0,8),some (identDom 1 5,9),some (identDom 2 3,8),some (identDom 1 3,8),some (identDom 1 2,8),some (subcubeFast 16 0,7),some (identDom 2 4,8),some (identDom 3 4,8),some (subcubeFast 40 16,4),some (subcubeFast 36 16,4),some (subcubeFast 34 16,4),some (subcubeFast 12 2,4),some (subcubeFast 33 8,4),some (subcubeFast 33 4,4),some (subcubeFast 33 2,4),some (subcubeFast 17 2,4),some (subcubeFast 10 1,4),some (subcubeFast 6 1,4)]
lemma S_22_ok : btAll (fun o => ∀ p, o = some p → Slice r_22 g_22 p.1 p.2) S_22 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (forall_cons (fun _ h => by cases h; exact sl_22_4) (forall_cons (fun _ h => by cases h; exact sl_22_5) (forall_cons (fun _ h => by cases h; exact sl_22_6) (forall_cons (fun _ h => by cases h; exact sl_22_7) (forall_cons (fun _ h => by cases h; exact sl_22_8) (forall_cons (fun _ h => by cases h; exact sl_22_9) (forall_cons (fun _ h => by cases h; exact sl_22_10) (forall_cons (fun _ h => by cases h; exact sl_22_11) (forall_cons (fun _ h => by cases h; exact sl_22_12) (forall_cons (fun _ h => by cases h; exact sl_22_13) (forall_cons (fun _ h => by cases h; exact sl_22_14) (forall_cons (fun _ h => by cases h; exact sl_22_15) (forall_cons (fun _ h => by cases h; exact sl_22_16) (forall_cons (fun _ h => by cases h; exact sl_22_17) (forall_cons (fun _ h => by cases h; exact sl_22_18) (forall_cons (fun _ h => by cases h; exact sl_22_19) (forall_cons (fun _ h => by cases h; exact sl_22_20) (forall_cons (fun _ h => by cases h; exact sl_22_21) (forall_cons (fun _ h => by cases h; exact sl_22_22) (forall_cons (fun _ h => by cases h; exact sl_22_23) (forall_cons (fun _ h => by cases h; exact sl_22_24) (forall_cons (fun _ h => by cases h; exact sl_22_25) (forall_cons (fun _ h => by cases h; exact sl_22_26) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))
def ps_22 : BT (Option PoolSpec) := btOfList 12 ((([(2,[(0,2,3),(1,2,3),(1,4,5),(3,6,7),(1,8,9)]),(0,[(0,2,3),(1,2,3),(1,4,5),(3,6,7),(1,8,9)]),(20,[]),(7,[(0,2,3),(1,2,3),(3,9,34)]),(0,[(0,1,4),(1,1,4),(3,16,17)]),(6,[(0,1,4),(1,1,4),(3,16,17)]),(5,[(0,1,4),(1,1,4),(3,16,17)]),(19,[]),(5,[]),(0,[(0,1,4),(1,1,4),(3,16,17),(2,18,3),(3,18,3),(1,20,51)]),(2,[(0,1,4),(1,1,4),(3,16,17),(2,18,3),(3,18,3),(1,20,51)]),(3,[(2,18,3),(3,18,3),(1,20,51)]),(1,[(0,1,4),(1,1,4),(3,16,17),(2,18,3),(3,18,3),(1,20,51)]),(7,[(2,18,3),(3,18,3),(1,20,51)]),(11,[(0,1,4),(1,1,4),(3,16,17)]),(7,[(0,2,3),(2,18,9),(1,2,3)]),(21,[]),(5,[(3,6,4)]),(14,[(0,2,3),(1,2,3)]),(0,[(0,2,3),(1,2,3),(0,6,4),(1,6,4),(3,72,73)]),(2,[(0,2,3),(1,2,3),(0,6,4),(1,6,4),(3,72,73)]),(1,[(0,2,3),(1,2,3),(0,6,4),(1,6,4),(3,72,73)]),(7,[(0,2,3),(1,2,3)]),(0,[(0,2,3),(1,2,3),(0,6,4),(1,6,4),(3,9,73)]),(2,[(0,2,3),(1,2,3),(0,6,4),(1,6,4),(3,9,73)]),(17,[]),(14,[(0,2,3),(1,2,3),(3,9,73)]),(11,[(3,1,6),(3,25,4),(1,26,5)]),(7,[(0,2,3),(1,2,3),(3,1,6)]),(8,[(0,2,3),(1,2,3)]),(1,[(0,2,3),(1,2,3),(0,1,6),(1,1,6),(3,9,76)]),(1,[(0,2,3),(1,2,3)]),(11,[(0,1,6),(3,32,4),(1,4,5)]),(0,[(0,2,3),(1,2,3)]),(2,[(0,2,3),(1,2,3)]),(11,[(0,1,6),(3,32,4),(1,45,5)]),(7,[(0,2,3),(1,2,3),(0,1,6)]),(0,[(0,2,3),(1,9,5),(1,2,3),(1,4,5),(0,6,7)]),(2,[(0,2,3),(1,9,5),(1,2,3),(1,4,5),(0,6,7)]),(4,[(0,2,3),(1,9,5),(1,2,3)]),(3,[(0,2,3),(1,9,5),(1,2,3)]),(7,[(2,1,62),(1,85,3)]),(18,[]),(6,[]),(0,[(0,1,3),(1,1,3),(0,2,4),(1,89,83),(1,2,4)]),(2,[(0,1,3),(1,1,3),(0,2,4),(1,89,83),(1,2,4)]),(3,[(0,2,4),(1,89,83),(1,2,4)]),(4,[(0,1,3),(1,1,3),(1,89,83)]),(1,[(0,1,3),(1,1,3),(0,2,4),(1,89,83),(1,2,4)]),(7,[(0,1,3),(1,1,3),(1,89,83)]),(9,[]),(14,[]),(7,[(0,1,3),(1,1,3),(1,89,95)]),(14,[(0,1,3),(1,1,3)]),(4,[(1,16,5),(0,2,3),(1,9,5),(1,2,3)]),(9,[(0,2,3),(1,9,5),(1,2,3)]),(0,[(0,1,4),(1,1,4),(0,2,3),(1,16,9),(1,2,3)]),(2,[(0,1,4),(1,1,4),(0,2,3),(1,16,9),(1,2,3)]),(3,[(0,2,3),(1,16,9),(1,2,3)]),(9,[(0,2,3),(1,2,3)]),(11,[(0,1,4),(1,1,4),(1,16,9)]),(1,[(0,1,4),(1,1,4),(0,2,3),(1,16,9),(1,2,3)]),(7,[(0,2,3),(1,16,9),(1,2,3)]),(7,[]),(0,[(0,2,3),(1,2,3),(2,6,4),(3,6,4),(1,69,9)]),(4,[(0,2,3),(1,2,3),(1,69,9)]),(2,[(0,2,3),(1,2,3),(2,6,4),(3,6,4),(1,69,9)]),(1,[(0,2,3),(1,2,3),(2,6,4),(3,6,4),(1,69,9)]),(7,[(0,2,3),(1,2,3),(1,69,9)]),(9,[(1,2,3),(1,6,5),(0,4,34)]),(24,[]),(11,[(1,6,5)]),(6,[(0,1,4),(1,16,5)]),(5,[(0,1,4),(1,16,5)]),(7,[(2,1,84),(1,102,3)]),(0,[(0,1,4),(1,1,4),(3,16,17),(2,18,3),(3,18,3)]),(2,[(0,1,4),(1,1,4),(3,16,17),(2,18,3),(3,18,3)]),(12,[]),(1,[(0,1,4),(1,1,4),(3,16,17),(2,18,3),(3,18,3)]),(7,[(2,18,3),(3,18,3)]),(25,[]),(4,[(1,16,5),(0,2,3),(1,9,47),(1,2,3)]),(7,[(0,2,3),(1,9,47),(1,2,3)]),(11,[]),(4,[(0,1,2),(1,107,5)]),(3,[(0,2,3),(1,2,3),(1,26,9)]),(0,[(0,1,4),(1,1,4),(3,16,17),(0,18,2),(1,18,2)]),(2,[(0,1,4),(1,1,4),(3,16,17),(0,18,2),(1,18,2)]),(13,[]),(0,[]),(1,[(0,1,4),(0,2,3),(1,2,3),(3,9,34)]),(13,[(3,3,4),(1,105,5),(1,3,5)]),(1,[(0,1,2),(1,1,2)]),(14,[(0,1,2),(1,1,2)]),(4,[(0,2,3),(1,2,3),(1,8,9)]),(1,[(0,2,3),(1,2,3),(3,6,7),(1,8,9)]),(7,[(2,18,3),(1,2,3)]),(1,[(0,2,3),(1,2,3),(3,9,34),(3,35,4)]),(0,[(0,1,4),(1,1,4),(3,16,17),(0,2,3),(1,2,3)]),(2,[(0,1,4),(1,1,4),(3,16,17),(0,2,3),(1,2,3)]),(1,[(0,1,4),(1,1,4),(3,16,17),(0,2,3),(1,2,3)]),(11,[(0,1,4),(1,16,5),(1,6,5)]),(4,[(0,1,2),(1,107,106)]),(22,[]),(4,[(0,2,3),(1,2,3),(3,1,6)]),(11,[(3,1,6),(1,4,5),(3,25,7)]),(2,[(0,1,4),(1,1,4),(3,16,17)]),(7,[(2,18,3),(1,20,2)]),(7,[(2,18,3),(3,2,3)]),(11,[(0,1,6),(1,32,5),(1,4,5)]),(1,[(0,1,4),(1,1,4),(3,16,17)]),(7,[(2,18,3),(2,20,2)]),(0,[(0,1,4),(1,1,4),(3,16,17),(3,18,3),(3,51,2)]),(2,[(0,1,4),(1,1,4),(3,16,17),(3,18,3),(3,51,2)]),(1,[(0,1,4),(1,1,4),(3,16,17),(3,18,3),(3,51,2)]),(7,[(3,18,3),(3,51,2)]),(4,[(0,2,3),(1,2,3),(0,1,6)]),(11,[(0,1,6),(1,4,5),(3,32,7)]),(0,[(0,1,4),(1,1,4),(3,16,17),(3,18,2),(1,148,3)]),(2,[(0,1,4),(1,1,4),(3,16,17),(3,18,2),(1,148,3)]),(11,[(3,1,6),(3,25,4),(1,4,5)]),(7,[(0,2,3),(2,18,9)]),(1,[(0,2,3),(1,2,3),(3,9,34)]),(7,[(2,3,2),(3,55,18)]),(3,[(0,2,3),(1,2,3),(1,9,153)]),(4,[(1,1,5),(0,2,3),(1,2,3),(1,9,153)]),(7,[(0,2,3),(1,2,3),(1,9,153)]),(0,[(0,2,3),(1,2,3),(2,1,6),(1,155,9),(3,1,6)]),(2,[(0,2,3),(1,2,3),(2,1,6),(1,155,9),(3,1,6)]),(3,[(0,2,3),(1,2,3),(1,155,9)]),(1,[(0,2,3),(1,2,3),(2,1,6),(1,155,9),(3,1,6)]),(11,[(0,1,4),(1,6,5),(3,16,34)]),(4,[(1,157,5),(0,2,3),(1,9,5),(1,2,3)]),(3,[(0,18,3),(3,19,18)]),(0,[(0,2,3),(1,9,5),(1,2,3),(0,1,6),(1,32,5)]),(2,[(0,2,3),(1,9,5),(1,2,3),(1,4,5)]),(0,[(0,2,3),(1,9,5),(1,2,3),(1,4,5)]),(2,[]),(4,[]),(3,[]),(2,[(0,3,4),(1,126,5)]),(3,[(0,3,4),(1,126,5)]),(1,[(0,3,4)]),(5,[(0,3,4),(1,126,5)]),(7,[(2,2,127)]),(5,[(1,3,5)]),(7,[(2,1,62)]),(0,[(2,2,3),(1,4,5),(3,3,7),(1,162,2)]),(2,[(2,2,3),(1,4,5),(3,3,7),(1,162,2)]),(5,[(1,4,5),(3,3,7)]),(3,[(2,3,2),(1,3,5)]),(7,[(1,2,3),(0,1,34)]),(3,[(1,2,3),(1,6,5)]),(0,[(1,2,3),(0,6,4),(1,6,4),(3,72,73)]),(2,[(1,2,3),(0,6,4),(1,6,4),(3,72,73)]),(1,[(1,2,3),(0,6,4),(1,6,4),(3,72,73)]),(7,[(1,2,3)]),(4,[(1,2,3),(3,1,6)]),(5,[(1,6,5)]),(7,[(1,2,3),(3,1,6)]),(7,[(1,3,2),(3,1,6)]),(5,[(3,1,6),(3,25,4)]),(1,[(1,2,3),(0,6,4)]),(2,[(1,2,3),(1,6,5),(0,4,34)]),(0,[(1,2,3),(1,6,5),(0,4,34)]),(7,[(1,2,3),(0,1,6)]),(3,[(1,2,3)]),(9,[(1,2,3)]),(14,[(1,2,3)]),(4,[(1,3,5)]),(7,[(1,3,2),(0,1,6)]),(5,[(0,1,6),(3,32,4)]),(5,[(1,6,5),(0,4,34)]),(0,[(0,2,3),(1,2,3),(1,6,5),(0,4,34)]),(3,[(0,2,3),(1,2,3)]),(11,[(1,6,5),(0,4,34)]),(0,[(0,2,3),(1,2,3),(1,6,5),(3,9,34)]),(2,[(0,2,3),(1,2,3),(1,6,5),(3,9,34)]),(0,[(0,2,3),(1,2,3),(3,6,4),(1,69,9)]),(2,[(0,2,3),(1,2,3),(3,6,4),(1,69,9)]),(1,[(0,2,3),(1,2,3),(3,6,4),(1,69,9)]),(0,[(0,2,3),(1,2,3),(1,6,4),(3,9,73)]),(2,[(0,2,3),(1,2,3),(1,6,4),(3,9,73)]),(0,[(0,2,3),(1,2,3),(0,6,4),(1,6,4)]),(2,[(0,2,3),(1,2,3),(0,6,4),(1,6,4)]),(5,[(0,6,4),(1,6,4)]),(4,[(0,2,3),(1,2,3)]),(5,[(0,6,4),(1,72,5)]),(2,[(0,2,3),(1,2,3),(0,6,4),(1,72,5)]),(11,[(0,6,4),(1,72,5)]),(1,[(0,2,3),(1,2,3),(0,6,4)]),(0,[(1,3,5),(0,1,62),(1,1,62),(3,63,64)]),(2,[(1,3,5),(0,1,62),(1,1,62),(3,63,64)]),(1,[(0,1,62),(1,1,62),(3,63,64)]),(3,[(1,3,5)]),(11,[(3,1,6),(2,4,5)]),(5,[(1,3,5),(2,1,62)]),(1,[(0,2,4),(2,1,62),(1,85,2)]),(0,[(0,2,3),(1,2,3),(3,1,6),(1,25,5)]),(5,[(3,1,6),(1,25,5)]),(11,[(3,1,6),(1,25,5)]),(1,[(0,2,3),(1,2,3),(3,1,6)]),(11,[(3,1,6),(3,25,4)]),(5,[(2,1,6),(3,1,6)]),(0,[(0,2,3),(1,2,3),(2,1,6),(3,1,6)]),(2,[(0,2,3),(1,2,3),(2,1,6),(3,1,6)]),(0,[(0,2,3),(1,2,3),(2,1,6),(1,155,9)]),(2,[(0,2,3),(1,2,3),(2,1,6),(1,155,9)]),(5,[(2,1,6)]),(5,[(1,1,6),(0,76,4)]),(11,[(1,1,6),(0,76,4)]),(0,[(0,2,3),(1,2,3),(0,1,6),(1,1,6)]),(5,[(0,1,6),(1,1,6)]),(2,[(0,2,3),(1,2,3),(0,1,6),(1,1,6)]),(0,[(0,2,3),(1,2,3),(0,1,6),(1,32,5)]),(5,[(0,1,6),(1,32,5)]),(11,[(0,1,6),(1,32,5)]),(1,[(0,2,3),(1,2,3),(0,1,6)]),(0,[(0,2,3),(1,9,5),(1,2,3),(2,6,5)]),(2,[(0,2,3),(1,9,5),(1,2,3),(2,6,5)]),(0,[(0,2,3),(1,9,5),(1,2,3)]),(2,[(0,2,3),(1,9,5),(1,2,3)]),(11,[(1,9,5)]),(0,[(0,2,3),(1,9,5),(1,2,3),(3,1,6)]),(2,[(0,2,3),(1,9,5),(1,2,3),(3,1,6)]),(5,[(3,1,6)]),(0,[(0,2,3),(1,9,5),(1,2,3),(0,1,6)]),(5,[(0,1,6)]),(2,[(0,2,3),(1,9,5),(2,1,29),(1,2,3)]),(7,[(0,2,3),(1,1,29),(1,2,3)]),(1,[(2,2,3),(1,93,3)]),(7,[(2,2,3),(1,93,3)]),(5,[(2,1,5),(3,81,4)]),(0,[(0,2,3),(1,2,3),(3,1,6)]),(2,[(0,2,3),(1,2,3),(3,1,6)]),(11,[(3,1,6),(1,4,5)]),(4,[(2,1,5),(0,2,3),(1,2,3)]),(1,[(3,81,4),(0,2,3),(1,2,3)]),(11,[(2,1,5),(3,81,4)]),(4,[(1,16,5),(0,2,3),(1,9,47)]),(7,[(0,2,3),(1,9,47)]),(1,[(1,3,2),(3,3,34),(3,2,34)]),(0,[(1,3,2),(1,6,5),(3,3,34),(3,2,34)]),(2,[(1,3,2),(1,6,5),(3,3,34),(3,2,34)]),(8,[(1,2,3)]),(0,[(0,2,3),(1,2,3),(1,4,5),(0,6,7)]),(2,[(0,2,3),(1,2,3),(1,4,5),(0,6,7)]),(5,[(1,4,5),(0,6,7)]),(1,[(0,2,3),(1,2,3),(0,6,7)]),(5,[(0,1,4),(1,86,5)]),(4,[(0,1,2),(1,1,2),(1,3,5)]),(1,[(0,1,2),(1,1,2),(3,3,4)]),(13,[(3,3,4),(1,3,5)]),(6,[(0,1,2),(1,1,2)]),(4,[(0,1,2),(1,1,2)]),(7,[(3,1,2)]),(6,[(3,1,2),(1,177,5)]),(2,[(0,2,4),(1,83,3)]),(3,[(0,2,4),(1,83,3)]),(1,[(3,1,3),(0,2,4),(1,83,3)]),(7,[(3,1,3),(1,83,3)]),(4,[(1,16,5),(1,2,5)]),(9,[(2,2,3),(1,2,5)]),(2,[(3,1,2),(1,177,3),(0,3,4),(1,126,5)]),(4,[(1,126,5)]),(1,[(3,1,2),(1,177,3),(0,3,4)]),(7,[(3,1,2),(1,177,3)]),(3,[(1,3,5),(0,4,62)]),(1,[(1,1,2),(0,4,62),(2,38,183)]),(2,[(1,1,3),(0,91,4),(1,117,5)]),(0,[(1,1,3),(0,91,4),(1,117,5)]),(3,[(1,117,5)]),(9,[(0,91,4),(1,117,5)]),(6,[(0,91,4),(1,117,5)]),(1,[(1,1,2)]),(14,[(1,1,2)]),(0,[(0,1,3),(1,1,3),(0,2,4),(1,89,83)]),(2,[(0,1,3),(1,1,3),(0,2,4),(1,89,83)]),(5,[(0,1,3),(1,1,3)]),(3,[(0,2,4),(1,89,83)]),(6,[(0,2,4)]),(1,[(0,1,3),(1,1,3),(0,2,4),(1,89,83)]),(12,[(3,2,4),(1,186,5),(1,2,5)]),(1,[(2,1,3)]),(14,[(2,1,3)]),(5,[(1,3,5),(0,4,62)]),(7,[(2,1,127)]),(0,[(1,1,2),(0,38,4),(1,39,5)]),(2,[(1,1,2),(0,38,4),(1,39,5)]),(4,[(1,1,2),(1,39,5)]),(3,[(1,39,5)]),(9,[(1,2,3),(1,190,5)]),(7,[(1,2,3),(3,16,6)]),(4,[(1,1,3),(1,117,5),(1,2,5)]),(14,[(1,2,5)]),(7,[(1,1,3)]),(4,[(1,2,3),(0,1,6)]),(1,[(1,2,3)]),(7,[(1,2,3),(3,1,34)]),(1,[(3,3,4)]),(5,[(2,38,5)]),(3,[(3,3,4)]),(7,[(1,1,2)]),(26,[]),(7,[(1,1,2),(2,38,127)]),(0,[(0,1,2),(1,1,2),(0,3,4),(1,3,4)]),(5,[(0,3,4),(1,3,4)]),(2,[(0,1,2),(1,1,2),(0,3,4),(1,3,4)]),(13,[(0,3,4),(1,3,4)]),(3,[(0,3,4),(1,3,4)]),(16,[(0,1,2),(1,1,2)]),(7,[(0,1,2),(1,1,2)]),(9,[(1,4,5),(3,3,7)]),(9,[(2,2,47)]),(2,[(0,2,3),(1,2,3),(2,4,5)]),(0,[(0,2,3),(1,2,3),(2,4,5)]),(11,[(0,1,6),(2,4,5)]),(6,[(2,2,195),(1,196,5)]),(7,[(0,1,3),(2,2,195)]),(5,[(0,1,3),(1,89,5)]),(6,[(0,2,4),(1,83,195)]),(7,[(0,1,3),(1,83,195)]),(2,[(0,1,4),(1,16,5)]),(4,[(1,16,5),(0,2,3),(1,9,5)]),(1,[(0,2,3)]),(9,[(0,2,3),(1,9,5)]),(4,[(0,1,2),(1,107,5),(1,105,5)]),(1,[(0,1,2)]),(7,[(0,1,2)]),(5,[(3,3,4),(1,4,5)]),(13,[(3,3,4),(1,4,5)]),(2,[(0,1,2),(1,1,2),(0,3,4),(1,126,5)]),(0,[(0,1,2),(1,1,2)]),(13,[(0,3,4),(1,126,5)]),(1,[(0,1,4)]),(0,[(0,1,4),(1,1,4),(3,16,17),(3,18,2)]),(2,[(0,1,4),(1,1,4),(3,16,17),(3,18,2)]),(3,[(2,3,178),(1,200,5)]),(5,[(2,3,178),(1,200,5)]),(7,[(3,1,2),(1,177,183)]),(7,[(3,1,3),(1,180,84)]),(0,[(1,2,3)]),(2,[(1,2,3)]),(2,[(3,3,4),(1,105,5),(1,3,5)]),(0,[(3,3,4),(1,105,5),(1,3,5)]),(6,[(1,105,5)]),(4,[(1,105,5),(1,3,5)]),(14,[(1,3,5)]),(14,[(0,1,2)]),(1,[]),(1,[(0,1,4),(1,3,2),(3,16,6)]),(0,[(0,2,3),(1,2,3),(1,4,5),(3,6,7)]),(2,[(0,2,3),(1,2,3),(1,4,5),(3,6,7)]),(5,[(1,4,5),(3,6,7)]),(4,[(1,16,5),(2,2,47),(1,115,5)]),(7,[(2,2,47)]),(0,[(0,1,2),(1,1,2),(1,4,5),(0,38,7)]),(5,[(1,4,5),(0,38,7)]),(2,[(0,1,2),(1,1,2),(1,4,5),(0,38,7)]),(1,[(0,1,2),(1,1,2),(0,38,7)]),(3,[(0,2,4),(1,83,181)]),(6,[(0,2,4),(1,83,181)]),(5,[(3,1,3),(1,180,5)]),(7,[(3,1,3),(1,83,181)]),(1,[(1,2,3),(3,3,58)]),(0,[(1,2,3),(1,2,5),(3,3,58),(2,6,5)]),(2,[(1,2,3),(1,2,5),(3,3,58),(2,6,5)]),(4,[(0,1,2),(1,107,5),(1,3,5)]),(6,[(0,1,2),(1,107,5)]),(0,[(0,1,4),(0,2,3),(1,16,9),(1,2,3)]),(2,[(0,1,4),(0,2,3),(1,16,9),(1,2,3)]),(5,[(0,1,4)]),(4,[(0,2,3),(1,16,9),(1,2,3)]),(11,[(0,1,4),(1,16,9)]),(1,[(0,1,4),(0,2,3),(1,16,9),(1,2,3)]),(6,[(0,4,62),(1,2,183)]),(3,[(1,3,5),(0,4,62),(1,2,183)]),(1,[(3,1,2),(0,4,62),(1,2,183)]),(7,[(0,1,3),(1,89,84)]),(0,[(0,1,2),(0,3,4),(1,107,126),(1,3,4)]),(2,[(0,1,2),(0,3,4),(1,107,126),(1,3,4)]),(4,[(0,1,2),(1,107,126)]),(3,[(0,3,4),(1,107,126),(1,3,4)]),(6,[(0,1,2)]),(9,[(0,3,4),(1,3,4)]),(1,[(0,1,2),(0,3,4),(1,107,126),(1,3,4)]),(7,[(0,1,2),(1,107,126)]),(9,[(1,2,5),(1,3,58)]),(3,[(1,16,5),(1,2,5)]),(1,[(0,1,3)]),(4,[(0,1,3),(1,89,5),(1,2,5)]),(7,[(0,1,3)]),(5,[(0,4,58)]),(5,[(3,3,4),(1,105,5)]),(2,[(0,1,2),(1,1,2)]),(13,[(3,3,4),(1,105,5)]),(3,[(3,3,4),(1,105,5)]),(4,[(0,1,2),(1,1,2),(1,105,5)]),(7,[(2,1,62),(1,85,2)]),(6,[(1,93,5)]),(4,[(2,1,3)]),(12,[(3,2,4),(1,4,5),(3,186,7)]),(5,[(2,6,4),(3,6,4)]),(14,[(3,3,7)]),(4,[(0,1,2)]),(1,[(0,1,2),(3,107,4),(3,3,7)]),(7,[(0,1,2),(1,107,183)]),(13,[(1,3,5),(2,4,62)]),(13,[(1,3,5),(0,4,62)]),(0,[(1,1,5),(0,2,3),(1,9,5),(1,2,3)]),(2,[(1,1,5),(0,2,3),(1,9,5),(1,2,3)]),(4,[(1,126,5),(2,1,127)]),(5,[(3,1,4),(1,157,5)]),(4,[(1,157,5),(0,2,3),(1,2,3)]),(11,[(3,1,4),(1,157,5)]),(1,[(3,1,4),(0,2,3),(1,2,3)]),(3,[(1,4,5),(3,3,7)]),(1,[(0,1,2),(1,1,2),(3,3,7)]),(13,[(1,4,5),(3,3,7)]),(0,[(3,3,4),(1,105,2),(1,2,5),(3,3,58)]),(2,[(3,3,4),(1,105,2),(1,2,5),(3,3,58)]),(2,[(3,3,4),(1,4,5),(3,105,7)]),(0,[(3,3,4),(1,4,5),(3,105,7)]),(1,[(1,1,2),(0,38,4)]),(11,[(0,1,4),(1,6,5)]),(1,[(1,2,3),(3,1,6),(3,25,4)]),(0,[(1,2,3),(0,1,6),(3,6,4),(1,69,32)]),(1,[(0,1,2),(3,3,4)]),(6,[(1,6,5)]),(5,[(2,1,3)]),(7,[(2,1,3),(1,185,2)]),(4,[(1,16,5)]),(3,[(1,16,5)]),(2,[(0,1,4),(1,16,5),(0,2,3),(1,2,3)]),(4,[(1,16,5),(0,2,3),(1,2,3)]),(1,[(0,1,4),(0,2,3),(1,2,3)]),(11,[(0,1,4),(1,16,5)]),(4,[(1,16,5),(1,3,2),(1,3,5)]),(9,[(1,3,2),(1,3,5)]),(1,[(0,1,4),(1,2,3)]),(3,[(1,3,5),(1,85,3)]),(9,[(1,3,5)]),(9,[(0,2,4)]),(1,[(0,1,4),(2,2,3),(1,93,47)]),(9,[(1,3,47)]),(9,[(3,3,4)]),(7,[(2,1,58),(1,124,2)]),(7,[(2,1,127),(1,189,2)]),(2,[(0,2,3),(1,2,3),(1,4,5)]),(0,[(0,2,3),(1,2,3),(1,4,5)]),(0,[(0,2,3),(1,2,3),(0,1,6)]),(2,[(0,2,3),(1,2,3),(0,1,6)]),(11,[(0,1,6),(1,4,5)]),(4,[(1,16,5),(1,2,3),(1,6,5)]),(9,[(1,2,3),(1,6,5)]),(11,[(0,1,6),(3,32,4)]),(7,[(1,1,2),(2,1,127)]),(7,[(2,2,3)]),(0,[(0,1,4),(1,1,4),(3,16,17),(2,2,3)]),(2,[(0,1,4),(1,1,4),(3,16,17),(2,2,3)]),(0,[(0,1,4),(1,16,5)]),(3,[(1,16,5),(1,3,5)]),(9,[(2,2,3)]),(2,[(0,1,4),(1,16,3)]),(1,[(0,1,4),(1,16,3),(2,3,2)]),(7,[(1,16,3),(2,3,2)]),(6,[(0,1,4)]),(9,[(1,3,5),(2,2,62)]),(4,[(1,16,5),(1,3,47)]),(4,[(1,16,5),(1,2,47)]),(4,[(1,16,5),(2,2,3),(1,93,5)]),(1,[(0,1,4),(2,2,3)]),(0,[(0,1,4),(1,1,4),(3,16,17),(2,18,3)]),(2,[(0,1,4),(1,1,4),(3,16,17),(2,18,3)]),(7,[(2,18,3)]),(4,[(1,16,5),(2,2,47)]),(2,[(0,1,4),(1,16,2)]),(1,[(0,1,4),(1,16,2),(3,3,58)]),(7,[(1,16,2),(3,3,58)]),(7,[(0,18,2)]),(0,[(0,1,4),(1,1,4),(3,16,17),(0,18,2)]),(2,[(0,1,4),(1,1,4),(3,16,17),(0,18,2)]),(0,[(0,1,4),(1,1,4),(3,16,17),(1,18,2)]),(2,[(0,1,4),(1,1,4),(3,16,17),(1,18,2)]),(0,[(0,1,4),(1,1,4),(3,16,17),(0,2,3)]),(2,[(0,1,4),(1,1,4),(3,16,17),(0,2,3)]),(1,[(0,1,4),(1,1,4),(3,16,17),(0,2,3)]),(7,[(0,2,3)]),(0,[(0,1,4),(1,1,4),(3,16,17),(1,2,3)]),(2,[(0,1,4),(1,1,4),(3,16,17),(1,2,3)]),(1,[(0,1,4),(1,1,4),(3,16,17),(1,2,3)]),(0,[(0,1,4),(1,1,4),(0,2,3),(1,16,9)]),(2,[(0,1,4),(1,1,4),(0,2,3),(1,16,9)]),(3,[(0,2,3),(1,16,9)]),(5,[(0,1,4),(1,1,4)]),(6,[(0,1,4),(1,1,4)]),(1,[(0,1,4),(1,1,4),(0,2,3),(1,16,9)]),(7,[(0,2,3),(1,16,9)]),(0,[(0,1,4),(1,1,4),(0,2,3),(1,2,3)]),(2,[(0,1,4),(1,1,4),(0,2,3),(1,2,3)]),(11,[(0,1,4),(1,1,4)]),(1,[(3,1,2)]),(14,[(3,1,2)]),(1,[(0,1,4),(1,2,3),(3,16,34)]),(1,[(0,1,4),(2,2,62),(1,142,16)]),(1,[(0,1,4),(1,3,58),(3,16,34)]),(0,[(1,2,5),(0,3,58),(1,3,58),(3,59,34)]),(2,[(1,2,5),(0,3,58),(1,3,58),(3,59,34)]),(6,[(1,2,5)]),(1,[(0,3,58),(1,3,58),(3,59,34)]),(1,[(0,1,4),(2,2,3),(1,93,16)]),(0,[(2,1,4),(3,1,4),(0,2,3),(1,2,3)]),(5,[(2,1,4),(3,1,4)]),(2,[(2,1,4),(3,1,4),(0,2,3),(1,2,3)]),(11,[(2,1,4),(3,1,4)]),(4,[(1,2,5)]),(2,[(2,2,3),(1,2,5),(2,1,58),(1,124,93)]),(3,[(0,2,3),(1,9,153)]),(4,[(1,1,5),(0,2,3),(1,9,153)]),(5,[(1,1,5),(0,4,152)]),(6,[(1,1,5),(0,4,152)]),(1,[(0,2,3),(0,4,152),(1,9,153)]),(3,[(0,2,3),(1,9,5)]),(4,[(1,157,5),(0,2,3),(1,9,5)]),(1,[(0,2,3),(1,2,3),(0,4,152)]),(4,[(1,1,5),(0,2,3),(1,2,3)]),(11,[(1,1,5),(0,4,152)]),(3,[(2,2,3),(1,93,153)]),(1,[(2,2,3),(0,4,152),(1,93,153)]),(0,[(0,1,2),(1,1,2),(2,3,4),(3,232,38)]),(5,[(2,3,4),(3,232,38)]),(2,[(0,1,2),(1,1,2),(2,3,4),(3,232,38)]),(3,[(2,3,4)]),(1,[(0,1,2),(1,1,2),(2,3,4),(3,232,38)]),(2,[(1,1,5),(0,4,152),(1,2,153)]),(3,[(2,2,3),(1,2,153)]),(7,[(2,2,3),(1,2,153)]),(2,[(1,3,5),(0,4,62),(1,2,183)]),(0,[(1,3,5)]),(0,[(1,3,5),(0,4,62),(1,2,183)]),(0,[(1,3,5),(2,2,62),(3,2,62)]),(2,[(1,3,5),(2,2,62),(3,2,62)]),(1,[(2,2,62),(3,2,62)]),(0,[(1,3,5),(2,2,62),(1,142,3)]),(2,[(1,3,5),(2,2,62),(1,142,3)]),(7,[(2,2,62),(1,142,3)]),(1,[(2,2,62),(1,142,3)]),(0,[(1,3,5),(0,2,62),(1,2,62)]),(2,[(1,3,5),(0,2,62),(1,2,62)]),(6,[(0,2,62),(1,2,62)]),(1,[(0,2,62),(1,2,62)]),(0,[(1,2,5),(1,3,58)]),(2,[(1,2,5),(1,3,58)]),(3,[(1,2,5),(1,3,58)]),(1,[(1,3,58)]),(5,[(1,3,58)]),(4,[(1,2,5),(1,3,58)]),(0,[(1,3,5),(2,1,62),(1,85,3)]),(2,[(1,3,5),(2,1,62),(1,85,3)]),(0,[(1,2,5)]),(2,[(1,2,5)]),(0,[(1,2,5),(1,1,58),(0,4,135)]),(2,[(1,2,5),(1,1,58),(0,4,135)]),(3,[(1,2,5)]),(1,[(1,1,58),(0,4,135)]),(0,[(1,2,5),(1,3,58),(0,4,34)]),(2,[(1,2,5),(1,3,58),(0,4,34)]),(9,[(1,2,5)]),(7,[(1,3,58)]),(1,[(1,1,58),(3,3,135)]),(0,[(1,2,5),(1,1,58),(3,3,135)]),(2,[(1,2,5),(1,1,58),(3,3,135)]),(7,[(1,1,58),(3,3,135)]),(0,[(1,2,5),(1,1,58)]),(2,[(1,2,5),(1,1,58)]),(3,[(1,2,5),(3,3,58)]),(1,[(1,1,58),(3,3,58)]),(5,[(1,1,58)]),(0,[(1,2,5),(3,3,58)]),(2,[(1,2,5),(3,3,58)]),(2,[(1,3,5)]),(0,[(1,3,5),(0,1,62),(1,63,2)]),(2,[(1,3,5),(0,1,62),(1,63,2)]),(1,[(0,1,62),(1,63,2)]),(7,[(0,1,62),(1,63,2)]),(6,[(2,1,62)]),(1,[(3,2,4),(2,1,62)]),(0,[(3,3,4),(1,105,2),(2,215,5)]),(2,[(3,3,4),(1,105,2),(2,215,5)]),(5,[(3,3,4),(2,215,5)]),(0,[(3,3,4),(1,105,2),(1,215,5)]),(2,[(3,3,4),(1,105,2),(1,215,5)]),(5,[(3,3,4),(1,215,5)]),(6,[(1,105,2),(1,215,5)]),(0,[(3,2,4),(1,186,3),(1,3,5)]),(2,[(3,2,4),(1,186,3),(1,3,5)]),(5,[(1,186,3),(1,3,5)]),(0,[(3,3,4),(1,105,2)]),(2,[(3,3,4),(1,105,2)]),(0,[(3,3,4),(1,105,2),(0,1,215)]),(2,[(3,3,4),(1,105,2),(0,1,215)]),(9,[(3,3,4),(1,105,2)]),(3,[(3,3,4),(1,105,2)]),(14,[(2,244,3)]),(0,[(3,2,4)]),(2,[(3,2,4)]),(3,[(3,2,4)]),(15,[(2,244,3)]),(0,[(0,3,4),(1,126,5)]),(9,[(0,3,4),(1,126,5)]),(6,[(2,2,127)]),(2,[(0,3,4),(1,126,5),(2,2,127)]),(0,[(0,3,4),(1,126,5),(2,2,127)]),(0,[(0,2,4),(1,83,5),(1,3,5)]),(2,[(0,2,4),(1,83,5),(1,3,5)]),(6,[(0,2,4),(1,83,5)]),(2,[(0,2,4),(1,83,5),(1,1,84)]),(0,[(0,2,4),(1,83,5),(1,1,84)]),(3,[(0,2,4),(1,83,5)]),(7,[(1,1,84)]),(0,[(0,2,4),(1,83,3),(1,3,5)]),(2,[(0,2,4),(1,83,3),(1,3,5)]),(7,[(1,83,3)]),(0,[(2,3,2),(1,4,5),(3,55,7)]),(2,[(2,3,2),(1,4,5),(3,55,7)]),(5,[(1,4,5),(3,55,7)]),(0,[(1,3,5),(0,4,62)]),(2,[(1,3,5),(0,4,62)]),(9,[(1,3,5),(0,4,62)]),(6,[(0,4,62)]),(15,[]),(14,[(2,2,3)]),(1,[(2,2,3),(0,4,62)]),(2,[(2,2,3)]),(0,[(2,2,3)]),(3,[(2,2,3)]),(0,[(2,2,3),(3,3,4),(1,105,2)]),(2,[(2,2,3),(3,3,4),(1,105,2)]),(5,[(3,3,4)]),(9,[(2,3,2),(1,3,5)]),(2,[(2,3,2),(1,3,5)]),(0,[(2,3,2),(1,3,5)]),(4,[(2,3,2),(1,3,5)]),(0,[(2,2,3),(1,93,5),(1,3,5)]),(2,[(2,2,3),(1,93,5),(1,3,5)]),(0,[(2,3,2),(1,55,5)]),(2,[(2,3,2),(1,55,5)]),(9,[(2,3,2),(1,55,5)]),(6,[(2,1,139)]),(4,[(2,3,2),(1,55,5)]),(0,[(2,2,3),(1,93,5),(1,1,207)]),(2,[(2,2,3),(1,93,5),(1,1,207)]),(3,[(2,2,3),(1,93,5)]),(0,[(2,3,2),(3,55,4),(1,4,5)]),(2,[(2,3,2),(3,55,4),(1,4,5)]),(4,[(2,3,2)]),(5,[(3,55,4),(1,4,5)]),(6,[(1,4,5)]),(1,[(2,3,2),(3,55,4)]),(0,[(1,2,5),(2,3,58),(3,251,4)]),(2,[(1,2,5),(2,3,58),(3,251,4)]),(1,[(2,3,58),(3,251,4)]),(0,[(2,2,3),(1,3,5),(3,2,62)]),(2,[(2,2,3),(1,3,5),(3,2,62)]),(0,[(2,3,2),(3,55,4),(1,250,5)]),(2,[(2,3,2),(3,55,4),(1,250,5)]),(5,[(3,55,4),(1,250,5)]),(6,[(1,250,5)]),(7,[(2,3,2)]),(0,[(2,2,3),(1,93,3)]),(2,[(2,2,3),(1,93,3)]),(9,[(2,2,3),(1,93,3)]),(3,[(2,2,3),(1,93,3)]),(5,[(2,4,5)]),(6,[(2,4,5)]),(9,[(2,4,5)]),(3,[(2,4,5)]),(0,[(0,2,4),(1,83,5),(3,3,84)]),(2,[(0,2,4),(1,83,5),(3,3,84)]),(0,[(2,2,3),(1,93,3),(2,6,5)]),(2,[(2,2,3),(1,93,3),(2,6,5)]),(0,[(2,3,2),(1,55,2),(1,3,5)]),(2,[(2,3,2),(1,55,2),(1,3,5)]),(7,[(2,3,2),(1,55,2)]),(1,[(2,3,2),(1,55,2)]),(0,[(1,2,3),(1,4,5),(0,6,7)]),(2,[(1,2,3),(1,4,5),(0,6,7)]),(1,[(1,2,3),(0,6,7)]),(4,[(1,2,3)]),(0,[(1,4,5),(3,3,7),(1,162,2)]),(2,[(1,4,5),(3,3,7),(1,162,2)]),(6,[(1,4,5),(1,162,2)]),(6,[(1,6,5),(0,4,34)]),(0,[(1,3,2),(1,6,5),(3,3,34)]),(2,[(1,3,2),(1,6,5),(3,3,34)]),(0,[(1,3,2),(1,6,5)]),(1,[(1,3,2),(3,3,34)]),(0,[(1,2,3),(1,6,5)]),(2,[(1,2,3),(1,6,5)]),(4,[(1,2,3),(1,6,5)]),(1,[(1,2,3),(3,1,34)]),(0,[(1,2,3),(1,6,5),(3,1,34)]),(2,[(1,2,3),(1,6,5),(3,1,34)]),(0,[(1,2,3),(3,6,4),(1,69,5)]),(2,[(1,2,3),(3,6,4),(1,69,5)]),(5,[(3,6,4),(1,69,5)]),(6,[(3,6,4),(1,69,5)]),(0,[(1,2,3),(3,6,4),(1,69,2)]),(2,[(1,2,3),(3,6,4),(1,69,2)]),(0,[(1,2,3),(0,6,4)]),(2,[(1,2,3),(0,6,4)]),(9,[(1,2,3),(0,6,4)]),(3,[(1,2,3),(0,6,4)]),(0,[(1,2,3),(0,6,4),(1,72,5)]),(2,[(1,2,3),(0,6,4),(1,72,5)]),(0,[(3,2,4),(1,186,5),(3,3,187)]),(2,[(3,2,4),(1,186,5),(3,3,187)]),(7,[(3,3,187)]),(5,[(1,186,5),(3,3,187)]),(1,[(3,3,4),(1,1,58)]),(0,[(0,2,4),(2,3,5),(1,257,83)]),(2,[(0,2,4),(2,3,5),(1,257,83)]),(7,[(1,257,83)]),(0,[(1,2,5),(0,4,58)]),(2,[(1,2,5),(0,4,58)]),(9,[(1,2,5),(0,4,58)]),(3,[(1,2,5),(0,4,58)]),(0,[(1,2,3),(1,2,5),(2,6,5)]),(2,[(1,2,3),(1,2,5),(2,6,5)]),(5,[(0,6,4)]),(6,[(0,6,4)]),(0,[(1,2,3),(1,2,5),(3,3,58)]),(2,[(1,2,3),(1,2,5),(3,3,58)]),(0,[(2,3,2),(1,3,5),(3,55,62)]),(2,[(2,3,2),(1,3,5),(3,55,62)]),(5,[(1,3,5),(3,55,62)]),(0,[(1,3,2),(1,3,5)]),(2,[(1,3,2),(1,3,5)]),(3,[(1,3,2),(1,3,5)]),(7,[(1,3,2)]),(0,[(1,3,2),(1,3,5),(2,6,5)]),(2,[(1,3,2),(1,3,5),(2,6,5)]),(9,[(1,4,5)]),(0,[(1,2,3),(3,1,6)]),(2,[(1,2,3),(3,1,6)]),(3,[(1,4,5)]),(4,[(1,3,2),(1,3,5)]),(1,[(1,3,2),(3,1,6)]),(0,[(1,3,2),(3,1,6),(1,3,5)]),(2,[(1,3,2),(3,1,6),(1,3,5)]),(0,[(2,3,2),(3,55,4),(1,2,4)]),(2,[(2,3,2),(3,55,4),(1,2,4)]),(5,[(3,55,4)]),(6,[(1,2,4)]),(1,[(2,3,2),(3,55,4),(1,2,4)]),(0,[(1,2,3),(1,1,6),(0,76,4)]),(2,[(1,2,3),(1,1,6),(0,76,4)]),(6,[(1,1,6),(0,76,4)]),(2,[(1,3,5),(2,1,62),(1,85,2)]),(0,[(1,3,5),(2,1,62),(1,85,2)]),(0,[(1,2,3),(0,1,6)]),(2,[(1,2,3),(0,1,6)]),(9,[(1,2,3),(3,6,4)]),(2,[(1,2,3),(3,6,4)]),(0,[(1,2,3),(0,1,6),(3,32,4)]),(2,[(1,2,3),(0,1,6),(3,32,4)]),(6,[(0,1,6),(3,32,4)]),(1,[(1,2,3),(0,1,6),(3,32,4)]),(0,[(0,2,3),(1,4,5),(3,9,7)]),(2,[(0,2,3),(1,4,5),(3,9,7)]),(5,[(1,4,5)]),(0,[(1,2,3),(1,6,4)]),(2,[(1,2,3),(1,6,4)]),(3,[(1,2,3),(1,6,4)]),(6,[(1,6,4)]),(5,[(1,6,4)]),(0,[(1,2,3),(3,1,6),(1,6,4)]),(11,[(2,4,5)]),(11,[(1,4,5)]),(0,[(0,2,3),(1,2,3),(2,6,5)]),(2,[(0,2,3),(1,2,3),(2,6,5)]),(11,[(2,6,5)]),(0,[(0,2,3),(1,2,3),(3,6,4)]),(2,[(0,2,3),(1,2,3),(3,6,4)]),(11,[(3,6,4)]),(0,[(0,2,3),(1,2,3),(1,6,4)]),(2,[(0,2,3),(1,2,3),(1,6,4)]),(1,[(0,2,3),(1,2,3),(1,6,4)]),(11,[(1,6,4)]),(2,[(1,3,5),(2,1,62)]),(0,[(1,3,5),(2,1,62)]),(0,[(3,3,4),(2,105,5),(1,212,2)]),(2,[(3,3,4),(2,105,5),(1,212,2)]),(5,[(3,3,4),(2,105,5)]),(6,[(2,105,5),(1,212,2)]),(0,[(0,2,3),(1,2,3),(0,6,4)]),(2,[(0,2,3),(1,2,3),(0,6,4)]),(11,[(0,6,4)]),(0,[(0,2,3),(1,2,3),(2,1,6)]),(2,[(0,2,3),(1,2,3),(2,1,6)]),(11,[(2,1,6)]),(0,[(0,2,3),(1,9,5),(1,1,29)]),(2,[(0,2,3),(1,9,5),(1,1,29)]),(7,[(0,2,3),(1,1,29)]),(5,[(1,1,29)]),(1,[(1,3,58),(0,4,58)]),(0,[(0,2,3),(3,9,4),(1,262,5)]),(2,[(0,2,3),(3,9,4),(1,262,5)]),(5,[(1,262,5)]),(0,[(2,1,5),(0,2,4),(1,81,83)]),(2,[(2,1,5),(0,2,4),(1,81,83)]),(1,[(0,2,4),(1,81,83)]),(3,[(0,2,4),(1,81,83)]),(5,[(2,1,5)]),(23,[]),(7,[(1,81,83)]),(6,[(2,1,5)]),(4,[(2,2,3),(1,93,3)]),(0,[(2,1,5),(3,3,4),(1,81,105)]),(2,[(2,1,5),(3,3,4),(1,81,105)]),(1,[(3,3,4),(1,81,105)]),(3,[(3,3,4),(1,81,105)]),(0,[(2,1,5),(2,2,3),(1,81,93)]),(2,[(2,1,5),(2,2,3),(1,81,93)]),(1,[(2,2,3),(1,81,93)]),(3,[(2,2,3),(1,81,93)]),(6,[(2,1,5),(1,81,93)]),(14,[(2,1,5)]),(0,[(1,2,3),(3,6,4)]),(0,[(2,1,5),(1,2,3),(3,81,6)]),(2,[(2,1,5),(1,2,3),(3,81,6)]),(5,[(2,1,5),(3,81,6)]),(1,[(1,2,3),(3,81,6)]),(0,[(2,1,5),(0,2,3),(1,2,3)]),(2,[(2,1,5),(0,2,3),(1,2,3)]),(11,[(2,1,5)]),(0,[(0,2,3),(1,2,3),(1,6,5)]),(2,[(0,2,3),(1,2,3),(1,6,5)]),(9,[(0,2,3),(3,9,4)]),(2,[(0,2,3),(3,9,4)]),(0,[(0,2,3),(3,9,4)]),(0,[(2,1,5)]),(2,[(2,1,5)]),(0,[(2,1,5),(0,2,3),(3,9,4)]),(0,[(2,1,5),(0,2,3),(1,81,9)]),(2,[(2,1,5),(0,2,3),(1,81,9)]),(1,[(0,2,3),(1,81,9)]),(3,[(0,2,3),(1,81,9)]),(9,[(0,2,3)]),(7,[(0,2,3),(1,81,9)]),(7,[(3,3,58)]),(0,[(3,3,4),(1,2,5),(3,3,58)]),(2,[(3,3,4),(1,2,5),(3,3,58)]),(14,[(1,2,5),(3,3,58)]),(0,[(2,1,5),(3,81,4),(1,2,174)]),(2,[(2,1,5),(3,81,4),(1,2,174)]),(3,[(3,81,4),(1,2,174)]),(7,[(1,2,174)]),(9,[(1,2,174)]),(0,[(2,1,5),(3,81,4)]),(2,[(2,1,5),(3,81,4)]),(3,[(3,81,4)]),(1,[(3,81,4),(2,2,3)]),(4,[(2,1,5),(2,2,3)]),(0,[(0,2,3)]),(2,[(0,2,3)]),(3,[(0,2,3)]),(4,[(2,1,5),(0,2,3)]),(1,[(3,81,4),(0,2,3)]),(6,[(2,1,5),(3,81,4)]),(0,[(2,1,5),(1,81,2)]),(2,[(2,1,5),(1,81,2)]),(3,[(1,81,2)]),(4,[(2,1,5),(1,81,2)]),(6,[(2,1,5),(1,81,2)]),(1,[(1,81,2),(3,3,4)]),(0,[(3,3,4)]),(2,[(3,3,4)]),(7,[(1,81,2)]),(11,[(3,1,6)]),(0,[(2,1,5),(1,81,3)]),(2,[(2,1,5),(1,81,3)]),(0,[(0,2,4)]),(2,[(0,2,4)]),(5,[(2,1,5),(1,81,3)]),(3,[(1,81,3)]),(7,[(1,81,3)]),(0,[(2,1,5),(1,81,2),(1,220,3)]),(2,[(2,1,5),(1,81,2),(1,220,3)]),(5,[(2,1,5),(1,220,3)]),(1,[(1,81,2),(1,220,3)]),(9,[(1,220,3)]),(0,[(1,1,5),(0,4,152),(1,2,153)]),(3,[(1,2,153)]),(7,[(1,2,153)]),(0,[(1,1,5),(3,3,152),(1,271,2)]),(2,[(1,1,5),(3,3,152),(1,271,2)]),(3,[(1,271,2)]),(5,[(1,1,5),(3,3,152)]),(1,[(3,3,152),(1,271,2)]),(0,[(1,2,5),(3,3,58),(1,175,1)]),(2,[(1,2,5),(3,3,58),(1,175,1)]),(4,[(1,1,5),(3,3,152)]),(0,[(1,1,5),(3,3,4),(3,3,152)]),(2,[(1,1,5),(3,3,4),(3,3,152)]),(14,[(1,1,5),(3,3,152)]),(6,[(1,1,5)]),(1,[(3,3,4),(3,3,152)]),(0,[(0,3,4),(1,126,2)]),(2,[(0,3,4),(1,126,2)]),(1,[(0,3,4),(1,126,2)]),(5,[(0,3,4)]),(9,[(0,3,4),(1,126,2)]),(4,[(1,126,2)]),(7,[(1,126,2)]),(0,[(1,1,5),(3,2,152)]),(2,[(1,1,5),(3,2,152)]),(5,[(1,1,5)]),(0,[(1,1,5),(3,2,4),(3,186,152)]),(2,[(1,1,5),(3,2,4),(3,186,152)]),(0,[(1,1,5),(3,3,4),(1,105,2)]),(2,[(1,1,5)]),(0,[(1,1,5),(0,3,4),(3,3,152)]),(2,[(1,1,5),(0,3,4),(3,3,152)]),(1,[(0,3,4),(3,3,152)]),(3,[(0,3,4)]),(0,[(1,1,5),(0,3,4),(3,126,152)]),(2,[(1,1,5),(0,3,4),(3,126,152)]),(1,[(0,3,4),(3,126,152)]),(0,[(1,2,3),(1,2,4),(3,3,92)]),(2,[(1,2,3),(1,2,4),(3,3,92)]),(5,[(3,3,92)]),(0,[(1,1,5),(2,3,2),(3,55,152)]),(2,[(1,1,5),(2,3,2),(3,55,152)]),(3,[(2,3,2)]),(5,[(1,1,5),(3,55,152)]),(0,[(1,1,5),(0,4,152)]),(2,[(1,1,5),(0,4,152)]),(4,[(1,1,5),(1,2,3)]),(1,[(1,2,3),(0,4,152)]),(0,[(1,1,5),(1,2,3),(3,6,152)]),(2,[(1,1,5),(1,2,3),(3,6,152)]),(1,[(1,2,3),(3,6,152)]),(0,[(1,1,5),(1,2,3),(0,6,152)]),(2,[(1,1,5),(1,2,3),(0,6,152)]),(5,[(1,1,5),(0,6,152)]),(6,[(1,1,5),(0,6,152)]),(4,[(1,1,5),(0,2,3)]),(14,[(0,2,3)]),(1,[(0,2,3),(0,4,152)]),(0,[(1,2,3),(3,1,6),(3,25,4)]),(2,[(1,2,3),(3,1,6),(3,25,4)]),(0,[(1,1,5),(0,2,3),(1,2,3)]),(2,[(1,1,5),(0,2,3),(1,2,3)]),(11,[(1,1,5)]),(0,[(1,1,5),(0,2,3),(1,9,5)]),(2,[(1,1,5),(0,2,3),(1,9,5)]),(1,[(3,1,4),(1,3,58)]),(1,[(3,3,4),(3,105,7)]),(6,[(1,4,5),(3,105,7)]),(3,[(2,2,3),(1,2,5)]),(5,[(3,1,4)]),(2,[(2,2,3),(1,2,5)]),(0,[(2,2,3),(1,2,5)]),(0,[(3,2,4),(1,186,5)]),(2,[(3,2,4),(1,186,5)]),(6,[(3,2,4),(1,186,5)]),(5,[(1,186,5)]),(3,[(3,2,4),(1,186,5)]),(7,[(2,1,3)]),(9,[(3,2,4),(1,186,5)]),(0,[(2,1,3)]),(2,[(2,1,3)]),(12,[(3,2,4),(1,186,5)]),(0,[(0,2,3),(1,2,3),(2,6,4)]),(5,[(2,6,4)]),(11,[(2,6,4)]),(0,[(0,2,4),(1,83,5)]),(2,[(0,2,4),(1,83,5)]),(9,[(0,2,4),(1,83,5)]),(2,[(2,1,3),(0,2,4),(1,83,5)]),(12,[(0,2,4),(1,83,5)]),(0,[(1,1,2),(0,38,4)]),(2,[(1,1,2),(0,38,4)]),(5,[(0,38,4)]),(6,[(1,1,2),(0,38,4)]),(0,[(1,3,2),(0,1,6),(1,3,5)]),(1,[(1,3,2),(0,1,6)]),(6,[(2,2,62)]),(1,[(0,1,4),(2,2,62)]),(9,[(3,2,4)]),(0,[(1,1,5),(3,2,4)]),(0,[(2,1,3),(1,1,5)]),(2,[(2,1,3),(1,1,5)]),(4,[(2,1,3),(1,1,5)]),(1,[(2,1,3),(3,2,4)]),(0,[(0,2,3),(1,9,5)]),(2,[(0,2,3),(1,9,5)]),(6,[(3,1,4)]),(2,[(3,1,4)]),(0,[(3,1,4)]),(0,[(2,1,3),(1,185,5),(1,3,5)]),(2,[(2,1,3),(1,185,5),(1,3,5)]),(4,[(2,2,3)]),(1,[(2,2,3),(3,3,7)]),(0,[(2,2,3),(1,4,5),(3,3,7)]),(2,[(2,2,3),(1,4,5),(3,3,7)]),(0,[(1,2,3),(1,6,5),(3,5,34)]),(2,[(1,2,3),(1,6,5),(3,5,34)]),(0,[(2,1,2),(1,282,5)]),(2,[(2,1,2),(1,282,5)]),(3,[(1,282,5)]),(5,[(1,282,5)]),(4,[(2,1,2),(1,282,5)]),(1,[(2,1,2)]),(1,[(2,1,2),(3,3,4)]),(0,[(2,1,2),(3,282,4)]),(2,[(2,1,2),(3,282,4)]),(0,[(1,1,2),(2,38,3),(1,285,5)]),(2,[(1,1,2),(2,38,3),(1,285,5)]),(3,[(1,285,5)]),(5,[(2,38,3),(1,285,5)]),(1,[(1,1,2),(2,38,3)]),(0,[(0,3,2),(1,4,5),(3,3,7)]),(2,[(0,3,2),(1,4,5),(3,3,7)]),(0,[(3,1,4),(2,2,5),(1,287,157)]),(2,[(3,1,4),(2,2,5),(1,287,157)]),(3,[(2,2,5)]),(1,[(3,1,4),(1,287,157)]),(0,[(2,1,3),(2,2,4),(1,289,185)]),(2,[(2,1,3),(2,2,4),(1,289,185)]),(6,[(2,2,4),(1,289,185)]),(3,[(2,2,4),(1,289,185)]),(1,[(2,1,3),(2,2,4),(1,289,185)]),(0,[(2,1,2),(3,282,4),(1,284,5)]),(2,[(2,1,2),(3,282,4),(1,284,5)]),(5,[(3,282,4),(1,284,5)]),(3,[(3,282,4),(1,284,5)]),(1,[(2,1,2),(3,282,4)]),(9,[(1,284,5)]),(7,[(2,1,2)]),(2,[(1,1,2),(0,3,4),(1,126,5)]),(0,[(1,1,2)]),(1,[(1,1,2),(0,3,4)]),(0,[(0,3,4),(1,126,2),(2,213,5)]),(2,[(0,3,4),(1,126,2),(2,213,5)]),(0,[(0,1,3),(1,89,2)]),(2,[(0,1,3),(1,89,2)]),(3,[(1,89,2)]),(5,[(0,1,3)]),(7,[(0,1,3),(1,89,2)]),(2,[(2,1,3),(1,185,2),(1,4,5)]),(0,[(1,4,5)]),(0,[(2,1,3),(1,185,2)]),(4,[(2,1,3),(1,185,2)]),(2,[(2,1,3),(1,185,2)]),(1,[(2,1,3),(1,185,2)]),(6,[(1,185,2)]),(0,[(1,2,3),(1,2,5)]),(2,[(1,4,5)]),(4,[(0,1,3),(1,89,2)]),(2,[(2,1,3),(1,185,2),(1,3,5)]),(2,[(1,1,2)]),(4,[(1,1,2)]),(1,[(1,1,2),(3,3,7)]),(2,[(1,4,5),(3,3,7)]),(0,[(0,3,4),(1,2,5),(3,3,58)]),(2,[(0,3,4),(1,2,5),(3,3,58)]),(0,[(3,1,3),(1,180,2)]),(2,[(3,1,3),(1,180,2)]),(5,[(3,1,3)]),(7,[(3,1,3),(1,180,2)]),(4,[(1,2,5),(1,1,58)]),(1,[(1,1,58)]),(0,[(2,1,3),(2,2,4),(1,289,3)]),(2,[(2,1,3),(2,2,4),(1,289,3)]),(6,[(2,2,4)]),(3,[(2,2,4),(1,289,3)]),(1,[(2,1,3),(2,2,4),(1,289,3)]),(9,[(2,2,4),(1,289,3)]),(2,[(1,2,3),(1,2,5)]),(3,[(1,2,3),(1,2,5)]),(4,[(1,2,3),(1,2,5)]),(0,[(2,1,3),(1,185,2),(2,2,3)]),(2,[(2,1,3),(1,185,2),(2,2,3)]),(0,[(2,1,3),(1,185,2),(1,1,5)]),(2,[(2,1,3),(1,185,2),(1,1,5)]),(5,[(2,1,3),(1,1,5)]),(4,[(1,1,5)]),(0,[(0,2,3),(1,2,3),(1,1,6)]),(2,[(0,2,3),(1,2,3),(1,1,6)]),(5,[(1,1,6)]),(11,[(1,1,6)]),(0,[(2,1,2),(1,3,4),(3,282,194)]),(2,[(2,1,2),(1,3,4),(3,282,194)]),(5,[(1,3,4),(3,282,194)]),(3,[(1,3,4),(3,282,194)]),(4,[(2,1,2)]),(6,[(2,1,2),(3,282,194)]),(9,[(1,3,4)]),(0,[(1,1,3),(2,91,5),(1,297,2)]),(2,[(1,1,3),(2,91,5),(1,297,2)]),(3,[(1,297,2)]),(0,[(1,1,2),(1,4,5),(0,38,7)]),(2,[(1,1,2),(1,4,5),(0,38,7)]),(1,[(1,1,2),(0,38,7)]),(9,[(1,4,5),(0,38,7)]),(2,[(1,2,3),(1,4,5)]),(0,[(1,2,3),(1,4,5)]),(3,[(3,3,4),(1,4,5)]),(1,[(1,1,2),(3,3,4)]),(9,[(3,3,4),(1,4,5)]),(6,[(1,1,2)]),(2,[(3,1,3),(1,180,2),(1,4,5)]),(4,[(3,1,3),(1,180,2)]),(0,[(1,2,3),(3,6,4),(1,4,5)]),(2,[(1,2,3),(3,6,4),(1,4,5)]),(0,[(3,3,4),(1,105,5)]),(2,[(3,3,4),(1,105,5)]),(9,[(3,3,4),(1,105,5)]),(2,[(1,2,3),(1,2,5),(0,1,58)]),(9,[(1,2,3),(1,2,5)]),(0,[(2,1,3),(1,185,2),(2,219,5)]),(2,[(2,1,3),(1,185,2),(2,219,5)]),(9,[(2,219,5)]),(5,[(2,1,3),(2,219,5)]),(6,[(1,185,2),(2,219,5)]),(0,[(1,2,3),(3,1,6),(1,25,5)]),(2,[(1,2,3),(3,1,6),(1,25,5)]),(0,[(1,1,3),(0,2,4),(1,83,3)]),(2,[(1,1,3),(0,2,4),(1,83,3)]),(11,[(0,1,6)]),(0,[(0,3,4)]),(2,[(0,3,4)]),(9,[(0,3,4)]),(6,[(1,1,2),(2,38,5)]),(0,[(0,1,4),(1,16,2),(2,86,3)]),(2,[(0,1,4),(1,16,2),(2,86,3)]),(9,[(2,86,3)]),(5,[(0,1,4),(2,86,3)]),(2,[(1,3,5),(2,4,62)]),(0,[(1,3,5),(2,4,62)]),(0,[(3,1,2),(2,3,4),(1,232,177)]),(2,[(3,1,2),(2,3,4),(1,232,177)]),(4,[(3,1,2)]),(5,[(2,3,4)]),(6,[(3,1,2)]),(1,[(3,1,2),(2,3,4),(1,232,177)]),(0,[(0,1,4),(1,16,2),(2,2,5)]),(2,[(0,1,4),(1,16,2),(2,2,5)]),(3,[(1,16,2),(2,2,5)]),(7,[(1,16,2)]),(4,[(1,1,2),(2,38,3)]),(2,[(1,1,2),(2,38,3)]),(0,[(2,1,2),(1,282,5),(3,3,283)]),(2,[(2,1,2),(1,282,5),(3,3,283)]),(1,[(2,1,2),(3,3,283)]),(9,[(3,3,283)]),(0,[(0,1,3),(3,89,4),(1,2,4)]),(2,[(0,1,3),(3,89,4),(1,2,4)]),(9,[(1,2,4)]),(4,[(0,1,3)]),(5,[(0,1,3),(3,89,4)]),(2,[(0,1,4),(1,16,5),(0,2,3)]),(4,[(1,16,5),(0,2,3)]),(1,[(0,1,4),(0,2,3)]),(0,[(2,1,2),(3,282,4),(1,2,4)]),(2,[(2,1,2),(3,282,4),(1,2,4)]),(5,[(3,282,4)]),(3,[(3,282,4),(1,2,4)]),(4,[(1,1,2),(1,3,5)]),(9,[(3,2,4),(1,4,5)]),(2,[(3,2,4),(1,4,5)]),(0,[(3,2,4),(1,4,5)]),(3,[(3,2,4),(1,4,5)]),(12,[(3,2,4),(1,4,5)]),(0,[(1,2,3),(0,1,6),(1,32,5)]),(2,[(1,2,3),(0,1,6),(1,32,5)]),(0,[(1,1,2),(1,3,5),(0,38,62)]),(2,[(1,1,2),(1,3,5),(0,38,62)]),(1,[(1,1,2),(0,38,62)]),(5,[(1,3,5),(0,38,62)]),(0,[(2,1,5),(1,2,3),(0,6,4)]),(0,[(1,1,2),(2,38,3),(2,285,5)]),(2,[(1,1,2),(2,38,3),(2,285,5)]),(3,[(2,285,5)]),(5,[(2,38,3),(2,285,5)]),(1,[(1,1,2),(3,3,58)]),(0,[(1,2,5),(0,1,58)]),(2,[(1,2,5),(0,1,58)]),(0,[(0,1,3),(1,1,3)]),(0,[(0,1,3),(1,1,3),(2,2,4)]),(2,[(0,1,3),(1,1,3)]),(4,[(0,1,3),(1,1,3)]),(3,[(2,2,4)]),(7,[(0,1,3),(1,1,3)]),(12,[(2,2,4)]),(15,[(0,1,3),(1,1,3)]),(0,[(3,1,3),(1,180,5)]),(2,[(3,1,3),(1,180,5)]),(3,[(0,2,4)]),(4,[(3,1,3),(1,180,5)]),(7,[(3,1,3)]),(0,[(2,3,5),(3,257,4),(1,2,306)]),(2,[(2,3,5),(3,257,4),(1,2,306)]),(5,[(2,3,5),(3,257,4)]),(7,[(1,2,306)]),(9,[(3,3,38)]),(2,[(1,3,5),(2,2,62)]),(0,[(1,3,5),(2,2,62)]),(3,[(1,3,5),(2,2,62)]),(1,[(2,2,62)]),(7,[(2,2,62)]),(3,[(1,2,4),(3,3,92)]),(2,[(1,2,4),(3,3,92)]),(0,[(0,1,4),(2,2,5),(1,287,16)]),(2,[(0,1,4),(2,2,5),(1,287,16)]),(4,[(2,2,5),(1,287,16)]),(7,[(1,287,16)]),(0,[(1,1,2),(1,2,4),(0,38,4)]),(2,[(1,1,2),(1,2,4),(0,38,4)]),(3,[(1,2,4)]),(9,[(1,2,4),(0,38,4)]),(0,[(1,1,2),(2,3,4),(3,232,38)]),(2,[(1,1,2),(2,3,4),(3,232,38)]),(9,[(2,3,4),(3,232,38)]),(0,[(0,1,4),(1,16,3)]),(5,[(0,1,4),(1,16,3)]),(3,[(1,16,3)]),(4,[(1,16,3)]),(7,[(1,16,3)]),(9,[(2,2,5)]),(0,[(1,2,4)]),(2,[(1,2,4)]),(5,[(2,38,3)]),(16,[]),(1,[(1,2,4)]),(7,[(1,1,2),(2,38,3)]),(2,[(1,1,2),(1,2,4),(2,38,3)]),(9,[(2,38,3)]),(0,[(1,1,3),(0,2,4),(1,2,4)]),(2,[(1,1,3),(0,2,4),(1,2,4)]),(3,[(0,2,4),(1,2,4)]),(5,[(1,1,3)]),(6,[(0,2,4),(1,2,4)]),(4,[(1,1,3)]),(15,[(1,1,3)]),(9,[(0,2,4),(1,2,4)]),(0,[(0,1,2),(1,1,2),(1,3,4)]),(5,[(1,3,4)]),(2,[(0,1,2),(1,1,2),(1,3,4)]),(13,[(1,3,4)]),(3,[(1,3,4)]),(0,[(0,1,3),(1,89,2),(2,293,5)]),(2,[(0,1,3),(1,89,2),(2,293,5)]),(9,[(2,293,5)]),(1,[(0,1,3),(1,89,2)]),(6,[(2,293,5)]),(0,[(1,3,5),(3,2,62)]),(2,[(1,3,5),(3,2,62)]),(9,[(1,3,5),(3,2,62)]),(0,[(1,2,3),(1,4,5),(3,6,7)]),(2,[(1,2,3),(1,4,5),(3,6,7)]),(0,[(0,1,2),(1,1,2),(1,4,5)]),(2,[(0,1,2),(1,1,2),(1,4,5)]),(13,[(1,4,5)]),(0,[(0,1,2),(1,107,5),(1,3,5)]),(2,[(0,1,2),(1,107,5),(1,3,5)]),(3,[(1,107,5),(1,3,5)]),(9,[(3,2,4),(1,186,3)]),(6,[(3,2,4)]),(15,[(2,1,3)]),(0,[(0,1,2),(1,107,5),(1,3,108)]),(2,[(0,1,2),(1,107,5),(1,3,108)]),(5,[(1,3,108)]),(1,[(0,1,2),(1,3,108)]),(9,[(1,3,108)]),(7,[(0,1,2),(1,3,108)]),(0,[(0,1,2),(1,107,5),(1,4,5)]),(2,[(0,1,2),(1,107,5),(1,4,5)]),(0,[(3,1,3),(1,4,5),(3,180,7)]),(2,[(3,1,3),(1,4,5),(3,180,7)]),(0,[(3,3,4),(1,105,2),(2,4,5)]),(2,[(3,3,4),(1,105,2),(2,4,5)]),(7,[(1,105,2)]),(5,[(3,3,4),(2,4,5)]),(6,[(1,105,2),(2,4,5)]),(0,[(2,3,2),(3,55,4)]),(2,[(2,3,2),(3,55,4)]),(9,[(2,3,2),(3,55,4)]),(4,[(2,1,5)]),(0,[(0,1,3),(1,1,3),(2,2,5)]),(2,[(0,1,3),(1,1,3),(2,2,5)]),(6,[(2,2,5)]),(1,[(0,1,3),(1,1,3)]),(12,[(2,2,5)]),(4,[(3,1,2),(1,3,5)]),(0,[(0,1,2),(1,107,5)]),(2,[(0,1,2),(1,107,5)]),(3,[(1,107,5)]),(0,[(0,2,3),(1,9,5),(1,4,5)]),(2,[(0,2,3),(1,9,5),(1,4,5)]),(4,[(0,2,3),(1,9,5)]),(2,[(2,1,3),(1,185,2),(1,3,4)]),(0,[(1,3,4)]),(3,[(1,185,2)]),(0,[(0,2,4),(1,2,4)]),(0,[(2,1,3),(0,2,4),(1,2,4)]),(2,[(0,2,4),(1,2,4)]),(2,[(2,1,3),(0,2,4),(1,2,4)]),(1,[(0,2,4),(1,2,4)]),(1,[(2,1,3),(0,2,4),(1,2,4)]),(12,[(0,2,4),(1,2,4)]),(0,[(0,3,4),(1,3,4)]),(0,[(0,1,2),(0,3,4),(1,3,4)]),(2,[(0,3,4),(1,3,4)]),(2,[(0,1,2),(0,3,4),(1,3,4)]),(16,[(0,1,2)]),(1,[(3,1,2),(3,3,4)]),(0,[(0,1,2),(1,1,2),(0,3,4)]),(2,[(0,1,2),(1,1,2),(0,3,4)]),(13,[(0,3,4)]),(9,[(3,3,4),(2,105,5)]),(0,[(2,1,2)]),(2,[(2,1,2)]),(14,[(2,1,2)]),(2,[(3,3,4),(2,105,5)]),(0,[(3,3,4),(2,105,5)]),(3,[(3,3,4),(2,105,5)]),(13,[(3,3,4),(2,105,5)]),(0,[(0,1,4),(1,1,4),(0,2,3)]),(2,[(0,1,4),(1,1,4),(0,2,3)]),(2,[(0,1,4),(1,1,4)]),(0,[(0,1,4),(1,1,4)]),(0,[(3,1,3),(3,180,4),(1,4,5)]),(2,[(3,1,3),(3,180,4),(1,4,5)]),(4,[(3,1,3)]),(3,[(1,3,5),(2,4,62)]),(0,[(2,1,2),(3,3,4),(1,282,105)]),(2,[(2,1,2),(3,3,4),(1,282,105)]),(5,[(3,3,4),(1,282,105)]),(3,[(3,3,4),(1,282,105)]),(0,[(2,3,5),(1,257,2)]),(2,[(2,3,5),(1,257,2)]),(0,[(0,1,4)]),(2,[(0,1,4)]),(4,[(2,3,5),(1,257,2)]),(5,[(2,3,5)]),(9,[(2,3,5),(1,257,2)]),(1,[(0,1,4),(1,257,2)]),(7,[(1,257,2)]),(0,[(0,1,3),(3,89,4)]),(2,[(0,1,3),(3,89,4)]),(0,[(2,1,2),(1,282,3),(1,3,2)]),(2,[(2,1,2),(1,282,3),(1,3,2)]),(5,[(1,282,3)]),(3,[(1,282,3),(1,3,2)]),(9,[(1,3,2)]),(0,[(0,1,2)]),(2,[(0,1,2)]),(5,[(0,3,4),(3,126,4)]),(2,[(0,3,4),(3,126,4)]),(0,[(0,3,4),(3,126,4)]),(9,[(0,3,4),(3,126,4)]),(0,[(1,2,5),(0,1,58),(1,1,58)]),(2,[(1,2,5),(0,1,58),(1,1,58)]),(1,[(0,1,58),(1,1,58)]),(5,[(0,1,58),(1,1,58)]),(0,[(1,3,5),(3,1,62),(1,316,2)]),(2,[(1,3,5),(3,1,62),(1,316,2)]),(1,[(3,1,62),(1,316,2)]),(0,[(3,1,2),(3,3,4),(1,105,177)]),(2,[(3,1,2),(3,3,4),(1,105,177)]),(4,[(3,1,2),(1,105,177)]),(6,[(3,1,2),(1,105,177)]),(1,[(3,1,2),(3,3,4),(1,105,177)]),(0,[(0,1,3),(1,89,2),(2,2,4)]),(0,[(0,3,4),(1,2,5),(3,126,58)]),(2,[(0,3,4),(1,2,5),(3,126,58)]),(5,[(0,38,4),(1,39,5)]),(0,[(1,1,3),(0,91,4),(1,117,2)]),(2,[(1,1,3),(0,91,4),(1,117,2)]),(3,[(1,117,2)]),(5,[(1,1,3),(0,91,4)]),(0,[(1,1,5),(0,2,4),(1,83,5)]),(2,[(1,1,5),(0,2,4),(1,83,5)]),(4,[(1,1,5),(1,83,5)]),(0,[(2,2,3),(1,93,5)]),(2,[(2,2,3),(1,93,5)]),(0,[(1,1,2),(2,1,5)]),(2,[(1,1,2),(2,1,5)]),(4,[(1,1,2),(2,1,5)]),(6,[(1,1,2),(2,1,5)]),(0,[(2,1,5),(3,3,4)]),(3,[(3,282,4)]),(0,[(0,1,2),(1,107,3),(1,3,4)]),(2,[(0,1,2),(1,107,3),(1,3,4)]),(4,[(0,1,2),(1,107,3)]),(3,[(1,107,3),(1,3,4)]),(7,[(0,1,2),(1,107,3)]),(0,[(2,2,5),(3,287,4)]),(2,[(2,2,5),(3,287,4)]),(6,[(2,2,5),(3,287,4)]),(3,[(2,2,5),(3,287,4)]),(9,[(2,2,5),(3,287,4)]),(1,[(2,1,3),(3,287,4)]),(12,[(2,2,5),(3,287,4)]),(4,[(2,1,3),(2,2,5)]),(0,[(3,3,4),(1,105,2),(2,2,5)]),(2,[(3,3,4),(1,105,2),(2,2,5)]),(0,[(0,1,3),(1,89,2),(2,2,5)]),(2,[(0,1,3),(1,89,2),(2,2,5)]),(6,[(2,1,127)]),(2,[(0,3,4),(1,126,5),(2,1,127)]),(0,[(0,3,4),(1,126,5),(2,1,127)]),(0,[(0,1,2),(1,1,2),(1,3,5)]),(2,[(0,1,2),(1,1,2),(1,3,5)]),(13,[(1,3,5)]),(0,[(0,1,2),(1,1,2),(3,3,4)]),(2,[(0,1,2),(1,1,2),(3,3,4)]),(13,[(3,3,4)]),(0,[(1,2,3),(1,2,4),(0,6,4)]),(2,[(1,2,3),(1,2,4),(0,6,4)]),(3,[(3,89,4)]),(0,[(2,2,5)]),(2,[(2,2,5)]),(0,[(1,1,3),(3,2,4),(3,186,91)]),(2,[(1,1,3),(3,2,4),(3,186,91)]),(0,[(3,1,3),(3,180,4)]),(2,[(3,1,3),(3,180,4)]),(5,[(3,1,3),(3,180,4)]),(0,[(2,1,2),(1,4,5),(3,282,7)]),(2,[(2,1,2),(1,4,5),(3,282,7)]),(5,[(1,4,5),(3,282,7)]),(3,[(1,4,5),(3,282,7)]),(1,[(2,1,2),(3,282,7)]),(0,[(0,1,3),(1,89,5)]),(2,[(0,1,3),(1,89,5)]),(3,[(1,89,5)]),(1,[(0,1,3),(0,2,4)]),(0,[(0,1,3),(0,2,4),(1,89,83)]),(2,[(0,1,3),(0,2,4),(1,89,83)]),(4,[(0,1,3),(1,89,83)]),(14,[(0,1,3)]),(1,[(0,1,3),(0,2,4),(1,89,83)]),(0,[(0,1,3),(3,89,4),(1,303,2)]),(2,[(0,1,3),(3,89,4),(1,303,2)]),(3,[(3,89,4),(1,303,2)]),(9,[(1,303,2)]),(6,[(1,303,2)]),(0,[(0,1,4),(1,16,3),(1,3,2)]),(2,[(0,1,4),(1,16,3),(1,3,2)]),(3,[(1,16,3),(1,3,2)]),(4,[(1,16,3),(1,3,2)]),(14,[(1,3,2)]),(4,[(0,1,2),(1,3,5)]),(2,[(3,3,4),(1,3,5)]),(0,[(3,3,4),(1,3,5)]),(0,[(0,1,2),(3,3,4),(1,105,107)]),(2,[(0,1,2),(3,3,4),(1,105,107)]),(4,[(0,1,2),(1,105,107)]),(6,[(0,1,2),(1,105,107)]),(1,[(0,1,2),(3,3,4),(1,105,107)]),(12,[(1,2,5),(0,4,58)]),(0,[(3,3,4),(1,105,2),(3,1,215)]),(2,[(3,3,4),(1,105,2),(3,1,215)]),(0,[(0,1,2),(1,107,5),(3,3,108)]),(2,[(0,1,2),(1,107,5),(3,3,108)]),(1,[(0,1,2),(3,3,108)]),(9,[(3,3,108)]),(5,[(3,3,108)]),(0,[(1,1,2),(0,3,4),(3,126,38)]),(2,[(1,1,2),(0,3,4),(3,126,38)]),(5,[(0,3,4),(3,126,38)]),(9,[(0,3,4),(3,126,38)]),(1,[(1,1,2),(0,3,4),(3,126,38)]),(4,[(1,1,2),(3,126,38)]),(0,[(0,1,3),(3,89,4),(1,303,5)]),(2,[(0,1,3),(3,89,4),(1,303,5)]),(9,[(1,303,5)]),(9,[(0,2,4),(3,83,4)]),(2,[(0,2,4),(3,83,4)]),(0,[(0,2,4),(3,83,4)]),(3,[(0,2,4),(3,83,4)]),(12,[(0,2,4),(3,83,4)]),(6,[(2,2,195)]),(4,[(0,1,3),(1,89,5)]),(2,[(0,1,3),(1,89,5),(2,2,195)]),(0,[(0,1,3),(1,89,5),(2,2,195)]),(9,[(2,2,195)]),(2,[(0,1,2),(0,3,4),(1,126,5)]),(0,[(0,1,2),(2,3,4),(1,232,107)]),(2,[(0,1,2),(2,3,4),(1,232,107)]),(0,[(0,1,2),(2,3,4),(1,232,2)]),(2,[(0,1,2),(2,3,4),(1,232,2)]),(9,[(2,3,4),(1,232,2)]),(0,[(1,1,2),(1,2,5),(2,38,5)]),(2,[(1,1,2),(1,2,5),(2,38,5)]),(0,[(1,1,2),(1,2,3),(2,38,3)]),(2,[(1,1,2),(1,2,3),(2,38,3)]),(0,[(0,1,3),(1,4,5),(3,89,7)]),(2,[(0,1,3),(1,4,5),(3,89,7)]),(5,[(2,1,29)]),(6,[(2,1,29)]),(2,[(0,2,3),(1,9,5),(2,1,29)]),(0,[(0,2,3),(1,9,5),(2,1,29)]),(0,[(1,1,4),(3,3,17),(1,334,2)]),(2,[(1,1,4),(3,3,17),(1,334,2)]),(3,[(1,334,2)]),(7,[(1,334,2)]),(0,[(0,1,3),(1,4,5),(3,3,7)]),(2,[(0,1,3),(1,4,5),(3,3,7)]),(0,[(1,2,5),(2,1,58),(3,124,4)]),(2,[(1,2,5),(2,1,58),(3,124,4)]),(1,[(2,1,58),(3,124,4)]),(5,[(1,1,3),(2,1,5)]),(2,[(1,1,3),(2,1,5)]),(0,[(2,1,5),(0,2,4)]),(0,[(0,1,4),(1,1,4),(1,2,3)]),(2,[(0,1,4),(1,1,4),(1,2,3)]),(0,[(0,1,2),(1,107,3),(1,3,5)]),(2,[(0,1,2),(1,107,3),(1,3,5)]),(1,[(0,1,2),(1,107,3)]),(3,[(1,107,3),(1,3,5)]),(1,[(0,1,2),(0,4,62)]),(0,[(0,1,4),(1,16,5),(1,2,5)]),(2,[(0,1,4),(1,16,5),(1,2,5)]),(0,[(3,2,4),(1,3,5),(3,186,62)]),(2,[(3,2,4),(1,3,5),(3,186,62)]),(5,[(1,3,5),(3,186,62)]),(6,[(3,2,4),(3,186,62)]),(0,[(0,1,4),(1,2,5),(3,16,58)]),(2,[(0,1,4),(1,2,5),(3,16,58)]),(4,[(1,2,5),(3,16,58)]),(3,[(1,2,5),(3,16,58)]),(7,[(3,16,58)]),(5,[(0,1,4),(3,16,58)]),(0,[(0,1,3),(1,2,5),(3,89,58)]),(2,[(0,1,3),(1,2,5),(3,89,58)]),(1,[(0,1,3),(3,89,58)]),(3,[(1,2,5),(3,89,58)]),(2,[(3,3,4),(2,4,5)]),(0,[(3,3,4),(2,4,5)]),(9,[(3,3,4),(2,4,5)]),(1,[(3,2,62)]),(1,[(2,1,3),(3,2,62)]),(0,[(3,1,4),(2,2,3),(1,93,157)]),(2,[(3,1,4),(2,2,3),(1,93,157)]),(4,[(1,1,2),(2,38,5)]),(0,[(0,1,2),(2,3,5),(1,257,107)]),(2,[(0,1,2),(2,3,5),(1,257,107)]),(9,[(2,3,5)]),(3,[(2,3,5),(1,257,107)]),(1,[(0,1,2),(1,257,107)]),(7,[(0,1,2),(1,257,107)]),(4,[(1,3,5),(1,2,183)]),(0,[(0,1,4),(1,16,2),(2,2,3)]),(2,[(0,1,4),(1,16,2),(2,2,3)]),(3,[(1,16,2),(2,2,3)]),(4,[(1,16,2),(2,2,3)]),(0,[(1,1,3),(0,91,4)]),(2,[(1,1,3),(0,91,4)]),(3,[(3,3,2)]),(9,[(0,91,4)]),(6,[(0,91,4)]),(14,[(3,3,2)]),(4,[(2,1,3),(1,2,5)]),(12,[(3,2,4),(1,2,5)]),(9,[(1,2,5),(2,38,3)]),(2,[(1,1,2),(1,2,5),(2,38,3)]),(0,[(1,1,2),(2,38,3)]),(0,[(3,1,4),(0,2,3),(1,157,9)]),(2,[(3,1,4),(0,2,3),(1,157,9)]),(4,[(0,2,3),(1,157,9)]),(9,[(0,2,3),(1,157,9)]),(1,[(3,1,4),(0,2,3),(1,157,9)]),(9,[(0,4,152)]),(1,[(2,2,3),(0,4,152)]),(0,[(2,1,3),(1,185,2),(1,219,5)]),(2,[(2,1,3),(1,185,2),(1,219,5)]),(5,[(2,1,3),(1,219,5)]),(3,[(1,185,2),(1,219,5)]),(9,[(1,219,5)]),(0,[(2,1,2),(1,3,5),(3,282,62)]),(2,[(2,1,2),(1,3,5),(3,282,62)]),(5,[(1,3,5),(3,282,62)]),(3,[(1,3,5),(3,282,62)]),(1,[(2,1,2),(3,282,62)]),(2,[(3,3,4),(1,4,5)]),(0,[(3,3,4),(1,4,5)]),(6,[(1,2,5),(0,4,58)]),(1,[(2,1,3),(0,4,58)]),(0,[(3,3,4),(1,105,2),(1,4,5)]),(2,[(3,3,4),(1,105,2),(1,4,5)]),(4,[(1,105,2)]),(6,[(1,105,2),(1,4,5)]),(0,[(1,3,2),(1,3,5),(0,2,62)]),(2,[(1,3,2),(1,3,5),(0,2,62)]),(0,[(1,2,3),(1,6,5),(0,1,34)]),(2,[(1,2,3),(1,6,5),(0,1,34)]),(0,[(2,1,3),(2,2,5),(1,287,185)]),(2,[(2,1,3),(2,2,5),(1,287,185)]),(6,[(2,2,5),(1,287,185)]),(3,[(2,2,5),(1,287,185)]),(1,[(2,1,3),(1,287,185)]),(0,[(2,2,3),(3,93,4)]),(2,[(2,2,3),(3,93,4)]),(6,[(3,93,4)]),(3,[(2,2,3),(3,93,4)]),(9,[(2,2,3),(3,93,4)]),(9,[(1,3,4),(3,2,194)]),(6,[(3,2,194)]),(6,[(1,105,2)]),(0,[(2,1,5),(1,81,2),(2,220,3)]),(2,[(2,1,5),(1,81,2),(2,220,3)]),(9,[(2,220,3)]),(5,[(2,1,5),(2,220,3)]),(0,[(2,1,4),(3,1,4),(1,2,3)]),(2,[(2,1,4),(3,1,4),(1,2,3)]),(6,[(2,1,4),(3,1,4)]),(4,[(0,1,2),(1,105,5)]),(0,[(0,1,4),(1,16,2),(2,86,5)]),(2,[(0,1,4),(1,16,2),(2,86,5)]),(3,[(1,16,2),(2,86,5)]),(9,[(2,86,5)]),(9,[(1,4,5),(3,2,7)]),(2,[(1,4,5),(3,2,7)]),(3,[(1,4,5),(3,2,7)]),(1,[(2,1,3),(3,2,7)]),(12,[(1,4,5),(3,2,7)]),(6,[(1,4,5),(3,2,7)]),(0,[(0,1,4),(0,2,3),(1,2,3)]),(2,[(0,1,4),(0,2,3),(1,2,3)]),(11,[(0,1,4)]),(2,[(0,2,4),(1,83,5),(1,3,84)]),(0,[(0,2,4),(1,83,5),(1,3,84)]),(7,[(1,3,84)]),(5,[(1,3,84)]),(1,[(0,1,4),(1,3,58)]),(1,[(3,3,4),(1,105,2)]),(0,[(2,1,3),(1,4,5),(3,3,7)]),(2,[(2,1,3),(1,4,5),(3,3,7)]),(1,[(2,1,3),(3,3,7)]),(0,[(3,1,4),(1,2,5),(3,157,58)]),(2,[(3,1,4),(1,2,5),(3,157,58)]),(1,[(3,1,4),(3,157,58)]),(1,[(1,1,3),(0,91,4)]),(14,[(2,2,5)]),(0,[(3,1,3),(1,180,2),(0,2,4)]),(2,[(3,1,3),(1,180,2),(0,2,4)]),(0,[(3,1,2),(1,177,3),(1,3,5)]),(2,[(3,1,2),(1,177,3),(1,3,5)]),(0,[(3,1,3),(1,180,2),(2,2,5)]),(2,[(3,1,3),(1,180,2),(2,2,5)]),(4,[(1,105,5)]),(0,[(3,1,3),(1,180,2),(2,294,5)]),(2,[(3,1,3),(1,180,2),(2,294,5)]),(3,[(2,294,5)]),(1,[(3,1,3),(1,180,2)]),(6,[(2,294,5)]),(2,[(3,1,2),(0,3,4),(1,126,5)]),(0,[(3,1,2)]),(0,[(0,1,3),(3,89,4),(1,4,5)]),(2,[(0,1,3),(3,89,4),(1,4,5)]),(0,[(3,1,3),(3,180,4),(1,312,5)]),(2,[(3,1,3),(3,180,4),(1,312,5)]),(3,[(1,312,5)]),(6,[(1,312,5)]),(0,[(3,1,2),(1,177,5)]),(2,[(3,1,2),(1,177,5)]),(4,[(3,1,2),(1,177,5)]),(0,[(3,1,2),(1,177,5),(1,3,178)]),(2,[(3,1,2),(1,177,5),(1,3,178)]),(3,[(1,3,178)]),(5,[(1,3,178)]),(0,[(1,2,5),(3,3,58),(3,175,1)]),(2,[(1,2,5),(3,3,58),(3,175,1)]),(9,[(1,2,5),(3,3,58)]),(0,[(3,1,3),(1,180,2),(1,294,5)]),(2,[(3,1,3),(1,180,2),(1,294,5)]),(3,[(1,294,5)]),(5,[(3,1,3),(1,294,5)]),(6,[(1,294,5)]),(0,[(1,1,2),(2,1,5),(2,38,3)]),(2,[(1,1,2),(2,1,5),(2,38,3)]),(5,[(2,1,5),(2,38,3)]),(3,[(2,2,181)]),(6,[(2,2,181)]),(2,[(3,1,3),(1,180,5),(2,2,181)]),(0,[(3,1,3),(1,180,5),(2,2,181)]),(0,[(3,1,2),(1,177,5),(3,3,178)]),(2,[(3,1,2),(1,177,5),(3,3,178)]),(1,[(3,1,2),(3,3,178)]),(3,[(3,3,178)]),(5,[(3,3,178)]),(0,[(2,3,5),(3,257,4)]),(2,[(2,3,5),(3,257,4)]),(9,[(2,3,5),(3,257,4)]),(1,[(0,1,2),(3,257,4)]),(0,[(3,1,3),(0,2,4),(1,180,83)]),(2,[(3,1,3),(0,2,4),(1,180,83)]),(4,[(3,1,3),(1,180,83)]),(14,[(3,1,3)]),(1,[(3,1,3),(0,2,4),(1,180,83)]),(0,[(1,2,3),(0,6,4),(1,6,4)]),(2,[(1,2,3),(0,6,4),(1,6,4)]),(0,[(2,1,4),(3,1,4)]),(0,[(2,1,4),(3,1,4),(2,2,3)]),(2,[(2,1,4),(3,1,4)]),(2,[(2,1,4),(3,1,4),(2,2,3)]),(0,[(3,1,2),(0,3,4),(1,2,126)]),(2,[(0,3,4),(1,2,126)]),(2,[(3,1,2),(0,3,4),(1,2,126)]),(3,[(0,3,4),(1,2,126)]),(1,[(3,1,2),(0,3,4),(1,2,126)]),(4,[(3,1,2),(1,2,126)]),(7,[(3,1,2),(1,2,126)]),(2,[(3,1,2)]),(0,[(1,3,5),(1,2,62),(3,3,34)]),(2,[(1,3,5),(1,2,62),(3,3,34)]),(0,[(3,1,3),(1,2,5),(3,180,58)]),(2,[(3,1,3),(1,2,5),(3,180,58)]),(1,[(3,1,3),(3,180,58)]),(0,[(3,1,2),(2,3,5),(1,257,177)]),(2,[(3,1,2),(2,3,5),(1,257,177)]),(3,[(2,3,5)]),(1,[(3,1,2),(1,257,177)]),(4,[(0,2,3)]),(0,[(2,1,4),(3,1,4),(0,2,3)]),(2,[(2,1,4),(3,1,4),(0,2,3)]),(1,[(3,1,2),(3,3,7)]),(0,[(0,1,4),(1,16,3),(1,3,5)]),(2,[(0,1,4),(1,16,3),(1,3,5)]),(0,[(0,1,4),(1,16,2),(1,86,3)]),(2,[(0,1,4),(1,16,2),(1,86,3)]),(5,[(0,1,4),(1,86,3)]),(3,[(1,16,2),(1,86,3)]),(9,[(1,86,3)]),(6,[(0,1,4),(1,16,2)]),(0,[(2,1,3),(0,2,4),(1,185,83)]),(2,[(2,1,3),(0,2,4),(1,185,83)]),(6,[(0,2,4),(1,185,83)]),(3,[(0,2,4),(1,185,83)]),(1,[(2,1,3),(0,2,4),(1,185,83)]),(4,[(2,1,3),(1,185,83)]),(7,[(2,1,3),(1,185,83)]),(0,[(0,1,2),(1,1,2),(2,4,5)]),(2,[(0,1,2),(1,1,2),(2,4,5)]),(13,[(2,4,5)]),(0,[(0,1,4),(1,16,2),(1,86,5)]),(2,[(0,1,4),(1,16,2),(1,86,5)]),(3,[(1,16,2),(1,86,5)]),(9,[(1,86,5)]),(0,[(2,1,4),(0,2,3),(1,2,3)]),(2,[(2,1,4),(0,2,3),(1,2,3)]),(5,[(2,1,4)]),(11,[(2,1,4)]),(0,[(3,1,2),(1,177,3),(3,3,4)]),(2,[(3,1,2),(1,177,3)]),(2,[(3,1,2),(1,177,3),(3,3,4)]),(4,[(3,1,2),(1,177,3)]),(1,[(3,1,2),(1,177,3),(3,3,4)]),(0,[(1,1,3)]),(2,[(1,1,3)]),(14,[(1,1,3)]),(2,[(0,1,4),(1,16,2),(1,3,5)]),(0,[(0,1,4),(1,16,2)]),(0,[(0,3,4),(1,126,2),(2,2,5)]),(2,[(0,3,4),(1,126,2),(2,2,5)]),(3,[(0,3,4),(1,126,2)]),(2,[(0,1,4),(1,16,5),(1,2,3)]),(4,[(1,16,5),(1,2,3)]),(1,[(0,1,2),(3,3,7)]),(2,[(0,1,4),(1,16,5),(2,2,3)]),(9,[(3,2,4),(2,4,5)]),(2,[(3,2,4),(2,4,5)]),(0,[(3,2,4),(2,4,5)]),(3,[(3,2,4),(2,4,5)]),(12,[(3,2,4),(2,4,5)]),(2,[(0,1,4),(1,16,5),(1,2,47)]),(0,[(0,1,4),(1,16,5),(1,2,47)]),(1,[(0,1,4),(1,2,47)]),(9,[(1,2,47)]),(4,[(2,1,3),(1,186,5)]),(0,[(0,1,4),(1,16,5),(3,3,47)]),(2,[(0,1,4),(1,16,5),(3,3,47)]),(1,[(0,1,4),(3,3,47)]),(9,[(3,3,47)]),(0,[(3,1,4),(1,157,5)]),(2,[(3,1,4),(1,157,5)]),(4,[(1,157,5),(0,2,3)]),(6,[(3,1,4),(1,157,5)]),(4,[(1,157,5)]),(1,[(3,1,4),(0,2,3)]),(0,[(2,2,3),(1,3,4),(3,2,194)]),(2,[(2,2,3),(1,3,4),(3,2,194)]),(0,[(1,1,2),(2,3,5),(3,257,38)]),(2,[(1,1,2),(2,3,5),(3,257,38)]),(1,[(1,1,2),(3,257,38)]),(5,[(2,3,5),(3,257,38)]),(9,[(2,3,5),(3,257,38)]),(0,[(0,1,4),(1,1,4),(2,2,3)]),(2,[(0,1,4),(1,1,4),(2,2,3)]),(9,[(0,38,4)]),(0,[(0,1,4),(0,2,3),(1,16,9)]),(2,[(0,1,4),(0,2,3),(1,16,9)]),(4,[(0,2,3),(1,16,9)]),(1,[(0,1,4),(0,2,3),(1,16,9)]),(0,[(0,3,4),(1,126,2),(1,213,5)]),(2,[(0,3,4),(1,126,2),(1,213,5)]),(5,[(0,3,4),(1,213,5)]),(6,[(1,213,5)]),(0,[(3,1,4),(1,157,2),(1,367,5)]),(2,[(3,1,4),(1,157,2),(1,367,5)]),(3,[(1,367,5)]),(7,[(1,157,2)]),(0,[(0,1,4),(1,2,3),(3,16,6)]),(2,[(0,1,4),(1,2,3),(3,16,6)]),(4,[(1,2,3),(3,16,6)]),(3,[(1,2,3),(3,16,6)]),(6,[(0,1,4),(3,16,6)]),(5,[(0,1,4),(3,16,6)]),(1,[(0,1,4),(1,2,3),(3,16,6)]),(0,[(0,1,3),(1,2,4),(3,89,92)]),(2,[(0,1,3),(1,2,4),(3,89,92)]),(1,[(0,1,4),(1,3,2)]),(0,[(2,2,3),(1,93,3),(1,6,5)]),(2,[(2,2,3),(1,93,3),(1,6,5)]),(9,[(1,157,5)]),(3,[(2,3,2),(3,55,4)]),(0,[(1,3,2),(2,3,5),(3,257,6)]),(2,[(1,3,2),(2,3,5),(3,257,6)]),(5,[(2,3,5),(3,257,6)]),(9,[(1,2,3),(2,2,5)]),(2,[(1,2,3),(2,2,5)]),(4,[(2,1,5),(1,2,3)]),(1,[(3,81,4),(1,2,3)]),(9,[(1,2,3),(2,6,5)]),(2,[(1,2,3),(2,6,5)]),(0,[(1,1,5),(0,2,3),(3,9,152)]),(2,[(1,1,5),(0,2,3),(3,9,152)]),(1,[(0,2,3),(3,9,152)]),(0,[(0,1,4),(2,2,3),(1,93,16)]),(2,[(0,1,4),(2,2,3),(1,93,16)]),(4,[(2,2,3),(1,93,16)]),(6,[(0,1,4),(1,93,16)]),(3,[(2,2,3),(1,93,16)]),(0,[(3,3,4),(2,2,5),(1,287,105)]),(2,[(3,3,4),(2,2,5),(1,287,105)]),(4,[(2,2,3),(1,93,5)]),(9,[(2,2,3),(1,93,5)]),(2,[(1,2,3),(2,4,5)]),(0,[(0,2,3),(3,9,4),(1,4,5)]),(2,[(0,2,3),(3,9,4),(1,4,5)]),(1,[(0,2,3),(3,9,4)]),(3,[(0,2,3),(3,9,4)]),(0,[(3,1,4),(1,157,3),(1,3,5)]),(2,[(3,1,4),(1,157,3),(1,3,5)]),(0,[(3,1,4),(1,157,2)]),(2,[(3,1,4),(1,157,2)]),(0,[(1,1,2),(1,3,4),(0,38,194)]),(2,[(1,1,2),(1,3,4),(0,38,194)]),(9,[(1,3,4),(0,38,194)]),(5,[(1,3,4),(0,38,194)]),(0,[(1,1,4),(0,2,3),(3,9,4)]),(2,[(1,1,4),(0,2,3),(3,9,4)]),(5,[(1,1,4)]),(8,[(0,2,3)]),(0,[(1,1,4),(0,2,3),(1,2,3)]),(2,[(1,1,4),(0,2,3),(1,2,3)]),(11,[(1,1,4)]),(0,[(1,3,5),(2,1,62),(3,1,62)]),(2,[(1,3,5),(2,1,62),(3,1,62)]),(1,[(2,1,62),(3,1,62)]),(0,[(1,3,5),(1,1,62),(3,3,64)]),(2,[(1,3,5),(1,1,62),(3,3,64)]),(1,[(1,1,62),(3,3,64)]),(0,[(1,1,4),(1,3,2),(3,3,17)]),(2,[(1,1,4),(1,3,2),(3,3,17)]),(3,[(1,3,2)]),(5,[(1,1,4),(3,3,17)]),(0,[(1,1,4),(1,2,3),(0,6,17)]),(2,[(1,1,4),(1,2,3),(0,6,17)]),(5,[(1,1,4),(0,6,17)]),(6,[(1,1,4),(0,6,17)]),(0,[(1,2,3),(3,2,4),(1,186,3)]),(2,[(1,2,3),(3,2,4),(1,186,3)]),(5,[(1,186,3)]),(1,[(1,2,3),(3,1,6)]),(10,[]),(0,[(1,1,4),(1,2,3),(3,6,17)]),(2,[(1,1,4),(1,2,3),(3,6,17)]),(0,[(3,1,2),(0,3,4),(1,3,4)]),(2,[(3,1,2),(0,3,4),(1,3,4)]),(16,[(3,1,2)]),(0,[(3,1,4),(1,157,2),(2,367,3)]),(2,[(3,1,4),(1,157,2),(2,367,3)]),(3,[(2,367,3)]),(5,[(3,1,4),(2,367,3)]),(14,[(2,367,3)]),(0,[(1,1,4),(2,3,2),(3,55,17)]),(2,[(1,1,4),(2,3,2),(3,55,17)]),(0,[(2,1,4),(1,227,2),(1,380,3)]),(2,[(2,1,4),(1,227,2),(1,380,3)]),(5,[(2,1,4),(1,380,3)]),(3,[(1,227,2),(1,380,3)]),(9,[(1,380,3)]),(7,[(1,380,3)]),(6,[(2,1,4),(1,227,2)]),(0,[(2,1,4),(1,227,2),(2,380,3)]),(2,[(2,1,4),(1,227,2),(2,380,3)]),(9,[(2,380,3)]),(5,[(2,1,4),(2,380,3)]),(0,[(0,1,3),(1,89,2),(1,293,5)]),(2,[(0,1,3),(1,89,2),(1,293,5)]),(5,[(0,1,3),(1,293,5)]),(3,[(1,89,2),(1,293,5)]),(9,[(1,293,5)]),(6,[(1,293,5)]),(0,[(2,1,4),(0,2,3),(1,227,9)]),(2,[(2,1,4),(0,2,3),(1,227,9)]),(6,[(2,1,4)]),(0,[(2,1,4),(1,2,3),(3,227,6)]),(2,[(2,1,4),(1,2,3),(3,227,6)]),(5,[(2,1,4),(3,227,6)]),(3,[(1,2,3),(3,227,6)]),(6,[(2,1,4),(3,227,6)]),(0,[(3,1,3),(1,2,4),(3,180,92)]),(2,[(3,1,3),(1,2,4),(3,180,92)]),(0,[(2,1,4),(2,2,3),(1,227,93)]),(2,[(2,1,4),(2,2,3),(1,227,93)]),(2,[(2,1,4)]),(0,[(2,1,4)]),(0,[(1,2,3),(0,1,6),(1,6,5)]),(1,[(1,2,3),(0,1,6)]),(0,[(3,1,4),(1,157,5),(3,3,158)]),(2,[(3,1,4),(1,157,5),(3,3,158)]),(1,[(3,1,4),(3,3,158)]),(3,[(3,3,158)]),(7,[(3,3,158)]),(1,[(0,1,4),(2,2,47)]),(2,[(0,1,4),(1,16,5),(2,2,47)]),(0,[(0,1,4),(1,16,5),(2,2,47)]),(0,[(3,1,4),(1,157,2),(2,2,5)]),(2,[(3,1,4),(1,157,2),(2,2,5)]),(0,[(3,1,4),(1,157,2),(1,367,3)]),(2,[(3,1,4),(1,157,2),(1,367,3)]),(3,[(1,367,3)]),(5,[(3,1,4),(1,367,3)]),(6,[(3,1,4),(1,157,2)]),(0,[(3,1,4),(1,157,2),(2,367,5)]),(2,[(3,1,4),(1,157,2),(2,367,5)]),(3,[(2,367,5)]),(1,[(3,1,4),(1,157,2)]),(0,[(3,1,3),(3,180,4),(1,312,2)]),(2,[(3,1,3),(3,180,4),(1,312,2)]),(3,[(1,312,2)]),(6,[(1,312,2)]),(4,[(1,157,5),(1,2,3)]),(1,[(3,1,4),(1,2,3)]),(0,[(1,2,3),(0,1,6),(1,1,6)]),(2,[(1,2,3),(0,1,6),(1,1,6)]),(0,[(3,1,4),(0,2,3),(1,2,3)]),(2,[(3,1,4),(0,2,3),(1,2,3)]),(11,[(3,1,4)]),(0,[(2,1,3),(3,185,4),(1,392,2)]),(2,[(2,1,3),(3,185,4),(1,392,2)]),(5,[(2,1,3),(3,185,4)]),(3,[(3,185,4),(1,392,2)]),(9,[(1,392,2)]),(1,[(2,1,3),(0,4,62)]),(0,[(3,1,4),(1,2,3),(3,157,6)]),(2,[(3,1,4),(1,2,3),(3,157,6)]),(5,[(3,1,4),(3,157,6)]),(6,[(3,1,4),(3,157,6)]),(1,[(3,257,4)]),(1,[(3,3,58)]),(0,[(1,3,5),(0,2,62)]),(2,[(1,3,5),(0,2,62)]),(6,[(0,2,62)]),(1,[(0,2,62)]),(1,[(2,1,62)]),(7,[(1,1,58)]),(1,[(0,1,58)]),(0,[(3,3,4),(1,2,5)]),(2,[(3,3,4),(1,2,5)]),(0,[(2,3,4),(1,232,2)]),(2,[(2,3,4),(1,232,2)]),(1,[(2,3,4),(1,232,2)]),(0,[(1,2,4),(3,3,92)]),(0,[(0,2,4),(1,3,5)]),(2,[(0,2,4),(1,3,5)]),(0,[(3,3,4),(1,105,1)]),(2,[(3,3,4),(1,105,1)]),(0,[(2,2,3),(1,4,5)]),(2,[(2,2,3),(1,4,5)]),(1,[(2,2,3)]),(0,[(2,2,3),(1,3,5)]),(2,[(2,2,3),(1,3,5)]),(0,[(3,1,2),(2,4,5)]),(2,[(3,1,2),(2,4,5)]),(0,[(3,1,2),(1,4,5)]),(2,[(3,1,2),(1,4,5)]),(1,[(0,4,152)]),(0,[(3,1,2),(1,3,5)]),(2,[(3,1,2),(1,3,5)]),(0,[(3,1,2),(3,3,4)]),(2,[(3,1,2),(3,3,4)]),(0,[(1,2,3),(2,6,5)]),(0,[(1,1,2),(1,4,5)]),(2,[(1,1,2),(1,4,5)]),(0,[(3,1,2),(1,3,4)]),(2,[(1,3,4)]),(2,[(3,1,2),(1,3,4)]),(0,[(2,1,3),(1,3,5)]),(2,[(2,1,3),(1,3,5)]),(0,[(3,1,4),(1,2,5)]),(2,[(3,1,4),(1,2,5)]),(0,[(0,1,2),(0,3,4)]),(2,[(0,1,2),(0,3,4)]),(1,[(0,1,2),(0,3,4)]),(0,[(2,2,3),(2,4,5)]),(2,[(2,2,3),(2,4,5)]),(0,[(2,1,3),(1,3,4)]),(2,[(2,1,3),(1,3,4)]),(0,[(2,1,3),(2,2,5)]),(2,[(2,1,3),(2,2,5)]),(0,[(1,1,4)]),(0,[(1,1,4),(2,2,3)]),(2,[(1,1,4)]),(2,[(1,1,4),(2,2,3)]),(0,[(2,1,3),(1,2,3)]),(2,[(2,1,3),(1,2,3)]),(0,[(0,1,4),(1,2,5)]),(2,[(0,1,4),(1,2,5)]),(0,[(0,1,2),(1,3,4)]),(2,[(0,1,2),(1,3,4)]),(0,[(1,1,5)]),(0,[(1,2,3),(1,1,6)]),(2,[(1,2,3),(1,1,6)]),(0,[(3,3,4),(3,105,1)]),(2,[(3,3,4),(3,105,1)]),(0,[(0,1,2),(1,3,5)]),(2,[(0,1,2),(1,3,5)]),(0,[(1,1,3),(3,3,4)]),(2,[(1,1,3),(3,3,4)]),(0,[(1,1,2),(2,4,5)]),(2,[(1,1,2),(2,4,5)]),(0,[(1,1,3),(0,2,4)]),(2,[(1,1,3),(0,2,4)]),(1,[(1,1,3)]),(1,[(0,2,4)]),(2,[(3,1,3)]),(0,[(3,1,3)]),(1,[(3,1,3)]),(4,[(2,2,5)]),(0,[(3,1,3),(2,2,5)]),(2,[(3,1,3),(2,2,5)]),(0,[(0,1,2),(3,3,4)]),(2,[(0,1,2),(3,3,4)]),(0,[(0,1,2),(1,4,5)]),(2,[(0,1,2),(1,4,5)]),(0,[(1,1,2),(2,38,5)]),(2,[(1,1,2),(2,38,5)]),(9,[(2,38,5)]),(0,[(1,1,4),(1,2,3)]),(2,[(1,1,4),(1,2,3)]),(6,[(1,1,4)]),(2,[(2,1,5),(2,2,3)]),(0,[(2,1,3),(2,2,3)]),(2,[(2,1,3),(2,2,3)]),(0,[(1,2,3),(2,4,5)]),(1,[(3,1,3),(3,180,4)]),(2,[(2,1,5),(0,2,4)]),(2,[(2,1,5),(3,3,4)]),(0,[(0,1,2),(2,4,5)]),(2,[(0,1,2),(2,4,5)]),(2,[(2,4,5)]),(0,[(2,4,5)]),(0,[(1,1,5),(1,2,3)]),(2,[(1,1,5),(1,2,3)]),(0,[(0,1,3)]),(0,[(0,1,3),(2,2,4)]),(2,[(0,1,3)]),(2,[(2,2,4)]),(0,[(2,2,4)]),(2,[(0,1,3),(2,2,4)]),(9,[(2,2,4)]),(15,[(0,1,3)]),(0,[(1,1,2),(1,2,4)]),(2,[(1,1,2),(1,2,4)]),(0,[(1,1,2),(1,2,3)]),(2,[(1,1,2),(1,2,3)]),(4,[(1,16,2)]),(0,[(0,1,3),(2,2,5)]),(2,[(0,1,3),(2,2,5)]),(0,[(1,1,2),(1,2,5)]),(2,[(1,1,2),(1,2,5)]),(0,[(1,1,2),(1,3,5)]),(2,[(1,1,2),(1,3,5)]),(0,[(1,4,5),(3,3,7)]),(1,[(3,3,7)]),(0,[(0,1,4),(2,2,5)]),(2,[(0,1,4),(2,2,5)]),(0,[(2,1,3),(0,2,4)]),(2,[(2,1,3),(0,2,4)]),(12,[(0,2,4)]),(1,[(2,1,3),(0,2,4)]),(0,[(1,1,2),(1,3,4)]),(2,[(1,1,2),(1,3,4)]),(0,[(1,1,2),(3,3,4)]),(2,[(1,1,2),(3,3,4)]),(16,[(1,1,2)]),(0,[(3,3,4),(3,105,2)]),(2,[(3,3,4),(3,105,2)]),(2,[(2,1,3),(2,4,5)]),(12,[(2,4,5)]),(0,[(1,2,5),(3,1,58)]),(2,[(1,2,5),(3,1,58)]),(1,[(3,1,58)]),(0,[(1,1,3),(3,3,2)]),(2,[(1,1,3),(3,3,2)]),(4,[(3,3,2)]),(0,[(2,1,3),(1,2,4)]),(2,[(2,1,3),(1,2,4)]),(12,[(1,2,4)]),(0,[(0,2,3),(2,4,5)]),(2,[(0,2,3),(2,4,5)]),(1,[(2,1,4),(3,1,4)]),(1,[(0,4,58)]),(6,[(2,105,5)]),(0,[(1,1,3),(2,2,5)]),(2,[(1,1,3),(2,2,5)]),(0,[(2,1,3),(1,185,5)]),(2,[(2,1,3),(1,185,5)]),(6,[(1,185,5)]),(6,[(3,6,4)]),(1,[(0,1,3),(3,89,4)]),(1,[(0,1,4),(1,1,4)]),(0,[(0,1,4),(0,2,3)]),(2,[(0,1,4),(0,2,3)]),(0,[(1,1,5),(0,2,3)]),(2,[(1,1,5),(0,2,3)]),(0,[(0,1,4),(1,2,3)]),(2,[(0,1,4),(1,2,3)]),(0,[(0,1,4),(2,2,3)]),(2,[(0,1,4),(2,2,3)]),(0,[(1,3,2)]),(0,[(1,3,2),(3,3,4)]),(2,[(1,3,2)]),(2,[(1,3,2),(3,3,4)]),(4,[(1,3,2)]),(0,[(1,1,4),(3,3,17)]),(2,[(1,1,4),(3,3,17)]),(1,[(1,1,4),(3,3,17)]),(0,[(2,1,4),(1,227,2)]),(2,[(2,1,4),(1,227,2)]),(0,[(2,1,4),(0,2,3)]),(2,[(2,1,4),(0,2,3)]),(1,[(1,81,2)]),(0,[(3,1,2),(0,3,4)]),(2,[(3,1,2),(0,3,4)]),(0,[(1,2,3),(2,6,4)]),(2,[(1,2,3),(2,6,4)]),(0,[(2,1,4),(1,2,3)]),(2,[(2,1,4),(1,2,3)]),(0,[(2,1,3),(1,4,5)]),(2,[(2,1,3),(1,4,5)]),(12,[(1,4,5)]),(0,[(2,1,4),(2,2,3)]),(2,[(2,1,4),(2,2,3)]),(4,[(1,157,2)]),(0,[(3,1,4),(0,2,3)]),(2,[(3,1,4),(0,2,3)]),(1,[(3,1,4)]),(1,[(1,257,2)]),(0,[(3,1,4),(1,2,3)]),(2,[(3,1,4),(1,2,3)]),(0,[(0,3,4),(2,2,5)]),(2,[(0,3,4),(2,2,5)]),(0,[(2,1,3),(3,2,4)]),(2,[(2,1,3),(3,2,4)]),(12,[(3,2,4)]),(0,[(1,1,5),(3,3,152)]),(2,[(1,1,5),(3,3,152)]),(1,[(3,3,152)]),(0,[(3,1,4),(2,2,3)]),(2,[(3,1,4),(2,2,3)]),(1,[(3,1,4),(2,2,3)]),(0,[(1,1,5),(2,2,3)]),(2,[(1,1,5),(2,2,3)]),(0,[(1,1,5),(0,2,4)]),(2,[(1,1,5),(0,2,4)]),(0,[(1,1,5),(3,3,4)]),(2,[(1,1,5),(3,3,4)]),(14,[(1,1,5)]),(2,[(3,3,4),(2,2,5)]),(1,[(3,81,4)]),(0,[(2,1,5),(0,2,3)]),(2,[(2,1,5),(0,2,3)]),(0,[(2,1,5),(1,2,3)]),(2,[(2,1,5),(1,2,3)]),(0,[(1,1,3),(2,2,4)]),(0,[(0,2,3),(1,4,5)]),(2,[(0,2,3),(1,4,5)]),(0,[(1,2,3),(2,1,6)]),(2,[(1,2,3),(2,1,6)]),(0,[(1,2,3),(1,2,4)]),(2,[(1,2,3),(1,2,4)]),(0,[(2,1,3),(1,2,5)]),(2,[(2,1,3),(1,2,5)]),(12,[(1,2,5)]),(1,[(1,3,2)]),(0,[(1,2,3),(2,2,5)]),(0,[(1,1,4),(0,2,3)]),(2,[(1,1,4),(0,2,3)]),(0,[(2,2,3),(1,3,4)]),(2,[(2,2,3),(1,3,4)]),(15,[(3,1,3)])] : List PoolSpec)).map some)
def B_22_2 : BT (List (List Nat)) := BT.empty
lemma B_22_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 2 xs.toFinset) B_22_2 := .empty
def P_22_3 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 []
def N_22_3 : List NodeSpec := [([13,0,4,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_3 : checkNodesBT W_22 g_22 F_22 P_22_3 A_22 B_22_2 3 N_22_3 = true := by decide +kernel
def B_22_3 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_3
set_option maxRecDepth 500000 in
lemma B_22_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 3 xs.toFinset) B_22_3 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_2_ok C_22_3
def P_22_4 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 []
def N_22_4 : List NodeSpec := [([14,15,0,4,5],[],[0]),([0,11,12,4,5],[],[0]),([18,0,21,24,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_4 : checkNodesBT W_22 g_22 F_22 P_22_4 A_22 B_22_3 4 N_22_4 = true := by decide +kernel
def B_22_4 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_4
set_option maxRecDepth 500000 in
lemma B_22_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 4 xs.toFinset) B_22_4 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_3_ok C_22_4
def P_22_5 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def N_22_5 : List NodeSpec := [([14,0,1,10,4,5],[0,1],[0]),([0,1,10,12,4,5],[],[0]),([0,11,1,10,4,5],[],[0]),([15,0,1,10,4,5],[0,1],[0]),([0,1,27,6,5,7],[2],[]),([28,0,1,6,4,5],[],[]),([0,1,26,6,29,7],[2],[]),([0,1,6,4,5,30],[],[]),([0,1,6,4,31,29],[],[]),([33,0,1,6,4,29],[],[]),([35,0,1,6,4,37],[3],[]),([43,0,1,2,4,5],[],[]),([44,18,0,2,24,5],[2],[0]),([0,1,6,4,46,29],[],[]),([20,18,0,2,24,5],[4,5],[0]),([20,18,0,21,6,5],[6],[]),([35,0,1,6,4,47],[2],[]),([49,0,1,6,4,5],[],[]),([20,23,18,0,6,5],[5,6,7],[]),([0,1,50,6,4,5],[8],[]),([20,0,52,2,5],[2,9,10,11,12,13],[]),([0,1,54,6,4,5],[],[]),([20,56,18,0,2,5],[5],[]),([57,18,0,6,5],[2,6,14,15],[]),([45,0,1,6,29,7],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_5 : checkNodesBT W_22 g_22 F_22 P_22_5 A_22 B_22_4 5 N_22_5 = true := by decide +kernel
def B_22_5 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_5
set_option maxRecDepth 500000 in
lemma B_22_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 5 xs.toFinset) B_22_5 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_4_ok C_22_5
def P_22_6 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [0,1,2,3,4,5,6,7,8,14,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136]
def N_22_6 : List NodeSpec := [([61,60,0,1,2,4,5],[2],[]),([65,0,2,66,3,4,5],[2],[]),([35,0,67,1,6,4,5],[2,16],[]),([68,35,0,1,6,4,5],[2],[]),([0,71,1,70,6,4,5],[2,16,17,18],[]),([74,0,1,9,5],[2,19,20,21,22],[]),([75,0,1,72,5],[2,23,24,25,26],[]),([0,1,9,6,4,5,31],[8,27,28],[0]),([77,0,32,4,5],[2,16,29,30],[]),([78,0,9,4,5],[2,16,29],[]),([45,0,1,9,6,5,7],[2,31,32],[0]),([0,1,9,6,4,5,46],[33,34,35,36],[0]),([0,1,79,4,29],[2,37,38,39],[]),([0,1,6,4,29,80],[2,22,40],[]),([0,1,2,82,4,84,62],[41,42],[]),([0,1,26,6,4,5,29],[25,31],[0]),([88,0,1,2,4,47,62],[43],[]),([0,90,91,92,5],[44,45,46,47,48,49],[]),([0,1,2,3,4,94,62],[43],[]),([0,1,2,3,4,47,34],[50,51],[]),([0,2,91,4,96,5,58],[52,53],[]),([0,1,6,4,47,29],[2,25,31,54,55],[]),([0,48,6,17,5],[56,57,58,59,60,61,62],[]),([0,1,2,3,4,98,47],[51,63],[]),([99,0,1,70,5],[2,64,65,66,67,68],[]),([0,1,2,3,100,47,34],[25,42,69,70],[]),([0,1,48,6,4,5,34],[18,58,59,62,71],[0]),([0,1,6,4,5,87,101],[72,73],[]),([0,1,2,103,4,84,62],[43,74],[]),([0,1,6,4,47,58,101],[7,73],[]),([20,0,51,2,5],[2,5,75,76,77,78,79],[0]),([0,1,6,4,5,47,104],[80],[]),([0,1,6,4,5,104],[25,80,81,82,83],[]),([105,0,1,2,3,106,108],[84],[]),([60,0,109,1,2,4,5],[2,16],[]),([0,1,27,6,4,5],[2,18,83,85],[0]),([45,0,1,6,4,5,29],[31],[0]),([22,0,110,3,5],[6,7,86,87,88],[]),([112,0,1,2,3,4,47],[89],[]),([113,0,1,70,6,4,5],[2],[]),([35,0,16,1,6,4,5],[2,16,90],[0]),([0,107,38,3,4,114,62],[91,92,93],[]),([115,0,1,6,4,47,62],[7],[]),([0,1,10,4,5],[0,1,94,95],[0]),([20,18,0,2,6,5],[2,5,6,7,96],[0]),([116,0,2,3,4,47,34],[50,70],[]),([0,1,119,3,4,58,118],[7],[]),([35,0,1,36,6,4,5],[3,97],[0]),([115,0,1,6,4,5,101],[8],[]),([18,0,9,6,5],[2,6,14,22,98,99,100],[0]),([120,121,0,1,3,4,5],[],[1]),([0,1,9,6,4,47,34],[2,18,59,101],[0]),([122,0,1,2,4,40,62],[43],[]),([123,0,1,2,3,4,5],[],[]),([0,1,2,125,4,58,127],[43],[]),([0,1,2,6,4,129,47],[7],[]),([0,1,2,3,4,31,34],[51],[]),([0,1,119,3,4,5,130],[],[1]),([105,0,1,2,3,131,5],[102],[]),([25,0,1,6,4,29,7],[2,16,39,40],[0]),([0,1,2,3,4,132,118],[8,51],[]),([133,0,1,2,3,4,118],[89,103],[]),([137,136,0,2,3,4,5],[2],[]),([0,1,53,9,6,4,5],[8,104,105],[0]),([0,1,2,138,4,139,58],[42],[]),([0,1,2,6,4,47,62],[7],[]),([44,20,18,0,2,3,5],[2,6],[0,1]),([0,1,2,140,4,47,62],[43],[]),([0,1,2,3,4,47,141],[50,51],[]),([0,1,2,143,4,47,62],[7],[]),([115,144,0,1,3,4,5],[],[]),([145,18,0,2,3,5],[2,4,5,6,7,106],[]),([18,0,2,21,3,5],[2,4,106,107],[1]),([20,55,18,0,2,5],[2,5,6,7,108],[0]),([20,18,0,2,21,3,5],[2,7],[0,1]),([0,1,9,6,4,146,7],[2,18,59,109],[]),([44,18,0,2,3,5],[2,4,106,110,111],[0,1]),([147,18,0,3,5],[5,6,112,113,114,115],[]),([33,0,1,9,6,4,5],[33,34,116,117],[0]),([20,23,18,0,2,3,5],[2],[0,1]),([0,1,2,6,4,31,62],[7],[]),([18,0,2,149,5],[6,7,118,119],[]),([0,1,26,9,6,5,7],[2,120],[0]),([57,18,0,2,3,5],[4,5,6,106,110,121],[0]),([150,35,0,1,6,4,5],[3,122],[]),([151,18,0,2,3,5],[2,4,5,6,106,110,123],[]),([0,1,6,4,154,5],[18,83,124,125,126],[]),([25,0,156,4,5],[2,16,127,128,129,130],[]),([123,0,1,9,6,4,5],[8,131],[0]),([0,1,6,4,158,29],[2,25,40,132],[]),([20,18,0,2,3,5],[2,4,6,7,106,133],[]),([0,1,6,4,146,29],[2,39,134],[]),([0,32,1,6,4,29,7],[2,16,39,40,135,136],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_6 : checkNodesBT W_22 g_22 F_22 P_22_6 A_22 B_22_5 6 N_22_6 = true := by decide +kernel
def B_22_6 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_6
set_option maxRecDepth 500000 in
lemma B_22_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 6 xs.toFinset) B_22_6 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_5_ok C_22_6
def P_22_7 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [2,3,4,5,6,7,8,14,16,17,18,22,25,29,31,33,34,39,40,42,43,47,50,51,53,55,58,59,63,65,69,70,72,73,80,83,84,89,91,92,93,103,106,122,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536]
def N_22_7 : List NodeSpec := [([0,1,2,3,159,4,5],[16,42,43,89,103,137,138,139],[]),([0,1,2,3,4,161,127],[8,25,140,141,142,143,144],[]),([85,0,1,2,3,4,84,62],[2,145,146],[0,1]),([93,0,1,163,4,5],[25,147,148,149],[0]),([0,1,2,164,4,5,62],[7,25,150],[]),([0,165,1,2,3,100,4,5],[50,51,69,139,151,152],[]),([74,0,1,2,3,5],[2,153,154,155,156],[0]),([0,1,53,2,3,6,4,5],[8,25,42,50,157],[0]),([0,1,26,2,3,4,5,34],[25,42,51,158,159],[0]),([0,1,26,2,6,4,5,62],[25,42,145,160,161],[0]),([0,166,1,2,3,4,5,80],[2,50,51,139,162],[]),([0,32,1,2,3,100,4,5],[50,51,163,164,165,166],[]),([0,1,2,3,6,4,146,7],[2,16,167,168],[0]),([45,0,1,2,3,4,5,34],[51,138,165],[]),([45,0,1,2,6,4,5,62],[169,170,171],[]),([0,1,9,6,100,4,5],[18,22,33,34,59,172,173,174,175],[]),([35,0,1,6,4,5],[2,3,16,122,176,177],[0]),([0,1,70,6,4,5],[2,8,16,17,18,65,178,179,180],[0]),([75,0,1,6,4,5],[2,8,25,181,182],[0]),([0,1,9,72,73,5],[2,18,22,183,184,185,186],[0]),([0,1,9,6,4,5,80],[2,22,33,187,188,189,190],[0]),([65,0,2,3,4,5],[2,16,25,191,192,193,194],[0,1]),([167,25,0,1,9,6,4,5],[16,18,22,174,195],[]),([0,1,83,168,3,4,5,62],[8,16,196,197],[1]),([0,1,9,6,4,5,169],[2,18,34,174,186,198,199,200,201],[]),([0,1,26,9,6,4,5],[2,18,31,33,34,59,161,174,186,202],[0]),([155,25,0,9,4,5],[16,59,174,203,204,205],[0]),([0,1,156,6,4,5],[2,16,59,206,207,208],[0]),([0,1,9,6,170,4,5],[16,33,34,174,209,210],[]),([77,0,1,6,4,5],[2,8,16,29],[0]),([0,32,9,76,4,5],[16,59,174,211,212,213],[0]),([0,1,9,6,4,5,146],[2,18,34,186,214,215,216,217],[0]),([0,1,6,4,29,7],[2,16,25,39,40,135,136],[0]),([171,0,1,6,4,29],[2,22,25,39,218,219,220],[]),([0,1,72,6,4,5,29],[2,22,40,55,220,221],[0]),([25,0,1,6,4,5,29],[16,25,39,40,55,201,220,221,222,223,224,225],[0]),([0,32,1,6,4,5,29],[16,25,39,40,55,217,220,221,222,226,227],[0]),([172,0,1,6,4,5,29],[2,16,25,39,55,220,221,222,228],[]),([0,1,6,4,5,29,173],[2,25,40,80,220,221,229],[]),([0,1,2,3,6,174,4,5],[7,51,230,231,232],[]),([25,0,1,9,6,4,5,7],[2,16,59,174,186,233,234,235],[0]),([0,1,9,6,174,4,5],[2,16,18,31,33,34,59,174,232,236,237,238],[]),([0,1,2,3,4,5,104],[25,73,80,89,137,138,139,239,240],[0]),([93,0,1,86,3,4,5,62],[25,103],[1]),([175,176,0,1,4,5],[25,42,241,242,243],[]),([78,0,2,3,4,5],[2,16,244],[0]),([0,16,1,2,6,4,5,62],[2,16,25,103,145],[0]),([0,1,9,79,4,5],[2,245,246,247,248],[0]),([93,0,1,3,4,5,87],[43,103,249],[]),([105,0,107,38,3,4,5,62],[92,93,250,251,252,253,254],[0]),([0,1,2,3,4,178,127],[140,141,143,255,256],[]),([0,1,2,179,4,5,181],[2,8,257,258,259,260],[]),([93,0,1,3,4,47,58],[7,25,42,73,261,262],[1]),([0,1,2,182,4,5,127],[2,141,143,263,264,265,266],[]),([184,0,1,2,3,4,5,62],[138,139,267,268],[]),([0,1,119,2,3,4,5,118],[7,8,51,103,269,270,271,272,273],[0]),([0,1,2,38,3,4,114,62],[274,275],[0]),([0,2,90,91,4,5],[2,47,53,276,277,278,279,280,281],[0]),([185,0,1,2,3,4,187,58],[282,283,284],[]),([120,0,1,2,3,4,5,118],[8,103],[0]),([85,0,1,2,3,4,188,5],[103,285],[]),([189,0,1,2,3,4,58,127],[2,143,286],[1]),([0,1,2,3,4,5,40,42],[16,43,103,287,288,289,290],[1]),([0,1,2,3,4,5,98],[2,8,25,42,63,89,137,139,291,292],[]),([0,1,2,3,4,58,118],[8,16,51,269,293,294,295],[0,1]),([45,0,1,2,3,6,5,7],[2,138,296,297],[0]),([142,0,1,86,3,4,5,62],[25,103],[1]),([0,191,1,2,3,4,5,34],[25,42,50,51,158,298],[0]),([192,105,0,1,2,3,4,58],[103,299,300,301,302],[]),([93,0,1,3,4,5,47,87],[7,73,303],[]),([123,0,1,2,3,4,5,34],[2,25,42,50,158],[]),([193,0,1,2,3,4,5,127],[2,304],[]),([0,107,38,126,194,5],[253,305,306,307,308,309,310,311],[1]),([162,0,1,2,3,4,108],[8,42,50,84,312],[]),([115,0,1,2,3,4,47,62],[7,72,313],[0,1]),([167,0,32,1,9,6,4,5],[16,18,22,59,314,315,316],[]),([0,1,2,3,4,197,195],[8,25,50,317,318,319],[]),([0,1,2,3,4,5,198],[2,25,50,89,137,139,319,320,321],[]),([0,1,2,3,4,47,29],[25,50,73,322,323,324,325],[0]),([105,0,1,2,3,4,114,108],[42,51,326,327,328],[]),([105,0,107,38,3,5,7],[70,92,253,254,329,330],[]),([0,107,38,3,4,5,127],[141,143,253,311,331,332,333],[]),([0,1,2,3,6,4,5,47],[2,7,16,43,73,103,334],[0,1]),([18,0,148,2,3,5],[2,4,6,7,106,335,336],[0,1]),([199,0,1,2,3,4,5,80],[2,50],[]),([0,1,2,3,4,178,201],[42,43,256,337,338],[]),([0,1,2,3,4,202,5,62],[139,339],[]),([0,1,2,3,4,5,84,203],[2,340],[]),([33,0,1,2,3,6,4,5],[138,139,296,341,342],[0]),([0,107,1,2,3,4,114,62],[16,25,327,343,344,345,346,347,348],[0]),([190,0,1,2,4,5,62],[2,25,43,169,349,350],[]),([8,0,1,9,4,5],[16,186,351,352,353],[0]),([0,1,2,3,4,204,47],[7,42,63,73,322,354,355],[1]),([0,107,205,3,4,5],[254,303,356,357,358,359],[]),([0,1,2,3,4,5,203],[2,89,137,138,360,361,362,363],[]),([171,175,0,1,2,4],[2,42,364,365,366],[]),([105,0,1,2,3,4,108,62],[25,84,327,367,368],[]),([0,1,48,6,4,5],[2,18,58,59,80,83,369,370,371,372,373,374],[0]),([177,0,1,3,4,188,5,62],[25,375,376,377],[]),([0,1,2,3,4,5,84,198],[2,25,378],[]),([0,1,2,3,4,108,127],[42,50,140,142,143,328,368],[]),([0,1,2,206,194,5],[306,379,380,381,382,383,384,385,386],[1]),([0,1,2,3,4,47,58,34],[2,25,42,294,387,388],[]),([0,1,2,3,95,4,195,58],[389,390,391,392],[]),([0,107,38,3,4,5,114],[93,251,311,332,393,394,395,396,397],[0]),([0,1,2,168,3,183,4,5],[51,103,169,196,398],[]),([175,0,1,2,3,4,47],[7,42,50,322,334],[0]),([0,16,1,2,3,4,207,62],[16,25,145,399],[0,1]),([185,186,0,1,2,208,3,5],[400,401],[]),([105,0,1,2,3,108,7],[42,84,329],[0]),([209,0,1,2,3,4,5,34],[51,138,139,151],[]),([99,69,0,1,9,5],[16,186,402],[0]),([162,210,0,1,2,3,5],[8,50,149,312,403,404,405],[]),([0,1,2,3,4,211,5,62],[8,348,406],[1]),([212,0,107,38,3,4,5,62],[93,311,407],[0]),([0,107,38,3,183,4,5,62],[92,93,145,250,311,408],[1]),([0,1,6,4,152,29],[2,22,25,40,409,410],[]),([0,1,2,3,4,211,5],[42,70,89,137,285,406],[]),([189,0,1,2,3,4,5,214],[50,103,141,143,411],[]),([0,1,9,6,4,5,158],[2,22,33,34,174,412,413,414,415],[0]),([162,0,107,38,3,4,5],[8,92,149,254,332,394,416,417,418],[]),([175,0,1,215,4,5],[25,42,419,420],[]),([105,0,107,1,2,3,106,5],[25,70,404,421,422],[0]),([122,0,1,2,3,4,5,40],[16,43,51,423],[0,1]),([0,1,2,3,4,5,47,94],[303],[]),([0,16,1,9,6,4,5,34],[2,16,18,59,158,186,424],[0]),([0,1,2,3,6,4,5,31],[7,8,25,42,159,425],[0,1]),([116,0,16,2,3,4,5,34],[16,50,70,103,152,298],[0]),([0,1,216,2,3,4,5],[2,16,137,138,139,349,426],[]),([105,217,0,1,2,3,5],[25,42,329,404],[]),([0,1,2,3,4,114,108],[16,42,50,326,393,427],[]),([0,16,1,2,3,4,5,34],[16,50,51,103,139,158,231,428],[0]),([0,1,218,2,3,4,5],[8,16,42,43,89,137,138,139],[]),([0,1,2,3,6,4,5,46],[2,138,165,341,342],[0]),([0,1,2,219,3,183,4,5],[51,103,169,303,429,430],[]),([212,0,1,2,3,4,108,62],[25,328],[]),([0,1,2,3,4,5,47,104],[80,431,432],[0]),([0,1,9,6,4,5,47],[2,16,22,33,59,73,433,434,435,436],[0]),([0,1,2,6,4,47,62],[2,7,25,437,438],[0,1]),([0,1,2,3,6,4,47,58],[2,7,42,73,167,439],[]),([0,1,83,2,82,4,5,62],[16,25,80,440,441,442],[0]),([0,1,2,3,4,5,94],[16,43,73,89,137,138,139,303,443],[0]),([0,1,26,2,3,6,5,7],[2,25,42],[0]),([0,1,2,3,4,47,58,101],[7,73,80,261,388,444],[0,1]),([105,0,1,220,3,4,5,58],[25,445,446],[]),([0,1,2,221,3,4,5,127],[2,103,447],[1]),([0,1,2,6,4,5,47,101],[7,73,80],[0]),([0,32,1,9,6,4,5,7],[2,16,31,59,174,186,448,449,450,451,452],[0]),([115,0,1,3,6,4,5,47],[2,7,73,103],[0,1]),([0,1,2,3,4,47,34],[2,25,42,50,51,156,322,453,454],[0]),([45,0,1,9,6,4,5],[2,18,31,33,34,59,171,174,186,455],[0]),([189,0,2,38,3,4,5,127],[2,25,456],[]),([0,1,2,3,6,4,47,34],[2,25,42,167,168],[0]),([93,18,0,2,3,5],[2,4,6,7,14,106,457,458,459],[1]),([185,0,1,2,3,4,188,5],[42,50,103,139,285,375],[]),([0,1,2,3,4,5,47,111],[2,322,431,432,460],[0]),([97,0,1,2,3,4,5,47],[16],[0]),([93,0,1,2,3,4,47,62],[7,25,72,441,461,462],[0]),([0,1,2,138,4,5,139],[16,50,463,464,465,466],[0]),([142,0,1,2,3,4,47,62],[25,441,461,467],[0]),([0,1,2,3,4,5,87,101],[16,72,73,103,468,469],[0]),([0,1,2,3,4,207,47],[16,50,73,322,457,470,471],[0]),([20,18,0,2,3,5],[2,4,5,6,7,106,472,473,474],[0]),([115,0,1,2,3,4,5,101],[8,16,72,475],[0]),([88,0,1,2,3,4,5,47],[16,25,303,334],[0,1]),([175,0,1,86,3,4,5],[50,103,476,477,478],[]),([22,18,0,2,3,5],[2,4,6,7,106,479,480,481],[0,1]),([0,1,2,222,3,4,5,47],[2,103,334],[0,1]),([157,0,1,6,4,5,29],[2,22,25,40,220,221],[0]),([18,0,2,110,3,5],[2,6,7,482,483],[0,1]),([18,0,9,2,3,5],[4,5,6,7,106,484,485,486,487],[0]),([18,0,2,3,6,5],[2,7,156,488,489,490],[0,1]),([0,2,48,3,17,5],[491,492,493,494,495,496,497],[0]),([0,16,9,6,17,5],[22,59,174,494,498,499,500],[0]),([0,16,1,6,4,5,29],[2,16,25,39,55,220,221,435],[0]),([177,0,1,2,3,4,114,62],[16,91,345,501,502],[]),([223,0,1,3,6,4,5],[2,42,43],[]),([123,0,1,2,3,4,5],[8,25,42,89,137,138,139,454,503],[]),([0,16,1,2,3,100,5,34],[16,25,42,69,70,103,152],[0]),([0,224,1,2,3,4,5,62],[16,43,50,467,504],[0]),([123,0,1,2,3,6,4,5],[8,25,42,50,503],[0]),([0,1,225,3,4,5,58],[16,42,262],[]),([123,0,1,2,3,4,5,58],[2,8,25,387,505],[]),([60,0,1,2,4,5],[2,25,42,506,507,508,509],[0]),([0,1,225,2,3,4,5,62],[16,25,43,510],[0]),([226,0,1,6,4,5],[25,29,83],[]),([0,16,1,2,143,4,5,62],[2,16,25,103,145],[0]),([227,157,0,9,6,5],[22,174,186,511,512,513,514],[0]),([228,0,1,3,4,5,58],[16,42,262,515,516],[]),([0,1,2,3,4,154,5],[89,137,517,518,519,520,521],[0]),([0,1,2,3,4,158,29],[25,412,522,523],[0]),([0,1,229,2,3,4,5,34],[139],[]),([157,0,165,2,3,4,5,34],[7,152],[]),([0,1,230,2,3,4,5,62],[2,16,145],[]),([0,1,9,6,153,4,5],[2,18,33,34,174,519,524,525,526],[0]),([0,1,2,3,4,231,5],[2,43,89,137,519,527,528],[]),([0,107,233,3,4,5],[253,254,311,529,530,531,532,533],[]),([93,0,1,3,4,234,5],[2,103,519,534,535,536],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7 = true := by decide +kernel
def B_22_7 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_7
set_option maxRecDepth 500000 in
lemma B_22_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 7 xs.toFinset) B_22_7 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_6_ok C_22_7
def P_22_8 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [2,4,7,8,16,17,18,22,25,31,33,34,42,43,50,51,59,63,70,71,72,73,77,80,83,84,88,89,92,103,106,110,137,138,139,140,141,142,143,144,145,149,151,152,156,157,158,159,162,163,164,165,166,167,168,169,171,172,174,185,186,187,190,194,196,201,208,209,212,217,220,221,222,225,227,230,231,232,233,234,238,247,249,251,252,253,254,255,256,258,261,262,264,266,267,274,275,278,280,283,284,285,286,287,288,290,294,295,296,297,298,300,301,302,303,306,308,309,310,311,312,314,315,319,322,324,325,327,328,329,330,332,333,334,341,342,343,344,345,347,348,349,353,357,362,368,371,375,383,384,387,388,391,392,393,394,395,396,398,399,400,402,404,407,408,412,414,415,416,418,421,422,425,427,428,429,430,431,432,435,436,438,439,441,442,445,448,449,450,451,454,457,460,462,463,466,467,469,471,476,487,493,494,495,497,500,501,502,508,510,512,514,515,519,520,522,526,530,532,534,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1198,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208,1209,1210,1211,1212,1213,1214,1215,1216,1217,1218,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248,1249,1250,1251,1252,1253,1254,1255,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1296,1297,1298,1299,1300,1301,1302,1303,1304,1305,1306,1307,1308,1309,1310,1311,1312,1313,1314,1315,1316,1317,1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1337,1338,1339,1340,1341,1342,1343,1344,1345,1346,1347,1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1367,1368,1369,1370,1371,1372,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410,1411,1412,1413,1414,1415,1416,1417,1418,1419,1420,1421,1422,1423,1424,1425,1426,1427,1428,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454,1455,1456,1457,1458,1459,1460,1461,1462,1463,1464,1465,1466,1467,1468,1469,1470,1471,1472,1473,1474,1475,1476,1477,1478,1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,1492,1493,1494,1495,1496,1497,1498,1499,1500,1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1529,1530,1531,1532,1533,1534,1535,1536,1537,1538,1539,1540,1541,1542,1543,1544,1545,1546,1547,1548,1549,1550,1551,1552,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689,1690,1691,1692,1693,1694,1695,1696,1697,1698,1699,1700,1701,1702,1703,1704,1705,1706,1707,1708,1709,1710,1711,1712,1713,1714,1715,1716,1717,1718,1719,1720,1721,1722,1723,1724,1725,1726,1727,1728,1729,1730,1731,1732,1733,1734,1735,1736,1737,1738,1739,1740,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1751,1752,1753,1754,1755,1756,1757,1758,1759,1760,1761,1762,1763,1764,1765,1766,1767,1768,1769,1770,1771,1772,1773,1774,1775,1776,1777,1778,1779,1780,1781,1782,1783,1784,1785,1786,1787,1788,1789,1790,1791,1792,1793,1794,1795,1796,1797,1798,1799,1800,1801,1802,1803,1804,1805,1806,1807,1808,1809,1810,1811,1812,1813,1814,1815,1816,1817,1818,1819,1820,1821,1822,1823,1824,1825,1826,1827,1828,1829,1830,1831,1832,1833,1834,1835,1836,1837,1838,1839,1840,1841,1842,1843,1844,1845,1846,1847,1848,1849,1850,1851,1852,1853,1854,1855,1856,1857,1858,1859,1860,1861,1862,1863,1864,1865,1866,1867,1868,1869,1870,1871,1872,1873,1874,1875,1876,1877,1878,1879,1880,1881,1882,1883,1884,1885,1886,1887,1888,1889,1890,1891,1892,1893,1894,1895,1896,1897,1898,1899,1900,1901,1902,1903,1904,1905,1906,1907,1908,1909,1910,1911,1912,1913,1914,1915,1916,1917,1918,1919,1920,1921,1922,1923,1924,1925,1926,1927,1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944,1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,1955,1956,1957,1958,1959,1960,1961,1962,1963,1964,1965,1966,1967,1968,1969,1970,1971,1972,1973,1974]
def N_22_8_0 : List NodeSpec := [([0,1,2,3,4,188,5,62],[8,25,70,103,194,441,537,538,539],[0]),([142,176,0,1,3,4,5],[25,145,540,541,542],[1]),([0,1,2,143,4,5,62],[2,16,25,145,543,544,545,546],[0]),([0,1,235,3,4,5,34],[16,25,145,547,548,549,550],[1]),([236,0,1,2,3,4,5,34],[2,42,77,103,551,552,553,554,555,556],[]),([0,1,2,82,4,5,62],[16,25,103,349,441,557,558],[0,1]),([0,1,2,3,237,4,5,58],[16,42,103,294,508,559,560,561,562,563,564],[]),([0,1,2,3,100,4,5,58],[42,103,294,559,560,563,565,566,567,568],[]),([238,0,1,2,3,4,5,58],[2,7,8,16,42,70,294,559,560,563,569,570,571,572],[]),([175,0,1,2,3,4,5,135],[2,42,77,573,574,575,576,577,578,579],[]),([0,1,2,239,3,4,5,62],[8,25,103,441,538,580,581,582,583,584],[]),([85,186,0,1,2,3,4,5,62],[2,16,25,42,103,347,441,585,586],[1]),([0,1,2,3,4,114,62],[16,25,51,63,343,344,345],[0,1]),([240,0,1,2,3,4,5],[25,50,51,89,103,137,139,349,587,588,589],[]),([0,1,2,3,4,5,241],[25,50,103,138,139,590,591,592,593],[]),([0,1,2,242,4,5,62],[16,25,42,349,594,595,596],[1]),([0,243,1,2,215,3,4,5],[25,51,103,597,598,599,600,601,602],[]),([245,186,0,1,2,3,4,5],[42,51,603,604,605,606,607],[]),([85,0,1,83,2,3,4,5,62],[2,16,25,145,194,441,442,585],[0]),([160,0,1,2,3,4,5,127],[2,25,103,140,141,143,144,264,608,609,610,611,612],[0]),([0,1,2,3,4,84,62],[2,25,42,43,63,145,613,614,615],[0,1]),([0,1,2,3,4,5,84,246],[2,7,42,303,616,617,618,619],[]),([0,1,2,179,4,5,62],[2,16,25,145,620,621,622],[]),([0,1,2,247,3,4,5],[25,50,103,139,623,624,625],[]),([93,0,1,2,3,183,4,5],[267,285,457,462,626,627,628,629,630,631,632,633,634,635],[]),([93,0,1,215,3,4,5],[25,636,637,638],[]),([85,55,0,1,2,4,5,62],[2,16,25,103,145,585,639,640,641,642],[1]),([0,1,2,3,4,207,62],[2,16,42,145,399,457,643,644],[0]),([248,0,1,2,3,4,5,139],[2,25,103,645,646,647,648,649],[]),([0,1,2,3,4,5,207,249],[2,42,303,650,651,652],[]),([0,1,2,250,3,5,7],[51,103,653,654,655,656,657,658],[]),([0,1,2,3,252,4,5,58],[2,42,103,559,560,563,567,659,660,661],[]),([93,176,0,1,3,4,5],[25,145,662,663],[]),([0,1,2,3,4,5,253],[25,50,103,139,664,665,666,667,668],[]),([167,0,1,2,3,6,4,5],[2,8,16,43,51,63,231,669,670,671,672,673,674,675,676],[]),([254,0,1,2,3,4,5],[16,42,50,89,137,139,677,678],[]),([171,0,1,2,3,4,5],[2,50,51,89,137,138,230,679,680],[]),([0,1,2,6,4,5,62],[2,16,25,145,681,682,683,684],[0]),([0,1,2,3,79,4,5],[2,247,685,686,687,688],[0]),([0,1,2,163,3,4,5],[25,50,103,138,139,149,689,690,691],[0]),([0,1,2,3,6,100,4,5],[16,70,156,163,164,166,167,168,172,692],[0]),([175,0,1,2,4,5,34],[16,42,89,693,694,695],[0]),([175,0,1,2,3,4,5],[42,50,89,137,139,428,693,694,696],[]),([116,0,1,2,3,4,5,34],[2,16,50,70,152,298,454,697,698,699,700,701,702],[0]),([0,1,2,3,4,5,255],[16,50,103,139,156,703,704,705,706],[]),([0,1,2,215,3,4,5],[17,25,50,139,707,708],[]),([99,69,0,1,2,3,5],[2,16,25,402,688],[0]),([0,1,2,3,72,4,5,34],[2,25,42,152,156,158,428,454,697,698,709,710,711,712],[]),([0,1,2,3,6,4,5,80],[2,51,156,162,713,714],[0]),([256,0,1,2,3,4,5],[16,25,50,89,103,137,139,349,715,716,717,718],[]),([0,1,2,3,4,5,80],[2,25,42,50,51,156,187,713,714],[0]),([105,0,1,2,3,4,5,58,135],[7,16,25,42,103,294,577,719],[0]),([0,1,258,2,3,4,5],[2,50,138,720,721,722],[]),([0,1,2,3,6,95,4,5],[25,43,103,156,166,167,168,341,342,392,723,724,725,726],[]),([171,0,1,2,3,4,58],[2,42,156,349,727,728],[0]),([0,1,2,3,72,4,5,58],[42,156,162,294,508,559,560,563,567,709,710,711,712,729,730],[]),([175,0,1,2,6,4,5],[2,8,42,508,731,732],[0]),([0,1,2,259,4,5,62],[25,42,43,733,734,735],[]),([0,1,2,6,183,4,5,62],[16,25,42,145,438,736,737,738,739],[]),([171,0,1,2,6,4,62],[2,16,349,736,740,741],[]),([25,0,1,2,3,6,4,5,7],[2,16,166,167,688,742,743,744,745],[0]),([25,0,1,2,6,4,5,62],[2,16,25,43,145,438,736,737,738,746,747,748,749],[0]),([0,1,2,250,3,92,5],[51,655,668,750,751,752,753,754],[]),([155,25,0,2,3,4,5],[2,16,166,167,743],[0]),([0,1,2,3,6,170,4,5],[2,16,166,209,755,756,757],[0]),([0,1,2,168,3,4,5,62],[8,16,103,169,347,398,441,538,758,759],[0]),([69,0,32,1,2,3,4,5],[2,16,51,688,760,761,762,763],[0]),([45,0,1,2,3,6,4,5],[2,25,42,166,167,168,171,341,342,764,765,766,767],[0,1]),([260,0,1,2,3,4,5],[8,25,50,89,137,138,139,768,769,770],[]),([25,0,1,2,3,4,73,5],[2,138,157,159,744,771,772,773,774,775,776],[0]),([167,0,1,9,6,4,5],[2,8,16,22,31,33,34,59,174,314,315,673,777],[0]),([0,1,9,6,4,5,7],[2,16,31,33,34,59,174,186,448,449,770,778],[0]),([171,0,1,9,6,4,5],[2,16,31,33,34,59,83,186,779,780,781],[0]),([69,0,1,9,6,4,5],[2,16,17,18,33,34,59,174,186,782,783,784],[0]),([0,1,9,6,4,73,5],[2,16,22,59,186,775,785,786,787,788],[0]),([85,0,1,2,3,183,4,5],[16,25,196,285,626,627,628,789,790],[0,1]),([0,1,2,261,3,4,5],[25,50,103,139,791,792,793,794],[]),([0,1,9,72,6,4,5],[2,16,18,59,174,186,190,729,795,796,797],[0]),([155,0,1,9,6,4,5],[2,16,33,34,59,174,186,208,798,799,800],[0]),([0,1,6,4,5,29],[8,16,22,25,31,83,220,221,222],[0]),([0,1,2,3,4,5,29,173],[25,80,522,801,802,803,804],[0]),([0,1,2,3,95,4,5,34],[25,42,103,387,551,552,553,556,568,723,724,725,726,805],[]),([0,1,2,3,4,5,263],[25,50,89,137,139,806,807,808],[]),([0,1,264,2,3,4,5],[16,43,139,349,442,809,810,811,812,813,814,815],[]),([81,0,1,2,3,6,4,5],[2,8,16,43,50,230,669,670,671,813,816,817],[0]),([265,0,1,2,3,4,5],[8,25,89,103,137,139,349,445,818,819,820,821],[]),([266,0,1,2,3,4,5],[8,16,43,51,89,137,138,139,349,813,814,822,823,824,825,826],[]),([81,69,0,1,2,3,4,5],[16,50,103,762,763,814,827,828],[]),([0,1,2,3,267,4,5],[2,51,138,349,829,830,831,832],[]),([81,0,1,9,6,4,5],[2,8,16,22,31,33,34,59,186,813,833,834,835],[0]),([0,1,9,6,4,5,34],[2,16,22,31,59,71,158,836,837],[0]),([81,262,0,1,2,3,4,5],[25,50,51,813,838,839,840,841,842,843],[]),([0,1,268,2,3,4,5],[51,139,349,813,814,816,844,845,846,847,848,849],[]),([105,175,0,1,2,4,5],[25,42,508,850,851,852,853],[0]),([0,1,2,3,4,269,5],[16,43,103,232,854,855,856,857,858],[]),([93,0,1,2,3,174,4,5],[7,16,43,50,51,232,238,462,633,634,635,859,860,861,862,863],[0]),([0,1,9,2,3,174,4,5],[7,50,51,232,324,848,859,860,861,864,865,866,867,868,869],[0]),([105,0,1,2,220,3,4,5],[16,25,50,51,103,303,445,813,870,871,872,873,874,875,876,877,878],[]),([25,0,1,9,6,4,5],[2,31,33,34,59,174,186,201,225,233,234,879],[0]),([0,1,83,2,3,82,4,5],[16,50,80,442,816,880,881,882,883,884,885,886],[]),([0,1,2,3,270,4,5],[16,51,103,138,874,887,888,889,890,891],[]),([0,1,2,3,4,234,5],[16,43,103,519,534,892,893,894],[0]),([0,1,2,272,3,4,5],[2,7,51,895,896,897,898,899],[]),([175,0,1,273,2,3,4,5],[2,42,50,575,900,901],[]),([105,271,0,1,2,4,5],[7,25,138,301,902,903,904,905,906,907],[]),([81,0,1,2,3,213,4,5],[2,103,816,908,909,910,911,912,913,914],[]),([105,274,0,1,2,3,4,5],[2,7,25,51,915,916,917],[]),([0,1,2,275,3,4,5],[16,42,43,606,918,919],[]),([0,1,2,215,3,4,5,152],[2,7,25,50,598,602,920,921],[]),([271,0,1,2,126,4,5],[7,906,922,923,924,925],[]),([276,0,1,2,3,4,5],[2,7,8,89,137,925,926,927,928],[]),([277,0,1,2,6,4,5],[8,16,688,929,930,931],[]),([0,1,2,278,3,4,5],[7,906,932,933,934,935],[]),([0,1,2,3,6,153,4,5],[2,8,16,43,103,166,168,341,342,519,520,936,937,938,939],[0]),([279,0,1,2,3,4,5],[2,7,89,137,166,940,941,942],[]),([0,1,2,3,280,4,5],[7,89,137,166,943,944,945,946],[]),([0,1,9,2,3,153,4,5],[139,519,520,864,865,866,936,937,947,948,949],[0]),([0,1,26,2,3,6,4,5],[2,8,25,42,43,166,168,341,342,425,950,951],[0,1]),([0,1,9,6,4,5,152],[2,22,31,174,917,952,953,954],[0]),([0,1,2,3,4,152,29],[25,50,487,522,906,917,955,956],[0]),([157,0,1,2,3,4,5,58,34],[2,7,25,42,103,553,555,957],[]),([105,0,1,2,3,106,5],[25,51,70,138,421,422,958,959],[0,1]),([93,157,0,1,3,4,5,58],[2,7,25,42,457,960,961,962,963],[]),([185,0,1,2,3,4,5,187],[16,42,50,103,284,964,965,966,967,968,969,970,971,972,973],[0]),([99,0,1,9,6,4,5],[2,22,33,34,59,174,186,974,975,976],[0]),([185,0,1,2,3,4,5,84],[2,8,50,429,615,618,969,971,977,978,979,980,981],[]),([0,1,2,39,3,4,5,62],[16,25,43,103,169,194,302,347,441,538,580,982,983,984,985],[1]),([0,32,1,2,6,4,5,62],[2,16,25,43,145,438,736,737,738,746,986,987],[0]),([142,0,16,1,2,3,4,5,62],[16,25,145,194,441,467,988,989],[0]),([185,186,0,2,3,4,5,152],[2,42,50,283,990,991,992,993,994,995],[]),([157,0,1,2,3,4,5,29],[7,25,487,522,961,996,997,998,999,1000],[0]),([0,1,2,3,4,281,62],[2,25,441,969,1001,1002],[]),([93,162,0,1,2,4,5],[16,149,312,1003,1004,1005,1006],[0]),([171,0,1,2,3,4,34],[2,16,89,697,1007,1008],[0,1]),([105,0,1,2,3,4,5,283],[2,25,50,51,876,877,1009,1010,1011,1012,1013,1014,1015],[]),([0,1,2,284,3,4,5,62],[2,7,145,194,441,538,580,1016,1017],[]),([0,1,2,3,4,5,286],[2,51,138,1018,1019,1020,1021,1022],[]),([162,0,1,9,2,4,5],[25,149,312,1023,1024],[0]),([288,0,1,2,3,4,5],[2,7,43,89,137,349,1025,1026,1027,1028],[]),([290,0,1,2,3,4,5],[8,43,89,137,139,349,400,429,969,1029,1030,1031,1032,1033],[]),([0,1,2,3,4,5,291],[2,7,16,51,103,1034,1035,1036,1037,1038,1039,1040],[]),([0,1,2,38,3,4,5,127],[2,25,50,140,141,143,302,303,608,609,1041,1042,1043],[0]),([292,0,1,2,3,4,5],[2,50,89,137,138,914,1044,1045],[]),([167,0,1,2,293,3,4,5],[43,50,51,103,674,675,1046,1047,1048,1049,1050],[]),([0,1,2,219,3,4,5,7],[16,103,303,429,742,770,1051,1052,1053,1054,1055,1056,1057],[]),([175,0,1,6,4,5,58],[16,42,43,731,732,1058],[]),([0,1,2,293,3,4,5,7],[2,103,657,742,1046,1047,1052,1059,1060],[]),([0,1,2,219,3,4,5,62],[2,16,25,169,347,429,441,538,1053,1054,1056,1057,1061],[0]),([162,0,1,2,38,3,4,5],[8,16,25,103,149,312,416,1042,1062,1063,1064,1065],[0]),([175,0,1,2,126,4,5],[42,508,1066,1067],[]),([167,0,1,2,294,3,4,5],[43,51,103,674,676,1068,1069,1070,1071],[]),([93,0,1,3,4,5,58,135],[2,42,303,577,962,963,1072,1073],[1]),([185,0,1,2,295,4,5],[8,25,139,400,429,969,1074,1075,1076,1077,1078,1079],[]),([0,1,2,3,6,4,5,7],[2,16,51,230,657,669,670,671,672,742,745,770,817,1052,1059],[]),([236,0,1,3,6,4,5,58],[2,42,103,1058,1080,1081,1082],[]),([93,0,1,219,3,4,5],[2,16,50,429,462,1055,1083,1084],[]),([0,2,219,3,4,5,152],[2,50,349,1056,1085,1086,1087,1088],[]),([0,1,9,6,76,4,5],[2,16,33,34,174,186,1089,1090,1091,1092],[0]),([0,1,2,296,3,4,5],[2,1040,1093,1094,1095,1096,1097,1098,1099],[]),([0,1,2,298,3,4,5],[16,51,103,138,349,1100,1101,1102],[]),([0,1,2,205,3,4,5],[16,43,50,103,303,357,745,1063,1103,1104,1105,1106],[0]),([0,32,1,2,3,6,4,5,7],[2,16,166,167,297,688,745,760,761,1107,1108],[0]),([105,0,1,2,38,3,5,7],[16,25,51,70,103,329,1063,1109,1110,1111,1112],[0]),([0,1,2,294,3,4,5,7],[2,103,657,745,1052,1068,1069,1070,1113,1114],[]),([69,0,1,2,3,5,7],[16,25,42,51,103,688,1115,1116],[]),([0,1,2,38,3,4,5,114],[16,25,103,275,302,345,393,396,1042,1062,1110,1117,1118,1119],[0]),([0,134,1,3,6,4,5,58],[2,16,42,103,508,1058,1080,1082,1120,1121],[]),([299,0,1,2,3,4,5],[8,16,50,51,89,103,137,138,349,1056,1122,1123,1124,1125,1126],[]),([0,1,2,3,6,4,5,169],[2,16,166,168,688,1127,1128],[0]),([0,1,2,91,179,4,5],[2,16,50,51,258,1129,1130],[]),([0,32,1,9,6,4,5],[2,31,33,34,59,174,186,217,227,450,451,1131],[0]),([192,0,1,2,126,3,4,5],[2,43,103,142,302,303,925,1043,1132,1133,1134,1135],[]),([300,0,1,2,3,4,5],[8,16,50,51,89,103,137,1136,1137,1138,1139],[]),([212,0,107,1,2,3,4,5,62],[16,25,145,328,347,348,1140,1141],[0]),([301,0,1,2,3,4,5],[8,43,89,137,255,349,532,1142,1143,1144,1145,1146,1147],[]),([287,0,1,86,3,4,5],[7,16,50,103,371,476,1148,1149,1150,1151],[]),([285,0,1,2,3,4,5,7],[2,16,103,349,742,745,770,1022,1052,1059,1152,1153],[]),([302,0,1,2,3,4,5],[2,50,51,89,137,138,1154,1155,1156,1157],[]),([303,0,1,2,3,92,5],[8,51,391,753,1158,1159,1160,1161,1162],[]),([0,1,9,2,3,4,5,47],[7,50,72,73,322,432,460,487,848,864,1163,1164,1165],[0]),([0,1,2,284,3,92,5],[51,1040,1097,1160,1166,1167,1168,1169],[]),([0,1,2,38,3,183,4,5,62],[16,25,103,145,169,194,267,275,302,347,441,1170],[0]),([185,186,0,1,2,3,5,7],[16,42,51,103,400,429,995,1171,1172,1173,1174,1175],[0]),([0,1,2,3,6,4,5,146],[2,16,168,688,1176,1177],[0]),([0,1,2,304,3,4,5],[8,25,50,103,194,1178,1179,1180,1181],[]),([81,0,1,2,3,72,4,5],[2,50,156,162,709,710,729,814,842,1182],[]),([305,0,1,2,3,4,5],[8,16,50,51,89,103,137,138,1183,1184,1185,1186],[]),([175,0,1,2,38,3,4,5],[2,8,42,77,575,578,579,1042,1062,1187],[]),([0,134,1,2,3,4,5,34],[2,16,42,103,387,508,551,552,553,554,556,1188,1189],[]),([105,0,1,2,38,3,4,5,58],[8,25,42,103,275,294,445,1110],[0]),([185,186,0,1,2,3,4,5,62],[2,16,25,42,284,347,441,995],[]),([289,0,89,2,91,4,5],[139,278,1076,1190,1191,1192,1193,1194,1195,1196,1197],[1]),([0,1,83,2,3,4,5,181],[25,280,362,882,883,1198,1199,1200,1201,1202],[0,1]),([0,1,2,3,4,307,5],[2,25,50,51,1203,1204,1205,1206],[]),([285,186,0,1,2,3,4,5],[2,25,42,50,51,103,604,605,990,1207],[]),([142,0,1,2,3,183,4,5],[25,267,285,467,626,627,628,630,1208,1209,1210,1211,1212],[]),([277,0,1,2,38,3,4,5],[8,16,25,77,274,302,931,1042,1062,1063,1213,1214],[]),([0,308,1,2,3,4,5],[2,16,43,89,103,137,138,371,1215,1216,1217,1218],[]),([0,1,2,39,3,92,5],[51,103,138,984,1063,1219,1220,1221,1222],[]),([0,1,2,233,3,4,5],[50,302,530,532,1112,1223,1224,1225],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_0 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_0 = true := by decide +kernel
def N_22_8_1 : List NodeSpec := [([287,0,1,2,3,138,4,5],[16,50,103,463,466,1226,1227,1228,1229,1230,1231],[]),([285,0,1,2,3,4,92,5],[2,8,16,1152,1221,1232,1233,1234,1235,1236,1237,1238,1239],[]),([0,1,83,3,91,92,5],[295,1240,1241,1242,1243,1244,1245,1246,1247],[1]),([0,107,38,3,4,194,5],[70,253,254,311,1248,1249,1250,1251,1252],[0]),([309,0,1,2,3,4,5],[2,43,50,51,89,137,138,349,1050,1253,1254,1255,1256,1257],[]),([85,176,0,1,2,3,4,5],[2,16,25,103,789,790,1258,1259,1260],[]),([8,0,1,2,3,4,5],[16,25,50,89,103,137,139,353,688,1261,1262],[0]),([0,107,38,3,4,5,7],[92,253,254,332,394,745,770,1263,1264,1265],[0]),([0,1,2,3,4,108,62],[42,43,145,327,328,368,441,1266,1267,1268],[0,1]),([185,186,0,1,2,3,242,4,5],[42,51,284,606,1269,1270,1271],[]),([0,1,2,3,4,5,108,310],[2,42,368,1272,1273,1274,1275,1276,1277],[]),([0,1,2,3,4,108,7],[42,51,84,742,770,1278,1279],[0]),([0,1,311,2,3,4,5],[8,25,103,745,1280,1281],[]),([167,0,1,2,215,3,5],[25,103,1282,1283,1284,1285,1286],[]),([81,0,1,2,250,3,4,5],[25,50,51,103,658,752,842,1287,1288,1289,1290],[]),([287,0,89,2,91,4,5],[70,139,278,1027,1190,1192,1193,1195,1291,1292,1293,1294,1295],[]),([177,0,1,2,3,183,4,5,62],[16,25,145,194,255,267,347,408,501,502,629,1296],[0]),([105,0,1,2,3,4,5,108],[8,16,25,42,50,51,84,327,368,427,445,638,876,877,1297,1298,1299],[0]),([0,1,2,3,4,29,7],[25,51,522,657,770,1300,1301,1302],[0]),([0,1,2,219,3,4,194,5],[2,429,430,630,1053,1054,1057,1099,1303,1304,1305],[]),([185,0,1,83,3,92,5],[8,400,429,969,1242,1244,1271,1306,1307,1308,1309,1310,1311,1312],[]),([0,107,1,2,126,194,5],[138,306,328,383,384,404,1313,1314,1315,1316,1317],[0]),([105,177,0,1,2,3,4,5,62],[16,25,194,252,347,501,502,1144,1146,1296,1318],[0]),([0,107,38,126,3,4,5],[70,92,139,253,911,925,1319,1320,1321],[0,1]),([212,282,0,1,2,3,4,5],[8,16,25,50,51,103,1040,1322,1323,1324,1325,1326,1327,1328,1329],[]),([0,16,9,2,3,17,5],[487,494,495,848,866,1330,1331,1332,1333],[0]),([0,1,312,2,3,5,7],[25,51,745,1334,1335,1336],[]),([212,0,1,2,38,3,4,5,62],[16,25,194,275,302,347,1337],[0]),([212,177,0,1,2,3,4,5,62],[16,25,194,255,347,407,502],[0]),([313,0,1,2,3,4,5],[8,25,89,137,139,445,1338,1339,1340,1341],[]),([0,16,1,2,314,3,4,5],[2,16,103,1342,1343,1344,1345,1346,1347,1348,1349,1350],[]),([303,0,1,2,3,4,5,58],[8,25,294,559,560,567,1162,1351,1352],[]),([0,1,2,315,6,4,5],[2,16,50,1353,1354,1355,1356,1357],[]),([105,0,107,1,2,3,4,5],[8,25,50,51,70,139,327,328,383,404,1358,1359,1360,1361,1362,1363],[]),([0,134,2,3,4,5,135],[42,103,563,567,1364,1365,1366,1367],[1]),([212,0,107,1,2,3,4,5],[8,16,25,50,51,70,139,328,348,793,1322,1326,1327,1358,1359],[]),([0,1,2,317,3,4,5,62],[2,16,25,194,538,580,1368,1369,1370],[]),([167,0,1,2,219,3,4,5],[16,50,51,103,429,430,673,675,1053,1055,1057,1305],[]),([318,0,1,2,3,4,5],[8,25,43,89,137,138,301,349,638,1371,1372,1373,1374,1375],[]),([289,0,1,293,3,4,5],[2,50,1050,1060,1376],[]),([319,0,1,2,3,4,5],[42,50,89,137,139,508,1377,1378],[]),([93,0,16,1,3,4,5,58],[8,16,25,42,262,334,371,471,515,960,962,963],[0,1]),([0,1,2,3,4,5,40],[16,43,51,103,287,288,290,302,1379],[0,1]),([0,1,2,3,320,4,5],[2,16,51,103,1380,1381,1382,1383],[]),([0,1,2,3,4,152,84],[2,42,50,63,618,917,1384,1385,1386],[]),([157,0,1,2,3,4,5,207],[2,7,42,457,652,961,999,1000,1387,1388],[]),([81,105,0,2,38,3,4,5],[16,25,50,103,301,302,445,638,813,1110,1389,1390,1391,1392,1393],[]),([0,1,2,284,3,4,5,58],[2,8,42,559,560,563,567,1016,1017,1040,1394],[]),([0,1,2,321,4,194,5],[2,51,1099,1249,1395,1396,1397,1398,1399],[]),([185,0,1,2,3,322,4,5],[2,8,42,50,51,429,971,972,1400,1401,1402,1403,1404,1405,1406,1407],[]),([287,0,1,215,3,4,5],[25,638,1408,1409],[]),([105,0,1,2,219,3,4,5],[2,16,25,50,51,429,1053,1054,1055,1056,1305],[]),([287,0,1,293,3,4,5],[2,25,50,1049,1231,1256,1410,1411],[]),([189,0,1,2,3,4,5,127],[2,25,140,143,264,286,608,609,1412,1413,1414],[0]),([0,107,38,3,4,5,62],[70,92,145,194,253,311,1415,1416,1417],[0]),([105,0,107,38,3,4,5],[8,70,92,251,253,254,301,310,332,394,638,1418,1419,1420],[0]),([0,1,2,3,72,92,5],[2,156,688,729,1421,1422],[]),([287,303,0,1,2,3,4,5],[8,25,50,51,1162,1231,1351,1352,1423,1424,1425],[]),([0,1,323,2,3,4,5],[42,43,50,606,1426,1427],[]),([0,1,312,2,3,4,5,58],[8,25,294,559,560,563,1428,1429,1430],[]),([105,177,0,1,2,3,5,7],[16,25,51,70,329,330,501,1109,1144,1146,1318],[]),([0,1,2,324,3,4,5],[2,742,1097,1431,1432,1433,1434,1435],[]),([0,1,83,2,3,4,5,195],[25,50,280,319,391,442,882,883,1436,1437,1438,1439],[0,1]),([0,1,2,90,3,4,5],[2,50,51,280,349,442,1049,1440,1441,1442,1443,1444],[0,1]),([0,1,2,325,3,4,5],[25,51,1162,1445,1446,1447,1448,1449],[]),([0,1,2,138,6,4,5],[8,16,466,1227,1357,1450,1451,1452,1453,1454],[]),([105,0,107,1,2,3,4,5,62],[16,25,145,327,347,348,383,404,427,1455,1456,1457],[0]),([0,326,1,2,3,4,5],[25,43,50,89,137,138,139,349,445,638,1458,1459,1460,1461,1462],[]),([185,0,1,2,3,95,4,5,58],[2,42,103,283,284,567,725,969,1463],[]),([327,0,1,2,215,3,4,5],[2,25,50,51,597,598,601,602,638,1464,1465],[]),([328,0,1,2,3,4,5],[8,16,42,50,89,137,1466,1467,1468,1469,1470],[]),([329,0,1,2,3,4,5],[2,8,50,51,89,137,275,303,349,925,1112,1471,1472,1473,1474,1475,1476],[]),([0,1,2,3,4,5,330],[8,25,51,89,103,137,1477,1478,1479],[]),([185,186,0,1,2,3,4,5],[2,42,43,50,51,429,969,971,972,1480,1481,1482,1483,1484],[]),([157,0,1,2,6,4,5,62],[2,7,16,25,736,737,738,739],[]),([196,0,1,2,3,4,5,195],[25,50,103,319,1436,1437,1438,1485,1486,1487,1488,1489],[0]),([0,107,1,2,3,4,5,127],[25,140,143,264,328,383,608,609,1358,1490],[0,1]),([0,331,1,2,3,4,5],[42,43,50,89,137,139,383,1491,1492],[]),([0,107,1,332,3,4,5],[42,43,139,1145,1493,1494,1495],[]),([192,0,1,2,3,4,58],[2,103,274,300,302,563,1496,1497],[0]),([285,0,1,2,6,4,5],[2,8,16,166,1234,1498,1499],[]),([333,0,1,2,3,4,5],[8,25,50,89,103,137,139,742,1500,1501],[1]),([172,0,1,2,3,4,5,29],[2,25,325,996,997,1302,1502,1503,1504,1505],[0]),([0,16,1,2,3,4,5,29],[8,25,43,324,325,371,466,522,996,997,1165,1302,1344,1345],[0]),([0,1,2,335,3,4,5],[2,1506,1507,1508,1509],[]),([162,0,89,1,2,4,5],[25,139,149,312,1510,1511],[]),([0,1,2,3,336,4,5,58],[7,42,103,294,508,559,560,567,1512,1513,1514],[]),([81,0,83,2,3,91,4,5],[16,50,80,280,295,442,814,816,1200,1515,1516,1517],[]),([0,16,2,3,6,17,5],[156,166,167,494,495,1518,1519],[0]),([0,1,2,321,4,5,62],[2,16,145,169,441,1399,1520,1521,1522,1523],[]),([0,107,1,2,3,183,4,5],[16,70,285,328,348,404,626,627,628,629,1358,1359,1524],[0]),([0,1,2,3,4,47,58],[7,8,42,63,73,261,388,567,1525,1526],[0,1]),([0,1,2,337,3,4,5],[25,42,50,139,1527,1528,1529,1530],[]),([223,0,1,2,3,4,5],[8,16,42,43,89,137,138,139,567,1531,1532,1533,1534,1535,1536],[0]),([338,0,1,2,3,4,5],[42,50,51,89,137,139,349,508,567,1537,1538,1539,1540],[]),([167,105,0,107,1,2,3,5],[16,25,51,63,70,327,328,348,383,427,1285,1541,1542,1543],[]),([0,107,1,2,3,183,4,5,62],[16,25,145,285,327,328,347,348,626,627,629,1455],[0,1]),([185,176,0,1,2,3,4,5],[2,25,283,349,971,972,1258,1259,1260,1544,1545],[]),([339,0,1,2,3,4,5],[7,8,89,137,635,961,1546,1547],[]),([287,0,1,312,2,3,4,5],[8,25,51,1027,1424,1425,1428,1429,1430],[]),([93,340,0,1,3,4,5],[2,16,1243],[]),([192,105,0,1,2,3,4,5],[16,25,51,70,103,302,303,445,1110,1548],[0]),([0,341,1,2,3,4,5],[2,50,51,89,137,138,139,383,1549,1550,1551,1552,1553,1554],[]),([0,1,2,3,4,188,5],[42,50,70,103,285,375,537,539,1555],[0]),([93,0,1,86,3,4,5],[50,51,80,103,303,371,462,476,631,1556,1557,1558,1559],[0,1]),([93,0,1,2,3,117,4,5],[16,630,1383,1560,1561,1562,1563,1564,1565],[]),([185,186,0,1,2,3,4,5,58],[2,42,283,284,294,400,567,990,995,1566,1567],[0]),([285,0,1,2,3,4,5,58],[2,8,16,42,70,294,349,515,559,560,563,1022,1234,1237,1239,1568,1569,1570],[]),([0,1,2,342,3,4,5],[7,8,43,50,349,866,961,998,1571,1572,1573,1574,1575],[]),([93,0,1,2,3,153,4,5],[2,519,526,631,633,634,635,936,937,1576,1577],[0]),([0,1,2,3,4,5,343],[2,51,138,1056,1578,1579,1580,1581,1582],[]),([0,1,2,344,3,4,5],[2,8,25,139,441,1583,1584,1585,1586,1587],[]),([105,0,107,1,2,3,5,7],[16,25,51,327,329,383,404,427,1111,1588,1589],[0]),([185,0,1,2,3,95,4,5],[2,16,50,103,284,392,723,724,725,726,969,971,972,1463,1590,1591],[]),([0,1,2,215,3,5,7],[25,103,329,1592,1593,1594,1595],[]),([0,1,235,6,4,5,62],[2,16,25,145,1596,1597],[]),([212,282,0,1,2,3,4,5,62],[16,25,347,407,441,1040,1325],[1]),([0,165,1,2,3,4,5,34],[16,103,139,151,454,697,698,699,1598,1599],[0]),([345,0,1,2,3,4,5],[2,43,51,89,137,138,139,349,429,1600,1601,1602,1603,1604],[]),([185,0,1,2,3,346,4,5],[2,8,16,42,50,51,283,429,971,972,1605,1606,1607,1608,1609],[]),([185,347,0,1,2,3,4,5],[2,42,50,283,400,969,971,972,1610,1611],[]),([185,0,1,2,215,3,4,5],[2,25,50,284,597,598,601,638,971,972,1612],[]),([348,0,1,2,3,4,5],[8,16,50,51,89,103,137,138,1613,1614,1615,1616],[]),([227,157,0,2,3,6,5],[156,166,512,688,1617,1618,1619],[0]),([105,0,107,1,2,3,4,5,114],[16,25,51,70,328,348,393,427,1117,1118,1620],[0]),([349,0,1,2,3,4,5],[16,43,50,63,89,103,137,139,303,1151,1621,1622,1623,1624],[]),([185,350,0,1,2,3,4,5],[2,16,42,50,103,400,971,972,1625,1626,1627,1628,1629,1630],[]),([0,16,1,9,6,4,5],[2,16,18,33,34,59,186,371,435,1631,1632,1633],[0]),([0,1,2,3,4,5,84,351],[2,25,42,979,1634,1635,1636,1637],[1]),([0,16,1,2,3,4,5,58,34],[2,16,25,42,103,294,387,508,555,563,1638],[0]),([81,0,1,2,215,3,4,5],[25,50,103,597,598,602,638,814,1612,1639],[]),([185,162,0,1,2,4,5],[16,25,139,149,312,400,416,657,1640,1641,1642],[]),([0,1,352,2,3,4,5],[16,42,43,349,563,1643,1644,1645],[]),([287,0,1,2,3,117,4,5],[2,103,1027,1383,1425,1560,1561,1646,1647],[]),([0,1,83,294,3,4,5],[25,103,1070,1200,1648,1649],[1]),([0,1,2,182,4,5,62],[2,16,70,145,169,194,266,349,1650,1651],[]),([287,0,1,294,3,4,5],[25,103,1027,1069,1070,1652,1653],[]),([0,107,1,2,3,4,5,114],[16,25,51,328,345,348,393,427,1117,1118,1119,1358,1359,1620,1654],[0]),([353,0,1,2,3,4,5],[2,43,51,89,137,138,349,1655,1656,1657,1658,1659],[]),([177,0,1,2,3,4,5,127],[25,140,141,143,255,264,333,608,1146,1660,1661],[0,1]),([0,16,1,2,3,6,4,5,34],[2,16,25,42,103,158,168,428,454,688],[0]),([0,16,1,2,3,6,4,5],[2,8,16,43,51,103,334,371,669,670,671,817,1344,1345],[0,1]),([303,0,1,2,3,5,7],[25,51,742,1662,1663],[1]),([0,1,2,3,4,5,354],[8,25,103,1202,1664,1665,1666,1667],[]),([0,1,2,72,6,4,5,62],[2,25,43,145,438,730,736,737,738,739],[]),([105,0,1,2,3,4,5,178],[8,16,25,42,51,256,301,501,638,876,877,1318,1668,1669,1670],[]),([0,1,2,3,4,5,178,355],[2,42,256,1671,1672,1673,1674],[]),([175,0,356,1,2,3,4,5],[16,42,50,139,575,1675,1676,1677],[]),([0,1,2,3,4,5,357],[51,103,1071,1678,1679,1680,1681,1682],[]),([81,285,0,2,3,4,5],[16,103,139,841,1022,1239,1290,1683,1684,1685],[]),([358,0,1,2,3,4,5,181],[25,103,362,1198,1199,1201,1686,1687,1688,1689],[1]),([359,0,1,2,3,4,5],[8,16,42,89,137,139,349,1690,1691,1692,1693,1694],[]),([167,25,0,1,2,3,6,4,5],[2,16,156,159,166,168,675],[0]),([0,107,1,2,3,306,4,5],[25,51,70,383,1205,1358,1359,1695,1696,1697,1698],[]),([0,1,2,360,3,4,5],[2,51,138,280,349,1070,1200,1699,1700,1701,1702,1703],[0]),([0,1,2,3,72,73,5],[2,156,185,688,1704,1705],[0]),([227,93,157,0,2,3,5],[2,138,457,512,514,635,1003,1706,1707,1708,1709],[0]),([177,0,1,3,213,4,5],[2,43,51,1710,1711,1712,1713,1714,1715,1716],[1]),([177,0,1,2,3,4,5,114],[16,25,255,345,393,395,396,502,1117,1118,1654,1661,1717],[0]),([175,0,1,2,4,5,62],[16,25,42,349,1718,1719],[0]),([0,1,361,2,3,4,5],[42,43,51,349,508,563,1720,1721,1722],[]),([362,0,1,2,3,4,5],[2,8,51,89,137,138,349,1347,1723,1724,1725,1726],[]),([227,157,0,9,2,3,5],[487,512,866,1619,1706,1708,1727,1728,1729],[0]),([162,177,0,1,2,3,4,5],[8,16,25,139,149,416,418,501,1065,1144,1661,1717,1730],[]),([0,1,2,138,4,5,62],[16,25,103,441,1230,1731,1732],[1]),([0,1,2,3,363,4,5],[16,103,138,139,1733,1734,1735,1736,1737,1738],[]),([0,1,2,364,3,4,5],[2,43,303,349,429,442,1739,1740,1741,1742,1743,1744,1745],[]),([167,0,107,38,3,4,5],[8,70,92,253,311,332,394,673,676,1746,1747,1748],[]),([0,1,2,3,4,5,87],[16,42,43,103,249,1151,1749,1750,1751,1752],[0]),([227,0,1,9,6,4,5],[2,16,22,33,34,59,186,1753,1754,1755,1756],[0]),([105,0,1,2,182,4,5],[8,16,138,301,638,1146,1757,1758,1759,1760,1761],[]),([0,1,2,215,3,91,4,5],[2,25,88,597,598,602,638,1612,1762,1763,1764],[]),([0,1,2,86,3,4,5,62],[16,25,43,103,371,441,538,1151,1738,1765,1766],[0]),([287,0,1,3,213,4,5],[2,25,43,909,911,914,1293,1767,1768,1769],[]),([0,1,2,3,100,4,5,34],[16,25,42,70,103,152,156,163,164,454,697,698],[0]),([0,1,2,3,6,4,5,47],[2,7,8,16,43,50,72,73,103,156,167,322,341,432,439,460,1770,1771],[0,1]),([162,0,107,1,2,3,4,5],[8,16,25,50,139,149,312,327,404,1065,1358,1359,1772],[0]),([93,0,1,2,3,4,5,47],[7,16,43,50,73,322,431,432,436,457,460,462,634,1773],[0]),([175,157,0,1,2,3,4,5],[2,7,42,139,575,578,579,999,1000],[]),([167,185,186,0,1,2,3,5],[16,103,284,429,673,969,1774,1775,1776,1777,1778],[]),([0,1,2,3,4,5,47,87],[7,42,72,303,432,469,1779,1780,1781,1782],[0,1]),([185,186,0,1,2,3,4,5,187],[2,42,51,284,969,970,973,995,1783],[]),([365,0,1,2,3,4,5],[7,8,16,50,89,103,137,1784,1785,1786,1787],[]),([0,1,9,2,3,4,5,158],[7,51,139,412,487,814,864,865,866,1788,1789,1790,1791,1792,1793],[0]),([93,347,0,1,3,4,5],[25,42,1249,1611,1794,1795],[]),([18,0,2,3,5],[4,63,106,110],[0,1]),([157,0,1,2,3,4,5,34],[2,7,16,25,42,152,156,697,698,999,1000],[0]),([167,285,0,1,2,3,4,5],[16,51,63,103,673,676,1234,1237],[]),([0,1,2,366,3,4,5],[2,8,50,51,138,1112,1725,1796,1797,1798,1799,1800],[]),([93,0,16,2,3,17,5],[2,457,462,494,500,1332,1333,1801,1802],[0]),([0,1,2,39,3,4,5,58],[16,42,103,302,508,559,560,563,982,983,1803],[]),([0,1,2,48,3,4,5],[80,138,371,466,493,497,848,1804,1805,1806,1807],[0]),([0,1,2,3,4,5,214],[2,50,103,914,1808,1809,1810,1811],[]),([0,1,2,3,4,5,368],[2,16,42,103,1812,1813,1814,1815],[]),([190,0,1,2,3,4,5],[2,8,43,89,137,138,139,167,168,349,1816,1817,1818,1819,1820,1821,1822],[0,1]),([369,0,1,2,3,4,5],[25,50,51,89,137,1160,1823,1824],[]),([0,16,1,2,6,4,5,62],[2,16,25,103,145,371,438,736,737,739,746,1825],[0,1]),([0,16,1,2,3,6,4,5,58],[2,8,16,42,103,167,439,508,567],[0]),([0,1,2,3,4,5,34],[2,16,50,51,158,230,231,428,1826,1827],[0]),([93,0,1,2,3,4,5,158],[2,7,412,414,457,633,634,635,814,1788,1789,1792,1828],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_1 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_1 = true := by decide +kernel
def N_22_8_2 : List NodeSpec := [([0,1,2,250,3,4,5,58],[42,51,294,508,515,559,560,563,567,668,752,1287,1288,1289,1829],[]),([0,1,2,370,6,4,5],[2,8,42,43,1830,1831,1832],[]),([287,0,16,1,3,6,4,5],[2,8,16,25,103,371,439,466,1293,1833,1834],[]),([0,16,1,2,3,4,5,34],[2,16,25,42,51,103,139,152,156,158,428,439,454,697,698,699,1344,1345],[0]),([0,1,2,3,6,174,4,5],[2,7,16,50,51,103,166,167,168,232,297,341,342,859,860,861,869,1835,1836],[0]),([171,0,16,1,2,3,4,5],[2,16,50,103,138,156,1344,1345,1837,1838],[]),([371,0,1,2,3,4,5],[7,8,43,51,89,137,866,906,917,1839,1840,1841],[]),([0,1,225,2,3,4,5],[16,138,303,371,462,510,631,1842,1843,1844,1845,1846],[0]),([372,0,1,2,3,4,5],[25,50,89,137,139,349,638,1847,1848],[]),([0,16,1,2,3,4,5,207],[8,16,42,371,399,471,652,1344,1345,1387,1388,1849,1850],[0,1]),([167,0,32,1,2,3,6,4,5],[2,16,156,165,167,168,676,1851],[0]),([105,0,1,2,38,3,4,5,62],[16,25,194,274,275,301,347,1063,1110,1112,1170],[0]),([93,0,16,1,2,3,4,5,62],[16,25,43,145,194,334,441,462,471],[0]),([262,0,1,2,3,5,7],[51,138,349,657,770,1727,1852,1853,1854,1855],[]),([175,0,16,1,2,3,4,5],[16,42,50,508,578,579,1344,1345,1677],[0]),([0,1,2,373,4,5,62],[7,16,25,103,194,349,1856,1857],[]),([0,1,2,367,3,4,5,62],[2,7,194,538,580,1815,1858,1859],[]),([0,1,2,374,3,4,5],[2,50,51,70,138,302,1063,1252,1860,1861,1862,1863],[]),([262,0,1,2,3,17,5],[43,50,51,487,1855,1864,1865,1866],[]),([226,0,1,2,3,4,5],[8,25,89,137,1866,1867],[0]),([0,1,9,6,4,17,5],[2,22,33,34,174,186,1866,1868,1869,1870],[0]),([85,316,0,2,3,4,5],[16,25,194,441,1871,1872,1873],[0]),([271,0,1,2,4,5,62],[7,16,25,103,194,1874,1875,1876],[]),([334,0,1,2,6,4,5],[8,25,739,1877,1878,1879,1880],[]),([0,1,2,39,3,6,4,5],[2,103,166,167,168,341,342,688,982,983,984,985],[]),([0,1,2,3,375,4,5],[156,166,688,1881,1882,1883,1884],[]),([0,1,2,242,6,4,5],[2,42,51,1270,1885,1886,1887],[]),([25,0,1,2,3,4,5,34],[2,16,70,152,157,158,428,697,698,699,1888,1889],[0]),([376,0,1,2,3,4,5],[25,42,89,137,156,166,688,1890,1891],[]),([177,0,1,2,126,194,5],[138,255,306,308,309,1144,1146,1313,1315,1892,1893,1894],[]),([377,0,1,2,3,4,5],[2,7,8,16,51,89,137,1895,1896,1897,1898,1899],[]),([0,1,2,378,3,4,5],[2,655,668,934,1900,1901],[]),([93,379,0,1,3,4,5],[2,25,139,457,1866],[]),([0,1,2,3,381,4,5],[25,42,1902,1903,1904,1905,1906,1907,1908],[]),([382,0,1,2,3,4,5],[8,16,42,50,89,137,1909,1910,1911,1912],[]),([0,1,2,3,4,5,383],[51,103,1050,1913,1914,1915,1916,1917,1918],[]),([0,1,384,2,3,4,5],[43,50,487,848,1755,1919,1920,1921],[]),([0,1,2,3,385,4,5],[156,167,688,1922,1923,1924,1925,1926],[]),([0,1,386,2,3,4,5],[25,51,753,1221,1927,1928],[]),([387,0,1,2,3,4,5],[16,42,50,89,137,462,1755,1929,1930],[]),([227,0,1,2,3,6,4,5],[2,16,231,669,670,671,817,1755,1921,1931,1932],[]),([0,32,1,2,3,4,5,34],[2,16,152,158,296,428,454,697,698,699,761,814,1933,1934],[0]),([388,0,1,2,3,4,5],[2,8,16,89,103,137,139,349,1935,1936,1937,1938,1939],[]),([115,0,1,2,3,4,5,47],[2,7,72,73,103,322,431,432,460,1940,1941,1942],[0,1]),([287,0,1,367,3,4,5],[2,7,961,1027,1943,1944],[]),([0,1,2,3,389,4,5],[2,7,1945,1946,1947,1948,1949],[]),([390,0,1,2,3,4,5],[2,7,43,89,137,349,1950,1951,1952,1953],[]),([0,1,2,391,3,4,5],[25,51,1430,1954,1955,1956,1957],[]),([0,1,2,3,6,4,5,158],[2,7,16,156,166,341,342,412,814,1788,1789,1791,1958,1959],[0]),([0,32,2,3,76,4,5],[2,16,166,167,212,760,1960,1961],[0]),([157,0,1,9,6,4,5],[2,22,31,33,34,59,174,186,415,961,1962,1963,1964],[0]),([0,1,2,3,393,4,5],[2,7,51,1965,1966,1967,1968,1969],[]),([185,0,1,2,3,183,4,5],[2,16,284,285,626,627,628,629,971,972,1970],[0]),([0,394,1,2,3,4,5],[7,89,137,166,1971,1972,1973,1974],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_2 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_2 = true := by decide +kernel
def N_22_8 := N_22_8_0 ++ N_22_8_1 ++ N_22_8_2
def B_22_8 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_8
set_option maxRecDepth 500000 in
lemma B_22_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 8 xs.toFinset) B_22_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_22) (raw := r_22) (pspecs := ps_22) (used := [2,4,7,8,16,17,18,22,25,31,33,34,42,43,50,51,59,63,70,71,72,73,77,80,83,84,88,89,92,103,106,110,137,138,139,140,141,142,143,144,145,149,151,152,156,157,158,159,162,163,164,165,166,167,168,169,171,172,174,185,186,187,190,194,196,201,208,209,212,217,220,221,222,225,227,230,231,232,233,234,238,247,249,251,252,253,254,255,256,258,261,262,264,266,267,274,275,278,280,283,284,285,286,287,288,290,294,295,296,297,298,300,301,302,303,306,308,309,310,311,312,314,315,319,322,324,325,327,328,329,330,332,333,334,341,342,343,344,345,347,348,349,353,357,362,368,371,375,383,384,387,388,391,392,393,394,395,396,398,399,400,402,404,407,408,412,414,415,416,418,421,422,425,427,428,429,430,431,432,435,436,438,439,441,442,445,448,449,450,451,454,457,460,462,463,466,467,469,471,476,487,493,494,495,497,500,501,502,508,510,512,514,515,519,520,522,526,530,532,534,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1198,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208,1209,1210,1211,1212,1213,1214,1215,1216,1217,1218,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248,1249,1250,1251,1252,1253,1254,1255,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1296,1297,1298,1299,1300,1301,1302,1303,1304,1305,1306,1307,1308,1309,1310,1311,1312,1313,1314,1315,1316,1317,1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1337,1338,1339,1340,1341,1342,1343,1344,1345,1346,1347,1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1367,1368,1369,1370,1371,1372,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410,1411,1412,1413,1414,1415,1416,1417,1418,1419,1420,1421,1422,1423,1424,1425,1426,1427,1428,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454,1455,1456,1457,1458,1459,1460,1461,1462,1463,1464,1465,1466,1467,1468,1469,1470,1471,1472,1473,1474,1475,1476,1477,1478,1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,1492,1493,1494,1495,1496,1497,1498,1499,1500,1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1529,1530,1531,1532,1533,1534,1535,1536,1537,1538,1539,1540,1541,1542,1543,1544,1545,1546,1547,1548,1549,1550,1551,1552,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689,1690,1691,1692,1693,1694,1695,1696,1697,1698,1699,1700,1701,1702,1703,1704,1705,1706,1707,1708,1709,1710,1711,1712,1713,1714,1715,1716,1717,1718,1719,1720,1721,1722,1723,1724,1725,1726,1727,1728,1729,1730,1731,1732,1733,1734,1735,1736,1737,1738,1739,1740,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1751,1752,1753,1754,1755,1756,1757,1758,1759,1760,1761,1762,1763,1764,1765,1766,1767,1768,1769,1770,1771,1772,1773,1774,1775,1776,1777,1778,1779,1780,1781,1782,1783,1784,1785,1786,1787,1788,1789,1790,1791,1792,1793,1794,1795,1796,1797,1798,1799,1800,1801,1802,1803,1804,1805,1806,1807,1808,1809,1810,1811,1812,1813,1814,1815,1816,1817,1818,1819,1820,1821,1822,1823,1824,1825,1826,1827,1828,1829,1830,1831,1832,1833,1834,1835,1836,1837,1838,1839,1840,1841,1842,1843,1844,1845,1846,1847,1848,1849,1850,1851,1852,1853,1854,1855,1856,1857,1858,1859,1860,1861,1862,1863,1864,1865,1866,1867,1868,1869,1870,1871,1872,1873,1874,1875,1876,1877,1878,1879,1880,1881,1882,1883,1884,1885,1886,1887,1888,1889,1890,1891,1892,1893,1894,1895,1896,1897,1898,1899,1900,1901,1902,1903,1904,1905,1906,1907,1908,1909,1910,1911,1912,1913,1914,1915,1916,1917,1918,1919,1920,1921,1922,1923,1924,1925,1926,1927,1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944,1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,1955,1956,1957,1958,1959,1960,1961,1962,1963,1964,1965,1966,1967,1968,1969,1970,1971,1972,1973,1974]) S_22_ok
  have hm0 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def P_22_9 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [2,7,8,16,17,25,31,33,34,42,43,50,51,63,70,80,83,88,89,92,103,137,138,139,142,145,146,156,158,162,166,167,168,169,194,230,255,274,280,283,284,294,295,297,299,301,302,303,322,324,327,328,332,334,341,342,345,347,348,349,371,383,389,391,392,394,399,400,404,423,427,428,429,431,439,441,442,445,457,460,462,466,471,476,487,501,508,515,538,551,552,554,555,559,560,563,567,568,573,574,578,579,580,597,598,604,605,606,630,631,633,634,635,638,657,658,669,670,673,674,675,676,688,697,698,709,710,723,724,729,736,737,739,742,743,744,745,752,753,760,761,763,770,771,772,774,775,777,778,789,790,813,814,816,828,835,839,840,841,842,848,859,860,864,865,866,870,871,876,877,878,882,883,906,908,909,910,911,913,917,921,925,931,936,937,954,961,962,963,969,971,972,977,978,982,983,984,990,992,993,995,996,997,998,999,1000,1003,1016,1017,1027,1038,1042,1046,1047,1049,1052,1053,1055,1058,1059,1062,1063,1065,1068,1069,1070,1073,1076,1080,1088,1099,1107,1108,1110,1112,1117,1118,1132,1133,1134,1140,1141,1144,1145,1146,1153,1160,1161,1165,1168,1188,1189,1194,1196,1200,1202,1208,1209,1211,1212,1214,1221,1231,1232,1233,1234,1235,1243,1245,1246,1249,1251,1252,1265,1270,1271,1287,1288,1290,1293,1295,1297,1298,1304,1306,1308,1310,1317,1318,1321,1326,1327,1332,1333,1336,1342,1343,1344,1345,1347,1350,1351,1352,1357,1358,1359,1361,1362,1387,1388,1389,1390,1394,1417,1420,1424,1425,1428,1429,1454,1456,1457,1517,1541,1542,1562,1570,1588,1589,1594,1612,1633,1654,1661,1668,1669,1695,1696,1706,1708,1717,1727,1748,1755,1756,1762,1763,1764,1766,1788,1789,1792,1793,1834,1838,1851,1854,1858,1859,1866,1870,1879,1888,1894,1921,1931,1932,1934,1959,1964,1975,1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031,2032,2033,2034,2035,2036,2037,2038,2039,2040,2041,2042,2043,2044,2045,2046,2047,2048,2049,2050,2051,2052,2053,2054,2055,2056,2057,2058,2059,2060,2061,2062,2063,2064,2065,2066,2067,2068,2069,2070,2071,2072,2073,2074,2075,2076,2077,2078,2079,2080,2081,2082,2083,2084,2085,2086,2087,2088,2089,2090,2091,2092,2093,2094,2095,2096,2097,2098,2099,2100,2101,2102,2103,2104,2105,2106,2107,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121,2122,2123,2124,2125,2126,2127,2128,2129,2130,2131,2132,2133,2134,2135,2136,2137,2138,2139,2140,2141,2142,2143,2144,2145,2146,2147,2148,2149,2150,2151,2152,2153,2154,2155,2156,2157,2158,2159,2160,2161,2162,2163,2164,2165,2166,2167,2168,2169,2170,2171,2172,2173,2174,2175,2176,2177,2178,2179,2180,2181,2182,2183,2184,2185,2186,2187,2188,2189,2190,2191,2192,2193,2194,2195,2196,2197,2198,2199,2200,2201,2202,2203,2204,2205,2206,2207,2208,2209,2210,2211,2212,2213,2214,2215,2216,2217,2218]
def N_22_9 : List NodeSpec := [([0,1,2,3,306,4,5],[8,43,50,51,70,139,1695,1696,1975],[0,1]),([175,0,1,2,3,4,5,58],[16,42,43,103,508,559,560,563,567,578,579,1976],[0,1]),([175,0,1,2,3,4,5],[8,16,42,50,51,89,137,138,139,508,578,579,1976],[0,1]),([0,1,2,3,4,5,58,34],[16,42,103,508,551,552,554,555,563,567,568],[0,1]),([0,1,235,2,3,4,5,62],[2,25,43,145,194,303,349,441,538,580,1977,1978,1979,1980],[0,1]),([85,0,1,2,3,4,5,62],[16,139,145,146,169,303,441,538,580,789,790,1981],[0,1]),([0,1,2,3,4,5,58,135],[2,42,50,70,103,508,563,573,574,1073,1982],[0,1]),([0,1,2,3,95,4,5,58],[42,51,63,70,349,392,508,515,563,567,723,724],[0,1]),([0,134,1,2,3,4,5,58],[42,80,349,508,515,559,560,563,567,1188,1189,1983],[0,1]),([167,105,0,1,2,3,5],[16,43,51,63,70,299,674,1541,1542],[0,1]),([105,0,1,2,3,4,5,62],[16,25,43,51,138,145,169,194,299,347,349,441,538,580,1456,1457],[0,1]),([105,0,1,2,3,4,5,58],[8,16,25,42,43,51,63,103,294,299,301,445,508,515,559,560,563,567,638,1984,1985],[0,1]),([105,0,1,2,215,3,4,5],[8,25,51,70,445,597,598,638,1235],[1]),([0,1,2,215,3,4,5],[25,50,51,103,138,139,349,597,598,638,1594,1612],[0,1]),([0,1,2,332,3,4,5],[2,43,50,63,138,139,1145,1986,1987,1988],[0,1]),([105,0,1,2,3,4,5,114],[16,25,51,63,70,349,445,638,1117,1118,1654],[0,1]),([277,0,1,2,3,4,5],[8,16,25,50,51,63,89,137,138,139,349,931,1214,1989],[0,1]),([0,1,83,2,3,4,5,62],[2,16,25,43,63,145,194,280,441,442,1990,1991],[0,1]),([0,1,83,3,92,5],[8,63,138,630,1306,1308,1310],[0,1]),([0,1,2,3,4,5,84],[8,42,43,50,63,139,977,978],[0,1]),([105,0,1,2,3,4,5],[8,43,50,51,63,70,89,137,138,139,1361,1362],[0,1]),([105,0,1,395,2,3,4,5],[25,50,51,301,638,1235,1992,1993],[1]),([0,1,2,3,213,4,5],[2,43,50,51,103,139,908,909,910,911,913],[0,1]),([93,0,1,2,3,4,5,7],[16,43,138,462,633,634,635,657,742,745,770,778,1003,1052,1059,1994,1995,1996],[0,1]),([93,0,1,2,3,4,5,62],[2,16,43,145,169,194,441,457,462,538,580,1996,1997,1998],[0,1]),([167,177,0,1,2,3,4,5],[8,51,63,70,139,255,501,673,674,676,1146,1661,1717,1748,1999,2000],[1]),([177,0,1,2,3,4,5,7],[50,138,501,657,745,770,1052,1059,1144,1146,1265,1661,1717,2001,2002],[0,1]),([0,1,2,3,153,4,5],[8,43,51,139,936,937,1088,2003],[0,1]),([177,0,1,2,3,4,5,62],[16,25,43,70,145,169,194,255,501,538,580,1146,1417,2004,2005],[0,1]),([105,177,0,1,2,3,4,5],[8,16,25,43,51,70,139,301,501,638,1144,1146,1318,1420,1661,1717,1894,2006,2007],[0]),([171,0,1,2,3,4,5],[2,8,16,43,50,51,89,103,137,138,139,156,297,349,1838,2008],[0,1]),([0,1,2,38,3,4,5,7],[103,274,657,742,745,770,1042,1062,1063,1112,2009,2010],[0]),([177,0,1,2,3,4,194,5],[16,43,70,138,255,1144,1146,1249,1251,1252,1304,2011,2012,2013],[0,1]),([0,1,2,294,3,4,5],[2,43,51,103,138,139,349,1068,1069,1070],[0,1]),([185,0,1,2,3,4,5,62],[2,16,25,43,139,145,169,194,283,400,441,538,580,2014,2015],[0,1]),([157,0,1,2,3,4,5,58],[2,8,42,50,63,103,508,559,560,563,2016,2017],[0,1]),([185,105,0,1,2,3,4,5],[16,43,50,51,138,139,284,301,400,429,445,638,876,877],[0]),([0,107,1,2,126,3,4,5],[51,138,142,327,328,383,404,911,1132,1133,1134,2018,2019,2020],[0,1]),([167,93,0,1,2,3,4,5],[8,16,43,51,63,457,462,633,634,635,673,674,675,676,777,1996,2021,2022],[0]),([185,0,1,2,3,4,194,5],[43,138,139,400,429,969,1099,1249,1304,2012,2023,2024],[0,1]),([0,1,2,3,4,5,158],[7,8,43,63,139,814,1788,1789,1792],[0,1]),([287,185,0,1,2,3,4,5],[2,8,283,400,429,969,971,972,1231,1295,2025,2026],[0]),([93,0,1,2,3,4,17,5],[2,138,457,633,634,635,1003,1866,1870,2027,2028,2029,2030],[0,1]),([185,0,1,2,3,6,4,5],[2,8,16,43,139,167,341,342,429,2031,2032],[1]),([0,16,1,2,3,4,5,58],[8,42,63,103,139,334,371,466,508,515,559,560,563,567,2033,2034],[0,1]),([0,107,1,2,3,4,194,5],[16,43,138,328,383,404,1099,1249,1304,2012,2035,2036],[0,1]),([185,0,2,3,4,5,152],[2,16,50,139,283,349,906,969,992,993,1088,2037],[0]),([0,1,9,6,4,5],[8,31,33,34,83],[0]),([0,1,2,3,6,76,4,5],[2,16,50,166,341,342,688,2038,2039],[0,1]),([0,1,2,284,3,4,5],[2,43,50,51,139,1016,1017,1038,1168,1394],[0,1]),([0,1,2,219,3,4,5],[2,8,50,51,103,138,139,303,349,429,1053,1055],[0,1]),([105,0,396,1,2,3,4,5],[25,50,51,70,139,301,445,1235,2040,2041],[]),([0,107,1,2,3,4,5,62],[16,25,43,145,169,327,328,383,441,538,580,2042,2043],[0,1]),([105,0,1,2,3,91,4,5],[16,25,43,50,51,138,301,638,1243,1762,1763,1764,2044,2045],[0,1]),([167,0,1,2,38,3,4,5],[8,51,70,103,274,302,673,674,675,676,1042,1062,1112,2046,2047],[0]),([0,1,83,2,3,91,4,5],[2,43,50,70,280,1200,1243,2048,2049,2050,2051],[0,1]),([287,180,0,1,2,3,4,5],[70,139,1027,1070,1202,1293,1295,1336,1424,1425,2052,2053,2054,2055,2056,2057],[0,1]),([105,0,107,1,2,3,4,5],[8,16,25,50,51,138,327,348,383,404,427,445,638,876,877,1317,1358,1359,2058,2059],[0]),([0,107,1,2,3,4,5,7],[139,327,383,404,657,742,770,1052,1059,1358,1359,2060,2061],[0,1]),([192,0,1,2,3,4,5],[43,50,51,89,103,137,138,139,274,302,303,349,2062,2063,2064],[0,1]),([0,1,2,3,6,4,17,5],[2,8,43,156,166,341,342,688,1866,2065,2066,2067],[0,1]),([0,1,2,3,6,4,5,58],[2,8,16,43,103,156,167,297,349,508,563,567,1058,1080],[0]),([81,0,2,38,3,4,5],[8,50,103,139,274,302,813,1290,1389,1390],[0,1]),([81,93,0,1,2,3,4,5],[8,16,43,139,457,462,633,634,813,816,835,841,842,1003,1290,1996,2068],[0,1]),([0,1,2,3,4,5,207],[8,16,42,50,51,139,399,457,1387,1388,1996],[0,1]),([0,1,2,39,3,4,5],[43,50,51,138,139,423,982,983,984],[0,1]),([0,1,2,293,3,4,5],[2,43,50,51,103,138,349,1046,1047,1049],[0,1]),([185,93,0,1,2,3,4,5],[2,8,16,43,50,139,400,429,462,633,634,1003,2069,2070],[0]),([167,0,1,2,3,6,4,5],[2,8,16,43,51,103,156,166,167,297,341,342,673,674,675,676,1851,2071],[0]),([0,1,312,2,3,4,5],[8,43,51,138,139,349,1428,1429,2072],[0]),([81,0,1,83,2,3,4,5],[8,63,138,139,280,442,813,816,882,883,1517,2051,2073],[0,1]),([81,105,0,1,2,3,4,5],[16,25,50,51,63,139,299,445,638,813,816,841,842,876,877,1290,2074],[0]),([167,0,107,1,2,3,4,5],[8,50,51,63,139,327,328,383,673,674,675,1358,1359,2075,2076,2077,2078],[0,1]),([0,1,2,3,6,4,5,152],[2,50,70,156,166,297,2079,2080],[0]),([289,0,89,1,2,3,4,5],[50,139,391,1049,1076,1161,2081,2082,2083,2084,2085,2086,2087,2088],[0,1]),([0,1,2,3,6,4,73,5],[2,7,16,51,103,167,688,771,772,774,775],[0,1]),([0,1,2,38,3,4,92,5],[8,50,103,302,753,1063,1112,1221,2089,2090],[0]),([0,1,2,38,3,6,4,5],[2,8,43,50,103,166,688,2091,2092],[0]),([0,1,2,86,3,4,5],[43,50,51,103,138,303,349,371,476,1766,2093],[0,1]),([287,0,89,1,2,3,4,5],[8,50,139,389,391,1049,1161,1231,1293,1424,1425,2055,2081,2083,2094,2095],[0,1]),([0,1,2,38,3,4,5,58],[2,8,42,50,70,103,274,508,563,1063,2096,2097],[0]),([289,185,0,1,2,3,4,5],[2,43,138,400,429,969,971,972,1196,1271,2087],[0]),([0,1,2,38,3,4,5,62],[16,25,43,70,103,145,169,194,274,302,441,1112,2098,2099],[0]),([162,0,1,2,3,4,5],[8,16,25,50,89,137,138,139,349,1065,2100,2101],[0,1]),([287,0,16,1,2,3,4,5],[8,63,138,371,466,1231,1293,1344,1345,2102,2103],[0,1]),([185,0,1,83,2,3,4,5],[2,8,51,138,139,280,283,400,429,442,882,883,969,1200,2104,2105,2106,2107],[0]),([0,1,2,38,3,4,194,5],[2,16,43,50,70,103,302,1063,1099,1249,1252,2108,2109],[0,1]),([0,107,38,3,4,5],[8,88,92,139,332,394],[0,1]),([105,0,1,2,38,3,4,5],[2,8,16,43,51,70,103,301,445,638,1042,1062,1063,1110,2110,2111,2112],[0,1]),([105,0,1,397,2,3,4,5],[25,51,301,445,638,876,877,1235,2113,2114],[0]),([0,1,2,3,4,5,178],[8,42,43,51,139,255,501,1668,1669],[0,1]),([167,185,0,1,2,3,4,5],[16,43,50,51,283,429,673,674,675,676,969,971,972,2077,2078,2115,2116],[0,1]),([0,1,2,3,72,6,4,5],[2,16,51,138,156,162,688,709,710,729],[0,1]),([236,0,1,2,3,4,5,58],[2,8,42,50,349,508,515,559,560,563,2117,2118,2119],[0,1]),([0,1,2,3,4,5,47],[7,8,43,50,63,322,431,460],[0,1]),([93,0,1,3,4,5,58],[8,16,42,349,457,508,515,962,963,1996],[0,1]),([0,1,2,3,4,5,108],[8,42,43,50,51,327,328,1297,1298],[0,1]),([93,0,1,2,3,91,4,5],[16,43,50,70,1243,1245,1562,1762,1763,2120,2121,2122],[0]),([185,0,1,2,3,4,92,5],[2,8,16,103,138,139,400,429,753,969,1160,1221,1232,1233,2123,2124,2125],[0,1]),([167,0,1,9,2,3,4,5],[8,43,51,324,487,673,674,675,676,848,864,865,866,2077,2078,2126,2127],[0]),([227,157,0,2,3,5],[63,138,139,1706,1708,2128],[0,1]),([0,1,2,3,95,4,5],[43,50,51,63,70,139,392,515,723,724,2129],[0,1]),([212,0,1,2,3,4,5],[8,16,50,51,63,70,89,137,139,1326,1327,2130],[0]),([287,0,1,2,3,91,4,5],[2,70,295,1027,1243,1245,1762,1763,2050,2131,2132],[0,1]),([0,1,2,3,4,5,281],[2,8,16,50,51,139,283,969,2133,2134,2135],[0,1]),([69,0,1,2,3,4,5],[16,17,50,51,70,89,103,137,139,349,763,828,2136],[0,1]),([303,0,1,2,3,4,5],[8,43,50,51,89,137,138,139,349,1351,1352,2137],[0]),([0,16,2,3,17,5],[50,63,139,1332,1333,2138],[0,1]),([105,0,1,2,3,5,7],[16,25,43,51,138,299,349,1588,1589],[0,1]),([0,16,1,9,2,3,4,5],[51,324,334,371,466,487,848,864,865,866,1165,1344,1345,1727,2139,2140],[0]),([0,1,9,2,3,4,5,152],[50,70,139,324,487,866,906,917,921,2037,2141,2142],[0]),([0,16,1,2,3,6,4,5],[2,8,16,43,103,167,168,341,342,371,439,466,688,2143,2144],[0,1]),([93,0,16,1,2,3,4,5],[8,16,43,51,138,139,334,371,462,466,471,631,635,1003,1344,1345,1633,2145,2146],[0]),([105,0,1,2,3,6,4,5],[2,8,16,25,43,51,103,138,301,445,638,1357,1454,1879,2147,2148,2149,2150,2151],[1]),([334,0,1,2,3,4,5],[2,8,63,89,137,138,139,349,2152,2153,2154],[0,1]),([0,1,2,380,3,4,5],[42,43,50,63,103,1755,2155,2156],[0]),([227,0,1,9,2,3,4,5],[139,487,848,864,865,1727,1755,1921,1931,1932,2157,2158],[0]),([0,1,2,220,3,4,5],[43,50,51,103,138,303,813,870,871,878,2159],[0,1]),([177,0,1,2,126,3,4,5],[51,70,138,142,501,911,925,1132,1133,1146,1321,2160,2161],[0,1]),([99,0,1,2,3,6,4,5],[2,8,43,51,156,166,167,341,342,688,2162,2163],[0]),([227,0,1,2,3,6,4,5],[2,8,16,43,103,156,167,341,342,688,1755,1921,2164,2165],[0]),([185,0,1,2,3,4,5,7],[16,43,138,283,400,429,657,742,745,770,971,972,1052,1059,2166,2167,2168],[0,1]),([0,1,2,250,3,4,5],[43,50,51,70,139,658,752,1287,1288],[0,1]),([227,93,0,1,2,3,4,5],[16,43,138,457,462,633,634,1003,1755,1756,1931,1932,2169,2170],[0]),([0,1,2,367,3,4,5],[2,43,51,103,139,349,961,1858,1859,2171],[0,1]),([157,0,1,9,2,3,4,5],[51,138,324,487,848,864,865,866,961,998,999,1000,1727,1793,2172,2173,2174],[0]),([0,1,2,314,3,4,5],[2,43,50,51,103,139,1342,1343,1347,1350,2175],[0]),([157,0,1,2,3,6,4,5],[2,51,156,166,167,297,341,342,688,1959,2174,2176,2177],[0,1]),([287,0,1,2,126,3,4,5],[63,138,911,925,1027,1132,1133,1134,1231,1293,2178,2179],[0,1]),([185,186,0,1,2,3,4,5],[2,16,42,43,50,51,103,284,400,429,604,605,606,971,972,990,995,1270,1271,2180,2181,2182],[0,1]),([271,0,1,2,3,4,5],[2,7,8,16,51,89,137,138,139,2183,2184,2185],[0,1]),([0,32,1,2,3,6,4,5],[2,7,8,43,166,167,297,341,342,688,760,761,1934],[0,1]),([93,157,0,1,2,3,4,5],[2,50,51,138,139,457,462,633,634,635,961,999,1000,1003,1964,1996,2174,2186,2187,2188],[0]),([287,157,0,1,2,3,4,5],[2,63,138,139,961,999,1000,1027,1424,1425],[0]),([93,0,1,2,3,4,5,152],[2,50,70,457,635,917,921,954,1088,1996,2037,2189,2190],[0,1]),([0,1,83,2,3,4,5,152],[2,50,63,917,1088,1200,2051,2191,2192],[0,1]),([105,0,1,2,3,4,5,152],[16,25,43,50,51,63,70,299,301,638,917,921,1088,2037,2193,2194,2195],[0,1]),([287,105,0,1,2,3,4,5],[8,16,25,51,63,299,301,445,638,876,877,1027,1231,1293,1424,1425,2055,2196],[0]),([0,1,2,3,174,4,5],[8,43,50,51,859,860,1290,2197],[0,1]),([212,0,1,2,3,4,5,62],[16,25,51,63,145,194,347,441,538,580,1140,1141],[0]),([81,0,1,9,2,3,4,5],[8,139,324,487,813,816,841,842,848,864,865,1727,2198,2199],[0]),([81,0,1,2,3,6,4,5],[2,8,16,43,50,103,139,156,167,297,341,342,688,813,816,2200,2201],[0]),([262,0,1,2,3,4,5],[8,43,50,51,70,89,137,138,139,349,839,840,1854],[0]),([289,0,1,2,3,91,4,5],[2,139,295,1194,1243,1245,1246,1762,1763,2084,2202],[0,1]),([0,1,9,2,3,4,5,7],[324,657,742,745,770,848,864,865,866,1052,1059,1727,2203,2204],[0,1]),([155,0,1,2,3,6,4,5],[2,16,139,167,341,342,2205,2206],[0,1]),([25,0,1,2,3,6,4,5],[2,8,43,50,70,166,167,297,341,342,688,743,744,1888],[0,1]),([0,1,2,3,6,4,92,5],[2,8,16,43,51,103,167,688,753,1160,1221,2207,2208],[0]),([171,0,1,2,3,6,4,5],[2,8,16,43,167,297,341,342,688,1838,2008],[0,1]),([69,0,1,2,3,6,4,5],[2,16,51,70,103,138,166,167,168,341,342,688,763,828],[0,1]),([185,0,1,2,3,4,5,58],[8,16,42,103,283,429,508,515,559,560,563,567,969,2209,2210,2211],[0,1]),([0,1,2,6,4,5,62],[8,16,43,103,145,736,737,739,2212],[0,1]),([0,1,2,3,4,5,29],[8,25,43,50,51,139,324,487,996,997],[0]),([287,0,1,3,6,4,5],[2,8,16,43,156,297,1293,1834,2213],[0,1]),([0,1,2,3,72,4,5],[2,8,43,50,51,139,162,709,710,729],[0,1]),([0,1,2,3,6,4,5,7],[2,16,103,166,167,297,341,342,657,688,742,745,770,1107,1108],[0]),([0,1,2,3,4,5,34],[16,50,51,103,139,156,158,297,428,697,698],[0,1]),([142,0,1,2,3,4,5,62],[2,16,145,169,194,303,441,538,580,1208,1209,1211,1212],[0,1]),([0,1,2,3,6,4,5,34],[2,16,103,156,158,167,297,428,697,698],[0,1]),([0,1,9,2,3,4,17,5],[50,487,864,865,866,1727,1866,2027,2029,2067,2214,2215],[0]),([0,1,2,3,6,4,5],[2,8,16,43,50,51,138,139,230,669,670],[0,1]),([0,1,2,3,4,5,114],[8,16,25,50,51,63,139,345,1117,1118],[0,1]),([93,0,1,2,3,4,194,5],[43,138,457,462,635,1003,1099,1249,1252,1304,2012,2216,2217],[0,1]),([289,180,0,1,2,3,4,5],[50,139,1070,1076,1194,1196,1202,1336,2052,2053,2084,2085,2218],[1]),([285,0,1,2,3,4,5],[2,8,16,50,51,89,137,138,139,349,1153,1234,1570],[0,1]),([93,105,0,1,2,3,4,5],[8,16,43,51,138,301,445,462,631,635,638,876,877,1003],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_9 : checkNodesBT W_22 g_22 F_22 P_22_9 A_22 B_22_8 9 N_22_9 = true := by decide +kernel
def B_22_9 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_9
set_option maxRecDepth 500000 in
lemma B_22_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 9 xs.toFinset) B_22_9 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_8_ok C_22_9
def P_22_10 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [8,43,50,51,63,77,83,88,89,137,138,139,274,283,297,299,324,327,334,341,342,349,501,559,560,630,633,634,841,842,864,865,876,877,882,883,921,971,972,999,1000,1042,1052,1059,1062,1232,1233,1235,1236,1344,1345,1358,1359,1424,1425,1661,1717,1931,1932,1996,2027,2029,2037,2051,2077,2078,2084,2085,2174]
def N_22_10 : List NodeSpec := [([167,0,1,2,3,4,5],[8,43,50,63,89,137,139,349,2077,2078],[0,1]),([0,1,2,3,4,5,7],[8,43,50,89,137,138,139,349,1052,1059],[0,1]),([287,0,1,2,3,4,5],[8,43,50,63,89,137,138,139,349,1424,1425],[0,1]),([0,1,2,3,4,5,58],[8,43,50,63,139,349,559,560],[0,1]),([105,0,1,2,3,4,5],[8,43,50,51,89,137,138,139,299,349,876,877,1235],[0,1]),([0,1,2,3,4,92,5],[8,43,50,63,138,139,1232,1233,1236],[0,1]),([0,107,1,2,3,4,5],[8,43,50,89,137,138,327,349,1358,1359],[0,1]),([0,1,2,38,3,4,5],[8,43,50,138,139,274,1042,1062],[0,1]),([185,0,1,2,3,4,5],[8,43,50,77,89,137,138,139,283,349,971,972],[0,1]),([177,0,1,2,3,4,5],[8,43,88,89,137,138,139,349,501,1661,1717],[0,1]),([227,0,1,2,3,4,5],[8,43,50,63,89,137,138,1931,1932],[0,1]),([93,0,1,2,3,4,5],[8,43,50,83,89,137,138,139,349,633,634,1996],[0,1]),([0,1,2,3,4,17,5],[8,43,63,89,137,138,139,2027,2029],[0,1]),([0,1,83,2,3,4,5],[8,43,50,51,138,139,882,883,2051],[0,1]),([0,1,9,2,3,4,5],[8,43,50,89,137,138,139,324,864,865],[0]),([0,16,1,2,3,4,5],[8,43,50,51,89,137,138,139,334,349,1344,1345],[0,1]),([0,1,2,3,4,5,152],[8,43,63,139,349,921,2037],[0,1]),([289,0,1,2,3,4,5],[8,43,50,63,89,137,138,139,630,2084,2085],[0,1]),([157,0,1,2,3,4,5],[8,43,50,51,89,137,138,139,349,999,1000,2174],[0,1]),([81,0,1,2,3,4,5],[8,43,50,63,89,137,138,349,841,842],[0,1]),([0,1,2,3,6,4,5],[8,43,50,138,139,297,341,342],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_10 : checkNodesBT W_22 g_22 F_22 P_22_10 A_22 B_22_9 10 N_22_10 = true := by decide +kernel
def B_22_10 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_10
set_option maxRecDepth 500000 in
lemma B_22_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 10 xs.toFinset) B_22_10 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_9_ok C_22_10
def P_22_11 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 [89,137,349]
def N_22_11 : List NodeSpec := [([0,1,2,3,4,5],[89,137,349],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_11 : checkNodesBT W_22 g_22 F_22 P_22_11 A_22 B_22_10 11 N_22_11 = true := by decide +kernel
def B_22_11 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_11
set_option maxRecDepth 500000 in
lemma B_22_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 11 xs.toFinset) B_22_11 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_10_ok C_22_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck r_22 g_22 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT B_22_11 r_22 = true := by decide +kernel
lemma low_22 : Lower r_22 g_22 12 := lower_of_forestBT root_22_ok B_22_11_ok root_22_in

def g_orig := 0xfeeeeee8fee8eaa8feeeeee8fee8eaa8feeeeee8fee8eaa8feeeeee8fee8eaa8
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,4)]) (by decide +kernel) low_22
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071592 * 2 ^ 32 + 4276677288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.and,[2,3]⟩,⟨.or,[3,2]⟩,⟨.and,[5,4]⟩,⟨.or,[5,4]⟩,⟨.or,[6,9]⟩,⟨.or,[8,7]⟩,⟨.and,[10,1]⟩,⟨.and,[6,4]⟩,⟨.or,[0,13]⟩,⟨.and,[1,0]⟩,⟨.or,[15,11]⟩,⟨.or,[12,14]⟩,⟨.and,[16,17]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_44776

open PEqualNP.Outside.L_meta_44776 in
theorem PEqualNP.Outside.L_meta_44776 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4276677288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4276677288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
