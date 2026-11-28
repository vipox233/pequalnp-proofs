import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45594
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
def g_3 := (d 0xfee0fee0fee0fee0)
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_4 := (d 0xfffefe80fffefe80)
def r_4 : List Nat := varsOf 31
def p_4 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14,17,17,18,18,19,20,20,21,22,24,24]
def q_4 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6,16,1,16,2,3,16,4,5,6,16,8]
def F_4 : Nat := fullMask 23
set_option maxHeartbeats 0 in
lemma gp_4 : goodPairs g_4 p_4 q_4 := goodPairs_of (by decide +kernel)
def W_4 : BT Decor := buildWiresBT 7 (mkBase p_4 q_4 r_4) [(1,2,1),(1,1,3),(1,2,4),(0,6,7),(1,3,4),(3,2,9),(0,2,0),(1,10,11),(1,2,0),(1,13,3),(1,14,4),(3,2,15),(1,0,3),(1,17,4),(3,1,18),(0,2,9),(1,2,3),(1,21,4),(3,20,22),(0,0,1),(1,24,3),(1,25,4),(3,2,26),(1,1,13),(1,28,3),(2,29,4),(3,2,17),(1,0,4),(0,1,18),(1,13,4),(2,17,4),(3,3,32),(1,1,4),(0,17,37),(0,0,22),(1,0,1),(1,40,3),(1,41,4),(3,2,42),(3,1,9),(1,44,0),(2,45,2),(3,0,9),(2,6,4),(1,48,0),(1,6,4),(0,0,50),(2,0,9),(2,31,4),(1,10,0),(3,2,32),(1,55,3),(3,20,0),(3,2,6),(1,58,0),(3,5,9),(1,24,4),(2,28,4),(2,25,4),(0,1,2),(3,64,9),(2,2,3),(3,66,7),(0,0,9),(3,2,41),(1,40,4),(1,52,4),(2,41,4),(3,5,17),(2,0,4),(1,74,3)]
lemma W_4_ok : btAll (fun x => faithful p_4 q_4 x ∧ x.1 < 2^256) W_4 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_4 : List (List (Nat × Nat)) := [[],[(3,4)],[(1,2)],[(1,2),(3,4)],[(0,1)],[(0,1),(3,4)],[(0,2),(1,2)],[(0,2),(1,2),(3,4)],[(0,1),(1,2)],[(0,1),(1,2),(3,4)],[(0,2)],[(0,2),(3,4)]]
def A_4 : BT (List (Nat × Nat)) := btOfList 4 al_4
set_option maxHeartbeats 0 in
lemma A_4_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_4 = g_4) A_4 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_4_0 : Slice r_4 g_4 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_1 : Slice r_4 g_4 (identDom 0 2) 7 := by
  have hc : Lower (varsOf 27) (d 0xffeeee88ffeeee88) 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_2 : Slice r_4 g_4 (identDom 1 2) 7 := by
  have hc : Lower (varsOf 27) (d 0xffeeee88ffeeee88) 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_3 : Slice r_4 g_4 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_4 : Slice r_4 g_4 (subcubeFast 16 0) 6 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_4_5 : Slice r_4 g_4 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_6 : Slice r_4 g_4 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffafa00fffafa00) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_7 : Slice r_4 g_4 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeeee00ffeeee00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_8 : Slice r_4 g_4 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_9 : Slice r_4 g_4 (subcubeFast 5 0) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_10 : Slice r_4 g_4 (subcubeFast 6 0) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 0) (by decide +kernel) hc
def S_4 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,7),some (identDom 0 2,7),some (identDom 1 2,7),some (subcubeFast 8 0,6),some (subcubeFast 16 0,6),some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 3 0,4),some (subcubeFast 5 0,4),some (subcubeFast 6 0,4)]
lemma S_4_ok : btAll (fun o => ∀ p, o = some p → Slice r_4 g_4 p.1 p.2) S_4 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_4_0) (forall_cons (fun _ h => by cases h; exact sl_4_1) (forall_cons (fun _ h => by cases h; exact sl_4_2) (forall_cons (fun _ h => by cases h; exact sl_4_3) (forall_cons (fun _ h => by cases h; exact sl_4_4) (forall_cons (fun _ h => by cases h; exact sl_4_5) (forall_cons (fun _ h => by cases h; exact sl_4_6) (forall_cons (fun _ h => by cases h; exact sl_4_7) (forall_cons (fun _ h => by cases h; exact sl_4_8) (forall_cons (fun _ h => by cases h; exact sl_4_9) (forall_cons (fun _ h => by cases h; exact sl_4_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_4 : BT (Option PoolSpec) := btOfList 7 [q 3 [36872,36873,90195],q 3 [],q 4 [],q 10 [],q 0 [],q 1 [],q 3 [36865,73739],q 3 [16453,73739],q 9 [],q 7 [],q 3 [36866,36867],q 1 [16397,36875,41],q 3 [16385,131083],q 3 [16393],q 4 [12297],q 3 [36872,83],q 1 [16397,36875],q 2 [16397,36887],q 0 [16481,12305],q 5 [],q 6 [],q 0 [9,12297],q 1 [53253],q 2 [9],q 0 [12385,16486],q 0 [12385,16485],q 0 [16385,12305],q 1 [16385,12305],q 1 [12341,57355],q 4 [12289,69643],q 2 [],q 0 [16397,36865],q 1 [16397,36865],q 0 [16397,36864],q 1 [16397,36864],q 3 [36864,36865],q 1 [12297,57355],q 3 [36875],q 0 [16397],q 1 [16397],q 3 [36864],q 3 [16454],q 4 [12289],q 0 [12289,16454],q 1 [12289,16454],q 3 [16453],q 0 [12289],q 1 [12289],q 3 [16389],q 0 [16389],q 8 [],q 3 [4097],q 3 [16385],q 3 [4096],q 0 [12385],q 1 [12297],q 3 [9],q 0 [8353],q 1 [4097],q 0 [12297],q 1 [4097,12297],q 2 [4097,12297],q 2 [4097],q 3 [16386],q 4 [12585],q 3 [69643],q 3 [36865],q 1 [12289,69643],q 2 [16397,36875],q 4 [36875],q 3 [36866],q 0 [12289,16453],q 1 [12289,16453],q 3 [69637],q 4 [4097],q 2 [16397],q 4 [4096]]
def B_4_2 : BT (List (List Nat)) := BT.empty
lemma B_4_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 2 xs.toFinset) B_4_2 := .empty
def U_4_3 : List Nat := []
def P_4_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_4 r_4 S_4 ps_4 U_4_3
def N_4_3 : List NodeSpec := [([0,5,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_3 : checkNodesBT W_4 g_4 F_4 P_4_3 A_4 B_4_2 3 N_4_3 = true := by decide +kernel
def B_4_3 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_3
set_option maxRecDepth 500000 in
lemma B_4_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 3 xs.toFinset) B_4_3 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_2_ok C_4_3
def U_4_4 : List Nat := (r 0 4)
def P_4_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_4 r_4 S_4 ps_4 U_4_4
def N_4_4 : List NodeSpec := [([0,12,1,3,4],[],[]),([16,19,0,3,4],[],[]),([0,5,3,8,4],[],[0]),([23,0,1,3,4],[0],[]),([27,0,1,3,4],[],[]),([30,0,1,2,3],[],[]),([31,1,2,32,9],[],[]),([16,0,33,3,4],[],[]),([0,1,21,34,9],[1],[]),([35,36,0,1,2],[],[]),([0,1,2,38,9],[1,2],[8]),([10,39,1,3,4],[],[]),([16,0,1,3,4],[],[]),([0,5,6,7,9],[3],[0]),([43,0,1,3,4],[],[]),([46,0,1,3,4],[],[]),([35,47,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_4 : checkNodesBT W_4 g_4 F_4 P_4_4 A_4 B_4_3 4 N_4_4 = true := by decide +kernel
def B_4_4 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_4
set_option maxRecDepth 500000 in
lemma B_4_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 4 xs.toFinset) B_4_4 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_3_ok C_4_4
def U_4_5 : List Nat := ([1,2]++r 4 33)
def P_4_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_4 r_4 S_4 ps_4 U_4_5
def N_4_5 : List NodeSpec := [a5 [18] [4,5] [0,2],([35,0,1,2,3,9],[1],[0]),([16,0,1,3,4,9],[6],[]),e5 [49] [],([16,0,1,3,17,4],[7],[]),([10,0,1,3,21,4],[1],[8]),e5 [16] [],([16,0,1,3,4],[],[]),([51,1,2,3,4,50],[8],[2,4,6]),([10,0,1,3,4,22],[4],[0,4,8,9]),([35,0,1,2,17,9],[1,2],[]),([10,0,1,3,7,9],[2,9],[]),a5 [38] [1,2] [0,8],([52,47,1,2,3,4],[10],[6]),e5 [53] [],a5 [54] [4,11] [0,2],e5 [56] [12],([0,5,3,6,4,7],[],[0]),u5 [29] [2],([0,1,21,7,9],[1,2,9,13,14],[0,1,4,5,8,9,10,11]),([57,1,2,3,4,9],[15],[]),([31,1,13,3,17,4],[5],[]),e5 [10] [],([10,11,0,1,3,4],[16],[0]),e5 [59] [4],e5 [60] [17],([0,1,3,21,4,34],[1],[0]),([0,1,2,3,61,9],[1,18,19,20],[]),([0,1,28,3,21,4],[1,21,22,23],[]),e5 [62] [],([0,1,13,3,7,9],[8],[1,4]),e5 [63] [24],([0,1,2,17,37,9],[],[0,3,6,8]),e5 [65] [],([35,1,2,3,17,32],[2,19],[]),([0,1,13,3,4,22],[5,23],[]),([0,1,3,67,4,7],[2,9],[]),u5 [26] [9,25],([68,1,2,3,32,9],[2,26,27],[]),([31,0,1,3,14,4],[4,8,28],[]),e5 [69] [],([31,0,1,2,4,9],[2,29],[0]),([0,1,2,3,70,9],[1],[2,6]),([0,1,2,3,71,9],[1,19],[]),([16,0,1,3,4,18],[5],[0]),a5 [42] [5] [0,2,6],([35,1,40,2,3,4],[20],[]),e5 [72] [],([31,0,1,5,3,4],[30],[]),([35,0,1,2,3,32],[2],[0]),([35,0,1,2,3,18],[4],[0]),e5 [73] [],([31,1,2,3,4,32],[],[0]),([68,1,2,3,4,18],(r 31 5),[6]),([0,1,2,17,32,9],[1,19],[]),([31,0,1,3,21,4],[1,36],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_5 : checkNodesBT W_4 g_4 F_4 P_4_5 A_4 B_4_4 5 N_4_5 = true := by decide +kernel
def B_4_5 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_5
set_option maxRecDepth 500000 in
lemma B_4_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 5 xs.toFinset) B_4_5 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_4_ok C_4_5
def U_4_6 : List Nat := (r 1 5++[8,9,13,14,16,19,20,21,23,26,27,29,30]++r 37 37)
def P_4_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_4 r_4 S_4 ps_4 U_4_6
def N_4_6 : List NodeSpec := [a5 [10,9] [1,2,9,37] [0,1,8],a5 [68,9] [1,2,19,38,39,40] [0,1,6,10],a5 [35] ([2,9,20]++r 41 4) [0,2,4,8],a5 [17,18] [42,45,46,47] [0,1,2,6],a5 [17,37] [42,46,48,49] [0,2,3,6,7,8],a5 [41] [2,5,50,51] [0,1,2,3,6,7],([0,1,2,3,32,9],[2,19,26,27,52],[0,1,2,3,6,10]),a5 [24,9] [1,2,19,20,38,53] [0,1,2,6,8],a5 [17,32] [2,19,52] [0,1],a5 [25] [2,8,20,53,54] [0,1],([0,1,13,3,21,4],[1,8,21,23,55,56],[0,1,5,8,10]),a5 [28] [1,2,3,8,50,57,58] [0,1,2,3,6,7],a5 [40,21] ([50,51]++r 58 5) [0,8,10],([74,1,2,3,17,4],[1,8,19,42,46,47,50,63],[7]),e5 [75] [8,50,64],a5 [31] [1,2,5,8,29,30,65] [0,1,4],a5 [9,18] [19,38,39,66] [0,1,2,6],u5 [31,17] [1,47,65,67],u5 [35,17] [2,19,41,42],a5 [40,9] [1,2,19,20,38,50,51] [0,1,2,3,6,7,8],([0,1,3,21,4,7],[9,13,14],[0,1,4,5,8,9,10,11]),a5 [10] [1,2,5,16,30,37,68,69] [0,4,8],a5 [52,9] [19,70] [0,1],a5 [18] [4,5,42,45,71,72] [0,1,2,4,6,8,10],a5 [17,41] [46,50,73] [2,6]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_6 : checkNodesBT W_4 g_4 F_4 P_4_6 A_4 B_4_5 6 N_4_6 = true := by decide +kernel
def B_4_6 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_6
set_option maxRecDepth 500000 in
lemma B_4_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 6 xs.toFinset) B_4_6 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_5_ok C_4_6
def U_4_7 : List Nat := [1,2,4,5,8,9,19,20,38,39,42,46,47,50,51,53,58,62,74,75,76]
def P_4_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_4 r_4 S_4 ps_4 U_4_7
def N_4_7 : List NodeSpec := [u5 [74] [1,2,4,5,8,9,19,20,50],a5 [17] [1,8,19,42,46,47,50] [0,1,2,6,10],a5 [40] [1,2,4,8,50,51,58,62,74] [0,1,2,3,6,7],a5 [9] [1,2,9,19,20,38,39,75] [0,1,2,4,5,6,8,9],a5 [24] [1,2,4,5,8,9,19,20,53,76] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_7 : checkNodesBT W_4 g_4 F_4 P_4_7 A_4 B_4_6 7 N_4_7 = true := by decide +kernel
def B_4_7 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_7
set_option maxRecDepth 500000 in
lemma B_4_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 7 xs.toFinset) B_4_7 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_6_ok C_4_7
def U_4_8 : List Nat := [1,2,4,5,30]
def P_4_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_4 r_4 S_4 ps_4 U_4_8
def N_4_8 : List NodeSpec := [a5 [] [1,2,4,5,30] [0,1,2,4,5,6,8,9]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_8 : checkNodesBT W_4 g_4 F_4 P_4_8 A_4 B_4_7 8 N_4_8 = true := by decide +kernel
def B_4_8 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_8
set_option maxRecDepth 500000 in
lemma B_4_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 8 xs.toFinset) B_4_8 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_7_ok C_4_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_4_ok : forestRootCheck r_4 g_4 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_4_in : bucketContainsBT B_4_8 r_4 = true := by decide +kernel
lemma low_4 : Lower r_4 g_4 9 := lower_of_forestBT root_4_ok B_4_8_ok root_4_in
def g_5 := (d 0xfec0fec0fec0fec0)
def r_5 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_5 : Lower r_5 g_5 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_6 := (d 0xffe8ffe8ffe8ffe8)
def r_6 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_6 : Lower r_6 g_6 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_7 := (d 0xf880f880f880f880)
def r_7 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_7 : Lower r_7 g_7 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_8 := (d 0xfffef880fffef880)
def r_8 : List Nat := varsOf 31
def p_8 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,17,17,18,18,19,20,20,21,22,24,24,25,26]
def q_8 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,1,16,2,3,16,4,5,6,16,8,9,10]
def F_8 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_8 : goodPairs g_8 p_8 q_8 := goodPairs_of (by decide +kernel)
def W_8 : BT Decor := buildWiresBT 7 (mkBase p_8 q_8 r_8) [(1,0,2),(3,3,5),(1,1,3),(3,2,7),(0,0,1),(1,2,3),(2,10,4),(1,2,4),(3,3,12),(1,10,4),(3,1,14),(3,0,14),(0,10,4),(3,17,14),(0,1,10),(1,1,10),(3,19,20),(0,0,14),(0,1,4),(1,1,4),(3,23,24),(2,0,3),(1,26,2),(1,3,4),(3,2,28),(1,9,2),(1,30,4),(3,3,31),(3,2,4),(3,33,28),(3,10,4),(1,35,3),(1,26,4),(0,0,4),(1,38,3),(1,2,39),(2,0,2),(1,41,3),(1,41,4),(3,3,43),(2,27,4),(1,27,4),(1,0,4),(3,3,47),(1,48,2),(0,5,7),(1,38,2),(3,3,51),(2,1,2),(3,53,28),(3,23,0),(3,9,12),(2,0,10),(3,0,10),(2,30,4),(1,9,3),(1,30,3),(1,9,4),(3,3,62),(3,2,47),(3,0,4),(3,65,10),(2,1,3),(1,67,2),(0,0,10),(1,0,10),(3,23,10),(3,1,47),(3,9,10),(3,10,47),(2,30,3),(2,0,4),(3,1,4),(1,77,3),(0,10,47),(1,77,2),(1,80,3),(2,80,3),(2,0,17),(1,58,1),(1,1,17),(2,1,10),(3,86,0),(1,35,2),(3,3,4),(0,0,12),(2,0,28),(1,1,2),(1,0,1),(3,1,10)]
lemma W_8_ok : btAll (fun x => faithful p_8 q_8 x ∧ x.1 < 2^256) W_8 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_8 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_8 : BT (List (Nat × Nat)) := btOfList 2 al_8
set_option maxHeartbeats 0 in
lemma A_8_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_8 = g_8) A_8 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_8_0 : Slice r_8 g_8 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_1 : Slice r_8 g_8 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_2 : Slice r_8 g_8 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_3 : Slice r_8 g_8 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_4 : Slice r_8 g_8 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_5 : Slice r_8 g_8 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_6 : Slice r_8 g_8 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_7 : Slice r_8 g_8 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_7
set_option maxHeartbeats 0 in
lemma sl_8_8 : Slice r_8 g_8 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_9 : Slice r_8 g_8 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_10 : Slice r_8 g_8 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
def S_8 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,7),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 16 0,5),some (subcubeFast 3 0,4),some (subcubeFast 16 1,4),some (subcubeFast 16 2,4)]
lemma S_8_ok : btAll (fun o => ∀ p, o = some p → Slice r_8 g_8 p.1 p.2) S_8 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_8_0) (forall_cons (fun _ h => by cases h; exact sl_8_1) (forall_cons (fun _ h => by cases h; exact sl_8_2) (forall_cons (fun _ h => by cases h; exact sl_8_3) (forall_cons (fun _ h => by cases h; exact sl_8_4) (forall_cons (fun _ h => by cases h; exact sl_8_5) (forall_cons (fun _ h => by cases h; exact sl_8_6) (forall_cons (fun _ h => by cases h; exact sl_8_7) (forall_cons (fun _ h => by cases h; exact sl_8_8) (forall_cons (fun _ h => by cases h; exact sl_8_9) (forall_cons (fun _ h => by cases h; exact sl_8_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_8 : BT (Option PoolSpec) := btOfList 7 [q 1 [16424,16425,57415],q 1 [40964,40965,81999],q 1 [16388,16389,98399],q 1 [],q 1 [49165,57344],q 2 [16393,57344],q 2 [],q 7 [],q 3 [],q 4 [],q 5 [],q 6 [],q 1 [16425,57351],q 1 [16425,57344],q 0 [],q 4 [12441],q 1 [16384,12441],q 1 [16426,16427],q 1 [16385,192527],q 2 [16384,8345],q 1 [16388,95],q 0 [12297,40963],q 0 [12297,40962],q 1 [40962,40963],q 8 [],q 9 [],q 10 [],q 2 [16388,16389,98399],q 0 [12294,8461],q 1 [40960,40961],q 1 [16388,41055],q 1 [16385,192519],q 0 [12297,40999],q 1 [16385,192555],q 1 [16386,16387],q 1 [16385,192552],q 1 [16384,12493],q 1 [16424,69634],q 0 [16421,16393],q 1 [40963,4329],q 4 [16397,16393],q 6 [16397,16393],q 2 [16393],q 1 [16424,69637],q 1 [40966,347],q 1 [16384,16385],q 1 [16424,16425],q 2 [8549],q 1 [49167],q 1 [16397],q 1 [16426],q 2 [16426],q 1 [16427],q 1 [16425],q 2 [16425],q 1 [16424],q 4 [16397],q 6 [16397],q 2 [16489],q 1 [12310],q 2 [8193],q 1 [12293],q 0 [8193],q 0 [12293],q 0 [12297],q 1 [16384],q 1 [4096],q 1 [16391],q 0 [16385,192519],q 2 [16385,192519],q 5 [8193],q 0 [12290],q 0 [16393],q 0 [8197],q 3 [8197],q 1 [4],q 0 [16421],q 1 [40961],q 1 [49165],q 1 [4097],q 0 [16385],q 2 [16385],q 0 [16384,12441],q 1 [16399],q 0 [12290,8297],q 1 [12290],q 2 [8297],q 2 [16388,95],q 0 [16384,8345],q 1 [16385],q 1 [16386],q 2 [16384,16385],q 1 [40962],q 2 [16386,16387],q 1 [40960],q 1 [40967],q 0 [16391],q 2 [16391],q 2 [16386],q 0 [16384],q 2 [16384],q 2 [4097],q 2 [4096]]
def B_8_2 : BT (List (List Nat)) := BT.empty
lemma B_8_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 2 xs.toFinset) B_8_2 := .empty
def U_8_3 : List Nat := []
def P_8_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_3
def N_8_3 : List NodeSpec := [([6,8,9,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_3 : checkNodesBT W_8 g_8 F_8 P_8_3 A_8 B_8_2 3 N_8_3 = true := by decide +kernel
def B_8_3 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_3
set_option maxRecDepth 500000 in
lemma B_8_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 3 xs.toFinset) B_8_3 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_2_ok C_8_3
def U_8_4 : List Nat := [0,1,2]
def P_8_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_4
def N_8_4 : List NodeSpec := [([11,13,0,1,2],[],[]),([15,16,2,3,4],[],[]),([18,0,1,2,3],[0],[]),([21,0,2,3,4],[1],[]),([15,22,2,3,4],[],[]),([25,0,2,3,10],[2],[]),([13,0,1,27,4],[],[]),([6,8,0,1,4],[],[0]),([13,29,0,1,4],[],[]),([6,9,2,7,4],[],[0]),([13,22,1,2,4],[],[]),([32,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_4 : checkNodesBT W_8 g_8 F_8 P_8_4 A_8 B_8_3 4 N_8_4 = true := by decide +kernel
def B_8_4 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_4
set_option maxRecDepth 500000 in
lemma B_8_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 4 xs.toFinset) B_8_4 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_3_ok C_8_4
def U_8_5 : List Nat := (r 2 45)
def P_8_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_5
def N_8_5 : List NodeSpec := [([11,0,1,2,3,12],[3],[0]),([22,1,2,3,4,12],[4,5],[0]),([0,1,2,34,3,28],[6,7],[]),([13,0,1,2,4,28],[6],[0]),([13,0,1,2,12,28],[6,7],[]),([0,1,2,36,10,4],[3,7],[]),([0,1,2,3,37,28],[6,8],[]),e5 [14] (r 8 4),([13,0,1,2,10,4],[3],[0]),([15,0,2,3,10,4],[12],[]),([22,1,2,3,10,4],[13],[]),([11,0,1,2,3,14],[14],[0,1]),([6,9,1,2,3,4],[11],[0]),([0,1,2,39,40,4],[8,15,16],[]),([0,2,30,3,7,4],[6],[]),([0,1,2,42,10,4],[3,8],[]),e5 [44] [],([11,35,0,1,2,3],[17],[0]),e5 [45] [],e5 [46] [9],([26,13,0,1,2,4],[9],[0]),([0,1,2,42,4,28],[7],[1]),e5 [49] [18],e5 [50] [],([13,0,1,10,4,12],[3,6],[]),([6,0,1,2,7,4],[9,10],[0]),([0,1,2,39,10,4],[3,8,15],[]),([52,0,1,51,3,4],[19],[]),e5 [54] [3],([13,0,1,2,4,14],[14],[0,2]),([55,1,2,3,10,4],[20],[]),e5 [56] [],u5 [31] [6,14],([9,2,5,3,7,4],[9],[0,3]),([57,58,1,2,3,4],[21,22,23],[2]),e5 [59] [],([0,1,2,60,10,4],[3],[]),e5 [61] [],e5 [63] [],([26,64,1,2,3,4],[],[]),([25,0,2,3],([2]++r 24 4),[0]),e5 [66] [],([0,2,68,3,4,24],[28],[]),([69,1,2,3,70,4],[29],[2]),e5 [71] [3,30],([72,0,2,3,10,4],[31],[]),e5 [73] [14,32],([15,0,2,3,4,14],[10],[0]),e5 [74] [33],([22,1,2,3,4,14],[9,24],[0,1]),e5 [75] [],([76,65,1,2,3,10],[34],[2]),([0,1,2,60,4,28],[7,8,10],[]),([0,1,2,78,10,4],[3,11],[]),e5 [79] [9,35],e5 [81] [8,9,11],([0,1,2,17,10,28],[6],[]),e5 [82] [],e5 [40] [8,36],([83,1,2,3,10,4],[37],[]),([6,0,1,2,10,4],[3,9],[]),([0,1,2,3,62,12],[3,8,10,25,26,38],[]),([0,1,10,4,12,28],[3,7],[]),([0,84,2,3,10,4],[39],[]),([0,1,10,12,28],[3,6,7,40,41,42],[]),e5 [52] [19],([11,0,1,2,10,28],[6,7],[]),([0,2,3,10,85,4],[43],[]),([87,1,2,3,10,4],[44],[]),e5 [11] [],([38,1,2,3,10,47],[45],[2]),([0,1,2,3,17,14],[46],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_5 : checkNodesBT W_8 g_8 F_8 P_8_5 A_8 B_8_4 5 N_8_5 = true := by decide +kernel
def B_8_5 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_5
set_option maxRecDepth 500000 in
lemma B_8_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 5 xs.toFinset) B_8_5 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_4_ok C_8_5
def U_8_6 : List Nat := ([3]++r 6 6++[16,18,19,20,24,25,26,31,34,42,45]++r 47 49)
def P_8_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_6
def N_8_6 : List NodeSpec := [e5 [88] [25,26,47],a5 [13] ([3]++r 8 4++[42,48]) [0,2],a5 [12,28] [6,7,49] [0,1],([0,1,2,3,12,28],[25,26,42,49],[0,1]),e5 [90,12] [3,7,8,9,25],a5 [11,10] [3,6,7,50] [0,1],u5 [11] ([3,6]++r 8 4++[50,51]),a5 [35,10] [7,52] [0,1],a5 [14] (r 8 4++[53,54]) [0,1,2],a5 [17,10] [6,7,55] [0,1,2],u5 [91,28] [8,25],([0,1,2,10,4,28],[6,7,49,56,57],[0,1]),a5 [37] [3,8,10,11,25,58] [0,1],u5 [6] [6,7,9,10,11,25,59,60],a5 [5,7] ([9,11]++r 60 4) [0,3],a5 [38,10] [3,6,8,9,64,65] [0,1,2],a5 [9,10] ([3,6]++r 8 4++[64,66]) [0,1],a5 [80] [6,11,25,67] [0,1],([72,0,2,3,4],[9,11,25,31,68,69],[0]),([26,1,2,5,3,4],[3,6,8,9,25,70,71],[]),a5 [9,12] [3,7,8,10,25,26,72] [0,1],([9,0,2,92,3,4],[3,11,26,73,74,75],[1,2]),a5 [26,12] [3,6,8,25] [0,1,3],a5 [62] [3,6,8,10,25,26,76] [0,1],a5 [10,70] [8,9,77] [0,1],a5 [12,14] [25,26,42,78] [0,1,2],e5 [93,10] (r 8 4++[24,64,79]),([26,1,2,3,4,47],[7,8,9,71,80,81],[0,2]),([0,1,2,39,4],[7,8,16,24,82],[0,1]),([89,0,1,2,3,12],[3,7,25,26,42,83],[1]),a5 [27] [7,8,24,84,85,86] [0,1,2],a5 [30] [6,7,8,10,66] [0,1,2],([55,1,2,3,4],[7,8,10,20,87],[0]),a5 [51] [7,8,19,24,65,88] [0,1],u5 [13,12] [3,6,7,42,48],u5 [10,47] [8,9,64,89],u5 [76,10] [8,25,90],([38,1,2,3,47],[8,9,24,45,91],[0,2]),a5 [57,10] [8,9,64,92] [0,1,2],a5 [48] ([3,6]++r 8 4++[18,25,81]) [0,1],([76,65,1,2,3],[8,9,24,34,93],[0,2]),a5 [77,10] [3,6,10,11,67] [0,1,2],u5 [69,10] [8,9,94],a5 [10,14] [7,53] [0,1,2],a5 [94,10] [10,11,64,95] [2]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_6 : checkNodesBT W_8 g_8 F_8 P_8_6 A_8 B_8_5 6 N_8_6 = true := by decide +kernel
def B_8_6 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_6
set_option maxRecDepth 500000 in
lemma B_8_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 6 xs.toFinset) B_8_6 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_5_ok C_8_6
def U_8_7 : List Nat := ([3]++r 6 6++[14,24,25,26,42,60]++r 64 4++[71,72,79,80,81,83,85,89,90]++r 96 7)
def P_8_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_7
def N_8_7 : List NodeSpec := [u5 [89] ([3]++r 6 6++[25,26,83]),a5 [12] [3,8,10,25,26,42,72] [0,1,2,3],a5 [10] ([3]++r 6 6++[64]) [0,1,2],a5 [77] [3,6,9,10,11,14,25,67,96,97] [0,1,2],u5 [76] [8,10,14,24,25,90,98],a5 [38] ([3]++r 6 5++[14,24,65,99,100]) [0,1,2],u5 [26] [3,6,7,8,10,14,24,25,71,85],a5 [5] [3,8,9,11,14,24,25,60] [0,2],a5 [47] [7,8,9,14,24,25,26,80,81,89] [0,1],u5 [93] [9,11,14,24,25,79,101],a5 [9] [3,6,7,8,10,14,25,26,66,102] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_7 : checkNodesBT W_8 g_8 F_8 P_8_7 A_8 B_8_6 7 N_8_7 = true := by decide +kernel
def B_8_7 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_7
set_option maxRecDepth 500000 in
lemma B_8_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 7 xs.toFinset) B_8_7 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_6_ok C_8_7
def U_8_8 : List Nat := [3,6,14]
def P_8_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_8 r_8 S_8 ps_8 U_8_8
def N_8_8 : List NodeSpec := [a5 [] [3,6,14] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_8 : checkNodesBT W_8 g_8 F_8 P_8_8 A_8 B_8_7 8 N_8_8 = true := by decide +kernel
def B_8_8 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_8
set_option maxRecDepth 500000 in
lemma B_8_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 8 xs.toFinset) B_8_8 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_7_ok C_8_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_8_ok : forestRootCheck r_8 g_8 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_8_in : bucketContainsBT B_8_8 r_8 = true := by decide +kernel
lemma low_8 : Lower r_8 g_8 9 := lower_of_forestBT root_8_ok B_8_8_ok root_8_in
def g_9 := (d 0xe880e880e880e880)
def r_9 : List Nat := varsOf 15
def p_9 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14]
def q_9 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6]
def F_9 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_9 : goodPairs g_9 p_9 q_9 := goodPairs_of (by decide +kernel)
def W_9 : BT Decor := buildWiresBT 4 (mkBase p_9 q_9 r_9) [(0,0,1),(0,0,2),(0,1,2),(0,6,3),(3,7,0),(0,2,3),(3,9,0),(0,4,2)]
lemma W_9_ok : btAll (fun x => faithful p_9 q_9 x ∧ x.1 < 2^256) W_9 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_9 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,2),(2,3)],[(0,1)],[(0,1),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)],[(0,1),(1,2),(2,3)],[(0,2),(1,3),(2,3)]]
def A_9 : BT (List (Nat × Nat)) := btOfList 4 al_9
set_option maxHeartbeats 0 in
lemma A_9_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_9 = g_9) A_9 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_9_0 : Slice r_9 g_9 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_1 : Slice r_9 g_9 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_2 : Slice r_9 g_9 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_3 : Slice r_9 g_9 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
def S_9 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4)]
lemma S_9_ok : btAll (fun o => ∀ p, o = some p → Slice r_9 g_9 p.1 p.2) S_9 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_9_0) (forall_cons (fun _ h => by cases h; exact sl_9_1) (forall_cons (fun _ h => by cases h; exact sl_9_2) (forall_cons (fun _ h => by cases h; exact sl_9_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_9 : BT (Option PoolSpec) := btOfList 2 [q 1 [],q 0 [],q 2 [],q 3 []]
def B_9_2 : BT (List (List Nat)) := BT.empty
lemma B_9_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 2 xs.toFinset) B_9_2 := .empty
def U_9_3 : List Nat := [0,1]
def P_9_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_9 r_9 S_9 ps_9 U_9_3
def N_9_3 : List NodeSpec := [([4,5,6,3],[0,1],[]),([8,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_3 : checkNodesBT W_9 g_9 F_9 P_9_3 A_9 B_9_2 3 N_9_3 = true := by decide +kernel
def B_9_3 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_3
set_option maxRecDepth 500000 in
lemma B_9_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 3 xs.toFinset) B_9_3 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_2_ok C_9_3
def U_9_4 : List Nat := [0,2,3]
def P_9_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_9 r_9 S_9 ps_9 U_9_4
def N_9_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([10,0,1,2,3],[],[]),([11,0,1,2,3],[3],[9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_4 : checkNodesBT W_9 g_9 F_9 P_9_4 A_9 B_9_3 4 N_9_4 = true := by decide +kernel
def B_9_4 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_4
set_option maxRecDepth 500000 in
lemma B_9_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 4 xs.toFinset) B_9_4 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_3_ok C_9_4
def U_9_5 : List Nat := (r 0 4)
def P_9_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_9 r_9 S_9 ps_9 U_9_5
def N_9_5 : List NodeSpec := [([4,0,1,2,3],(r 0 4),[0,1,4,5,8,10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_5 : checkNodesBT W_9 g_9 F_9 P_9_5 A_9 B_9_4 5 N_9_5 = true := by decide +kernel
def B_9_5 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_5
set_option maxRecDepth 500000 in
lemma B_9_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 5 xs.toFinset) B_9_5 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_4_ok C_9_5
def U_9_6 : List Nat := (r 0 4)
def P_9_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_9 r_9 S_9 ps_9 U_9_6
def N_9_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,3,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_6 : checkNodesBT W_9 g_9 F_9 P_9_6 A_9 B_9_5 6 N_9_6 = true := by decide +kernel
def B_9_6 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_6
set_option maxRecDepth 500000 in
lemma B_9_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 6 xs.toFinset) B_9_6 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_5_ok C_9_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_ok : forestRootCheck r_9 g_9 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_in : bucketContainsBT B_9_6 r_9 = true := by decide +kernel
lemma low_9 : Lower r_9 g_9 7 := lower_of_forestBT root_9_ok B_9_6_ok root_9_in
def g_10 := (d 0xfc80fc80fc80fc80)
def r_10 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_10 : Lower r_10 g_10 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_11 := (d 0xfff8e880fff8e880)
def r_11 : List Nat := varsOf 31
def p_11 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,19,19,19,20,20,21,21,22,22,24,24,25,25,26,26,28]
def q_11 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,18,17,3,16,4,17,5,18,6,16,8,17,9,18,10,12]
def F_11 : Nat := fullMask 28
set_option maxHeartbeats 0 in
lemma gp_11 : goodPairs g_11 p_11 q_11 := goodPairs_of (by decide +kernel)
def W_11 : BT Decor := buildWiresBT 8 (mkBase p_11 q_11 r_11) [(1,2,3),(0,0,1),(1,6,4),(0,5,7),(0,2,3),(1,9,4),(0,6,2),(1,11,4),(0,3,12),(1,3,12),(3,13,14),(1,6,9),(2,16,4),(0,0,5),(2,0,4),(0,0,3),(0,1,2),(1,20,21),(2,22,4),(1,21,4),(1,20,24),(0,0,2),(1,26,4),(0,1,3),(1,28,4),(1,6,2),(1,30,4),(3,6,31),(0,6,3),(1,33,4),(0,2,34),(1,2,34),(3,3,36),(3,6,10),(1,9,7),(1,3,4),(1,2,4),(0,0,41),(1,20,4),(1,37,33),(0,1,41),(0,3,24),(1,3,24),(3,46,47),(1,28,2),(1,49,4),(0,0,50),(0,2,29),(0,3,41),(0,3,7),(1,54,2),(1,3,7),(0,6,5),(1,57,4),(2,6,4),(1,59,9),(3,54,56),(2,2,34),(3,2,34),(0,2,7),(0,3,31),(3,45,3),(2,5,4),(2,2,7),(3,2,7),(0,2,56),(3,54,2),(1,5,4),(1,30,3),(3,6,73),(2,2,3),(1,75,4),(2,5,7),(3,3,7),(3,6,3),(2,30,4),(3,6,2),(1,6,3),(3,28,41),(2,2,4),(3,79,41),(3,33,41),(3,79,40),(3,28,2),(1,88,4),(3,3,31),(0,0,10),(2,1,4),(3,92,0),(3,3,27),(0,1,5),(2,73,4),(1,75,7),(3,21,3),(3,59,5),(2,0,46),(1,79,2),(1,59,75),(1,74,4),(1,37,6),(1,79,4),(3,3,30),(3,79,5),(0,2,43),(2,3,2),(3,109,7),(1,81,4),(1,75,6),(2,112,4),(0,6,40),(3,114,2),(2,3,4),(1,116,2),(3,3,12),(2,0,29),(3,6,72),(1,64,3),(3,26,3),(3,6,117),(3,28,0),(1,26,3),(3,9,7),(1,20,2),(2,127,4),(3,122,40),(3,28,27),(3,20,0),(1,131,4),(1,2,43),(2,2,29),(3,2,29),(1,19,2),(3,28,136),(0,28,41),(3,138,0),(0,0,40),(0,2,40),(3,2,14),(1,142,26),(2,0,10),(2,9,4),(3,145,5),(3,95,0),(3,75,41),(2,0,53),(0,1,40),(3,150,0),(3,84,3),(3,109,40),(3,150,2),(1,84,6),(1,92,3),(1,122,4),(2,1,2),(3,158,0),(1,18,4),(3,33,2),(3,19,3),(0,0,24),(0,26,40),(1,116,26),(1,158,4),(2,1,3),(3,167,2),(1,168,4),(1,125,4),(3,167,0),(1,11,3),(0,26,3),(1,173,4),(0,6,41),(0,21,3),(3,176,0),(0,0,72),(1,167,4),(1,75,20),(3,142,0),(1,92,2),(3,158,40),(3,116,2),(3,116,0),(2,75,4),(3,109,0),(2,26,3),(2,26,4),(2,6,3),(3,92,2),(2,0,9),(2,131,2),(1,131,2),(2,131,4)]
lemma W_11_ok : btAll (fun x => faithful p_11 q_11 x ∧ x.1 < 2^256) W_11 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_11 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_11 : BT (List (Nat × Nat)) := btOfList 2 al_11
set_option maxHeartbeats 0 in
lemma A_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_11 = g_11) A_11 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_11_0 : Slice r_11 g_11 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_1 : Slice r_11 g_11 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_2 : Slice r_11 g_11 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_9
set_option maxHeartbeats 0 in
lemma sl_11_3 : Slice r_11 g_11 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_4 : Slice r_11 g_11 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xff888800ff888800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_5 : Slice r_11 g_11 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffffee88ffffee88) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_6 : Slice r_11 g_11 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f88080f8f88080) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_7 : Slice r_11 g_11 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_8 : Slice r_11 g_11 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_9 : Slice r_11 g_11 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_11_10 : Slice r_11 g_11 (subcubeFast 16 4) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_11 : Slice r_11 g_11 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_12 : Slice r_11 g_11 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_13 : Slice r_11 g_11 (subcubeFast 4 2) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_14 : Slice r_11 g_11 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_15 : Slice r_11 g_11 (subcubeFast 8 1) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_16 : Slice r_11 g_11 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_17 : Slice r_11 g_11 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_18 : Slice r_11 g_11 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_19 : Slice r_11 g_11 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_11 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 1,7),some (subcubeFast 0 2,7),some (subcubeFast 16 0,7),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (subcubeFast 1 0,5),some (subcubeFast 16 8,4),some (subcubeFast 16 4,4),some (subcubeFast 16 2,4),some (subcubeFast 8 2,4),some (subcubeFast 4 2,4),some (subcubeFast 16 1,4),some (subcubeFast 8 1,4),some (subcubeFast 4 1,4),some (subcubeFast 2 1,4),some (subcubeFast 1 2,4),some (identDom 2 3,6)]
lemma S_11_ok : btAll (fun o => ∀ p, o = some p → Slice r_11 g_11 p.1 p.2) S_11 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_11_0) (forall_cons (fun _ h => by cases h; exact sl_11_1) (forall_cons (fun _ h => by cases h; exact sl_11_2) (forall_cons (fun _ h => by cases h; exact sl_11_3) (forall_cons (fun _ h => by cases h; exact sl_11_4) (forall_cons (fun _ h => by cases h; exact sl_11_5) (forall_cons (fun _ h => by cases h; exact sl_11_6) (forall_cons (fun _ h => by cases h; exact sl_11_7) (forall_cons (fun _ h => by cases h; exact sl_11_8) (forall_cons (fun _ h => by cases h; exact sl_11_9) (forall_cons (fun _ h => by cases h; exact sl_11_10) (forall_cons (fun _ h => by cases h; exact sl_11_11) (forall_cons (fun _ h => by cases h; exact sl_11_12) (forall_cons (fun _ h => by cases h; exact sl_11_13) (forall_cons (fun _ h => by cases h; exact sl_11_14) (forall_cons (fun _ h => by cases h; exact sl_11_15) (forall_cons (fun _ h => by cases h; exact sl_11_16) (forall_cons (fun _ h => by cases h; exact sl_11_17) (forall_cons (fun _ h => by cases h; exact sl_11_18) (forall_cons (fun _ h => by cases h; exact sl_11_19) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_11 : BT (Option PoolSpec) := btOfList 9 [q 1 [12296,36889,12297],q 1 [],q 0 [],q 4 [4],q 6 [4],q 19 [],q 19 [4096,20504,16613],q 5 [],q 7 [],q 4 [],q 19 [4096,16410],q 1 [12296,36889],q 8 [],q 3 [],q 1 [16409,16393,167936],q 19 [4096,20507],q 2 [12296,12297],q 0 [12296,16421,12297],q 1 [12296,16421,12297],q 1 [12296,12297],q 19 [4096,20480],q 6 [],q 0 [12313,16409,16397],q 2 [4096,12313],q 0 [8217,12313,12297],q 12 [],q 9 [],q 5 [16386],q 2 [4096,12312,168071],q 19 [4096,16386],q 2 [],q 19 [4096,16409],q 19 [16390,371],q 1 [12297],q 0 [12297],q 0 [8216,16429],q 1 [8216,16429],q 0 [8217,12409,16678],q 2 [12288],q 2 [4096,163864,8651],q 0 [8217,16505,126991],q 15 [],q 3 [12288],q 0 [12296,36889,12297],q 0 [12297,16405,294939],q 19 [4096,20504],q 0 [12312,16517],q 1 [12312,16517],q 2 [4096,12312],q 10 [],q 0 [8196,16469],q 1 [16393],q 0 [16393],q 0 [12393,16489,16397],q 2 [8192,12393],q 2 [12292,168048,555],q 0 [16397,163848],q 2 [8192,163840,163848],q 0 [16489,16397,163848],q 2 [12296,12297,21063],q 19 [20484,383],q 0 [16393,167948],q 2 [167948,217090],q 0 [16393,167951],q 2 [167936],q 2 [167936,167948],q 0 [16393,167940],q 0 [16397,163844],q 2 [163844,603],q 2 [12298,12627],q 0 [12298,16393],q 2 [8206,164279],q 13 [],q 2 [8205,163848],q 0 [12296,12297],q 19 [20480],q 19 [16421],q 1 [16397],q 2 [163844,8795],q 0 [12296,16421],q 0 [12297,20484],q 2 [12296,8231,12589],q 0 [12296,8231,12589],q 0 [12297,16406],q 2 [12297],q 19 [16386],q 17 [],q 1 [371],q 2 [371],q 0 [12296,36889],q 0 [16394,24913],q 1 [12297,20480],q 1 [12296],q 4 [4096],q 3 [16386],q 2 [12296],q 1 [16386],q 1 [12288],q 1 [16394],q 2 [4096,12288],q 2 [167951],q 2 [4096,28687],q 0 [16409,28687],q 0 [12298,24877],q 0 [16398,8657],q 3 [8192],q 1 [8192],q 2 [4096,8192],q 1 [12657],q 0 [16390,12657],q 2 [4096],q 1 [16409],q 0 [16409],q 0 [16409,16393],q 1 [16409,16393],q 14 [],q 1 [12298],q 19 [4096],q 0 [16465],q 1 [12288,16465],q 0 [12298,8495,16421],q 1 [12298,8495,16421],q 2 [4096,12315],q 1 [16393,168051],q 2 [12292,168051],q 0 [8217,12409],q 2 [8192,12395],q 0 [12395,16873],q 2 [8198,635],q 7 [16386],q 0 [8196,86097],q 1 [12288,86097],q 16 [],q 0 [12297,16457],q 1 [12297,20480,16457],q 0 [12315,8509],q 0 [12312,8327],q 1 [12312,8327],q 2 [4096,12312,8327],q 1 [12290,16386,12367],q 2 [12290,12367],q 0 [8217,12298],q 1 [12296,16421],q 2 [4096,8216],q 2 [12292,8307],q 1 [8307,16393],q 8 [12292],q 0 [12292],q 6 [4096],q 2 [8192,163944],q 0 [8219,12297],q 1 [8219,12297],q 2 [4096,8219],q 2 [12288,167951],q 0 [8219,16393],q 0 [12297,20507],q 0 [16398,106961],q 0 [8198,17017],q 0 [8219],q 1 [8219],q 0 [8217,12313],q 0 [8216],q 1 [8216],q 0 [8217,16409],q 2 [12290,167948],q 0 [8219,16709],q 1 [8863,17057],q 7 [17057],q 2 [12294,8863],q 1 [8217,8192],q 0 [12313,16397],q 0 [12313,8205],q 8 [8196],q 0 [8196],q 2 [4,8196],q 1 [16469],q 2 [4096,8217],q 0 [8217,16506],q 0 [8217,16394],q 0 [16489],q 1 [8192,16489],q 7 [16393],q 1 [8219,16393],q 0 [8217,12410],q 1 [8219,16709],q 2 [12294,671],q 0 [8216,12333],q 1 [8216,12333],q 2 [4096,8216,12333],q 0 [16410],q 1 [16410],q 5 [16397],q 2 [8205],q 0 [8205,16397],q 0 [8217,16505],q 7 [16394],q 0 [12297,16394],q 1 [12298,24877],q 0 [12297,16405],q 2 [12292],q 0 [12298,12589],q 0 [12392,17077],q 2 [8196],q 2 [12298],q 2 [4096,167960],q 0 [12292,16497],q 0 [16393,167963],q 2 [4096,167963],q 1 [16393,167963],q 1 [16393,167936],q 2 [4096,167936],q 1 [8307,16737],q 1 [115],q 2 [12292,115],q 1 [8217,12298],q 0 [12298,16685],q 1 [12372,707],q 2 [8196,12372,707],q 2 [8192,12392],q 1 [8192,12392,17077],q 0 [12393,16885],q 0 [8273,16465],q 0 [12393,16397],q 0 [8273,16394],q 2 [12297,294912],q 2 [12288,8273],q 0 [8273,16894],q 2 [8192],q 11 [],q 0 [16489,16397],q 2 [8192,110607],q 0 [16489,110607],q 1 [17053],q 2 [12294],q 0 [12294,17053],q 0 [8207,82221],q 0 [16397,163851],q 2 [163851,571],q 2 [8192,163840],q 0 [16397],q 2 [8192,163848],q 0 [16390,8561],q 2 [8198,164475],q 0 [16398,8659],q 1 [16398,8657],q 0 [16398],q 18 [],q 1 [16393,167951],q 1 [12298,16393],q 1 [12298,16685],q 0 [8206],q 2 [8206,439],q 1 [8206,439],q 1 [12297,16406],q 1 [12297,16405],q 2 [12297,20480],q 1 [8205,16397],q 2 [12290],q 2 [12298,8495],q 0 [12298,8495],q 1 [8307],q 0 [8269],q 1 [16386,8269],q 2 [8269],q 0 [8273],q 1 [12288,8273],q 0 [12294],q 0 [12393],q 1 [8192,12393],q 0 [16394],q 0 [12394],q 0 [12298],q 0 [8217],q 1 [8217],q 0 [16490],q 0 [12314],q 0 [8198],q 1 [635],q 1 [16397,163848],q 2 [163848],q 0 [12296],q 1 [8563],q 2 [8563],q 0 [12392],q 1 [8192,12392],q 0 [8207],q 2 [8198],q 1 [12296,36866],q 2 [12296,36866],q 1 [8863],q 0 [12294,8863],q 0 [8718],q 0 [16909],q 1 [12290,16909],q 1 [12290],q 1 [12298,12589],q 2 [12298,12589],q 0 [16390],q 0 [8717],q 0 [16910],q 2 [12296,8231],q 0 [12296,8231],q 1 [12297,16394]]
def B_11_2 : BT (List (List Nat)) := BT.empty
lemma B_11_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 2 xs.toFinset) B_11_2 := .empty
def U_11_3 : List Nat := []
def P_11_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_11 r_11 S_11 ps_11 U_11_3
def N_11_3 : List NodeSpec := [([0,1,8,10],[],[]),([15,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_3 : checkNodesBT W_11 g_11 F_11 P_11_3 A_11 B_11_2 3 N_11_3 = true := by decide +kernel
def B_11_3 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_3
set_option maxRecDepth 500000 in
lemma B_11_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 3 xs.toFinset) B_11_3 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_2_ok C_11_3
def U_11_4 : List Nat := (r 0 7)
def P_11_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_11 r_11 S_11 ps_11 U_11_4
def N_11_4 : List NodeSpec := [([17,0,1,5,4],[],[]),([18,1,16,5,4],[0],[]),([19,1,16,5,4],[0],[]),([23,6,2,3,4],[],[]),([6,2,3,4,25],[1,2],[]),([6,2,3,27,29],[3,4],[]),([32,0,2,3,29],[],[]),([0,1,35,3,36],[],[1]),([37,0,1,2,34],[],[]),([38,0,1,5,4],[],[]),([0,1,5,4,39],[5],[]),([0,1,2,8,40],[],[]),([37,42,1,2,43],[],[]),([44,0,1,2,4],[],[]),([42,45,2,3,7],[],[]),([48,0,1,2,4],[],[]),([51,1,52,3,4],[],[]),([42,1,2,53,43],[],[]),([0,1,9,8,4],[5],[0]),([0,1,55,4,56],[5],[]),([0,1,9,5,58],[6],[]),([0,1,55,7,40],[],[]),([0,1,60,5,4],[],[]),([61,0,1,2,4],[],[]),([62,63,0,1,3],[],[1]),([0,1,5,7,10],[],[0]),([0,1,64,65,4],[5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_4 : checkNodesBT W_11 g_11 F_11 P_11_4 A_11 B_11_3 4 N_11_4 = true := by decide +kernel
def B_11_4 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_4
set_option maxRecDepth 500000 in
lemma B_11_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 4 xs.toFinset) B_11_4 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_3_ok C_11_4
def U_11_5 : List Nat := (r 0 6++r 7 54)
def P_11_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_11 r_11 S_11 ps_11 U_11_5
def N_11_5 : List NodeSpec := [([37,66,0,1,2,4],[],[]),([59,67,0,1,2,3],[7,8],[]),([59,0,1,9,5,4],[9,10],[0]),([19,1,2,16,3,4],[2,11],[0]),([68,69,0,1,3,4],[],[1]),([0,1,70,3,4,7],[8],[1]),([71,0,1,3,4,7],[],[]),([0,1,2,3,7,72],[12,13],[]),([37,0,1,2,3,7],[],[]),([42,1,2,3,7,41],[14],[0]),([0,1,64,3,4,31],[],[0,1]),([74,0,1,9,5,4],[5,9,15],[]),([0,1,2,3,76,7],[8],[]),e5 [77] [],([78,79,0,1,2,4],[],[]),([80,0,1,2,3,7],[2,7],[]),u5 [60] [],([6,0,1,5,4,10],[16,17,18],[0]),([6,18,1,9,5,4],[7,19,20],[0]),([0,1,2,3,27,29],[9,12,13,21],[0]),([62,0,1,2,3,34],[],[0]),([81,0,1,5,4,40],[9],[]),([0,1,2,5,7,40],[],[0]),([42,1,2,3,43,41],[],[0]),([0,1,2,82,7,40],[12,13,22,23],[]),([83,6,0,2,3,4],[2],[]),([32,0,1,3,5,4],[21],[]),([0,1,30,82,5,4],[12,13,24,25],[]),([19,67,6,1,2,3],[26,27],[]),([84,79,0,1,5,4],[9],[]),([37,33,0,1,2,4],[7],[0]),e5 [85] [13],e5 [86] [28],([19,6,1,9,5,4],[16,19,29],[0]),([87,0,1,2,4,40],[21,30],[]),([0,1,2,3,89,29],[9,13,21],[]),u5 [23] [],([90,0,1,2,4,7],[],[]),([91,0,1,5,4,10],[17],[]),e5 [74] [],([0,1,9,5,4,7],[7,9,31],[0]),([93,0,1,9,5,4],[32],[]),([94,0,1,2,27,40],[21],[]),([81,79,0,1,5,4],[9],[]),([6,18,95,2,3,4],[7,8,33,34],[]),([0,1,2,3,12,14],[9,12,13,35,36],[1]),([96,6,0,1,2,3],[37],[]),([75,0,1,3,7,41],[],[]),e5 [97] [7],([37,98,0,1,2,4],[],[]),e5 [32] [],e5 [99] [],([100,1,2,3,4,24],[],[]),([81,0,1,3,4,72],[12,13],[1]),([0,1,64,3,7,41],[],[1]),e5 [83] [],a5 [8] [1,2,7,9,13] [0,1],([81,0,1,101,3,4],[],[]),u5 [25] [1,2,8,13],e5 [102] [],e5 [103] [1,2],([81,0,1,3,7,41],[12,13,30],[]),e5 [104] [7],([0,1,2,5,4,105],[9],[]),([106,79,0,1,2,4],[],[]),([107,0,1,2,5,4],[9,21],[]),([0,1,108,3,43,41],[38],[]),([67,81,0,1,3,4],[],[]),([37,81,0,1,3,4],[],[]),e5 [110] [9],([0,1,2,3,5,58],[],[0]),u5 [39] [1,2,7,9],([0,1,2,3,111,7],[9,12,13],[]),([81,0,1,82,5,4],[9,12,13],[]),e5 [113] [],([115,0,1,3,4,40],[39],[]),([81,0,1,117,3,4],[],[]),([6,26,2,3,4,29],[3],[0,1]),([118,0,1,2,3,12],[],[1]),([90,6,0,1,2,4],[40],[]),([119,6,2,3,4,29],[41],[]),([6,22,2,3,4],[1,2,42],[0]),([32,20,1,2,3,4],[8],[2]),([37,6,20,1,2,4],[8],[]),([19,112,1,2,3,4],[],[]),([0,1,16,5,4],[0,5,43],[0,2]),u5 [17] [],([6,0,1,16,5,4],[0,9,43],[]),e5 [120] [2,44],([37,20,42,1,2,4],[2,7],[0]),([57,0,1,9,5,4],[5,9,16,45],[0]),([0,1,2,121,4,7],[9],[1]),([74,0,1,2,4,40],[30],[]),([0,1,2,3,7,10],[9,12,13,21],[0]),([94,122,0,1,2,4],[],[]),([84,74,0,1,3,4],[],[]),([112,0,1,3,4,41],[],[]),([0,1,35,2,3,34],[12,13,21,46,47,48],[0]),([75,32,0,1,3,4],[],[]),([6,0,2,3,24,40],[3,4,49,50],[1]),([6,42,45,2,3,4],[7,51,52],[0]),e5 [123] [],([37,124,0,1,2,4],[],[]),([0,1,2,125,27,40],[9,12,53,54],[]),e5 [126] [],([51,1,2,3,4,29],[7],[0]),u5 [38] [],([128,0,1,2,3,43],[2,7],[]),([129,0,1,2,4,40],[21,30],[]),([78,0,1,2,7,40],[21],[]),([88,0,1,3,29,41],[13,21,30],[]),e5 [130] [],([0,1,2,3,132,24],[8],[]),([37,0,1,2,43,41],[21],[0]),([0,1,108,3,4,133],[],[2,3]),([134,135,0,1,3,4],[],[1]),e5 [137] [],([139,1,2,3,4,41],[55],[]),([26,140,1,141,3,4],[8,56,57],[1]),([26,0,143,1,3,4],[7],[]),([67,93,0,1,2,3],[],[]),([144,0,1,5,4,10],[41],[]),([0,1,141,3,27,40],[58],[1]),([0,1,146,4],[25,41,59],[]),([84,0,1,2,3,34],[7,13],[]),([147,0,1,9,5,4],[60],[]),([0,1,2,3,12,40],[9,12,13,21,35,36],[1]),([42,0,1,3,148,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_5 : checkNodesBT W_11 g_11 F_11 P_11_5 A_11 B_11_4 5 N_11_5 = true := by decide +kernel
def B_11_5 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_5
set_option maxRecDepth 500000 in
lemma B_11_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 5 xs.toFinset) B_11_5 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_4_ok C_11_5
def U_11_6 : List Nat := (r 1 5++r 7 7++r 16 4++[21,23,25,26,27]++r 29 5++[35,36,38,41,42]++r 48 5++[54,56]++r 61 182)
def P_11_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_11 r_11 S_11 ps_11 U_11_6
def N_11_6 : List NodeSpec := [e5 [149,41] [2,8,12,61,62],a5 [37,42] [8,12,21,63] [0,2],a5 [42,53] [7,8,12,21,26,61,64,65] [1],u5 [42,45] [1,12,13,51,66],e5 [151,40] [1,2,12,67,68],([75,0,1,152,4],[9,21,25,69],[0]),([75,42,0,1,3,4,41],[70],[0]),([0,1,2,153,4,40],[8,21,71],[1,3]),([0,1,141,5,4],[8,72,73],[]),([18,0,1,9,5,4],[7,16,19,26,41,74,75],[0,2]),([0,1,9,5,4,10],[9,16,17,18,25,26,41,76],[]),a5 [154,40] [8,9,77,78] [1],u5 [144,10] [12,41],u5 [91,10] [12,79],u5 [147,5] [1,2,12,80],([0,1,9,5,4],[5,7,25,26,81,82],[]),([19,67,0,1,2,3],[2,7,8,26,27,83,84],[0,2]),([19,0,1,9,5,4],[9,16,19,26,41,85],[0,2]),e5 [75,93] [9,12,32,86,87],u5 [93,5] [7,12,86,88],u5 [6,16] [9,11,89],e5 [6,155] [1,2,9,90],([6,18,1,2,3,5,4],[2,7,8,33,91],[0]),([19,6,1,9,2,3,4],(r 92 5),[0]),([84,6,20,1,2,3,4],[26,42,93,97,98,99],[]),u5 [59,9] [9,13],a5 [37,6] [1,2,7,8,12,13,63,100] [0,2],u5 [78,6] [8,12,13,101,102],e5 [6,112] [1,2,9,103],u5 [6,117] [1,7,12,13,21,26,104],([6,26,1,2,3,4,40],[25,49,77,93,105,106,107],[1,2,3]),a5 [26,156] [8,9,13,25,108,109] [3],a5 [78,7] [8,13,21,110] [0,1],a5 [81,82] [8,9,12,13,25] [0,1],u5 [68,7] [7,9],a5 [7,31] [7,9,111,112] [0,1],([0,1,2,3,7,41],[9,12,13,110,113,114],[0,1,2]),u5 [9,7] [7,8,9,21,110],([19,75,6,1,2,3,4],[12,29,49,94,96,115,116],[0]),([6,0,1,9,5,4],[7,9,16,19,25,74,117],[0,2]),a5 [108,43] [7,9,12,21,38,118,119] [0,3],e5 [10] [9,12,13,26,120,121],a5 [84,79] [9,21,49,122] [0,1],u5 [83] [2,7,12,13,123,124],u5 [6,73] [1,110,125],a5 [26,157] [7,8,9,12,126,127] [3],e5 [159,40] [7,8,12,72,86,128],([19,6,1,2,3,5,4],[12,27,33,84,94,96,115,129],[0]),u5 [22] [25,30,130,131,132],e5 [160] [7,8,12,13,133,134],u5 [6,101] [1,7,12,13,135],([161,0,1,3,4],[9,21,136,137,138],[]),([145,0,1,5,4],[9,25,26],[0]),([131,1,2,162,4],[12,21,25,129,139,140],[]),([75,6,0,1,30,3,4],[9,12,13,141],[]),e5 [163,24] [12,50],u5 [6,10] [12,13,79,95,142],a5 [12] [8,9,21,35,36,143] [0,1],([88,0,1,3,4,41],[7,9,21,30,132,144,145],[3]),([6,26,28,2,3,4],[1,2,93,105,106,146,147,148],[0,1,3]),a5 [164,40] [21,30,77,149] [3],([81,0,1,3,5,4],[9,21,150,151],[0,1]),a5 [81,7] [7,9,110,152] [0,1],e5 [153] [1,2,8,12,13,21],([37,20,0,1,2,4],[2,7,8,63,153],[0,1,2]),([81,6,0,1,3,4,41],[7,12,13,110,152,154],[0]),a5 [74] [1,7,9,13,30,155] [0,1],e5 [26,165] [21,156],e5 [131,166] [8,49,72,157],a5 [81,40] [8,9,12,13,21,152,158,159] [0,1],([37,20,0,1,2,4,41],[7,21,52,63,153],[0]),u5 [30,82] [7,8,12,13,25,72,160],u5 [18,95] [1,12,13,33,80],a5 [11,40] [8,9,12,13,21,30,143,161,162] [0,1],a5 [30,7] [7,12,13,72,110,163] [0,1],([131,0,1,2,53,4,41],[7,8,164],[]),u5 [6,111] [1,7,12,13,152,165],u5 [74,5] [7,9,13,21],e5 [74,6] [1,2,7,155],e5 [169] [2,7,9,12,166,167,168],([0,1,5,4,10],[9,17,18,26],[0,2]),([26,1,30,3,4],[7,12,49,169],[]),([6,0,1,2,82,4,40],[12,13,21,23,170],[0]),([6,0,1,2,82,5,4],[12,13,21,72,171],[0]),([19,6,21,2,3,4],[1,3,25,41,49,94,96,115,172,173,174],[]),a5 [64,7] [7,9,12,13,110,111,112] [0,1],([6,0,2,3,4,24],[3,4,13,49,50,174,175],[0,1]),u5 [80,6] [1,2,9,12,13,176,177],([84,6,0,1,30,3,4],[9,12,13,178],[]),a5 [27,170] [8,12,21,49,179,180] [1,3],([81,0,1,3,4,41],[9,30,152,154,181,182],[0,1]),u5 [106,6] [8,12,13,72,183],u5 [84,33] [9,13,48,49],u5 [57,5] [7,9,21,84],a5 [5,7] [7,8,9,21,110] [0,1],a5 [111] [8,9,21,165,184] [1],e5 [84,171] [9,49,185],a5 [75,7] [7,8,9,12,13,21,31,110,111,112] [0,1],([0,1,2,172,4],[8,9,186,187,188],[]),u5 [59,75] [7,9,10,12,13,189,190],u5 [119,29] [12,41],([6,0,1,2,5,4,40],[8,72,110,191,192,193],[0,1]),a5 [16] [11,13,25,30,72,89,93,148] [0,2],u5 [6,31] [1,25,194],([84,6,0,1,3,5,4],[9,25,49,195,196],[0]),a5 [112] [1,7,9,13,30,72,93,103,197] [0,2],a5 [6,72] [1,7,8,12,13,84,198] [0,1],a5 [88,29] [7,9,144,199] [0,3],u5 [6,5] [1,7,8,9,12,13,21,25,200],([0,1,2,3,174],[9,12,21,25,201],[]),u5 [131,24] [8,12,41,50,202],([81,6,0,1,3,5,4],[7,12,13,25,150],[0]),([75,6,0,1,3,4,41],[7,9,70,203],[0]),u5 [59,5] [7,8,9,13,21,110],a5 [175,41] [9,26,30,204] [0,1],([0,1,2,3,12],[9,35,36],[0,1]),a5 [26,29] [7,9,12,199,205] [0,1,3],a5 [32] [1,8,13,21,206,207,208] [0,2],e5 [83,28] [1,7,13,123],e5 [32,6] [1,2,7,206],([6,42,1,2,3,4,41],[2,7,51,209,210],[0]),e5 [32,41] [9,13,207],e5 [89] [7,21,132,211],u5 [124,41] [7,12,13,41,212,213],([75,0,1,30,3,4],[7,21,49,72,141,214],[]),u5 [6,76] [1,9,12,13,26,49,215],e5 [84,124] [9,12,49,147,213],([177,1,2,3,4],[9,12,21,216,217],[]),e5 [174] [9,12,25,201,218,219],a5 [26,170] [7,86,106,220] [3],a5 [127,43] [7,38,132,221] [0,1],([26,0,1,2,125,4,40],[9,12,21,54,222],[0]),([84,20,0,1,127,3,4],[9,21,223],[]),([178,1,2,3,4],[7,8,12,224],[]),u5 [128,20] [9,225,226],a5 [67,6] [1,2,7,12,13,26,83] [0,1,2],a5 [94,27] [8,9,21,227] [0,3],a5 [88,40] [9,21,77,191,228] [1],([88,0,28,1,3,4,41],[7,13,21,144,145,199],[0]),([0,1,2,3,27,40],[9,12,21,49,180,229],[0,1,2]),u5 [134,29] [7,9],([26,0,1,2,3,27,40],[9,12,41,49,229],[0,3]),u5 [94,26] [8,9,230,231],a5 [26,179] [9,13,25,26,232,233,234] [2],e5 [180] [25,26,30,235],e5 [181,40] [8,9,12,21,30,41,236,237],a5 [37,26] [8,9,63,115] [2],([6,0,1,2,3,7,41],[12,13,30,72,113],[0,1]),([26,140,1,2,3,4,40],[2,8,49,238],[0,1]),e5 [83,41] [9,13,124],a5 [81,79] [7,9,21] [0,1],([26,0,1,141,3,4,40],[7,8,56,239,240],[0]),e5 [131,182] [7,8,12,41,241],e5 [183,40] [13,242],u5 [93,9] [9,12,86]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_6 : checkNodesBT W_11 g_11 F_11 P_11_6 A_11 B_11_5 6 N_11_6 = true := by decide +kernel
def B_11_6 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_6
set_option maxRecDepth 500000 in
lemma B_11_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 6 xs.toFinset) B_11_6 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_5_ok C_11_6
def U_11_7 : List Nat := ([1,2,5,7,8,9,12,13,16,19,21,25,26,27,30,33,34,38,41,49,51,52,54,56,63,64,70,72,74,77,79]++r 83 6++[91,92,93]++r 95 4++[100]++r 104 4++[110,111,112,115,116,117,128,132,142,143,144,147,152,158,159,161,168,176,179,180,189,193,196,198,199,200,202,203,209,212,213,215,218,225,227,233,239]++r 243 60)
def P_11_7 : BT (Option BoundPool) := buildPoolsSubBT 9 W_11 r_11 S_11 ps_11 U_11_7
def N_11_7 : List NodeSpec := [a5 [184] [2,12,21,26,30,72,243] [1],u5 [117] [7,12,13,21,26,104,244],e5 [185] [1,2,7,9,12,13,21,26,245,246],a5 [37,41] [7,9,21,26,30,51,52,63,247] [0,1,2,3],a5 [37] [1,2,7,8,9,12,13,30,63,100,247] [0,2],([84,0,1,2,3,41],[7,9,30,72,132],[]),e5 [42] [1,2,7,8,12,13,21,52,64,132,246],([84,75,0,1,3,4],[9,21,26,72,203],[0]),([75,0,1,3,4,41],[7,9,26,70,248],[0,1,2]),e5 [186] [1,2,8,9,12,13,72,203],u5 [76] [9,12,13,26,49,215,249],e5 [187] [1,2,7,12,13,41,132,246,250,251,252],a5 [67] [1,2,7,12,13,26,30,49,83,253] [0,2],a5 [72] [1,2,7,8,12,13,84,198,254] [0,2],([75,0,1,2,5,4],[2,5,9,26,34,72],[0]),u5 [18] [1,2,7,8,12,13,30,34,41,91,132,246,255],([0,1,2,5,4,40],[8,30,49,193,256],[0]),e5 [9,41] [7,9,26,51,52,72,95,132],e5 [9,5] [5,9,25,26,33,34,41],a5 [131,21] [8,13,25,41,132,202,246,257] [0,2],a5 [26,41] [7,9,26,41,51,52,72,115] [0,3],([0,1,9,2,5,4],[5,7,16,49,72,74],[]),a5 [26,28] [41,72,147,199,227] [0,1,3],([19,131,1,2,3,4],[2,12,21,26,49,246,257],[0]),([6,26,1,2,3,4],[2,7,12,25,72,93,105,106,107],[0,1,2]),u5 [9] [2,9,12,25,41,258,259],a5 [27] [8,9,13,21,49,179,180,227] [0,1,2,3],u5 [88] [1,2,7,9,12,21,30,132,144,260],a5 [84,20] [8,9,21,26,38,49,86,97,98,132] [0,1,2],a5 [136] [1,7,8,13,21,261,262,263] [2,3],a5 [88,28] [7,41,72,144,147,199] [0,3],e5 [127] [7,9,13,21,25,49,225,264,265],([131,20,1,2,3,4],[2,8,25,26],[]),a5 [19,167] [8,12,13,25,26,49,72,115,132,233,246,266] [2],a5 [19,5] [7,8,9,12,21,26,27,33,34,49,84,86,96,115] [0,2],a5 [26,125] [9,41,54,72,267,268] [0,1],a5 [84,6] [1,2,9,13,25,26,49,72,110,269] [0,1,2],e5 [75] [1,2,5,7,9,12,13,26,72],e5 [188] [1,8,9,13,26,270],a5 [81] [1,8,9,13,21,30,152,158,159] [0,1],a5 [75,41] [7,9,21,51,52,72,132,203] [1],a5 [75,6] [1,2,8,9,12,13,21,25,41,72,110,117,203,271] [0,2],a5 [11] [8,9,13,21,30,143,161] [0,1],a5 [30] [1,7,8,21,49,272,273] [0,2],a5 [19,21] [1,12,13,25,26,41,115,132,202,246] [0,2],e5 [189] [1,8,9,12,13,21,72,227,274],a5 [26,27] [9,41,49,72,179,180,227] [0,1,3],e5 [190] [7,8,9,13,26,275],a5 [159] [1,2,8,12,13,21,72,86,128,276,277] [0,1],a5 [141,40] [8,49,56,77,239,278,279] [0,1,2,3],a5 [7] [7,8,9,13,21,110,111,112] [0,1],a5 [81,6] [2,7,12,13,25,72,110,152,158] [0,1],a5 [6,7] [12,13,25,72,110,111,112] [0,1],([19,6,1,2,3,4],[12,25,26,30,49,72,96,110],[0,1]),a5 [6,9] [7,9,13,25,72,92,93,95,110,280] [0,2],e5 [26,5] [9,21,33,34,41,49,72],a5 [6,30] [12,13,25,72,176,272,273] [0,1],a5 [59] [7,8,9,13,21,110,189] [0,1],a5 [191] [1,8,21,30,132,281,282] [3],a5 [6,5] [7,8,9,12,13,21,25,33,34,41,72,84,110,132] [0,1,2],a5 [42,41] [7,26,51,52,64,209] [0,1,3],a5 [173] [1,9,12,13,21,25,30,218,283,284] [0,2],u5 [75,20] [2,7,8,21,25,26,97,285],u5 [124] [2,7,9,12,13,41,147,212,213],([0,1,9,5,4],[5,7,9,16,19,25,26,41,74],[0,2]),a5 [26,40] [8,9,12,21,41,49,77,86,106,227,239] [0,1,3],a5 [18,5] [7,9,26,33,34,84,91] [0,2],u5 [9,10] [9,25,26,41,49,79,142],a5 [6,41] [7,9,12,13,25,26,51,52,72,110,132] [0,1,2,3],a5 [131,158] [7,8,13,25,41,72,86,132,246,257,276,286] [0,3],e5 [192] [1,2,9,12,13,41,72,132,246,280,287,288],u5 [168] [2,9,12,25,132,168,289,290],e5 [193] [1,7,8,13,26,291],a5 [19,75] [7,9,12,26,41,49,85,86,96,115,116,271] [0,2],u5 [141] [2,7,8,12,30,72,132,279],a5 [132] [7,9,13,26,292,293] [2,3],a5 [131,41] [7,9,26,41,51,52,86,132,294] [0,3],u5 [5] [7,8,9,12,13,21,26,200,295,296],a5 [84,131] [8,9,26,49,86,98,132,269,294] [2],a5 [93] [2,7,8,9,12,13,21,87,88,297] [0,1],e5 [194] [1,13,41,49,298],a5 [19,9] [7,9,12,26,41,49,86,92,95,96,115] [0,2],e5 [195] [1,7,8,9,13,246,257,299],([75,0,1,9,3,4],[2,5,9,21,25,26,300,301],[0]),a5 [10] [9,12,13,21,26,49,79,95,142] [0,2],([84,0,1,3,5,4],[9,21,26,49,196,302],[0]),u5 [145] [1,2,9,12,13,21,25,95]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_7 : checkNodesBT W_11 g_11 F_11 P_11_7 A_11 B_11_6 7 N_11_7 = true := by decide +kernel
def B_11_7 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_7
set_option maxRecDepth 500000 in
lemma B_11_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 7 xs.toFinset) B_11_7 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_6_ok C_11_7
def U_11_8 : List Nat := [1,2,5,7,8,9,12,13,25,26,30,33,34,41,49,51,52,72,84,92,95,96,98,106,110,115,116,132,227,257,269,271,280,294]
def P_11_8 : BT (Option BoundPool) := buildPoolsSubBT 9 W_11 r_11 S_11 ps_11 U_11_8
def N_11_8 : List NodeSpec := [a5 [84] [1,2,9,30,49,98,269] [0,1,2,3],a5 [41] [7,30,51,52] [0,1,2,3],a5 [5] [7,8,26,33,34,49,84] [0,1,2,3],a5 [75] [1,2,5,8,9,26,30,72,116,132,271] [0,1,2,3],a5 [19] [1,2,12,30,96,115] [0,1,2,3],a5 [131] [1,2,8,30,41,257,294] [0,2,3],a5 [26] [1,2,9,30,72,106,227] [0,1,2,3],a5 [9] [9,25,41,72,92,95,132,280] [0,1,2],a5 [6] [1,2,13,30,110] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_8 : checkNodesBT W_11 g_11 F_11 P_11_8 A_11 B_11_7 8 N_11_8 = true := by decide +kernel
def B_11_8 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_8
set_option maxRecDepth 500000 in
lemma B_11_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 8 xs.toFinset) B_11_8 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_7_ok C_11_8
def U_11_9 : List Nat := [1,2,30]
def P_11_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_11 r_11 S_11 ps_11 U_11_9
def N_11_9 : List NodeSpec := [a5 [] [1,2,30] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_9 : checkNodesBT W_11 g_11 F_11 P_11_9 A_11 B_11_8 9 N_11_9 = true := by decide +kernel
def B_11_9 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_9
set_option maxRecDepth 500000 in
lemma B_11_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 9 xs.toFinset) B_11_9 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_8_ok C_11_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck r_11 g_11 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT B_11_9 r_11 = true := by decide +kernel
lemma low_11 : Lower r_11 g_11 10 := lower_of_forestBT root_11_ok B_11_9_ok root_11_in
def g_12 := (d 0xfffefec0fffefec0)
def r_12 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_12 : Lower r_12 g_12 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_13 := (d 0xfeece000feece000)
def r_13 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_13 : Lower r_13 g_13 8 := by
  have hc : Lower (varsOf 29) (d 0xfaa0a000faa0a000) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact lift_of_f (z := 2) (o := 0) (essPairs := [(VAR 1,12,14)]) (by decide +kernel) hc
def g_14 := (d 0xfefce800fefce800)
def r_14 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 8 := by
  have hc : Lower (varsOf 23) (d 0xfefee8e8fefee8e8) 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 8) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) hc
def g_15 := (d 0xe800e800e800e800)
def r_15 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_16 := (d 0xfec08000fec08000)
def r_16 : List Nat := varsOf 31
def p_16 : List Nat := [15,15,15,15,22,22,22,23,23,23,25,25,25,26,26,26,27,27,28,28,28,29,29,30]
def q_16 : List Nat := [14,13,11,7,20,18,6,21,19,7,24,17,9,24,18,10,19,11,24,20,12,21,13,14]
def F_16 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_16 : goodPairs g_16 p_16 q_16 := goodPairs_of (by decide +kernel)
def W_16 : BT Decor := buildWiresBT 4 (mkBase p_16 q_16 r_16) [(0,1,2),(0,5,4),(3,6,3),(0,2,4),(3,8,1),(0,1,4),(3,5,4)]
lemma W_16_ok : btAll (fun x => faithful p_16 q_16 x ∧ x.1 < 2^256) W_16 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_16 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_16 : BT (List (Nat × Nat)) := btOfList 1 al_16
set_option maxHeartbeats 0 in
lemma A_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_16 = g_16) A_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_16_0 : Slice r_16 g_16 (identDom 0 2) 7 := by
  have hc : Lower (varsOf 27) (d 0xee888800ee888800) 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_1 : Slice r_16 g_16 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) (d 0xfaa0a000faa0a000) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_2 : Slice r_16 g_16 (subcubeFast 0 8) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_3 : Slice r_16 g_16 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_4 : Slice r_16 g_16 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_5 : Slice r_16 g_16 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcc8800ffcc8800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_6 : Slice r_16 g_16 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_5
set_option maxHeartbeats 0 in
lemma sl_16_7 : Slice r_16 g_16 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfcc00000fcc00000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_8 : Slice r_16 g_16 (subcubeFast 1 16) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 16) (by decide +kernel) hc
def S_16 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 2,7),some (identDom 0 1,7),some (subcubeFast 0 8,6),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 16,5),some (subcubeFast 1 0,5),some (subcubeFast 1 16,4)]
lemma S_16_ok : btAll (fun o => ∀ p, o = some p → Slice r_16 g_16 p.1 p.2) S_16 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_16_0) (forall_cons (fun _ h => by cases h; exact sl_16_1) (forall_cons (fun _ h => by cases h; exact sl_16_2) (forall_cons (fun _ h => by cases h; exact sl_16_3) (forall_cons (fun _ h => by cases h; exact sl_16_4) (forall_cons (fun _ h => by cases h; exact sl_16_5) (forall_cons (fun _ h => by cases h; exact sl_16_6) (forall_cons (fun _ h => by cases h; exact sl_16_7) (forall_cons (fun _ h => by cases h; exact sl_16_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_16 : BT (Option PoolSpec) := btOfList 4 [q 1 [8196],q 5 [],q 6 [],q 0 [],q 7 [],q 2 [],q 1 [16388],q 8 [],q 2 [16388],q 4 [],q 0 [8196],q 2 [8196],q 1 [],q 3 []]
def B_16_3 : BT (List (List Nat)) := BT.empty
lemma B_16_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 3 xs.toFinset) B_16_3 := .empty
def U_16_4 : List Nat := []
def P_16_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_4
def N_16_4 : List NodeSpec := [([7,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_4 : checkNodesBT W_16 g_16 F_16 P_16_4 A_16 B_16_3 4 N_16_4 = true := by decide +kernel
def B_16_4 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_4
set_option maxRecDepth 500000 in
lemma B_16_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 4 xs.toFinset) B_16_4 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_3_ok C_16_4
def U_16_5 : List Nat := (r 0 6)
def P_16_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_5
def N_16_5 : List NodeSpec := [e5 [9] [],([0,5,10,2,3,4],[0,1,2],[]),e5 [11] [],u5 [6] [3,4,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_5 : checkNodesBT W_16 g_16 F_16 P_16_5 A_16 B_16_4 5 N_16_5 = true := by decide +kernel
def B_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_5
set_option maxRecDepth 500000 in
lemma B_16_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 5 xs.toFinset) B_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_4_ok C_16_5
def U_16_6 : List Nat := ([0,1,2,4]++r 6 6)
def P_16_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_6
def N_16_6 : List NodeSpec := [a5 [10] ([1,4]++r 6 4) [0,1],a5 [5] [0,1,2,4,9,10,11] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_6 : checkNodesBT W_16 g_16 F_16 P_16_6 A_16 B_16_5 6 N_16_6 = true := by decide +kernel
def B_16_6 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_6
set_option maxRecDepth 500000 in
lemma B_16_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 6 xs.toFinset) B_16_6 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_5_ok C_16_6
def U_16_7 : List Nat := (r 1 5++[9,12,13])
def P_16_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_7
def N_16_7 : List NodeSpec := [a5 [] (r 1 5++[9,12,13]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_7 : checkNodesBT W_16 g_16 F_16 P_16_7 A_16 B_16_6 7 N_16_7 = true := by decide +kernel
def B_16_7 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_7
set_option maxRecDepth 500000 in
lemma B_16_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 7 xs.toFinset) B_16_7 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_6_ok C_16_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck r_16 g_16 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,6,22)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT B_16_7 r_16 = true := by decide +kernel
lemma low_16 : Lower r_16 g_16 8 := lower_of_forestBT root_16_ok B_16_7_ok root_16_in
def g_17 := (d 0xfff88000fff88000)
def r_17 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_17 : Lower r_17 g_17 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,14,15)]) (by decide +kernel) hc
def g_18 := (d 0xfff8c000fff8c000)
def r_18 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_18 : Lower r_18 g_18 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,18,19)]) (by decide +kernel) hc
def g_19 := (d 0xfffe8000fffe8000)
def r_19 : List Nat := varsOf 31
def p_19 : List Nat := [15,15,15,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26,27,28,29,30]
def q_19 : List Nat := [14,13,11,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10,11,12,13,14]
def F_19 : Nat := fullMask 22
set_option maxHeartbeats 0 in
lemma gp_19 : goodPairs g_19 p_19 q_19 := goodPairs_of (by decide +kernel)
def W_19 : BT Decor := buildWiresBT 7 (mkBase p_19 q_19 r_19) [(0,3,4),(1,3,4),(3,5,6),(0,0,6),(0,2,4),(1,2,4),(3,9,10),(2,11,3),(0,7,0),(0,0,3),(0,14,4),(3,15,0),(1,3,0),(1,17,4),(3,3,18),(0,0,4),(1,0,4),(3,20,21),(1,5,2),(3,3,4),(0,1,21),(2,0,4),(1,1,4),(0,0,27),(0,2,27),(1,0,1),(0,30,4),(1,31,3),(2,3,4),(3,33,17),(0,2,3),(1,0,2),(3,35,36),(2,30,2),(1,38,3),(0,0,1),(1,40,4),(3,3,41),(3,2,21),(1,24,14),(0,35,4),(3,45,0),(3,2,4),(1,47,0),(2,48,3),(0,17,4),(0,1,2),(3,51,3),(3,52,0),(2,1,4),(3,54,3),(3,55,0),(1,51,4),(0,0,57),(1,2,3),(0,59,4),(3,60,0),(1,30,4),(3,3,62),(1,20,3),(1,20,2),(3,0,4),(2,1,5),(2,30,3),(1,24,0),(1,30,2),(2,40,4),(3,35,0),(1,1,2),(0,40,4),(0,40,2),(3,33,0),(2,30,4),(3,35,4),(3,59,4)]
lemma W_19_ok : btAll (fun x => faithful p_19 q_19 x ∧ x.1 < 2^256) W_19 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_19 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(0,1)],[(0,1),(2,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2)],[(0,3),(2,3)],[(0,2),(1,3)],[(0,3),(1,2),(2,3)],[(0,1),(1,2),(2,3)],[(0,1),(1,3)],[(0,2),(2,3)],[(0,3)],[(0,2),(1,3),(2,3)]]
def A_19 : BT (List (Nat × Nat)) := btOfList 5 al_19
set_option maxHeartbeats 0 in
lemma A_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_19 = g_19) A_19 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_19_0 : Slice r_19 g_19 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_1 : Slice r_19 g_19 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_2 : Slice r_19 g_19 (identDom 1 2) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_3 : Slice r_19 g_19 (identDom 0 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_4 : Slice r_19 g_19 (identDom 0 2) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_5 : Slice r_19 g_19 (identDom 0 1) 6 := by
  have hc : Lower (varsOf 29) (d 0xfffaa000fffaa000) 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
def S_19 : BT (Option (Nat × Nat)) := btOfList 3 [some (identDom 2 3,6),some (identDom 1 3,6),some (identDom 1 2,6),some (identDom 0 3,6),some (identDom 0 2,6),some (identDom 0 1,6)]
lemma S_19_ok : btAll (fun o => ∀ p, o = some p → Slice r_19 g_19 p.1 p.2) S_19 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_19_0) (forall_cons (fun _ h => by cases h; exact sl_19_1) (forall_cons (fun _ h => by cases h; exact sl_19_2) (forall_cons (fun _ h => by cases h; exact sl_19_3) (forall_cons (fun _ h => by cases h; exact sl_19_4) (forall_cons (fun _ h => by cases h; exact sl_19_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_19 : BT (Option PoolSpec) := btOfList 6 [q 5 [16504,12413],q 3 [12296,9,147599],q 5 [8314,12441],q 2 [12495,211],q 2 [16589,233472],q 5 [],q 4 [],q 3 [],q 0 [],q 3 [16399],q 1 [16399],q 0 [16399],q 1 [],q 5 [12410],q 3 [4097,12410],q 1 [4097,12410],q 3 [16399,97],q 5 [8313],q 4 [4097],q 2 [4097],q 1 [13],q 0 [13],q 4 [4096],q 3 [4096],q 5 [16546],q 5 [16545],q 4 [12296,143],q 3 [12296,143],q 0 [143],q 2 [4],q 4 [4,8197],q 5 [8197],q 5 [16386],q 2 [],q 5 [8352],q 2 [4096],q 5 [16504],q 3 [16398,135],q 0 [16623],q 5 [16385],q 4 [16385],q 3 [16385],q 5 [16384],q 4 [16384],q 3 [16384],q 4 [16386],q 3 [16386],q 3 [4097],q 1 [4097],q 1 [4096]]
def B_19_2 : BT (List (List Nat)) := BT.empty
lemma B_19_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 2 xs.toFinset) B_19_2 := .empty
def U_19_3 : List Nat := []
def P_19_3 : BT (Option BoundPool) := buildPoolsSubBT 6 W_19 r_19 S_19 ps_19 U_19_3
def N_19_3 : List NodeSpec := [([7,8,1,2],[],[]),([12,11,0,1],[],[]),([13,7,1,2],[],[]),([16,7,1,2],[],[]),([19,22,1,2],[],[]),([7,0,1,23],[],[]),([7,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_3 : checkNodesBT W_19 g_19 F_19 P_19_3 A_19 B_19_2 3 N_19_3 = true := by decide +kernel
def B_19_3 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_3
set_option maxRecDepth 500000 in
lemma B_19_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 3 xs.toFinset) B_19_3 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_2_ok C_19_3
def U_19_4 : List Nat := (r 0 5)
def P_19_4 : BT (Option BoundPool) := buildPoolsSubBT 6 W_19 r_19 S_19 ps_19 U_19_4
def N_19_4 : List NodeSpec := [([24,7,0,1,2],[],[]),([19,0,25,2,4],[],[]),([26,22,1,2,3],[],[]),([28,1,29,3,4],[],[]),([24,8,1,2,4],[],[]),([7,0,1,2,4],[],[]),([0,1,2,32,4],[0],[]),([0,1,2,34,4],[],[]),([37,0,1,3,4],[1],[]),([0,1,2,39,4],[2],[]),([7,0,1,2,6],[],[0,5,11,16,17,19]),([42,0,1,2,4],[],[]),([16,1,2,5,6],[],[0]),([19,43,0,1,4],[],[]),([20,1,2,3,41],[],[]),([0,44,1,2,4],[],[]),([46,1,2,3,4],[],[]),([49,0,1,2,4],[],[]),([0,1,2,50,6],[],[]),([53,1,2,3,4],[3],[]),([19,0,1,2,4],[],[]),([56,1,2,3,4],[],[]),([58,1,2,3,4],[4],[]),([61,1,2,3,4],[],[]),([16,1,2,3,4],[],[]),([63,0,1,2,4],[],[]),([20,1,2,64,21],[],[8]),([20,1,2,3,21],[],[8]),([26,1,2,64,4],[],[]),([0,1,65,64,4],[],[]),([7,0,1,2,5],[],[0,2,5,7,11]),([26,66,1,2,3],[],[8]),([7,0,1,2],[],[0,1,3,5,8,11]),([16,67,2,3,4],[],[]),([20,25,2,3,21],[],[8]),([16,1,3,23,4],[],[]),([19,20,1,2,21],[],[0]),([7,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_4 : checkNodesBT W_19 g_19 F_19 P_19_4 A_19 B_19_3 4 N_19_4 = true := by decide +kernel
def B_19_4 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_4
set_option maxRecDepth 500000 in
lemma B_19_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 4 xs.toFinset) B_19_4 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_3_ok C_19_4
def U_19_5 : List Nat := (r 5 40)
def P_19_5 : BT (Option BoundPool) := buildPoolsSubBT 6 W_19 r_19 S_19 ps_19 U_19_5
def N_19_5 : List NodeSpec := [([26,66,1,2,3,4],[],[8]),([26,66,0,1,2,3],[],[8]),a5 [20] [5,6,7] [0,8,13,19],([19,0,1,2,4,21],[7],[0,2]),([28,1,2,3,4,27],[],[0,1,3,5,6,8]),([24,0,1,2,4,6],(r 8 4),[16]),a5 [68] ([7,8]++r 12 4) [1],a5 [69] [5,6,16] [0,1,3],([19,0,1,2,4],[],[]),([24,14,0,1,2,4],[9],[0]),e5 [70] [17,18,19],([0,1,2,17,4,6],[7,20,21],[0]),([40,20,1,2,3,4],[5,22,23],[0]),u5 [26] [],e5 [71] [24],a5 [41] [25] [0,1,5,11,16],([20,0,1,2,3,21],[],[8]),e5 [19] [],a5 [72] [5,8,26,27,28] [8],([20,1,2,3,21],[],[0,1,2,3,4,8,13,19]),([40,0,2,73,3,4],[29,30,31],[15]),([26,1,30,2,3,4],[32],[8]),([16,1,2,5,3,4],[7],[0,2]),a5 [74] [12,33] [3,8,14,20],a5 [24] [] [16],e5 [75] [22,34,35],([26,66,1,2,3],[],[0,8]),a5 [21] [5,6,7] [0,1,3],a5 [31] [36] [0,1,3,8,14,20],a5 [76] [5,6,37] [10,15,19],e5 [77] [],([26,20,1,2,3,4],[8],[0,1,3]),([16,1,2,3,4],[],[]),e5 [78] [],e5 [79] [38],([20,0,1,2,64,4],[],[0,2,8,13,19]),([20,1,2,3,4,21],(r 39 6),[8]),a5 [62] [12,33] [0,1,3,8],e5 [16] [],([24,0,1,2,5,3],[8],[16]),([26,0,1,2,3,21],[8],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_5 : checkNodesBT W_19 g_19 F_19 P_19_5 A_19 B_19_4 5 N_19_5 = true := by decide +kernel
def B_19_5 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_5
set_option maxRecDepth 500000 in
lemma B_19_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 5 xs.toFinset) B_19_5 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_4_ok C_19_5
def U_19_6 : List Nat := (r 5 8++[18,19,22,23,32,33,35]++r 39 11)
def P_19_6 : BT (Option BoundPool) := buildPoolsSubBT 6 W_19 r_19 S_19 ps_19 U_19_6
def N_19_6 : List NodeSpec := [a5 [24] (r 7 6) [0,2,5,7,11,16],a5 [26] [5,6,7,32,45,46] [0,2,4,8,13,19],a5 [20] [5,6,7,42,43,44] [0,1,2,3,4,8,13,19],a5 [21] [5,6,7,39,40,41] [0,1,2,3,4,5,8,11,13,16,19],a5 [30] [5,12,18,19,33,47,48] [0,1,3,5,8,11,12,14,16,18],a5 [40] [5,12,22,23,33,35,49] [0,1,3,5,6,8,14,20]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_6 : checkNodesBT W_19 g_19 F_19 P_19_6 A_19 B_19_5 6 N_19_6 = true := by decide +kernel
def B_19_6 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_6
set_option maxRecDepth 500000 in
lemma B_19_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 6 xs.toFinset) B_19_6 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_5_ok C_19_6
def U_19_7 : List Nat := (r 5 4++[12,33])
def P_19_7 : BT (Option BoundPool) := buildPoolsSubBT 6 W_19 r_19 S_19 ps_19 U_19_7
def N_19_7 : List NodeSpec := [a5 [] (r 5 4++[12,33]) [0,1,2,3,4,5,7,8,9,11,14,16]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_7 : checkNodesBT W_19 g_19 F_19 P_19_7 A_19 B_19_6 7 N_19_7 = true := by decide +kernel
def B_19_7 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_7
set_option maxRecDepth 500000 in
lemma B_19_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 7 xs.toFinset) B_19_7 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_6_ok C_19_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck r_19 g_19 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT B_19_7 r_19 = true := by decide +kernel
lemma low_19 : Lower r_19 g_19 8 := lower_of_forestBT root_19_ok B_19_7_ok root_19_in
def g_20 := (d 0xfac0fac0fac0fac0)
def r_20 : List Nat := varsOf 15
def p_20 : List Nat := [6,6,7,7,9,9,11,11,12,12,13,14]
def q_20 : List Nat := [4,2,5,3,8,1,10,3,8,4,5,10]
def F_20 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_20 : goodPairs g_20 p_20 q_20 := goodPairs_of (by decide +kernel)
def W_20 : BT Decor := buildWiresBT 2 (mkBase p_20 q_20 r_20) []
lemma W_20_ok : btAll (fun x => faithful p_20 q_20 x ∧ x.1 < 2^256) W_20 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_20 : List (List (Nat × Nat)) := [[]]
def A_20 : BT (List (Nat × Nat)) := btOfList 1 al_20
set_option maxHeartbeats 0 in
lemma A_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_20 = g_20) A_20 := btAll_ofList (autos_of (by decide +kernel))
def S_20 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_20_ok : btAll (fun o => ∀ p, o = some p → Slice r_20 g_20 p.1 p.2) S_20 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_20 : BT (Option PoolSpec) := btOfList 1 []
def B_20_2 : BT (List (List Nat)) := BT.empty
lemma B_20_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 2 xs.toFinset) B_20_2 := .empty
def U_20_3 : List Nat := []
def P_20_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_20 r_20 S_20 ps_20 U_20_3
def N_20_3 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_3 : checkNodesBT W_20 g_20 F_20 P_20_3 A_20 B_20_2 3 N_20_3 = true := by decide +kernel
def B_20_3 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_3
set_option maxRecDepth 500000 in
lemma B_20_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 3 xs.toFinset) B_20_3 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_2_ok C_20_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck r_20 g_20 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT B_20_3 r_20 = true := by decide +kernel
lemma low_20 : Lower r_20 g_20 4 := lower_of_forestBT root_20_ok B_20_3_ok root_20_in
def g_21 := (d 0xffecf800ffecf800)
def r_21 : List Nat := varsOf 31
def p_21 : List Nat := [11,11,11,12,12,13,13,14,14,15,18,18,19,19,21,21,21,22,22,23,24,24,25,25,26,28]
def q_21 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,2,17,3,20,17,5,20,6,7,16,8,17,9,10,20]
def F_21 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_21 : goodPairs g_21 p_21 q_21 := goodPairs_of (by decide +kernel)
def W_21 : BT Decor := buildWiresBT 6 (mkBase p_21 q_21 r_21) [(0,3,4),(1,3,4),(3,5,6),(2,7,2),(0,7,1),(2,7,0),(1,2,3),(0,0,11),(1,2,4),(0,3,13),(1,0,5),(1,2,5),(1,13,3),(3,2,17),(1,1,5),(3,0,6),(0,7,0),(2,1,5),(0,0,6),(2,0,5),(0,1,6),(0,2,6),(2,3,4),(3,1,4),(1,28,3),(3,2,29),(1,1,2),(1,31,3),(2,32,4),(0,0,31),(2,31,4),(1,1,3),(1,36,4),(3,2,37),(3,2,3),(0,0,4),(1,40,3),(3,2,41),(3,5,4),(2,2,5),(3,1,37),(3,2,36),(3,13,3),(1,1,4),(3,2,48),(2,11,4),(2,0,4),(3,51,3),(1,43,1),(3,40,3),(1,51,3),(2,36,4),(0,0,3)]
lemma W_21_ok : btAll (fun x => faithful p_21 q_21 x ∧ x.1 < 2^256) W_21 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_21 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_21 : BT (List (Nat × Nat)) := btOfList 1 al_21
set_option maxHeartbeats 0 in
lemma A_21_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_21 = g_21) A_21 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_21_0 : Slice r_21 g_21 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_1 : Slice r_21 g_21 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xffa0f000ffa0f000) 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_2 : Slice r_21 g_21 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcc8800ffcc8800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_3 : Slice r_21 g_21 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_4 : Slice r_21 g_21 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_5 : Slice r_21 g_21 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xececc8c8ececc8c8) 6 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_6 : Slice r_21 g_21 (identDom 2 4) 6 := by
  have hc : Lower (varsOf 15) (d 0xf8e0f8e0f8e0f8e0) 6 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_7 : Slice r_21 g_21 (identDom 0 1) 5 := by
  have hc : Lower (varsOf 29) (d 0xffaafa00ffaafa00) 5 := carry_of (swaps := [(0,1),(1,4),(2,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_8 : Slice r_21 g_21 (identDom 0 4) 5 := by
  have hc : Lower (varsOf 15) (d 0xfaa8faa8faa8faa8) 5 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_5
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_9 : Slice r_21 g_21 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeeeea8a8eeeea8a8) 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_10 : Slice r_21 g_21 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) (d 0xffccf000ffccf000) 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_21 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 4 1,4),some (subcubeFast 2 1,4),some (identDom 1 3,6),some (identDom 2 4,6),some (identDom 0 1,5),some (identDom 0 4,5),some (identDom 0 3,5),some (subcubeFast 1 0,4)]
lemma S_21_ok : btAll (fun o => ∀ p, o = some p → Slice r_21 g_21 p.1 p.2) S_21 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_21_0) (forall_cons (fun _ h => by cases h; exact sl_21_1) (forall_cons (fun _ h => by cases h; exact sl_21_2) (forall_cons (fun _ h => by cases h; exact sl_21_3) (forall_cons (fun _ h => by cases h; exact sl_21_4) (forall_cons (fun _ h => by cases h; exact sl_21_5) (forall_cons (fun _ h => by cases h; exact sl_21_6) (forall_cons (fun _ h => by cases h; exact sl_21_7) (forall_cons (fun _ h => by cases h; exact sl_21_8) (forall_cons (fun _ h => by cases h; exact sl_21_9) (forall_cons (fun _ h => by cases h; exact sl_21_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_21 : BT (Option PoolSpec) := btOfList 5 [q 2 [],q 8 [],q 4 [],q 3 [],q 0 [],q 10 [],q 5 [],q 1 [],q 6 [],q 6 [16397],q 1 [126976],q 7 [],q 2 [126976],q 0 [8197],q 9 [],q 2 [45056],q 5 [16391,12401],q 5 [16398],q 5 [16397],q 6 [12299]]
def B_21_2 : BT (List (List Nat)) := BT.empty
lemma B_21_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 2 xs.toFinset) B_21_2 := .empty
def U_21_3 : List Nat := []
def P_21_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 U_21_3
def N_21_3 : List NodeSpec := [([8,7,0,1],[],[]),([9,7,0,2],[],[]),([10,7,1,2],[],[]),([12,1,14,4],[],[]),([1,15,16,6],[],[]),([7,0,1,16],[],[]),([7,18,0,1],[],[]),([0,19,16,6],[],[]),([7,20,1,2],[],[]),([21,7,1,2],[],[]),([22,7,0,2],[],[]),([7,23,1,2],[],[]),([7,1,2,15],[],[]),([7,0,1,2],[],[]),([24,7,1,2],[],[]),([0,25,26,5],[],[]),([7,0,25,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_3 : checkNodesBT W_21 g_21 F_21 P_21_3 A_21 B_21_2 3 N_21_3 = true := by decide +kernel
def B_21_3 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_3
set_option maxRecDepth 500000 in
lemma B_21_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 3 xs.toFinset) B_21_3 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_2_ok C_21_3
def U_21_4 : List Nat := []
def P_21_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 U_21_4
def N_21_4 : List NodeSpec := [([27,7,0,1,2],[],[]),([18,0,25,3,4],[],[]),([0,25,26,3,4],[],[0]),([7,0,1,2,3],[],[]),([1,3,15,16,4],[],[0]),([18,0,1,5,6],[],[0]),([18,0,1,3,4],[],[]),([0,1,14,11,4],[],[0]),([0,25,2,5,6],[],[0]),([30,0,1,3,4],[],[]),([7,0,1,2,6],[],[0,1]),([27,0,2,19,4],[],[]),([33,0,1,2,3],[],[]),([34,1,3,4,13],[],[]),([7,0,1,2],[],[0,1]),([35,28,0,2,3],[],[]),([23,25,2,3,4],[],[]),([0,1,2,14,6],[],[]),([38,0,1,3,4],[],[]),([39,34,1,3,4],[],[]),([7,0,1,2,5],[],[0,1]),([39,12,1,3,4],[],[]),([42,0,1,3,4],[],[]),([24,1,2,5,6],[],[0]),([18,20,1,3,4],[],[]),([27,43,0,1,2],[],[0]),([12,1,3,4,13],[],[0]),([1,2,5,15,6],[],[0,1]),([24,1,3,16,4],[],[]),([18,23,1,3,4],[],[]),([24,22,2,3,4],[],[]),([0,3,19,16,4],[],[0]),([22,0,3,16,4],[],[]),([0,1,5,16,6],[],[0]),([22,44,0,3,4],[],[]),([22,0,2,5,6],[],[0]),([0,1,2,5,6],[],[0]),([23,1,2,5,6],[],[0]),([18,45,0,3,4],[],[]),([20,1,2,5,6],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_4 : checkNodesBT W_21 g_21 F_21 P_21_4 A_21 B_21_3 4 N_21_4 = true := by decide +kernel
def B_21_4 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_4
set_option maxRecDepth 500000 in
lemma B_21_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 4 xs.toFinset) B_21_4 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_3_ok C_21_4
def U_21_5 : List Nat := (r 0 17)
def P_21_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 U_21_5
def N_21_5 : List NodeSpec := [([27,43,0,1,2],[],[0,1]),([18,0,1,3,4,6],[0],[0]),e5 [18] [],([20,1,2,3,4,6],[1,2,3],[0,1]),([23,1,2,3,4],[],[]),u5 [27] [],([27,0,1,2,5,4],[4],[0]),([18,0,1,3,4],[],[]),([23,1,2,3,4,6],[4],[0,1]),e5 [46] [],u5 [14] (r 4 5),u5 [35] [0],a5 [6] [0,1,4,7] [0,1],e5 [47] [],e5 [49] [],e5 [50] [],([39,0,1,31,3,4],[7],[0,1]),([27,43,0,1,2,3],[],[0]),([0,1,2,5,3,6],[9],[0]),([34,1,2,31,3,4],[4,10],[]),e5 [52] [5,6,7],e5 [53] [4,11],e5 [54] [],([0,25,2,3,4,6],[2],[0,1]),e5 [55] [],u5 [32] [4,8,11],([0,1,31,3,4,13],[7,8],[0]),([34,1,2,3,4],[10,12,13],[0,1]),([1,2,5,3,15,4],[2,3,5],[0,1]),u5 [41] [0,14],([12,1,2,3,11,4],[4,15],[0]),([12,1,2,3,4],[15],[0]),([39,0,1,3,11,4],[0],[0]),([22,0,2,5,3,4],[2,6],[0]),([27,0,1,2,36,4],[7],[]),([0,1,3,11,4,13],[8],[0]),a5 [37] [0,4,11] [0,1],e5 [56] [],a5 [29] [0,4,14,16] [0,1],([27,0,1,2,3,6],[4],[0]),([0,1,2,3,13,6],[0],[0]),([24,1,2,5,3,4],[4],[0,1]),([24,1,2,3,4],[],[]),u5 [5] ([0]++r 4 5),([0,1,2,5,6],[],[0,1]),([0,1,5,3,16,4],[0],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_5 : checkNodesBT W_21 g_21 F_21 P_21_5 A_21 B_21_4 5 N_21_5 = true := by decide +kernel
def B_21_5 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_5
set_option maxRecDepth 500000 in
lemma B_21_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 5 xs.toFinset) B_21_5 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_4_ok C_21_5
def U_21_6 : List Nat := (r 0 10++[13,14,17,18,19])
def P_21_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 U_21_6
def N_21_6 : List NodeSpec := [a5 [27] ([0,1]++r 4 4++[17]) [0,1],a5 [6] [0,4,5,7,9,18] [0,1],a5 [5] ([0]++r 4 5) [0,1],a5 [39] [3,6,7,8,19] [0,1],a5 [11] [3,7,8] [0,1],a5 [36] [0,2,6,7] [0,1],a5 [31] [3,6,7,8,13] [0,1],u5 [51] (r 1 5),a5 [57] [0,2,3,5,7,14] [1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_6 : checkNodesBT W_21 g_21 F_21 P_21_6 A_21 B_21_5 6 N_21_6 = true := by decide +kernel
def B_21_6 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_6
set_option maxRecDepth 500000 in
lemma B_21_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 6 xs.toFinset) B_21_6 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_5_ok C_21_6
def U_21_7 : List Nat := [0,2,3,4,6,7,8]
def P_21_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 U_21_7
def N_21_7 : List NodeSpec := [a5 [] [0,2,3,4,6,7,8] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_7 : checkNodesBT W_21 g_21 F_21 P_21_7 A_21 B_21_6 7 N_21_7 = true := by decide +kernel
def B_21_7 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_7
set_option maxRecDepth 500000 in
lemma B_21_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 7 xs.toFinset) B_21_7 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_6_ok C_21_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_ok : forestRootCheck r_21 g_21 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_in : bucketContainsBT B_21_7 r_21 = true := by decide +kernel
lemma low_21 : Lower r_21 g_21 8 := lower_of_forestBT root_21_ok B_21_7_ok root_21_in
def g_22 := (d 0xfffefefcfec08000)
def r_22 : List Nat := varsOf 63
def p_22 : List Nat := [15,15,15,15,22,22,22,23,23,23,25,25,25,26,26,26,27,27,28,28,28,29,29,30,34,34,35,35,36,36,37,37,38,39,41,41,41,42,42,43,44,44,45,46,49,49,49,50,50,51,52,52,53,56,56,56]
def q_22 : List Nat := [14,13,11,7,20,18,6,21,19,7,24,17,9,24,18,10,19,11,24,20,12,21,13,14,32,2,33,3,32,4,33,5,6,7,40,33,9,40,10,11,40,12,13,14,48,33,17,48,18,19,48,20,21,48,40,24]
def F_22 : Nat := fullMask 56
set_option maxHeartbeats 0 in
lemma gp_22 : goodPairs g_22 p_22 q_22 := goodPairs_of (by decide +kernel)
def W_22 : BT Decor := buildWiresBT 9 (mkBase p_22 q_22 r_22) [(1,2,5),(0,4,6),(1,4,6),(3,7,8),(0,2,5),(3,9,3),(1,10,11),(1,1,11),(3,10,6),(0,14,3),(0,15,4),(3,16,14),(3,17,6),(1,1,18),(0,3,4),(1,1,20),(3,2,21),(3,2,5),(1,23,1),(1,20,5),(0,9,3),(1,1,2),(1,27,5),(1,20,28),(3,2,29),(0,1,5),(1,31,20),(1,1,5),(1,20,33),(0,32,33),(1,2,35),(2,0,18),(3,4,33),(0,3,33),(3,16,6),(3,20,5),(3,41,6),(2,2,20),(3,43,6),(0,3,6),(1,10,20),(3,31,33),(1,47,20),(3,2,48),(0,47,3),(3,50,4),(0,14,4),(1,14,4),(3,52,53),(3,20,33),(2,14,4),(3,4,6),(1,57,20),(3,39,4),(1,57,46),(0,1,2),(0,3,5),(1,61,62),(0,63,4),(1,63,4),(3,64,65),(0,21,6),(3,56,6),(1,56,20),(3,45,4),(3,15,4),(1,61,20),(0,72,5),(1,61,5),(1,20,74),(3,73,75),(1,2,62),(0,77,4),(2,0,78),(3,1,77),(0,2,25),(1,20,6),(3,81,82),(1,2,20),(3,1,84),(3,85,25),(1,22,5),(1,23,20),(1,55,5),(3,41,89),(2,2,5),(2,1,20),(1,41,1),(3,92,93),(1,4,33),(0,3,95),(0,4,33),(1,96,97),(3,1,5),(1,99,2),(2,21,5),(3,1,75),(3,2,75),(0,1,82),(0,0,34),(3,2,33),(2,3,7),(2,3,4),(3,108,6),(3,57,28),(0,20,6),(3,111,28),(3,57,3),(1,10,113),(3,10,8),(2,1,5),(1,38,20),(3,10,82),(2,4,33),(1,119,31),(0,20,28),(3,121,28),(3,52,3),(2,0,4),(3,124,14),(3,108,14),(3,14,3),(3,127,4),(0,2,4),(1,2,4),(3,129,130),(2,131,62),(2,131,5),(3,131,5),(0,3,53),(0,131,5),(1,131,5),(0,4,5),(1,61,138),(0,3,139),(1,4,5),(0,24,3),(0,142,4),(3,143,24),(0,131,3),(2,55,2),(0,3,28),(0,4,28),(1,14,20),(2,3,148),(3,147,4),(0,0,3),(2,14,152),(0,3,8),(3,108,28),(2,72,5),(3,41,33),(0,20,74),(3,158,74),(0,0,53),(3,14,4),(3,161,3),(0,1,25),(3,72,5),(3,56,3),(3,20,6),(3,166,28),(1,103,61),(1,47,4),(3,2,169),(2,63,4),(3,63,4),(2,3,139),(2,3,5),(3,174,131),(1,15,4),(0,3,74),(0,4,74),(1,27,20),(0,24,4),(3,124,6),(3,152,6),(0,0,4),(2,14,183),(3,166,33),(0,84,5),(3,186,82),(0,2,34),(3,2,4),(2,189,5),(3,183,6),(3,92,33),(0,21,5),(1,2,193),(1,45,4),(3,2,3),(2,196,5),(3,197,4),(3,2,95),(3,190,3),(1,2,138),(3,1,201),(3,202,3),(1,1,62),(2,204,4),(3,2,204),(1,103,1),(3,81,1),(1,41,2),(3,84,5),(3,21,5),(3,99,25),(1,99,20),(3,2,213),(3,108,24),(2,93,2),(0,100,4),(3,217,3),(3,91,84),(3,108,33),(0,20,33),(2,24,4),(3,222,3),(2,3,33),(1,224,97),(1,190,45),(1,39,4),(0,0,227),(0,204,4),(1,2,221),(2,21,6),(1,55,2),(3,38,3),(3,1,6),(1,2,97),(3,183,33),(3,124,33),(3,124,3),(1,41,27),(0,130,33),(2,3,240),(3,152,33),(3,189,3),(1,2,39),(1,1,45),(0,3,141),(1,61,246),(1,41,61),(1,24,20),(3,196,4),(3,183,24),(3,4,28),(3,252,3),(3,4,5),(3,254,74),(2,242,2),(3,177,4),(3,4,74),(3,258,3),(0,3,130),(3,260,33),(3,183,3),(3,27,25),(3,236,3),(0,1,3),(1,265,5),(3,183,266),(0,236,3),(3,183,28),(3,183,74),(3,152,28),(1,242,2),(1,183,39),(2,1,25),(1,236,2),(3,124,266),(2,3,178),(2,84,5),(1,278,1),(3,152,74),(1,1,4),(3,45,281),(2,2,4),(3,283,77),(3,124,74),(3,152,24),(0,14,0),(3,61,25),(3,2,281),(1,289,5),(0,204,130),(2,236,2),(3,1,3),(3,293,6),(0,100,3),(3,295,4),(3,108,74),(2,179,5),(3,14,0),(3,254,266),(3,1,4),(3,301,6),(1,265,138),(1,196,1),(0,304,141),(2,4,5),(3,306,304),(0,293,4),(3,308,6),(3,250,33),(3,224,4),(3,196,33),(3,293,201),(3,131,3),(1,166,1),(1,129,62),(0,281,6),(0,3,317),(0,0,6),(1,189,5),(3,99,84),(1,1,138),(3,2,322),(0,3,322),(3,189,5),(1,224,31),(1,116,20),(3,301,77),(3,119,3),(3,183,204),(1,119,39),(0,196,33),(1,106,20),(1,1,246),(3,2,141),(1,335,1),(1,108,5),(3,2,337),(1,108,1),(2,339,2),(3,23,4),(1,341,1),(3,306,3),(3,174,4),(1,1,344),(3,91,3),(1,1,7),(3,23,130),(3,62,4),(1,349,1),(1,57,1),(2,339,5),(0,0,33),(3,10,1),(3,189,141),(0,189,33),(3,301,3),(1,189,1),(2,358,5),(1,358,5),(0,358,3),(2,1,4),(1,301,5),(2,130,5),(1,364,1),(3,61,141),(3,1,141),(3,283,3),(1,368,5),(2,3,138),(0,196,4),(1,371,5),(1,306,1),(2,0,5),(3,374,3),(1,1,375),(1,174,1),(2,377,2),(0,2,3),(3,379,4),(1,380,5),(1,190,1),(3,61,4),(1,383,5),(1,374,265),(1,254,1),(2,386,2),(3,62,281),(3,61,3),(1,254,2),(1,374,61),(0,0,5),(1,392,265),(1,183,62),(3,392,3),(2,20,5),(3,306,281),(1,183,61),(1,23,152),(3,10,3),(1,23,183),(3,2,363),(1,183,5),(1,362,62),(1,238,5),(3,23,3),(1,196,5),(1,1,403),(2,0,129),(0,0,2),(3,410,3),(1,411,5),(2,304,5),(1,152,5),(3,2,414),(3,27,3),(1,416,5),(1,196,4),(2,418,5),(1,293,5),(0,0,74),(3,10,4),(1,152,61),(0,0,1),(1,424,62),(1,196,392),(1,196,183),(1,374,196),(1,1,260),(3,293,141),(2,281,5),(1,124,5),(3,2,432),(1,389,5),(0,1,4),(3,293,4),(1,183,31),(3,254,3),(1,183,265),(1,152,31),(0,3,281),(3,99,130),(1,1,414),(1,1,238),(3,27,4),(3,99,4),(3,27,141),(1,396,1),(1,392,61),(3,99,3),(0,304,4),(3,293,130),(1,27,138),(1,306,27),(3,2,420),(1,254,27),(0,0,266),(1,254,61),(1,27,62),(1,301,23),(3,4,266),(1,116,152),(3,379,141),(1,306,265),(1,254,265),(2,304,4),(1,304,5),(2,373,2),(3,91,4),(3,2,403),(1,445,5),(1,371,1),(0,4,266),(1,435,62),(1,293,189),(1,436,5),(3,301,5),(1,306,61),(1,250,1),(1,197,1),(1,196,138),(1,189,62),(1,293,23),(1,306,196),(1,254,196),(1,435,5),(0,3,486),(1,116,183),(2,289,5),(1,441,5),(2,0,10),(3,306,1),(1,31,4),(1,362,5),(1,424,5),(3,196,5),(3,129,3)]
lemma W_22_ok : btAll (fun x => faithful p_22 q_22 x ∧ x.1 < 2^256) W_22 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_22 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_22 : BT (List (Nat × Nat)) := btOfList 1 al_22
set_option maxHeartbeats 0 in
lemma A_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_22 = g_22) A_22 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_22_0 : Slice r_22 g_22 (subcubeFast 0 8) 9 := by
  have hc : Lower (varsOf 55) (d 0xfffffefefefe8080) 9 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_1 : Slice r_22 g_22 (subcubeFast 0 1) 9 := by
  have hc : Lower (varsOf 62) (d 0xfffffffcffc0c000) 9 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_2 : Slice r_22 g_22 (identDom 1 2) 10 := by
  have hc : Lower (varsOf 59) (d 0xffeeeecceecc8800) 10 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_11
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_3 : Slice r_22 g_22 (identDom 0 2) 10 := by
  have hc : Lower (varsOf 59) (d 0xffeeeeeeee888800) 10 := carry_of (swaps := [(0,2),(1,3),(2,5),(3,5),(4,5)]) (by decide +kernel) low_11
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_4 : Slice r_22 g_22 (identDom 0 1) 10 := by
  have hc : Lower (varsOf 61) (d 0xfffafafafaa0a000) 10 := carry_of (swaps := [(0,2),(1,5),(2,3),(4,5)]) (by decide +kernel) low_11
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_5 : Slice r_22 g_22 (subcubeFast 0 16) 8 := by
  have hc : Lower (varsOf 47) (d 0xfffefffefec0fec0) 8 := carry_of (swaps := [(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_6 : Slice r_22 g_22 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) (d 0xffeeeeccee000000) 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_7 : Slice r_22 g_22 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffafaf0fa000000) 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_8 : Slice r_22 g_22 (subcubeFast 1 0) 8 := by
  have hc : Lower (varsOf 62) (d 0xfffcfcfcfcc00000) 8 := carry_of (swaps := [(0,5),(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_9 : Slice r_22 g_22 (subcubeFast 1 16) 7 := by
  have hc : Lower (varsOf 46) (d 0xfffcfffcfcc0fcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_10 : Slice r_22 g_22 (subcubeFast 6 0) 7 := by
  have hc : Lower (varsOf 57) (d 0xffaaaa00aa000000) 7 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 6) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_11 : Slice r_22 g_22 (subcubeFast 32 0) 8 := by
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) low_16
set_option maxHeartbeats 0 in
lemma sl_22_12 : Slice r_22 g_22 (subcubeFast 16 0) 7 := by
  have hc : Lower (varsOf 47) (d 0xfefcfefc80008000) 7 := carry_of (swaps := [(1,2),(2,3),(4,5)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_13 : Slice r_22 g_22 (subcubeFast 8 0) 7 := by
  have hc : Lower (varsOf 55) (d 0xfefefcfcc0c00000) 7 := carry_of (swaps := [(1,2),(2,3),(3,5),(4,5)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_14 : Slice r_22 g_22 (subcubeFast 16 8) 6 := by
  have hc : Lower (varsOf 39) (d 0xfefefefe80808080) 6 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_15 : Slice r_22 g_22 (subcubeFast 32 8) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 32) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_16 : Slice r_22 g_22 (subcubeFast 16 1) 6 := by
  have hc : Lower (varsOf 46) (d 0xfffcfffcc000c000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_17 : Slice r_22 g_22 (subcubeFast 8 1) 6 := by
  have hc : Lower (varsOf 54) (d 0xfffffcfcc0c00000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_18 : Slice r_22 g_22 (identDom 4 5) 8 := by
  exact slice_ident (u := 4) (v := 5) (by decide +kernel) low_19
set_option maxHeartbeats 0 in
lemma sl_22_19 : Slice r_22 g_22 (identDom 1 3) 8 := by
  have hc : Lower (varsOf 55) (d 0xfefefcfccccc8080) 8 := carry_of (swaps := [(1,3),(2,3),(3,5),(4,5)]) (by decide +kernel) low_21
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_20 : Slice r_22 g_22 (subcubeFast 6 32) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_21 : Slice r_22 g_22 (subcubeFast 6 16) 4 := by
  have hc : Lower (varsOf 41) (d 0xffaaffaaaa00aa00) 4 := carry_of (swaps := [(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_22 : Slice r_22 g_22 (subcubeFast 6 8) 4 := by
  have hc : Lower (varsOf 49) (d 0xffffaaaaaaaa0000) 4 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_23 : Slice r_22 g_22 (subcubeFast 33 16) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_24 : Slice r_22 g_22 (subcubeFast 9 16) 4 := by
  have hc : Lower (varsOf 38) (d 0xfcfcfcfcc0c0c0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_25 : Slice r_22 g_22 (subcubeFast 32 5) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_26 : Slice r_22 g_22 (subcubeFast 5 16) 4 := by
  have hc : Lower (varsOf 42) (d 0xffccffcccc00cc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_27 : Slice r_22 g_22 (subcubeFast 5 8) 4 := by
  have hc : Lower (varsOf 50) (d 0xffffcccccccc0000) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_28 : Slice r_22 g_22 (subcubeFast 32 3) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_29 : Slice r_22 g_22 (subcubeFast 3 16) 4 := by
  have hc : Lower (varsOf 44) (d 0xfff0fff0f000f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_30 : Slice r_22 g_22 (subcubeFast 3 8) 4 := by
  have hc : Lower (varsOf 52) (d 0xfffff0f0f0f00000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 8) (by decide +kernel) hc
def S_22 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 8,9),some (subcubeFast 0 1,9),some (identDom 1 2,10),some (identDom 0 2,10),some (identDom 0 1,10),some (subcubeFast 0 16,8),some (subcubeFast 4 0,8),some (subcubeFast 2 0,8),some (subcubeFast 1 0,8),some (subcubeFast 1 16,7),some (subcubeFast 6 0,7),some (subcubeFast 32 0,8),some (subcubeFast 16 0,7),some (subcubeFast 8 0,7),some (subcubeFast 16 8,6),some (subcubeFast 32 8,6),some (subcubeFast 16 1,6),some (subcubeFast 8 1,6),some (identDom 4 5,8),some (identDom 1 3,8),some (subcubeFast 6 32,4),some (subcubeFast 6 16,4),some (subcubeFast 6 8,4),some (subcubeFast 33 16,4),some (subcubeFast 9 16,4),some (subcubeFast 32 5,4),some (subcubeFast 5 16,4),some (subcubeFast 5 8,4),some (subcubeFast 32 3,4),some (subcubeFast 3 16,4),some (subcubeFast 3 8,4)]
lemma S_22_ok : btAll (fun o => ∀ p, o = some p → Slice r_22 g_22 p.1 p.2) S_22 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (forall_cons (fun _ h => by cases h; exact sl_22_4) (forall_cons (fun _ h => by cases h; exact sl_22_5) (forall_cons (fun _ h => by cases h; exact sl_22_6) (forall_cons (fun _ h => by cases h; exact sl_22_7) (forall_cons (fun _ h => by cases h; exact sl_22_8) (forall_cons (fun _ h => by cases h; exact sl_22_9) (forall_cons (fun _ h => by cases h; exact sl_22_10) (forall_cons (fun _ h => by cases h; exact sl_22_11) (forall_cons (fun _ h => by cases h; exact sl_22_12) (forall_cons (fun _ h => by cases h; exact sl_22_13) (forall_cons (fun _ h => by cases h; exact sl_22_14) (forall_cons (fun _ h => by cases h; exact sl_22_15) (forall_cons (fun _ h => by cases h; exact sl_22_16) (forall_cons (fun _ h => by cases h; exact sl_22_17) (forall_cons (fun _ h => by cases h; exact sl_22_18) (forall_cons (fun _ h => by cases h; exact sl_22_19) (forall_cons (fun _ h => by cases h; exact sl_22_20) (forall_cons (fun _ h => by cases h; exact sl_22_21) (forall_cons (fun _ h => by cases h; exact sl_22_22) (forall_cons (fun _ h => by cases h; exact sl_22_23) (forall_cons (fun _ h => by cases h; exact sl_22_24) (forall_cons (fun _ h => by cases h; exact sl_22_25) (forall_cons (fun _ h => by cases h; exact sl_22_26) (forall_cons (fun _ h => by cases h; exact sl_22_27) (forall_cons (fun _ h => by cases h; exact sl_22_28) (forall_cons (fun _ h => by cases h; exact sl_22_29) (forall_cons (fun _ h => by cases h; exact sl_22_30) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_22 : BT (Option PoolSpec) := btOfList 12 [q 0 [20488,20489,24592,24593,32799,45097],q 0 [20491,4189,81925,86027,20561],q 0 [20488,20489,24592,24593,32799],q 1 [20488,20489,24592,24593,32799],q 9 [20488,20489],q 10 [24592,24593,32799],q 0 [20484,20485,82045,135297,139275],q 0 [20484,20485,82045,135296,143369],q 0 [20484,20485,82045],q 6 [],q 5 [20488,20489,24619],q 20 [],q 1 [20488,20489,24619],q 8 [20488,20489,24619],q 28 [],q 7 [20488,20489,24619],q 0 [20488,20489,81961],q 0 [20484,20485,135295,82109,196619],q 9 [20488,20489,24619],q 10 [16440,16441,217299],q 12 [20488,20489,24619],q 0 [20488,20489,24619,16440,16441,217299],q 14 [20488,20489,24619],q 5 [20484,20485,135295],q 0 [20484,20485,135295,135249,139275],q 0 [20488,20489,24619],q 2 [20492,254197,16636,16637,266499],q 1 [20488,20489,24619,16396,81978],q 13 [20488,20489,24619],q 0 [4105,20489,81925,20561,24660],q 0 [20488,20489,24619,16442,16567],q 0 [20488,20489,24619,16447,16442],q 2 [16396,82165,20768,20769,307495],q 0 [20484,20485,135295],q 12 [102408,102409,336199],q 0 [20561,102408,102409,336199],q 7 [],q 0 [20491,81925,86027,20569],q 0 [20491,82013,81925,86027],q 11 [16396,81925,86027],q 0 [20491,4189,81925,86027],q 0 [20490,20845,81929,20561],q 13 [],q 6 [16396,20561],q 12 [],q 0 [20489,24592,24593,32799],q 1 [20489,24592,24593,32799],q 9 [20489],q 23 [],q 11 [],q 9 [20485],q 1 [20485,135184,135185,389132],q 0 [20485,135184,135185],q 0 [20487,8589,81929,20561],q 0 [20485,135249,139275],q 0 [20485,135249,139271,139287],q 0 [20489,24657,335883,335876],q 0 [20485,135249,139264,139275],q 0 [20485,20561,102407,135251],q 0 [20485,81925,135251,20566],q 0 [20485,81925,20561],q 13 [20485,135187],q 15 [135187],q 0 [20485,81925,86027,20561],q 0 [20485,135179,81925,20561],q 25 [],q 0 [],q 10 [],q 1 [20489,24581,114699],q 9 [20488,20489,462889],q 13 [20488,20489],q 0 [20488,20489,24595,462889],q 6 [24592,24593,32799],q 12 [20488,20489],q 14 [20488,20489],q 12 [20488,20489,32811],q 0 [20488,20489,24592,24593,32811],q 14 [20488,20489,32811],q 0 [20486,20945,135184],q 0 [20484,20485,16543,135187],q 5 [20484,20485],q 0 [20484,20485],q 6 [16396,24657],q 12 [20488,20489,335915],q 0 [20488,20489,24657,335915],q 13 [20488,20489,335915],q 5 [20484,20485,127453],q 18 [20484],q 9 [20484,20485,127453],q 10 [135186,135187],q 0 [20488,20489,24619,16440],q 10 [16440,12499],q 8 [20488,20489,24619,16396],q 1 [20488,20489,24619,57843],q 10 [16386,57843],q 0 [20488,20489,24619,16447],q 15 [],q 0 [20488,20489,24619,16895],q 11 [16392,16393,532999],q 8 [16392,16393,532999],q 1 [16392,16393,532999],q 7 [16392,16393,532999],q 10 [20492,254478],q 0 [16392,16393,532999,254478],q 1 [16392,16393,532999,20492,254478],q 9 [21006,21007],q 10 [21006,21007],q 18 [],q 10 [16441,217100],q 9 [21004,21005],q 10 [21004,21005],q 2 [20496,565493,569356,20497],q 11 [8196],q 7 [20496,20497],q 6 [20496,20497],q 0 [8196,20496,565493,20497],q 10 [16442,57571],q 10 [16398,57779],q 0 [20488,20489,24619,57779],q 0 [16392,16393,532999,21004],q 13 [16392,16393,532999],q 21 [],q 10 [24588,16567],q 0 [20488,20489,24619,16567],q 0 [8197,20589,114704],q 0 [4105,20589,114769,118795],q 1 [20488,20489,24619,16396],q 10 [16396],q 0 [20488,20489,24619,81977],q 10 [12288,622650],q 0 [20488,20489,24619,622650],q 10 [24593,32780],q 0 [20484,20485,135295,135251],q 0 [20491,81925,86027,20561],q 2 [16396,82165,20563,20770],q 0 [20488,20489,24619,16442],q 2 [20725,16396,303184,303739],q 10 [16441,217088],q 0 [20488,20489,24619,16443],q 10 [16443,12935],q 2 [16396,20561,102405,139347],q 2 [16396,82165,20770,20771],q 10 [16442,12515],q 1 [],q 8 [],q 0 [4104,20561,102411,250269],q 0 [20488,20489,24619,24592],q 10 [16573],q 9 [20484,20485,135295],q 2 [20492,254197,16638,16639],q 12 [20484,20485,135295],q 0 [20484,20485,135295,135187],q 16 [20488,20489],q 10 [16396,24760],q 2 [20496,565493,569358,20497],q 2 [16396,82165,20769,307211],q 0 [16392,16393,532999,21006],q 10 [20494,537275],q 0 [16392,16393,532999],q 0 [16392,16393,532999,537275],q 15 [16392,16393,532999],q 2 [20489,16396,81925,24660],q 0 [4105,20489,81925,24660],q 0 [20488,20489,24619,16444],q 0 [20488,20489,24619,16445],q 27 [],q 1 [20488,20489,24619,12344],q 0 [4105,20489,81925,20561],q 0 [4105,20589,81929,20561],q 2 [16396,81925],q 1 [4105,20589,114699],q 2 [20725,16396,303116,303120],q 5 [8196,20725],q 0 [8196,20725],q 0 [4105,20489,82029,20561],q 11 [16396],q 0 [20491,4189,16480],q 0 [20488,20489,24619,24593],q 1 [20488,20489,25075,24619],q 4 [16386,20488,20489,25075,24619],q 10 [16386,25075],q 6 [12288,25187],q 10 [12288,25187],q 0 [20488,20489,25187,24619],q 7 [16396,135249,139275],q 0 [20484,20485,135249,139275],q 10 [16384,749626],q 0 [16384,20488,20489,24619,749626],q 1 [20488,20489,24619,749626],q 10 [16396,81978],q 0 [20488,20489,24619,81978],q 10 [16440,16441],q 0 [20488,20489,24619,16440,16441],q 0 [20488,20489,24619,16441],q 3 [20488,20489,24619,16396],q 2 [20488,20489,24619,16396],q 0 [20488,20489,24619,24657],q 12 [20816,20817,336619],q 0 [81929,20816,20817,336619],q 10 [16396,24588,24592],q 5 [4105,20489],q 0 [4105,20489],q 2 [20492,254197,16636,16637],q 6 [16396,24656],q 0 [20488,20489,24619,24656],q 2 [20489,16396,81929,24660],q 6 [24594,17147],q 10 [24594,17147],q 15 [24595],q 10 [24595,12519],q 7 [16396,135251],q 8 [20484,20485,135295],q 1 [20484,20485,135295],q 6 [20484,20485,135295],q 10 [16396,135251],q 5 [20484,20485,82045],q 8 [20488,20489,16396,81961],q 5 [20488,20489,81961],q 12 [20488,20489,41626],q 10 [12344,16447],q 6 [16384,25311],q 10 [16384,25311],q 1 [20488,20489,25311,24619],q 10 [16398,25011],q 0 [20488,20489,24619,25011],q 0 [81925,20561,20564,790537],q 9 [20488,20489,81961],q 0 [20488,20489,81961,24592],q 13 [20484,20485,135295],q 0 [20489,81925,20561,24660],q 1 [20488,20489,24619,24588],q 2 [16396,82165,20768,20769],q 0 [20488,20489,24619,17175],q 10 [135185],q 0 [20488,20489,24619,24594],q 1 [20488,20489,16396,81961],q 0 [20488,20489,81961,24760],q 3 [20488,20489,16396,81961],q 2 [20488,20489,16396,81961],q 0 [20488,20489,81961,24761],q 0 [20488,20489,81961,24763],q 12 [20488,20489,24763],q 12 [20484,20485],q 9 [20484,20485,82045],q 0 [20484,20485,82045,135187],q 0 [20484,20485,82045,135251],q 13 [20484,20485],q 14 [],q 6 [20496],q 0 [20496,565257,823303],q 8 [20492,253961],q 2 [20492,253961,16692,319490],q 10 [20492,16692,319490],q 0 [253961,16692,319490],q 5 [20492,253961,319490],q 5 [],q 10 [20492,17202],q 14 [253957],q 0 [20563,4261],q 13 [4261,16758],q 0 [20563,4261,16758],q 4 [16396],q 1 [16396],q 2 [16396,20561,102411,4509],q 10 [16396,20561],q 0 [20561,102411,4509],q 12 [102405,139275],q 11 [16396,102405,139275],q 0 [20561,102405,139275],q 2 [16396,20561,102405],q 2 [16396,20561,102404],q 12 [102404,102405],q 0 [20561,102404,102405],q 12 [102408,4423],q 11 [16396,102408,4423],q 0 [20561,102408,4423],q 7 [16396,20563],q 2 [16396,20563,4261],q 1 [16396,81926],q 10 [16396,20563],q 0 [81926,20563,4261],q 6 [16396],q 6 [16396,20819],q 0 [81929,20819,9033],q 12 [20566,20567],q 0 [81925,20566,20567],q 6 [16396,20817],q 0 [81929,20817,335883],q 0 [20561],q 0 [81929,20561,102411],q 2 [16396,81925,20566],q 2 [16396,81929,86027],q 0 [20487,20561,102799],q 0 [20491,81925,20561],q 12 [20491],q 0 [20491,82013,81929],q 6 [16396,82013],q 10 [16396,82317],q 0 [20487,82317,872459],q 7 [16396],q 2 [20491,16396,82013],q 0 [20491,82013,81925],q 0 [20491,4189,20561],q 0 [20491,4189,82018],q 2 [],q 12 [4261,8566],q 0 [20563,4261,8566],q 7 [20491],q 10 [16396,82018],q 11 [16396,82018],q 6 [20487],q 11 [16396,81929],q 0 [20487,8589,81929],q 5 [20491,4189],q 0 [20491,4189],q 0 [20487,8589,16784],q 1 [20491,4189],q 8 [20491,4189],q 7 [16396,20561],q 12 [20486,102407],q 0 [20486,20561,102407],q 0 [20486,81925,20561],q 0 [20490,81929,344431],q 7 [16398,135603],q 0 [20486,20945],q 7 [16396,135187],q 24 [],q 0 [20486,20945,135187],q 7 [16396,135180],q 5 [20486,20945],q 1 [20486,20945],q 8 [20486,20945],q 7 [16396,135248],q 6 [20486,20945],q 0 [20490,20845,81929],q 0 [20491,4189,16482],q 12 [20489],q 5 [20489],q 13 [20489,24592],q 14 [20489],q 13 [20485,135184],q 7 [135184,135185,389132],q 4 [20485,135184,135185,389132],q 12 [20485,389132],q 0 [20485,135184,398209],q 12 [20489,24588],q 0 [20489,24594,185081],q 0 [20485,16543,135187],q 30 [],q 13 [929792],q 5 [20485],q 12 [20485],q 0 [20485,135187,82073],q 0 [20485],q 12 [20485,135180],q 0 [20485,135187],q 10 [20492,17200],q 5 [20492,253957],q 1 [20492,253957,835595],q 11 [835595],q 11 [16396,135180,135184],q 0 [20485,135184],q 5 [20485,135180],q 12 [20485,139275],q 13 [20485,139275],q 0 [20485,135249,139287],q 11 [16396,135249],q 0 [20485,135249],q 9 [],q 16 [20485],q 0 [20485,135249,139283],q 0 [20485,135249,139347],q 13 [20485],q 2 [16396],q 16 [20485,139275],q 0 [20489,24657,335883],q 26 [],q 0 [20485,135249,139264],q 0 [20485,135248,136055],q 2 [20485,16396,135248,136055],q 0 [20485,20563],q 0 [20485,20563,135335],q 0 [20485,20561,135251],q 11 [16396,102411],q 0 [20489,20561,102411],q 0 [20485,20561],q 9 [20485,135248,905225],q 1 [20485,16396,135248,905225],q 7 [16396,135248,905225],q 0 [20485,135248,905225],q 10 [16396,24662],q 0 [20489,81925,24662],q 10 [16396,24660],q 12 [20489,24660],q 0 [20489,81925,24660],q 1 [20489,16396,81925,24660],q 0 [20485,81926],q 0 [20490,20845,16567],q 6 [24588,16567],q 2 [20485,16396,20563],q 11 [16396,81926],q 1 [16396,81926,20563],q 0 [20485,81926,20563],q 0 [20489,81930,24751],q 0 [20485,81925],q 11 [16396,135187],q 0 [20486,20945,135249],q 6 [16396,20816],q 0 [20489,81929,20816],q 0 [20485,81925,135251],q 11 [16396,81925],q 11 [16396,135251],q 0 [20486,20945,20561],q 0 [20489,81929,20561],q 9 [20489,81929,20561],q 1 [16396,81929,20561],q 13 [20489],q 0 [20485,81925,86027],q 7 [20489],q 13 [20489,24583],q 10 [135184],q 0 [20489,24583,16567],q 12 [20489,24583],q 5 [20485,135179],q 6 [20485],q 0 [20485,135179],q 2 [16396,20561],q 7 [16396,81929],q 0 [4105,81929,20561],q 7 [16396,86027],q 0 [8197,81925,86027],q 0 [81925,20561,20566],q 0 [8197,20589],q 5 [8197,20589],q 8 [20485,135179],q 1 [20485,135667],q 8 [20485],q 0 [16386,20485,135667],q 22 [],q 13 [20485,135179],q 2 [20489,16396,24592],q 10 [16396,24592],q 9 [12812],q 10 [12812],q 11 [16396,102405],q 0 [20561,102405,139287],q 1 [20488,20489,24619,24592],q 10 [24592],q 2 [20485,16396,135251],q 2 [20489,24592,28686],q 10 [24592,28686],q 1 [16396,81925,20561],q 0 [81925,20561,20564],q 1 [4105,20489],q 8 [4105,20489],q 2 [20489,16396,24656],q 10 [16396,24656],q 0 [8197,20589,114771],q 9 [20485,135249,139275],q 0 [16384,20485,135903],q 0 [8197,20563,110757],q 0 [16393,20485,135688],q 7 [12288,135779],q 10 [12288,135779],q 9 [20486,20945],q 14 [20485,135179],q 7 [16398,135184],q 0 [20484,20485,135184],q 14 [20484,20485],q 0 [20485,135179,159753],q 6 [20485,135180],q 7 [20489,24588],q 0 [20489,184325],q 0 [20489,184325,24592],q 7 [20589],q 6 [20589],q 0 [4105,20489,82029],q 2 [20489,16396,20561],q 6 [16396,81925],q 0 [20489,81925,20561],q 9 [8196,1007861],q 2 [20497,577548,1007861],q 7 [20497,577548],q 6 [20497,577548],q 0 [8196,20497,1007861],q 13 [8196],q 1 [8196,20492,254197],q 2 [20492,254197,16637],q 7 [16396,135184],q 2 [20489,24588,16567],q 2 [20492,254197,16636],q 7 [20492],q 2 [20489,24595,12519],q 0 [4105,20489,24595],q 6 [16396,20563],q 2 [16396,20563,250021],q 0 [8196,20563,250021],q 6 [16396,20770],q 2 [16396,82165,20770],q 0 [8196,82165,20770],q 2 [16396,82165,20561],q 0 [8196,82165,20561],q 10 [16396,135249],q 10 [16396,24657],q 0 [4105,20489,24657],q 0 [20491,4189,82017],q 1 [20484,20485,135180],q 0 [20484,20485,16541],q 5 [20488,20489],q 9 [8196,82165],q 1 [8196,16396,82165],q 2 [16396,82165,20769],q 0 [8196,82165],q 3 [20485,16396,135249,139275],q 1 [20485,16396,135249,139275],q 2 [20485,16396,135249,139275],q 2 [20725,16396,20561],q 0 [8196,20725,20561],q 0 [20485,135177],q 1 [20485,135179],q 10 [17171],q 12 [20485,135179],q 0 [17171,20485,135179],q 1 [20491,4189,99039],q 10 [16384,99039],q 11 [16384,99039],q 2 [20496,565493,569358],q 0 [8196,20496,565493],q 6 [24595,12519],q 0 [20490,20845,24595],q 10 [24588,24592],q 0 [4105,20489,24592],q 2 [20485,16396,20561],q 11 [16396,102404],q 0 [20485,20561,102404],q 0 [8197,20589,114707],q 2 [20489,16398,25011],q 2 [20725,20499,304123],q 2 [16396,82165,20563],q 2 [20725,303116,303120],q 0 [8196,20725,303120],q 6 [303116],q 3 [16396,81925],q 1 [16396,81925],q 5 [81925],q 0 [81925],q 4 [20488,20489,24619],q 10 [16386],q 6 [16398],q 2 [20485,135179,16398],q 0 [20489,20485,135179],q 1 [20484,20485,135903],q 7 [16384,135903],q 6 [20484,20485],q 10 [16384,135903],q 8 [20484,20485],q 0 [16384,20484,20485,135903],q 9 [20484,20485],q 2 [20725,303116,17095],q 2 [20725,303123,13323],q 0 [8196,20725,303123],q 0 [8197,20589,20563],q 0 [81926,20849],q 13 [20849,364563],q 0 [81926,20849,364563],q 2 [16398],q 0 [8197,20485,135179],q 10 [12288],q 0 [81925,86027,20561],q 9 [8196,565493],q 2 [20496,565493,20497],q 10 [532492,136211],q 0 [16393,20485,136211],q 3 [16384,13023],q 1 [13023],q 5 [13023],q 2 [16396,20561,102511],q 0 [8197,20561,102511],q 15 [16384,135903],q 2 [12299,17171],q 0 [20485,81925,20566],q 7 [16396,20566],q 7 [16384,1090271],q 12 [20564,790537],q 7 [16396,20564,790537],q 0 [81925,20564,790537],q 1 [12292,21541,1090271],q 10 [16384,1090271],q 0 [16384,21541,1090271],q 1 [8197,20589,115423],q 8 [8197,20589],q 10 [16384,115423],q 2 [20725,303116,20499],q 0 [8196,20725,20499],q 4 [16384,13023],q 10 [16398],q 11 [8197],q 0 [8197,20589,20561],q 1 [8196,20725,303839],q 7 [16384,303839],q 6 [16384,303839],q 8 [8196,20725],q 0 [4105,20589,114699],q 10 [12288,115299],q 9 [8197,20589],q 2 [20489,16398,24592],q 10 [16398,24592],q 2 [16396,20561,102411],q 0 [4104,20561,102411],q 10 [16396,135248],q 8 [20485,135180],q 1 [20485,135180,160477],q 10 [16396,20569],q 0 [81925,86027,20569],q 2 [20589,114699,16398],q 12 [102406,102407],q 0 [20561,102406,102407],q 6 [20485,135184],q 8 [20484,20485,16396],q 8 [20488,20489],q 1 [20488,20489],q 7 [20488,20489],q 0 [20488,20489],q 0 [20488,20489,24592],q 10 [16440],q 1 [20488,20489,24619,16440],q 3 [20488,20489,24619],q 1 [20488,20489,24619,24594],q 1 [16396,20563],q 0 [81926,20849,20563],q 12 [20564,20565],q 0 [81925,20564,20565],q 0 [8197,20589,16975],q 2 [20725,303120,729102],q 2 [20725,16398,303120],q 10 [16396,20818],q 0 [81929,20818,5209],q 12 [20565,139275],q 7 [16396,20565,139275],q 0 [81925,20565,139275],q 7 [12288,303715],q 6 [12288,303715],q 9 [8196,20725],q 10 [12344],q 2 [16384,13023],q 10 [16384,13023],q 0 [16389,20489,1151159],q 10 [24588,1151159],q 2 [12288,20725,303715],q 1 [20492,253961],q 2 [20492,253961],q 10 [20492],q 0 [16394,253961,316527],q 11 [16394,316527],q 5 [20492,253961],q 0 [20486,20945,135251],q 1 [20484,20485],q 0 [20484,20485,135779],q 10 [16396,20566],q 0 [8197,81925,20566],q 9 [20494],q 2 [16386,20725,303603],q 1 [20485,135779,135179],q 10 [12288,98915],q 9 [20491,4189],q 11 [12288,98915],q 2 [16384,20485,135903],q 10 [56],q 10 [16384],q 11 [4105],q 0 [4105,20489,20561],q 10 [16398,135603],q 0 [20484,20485,135603],q 0 [8196,20561,102647],q 2 [20492,254197,16639],q 3 [16389,1150987,21637,20491],q 1 [16389,1150987,21637,20491],q 9 [21637,20491],q 2 [16389,1150987,21637,20491],q 10 [21637],q 11 [16389,1150987],q 2 [16386,12787],q 10 [16386,12787],q 2 [20489,16396,24588],q 10 [16396,24588],q 10 [135187],q 2 [20485,16396,114771],q 10 [16396,114771],q 2 [20589,114699,16396],q 0 [4105,20563,8357],q 1 [12787,20485,135179],q 29 [],q 16 [20489,335876],q 0 [20489,24657,335876],q 2 [20725,16396,303116],q 1 [8196,20725],q 2 [20725,16396,303184],q 8 [20485,16396,135184],q 2 [20485,16396,135180,135184],q 0 [20489,25751],q 2 [20725,16396,20563],q 0 [8196,20725,20563],q 0 [20487,8589,17567],q 2 [20496,565493,569356],q 7 [20496],q 8 [16396],q 2 [20725,16396,303185],q 0 [8196,20725,303185],q 7 [16396,303187],q 6 [16396,303187],q 0 [8196,20725,303187],q 2 [20725,16396,303187],q 2 [16396,81929,733195],q 6 [16396,344069],q 0 [81929,344069,733195],q 2 [20725,16398,303539],q 2 [20489,16396,81929],q 6 [24592],q 0 [8197,20485],q 2 [20485,16396,135187],q 10 [16396,135187],q 0 [8197,20485,135187],q 5 [21006],q 11 [16394,16395,775277],q 8 [16394,16395,775277],q 1 [16394,16395,775277],q 7 [16394,16395,775277],q 10 [21006],q 14 [21006],q 1 [16394,16395,775277,21006],q 9 [21006],q 0 [4105,20489,81925],q 2 [20725,16396,303120],q 2 [16396,82029,733195],q 0 [4105,82029,733195],q 2 [16396,81925,20561,102411],q 10 [24593],q 1 [8197,20589],q 10 [16396,21198],q 0 [8197,82029,21198],q 10 [24588],q 10 [59],q 0 [21541,20499,1090555],q 7 [20499,1090555],q 5 [12292,21541],q 0 [16391,20489,25783],q 0 [20484,20485,135251],q 1 [20484,20485,16396,135251],q 2 [16384,20725,303839],q 9 [12292,566309],q 0 [20496,566309,20497],q 10 [20496,20497],q 5 [12299,4881],q 10 [20497,578752],q 0 [4881,20497,578752],q 2 [20589,16396,81929],q 0 [4105,20589,81929],q 10 [20498,1246411],q 10 [17556,25811],q 0 [17556,20489,25811],q 12 [12787],q 2 [20489],q 10 [17171,136171],q 0 [4105,20489,20563],q 7 [135182,17283],q 0 [20484,20485,17283],q 3 [20484,20485,135185,389131],q 1 [20484,20485,135185,389131],q 2 [20484,20485,135185,389131],q 7 [135185,389131],q 11 [135179],q 0 [20485,135179,20561],q 0 [20488,20489,16567],q 2 [20496,565257],q 9 [12815],q 10 [12815],q 9 [21005],q 10 [21005],q 0 [16392,16393,532999,21005],q 9 [21007],q 10 [21007],q 10 [16396,24659],q 0 [20489,24659,4761],q 1 [20484,20485,135667],q 7 [16386,135667],q 3 [16386,20484,20485,135667],q 10 [16386,135667],q 9 [20492],q 10 [16396,82346],q 0 [20485,135179,82346],q 10 [135180,135688],q 9 [20492,254469],q 0 [16392,16393,254469],q 11 [16392,16393],q 7 [20489,25700],q 6 [16389,25700],q 0 [16389,20489,25700],q 0 [8197,82029,20561],q 10 [24576],q 10 [20492,533296],q 11 [16393,533296],q 0 [16393,253957,533296],q 10 [21004],q 9 [21004],q 9 [21237],q 10 [21237],q 2 [16395,13047],q 10 [13047],q 9 [8197,20589,114771],q 3 [20488,20489,24619,24590],q 1 [20488,20489,24619,24590],q 17 [20488,20489,24619],q 2 [20488,20489,24619],q 10 [24590],q 0 [20491,81925,86027],q 2 [16396,82165,20771],q 10 [16441],q 5 [20489,24581],q 10 [24595,114919],q 10 [16442],q 10 [16396,344463],q 0 [20487,81929,344463],q 1 [20485,135667,135179],q 1 [20488,20489,24619,16443],q 10 [16443],q 0 [20496,565253,1318923],q 6 [20496,565253],q 1 [20485,135177],q 8 [20485,135177],q 11 [135177],q 7 [135177],q 0 [20491,81929,20561],q 0 [20484,20485,135248],q 2 [20492,254197,16638],q 4 [20484,20485,16396],q 1 [20484,20485,16396],q 7 [16396,135249],q 2 [20484,20485,16396],q 0 [20484,20485,135249],q 11 [16396,102406],q 0 [20561,102406,21577],q 2 [20725,16396,303123],q 9 [21239],q 10 [21239],q 0 [20484,20485,135187],q 2 [16396,82165,20768],q 12 [8196],q 0 [20484,20485,127873],q 12 [20486],q 0 [20486,82385,20561],q 7 [135184,135185],q 10 [135184,135185],q 0 [20484,20485,135184,135185],q 7 [135185,389132],q 7 [135186,12767],q 1 [20484,20485,135186,127453],q 10 [135186],q 1 [20486,20945,135903],q 7 [135186,16863],q 3 [16396],q 0 [8197,20589,114769],q 2 [12288,20485,135779],q 7 [135187,12443],q 10 [135187,12443],q 12 [20487,20566],q 0 [20487,81925,20566],q 1 [20492,253957,836319],q 8 [20492,253957],q 0 [16384,253957,836319],q 11 [16384,836319],q 2 [16396,81925,20561],q 0 [81925,20561,102404],q 2 [20485,135179,16396],q 11 [135179,24592],q 5 [20485,135177],q 5 [20489,24588],q 0 [20485,135952],q 0 [20485,135177,135184],q 0 [20489,24581,24592],q 6 [24581],q 0 [20489,24581,24595],q 10 [16396,82345],q 0 [20485,135179,82345],q 0 [8197,20485,135251],q 0 [20485,135179,81925],q 0 [20485,16541,135184],q 0 [20485,135179,20563],q 1 [20497,577548,1007621],q 4 [20497,577548,1007621],q 9 [1007621],q 2 [20497,577548,1007621],q 7 [20497,577547],q 1 [20497,577547,5437],q 4 [20497,577547,5437],q 4 [],q 9 [5437],q 2 [20497,577547,5437],q 1 [20492,253957],q 6 [20492,253957],q 0 [253957,17202],q 1 [20492,253957,17202],q 2 [20492,253957,17202],q 1 [20492,253957,17200],q 9 [20492,253957],q 2 [20492,253957,17200],q 3 [],q 3 [20492,253957,835595],q 0 [253957,835595],q 3 [16398,20913,1380363],q 1 [16398,20913,1380363],q 9 [1380363],q 2 [16398,20913,1380363],q 0 [20913,1380363],q 3 [16398,4529,9550],q 1 [16398,4529,9550],q 9 [9550],q 6 [16398,4529],q 12 [102411],q 0 [20561,102411],q 1 [16396,20561,102411],q 9 [20561,102411],q 4 [16396,20561],q 1 [16396,20561],q 12 [102405],q 0 [20561,102405],q 5 [20561],q 9 [20561],q 12 [102404],q 0 [20561,102404],q 8 [16396,20563],q 2 [16396,20563],q 0 [20563],q 0 [81926,20563],q 5 [20563],q 8 [16396,81926],q 5 [81926],q 12 [20566],q 0 [81925,20566],q 12 [86027],q 0 [81925,86027],q 12 [86025],q 0 [81925,86025],q 9 [81925,20566],q 1 [16396,81925,20566],q 2 [16396,81925,86027],q 5 [81925,86027],q 0 [20491,81925],q 9 [20491,82013],q 1 [20491,16396,82013],q 10 [16396,82013],q 0 [20491,82013],q 7 [20491,16479],q 1 [20491,16479,5461],q 4 [20491,16479,5461],q 6 [16479,5461],q 3 [20491,16479,5461],q 9 [20491,5461],q 10 [16479],q 11 [5461],q 4 [16398],q 1 [16398],q 11 [16398],q 10 [16482],q 1 [20491,4189,16482],q 3 [20491,16396,20561],q 1 [20491,16396,20561],q 9 [20491,20561],q 2 [20491,16396,20561],q 0 [20491,20561],q 1 [20491,4189,16480],q 10 [16480],q 11 [16480],q 7 [20498,13515],q 1 [20498,13515],q 8 [20498,13515],q 2 [20498,13515],q 6 [20498,13515],q 5 [13515],q 11 [13515],q 8 [20486],q 1 [20486],q 10 [20498,13515],q 0 [20486],q 1 [20497,577548],q 8 [20497,577548],q 2 [20497,577548],q 19 [],q 13 [20486],q 5 [20486],q 11 [577548],q 0 [20486,20497],q 10 [20497,577548],q 0 [20486,20561],q 0 [20486,81925],q 9 [20486,81925],q 1 [20486,16396,81925],q 9 [20486,82385],q 1 [20486,16396,82385],q 0 [20486,82385],q 11 [16396,82385],q 9 [20486,20487],q 1 [20486,20487,16396],q 6 [20486,20487],q 0 [20486,20487],q 7 [16398],q 7 [20494,17083],q 1 [20494,17083,1409029],q 4 [20494,17083,1409029],q 9 [20494,1409029],q 10 [20494,17083],q 0 [17083,1409029],q 8 [20490,12655],q 1 [20490,12655],q 7 [20490,12655],q 10 [20498],q 14 [20490],q 5 [20490,12655],q 8 [20498],q 1 [20498],q 11 [12655],q 1 [20485],q 9 [20485,12767],q 1 [20485,135186,12767],q 0 [20485,135186],q 3 [20485,135185,389131],q 1 [20485,135185,389131],q 2 [20485,135185,389131],q 0 [20485,135185,389131],q 1 [20485,135184,135185],q 4 [20485,135184,135185],q 14 [20485],q 5 [20485,397321],q 9 [81925,20561],q 0 [81925,20561],q 4 [20489],q 1 [20489],q 9 [20489,28677],q 1 [20489,24592,28677],q 0 [20489,24592,28677],q 1 [20485,135184],q 2 [20485,135184],q 7 [135184],q 11 [135184],q 9 [20489,9417],q 1 [20489,20498,9417],q 7 [20492,16635],q 1 [20492,16635,5493],q 4 [20492,16635,5493],q 9 [20492,5493],q 10 [20492,16635],q 0 [16635,5493],q 11 [5493],q 0 [20497],q 9 [20485,135182],q 1 [20485,135182,17283],q 0 [20485,17283],q 11 [135180,135184],q 8 [20485,135184],q 1 [20485,135180],q 2 [20485,135180,135184],q 7 [135180],q 0 [20485,16541],q 10 [135180],q 0 [20485,159753],q 1 [20489,24588,184325],q 2 [20485,16398,135184],q 11 [16398,135184],q 10 [16398,135184],q 3 [16398,4529],q 1 [16398,4529],q 0 [20489,4529],q 1 [20485,16396,135184],q 2 [20485,16396,135184],q 11 [16396,135184],q 10 [16396,135184],q 3 [16396,81925,86027],q 1 [16396,81925,86027],q 9 [81925,86027],q 0 [20485,135251],q 9 [20485,135251],q 1 [20485,16396,135251],q 5 [20485,135251],q 4 [20485,16396],q 1 [20485,16396],q 2 [20485,16396],q 7 [135187],q 1 [20486,20945,135187],q 1 [20485,16396,135249],q 4 [20485,16396,135249],q 9 [20485,135249],q 9 [20485,135248],q 1 [20485,16396,135248],q 2 [20485,16396,135248],q 11 [16396,135248],q 0 [20485,135248],q 12 [20819],q 0 [81929,20819],q 1 [20489,24595,4325],q 10 [24595],q 0 [20489],q 0 [20489,24595,4325],q 1 [20485,16396,20561],q 4 [20485,16396,20561],q 9 [20485,20561],q 9 [20489,81929],q 1 [20489,16396,81929],q 0 [20489,81929],q 9 [21838],q 7 [16398,21838],q 10 [16398,21838],q 0 [4529,21838],q 3 [20485,135184],q 1 [20485,135179,135184],q 3 [20485,135180],q 2 [20485,135180],q 1 [20485,135179,135180],q 3 [16398],q 1 [20485,135179,16398],q 1 [20485,135179,16396],q 9 [20485,135179],q 3 [20485,135187],q 1 [20485,135187],q 17 [20485],q 2 [20485,114700],q 10 [114700],q 11 [135177,114700],q 8 [20489],q 3 [20485,135168],q 2 [20485,135168],q 10 [135168],q 0 [20485,135168],q 3 [20485,135179],q 9 [20484,82045],q 1 [20484,16396,82045],q 0 [20484,82045],q 3 [20488,20489],q 3 [20488,20489,24594],q 1 [20488,20489,24594],q 2 [20488,20489],q 2 [20488,20489,24594],q 10 [24594],q 7 [135185],q 4 [20484,20485],q 2 [20484,20485],q 3 [20488,20489,24590],q 1 [20488,20489,24590],q 17 [20488,20489],q 17 [20484,20485],q 4 [16396,81925],q 12 [20565],q 7 [16396,20565],q 0 [81925,20565],q 7 [135168],q 3 [20484,20485],q 5 [20488,4139],q 1 [20488,4139],q 8 [20488,4139],q 0 [20488,4139],q 9 [20488,4139],q 1 [20488,4139,16396],q 3 [16395,20497,578295],q 1 [16395,20497,578295],q 2 [16395,20497,578295],q 3 [20492,253957],q 2 [20492,253957],q 11 [16395],q 1 [16395,20492,253957],q 4 [16395],q 3 [20489,24588],q 1 [20489,24588],q 2 [20489,24588],q 11 [24588],q 13 [16395],q 0 [16395,20489],q 1 [16395],q 8 [16395],q 11 [16395,24588],q 2 [20485,16398],q 11 [135180],q 0 [16395],q 0 [16395,20485],q 2 [16395],q 0 [16395,20485,135179],q 1 [16395,20485,135179],q 9 [20489,25783],q 1 [16391,20489,25783],q 10 [25783],q 11 [16391,25783],q 7 [20489,25783],q 4 [16391,20489,25783],q 3 [20485],q 2 [20485],q 10 [135924],q 9 [20485,135924],q 1 [16395,20485,135924],q 11 [16395,135924],q 3 [16395,21237,20491],q 1 [16395,21237,20491],q 9 [21237,20491],q 2 [16395,21237,20491],q 3 [16395,13047],q 1 [16395,13047],q 5 [20491],q 5 [13047],q 11 [16395,13047],q 0 [16395,20491],q 8 [20491],q 1 [20491],q 4 [16391,13495],q 1 [16391,13495],q 0 [16391,20485],q 10 [13495],q 11 [16391,13495],q 5 [13495],q 10 [21914],q 11 [16395,4853],q 3 [16395,4853,21914],q 1 [16395,4853,21914],q 9 [4853,21914],q 12 [21914],q 0 [16395,4853,21914],q 14 [21914],q 7 [16395,20497],q 1 [16395,4853,20497],q 4 [16395,4853,20497],q 9 [4853],q 10 [20497],q 0 [16395,4853,20497],q 3 [20496,565253,1318923],q 1 [20496,565253,1318923],q 9 [565253,1318923],q 2 [20496,565253,1318923],q 10 [20496],q 12 [1318923],q 9 [81926,20849],q 1 [16396,81926,20849],q 12 [20849],q 13 [20849],q 8 [16395,4853],q 1 [16395,4853],q 7 [16395],q 10 [20494],q 7 [16395,21913],q 1 [16395,4853,21913],q 4 [16395,4853,21913],q 6 [4853,21913],q 3 [16395,4853,21913],q 9 [4853,21913],q 12 [21913],q 1 [16395,4853,13720],q 9 [4853,13720],q 0 [16395,4853],q 10 [13720],q 12 [13720],q 0 [20489,16567],q 9 [20489,24588],q 1 [20489,24588,16567],q 11 [24588,16567],q 0 [16390,253957],q 11 [16390],q 5 [20494],q 12 [20494],q 8 [16390,16391],q 6 [16390,16391],q 11 [16390,16391],q 12 [102406],q 0 [20561,102406],q 5 [20492],q 5 [21685],q 10 [21685],q 9 [21685],q 0 [16390,16391,21685],q 7 [16393,21002],q 1 [16393,21002,5553],q 4 [16393,21002,5553],q 9 [5553],q 10 [21002],q 0 [16389,16635],q 11 [16389],q 1 [20485,135903],q 11 [16384,135903],q 2 [20485,114704],q 10 [114704],q 11 [135177,114704],q 9 [8196],q 2 [20497,577783],q 7 [20497],q 8 [20497,577543],q 9 [20486],q 9 [21953],q 6 [21953],q 0 [16394,21953],q 10 [21953],q 8 [8196],q 1 [8196],q 6 [20496,565262],q 7 [20496,565262],q 0 [8196],q 1 [20496,565262],q 8 [20496,565262],q 0 [8196,20496],q 1 [8196,20496,565262],q 5 [565262],q 2 [20496,565262],q 1 [8196,20496,565493],q 2 [20496,565493],q 6 [20492],q 0 [8196,254197],q 2 [20492,254197],q 9 [12299,21965],q 1 [12299,17168,21965],q 6 [17168,21965],q 10 [17168,21965],q 0 [17168,21965],q 3 [20489,20485,135179],q 1 [20489,20485,135179],q 2 [20485,135179],q 0 [8196,20561],q 1 [8196,20725,303120],q 2 [20725,303120],q 7 [303120],q 6 [303120],q 7 [20498],q 9 [20486,5321],q 0 [20486,20498,5321],q 1 [20486,20498,5321],q 7 [303123],q 6 [303123],q 1 [8196,20725,303123],q 2 [20725,303123],q 1 [13787,1536005],q 7 [20482,13787],q 2 [20482,13787,1536005],q 0 [20482,1536005],q 9 [1536005],q 3 [20494,4793,9702],q 1 [20494,4793,9702],q 0 [4793,9702],q 1 [8196,20725,303116],q 2 [20725,303116],q 7 [303116],q 8 [16398],q 2 [20725,16398],q 9 [12296,22001],q 1 [12296,17903,22001],q 6 [22001],q 0 [17903,22001],q 10 [22001],q 7 [16395,21238],q 1 [16395,21238,4857],q 4 [16395,21238,4857],q 9 [21238,4857],q 10 [21238],q 2 [16631,20497],q 6 [20497],q 11 [8196,16631],q 0 [8196,16631,20497],q 7 [22013],q 6 [22013],q 9 [8196,22013],q 0 [8196,16631,22013],q 1 [8196,16631,22013],q 3 [16384],q 2 [16384],q 0 [16384],q 13 [16384],q 5 [8197,20485],q 1 [8197,20485],q 8 [8197,20485],q 1 [12292,1086937],q 0 [20482,1086937],q 4 [20482,12292,1086937],q 10 [20482],q 9 [12292],q 3 [20499,5113,9738],q 1 [20499,5113,9738],q 9 [9738],q 6 [20499,5113],q 11 [9738],q 7 [20492,1151227],q 14 [1151227],q 10 [20492,1151227],q 0 [16389,1151227],q 8 [20496],q 1 [20496],q 2 [20496],q 0 [20496],q 11 [8196,12535],q 9 [8196,12535],q 1 [8196,12535],q 14 [8196],q 7 [20499,9209],q 1 [4105,20499,9209],q 4 [4105,20499,9209],q 9 [4105],q 2 [20499,9209],q 1 [8196,251353],q 2 [20482,251353],q 4 [20482,8196,251353],q 3 [20482,8196,251353],q 5 [20494,4793],q 1 [20494,4793],q 4 [20494,4793],q 7 [20494],q 16 [],q 15 [16386],q 3 [20494,4793],q 6 [20494,4793],q 4 [16386,20494,4793],q 3 [16386,20494,4793],q 13 [16386],q 2 [16386],q 11 [24595,12519],q 0 [20489,24595],q 7 [16396,82029],q 1 [8197,16396,82029],q 4 [8197,16396,82029],q 6 [16396,82029],q 3 [8197,16396,82029],q 0 [8197,82029],q 9 [8197,82029],q 0 [20485,20489],q 1 [12292,1087009],q 0 [20480,1087009],q 8 [12292],q 7 [20480],q 10 [20480],q 1 [20492,254685],q 0 [16384,254685],q 5 [20492,254685],q 1 [13859,8197],q 10 [20480,13859],q 8 [8197],q 9 [8197],q 0 [8197],q 2 [20480,13859],q 4 [20491,4189],q 3 [20491,4189],q 6 [4189],q 3 [16386,20491,4189],q 2 [16386,20491,4189],q 0 [16386],q 13 [86027],q 4 [20486,20945],q 3 [20486,20945],q 11 [16386],q 9 [20562,22065],q 1 [16396,20562,22065],q 0 [20562,22065],q 7 [20498,1152203],q 3 [4104,20497,577547],q 1 [4104,20497,577547],q 9 [4104],q 2 [20497,577547],q 1 [8196,250589],q 2 [16384,250589],q 7 [16384],q 6 [20492,16635],q 0 [8196,16635],q 1 [20492,16635],q 1 [8196,20492,16635],q 2 [20492,16635],q 3 [4105,20589,114699],q 2 [20589,114699],q 16 [20489],q 1 [20485,20489],q 2 [16386,20485],q 0 [20491,622685],q 1 [20491,622685],q 4 [12288,20491,622685],q 3 [12288,20491,622685],q 10 [12288,622685],q 9 [20491],q 7 [16386],q 5 [20488,12331],q 1 [20488,12331],q 4 [20488,12331],q 7 [20488,12331],q 3 [20488,12331],q 3 [16391,13495],q 0 [16391,20489],q 2 [16396,82165],q 3 [20488,4139],q 9 [20492,253961],q 0 [16393,253961],q 5 [20486,20487],q 1 [20486,20487],q 3 [20486,20487],q 7 [1151375],q 9 [20487],q 10 [1151375],q 5 [12299],q 16 [12299],q 1 [12299,20485],q 1 [20491,749661],q 10 [16384,749661],q 1 [20489,16396,81925],q 2 [20489,16396,81925],q 0 [20489,81925],q 4 [8197,20589],q 3 [8197,20589],q 4 [16386,8197,20589],q 4 [8196,20725],q 3 [8196,20725],q 2 [16386,20725],q 4 [16386,20485,135667],q 3 [16386,20485,135667],q 2 [16386,20485,135667],q 3 [16391,21685,1486859],q 1 [16391,21685,1486859],q 9 [21685,1486859],q 2 [16391,21685,1486859],q 12 [1486859],q 8 [20494,4793],q 0 [4793],q 0 [16384,4793],q 11 [4793],q 15 [16384],q 9 [20494,4793],q 1 [21213,12299],q 2 [16384,21213],q 0 [16384,21213],q 9 [12299],q 11 [16384],q 17 [21213],q 1 [13023,20485],q 2 [16384,13023,20485],q 11 [16384,13023],q 1 [12292,21541],q 4 [12292,21541],q 3 [12292,21541],q 6 [12292,21541],q 0 [21541],q 0 [16386,21541],q 11 [12292],q 4 [16386,12292,21541],q 3 [16386,12292,21541],q 6 [16386],q 0 [16390,255401],q 3 [8197,20485,135179],q 1 [8197,20485,135179],q 1 [16396,81925,81929],q 9 [81925,81929],q 0 [81925,81929],q 1 [12787,21433],q 4 [16386,12787,21433],q 3 [16386,12787,21433],q 8 [21433],q 0 [16386,21433],q 1 [12787,20485],q 4 [16386,12787,20485],q 3 [16386,12787,20485],q 2 [16386,12787,20485],q 11 [16386,12787],q 3 [20491,12383],q 1 [20491,12383],q 2 [20491,12383],q 10 [12383],q 14 [20491],q 4 [12299,21265],q 1 [12299,21265],q 8 [16389],q 1 [16389],q 10 [21265],q 5 [12299,21265],q 0 [21265,16389],q 6 [16391],q 11 [16391],q 13 [16391],q 0 [16391],q 4 [12299,20494],q 1 [12299,20494],q 5 [12299,20494],q 11 [12299],q 5 [8197],q 15 [8197],q 13 [8197],q 16 [20494],q 3 [16386,20494],q 1 [8197,20494],q 2 [16386,20494],q 0 [16386,8197],q 7 [20489,25751],q 1 [12295,20489,25751],q 4 [12295,20489,25751],q 11 [12295,25751],q 1 [21213,1650693],q 8 [1650693],q 7 [16384,21213],q 10 [16384,21213],q 0 [16384,21213,1650693],q 9 [1650693],q 4 [4105,20489],q 9 [4105,20489],q 2 [12288,20489],q 8 [20494],q 7 [16392,528386],q 11 [16392,528386],q 0 [16392,528386],q 3 [16386],q 4 [20485,135179],q 3 [16396,20561,102411],q 7 [12288],q 6 [12288],q 11 [12288],q 3 [12288,20485],q 2 [12288],q 2 [12288,20485,135179],q 3 [12288],q 5 [12288],q 4 [20489,24588,184325],q 6 [24588,184325],q 3 [20489,24588,184325],q 17 [],q 1 [13023,20491],q 13 [20491],q 0 [20497,577547],q 3 [20497,577547],q 3 [12299,20497,577547],q 1 [12299,20497,577547],q 2 [12299,20497,577547],q 4 [20485,20489],q 3 [20485,20489],q 2 [12288,20485],q 1 [12292,20496,566309],q 0 [20496,566309],q 12 [12292],q 3 [20499,5113],q 1 [20499,5113],q 2 [20499,5113],q 10 [20499],q 0 [20499,5113],q 1 [12299],q 4 [12299],q 9 [20563,4261],q 1 [16396,20563,4261],q 12 [4261],q 13 [4261],q 8 [20486,20487],q 6 [21237],q 11 [16392,16903],q 0 [16392,16903,21237],q 6 [20494,17083],q 1 [20494,17083],q 8 [20494,17083],q 2 [20494,17083],q 0 [17083],q 0 [8196,17083],q 15 [8196],q 2 [20489,24592],q 2 [12288,20486,20945],q 4 [12299,20485],q 2 [16384,20485],q 1 [13931,22125],q 4 [8192,13931,22125],q 3 [13931,22125],q 8 [22125],q 6 [22125],q 0 [8192,22125],q 9 [22125],q 10 [22125],q 0 [16386,20485],q 1 [20485,20494],q 2 [20489,16398],q 10 [21698],q 11 [12299,4881],q 8 [12299],q 0 [4881,21698],q 12 [12299],q 3 [12299,4881,21698],q 1 [12299,4881,21698],q 17 [21698],q 10 [25751],q 1 [21089,1695755],q 2 [12288,21089,1695755],q 0 [21089,1695755],q 9 [1695755],q 1 [12787,8197],q 4 [16386,12787,8197],q 3 [16386,12787,8197],q 2 [20489,16396],q 7 [12399,22145],q 1 [8197,12399,22145],q 4 [8197,12399,22145],q 6 [12399,22145],q 3 [8197,12399,22145],q 0 [8197,22145],q 10 [22145],q 11 [8197,12399],q 7 [20489,24592],q 4 [20489,24592,28677],q 6 [24592,28677],q 3 [20489,24592,28677],q 13 [22154],q 1 [12299,17169,22154],q 2 [12288,20491,4189],q 8 [8196,12535],q 6 [20498],q 5 [8196,12535],q 18 [8196,12535],q 3 [12295,21653],q 1 [12295,21653],q 2 [12295,21653],q 10 [21653],q 5 [12295,21653],q 0 [21653,16395],q 11 [12295],q 4 [20492,253957],q 0 [253957],q 0 [16386,253957],q 3 [16386,20492,253957],q 4 [16386],q 2 [16386,20492,253957],q 1 [20484,20485,135184],q 5 [20485,135903],q 0 [16384,253957],q 2 [16384,20492,253957],q 1 [16389,20489,25700],q 4 [16389,20489,25700],q 3 [16389,20489,25700],q 10 [25700],q 11 [16389,25700],q 2 [20725,303104],q 7 [303104],q 10 [135952],q 11 [12299,135952],q 8 [20488,16427],q 4 [20488,16427],q 7 [20488,16427],q 3 [20488,16427],q 1 [20488,16427],q 9 [20489,28686],q 1 [20489,24592,28686],q 11 [24592,28686],q 3 [20489,20497,577547],q 1 [20489,20497,577547],q 2 [20489,20497,577547],q 1 [8196,250465],q 2 [12288,250465],q 4 [12288,8196,250465],q 0 [8196,250465],q 3 [12288,8196,250465],q 4 [16393],q 1 [16393],q 13 [16393],q 15 [16393],q 0 [4096,255649],q 1 [20492,255649],q 4 [20492,255649],q 3 [4096,20492,255649],q 11 [4096],q 1 [13023,8197],q 14 [8197],q 1 [12299,1606417],q 0 [20480,1606417],q 10 [20480,1606417],q 1 [12299,750353],q 0 [16384,750353],q 10 [16384,750353],q 1 [12299,804313],q 10 [20482,804313],q 3 [20498,5321],q 1 [20498,5321],q 2 [20498,5321],q 0 [20498,5321],q 5 [5321],q 7 [16393,532492],q 1 [16393,532492,1064965],q 4 [16393,532492,1064965],q 6 [532492,1064965],q 3 [16393,532492,1064965],q 0 [16393,1064965],q 9 [1064965],q 10 [532492],q 0 [20485,135779],q 1 [20485,135779],q 11 [12288,135779],q 1 [20485,16396,20563],q 9 [20485,20563],q 1 [8197,12399],q 8 [8197,12399],q 5 [8197,12399],q 3 [20498],q 13 [20498],q 18 [8197,12399],q 0 [20485,20498],q 4 [16386,4105,20489],q 2 [16386,20489],q 2 [16384,20485,135179],q 2 [16384,20494],q 7 [20497,578711],q 1 [12295,20497,578711],q 4 [12295,20497,578711],q 9 [12295],q 0 [20497,578711],q 10 [20497,578711],q 3 [16389,21606],q 1 [16389,21606],q 0 [16389,21606],q 1 [20977,1769483],q 2 [16386,20977,1769483],q 5 [1769483],q 2 [20725,16396],q 7 [22037],q 6 [22037],q 0 [8196,22037],q 0 [20491],q 8 [16388,16389],q 6 [16388,16389],q 11 [16388,16389],q 0 [16388,16389],q 8 [20485,16396],q 9 [20485,135180],q 1 [20485,16396,135180],q 2 [20485,16396,135180],q 11 [16396,135180],q 10 [16396,135180],q 0 [16384,20485],q 4 [20485,20494],q 7 [17559],q 0 [17559,16389],q 10 [17559],q 4 [20485,135180],q 1 [20484,127709],q 5 [20484,127709],q 8 [20484],q 6 [20499,13307],q 1 [20499,13307],q 8 [20499,13307],q 2 [20499,13307],q 7 [20499,13307],q 1 [20977,12299],q 2 [16386,20977],q 0 [16386,20977],q 8 [20488,12331],q 9 [20488,12331],q 7 [20499],q 6 [20499],q 2 [20725,20499],q 7 [20496,565257],q 1 [4105,20496,565257],q 4 [4105,20496,565257],q 9 [4105,565257],q 0 [4105,20496,565257],q 12 [4105],q 1 [12292,1086173],q 0 [16384,1086173],q 5 [12292,1086173],q 4 [16384,12292,1086173],q 2 [16396,82029],q 12 [8197],q 1 [20484,127585],q 4 [12288,20484,127585],q 0 [20484,127585],q 3 [12288,20484,127585],q 9 [20484],q 3 [16389,1150988],q 1 [16389,1150988],q 2 [16389,1150988],q 10 [1150988],q 11 [16389,1150988],q 0 [16389,20491],q 10 [532879],q 2 [16384,20491,4189],q 1 [21089,1695749],q 0 [21089,1695749],q 7 [12288,21089],q 10 [12288,21089],q 9 [1695749],q 11 [12288,1695749],q 1 [12787,974853],q 7 [16386,12787],q 5 [974853],q 3 [8197,16495,20497],q 1 [8197,16495,20497],q 11 [8197,16495],q 0 [8197,16495,20497],q 7 [1150987,21637],q 1 [16389,1150987,21637],q 4 [16389,1150987,21637],q 6 [16389,21637],q 3 [16389,1150987,21637],q 9 [21637],q 0 [16389,1150987,21637],q 0 [20485,135185],q 10 [114707],q 3 [20494,17083],q 1 [8197],q 4 [20498,13515],q 0 [21541,20499],q 9 [12292,21541],q 3 [16389,1150987,20491],q 1 [16389,1150987,20491],q 2 [16389,1150987,20491],q 1 [4105,16396,81929],q 4 [4105,16396,81929],q 9 [4105,81929],q 2 [16396,81929],q 0 [4105,81929],q 7 [16783],q 10 [16783],q 1 [16396,81929],q 0 [8196,20563],q 3 [8197,20497,577647],q 1 [8197,20497,577647],q 2 [20497,577647],q 1 [12787,20491],q 3 [12295,17559],q 1 [12295,17559],q 0 [17559,20489],q 11 [12295,17559],q 7 [16396,20562],q 1 [16396,20562,5681],q 4 [16396,20562,5681],q 9 [20562,5681],q 0 [20562,5681],q 1 [8196,251425],q 2 [20480,251425],q 0 [8197,20561],q 3 [20487,12687],q 1 [20487,12687],q 14 [20487],q 10 [12687],q 0 [8197,20563],q 2 [16386,20485,135179],q 7 [20492,253961],q 1 [4105,20492,253961],q 4 [4105,20492,253961],q 0 [4105,253961],q 1 [12299,4881,17600],q 8 [12299,4881],q 9 [12299,4881],q 7 [12299],q 10 [17600],q 13 [17600],q 14 [4881],q 1 [20485,16396,81926],q 9 [20485,81926],q 7 [16393,533655],q 1 [12295,16393,533655],q 4 [12295,16393,533655],q 0 [16393,533655],q 10 [533655],q 0 [8197,16635],q 1 [8197,20492,16635],q 2 [20494,4793],q 14 [4793],q 3 [20496,20497],q 3 [12299,20496,20497],q 1 [20496,20497],q 1 [12299,20496,20497],q 2 [20496,20497],q 2 [12299,20496,20497],q 0 [20496,20497],q 18 [12299],q 7 [20496,565357],q 1 [8197,20496,565357],q 4 [8197,20496,565357],q 6 [20496,565357],q 3 [8197,20496,565357],q 9 [8197,565357],q 2 [20496,565357],q 0 [8197,20496,565357],q 2 [20725,20497],q 10 [20496,565262],q 3 [20496,565262],q 0 [8197,20496],q 1 [8197,20496,565262],q 0 [20489,24594],q 8 [20489,24594],q 1 [20489,24594],q 1 [12299,4881],q 1 [8197,20496,20497],q 4 [8197,20496,20497],q 3 [8197,20496,20497],q 0 [8197,20496,20497],q 18 [8197],q 3 [20497,577548],q 0 [8197,20497],q 7 [20498,111817],q 1 [8197,20498,111817],q 4 [8197,20498,111817],q 6 [20498,111817],q 3 [8197,20498,111817],q 9 [8197,111817],q 2 [20498,111817],q 3 [20498,13515],q 3 [12295,21653,1720331],q 1 [12295,21653,1720331],q 0 [21653,1720331],q 0 [16384,21541],q 8 [12292,21541],q 6 [16384],q 7 [20499,111609],q 1 [8197,20499,111609],q 4 [8197,20499,111609],q 6 [20499,111609],q 3 [8197,20499,111609],q 1 [20491,4189,12384],q 10 [12384],q 11 [12384],q 3 [12299,20485,135179],q 1 [12299,20485,135179],q 17 [20485,135179],q 3 [20499,13307],q 10 [20499,13307],q 9 [12296],q 0 [17903,20497],q 2 [16384,20489],q 3 [12299,17171],q 1 [12299,17171],q 11 [12299,17171],q 0 [17171],q 0 [17171,20491],q 0 [21541,1089536],q 7 [1089536],q 10 [1089536],q 2 [20499,250873],q 7 [20492,254061],q 1 [8197,20492,254061],q 4 [8197,20492,254061],q 6 [20492,254061],q 3 [8197,20492,254061],q 0 [8197,254061],q 0 [21541,20497],q 9 [20491,95413],q 1 [16391,20491,95413],q 2 [16391,20491,95413],q 10 [95413],q 3 [20497,577543],q 1 [20497,577543],q 7 [1089555],q 10 [1089555],q 0 [21541,1089555],q 14 [21541],q 1 [12292,21541,1089555],q 1 [16395,4853,20498],q 7 [16395,20498],q 8 [20496,20497],q 18 [12292],q 0 [20486,623057],q 1 [20486,623057],q 2 [12295,17559],q 0 [17559],q 0 [17559,20491],q 2 [20492,253957,835595],q 0 [20497,579055],q 14 [579055],q 9 [12292,1086665],q 1 [12292,20498,1086665],q 0 [20498,1086665],q 11 [12292,1086665],q 9 [21237,20489],q 1 [16395,21237,20489],q 0 [20499,1086457],q 1 [20485,135179,135187],q 10 [17602],q 0 [4881,17602],q 1 [12299,4881,17602],q 13 [17602],q 1 [20485,135185,389132],q 4 [20485,135185,389132],q 3 [20489,24592],q 1 [20489,24592],q 0 [20489,24592],q 1 [20489,24590],q 8 [20489,24590],q 7 [12299,21697],q 1 [12299,4881,21697],q 4 [12299,4881,21697],q 6 [4881,21697],q 3 [12299,4881,21697],q 0 [4881,21697],q 10 [21697],q 3 [20498,5321,9686],q 1 [20498,5321,9686],q 9 [5321,9686],q 2 [20498,5321,9686],q 12 [9686],q 9 [20490],q 11 [16751],q 0 [4881],q 7 [12299,20494],q 1 [12299,4881,20494],q 4 [12299,4881,20494],q 2 [20485,16398,135603],q 11 [16398,135603],q 0 [20485,135603],q 1 [21213,1650699],q 2 [16384,21213,1650699],q 9 [1650699],q 1 [12299,4881,20497],q 4 [20497],q 13 [20497],q 1 [20496,565253,1318924],q 8 [20496,565253],q 9 [565253,1318924],q 2 [20496,565253,1318924],q 0 [20496,565253],q 12 [1318924],q 10 [20496,1318924],q 9 [81925],q 12 [20564],q 7 [16396,20564],q 0 [81925,20564],q 0 [16389],q 0 [16389,20489],q 2 [12299,4881,20498],q 2 [20498],q 0 [4881,20498],q 18 [12299,4881],q 7 [16495,22261],q 1 [8197,16495,22261],q 4 [8197,16495,22261],q 6 [16495,22261],q 3 [8197,16495,22261],q 9 [8197,22261],q 2 [16495,22261],q 0 [8197,16495,22261],q 10 [22261],q 7 [12299,17168],q 1 [12299,17168,5581],q 4 [12299,17168,5581],q 9 [12299,5581],q 10 [17168],q 0 [17168,5581],q 3 [20496,565253],q 1 [20496,565253],q 2 [20496,565253],q 11 [1318923],q 1 [12292,21541,1089552],q 0 [21541,1089552],q 7 [1089552],q 10 [1089552],q 7 [17556],q 1 [12295,17556,5329],q 9 [12295,5329],q 10 [17556],q 0 [17556,5329],q 9 [20492,255693],q 1 [16388,20492,255693],q 0 [16388,255693],q 11 [16388],q 12 [20492],q 0 [17168,20485],q 4 [12299,17168],q 1 [12299,17168],q 11 [12299,17168],q 2 [12288,20725],q 4 [12295,17559],q 0 [17559,20485],q 9 [12295,775317],q 1 [12295,16395,775317],q 2 [12295,16395,775317],q 0 [16395,775317],q 10 [775317],q 0 [16393],q 0 [16393,20485],q 18 [8196],q 1 [16391],q 3 [16391],q 10 [21266],q 4 [12299,21266],q 1 [12299,21266],q 5 [12299,21266],q 2 [16384,20725],q 7 [17559,22225],q 1 [12295,17559,22225],q 4 [12295,17559,22225],q 9 [12295,22225],q 10 [17559,22225],q 0 [17559,22225],q 2 [20485,16396,135249],q 5 [21687],q 1 [16390,16391],q 9 [21687],q 10 [21687],q 0 [16390,16391],q 9 [8196,251081],q 1 [8196,20498,251081],q 2 [20498,251081],q 0 [21265,20489],q 7 [12299,17171],q 1 [12299,17171,5097],q 4 [12299,17171,5097],q 6 [17171,5097],q 3 [12299,17171,5097],q 9 [12299,5097],q 0 [17171,5097],q 3 [12299,21265,20491],q 1 [12299,21265,20491],q 6 [21265],q 0 [21265,20491],q 7 [12299,21266],q 1 [12299,21266,4885],q 4 [12299,21266,4885],q 9 [12299,566033],q 1 [12299,20496,566033],q 6 [20496,566033],q 10 [20496,566033],q 0 [20496,566033],q 10 [21266,21269],q 1 [12299,21266,21269],q 4 [12299,21266,21269],q 3 [12299,21266,21269],q 0 [21266,21269],q 3 [16389,20498],q 1 [16389,20498],q 2 [16389,20498],q 3 [16391,20497],q 1 [16391,20497],q 2 [16391,20497],q 9 [20492,254709],q 1 [16395,20492,254709],q 6 [20492,254709],q 10 [20492,254709],q 0 [16395,254709],q 2 [12299],q 0 [20491,81929],q 0 [20491,95381],q 7 [20497,135184],q 1 [20485,20497,135184],q 4 [20485,20497,135184],q 10 [20497,135184],q 0 [20485,20497,135184],q 3 [16393,532492],q 1 [16393,532492],q 2 [16393,532492],q 11 [16393,532492],q 0 [16393,20491],q 7 [16395,21914],q 5 [565253],q 9 [12299,804041],q 1 [12299,20498,804041],q 10 [20498,804041],q 11 [12299,804041],q 1 [20486,20945,135180],q 3 [16394,16395,775277],q 2 [16394,16395,775277],q 0 [16394,16395,775277],q 10 [20499,803833],q 3 [12296,20497,577547],q 1 [12296,20497,577547],q 2 [12296,20497,577547],q 8 [20492],q 5 [528386],q 8 [16388,22221],q 1 [16388,22221],q 9 [22221,1990668],q 1 [16388,22221,1990668],q 7 [1990668],q 6 [16388,22221],q 10 [1990668],q 0 [16388,22221],q 12 [1990668],q 0 [16389,20485],q 1 [16389,20485,135184],q 0 [16389,20485,135184],q 11 [16389,135184],q 1 [20486,750033],q 7 [21606],q 1 [16393,20492,253957],q 0 [16393,253957],q 11 [16393],q 3 [16389,1150987,21638],q 1 [16389,1150987,21638],q 9 [21638],q 2 [16389,1150987,21638],q 10 [21638],q 3 [16389,1150987,20498],q 1 [16389,1150987,20498],q 3 [16391,21685],q 1 [16391,21685],q 2 [16391,21685],q 0 [16391,21685],q 7 [1150988,22245],q 1 [16389,1150988,22245],q 4 [16389,1150988,22245],q 9 [22245],q 10 [1150988,22245],q 0 [16389,22245],q 4 [20499,5113],q 9 [13515],q 9 [5321],q 0 [20496,16939],q 4 [20496,565253],q 9 [565253],q 11 [17083],q 9 [20563],q 9 [20562],q 1 [16396,20562],q 0 [20562],q 3 [20491,16396],q 1 [20491,16396],q 2 [20491,16396],q 1 [20487,16783],q 0 [20487,16783],q 1 [20497],q 8 [20497],q 2 [20497],q 1 [20494],q 2 [20494],q 6 [20494],q 1 [20486,20494],q 6 [20486],q 1 [20490,16751],q 0 [20490,16751],q 4 [20485,135187],q 2 [20485,135187],q 11 [135187],q 3 [20489],q 3 [20489,24594],q 2 [20489,24594],q 4 [20485,135184],q 1 [20485,20497],q 4 [20485,20497],q 4 [20494],q 0 [20498],q 1 [20486,20498],q 1 [20485,20498],q 1 [20485,16398],q 4 [20485,16398],q 0 [20913],q 0 [20490],q 5 [20484],q 1 [20484],q 0 [20484],q 0 [20488],q 1 [16395,20498],q 0 [16395,20498],q 3 [16395,20497],q 1 [16395,20497],q 2 [16395,20497],q 0 [16395,20497],q 1 [16395,20494],q 15 [16395],q 9 [565262],q 3 [20489,24590],q 17 [20489],q 3 [20492],q 3 [16395,20492],q 1 [20492],q 1 [16395,20492],q 2 [20492],q 2 [16395,20492],q 3 [20491],q 3 [16395,20491],q 1 [16395,20491],q 2 [20491],q 2 [16395,20491],q 1 [20497,577547],q 3 [20487],q 3 [16395,20487],q 1 [20487],q 1 [16395,20487],q 2 [20487],q 5 [20487],q 0 [20487],q 12 [20487],q 4 [20498,5321],q 3 [16395,20485],q 1 [16395,20485],q 2 [16395,20485],q 5 [8196],q 1 [20499],q 8 [20499],q 0 [20499],q 2 [20499],q 1 [8196,20496],q 4 [20485],q 4 [16386,20485],q 3 [16386,20485],q 1 [20484,16396],q 6 [20484],q 1 [12292],q 1 [12292,20498],q 7 [20482],q 3 [12292],q 6 [12292],q 0 [20482],q 5 [12292],q 2 [20482],q 6 [20482],q 1 [12292,20496],q 2 [20482,20485],q 0 [20482,20485],q 3 [12299,21265],q 0 [21265],q 3 [20494],q 4 [16386,20494],q 4 [20492],q 4 [16386,20492],q 3 [16386,20492],q 3 [16386,12292],q 3 [16386,20491],q 4 [20491],q 4 [16386,20491],q 0 [16386,20491],q 3 [20484],q 3 [16395,20489],q 1 [16395,20489],q 2 [16395,20489],q 3 [16395,21239],q 1 [16395,21239],q 2 [16395,21239],q 13 [20482],q 1 [16389,20489],q 4 [16389,20489],q 6 [16389],q 3 [16389,20489],q 4 [8196],q 3 [8196],q 0 [16635],q 4 [20485,135177],q 3 [20485,135177],q 3 [16389],q 3 [12299,16389],q 1 [12299,16389],q 2 [16389],q 2 [12299,16389],q 13 [16389],q 2 [20725],q 3 [16389,1150987],q 1 [16389,1150987],q 2 [16389,1150987],q 0 [16389,1150987],q 1 [8196,20494],q 3 [12299],q 3 [16386,12299],q 3 [16395,4853],q 2 [16395,4853],q 1 [13787],q 4 [20482,13787],q 3 [20482,13787],q 6 [4096],q 0 [4096],q 4 [8197],q 3 [8197],q 0 [16384,8197],q 3 [16395,21238],q 1 [16395,21238],q 9 [21238],q 2 [16395,21238],q 6 [21238],q 0 [16395,21238],q 1 [13931],q 0 [8192],q 3 [20486],q 1 [21089],q 4 [12288,21089],q 3 [12288,21089],q 0 [21089],q 4 [20482],q 1 [8196,16631],q 2 [16631],q 1 [8196,16396],q 6 [20480],q 2 [20480],q 0 [20482,8197],q 0 [20480],q 7 [12687],q 4 [20487,12687],q 3 [12299,20494],q 3 [12299,20489],q 1 [12299,20489],q 4 [16398,4529],q 0 [4529],q 1 [21213],q 5 [21213],q 9 [5323],q 1 [20498,5323],q 0 [20498,5323],q 3 [20482],q 3 [20482,12299],q 4 [20486],q 3 [16384,20491],q 0 [16384,20491],q 4 [16386,8197],q 3 [16386,8197],q 3 [16384,12299],q 1 [8196,20492],q 1 [20494,20498],q 3 [20497],q 3 [12299,20497],q 1 [12299,20497],q 2 [12299,20497],q 0 [81926],q 9 [81926],q 9 [22221],q 1 [12787],q 4 [16386,12787],q 3 [16386,12787],q 3 [8197,16495],q 1 [8197,16495],q 1 [8196,20498],q 3 [12288,20491],q 1 [20977],q 4 [16386,20977],q 3 [16386,20977],q 3 [8197,12399],q 1 [8197,16396],q 4 [8197,16396],q 3 [8197,16396],q 3 [16395,21237],q 1 [16395,21237],q 2 [16395,21237],q 0 [16395,21237],q 1 [16388,20492],q 0 [16388],q 1 [16389,20485],q 1 [8197,20492],q 4 [8197,20492],q 3 [8197,20492],q 1 [8197,20496],q 4 [8197,20496],q 3 [8197,20496],q 3 [20496],q 1 [8197,20497],q 4 [8197,20497],q 3 [8197,20497],q 9 [20488],q 0 [20488,16427],q 4 [16395,4853],q 1 [8197,20498],q 0 [20480,8197],q 3 [20499],q 1 [12296,17903],q 0 [17903],q 3 [12299,20487],q 1 [12299,20487],q 4 [12299,4881],q 1 [20486,16396],q 3 [12299,4881],q 3 [12299,17168],q 2 [12299,17168],q 0 [17168],q 6 [17168],q 3 [12299,17169],q 1 [12299,17169],q 2 [12299,17169],q 0 [17169],q 0 [16390,21929],q 3 [12299,21266],q 1 [20485,135185],q 4 [20485,135185],q 1 [22177],q 4 [22177],q 3 [4096,22177],q 0 [4096,22177],q 3 [12299,21267],q 1 [12299,21267],q 0 [21267],q 3 [12299,16391],q 1 [12299,16391],q 2 [16391],q 3 [12299,20485],q 4 [12299,20498],q 3 [16393],q 3 [12299,16393],q 1 [12299,16393],q 2 [16393],q 2 [12299,16393],q 3 [16395],q 3 [12299,16395],q 1 [12299,16395],q 2 [12299,16395],q 3 [20480],q 3 [20480,12299],q 3 [12299,20491],q 1 [12299,20491],q 17 [20491],q 3 [12299,20496],q 1 [12299,20496],q 2 [12299,20496],q 3 [16392,16903],q 1 [16392,16903],q 2 [16392,16903],q 3 [16393,20491],q 1 [16393,20491],q 2 [16393,20491],q 9 [12807],q 1 [16392,12807],q 3 [16389,20491],q 1 [16389,20491],q 2 [16389,20491],q 7 [1150988],q 4 [16389,1150988],q 1 [16389,20492],q 4 [16389,20492],q 15 [16389],q 0 [16389,20498],q 0 [16394],q 4 [16390,16391],q 2 [16390,16391],q 0 [16390],q 8 [16388],q 1 [16388],q 1 [16388,20494],q 6 [16388],q 8 [16390],q 6 [16390],q 1 [13859],q 9 [13495],q 4 [16389]]
def B_22_3 : BT (List (List Nat)) := BT.empty
lemma B_22_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 3 xs.toFinset) B_22_3 := .empty
def U_22_4 : List Nat := [0]
def P_22_4 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_4
def N_22_4 : List NodeSpec := [([9,0,1,3,12],[0],[]),([9,0,10,3,13],[],[]),([17,0,3,19,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_4 : checkNodesBT W_22 g_22 F_22 P_22_4 A_22 B_22_3 4 N_22_4 = true := by decide +kernel
def B_22_4 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_4
set_option maxRecDepth 500000 in
lemma B_22_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 4 xs.toFinset) B_22_4 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_3_ok C_22_4
def U_22_5 : List Nat := (r 1 33)
def P_22_5 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_5
def N_22_5 : List NodeSpec := [([22,0,24,3,4,25],[1],[]),([9,0,2,3,13,5],[],[0]),([9,0,1,10,11,3],(r 2 4),[0]),([26,9,0,1,10,3],[2],[]),([30,0,3,32,4,33],[6],[]),([0,3,32,36,4,33],[7],[1]),([0,3,35,36,4,33],[7],[1]),([37,1,3,18,4,6],[],[]),([38,0,2,39,32,33],[8],[]),([14,0,1,40,3,4],[],[]),([0,1,42,3,44,4],[9],[]),([15,14,0,1,20,7],[10,11],[]),([14,0,1,3,18,4],(r 12 4),[]),([17,0,1,3,4,6],[],[]),([0,1,45,46,7,6],[16],[]),([49,47,0,20,3,4],[17],[]),([38,47,0,51,2,3],[],[]),([52,0,1,54,3],(r 18 5),[]),([38,50,47,0,2,20],[11,23],[]),([55,47,0,2,3,4],[],[]),([30,47,0,20,3,4],[24],[]),([56,15,14,0,1,20],[10,11,25],[]),([0,1,3,58,46,6],[16],[]),([56,14,0,1,20,45],[11,25],[]),([15,52,14,0,1,20],[10,11,25],[]),([38,59,47,0,2,3],[],[]),([0,1,3,46,60,6],[16],[]),([66,0,1,2,3,5],[26],[]),([17,0,1,3,18,4],[20,27,28],[0]),([17,0,1,3,46,7],[],[]),([0,27,3,67,4,25],[29],[]),([14,0,1,20,3,68],[11,25],[]),([14,0,1,20,69,3],[10],[]),([56,70,14,0,1,3],[30],[]),([56,14,0,1,71,3],[31],[]),([76,0,1,2,3,4],[32],[]),([17,14,0,1,3,4],[],[]),([38,47,0,2,20,39],[11,33],[]),([52,14,0,1,20,45],[11,25],[]),([55,0,2,3,35,4],[],[]),([17,0,1,45,46,4],[],[]),([0,1,3,18,4,6],[],[]),([14,0,1,20,45,7],[11,25],[]),([14,0,1,20,3,58],[10],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_5 : checkNodesBT W_22 g_22 F_22 P_22_5 A_22 B_22_4 5 N_22_5 = true := by decide +kernel
def B_22_5 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_5
set_option maxRecDepth 500000 in
lemma B_22_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 5 xs.toFinset) B_22_5 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_4_ok C_22_5
def U_22_6 : List Nat := ([2,4,5]++r 8 9++[18,20,22,23,25,27,28]++r 33 214)
def P_22_6 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_6
def N_22_6 : List NodeSpec := [([79,80,1,2,3,4,5],[],[]),([83,0,1,20,3,4,5],[34,35],[]),e6 [86] [9,36],([23,0,1,20,3,4,87],[37],[]),([22,0,1,3,88,4,5],[38],[]),([22,0,24,20,3,4,5],[39,40],[0]),e6 [55] [],([0,1,2,90,3,4,89],[36],[]),([0,1,3,84,4,6,25],(r 41 4),[]),([9,0,1,2,11,3,5],([5,11]++r 45 4),[0]),([0,94,93,2,3,4,5],[49],[]),([26,9,0,1,2,3,5],[45],[0]),([0,1,2,96,97,98,5],[50,51,52],[]),([0,1,100,3,84,4,25],[42,44,53],[1]),([38,30,0,1,20,3,5],[54],[]),([55,30,0,1,3,4,5],[],[]),([101,102,0,2,20,3,4],[55],[]),([103,0,104,20,3,4,5],[56],[]),([55,105,1,2,3,4,5],[],[]),([30,105,1,20,3,4,5],[57],[]),([55,102,0,2,3,4,5],[58],[]),([101,55,0,1,2,3,4],[59],[]),([38,0,2,3,21,33,25],[44,60,61,62],[]),([22,0,2,3,4,33,25],[63],[]),([106,0,2,3,21,4,25],[64],[]),([107,106,0,1,3,4,5],[],[]),([70,106,0,1,3,4,5],[],[]),([41,0,1,3,44,4,6],[9],[0]),([108,106,0,1,3,7,5],[],[]),([106,0,1,3,4,109,5],[],[]),([0,1,2,20,3,110,5],[11,65,66],[]),e6 [112] [36],([106,0,1,111,3,4,5],[14,67,68],[]),([0,1,3,114,4,6],[69,70,71],[]),([9,0,1,10,3,7],[2,4,5,72,73,74],[]),([9,0,1,10,3],[2,4,5],[0]),([115,0,1,3,7],[4,11,75,76,77],[]),([0,1,2,20,39,97,5],[11,14,78],[]),([38,59,0,31,2,3,33],[79],[0]),([0,31,2,20,3,117,33],[80],[1]),([0,31,2,20,39,97,33],[11,80,81],[1]),([118,0,1,20,3,4,6],(r 82 4),[0]),([55,0,31,2,3,4,33],[36],[0,1]),([108,52,14,0,1,3],[10,22],[]),([38,0,120,2,3],([11]++r 86 4),[]),([52,14,0,1,20,3],[10,11,18,20,25,90],[0]),e6 [122] [],([14,0,1,123,3,4],[10,12,13,25,28,90,91],[]),([15,14,0,1,20,4],[10,11,25,28,92],[0]),([15,52,14,0,1,3,4],[10,11,20,28,90],[0]),([125,14,0,1,3,4],[10,15,25,28,93,94],[]),([106,0,1,20,45,4,5],[11],[]),([38,0,31,2,20,39,33],[11,80,81],[0]),([15,14,0,1,71,3,4],[10,20,28,95],[]),([126,14,0,1,3,4,6],[10],[]),([14,0,1,71,3,4,6],[10,20,96],[1]),([14,128,0,1,3,4],(r 10 4++[97]),[]),([107,14,0,1,3,4],[10,22,28],[]),([132,131,0,1,3,5],(r 98 7),[]),([133,0,1,134,3],[11,98,105,106,107],[]),([14,0,1,135,4],[11,18,28,108],[]),([136,0,1,3,137],[11,98,107,109,110],[]),([0,1,2,140,3,139,141],(r 111 5),[]),([52,14,0,1,3,4],[10,12,13,15,20,25,28,116],[]),e6 [144] [],([126,14,0,1,3,4],[10,12,13,15,117,118],[]),([145,136,131,0,1,3,5],[11,98,119,120,121],[]),([146,55,0,27,3,4,5],[9],[]),([70,14,0,1,3,4],[11,12,13,20,25,122,123],[0]),([0,1,2,20,147,148,5],[11,14,65,124],[]),([30,0,1,20,3,4,5],[125],[]),([14,0,1,20,3,149,4],[18,20,25,28,126,127,128],[0,1]),([150,106,0,1,3,4,5],[],[]),([151,106,0,1,3,4,5],[],[]),([153,14,0,1,3,4],[13,15,18,129,130],[]),([14,0,1,154,4],[11,18,28,131],[]),([108,106,0,1,3,148,5],[],[]),([55,47,0,2,20,3,4],[11,23,33,132],[]),([106,0,1,3,4,155,5],[],[]),([70,14,0,1,3,4,6],[10,20,25],[1]),([22,23,0,1,3,4,25],[133],[0]),([156,41,0,1,2,3,4],[134],[]),([56,15,14,0,1,3,4],[10,11,20,28,135],[0]),([92,0,2,157,3,4,33],[36],[1]),e6 [159] [136],([14,160,1,3,4],[10,11,13,137],[]),([162,14,0,1,3,4],(r 10 4++[15,20,22,25,28,138,139]),[]),([55,0,163,2,3,4,5],[36,140],[]),([156,164,0,1,2,3,4],[141],[0]),([14,0,1,165,3,4],[12,13,20,25,28,135,142],[]),e6 [167] [44,143,144],([0,1,168,20,3,4,5],[145],[]),([107,14,0,1,3,4,6],[10,25,28,146],[]),([170,47,0,3,4],[11,147,148],[]),([171,172,0,1,2,3,5],[149],[0]),([52,14,0,1,20,3,6],[11,25,90,121],[0]),([38,47,0,2,20,3],[11,23,33,148,150,151],[0,1]),([17,14,0,1,3,4,6],[],[0]),([0,1,3,18,4,6],[70,152,153],[0,1]),([173,0,1,2,3,139,141],[115,154],[]),([103,0,1,3,72,4,5],[155],[]),([133,145,131,0,1,3,5],[11,98,120,121,156],[]),([175,131,0,1,3,5],(r 98 4++[120]++r 157 4),[]),([0,27,20,3,67,4,5],[14,36,161,162],[0]),([16,14,0,1,3,4],(r 12 4++[20,163]),[0]),([15,14,0,1,3,4,176],[20,28,164,165,166],[]),([0,27,3,21,4,6,25],[127,167],[0]),([14,0,1,165,3,4,6],[28,135],[]),([55,106,0,27,3,4,5],[9],[]),([0,1,3,84,4,28,25],[42,44,168],[]),([0,27,3,21,4,5,82],[169],[]),([55,0,27,3,84,4,5],[9],[]),([108,14,0,1,3,7,6],[10,22],[]),([106,0,1,121,3,4,5],[14,67,170],[]),([0,1,2,20,177,178,5],[11,171,172,173],[]),([0,1,3,179,4,6,25],[174,175],[]),([0,1,142,180,2,20,5],[11,14,176],[]),([55,0,2,27,3,4,5],[9],[]),([14,0,1,154,3,4],[11,12,13,25,28,177],[]),([106,0,1,20,147,4,5],[11,14],[]),([14,0,1,3,4,181],[10,15,25,28,178,179,180],[]),([14,182,0,1,3,4],[13,15,18,181,182,183],[]),([14,0,1,20,3,7,6],[10,11,25,146],[0]),([106,0,1,20,3,148,5],[11,14],[]),([30,0,31,20,3,4,33],[184,185],[0]),([56,14,0,1,20,3],[10,11,18,20,25,135],[0]),([184,14,0,1,3,4],[10,12,13,15,18,25,28,186,187,188],[]),([17,14,0,1,3,4],[10,12,13,15,20,27,189,190],[]),([17,14,0,1,20,3,4],[10,11,20,25,28,190],[]),([52,0,1,3,53],[18,20,22,107,191,192],[0]),([14,0,1,135,3,4],[11,12,13,20,25,28,193],[]),([16,14,0,1,3,4,6],(r 12 4),[0]),([15,14,0,1,20,4,6],[10,11,25],[0,1]),e6 [185] [9,49,143,144],([15,14,0,1,3,7,4],[10,20,28,146],[0]),([14,0,1,123,3,4,6],[25,28,90],[]),([108,52,14,0,1,3,6],[10,22],[]),([14,0,1,20,3,4,82],[10,126,194,195,196],[1]),([52,14,0,1,45,3,4],[10,11,20,28,90],[0]),([187,0,1,2,20,3,4],[197,198],[]),([14,0,1,3,4,109,6],[10],[]),([56,14,0,1,45,3,4],[10,11,28,135],[0]),([0,1,20,3,149,4,6],[20,28,128],[0]),([17,0,1,3,4,6],[20,27,189,190],[0]),([55,0,1,188,3,4,5],[],[]),([55,0,1,2,157,3,4],[49],[]),([106,0,1,20,3,7,5],[11],[]),([0,1,27,20,45,7,5],[11,199,200,201],[]),([17,0,1,20,3,4,6],[11,20,28,190],[]),([0,1,2,3,64,65,5],[202],[0]),([14,0,1,111,3,4],(r 12 4++[20,203,204]),[0]),([0,1,3,67,84,4,5],[14,205],[]),([14,0,1,3,7,4],[10,12,13,15,20,25,28,206,207],[]),([14,0,1,113,3,4],[12,13,20,28,96,208,209],[]),([14,0,1,111,3,4,6],([9]++r 12 4),[0,1]),([55,47,0,2,3,4],([23,132,150]++r 210 5),[]),([38,0,2,20,3,32,33],[8,215],[1]),([14,0,1,20,45,4,6],[10,11,25],[0,1]),([0,1,45,46,4,6],[16,70,216,217],[0,1]),([14,0,1,20,3,7],[10,11,18,20,146],[0]),([17,166,0,1,3,4,6],[9,218],[1]),([14,0,1,71,3,4],[10,12,13,20,25,95,219],[0]),([70,14,0,1,45,3,4],[10,25,28],[]),([14,191,0,1,3,4],[10,12,13,15,25,28,220,221,222],[]),([14,0,1,3,4,68],(r 10 4++[25,28]),[0]),([38,47,0,2,20,3,33],[11,33,150,151],[0]),([55,0,2,3,192,4,5],[36],[]),([56,0,1,161,3],[10,11,18,107],[]),([14,0,1,3,4,109],[10,12,13,15,223,224],[]),([0,1,3,21,194,4,25],[225],[]),([0,1,3,46,7,6],[73,226,227],[0]),([55,0,1,2,3,193,4],[49],[]),([38,50,47,0,2,3,4],[23,96,150,151,228],[0]),([108,14,0,1,3,7],[10,22],[]),([0,1,2,3,67,4,25],[44,175,229],[0]),([14,0,1,45,3,4,195],[20,28,165,230],[]),([14,0,1,45,3,7,4],[10,20,28,146],[0]),([38,47,0,2,39,3,4],[23,150,151,228],[0]),([0,1,2,3,73,4,75],[231],[0]),([14,0,1,20,45,4],[10,11,25,28,92],[0]),([14,0,1,3,198,4],[11,12,13,232],[]),([199,47,0,3,4],[11,148,233],[]),([14,0,1,113,3,4,6],[20,28,96,208],[]),([14,0,1,200,3,4],[11,22,25,28,234],[]),([0,1,3,18,46,4,6],[70,73,127,226,235,236],[0,1]),([0,1,3,46,4,6,82],[70,73,217,235,237,238,239],[0,1]),([56,14,0,1,20,3,6],[11,25,135],[0]),([17,0,1,3,46,4,6],[16,217,240,241],[0]),([38,0,2,3,32,33],[8,215,242,243,244],[0,1]),([55,47,0,2,3,4,33],[150,210],[]),([55,0,2,3,32,4,33],[8,36,210,215,242,245,246],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_6 : checkNodesBT W_22 g_22 F_22 P_22_6 A_22 B_22_5 6 N_22_6 = true := by decide +kernel
def B_22_6 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_6
set_option maxRecDepth 500000 in
lemma B_22_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 6 xs.toFinset) B_22_6 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_5_ok C_22_6
def U_22_7 : List Nat := ([4,5]++r 9 8++[18,20,22,23,25,28,33,36,39]++r 42 6++r 49 4++[54,60,61,65,66,67,70,73,78,80,81,82,88,90,96]++r 98 4++r 112 4++r 119 4++[124,126,127,135,143,144,146,148,151,156,158,161,165,166,169,170,172,173,175,176,200,201]++r 209 4++[214,223,226,234,235,242]++r 246 641)
def P_22_7 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_7
def N_22_7_0 : List NodeSpec := [e6 [203,201] [36,42,247,248,249],([79,1,2,3,77,4,5],([65]++r 250 5),[0]),e6 [205,206] [44,65,255,256,257],([38,0,1,93,2,20,3,5],[14,44,258,259,260],[]),u6 [207,20] ([42,44,65,66,255]++r 261 5),([30,0,1,20,3,4,5,25],[266,267,268],[]),([0,163,2,20,3,4,5,34],(r 269 4),[0,1]),([208,0,2,20,3,4,5,25],[273,274,275],[]),([92,0,93,2,3,4,5],([44,49]++r 276 5),[0]),([0,1,209,20,3,84,4,5],[42,44,175,281,282,283],[]),([101,211,0,1,2,20,3,4],[11,284,285],[1]),([103,0,1,20,3,84,4,5],[281,286,287],[1]),([103,0,1,3,84,4,5,25],[11,44,281,288,289],[]),e6 [101,84] [14,65,281,290],([22,0,1,3,21,84,4,5],[42,44,291],[]),([0,1,212,2,20,3,4,25],[42,44,175,292],[]),([23,0,1,2,3,21,4,25],[11,175,293],[0,1]),e6 [88,84] [11,175,281,294,295,296],e6 [214,20] [49,65,297,298],u6 [88,21] [14,299,300,301],e6 [215,24] [255],([0,1,24,2,20,3,4,25],[42,44,49,264,302],[1]),e6 [144,20] [11,66,255,303],e6 [216,20] [11,14,279,304,305,306],e6 [144,24] [44,49,307],e6 [144] [36,49,143,144,255,303,308,309],([0,1,100,20,3,84,4,5],[42,44,310,311,312],[0,1]),([108,0,1,180,24,2,3,5],[247,313],[]),([0,1,180,24,2,20,3,5],[11,14,176,255,314],[0]),e6 [218,100] [42,66,255,315],u6 [142,180] [42,44,176,255,313],u6 [143,24] [49,65,307,316,317],([116,102,0,2,20,3,4,5],[14,318,319,320],[]),([116,0,2,3,21,4,5,25],[44,175,299,321],[1]),([0,1,20,3,219,84,4,5],[42,44,281,322],[]),e6 [220,33] [255,323],([38,0,1,2,20,3,5,33],([11,14,44]++r 324 4),[]),([0,1,2,20,39,4,5,33],[11,14,66,326,328,329],[0]),u6 [221,33] ([36,49,65]++r 330 4),([0,1,20,3,84,4,5,6],[9,42,44,311,334],[0]),e6 [24,223] [42,44,96,307,335],([9,0,1,2,3,7,5],([11,45,46,47]++r 336 4),[0]),([9,0,1,2,3,5],[5,11,45,47],[0]),([0,1,2,96,3,97,5],[11,50,52,340],[]),([0,1,2,96,97,5],([11,50,51]++r 340 4),[0]),u6 [39,97] [42,44,78,255,329],e6 [225] [11,143,144,344],e6 [226] [11,143,144,255,345,346],([38,59,0,1,2,3,5,33],[44,255,347],[0]),([228,1,2,39,3,4,5,33],[348,349],[]),([0,1,2,20,3,117,5,33],[61,350,351,352],[0]),([38,0,1,2,20,39,5,33],[11,14,353,354,355],[0]),a6 [206,229] ([14,44,65,255]++r 356 4) [1],([0,1,2,20,39,97,5,33],[11,14,353,360,361,362],[0]),u6 [146,55] [9,65,214],e6 [55,93] [49,210],([30,0,1,20,3,4,5,33],[11,14,54,363,364],[0]),([101,0,1,2,20,3,4,34],[66,365],[0]),e6 [101,20] [11,36,365,366],([38,0,1,2,20,3,5,34],([121]++r 367 4),[0]),u6 [55,34] [367,369,371,372],([30,0,1,20,3,4,5,34],[54,364,373,374],[0]),e6 [103,20] [49,65,82,375],([105,1,2,20,3,4,5,34],[262,376,377],[0]),u6 [55] [9,36,49,65,143,144,255,378,379],([38,41,0,1,2,20,3,33],[11,14,44,61,325,380],[]),([41,55,0,1,2,3,4,33],[36,44,49,210],[0]),([0,1,2,157,20,3,4,33],[14,175,299,381],[0]),u6 [55,25] [175,210,288,318,382],([103,0,1,20,3,4,5,6],[11,383,384],[1]),([38,0,1,2,20,3,33,25],[11,44,61,325,351,385],[0]),u6 [55,33] [36,49,378],([55,0,1,2,3,4,33,25],[44,175,210,318,351,372,382,385],[]),([0,1,3,230,4,5,33],([44,65]++r 386 4),[]),([103,0,1,20,3,4,6,25],[175,281,383,384],[]),e6 [231,20] [11,42,44,65,390,391],u6 [20,67] [14,175,392,393,394],e6 [67,6] [14,161],e6 [67] [14,44,144,161,392,394,395],e6 [55,232] [65,214],([38,92,0,2,20,3,5,33],[11,14,44,61,325,396],[]),e6 [70,6] [44,66,255,326,397,398],([92,55,0,2,3,4,5,33],[44,49,210],[0]),([92,41,0,2,3,4,33],([36,44,49,276,279]++r 399 4),[0,1]),([0,1,20,3,44,4,5,6],[11,96,281,403],[0,1]),([0,1,2,3,21,4,33,25],[42,44,60,299],[]),([38,0,2,20,3,21,5,33],[14,44,61,351,404,405],[0]),u6 [20,34] [255,261,262,373,406],([0,1,20,3,186,84,4,6],[281,407,408],[]),([55,0,2,3,21,4,5,33],[36,44,49,299,351,372,404,409,410,411],[]),([0,1,2,20,3,4,33,25],[42,44,49,318,412],[1]),([0,1,3,84,4,5,6,25],[42,44,175,413],[]),([0,1,3,84,4,6,25],([42,44,175,281,336]++r 413 4),[0,1]),([22,0,2,20,3,4,5,33],[65,127,417],[0]),e6 [106,233] [11,44,65],e6 [107,234] [42,247,255,418,419],([106,0,1,3,97,4,235,5],[44,420],[]),e6 [70,234] [11,66,421,422],([108,106,0,1,2,3,97,5],[247,350],[]),e6 [106,220] [9,65,423,424],([106,0,1,2,20,3,97,5],[11,14,425],[]),([0,1,27,3,84,4,5,25],[11,65,127,426,427,428],[0,1]),([22,0,27,20,3,21,4,5],[169,429,430],[]),([101,0,1,2,3,21,4,25],[14,44,175,431],[]),([0,1,2,20,3,148,5,28],[11,14,65,124,255,432],[0,1]),([0,1,2,20,147,4,5,28],[11,14,65,66,326,433],[0,1]),e6 [106,236] [9,65,424,434],e6 [39,237] [42,435,436,437],([196,106,0,1,3,97,4,5],[361,438,439],[]),e6 [24,238] [11,42,165],([0,1,27,20,3,7,5,6],[11,201,440,441],[0]),([145,131,0,1,3,5],[11,98,99,101,120,121,158,326,442,443],[0]),([101,0,1,2,20,3,4,25],[175,444,445],[0]),([14,0,1,3,7,4],[11,18,20,22,146,446,447],[0]),([55,0,2,27,3,4,5,33],[65,67,214,424,448],[0]),([107,0,1,27,3,4,5,6],[449,450],[]),([0,1,2,3,193,21,4,25],[11,14,42,44,451,452],[0]),([0,1,27,111,3,4,5,6],([14,67,418]++r 453 4),[1]),a6 [220,28] [121] [1],e6 [122,20] [11,66,255,457],([30,0,1,20,3,4,5],[11,14,54,65,363,458],[]),e6 [196,236] [42,438,459],e6 [239,20] [14,42,44,65,66,255,279,460],e6 [241,240] [42,66,461],e6 [242] [9,36,66,143,462,463,464],([106,0,1,243,3,4,5],[439,465],[]),([108,0,31,2,3,97,33],[80,466,467,468],[1]),([106,0,1,39,3,244,4,5],[42,469,470],[]),([55,0,2,27,3,4,5],[9,214,448],[0]),e6 [245,7] [14,42,121,471,472,473],e6 [122,28] [14,44,65,67,474,475],([0,1,20,3,179,4,5,6],[65,67,175,476],[0]),([0,1,2,3,21,4,6,25],[11,42,44,477,478,479],[0,1]),e6 [247] ([11]++r 480 6),u6 [63,65] [44,165,255,485,486,487],([0,1,2,20,3,97,5,33],[11,14,78,255,324,488],[0]),([70,0,1,27,3,4,5,6],[122,489],[]),u6 [64,63] [44,112,165,255,485,486,490,491],([0,1,27,113,3,4,5,6],[11,14,67,209,418,492,493],[]),e6 [248,20] [9,11,42,44,66,255,494,495,496],u6 [156,20] [11,49,497,498,499],a6 [72,25] [11,175,281,299,500,501] [0,1],e6 [30,20] [54,65,502],([0,1,27,20,3,4,5,82],[503,504],[0,1]),([38,106,0,1,2,20,3,5],[11,14,425],[]),u6 [156,72] [11,49,498],u6 [20,249] [66,255,261,262,505],([14,0,1,127,3,4],(r 10 4++[25,65]),[0]),([0,31,2,39,3,4,227,33],[242,246,348,506,507],[1]),([103,0,1,20,3,4,5,82],[66,375],[0,1]),([190,57,0,1,10,3],[4,11,508],[0,1]),a6 [72,75] ([11,49]++r 509 4) [0,1],([30,0,1,3,4,5],[11,54,458,513,514,515],[]),([0,1,2,20,3,4,74,25],[42,44,112,281,299,516,517],[]),([0,1,2,20,3,97,5,28],[11,14,121,340,361,518],[1]),([106,0,1,250,3,4,5],([11]++r 519 4),[]),e6 [251] [36,42,49,66,255,317,523,524,525],u6 [173,139] [42,66,526,527],([0,31,2,39,3,97,4,33],[11,80,242,246,467],[0,1]),e6 [113,6] [9,11,42,44,96,528,529],([0,1,27,45,3,7,4,5],[200,530,531],[0]),([0,163,2,20,3,4,33,25],[175,532,533,534],[]),e6 [253,28] [11,14,42,44,65,474,475,535],([108,0,1,2,3,148,5,28],[247,433],[0,1]),([0,1,27,3,4,109,5,6],[223,536],[]),([0,1,2,3,255,4,74],[9,36,172,537],[]),u6 [41,72] [9,11,49,494,538],u6 [177,178] [11,42,44,172,255,539,540,541],u6 [21,82] ([14,169]++r 542 4),e6 [256,242] [9,65,463],([124,14,0,1,3,4],[10,11,12,25,165,546,547],[0]),([108,106,0,1,3,4,5,6],[465,548,549,550],[]),([236,0,31,2,3,4,33],([14,36,80,81,246]++r 551 7),[1]),e6 [257,74] [11,44,173,326,558],e6 [259,74] [11,42,44,112,559,560],([41,0,1,2,20,3,4,28],[11,14,42,44,65,279,561],[]),([38,0,1,2,20,3,5,89],[11,44,562,563,564],[]),([108,106,0,27,3,4,5,33],[565,566],[]),([14,152,0,1,3,4],[11,12,13,18,25,567],[0]),a6 [22,25] [11,65,175,264,288,426,568] [0,1],([0,1,2,3,139,141],[113,114,115,569,570],[0]),e6 [261] [36,49,143,144,255,571,572],e6 [262,28] [42,247,573,574,575],e6 [263,20] [14,49,65,264,576,577],e6 [236,264] [42,66,348,459,552,578],([106,0,1,250,3,4,5,33],[11,520,579],[]),([101,0,1,2,20,3,4,33],[11,299,580,581],[0]),e6 [267,266] [144,582],([0,1,20,3,21,194,4,5],[410,583,584,585],[0]),e6 [267] [9,36,144,255,582,586,587,588],e6 [268,236] [42,66,459],([115,0,1,3,4,6],[4,9,11],[0]),e6 [269] [36,42,66,255,589,590,591],([254,0,1,2,177,3,4,74],[592,593],[]),e6 [262,24] [42,247,574,594],([108,14,0,1,3,4,6],(r 10 4++[18,25,595]),[0]),([0,1,2,20,3,4,28,25],[42,44,264,596,597],[0,1]),e6 [270] ([9,36,42,66,144,255]++r 598 4),([106,0,1,147,3,4,5],[11,65,170,602],[0]),e6 [271] [36,66,143,590,603,604]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7_0 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7_0 = true := by decide +kernel
def N_22_7_1 : List NodeSpec := [([108,0,1,27,3,7,5,6],[200,605,606],[]),([103,0,61,1,20,3,4,5],[43,607,608],[0]),e6 [106,221] [65,434,609],e6 [242,272] [14,65,463],e6 [273,33] [348,350,610,611],u6 [20,87] [65,612,613],([108,106,0,1,3,4,5,28],[11,66,595,602,614],[0]),([274,102,0,2,20,3,4,5],[14,615,616],[1]),e6 [39,235] [42,65,438,617],e6 [236,275] [14,65,554],([14,0,1,45,3,4,6],(r 10 4++[25,65]),[0,1]),([0,31,2,20,39,4,33],[11,80,81,246,328,618],[0,1]),e6 [276,266] [255],([107,0,1,10,3,4,6],([70,73,450,508]++r 619 5),[0]),([52,14,0,1,3,4,6],(r 10 4++[15,18,25,90,121,624,625]),[0]),([190,14,0,1,3,4],[11,12,18,20,25,234,626,627],[0]),([0,31,2,20,3,97,33],[11,81,242,467,488,557],[0,1]),([41,0,1,2,3,4,89],[36,44,279,400,628,629],[0]),([0,1,2,20,3,193,4,34],[630,631],[0,1]),a6 [151,28] [44,66,255,326,632] [0,1],e6 [277,74] [42,66,255,540,633],([108,0,1,2,3,178,5,74],[172,247,634],[]),e6 [279,20] [11,49,65,635,636],([30,0,1,20,3,21,4,5],[637,638,639],[]),([106,0,1,3,148,4,5],[11,65,170,475],[0]),e6 [280] [9,36,66,143,640,641,642],([15,14,0,1,3,4,6],(r 10 4++[15,25,65,643]),[0,1]),([14,152,0,1,3,4,6],(r 10 4++[18,25,65,546,567]),[0]),([262,0,1,27,3,4,5,6],[644,645],[]),e6 [282,6] [66,255,646,647],e6 [280,74] [144,641,648],([0,1,3,284,77,4,5],(r 649 6),[]),e6 [55,20] [11,66,255,655],([242,0,31,2,3,4,33],[14,36,81,462,463,553,557,656,657],[1]),([101,0,2,27,20,3,4,5],[11,14,281,290,658,659],[]),([174,131,0,1,3,5],[11,99,100,121,158,660],[0]),u6 [147,148] [42,44,124,255,433],e6 [285,74] [255,661],e6 [106,242] [9,65,424,434,662],e6 [286] [36,49,66,143,317,663,664,665],e6 [236,6] [9,14,65,376,666],([287,14,0,1,3,4],[12,13,15,18,25,65,546,667],[]),([14,183,0,1,3,4,6],[11,12,13,18,25,65,165,546,668],[0]),([0,1,27,20,3,4,6,25],[264,669,670],[0]),e6 [236,39] [42,144,459],([0,31,2,3,4,220,33],[80,323,553,555,656,671,672],[1]),([14,183,0,1,3,4],[11,12,13,18,165,668],[0]),([14,0,1,20,3,4],[11,18,20,25,126,127],[0]),e6 [288,20] [43,49,673],u6 [172,63] [44,255,674],([14,0,1,20,3,4,6],[11,12,13,18,20,25,126,127],[0,1]),([23,0,1,3,4,290],([11]++r 675 6),[]),e6 [291,204] [357],([0,1,27,238,3,4,5,6],[165,681,682],[]),([222,0,1,24,2,20,3,5],[11,14,44,314,326,335],[]),([0,1,27,20,45,4,5,6],[11,200,683,684],[0]),u6 [55,84] [65,281],([38,47,0,2,3,4],[11,23,33,36,148,151,211,212,685],[0,1]),e6 [292,236] [9,65,554],e6 [122,33] [14,36,44,67,686,687],([106,0,1,2,20,39,4,5],[11,14,423],[]),([106,0,1,20,3,4,5,28],[11,14,65,66,127,602,688],[0]),([0,1,209,27,20,3,4,5],[11,14,279,373,689],[]),e6 [106,238] [11,42,65,690],([0,104,2,20,3,4,5,82],[691,692,693],[0,1]),([0,1,2,20,177,4,5,74],[11,66,172,326,694],[0]),u6 [158,74] [9,36,112,601,695,696],([0,1,2,20,39,97,5],[11,14,354,360,361,697,698],[1]),e6 [294,7] [44,121,416,699],([41,0,1,2,20,3,4,74],[11,42,44,700,701],[]),e6 [296,100] [44,66,255,326,702],u6 [140,139] [42,66,112,248,527,703,704],u6 [20,75] [255,262,705,706,707],e6 [159] ([9,36,49,143,144,255]++r 708 4),([22,0,1,20,3,84,4,5],[42,44,281,712,713,714],[]),e6 [297,74] [255,715],([0,1,3,21,84,4,5,6],[14,42,44,65,716],[0]),e6 [159,20] [11,66,255,710,711],([14,0,1,3,7,4,6],(r 10 4++[18,25,146,446,717]),[0]),([38,0,2,27,20,3,5,33],([11]++r 718 4),[]),([133,189,131,0,1,3,5],([11,121]++r 722 9),[]),([0,27,20,3,21,4,5,6],[14,418,731],[0,1]),([0,1,2,20,3,178,5,74],[11,173,255,540,732],[0]),([22,0,1,20,3,179,4,5],[66,127,733,734],[]),e6 [103,21] [14,65,169,264,735],([14,0,1,3,4,8],[11,12,18,25,626,736],[0,1]),a6 [121,28] [14,65,67,474,475,590,737] [0,1],e6 [298,20] [11,49,65,738,739],([106,0,1,45,3,4,5],[424,439,519,521,550,740],[]),([14,299,0,1,3,4],(r 10 4++[18,25,165,546,741]),[]),([0,1,2,3,300,4,266],[742,743,744],[]),e6 [302,45] [42,44,745],([55,0,31,2,3,4,33],[36,80,210,214,242,553,555,656,746,747],[0,1]),e6 [270,74] [144,600,748],([0,1,2,3,303,141],[113,749,750,751],[]),e6 [305] [11,44,49,143,144,255,752,753,754],([0,1,20,3,84,4,5,28],[42,44,65,127,755,756],[0]),e6 [196,307] [44,247,757],e6 [309] [44,143,144,255,304,758,759],([124,14,0,1,3,4,6],[10,11,25,65,165,546,547],[0]),e6 [238,28] [11,42,165,255,760],([189,106,0,1,39,3,4,5],[121,362,521],[]),e6 [309,6] [9,44,49,758,761],e6 [310,33] [44,762],([41,0,1,27,20,3,4,6],[11,14,127,279,763],[]),([0,31,2,3,311,4,33],[11,555,656,764,765],[1]),([199,0,31,3,4,33],([11,557]++r 766 4),[0]),([106,0,1,2,20,3,4,25],[44,264,521,770,771],[0]),e6 [38,312] [44,65,255,351],([38,196,106,0,1,3,4,5],[355,438,439],[]),([70,0,1,10,45,3,4,6],[70,508,622,772],[0]),e6 [313,201] [42,49,773],u6 [55,106] [44,65,214],([131,0,1,314,3,5],[11,98,121,158,774,775],[]),([131,0,1,3,5,137],[11,98,100,121,326,776,777,778],[0]),([131,0,1,134,3,5],[11,98,121,158,326,779,780],[0]),e6 [315,20] [14,42,44,66,255,781,782],([0,31,2,3,4,237,33],([14,80,81,246,553]++r 783 4),[1]),([131,0,1,62,3,5],[98,121,158,651,787],[0]),e6 [146,20] [11,521,788,789],e6 [39,240] [42,65,461,790],([133,131,0,1,3,5],[11,98,99,101,121,156,158,326,727,730],[0]),([0,1,3,316,130,5],[651,791,792,793],[]),e6 [318,317] [14,42,66,794,795,796],a6 [179,25] [11,175,797] [0,1],([14,319,0,1,3,4],[12,13,18,65,626,798],[]),e6 [291] [143,144,357,799,800,801],([136,131,0,1,3,5],[11,98,99,100,119,121,158,326,802,803],[0]),([131,0,1,3,5,320],[121,247,804,805],[]),([106,0,27,20,3,4,5,33],[11,65,373,566],[0]),([106,0,1,243,3,4,5,33],[439,465,806,807],[]),e6 [122] [36,49,143,144,255,457,687,808],a6 [55,6] [9,65,214,448] [1],([197,14,0,1,3,4],([10,11,12,25,65,626]++r 809 5),[0]),([15,14,0,1,3,4],(r 10 4++[15,25,28,65,165,166,643,811]),[0]),e6 [55,89] [49,210],([52,14,0,1,3,4],(r 10 4++[15,18,20,22,25,90,624,625]),[0]),([22,23,0,1,20,3,4,5],[39,814],[0]),u6 [164,72] [11,49,815],([14,0,1,3,4,53],[11,12,18,25,816],[0,1]),([0,1,142,24,2,20,4,5],[11,14,66,313,326],[0]),e6 [261,33] [36,42,49,571],u6 [110] [11,42,66,143,144,255,817,818],([56,14,0,1,3,4],(r 10 4++[18,25,135,819]),[0]),e6 [321,20] [11,49,311,820,821],e6 [106,237] [9,65,423,424,822],([14,0,1,161,3,4],[11,18,20,25,823,824],[0]),e6 [323,324] [9,42,65,825,826],a6 [221,28] ([65,424]++r 827 4) [1],([101,0,2,20,3,21,4,33],[175,299,580,581],[]),([108,14,0,1,3,4],(r 10 4++[18,25,595]),[0]),([56,14,0,1,3,4,6],(r 10 4++[18,25,135]),[0]),([14,0,1,45,3,4],[10,13,25,28,65,165,740,811],[0]),([38,47,0,2,3,4,33],[11,23,33,36,148,151,211,212],[0,1]),([0,1,3,46,4,6],[16,73,127,226,235],[0,1]),([23,0,1,2,3,84,4,25],[44,175,281,831],[0]),([0,31,2,221,3,4,33],[65,242,332,553,555,656,832],[0,1]),u6 [171,63] [44,255,833],([0,31,2,20,3,4,33,34],([80,242,246]++r 834 5),[0,1]),([0,1,2,20,3,4,89,25],[42,44,175,299,839,840],[]),([258,0,1,2,20,3,5,74],[11,44,173,326,560,841],[]),([55,0,31,2,20,3,4,33],[11,80,81,210,242,246,299,746],[0,1]),([131,0,1,325,3,5],[11,121,247,723,842,843],[]),([38,0,31,2,20,3,33],[11,80,81,242,325,557,844],[0]),([38,0,31,2,39,3,4,33],[11,80,242,246,844],[0]),u6 [73,72] [11,49,281,299,485,509,510,845,846],([0,326,2,3,4,33],[11,14,847],[]),e6 [327,25] [14,175,299,848,849],([70,0,1,10,3,4,6],[73,122,508,619,620,621,772],[0,1]),([0,31,2,3,97,95],[242,468,557,850,851,852],[1]),e6 [328,77] [44,49,650],([0,31,2,96,4,33],[11,557,853],[1]),([0,31,2,329,3,4,33],[11,81,242,555,656,854],[1]),([0,31,2,96,3,4,33],[11,555,557,656,853],[1]),([0,120,2,3,4,33],[11,88,242,855,856],[0]),e6 [236] [9,36,42,66,144,255,331,552,554,857],([0,31,2,3,97,4,33],[11,80,81,242,246,555,656,858],[1]),a6 [20,29] [255,262,859,860] [0,1],e6 [242,6] [9,14,65,376,861],([0,31,2,233,3,4,33],[81,246,555,557,656,844,862,863],[1]),([101,99,0,1,2,20,3,4],[11,299,410,864,865],[]),e6 [330] ([9,36,49,65,255]++r 866 4),e6 [159,74] [44,709,711],([38,0,1,2,20,3,5,28],[11,14,61,355,518],[1]),([0,163,2,3,21,4,5,25],[11,14,42,44,451,870,871],[]),([106,0,1,20,3,4,5,6],[11,14,65,281,439,521,550,872],[]),([106,0,1,3,7,4,5],[424,439,447,465,519,521,873],[]),([108,0,1,2,3,97,5,33],[247,329,466],[]),a6 [55,28] [65,214,424,830] [1],([0,1,2,20,39,4,5,28],[11,14,354,362,438,874],[1]),([108,0,1,2,3,97,5,28],[121],[1]),e6 [39,331] [11],a6 [150,28] [42,66,124,255] [0,1],u6 [70,28] [44,255,438,875],e6 [332,97] [42,44,121,876],e6 [147,97] [42,340,877],u6 [55,21] [299,409,410,411,545],e6 [174,236] [36,42,247,459,578],u6 [107,28] [42,66,878],e6 [113,28] [14,42,418,879,880]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7_1 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7_1 = true := by decide +kernel
def N_22_7_2 : List NodeSpec := [([0,1,20,3,46,4,6],[16,70,73,127,226,235],[0,1]),e6 [20,333] [65,521,881,882],a6 [155,28] [255] [0,1],e6 [106,262] [42,247,424,439],([55,0,2,27,20,3,4,5],[11,214,281,883],[0]),([106,0,2,3,21,4,5],[14,44,127,521,543,884],[]),([252,0,1,2,20,3,5,28],[11,14,44,65,326,432,535],[]),([106,0,2,20,3,21,4,5],[14,44,127,521,884],[0]),([0,1,2,39,3,97,227,5],[42,44,255,340,885],[]),([41,106,0,1,2,20,3,4],[11,14,44,279,521,886],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7_2 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7_2 = true := by decide +kernel
def N_22_7 := N_22_7_0 ++ N_22_7_1 ++ N_22_7_2
def B_22_7 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_7
set_option maxRecDepth 500000 in
lemma B_22_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 7 xs.toFinset) B_22_7 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_22) (raw := r_22) (pspecs := ps_22) (used := U_22_7) S_22_ok
  have hm0 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_6_ok C_22_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_6_ok C_22_7_1
  have hm2 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_6_ok C_22_7_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def U_22_8 : List Nat := ([4,9,11,12,14,25,36,42,43,44]++r 47 4++[52,65,66,67,73,80,81,96,107,112,113,114,121,122,124,127,143,144,158,165,169,170,172,173,175,176,200,201,209,210,214,242,246,247,248]++r 255 4++[261,262,264]++r 276 4++[281,282,290,294,296,299,304,307,311,313,314,316,317,318]++r 323 11++[335,336,337,339,348,350,351]++r 353 7++[361,362,367,368,369,372,373,376,380,383,385,396,399,400,401,404,405,410,411,416,418,420]++r 423 5++r 432 7++[444]++r 447 5++[453,454,459,462,463,464,466,467,468,470,471,472,474,475,478,482,483,485,486,488,489,491,492,494,502,506,508,509,510,512]++r 518 4++[527,532,533,535]++r 540 5++[547,548,550]++r 552 4++[557,560,562,566,567,569,574,575,579,581,590]++r 593 4++[601,602,604,607,609,610,617,620,622,626,628,642,644,645,651,656,658,660,664,666,668,669,671]++r 679 4++[685,695,699,704,705]++r 718 4++[725,737,740,744,745,749,751,752,761,770,773,786,787,794,795,796]++r 804 4++[813]++r 825 6++[835,836,839,844,846,848,850,853,859,861,867,870,874,875,876]++r 887 1394)
def P_22_8 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_8
def N_22_8_0 : List NodeSpec := [e6 [334] ([14,42,65,304,482]++r 887 4),e6 [336] ([11,42,66,143]++r 891 6),u6 [205,204] ([14,44,49,65,256,257,357,368,491,867]++r 897 5),a6 [229,204] [14,65,257,356,867,897,898,902,903,904] [0,1],e6 [206] [44,65,143,255,358,651,905,906,907],e6 [338] ([11,143,304,905]++r 908 5),e6 [340] ([11,49,121,143,247,304,905]++r 913 4),a6 [103,20] ([11,44,65,96,262,373,383,607,859]++r 917 4) [0,1],a6 [20,25,34] ([299,426,444]++r 921 5) [0,1],a6 [163,20,25] [42,44,175,318,426,533,922,926,927,928] [0,1],u6 [92,41] ([36,44,276,278,279,400,401,494,628]++r 929 7),u6 [101,20,21] [14,44,175,299,581,936,937],u6 [22,20,21] [42,44,127,169,938,939],a6 [20,21,179] [127,940,941] [0,1],e6 [101] [11,36,44,143,144,581,937,942,943],e6 [22,21] [14,44,169,478,542,543,938,939,944,945],a6 [23,20,21] [44,127,169,294,410,946] [0,1],e6 [88] ([11,296]++r 947 4),e6 [342] ([42,44,247,894]++r 951 8),u6 [108,24] [11,49,247,313,314,316,317,595,959,960,961],a6 [24,20] [11,14,42,44,66,127,175,255,261,262,314,316,317,664] [0,1],u6 [222,24] [11,44,313,314,316,317,326,335,368,962,963],([23,0,1,2,3,4,25],([11,175,922]++r 964 5),[]),a6 [180,24] [11,176,307,314,316,317,664,969,970,971] [0,1],e6 [116,343] ([42,247,848]++r 972 11),e6 [116,246] ([255,482,483,979,980]++r 983 9),u6 [116,20,25] [44,175,318,848,992],([116,0,2,20,3,21,4,5],[44,127,169,299,410,543,848,993,994,995],[0,1]),u6 [20,327] ([127,848]++r 996 4),([116,99,0,2,20,3,4],([127,175,299]++r 1000 4),[1]),u6 [108,33] [11,247,324,329,330,331,595,959,960,961,1004],a6 [20,33] [11,14,42,44,127,175,255,262,324,330,331,464] [0,1],e6 [345] ([44,65,96,326]++r 1005 6),e6 [306,346] ([42,44,438]++r 1011 9),u6 [329,33] ([11,44,326,351,436]++r 1020 4),([199,0,1,3,4,5,33],([11,50,326]++r 1024 4),[0]),([0,1,2,3,97,5,95],[11,50,52,351,850,1028,1029,1030],[0,1]),u6 [97,235,33] [11,351,420,1031],a6 [21,25] [11,14,44,175,299,426,451,478,870,1032,1033] [0,1],a6 [347,6] ([11,14,336,416,447]++r 1034 5) [1],e6 [97,33] ([350,351,361,420,424]++r 1039 4),([0,1,348,3,4,5,6],[11,44,336,1014,1043,1044],[]),e6 [350] ([44,48,65,894]++r 1045 7),e6 [246,33] [11,42,50,247,372,436,438,989,1020,1052],u6 [311,33] [11,42,436,1020,1053,1054,1055],u6 [39,97,33] [11,350,351,361,362,372,1056],a6 [39,97] ([11,14,42,255,350,361,362,470,610,617,1030,1039,1041,1042]++r 1056 5) [0,1],u6 [39,227,33] [351,362,372,1030,1058,1061],u6 [39,244,33] [372,1062,1063],u6 [245,6] [11,14,326,336,337,416,472,740,1034,1035,1064],([108,0,1,2,3,97,5,33],[50,350,466,1030,1065,1066,1067],[0,1]),e6 [339,6] [14,121,337,595,1034,1035,1068,1069,1070],([0,1,2,20,3,97,5,33],([11,14,50,351,353,361,488]++r 1071 4),[0,1]),e6 [22] [44,65,127,143,304,905,939,944,1075,1076,1077],u6 [55,33] [36,44,49,65,210,214,350,351,411,424,436,448,1020,1078,1079,1080],a6 [55,20] ([11,66,175,210,214,255,262,281,299,351,411,448,705]++r 1078 4) [0,1],a6 [20,33,34] [11,14,350,351,367,372,1082,1083,1084] [0,1],a6 [38,33] [11,44,49,324,326,327,329,330,331,368,685,1085,1086] [0,1],u6 [34] [11,143,255,304,367,836,894,1087,1088,1089],a6 [221,33] ([36,49,65,332,351,424,436,609,1020]++r 1090 5) [0,1],a6 [210,20,84] [175,282,1095,1096] [0,1],a6 [20,33,25] [11,42,44,175,299,351,385,925] [0,1],e6 [351,6] ([14,326,337,368,416,1034,1035]++r 1097 4),([0,1,2,3,4,33,25],[11,36,42,44,318,385,1101,1102,1103],[]),u6 [20,21,33] [14,42,175,299,351,404,544],([0,1,3,84,4,5,6],[14,42,44,49,65,127,336,1104,1105,1106],[1]),e6 [352] ([9,11,36,144]++r 1107 4),a6 [106,97] [11,65,255,350,361,420,425,434,521,1039,1040,1111,1112] [0,1],a6 [106,39] [11,65,66,353,362,423,425,434,1030,1058,1062,1113,1114,1115] [0,1],u6 [108,106] [11,65,247,255,423,425,434,595,960,1116,1117],u6 [106,20] [11,44,65,127,255,262,373,425,434,521,859,1118,1119],a6 [38,28] [11,326,355,518,685,827,828,829,874,1120,1121] [0,1],u6 [147,33] ([11,326,350,351,372,436,518,1020]++r 1122 4),a6 [39,28] [11,362,438,518,827,828,874,1030,1058,1062,1113] [0,1],a6 [20,33,28] [11,14,65,127,350,351,372,518,830] [0,1],a6 [97,6] [11,121,336,337,339,416,420,1035,1039,1040,1099,1111,1126] [1],e6 [106,353] ([9,11,14,65,424,425,434,519,1119,1122]++r 1127 5),a6 [20,32] [127,175,299,1132,1133,1134] [1],a6 [101,20] [11,14,44,262,281,290,299,581,658,705,936,937,942] [0,1],a6 [32] [9,127,175,299,1132,1133,1134] [1],([38,0,31,2,3,4,33],[11,80,81,555,557,656,685,844,1085],[0,1]),([190,0,1,10,3,4,6],([4,11,73,620,622]++r 1135 6),[0,1]),([0,31,2,3,4,33,95],[11,81,557,656,1141,1142,1143],[0,1]),([197,0,1,10,3,4,6],[11,65,508,620,622,813,1135,1138,1144,1145,1146],[0,1]),([0,31,2,39,3,4,33],[11,80,81,246,348,506,555,656,1060,1062,1147],[0,1]),u6 [55,20,33] [11,44,175,299,350,351,353,372,1078],([14,0,1,3,4,6],[12,25,65,67,626],[0,1]),a6 [20,21,34] ([169,175,543,544]++r 1148 4) [0,1],([353,0,31,2,3,4,33],[14,81,553,555,557,1129,1142,1152,1153],[1]),([108,354,0,2,3,4,5],([548,961,1004]++r 1154 4),[]),([354,0,2,20,3,4,5],([49,175,281,299]++r 1155 5),[]),([189,0,1,2,355,3,5],[11,44,121,247,368,1160,1161,1162],[]),a6 [189,204] ([14,121,257,357,651,897]++r 1163 5) [1],e6 [189,45] ([11,44,49,121,740,875,1099,1165]++r 1168 9),u6 [108,106,33] [11,65,350,423,424,425,595,961,1030,1177],a6 [189,39,33] [11,121,351,1030,1062] [0,1],e6 [189,39] [11,42,44,121,362,1058,1062,1113,1114,1172,1174,1175,1178,1179,1180],([189,106,0,1,3,4,5,33],[11,65,350,423,519,521,1181,1182],[0]),([189,106,0,1,3,4,5],[11,65,67,255,423,519,521,1119,1183],[0]),u6 [302,6] ([11,44,49,336,337,416,745,761,1035,1099,1126]++r 1184 4),e6 [302] ([11,42,49,66,121,144,255,745]++r 1184 6),e6 [356,33] ([11,49,121,351,353,372,1020,1030]++r 1190 6),([23,0,1,2,3,4,320],([11,44,65,294,805,1165]++r 1196 4),[]),e6 [23,243] ([247,255,294,806,807]++r 1200 8),e6 [357,33] ([49,121,350,351,353,372,424,436,1020,1030]++r 1208 6),e6 [359,189] ([11,44,49,121,1172,1174,1175,1179]++r 1214 8),([0,1,358,2,3,5,141],([11,44,49,121,1215]++r 1222 6),[]),e6 [323] ([42,44,65,66,143,304,905]++r 1228 6),u6 [20,89] ([11,42,127,255,400,562]++r 1234 4),e6 [174,358] ([11,14,42,44,96,121]++r 1238 4),([0,31,2,20,3,4,33],[11,81,127,242,299,553,557,835],[0,1]),e6 [360] ([11,42,66,143,255,894]++r 1242 7),e6 [361,358] ([11,14,121,1215,1238]++r 1249 5),a6 [70,6] ([11,14,48,122,326,336,418,489,1035,1099,1126]++r 1254 4) [0,1],([362,0,2,3,204,4,5],[49,357,651,897,903,1164,1258,1259],[1]),([174,362,301,0,2,3,5],([44,247,255,660,1241]++r 1260 5),[1]),u6 [274,20,25] [299,839,1265,1266],([362,301,0,2,62,3,5],[247,651,787,1263,1264,1267],[1]),([362,301,0,2,3,5,363],([44,247,1264]++r 1268 4),[1]),e6 [365] ([11,42,66,894]++r 1272 5),([349,0,1,2,3,281,5],[36,44,65,787,1045,1049,1277,1278],[]),u6 [236,33] [14,36,49,50,65,350,353,372,424,436,459,554,666,1279,1280],u6 [148,33] [11,255,351,353,369,372,436,1020,1030,1281,1282,1283],e6 [366] [11,42,66,144,304,1284,1285],([116,367,0,2,3,4,5],[11,326,1286,1287,1288],[]),e6 [369] ([42]++r 1289 4),e6 [370,61] ([9,36,42,112,247,846]++r 1293 11),u6 [139] [42,112,248,527,569,704,846,1304,1305],u6 [63] [44,112,143,144,165,255,486,491,1306,1307,1308],e6 [372] ([11,44]++r 1309 5),([106,0,1,3,4,5,6],[9,11,65,550,1314,1315,1316],[0]),a6 [61,20,25] [43,44,112,175,299,426,846,1317] [0,1],u6 [178,74] ([9,11,36,173,540,601,642,695]++r 1318 4),([116,0,373,2,3,4,5],([11,44,848]++r 1322 4),[]),u6 [258,74] ([11,44,112,172,173,326,368,560,601,695]++r 1326 4),e6 [376] ([11,65]++r 1330 5),e6 [378] [11,44,65,66,143,255,905,1335,1336,1337],u6 [177,74] [9,11,36,66,172,173,326,541,601,695,1338,1339,1340],u6 [108,74] [11,112,172,173,247,548,601,695,960,1004,1341,1342],e6 [381] ([44]++r 1343 5),e6 [382] ([11,44,247,894]++r 1348 5),([383,0,1,2,3,5,141],([44,49,247,1284,1286]++r 1353 4),[]),e6 [384] ([44,247,1355]++r 1357 5),u6 [106,183] ([11,65,255,425,434,668,905,1119,1131]++r 1362 4),([38,0,2,27,3,4,5,33],[11,596,685,718,721,1366,1367,1368],[0,1]),e6 [385] ([9,66,894]++r 1369 5),e6 [387] ([42,49,66,121,143,304,905]++r 1374 5),e6 [388] ([9,36,44,48,65,144,787,1278]++r 1379 4),e6 [389,138] ([42,44,49,248,255,326,438,704]++r 1383 8),([0,1,390,27,3,4,5],([121,304,669]++r 1391 5),[]),e6 [391] ([11,42,66,255,304,894,905,1284]++r 1396 4),e6 [124,377] ([65]++r 1400 12),a6 [113,6] [9,11,14,47,96,209,416,418,492,1035,1126,1412,1413] [0,1],e6 [179] ([65,127,905]++r 1414 7),a6 [108,33,6] [337,339,350,595,1030,1177,1421] [0,1],e6 [393] ([9,1373]++r 1422 5),e6 [394] [14,36,48,65,165,1427,1428,1429],e6 [395,27] ([36,42,96,596]++r 1430 6),u6 [124,24] ([14,307,313,314,316,547,1404,1410,1411]++r 1436 6),u6 [22,20] [42,44,65,127,175,262,373,859,938,939,1076,1077,1442],e6 [124,33] [14,36,324,329,330,333,348,547,1404,1411,1443,1444,1445],e6 [25] [11,175,1446,1447,1448],([306,0,1,2,3,397,5],[11,247,368,1449],[]),([335,0,61,1,3,4,5],([11,326]++r 1450 4),[]),e6 [398] [11,42,49,66,165,304,376,1293,1454,1455,1456],e6 [349,61] ([9,36,44,48,112,1045,1293,1294]++r 1457 5),([106,0,1,3,4,5,28],[11,65,66,67,170,602,1462,1463],[0]),e6 [124,33,6] [14,65,337,350,369,547,1464,1465,1466],e6 [399] ([11,36,66,143,1206]++r 1467 6),([124,0,31,2,3,4,33],[80,81,348,547,553,656,1142,1153,1473],[0,1]),([124,400,0,1,2,4,5],([9,42,96,547,1445]++r 1474 5),[]),a6 [357,6] [9,49,336,337,339,416,1035,1099,1126,1209,1211,1212,1479,1480] [1],u6 [72] [11,49,143,281,299,509,510,512,846,1481],([124,354,0,2,3,4,5],[9,165,1154,1155,1157,1445,1473,1482],[]),([0,1,3,77,4,130,5],[14,42,44,65,651,1483,1484],[]),([116,124,99,0,2,3,4],[348,1002,1003,1445,1473,1485,1486,1487],[1]),e6 [373] [42,44,247,304,894,1278,1488,1489,1490],e6 [124,196,33] [65,165,350,369,547,1190,1410,1491,1492,1493],e6 [401] [11,36,42,66,255,1472,1494,1495],u6 [21,6] [11,14,44,127,542,544,1034,1496,1497,1498],u6 [124,28] [11,65,432,433,474,475,547,596,737,1404,1410,1441,1499,1500,1501],u6 [124,74] [9,11,36,112,165,172,173,695,1404,1473,1502,1503,1504],u6 [237,33] [14,65,350,353,372,424,435,437,786,1505,1506,1507],([116,0,2,3,21,4,5],[14,127,169,299,543,993],[]),e6 [402] ([11,42,66,143,304,905,1269]++r 1508 5),e6 [183,377] ([11,65,1363,1365]++r 1400 4++[1406]++r 1513 6),e6 [196,403] ([11,438]++r 1519 6),a6 [262,33] [36,348,372,436,594,644,1030,1525,1526,1527] [0,1],u6 [124,266] ([11,36,547,744,1404,1473]++r 1528 10),e6 [404] [9,491,651,787,1259,1538],([106,0,27,3,4,5,33],[11,65,304,566,1539,1540],[0]),a6 [21,84] [14,44,65,127,169,1541,1542,1543] [0,1],e6 [405] ([11,255]++r 1544 5),a6 [238,33] ([14,36,348,350,372,424,681]++r 1549 5) [0,1],e6 [189,406] ([42,44,96,1165,1174,1175]++r 1554 5),e6 [281,407] ([11,65]++r 1559 7),([174,196,301,0,1,2,4,5],([11,42,1241]++r 1566 8),[]),e6 [196,353,33] [11,65,165,372,438,1020,1122,1127,1129,1190],e6 [174,124,27] ([547,1260,1405,1410]++r 1574 8),e6 [294] ([9,11,44,49,144,255,348,438]++r 1582 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_0 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_0 = true := by decide +kernel
def N_22_8_1 : List NodeSpec := [e6 [408] ([11,42,894]++r 1586 6),([152,0,1,27,3,4,5,6],[11,65,67,200,201,418,454,567,669,1592,1593,1594],[]),([174,409,1,2,3,4,5],([144,660,1241]++r 1595 4),[]),u6 [106,20,33] [11,14,65,127,175,351,425,1084],u6 [124,106] [11,65,423,425,519,547,770,905,1131,1404,1410,1411,1441,1599,1600],e6 [103] [11,44,143,304,607,905,918,919,920,1601],([354,152,0,2,3,4,5],([9,36]++r 1154 5++[1602,1603,1604]),[]),u6 [106,152,33] [11,65,434,519,1020,1190,1600,1605,1606,1607],e6 [106,152] [11,65,66,143,425,434,519,567,905,1119,1131,1606,1608,1609],e6 [245] ([14,44,326,471,472,740,894,1064]++r 1610 4),u6 [23,262] [42,49,165,247,307,574,575,644,1527,1614,1615],([196,335,0,1,3,4,5],([11,255,326,1453,1491,1522]++r 1616 5),[]),a6 [152,33,6] [11,14,49,65,418,424,436,567,1020,1035,1126,1421,1621,1622,1623] [0,1],u6 [303] [44,704,749,1232,1534,1624,1625,1626],e6 [196,386] ([42,49,121,438,1573]++r 1627 7),a6 [93,20] ([14,42,65,66,175,255,258,261,262,276,277,279,373]++r 1634 4) [0,1],([116,99,152,0,2,3,4],[1000,1002,1003,1485,1486,1487,1602,1604,1638],[1]),e6 [320] [247,804,805,1639,1640,1641],e6 [61,344] ([44,326,846,1005,1293,1294]++r 1642 7),([23,0,1,2,20,3,4,25],[44,175,264,294,922,965,966,968],[0,1]),([0,1,27,3,7,4,5,6],[11,201,418,447,453,454,1593,1649],[0]),u6 [152,33] [14,36,143,324,329,331,333,464,567,1443,1444,1604,1606,1650],u6 [196,183,33] [65,165,372,438,668,1190,1365,1493,1651],a6 [183,33,6] [11,14,49,65,418,424,436,668,1126,1465,1621,1622,1652] [0,1],a6 [108,28] [11,247,432,433,590,595,596,737,960,1116] [0,1],e6 [412] ([42]++r 1653 8),e6 [174,124,33] [96,350,372,1260,1405,1410,1473,1577,1661,1662],([108,0,1,27,3,4,5,6],[11,200,201,453,454,595,669,961,1663],[0,1]),e6 [413,196] ([11,49,438,1491,1632]++r 1664 8),a6 [294,6] [11,42,49,336,337,348,416,699,761,1035,1126,1583,1585,1672] [0,1],e6 [415] ([11,304]++r 1673 4),a6 [27,238] [36,65,165,681,682,1553,1574,1576,1677,1678,1679] [0,1],([0,1,27,45,3,4,5,6],[11,200,201,418,453,454,740,1170],[0]),([0,1,27,20,3,4,5,6],[11,14,127,175,201,418,453,454,1593,1680],[0,1]),e6 [417] ([11,44,255,1613]++r 1681 8),e6 [347] ([11,42,44,247,447,1036,1037,1038]++r 1689 4),e6 [419,196] [11,42,247,368,438,1491,1632,1666,1693,1694],u6 [152,24] [14,143,307,313,314,317,567,664,1436,1437,1438,1606,1695],e6 [306,389] ([11,42,44,49,438,1017,1018,1322,1388,1389,1390]++r 1696 4),e6 [189,420] ([11,44,121,1174,1175]++r 1700 7),([116,108,99,0,2,3,4],[595,961,1003,1004,1485,1486,1638],[1]),e6 [124,204] ([14,65,357,491,897,898,1163,1404,1411]++r 1707 6),a6 [20,88] ([175,294]++r 947 4) [0,1],([0,31,2,3,97,4,33],[11,81,242,420,467,468,557,1041,1713],[0,1]),u6 [236] [9,14,36,42,49,50,65,66,255,436,459,552,554,1279,1280,1714],u6 [183,204] [14,65,143,357,491,867,898,903,1163,1363,1707,1708,1715,1716],a6 [317] ([11,42,47,66,794,795,796]++r 1717 5) [0,1],e6 [421,74] [9,36,165,172,173,601,642,695,1502,1503,1722,1723],u6 [332,33] [11,49,326,350,351,372,438,876,1020,1122,1190,1191,1724,1725],([422,152,0,1,2,3,5],([9,247,1603,1604]++r 1726 5),[]),u6 [107,6] [339,416,418,449,450,1035,1126,1731,1732,1733],([335,0,1,3,4,5,6],[9,11,47,326,1734,1735,1736],[]),e6 [423] ([11,49,304,376,894,905,1284,1602]++r 1737 5),e6 [377,130] ([11,14,44,1241,1400,1401,1406]++r 1742 4),e6 [425] ([9,491,651,787]++r 1746 5),a6 [262,27] [36,42,247,596,644,645,1432,1434,1527,1576,1751,1752] [0,1],e6 [426] [36,438,1522,1573,1753,1754,1755],e6 [427] [11,36,49,255,438,1522,1613,1756,1757,1758],a6 [147,28] [65,326,432,433,590,737,1124] [0,1],e6 [428] [36,49,438,1522,1613,1759,1760],e6 [196,373] ([11,42,44,438,1014,1632,1633,1668]++r 1761 5),e6 [429] ([14,42,894]++r 1766 8),u6 [242] [9,36,49,50,65,66,143,436,462,463,1774,1775,1776],e6 [327] ([11,14,49,66,127,299]++r 996 4),([41,0,1,2,20,3,4,33],[11,14,42,65,175,276,279,299,351,372,380,399,1777,1778],[0,1]),e6 [306,416] ([11,42,44,438,1014,1018,1752]++r 1779 6),e6 [306,39] [11,44,48,610,1018,1058,1060,1178,1783,1785],([108,0,31,2,3,4,33],[11,80,81,555,557,595,656,1004],[0,1]),([124,0,1,27,3,4,5,6],[11,65,67,200,201,418,453,547,669,1592,1786,1787],[0]),u6 [106,183,33] [11,65,434,1190,1363,1600,1788],e6 [174,183,27] [65,668,1241,1365,1432,1517,1575,1576,1595,1789],e6 [430] ([11,44,49,66,144,438]++r 1790 6),e6 [431,196] [11,42,438,1491,1632,1666,1796,1797,1798],u6 [70,45,6] [326,337,339,416,875,1099,1254],e6 [433] [11,42,66,304,1799,1800,1801],u6 [20,74] [9,11,36,42,44,112,173,255,262,281,299,601,642,695,1802],e6 [434] [11,44,255,1387,1613,1803,1804,1805],e6 [23,357] [42,49,247,294,1206,1207,1209,1211,1212,1213,1479,1806],([131,0,1,3,5],[67,158,368],[0]),u6 [242,33] [14,36,49,50,65,353,424,436,463,861,1020,1774,1775,1776],([174,0,435,2,3,281,5],([36,660,1241,1403]++r 1807 4),[1]),([0,1,2,20,39,4,5,33],([11,14,326,328,350,353,354,372]++r 1811 6),[0,1]),u6 [174,183,33] [96,372,436,1365,1403,1456,1517,1595,1662,1817,1818],([38,0,1,2,20,3,5,33],[11,14,44,50,325,326,350,351,353,355,405,719,720],[0]),([0,1,436,2,3,281,5],[11,44,1793,1819,1820,1821],[]),([190,57,0,1,2,3,5],[11,47,326,337],[0]),u6 [124,39,33] [348,350,353,362,369,372,436,1058,1410,1822],e6 [437] [9,36,42,48,66,668,1456,1523,1823,1824,1825],a6 [97,28] [11,121,361,420,518,827,828,830,1039,1111] [0,1],e6 [61,438] ([36,42,96,112,1284,1293,1294]++r 1826 5),e6 [196,432] [11,42,438,1491,1831,1832,1833],([400,183,0,1,2,4,5],[42,96,668,1475,1523,1834,1835],[]),a6 [20,28] [11,14,42,44,65,127,255,262,432,474,590,604,737] [0,1],([254,0,1,2,3,4,74],[9,11,36,172,593,642,1836,1837,1838],[0]),([0,1,27,3,4,201,5],([65,773,1232]++r 1839 6),[]),([183,0,31,2,3,4,33],[36,80,81,348,553,555,557,656,668,1142,1153,1456],[0,1]),e6 [439] ([9,11,49,326,668,894,1456]++r 1845 4),u6 [183,39,33] [348,372,436,610,1020,1058,1060,1365,1822],a6 [20,179] [65,127,175,1414,1415,1419,1420,1849,1850] [0,1],e6 [440] ([9,36,567,1602,1604,1825]++r 1851 5),e6 [23,441] ([11,255,1202,1206,1207,1615]++r 1856 6),([116,99,183,0,2,3,4],[348,1000,1002,1003,1456,1485,1486,1487,1523,1638],[1]),e6 [442] [11,42,66,144,1489,1862],u6 [183,28] [11,44,65,255,432,433,474,475,590,596,668,737,1364,1365,1499,1500],u6 [183,24] [14,143,307,313,314,317,664,668,1363,1364,1365,1436,1437,1438,1863],u6 [20,72] [175,281,299,509,510,512,846,1481],e6 [443] ([11,66]++r 1864 6),u6 [61,246] [11,483,485,983,984,985,1284,1293,1294],e6 [444] [14,42,165,1870,1871,1872],([445,0,1,2,3,5,141],([44,49,247,1226,1433]++r 1873 4),[]),a6 [148,28] [65,124,255,432,433,474,590,737,1282] [0,1],u6 [290] ([11,42,679,680]++r 1877 7),u6 [96,33] [11,42,50,436,1020,1884],u6 [252,28] [11,44,326,432,433,535,590,596,604,737,1885],e6 [27,344] [36,44,326,1009,1432,1575,1643,1645,1850,1886,1887],e6 [343,33] [11,42,247,351,353,436,973,977,978,1020,1888],([254,0,1,2,3,4,266],[36,744,1630,1836,1889,1890],[0]),([289,23,0,1,3,4,5],[65,67,680,1202,1472,1891,1892,1893],[0]),([0,1,27,3,84,4,5],([65,127,427]++r 1894 5),[]),a6 [39,6] [11,336,337,362,416,438,1030,1035,1058,1062,1099,1113,1114,1126,1421] [1],([0,446,1,2,3,281,5],[44,1278,1489,1899,1900],[]),([0,1,27,20,3,84,4,5],[44,65,127,427,1844,1894,1896,1897,1898,1901],[0,1]),u6 [41,61,20] [11,44,112,175,281,494,846,930,1902],e6 [447] [11,42,66,143,905,1433,1903,1904,1905],e6 [61,343] ([11,42,112,247,846]++r 973 5++[1293,1294,1297]),u6 [23,238] [42,165,255,307,681,1202,1553,1615,1906],a6 [436,6] ([11,49,326,336,337,1035,1126,1821]++r 1907 4) [1],e6 [448] ([11,44,894]++r 1911 5),a6 [317,6] [11,47,416,796,1035,1099,1126,1720,1721] [1],e6 [449] [42,66,112,304,376,1293,1425,1916,1917],a6 [27,20,25] [44,175,264,426,596,1850,1918] [0,1],e6 [189,450] ([42,44,96,1165,1174,1175]++r 1919 4),a6 [41,27,20] [11,14,65,127,175,279,281,299,930,1850,1923] [0,1],u6 [124,106,33] [65,350,369,423,424,519,1131,1190,1445,1466,1600,1924],([0,1,27,3,77,4,5],([65,651]++r 1925 4),[]),e6 [451,304] ([11,14,438,1665]++r 1929 7),([92,0,2,20,3,4,5,33],[11,14,42,127,175,299,351,372,396,400,1084,1936,1937],[0,1]),e6 [452] ([11,49,66,144,438,1793]++r 1938 5),e6 [349,27] [36,44,48,596,1049,1432,1459,1461,1887,1943,1944],e6 [189,377] [11,44,96,1167,1174,1241,1401,1406,1945,1946],([196,0,1,2,3,138,141],([14,114,326,751,1522,1573]++r 1947 8),[]),([152,0,31,2,3,4,33],[36,80,81,553,555,557,567,656,1142,1153,1602],[0,1]),e6 [453] ([42,65,1232,1850]++r 1955 8),([0,1,2,3,4,74,141],[11,44,642,1286,1354,1963],[]),e6 [370,27] ([36,42,247,596,1298,1302,1303,1432,1434,1850,1887]++r 1964 4),a6 [190,45] [11,339,1099,1168,1169,1170,1968,1969,1970] [0,1],e6 [306,304] [14,44,48,438,1014,1930,1932,1935,1971],([0,1,2,27,3,138,141],([113,114,326,596,751,1433,1947,1951]++r 1972 5),[]),a6 [20,21,6] [14,42,127,336,544,1498] [0,1],e6 [27,246] [11,14,36,65,983,985,1432,1433,1576,1887,1977,1978],u6 [38,39,33] [11,350,351,355,372,1030],e6 [454] ([11,42,49,66,905,1014,1850]++r 1979 7),e6 [27,343] [11,36,42,247,596,973,975,977,981,1432,1434,1850,1887,1986],e6 [455] [11,44,65,143,255,905,1987,1988,1989],u6 [183,266] ([11,36,668,744,1456]++r 1528 4++[1534,1890,1990,1991,1992]),e6 [456] ([42,49,66,121,596,905,1433,1630]++r 1993 5),a6 [142,24] [11,313,314,316,317,326,1998,1999,2000] [0,1],([196,106,0,1,3,4,5],[11,65,67,425,519,2001,2002,2003],[0]),e6 [27,438] [36,42,96,596,1432,1433,1827,1829,1887,2004,2005],([380,0,1,2,3,5,141],[44,49,1226,2006,2007],[]),([183,0,1,27,3,4,5,6],[11,65,67,200,201,418,453,454,668,669,1592,2008],[0]),e6 [23,250] ([107,294,520,579,1206,1207]++r 2009 5),e6 [457,266] ([36,744]++r 1528 5++[1890,1991,2014,2015,2016]),e6 [458] [9,42,49,66,112,121,144,304,1284,2017],e6 [459] ([44,65,255,651,905]++r 2018 6),([0,1,2,3,4,266,141],[11,42,44,1226,1286,1890,2024],[]),e6 [460] ([11,42,66,143,144,255,294,304]++r 2025 4),e6 [196,367] [11,14,42,326,438,2029,2030],([0,1,2,20,3,4,33,25],[11,42,175,299,318,351,372,385,532,1101,1103],[0,1]),e6 [461,266] ([11,44,368,744,1528,1532,1534,1991]++r 2031 5),([306,0,1,358,2,3,5],[11,44,49,247,1014,1215,1225,2036,2037],[]),([0,265,1,2,3,138,141],[113,114,1373,1534,1949,1951,1953,2038,2039],[0]),([14,0,1,3,4],[12,25,67],[0]),e6 [462] [9,11,14,36,66,143,567,1288,1602,2040,2041],e6 [23,436] [11,49,294,1206,1207,1821,1907,1908,1910,2042,2043,2044],u6 [206,204] [14,49,65,257,357,359,651,897,907,1163,1164,2045],e6 [463] [36,44,144,1226,2006,2046,2047],e6 [464] ([9,49,66,143,144,1014,1322]++r 2048 4),([0,1,2,3,4,320,6],[11,44,336,805,1639,2052,2053],[]),a6 [196,97,33] [11,351,372,420,438,1491] [0,1],e6 [465] [9,49,66,144,1373,1534,1630,2054],u6 [38,106] [11,44,65,67,255,326,355,423,425,434,519,1120,1121,2055],e6 [466,304] ([11,14,44,48,368,438,752,1665,1930,1935,1971]++r 2056 4),([0,1,2,96,4,5,33],[11,42,50,853,1884,2060,2061],[0]),a6 [197,7] ([11,339,1649]++r 2062 5) [1],e6 [467] ([11,44,143,165,255,894,1665]++r 2067 7),e6 [468] ([11,42,44,66,143,304,905,1014]++r 2074 5),([0,1,2,3,469,5,141],[44,1226,1354,2079,2080],[]),e6 [413] [11,44,66,143,144,165,255,1667,1670],([174,0,1,304,2,4,5],([14,42,1241,1613]++r 2081 4),[]),a6 [220,33] [49,50,65,323,424,436,671,1020,2085,2086,2087] [0,1],e6 [470] [11,42,66,304,2088,2089,2090],u6 [304,141] [14,752,1226,1930,2081,2091,2092,2093],u6 [324,322] ([14,65,826]++r 2094 7),a6 [20,193,21] ([42,127,299,410,543]++r 2101 4) [0,1],a6 [441,6] [11,47,65,416,1035,1126,1859,1860,2105,2106] [1],u6 [306,196,304] ([42,438,1668,1783]++r 2107 4),e6 [471] ([44,247,1875]++r 2111 9),e6 [472] ([14,44,894]++r 2120 6),a6 [323,322] ([14,44,49,65,825,1231,1232,1233,2098]++r 2126 4) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_1 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_1 = true := by decide +kernel
def N_22_8_2 : List NodeSpec := [e6 [473,266] ([11,1528,1531,1890,1991,2034]++r 2130 4),e6 [21] ([14]++r 2134 5),([0,1,20,3,84,4,5,6],[42,65,127,175,336,416,1104,1105,1106],[0,1]),a6 [474] ([9,44,491,651]++r 2139 5) [1],a6 [371,33] ([11,14,65,351,1020,1190,1191,2124]++r 2144 4) [1],u6 [152,74] [9,11,36,112,172,173,601,642,695,1502,1503,1602,1603,2148],e6 [436,33] [11,14,42,48,350,351,436,1020,1821,1908,1910,2149,2150],a6 [20,33,6] [11,14,65,127,336,337,350,351,372,416,418,1084,1421] [0,1],e6 [475] ([11,49,66,121,143,144,255,304]++r 2151 5),a6 [39,130,33] [11,65,353,362,372,1062,1744,2156,2157] [0,1],([0,61,1,2,3,138,141],[112,113,114,326,1284,1949,1951,1953,2038,2158],[0]),e6 [197,301] ([11,14,42,44,121,1568]++r 2159 6),u6 [183,74] [9,11,36,112,165,172,173,601,642,695,1456,1502,1503,2165],e6 [476] ([11,44]++r 2166 6),a6 [20,34] [11,14,255,261,262,367,369,372,373,502,836,1087,1089,2172] [0,1],([362,301,0,477,2,3,5],([44,247,1262,1264]++r 2173 5),[1]),e6 [478] [11,42,49,66,143,144,304,846,1322,1697,2178,2179,2180],([0,1,2,3,4,407,6],[42,65,1563,2181],[]),e6 [479] ([11,44,49,438,520,894]++r 2182 7),([23,0,1,2,3,4,407],([11,65,1573]++r 2189 4),[]),u6 [152,28] [11,42,65,432,433,474,475,567,590,596,604,737,1499,1500],e6 [480] [14,44,255,894,1613,2161,2193,2194,2195],e6 [481] ([255,438,1573,1668]++r 2196 5),([431,99,0,1,2,3,4],[11,36,255,1489],[]),u6 [183,33] [14,36,324,329,330,331,333,348,464,668,1363,1443,1444,1523],e6 [407] ([11,44,255,1613]++r 2201 5),([306,196,0,1,2,3,281,5],[11,44,247,1014,1278,1491,1932,2206,2207,2208],[]),([196,301,0,1,2,3,5,141],[11,44,247,1226,1567,2209,2210,2211],[]),e6 [482] ([121,1165]++r 2212 5),([196,106,0,1,3,4,5,33],[11,65,353,425,519,2217],[0]),a6 [23,20,84] [44,281,294,311,2218] [0,1],u6 [38,196,33] [11,326,350,372,438,685,1668],e6 [483] [11,14,44,143,144,255,2219],([0,1,2,3,97,5,141],([11,50,247,1042]++r 2220 5),[]),a6 [108,33,28] [11,518,595,874,1030] [0,1],e6 [23,260] ([11,255,1202,1206,1207,1615,1773]++r 2225 5),e6 [359] [11,36,42,44,66,143,144,1214,1217,1218,1219,2230],a6 [196,322] [14,44,65,438,1232,1668,2098,2126,2127,2128,2231] [1],e6 [484] ([11,36,49,143,144,255,438]++r 2232 4),a6 [39,33] [11,66,324,326,329,330,331,1062,1178,2236] [0,1],([189,131,0,1,3,5],[44,65,67,121,247,255,368,725,2237,2238,2239],[0]),([354,183,0,2,3,4,5],([9,36,165]++r 1154 4++[1456,1523,1992]),[]),e6 [485] [36,49,144,438,1522,1573,2240],u6 [55] [9,36,49,65,66,143,144,210,214,351,411,448,1078,1079,1080],([335,0,1,379,3,4,5],[11,66,1226,1616,2006,2241,2242,2243],[]),([409,1,2,62,3,4,5],[651,787,1306,1596,1597,1598,2244,2245],[]),e6 [487,486] ([11,36,44]++r 2246 9),([0,435,2,62,3,281,5],[491,651,787,1809,1810],[1]),e6 [441,33] [11,14,42,50,96,247,372,436,1020,1859,1860,2255],a6 [103,20,25] [11,44,175,281,383,917,918] [0,1],([0,1,2,3,97,281,5],[11,44,50,247,420,1041,2256,2257,2258],[]),e6 [488] [9,14,36,42,66,668,979,1288,1456,2259],([431,0,1,2,3,4,33],[11,36,50,2260],[]),u6 [204,130] [14,42,357,651,1163,1742,2261,2262,2263],e6 [489] ([11,42,66,143,304,905]++r 2264 5),e6 [174,289] [11,42,65,96,121,1260],([306,289,0,1,2,3,5],[11,65,368,1014,2269,2270],[]),e6 [196,363] ([11,42,44,438,1268,1269,1491,1567,1632,1666,1668]++r 2271 4),([0,446,1,2,3,130,5],[44,1489,1900,2263],[]),e6 [490] ([11,143,1613]++r 2275 6)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_8_2 : checkNodesBT W_22 g_22 F_22 P_22_8 A_22 B_22_7 8 N_22_8_2 = true := by decide +kernel
def N_22_8 := N_22_8_0 ++ N_22_8_1 ++ N_22_8_2
def B_22_8 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_8
set_option maxRecDepth 500000 in
lemma B_22_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 8 xs.toFinset) B_22_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_22) (raw := r_22) (pspecs := ps_22) (used := U_22_8) S_22_ok
  have hm0 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_7_ok C_22_8_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def U_22_9 : List Nat := ([9,11,14,36,42,44]++r 47 4++[65,66,67,81,96,107,112,121,127,143,144,165,169,173,175,201,247,248,255,262,278,281,288,294,299,304,307,314,316,324,326,330,336,337,348,350,351,353,355,361,368,372,373,418,420,424,425,426,432,436,438,453,474,475,485,491,518,519,543,545,547,548,565,567,574,579,595,596,628,644,651,656,660,668,669,681,685,695,704,705,737,761,787,804,805,827,830,842,846,848,859,894,897,905,922,926,930,931,960,961,973,975,978,979,980,982,985,987,988,989,1003,1004,1014]++r 1017 4++[1030,1034,1035]++r 1039 4++[1052,1058,1060,1062,1069]++r 1082 4++[1099,1113,1114,1116,1121,1122]++r 1128 4++[1141,1142,1148,1155,1157,1163,1164,1165,1172,1174,1175]++r 1177 5++[1190,1191,1202,1206,1207,1209,1211,1225,1226,1232,1239,1240,1241,1251,1259,1260,1261,1267,1278,1284,1286,1288,1293,1294,1297,1298,1300,1303,1306,1322,1341,1352,1354]++r 1362 4++[1372,1373]++r 1383 4++r 1401 6++[1410,1411,1421,1424,1425,1426]++r 1432 7++[1441,1445,1453,1456,1459,1461,1465,1466,1472,1473,1475,1486,1489,1491,1493,1499,1500,1517,1521,1522,1523,1528,1532,1534,1537]++r 1559 5++r 1567 5++r 1573 4++r 1578 4++[1592,1595,1598,1599,1602,1603,1604,1606,1608,1609,1613,1616,1617,1621,1622,1623]++r 1628 6++[1639,1643,1645,1646,1648,1652,1661,1662,1666,1668,1697,1707,1708,1730,1743,1744,1750,1762,1764,1779,1782,1783,1789,1793,1798,1806,1810,1817,1819,1821,1822,1825,1829,1833,1836,1837,1850,1855,1857,1859,1884,1887,1899,1900,1908,1919,1920,1922,1932,1951,1953,1954,1966,1968,1970,1971,1976,1978,1992,2006,2009,2010,2012,2039,2043,2065,2079,2080,2081,2093,2098,2101,2105,2106,2108,2124,2127,2128,2142,2146,2149,2156]++r 2158 6++[2174,2177,2244,2247,2253,2255,2260,2263]++r 2281 322)
def P_22_9 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_9
def N_22_9_0 : List NodeSpec := [u6 [438] [36,42,96,368,1829],a6 [386] ([14,42,49,121,368,894]++r 1628 4++[1836,2281]) [0,1],a6 [343] [36,42,247,973,975,978,2282] [0,1],e6 [306,373] [11,44,107,247,255,1322,1762,1764,2283],a6 [246] [9,36,42,368,985,989,1052] [0,1],a6 [306] [9,11,36,42,44,66,144,247,368,2284] [0,1],a6 [322] [14,42,44,49,704,1232,2098,2127,2128,2285,2286] [0,1],a6 [344] [9,36,44,96,660,1643,1645,1646,2287] [0,1],a6 [41,20] [14,44,65,66,175,262,281,299,628,705,930,931,2288] [0,1],a6 [396] [9,11,36,44,143,144,2289,2290,2291] [0,1],a6 [20,25] [11,44,175,281,288,299,426,922,926] [0,1],a6 [25] [9,11,36,44,288,922,926] [0,1],a6 [21] [14,44,49,127,169,299,543,545,1148,2101] [0,1],a6 [23,20] [14,44,65,66,127,175,262,281,294,373,859,1472,1806,2292,2293,2294] [0,1],a6 [446] [9,36,42,44,49,66,143,144,247,255,1489,1899,1900,2295,2296] [0,1],a6 [116,141] [49,255,326,982,988,1052,1226,1286,1288,1354,2297,2298,2299] [0,1],e6 [116,174] ([11,42,49,96,247,348,979,980,982,987,1241,1260,1403,1595]++r 2300 5),u6 [116,108] [11,49,247,255,548,565,595,960,961,979,980,982,988,1004,1288,1341],u6 [33] [14,36,42,44,49,67,255,324,330,894],u6 [469] [9,42,44,66,67,247,2079,2080,2305,2306],a6 [38,33] [11,14,36,44,49,50,326,350,353,355,424,436,685,1020,1085,1121,2307,2308,2309] [0,1],a6 [190,6] [11,44,47,336,761,1035,1099,1968,1970,2310,2311,2312] [0,1],a6 [97,33] ([11,14,44,50,351,361,420,1030]++r 1039 4++[2313]) [0,1],a6 [33,141] [11,36,44,49,50,326,353,1052,1286,2314,2315] [0,1],a6 [39] [42,44,144,255,326,353,1058,1060,1062,1113,1178,1613,1822] [0,1],u6 [174,33] [11,36,42,96,247,353,372,424,436,1020,1260,1662,2316],a6 [116,306] [11,36,44,49,255,848,979,980,982,1017,1018,1288,1322,1697,2108,2317,2318] [0,1],a6 [306,33] [11,36,44,49,50,255,351,353,436,1020,1322,2317,2319] [0,1],a6 [108,33] [11,14,36,50,247,350,353,424,436,595,961,1004,1020,1177,2320,2321] [0,1],a6 [20,33] [11,14,36,42,44,49,50,127,175,255,299,351,353,1082,1083,1084] [0,1],a6 [337] [9,11,36,247,368,2322] [0,1],u6 [106] [11,42,44,65,66,67,143,255,304,425,519,905,1131],u6 [346] [42,44,67,143,144,255,326,1019,1613,2323],a6 [33,6] [11,49,337,350,418,424,1034,1190,1191,1421,1465,1621,1622] [0,1],a6 [108,31] [42,247,368,565,595,960,961,1004,1825,2324,2325,2326] [0,1],e6 [400] [42,44,49,66,67,143,144,255,1613,2327],([400,0,1,2,4,5],[42,49,67,96,1475],[0]),([491,1,2,3,4,5],[9,49,67,144,368],[]),([306,189,0,1,2,3,5],[9,11,44,49,247,255,368,1014,1697,2328,2329],[0]),([189,0,1,2,3,5,141],([9,11,44,49,65,121,368]++r 2330 4),[0,1]),a6 [174,189] [11,42,44,65,96,247,660,1172,1174,1175,1240,1241,1261,2334,2335] [0,1],u6 [370] [36,42,49,143,144,247,1298,1303,2336],a6 [197,6] [11,42,65,96,326,337,761,1035,1099,2065,2310,2337,2338] [0,1],a6 [189,62] ([14,65,247,255,651,787,1165,1306]++r 2339 6) [0,1],u6 [189,23] ([44,49,65,67,255,294,1165,1179,1207,1472,1806]++r 2345 5),a6 [335] [9,11,42,44,65,66,143,304,368,905,1453,1616,1617,2350] [0,1],a6 [189,99] ([44,49,65,67,121,255,1165,1179]++r 2351 8) [0,1],a6 [373] [11,14,36,42,44,255,894,1014,1322,1762,1764,2283,2359] [0,1],a6 [189,33] [11,44,49,50,67,121,351,353,1020,1030,1165,1180,1190,1191,2360,2361,2362] [0,1],([0,1,2,3,138,141],[49,107,368,1951,1953],[0,1]),u6 [254,61] ([112,326,1284,1293,1294,1297,1836,1837,2158]++r 2363 5),u6 [61,138] [11,44,112,248,704,846,1284,1300,1383,1384,1385,2368],a6 [124,33] [11,14,36,49,350,353,424,547,1020,1190,1404,1445,1466,1473,1613,1661,2369,2370,2371] [0,1],a6 [31,20] [42,44,66,127,175,262,281,299,368,373,1855,2326,2372,2373] [0,1],u6 [306,265] [11,36,247,255,1014,1322,1373,1424,2039,2374,2375],u6 [374,265] ([11,66,1373,1424,2374]++r 2376 7),u6 [265,138] ([44,247,248,704,1232,1373]++r 1383 4++[1534,2383]),e6 [374,33] [11,14,36,49,50,353,424,436,1020,1190,1372,1613,2369,2384,2385],e6 [196,407] [11,49,247,438,1491,1560,1573,1613,2386,2387],a6 [174,124] [11,42,96,165,255,348,1260,1403,1405,1410,1441,1473,1537,1578,1580,1613,2300,2302,2316,2388,2389] [0,1],a6 [28] [11,42,44,65,67,255,432,474,475,596,737,905,1499,1500] [0,1],a6 [124,62] [65,66,144,165,491,1267,1306,1404,1441,1445,1473,2339,2341,2390,2391,2392] [0,1],u6 [108,61] [11,42,112,247,548,565,960,961,1004,1284,1293,1294,1297,1341,2363],u6 [124,265] [11,66,144,547,1404,1411,1441,1445,1473,1534,1537,2374,2377,2378,2380,2393],a6 [124,23] ([9,14,65,307,547,905,1202,1207,1404,1411,1441,1445,1537,1599,1613,1806,2345]++r 2394 4) [0,1],a6 [124,31] [144,348,1404,1411,1441,1445,1473,1537,2324,2325,2326,2373,2398] [0,1],a6 [189,6] [44,47,49,65,67,255,336,761,1035,1099,1179,2310,2399,2400,2401] [0,1],a6 [189,325] [44,121,247,255,842,1179,2402,2403,2404] [0,1],e6 [374,174] [11,42,96,143,660,1260,1403,1595,1613,2300,2302,2316,2376,2379,2388,2405],a6 [281,6] ([11,47,67,326,418,1099,1278,2106]++r 2406 4) [0,1],u6 [374,61] [11,36,165,1284,1293,1294,1297,2363,2381,2382,2410,2411],a6 [349] [9,36,44,49,143,144,787,1459,1461,2412] [0,1],a6 [33,28] [14,67,350,424,518,827,830,1191,2413,2414] [0,1],a6 [183,33] [11,14,36,49,50,350,353,424,436,668,1020,1190,1456,1523,1613,1652,1817,2369] [0,1],u6 [377] [14,42,44,96,255,894,1241,1401,1402,1403,1406],a6 [196,281] ([42,67,326,438,1278,1522,1562,1573,2105]++r 2415 6) [0,1],a6 [152,31] [36,42,143,1602,1603,1604,1606,1825,1855,2324,2325,2326,2373,2398] [0,1],u6 [74] [9,11,36,42,44,112,144,173,255,695,2421],a6 [183,31] [36,44,255,348,1363,1364,1456,1523,1825,1855,1992,2324,2325,2326,2373,2398] [0,1],u6 [289] ([42,49,65,66,67,121,143,304,368,905]++r 2422 4),u6 [174,61] [9,11,36,42,96,112,165,247,485,1260,1293,1294,1297,1403,1595,1648,2301,2302,2363,2426],u6 [124,196] [9,65,165,547,905,1404,1441,1491,1573,1599,1613,1633,1932,2427,2428],u6 [189,358] [44,67,121,247,1165,1225,1239,1240,1251,2429,2430],a6 [375] [9,14,36,42,65,66,144,165,368,2379,2431,2432,2433] [0,1],e6 [174,424] [11,36,42,96,660,1241,1403,1750,2300,2434,2435],a6 [152,27] [9,11,36,67,567,596,1432,1433,1434,1574,1602,1604,1606,1887,2436,2437] [0,1],a6 [183,27] [9,11,36,65,67,596,668,1363,1432,1433,1434,1456,1523,1574,1613,1887,2436,2437,2438] [0,1],a6 [190] ([11,42,44,66,143,247,304,905,1352]++r 2439 6) [0,1],u6 [411] [36,42,49,67,368,2445,2446],u6 [116,124] [11,49,144,255,348,547,980,982,988,1404,1411,1441,1445,1473,1537,1613,2304,2447],u6 [152,61] [9,11,36,42,112,143,1284,1293,1294,1297,1602,1603,1604,1606,2363,2410,2411],a6 [414] ([9,11,36,144,368]++r 2448 4) [0,1],e6 [374,116] [14,36,49,894,979,980,982,1288,1372,2304,2376,2381,2382,2447,2452],u6 [383] [9,36,42,44,49,66,143,144,247,304,1284,2453,2454],u6 [61,20] [11,44,66,112,175,262,281,299,373,705,846,1284,1293,1294,1297,2455],u6 [106,33] [11,49,67,350,353,425,519,1020,1131,1190,1191],u6 [392,61] [36,112,165,1284,1293,1294,1297,2363,2410,2456,2457],e6 [374,27] [9,36,65,67,143,1372,1432,1433,1434,1887,2376,2381,2436,2437,2458],u6 [254,196] [14,42,65,66,255,438,1491,1632,1666,1954,2366,2367],u6 [392,265] [66,1373,1424,1425,1534,2374,2377,2378,2380,2456,2457,2459],a6 [450] [42,96,143,144,326,1613,1919,1920,1922,2357,2460,2461] [0,1],([174,196,0,1,2,4,5],[9,11,42,49,65,66,326,1241,1570,1571,1613,2462],[0]),a6 [152,33] [11,14,36,49,50,350,353,424,436,567,1020,1190,1602,1604,1623,2369] [0,1],a6 [183,62] [65,66,165,491,787,1267,1306,1364,1456,1523,2244,2339,2341,2390] [0,1],e6 [174,141] [11,42,44,96,660,1052,1286,2093,2298],a6 [196,6] [42,49,65,67,247,337,761,1035,1099,1491,2310,2338,2463,2464] [0,1],u6 [339] [14,49,247,368,595,894,1004,1069,2465,2466],e6 [196,250] [42,44,326,438,579,1522,2009,2010,2012],a6 [403] [9,11,36,42,48,368,1521,1523,2467,2468] [0,1],([116,99,0,2,3,4],[36,49,67,1003,1486],[0,1]),u6 [424,62] [66,491,651,787,1267,1306,1750,2341,2343,2390,2435],u6 [306,492] [11,44,49,107,247,255,1014,1322,2469,2470,2471],u6 [374,196] [9,11,165,905,1372,1491,1522,1613,1633,1666,1932,2379,2427,2472,2473],([0,1,2,3,493,5],[36,49,67,368],[]),u6 [116,183] [11,36,49,255,348,668,979,980,982,1288,1363,1364,1456,1523,1613,1992,2304,2447,2474],u6 [116,152] [11,36,49,66,143,567,979,980,982,1288,1602,1603,1604,1606,1609,2304,2447,2474],a6 [108,23] [9,14,65,247,255,307,548,565,595,960,961,1116,1202,1206,1207,1472,1806] [0,1],a6 [23,183] [9,14,65,255,307,668,905,1206,1207,1362,1363,1364,1472,1523,1613,1806,1992,2345,2395,2475,2476] [0,1],a6 [124,27] [9,11,36,65,67,547,596,1411,1434,1445,1473,1574,1581,1613,1887,2436,2437,2477,2478] [0,1],u6 [196,183] [65,165,668,905,1362,1364,1522,1573,1613,1633,1666,1932,2427,2479],u6 [61,62] [112,165,247,491,1267,1293,1294,1297,1306,2244,2341,2343,2363,2480],a6 [431] [9,11,14,36,42,44,48,66,144,368,1798,2260] [0,1],e6 [174,306] [11,42,96,255,660,1017,1018,1260,1322,1783,2317,2481],a6 [196,141] ([9,11,42,49,65,247,326,1052,1522,1932,2297,2299]++r 2482 4) [0,1],u6 [92,20] [11,44,66,127,175,262,278,281,299,373,705,2486,2487],u6 [486] [11,36,42,44,67,2142,2247,2253,2488],([409,1,2,3,4,5],[9,67,144,368,1598],[0]),a6 [238] [9,36,42,49,165,255,348,681,2489,2490,2491] [0,1],u6 [183,61] [9,11,36,112,165,1284,1293,1294,1297,1363,1456,1523,1992,2363,2410,2411],u6 [445] [42,44,49,66,67,143,247,905,1433,2492,2493],u6 [306,61] [9,11,44,112,255,846,1284,1293,1294,1297,1697,2108,2158,2317,2494],a6 [23,152] [9,66,307,567,905,1206,1207,1472,1603,1604,1606,1608,1609,1806,2345,2395,2495] [0,1],a6 [432] [9,11,36,42,255,1404,1445,1833,2496,2497,2498] [0,1],a6 [174,183] [11,42,96,144,165,255,348,660,1364,1365,1403,1456,1517,1595,1613,1789,1992,2302,2316,2388] [0,1],u6 [124,61] [11,36,112,144,165,1294,1297,1404,1411,1445,1473,1537,2363,2410],([0,1,27,3,4,5,6],[11,65,67,201,418,453,669,761,1592],[0,1]),u6 [416] [42,44,49,65,67,143,255,326,905,1434,1613,1779,2499],u6 [24] [14,42,44,49,67,255,307,314,316,894,1436,1437,1438],a6 [27,20] [11,44,66,127,175,281,299,373,596,859,1433,1434,1850,2500,2501,2502] [0,1],a6 [189,320] ([44,49,121,247,255,804,1165]++r 2503 4) [1],a6 [435,62] [66,247,491,651,787,1306,2142,2244,2341,2343,2507,2508] [0,1],u6 [353,33] [14,50,143,326,353,424,436,1128,1129,1130,1190,2369],a6 [108,27] [11,247,565,595,596,960,961,1116,1432,1433,1434,1574,1887] [0,1],u6 [281,33] [11,14,36,44,49,50,67,326,1278,2255,2509],a6 [27,62] [65,491,596,651,1306,1432,1434,1574,2339,2343,2510,2511,2512] [0,1],a6 [27,138] ([11,65,248,596,704,1232,1385,1433,1850,1966]++r 2513 4) [0,1],u6 [27,141] [11,326,1226,1286,1354,1433,1978,2299,2482,2517,2518,2519],e6 [422] [36,42,44,49,66,67,143,144,247,1404,1730,2520,2521],u6 [358] [14,42,44,49,66,67,121,894,1225,1239,1240,1251,2522],u6 [306,27] [11,36,44,255,596,1014,1322,1432,1433,1434,1850,1887,1976,2108,2317,2523],u6 [392,27] [9,36,67,596,1425,1426,1432,1433,1434,1574,1613,1887,2436,2437,2457,2524],a6 [254,27] [326,596,1432,1433,1434,1574,1630,1887,1976,2364,2366,2367,2525] [0,1],u6 [380] [36,44,49,67,143,144,2006,2526,2527],a6 [97] [36,49,50,247,361,420,1039,1041,1042,2313] [0,1],a6 [196,99] [42,49,65,67,247,438,1491,1573,2351,2353,2355,2356,2357,2528,2529] [1],u6 [266] [11,36,44,67,144,255,1528,1532,1534],a6 [265,141] [11,42,49,1052,1286,1354,1373,2297,2298,2299] [0,1],a6 [61,141] [11,49,326,1052,1284,1286,1297,1354,2297,2298,2299] [0,1],u6 [304] [14,42,44,49,67,165,255,894,1932,1971,2081,2530],u6 [116,20] [11,44,66,127,175,255,262,281,299,373,705,848,982,1288,2531],u6 [196,304] [65,247,326,438,1491,1573,1613,1932,1971,2081,2532],a6 [371] ([44,49,65,143,304,905,1522,2124,2146]++r 2533 4) [0,1],u6 [196,418] ([42,44,368,438,1522,1573]++r 2537 4),e6 [494] [11,36,42,48,67,368,1259,2541],a6 [407] [11,42,44,65,144,165,255,1559,1560,1563,2386,2387] [0,1],a6 [204] [14,44,49,255,491,651,894,897,1163,1164,1707,1708] [0,1],([0,31,2,3,4,33],[36,67,81,656,1142],[0,1]),u6 [389] [9,36,42,44,49,66,143,144,255,326,1297,1613],u6 [197] [11,42,44,65,96,143,255,304,326,905,1613,2161,2162,2163,2542],a6 [33,95] [11,44,50,326,353,1020,1141,1191,1884,2369,2543,2544] [0,1],e6 [495] ([11,36,42,48,67,368,1750]++r 2545 4),u6 [254,265] [66,1424,1534,1630,1836,2039,2364,2365,2366,2374,2380],u6 [196,496] [247,438,1491,1573,1613,2549,2550,2551],a6 [196,301] [42,44,67,247,438,1522,1567,1568,1573,1633,1668,2159,2160,2552,2553,2554] [0,1],a6 [196,33] [11,42,49,67,247,350,353,438,1020,1122,1190,1191,1491,1493,1573,1633,2555] [0,1],u6 [306,196] [11,42,44,49,65,247,438,1014,1018,1491,1632,1666,1668,1782,1954,2108,2556],a6 [196,130] ([42,44,65,67,438,1522,1743,1744,2156,2263]++r 2557 5) [1],e6 [196,189] ([42,44,65,67,255,438,1165,1172,1174,1179,1181,1491,1522]++r 2562 4),u6 [196,392] [66,165,905,1426,1491,1522,1573,1613,1633,1666,1932,2427,2459,2566,2567],u6 [174,27] [11,36,42,96,247,596,1241,1260,1432,1434,1574,1575,1576,1579,1887,2301,2388],u6 [196,23] [42,65,67,247,1202,1207,1491,1573,1806,2345,2348,2568,2569,2570],a6 [436] [44,49,66,144,1793,1819,1821,1908,2043,2149] [0,1],u6 [196,138] [14,42,44,49,65,247,1232,1384,1385,1386,1522,1668,1932,2516,2571,2572,2573],u6 [189] [42,44,49,66,67,143,247,304,368,905,2574,2575,2576],u6 [183,265] [11,36,66,668,1363,1364,1373,1424,1456,1523,1534,1992,2374,2377,2378,2380],([0,435,2,3,281,5],[36,67,368,1810],[0,1]),a6 [23,130] [67,326,1472,1743,1806,2156,2263,2557,2560,2577,2578,2579] [0,1],e6 [497] [36,42,44,49,67,143,144,247,2580,2581],a6 [23,281] [67,326,1278,1472,1562,1806,2105,2415,2418,2582,2583,2584] [0,1],a6 [441] [42,44,49,368,1857,1859,2105,2585,2586] [0,1],a6 [62,281] [14,36,42,49,65,491,651,787,2105,2587,2588] [0,1],a6 [174,281] [11,14,36,42,96,247,326,660,1241,1403,1561,2105,2408,2589] [0,1],([354,0,2,3,4,5],[9,36,49,1155,1157],[0]),([306,0,1,2,3,281,5],[11,14,36,49,247,368,1322,2590],[0]),([422,0,1,2,3,5],[44,49,67,247,1404,1730,2521],[0]),u6 [368] [9,36,42,49,67,368,2591],([362,301,0,2,3,5],[44,67,247,255,368,2174,2177,2592,2593],[0,1]),u6 [362,62] [66,491,651,787,1259,1267,1306,2244,2341,2343,2594],a6 [174,435] ([11,36,42,44,96,247,660,1241,1261,1403,2142,2300,2508]++r 2595 4) [0,1],u6 [174,362] [11,36,42,96,255,660,1241,1259,1260,1403,2594,2599,2600]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_9_0 : checkNodesBT W_22 g_22 F_22 P_22_9 A_22 B_22_8 9 N_22_9_0 = true := by decide +kernel
def N_22_9_1 : List NodeSpec := [a6 [39,33] [11,14,42,326,350,353,372,436,1058,1060,1062,1113,1114,1122,1178,1822] [0,1],u6 [395] [36,42,96,165,368,1435,2601],a6 [357] [9,42,66,143,144,247,1209,1211,1569,2602] [0,1],a6 [20,21] [14,44,127,169,175,299,543,545,1148,2101] [0,1],a6 [262] [36,42,165,247,348,574,644] [0,1],a6 [320] [11,42,44,65,255,804,805,1639,2504,2506] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_9_1 : checkNodesBT W_22 g_22 F_22 P_22_9 A_22 B_22_8 9 N_22_9_1 = true := by decide +kernel
def N_22_9 := N_22_9_0 ++ N_22_9_1
def B_22_9 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_9
set_option maxRecDepth 500000 in
lemma B_22_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 9 xs.toFinset) B_22_9 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_22) (raw := r_22) (pspecs := ps_22) (used := U_22_9) S_22_ok
  have hm0 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_8_ok C_22_9_0
  have hm1 := checkNodesBT_mem (by decide) gp_22 W_22_ok hP A_22_ok B_22_8_ok C_22_9_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_22_10 : List Nat := [9,36,42,44,49,66,67,96,107,143,144,247,255,262,304,353,368,373,565,894,905,980,982,1018,1020,1052,1174,1179,1181,1190,1191,1207,1294,1297,1363,1364,1384,1385,1386,1411,1434,1441,1562,1599,1606,1613,1632,1633,1711,1806,1887,2105,2108,2299,2300,2301,2316,2317,2325,2326,2339,2341,2343,2345,2366,2367,2369,2374,2379,2381,2388,2390,2395,2427,2435,2436,2437,2457,2459,2508,2562,2594,2596,2603]
def P_22_10 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_10
def N_22_10 : List NodeSpec := [a6 [306] [9,36,44,49,66,107,143,144,247,368,1018,2108,2317] [0,1],a6 [141] [9,36,49,368,1052,2299] [0,1],a6 [62] [9,36,49,66,144,255,2339,2341,2343,2390] [0,1],a6 [108] [9,36,49,66,143,144,255,368,565] [0,1],a6 [23] [49,66,67,143,255,304,905,1207,1806,2345,2395] [0,1],a6 [31] [36,49,66,67,143,144,255,304,2325,2326] [0,1],a6 [189] [44,49,66,67,143,247,304,368,905,1174,1179,1181,2562] [0,1],a6 [424] [9,36,49,66,67,143,255,304,368,894,2435] [0,1],a6 [116] [9,36,49,66,67,143,144,255,304,980,982] [0,1],a6 [152] [9,36,49,66,143,144,255,368,894,905,1606] [0,1],a6 [33] [36,49,67,255,353,894,1020,1190,1191,2369] [0,1],a6 [435] [9,36,44,49,66,67,143,144,304,368,2508,2596] [0,1],a6 [138] [9,36,44,49,368,1384,1385,1386] [0,1],a6 [174] [9,36,42,49,66,96,143,144,255,2300,2301,2316,2388] [0,1],a6 [124] [9,36,49,66,143,255,894,905,1411,1441,1599,1711] [0,1],a6 [362] [9,36,49,66,67,143,144,255,304,368,2594] [0,1],a6 [254] [9,36,49,66,107,143,144,255,368,2366,2367] [0,1],a6 [392] [9,36,49,66,143,144,255,368,894,905,2457,2459] [0,1],a6 [374] [9,36,49,66,143,144,255,368,894,905,2379,2381] [0,1],u6 [61] [9,36,49,143,144,255,304,1294,1297],a6 [265] [36,49,66,67,143,144,255,2374] [0,1],a6 [20] [9,36,44,49,66,262,368,373] [0,1],a6 [27] [9,36,49,67,255,304,905,1434,1887,2436,2437] [0,1],a6 [196] [49,66,67,143,255,304,905,1613,1632,1633,2427] [0,1],a6 [183] [9,36,49,66,143,144,255,368,894,905,1363,1364] [0,1],a6 [281] [36,49,67,368,1562,2105,2603] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_10 : checkNodesBT W_22 g_22 F_22 P_22_10 A_22 B_22_9 10 N_22_10 = true := by decide +kernel
def B_22_10 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_10
set_option maxRecDepth 500000 in
lemma B_22_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 10 xs.toFinset) B_22_10 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_9_ok C_22_10
def U_22_11 : List Nat := [66,143,304,894,905]
def P_22_11 : BT (Option BoundPool) := buildPoolsSubBT 12 W_22 r_22 S_22 ps_22 U_22_11
def N_22_11 : List NodeSpec := [a6 [] [66,143,304,894,905] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_11 : checkNodesBT W_22 g_22 F_22 P_22_11 A_22 B_22_10 11 N_22_11 = true := by decide +kernel
def B_22_11 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_11
set_option maxRecDepth 500000 in
lemma B_22_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 11 xs.toFinset) B_22_11 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_10_ok C_22_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck r_22 g_22 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,6,22),(VAR 5,2,34)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT B_22_11 r_22 = true := by decide +kernel
lemma low_22 : Lower r_22 g_22 12 := lower_of_forestBT root_22_ok B_22_11_ok root_22_in

def g_orig := (d 0xfeeaeae8eeeaea80)
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,4),(2,3),(3,4)]) (by decide +kernel) low_22
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808424 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.or,[3,4]⟩,⟨.and,[4,3]⟩,⟨.and,[1,2]⟩,⟨.or,[8,6]⟩,⟨.or,[5,6]⟩,⟨.and,[0,9]⟩,⟨.or,[0,7]⟩,⟨.and,[1,10]⟩,⟨.and,[5,2]⟩,⟨.or,[12,8]⟩,⟨.or,[13,14]⟩,⟨.and,[16,15]⟩,⟨.or,[11,17]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_45594

open PEqualNP.Outside.L_meta_45594 in
theorem PEqualNP.Outside.L_meta_45594 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
