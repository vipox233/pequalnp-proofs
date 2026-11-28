import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_44988
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
def g_8 := 0xf880f880f880f880f880f880f880f880f880f880f880f880f880f880f880f880
def r_8 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_9 := 0xfac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0
def r_9 : List Nat := varsOf 15
def p_9 : List Nat := [6,6,7,7,9,9,11,11,12,12,13,14]
def q_9 : List Nat := [4,2,5,3,8,1,10,3,8,4,5,10]
def F_9 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_9 : goodPairs g_9 p_9 q_9 := goodPairs_of (by decide +kernel)
def W_9 : BT Decor := buildWiresBT 2 (mkBase p_9 q_9 r_9) []
lemma W_9_ok : btAll (fun x => faithful p_9 q_9 x ∧ x.1 < 2^256) W_9 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_9 : List (List (Nat × Nat)) := [[]]
def A_9 : BT (List (Nat × Nat)) := btOfList 1 al_9
set_option maxHeartbeats 0 in
lemma A_9_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_9 = g_9) A_9 := btAll_ofList (autos_of (by decide +kernel))
def S_9 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_9_ok : btAll (fun o => ∀ p, o = some p → Slice r_9 g_9 p.1 p.2) S_9 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_9 : BT (Option PoolSpec) := btOfList 1 ((([] : List PoolSpec)).map some)
def B_9_2 : BT (List (List Nat)) := BT.empty
lemma B_9_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 2 xs.toFinset) B_9_2 := .empty
def P_9_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_9 r_9 S_9 ps_9 []
def N_9_3 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_3 : checkNodesBT W_9 g_9 F_9 P_9_3 A_9 B_9_2 3 N_9_3 = true := by decide +kernel
def B_9_3 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_3
set_option maxRecDepth 500000 in
lemma B_9_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 3 xs.toFinset) B_9_3 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_2_ok C_9_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_ok : forestRootCheck r_9 g_9 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_in : bucketContainsBT B_9_3 r_9 = true := by decide +kernel
lemma low_9 : Lower r_9 g_9 4 := lower_of_forestBT root_9_ok B_9_3_ok root_9_in
def g_10 := 0xffecf880ffecf880ffecf880ffecf880ffecf880ffecf880ffecf880ffecf880
def r_10 : List Nat := varsOf 31
def p_10 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,18,18,19,19,21,21,21,22,22,24,24,25,25,26,28]
def q_10 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,2,17,3,20,17,5,20,6,16,8,17,9,10,20]
def F_10 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_10 : goodPairs g_10 p_10 q_10 := goodPairs_of (by decide +kernel)
def W_10 : BT Decor := buildWiresBT 7 (mkBase p_10 q_10 r_10) [(0,1,4),(0,2,3),(1,5,6),(1,2,3),(1,1,4),(0,8,9),(3,6,8),(3,5,9),(0,0,9),(1,13,6),(2,1,4),(3,1,4),(2,11,5),(1,5,3),(0,2,18),(1,2,18),(3,19,20),(2,0,6),(2,2,3),(3,2,3),(0,0,8),(3,13,8),(1,25,4),(0,1,27),(1,16,6),(1,25,5),(3,6,9),(2,0,19),(1,6,4),(0,0,20),(1,13,3),(3,2,35),(3,4,20),(0,1,33),(1,1,33),(2,1,33),(3,1,33),(0,3,4),(1,3,4),(3,42,43),(3,16,8),(3,13,3),(1,25,1),(1,24,16),(3,25,1),(1,24,5),(2,2,4),(2,1,3),(1,52,4),(0,1,2),(3,54,43),(1,54,3),(2,56,4),(1,51,52),(1,56,4),(1,54,4),(3,2,18),(2,3,4),(3,3,4),(2,1,43),(2,0,42),(1,16,3),(3,6,1),(1,2,42),(2,1,42),(1,51,3),(0,1,3),(1,1,3),(0,2,4),(1,73,3),(1,1,2),(0,0,75),(1,5,2),(3,1,3),(3,78,0),(3,6,4),(0,1,43),(2,2,1),(1,82,3),(3,2,4),(2,1,2)]
lemma W_10_ok : btAll (fun x => faithful p_10 q_10 x ∧ x.1 < 2^256) W_10 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_10 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_10 : BT (List (Nat × Nat)) := btOfList 1 al_10
set_option maxHeartbeats 0 in
lemma A_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_10 = g_10) A_10 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_10_0 : Slice r_10 g_10 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_1 : Slice r_10 g_10 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xffa0f000ffa0f000ffa0f000ffa0f000ffa0f000ffa0f000ffa0f000ffa0f000 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_2 : Slice r_10 g_10 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_3 : Slice r_10 g_10 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_4 : Slice r_10 g_10 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_5 : Slice r_10 g_10 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xecec8080ecec8080ecec8080ecec8080ecec8080ecec8080ecec8080ecec8080 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_6 : Slice r_10 g_10 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_8
set_option maxHeartbeats 0 in
lemma sl_10_7 : Slice r_10 g_10 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_8 : Slice r_10 g_10 (subcubeFast 8 4) 4 := by
  have hc : Lower (varsOf 19) 0xeeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_9 : Slice r_10 g_10 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_10 : Slice r_10 g_10 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) 0xececc8c8ececc8c8ececc8c8ececc8c8ececc8c8ececc8c8ececc8c8ececc8c8 6 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_11 : Slice r_10 g_10 (identDom 2 4) 6 := by
  have hc : Lower (varsOf 15) 0xf8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0 6 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_3
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_12 : Slice r_10 g_10 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xeeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_13 : Slice r_10 g_10 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) 0xffcccc88ffcccc88ffcccc88ffcccc88ffcccc88ffcccc88ffcccc88ffcccc88 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_14 : Slice r_10 g_10 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_10 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,7),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 4 1,4),some (subcubeFast 8 4,4),some (subcubeFast 16 2,4),some (identDom 1 3,6),some (identDom 2 4,6),some (identDom 0 3,5),some (identDom 1 2,5),some (subcubeFast 1 0,4)]
lemma S_10_ok : btAll (fun o => ∀ p, o = some p → Slice r_10 g_10 p.1 p.2) S_10 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_10_0) (forall_cons (fun _ h => by cases h; exact sl_10_1) (forall_cons (fun _ h => by cases h; exact sl_10_2) (forall_cons (fun _ h => by cases h; exact sl_10_3) (forall_cons (fun _ h => by cases h; exact sl_10_4) (forall_cons (fun _ h => by cases h; exact sl_10_5) (forall_cons (fun _ h => by cases h; exact sl_10_6) (forall_cons (fun _ h => by cases h; exact sl_10_7) (forall_cons (fun _ h => by cases h; exact sl_10_8) (forall_cons (fun _ h => by cases h; exact sl_10_9) (forall_cons (fun _ h => by cases h; exact sl_10_10) (forall_cons (fun _ h => by cases h; exact sl_10_11) (forall_cons (fun _ h => by cases h; exact sl_10_12) (forall_cons (fun _ h => by cases h; exact sl_10_13) (forall_cons (fun _ h => by cases h; exact sl_10_14) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))
def ps_10 : BT (Option PoolSpec) := btOfList 7 ((([(9,[]),(8,[]),(0,[(0,2,3),(1,2,3),(3,6,8)]),(0,[(0,3,4),(1,3,4),(3,42,43)]),(2,[]),(0,[(2,1,4),(3,1,4)]),(0,[(1,1,4)]),(14,[]),(0,[(0,2,3),(1,6,4)]),(4,[(1,6,4)]),(3,[]),(5,[]),(1,[]),(0,[(0,2,3),(1,2,3)]),(4,[]),(3,[(0,0,8)]),(5,[(0,0,8)]),(1,[(0,0,9)]),(12,[]),(0,[]),(7,[]),(4,[(2,0,6)]),(0,[(0,1,4),(1,1,4)]),(6,[]),(0,[(2,3,4),(3,3,4)]),(0,[(2,3,4),(1,62,4)]),(0,[(0,3,4),(1,3,4)]),(0,[(3,1,4),(1,16,3)]),(0,[(2,2,4),(1,2,3)]),(2,[(2,2,4)]),(0,[(1,2,3)]),(0,[(0,2,3),(3,6,1)]),(0,[(1,2,3),(2,8,4)]),(0,[(0,4,3),(1,2,42)]),(4,[(1,3,4)]),(0,[(0,3,4),(2,1,42)]),(0,[(2,2,4),(1,51,3)]),(0,[(0,1,3),(1,1,3)]),(10,[]),(0,[(0,2,4),(1,73,3)]),(0,[(0,1,2),(1,1,2)]),(13,[]),(0,[(1,1,2)]),(1,[(0,0,75)]),(0,[(0,1,2),(1,54,3)]),(0,[(0,1,4),(1,5,2)]),(0,[(0,1,4),(1,5,3)]),(0,[(3,1,3)]),(0,[(0,2,3),(3,6,4)]),(2,[(1,3,4)]),(0,[(0,2,3)]),(0,[(0,1,4)]),(0,[(2,2,1),(1,82,3)]),(0,[(3,2,3)]),(0,[(2,1,4)]),(0,[(2,3,4)]),(0,[(0,1,3)]),(0,[(0,1,2)]),(0,[(1,1,3)]),(0,[(3,2,4)]),(11,[]),(0,[(2,1,2)]),(0,[(0,3,4)]),(0,[(2,2,4)]),(0,[(1,3,4)])] : List PoolSpec)).map some)
def B_10_1 : BT (List (List Nat)) := BT.empty
lemma B_10_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 1 xs.toFinset) B_10_1 := .empty
def P_10_2 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 []
def N_10_2 : List NodeSpec := [([0,7,10],[],[]),([11,12,0],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_2 : checkNodesBT W_10 g_10 F_10 P_10_2 A_10 B_10_1 2 N_10_2 = true := by decide +kernel
def B_10_2 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_2
set_option maxRecDepth 500000 in
lemma B_10_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 2 xs.toFinset) B_10_2 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_1_ok C_10_2
def P_10_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 []
def N_10_3 : List NodeSpec := [([1,14,8,4],[],[]),([0,5,6,10],[],[0]),([15,11,16,0],[],[0]),([11,0,5,9],[],[0]),([17,0,1,4],[],[]),([0,7,8,9],[],[0]),([11,13,1,4],[],[]),([21,0,1,4],[],[]),([22,12,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_3 : checkNodesBT W_10 g_10 F_10 P_10_3 A_10 B_10_2 3 N_10_3 = true := by decide +kernel
def B_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_3
set_option maxRecDepth 500000 in
lemma B_10_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 3 xs.toFinset) B_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_2_ok C_10_3
def P_10_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 [0,1,2]
def N_10_4 : List NodeSpec := [([15,23,24,16,0],[],[0,1]),([15,16,25,2,3],[],[1]),([26,1,2,3,4],[],[]),([25,28,2,3,4],[],[]),([15,0,2,29,3],[0],[]),([15,16,0,6,8],[],[0,1]),([0,5,2,3,10],[],[0]),([1,30,2,3,4],[],[1]),([0,1,7,8,4],[],[0]),([22,1,2,18,4],[],[]),([22,5,2,3,9],[],[0]),([31,0,5,2,3],[],[1]),([15,22,16,2,3],[],[0]),([25,5,2,3,9],[],[1]),([0,5,6,8,9],[],[0,1]),([32,1,2,18,4],[],[]),([0,1,2,18,33],[],[]),([34,1,2,18,4],[],[]),([36,13,1,3,4],[],[]),([25,1,2,18,4],[],[]),([37,0,1,2,18],[],[]),([24,12,0,2,3],[],[1]),([11,0,5,1,4],[1,2],[0,1]),([0,38,2,3,39],[],[1]),([40,41,0,2,3],[],[1]),([11,0,1,4,9],[2],[0]),([15,11,0,1,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_4 : checkNodesBT W_10 g_10 F_10 P_10_4 A_10 B_10_3 4 N_10_4 = true := by decide +kernel
def B_10_4 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_4
set_option maxRecDepth 500000 in
lemma B_10_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 4 xs.toFinset) B_10_4 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_3_ok C_10_4
def P_10_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def N_10_5 : List NodeSpec := [([44,0,1,2],[0,1,3],[]),([0,45,1,2,3,4],[],[]),([15,37,0,1,2,3],[4],[]),([15,16,0,2,3,8],[5],[0,1]),([15,25,1,2,3,4],[],[0]),([46,13,1,2,3,4],[4,6,7],[]),([25,1,47,2,3,4],[7],[]),([22,16,1,2,3,4],[],[0]),([48,0,1,2,3,4],[],[]),([49,25,1,2,3,4],[7],[]),([0,38,1,2,3,33],[8,9,10,11],[0,1]),([0,1,50,2,3,4],[12],[1]),([40,0,1,2,3,33],[],[0]),([0,5,1,6,8,4],[10,13,14],[0,1]),([15,24,16,0,2,3],[],[0]),([51,25,1,3,4],[14,15,16],[]),([24,13,1,2,3,4],[4,17],[1]),([0,1,2,3,33,39],[8,9,10],[0,1]),([15,0,1,6,8,4],[],[0]),([25,1,2,3,4,27],[7],[0,1]),([15,22,1,2,3,4],[],[0]),([15,23,24,0,1,4],[],[0]),([0,1,2,3,53,43],[11,12],[]),([55,0,1,2,3,4],[],[]),([57,0,1,2,3,4],[],[]),([58,0,1,2,3,4],[],[]),([44,0,1,2,43],[0,1,3],[]),([0,1,2,3,4,59],[4,12,18,19],[]),([25,1,2,3,4,9],[7],[0,1]),([22,1,2,3,4,9],[7,20],[0]),([0,1,2,3,60,43],[10,11,12],[]),([0,1,2,3,10,4],[7,19],[0,1]),([22,5,1,2,3,4],[7,11,20,21],[0]),([25,5,1,2,3,4],[7,14,15,16],[0]),([61,0,1,2,18,4],[],[1]),([24,0,1,2,18,4],[10],[]),([0,5,1,2,3,33],[4,8,9,10,11],[0,1]),([0,1,2,3,9,33],[8,9,10,11,12],[1]),([11,0,1,4],[1,2],[0,1]),([15,0,1,2,3,33],[4],[]),([0,5,2,3,8,9],[4,22],[0,1]),([24,0,5,2,3,9],[],[0,1]),([0,1,2,7,3,4],[4,7,10,12,19],[0,1]),([37,0,5,1,2,3],[4,14],[0]),([31,0,1,2,3,4],[7,10,12,19],[0]),([15,16,0,6,2,3],[0,5,12],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_5 : checkNodesBT W_10 g_10 F_10 P_10_5 A_10 B_10_4 5 N_10_5 = true := by decide +kernel
def B_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_5
set_option maxRecDepth 500000 in
lemma B_10_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 5 xs.toFinset) B_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_4_ok C_10_5
def P_10_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 [0,1,4,5,6,7,8,10,11,12,14,15,16,20,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54]
def N_10_6 : List NodeSpec := [([62,63,0,1,2],[1,11,23,24],[0]),([0,1,2,3,4,43],[0,1,25],[]),([64,0,1,2,3,4,43],[0,12],[0]),([0,1,2,42,43],[0,1,11,26],[0]),([65,1,2,3,4],[0,1],[]),([0,1,2,3,66,4],[4,10,14,23,27],[]),([15,24,0,1,2,3,4],[0,12],[0]),([51,0,1,3,8,4],[10,11,14,23,28,29],[0]),([25,1,2,3,4],[1,7,14,15,16,30],[0,1]),([51,52,0,1,2,3,4],[1,4,10,12,14],[0]),([67,0,2,3,4],[10,11,12,31],[]),([0,1,2,3,33],[8,10,11],[0,1]),([37,0,1,2,3,4],[1,4,10,11,12,14,32],[0]),([0,1,3,68,4],[11,14,23,33],[]),([15,23,0,1,2,3,4],[1,10,12],[0,1]),([51,0,1,2,3,4,43],[10,11,14,23,34],[1]),([69,0,2,3,4],[11,12,23,35],[]),([0,1,2,3,70,4],[1,4,10,12,36],[1]),([0,71,2,72,4],[0,12,37,38],[]),([0,54,1,2,3,4,43],[1,4,10,11,12,23],[0,1]),([0,1,2,3,74,4],[0,1,10,39],[]),([22,1,2,3,4],[11,20],[0]),([0,54,75,3,4],[1,4,12,40,41],[]),([24,16,0,1,2,3,4],[4,14],[0,1]),([76,1,2,3,4],[0,1,4,42,43],[]),([0,1,2,3,56,4],[1,10,12,23,44],[0,1]),([0,1,77,3,4],[12,14,23,45],[]),([0,1,2,3,18,4],[10,12,14,23,46],[0,1]),([79,1,2,3,4],[0,1,4,47],[]),([0,1,2,3,8,4,9],[4,6,14,30],[0,1]),([80,0,1,2,3],[10,11,23,48],[]),([0,81,1,2,3,4,43],[0,12,23,49],[]),([0,5,1,6,2,3,4],[4,10,11,12,14,23,50,51],[0,1]),([0,1,2,3,83,4],[0,1,4,10,23,52],[]),([0,5,2,3,9],[4,12,22],[0,1]),([0,5,1,2,3,8,4],[4,10,11,12,14,23,30,51],[0,1]),([24,0,1,2,3,4,9],[4,10,12,14,53],[0,1]),([24,0,5,1,2,3,4],[10,11,12,14,53],[0,1]),([15,0,1,6,2,3,4],[0,12,54],[0]),([15,0,1,2,3,8,4],[0,12,14,54],[0]),([15,16,0,2,3],[4,5,12],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_6 : checkNodesBT W_10 g_10 F_10 P_10_6 A_10 B_10_5 6 N_10_6 = true := by decide +kernel
def B_10_6 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_6
set_option maxRecDepth 500000 in
lemma B_10_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 6 xs.toFinset) B_10_6 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_5_ok C_10_6
def P_10_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 [0,1,4,10,11,12,14,23,30,41,42,51,53,54,55,56,57,58,59,60,61,62,63,64]
def N_10_7 : List NodeSpec := [([62,0,1,2,3,4],[0,1,4,10,11,12,14,55],[0]),([0,71,1,2,3,4],[1,4,10,11,12,14,23,56],[0,1]),([0,54,1,2,3,4],[0,1,4,10,11,12,23,57],[0,1]),([0,1,2,75,3,4],[0,1,4,10,42],[0]),([0,1,2,3,72,4],[0,1,4,10,12,58],[0]),([84,0,1,2,3,4],[1,4,10,12,14,23,59,60],[1]),([85,0,1,2,3,4],[1,4,12,23,41,61],[1]),([24,0,1,2,3,4],[4,10,11,12,14,23,53],[0,1]),([0,5,1,2,3,4],[4,10,11,12,14,23,51],[0,1]),([0,1,2,3,8,4],[1,4,11,12,14,23,30],[0,1]),([15,0,1,2,3,4],[0,10,12,14,54],[0]),([0,1,2,42,3,4],[1,4,11,12,23,62],[0,1]),([51,0,1,2,3,4],[0,1,4,10,11,12,14,60,63],[0]),([0,1,2,3,4,43],[0,1,10,12,64],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_7 : checkNodesBT W_10 g_10 F_10 P_10_7 A_10 B_10_6 7 N_10_7 = true := by decide +kernel
def B_10_7 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_7
set_option maxRecDepth 500000 in
lemma B_10_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 7 xs.toFinset) B_10_7 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_6_ok C_10_7
def P_10_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 [19]
def N_10_8 : List NodeSpec := [([0,1,2,3,4],[19],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_8 : checkNodesBT W_10 g_10 F_10 P_10_8 A_10 B_10_7 8 N_10_8 = true := by decide +kernel
def B_10_8 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_8
set_option maxRecDepth 500000 in
lemma B_10_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 8 xs.toFinset) B_10_8 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_7_ok C_10_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck r_10 g_10 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT B_10_8 r_10 = true := by decide +kernel
lemma low_10 : Lower r_10 g_10 9 := lower_of_forestBT root_10_ok B_10_8_ok root_10_in
def g_11 := 0xfee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0
def r_11 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_11 : Lower r_11 g_11 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_12 := 0xffeef880ffeef880ffeef880ffeef880ffeef880ffeef880ffeef880ffeef880
def r_12 : List Nat := varsOf 31
def p_12 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,17,17,18,18,19,21,21,22,22,24,24,25,26,28]
def q_12 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,1,16,2,3,20,5,20,6,16,8,9,10,20]
def F_12 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_12 : goodPairs g_12 p_12 q_12 := goodPairs_of (by decide +kernel)
def W_12 : BT Decor := buildWiresBT 8 (mkBase p_12 q_12 r_12) [(0,0,1),(1,5,3),(1,2,4),(0,6,7),(1,3,4),(0,1,4),(1,1,4),(3,10,11),(1,2,3),(2,0,3),(1,0,4),(0,1,15),(3,16,3),(0,5,7),(1,18,3),(3,2,3),(1,0,1),(3,20,21),(0,2,6),(1,23,4),(0,0,11),(1,25,3),(3,2,26),(3,5,9),(1,6,4),(3,20,0),(2,21,3),(3,5,3),(1,5,4),(2,2,4),(3,34,6),(3,2,6),(2,5,3),(1,37,4),(1,16,3),(0,0,7),(3,3,33),(3,5,13),(0,3,4),(3,43,9),(0,0,9),(0,1,7),(3,46,0),(0,0,13),(1,48,4),(3,1,4),(1,20,50),(3,20,15),(0,13,15),(3,1,15),(0,0,4),(1,20,55),(3,10,13),(1,30,4),(0,1,13),(1,55,3),(1,2,60),(3,10,0),(2,1,3),(3,63,15),(3,14,15),(1,55,1),(1,14,4),(3,63,0),(1,68,4),(1,0,3),(3,5,70),(2,0,4),(3,0,4),(2,5,4),(1,74,3),(2,0,1),(1,20,76),(1,25,2),(0,21,13),(1,5,2),(2,3,4),(1,81,5),(2,6,4),(0,1,3),(3,84,15),(2,1,0),(1,14,86),(3,73,13),(3,84,0),(1,89,4),(1,1,3),(3,2,60),(2,1,2),(3,93,0),(2,14,4),(1,20,5),(3,20,1),(3,5,7),(3,86,13),(1,94,4),(3,93,15),(0,0,91),(0,0,3),(1,103,4),(3,3,4),(1,105,2),(1,2,43),(1,20,4),(2,13,4),(1,50,3),(3,3,15),(3,81,0),(3,10,3),(1,1,43),(1,1,2),(0,0,115),(1,76,3),(3,0,3),(1,118,1),(2,0,43),(3,2,70),(3,1,3),(3,122,0),(3,14,1),(1,55,2),(1,14,1),(2,0,2),(1,127,4),(1,50,2),(3,2,4),(1,0,2)]
lemma W_12_ok : btAll (fun x => faithful p_12 q_12 x ∧ x.1 < 2^256) W_12 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_12 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_12 : BT (List (Nat × Nat)) := btOfList 1 al_12
set_option maxHeartbeats 0 in
lemma A_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_12 = g_12) A_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_12_0 : Slice r_12 g_12 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_1 : Slice r_12 g_12 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_2 : Slice r_12 g_12 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_3 : Slice r_12 g_12 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88ffeeff88 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_4 : Slice r_12 g_12 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xeeee8080eeee8080eeee8080eeee8080eeee8080eeee8080eeee8080eeee8080 5 := carry_of (swaps := [(0,1),(1,2),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_5 : Slice r_12 g_12 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_8
set_option maxHeartbeats 0 in
lemma sl_12_6 : Slice r_12 g_12 (subcubeFast 8 4) 4 := by
  have hc : Lower (varsOf 19) 0xeeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_7 : Slice r_12 g_12 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_8 : Slice r_12 g_12 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_9 : Slice r_12 g_12 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xeeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_10 : Slice r_12 g_12 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xeeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8eeeec8c8 5 := carry_of (swaps := [(0,1),(1,3),(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_11 : Slice r_12 g_12 (identDom 0 1) 5 := by
  have hc : Lower (varsOf 29) 0xffaafaa0ffaafaa0ffaafaa0ffaafaa0ffaafaa0ffaafaa0ffaafaa0ffaafaa0 5 := carry_of (swaps := [(0,2),(1,4)]) (by decide +kernel) low_11
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_12 : Slice r_12 g_12 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 29) 0xffaaf000ffaaf000ffaaf000ffaaf000ffaaf000ffaaf000ffaaf000ffaaf000 4 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_13 : Slice r_12 g_12 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_12 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 4 0,6),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 8 4,4),some (subcubeFast 16 2,4),some (subcubeFast 16 1,4),some (identDom 0 3,5),some (identDom 1 3,5),some (identDom 0 1,5),some (subcubeFast 2 0,4),some (subcubeFast 1 0,4)]
lemma S_12_ok : btAll (fun o => ∀ p, o = some p → Slice r_12 g_12 p.1 p.2) S_12 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_12_0) (forall_cons (fun _ h => by cases h; exact sl_12_1) (forall_cons (fun _ h => by cases h; exact sl_12_2) (forall_cons (fun _ h => by cases h; exact sl_12_3) (forall_cons (fun _ h => by cases h; exact sl_12_4) (forall_cons (fun _ h => by cases h; exact sl_12_5) (forall_cons (fun _ h => by cases h; exact sl_12_6) (forall_cons (fun _ h => by cases h; exact sl_12_7) (forall_cons (fun _ h => by cases h; exact sl_12_8) (forall_cons (fun _ h => by cases h; exact sl_12_9) (forall_cons (fun _ h => by cases h; exact sl_12_10) (forall_cons (fun _ h => by cases h; exact sl_12_11) (forall_cons (fun _ h => by cases h; exact sl_12_12) (forall_cons (fun _ h => by cases h; exact sl_12_13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
def ps_12 : BT (Option PoolSpec) := btOfList 7 ((([(0,[(0,1,4),(1,1,4),(3,10,11)]),(0,[]),(2,[(1,5,4),(1,2,4)]),(11,[(1,5,3),(3,2,6)]),(8,[]),(7,[]),(0,[(0,3,4),(1,3,4),(3,43,9)]),(6,[]),(5,[]),(1,[(1,2,4),(1,3,4)]),(13,[]),(12,[]),(2,[]),(0,[(1,0,4),(0,13,15)]),(0,[(1,0,4),(3,1,15)]),(9,[]),(3,[]),(1,[]),(0,[(0,0,4),(1,20,55)]),(0,[(0,1,4),(3,10,13)]),(0,[(0,0,4),(1,0,4)]),(1,[(1,55,3)]),(0,[(0,0,4),(1,55,3)]),(0,[(0,1,4),(3,10,0)]),(4,[]),(0,[(0,0,4),(1,55,1)]),(1,[(1,1,4)]),(0,[(1,1,4),(0,0,11)]),(0,[(2,0,4),(3,0,4)]),(2,[(1,5,4)]),(5,[(0,0,1)]),(11,[(1,2,3)]),(0,[(0,0,1),(1,0,1)]),(2,[(1,2,4)]),(1,[(1,5,4),(1,2,4)]),(11,[]),(11,[(3,5,3)]),(0,[(2,1,3),(3,63,0)]),(11,[(1,5,2)]),(4,[(1,2,4)]),(11,[(3,2,3)]),(10,[]),(2,[(2,2,4)]),(4,[(2,2,4)]),(0,[(2,1,0),(3,86,13)]),(0,[(1,0,4),(3,93,15)]),(1,[(1,55,1)]),(11,[(1,5,3)]),(4,[(1,105,2)]),(0,[(0,3,4),(1,3,4)]),(0,[(2,3,4)]),(1,[(2,2,4)]),(0,[(0,0,7)]),(1,[(1,2,4)]),(0,[(1,20,4)]),(0,[(2,13,4)]),(0,[(0,0,13)]),(0,[(3,1,4)]),(0,[(1,0,4),(3,3,15)]),(0,[(1,0,4)]),(0,[(2,0,4)]),(0,[(0,0,4)]),(0,[(1,3,4)]),(1,[(2,3,4)]),(0,[(0,1,4),(3,10,3)]),(0,[(0,3,4),(1,1,43)]),(0,[(2,0,1)]),(5,[(2,1,0)]),(3,[(2,0,3)]),(0,[(0,0,1)]),(0,[(2,3,4),(3,3,4)]),(0,[(1,0,1)]),(0,[(0,0,115)]),(2,[(1,0,4)]),(0,[(2,0,1),(1,76,3)]),(0,[(3,93,0)]),(0,[(3,0,3),(1,118,1)]),(0,[(0,3,4),(2,0,43)]),(3,[(1,1,3)]),(0,[(3,20,0)]),(4,[(3,2,70)]),(2,[(2,0,4)]),(1,[(1,5,4)]),(0,[(3,1,3),(3,122,0)]),(1,[(1,127,4)]),(1,[(1,3,4)]),(0,[(2,0,3)]),(0,[(0,0,3),(1,0,3)]),(0,[(0,0,3)]),(0,[(1,1,3)]),(0,[(1,0,3)]),(1,[(1,14,4)]),(0,[(1,1,4)]),(0,[(0,3,4)]),(0,[(3,3,4)]),(0,[(3,1,3)])] : List PoolSpec)).map some)
def B_12_2 : BT (List (List Nat)) := BT.empty
lemma B_12_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 2 xs.toFinset) B_12_2 := .empty
def P_12_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 []
def N_12_3 : List NodeSpec := [([0,1,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_3 : checkNodesBT W_12 g_12 F_12 P_12_3 A_12 B_12_2 3 N_12_3 = true := by decide +kernel
def B_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_3
set_option maxRecDepth 500000 in
lemma B_12_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 3 xs.toFinset) B_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_2_ok C_12_3
def P_12_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 [0,1,2,3]
def N_12_4 : List NodeSpec := [([12,0,2,3,13],[0],[]),([14,17,16,2,4],[],[]),([0,1,19,4,7],[],[]),([5,22,2,3,4],[],[]),([0,1,3,6,24],[],[]),([20,12,0,2,3],[0],[]),([0,1,6,7,9],[],[0]),([27,25,1,3,4],[],[]),([28,0,1,3,7],[],[]),([0,1,3,7,29],[1],[]),([0,1,3,8,4],[1],[0]),([30,16,2,3,4],[],[]),([31,5,2,6,4],[],[]),([31,32,5,2,4],[],[]),([14,1,3,33,7],[2],[]),([0,1,3,35,4],[],[]),([36,5,21,3,4],[3],[]),([0,1,3,38,7],[],[]),([14,16,2,39,4],[],[]),([40,1,3,33,7],[2],[]),([41,0,1,3,7],[],[]),([42,21,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_4 : checkNodesBT W_12 g_12 F_12 P_12_4 A_12 B_12_3 4 N_12_4 = true := by decide +kernel
def B_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_4
set_option maxRecDepth 500000 in
lemma B_12_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 4 xs.toFinset) B_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_3_ok C_12_4
def P_12_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47]
def N_12_5 : List NodeSpec := [([44,0,1,2],[4,5,6,7],[]),([45,0,1,3,7,9],[4,8,9],[]),([47,0,1,3,4,7],[],[]),([0,1,2,3,4,49],[10,11,12],[]),([51,0,1,2,3,4],[1],[]),([0,1,2,52,3,4],[],[]),([30,1,2,3,4,15],[],[0]),([0,1,2,3,53,4],[13],[]),([54,0,2,3,13,4],[14],[]),([0,1,2,3,26,4],[1,15,16],[]),([17,0,16,2,3,4],[5,11,17],[0]),([0,56,1,2,3,4],[1,18],[]),([57,0,1,2,3,4],[1,19],[]),([0,1,2,3,4,58],[],[]),([50,0,59,2,3,4],[16],[]),([55,1,2,3,13,15],[20],[1]),([20,0,1,2,60,4],[1],[]),([0,1,2,60,13,4],[1,15,21],[]),([0,1,2,60,61,4],[15,21,22],[]),([20,62,1,2,3,4],[23],[]),([62,1,2,3,13,4],[23],[]),([0,1,2,3,64,4],[17],[]),([14,16,1,2,3,4],[5,24],[]),([14,16,2,3,4],[4,5,17],[0]),([14,1,2,3,65,4],[17],[]),([20,0,66,2,3,4],[25],[]),([0,1,2,3,67,9],[15,24],[]),([34,68,0,1,3,4],[],[]),([20,54,0,2,3,4],[14],[]),([25,1,2,3,26,4],[10,12,26,27],[0,1]),([0,1,2,3,4,69],[17],[]),([71,5,1,2,3,4],[17],[]),([72,20,73,1,2,3],[28],[1]),([68,1,2,3,4,15],[11],[]),([0,1,2,3,75,4],[1,16],[]),([0,1,3,6,4,7],[8,16],[0]),([0,1,2,6,13,4],[1],[]),([14,1,2,3,4,33],[4,29,30],[0]),([5,21,2,3,13,4],[11,31,32],[0]),([5,40,1,3,4,7],[16,33],[0]),([5,0,1,3,33,7],[2,5,8,34],[]),([77,0,1,2,3,4],[],[]),([32,5,21,2,3,4],[11,17,35,36],[0]),([25,1,2,78,3,4],[27],[]),([31,5,2,3,4],[5,17,30,35],[0]),([0,1,79,2,3,4],[],[]),([34,37,0,1,3,4],[],[]),([68,1,2,3,70,4],[17,37],[]),([0,1,2,3,33,9],[4,5,10,11,24],[]),([0,1,2,3,6,4],[1,16],[]),([0,1,2,3,4,38],[],[0]),([34,0,1,3,6,4],[1],[0]),([37,0,1,3,4,7],[8],[0]),([5,21,2,80,3,4],[32,38],[]),([36,5,0,1,3,4],[],[0]),([18,0,1,3,4,7],[1,8,39],[0]),([20,55,1,2,3,15],[20],[1]),([82,0,1,2,3,4],[1,16],[]),([25,1,2,3,13,4],[27],[]),([83,0,1,2,3,4],[1,16],[]),([20,5,21,2,3,4],[17,32,40],[0]),([0,1,2,3,33,7],[1,5,10,11],[]),([36,0,1,3,6,4],[1],[]),([41,0,1,2,3,4],[],[0]),([85,0,1,2,3,4],[17],[]),([81,0,1,2,6,4],[],[]),([0,1,23,3,6,4],[16],[0]),([0,1,2,6,4,9],[8,15,41],[0]),([68,0,1,3,4,7],[],[]),([14,87,1,2,3,4],[17],[]),([0,1,3,33,7],[1,4,5,34],[0,1]),([88,0,1,2,3,4],[1],[]),([0,1,2,3,4,90],[17],[]),([20,0,1,2,6,4],[1],[]),([5,2,3,70,91,4],[17,24],[]),([14,5,2,3,91,4],[12,24],[]),([92,0,1,2,60,4],[22],[]),([14,63,5,2,3,4],[12,17,24],[]),([14,5,1,3,4,7],[33,39],[0]),([94,1,2,3,4,15],[11],[]),([34,14,5,1,3,4],[42,43],[]),([95,0,1,3,7,9],[4],[]),([0,1,2,3,4,29],[1,12,16,17],[0]),([96,0,1,2,3,4],[16],[]),([76,0,97,2,3,4],[],[]),([98,0,1,3,4,7],[1,8],[]),([20,25,1,2,3,4],[12,27],[1]),([98,0,1,2,3,4],[16],[]),([28,0,1,2,3,4],[],[0]),([44,0,1,2,9],[4,5,6,7,24],[]),([48,1,21,2,3,4],[11],[]),([89,1,2,3,4,15],[8,11],[]),([42,0,1,2,3,4],[],[0]),([5,0,1,3,7,9],[4,5,39],[0]),([0,1,22,2,3,4],[],[0]),([0,99,1,2,3,4],[44],[]),([34,89,0,1,3,4],[],[]),([0,1,2,3,4,100],[17],[]),([72,73,1,2,3,13],[28],[1]),([0,1,2,101,3,4],[45],[]),([12,0,2,3],[0,4,5],[0]),([0,66,2,3,13,4],[10,25,46],[]),([5,21,2,3,6,4],[11,17,32,47],[0]),([102,1,2,3,70,4],[17],[]),([0,1,2,3,104,11],[4,10,11],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_5 : checkNodesBT W_12 g_12 F_12 P_12_5 A_12 B_12_4 5 N_12_5 = true := by decide +kernel
def B_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_5
set_option maxRecDepth 500000 in
lemma B_12_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 5 xs.toFinset) B_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_4_ok C_12_5
def P_12_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 [1,4,5,7,8,10,11,12,14,15,16,17,20,21,22,23,24,25,26,27,28,29,30,31,32,33,35,37,39,40,41,42,43,46,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92]
def N_12_6 : List NodeSpec := [([0,1,106,3,4],[5,7,16,48],[]),([0,1,2,3,4,9],[4,5,7],[]),([45,0,1,2,3,4],[1,4,8,10,11,12,15,16,17],[]),([0,1,2,43,9],[4,5,7,49],[0]),([0,1,3,107,4],[5,16,24],[]),([34,81,0,1,3,4],[1,4,5,8,42,43,50,51],[]),([0,1,3,4,7],[5,7],[]),([40,0,1,2,3,4],[4,7,10,11,12,16,17,24,52],[]),([40,0,1,3,4,7],[1,4,7,8,16,33,39,53],[0,1]),([0,1,2,3,4,108],[10,11,12,16,17,24,54],[]),([109,0,1,2,3,4],[1,7,10,11,12,16,17,24,55],[]),([48,0,1,2,3,4],[7,8,10,11,12,16,17,56],[0,1]),([20,50,0,1,2,3,4],[1,12,16,57],[0,1]),([0,1,2,3,110,4],[1,4,12,16],[]),([72,73,1,2,3],[4,5,28],[0,1]),([111,0,1,2,3,4],[1,4,11,12,16,17,24,41,58],[]),([0,1,3,4,7,9],[4,5,7,39],[]),([20,0,1,2,3,4,15],[16,17,59],[0,1]),([72,20,0,1,2,3,4],[1,4,10,16,60],[0]),([0,1,2,3,13,4,15],[16,17,59],[0,1]),([54,0,2,3,4],[5,12,14,17],[0]),([25,0,1,2,3,4],[1,4,5,10,12,15,16,17,24,26,27],[0,1]),([25,1,2,3,4],[4,5,10,12,27],[0,1]),([20,55,0,1,2,3,4],[1,8,16,24,61],[0,1]),([34,0,1,3,4,9],[4,5,7,62],[]),([55,0,1,2,3,13,4],[1,8,10,16,17,24,61],[0,1]),([55,1,2,3,15],[5,8,17,20],[0,1]),([112,0,1,2,3,4],[1,4,10,11,12,16,17,24,63],[]),([113,0,1,2,4],[5,7,24,64],[]),([0,2,3,114,4],[7,8,12,65],[]),([0,1,2,3,60,4],[4,5,16,22],[0]),([0,1,2,60,4],[4,5,21,22],[0]),([62,1,2,3,4],[4,5,23],[0]),([0,66,2,3,4],[4,12,25,46],[0]),([20,76,0,1,2,3,4],[1,12,16,40,66],[0]),([14,86,1,2,3,4],[4,10,12,17,24,67,68],[0]),([0,1,3,7,9],[4,5,7,39],[0,1]),([5,0,1,2,3,4,7],[1,5,8,10,11,16,17,69],[0]),([81,105,0,1,2],[5,7,8,24,70],[0]),([5,0,1,2,3,4],[1,5,8,10,11,12,15,16,17,24],[0]),([20,0,1,21,2,3,4],[1,16,17,71],[0]),([37,0,1,2,3,4],[1,8,10,11,15,16],[0]),([31,0,1,2,3,4],[1,5,8,12,16,17],[0]),([116,0,1,2,3,4],[1,5,7,8,12,24,72],[]),([50,0,1,2,3,13,4],[1,12,16,57],[0,1]),([102,0,1,2,3,4],[1,5,8,12,15,16,17],[0]),([34,5,0,1,3,4],[1,4,5,43,51,69],[0,1]),([103,0,1,2,3,4,11],[4,8,10,12,24],[0,1]),([14,1,2,3,4,15],[4,8,17,24,68,73],[0]),([0,1,2,3,117,4],[5,10,12,16,17,74],[]),([94,0,1,2,3,4],[1,7,8,10,11,16,17,24,75],[0]),([0,119,2,3,4],[5,7,12,17,24,76],[]),([120,1,2,3,4],[5,7,77],[]),([0,1,21,2,3,13,4],[12,16,17,71],[0,1]),([14,0,1,2,3,4],[1,4,10,11,12,15,16,24],[]),([76,0,1,2,3,13,4],[10,12,16,17,31,66],[1]),([14,0,1,3,4,7],[4,7,8,33,39,53],[0,1]),([0,1,2,3,6,4],[1,8,10,11,12,16,17],[0]),([32,5,0,1,2,3,4],[10,11,12,17,24],[0]),([5,0,2,3,91,4],[5,11,12,17,24,78],[0,1]),([95,0,1,2,3,4,9],[4,15],[0]),([30,0,1,2,3,4],[1,8,10,11,12,16,17,24,79],[0,1]),([121,0,1,3,4],[4,7,16,17,80],[]),([72,14,1,2,3,4],[4,8,10,24,81],[]),([5,0,1,3,4,7],[4,5,8,16,33,39,53,69],[0,1]),([0,1,2,3,4,33],[1,4,5,11,16,24,82],[0,1]),([72,93,0,1,2,3,4],[4,5,10,16],[]),([105,0,1,3,7],[5,7,8],[]),([123,0,1,2,3,4],[1,5,7,8,12,16,24,83],[]),([5,0,1,2,3,4,33],[5,11,29,82],[0]),([20,5,0,1,2,3,4],[1,10,11,12,16,17,24,69],[0]),([14,0,124,1,2,3,4],[10,12,15,17,24],[]),([0,1,125,3,4],[5,7,16],[]),([14,0,1,126,2,3,4],[10,11,15,17],[]),([5,21,2,3,4],[5,11,32,35],[0]),([0,1,2,3,4,128],[4,7,11,12,84],[]),([45,0,1,2,3,4,9],[4,8,15,85],[0]),([81,5,0,1,2,3,4],[4,5,10,11,12,17,24],[0]),([34,14,0,1,3,4],[1,4,7,8,42,51,86],[0,1]),([5,0,1,2,80,3,4],[16,69],[0]),([14,5,1,2,3,4],[4,10,12,17,24,30,68],[0]),([74,0,1,2,3,4],[1,4,5,10,11,15,16,24],[0]),([0,1,2,3,4,104],[4,7,11,12,24],[0]),([0,1,129,3,4],[7,8,12,16],[]),([103,1,2,70,4],[4,7,15,24,87],[]),([5,0,1,2,3,13,4],[1,11,16,24,69],[0]),([14,0,1,2,3,4,9],[4,7,8,15,85],[0]),([89,0,1,2,3,4],[1,7,8,10,11,15,16,17,24],[0]),([72,0,84,1,2,3,4],[4,5,10,24],[]),([34,103,0,1,3,4],[1,4,7,42,88],[1]),([68,0,1,2,3,4],[1,8,10,11,12,15,16,17,24,37],[0]),([0,1,2,3,70,91,4],[7,12,17,24,89,90],[0,1]),([14,0,1,2,3,91,4],[7,12,15,17,24,86],[0,1]),([5,0,1,2,3,6,4],[10,11,12,17,24,69],[0]),([14,0,1,2,3,4,67],[4,10,15,91],[]),([95,0,1,2,3,4],[1,4,11,12,15,16],[]),([127,0,1,2,3,4,11],[4,10,12,16,17,92],[1]),([0,1,2,3,4,67],[1,4,11,12,15,16,91],[0]),([5,0,1,2,3,4,9],[4,5,8,10,11,24],[0]),([14,0,1,2,3,4,11],[4,10,12,15],[1]),([14,63,0,1,2,3,4],[12,15,17,24,41],[0]),([72,0,1,2,3,13,4],[4,10,16,60],[0]),([72,63,0,1,2,3,4],[4,5,10,11,12,15],[]),([123,1,2,3,4],[5,7,12,83],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_6 : checkNodesBT W_12 g_12 F_12 P_12_6 A_12 B_12_5 6 N_12_6 = true := by decide +kernel
def B_12_6 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_6
set_option maxRecDepth 500000 in
lemma B_12_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 6 xs.toFinset) B_12_6 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_5_ok C_12_6
def P_12_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 [1,4,5,7,8,10,11,12,15,16,17,24,35,41,50,57,59,60,61,62,66,69,71,86,88,90,93,94,95]
def N_12_7 : List NodeSpec := [([0,1,2,3,4,9],[4,5,7,62],[0,1]),([130,0,1,2,3,4],[1,4,5,7,12,16,17],[0]),([0,1,2,43,3,4],[1,4,5,7,17,93],[0,1]),([0,1,2,3,4,7],[1,4,5,7,16],[0,1]),([20,0,1,2,3,4],[1,8,12,16,17,24],[0,1]),([0,1,3,4,7],[1,4,5,7],[0,1]),([0,1,2,3,13,4],[1,7,8,12,17,24],[0,1]),([0,1,21,2,3,4],[1,5,12,16,17,24,71],[0]),([34,0,1,3,4],[1,4,5],[0,1]),([0,1,2,3,4,15],[4,5,16,17,24,59],[0,1]),([76,0,1,2,3,4],[1,5,10,12,16,17,24,35,66],[0,1]),([0,1,2,131,3,4],[1,4,7,12,17],[1]),([5,0,1,2,3,4],[1,4,5,8,10,11,12,16,17,24,69],[0,1]),([0,1,2,3,70,4],[1,4,7,12,17,90],[0,1]),([81,0,1,2,3,4],[1,4,5,7,12,16,17,24,50],[0,1]),([127,0,1,2,3,4],[1,4,7,8,10,12,16,17],[0,1]),([103,0,1,2,3,4],[1,4,7,8,10,12,16,17,24,88],[0,1]),([14,0,1,2,3,4],[1,4,7,8,10,12,15,16,17,24,86],[0,1]),([105,0,1,2,3,4],[1,4,5,7,8,12,16,17,94],[0]),([122,0,1,2,3,4],[1,5,7,12,16,17,24,41,95],[0,1]),([55,0,1,2,3,4],[1,4,5,8,12,16,24,61],[0,1]),([72,0,1,2,3,4],[1,4,5,8,12,16,24,60],[0]),([50,0,1,2,3,4],[1,4,12,16,17,24,57],[0,1])]
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
lemma root_12_ok : forestRootCheck r_12 g_12 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT B_12_8 r_12 = true := by decide +kernel
lemma low_12 : Lower r_12 g_12 9 := lower_of_forestBT root_12_ok B_12_8_ok root_12_in
def g_13 := 0xfffefee0fffefee0fffefee0fffefee0fffefee0fffefee0fffefee0fffefee0
def r_13 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_13 : Lower r_13 g_13 8 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_14 := 0xfffffee8fffffee8fffffee8fffffee8fffffee8fffffee8fffffee8fffffee8
def r_14 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 8 := by
  exact lift_of_f (z := 16) (o := 0) (other := r_1) (G := g_1) (essPairs := [(VAR 4,0,16)]) (by decide +kernel) low_1
def g_15 := 0xfef8e800fef8e800fef8e800fef8e800fef8e800fef8e800fef8e800fef8e800
def r_15 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 8 := by
  have hc : Lower (varsOf 27) 0xee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 4) (o := 0) (essPairs := [(VAR 2,9,13)]) (by decide +kernel) hc
def g_16 := 0xe800e800e800e800e800e800e800e800e800e800e800e800e800e800e800e800
def r_16 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_16 : Lower r_16 g_16 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_17 := 0xfff8e800fff8e800fff8e800fff8e800fff8e800fff8e800fff8e800fff8e800
def r_17 : List Nat := varsOf 31
def p_17 : List Nat := [11,11,11,13,13,13,14,14,14,15,19,19,19,20,20,21,21,22,22,23,24,24,25,25,26,26,28]
def q_17 : List Nat := [10,9,3,12,9,5,12,10,6,7,18,17,3,16,4,17,5,18,6,7,16,8,17,9,18,10,12]
def F_17 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 3 (mkBase p_17 q_17 r_17) [(1,2,4)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^256) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[]]
def A_17 : BT (List (Nat × Nat)) := btOfList 1 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfff0a000fff0a000fff0a000fff0a000fff0a000fff0a000fff0a000fff0a000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffafa00fffafa00fffafa00fffafa00fffafa00fffafa00fffafa00fffafa00 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xff888800ff888800ff888800ff888800ff888800ff888800ff888800ff888800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfff0c000fff0c000fff0c000fff0c000fff0c000fff0c000fff0c000fff0c000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_16
set_option maxHeartbeats 0 in
lemma sl_17_7 : Slice r_17 g_17 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_17_8 : Slice r_17 g_17 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) 0xf8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_17 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 1 0,5),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (identDom 2 3,6)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (forall_cons (fun _ h => by cases h; exact sl_17_7) (forall_cons (fun _ h => by cases h; exact sl_17_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_17 : BT (Option PoolSpec) := btOfList 4 ((([(4,[]),(0,[]),(1,[]),(2,[]),(5,[(1,2,4)]),(3,[]),(6,[]),(7,[]),(5,[]),(8,[])] : List PoolSpec)).map some)
def B_17_5 : BT (List (List Nat)) := BT.empty
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 := .empty
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 [0,1,2,3,4,5,6,7]
def N_17_6 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6 = true := by decide +kernel
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_5_ok C_17_6
def P_17_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 [0,1,2,3,5,6,7,8,9]
def N_17_7 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,5,6,7,8,9],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7 = true := by decide +kernel
def B_17_7 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_7
set_option maxRecDepth 500000 in
lemma B_17_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 7 xs.toFinset) B_17_7 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_6_ok C_17_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_7 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 8 := lower_of_forestBT root_17_ok B_17_7_ok root_17_in
def g_18 := 0xfffee880fffee880fffee880fffee880fffee880fffee880fffee880fffee880
def r_18 : List Nat := varsOf 31
def p_18 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,17,17,18,18,19,20,20,21,22,24,24,25,26,28]
def q_18 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,16,1,16,2,3,16,4,5,6,16,8,9,10,12]
def F_18 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_18 : goodPairs g_18 p_18 q_18 := goodPairs_of (by decide +kernel)
def W_18 : BT Decor := buildWiresBT 3 (mkBase p_18 q_18 r_18) [(1,0,1),(1,2,3),(0,5,6)]
lemma W_18_ok : btAll (fun x => faithful p_18 q_18 x ∧ x.1 < 2^256) W_18 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_18 : List (List (Nat × Nat)) := [[],[(1,2)],[(1,2),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)]]
def A_18 : BT (List (Nat × Nat)) := btOfList 3 al_18
set_option maxHeartbeats 0 in
lemma A_18_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_18 = g_18) A_18 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_18_0 : Slice r_18 g_18 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_18_1 : Slice r_18 g_18 (subcubeFast 2 0) 6 := by
  have hc : Lower (varsOf 29) 0xfffaa000fffaa000fffaa000fffaa000fffaa000fffaa000fffaa000fffaa000 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_2 : Slice r_18 g_18 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_3 : Slice r_18 g_18 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) 0xfefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_4 : Slice r_18 g_18 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_5 : Slice r_18 g_18 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_6 : Slice r_18 g_18 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_7 : Slice r_18 g_18 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffffee88ffffee88ffffee88ffffee88ffffee88ffffee88ffffee88ffffee88 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_8 : Slice r_18 g_18 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
def S_18 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 16 0,7),some (subcubeFast 2 0,6),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,6),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5)]
lemma S_18_ok : btAll (fun o => ∀ p, o = some p → Slice r_18 g_18 p.1 p.2) S_18 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_18_0) (forall_cons (fun _ h => by cases h; exact sl_18_1) (forall_cons (fun _ h => by cases h; exact sl_18_2) (forall_cons (fun _ h => by cases h; exact sl_18_3) (forall_cons (fun _ h => by cases h; exact sl_18_4) (forall_cons (fun _ h => by cases h; exact sl_18_5) (forall_cons (fun _ h => by cases h; exact sl_18_6) (forall_cons (fun _ h => by cases h; exact sl_18_7) (forall_cons (fun _ h => by cases h; exact sl_18_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_18 : BT (Option PoolSpec) := btOfList 4 ((([(1,[(1,2,3)]),(4,[]),(5,[]),(6,[]),(2,[]),(7,[]),(3,[]),(8,[]),(2,[(1,0,1)]),(1,[]),(0,[(1,0,1)]),(3,[(1,0,1)]),(0,[])] : List PoolSpec)).map some)
def B_18_4 : BT (List (List Nat)) := BT.empty
lemma B_18_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 4 xs.toFinset) B_18_4 := .empty
def P_18_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_18 r_18 S_18 ps_18 []
def N_18_5 : List NodeSpec := [([0,1,7,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_5 : checkNodesBT W_18 g_18 F_18 P_18_5 A_18 B_18_4 5 N_18_5 = true := by decide +kernel
def B_18_5 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_5
set_option maxRecDepth 500000 in
lemma B_18_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 5 xs.toFinset) B_18_5 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_4_ok C_18_5
def P_18_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_18 r_18 S_18 ps_18 [0,1,2,3,4,5,6,7,8]
def N_18_6 : List NodeSpec := [([0,1,5,2,3,6,4],[0,1,2,3,4,5,6,7,8],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_6 : checkNodesBT W_18 g_18 F_18 P_18_6 A_18 B_18_5 6 N_18_6 = true := by decide +kernel
def B_18_6 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_6
set_option maxRecDepth 500000 in
lemma B_18_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 6 xs.toFinset) B_18_6 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_5_ok C_18_6
def P_18_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_18 r_18 S_18 ps_18 [1,2,4,5,6,7,8,9,10,11]
def N_18_7 : List NodeSpec := [([0,1,5,2,3,4],[1,2,4,5,6,7,8,9,10,11],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_7 : checkNodesBT W_18 g_18 F_18 P_18_7 A_18 B_18_6 7 N_18_7 = true := by decide +kernel
def B_18_7 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_7
set_option maxRecDepth 500000 in
lemma B_18_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 7 xs.toFinset) B_18_7 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_6_ok C_18_7
def P_18_8 : BT (Option BoundPool) := buildPoolsSubBT 4 W_18 r_18 S_18 ps_18 [1,4,6,9,12]
def N_18_8 : List NodeSpec := [([0,1,2,3,4],[1,4,6,9,12],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_8 : checkNodesBT W_18 g_18 F_18 P_18_8 A_18 B_18_7 8 N_18_8 = true := by decide +kernel
def B_18_8 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_8
set_option maxRecDepth 500000 in
lemma B_18_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 8 xs.toFinset) B_18_8 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_7_ok C_18_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_ok : forestRootCheck r_18 g_18 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_in : bucketContainsBT B_18_8 r_18 = true := by decide +kernel
lemma low_18 : Lower r_18 g_18 9 := lower_of_forestBT root_18_ok B_18_8_ok root_18_in
def g_19 := 0xffecf800ffecf800ffecf800ffecf800ffecf800ffecf800ffecf800ffecf800
def r_19 : List Nat := varsOf 31
def p_19 : List Nat := [11,11,11,12,12,13,13,14,14,15,18,18,19,19,21,21,21,22,22,23,24,24,25,25,26,28]
def q_19 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,2,17,3,20,17,5,20,6,7,16,8,17,9,10,20]
def F_19 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_19 : goodPairs g_19 p_19 q_19 := goodPairs_of (by decide +kernel)
def W_19 : BT Decor := buildWiresBT 6 (mkBase p_19 q_19 r_19) [(0,3,4),(1,3,4),(3,5,6),(2,7,2),(0,7,1),(2,7,0),(1,2,3),(0,0,11),(1,2,4),(0,3,13),(1,0,5),(1,2,5),(1,13,3),(3,2,17),(1,1,5),(3,0,6),(0,7,0),(2,1,5),(0,0,6),(2,0,5),(0,1,6),(0,2,6),(2,3,4),(3,1,4),(1,28,3),(3,2,29),(1,1,2),(1,31,3),(2,32,4),(0,0,31),(2,31,4),(1,1,3),(1,36,4),(3,2,37),(3,2,3),(0,0,4),(1,40,3),(3,2,41),(3,5,4),(2,2,5),(3,1,37),(3,2,36),(3,13,3),(1,1,4),(3,2,48),(2,11,4),(2,0,4),(3,51,3),(1,43,1),(3,40,3),(1,51,3),(2,36,4),(0,0,3)]
lemma W_19_ok : btAll (fun x => faithful p_19 q_19 x ∧ x.1 < 2^256) W_19 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_19 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_19 : BT (List (Nat × Nat)) := btOfList 1 al_19
set_option maxHeartbeats 0 in
lemma A_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_19 = g_19) A_19 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_19_0 : Slice r_19 g_19 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_1 : Slice r_19 g_19 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xffa0f000ffa0f000ffa0f000ffa0f000ffa0f000ffa0f000ffa0f000ffa0f000 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_2 : Slice r_19 g_19 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800ffcc8800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_3 : Slice r_19 g_19 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_4 : Slice r_19 g_19 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_5 : Slice r_19 g_19 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) 0xececc8c8ececc8c8ececc8c8ececc8c8ececc8c8ececc8c8ececc8c8ececc8c8 6 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_6 : Slice r_19 g_19 (identDom 2 4) 6 := by
  have hc : Lower (varsOf 15) 0xf8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0f8e0 6 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_3
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_7 : Slice r_19 g_19 (identDom 0 1) 5 := by
  have hc : Lower (varsOf 29) 0xffaafa00ffaafa00ffaafa00ffaafa00ffaafa00ffaafa00ffaafa00ffaafa00 5 := carry_of (swaps := [(0,1),(1,4),(2,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_8 : Slice r_19 g_19 (identDom 0 4) 5 := by
  have hc : Lower (varsOf 15) 0xfaa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8 5 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_6
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_9 : Slice r_19 g_19 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xeeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_10 : Slice r_19 g_19 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_19 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 4 1,4),some (subcubeFast 2 1,4),some (identDom 1 3,6),some (identDom 2 4,6),some (identDom 0 1,5),some (identDom 0 4,5),some (identDom 0 3,5),some (subcubeFast 1 0,4)]
lemma S_19_ok : btAll (fun o => ∀ p, o = some p → Slice r_19 g_19 p.1 p.2) S_19 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_19_0) (forall_cons (fun _ h => by cases h; exact sl_19_1) (forall_cons (fun _ h => by cases h; exact sl_19_2) (forall_cons (fun _ h => by cases h; exact sl_19_3) (forall_cons (fun _ h => by cases h; exact sl_19_4) (forall_cons (fun _ h => by cases h; exact sl_19_5) (forall_cons (fun _ h => by cases h; exact sl_19_6) (forall_cons (fun _ h => by cases h; exact sl_19_7) (forall_cons (fun _ h => by cases h; exact sl_19_8) (forall_cons (fun _ h => by cases h; exact sl_19_9) (forall_cons (fun _ h => by cases h; exact sl_19_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_19 : BT (Option PoolSpec) := btOfList 5 ((([(2,[]),(8,[]),(4,[]),(3,[]),(0,[]),(10,[]),(5,[]),(1,[]),(6,[]),(6,[(1,3,4)]),(1,[(0,0,31)]),(7,[]),(2,[(0,0,31)]),(0,[(1,1,2)]),(9,[]),(2,[(0,0,11)]),(5,[(3,1,4),(1,28,3)]),(5,[(2,3,4)]),(5,[(1,3,4)]),(6,[(3,2,3)])] : List PoolSpec)).map some)
def B_19_2 : BT (List (List Nat)) := BT.empty
lemma B_19_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 2 xs.toFinset) B_19_2 := .empty
def P_19_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_19 r_19 S_19 ps_19 []
def N_19_3 : List NodeSpec := [([8,7,0,1],[],[]),([9,7,0,2],[],[]),([10,7,1,2],[],[]),([12,1,14,4],[],[]),([1,15,16,6],[],[]),([7,0,1,16],[],[]),([7,18,0,1],[],[]),([0,19,16,6],[],[]),([7,20,1,2],[],[]),([21,7,1,2],[],[]),([22,7,0,2],[],[]),([7,23,1,2],[],[]),([7,1,2,15],[],[]),([7,0,1,2],[],[]),([24,7,1,2],[],[]),([0,25,26,5],[],[]),([7,0,25,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_3 : checkNodesBT W_19 g_19 F_19 P_19_3 A_19 B_19_2 3 N_19_3 = true := by decide +kernel
def B_19_3 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_3
set_option maxRecDepth 500000 in
lemma B_19_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 3 xs.toFinset) B_19_3 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_2_ok C_19_3
def P_19_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_19 r_19 S_19 ps_19 []
def N_19_4 : List NodeSpec := [([27,7,0,1,2],[],[]),([18,0,25,3,4],[],[]),([0,25,26,3,4],[],[0]),([7,0,1,2,3],[],[]),([1,3,15,16,4],[],[0]),([18,0,1,5,6],[],[0]),([18,0,1,3,4],[],[]),([0,1,14,11,4],[],[0]),([0,25,2,5,6],[],[0]),([30,0,1,3,4],[],[]),([7,0,1,2,6],[],[0,1]),([27,0,2,19,4],[],[]),([33,0,1,2,3],[],[]),([34,1,3,4,13],[],[]),([7,0,1,2],[],[0,1]),([35,28,0,2,3],[],[]),([23,25,2,3,4],[],[]),([0,1,2,14,6],[],[]),([38,0,1,3,4],[],[]),([39,34,1,3,4],[],[]),([7,0,1,2,5],[],[0,1]),([39,12,1,3,4],[],[]),([42,0,1,3,4],[],[]),([24,1,2,5,6],[],[0]),([18,20,1,3,4],[],[]),([27,43,0,1,2],[],[0]),([12,1,3,4,13],[],[0]),([1,2,5,15,6],[],[0,1]),([24,1,3,16,4],[],[]),([18,23,1,3,4],[],[]),([24,22,2,3,4],[],[]),([0,3,19,16,4],[],[0]),([22,0,3,16,4],[],[]),([0,1,5,16,6],[],[0]),([22,44,0,3,4],[],[]),([22,0,2,5,6],[],[0]),([0,1,2,5,6],[],[0]),([23,1,2,5,6],[],[0]),([18,45,0,3,4],[],[]),([20,1,2,5,6],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_4 : checkNodesBT W_19 g_19 F_19 P_19_4 A_19 B_19_3 4 N_19_4 = true := by decide +kernel
def B_19_4 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_4
set_option maxRecDepth 500000 in
lemma B_19_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 4 xs.toFinset) B_19_4 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_3_ok C_19_4
def P_19_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_19 r_19 S_19 ps_19 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]
def N_19_5 : List NodeSpec := [([27,43,0,1,2],[],[0,1]),([18,0,1,3,4,6],[0],[0]),([18,0,1,2,3,4],[],[]),([20,1,2,3,4,6],[1,2,3],[0,1]),([23,1,2,3,4],[],[]),([27,0,1,2,3,4],[],[0]),([27,0,1,2,5,4],[4],[0]),([18,0,1,3,4],[],[]),([23,1,2,3,4,6],[4],[0,1]),([46,0,1,2,3,4],[],[]),([0,1,2,14,3,4],[4,5,6,7,8],[0]),([35,0,1,2,3,4],[0],[0]),([0,1,2,3,4,6],[0,1,4,7],[0,1]),([47,0,1,2,3,4],[],[]),([49,0,1,2,3,4],[],[]),([50,0,1,2,3,4],[],[]),([39,0,1,31,3,4],[7],[0,1]),([27,43,0,1,2,3],[],[0]),([0,1,2,5,3,6],[9],[0]),([34,1,2,31,3,4],[4,10],[]),([0,1,2,52,3,4],[5,6,7],[]),([0,1,53,2,3,4],[4,11],[]),([54,0,1,2,3,4],[],[]),([0,25,2,3,4,6],[2],[0,1]),([0,1,2,3,55,4],[],[]),([0,1,2,3,32,4],[4,8,11],[0]),([0,1,31,3,4,13],[7,8],[0]),([34,1,2,3,4],[10,12,13],[0,1]),([1,2,5,3,15,4],[2,3,5],[0,1]),([0,1,2,3,41,4],[0,14],[0]),([12,1,2,3,11,4],[4,15],[0]),([12,1,2,3,4],[15],[0]),([39,0,1,3,11,4],[0],[0]),([22,0,2,5,3,4],[2,6],[0]),([27,0,1,2,36,4],[7],[]),([0,1,3,11,4,13],[8],[0]),([0,1,2,3,4,37],[0,4,11],[0,1]),([56,0,1,2,3,4],[],[]),([0,1,2,3,29,4],[0,4,14,16],[0,1]),([27,0,1,2,3,6],[4],[0]),([0,1,2,3,13,6],[0],[0]),([24,1,2,5,3,4],[4],[0,1]),([24,1,2,3,4],[],[]),([0,1,2,5,3,4],[0,4,5,6,7,8],[0]),([0,1,2,5,6],[],[0,1]),([0,1,5,3,16,4],[0],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_5 : checkNodesBT W_19 g_19 F_19 P_19_5 A_19 B_19_4 5 N_19_5 = true := by decide +kernel
def B_19_5 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_5
set_option maxRecDepth 500000 in
lemma B_19_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 5 xs.toFinset) B_19_5 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_4_ok C_19_5
def P_19_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_19 r_19 S_19 ps_19 [0,1,2,3,4,5,6,7,8,9,13,14,17,18,19]
def N_19_6 : List NodeSpec := [([27,0,1,2,3,4],[0,1,4,5,6,7,17],[0,1]),([0,1,2,3,4,6],[0,4,5,7,9,18],[0,1]),([0,1,2,5,3,4],[0,4,5,6,7,8],[0,1]),([39,0,1,2,3,4],[3,6,7,8,19],[0,1]),([0,1,2,3,11,4],[3,7,8],[0,1]),([0,1,2,3,36,4],[0,2,6,7],[0,1]),([0,1,2,31,3,4],[3,6,7,8,13],[0,1]),([51,0,1,2,3,4],[1,2,3,4,5],[0]),([57,0,1,2,3,4],[0,2,3,5,7,14],[1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_6 : checkNodesBT W_19 g_19 F_19 P_19_6 A_19 B_19_5 6 N_19_6 = true := by decide +kernel
def B_19_6 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_6
set_option maxRecDepth 500000 in
lemma B_19_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 6 xs.toFinset) B_19_6 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_5_ok C_19_6
def P_19_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_19 r_19 S_19 ps_19 [0,2,3,4,6,7,8]
def N_19_7 : List NodeSpec := [([0,1,2,3,4],[0,2,3,4,6,7,8],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_7 : checkNodesBT W_19 g_19 F_19 P_19_7 A_19 B_19_6 7 N_19_7 = true := by decide +kernel
def B_19_7 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_7
set_option maxRecDepth 500000 in
lemma B_19_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 7 xs.toFinset) B_19_7 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_6_ok C_19_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck r_19 g_19 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT B_19_7 r_19 = true := by decide +kernel
lemma low_19 : Lower r_19 g_19 8 := lower_of_forestBT root_19_ok B_19_7_ok root_19_in
def g_20 := 0xfffef880fffef880fffef880fffef880fffef880fffef880fffef880fffef880
def r_20 : List Nat := varsOf 31
def p_20 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,17,17,18,18,19,20,20,21,22,24,24,25,26]
def q_20 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,1,16,2,3,16,4,5,6,16,8,9,10]
def F_20 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_20 : goodPairs g_20 p_20 q_20 := goodPairs_of (by decide +kernel)
def W_20 : BT Decor := buildWiresBT 7 (mkBase p_20 q_20 r_20) [(1,0,2),(3,3,5),(1,1,3),(3,2,7),(0,0,1),(1,2,3),(2,10,4),(1,2,4),(3,3,12),(1,10,4),(3,1,14),(3,0,14),(0,10,4),(3,17,14),(0,1,10),(1,1,10),(3,19,20),(0,0,14),(0,1,4),(1,1,4),(3,23,24),(2,0,3),(1,26,2),(1,3,4),(3,2,28),(1,9,2),(1,30,4),(3,3,31),(3,2,4),(3,33,28),(3,10,4),(1,35,3),(1,26,4),(0,0,4),(1,38,3),(1,2,39),(2,0,2),(1,41,3),(1,41,4),(3,3,43),(2,27,4),(1,27,4),(1,0,4),(3,3,47),(1,48,2),(0,5,7),(1,38,2),(3,3,51),(2,1,2),(3,53,28),(3,23,0),(3,9,12),(2,0,10),(3,0,10),(2,30,4),(1,9,3),(1,30,3),(1,9,4),(3,3,62),(3,2,47),(3,0,4),(3,65,10),(2,1,3),(1,67,2),(0,0,10),(1,0,10),(3,23,10),(3,1,47),(3,9,10),(3,10,47),(2,30,3),(2,0,4),(3,1,4),(1,77,3),(0,10,47),(1,77,2),(1,80,3),(2,80,3),(2,0,17),(1,58,1),(1,1,17),(2,1,10),(3,86,0),(1,35,2),(3,3,4),(0,0,12),(2,0,28),(1,1,2),(1,0,1),(3,1,10)]
lemma W_20_ok : btAll (fun x => faithful p_20 q_20 x ∧ x.1 < 2^256) W_20 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_20 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_20 : BT (List (Nat × Nat)) := btOfList 2 al_20
set_option maxHeartbeats 0 in
lemma A_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_20 = g_20) A_20 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_20_0 : Slice r_20 g_20 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) 0xfffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_1 : Slice r_20 g_20 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_2 : Slice r_20 g_20 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) 0xfefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_3 : Slice r_20 g_20 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcf000fffcf000fffcf000fffcf000fffcf000fffcf000fffcf000fffcf000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_4 : Slice r_20 g_20 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_5 : Slice r_20 g_20 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_6 : Slice r_20 g_20 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_7 : Slice r_20 g_20 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_8
set_option maxHeartbeats 0 in
lemma sl_20_8 : Slice r_20 g_20 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_9 : Slice r_20 g_20 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_10 : Slice r_20 g_20 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
def S_20 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,7),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 16 0,5),some (subcubeFast 3 0,4),some (subcubeFast 16 1,4),some (subcubeFast 16 2,4)]
lemma S_20_ok : btAll (fun o => ∀ p, o = some p → Slice r_20 g_20 p.1 p.2) S_20 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (forall_cons (fun _ h => by cases h; exact sl_20_4) (forall_cons (fun _ h => by cases h; exact sl_20_5) (forall_cons (fun _ h => by cases h; exact sl_20_6) (forall_cons (fun _ h => by cases h; exact sl_20_7) (forall_cons (fun _ h => by cases h; exact sl_20_8) (forall_cons (fun _ h => by cases h; exact sl_20_9) (forall_cons (fun _ h => by cases h; exact sl_20_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_20 : BT (Option PoolSpec) := btOfList 7 ((([(1,[(0,10,4),(1,10,4),(3,17,14)]),(1,[(0,1,10),(1,1,10),(3,19,20)]),(1,[(0,1,4),(1,1,4),(3,23,24)]),(1,[]),(1,[(1,3,12),(0,0,14)]),(2,[(1,2,4),(0,0,14)]),(2,[]),(7,[]),(3,[]),(4,[]),(5,[]),(6,[]),(1,[(1,10,4),(3,1,14)]),(1,[(1,10,4),(0,0,14)]),(0,[]),(4,[(1,38,3)]),(1,[(0,0,4),(1,38,3)]),(1,[(2,10,4),(3,10,4)]),(1,[(1,0,4),(3,3,47)]),(2,[(0,0,4),(1,38,2)]),(1,[(0,1,4),(3,23,0)]),(0,[(1,2,3),(3,0,10)]),(0,[(1,2,3),(2,0,10)]),(1,[(2,0,10),(3,0,10)]),(8,[]),(9,[]),(10,[]),(2,[(0,1,4),(1,1,4),(3,23,24)]),(0,[(2,1,3),(1,67,2)]),(1,[(0,0,10),(1,0,10)]),(1,[(0,1,4),(3,23,10)]),(1,[(1,0,4),(3,1,47)]),(0,[(1,2,3),(3,9,10)]),(1,[(1,0,4),(3,10,47)]),(1,[(2,0,4),(3,0,4)]),(1,[(1,0,4),(0,10,47)]),(1,[(0,0,4),(1,51,3)]),(1,[(0,10,4),(2,0,17)]),(0,[(1,9,4),(1,2,4)]),(1,[(3,0,10),(1,58,1)]),(4,[(1,3,4),(1,2,4)]),(6,[(1,3,4),(1,2,4)]),(2,[(1,2,4)]),(1,[(0,10,4),(1,1,17)]),(1,[(2,1,10),(3,86,0)]),(1,[(0,0,4),(1,0,4)]),(1,[(0,10,4),(1,10,4)]),(2,[(1,89,2)]),(1,[(3,3,12)]),(1,[(1,3,4)]),(1,[(2,10,4)]),(2,[(2,10,4)]),(1,[(3,10,4)]),(1,[(1,10,4)]),(2,[(1,10,4)]),(1,[(0,10,4)]),(4,[(1,3,4)]),(6,[(1,3,4)]),(2,[(1,26,4)]),(1,[(2,5,3)]),(2,[(1,0,2)]),(1,[(1,1,3)]),(0,[(1,0,2)]),(0,[(1,1,3)]),(0,[(1,2,3)]),(1,[(0,0,4)]),(1,[(0,0,1)]),(1,[(3,1,4)]),(0,[(1,0,4),(3,1,47)]),(2,[(1,0,4),(3,1,47)]),(5,[(1,0,2)]),(0,[(2,0,3)]),(0,[(1,2,4)]),(0,[(1,1,2)]),(3,[(1,1,2)]),(1,[(0,1,0)]),(0,[(1,9,4)]),(1,[(1,0,10)]),(1,[(1,3,12)]),(1,[(1,0,1)]),(0,[(1,0,4)]),(2,[(1,0,4)]),(0,[(0,0,4),(1,38,3)]),(1,[(3,3,4)]),(0,[(2,0,3),(1,26,2)]),(1,[(2,0,3)]),(2,[(1,26,2)]),(2,[(0,1,4),(3,23,0)]),(0,[(0,0,4),(1,38,2)]),(1,[(1,0,4)]),(1,[(2,0,4)]),(2,[(0,0,4),(1,0,4)]),(1,[(2,0,10)]),(2,[(2,0,4),(3,0,4)]),(1,[(0,0,10)]),(1,[(3,1,10)]),(0,[(3,1,4)]),(2,[(3,1,4)]),(2,[(2,0,4)]),(0,[(0,0,4)]),(2,[(0,0,4)]),(2,[(1,0,1)]),(2,[(0,0,1)])] : List PoolSpec)).map some)
def B_20_2 : BT (List (List Nat)) := BT.empty
lemma B_20_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 2 xs.toFinset) B_20_2 := .empty
def P_20_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 []
def N_20_3 : List NodeSpec := [([6,8,9,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_3 : checkNodesBT W_20 g_20 F_20 P_20_3 A_20 B_20_2 3 N_20_3 = true := by decide +kernel
def B_20_3 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_3
set_option maxRecDepth 500000 in
lemma B_20_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 3 xs.toFinset) B_20_3 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_2_ok C_20_3
def P_20_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 [0,1,2]
def N_20_4 : List NodeSpec := [([11,13,0,1,2],[],[]),([15,16,2,3,4],[],[]),([18,0,1,2,3],[0],[]),([21,0,2,3,4],[1],[]),([15,22,2,3,4],[],[]),([25,0,2,3,10],[2],[]),([13,0,1,27,4],[],[]),([6,8,0,1,4],[],[0]),([13,29,0,1,4],[],[]),([6,9,2,7,4],[],[0]),([13,22,1,2,4],[],[]),([32,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_4 : checkNodesBT W_20 g_20 F_20 P_20_4 A_20 B_20_3 4 N_20_4 = true := by decide +kernel
def B_20_4 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_4
set_option maxRecDepth 500000 in
lemma B_20_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 4 xs.toFinset) B_20_4 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_3_ok C_20_4
def P_20_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
def N_20_5 : List NodeSpec := [([11,0,1,2,3,12],[3],[0]),([22,1,2,3,4,12],[4,5],[0]),([0,1,2,34,3,28],[6,7],[]),([13,0,1,2,4,28],[6],[0]),([13,0,1,2,12,28],[6,7],[]),([0,1,2,36,10,4],[3,7],[]),([0,1,2,3,37,28],[6,8],[]),([0,1,2,3,4,14],[8,9,10,11],[]),([13,0,1,2,10,4],[3],[0]),([15,0,2,3,10,4],[12],[]),([22,1,2,3,10,4],[13],[]),([11,0,1,2,3,14],[14],[0,1]),([6,9,1,2,3,4],[11],[0]),([0,1,2,39,40,4],[8,15,16],[]),([0,2,30,3,7,4],[6],[]),([0,1,2,42,10,4],[3,8],[]),([44,0,1,2,3,4],[],[]),([11,35,0,1,2,3],[17],[0]),([45,0,1,2,3,4],[],[]),([0,1,2,3,4,46],[9],[]),([26,13,0,1,2,4],[9],[0]),([0,1,2,42,4,28],[7],[1]),([0,1,2,49,3,4],[18],[]),([0,1,2,50,3,4],[],[]),([13,0,1,10,4,12],[3,6],[]),([6,0,1,2,7,4],[9,10],[0]),([0,1,2,39,10,4],[3,8,15],[]),([52,0,1,51,3,4],[19],[]),([0,1,2,54,3,4],[3],[]),([13,0,1,2,4,14],[14],[0,2]),([55,1,2,3,10,4],[20],[]),([56,0,1,2,3,4],[],[]),([0,1,2,3,4,31],[6,14],[0]),([9,2,5,3,7,4],[9],[0,3]),([57,58,1,2,3,4],[21,22,23],[2]),([59,0,1,2,3,4],[],[]),([0,1,2,60,10,4],[3],[]),([0,1,2,3,61,4],[],[]),([63,0,1,2,3,4],[],[]),([26,64,1,2,3,4],[],[]),([25,0,2,3],[2,24,25,26,27],[0]),([66,0,1,2,3,4],[],[]),([0,2,68,3,4,24],[28],[]),([69,1,2,3,70,4],[29],[2]),([71,0,1,2,3,4],[3,30],[]),([72,0,2,3,10,4],[31],[]),([73,0,1,2,3,4],[14,32],[]),([15,0,2,3,4,14],[10],[0]),([74,0,1,2,3,4],[33],[]),([22,1,2,3,4,14],[9,24],[0,1]),([75,0,1,2,3,4],[],[]),([76,65,1,2,3,10],[34],[2]),([0,1,2,60,4,28],[7,8,10],[]),([0,1,2,78,10,4],[3,11],[]),([0,1,2,3,79,4],[9,35],[]),([0,1,2,3,81,4],[8,9,11],[]),([0,1,2,17,10,28],[6],[]),([82,0,1,2,3,4],[],[]),([0,1,2,3,40,4],[8,36],[]),([83,1,2,3,10,4],[37],[]),([6,0,1,2,10,4],[3,9],[]),([0,1,2,3,62,12],[3,8,10,25,26,38],[]),([0,1,10,4,12,28],[3,7],[]),([0,84,2,3,10,4],[39],[]),([0,1,10,12,28],[3,6,7,40,41,42],[]),([52,0,1,2,3,4],[19],[]),([11,0,1,2,10,28],[6,7],[]),([0,2,3,10,85,4],[43],[]),([87,1,2,3,10,4],[44],[]),([11,0,1,2,3,4],[],[]),([38,1,2,3,10,47],[45],[2]),([0,1,2,3,17,14],[46],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_5 : checkNodesBT W_20 g_20 F_20 P_20_5 A_20 B_20_4 5 N_20_5 = true := by decide +kernel
def B_20_5 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_5
set_option maxRecDepth 500000 in
lemma B_20_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 5 xs.toFinset) B_20_5 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_4_ok C_20_5
def P_20_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 [3,6,7,8,9,10,11,16,18,19,20,24,25,26,31,34,42,45,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95]
def N_20_6 : List NodeSpec := [([0,1,2,88,3,4],[25,26,47],[]),([13,0,1,2,3,4],[3,8,9,10,11,42,48],[0,2]),([0,1,2,3,4,12,28],[6,7,49],[0,1]),([0,1,2,3,12,28],[25,26,42,49],[0,1]),([90,0,1,2,3,4,12],[3,7,8,9,25],[]),([11,0,1,2,3,10,4],[3,6,7,50],[0,1]),([11,0,1,2,3,4],[3,6,8,9,10,11,50,51],[0]),([35,0,1,2,3,10,4],[7,52],[0,1]),([0,1,2,3,4,14],[8,9,10,11,53,54],[0,1,2]),([0,1,2,3,17,10,4],[6,7,55],[0,1,2]),([91,0,1,2,3,4,28],[8,25],[0]),([0,1,2,10,4,28],[6,7,49,56,57],[0,1]),([0,1,2,3,4,37],[3,8,10,11,25,58],[0,1]),([6,0,1,2,3,4],[6,7,9,10,11,25,59,60],[0]),([0,1,2,5,3,7,4],[9,11,60,61,62,63],[0,3]),([38,0,1,2,3,10,4],[3,6,8,9,64,65],[0,1,2]),([9,0,1,2,3,10,4],[3,6,8,9,10,11,64,66],[0,1]),([0,1,2,80,3,4],[6,11,25,67],[0,1]),([72,0,2,3,4],[9,11,25,31,68,69],[0]),([26,1,2,5,3,4],[3,6,8,9,25,70,71],[]),([9,0,1,2,3,4,12],[3,7,8,10,25,26,72],[0,1]),([9,0,2,92,3,4],[3,11,26,73,74,75],[1,2]),([26,0,1,2,3,4,12],[3,6,8,25],[0,1,3]),([0,1,2,3,4,62],[3,6,8,10,25,26,76],[0,1]),([0,1,2,3,10,70,4],[8,9,77],[0,1]),([0,1,2,3,4,12,14],[25,26,42,78],[0,1,2]),([0,1,93,2,3,10,4],[8,9,10,11,24,64,79],[]),([26,1,2,3,4,47],[7,8,9,71,80,81],[0,2]),([0,1,2,39,4],[7,8,16,24,82],[0,1]),([89,0,1,2,3,12],[3,7,25,26,42,83],[1]),([0,1,2,27,3,4],[7,8,24,84,85,86],[0,1,2]),([0,1,2,30,3,4],[6,7,8,10,66],[0,1,2]),([55,1,2,3,4],[7,8,10,20,87],[0]),([0,1,2,51,3,4],[7,8,19,24,65,88],[0,1]),([13,0,1,2,3,4,12],[3,6,7,42,48],[0]),([0,1,2,3,10,4,47],[8,9,64,89],[0]),([76,0,1,2,3,10,4],[8,25,90],[0]),([38,1,2,3,47],[8,9,24,45,91],[0,2]),([57,0,1,2,3,10,4],[8,9,64,92],[0,1,2]),([48,0,1,2,3,4],[3,6,8,9,10,11,18,25,81],[0,1]),([76,65,1,2,3],[8,9,24,34,93],[0,2]),([77,0,1,2,3,10,4],[3,6,10,11,67],[0,1,2]),([69,0,1,2,3,10,4],[8,9,94],[0]),([0,1,2,3,10,4,14],[7,53],[0,1,2]),([94,0,1,2,3,10,4],[10,11,64,95],[2])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_6 : checkNodesBT W_20 g_20 F_20 P_20_6 A_20 B_20_5 6 N_20_6 = true := by decide +kernel
def B_20_6 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_6
set_option maxRecDepth 500000 in
lemma B_20_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 6 xs.toFinset) B_20_6 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_5_ok C_20_6
def P_20_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 [3,6,7,8,9,10,11,14,24,25,26,42,60,64,65,66,67,71,72,79,80,81,83,85,89,90,96,97,98,99,100,101,102]
def N_20_7 : List NodeSpec := [([89,0,1,2,3,4],[3,6,7,8,9,10,11,25,26,83],[0]),([0,1,2,3,4,12],[3,8,10,25,26,42,72],[0,1,2,3]),([0,1,2,3,10,4],[3,6,7,8,9,10,11,64],[0,1,2]),([77,0,1,2,3,4],[3,6,9,10,11,14,25,67,96,97],[0,1,2]),([76,0,1,2,3,4],[8,10,14,24,25,90,98],[0]),([38,0,1,2,3,4],[3,6,7,8,9,10,14,24,65,99,100],[0,1,2]),([26,0,1,2,3,4],[3,6,7,8,10,14,24,25,71,85],[0]),([0,1,2,5,3,4],[3,8,9,11,14,24,25,60],[0,2]),([0,1,2,3,4,47],[7,8,9,14,24,25,26,80,81,89],[0,1]),([0,1,93,2,3,4],[9,11,14,24,25,79,101],[0]),([9,0,1,2,3,4],[3,6,7,8,10,14,25,26,66,102],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_7 : checkNodesBT W_20 g_20 F_20 P_20_7 A_20 B_20_6 7 N_20_7 = true := by decide +kernel
def B_20_7 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_7
set_option maxRecDepth 500000 in
lemma B_20_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 7 xs.toFinset) B_20_7 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_6_ok C_20_7
def P_20_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 [3,6,14]
def N_20_8 : List NodeSpec := [([0,1,2,3,4],[3,6,14],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_8 : checkNodesBT W_20 g_20 F_20 P_20_8 A_20 B_20_7 8 N_20_8 = true := by decide +kernel
def B_20_8 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_8
set_option maxRecDepth 500000 in
lemma B_20_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 8 xs.toFinset) B_20_8 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_7_ok C_20_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck r_20 g_20 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT B_20_8 r_20 = true := by decide +kernel
lemma low_20 : Lower r_20 g_20 9 := lower_of_forestBT root_20_ok B_20_8_ok root_20_in
def g_21 := 0xfffcfc80fffcfc80fffcfc80fffcfc80fffcfc80fffcfc80fffcfc80fffcfc80
def r_21 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_21 : Lower r_21 g_21 8 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_22 := 0xfffefc80fffefc80fffefc80fffefc80fffefc80fffefc80fffefc80fffefc80
def r_22 : List Nat := varsOf 31
def p_22 : List Nat := [7,7,7,10,10,11,11,12,12,13,13,14,17,17,18,18,19,20,20,21,22,24,24,25]
def q_22 : List Nat := [6,5,3,8,2,9,3,8,4,9,5,6,16,1,16,2,3,16,4,5,6,16,8,9]
def F_22 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_22 : goodPairs g_22 p_22 q_22 := goodPairs_of (by decide +kernel)
def W_22 : BT Decor := buildWiresBT 4 (mkBase p_22 q_22 r_22) [(1,1,2),(1,5,4),(3,3,6),(1,1,4),(3,2,8),(2,5,4),(1,2,4)]
lemma W_22_ok : btAll (fun x => faithful p_22 q_22 x ∧ x.1 < 2^256) W_22 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_22 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_22 : BT (List (Nat × Nat)) := btOfList 1 al_22
set_option maxHeartbeats 0 in
lemma A_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_22 = g_22) A_22 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_22_0 : Slice r_22 g_22 (identDom 0 2) 7 := by
  have hc : Lower (varsOf 27) 0xffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_1 : Slice r_22 g_22 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) 0xfffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_2 : Slice r_22 g_22 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) 0xfefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_3 : Slice r_22 g_22 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_4 : Slice r_22 g_22 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_5 : Slice r_22 g_22 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffeecc00ffeecc00ffeecc00ffeecc00ffeecc00ffeecc00ffeecc00ffeecc00 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_6 : Slice r_22 g_22 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_4
set_option maxHeartbeats 0 in
lemma sl_22_7 : Slice r_22 g_22 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_8 : Slice r_22 g_22 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
def S_22 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 2,7),some (identDom 0 1,7),some (subcubeFast 8 0,6),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 16 0,5),some (subcubeFast 1 0,5),some (subcubeFast 16 1,4)]
lemma S_22_ok : btAll (fun o => ∀ p, o = some p → Slice r_22 g_22 p.1 p.2) S_22 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (forall_cons (fun _ h => by cases h; exact sl_22_4) (forall_cons (fun _ h => by cases h; exact sl_22_5) (forall_cons (fun _ h => by cases h; exact sl_22_6) (forall_cons (fun _ h => by cases h; exact sl_22_7) (forall_cons (fun _ h => by cases h; exact sl_22_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_22 : BT (Option PoolSpec) := btOfList 4 ((([(0,[]),(3,[]),(2,[]),(0,[(1,2,1)]),(4,[]),(6,[]),(1,[(1,1,4)]),(2,[(1,1,4)]),(8,[]),(5,[]),(1,[(1,1,2)]),(0,[(1,1,2)]),(2,[(1,1,2)]),(1,[]),(7,[])] : List PoolSpec)).map some)
def B_22_3 : BT (List (List Nat)) := BT.empty
lemma B_22_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 3 xs.toFinset) B_22_3 := .empty
def P_22_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_22 r_22 S_22 ps_22 []
def N_22_4 : List NodeSpec := [([7,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_4 : checkNodesBT W_22 g_22 F_22 P_22_4 A_22 B_22_3 4 N_22_4 = true := by decide +kernel
def B_22_4 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_4
set_option maxRecDepth 500000 in
lemma B_22_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 4 xs.toFinset) B_22_4 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_3_ok C_22_4
def P_22_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_22 r_22 S_22 ps_22 [0,1,2,3,4,5]
def N_22_5 : List NodeSpec := [([9,0,1,2,3,4],[],[]),([10,0,1,2,3,4],[],[]),([0,1,2,3,4,6],[0,1,2],[0]),([0,1,5,3,4,11],[3,4,5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_5 : checkNodesBT W_22 g_22 F_22 P_22_5 A_22 B_22_4 5 N_22_5 = true := by decide +kernel
def B_22_5 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_5
set_option maxRecDepth 500000 in
lemma B_22_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 5 xs.toFinset) B_22_5 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_4_ok C_22_5
def P_22_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_22 r_22 S_22 ps_22 [1,4,5,6,7,8,9,10,11,12]
def N_22_6 : List NodeSpec := [([0,1,2,3,4,8],[1,4,6,7,8,9],[0,1]),([0,1,2,5,3,4],[1,4,5,9,10,11,12],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_6 : checkNodesBT W_22 g_22 F_22 P_22_6 A_22 B_22_5 6 N_22_6 = true := by decide +kernel
def B_22_6 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_6
set_option maxRecDepth 500000 in
lemma B_22_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 6 xs.toFinset) B_22_6 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_5_ok C_22_6
def P_22_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_22 r_22 S_22 ps_22 [0,1,2,4,5,9,13,14]
def N_22_7 : List NodeSpec := [([0,1,2,3,4],[0,1,2,4,5,9,13,14],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7 = true := by decide +kernel
def B_22_7 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_7
set_option maxRecDepth 500000 in
lemma B_22_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 7 xs.toFinset) B_22_7 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_6_ok C_22_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck r_22 g_22 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT B_22_7 r_22 = true := by decide +kernel
lemma low_22 : Lower r_22 g_22 8 := lower_of_forestBT root_22_ok B_22_7_ok root_22_in
def g_23 := 0xfffef800fffef800fffef800fffef800fffef800fffef800fffef800fffef800
def r_23 : List Nat := varsOf 31
def p_23 : List Nat := [11,11,11,12,12,13,13,14,14,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26]
def q_23 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10]
def F_23 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_23 : goodPairs g_23 p_23 q_23 := goodPairs_of (by decide +kernel)
def W_23 : BT Decor := buildWiresBT 6 (mkBase p_23 q_23 r_23) [(0,3,4),(1,2,5),(1,0,6),(1,1,6),(1,3,4),(3,6,9),(3,5,9),(2,11,1),(3,2,9),(1,1,3),(1,14,4),(3,1,15),(1,0,3),(0,17,4),(1,2,18),(2,0,5),(1,1,5),(2,13,1),(2,13,0),(1,0,5),(0,0,9),(0,11,0),(2,0,6),(3,3,4),(1,28,0),(2,29,1),(2,3,4),(0,13,0),(3,0,3),(3,33,4),(3,1,4),(3,1,3),(1,36,4),(1,35,3),(1,33,1),(3,0,4),(1,40,3),(3,1,41),(1,1,18),(1,17,4),(3,2,44),(3,1,44),(3,2,38),(3,0,44),(0,14,4),(1,1,4),(1,31,0),(3,14,4),(2,17,4),(3,40,3),(1,0,4),(3,1,55),(0,3,55),(3,3,55)]
lemma W_23_ok : btAll (fun x => faithful p_23 q_23 x ∧ x.1 < 2^256) W_23 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_23 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_23 : BT (List (Nat × Nat)) := btOfList 1 al_23
set_option maxHeartbeats 0 in
lemma A_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_23 = g_23) A_23 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_23_0 : Slice r_23 g_23 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_1 : Slice r_23 g_23 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_2 : Slice r_23 g_23 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcf000fffcf000fffcf000fffcf000fffcf000fffcf000fffcf000fffcf000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_3 : Slice r_23 g_23 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_4 : Slice r_23 g_23 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xfefec8c8fefec8c8fefec8c8fefec8c8fefec8c8fefec8c8fefec8c8fefec8c8 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_11
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_5 : Slice r_23 g_23 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xfefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8fefea8a8 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_11
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
def S_23 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 4 0,6),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 3 0,4),some (identDom 1 3,5),some (identDom 0 3,5)]
lemma S_23_ok : btAll (fun o => ∀ p, o = some p → Slice r_23 g_23 p.1 p.2) S_23 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (forall_cons (fun _ h => by cases h; exact sl_23_4) (forall_cons (fun _ h => by cases h; exact sl_23_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_23 : BT (Option PoolSpec) := btOfList 5 ((([(0,[(0,3,4),(1,3,4),(3,5,9)]),(0,[(0,3,4),(1,3,4)]),(1,[]),(0,[(2,3,4),(3,3,4)]),(2,[]),(0,[]),(3,[]),(0,[(1,3,4),(0,0,9)]),(5,[]),(0,[(0,3,4),(1,1,5)]),(0,[(1,3,4),(3,1,9)]),(2,[(3,1,4)]),(0,[(3,0,3),(1,33,1)]),(0,[(0,3,4),(2,0,5)]),(2,[(1,1,3)]),(4,[]),(0,[(1,0,4),(3,1,55)]),(2,[(3,1,55)]),(0,[(3,3,4)]),(0,[(2,3,4)]),(0,[(1,3,4)]),(0,[(0,3,4)]),(0,[(3,1,4)]),(0,[(1,0,4)]),(0,[(3,1,3)]),(1,[(1,0,3)]),(0,[(1,0,3)])] : List PoolSpec)).map some)
def B_23_1 : BT (List (List Nat)) := BT.empty
lemma B_23_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 1 xs.toFinset) B_23_1 := .empty
def P_23_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 []
def N_23_2 : List NodeSpec := [([7,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_2 : checkNodesBT W_23 g_23 F_23 P_23_2 A_23 B_23_1 2 N_23_2 = true := by decide +kernel
def B_23_2 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_2
set_option maxRecDepth 500000 in
lemma B_23_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 2 xs.toFinset) B_23_2 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_1_ok C_23_2
def P_23_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 []
def N_23_3 : List NodeSpec := [([10,11,0,1],[],[]),([12,11,0,2],[],[]),([11,13,0,1],[],[]),([11,16,0,2],[],[]),([11,0,1,2],[],[]),([0,1,19,9],[],[]),([20,11,1,2],[],[]),([0,21,6,9],[],[]),([22,23,3,4],[],[]),([2,24,21,9],[],[]),([11,0,2,21],[],[]),([11,0,1,6],[],[]),([20,1,6,9],[],[]),([11,25,1,2],[],[]),([3,7,8,4],[],[0]),([10,0,1,9],[],[]),([25,1,6,9],[],[]),([16,0,6,9],[],[]),([26,11,1,2],[],[]),([0,6,8,9],[],[0]),([27,1,6,9],[],[]),([0,1,6,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_3 : checkNodesBT W_23 g_23 F_23 P_23_3 A_23 B_23_2 3 N_23_3 = true := by decide +kernel
def B_23_3 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_3
set_option maxRecDepth 500000 in
lemma B_23_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 3 xs.toFinset) B_23_3 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_2_ok C_23_3
def P_23_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 [0,1]
def N_23_4 : List NodeSpec := [([13,0,1,3,4],[],[]),([0,1,3,6,4],[],[0]),([22,13,0,3,4],[],[0]),([13,16,0,3,4],[],[]),([13,25,1,3,4],[],[]),([30,0,2,3,4],[],[]),([16,25,2,3,4],[],[]),([11,0,1,2,4],[],[]),([11,0,1,2,3],[],[]),([11,0,1,2],[0],[0,1]),([13,0,1,5,9],[],[0]),([16,0,2,5,9],[],[0]),([31,28,0,1,2],[],[0]),([32,13,1,3,4],[],[]),([25,1,2,5,9],[],[0]),([0,1,2,5,9],[],[0]),([0,1,5,6,9],[],[0,1]),([0,1,6,9],[1],[0,1]),([31,0,34,1,2],[],[]),([20,1,3,6,4],[],[0]),([35,0,2,3,37],[],[]),([28,11,0,1,2],[],[]),([0,1,3,6,9],[],[]),([36,0,2,38,4],[],[]),([0,39,2,4,9],[],[]),([28,0,1,3,6],[],[0]),([31,11,0,1,2],[],[]),([42,0,2,3,4],[],[]),([16,0,2,3,4],[],[]),([0,1,3,19,4],[],[0]),([11,0,1,2,5],[0],[0,1]),([0,2,3,43,4],[],[]),([45,0,1,3,4],[],[]),([0,1,2,18,9],[],[0]),([46,0,2,3,4],[],[]),([47,0,1,3,4],[],[]),([11,0,1,2,9],[0],[0,1]),([31,0,2,21,4],[],[]),([0,2,21,4,9],[],[]),([0,3,21,6,4],[],[0]),([16,48,2,3,4],[],[]),([20,2,3,21,4],[],[]),([31,0,39,2,4],[],[]),([0,2,5,21,9],[],[0]),([20,1,2,5,9],[],[0]),([2,3,24,21,4],[],[0]),([0,3,6,8,4],[],[0]),([0,2,3,49,50],[],[]),([31,0,1,6,4],[],[0]),([27,1,3,6,4],[],[0]),([0,1,6,4,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_4 : checkNodesBT W_23 g_23 F_23 P_23_4 A_23 B_23_3 4 N_23_4 = true := by decide +kernel
def B_23_4 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_4
set_option maxRecDepth 500000 in
lemma B_23_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 4 xs.toFinset) B_23_4 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_3_ok C_23_4
def P_23_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]
def N_23_5 : List NodeSpec := [([0,29,1,2,3,4],[2],[0]),([31,28,0,1,2,4],[],[0]),([31,28,0,1,2],[3],[0]),([0,1,2,3,4,9],[2,4,5],[0,1]),([0,51,1,2,3,4],[],[]),([16,0,1,2,3,4],[],[]),([13,0,1,3,4],[],[0,1]),([25,1,2,3,4,9],[6,7],[0,1]),([31,28,0,1,2,3],[],[0]),([0,1,2,5,3,9],[],[0]),([28,0,1,2,3,4],[],[0]),([31,36,0,1,2,4],[2],[1]),([0,1,2,3,18,4],[2,5,8],[0,1]),([0,2,5,3,21,4],[2,9],[0]),([0,1,3,6,4],[],[0,1]),([0,1,2,3,4,37],[],[0]),([36,0,1,2,4,9],[2],[1]),([52,0,1,2,3,4],[],[]),([28,0,1,2,4,9],[5],[0]),([53,0,1,2,3,4],[],[]),([16,0,2,3,4],[10],[]),([54,0,1,2,3,4],[],[]),([36,35,0,2,3,4],[11],[0]),([0,1,2,3,4,44],[2,5],[0,1]),([0,1,2,3,38,4],[4,5],[0,1]),([31,0,1,2,3,9],[5],[0]),([0,39,2,3,4],[12],[0]),([20,1,2,5,3,4],[6,8,13],[0]),([31,0,1,2,17,4],[4],[]),([16,0,2,3,4,9],[2,10],[0]),([35,0,2,3,4,50],[2,11],[]),([0,2,3,14,4,50],[14,15],[0]),([0,1,2,3,24,4],[],[]),([0,34,1,2,3,4],[4],[0]),([31,0,1,2,5,4],[5],[0,1]),([0,1,2,17,4,9],[4],[0]),([56,0,2,3,4],[16],[]),([0,1,2,5,4,9],[],[0,1]),([0,2,3,21,4],[9],[0]),([56,0,2,3,4,55],[2,17],[]),([0,1,2,5,3,4],[2,4,5,8,15],[0]),([0,1,2,5,9],[1],[0,1]),([0,1,5,3,6,4],[5],[0,1]),([0,1,2,57,3,4],[8],[]),([58,0,1,2,3,4],[],[]),([31,0,1,2,3,4],[],[0]),([13,0,1,3,4,9],[5],[0,1]),([28,0,1,2,5,3],[5],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_5 : checkNodesBT W_23 g_23 F_23 P_23_5 A_23 B_23_4 5 N_23_5 = true := by decide +kernel
def B_23_5 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_5
set_option maxRecDepth 500000 in
lemma B_23_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 5 xs.toFinset) B_23_5 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_4_ok C_23_5
def P_23_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 [2,4,5,6,8,15,18,19,20,21,22,23,24,25,26]
def N_23_6 : List NodeSpec := [([28,0,1,2,3,4],[2,4,5,18],[0,1]),([31,0,1,2,3,4],[2,4,5,8,15,19],[0,1]),([0,1,2,3,4,9],[2,4,20],[0,1]),([0,1,2,5,3,4],[2,4,8,15,21],[0,1]),([35,0,1,2,3,4],[4,5,6,15,22],[0,1]),([0,1,2,3,4,55],[6,8,23],[0,1]),([36,0,1,2,3,4],[4,6,15,24],[0,1]),([0,1,2,3,17,4],[4,6,8,25,26],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_6 : checkNodesBT W_23 g_23 F_23 P_23_6 A_23 B_23_5 6 N_23_6 = true := by decide +kernel
def B_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_6
set_option maxRecDepth 500000 in
lemma B_23_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 6 xs.toFinset) B_23_6 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_5_ok C_23_6
def P_23_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 [2,5,6]
def N_23_7 : List NodeSpec := [([0,1,2,3,4],[2,5,6],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_7 : checkNodesBT W_23 g_23 F_23 P_23_7 A_23 B_23_6 7 N_23_7 = true := by decide +kernel
def B_23_7 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_7
set_option maxRecDepth 500000 in
lemma B_23_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 7 xs.toFinset) B_23_7 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_6_ok C_23_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck r_23 g_23 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT B_23_7 r_23 = true := by decide +kernel
lemma low_23 : Lower r_23 g_23 8 := lower_of_forestBT root_23_ok B_23_7_ok root_23_in
def g_24 := 0xffffffecfef8e800ffffffecfef8e800ffffffecfef8e800ffffffecfef8e800
def r_24 : List Nat := varsOf 63
def p_24 : List Nat := [11,11,11,13,13,13,14,14,14,15,19,19,19,20,20,21,21,22,22,23,25,25,25,26,26,26,28,28,34,34,35,35,37,37,37,38,38,39,40,40,41,41,42,44,44,48,48,49,49,50,52,56]
def q_24 : List Nat := [10,9,3,12,9,5,12,10,6,7,18,17,3,16,4,17,5,18,6,7,24,17,9,24,18,10,24,12,32,2,33,3,36,33,5,36,6,7,32,8,33,9,10,36,12,32,16,33,17,18,36,24]
def F_24 : Nat := fullMask 52
set_option maxHeartbeats 0 in
lemma gp_24 : goodPairs g_24 p_24 q_24 := goodPairs_of (by decide +kernel)
def W_24 : BT Decor := buildWiresBT 9 (mkBase p_24 q_24 r_24) [(1,0,1),(1,3,5),(0,6,7),(0,8,4),(1,8,4),(3,9,10),(1,9,2),(0,3,5),(1,1,13),(0,14,4),(1,1,4),(1,13,16),(3,15,17),(1,1,2),(1,4,5),(0,3,20),(2,19,21),(1,2,5),(2,14,4),(3,1,4),(1,24,25),(0,19,20),(2,8,4),(3,8,4),(3,2,10),(2,6,4),(2,31,5),(2,6,5),(0,33,3),(1,34,5),(0,33,4),(1,34,4),(1,2,4),(1,38,5),(3,1,39),(0,4,5),(3,41,20),(1,42,1),(1,42,0),(3,1,20),(3,0,20),(1,0,20),(3,41,47),(3,14,4),(1,16,5),(3,41,50),(2,38,5),(3,2,20),(0,3,38),(1,3,38),(3,54,55),(3,2,3),(1,57,5),(3,4,58),(3,1,58),(1,57,4),(2,42,1),(1,1,5),(0,4,63),(3,64,50),(1,19,5),(3,4,66),(0,3,63),(3,68,38),(3,54,63),(1,54,5),(3,25,39),(3,1,7),(1,73,4),(3,13,7),(0,3,4),(2,33,76),(0,19,3),(1,19,3),(3,78,79),(3,2,16),(1,19,4),(3,1,82),(1,0,2),(1,76,5),(2,84,85),(1,78,5),(1,36,5),(2,19,4),(2,6,21),(2,3,4),(1,91,5),(0,82,7),(1,0,4),(2,84,5),(1,2,76),(3,1,3),(1,97,4),(3,78,20),(0,19,4),(1,100,5),(3,4,7),(0,0,82),(2,19,5),(3,2,66),(0,3,82),(3,3,82),(3,0,82),(3,0,4),(2,19,85),(2,33,91),(2,3,5),(2,82,5),(0,16,5),(1,2,114),(2,96,5),(3,2,4),(3,2,7),(1,118,4),(3,25,58),(2,42,0),(0,3,16),(1,3,16),(3,122,123),(3,25,20),(3,100,82),(2,16,5),(0,4,58),(1,2,128),(3,114,50),(3,100,7),(3,4,63),(2,4,5),(1,133,2),(3,1,134),(1,1,21),(3,3,5),(1,137,4),(3,1,138),(1,137,1),(2,140,4),(1,102,2),(1,102,1),(1,118,1),(3,0,14),(1,0,14),(3,3,4),(1,147,2),(3,1,148),(1,147,1),(2,150,2),(1,91,2),(3,1,152),(1,91,1),(2,154,5),(2,154,2),(1,3,4),(3,1,157),(1,158,2),(3,1,85),(1,1,76),(2,161,5),(3,2,5),(1,163,4),(3,1,164),(1,163,1),(2,166,4),(3,19,4),(1,168,1),(2,169,5),(1,52,1),(1,13,4),(1,0,172),(1,76,63),(3,38,7),(3,2,157),(0,38,7),(3,3,38),(1,133,1),(2,179,2),(3,19,3),(1,181,1),(2,182,5),(1,117,5),(3,1,184),(1,2,3),(2,186,4),(1,187,1),(1,132,2),(2,182,4),(2,4,63),(1,25,5),(3,1,172),(1,2,68),(1,91,63),(1,105,4),(3,117,63),(1,117,63),(3,38,63),(3,2,161),(1,91,23),(0,38,63),(3,57,63),(1,57,63),(1,0,85),(1,2,64),(1,25,13),(1,163,25),(3,25,186),(1,168,2),(1,1,41),(1,0,211),(2,210,5),(3,16,5),(1,214,4),(1,127,2),(1,61,5),(0,3,50),(2,3,114),(3,4,5),(3,133,16),(1,1,54),(3,137,16),(1,137,16),(0,16,7),(2,3,16),(3,3,16),(1,1,3),(2,228,4),(1,76,23),(1,122,5),(1,97,5),(3,2,232),(2,19,3),(3,2,92),(3,2,79),(3,1,92),(3,19,20),(2,38,63),(1,68,4),(3,76,63),(1,0,5),(3,91,242),(1,2,13),(1,137,109),(3,137,94),(3,2,85),(3,16,7),(1,57,16),(1,109,13),(3,1,96),(1,98,5),(2,94,5),(0,94,7),(2,3,38),(3,2,192),(3,57,20),(3,0,3),(3,258,20),(3,1,61),(3,97,38),(1,258,5),(3,4,262),(1,258,4),(1,264,5),(1,82,5),(1,133,258),(3,13,94),(3,2,50),(1,3,114),(1,78,4),(2,264,5),(2,6,41),(2,84,4),(1,274,5),(1,53,1),(1,220,1),(0,6,157),(3,13,4),(3,4,242),(1,3,41),(3,220,6),(1,234,4),(3,163,20),(3,137,6),(1,57,25),(0,6,20),(0,19,157),(2,6,13),(1,95,4),(1,33,4),(1,137,25),(2,6,76),(3,0,211),(1,91,19),(0,19,7),(1,31,5),(3,133,6),(1,2,21),(3,117,228),(0,186,16),(1,163,16),(3,91,6),(3,25,7),(3,1,79),(1,305,4),(3,147,6),(1,181,2),(2,3,20),(1,2,41),(2,3,41),(1,229,2),(3,109,7),(2,61,5),(1,89,5),(3,19,157),(1,176,1),(2,3,63),(2,89,5),(1,45,2),(0,3,66),(3,13,16),(1,308,5),(2,152,5),(0,3,39),(1,104,4),(1,178,1),(1,19,76),(3,76,242),(2,19,76),(1,308,4),(1,73,2),(3,91,19),(1,236,4),(1,83,5),(1,147,19),(3,19,7),(1,133,19),(3,133,19),(1,117,97),(2,236,4),(0,228,38),(2,308,4),(2,98,5),(3,2,98),(2,308,5),(3,4,232),(3,117,7),(3,91,63),(1,210,5),(3,0,172),(3,97,20),(1,133,97),(3,147,19),(2,186,16),(3,57,16),(1,81,5),(2,81,5),(3,163,16),(1,133,57),(1,0,41),(3,1,5),(3,0,5),(1,363,2),(1,109,5),(1,363,4),(1,163,0),(1,0,3),(2,368,4),(1,0,13)]
lemma W_24_ok : btAll (fun x => faithful p_24 q_24 x ∧ x.1 < 2^256) W_24 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_24 : List (List (Nat × Nat)) := [[]]
def A_24 : BT (List (Nat × Nat)) := btOfList 1 al_24
set_option maxHeartbeats 0 in
lemma A_24_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_24 = g_24) A_24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_24_0 : Slice r_24 g_24 (subcubeFast 4 0) 9 := by
  have hc : Lower (varsOf 59) 0xffffffccee888800ffffffccee888800ffffffccee888800ffffffccee888800 9 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_1 : Slice r_24 g_24 (subcubeFast 2 0) 9 := by
  have hc : Lower (varsOf 61) 0xffffffa0faf0a000ffffffa0faf0a000ffffffa0faf0a000ffffffa0faf0a000 9 := carry_of (swaps := [(1,5),(2,5),(3,5)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_2 : Slice r_24 g_24 (subcubeFast 1 0) 9 := by
  have hc : Lower (varsOf 62) 0xffffffccfcf0c000ffffffccfcf0c000ffffffccfcf0c000ffffffccfcf0c000 9 := carry_of (swaps := [(0,5),(1,5),(3,5),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_3 : Slice r_24 g_24 (subcubeFast 0 1) 8 := by
  have hc : Lower (varsOf 62) 0xfffffffcfffcfc00fffffffcfffcfc00fffffffcfffcfc00fffffffcfffcfc00 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_4 : Slice r_24 g_24 (subcubeFast 0 8) 8 := by
  have hc : Lower (varsOf 55) 0xfffffffffefee8e8fffffffffefee8e8fffffffffefee8e8fffffffffefee8e8 8 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_5 : Slice r_24 g_24 (subcubeFast 32 0) 8 := by
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) low_15
set_option maxHeartbeats 0 in
lemma sl_24_6 : Slice r_24 g_24 (subcubeFast 16 0) 8 := by
  have hc : Lower (varsOf 47) 0xffecffece800e800ffecffece800e800ffecffece800e800ffecffece800e800 8 := carry_of (swaps := [(1,2),(4,5)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_7 : Slice r_24 g_24 (identDom 2 5) 9 := by
  have hc : Lower (varsOf 31) 0xfef8f8e0fef8f8e0fef8f8e0fef8f8e0fef8f8e0fef8f8e0fef8f8e0fef8f8e0 9 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_18
  exact slice_ident (u := 2) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_8 : Slice r_24 g_24 (subcubeFast 2 1) 7 := by
  have hc : Lower (varsOf 60) 0xfffffff0fff0f000fffffff0fff0f000fffffff0fff0f000fffffff0fff0f000 7 := carry_of (swaps := [(0,4),(1,5),(2,4),(3,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_9 : Slice r_24 g_24 (subcubeFast 4 1) 7 := by
  have hc : Lower (varsOf 58) 0xffffffccffcccc00ffffffccffcccc00ffffffccffcccc00ffffffccffcccc00 7 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_10 : Slice r_24 g_24 (subcubeFast 36 0) 7 := by
  have hc : Lower (varsOf 27) 0xee888800ee888800ee888800ee888800ee888800ee888800ee888800ee888800 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 36) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_11 : Slice r_24 g_24 (subcubeFast 32 8) 7 := by
  have hc : Lower (varsOf 23) 0xfefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8fefee8e8 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 32) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_12 : Slice r_24 g_24 (subcubeFast 8 0) 8 := by
  have hc : Lower (varsOf 55) 0xffffececf8f80000ffffececf8f80000ffffececf8f80000ffffececf8f80000 8 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_13 : Slice r_24 g_24 (identDom 1 4) 9 := by
  have hc : Lower (varsOf 47) 0xffecffececc8ecc8ffecffececc8ecc8ffecffececc8ecc8ffecffececc8ecc8 9 := carry_of (swaps := [(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_20
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_14 : Slice r_24 g_24 (identDom 1 2) 8 := by
  have hc : Lower (varsOf 59) 0xffffffcceecccc00ffffffcceecccc00ffffffcceecccc00ffffffcceecccc00 8 := carry_of (swaps := [(1,3),(2,5),(4,5)]) (by decide +kernel) low_21
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_15 : Slice r_24 g_24 (identDom 1 3) 8 := by
  have hc : Lower (varsOf 55) 0xffffececfcfcc8c8ffffececfcfcc8c8ffffececfcfcc8c8ffffececfcfcc8c8 8 := carry_of (swaps := [(1,4),(2,4),(3,5),(4,5)]) (by decide +kernel) low_22
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_16 : Slice r_24 g_24 (subcubeFast 5 0) 6 := by
  have hc : Lower (varsOf 58) 0xffffffcccc000000ffffffcccc000000ffffffcccc000000ffffffcccc000000 6 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 5) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_17 : Slice r_24 g_24 (identDom 3 4) 8 := by
  have hc : Lower (varsOf 47) 0xffecffecfe00fe00ffecffecfe00fe00ffecffecfe00fe00ffecffecfe00fe00 8 := carry_of (swaps := [(1,2),(3,4),(4,5)]) (by decide +kernel) low_23
  exact slice_ident (u := 3) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_18 : Slice r_24 g_24 (subcubeFast 48 8) 4 := by
  exact slice_fast_direct_f (z := 48) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_24_19 : Slice r_24 g_24 (subcubeFast 36 16) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 36) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_20 : Slice r_24 g_24 (subcubeFast 36 8) 4 := by
  have hc : Lower (varsOf 19) 0xeeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 36) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_21 : Slice r_24 g_24 (subcubeFast 34 8) 4 := by
  have hc : Lower (varsOf 21) 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 34) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_22 : Slice r_24 g_24 (subcubeFast 36 2) 4 := by
  have hc : Lower (varsOf 25) 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 36) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_23 : Slice r_24 g_24 (subcubeFast 18 4) 4 := by
  have hc : Lower (varsOf 41) 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00 4 := carry_of (swaps := [(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 18) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_24 : Slice r_24 g_24 (subcubeFast 33 8) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_25 : Slice r_24 g_24 (subcubeFast 36 1) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 36) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_26 : Slice r_24 g_24 (subcubeFast 17 4) 4 := by
  have hc : Lower (varsOf 42) 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_27 : Slice r_24 g_24 (subcubeFast 20 1) 4 := by
  have hc : Lower (varsOf 42) 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 20) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_28 : Slice r_24 g_24 (subcubeFast 12 1) 4 := by
  have hc : Lower (varsOf 50) 0xffffcccccccc0000ffffcccccccc0000ffffcccccccc0000ffffcccccccc0000 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_29 : Slice r_24 g_24 (subcubeFast 33 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_30 : Slice r_24 g_24 (subcubeFast 6 1) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000ffffff00ff000000ffffff00ff000000ffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 1) (by decide +kernel) hc
def S_24 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 4 0,9),some (subcubeFast 2 0,9),some (subcubeFast 1 0,9),some (subcubeFast 0 1,8),some (subcubeFast 0 8,8),some (subcubeFast 32 0,8),some (subcubeFast 16 0,8),some (identDom 2 5,9),some (subcubeFast 2 1,7),some (subcubeFast 4 1,7),some (subcubeFast 36 0,7),some (subcubeFast 32 8,7),some (subcubeFast 8 0,8),some (identDom 1 4,9),some (identDom 1 2,8),some (identDom 1 3,8),some (subcubeFast 5 0,6),some (identDom 3 4,8),some (subcubeFast 48 8,4),some (subcubeFast 36 16,4),some (subcubeFast 36 8,4),some (subcubeFast 34 8,4),some (subcubeFast 36 2,4),some (subcubeFast 18 4,4),some (subcubeFast 33 8,4),some (subcubeFast 36 1,4),some (subcubeFast 17 4,4),some (subcubeFast 20 1,4),some (subcubeFast 12 1,4),some (subcubeFast 33 2,4),some (subcubeFast 6 1,4)]
lemma S_24_ok : btAll (fun o => ∀ p, o = some p → Slice r_24 g_24 p.1 p.2) S_24 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_24_0) (forall_cons (fun _ h => by cases h; exact sl_24_1) (forall_cons (fun _ h => by cases h; exact sl_24_2) (forall_cons (fun _ h => by cases h; exact sl_24_3) (forall_cons (fun _ h => by cases h; exact sl_24_4) (forall_cons (fun _ h => by cases h; exact sl_24_5) (forall_cons (fun _ h => by cases h; exact sl_24_6) (forall_cons (fun _ h => by cases h; exact sl_24_7) (forall_cons (fun _ h => by cases h; exact sl_24_8) (forall_cons (fun _ h => by cases h; exact sl_24_9) (forall_cons (fun _ h => by cases h; exact sl_24_10) (forall_cons (fun _ h => by cases h; exact sl_24_11) (forall_cons (fun _ h => by cases h; exact sl_24_12) (forall_cons (fun _ h => by cases h; exact sl_24_13) (forall_cons (fun _ h => by cases h; exact sl_24_14) (forall_cons (fun _ h => by cases h; exact sl_24_15) (forall_cons (fun _ h => by cases h; exact sl_24_16) (forall_cons (fun _ h => by cases h; exact sl_24_17) (forall_cons (fun _ h => by cases h; exact sl_24_18) (forall_cons (fun _ h => by cases h; exact sl_24_19) (forall_cons (fun _ h => by cases h; exact sl_24_20) (forall_cons (fun _ h => by cases h; exact sl_24_21) (forall_cons (fun _ h => by cases h; exact sl_24_22) (forall_cons (fun _ h => by cases h; exact sl_24_23) (forall_cons (fun _ h => by cases h; exact sl_24_24) (forall_cons (fun _ h => by cases h; exact sl_24_25) (forall_cons (fun _ h => by cases h; exact sl_24_26) (forall_cons (fun _ h => by cases h; exact sl_24_27) (forall_cons (fun _ h => by cases h; exact sl_24_28) (forall_cons (fun _ h => by cases h; exact sl_24_29) (forall_cons (fun _ h => by cases h; exact sl_24_30) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))
def ps_24 : BT (Option PoolSpec) := btOfList 12 ((([(1,[(1,3,5),(0,6,7),(0,8,4),(1,8,4),(3,9,10)]),(1,[(1,3,5),(0,6,7),(0,8,4),(1,9,2),(1,8,4)]),(2,[(0,3,5),(1,1,13),(0,14,4),(1,14,4),(3,15,17)]),(29,[]),(0,[(0,3,5),(1,1,13),(0,14,4),(1,14,4),(3,15,17)]),(10,[(0,14,4),(1,14,4),(3,15,17)]),(11,[(0,14,4),(1,14,4),(3,15,17)]),(2,[(3,1,4),(0,3,5),(1,1,13),(2,14,4),(1,24,25)]),(8,[(0,3,5),(2,14,4),(1,24,25)]),(0,[(3,1,4),(0,3,5),(1,1,13),(2,14,4),(1,24,25)]),(10,[(3,1,4),(2,14,4),(1,24,25)]),(11,[(3,1,4),(2,14,4),(1,24,25)]),(2,[(1,1,2),(1,1,4),(1,2,5),(1,4,5),(0,19,20)]),(8,[(1,2,5),(1,4,5),(0,19,20)]),(18,[]),(10,[(1,1,4),(0,19,20)]),(1,[(1,3,5),(0,6,7),(2,8,4),(3,8,4)]),(1,[(1,3,5),(0,6,7),(1,8,4),(3,2,10)]),(1,[(1,3,5),(0,6,7),(0,8,4),(1,8,4)]),(1,[(1,3,5),(0,6,7),(0,8,4),(1,9,2)]),(6,[]),(12,[]),(1,[(1,4,5),(1,2,20),(0,3,20)]),(20,[]),(22,[]),(11,[(1,2,20),(3,1,39)]),(2,[(0,4,5),(1,4,5),(3,41,20),(1,42,1)]),(8,[(0,4,5),(1,4,5),(3,41,20)]),(1,[(0,4,5),(1,4,5),(3,41,20)]),(10,[(1,42,1)]),(11,[(1,42,1)]),(2,[(0,4,5),(1,4,5),(3,41,20)]),(3,[(0,4,5),(1,4,5),(3,41,20)]),(1,[(0,4,5),(1,4,5),(3,41,20),(1,42,0)]),(0,[(0,4,5),(1,4,5),(3,41,20),(1,42,0)]),(9,[(0,4,5),(1,4,5),(3,41,20)]),(11,[(1,42,0)]),(2,[(0,4,5),(1,4,5),(3,1,20),(3,41,20)]),(10,[(3,1,20)]),(1,[(0,4,5),(1,4,5),(3,0,20),(3,41,20)]),(0,[(0,4,5),(1,4,5),(3,0,20),(3,41,20)]),(11,[(3,0,20)]),(2,[(0,4,5),(1,4,5),(3,41,47)]),(3,[(0,4,5),(1,4,5)]),(1,[(0,4,5),(1,4,5),(1,0,20),(3,41,47)]),(8,[(0,4,5),(1,4,5)]),(0,[(0,4,5),(1,4,5),(1,0,20),(3,41,47)]),(9,[(0,4,5),(1,4,5)]),(11,[(1,0,20)]),(19,[]),(6,[(0,3,5),(1,1,13)]),(2,[(0,3,5),(1,1,13),(2,14,4),(3,14,4)]),(4,[(1,1,13),(2,14,4),(3,14,4)]),(11,[(2,14,4),(3,14,4)]),(0,[(0,3,5),(1,1,13),(0,14,4),(1,14,4)]),(10,[(0,14,4),(1,14,4)]),(2,[(0,3,5),(1,1,13),(0,14,4),(1,14,4)]),(4,[(1,1,13),(0,14,4),(1,14,4)]),(11,[(0,14,4),(1,14,4)]),(2,[(0,4,5),(1,4,5),(1,1,20),(3,41,50)]),(8,[(0,4,5),(1,4,5),(3,41,50)]),(1,[(0,4,5),(1,4,5),(3,41,50)]),(0,[(0,4,5),(1,4,5),(1,1,20),(3,41,50)]),(10,[(1,1,20)]),(11,[(1,1,20)]),(0,[(1,4,5),(2,38,5)]),(2,[(1,2,4),(1,4,5),(3,2,20),(2,38,5)]),(9,[(1,4,5),(2,38,5)]),(1,[(1,2,4),(1,4,5),(3,2,20),(2,38,5)]),(11,[(1,2,4),(3,2,20)]),(2,[(1,2,4),(0,3,38),(1,3,38),(3,54,55)]),(9,[(0,3,38),(1,3,38),(3,54,55)]),(1,[(1,2,4),(0,3,38),(1,3,38),(3,54,55)]),(23,[]),(10,[(0,3,38),(1,3,38),(3,54,55)]),(11,[(1,2,4)]),(0,[(0,3,38),(1,3,38),(3,54,55)]),(1,[(3,2,3),(1,57,5),(3,4,58)]),(6,[(3,2,3),(1,57,5)]),(2,[(3,2,3),(1,57,4),(1,4,5),(3,2,20)]),(9,[(1,57,4),(1,4,5)]),(1,[(3,2,3),(1,57,4),(1,4,5),(3,2,20)]),(2,[(0,4,5),(1,4,5),(3,41,20),(2,42,1)]),(10,[(2,42,1)]),(2,[(1,1,5),(0,4,63),(1,4,63),(3,64,50)]),(8,[(0,4,63),(1,4,63),(3,64,50)]),(1,[(0,4,63),(1,4,63),(3,64,50)]),(13,[(1,1,5),(3,64,50)]),(0,[(1,1,5),(0,4,63),(1,4,63),(3,64,50)]),(21,[]),(5,[(1,2,63),(3,4,66)]),(11,[(1,2,63),(3,4,66)]),(6,[(1,1,5),(1,2,63)]),(4,[]),(11,[]),(1,[(1,2,4),(0,3,63),(3,68,38)]),(11,[(1,2,4),(3,54,63)]),(0,[(1,1,5),(0,3,38),(3,54,63)]),(1,[(1,2,4)]),(0,[(1,1,5),(0,3,38),(1,54,5)]),(12,[(1,2,4)]),(27,[]),(1,[(1,4,5),(1,2,20),(3,25,39)]),(4,[(1,4,5)]),(5,[]),(0,[(3,1,4),(1,4,5),(3,25,39)]),(2,[(3,1,4),(1,3,5),(3,1,7),(1,73,4)]),(6,[(1,3,5),(3,1,7)]),(4,[(3,1,4),(1,73,4)]),(6,[(0,3,5),(1,3,5),(3,13,7)]),(11,[(3,1,4)]),(3,[(0,3,5),(1,3,5),(3,13,7)]),(2,[(0,3,5),(1,3,5),(3,13,7)]),(1,[(0,3,5),(1,3,5),(3,13,7)]),(10,[(3,1,4)]),(0,[(1,0,1),(0,4,5),(1,4,5),(3,41,20)]),(11,[(1,0,1)]),(9,[(0,3,5),(1,3,5),(3,13,7)]),(1,[(1,3,5),(0,6,7),(2,8,4)]),(11,[(1,0,1),(0,33,4)]),(1,[(1,3,5),(0,6,7),(1,8,4)]),(2,[(1,3,5),(0,6,7)]),(3,[(1,3,5)]),(11,[(1,0,1),(1,34,4)]),(1,[(2,6,5),(0,3,4),(2,33,76)]),(2,[]),(0,[]),(9,[(0,3,4),(2,33,76)]),(11,[(1,0,1),(2,33,76)]),(6,[(1,0,1),(2,6,5)]),(2,[(1,1,2),(0,19,3),(1,19,3),(3,78,79)]),(8,[(0,19,3),(1,19,3),(3,78,79)]),(0,[(0,19,3),(1,19,3),(3,78,79)]),(1,[(0,19,3),(1,19,3),(3,78,79)]),(10,[(0,19,3),(1,19,3),(3,78,79)]),(11,[(1,1,2)]),(9,[(0,19,3),(1,19,3),(3,78,79)]),(2,[(1,1,2),(1,1,4),(1,2,5),(1,4,5)]),(8,[(1,2,5),(1,4,5)]),(10,[]),(2,[(0,4,5),(1,4,5),(1,1,20),(3,41,20)]),(0,[(1,19,4),(3,1,82)]),(2,[(1,1,2),(1,19,4),(3,1,82),(3,2,82)]),(8,[(1,19,4),(3,2,82)]),(11,[(1,0,2),(2,84,85)]),(0,[(0,19,3),(1,78,5),(1,4,5)]),(30,[]),(12,[(1,1,2)]),(6,[(1,1,2)]),(11,[(1,0,1),(2,33,4)]),(1,[(1,3,5),(0,6,7),(0,8,4)]),(0,[(1,0,1),(1,3,5),(0,6,7)]),(4,[(1,0,1)]),(12,[(1,0,1),(0,6,7)]),(5,[(1,0,1),(0,6,7)]),(0,[(1,1,4),(1,4,5),(0,19,20)]),(2,[(1,1,2),(1,1,4),(1,4,5),(0,19,20)]),(8,[(1,4,5),(0,19,20)]),(13,[]),(9,[(0,33,4),(1,36,5)]),(0,[(1,19,4),(3,1,82),(3,4,82)]),(1,[(1,19,4),(3,4,82)]),(2,[(1,1,2),(1,19,4),(3,1,82),(3,4,82)]),(8,[(1,19,4),(3,4,82)]),(1,[(1,2,5),(1,4,5),(0,19,20)]),(2,[(1,1,2),(1,2,5),(1,4,5),(0,19,20)]),(7,[]),(3,[]),(3,[(1,4,5),(0,3,20)]),(11,[(1,0,1),(2,6,21)]),(1,[(2,3,4),(1,91,5),(1,4,5)]),(12,[(1,0,1)]),(5,[(1,0,1)]),(1,[(1,19,4),(1,3,5),(0,82,7)]),(0,[(1,19,4),(1,3,5),(0,82,7)]),(10,[(1,19,4),(0,82,7)]),(4,[(1,1,2),(1,19,4)]),(1,[(1,0,4),(0,3,5),(1,3,5),(3,13,7)]),(8,[(0,3,5),(1,3,5),(3,13,7)]),(0,[(1,0,4),(0,3,5),(1,3,5),(3,13,7)]),(11,[(1,0,4)]),(0,[(0,3,4)]),(8,[(0,3,4),(1,2,76)]),(11,[(1,0,2),(1,2,76)]),(2,[(2,84,5),(0,3,4),(1,2,76)]),(6,[(1,0,2),(2,84,5)]),(1,[(1,3,5),(0,6,7),(3,8,4)]),(2,[(3,1,3),(1,97,4),(1,4,5),(3,1,20)]),(8,[(1,97,4),(1,4,5)]),(0,[(3,1,3),(1,97,4),(1,4,5),(3,1,20)]),(1,[(2,3,4),(1,3,5),(0,6,7)]),(3,[(2,3,4),(1,3,5)]),(2,[(2,3,4),(1,3,5),(0,6,7)]),(9,[(2,3,4),(1,3,5)]),(11,[(1,1,2),(3,78,20)]),(0,[(0,19,3),(1,4,5),(3,78,20)]),(0,[(0,19,4),(1,100,5),(1,3,5)]),(1,[(0,19,4),(1,100,5)]),(0,[(1,19,4),(0,0,82)]),(2,[(1,1,2),(1,19,4),(3,2,82)]),(1,[(1,19,4),(0,0,82),(3,2,82)]),(0,[(1,19,5),(3,5,66)]),(2,[(1,1,2),(1,19,5),(3,2,66),(3,5,66)]),(8,[(1,19,5),(3,2,66),(3,5,66)]),(2,[(1,1,2),(1,19,4),(0,3,82)]),(1,[(1,19,4),(0,0,82)]),(1,[(1,19,4),(0,0,82),(0,3,82)]),(0,[(1,19,4),(0,0,82),(0,3,82)]),(9,[(0,33,3),(1,34,5)]),(12,[(1,0,1),(2,6,5)]),(2,[(1,1,2),(1,19,4)]),(1,[(1,19,4),(3,0,82)]),(1,[(1,19,4),(3,0,82),(3,3,82)]),(0,[(1,19,4),(3,0,82)]),(0,[(1,19,4),(3,0,82),(3,3,82)]),(4,[(1,1,2),(1,19,4),(3,0,82)]),(8,[(1,19,4),(3,3,82)]),(11,[(3,0,4)]),(11,[(1,0,1),(2,6,85)]),(11,[(1,1,2),(2,19,85)]),(28,[]),(0,[(1,19,4),(3,4,82)]),(2,[(1,1,2),(1,19,4),(3,2,82),(3,4,82)]),(8,[(1,19,4),(3,2,82),(3,4,82)]),(1,[(1,19,4),(3,2,82),(3,4,82)]),(11,[(1,1,2),(1,19,4)]),(12,[(1,1,2),(1,19,4),(2,82,5)]),(2,[(3,1,4),(0,3,5),(1,1,13),(2,14,4)]),(4,[(3,1,4),(1,1,13),(2,14,4)]),(8,[(0,3,5),(2,14,4)]),(1,[(1,4,5),(0,16,5),(1,2,114)]),(2,[(1,1,4),(1,4,5),(0,16,5),(1,2,114)]),(8,[(1,4,5),(0,16,5),(1,2,114)]),(6,[(0,16,5),(1,2,114)]),(10,[(1,1,4)]),(11,[(1,1,4)]),(3,[(0,3,4),(1,2,76)]),(11,[(1,1,2),(1,2,76)]),(1,[(2,19,5),(0,3,4),(1,2,76)]),(3,[(1,1,2)]),(1,[]),(6,[(1,1,2),(2,96,5)]),(9,[(0,3,4),(2,96,5)]),(2,[(3,2,4),(1,3,5),(3,2,7),(1,118,4)]),(6,[(1,3,5),(3,2,7)]),(9,[(1,3,5),(1,118,4)]),(1,[(3,2,4),(1,3,5),(3,2,7),(1,118,4)]),(4,[(3,2,4),(1,118,4)]),(1,[(3,2,3),(1,57,5),(3,25,58)]),(0,[(3,1,4),(1,57,5),(3,25,58)]),(10,[(3,1,4),(3,25,58)]),(11,[(3,1,4),(3,25,58)]),(5,[(3,1,3)]),(6,[(2,38,5)]),(1,[(1,2,4),(1,4,5),(2,38,5)]),(4,[(0,4,5),(1,4,5),(3,41,20)]),(11,[(2,42,0)]),(1,[(1,2,5),(1,4,5)]),(4,[(1,2,5),(1,4,5)]),(4,[(1,1,2),(1,2,5),(1,4,5)]),(10,[(0,3,20),(2,19,21)]),(2,[(1,1,4),(0,3,16),(1,3,16),(3,122,123)]),(8,[(0,3,16),(1,3,16),(3,122,123)]),(1,[(0,3,16),(1,3,16),(3,122,123)]),(0,[(1,1,4),(0,3,16),(1,3,16),(3,122,123)]),(2,[(1,1,4),(0,3,5),(1,3,5),(3,13,7)]),(0,[(1,1,4),(0,3,5),(1,3,5),(3,13,7)]),(1,[(2,3,4)]),(1,[(1,2,63),(3,5,66)]),(0,[(3,1,4),(1,4,5),(3,25,20)]),(2,[(3,1,4),(1,2,5),(1,4,5),(3,25,20)]),(1,[(1,2,5),(1,4,5),(3,25,20)]),(2,[(1,1,2),(0,19,4),(1,19,4),(3,100,82)]),(8,[(0,19,4),(1,19,4),(3,100,82)]),(1,[(0,19,4),(1,19,4),(3,100,82)]),(13,[(1,1,2),(3,100,82)]),(9,[(0,19,4),(1,19,4),(3,100,82)]),(0,[(0,19,4),(1,19,4),(3,100,82)]),(10,[(0,19,4),(1,19,4),(3,100,82)]),(1,[(1,4,5),(2,16,5)]),(2,[(1,1,4),(1,4,5),(3,1,20),(2,16,5)]),(8,[(1,4,5),(2,16,5)]),(0,[(1,1,4),(1,4,5),(3,1,20),(2,16,5)]),(1,[(0,4,5),(1,4,5),(1,0,20),(3,41,20)]),(0,[(0,4,5),(1,4,5),(1,0,20),(3,41,20)]),(9,[(1,57,5),(0,4,58)]),(2,[(1,1,4),(0,16,5),(1,16,5),(3,114,50)]),(8,[(0,16,5),(1,16,5),(3,114,50)]),(1,[(0,16,5),(1,16,5),(3,114,50)]),(0,[(1,1,4),(0,16,5),(1,16,5),(3,114,50)]),(0,[(0,19,4),(1,3,5),(3,100,7)]),(1,[(1,16,5),(3,4,50)]),(2,[(1,1,4),(1,16,5),(3,1,50),(3,4,50)]),(8,[(1,16,5),(3,4,50)]),(0,[(1,1,4),(1,16,5),(3,1,50),(3,4,50)]),(1,[(1,16,5),(3,4,50),(3,5,50)]),(2,[(1,1,4),(1,16,5),(3,4,50),(3,5,50)]),(8,[(1,16,5),(3,4,50),(3,5,50)]),(2,[(2,4,5),(1,133,5),(3,1,20)]),(8,[(2,4,5),(1,133,5)]),(1,[(2,4,5),(1,133,5)]),(2,[(2,4,5),(1,133,2),(3,1,134)]),(8,[(2,4,5),(1,133,2)]),(0,[(2,4,5),(3,1,134)]),(6,[(3,1,134)]),(1,[(1,4,5),(0,3,20)]),(2,[(1,4,5)]),(3,[(1,4,5)]),(2,[(1,4,5),(0,3,20),(1,1,21)]),(8,[(1,4,5),(0,3,20)]),(4,[(1,4,5),(1,1,21)]),(11,[(1,1,21)]),(2,[(1,4,5),(1,2,20)]),(3,[(1,4,5),(1,2,20)]),(1,[(1,4,5),(1,2,20)]),(0,[(1,4,5)]),(14,[]),(2,[(1,4,5),(3,1,20)]),(3,[(1,4,5),(3,1,20)]),(0,[(0,4,5),(1,4,5),(3,41,20)]),(1,[(0,4,5),(1,4,5)]),(0,[(0,4,5),(1,4,5),(1,1,20)]),(2,[(0,4,5),(1,4,5),(1,1,20)]),(5,[(1,1,20)]),(1,[(0,4,5),(1,4,5),(1,0,20)]),(2,[(0,4,5),(1,4,5)]),(5,[(1,0,20)]),(0,[(0,4,5),(1,4,5),(1,0,20)]),(2,[(3,3,5),(1,137,4),(3,1,138)]),(8,[(3,3,5),(1,137,4)]),(1,[(3,3,5),(1,137,4)]),(10,[(3,1,138)]),(2,[(3,3,5),(1,137,1),(2,140,4)]),(8,[(3,3,5),(2,140,4)]),(1,[(3,3,5),(2,140,4)]),(0,[(3,3,5),(1,137,1),(2,140,4)]),(10,[(2,140,4)]),(4,[(2,140,4)]),(1,[(1,3,5),(3,4,7),(1,102,2)]),(9,[(1,3,5),(3,4,7)]),(2,[(1,3,5),(3,4,7),(1,102,2)]),(0,[(1,3,5),(3,4,7)]),(1,[(1,3,5),(3,4,7)]),(2,[(1,3,5),(3,4,7),(1,102,1)]),(8,[(1,3,5),(3,4,7)]),(1,[(1,3,5),(3,2,7)]),(2,[(1,3,5),(3,2,7),(1,118,1)]),(8,[(1,3,5),(3,2,7)]),(2,[(0,3,5),(1,1,13),(2,14,4)]),(5,[(2,14,4)]),(1,[(0,3,5),(2,14,4)]),(0,[(0,3,5),(1,1,13),(2,14,4)]),(10,[(2,14,4)]),(11,[(2,14,4)]),(0,[(0,3,5),(1,1,13),(1,14,4)]),(10,[(1,14,4)]),(2,[(0,3,5),(1,1,13),(1,14,4)]),(4,[(1,1,13),(1,14,4)]),(11,[(1,14,4)]),(3,[(0,3,5),(1,1,13)]),(2,[(0,4,5),(1,4,5),(3,1,20)]),(0,[(0,3,5),(1,1,13),(0,14,4)]),(10,[(0,14,4)]),(2,[(0,3,5),(1,1,13),(0,14,4)]),(4,[(1,1,13),(0,14,4)]),(11,[(0,14,4)]),(9,[(0,3,5),(1,1,13)]),(1,[(0,3,5)]),(11,[(3,0,14)]),(2,[(0,3,5),(1,1,13)]),(0,[(0,3,5),(1,1,13),(1,0,14)]),(4,[(1,1,13),(1,0,14)]),(8,[(0,3,5)]),(11,[(1,0,14)]),(2,[(3,3,4),(1,147,2),(3,1,148)]),(8,[(3,3,4),(1,147,2)]),(1,[(3,3,4),(1,147,2)]),(2,[(3,3,4),(1,147,1),(2,150,2)]),(8,[(3,3,4),(2,150,2)]),(0,[(3,3,4),(1,147,1)]),(1,[(3,3,4),(2,150,2)]),(0,[(2,3,4),(1,3,5)]),(12,[(3,2,7)]),(2,[(2,3,4),(1,3,5),(3,2,7)]),(1,[(2,3,4),(1,3,5),(3,2,7)]),(2,[(2,3,4),(1,91,5),(1,4,5)]),(4,[(1,91,5),(1,4,5)]),(6,[(1,91,5)]),(2,[(2,3,4),(1,91,2),(3,1,152)]),(8,[(2,3,4),(1,91,2)]),(0,[(2,3,4),(3,1,152)]),(12,[(3,1,152)]),(2,[(2,3,4),(1,91,1),(2,154,5)]),(8,[(2,3,4),(2,154,5)]),(1,[(2,3,4),(2,154,5)]),(0,[(2,3,4),(1,91,1),(2,154,5)]),(2,[(2,3,4),(1,91,1),(2,154,2)]),(8,[(2,3,4),(2,154,2)]),(0,[(2,3,4),(1,91,1)]),(1,[(2,3,4),(2,154,2)]),(12,[(2,154,2)]),(1,[(1,3,4),(1,158,2)]),(0,[(1,3,4),(3,1,157)]),(2,[(1,3,4),(3,1,157),(1,158,2)]),(8,[(1,3,4),(1,158,2)]),(2,[(0,3,4),(1,76,5),(3,1,85)]),(8,[(0,3,4),(1,76,5)]),(1,[(0,3,4),(1,76,5)]),(2,[(0,3,4),(1,2,76),(2,96,5)]),(1,[(0,3,4),(1,2,76),(2,96,5)]),(11,[(1,2,76)]),(2,[(0,3,4),(1,1,76),(2,161,5)]),(8,[(0,3,4),(2,161,5)]),(1,[(0,3,4),(2,161,5)]),(0,[(0,3,4),(1,1,76),(2,161,5)]),(4,[(1,1,76),(2,161,5)]),(6,[(2,161,5)]),(2,[(3,2,5),(1,163,4),(3,1,164)]),(8,[(3,2,5),(1,163,4)]),(1,[(3,2,5),(1,163,4)]),(0,[(1,163,4),(3,1,164)]),(2,[(3,2,5),(1,163,1),(2,166,4)]),(8,[(3,2,5),(2,166,4)]),(1,[(3,2,5),(2,166,4)]),(0,[(1,163,1),(2,166,4)]),(11,[(2,166,4)]),(0,[(1,4,5),(0,3,20)]),(2,[(1,2,5),(1,4,5),(0,3,20)]),(3,[(1,2,5),(1,4,5)]),(1,[(1,2,5),(2,3,4),(1,91,2)]),(9,[(2,3,4)]),(2,[(1,2,5),(2,3,4),(1,91,2)]),(3,[(1,3,5),(3,1,7)]),(2,[(1,3,5),(3,1,7)]),(4,[(3,2,4)]),(3,[(3,2,4)]),(2,[(3,2,4)]),(1,[(3,2,4),(1,3,5)]),(2,[(1,3,5)]),(2,[(3,2,4),(1,117,1)]),(3,[(3,2,4),(1,117,1)]),(6,[(1,3,5)]),(0,[(1,117,1),(1,3,5)]),(10,[(1,117,1)]),(4,[(3,2,4),(1,117,1)]),(2,[(3,2,4),(1,117,1),(2,169,5)]),(8,[(3,2,4),(2,169,5)]),(1,[(3,2,4),(2,169,5)]),(0,[(1,117,1),(2,169,5)]),(1,[(1,2,4),(2,38,5)]),(2,[(1,2,4),(2,38,5),(1,52,1)]),(8,[(1,2,4),(2,38,5)]),(2,[(1,2,4),(1,38,5),(3,2,39)]),(9,[(1,38,5)]),(1,[(1,2,4),(1,38,5),(3,2,39)]),(2,[(1,2,4),(1,38,5),(3,1,39)]),(8,[(1,2,4),(1,38,5)]),(0,[(1,38,5),(3,1,39)]),(1,[(1,2,4),(1,38,5)]),(6,[(1,38,5),(3,1,39)]),(2,[(1,2,4),(1,4,5),(2,38,5)]),(1,[(0,3,5),(1,13,4),(1,0,172)]),(2,[(0,3,5),(1,13,4)]),(3,[(0,3,5),(1,13,4)]),(8,[(0,3,5),(1,13,4)]),(0,[(0,3,5),(1,13,4),(1,0,172)]),(4,[(1,13,4),(1,0,172)]),(9,[(0,3,5),(1,13,4)]),(11,[(1,0,172)]),(2,[(0,3,4),(1,76,5),(1,1,85)]),(0,[(0,3,4),(1,76,5),(1,1,85)]),(11,[(1,1,85)]),(2,[(1,2,4)]),(3,[(1,2,4)]),(1,[(1,2,4),(1,4,5)]),(0,[(1,4,5),(3,1,20)]),(2,[(1,2,4),(1,3,5),(3,38,7)]),(9,[(1,3,5),(3,38,7)]),(1,[(1,2,4),(1,3,5),(3,38,7)]),(4,[(1,2,4)]),(0,[(1,3,5),(3,1,7)]),(1,[(1,2,4),(1,3,5)]),(2,[(1,2,4),(0,3,38),(1,54,5)]),(9,[(0,3,38),(1,54,5)]),(1,[(1,2,4),(0,3,38),(1,54,5)]),(0,[(0,3,38),(1,54,5)]),(2,[(1,2,4),(1,3,4),(3,2,157)]),(9,[(1,3,4)]),(1,[(1,2,4),(1,3,4),(3,2,157)]),(0,[(3,1,38),(1,3,5)]),(4,[(1,2,4),(3,1,38)]),(1,[(1,3,5)]),(10,[(3,1,38)]),(2,[(1,2,4),(3,1,38)]),(3,[(1,2,4),(3,1,38)]),(0,[(2,3,4)]),(0,[(3,1,38)]),(5,[(1,2,4),(3,1,38)]),(2,[(2,3,4)]),(3,[(2,3,4)]),(2,[(1,3,4)]),(3,[(1,3,4)]),(0,[(3,1,38),(1,3,4)]),(15,[]),(1,[(1,2,4),(1,3,5),(0,38,7)]),(9,[(1,3,5),(0,38,7)]),(2,[(1,2,4),(1,3,5),(0,38,7)]),(0,[(1,3,5),(0,38,7)]),(6,[(1,3,5),(0,38,7)]),(10,[(0,38,7)]),(2,[(1,2,4),(1,1,38)]),(3,[(1,2,4),(1,1,38)]),(1,[(1,2,4),(3,3,38)]),(0,[(1,1,38)]),(0,[(1,1,38),(3,3,38)]),(4,[(1,2,4),(1,1,38)]),(6,[(1,1,38)]),(2,[(1,2,4),(3,3,38)]),(9,[(3,3,38)]),(2,[(1,2,4),(0,3,38)]),(9,[(0,3,38)]),(1,[(1,2,4),(0,3,38)]),(12,[(1,2,4),(1,1,38)]),(2,[(3,2,3),(1,57,5),(3,4,58)]),(9,[(1,57,5),(3,4,58)]),(11,[(3,4,58)]),(2,[(3,2,3),(1,57,5)]),(3,[(3,2,3),(1,57,5)]),(2,[(3,2,3),(1,57,5),(0,4,58)]),(1,[(3,2,3),(1,57,5)]),(1,[(3,2,3),(1,57,5),(0,4,58)]),(2,[(3,2,3),(1,57,5),(3,1,58)]),(8,[(3,2,3),(1,57,5)]),(0,[(1,57,5),(3,1,58)]),(10,[(3,1,58)]),(11,[(3,1,58)]),(2,[(3,2,3),(1,57,4),(2,4,5)]),(6,[(3,2,3)]),(0,[(1,57,4),(2,4,5)]),(11,[(1,57,4)]),(9,[(1,57,4),(2,4,5)]),(2,[(2,4,5),(1,133,1),(2,179,2)]),(8,[(2,4,5),(2,179,2)]),(0,[(2,4,5),(1,133,1)]),(1,[(2,4,5),(2,179,2)]),(2,[(3,2,3),(1,57,1),(2,182,5)]),(8,[(3,2,3),(2,182,5)]),(1,[(3,2,3),(2,182,5)]),(0,[(1,57,1),(2,182,5)]),(10,[(1,57,1)]),(2,[(3,2,4),(1,117,5),(3,1,184)]),(8,[(3,2,4),(1,117,5)]),(1,[(3,2,4),(1,117,5)]),(0,[(1,117,5),(3,1,184)]),(1,[(1,2,3),(2,186,4)]),(2,[(1,2,3),(2,186,4),(1,187,1)]),(8,[(1,2,3),(2,186,4)]),(0,[(2,186,4),(1,187,1)]),(2,[(1,1,5)]),(3,[(1,1,5)]),(2,[(1,1,5),(3,4,63),(1,132,2)]),(8,[(3,4,63),(1,132,2)]),(1,[(3,4,63),(1,132,2)]),(10,[(3,4,63)]),(11,[(3,4,63),(1,132,2)]),(0,[(1,1,5),(3,4,63)]),(2,[(3,2,3),(1,57,1),(2,182,4)]),(8,[(3,2,3),(2,182,4)]),(1,[(3,2,3),(2,182,4)]),(0,[(1,57,1),(2,182,4)]),(12,[(2,182,4)]),(6,[(1,1,5)]),(0,[(1,1,5),(2,4,63),(3,4,63)]),(8,[(2,4,63),(3,4,63)]),(2,[(1,1,5),(2,4,63),(3,4,63)]),(1,[(2,4,63),(3,4,63)]),(1,[(2,4,63),(1,191,5)]),(0,[(1,1,5),(2,4,63),(1,191,5)]),(8,[(2,4,63),(1,191,5)]),(2,[(1,1,5),(2,4,63),(1,191,5)]),(11,[(2,4,63)]),(4,[(2,4,5)]),(1,[(2,4,5),(3,4,63)]),(2,[(1,1,5),(2,4,5),(3,4,63)]),(8,[(2,4,5),(3,4,63)]),(2,[(0,3,5),(1,13,4),(3,1,172)]),(1,[(0,3,5),(1,13,4)]),(10,[(3,1,172)]),(2,[(1,1,5),(2,4,5),(1,133,1)]),(8,[(2,4,5)]),(0,[(1,1,5),(2,4,5),(1,133,1)]),(10,[(1,133,1)]),(11,[(1,133,1)]),(1,[(2,4,5)]),(2,[(1,1,5),(1,4,5),(3,4,63)]),(8,[(1,4,5),(3,4,63)]),(1,[(1,4,5),(3,4,63)]),(0,[(1,1,5),(1,4,5),(3,4,63)]),(11,[(3,4,63)]),(2,[(1,1,5),(1,4,63)]),(3,[(1,1,5),(1,4,63)]),(2,[(1,1,5),(0,3,63),(1,4,63)]),(3,[(1,1,5),(0,3,63)]),(1,[(1,4,63)]),(5,[(1,4,63)]),(11,[(1,4,63)]),(1,[(0,3,63),(1,4,63)]),(0,[(1,1,5),(1,4,63)]),(12,[(1,1,5),(1,4,63)]),(8,[(0,3,63),(1,2,68)]),(2,[(1,1,5),(0,3,63),(1,2,68)]),(4,[(1,1,5),(1,2,68)]),(1,[(0,3,63),(1,2,68)]),(11,[(1,2,68)]),(12,[(1,1,5)]),(0,[(1,1,5),(0,3,63)]),(1,[(2,3,4),(1,91,63)]),(0,[(1,1,5),(2,3,4),(1,91,63)]),(8,[(2,3,4),(1,91,63)]),(2,[(1,1,5),(2,3,4),(1,91,63)]),(0,[(1,1,5),(0,3,4),(1,76,5)]),(2,[(1,1,5),(0,3,4),(1,76,5)]),(4,[(1,1,5),(1,76,5)]),(5,[(0,3,4)]),(2,[(0,3,4),(1,2,76)]),(1,[(0,3,4),(1,2,76)]),(4,[(1,1,5),(1,2,76)]),(5,[(0,3,4),(1,2,76)]),(0,[(1,1,5),(0,3,4)]),(12,[(1,1,5),(3,2,63)]),(3,[(1,1,5),(3,2,63)]),(2,[(1,1,5),(3,2,63)]),(0,[(1,1,5),(2,3,4)]),(1,[(3,2,63),(1,105,4)]),(0,[(1,1,5),(1,105,4)]),(2,[(1,1,5),(3,2,63),(1,105,4)]),(8,[(3,2,63),(1,105,4)]),(10,[(1,105,4)]),(6,[(1,1,5),(3,2,63)]),(11,[(3,2,63),(1,105,4)]),(11,[(3,2,20)]),(12,[(1,4,5),(3,2,20)]),(1,[(3,2,3),(1,4,5),(3,2,20)]),(9,[(1,4,5)]),(2,[(3,2,3),(1,4,5),(3,2,20)]),(2,[(1,1,5),(1,2,63),(3,5,66)]),(8,[(1,2,63),(3,5,66)]),(0,[(1,1,5),(3,5,66)]),(11,[(1,2,63)]),(2,[(1,1,5),(1,2,63)]),(3,[(1,1,5),(1,2,63)]),(2,[(1,1,5),(1,2,63),(0,3,63)]),(1,[(1,2,63)]),(5,[(1,2,63)]),(10,[(0,3,63)]),(1,[(1,2,63),(0,3,63)]),(6,[(1,1,5),(0,3,63)]),(1,[(0,3,63)]),(1,[(3,2,4)]),(1,[(3,2,4),(0,3,63)]),(1,[(3,2,4),(3,117,63)]),(0,[(1,1,5),(3,117,63)]),(2,[(1,1,5),(3,2,4),(3,117,63)]),(8,[(3,2,4),(3,117,63)]),(1,[(3,2,4),(1,117,63)]),(0,[(1,1,5),(1,117,63)]),(2,[(1,1,5),(3,2,4),(1,117,63)]),(8,[(3,2,4),(1,117,63)]),(2,[(1,1,5),(3,2,4),(1,117,1)]),(8,[(3,2,4)]),(0,[(1,1,5),(1,117,1)]),(4,[(1,1,5)]),(2,[(1,1,5),(1,2,4),(3,38,63)]),(8,[(1,2,4),(3,38,63)]),(1,[(1,2,4),(3,38,63)]),(2,[(0,3,4),(1,1,76),(3,2,161)]),(8,[(0,3,4),(3,2,161)]),(0,[(0,3,4),(1,1,76)]),(1,[(0,3,4),(3,2,161)]),(4,[(1,1,76),(3,2,161)]),(6,[(3,2,161)]),(1,[(1,2,5),(2,3,4),(1,91,23)]),(9,[(2,3,4),(1,91,23)]),(2,[(1,2,5),(2,3,4),(1,91,23)]),(0,[(2,3,4),(1,91,23)]),(4,[(1,2,5),(1,91,23)]),(11,[(1,91,23)]),(1,[(1,2,4),(0,38,63)]),(0,[(1,1,5),(0,38,63)]),(1,[(3,2,3),(3,57,63)]),(0,[(1,1,5),(3,57,63)]),(2,[(1,1,5),(3,2,3),(3,57,63)]),(8,[(3,2,3),(3,57,63)]),(4,[(1,1,5),(3,57,63)]),(1,[(3,2,3),(1,57,63)]),(0,[(1,1,5),(1,57,63)]),(2,[(1,1,5),(3,2,3),(1,57,63)]),(4,[(1,1,5),(1,57,63)]),(8,[(3,2,3),(1,57,63)]),(3,[(0,3,4),(1,76,5)]),(2,[(0,3,4),(1,76,5)]),(9,[(0,3,4),(1,76,5)]),(11,[(1,0,85)]),(6,[(1,0,85)]),(26,[]),(2,[(1,1,5),(3,2,3),(1,57,1)]),(8,[(3,2,3)]),(0,[(1,1,5),(1,57,1)]),(8,[(0,4,63),(1,2,64)]),(2,[(1,1,5),(0,4,63),(1,2,64)]),(11,[(0,4,63),(1,2,64)]),(1,[(0,4,63),(1,2,64)]),(10,[(0,4,63)]),(6,[(1,2,20)]),(4,[(1,4,5),(1,2,20)]),(5,[(1,2,20)]),(2,[(3,1,4),(1,4,5)]),(3,[(3,1,4),(1,4,5)]),(2,[(2,3,5),(3,3,5)]),(2,[(3,1,4),(2,3,5),(3,3,5)]),(3,[(2,3,5),(3,3,5)]),(6,[(2,3,5),(3,3,5)]),(1,[(2,3,5),(3,3,5)]),(2,[(0,3,5),(1,3,5)]),(2,[(3,1,4),(0,3,5),(1,3,5)]),(3,[(0,3,5),(1,3,5)]),(6,[(0,3,5),(1,3,5)]),(1,[(0,3,5),(1,3,5)]),(4,[(3,1,4)]),(2,[(3,1,4),(0,3,5),(1,13,4)]),(6,[(0,3,5)]),(4,[(1,13,4)]),(1,[(0,3,5),(1,25,13)]),(0,[(3,1,4),(0,3,5),(1,25,13)]),(8,[(0,3,5),(1,25,13)]),(2,[(3,1,4),(0,3,5),(1,25,13)]),(2,[(3,1,4),(3,2,5),(1,163,4)]),(6,[(3,2,5)]),(0,[(3,1,4),(1,163,4)]),(4,[(3,2,5),(1,163,4)]),(12,[(1,4,5),(3,1,20)]),(1,[(3,2,3),(1,4,5)]),(3,[(3,2,3)]),(2,[(3,2,3)]),(2,[(1,1,5),(1,2,4),(0,38,63)]),(8,[(1,2,4),(0,38,63)]),(10,[(0,38,63)]),(6,[(1,1,5),(0,38,63)]),(2,[(3,1,4),(3,2,5),(1,163,25)]),(8,[(3,2,5),(1,163,25)]),(1,[(3,2,5),(1,163,25)]),(0,[(3,1,4),(1,163,25)]),(2,[(3,1,4),(1,2,5),(1,4,5)]),(6,[(1,2,5)]),(0,[(3,1,4),(1,4,5)]),(0,[(3,1,4),(1,57,5)]),(4,[(1,57,5)]),(2,[(3,1,4)]),(3,[(3,1,4)]),(4,[(3,1,4),(1,57,5)]),(12,[(3,1,4)]),(2,[(3,1,4),(1,2,3),(3,25,186)]),(8,[(1,2,3),(3,25,186)]),(1,[(1,2,3),(3,25,186)]),(0,[(3,1,4),(3,25,186)]),(10,[(3,1,4),(3,25,186)]),(2,[(3,1,4),(1,25,5),(3,2,5)]),(5,[(3,1,4)]),(1,[(1,25,5),(3,2,5)]),(0,[(3,1,4),(1,25,5)]),(1,[(1,25,5),(1,2,5)]),(2,[(3,1,4),(1,25,5),(1,2,5)]),(8,[(1,25,5),(1,2,5)]),(2,[(3,1,4),(1,25,5)]),(3,[(3,1,4),(1,25,5)]),(1,[(1,25,5)]),(1,[(1,25,5),(3,2,3)]),(4,[(3,1,4),(1,25,5)]),(12,[(3,1,4),(1,25,5)]),(2,[(3,1,4),(1,25,2)]),(3,[(3,1,4),(1,25,2)]),(1,[(1,25,2),(1,3,5)]),(4,[(3,1,4),(1,25,2)]),(0,[(0,4,5),(1,1,41),(1,0,211)]),(3,[(0,4,5),(1,1,41)]),(2,[(0,4,5),(1,1,41)]),(9,[(0,4,5),(1,1,41)]),(6,[(1,0,211)]),(11,[(1,0,211)]),(2,[(3,1,4),(1,25,2),(2,210,5)]),(8,[(1,25,2),(2,210,5)]),(1,[(1,25,2),(2,210,5)]),(0,[(3,1,4),(2,210,5)]),(6,[(2,210,5)]),(1,[(1,25,2),(1,2,5)]),(2,[(1,2,5)]),(2,[(3,1,4),(1,25,2),(1,2,5)]),(8,[(1,25,2),(1,2,5)]),(4,[(1,2,5)]),(12,[(1,4,5)]),(0,[(3,1,38),(1,4,5)]),(6,[(3,1,38)]),(12,[(1,2,4),(3,1,38)]),(1,[(3,16,5),(1,214,4)]),(0,[(1,1,4),(3,16,5),(1,214,4)]),(8,[(3,16,5),(1,214,4)]),(2,[(1,1,4),(3,16,5),(1,214,4)]),(1,[(2,16,5),(1,127,2)]),(0,[(1,1,4),(2,16,5)]),(2,[(1,1,4),(2,16,5),(1,127,2)]),(8,[(2,16,5),(1,127,2)]),(11,[(1,2,4),(3,1,38)]),(2,[(2,3,5)]),(3,[(2,3,5)]),(0,[(3,1,38),(2,3,5)]),(1,[(2,3,5)]),(2,[(1,1,5),(0,3,63)]),(1,[(0,3,63),(2,4,63)]),(17,[]),(12,[(1,1,5),(2,4,63)]),(3,[(1,1,5),(2,4,63)]),(2,[(1,1,5),(2,4,63)]),(2,[(1,1,5),(0,3,63),(2,4,63)]),(2,[(1,1,4),(1,16,5),(3,4,50)]),(2,[(1,1,4),(1,16,5),(3,5,50)]),(8,[(1,16,5),(3,5,50)]),(1,[(1,16,5),(3,5,50)]),(0,[(1,1,4),(1,16,5),(3,5,50)]),(1,[(3,2,3),(1,57,4),(1,61,5)]),(9,[(1,57,4),(1,61,5)]),(2,[(3,2,3),(1,57,4),(1,61,5)]),(0,[(1,57,4),(1,61,5)]),(4,[(1,57,4),(1,61,5)]),(0,[(1,1,4),(1,16,5),(3,4,50)]),(2,[(1,1,4),(1,16,5)]),(3,[(1,1,4),(1,16,5)]),(2,[(1,1,4),(1,16,5),(0,3,50)]),(8,[(1,16,5),(0,3,50)]),(1,[(1,16,5),(0,3,50)]),(0,[(1,1,4),(1,16,5)]),(1,[(0,16,5),(1,16,5)]),(0,[(1,1,4),(0,16,5),(1,16,5)]),(8,[(0,16,5),(1,16,5)]),(2,[(1,1,4),(0,16,5),(1,16,5)]),(5,[(1,1,4)]),(6,[(0,16,5),(1,16,5)]),(0,[(1,1,5),(0,3,38)]),(2,[(1,1,4),(0,16,5),(2,3,114)]),(8,[(0,16,5),(2,3,114)]),(1,[(0,16,5),(2,3,114)]),(0,[(1,1,4),(0,16,5),(2,3,114)]),(6,[(0,16,5),(2,3,114)]),(1,[(3,4,5),(1,220,16)]),(0,[(1,1,4),(3,4,5),(1,220,16)]),(8,[(3,4,5),(1,220,16)]),(2,[(1,1,4),(3,4,5),(1,220,16)]),(1,[(2,4,5),(3,133,16)]),(0,[(1,1,4),(2,4,5),(3,133,16)]),(8,[(2,4,5),(3,133,16)]),(2,[(1,1,4),(2,4,5),(3,133,16)]),(2,[(1,1,4),(1,4,5),(2,16,5)]),(0,[(1,1,4),(1,4,5),(2,16,5)]),(6,[(2,16,5)]),(9,[(0,3,38),(1,1,54)]),(2,[(1,2,4),(0,3,38),(1,1,54)]),(6,[(0,3,38),(1,1,54)]),(2,[(1,1,4),(1,4,5),(3,1,20)]),(8,[(1,4,5)]),(0,[(1,1,4),(1,4,5),(3,1,20)]),(1,[(1,4,5),(0,16,5)]),(0,[(1,1,4),(1,4,5),(0,16,5)]),(8,[(1,4,5),(0,16,5)]),(2,[(1,1,4),(1,4,5),(0,16,5)]),(6,[(0,16,5)]),(1,[(0,3,4),(1,76,63)]),(0,[(1,1,5),(0,3,4),(1,76,63)]),(8,[(0,3,4),(1,76,63)]),(2,[(1,1,5),(0,3,4),(1,76,63)]),(11,[(1,76,63)]),(1,[(3,3,5),(3,137,16)]),(0,[(1,1,4),(3,3,5),(3,137,16)]),(8,[(3,3,5),(3,137,16)]),(2,[(1,1,4),(3,3,5),(3,137,16)]),(4,[(1,1,4)]),(1,[(3,3,5),(1,137,16)]),(0,[(1,1,4),(3,3,5),(1,137,16)]),(8,[(3,3,5),(1,137,16)]),(2,[(1,1,4),(3,3,5),(1,137,16)]),(12,[(3,1,58)]),(1,[(1,3,5),(0,16,7)]),(0,[(1,1,4),(1,3,5),(0,16,7)]),(8,[(1,3,5),(0,16,7)]),(2,[(1,1,4),(1,3,5),(0,16,7)]),(0,[(1,1,4),(0,3,5),(1,3,5)]),(8,[(0,3,5),(1,3,5)]),(2,[(1,1,4),(0,3,5),(1,3,5)]),(1,[(0,3,5),(1,13,16)]),(0,[(1,1,4),(0,3,5),(1,13,16)]),(8,[(0,3,5),(1,13,16)]),(2,[(1,1,4),(0,3,5),(1,13,16)]),(6,[(0,3,5),(1,13,16)]),(0,[(1,1,4),(0,3,5),(1,1,13)]),(2,[(1,1,4),(0,3,5),(1,1,13)]),(4,[(1,1,4),(1,1,13)]),(12,[(1,1,4)]),(1,[(2,3,16),(3,3,16)]),(2,[(1,1,4),(1,3,16),(3,4,123)]),(8,[(1,3,16),(3,4,123)]),(1,[(1,3,16),(3,4,123)]),(0,[(1,1,4),(1,3,16),(3,4,123)]),(2,[(1,1,4),(1,4,5)]),(3,[(1,1,4),(1,4,5)]),(1,[(1,4,5)]),(5,[(0,3,20)]),(1,[(0,3,16),(1,4,5)]),(4,[(1,1,4),(1,4,5)]),(1,[(0,3,16),(1,3,16)]),(0,[(1,1,4),(0,3,16),(1,3,16)]),(8,[(0,3,16),(1,3,16)]),(2,[(1,1,4),(0,3,16),(1,3,16)]),(2,[(1,4,5),(0,3,20)]),(2,[(0,3,4),(1,76,5),(1,2,85)]),(0,[(0,3,4),(1,76,5)]),(11,[(1,2,85)]),(2,[(1,1,4),(0,3,16),(1,122,5)]),(8,[(0,3,16),(1,122,5)]),(1,[(0,3,16),(1,122,5)]),(4,[(1,1,4),(1,122,5)]),(2,[(1,1,2),(1,1,4),(2,19,5)]),(8,[(2,19,5)]),(0,[(1,1,4),(2,19,5)]),(6,[(1,1,2),(2,19,5)]),(11,[(1,1,2),(1,1,4)]),(2,[(3,1,3),(1,97,5),(3,2,232)]),(8,[(1,97,5),(3,2,232)]),(1,[(1,97,5),(3,2,232)]),(10,[(3,1,3)]),(11,[(3,2,232)]),(4,[(1,1,2)]),(1,[(2,19,3),(3,19,3)]),(0,[(2,19,3),(3,19,3)]),(9,[(2,19,3),(3,19,3)]),(8,[(2,19,3),(3,19,3)]),(2,[(1,1,2),(2,19,3),(3,19,3)]),(2,[(2,3,4),(1,91,5),(3,2,92)]),(9,[(2,3,4),(1,91,5)]),(1,[(2,3,4),(1,91,5),(3,2,92)]),(11,[(3,2,92)]),(2,[(1,1,2),(1,19,3),(3,2,79)]),(8,[(1,19,3),(3,2,79)]),(0,[(1,19,3)]),(1,[(1,19,3),(3,2,79)]),(1,[(1,4,5),(0,19,20)]),(0,[(1,4,5),(0,19,20)]),(2,[(1,1,2),(1,4,5),(0,19,20)]),(2,[(1,1,2),(0,19,3)]),(3,[(1,1,2),(0,19,3)]),(6,[(1,1,2),(0,19,3)]),(1,[(0,19,3),(3,19,4)]),(0,[(0,19,3),(3,19,4)]),(12,[(1,1,2),(3,19,4)]),(3,[(1,1,2),(3,19,4)]),(2,[(1,1,2),(3,19,4)]),(2,[(2,3,4),(1,91,2)]),(3,[(2,3,4),(1,91,2)]),(1,[(2,3,4),(1,91,2)]),(4,[(1,1,5),(1,91,2)]),(0,[(1,1,4),(1,4,5)]),(2,[(1,1,4),(1,2,5),(1,4,5)]),(3,[(1,1,2),(1,19,4)]),(8,[(0,19,3)]),(12,[(1,1,2),(1,19,4)]),(2,[(2,3,4),(1,91,5),(3,1,92)]),(8,[(2,3,4),(1,91,5)]),(0,[(2,3,4),(1,91,5),(3,1,92)]),(11,[(3,1,92)]),(2,[(1,2,4),(1,3,38),(3,4,55)]),(9,[(1,3,38),(3,4,55)]),(1,[(1,2,4),(1,3,38),(3,4,55)]),(12,[(1,1,2),(2,19,5)]),(0,[(2,19,5),(2,3,4)]),(2,[(1,1,2),(2,19,5)]),(1,[(2,19,5),(2,3,4)]),(2,[(1,1,2),(1,4,5),(3,19,20)]),(8,[(1,4,5),(3,19,20)]),(1,[(1,4,5),(3,19,20)]),(0,[(1,4,5),(3,19,20)]),(2,[(1,1,2),(1,2,5)]),(3,[(1,1,2),(1,2,5)]),(1,[(1,2,5)]),(1,[(1,2,5),(2,3,4)]),(12,[(1,1,2),(1,2,5)]),(10,[(2,3,4)]),(2,[(1,2,5),(2,3,4)]),(2,[(1,1,2),(1,1,4),(1,4,5)]),(2,[(1,1,2),(3,19,3),(1,181,1)]),(8,[(3,19,3)]),(0,[(3,19,3),(1,181,1)]),(1,[(3,19,3)]),(5,[(2,3,4)]),(0,[(0,19,3),(1,4,5)]),(2,[(1,2,5),(1,4,5)]),(2,[(1,1,2),(1,2,5),(1,4,5)]),(2,[(1,4,5),(1,2,20),(3,1,39)]),(8,[(1,4,5),(1,2,20)]),(2,[(1,1,5),(1,2,4),(2,38,63)]),(8,[(1,2,4),(2,38,63)]),(0,[(1,1,5),(2,38,63)]),(6,[(1,1,5),(2,38,63)]),(2,[(1,2,4),(1,2,5)]),(3,[(1,2,4),(1,2,5)]),(4,[(1,2,4),(1,2,5)]),(1,[(1,2,4),(1,2,5)]),(12,[(1,2,4),(1,2,5)]),(2,[(3,1,3),(1,2,5)]),(1,[(0,4,63),(1,4,63)]),(0,[(1,1,5),(0,4,63),(1,4,63)]),(8,[(0,4,63),(1,4,63)]),(2,[(1,1,5),(0,4,63),(1,4,63)]),(11,[(0,4,63),(1,4,63)]),(8,[(0,3,63),(1,68,4)]),(2,[(1,1,5),(0,3,63),(1,68,4)]),(4,[(1,1,5),(1,68,4)]),(11,[(1,68,4)]),(1,[(0,3,63),(1,68,4)]),(0,[(1,1,4),(1,19,5)]),(2,[(1,1,2),(1,1,4),(1,19,5)]),(8,[(1,19,5)]),(6,[(1,1,2),(1,19,5)]),(2,[(1,1,5),(0,3,4),(3,76,63)]),(8,[(0,3,4),(3,76,63)]),(1,[(0,3,4),(3,76,63)]),(0,[(1,1,5),(0,3,4),(3,76,63)]),(11,[(3,76,63)]),(0,[(1,1,4),(0,19,4)]),(8,[(0,19,4)]),(2,[(1,1,2),(1,1,4),(0,19,4)]),(1,[(1,0,5),(2,3,4),(3,91,242)]),(2,[(2,3,4),(3,91,242)]),(8,[(2,3,4)]),(0,[(1,0,5),(2,3,4),(3,91,242)]),(4,[(1,0,5),(3,91,242)]),(6,[(1,0,5),(3,91,242)]),(5,[(2,3,4),(3,91,242)]),(11,[(3,91,242)]),(3,[(0,3,5),(1,2,13)]),(8,[(0,3,5),(1,2,13)]),(4,[(1,2,13)]),(10,[(3,0,4)]),(2,[(0,3,5),(1,2,13)]),(1,[(1,2,63),(3,4,66)]),(10,[(3,4,66)]),(2,[(1,1,5),(1,2,63),(3,4,66)]),(8,[(1,2,63),(3,4,66)]),(1,[(1,0,5),(0,3,4),(1,76,5)]),(0,[(1,0,5),(0,3,4),(1,76,5)]),(4,[(1,0,5),(1,76,5)]),(6,[(1,0,5)]),(2,[(3,3,5),(1,137,109)]),(1,[(3,0,4),(3,3,5),(1,137,109)]),(8,[(3,3,5)]),(0,[(3,0,4),(3,3,5),(1,137,109)]),(9,[(3,3,5)]),(4,[(3,0,4)]),(5,[(3,0,4)]),(2,[(1,1,2),(1,2,5),(2,19,5)]),(8,[(1,2,5),(2,19,5)]),(0,[(2,19,5)]),(5,[(1,1,2)]),(9,[(0,19,3)]),(2,[(1,1,2),(1,2,5),(0,19,3)]),(0,[(0,19,3)]),(1,[(1,2,5),(0,19,3)]),(4,[(1,1,2),(1,2,5)]),(6,[(1,1,2),(1,2,5)]),(10,[(0,19,3)]),(2,[(1,4,5),(1,1,20)]),(3,[(1,4,5),(1,1,20)]),(1,[(1,2,4),(1,3,4)]),(6,[(3,1,157)]),(2,[(1,3,4),(3,1,157)]),(3,[(1,3,4),(3,1,157)]),(1,[(1,0,4),(3,3,5),(3,137,94)]),(2,[(3,3,5),(3,137,94)]),(0,[(1,0,4),(3,3,5),(3,137,94)]),(4,[(1,0,4)]),(5,[(1,0,4)]),(2,[(3,1,4),(3,3,5),(1,137,4)]),(6,[(3,3,5)]),(9,[(0,3,5),(1,3,5)]),(2,[(0,3,4),(1,76,5),(3,2,85)]),(1,[(0,3,4),(1,76,5),(3,2,85)]),(2,[(1,1,2),(1,1,4)]),(3,[(1,1,2),(1,1,4)]),(0,[(1,1,4)]),(0,[(1,1,4),(2,19,3)]),(4,[(1,1,2),(1,1,4)]),(12,[(1,1,2),(1,1,4)]),(8,[(2,19,3)]),(2,[(1,1,2),(1,1,4),(1,2,5)]),(8,[(1,2,5)]),(2,[(1,1,4),(1,3,5),(3,16,7)]),(8,[(1,3,5),(3,16,7)]),(0,[(1,1,4),(1,3,5),(3,16,7)]),(2,[(3,1,3),(1,97,4),(2,4,5)]),(6,[(3,1,3)]),(1,[(1,97,4),(2,4,5)]),(11,[(1,97,4)]),(1,[(3,2,3),(1,57,16)]),(0,[(1,1,4),(1,57,16)]),(2,[(1,1,4),(3,2,3),(1,57,16)]),(4,[(1,1,4),(1,57,16)]),(8,[(3,2,3),(1,57,16)]),(2,[(0,3,5),(1,1,13),(3,14,4)]),(10,[(3,14,4)]),(4,[(1,1,13)]),(11,[(3,14,4)]),(0,[(1,1,5),(0,3,4),(1,1,76)]),(8,[(0,3,4)]),(2,[(1,1,5),(0,3,4),(1,1,76)]),(4,[(1,1,5),(1,1,76)]),(11,[(1,1,76)]),(3,[(2,3,4),(1,91,5)]),(2,[(2,3,4),(1,91,5)]),(0,[(2,3,4),(1,91,5)]),(11,[(1,0,2)]),(16,[]),(1,[(3,2,4),(2,3,5)]),(12,[(3,2,4),(1,117,1)]),(11,[(3,2,4),(1,117,1)]),(6,[(2,3,5)]),(0,[(1,117,1),(2,3,5)]),(1,[(3,0,4),(0,3,5),(1,109,13)]),(2,[(0,3,5),(1,109,13)]),(3,[(0,3,5)]),(0,[(3,0,4),(0,3,5),(1,109,13)]),(4,[(3,0,4),(1,109,13)]),(9,[(0,3,5)]),(2,[(0,3,4),(1,2,76),(3,1,96)]),(0,[(0,3,4),(3,1,96)]),(4,[(1,2,76),(3,1,96)]),(6,[(3,1,96)]),(2,[(1,2,5),(1,4,5),(3,1,20)]),(1,[(1,2,5),(0,3,4),(1,2,76)]),(9,[(0,3,4)]),(2,[(1,2,5),(0,3,4),(1,2,76)]),(4,[(1,2,5),(1,2,76)]),(2,[(1,2,4),(1,2,5),(2,38,5)]),(9,[(2,38,5)]),(1,[(1,2,4),(1,2,5),(2,38,5)]),(1,[(1,97,4),(1,98,5)]),(0,[(3,1,3),(1,97,4),(1,98,5)]),(8,[(1,97,4),(1,98,5)]),(2,[(3,1,3),(1,97,4),(1,98,5)]),(2,[(3,4,5),(2,94,5)]),(1,[(1,0,4),(3,4,5),(2,94,5)]),(8,[(3,4,5)]),(2,[(1,1,2)]),(1,[(0,19,4),(1,19,4)]),(9,[(0,19,4),(1,19,4)]),(8,[(0,19,4),(1,19,4)]),(2,[(1,1,2),(0,19,4),(1,19,4)]),(1,[(1,0,4),(1,3,5),(0,94,7)]),(2,[(1,3,5),(0,94,7)]),(8,[(1,3,5)]),(0,[(1,0,4),(1,3,5),(0,94,7)]),(9,[(1,3,5)]),(1,[(1,2,4),(2,3,38),(1,255,4)]),(9,[(2,3,38),(1,255,4)]),(2,[(1,2,4),(2,3,38),(1,255,4)]),(0,[(2,3,38),(1,255,4)]),(4,[(1,2,4),(1,255,4)]),(2,[(3,1,4),(1,25,5),(3,2,192)]),(8,[(1,25,5),(3,2,192)]),(1,[(1,25,5),(3,2,192)]),(1,[(1,0,4),(0,3,5),(1,3,5)]),(0,[(1,0,4),(0,3,5),(1,3,5)]),(8,[(1,19,4)]),(24,[]),(1,[(3,2,3),(1,4,5),(3,57,20)]),(9,[(1,4,5),(3,57,20)]),(2,[(3,2,3),(1,4,5),(3,57,20)]),(0,[(1,4,5),(3,57,20)]),(1,[(1,0,4),(0,3,5),(1,13,4)]),(0,[(1,0,4),(0,3,5),(1,13,4)]),(4,[(1,0,4),(1,13,4)]),(2,[(1,4,5),(3,258,20)]),(1,[(3,0,3),(1,4,5),(3,258,20)]),(0,[(3,0,3),(1,4,5),(3,258,20)]),(4,[(1,4,5),(3,258,20)]),(5,[(3,0,3),(3,258,20)]),(6,[(3,0,3),(3,258,20)]),(11,[(3,258,20)]),(2,[(3,2,3),(1,57,4),(3,1,61)]),(8,[(3,2,3),(1,57,4)]),(0,[(1,57,4),(3,1,61)]),(12,[(3,1,61)]),(1,[(1,2,4),(3,97,38)]),(2,[(3,1,3),(1,2,4),(3,97,38)]),(8,[(1,2,4),(3,97,38)]),(0,[(3,1,3),(3,97,38)]),(4,[(1,2,4),(3,97,38)]),(6,[(3,1,3),(3,97,38)]),(10,[(3,1,3),(3,97,38)]),(2,[(1,2,4),(1,2,5),(0,3,38)]),(6,[(0,3,38)]),(10,[(0,3,38)]),(2,[(1,1,4),(3,2,5),(1,163,1)]),(8,[(3,2,5)]),(0,[(1,1,4),(1,163,1)]),(6,[(3,2,5),(1,163,1)]),(2,[(1,258,5),(3,4,262)]),(1,[(3,0,3),(1,258,5),(3,4,262)]),(8,[(3,4,262)]),(0,[(3,0,3),(1,258,5),(3,4,262)]),(9,[(3,4,262)]),(11,[(3,4,262)]),(9,[(2,19,4),(3,19,4)]),(0,[(2,19,4),(3,19,4)]),(2,[(1,1,2),(2,19,4),(3,19,4)]),(10,[(2,19,4),(3,19,4)]),(2,[(1,1,2),(1,1,4),(0,19,3)]),(0,[(1,1,4),(0,19,3)]),(1,[(3,0,3),(1,258,4),(1,264,5)]),(2,[(1,258,4),(1,264,5)]),(3,[(1,264,5)]),(8,[(1,264,5)]),(0,[(3,0,3),(1,258,4),(1,264,5)]),(4,[(1,258,4),(1,264,5)]),(9,[(1,264,5)]),(6,[(3,0,3),(1,264,5)]),(11,[(1,258,4)]),(2,[(1,1,2),(1,1,4),(2,4,5)]),(4,[(3,1,4),(1,4,5)]),(12,[(3,1,4),(1,4,5)]),(2,[(0,3,4)]),(3,[(0,3,4)]),(0,[(2,19,5),(0,3,4)]),(1,[(0,3,4)]),(2,[(1,4,5),(2,94,5)]),(1,[(1,0,4),(1,4,5),(2,94,5)]),(0,[(1,0,4),(1,4,5),(2,94,5)]),(6,[(2,94,5)]),(0,[(0,3,5),(1,13,4),(1,1,172)]),(2,[(0,3,5),(1,13,4),(1,1,172)]),(10,[(1,1,172)]),(11,[(1,1,172)]),(0,[(1,1,4),(2,4,5),(1,133,5)]),(2,[(1,1,4),(2,4,5),(1,133,5)]),(2,[(1,1,4),(1,1,5),(3,4,63)]),(8,[(3,4,63)]),(0,[(1,1,4),(1,1,5),(3,4,63)]),(2,[(1,1,2),(1,1,4),(3,2,16)]),(8,[(3,2,16)]),(1,[(3,2,16)]),(0,[(1,0,1),(0,3,4),(1,1,76)]),(3,[(0,3,4),(1,1,76)]),(2,[(0,3,4),(1,1,76)]),(9,[(0,3,4),(1,1,76)]),(4,[(1,0,1),(1,1,76)]),(6,[(1,0,1)]),(1,[(3,0,3),(1,258,4),(1,4,5)]),(2,[(1,258,4),(1,4,5)]),(0,[(3,0,3),(1,258,4),(1,4,5)]),(4,[(1,258,4),(1,4,5)]),(5,[(3,0,3),(1,258,4)]),(4,[(0,4,5),(1,4,5)]),(1,[(1,19,4),(1,82,5)]),(0,[(1,19,4),(1,82,5)]),(2,[(1,1,2),(1,19,4),(1,82,5)]),(8,[(1,19,4),(1,82,5)]),(0,[(1,3,5)]),(0,[(1,1,4),(1,3,5)]),(1,[(2,6,4),(2,31,5)]),(2,[(2,6,4),(2,31,5)]),(0,[(1,0,1),(2,6,4),(2,31,5)]),(9,[(2,31,5)]),(2,[(1,1,4),(1,16,5),(3,1,50)]),(8,[(1,16,5)]),(0,[(1,1,4),(1,16,5),(3,1,50)]),(2,[(1,1,4),(1,2,4),(3,1,38)]),(8,[(1,2,4)]),(0,[(1,1,4),(3,1,38)]),(0,[(2,19,4),(1,3,5)]),(4,[(1,1,2),(2,19,4)]),(2,[(1,1,2),(2,19,4)]),(3,[(1,1,2),(2,19,4)]),(1,[(2,19,4),(1,3,5)]),(2,[(3,1,4),(0,3,5),(1,2,13)]),(6,[(0,3,5),(1,2,13)]),(1,[(0,3,5),(1,2,13)]),(2,[(2,4,5),(1,133,258)]),(1,[(3,0,3),(2,4,5),(1,133,258)]),(0,[(3,0,3),(2,4,5),(1,133,258)]),(9,[(2,4,5)]),(4,[(2,4,5),(1,133,258)]),(5,[(3,0,3),(1,133,258)]),(11,[(1,133,258)]),(2,[(0,3,5),(3,13,94)]),(1,[(1,0,4),(0,3,5),(3,13,94)]),(0,[(1,0,4),(0,3,5),(3,13,94)]),(2,[(1,1,4)]),(3,[(1,1,4)]),(0,[(1,1,4),(1,57,5)]),(4,[(1,1,4),(1,57,5)]),(2,[(1,1,4),(1,16,5),(3,2,50)]),(8,[(1,16,5),(3,2,50)]),(1,[(1,16,5),(3,2,50)]),(1,[(0,16,5),(1,3,114)]),(0,[(1,1,4),(0,16,5),(1,3,114)]),(8,[(0,16,5),(1,3,114)]),(2,[(1,1,4),(0,16,5),(1,3,114)]),(6,[(0,16,5),(1,3,114)]),(2,[(1,1,2),(1,19,5)]),(3,[(1,1,2),(1,19,5)]),(0,[(0,19,3),(1,19,5)]),(1,[(1,19,5)]),(1,[(0,19,3),(1,19,5)]),(12,[(1,1,5),(1,2,63)]),(1,[(1,2,63),(2,3,4)]),(9,[(0,19,3),(1,78,4)]),(8,[(0,19,3),(1,78,4)]),(2,[(1,1,2),(0,19,3),(1,78,4)]),(0,[(0,19,3),(1,78,4)]),(1,[(0,19,3),(1,78,4)]),(4,[(1,1,2),(1,78,4)]),(12,[(1,1,4),(1,4,5)]),(2,[(1,1,5),(1,4,5),(3,1,20)]),(0,[(1,1,5),(1,4,5),(3,1,20)]),(11,[(3,1,20)]),(2,[(1,258,4),(2,264,5)]),(1,[(3,0,3),(1,258,4),(2,264,5)]),(8,[(2,264,5)]),(0,[(3,0,3),(1,258,4),(2,264,5)]),(9,[(2,264,5)]),(1,[(0,4,5),(2,6,41)]),(2,[(0,4,5),(2,6,41)]),(0,[(1,0,1),(0,4,5),(2,6,41)]),(9,[(0,4,5)]),(1,[(3,4,5),(2,16,5)]),(2,[(1,1,4),(3,4,5),(2,16,5)]),(8,[(3,4,5),(2,16,5)]),(1,[(1,0,2),(2,84,4),(1,274,5)]),(2,[(2,84,4),(1,274,5)]),(0,[(2,84,4),(1,274,5)]),(8,[(1,274,5)]),(6,[(1,0,2),(1,274,5)]),(11,[(1,0,2),(2,84,4)]),(0,[(2,19,3),(1,19,4)]),(1,[(1,19,4)]),(1,[(2,19,3),(1,19,4)]),(8,[(2,19,3),(1,19,4)]),(2,[(1,1,2),(2,19,3)]),(1,[(1,4,5),(3,2,20)]),(2,[(1,4,5),(3,2,20),(1,53,1)]),(8,[(1,4,5),(3,2,20)]),(0,[(1,4,5),(1,53,1)]),(2,[(1,1,4),(3,4,5),(1,220,1)]),(0,[(1,1,4),(3,4,5),(1,220,1)]),(1,[(3,4,5)]),(1,[(1,3,4),(0,6,157)]),(2,[(1,3,4),(0,6,157)]),(0,[(1,0,1),(1,3,4),(0,6,157)]),(12,[(1,0,1),(0,6,157)]),(2,[(3,2,4),(1,3,5),(3,2,7)]),(1,[(3,2,4),(1,3,5),(3,2,7)]),(2,[(1,2,4),(1,4,5),(3,2,20)]),(1,[(1,2,4),(1,4,5),(3,2,20)]),(2,[(1,1,2),(0,3,4),(1,1,76)]),(4,[(1,1,2),(1,1,76)]),(1,[(1,97,4),(1,4,5)]),(0,[(3,1,3),(1,97,4),(1,4,5)]),(2,[(3,1,3),(1,97,4),(1,4,5)]),(8,[(2,3,5),(3,3,5)]),(9,[(2,3,5),(3,3,5)]),(1,[(3,2,3),(1,57,4),(1,4,5)]),(2,[(3,2,3),(1,57,4),(1,4,5)]),(0,[(1,57,4),(1,4,5)]),(4,[(1,57,4),(1,4,5)]),(1,[(1,4,5),(3,25,20)]),(2,[(3,1,4),(1,4,5),(3,25,20)]),(8,[(1,4,5),(3,25,20)]),(2,[(0,3,5),(3,13,4)]),(1,[(0,3,5),(3,13,4)]),(3,[(0,3,5),(3,13,4)]),(9,[(0,3,5),(3,13,4)]),(1,[(1,2,4),(0,3,38),(1,3,38)]),(9,[(0,3,38),(1,3,38)]),(2,[(1,2,4),(0,3,38),(1,3,38)]),(0,[(0,3,38),(1,3,38)]),(2,[(1,2,4),(3,1,38),(1,2,5)]),(8,[(1,2,4),(1,2,5)]),(6,[(3,1,38),(1,2,5)]),(2,[(1,4,5),(3,4,242)]),(1,[(1,0,5),(1,4,5),(3,4,242)]),(0,[(1,0,5),(1,4,5),(3,4,242)]),(11,[(3,4,242)]),(2,[(1,1,2),(1,1,4),(2,19,4)]),(8,[(2,19,4)]),(0,[(1,1,4),(2,19,4)]),(1,[(0,4,5),(1,3,41)]),(2,[(0,4,5),(1,3,41)]),(3,[(0,4,5),(1,3,41)]),(9,[(0,4,5),(1,3,41)]),(4,[(1,0,1),(1,4,5)]),(1,[(2,3,4),(1,4,5)]),(0,[(1,1,4),(0,3,5),(1,13,4)]),(2,[(1,1,4),(0,3,5),(1,13,4)]),(1,[(3,4,5),(3,220,6)]),(2,[(3,4,5),(3,220,6)]),(0,[(1,0,1),(3,4,5),(3,220,6)]),(9,[(3,4,5)]),(2,[(1,2,4),(1,1,38),(3,4,82)]),(8,[(1,2,4),(3,4,82)]),(0,[(1,1,38),(3,4,82)]),(1,[(1,2,4),(3,4,82)]),(2,[(1,2,4),(1,38,5)]),(3,[(1,2,4),(1,38,5)]),(4,[(1,2,4),(1,38,5)]),(0,[(1,38,5)]),(0,[(3,1,3),(1,38,5)]),(6,[(1,38,5)]),(12,[(1,2,4),(1,38,5)]),(2,[(3,1,3)]),(3,[(3,1,3)]),(4,[(1,0,1),(2,6,5)]),(1,[(2,6,5),(0,33,3)]),(2,[(2,6,5)]),(0,[(1,0,1),(2,6,5)]),(9,[(0,33,3)]),(9,[(0,19,4),(1,100,5)]),(8,[(0,19,4),(1,100,5)]),(2,[(1,1,2),(0,19,4),(1,100,5)]),(0,[(0,19,4),(1,100,5)]),(9,[(2,19,3),(1,234,4)]),(8,[(2,19,3),(1,234,4)]),(2,[(1,1,2),(2,19,3),(1,234,4)]),(0,[(2,19,3),(1,234,4)]),(1,[(2,19,3),(1,234,4)]),(2,[(1,1,2),(3,19,4),(1,168,1)]),(8,[(3,19,4)]),(0,[(3,19,4),(1,168,1)]),(1,[(3,19,4)]),(1,[(3,2,5),(1,4,5),(3,163,20)]),(9,[(1,4,5),(3,163,20)]),(2,[(3,2,5),(1,4,5),(3,163,20)]),(0,[(1,4,5),(3,163,20)]),(1,[(3,3,5),(3,137,6)]),(2,[(3,3,5),(3,137,6)]),(0,[(1,0,1),(3,3,5),(3,137,6)]),(2,[(3,1,4),(3,2,3),(1,57,25)]),(8,[(3,2,3),(1,57,25)]),(1,[(3,2,3),(1,57,25)]),(0,[(3,1,4),(1,57,25)]),(4,[(3,1,4),(1,57,25)]),(10,[(3,1,4),(1,57,25)]),(2,[(1,3,5),(3,4,7)]),(3,[(1,3,5),(3,4,7)]),(1,[(1,0,2)]),(4,[(1,0,2)]),(2,[(3,2,3),(1,57,4)]),(3,[(3,2,3),(1,57,4)]),(4,[(1,1,5),(1,57,4)]),(1,[(3,2,3),(1,57,4)]),(1,[(1,4,5),(0,6,20)]),(2,[(1,4,5),(0,6,20)]),(0,[(1,0,1),(1,4,5),(0,6,20)]),(1,[(0,3,4),(1,3,4)]),(2,[(0,3,4),(1,3,4)]),(3,[(0,3,4),(1,3,4)]),(9,[(0,3,4),(1,3,4)]),(5,[(0,3,4),(1,3,4)]),(17,[(1,0,1)]),(12,[(1,1,4),(3,2,16)]),(11,[(1,1,4),(3,2,16)]),(0,[(2,3,5)]),(0,[(1,1,4),(2,3,5)]),(1,[(3,2,16),(2,3,5)]),(2,[(1,1,4),(3,2,16),(2,3,5)]),(1,[(1,19,4),(0,3,82)]),(0,[(1,19,4)]),(1,[(1,19,4),(3,2,82)]),(6,[(1,1,2),(3,2,82)]),(12,[(1,0,1),(2,6,4)]),(11,[(1,0,1),(2,6,4)]),(1,[(2,6,4),(2,3,5)]),(9,[(2,3,5)]),(0,[(1,57,5),(3,4,58)]),(10,[(3,4,58)]),(1,[(1,3,4),(0,19,157)]),(0,[(1,3,4),(0,19,157)]),(2,[(1,1,2),(1,3,4),(0,19,157)]),(8,[(1,3,4),(0,19,157)]),(6,[(1,1,2),(0,19,157)]),(1,[(0,3,5),(2,6,13)]),(2,[(0,3,5),(2,6,13)]),(0,[(1,0,1),(0,3,5),(2,6,13)]),(1,[(2,6,5),(2,3,4)]),(0,[(0,19,4),(1,3,5)]),(1,[(0,19,4)]),(1,[(1,0,2),(2,84,5),(1,95,4)]),(2,[(2,84,5),(1,95,4)]),(0,[(2,84,5),(1,95,4)]),(8,[(1,95,4)]),(11,[(1,0,2),(1,95,4)]),(0,[(2,3,38),(3,3,38)]),(1,[(1,2,4),(2,3,38),(3,3,38)]),(9,[(2,3,38),(3,3,38)]),(2,[(1,2,4),(2,3,38),(3,3,38)]),(1,[(1,0,4),(2,3,5),(3,3,5)]),(0,[(1,0,4),(2,3,5),(3,3,5)]),(1,[(2,6,5)]),(1,[(2,6,5),(0,33,4)]),(2,[(2,6,5),(0,33,4)]),(1,[(2,6,5),(1,33,4)]),(0,[(1,0,1),(2,6,5),(1,33,4)]),(2,[(2,6,5),(1,33,4)]),(9,[(1,33,4)]),(11,[(1,0,1),(1,33,4)]),(2,[(3,1,4),(3,3,5),(1,137,25)]),(8,[(3,3,5),(1,137,25)]),(1,[(3,3,5),(1,137,25)]),(0,[(3,1,4),(3,3,5),(1,137,25)]),(2,[(1,1,4),(0,16,5),(3,114,16)]),(8,[(0,16,5),(3,114,16)]),(1,[(0,16,5),(3,114,16)]),(0,[(1,1,4),(0,16,5),(3,114,16)]),(1,[(2,4,5),(3,4,5)]),(2,[(2,4,5),(3,4,5)]),(3,[(2,4,5),(3,4,5)]),(9,[(2,4,5),(3,4,5)]),(3,[(1,2,4),(0,3,38)]),(1,[(0,3,4),(2,6,76)]),(2,[(0,3,4),(2,6,76)]),(0,[(1,0,1),(0,3,4),(2,6,76)]),(4,[(1,0,1),(2,6,76)]),(11,[(1,0,1),(2,6,76)]),(4,[(0,4,5),(1,1,41)]),(11,[(3,0,211)]),(1,[(0,4,5)]),(6,[(3,0,211)]),(1,[(2,3,4),(1,91,19)]),(0,[(2,3,4),(1,91,19)]),(2,[(1,1,2),(2,3,4),(1,91,19)]),(8,[(2,3,4),(1,91,19)]),(1,[(1,0,2),(0,3,4),(1,2,76)]),(12,[(1,0,2)]),(6,[(1,0,2)]),(10,[(0,3,4)]),(1,[(1,3,5),(0,19,7)]),(0,[(1,3,5),(0,19,7)]),(2,[(1,1,2),(1,3,5),(0,19,7)]),(8,[(1,3,5),(0,19,7)]),(10,[(0,19,7)]),(1,[(2,6,4),(1,31,5)]),(0,[(1,0,1),(2,6,4),(1,31,5)]),(2,[(2,6,4),(1,31,5)]),(9,[(1,31,5)]),(6,[(1,0,1),(1,31,5)]),(1,[(2,4,5),(3,133,6)]),(2,[(2,4,5),(3,133,6)]),(3,[(2,4,5)]),(1,[(1,2,4),(2,3,4),(1,91,2)]),(2,[(1,2,4),(2,3,4),(1,91,2)]),(0,[(3,1,3)]),(2,[(1,4,5),(0,3,20),(1,2,21)]),(9,[(1,4,5),(0,3,20)]),(11,[(1,2,21)]),(1,[(3,2,4),(3,117,228)]),(2,[(1,1,3),(3,2,4),(3,117,228)]),(8,[(3,2,4),(3,117,228)]),(11,[(3,2,4)]),(0,[(1,1,3),(3,117,228)]),(12,[(1,0,2),(2,84,5)]),(16,[(2,3,4)]),(1,[(1,2,3),(0,186,16)]),(0,[(1,1,4),(0,186,16)]),(2,[(1,1,4),(1,2,3),(0,186,16)]),(8,[(1,2,3),(0,186,16)]),(1,[(3,19,4),(1,168,2)]),(9,[(3,19,4)]),(2,[(1,1,2),(3,19,4),(1,168,2)]),(0,[(3,19,4)]),(1,[(3,2,5),(1,163,16)]),(0,[(1,1,4),(1,163,16)]),(2,[(1,1,4),(3,2,5),(1,163,16)]),(8,[(3,2,5),(1,163,16)]),(10,[(1,0,1)]),(1,[(0,16,5),(1,2,114)]),(2,[(1,1,4),(0,16,5),(1,2,114)]),(8,[(0,16,5),(1,2,114)]),(2,[(1,1,2),(0,3,4),(1,2,76)]),(4,[(1,1,2),(1,2,76)]),(12,[(1,1,5),(3,4,63)]),(1,[(3,2,3)]),(3,[(1,1,5),(3,4,63)]),(2,[(1,1,5),(3,4,63)]),(1,[(3,2,3),(3,4,63)]),(1,[(2,3,4),(3,91,6)]),(2,[(2,3,4),(3,91,6)]),(0,[(1,0,1),(2,3,4),(3,91,6)]),(6,[(1,0,1),(3,91,6)]),(4,[(1,0,1),(3,91,6)]),(11,[(1,0,1),(3,91,6)]),(0,[(1,0,1)]),(2,[(3,2,4),(1,117,5)]),(3,[(3,2,4),(1,117,5)]),(4,[(3,2,4),(1,117,5)]),(0,[(1,117,5)]),(0,[(3,1,3),(1,117,5)]),(5,[(3,2,4)]),(12,[(3,2,4),(1,117,5)]),(1,[(1,3,5),(3,25,7)]),(2,[(3,1,4),(1,3,5),(3,25,7)]),(8,[(1,3,5),(3,25,7)]),(0,[(3,1,4),(1,3,5),(3,25,7)]),(1,[(1,2,3),(1,305,4)]),(0,[(3,1,186),(1,305,4)]),(2,[(1,2,3),(3,1,186),(1,305,4)]),(4,[(1,305,4)]),(8,[(1,2,3),(1,305,4)]),(11,[(1,305,4)]),(1,[(3,3,4),(3,147,6)]),(2,[(3,3,4),(3,147,6)]),(3,[(3,3,4)]),(9,[(3,3,4)]),(1,[(1,0,4),(0,3,5),(1,2,13)]),(4,[(1,0,4),(1,2,13)]),(10,[(1,0,4)]),(2,[(3,3,5),(1,137,4)]),(3,[(3,3,5),(1,137,4)]),(9,[(3,3,5),(1,137,4)]),(12,[(1,137,4)]),(0,[(1,0,1),(0,4,5),(1,1,41)]),(1,[(1,3,5),(0,6,7)]),(1,[(3,19,3),(1,181,2)]),(9,[(3,19,3)]),(2,[(1,1,2),(3,19,3),(1,181,2)]),(0,[(3,19,3)]),(2,[(1,1,2),(0,19,4),(3,100,19)]),(8,[(0,19,4),(3,100,19)]),(0,[(0,19,4),(3,100,19)]),(1,[(0,19,4),(3,100,19)]),(2,[(1,1,2),(1,19,5),(3,5,66)]),(8,[(1,19,5),(3,5,66)]),(1,[(1,19,5),(3,5,66)]),(1,[(0,19,3),(1,19,3)]),(9,[(0,19,3),(1,19,3)]),(8,[(0,19,3),(1,19,3)]),(2,[(1,1,2),(0,19,3),(1,19,3)]),(1,[(1,4,5),(2,3,20)]),(3,[(1,4,5),(2,3,20)]),(1,[(2,6,5),(0,3,4)]),(0,[(1,0,1),(0,3,5),(1,1,13)]),(1,[(2,3,16),(1,226,4)]),(0,[(1,1,4),(2,3,16),(1,226,4)]),(8,[(2,3,16),(1,226,4)]),(2,[(1,1,4),(2,3,16),(1,226,4)]),(1,[(0,4,5),(1,2,41)]),(2,[(0,4,5),(1,2,41)]),(3,[(0,4,5),(1,2,41)]),(1,[(1,19,5),(2,3,4)]),(0,[(1,19,5)]),(0,[(1,19,5),(2,3,4)]),(4,[(1,1,2),(1,19,5)]),(12,[(1,1,2),(1,19,5)]),(2,[(0,4,5),(2,3,41)]),(1,[(0,4,5),(2,3,41)]),(3,[(0,4,5),(2,3,41)]),(9,[(0,4,5),(2,3,41)]),(2,[(1,1,5),(1,4,63),(3,5,50)]),(8,[(1,4,63),(3,5,50)]),(1,[(1,4,63),(3,5,50)]),(6,[(1,1,5),(3,5,50)]),(1,[(1,2,5),(1,19,4)]),(2,[(1,1,2),(1,2,5),(1,19,4)]),(8,[(1,2,5),(1,19,4)]),(2,[(2,4,5),(1,133,5)]),(3,[(2,4,5),(1,133,5)]),(9,[(2,4,5),(1,133,5)]),(16,[(1,4,5)]),(10,[(0,3,20)]),(1,[(2,228,4),(1,229,2)]),(0,[(1,1,3),(2,228,4)]),(2,[(1,1,3),(2,228,4),(1,229,2)]),(8,[(2,228,4),(1,229,2)]),(12,[(1,0,2),(2,84,4)]),(0,[(2,84,4),(2,3,5)]),(8,[(2,3,5)]),(10,[(2,84,4)]),(2,[(1,3,5),(3,109,7)]),(1,[(3,0,4),(1,3,5),(3,109,7)]),(0,[(3,0,4),(1,3,5),(3,109,7)]),(2,[(3,2,3),(1,57,4),(2,61,5)]),(9,[(1,57,4),(2,61,5)]),(1,[(3,2,3),(1,57,4),(2,61,5)]),(4,[(1,57,4),(2,61,5)]),(12,[(1,1,2),(2,19,4)]),(11,[(1,1,2),(2,19,4)]),(0,[(2,19,4),(2,3,5)]),(2,[(1,1,4),(3,3,5),(1,137,1)]),(0,[(1,1,4),(3,3,5),(1,137,1)]),(6,[(3,3,5),(1,137,1)]),(1,[(2,19,4),(1,89,5)]),(0,[(2,19,4),(1,89,5)]),(2,[(1,1,2),(2,19,4),(1,89,5)]),(8,[(2,19,4),(1,89,5)]),(6,[(1,1,2),(1,89,5)]),(2,[(1,1,2),(1,3,4),(3,19,157)]),(8,[(1,3,4),(3,19,157)]),(6,[(1,1,2),(3,19,157)]),(8,[(2,3,4),(1,3,5)]),(5,[(1,0,2)]),(2,[(2,3,4),(1,3,5)]),(12,[(1,1,2),(0,19,4)]),(11,[(1,1,2),(0,19,4)]),(0,[(0,19,4),(2,3,5)]),(0,[(2,84,5),(0,3,4)]),(25,[]),(0,[(1,1,4),(1,1,5),(1,4,5)]),(2,[(1,1,4),(1,1,5),(1,4,5)]),(2,[(1,1,2),(1,19,4),(3,1,82)]),(6,[(1,1,2),(3,1,82)]),(1,[(1,25,2)]),(1,[(1,25,2),(2,3,5)]),(0,[(3,1,4)]),(0,[(3,1,4),(2,3,5)]),(12,[(3,1,4),(1,25,2)]),(11,[(3,1,4),(1,25,2)]),(1,[(1,19,4),(3,3,82)]),(0,[(1,19,4),(3,3,82)]),(1,[(1,3,5),(1,73,4)]),(0,[(1,3,5),(3,1,7),(1,73,4)]),(8,[(1,3,5),(1,73,4)]),(2,[(1,3,5),(3,1,7),(1,73,4)]),(2,[(1,1,4),(1,3,4),(3,1,157)]),(8,[(1,3,4)]),(0,[(1,1,4),(1,3,4),(3,1,157)]),(1,[(1,3,4)]),(1,[(1,19,4),(1,3,5)]),(1,[(1,3,4),(3,2,157)]),(2,[(1,3,4),(3,2,157),(1,176,1)]),(8,[(1,3,4),(3,2,157)]),(1,[(1,19,4),(2,3,5)]),(0,[(1,19,4),(2,3,5)]),(5,[(1,1,2),(1,19,4)]),(1,[(2,3,4),(1,3,5)]),(2,[(1,1,2),(1,19,4),(3,4,82)]),(2,[(1,1,2),(1,19,4),(2,82,5)]),(8,[(1,19,4),(2,82,5)]),(1,[(1,19,4),(2,82,5)]),(0,[(1,19,4),(2,82,5)]),(1,[(1,97,2),(1,2,5)]),(2,[(3,1,3),(1,97,2),(1,2,5)]),(8,[(1,97,2),(1,2,5)]),(2,[(3,1,3),(1,97,5)]),(3,[(3,1,3),(1,97,5)]),(4,[(1,97,5),(1,2,4)]),(1,[(1,97,5)]),(1,[(1,97,5),(1,2,4)]),(0,[(3,1,3),(1,97,5)]),(6,[(3,1,3),(1,97,5)]),(1,[(1,2,5),(0,3,4),(1,76,5)]),(2,[(1,2,5),(0,3,4),(1,76,5)]),(1,[(2,3,63),(1,318,5)]),(0,[(1,1,5),(2,3,63),(1,318,5)]),(8,[(2,3,63),(1,318,5)]),(2,[(1,1,5),(2,3,63),(1,318,5)]),(4,[(1,1,5),(1,318,5)]),(1,[(2,19,4),(1,89,4)]),(0,[(2,19,4),(1,89,4)]),(2,[(1,1,2),(2,19,4),(1,89,4)]),(8,[(2,19,4),(1,89,4)]),(2,[(1,1,2),(2,19,4),(2,89,5)]),(8,[(2,19,4),(2,89,5)]),(0,[(2,19,4),(2,89,5)]),(1,[(2,19,4),(2,89,5)]),(0,[(1,0,4),(0,3,5),(1,1,13)]),(4,[(1,0,4),(1,1,13)]),(1,[(2,19,4),(2,3,5)]),(2,[(1,4,5),(3,1,20),(1,45,2)]),(8,[(1,4,5),(1,45,2)]),(1,[(1,4,5),(1,45,2)]),(2,[(1,1,2),(1,19,5),(3,2,66)]),(8,[(1,19,5),(3,2,66)]),(1,[(1,19,5),(3,2,66)]),(2,[(1,1,2),(1,19,5),(0,3,66)]),(8,[(1,19,5),(0,3,66)]),(1,[(1,19,5),(0,3,66)]),(2,[(1,1,4),(0,3,5),(3,13,16)]),(8,[(0,3,5),(3,13,16)]),(1,[(0,3,5),(3,13,16)]),(6,[(0,3,5),(3,13,16)]),(0,[(1,1,4),(0,3,5),(3,13,16)]),(1,[(1,97,2),(1,308,5)]),(0,[(3,1,3),(1,308,5)]),(2,[(3,1,3),(1,97,2),(1,308,5)]),(4,[(1,97,2),(1,308,5)]),(8,[(1,97,2),(1,308,5)]),(2,[(2,3,4),(1,91,2),(2,152,5)]),(9,[(2,3,4),(2,152,5)]),(1,[(2,3,4),(1,91,2),(2,152,5)]),(2,[(1,1,2),(1,19,5),(3,4,66)]),(8,[(1,19,5),(3,4,66)]),(1,[(1,19,5),(3,4,66)]),(0,[(1,19,5),(3,4,66)]),(9,[(0,19,3),(1,78,5)]),(8,[(0,19,3),(1,78,5)]),(2,[(1,1,2),(0,19,3),(1,78,5)]),(0,[(0,19,3),(1,78,5)]),(1,[(0,19,3),(1,78,5)]),(4,[(1,1,2),(1,78,5)]),(1,[(2,3,4),(1,91,5)]),(2,[(1,1,4),(1,1,5)]),(3,[(1,1,4),(1,1,5)]),(2,[(1,1,4),(1,1,5),(0,3,63)]),(0,[(1,1,4),(1,1,5)]),(12,[(1,1,4),(1,1,5)]),(2,[(1,2,4),(1,38,5),(0,3,39)]),(9,[(1,38,5),(0,3,39)]),(1,[(1,2,4),(1,38,5),(0,3,39)]),(1,[(2,19,5),(1,104,4)]),(0,[(2,19,5),(1,104,4)]),(2,[(1,1,2),(2,19,5),(1,104,4)]),(8,[(2,19,5),(1,104,4)]),(11,[(1,1,2),(1,104,4)]),(2,[(1,2,4),(3,3,38),(1,178,1)]),(8,[(1,2,4),(3,3,38)]),(6,[(3,3,38),(1,178,1)]),(1,[(0,3,4),(1,19,76)]),(9,[(0,3,4),(1,19,76)]),(8,[(0,3,4),(1,19,76)]),(2,[(1,1,2),(0,3,4),(1,19,76)]),(4,[(1,1,2),(1,19,76)]),(1,[(2,16,5),(3,16,5)]),(2,[(1,1,4),(2,16,5),(3,16,5)]),(8,[(2,16,5),(3,16,5)]),(2,[(1,1,4),(0,3,16)]),(3,[(1,1,4),(0,3,16)]),(1,[(1,16,5)]),(1,[(0,3,16),(1,16,5)]),(2,[(0,3,4),(3,76,242)]),(1,[(1,0,5),(0,3,4),(3,76,242)]),(0,[(1,0,5),(0,3,4),(3,76,242)]),(11,[(3,76,242)]),(2,[(1,1,4),(1,2,4),(3,2,16)]),(8,[(1,2,4),(3,2,16)]),(1,[(1,2,4),(3,2,16)]),(2,[(1,1,2),(0,3,4),(2,19,76)]),(8,[(0,3,4),(2,19,76)]),(0,[(0,3,4),(2,19,76)]),(4,[(1,1,2),(2,19,76)]),(10,[(0,3,4),(2,19,76)]),(1,[(1,2,63),(3,4,63)]),(5,[(1,2,63),(3,4,63)]),(0,[(1,1,5)]),(4,[(1,1,5),(1,2,63)]),(4,[(1,1,5),(3,4,63)]),(8,[(0,3,4),(1,3,4)]),(2,[(1,1,2),(0,3,4),(1,3,4)]),(0,[(0,3,4),(1,3,4)]),(17,[(1,1,2)]),(1,[(1,97,2),(1,308,4)]),(0,[(3,1,3),(1,308,4)]),(2,[(3,1,3),(1,97,2),(1,308,4)]),(4,[(1,97,2),(1,308,4)]),(8,[(1,97,2),(1,308,4)]),(9,[(1,19,5)]),(0,[(1,1,4),(1,1,5),(0,16,5)]),(8,[(0,16,5)]),(2,[(1,1,4),(1,1,5),(0,16,5)]),(6,[(1,1,5),(0,16,5)]),(1,[(0,16,5)]),(0,[(1,1,4),(1,1,5),(0,4,63)]),(8,[(0,4,63)]),(2,[(1,1,4),(1,1,5),(0,4,63)]),(11,[(1,1,4),(0,4,63)]),(1,[(1,3,5),(1,73,2)]),(2,[(1,3,5),(3,1,7),(1,73,2)]),(8,[(1,3,5),(1,73,2)]),(1,[(2,3,4),(3,91,19)]),(0,[(2,3,4),(3,91,19)]),(2,[(1,1,2),(2,3,4),(3,91,19)]),(8,[(2,3,4),(3,91,19)]),(1,[(1,2,4),(1,2,5),(1,4,5)]),(2,[(1,2,4),(1,2,5),(1,4,5)]),(1,[(3,2,228),(1,236,4)]),(0,[(1,1,3),(1,236,4)]),(2,[(1,1,3),(3,2,228),(1,236,4)]),(4,[(1,236,4)]),(8,[(3,2,228),(1,236,4)]),(2,[(2,3,4),(1,91,1)]),(3,[(2,3,4),(1,91,1)]),(1,[(1,2,4),(2,3,4)]),(6,[(1,91,1)]),(2,[(3,2,3),(1,57,1)]),(3,[(3,2,3),(1,57,1)]),(0,[(1,57,1),(1,4,5)]),(6,[(3,2,3),(1,57,1)]),(2,[(1,1,2),(3,3,4),(1,147,1)]),(8,[(3,3,4)]),(1,[(3,3,4)]),(1,[(1,2,4),(1,83,5)]),(0,[(3,1,38),(1,83,5)]),(2,[(1,2,4),(3,1,38),(1,83,5)]),(8,[(1,2,4),(1,83,5)]),(6,[(3,1,38),(1,83,5)]),(0,[(1,1,4),(3,3,5),(1,137,4)]),(2,[(1,1,4),(3,3,5),(1,137,4)]),(2,[(3,1,3),(1,97,2)]),(3,[(3,1,3),(1,97,2)]),(1,[(1,97,2),(1,4,5)]),(0,[(3,1,3),(1,4,5)]),(1,[(3,3,4),(1,147,19)]),(0,[(3,3,4),(1,147,19)]),(2,[(1,1,2),(3,3,4),(1,147,19)]),(8,[(3,3,4),(1,147,19)]),(12,[(1,2,4),(2,38,5)]),(0,[(3,1,3),(2,38,5)]),(2,[(1,2,4),(2,38,5)]),(2,[(1,1,2),(1,3,5),(3,1,7)]),(2,[(1,1,2),(1,3,5),(3,19,7)]),(8,[(1,3,5),(3,19,7)]),(2,[(1,1,2),(1,2,5),(2,19,4)]),(8,[(1,2,5),(2,19,4)]),(0,[(2,19,4)]),(1,[(1,2,5),(2,19,4)]),(2,[(1,1,2),(2,4,5),(1,133,1)]),(2,[(3,1,4),(0,3,5),(1,1,13)]),(1,[(2,4,5),(1,133,19)]),(0,[(2,4,5),(1,133,19)]),(2,[(1,1,2),(2,4,5),(1,133,19)]),(8,[(2,4,5),(1,133,19)]),(2,[(1,1,5),(2,3,4),(1,91,1)]),(0,[(1,1,5),(2,3,4),(1,91,1)]),(1,[(2,4,5),(3,133,19)]),(0,[(2,4,5),(3,133,19)]),(2,[(1,1,2),(2,4,5),(3,133,19)]),(8,[(2,4,5),(3,133,19)]),(10,[(3,133,19)]),(5,[(1,2,4)]),(0,[(2,84,4),(1,3,5)]),(4,[(1,0,2),(2,84,4)]),(2,[(3,1,3),(3,2,4),(1,117,97)]),(8,[(3,2,4),(1,117,97)]),(1,[(3,2,4),(1,117,97)]),(0,[(3,1,3),(1,117,97)]),(4,[(3,2,4),(1,117,97)]),(10,[(3,1,3),(1,117,97)]),(2,[(1,1,3),(3,2,228),(2,236,4)]),(8,[(3,2,228),(2,236,4)]),(1,[(3,2,228),(2,236,4)]),(4,[(2,236,4)]),(1,[(1,2,4),(0,228,38)]),(0,[(1,1,3),(0,228,38)]),(2,[(1,1,3),(1,2,4),(0,228,38)]),(8,[(1,2,4),(0,228,38)]),(10,[(1,1,3),(0,228,38)]),(2,[(3,1,3),(1,97,2),(2,308,4)]),(8,[(1,97,2),(2,308,4)]),(1,[(1,97,2),(2,308,4)]),(0,[(3,1,3),(2,308,4)]),(12,[(2,308,4)]),(2,[(3,1,3),(1,97,4),(2,98,5)]),(8,[(1,97,4),(2,98,5)]),(1,[(1,97,4),(2,98,5)]),(0,[(3,1,3),(1,97,4),(2,98,5)]),(2,[(3,1,3),(1,97,4),(3,2,98)]),(8,[(1,97,4),(3,2,98)]),(1,[(1,97,4),(3,2,98)]),(2,[(1,1,4),(1,1,5),(3,2,63)]),(8,[(3,2,63)]),(11,[(1,1,4),(3,2,63)]),(1,[(1,97,4),(1,3,5)]),(0,[(3,1,3),(1,97,4),(1,3,5)]),(8,[(1,97,4),(1,3,5)]),(2,[(3,1,3),(1,97,4),(1,3,5)]),(4,[(1,97,4)]),(2,[(1,1,4),(1,2,16),(3,4,82)]),(8,[(1,2,16),(3,4,82)]),(0,[(1,1,4),(3,4,82)]),(1,[(1,2,16),(3,4,82)]),(2,[(1,258,4),(2,4,5)]),(1,[(3,0,3),(1,258,4),(2,4,5)]),(6,[(3,0,3)]),(1,[(1,97,5),(3,2,4)]),(4,[(1,97,5)]),(2,[(3,1,3),(1,97,2),(2,308,5)]),(8,[(1,97,2),(2,308,5)]),(1,[(1,97,2),(2,308,5)]),(0,[(3,1,3),(2,308,5)]),(11,[(1,97,2)]),(2,[(1,1,2),(1,3,4),(3,2,157)]),(0,[(1,3,4)]),(6,[(1,1,2),(3,2,157)]),(2,[(3,1,3),(1,97,5),(3,4,232)]),(8,[(1,97,5),(3,4,232)]),(1,[(1,97,5),(3,4,232)]),(0,[(3,1,3),(1,97,5),(3,4,232)]),(11,[(3,4,232)]),(1,[(1,3,5),(3,2,7),(1,118,4)]),(2,[(1,3,5),(3,2,7),(1,118,4)]),(0,[(1,3,5),(1,118,4)]),(4,[(1,118,4)]),(1,[(3,2,4),(1,3,5),(3,117,7)]),(9,[(1,3,5),(3,117,7)]),(2,[(3,2,4),(1,3,5),(3,117,7)]),(0,[(1,3,5),(3,117,7)]),(2,[(3,1,3),(1,3,5)]),(3,[(3,1,3),(1,3,5)]),(0,[(3,1,3),(1,3,5)]),(6,[(3,1,3),(1,3,5)]),(1,[(1,2,5),(0,3,4),(1,76,23)]),(9,[(0,3,4),(1,76,23)]),(2,[(1,2,5),(0,3,4),(1,76,23)]),(5,[(0,3,4),(1,76,23)]),(4,[(1,2,5),(1,76,23)]),(1,[(2,3,4),(3,91,63)]),(0,[(1,1,5),(2,3,4),(3,91,63)]),(8,[(2,3,4),(3,91,63)]),(2,[(1,1,5),(2,3,4),(3,91,63)]),(1,[(1,25,2),(1,210,5)]),(0,[(3,1,4),(1,210,5)]),(2,[(3,1,4),(1,25,2),(1,210,5)]),(8,[(1,25,2),(1,210,5)]),(6,[(1,210,5)]),(2,[(1,1,4),(3,2,5),(1,4,5)]),(1,[(3,2,5),(1,4,5)]),(8,[(3,2,5),(1,4,5)]),(4,[(3,2,5),(1,4,5)]),(2,[(1,1,2),(1,19,3),(3,1,79)]),(8,[(1,19,3)]),(0,[(1,19,3),(3,1,79)]),(1,[(1,19,3)]),(12,[(3,2,4)]),(11,[(3,0,172)]),(12,[(1,2,5),(1,4,5)]),(2,[(1,2,4),(1,38,5),(3,5,39)]),(9,[(1,38,5),(3,5,39)]),(1,[(1,2,4),(1,38,5),(3,5,39)]),(1,[(1,4,5),(3,97,20)]),(2,[(3,1,3),(1,4,5),(3,97,20)]),(8,[(1,4,5),(3,97,20)]),(0,[(3,1,3),(1,4,5),(3,97,20)]),(0,[(1,1,4),(2,3,5),(3,3,5)]),(2,[(1,1,4),(2,3,5),(3,3,5)]),(12,[(1,4,5),(1,2,20)]),(3,[(1,4,5),(3,2,20)]),(2,[(1,4,5),(3,2,20)]),(2,[(3,1,3),(2,4,5),(1,133,97)]),(8,[(2,4,5),(1,133,97)]),(1,[(2,4,5),(1,133,97)]),(0,[(3,1,3),(2,4,5),(1,133,97)]),(1,[(2,6,4),(1,3,5)]),(4,[(1,0,1),(2,6,4)]),(1,[(2,6,5),(1,4,5)]),(2,[(2,4,5),(1,133,2)]),(3,[(2,4,5),(1,133,2)]),(4,[(2,4,5),(1,133,2)]),(0,[(2,4,5)]),(0,[(3,1,3),(2,4,5)]),(12,[(2,4,5),(1,133,2)]),(2,[(1,2,5),(1,4,5),(3,2,20)]),(1,[(1,2,5),(1,4,5),(3,2,20)]),(1,[(3,3,4),(3,147,19)]),(0,[(3,3,4),(3,147,19)]),(2,[(1,1,2),(3,3,4),(3,147,19)]),(8,[(3,3,4),(3,147,19)]),(1,[(2,6,5),(2,33,4)]),(9,[(2,33,4)]),(4,[(1,1,4),(1,1,5)]),(6,[(0,3,16)]),(1,[(0,3,16)]),(2,[(2,3,4),(1,91,1),(1,3,5)]),(2,[(1,1,4),(0,3,5),(1,2,13)]),(4,[(1,1,4),(1,2,13)]),(2,[(1,1,4),(1,1,5),(2,4,5)]),(4,[(1,1,5),(2,4,5)]),(2,[(1,1,4),(1,1,5),(2,16,5)]),(8,[(2,16,5)]),(0,[(1,1,4),(1,1,5),(2,16,5)]),(0,[(3,1,3),(1,4,5),(3,1,20)]),(2,[(3,1,3),(1,4,5),(3,1,20)]),(2,[(1,1,4),(1,2,3),(2,186,16)]),(8,[(1,2,3),(2,186,16)]),(0,[(1,1,4),(2,186,16)]),(1,[(3,2,3),(3,57,16)]),(0,[(1,1,4),(3,57,16)]),(2,[(1,1,4),(3,2,3),(3,57,16)]),(8,[(3,2,3),(3,57,16)]),(1,[(3,2,3),(1,16,5)]),(4,[(1,1,4),(1,16,5)]),(6,[(1,16,5)]),(1,[(3,2,16),(1,81,5)]),(0,[(1,1,4),(1,81,5)]),(2,[(1,1,4),(3,2,16),(1,81,5)]),(8,[(3,2,16),(1,81,5)]),(2,[(1,1,4),(3,2,16),(2,81,5)]),(8,[(3,2,16),(2,81,5)]),(1,[(3,2,16),(2,81,5)]),(1,[(3,2,16),(1,3,5)]),(4,[(1,1,4),(3,2,16)]),(2,[(1,1,4),(3,2,16),(1,3,5)]),(3,[(1,1,4),(3,2,16)]),(1,[(1,0,2),(0,3,4),(1,3,4)]),(17,[(1,0,2)]),(0,[(1,1,4),(1,163,4)]),(2,[(1,1,4),(3,2,5),(1,163,4)]),(1,[(3,2,5),(3,163,16)]),(2,[(1,1,4),(3,2,5),(3,163,16)]),(8,[(3,2,5),(3,163,16)]),(0,[(1,1,4),(3,163,16)]),(2,[(3,2,3),(2,4,5),(1,133,57)]),(9,[(2,4,5),(1,133,57)]),(1,[(3,2,3),(2,4,5),(1,133,57)]),(4,[(2,4,5),(1,133,57)]),(11,[(1,133,57)]),(2,[(1,1,4),(2,3,4),(1,91,1)]),(0,[(1,1,4),(2,3,4),(1,91,1)]),(11,[(1,2,20)]),(6,[(3,0,20)]),(1,[(1,4,5),(1,0,20)]),(0,[(1,4,5),(1,0,20)]),(6,[(1,0,20)]),(0,[(0,4,5),(1,0,41)]),(8,[]),(9,[]),(1,[(3,3,5)]),(2,[(3,3,5),(1,137,1)]),(0,[(3,3,5),(1,137,1)]),(2,[(1,3,5),(3,2,7)]),(2,[(3,3,4),(1,147,2)]),(0,[(3,3,4)]),(1,[(2,4,5),(1,133,2)]),(11,[(1,133,2)]),(2,[(2,3,4),(1,4,5)]),(2,[(1,3,4),(3,2,157)]),(3,[(1,2,5)]),(12,[(1,2,5)]),(2,[(3,2,4),(2,3,5)]),(2,[(1,2,4),(1,4,5)]),(2,[(1,2,4),(2,3,5)]),(1,[(1,2,4),(2,3,5)]),(0,[(3,3,38)]),(6,[(3,3,38)]),(2,[(1,2,4),(2,3,38)]),(9,[(2,3,38)]),(1,[(1,2,4),(2,3,38)]),(0,[(2,3,38)]),(1,[(1,2,4),(1,3,38)]),(9,[(1,3,38)]),(2,[(1,2,4),(1,3,38)]),(0,[(1,3,38)]),(4,[(1,76,5)]),(2,[(1,2,4),(1,3,4)]),(2,[(3,2,3),(1,4,5)]),(9,[(1,57,4)]),(0,[(1,57,4)]),(4,[(1,57,4)]),(2,[(1,2,3),(2,186,4)]),(9,[(2,186,4)]),(0,[(2,186,4)]),(2,[(1,2,3),(2,3,4)]),(1,[(1,2,3),(2,3,4)]),(6,[(1,2,3)]),(2,[(1,2,3),(3,1,186)]),(8,[(1,2,3)]),(0,[(3,1,186)]),(1,[(1,362,4)]),(0,[(3,1,5),(1,362,4)]),(8,[(1,362,4)]),(2,[(3,1,5),(1,362,4)]),(6,[(3,1,5)]),(8,[(1,4,63)]),(1,[(0,4,63)]),(0,[(1,1,5),(0,4,63)]),(2,[(1,1,5),(0,4,63)]),(11,[(0,4,63)]),(0,[(1,1,5),(1,4,5)]),(2,[(1,1,5),(1,4,5)]),(8,[(0,3,63)]),(4,[(3,13,4)]),(2,[(1,1,5),(2,4,5)]),(2,[(1,1,5),(2,3,4)]),(2,[(1,1,5),(0,3,4)]),(1,[(3,2,63)]),(4,[(1,91,5)]),(8,[(1,2,63)]),(2,[(2,4,5),(1,133,1)]),(2,[(1,1,5),(3,2,4)]),(2,[(1,1,5),(3,2,3)]),(2,[(3,2,3),(1,3,4)]),(1,[(3,2,3),(1,3,4)]),(9,[(1,19,4)]),(2,[(1,1,2),(3,19,3)]),(9,[(2,19,3)]),(0,[(2,19,3)]),(1,[(2,19,3)]),(1,[(1,0,5),(1,4,5)]),(0,[(1,0,5),(1,4,5)]),(2,[(1,1,4),(2,3,16)]),(8,[(2,3,16)]),(1,[(2,3,16)]),(2,[(1,1,2),(1,3,5)]),(2,[(3,3,4),(1,147,1)]),(2,[(1,1,5),(2,3,63)]),(8,[(2,3,63)]),(0,[(1,1,5),(2,3,63)]),(1,[(1,0,5)]),(1,[(1,0,5),(2,3,4)]),(0,[(1,0,5)]),(0,[(1,0,5),(2,3,4)]),(4,[(1,0,5)]),(12,[(1,0,5)]),(2,[(1,1,5),(1,2,4)]),(3,[(3,3,5)]),(2,[(3,3,5)]),(9,[(0,19,4)]),(2,[(1,1,2),(0,19,4)]),(0,[(0,19,4)]),(10,[(0,19,4)]),(0,[(2,38,5)]),(0,[(0,3,38)]),(2,[(1,2,4),(2,3,4)]),(1,[(1,0,4),(1,3,5)]),(0,[(1,0,4),(1,3,5)]),(2,[(0,3,5)]),(2,[(2,94,5)]),(1,[(1,0,4),(2,94,5)]),(0,[(1,0,4),(2,94,5)]),(9,[(1,19,3)]),(2,[(1,1,2),(1,19,3)]),(2,[(3,4,5)]),(3,[(3,4,5)]),(1,[(1,0,4)]),(1,[(1,0,4),(3,4,5)]),(0,[(1,0,4)]),(0,[(1,0,4),(3,4,5)]),(0,[(1,0,1),(2,3,5)]),(8,[(1,97,5)]),(2,[(3,1,4),(2,3,5)]),(1,[(1,0,4),(1,4,5)]),(0,[(1,0,4),(1,4,5)]),(12,[(1,0,4)]),(1,[(3,4,63)]),(1,[(3,0,5),(1,363,2)]),(2,[(1,363,2)]),(9,[(1,117,5)]),(2,[(3,1,3),(1,4,5)]),(1,[(1,0,4),(3,3,5)]),(0,[(1,0,4),(3,3,5)]),(2,[(3,2,5),(1,4,5)]),(4,[(1,2,76)]),(12,[(2,4,5)]),(2,[(2,4,5)]),(2,[(3,1,4),(0,3,5)]),(1,[(1,0,2),(1,3,5)]),(1,[(1,0,4),(1,3,4)]),(0,[(1,0,4),(1,3,4)]),(5,[(3,4,63)]),(1,[(3,0,4),(1,109,5)]),(2,[(1,109,5)]),(0,[(3,0,4),(1,109,5)]),(9,[(1,57,5)]),(0,[(1,57,5)]),(2,[(0,4,5)]),(3,[(0,4,5)]),(1,[(1,0,4),(0,3,5)]),(0,[(1,4,5),(1,1,20)]),(8,[(0,4,5)]),(1,[(3,0,5),(1,363,4)]),(2,[(1,363,4)]),(0,[(3,0,5),(1,363,4)]),(6,[(3,0,5)]),(1,[(0,19,3)]),(1,[(3,2,5),(1,163,0)]),(0,[(1,163,0)]),(1,[(1,0,2),(2,4,5)]),(8,[(1,25,5)]),(1,[(1,0,2),(0,3,4)]),(2,[(1,1,4),(1,2,5)]),(1,[(1,2,5),(0,3,4)]),(2,[(1,2,5),(0,3,4)]),(2,[(1,1,2),(2,3,5)]),(1,[(2,4,63)]),(8,[(2,4,63)]),(2,[(1,1,4),(3,2,16)]),(6,[(3,2,16)]),(1,[(1,0,4),(2,3,5)]),(0,[(1,0,4),(2,3,5)]),(2,[(1,1,3)]),(2,[(1,1,3),(3,2,4)]),(3,[(1,1,3)]),(6,[(1,1,3)]),(0,[(1,1,3)]),(1,[(2,6,4)]),(2,[(2,6,4)]),(0,[(1,0,1),(2,6,4)]),(2,[(1,1,4),(2,16,5)]),(1,[(2,16,5)]),(1,[(1,0,2),(2,3,4)]),(1,[(1,0,5),(0,3,4)]),(0,[(1,0,5),(0,3,4)]),(2,[(1,4,5),(2,3,20)]),(2,[(3,3,4)]),(1,[(1,0,2),(1,3,4)]),(1,[(1,0,2),(2,3,5)]),(2,[(1,1,4),(3,16,5)]),(1,[(3,16,5)]),(8,[(3,16,5)]),(0,[(2,84,5)]),(2,[(2,84,5)]),(1,[(1,0,2),(2,84,5)]),(1,[(1,2,16)]),(2,[(1,1,4),(1,2,16)]),(8,[(1,2,16)]),(0,[(1,1,4),(1,3,4)]),(2,[(1,1,4),(1,3,4)]),(1,[(1,0,2),(1,4,5)]),(1,[(3,0,3),(1,258,5)]),(2,[(1,258,5)]),(0,[(3,0,3),(1,258,5)]),(4,[(1,258,5)]),(2,[(2,368,4)]),(1,[(1,0,3),(2,368,4)]),(0,[(1,0,3),(2,368,4)]),(2,[(3,1,4),(1,3,5)]),(1,[(1,97,4)]),(0,[(3,1,3),(1,97,4)]),(8,[(1,97,4)]),(2,[(3,1,3),(1,97,4)]),(1,[(3,0,4)]),(1,[(3,0,4),(2,3,5)]),(0,[(3,0,4)]),(0,[(3,0,4),(2,3,5)]),(1,[(1,0,4),(2,3,4)]),(0,[(1,0,4),(2,3,4)]),(0,[(1,1,4),(0,3,5)]),(2,[(1,1,4),(0,3,5)]),(1,[(1,0,5),(2,4,5)]),(0,[(1,0,5),(2,4,5)]),(0,[(1,57,1)]),(1,[(2,19,5)]),(1,[(3,2,5)]),(2,[(3,2,5),(1,163,1)]),(0,[(1,163,1)]),(2,[(1,1,2),(0,3,4)]),(2,[(1,1,2),(1,3,4)]),(2,[(1,1,4),(2,3,4)]),(2,[(1,1,2),(2,3,4)]),(2,[(1,1,2),(1,4,5)]),(0,[(1,117,1)]),(1,[(2,19,4)]),(2,[(1,1,2),(2,4,5)]),(2,[(1,1,4),(3,3,16)]),(1,[(3,3,16)]),(8,[(3,3,16)]),(2,[(1,1,2),(3,3,4)]),(2,[(1,1,3),(3,2,228)]),(8,[(3,2,228)]),(1,[(3,2,228)]),(2,[(1,1,3),(1,2,4)]),(2,[(1,1,3),(2,228,4)]),(8,[(2,228,4)]),(1,[(2,228,4)]),(2,[(3,4,242)]),(1,[(1,0,5),(3,4,242)]),(0,[(1,0,5),(3,4,242)]),(1,[(1,97,2)]),(8,[(1,97,2)]),(2,[(3,1,3),(1,2,4)]),(1,[(1,2,3)]),(2,[(1,1,4),(1,2,3)]),(2,[(3,1,3),(3,2,4)]),(0,[(1,1,4),(0,3,16)]),(8,[(0,3,16)]),(1,[(1,0,2),(3,3,4)]),(2,[(1,2,3)]),(2,[(3,1,4),(1,2,3)]),(3,[(1,2,3)]),(2,[(1,1,4),(3,2,3)]),(5,[(3,2,3)]),(0,[(0,4,5),(1,1,41)]),(0,[(0,3,5),(1,1,13)]),(2,[(1,1,4),(1,2,4)]),(0,[(0,3,5),(1,0,13)]),(4,[(1,0,13)]),(1,[(3,0,3),(1,258,4)]),(2,[(1,258,4)]),(0,[(3,0,3),(1,258,4)]),(4,[(1,258,4)]),(1,[(1,3,16)]),(0,[(1,1,4),(1,3,16)]),(8,[(1,3,16)]),(2,[(1,1,4),(1,3,16)]),(2,[(1,1,4),(3,2,5)]),(3,[(3,2,5)]),(2,[(1,1,4),(1,3,5)]),(2,[(1,1,4),(2,3,5)]),(2,[(1,1,4),(3,4,5)]),(2,[(1,1,4),(3,3,5)]),(2,[(1,2,4),(1,3,5)]),(2,[(1,1,4),(2,4,5)]),(0,[(1,1,4),(2,4,5)]),(2,[(3,2,4),(1,3,5)]),(2,[(3,1,4),(1,2,5)]),(0,[(1,1,4),(0,16,5)]),(2,[(1,1,4),(0,16,5)]),(2,[(3,4,5),(1,220,1)]),(0,[(3,4,5),(1,220,1)]),(0,[(2,84,4)]),(2,[(2,84,4)]),(1,[(1,0,2),(2,84,4)]),(8,[(1,25,2)]),(9,[(1,163,4)]),(2,[(3,2,5),(1,163,4)]),(0,[(1,163,4)]),(2,[(3,1,4),(3,2,3)]),(2,[(3,2,5)]),(1,[(1,0,3)]),(0,[(1,0,3)]),(2,[(3,1,5)])] : List PoolSpec)).map some)
def B_24_4 : BT (List (List Nat)) := BT.empty
lemma B_24_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 4 xs.toFinset) B_24_4 := .empty
def P_24_5 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 [0,1]
def N_24_5 : List NodeSpec := [([11,0,1,2,3,5],[0],[]),([0,1,12,3,10,5],[1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_5 : checkNodesBT W_24 g_24 F_24 P_24_5 A_24 B_24_4 5 N_24_5 = true := by decide +kernel
def B_24_5 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_5
set_option maxRecDepth 500000 in
lemma B_24_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 5 xs.toFinset) B_24_5 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_4_ok C_24_5
def P_24_6 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
def N_24_6 : List NodeSpec := [([18,0,2,3,5],[2,3,4,5,6],[]),([22,0,1,3,4,23,20],[],[]),([26,0,2,3,5],[7,8,9,10,11],[]),([0,27,3,16,23],[12,13,14,15],[]),([28,29,0,1,2,3,5],[16],[0]),([30,0,1,8,3,4,5],[17],[]),([0,1,9,2,3,10,5],[18],[0]),([0,1,8,12,3,4,5],[19,20],[0]),([32,0,1,2,3,4,35],[21],[]),([36,0,1,2,3,37,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_6 : checkNodesBT W_24 g_24 F_24 P_24_6 A_24 B_24_5 6 N_24_6 = true := by decide +kernel
def B_24_6 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_6
set_option maxRecDepth 500000 in
lemma B_24_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 6 xs.toFinset) B_24_6 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_5_ok C_24_6
def P_24_7 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 [13,14,15,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297]
def N_24_7 : List NodeSpec := [([40,0,1,2,21,3,4,5],[22,23,24,25],[]),([42,0,1,43,2,3],[14,26,27,28,29,30],[]),([42,0,44,1,2,3],[27,31,32,33,34,35,36],[]),([42,45,0,1,2,3],[14,27,28,37,38],[]),([42,46,0,1,2,3],[27,31,32,35,39,40,41],[]),([48,0,1,2,3,20],[42,43,44,45,46,47,48],[]),([24,49,0,2,3,5],[49,50,51,52,53],[0]),([0,2,3,15,17,5],[49,50,54,55,56,57,58],[0]),([51,0,1,2,3,20],[14,59,60,61,62,63,64],[]),([52,53,0,1,3,4],[14,49,65,66,67,68,69],[]),([56,0,1,2,4,5],[70,71,72,73,74,75,76],[]),([59,60,0,1,2,3,4,5],[20,24,49,77,78],[]),([53,0,1,3,61,5],[14,49,79,80,81],[]),([62,42,0,1,2,3],[14,27,28,31,32,82,83],[]),([65,0,1,2,3,5],[24,84,85,86,87,88,89],[]),([67,0,1,2,68,3,4,5],[21,23,49,90,91,92],[]),([69,0,1,2,3,4,5,63],[49,93,94,95],[]),([70,0,1,2,3,4,38,5],[49,93,96,97],[]),([0,1,2,3,4,38,63,71],[98,99,100,101],[]),([0,1,72,2,3,5,20],[14,102,103,104,105],[]),([25,0,2,3,74,5],[49,106,107,108],[]),([75,25,0,1,2,4],[94,109,110,111,112,113,114],[]),([42,0,1,6,2,3],[14,28,31,32,35,49,115,116],[]),([75,0,1,6,2,4],[49,109,111,112,113,116,117],[]),([28,0,1,8,2,3,4,5],[20,49,118],[0]),([34,36,0,1,2,3,4,5],[20,21,119],[0]),([0,1,8,2,3,4,10,5],[20,24,49,120,121,122],[0]),([33,0,1,2,3,4,37,5],[20,49,123],[0]),([42,0,1,6,2,3,20],[14,28,31,32,35,49,116],[]),([77,0,1,2,3,4,5],[101,124,125,126,127,128,129],[]),([80,0,1,2,4,5],[73,130,131,132,133,134,135,136],[]),([0,19,3,16,23,20],[14,24,49,137,138,139],[0]),([42,0,1,2,3,50],[14,27,28,63,64,140],[]),([81,83,0,3,4,5],[24,49,141,142,143],[]),([86,0,1,2,3,4,5,85],[73,144],[]),([0,1,2,19,3,4,87,20],[24,145,146,147,148],[]),([77,33,0,1,2,3,4,5],[20,101],[]),([32,34,0,1,2,3,4,5],[20,21,49,129,149],[0]),([0,1,9,8,2,3,4,5],[20,49,121,150,151,152,153,154],[0]),([0,2,27,3,16,5],[14,15,155,156,157,158],[0]),([33,0,1,2,3,4,88],[24,119,159],[]),([89,83,0,2,3,5],[24,49,160,161,162,163],[]),([0,1,27,3,4,23],[13,14,164,165,166],[0]),([90,0,1,2,3,4,5,20],[93,167,168,169],[]),([0,1,6,2,3,4,92,20],[170,171,172],[]),([0,1,2,3,4,93,5],[49,125,126,167,173,174,175,176],[]),([75,0,1,2,4,94],[109,112,117,177,178,179,180],[]),([95,0,1,3,96,4,5],[14,181,182,183,184,185],[]),([29,0,1,8,2,3,4,5],[20,49,122,152,186],[0]),([45,0,2,3,98,5],[14,49,187,188,189],[]),([91,0,1,8,2,4,5],[20,152,153,154,190,191,192,193],[]),([99,0,1,2,19,3,4,5],[49,93,194,195],[]),([0,1,2,19,3,4,101,7],[24,146,147,148,196,197],[]),([102,0,1,2,100,19,3,5],[14,49],[]),([81,103,1,3,4,5],[49,198,199,200],[]),([104,105,0,1,3,4],[24,89,201,202,203],[]),([103,1,2,106,3,4,5],[49,125,198,204,205,206,207],[]),([33,0,1,2,3,4,35],[21,24,116,208,209],[0]),([107,108,1,2,3,4,5],[49,167,210,211,212,213,214,215,216],[]),([75,109,0,1,2,4],[94,111,112,117,178,217],[]),([77,0,1,2,3,4,5,85],[101,218],[]),([110,0,1,2,3,4,5,85],[73,219],[]),([111,33,0,1,2,3,4,5],[21,220],[]),([89,81,0,1,3,5],[49,221,222,223,224],[]),([112,113,0,1,2,3,4],[93,225,226],[]),([24,25,0,2,3,5],[49,50,227,228,229],[0]),([0,1,3,16,115,20],[14,230,231,232,233,234,235],[]),([104,0,1,3,96,4,5],[14,73,181,236,237,238],[]),([116,0,1,19,3,4,5],[73,89,239,240,241,242],[]),([117,0,1,3,119,5],[49,243,244,245,246,247],[]),([0,1,120,2,3,4,5],[78,125,126,167,240,248,249,250,251],[]),([52,97,0,1,2,3,4,20],[14,49,252,253,254],[]),([121,42,0,1,2,3],[27,31,32,35,255,256],[]),([0,1,19,21,3,4,23,20],[14,24,49,257,258,259],[0]),([22,0,1,2,3,4,5,20],[49,93,94,260],[0]),([124,0,1,2,4,5],[49,261,262,263,264],[]),([75,0,1,2,4,16],[109,113,178,234,235,265,266],[]),([104,91,0,1,2,3,4,63],[24,89,267,268],[]),([0,1,125,2,3,23,20],[14,139,269,270,271],[]),([126,0,1,2,3,5],[24,73,272,273,274,275,276,277,278],[]),([127,45,0,2,3,4],[14,49,279,280,281,282],[]),([42,0,1,2,3,47],[27,31,32,35,48,283,284],[]),([0,1,3,4,129,5,58],[23,73,285],[]),([130,0,1,2,3,4],[14,49,234,235,286,287,288,289],[]),([131,0,1,2,19,3,4,5],[23,49,240,290],[]),([132,45,0,2,3,5],[14,49,291,292,293,294],[]),([127,132,0,1,2,3],[49,295,296,297],[]),([0,1,120,2,3,4,5,58],[20],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_7 : checkNodesBT W_24 g_24 F_24 P_24_7 A_24 B_24_6 7 N_24_7 = true := by decide +kernel
def B_24_7 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_7
set_option maxRecDepth 500000 in
lemma B_24_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 7 xs.toFinset) B_24_7 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_6_ok C_24_7
def P_24_8 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 [14,20,21,23,24,25,28,31,38,41,43,45,47,48,49,50,63,64,67,73,75,77,78,80,89,91,92,93,94,98,100,101,103,104,107,110,112,113,114,116,119,121,122,125,126,129,135,138,139,141,143,146,147,148,149,152,157,161,163,167,168,170,171,172,176,180,181,182,185,188,191,193,197,198,199,201,204,205,209,210,211,213,216,217,220,221,225,229,233,234,235,236,237,239,240,242,244,245,252,253,254,257,258,267,268,269,279,281,285,291,293,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1198,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208,1209,1210,1211,1212,1213,1214,1215,1216,1217,1218,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248,1249,1250,1251,1252,1253,1254,1255,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1296,1297,1298,1299,1300,1301,1302,1303,1304,1305,1306,1307,1308,1309,1310,1311,1312,1313,1314,1315,1316,1317,1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1337,1338,1339,1340,1341,1342,1343,1344,1345,1346,1347,1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1367,1368,1369,1370,1371,1372,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410,1411,1412,1413,1414,1415,1416,1417,1418,1419,1420,1421,1422,1423,1424,1425,1426,1427,1428,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454,1455,1456,1457,1458,1459,1460,1461,1462,1463,1464,1465,1466,1467,1468,1469,1470,1471,1472,1473,1474,1475,1476,1477,1478,1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,1492,1493,1494,1495,1496,1497,1498,1499,1500,1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1529,1530,1531,1532,1533,1534,1535,1536,1537,1538,1539,1540,1541,1542,1543,1544,1545,1546,1547,1548,1549,1550,1551,1552,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689,1690,1691,1692,1693,1694,1695,1696,1697,1698,1699,1700,1701,1702,1703,1704,1705,1706,1707,1708,1709,1710,1711,1712,1713,1714,1715,1716,1717,1718,1719,1720,1721,1722,1723,1724,1725,1726,1727,1728,1729,1730,1731,1732,1733,1734,1735,1736,1737,1738,1739,1740,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1751,1752,1753,1754,1755,1756,1757,1758,1759,1760,1761,1762,1763,1764,1765,1766,1767,1768,1769,1770,1771,1772,1773,1774,1775,1776,1777,1778,1779,1780,1781,1782,1783,1784,1785,1786,1787,1788,1789,1790,1791,1792,1793,1794,1795,1796,1797,1798,1799,1800,1801,1802,1803,1804,1805,1806,1807,1808,1809,1810,1811,1812,1813,1814,1815,1816,1817,1818,1819,1820,1821,1822,1823,1824,1825,1826,1827,1828,1829,1830,1831,1832,1833,1834,1835,1836,1837,1838,1839,1840,1841,1842,1843,1844,1845,1846,1847,1848,1849,1850,1851,1852,1853,1854,1855,1856,1857,1858,1859,1860,1861,1862,1863,1864,1865,1866,1867,1868,1869,1870,1871,1872,1873,1874,1875,1876,1877,1878,1879,1880,1881,1882,1883,1884,1885,1886,1887,1888,1889,1890,1891,1892,1893,1894,1895,1896,1897,1898,1899,1900,1901,1902,1903,1904,1905,1906,1907,1908,1909,1910,1911,1912,1913,1914,1915,1916,1917,1918,1919,1920,1921,1922,1923,1924,1925,1926,1927,1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944,1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,1955,1956,1957,1958,1959,1960,1961,1962,1963,1964,1965,1966,1967,1968,1969,1970,1971,1972,1973,1974,1975,1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031,2032,2033,2034,2035,2036,2037,2038,2039,2040,2041,2042,2043,2044,2045,2046,2047,2048,2049,2050,2051,2052,2053,2054,2055,2056,2057,2058,2059,2060,2061,2062,2063,2064,2065,2066,2067,2068,2069,2070,2071,2072,2073,2074,2075,2076,2077,2078,2079,2080,2081,2082,2083,2084,2085,2086,2087,2088,2089,2090,2091,2092,2093,2094,2095,2096,2097,2098,2099,2100,2101,2102,2103,2104,2105,2106,2107,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118]
def N_24_8_0 : List NodeSpec := [([45,0,1,2,3,4,5],[14,38,125,167,298,299,300],[]),([135,0,1,2,3,4,5],[20,21,24,49,93,125,167,301,302,303,304],[]),([0,1,2,3,136,4,5,20],[14,24,305,306,307,308,309,310,311],[]),([45,0,1,2,3,4,5,39],[14,49,312,313,314,315,316,317,318],[]),([42,0,1,2,3],[28,31,94,139,319],[0]),([0,1,2,3,41,20,50],[14,45,49,63,64,320,321,322,323],[0]),([0,1,2,3,41,20,47],[43,45,47,48,49,324,325,326,327],[0]),([139,0,1,2,3,4,5],[14,125,167,328,329,330,331],[]),([141,0,1,2,3,4,5],[49,93,125,126,167,332,333,334,335,336,337],[]),([0,1,2,142,3,4,5],[14,49,338,339,340,341],[]),([0,1,143,2,3,4,5],[14,24,125,126,167,342,343,344],[]),([0,1,144,2,3,4,5],[20,23,49,125,167,345,346,347],[]),([75,0,1,2,4],[94,112,113,139],[0]),([24,0,1,2,3,4,5],[49,104,125,126,167,229,348,349,350,351,352,353],[0]),([0,2,3,14,4,17,5],[24,49,354,355,356,357,358,359],[0]),([45,0,1,2,3,41,20],[14,38,43,45,320,325,360],[0]),([0,2,3,15,14,4,5],[50,89,359,361,362,363,364,365],[0]),([145,0,2,3,14,4,5],[49,50,89,359,366,367,368,369],[]),([0,2,3,14,146,4,5],[21,24,49,50,89,359,366,369,370,371,372,373],[]),([149,0,1,2,3,4,5],[20,23,125,126,167,374,375,376],[]),([151,0,1,2,3,4,5],[20,89,125,167,377,378,379,380],[]),([91,118,0,1,2,4,5],[23,73,93,193,381,382,383,384],[]),([0,1,2,3,4,92,20],[21,49,94,170,385,386,387],[0]),([153,0,1,2,3,4,5],[14,21,49,125,126,167,388,389,390,391],[]),([155,0,1,2,3,4,5],[14,24,125,126,167,392,393,394,395],[]),([156,0,1,2,3,4,5],[14,21,24,49,125,167,396,397,398,399,400],[]),([0,1,2,159,3,4,5],[49,89,125,167,401,402,403,404],[]),([160,0,1,2,3,4,5],[14,24,125,167,405,406,407],[]),([116,0,1,2,3,4,5],[24,101,125,126,167,240,242,408,409,410],[0]),([162,0,1,2,3,4,5],[24,125,126,167,411,412,413,414,415,416],[]),([165,0,1,2,3,4,5],[14,125,167,417,418,419,420],[]),([167,0,1,2,3,4,5],[49,125,167,421,422,423,424,425],[]),([0,1,2,21,3,4,23,20],[14,24,49,73,257,426,427,428],[0]),([0,1,152,3,4,5,23],[14,49,104,429,430,431],[]),([117,73,0,1,2,3,4,5],[20,24,49,89,107,432,433,434,435,436,437],[]),([0,1,169,2,3,4,5,7],[21,49,73,122,437,438,439,440,441,442,443,444],[]),([170,0,1,2,3,4,5],[21,49,93,125,167,445,446,447,448],[]),([0,1,171,2,3,4,5],[21,49,93,125,167,449,450,451],[]),([53,0,1,3,4,5,39],[14,49,139,452,453,454],[0]),([40,0,1,2,3,4,5],[21,24,49,93,125,167,455,456,457,458,459],[]),([52,0,1,2,3,4,20],[49,67,75,104,253,254,460],[0]),([0,1,2,3,172,173,5],[461,462,463,464,465,466,467,468],[]),([0,1,2,3,4,5,85,174],[14,73,406,407,469,470,471],[]),([45,0,1,2,3,4,38,5],[14,49,139,316,317,318,472,473,474,475],[]),([175,0,1,2,3,4,5],[24,49,93,125,167,240,476,477,478,479],[]),([73,0,1,2,3,4,38,5],[20,24,49,89,101,107,126,432,433,472,473,479,480,481],[]),([0,1,2,3,4,38,5,71],[24,49,75,101,482,483,484,485],[0]),([176,0,1,3,4,38,5],[49,73,479,486,487,488],[]),([83,0,1,2,3,4,5,7],[24,49,73,122,438,489,490,491,492,493,494],[]),([91,83,0,1,2,3,4,5],[14,21,49,73,126,490,493,494,495,496,497,498,499],[]),([83,0,1,2,3,4,157,5],[49,73,490,493,494,500,501,502,503],[]),([0,1,2,3,4,177,5],[24,49,101,479,504,505,506,507,508,509],[]),([178,0,1,2,3,4,82,5],[49,98,503,510,511,512,513,514,515,516,517,518],[]),([0,1,2,54,3,4,82,5],[49,89,98,510,511,519,520,521,522],[]),([59,0,1,2,3,4,5],[24,49,77,93,125,167,240,523,524,525],[]),([0,1,2,3,128,4,5,58],[21,23,24,49,73,285,526,527,528,529,530],[0]),([60,0,1,2,3,4,5],[20,23,24,49,125,167,531,532,533,534,535],[]),([133,0,1,2,3,61,5],[24,49,536,537,538,539,540],[]),([180,0,1,2,3,4,5],[21,49,93,125,167,541,542,543,544],[]),([183,0,1,2,3,4,5],[20,23,49,125,139,167,545,546,547,548,549],[]),([185,0,1,2,3,4,5],[14,125,167,550,551,552,553],[]),([0,1,188,2,3,4,5],[14,125,126,167,554,555,556,557],[]),([0,1,2,189,3,4,5,63],[49,89,139,240,558,559,560,561,562,563,564],[]),([0,1,2,189,3,4,5],[21,49,93,125,167,560,561,562,565],[]),([190,0,1,2,3,4,5],[21,49,125,167,566,567,568,569,570],[]),([191,132,0,1,2,3,5],[89,571,572,573,574,575],[0]),([0,1,2,3,4,192,63],[14,24,571,576,577,578,579,580],[]),([133,132,0,1,2,3,5],[49,571,581,582,583,584],[]),([193,0,1,2,3,4,5],[14,125,167,464,585,586,587],[]),([83,0,1,2,3,4,38,5,7],[24,73,101,479,481,491],[]),([0,179,2,3,4,5,63],[20,49,571,588,589,590,591,592,593],[]),([132,0,1,2,3,5,20],[14,563,571,594,595,596,597,598],[0]),([0,1,2,68,3,4,5,50],[14,24,89,599,600,601,602,603,604,605,606,607,608],[]),([0,1,2,3,194,4,5,63],[24,73,558,609,610,611,612,613,614,615],[]),([0,1,2,3,4,5,195],[14,24,616,617,618,619],[]),([0,1,2,3,4,63,85],[14,73,94,406,407,571,620,621,622,623],[]),([0,1,2,3,96,4,5,63],[24,73,89,182,410,558,571,624,625,626,627,628],[]),([91,105,0,1,2,3,4,5],[14,21,49,89,498,499,629,630,631,632],[]),([0,1,2,3,4,196,5],[21,49,633,634,635,636,637,638,639],[]),([57,53,0,1,3,4,5],[14,640,641,642,643,644],[0]),([104,0,1,2,3,4,63],[24,73,240,268,645,646,647,648],[0]),([0,1,2,68,3,4,5,66],[23,24,49,92,602,648,649,650,651,652,653,654,655,656],[0]),([117,0,1,2,68,3,4,5,63],[24,49,89,434,571,656,657,658,659],[]),([0,1,2,197,3,4,5],[21,49,93,125,167,660,661,662,663],[]),([0,1,2,3,4,5,198],[14,21,49,664,665,666,667],[]),([0,169,2,3,4,5,63],[24,49,104,668,669,670,671],[]),([199,0,1,2,3,4,5],[21,49,93,125,167,672,673,674],[]),([200,0,1,2,3,4,5],[24,125,167,675,676,677,678,679,680],[]),([0,1,2,3,4,5,201],[14,49,681,682,683,684,685,686],[]),([0,1,2,3,4,202,38,5,63],[24,49,687,688],[]),([0,1,2,203,3,4,5],[20,23,49,93,125,167,689,690,691,692,693],[]),([0,1,2,3,4,5,204],[20,23,49,694,695,696,697,698],[]),([0,1,2,3,4,5,85,205],[406,699,700,701,702,703,704],[]),([0,182,2,3,4,5,63],[23,24,49,89,104,705,706,707],[]),([0,1,2,3,4,206,5,63],[89,558,571,708,709,710,711,712],[]),([25,0,1,2,3,5,20,39],[14,49,101,314,713,714,715,716,717],[0]),([112,137,25,0,1,2,4],[110,114,718,719,720,721,722],[0]),([25,0,1,2,13,4,7],[93,114,723,724,725,726,727,728],[0]),([25,0,1,2,3,172,5],[14,110,114,462,463,586,729,730,731],[]),([0,1,2,3,207,4,5],[14,114,732,733,734,735],[]),([25,0,1,2,3,164,5],[14,419,736,737,738,739],[]),([57,45,0,1,2,3,4,5],[14,21,23,317,318,475,740,741,742,743],[]),([0,1,2,3,4,202,5],[21,49,89,687,688,744,745,746,747],[]),([208,0,1,2,3,4,5],[110,125,126,167,737,748,749,750,751],[]),([25,0,1,2,3,23,20],[14,110,114,138,139,257,258,752,753,754],[0]),([25,0,1,2,3,4,5,58],[21,23,78,110,114,526,527,529,755,756,757,758,759,760],[0]),([0,209,1,2,3,4,5],[104,110,125,126,167,728,761,762,763,764,765],[]),([163,0,1,2,3,4,192],[14,20,766,767,768,769],[]),([0,1,2,3,4,192,23],[14,110,114,753,769,770,771,772],[]),([57,0,1,2,3,4,5,192],[14,20,21,23,114,537,742,743,767,769,773,774,775,776,777,778],[]),([0,1,2,210,3,4,5,7],[24,73,93,122,438,441,779,780,781,782],[]),([0,2,3,4,211,212,5],[783,784,785,786,787,788],[]),([213,0,1,2,3,4,5],[20,21,24,93,125,126,167,789,790,791,792,793],[]),([0,1,210,3,4,5,23],[24,104,753,794,795,796,797,798],[]),([83,0,1,2,3,4,5,20],[14,24,49,73,103,306,307,490,493,494,799,800,801,802],[]),([0,1,2,3,215,16,5],[14,49,234,235,803,804,805,806],[]),([0,1,2,216,3,4,5],[21,49,93,125,167,807,808,809,810],[]),([112,83,0,1,2,3,4,5],[21,49,94,492,802,811,812,813,814,815],[]),([191,0,1,2,68,3,4,5],[24,602,656,816,817,818,819,820,821,822],[]),([132,0,1,2,3,16,5],[49,240,291,293,823],[0]),([127,0,1,2,3,4,50],[49,824,825,826,827],[0]),([0,1,2,3,4,5,217],[24,49,539,828,829,830,831,832],[]),([132,0,1,2,3,5,50],[49,291,293,823,833],[0]),([0,1,2,218,3,4,5,50],[14,49,834,835,836,837,838,839],[]),([0,1,2,3,4,114,50],[14,49,234,235,840,841,842,843,844,845],[0]),([0,1,2,54,3,4,38,5,63],[24,49,75,98,100,101,521,614,671,846],[0]),([219,0,1,2,4,16,5],[234,235,847,848,849,850,851],[]),([0,1,2,3,4,5,50],[14,49,234,235,852,853,854,855],[]),([0,1,2,3,221,16,5],[20,49,856,857,858,859],[]),([127,0,1,2,3,4,20],[49,104,279,281,860,861,862],[0]),([0,1,2,3,222,4,38,5],[24,49,100,472,521,863,864,865],[]),([45,0,2,3,4,16,5],[14,49,866,867,868],[0]),([127,0,1,2,3,16,20],[49,104,235,279,281,860,861,862],[]),([0,1,2,3,114,16,20],[14,49,234,235,844,869,870,871,872,873],[0]),([0,1,2,3,4,5,174],[14,24,571,874,875,876,877,878],[]),([45,0,2,3,16,5,20],[14,49,866,867,868],[]),([0,1,2,223,3,4,5],[234,879,880,881,882,883],[]),([0,1,2,3,4,224,5],[14,49,234,883,884,885,886,887],[]),([60,0,1,2,3,4,5,58],[23,49,73,78,240,526,527,529,531,532,888],[0]),([0,1,2,3,4,225,5],[73,235,889,890,891,892],[]),([0,1,2,13,4,16,7],[234,726,727,844,883,893,894,895],[0]),([0,1,2,3,4,17,5],[14,49,234,235,896,897,898,899,900],[]),([0,2,3,14,4,16,5],[20,50,89,234,235,367,372,901,902,903],[]),([226,227,0,1,2,4,5],[49,883,904,905],[0]),([229,0,1,2,3,16,5],[14,49,93,906,907,908,909],[]),([0,1,2,21,3,16,5,20],[49,89,305,910,911,912,913],[]),([0,1,2,122,3,16,5,20],[49,103,235,910,911,912,914,915],[]),([24,0,2,3,14,4,5],[49,50,89,348,353,359,367,369],[0]),([0,1,2,122,4,123,5],[49,904,916,917,918,919],[0]),([0,1,2,21,3,4,5,39],[23,24,49,168,305,312,313,314,426,714,920],[0]),([0,1,2,3,4,5,85,230],[73,101,701,921,922,923],[]),([0,1,2,3,4,16,5,231],[49,73,235,924,925,926,927],[]),([104,0,2,3,4,16,5],[20,24,49,928,929,930,931,932],[]),([233,0,1,2,3,4,5],[20,24,49,89,125,167,933,934,935,936,937],[]),([234,181,0,1,2,4,5],[24,147,938,939,940,941,942,943],[0]),([235,0,1,2,3,4,5],[24,49,93,125,167,240,944,945,946,947],[]),([236,0,1,19,3,4,5],[24,93,239,938,948,949,950,951],[]),([0,1,2,27,3,4,5],[14,125,157,167,952,953,954],[0]),([168,0,1,2,78,3,4,5],[24,818,955,956,957,958,959,960,961,962],[]),([0,1,2,152,3,4,5,63],[14,49,240,558,559,632,963,964,965,966],[]),([0,1,2,3,16,23,20],[49,138,234,235,257,753,967,968],[0]),([0,1,2,78,3,4,82,5],[14,24,49,73,148,210,955,969,970,971],[]),([237,0,1,2,3,4,5],[14,49,125,126,167,972,973,974,975],[]),([187,0,1,2,3,38,5],[14,49,126,479,976,977,978],[]),([104,91,0,1,2,3,4,5],[14,21,24,49,73,135,146,495,498,499,979,980,981,982],[]),([238,0,1,2,3,4,5],[14,125,167,983,984,985,986],[]),([91,0,1,19,3,4,5,23],[14,24,73,430,987,988,989,990,991,992,993],[]),([0,2,19,3,16,5,20],[24,49,867,967,994],[0]),([0,182,2,19,3,4,5],[21,23,24,49,147,239,995,996,997,998],[]),([104,91,0,1,2,19,3,4,5],[24,73,146,147,267,495,980,999],[]),([0,1,2,78,19,3,4,5,20],[24,49,73,103,146,147,938,1000],[0]),([0,1,19,3,4,23,20],[14,49,73,135,257,258,643,1001,1002],[0]),([40,0,1,2,3,4,5,20],[24,25,49,103,306,307,314,799,912,1003,1004],[0]),([193,0,1,2,3,172,5],[14,462,463,464,585,586,587],[]),([239,0,1,2,3,4,5],[20,21,24,49,93,125,167,1005,1006,1007,1008],[]),([97,0,1,3,4,38,5,23],[49,73,89,753,936,1009,1010,1011,1012,1013,1014],[]),([0,1,2,3,64,5,50],[14,24,49,89,571,1015,1016,1017,1018,1019],[0]),([0,1,2,3,4,240,5,63],[20,49,89,558,1020,1021,1022,1023,1024],[]),([0,2,3,4,16,5,66],[20,24,49,932,1025,1026,1027,1028],[]),([241,0,1,2,3,4,5],[73,125,126,167,571,1029,1030,1031,1032,1033],[]),([0,2,100,19,3,16,5],[24,146,148,1034,1035,1036],[]),([0,1,2,3,4,243,5],[430,499,1037,1038,1039,1040,1041,1042,1043,1044],[]),([109,0,1,3,244,4,5],[217,1045,1046,1047,1048,1049],[]),([67,0,1,2,3,4,5,63],[20,24,49,73,91,139,240,558,559,571,614,671,1050,1051,1052,1053],[0]),([0,1,2,3,4,242,85],[94,406,699,700,701,1054,1055,1056,1057],[]),([245,0,1,2,3,4,5],[93,104,125,126,240,1058,1059,1060,1061,1062,1063,1064],[]),([104,0,1,19,3,4,23],[24,73,104,135,1065,1066,1067,1068],[]),([0,1,6,2,3,172,5],[14,21,49,116,172,462,463,467,586,731],[]),([0,1,78,19,3,4,5,23],[24,49,73,798,987,989,1069,1070,1071,1072,1073,1074,1075],[]),([0,1,2,21,3,4,5,50],[14,49,89,168,305,912,920,1076,1077],[]),([158,0,1,2,3,4,38,5],[24,49,98,126,316,402,472,473,479,1078,1079,1080,1081],[]),([0,1,2,246,3,4,5],[93,104,126,1060,1062,1082,1083,1084,1085,1086],[]),([25,0,1,2,3,138,5],[14,93,329,330,1087,1088],[]),([109,0,1,2,13,4,7],[93,723,725,894,1063,1064,1089],[0]),([247,0,1,2,3,4,5],[14,24,125,167,240,701,922,1090,1091],[]),([234,0,2,19,3,4,16,5],[14,24,49,148,1092,1093,1094,1095,1096,1097,1098],[]),([0,19,3,4,16,5,23],[24,49,139,932,1074,1099,1100],[0]),([248,0,1,2,3,4,5],[14,49,125,126,167,883,1101,1102,1103],[]),([133,0,1,2,3,98,5],[49,1104,1105,1106,1107],[]),([0,1,2,3,4,249,5],[49,1108,1109,1110,1111,1112],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_8_0 : checkNodesBT W_24 g_24 F_24 P_24_8 A_24 B_24_7 8 N_24_8_0 = true := by decide +kernel
def N_24_8_1 : List NodeSpec := [([109,0,1,2,3,172,5],[14,125,217,463,464,467,731],[]),([49,0,2,3,14,4,5],[24,49,50,359,369,1113,1114,1115,1116],[0]),([0,2,3,161,4,5,63],[20,24,1117,1118,1119,1120,1121],[]),([0,1,2,84,3,4,5,92],[49,126,387,973,1122,1123,1124,1125,1126],[]),([112,0,1,169,2,3,4,5],[21,94,439,440,443,658,812,813,1127,1128,1129,1130,1131],[]),([0,1,2,3,250,4,5],[217,372,1132,1133,1134,1135,1136,1137],[]),([251,0,1,2,3,4,5],[20,21,24,125,126,167,182,1138,1139,1140,1141],[]),([45,0,1,2,3,4,23,20],[14,49,104,139,257,428,475,753,1001,1142],[]),([0,1,3,96,4,5,23],[24,73,410,1143,1144,1145,1146],[]),([52,0,1,3,4,38,23],[49,73,75,104,1147,1148,1149],[]),([0,1,2,3,4,5,252],[49,93,1107,1150,1151,1152,1153],[]),([253,220,0,1,2,3,4],[49,1154,1155,1156],[]),([0,1,2,19,3,4,5,85],[14,73,135,146,148,406,407,700,701,922,1157],[0]),([0,1,2,100,3,82,5],[24,148,1158,1159,1160,1161],[0]),([0,1,2,3,4,254,5],[49,122,180,1085,1162,1163,1164,1165,1166],[]),([0,1,2,3,61,38,5],[49,100,1167,1168,1169,1170,1171],[]),([256,0,1,2,3,4,5],[14,125,167,769,1172,1173,1174],[]),([0,1,2,13,4,94,7],[723,725,894,1085,1086,1089,1175,1176],[0]),([103,1,2,3,4,82,5],[49,167,198,205,210,1177,1178],[0]),([0,1,2,257,3,4,5],[14,24,1179,1180,1181,1182],[]),([0,1,2,3,94,172,5],[180,462,463,464,467,1183,1184,1185],[]),([0,259,1,2,3,4,5],[20,93,104,125,126,240,643,867,1186,1187,1188,1189,1190,1191,1192],[]),([260,0,1,2,3,4,5],[21,24,49,125,167,1193,1194,1195,1196],[]),([0,1,261,2,3,4,5],[20,89,93,104,125,126,167,1197,1198,1199,1200,1201,1202,1203],[]),([0,1,54,3,4,38,5,23],[24,49,73,798,1009,1010,1011,1012,1204,1205,1206],[]),([0,166,2,3,4,16,5],[20,89,235,1207,1208,1209,1210],[]),([263,0,1,2,3,4,5],[49,125,126,240,1211,1212,1213,1214,1215,1216],[]),([89,168,0,1,2,3,5],[24,73,1217,1218,1219,1220],[0]),([0,2,78,19,3,4,16,5],[24,49,146,148,970,1092,1094,1096,1221,1222],[]),([0,1,2,3,4,5,265],[49,167,1223,1224,1225,1226,1227,1228,1229,1230,1231],[]),([133,0,2,19,3,16,5],[24,49,148,589,1232],[]),([57,25,0,1,2,3,5,20],[14,20,23,114,537,716,717,741,754,767,912,1233,1234],[]),([104,0,1,2,76,3,4,5],[20,24,73,135,146,931,981,1235,1236,1237,1238],[0]),([253,0,1,2,3,4,20],[49,104,643,867,1239,1240,1241,1242],[]),([0,1,2,3,172,17,5],[14,464,586,1243,1244,1245,1246],[]),([0,1,2,3,16,5,20],[14,20,234,235,299,300,1247,1248],[]),([132,0,2,3,16,5,63],[20,49,89,571,1249,1250,1251],[]),([81,0,19,3,4,16,5],[24,49,1093,1094,1252,1253,1254],[]),([0,6,2,3,161,4,5],[20,21,24,1238,1255,1256,1257,1258,1259,1260],[]),([0,1,2,3,264,5,20],[49,167,307,643,867,1231,1261,1262,1263,1264,1265],[]),([46,0,1,2,3,41,20],[14,41,43,45,47,325,1266],[0]),([0,1,2,3,4,5,266],[21,49,93,125,167,1267,1268,1269,1270],[]),([0,2,19,3,4,16,5,7],[24,49,73,441,1092,1096,1164,1271,1272],[]),([32,0,1,2,3,4,5],[21,49,93,125,126,1273,1274,1275,1276],[]),([45,0,2,3,4,5,50],[14,49,1277,1278,1279],[0]),([83,0,2,3,4,16,5],[24,801,1280,1281,1282],[0]),([89,0,1,2,3,4,5,7],[49,73,122,438,491,1283,1284,1285,1286,1287],[]),([25,0,1,3,244,4,5],[110,114,1045,1047,1049,1288,1289,1290],[]),([267,0,1,2,3,4,5],[93,104,125,126,240,589,1291,1292,1293,1294,1295,1296,1297],[]),([268,0,1,2,3,4,5],[125,126,180,240,372,1134,1137,1298,1299,1300],[]),([0,1,2,3,4,16,5,58],[49,73,78,234,235,526,527,529,904,1301,1302,1303,1304],[]),([269,0,1,2,3,4,5],[21,49,73,93,125,167,839,1305,1306,1307],[]),([0,1,2,4,16,270,5],[234,883,1308,1309,1310,1311,1312],[]),([0,1,2,78,3,4,5,66],[24,49,73,94,135,955,956,957,1028,1313,1314,1315,1316,1317],[]),([91,0,1,2,3,4,5,63,66],[14,24,49,89,652,992,1318,1319],[0]),([0,1,2,19,3,4,271,5],[49,73,146,1320,1321,1322,1323,1324,1325],[]),([57,0,1,2,3,16,5,20],[23,49,741,910,911,912,915,967,1326],[]),([45,0,2,3,4,5,63],[14,38,89,867,912,1327,1328,1329],[0]),([272,0,1,2,3,4,5],[49,125,126,240,1231,1330,1331,1332,1333,1334],[]),([273,0,1,2,3,4,5],[20,116,125,126,1260,1335,1336,1337,1338],[]),([127,220,0,1,2,3,4],[49,1339,1340,1341],[]),([0,1,2,3,4,5,275],[21,49,1342,1343,1344,1345,1346,1347],[]),([234,0,1,2,3,4,82,5],[24,49,73,148,176,210,818,969,1098,1348,1349,1350,1351,1352],[]),([0,1,276,2,3,4,5],[14,21,49,125,167,1353,1354,1355,1356],[]),([0,277,2,3,4,16,5],[49,234,235,1156,1357,1358,1359],[]),([0,1,278,2,3,4,5],[21,93,104,116,125,126,152,487,1360,1361,1362,1363],[]),([117,118,0,1,3,4,5],[23,73,139,244,434,1166,1364,1365],[0]),([53,0,1,3,4,38,5],[14,49,643,1366,1367],[0]),([0,2,19,3,161,4,5],[20,21,24,148,677,1118,1368,1369],[]),([0,1,2,3,98,5,20],[14,49,188,1107,1370,1371,1372],[0]),([112,137,109,0,1,2,4],[217,718,720,1373,1374],[0]),([0,1,2,3,61,5,20],[24,49,80,539,1375,1376,1377,1378],[0]),([0,1,125,2,3,5,20],[14,20,269,1379,1380,1381],[0]),([279,0,1,6,2,3,5],[20,116,1260,1382,1383,1384,1385],[]),([0,1,2,54,4,55,5],[49,100,479,1386,1387,1388,1389],[0]),([83,0,1,3,4,5,23],[24,49,73,795,798,1390,1391,1392],[]),([280,0,1,2,3,5,20],[643,867,1057,1393,1394,1395,1396],[]),([89,0,2,19,3,16,5],[20,24,49,148,1397,1398,1399],[]),([0,1,6,2,4,281,5],[20,104,152,172,1260,1400,1401,1402,1403],[]),([91,0,1,6,2,3,4,5,20],[14,49,116,171,172,307,499,799,1404,1405],[0]),([0,1,2,3,16,172,5],[14,234,235,464,586,730,1406,1407],[]),([0,1,282,2,3,4,5],[24,49,116,125,126,1408,1409,1410,1411],[]),([89,0,1,2,3,38,5],[49,1412,1413,1414,1415],[0]),([97,0,1,2,3,4,5,39],[21,24,49,73,89,458,936,1416,1417,1418,1419,1420,1421,1422,1423,1424],[]),([34,33,0,1,2,3,4,5],[24,93,116,129,209,1425,1426,1427,1428,1429],[0]),([0,1,2,19,3,4,5,101],[24,73,146,147,197,938,1430,1431,1432,1433],[0]),([0,1,2,19,3,4,283,5],[14,49,73,938,1434,1435,1436,1437,1438],[]),([0,169,2,19,3,4,5],[20,24,49,239,1439,1440,1441,1442],[]),([0,1,2,284,3,4,20],[14,49,104,1443,1444,1445,1446],[]),([0,1,6,2,13,4,7],[49,152,172,723,725,726,727,1089],[0]),([0,1,285,2,3,4,5],[20,24,49,93,125,126,152,1062,1447,1448,1449],[]),([286,0,1,2,3,4,5],[23,93,104,125,126,167,537,1450,1451,1452,1453,1454,1455],[]),([102,0,1,2,84,3,4,5],[49,125,126,167,341,344,441,1126,1456,1457,1458,1459],[]),([0,1,2,3,4,61,5,63],[24,49,89,240,539,558,559,1460,1461,1462,1463],[]),([0,1,287,2,3,4,5],[14,21,125,126,307,643,1464,1465,1466],[]),([0,1,6,2,76,157,5],[116,152,1260,1467,1468,1469,1470,1471,1472],[]),([112,81,0,1,2,3,4,5],[21,49,94,812,813,1473,1474,1475,1476,1477,1478],[]),([0,1,2,106,3,4,82,5],[49,93,176,204,210,220,969,1349,1479],[0]),([81,0,1,19,3,4,5],[24,49,143,199,239,1480,1481,1482],[0]),([112,31,0,1,2,3,4,5],[21,49,94,812,1475,1483,1484,1485,1486],[]),([59,0,1,2,3,4,5,58],[20,23,24,49,77,78,523,524,525,526,527,529,1487,1488],[0]),([0,1,2,288,3,4,5],[20,49,125,135,167,938,1489,1490,1491,1492,1493],[]),([289,0,1,2,3,4,5],[20,24,49,116,125,126,1137,1494,1495,1496],[]),([33,91,0,1,2,3,4,5],[14,21,24,49,116,209,267,430,495,1497],[0]),([25,73,0,2,3,4,5],[24,107,433,728],[0]),([0,1,2,100,19,3,4,5,7],[24,49,146,147,148,491,938,1498,1499],[0]),([0,1,2,3,4,290,5],[21,49,185,1500,1501,1502,1503,1504],[]),([255,178,0,1,2,4,5],[49,100,479,1505,1506,1507,1508],[0]),([112,137,0,1,2,4,94],[180,718,720,1373,1374,1509,1510],[0]),([36,33,0,1,2,3,4,5],[24,49,119,129,209,1425,1427,1511,1512,1513],[0]),([0,1,2,3,4,291,5],[21,49,129,1514,1515,1516,1517,1518],[]),([292,0,1,2,3,4,5],[114,125,126,167,728,1088,1519,1520,1521,1522],[]),([0,1,6,2,21,3,4,5,20],[14,24,49,103,116,168,171,305,306,307,799,1404],[0]),([127,0,1,2,3,4,5],[49,125,126,167,234,235,1523,1524,1525,1526],[]),([133,220,0,1,6,2,3],[116,172,1260,1527,1528,1529,1530],[0]),([0,1,2,54,3,4,5,39],[14,24,49,73,458,519,521,1206,1416,1417,1531],[]),([293,0,1,2,3,4,5],[21,93,101,104,125,126,171,1144,1532,1533,1534,1535,1536],[0]),([294,0,2,3,4,211,5],[20,784,785,786,1537,1538,1539,1540],[]),([0,1,2,295,3,4,5],[14,125,167,1541,1542,1543,1544],[]),([133,280,0,1,2,3,5],[49,581,589,1057],[]),([0,1,84,3,96,4,5],[20,21,73,181,182,236,624,1545,1546,1547,1548],[0]),([0,1,2,296,3,4,5],[20,49,125,146,167,938,1549,1550,1551,1552,1553],[]),([0,1,2,3,4,5,297],[21,49,1484,1554,1555,1556,1557,1558],[]),([0,1,298,2,3,4,5],[21,49,93,125,1294,1559,1560,1561],[]),([0,1,152,3,4,38,5],[14,21,49,430,1562,1563],[]),([97,0,1,2,3,4,38,5,20],[14,20,49,73,89,100,799,1564],[0]),([0,1,2,3,299,4,5,20],[73,306,307,426,1565,1566,1567],[]),([0,1,300,2,3,4,5],[125,167,1568,1569,1570,1571,1572],[]),([95,91,0,1,2,3,4,5],[14,21,49,1039,1125,1573,1574],[]),([0,1,2,3,301,4,5],[49,167,235,883,1575,1576,1577,1578],[]),([42,0,1,2,3,20],[14,28,31,49,94,104,139],[0]),([0,1,210,19,3,4,5],[24,148,1579,1580,1581,1582],[]),([0,1,2,3,4,302,5],[14,49,235,844,1583,1584,1585,1586],[]),([0,1,6,2,3,41,20],[14,43,47,49,116,172,320,325],[0]),([0,1,6,3,244,4,5],[49,116,1045,1049,1289,1290,1587],[]),([0,1,3,4,16,115,5],[49,233,234,235,1588,1589,1590],[0]),([33,133,0,1,2,3,4,5],[24,49,116,129,1561],[]),([0,1,19,3,96,4,5],[21,73,237,625,1144,1548,1591,1592],[0]),([132,57,0,1,2,3,4,5],[21,23,49,742,743,1593,1594,1595,1596,1597],[]),([0,1,303,2,3,4,5],[14,20,93,104,125,126,430,499,1598,1599,1600,1601,1602,1603],[]),([102,0,1,6,2,3,4,5],[14,49,116,125,152,172,240,339,342,1456,1457,1604],[]),([97,0,1,2,3,4,5,184],[14,20,21,49,552,936,1105,1423,1424,1605,1606,1607,1608,1609,1610,1611],[]),([0,1,304,2,3,4,5],[14,73,125,126,167,1612,1613,1614,1615],[]),([112,137,0,1,6,2,4],[49,116,718,720,721,722,1374],[0]),([0,1,2,3,4,306,5],[49,1616,1617,1618,1619,1620,1621],[]),([132,0,1,2,3,4,5],[21,49,93,125,126,167,291,293,823,833],[]),([0,1,307,2,3,4,5],[20,93,104,116,152,1260,1622,1623,1624,1625],[]),([0,1,3,244,4,94,5],[180,1045,1046,1049,1137,1289,1626,1627,1628],[]),([0,1,6,2,3,4,138,5],[14,49,93,152,172,330,1088,1629,1630,1631,1632],[]),([0,6,2,3,4,211,5],[20,116,784,785,786,1260,1539,1633],[]),([0,1,8,2,3,4,5],[20,49,93,116,121,122,152,1166,1634],[0]),([0,1,308,19,3,4,5],[21,24,147,1635,1636,1637,1638],[]),([89,0,1,2,3,4,5],[21,49,93,125,126,167,1639,1640,1641,1642],[]),([104,0,1,2,3,4,66],[24,73,139,201,1643,1644,1645],[0]),([0,1,2,78,79,4,5],[24,147,938,1646,1647,1648,1649],[0]),([309,0,1,6,2,3,4,5,20],[14,49,116,171,307,799,1650,1651],[0]),([33,0,1,2,76,3,4,5],[20,24,116,129,181,1144,1235,1427,1652],[0]),([0,6,2,3,14,4,5],[21,24,49,50,89,116,172,359,366,367,369,1115,1653],[]),([0,1,2,3,98,16,5],[21,49,1654,1655,1656,1657],[]),([0,1,6,2,3,4,5,85],[14,20,116,407,699,700,701,1260],[0]),([0,1,6,3,4,310,5],[20,116,1260,1587,1658,1659,1660],[]),([91,0,1,2,3,4,5,66],[14,21,24,49,73,498,499,992,1028,1068,1313,1314,1316,1661,1662,1663,1664,1665],[]),([311,0,1,6,2,4,5],[20,116,1260,1666,1667,1668,1669],[]),([127,0,1,2,3,4,63],[24,49,1670,1671,1672,1673],[0]),([0,1,3,4,82,5,23],[49,104,795,798,1674,1675,1676],[]),([0,1,6,2,3,4,5,20],[14,20,49,116,300,1260,1677,1678,1679],[]),([0,1,2,84,21,3,4,5,20],[14,49,73,103,168,306,307,426,799,1459,1680,1681],[]),([0,1,2,312,3,4,5],[14,125,167,1682,1683,1684,1685],[]),([112,274,0,1,2,3,4,5],[21,94,812,815,1347,1686,1687,1688,1689],[]),([0,313,1,2,3,4,5],[93,125,126,217,240,1063,1164,1166,1690,1691,1692],[]),([112,83,0,1,2,3,4,38,5],[49,75,100,802,811,814,815],[]),([314,0,1,2,3,4,5],[24,49,93,125,139,167,240,539,1693,1694,1695,1696],[]),([112,0,2,19,3,4,16,5],[24,49,932,1092,1093,1094,1097,1130,1476,1688],[]),([112,89,0,1,2,19,3,4,5],[24,49,135,147,1130,1697,1698,1699],[]),([0,140,2,3,4,16,5],[20,89,234,883,1060,1700,1701,1702],[]),([0,1,2,3,4,5,315],[21,49,1698,1703,1704,1705,1706,1707],[]),([316,0,1,2,3,4,5],[20,49,89,125,135,167,938,1708,1709,1710],[]),([91,0,1,2,84,4,5,7],[21,49,381,441,1459,1546,1711,1712,1713],[]),([112,0,1,2,100,19,3,4,5],[24,49,135,147,148,815,1714,1715,1716],[]),([95,0,1,2,76,3,4,5],[20,185,1118,1125,1126,1235,1238,1717,1718],[0]),([0,2,3,16,5,63,20],[49,234,235,240,867,1719,1720],[]),([83,0,2,3,4,82,5],[24,49,141,1177,1721,1722],[0]),([81,0,1,3,4,82,5],[49,143,199,1480,1481],[0]),([112,0,1,2,210,3,4,5],[21,94,114,779,780,812,813,1130,1723,1724,1725,1726,1727,1728],[]),([107,0,1,2,3,4,82,5],[21,49,176,210,216,969,1178,1349,1480,1729,1730],[0]),([0,1,2,3,4,74,5],[49,93,1731,1732,1733,1734],[0]),([0,1,2,84,3,4,5,85],[14,20,406,699,700,922,1125,1126,1547],[0]),([158,0,2,3,4,16,5],[49,883,1735,1736,1737,1738],[]),([0,1,2,3,4,82,5,7],[49,122,176,210,438,969,1739],[0]),([0,1,317,2,3,4,5],[49,93,125,126,167,1740,1741,1742],[]),([112,0,1,2,3,4,82,5],[49,148,210,225,812,813,969,971,1349,1480,1743,1744,1745],[0]),([91,0,1,6,2,4,5,7],[21,49,116,152,171,172,191,193,441,1260,1713,1746],[0]),([89,0,1,2,3,82,5],[49,161,163,221,1747],[0]),([113,0,1,2,3,4,5],[21,49,93,125,126,167,1748,1749,1750,1751],[0]),([0,1,308,3,4,5,23],[49,73,89,104,126,795,1564,1752,1753,1754],[]),([0,1,2,3,4,38,5,232],[24,49,75,89,101,472,473,936,1755,1756,1757,1758,1759,1760,1761],[]),([0,1,2,3,4,23,85],[73,94,701,922,1762,1763],[]),([0,1,2,3,4,232,63],[21,24,94,1764,1765,1766,1767,1768],[]),([83,0,2,19,3,4,5],[24,49,126,141,239,1177,1349,1721,1722],[0]),([0,1,2,3,4,82,5],[21,49,93,125,167,1769,1770,1771,1772],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_8_1 : checkNodesBT W_24 g_24 F_24 P_24_8 A_24 B_24_7 8 N_24_8_1 = true := by decide +kernel
def N_24_8_2 : List NodeSpec := [([319,0,1,2,3,4,5],[21,49,93,125,126,167,1773,1774,1775,1776],[]),([0,2,3,14,4,94,5],[24,49,50,89,180,359,366,369,372,1777,1778],[]),([112,89,0,1,2,3,4,5],[21,49,94,812,813,815,1697,1698,1699,1779],[]),([0,1,2,320,3,4,5,20],[14,38,49,306,307,1780,1781,1782],[]),([0,1,2,19,21,3,4,5,20],[14,24,49,73,103,426,799,912,938,1681],[0]),([89,0,1,2,19,3,4,5,7],[24,49,73,146,441,938,1283],[]),([105,0,1,3,4,5,66],[24,89,139,1662,1783,1784,1785],[0]),([0,1,2,321,3,4,5,66],[24,49,73,93,135,1028,1313,1314,1664,1665,1786,1787,1788],[]),([322,0,1,2,3,4,5],[125,126,167,234,235,240,1789,1790,1791,1792,1793],[]),([0,1,2,3,4,5,323],[20,49,89,1794,1795,1796,1797,1798],[]),([324,0,1,2,3,4,5],[14,49,125,167,240,1799,1800,1801],[]),([109,0,2,3,14,4,5],[24,50,89,217,359,366,369,1115],[]),([67,0,1,2,3,4,5],[21,49,73,93,125,126,167,1802,1803,1804,1805],[]),([0,1,2,19,3,4,5,87],[24,49,135,146,148,1806,1807,1808,1809,1810,1811],[0]),([0,1,2,19,3,4,5,92],[14,24,49,135,146,945,973,1123,1124,1157,1812],[]),([102,0,1,2,19,3,4,5],[14,24,49,146,239,240,339,342,344,938,1157,1456],[0]),([0,2,68,3,4,16,5,63],[14,24,89,235,571,657,1813,1814,1815,1816,1817],[]),([0,1,2,325,3,4,5,39],[14,24,49,73,458,1416,1417,1818,1819,1820],[]),([0,1,2,3,4,326,5],[21,49,931,1821,1822,1823,1824,1825],[]),([0,1,327,2,3,4,38,5],[20,24,49,472,473,479,512,1826,1827,1828],[]),([0,1,2,3,328,4,5],[21,24,93,125,148,167,1829,1830,1831,1832,1833],[]),([127,214,0,1,2,3,4],[49,1834,1835,1836],[0]),([0,1,2,122,3,4,5,50],[14,49,235,834,835,839,1837,1838,1839,1840],[]),([329,0,1,2,3,4,5],[125,126,240,1118,1144,1841,1842,1843,1844],[]),([81,0,1,3,4,38,5],[49,1094,1845,1846,1847],[0]),([330,0,1,2,3,4,5],[21,73,93,104,125,126,146,147,148,167,1848,1849,1850,1851,1852],[]),([132,0,1,2,3,4,5,66],[24,49,101,565,649,650,652,1318,1593,1595,1596,1853,1854,1855,1856,1857],[]),([0,1,2,19,76,157,5],[135,148,938,1467,1468,1470,1858,1859,1860,1861],[]),([0,1,2,3,4,331,5],[49,1862,1863,1864,1865,1866],[]),([105,0,1,19,3,4,5],[24,89,239,1662,1783,1784,1785,1867],[0]),([0,2,3,4,114,16,63],[24,49,234,235,844,1868,1869,1870,1871,1872],[]),([0,2,3,64,16,5,63],[24,49,89,1873,1874,1875,1876],[]),([0,1,2,332,3,4,5],[20,49,89,125,167,480,1877,1878,1879],[]),([108,1,2,3,4,82,5],[49,125,210,211,213,220,969,1177],[0]),([0,1,2,333,3,4,5],[14,125,167,1880,1881,1882,1883],[]),([0,1,3,4,38,23,20],[14,20,73,75,126,643,1884,1885],[]),([0,1,2,3,4,334,5],[49,1886,1887,1888,1889,1890],[]),([0,1,154,2,3,4,38,5],[14,49,100,126,316,398,472,473,1891,1892,1893,1894],[]),([91,0,1,2,19,4,5,7],[21,49,147,193,938,1068,1711,1713,1746],[]),([0,1,182,2,3,4,5,20],[14,20,23,49,306,307,549,741,799,1895,1896,1897,1898],[]),([0,150,2,19,3,4,5],[89,126,135,148,239,240,379,1899,1900,1901],[]),([0,1,2,320,3,4,5],[14,21,24,49,125,167,475,1780,1781,1782],[]),([0,1,2,3,4,5,335],[21,24,49,93,492,1902,1903,1904,1905,1906],[]),([0,1,2,3,138,16,5],[14,234,329,330,883,1907,1908],[]),([0,1,2,308,3,4,5,20],[14,49,73,104,306,307,799,936,1909,1910,1911,1912],[]),([0,1,2,336,3,4,5],[20,23,89,125,135,148,167,1913,1914,1915,1916],[]),([52,97,0,1,2,3,4,5],[21,49,73,89,101,449,936,1423,1424,1917,1918,1919],[0]),([73,0,2,19,3,4,5],[24,49,89,107,126,239,480,938,1164,1920],[]),([337,0,1,2,3,4,5],[20,23,24,49,89,125,167,938,1921,1922],[]),([0,1,2,27,19,3,4,5,20],[49,73,953],[]),([89,0,1,3,4,5,23],[49,104,126,795,798,1923,1924,1925,1926],[]),([0,179,2,19,3,4,5],[24,49,126,239,543,589,1927],[]),([25,0,2,3,14,4,5],[49,50,89,110,114,359,369,372,1115,1928],[0]),([0,1,2,338,3,4,5],[21,49,93,125,167,1929,1930,1931,1932],[]),([0,154,2,3,4,5,63],[14,24,104,1039,1933,1934],[]),([0,1,2,339,3,4,5],[21,49,93,125,167,1935,1936,1937,1938,1939],[]),([0,1,2,68,3,4,38,5,63],[24,49,73,75,89,98,100,614,615,1855,1940],[0]),([274,0,1,2,3,4,5,7],[49,73,104,438,491,1126,1164,1689,1941,1942],[]),([0,1,6,2,3,4,5,92],[14,49,116,171,387,945,1122,1123,1812],[0]),([340,0,1,2,3,4,5],[49,93,104,125,126,167,1105,1943,1944,1945,1946,1947,1948],[]),([341,0,1,2,3,4,5],[14,49,125,167,1949,1950,1951,1952],[]),([0,1,2,3,342,4,5],[75,104,167,479,1953,1954,1955,1956,1957],[]),([343,0,1,2,3,4,5],[21,49,125,126,167,1958,1959,1960,1961,1962],[]),([344,0,1,2,3,4,5],[49,125,126,167,1107,1963,1964,1965,1966],[]),([345,0,1,2,3,4,5],[21,49,93,125,167,1967,1968,1969],[]),([105,0,2,3,4,16,5],[20,24,49,638,1970,1971,1972],[]),([0,1,2,4,98,5,7],[49,1973,1974,1975,1976,1977],[]),([89,0,1,2,3,16,5],[49,240,1978,1979,1980,1981],[0]),([133,0,1,2,3,264,5],[49,589,1231,1982,1983,1984],[]),([117,0,1,2,3,4,5,232],[24,49,89,435,436,1571,1755,1756,1758,1760,1761,1985,1986],[]),([346,0,1,2,3,4,5],[20,49,89,125,126,167,1987,1988,1989,1990,1991],[]),([176,0,1,19,3,4,5],[49,135,239,487,938,1740,1742,1992,1993,1994],[]),([347,0,1,2,3,4,5],[49,93,125,126,167,1995,1996,1997,1998,1999],[]),([0,1,2,3,4,119,5],[24,49,245,2000,2001,2002,2003],[0]),([0,1,2,348,3,4,5],[14,49,2004,2005,2006,2007],[]),([97,0,1,2,4,38,5,7],[21,49,100,479,481,491,936,2008,2009,2010,2011],[]),([0,1,2,3,4,5,230],[73,1548,2012,2013,2014,2015,2016],[]),([0,1,2,3,4,349,5],[14,73,2017,2018,2019,2020],[]),([0,1,2,3,4,5,350],[14,21,24,2021,2022,2023,2024,2025],[]),([52,97,0,1,2,3,4,38,5],[49,73,100,101,252,449,1105,1564,1918],[]),([163,0,1,2,3,16,20],[49,844,967,2026,2027,2028,2029],[]),([305,0,2,19,3,4,5],[24,49,93,126,239,938,2030,2031,2032,2033],[]),([117,97,0,1,2,4,5,7],[49,93,434,437,936,2008,2009,2010,2011,2034],[]),([351,0,1,2,3,172,5],[462,463,464,467,731,2035],[]),([97,0,1,2,3,4,23,20],[14,49,73,252,258,315,428,1001,1105,1912,2036],[]),([52,0,1,2,3,4,39],[49,73,75,126,139,2037,2038,2039],[0]),([163,25,0,1,2,3,20],[14,754,767,2027],[]),([0,1,352,2,3,4,5],[14,73,125,126,167,2040,2041,2042,2043],[]),([112,137,0,1,2,4,16],[234,235,721,722,1373,2044,2045],[0]),([97,0,1,2,3,4,5,20,39],[14,24,49,89,713,2046],[0]),([53,97,0,1,2,3,4,5],[14,21,49,641,1353,1423,1424,1912,2047,2048],[]),([353,0,1,2,3,4,5],[49,93,125,126,167,2049,2050,2051,2052],[]),([31,0,1,2,3,4,5,7],[49,101,104,438,1166,1271,1484,2053,2054],[]),([33,0,1,2,3,4,5,20],[20,24,49,116,129,306,315,643,2055],[]),([97,0,1,2,134,3,4,5],[21,49,73,89,936,1423,1424,2056,2057,2058,2059,2060,2061],[]),([53,0,1,3,4,23,20],[14,49,643,1001,2062,2063],[]),([0,1,2,354,3,4,5],[20,125,135,148,167,2064,2065,2066,2067],[]),([32,33,0,1,2,3,4,5],[20,24,101,129,149,209,1425,1427,1428,2068,2069],[0]),([57,0,2,3,4,16,5,63],[23,24,49,537,571,1813,1814,1816,1817,2070],[]),([0,2,122,3,4,16,5,63],[49,89,235,571,671,1813,1814,1816,2070,2071,2072],[]),([0,1,154,2,4,5,7],[14,21,1711,1746,2073],[]),([0,1,3,244,4,16,5],[234,235,1046,1289,1290,2074,2075],[]),([133,0,2,3,16,5,63],[49,235,571,589,2076,2077],[]),([127,0,2,3,4,16,63],[24,49,104,235,2078,2079,2080],[]),([97,45,0,2,3,4,5],[14,740,867,1329,2081,2082],[0]),([355,0,1,2,3,4,5],[14,49,125,126,167,883,2083,2084,2085],[]),([0,1,2,356,3,4,5],[20,23,125,167,904,2086,2087,2088,2089],[]),([57,0,1,2,3,4,5,50],[21,23,49,73,742,743,834,835,839,1839,2090,2091,2092],[]),([0,1,2,3,4,5,357],[21,49,93,2093,2094,2095,2096],[]),([0,1,6,2,3,4,172,5],[14,21,49,116,172,462,463,467,586,730,731],[]),([358,0,1,2,3,4,5],[21,49,93,125,167,2097,2098,2099],[]),([81,0,1,2,3,4,5,7],[49,73,122,438,1271,1272,2100,2101,2102,2103],[]),([0,1,2,84,76,157,5],[1125,1459,1468,1469,1471,1547,1858,1860,2104,2105],[]),([0,1,2,3,164,16,5],[14,235,418,419,844,2106,2107],[]),([0,1,359,2,3,4,5],[49,125,167,235,2108,2109,2110,2111],[]),([360,0,1,2,3,4,5],[24,49,93,125,126,167,240,2112,2113,2114,2115,2116],[]),([0,154,2,3,4,16,5],[14,21,49,1039,2117,2118],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_8_2 : checkNodesBT W_24 g_24 F_24 P_24_8 A_24 B_24_7 8 N_24_8_2 = true := by decide +kernel
def N_24_8 := N_24_8_0 ++ N_24_8_1 ++ N_24_8_2
def B_24_8 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_8
set_option maxRecDepth 500000 in
lemma B_24_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 8 xs.toFinset) B_24_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_24) (raw := r_24) (pspecs := ps_24) (used := [14,20,21,23,24,25,28,31,38,41,43,45,47,48,49,50,63,64,67,73,75,77,78,80,89,91,92,93,94,98,100,101,103,104,107,110,112,113,114,116,119,121,122,125,126,129,135,138,139,141,143,146,147,148,149,152,157,161,163,167,168,170,171,172,176,180,181,182,185,188,191,193,197,198,199,201,204,205,209,210,211,213,216,217,220,221,225,229,233,234,235,236,237,239,240,242,244,245,252,253,254,257,258,267,268,269,279,281,285,291,293,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1198,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208,1209,1210,1211,1212,1213,1214,1215,1216,1217,1218,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248,1249,1250,1251,1252,1253,1254,1255,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1296,1297,1298,1299,1300,1301,1302,1303,1304,1305,1306,1307,1308,1309,1310,1311,1312,1313,1314,1315,1316,1317,1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1337,1338,1339,1340,1341,1342,1343,1344,1345,1346,1347,1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1367,1368,1369,1370,1371,1372,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410,1411,1412,1413,1414,1415,1416,1417,1418,1419,1420,1421,1422,1423,1424,1425,1426,1427,1428,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454,1455,1456,1457,1458,1459,1460,1461,1462,1463,1464,1465,1466,1467,1468,1469,1470,1471,1472,1473,1474,1475,1476,1477,1478,1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,1492,1493,1494,1495,1496,1497,1498,1499,1500,1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1529,1530,1531,1532,1533,1534,1535,1536,1537,1538,1539,1540,1541,1542,1543,1544,1545,1546,1547,1548,1549,1550,1551,1552,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689,1690,1691,1692,1693,1694,1695,1696,1697,1698,1699,1700,1701,1702,1703,1704,1705,1706,1707,1708,1709,1710,1711,1712,1713,1714,1715,1716,1717,1718,1719,1720,1721,1722,1723,1724,1725,1726,1727,1728,1729,1730,1731,1732,1733,1734,1735,1736,1737,1738,1739,1740,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1751,1752,1753,1754,1755,1756,1757,1758,1759,1760,1761,1762,1763,1764,1765,1766,1767,1768,1769,1770,1771,1772,1773,1774,1775,1776,1777,1778,1779,1780,1781,1782,1783,1784,1785,1786,1787,1788,1789,1790,1791,1792,1793,1794,1795,1796,1797,1798,1799,1800,1801,1802,1803,1804,1805,1806,1807,1808,1809,1810,1811,1812,1813,1814,1815,1816,1817,1818,1819,1820,1821,1822,1823,1824,1825,1826,1827,1828,1829,1830,1831,1832,1833,1834,1835,1836,1837,1838,1839,1840,1841,1842,1843,1844,1845,1846,1847,1848,1849,1850,1851,1852,1853,1854,1855,1856,1857,1858,1859,1860,1861,1862,1863,1864,1865,1866,1867,1868,1869,1870,1871,1872,1873,1874,1875,1876,1877,1878,1879,1880,1881,1882,1883,1884,1885,1886,1887,1888,1889,1890,1891,1892,1893,1894,1895,1896,1897,1898,1899,1900,1901,1902,1903,1904,1905,1906,1907,1908,1909,1910,1911,1912,1913,1914,1915,1916,1917,1918,1919,1920,1921,1922,1923,1924,1925,1926,1927,1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944,1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,1955,1956,1957,1958,1959,1960,1961,1962,1963,1964,1965,1966,1967,1968,1969,1970,1971,1972,1973,1974,1975,1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031,2032,2033,2034,2035,2036,2037,2038,2039,2040,2041,2042,2043,2044,2045,2046,2047,2048,2049,2050,2051,2052,2053,2054,2055,2056,2057,2058,2059,2060,2061,2062,2063,2064,2065,2066,2067,2068,2069,2070,2071,2072,2073,2074,2075,2076,2077,2078,2079,2080,2081,2082,2083,2084,2085,2086,2087,2088,2089,2090,2091,2092,2093,2094,2095,2096,2097,2098,2099,2100,2101,2102,2103,2104,2105,2106,2107,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118]) S_24_ok
  have hm0 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_7_ok C_24_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_7_ok C_24_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_7_ok C_24_8_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def P_24_9 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 [14,20,21,23,24,41,48,49,64,73,75,89,93,94,98,100,101,103,104,110,114,116,122,125,126,135,139,146,147,148,152,167,171,172,180,181,210,217,220,234,235,239,240,252,257,267,300,305,306,307,312,314,315,317,320,325,330,342,345,367,369,372,376,379,381,387,398,402,407,419,426,430,433,434,435,436,438,439,441,449,453,458,462,472,473,474,475,479,480,481,487,491,493,495,496,498,499,500,501,510,512,513,517,518,519,520,521,526,529,537,543,552,554,558,559,565,571,580,581,586,589,592,593,598,599,603,605,607,614,615,623,624,625,628,631,643,648,649,652,657,658,669,671,677,700,704,706,716,718,722,723,727,728,730,731,737,741,742,743,753,754,756,757,758,760,767,769,773,775,779,785,795,798,799,808,812,813,815,816,818,821,834,839,844,862,867,873,883,904,910,912,920,922,929,936,938,955,962,963,965,967,970,981,987,989,990,992,993,996,998,999,1001,1009,1012,1014,1027,1035,1039,1047,1049,1057,1060,1062,1063,1064,1067,1068,1069,1071,1075,1076,1078,1079,1080,1085,1086,1088,1092,1094,1098,1100,1105,1115,1118,1123,1124,1125,1126,1127,1130,1134,1137,1144,1148,1156,1157,1164,1166,1177,1178,1205,1206,1208,1235,1236,1238,1250,1253,1254,1257,1260,1271,1272,1278,1281,1285,1290,1294,1301,1302,1313,1316,1329,1338,1349,1352,1353,1359,1382,1383,1396,1398,1400,1401,1405,1411,1416,1419,1421,1423,1424,1427,1428,1440,1442,1456,1458,1459,1460,1463,1467,1468,1472,1475,1476,1480,1486,1499,1511,1527,1528,1539,1546,1547,1548,1561,1564,1571,1582,1594,1596,1604,1605,1608,1610,1624,1625,1629,1638,1650,1658,1659,1662,1666,1667,1677,1683,1688,1712,1713,1718,1723,1725,1726,1736,1738,1740,1746,1755,1758,1760,1812,1813,1816,1837,1839,1855,1860,1861,1867,1869,1872,1874,1891,1893,1895,1900,1901,1909,1912,1919,1925,1971,1977,1984,1986,1993,2008,2010,2027,2031,2033,2034,2048,2056,2059,2060,2072,2079,2092,2105,2119,2120,2121,2122,2123,2124,2125,2126,2127,2128,2129,2130,2131,2132,2133,2134,2135,2136,2137,2138,2139,2140,2141,2142,2143,2144,2145,2146,2147,2148,2149,2150,2151,2152,2153,2154,2155,2156,2157,2158,2159,2160,2161,2162,2163,2164,2165,2166,2167,2168,2169,2170,2171,2172,2173,2174,2175,2176,2177,2178,2179,2180,2181,2182,2183,2184,2185,2186,2187,2188,2189,2190,2191,2192,2193,2194,2195,2196,2197,2198,2199,2200,2201,2202,2203,2204,2205,2206,2207,2208,2209,2210,2211,2212,2213,2214,2215,2216,2217,2218,2219,2220,2221,2222,2223,2224,2225,2226,2227,2228,2229,2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2249,2250,2251,2252,2253,2254,2255,2256,2257,2258,2259,2260,2261,2262,2263,2264,2265,2266,2267,2268,2269,2270,2271,2272,2273,2274,2275,2276,2277,2278,2279,2280,2281,2282,2283,2284,2285,2286,2287,2288,2289,2290,2291,2292,2293,2294,2295,2296,2297,2298,2299,2300,2301,2302,2303,2304,2305,2306,2307,2308,2309,2310,2311,2312,2313,2314,2315,2316,2317,2318,2319,2320,2321,2322,2323,2324,2325,2326,2327,2328,2329,2330,2331,2332,2333,2334,2335,2336,2337,2338,2339,2340,2341,2342,2343,2344,2345,2346,2347,2348,2349,2350,2351,2352,2353,2354,2355,2356,2357,2358,2359,2360,2361,2362,2363,2364,2365,2366,2367,2368,2369,2370,2371,2372,2373,2374,2375,2376,2377,2378,2379,2380,2381,2382,2383,2384,2385,2386,2387,2388,2389,2390,2391,2392,2393,2394,2395,2396,2397,2398,2399,2400,2401,2402,2403,2404,2405,2406,2407,2408,2409,2410,2411,2412,2413,2414,2415,2416,2417,2418]
def N_24_9_0 : List NodeSpec := [([0,1,2,21,3,4,5,20],[14,94,103,104,220,305,307,426,799,920],[0]),([53,0,1,2,3,4,5],[14,20,21,49,93,104,125,139,167,240,315,643,1353,2048],[0]),([0,1,2,3,4,5,20,39],[49,139,312,314,315,643,799,2119],[0]),([45,0,1,2,3,4,5,20],[14,104,306,307,315,317,475,867,912],[0]),([45,0,1,2,3,4,5],[14,20,21,24,93,125,126,167,317,475,867,912,1329],[0]),([46,0,1,2,3,4,5,20],[14,41,103,306,307,643,799,867,2120],[0]),([0,1,2,3,4,5,20,47],[14,48,49,167,220,306,307,643,799,867,2121,2122,2123],[0]),([311,0,1,2,4,5],[20,94,139,1666,1667],[0]),([1,2,3,4,361,5],[20,104,2124,2125,2126],[]),([0,1,140,2,3,4,5],[20,24,89,93,104,125,126,139,167,1060,2127,2128,2129],[0]),([102,0,1,2,3,4,5],[14,49,93,94,104,125,126,167,240,342,1456],[0]),([118,0,1,2,3,4,5],[20,23,73,93,125,126,139,167,240,345,1166,1271,2130],[0]),([0,1,2,13,4,7],[93,139,723,727],[0]),([0,1,2,3,4,172,5],[14,49,94,139,167,462,586,730,731],[0]),([0,1,2,3,14,4,5],[20,24,89,94,139,367,369,372,1115],[0]),([0,1,2,148,3,4,5],[20,73,93,94,376,1625,2131,2132],[0]),([0,1,2,134,3,4,5],[20,21,49,73,101,139,1294,2056,2059,2133,2134],[0]),([91,0,1,2,3,4,5,20],[14,20,49,93,103,104,306,307,799,1405,2135],[0]),([91,0,1,2,4,5,7],[21,49,93,94,104,381,441,1713,1746],[0]),([176,0,1,2,3,4,5],[21,49,73,93,94,104,125,126,167,240,487,1740,1993,2136],[0]),([73,0,1,2,3,4,5],[20,24,89,93,94,125,126,167,240,433,480,491,1164],[0]),([158,0,1,2,3,4,5],[21,24,89,93,94,104,125,126,167,240,402,1079,1080,1736,1738],[0]),([0,1,2,3,4,23,20],[49,94,139,257,315,643,753,1001],[0]),([91,0,1,2,3,4,5,23],[24,49,94,430,495,795,798,989,990,992,993,2137,2138],[0]),([112,117,0,1,2,3,4,5],[20,21,94,139,435,436,658,1127,1130,1475,1486,1571,2034,2139],[0]),([0,1,2,3,4,38,5,20],[20,49,75,100,104,315,474,643,799,2140],[0]),([112,0,1,2,3,4,38,5],[49,75,98,100,139,472,473,1130,1475,1486,2141,2142],[0]),([178,0,1,2,3,4,38,5],[20,21,49,75,98,100,101,472,473,479,512,517,518,2143,2144],[0]),([255,0,1,2,3,4,38,5],[49,73,93,98,100,472,473,2145,2146,2147,2148],[0]),([0,1,2,3,4,38,55,5],[21,49,73,472,479,2126,2149,2150,2151,2152],[0]),([112,137,0,1,2,4],[94,139,718,722],[0]),([0,1,2,3,4,5,85],[14,20,94,167,407,700,922,2153],[0]),([0,1,2,3,4,38,157,5],[20,21,49,479,487,1078,1993,2154],[0]),([83,0,1,2,3,4,38,5],[24,49,73,98,100,101,472,473,479,493,496,1281],[0]),([57,0,1,2,3,4,5,20],[14,20,49,94,139,306,307,315,537,643,741,799,912,2155],[0]),([0,1,2,3,4,61,5],[21,49,73,104,537,1460,1463,2156,2157,2158],[0]),([0,1,2,3,172,5],[94,139,462,586,731],[0]),([187,0,1,2,3,4,5],[14,49,93,94,104,125,167,240,554,2159,2160,2161],[0]),([91,0,1,2,186,4,5],[21,49,93,94,430,495,2162,2163,2164],[]),([305,0,1,2,3,4,5],[20,24,89,93,94,104,125,126,167,2165,2166,2167],[0]),([0,1,2,3,4,215,5],[94,104,139,2168,2169,2170,2171,2172],[]),([0,1,2,3,4,5,63,50],[24,49,89,571,599,603,605,607,614,2173],[0]),([0,1,2,3,64,4,5,63],[73,89,104,571,1874,2174,2175,2176,2177],[0]),([0,1,2,3,4,5,63,20],[14,20,49,89,94,139,571,867,912,2178,2179],[0]),([0,1,2,68,3,4,5,63],[89,94,104,571,614,615,657,816,2180],[0]),([279,0,1,2,3,5],[20,94,139,1382,1383,2181],[0]),([133,0,1,2,3,4,5,63],[24,89,94,139,558,559,571,589,593,671,1561,2182],[0]),([91,0,1,2,3,4,5,63],[20,24,49,89,94,267,558,559,571,614,671,1039,1855,2183],[0]),([0,1,2,76,3,4,5,63],[24,73,89,94,571,623,628,671,1118,1238,2184],[0]),([105,0,1,2,3,4,5,63],[24,89,558,559,631,1855,1971,2185],[0]),([0,1,2,3,4,5,92],[14,21,49,94,167,387,1123,1124,1812,2186],[0]),([105,0,1,2,3,4,5],[20,21,24,73,89,93,125,139,167,631,1855,1971,2185],[0]),([0,1,2,3,4,5,63,66],[24,73,139,571,614,648,649,652,1855,2187],[0]),([0,1,179,2,3,4,5],[20,21,49,73,93,125,126,167,543,589,592,593,2188],[0]),([117,0,1,2,3,4,5,63],[24,89,139,558,559,571,614,658,669,671,1571,1855,2034,2189],[0]),([57,0,1,2,3,4,5,63],[24,89,94,139,537,558,559,571,614,706,1594,1855,2190],[0]),([57,0,1,2,4,157,5],[20,21,49,93,94,487,537,1993,2191,2192],[]),([0,1,2,19,3,4,82,5],[24,49,73,147,148,210,938,1157,1177,1349,2125,2193],[0]),([181,0,1,2,19,3,4,5],[24,73,93,147,239,938,996,998,1157,1638,2194],[0]),([234,0,1,2,19,3,4,5],[14,21,24,73,126,135,146,147,148,239,240,938,1098,1157,1352,2195,2196,2197],[0]),([0,1,2,3,4,5,242,20],[20,49,94,306,307,643,867,1057,2198,2199],[0]),([226,0,1,2,3,4,16,5],[49,93,904,1301,1302,2200,2201,2202],[0]),([0,1,2,19,3,4,5,7],[24,139,146,148,438,441,491,938,1164,1166,1271,2203],[0]),([0,1,2,3,4,138,5],[14,49,93,139,167,330,1088,1629],[0]),([0,1,150,2,3,4,5],[20,24,93,94,126,167,379,1900,1901,2204],[0]),([318,0,1,2,3,4,5,63],[24,89,94,558,559,614,1855,2205,2206,2207],[0]),([91,0,1,2,3,4,5,242],[21,49,94,104,125,167,430,498,499,999,1039,1057,2208,2209,2210,2211,2212,2213],[0]),([0,1,2,3,4,38,5,63],[24,49,75,89,98,100,101,139,571,614,1281,1855,2214],[0]),([137,109,0,1,2,3,4,5],[167,1060,1062,1063,1064,1088,2215,2216],[0]),([0,1,2,100,19,3,4,5],[73,126,146,147,148,938,1035,1068,1157,1499,2217,2218,2219,2220],[0]),([109,0,1,2,3,4,5,7],[21,93,122,217,438,441,1164,1166],[0]),([0,1,2,152,3,4,5],[14,21,49,93,104,430,495,963,965],[0]),([52,0,1,2,3,4,5],[21,49,75,93,101,104,125,139,167,240,449,1148,1919,2221],[0]),([0,1,2,54,3,4,38,5],[49,93,100,101,519,520,521,1205,1206,2222],[0]),([91,0,1,2,3,4,38,5],[20,49,93,98,100,430,472,473,479,495,1893,2223],[0]),([0,1,2,3,4,94,5,7],[20,49,104,122,180,438,1085,1164,1166,2224,2225],[0]),([109,0,1,2,13,3,4,5],[93,217,372,730,1064,1134,1137,2226],[0]),([253,0,1,2,3,4,5],[21,49,93,125,126,180,240,704,2125,2126,2227,2228,2229],[0]),([0,1,2,19,3,79,4,5],[14,21,24,73,938,1157,2031,2033,2125,2230,2231],[0]),([220,0,1,2,3,4,94,5],[20,125,167,180,1085,1086,1156,1411,2232,2233,2234,2235,2236,2237],[0]),([112,0,1,6,2,3,4,5],[21,94,116,125,171,172,240,812,813,815,1130,1260,1486,1604,2238],[0]),([0,1,2,3,4,5,232],[20,21,24,89,94,1755,1758,1760,1986,2239],[0]),([112,25,0,1,2,3,4,5],[20,21,94,110,757,758,760,815,1130,1688,1725,1726,2240],[0]),([0,1,2,3,4,94,5,20],[14,20,49,104,180,306,307,643,799,867,2241,2242,2243],[0]),([132,0,1,2,3,4,5],[21,49,89,93,125,126,167,565,571,598,1250,1596,2244],[0]),([0,1,364,3,4,5],[94,2125,2126,2245,2246],[]),([0,1,2,3,4,5,184],[14,20,21,49,139,552,1571,1605,1608,2247],[0]),([97,0,1,2,3,4,5,20],[14,20,49,94,103,306,307,315,799,867,912,1105,1912,2248],[0]),([137,0,1,2,3,4,94,5],[49,125,167,1060,1062,1085,2215,2216,2234,2236,2249,2250],[0]),([163,0,1,2,3,4,20],[14,20,49,94,104,315,643,737,2027,2251],[0]),([0,1,19,3,4,5,23],[24,73,135,139,795,798,987,989,2126],[0]),([0,1,2,3,96,4,5],[20,21,73,101,181,624,625,1144,1548,2252],[0]),([133,97,0,1,2,3,4,5],[20,73,94,593,1105,1423,1424,1561,1564,2059,2060,2253,2254],[0]),([25,0,1,2,13,3,4,5],[93,110,114,367,730,757,1134,1725,2125,2226,2255],[0]),([0,2,19,3,4,16,5],[20,24,49,73,148,1092,1094,2125],[0]),([0,1,2,84,3,4,5,7],[104,122,139,438,441,1126,1164,1271,1459,1547,2256],[0]),([0,1,2,3,4,94,157,5],[20,21,180,487,500,501,1085,1736,2257,2258],[]),([0,1,2,4,281,5],[20,93,139,1400,1401],[0]),([132,0,1,2,3,4,5,63],[20,24,49,89,104,240,558,559,565,571,1250,1596,1855,2244,2259],[0]),([0,1,2,3,4,5,365],[14,20,21,167,217,1064,2125,2126,2260,2261,2262],[]),([0,1,2,3,4,5,58],[20,21,23,94,526,529,756,2263,2264],[0]),([97,0,1,2,3,4,5,23],[49,126,753,795,798,936,989,1014,1100,1105,1564,2137,2138],[0]),([0,1,6,2,3,41,4,5],[20,116,172,1260,1338,1539,2265,2266],[0]),([0,1,2,13,3,4,94,5],[20,49,180,372,1086,1134,1137,2226,2267],[0]),([0,1,2,3,4,5,20,50],[14,49,64,799,867,912,1076,2268],[0]),([0,1,2,3,4,211,5],[20,94,139,785,1539,2269],[0]),([0,1,2,3,4,366,5],[94,167,2125,2126,2270,2271,2272,2273],[]),([0,1,3,244,4,5],[94,139,1047,1049,1290],[0]),([0,1,6,2,3,4,157,5],[20,21,49,93,116,152,171,487,500,501,1260,1738],[0]),([0,1,2,78,19,3,4,5],[24,73,93,146,147,148,938,955,970,1068,1069,1071,1075,1157,2274],[0]),([367,1,2,3,4,5],[94,167,2125,2275,2276],[]),([133,0,1,2,84,3,4,5],[20,125,126,139,167,581,589,1125,1126,1458,1459,1546,1547,1561,2059,2253,2254,2277],[]),([0,1,6,2,13,3,4,5],[21,49,93,116,172,367,730,1134,1137,1260,2226],[0]),([0,1,2,3,4,5,192],[14,20,21,24,110,114,769,773,775,2278],[0]),([0,1,2,84,76,3,4,5],[21,93,126,181,623,1118,1126,1235,1236,1546,1547,1712,2279],[0]),([0,1,2,3,4,16,5,23],[49,234,235,753,904,989,1094,1100,2138,2280],[0]),([0,1,2,76,3,4,5,23],[20,73,94,126,139,181,1144,2281,2282],[0]),([91,0,1,6,2,3,4,5],[20,21,49,93,116,125,152,171,172,240,267,430,498,499,1260,1472],[0]),([112,0,1,2,19,3,4,5],[21,24,94,126,135,139,147,239,815,1130,1157,1475,1486,1688,2283],[0]),([191,0,1,2,3,4,5,63],[24,558,559,571,580,614,671,821,2284,2285],[0]),([81,0,1,2,3,4,16,5],[20,49,73,883,904,1094,1253,1254,1301,1302,2286,2287],[0]),([133,258,0,1,2,3,4,5],[93,94,167,589,1294,1561,1984],[0]),([112,0,1,2,3,4,94,5],[20,125,180,812,1086,1130,1486,1688,2234,2236,2243,2288,2289],[0]),([117,0,1,2,3,228,4,5],[93,434,435,658,1571,2290,2291,2292,2293,2294],[0]),([0,1,6,2,76,3,4,5],[21,93,171,172,623,1144,1235,1236,1238,1260],[0]),([31,0,1,2,3,4,5],[21,49,93,101,104,125,126,2126,2295,2296,2297],[0]),([127,0,1,2,3,4,5],[21,49,73,93,104,125,126,167,235,808,2079,2298,2299],[0]),([91,0,1,2,84,3,4,5],[20,21,49,125,126,495,498,1039,1126,1458,1459,1546,1712,2105,2300],[0]),([0,1,2,76,3,4,5,242],[94,1057,1118,1144,1235,1236,2210,2301,2302],[0]),([309,0,1,2,3,4,5,20],[14,49,94,306,307,799,1650,2303],[0]),([147,0,1,6,2,3,4,5],[93,116,125,152,240,1260,1472,1624,1625,1901,2304],[0]),([104,0,1,2,19,3,4,5],[24,73,104,126,135,139,146,147,148,239,929,938,981,1067,1068,1157],[0]),([0,1,2,84,3,4,157,5],[20,49,500,501,1125,1126,1459,1546,1547,1736,1993,2305],[0]),([112,0,1,2,84,3,4,5],[21,94,125,126,139,812,1125,1130,1458,1475,1546,1547,1688,1712,2306],[0]),([83,0,1,2,3,4,5],[21,24,73,93,98,104,125,167,493,496,1281],[0]),([33,0,1,2,3,4,5],[20,21,24,93,116,125,126,1427,1428,1511,2126],[0]),([0,1,6,2,3,4,5,20],[14,20,49,103,116,171,306,307,643,799,912,1260],[0]),([214,0,1,2,3,4,16,5],[49,234,235,844,883,1301,1302,2307,2308,2309],[0]),([95,0,1,2,3,4,5],[20,21,93,125,139,240,1125,1126,2125,2310,2311,2312],[0]),([0,1,2,3,4,16,82,5],[49,73,883,904,1094,1301,2125,2313,2314,2315],[0]),([0,1,2,3,4,5,66],[20,21,73,135,139,1027,1313,1316,1662],[0]),([0,1,2,3,4,16,157,5],[20,21,49,93,1736,1738,2316,2317],[0]),([0,1,2,84,3,4,5,20],[14,20,49,103,139,306,307,315,799,867,1125,1126,1546,1547,2318],[0]),([0,1,2,3,4,82,5],[21,49,93,104,125,148,167,210,1177,1349,1480],[0]),([0,1,2,3,4,5,262],[20,94,167,1178,1718,2125,2126,2319,2320,2321,2322],[0]),([0,1,2,3,4,38,82,5],[49,98,100,472,479,510,513,1281,2126],[0]),([369,0,1,2,3,4,5],[93,94,104,125,126,240,2125,2126,2323,2324,2325],[]),([220,0,1,6,2,3,4,5],[20,49,104,116,125,152,167,172,240,1260,1359,1411,2232,2233],[0]),([25,0,1,2,3,4,5,7],[21,73,93,110,122,438,441,491,1164,1271,1725,2326],[0]),([133,0,1,6,2,3,4,5],[20,104,116,125,152,171,240,581,593,1260,1294,1561,2253,2254],[0]),([133,57,0,1,2,3,4,5],[20,73,93,94,139,537,742,743,1561,2253,2254],[0]),([0,1,2,3,4,98,5],[21,49,104,1977,2327,2328,2329,2330],[0]),([112,109,0,1,2,3,4,5],[20,21,94,167,217,812,813,1063,1064,1130,1486,1688,2331,2332,2333,2334],[0]),([91,0,1,2,3,4,94,5],[20,21,49,93,125,167,180,430,498,499,1039,1085,1086,2234,2236,2335,2336],[]),([258,0,1,2,3,4,5,20],[14,20,49,94,306,307,643,867,1984],[0]),([0,1,2,13,3,4,16,5],[20,49,234,235,367,372,730,844,1094,1301,2125,2337,2338],[0]),([0,1,2,3,4,16,5,50],[49,235,834,839,904,1278,1839],[0]),([168,0,1,2,19,3,4,5],[14,24,147,148,239,938,962,1157,1440,1442,1582],[0]),([133,0,1,2,3,4,5,242],[94,125,167,589,1057,1294,1561,2208,2210,2212,2254,2339,2340],[0]),([0,1,2,19,3,4,5,66],[24,73,135,139,147,1027,1313,1316,1867],[0]),([0,1,3,4,310,5],[20,94,139,1658,1659],[0]),([0,1,182,2,3,4,5],[20,21,23,73,104,125,167,706,1594,1895,2341],[0]),([104,0,1,2,3,4,5],[20,21,24,93,125,126,135,139,146,167,929,981,1067,2342],[0]),([0,1,166,2,3,4,5],[20,24,89,94,104,125,167,1208,2343,2344,2345],[0]),([137,0,1,6,2,3,4,5],[21,49,93,125,152,167,172,240,1062,1088,1260,2127,2215,2216],[0]),([0,1,2,19,76,3,4,5],[21,73,93,147,148,181,623,1068,1118,1144,1235,1238,2346],[0]),([0,1,2,19,3,4,157,5],[20,24,49,135,146,147,148,487,500,938,1736,1738,1993,2347],[0]),([133,220,0,1,2,3],[20,94,104,139,1527,1528],[0]),([91,0,1,2,3,4,16,5],[20,49,93,267,904,1039,1301,1302,2348],[0]),([91,0,1,2,19,3,4,5],[20,21,24,49,73,126,146,147,148,239,267,430,495,938,1039,1157,1861,2349],[0]),([52,0,1,2,3,4,38,5],[20,49,75,98,101,104,126,139,449,472,473,1148,1919,2221],[0]),([0,1,2,19,3,4,5,20],[14,20,24,49,103,135,139,146,147,148,306,315,643,799,867,912,2350],[0]),([0,1,2,3,4,5,20],[14,20,49,94,139,167,300,1677],[0]),([0,1,169,2,3,4,5],[20,21,49,73,93,104,125,167,439,658,669,2351],[0]),([89,0,1,2,3,4,5],[21,49,73,93,104,125,126,167,1285,1398,1925,2352],[0]),([133,0,1,2,19,3,4,5],[24,73,135,139,147,148,239,581,593,938,1157,1294,2059,2253,2353],[0]),([227,0,1,2,3,4,16,5],[21,73,235,883,1301,1302,2354,2355,2356],[0]),([0,1,2,3,4,16,5,20],[20,49,103,104,799,867,883,904,910,912,967],[0]),([147,0,1,2,19,3,4,5],[24,73,135,239,938,1157,1625,1861,1901,2132,2357],[0]),([236,0,1,2,3,4,5],[20,73,93,94,104,125,167,2294,2358,2359,2360],[0]),([53,0,1,2,3,4,5,20],[14,20,49,139,306,307,315,643,912,1353,2048],[0]),([0,1,2,3,228,4,38,5],[49,75,98,101,473,479,1281,2293,2294,2361],[0]),([0,1,2,3,4,38,5,39],[73,75,100,139,453,458,1416,1419],[0]),([229,0,1,2,3,4,5],[14,49,93,94,104,125,126,167,1683,2362,2363,2364],[0]),([280,0,1,2,3,4,5],[21,49,93,125,126,240,1057,1178,1396,2125,2126,2365,2366,2367],[0]),([0,1,2,308,3,4,5],[20,21,24,73,89,104,125,167,1564,1909,2368,2369],[0]),([0,1,2,76,157,5],[20,93,94,818,1467,1468,1860],[0]),([97,0,1,2,3,4,38,5],[20,49,73,98,100,101,126,472,473,479,936,1105,1281,1564,2370],[0]),([0,1,2,3,186,4,16,5],[49,73,235,883,1094,1302,2164,2166,2371,2372],[0]),([117,97,0,1,2,3,4,5],[20,252,435,436,658,669,1105,1423,1424,1564,1610,2034,2373],[0]),([0,1,154,2,3,4,5],[14,21,24,93,104,125,126,167,267,398,1039,1891],[0]),([0,1,2,122,3,4,16,5],[73,93,235,844,904,1837,2072,2374,2375],[0]),([97,0,1,2,4,5,7],[21,93,94,104,491,936,1164,2008,2010],[0]),([0,2,3,4,16,5,63],[20,24,49,104,235,571,1813,1816,2125],[0]),([0,1,2,3,16,5,20],[20,49,104,235,867,910,912,967],[0]),([147,0,1,2,84,3,4,5],[93,125,126,167,1125,1126,1458,1459,1547,1624,1900,2105,2132,2304,2376],[]),([25,0,1,2,3,186,4,5],[21,93,110,728,758,1725,2164,2371,2377,2378,2379],[0]),([57,0,1,2,3,4,16,5],[20,21,49,73,537,706,883,904,1094,1301,1302,1594,2380,2381],[0]),([0,1,2,3,41,20],[94,139,320,325],[0]),([0,2,3,4,211,5],[20,94,139,785,2382],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_9_0 : checkNodesBT W_24 g_24 F_24 P_24_9 A_24 B_24_8 9 N_24_9_0 = true := by decide +kernel
def N_24_9_1 : List NodeSpec := [([0,2,3,14,4,5],[94,139,369,1115,2383],[0]),([0,1,2,3,4,16,38,5],[20,49,98,100,479,883,904,1094,1281,2384],[0]),([81,0,1,2,3,4,5],[21,49,73,93,104,125,167,1094,1253,1254,2286],[0]),([1,2,3,370,4,5],[94,2125,2126,2385,2386],[]),([0,1,2,3,4,264,5],[21,49,104,1984,2125,2126,2387,2388,2389,2390],[0]),([0,1,2,3,4,16,123,5],[21,49,883,2391,2392,2393,2394],[0]),([0,1,6,2,3,4,5,7],[104,116,122,152,438,441,491,1166,1260],[0]),([163,0,1,2,3,4,16,5],[20,49,235,844,883,1094,1301,2125,2343,2395,2396],[0]),([0,1,3,4,38,5,23],[49,73,75,139,753,1009,1012,2126],[0]),([0,1,2,3,4,16,5,7],[21,49,73,235,441,491,1164,1272,2397],[0]),([112,0,1,2,3,4,16,5],[49,235,815,904,1094,1130,1301,1302,1476,1688,2398],[0]),([0,1,2,3,161,4,5],[20,21,24,104,677,1118,1238,1257],[0]),([220,0,1,2,3,4,16,5],[20,49,234,235,844,883,1301,1302,1359,2233,2399],[0]),([137,0,1,2,3,4,16,5],[20,49,234,883,1301,1302,2127,2215,2400],[0]),([137,25,0,1,2,3,4,5],[93,114,728,757,758,1088,2127,2215,2216],[0]),([0,1,2,3,4,38,5,7],[49,101,139,441,479,481,1166,1271,2401],[0]),([133,0,1,2,3,16,5],[20,49,73,235,240,589,593,2402,2403],[0]),([117,0,1,2,3,4,5,7],[21,93,122,139,434,438,441,491,658,1166,1271,2404],[0]),([25,0,1,2,3,4,5,23],[110,114,753,760,795,798,989,1100,1725,2137,2138,2405],[0]),([0,1,2,3,4,114,16,5],[20,49,234,235,844,873,1094,1301,1869,1872,2125,2406,2407],[0]),([0,1,2,3,4,5,50],[21,49,235,834,839,1278,1839,2092],[0]),([0,1,277,2,3,4,5],[24,94,104,125,126,139,167,1156,1359,2408,2409],[0]),([127,0,1,2,3,4,16,5],[20,49,73,104,240,808,862,883,904,1094,1301,1302,2079,2298,2299],[0]),([0,1,2,3,4,5,39],[21,49,73,75,139,453,458,1416,1419,1421],[0]),([274,0,1,2,3,4,5],[21,49,93,104,125,240,1126,1547,2125,2410,2411,2412],[0]),([0,1,2,210,3,4,5],[20,21,24,73,93,104,125,167,779,1723,1725,2413],[0]),([0,1,2,3,4,164,5],[14,49,94,419,737,2414,2415,2416],[0]),([89,0,1,2,19,3,4,5],[20,49,73,146,147,148,239,938,1068,1157,1285,1398,1925],[0]),([57,25,0,1,2,3,4,5],[20,93,537,706,742,743,757,758,760,767,1594,1725,2381,2417],[0]),([163,25,0,1,2,3,4,5],[104,110,728,737,757,767,1725,2125,2343,2396,2418],[0]),([25,0,1,2,3,5,20],[14,20,103,104,110,114,716,754,867,912],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_9_1 : checkNodesBT W_24 g_24 F_24 P_24_9 A_24 B_24_8 9 N_24_9_1 = true := by decide +kernel
def N_24_9 := N_24_9_0 ++ N_24_9_1
def B_24_9 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_9
set_option maxRecDepth 500000 in
lemma B_24_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 9 xs.toFinset) B_24_9 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_24) (raw := r_24) (pspecs := ps_24) (used := [14,20,21,23,24,41,48,49,64,73,75,89,93,94,98,100,101,103,104,110,114,116,122,125,126,135,139,146,147,148,152,167,171,172,180,181,210,217,220,234,235,239,240,252,257,267,300,305,306,307,312,314,315,317,320,325,330,342,345,367,369,372,376,379,381,387,398,402,407,419,426,430,433,434,435,436,438,439,441,449,453,458,462,472,473,474,475,479,480,481,487,491,493,495,496,498,499,500,501,510,512,513,517,518,519,520,521,526,529,537,543,552,554,558,559,565,571,580,581,586,589,592,593,598,599,603,605,607,614,615,623,624,625,628,631,643,648,649,652,657,658,669,671,677,700,704,706,716,718,722,723,727,728,730,731,737,741,742,743,753,754,756,757,758,760,767,769,773,775,779,785,795,798,799,808,812,813,815,816,818,821,834,839,844,862,867,873,883,904,910,912,920,922,929,936,938,955,962,963,965,967,970,981,987,989,990,992,993,996,998,999,1001,1009,1012,1014,1027,1035,1039,1047,1049,1057,1060,1062,1063,1064,1067,1068,1069,1071,1075,1076,1078,1079,1080,1085,1086,1088,1092,1094,1098,1100,1105,1115,1118,1123,1124,1125,1126,1127,1130,1134,1137,1144,1148,1156,1157,1164,1166,1177,1178,1205,1206,1208,1235,1236,1238,1250,1253,1254,1257,1260,1271,1272,1278,1281,1285,1290,1294,1301,1302,1313,1316,1329,1338,1349,1352,1353,1359,1382,1383,1396,1398,1400,1401,1405,1411,1416,1419,1421,1423,1424,1427,1428,1440,1442,1456,1458,1459,1460,1463,1467,1468,1472,1475,1476,1480,1486,1499,1511,1527,1528,1539,1546,1547,1548,1561,1564,1571,1582,1594,1596,1604,1605,1608,1610,1624,1625,1629,1638,1650,1658,1659,1662,1666,1667,1677,1683,1688,1712,1713,1718,1723,1725,1726,1736,1738,1740,1746,1755,1758,1760,1812,1813,1816,1837,1839,1855,1860,1861,1867,1869,1872,1874,1891,1893,1895,1900,1901,1909,1912,1919,1925,1971,1977,1984,1986,1993,2008,2010,2027,2031,2033,2034,2048,2056,2059,2060,2072,2079,2092,2105,2119,2120,2121,2122,2123,2124,2125,2126,2127,2128,2129,2130,2131,2132,2133,2134,2135,2136,2137,2138,2139,2140,2141,2142,2143,2144,2145,2146,2147,2148,2149,2150,2151,2152,2153,2154,2155,2156,2157,2158,2159,2160,2161,2162,2163,2164,2165,2166,2167,2168,2169,2170,2171,2172,2173,2174,2175,2176,2177,2178,2179,2180,2181,2182,2183,2184,2185,2186,2187,2188,2189,2190,2191,2192,2193,2194,2195,2196,2197,2198,2199,2200,2201,2202,2203,2204,2205,2206,2207,2208,2209,2210,2211,2212,2213,2214,2215,2216,2217,2218,2219,2220,2221,2222,2223,2224,2225,2226,2227,2228,2229,2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2249,2250,2251,2252,2253,2254,2255,2256,2257,2258,2259,2260,2261,2262,2263,2264,2265,2266,2267,2268,2269,2270,2271,2272,2273,2274,2275,2276,2277,2278,2279,2280,2281,2282,2283,2284,2285,2286,2287,2288,2289,2290,2291,2292,2293,2294,2295,2296,2297,2298,2299,2300,2301,2302,2303,2304,2305,2306,2307,2308,2309,2310,2311,2312,2313,2314,2315,2316,2317,2318,2319,2320,2321,2322,2323,2324,2325,2326,2327,2328,2329,2330,2331,2332,2333,2334,2335,2336,2337,2338,2339,2340,2341,2342,2343,2344,2345,2346,2347,2348,2349,2350,2351,2352,2353,2354,2355,2356,2357,2358,2359,2360,2361,2362,2363,2364,2365,2366,2367,2368,2369,2370,2371,2372,2373,2374,2375,2376,2377,2378,2379,2380,2381,2382,2383,2384,2385,2386,2387,2388,2389,2390,2391,2392,2393,2394,2395,2396,2397,2398,2399,2400,2401,2402,2403,2404,2405,2406,2407,2408,2409,2410,2411,2412,2413,2414,2415,2416,2417,2418]) S_24_ok
  have hm0 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_8_ok C_24_9_0
  have hm1 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_8_ok C_24_9_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def P_24_10 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 [20,21,93,94,98,104,125,126,139,167,181,240,267,306,315,367,436,438,472,491,495,498,500,558,593,658,743,757,795,812,815,818,912,989,1094,1157,1235,1238,1271,1301,1359,1423,1458,1475,1539,1564,1594,1725,1738,1855,1901,1993,2059,2125,2126,2127,2132,2208,2210,2216,2226,2232,2234,2236,2254,2265,2290,2294,2304,2343,2371,2377,2418,2419,2420,2421]
def N_24_10 : List NodeSpec := [([133,0,1,2,3,4,5],[20,21,93,94,125,126,139,167,240,593,2059,2254],[0]),([0,1,2,3,4,5,20],[20,21,94,139,167,306,315,912],[0]),([0,1,2,3,41,4,5],[20,94,125,126,139,167,240,1539,2265],[0]),([97,0,1,2,3,4,5],[20,21,93,94,104,125,126,167,240,1423,1564,2125],[0]),([0,1,2,3,4,5,242],[20,21,94,125,167,2125,2126,2208,2210],[0]),([0,1,2,13,3,4,5],[20,93,94,125,126,139,167,240,367,2226],[0]),([0,1,2,3,228,4,5],[20,93,94,240,2125,2290,2294],[0]),([57,0,1,2,3,4,5],[20,21,104,125,126,139,167,240,743,1594,2126],[0]),([0,1,2,76,3,4,5],[20,21,93,94,167,181,1235,1238],[0]),([109,0,1,2,3,4,5],[20,21,93,104,125,167,2125,2126],[0]),([0,1,2,3,4,94,5],[20,21,93,104,125,167,2125,2126,2234,2236],[0]),([258,0,1,2,3,4,5],[20,21,94,104,125,167,2125,2126],[0]),([363,0,1,2,3,4,5],[20,93,94,125,126,167,2125,2126],[0]),([0,1,2,3,4,16,5],[20,21,93,104,240,1094,1301,2125],[0]),([91,0,1,2,3,4,5],[20,21,93,94,104,125,126,167,240,267,495,498,818],[0]),([220,0,1,2,3,4,5],[20,93,94,104,125,139,167,240,1359,2232],[0]),([0,1,2,3,368,4,5],[20,93,94,104,125,167,2125,2126,2419,2420],[0]),([147,0,1,2,3,4,5],[20,93,94,125,126,167,240,818,1901,2132,2304],[0]),([0,1,6,2,3,4,5],[20,21,93,104,125,167,240,2126],[0]),([117,0,1,2,3,4,5],[20,21,93,104,125,126,139,167,240,436,658,2126],[0]),([0,1,2,3,4,5,63],[20,21,94,139,240,558,1855,2125],[0]),([362,0,1,2,3,4,5],[20,93,94,104,125,139,167,240,2125,2421],[0]),([0,1,2,3,186,4,5],[20,93,94,126,2126,2371,2377],[0]),([0,1,2,84,3,4,5],[20,21,93,104,125,126,139,167,1458,2125],[0]),([0,1,2,3,4,38,5],[20,21,93,98,126,139,472,2126],[0]),([0,1,2,19,3,4,5],[20,21,93,104,125,126,139,240,1157,2125,2126],[0]),([0,1,2,3,4,5,23],[20,21,94,126,139,795,989,2126],[0]),([0,1,2,3,4,157,5],[20,21,93,94,167,500,1738,1993],[0]),([163,0,1,2,3,4,5],[20,93,94,104,125,126,167,240,2126,2343,2418],[0]),([25,0,1,2,3,4,5],[20,21,93,104,125,126,167,240,757,1725,2125],[0]),([0,1,2,3,4,5,7],[20,93,94,167,438,491,1271],[0]),([112,0,1,2,3,4,5],[21,94,125,167,240,812,815,1475],[0]),([137,0,1,2,3,4,5],[20,93,125,139,167,240,2127,2216],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_10 : checkNodesBT W_24 g_24 F_24 P_24_10 A_24 B_24_9 10 N_24_10 = true := by decide +kernel
def B_24_10 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_10
set_option maxRecDepth 500000 in
lemma B_24_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 10 xs.toFinset) B_24_10 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_9_ok C_24_10
def P_24_11 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 [125,126,240]
def N_24_11 : List NodeSpec := [([0,1,2,3,4,5],[125,126,240],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_11 : checkNodesBT W_24 g_24 F_24 P_24_11 A_24 B_24_10 11 N_24_11 = true := by decide +kernel
def B_24_11 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_11
set_option maxRecDepth 500000 in
lemma B_24_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 11 xs.toFinset) B_24_11 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_10_ok C_24_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_24_ok : forestRootCheck r_24 g_24 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,3,19),(VAR 5,2,34)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_24_in : bucketContainsBT B_24_11 r_24 = true := by decide +kernel
lemma low_24 : Lower r_24 g_24 12 := lower_of_forestBT root_24_ok B_24_11_ok root_24_in

def g_orig := 0xfefefee8feeaeca8fefefee8feeaeca8fefefee8feeaeca8fefefee8feeaeca8
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,4),(2,3)]) (by decide +kernel) low_24
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124264 * 2 ^ 32 + 4276808872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.and,[0,2]⟩,⟨.or,[2,0]⟩,⟨.or,[5,0]⟩,⟨.or,[1,6]⟩,⟨.and,[4,8]⟩,⟨.or,[5,4]⟩,⟨.or,[10,3]⟩,⟨.and,[11,7]⟩,⟨.or,[12,0]⟩,⟨.or,[14,13]⟩,⟨.and,[12,13]⟩,⟨.and,[15,9]⟩,⟨.or,[17,16]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_44988

open PEqualNP.Outside.L_meta_44988 in
theorem PEqualNP.Outside.L_meta_44988 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124264 * 2 ^ 32 + 4276808872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124264 * 2 ^ 32 + 4276808872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
