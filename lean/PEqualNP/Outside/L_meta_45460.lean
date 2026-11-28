import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45460
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
def g_2 := (d 0xe880e880e880e880)
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
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_1 : Slice r_2 g_2 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_2 : Slice r_2 g_2 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_3 : Slice r_2 g_2 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
def S_2 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4)]
lemma S_2_ok : btAll (fun o => ∀ p, o = some p → Slice r_2 g_2 p.1 p.2) S_2 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_2_0) (forall_cons (fun _ h => by cases h; exact sl_2_1) (forall_cons (fun _ h => by cases h; exact sl_2_2) (forall_cons (fun _ h => by cases h; exact sl_2_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_2 : BT (Option PoolSpec) := btOfList 2 [q 1 [],q 0 [],q 2 [],q 3 []]
def B_2_2 : BT (List (List Nat)) := BT.empty
lemma B_2_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 2 xs.toFinset) B_2_2 := .empty
def U_2_3 : List Nat := [0,1]
def P_2_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_3
def N_2_3 : List NodeSpec := [([4,5,6,3],[0,1],[]),([8,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_3 : checkNodesBT W_2 g_2 F_2 P_2_3 A_2 B_2_2 3 N_2_3 = true := by decide +kernel
def B_2_3 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_3
set_option maxRecDepth 500000 in
lemma B_2_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 3 xs.toFinset) B_2_3 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_2_ok C_2_3
def U_2_4 : List Nat := [0,2,3]
def P_2_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_4
def N_2_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([10,0,1,2,3],[],[]),([11,0,1,2,3],[3],[9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_4 : checkNodesBT W_2 g_2 F_2 P_2_4 A_2 B_2_3 4 N_2_4 = true := by decide +kernel
def B_2_4 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_4
set_option maxRecDepth 500000 in
lemma B_2_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 4 xs.toFinset) B_2_4 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_3_ok C_2_4
def U_2_5 : List Nat := (r 0 4)
def P_2_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_5
def N_2_5 : List NodeSpec := [([4,0,1,2,3],(r 0 4),[0,1,4,5,8,10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_5 : checkNodesBT W_2 g_2 F_2 P_2_5 A_2 B_2_4 5 N_2_5 = true := by decide +kernel
def B_2_5 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_5
set_option maxRecDepth 500000 in
lemma B_2_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 5 xs.toFinset) B_2_5 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_4_ok C_2_5
def U_2_6 : List Nat := (r 0 4)
def P_2_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_6
def N_2_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,3,6,7,8])]
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
def g_3 := (d 0xffe8ffe8ffe8ffe8)
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_4 := (d 0xf880f880f880f880)
def r_4 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_4 : Lower r_4 g_4 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_5 := (d 0xffe8e880ffe8e880)
def r_5 : List Nat := varsOf 31
def p_5 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,19,19,19,21,21,21,22,22,22,24,24,25,25,26,26,28,28]
def q_5 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,18,17,3,20,17,5,20,18,6,16,8,17,9,18,10,20,12]
def F_5 : Nat := fullMask 29
set_option maxHeartbeats 0 in
lemma gp_5 : goodPairs g_5 p_5 q_5 := goodPairs_of (by decide +kernel)
def W_5 : BT Decor := buildWiresBT 6 (mkBase p_5 q_5 r_5) [(0,1,2),(1,5,3),(1,6,4),(3,5,7),(0,0,1),(0,0,2),(1,3,4),(0,0,11),(0,1,11),(0,5,11),(3,14,0),(1,9,3),(1,9,4),(0,9,2),(3,18,11),(1,18,4),(3,5,0),(0,2,11),(3,22,0),(2,16,4),(1,16,4),(2,2,4),(1,26,3),(0,9,11),(2,9,4),(2,0,4),(1,30,3),(2,30,3),(2,0,3),(2,2,3),(3,34,0),(2,1,3)]
lemma W_5_ok : btAll (fun x => faithful p_5 q_5 x ∧ x.1 < 2^256) W_5 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_5 : List (List (Nat × Nat)) := [[],[(3,4)],[(1,2)],[(0,1)],[(0,1),(3,4)],[(0,2),(1,2)],[(0,2),(1,2),(3,4)],[(0,1),(1,2)],[(0,1),(1,2),(3,4)],[(0,2)],[(0,2),(3,4)]]
def A_5 : BT (List (Nat × Nat)) := btOfList 4 al_5
set_option maxHeartbeats 0 in
lemma A_5_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_5 = g_5) A_5 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_5_0 : Slice r_5 g_5 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_1 : Slice r_5 g_5 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_2 : Slice r_5 g_5 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_5_3 : Slice r_5 g_5 (subcubeFast 0 4) 7 := by
  have hc : Lower (varsOf 27) (d 0xffeeee88ffeeee88) 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_4 : Slice r_5 g_5 (subcubeFast 8 0) 7 := by
  have hc : Lower (varsOf 23) (d 0xe8e88080e8e88080) 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_5 : Slice r_5 g_5 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_5_6 : Slice r_5 g_5 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_7 : Slice r_5 g_5 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_8 : Slice r_5 g_5 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xff888800ff888800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_9 : Slice r_5 g_5 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xffa0a000ffa0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_10 : Slice r_5 g_5 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_5_11 : Slice r_5 g_5 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_5_12 : Slice r_5 g_5 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_13 : Slice r_5 g_5 (subcubeFast 4 2) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_14 : Slice r_5 g_5 (subcubeFast 2 4) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_15 : Slice r_5 g_5 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_16 : Slice r_5 g_5 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_17 : Slice r_5 g_5 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_18 : Slice r_5 g_5 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
def S_5 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 1,7),some (subcubeFast 0 2,7),some (subcubeFast 16 0,7),some (subcubeFast 0 4,7),some (subcubeFast 8 0,7),some (subcubeFast 0 16,5),some (subcubeFast 1 0,5),some (subcubeFast 0 8,5),some (subcubeFast 4 0,5),some (subcubeFast 2 0,5),some (subcubeFast 16 8,4),some (subcubeFast 8 16,4),some (subcubeFast 8 2,4),some (subcubeFast 4 2,4),some (subcubeFast 2 4,4),some (subcubeFast 16 1,4),some (subcubeFast 4 1,4),some (subcubeFast 1 4,4),some (subcubeFast 1 2,4)]
lemma S_5_ok : btAll (fun o => ∀ p, o = some p → Slice r_5 g_5 p.1 p.2) S_5 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_5_0) (forall_cons (fun _ h => by cases h; exact sl_5_1) (forall_cons (fun _ h => by cases h; exact sl_5_2) (forall_cons (fun _ h => by cases h; exact sl_5_3) (forall_cons (fun _ h => by cases h; exact sl_5_4) (forall_cons (fun _ h => by cases h; exact sl_5_5) (forall_cons (fun _ h => by cases h; exact sl_5_6) (forall_cons (fun _ h => by cases h; exact sl_5_7) (forall_cons (fun _ h => by cases h; exact sl_5_8) (forall_cons (fun _ h => by cases h; exact sl_5_9) (forall_cons (fun _ h => by cases h; exact sl_5_10) (forall_cons (fun _ h => by cases h; exact sl_5_11) (forall_cons (fun _ h => by cases h; exact sl_5_12) (forall_cons (fun _ h => by cases h; exact sl_5_13) (forall_cons (fun _ h => by cases h; exact sl_5_14) (forall_cons (fun _ h => by cases h; exact sl_5_15) (forall_cons (fun _ h => by cases h; exact sl_5_16) (forall_cons (fun _ h => by cases h; exact sl_5_17) (forall_cons (fun _ h => by cases h; exact sl_5_18) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))
def ps_5 : BT (Option PoolSpec) := btOfList 7 [q 1 [16397],q 0 [16397],q 7 [],q 5 [],q 2 [4096,45056,45060],q 2 [8196,45076,59],q 0 [],q 6 [8196],q 8 [4096],q 2 [4096,8192,8196],q 0 [12325,16421,16397],q 6 [],q 9 [],q 2 [4096,12325],q 2 [4096,8228,45131],q 1 [16397,45056],q 2 [4096,45056],q 0 [8228,16457],q 1 [8228,16457],q 3 [4096,16457],q 4 [4096,8228,16457],q 2 [8196,45079],q 4 [],q 8 [],q 16 [],q 1 [23],q 3 [23],q 2 [8196,23],q 0 [16397,45060],q 1 [],q 2 [45056,45060],q 3 [],q 0 [16397,45064],q 2 [45064,91],q 0 [12325,16450],q 0 [12325,16421],q 4 [4096],q 2 [4096],q 2 [],q 0 [8228],q 1 [8228],q 3 [4096],q 2 [4096,8228],q 4 [4096,16421],q 0 [16421,12305],q 0 [12325,16449],q 13 [],q 0 [8196],q 1 [8192],q 4 [4096,8192,8196],q 1 [16397,45079],q 3 [16397,45079],q 3 [16397],q 9 [8192],q 2 [4096,8192],q 3 [12393],q 4 [16394],q 11 [],q 0 [16394,12393],q 2 [4096,45092],q 4 [45056],q 3 [16397,45056],q 17 [],q 2 [45056],q 4 [4096,8228],q 4 [8196,23],q 0 [12325],q 1 [12325],q 3 [4096,12325],q 10 [],q 14 [],q 0 [16422],q 1 [16422],q 4 [4096,16422],q 3 [4096,16422],q 4 [4096,8192],q 0 [12409],q 1 [16386,12409],q 3 [16386,12409],q 4 [16386],q 2 [12409],q 0 [12410],q 2 [8196],q 15 [],q 1 [16386],q 4 [8196],q 2 [12290],q 5 [12290],q 1 [16386,12290],q 0 [12298],q 3 [139],q 4 [139],q 2 [12298,139],q 1 [12298,139],q 18 [],q 12 [],q 0 [12294],q 3 [12294],q 3 [16386]]
def B_5_3 : BT (List (List Nat)) := BT.empty
lemma B_5_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 3 xs.toFinset) B_5_3 := .empty
def U_5_4 : List Nat := []
def P_5_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_4
def N_5_4 : List NodeSpec := [([8,9,10,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_4 : checkNodesBT W_5 g_5 F_5 P_5_4 A_5 B_5_3 4 N_5_4 = true := by decide +kernel
def B_5_4 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_4
set_option maxRecDepth 500000 in
lemma B_5_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 4 xs.toFinset) B_5_4 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_3_ok C_5_4
def U_5_5 : List Nat := (r 0 15)
def P_5_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_5
def N_5_5 : List NodeSpec := [([9,12,13,2,3,4],(r 0 5),[]),([15,1,2,3,4,11],[5],[]),([8,9,0,2,3,4],[6],[0]),([9,10,5,3,4,11],[0,1,7,8,9],[0,3,7]),e5 [8] [],([0,1,2,16,17,11],(r 10 4),[]),e5 [19] [14]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_5 : checkNodesBT W_5 g_5 F_5 P_5_5 A_5 B_5_4 5 N_5_5 = true := by decide +kernel
def B_5_5 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_5
set_option maxRecDepth 500000 in
lemma B_5_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 5 xs.toFinset) B_5_5 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_4_ok C_5_5
def U_5_6 : List Nat := ([0,2,3]++r 6 4++[11,12,13]++r 15 45)
def P_5_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_6
def N_5_6 : List NodeSpec := [([9,12,1,2,3,4,11],[0,2,3,6,15,16],[0]),([0,1,2,3,20],([3]++r 17 4),[]),e5 [8,11] [21,22,23],e5 [21,11] ([3,11,12]++r 24 4),u5 [12,13] [0,11,12,28,29,30],e5 [23,11] [6,11,31,32,33],e5 [24,9] [3,13,22,34],u5 [16,17] [2,3,35,36,37],u5 [18,11] ([2,3,11,12,22,23]++r 38 5),([9,0,1,2,3,17,11],[11,12,38,43,44],[0]),a5 [9,25] [29,41,45,46] [7],([9,10,5,3,4],[7,8,9,29,31,41,47,48,49],[0]),a5 [8] [6,11,21,22,31,50,51] [0,2],e5 [8,5] [3,29,31,50],([9,10,1,2,3,4,11],[0,8,11,41,48,52,53,54],[0,3,7]),e5 [9,27] ([2,11,23]++r 55 4),a5 [28,11] [22,38,52,59] [7]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_6 : checkNodesBT W_5 g_5 F_5 P_5_6 A_5 B_5_5 6 N_5_6 = true := by decide +kernel
def B_5_6 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_6
set_option maxRecDepth 500000 in
lemma B_5_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 6 xs.toFinset) B_5_6 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_5_ok C_5_6
def U_5_7 : List Nat := (r 0 4++[6,11,12,13,15]++r 22 6++[29,31,36,37,38,40,41,42,46,47,48,52,54,57]++r 60 39)
def P_5_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_7
def N_5_7 : List NodeSpec := [a5 [12,11] [0,1,3,15,38,52,60,61] [0,2,5,9],e5 [12] [1,3,11,12,23,29,31,60,62,63],a5 [18] [2,3,11,22,38,40,41,42,64] [0,1],u5 [21] [2,3,6,11,22,25,26,27,38,47,65],a5 [9,11] (r 0 4++[11,12,22,36,37,38,41,46,52]) [0,1,3,7],e5 [16] ([2,13,23,36]++r 66 4),a5 [9,16] [11,13,36,66,67,68,70] [0,1],e5 [29] ([2,3,22,23,31,57]++r 71 4),([9,10,1,2,3,4],[6,11,31,41,48,54,75],[0]),a5 [31] ([2,12,23]++r 76 5) [5],e5 [32] [3,12,23,29,31,62,79,81],a5 [30,5] ([3,23,24,62,69,79]++r 82 4) [5],([30,33,1,2,3,4],[11,22,62,79,86,87,88],[]),e5 [35] ([3,6,11,12,29,38]++r 89 6),e5 [30,36] ([2,3,24,46,57,69,84]++r 95 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_7 : checkNodesBT W_5 g_5 F_5 P_5_7 A_5 B_5_6 7 N_5_7 = true := by decide +kernel
def B_5_7 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_7
set_option maxRecDepth 500000 in
lemma B_5_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 7 xs.toFinset) B_5_7 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_6_ok C_5_7
def U_5_8 : List Nat := [0,1,3,6,11,22,29,31,36,37,38,41,52,70,79,83,84,98]
def P_5_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_8
def N_5_8 : List NodeSpec := [a5 [30] [3,6,22,29,31,38,79,83,84,98] [0,2,6,10],a5 [11] [0,1,3,22,38,52] [0,2,3,5,7],a5 [9] [6,11,22,29,31,36,37,38,41,70] [0,1,3,7,8]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_8 : checkNodesBT W_5 g_5 F_5 P_5_8 A_5 B_5_7 8 N_5_8 = true := by decide +kernel
def B_5_8 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_8
set_option maxRecDepth 500000 in
lemma B_5_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 8 xs.toFinset) B_5_8 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_7_ok C_5_8
def U_5_9 : List Nat := [6,22,29,31,38]
def P_5_9 : BT (Option BoundPool) := buildPoolsSubBT 7 W_5 r_5 S_5 ps_5 U_5_9
def N_5_9 : List NodeSpec := [a5 [] [6,22,29,31,38] [0,1,2,3,4,5,7,8]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_9 : checkNodesBT W_5 g_5 F_5 P_5_9 A_5 B_5_8 9 N_5_9 = true := by decide +kernel
def B_5_9 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_9
set_option maxRecDepth 500000 in
lemma B_5_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 9 xs.toFinset) B_5_9 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_8_ok C_5_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_5_ok : forestRootCheck r_5 g_5 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_5_in : bucketContainsBT B_5_9 r_5 = true := by decide +kernel
lemma low_5 : Lower r_5 g_5 10 := lower_of_forestBT root_5_ok B_5_9_ok root_5_in
def g_6 := (d 0xfffcfc80fffcfc80)
def r_6 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_6 : Lower r_6 g_6 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_7 := (d 0xfee0c000fee0c000)
def r_7 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_7 : Lower r_7 g_7 8 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,20,21)]) (by decide +kernel) hc
def g_8 := (d 0xfffefec0fffefec0)
def r_8 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_9 := (d 0xfef8e800fef8e800)
def r_9 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_9 : Lower r_9 g_9 8 := by
  have hc : Lower (varsOf 27) (d 0xee888800ee888800) 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 4) (o := 0) (essPairs := [(VAR 2,9,13)]) (by decide +kernel) hc
def g_10 := (d 0xfe80fe80fe80fe80)
def r_10 : List Nat := varsOf 15
def p_10 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14]
def q_10 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6]
def F_10 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_10 : goodPairs g_10 p_10 q_10 := goodPairs_of (by decide +kernel)
def W_10 : BT Decor := buildWiresBT 5 (mkBase p_10 q_10 r_10) [(0,2,3),(1,2,3),(3,4,5),(0,1,2),(1,1,2),(3,7,8),(2,0,3),(3,0,3),(1,0,3),(3,2,12),(1,1,3),(0,0,14),(0,0,3),(1,16,2),(3,4,0),(2,0,2),(3,0,2),(2,2,1),(3,21,0),(2,0,1),(1,23,2),(0,0,1),(1,0,1),(3,2,3)]
lemma W_10_ok : btAll (fun x => faithful p_10 q_10 x ∧ x.1 < 2^256) W_10 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_10 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_10 : BT (List (Nat × Nat)) := btOfList 3 al_10
set_option maxHeartbeats 0 in
lemma A_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_10 = g_10) A_10 := btAll_ofList (autos_of (by decide +kernel))
def S_10 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_10_ok : btAll (fun o => ∀ p, o = some p → Slice r_10 g_10 p.1 p.2) S_10 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_10 : BT (Option PoolSpec) := btOfList 1 []
def B_10_1 : BT (List (List Nat)) := BT.empty
lemma B_10_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 1 xs.toFinset) B_10_1 := .empty
def U_10_2 : List Nat := []
def P_10_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_10 r_10 S_10 ps_10 U_10_2
def N_10_2 : List NodeSpec := [([6,0,1],[],[]),([9,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_2 : checkNodesBT W_10 g_10 F_10 P_10_2 A_10 B_10_1 2 N_10_2 = true := by decide +kernel
def B_10_2 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_2
set_option maxRecDepth 500000 in
lemma B_10_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 2 xs.toFinset) B_10_2 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_1_ok C_10_2
def U_10_3 : List Nat := []
def P_10_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_10 r_10 S_10 ps_10 U_10_3
def N_10_3 : List NodeSpec := [([10,11,1,2],[],[3]),([13,0,1,3],[],[]),([15,1,2,3],[],[]),([16,1,2,12],[],[3]),([0,1,17,3],[],[]),([18,1,2,3],[],[]),([19,20,1,3],[],[2]),([22,1,2,3],[],[]),([0,1,24,3],[],[]),([25,26,2,3],[],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_3 : checkNodesBT W_10 g_10 F_10 P_10_3 A_10 B_10_2 3 N_10_3 = true := by decide +kernel
def B_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_3
set_option maxRecDepth 500000 in
lemma B_10_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 3 xs.toFinset) B_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_2_ok C_10_3
def U_10_4 : List Nat := []
def P_10_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_10 r_10 S_10 ps_10 U_10_4
def N_10_4 : List NodeSpec := [([27,0,1,2,3],[],[4]),([10,0,1,2,3],[],[0]),([0,1,2,3,12],[],[0,1,2,4]),([16,0,1,2,3],[],[0,1,3,5]),([19,0,1,2,3],[],[0,1,3]),([0,1,26,2,3],[],[0]),([25,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_4 : checkNodesBT W_10 g_10 F_10 P_10_4 A_10 B_10_3 4 N_10_4 = true := by decide +kernel
def B_10_4 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_4
set_option maxRecDepth 500000 in
lemma B_10_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 4 xs.toFinset) B_10_4 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_3_ok C_10_4
def U_10_5 : List Nat := []
def P_10_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_10 r_10 S_10 ps_10 U_10_5
def N_10_5 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_5 : checkNodesBT W_10 g_10 F_10 P_10_5 A_10 B_10_4 5 N_10_5 = true := by decide +kernel
def B_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_5
set_option maxRecDepth 500000 in
lemma B_10_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 5 xs.toFinset) B_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_4_ok C_10_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck r_10 g_10 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT B_10_5 r_10 = true := by decide +kernel
lemma low_10 : Lower r_10 g_10 6 := lower_of_forestBT root_10_ok B_10_5_ok root_10_in
def g_11 := (d 0xfc80fc80fc80fc80)
def r_11 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_11 : Lower r_11 g_11 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_12 := (d 0xfec0fec0fec0fec0)
def r_12 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_12 : Lower r_12 g_12 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_13 := (d 0xfffce880fffce880)
def r_13 : List Nat := varsOf 31
def p_13 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,18,18,19,19,20,20,21,21,22,24,24,25,25,26,28]
def q_13 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,16,2,17,3,16,4,17,5,6,16,8,17,9,10,12]
def F_13 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_13 : goodPairs g_13 p_13 q_13 := goodPairs_of (by decide +kernel)
def W_13 : BT Decor := buildWiresBT 3 (mkBase p_13 q_13 r_13) [(0,1,2),(1,1,2),(2,1,3)]
lemma W_13_ok : btAll (fun x => faithful p_13 q_13 x ∧ x.1 < 2^256) W_13 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_13 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)]]
def A_13 : BT (List (Nat × Nat)) := btOfList 3 al_13
set_option maxHeartbeats 0 in
lemma A_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_13 = g_13) A_13 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_13_0 : Slice r_13 g_13 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_1 : Slice r_13 g_13 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_13_2 : Slice r_13 g_13 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_3 : Slice r_13 g_13 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_4 : Slice r_13 g_13 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_5 : Slice r_13 g_13 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcc8800ffcc8800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_6 : Slice r_13 g_13 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffffee88ffffee88) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_7 : Slice r_13 g_13 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xfcfc8080fcfc8080) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_8 : Slice r_13 g_13 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_9 : Slice r_13 g_13 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcccc88ffcccc88) 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_12
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_10 : Slice r_13 g_13 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfcfcc8c8fcfcc8c8) 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_12
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
def S_13 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,7),some (subcubeFast 16 0,7),some (subcubeFast 1 0,6),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (identDom 1 2,5),some (identDom 1 3,5)]
lemma S_13_ok : btAll (fun o => ∀ p, o = some p → Slice r_13 g_13 p.1 p.2) S_13 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (forall_cons (fun _ h => by cases h; exact sl_13_4) (forall_cons (fun _ h => by cases h; exact sl_13_5) (forall_cons (fun _ h => by cases h; exact sl_13_6) (forall_cons (fun _ h => by cases h; exact sl_13_7) (forall_cons (fun _ h => by cases h; exact sl_13_8) (forall_cons (fun _ h => by cases h; exact sl_13_9) (forall_cons (fun _ h => by cases h; exact sl_13_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_13 : BT (Option PoolSpec) := btOfList 5 [q 0 [8196,8197],q 4 [],q 1 [8196,8197],q 9 [],q 3 [],q 0 [12294],q 6 [],q 5 [],q 1 [12294],q 10 [],q 7 [],q 8 [],q 0 [8197],q 2 [],q 1 [8197],q 0 [8196],q 1 [8196],q 0 [],q 1 []]
def B_13_5 : BT (List (List Nat)) := BT.empty
lemma B_13_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 5 xs.toFinset) B_13_5 := .empty
def U_13_6 : List Nat := (r 0 5)
def P_13_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_13 r_13 S_13 ps_13 U_13_6
def N_13_6 : List NodeSpec := [([0,5,6,3,4],(r 0 5),[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_6 : checkNodesBT W_13 g_13 F_13 P_13_6 A_13 B_13_5 6 N_13_6 = true := by decide +kernel
def B_13_6 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_6
set_option maxRecDepth 500000 in
lemma B_13_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 6 xs.toFinset) B_13_6 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_5_ok C_13_6
def U_13_7 : List Nat := ([1]++r 4 13)
def P_13_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_13 r_13 S_13 ps_13 U_13_7
def N_13_7 : List NodeSpec := [e5 [7] ([1]++r 4 8),u5 [6] ([1,4,6,7]++r 10 5),u5 [5] [1,4,7,10,11,15,16]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_7 : checkNodesBT W_13 g_13 F_13 P_13_7 A_13 B_13_6 7 N_13_7 = true := by decide +kernel
def B_13_7 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_7
set_option maxRecDepth 500000 in
lemma B_13_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 7 xs.toFinset) B_13_7 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_6_ok C_13_7
def U_13_8 : List Nat := [17,18]
def P_13_8 : BT (Option BoundPool) := buildPoolsSubBT 5 W_13 r_13 S_13 ps_13 U_13_8
def N_13_8 : List NodeSpec := [a5 [] [17,18] [0,1,2,3,4,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_8 : checkNodesBT W_13 g_13 F_13 P_13_8 A_13 B_13_7 8 N_13_8 = true := by decide +kernel
def B_13_8 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_8
set_option maxRecDepth 500000 in
lemma B_13_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 8 xs.toFinset) B_13_8 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_7_ok C_13_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck r_13 g_13 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT B_13_8 r_13 = true := by decide +kernel
lemma low_13 : Lower r_13 g_13 9 := lower_of_forestBT root_13_ok B_13_8_ok root_13_in
def g_14 := (d 0xfefce800fefce800)
def r_14 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 8 := by
  have hc : Lower (varsOf 23) (d 0xfefee8e8fefee8e8) 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 8) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) hc
def g_15 := (d 0xfffcf880fffcf880)
def r_15 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_16 := (d 0xffe0c000ffe0c000)
def r_16 : List Nat := varsOf 31
def p_16 : List Nat := [14,14,14,15,15,15,21,21,21,22,22,22,23,23,24,24,25,25,26,26,27,27,28,28,29]
def q_16 : List Nat := [12,10,6,13,11,7,20,17,5,20,18,6,19,7,16,8,17,9,18,10,19,11,20,12,13]
def F_16 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_16 : goodPairs g_16 p_16 q_16 := goodPairs_of (by decide +kernel)
def W_16 : BT Decor := buildWiresBT 4 (mkBase p_16 q_16 r_16) [(0,3,4),(1,3,4),(3,5,6),(0,2,6),(2,3,4),(3,3,4),(2,2,5),(2,1,5)]
lemma W_16_ok : btAll (fun x => faithful p_16 q_16 x ∧ x.1 < 2^256) W_16 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_16 : List (List (Nat × Nat)) := [[]]
def A_16 : BT (List (Nat × Nat)) := btOfList 1 al_16
set_option maxHeartbeats 0 in
lemma A_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_16 = g_16) A_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_16_0 : Slice r_16 g_16 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_1 : Slice r_16 g_16 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_2 : Slice r_16 g_16 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeecc00ffeecc00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_3 : Slice r_16 g_16 (subcubeFast 0 3) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_4 : Slice r_16 g_16 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xececc0c0ececc0c0) 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_11
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
def S_16 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,5),some (subcubeFast 1 0,5),some (subcubeFast 0 4,5),some (subcubeFast 0 3,4),some (identDom 1 3,5)]
lemma S_16_ok : btAll (fun o => ∀ p, o = some p → Slice r_16 g_16 p.1 p.2) S_16 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_16_0) (forall_cons (fun _ h => by cases h; exact sl_16_1) (forall_cons (fun _ h => by cases h; exact sl_16_2) (forall_cons (fun _ h => by cases h; exact sl_16_3) (forall_cons (fun _ h => by cases h; exact sl_16_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_16 : BT (Option PoolSpec) := btOfList 3 [q 1 [],q 0 [],q 4 [],q 3 [],q 2 []]
def B_16_2 : BT (List (List Nat)) := BT.empty
lemma B_16_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 2 xs.toFinset) B_16_2 := .empty
def U_16_3 : List Nat := []
def P_16_3 : BT (Option BoundPool) := buildPoolsSubBT 3 W_16 r_16 S_16 ps_16 U_16_3
def N_16_3 : List NodeSpec := [([7,0,1,2],[],[]),([0,1,8,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_3 : checkNodesBT W_16 g_16 F_16 P_16_3 A_16 B_16_2 3 N_16_3 = true := by decide +kernel
def B_16_3 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_3
set_option maxRecDepth 500000 in
lemma B_16_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 3 xs.toFinset) B_16_3 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_2_ok C_16_3
def U_16_4 : List Nat := []
def P_16_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_16 r_16 S_16 ps_16 U_16_4
def N_16_4 : List NodeSpec := [([9,10,0,1,2],[],[0]),([0,1,8,3,4],[],[0]),([0,1,2,5,6],[],[0]),([11,0,1,3,4],[],[]),([12,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_4 : checkNodesBT W_16 g_16 F_16 P_16_4 A_16 B_16_3 4 N_16_4 = true := by decide +kernel
def B_16_4 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_4
set_option maxRecDepth 500000 in
lemma B_16_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 4 xs.toFinset) B_16_4 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_3_ok C_16_4
def U_16_5 : List Nat := (r 0 5)
def P_16_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_16 r_16 S_16 ps_16 U_16_5
def N_16_5 : List NodeSpec := [u5 [10] [0,1],u5 [9] [0,1],u5 [6] (r 0 5),u5 [5] [0,1,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_5 : checkNodesBT W_16 g_16 F_16 P_16_5 A_16 B_16_4 5 N_16_5 = true := by decide +kernel
def B_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_5
set_option maxRecDepth 500000 in
lemma B_16_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 5 xs.toFinset) B_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_4_ok C_16_5
def U_16_6 : List Nat := [0,1,3,4]
def P_16_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_16 r_16 S_16 ps_16 U_16_6
def N_16_6 : List NodeSpec := [u5 [] [0,1,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_6 : checkNodesBT W_16 g_16 F_16 P_16_6 A_16 B_16_5 6 N_16_6 = true := by decide +kernel
def B_16_6 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_6
set_option maxRecDepth 500000 in
lemma B_16_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 6 xs.toFinset) B_16_6 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_5_ok C_16_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck r_16 g_16 [(VAR 0,20,21),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,5,21)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT B_16_6 r_16 = true := by decide +kernel
lemma low_16 : Lower r_16 g_16 7 := lower_of_forestBT root_16_ok B_16_6_ok root_16_in
def g_17 := (d 0xfffffae0fec0e000)
def r_17 : List Nat := varsOf 63
def p_17 : List Nat := [13,13,13,14,14,14,15,15,22,22,22,23,23,23,25,25,25,26,26,26,27,27,28,28,28,29,37,37,37,38,38,38,39,39,41,41,41,43,43,43,44,44,44,46,48,48,49,49,50,50,51,51,52,52,53,56,56,58]
def q_17 : List Nat := [12,9,5,12,10,6,11,7,20,18,6,21,19,7,24,17,9,24,18,10,19,11,24,20,12,21,36,33,5,36,34,6,35,7,40,33,9,42,35,11,40,36,12,42,32,16,33,17,34,18,35,19,36,20,21,40,24,42]
def F_17 : Nat := fullMask 58
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 10 (mkBase p_17 q_17 r_17) [(1,2,3),(1,4,5),(0,6,7),(0,2,3),(1,9,4),(1,9,5),(0,10,11),(0,8,12),(1,8,12),(3,13,14),(3,9,6),(0,16,5),(1,16,5),(3,17,18),(0,19,4),(1,19,4),(3,20,21),(0,4,5),(3,23,7),(0,24,2),(1,25,3),(3,1,26),(0,2,4),(1,2,4),(3,28,29),(0,30,5),(1,30,5),(3,31,32),(0,2,7),(1,2,7),(3,34,35),(2,36,3),(3,36,3),(1,38,23),(0,2,5),(0,3,4),(1,40,41),(1,3,4),(1,2,5),(0,43,44),(2,42,45),(3,41,43),(3,40,44),(0,47,48),(1,1,13),(2,47,48),(2,48,47),(3,1,14),(0,3,5),(1,28,54),(1,3,5),(0,29,56),(3,54,56),(2,58,30),(2,30,58),(1,60,1),(0,58,30),(1,58,30),(3,33,3),(1,64,1),(1,59,1),(2,33,3),(2,55,57),(0,58,4),(1,58,4),(3,69,70),(2,71,2),(1,72,1),(0,71,2),(1,2,71),(0,24,3),(1,76,2),(3,1,77),(0,12,7),(0,24,16),(3,8,12),(1,52,1),(2,16,4),(0,83,5),(3,16,4),(1,84,85),(1,83,5),(1,67,1),(0,16,4),(1,16,4),(3,89,90),(3,83,5),(1,1,92),(2,16,5),(2,94,10),(1,95,85),(3,84,87),(3,16,7),(1,10,5),(3,98,99),(3,94,4),(1,1,101),(1,95,1),(2,24,16),(1,24,9),(1,51,1),(3,71,2),(1,107,1),(1,1,79),(1,16,7),(3,23,110),(0,16,7),(0,6,99),(3,1,113),(2,91,5),(3,91,5),(1,115,1),(2,19,4),(1,118,1),(3,1,105),(3,23,99),(3,112,110),(1,95,23),(1,116,1),(1,1,98),(1,24,16),(1,104,1),(3,1,99),(3,19,4),(1,129,1),(3,24,16),(1,47,48),(1,131,1),(3,0,26),(1,24,2),(0,3,35),(0,3,7),(1,3,7),(3,137,138),(3,139,2),(1,1,140),(2,139,2),(1,142,0),(3,23,35),(1,34,3),(3,1,145),(1,137,2),(3,1,147),(0,2,138),(3,76,2),(3,12,7),(0,24,6),(0,105,6),(2,6,79),(3,0,147),(0,139,2),(1,139,2),(3,16,5),(1,0,101),(2,10,5),(3,4,11),(1,95,0),(1,94,4),(0,5,10),(3,164,99),(0,94,4),(1,166,158),(2,16,23),(3,168,7),(3,0,145),(1,142,1),(1,91,5),(1,95,158),(3,166,163),(1,0,140),(3,9,7),(1,140,23),(1,33,3),(2,24,3),(3,25,3),(3,3,7),(2,24,2),(3,182,3),(1,182,181),(3,2,7),(3,185,3),(1,186,23),(1,0,2),(0,188,7),(0,189,3),(3,190,2),(2,2,5),(3,192,47),(1,193,1),(2,48,3),(0,48,4),(1,196,0),(2,47,5),(2,47,2),(1,199,1),(0,47,5),(2,47,0),(1,192,202),(1,47,0),(3,192,204),(1,181,9),(2,3,2),(1,25,207),(3,94,90),(1,1,3),(0,210,7),(0,211,2),(3,212,3),(0,4,11),(1,207,34),(3,11,4),(1,216,5),(2,6,164),(3,5,4),(3,219,10),(2,6,220),(3,0,5),(3,47,2),(1,222,223),(1,17,4),(2,90,5),(3,9,5),(3,227,7),(3,9,4),(3,229,7),(1,17,10),(1,3,189),(3,190,232),(1,89,5),(1,47,5),(0,188,235),(0,0,2),(3,237,188),(3,10,5),(1,239,4),(0,6,240),(1,185,9),(1,181,12),(3,179,7),(3,198,188),(0,47,2),(1,201,1),(1,89,9),(2,248,5),(1,179,9),(1,17,229),(3,4,5),(3,252,16),(3,4,18),(3,219,16),(1,246,222),(0,24,9),(3,257,7),(3,252,11),(0,210,29),(0,260,5),(1,260,5),(3,261,262),(1,95,9),(3,24,3),(3,265,2),(2,135,3),(1,24,3),(0,268,2),(3,1,135),(3,1,268),(3,181,2),(1,272,23),(2,3,5),(2,274,4),(1,275,23),(3,275,2),(2,2,4),(2,278,5),(3,3,35),(3,1,35),(3,2,5),(3,282,47),(3,48,3),(1,47,2),(3,47,0),(3,278,58),(3,274,4),(1,0,288),(3,3,5),(1,1,23),(1,1,158),(0,0,5),(2,47,293),(1,58,2),(3,1,295),(1,1,85),(2,2,3),(2,0,2),(3,299,47),(1,16,23),(2,6,5),(1,302,4),(3,219,303),(3,2,4),(3,305,58),(0,58,2),(3,58,2),(1,0,308),(3,0,99),(1,0,5),(0,47,44),(0,1,3),(3,313,210),(0,188,56),(0,315,4),(1,315,4),(1,275,34),(0,1,4),(1,319,40),(1,1,4),(3,207,7),(3,0,2),(0,47,188),(3,211,2),(2,211,2),(2,47,237),(2,317,5),(2,260,5),(3,260,5),(3,229,240),(1,2,211),(2,47,40),(2,47,222),(3,179,2),(0,47,0),(1,219,9),(0,0,99),(3,1,138),(3,1,29),(2,0,5),(3,341,47),(2,30,5),(3,30,5),(1,282,1),(1,158,4),(3,182,7),(1,0,28),(2,1,3),(3,1,3),(0,9,7),(3,58,4),(1,0,352),(2,58,2),(2,3,4),(3,355,48),(3,1,6),(0,30,3),(2,30,54),(2,24,207),(1,28,5),(3,3,361),(3,0,361),(3,363,3),(2,30,3),(3,1,70),(0,58,29),(3,47,5),(1,274,2),(3,1,369),(3,0,35),(2,2,23),(1,372,3),(3,0,373),(3,3,4),(0,48,3),(3,355,5),(1,355,5),(3,355,2),(1,355,2),(1,355,0),(1,192,0),(3,355,382),(0,2,43),(1,41,5),(3,282,385),(3,355,0),(1,0,7),(3,9,388),(1,349,299),(1,0,1),(1,176,0),(3,0,7),(1,313,40),(2,6,23),(1,0,9),(3,24,2),(3,185,210),(0,188,43),(1,399,5),(3,1,373),(3,1,7),(0,188,3),(1,1,2),(3,137,404),(0,210,2),(1,282,4),(0,391,7),(0,391,2),(3,1,2),(3,410,3),(3,411,7),(1,207,23),(1,349,293),(2,176,1),(1,293,41),(1,54,4),(0,404,417),(0,391,3),(3,419,7),(2,391,137),(1,274,4),(1,319,5),(3,137,188),(1,0,3),(0,425,7),(3,0,3),(3,427,7),(1,293,319),(1,1,9),(1,419,5),(2,391,9),(1,222,4),(0,404,3),(3,434,7),(3,305,417),(2,399,5),(2,189,3),(0,188,385),(0,3,361),(1,1,440),(3,1,4),(1,40,4),(0,3,443),(3,427,361),(1,375,0),(1,0,4),(1,279,23),(3,403,7),(2,188,5),(1,450,4),(2,391,5),(1,452,4),(3,0,6),(3,0,385),(3,455,2),(2,302,4),(0,3,388),(1,1,7),(3,207,459),(1,1,54),(0,461,29),(1,340,54),(0,2,56),(3,274,2),(0,2,459),(3,372,3),(1,375,282),(3,282,3),(1,469,4),(3,219,3),(1,192,375),(1,192,355),(1,192,4),(3,192,3),(1,192,3),(2,476,4),(3,192,1),(3,219,2),(2,43,5),(3,355,44),(0,3,44),(1,375,40),(0,2,385),(3,40,3),(1,485,4),(1,278,290),(1,274,278),(2,2,288),(1,355,40),(1,278,5),(2,369,4),(3,252,2),(3,290,2),(3,5,29),(3,0,56),(1,274,28),(3,41,2),(0,2,417),(3,1,417),(3,3,443),(3,54,2),(1,502,4),(1,252,298),(1,494,4),(3,278,56),(0,382,3),(1,0,23),(1,207,4),(2,509,5),(1,298,4),(2,511,5),(1,290,28),(3,252,6),(2,9,4),(2,9,5),(1,516,4),(2,404,5),(1,518,4),(3,0,4),(1,520,5),(0,425,2),(3,282,210),(1,434,4),(1,1,5),(0,3,525),(3,427,2),(1,527,4),(3,1,5),(1,529,9),(2,404,4),(3,9,447),(1,475,4),(1,299,375),(1,355,1),(2,535,5),(1,465,4),(1,375,5),(1,355,293),(3,355,188),(1,349,237),(2,447,5),(1,406,4),(3,41,188),(0,3,447),(3,54,29),(2,210,5),(3,299,43),(2,188,4),(2,549,5),(3,355,525),(3,4,44),(1,219,298),(1,313,5),(0,2,447),(3,237,3),(1,556,4),(3,219,188),(3,355,391),(0,2,525),(1,560,4),(1,298,23),(3,222,43),(1,355,237),(2,452,4),(2,1,5),(1,427,28),(1,419,4),(1,341,349),(1,237,313),(3,192,29),(3,222,2),(2,425,5),(1,573,4),(3,274,188),(1,409,4),(0,1,2),(1,349,40),(3,274,404),(3,349,2),(3,529,3),(1,581,4),(1,442,9),(3,566,2),(3,4,56),(1,349,5),(1,577,5),(3,1,10),(3,319,2),(3,192,4),(2,3,590),(1,464,4),(1,403,4),(3,278,391),(3,222,3),(3,299,3),(1,596,4),(3,313,44),(1,237,4),(1,237,319),(2,1,4),(1,601,237),(0,404,7),(3,41,44),(2,425,4),(3,355,404),(1,0,34),(1,427,4),(3,54,404),(1,282,442),(3,252,404),(3,520,3),(1,410,4),(2,613,5),(3,1,443),(2,608,5),(1,355,410),(1,482,4),(1,375,237),(1,274,410),(1,572,4),(2,531,5),(1,252,410),(3,282,43),(1,601,293),(1,192,1),(1,511,5),(3,207,525),(1,613,5),(1,526,4),(3,601,2),(0,447,56),(2,210,4),(3,278,525),(0,2,388),(3,341,3),(1,636,4),(0,3,29),(1,192,349),(1,207,442),(1,274,442),(1,411,4),(3,529,2),(1,643,4),(3,520,2),(1,192,442),(3,274,43),(1,529,4),(1,207,529),(3,520,56),(1,278,529),(1,355,529),(3,293,3),(1,653,4),(1,442,40),(1,293,4),(3,305,56),(3,319,44),(1,375,293),(1,522,4),(1,341,601),(1,601,40),(1,547,4),(3,601,44),(1,595,4),(1,601,192),(1,341,375),(3,442,2),(3,442,3),(1,1,34),(1,222,28),(1,290,305),(3,375,0),(1,290,4),(1,274,0),(0,0,56),(2,1,54),(3,577,0),(0,0,3),(1,3,23),(1,299,4),(1,274,1),(1,679,4),(2,0,23),(0,0,6),(3,313,2),(2,0,3),(1,687,4),(3,349,0),(0,1,5),(3,690,2),(0,0,4),(3,566,0),(3,319,0),(1,341,4),(0,0,1)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^256) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[],[(0,1),(2,3),(4,5)]]
def A_17 : BT (List (Nat × Nat)) := btOfList 1 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (identDom 0 1) 10 := by
  have hc : Lower (varsOf 61) (d 0xfffffaa0faa0a000) 10 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_5
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 0 1) 8 := by
  have hc : Lower (varsOf 62) (d 0xfffffff0ffc0f000) 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(4,5)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 32 0) 8 := by
  have hc : Lower (varsOf 31) (d 0xfec0e000fec0e000) 8 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 16 0) 8 := by
  have hc : Lower (varsOf 47) (d 0xfae0fae0e000e000) 8 := carry_of (swaps := [(0,1),(2,4),(3,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 0 8) 8 := by
  have hc : Lower (varsOf 55) (d 0xfffffafafefee0e0) 8 := carry_of (swaps := [(0,1),(2,3),(3,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 0 4) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffffeeffccee00) 8 := carry_of (swaps := [(2,5),(4,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (subcubeFast 1 0) 8 := by
  have hc : Lower (varsOf 62) (d 0xfffff0c0fcc0c000) 8 := carry_of (swaps := [(0,5),(1,5),(2,3),(3,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_7 : Slice r_17 g_17 (subcubeFast 0 2) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffffaf0fff0f000) 8 := carry_of (swaps := [(1,5),(2,3),(3,5)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_8 : Slice r_17 g_17 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffffaa0fa00a000) 8 := carry_of (swaps := [(1,5),(2,5),(4,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_9 : Slice r_17 g_17 (identDom 1 4) 9 := by
  have hc : Lower (varsOf 47) (d 0xfeecfeececc0ecc0) 9 := carry_of (swaps := [(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_13
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_10 : Slice r_17 g_17 (identDom 0 5) 9 := by
  have hc : Lower (varsOf 31) (d 0xfeeaeaa0feeaeaa0) 9 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_13
  exact slice_ident (u := 0) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_11 : Slice r_17 g_17 (subcubeFast 0 3) 7 := by
  have hc : Lower (varsOf 60) (d 0xfffffff0fff0f000) 7 := carry_of (swaps := [(0,4),(1,5),(2,4),(3,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_12 : Slice r_17 g_17 (subcubeFast 1 4) 7 := by
  have hc : Lower (varsOf 58) (d 0xffffffccffcccc00) 7 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_13 : Slice r_17 g_17 (subcubeFast 18 0) 7 := by
  have hc : Lower (varsOf 45) (d 0xfaa0faa0a000a000) 7 := carry_of (swaps := [(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 18) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_14 : Slice r_17 g_17 (subcubeFast 2 8) 7 := by
  have hc : Lower (varsOf 53) (d 0xfffffafafafaa0a0) 7 := carry_of (swaps := [(1,4),(2,4),(3,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 2) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_15 : Slice r_17 g_17 (subcubeFast 33 0) 7 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 33) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_16 : Slice r_17 g_17 (identDom 1 5) 8 := by
  have hc : Lower (varsOf 31) (d 0xfecce8c0fecce8c0) 8 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_14
  exact slice_ident (u := 1) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_17 : Slice r_17 g_17 (identDom 0 4) 8 := by
  have hc : Lower (varsOf 47) (d 0xfaeafaeaea80ea80) 8 := carry_of (swaps := [(0,4),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_14
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_18 : Slice r_17 g_17 (identDom 0 3) 8 := by
  have hc : Lower (varsOf 55) (d 0xffffeaeaeaeaa0a0) 8 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_15
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_19 : Slice r_17 g_17 (identDom 1 2) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffeecceecccc00) 8 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_15
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_20 : Slice r_17 g_17 (subcubeFast 8 0) 7 := by
  have hc : Lower (varsOf 55) (d 0xffffe0e0c0c00000) 7 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_21 : Slice r_17 g_17 (subcubeFast 4 0) 7 := by
  have hc : Lower (varsOf 59) (d 0xffffaa00ee000000) 7 := carry_of (swaps := [(0,1),(2,5),(3,5)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_22 : Slice r_17 g_17 (subcubeFast 18 32) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 18) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_23 : Slice r_17 g_17 (subcubeFast 34 8) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 34) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_24 : Slice r_17 g_17 (subcubeFast 18 8) 4 := by
  have hc : Lower (varsOf 37) (d 0xfafafafaa0a0a0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 18) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_25 : Slice r_17 g_17 (subcubeFast 18 4) 4 := by
  have hc : Lower (varsOf 41) (d 0xffaaffaaaa00aa00) 4 := carry_of (swaps := [(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 18) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_26 : Slice r_17 g_17 (subcubeFast 6 8) 4 := by
  have hc : Lower (varsOf 49) (d 0xffffaaaaaaaa0000) 4 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_27 : Slice r_17 g_17 (subcubeFast 33 16) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_28 : Slice r_17 g_17 (subcubeFast 33 8) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_29 : Slice r_17 g_17 (subcubeFast 33 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_30 : Slice r_17 g_17 (subcubeFast 17 4) 4 := by
  have hc : Lower (varsOf 42) (d 0xffccffcccc00cc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_31 : Slice r_17 g_17 (subcubeFast 9 4) 4 := by
  have hc : Lower (varsOf 50) (d 0xffffcccccccc0000) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_32 : Slice r_17 g_17 (subcubeFast 32 3) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_33 : Slice r_17 g_17 (subcubeFast 16 3) 4 := by
  have hc : Lower (varsOf 44) (d 0xfff0fff0f000f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_34 : Slice r_17 g_17 (subcubeFast 3 8) 4 := by
  have hc : Lower (varsOf 52) (d 0xfffff0f0f0f00000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_35 : Slice r_17 g_17 (subcubeFast 8 3) 4 := by
  have hc : Lower (varsOf 52) (d 0xfffff0f0f0f00000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_36 : Slice r_17 g_17 (subcubeFast 9 2) 4 := by
  have hc : Lower (varsOf 52) (d 0xfffff0f0f0f00000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_37 : Slice r_17 g_17 (subcubeFast 3 4) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_38 : Slice r_17 g_17 (subcubeFast 4 3) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_39 : Slice r_17 g_17 (subcubeFast 6 1) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 1) (by decide +kernel) hc
def S_17 : BT (Option (Nat × Nat)) := btOfList 6 [some (identDom 0 1,10),some (subcubeFast 0 1,8),some (subcubeFast 32 0,8),some (subcubeFast 16 0,8),some (subcubeFast 0 8,8),some (subcubeFast 0 4,8),some (subcubeFast 1 0,8),some (subcubeFast 0 2,8),some (subcubeFast 2 0,8),some (identDom 1 4,9),some (identDom 0 5,9),some (subcubeFast 0 3,7),some (subcubeFast 1 4,7),some (subcubeFast 18 0,7),some (subcubeFast 2 8,7),some (subcubeFast 33 0,7),some (identDom 1 5,8),some (identDom 0 4,8),some (identDom 0 3,8),some (identDom 1 2,8),some (subcubeFast 8 0,7),some (subcubeFast 4 0,7),some (subcubeFast 18 32,4),some (subcubeFast 34 8,4),some (subcubeFast 18 8,4),some (subcubeFast 18 4,4),some (subcubeFast 6 8,4),some (subcubeFast 33 16,4),some (subcubeFast 33 8,4),some (subcubeFast 33 4,4),some (subcubeFast 17 4,4),some (subcubeFast 9 4,4),some (subcubeFast 32 3,4),some (subcubeFast 16 3,4),some (subcubeFast 3 8,4),some (subcubeFast 8 3,4),some (subcubeFast 9 2,4),some (subcubeFast 3 4,4),some (subcubeFast 4 3,4),some (subcubeFast 6 1,4)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (forall_cons (fun _ h => by cases h; exact sl_17_7) (forall_cons (fun _ h => by cases h; exact sl_17_8) (forall_cons (fun _ h => by cases h; exact sl_17_9) (forall_cons (fun _ h => by cases h; exact sl_17_10) (forall_cons (fun _ h => by cases h; exact sl_17_11) (forall_cons (fun _ h => by cases h; exact sl_17_12) (forall_cons (fun _ h => by cases h; exact sl_17_13) (forall_cons (fun _ h => by cases h; exact sl_17_14) (forall_cons (fun _ h => by cases h; exact sl_17_15) (forall_cons (fun _ h => by cases h; exact sl_17_16) (forall_cons (fun _ h => by cases h; exact sl_17_17) (forall_cons (fun _ h => by cases h; exact sl_17_18) (forall_cons (fun _ h => by cases h; exact sl_17_19) (forall_cons (fun _ h => by cases h; exact sl_17_20) (forall_cons (fun _ h => by cases h; exact sl_17_21) (forall_cons (fun _ h => by cases h; exact sl_17_22) (forall_cons (fun _ h => by cases h; exact sl_17_23) (forall_cons (fun _ h => by cases h; exact sl_17_24) (forall_cons (fun _ h => by cases h; exact sl_17_25) (forall_cons (fun _ h => by cases h; exact sl_17_26) (forall_cons (fun _ h => by cases h; exact sl_17_27) (forall_cons (fun _ h => by cases h; exact sl_17_28) (forall_cons (fun _ h => by cases h; exact sl_17_29) (forall_cons (fun _ h => by cases h; exact sl_17_30) (forall_cons (fun _ h => by cases h; exact sl_17_31) (forall_cons (fun _ h => by cases h; exact sl_17_32) (forall_cons (fun _ h => by cases h; exact sl_17_33) (forall_cons (fun _ h => by cases h; exact sl_17_34) (forall_cons (fun _ h => by cases h; exact sl_17_35) (forall_cons (fun _ h => by cases h; exact sl_17_36) (forall_cons (fun _ h => by cases h; exact sl_17_37) (forall_cons (fun _ h => by cases h; exact sl_17_38) (forall_cons (fun _ h => by cases h; exact sl_17_39) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_17 : BT (Option PoolSpec) := btOfList 12 [q 12 [20496,20497,28767],q 13 [8288,8289,553063],q 12 [16396,16397,168097],q 13 [20488,20489,180396],q 12 [20492,20493,221297],q 13 [20492,20493,229492],q 15 [16616,16617,286999],q 13 [20492,20493,229595],q 12 [20600,20601,131199],q 13 [20600,20601,131199],q 4 [20496,94245,20497,28721],q 20 [20496,20497,405528],q 12 [20496,94245,20497],q 13 [12296,12297,28696],q 2 [12296,12297,28696,49185],q 2 [12296,12297,24615],q 12 [16450,16451,348493],q 13 [12296,12297,24615],q 2 [12296,16421,12297,28696],q 12 [20544,20545,73799],q 14 [20544,20545,73799],q 2 [8204,8205,24615,16760],q 2 [8204,8205,24615,16762],q 12 [16448,16449,368999],q 4 [20496,20497,28767],q 12 [16396,16397,176295],q 13 [20488,20489,180387],q 12 [20492,20493,229595],q 4 [20496,20497,28767,8288],q 15 [28684,28685,565799],q 13 [28684,28685,565799],q 12 [20496,20497],q 13 [28680,28681,143499],q 21 [20496,20497,143940],q 21 [16404,16405,28684],q 8 [16396,16397,176295],q 1 [20488,20489,180387],q 18 [20488,20489,180387],q 29 [],q 24 [],q 7 [16396,16397,176295],q 22 [],q 1 [20496,20497,28767],q 6 [20496,20497,28767],q 7 [20496,20497,28767],q 8 [20496,20497,28767],q 2 [],q 4 [16404,16405,28767],q 4 [16404,94245,16405],q 21 [20496,20497,28991],q 20 [20496,20497,28991],q 2 [8204,28720,323589],q 4 [20496,94245,20497],q 20 [20496,20497,28680],q 23 [],q 5 [20496,94245,20497],q 20 [20496,20497,28767],q 20 [20496,20497,28696],q 2 [12296,12297,28696],q 2 [12296,12297],q 20 [20496,20497,405599],q 20 [20496,20497,28723],q 5 [16404,16405,28767],q 21 [20496,20497,28767],q 26 [],q 13 [28680,28681,143372],q 6 [12296,12297,24615],q 1 [12296,12297,24615],q 8 [12296,12297,24615],q 7 [12296,12297,24615],q 13 [12296,12297],q 3 [12296,12297,28696],q 2 [8204,8205,28696],q 3 [8204,8205,24615],q 3 [12296,12297,901146],q 0 [8204,8205,24615],q 4 [],q 2 [8204,8205,24615],q 5 [20496,20497,28767],q 12 [20546,20547],q 14 [20546,20547],q 4 [20496,20497],q 13 [8288,8289],q 3 [8204,8205,24615,20544],q 20 [20520,40981,406163],q 21 [20496,20497,143455],q 2 [8204,8205,24615,16450],q 11 [16396,16397,176295],q 15 [16396,16397,176295],q 2 [12296,12297,983064],q 0 [12296,12297,24615],q 5 [16404,94245,16405],q 2 [12296,16421,12297],q 3 [12296,12297],q 3 [8204,8205,28696],q 6 [8204,8205,24615],q 1 [8204,8205,24615],q 8 [8204,8205,24615],q 7 [8204,8205,24615],q 2 [12296,12297,49178],q 2 [16396,16397,176295],q 3 [12296,12297,24615],q 3 [12296,12297,24615,20546],q 3 [8204,8205,24615,20546],q 11 [12296,12297,24615],q 12 [16450,20814,4477],q 13 [28680,28681],q 20 [20496,20497],q 12 [20546,20547,647545],q 14 [20546,20547,647545],q 20 [16428,45073,405528],q 4 [20517,16429,405511],q 12 [20517,16429,405511],q 11 [8204,8205,24615],q 20 [20496,20497,28736],q 4 [20496,20497,28767,8290],q 12 [20497],q 20 [20497,28680],q 21 [16405,28684],q 21 [16404,16405,28767],q 6 [16404,16405,28767],q 1 [16404,16405,28767],q 20 [16404,16405,28767],q 15 [12386,12387],q 13 [8289,12830],q 15 [12385,9264],q 13 [12385,9264],q 11 [20496,20497,28767],q 7 [16404,16405,28767],q 11 [16404,16405,28767],q 15 [12384,8499],q 8 [16404,16405,28767],q 13 [8288],q 4 [16404,16405,95297],q 21 [16404,16405],q 4 [16404,16405,95309],q 15 [28686,28687],q 2 [28682,9311],q 13 [28681,143375],q 15 [28685,565256],q 2 [12386],q 5 [16404,16405,28684],q 4 [16404,16405],q 2 [28680,28681,143372],q 21 [20496,20497,143372],q 2 [28684,28685,565799],q 20 [16404,16405],q 5 [16404,16405],q 20 [16404,16405,28680],q 15 [28684,8743],q 21 [20496,20497],q 12 [16396,16397],q 2 [16396,16397,180396],q 3 [20488,20489,180396],q 13 [20488,20489],q 2 [16396,16397],q 4 [20488,168097,20489],q 6 [16396,16397,176295],q 1 [16396,16397,176295],q 5 [16396,16397,176295],q 3 [20488,20489,180387],q 27 [],q 12 [12482],q 4 [20488,20489,180387],q 31 [],q 14 [20488,20489,180387],q 21 [16396,16397,176295],q 13 [8380,8381],q 17 [],q 2 [16394,238683],q 20 [],q 11 [20494,20495,1188937],q 3 [20494,20495,1188937],q 21 [20497,143940],q 12 [20496,94274],q 13 [20480,1200318],q 7 [20492,20493,229595],q 11 [20492,20493,229595],q 5 [20492,20493,229595],q 12 [20546],q 14 [20546],q 6 [8204,8205],q 1 [8204,8205],q 8 [8204,8205],q 7 [8204,8205],q 12 [20546,16762],q 14 [20546,16762],q 4 [20496,20497,28683],q 12 [16449,20842],q 2 [12298,12299],q 13 [12298,12299],q 4 [20498,21357],q 5 [20498,21357],q 2 [12296,28680,28684],q 2 [8204,8205],q 13 [8194,193711],q 12 [16448,16449],q 12 [20544,16453],q 12 [20496,94273],q 2 [28683,757858],q 12 [17593,20498,1241967],q 4 [17593,20498,1241967],q 13 [8205,20506],q 20 [17293,983064],q 2 [8204,12297,983064],q 4 [20497,28711],q 3 [],q 20 [16428,45073],q 3 [20492,20493,229595],q 6 [20492,20493,229595],q 1 [20492,20493,229595],q 8 [20492,20493,229595],q 3 [8204,8205],q 21 [20492,20493,229595],q 12 [16421,20521],q 14 [16421,20521],q 20 [20521,405528],q 5 [20492,20493,229595,1261569],q 4 [20496,20497,95309],q 11 [8204,8205],q 4 [16421,20521,405507],q 35 [],q 12 [20517],q 11 [20488,20489],q 2 [12292,12293,861415],q 5 [12292,12293,861415],q 15 [16616,16617],q 0 [8204,8205],q 20 [20497,28696],q 2 [12297,28696],q 11 [20488,165117,20489],q 14 [20488,20489],q 5 [16388,16389,165117],q 2 [12296,28711],q 2 [8206,29503],q 12 [20492,20493],q 3 [20492,20493,229492],q 2 [16392,16393,229492],q 13 [20490,193283],q 0 [8193,16396,16397,176295,770236],q 15 [12296,28720],q 13 [12296,28720],q 5 [16421,20517,20497,45096],q 21 [20497,45096],q 25 [],q 20 [20497,45096],q 11 [20490,20491],q 4 [20517,16421,16405],q 21 [16405,28687],q 13 [12296],q 2 [12298,28684],q 10 [16396,16397,176295],q 20 [20497],q 21 [20496,20497,28723],q 1 [8204,20517,8205,24615],q 7 [8204,20517,8205,24615],q 20 [16430,16431],q 15 [12296,36962],q 13 [12296,36962],q 2 [12296,28680],q 4 [20497],q 20 [20497,28739],q 4 [16421,20517,20497],q 1 [12296,16421,20517,12297],q 7 [12296,16421,20517,12297],q 21 [],q 2 [12296,16421],q 13 [20488,164030],q 20 [16405,28696],q 0 [20483,16396,16397,176295,909502],q 1 [12296,16423,12297,24615],q 7 [12296,16423,12297,24615],q 20 [20520,671770],q 20 [20498],q 4 [16421],q 12 [16421],q 4 [16421,20521],q 5 [20496,20497],q 12 [20517,16405],q 3 [20492,20493,229595,118791],q 12 [20602,20603],q 13 [20602,20603],q 2 [16392,16393,118899],q 2 [8204,28709,405511],q 12 [20498,20499],q 4 [16421,20546],q 2 [12296,28720],q 5 [114689,20492,20493,229595],q 20 [20497,28736],q 2 [8204,28687],q 1 [12296,16421,12297,24615],q 7 [12296,16421,12297,24615],q 21 [20496,20497,28684],q 13 [8380],q 12 [20496,94245],q 13 [12296,12297,49178],q 4 [16405,28709,405511],q 7 [20488,20489,180387],q 11 [20488,20489,180387],q 20 [20497,405528],q 14 [8424,8425],q 6 [8204,12297,24615],q 1 [8204,12297,24615],q 7 [8204,12297,24615],q 2 [8204,12297,24615],q 2 [12296,28723],q 15 [12296,28723],q 13 [12296,28723],q 2 [12296,28708],q 2 [12296,28709],q 21 [20496,20497,405599],q 20 [20496,20497,94914],q 2 [16398,198031],q 20 [20490,20491,1155841],q 1 [20490,20491,1155841],q 6 [20490,20491,1155841],q 13 [20670],q 13 [28680],q 20 [16392,16393,118899],q 4 [16392,16393,118899],q 6 [16392,16393,118899],q 1 [16392,16393,118899],q 8 [16392,16393,118899],q 7 [16392,16393,118899],q 12 [20492,221306],q 3 [20492,20493,229595,286727],q 13 [28685,565256],q 13 [20670,20671],q 12 [20494,20495],q 2 [8205,24583],q 4 [16392,221297,16393],q 13 [20492,20493],q 7 [20494,20495,1188937],q 5 [20494,20495,1188937],q 5 [],q 2 [28687,8919],q 4 [20497,28683],q 1 [],q 1 [20497,28687],q 4 [20497,28681,143363],q 7 [20497,28681,143363],q 8 [20497,28681,143363],q 5 [20497,28687],q 2 [28681,143363],q 3 [28681,143363],q 6 [],q 8 [],q 7 [],q 21 [20497,143372],q 4 [16405],q 20 [16405],q 14 [16405],q 5 [16405,28684],q 4 [20497,28680],q 21 [20497,28684],q 21 [20497],q 5 [20497,12425,593927],q 21 [593927],q 5 [20497],q 2 [28680,28684],q 15 [12386],q 15 [8288],q 13 [8289],q 15 [],q 6 [16404,16405],q 1 [16404,16405],q 8 [16404,16405],q 7 [16404,16405],q 15 [28682],q 2 [28686,9295],q 13 [12386],q 6 [20496,20497],q 1 [20496,20497],q 8 [20496,20497],q 7 [20496,20497],q 13 [28681],q 2 [28681,143375],q 0 [16404,16405,28685,565255],q 2 [28685,565255],q 11 [16404,16405],q 2 [28680],q 15 [28680],q 2 [28680,28681],q 4 [20497,28681],q 1 [20497,28681,143372],q 6 [20497,28681,143372],q 7 [20497,28681,143372],q 8 [20497,28681,143372],q 2 [28684,8743],q 1 [20496,94218],q 11 [20496,94218],q 4 [20496,94218],q 3 [13777,1527811],q 2 [13777,1527811],q 20 [20490],q 1 [16398,16399,1537421],q 6 [16398,16399,1537421],q 2 [16398,16399,1537421],q 5 [16398,16399,1537421],q 21 [16398,16399,1537421],q 2 [12480],q 4 [20490,20491,1155841],q 12 [12480],q 14 [20490,20491,1155841],q 3 [20490,20491,1155841],q 15 [16398,16399,1537421],q 13 [21903],q 12 [16398,16399,1537421],q 13 [9613],q 12 [16398,1566095],q 1 [20490],q 20 [176136],q 3 [176136,28684],q 3 [20488,20489],q 4 [20488,20489],q 13 [20488],q 15 [16396,16397],q 21 [16396,16397],q 4 [20488,168097],q 12 [],q 8 [20488,20489,180387],q 12 [16399],q 13 [20489],q 13 [20671],q 13 [8381],q 0 [16396,16397,176295],q 13 [],q 0 [16396,16397,176295,190],q 1 [16396,20645],q 7 [16396,20645],q 5 [16396,20645],q 2 [16396],q 3 [20491,1578091],q 12 [16423],q 4 [20519,17293],q 21 [17293,983055],q 0 [8204],q 3 [1423],q 5 [16421,20521],q 21 [20521],q 20 [20521],q 2 [8204],q 12 [16448],q 12 [20497,1589287],q 15 [12296,1589287],q 12 [20495],q 13 [20495],q 4 [20517,16429],q 28 [],q 14 [],q 3 [8204,20517],q 20 [16407,45075],q 1 [12294,1226101],q 4 [5,8194],q 12 [20497,28711],q 6 [8204],q 1 [8204],q 8 [8204],q 7 [8204],q 3 [20602],q 2 [16394,16395,1250393],q 6 [16394,16395,1250393],q 1 [16394,16395,1250393],q 8 [16394,16395,1250393],q 7 [16394,16395,1250393],q 4 [16394,16395,1250393],q 12 [20602],q 21 [20602],q 20 [16407],q 2 [8204,37741],q 3 [8204],q 20 [16394],q 15 [16394],q 3 [8204,20519],q 1 [8204,16423],q 7 [8204,16423],q 4 [20497,28675],q 3 [12296,20522],q 5 [16421],q 3 [12296],q 11 [20488,165093],q 8 [20488],q 21 [12292,12293],q 5 [12292,12293,165093],q 2 [12296],q 3 [12296,40983],q 4 [20517,16405],q 3 [8204,28687],q 5 [20517,16405],q 21 [16405],q 3 [8204,28711],q 2 [12292,12293],q 4 [20490,20491],q 0 [20488,20489,180387],q 12 [12294],q 2 [16393,118791],q 3 [118791,20494,20495],q 7 [20494,20495],q 12 [20496],q 7 [20496,94218],q 3 [8205,24583],q 1 [12296],q 34 [],q 36 [],q 6 [12296],q 14 [8426],q 4 [16421,20517],q 12 [16421,20517],q 14 [16421,20517],q 15 [8291],q 13 [8291],q 15 [12296,16421],q 1 [12296,16421,12297],q 7 [12296,16421,12297],q 4 [16421,20498],q 1 [12296,16421],q 3 [12298,12299],q 4 [20498,20499],q 5 [20498,20499],q 15 [16392],q 4 [16392,221297],q 21 [20492,20493],q 4 [16404,94213],q 5 [16404,94213],q 3 [8206,8207],q 7 [8206,8207],q 2 [8206,8207],q 15 [16619],q 13 [20480],q 2 [16388,16389],q 9 [20490,20491],q 1 [12296,20517],q 12 [20517,20497],q 3 [12296,36865],q 4 [16405,28683],q 13 [28683,860903],q 4 [8193],q 1 [16397],q 5 [16397],q 15 [16397,176880],q 3 [13777,1527815],q 2 [13777,1527815],q 5 [16405,28679],q 8 [16405],q 6 [12296,12297],q 1 [12296,12297],q 8 [12296,12297],q 7 [12296,12297],q 4 [16421,20522],q 20 [20522],q 15 [13040,28687],q 13 [188],q 5 [20497,28684],q 13 [28684,1655335],q 6 [20497],q 1 [20497,28684,8743],q 20 [1511431],q 2 [9289,1511431],q 0 [20494,9289,1511431,20495],q 5 [20494,20495],q 11 [20494,20495],q 4 [8193,17645],q 1 [20493],q 14 [8193],q 11 [20493],q 5 [20493],q 7 [20491,17513],q 0 [12293,9032,20491,17513],q 6 [12293,9032],q 4 [20491,17513],q 2 [12293,9032],q 21 [17513],q 20 [16394,16395],q 2 [16394,16395],q 2 [8204,45072],q 15 [16617],q 14 [16617],q 1 [20497],q 6 [20497,30236],q 1 [20497,28680],q 13 [30236,28680],q 11 [20488,165117],q 3 [20488],q 21 [16388,16389],q 14 [20488],q 0 [16398,21901],q 1 [16398,21901],q 8 [9756],q 2 [16398],q 14 [20490],q 6 [12292,12293,861415],q 11 [20490],q 3 [12292,12293,861415],q 13 [20490],q 3 [8205,20506],q 5 [17593,20498],q 4 [17593,20498],q 13 [13931,30319],q 4 [16404,95037],q 2 [12298,9387],q 4 [5,20480],q 1 [12294,1201525],q 6 [8204,12297],q 1 [8204,12297],q 8 [8204,12297],q 7 [8204,12297],q 20 [17293],q 2 [8204,12297],q 13 [8204,28711],q 5 [16405,28687],q 6 [16396,16397],q 4 [20480,169109],q 3 [8192,8193,770999],q 7 [8192,8193,770999],q 8 [8192,8193,770999],q 4 [8192,8193,770999],q 15 [16399],q 1 [16396,16397],q 3 [8192,8193],q 4 [8192,8193],q 11 [16396,16397],q 0 [16405,28684],q 5 [16405],q 20 [16405,28680],q 13 [13852,30351],q 4 [16405,28711],q 0 [16405],q 1 [16405,28684],q 15 [28684,562718],q 13 [28684,562718],q 7 [16405,28684],q 3 [20480,20481],q 10 [16396,16397],q 4 [20480,20481],q 0 [20494,17481],q 1 [20494,17481],q 3 [20494],q 0 [12296,20497,28711],q 5 [20497,28711],q 0 [16388,21757],q 0 [16388,21757,9756],q 5 [5,16388,21757],q 1 [16388,21757],q 12 [16388,21757],q 21 [16388,21757],q 14 [9756],q 3 [5,9756],q 8 [12296,36865],q 7 [12296,36865],q 4 [36865],q 5 [36865],q 2 [28687],q 15 [28687],q 13 [28687],q 20 [1179649],q 2 [17483,1179649],q 3 [20494,20495],q 12 [16397],q 2 [16397,180396],q 11 [20488],q 1 [20497,28684],q 15 [28684,770599],q 7 [20488,20489],q 2 [12294,12295],q 5 [12294,12295],q 1 [16405],q 6 [16405,30372],q 1 [16405,28680],q 15 [30372,28680],q 3 [12296,28680,28684],q 12 [16388],q 14 [20480],q 1 [16388,1307797],q 4 [16405,8741,602119],q 20 [602119],q 13 [8204,40983],q 16 [],q 15 [8427],q 14 [8427],q 13 [12297,28696],q 7 [16393],q 5 [12293],q 5 [12293,21523],q 2 [12296,16423],q 3 [12296,20519],q 1 [12296,16423,20519],q 7 [12296,16423,20519],q 14 [20517],q 20 [16428],q 7 [16405],q 8 [16405,29512],q 4 [16405,28680],q 13 [29512,28680],q 0 [8205,24583,20496,20497],q 11 [20496,20497],q 0 [20480,13852,22157],q 2 [4097,13852],q 7 [20480,22157],q 12 [13852,22157],q 1 [12296,16421,20517],q 7 [12296,16421,20517],q 5 [16421,20517,20497],q 7 [20490,20491],q 20 [20496],q 21 [4097],q 5 [4097,38430],q 13 [12296,38430],q 2 [8204,16431],q 14 [20497],q 13 [8192],q 0 [20492,20493,16393,118791],q 7 [20492,20493],q 5 [20492,20493],q 3 [20492,20493,118791],q 11 [20492,20493],q 4 [16393,118791],q 0 [20483,17273,12296,20517],q 12 [17273,20517],q 7 [12296,20517],q 14 [16421],q 4 [16423,20497],q 1 [12296,16423,12297],q 7 [12296,16423,12297],q 5 [16405,30411],q 4 [20519,16405],q 4 [16421,20497],q 21 [20497,28687],q 2 [12296,28687],q 6 [20493,230128],q 4 [8193,17644],q 2 [8193,230128],q 15 [12298],q 13 [12298],q 13 [20602],q 1 [20492,16601],q 5 [20492,16601],q 3 [20492],q 2 [16395,1709255],q 7 [16396,16397],q 5 [16396,16397],q 3 [20491,5225],q 4 [20491,5225],q 0 [8193,16396,20645,1577712],q 3 [8193,1577712],q 15 [16396,1577712],q 1 [16405,30351],q 7 [16405,30351],q 14 [16405,30351],q 1 [16397,20494],q 3 [8193,176880],q 0 [8193,16397,176880,20494],q 5 [16397,20494],q 12 [16397,20494],q 8 [16393,119624],q 5 [12293,21522],q 11 [16405],q 15 [12293,29512],q 3 [12293,29512],q 8 [16392,20593],q 3 [1478668,1802245],q 4 [16392,20593,1802245],q 11 [8204],q 21 [16429,405511],q 20 [16431],q 2 [8204,983079],q 13 [13904,30411],q 4 [20488,16545],q 7 [20488,16545],q 8 [20488,16545],q 14 [20488,16545],q 15 [12296],q 4 [16423,21397],q 21 [21397,888847],q 1 [16392,20593],q 12 [16449],q 14 [16449],q 6 [20497,29424],q 13 [8193,29424],q 11 [20497],q 3 [28673],q 2 [28673],q 15 [12296,28711],q 12 [16451],q 13 [20482],q 4 [20497,28709],q 12 [20498],q 2 [16399,1501],q 1 [20490,20491],q 20 [20490,20491],q 2 [16398,16399],q 12 [20494,20495,1188937],q 14 [9289],q 30 [],q 12 [20496,20497,95325],q 13 [28682],q 4 [20498,37741],q 15 [13040,30287],q 11 [20489],q 14 [20489],q 3 [12297,28696],q 1 [18185,20498],q 3 [8193,21234],q 5 [18185,20498],q 0 [8205,24583,20498,20499],q 7 [20498,20499],q 13 [12296,28711],q 4 [16406,17393],q 1 [18193],q 6 [22046,18193],q 7 [18193],q 8 [22046,18193],q 3 [5,22046],q 12 [22046,18193],q 4 [20497,28673],q 18 [12296],q 1 [16404,94218],q 11 [16404,94218],q 4 [16404,94218],q 3 [12297,24579],q 2 [12297,24579],q 2 [28679],q 12 [16396,20645],q 4 [20497,28681,143367],q 7 [20497,28687],q 1 [20497,28681,143367],q 6 [20497,28681,143367],q 2 [28681,143367],q 3 [28681,143367],q 7 [8204,20517,8205],q 12 [17594,20496],q 4 [17594,20496],q 20 [16405,28683],q 12 [20494],q 14 [16393],q 1 [20498,21357],q 6 [20498,21357],q 7 [20498,21357],q 8 [20498,21357],q 12 [20493],q 3 [20493,229492],q 4 [16392,16393],q 13 [20493,229492],q 6 [8205,24583],q 1 [8205,24583],q 13 [12297],q 11 [16396,20645],q 20 [20491,5225],q 1 [16405,30287],q 0 [8193,13040,16405,30287],q 5 [16405,30287],q 12 [16405,30287],q 4 [20496,94245],q 5 [20496,94245],q 3 [12298,9387],q 2 [16392,16393],q 6 [20498,20499],q 1 [20498,20499],q 8 [20498,20499],q 6 [12298,12299],q 1 [12298,12299],q 8 [12298,12299],q 7 [12298,12299],q 12 [20497,1589260],q 1 [12298],q 15 [12298,1589260],q 3 [20670],q 8 [16398,16399,1537421],q 7 [16398,16399,1537421],q 20 [20670],q 20 [16405,405511],q 21 [16405,405511],q 13 [8206,1880895],q 7 [8206],q 14 [8425],q 2 [8204,16429],q 13 [20668],q 3 [20492,221189],q 11 [16392,16393],q 5 [20492,221189],q 11 [16393],q 12 [20492,221189],q 20 [16393,120628],q 4 [221189,16393,120628],q 2 [16392,114689],q 1 [20494,20495],q 2 [16392],q 12 [20593,13743],q 12 [20593,1478671],q 11 [16392,20593],q 21 [1478668,1802245],q 5 [20593,1478668,1802245],q 15 [8424],q 14 [8424],q 15 [16616],q 3 [20492,20493],q 5 [20492,222545],q 11 [20492],q 12 [20492,222545],q 20 [16393,118791],q 4 [16393,118791,222545],q 3 [20492,118791,222545],q 0 [20496,20497,28681,143367],q 13 [20493,229384,28684],q 20 [229384],q 2 [229384,28684],q 15 [9291],q 14 [9291],q 21 [20494,20495,1188937],q 15 [17481],q 13 [20494,20495,1188937],q 14 [17481],q 2 [12296,36865],q 15 [17483],q 2 [8424],q 20 [8424],q 3 [28681,143375],q 6 [16405],q 5 [16405,28685],q 1 [20497,28681],q 6 [20497,28681],q 7 [20497,28681],q 8 [20497,28681],q 2 [28681],q 3 [28681],q 5 [20497,12425],q 6 [20497,28680],q 8 [20497],q 7 [20497],q 8 [20497,28680],q 7 [20497,28680],q 7 [20497,28675],q 8 [20497,28675],q 5 [20497,28675],q 38 [],q 3 [28675],q 0 [20497,28687],q 13 [1880072],q 5 [16405,28677],q 14 [16405,1880072],q 7 [20497,28673],q 8 [20497,28673],q 5 [20497,28673],q 18 [],q 15 [13779],q 13 [13779],q 13 [20491],q 4 [20491],q 2 [16399],q 12 [18261],q 13 [20491,13419],q 4 [20491,18261],q 14 [20491,18261],q 6 [20498,13167],q 1 [20498,13167],q 8 [20498,13167],q 7 [20498,13167],q 2 [13167],q 6 [20490],q 15 [13777],q 13 [13777],q 6 [20497,28684],q 8 [20497,28684],q 7 [20497,28684],q 2 [28684],q 3 [20490],q 3 [28684],q 8 [16399,1501],q 4 [20490],q 5 [16399,1501],q 12 [16399,1536769],q 21 [16398],q 1 [16398,16399],q 6 [16398,16399],q 5 [16398,16399],q 21 [16398,16399],q 2 [17153],q 3 [20490,20491],q 12 [17153],q 13 [20490,20491],q 2 [13059],q 12 [13059],q 8 [20490,20491],q 14 [20490,20491],q 6 [16398,9615],q 1 [16398,9615],q 8 [16398,9615],q 7 [16398,9615],q 3 [9615],q 4 [9615],q 21 [18290],q 2 [4867],q 6 [20490,20491],q 0 [20490,20491],q 12 [4867],q 12 [16407],q 2 [9071],q 3 [20490,13059],q 1 [20490,13059],q 6 [20490,13059],q 7 [20490,13059],q 8 [20490,13059],q 5 [13059],q 6 [16407],q 1 [16407],q 8 [16407],q 7 [16407],q 4 [16407],q 21 [16407],q 15 [16397],q 2 [16397],q 12 [16398],q 13 [20489,181647],q 4 [20489,181647],q 14 [20489,181647],q 3 [20489,180236],q 1 [20489,180236],q 6 [20489,180236],q 7 [20489,180236],q 8 [20489,180236],q 5 [16407],q 2 [180236],q 6 [16397,176136],q 1 [16397,176136],q 8 [16397,176136],q 7 [16397,176136],q 3 [176136],q 5 [16399],q 12 [16399,165341],q 21 [16399],q 4 [20488],q 12 [16405,28686],q 12 [16396,168097],q 15 [16396],q 20 [20488],q 21 [16396],q 6 [16396,20645],q 20 [1576968],q 2 [16396,1576968],q 1 [20488,16545],q 12 [16545,16399],q 12 [12451,18325],q 15 [18325],q 13 [20488,12451],q 21 [18325],q 4 [20488,18325],q 14 [20488,18325],q 1 [16398],q 6 [16398],q 7 [16398],q 6 [20488,8355],q 1 [20488,8355],q 4 [20488,8355],q 6 [20498,9071],q 1 [20498,9071],q 8 [20498,9071],q 7 [20498,9071],q 21 [20494],q 4 [20498,9071],q 1 [20494],q 6 [20494],q 7 [20494],q 3 [28680],q 12 [20495,1188953],q 13 [20495,1188953],q 14 [16394],q 12 [20494,1139785],q 20 [1179658],q 12 [16398,165261],q 15 [16398],q 13 [20488,165261],q 12 [21593,16405],q 13 [21593],q 2 [9291],q 21 [20494,20495],q 3 [20494,9291],q 1 [20494,9291],q 6 [20494,9291],q 7 [20494,9291],q 8 [20494,9291],q 21 [20498],q 4 [9291],q 1 [20498],q 7 [20498],q 8 [20498],q 4 [20498],q 14 [9291,20489],q 20 [17862],q 5 [20494],q 11 [20494],q 12 [20499],q 13 [9203],q 2 [16393],q 13 [20495,9355],q 4 [16393,20598],q 6 [16393,20598],q 13 [20494,20598],q 6 [20493,229384],q 1 [20493,229384],q 13 [20493,229384],q 7 [20493,229384],q 2 [229384],q 13 [176136],q 4 [16393],q 2 [17483],q 13 [20494,20495],q 6 [16393,118791],q 3 [118791],q 3 [118791,20494],q 8 [20493,229379],q 2 [229379],q 3 [20493,229379],q 21 [20493,229379],q 0 [16393,118791,16397],q 7 [16397],q 1 [16393,118791],q 11 [16397],q 12 [20494,115785],q 13 [20494],q 4 [16392,115785],q 20 [16392],q 12 [20492],q 13 [20492,118807],q 4 [16393,118807],q 14 [16393,118807],q 12 [16396],q 20 [20489],q 4 [8359,20489],q 0 [20492,16393,118791],q 7 [20492],q 5 [20492],q 12 [20492,221297],q 13 [20492],q 21 [20492],q 4 [16392,20593],q 6 [16392,20593],q 7 [16392,20593],q 21 [1478671],q 6 [20492,16601],q 15 [1708040],q 8 [20492,16601],q 7 [20492,16601],q 13 [20492,1708040],q 20 [1708040],q 12 [20593,20495],q 21 [20495],q 13 [21901],q 4 [21901,16405],q 0 [20492,16601],q 14 [16601],q 11 [20492,16601],q 6 [20488,16545],q 21 [1814543],q 3 [20488,1814543],q 12 [20492,18393],q 15 [18393],q 13 [20492,8411],q 4 [8411,18393],q 14 [8411,18393],q 7 [16392,114689],q 8 [16392,114689],q 5 [114689],q 1 [20495],q 4 [16392,114689],q 3 [20495],q 11 [20495],q 0 [16405,28685,565255],q 3 [28685,565255],q 20 [16392,114689],q 5 [114689,20494],q 11 [],q 11 [16392],q 4 [221189],q 4 [221189,16392],q 12 [20499,1221617],q 13 [12298,1221617],q 14 [20499],q 21 [20499],q 3 [12298],q 2 [12298],q 4 [16405,8743],q 12 [20497,28684],q 13 [12298,28684],q 3 [12298,28684],q 12 [20495,18361],q 14 [18361],q 15 [18361],q 6 [12298],q 12 [16405],q 13 [8206,29503],q 4 [16405,29503],q 12 [20493,230491],q 15 [16394,230491],q 12 [13816],q 4 [20490,769],q 2 [769,13816],q 21 [13816],q 3 [20493],q 13 [20493],q 4 [20496,94213],q 1 [20496,94213],q 6 [20496,94213],q 7 [12298],q 11 [12298],q 5 [20496,94213],q 4 [20496,94209],q 7 [20496,94209],q 8 [20496,94209],q 5 [20496,94209],q 4 [20496],q 5 [20496],q 12 [22518],q 13 [8206,22518],q 12 [17577,22526],q 4 [22526],q 12 [20495,115849],q 4 [16392],q 6 [12297],q 1 [12297],q 8 [12297],q 7 [12297],q 3 [12297],q 2 [12297],q 12 [16406],q 4 [16406],q 13 [8205,25587],q 14 [16406],q 3 [8205],q 7 [8205],q 2 [8205],q 12 [17594],q 14 [17594],q 4 [221189,16393],q 20 [16393],q 7 [12297,24579],q 8 [12297,24579],q 11 [16407],q 0 [8205,24583,20497],q 8 [12296],q 7 [12296],q 4 [17481,20498],q 12 [20498,37741],q 2 [12296,37741],q 6 [16392,16393],q 8 [16392,16393],q 13 [12296,28680],q 4 [20489],q 3 [20489,180396],q 13 [20489,180396],q 8 [12298],q 3 [12296,28711],q 13 [119795],q 12 [20497,28708],q 13 [12296,28708],q 13 [8204],q 12 [17153,20498],q 15 [17153],q 13 [20492,12507],q 1 [12298,9387],q 6 [12298,9387],q 7 [12298,9387],q 8 [12298,9387],q 5 [20498],q 33 [],q 12 [16423,20497],q 1 [12296,16423],q 7 [12296,16423],q 4 [16423],q 12 [20519,17293],q 15 [8204],q 13 [8204,20519],q 32 [],q 21 [17293],q 12 [16422,18445],q 4 [16422,18445],q 12 [20518,18449],q 4 [20518,18449],q 13 [12296,20522],q 5 [16421,20522],q 3 [12296,20521],q 13 [12296,20521],q 2 [8204,16428],q 3 [28680,28684],q 7 [12296,16421],q 12 [16421,20498],q 7 [18457],q 5 [18457],q 11 [18457],q 3 [8197,22098],q 13 [22098],q 2 [17481],q 1 [8207],q 4 [16387,22561],q 7 [16387,22561],q 8 [16387,22561],q 12 [22561],q 3 [8207],q 15 [8207],q 8 [8207],q 7 [8207],q 3 [12289,9892],q 7 [12289,9892],q 8 [12289,9892],q 15 [9892],q 11 [20498],q 7 [20491],q 0 [12293,20491,861291],q 11 [20491],q 2 [12293],q 13 [20491,861291],q 7 [18121],q 5 [18121],q 11 [18121],q 13 [13904],q 14 [18121],q 6 [20485,2150412],q 1 [20485,2150412],q 7 [20490],q 2 [2150412],q 8 [20490],q 8 [2150412],q 3 [20485,2150412],q 0 [20490,17153],q 1 [20490,17153],q 4 [20490,17153],q 7 [20490,17153],q 5 [17153],q 14 [20490,17153],q 6 [12295],q 1 [12295],q 21 [12295],q 0 [20491,17513],q 1 [20491,17513],q 5 [12295],q 8 [20491,17513],q 14 [20491,17513],q 2 [12295],q 6 [13852],q 12 [13852],q 2 [5,13852],q 3 [5,13852],q 15 [13852],q 0 [20488,16545],q 5 [16545],q 11 [20488,16545],q 1 [18493],q 11 [18493],q 12 [18493],q 3 [12291,9903],q 4 [9903,18493],q 20 [18493],q 1 [20494,16397],q 12 [20494,16397],q 3 [8195],q 20 [8195],q 11 [12296],q 4 [20487,38981],q 5 [20487,38981],q 13 [12296,38981],q 21 [20487],q 1 [8197,18002],q 6 [8197,18002],q 4 [16385,1830951],q 5 [16385,1830951],q 3 [12296,1830951],q 12 [1830951],q 15 [12296,1830951],q 20 [16385],q 0 [20488,20489],q 8 [20488,20489],q 2 [12294],q 5 [12294],q 8 [16397],q 4 [8193,21234],q 12 [13059,18285],q 1 [16405,28687],q 12 [16405,28687],q 4 [8195],q 10 [16397],q 6 [12294,12295],q 3 [12294,12295],q 3 [8194],q 6 [16399],q 13 [8194],q 1 [16399,1537197],q 4 [8194],q 12 [16397,20654],q 13 [20488,20654],q 7 [20489],q 0 [16391,20488,20489],q 1 [20488,20489],q 2 [16391],q 5 [16391],q 9 [20488,20489],q 0 [12291,16405,30383],q 15 [30383],q 3 [12291,30383],q 12 [16405,30383],q 4 [20480],q 6 [12294],q 7 [20480,1201525],q 8 [20480],q 1 [16396,8359],q 11 [16396,8359],q 3 [8193],q 15 [16396,8359],q 4 [8193,8359],q 20 [8193],q 8 [8194],q 15 [12294],q 13 [22622],q 2 [16398,5517],q 5 [16398],q 14 [22622],q 11 [16398],q 20 [22622],q 12 [20494,18245],q 13 [20494,9291],q 4 [9291,18245],q 14 [9291,18245],q 14 [20497,28680],q 1 [16399,21981],q 0 [8193,16399,21981],q 0 [16399,21981],q 7 [16399,21981],q 8 [8193],q 7 [8193],q 5 [16399,21981],q 20 [4097],q 37 [],q 0 [20490,16398],q 20 [20480],q 13 [20480,1201549],q 11 [16398,1201549],q 4 [20480,1201549],q 2 [16393,28680],q 0 [8193,20493,230128],q 15 [230128],q 3 [8193,771471],q 4 [8193,771471],q 15 [16398,771471],q 4 [20490,16393],q 3 [12293],q 7 [20490,16393],q 1 [20490,16393],q 12 [20593,20493],q 5 [12289],q 4 [8192],q 5 [12294,972149],q 8 [8192],q 1 [12294,972149],q 4 [16385,22270],q 12 [22270],q 7 [16385,22270],q 1 [16394],q 6 [16394],q 7 [16394],q 6 [20492,12507],q 1 [20492,12507],q 5 [20492,12507],q 2 [16394],q 7 [16397,20494],q 7 [18009],q 11 [18009],q 13 [9032],q 4 [18009],q 7 [8192,8193],q 8 [8192,8193],q 1 [16399],q 1 [16396],q 11 [16396],q 5 [16396],q 15 [16396,770215],q 4 [8193,770215],q 4 [16385],q 12 [1830924],q 3 [12298,1830924],q 0 [12293,20488,20489],q 13 [20492,119003],q 4 [16393,119003],q 14 [16393,119003],q 13 [8204,28687],q 0 [8193,16396,20645],q 0 [16396,20645],q 4 [20645],q 15 [16388],q 21 [16388],q 5 [16388,165117],q 6 [16393],q 1 [16393],q 5 [12293,21322],q 6 [12293,21322],q 1 [12293,21322],q 6 [16397],q 14 [8194],q 1 [22678],q 11 [22678],q 5 [22678],q 6 [13040],q 3 [8193,13040],q 7 [8193,13040],q 8 [8193,13040],q 15 [13040],q 0 [8193,13040,16399],q 11 [16399],q 0 [20485,16398,2151823],q 13 [2151823],q 14 [2151823],q 3 [20489],q 2 [4097,9756],q 3 [4097,9756],q 4 [4097,9756],q 15 [9756],q 12 [20498,1221485],q 15 [12298,1221485],q 2 [12292],q 6 [12292,21733],q 5 [12292,21733],q 14 [20482],q 11 [21733],q 12 [12292,21733],q 4 [5,22046],q 0 [12294,22046],q 2 [5,12294],q 1 [12294],q 8 [16385,1830920],q 7 [16385,1830920],q 2 [16385,1830920],q 3 [1830920],q 4 [16385,1830920],q 15 [1830920],q 13 [9615],q 4 [16393,9615],q 0 [12292,21733,8199],q 7 [21733],q 4 [21733],q 2 [12292,8199],q 21 [12292,21733],q 0 [12296,16421],q 5 [4097,16421],q 4 [4097,16421],q 3 [4097,12296],q 6 [18609],q 12 [18609],q 13 [8192,13239],q 4 [8192,18609],q 11 [13239,18609],q 15 [18609],q 0 [8193,20498,770927],q 15 [770927],q 0 [12296,38430],q 4 [4097,38430],q 12 [38430],q 15 [12296,38430],q 5 [5,22046],q 1 [18185],q 5 [18185],q 11 [18185],q 6 [12292,12293],q 3 [12292,12293],q 5 [12292,12293],q 0 [16398,1602959],q 20 [5],q 13 [1602959],q 15 [16398,1602959],q 12 [16398,1602959],q 6 [16405,28684],q 8 [16405,28684],q 6 [16405,28682],q 1 [16405,28682],q 7 [18625],q 11 [18625],q 13 [2150408],q 14 [2150408,18625],q 12 [20496,95401],q 0 [12295,20488,20489],q 2 [9289],q 0 [22046,12296],q 2 [5,12296],q 12 [22046],q 0 [16396,16397],q 8 [16396,16397],q 3 [8192],q 2 [16395],q 6 [20494,20495],q 0 [9756,20497],q 5 [4097,20497],q 13 [9756],q 0 [22046,18193],q 14 [22046,18193],q 13 [22046],q 1 [16397,20654],q 5 [16397,20654],q 2 [8193],q 7 [16397,20654],q 3 [20483,177019],q 12 [16397,177019],q 7 [16396],q 1 [20491,5225],q 6 [20491,5225],q 0 [20497,28680],q 0 [8193,20497,29424],q 15 [29424],q 3 [8193,29424],q 13 [8192,972173],q 11 [16398,972173],q 4 [8192,972173],q 20 [8192],q 0 [16394,21593],q 1 [16394,21593],q 4 [16394,21593],q 7 [16394,21593],q 5 [21593],q 14 [16394,21593],q 0 [22046,18194],q 15 [18194],q 0 [8193,16398,21901],q 7 [16398,21901],q 5 [16398,21901],q 4 [21901],q 3 [21901],q 0 [20486,9756],q 5 [5,20486],q 1 [20486],q 12 [20486],q 2 [5,9756],q 0 [20497,28681,143367],q 0 [20480,13852],q 4 [4097,20480],q 7 [20480],q 13 [20480,13852],q 13 [20598],q 6 [12296,20517],q 6 [12296,16421],q 8 [12296,20517],q 8 [12296,16421],q 5 [16421,20517],q 1 [16392],q 0 [12291,16392,116397],q 12 [116397],q 3 [12291],q 15 [16392,116397],q 12 [12292,165093],q 21 [12292],q 4 [20488,165093],q 3 [20493,229384],q 8 [20493,229384],q 0 [8199,16388,21757],q 7 [21757],q 3 [8199],q 11 [21757],q 2 [8199,16388],q 5 [16388,21757],q 4 [8411,16393],q 14 [8411,16393],q 0 [13852,18061],q 1 [18061],q 7 [18061],q 14 [18061],q 12 [13852,18061],q 13 [13852],q 6 [16404,94213],q 5 [5,12294],q 3 [5,8194],q 1 [12294,12295],q 4 [20482],q 2 [12294,1430869],q 8 [20482],q 1 [12294,1430869],q 11 [1430869],q 6 [12292],q 5 [12292,1282997],q 11 [1282997],q 15 [12292],q 12 [12292],q 3 [5,20480],q 13 [20490,119555],q 0 [8193,16397,176880],q 8 [16396],q 3 [20483,9083],q 7 [20483,9083],q 8 [20483,9083],q 1 [18677],q 11 [18677],q 4 [18677],q 3 [12289,22182],q 12 [22182,18677],q 0 [8193,20494,771147],q 2 [8193,771147],q 0 [9756,18021],q 1 [18021],q 5 [4097,18021],q 12 [18021],q 7 [18021],q 14 [9756,18021],q 0 [8196,22046],q 2 [5,8196],q 8 [22046],q 14 [22046],q 3 [8196],q 1 [8196],q 21 [12294],q 5 [12294,165237],q 0 [20497,30236],q 15 [30236],q 13 [30236],q 12 [20497,30236],q 14 [20497,30236],q 2 [8197,1655883],q 13 [20494,1655883],q 2 [16389],q 5 [4097,17153],q 0 [12294,9591],q 1 [12294,9591],q 4 [5],q 3 [5],q 21 [5],q 7 [18709],q 11 [18709],q 14 [18709],q 3 [20487,14407],q 13 [14407],q 0 [16391,12296,38633],q 4 [16391,38633],q 5 [16391,38633],q 21 [16391],q 0 [20486,10459],q 1 [20486,10459],q 7 [10459],q 15 [10459],q 7 [20494,17481],q 5 [20494,17481],q 8 [16394],q 0 [20494,16394],q 13 [28687,8919],q 7 [20488],q 2 [8193,29424],q 3 [20482],q 0 [16398,16399],q 12 [16398,16399],q 10 [16398,16399],q 2 [4097,16388],q 3 [4097,20480],q 1 [16388],q 5 [4097,16388],q 15 [229395],q 0 [12294,21877],q 1 [12294,21877],q 12 [12294,21877],q 0 [8196,22789],q 1 [8196,22789],q 5 [5,22789],q 12 [22789],q 1 [16405,28683],q 6 [16405,28683],q 7 [16405,28683],q 8 [16405,28683],q 2 [28683],q 3 [28683],q 6 [16405,28687],q 7 [16405,28687],q 8 [16405,28687],q 3 [28687],q 0 [16393,118791,20493],q 7 [20493],q 3 [118791,20493],q 1 [16388,9471],q 15 [16388,9471],q 6 [16396],q 7 [20493,229379],q 5 [20493,229379],q 6 [12293],q 1 [12293],q 13 [118807],q 7 [16393,118807],q 1 [16393,118807],q 11 [16393,118807],q 0 [8193,20494,17481],q 4 [17481],q 8 [20489],q 4 [21733,20489],q 7 [16393,20598],q 14 [16393,20598],q 3 [12295],q 11 [16393,20598],q 21 [2416654],q 11 [9591],q 4 [20485],q 2 [12294,9591],q 21 [20485],q 12 [20493,18241],q 14 [18241],q 1 [17997],q 0 [8193,13040,17997],q 5 [17997],q 11 [17997],q 0 [16394,1602651],q 12 [1602651],q 15 [16394,1602651],q 14 [16394,1602651],q 4 [20483],q 3 [20483,13179],q 12 [13179,16397],q 6 [18769],q 3 [8194,13487],q 5 [18769],q 15 [18769],q 4 [20489,181479],q 7 [20489,181479],q 1 [16392,16393],q 7 [16392,16393],q 5 [20495],q 1 [16397,176151],q 12 [16397,176151],q 8 [8195],q 7 [8195],q 2 [8195],q 8 [8192,17333],q 4 [8192,17333],q 5 [16385,20497],q 6 [16388],q 0 [],q 5 [16388,1307573],q 11 [1307573],q 14 [8192],q 6 [16390],q 3 [8192,973157],q 1 [16390,973157],q 7 [8192,973157],q 15 [16390],q 5 [16390,973157],q 12 [16390],q 6 [17273],q 4 [20483,17273],q 7 [20483,17273],q 8 [20483,17273],q 12 [17273],q 3 [20483],q 2 [8197,30288],q 3 [8197,30288],q 3 [8197,1656207],q 4 [8197,1656207],q 6 [18093],q 12 [18093],q 8 [12291,18093],q 7 [12291,18093],q 2 [12291,18093],q 4 [18093],q 0 [12296,20497],q 3 [4097],q 6 [8197],q 1 [8197],q 14 [21901],q 2 [8197],q 14 [1655003],q 13 [20492,1655003],q 8 [8193,17138],q 7 [8193,17138],q 4 [8193,17138],q 21 [12289],q 7 [20499],q 5 [20499],q 11 [20499],q 7 [20495],q 4 [16387],q 2 [16387,14371],q 12 [14371,20493],q 15 [14371],q 15 [9903],q 8 [12291,9903],q 7 [12291,9903],q 4 [9903],q 5 [16385,22270],q 2 [16385],q 21 [16385,22270],q 2 [17155],q 12 [17155],q 2 [16388],q 0 [20483,17273,12296],q 11 [22934],q 13 [22934],q 21 [22934],q 5 [18025,22934],q 13 [28684],q 4 [8199],q 0 [20488,16545,1814535],q 21 [1814535],q 2 [1814535],q 1 [22914],q 11 [22914],q 20 [22914],q 4 [18093,22914],q 7 [16399],q 5 [16404],q 6 [16404,94218],q 7 [16404,94218],q 8 [16404,94218],q 3 [8206],q 2 [8206],q 12 [16404],q 13 [8206],q 13 [1680781],q 5 [16398,1680781],q 8 [16398,21901],q 6 [8199],q 1 [8199],q 12 [18313],q 13 [20489,180236],q 4 [20489,18313],q 14 [20489,18313],q 5 [16399,972253],q 1 [16399,972253],q 4 [16601],q 2 [8199],q 14 [1680457],q 5 [20494,1680457],q 13 [20494,1680457],q 6 [1830924],q 8 [16385,1830924],q 7 [16385,1830924],q 2 [16385,1830924],q 3 [1830924],q 15 [1830924],q 1 [18673],q 12 [18673],q 11 [18673],q 11 [22606],q 5 [22606],q 8 [20494,17481],q 7 [20480,20481],q 8 [20480,20481],q 5 [20480,20481],q 10 [16399],q 8 [20499,1680369],q 5 [20499,1680369],q 0 [12293,9032,20497],q 7 [8204,20517],q 0 [20485,8204,20517],q 11 [8204,20517],q 13 [8204,20517],q 5 [20485,20517],q 4 [16394],q 21 [16385],q 13 [20491,177259],q 14 [20491],q 11 [1202533],q 3 [20480,1202533],q 2 [16390],q 7 [20483,13179],q 0 [20483,13179,12298],q 12 [13179],q 2 [4865],q 12 [17577,22525],q 14 [22525],q 0 [20485,8206,2151231],q 5 [20485],q 11 [8206],q 14 [2151231],q 13 [8206,2151231],q 0 [16393,118791,20497],q 7 [8206,17213],q 0 [20485,8206,17213],q 6 [20485],q 1 [20485],q 0 [8206,17213],q 1 [8206,17213],q 4 [20485,17213],q 14 [17213],q 7 [22933],q 11 [22933],q 21 [22933],q 5 [18025,22933],q 7 [18489],q 11 [18489],q 14 [18489],q 13 [2150412],q 1 [16406,17393],q 6 [16406,17393],q 7 [16406,17393],q 8 [16406,17393],q 5 [16406,17393],q 0 [20485,20489,2150408],q 2 [2150408],q 11 [10599],q 3 [20485,10599],q 2 [16390,10599],q 0 [20485,2150408,20497],q 6 [20485,2150408],q 1 [20485,2150408],q 8 [2150408],q 0 [16385,20493,231164],q 15 [231164],q 3 [20493,231164],q 12 [20493,231164],q 0 [20485,16394,2151515],q 11 [16394],q 13 [2151515],q 5 [20485,2151515],q 15 [1589256],q 14 [20497,30288],q 13 [30288],q 6 [18929],q 12 [18929],q 13 [20482,13655],q 4 [20482,18929],q 11 [13655,18929],q 15 [18929],q 2 [16393,118796],q 6 [16393,118796],q 12 [12294,1430273],q 11 [20490,1430273],q 2 [12294,1430273],q 7 [10459,20489],q 1 [8204,20517],q 11 [12299],q 4 [16391,1811261],q 14 [1811261],q 3 [12299],q 1 [12296,20519],q 6 [12296,20519],q 7 [12296,20519],q 8 [12296,20519],q 5 [20519],q 4 [20519],q 6 [12296,16423],q 8 [12296,16423],q 5 [16423],q 15 [12296,16423],q 13 [12296,20519],q 14 [1811529],q 1 [20492,20493],q 0 [16385,12296,20517],q 5 [16385,20517],q 0 [12296,20517],q 11 [12296,20517],q 4 [20517],q 7 [18029],q 11 [18029],q 14 [18029],q 3 [8199,13931],q 5 [13931,18029],q 13 [13931],q 21 [18029],q 7 [18957],q 11 [18957],q 13 [10311],q 12 [14371],q 13 [20489,28680],q 12 [16421,20522],q 8 [16387,10275],q 7 [16387,10275],q 2 [16387,10275],q 4 [16387,10275],q 15 [10275],q 2 [16391,1811201],q 5 [16391,1811201],q 15 [16397,177227],q 3 [20494,177227],q 6 [20487,18501],q 1 [20487,18501],q 4 [20487,18501],q 5 [20487,18501],q 3 [20487],q 14 [18501],q 12 [16398,1454849],q 15 [16398,1454849],q 4 [20487,2167613],q 14 [2167613],q 13 [12299,2167613],q 3 [20487,2167897],q 5 [20487,2167897],q 2 [13057],q 12 [13057],q 12 [17593],q 4 [17593],q 14 [17593],q 12 [16405,28684],q 13 [28684,8743],q 14 [2168205],q 6 [18997],q 3 [20480,13463],q 12 [18997],q 7 [16393,20490],q 14 [16393,20490],q 0 [16391,20488,165609],q 5 [16391,165609],q 4 [16388,21757],q 3 [20480],q 5 [20480,17557],q 4 [20480,17557],q 2 [16395,230599],q 10 [16396],q 6 [16388,16389],q 5 [16388,16389],q 9 [20490],q 7 [20480,1307797],q 11 [1307797],q 6 [20496],q 1 [20496],q 8 [20496],q 7 [20496],q 0 [16391,20488,16545],q 5 [16391,16545],q 3 [20481],q 20 [20481],q 4 [20481,20645],q 5 [16389],q 1 [18473],q 4 [18473],q 11 [18473],q 12 [18473],q 3 [20482,2463061],q 7 [20482,2463061],q 1 [16390,2463061],q 11 [2463061],q 0 [8205,24583,20496],q 12 [16390,166245],q 11 [20488,166245],q 21 [16390],q 4 [20481,20517],q 0 [12293,9032,16393],q 7 [18573],q 11 [18573],q 4 [18573],q 3 [12293,21322],q 13 [21322],q 5 [16390],q 3 [20489,182631],q 1 [18765],q 0 [20483,13179,18765],q 11 [18765],q 12 [13179,18765],q 12 [16390,788837],q 11 [20490,788837],q 2 [16390,788837],q 3 [20490,788837],q 2 [16399,1537365],q 1 [16399,1537365],q 8 [16392],q 7 [16392],q 6 [8199,18025],q 1 [8199,18025],q 5 [18025],q 2 [8199,18025],q 0 [16391,12296,16421],q 5 [16391,16421],q 11 [12296,16421],q 6 [16391,9963],q 1 [16391,9963],q 20 [16391,9963],q 2 [16391,9963],q 4 [16391,9963],q 0 [16391,9963,20494],q 14 [9963],q 6 [16391,14059],q 1 [16391,14059],q 2 [16391,14059],q 5 [20497,139269],q 0 [20483,16392,115577],q 12 [115577],q 0 [12296,36865,16421],q 4 [36865,16421],q 0 [20487,12296,20517],q 0 [12296,36865,20517],q 4 [36865,20517],q 3 [12296,20517],q 5 [16421,20498],q 4 [16395],q 0 [16405,28679],q 3 [20491],q 1 [20491],q 8 [20491],q 2 [769],q 1 [20489],q 6 [20489],q 1 [20488],q 12 [16545],q 1 [16395],q 6 [16395],q 7 [16395],q 8 [16395],q 6 [20495],q 8 [20495],q 12 [21594],q 13 [21594],q 8 [16393],q 6 [20493],q 8 [20493],q 0 [16393,118791],q 2 [229376],q 6 [16392],q 4 [17213],q 12 [17577],q 12 [20518],q 14 [20518],q 0 [12296,36865],q 14 [8411],q 7 [20483],q 8 [20483],q 5 [20483],q 0 [16399],q 0 [20483,16399],q 0 [8205,24583],q 0 [12296],q 0 [16391,12296],q 9 [12296],q 4 [16391],q 0 [20483,17273],q 8 [16399],q 7 [20482],q 5 [2311],q 5 [16388],q 0 [16388],q 4 [16388],q 0 [8192],q 0 [20489],q 0 [12295,20489],q 0 [20488],q 0 [12295,20488],q 0 [16396],q 5 [5],q 0 [20487,12296],q 5 [20487],q 11 [17581],q 0 [20497],q 0 [12295,20497],q 7 [8192],q 0 [20498],q 0 [20491],q 11 [17557],q 0 [12292,8199],q 0 [8199],q 5 [12292],q 2 [4097],q 0 [8193,16397],q 0 [16397],q 0 [12294],q 39 [],q 0 [16391,20488],q 1 [16391],q 6 [16391],q 9 [20488],q 0 [12291,18093],q 0 [20480],q 6 [20498],q 13 [12288],q 4 [19101],q 11 [19101],q 0 [16391,20489],q 9 [20489],q 0 [8194],q 20 [8199],q 7 [20481],q 8 [20481],q 4 [20481],q 4 [4097],q 1 [12292],q 0 [20482],q 10 [12294],q 5 [20480],q 8 [16385],q 5 [16385],q 0 [22046],q 2 [5],q 0 [9756],q 5 [4097],q 10 [12292],q 0 [8193,20497],q 11 [9447],q 4 [9447],q 5 [20486],q 0 [16393],q 0 [12295,16393],q 0 [12293,9032],q 0 [20494],q 9 [20494],q 7 [16385],q 0 [12293,20488],q 5 [17333],q 11 [17333],q 2 [16387],q 14 [22098],q 0 [12288],q 7 [12288],q 2 [12288],q 8 [12289],q 2 [12289],q 3 [12289],q 11 [10459],q 2 [10459],q 0 [20487,16393],q 4 [20487],q 3 [8197],q 4 [8197],q 3 [12290],q 11 [19133],q 13 [12290],q 6 [9903],q 14 [18025],q 0 [8193,16399],q 0 [8199,16388],q 21 [20486],q 0 [20492],q 0 [16391,20492],q 1 [20492],q 8 [12291],q 2 [12291],q 21 [12291],q 0 [20490],q 0 [20486],q 4 [20486],q 0 [8199,20492],q 8 [20492],q 12 [20484],q 11 [10955],q 4 [8359],q 2 [8207],q 0 [8207],q 11 [8207],q 0 [8199,20497],q 6 [16389],q 0 [16385],q 3 [12288],q 0 [8193,20493],q 0 [20493],q 0 [16385,16397],q 0 [20485],q 0 [20485,2150408],q 14 [2150408],q 0 [16385,20493],q 12 [22182],q 0 [16385,20497],q 2 [2267],q 6 [20486],q 0 [16385,12296],q 7 [16387],q 8 [16387],q 5 [16387],q 20 [16387],q 7 [12291],q 5 [12291],q 0 [16407],q 1 [16389],q 4 [16389],q 21 [16389],q 10 [],q 3 [10599],q 1 [8206],q 6 [8206],q 8 [8206],q 10 [16388],q 7 [12289],q 0 [16392],q 11 [9471],q 5 [20481],q 11 [17749],q 4 [16390],q 1 [16390],q 10 [16390],q 9 [20482],q 0 [16398],q 10 [16398],q 0 [12295],q 19 [],q 0 [20487],q 0 [16391],q 9 [],q 0 [8193]]
def B_17_1 : BT (List (List Nat)) := BT.empty
lemma B_17_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 1 xs.toFinset) B_17_1 := .empty
def U_17_2 : List Nat := []
def P_17_2 : BT (Option BoundPool) := buildPoolsSubBT 12 W_17 r_17 S_17 ps_17 U_17_2
def N_17_2 : List NodeSpec := [([15,0,1],[],[]),([22,0,1],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_2 : checkNodesBT W_17 g_17 F_17 P_17_2 A_17 B_17_1 2 N_17_2 = true := by decide +kernel
def B_17_2 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_2
set_option maxRecDepth 500000 in
lemma B_17_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 2 xs.toFinset) B_17_2 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_1_ok C_17_2
def U_17_3 : List Nat := []
def P_17_3 : BT (Option BoundPool) := buildPoolsSubBT 12 W_17 r_17 S_17 ps_17 U_17_3
def N_17_3 : List NodeSpec := [([27,0,33,3],[],[]),([37,0,1,39],[],[]),([46,49,0,1],[],[0]),([0,42,50,45],[],[]),([51,52,0,1],[],[0]),([53,0,55,57],[],[]),([0,55,50,57],[],[]),([59,60,0,1],[],[0]),([58,30,0,61],[],[]),([62,63,0,1],[],[0]),([0,65,33,3],[],[]),([58,30,0,66],[],[]),([67,64,0,1],[],[0]),([68,62,0,1],[],[0]),([0,73,2,71],[],[]),([0,1,74,75],[],[0]),([78,0,2,71],[],[]),([0,1,79,14],[],[]),([80,81,0,1],[],[0]),([47,48,0,82],[],[]),([0,1,86,87],[],[]),([0,88,33,3],[],[]),([0,91,93,5],[],[]),([0,1,96,92],[],[]),([0,1,85,97],[],[]),([100,0,1,23],[],[]),([0,19,4,102],[],[]),([0,103,19,4],[],[]),([53,0,42,45],[],[]),([104,0,1,105],[],[]),([47,48,0,106],[],[]),([0,108,2,71],[],[]),([0,8,50,12],[],[]),([0,8,12,109],[],[]),([111,112,0,1],[],[]),([114,0,8,12],[],[]),([115,116,0,1],[],[0]),([0,1,13,14],[],[0]),([0,117,91,5],[],[]),([0,119,19,4],[],[]),([0,1,20,21],[],[0]),([24,16,120,0],[],[]),([121,0,1,98],[],[]),([0,1,122,23],[],[]),([24,16,0,103],[],[]),([0,1,98,123],[],[]),([0,124,91,5],[],[]),([24,16,0,125],[],[]),([0,103,91,5],[],[]),([80,126,0,1],[],[0]),([24,16,0,127],[],[]),([128,0,8,12],[],[]),([0,130,19,4],[],[]),([104,131,0,1],[],[0]),([49,132,0,1],[],[0]),([24,16,128,0],[],[]),([53,0,8,12],[],[]),([24,16,0,133],[],[]),([0,1,105,98],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_3 : checkNodesBT W_17 g_17 F_17 P_17_3 A_17 B_17_2 3 N_17_3 = true := by decide +kernel
def B_17_3 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_3
set_option maxRecDepth 500000 in
lemma B_17_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 3 xs.toFinset) B_17_3 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_2_ok C_17_3
def U_17_4 : List Nat := (r 0 28)
def P_17_4 : BT (Option BoundPool) := buildPoolsSubBT 12 W_17 r_17 S_17 ps_17 U_17_4
def N_17_4 : List NodeSpec := [([25,134,1,135,3],[],[1]),([0,1,33,3,26],[0,1],[0,1]),([114,0,34,136,23],[],[]),([139,0,2,141,23],[],[]),([139,143,1,2,23],[],[]),([144,146,0,34,3],[],[]),([25,27,0,135,3],[],[0]),([146,0,34,136,23],[],[]),([139,148,0,2,23],[],[]),([148,0,149,137,23],[],[]),([46,0,1,42,45],[],[0]),([0,1,13,42,45],[2,3],[0,1]),([49,47,48,0,1],[],[0]),([62,0,1,55,57],[],[0]),([0,1,55,57,14],[4,5],[0,1]),([0,1,13,55,57],[4,5],[0,1]),([58,30,63,0,1],[],[0]),([62,58,30,0,1],[],[0]),([0,1,150,2,71],[],[]),([107,0,1,2,71],[6,7],[0,1]),([67,0,1,33,3],[8,9],[0,1]),([0,1,74,2,71],[],[0]),([114,0,149,137,23],[],[]),([151,0,2,3,109],[],[]),([49,0,1,42,45],[],[0]),([151,152,0,1,9],[],[]),([0,1,9,105,8],[],[]),([24,0,1,9,113],[],[]),([121,0,1,9,8],[],[]),([128,0,9,8,23],[],[0]),([151,0,1,9,8],[],[]),([114,0,9,8,23],[],[0]),([112,0,1,8,12],[],[]),([0,1,113,12,7],[10,11],[]),([24,0,1,9,153],[],[]),([128,0,6,12,7],[],[0]),([154,0,1,12,7],[],[]),([151,0,1,8,12],[],[]),([139,155,1,2,23],[],[]),([0,1,8,12,99],[12,13],[0,1]),([0,1,8,79,12],[12,13],[0,1]),([0,1,42,45,14],[2,3],[0,1]),([0,1,12,14,7],[14],[0]),([81,0,1,8,12],[],[0]),([80,0,1,8,12],[],[0]),([111,16,0,1,7],[15],[0]),([156,0,1,157,23],[],[0]),([94,1,158,4,159],[],[1]),([0,1,91,92,5],[16,17],[0,1]),([95,0,1,85,92],[],[0]),([160,161,16,0,1],[],[]),([160,112,0,1,4],[],[]),([80,0,1,12,7],[],[]),([94,162,1,158,4],[],[1]),([16,0,103,23,7],[],[0]),([16,0,125,23,7],[],[0]),([95,0,1,91,5],[16,17],[0,1]),([0,6,12,109,7],[],[0]),([160,16,0,1,163],[],[]),([0,1,8,10,11],[18],[]),([165,16,0,1,4],[],[]),([47,48,132,0,1],[],[0]),([129,0,1,19,4],[19,20],[0,1]),([68,0,1,55,57],[],[0]),([94,0,1,167,4],[21],[1]),([0,1,91,5,87],[],[]),([112,0,1,12,7],[],[]),([100,0,1,4,5],[],[0]),([0,1,12,169,7],[],[]),([0,1,20,19,4],[],[0]),([144,170,1,34,3],[],[]),([0,1,8,113,12],[12,13],[0,1]),([166,0,1,19,4],[],[]),([24,112,16,0,1],[],[]),([104,24,16,0,1],[0,17],[0,1]),([151,16,0,1,7],[],[]),([139,0,171,2,23],[],[]),([24,128,0,9,6],[],[0]),([0,1,91,5,172],[],[1]),([152,0,1,9,105],[],[]),([94,0,1,173,4],[22],[1]),([0,1,13,8,12],[12,13],[0,1]),([16,0,1,174,5],[],[1]),([139,1,2,175,23],[],[]),([115,0,1,91,5],[17,23],[0,1]),([166,0,1,158,163],[],[1]),([112,0,1,4,87],[],[]),([80,24,16,0,1],[],[0]),([16,0,1,123,7],[15],[0]),([95,0,1,98,23],[],[0]),([0,1,98,12,7],[],[]),([0,1,8,12,14],[12,13],[0,1]),([95,24,16,0,1],[0,17],[0,1]),([16,128,0,23,7],[],[0]),([24,16,0,1,98],[0,17],[0,1]),([16,0,1,163,87],[],[]),([24,16,126,0,1],[],[0]),([24,120,0,9,6],[],[0]),([16,0,1,105,7],[15],[0]),([24,131,16,0,1],[0,17],[0,1]),([24,112,0,1,9],[],[]),([94,0,158,4,102],[],[0]),([24,16,176,0,1],[],[]),([139,0,1,2,177],[],[1]),([94,0,103,158,4],[],[0]),([0,1,122,4,5],[],[0]),([0,1,98,23,99],[],[0]),([0,1,33,3,178],[],[1]),([112,0,1,23,110],[],[0]),([24,0,1,9,98],[24],[0]),([24,16,0,1,99],[0,17,24],[0,1]),([51,47,48,0,1],[25,26],[0,1]),([121,16,0,1,7],[15],[0]),([59,58,30,0,1],[7,27],[0,1]),([80,24,0,1,9],[],[]),([104,24,0,1,9],[24],[0]),([176,0,1,8,12],[],[]),([151,24,16,0,1],[],[]),([37,0,1,38,23],[],[0]),([24,16,0,1,105],[0,17,24],[0,1]),([168,0,1,79,7],[],[]),([24,16,0,1,110],[],[]),([168,151,0,1,7],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_4 : checkNodesBT W_17 g_17 F_17 P_17_4 A_17 B_17_3 4 N_17_4 = true := by decide +kernel
def B_17_4 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_4
set_option maxRecDepth 500000 in
lemma B_17_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 4 xs.toFinset) B_17_4 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_3_ok C_17_4
def U_17_5 : List Nat := (r 0 6++[7,8,9,11,12,13,15,17]++r 23 93)
def P_17_5 : BT (Option BoundPool) := buildPoolsSubBT 12 W_17 r_17 S_17 ps_17 U_17_5
def N_17_5_0 : List NodeSpec := [([37,0,1,38,4,5],[],[0]),([139,143,1,2,4,5],[],[0]),([146,0,34,136,4,5],[],[0]),([148,0,149,137,4,5],[],[0]),([179,24,0,1,2,180],[28],[]),([24,181,0,1,2,183],[],[]),([24,184,0,1,2,3],[],[]),([179,24,0,1,186,2],[],[]),([24,181,0,1,186,2],[],[]),([181,0,1,2,187,7],[],[]),([139,0,1,140,2,23],[29,30],[0,1]),([37,36,0,1,3,23],[31,32],[0,1]),([191,139,0,1,2,23],[],[]),([0,1,34,3,113,23],[33],[]),([139,0,1,2,147,23],[29,30,34],[0]),([24,146,0,34,2,3],[],[]),([24,148,0,2,137,3],[],[]),([0,1,42,45],[2,3],[0]),([193,47,0,194,2,5],[35],[]),([195,48,197,1,3,4],[36,37,38],[]),([198,47,0,200,2,5],[39],[]),([24,191,185,0,1,3],[],[]),([201,47,0,200,2,5],[39,40,41],[]),([139,0,171,2,4,5],[],[0]),([203,47,0,1,2,5],[],[]),([47,0,205,1,2,5],[35,40],[]),([0,1,33,3],[8,9],[0,1]),([179,182,0,1,9,7],[41],[]),([24,0,1,2,3,79],(r 42 5),[]),([179,182,24,0,1,9],[41,47],[]),([179,25,24,0,1,9],[24,41],[]),([24,120,0,9,2,3],[],[0]),([179,24,185,0,1,9],[24],[]),([24,181,185,0,1,9],[47],[]),([24,0,1,9,2,206],[47],[]),([179,24,0,1,9,34],[24,41],[]),([24,181,0,1,9,34],[24,41],[]),([176,0,1,2,3,79],[],[]),([25,24,181,0,1,9],[41,47],[]),([25,24,0,1,9,137],[41,47],[]),([24,128,0,9,2,3],[],[0]),([0,1,2,206,12,7],[48],[]),([128,0,2,3,12,7],[],[0]),([151,0,1,2,3,79],[49,50],[0,1]),([0,2,3,79,109,7],[51],[0]),([181,185,0,1,12,7],[48],[]),([181,0,1,34,12,7],[52,53],[]),([0,1,34,137,12,7],[52],[]),([0,1,34,137,12],[54,55],[]),([114,0,9,8,4,5],[],[0]),([128,0,9,8,4,5],[],[0]),([0,1,9,105,6,7],[56],[0]),([112,0,1,9,8,23],[57],[0]),([0,1,9,8,113,23],[13,31,57],[0,1]),([176,0,1,9,8,23],[58],[0]),([121,0,1,9,6,7],[59,60],[0]),([0,1,9,113,23,7],[11],[0]),([114,0,149,137,4,5],[],[0]),([0,1,9,8,23,99],[13,31],[0,1]),([151,0,1,9,6,7],[61],[0]),([25,24,208,0,1,3],[62],[]),([0,1,9,8,12,7],[57],[0]),([0,1,9,8,12],[12,13,57],[0]),([25,0,1,33,3],[0,1,63],[0,1]),([112,0,1,113,4,5],[],[]),([176,0,1,113,4,5],[],[]),([94,0,1,4,209,5],[64],[]),([160,0,1,9,113,4],[],[0]),([0,1,9,113,4,5],[],[]),([94,16,162,1,4,5],[],[0]),([114,0,34,136,4,5],[],[0]),([179,24,213,0,1,2],[56],[]),([0,1,34,136,145,23],[31,65],[0,1]),([16,0,1,113,4,5],(r 66 4),[]),([160,176,0,1,6,4],[],[0]),([24,0,1,9,105,6],[0,56,70],[0,1]),([160,0,1,9,8,10],[58,71],[]),([151,0,1,34,3,12],[55],[]),([94,0,1,158,4,163],[],[0,1]),([0,1,9,8,214,11],[72],[]),([16,0,1,214,11,7],[],[]),([47,48,0,1],[25,26],[0,1]),([24,176,0,1,2,3],[],[]),([112,0,1,8,4,11],[],[]),([179,0,1,2,183,7],[],[]),([176,0,1,8,4,11],[72],[]),([24,0,1,34,3,215],[],[]),([16,0,1,4,217,11],[54,73],[]),([218,0,1,4,10,11],[],[]),([139,0,2,141,4,5],[],[0]),([221,0,1,9,10,5],[74],[]),([216,161,16,0,1,5],[],[1]),([47,0,1,2,224,5],[],[]),([160,16,0,1,4,99],[75],[0]),([156,139,0,1,2,23],[],[0]),([160,161,0,1,9,6],[],[0]),([112,0,1,4,5,99],[76],[0,1]),([219,16,0,1,163,5],[77],[]),([25,76,24,0,1,9],[24,41,78],[]),([152,24,0,1,9],[24],[0]),([95,94,0,1,158,4],[79,80],[0,1]),([146,0,34,3,23,35],[],[0,1]),([0,1,9,98,23,7],[81],[0]),([16,0,1,214,5,99],[],[1]),([25,0,1,135,3,26],[0,63,82],[0]),([89,16,0,1,225,5],[83],[]),([151,0,1,2,3,7],[],[]),([165,0,1,9,6,4],[84],[0]),([226,16,0,1,4,7],[15,64],[]),([16,0,1,4,87,7],[15],[0]),([95,16,0,1,4,5],(r 66 4),[]),([0,1,228,230,2,3],[46],[]),([16,0,1,4,231,5],([15]++r 66 4),[]),([0,2,3,12,109,7],[51],[0]),([160,16,0,1,4,7],[15],[0]),([0,1,8,10,11,7],[54,71],[]),([0,1,8,4,10,11],[71],[]),([0,1,34,136,113,23],[31,53,65],[0,1]),([144,213,0,1,34,3],[85],[]),([16,0,1,4,87,11],[75],[1]),([139,148,0,2,4,5],[],[0]),([24,16,0,1,7],[0,15,17],[0]),([0,1,8,10,11],[54,71],[]),([233,0,1,2,4,5],[],[]),([112,16,0,1,23,7],[],[0]),([16,0,1,4,234,11],[73],[]),([176,0,1,6,12,7],[52],[0]),([0,1,2,3,79,7],[],[]),([160,16,0,1,4,5],[],[]),([47,0,1,2,236,5],[],[]),([151,24,0,1,9,6],[24,56],[0]),([94,83,0,1,4,5],[73,86],[]),([0,1,98,4,11,7],[],[]),([16,0,1,228,4,7],[77],[]),([47,238,1,5],[25,87,88],[]),([139,0,1,2,157,23],[],[0]),([160,17,16,0,1,4],[54],[]),([94,160,16,0,1,4],[54,76],[0]),([152,24,0,1,9,7],[24],[]),([0,1,9,241,10,5],[89],[]),([0,1,206,242,4,5],[76],[]),([166,94,0,1,158,4],[],[0]),([94,16,0,1,4,87],[15,90],[0]),([112,0,1,9,4,5],[],[]),([16,0,125,4,5,7],[],[0]),([160,0,1,9,8,4],[58],[0]),([58,30,0,1],[7,27],[0,1]),([0,1,2,12,243,7],[91],[]),([112,16,0,1,4,5],[],[]),([166,16,0,1,163,5],[],[0]),([94,83,0,1,101,5],[],[]),([160,16,0,1,4,11],[75],[0]),([24,0,1,9,2,244],[41,62],[]),([16,0,1,23,7,110],[],[0]),([24,0,1,9,6,99],[0,70],[0,1]),([89,0,1,9,225,5],[],[]),([0,1,6,10,11,7],[92,93],[0]),([16,0,1,4,11,7],[64,73],[]),([16,0,1,4,163,5],[],[]),([114,0,9,113,4,5],[],[]),([47,0,1,2,245,5],[],[]),([0,1,9,8,4,11],[94],[0]),([25,24,134,1,2,3],[],[0]),([16,0,1,4,5,99],([76]++r 95 4),[]),([168,0,1,9,12,7],[99],[]),([24,16,0,1,9,7],[56],[0]),([16,229,0,1,225,5],[],[]),([156,0,1,157,4,5],[],[0]),([246,47,0,247,2,5],[39,41,100],[]),([16,229,0,1,163,5],[],[]),([128,0,9,113,4,5],[],[]),([0,1,9,228,8,4],[72],[]),([94,16,0,1,4,234],[15,101],[]),([0,1,91,5],[17,23],[0,1]),([249,16,0,1,4,5],[],[]),([24,0,1,9,250,2],[47],[]),([112,0,1,4,10,5],[],[0]),([89,16,0,1,163,5],[102],[]),([16,251,0,1,4,5],[],[]),([112,0,1,4,90,5],[101],[]),([253,0,1,4,90,5],[101],[]),([24,181,0,1,2,180],[],[]),([219,254,16,0,1,5],[77],[]),([94,255,0,1,4,5],[77,103],[]),([95,16,0,1,4,87],[90],[0]),([95,112,0,1,4,5],[76],[0,1]),([24,0,1,9,8,7],[24,58],[]),([168,0,1,12,7],[99],[0]),([0,1,55,57],[4,5],[0]),([95,16,0,1,101,5],[],[0,1]),([94,112,0,1,4,5],[76,77],[1]),([139,155,1,2,4,5],[],[0]),([24,0,1,9,34,137],[24,41],[]),([94,16,0,4,102,5],[],[0]),([47,256,0,1,2,5],[],[]),([94,83,0,1,4,87],[15],[]),([95,0,1,98,4,5],[],[0]),([0,1,8,12],[12,13],[0]),([95,16,0,103,4,5],[68,104,105],[]),([94,0,1,158,101,4],[79,80],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_5_0 : checkNodesBT W_17 g_17 F_17 P_17_5 A_17 B_17_4 5 N_17_5_0 = true := by decide +kernel
def N_17_5_1 : List NodeSpec := [([144,0,1,34,3,145],[31,85,106],[0]),([94,16,1,4,159,5],[],[0]),([24,0,1,2,3,258],[],[]),([0,1,6,12,7,99],[12,70,107],[0,1]),([151,24,0,1,2,3],[],[]),([112,0,1,4,11,7],[64],[]),([94,0,1,19,4],[108,109],[0,1]),([148,0,2,137,23,138],[],[0,1]),([95,16,0,1,23,7],[17,31],[0,1]),([16,0,1,259,4,11],[77],[]),([16,0,1,98,23,7],[17,31],[0,1]),([0,1,9,113,214,5],[110],[]),([24,16,0,1],[0,17],[0]),([160,16,0,1,10,7],[15],[]),([219,161,16,0,1,5],[77],[]),([0,1,98,4,5,99],[],[0]),([16,128,0,4,5,99],[97,111,112,113],[]),([112,0,1,4,5,110],[],[0]),([263,0,1,2,3,4],[],[]),([16,0,103,4,5,7],[],[0]),([16,0,1,264,4,5],[],[]),([25,0,1,135,180,3],[63],[1]),([16,0,1,12,7],[15,107],[0]),([112,0,1,9,23,7],[114],[0]),([16,0,1,23,7,99],[17,31,81],[0,1]),([151,0,1,6,12,7],[52,61],[0]),([179,24,0,1,2,183],[115],[]),([16,176,0,1,23,7],[15],[0]),([24,176,0,1,9,6],[24],[0]),([128,0,9,6,23,7],[],[0]),([94,16,0,103,4,5],[],[0]),([24,16,0,1,9],[0,15,17,56],[0]),([16,128,0,4,5,7],[],[0]),([16,176,0,1,4,5],[],[]),([25,24,27,0,2,3],[],[0]),([24,0,1,9,8],[24,58],[0]),([0,1,8,12,7],[12,13,57],[0]),([139,1,2,175,4,5],[],[0]),([0,1,6,79,12,7],[12,70,107],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_5_1 : checkNodesBT W_17 g_17 F_17 P_17_5 A_17 B_17_4 5 N_17_5_1 = true := by decide +kernel
def N_17_5 := N_17_5_0 ++ N_17_5_1
def B_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_5
set_option maxRecDepth 500000 in
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_17) (raw := r_17) (pspecs := ps_17) (used := U_17_5) S_17_ok
  have hm0 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_4_ok C_17_5_0
  have hm1 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_4_ok C_17_5_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_17_6 : List Nat := ([0]++r 2 4++[7,12,13,15,17]++r 24 4++r 29 4++[34,35]++r 38 11++r 52 22++r 76 7++[84,85,87,88,91]++r 93 9++[104,106,107,111,112,113]++r 116 218)
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 12 W_17 r_17 S_17 ps_17 U_17_6
def N_17_6_0 : List NodeSpec := [([0,1,34,136,113,4,5],[65,116,117],[0,1]),([37,36,0,1,3,4,5],[32,116],[0,1]),([156,139,0,1,2,4,5],[],[0]),([191,139,0,1,2,4,5],[],[0]),([139,0,1,2,147,4,5],[29,30,118],[0]),([146,0,34,3,4,5,35],[],[0,1]),([24,0,1,150,2,3,7],[54,62,119],[1]),([24,266,0,1,2,3],[41,47,62,120,121,122],[]),([179,0,1,2,265],[41,47,123],[1]),([179,182,24,0,1,2,3],[41,47,62],[0,1]),([24,267,0,1,2],[0,24,124],[]),([24,0,1,269,3],[41,47,119,125,126],[]),([24,270,0,2,3],[41,44,78,127],[]),([24,271,0,2,3],[41,47,128,129],[]),([179,25,24,0,1,2,3],[24,41,56,63,78],[0]),([181,0,1,186,2,4,5],[],[]),([25,76,24,0,1,2,3],[24,41,56,63,78],[0]),([25,24,0,1,2,180,3],[24,56,63,78],[0]),([24,0,1,150,2,3],([47,62]++r 119 4++[128,130,131]),[1]),([25,24,0,1,2,3,26],[0,56,63,132],[0]),([0,1,2,3,273,7],[133,134],[0,1]),([179,24,185,0,1,2,3],[24,41,78],[0,1]),([181,0,1,2,276],[41,135,136],[]),([24,0,1,277,2,3],[41,62,120,121,122],[]),([24,0,1,34,2,3],([24]++r 42 4++[56,63,78,137]),[]),([24,280,0,1,2],[0,24,138],[]),([24,0,1,149,2,3],[41,47,62,120,121,139],[]),([24,281,0,2,3],[41,44,78,127],[]),([179,24,0,1,34,2,3],[24,41,63,78,140],[0]),([0,1,34,2,137,3,23],[34,141,142],[]),([24,0,1,34,2,137,3],[24,56,63,78],[0]),([144,0,1,34,3],[31,41,85],[0]),([0,1,34,136,3,23],[31,53,65,143,144],[0]),([24,181,185,0,1,2,3],[47,62],[0,1]),([139,0,1,2,137,23],[29,30,34,145,146],[0]),([24,191,0,1,2,137,3],[47,62,122],[]),([191,0,1,34,137,3,23],[147,148],[]),([24,191,0,1,2,3,7],[47,62,119],[0]),([24,191,0,1,2,3],([41,47]++r 119 4++[128,149]),[1]),([191,185,0,1,3,23,7],[141],[0]),([0,1,34,3,145,23,35],[31,106,150],[0,1]),([146,0,34,2,3,23,7],[],[0]),([148,0,2,137,3,23,7],[],[0]),([0,1,40,41,45],[3,151,152,153],[0]),([0,1,42,43,44],[2,154,155,156],[0]),([283,47,0,1,2,5],[35,40,100,157,158,159],[]),([47,0,1,40,44],[25,100,154],[0]),([201,0,1,2,235],[41,88,100],[1]),([195,196,48,0,1,3,4],([38]++r 160 5),[0,1]),([195,0,1,284,4],[38,163,165],[1]),([198,246,47,0,1,2,5],[39,41,100,159,166],[]),([246,0,1,285,5],[25,64,167],[0]),([192,202,47,0,1,2,5],[25,157,158,166],[0]),([198,202,47,0,1,2,5],[41,88,100,157,158],[]),([47,0,200,2,5],[39,87,159],[0]),([202,246,47,0,1,2,5],[25,157,158,159,166],[]),([202,286,1,2,5],[25,87,157,158,168],[]),([274,287,58,0,1,2,4],[169,170],[]),([58,1,2,4,289],[54,171,172],[]),([253,16,0,1,4,5],([73,77]++r 95 4),[0,1]),([16,0,1,4,5,7,110],[64],[0,1]),([0,1,34,3,113,4,5],[173],[0]),([47,0,247,2,5],[39,87,100],[0,1]),([16,0,4,291,5],[73,77,113],[]),([168,0,1,4,5],[15,17,174],[]),([16,0,292,4,5],[64,77,113],[]),([294,47,0,1,2,5],[25,35,40,100,157,175],[]),([58,296,0,2,4],[54,176,177,178],[]),([94,0,1,158,4],[77,79,80],[0,1]),([139,0,1,2,157,4,5],[],[0]),([94,83,0,1,4,5],[54,64,73],[0,1]),([95,94,16,0,1,4,5],[73,179,180],[0,1]),([0,1,9,6,4,5,99],([76]++r 181 4),[0]),([95,16,0,1,4,5],(r 95 4++[185,186]),[0,1]),([16,0,1,98,4,5,7],[17,64,116],[0,1]),([181,0,1,186,2,23,7],[187],[0]),([226,16,0,1,4,5],([15,64]++r 66 4++[101,188]),[0,1]),([16,0,297,4,5],[64,101,104],[]),([24,298,207,0,1,7],[0,24,78,189,190],[0]),([219,16,0,1,4,5,18],[64,73,77],[0,1]),([0,1,9,34,137,4,5],[41,161,191,192,193],[]),([0,1,34,136,145,4,5],[65,116],[0,1]),([16,0,1,4,90,5,7],[15,64,101],[0]),([0,1,9,6,214,11,7],[194],[0]),([94,89,16,0,1,4,5],[15,64,101],[0]),([300,47,0,1,2,5],[35,40,88,100,157,159,195],[]),([95,16,0,1,9,4,5],(r 95 4),[0]),([89,0,1,90,5],[64,101,196],[0]),([24,0,1,9,34,3],[24,41,63,78],[0,1]),([16,0,1,4,225,5],[73,77,97,98,197],[0,1]),([229,0,1,228,2,3,7],[46],[0]),([0,1,4,301,5],[15,17,101,198],[]),([0,1,9,6,259,4,11],[194],[0,1]),([25,24,0,1,2,3],([24]++r 42 4++[56,63,78,199]),[]),([94,16,229,0,1,4,5],[54,64,101],[0]),([0,1,2,3,304],[200,201,202],[]),([0,1,9,241,4,5],[203,204],[]),([192,47,282,0,1],[25,41,100,166],[0]),([165,0,1,9,2,3,4],[84],[0]),([94,83,16,0,1,4,5],[64,73,77],[0,1]),([176,0,1,9,6,4,5],[76],[0]),([181,128,0,9,2,4,5],[111],[]),([0,1,34,136,23],[31,53,65,143,144],[0]),([16,176,0,1,4,5],([15]++r 66 4++[101,205]),[0]),([176,0,1,2,3,214,5],[206],[]),([176,0,1,9,8,4,5],[58,71,205],[0,1]),([94,219,16,0,1,4,5],[64,73,77],[0]),([0,1,9,6,214,5,99],[207],[0,1]),([306,58,0,1,2,4],([176,178]++r 208 4),[]),([0,1,9,6,4,217,11],[194,212],[0,1]),([307,69,58,0,1,2,4],[54,161,178,208,213],[]),([0,1,9,113,4,5],[214,215,216],[0,1]),([58,1,2,309,4],[54,177,213,217],[]),([0,1,34,2,3,276],[41,53,218],[]),([128,0,9,6,4,5,99],[112,183,219],[0]),([139,0,1,140,2,4,5],[29,30,41,54],[0,1]),([181,310,1,9,2,4,5],[220],[]),([16,0,1,214,4,5,11],[54,64,73,221,222],[0,1]),([47,0,1,2,188,5,235],[41,64,88,158,159],[0]),([148,0,2,137,4,5,138],[],[0]),([166,94,16,0,1,4,5],[73],[0]),([16,0,1,4,163,5],([64,73,77]++r 95 4),[0,1]),([246,47,222,0,1,2,5],[25,158,166],[0]),([25,0,1,135,3],[0,63,82],[0]),([89,16,0,1,4,5,11],[64,73,77],[0,1]),([160,176,0,1,2,3,4],[],[0]),([181,0,1,9,242,4,5],[76],[0]),([47,0,1,223,2,5,311],[25,88,158],[]),([312,47,0,1,2,5],[35,40,41,100,157,158,159],[]),([160,0,1,9,6,10,7],[59,93],[0]),([229,0,1,9,8,5,7],[58,71],[1]),([314,0,40,4,44],[154,223,224,225],[1]),([216,16,0,1,4,5,11],[73],[0]),([176,0,1,2,3,23,7],[46],[0]),([69,0,1,2,70],[54,208,226],[1]),([112,16,0,1,4,5,7],[64],[0]),([160,0,1,9,6,4,99],[227],[0]),([16,0,1,248,4,5],[15,64,66,67,101],[0,1]),([16,176,0,1,4,5,7],[15,101,170],[0]),([24,298,207,0,1],[0,24,78,190],[0]),([0,1,2,316,3,317,5],[],[1]),([0,1,9,8,113,4,5],[13,116,228],[0,1]),([24,0,1,2,3,8],([24]++r 42 4++[78,229]),[0]),([181,0,1,9,2,12,7],[48],[0]),([0,1,34,2,318,3,23],[41],[]),([0,320,3,321,44],[230,231,232],[]),([0,1,9,8,4,10,5],[58,71],[0]),([112,16,0,1,4,5],([15]++r 66 4++[101]),[0,1]),([24,176,0,1,2,3,7],[56,233],[]),([24,0,1,2,322,3],[47,62,120,121,122,128,131,234],[]),([0,1,28,54,57],[5,235,236,237],[0]),([191,0,1,189,3,4,5],[],[]),([193,47,0,1,2,5],[35,40,41,100,157,158,159,166,238],[0]),([181,185,0,1,9,4,5],[76],[]),([176,0,1,6,4,5,99],[76],[0,1]),([219,0,1,6,10,5,11],[59,93],[0]),([89,16,227,0,1,4,5],[64,73,77],[1]),([47,323,0,1,2,5,235],[25,88,158,166],[]),([324,47,0,1,2,5],[35,40,41,100,158,159,239],[]),([176,0,1,6,4,10,5],[93],[0]),([325,326,0,1,3,4,5],[],[1]),([327,47,0,1,2,5],[25,35,40,88,100,157,158,159],[]),([160,16,0,1,4,5],[54,66,67,69,101,170],[0,1]),([0,1,2,3,79,7],[107,150,240,241],[0,1]),([0,1,2,3,12,7],([54]++r 242 4),[0]),([246,47,0,1,2,5,311],[25,88,157,158],[]),([16,0,1,23,7],[17,31],[0]),([253,16,0,1,9,4,5],[77],[]),([192,282,314,0,4],[41,224,246],[1]),([181,0,1,2,10,11,7],[54,170,247,248],[]),([24,0,1,9,2,3,99],[0,24,249],[0,1]),([94,0,1,4,90,5],[15,64,101],[0]),([94,16,0,1,4,5],([64,73,77]++r 95 4),[0]),([139,0,1,2,23],[29,30],[0,1]),([24,298,0,1,2,137],[24,41,56,78,250],[1]),([47,293,1,2,311],[25,87,100,251],[]),([152,24,0,1,2,3,7],[24],[0]),([16,0,1,4,10,5,7],[15,64,101,252],[0]),([328,0,1,2,315,3,4],[],[]),([151,0,1,9,2,3,7],[41,61,253],[0]),([16,0,1,4,11,7],[64,73,77,254,255],[0,1]),([329,330,0,1,2,3,4],[],[0]),([216,161,0,1,9,6,5],[256],[0,1]),([0,1,9,6,12,7],[12,70,107],[0]),([151,24,0,1,2,3],([24]++r 42 4++[56,63,78,257,258]),[]),([0,1,34,3,12,7],[52,53,55,150,259],[0]),([160,16,0,1,4,10,5],[15,101,170],[0,1]),([47,237,1,188,5],[87,88,157],[0]),([0,1,331,2,3,240,5],[46],[]),([0,1,9,98,4,5,7],[260,261],[0,1]),([0,1,6,10,11,7],[54,93,170,262,263,264],[0]),([0,1,212,3,332,4,5],[],[1]),([0,1,9,228,6,4,7],[194],[0]),([0,1,2,3,10,11,7],[170,265,266],[0]),([25,24,0,1,2,137,3],[41,47,62,119,122],[0]),([191,0,1,2,137,23,138],[34,146],[0,1]),([333,47,0,1,2,5],[35,40,88,100,157,158,159,166,267],[]),([0,1,9,8,4,11,7],[72,94,268],[0]),([334,47,0,1,2,5],[35,40,100,158,159,166,269],[]),([168,0,1,9,4,12,5],[99],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6_0 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6_0 = true := by decide +kernel
def N_17_6_1 : List NodeSpec := [([24,0,1,335,2,3,7],[62,119],[0,1]),([176,0,1,228,2,3,4],[46],[]),([219,16,0,1,4,5,11],[73,77,170],[0]),([336,204,1,2,5],[25,87,157,158,168],[]),([16,229,0,1,5,7],[15,64,101,270,271],[1]),([152,24,0,1,2,3],([24]++r 42 4++[78]),[0]),([160,0,1,9,6,4,5],[],[0]),([94,16,0,1,4,163,5],[64,73,77],[0,1]),([47,222,0,1,223,2,5],[25,158,166],[0]),([94,16,0,1,101,4,5],[64,73,77,179],[0]),([0,1,337,6,4,5,11],[194,212],[]),([176,338,1,2,3,4,5],[],[]),([198,47,0,1,2,188,5],[41,88,158],[0]),([0,1,9,8,4,5],[58,71],[0,1]),([24,339,0,2,3],[41,47,128,129],[]),([0,1,9,113,4,10,5],[216],[0,1]),([218,0,1,9,4,10,5],[39,272],[0]),([229,0,1,9,8,5],[58,71,228],[]),([24,181,0,1,34,2,3],[24,56,63,78],[0,1]),([16,0,1,337,4,5],([15]++r 66 4++[101,273]),[0]),([16,0,1,4,10,5,99],[15,17,221,274,275],[0,1]),([16,0,1,4,5,99],(r 66 4++[76,214,215,276]),[0,1]),([0,1,9,241,4,240,5],[76,204],[]),([0,1,9,34,137,23,7],[41,81,277],[0]),([0,1,9,113,4,5,99],[214,215],[0,1]),([0,1,9,8,4,11],[72,94,268,278],[0,1]),([58,340,0,2,4],[161,176,177,178,279],[]),([342,47,0,1,2,5],[25,35,40,88,100,157,158],[]),([343,0,1,344,3],[41,280,281,282],[0]),([47,0,345,2,5],[87,100,159],[]),([219,161,0,1,9,6,5],[194],[0]),([128,0,9,2,3,23,7],[283],[0]),([0,1,9,6,4,11,7],[170,212],[0]),([219,252,16,0,1],[15,17,101,284],[0]),([176,128,0,2,3,4,5],[],[]),([16,0,1,9,4,225,5],[73],[0,1]),([16,0,1,9,4,163,5],[54,73],[0,1]),([94,16,0,1,4,10,5],[54,64,101,285],[0,1]),([16,0,1,4,346,5],[64,77,95,96],[]),([94,83,0,1,9,4,5],[54,73],[]),([0,1,9,8,23],[13,31,57,58],[0]),([24,0,1,2,3,347],[24,41,42,43,56,78],[1]),([168,0,1,9,4,5],[15,17,174],[]),([0,1,2,3,79,12,7],[12,107,150,249,286],[0,1]),([25,24,0,1,9,3],[24,41,63,78],[0]),([16,0,1,4,12,5],([15]++r 66 4++[101]),[0]),([16,0,1,9,23,7],[15,17,31,107],[0]),([58,1,2,348,4],[177,208,213,287],[]),([112,0,1,9,4,5],[288],[0,1]),([112,16,0,1,9,4,5],[],[0]),([112,0,1,9,4,5,7],[64,288],[0,1]),([24,181,0,1,9,2],[41,47,62,122,289],[0,1]),([179,182,0,1,2,3,7],[41],[0,1]),([16,0,1,4,5,7,99],[17,116,170,260],[0,1]),([25,24,181,0,1,2,3],[41,47,119,122,244],[0]),([0,1,9,8,23,7],[13,31,57,58],[0]),([58,0,1,28,29],[7,27],[0]),([219,16,0,1,10,5],[15,64,101,290,291],[1]),([16,0,1,9,4,5,7],[15,64,101],[0,1]),([0,1,9,34,137,23],[53,81,193,277,292],[0]),([219,252,16,0,1,9],[15,17,101,284],[0]),([25,24,207,0,1,3],[41,47,62,119],[0]),([246,201,47,0,1,2,5],[39,41,100,159,166,293],[0]),([168,16,0,1,9,4,5],[15],[]),([168,0,1,4,12,5],[99,294,295],[0]),([0,1,6,12,7],[12,70,107],[0]),([24,298,0,1,2,137,7],[24,41],[]),([94,16,0,1,4,5,7],[64,73,77],[0,1]),([0,1,9,6,23,7,99],[31,70,107],[0,1]),([16,0,1,4,5,7],[15,64,66,67,69,101],[0]),([176,0,1,9,6,23,7],[59,81,107],[0]),([24,0,1,9,2,3,7],[24,41,56,63,78],[0]),([24,0,1,272,2,3],([41,47]++r 119 4++[128]),[0,1]),([89,17,16,0,1,4,5],[15,64,101],[0,1]),([24,0,1,9,6,7],[0,24,56,70],[0]),([0,1,6,214,10,5,11],[221],[1]),([257,24,0,1,2,3],(r 42 4++[56,63]),[0]),([128,0,9,6,4,5,7],[296],[0]),([160,0,1,9,6,4,7],[59],[0]),([24,0,1,9,105,2,3],[0,24,56,63,249],[0,1]),([349,48,350,0,4],[26,163,297,298],[1]),([0,1,9,8,4,5,99],[13,64,116],[0,1]),([0,1,9,113,4,5,7],[76,299],[0]),([112,176,0,1,9,4,5],[76],[0]),([198,47,323,0,1,2,5],[25,88,158],[]),([160,161,0,1,9,2,3],[],[0]),([112,0,1,9,8,4,5],[228],[0,1]),([307,0,1,295,4],[27,64,300],[1]),([0,1,9,8,4,5,7],[58,71,76],[]),([24,0,1,9,2,3],([24]++r 41 4++[56,63,78]),[0]),([181,0,1,2,12,7],[48,91,146],[0]),([16,0,1,4,240,5],([39]++r 301 4),[0]),([151,0,1,2,3,12,7],[52,55,61,305],[0,1]),([0,1,2,3,12,7,99],[12,52,107,150,249],[0,1]),([24,0,1,335,2,3],([47,62]++r 119 4++[128,131]),[0,1]),([151,0,1,2,3,7],[61,253,306,307],[0]),([176,0,1,2,3,12,7],[46,52,55,107,150,233],[0]),([24,0,1,351,2,3],(r 42 4++[56,63,308]),[0]),([58,1,2,353,4],[54,177,208],[]),([24,0,1,351,2,3,7],(r 42 5),[0]),([179,24,0,1,9,2],[41,47,62,122],[0]),([95,16,0,1,4,5,7],[17,64,116],[0,1]),([121,0,1,9,2,3,7],[60,309,310],[0]),([160,0,1,6,4,10,11],[170,194],[]),([354,0,1,308,4],[27,54,178],[1]),([151,176,0,1,2,3,7],[46,311],[0]),([192,47,0,204,1,2,5],[25,158,166],[0]),([24,176,0,1,2,3],([24]++r 42 4++[56,78,233]),[]),([24,176,0,1,9,2,3],[24,41,78],[0]),([181,0,1,9,34,23,7],[41,53,81],[0]),([192,356,48,0,1,3,4],(r 312 4),[]),([24,0,1,9,34,3,7],[24,41,78],[0]),([0,1,9,2,206,23,7],[142],[0]),([181,185,0,1,9,23,7],[41,142],[0]),([24,357,0,2,3],[24,44,78,127],[]),([151,24,0,1,9,2,3],[24,41,56,63,78],[0]),([0,1,9,105,2,3,7],[56,63],[0]),([151,24,0,1,2,3,7],[],[0]),([25,24,0,1,9,3,7],[24,41,244],[0]),([198,199,47,0,1,2,5],[39,41,64,100,159,166,316],[0]),([257,24,0,1,2,3,7],(r 42 4),[0]),([179,24,0,1,9,2,7],[41,47],[0]),([24,0,1,34,2,3,145],[0,56,63,317],[0,1]),([24,0,1,9,6],[0,56,70],[0]),([176,0,1,2,206,4,5],[76],[]),([287,58,0,1,2,4],([161,176,178]++r 208 4++[213]),[]),([24,0,1,2,3,8,7],[24,229],[0]),([343,358,30,0,1,3,5],[41,244,282,318,319],[]),([168,16,0,1,4,5],([15,17]++r 66 4++[101,174]),[]),([24,0,1,2,322,3,7],[62],[]),([24,0,1,272,2,3,7],[41,119,122],[0,1]),([24,181,0,1,9,2,7],[41,47,122],[0]),([0,1,34,3,215,23,7],[147],[0]),([89,17,0,1,9,4,5],[],[0,1]),([359,30,0,1,3,5],([282]++r 318 7),[]),([360,24,0,1,2,3],[47,62,120,121,122,128,131],[]),([360,24,0,1,2,3,7],[62],[]),e6 [176] [],([176,0,1,6,4,11,7],[170,194],[0]),([25,24,207,0,1,3,7],[41,62],[]),([24,0,1,269,2,3],[41,47,62,120,121,125],[]),([362,364,0,1,2,4,5],[],[]),([0,1,6,4,10,11,7],[59,93],[0]),([354,69,58,0,1,2,4],[54,64,161,178,208],[]),([343,365,30,0,1,3,5],[41,164,244,282,318,319],[]),([58,366,0,2,4],[54,161,176,177,325],[]),([160,0,1,9,6,4,11],[194],[0]),([367,58,0,1,2,4],([27,64,161,176,178]++r 208 4),[]),([24,0,1,149,3],[41,47,119,139,326],[]),([0,1,34,2,137,145,23],[292],[]),([198,0,1,2,368],[41,88,327],[1]),([274,290,30,0,1],[41,282,328],[0]),([24,357,0,2,3,7],[24,44,78,127,329],[]),([0,1,55,29,56],[4,330,331],[0]),([58,370,0,2,4],[41,54,171,332,333],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6_1 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6_1 = true := by decide +kernel
def N_17_6 := N_17_6_0 ++ N_17_6_1
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_17) (raw := r_17) (pspecs := ps_17) (used := U_17_6) S_17_ok
  have hm0 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_5_ok C_17_6_0
  have hm1 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_5_ok C_17_6_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_17_7 : List Nat := ([0,2,3,4,7,12,13,15,17]++r 24 4++[29,30,31,34,35,36]++r 38 10++[52,53,54,56,58,59]++r 62 9++[73,76,77,78,81,87,88,93]++r 95 4++[100,101,106,107,116,117,118,120,121,128,131,132,134,137,138,139,142,146,147,149,150,151,153,155]++r 157 10++[170,172,176,178,179,180]++r 189 6++[202]++r 205 11++[219]++r 221 5++[228,229]++r 231 5++[237,244,246]++r 248 5++[256,259,260,262,265,266]++r 273 6++[282,284,289,292,294,297,308,309]++r 317 7++[326,329,331]++r 333 582)
def P_17_7 : BT (Option BoundPool) := buildPoolsSubBT 12 W_17 r_17 S_17 ps_17 U_17_7
def N_17_7_0 : List NodeSpec := [a6 [181,185] [76,334] [0,1],a6 [272,7] [41,161,170,206,265,335] [0,1],([181,0,1,186,2,4,5],[41,54,252,334,336],[]),([181,371,1,2,3,4,5],([41,334]++r 337 8),[]),u6 [34,318] [41],e6 [318] [41,76,117,337,345,346,347],([0,1,34,136,3,4,5],[41,65,116,117,348],[0]),([139,0,1,2,137,4,5],[118,161,349,350,351],[0]),([191,0,1,2,137,4,5,138],[118,350],[0]),([191,185,0,1,3,4,5,7],[265,334,352],[0]),([0,1,34,2,137,145,4,5],[170,265,353,354],[0]),([0,1,34,3,145,4,5,35],[106,116,355],[0,1]),([146,0,34,2,3,4,5,7],[356,357],[0]),e6 [34,137] [117,170,265,334,353,358,359],([179,24,0,1,2,3,7],[41,47,62,120,121,360],[0,1]),([25,24,0,1,2,3,7],([0,24]++r 41 5++[78,244,361]),[0,1]),([24,0,1,2,135,3],[0,24,41,362,363],[0,1]),([25,24,0,1,2,3],[0,24,41,42,43,45,63,78,132,361],[0,1]),([181,185,0,1,2,3,23,7],[41,142,147],[0,1]),([0,1,272,2,3,23,7],([134,142,147,335]++r 364 4),[0,1]),([279,24,0,1,2,3],[0,24,41,42,43,63,368],[0,1]),([279,185,0,1,3,23],[31,41,277],[1]),([0,1,277,2,3,23,7],([41,142,146,147]++r 364 4++[369]),[0]),([179,24,0,1,2,3],[41,47,62,120,121,128,131,360,370],[0,1]),([0,1,34,2,3,23,7],([41,81,107,137,150,277]++r 371 4),[0]),([24,0,1,2,3,35],[0,24,41,363,375],[0,1]),([280,0,1,2,23,7],[31,41,81,138,376],[0]),([0,1,149,2,3,23,7],([41,139,142,147,326]++r 364 4),[0,1]),([339,0,2,3,23,7],[41,142,367,377,378,379],[0]),([24,0,1,34,2,3,7],[0,24,41,42,43,78,380,381],[0,1]),([24,0,1,34,2,3],[0,24,41,63,317,381],[0,1]),([0,1,34,2,137,3,23],[41,53,54,277,292,359],[0,1]),([0,1,34,3,23,35],[31,106,150,382],[0,1]),([181,0,1,2,136,4,5],([252,334,342]++r 383 5),[]),([191,0,1,2,3,23,7],([134,142,146,147,149]++r 364 4++[388]),[0]),([0,1,34,2,3,145,23,7],[31,41,107,150,317],[0,1]),([372,374,1,3,4,5],(r 389 5),[]),([192,355,47,0,1,2,5],([39,41,161,170]++r 394 6),[1]),([192,376,48,0,1,3,4],([38,64,161]++r 400 5),[]),([47,0,1,2,377,5],[39,64,398,405,406],[]),([191,0,1,2,137,3,23,7],[41,142,146,147],[0]),([47,0,1,2,5,378],[39,161,405],[]),([47,0,1,379,2,5],[39,41,161,395,399,407],[]),([47,0,1,2,380,5],[39,41,397,407,408],[]),([47,0,381,1,2,5],[39,41,64,161,395,397,398,405,407],[]),e6 [192,383] [170,409,410],([0,1,384,2,137,4,5],[41,161,260,411,412],[]),([0,1,40,41,43,44],[151,155,413,414],[0,1]),([0,1,2,42,43,5],([2]++r 415 4),[0]),([375,48,0,1,3,4],[26,36,38,160,163,297,419,420,421],[1]),([192,47,0,1,2,5],[25,39,41,100,157,158,166],[0]),([47,0,1,2,5,44],[25,39,41,100,422],[0]),([47,0,1,2,368,5],[39,64,88,159,423],[0]),([198,47,0,1,2,5],[39,41,64,88,100,157,158,159],[0]),([47,0,1,2,5,235],[39,41,64,88,158,159],[0]),([47,0,1,2,285,5],[25,39,41,100,424],[0]),([47,286,0,1,2,5],[25,39,88,157,158,159,425,426],[0]),([202,47,0,1,2,5],[25,39,40,41,64,87,88,100,157,158,159,425,427],[0]),([0,1,2,386,3,4,385],([170,206]++r 428 5),[]),([16,229,0,1,4,5],[15,17,64,76,101,433],[0,1]),([181,0,1,9,2,4,240,5],[161,170,434,435],[0]),([216,161,0,1,9,2,3,5],[161,256],[0,1]),([160,0,1,9,2,3,4,99],[436],[0]),([47,387,0,1,2,5],[39,206,395,396,398,405,407,437],[]),a6 [176,99] [276,438,439,440] [0,1],([0,1,9,228,2,3,4,7],[39,161,441],[0]),([89,16,0,1,4,5],([15,17,64]++r 66 4++[101,442]),[0,1]),e6 [389,7] [41,170,206,363,443,444],([298,207,0,1,23,7],[31,81,189,190,277],[0]),([290,30,0,1,3,5],[244,282,319,320,321,323,445,446],[0,1]),([181,0,1,9,2,4,5,99],[334,447,448,449],[0]),([0,1,34,136,4,5],[41,65,116,117,348],[0]),([219,161,0,1,9,2,3,5],[161,450,451],[0]),([390,391,2,3,4,5],[244,452,453],[]),e6 [176,392] [337,454],u6 [9,99] ([76,334]++r 455 4),([343,278,30,0,1,3,5],([41,164,244]++r 459 9),[]),u6 [337,11] [161,441,468,469,470],([274,278,58,0,1,2,4],[41,54,64,170,471,472],[0]),([0,1,9,2,3,4,11,7],[46,170,265,450],[0]),([229,0,1,2,3,240,5],[46,170,265,473,474,475],[0]),([181,393,0,1,9,2,4,5],[41,161,476],[]),([160,0,1,9,2,3,4,7],[161,477],[0]),u6 [176,10] [233,266,274,478,479],([0,2,394,210,4,5],([415]++r 480 4),[]),([160,0,1,9,2,3,10,7],[479,484,485],[0]),([181,0,1,9,2,4,11,7],[41,170,248,350,486,487],[0]),([176,0,1,2,3,4,11,7],[170,350,441,450,486,488,489,490],[0]),([192,282,0,313,210,4],[41,491,492],[0,1]),([349,48,0,1,3,4],[26,38,163,419,420,493,494],[0,1]),([274,290,340,0,2,4],[164,495,496,497],[0]),([219,0,1,9,6,4,5,11],[170,194,212],[0]),([395,0,1,9,4,5],[54,93,498],[0]),([372,357,0,3,4,5],[329,390,391,499,500],[]),([338,1,9,2,3,4,5,99],[214,501,502,503],[0]),e6 [337,396] [337,504],([354,58,0,1,2,4],[27,54,64,161,176,178,208,209,210,505],[0,1]),([160,0,1,2,3,4,10,11],[161,170,441],[0]),([0,1,2,3,4,10,11,7],[170,265,479],[0]),([0,1,6,4,10,5,11],[59,93,170,506,507,508],[0,1]),([24,0,1,397,2,3],[0,24,41,63,509,510],[0,1]),e6 [160,396] [337,504,511],([219,0,1,9,6,10,5],[59,70,93,170,273,512,513,514],[0,1]),([219,0,1,2,396,3,10,5],[161,479,515],[]),([219,252,298,207,0,1],[189,284,516,517,518],[0]),([0,1,2,55,4,56],[4,331,519,520,521],[0]),([47,0,1,40,2,5],[25,39,41,88,166,415],[0]),([298,207,0,4,291,5],(r 522 5),[0]),([47,0,1,2,5,311],[25,87,88,100,158],[0]),([58,0,1,2,352,4],[7,54,64,178,527],[0,1]),([47,293,0,1,2,5],[25,39,100,157,425,528],[0]),([192,282,0,319,3,321],[41,246,529,530],[1]),([0,1,2,396,3,4,11,7],[164,265,531,532,533],[]),e6 [398,7] [41,54,206,265,534,535],e6 [399,400] ([41]++r 536 4),([372,401,0,3,4,5],[390,391,499,540,541],[]),e6 [402,322] [346,347,542,543],([160,0,1,9,6,4,5],([59,93,170]++r 544 6),[0,1]),([181,0,1,2,403,4,5,7],[41,161,170,550],[]),([336,47,0,1,2,5],[25,35,39,88,157,158,159,425,551],[0]),e6 [405,7] [76,334,552,553],([0,1,9,6,4,5,99],([214,215,276,440]++r 544 4),[0,1]),([191,0,1,188,3,4,5,7],[149,554,555],[0]),([274,290,370,0,2,4],([497]++r 556 5),[0]),u6 [315,317] ([161,206]++r 561 5),([0,1,406,3,4,407,5],(r 566 6),[]),([274,278,290,305,0,1],[41,64,572,573],[0,1]),([0,1,9,2,3,214,11,7],[441,574],[0]),([58,0,1,2,4,70],[7,54,64,161,178,575,576],[0]),e6 [408,34] ([265,334,358]++r 577 4),([0,2,320,3,321,5],([232,529]++r 581 4),[0]),e6 [409,378] ([41,161,265,347]++r 585 4),([192,314,0,2,4,5],([224,225]++r 589 5),[0]),([219,0,1,2,3,303],[41,594,595,596],[0]),e6 [412,7] [170,597],u6 [8] [46,191,192,229,337,345,346,347],([298,0,1,4,413,5],[244,526,598],[0]),([0,1,9,2,3,23,7],([41,81,107,150,277]++r 371 4++[599]),[0]),([414,391,2,3,4,5],[41,494,528,600,601],[]),([0,1,9,2,3,259,4,11],[170,265,441],[0]),([0,1,9,6,4,240,5],([434]++r 602 6),[0]),e6 [415,176] [346,347,608],([181,185,0,1,9,4,5],[41,76,161,334,534,609],[0,1]),([0,1,2,416,43,5],[151,155,528,610,611],[1]),([0,1,9,2,3,214,5,99],[207],[0,1]),e6 [418,417] [334],([375,238,1,3,4,5],([419,421]++r 612 5),[1]),([237,1,188,41,43,5],([610]++r 617 4),[0,1]),([191,0,1,34,137,3,4,5],[621,622,623],[0]),e6 [420,7] [46,170,206,624],([181,176,0,1,9,2,4,5],[41,334,625],[0]),e6 [421,7] ([76,337]++r 626 5),([293,1,2,41,43,311],[155,620,631,632,633],[0,1]),e6 [409,422] [41,161,265,347,587,634,635,636],e6 [176,391] [205,252,337,345,346,347,355,502,637,638],([0,409,2,3,4,5,423],([161]++r 639 8),[]),e6 [396,99] ([337,504]++r 647 4),([0,1,2,3,214,10,5,11],[41,161,221,265],[0]),([24,181,0,1,2,3],[41,47,62,651,652,653],[0,1]),([274,290,1,2,4,289],[560,654,655,656],[0]),([0,1,40,3,4,45],[3,153,161,231,414,657,658],[0]),([314,0,40,2,4,5],[41,224,225,415,449,584,659],[0]),e6 [424,7] [76,337,660,661],([349,350,0,40,4,44],[223,414,662,663,664],[0]),e6 [34,426] ([265,334,622]++r 665 4),([0,1,9,34,137,4,5],[41,117,161,193,260,354,358,669],[0]),e6 [428,34] [265,334,622,667],u6 [160,9] [41,206,266],([429,391,2,3,4,5],[41,670,671,672],[]),([148,0,2,137,3,4,5,7],[673,674],[0]),e6 [181,189] [76,170,252,338],e6 [160,430] [347,457,675,676],([58,0,1,308,2,4],[27,54,64,161,208,677,678],[0]),([0,1,2,3,8,23],[31,81,229,679],[0]),u6 [330,260] [41,46,680,681,682],([229,227,0,1,2,3,7],([46,170,206,265]++r 683 4),[0,1]),([0,1,9,6,214,4,5,11],[194,212,221,222,687,688],[0,1]),a6 [34,211] ([265,334,349,622]++r 689 4) [1],([357,0,2,3,23,7],[81,277,329,374,693,694],[0]),([293,1,2,3,4,431],([41]++r 695 4),[]),([160,0,1,9,6,4,10,5],[59,93,170,549],[0,1]),([0,1,2,3,10,11,7],[170,252,262,265,355,479,484,699,700,701],[0,1]),([192,349,282,350,0,4],[41,492,663,702],[0]),([16,0,1,9,23,4,5],[15,17,64,221,498,703],[0]),e6 [432,7] [41,221,502,704,705,706],([0,1,9,2,3,4,217,11],[170,265,441,470,707],[0]),([0,1,9,8,4,5],[13,58,116,228,708],[0,1]),([47,237,0,1,2,5],[25,39,88,157,709],[0]),([340,0,2,54,4,56],([495]++r 710 6),[0]),([176,0,1,9,2,3,23,7],[41,81,107,150,233,277,484],[0]),([0,1,2,3,4,433,11],[41,170,531,716,717,718],[]),([16,0,1,4,10,5],[15,17,64,275,719],[0,1]),([229,0,1,9,6,5,7],[59,93,252,720,721,722],[0,1]),e6 [435] [46,76,206,334,337,345,347,723],([181,227,0,1,9,2,4,7],[41,161,170,248,289,724],[]),([181,0,1,9,2,10,5,7],[161,170,252,725,726,727],[0]),u6 [316,315] [64,161,164,206,562,563,564,728,729,730],([58,0,1,28,2,4],[7,27,54,64,213,519],[0,1]),([24,298,0,1,2,3],[0,24,41,63,731,732],[0,1]),([343,30,0,1,3,5],[41,164,244,282,319,320,322,466,733],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7_0 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7_0 = true := by decide +kernel
def N_17_7_1 : List NodeSpec := [([0,1,2,436,3,417,5],([46,170]++r 734 4),[]),e6 [437,399] [41,46,539],a6 [438,189] [76,170] [1],([0,345,2,41,43,5],([155]++r 738 4),[0]),([246,47,0,1,2,5],[25,39,41,64,100,157,158,159],[0]),([0,1,9,6,4,10,5,7],[59,93,170,252,274],[0]),e6 [439] [170,346,347,428,430,742,743,744],([47,222,0,1,2,5],[25,39,64,87,100,158,251],[0]),e6 [420] [46,76,206,265,334,347,350,624,745,746,747],([274,0,1,2,399,4,5],([54,170,536]++r 748 5),[]),u6 [329,260] [41,46,680,753,754],a6 [212,211] [265,334,690,755,756,757] [0,1],([0,2,440,3,441,4,5,361],[41,758,759,760],[]),([128,0,9,2,3,4,5,99],[457,503,761,762],[0,1]),u6 [325,211] [265,334],([216,0,1,9,6,4,5,11],[212,763],[0]),e6 [176,240] [206,764],([229,176,0,1,2,3,5,7],[46,170,206,233],[1]),([0,1,149,3,23,7],[41,134,139,142,326],[0,1]),e6 [435,7] [46,170,206,765],([0,1,9,34,3,4,5,7],[41,64,161,191,259,334],[0]),([442,0,1,2,444,3,443,5],(r 766 4),[]),([24,181,0,1,2,3,7],[41,47,62,120,121,651,652],[0,1]),([24,0,1,9,2,3,7],([0,24]++r 41 4++[56,63,249,484,770]),[0,1]),([181,0,1,9,2,4,5,217],[41,170,771,772],[0]),([219,0,1,2,3,10,5,11],[170,479,484],[0]),e6 [445,361] [206,773],([0,1,34,2,137,3,23,7],[41,81,107,150,277],[0]),([181,229,0,1,9,2,5,7],[41,161,170,720,726,727],[]),([16,0,1,4,90,5],[15,17,64,774,775],[0,1]),a6 [189,232] [76,161,170,358,577,776,777,778] [1],([94,16,0,1,4,5],[64,73,77,95,97,179,180],[0]),e6 [176,388] [164,337,554,779,780,781],([144,0,1,2,3,7],[31,41,46],[0]),([16,0,1,85,4,5],[15,17,64,449,782],[0,1]),([192,282,0,1,41,43],[41,155,492],[0,1]),([341,47,0,1,2,5],[25,39,88,100,157,158,159,251,425,783],[0]),([0,1,9,6,4,5,7,99],[70,116,252,784],[0,1]),([16,0,1,4,5,7],[15,17,64,116,708],[0,1]),([24,0,1,9,2,3],[0,24,41,56,63,249,770],[0,1]),([219,16,0,1,4,5],[15,17,64,66,67,69,101,785],[0,1]),([89,16,0,1,9,4,5],[15,64,66,67,101,442],[0,1]),([94,16,0,1,9,4,5],([54,64,73,77]++r 95 4++[179]),[0]),([219,16,0,1,9,4,5],[15,17,64,66,67,69,101,273,785],[0,1]),([0,9,6,4,291,5],[194,219,221,522],[0]),([192,282,446,1,3,4],[41,786,787],[1]),([192,355,375,282,0,1],[41,161,788,789],[0,1]),([0,1,9,6,4,12,5],[59,70,294,703],[0]),([58,0,1,2,369,4],[54,161,172,790,791],[0]),e6 [176,447] [206,337,345,781,792],([0,1,9,6,23,7],[31,59,70,107],[0]),([0,1,2,3,448,7],[41,150,368,793,794],[1]),([0,1,9,337,6,4,5],[70,273,544,545,795],[0]),e6 [449,7] [46,170,206,796],([314,0,2,4,5,44],[41,224,225,422,797,798],[0]),([0,1,9,6,4,5,7],([59,93,170,191]++r 544 4),[0,1]),u6 [8,7] [76,229,799],([219,252,0,1,9,6],[59,70,93,284],[0]),([219,0,1,2,3,451],[41,800,801,802],[]),([181,0,1,9,2,23,7],[41,142,146,147,289],[0]),([0,1,9,2,3,12,7],[12,52,107,150,249,770],[0,1]),([0,1,351,2,3,23,7],([107,150,308]++r 371 4),[0]),([16,0,1,9,4,5,7],[15,17,64,116,252,260,708],[0,1]),([219,252,357,0,2,3],[329,500,517,518,803,804],[0]),([47,0,204,1,2,5],[25,39,41,64,88,100,158,159],[0]),([176,0,1,2,3,23,7],([46,81,107,150,233,277]++r 371 4++[781,805]),[0]),([181,0,1,9,2,4,5,7],[41,64,161,170,289,806],[0]),e6 [9,453] ([41,161,170]++r 807 6),([47,323,0,1,2,5],[25,87,88,158],[0,1]),([0,1,9,34,3,23,7],[41,53,81,150,259,277],[0]),([181,0,1,9,2,4,5,388],[41,161,342,726,813,814],[]),e6 [439,385] [428],([372,454,1,3,4,5],(r 815 5),[]),([181,0,1,186,2,4,5,7],[41,54,170],[0]),e6 [176,402] [347,426,608,820],e6 [176] [46,76,206,334,337,345,346,347],u6 [176,7] [46,170,206],([0,1,9,6,4,10,5,99],[59,70,221,275,440],[0,1]),([0,1,9,34,137,4,5,7],[41,161,193,260,353,358,552,669],[0]),([181,0,1,9,34,4,5,7],[41,117,161,260,342],[0]),([47,0,1,2,188,5],[39,41,87,88,158,159],[0]),e6 [456,385] [41,265,345,431,821],([181,281,0,2,3,4,5],([41,334,342]++r 822 6),[]),([0,1,9,6,4,11,7],[194,212,278,350,828],[0,1]),([457,0,1,2,3,23],[41,202,829,830],[0]),([181,185,0,1,9,4,5,7],[41,161,248,349,831],[0]),([274,30,0,1,3,5],([41,244,282]++r 318 4++[832]),[0,1]),([58,0,1,2,4,29],[7,27,54,161,833],[0]),u6 [351,7] ([46,206,308]++r 834 4),([0,1,28,3,57,5],([41,237]++r 838 4),[0]),u6 [176,9] [41,76,334],([357,0,2,3,4,5,7],[191,192,329,347,836,842,843],[]),([279,0,1,2,137,3,23],[34,41,142,147],[0,1]),([0,1,2,3,8,23,7],([31,81,229]++r 371 4++[679]),[0]),([0,1,6,4,12,5],[59,70,93,294],[0]),([24,0,1,2,3,6],[0,24,41,363,844],[0,1]),([0,345,2,3,4,385],[429,430,431,740,845,846],[]),([16,0,1,23,4,5],[15,17,64,449,498],[0,1]),e6 [449] ([46,76,206,334,346,347,796]++r 847 4),([0,1,9,8,4,5,7],[13,58,116,228,708],[0,1]),([24,0,1,2,3,6,7],[0,24,41,42,44,363,844],[0,1]),u6 [12] [206,337,345,346,347,599,851,852,853],([274,290,0,1,28,29],[41,559,854],[0]),([219,252,0,1,9,2,3],[518,599,804,853,855,856,857],[0]),([298,207,0,1,4,5,7],([189,191,192]++r 858 4),[0]),([0,1,2,322,3,23,7],([142,146,147,234]++r 364 4),[0]),([298,0,1,2,458,4,5,7],[41,76,862,863,864],[]),([298,0,1,2,137,23,7],[41,81,107,250,277,292],[0,1]),([24,298,0,1,2,3,7],([0,24]++r 41 4++[63,731,732]),[0,1]),([198,355,47,0,1,2,5],([39,41,64]++r 395 4++[405]++r 865 4),[]),e6 [322,459] [244],([181,0,1,34,2,3,23,7],[41,81,107,150,277],[0,1]),([128,0,9,2,3,4,5,7],[41,161,869,870],[0,1]),([0,1,2,3,12,7],[12,52,107,150,249,770],[0,1]),e6 [460,7] [334,871,872],([58,0,1,2,295,4],[27,54,161,208,873],[0]),([0,1,34,3,215,4,5,7],[622],[0]),([160,0,1,9,2,3,4,11],[441,874],[0]),e6 [322,7] [234,334],([298,0,1,2,137,4,5,7],[41,76,250],[]),([139,0,1,2,4,5],[29,30,161,351],[0,1]),([201,47,0,1,2,5],[39,40,41,64,88,100,157,158,159,426,875],[0,1]),([0,28,3,461,29,5],[854,876,877,878],[1]),u6 [9,7] [41,161,170,191,206,265,334,599],([0,2,3,462,4,5],([54]++r 878 5),[]),([274,290,1,2,348,4],[41,883,884],[0]),u6 [364,361] [41,170,345,885,886],u6 [362,363] [76,337,887],([47,0,1,223,2,5],[25,39,41,64,100,158],[0,1]),([176,0,1,9,6,4,5],([59,93,205,252]++r 544 4),[0,1]),([0,2,3,441,4,5,361],[170,759,760,888,889,890],[]),e6 [176,396] [337,504],([0,1,9,2,206,4,5,7],[248,349,350],[0,1]),([307,58,0,1,2,4],([27,54,64,161,178]++r 208 4++[213,891,892]),[0,1]),([69,58,0,1,2,4],[7,54,64,161,176,178,208,210,211,893],[0]),([0,1,28,54,29,56],[235,840,854,894],[0,1]),([0,2,3,463,4,5],([244]++r 895 6),[]),([281,0,2,3,23,7],[41,277,374,694,826,901],[0]),([195,48,0,1,3,4],([36,38]++r 160 6++[297,419,420]),[0,1]),([0,1,464,2,137,4,5],[41,260,902,903,904],[]),([58,0,1,465,2,4],[54,161,170,172,790,905,906,907],[]),([176,0,1,9,6,4,5,7],[59,93,170,205,252,260],[0,1]),([58,0,1,2,4,422],[41,54,908,909,910],[]),([0,1,2,396,3,10,5,7],[164,265,515,911],[]),([58,0,1,2,288,4],[54,64,333,909,912],[0]),([0,1,9,2,3,23,7,99],[31,81,107,150,249,309],[0,1]),([274,307,58,0,1,2,4],[54,161,172,333,790,891,892,913,914],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7_1 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7_1 = true := by decide +kernel
def N_17_7 := N_17_7_0 ++ N_17_7_1
def B_17_7 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_7
set_option maxRecDepth 500000 in
lemma B_17_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 7 xs.toFinset) B_17_7 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_17) (raw := r_17) (pspecs := ps_17) (used := U_17_7) S_17_ok
  have hm0 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_6_ok C_17_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_6_ok C_17_7_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_17_8 : List Nat := ([31,38,39,41,46,54,59,64,70,76,81,93,106,107,116,117,118,138,139,142,147,150,151,154,155,161,164,170]++r 189 4++[202,205,206,214,221,222,223,229,231,233,234,235,244,246,249,250,252,259,260,265,266]++r 273 4++[278,284,289,294,308,317,326,328,329,331,334,335,337,338,342,345,346,347]++r 349 7++[358,359]++r 363 6++r 371 6++[380,381,383,388,391,394,410]++r 413 4++[418,419,421,422,426]++r 428 4++[433,434,439,440,441,445,446,448,449,450,452,453,454,457,458,468,470,471,472]++r 476 6++[484,486,489,491,492,494,495,497,498,500,501,502,504,506]++r 514 4++[519,520,522,523]++r 528 4++[533,534,536,537,538]++r 543 7++[552,554,556,557,559,562,564,565,566,569,570,577,579,582]++r 584 6++[591,593,594,599,600,606,609,610]++r 616 5++[622,627]++r 630 7++[639]++r 642 5++[649]++r 651 4++[656,657,659,660]++r 662 4++[667,670,671,679,680,681,683,684,687,688,689,691,696]++r 702 8++[715,718,719,720,731,732,734,735,736,739,740,741,748,749,755,758,761,763]++r 766 5++[773]++r 778 4++[783,785,786,787,789,791,792,794,795,797,798,801]++r 804 4++[809,811,812,813,815,818,819,821,823,827]++r 832 14++[851]++r 853 9++[863,872,876,878,879,883,884,885,887,896,905,906,908,910,911,912]++r 915 1252)
def P_17_8 : BT (Option BoundPool) := buildPoolsSubBT 12 W_17 r_17 S_17 ps_17 U_17_8
def N_17_8_0 : List NodeSpec := [([279,185,0,1,3,4,5],[41,116,164,358],[0,1]),([280,0,1,2,4,5,7],[116,138,260,376,708,915],[0]),a6 [149,7] [139,161,265,326,334,351,543,665,689,916,917] [0,1],a6 [181,35] ([41,334,338,342,383,652,653,823]++r 918 6) [0,1],a6 [34,145,7] [41,116,252,317,353,355,924] [0,1],u6 [34,7] ([41,46,206,252,260,334,353,355,358,380,554,577,579]++r 925 5),u6 [181,393] ([64,161,337,338,342,363,476,823]++r 930 6),a6 [466,7] [41,46,221,334,349,350,489,665,755,916,936,937,938] [1],u6 [181,388] ([41,64,338,342,779,780,813,823,933,935]++r 939 4),([279,0,1,2,3,23,7],[31,41,81,150,368,371,372,373,794],[0,1]),([0,1,2,3,23,7,35],[31,41,81,363,375,922],[0,1]),([372,0,1,467,3,4,5],[265,391,943,944],[]),e6 [468] [46,76,345,346,421,945,946,947],e6 [470] ([54,170,347]++r 948 4),e6 [192,471] ([39,41,170,265,334,394,410]++r 952 6),([372,0,1,3,373,4,5],[265,391,958,959],[0]),e6 [192,137] ([38,41,206,260,354,394,410,660]++r 960 6),([192,446,1,2,3,4,5],[206,410,591,786,964,966,967,968],[0]),e6 [472] [41,46,76,337,345,967,969],e6 [192,355,473] [41,161,394,970],([192,355,375,0,1,2,5],([39,41,161,170,394,789]++r 971 4),[0]),([192,48,0,1,3,4],[38,41,46,64,265,419,933],[0,1]),([192,282,0,1,3,4,474],([41,161,265,492]++r 975 4),[1]),([192,282,0,1,475,3,4],([64,161,265,492,702,976]++r 979 4),[1]),e6 [379,7] ([38,41,46,161,170,206,252,260,265,355,554,577,926,927]++r 983 6),e6 [192,477] [39,161,170,265,589,989],([192,282,0,478,1,3,4],([265,492,702,978,981,982]++r 990 4),[1]),([0,1,479,3,4,5,44],[265,422,994,995],[]),e6 [219,475] ([64,170,265,468,979]++r 996 12),([480,0,1,2,3,4,7],[41,64,161,260,1008],[]),([192,282,0,1,3,4,43],[64,161,657,976,1009],[0,1]),e6 [481] ([39,41,46,347]++r 1010 4),e6 [219,482] ([161,334,468,1003,1004,1005]++r 1014 7),u6 [384,7] ([38,161,206,260,265,355,538,554,577,926,927]++r 1021 5),([375,0,1,2,482,4,5],[41,170,334,1014,1026],[]),e6 [483] [76,265,337,415,616,1027,1028,1029],u6 [277,7] [41,64,161,170,265,349,350,665,916,1030],a6 [42] ([265,415,418]++r 1031 4) [0,1],([192,0,1,2,41,43,5],[41,76,151,155,610,617,967],[0]),([0,1,40,2,41,43,5],[41,151,155,415,617,1029],[0]),a6 [484,385] [41,170,428,431,821,933,1035,1036,1037] [1],([375,0,1,2,3,443,5],[46,265,415,582,616,766,767,1028,1038,1039],[1]),e6 [486] ([54,170,347]++r 1040 6),e6 [192,355] ([39,41,170,265,588,970]++r 1046 6),e6 [274,479] ([54,170,206,265,636,995]++r 1052 9),e6 [274,34] [41,54,117,206,358,380,579,636,925,928,929,1056,1058,1059,1061],e6 [487] [337,345,346,347,472,1062,1063,1064],([274,278,290,0,1,2,4],[41,54,64,170,471,472,559],[0,1]),e6 [488] [54,206,244,334,337,345,1065],e6 [274,489] [54,64,170,636,1058,1059,1066],e6 [490] [39,347,970,1067,1068,1069],([0,1,2,3,4,491,7],[161,265,489,1070,1071],[]),([274,290,0,1,465,2,4],[54,161,170,328,559,656,884,905,906,1072,1073],[0]),e6 [219,465] ([161,170,273,1072]++r 1074 11),([0,1,465,3,4,5,44],[41,170,265,832,1085],[]),e6 [274,492] [54,161,170,636,1058,1059,1086,1087],([274,370,0,2,3,4,5],[54,347,556,557,1060,1087,1088],[0]),([0,1,493,3,4,29,5],[265,1089,1090,1091],[]),([0,1,494,3,4,29,5],[265,445,833,1091,1092],[]),([274,495,0,1,2,3,4],[41,76,832,1087,1091,1093,1094,1095],[]),u6 [464,7] ([41,244,260,265,355,554,565,577,926,927]++r 1096 5),([0,1,464,3,4,5,44],[41,265,798,838],[]),([0,1,384,3,4,29,5],[41,161,265,657,1101,1102],[]),([274,290,0,1,2,288,4],[64,170,559,656,912,1103,1104],[0]),([274,340,0,2,3,4,5],[161,347,495,715,1060,1087,1088,1105,1106,1107],[0]),([192,496,1,2,3,4,5],([41,337,410,591,967]++r 1108 4),[]),([340,0,2,3,4,43,5],([161,538,715,1105,1106]++r 1112 4),[]),([274,290,0,1,28,2,4],[41,64,328,363,884,885],[0]),e6 [497] ([41,265,337]++r 1116 4),([495,0,1,2,54,3,4],([41,76,161]++r 1120 4),[]),([498,0,1,3,4,5,44],[46,265,422,1124,1125,1126],[]),([340,0,2,54,3,4,5],[161,164,495,896,1105,1114,1127,1128,1129],[0]),a6 [55] [265,519,520,1119,1130,1131,1132] [0,1],u6 [362,361] ([41,170,206,265,758,773,885,887]++r 1133 4),a6 [499,417] ([161,170,363,734,735,736,933]++r 1137 6) [1],([290,0,1,2,3,4,361],[206,265,446,519,885,1133,1135,1143,1144],[1]),([0,1,2,3,4,378,7],[161,170,350,1068,1145,1146],[]),a6 [500,417] [161,734,735,736,933,1131,1140,1147,1148,1149] [1],e6 [501,443] ([161,170,265,582]++r 766 4++[1038,1150,1151,1152]),e6 [503] ([161,170,265,346,347]++r 1153 5),([290,1,2,348,3,4,5],([265,337,883]++r 1158 7),[0]),([339,0,2,3,4,5,7],[41,64,349,689,755,1165,1166],[0,1]),([274,1,2,348,3,4,5],[206,265,636,883,1056,1088,1159,1160,1162,1167,1168],[0]),([0,28,2,3,461,4,5],([161,170,363,876,878,885,1119]++r 1169 4),[0]),e6 [504] ([41,170,337,345,346,347,731]++r 1173 4),([219,252,298,0,1,2,3],[284,517,732,804,855,856,857,1177,1178],[0]),u6 [191,137,7] [41,164,349,350,352,622,1179],([298,0,1,2,137,4,5,7],[41,161,221,250,252,260,354,1180,1181],[0,1]),([298,0,1,2,137,4,5],[41,161,164,170,250,260,708,1180,1182],[]),e6 [505] [265,1183,1184,1185],a6 [298,393,7] [116,161,221,476,577,731,863,1186] [1],a6 [298,7,388] [41,116,221,731,792,813,863] [0,1],u6 [322,7] [46,234,349,350,543,665,689,916,1187,1188,1189],e6 [506] [41,244,337,1064,1190,1191],e6 [322] [64,234,346,347,1187,1188],e6 [192,507] ([38,76,161,591,964,967]++r 1192 4),([0,1,28,3,29,5,56],[41,838,840,854,1196,1197],[0,1]),([298,0,2,3,4,291,5],([221,1177,1178]++r 1198 6),[0]),([298,1,2,3,4,508,5],([221,863,1177,1178,1202]++r 1204 4),[1]),a6 [181,34,7] [41,252,260,342,355,358] [0,1],([298,207,0,1,4,5,7],[116,189,190,260,358,516,708],[0]),([298,207,0,1,23,4,5],[189,449,498,516,861,1208,1209],[0,1]),e6 [510] [41,170,206,345,346,347,1210,1211],([192,282,0,1,41,3,4],[41,161,431,492,787,991,1124],[0,1]),([58,0,1,2,4],[363,449],[0,1]),e6 [512] [41,76,206,265,337,345,1212,1213],e6 [513] [76,265,337,446,519,1144,1214,1215],a6 [6,7] ([41,191,192,363,426,834,836]++r 1216 6) [0,1],e6 [514] ([41,346,347]++r 1222 4),u6 [8,7] [46,116,229,554,577,679,708,926,927],u6 [8] [46,116,229,260,346,347,679,708],([24,0,1,2,3,7],[41,363,426],[0,1]),u6 [395] [46,54,206,337,345,346,347,498],([372,0,1,3,6,4,5],[170,265,363,498,844,1221],[0]),([0,2,3,6,4,291,5],[363,426,522,523,1169,1226,1227,1228],[0]),u6 [457] [41,202,345,346,347,1229,1230],([0,2,3,461,4,29,5],[161,876,878,879,1091,1231,1232],[0]),([219,454,1,2,3,4,5],[76,334,337,818,819,1003,1006,1019,1233,1234,1235],[1]),([357,0,2,3,4,5,7],[260,329,358,500,778,927,1236],[0]),([219,252,0,1,9,2,3],[249,284,479,484,517,770,856],[0]),a6 [9,7] ([41,76,161,170,191,192,206,265,334,479,484,501,504]++r 834 4++[1237,1238]) [0,1],([219,0,1,2,3,422,5],[41,170,273,636,908,1239],[]),u6 [9,337] [249,273,501,795,1240,1241],e6 [337] [161,249,337,795,1240],([274,0,1,28,3,29,5],[832,840,854,1117,1242,1243],[0]),([0,1,9,34,3,4,5,7],[41,64,116,117,161,259,260,353,355,933,1244],[0]),a6 [45] [41,161,347,657,798,1245,1246,1247] [0,1],a6 [176,9,7] [41,170,252,260,355,358,479,484] [0,1],a6 [298,7] ([41,164,191,192,265]++r 834 4++[863,1177,1178,1201,1248]) [0,1],a6 [176,9] [41,76,205,233,252,334,454,479,484,501,504,805,1237,1238] [0,1],a6 [176,7] [46,170,205,206,233,252,260,355,358,454,554,577,805,926,927,1249] [0,1],a6 [176] [46,76,205,206,233,252,334,337,345,346,347,355,454,781,805] [0,1],e6 [474] [41,76,170,1089,1250],u6 [351,7] [46,206,221,252,308,355,554,577,926,927,1251,1252],a6 [402,9,7] [41,161,221,351,457,458,689,933,1253] [0,1],u6 [9,7,388] [41,116,161,221,252,260,355,501,554,577,770,779,792,933],([219,0,1,2,3,474,5],[41,265,964,1079,1254,1255],[]),u6 [12] [249,294,770,851],([219,0,1,9,6,4,5],([59,70,76,93,170,273]++r 544 4++[785,1084]),[0]),([0,1,9,6,4,5,7],[59,70,116,252,708],[0,1]),([0,1,9,6,23,4,5],[59,70,170,449,498],[0,1]),([16,0,1,9,4,5],[64,170,419,449],[0,1]),([16,0,1,4,5],[419,449],[0,1]),e6 [422] [41,265,334,908,910,1256],u6 [219,9] ([41,161,273,334,599,853,1081,1082,1083]++r 1257 5),([229,0,1,9,2,3,5,7],([41,161,252,265,355,426,479,484,683,720]++r 1262 4),[0,1]),([229,0,1,9,6,4,5],([59,70,76,93,170,433]++r 544 4++[1266]),[0,1]),a6 [9,240] ([76,161,265,334,434,458,606]++r 1267 5) [0,1],e6 [10] [161,170,249,1272,1273],([0,1,2,3,6,23,7],[31,41,81,363,374,426,844,1221],[0,1]),e6 [517] [41,161,170,1274,1275],a6 [160,9,10] [161,170,477,479,484,549] [0,1],a6 [160,9] [41,161,170,206,265,477,479,501,504,548,549,1237,1238,1276,1277] [0,1],a6 [9,10,99] [221,249,274,275,440,484,1278] [0,1],a6 [9,99] [41,76,161,214,276,334,439,440,501,504,1237,1238,1279] [0,1],a6 [9,214,11] [221,222,265,441,450,687,688,1280] [0,1],u6 [34,137,7] [41,252,260,353,355,358,359,552,1281],u6 [219,9,11] [170,441,450,468],([219,0,1,9,2,3,10,5],[170,249,265,266,273,479,514,515,1282,1283],[0,1]),u6 [9,10,7] [161,252,265,274,478,479,484],e6 [519] ([41,76,170]++r 1284 5),([274,290,0,1,2,4,422],[41,54,170,559,656,908,910,1104,1289],[0]),e6 [298,521] ([41,164,1270]++r 1290 9),e6 [219,522] ([76,161,1079]++r 1081 4++r 1299 5),e6 [523] ([46,54,161,206,334,345,681,946]++r 1304 5),e6 [524] ([46,161,170]++r 1309 5),e6 [192,526] ([38,41,346,394,410,589]++r 1314 7),e6 [350,474] ([41,593]++r 1321 9),e6 [350,407] ([449,566,569,945,1327,1328]++r 1330 6),a6 [192,419] ([38,64,161,170,265,394,410,964,1316]++r 1336 5) [1],e6 [350,443] [415,766,767,769,1038,1329,1335,1341,1342,1343],e6 [528] ([161,170,265]++r 1344 6),u6 [216,9,11] [470,707,763],([274,323,0,1,2,4,43,5],([448]++r 1350 4),[]),([274,58,0,1,2,4],[41,46,54,164,170,363,449],[0,1]),e6 [530] ([41,76,484,1238]++r 1354 5),e6 [274,531] [41,54,64,170,244,1058,1059,1359,1360],e6 [532] ([41,46,76,206,334,345,346,501,792,1354]++r 1361 6),([349,0,1,40,3,4,44],([154,414,419,494]++r 1367 4),[0]),e6 [450,43] [38,41,206,537,538,1009,1113,1371,1372],e6 [533] [64,161,1373],e6 [181,323,7] [161,652,665,1187,1353,1374,1375,1376],([293,1,2,3,4,43,311],[161,631,633,657,1009,1115,1377],[0]),([192,349,350,0,2,4,5],[76,347,591,593,663,664,967,1316,1378,1379],[0]),e6 [534] ([46,76,337,346,616,1026]++r 1380 5),([181,0,1,2,3,23,7],([41,142,147]++r 364 4++[651,652,653]),[0,1]),([480,0,1,40,2,3,4],[41,54,161,334,584,1008,1385,1386],[]),([314,0,2,4,5],[426,449,1169],[0,1]),([349,350,0,2,4,5,44],[41,422,663,664,797,1245,1387],[0]),([442,0,1,40,3,4,44],([164,223,413,414,662,1367]++r 1388 5),[1]),a6 [9,7,99] [41,116,161,249,252,260,355] [0,1],e6 [428] ([161,265,334,346,448,665,755]++r 1393 4),u6 [414] ([206,345,494,528,1369]++r 1397 4),([498,0,1,188,3,4,5],([41,170,206,265,345,1124]++r 1401 6),[]),u6 [390] [46,206,337,452,1370,1382,1384,1398,1407,1408],e6 [536,355] ([39,46,970,1046,1047,1048]++r 1409 6),e6 [537] ([161,170,265,347]++r 1415 4),([298,0,1,2,3,23,7],([31,41,81,150]++r 371 4++[731,732,1178]),[0,1]),e6 [350,34,7] [41,252,317,708,927,929,1332,1419],a6 [34,210,7] [41,317,349,489,543,622,681,689,691] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_8_0 : checkNodesBT W_17 g_17 F_17 P_17_8 A_17 B_17_7 8 N_17_8_0 = true := by decide +kernel
def N_17_8_1 : List NodeSpec := [a6 [188,538] ([41,54,206,536,616,1403]++r 1420 7) [1],e6 [192,355,391] [39,394,410,502,593,957,970,1010,1046,1047,1048,1316,1318,1427,1428,1429],e6 [539] ([76,337,345,346,347,588,1010,1047]++r 1430 4),([0,1,34,3,4,29,5],[41,64,116,265,317,1434],[1]),a6 [315] [76,161,206,346,536,562,564,565,838,1435,1436] [0,1],e6 [540] [39,41,46,76,164,206,346,1010,1046,1413,1437,1438,1439],([192,0,1,3,210,4,29,5],([38,41,265,681]++r 1440 4),[]),([0,1,2,3,4,361,56],[41,170,265,1133,1197,1444],[]),a6 [522,7] [116,161,206,260,355,577,778,926,927,1299,1302,1445] [1],e6 [541] ([46,206,337,346,709,1398,1408]++r 1446 4),e6 [542,298] [41,76,161,792,863,1178,1201,1248,1450,1451,1452],e6 [274,278] ([41,54,170,244,265,471]++r 1453 7),([274,0,1,2,188,4,43,5],[54,161,170,448,636,748,1403,1460],[0]),e6 [543] ([161,265,334]++r 1461 4),([375,237,1,188,3,4,5],[337,616,618,619,1381,1465,1466,1467],[0,1]),e6 [544] ([41,46,170,206,244,334,346,1403,1406]++r 1468 5),([298,0,1,2,545,4,5],[161,170,792,863,1202,1473,1474,1475],[]),([375,0,1,40,3,4,44],[413,414,419,421,662,947,1026,1368,1389],[0,1]),([0,1,40,3,210,4,44],[161,223,413,414,662,681,1307,1367,1389,1476],[1]),e6 [546] [161,170,345,346,347,1120,1477,1478,1479],([181,0,1,9,2,4,5,7],[41,64,161,170,289,349,350,351,622,1375,1480],[0]),u6 [188,385] [41,170,206,428,429,430,845,1032,1403,1406,1481,1482,1483],a6 [320] [481,582,584,1484,1485,1486] [0,1],e6 [547,29] ([41,54,265,334,680,1091,1102]++r 1487 5),([0,1,40,3,4,43,44],[154,161,413,414,657,662,1009],[0,1]),e6 [548] [161,538,1492,1493],e6 [550] [41,76,170,346,1494,1495,1496],e6 [219,403] ([161,334,468,1003,1004,1005,1019,1235]++r 1497 5),([375,0,1,2,403,4,5],[170,334,1026,1467,1498,1500,1502,1503],[1]),e6 [551] [54,265,334,1048,1413,1504,1505,1506],([219,552,0,1,2,3,5],[41,161,334,1019,1507],[]),u6 [274,409] ([54,161,164,170,265,636,645,1056,1058,1060]++r 1508 4),e6 [553] [39,41,46,170,337,345,1079,1512,1513],a6 [181,188,7] [41,161,260,338,536,577,652,1406] [0,1],([341,0,1,2,3,4,554],([337,346,783]++r 1514 6),[]),([452,349,0,2,3,4,5],([41,1428]++r 1520 4),[]),e6 [274,555] ([54,161,170,265,832,1056,1058,1060]++r 1524 6),([0,1,379,3,4,29,5],[41,170,265,1010,1232,1530,1531],[]),([410,0,2,3,4,5,554],([346,426,449,1516,1518]++r 1532 5),[]),([542,0,1,2,3,4,7],[41,46,577,778,792],[]),e6 [391,10] ([161,249,275,346,502,515,719,1282]++r 1537 4),e6 [557] ([170]++r 1541 6),([0,1,9,2,3,23,7],[31,41,81,107,150,249,372,770],[0,1]),e6 [558] [76,170,244,346,1081,1261,1303,1547,1548],u6 [432] ([41,76,161,206,334,501,502,705,706,1238]++r 1549 4),e6 [452,355] [39,41,161,170,347,933,970,1046,1048,1411,1553],u6 [451] [41,76,170,801,1554,1555,1556],([192,0,313,2,210,4,5],[346,491,591,593,1318,1557,1558,1559],[0]),e6 [559] ([39,41,46,265,334,1046,1048,1428]++r 1560 5),a6 [279,137] ([41,118,170,265,349,622,627,630]++r 1565 4) [0,1],([192,349,282,0,1,3,4],[41,419,492,494,992,1369],[0]),e6 [561] ([41,161,170,265,334]++r 1569 4),a6 [562] [54,170,337,731,732,1208,1573] [1],([350,0,1,40,3,4,44],[223,231,662,1332,1335,1367,1368,1389,1574],[0,1]),([47,0,1,2,5],[426],[0,1]),([274,290,0,1,2,369,4],[161,170,328,449,497,559,656,791,1575],[0]),([219,298,207,0,1,4,5],([189,190,516,785]++r 858 4++[1084,1261]),[0]),u6 [452,9] [41,161,170,221,479,502,1270,1576,1577,1578],([237,0,1,2,41,43,5],[76,151,416,610,617,739,1446,1579,1580,1581],[0]),([274,290,305,0,1,2,4],[41,559,884,1582,1583],[0,1]),a6 [409,7] [116,161,164,252,260,355,577,927,1509,1510,1511,1584,1585,1586] [1],u6 [453] [41,170,265,807,809,811,812,1587,1588,1589],([24,0,1,2,3],[363,426],[0,1]),e6 [480,188] ([41,54,161,536,1008,1403,1406,1424,1425]++r 1590 4),e6 [563] [54,161,170,265,334,346,537,1115,1594,1595],([0,345,2,41,3,4,5],[161,431,740,741,1469,1470,1596,1597,1598],[0]),a6 [391,34,7] [41,116,317,355,554,577,579,926,927,929,1599] [0,1],a6 [189,7] [46,116,161,206,252,260,358,577,778,926,927,1600,1601,1602] [0,1],e6 [465,7] ([41,170,206,244,252,260,265,355,554,577,926,927,1072]++r 1075 4++[1080]),e6 [564] ([46,76,334,337,346,347,1010,1047,1068]++r 1603 4),e6 [350,491] ([1071,1327,1328,1329,1335]++r 1607 6),([192,282,350,0,1,3,4],[64,246,702,787,976,992,1335],[0,1]),e6 [565] [41,76,170,265,334,502,1589,1613,1614],u6 [192,355,382] [38,41,265,394,410,1010,1046],e6 [188,378] ([41,161,170,585,586,1068,1406,1424,1425]++r 1615 5),([566,0,409,2,3,4,5],([46,347,587,645,646,1511,1586]++r 1620 5),[]),([281,0,2,3,4,5,7],[41,164,358,778,827,927,1625],[0]),([274,1,2,3,4,289,5],[54,636,654,1088],[0]),([293,1,419,2,3,4,5],([696,1337,1430]++r 1626 4),[0,1]),([495,0,1,2,3,4,7],[41,116,164,1630],[]),a6 [10,11] ([41,161,221,265,479,484,506]++r 1631 5) [0,1],e6 [567] ([41,46,206,346,448,1170]++r 1636 5),u6 [9,12] [249,294,770,851],u6 [394] [206,337,415,480,481,1514,1641,1642,1643],e6 [219,464] ([76,161,1079]++r 1081 4++r 1096 5++[1644,1645]),([410,0,2,3,4,5,423],([346,449,642,644]++r 1646 6),[]),([502,0,1,3,4,29,5],[265,1091,1120,1155,1232,1652,1653],[]),e6 [568] ([161,265,1339]++r 1654 6),([0,9,2,3,4,291,5],[46,206,441,470,522,523,761,1660],[0]),([293,0,1,2,3,4,554],[54,337,346,528,671,1514,1515,1516,1518],[]),([349,299,391,2,3,4,5],[453,1382,1408,1523,1661,1662],[0]),([349,282,350,0,2,4,5],[663,664,945,946,1304,1378,1663],[0,1]),e6 [569] ([46,206,337,346,494,783,1398]++r 1664 5),e6 [570] ([46,206,709,1448]++r 1669 5),([349,293,391,2,3,4,5],[494,528,600,1522,1523,1674],[0]),([192,0,1,3,4,571,5],[38,41,265,419,1675],[]),u6 [399] [41,161,170,206,346,536,537,538,657,749,1115,1676],a6 [181,185,7] [41,64,164,349,609,622] [0,1],e6 [572,41] ([38,64,76,170,206,265,431,1124,1468,1596]++r 1677 4),e6 [574] ([41,265]++r 1681 5),e6 [575] [46,54,161,206,346,1058,1087,1088,1686,1687],([302,0,1,2,3,23,4],[41,202,498,1208,1228],[0]),e6 [298,447,7] [161,164,206,260,554,577,792,863,1177,1473],a6 [576] ([161,170,1509,1586]++r 1688 6) [1],e6 [542,9] [41,161,170,221,484,501,792,1237,1238,1451],([452,0,577,2,3,4,5],([1578,1589]++r 1694 6),[]),e6 [578] [206,265,415,481,1029,1408,1700,1701],a6 [408,7] ([41,252,260,355,358,577,927]++r 1702 5) [0,1],e6 [579] [46,54,161,206,345,1060,1087,1088,1707,1708],([192,282,0,1,3,4,321],[41,246,1709],[0,1]),a6 [391,474] ([41,161,593,977]++r 1321 4++[1710]) [1],([0,391,580,2,3,4,5],([345,426,494,1428]++r 1711 5),[]),e6 [582] ([41,265,334]++r 1716 5),e6 [583] ([41,46,76,221,249,1238,1354]++r 1721 4),([0,391,584,2,3,4,5],([345,346,347,426,449,1623,1714]++r 1725 4),[]),u6 [391,422] [41,54,634,635,908,910,1117,1729,1730],e6 [274,278,391] [54,471,502,832,1056,1058,1059,1060,1064,1428,1453,1454,1455,1561,1731,1732],a6 [272,7] [41,161,206,335,349,489,543,665,689,916,933,1375,1733] [0,1],([219,357,0,2,3,4,5],[76,329,334,500,842,843,1082,1084,1261,1303],[0]),([349,350,0,40,2,4,5],[41,415,659,663,664,1029,1378,1663,1734],[0]),a6 [189] [46,76,116,161,170,206,346,358,577,778,1600,1601,1602,1735] [0,1],([341,355,375,0,1,2,5],([39,161,170,971,972,973]++r 1736 4),[0]),a6 [57] [41,161,347,833,838,839,841,1102] [0,1],([293,319,391,2,3,4,5],([670,671]++r 1740 4),[0]),([219,585,0,1,2,3,5],[41,64,1006,1196,1744],[]),([0,391,2,3,4,5,586],[41,54,426,1408,1713,1715,1745,1746,1747],[]),([0,391,2,3,4,5,587],([426,449,1695]++r 1748 4),[]),e6 [588,10] [161,249,479,515,719,1282,1537],a6 [181,185] ([41,76,161,534,609,651,1374]++r 1752 10) [0,1],([340,0,2,3,4,5,56],[161,164,419,564,565,715,1762,1763,1764],[0]),([589,0,391,2,3,4,5],[345,449,670,792,1714,1715,1765,1766],[]),([237,1,188,41,3,4,5],[161,618,619,1032,1465,1466,1468,1469,1767],[0,1]),([219,496,1,2,3,4,5],[64,337,1003,1006,1108,1109,1110,1235,1768,1769],[]),([237,1,188,3,4,43,5],[161,537,618,619,1008,1115,1492],[0,1]),([0,391,2,3,4,5,423],[41,54,449,639,642,643,1484,1714,1715],[0]),([450,219,0,1,2,3,4],[41,801,1081,1261,1303],[0]),e6 [495,210] ([41,161,346,347,681,1122,1307]++r 1770 6),e6 [188,422] [41,161,170,634,635,636,908,1403,1406,1424,1425,1729,1730,1776,1777],([0,1,2,3,4,554,44],[41,265,422,798,1516,1519,1778,1779],[]),([302,219,0,1,2,3,4],[41,76,202,594,785,1084],[0]),e6 [495,350] ([347,449,1327,1328,1332,1335,1630]++r 1780 4),e6 [192,591] [38,39,164,170,964,967,1316,1318,1784],([0,580,2,3,4,5,525],([46,426]++r 1785 4),[]),([0,1,149,3,4,5,7],[139,161,265,326,351],[0,1]),e6 [592] [161,265,347,1789,1790],e6 [593] ([161,170,1498]++r 1791 4),e6 [594] ([41,46,76,170,244,502,1453,1455]++r 1795 4),([595,0,1,2,4,43,5],[161,170,206,537,933,1115,1799,1800,1801],[]),e6 [597] ([170,502]++r 1802 4),e6 [598] [41,76,206,265,345,347,422,1673,1806,1807],([290,0,1,28,3,29,5],[334,445,840,854,1163,1242,1243,1808,1809,1810],[0]),e6 [480,323] ([161,337,419,1008,1352,1353,1376]++r 1811 5),([375,0,1,2,3,599,5],[345,421,616,792,1581,1816,1817],[]),e6 [555,7] [38,46,116,164,252,260,577,926,927,1524,1525,1527,1528,1529,1818],e6 [600] ([46,1448,1484,1581]++r 1819 5),e6 [602] ([46,206,334,337,347,1448]++r 1823 8),e6 [298,433] ([161,164,863,1178,1201,1248,1262]++r 1831 6),e6 [603] [64,170,345,358,778,927,1837,1838],e6 [604] [41,170,265,345,346,422,1124,1125],e6 [192,605] [39,64,161,265],e6 [606] [39,41,46,76,206,345,1048,1411,1413,1839,1840],e6 [34,607,7] [116,265,381,577,579],e6 [192,608] ([38,161,170,265,394,410,964,1316,1318,1639]++r 1841 6),u6 [391,9,7] [41,116,161,249,252,260,355,358,501,502,504,554,577,704,926,927,1237,1238,1427,1847,1848],e6 [404,378] [41,64,585,586,588,1145,1617,1849,1850,1851],e6 [609] [46,64,161,206,334,345,896,1129,1852,1853,1854],u6 [404,417] [64,161,734,735,1131,1147,1148,1149,1852],e6 [404,422] [41,54,634,635,910,1117,1730,1849,1850],e6 [610] [46,76,170,244,334,345,1306,1390,1391],([192,375,282,0,1,3,4],[41,419,492,787,947,976],[0]),e6 [274,549] [54,161,170,1058,1060,1087,1855,1856,1857],a6 [34,425,7] [41,381,489,665,667,916,1187,1858] [0,1],e6 [611] [41,76,170,345,1859,1860,1861],([290,340,0,2,3,4,5],[161,334,495,715,1105,1114,1810,1862],[0]),([612,0,1,2,4,5,56],([46,170,562,564,1196]++r 1863 4),[]),([0,1,34,3,4,5,35],[41,106,116,355],[0,1]),a6 [527,7] ([116,161,164,206,260,265,355,554,577,926,927,1347]++r 1867 4) [1],([192,542,0,1,2,3,4],[41,334,410,591,1451,1871,1872,1873],[]),([192,282,0,1,3,590,4],[164,265,492,976,978,1874,1875],[1]),e6 [219,527] ([161,170,206,337,785,1079]++r 1081 4++[1347]++r 1867 4),([192,282,0,319,1,3,4],[41,419,492,670,982,992,1876],[0,1]),u6 [9,433] ([161,221,484,501,1237,1238,1262]++r 1832 5++[1877]),([219,252,0,1,2,3,6],[284,363,426,517,804,1220,1221],[0,1]),e6 [614] ([41,76,170,265,345]++r 1878 4),a6 [410,137,7] [41,244,927,962,1882,1883] [1],a6 [615,443] ([46,221,265,346,415,582]++r 766 4++[1038,1341,1343,1884,1885,1886]) [1],e6 [616] ([41,206,265,334,346,363]++r 1887 4),([375,0,345,2,3,4,5],[419,740,741,947,1026,1169,1891],[1]),([372,207,0,1,3,4,5],([76,265,815]++r 1892 8),[]),e6 [617] [39,41,46,334,345,346,970,1413,1900,1901],e6 [410,378] [41,244,265,585,586,1145,1616,1617,1618,1851,1902,1903,1904],e6 [618] ([161,170,347]++r 1905 4),e6 [619] [46,337,346,616,709,1446,1581,1909,1910],a6 [410,417] [161,244,265,734,735,736,1139,1140,1147,1148,1149,1911,1912] [1],e6 [620] [54,206,244,334,345,1088,1913,1914,1915],e6 [192,545] ([38,161,170,265,394,410,964,1316,1318,1474]++r 1916 6),e6 [621] [64,161,170,1678,1922,1923,1924],e6 [622] [41,76,170,345,1925,1926],e6 [410,422] [41,54,634,635,910,1117,1729,1730,1777,1927],([375,293,1,2,3,4,311],([46,337,421,631,633,947,1467]++r 1928 4),[1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_8_1 : checkNodesBT W_17 g_17 F_17 P_17_8 A_17 B_17_7 8 N_17_8_1 = true := by decide +kernel
def N_17_8_2 : List NodeSpec := [u6 [428,7] [161,349,350,489,543,622,665,689,755,1393,1394,1396],e6 [623] [41,76,170,345,346,1176,1861,1912,1932,1933],a6 [406,7] [41,161,260,355,554,570,577,681,778,927,1463,1934] [1],([0,1,2,3,4,525,11],([41,265,687,1788]++r 1935 5),[]),e6 [452,278] [41,161,221,244,265,471,1453,1455,1520,1940],u6 [9,447,7] [41,161,252,479,501,504,554,577,792,1366,1473,1941],e6 [624] [54,170,346,347,657,1942,1943],e6 [625] [345,671,1824,1830,1944,1945,1946],([298,595,0,1,2,4,5],[161,170,334,337,863,1178,1202,1799,1947,1948,1949],[]),([192,282,0,1,626,3,4],[41,246,265,702,787,992,1950],[1]),e6 [627] [41,170,337,1951,1952],e6 [628] ([54,161,206,345,872]++r 1953 5),([340,0,2,3,4,5,7],[41,161,164,358,495,715,778,927,1106,1958],[]),e6 [408] [265,334,502,577,927,1702,1703,1704],e6 [509,525] ([41,46,54,244,1899,1954]++r 1959 8),e6 [629] ([41,76,170,345]++r 1967 4),e6 [630] ([161,265,334,1320]++r 1971 4),u6 [181,7] ([41,46,64,170,206,652,806]++r 1975 5),([0,1,560,3,4,5,44],[41,54,265,797,1387,1980,1981],[]),([0,631,2,3,4,5,525],[46,346,426,449,1788,1982,1983,1984],[]),e6 [560,7] ([41,54,244,252,260,355,554,577,927,1571,1981]++r 1985 4),e6 [632] ([161,265,562,564,792,1473]++r 1989 4),([192,480,0,1,2,3,4],[41,334,967,1009,1385,1591],[]),e6 [192,633] [39,41,161,265,334,967],e6 [634] ([41,54,170,1455,1788]++r 1993 4),e6 [635,7] [41,64,116,221,252,260,355,363,577,778,926,927,1997],a6 [603,7] [41,46,206,252,260,358,554,577,778,1998,1999] [1],e6 [637] ([170]++r 2000 6),([290,0,1,2,638,4,5],[161,170,334,1810,2006,2007],[]),e6 [639] [41,46,206,337,345,346,593,967,1318,2008,2009,2010],([0,1,584,3,4,5,44],[265,422,798,1623,1778,2011],[]),([0,1,9,2,3,4,11,7],[41,46,265,278,350,441,470,486,489,1935,1938,2012],[0,1]),e6 [640] ([41,46,76,244,345]++r 2013 4),([0,1,34,2,3,23,7],[31,41,81,150,317,372,381],[0,1]),a6 [229,227] ([46,170,265,683,684,1264,1265,1266]++r 2017 11) [0,1],e6 [641] [41,46,265,334,345,1088,2028],([0,1,28,2,54,4,56],[64,235,331,363,885,1215,2029],[0,1]),e6 [447,11] ([41,170,222,531,718,770,792,1366]++r 2030 5),e6 [642] ([41,46,170,244,426]++r 2035 7),e6 [644] [41,76,170,265,334,2042,2043,2044],e6 [192,612] [39,41,170,334,337,394,410,1864,2045],([0,1,34,3,4,5,44],[41,265,380,1187,2046],[1]),e6 [160] [41,170,206,265,337,345,548,549,2047],e6 [274,645] ([54,170,206,265,636,1056,1058,1060]++r 2048 5),e6 [646] [41,46,76,170,345,591,1724,2053,2054],([274,0,1,2,4,647,5],[41,54,76,170,448,2055,2056],[]),e6 [9,648] ([41,161,221,265,484,501,504,1238,1262]++r 2057 6),e6 [473] [39,41,46,334,337,345,970,2063,2064],e6 [649] [41,76,206,345,2013,2065,2066,2067],e6 [650] [41,76,265,334,337,346,562,564,1196,1863],e6 [651] [41,76,170,206,345,1358,1994,2068,2069],([192,282,0,1,3,476,4],[161,265,492,702,976,981,982,2070,2071],[1]),u6 [303] [41,202,347,594,2072,2073,2074],([192,282,442,0,1,3,4],[41,164,246,492,530,702,787,992,1390],[1]),u6 [191,7] [41,161,164,221,265,349,350,352,388,489,543,665,689,916,1179,2075,2076],e6 [652] [41,265,334,345,1413,2077],e6 [654] [54,170,2078,2079,2080],a6 [34,137] ([41,117,161,170,260,265,354,358,359,579,660,925,928,929]++r 960 4++[1281]) [0,1],([192,350,0,1,3,4,29,5],[41,1332,1782,2081,2082],[]),e6 [655] [76,170,265,415,659,1270,1390,1724,1734,2083,2084],([0,1,2,3,4,44,385],[41,170,265,422,821],[]),([0,1,2,3,4,423,44],[41,265,643,1507,1778,2085],[]),([375,0,1,2,3,656,5],[46,345,528,792,947,2086,2087,2088],[]),e6 [657] [41,46,170,346,838,1197,2089],e6 [658] [41,206,265,345,346,670,798,1507,1778],([293,1,2,41,3,4,311],[161,431,631,633,1124,1469,1930,2090],[0,1]),([192,0,319,2,3,321,5],[206,529,589,591,964,2091,2092,2093],[0]),([589,0,1,3,4,5,44],[46,265,670,798,1507,1778],[]),u6 [429] [670,671,1400,1819,1820,2086,2094,2095],e6 [274,278,488] [41,64,471,1056],([0,1,2,3,4,11,7],[41,170,206,265,278,350,486,2012],[]),([293,0,1,2,41,43,5],[76,151,155,426,528,610,739,1397,1579,2086],[0]),([0,345,2,3,4,43,5],[161,538,740,741,1009,1113,1115],[0]),u6 [9,23] ([221,265,419,449,599,703,853,1209]++r 2096 4),e6 [659] [345,421,528,947,1381,1397,2086],([0,1,469,2,4,43,5],[170,657,949,1009,1943],[]),([442,0,1,2,3,443,5],[54,161,265,415,582,766,767,1038,1343,1390,1724,2100,2101],[0]),([0,1,2,3,4,311,385],[41,345,428,845,1032,2102,2103,2104],[]),([0,1,40,3,4,321,44],[154,223,413,662,1709,2105],[1]),e6 [660] ([161,265,1299]++r 2106 4),e6 [661] ([46,206,337,347,783,1517,1824,1830]++r 2110 4),([357,0,2,3,23,4,5],[329,419,449,500,1169,1208,1209,2099,2114],[0,1]),e6 [662] [265,337,481,584,1946,2115,2116,2117],([0,1,2,3,4,311,11],[41,222,1268,1937,2012,2103,2118],[]),u6 [219,9,396] [164,170,501,504,533,770,785,1081],([0,1,406,3,4,29,5],[41,265,570,680,681,879,1102,1463,2119],[]),([341,0,1,2,41,43,5],[76,151,155,610,617,620,632,739,783,1579,1580,1664,1736],[0]),e6 [663] ([41,265,334]++r 2120 5),e6 [664] [41,798,1778,1830,2125,2126],e6 [665] ([161,170,265,1800]++r 2127 4),e6 [666] ([41,46,206,337,345,347,589,593,1318]++r 2131 4),e6 [667] [46,76,337,346,421,783,1664,1736,2135,2136],e6 [595,28] [54,170,206,885,1170,1636,1800,1947,1949,2137,2138],e6 [274,613] ([41,54,161,170,244,265,1060,1117,1648]++r 2139 4),([442,0,1,2,3,10,5],[64,161,265,479,515,719,1282,2143,2144,2145],[1]),e6 [274,668] ([41,54,170,206,265,636,1056,1058,1059,1060,1088,1391]++r 2146 7),e6 [192,669] [39,41,164,170,265,334,394,410,957,1316,2153,2154,2155],e6 [34,670,7] [41,317,927,929,2156],e6 [671] [76,170,206,346,885,1170,1262,1636,1836,2157,2158],u6 [396,10] [161,164,275,479,515,911,1282,1537,2145,2159,2160],([529,0,1,2,3,4,11],[41,265,484,531,687,718,2033,2161],[]),a6 [396,11] [164,222,531,533,718,770,2032,2033,2162,2163,2164] [0,1],u6 [9,396,7] [116,164,170,265,501,577,649,770,1262],([192,282,0,313,1,3,4],[41,492,702,991,992,1514,1673],[0,1]),([219,0,1,2,3,10,5],[161,170,249,265,479,514,515,1282,2165],[]),e6 [99] [41,76,214,276,334,337,345,346,347,440],e6 [672] [46,76,345,346,445,446,1582,2166],([274,290,0,1,2,4,29],[64,164,449,497,656,1091,1104],[0]),([192,282,0,1,3,210,4],[64,161,246,702,787,976,992,1307],[0,1]),([0,1,9,6,4,10,5],[59,70,170,275,719],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_8_2 : checkNodesBT W_17 g_17 F_17 P_17_8 A_17 B_17_7 8 N_17_8_2 = true := by decide +kernel
def N_17_8 := N_17_8_0 ++ N_17_8_1 ++ N_17_8_2
def B_17_8 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_8
set_option maxRecDepth 500000 in
lemma B_17_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 8 xs.toFinset) B_17_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_17) (raw := r_17) (pspecs := ps_17) (used := U_17_8) S_17_ok
  have hm0 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_7_ok C_17_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_7_ok C_17_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_7_ok C_17_8_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def U_17_9 : List Nat := ([38,39,41,46,54,64,76,116,161,164,168,170,206,221,244,249,252,260,265,273,274,275,317,334,337,345,346,347,349,351,355,358,363,375,380,394,410,415,419,421,422,426,431,433,441,445,446,448,449,468,471,479,481,484,494,498,501,503,504,519,528,536,537,538,543,554,562,564,565,577,582,584,588,589,591,593,616,622,626,634,636,645,649,652,653,657,659,665,670,671,680,681,689,704,708,709,731,732,736,755,770,778,779,783,785,791,792,797,798,832,833,838,844,863,872,879,885,896,906,908,912,916,926,927,933,942,945,946,947,957,964,967,970,977,980,988,993,994,995]++r 1002 5++[1008,1009,1010,1019,1025,1026,1029,1032,1033,1046,1047,1048,1056,1058,1059,1060,1072,1079]++r 1081 4++[1087,1088,1090,1091,1100,1102,1106,1113,1115,1117,1119,1120,1124,1128,1129,1131,1132,1148,1161,1163,1169,1170,1171,1177,1178,1186,1196,1197,1201,1202,1208]++r 1215 8++[1235,1237,1238,1245,1248,1261,1262,1266,1270,1290,1295,1296,1298,1302,1303,1304,1307,1316,1318,1321,1327,1328,1332,1335,1352,1353,1354,1358,1366,1369,1370,1371,1376,1377,1381,1382,1384,1387,1390,1391,1397,1398,1400,1403,1406,1407,1408,1411,1413,1424,1425,1430,1441,1445,1446,1448,1451,1453,1454,1455,1459,1463,1467,1468,1470,1473,1484,1485,1487,1488,1492,1503,1507,1511,1514,1517,1523,1527,1529,1530,1537,1571,1578,1581,1582,1586,1592,1599,1606,1622,1623,1628,1630,1636,1639,1642,1648,1664,1666,1669,1672,1673,1677,1697,1709,1713,1714,1724,1734,1736,1742,1763,1767,1770,1771,1777,1778,1782,1785,1786,1788,1799,1810,1813,1814,1815,1819,1823,1824,1828,1830,1835,1836,1842]++r 1846 4++[1852,1862,1863,1866,1867,1870,1872,1875,1876,1883,1891,1896,1897,1899,1903,1911,1912,1931,1940,1941,1943,1949,1954,1961,1966,1981,1982,2045,2052,2061,2062,2071,2086,2090,2093]++r 2096 4++[2102,2105,2125,2137,2138,2141]++r 2166 195)
def P_17_9 : BT (Option BoundPool) := buildPoolsSubBT 12 W_17 r_17 S_17 ps_17 U_17_9
def N_17_9_0 : List NodeSpec := [a6 [493] [64,76,170,265,346,347,363,1090,1222] [0,1],a6 [479] [64,76,170,265,337,426,785,933,995] [0,1],a6 [279,7] [41,64,116,161,260,265,355,554,577] [0,1],a6 [7,35] [41,116,164,260,265,363,375,426] [0,1],a6 [34,7] [41,64,116,161,260,265,317,355,380,577,926,927,933,1599] [0,1],a6 [34] [46,64,76,116,170,206,265,317,337,346,347,380,933] [0,1],a6 [402,7] [41,221,346,351,426,622,626,665,689,755,933,2167] [0,1],a6 [7,388] [41,116,221,260,363,577,778,779,933] [0,1],a6 [375,282] [46,419,421,426,946,947,1026,1304,1381,1467,1891,2168,2169,2170] [0,1],a6 [407] [46,76,161,170,244,347,419,945] [0,1],([0,345,2,3,4,5],[46,334,347,1169],[0,1]),u6 [192,375] [41,76,206,265,410,419,421,947,964,967,1381,1467],a6 [379] [46,76,170,265,337,346,347,933,988,1010,1530] [0,1],u6 [192,476] [38,170,265,449,589,964,2071],u6 [192,626] [41,64,265,346,589,591],a6 [192,382] [38,41,64,265,337,410,419,591,964,967,2171] [0,1],a6 [480] [41,46,54,76,161,170,206,265,334,337,345,346,347,449,1008] [0,1],a6 [219,44] [46,164,334,422,994,1006,1019,1245,1387,1507,1778,2172,2173] [0,1],([673,1,2,3,4,5],[76,206,345,419,426],[]),a6 [192,43] [41,46,64,76,161,206,265,410,537,657,964,1492] [0,1],a6 [40,41] [41,161,170,265,415,431,1029,1032,1033,1124,1468,2174] [0,1],a6 [443] [76,161,170,265,347,363,415,2175] [0,1],a6 [181,7] [41,46,64,161,170,206,349,351,543,622,652,653,665,689,916] [0,1],u6 [192] [41,46,64,76,170,206,265,345,346,347,419],a6 [43,7] [46,64,161,170,260,358,426,538,1008] [0,1],a6 [290,305] ([46,334,445,1161,1163,1582,1810,1862,2166]++r 2176 6) [0,1],e6 [674] [39,161,265,334,363,446,449],u6 [494] [206,265,337,363,445,449],e6 [192,274] [41,46,76,170,265,334,394,410,832,957,967,1058,1059],a6 [43,44] [41,46,64,161,164,422,657,798,1245,1387,1507] [0,1],a6 [274,305] [41,76,170,206,334,636,832,1058,1059,1087,1582,2166,2176,2177] [0,1],u6 [274,288] [54,76,170,363,448,636,912,1087],a6 [279] [41,64,76,161,170,265,337,345,346,347,933,2182,2183] [0,1],u6 [274,422] [41,54,76,170,206,448,636,908],u6 [274,465] [54,164,170,448,832,1058],a6 [274,7] [41,76,170,206,252,260,358,363,554,926,927,1087,1117] [0,1],u6 [274,369] [54,170,265,419,449,636,791,832],e6 [274,675] [54,164,170,337,363,832,1058,1088],a6 [29,7] [41,46,116,161,164,260,265,426,1102] [0,1],a6 [290,29] [161,334,449,680,1091,1102,1487,1488,1810,1862,2184] [0,1],a6 [29,56] [41,46,64,161,164,449,833,838,1102,1196,1197,1763] [0,1],a6 [464] [206,265,337,449,838,933,1100] [0,1],a6 [192,56] [41,170,265,334,363,562,589,838,2185,2186] [0,1],([340,0,2,3,4,5],[334,347,1106,1169,2187],[0,1]),([676,1,2,3,4,5],[76,345,363,419,449,2188],[]),u6 [290,28] [64,265,334,363,445,446,885,1161,1163,1215,1636,2137,2138,2189],u6 [274,28] [41,76,170,206,265,363,832,885,1058,1119,1215,1636,2189],a6 [28,56] [41,64,265,363,419,519,562,838,1197,1215,1636] [0,1],([0,1,28,3,29,5],[206,419,426],[0,1]),a6 [417] [161,170,265,334,347,363,1131,1148,1911] [0,1],([219,252,0,1,2,3],[46,206,363,426],[0,1]),([677,0,2,3,4,5],[346,363,426,449],[]),([0,1,2,3,23,7],[363,426],[0,1]),([0,2,3,4,291,5],[46,206,1169],[0,1]),a6 [384] [46,265,337,449,657,933,1025] [0,1],([0,2,3,461,4,5],[46,170,1169,1171],[0,1]),a6 [298,7] [41,116,161,206,260,355,554,577,708,731,863,926,927,1177] [0,1],([372,0,1,3,4,5],[265,363,426],[0]),a6 [298,23] ([265,419,449,498,732,863,1177,1178,1208]++r 2096 4) [0,1],a6 [509] [46,161,170,244,347,419,1899,1966,2190] [0,1],([274,290,0,1,2,4],[46,170,363,449],[0]),a6 [29,43] [161,206,426,657,1102] [0,1],a6 [9] [46,170,206,346,419,449] [0,1],a6 [6,23] [363,426,449,498,1208,1219,1220,1221,2099] [0,1],a6 [274,29] [41,46,54,161,170,449,680,832,833,1060,1091,1102,1117,1487,2184] [0,1],u6 [511] [46,161,265,337,449,2191],u6 [302] [41,206,345,346,419,449],u6 [219,9] [41,76,170,249,265,273,334,479,501,504,770,785,1079,1081,1084,1237,1238],u6 [465] [76,170,206,265,337,346,347,832,906,933,1072],a6 [9,7] [41,46,76,116,161,170,206,249,252,260,265,334,355,479,501,577,770,926,927,1238,1847] [0,1],a6 [6,7] [41,116,161,260,363,426,708,844,927,1220,1221] [0,1],a6 [516] [41,170,206,221,265,337,345,346,347,441,2192,2193] [0,1],u6 [192,478] [41,265,334,346,449,589,591,593,993,1318],a6 [9,10] [161,170,221,249,265,274,275,484] [0,1],a6 [10] [46,161,170,249,265,274,275,337,347,1537] [0,1],a6 [474] [41,46,76,161,170,265,334,337,347,593,977,1321] [0,1],u6 [9,396] [164,170,419,479,501,649,770,1262,1354,2194],u6 [502] [170,206,265,337,345,346,347,363,933,1120,2195],a6 [375,222] ([64,337,345,933,947,1026,1467,1503,1799,1836,1891,1931]++r 2196 5) [1],a6 [219,56] [46,64,76,363,562,565,1006,1019,1196,1197,1763,2185,2186] [0,1],([357,0,2,3,4,5],[76,334,347,1169,2201],[0,1]),a6 [442,9] ([41,170,221,249,265,334,449,479,484,501,1238,1390,1391,1724]++r 2202 4) [0,1],u6 [433] [76,161,170,265,337,363,1169,1262,1835,1836,2206],a6 [572] [46,64,76,170,206,265,337,346,419,1169] [0,1],a6 [595] [46,170,206,265,334,337,346,1169,1949] [0,1],u6 [341,375] [76,206,337,421,616,1026,1381,1467,1664,1666,1736,1931,2199,2207,2208],([678,1,2,3,4,5],[345,346,419,426,449,2209],[]),([679,1,2,425,4,5],[345,363,419,942,1169],[]),a6 [237,319] ([206,346,670,1169,1484,1581,1742,1819,1823]++r 2210 4) [0,1],a6 [350,44] [41,64,334,797,798,1332,1335,1387,1778,1782,2172,2214,2215] [0,1],u6 [350,40] [64,170,334,449,584,659,1327,1328,1335,1734,1782,2174,2216,2217],u6 [192,350] [41,64,347,449,589,591,593,1316,1327,1332,1335,1782],u6 [192,590] [38,265,334,426,593,967,1875],a6 [192,41] [41,76,170,206,265,334,394,410,431,967,1124,1468,1767] [0,1],([192,278,0,1,3,4,5],[41,46,64,161,206,265,334,419,593,933],[]),a6 [274,323] [164,337,363,419,448,832,1058,1088,1352,1353,1376,1813,1815] [0,1],a6 [648] [41,46,170,265,334,347,426,1169,1262,2061,2062] [0,1],u6 [349,40] [41,265,347,415,419,481,1029,1369,1370,1408,2216],a6 [341,41] [76,161,170,337,431,783,1032,1124,1468,1470,1664,1666,1677,1736,1767,2090,2208,2218] [0,1],([349,350,0,2,4,5],[76,347,426,1169],[0]),a6 [274,391] [54,170,221,345,346,363,449,636,832,933,1058,1060,1087,1117,1714,2219] [0,1],([0,1,2,4,680,5],[76,363,426],[]),u6 [529,9] [161,170,221,249,265,334,449,479,484,501,1238,1358,2061,2202,2220,2221],u6 [542] [41,46,76,161,170,265,334,337,345,346,363,1169,1451],a6 [681] [76,161,170,244,334,345,363,1382,2222] [1],a6 [350,7] [41,64,358,426,577,708,778,927,1332,1335,2223,2224] [0,1],a6 [237,41] [76,161,170,1032,1124,1446,1448,1468,1470,1581,1606,1677,1767,2218,2225] [0,1],u6 [219,188] [164,334,345,363,536,1081,1082,1084,1261,1303,1403,1424,1425,2226],u6 [469] [46,170,206,221,346,347,419,1943],u6 [274,44] [41,46,76,170,798,832,1387,1778,2173],a6 [229,9] [41,76,170,221,249,265,334,433,479,484,501,504,1237,1238,1262,1266] [0,1],a6 [349,282] [46,347,419,494,945,946,1369,1370,1398,1523,2170,2227] [0,1],a6 [349,44] [41,419,422,494,1245,1370,1778,2214] [0,1],a6 [422] [41,76,161,170,265,334,337,347,634,908,1117,1777] [0,1],e6 [274,682] [41,54,170,449,1088],u6 [192,525] [41,46,221,265,334,346,591,967,1786,1788,1954,1961],a6 [656] [46,76,161,170,345,419,528,792,2228] [0,1],a6 [375,44] [41,419,1026,1245,1381,1387,1467,1507,1778,2172] [0,1],([410,0,313,2,3,4,5],[76,334,346,347,426,449,1169,1642,1648,2229,2230,2231],[0]),u6 [372] [76,170,265,337,345,346,363,426,498],a6 [391,9] [170,221,249,265,345,346,419,449,479,484,501,770,1238,1848,2202,2232] [0,1],a6 [188,43] [161,164,536,537,538,657,1113,1115,1403,1592,2233,2234] [0,1],([349,0,391,2,3,4,5],[345,426,494,1408,1523,1713,1714,2235,2236],[0]),a6 [442,40] ([41,221,265,334,415,582,659,1029,1390,1391,1724,1734,2174,2205,2216]++r 2237 4) [0,1],a6 [608] [46,161,170,265,337,1169,1262,1639,1842,1846,2241] [0,1],a6 [40,43] [64,161,206,265,334,537,584,657,1008,1009] [0,1],u6 [293,319] [346,670,671,1169,1819,1876,2086,2210,2211,2212,2242],u6 [219,298] ([41,46,206,265,334,731,732,785,863,1079]++r 1081 4++[1177,1186,1201,1248,2243]),a6 [683] [170,345,363,419,2244,2245,2246] [1],u6 [274,188] [54,76,164,170,363,448,536,636,1058,1087,1088,1403,1406,1424,1592],a6 [442,44] [41,164,221,334,346,797,1245,1387,1391,1507,2172,2205,2214,2247,2248] [0,1],u6 [349,299] [76,345,1169,1370,1382,1384,1407,1408,2235,2249],a6 [192,7] [41,116,206,260,265,334,355,363,554,577,593,926,927,967] [0,1],u6 [274,410] [41,54,170,221,265,334,346,347,449,636,1056,1060,1087,1088,1648,1903,1912,2250],u6 [274] [41,164,170,206,265,334,345,346,363,449],a6 [293,41] [76,161,170,426,431,528,1124,1397,1430,1470,1767,2086,2218] [0,1],a6 [375,40] [41,265,415,419,421,481,582,947,1029,1467,1734,2174] [0,1],e6 [28,311] [221,345,419,519,1170,1636,2102,2251,2252,2253],a6 [192,391] [38,221,265,345,346,347,363,410,419,589,593,704,933,964,967,1316,1848,2232,2236,2254] [0,1],a6 [192,313] [41,76,265,346,589,591,1318,1514,1642,1669,1673,2255] [0,1],u6 [341,349] [76,346,494,783,1169,1370,1398,1408,1523,1664,2235,2256,2257],u6 [349,293] [46,345,494,528,1169,1369,1397,1400,2235,2242,2258],([237,1,188,3,4,5],[337,345,363,1169],[0,1]),a6 [274,447] [161,170,206,221,337,345,363,636,933,1058,1087,1088,2259,2260] [0,1],a6 [522] [46,76,206,265,337,346,1169,1302] [0,1],u6 [452] [41,76,170,206,265,334,337,347,363,1270,1578,1697,2261,2262],a6 [555] [46,64,76,170,265,337,346,419,1169,1527,1529,2260] [0,1],u6 [237,313] [76,345,709,1169,1448,1669,1672,1673,1823,2231,2255],([684,1,2,3,4,5],[46,345,419,426],[]),a6 [409] [46,76,170,206,265,337,347,419,645,1511,1586,2263,2264] [0,1],a6 [237,43] [76,161,206,337,537,538,657,1371,1446,1448,1492,2225,2234] [0,1],a6 [341,313] [76,345,783,1169,1514,1517,1666,1669,1672,1673,2231,2255,2265] [0,1],([685,1,2,3,4,5],[76,334,345,363,449],[]),a6 [188,7] [161,164,206,260,358,363,536,577,778,927,1403,2223,2266] [0,1],([274,0,1,2,4,43,5],[41,54,76,161,170,206,449,636,1008],[0]),a6 [192,210] [41,64,265,591,681,964,967,1307,1441,1770] [0,1],u6 [192,475] [38,41,64,265,589,980,1316],a6 [686] [46,76,206,265,337,345,346,347,426,449,1673,2267,2268] [1],a6 [547] [41,46,54,76,206,265,334,345,1169] [0,1],([0,1,9,6,4,5],[170,419,449],[0,1]),u6 [566,44] [46,347,419,422,798,1245,1623,1778,2173,2214,2269],u6 [350,29] [334,426,449,680,833,879,1327,1328,1332,1335,1488,2184,2270,2271],a6 [406] [46,76,206,265,345,347,449,1169,1463,2272] [0,1],a6 [450] [38,41,46,76,170,206,334,337,346,363,419,1169] [0,1],u6 [274,442] [41,76,170,206,449,636,933,1058,1060,1087,1088,1390,1391,2238,2239,2273,2274],a6 [298,447] [161,206,345,419,731,863,1177,1202,1473,2259,2275] [0,1],a6 [580] [46,76,206,265,337,345,346,426,494,1785] [0,1],a6 [40,210] [64,161,265,334,346,582,659,1029,1307,1441,1734,1770,1771,2276] [0,1],([0,1,40,3,4,44],[46,419],[0,1]),a6 [599] [76,161,170,345,363,419,709,792,2277,2278] [0,1],a6 [192,520] [41,221,265,334,337,410,419,967,1863,2279] [0,1],([192,282,0,1,3,4],[46,265,419],[0,1]),a6 [518] [41,46,64,76,170,206,334,345,1169,1852,2280] [0,1],([679,1,391,2,3,4,5],[337,345,346,363,419,449,2232,2244,2254,2264,2281,2282,2283],[1]),a6 [192,425] [64,265,363,410,419,591,964,967,1445,2284,2285,2286] [0,1],u6 [192,474] [38,41,265,334,593,977],u6 [584] [46,206,265,337,345,346,347,426,449,1623,2287,2288],a6 [529,29] [164,221,334,426,680,879,1091,1102,1488,2221,2270,2289,2290] [1],u6 [274,404] [41,54,164,170,449,1087,1088,1117,1849,1852,2291,2292],a6 [192,355] [38,39,41,161,170,265,394,410,588,967,970,1010,1046,1047,1048,1316] [0,1],a6 [375,323] [337,419,421,1352,1376,1467,1503,1813,1814,1815] [1],a6 [404,7] [41,46,164,260,358,426,577,708,778,927,1852,2223,2292] [0,1],a6 [219,6] ([41,76,334,363,426,785,844,1082,1084]++r 1216 6++[1261]) [0,1],e6 [688] [76,345,363,419,2293,2294,2295],a6 [527] [46,76,170,206,265,337,345,346,419,1169,1867,1870,2296] [0,1],u6 [274,219] [41,76,170,206,273,363,636,1083,1084,1087,1117,1261,2243],u6 [613] [46,76,161,170,244,265,347,426,1169,1262,1648,2141,2297],a6 [375,188] [41,334,345,536,947,1026,1403,1424,1425,1467,1503,1592,1891,2199,2298] [0,1],([410,0,319,2,3,4,5],[334,346,347,449,1169,1485,1648,1742,2210,2230,2299],[0]),([689,1,2,3,4,5],[76,345,346,419,426],[]),([566,410,0,2,3,4,5],[46,334,346,347,426,449,1169,1622,1648,1912,2230,2269,2300],[]),a6 [442,54] [76,449,736,896,933,1128,1129,1390,1391,2301,2302,2303] [1],a6 [375,237] [206,334,337,421,616,1381,1446,1448,1581,2199,2207,2225] [0,1],a6 [192,427] [38,76,170,265,337,345,363,394,410,419,591,933,964,967,1639,2304,2305,2306] [0,1],u6 [192,349] [41,76,265,419,967,1369,1398,1523,2236,2307],a6 [645] [46,64,76,170,206,265,337,346,419,1169,2052] [0,1],u6 [192,219] [41,206,265,334,363,593,785,964,967,1079,1081,1083,1084,2243],([566,0,391,2,3,4,5],[345,346,347,363,426,449,1622,1713,1714,2308,2309],[0]),a6 [410,54] [76,161,265,334,449,736,896,1128,1129,1131,1132,1912,2301,2303,2310,2311] [0,1],a6 [28,54] [41,161,170,265,363,519,885,1119,1120,1131,1215,1636,2303] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_9_0 : checkNodesBT W_17 g_17 F_17 P_17_9 A_17 B_17_8 9 N_17_9_0 = true := by decide +kernel
def N_17_9_1 : List NodeSpec := [a6 [9,23] [170,249,265,419,449,498,770,1208,2097] [0,1],e6 [691] [46,206,337,345,346,426,449,2312,2313],a6 [498] [46,170,206,265,337,345,346,347,426,933,1124,2314] [0,1],a6 [293,43] [76,161,337,426,538,657,671,1009,1397,1492,2234] [0,1],a6 [391,7] [41,116,221,260,358,363,426,577,708,927,933,2223] [0,1],([692,1,2,3,447,5],[168,206,363,419,1169],[]),a6 [298,222] [161,337,345,419,1290,1295,1298,1799,1836,2196,2197,2315,2316,2317] [0,1],a6 [410,7] [41,46,221,260,355,358,426,577,708,778,926,927,1883,1912,2223,2318] [0,1],e6 [274,321] [41,426,449,933,1088,1709,2105,2319],([341,1,2,3,4,447,5],[161,206,337,345,363,419,1169,1736,2260,2320],[1]),([679,1,2,3,4,447,5],[206,337,345,363,419,1169,1366,1473,2260,2320,2321],[]),e6 [274,525] [41,54,170,346,449,1088,1954,1961],a6 [274,278] [41,54,64,161,164,170,244,265,471,1056,1058,1060,1453,1454,1455,1459,1940] [0,1],a6 [192,447] [38,161,206,221,265,345,363,410,419,591,964,967,1473,1872,1941,2259] [0,1],([298,207,0,1,4,5],[76,334,419,449],[0,1]),a6 [188,56] [363,536,562,564,565,1196,1403,1763,2322,2323] [0,1],a6 [447,43] [64,161,206,345,537,538,933,1115,1473,2260,2324] [1],([349,0,2,3,4,5,525],[41,46,347,426,1169,1369,1786,2325],[0]),e6 [298,311] [161,419,1290,1296,2102,2251,2252,2253,2317],a6 [560] [46,54,76,170,206,265,345,346,347,1169,1571,1981,2326,2327] [0,1],a6 [495] [41,76,161,170,265,345,346,347,419,1630] [0,1],u6 [447,56] [64,161,363,562,564,838,933,1196,1473,2328],a6 [573] [41,46,54,76,206,265,334,337,346,1169,2329] [0,1],a6 [447,7] [116,161,206,221,260,363,577,778,933,1473,2330] [0,1],([693,1,2,3,4,5],[345,346,419,426,449,2331],[]),([192,0,1,3,4,29,5],[38,41,46,161,265,419,593],[0]),e6 [566,192] [41,46,265,334,346,347,363,419,589,591,593,967,1316,1318,1622,1623,2300,2307,2332],a6 [9,447] [76,161,170,206,221,345,419,479,501,770,1354,1473,2259,2333] [0,1],a6 [298,520] [41,337,419,1290,1295,1298,1863,2279,2315,2316,2317,2334,2335] [0,1],a6 [274,520] [41,76,170,337,363,933,1058,1087,1863,2279,2336,2337] [0,1],([694,1,2,3,4,5],[206,345,346,419,449],[]),a6 [219,427] [76,170,337,345,363,468,933,1003,1005,1006,1019,1235,1639,2304,2338,2339,2340] [0,1],a6 [40,321] [41,221,346,415,582,659,1709,1734,2105,2319,2341,2342,2343] [0,1],u6 [349,237] [76,334,494,709,1169,1398,1408,1446,1448,2213,2235],([293,1,2,3,4,311],[46,419,1169,2344],[0,1]),a6 [631] [46,265,337,345,346,347,426,449,1830,1982,2345] [0,1],a6 [219,207] ([41,46,76,170,206,468,872,994]++r 1002 5++[1019,1896,1897,1899,2346,2347,2348]) [0,1],a6 [612] [46,170,206,265,334,337,346,1169,1866,2045] [0,1],a6 [341,319] [206,346,670,1169,1484,1517,1736,1742,1819,1876,2210,2211,2212,2256,2349] [1],a6 [28,425] [41,345,419,885,1170,1215,1636,2138,2284,2285,2286,2350,2351] [1],a6 [192,319] [41,206,265,419,589,591,670,964,1742,1819,1876,2212,2236,2307] [0,1],u6 [192,442] [41,206,221,265,334,410,591,964,967,1316,1390,1391,1724,2093,2205,2238,2239,2307],e6 [219,323] [164,337,363,419,994,1003,1235,1352,1376,1813,1814],a6 [375,293] [46,337,345,421,426,528,947,1397,1400,1628,2086,2199,2258] [0,1],([293,1,391,2,3,4,5],[337,346,419,503,528,671,1628,2232,2242,2264],[0,1]),a6 [9,321] [41,221,249,346,449,1238,1354,1709,2105,2319,2343] [1],a6 [341,43] [76,161,538,657,1009,1371,1377,1492,1664,1666,2208,2234] [0,1],a6 [321,44] [41,221,422,797,798,1387,1507,1709,2105] [0,1],u6 [192,321] [41,221,426,591,1709,2105,2319,2342,2343],a6 [7] [41,76,170,265,334,363,426] [0,1],a6 [589] [46,206,265,337,345,346,449,670,2352] [0,1],a6 [375,311] [345,616,933,1467,1503,2102,2251,2252,2253,2353] [0,1],e6 [695] [41,76,161,170,345,363,419,783,2354],a6 [219,425] [64,363,1003,1006,1019,1235,1445,2284,2286,2350] [0,1],u6 [341,601] ([345,783,1517,1666,1824,1828,1830,2125]++r 2355 4),a6 [341,355] [39,161,170,345,783,1010,1047,1411,1413,1664,1666,1736,2208,2359,2360] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_9_1 : checkNodesBT W_17 g_17 F_17 P_17_9 A_17 B_17_8 9 N_17_9_1 = true := by decide +kernel
def N_17_9 := N_17_9_0 ++ N_17_9_1
def B_17_9 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_9
set_option maxRecDepth 500000 in
lemma B_17_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 9 xs.toFinset) B_17_9 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_17) (raw := r_17) (pspecs := ps_17) (used := U_17_9) S_17_ok
  have hm0 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_8_ok C_17_9_0
  have hm1 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_8_ok C_17_9_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_17_10 : List Nat := ([46,76,170,206,265,334,337,345,346,347,363,419,426,449,676,942,1169,1820,2202,2223,2230,2307,2320,2344]++r 2361 6)
def P_17_10 : BT (Option BoundPool) := buildPoolsSubBT 12 W_17 r_17 S_17 ps_17 U_17_10
def N_17_10 : List NodeSpec := [a6 [219] [76,206,334,337,345,346,347,363,426] [0,1],a6 [7] [76,334,337,347,363,426,2223] [0,1],a6 [23] [76,334,363,426] [0,1],u6 [566] [76,334,345,346,347,363,426,449,676,1169,1820],a6 [679] [76,170,206,334,337,345,346,363,419,449,1169,1820] [0,1],a6 [447] [76,206,337,363,419,1169,2320] [0,1],a6 [40] [76,206,265,346,347,363,419] [0,1],a6 [404] [46,76,206,334,337,347,426,449,1169,1820] [0,1],a6 [349] [46,76,334,345,346,426,1169,1820] [0,1],a6 [350] [334,337,347,426,449,1169,1820,2361] [0,1],a6 [410] [46,76,206,265,334,337,346,347,426,449,1169,1820,2230,2362] [0,1],a6 [375] [46,76,206,334,337,345,346,347,426] [0,1],u6 [687] [76,206,334,345,346,363,419,449,942,1820],a6 [237] [76,206,334,337,345,346,363,419,1169,1820] [0,1],a6 [692] [76,206,334,345,346,363,419,426,1820] [0,1],a6 [321] [206,347,426,449,1169] [0,1],a6 [391] [46,76,206,334,337,347,363,419,426,449,1820] [0,1],a6 [529] [46,76,206,334,337,347,426,449,676,1169,1820,2363] [0,1],e6 [696] [334,345,419,426,449,1169,1820],a6 [293] [46,76,206,334,345,346,419,1169,1820] [0,1],a6 [290] [46,76,206,334,337,345,346,347,363,449] [0,1],a6 [341] [46,76,206,334,337,345,346,363,419,1169,1820,2344] [0,1],a6 [9] [46,76,170,206,265,337,346,347,419,449,2202] [0,1],a6 [442] [46,76,206,334,337,347,426,449,1169,1820,2364,2365] [0,1],a6 [298] [46,76,206,265,337,345,346,347,419,449] [0,1],a6 [28] [46,76,265,337,419,426] [0,1],a6 [6] [46,76,206,346,347,419,449] [0,1],a6 [188] [46,76,206,334,337,347,363,419,1169,1820,2366] [0,1],a6 [29] [46,76,347,419,426] [0,1],a6 [274] [170,206,334,337,345,346,347,363,449] [0,1],a6 [43] [46,334,337,345,426,449] [0,1],a6 [192] [46,76,206,265,337,345,346,347,363,419,2307] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_10 : checkNodesBT W_17 g_17 F_17 P_17_10 A_17 B_17_9 10 N_17_10 = true := by decide +kernel
def B_17_10 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_10
set_option maxRecDepth 500000 in
lemma B_17_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 10 xs.toFinset) B_17_10 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_9_ok C_17_10
def U_17_11 : List Nat := [1820]
def P_17_11 : BT (Option BoundPool) := buildPoolsSubBT 12 W_17 r_17 S_17 ps_17 U_17_11
def N_17_11 : List NodeSpec := [a6 [] [1820] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_11 : checkNodesBT W_17 g_17 F_17 P_17_11 A_17 B_17_10 11 N_17_11 = true := by decide +kernel
def B_17_11 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_11
set_option maxRecDepth 500000 in
lemma B_17_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 11 xs.toFinset) B_17_11 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_10_ok C_17_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,6,22),(VAR 5,5,37)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_11 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 12 := lower_of_forestBT root_17_ok B_17_11_ok root_17_in

def g_orig := (d 0xfee8eee8fee0e8a0)
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,4),(1,2),(2,5)]) (by decide +kernel) low_17
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4276678376 * 2 ^ 32 + 4276152480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.or,[1,4]⟩,⟨.and,[3,6]⟩,⟨.and,[7,2]⟩,⟨.and,[1,0]⟩,⟨.or,[3,9]⟩,⟨.or,[2,7]⟩,⟨.and,[5,10]⟩,⟨.or,[11,12]⟩,⟨.or,[8,0]⟩,⟨.or,[5,4]⟩,⟨.and,[15,1]⟩,⟨.or,[16,14]⟩,⟨.and,[17,13]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_45460

open PEqualNP.Outside.L_meta_45460 in
theorem PEqualNP.Outside.L_meta_45460 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678376 * 2 ^ 32 + 4276152480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4276152480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
