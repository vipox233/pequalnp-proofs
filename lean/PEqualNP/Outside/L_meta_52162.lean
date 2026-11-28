import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52162
namespace Wide
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 256
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
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
set_option maxRecDepth 16000 in
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
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
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
def varsOf (m : Nat) : List Nat :=
  (List.range 8).filterMap fun i => if m.testBit i then some (VAR i) else none
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
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL256))
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
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL256]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 256 r'.val |> fun e => by simpa [this] using e⟩
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
      have hi7 : i < 8 := by simpa using hi2
      have hv : (varsOf 255)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 255)[i]'(by simpa [seeds] using hi1) = VAR i := by
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

end Wide
namespace Small
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
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
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
def hashWs (nb : Nat) (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) % nb
def bucketContains (buckets : Array (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (buckets.getD (hashWs buckets.size s) []).contains s
def closeChild (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContains prevBuckets (ws.map (permWord sw)))
lemma closeChild_sound {raw T pools autos prevBuckets k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T k xs.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChild pools autos prevBuckets k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContains at hhit
    simp only [Array.getD, List.contains_eq_mem, decide_eq_true_eq] at hhit
    split at hhit
    next hlt_b =>
      have himp := hPrev _ hlt_b _ hhit
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
        · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
              Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
      have hfix_r : permWord sw.reverse T = T := by
        conv_lhs => rw [← hfix]
        exact hinv_w T hT
      have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [permWord_eq_renameW sw hsv x (hlt x hx)]
        exact renameW_lt _ x
      have hrot := rotate_impossible himp sw.reverse hvr hT hfix_r hmap_lt
      have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
        exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
      rwa [hback] at hrot
    next => simp at hhit
def evalMove (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild pools autos prevBuckets (cap - 1) rest (d, a.1, b.1)
def testPair (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMove cap n fmask ws cov pools autos prevBuckets d a b z
  go false false && go true false && go false true && go true true
def testAll (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPair cap n fmask ws cov pools autos prevBuckets a b)) &&
      testAll cap n fmask ws cov pools autos prevBuckets bs
lemma evalMove_sound {raw T pos neg ws pools autos prevBuckets cap a b d ka kb}
    (hT : T < 2^128)
    (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (hd : d < 4)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (hnz : (dbin d a b).1 ≠ 0) (hfr : (dbin d a b).1 ∉ ws.map Prod.fst)
    (test : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets
      d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => hfr ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact hlt w (sub.subset hw)
  have hfr_b : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
    exact hfr (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    change _ = (z.1 :: rest.map Prod.fst).length
    rw [List.length_cons, List.length_map, delTwo_len ws a b ka kb ha hb ne, Nat.add_comm 1]
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
  unfold evalMove at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  exact closeChild_sound (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT hPools hAutos hPrev ndc hltc test k hk h
lemma testAll_pair {cap n fmask ws cov pools autos prevBuckets l}
    (h : testAll cap n fmask ws cov pools autos prevBuckets l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets a b d = true) ∨
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAll, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma node_sound {raw T pos neg ws pools autos prevBuckets cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (checks : cap = 0 ∨ testAll cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0; intro k hk h
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
      (ht : testPair cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPair, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMove_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAll_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
lemma lower_of_forest {roots T cap} {topBuckets : Array (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : ∀ i (hi : i < topBuckets.size), ∀ xs ∈ topBuckets[i], Impossible T cap xs.toFinset)
    (hRoot : bucketContains topBuckets roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContains Array.getD at hRoot
    dsimp only at hRoot
    split at hRoot
    next hi => exact hTop _ hi _ (List.contains_iff_mem.mp hRoot)
    next => simp at hRoot
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def buildWires (base : List Decor) (steps : List (Nat × Nat × Nat)) : Array Decor :=
  steps.foldl (fun arr s =>
    let a := arr.getD s.2.1 (0, 0, 0)
    let b := arr.getD s.2.2 (0, 0, 0)
    arr.push (dbin s.1 a b)) base.toArray
lemma buildWires_faithful {pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    ∀ x ∈ (buildWires base steps).toList, faithful pos neg x ∧ x.1 < 2^128 := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hstep : ∀ (arr : Array Decor) (s : Nat × Nat × Nat),
      (∀ x ∈ arr.toList, faithful pos neg x ∧ x.1 < 2^128) →
      ∀ x ∈ (arr.push (dbin s.1 (arr.getD s.2.1 (0, 0, 0)) (arr.getD s.2.2 (0, 0, 0)))).toList,
        faithful pos neg x ∧ x.1 < 2^128 := by
    intro arr s harr x hx
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact harr x hx
    · have hget (i : Nat) : faithful pos neg (arr.getD i (0, 0, 0)) ∧ (arr.getD i (0, 0, 0)).1 < 2^128 := by
        unfold Array.getD
        split
        next hi => exact harr arr[i] (Array.getElem_mem_toList hi)
        next => exact hdef
      exact ⟨faithful_bin s.1 (hget s.2.1).1 (hget s.2.2).1, bin_lt s.1 _ _ (hget s.2.1).2 (hget s.2.2).2⟩
  unfold buildWires
  have hinit : ∀ x ∈ base.toArray.toList, faithful pos neg x ∧ x.1 < 2^128 := by simpa using hbase
  clear hbase
  generalize base.toArray = acc at hinit ⊢
  induction steps generalizing acc with
  | nil => exact hinit
  | cons s ss ih => exact ih _ (hstep acc s hinit)
lemma array_forall_of_list {α : Type} {P : α → Prop} {l : List α} (h : ∀ x ∈ l, P x) :
    ∀ i (hi : i < l.toArray.size), P l.toArray[i] :=
  fun i hi => h l.toArray[i] (Array.getElem_mem_toList hi)
def buildPools (W : Array Decor) (raw : List Nat) (slices : Array (Nat × Nat))
    (pspecs : List PoolSpec) : Array (Option BoundPool) :=
  (pspecs.map fun (slIdx, chIdxs) =>
    match slices[slIdx]? with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
      materialize raw cs dom lb).toArray
lemma buildPools_sound {W : Array Decor} {raw T} {slices : Array (Nat × Nat)} {pspecs : List PoolSpec}
    (hSlices : ∀ i (hi : i < slices.size), Slice raw T slices[i].1 slices[i].2) :
    ∀ i (hi : i < (buildPools W raw slices pspecs).size),
      ∀ c, (buildPools W raw slices pspecs)[i] = some c → ValidPool raw T c := by
  intro i hi c hc
  unfold buildPools at hi hc
  have hmem : some c ∈ pspecs.map (fun (slIdx, chIdxs) =>
      match slices[slIdx]? with
      | none => none
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
        materialize raw cs dom lb) := by
    rw [← hc]
    exact Array.getElem_mem_toList hi
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp hmem
  cases hget_sl : slices[slIdx]? with
  | none => simp [hget_sl] at hmat
  | some sl =>
    simp only [hget_sl] at hmat
    have ⟨hsi, hval⟩ := Array.getElem?_eq_some_iff.mp hget_sl
    exact materialize_sound (hval ▸ hSlices slIdx hsi) hmat
def checkNode (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  let vals := ws.map Prod.fst
  let pools := ns.2.1.filterMap fun pIdx => poolTable.getD pIdx none
  let nodeAutos := ns.2.2.filterMap fun aIdx => autosTable[aIdx]?
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAll k ws.length fmask ws (coverage ws) pools nodeAutos prevBuckets ws)
def checkNodes (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNode W T fmask poolTable autosTable prevBuckets k)
lemma checkNode_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (ok : checkNode W T (fullMask pos.length) poolTable autosTable prevBuckets k ns = true) :
    Impossible T k ((ns.1.map fun idx => (W.getD idx (0, 0, 0)).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (W.getD idx (0, 0, 0)) ∧ (W.getD idx (0, 0, 0)).1 < 2^128 := by
    unfold Array.getD; split
    next hi => exact hW W[idx] (Array.getElem_mem_toList hi)
    next => exact hdef
  unfold checkNode at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (W.getD idx (0, 0, 0)).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply node_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun c hc => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hc
      unfold Array.getD at hmat
      split at hmat
      next hi => exact hPoolTable pIdx hi c hmat
      next => simp at hmat)
    (fun sw hsw => by
      obtain ⟨aIdx, _, ha⟩ := List.mem_filterMap.mp hsw
      have ⟨hi, hval⟩ := Array.getElem?_eq_some_iff.mp ha
      exact hAutos sw (hval ▸ Array.getElem_mem_toList hi))
    hPrev ok.2
def nodeVals (W : Array Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (W.getD idx (0, 0, 0)).1)
def insertBucket (buckets : Array (List (List Nat))) (xs : List Nat) : Array (List (List Nat)) :=
  let idx := hashWs buckets.size xs
  if h : idx < buckets.size then
    let b := buckets[idx]
    if b.contains xs then buckets else buckets.set idx (xs :: b) h
  else buckets
def buildBuckets (nb : Nat) (W : Array Decor) (nodes : List NodeSpec) : Array (List (List Nat)) :=
  nodes.foldl (fun acc ns => insertBucket acc (nodeVals W ns)) (Array.replicate nb [])
lemma insertBucket_mem {bks : Array (List (List Nat))} {P : List Nat → Prop} {xs : List Nat}
    (hb : ∀ i (hi : i < bks.size), ∀ ys ∈ bks[i], P ys) (hxs : P xs) :
    ∀ i (hi : i < (insertBucket bks xs).size), ∀ ys ∈ (insertBucket bks xs)[i], P ys := by
  unfold insertBucket
  dsimp only
  split
  next hidx =>
    split
    · exact hb
    · intro i hi ys hys
      rw [Array.size_set] at hi
      rw [Array.getElem_set] at hys
      split at hys
      next =>
        rcases List.mem_cons.mp hys with rfl | hys'
        · exact hxs
        · exact hb _ hidx ys hys'
      next => exact hb i hi ys hys
  next => exact hb
lemma buildBuckets_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k nb}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (hNodes : checkNodes W T (fullMask pos.length) poolTable autosTable prevBuckets k nodes = true) :
    ∀ i (hi : i < (buildBuckets nb W nodes).size), ∀ xs ∈ (buildBuckets nb W nodes)[i], Impossible T k xs.toFinset := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeVals W ns).toFinset := fun ns hns => by
    unfold nodeVals
    rw [sortNats_toFinset]
    exact checkNode_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBuckets
  have hinit : ∀ i (hi : i < (Array.replicate nb ([] : List (List Nat))).size),
      ∀ xs ∈ (Array.replicate nb ([] : List (List Nat)))[i], Impossible T k xs.toFinset := by
    intro i hi xs hxs; simp at hxs
  generalize Array.replicate nb ([] : List (List Nat)) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      (insertBucket acc (nodeVals W ns)) (insertBucket_mem hinit (hmem ns (List.mem_cons_self ..)))
lemma checkNodesBT_mem {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
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
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := trivial
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

def dualRow (r : Row) : Row := ⟨(r.val ^^^ 127) % 128, Nat.mod_lt _ (by decide)⟩

lemma map_available (f : Row → Row) {b c : List Wire}
    (cover : ∀ w ∈ b, Avail c (restrictW f w)) {w : Wire} (hw : Avail b w) :
    Avail c (restrictW f w) := by
  rcases hw with hb | ⟨bit,rfl⟩ | hi
  · exact cover _ hb
  · exact Or.inr (Or.inl ⟨bit,rfl⟩)
  · have h : Avail c (invW (restrictW f w)) := cover _ hi
    simpa only [invW_inv] using avail_inv h

lemma map_reach (f : Row → Row) {R S : List Wire}
    (cover : ∀ w ∈ R, Avail S (restrictW f w)) {p b} (hr : Reach R p b) :
    ∃ c, Reach S p c ∧ ∀ w ∈ b, Avail c (restrictW f w) := by
  induction p generalizing b with
  | zero =>
    have hb : b = R := hr
    exact ⟨S,rfl,hb.symm ▸ cover⟩
  | succ p ih =>
    obtain ⟨op,b,a,d,prev,ha,hd,rfl⟩ := hr
    obtain ⟨c,hc,hmap⟩ := ih prev
    let w := comb2 op (restrictW f a) (restrictW f d)
    have eq : restrictW f (comb2 op a d) = w := by cases op <;> rfl
    refine ⟨w :: c,⟨op,c,_,_,hc,map_available f hmap ha,map_available f hmap hd,rfl⟩,?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | hold
    · rw [eq]
      exact Or.inl List.mem_cons_self
    · exact avail_cons w (hmap t hold)

lemma dualLower {roots : List Nat} {T G L : Nat}
    (hvars : ∀ r : Row, roots.all (fun a => decide (obs a (dualRow r) = !(obs a r))) = true)
    (hgoal : ∀ r : Row, (!(obs T (dualRow r))) = obs G r)
    (prior : Lower roots G L) : Lower roots T L := by
  intro p bank hr hav
  have maps (w : Wire) (hw : w ∈ roots.map obs) : Avail (roots.map obs) (restrictW dualRow w) := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    have eq : restrictW dualRow (obs a) = invW (obs a) :=
      funext fun r => of_decide_eq_true (List.all_eq_true.mp (hvars r) a ha)
    rw [eq]
    exact avail_inv (Or.inl (List.mem_map.mpr ⟨a,ha,rfl⟩))
  obtain ⟨c,hc,hmap⟩ := map_reach dualRow maps hr
  have eq : invW (restrictW dualRow (obs T)) = obs G := funext hgoal
  exact prior p c hc (eq ▸ avail_inv (map_available dualRow hmap hav))

def lb0 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def lb11 : List Nat := varsOf 14
def lb90 : List Nat := [6,6,10,10,12,12,6,10,12]
def lb82 : List Nat := [4,2,8,2,8,4,8,4,2]
def lb62 : Nat := fullMask 9
def lb26 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bc,0x54)]
def lb108 : List (Nat × Nat × Nat) := []
def lb18 : Array Decor := buildWires lb26 lb108
def lb22 : Array (List (Nat × Nat)) := #[]
def lb102 : List (Nat × Nat) := []
def lb104 : Array (Nat × Nat) := lb102.toArray
def lb92 : List PoolSpec := []
def lb7 : Array (Option BoundPool) := buildPools lb18 lb11 lb104 lb92
lemma lb68 : goodPairs lb0 lb90 lb82 := goodPairs_of (by decide +kernel)
lemma lb27 : ∀ x ∈ lb26, faithful lb90 lb82 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb19 : ∀ x ∈ lb18.toList, faithful lb90 lb82 x ∧ x.1 < 2^128 := buildWires_faithful lb27
lemma lb23 : ∀ sw ∈ lb22.toList, swapsValid sw = true ∧ permWord sw lb0 = lb0 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma lb105 : ∀ i (hi : i < lb104.size), Slice lb11 lb0 lb104[i].1 lb104[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb11 lb0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb8 : ∀ i (hi : i < lb7.size), ∀ c, lb7[i] = some c → ValidPool lb11 lb0 c := buildPools_sound lb105
def lb36 : Array (List (List Nat)) := #[]
lemma lb37 : ∀ i (hi : i < lb36.size), ∀ xs ∈ lb36[i], Impossible lb0 (0 - 1) xs.toFinset := by intro i hi; simp [lb36] at hi
def lb84 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb51 : checkNodes lb18 lb0 lb62 lb7 lb22 lb36 0 lb84 = true := by decide +kernel
def lb30 : Array (List (List Nat)) := buildBuckets 1 lb18 lb84
lemma lb31 : ∀ i (hi : i < lb30.size), ∀ xs ∈ lb30[i], Impossible lb0 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb68 lb19 lb8 lb23 lb37 lb51
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb52 : checkNodes lb18 lb0 lb62 lb7 lb22 lb30 1 lb84 = true := by decide +kernel
lemma lb32 : ∀ i (hi : i < lb30.size), ∀ xs ∈ lb30[i], Impossible lb0 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb68 lb19 lb8 lb23 lb31 lb52
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb53 : checkNodes lb18 lb0 lb62 lb7 lb22 lb30 2 lb84 = true := by decide +kernel
lemma lb33 : ∀ i (hi : i < lb30.size), ∀ xs ∈ lb30[i], Impossible lb0 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb68 lb19 lb8 lb23 lb32 lb53
def lb85 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb54 : checkNodes lb18 lb0 lb62 lb7 lb22 lb30 3 lb85 = true := by decide +kernel
def lb34 : Array (List (List Nat)) := buildBuckets 1 lb18 lb85
lemma lb35 : ∀ i (hi : i < lb34.size), ∀ xs ∈ lb34[i], Impossible lb0 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb68 lb19 lb8 lb23 lb33 lb54
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb65 : forestRootCheck lb11 lb0 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb64 : bucketContains lb34 lb11 = true := by decide +kernel
lemma lb70 : Lower lb11 lb0 4 := lower_of_forest lb65 lb35 lb64
def lb1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def lb12 : List Nat := varsOf 7
lemma lb73 : carryOK [(0,3),(0,2),(0,1)] lb12 lb1 lb11 lb0 = true := by decide +kernel
lemma lb71 : Lower lb12 lb1 4 := carry_of lb73 lb70
def lb3 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def lb14 : List Nat := varsOf 19
lemma lb77 : carryOK [(3,4),(0,2),(0,1)] lb14 lb3 lb11 lb0 = true := by decide +kernel
lemma lb74 : Lower lb14 lb3 4 := carry_of lb77 lb70
def lb5 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def lb16 : List Nat := varsOf 21
lemma lb79 : carryOK [(3,4),(0,1)] lb16 lb5 lb11 lb0 = true := by decide +kernel
lemma lb78 : Lower lb16 lb5 4 := carry_of lb79 lb70
def lb6 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def lb17 : List Nat := varsOf 22
lemma lb81 : carryOK [(3,4)] lb17 lb6 lb11 lb0 = true := by decide +kernel
lemma lb80 : Lower lb17 lb6 4 := carry_of lb81 lb70
def lb2 : Nat := 0xe8e88080e8e88080e8e88080e8e88080
def lb13 : List Nat := varsOf 23
def lb91 : List Nat := [7,7,7,19,19,19,21,21,21,22,22,22,7,7,7,19,19,19,21,21,21,22,22,22]
def lb83 : List Nat := [6,5,3,18,17,3,20,17,5,20,18,6,17,18,20,5,6,20,3,6,18,3,5,17]
def lb63 : Nat := fullMask 24
def lb28 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ff1ff,0xe491b6),(0xcccccccccccccccccccccccccccccccc,0xe3fe3f,0x3d2c2d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfc7fc7,0x4bcb43),(0xffff0000ffff0000ffff0000ffff0000,0xff8ff8,0x9276d8)]
def lb109 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def lb20 : Array Decor := buildWires lb28 lb109
def lb24 : Array (List (Nat × Nat)) := #[[],[(2,4)],[(0,1)],[(2,4),(0,1)],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def lb103 : List (Nat × Nat) := [(subcube 0 4,4),(subcube 0 1,4),(subcube 0 2,4),(subcube 0 16,4)]
def lb106 : Array (Nat × Nat) := lb103.toArray
def lb93 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def lb9 : Array (Option BoundPool) := buildPools lb20 lb13 lb106 lb93
lemma lb69 : goodPairs lb2 lb91 lb83 := goodPairs_of (by decide +kernel)
lemma lb29 : ∀ x ∈ lb28, faithful lb91 lb83 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb21 : ∀ x ∈ lb20.toList, faithful lb91 lb83 x ∧ x.1 < 2^128 := buildWires_faithful lb29
lemma lb25 : ∀ sw ∈ lb24.toList, swapsValid sw = true ∧ permWord sw lb2 = lb2 := autos_of (by decide +kernel)
lemma lb95 : sliceDirectCheck 0 4 0 lb13 lb2 lb14 lb3 = true := by decide +kernel
lemma lb94 : Slice lb13 lb2 (subcube 0 4) 4 := slice_direct lb95 lb74
lemma lb97 : sliceDirectCheck 0 1 0 lb13 lb2 lb17 lb6 = true := by decide +kernel
lemma lb96 : Slice lb13 lb2 (subcube 0 1) 4 := slice_direct lb97 lb80
lemma lb99 : sliceDirectCheck 0 2 0 lb13 lb2 lb16 lb5 = true := by decide +kernel
lemma lb98 : Slice lb13 lb2 (subcube 0 2) 4 := slice_direct lb99 lb78
lemma lb101 : sliceDirectCheck 0 16 0 lb13 lb2 lb12 lb1 = true := by decide +kernel
lemma lb100 : Slice lb13 lb2 (subcube 0 16) 4 := slice_direct lb101 lb71
set_option maxRecDepth 200000 in
lemma lb107 : ∀ i (hi : i < lb106.size), Slice lb13 lb2 lb106[i].1 lb106[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb13 lb2 p.1 p.2) (forall_cons lb94 (forall_cons lb96 (forall_cons lb98 (forall_cons lb100 (fun _ h => (List.not_mem_nil h).elim)))))
lemma lb10 : ∀ i (hi : i < lb9.size), ∀ c, lb9[i] = some c → ValidPool lb13 lb2 c := buildPools_sound lb107
lemma lb50 : ∀ i (hi : i < lb36.size), ∀ xs ∈ lb36[i], Impossible lb2 (0 - 1) xs.toFinset := by intro i hi; simp [lb36] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb55 : checkNodes lb20 lb2 lb63 lb9 lb24 lb36 0 lb84 = true := by decide +kernel
def lb38 : Array (List (List Nat)) := buildBuckets 1 lb20 lb84
lemma lb39 : ∀ i (hi : i < lb38.size), ∀ xs ∈ lb38[i], Impossible lb2 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb69 lb21 lb10 lb25 lb50 lb55
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb56 : checkNodes lb20 lb2 lb63 lb9 lb24 lb38 1 lb84 = true := by decide +kernel
lemma lb40 : ∀ i (hi : i < lb38.size), ∀ xs ∈ lb38[i], Impossible lb2 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb69 lb21 lb10 lb25 lb39 lb56
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb57 : checkNodes lb20 lb2 lb63 lb9 lb24 lb38 2 lb84 = true := by decide +kernel
lemma lb41 : ∀ i (hi : i < lb38.size), ∀ xs ∈ lb38[i], Impossible lb2 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb69 lb21 lb10 lb25 lb40 lb57
def lb86 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb58 : checkNodes lb20 lb2 lb63 lb9 lb24 lb38 3 lb86 = true := by decide +kernel
def lb42 : Array (List (List Nat)) := buildBuckets 1 lb20 lb86
lemma lb43 : ∀ i (hi : i < lb42.size), ∀ xs ∈ lb42[i], Impossible lb2 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb69 lb21 lb10 lb25 lb41 lb58
def lb87 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb59 : checkNodes lb20 lb2 lb63 lb9 lb24 lb42 4 lb87 = true := by decide +kernel
def lb44 : Array (List (List Nat)) := buildBuckets 2 lb20 lb87
lemma lb45 : ∀ i (hi : i < lb44.size), ∀ xs ∈ lb44[i], Impossible lb2 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb69 lb21 lb10 lb25 lb43 lb59
def lb88 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb60 : checkNodes lb20 lb2 lb63 lb9 lb24 lb44 5 lb88 = true := by decide +kernel
def lb46 : Array (List (List Nat)) := buildBuckets 1 lb20 lb88
lemma lb47 : ∀ i (hi : i < lb46.size), ∀ xs ∈ lb46[i], Impossible lb2 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb69 lb21 lb10 lb25 lb45 lb60
def lb89 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb61 : checkNodes lb20 lb2 lb63 lb9 lb24 lb46 6 lb89 = true := by decide +kernel
def lb48 : Array (List (List Nat)) := buildBuckets 1 lb20 lb89
lemma lb49 : ∀ i (hi : i < lb48.size), ∀ xs ∈ lb48[i], Impossible lb2 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb69 lb21 lb10 lb25 lb47 lb61
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb67 : forestRootCheck lb13 lb2 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 4,19,3)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb66 : bucketContains lb48 lb13 = true := by decide +kernel
lemma lb72 : Lower lb13 lb2 7 := lower_of_forest lb67 lb49 lb66
def lb4 : Nat := 0xe8e88080e8e80000e8e88080e8e80000
def lb15 : List Nat := varsOf 55
lemma lb76 : liftCheck 0 32 lb15 lb4 lb13 lb2 [(VAR 5,39,7)] = true := by decide +kernel
lemma lb75 : Lower lb15 lb4 8 := lift_of lb76 lb72
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q1d : Lower (varsOf 61) 0xfaa0a000aaa0a000faa0a000aaa0a000 8 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := lb15) (T2 := lb4) _ lb75
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q1 : Lower (varsOf 61) 0xfffafaaafffafaa0fffafaaafffafaa0 8 := dualLower (by decide +kernel) (by decide +kernel) q1d
def lb206 : Nat := 0xffffff00ff000000ffffff00ff000000
def lb217 : List Nat := varsOf 56
def lb296 : List Nat := [24,24,40,40,48,48,24,40,48]
def lb290 : List Nat := [16,8,32,8,32,16,32,16,8]
def lb233 : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def lb223 : BT Decor := buildWiresBT 2 lb233 lb108
def lb227 : List (List (Nat × Nat)) := []
def lb229 : BT (List (Nat × Nat)) := btOfList 1 lb227
def lb312 : List (Option (Nat × Nat)) := []
def lb314 : BT (Option (Nat × Nat)) := btOfList 1 lb312
def lb298 : BT (Option PoolSpec) := btOfList 1 []
lemma lb276 : goodPairs lb206 lb296 lb290 := goodPairs_of (by decide +kernel)
lemma lb234 : ∀ x ∈ lb233, faithful lb296 lb290 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb224 : btAll (fun x => faithful lb296 lb290 x ∧ x.1 < 2^128) lb223 := buildWiresBT_faithful lb234
set_option maxRecDepth 500000 in
lemma lb230 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb206 = lb206) lb229 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb315 : btAll (fun o => ∀ p, o = some p → Slice lb217 lb206 p.1 p.2) lb314 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb217 lb206 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
def lb243 : BT (List (List Nat)) := BT.empty
lemma lb244 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb206 (0 - 1) xs.toFinset) lb243 := trivial
def lb212 : BT (Option BoundPool) := buildPoolsSubBT 1 lb223 lb217 lb314 lb298 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb259 : checkNodesBT lb223 lb206 lb62 lb212 lb229 lb243 0 lb84 = true := by decide +kernel
def lb237 : BT (List (List Nat)) := buildBucketsBT lb223 lb84
set_option maxRecDepth 500000 in
lemma lb238 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb206 0 xs.toFinset) lb237 :=
  buildBucketsBT_sound (by decide) lb276 lb224 (buildPoolsSubBT_sound lb315) lb230 lb244 lb259
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb260 : checkNodesBT lb223 lb206 lb62 lb212 lb229 lb237 1 lb84 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb239 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb206 1 xs.toFinset) lb237 :=
  buildBucketsBT_sound (by decide) lb276 lb224 (buildPoolsSubBT_sound lb315) lb230 lb238 lb260
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb261 : checkNodesBT lb223 lb206 lb62 lb212 lb229 lb237 2 lb84 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb240 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb206 2 xs.toFinset) lb237 :=
  buildBucketsBT_sound (by decide) lb276 lb224 (buildPoolsSubBT_sound lb315) lb230 lb239 lb261
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb262 : checkNodesBT lb223 lb206 lb62 lb212 lb229 lb237 3 lb85 = true := by decide +kernel
def lb241 : BT (List (List Nat)) := buildBucketsBT lb223 lb85
set_option maxRecDepth 500000 in
lemma lb242 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb206 3 xs.toFinset) lb241 :=
  buildBucketsBT_sound (by decide) lb276 lb224 (buildPoolsSubBT_sound lb315) lb230 lb240 lb262
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb273 : forestRootCheck lb217 lb206 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb272 : bucketContainsBT lb241 lb217 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb278 : Lower lb217 lb206 4 := lower_of_forestBT lb273 lb242 lb272
lemma lb287 : carryOK [(1,2),(1,5),(2,4),(1,3)] lb11 lb0 lb217 lb206 = true := by decide +kernel
lemma lb286 : Lower lb11 lb0 4 := carry_of lb287 lb278
def lb211 : Nat := 0xfff0ff00ff000000fff0ff00ff000000
def lb222 : List Nat := varsOf 60
lemma lb289 : liftCheck 0 4 lb222 lb211 lb217 lb206 [(VAR 2,52,48)] = true := by decide +kernel
lemma lb288 : Lower lb222 lb211 5 := lift_of lb289 lb278
def lb207 : Nat := 0xfcc0fc00fcc0fc00fcc0fc00fcc0fc00
def lb218 : List Nat := varsOf 30
lemma lb280 : carryOK [(1,2),(2,5),(1,4)] lb218 lb207 lb222 lb211 = true := by decide +kernel
lemma lb279 : Lower lb218 lb207 5 := carry_of lb280 lb288
def lb208 : Nat := 0xfcc0fcc0fc00fc00fcc0fcc0fc00fc00
def lb219 : List Nat := varsOf 46
lemma lb282 : carryOK [(2,5),(1,4)] lb219 lb208 lb222 lb211 = true := by decide +kernel
lemma lb281 : Lower lb219 lb208 5 := carry_of lb282 lb288
def lb209 : Nat := 0xffccff00ff000000ffccff00ff000000
def lb220 : List Nat := varsOf 58
lemma lb284 : carryOK [(1,2)] lb220 lb209 lb222 lb211 = true := by decide +kernel
lemma lb283 : Lower lb220 lb209 5 := carry_of lb284 lb288
def lb210 : Nat := 0xfcc0fc00fc000000fcc0fc00fc000000
def lb221 : List Nat := varsOf 62
def lb297 : List Nat := [26,26,26,28,28,28,30,30,42,42,42,44,44,44,46,46,54,54,54,54,58,58,60,60,26,26,26,26,26,26,28,28,28,28,28,28,42,42,42,42,42,42,44,44,44,44,44,44,54,54]
def lb291 : List Nat := [24,18,10,24,20,12,22,14,40,34,10,40,36,12,38,14,52,50,38,22,56,50,56,52,14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56,14,56]
def lb271 : Nat := fullMask 50
def lb235 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x303f03f3fc7c7,0x13cf3cf2ec6c6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3fc0fc0cff8f8,0x15d75d78df0f0),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffffff0ffff,0x386186150adad),(0xffff0000ffff0000ffff0000ffff0000,0x3000fffff00ff,0x2ebaebafb005b),(0xffffffff00000000ffffffff00000000,0x3fff000ffff00,0x2f3cf3cf75b00)]
def lb318 : List (Nat × Nat × Nat) := [(0,0,3),(2,0,2),(0,0,2),(0,6,3),(3,5,2),(1,5,2),(3,7,3),(0,7,3),(3,6,3),(3,7,1),(0,1,10),(3,13,4),(3,12,1)]
def lb225 : BT Decor := buildWiresBT 5 lb235 lb318
def lb228 : List (List (Nat × Nat)) := [[],[(2,5),(1,4)],[(4,5)],[(1,2)],[(4,5),(1,2)],[(1,2),(2,5),(1,4)]]
def lb231 : BT (List (Nat × Nat)) := btOfList 3 lb228
def lb313 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 6,4),some (subcubeFast 0 4,5),some (subcubeFast 0 2,5),some (subcubeFast 0 32,5),some (subcubeFast 0 48,4)]
def lb316 : BT (Option (Nat × Nat)) := btOfList 3 lb313
def lb299 : BT (Option PoolSpec) := btOfList 3 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[])]
lemma lb277 : goodPairs lb210 lb297 lb291 := goodPairs_of (by decide +kernel)
lemma lb236 : ∀ x ∈ lb235, faithful lb297 lb291 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb226 : btAll (fun x => faithful lb297 lb291 x ∧ x.1 < 2^128) lb225 := buildWiresBT_faithful lb236
set_option maxRecDepth 500000 in
lemma lb232 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb210 = lb210) lb231 := btAll_ofList (autos_of (by decide +kernel))
lemma lb301 : sliceDirectCheck 0 16 0 lb221 lb210 lb219 lb208 = true := by decide +kernel
lemma lb300 : Slice lb221 lb210 (subcubeFast 0 16) 5 := slice_fast_direct lb301 lb281
lemma lb303 : sliceDirectCheck 0 6 0 lb221 lb210 lb217 lb206 = true := by decide +kernel
lemma lb302 : Slice lb221 lb210 (subcubeFast 0 6) 4 := slice_fast_direct lb303 lb278
lemma lb305 : sliceDirectCheck 0 4 0 lb221 lb210 lb220 lb209 = true := by decide +kernel
lemma lb304 : Slice lb221 lb210 (subcubeFast 0 4) 5 := slice_fast_direct lb305 lb283
lemma lb307 : sliceDirectCheck 0 2 0 lb221 lb210 lb222 lb211 = true := by decide +kernel
lemma lb306 : Slice lb221 lb210 (subcubeFast 0 2) 5 := slice_fast_direct lb307 lb288
lemma lb309 : sliceDirectCheck 0 32 0 lb221 lb210 lb218 lb207 = true := by decide +kernel
lemma lb308 : Slice lb221 lb210 (subcubeFast 0 32) 5 := slice_fast_direct lb309 lb279
lemma lb311 : sliceDirectCheck 0 48 0 lb221 lb210 lb11 lb0 = true := by decide +kernel
lemma lb310 : Slice lb221 lb210 (subcubeFast 0 48) 4 := slice_fast_direct lb311 lb286
set_option maxRecDepth 500000 in
lemma lb317 : btAll (fun o => ∀ p, o = some p → Slice lb221 lb210 p.1 p.2) lb316 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb221 lb210 p.1 p.2) (forall_cons (fun _ h => by cases h; exact lb300) (forall_cons (fun _ h => by cases h; exact lb302) (forall_cons (fun _ h => by cases h; exact lb304) (forall_cons (fun _ h => by cases h; exact lb306) (forall_cons (fun _ h => by cases h; exact lb308) (forall_cons (fun _ h => by cases h; exact lb310) (fun _ h => (List.not_mem_nil h).elim)))))))
lemma lb258 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb210 (0 - 1) xs.toFinset) lb243 := trivial
def lb213 : BT (Option BoundPool) := buildPoolsSubBT 3 lb225 lb221 lb316 lb299 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb263 : checkNodesBT lb225 lb210 lb271 lb213 lb231 lb243 0 lb84 = true := by decide +kernel
def lb245 : BT (List (List Nat)) := buildBucketsBT lb225 lb84
set_option maxRecDepth 500000 in
lemma lb246 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb210 0 xs.toFinset) lb245 :=
  buildBucketsBT_sound (by decide) lb277 lb226 (buildPoolsSubBT_sound lb317) lb232 lb258 lb263
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb264 : checkNodesBT lb225 lb210 lb271 lb213 lb231 lb245 1 lb84 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb247 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb210 1 xs.toFinset) lb245 :=
  buildBucketsBT_sound (by decide) lb277 lb226 (buildPoolsSubBT_sound lb317) lb232 lb246 lb264
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb265 : checkNodesBT lb225 lb210 lb271 lb213 lb231 lb245 2 lb84 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb248 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb210 2 xs.toFinset) lb245 :=
  buildBucketsBT_sound (by decide) lb277 lb226 (buildPoolsSubBT_sound lb317) lb232 lb247 lb265
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb266 : checkNodesBT lb225 lb210 lb271 lb213 lb231 lb245 3 lb84 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb249 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb210 3 xs.toFinset) lb245 :=
  buildBucketsBT_sound (by decide) lb277 lb226 (buildPoolsSubBT_sound lb317) lb232 lb248 lb266
def lb292 : List NodeSpec := [([0,15,2,3,4],[],[]),([16,0,1,2,3],[],[]),([17,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb267 : checkNodesBT lb225 lb210 lb271 lb213 lb231 lb245 4 lb292 = true := by decide +kernel
def lb250 : BT (List (List Nat)) := buildBucketsBT lb225 lb292
set_option maxRecDepth 500000 in
lemma lb251 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb210 4 xs.toFinset) lb250 :=
  buildBucketsBT_sound (by decide) lb277 lb226 (buildPoolsSubBT_sound lb317) lb232 lb249 lb267
def lb293 : List NodeSpec := [([8,0,1,2,3,4],[],[]),([7,5,1,2,3,4],[0,1],[]),([9,0,1,2,3,4],[],[]),([0,1,2,10,3,4],[0,2,3,4],[0,1]),([11,0,1,2,3,4],[],[]),([12,0,1,2,3,4],[2,4],[0,1]),([0,1,2,13,3,4],[4],[0]),([14,0,2,3,4],[],[]),([14,7,0,2,3,4],[2],[]),([6,7,1,2,3,4],[1],[])]
def lb214 : BT (Option BoundPool) := buildPoolsSubBT 3 lb225 lb221 lb316 lb299 [0,1,2,3,4]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb268 : checkNodesBT lb225 lb210 lb271 lb214 lb231 lb250 5 lb293 = true := by decide +kernel
def lb252 : BT (List (List Nat)) := buildBucketsBT lb225 lb293
set_option maxRecDepth 500000 in
lemma lb253 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb210 5 xs.toFinset) lb252 :=
  buildBucketsBT_sound (by decide) lb277 lb226 (buildPoolsSubBT_sound lb317) lb232 lb251 lb268
def lb294 : List NodeSpec := [([5,0,1,2,3,4],[1,5],[0,1]),([6,0,1,2,3,4],[1,0,4],[0,2]),([7,0,1,2,3,4],[1,0,4],[0,2])]
def lb215 : BT (Option BoundPool) := buildPoolsSubBT 3 lb225 lb221 lb316 lb299 [0,1,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb269 : checkNodesBT lb225 lb210 lb271 lb215 lb231 lb252 6 lb294 = true := by decide +kernel
def lb254 : BT (List (List Nat)) := buildBucketsBT lb225 lb294
set_option maxRecDepth 500000 in
lemma lb255 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb210 6 xs.toFinset) lb254 :=
  buildBucketsBT_sound (by decide) lb277 lb226 (buildPoolsSubBT_sound lb317) lb232 lb253 lb269
def lb295 : List NodeSpec := [([0,1,2,3,4],[1,5],[0,2,3,4,1,5])]
def lb216 : BT (Option BoundPool) := buildPoolsSubBT 3 lb225 lb221 lb316 lb299 [1,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb270 : checkNodesBT lb225 lb210 lb271 lb216 lb231 lb254 7 lb295 = true := by decide +kernel
def lb256 : BT (List (List Nat)) := buildBucketsBT lb225 lb295
set_option maxRecDepth 500000 in
lemma lb257 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb210 7 xs.toFinset) lb256 :=
  buildBucketsBT_sound (by decide) lb277 lb226 (buildPoolsSubBT_sound lb317) lb232 lb255 lb270
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb275 : forestRootCheck lb221 lb210 [(VAR 1,26,24),(VAR 2,28,24),(VAR 3,26,18),(VAR 4,26,10),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb274 : bucketContainsBT lb256 lb221 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb285 : Lower lb221 lb210 8 := lower_of_forestBT lb275 lb257 lb274
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q2d : Lower (varsOf 59) 0xeeaaaa0088888800eeaaaa0088888800 8 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (0, 1)]) (roots2 := lb221) (T2 := lb210) _ lb285
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q2 : Lower (varsOf 59) 0xffeeeeeeffaaaa88ffeeeeeeffaaaa88 8 := dualLower (by decide +kernel) (by decide +kernel) q2d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q3d : Lower (varsOf 55) 0xeaeaa0a088888080eaeaa0a088888080 8 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (0, 1)]) (roots2 := lb221) (T2 := lb210) _ lb285
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q3 : Lower (varsOf 55) 0xfefeeeeefafaa8a8fefeeeeefafaa8a8 8 := dualLower (by decide +kernel) (by decide +kernel) q3d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q4d : Lower (varsOf 47) 0xeaa0eaa088808880eaa0eaa088808880 8 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (0, 1)]) (roots2 := lb221) (T2 := lb210) _ lb285
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q4 : Lower (varsOf 47) 0xfeeefeeefaa8faa8feeefeeefaa8faa8 8 := dualLower (by decide +kernel) (by decide +kernel) q4d
def lb330 : Array Decor := buildWires lb233 lb108
def lb323 : Array (Option BoundPool) := buildPools lb330 lb217 lb104 lb92
lemma lb331 : ∀ x ∈ lb330.toList, faithful lb296 lb290 x ∧ x.1 < 2^128 := buildWires_faithful lb234
lemma lb334 : ∀ sw ∈ lb22.toList, swapsValid sw = true ∧ permWord sw lb206 = lb206 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma lb394 : ∀ i (hi : i < lb104.size), Slice lb217 lb206 lb104[i].1 lb104[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb217 lb206 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb324 : ∀ i (hi : i < lb323.size), ∀ c, lb323[i] = some c → ValidPool lb217 lb206 c := buildPools_sound lb394
lemma lb345 : ∀ i (hi : i < lb36.size), ∀ xs ∈ lb36[i], Impossible lb206 (0 - 1) xs.toFinset := by intro i hi; simp [lb36] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb359 : checkNodes lb330 lb206 lb62 lb323 lb22 lb36 0 lb84 = true := by decide +kernel
def lb339 : Array (List (List Nat)) := buildBuckets 1 lb330 lb84
lemma lb340 : ∀ i (hi : i < lb339.size), ∀ xs ∈ lb339[i], Impossible lb206 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb276 lb331 lb324 lb334 lb345 lb359
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb360 : checkNodes lb330 lb206 lb62 lb323 lb22 lb339 1 lb84 = true := by decide +kernel
lemma lb341 : ∀ i (hi : i < lb339.size), ∀ xs ∈ lb339[i], Impossible lb206 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb276 lb331 lb324 lb334 lb340 lb360
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb361 : checkNodes lb330 lb206 lb62 lb323 lb22 lb339 2 lb84 = true := by decide +kernel
lemma lb342 : ∀ i (hi : i < lb339.size), ∀ xs ∈ lb339[i], Impossible lb206 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb276 lb331 lb324 lb334 lb341 lb361
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb362 : checkNodes lb330 lb206 lb62 lb323 lb22 lb339 3 lb85 = true := by decide +kernel
def lb343 : Array (List (List Nat)) := buildBuckets 1 lb330 lb85
lemma lb344 : ∀ i (hi : i < lb343.size), ∀ xs ∈ lb343[i], Impossible lb206 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb276 lb331 lb324 lb334 lb342 lb362
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb371 : forestRootCheck lb217 lb206 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb370 : bucketContains lb343 lb217 = true := by decide +kernel
lemma lb375 : Lower lb217 lb206 4 := lower_of_forest lb371 lb344 lb370
def lb319 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def lb327 : List Nat := varsOf 28
lemma lb377 : carryOK [(2,5),(2,4),(2,3)] lb327 lb319 lb217 lb206 = true := by decide +kernel
lemma lb376 : Lower lb327 lb319 4 := carry_of lb377 lb375
def lb320 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def lb328 : List Nat := varsOf 44
lemma lb379 : carryOK [(2,4),(2,3)] lb328 lb320 lb217 lb206 = true := by decide +kernel
lemma lb378 : Lower lb328 lb320 4 := carry_of lb379 lb375
def lb321 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def lb329 : List Nat := varsOf 52
lemma lb381 : carryOK [(2,3)] lb329 lb321 lb217 lb206 = true := by decide +kernel
lemma lb380 : Lower lb329 lb321 4 := carry_of lb381 lb375
def lb322 : Nat := 0xfff0f000f0000000fff0f000f0000000
def lb384 : List Nat := [28,28,28,44,44,44,52,52,52,56,56,56,28,28,28,44,44,44,52,52,52,56,56,56]
def lb383 : List Nat := [24,20,12,40,36,12,48,36,20,48,40,24,36,40,48,20,24,48,12,24,40,12,20,36]
def lb337 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1ff1ff,0xe491b6),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def lb332 : Array Decor := buildWires lb337 lb109
def lb335 : Array (List (Nat × Nat)) := #[[],[(4,5)],[(2,3)],[(4,5),(2,3)],[(3,4)],[(3,5),(3,4)],[(2,3),(2,4)],[(3,5),(2,3),(2,4)],[(3,5),(2,4)]]
def lb393 : List (Nat × Nat) := [(subcube 0 16,4),(subcube 0 4,4),(subcube 0 8,4),(subcube 0 32,4)]
def lb395 : Array (Nat × Nat) := lb393.toArray
def lb325 : Array (Option BoundPool) := buildPools lb332 lb222 lb395 lb93
lemma lb374 : goodPairs lb322 lb384 lb383 := goodPairs_of (by decide +kernel)
lemma lb338 : ∀ x ∈ lb337, faithful lb384 lb383 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb333 : ∀ x ∈ lb332.toList, faithful lb384 lb383 x ∧ x.1 < 2^128 := buildWires_faithful lb338
lemma lb336 : ∀ sw ∈ lb335.toList, swapsValid sw = true ∧ permWord sw lb322 = lb322 := autos_of (by decide +kernel)
lemma lb386 : sliceDirectCheck 0 16 0 lb222 lb322 lb328 lb320 = true := by decide +kernel
lemma lb385 : Slice lb222 lb322 (subcube 0 16) 4 := slice_direct lb386 lb378
lemma lb388 : sliceDirectCheck 0 4 0 lb222 lb322 lb217 lb206 = true := by decide +kernel
lemma lb387 : Slice lb222 lb322 (subcube 0 4) 4 := slice_direct lb388 lb375
lemma lb390 : sliceDirectCheck 0 8 0 lb222 lb322 lb329 lb321 = true := by decide +kernel
lemma lb389 : Slice lb222 lb322 (subcube 0 8) 4 := slice_direct lb390 lb380
lemma lb392 : sliceDirectCheck 0 32 0 lb222 lb322 lb327 lb319 = true := by decide +kernel
lemma lb391 : Slice lb222 lb322 (subcube 0 32) 4 := slice_direct lb392 lb376
set_option maxRecDepth 200000 in
lemma lb396 : ∀ i (hi : i < lb395.size), Slice lb222 lb322 lb395[i].1 lb395[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb222 lb322 p.1 p.2) (forall_cons lb385 (forall_cons lb387 (forall_cons lb389 (forall_cons lb391 (fun _ h => (List.not_mem_nil h).elim)))))
lemma lb326 : ∀ i (hi : i < lb325.size), ∀ c, lb325[i] = some c → ValidPool lb222 lb322 c := buildPools_sound lb396
lemma lb358 : ∀ i (hi : i < lb36.size), ∀ xs ∈ lb36[i], Impossible lb322 (0 - 1) xs.toFinset := by intro i hi; simp [lb36] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb363 : checkNodes lb332 lb322 lb63 lb325 lb335 lb36 0 lb84 = true := by decide +kernel
def lb346 : Array (List (List Nat)) := buildBuckets 1 lb332 lb84
lemma lb347 : ∀ i (hi : i < lb346.size), ∀ xs ∈ lb346[i], Impossible lb322 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb374 lb333 lb326 lb336 lb358 lb363
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb364 : checkNodes lb332 lb322 lb63 lb325 lb335 lb346 1 lb84 = true := by decide +kernel
lemma lb348 : ∀ i (hi : i < lb346.size), ∀ xs ∈ lb346[i], Impossible lb322 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb374 lb333 lb326 lb336 lb347 lb364
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb365 : checkNodes lb332 lb322 lb63 lb325 lb335 lb346 2 lb84 = true := by decide +kernel
lemma lb349 : ∀ i (hi : i < lb346.size), ∀ xs ∈ lb346[i], Impossible lb322 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb374 lb333 lb326 lb336 lb348 lb365
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb366 : checkNodes lb332 lb322 lb63 lb325 lb335 lb346 3 lb86 = true := by decide +kernel
def lb350 : Array (List (List Nat)) := buildBuckets 1 lb332 lb86
lemma lb351 : ∀ i (hi : i < lb350.size), ∀ xs ∈ lb350[i], Impossible lb322 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb374 lb333 lb326 lb336 lb349 lb366
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb367 : checkNodes lb332 lb322 lb63 lb325 lb335 lb350 4 lb87 = true := by decide +kernel
def lb352 : Array (List (List Nat)) := buildBuckets 2 lb332 lb87
lemma lb353 : ∀ i (hi : i < lb352.size), ∀ xs ∈ lb352[i], Impossible lb322 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb374 lb333 lb326 lb336 lb351 lb367
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb368 : checkNodes lb332 lb322 lb63 lb325 lb335 lb352 5 lb88 = true := by decide +kernel
def lb354 : Array (List (List Nat)) := buildBuckets 1 lb332 lb88
lemma lb355 : ∀ i (hi : i < lb354.size), ∀ xs ∈ lb354[i], Impossible lb322 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb374 lb333 lb326 lb336 lb353 lb368
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb369 : checkNodes lb332 lb322 lb63 lb325 lb335 lb354 6 lb89 = true := by decide +kernel
def lb356 : Array (List (List Nat)) := buildBuckets 1 lb332 lb89
lemma lb357 : ∀ i (hi : i < lb356.size), ∀ xs ∈ lb356[i], Impossible lb322 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb374 lb333 lb326 lb336 lb355 lb369
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb373 : forestRootCheck lb222 lb322 [(VAR 2,28,24),(VAR 3,28,20),(VAR 4,28,12),(VAR 5,44,12)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb372 : bucketContains lb356 lb222 = true := by decide +kernel
lemma lb382 : Lower lb222 lb322 7 := lower_of_forest lb373 lb357 lb372
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q5d : Lower (varsOf 29) 0xfaa0a000faa0a000faa0a000faa0a000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (0, 1)]) (roots2 := lb222) (T2 := lb322) _ lb382
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q5 : Lower (varsOf 29) 0xfffafaa0fffafaa0fffafaa0fffafaa0 7 := dualLower (by decide +kernel) (by decide +kernel) q5d
def lb423 : List Nat := [6,6,18,18,20,20,6,18,20]
def lb422 : List Nat := [4,2,16,2,16,4,16,4,2]
def lb403 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def lb400 : Array Decor := buildWires lb403 lb108
def lb398 : Array (Option BoundPool) := buildPools lb400 lb17 lb104 lb92
lemma lb418 : goodPairs lb6 lb423 lb422 := goodPairs_of (by decide +kernel)
lemma lb404 : ∀ x ∈ lb403, faithful lb423 lb422 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb401 : ∀ x ∈ lb400.toList, faithful lb423 lb422 x ∧ x.1 < 2^128 := buildWires_faithful lb404
lemma lb402 : ∀ sw ∈ lb22.toList, swapsValid sw = true ∧ permWord sw lb6 = lb6 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma lb424 : ∀ i (hi : i < lb104.size), Slice lb17 lb6 lb104[i].1 lb104[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb17 lb6 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb399 : ∀ i (hi : i < lb398.size), ∀ c, lb398[i] = some c → ValidPool lb17 lb6 c := buildPools_sound lb424
lemma lb411 : ∀ i (hi : i < lb36.size), ∀ xs ∈ lb36[i], Impossible lb6 (0 - 1) xs.toFinset := by intro i hi; simp [lb36] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb412 : checkNodes lb400 lb6 lb62 lb398 lb22 lb36 0 lb84 = true := by decide +kernel
def lb405 : Array (List (List Nat)) := buildBuckets 1 lb400 lb84
lemma lb406 : ∀ i (hi : i < lb405.size), ∀ xs ∈ lb405[i], Impossible lb6 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb418 lb401 lb399 lb402 lb411 lb412
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb413 : checkNodes lb400 lb6 lb62 lb398 lb22 lb405 1 lb84 = true := by decide +kernel
lemma lb407 : ∀ i (hi : i < lb405.size), ∀ xs ∈ lb405[i], Impossible lb6 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb418 lb401 lb399 lb402 lb406 lb413
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb414 : checkNodes lb400 lb6 lb62 lb398 lb22 lb405 2 lb84 = true := by decide +kernel
lemma lb408 : ∀ i (hi : i < lb405.size), ∀ xs ∈ lb405[i], Impossible lb6 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb418 lb401 lb399 lb402 lb407 lb414
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb415 : checkNodes lb400 lb6 lb62 lb398 lb22 lb405 3 lb85 = true := by decide +kernel
def lb409 : Array (List (List Nat)) := buildBuckets 1 lb400 lb85
lemma lb410 : ∀ i (hi : i < lb409.size), ∀ xs ∈ lb409[i], Impossible lb6 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb418 lb401 lb399 lb402 lb408 lb415
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb417 : forestRootCheck lb17 lb6 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb416 : bucketContains lb409 lb17 = true := by decide +kernel
lemma lb419 : Lower lb17 lb6 4 := lower_of_forest lb417 lb410 lb416
def lb397 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
lemma lb421 : liftCheck 0 8 lb218 lb397 lb17 lb6 [(VAR 3,14,6)] = true := by decide +kernel
lemma lb420 : Lower lb218 lb397 5 := lift_of lb421 lb419
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q6d : Lower (varsOf 60) 0xfff0f00000000000fff0f00000000000 5 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (3, 4), (2, 3), (1, 2)]) (roots2 := lb218) (T2 := lb397) _ lb420
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q6 : Lower (varsOf 60) 0xfffffffffff0f000fffffffffff0f000 5 := dualLower (by decide +kernel) (by decide +kernel) q6d
def lb452 : List Nat := [5,5,17,17,20,20,5,17,20]
def lb451 : List Nat := [4,1,16,1,16,4,16,4,1]
def lb435 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def lb432 : BT Decor := buildWiresBT 2 lb435 lb108
lemma lb443 : goodPairs lb5 lb452 lb451 := goodPairs_of (by decide +kernel)
lemma lb436 : ∀ x ∈ lb435, faithful lb452 lb451 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb433 : btAll (fun x => faithful lb452 lb451 x ∧ x.1 < 2^128) lb432 := buildWiresBT_faithful lb436
set_option maxRecDepth 500000 in
lemma lb434 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb5 = lb5) lb229 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb453 : btAll (fun o => ∀ p, o = some p → Slice lb16 lb5 p.1 p.2) lb314 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb16 lb5 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb437 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb5 2 xs.toFinset) lb243 := trivial
def lb428 : BT (Option BoundPool) := buildPoolsSubBT 1 lb432 lb16 lb314 lb298 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb440 : checkNodesBT lb432 lb5 lb62 lb428 lb229 lb243 3 lb85 = true := by decide +kernel
def lb438 : BT (List (List Nat)) := buildBucketsBT lb432 lb85
set_option maxRecDepth 500000 in
lemma lb439 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb5 3 xs.toFinset) lb438 :=
  buildBucketsBT_sound (by decide) lb443 lb433 (buildPoolsSubBT_sound lb453) lb434 lb437 lb440
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb442 : forestRootCheck lb16 lb5 [(VAR 0,5,4),(VAR 2,5,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb441 : bucketContainsBT lb438 lb16 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb444 : Lower lb16 lb5 4 := lower_of_forestBT lb442 lb439 lb441
def lb425 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def lb429 : List Nat := varsOf 13
lemma lb446 : carryOK [(3,4)] lb429 lb425 lb16 lb5 = true := by decide +kernel
lemma lb445 : Lower lb429 lb425 4 := carry_of lb446 lb444
def lb426 : Nat := 0xfaa0faa0fa00fa00faa0faa0fa00fa00
def lb430 : List Nat := varsOf 45
lemma lb448 : liftCheck 0 32 lb430 lb426 lb429 lb425 [(VAR 5,37,5)] = true := by decide +kernel
lemma lb447 : Lower lb430 lb426 5 := lift_of lb448 lb445
def lb427 : Nat := 0xeeee8888cccc8888eeee8888cccc8888
def lb431 : List Nat := varsOf 51
lemma lb450 : carryOK [(2,4),(1,2),(1,3)] lb431 lb427 lb430 lb426 = true := by decide +kernel
lemma lb449 : Lower lb431 lb427 5 := carry_of lb450 lb447
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q7d : Lower (varsOf 51) 0xeeeeaaaa88888888eeeeaaaa88888888 5 := by
  apply carry_of (swaps := [(4, 5), (0, 1)]) (roots2 := lb431) (T2 := lb427) _ lb449
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q7 : Lower (varsOf 51) 0xeeeeeeeeaaaa8888eeeeeeeeaaaa8888 5 := dualLower (by decide +kernel) (by decide +kernel) q7d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q8d : Lower (varsOf 39) 0xeaeaeaea88888888eaeaeaea88888888 5 := by
  apply carry_of (swaps := [(4, 5), (3, 4), (2, 3), (0, 1)]) (roots2 := lb431) (T2 := lb427) _ lb449
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q8 : Lower (varsOf 39) 0xeeeeeeeea8a8a8a8eeeeeeeea8a8a8a8 5 := dualLower (by decide +kernel) (by decide +kernel) q8d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q9 : Lower (varsOf 35) 0xeeeeeeee88888888eeeeeeee88888888 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2)]) (roots2 := lb11) (T2 := lb0) _ lb70
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q10 : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000 4 := by
  apply carry_of (swaps := [(3, 4), (2, 3), (1, 2)]) (roots2 := lb11) (T2 := lb0) _ lb70
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q11 : Lower (varsOf 25) 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00 4 := by
  apply carry_of (swaps := [(3, 4), (2, 3), (0, 1)]) (roots2 := lb11) (T2 := lb0) _ lb70
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q12 : Lower (varsOf 21) 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0 4 := by
  apply carry_of (swaps := [(3, 4), (0, 1)]) (roots2 := lb11) (T2 := lb0) _ lb70
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q13 : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0 4 := by
  apply carry_of (swaps := [(0, 1)]) (roots2 := lb11) (T2 := lb0) _ lb70
  decide +kernel
def s0NR : List Nat := varsOf 63
def s0NG : Nat := 0xfffefeeefffafaa8fffefeeefffafaa8
def s0NPos : List Nat := [3,3,3,3,3,5,5,5,5,5,5,7,7,9,9,9,9,11,11,11,12,12,12,12,12,12,13,13,13,13,14,14,14,14,17,17,17,17,17,19,19,20,20,20,20,20,20,20,21,21,21,22,22,22,24,24,24,24,24,24,25,25,25,26,26,26,26,28,28,28,29,33,33,33,33,34,34,37,38,38,41,42,42,44,44,49,50,50,52,52,56,56]
def s0NNeg : List Nat := [0,1,2,6,10,0,1,4,6,8,16,4,6,0,1,8,10,1,8,10,0,1,4,6,8,10,0,1,4,8,2,6,8,10,0,1,8,16,18,1,18,0,1,4,6,8,16,18,1,4,16,2,6,18,0,1,4,8,16,18,1,8,16,2,10,16,18,1,8,16,1,1,32,36,40,2,32,36,6,36,40,10,40,36,40,48,18,48,36,48,40,48]
def s0NMask : Nat := fullMask 92
def s0NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x2127c0700701fc3c0fffff,0xc81081048808224042),(0xcccccccccccccccccccccccccccccccc,0xc6d80780380183c00e181f,0x42480588389142c289111c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x318e078003ffe03fff01fe0,0x108e2000112180090c01988),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xc1f007fffc00003ffffe000,0x417041122002013230d8210),(0xffff0000ffff0000ffff0000ffff0000,0xfe0007ffffffffc00000000,0xae000264c24c16000000400),(0xffffffff00000000ffffffff00000000,0xfffff800000000000000000,0xfbdb7000000000000000000)]
def s0NSteps : List (Nat × Nat × Nat) := [(1,0,1),(2,0,1),(1,7,2),(1,2,3),(1,2,4),(1,8,3),(2,11,4),(2,8,3),(1,8,4),(2,8,4),(1,7,3),(1,7,4),(1,3,4),(1,0,2),(1,0,3),(2,6,5),(1,0,4),(1,19,3),(2,23,4),(2,19,3),(1,19,4),(2,19,4),(1,1,2),(2,6,3),(1,29,4),(2,28,4),(2,6,4),(2,28,3),(1,33,4),(3,2,18),(1,1,3),(1,1,4),(1,6,2),(2,38,3),(1,39,4),(2,39,4),(2,38,4),(2,38,5),(2,6,2),(1,44,3),(1,45,4),(2,45,4),(1,44,4),(1,6,3),(1,6,4),(3,0,9),(1,9,4),(2,9,4),(1,1,9),(1,6,9),(3,2,55),(2,55,4),(2,55,5),(2,6,9),(1,59,2),(3,2,16),(3,2,20),(0,11,4),(1,11,4),(3,2,64),(3,3,64),(1,13,4),(2,13,4),(2,7,2),(1,69,3),(1,70,4),(2,70,4),(1,69,4),(2,7,3),(2,7,4),(3,7,23),(2,7,9),(1,77,2),(3,7,9),(1,7,51),(2,80,4),(1,7,18),(1,53,7),(2,0,2),(1,84,3),(3,3,22),(2,85,4),(1,85,4),(1,84,4),(1,20,4),(2,20,4),(2,0,3),(3,9,22),(2,62,4),(3,2,22),(2,0,4),(1,0,5),(2,0,5),(2,0,9),(1,62,4),(3,3,26),(2,27,3),(1,92,4),(3,2,103),(3,3,10),(0,28,20),(1,31,3),(3,1,19),(3,1,20),(1,19,5),(2,19,5),(1,20,5),(2,20,5),(3,53,19),(3,53,20),(1,4,5),(1,9,5),(3,3,100),(1,3,5),(1,2,5),(1,102,4),(2,92,4),(3,33,19),(0,23,4),(1,108,3),(1,108,4),(1,125,4),(2,125,4),(0,19,36),(3,19,36),(1,130,0),(2,36,4),(1,132,2),(1,132,19),(3,132,19),(0,0,54),(1,136,4),(3,0,54),(1,23,4),(3,2,139),(1,27,3),(3,124,55),(3,1,23),(1,23,5),(2,23,5),(1,24,0),(1,24,1),(2,147,5),(2,24,1),(1,24,5),(2,24,5),(1,25,1),(2,152,5),(2,25,1),(1,25,5),(2,25,5),(1,84,1),(2,157,5),(1,99,4),(2,84,4),(1,84,5),(2,84,5),(1,35,0),(0,0,28),(1,164,3),(1,165,4),(2,165,4),(3,2,166),(1,164,4),(1,164,5),(1,35,164),(3,0,28),(2,54,4),(1,33,0),(1,174,4),(2,174,4),(3,0,34),(1,28,4),(1,24,9),(2,24,9),(1,99,1),(2,181,5),(1,99,2),(1,99,5),(2,99,5),(0,0,9),(1,186,1),(1,186,4),(1,186,5),(1,136,5),(3,1,9),(1,191,5),(2,9,5)]
def s0NW : BT Decor := buildWiresBT 8 s0NBase s0NSteps
def s0NAutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(2,3)],[(2,3),(3,4)],[(2,4),(3,4)],[(2,4)],[(1,5)],[(1,5),(3,4)],[(1,5),(2,3)],[(1,5),(2,3),(3,4)],[(1,5),(2,4),(3,4)],[(1,5),(2,4)]]
def s0NAutos : BT (List (Nat × Nat)) := btOfList 4 s0NAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NPairs : goodPairs s0NG s0NPos s0NNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBaseOk : ∀ x ∈ s0NBase, faithful s0NPos s0NNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NWOk : btAll (fun x => faithful s0NPos s0NNeg x ∧ x.1 < 2^128) s0NW := buildWiresBT_faithful s0NBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw s0NG = s0NG) s0NAutos := btAll_ofList (autos_of (by decide +kernel))
def s0NSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,8),some (subcubeFast 4 0,8),some (subcubeFast 8 0,8),some (subcubeFast 16 0,8),some (subcubeFast 34 0,7),some (subcubeFast 1 2,5),some (subcubeFast 12 0,5),some (subcubeFast 24 0,5),some (subcubeFast 28 0,4),some (subcubeFast 3 32,4),some (subcubeFast 33 2,4),some (subcubeFast 38 0,4),some (subcubeFast 42 0,4),some (subcubeFast 50 0,4)]
def s0NSlices : BT (Option (Nat × Nat)) := btOfList 4 s0NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice0 : Slice s0NR s0NG (subcubeFast 2 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafaaafffafaa0fffafaaafffafaa0) (by decide +kernel) q1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice1 : Slice s0NR s0NG (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeeeeeffaaaa88ffeeeeeeffaaaa88) (by decide +kernel) q2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice2 : Slice s0NR s0NG (subcubeFast 8 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeeeeefafaa8a8fefeeeeefafaa8a8) (by decide +kernel) q3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice3 : Slice s0NR s0NG (subcubeFast 16 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfeeefeeefaa8faa8feeefeeefaa8faa8) (by decide +kernel) q4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice4 : Slice s0NR s0NG (subcubeFast 34 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 29) (qGoal := 0xfffafaa0fffafaa0fffafaa0fffafaa0) (by decide +kernel) q5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice5 : Slice s0NR s0NG (subcubeFast 1 2) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 60) (qGoal := 0xfffffffffff0f000fffffffffff0f000) (by decide +kernel) q6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice6 : Slice s0NR s0NG (subcubeFast 12 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 51) (qGoal := 0xeeeeeeeeaaaa8888eeeeeeeeaaaa8888) (by decide +kernel) q7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice7 : Slice s0NR s0NG (subcubeFast 24 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 39) (qGoal := 0xeeeeeeeea8a8a8a8eeeeeeeea8a8a8a8) (by decide +kernel) q8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice8 : Slice s0NR s0NG (subcubeFast 28 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) q9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice9 : Slice s0NR s0NG (subcubeFast 3 32) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) q10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice10 : Slice s0NR s0NG (subcubeFast 33 2) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) q10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice11 : Slice s0NR s0NG (subcubeFast 38 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 25) (qGoal := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00) (by decide +kernel) q11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice12 : Slice s0NR s0NG (subcubeFast 42 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 21) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) q12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice13 : Slice s0NR s0NG (subcubeFast 50 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 13) (qGoal := 0xfaa0faa0faa0faa0faa0faa0faa0faa0) (by decide +kernel) q13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s0NR s0NG p.1 p.2) s0NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s0NR s0NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s0NSlice0) (forall_cons (fun _ h => by cases h; exact s0NSlice1) (forall_cons (fun _ h => by cases h; exact s0NSlice2) (forall_cons (fun _ h => by cases h; exact s0NSlice3) (forall_cons (fun _ h => by cases h; exact s0NSlice4) (forall_cons (fun _ h => by cases h; exact s0NSlice5) (forall_cons (fun _ h => by cases h; exact s0NSlice6) (forall_cons (fun _ h => by cases h; exact s0NSlice7) (forall_cons (fun _ h => by cases h; exact s0NSlice8) (forall_cons (fun _ h => by cases h; exact s0NSlice9) (forall_cons (fun _ h => by cases h; exact s0NSlice10) (forall_cons (fun _ h => by cases h; exact s0NSlice11) (forall_cons (fun _ h => by cases h; exact s0NSlice12) (forall_cons (fun _ h => by cases h; exact s0NSlice13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
def s0NEmpty : BT (List (List Nat)) := BT.empty
lemma s0NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG (5 - 1) xs.toFinset) s0NEmpty := trivial
def s0NBlock5_0Specs : List PoolSpec := [(11,[]),(12,[]),(8,[])]
def s0NBlock5_0Pools : BT (Option BoundPool) := buildPoolsBT 2 s0NW s0NR s0NSlices s0NBlock5_0Specs
def s0NBlock5_0 : List NodeSpec := [([148,24,0,1,2,3],[],[]),([158,35,0,1,3,4],[],[]),([21,24,0,1,2,3],[],[]),([21,0,1,9,10,18],[0,1],[]),([21,1,19,20,9,4],[0],[]),([43,24,0,1,2,3],[],[]),([43,0,1,2,3,124],[],[]),([43,1,19,20,9,4],[0],[]),([58,24,0,1,2,3],[],[]),([58,0,1,2,3,124],[],[]),([102,94,0,1,9,5],[2],[]),([102,94,0,1,23,5],[2],[]),([102,0,1,9,26,5],[2],[]),([94,1,19,20,18,5],[],[]),([81,0,1,2,3,5],[],[]),([96,53,1,19,20,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock5_0Pools s0NAutos s0NEmpty 5 s0NBlock5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_0Mem : ∀ ns ∈ s0NBlock5_0, Impossible s0NG 5 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NEmptyOk s0NBlock5_0Ok
def s0NBlock5_1Specs : List PoolSpec := [(4,[(1,7,2),(1,8,3),(2,11,4)]),(8,[])]
def s0NBlock5_1Pools : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NBlock5_1Specs
def s0NBlock5_1 : List NodeSpec := [([27,91,0,1,9,5],[],[]),([27,91,1,19,9,5],[],[]),([27,53,1,19,20,5],[],[]),([27,0,1,9,121,5],[],[]),([27,1,20,9,22,5],[],[]),([27,1,20,9,26,5],[],[]),([31,91,1,19,3,5],[],[]),([87,1,19,3,22,5],[],[]),([91,62,1,19,18,5],[],[]),([91,1,19,3,100,5],[],[]),([53,1,19,20,37,5],[],[]),([12,0,6,2,3,5],[0],[]),([142,0,1,2,3,5],[],[]),([93,1,19,20,4,5],[1],[]),([93,1,20,4,26,5],[1],[]),([92,105,1,19,103,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_1Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock5_1Pools s0NAutos s0NEmpty 5 s0NBlock5_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_1Mem : ∀ ns ∈ s0NBlock5_1, Impossible s0NG 5 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NEmptyOk s0NBlock5_1Ok
def s0NBlock5_2Specs : List PoolSpec := [(6,[])]
def s0NBlock5_2Pools : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NBlock5_2Specs
def s0NBlock5_2 : List NodeSpec := [([13,0,1,2,63,5],[],[]),([39,0,1,2,124,5],[],[]),([86,1,19,85,4,5],[],[]),([35,0,1,3,4,170],[],[]),([35,0,1,165,4,5],[],[]),([65,0,1,3,4,5],[],[]),([168,0,1,165,4,5],[],[]),([0,171,1,3,4,5],[],[]),([0,1,9,14,18,5],[0],[]),([1,2,3,23,137,5],[],[]),([1,114,19,20,4,5],[],[]),([1,19,3,9,137,5],[],[]),([1,19,107,20,4,5],[],[]),([1,19,85,22,18,5],[],[]),([1,19,20,22,52,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_2Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock5_2Pools s0NAutos s0NEmpty 5 s0NBlock5_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_2Mem : ∀ ns ∈ s0NBlock5_2, Impossible s0NG 5 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NEmptyOk s0NBlock5_2Ok
def s0NNodes5 : List NodeSpec := s0NBlock5_0 ++ s0NBlock5_1 ++ s0NBlock5_2
def s0NBucket5 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 5 xs.toFinset) s0NBucket5 := buildBucketsBT_of_mem (forall_append (forall_append s0NBlock5_0Mem s0NBlock5_1Mem) s0NBlock5_2Mem)
def s0NBlock6_0Specs : List PoolSpec := [(11,[]),(12,[]),(13,[]),(2,[(1,0,1),(1,6,2),(2,38,5)]),(2,[(1,0,2),(1,1,19),(2,38,5)]),(2,[(2,0,2),(1,84,1),(2,157,5)]),(1,[(2,0,9),(1,99,1),(2,181,5)])]
def s0NBlock6_0Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_0Specs
def s0NBlock6_0 : List NodeSpec := [([182,0,1,2,3,9,4],[6],[]),([153,25,0,1,2,3,4],[],[]),([158,0,1,2,3,4,18],[0,5],[0]),([21,53,0,1,2,3,4],[],[]),([21,25,0,1,2,3,4],[],[]),([21,51,0,1,2,3,4],[],[]),([21,0,1,2,3,23,4],[2],[0]),([21,0,1,2,3,4,52],[],[]),([21,0,1,19,3,9,4],[1],[0]),([21,0,1,3,9,4,10],[1,2],[0]),([21,1,2,19,3,20,4],[0],[0]),([43,25,0,1,2,3,4],[],[]),([43,0,1,2,3,23,4],[],[0]),([43,0,1,2,3,4,18],[3],[]),([43,0,1,19,3,9,4],[4],[0]),([43,1,2,19,3,20,4],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_0Pools s0NAutos s0NBucket5 6 s0NBlock6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_0Mem : ∀ ns ∈ s0NBlock6_0, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_0Ok
def s0NBlock6_1Specs : List PoolSpec := [(5,[]),(6,[]),(2,[(1,0,1),(1,6,2),(2,39,4)]),(1,[(1,0,1),(1,6,9),(2,55,5)]),(8,[]),(3,[(2,0,1),(1,7,2),(2,8,3)])]
def s0NBlock6_1Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_1Specs
def s0NBlock6_1 : List NodeSpec := [([58,0,1,2,3,9,4],[3],[]),([58,0,1,2,3,23,4],[],[0]),([180,24,0,1,2,3,5],[4],[]),([68,0,1,2,3,4,5],[5],[]),([102,27,0,1,9,4,5],[1],[0]),([102,27,1,2,20,4,5],[],[2,5]),([102,0,1,2,3,121,5],[4],[]),([102,0,1,19,9,4,5],[4],[0,3]),([41,0,1,2,3,4,5],[2],[]),([94,24,0,1,19,3,5],[4],[]),([94,24,0,1,3,9,5],[4],[0]),([94,24,0,1,3,23,5],[4],[0]),([94,0,1,19,3,4,5],[4],[1]),([94,1,19,3,20,4,5],[0],[0,3]),([149,24,0,1,2,3,5],[],[]),([96,62,1,19,3,4,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_1Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_1Pools s0NAutos s0NBucket5 6 s0NBlock6_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_1Mem : ∀ ns ∈ s0NBlock6_1, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_1Ok
def s0NBlock6_2Specs : List PoolSpec := [(5,[]),(6,[]),(7,[]),(8,[]),(2,[(2,0,1),(1,7,2),(2,8,4)]),(1,[])]
def s0NBlock6_2Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_2Specs
def s0NBlock6_2 : List NodeSpec := [([96,1,19,20,9,4,5],[0,2],[0]),([176,0,1,2,3,4,5],[],[]),([15,0,1,3,9,4,5],[4],[]),([27,91,0,1,2,3,5],[3],[0]),([27,91,1,2,19,3,5],[3],[0]),([27,132,0,1,2,3,5],[0],[2]),([27,53,0,1,19,3,5],[3],[0]),([27,92,1,2,3,103,5],[],[4]),([27,92,1,2,3,26,5],[3],[]),([27,92,1,19,3,10,5],[1],[]),([27,25,0,1,9,4,5],[1],[0,3]),([27,0,1,2,3,103,5],[5],[4]),([27,0,1,2,3,121,5],[5],[0,2]),([27,0,1,3,9,26,5],[3],[0]),([27,0,1,20,9,4,5],[3],[0]),([27,1,2,19,3,103,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_2Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_2Pools s0NAutos s0NBucket5 6 s0NBlock6_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_2Mem : ∀ ns ∈ s0NBlock6_2, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_2Ok
def s0NBlock6_3Specs : List PoolSpec := [(5,[]),(7,[]),(8,[]),(1,[])]
def s0NBlock6_3Pools : BT (Option BoundPool) := buildPoolsBT 2 s0NW s0NR s0NSlices s0NBlock6_3Specs
def s0NBlock6_3 : List NodeSpec := [([27,1,2,3,20,26,5],[2],[0,5]),([27,1,19,3,20,10,5],[3],[2]),([27,1,19,20,9,4,5],[0,2],[0]),([27,1,20,9,4,5],[2],[0,2]),([31,29,0,2,3,4,5],[],[]),([31,1,19,3,20,4,5],[0],[0]),([72,0,1,2,3,4,5],[],[]),([87,0,1,2,3,88,5],[2],[]),([87,0,1,2,85,18,5],[1],[]),([87,0,1,19,3,4,5],[],[0]),([47,0,1,2,3,4,5],[],[]),([128,0,1,2,3,4,5],[],[]),([167,0,1,2,3,4,5],[0],[]),([167,0,1,2,165,4,5],[],[]),([91,84,1,19,3,4,5],[],[1]),([91,62,1,19,3,4,5],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_3Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_3Pools s0NAutos s0NBucket5 6 s0NBlock6_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_3Mem : ∀ ns ∈ s0NBlock6_3, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_3Ok
def s0NBlock6_4Specs : List PoolSpec := [(4,[(1,7,2),(1,8,3),(2,11,4)]),(9,[]),(5,[]),(7,[]),(8,[]),(1,[(2,0,1),(1,7,9),(2,11,4)])]
def s0NBlock6_4Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_4Specs
def s0NBlock6_4 : List NodeSpec := [([91,1,19,28,3,4,5],[],[0]),([53,0,1,8,3,4,5],[],[]),([53,0,1,19,20,4,5],[2],[0]),([53,1,19,20,4,5],[1,2,4],[0,2,6]),([12,7,0,1,2,3,5],[],[0]),([12,0,1,2,8,3,5],[],[]),([12,0,1,2,3,9,5],[5],[]),([12,0,1,2,3,11,5],[3],[]),([12,0,1,2,3,4,5],[],[]),([12,0,1,2,3,5],[0],[0]),([24,99,0,1,2,3,5],[],[]),([24,25,0,1,2,23,5],[4],[]),([24,84,0,1,19,3,5],[4],[]),([24,62,0,1,19,3,5],[4],[]),([24,62,0,1,3,9,5],[4],[]),([24,7,0,1,2,3,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_4Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_4Pools s0NAutos s0NBucket5 6 s0NBlock6_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_4Mem : ∀ ns ∈ s0NBlock6_4, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_4Ok
def s0NBlock6_5Specs : List PoolSpec := [(13,[]),(4,[(1,0,2),(1,19,3),(2,23,4)]),(6,[]),(7,[]),(1,[(1,0,1),(1,6,9),(2,55,4)]),(8,[]),(1,[])]
def s0NBlock6_5Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_5Specs
def s0NBlock6_5 : List NodeSpec := [([24,108,0,1,2,3,5],[],[]),([24,143,0,1,2,3,5],[],[]),([24,0,146,1,2,3,5],[],[]),([24,0,1,147,2,3,5],[1],[0]),([24,0,1,6,2,3,5],[1],[0]),([24,0,1,2,38,3,5],[1],[0]),([24,0,1,2,3,23,5],[3],[]),([24,0,1,2,3,54,5],[],[]),([24,0,1,2,3,55,5],[0,1],[0]),([24,0,1,2,3,139,5],[6],[]),([24,0,1,19,28,3,5],[1],[]),([57,0,1,2,3,9,5],[4],[]),([57,0,1,2,3,23,5],[5],[]),([99,62,1,19,20,4,5],[2],[]),([99,1,19,20,9,4,5],[2],[]),([93,0,1,3,4,26,5],[5],[0,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_5Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_5Pools s0NAutos s0NBucket5 6 s0NBlock6_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_5Mem : ∀ ns ∈ s0NBlock6_5, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_5Ok
def s0NBlock6_6Specs : List PoolSpec := [(4,[(1,7,2),(2,8,3)]),(4,[]),(5,[]),(6,[]),(8,[]),(2,[(1,0,2),(3,2,20)])]
def s0NBlock6_6Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_6Specs
def s0NBlock6_6 : List NodeSpec := [([92,105,0,1,19,4,5],[4],[1]),([92,105,1,19,4,5],[4],[0]),([92,101,0,1,2,4,5],[],[]),([92,101,1,2,19,4,5],[],[]),([92,101,1,2,4,26,5],[4],[]),([92,104,1,19,3,4,5],[2],[4]),([92,1,19,3,103,10,5],[2],[0,4]),([13,0,1,2,20,4,5],[1],[]),([13,0,1,2,11,4,5],[1],[0]),([13,0,1,8,9,4,5],[3],[]),([13,0,6,2,3,4,5],[0],[]),([25,84,1,19,20,4,5],[2],[]),([25,62,0,1,20,4,5],[],[]),([25,62,0,1,9,4,5],[3],[]),([25,62,0,1,23,4,5],[],[]),([25,62,1,19,20,4,5],[5],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_6Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_6Pools s0NAutos s0NBucket5 6 s0NBlock6_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_6Mem : ∀ ns ∈ s0NBlock6_6, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_6Ok
def s0NBlock6_7Specs : List PoolSpec := [(9,[]),(4,[]),(11,[]),(5,[]),(6,[]),(7,[]),(8,[]),(1,[])]
def s0NBlock6_7Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_7Specs
def s0NBlock6_7 : List NodeSpec := [([25,0,1,2,19,124,5],[5],[]),([25,0,1,2,125,4,5],[7],[]),([25,0,1,2,124,23,5],[5],[]),([25,0,1,2,124,5],[6],[]),([25,0,1,19,85,4,5],[3],[]),([25,0,1,9,4,26,5],[6],[0]),([25,1,19,28,20,4,5],[3],[]),([39,0,1,2,23,4,5],[7],[0]),([39,0,1,19,9,4,5],[2,4],[]),([39,1,2,19,20,4,5],[0],[]),([118,0,1,2,85,4,5],[7],[]),([105,0,1,19,36,4,5],[],[1]),([101,0,1,2,19,4,5],[],[]),([101,0,1,2,20,4,5],[7],[]),([101,0,1,2,36,4,5],[1],[]),([101,0,1,2,23,4,5],[6],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_7Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_7Pools s0NAutos s0NBucket5 6 s0NBlock6_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_7Mem : ∀ ns ∈ s0NBlock6_7, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_7Ok
def s0NBlock6_8Specs : List PoolSpec := [(4,[]),(5,[]),(6,[]),(8,[])]
def s0NBlock6_8Pools : BT (Option BoundPool) := buildPoolsBT 2 s0NW s0NR s0NSlices s0NBlock6_8Specs
def s0NBlock6_8 : List NodeSpec := [([101,0,1,19,9,4,5],[3],[]),([101,0,1,9,4,26,5],[3],[0]),([101,1,2,19,20,4,5],[3],[0]),([101,1,2,20,4,26,5],[3],[0,5]),([69,35,0,1,3,4,5],[],[0]),([84,35,0,1,85,4,5],[3],[3]),([84,0,163,1,3,4,5],[3],[]),([84,1,19,3,4,90,5],[2],[]),([84,1,19,20,4,18,5],[1],[1]),([44,35,0,1,3,4,5],[1],[]),([61,0,1,8,3,4,5],[0],[]),([61,0,1,3,9,4,5],[2],[]),([62,0,1,8,3,4,5],[0],[]),([62,0,1,19,3,124,5],[3],[]),([62,0,1,19,4,18,5],[3],[4]),([62,1,19,3,4,22,5],[2],[1,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_8Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_8Pools s0NAutos s0NBucket5 6 s0NBlock6_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_8Mem : ∀ ns ∈ s0NBlock6_8, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_8Ok
def s0NBlock6_9Specs : List PoolSpec := [(11,[]),(5,[]),(12,[]),(4,[(1,3,4),(3,2,18)]),(6,[]),(8,[])]
def s0NBlock6_9Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_9Specs
def s0NBlock6_9 : List NodeSpec := [([62,1,19,3,4,90,5],[4],[3]),([62,1,19,20,4,18,5],[1],[0]),([56,0,1,3,9,4,5],[4],[]),([104,0,1,19,3,4,5],[1],[4]),([104,1,19,3,4,103,5],[1],[]),([35,164,0,1,3,4,5],[4],[0,1]),([35,0,1,157,3,4,5],[],[0]),([35,0,6,28,3,4,5],[3,4],[]),([140,0,1,3,85,4,5],[],[]),([140,0,1,3,4,88,5],[],[]),([140,0,1,3,4,5],[],[]),([7,0,1,9,10,18,5],[0,2,5],[0,1,2]),([7,1,19,20,9,4,5],[0,1],[]),([83,0,1,2,3,4,5],[],[3]),([108,1,19,20,9,4,5],[0,1],[]),([143,0,1,2,3,124,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_9Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_9Pools s0NAutos s0NBucket5 6 s0NBlock6_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_9Mem : ∀ ns ∈ s0NBlock6_9, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_9Ok
def s0NBlock6_10Specs : List PoolSpec := [(11,[]),(5,[]),(12,[]),(13,[]),(7,[]),(4,[(1,2,3),(1,2,4),(1,3,4)]),(8,[]),(1,[]),(1,[(1,1,9),(0,0,54),(1,136,4)]),(1,[(1,1,9),(0,0,54),(1,136,5)])]
def s0NBlock6_10Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_10Specs
def s0NBlock6_10 : List NodeSpec := [([138,1,2,3,23,4,5],[7],[]),([138,1,19,3,9,4,5],[0],[]),([177,0,1,2,3,4,5],[],[]),([80,0,1,2,3,4,5],[6],[0]),([136,1,2,3,23,4,5],[],[0]),([136,1,19,3,9,4,5],[0],[0]),([0,163,1,28,3,4,5],[],[]),([0,1,76,2,3,4,5],[],[]),([0,1,6,9,10,18,5],[0,2,5],[0]),([0,1,2,135,3,4,5],[4],[]),([0,1,2,134,3,4,5],[1],[]),([0,1,2,3,9,4,190],[9],[]),([0,1,2,3,9,137,5],[1,8],[0,2]),([0,1,2,3,63,11,5],[],[0,2,3]),([0,1,2,3,11,4,5],[4],[3]),([0,1,2,3,124,55,5],[3],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_10Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_10Pools s0NAutos s0NBucket5 6 s0NBlock6_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_10Mem : ∀ ns ∈ s0NBlock6_10, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_10Ok
def s0NBlock6_11Specs : List PoolSpec := [(11,[]),(5,[]),(7,[]),(8,[]),(3,[(2,0,1),(1,7,2),(2,8,3)]),(1,[]),(2,[(1,1,2),(0,0,28),(1,165,4)]),(3,[(1,1,2),(0,0,28),(1,164,3)]),(2,[(1,1,2),(0,0,28),(1,164,5)])]
def s0NBlock6_11Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_11Specs
def s0NBlock6_11 : List NodeSpec := [([0,1,2,3,4,67,5],[4],[]),([0,1,2,3,4,40,5],[1],[]),([0,1,2,3,4,18,170],[0,8],[0]),([0,1,2,3,4,71,5],[],[0]),([0,1,2,3,4,46,5],[1],[]),([0,1,2,3,4,127,5],[5],[0]),([0,1,2,3,4,166,5],[5,6],[]),([0,1,2,3,4,64,5],[],[0,2,3]),([0,1,2,70,4,18,5],[2],[]),([0,1,2,85,89,18,5],[1,3],[]),([0,1,2,125,4,18,5],[2],[]),([0,1,2,165,4,18,5],[0,2],[0]),([0,1,2,165,4,166,5],[0,7],[0]),([0,1,2,23,4,121,5],[3],[]),([0,1,2,23,26,18,5],[3],[]),([0,1,133,19,3,4,5],[1],[2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_11Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_11Pools s0NAutos s0NBucket5 6 s0NBlock6_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_11Mem : ∀ ns ∈ s0NBlock6_11, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_11Ok
def s0NBlock6_12Specs : List PoolSpec := [(11,[]),(5,[]),(6,[]),(7,[]),(8,[]),(1,[(2,0,1),(1,0,3)])]
def s0NBlock6_12Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_12Specs
def s0NBlock6_12 : List NodeSpec := [([0,1,78,3,9,4,5],[2],[]),([0,1,183,85,9,4,5],[2],[]),([0,1,60,3,9,4,5],[2],[]),([0,1,8,3,4,52,5],[1],[]),([0,1,8,16,9,4,5],[0,1],[]),([0,1,8,20,9,4,5],[1,5],[]),([0,1,8,9,4,18,5],[3],[0]),([0,1,123,19,3,4,5],[],[]),([0,1,114,19,3,4,5],[],[0]),([0,1,19,3,4,34,5],[],[1]),([0,1,19,3,4,100,5],[],[]),([0,1,19,3,4,88,5],[2],[]),([0,1,19,3,103,10,5],[1,4],[4]),([0,1,19,85,9,4,5],[2],[]),([0,1,19,85,4,18,5],[1,4],[0]),([0,1,19,20,4,52,5],[1,4],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_12Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_12Pools s0NAutos s0NBucket5 6 s0NBlock6_12 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_12Mem : ∀ ns ∈ s0NBlock6_12, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_12Ok
def s0NBlock6_13Specs : List PoolSpec := [(4,[(1,7,2),(1,2,3)]),(4,[(1,7,2),(1,8,3)]),(9,[]),(11,[]),(5,[]),(4,[(1,0,2),(1,0,3),(1,2,3)]),(6,[]),(8,[]),(1,[])]
def s0NBlock6_13Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_13Specs
def s0NBlock6_13 : List NodeSpec := [([0,1,19,20,10,18,5],[7],[]),([0,1,19,9,4,121,5],[7],[0]),([0,1,19,9,26,18,5],[7],[0]),([0,1,3,9,4,14,5],[6],[0]),([0,1,20,9,4,26,5],[6],[]),([0,1,9,26,18,5],[7],[0,5]),([0,6,2,3,11,4,5],[1],[0]),([0,6,2,3,4,34,5],[3],[]),([0,6,8,3,9,4,5],[0],[]),([0,2,28,3,4,30,5],[],[]),([131,1,2,19,3,4,5],[8],[]),([1,6,19,20,9,4,5],[2,3,4,5],[0]),([1,19,106,3,20,4,5],[4],[]),([1,19,28,3,4,90,5],[8],[]),([1,19,28,20,4,18,5],[4],[]),([1,19,38,20,9,4,5],[2,3,5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_13Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_13Pools s0NAutos s0NBucket5 6 s0NBlock6_13 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_13Mem : ∀ ns ∈ s0NBlock6_13, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_13Ok
def s0NBlock6_14Specs : List PoolSpec := [(9,[]),(11,[]),(5,[]),(12,[]),(6,[]),(7,[]),(8,[])]
def s0NBlock6_14Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_14Specs
def s0NBlock6_14 : List NodeSpec := [([1,19,3,85,4,22,5],[],[0]),([1,19,3,20,4,100,5],[],[0,1]),([1,19,3,20,10,90,5],[4],[3]),([1,19,3,103,10,5],[0,2,6],[]),([1,19,20,9,54,4,5],[1,3,4],[]),([1,19,20,9,4,22,5],[6],[0,2]),([1,19,20,9,4,37,5],[2,5],[0]),([1,19,20,9,4,26,5],[6],[0]),([1,19,20,4,52,5],[0,2,6],[]),([1,19,20,10,18,5],[6],[0,2]),([1,20,9,4,26,5],[6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_14Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_14Pools s0NAutos s0NBucket5 6 s0NBlock6_14 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_14Mem : ∀ ns ∈ s0NBlock6_14, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_14Ok
def s0NNodes6 : List NodeSpec := s0NBlock6_0 ++ s0NBlock6_1 ++ s0NBlock6_2 ++ s0NBlock6_3 ++ s0NBlock6_4 ++ s0NBlock6_5 ++ s0NBlock6_6 ++ s0NBlock6_7 ++ s0NBlock6_8 ++ s0NBlock6_9 ++ s0NBlock6_10 ++ s0NBlock6_11 ++ s0NBlock6_12 ++ s0NBlock6_13 ++ s0NBlock6_14
def s0NBucket6 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 6 xs.toFinset) s0NBucket6 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append s0NBlock6_0Mem s0NBlock6_1Mem) s0NBlock6_2Mem) s0NBlock6_3Mem) s0NBlock6_4Mem) s0NBlock6_5Mem) s0NBlock6_6Mem) s0NBlock6_7Mem) s0NBlock6_8Mem) s0NBlock6_9Mem) s0NBlock6_10Mem) s0NBlock6_11Mem) s0NBlock6_12Mem) s0NBlock6_13Mem) s0NBlock6_14Mem)
def s0NBlock7_0Specs : List PoolSpec := [(9,[]),(4,[]),(11,[]),(5,[]),(12,[]),(13,[]),(1,[(1,0,1),(2,6,5)]),(10,[]),(2,[(1,0,1),(1,6,2),(2,38,5)]),(1,[(1,0,1),(2,38,5)]),(3,[(1,0,1),(1,6,2),(2,38,5)]),(2,[(1,0,1),(2,6,5)]),(8,[]),(2,[(1,0,2),(2,19,4)]),(2,[(1,0,2),(1,1,19),(2,38,5)]),(1,[(1,1,19),(2,38,5)]),(3,[(1,0,2),(1,1,19),(2,38,5)]),(3,[(1,0,2),(2,19,3)]),(2,[(2,0,2),(1,84,1),(2,157,5)]),(1,[(1,84,1),(2,157,5)]),(3,[(2,0,2),(1,84,1),(2,157,5)])]
def s0NBlock7_0Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_0Specs
def s0NBlock7_0 : List NodeSpec := [([158,0,1,2,3,4],[0,18,19,20],[0]),([21,0,1,6,2,3,9,4],[0,2,3,6],[]),([21,0,1,2,19,3,4],[0,4,5,6],[0,1]),([21,0,1,2,3,9,4],[0,5,6,7,11],[0,2]),([43,0,1,2,19,3,4],[0,14,15,16],[0,1]),([43,0,1,2,3,4],[0,8,9,10],[0]),([122,1,2,19,3,4,5],[0,12],[]),([102,25,0,1,2,3,4,5],[17],[0,1,4]),([102,0,1,2,19,3,4,5],[3,12,17],[0,1,2,3,4,5]),([102,0,1,2,3,4,5],[0,1,3,12,17],[0,1,2,3]),([96,1,2,19,3,20,4,5],[3,12],[0,2]),([96,1,2,3,85,4,5],[0,12],[]),([27,92,0,1,2,3,4,5],[12],[0,2,3]),([27,92,1,2,19,3,4,5],[3,12],[0]),([27,92,1,2,3,4,5],[12],[0,2]),([27,25,0,1,2,3,4,5],[12,13],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_0Pools s0NAutos s0NBucket6 7 s0NBlock7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_0Mem : ∀ ns ∈ s0NBlock7_0, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_0Ok
def s0NBlock7_1Specs : List PoolSpec := [(9,[]),(4,[]),(5,[]),(12,[]),(10,[]),(7,[]),(4,[(1,2,3),(2,9,4)]),(8,[]),(2,[(1,0,2),(2,19,4)]),(2,[(1,0,2),(2,23,4)])]
def s0NBlock7_1Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock7_1Specs
def s0NBlock7_1 : List NodeSpec := [([27,0,1,2,3,20,4,5],[7,8],[0,2,3]),([27,0,1,2,3,36,4,5],[2,3,7],[0,2]),([27,0,1,2,3,23,4,5],[7,8],[1,3,4]),([27,0,1,19,3,9,4,5],[2,7,8],[0,3]),([27,0,1,3,9,4,5],[7,8],[0,3]),([27,1,2,19,3,20,4,5],[2,7,8],[0,2]),([27,1,2,3,20,4,5],[7,8],[0,2,8]),([31,0,2,3,36,4,5],[4,7],[]),([87,84,0,1,2,3,4,5],[7],[0,1,3]),([87,0,1,2,3,85,4,5],[2,7],[0,3]),([87,0,1,2,3,4,5],[0,1,2,7],[0,3]),([132,0,1,2,19,3,4,5],[2,3,7],[0,2]),([53,7,0,1,2,3,4,5],[2,7],[0,2,3]),([53,0,1,6,2,3,4,5],[0,2,5,6],[0,3]),([53,0,1,19,3,4,5],[0,2,7],[0,1,7]),([24,0,1,2,19,3,23,5],[7,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_1Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_1Pools s0NAutos s0NBucket6 7 s0NBlock7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_1Mem : ∀ ns ∈ s0NBlock7_1, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_1Ok
def s0NBlock7_2Specs : List PoolSpec := [(9,[]),(5,[]),(4,[(1,0,2),(1,19,3),(2,23,4)]),(4,[(1,0,2),(2,19,3)]),(6,[]),(10,[]),(1,[(1,0,1),(2,6,9)]),(8,[]),(1,[(2,0,1),(2,7,9)]),(1,[(1,19,3),(2,23,4)]),(2,[(1,0,2),(2,23,4)]),(1,[(1,0,9),(2,0,9)]),(1,[(1,0,9),(2,23,4)]),(4,[(1,2,3),(1,0,9),(2,23,4)]),(2,[(1,0,9),(2,23,4)])]
def s0NBlock7_2Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock7_2Specs
def s0NBlock7_2 : List NodeSpec := [([24,0,1,2,19,3,4,5],[7,9,10],[0,1]),([24,0,1,2,19,3,5],[2,7,9,10],[0,1,6]),([24,0,1,2,3,9,23,5],[7,12],[0,2]),([24,0,1,2,3,9,5],[7,12,13,14],[0,2,3,6]),([24,0,1,2,3,23,4,5],[7,9,10],[0,1,4]),([24,0,1,2,3,23,5],[2,7,9,10],[0,1,2,6]),([24,0,1,2,3,4,5],[0,1,2,7],[0,1,7]),([24,0,1,2,3,5],[2,7,9,10],[0,1,6]),([173,0,1,2,3,4,5],[5,7],[]),([77,0,1,2,3,9,4,5],[8],[0,2]),([99,25,0,1,19,3,4,5],[1,4],[0,2]),([99,0,1,2,3,23,4,5],[7,11],[0]),([99,0,1,183,3,9,4,5],[4],[0]),([99,0,1,19,3,9,4,5],[4],[0]),([59,0,1,2,3,9,4,5],[1,6],[0,2]),([154,25,0,1,2,3,4,5],[1,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_2Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_2Pools s0NAutos s0NBucket6 7 s0NBlock7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_2Mem : ∀ ns ∈ s0NBlock7_2, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_2Ok
def s0NBlock7_3Specs : List PoolSpec := [(4,[(1,7,2),(2,8,3)]),(9,[]),(11,[]),(5,[]),(4,[(1,0,2),(2,19,3)]),(6,[]),(8,[]),(2,[(2,0,1),(1,7,2)]),(3,[(2,0,1),(1,7,2),(2,8,3)]),(1,[(2,0,1),(2,8,3)]),(2,[(2,0,1),(1,0,2)]),(1,[(2,19,3)]),(2,[(1,0,2),(3,1,19)])]
def s0NBlock7_3Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock7_3Specs
def s0NBlock7_3 : List NodeSpec := [([92,0,1,2,3,4,26,5],[6],[0,2]),([92,0,1,19,3,4,10,5],[3,6],[0,1,2]),([92,1,2,19,3,4,103,5],[3,6],[0,4]),([92,1,2,19,3,4,26,5],[6],[0,1]),([92,1,2,3,4,26,5],[6],[0,2,5]),([92,1,19,3,4,10,5],[1,3,6],[0,2]),([29,0,2,28,3,4,5],[1,2,3],[0]),([13,7,0,1,2,3,4,5],[5,7],[0,2]),([13,0,1,2,8,3,4,5],[3,7],[0]),([13,0,1,2,3,4,5],[0,3,7,8,9],[0,1]),([25,84,0,1,19,3,4,5],[11],[0]),([25,7,0,1,2,3,4,5],[2,10],[2]),([25,108,0,1,2,3,4,5],[1,3,12],[0]),([25,0,1,152,2,3,4,5],[3,4],[0]),([25,0,1,6,2,3,4,5],[1,3,4],[0]),([25,0,1,2,19,23,4,5],[5],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_3Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_3Pools s0NAutos s0NBucket6 7 s0NBlock7_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_3Mem : ∀ ns ∈ s0NBlock7_3, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_3Ok
def s0NBlock7_4Specs : List PoolSpec := [(9,[]),(11,[]),(5,[]),(12,[]),(4,[(1,0,2),(2,19,3)]),(6,[]),(10,[]),(1,[(1,0,1),(2,38,3)]),(3,[(1,0,1),(1,6,2),(2,38,3)]),(0,[(1,6,2),(2,38,3)]),(7,[]),(8,[]),(2,[(2,0,1),(2,7,2)]),(2,[(1,0,2),(2,0,2)]),(3,[(1,0,2),(2,0,2)]),(1,[(2,19,3)]),(2,[(1,0,2),(1,1,2)]),(2,[(1,0,2),(1,1,19)]),(1,[(1,19,3),(2,19,3)]),(3,[(1,0,2),(2,19,3)])]
def s0NBlock7_4Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_4Specs
def s0NBlock7_4 : List NodeSpec := [([25,0,1,2,38,3,4,5],[2,3,4],[0]),([25,0,1,2,3,4,121,5],[19],[0]),([25,0,1,2,23,4,5],[11,18],[0,1,4]),([25,0,1,19,28,3,4,5],[1,2,4],[0]),([25,0,1,19,9,4,5],[5,15],[0,1]),([33,0,1,19,3,4,5],[1,6,16],[0,1]),([33,0,6,2,3,4,5],[1,2],[0,1]),([39,0,1,2,19,3,4,5],[0,1,17],[0]),([39,0,1,2,3,4,5],[6,7,8,9],[0]),([69,0,1,2,3,4,18,5],[1,2,10,12],[0,1]),([130,0,1,2,19,3,4,5],[2],[0]),([84,35,0,1,3,4,5],[11],[0,1,2,3,6]),([84,0,1,2,3,4,88,5],[11],[0,2]),([84,0,1,2,85,4,18,5],[2,11],[0,3]),([84,0,1,19,3,23,4,5],[5,13,14],[0]),([84,0,1,19,3,4,18,5],[2,11,13],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_4Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_4Pools s0NAutos s0NBucket6 7 s0NBlock7_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_4Mem : ∀ ns ∈ s0NBlock7_4, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_4Ok
def s0NBlock7_5Specs : List PoolSpec := [(9,[]),(11,[]),(5,[]),(13,[]),(4,[(1,3,4),(3,2,18)]),(6,[]),(7,[]),(2,[(1,0,1),(2,6,2)]),(8,[]),(2,[(2,0,1),(1,7,2)]),(2,[(2,0,1),(1,0,2)]),(2,[(1,0,2),(2,0,2)]),(1,[(1,0,3)]),(2,[(1,0,2),(3,2,20)]),(2,[(1,0,2),(3,2,23)]),(1,[(1,0,9)])]
def s0NBlock7_5Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock7_5Specs
def s0NBlock7_5 : List NodeSpec := [([84,1,19,3,20,4,5],[0,5,11],[0,1]),([44,0,1,2,3,4,18,5],[0,1,2,6,7],[0]),([62,0,1,19,3,20,4,5],[2,12,13],[0,2]),([62,0,1,19,3,23,4,5],[5,14],[0,2]),([62,0,1,19,3,4,5],[0,2,8,13],[0,2]),([62,0,1,3,9,23,4,5],[8],[0]),([62,0,1,3,9,4,5],[8,15],[]),([62,1,19,3,20,4,5],[0,2,5,13],[0,2,8]),([35,0,1,28,3,4,5],[4,8],[0,2,3]),([7,51,0,1,2,3,4,5],[],[0]),([7,0,1,79,2,3,4,5],[],[0]),([7,0,1,2,3,11,4,5],[3,5],[0]),([7,0,1,2,3,23,4,5],[3],[0]),([7,0,1,2,3,4,52,5],[2,8],[0,2,3]),([7,0,1,8,3,9,4,5],[2,5,9],[0]),([7,0,1,19,3,9,4,5],[1,2,10],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_5Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_5Pools s0NAutos s0NBucket6 7 s0NBlock7_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_5Mem : ∀ ns ∈ s0NBlock7_5, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_5Ok
def s0NBlock7_6Specs : List PoolSpec := [(9,[]),(1,[(1,0,1),(2,0,1)]),(4,[(1,2,3)]),(4,[]),(11,[]),(5,[]),(12,[]),(13,[]),(4,[(1,0,2),(1,19,3)]),(6,[]),(7,[]),(4,[(1,2,3),(3,0,9)]),(8,[]),(2,[(1,0,2),(3,1,19)]),(3,[(1,0,2),(3,1,19)]),(2,[(1,1,2),(0,0,28)]),(3,[]),(2,[(1,1,2),(3,0,28)]),(2,[(1,1,2),(1,33,0)]),(0,[(1,2,3),(1,0,9)]),(1,[(1,0,9),(3,1,23)]),(1,[(1,1,9),(0,0,54)]),(1,[(1,1,9),(3,0,54)])]
def s0NBlock7_6Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_6Specs
def s0NBlock7_6 : List NodeSpec := [([7,0,1,3,9,4,10,5],[6,7,12],[0,1,2,3]),([7,0,6,2,3,9,4,5],[0,1,2],[0,2]),([7,1,2,19,3,20,4,5],[4,5],[0]),([108,0,1,2,3,23,4,5],[6,14],[0]),([108,0,1,2,3,4,18,5],[5,10,13],[0,1]),([108,0,1,19,3,9,4,5],[5,13],[0]),([108,1,2,19,3,20,4,5],[4,5],[0]),([143,0,1,2,3,9,4,5],[5,19,20],[]),([143,0,1,2,3,23,4,5],[5,8],[0]),([172,0,1,2,3,4,18,5],[4,5,17],[]),([51,0,1,6,2,3,4,5],[5,11],[0]),([138,0,1,2,3,9,4,5],[4,5,6,9,22],[0,2]),([164,0,1,2,3,4,18,5],[4,6,12,15],[0,1]),([136,0,1,2,3,9,4,5],[4,5,6,12,21],[0,2]),([0,146,1,2,3,4,5],[0,3,5,12],[0,3,9]),([0,174,1,2,3,4,5],[4,5,16,18],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_6Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_6Pools s0NAutos s0NBucket6 7 s0NBlock7_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_6Mem : ∀ ns ∈ s0NBlock7_6, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_6Ok
def s0NBlock7_7Specs : List PoolSpec := [(9,[]),(11,[]),(5,[]),(12,[]),(13,[]),(4,[(1,0,2),(1,2,3)]),(4,[(1,0,2),(1,19,3)]),(7,[]),(4,[(1,2,3),(1,2,4)]),(4,[(1,2,3),(1,9,4)]),(8,[]),(1,[(2,0,1),(1,7,3)]),(2,[(2,0,1),(1,7,2)]),(3,[(2,0,1),(1,7,2)]),(1,[(2,0,1),(1,0,3)]),(0,[(1,0,2),(1,108,3)]),(2,[(1,0,2),(3,1,19)]),(3,[(1,0,2),(2,19,3)]),(2,[(2,0,2),(1,84,1)]),(4,[(1,2,3),(2,0,9)]),(1,[(2,0,9),(1,99,1)])]
def s0NBlock7_7Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_7Specs
def s0NBlock7_7 : List NodeSpec := [([0,1,181,2,3,9,4,5],[2,19,20],[0]),([0,1,157,2,3,4,18,5],[0,1,2,3,18],[0]),([0,1,6,2,3,23,4,5],[2,4,6],[0]),([0,1,6,2,3,4,52,5],[0,2,9],[0]),([0,1,6,19,3,9,4,5],[0,2,3,5],[0]),([0,1,6,3,9,4,10,5],[3,4,8],[0]),([0,1,2,8,3,16,4,5],[3,11],[0,2]),([0,1,2,8,3,20,4,5],[2,3,14],[0]),([0,1,2,8,3,11,4,5],[12,13],[0]),([0,1,2,8,3,4,18,5],[1,7,12],[0,1,4,5]),([0,1,2,129,19,3,4,5],[2,3],[2]),([0,1,2,19,3,125,4,5],[2,15,16],[0,2]),([0,1,2,19,3,124,23,5],[10],[0,1]),([0,1,2,19,3,4,103,5],[2,10],[0,4]),([0,1,2,19,3,4,121,5],[10,17],[0,2]),([0,1,2,19,3,4,139,5],[10],[0,1,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_7Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_7Pools s0NAutos s0NBucket6 7 s0NBlock7_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_7Mem : ∀ ns ∈ s0NBlock7_7, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_7Ok
def s0NBlock7_8Specs : List PoolSpec := [(4,[(1,7,2),(1,8,3)]),(9,[]),(11,[]),(5,[]),(12,[]),(13,[]),(4,[(1,0,2),(1,19,3)]),(6,[]),(10,[]),(4,[(1,6,2),(1,3,4)]),(7,[]),(2,[(1,0,1),(1,6,2)]),(1,[(1,0,1),(1,44,3)]),(1,[(1,0,1),(1,6,9)]),(8,[]),(2,[(2,0,1),(1,7,2)]),(1,[(2,0,1),(1,8,3)]),(1,[(2,0,1),(1,69,3)]),(2,[(2,0,1),(2,7,2)]),(1,[(2,0,1),(1,7,9)]),(3,[(1,0,2),(1,1,19)]),(2,[(1,0,2),(3,1,19)]),(1,[(3,1,19),(1,108,3)]),(3,[(1,1,2),(0,0,28),(1,164,3)]),(2,[(1,1,2),(0,0,28)]),(0,[(1,2,3),(1,0,9)]),(1,[(1,0,9),(1,1,9)])]
def s0NBlock7_8Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_8Specs
def s0NBlock7_8 : List NodeSpec := [([0,1,2,19,23,4,18,5],[14],[0,1,3,4]),([0,1,2,38,3,23,4,5],[3,6,7,20],[0]),([0,1,2,38,3,4,18,5],[3,9,10,11],[0]),([0,1,2,3,70,4,5],[1,10,17,18],[0]),([0,1,2,3,85,4,89,5],[3,14],[0,1]),([0,1,2,3,85,4,88,5],[14],[0]),([0,1,2,3,45,4,5],[1,10,12],[0,3]),([0,1,2,3,125,4,5],[8,10,21,22],[0]),([0,1,2,3,165,4,5],[1,2,23,24],[0]),([0,1,2,3,20,4,26,5],[14],[0,2,5]),([0,1,2,3,36,4,26,5],[3,4],[0,2]),([0,1,2,3,9,11,4,5],[3,10,19],[0,2]),([0,1,2,3,9,55,4,5],[1,2,10,13],[0,2]),([0,1,2,3,11,4,5],[0,14,15,16],[0,1,2,4]),([0,1,2,3,124,23,5],[5,14],[0,2,3,6]),([0,1,2,3,23,54,4,5],[3,14,25,26],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_8Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_8Pools s0NAutos s0NBucket6 7 s0NBlock7_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_8Mem : ∀ ns ∈ s0NBlock7_8, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_8Ok
def s0NBlock7_9Specs : List PoolSpec := [(4,[(1,7,2),(1,2,3)]),(9,[]),(4,[]),(11,[]),(5,[]),(4,[(1,0,2),(1,19,3)]),(6,[]),(8,[]),(2,[(2,0,1),(1,7,2)]),(3,[(1,0,2),(2,19,3)]),(3,[(1,1,2),(0,0,28),(1,164,3)]),(2,[(1,1,2),(0,0,28),(1,164,5)]),(3,[(1,1,2),(0,0,28),(1,164,5)]),(1,[(2,0,9)]),(1,[(2,0,9),(1,99,9)]),(2,[(2,0,9),(1,99,9)])]
def s0NBlock7_9Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock7_9Specs
def s0NBlock7_9 : List NodeSpec := [([0,1,2,3,23,55,4,5],[4,5,7],[0,2]),([0,1,2,3,23,4,26,5],[7],[0,1]),([0,1,2,3,23,4,139,5],[7],[0,2]),([0,1,2,3,23,4,5],[1,2,4,7,14,15],[0,3]),([0,1,2,3,4,159,5],[1,7],[]),([0,1,2,3,4,121,5],[1,2,4,7,9],[0,2]),([0,1,2,3,4,34,5],[3,4,7],[0,3]),([0,1,2,3,4,88,5],[1,2,4,7],[0,1]),([0,1,2,3,4,139,5],[1,2,4,7],[0,1,2,3,4]),([0,1,2,3,4,192],[1,6],[]),([0,1,2,3,4,170],[1,3,11,12],[0]),([0,1,2,3,188,5],[4,7],[]),([0,1,2,85,4,18,5],[1,4,7],[0,3]),([0,1,2,165,4,5],[1,3,10],[0]),([0,1,183,3,9,4,5],[1,4,7,13],[2]),([0,1,8,3,9,4,5],[0,3,4,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_9Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_9Pools s0NAutos s0NBucket6 7 s0NBlock7_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_9Mem : ∀ ns ∈ s0NBlock7_9, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_9Ok
def s0NBlock7_10Specs : List PoolSpec := [(9,[]),(1,[(1,0,1),(2,0,1)]),(4,[(1,7,2)]),(11,[]),(5,[]),(4,[(1,0,2),(1,0,3),(1,2,3)]),(12,[]),(4,[(1,0,2),(1,2,3)]),(4,[(1,0,2),(1,19,3)]),(6,[]),(4,[(1,3,4)]),(2,[(1,0,1),(1,1,2)]),(7,[]),(4,[(1,2,3),(1,2,4),(1,3,4)]),(8,[]),(2,[(1,0,2),(2,0,2)]),(1,[]),(1,[(1,0,3)]),(2,[(1,0,2),(1,1,2)]),(3,[(1,0,2),(1,1,2)]),(2,[(1,0,2),(1,1,19)]),(2,[])]
def s0NBlock7_10Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_10Specs
def s0NBlock7_10 : List NodeSpec := [([0,1,19,28,3,23,4,5],[4,8,9,18,19],[0]),([0,1,19,28,3,4,18,5],[3,4,6,14,18],[0,1]),([0,1,19,38,3,9,4,5],[0,3,7,20],[0]),([0,1,19,3,85,4,5],[0,9,15],[0]),([0,1,19,3,20,4,10,5],[4,14],[0,1,2,3]),([0,1,19,3,36,4,10,5],[4,12],[0,1,2]),([0,1,19,3,9,54,4,5],[3,6,9],[0]),([0,1,19,3,9,4,26,5],[14],[0,1]),([0,1,19,3,4,52,5],[0,4,14],[0,1]),([0,1,19,20,9,4,5],[0,4,5,14,17],[0,2,6]),([0,1,19,9,4,18,5],[14],[0,1,2]),([0,1,3,9,4,26,5],[14],[0]),([0,1,9,10,18,5],[13,14,16,21],[0,1,2,6]),([0,187,2,3,4,5],[0,9],[]),([0,6,2,8,3,4,5],[0,1,2],[0,1]),([0,6,2,28,3,4,18,5],[0,3,4,9,10,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_10Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_10Pools s0NAutos s0NBucket6 7 s0NBlock7_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_10Mem : ∀ ns ∈ s0NBlock7_10, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_10Ok
def s0NBlock7_11Specs : List PoolSpec := [(9,[]),(4,[(1,2,3)]),(11,[]),(5,[]),(4,[(1,0,2),(1,0,3),(1,2,3)]),(4,[(1,0,2),(1,0,3)]),(12,[]),(6,[]),(10,[]),(7,[]),(1,[(1,0,1),(1,1,9)]),(8,[]),(1,[]),(1,[(1,0,3)]),(2,[(1,0,2)]),(2,[(1,0,2),(1,1,2)])]
def s0NBlock7_11Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock7_11Specs
def s0NBlock7_11 : List NodeSpec := [([0,6,2,3,9,54,4,5],[1,2,6,7,10],[]),([1,6,2,19,3,20,4,5],[0,2,3,5],[0]),([1,2,19,38,3,20,4,5],[0,2,3,5,7],[0]),([1,2,19,3,20,4,22,5],[11],[0,1,2,3,4,5]),([1,2,19,3,20,4,37,5],[3,9],[0]),([1,2,19,3,20,4,26,5],[11],[0,1,2]),([1,2,19,3,4,103,5],[0,3,11],[0]),([1,2,3,20,4,26,5],[11],[0,2,5,8]),([1,19,28,3,20,4,5],[5,8,12,15],[0]),([1,19,3,20,4,10,5],[0,3,11],[0,2,3,8]),([1,19,20,9,4,5],[0,3,4,11,13,14],[0,2,6,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_11Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_11Pools s0NAutos s0NBucket6 7 s0NBlock7_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_11Mem : ∀ ns ∈ s0NBlock7_11, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_11Ok
def s0NNodes7 : List NodeSpec := s0NBlock7_0 ++ s0NBlock7_1 ++ s0NBlock7_2 ++ s0NBlock7_3 ++ s0NBlock7_4 ++ s0NBlock7_5 ++ s0NBlock7_6 ++ s0NBlock7_7 ++ s0NBlock7_8 ++ s0NBlock7_9 ++ s0NBlock7_10 ++ s0NBlock7_11
def s0NBucket7 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 7 xs.toFinset) s0NBucket7 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append s0NBlock7_0Mem s0NBlock7_1Mem) s0NBlock7_2Mem) s0NBlock7_3Mem) s0NBlock7_4Mem) s0NBlock7_5Mem) s0NBlock7_6Mem) s0NBlock7_7Mem) s0NBlock7_8Mem) s0NBlock7_9Mem) s0NBlock7_10Mem) s0NBlock7_11Mem)
def s0NBlock8_0Specs : List PoolSpec := [(9,[]),(4,[]),(11,[]),(5,[]),(1,[(1,0,1),(2,6,5)]),(4,[(1,0,2),(2,19,3)]),(1,[(1,0,1)]),(10,[]),(2,[(1,0,1),(2,6,2)]),(3,[(1,0,1),(2,6,2)]),(2,[(1,0,1),(2,6,5)]),(3,[(1,0,1),(2,6,5)]),(4,[(1,2,3),(2,9,4)]),(8,[]),(1,[(2,0,1)]),(2,[(2,0,1),(2,7,2)]),(3,[(2,0,1),(2,7,2)]),(2,[(1,0,2),(2,0,2)]),(3,[(1,0,2),(2,0,2)]),(1,[(2,19,3)]),(1,[]),(2,[(1,0,2)]),(1,[(2,0,3)]),(3,[(1,0,2),(2,19,3)]),(1,[(1,84,3)]),(2,[(2,0,2)]),(1,[(2,84,3)]),(4,[(2,0,2),(1,3,4)]),(2,[(1,1,2)]),(4,[(1,2,3),(2,0,9)]),(1,[(2,0,9)])]
def s0NBlock8_0Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock8_0Specs
def s0NBlock8_0 : List NodeSpec := [([21,0,1,6,2,3,4],[0,1,3,4,10,11],[0,1,4]),([21,0,1,2,3,4],[0,4,7,10,11],[0,1,2,3,4]),([53,0,1,2,3,4,5],[0,3,12,13],[0,2,3,6,9]),([99,0,1,2,3,9,4,5],[0,3,13,29,30],[0,2,6]),([99,0,1,2,3,4,5],[0,13,25,26],[0,3]),([92,84,1,2,3,4,5],[0,13,22,25],[1,4]),([92,0,1,2,19,3,4,5],[0,13,21,22],[0,1,2]),([92,1,2,19,3,4,5],[0,7,13,21,22],[0,2]),([25,0,1,2,19,3,4,5],[0,3,5,19,21,23],[0,1,2,6]),([25,0,1,2,3,4,5],[0,3,5,13,19,21,23],[0,1,2,6,7]),([33,0,1,2,3,4,5],[2,3,13,28],[0,1,3]),([69,0,1,2,3,4,5],[0,14,15,16],[0,1]),([84,0,1,2,3,85,4,5],[0,13,24,25],[0,3]),([84,0,1,2,3,4,18,5],[0,3,13,20,25,27],[0,1,2,3,6]),([84,0,1,19,3,4,5],[0,17,18,20],[0,1]),([44,0,1,2,3,4,5],[0,6,8,9],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock8_0Pools s0NAutos s0NBucket7 8 s0NBlock8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_0Mem : ∀ ns ∈ s0NBlock8_0, Impossible s0NG 8 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket7Ok s0NBlock8_0Ok
def s0NBlock8_1Specs : List PoolSpec := [(9,[]),(1,[(1,0,1),(2,0,1)]),(4,[(1,7,2)]),(4,[(1,2,3)]),(2,[(1,0,1),(2,0,1)]),(4,[]),(3,[(1,0,1),(2,0,1)]),(11,[]),(5,[]),(12,[]),(13,[]),(1,[(1,0,1)]),(4,[(1,0,2)]),(10,[]),(4,[(1,2,3),(3,0,9)]),(2,[(1,0,1)]),(8,[]),(2,[(2,0,1),(1,7,2)]),(1,[(2,0,1)]),(3,[(2,0,1),(1,7,2)]),(2,[(2,0,1),(1,0,2)]),(3,[(2,0,1),(1,0,2)]),(2,[(2,0,1)]),(1,[]),(2,[(1,0,2),(1,1,19)]),(3,[(1,0,2),(1,1,19)]),(1,[(1,1,19)]),(2,[(1,0,2),(3,1,19)]),(3,[(1,0,2),(3,1,19)]),(1,[(3,1,19)]),(2,[(2,0,2),(1,84,1)]),(1,[(1,84,1)]),(3,[(2,0,2),(1,84,1)]),(2,[(1,1,2),(0,0,28)]),(1,[(0,0,28)]),(3,[]),(2,[]),(3,[(1,1,2),(0,0,28)]),(2,[(1,1,2),(3,0,28)]),(3,[(1,1,2),(3,0,28)])]
def s0NBlock8_1Pools : BT (Option BoundPool) := buildPoolsBT 6 s0NW s0NR s0NSlices s0NBlock8_1Specs
def s0NBlock8_1 : List NodeSpec := [([7,0,1,2,8,3,4,5],[0,17,18,19],[0,1]),([7,0,1,2,19,3,4,5],[0,7,18,20,21],[0,1,2,3]),([7,0,1,2,3,9,4,5],[3,8,10,16,18,22],[0,2,3]),([7,0,6,2,3,4,5],[0,1,4,5,6],[0,1,2,3,4]),([108,0,1,2,19,3,4,5],[12,13,27,28,29],[0,1]),([108,0,1,2,3,4,5],[13,27,28,29],[0,1]),([191,0,1,2,3,4,5],[5,13,16],[0]),([172,0,1,2,3,4,5],[7,8,38,39],[0]),([51,0,1,2,3,4,5],[0,8,14,16],[0,6]),([164,0,1,2,3,4,5],[0,5,33,34,35,36,37],[0,1]),([186,0,1,2,3,4,5],[0,5,16,23,35,36],[0,6]),([0,1,157,2,3,4,5],[0,5,8,30,31,32],[0]),([0,1,6,2,19,3,4,5],[0,8,9,10,11,12],[0,1]),([0,1,6,2,3,9,4,5],[0,3,8,10,11,15,16],[0,2,3]),([0,1,2,8,3,4,5],[2,8,17,18,19],[0,1]),([0,1,2,19,38,3,4,5],[0,7,12,13,24,25,26],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_1Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock8_1Pools s0NAutos s0NBucket7 8 s0NBlock8_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_1Mem : ∀ ns ∈ s0NBlock8_1, Impossible s0NG 8 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket7Ok s0NBlock8_1Ok
def s0NBlock8_2Specs : List PoolSpec := [(9,[]),(4,[(1,2,3)]),(4,[]),(11,[]),(5,[]),(4,[(1,0,2),(1,0,3)]),(12,[]),(4,[(1,0,2),(1,2,3)]),(4,[(1,0,2),(1,19,3)]),(1,[(1,0,1)]),(4,[(1,0,2)]),(4,[(1,3,4)]),(2,[(1,0,1),(1,1,2)]),(10,[]),(3,[(1,0,1),(1,1,2)]),(2,[(1,0,1),(1,6,2)]),(4,[(1,6,2)]),(3,[(1,0,1),(1,6,2)]),(4,[(1,2,3),(1,2,4)]),(4,[(1,2,3),(1,9,4)]),(8,[]),(1,[]),(1,[(1,0,3)]),(2,[(1,0,2)]),(2,[(1,0,2),(1,1,2)]),(3,[(1,0,2),(1,1,2)]),(1,[(1,1,3)]),(1,[(1,19,3)]),(3,[(1,0,2)]),(4,[(1,0,2),(1,3,4)]),(1,[(1,84,3)]),(2,[(2,0,2)]),(3,[]),(2,[]),(0,[(1,28,3)]),(2,[(1,1,2)]),(1,[(1,0,9)]),(4,[(1,2,3),(1,0,9)]),(2,[(1,0,9)]),(1,[(1,1,9)])]
def s0NBlock8_2Pools : BT (Option BoundPool) := buildPoolsBT 6 s0NW s0NR s0NSlices s0NBlock8_2Specs
def s0NBlock8_2 : List NodeSpec := [([0,1,2,19,3,20,4,5],[0,5,13,20,22,23],[0,2,6]),([0,1,2,19,3,36,4,5],[6,10,13,20,23,26],[0,1,2]),([0,1,2,19,3,23,4,5],[0,4,8,20,23,27,28],[0,1,6]),([0,1,2,19,3,4,18,5],[0,4,20,21,23,29],[0,1,2,3,4,5,6]),([0,1,2,28,3,4,18,5],[3,4,11,20,35],[0,2,3]),([0,1,2,38,3,4,5],[9,13,15,16,17],[0,1]),([0,1,2,3,85,4,5],[0,13,20,30,31],[0,3]),([0,1,2,3,9,23,4,5],[4,20,36,37,38],[0,2,6]),([0,1,2,3,9,54,4,5],[1,3,4,6,20,39],[0,2]),([0,1,2,3,23,4,5],[0,4,8,20,23,27,28],[0,1,2,4,6,7]),([0,1,2,3,54,4,5],[3,6,13,20,34],[0]),([0,1,2,3,4,52,5],[0,4,19,20],[0,2,3,6]),([0,1,19,28,3,4,5],[10,13,21,24,25],[0,1]),([0,1,19,3,9,4,5],[0,4,7,20,21,23],[0,1,6,7]),([0,1,3,9,4,10,5],[18,20,32,33],[0,1,2,3,6]),([0,6,2,28,3,4,5],[2,9,12,13,14],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_2Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock8_2Pools s0NAutos s0NBucket7 8 s0NBlock8_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_2Mem : ∀ ns ∈ s0NBlock8_2, Impossible s0NG 8 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket7Ok s0NBlock8_2Ok
def s0NBlock8_3Specs : List PoolSpec := [(4,[]),(4,[(1,0,2),(1,0,3)]),(10,[]),(8,[]),(1,[]),(1,[(1,0,3)]),(2,[(1,0,2)])]
def s0NBlock8_3Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock8_3Specs
def s0NBlock8_3 : List NodeSpec := [([0,2,28,3,36,4,5],[0,2,3,4],[0,2]),([1,2,19,3,20,4,5],[1,3,5,6],[0,2,6,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_3Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock8_3Pools s0NAutos s0NBucket7 8 s0NBlock8_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_3Mem : ∀ ns ∈ s0NBlock8_3, Impossible s0NG 8 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket7Ok s0NBlock8_3Ok
def s0NNodes8 : List NodeSpec := s0NBlock8_0 ++ s0NBlock8_1 ++ s0NBlock8_2 ++ s0NBlock8_3
def s0NBucket8 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 8 xs.toFinset) s0NBucket8 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append s0NBlock8_0Mem s0NBlock8_1Mem) s0NBlock8_2Mem) s0NBlock8_3Mem)
def s0NBlock9_0Specs : List PoolSpec := [(9,[]),(4,[(1,2,3)]),(4,[]),(11,[]),(5,[]),(1,[(1,0,1)]),(4,[(1,0,2)]),(10,[]),(2,[(1,0,1)]),(8,[]),(3,[(1,0,1)]),(1,[(2,0,1)]),(2,[(2,0,1)]),(3,[(2,0,1)]),(1,[]),(2,[(1,0,2)]),(3,[(1,0,2)]),(2,[(2,0,2)]),(3,[(2,0,2)]),(3,[]),(2,[]),(2,[(1,1,2)]),(3,[(1,1,2)])]
def s0NBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock9_0Specs
def s0NBlock9_0 : List NodeSpec := [([84,0,1,2,3,4,5],[0,2,7,14,17,18],[0,1,2,3,6]),([7,0,1,2,3,4,5],[2,4,11,12,13],[0,1,2,3,4]),([0,1,6,2,3,4,5],[0,2,4,5,8,10],[0,1,2,3,4]),([0,1,2,19,3,4,5],[6,14,15,16],[0,1,6,7]),([0,1,2,28,3,4,5],[2,3,4,14,21,22],[0,1,2,3]),([0,1,2,3,9,4,5],[1,9,14,19,20],[0,2,3,6,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock9_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock9_0Pools s0NAutos s0NBucket8 9 s0NBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock9_0Mem : ∀ ns ∈ s0NBlock9_0, Impossible s0NG 9 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket8Ok s0NBlock9_0Ok
def s0NNodes9 : List NodeSpec := s0NBlock9_0
def s0NBucket9 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 9 xs.toFinset) s0NBucket9 := buildBucketsBT_of_mem s0NBlock9_0Mem
def s0NBlock10_0Specs : List PoolSpec := [(4,[]),(1,[]),(3,[]),(2,[])]
def s0NBlock10_0Pools : BT (Option BoundPool) := buildPoolsBT 2 s0NW s0NR s0NSlices s0NBlock10_0Specs
def s0NBlock10_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3],[0,1,2,3,4,6,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock10_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock10_0Pools s0NAutos s0NBucket9 10 s0NBlock10_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock10_0Mem : ∀ ns ∈ s0NBlock10_0, Impossible s0NG 10 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket9Ok s0NBlock10_0Ok
def s0NNodes10 : List NodeSpec := s0NBlock10_0
def s0NBucket10 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 10 xs.toFinset) s0NBucket10 := buildBucketsBT_of_mem s0NBlock10_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBound : Lower s0NR s0NG 11 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) s0NBucket10Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q0 : Lower (varsOf 95) 0xfffffffefffffffefefaeca0fefaeca0 11 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (3, 4), (0, 1)]) (roots2 := s0NR) (T2 := s0NG) _ s0NBound
  decide +kernel
lemma lb519 : Lower lb11 lb0 4 := carry_of lb287 lb375
def lb461 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def lb467 : List Nat := varsOf 38
lemma lb521 : carryOK [(2,4),(1,3)] lb467 lb461 lb217 lb206 = true := by decide +kernel
lemma lb520 : Lower lb467 lb461 4 := carry_of lb521 lb375
def lb454 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def lb464 : List Nat := varsOf 42
lemma lb507 : carryOK [(2,4),(1,2),(1,3)] lb464 lb454 lb217 lb206 = true := by decide +kernel
lemma lb506 : Lower lb464 lb454 4 := carry_of lb507 lb375
def lb455 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def lb465 : List Nat := varsOf 50
lemma lb509 : carryOK [(1,2),(1,3)] lb465 lb455 lb217 lb206 = true := by decide +kernel
lemma lb508 : Lower lb465 lb455 4 := carry_of lb509 lb375
def lb456 : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000
lemma lb511 : carryOK [(1,5),(1,4),(1,3),(1,2)] lb218 lb456 lb222 lb322 = true := by decide +kernel
lemma lb510 : Lower lb218 lb456 7 := carry_of lb511 lb382
def lb457 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
lemma lb513 : carryOK [(1,4),(1,3),(1,2)] lb219 lb457 lb222 lb322 = true := by decide +kernel
lemma lb512 : Lower lb219 lb457 7 := carry_of lb513 lb382
def lb458 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def lb466 : List Nat := varsOf 54
lemma lb515 : carryOK [(1,3),(1,2)] lb466 lb458 lb222 lb322 = true := by decide +kernel
lemma lb514 : Lower lb466 lb458 7 := carry_of lb515 lb382
def lb459 : Nat := 0xffcccc00cc000000ffcccc00cc000000
lemma lb517 : carryOK [(1,2)] lb220 lb459 lb222 lb322 = true := by decide +kernel
lemma lb516 : Lower lb220 lb459 7 := carry_of lb517 lb382
def lb460 : Nat := 0xfcc0c000c0000000fcc0c000c0000000
def lb530 : List Nat := [30,30,30,30,46,46,46,46,54,54,54,54,58,58,58,58,60,60,60,60,30,30,30,30,30,30,46,46,46,46,46,46,54,54,54,54,54,54,58,58,58,58,58,58,60,60,60,60,60,60]
def lb522 : List Nat := [28,26,22,14,44,42,38,14,52,50,38,22,56,50,42,26,56,52,44,28,38,42,44,50,52,56,22,26,28,50,52,56,14,26,28,42,44,56,14,22,28,38,44,52,14,22,26,38,42,50]
def lb472 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xffffff0ffff,0x3f2cb2cb0eeee),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3f03fffff0fff,0xbfd5555e0ddd),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffc0fffff0ff,0x1557f9a6dd0bb),(0xffff0000ffff0000ffff0000ffff0000,0x3ffff03ffff0f,0x269a6ff8bbb07),(0xffffffff00000000ffffffff00000000,0x3fffffc0ffff0,0x38e38e3f77770)]
def lb561 : List (Nat × Nat × Nat) := [(0,0,1),(0,2,3),(0,0,2),(3,5,2),(0,5,2),(0,1,3),(0,3,4),(3,8,3),(2,5,6),(0,9,3),(0,1,2),(0,0,3),(3,9,3),(0,5,3),(3,13,0),(0,1,4),(0,2,4),(3,12,4),(3,16,4),(3,14,4),(0,0,4),(3,14,0),(0,12,4),(1,14,4),(2,2,11),(0,17,4),(0,14,4),(0,16,4),(3,17,4),(3,14,1),(3,31,0)]
def lb468 : Array Decor := buildWires lb472 lb561
def lb470 : Array (List (Nat × Nat)) := #[[],[(1,2)],[(1,3),(1,2)],[(1,2),(2,4),(1,5)],[(4,5)],[(1,5),(1,4),(1,3),(1,2)],[(3,5),(3,4)],[(3,5),(2,3),(2,4)],[(3,5),(1,2),(1,4)],[(2,3),(1,3),(2,5),(1,4)],[(2,3),(3,5),(2,4)],[(3,4),(3,5)],[(3,4)],[(3,4),(2,3),(2,5)],[(2,3),(2,4)],[(3,4),(2,3),(1,2),(1,5)],[(2,3),(1,2),(1,4)],[(3,5),(2,3),(1,2),(1,4)],[(3,5),(2,4)],[(2,5),(2,4),(2,3)],[(2,4)],[(2,3),(3,5),(1,2),(1,4)],[(2,3)],[(1,4),(1,3),(1,2)],[(2,4),(2,3)],[(4,5),(1,2),(1,3)],[(2,5),(1,4)],[(4,5),(1,2)],[(4,5),(2,3)],[(1,2),(1,4)],[(3,4),(1,2)],[(4,5),(1,3),(1,2)],[(2,5),(2,4)],[(3,5),(3,4),(1,2)],[(1,3),(1,4),(1,2)],[(3,5),(1,3),(1,4),(1,2)],[(2,4),(1,3)],[(1,2),(2,3),(1,4)],[(1,2),(1,3)],[(2,4),(1,2),(1,3)],[(2,3),(2,5),(1,4)],[(2,5),(2,4),(1,2),(1,3)],[(2,5),(2,4),(1,3)],[(1,2),(1,5),(2,4),(1,3)]]
def lb558 : List (Nat × Nat) := [(subcube 0 12,4),(subcube 0 6,4),(subcube 0 32,7),(subcube 0 48,4),(subcube 0 2,7),(subcube 0 24,4),(subcube 0 20,4),(subcube 0 10,4),(subcube 0 8,7),(subcube 0 16,7),(subcube 0 4,7),(subcube 0 34,4),(subcube 0 18,4)]
def lb559 : Array (Nat × Nat) := lb558.toArray
def lb531 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(2,[(0,0,1),(0,0,2),(0,1,2)]),(8,[(0,0,1),(0,0,3),(0,1,3)]),(9,[]),(4,[(0,5,2),(0,9,3),(3,14,4)]),(2,[(0,0,1),(0,5,2),(3,9,3)]),(4,[(0,5,2),(0,5,3),(0,2,3)]),(10,[]),(9,[(0,0,1),(0,0,2)]),(8,[(0,0,1),(0,1,3)]),(2,[(0,0,1),(3,5,2)]),(8,[(0,0,1),(3,8,3)]),(9,[(0,0,1),(3,5,2)]),(4,[(0,2,3),(2,5,6)]),(8,[]),(9,[(0,0,1),(0,5,2)]),(4,[(0,5,2),(0,2,3)]),(2,[(0,0,1),(0,5,2)]),(4,[(0,1,2)]),(9,[(0,0,1),(0,0,2),(0,1,2)]),(10,[(0,5,2),(0,0,3)]),(8,[(0,0,1),(0,0,3)]),(11,[]),(4,[(0,5,2),(0,9,3)]),(4,[(0,5,2),(3,9,3)]),(10,[(0,5,2),(3,9,3)]),(8,[(0,0,1),(3,9,3)]),(2,[(0,0,1),(0,0,2)]),(10,[(0,5,2),(0,9,3)]),(8,[(0,0,1),(0,9,3)]),(4,[(0,5,2),(0,5,3)]),(12,[]),(8,[(0,0,1)]),(9,[(0,0,1)]),(4,[(0,2,3)]),(10,[(0,2,3)]),(10,[(0,0,2)]),(4,[(0,5,2)]),(10,[(0,5,2)]),(2,[(0,0,1)])]
def lb462 : Array (Option BoundPool) := buildPools lb468 lb221 lb559 lb531
lemma lb505 : goodPairs lb460 lb530 lb522 := goodPairs_of (by decide +kernel)
lemma lb473 : ∀ x ∈ lb472, faithful lb530 lb522 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb469 : ∀ x ∈ lb468.toList, faithful lb530 lb522 x ∧ x.1 < 2^128 := buildWires_faithful lb473
lemma lb471 : ∀ sw ∈ lb470.toList, swapsValid sw = true ∧ permWord sw lb460 = lb460 := autos_of (by decide +kernel)
lemma lb533 : sliceDirectCheck 0 12 0 lb221 lb460 lb465 lb455 = true := by decide +kernel
lemma lb532 : Slice lb221 lb460 (subcube 0 12) 4 := slice_direct lb533 lb508
lemma lb541 : sliceDirectCheck 0 6 0 lb221 lb460 lb217 lb206 = true := by decide +kernel
lemma lb534 : Slice lb221 lb460 (subcube 0 6) 4 := slice_direct lb541 lb375
lemma lb543 : sliceDirectCheck 0 32 0 lb221 lb460 lb218 lb456 = true := by decide +kernel
lemma lb542 : Slice lb221 lb460 (subcube 0 32) 7 := slice_direct lb543 lb510
lemma lb545 : sliceDirectCheck 0 48 0 lb221 lb460 lb11 lb0 = true := by decide +kernel
lemma lb544 : Slice lb221 lb460 (subcube 0 48) 4 := slice_direct lb545 lb519
lemma lb547 : sliceDirectCheck 0 2 0 lb221 lb460 lb222 lb322 = true := by decide +kernel
lemma lb546 : Slice lb221 lb460 (subcube 0 2) 7 := slice_direct lb547 lb382
lemma lb549 : sliceDirectCheck 0 24 0 lb221 lb460 lb467 lb461 = true := by decide +kernel
lemma lb548 : Slice lb221 lb460 (subcube 0 24) 4 := slice_direct lb549 lb520
lemma lb551 : sliceDirectCheck 0 20 0 lb221 lb460 lb464 lb454 = true := by decide +kernel
lemma lb550 : Slice lb221 lb460 (subcube 0 20) 4 := slice_direct lb551 lb506
lemma lb553 : sliceDirectCheck 0 10 0 lb221 lb460 lb329 lb321 = true := by decide +kernel
lemma lb552 : Slice lb221 lb460 (subcube 0 10) 4 := slice_direct lb553 lb380
lemma lb555 : sliceDirectCheck 0 8 0 lb221 lb460 lb466 lb458 = true := by decide +kernel
lemma lb554 : Slice lb221 lb460 (subcube 0 8) 7 := slice_direct lb555 lb514
lemma lb557 : sliceDirectCheck 0 16 0 lb221 lb460 lb219 lb457 = true := by decide +kernel
lemma lb556 : Slice lb221 lb460 (subcube 0 16) 7 := slice_direct lb557 lb512
lemma lb536 : sliceDirectCheck 0 4 0 lb221 lb460 lb220 lb459 = true := by decide +kernel
lemma lb535 : Slice lb221 lb460 (subcube 0 4) 7 := slice_direct lb536 lb516
lemma lb538 : sliceDirectCheck 0 34 0 lb221 lb460 lb327 lb319 = true := by decide +kernel
lemma lb537 : Slice lb221 lb460 (subcube 0 34) 4 := slice_direct lb538 lb376
lemma lb540 : sliceDirectCheck 0 18 0 lb221 lb460 lb328 lb320 = true := by decide +kernel
lemma lb539 : Slice lb221 lb460 (subcube 0 18) 4 := slice_direct lb540 lb378
set_option maxRecDepth 200000 in
lemma lb560 : ∀ i (hi : i < lb559.size), Slice lb221 lb460 lb559[i].1 lb559[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb221 lb460 p.1 p.2) (forall_cons lb532 (forall_cons lb534 (forall_cons lb542 (forall_cons lb544 (forall_cons lb546 (forall_cons lb548 (forall_cons lb550 (forall_cons lb552 (forall_cons lb554 (forall_cons lb556 (forall_cons lb535 (forall_cons lb537 (forall_cons lb539 (fun _ h => (List.not_mem_nil h).elim))))))))))))))
lemma lb463 : ∀ i (hi : i < lb462.size), ∀ c, lb462[i] = some c → ValidPool lb221 lb460 c := buildPools_sound lb560
lemma lb492 : ∀ i (hi : i < lb36.size), ∀ xs ∈ lb36[i], Impossible lb460 (0 - 1) xs.toFinset := by intro i hi; simp [lb36] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb493 : checkNodes lb468 lb460 lb271 lb462 lb470 lb36 0 lb84 = true := by decide +kernel
def lb474 : Array (List (List Nat)) := buildBuckets 1 lb468 lb84
lemma lb475 : ∀ i (hi : i < lb474.size), ∀ xs ∈ lb474[i], Impossible lb460 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb505 lb469 lb463 lb471 lb492 lb493
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb494 : checkNodes lb468 lb460 lb271 lb462 lb470 lb474 1 lb84 = true := by decide +kernel
lemma lb476 : ∀ i (hi : i < lb474.size), ∀ xs ∈ lb474[i], Impossible lb460 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb505 lb469 lb463 lb471 lb475 lb494
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb495 : checkNodes lb468 lb460 lb271 lb462 lb470 lb474 2 lb84 = true := by decide +kernel
lemma lb477 : ∀ i (hi : i < lb474.size), ∀ xs ∈ lb474[i], Impossible lb460 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb505 lb469 lb463 lb471 lb476 lb495
def lb523 : List NodeSpec := [([29,8,16,20],[],[]),([29,12,25,1],[],[]),([9,32,10,21],[0],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb496 : checkNodes lb468 lb460 lb271 lb462 lb470 lb474 3 lb523 = true := by decide +kernel
def lb478 : Array (List (List Nat)) := buildBuckets 2 lb468 lb523
lemma lb479 : ∀ i (hi : i < lb478.size), ∀ xs ∈ lb478[i], Impossible lb460 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb505 lb469 lb463 lb471 lb477 lb496
def lb524 : List NodeSpec := [([8,16,20,2,11],[1],[0]),([23,8,10,2,4],[],[]),([29,12,0,1,4],[],[0,1]),([12,25,1,2,11],[2],[0]),([12,25,20,2,3],[],[]),([26,34,2,3,4],[],[]),([26,1,2,3,28],[],[]),([9,16,20,2,11],[3],[2]),([23,9,10,2,4],[],[]),([17,25,20,2,3],[],[]),([35,1,2,3,4],[],[]),([9,32,10,2,4],[0],[0]),([9,16,10,21,4],[],[0,1]),([5,7,10,21,11],[],[]),([29,8,16,1,4],[],[3,4,0]),([14,25,20,2,3],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb497 : checkNodes lb468 lb460 lb271 lb462 lb470 lb478 4 lb524 = true := by decide +kernel
def lb480 : Array (List (List Nat)) := buildBuckets 6 lb468 lb524
lemma lb481 : ∀ i (hi : i < lb480.size), ∀ xs ∈ lb480[i], Impossible lb460 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb505 lb469 lb463 lb471 lb479 lb497
def lb525 : List NodeSpec := [([5,19,1,2,3,4],[4],[]),([14,0,1,2,3,4],[2],[5]),([5,7,10,6,4],[5,1,6,7],[6,7,8,9]),([8,16,1,2,11,4],[1],[4,8,0]),([8,16,20,2,3,4],[],[10,8,0]),([5,7,15,11,3,4],[5,1,6,7,0,8],[11,12,6,13,14,7,15,16,17]),([8,16,10,2,4],[5,1,9],[4,18,8]),([5,7,10,21,3,4],[],[19,20,15,21,9,0]),([12,0,1,2,11,4],[2],[0,1]),([22,0,1,2,3,4],[],[]),([23,8,1,2,3,4],[],[0]),([9,16,10,2,4],[10,0,7,1,9],[4,0,1]),([9,5,16,10,2,4],[0,6,7,1],[]),([24,5,0,1,2,3],[11],[]),([9,5,16,1,6,4],[0,7,6,1],[]),([17,25,1,2,3,4],[2,12],[0,22]),([17,5,16,1,2,4],[10,7],[]),([26,5,1,2,3,4],[4],[]),([12,25,1,2,3,4],[2],[0]),([27,0,1,2,3,4],[],[2]),([24,0,1,2,3,4],[],[]),([14,0,1,2,3,28],[],[0,1,2,23,5]),([9,16,1,2,11,4],[3],[19,1,0,2,22]),([26,9,1,2,3,4],[4],[24]),([14,25,1,2,3,4],[2],[0,22,24]),([9,16,20,2,3,4],[],[4,1,22,25,0]),([26,14,1,2,3,4],[4],[0,22,24]),([29,8,0,1,3,4],[],[2,26,3,0,4,27]),([30,0,1,2,3,4],[12],[]),([17,9,16,1,2,4],[10,7,1],[]),([24,14,0,1,2,3],[2],[]),([9,18,0,1,6,4],[0,6,13],[]),([24,9,0,1,2,3],[],[]),([23,9,1,2,3,4],[],[0,22]),([24,0,1,2,3],[],[]),([31,0,1,2,3,4],[],[0,1,2,23,5]),([9,32,1,2,3,4],[0],[0,4,22,28]),([33,0,1,2,3,4],[12],[23])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb498 : checkNodes lb468 lb460 lb271 lb462 lb470 lb480 5 lb525 = true := by decide +kernel
def lb482 : Array (List (List Nat)) := buildBuckets 13 lb468 lb525
lemma lb483 : ∀ i (hi : i < lb482.size), ∀ xs ∈ lb482[i], Impossible lb460 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb505 lb469 lb463 lb471 lb481 lb498
def lb526 : List NodeSpec := [([5,7,10,2,3,4],[14,4,1,6,7,15,16],[6,20,14,7,16,29,8,0,30]),([8,0,1,2,11,3,4],[1,3,0,17],[0,4,18,8,1,27]),([12,0,1,2,3,4],[6,4,1,18,2,19],[0,1]),([13,5,0,1,2,3,4],[20],[0,1]),([9,5,0,1,6,3,4],[21,0,7,6,1,22,23],[0,1]),([14,9,0,1,2,3,4],[10,24,22],[0,1,2,23]),([9,0,1,2,11,3,4],[3,1,0,24],[0,23,5,4,1,27,2,31]),([5,7,15,3,4],[25,14,21,1,0,26,8,7],[12,6,14,7,16,17,0]),([9,16,1,2,3,4],[10,0,7,1,22,27,28],[0,4,22]),([17,9,0,1,2,3,4],[10,0,1,7,22],[23,0,1,2]),([14,5,0,1,2,3,4],[5,29,30],[0,1]),([17,5,0,1,2,3,4],[21,10,6,0,7,22,31],[23,0,1]),([8,16,1,2,3,4],[5,4,1,28,19],[4,18,0]),([17,0,1,2,3,4],[0,4,7,1,22,2,31,32,33,12],[23,0,1,2]),([5,7,1,2,11,3,4],[5,1,6,7,34],[11,24,19,13,20,32,0,8,30,33,9,34,35]),([14,0,1,2,3,4],[30,35,36,22,2],[0,1,2,23]),([9,5,16,1,2,3,4],[0,7,6,1],[0]),([9,18,0,1,2,3,4],[22,21,0,37],[23,2,0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb499 : checkNodes lb468 lb460 lb271 lb462 lb470 lb482 6 lb526 = true := by decide +kernel
def lb484 : Array (List (List Nat)) := buildBuckets 7 lb468 lb526
lemma lb485 : ∀ i (hi : i < lb484.size), ∀ xs ∈ lb484[i], Impossible lb460 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb505 lb469 lb463 lb471 lb483 lb499
def lb527 : List NodeSpec := [([5,0,1,6,2,3,4],[0,38,5,1,39,40,3,41,42,29],[0,36,2,23,12,6,14,22,24,16,37,38,39,33,9,40]),([5,7,1,2,3,4],[43,21,0,4,1,15,34,7,39],[12,6,14,7,0,4,22,28]),([8,0,1,2,3,4],[14,0,4,1,39,10,2,17,19],[0,4,1,27]),([9,5,0,1,2,3,4],[21,0,7,1,6,29,22,24,44,45,39],[0,4,1,27]),([9,0,1,2,3,4],[0,7,1,10,22,2,24,44,45,39],[0,4,1,27,2,31])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb500 : checkNodes lb468 lb460 lb271 lb462 lb470 lb484 7 lb527 = true := by decide +kernel
def lb486 : Array (List (List Nat)) := buildBuckets 2 lb468 lb527
lemma lb487 : ∀ i (hi : i < lb486.size), ∀ xs ∈ lb486[i], Impossible lb460 7 xs.toFinset :=
  buildBuckets_sound (by decide) lb505 lb469 lb463 lb471 lb485 lb500
def lb528 : List NodeSpec := [([5,0,1,2,3,4],[14,4,21,1,39,10,40,2,46],[0,12,6,1,30,33,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb501 : checkNodes lb468 lb460 lb271 lb462 lb470 lb486 8 lb528 = true := by decide +kernel
def lb488 : Array (List (List Nat)) := buildBuckets 1 lb468 lb528
lemma lb489 : ∀ i (hi : i < lb488.size), ∀ xs ∈ lb488[i], Impossible lb460 8 xs.toFinset :=
  buildBuckets_sound (by decide) lb505 lb469 lb463 lb471 lb487 lb501
def lb529 : List NodeSpec := [([0,1,2,3,4],[4,14,21,10,2],[0,22,24,19,38,39,41,36,42,43])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb502 : checkNodes lb468 lb460 lb271 lb462 lb470 lb488 9 lb529 = true := by decide +kernel
def lb490 : Array (List (List Nat)) := buildBuckets 1 lb468 lb529
lemma lb491 : ∀ i (hi : i < lb490.size), ∀ xs ∈ lb490[i], Impossible lb460 9 xs.toFinset :=
  buildBuckets_sound (by decide) lb505 lb469 lb463 lb471 lb489 lb502
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb504 : forestRootCheck lb221 lb460 [(VAR 1,30,28),(VAR 2,30,26),(VAR 3,30,22),(VAR 4,30,14),(VAR 5,46,14)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb503 : bucketContains lb490 lb221 = true := by decide +kernel
lemma lb518 : Lower lb221 lb460 10 := lower_of_forest lb504 lb491 lb503
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q15d : Lower (varsOf 117) 0xfafaa0a0a0a00000a0a0000000000000 10 := by
  apply carry_of (swaps := [(5, 6), (4, 5), (3, 4), (0, 1)]) (roots2 := lb221) (T2 := lb460) _ lb518
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q15 : Lower (varsOf 117) 0xfffffffffffffafafffffafafafaa0a0 10 := dualLower (by decide +kernel) (by decide +kernel) q15d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q14 : Lower (varsOf 125) 0xfffffffffffffffafffffafafafaa0a0 11 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,64,72)]) (by decide +kernel) q15
def lb634 : List Nat := [20,20,36,36,48,48,20,36,48]
def lb630 : List Nat := [16,4,32,4,32,16,32,16,4]
def lb577 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def lb569 : BT Decor := buildWiresBT 2 lb577 lb108
def lb564 : BT (Option BoundPool) := buildPoolsBT 1 lb569 lb329 lb314 lb92
lemma lb616 : goodPairs lb321 lb634 lb630 := goodPairs_of (by decide +kernel)
lemma lb578 : ∀ x ∈ lb577, faithful lb634 lb630 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb570 : btAll (fun x => faithful lb634 lb630 x ∧ x.1 < 2^128) lb569 := buildWiresBT_faithful lb578
set_option maxRecDepth 500000 in
lemma lb574 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb321 = lb321) lb229 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb645 : btAll (fun o => ∀ p, o = some p → Slice lb329 lb321 p.1 p.2) lb314 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb329 lb321 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma lb565 : btAll (fun o => ∀ c, o = some c → ValidPool lb329 lb321 c) lb564 := buildPoolsBT_sound lb645
lemma lb587 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb321 (0 - 1) xs.toFinset) lb243 := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb601 : checkNodesBT lb569 lb321 lb62 lb564 lb229 lb243 0 lb84 = true := by decide +kernel
def lb581 : BT (List (List Nat)) := buildBucketsBT lb569 lb84
set_option maxRecDepth 500000 in
lemma lb582 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb321 0 xs.toFinset) lb581 :=
  buildBucketsBT_sound (by decide) lb616 lb570 lb565 lb574 lb587 lb601
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb602 : checkNodesBT lb569 lb321 lb62 lb564 lb229 lb581 1 lb84 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb583 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb321 1 xs.toFinset) lb581 :=
  buildBucketsBT_sound (by decide) lb616 lb570 lb565 lb574 lb582 lb602
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb603 : checkNodesBT lb569 lb321 lb62 lb564 lb229 lb581 2 lb84 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb584 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb321 2 xs.toFinset) lb581 :=
  buildBucketsBT_sound (by decide) lb616 lb570 lb565 lb574 lb583 lb603
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb604 : checkNodesBT lb569 lb321 lb62 lb564 lb229 lb581 3 lb85 = true := by decide +kernel
def lb585 : BT (List (List Nat)) := buildBucketsBT lb569 lb85
set_option maxRecDepth 500000 in
lemma lb586 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb321 3 xs.toFinset) lb585 :=
  buildBucketsBT_sound (by decide) lb616 lb570 lb565 lb574 lb584 lb604
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb613 : forestRootCheck lb329 lb321 [(VAR 2,20,16),(VAR 4,20,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb612 : bucketContainsBT lb585 lb329 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb618 : Lower lb329 lb321 4 := lower_of_forestBT lb613 lb586 lb612
lemma lb625 : carryOK [(3,5),(1,3),(1,4),(1,2)] lb17 lb6 lb329 lb321 = true := by decide +kernel
lemma lb624 : Lower lb17 lb6 4 := carry_of lb625 lb618
lemma lb627 : carryOK [(1,3),(1,4),(1,2)] lb467 lb461 lb329 lb321 = true := by decide +kernel
lemma lb626 : Lower lb467 lb461 4 := carry_of lb627 lb618
lemma lb629 : carryOK [(1,2)] lb465 lb455 lb329 lb321 = true := by decide +kernel
lemma lb628 : Lower lb465 lb455 4 := carry_of lb629 lb618
def lb635 : List Nat := [22,22,22,38,38,38,50,50,50,52,52,52,22,22,22,38,38,38,50,50,50,52,52,52]
def lb631 : List Nat := [20,18,6,36,34,6,48,34,18,48,36,20,34,36,48,18,20,48,6,20,36,6,18,34]
def lb579 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def lb648 : List (Nat × Nat × Nat) := [(0,0,1),(3,4,2),(0,0,2),(0,4,2),(0,1,2),(3,7,3)]
def lb571 : BT Decor := buildWiresBT 4 lb579 lb648
def lb573 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def lb575 : BT (List (Nat × Nat)) := btOfList 4 lb573
def lb644 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def lb646 : BT (Option (Nat × Nat)) := btOfList 2 lb644
def lb566 : BT (Option BoundPool) := buildPoolsBT 2 lb571 lb466 lb646 lb93
lemma lb617 : goodPairs lb458 lb635 lb631 := goodPairs_of (by decide +kernel)
lemma lb580 : ∀ x ∈ lb579, faithful lb635 lb631 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb572 : btAll (fun x => faithful lb635 lb631 x ∧ x.1 < 2^128) lb571 := buildWiresBT_faithful lb580
set_option maxRecDepth 500000 in
lemma lb576 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb458 = lb458) lb575 := btAll_ofList (autos_of (by decide +kernel))
lemma lb637 : sliceDirectCheck 0 16 0 lb466 lb458 lb467 lb461 = true := by decide +kernel
lemma lb636 : Slice lb466 lb458 (subcubeFast 0 16) 4 := slice_fast_direct lb637 lb626
lemma lb639 : sliceDirectCheck 0 2 0 lb466 lb458 lb329 lb321 = true := by decide +kernel
lemma lb638 : Slice lb466 lb458 (subcubeFast 0 2) 4 := slice_fast_direct lb639 lb618
lemma lb641 : sliceDirectCheck 0 4 0 lb466 lb458 lb465 lb455 = true := by decide +kernel
lemma lb640 : Slice lb466 lb458 (subcubeFast 0 4) 4 := slice_fast_direct lb641 lb628
lemma lb643 : sliceDirectCheck 0 32 0 lb466 lb458 lb17 lb6 = true := by decide +kernel
lemma lb642 : Slice lb466 lb458 (subcubeFast 0 32) 4 := slice_fast_direct lb643 lb624
set_option maxRecDepth 500000 in
lemma lb647 : btAll (fun o => ∀ p, o = some p → Slice lb466 lb458 p.1 p.2) lb646 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb466 lb458 p.1 p.2) (forall_cons (fun _ h => by cases h; exact lb636) (forall_cons (fun _ h => by cases h; exact lb638) (forall_cons (fun _ h => by cases h; exact lb640) (forall_cons (fun _ h => by cases h; exact lb642) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma lb567 : btAll (fun o => ∀ c, o = some c → ValidPool lb466 lb458 c) lb566 := buildPoolsBT_sound lb647
lemma lb600 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb458 (0 - 1) xs.toFinset) lb243 := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb605 : checkNodesBT lb571 lb458 lb63 lb566 lb575 lb243 0 lb84 = true := by decide +kernel
def lb588 : BT (List (List Nat)) := buildBucketsBT lb571 lb84
set_option maxRecDepth 500000 in
lemma lb589 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb458 0 xs.toFinset) lb588 :=
  buildBucketsBT_sound (by decide) lb617 lb572 lb567 lb576 lb600 lb605
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb606 : checkNodesBT lb571 lb458 lb63 lb566 lb575 lb588 1 lb84 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb590 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb458 1 xs.toFinset) lb588 :=
  buildBucketsBT_sound (by decide) lb617 lb572 lb567 lb576 lb589 lb606
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb607 : checkNodesBT lb571 lb458 lb63 lb566 lb575 lb588 2 lb84 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb591 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb458 2 xs.toFinset) lb588 :=
  buildBucketsBT_sound (by decide) lb617 lb572 lb567 lb576 lb590 lb607
def lb632 : List NodeSpec := [([4,6,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb608 : checkNodesBT lb571 lb458 lb63 lb566 lb575 lb588 3 lb632 = true := by decide +kernel
def lb592 : BT (List (List Nat)) := buildBucketsBT lb571 lb632
set_option maxRecDepth 500000 in
lemma lb593 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb458 3 xs.toFinset) lb592 :=
  buildBucketsBT_sound (by decide) lb617 lb572 lb567 lb576 lb591 lb608
def lb633 : List NodeSpec := [([5,0,1,2,3],[],[]),([4,6,1,2,3],[0,2],[0]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb609 : checkNodesBT lb571 lb458 lb63 lb566 lb575 lb592 4 lb633 = true := by decide +kernel
def lb594 : BT (List (List Nat)) := buildBucketsBT lb571 lb633
set_option maxRecDepth 500000 in
lemma lb595 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb458 4 xs.toFinset) lb594 :=
  buildBucketsBT_sound (by decide) lb617 lb572 lb567 lb576 lb593 lb609
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb610 : checkNodesBT lb571 lb458 lb63 lb566 lb575 lb594 5 lb88 = true := by decide +kernel
def lb596 : BT (List (List Nat)) := buildBucketsBT lb571 lb88
set_option maxRecDepth 500000 in
lemma lb597 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb458 5 xs.toFinset) lb596 :=
  buildBucketsBT_sound (by decide) lb617 lb572 lb567 lb576 lb595 lb610
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb611 : checkNodesBT lb571 lb458 lb63 lb566 lb575 lb596 6 lb89 = true := by decide +kernel
def lb598 : BT (List (List Nat)) := buildBucketsBT lb571 lb89
set_option maxRecDepth 500000 in
lemma lb599 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb458 6 xs.toFinset) lb598 :=
  buildBucketsBT_sound (by decide) lb617 lb572 lb567 lb576 lb597 lb611
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb615 : forestRootCheck lb466 lb458 [(VAR 1,22,20),(VAR 2,22,18),(VAR 4,22,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb614 : bucketContainsBT lb598 lb466 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb619 : Lower lb466 lb458 7 := lower_of_forestBT lb615 lb599 lb614
def lb562 : Nat := 0xfc00c000c0000000fc00c000c0000000
lemma lb621 : liftCheck 0 8 lb221 lb562 lb466 lb458 [(VAR 3,30,22)] = true := by decide +kernel
lemma lb620 : Lower lb221 lb562 8 := lift_of lb621 lb619
def lb563 : Nat := 0xe8008000e8008000e8008000e8008000
def lb568 : List Nat := varsOf 31
lemma lb623 : carryOK [(0,5),(0,4),(0,2),(0,1)] lb568 lb563 lb221 lb562 = true := by decide +kernel
lemma lb622 : Lower lb568 lb563 8 := carry_of lb623 lb620
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q17d : Lower (varsOf 31) 0xa8808000a8808000a8808000a8808000 8 := by
  apply carry_of (swaps := [(2, 3), (1, 2), (0, 1)]) (roots2 := lb568) (T2 := lb563) _ lb622
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q17 : Lower (varsOf 31) 0xfffefeeafffefeeafffefeeafffefeea 8 := dualLower (by decide +kernel) (by decide +kernel) q17d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q18d : Lower (varsOf 31) 0xecc0c000ecc0c000ecc0c000ecc0c000 8 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := lb15) (T2 := lb4) _ lb75
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q18 : Lower (varsOf 31) 0xfffcfcc8fffcfcc8fffcfcc8fffcfcc8 8 := dualLower (by decide +kernel) (by decide +kernel) q18d
def lb649 : Nat := 0xfcc00000fcc00000fcc00000fcc00000
lemma lb706 : liftCheck 0 16 lb218 lb649 lb11 lb0 [(VAR 4,22,6)] = true := by decide +kernel
lemma lb705 : Lower lb218 lb649 5 := lift_of lb706 lb70
lemma lb708 : liftCheck 0 16 lb218 lb207 lb11 lb0 [(VAR 4,22,6)] = true := by decide +kernel
lemma lb707 : Lower lb218 lb207 5 := lift_of lb708 lb70
def lb650 : Nat := 0xfff0ff00fff00000fff0ff00fff00000
def lb719 : List Nat := [20,20,24,24,28,40,40,44,44,52,52,56,20,20,20,24,24,24,40,40,40]
def lb713 : List Nat := [16,4,16,8,12,32,8,36,12,48,36,48,12,36,48,12,36,48,12,36,48]
def lb698 : Nat := fullMask 21
def lb664 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7793,0xdb592),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f89fc,0x49158),(0xffff0000ffff0000ffff0000ffff0000,0x3fe1f,0x124a05),(0xffffffff00000000ffffffff00000000,0x1c0fe0,0x1b6ea0)]
def lb657 : Array Decor := buildWires lb664 lb108
def lb653 : Array (Option BoundPool) := buildPools lb657 lb222 lb104 lb92
lemma lb703 : goodPairs lb650 lb719 lb713 := goodPairs_of (by decide +kernel)
lemma lb665 : ∀ x ∈ lb664, faithful lb719 lb713 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb658 : ∀ x ∈ lb657.toList, faithful lb719 lb713 x ∧ x.1 < 2^128 := buildWires_faithful lb665
lemma lb661 : ∀ sw ∈ lb22.toList, swapsValid sw = true ∧ permWord sw lb650 = lb650 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma lb733 : ∀ i (hi : i < lb104.size), Slice lb222 lb650 lb104[i].1 lb104[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb222 lb650 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb654 : ∀ i (hi : i < lb653.size), ∀ c, lb653[i] = some c → ValidPool lb222 lb650 c := buildPools_sound lb733
lemma lb674 : ∀ i (hi : i < lb36.size), ∀ xs ∈ lb36[i], Impossible lb650 (0 - 1) xs.toFinset := by intro i hi; simp [lb36] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb687 : checkNodes lb657 lb650 lb698 lb653 lb22 lb36 0 lb84 = true := by decide +kernel
def lb668 : Array (List (List Nat)) := buildBuckets 1 lb657 lb84
lemma lb669 : ∀ i (hi : i < lb668.size), ∀ xs ∈ lb668[i], Impossible lb650 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb703 lb658 lb654 lb661 lb674 lb687
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb688 : checkNodes lb657 lb650 lb698 lb653 lb22 lb668 1 lb84 = true := by decide +kernel
lemma lb670 : ∀ i (hi : i < lb668.size), ∀ xs ∈ lb668[i], Impossible lb650 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb703 lb658 lb654 lb661 lb669 lb688
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb689 : checkNodes lb657 lb650 lb698 lb653 lb22 lb668 2 lb84 = true := by decide +kernel
lemma lb671 : ∀ i (hi : i < lb668.size), ∀ xs ∈ lb668[i], Impossible lb650 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb703 lb658 lb654 lb661 lb670 lb689
def lb715 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb690 : checkNodes lb657 lb650 lb698 lb653 lb22 lb668 3 lb715 = true := by decide +kernel
def lb672 : Array (List (List Nat)) := buildBuckets 1 lb657 lb715
lemma lb673 : ∀ i (hi : i < lb672.size), ∀ xs ∈ lb672[i], Impossible lb650 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb703 lb658 lb654 lb661 lb671 lb690
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb700 : forestRootCheck lb222 lb650 [(VAR 2,20,16),(VAR 3,24,16),(VAR 4,20,4),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb699 : bucketContains lb672 lb222 = true := by decide +kernel
lemma lb709 : Lower lb222 lb650 4 := lower_of_forest lb700 lb673 lb699
def lb651 : Nat := 0xffccff00ffcc0000ffccff00ffcc0000
lemma lb711 : carryOK [(1,2)] lb220 lb651 lb222 lb650 = true := by decide +kernel
lemma lb710 : Lower lb220 lb651 4 := carry_of lb711 lb709
def lb652 : Nat := 0xfcc0fc00fcc00000fcc0fc00fcc00000
def lb720 : List Nat := [22,22,22,26,26,26,28,28,28,30,42,42,42,44,44,44,46,46,54,54,54,58,58,60,60,22,22,22,22,22,26,26,26,26,26,28,28,28,28,28,42,42,42,42,42,44,44,44,44,44]
def lb714 : List Nat := [20,18,6,24,18,10,24,20,12,14,40,34,10,40,36,12,38,14,52,50,38,56,50,56,52,14,38,50,52,56,14,38,50,52,56,14,38,50,52,56,14,38,50,52,56,14,38,50,52,56]
def lb666 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1f07fe7f1e3f,0xe739ce5b1a36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3e0f83f9fe3c7,0x16b5ad717c385),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffffc1e3fff8,0x2318c62a2b768),(0xffff0000ffff0000ffff0000ffff0000,0xfffffc03ff,0x39ce739ec00db),(0xffffffff00000000ffffffff00000000,0x3ff0001fffc00,0x3def7bdfd6c00)]
def lb736 : List (Nat × Nat × Nat) := [(2,0,2),(0,0,2),(0,0,1),(3,6,1)]
def lb659 : Array Decor := buildWires lb666 lb736
def lb662 : Array (List (Nat × Nat)) := #[[],[(1,2)]]
def lb732 : List (Nat × Nat) := [(subcube 0 32,5),(subcube 32 0,5),(subcube 0 2,4),(subcube 0 4,4),(subcube 0 48,4)]
def lb734 : Array (Nat × Nat) := lb732.toArray
def lb721 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def lb655 : Array (Option BoundPool) := buildPools lb659 lb221 lb734 lb721
lemma lb704 : goodPairs lb652 lb720 lb714 := goodPairs_of (by decide +kernel)
lemma lb667 : ∀ x ∈ lb666, faithful lb720 lb714 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb660 : ∀ x ∈ lb659.toList, faithful lb720 lb714 x ∧ x.1 < 2^128 := buildWires_faithful lb667
lemma lb663 : ∀ sw ∈ lb662.toList, swapsValid sw = true ∧ permWord sw lb652 = lb652 := autos_of (by decide +kernel)
lemma lb723 : sliceDirectCheck 0 32 0 lb221 lb652 lb218 lb207 = true := by decide +kernel
lemma lb722 : Slice lb221 lb652 (subcube 0 32) 5 := slice_direct lb723 lb707
lemma lb725 : sliceDirectCheck 32 0 0 lb221 lb652 lb218 lb649 = true := by decide +kernel
lemma lb724 : Slice lb221 lb652 (subcube 32 0) 5 := slice_direct lb725 lb705
lemma lb727 : sliceDirectCheck 0 2 0 lb221 lb652 lb222 lb650 = true := by decide +kernel
lemma lb726 : Slice lb221 lb652 (subcube 0 2) 4 := slice_direct lb727 lb709
lemma lb729 : sliceDirectCheck 0 4 0 lb221 lb652 lb220 lb651 = true := by decide +kernel
lemma lb728 : Slice lb221 lb652 (subcube 0 4) 4 := slice_direct lb729 lb710
lemma lb731 : sliceDirectCheck 0 48 0 lb221 lb652 lb11 lb0 = true := by decide +kernel
lemma lb730 : Slice lb221 lb652 (subcube 0 48) 4 := slice_direct lb731 lb70
set_option maxRecDepth 200000 in
lemma lb735 : ∀ i (hi : i < lb734.size), Slice lb221 lb652 lb734[i].1 lb734[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb221 lb652 p.1 p.2) (forall_cons lb722 (forall_cons lb724 (forall_cons lb726 (forall_cons lb728 (forall_cons lb730 (fun _ h => (List.not_mem_nil h).elim))))))
lemma lb656 : ∀ i (hi : i < lb655.size), ∀ c, lb655[i] = some c → ValidPool lb221 lb652 c := buildPools_sound lb735
lemma lb686 : ∀ i (hi : i < lb36.size), ∀ xs ∈ lb36[i], Impossible lb652 (0 - 1) xs.toFinset := by intro i hi; simp [lb36] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb691 : checkNodes lb659 lb652 lb271 lb655 lb662 lb36 0 lb84 = true := by decide +kernel
def lb675 : Array (List (List Nat)) := buildBuckets 1 lb659 lb84
lemma lb676 : ∀ i (hi : i < lb675.size), ∀ xs ∈ lb675[i], Impossible lb652 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb704 lb660 lb656 lb663 lb686 lb691
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb692 : checkNodes lb659 lb652 lb271 lb655 lb662 lb675 1 lb84 = true := by decide +kernel
lemma lb677 : ∀ i (hi : i < lb675.size), ∀ xs ∈ lb675[i], Impossible lb652 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb704 lb660 lb656 lb663 lb676 lb692
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb693 : checkNodes lb659 lb652 lb271 lb655 lb662 lb675 2 lb84 = true := by decide +kernel
lemma lb678 : ∀ i (hi : i < lb675.size), ∀ xs ∈ lb675[i], Impossible lb652 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb704 lb660 lb656 lb663 lb677 lb693
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb694 : checkNodes lb659 lb652 lb271 lb655 lb662 lb675 3 lb84 = true := by decide +kernel
lemma lb679 : ∀ i (hi : i < lb675.size), ∀ xs ∈ lb675[i], Impossible lb652 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb704 lb660 lb656 lb663 lb678 lb694
def lb716 : List NodeSpec := [([8,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb695 : checkNodes lb659 lb652 lb271 lb655 lb662 lb675 4 lb716 = true := by decide +kernel
def lb680 : Array (List (List Nat)) := buildBuckets 1 lb659 lb716
lemma lb681 : ∀ i (hi : i < lb680.size), ∀ xs ∈ lb680[i], Impossible lb652 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb704 lb660 lb656 lb663 lb679 lb695
def lb717 : List NodeSpec := [([5,0,1,2,3,4],[0,1,2],[]),([6,0,1,2,3,4],[3],[0]),([7,0,1,2,3,4],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb696 : checkNodes lb659 lb652 lb271 lb655 lb662 lb680 5 lb717 = true := by decide +kernel
def lb682 : Array (List (List Nat)) := buildBuckets 2 lb659 lb717
lemma lb683 : ∀ i (hi : i < lb682.size), ∀ xs ∈ lb682[i], Impossible lb652 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb704 lb660 lb656 lb663 lb681 lb696
def lb718 : List NodeSpec := [([0,1,2,3,4],[2,3,4,1],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb697 : checkNodes lb659 lb652 lb271 lb655 lb662 lb682 6 lb718 = true := by decide +kernel
def lb684 : Array (List (List Nat)) := buildBuckets 1 lb659 lb718
lemma lb685 : ∀ i (hi : i < lb684.size), ∀ xs ∈ lb684[i], Impossible lb652 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb704 lb660 lb656 lb663 lb683 lb697
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb702 : forestRootCheck lb221 lb652 [(VAR 1,22,20),(VAR 2,22,18),(VAR 3,26,18),(VAR 4,22,6),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb701 : bucketContains lb684 lb221 = true := by decide +kernel
lemma lb712 : Lower lb221 lb652 7 := lower_of_forest lb702 lb685 lb701
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q19d : Lower (varsOf 59) 0xeecccc00aa888800eecccc00aa888800 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := lb221) (T2 := lb652) _ lb712
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q19 : Lower (varsOf 59) 0xffeeeeaaffcccc88ffeeeeaaffcccc88 7 := dualLower (by decide +kernel) (by decide +kernel) q19d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q20d : Lower (varsOf 55) 0xececc0c0a8a88080ececc0c0a8a88080 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (0, 1), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := lb221) (T2 := lb652) _ lb712
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q20 : Lower (varsOf 55) 0xfefeeaeafcfcc8c8fefeeaeafcfcc8c8 7 := dualLower (by decide +kernel) (by decide +kernel) q20d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q21d : Lower (varsOf 47) 0xecc0ecc0a880a880ecc0ecc0a880a880 7 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := lb221) (T2 := lb652) _ lb712
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q21 : Lower (varsOf 47) 0xfeeafeeafcc8fcc8feeafeeafcc8fcc8 7 := dualLower (by decide +kernel) (by decide +kernel) q21d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q22d : Lower (varsOf 30) 0xfcc0c000fcc0c000fcc0c000fcc0c000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5)]) (roots2 := lb222) (T2 := lb322) _ lb382
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q22 : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := dualLower (by decide +kernel) (by decide +kernel) q22d
def lb754 : List Nat := [18,20,6,6,20,18]
def lb749 : List Nat := [16,16,2,4,4,2]
def lb748 : Nat := fullMask 6
def lb740 : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def lb757 : BT Decor := buildWiresBT 2 lb740 lb108
def lb737 : List (List (Nat × Nat)) := [[]]
def lb738 : BT (List (Nat × Nat)) := btOfList 1 lb737
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb751 : goodPairs lb6 lb754 lb749 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb741 : ∀ x ∈ lb740, faithful lb754 lb749 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb758 : btAll (fun x => faithful lb754 lb749 x ∧ x.1 < 2^128) lb757 := buildWiresBT_faithful lb741
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb739 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb6 = lb6) lb738 := btAll_ofList (autos_of (by decide +kernel))
def lb752 : BT (Option BoundPool) := buildPoolsBT 1 lb757 lb17 lb314 lb92
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb755 : btAll (fun o => ∀ p, o = some p → Slice lb17 lb6 p.1 p.2) lb314 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb17 lb6 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb753 : btAll (fun o => ∀ c, o = some c → ValidPool lb17 lb6 c) lb752 := buildPoolsBT_sound lb755
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb747 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb6 (3 - 1) xs.toFinset) lb243 := trivial
def lb742 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb756 : checkNodesBT lb757 lb6 lb748 lb752 lb738 lb243 3 lb742 = true := by decide +kernel
def lb750 : List NodeSpec := lb742
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb746 : checkNodesBT lb757 lb6 lb748 lb752 lb738 lb243 3 lb750 = true := lb756
def lb744 : BT (List (List Nat)) := buildBucketsBT lb757 lb750
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb745 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb6 3 xs.toFinset) lb744 := buildBucketsBT_sound (by decide) lb751 lb758 lb753 lb739 lb747 lb746
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb743 : Lower lb17 lb6 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 4,2,18)]) (by decide +kernel) lb745 (by decide +kernel)
def lb760 : Nat := 0xfefeeaeafcfcc0c0fefeeaeafcfcc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb759 : Lower lb15 lb760 6 := lift_of (z := 1) (o := 32) (essPairs := [(VAR 0,32,33),(VAR 5,1,33)]) (by decide +kernel) lb743
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q23 : Lower (varsOf 61) 0xfffafaaafff0f000fffafaaafff0f000 6 := by
  apply carry_of (swaps := [(2, 3), (1, 2)]) (roots2 := lb15) (T2 := lb760) _ lb759
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q24d : Lower (varsOf 23) 0xa8a88080a8a88080a8a88080a8a88080 5 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (1, 2), (0, 1)]) (roots2 := lb218) (T2 := lb397) _ lb420
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q24 : Lower (varsOf 23) 0xfefeeaeafefeeaeafefeeaeafefeeaea 5 := dualLower (by decide +kernel) (by decide +kernel) q24d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q25d : Lower (varsOf 23) 0xececc0c0ececc0c0ececc0c0ececc0c0 5 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (3, 4), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := lb431) (T2 := lb427) _ lb449
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q25 : Lower (varsOf 23) 0xfcfcc8c8fcfcc8c8fcfcc8c8fcfcc8c8 5 := dualLower (by decide +kernel) (by decide +kernel) q25d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q26 : Lower (varsOf 51) 0xeeeeaaaacccc8888eeeeaaaacccc8888 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb222) (T2 := lb650) _ lb709
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q27 : Lower (varsOf 43) 0xeeaaeeaacc88cc88eeaaeeaacc88cc88 4 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb222) (T2 := lb650) _ lb709
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q28 : Lower (varsOf 39) 0xeaeaeaeac8c8c8c8eaeaeaeac8c8c8c8 4 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb222) (T2 := lb650) _ lb709
  decide +kernel
def s1NR : List Nat := varsOf 63
def s1NG : Nat := 0xfffefeeafffcfcc8fffefeeafffcfcc8
def s1NPos : List Nat := [3,3,3,3,6,6,6,7,10,10,10,11,12,12,12,13,13,14,14,18,18,20,20,21,21,22,22,24,24,25,26,33,33,37,37,38,38,41,41,42,42,44,44,49,49,50,50,52,52,56]
def s1NNeg : List Nat := [1,2,5,9,0,2,4,5,0,2,8,9,0,2,8,5,9,2,8,2,16,4,16,5,17,2,4,8,16,17,2,1,32,5,36,34,36,9,40,34,40,36,40,17,48,34,48,36,48,48]
def s1NMask : Nat := fullMask 50
def s1NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1867a181888f,0x822a181888d),(0xcccccccccccccccccccccccccccccccc,0x6198461e0fff,0x2088420a2222),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1861e07e7f0f0,0x821604a080c4),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x207e07807ff00,0x56008054c08),(0xffff0000ffff0000ffff0000ffff0000,0x3f8007ff80000,0x3580031500000),(0xffffffff00000000ffffffff00000000,0x3ffff80000000,0x3f7dd00000000)]
def s1NSteps : List (Nat × Nat × Nat) := [(1,1,2),(1,1,3),(1,2,3),(3,2,7),(2,6,3),(1,6,4),(2,6,4),(1,7,4),(2,7,4),(1,8,4),(2,8,4),(1,2,4),(1,3,4),(2,1,3),(1,19,4),(3,3,17),(1,1,4),(2,1,4),(1,6,3),(0,24,4),(2,24,4),(1,24,4),(3,2,27),(3,3,27),(1,10,4),(2,10,4),(2,1,2),(1,32,3),(1,33,4),(2,33,4),(1,32,4),(3,2,18),(2,1,8),(1,38,2),(3,1,8),(1,40,4),(3,1,17),(3,1,18),(3,1,15),(1,16,1)]
def s1NW : BT Decor := buildWiresBT 6 s1NBase s1NSteps
def s1NAutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(2,3)],[(2,3),(3,4)],[(2,4),(3,4)],[(2,4)]]
def s1NAutos : BT (List (Nat × Nat)) := btOfList 3 s1NAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NPairs : goodPairs s1NG s1NPos s1NNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBaseOk : ∀ x ∈ s1NBase, faithful s1NPos s1NNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NWOk : btAll (fun x => faithful s1NPos s1NNeg x ∧ x.1 < 2^128) s1NW := buildWiresBT_faithful s1NBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw s1NG = s1NG) s1NAutos := btAll_ofList (autos_of (by decide +kernel))
def s1NSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 32,8),some (subcubeFast 32 0,8),some (subcubeFast 4 0,7),some (subcubeFast 8 0,7),some (subcubeFast 16 0,7),some (subcubeFast 1 32,7),some (subcubeFast 2 0,6),some (subcubeFast 2 1,5),some (subcubeFast 8 32,5),some (subcubeFast 40 0,5),some (subcubeFast 12 0,4),some (subcubeFast 20 0,4),some (subcubeFast 24 0,4),some (subcubeFast 3 32,4)]
def s1NSlices : BT (Option (Nat × Nat)) := btOfList 4 s1NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice0 : Slice s1NR s1NG (subcubeFast 0 32) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfffefeeafffefeeafffefeeafffefeea) (by decide +kernel) q17
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice1 : Slice s1NR s1NG (subcubeFast 32 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfffcfcc8fffcfcc8fffcfcc8fffcfcc8) (by decide +kernel) q18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice2 : Slice s1NR s1NG (subcubeFast 4 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeeeaaffcccc88ffeeeeaaffcccc88) (by decide +kernel) q19
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice3 : Slice s1NR s1NG (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeeaeafcfcc8c8fefeeaeafcfcc8c8) (by decide +kernel) q20
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice4 : Slice s1NR s1NG (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfeeafeeafcc8fcc8feeafeeafcc8fcc8) (by decide +kernel) q21
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice5 : Slice s1NR s1NG (subcubeFast 1 32) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0) (by decide +kernel) q22
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice6 : Slice s1NR s1NG (subcubeFast 2 0) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafaaafff0f000fffafaaafff0f000) (by decide +kernel) q23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice7 : Slice s1NR s1NG (subcubeFast 2 1) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 60) (qGoal := 0xfffffffffff0f000fffffffffff0f000) (by decide +kernel) q6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice8 : Slice s1NR s1NG (subcubeFast 8 32) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 23) (qGoal := 0xfefeeaeafefeeaeafefeeaeafefeeaea) (by decide +kernel) q24
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice9 : Slice s1NR s1NG (subcubeFast 40 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 23) (qGoal := 0xfcfcc8c8fcfcc8c8fcfcc8c8fcfcc8c8) (by decide +kernel) q25
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice10 : Slice s1NR s1NG (subcubeFast 12 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 51) (qGoal := 0xeeeeaaaacccc8888eeeeaaaacccc8888) (by decide +kernel) q26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice11 : Slice s1NR s1NG (subcubeFast 20 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xeeaaeeaacc88cc88eeaaeeaacc88cc88) (by decide +kernel) q27
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice12 : Slice s1NR s1NG (subcubeFast 24 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 39) (qGoal := 0xeaeaeaeac8c8c8c8eaeaeaeac8c8c8c8) (by decide +kernel) q28
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice13 : Slice s1NR s1NG (subcubeFast 3 32) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) q10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s1NR s1NG p.1 p.2) s1NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s1NR s1NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s1NSlice0) (forall_cons (fun _ h => by cases h; exact s1NSlice1) (forall_cons (fun _ h => by cases h; exact s1NSlice2) (forall_cons (fun _ h => by cases h; exact s1NSlice3) (forall_cons (fun _ h => by cases h; exact s1NSlice4) (forall_cons (fun _ h => by cases h; exact s1NSlice5) (forall_cons (fun _ h => by cases h; exact s1NSlice6) (forall_cons (fun _ h => by cases h; exact s1NSlice7) (forall_cons (fun _ h => by cases h; exact s1NSlice8) (forall_cons (fun _ h => by cases h; exact s1NSlice9) (forall_cons (fun _ h => by cases h; exact s1NSlice10) (forall_cons (fun _ h => by cases h; exact s1NSlice11) (forall_cons (fun _ h => by cases h; exact s1NSlice12) (forall_cons (fun _ h => by cases h; exact s1NSlice13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
def s1NEmpty : BT (List (List Nat)) := BT.empty
lemma s1NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG (5 - 1) xs.toFinset) s1NEmpty := trivial
def s1NBlock5_0Specs : List PoolSpec := []
def s1NBlock5_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock5_0Specs
def s1NBlock5_0 : List NodeSpec := [([12,0,7,8,4,5],[],[]),([16,0,6,7,4,5],[],[]),([19,21,0,6,4,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock5_0Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock5_0Pools s1NAutos s1NEmpty 5 s1NBlock5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock5_0Mem : ∀ ns ∈ s1NBlock5_0, Impossible s1NG 5 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NEmptyOk s1NBlock5_0Ok
def s1NBlock5_1Specs : List PoolSpec := []
def s1NBlock5_1Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock5_1Specs
def s1NBlock5_1 : List NodeSpec := [([10,0,1,2,25,5],[],[]),([28,0,1,3,4,5],[],[]),([40,0,1,17,18,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock5_1Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock5_1Pools s1NAutos s1NEmpty 5 s1NBlock5_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock5_1Mem : ∀ ns ∈ s1NBlock5_1, Impossible s1NG 5 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NEmptyOk s1NBlock5_1Ok
def s1NBlock5_2Specs : List PoolSpec := [(3,[])]
def s1NBlock5_2Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock5_2Specs
def s1NBlock5_2 : List NodeSpec := [([0,1,8,11,18,5],[0],[]),([0,6,3,20,17,5],[],[]),([0,6,7,4,15,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock5_2Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock5_2Pools s1NAutos s1NEmpty 5 s1NBlock5_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock5_2Mem : ∀ ns ∈ s1NBlock5_2, Impossible s1NG 5 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NEmptyOk s1NBlock5_2Ok
def s1NBlock5_3Specs : List PoolSpec := [(3,[])]
def s1NBlock5_3Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock5_3Specs
def s1NBlock5_3 : List NodeSpec := [([0,6,7,17,18,5],[],[]),([0,7,8,4,11,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock5_3Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock5_3Pools s1NAutos s1NEmpty 5 s1NBlock5_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock5_3Mem : ∀ ns ∈ s1NBlock5_3, Impossible s1NG 5 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NEmptyOk s1NBlock5_3Ok
def s1NNodes5 : List NodeSpec := s1NBlock5_0 ++ s1NBlock5_1 ++ s1NBlock5_2 ++ s1NBlock5_3
def s1NBucket5 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 5 xs.toFinset) s1NBucket5 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append s1NBlock5_0Mem s1NBlock5_1Mem) s1NBlock5_2Mem) s1NBlock5_3Mem)
def s1NBlock6_0Specs : List PoolSpec := [(3,[(1,1,2),(2,6,4)]),(4,[(1,1,2),(2,6,3)])]
def s1NBlock6_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock6_0Specs
def s1NBlock6_0 : List NodeSpec := [([31,0,1,2,3,4,5],[1],[]),([12,19,0,2,3,4,5],[],[]),([12,0,1,3,8,4,5],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_0Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_0Pools s1NAutos s1NBucket5 6 s1NBlock6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_0Mem : ∀ ns ∈ s1NBlock6_0, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_0Ok
def s1NBlock6_1Specs : List PoolSpec := [(3,[(1,1,2),(2,6,4)])]
def s1NBlock6_1Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock6_1Specs
def s1NBlock6_1 : List NodeSpec := [([12,0,2,3,7,4,5],[0],[0]),([35,0,1,2,3,4,5],[],[]),([16,0,1,6,3,4,5],[],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_1Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_1Pools s1NAutos s1NBucket5 6 s1NBlock6_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_1Mem : ∀ ns ∈ s1NBlock6_1, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_1Ok
def s1NBlock6_2Specs : List PoolSpec := [(12,[]),(2,[(1,1,8),(2,24,4)])]
def s1NBlock6_2Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock6_2Specs
def s1NBlock6_2 : List NodeSpec := [([26,0,1,2,6,3,5],[],[]),([26,0,1,2,3,8,5],[1],[]),([26,0,1,2,3,24,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_2Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_2Pools s1NAutos s1NBucket5 6 s1NBlock6_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_2Mem : ∀ ns ∈ s1NBlock6_2, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_2Ok
def s1NBlock6_3Specs : List PoolSpec := [(3,[]),(5,[(1,1,2),(1,6,3),(2,24,4)]),(1,[(1,1,2),(1,6,3),(2,24,4)])]
def s1NBlock6_3Pools : BT (Option BoundPool) := buildPoolsBT 2 s1NW s1NR s1NSlices s1NBlock6_3Specs
def s1NBlock6_3 : List NodeSpec := [([26,0,1,2,3,4,5],[],[]),([26,0,1,2,3,5],[1,2],[]),([19,0,2,3,4,11,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_3Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_3Pools s1NAutos s1NBucket5 6 s1NBlock6_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_3Mem : ∀ ns ∈ s1NBlock6_3, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_3Ok
def s1NBlock6_4Specs : List PoolSpec := [(2,[]),(10,[])]
def s1NBlock6_4Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock6_4Specs
def s1NBlock6_4 : List NodeSpec := [([19,0,6,3,4,17,5],[],[0]),([10,0,1,2,24,4,5],[0],[0]),([10,0,1,6,8,4,5],[1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_4Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_4Pools s1NAutos s1NBucket5 6 s1NBlock6_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_4Mem : ∀ ns ∈ s1NBlock6_4, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_4Ok
def s1NBlock6_5Specs : List PoolSpec := [(2,[])]
def s1NBlock6_5Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock6_5Specs
def s1NBlock6_5 : List NodeSpec := [([32,37,0,1,3,4,5],[],[0,2,3]),([9,0,1,6,3,4,5],[0],[]),([9,0,1,3,8,4,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_5Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_5Pools s1NAutos s1NBucket5 6 s1NBlock6_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_5Mem : ∀ ns ∈ s1NBlock6_5, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_5Ok
def s1NBlock6_6Specs : List PoolSpec := [(6,[]),(10,[]),(0,[(1,2,3),(1,8,4),(3,1,15)])]
def s1NBlock6_6Pools : BT (Option BoundPool) := buildPoolsBT 2 s1NW s1NR s1NSlices s1NBlock6_6Specs
def s1NBlock6_6 : List NodeSpec := [([9,0,6,3,7,4,5],[0],[]),([40,0,1,3,4,17,5],[1],[0]),([44,0,1,2,3,4,5],[2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_6Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_6Pools s1NAutos s1NBucket5 6 s1NBlock6_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_6Mem : ∀ ns ∈ s1NBlock6_6, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_6Ok
def s1NBlock6_7Specs : List PoolSpec := [(12,[])]
def s1NBlock6_7Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock6_7Specs
def s1NBlock6_7 : List NodeSpec := [([0,1,45,2,3,4,5],[],[3]),([0,1,2,3,25,24,5],[],[0,2,3]),([0,1,2,3,24,4,5],[0],[3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_7Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_7Pools s1NAutos s1NBucket5 6 s1NBlock6_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_7Mem : ∀ ns ∈ s1NBlock6_7, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_7Ok
def s1NBlock6_8Specs : List PoolSpec := [(4,[(1,1,2),(2,6,3)])]
def s1NBlock6_8Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock6_8Specs
def s1NBlock6_8 : List NodeSpec := [([0,1,2,3,4,30,5],[0],[]),([0,1,2,3,4,41,5],[],[]),([0,1,2,3,4,34,5],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_8Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_8Pools s1NAutos s1NBucket5 6 s1NBlock6_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_8Mem : ∀ ns ∈ s1NBlock6_8, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_8Ok
def s1NBlock6_9Specs : List PoolSpec := [(2,[]),(12,[])]
def s1NBlock6_9Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock6_9Specs
def s1NBlock6_9 : List NodeSpec := [([0,1,2,3,4,27,5],[],[0,2,3]),([0,1,2,33,4,18,5],[1],[3]),([0,1,39,3,8,4,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_9Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_9Pools s1NAutos s1NBucket5 6 s1NBlock6_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_9Mem : ∀ ns ∈ s1NBlock6_9, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_9Ok
def s1NBlock6_10Specs : List PoolSpec := [(6,[]),(2,[]),(0,[(1,1,2),(1,1,3),(1,2,3)]),(1,[(1,1,2),(1,1,3),(1,2,3)]),(12,[])]
def s1NBlock6_10Pools : BT (Option BoundPool) := buildPoolsBT 3 s1NW s1NR s1NSlices s1NBlock6_10Specs
def s1NBlock6_10 : List NodeSpec := [([0,1,6,3,4,15,5],[0],[0,1]),([0,1,6,7,8,4,5],[0,1,2,3],[]),([0,1,6,8,4,18,5],[4],[0,1,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_10Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_10Pools s1NAutos s1NBucket5 6 s1NBlock6_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_10Mem : ∀ ns ∈ s1NBlock6_10, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_10Ok
def s1NBlock6_11Specs : List PoolSpec := [(3,[]),(4,[(1,2,3)]),(2,[(1,3,4)]),(5,[(1,2,3),(1,2,4),(1,3,4)]),(1,[(1,2,3),(1,2,4),(1,3,4)])]
def s1NBlock6_11Pools : BT (Option BoundPool) := buildPoolsBT 3 s1NW s1NR s1NSlices s1NBlock6_11Specs
def s1NBlock6_11 : List NodeSpec := [([0,1,3,8,4,11,5],[0],[0]),([0,1,8,17,18,5],[0,1,2,3,4],[0,1,2,4]),([0,2,6,3,4,20,5],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_11Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_11Pools s1NAutos s1NBucket5 6 s1NBlock6_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_11Mem : ∀ ns ∈ s1NBlock6_11, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_11Ok
def s1NBlock6_12Specs : List PoolSpec := [(2,[(1,1,3)]),(3,[]),(7,[]),(5,[(1,1,2),(1,1,3),(1,2,3)])]
def s1NBlock6_12Pools : BT (Option BoundPool) := buildPoolsBT 2 s1NW s1NR s1NSlices s1NBlock6_12Specs
def s1NBlock6_12 : List NodeSpec := [([0,2,3,7,4,11,5],[1],[0,5]),([0,6,3,7,4,17,5],[],[0,3]),([0,6,7,8,4,5],[0,1,2,3],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_12Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_12Pools s1NAutos s1NBucket5 6 s1NBlock6_12 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_12Mem : ∀ ns ∈ s1NBlock6_12, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_12Ok
def s1NNodes6 : List NodeSpec := s1NBlock6_0 ++ s1NBlock6_1 ++ s1NBlock6_2 ++ s1NBlock6_3 ++ s1NBlock6_4 ++ s1NBlock6_5 ++ s1NBlock6_6 ++ s1NBlock6_7 ++ s1NBlock6_8 ++ s1NBlock6_9 ++ s1NBlock6_10 ++ s1NBlock6_11 ++ s1NBlock6_12
def s1NBucket6 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 6 xs.toFinset) s1NBucket6 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append s1NBlock6_0Mem s1NBlock6_1Mem) s1NBlock6_2Mem) s1NBlock6_3Mem) s1NBlock6_4Mem) s1NBlock6_5Mem) s1NBlock6_6Mem) s1NBlock6_7Mem) s1NBlock6_8Mem) s1NBlock6_9Mem) s1NBlock6_10Mem) s1NBlock6_11Mem) s1NBlock6_12Mem)
def s1NBlock7_0Specs : List PoolSpec := [(6,[]),(7,[]),(3,[(1,1,2)]),(10,[]),(2,[(2,1,3)]),(8,[]),(9,[]),(4,[(1,2,3)]),(2,[(2,1,8)]),(5,[(1,2,3),(2,8,4)]),(1,[(1,2,3),(2,8,4)])]
def s1NBlock7_0Pools : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NBlock7_0Specs
def s1NBlock7_0 : List NodeSpec := [([16,0,1,2,3,4,5],[0,3,7,9,10],[0,2,3]),([38,0,1,2,3,8,4,5],[3,5,6,8],[0,2]),([19,0,2,6,3,4,5],[1,2,3,4],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_0Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock7_0Pools s1NAutos s1NBucket6 7 s1NBlock7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_0Mem : ∀ ns ∈ s1NBlock7_0, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket6Ok s1NBlock7_0Ok
def s1NBlock7_1Specs : List PoolSpec := [(6,[]),(2,[]),(3,[(1,1,2)]),(12,[]),(4,[(1,1,2),(2,6,3)]),(5,[(1,1,2),(2,6,3)]),(2,[(2,6,3)]),(1,[(1,1,2),(2,6,3)]),(3,[(2,1,2)]),(8,[]),(9,[])]
def s1NBlock7_1Pools : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NBlock7_1Specs
def s1NBlock7_1 : List NodeSpec := [([10,0,1,2,6,3,4,5],[0,1,2],[0,2]),([10,0,1,2,3,4,5],[2,4,5,6,7],[0,1,2]),([32,0,1,2,3,4,18,5],[0,1,3,8,9,10],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_1Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock7_1Pools s1NAutos s1NBucket6 7 s1NBlock7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_1Mem : ∀ ns ∈ s1NBlock7_1, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket6Ok s1NBlock7_1Ok
def s1NBlock7_2Specs : List PoolSpec := [(6,[]),(2,[(1,1,3)]),(3,[]),(0,[(1,1,2),(1,1,3)]),(1,[(1,1,2),(1,1,3)]),(3,[(1,1,2)]),(10,[]),(12,[]),(4,[(1,1,2)]),(5,[(1,2,3),(3,1,8)]),(1,[(1,2,3),(3,1,8)])]
def s1NBlock7_2Pools : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NBlock7_2Specs
def s1NBlock7_2 : List NodeSpec := [([40,0,1,2,3,4,5],[6,7,9,10],[0,2]),([0,1,2,6,3,7,4,5],[0,1,2,3,4],[0,2]),([0,1,2,6,3,24,4,5],[5,6,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_2Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock7_2Pools s1NAutos s1NBucket6 7 s1NBlock7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_2Mem : ∀ ns ∈ s1NBlock7_2, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket6Ok s1NBlock7_2Ok
def s1NBlock7_3Specs : List PoolSpec := [(6,[]),(2,[]),(3,[(1,1,2)]),(10,[]),(12,[]),(13,[]),(2,[(1,32,3)]),(3,[(2,1,2)]),(2,[(1,1,8)]),(4,[(1,2,3)])]
def s1NBlock7_3Pools : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NBlock7_3Specs
def s1NBlock7_3 : List NodeSpec := [([0,1,2,6,3,4,18,5],[0,1,2,4],[0,1,2,3,4,5]),([0,1,2,3,33,4,5],[4,5,6,7],[0,3]),([0,1,2,3,8,24,4,5],[0,3,8,9],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_3Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock7_3Pools s1NAutos s1NBucket6 7 s1NBlock7_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_3Mem : ∀ ns ∈ s1NBlock7_3, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket6Ok s1NBlock7_3Ok
def s1NBlock7_4Specs : List PoolSpec := [(6,[]),(3,[(1,1,2)]),(10,[]),(12,[]),(4,[(1,1,2)]),(5,[(1,1,2),(1,6,3)]),(2,[(1,6,3)]),(1,[(1,1,2),(1,6,3)]),(4,[(1,2,3)]),(11,[]),(2,[(1,8,4)]),(5,[(1,2,3),(1,8,4)]),(3,[(1,8,4)]),(1,[(1,2,3),(1,8,4)])]
def s1NBlock7_4Pools : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NBlock7_4Specs
def s1NBlock7_4 : List NodeSpec := [([0,1,2,3,8,4,15,5],[2,3,9,10],[]),([0,1,2,3,24,4,5],[1,2,4,5,6,7],[0,1,2,4]),([0,1,2,3,4,15,5],[0,2,3,8,9,10,11,12,13],[0,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_4Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock7_4Pools s1NAutos s1NBucket6 7 s1NBlock7_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_4Mem : ∀ ns ∈ s1NBlock7_4, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket6Ok s1NBlock7_4Ok
def s1NBlock7_5Specs : List PoolSpec := [(2,[]),(2,[(1,1,3)]),(7,[]),(3,[(1,1,2)]),(5,[(1,1,2),(1,1,3)]),(10,[]),(5,[(1,1,2),(1,2,3)]),(1,[(1,1,2),(1,2,3)]),(4,[(1,2,3)]),(3,[(1,2,4)]),(5,[(1,2,3),(1,2,4)]),(11,[]),(1,[(1,2,3),(1,2,4)])]
def s1NBlock7_5Pools : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NBlock7_5Specs
def s1NBlock7_5 : List NodeSpec := [([0,1,6,3,8,4,5],[0,2,3,5,6,7],[0,1]),([0,1,3,8,4,17,5],[0,5,8,9,10,11,12],[0,1,2,3]),([0,2,6,3,7,4,5],[1,2,3,4],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_5Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock7_5Pools s1NAutos s1NBucket6 7 s1NBlock7_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_5Mem : ∀ ns ∈ s1NBlock7_5, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket6Ok s1NBlock7_5Ok
def s1NNodes7 : List NodeSpec := s1NBlock7_0 ++ s1NBlock7_1 ++ s1NBlock7_2 ++ s1NBlock7_3 ++ s1NBlock7_4 ++ s1NBlock7_5
def s1NBucket7 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 7 xs.toFinset) s1NBucket7 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append s1NBlock7_0Mem s1NBlock7_1Mem) s1NBlock7_2Mem) s1NBlock7_3Mem) s1NBlock7_4Mem) s1NBlock7_5Mem)
def s1NBlock8_0Specs : List PoolSpec := [(6,[]),(2,[]),(3,[]),(3,[(1,1,2)]),(10,[]),(4,[(1,1,2)]),(5,[(1,1,2)]),(1,[(1,1,2)]),(13,[]),(3,[(2,1,2)]),(4,[(2,1,2)]),(0,[]),(1,[]),(4,[(1,2,3)]),(5,[(1,2,3)]),(1,[(1,2,3)])]
def s1NBlock8_0Pools : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NBlock8_0Specs
def s1NBlock8_0 : List NodeSpec := [([32,0,1,2,3,4,5],[1,8,9,10,11,12],[0,1,2,3]),([0,1,2,6,3,4,5],[0,1,3,5,6,7],[0,1]),([0,1,2,3,8,4,5],[0,1,2,4,13,14,15],[0,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock8_0Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock8_0Pools s1NAutos s1NBucket7 8 s1NBlock8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock8_0Mem : ∀ ns ∈ s1NBlock8_0, Impossible s1NG 8 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket7Ok s1NBlock8_0Ok
def s1NNodes8 : List NodeSpec := s1NBlock8_0
def s1NBucket8 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 8 xs.toFinset) s1NBucket8 := buildBucketsBT_of_mem s1NBlock8_0Mem
def s1NBlock9_0Specs : List PoolSpec := [(2,[]),(3,[]),(1,[]),(5,[]),(4,[])]
def s1NBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 3 s1NW s1NR s1NSlices s1NBlock9_0Specs
def s1NBlock9_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4],[0,1,2,3,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock9_0Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock9_0Pools s1NAutos s1NBucket8 9 s1NBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock9_0Mem : ∀ ns ∈ s1NBlock9_0, Impossible s1NG 9 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket8Ok s1NBlock9_0Ok
def s1NNodes9 : List NodeSpec := s1NBlock9_0
def s1NBucket9 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 9 xs.toFinset) s1NBucket9 := buildBucketsBT_of_mem s1NBlock9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBound : Lower s1NR s1NG 10 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,2,6),(VAR 3,2,10),(VAR 4,2,18),(VAR 5,1,33)]) (by decide +kernel) s1NBucket9Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q16 : Lower (varsOf 63) 0xfffffefefefaeca0fffffefefefaeca0 10 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (3, 4), (0, 1)]) (roots2 := s1NR) (T2 := s1NG) _ s1NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q30d : Lower (varsOf 62) 0xfcf0f000ccc0c000fcf0f000ccc0c000 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (1, 2)]) (roots2 := lb221) (T2 := lb652) _ lb712
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q30 : Lower (varsOf 62) 0xfffcfcccfff0f0c0fffcfcccfff0f0c0 7 := dualLower (by decide +kernel) (by decide +kernel) q30d
def lb160 : List Nat := [5,5,9,9,12,12,5,9,12]
def lb157 : List Nat := [4,1,8,1,8,4,8,4,1]
def lb126 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bc,0x54)]
def lb120 : BT Decor := buildWiresBT 2 lb126 lb108
lemma lb143 : goodPairs lb425 lb160 lb157 := goodPairs_of (by decide +kernel)
lemma lb127 : ∀ x ∈ lb126, faithful lb160 lb157 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb121 : btAll (fun x => faithful lb160 lb157 x ∧ x.1 < 2^128) lb120 := buildWiresBT_faithful lb127
set_option maxRecDepth 500000 in
lemma lb124 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb425 = lb425) lb229 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb172 : btAll (fun o => ∀ p, o = some p → Slice lb429 lb425 p.1 p.2) lb314 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb429 lb425 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb130 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb425 2 xs.toFinset) lb243 := trivial
def lb115 : BT (Option BoundPool) := buildPoolsSubBT 1 lb120 lb429 lb314 lb298 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb136 : checkNodesBT lb120 lb425 lb62 lb115 lb229 lb243 3 lb85 = true := by decide +kernel
def lb131 : BT (List (List Nat)) := buildBucketsBT lb120 lb85
set_option maxRecDepth 500000 in
lemma lb132 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb425 3 xs.toFinset) lb131 :=
  buildBucketsBT_sound (by decide) lb143 lb121 (buildPoolsSubBT_sound lb172) lb124 lb130 lb136
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb140 : forestRootCheck lb429 lb425 [(VAR 0,5,4),(VAR 2,5,1),(VAR 3,9,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb139 : bucketContainsBT lb131 lb429 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb145 : Lower lb429 lb425 4 := lower_of_forestBT lb140 lb132 lb139
lemma lb152 : carryOK [(3,4),(1,2)] lb14 lb3 lb429 lb425 = true := by decide +kernel
lemma lb151 : Lower lb14 lb3 4 := carry_of lb152 lb145
def lb113 : Nat := 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8
lemma lb154 : liftCheck 4 0 lb13 lb113 lb14 lb3 [(VAR 2,5,1)] = true := by decide +kernel
lemma lb153 : Lower lb13 lb113 5 := lift_of lb154 lb151
def lb114 : Nat := 0xfaaafaa0faaafaa0faaafaa0faaafaa0
def lb119 : List Nat := varsOf 29
lemma lb156 : liftCheck 16 0 lb119 lb114 lb429 lb425 [(VAR 4,17,1)] = true := by decide +kernel
lemma lb155 : Lower lb119 lb114 5 := lift_of lb156 lb145
def lb110 : Nat := 0xeeeeaa88eeeeaa88eeeeaa88eeeeaa88
def lb117 : List Nat := varsOf 27
lemma lb147 : carryOK [(3,4),(1,2)] lb117 lb110 lb119 lb114 = true := by decide +kernel
lemma lb146 : Lower lb117 lb110 5 := carry_of lb147 lb155
def lb111 : Nat := 0xfae8fae8fae8fae8fae8fae8fae8fae8
def lb118 : List Nat := varsOf 15
lemma lb149 : carryOK [(3,4),(1,2)] lb118 lb111 lb13 lb113 = true := by decide +kernel
lemma lb148 : Lower lb118 lb111 5 := carry_of lb149 lb153
def lb112 : Nat := 0xfeeefae8feeefae8feeefae8feeefae8
def lb161 : List Nat := [3,3,5,5,6,6,9,9,11,12,12,14,17,17,18,18,21,22,25,26,26,28,28,3,3,3,5,5,5,6,6,6,6,9,9,9,12,12,12,12,17,17,17,18,18,18,18]
def lb158 : List Nat := [2,1,4,1,4,2,8,1,10,8,4,10,16,1,16,2,20,20,24,24,10,24,20,10,20,24,10,20,24,1,10,20,24,10,20,24,1,10,20,24,10,20,24,1,10,20,24]
def lb138 : Nat := fullMask 47
def lb128 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x70e1f8531cf,0x8102000208a),(0xcccccccccccccccccccccccccccccccc,0x7801e39ac933,0x112244908921),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf1fc630e3c,0x224489430414),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfe007c0fc0,0x55ab56bc0b40),(0xffff0000ffff0000ffff0000ffff0000,0x7f00007ff000,0x66cd9b6f5000)]
def lb122 : BT Decor := buildWiresBT 3 lb128 lb108
def lb171 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5)]
def lb173 : BT (Option (Nat × Nat)) := btOfList 2 lb171
def lb162 : BT (Option PoolSpec) := btOfList 2 [some (0,[]),some (1,[]),some (2,[]),some (3,[])]
lemma lb144 : goodPairs lb112 lb161 lb158 := goodPairs_of (by decide +kernel)
lemma lb129 : ∀ x ∈ lb128, faithful lb161 lb158 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb123 : btAll (fun x => faithful lb161 lb158 x ∧ x.1 < 2^128) lb122 := buildWiresBT_faithful lb129
set_option maxRecDepth 500000 in
lemma lb125 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb112 = lb112) lb229 := btAll_ofList (autos_of (by decide +kernel))
lemma lb164 : sliceDirectCheck 2 0 0 lb568 lb112 lb119 lb114 = true := by decide +kernel
lemma lb163 : Slice lb568 lb112 (subcubeFast 2 0) 5 := slice_fast_direct lb164 lb155
lemma lb166 : sliceDirectCheck 4 0 0 lb568 lb112 lb117 lb110 = true := by decide +kernel
lemma lb165 : Slice lb568 lb112 (subcubeFast 4 0) 5 := slice_fast_direct lb166 lb146
lemma lb168 : sliceDirectCheck 8 0 0 lb568 lb112 lb13 lb113 = true := by decide +kernel
lemma lb167 : Slice lb568 lb112 (subcubeFast 8 0) 5 := slice_fast_direct lb168 lb153
lemma lb170 : sliceDirectCheck 16 0 0 lb568 lb112 lb118 lb111 = true := by decide +kernel
lemma lb169 : Slice lb568 lb112 (subcubeFast 16 0) 5 := slice_fast_direct lb170 lb148
set_option maxRecDepth 500000 in
lemma lb174 : btAll (fun o => ∀ p, o = some p → Slice lb568 lb112 p.1 p.2) lb173 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb568 lb112 p.1 p.2) (forall_cons (fun _ h => by cases h; exact lb163) (forall_cons (fun _ h => by cases h; exact lb165) (forall_cons (fun _ h => by cases h; exact lb167) (forall_cons (fun _ h => by cases h; exact lb169) (fun _ h => (List.not_mem_nil h).elim)))))
lemma lb133 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb112 5 xs.toFinset) lb243 := trivial
def lb159 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3],[])]
def lb116 : BT (Option BoundPool) := buildPoolsSubBT 2 lb122 lb568 lb173 lb162 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb137 : checkNodesBT lb122 lb112 lb138 lb116 lb229 lb243 6 lb159 = true := by decide +kernel
def lb134 : BT (List (List Nat)) := buildBucketsBT lb122 lb159
set_option maxRecDepth 500000 in
lemma lb135 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb112 6 xs.toFinset) lb134 :=
  buildBucketsBT_sound (by decide) lb144 lb123 (buildPoolsSubBT_sound lb174) lb125 lb133 lb137
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb142 : forestRootCheck lb568 lb112 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,9,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb141 : bucketContainsBT lb134 lb568 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb150 : Lower lb568 lb112 7 := lower_of_forestBT lb142 lb135 lb141
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q31 : Lower (varsOf 55) 0xfefeeeeefafae8e8fefeeeeefafae8e8 7 := by
  apply carry_of (swaps := [(4, 5), (3, 4)]) (roots2 := lb568) (T2 := lb112) _ lb150
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q32 : Lower (varsOf 47) 0xfeeefeeefae8fae8feeefeeefae8fae8 7 := by
  apply carry_of (swaps := [(4, 5)]) (roots2 := lb568) (T2 := lb112) _ lb150
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q33d : Lower (varsOf 30) 0xccc0c000ccc0c000ccc0c000ccc0c000 5 := by
  apply carry_of (swaps := [(2, 3), (1, 2)]) (roots2 := lb218) (T2 := lb397) _ lb420
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q33 : Lower (varsOf 30) 0xfffcfcccfffcfcccfffcfcccfffcfccc 5 := dualLower (by decide +kernel) (by decide +kernel) q33d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q34 : Lower (varsOf 54) 0xfcfcccccf0f0c0c0fcfcccccf0f0c0c0 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3)]) (roots2 := lb222) (T2 := lb650) _ lb709
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q35 : Lower (varsOf 46) 0xfcccfcccf0c0f0c0fcccfcccf0c0f0c0 4 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (1, 2), (2, 3)]) (roots2 := lb222) (T2 := lb650) _ lb709
  decide +kernel
def s2NR : List Nat := varsOf 63
def s2NG : Nat := 0xfffefeeefffafae8fffefeeefffafae8
def s2NPos : List Nat := [3,3,3,3,5,5,6,6,9,9,11,12,12,17,17,19,20,20,24,24,26,26,33,34,41,42,42,44,49,50,50,52,56,56]
def s2NNeg : List Nat := [1,2,10,18,1,4,2,4,1,8,10,4,8,1,16,18,4,16,8,16,10,18,1,2,40,10,40,40,48,18,48,36,40,48]
def s2NMask : Nat := fullMask 34
def s2NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1140e73f,0x402111),(0xcccccccccccccccccccccccccccccccc,0x66b084cf,0x22b0844e),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x880318f0,0x800108a0),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x30f3c1f00,0x10f141604),(0xffff0000ffff0000ffff0000ffff0000,0x3f03fe000,0x2702ac008),(0xffffffff00000000ffffffff00000000,0x3ffc00000,0x3dd000000)]
def s2NSteps : List (Nat × Nat × Nat) := [(1,0,3),(1,0,4),(1,3,4),(1,6,4),(2,6,4)]
def s2NW : BT Decor := buildWiresBT 4 s2NBase s2NSteps
def s2NAutoList : List (List (Nat × Nat)) := [[],[(3,4)]]
def s2NAutos : BT (List (Nat × Nat)) := btOfList 1 s2NAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NPairs : goodPairs s2NG s2NPos s2NNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBaseOk : ∀ x ∈ s2NBase, faithful s2NPos s2NNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NWOk : btAll (fun x => faithful s2NPos s2NNeg x ∧ x.1 < 2^128) s2NW := buildWiresBT_faithful s2NBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw s2NG = s2NG) s2NAutos := btAll_ofList (autos_of (by decide +kernel))
def s2NSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,8),some (subcubeFast 4 0,8),some (subcubeFast 1 0,7),some (subcubeFast 8 0,7),some (subcubeFast 16 0,7),some (subcubeFast 34 0,7),some (subcubeFast 1 32,5),some (subcubeFast 9 0,4),some (subcubeFast 17 0,4),some (subcubeFast 28 0,4)]
def s2NSlices : BT (Option (Nat × Nat)) := btOfList 4 s2NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice0 : Slice s2NR s2NG (subcubeFast 2 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafaaafffafaa0fffafaaafffafaa0) (by decide +kernel) q1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice1 : Slice s2NR s2NG (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeeeeeffaaaa88ffeeeeeeffaaaa88) (by decide +kernel) q2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice2 : Slice s2NR s2NG (subcubeFast 1 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffcfcccfff0f0c0fffcfcccfff0f0c0) (by decide +kernel) q30
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice3 : Slice s2NR s2NG (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeeeeefafae8e8fefeeeeefafae8e8) (by decide +kernel) q31
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice4 : Slice s2NR s2NG (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfeeefeeefae8fae8feeefeeefae8fae8) (by decide +kernel) q32
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice5 : Slice s2NR s2NG (subcubeFast 34 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 29) (qGoal := 0xfffafaa0fffafaa0fffafaa0fffafaa0) (by decide +kernel) q5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice6 : Slice s2NR s2NG (subcubeFast 1 32) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xfffcfcccfffcfcccfffcfcccfffcfccc) (by decide +kernel) q33
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice7 : Slice s2NR s2NG (subcubeFast 9 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 54) (qGoal := 0xfcfcccccf0f0c0c0fcfcccccf0f0c0c0) (by decide +kernel) q34
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice8 : Slice s2NR s2NG (subcubeFast 17 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 46) (qGoal := 0xfcccfcccf0c0f0c0fcccfcccf0c0f0c0) (by decide +kernel) q35
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice9 : Slice s2NR s2NG (subcubeFast 28 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) q9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s2NR s2NG p.1 p.2) s2NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s2NR s2NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s2NSlice0) (forall_cons (fun _ h => by cases h; exact s2NSlice1) (forall_cons (fun _ h => by cases h; exact s2NSlice2) (forall_cons (fun _ h => by cases h; exact s2NSlice3) (forall_cons (fun _ h => by cases h; exact s2NSlice4) (forall_cons (fun _ h => by cases h; exact s2NSlice5) (forall_cons (fun _ h => by cases h; exact s2NSlice6) (forall_cons (fun _ h => by cases h; exact s2NSlice7) (forall_cons (fun _ h => by cases h; exact s2NSlice8) (forall_cons (fun _ h => by cases h; exact s2NSlice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
def s2NEmpty : BT (List (List Nat)) := BT.empty
lemma s2NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG (6 - 1) xs.toFinset) s2NEmpty := trivial
def s2NBlock6_0Specs : List PoolSpec := [(9,[]),(6,[]),(0,[(1,0,3),(1,0,4),(1,3,4)])]
def s2NBlock6_0Pools : BT (Option BoundPool) := buildPoolsBT 2 s2NW s2NR s2NSlices s2NBlock6_0Specs
def s2NBlock6_0 : List NodeSpec := [([1,2,6,7,8,5],[0,1,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock6_0Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock6_0Pools s2NAutos s2NEmpty 6 s2NBlock6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock6_0Mem : ∀ ns ∈ s2NBlock6_0, Impossible s2NG 6 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NEmptyOk s2NBlock6_0Ok
def s2NNodes6 : List NodeSpec := s2NBlock6_0
def s2NBucket6 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 6 xs.toFinset) s2NBucket6 := buildBucketsBT_of_mem s2NBlock6_0Mem
def s2NBlock7_0Specs : List PoolSpec := [(9,[]),(7,[]),(8,[]),(5,[(1,0,3),(1,6,4)]),(5,[(1,0,3),(2,6,4)])]
def s2NBlock7_0Pools : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NBlock7_0Specs
def s2NBlock7_0 : List NodeSpec := [([10,0,1,2,3,4,5],[0,1,4],[]),([0,1,2,3,6,4,9,5],[0,1,2],[]),([0,1,2,3,4,9,5],[0,1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock7_0Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock7_0Pools s2NAutos s2NBucket6 7 s2NBlock7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock7_0Mem : ∀ ns ∈ s2NBlock7_0, Impossible s2NG 7 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket6Ok s2NBlock7_0Ok
def s2NBlock7_1Specs : List PoolSpec := [(9,[]),(6,[]),(0,[(1,0,3),(1,0,4)]),(7,[]),(8,[]),(2,[(1,3,4)]),(0,[(1,0,3),(1,3,4)])]
def s2NBlock7_1Pools : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NBlock7_1Specs
def s2NBlock7_1 : List NodeSpec := [([0,1,2,6,4,8,5],[0,1,3,5,6],[0]),([1,2,3,6,4,7,5],[0,1,2,3,4],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock7_1Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock7_1Pools s2NAutos s2NBucket6 7 s2NBlock7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock7_1Mem : ∀ ns ∈ s2NBlock7_1, Impossible s2NG 7 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket6Ok s2NBlock7_1Ok
def s2NNodes7 : List NodeSpec := s2NBlock7_0 ++ s2NBlock7_1
def s2NBucket7 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 7 xs.toFinset) s2NBucket7 := buildBucketsBT_of_mem (forall_append s2NBlock7_0Mem s2NBlock7_1Mem)
def s2NBlock8_0Specs : List PoolSpec := [(9,[]),(7,[]),(5,[(1,0,3)]),(2,[]),(1,[(1,0,3)]),(3,[]),(5,[(1,3,4)])]
def s2NBlock8_0Pools : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NBlock8_0Specs
def s2NBlock8_0 : List NodeSpec := [([0,1,2,3,6,4,5],[0,1,2,3,4,5],[0]),([0,1,2,3,4,8,5],[0,3,5,6],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock8_0Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock8_0Pools s2NAutos s2NBucket7 8 s2NBlock8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock8_0Mem : ∀ ns ∈ s2NBlock8_0, Impossible s2NG 8 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket7Ok s2NBlock8_0Ok
def s2NNodes8 : List NodeSpec := s2NBlock8_0
def s2NBucket8 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 8 xs.toFinset) s2NBucket8 := buildBucketsBT_of_mem s2NBlock8_0Mem
def s2NBlock9_0Specs : List PoolSpec := [(2,[]),(3,[]),(5,[]),(1,[]),(4,[])]
def s2NBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NBlock9_0Specs
def s2NBlock9_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock9_0Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock9_0Pools s2NAutos s2NBucket8 9 s2NBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock9_0Mem : ∀ ns ∈ s2NBlock9_0, Impossible s2NG 9 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket8Ok s2NBlock9_0Ok
def s2NNodes9 : List NodeSpec := s2NBlock9_0
def s2NBucket9 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 9 xs.toFinset) s2NBucket9 := buildBucketsBT_of_mem s2NBlock9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBound : Lower s2NR s2NG 10 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) s2NBucket9Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q29 : Lower (varsOf 111) 0xfffffffffffefffefefefefeeca0eca0 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (0, 1)]) (roots2 := s2NR) (T2 := s2NG) _ s2NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q36 : Lower (varsOf 123) 0xffffffffffffffeeffffeeeeeeaacc00 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (2, 3), (3, 4), (2, 3), (0, 1)]) (roots2 := s2NR) (T2 := s2NG) _ s2NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q37 : Lower (varsOf 126) 0xfffffffffffffffcfffffcfcfcf0cc00 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (2, 3), (3, 4), (2, 3), (1, 2), (0, 1)]) (roots2 := s2NR) (T2 := s2NG) _ s2NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q38d : Lower (varsOf 53) 0xfafaa0a0a0a00000fafaa0a0a0a00000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (0, 1)]) (roots2 := lb222) (T2 := lb322) _ lb382
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q38 : Lower (varsOf 53) 0xfffffafafafaa0a0fffffafafafaa0a0 7 := dualLower (by decide +kernel) (by decide +kernel) q38d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q39d : Lower (varsOf 47) 0xfac8fac880808080fac8fac880808080 7 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (1, 2)]) (roots2 := lb221) (T2 := lb652) _ lb712
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q39 : Lower (varsOf 47) 0xfefefefeeca0eca0fefefefeeca0eca0 7 := dualLower (by decide +kernel) (by decide +kernel) q39d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q40d : Lower (varsOf 59) 0xffccaa8888880000ffccaa8888880000 7 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (3, 4), (0, 1), (1, 2)]) (roots2 := lb221) (T2 := lb652) _ lb712
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q40 : Lower (varsOf 59) 0xffffeeeeeeaacc00ffffeeeeeeaacc00 7 := dualLower (by decide +kernel) (by decide +kernel) q40d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q41 : Lower (varsOf 107) 0xffffffffffeeffeeeeeeeeeecc00cc00 7 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (2, 3), (0, 1)]) (roots2 := lb568) (T2 := lb112) _ lb150
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q42d : Lower (varsOf 62) 0xffccf0c0c0c00000ffccf0c0c0c00000 7 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (3, 4), (1, 2)]) (roots2 := lb221) (T2 := lb652) _ lb712
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q42 : Lower (varsOf 62) 0xfffffcfcfcf0cc00fffffcfcfcf0cc00 7 := dualLower (by decide +kernel) (by decide +kernel) q42d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q43 : Lower (varsOf 110) 0xfffffffffffcfffcfcfcfcfccc00cc00 7 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (2, 3), (1, 2), (0, 1)]) (roots2 := lb568) (T2 := lb112) _ lb150
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q44 : Lower (varsOf 122) 0xffffffffffffffccffffcccccc00cc00 7 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1)]) (roots2 := lb568) (T2 := lb112) _ lb150
  decide +kernel
def lb204 : List Nat := [6,6,34,34,36,36,6,34,36]
def lb203 : List Nat := [4,2,32,2,32,4,32,4,2]
def lb182 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def lb179 : BT Decor := buildWiresBT 2 lb182 lb108
def lb177 : BT (Option BoundPool) := buildPoolsBT 1 lb179 lb467 lb314 lb92
lemma lb197 : goodPairs lb461 lb204 lb203 := goodPairs_of (by decide +kernel)
lemma lb183 : ∀ x ∈ lb182, faithful lb204 lb203 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb180 : btAll (fun x => faithful lb204 lb203 x ∧ x.1 < 2^128) lb179 := buildWiresBT_faithful lb183
set_option maxRecDepth 500000 in
lemma lb181 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb461 = lb461) lb229 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb205 : btAll (fun o => ∀ p, o = some p → Slice lb467 lb461 p.1 p.2) lb314 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb467 lb461 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma lb178 : btAll (fun o => ∀ c, o = some c → ValidPool lb467 lb461 c) lb177 := buildPoolsBT_sound lb205
lemma lb190 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb461 (0 - 1) xs.toFinset) lb243 := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb191 : checkNodesBT lb179 lb461 lb62 lb177 lb229 lb243 0 lb84 = true := by decide +kernel
def lb184 : BT (List (List Nat)) := buildBucketsBT lb179 lb84
set_option maxRecDepth 500000 in
lemma lb185 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb461 0 xs.toFinset) lb184 :=
  buildBucketsBT_sound (by decide) lb197 lb180 lb178 lb181 lb190 lb191
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb192 : checkNodesBT lb179 lb461 lb62 lb177 lb229 lb184 1 lb84 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb186 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb461 1 xs.toFinset) lb184 :=
  buildBucketsBT_sound (by decide) lb197 lb180 lb178 lb181 lb185 lb192
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb193 : checkNodesBT lb179 lb461 lb62 lb177 lb229 lb184 2 lb84 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb187 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb461 2 xs.toFinset) lb184 :=
  buildBucketsBT_sound (by decide) lb197 lb180 lb178 lb181 lb186 lb193
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb194 : checkNodesBT lb179 lb461 lb62 lb177 lb229 lb184 3 lb85 = true := by decide +kernel
def lb188 : BT (List (List Nat)) := buildBucketsBT lb179 lb85
set_option maxRecDepth 500000 in
lemma lb189 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb461 3 xs.toFinset) lb188 :=
  buildBucketsBT_sound (by decide) lb197 lb180 lb178 lb181 lb187 lb194
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb196 : forestRootCheck lb467 lb461 [(VAR 1,6,4),(VAR 2,6,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb195 : bucketContainsBT lb188 lb467 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb198 : Lower lb467 lb461 4 := lower_of_forestBT lb196 lb189 lb195
def lb175 : Nat := 0xfcfc0000c0c00000fcfc0000c0c00000
lemma lb200 : liftCheck 0 16 lb466 lb175 lb467 lb461 [(VAR 4,22,6)] = true := by decide +kernel
lemma lb199 : Lower lb466 lb175 5 := lift_of lb200 lb198
def lb176 : Nat := 0xfc000000c0000000fc000000c0000000
lemma lb202 : liftCheck 0 8 lb221 lb176 lb466 lb175 [(VAR 3,30,22)] = true := by decide +kernel
lemma lb201 : Lower lb221 lb176 6 := lift_of lb202 lb199
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q45d : Lower (varsOf 61) 0xfa00a00000000000fa00a00000000000 6 := by
  apply carry_of (swaps := [(4, 5), (0, 1)]) (roots2 := lb221) (T2 := lb176) _ lb201
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q45 : Lower (varsOf 61) 0xfffffffffffaffa0fffffffffffaffa0 6 := dualLower (by decide +kernel) (by decide +kernel) q45d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q46d : Lower (varsOf 51) 0xcccc888888880000cccc888888880000 5 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (3, 4), (0, 1), (1, 2)]) (roots2 := lb218) (T2 := lb397) _ lb420
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q46 : Lower (varsOf 51) 0xffffeeeeeeeeccccffffeeeeeeeecccc 5 := dualLower (by decide +kernel) (by decide +kernel) q46d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q47 : Lower (varsOf 74) 0xffccffccffccffcccc00cc00cc00cc00 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (5, 6), (2, 3)]) (roots2 := lb11) (T2 := lb0) _ lb70
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q48 : Lower (varsOf 98) 0xffffffffcccccccccccccccc00000000 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (5, 6), (2, 3), (3, 4), (4, 5)]) (roots2 := lb11) (T2 := lb0) _ lb70
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q49 : Lower (varsOf 43) 0xeeeeeeeecc00cc00eeeeeeeecc00cc00 4 := by
  apply carry_of (swaps := [(4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2)]) (roots2 := lb222) (T2 := lb650) _ lb709
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q50 : Lower (varsOf 46) 0xfcfcfcfccc00cc00fcfcfcfccc00cc00 4 := by
  apply carry_of (swaps := [(4, 5), (1, 2), (2, 3), (3, 4), (1, 2)]) (roots2 := lb222) (T2 := lb650) _ lb709
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q51 : Lower (varsOf 58) 0xffffcccccc00cc00ffffcccccc00cc00 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (1, 2)]) (roots2 := lb222) (T2 := lb650) _ lb709
  decide +kernel
def rootNR : List Nat := varsOf 127
def rootNG : Nat := 0xfffffffffffffffefffffefefefaeca0
def rootNPos : List Nat := [5,5,5,5,7,7,10,10,11,11,13,13,14,14,17,17,17,17,19,19,20,20,21,22,22,25,25,26,26,28,33,33,34,34,36,36,41,41,44,48,48,56,65,65,65,66,66,66,66,66,67,68,68,68,69,70,72,72,73,76,80,80,80,80,82,88,96,96]
def rootNNeg : List Nat := [0,1,4,64,3,6,2,8,3,9,9,12,6,12,0,1,4,16,3,18,4,16,0,6,18,9,24,18,24,24,1,32,2,32,4,32,9,40,40,16,32,40,0,1,64,2,3,6,18,64,3,1,4,64,0,6,8,64,9,12,0,1,16,64,18,24,32,64]
def rootNMask : Nat := fullMask 68
def rootNBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x4441c30c64fcf3f,0x240c481042048712),(0xcccccccccccccccccccccccccccccccc,0x10087e003198c33f0,0x10085e001098c1170),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x8f8004c21f03c3f,0x890800400913824),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x20f0002703e003fc0,0x20d00027036002e80),(0xffff0000ffff0000ffff0000ffff0000,0x3f00003803fffc000,0x3400100803d2a0000),(0xffffffff00000000ffffffff00000000,0xc000003ffc0000000,0x40000036a80000000),(0xffffffffffffffff0000000000000000,0xffffffc0000000000,0x88222100000000008)]
def rootNSteps : List (Nat × Nat × Nat) := [(1,0,2),(1,0,4),(1,2,4),(1,7,6),(2,7,6),(1,8,6),(2,8,6),(1,9,6),(2,9,6),(1,2,6),(1,4,6),(1,7,17),(3,4,10),(1,0,6),(1,7,4),(2,7,4),(3,4,20),(3,4,16),(3,2,12),(3,0,18),(2,21,6),(1,22,6),(1,11,4),(2,7,17),(3,7,17),(1,31,0),(1,31,2),(3,2,20),(1,34,4)]
def rootNW : BT Decor := buildWiresBT 6 rootNBase rootNSteps
def rootNAutoList : List (List (Nat × Nat)) := [[],[(2,4)],[(0,2)],[(0,2),(2,4)],[(0,4),(2,4)],[(0,4)]]
def rootNAutos : BT (List (Nat × Nat)) := btOfList 3 rootNAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNPairs : goodPairs rootNG rootNPos rootNNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBaseOk : ∀ x ∈ rootNBase, faithful rootNPos rootNNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNWOk : btAll (fun x => faithful rootNPos rootNNeg x ∧ x.1 < 2^128) rootNW := buildWiresBT_faithful rootNBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw rootNG = rootNG) rootNAutos := btAll_ofList (autos_of (by decide +kernel))
def rootNSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,11),some (subcubeFast 2 0,11),some (subcubeFast 10 0,10),some (subcubeFast 64 0,10),some (subcubeFast 16 0,10),some (subcubeFast 4 0,10),some (subcubeFast 1 0,10),some (subcubeFast 66 8,7),some (subcubeFast 80 0,7),some (subcubeFast 68 0,7),some (subcubeFast 20 0,7),some (subcubeFast 65 0,7),some (subcubeFast 17 0,7),some (subcubeFast 5 0,7),some (subcubeFast 64 2,6),some (subcubeFast 68 8,5),some (subcubeFast 53 0,4),some (subcubeFast 29 0,4),some (subcubeFast 84 0,4),some (subcubeFast 81 0,4),some (subcubeFast 69 0,4)]
def rootNSlices : BT (Option (Nat × Nat)) := btOfList 5 rootNSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice0 : Slice rootNR rootNG (subcubeFast 32 0) 11 := slice_fast_direct (zDead := 0) (qRoots := varsOf 95) (qGoal := 0xfffffffefffffffefefaeca0fefaeca0) (by decide +kernel) q0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice1 : Slice rootNR rootNG (subcubeFast 2 0) 11 := slice_fast_direct (zDead := 0) (qRoots := varsOf 125) (qGoal := 0xfffffffffffffffafffffafafafaa0a0) (by decide +kernel) q14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice2 : Slice rootNR rootNG (subcubeFast 10 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 117) (qGoal := 0xfffffffffffffafafffffafafafaa0a0) (by decide +kernel) q15
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice3 : Slice rootNR rootNG (subcubeFast 64 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 63) (qGoal := 0xfffffefefefaeca0fffffefefefaeca0) (by decide +kernel) q16
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice4 : Slice rootNR rootNG (subcubeFast 16 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 111) (qGoal := 0xfffffffffffefffefefefefeeca0eca0) (by decide +kernel) q29
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice5 : Slice rootNR rootNG (subcubeFast 4 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 123) (qGoal := 0xffffffffffffffeeffffeeeeeeaacc00) (by decide +kernel) q36
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice6 : Slice rootNR rootNG (subcubeFast 1 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 126) (qGoal := 0xfffffffffffffffcfffffcfcfcf0cc00) (by decide +kernel) q37
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice7 : Slice rootNR rootNG (subcubeFast 66 8) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 53) (qGoal := 0xfffffafafafaa0a0fffffafafafaa0a0) (by decide +kernel) q38
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice8 : Slice rootNR rootNG (subcubeFast 80 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfefefefeeca0eca0fefefefeeca0eca0) (by decide +kernel) q39
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice9 : Slice rootNR rootNG (subcubeFast 68 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffffeeeeeeaacc00ffffeeeeeeaacc00) (by decide +kernel) q40
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice10 : Slice rootNR rootNG (subcubeFast 20 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 107) (qGoal := 0xffffffffffeeffeeeeeeeeeecc00cc00) (by decide +kernel) q41
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice11 : Slice rootNR rootNG (subcubeFast 65 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffffcfcfcf0cc00fffffcfcfcf0cc00) (by decide +kernel) q42
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice12 : Slice rootNR rootNG (subcubeFast 17 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 110) (qGoal := 0xfffffffffffcfffcfcfcfcfccc00cc00) (by decide +kernel) q43
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice13 : Slice rootNR rootNG (subcubeFast 5 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 122) (qGoal := 0xffffffffffffffccffffcccccc00cc00) (by decide +kernel) q44
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice14 : Slice rootNR rootNG (subcubeFast 64 2) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffffffffffaffa0fffffffffffaffa0) (by decide +kernel) q45
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice15 : Slice rootNR rootNG (subcubeFast 68 8) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 51) (qGoal := 0xffffeeeeeeeeccccffffeeeeeeeecccc) (by decide +kernel) q46
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice16 : Slice rootNR rootNG (subcubeFast 53 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 74) (qGoal := 0xffccffccffccffcccc00cc00cc00cc00) (by decide +kernel) q47
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice17 : Slice rootNR rootNG (subcubeFast 29 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 98) (qGoal := 0xffffffffcccccccccccccccc00000000) (by decide +kernel) q48
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice18 : Slice rootNR rootNG (subcubeFast 84 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xeeeeeeeecc00cc00eeeeeeeecc00cc00) (by decide +kernel) q49
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice19 : Slice rootNR rootNG (subcubeFast 81 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 46) (qGoal := 0xfcfcfcfccc00cc00fcfcfcfccc00cc00) (by decide +kernel) q50
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice20 : Slice rootNR rootNG (subcubeFast 69 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffffcccccc00cc00ffffcccccc00cc00) (by decide +kernel) q51
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlicesOk : btAll (fun o => ∀ p, o = some p → Slice rootNR rootNG p.1 p.2) rootNSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice rootNR rootNG p.1 p.2) (forall_cons (fun _ h => by cases h; exact rootNSlice0) (forall_cons (fun _ h => by cases h; exact rootNSlice1) (forall_cons (fun _ h => by cases h; exact rootNSlice2) (forall_cons (fun _ h => by cases h; exact rootNSlice3) (forall_cons (fun _ h => by cases h; exact rootNSlice4) (forall_cons (fun _ h => by cases h; exact rootNSlice5) (forall_cons (fun _ h => by cases h; exact rootNSlice6) (forall_cons (fun _ h => by cases h; exact rootNSlice7) (forall_cons (fun _ h => by cases h; exact rootNSlice8) (forall_cons (fun _ h => by cases h; exact rootNSlice9) (forall_cons (fun _ h => by cases h; exact rootNSlice10) (forall_cons (fun _ h => by cases h; exact rootNSlice11) (forall_cons (fun _ h => by cases h; exact rootNSlice12) (forall_cons (fun _ h => by cases h; exact rootNSlice13) (forall_cons (fun _ h => by cases h; exact rootNSlice14) (forall_cons (fun _ h => by cases h; exact rootNSlice15) (forall_cons (fun _ h => by cases h; exact rootNSlice16) (forall_cons (fun _ h => by cases h; exact rootNSlice17) (forall_cons (fun _ h => by cases h; exact rootNSlice18) (forall_cons (fun _ h => by cases h; exact rootNSlice19) (forall_cons (fun _ h => by cases h; exact rootNSlice20) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))
def rootNEmpty : BT (List (List Nat)) := BT.empty
lemma rootNEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG (6 - 1) xs.toFinset) rootNEmpty := trivial
def rootNBlock6_0Specs : List PoolSpec := [(16,[])]
def rootNBlock6_0Pools : BT (Option BoundPool) := buildPoolsBT 1 rootNW rootNR rootNSlices rootNBlock6_0Specs
def rootNBlock6_0 : List NodeSpec := [([1,3,21,5,10,12,14],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock6_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock6_0Pools rootNAutos rootNEmpty 6 rootNBlock6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock6_0Mem : ∀ ns ∈ rootNBlock6_0, Impossible rootNG 6 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNEmptyOk rootNBlock6_0Ok
def rootNNodes6 : List NodeSpec := rootNBlock6_0
def rootNBucket6 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 6 xs.toFinset) rootNBucket6 := buildBucketsBT_of_mem rootNBlock6_0Mem
def rootNBlock7_0Specs : List PoolSpec := [(16,[])]
def rootNBlock7_0Pools : BT (Option BoundPool) := buildPoolsBT 1 rootNW rootNR rootNSlices rootNBlock7_0Specs
def rootNBlock7_0 : List NodeSpec := [([25,26,1,7,3,4,5,6],[0],[]),([25,26,1,3,4,21,5,6],[],[]),([25,26,1,3,4,5,6,10],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock7_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock7_0Pools rootNAutos rootNBucket6 7 rootNBlock7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock7_0Mem : ∀ ns ∈ rootNBlock7_0, Impossible rootNG 7 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket6Ok rootNBlock7_0Ok
def rootNBlock7_1Specs : List PoolSpec := [(16,[])]
def rootNBlock7_1Pools : BT (Option BoundPool) := buildPoolsBT 1 rootNW rootNR rootNSlices rootNBlock7_1Specs
def rootNBlock7_1 : List NodeSpec := [([25,26,1,3,4,5,6,18],[],[]),([1,2,3,21,5,10,17,12],[0],[0]),([1,7,3,4,5,10,12,14],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock7_1Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock7_1Pools rootNAutos rootNBucket6 7 rootNBlock7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock7_1Mem : ∀ ns ∈ rootNBlock7_1, Impossible rootNG 7 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket6Ok rootNBlock7_1Ok
def rootNBlock7_2Specs : List PoolSpec := [(16,[]),(18,[])]
def rootNBlock7_2Pools : BT (Option BoundPool) := buildPoolsBT 1 rootNW rootNR rootNSlices rootNBlock7_2Specs
def rootNBlock7_2 : List NodeSpec := [([1,7,3,8,5,16,17,18],[0,1],[]),([1,7,3,8,5,16,12,14],[0],[]),([1,7,3,21,5,6,12,14],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock7_2Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock7_2Pools rootNAutos rootNBucket6 7 rootNBlock7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock7_2Mem : ∀ ns ∈ rootNBlock7_2, Impossible rootNG 7 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket6Ok rootNBlock7_2Ok
def rootNBlock7_3Specs : List PoolSpec := [(16,[])]
def rootNBlock7_3Pools : BT (Option BoundPool) := buildPoolsBT 1 rootNW rootNR rootNSlices rootNBlock7_3Specs
def rootNBlock7_3 : List NodeSpec := [([1,7,3,21,5,20,17,14],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock7_3Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock7_3Pools rootNAutos rootNBucket6 7 rootNBlock7_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock7_3Mem : ∀ ns ∈ rootNBlock7_3, Impossible rootNG 7 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket6Ok rootNBlock7_3Ok
def rootNNodes7 : List NodeSpec := rootNBlock7_0 ++ rootNBlock7_1 ++ rootNBlock7_2 ++ rootNBlock7_3
def rootNBucket7 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 7 xs.toFinset) rootNBucket7 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append rootNBlock7_0Mem rootNBlock7_1Mem) rootNBlock7_2Mem) rootNBlock7_3Mem)
def rootNBlock8_0Specs : List PoolSpec := [(16,[]),(3,[(1,0,2),(1,0,4),(1,2,4)]),(11,[]),(7,[(1,0,2),(1,0,4),(1,2,4)]),(8,[(1,0,2)]),(13,[]),(4,[(1,0,2),(1,0,6),(1,2,6)]),(2,[(1,0,2),(1,0,6),(1,2,6),(2,7,4)]),(0,[(1,0,2),(1,0,6),(1,2,6),(2,7,4)]),(2,[(1,0,2),(1,0,6),(1,2,6),(3,4,20)]),(0,[(1,0,2),(1,0,6),(1,2,6),(3,4,20)])]
def rootNBlock8_0Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock8_0Specs
def rootNBlock8_0 : List NodeSpec := [([11,1,3,8,9,5,6],[0,1,3],[]),([22,1,3,4,5,20,16],[0,4,5,6,7,8],[]),([23,1,7,3,4,5,16],[0,2,6,9,10],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_0Pools rootNAutos rootNBucket7 8 rootNBlock8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_0Mem : ∀ ns ∈ rootNBlock8_0, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_0Ok
def rootNBlock8_1Specs : List PoolSpec := [(16,[]),(18,[]),(20,[]),(19,[]),(1,[(1,0,2),(1,7,4),(1,7,6),(3,4,10)]),(0,[(1,0,2),(1,4,6),(1,7,17),(3,4,18)]),(2,[(1,0,2),(1,4,6),(1,7,17),(3,4,18)])]
def rootNBlock8_1Pools : BT (Option BoundPool) := buildPoolsBT 3 rootNW rootNR rootNSlices rootNBlock8_1Specs
def rootNBlock8_1 : List NodeSpec := [([19,0,1,2,3,21,5,6],[0,2,4],[]),([19,0,1,2,3,5,6,17],[0,2,5,6],[]),([19,0,1,2,3,5,6,17,18],[0,1,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_1Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_1Pools rootNAutos rootNBucket7 8 rootNBlock8_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_1Mem : ∀ ns ∈ rootNBlock8_1, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_1Ok
def rootNBlock8_2Specs : List PoolSpec := [(16,[]),(11,[]),(20,[]),(0,[(1,0,2),(1,0,4),(1,7,6),(3,4,10)]),(0,[(1,0,2),(1,7,6),(1,4,6),(3,4,10)]),(15,[]),(1,[(1,0,2),(1,7,6),(1,4,6),(3,4,10)])]
def rootNBlock8_2Pools : BT (Option BoundPool) := buildPoolsBT 3 rootNW rootNR rootNSlices rootNBlock8_2Specs
def rootNBlock8_2 : List NodeSpec := [([19,0,1,2,3,5,10,17],[0,1,2,4,5,6],[]),([19,1,2,7,3,8,5,6],[0,1,2],[]),([19,1,2,3,8,5,6,10],[0,1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_2Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_2Pools rootNAutos rootNBucket7 8 rootNBlock8_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_2Mem : ∀ ns ∈ rootNBlock8_2, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_2Ok
def rootNBlock8_3Specs : List PoolSpec := [(16,[]),(18,[]),(19,[]),(0,[(1,0,2),(1,0,6),(1,4,20),(3,2,12)]),(1,[(1,0,2),(1,0,6),(1,4,20),(3,2,12)]),(1,[(1,0,2),(1,7,4),(1,21,6),(3,0,18)]),(8,[]),(0,[(1,0,6),(1,2,6),(1,4,20),(3,2,12)]),(2,[(1,0,6),(1,2,6),(1,4,20),(3,2,12)]),(9,[(1,4,20)])]
def rootNBlock8_3Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock8_3Specs
def rootNBlock8_3 : List NodeSpec := [([25,0,1,3,4,5,20,16],[2,6,7,8,9],[]),([25,1,7,3,4,5,6,20],[0,2,3,4],[]),([26,1,2,7,3,4,5,6],[0,1,5],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_3Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_3Pools rootNAutos rootNBucket7 8 rootNBlock8_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_3Mem : ∀ ns ∈ rootNBlock8_3, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_3Ok
def rootNBlock8_4Specs : List PoolSpec := [(16,[]),(20,[]),(11,[(1,4,10)])]
def rootNBlock8_4Pools : BT (Option BoundPool) := buildPoolsBT 2 rootNW rootNR rootNSlices rootNBlock8_4Specs
def rootNBlock8_4 : List NodeSpec := [([26,1,2,7,3,4,5,6,10],[0,1,2],[]),([26,1,2,7,3,4,5,6,18],[0,1],[0]),([26,1,2,3,4,21,5,6,18],[0],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_4Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_4Pools rootNAutos rootNBucket7 8 rootNBlock8_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_4Mem : ∀ ns ∈ rootNBlock8_4, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_4Ok
def rootNBlock8_5Specs : List PoolSpec := [(16,[]),(18,[]),(20,[]),(11,[(1,4,10)]),(0,[(1,0,2),(1,7,6),(1,4,10),(3,0,18)]),(1,[(1,0,2),(1,7,6),(1,4,10),(3,0,18)])]
def rootNBlock8_5Pools : BT (Option BoundPool) := buildPoolsBT 3 rootNW rootNR rootNSlices rootNBlock8_5Specs
def rootNBlock8_5 : List NodeSpec := [([26,1,2,3,4,5,6,20,10],[0,2,3],[]),([26,1,2,3,4,5,6,10],[0,1,2,3,4,5],[]),([26,1,2,3,4,5,6,10,18],[0,1,2],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_5Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_5Pools rootNAutos rootNBucket7 8 rootNBlock8_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_5Mem : ∀ ns ∈ rootNBlock8_5, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_5Ok
def rootNBlock8_6Specs : List PoolSpec := [(16,[]),(18,[]),(20,[]),(19,[]),(1,[(1,0,2),(1,7,4),(1,21,6),(3,0,18)]),(0,[(1,0,2),(1,7,4),(1,21,6),(3,0,18)]),(2,[(1,0,2),(1,4,6),(2,7,17),(1,30,6)]),(2,[(1,0,2),(1,4,6),(2,7,17),(1,30,17)])]
def rootNBlock8_6Pools : BT (Option BoundPool) := buildPoolsBT 3 rootNW rootNR rootNSlices rootNBlock8_6Specs
def rootNBlock8_6 : List NodeSpec := [([26,1,2,3,4,5,6,18],[0,1,4,5],[0,1]),([0,1,2,3,4,5,6,18],[0,1,2,3,7],[]),([0,1,2,3,4,5,28,17],[0,2,6],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_6Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_6Pools rootNAutos rootNBucket7 8 rootNBlock8_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_6Mem : ∀ ns ∈ rootNBlock8_6, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_6Ok
def rootNBlock8_7Specs : List PoolSpec := [(16,[]),(8,[(1,0,2)]),(9,[(1,7,4)]),(11,[(1,7,4)]),(19,[]),(2,[(1,0,2),(1,7,4),(1,7,6),(1,4,6)]),(5,[(1,7,4),(1,7,6),(1,4,6)]),(15,[]),(14,[])]
def rootNBlock8_7Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock8_7Specs
def rootNBlock8_7 : List NodeSpec := [([0,1,2,3,29,5,6,17],[0,7,8],[]),([0,1,2,3,21,5,10,17],[0,2,3,5,6],[0,2]),([32,1,2,7,3,4,5,6],[0,1,4],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_7Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_7Pools rootNAutos rootNBucket7 8 rootNBlock8_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_7Mem : ∀ ns ∈ rootNBlock8_7, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_7Ok
def rootNBlock8_8Specs : List PoolSpec := [(16,[]),(11,[]),(20,[]),(12,[]),(19,[]),(3,[(1,0,2),(1,7,17)]),(6,[(1,4,6),(1,7,17)])]
def rootNBlock8_8Pools : BT (Option BoundPool) := buildPoolsBT 3 rootNW rootNR rootNSlices rootNBlock8_8Specs
def rootNBlock8_8 : List NodeSpec := [([1,2,7,3,4,5,20,17,18],[0,2,4,5,6],[2]),([1,2,7,3,4,5,10,17,12],[0,1],[0,4]),([1,2,7,3,21,5,6,17,12],[0,3],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_8Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_8Pools rootNAutos rootNBucket7 8 rootNBlock8_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_8Mem : ∀ ns ∈ rootNBlock8_8, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_8Ok
def rootNBlock8_9Specs : List PoolSpec := [(16,[]),(11,[]),(9,[(1,0,4)]),(18,[]),(8,[(1,0,2)]),(2,[(1,0,2),(1,0,4),(1,2,6),(1,8,6)]),(5,[(1,0,4),(1,8,6)]),(20,[]),(5,[(1,0,4),(1,8,16)]),(6,[(1,2,6),(1,8,16)]),(12,[]),(3,[(1,0,2),(1,7,4)]),(7,[(1,0,2),(1,7,4)]),(2,[(1,0,2),(1,0,6),(1,7,4),(1,4,6)]),(11,[(1,7,4)])]
def rootNBlock8_9Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock8_9Specs
def rootNBlock8_9 : List NodeSpec := [([1,2,7,3,21,5,20,17],[0,4,10,11,12,13,14],[0]),([1,7,3,4,8,5,6,16,18],[0,3,7,8,9],[0]),([1,7,3,4,8,5,16,12],[0,1,2,4,5,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_9Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_9Pools rootNAutos rootNBucket7 8 rootNBlock8_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_9Mem : ∀ ns ∈ rootNBlock8_9, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_9Ok
def rootNBlock8_10Specs : List PoolSpec := [(16,[]),(11,[]),(8,[(1,0,2)]),(13,[]),(3,[(1,0,2),(1,7,4)]),(2,[(1,0,2),(1,0,6),(1,2,6),(1,7,4)]),(4,[(1,0,2),(1,0,6),(1,2,6)]),(2,[(1,0,2),(1,0,6),(1,2,6),(1,4,20)]),(5,[(1,0,6),(1,4,20)]),(0,[(1,0,2),(1,0,6),(1,2,6),(1,4,20)]),(6,[(1,4,6),(1,2,17)]),(11,[(1,2,17)]),(0,[(1,0,2),(1,4,6),(1,0,17),(1,2,17)]),(2,[(1,0,2),(1,4,6),(1,0,17),(1,2,17)]),(9,[(1,0,17)])]
def rootNBlock8_10Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock8_10Specs
def rootNBlock8_10 : List NodeSpec := [([1,7,3,4,21,5,20,16],[0,3,4,5],[]),([1,7,3,4,5,6,12,14],[0,2,10,11,12,13,14],[0]),([1,7,3,4,5,20,16,12],[0,1,2,6,7,8,9],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_10Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_10Pools rootNAutos rootNBucket7 8 rootNBlock8_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_10Mem : ∀ ns ∈ rootNBlock8_10, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_10Ok
def rootNBlock8_11Specs : List PoolSpec := [(16,[]),(2,[(1,0,2),(1,0,4),(1,2,4),(1,7,6)]),(9,[]),(11,[(1,2,4)]),(3,[(1,0,2),(1,0,4),(1,2,4)]),(11,[]),(8,[(1,0,2)]),(3,[(1,0,2),(1,0,4)]),(2,[(1,0,2),(1,0,4),(1,2,6),(1,8,6)]),(5,[(1,0,4),(1,8,6)]),(0,[(1,0,2),(1,0,4),(1,2,6),(1,8,6)]),(4,[(1,0,2),(1,2,6),(1,8,6)]),(0,[(1,0,2),(1,0,6),(1,4,6),(1,2,17)]),(6,[(1,4,6),(1,2,17)]),(2,[(1,0,2),(1,0,6),(1,4,6),(1,2,17)]),(11,[(1,2,17)])]
def rootNBlock8_11Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock8_11Specs
def rootNBlock8_11 : List NodeSpec := [([1,7,3,4,5,20,17,14],[0,2,6,12,13,14,15],[0]),([1,7,3,4,5,16,12],[0,5,6,7,8,9,10,11],[]),([1,7,3,8,9,5,6,10],[0,1,2,3,4,5],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_11Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_11Pools rootNAutos rootNBucket7 8 rootNBlock8_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_11Mem : ∀ ns ∈ rootNBlock8_11, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_11Ok
def rootNBlock8_12Specs : List PoolSpec := [(16,[]),(9,[(1,0,4)]),(18,[]),(2,[(1,0,2),(1,0,4),(1,2,6),(1,4,6)]),(0,[(1,0,2),(1,0,4),(1,2,6),(1,4,6)]),(8,[(1,0,2)]),(3,[(1,0,2),(1,0,4)]),(4,[(1,0,2),(1,2,6)]),(0,[(1,0,2),(1,0,4),(1,2,6),(1,4,16)]),(17,[]),(6,[(1,2,6),(1,4,16)]),(2,[(1,0,2),(1,0,4),(1,2,6),(1,4,16)]),(13,[]),(3,[(1,0,2),(1,7,4)]),(2,[(1,0,2),(1,0,6),(1,2,6),(1,7,4)]),(0,[(1,0,2),(1,0,6),(1,2,6),(1,7,4)]),(4,[(1,0,2),(1,0,6),(1,2,6)]),(9,[(1,7,4)])]
def rootNBlock8_12Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock8_12Specs
def rootNBlock8_12 : List NodeSpec := [([1,7,3,8,5,6,16,14],[1,2,8,9,10,11],[0]),([1,7,3,8,5,16,17],[0,1,3,4,5,6,7],[0]),([1,3,4,21,5,20,16],[0,12,13,14,15,16,17],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_12Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_12Pools rootNAutos rootNBucket7 8 rootNBlock8_12 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_12Mem : ∀ ns ∈ rootNBlock8_12, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_12Ok
def rootNBlock8_13Specs : List PoolSpec := [(16,[]),(2,[(1,0,2),(1,0,4),(1,2,4),(1,7,6)]),(11,[(1,2,4)]),(3,[(1,0,2),(1,0,4),(1,2,4)]),(0,[(1,0,2),(1,0,4),(1,2,4),(1,7,6)]),(4,[(1,0,2),(1,7,6)]),(9,[(1,0,4)])]
def rootNBlock8_13Pools : BT (Option BoundPool) := buildPoolsBT 3 rootNW rootNR rootNSlices rootNBlock8_13Specs
def rootNBlock8_13 : List NodeSpec := [([1,3,8,9,5,6,10],[0,1,2,3,4,5,6],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_13Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_13Pools rootNAutos rootNBucket7 8 rootNBlock8_13 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_13Mem : ∀ ns ∈ rootNBlock8_13, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket7Ok rootNBlock8_13Ok
def rootNNodes8 : List NodeSpec := rootNBlock8_0 ++ rootNBlock8_1 ++ rootNBlock8_2 ++ rootNBlock8_3 ++ rootNBlock8_4 ++ rootNBlock8_5 ++ rootNBlock8_6 ++ rootNBlock8_7 ++ rootNBlock8_8 ++ rootNBlock8_9 ++ rootNBlock8_10 ++ rootNBlock8_11 ++ rootNBlock8_12 ++ rootNBlock8_13
def rootNBucket8 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 8 xs.toFinset) rootNBucket8 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append rootNBlock8_0Mem rootNBlock8_1Mem) rootNBlock8_2Mem) rootNBlock8_3Mem) rootNBlock8_4Mem) rootNBlock8_5Mem) rootNBlock8_6Mem) rootNBlock8_7Mem) rootNBlock8_8Mem) rootNBlock8_9Mem) rootNBlock8_10Mem) rootNBlock8_11Mem) rootNBlock8_12Mem) rootNBlock8_13Mem)
def rootNBlock9_0Specs : List PoolSpec := [(16,[]),(8,[(1,0,2)]),(3,[(1,0,2),(1,0,4)]),(13,[]),(7,[(1,0,2),(1,0,4)]),(3,[(1,0,2),(1,7,4)]),(2,[(1,0,2),(1,7,4),(2,21,6)]),(2,[(1,0,2),(1,4,6),(2,7,17)])]
def rootNBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 3 rootNW rootNR rootNSlices rootNBlock9_0Specs
def rootNBlock9_0 : List NodeSpec := [([30,0,1,2,3,4,5,6,17],[0,1,7],[0]),([11,1,2,3,4,8,5,6],[0,2,3,4],[0]),([27,0,1,2,3,4,5,6],[0,5,6],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_0Pools rootNAutos rootNBucket8 9 rootNBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_0Mem : ∀ ns ∈ rootNBlock9_0, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_0Ok
def rootNBlock9_1Specs : List PoolSpec := [(16,[]),(9,[]),(11,[]),(13,[]),(4,[(1,0,2),(1,0,6)]),(2,[(1,0,2),(1,0,6),(2,7,4)]),(0,[(1,0,2),(1,0,6),(2,7,4)]),(3,[(1,0,2),(2,7,4)]),(2,[(1,0,2),(1,0,6),(3,4,20)]),(0,[(1,0,2),(1,0,6),(3,4,20)]),(5,[(1,0,6),(3,4,20)]),(4,[(1,0,6),(1,2,6)]),(2,[(1,0,6),(1,2,6),(3,4,20)]),(0,[(1,0,6),(1,2,6),(3,4,20)])]
def rootNBlock9_1Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock9_1Specs
def rootNBlock9_1 : List NodeSpec := [([22,1,2,3,4,5,6,20],[2,3,4,5,6,7],[0]),([23,0,1,2,3,4,5,16],[1,2,10,11,12,13],[0]),([23,1,2,7,3,4,5,6],[0,2,4,8,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_1Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_1Pools rootNAutos rootNBucket8 9 rootNBlock9_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_1Mem : ∀ ns ∈ rootNBlock9_1, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_1Ok
def rootNBlock9_2Specs : List PoolSpec := [(16,[]),(9,[]),(11,[]),(4,[(1,0,2),(1,7,6)]),(20,[]),(13,[]),(2,[(1,0,2),(1,7,6),(3,4,10)]),(5,[(1,7,6),(3,4,10)]),(0,[(1,0,2),(1,7,6),(3,4,10)]),(6,[(1,7,6),(3,4,10)]),(3,[(1,0,2),(3,4,10)]),(4,[(1,0,6),(1,2,20)]),(2,[(1,0,6),(1,2,20),(3,4,10)]),(0,[(1,0,6),(1,2,20),(3,4,10)])]
def rootNBlock9_2Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock9_2Specs
def rootNBlock9_2 : List NodeSpec := [([19,0,1,2,7,3,4,5,6],[0,1,2,3,4,6,7],[0,2]),([19,0,1,2,3,4,5,6],[0,3,4,6,7,8,9,10],[3]),([19,0,1,2,3,4,5,6,20],[1,4,5,11,12,13],[1,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_2Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_2Pools rootNAutos rootNBucket8 9 rootNBlock9_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_2Mem : ∀ ns ∈ rootNBlock9_2, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_2Ok
def rootNBlock9_3Specs : List PoolSpec := [(16,[]),(9,[]),(11,[]),(4,[(1,0,2),(1,7,6)]),(8,[(1,0,2)]),(20,[]),(13,[]),(11,[(1,4,10)]),(9,[(1,4,10)]),(5,[(1,7,6),(1,4,10)]),(2,[(1,0,2),(1,7,6),(3,4,10)]),(0,[(1,0,2),(1,7,6),(3,4,10)]),(2,[(1,0,2),(1,4,6),(3,7,17)]),(5,[(1,4,6),(3,7,17)])]
def rootNBlock9_3Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock9_3Specs
def rootNBlock9_3 : List NodeSpec := [([19,0,1,2,3,4,5,6,10],[1,2,3,5,6,10,11],[0,2,3]),([31,0,1,2,7,3,4,5,6],[0,4,12,13],[0,2]),([0,1,2,7,3,4,5,6,10,18],[0,4,5,7,8,9],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_3Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_3Pools rootNAutos rootNBucket8 9 rootNBlock9_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_3Mem : ∀ ns ∈ rootNBlock9_3, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_3Ok
def rootNBlock9_4Specs : List PoolSpec := [(16,[]),(9,[]),(11,[]),(4,[(1,0,2),(1,7,6)]),(18,[]),(8,[(1,0,2)]),(20,[]),(3,[(1,0,2),(1,7,4)]),(19,[]),(3,[(1,0,2),(1,7,17)]),(6,[(1,4,6),(1,7,17)]),(2,[(1,0,2),(1,7,4),(1,21,6)]),(5,[(1,7,4),(1,21,6)]),(7,[(1,0,2)]),(2,[(1,0,2),(1,7,6),(1,4,6)]),(5,[(1,7,6),(1,4,6)]),(4,[(1,0,2),(1,7,17)]),(5,[(1,4,6),(1,7,17)])]
def rootNBlock9_4Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock9_4Specs
def rootNBlock9_4 : List NodeSpec := [([0,1,2,7,3,4,5,6,17,18],[0,4,5,6,8,9,10,16,17],[0,1,2,4]),([0,1,2,7,3,4,5,6,18],[0,5,6,7,11,12],[0,2]),([0,1,2,7,3,4,5,10,17],[0,1,2,3,5,6,13,14,15],[0,1,2,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_4Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_4Pools rootNAutos rootNBucket8 9 rootNBlock9_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_4Mem : ∀ ns ∈ rootNBlock9_4, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_4Ok
def rootNBlock9_5Specs : List PoolSpec := [(16,[]),(11,[]),(8,[(1,0,2)]),(12,[]),(3,[(1,0,2),(1,7,4)]),(2,[(1,0,2),(1,7,4),(1,4,6)]),(10,[]),(5,[(1,7,4),(1,4,6)]),(2,[(1,0,2),(2,7,6),(1,11,4)]),(3,[(1,0,2),(1,11,4)]),(2,[(1,0,6),(3,2,20),(1,34,4)]),(0,[(1,0,6),(3,2,20),(1,34,4)]),(5,[(1,0,6),(1,34,4)])]
def rootNBlock9_5Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock9_5Specs
def rootNBlock9_5 : List NodeSpec := [([0,1,2,7,3,21,5,6,17],[0,2,3,4,5,6,7],[0,2]),([0,1,2,3,4,29,5,6],[0,8,9],[]),([0,1,2,3,4,35,5,6],[1,10,11,12],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_5Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_5Pools rootNAutos rootNBucket8 9 rootNBlock9_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_5Mem : ∀ ns ∈ rootNBlock9_5, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_5Ok
def rootNBlock9_6Specs : List PoolSpec := [(16,[]),(20,[]),(13,[]),(3,[(1,0,2),(1,7,4)]),(9,[(1,7,4)]),(11,[(1,7,4)]),(2,[(1,0,2),(1,7,4),(1,7,6)]),(5,[(1,7,4),(1,7,6)]),(2,[(1,0,2),(1,7,4),(1,21,6)]),(2,[(1,0,2),(2,7,4),(1,22,6)]),(0,[(1,0,2),(2,7,4),(1,22,6)]),(4,[(1,0,2),(1,22,6)])]
def rootNBlock9_6Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock9_6Specs
def rootNBlock9_6 : List NodeSpec := [([0,1,2,3,4,21,5,6,10],[0,1,3,4,5,6,7],[0]),([0,1,2,3,4,21,5,6,18],[0,3,8],[0,1,2,3,4]),([0,1,2,3,4,5,6,28],[2,9,10,11],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_6Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_6Pools rootNAutos rootNBucket8 9 rootNBlock9_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_6Mem : ∀ ns ∈ rootNBlock9_6, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_6Ok
def rootNBlock9_7Specs : List PoolSpec := [(16,[]),(11,[]),(4,[(1,0,2),(1,7,6)]),(20,[]),(5,[(1,0,6),(1,4,20)]),(19,[]),(11,[(1,4,10)]),(9,[(1,4,10)]),(5,[(1,7,6),(1,4,10)]),(0,[(1,0,2),(1,7,6),(1,4,10)]),(2,[(1,0,2),(1,7,6),(1,4,10)]),(6,[(1,7,6),(1,4,10)]),(9,[(1,4,20)]),(2,[(1,0,6),(1,2,20),(1,4,20)]),(0,[(1,0,6),(1,2,20),(1,4,20)]),(4,[(1,0,6),(1,2,20)]),(8,[(1,2,20)])]
def rootNBlock9_7Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock9_7Specs
def rootNBlock9_7 : List NodeSpec := [([0,1,2,3,4,5,6,20,10,18],[0,3,5,6,7],[0]),([0,1,2,3,4,5,6,10,12],[0,1,3,4,5,12,13,14,15,16],[2,3,4]),([0,1,2,3,4,5,6,10,18],[0,2,3,6,7,8,9,10,11],[0,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_7Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_7Pools rootNAutos rootNBucket8 9 rootNBlock9_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_7Mem : ∀ ns ∈ rootNBlock9_7, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_7Ok
def rootNBlock9_8Specs : List PoolSpec := [(16,[]),(11,[]),(18,[]),(8,[(1,0,2)]),(3,[(1,0,2),(1,7,4)]),(5,[(1,0,6),(1,4,20)]),(19,[]),(6,[(1,4,6),(1,7,17)]),(2,[(1,0,2),(1,7,4),(1,21,6)]),(5,[(1,7,4),(1,21,6)]),(0,[(1,0,2),(1,7,4),(1,21,6)]),(4,[(1,0,2),(1,21,6)]),(6,[(1,7,4),(1,21,6)]),(5,[(1,4,6),(1,7,17)]),(2,[(1,0,2),(1,4,6),(1,7,17)]),(0,[(1,0,2),(1,4,6),(1,7,17)]),(8,[]),(9,[(1,4,20)]),(2,[(1,0,6),(1,2,6),(1,4,20)]),(0,[(1,0,6),(1,2,6),(1,4,20)]),(4,[(1,0,6),(1,2,6)])]
def rootNBlock9_8Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock9_8Specs
def rootNBlock9_8 : List NodeSpec := [([0,1,2,3,4,5,6,17,18],[0,2,3,6,7,13,14,15],[0]),([0,1,2,3,4,5,6,18],[0,4,8,9,10,11,12],[0,2,3]),([0,1,2,3,4,5,20,16,12],[0,1,5,6,16,17,18,19,20],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_8Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_8Pools rootNAutos rootNBucket8 9 rootNBlock9_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_8Mem : ∀ ns ∈ rootNBlock9_8, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_8Ok
def rootNBlock9_9Specs : List PoolSpec := [(16,[]),(9,[]),(11,[]),(4,[(1,0,2),(1,7,6)]),(3,[(1,0,2),(1,0,4)]),(20,[]),(13,[]),(2,[(1,0,2),(1,0,4),(1,7,6)]),(12,[]),(3,[(1,0,2),(1,7,4)]),(11,[(1,7,4)]),(2,[(1,0,2),(1,0,6),(1,7,4)]),(2,[(1,0,2),(1,7,6),(1,4,6)]),(5,[(1,7,6),(1,4,6)]),(0,[(1,0,2),(1,7,6),(1,4,6)]),(6,[(1,7,6),(1,4,6)])]
def rootNBlock9_9Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock9_9Specs
def rootNBlock9_9 : List NodeSpec := [([0,1,2,3,4,5,10,17],[0,1,2,3,12,13,14,15],[0,1,4]),([1,2,7,3,4,8,5,6,10],[0,1,2,4,5,6,7],[0,1]),([1,2,7,3,4,21,5,6,20],[0,6,8,9,10,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_9Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_9Pools rootNAutos rootNBucket8 9 rootNBlock9_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_9Mem : ∀ ns ∈ rootNBlock9_9, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_9Ok
def rootNBlock9_10Specs : List PoolSpec := [(16,[]),(11,[]),(8,[(1,0,2)]),(17,[]),(5,[(1,0,6),(1,4,20)]),(4,[(1,0,2),(1,0,6)]),(19,[]),(2,[(1,0,2),(1,0,6),(1,4,6)]),(0,[(1,0,2),(1,0,6),(1,4,6)]),(5,[(1,0,6),(1,4,6)]),(2,[(1,0,2),(1,0,6),(1,4,20)]),(0,[(1,0,2),(1,0,6),(1,4,20)]),(5,[(1,4,6),(1,0,17)]),(0,[(1,0,2),(1,4,6),(1,0,17)]),(2,[(1,0,2),(1,4,6),(1,0,17)])]
def rootNBlock9_10Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock9_10Specs
def rootNBlock9_10 : List NodeSpec := [([1,2,7,3,4,5,6,20,12],[0,1,2,4,5,6,10,11],[0,2]),([1,2,7,3,4,5,6,17,12],[1,2,3,6,12,13,14],[0,2,4]),([1,2,7,3,4,5,20,17],[0,1,2,5,7,8,9],[0,1,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_10Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_10Pools rootNAutos rootNBucket8 9 rootNBlock9_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_10Mem : ∀ ns ∈ rootNBlock9_10, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_10Ok
def rootNBlock9_11Specs : List PoolSpec := [(16,[]),(9,[]),(11,[]),(4,[(1,0,2),(1,7,6)]),(9,[(1,0,4)]),(3,[(1,0,2),(1,0,4)]),(4,[(1,0,2),(1,2,6)]),(2,[(1,0,2),(1,0,4),(1,2,6)]),(0,[(1,0,2),(1,0,4),(1,2,6)]),(13,[]),(2,[(1,0,2),(1,0,4),(1,7,6)]),(0,[(1,0,2),(1,0,4),(1,7,6)]),(5,[(1,0,4),(1,7,6)]),(12,[]),(3,[(1,0,2),(1,7,4)]),(2,[(1,0,2),(1,0,6),(1,7,4)]),(0,[(1,0,2),(1,0,6),(1,7,4)]),(4,[(1,0,2),(1,0,6)]),(5,[(1,0,6),(1,7,4)])]
def rootNBlock9_11Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock9_11Specs
def rootNBlock9_11 : List NodeSpec := [([1,2,3,4,8,5,6,10],[0,2,3,4,5,10,11,12],[0,1]),([1,2,3,4,21,5,6,20],[0,9,13,14,15,16,17,18],[0,1]),([1,7,3,4,8,5,6,16],[0,1,4,5,6,7,8,9],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_11Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_11Pools rootNAutos rootNBucket8 9 rootNBlock9_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_11Mem : ∀ ns ∈ rootNBlock9_11, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_11Ok
def rootNBlock9_12Specs : List PoolSpec := [(16,[]),(9,[]),(3,[(1,0,2),(1,0,4),(1,2,4)]),(11,[]),(2,[(1,0,2),(1,0,4),(1,2,4)]),(0,[(1,0,2),(1,0,4),(1,2,4)]),(4,[(1,0,2)]),(5,[(1,0,4)]),(13,[]),(4,[(1,0,2),(1,0,6),(1,2,6)]),(2,[(1,0,2),(1,0,6),(1,2,6)]),(0,[(1,0,2),(1,0,6),(1,2,6)]),(6,[(1,2,6)])]
def rootNBlock9_12Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock9_12Specs
def rootNBlock9_12 : List NodeSpec := [([1,7,3,4,5,20,16],[1,3,8,9,10,11,12],[0,2]),([1,7,3,8,9,5,6],[0,2,3,4,5,6,7],[0,1,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_12Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_12Pools rootNAutos rootNBucket8 9 rootNBlock9_12 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_12Mem : ∀ ns ∈ rootNBlock9_12, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_12Ok
def rootNNodes9 : List NodeSpec := rootNBlock9_0 ++ rootNBlock9_1 ++ rootNBlock9_2 ++ rootNBlock9_3 ++ rootNBlock9_4 ++ rootNBlock9_5 ++ rootNBlock9_6 ++ rootNBlock9_7 ++ rootNBlock9_8 ++ rootNBlock9_9 ++ rootNBlock9_10 ++ rootNBlock9_11 ++ rootNBlock9_12
def rootNBucket9 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 9 xs.toFinset) rootNBucket9 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append rootNBlock9_0Mem rootNBlock9_1Mem) rootNBlock9_2Mem) rootNBlock9_3Mem) rootNBlock9_4Mem) rootNBlock9_5Mem) rootNBlock9_6Mem) rootNBlock9_7Mem) rootNBlock9_8Mem) rootNBlock9_9Mem) rootNBlock9_10Mem) rootNBlock9_11Mem) rootNBlock9_12Mem)
def rootNBlock10_0Specs : List PoolSpec := [(9,[]),(11,[]),(4,[(1,0,2)]),(13,[]),(5,[(1,0,6)]),(3,[(1,0,2)]),(10,[]),(2,[(1,0,2),(2,7,4)]),(0,[(1,0,2),(2,7,4)]),(2,[(1,0,2),(2,7,6)]),(0,[(1,0,2),(2,7,6)]),(8,[]),(2,[(1,0,6),(3,2,20)]),(0,[(1,0,6),(3,2,20)])]
def rootNBlock10_0Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock10_0Specs
def rootNBlock10_0 : List NodeSpec := [([11,0,1,2,3,4,5,6],[3,5,6,9,10],[0,2]),([22,0,1,2,3,4,5,6],[0,2,3,7,8],[0,2]),([34,0,1,2,3,4,5,6],[1,4,11,12,13],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock10_0Pools rootNAutos rootNBucket9 10 rootNBlock10_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_0Mem : ∀ ns ∈ rootNBlock10_0, Impossible rootNG 10 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket9Ok rootNBlock10_0Ok
def rootNBlock10_1Specs : List PoolSpec := [(16,[]),(9,[]),(11,[]),(4,[(1,0,2),(1,7,6)]),(4,[(1,0,2)]),(8,[(1,0,2)]),(20,[]),(13,[]),(12,[]),(3,[(1,0,2),(1,7,4)]),(3,[(1,0,2)]),(10,[]),(2,[(1,0,2),(1,7,4)]),(5,[(1,7,4)]),(2,[(1,0,2),(1,7,6)]),(0,[(1,0,2),(1,7,6)]),(5,[(1,7,6)]),(2,[(1,0,2),(1,4,6)]),(5,[(1,4,6)]),(0,[(1,0,2),(1,4,6)]),(6,[(1,4,6)]),(8,[])]
def rootNBlock10_1Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock10_1Specs
def rootNBlock10_1 : List NodeSpec := [([0,1,2,7,3,4,21,5,6],[0,7,8,9,11,12,13],[0,2]),([0,1,2,7,3,4,5,6,10],[1,2,3,6,7,10,14,15,16],[0,2]),([0,1,2,7,3,4,5,6,17],[0,4,5,7,10,17,18,19,20,21],[0,1,2,3,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_1Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock10_1Pools rootNAutos rootNBucket9 10 rootNBlock10_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_1Mem : ∀ ns ∈ rootNBlock10_1, Impossible rootNG 10 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket9Ok rootNBlock10_1Ok
def rootNBlock10_2Specs : List PoolSpec := [(16,[]),(9,[]),(11,[]),(4,[(1,0,2),(1,7,6)]),(4,[(1,0,2)]),(20,[]),(13,[]),(12,[]),(3,[(1,0,2),(1,7,4)]),(5,[(1,0,6)]),(3,[(1,0,2)]),(10,[]),(2,[(1,0,2),(1,7,4)]),(5,[(1,7,4)]),(0,[(1,0,2),(1,7,4)]),(6,[(1,7,4)]),(2,[(1,0,2),(1,7,6)]),(0,[(1,0,2),(1,7,6)]),(5,[(1,7,6)]),(6,[(1,7,6)]),(4,[(1,0,6),(1,2,20)]),(2,[(1,0,6),(1,2,20)]),(0,[(1,0,6),(1,2,20)])]
def rootNBlock10_2Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock10_2Specs
def rootNBlock10_2 : List NodeSpec := [([0,1,2,3,4,21,5,6],[0,4,6,7,8,11,12,13,14,15],[0,2,3]),([0,1,2,3,4,5,6,20,10],[1,2,5,6,9,20,21,22],[0,1,4]),([0,1,2,3,4,5,6,10],[1,2,3,6,10,16,17,18,19],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_2Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock10_2Pools rootNAutos rootNBucket9 10 rootNBlock10_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_2Mem : ∀ ns ∈ rootNBlock10_2, Impossible rootNG 10 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket9Ok rootNBlock10_2Ok
def rootNBlock10_3Specs : List PoolSpec := [(16,[]),(9,[]),(11,[]),(4,[(1,0,2)]),(5,[(1,0,4)]),(3,[(1,0,2),(1,0,4)]),(13,[]),(2,[(1,0,2),(1,0,4)]),(0,[(1,0,2),(1,0,4)]),(12,[]),(6,[(1,2,6)]),(4,[(1,0,2),(1,0,6)]),(2,[(1,0,2),(1,0,6)]),(5,[(1,0,6)]),(0,[(1,0,2),(1,0,6)]),(3,[(1,0,2)]),(4,[(1,0,6),(1,2,6)]),(2,[(1,0,6),(1,2,6)]),(0,[(1,0,6),(1,2,6)])]
def rootNBlock10_3Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock10_3Specs
def rootNBlock10_3 : List NodeSpec := [([0,1,2,3,4,5,20,16],[1,2,10,13,16,17,18],[0,1,2,4]),([1,2,7,3,4,8,5,6],[0,3,4,5,6,7,8,9],[0,1]),([1,2,7,3,4,5,6,20],[2,6,11,12,13,14,15],[0,1,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_3Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock10_3Pools rootNAutos rootNBucket9 10 rootNBlock10_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_3Mem : ∀ ns ∈ rootNBlock10_3, Impossible rootNG 10 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket9Ok rootNBlock10_3Ok
def rootNNodes10 : List NodeSpec := rootNBlock10_0 ++ rootNBlock10_1 ++ rootNBlock10_2 ++ rootNBlock10_3
def rootNBucket10 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 10 xs.toFinset) rootNBucket10 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append rootNBlock10_0Mem rootNBlock10_1Mem) rootNBlock10_2Mem) rootNBlock10_3Mem)
def rootNBlock11_0Specs : List PoolSpec := [(11,[]),(4,[(1,0,2)]),(13,[]),(5,[(1,0,6)]),(3,[(1,0,2)]),(2,[(1,0,2)]),(0,[(1,0,2)]),(5,[]),(6,[]),(2,[(1,0,6)]),(0,[(1,0,6)]),(3,[]),(4,[(1,0,6)])]
def rootNBlock11_0Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock11_0Specs
def rootNBlock11_0 : List NodeSpec := [([0,1,2,7,3,4,5,6],[1,2,4,5,6,7,8],[0,2]),([0,1,2,3,4,5,6,20],[0,3,8,9,10,11,12],[0,1,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock11_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock11_0Pools rootNAutos rootNBucket10 11 rootNBlock11_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock11_0Mem : ∀ ns ∈ rootNBlock11_0, Impossible rootNG 11 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket10Ok rootNBlock11_0Ok
def rootNNodes11 : List NodeSpec := rootNBlock11_0
def rootNBucket11 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 11 xs.toFinset) rootNBucket11 := buildBucketsBT_of_mem rootNBlock11_0Mem
def rootNBlock12_0Specs : List PoolSpec := [(5,[]),(6,[]),(3,[]),(2,[]),(0,[]),(4,[])]
def rootNBlock12_0Pools : BT (Option BoundPool) := buildPoolsBT 3 rootNW rootNR rootNSlices rootNBlock12_0Specs
def rootNBlock12_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5],[0,1,2,3,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock12_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock12_0Pools rootNAutos rootNBucket11 12 rootNBlock12_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock12_0Mem : ∀ ns ∈ rootNBlock12_0, Impossible rootNG 12 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket11Ok rootNBlock12_0Ok
def rootNNodes12 : List NodeSpec := rootNBlock12_0
def rootNBucket12 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket12Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 12 xs.toFinset) rootNBucket12 := buildBucketsBT_of_mem rootNBlock12_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBound : Lower rootNR rootNG 13 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) rootNBucket12Ok (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sevenGraph : Lower (varsOf 127) 0xfffffffffffffffefffffffafeecfaa0 13 := carry_of (swaps := [(1, 2), (2, 3), (3, 4), (1, 2)]) (roots2 := rootNR) (T2 := rootNG) (by decide +kernel) rootNBound
end Small
namespace Relate
def insertRow (r : Small.Row) : Wide.Row :=
  ⟨(0 + ((r.val / 1) % 2) * 1 + ((r.val / 2) % 2) * 4 + ((r.val / 4) % 2) * 8 + ((r.val / 8) % 2) * 16 + ((r.val / 16) % 2) * 32 + ((r.val / 32) % 2) * 64 + ((r.val / 64) % 2) * 128) % 256, Nat.mod_lt _ (by decide)⟩
def project (w : Wide.Wire) : Small.Wire := fun r => w (insertRow r)
lemma avail {b : List Wide.Wire} {v : Wide.Wire} (h : Wide.Avail b v) :
    Small.Avail (b.map project) (project v) := by
  rcases h with h | ⟨k, rfl⟩ | h
  · exact Or.inl (List.mem_map_of_mem h)
  · exact Or.inr (Or.inl ⟨k,rfl⟩)
  · exact Or.inr (Or.inr (List.mem_map_of_mem (f := project) h))
lemma reach {roots b : List Wide.Wire} {n : Nat} (h : Wide.Reach roots n b) :
    Small.Reach (roots.map project) n (b.map project) := by
  induction n generalizing b with
  | zero => change b = roots at h; rw [h]; rfl
  | succ n ih =>
    obtain ⟨op,bank,a,b,hr,ha,hb,rfl⟩ := h
    refine ⟨op, bank.map project, project a, project b, ih hr, avail ha, avail hb, ?_⟩
    cases op <;> rfl
lemma liftPins : Wide.Lower (Wide.varsOf 255) 0xfffffffffffffffffffffffffffffffaffffffffffffffeefffefefcffaaaa00 14 := by
  have bound : Wide.Lower (Wide.varsOf 253) 0xfffffffffffffffffffffffffffffffaffffffffffffffaafffafaf0ffaaaa00 13 := by
    intro n bank hr ha
    have proots : (((Wide.varsOf 253).map Wide.obs).map project) = (Small.varsOf 127).map Small.obs := by
      change [_,_,_,_,_,_,_] = [_,_,_,_,_,_,_]
      repeat' apply congrArg₂ List.cons
      all_goals first | rfl | funext r; revert r; decide +kernel
    have target : project (Wide.obs 0xfffffffffffffffffffffffffffffffaffffffffffffffaafffafaf0ffaaaa00) = Small.obs 0xfffffffffffffffefffffffafeecfaa0 := by funext r; revert r; decide +kernel
    have r := reach hr
    have a := avail ha
    rw [proots] at r
    rw [target] at a
    exact Small.sevenGraph n _ r a
  exact Wide.lift_of (z := 2) (o := 0) (essPairs := [(Wide.VAR 1,32,34)]) (by decide +kernel) bound
end Relate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
def onWit : List Gate := [⟨.or, [0, 3]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [7, 5]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [6, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [2, 15]⟩, ⟨.and, [10, 16]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [18, 19]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [21, 20]⟩]

theorem onWitBasis : ∀ g ∈ onWit,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [onWit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onWitCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨onWit, 22⟩ (List.ofFn x) = f x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onGraphCorrect : ∀ x : Fin 8 → Bool, f x = decide (∃ i < ([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

theorem onFinal :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfit _hone hev
  have hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y := fun y => (hev y).trans (onGraphCorrect y).symm
  have hrow : ∀ r : Wide.Row, f (Wide.evalInput r) = (0xfffffffffffffffffffffffffffffffaffffffffffffffeefffefefcffaaaa00 : Nat).testBit r.val := by decide +kernel
  have hw : ∀ r : Wide.Row, Circuit.eval ⟨onWit, 22⟩ (List.ofFn (Wide.evalInput r)) = (0xfffffffffffffffffffffffffffffffaffffffffffffffeefffefefcffaaaa00 : Nat).testBit r.val :=
    fun r => (onWitCorrect (Wide.evalInput r)).trans (hrow r)
  obtain ⟨gs, out, hg, hlen, hev⟩ := Wide.replace_of_lower (0xfffffffffffffffffffffffffffffffaffffffffffffffeefffefefcffaaaa00 : Nat) (by decide) (by decide) (by decide)
    14 Relate.liftPins onWit 22 (by decide) onWitBasis f hrow hw gates o hfit hf
  exact ⟨gs, out, hg, hlen, fun x => (hev x).trans (onGraphCorrect x)⟩
end PEqualNP.Outside.L_meta_52162

theorem PEqualNP.Outside.L_meta_52162 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_52162.onFinal
