import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_52014
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

def identifyRow (z o i j : Nat) (r : Row) : Row :=
  let mask := if r.val.testBit i then 1 <<< j else 0
  ⟨((fixRow z o r).val &&& (127 ^^^ (1 <<< j)) ||| mask) % 128, Nat.mod_lt _ (by decide)⟩
lemma mappedSlice {f : Row → Row} {raw R : List Nat} {T G D L : Nat}
    (proper : checkProper G = true) (inDomain : ∀ r : Row, D.testBit (f r).val = true)
    (covered : raw.all (fun v => freeIn R (renameW f v)) = true)
    (mapped : renameW f T = G) (bound : Lower R G L) : Slice raw T D L := by
  have ⟨g0,glt,gb0⟩ := checkProper_sound proper
  refine ⟨f, R, inDomain, fun a ha => freeIn_sound (List.all_eq_true.mp covered a ha), ?_, ?_⟩
  · rw [← obs_renameW, mapped]
    exact obs_not_const g0 glt gb0
  · rw [← obs_renameW, mapped]
    exact bound

def lb77 : List Nat := varsOf 30
def lb69 : Nat := 0xffccf000ffccf000ffccf000ffccf000
def lb76 : List Nat := [12,14,12,14,24,18,24,22]
def lb71 : List Nat := [8,10,4,6,8,2,16,6]
def lb70 : Nat := fullMask 8
def lb60 : List Decor := [(0xcccccccccccccccccccccccccccccccc,170,170),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,143,140),(0xff00ff00ff00ff00ff00ff00ff00ff00,95,19),(0xffff0000ffff0000ffff0000ffff0000,240,64)]
def lb82 : List (Nat × Nat × Nat) := []
def lb84 : BT Decor := buildWiresBT 2 lb60 lb82
def lb57 : List (List (Nat × Nat)) := [[],[(3,4),(1,2)]]
def lb58 : BT (List (Nat × Nat)) := btOfList 1 lb57
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb73 : goodPairs lb69 lb76 lb71 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb61 : ∀ x ∈ lb60, faithful lb76 lb71 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb85 : btAll (fun x => faithful lb76 lb71 x ∧ x.1 < 2^128) lb84 := buildWiresBT_faithful lb61
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb59 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb69 = lb69) lb58 := btAll_ofList (autos_of (by decide +kernel))
def lb78 : List (Option (Nat × Nat)) := []
def lb79 : BT (Option (Nat × Nat)) := btOfList 1 lb78
def lb81 : List PoolSpec := []
def lb74 : BT (Option BoundPool) := buildPoolsBT 1 lb84 lb77 lb79 lb81
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb80 : btAll (fun o => ∀ p, o = some p → Slice lb77 lb69 p.1 p.2) lb79 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb77 lb69 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb75 : btAll (fun o => ∀ c, o = some c → ValidPool lb77 lb69 c) lb74 := buildPoolsBT_sound lb80
def lb67 : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb68 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb69 (3 - 1) xs.toFinset) lb67 := trivial
def lb62 : List NodeSpec := nodesWithIdentity [([0,1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb83 : checkNodesBT lb84 lb69 lb70 lb74 lb58 lb67 3 lb62 = true := by decide +kernel
def lb72 : List NodeSpec := lb62
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb66 : checkNodesBT lb84 lb69 lb70 lb74 lb58 lb67 3 lb72 = true := lb83
def lb64 : BT (List (List Nat)) := buildBucketsBT lb84 lb72
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb65 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb69 3 xs.toFinset) lb64 := buildBucketsBT_sound (by decide) lb73 lb85 lb75 lb59 lb68 lb66
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb63 : Lower lb77 lb69 4 := lower_of_forestBT (essPairs := [(VAR 1,16,18),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,2,18)]) (by decide +kernel) lb65 (by decide +kernel)
def lb2 : List Nat := varsOf 46
def lb1 : Nat := 0xfcfcfcfcf000f000fcfcfcfcf000f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb0 : Lower lb2 lb1 4 := carry_of (swaps := [(4,5),(2,3)]) (roots2 := lb77) (T2 := lb69) (by decide +kernel) lb63
def lb5 : List Nat := varsOf 54
def lb4 : Nat := 0xfcfcfcfccccc0000fcfcfcfccccc0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb3 : Lower lb5 lb4 4 := carry_of (swaps := [(4,5),(2,3),(3,4),(1,2)]) (roots2 := lb77) (T2 := lb69) (by decide +kernel) lb63
def lb8 : List Nat := varsOf 58
def lb7 : Nat := 0xffccccccffcc0000ffccccccffcc0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb6 : Lower lb8 lb7 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(3,4),(1,2),(2,3)]) (roots2 := lb77) (T2 := lb69) (by decide +kernel) lb63
def lb11 : List Nat := varsOf 60
def lb10 : Nat := 0xfff0f0f0ff00f000fff0f0f0ff00f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb9 : Lower lb11 lb10 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(2,3),(1,2)]) (roots2 := lb77) (T2 := lb69) (by decide +kernel) lb63
def lb41 : List Nat := varsOf 62
def lb31 : Nat := 0xfffcfcfcffccf000fffcfcfcffccf000
def lb40 : List Nat := [12,18,14,22,12,14,12,24,18,34,36,24,22,42,52,42,24,36,52,56,56]
def lb33 : List Nat := [8,16,10,20,10,6,4,8,2,2,4,16,6,10,20,40,10,32,48,48,40]
def lb32 : Nat := fullMask 21
def lb15 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xb32e,0x13334),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x6547d,0x5468),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x19a8f5,0x11a095),(0xffff0000ffff0000ffff0000ffff0000,0x1d598a,0xc480a),(0xffffffff00000000ffffffff00000000,0x1ee600,0x1e8000)]
def lb51 : List (Nat × Nat × Nat) := [(1,0,1),(1,0,3),(3,4,5)]
def lb55 : BT Decor := buildWiresBT 3 lb15 lb51
def lb12 : List (List (Nat × Nat)) := [[],[(4,5),(2,3)],[(3,4),(1,2)],[(2,5),(1,3)],[(3,5),(1,4)],[(2,4),(1,5)],[(4,5),(3,4),(2,4),(1,2)],[(4,5),(3,5),(2,3),(1,3)],[(4,5),(3,5),(2,5),(1,4)],[(4,5),(3,4),(2,3),(1,5)]]
def lb13 : BT (List (Nat × Nat)) := btOfList 4 lb12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb37 : goodPairs lb31 lb40 lb33 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb16 : ∀ x ∈ lb15, faithful lb40 lb33 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb56 : btAll (fun x => faithful lb40 lb33 x ∧ x.1 < 2^128) lb55 := buildWiresBT_faithful lb16
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb14 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb31 = lb31) lb13 := btAll_ofList (autos_of (by decide +kernel))
def lb47 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4),some (subcubeFast 16 0,4),some (subcubeFast 32 0,4)]
def lb48 : BT (Option (Nat × Nat)) := btOfList 3 lb47
def lb50 : List PoolSpec := [(0,[]),(4,[]),(1,[]),(2,[]),(3,[])]
def lb38 : BT (Option BoundPool) := buildPoolsBT 3 lb55 lb41 lb48 lb50
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb46 : Slice lb41 lb31 (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) lb63
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb45 : Slice lb41 lb31 (subcubeFast 16 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) lb0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb44 : Slice lb41 lb31 (subcubeFast 8 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) lb3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb43 : Slice lb41 lb31 (subcubeFast 4 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) lb6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb42 : Slice lb41 lb31 (subcubeFast 2 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) lb9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb49 : btAll (fun o => ∀ p, o = some p → Slice lb41 lb31 p.1 p.2) lb48 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb41 lb31 p.1 p.2) (forall_cons (fun _ h => by cases h; exact lb42) (forall_cons (fun _ h => by cases h; exact lb43) (forall_cons (fun _ h => by cases h; exact lb44) (forall_cons (fun _ h => by cases h; exact lb45) (forall_cons (fun _ h => by cases h; exact lb46) (fun _ h => (List.not_mem_nil h).elim))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb39 : btAll (fun o => ∀ c, o = some c → ValidPool lb41 lb31 c) lb38 := buildPoolsBT_sound lb49
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb30 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb31 (4 - 1) xs.toFinset) lb67 := trivial
def lb17 : List NodeSpec := nodesWithIdentity [([0,1,2,3,7],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb52 : checkNodesBT lb55 lb31 lb32 lb38 lb13 lb67 4 lb17 = true := by decide +kernel
def lb34 : List NodeSpec := lb17
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb27 : checkNodesBT lb55 lb31 lb32 lb38 lb13 lb67 4 lb34 = true := lb52
def lb21 : BT (List (List Nat)) := buildBucketsBT lb55 lb34
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb22 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb31 4 xs.toFinset) lb21 := buildBucketsBT_sound (by decide) lb37 lb56 lb39 lb14 lb30 lb27
def lb18 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[1]),([0,1,2,3,4,6],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb53 : checkNodesBT lb55 lb31 lb32 lb38 lb13 lb21 5 lb18 = true := by decide +kernel
def lb35 : List NodeSpec := lb18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb28 : checkNodesBT lb55 lb31 lb32 lb38 lb13 lb21 5 lb35 = true := lb53
def lb23 : BT (List (List Nat)) := buildBucketsBT lb55 lb35
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb24 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb31 5 xs.toFinset) lb23 := buildBucketsBT_sound (by decide) lb37 lb56 lb39 lb14 lb22 lb28
def lb19 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb54 : checkNodesBT lb55 lb31 lb32 lb38 lb13 lb23 6 lb19 = true := by decide +kernel
def lb36 : List NodeSpec := lb19
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb29 : checkNodesBT lb55 lb31 lb32 lb38 lb13 lb23 6 lb36 = true := lb54
def lb25 : BT (List (List Nat)) := buildBucketsBT lb55 lb36
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb26 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb31 6 xs.toFinset) lb25 := buildBucketsBT_sound (by decide) lb37 lb56 lb39 lb14 lb24 lb29
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb20 : Lower lb41 lb31 7 := lower_of_forestBT (essPairs := [(VAR 1,16,18),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,2,18),(VAR 5,2,34)]) (by decide +kernel) lb26 (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q1 : Lower (varsOf 62) 0xfffcfcfcffccf000fffcfcfcffccf000 7 := by
  apply carry_of (swaps := []) (roots2 := lb41) (T2 := lb31) _ lb20
  decide +kernel
def lb342 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def lb351 : List Nat := varsOf 13
def lb402 : List Nat := [5,5,9,9,12,12,5,9,12]
def lb398 : List Nat := [4,1,8,1,8,4,8,4,1]
def lb378 : Nat := fullMask 9
def lb366 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bc,0x54)]
def lb358 : BT Decor := buildWiresBT 2 lb366 lb82
def lb362 : List (List (Nat × Nat)) := []
def lb363 : BT (List (Nat × Nat)) := btOfList 1 lb362
def lb404 : BT (Option PoolSpec) := btOfList 1 []
lemma lb384 : goodPairs lb342 lb402 lb398 := goodPairs_of (by decide +kernel)
lemma lb367 : ∀ x ∈ lb366, faithful lb402 lb398 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb359 : btAll (fun x => faithful lb402 lb398 x ∧ x.1 < 2^128) lb358 := buildWiresBT_faithful lb367
set_option maxRecDepth 500000 in
lemma lb364 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb342 = lb342) lb363 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb415 : btAll (fun o => ∀ p, o = some p → Slice lb351 lb342 p.1 p.2) lb79 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb351 lb342 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb370 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb342 2 xs.toFinset) lb67 := trivial
def lb400 : List NodeSpec := [([0,1,2],[],[])]
def lb349 : BT (Option BoundPool) := buildPoolsSubBT 1 lb358 lb351 lb79 lb404 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb376 : checkNodesBT lb358 lb342 lb378 lb349 lb363 lb67 3 lb400 = true := by decide +kernel
def lb371 : BT (List (List Nat)) := buildBucketsBT lb358 lb400
set_option maxRecDepth 500000 in
lemma lb372 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb342 3 xs.toFinset) lb371 :=
  buildBucketsBT_sound (by decide) lb384 lb359 (buildPoolsSubBT_sound lb415) lb364 lb370 lb376
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb381 : forestRootCheck lb351 lb342 [(VAR 0,5,4),(VAR 2,5,1),(VAR 3,9,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb380 : bucketContainsBT lb371 lb351 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb386 : Lower lb351 lb342 4 := lower_of_forestBT lb381 lb372 lb380
def lb346 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def lb355 : List Nat := varsOf 19
lemma lb393 : carryOK [(3,4),(1,2)] lb355 lb346 lb351 lb342 = true := by decide +kernel
lemma lb392 : Lower lb355 lb346 4 := carry_of lb393 lb386
def lb347 : Nat := 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8
def lb356 : List Nat := varsOf 23
lemma lb395 : liftCheck 4 0 lb356 lb347 lb355 lb346 [(VAR 2,5,1)] = true := by decide +kernel
lemma lb394 : Lower lb356 lb347 5 := lift_of lb395 lb392
def lb348 : Nat := 0xfaaafaa0faaafaa0faaafaa0faaafaa0
def lb357 : List Nat := varsOf 29
lemma lb397 : liftCheck 16 0 lb357 lb348 lb351 lb342 [(VAR 4,17,1)] = true := by decide +kernel
lemma lb396 : Lower lb357 lb348 5 := lift_of lb397 lb386
def lb343 : Nat := 0xeeeeaa88eeeeaa88eeeeaa88eeeeaa88
def lb352 : List Nat := varsOf 27
lemma lb388 : carryOK [(3,4),(1,2)] lb352 lb343 lb357 lb348 = true := by decide +kernel
lemma lb387 : Lower lb352 lb343 5 := carry_of lb388 lb396
def lb344 : Nat := 0xfae8fae8fae8fae8fae8fae8fae8fae8
def lb353 : List Nat := varsOf 15
lemma lb390 : carryOK [(3,4),(1,2)] lb353 lb344 lb356 lb347 = true := by decide +kernel
lemma lb389 : Lower lb353 lb344 5 := carry_of lb390 lb394
def lb345 : Nat := 0xfeeefae8feeefae8feeefae8feeefae8
def lb354 : List Nat := varsOf 31
def lb403 : List Nat := [3,3,5,5,6,6,9,9,11,12,12,14,17,17,18,18,21,22,25,26,26,28,28,3,3,3,5,5,5,6,6,6,6,9,9,9,12,12,12,12,17,17,17,18,18,18,18]
def lb399 : List Nat := [2,1,4,1,4,2,8,1,10,8,4,10,16,1,16,2,20,20,24,24,10,24,20,10,20,24,10,20,24,1,10,20,24,10,20,24,1,10,20,24,10,20,24,1,10,20,24]
def lb379 : Nat := fullMask 47
def lb368 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x70e1f8531cf,0x8102000208a),(0xcccccccccccccccccccccccccccccccc,0x7801e39ac933,0x112244908921),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf1fc630e3c,0x224489430414),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfe007c0fc0,0x55ab56bc0b40),(0xffff0000ffff0000ffff0000ffff0000,0x7f00007ff000,0x66cd9b6f5000)]
def lb360 : BT Decor := buildWiresBT 3 lb368 lb82
def lb414 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5)]
def lb416 : BT (Option (Nat × Nat)) := btOfList 2 lb414
def lb405 : BT (Option PoolSpec) := btOfList 2 [some (0,[]),some (1,[]),some (2,[]),some (3,[])]
lemma lb385 : goodPairs lb345 lb403 lb399 := goodPairs_of (by decide +kernel)
lemma lb369 : ∀ x ∈ lb368, faithful lb403 lb399 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb361 : btAll (fun x => faithful lb403 lb399 x ∧ x.1 < 2^128) lb360 := buildWiresBT_faithful lb369
set_option maxRecDepth 500000 in
lemma lb365 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb345 = lb345) lb363 := btAll_ofList (autos_of (by decide +kernel))
lemma lb407 : sliceDirectCheck 2 0 0 lb354 lb345 lb357 lb348 = true := by decide +kernel
lemma lb406 : Slice lb354 lb345 (subcubeFast 2 0) 5 := slice_fast_direct lb407 lb396
lemma lb409 : sliceDirectCheck 4 0 0 lb354 lb345 lb352 lb343 = true := by decide +kernel
lemma lb408 : Slice lb354 lb345 (subcubeFast 4 0) 5 := slice_fast_direct lb409 lb387
lemma lb411 : sliceDirectCheck 8 0 0 lb354 lb345 lb356 lb347 = true := by decide +kernel
lemma lb410 : Slice lb354 lb345 (subcubeFast 8 0) 5 := slice_fast_direct lb411 lb394
lemma lb413 : sliceDirectCheck 16 0 0 lb354 lb345 lb353 lb344 = true := by decide +kernel
lemma lb412 : Slice lb354 lb345 (subcubeFast 16 0) 5 := slice_fast_direct lb413 lb389
set_option maxRecDepth 500000 in
lemma lb417 : btAll (fun o => ∀ p, o = some p → Slice lb354 lb345 p.1 p.2) lb416 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb354 lb345 p.1 p.2) (forall_cons (fun _ h => by cases h; exact lb406) (forall_cons (fun _ h => by cases h; exact lb408) (forall_cons (fun _ h => by cases h; exact lb410) (forall_cons (fun _ h => by cases h; exact lb412) (fun _ h => (List.not_mem_nil h).elim)))))
lemma lb373 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb345 5 xs.toFinset) lb67 := trivial
def lb401 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3],[])]
def lb350 : BT (Option BoundPool) := buildPoolsSubBT 2 lb360 lb354 lb416 lb405 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb377 : checkNodesBT lb360 lb345 lb379 lb350 lb363 lb67 6 lb401 = true := by decide +kernel
def lb374 : BT (List (List Nat)) := buildBucketsBT lb360 lb401
set_option maxRecDepth 500000 in
lemma lb375 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb345 6 xs.toFinset) lb374 :=
  buildBucketsBT_sound (by decide) lb385 lb361 (buildPoolsSubBT_sound lb417) lb365 lb373 lb377
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb383 : forestRootCheck lb354 lb345 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,9,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb382 : bucketContainsBT lb374 lb354 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb391 : Lower lb354 lb345 7 := lower_of_forestBT lb383 lb375 lb382
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q2 : Lower (varsOf 55) 0xfefefefeeeeea8a8fefefefeeeeea8a8 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (3, 4)]) (roots2 := lb354) (T2 := lb345) _ lb391
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q3 : Lower (varsOf 47) 0xfefefefefaa8faa8fefefefefaa8faa8 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2)]) (roots2 := lb354) (T2 := lb345) _ lb391
  decide +kernel
def lb418 : Nat := 0xffffff00ff000000ffffff00ff000000
def lb427 : List Nat := varsOf 56
def lb497 : List Nat := [24,24,40,40,48,48,24,40,48]
def lb490 : List Nat := [16,8,32,8,32,16,32,16,8]
def lb439 : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def lb431 : Array Decor := buildWires lb439 lb82
def lb435 : Array (List (Nat × Nat)) := #[]
def lb508 : List (Nat × Nat) := []
def lb510 : Array (Nat × Nat) := lb508.toArray
def lb423 : Array (Option BoundPool) := buildPools lb431 lb427 lb510 lb81
lemma lb480 : goodPairs lb418 lb497 lb490 := goodPairs_of (by decide +kernel)
lemma lb440 : ∀ x ∈ lb439, faithful lb497 lb490 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb432 : ∀ x ∈ lb431.toList, faithful lb497 lb490 x ∧ x.1 < 2^128 := buildWires_faithful lb440
lemma lb436 : ∀ sw ∈ lb435.toList, swapsValid sw = true ∧ permWord sw lb418 = lb418 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma lb511 : ∀ i (hi : i < lb510.size), Slice lb427 lb418 lb510[i].1 lb510[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb427 lb418 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb424 : ∀ i (hi : i < lb423.size), ∀ c, lb423[i] = some c → ValidPool lb427 lb418 c := buildPools_sound lb511
def lb449 : Array (List (List Nat)) := #[]
lemma lb450 : ∀ i (hi : i < lb449.size), ∀ xs ∈ lb449[i], Impossible lb418 (0 - 1) xs.toFinset := by intro i hi; simp [lb449] at hi
def lb492 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb464 : checkNodes lb431 lb418 lb378 lb423 lb435 lb449 0 lb492 = true := by decide +kernel
def lb443 : Array (List (List Nat)) := buildBuckets 1 lb431 lb492
lemma lb444 : ∀ i (hi : i < lb443.size), ∀ xs ∈ lb443[i], Impossible lb418 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb480 lb432 lb424 lb436 lb450 lb464
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb465 : checkNodes lb431 lb418 lb378 lb423 lb435 lb443 1 lb492 = true := by decide +kernel
lemma lb445 : ∀ i (hi : i < lb443.size), ∀ xs ∈ lb443[i], Impossible lb418 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb480 lb432 lb424 lb436 lb444 lb465
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb466 : checkNodes lb431 lb418 lb378 lb423 lb435 lb443 2 lb492 = true := by decide +kernel
lemma lb446 : ∀ i (hi : i < lb443.size), ∀ xs ∈ lb443[i], Impossible lb418 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb480 lb432 lb424 lb436 lb445 lb466
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb467 : checkNodes lb431 lb418 lb378 lb423 lb435 lb443 3 lb400 = true := by decide +kernel
def lb447 : Array (List (List Nat)) := buildBuckets 1 lb431 lb400
lemma lb448 : ∀ i (hi : i < lb447.size), ∀ xs ∈ lb447[i], Impossible lb418 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb480 lb432 lb424 lb436 lb446 lb467
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb477 : forestRootCheck lb427 lb418 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb476 : bucketContains lb447 lb427 = true := by decide +kernel
lemma lb482 : Lower lb427 lb418 4 := lower_of_forest lb477 lb448 lb476
def lb419 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def lb428 : List Nat := varsOf 28
lemma lb484 : carryOK [(2,5),(2,4),(2,3)] lb428 lb419 lb427 lb418 = true := by decide +kernel
lemma lb483 : Lower lb428 lb419 4 := carry_of lb484 lb482
def lb420 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def lb429 : List Nat := varsOf 44
lemma lb486 : carryOK [(2,4),(2,3)] lb429 lb420 lb427 lb418 = true := by decide +kernel
lemma lb485 : Lower lb429 lb420 4 := carry_of lb486 lb482
def lb421 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def lb430 : List Nat := varsOf 52
lemma lb488 : carryOK [(2,3)] lb430 lb421 lb427 lb418 = true := by decide +kernel
lemma lb487 : Lower lb430 lb421 4 := carry_of lb488 lb482
def lb422 : Nat := 0xfff0f000f0000000fff0f000f0000000
def lb498 : List Nat := [28,28,28,44,44,44,52,52,52,56,56,56,28,28,28,44,44,44,52,52,52,56,56,56]
def lb491 : List Nat := [24,20,12,40,36,12,48,36,20,48,40,24,36,40,48,20,24,48,12,24,40,12,20,36]
def lb475 : Nat := fullMask 24
def lb441 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1ff1ff,0xe491b6),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def lb514 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def lb433 : Array Decor := buildWires lb441 lb514
def lb437 : Array (List (Nat × Nat)) := #[[],[(4,5)],[(2,3)],[(4,5),(2,3)],[(3,4)],[(3,5),(3,4)],[(2,3),(2,4)],[(3,5),(2,3),(2,4)],[(3,5),(2,4)]]
def lb509 : List (Nat × Nat) := [(subcube 0 16,4),(subcube 0 4,4),(subcube 0 8,4),(subcube 0 32,4)]
def lb512 : Array (Nat × Nat) := lb509.toArray
def lb499 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def lb425 : Array (Option BoundPool) := buildPools lb433 lb11 lb512 lb499
lemma lb481 : goodPairs lb422 lb498 lb491 := goodPairs_of (by decide +kernel)
lemma lb442 : ∀ x ∈ lb441, faithful lb498 lb491 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb434 : ∀ x ∈ lb433.toList, faithful lb498 lb491 x ∧ x.1 < 2^128 := buildWires_faithful lb442
lemma lb438 : ∀ sw ∈ lb437.toList, swapsValid sw = true ∧ permWord sw lb422 = lb422 := autos_of (by decide +kernel)
lemma lb501 : sliceDirectCheck 0 16 0 lb11 lb422 lb429 lb420 = true := by decide +kernel
lemma lb500 : Slice lb11 lb422 (subcube 0 16) 4 := slice_direct lb501 lb485
lemma lb503 : sliceDirectCheck 0 4 0 lb11 lb422 lb427 lb418 = true := by decide +kernel
lemma lb502 : Slice lb11 lb422 (subcube 0 4) 4 := slice_direct lb503 lb482
lemma lb505 : sliceDirectCheck 0 8 0 lb11 lb422 lb430 lb421 = true := by decide +kernel
lemma lb504 : Slice lb11 lb422 (subcube 0 8) 4 := slice_direct lb505 lb487
lemma lb507 : sliceDirectCheck 0 32 0 lb11 lb422 lb428 lb419 = true := by decide +kernel
lemma lb506 : Slice lb11 lb422 (subcube 0 32) 4 := slice_direct lb507 lb483
set_option maxRecDepth 200000 in
lemma lb513 : ∀ i (hi : i < lb512.size), Slice lb11 lb422 lb512[i].1 lb512[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb11 lb422 p.1 p.2) (forall_cons lb500 (forall_cons lb502 (forall_cons lb504 (forall_cons lb506 (fun _ h => (List.not_mem_nil h).elim)))))
lemma lb426 : ∀ i (hi : i < lb425.size), ∀ c, lb425[i] = some c → ValidPool lb11 lb422 c := buildPools_sound lb513
lemma lb463 : ∀ i (hi : i < lb449.size), ∀ xs ∈ lb449[i], Impossible lb422 (0 - 1) xs.toFinset := by intro i hi; simp [lb449] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb468 : checkNodes lb433 lb422 lb475 lb425 lb437 lb449 0 lb492 = true := by decide +kernel
def lb451 : Array (List (List Nat)) := buildBuckets 1 lb433 lb492
lemma lb452 : ∀ i (hi : i < lb451.size), ∀ xs ∈ lb451[i], Impossible lb422 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb481 lb434 lb426 lb438 lb463 lb468
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb469 : checkNodes lb433 lb422 lb475 lb425 lb437 lb451 1 lb492 = true := by decide +kernel
lemma lb453 : ∀ i (hi : i < lb451.size), ∀ xs ∈ lb451[i], Impossible lb422 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb481 lb434 lb426 lb438 lb452 lb469
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb470 : checkNodes lb433 lb422 lb475 lb425 lb437 lb451 2 lb492 = true := by decide +kernel
lemma lb454 : ∀ i (hi : i < lb451.size), ∀ xs ∈ lb451[i], Impossible lb422 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb481 lb434 lb426 lb438 lb453 lb470
def lb493 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb471 : checkNodes lb433 lb422 lb475 lb425 lb437 lb451 3 lb493 = true := by decide +kernel
def lb455 : Array (List (List Nat)) := buildBuckets 1 lb433 lb493
lemma lb456 : ∀ i (hi : i < lb455.size), ∀ xs ∈ lb455[i], Impossible lb422 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb481 lb434 lb426 lb438 lb454 lb471
def lb494 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb472 : checkNodes lb433 lb422 lb475 lb425 lb437 lb455 4 lb494 = true := by decide +kernel
def lb457 : Array (List (List Nat)) := buildBuckets 2 lb433 lb494
lemma lb458 : ∀ i (hi : i < lb457.size), ∀ xs ∈ lb457[i], Impossible lb422 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb481 lb434 lb426 lb438 lb456 lb472
def lb495 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb473 : checkNodes lb433 lb422 lb475 lb425 lb437 lb457 5 lb495 = true := by decide +kernel
def lb459 : Array (List (List Nat)) := buildBuckets 1 lb433 lb495
lemma lb460 : ∀ i (hi : i < lb459.size), ∀ xs ∈ lb459[i], Impossible lb422 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb481 lb434 lb426 lb438 lb458 lb473
def lb496 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb474 : checkNodes lb433 lb422 lb475 lb425 lb437 lb459 6 lb496 = true := by decide +kernel
def lb461 : Array (List (List Nat)) := buildBuckets 1 lb433 lb496
lemma lb462 : ∀ i (hi : i < lb461.size), ∀ xs ∈ lb461[i], Impossible lb422 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb481 lb434 lb426 lb438 lb460 lb474
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb479 : forestRootCheck lb11 lb422 [(VAR 2,28,24),(VAR 3,28,20),(VAR 4,28,12),(VAR 5,44,12)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb478 : bucketContains lb461 lb11 = true := by decide +kernel
lemma lb489 : Lower lb11 lb422 7 := lower_of_forest lb479 lb462 lb478
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q4d : Lower (varsOf 27) 0xee888800ee888800ee888800ee888800 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2)]) (roots2 := lb11) (T2 := lb422) _ lb489
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q4 : Lower (varsOf 27) 0xffeeee88ffeeee88ffeeee88ffeeee88 7 := dualLower (by decide +kernel) (by decide +kernel) q4d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q5d : Lower (varsOf 39) 0xe8e8e8e880808080e8e8e8e880808080 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3)]) (roots2 := lb11) (T2 := lb422) _ lb489
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q5 : Lower (varsOf 39) 0xfefefefee8e8e8e8fefefefee8e8e8e8 7 := dualLower (by decide +kernel) (by decide +kernel) q5d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q6d : Lower (varsOf 29) 0xfaa0a000faa0a000faa0a000faa0a000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (0, 1)]) (roots2 := lb11) (T2 := lb422) _ lb489
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q6 : Lower (varsOf 29) 0xfffafaa0fffafaa0fffafaa0fffafaa0 7 := dualLower (by decide +kernel) (by decide +kernel) q6d
def lb515 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def lb519 : List Nat := varsOf 21
def lb542 : List Nat := [5,5,17,17,20,20,5,17,20]
def lb541 : List Nat := [4,1,16,1,16,4,16,4,1]
def lb525 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def lb522 : BT Decor := buildWiresBT 2 lb525 lb82
lemma lb533 : goodPairs lb515 lb542 lb541 := goodPairs_of (by decide +kernel)
lemma lb526 : ∀ x ∈ lb525, faithful lb542 lb541 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb523 : btAll (fun x => faithful lb542 lb541 x ∧ x.1 < 2^128) lb522 := buildWiresBT_faithful lb526
set_option maxRecDepth 500000 in
lemma lb524 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb515 = lb515) lb363 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb543 : btAll (fun o => ∀ p, o = some p → Slice lb519 lb515 p.1 p.2) lb79 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb519 lb515 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb527 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb515 2 xs.toFinset) lb67 := trivial
def lb518 : BT (Option BoundPool) := buildPoolsSubBT 1 lb522 lb519 lb79 lb404 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb530 : checkNodesBT lb522 lb515 lb378 lb518 lb363 lb67 3 lb400 = true := by decide +kernel
def lb528 : BT (List (List Nat)) := buildBucketsBT lb522 lb400
set_option maxRecDepth 500000 in
lemma lb529 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb515 3 xs.toFinset) lb528 :=
  buildBucketsBT_sound (by decide) lb533 lb523 (buildPoolsSubBT_sound lb543) lb524 lb527 lb530
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb532 : forestRootCheck lb519 lb515 [(VAR 0,5,4),(VAR 2,5,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb531 : bucketContainsBT lb528 lb519 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb534 : Lower lb519 lb515 4 := lower_of_forestBT lb532 lb529 lb531
lemma lb536 : carryOK [(3,4)] lb351 lb342 lb519 lb515 = true := by decide +kernel
lemma lb535 : Lower lb351 lb342 4 := carry_of lb536 lb534
def lb516 : Nat := 0xfaa0faa0fa00fa00faa0faa0fa00fa00
def lb520 : List Nat := varsOf 45
lemma lb538 : liftCheck 0 32 lb520 lb516 lb351 lb342 [(VAR 5,37,5)] = true := by decide +kernel
lemma lb537 : Lower lb520 lb516 5 := lift_of lb538 lb535
def lb517 : Nat := 0xeeee8888cccc8888eeee8888cccc8888
def lb521 : List Nat := varsOf 51
lemma lb540 : carryOK [(2,4),(1,2),(1,3)] lb521 lb517 lb520 lb516 = true := by decide +kernel
lemma lb539 : Lower lb521 lb517 5 := carry_of lb540 lb537
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q7d : Lower (varsOf 15) 0xeaa0eaa0eaa0eaa0eaa0eaa0eaa0eaa0 5 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (3, 4), (2, 3), (0, 1), (1, 2)]) (roots2 := lb521) (T2 := lb517) _ lb539
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q7 : Lower (varsOf 15) 0xfaa8faa8faa8faa8faa8faa8faa8faa8 5 := dualLower (by decide +kernel) (by decide +kernel) q7d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q8d : Lower (varsOf 58) 0xffcccc00cccccc00ffcccc00cccccc00 5 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (0, 1)]) (roots2 := lb521) (T2 := lb517) _ lb539
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q8 : Lower (varsOf 58) 0xffccccccffcccc00ffccccccffcccc00 5 := dualLower (by decide +kernel) (by decide +kernel) q8d
def lb544 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def lb548 : List Nat := varsOf 14
def lb574 : List Nat := [6,6,10,10,12,12,6,10,12]
def lb573 : List Nat := [4,2,8,2,8,4,8,4,2]
def lb552 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bc,0x54)]
def lb549 : Array Decor := buildWires lb552 lb82
def lb546 : Array (Option BoundPool) := buildPools lb549 lb548 lb510 lb81
lemma lb567 : goodPairs lb544 lb574 lb573 := goodPairs_of (by decide +kernel)
lemma lb553 : ∀ x ∈ lb552, faithful lb574 lb573 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb550 : ∀ x ∈ lb549.toList, faithful lb574 lb573 x ∧ x.1 < 2^128 := buildWires_faithful lb553
lemma lb551 : ∀ sw ∈ lb435.toList, swapsValid sw = true ∧ permWord sw lb544 = lb544 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma lb575 : ∀ i (hi : i < lb510.size), Slice lb548 lb544 lb510[i].1 lb510[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb548 lb544 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb547 : ∀ i (hi : i < lb546.size), ∀ c, lb546[i] = some c → ValidPool lb548 lb544 c := buildPools_sound lb575
lemma lb560 : ∀ i (hi : i < lb449.size), ∀ xs ∈ lb449[i], Impossible lb544 (0 - 1) xs.toFinset := by intro i hi; simp [lb449] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb561 : checkNodes lb549 lb544 lb378 lb546 lb435 lb449 0 lb492 = true := by decide +kernel
def lb554 : Array (List (List Nat)) := buildBuckets 1 lb549 lb492
lemma lb555 : ∀ i (hi : i < lb554.size), ∀ xs ∈ lb554[i], Impossible lb544 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb567 lb550 lb547 lb551 lb560 lb561
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb562 : checkNodes lb549 lb544 lb378 lb546 lb435 lb554 1 lb492 = true := by decide +kernel
lemma lb556 : ∀ i (hi : i < lb554.size), ∀ xs ∈ lb554[i], Impossible lb544 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb567 lb550 lb547 lb551 lb555 lb562
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb563 : checkNodes lb549 lb544 lb378 lb546 lb435 lb554 2 lb492 = true := by decide +kernel
lemma lb557 : ∀ i (hi : i < lb554.size), ∀ xs ∈ lb554[i], Impossible lb544 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb567 lb550 lb547 lb551 lb556 lb563
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb564 : checkNodes lb549 lb544 lb378 lb546 lb435 lb554 3 lb400 = true := by decide +kernel
def lb558 : Array (List (List Nat)) := buildBuckets 1 lb549 lb400
lemma lb559 : ∀ i (hi : i < lb558.size), ∀ xs ∈ lb558[i], Impossible lb544 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb567 lb550 lb547 lb551 lb557 lb564
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb566 : forestRootCheck lb548 lb544 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb565 : bucketContains lb558 lb548 = true := by decide +kernel
lemma lb568 : Lower lb548 lb544 4 := lower_of_forest lb566 lb559 lb565
lemma lb572 : carryOK [(3,5),(2,3),(1,2),(1,4)] lb429 lb420 lb548 lb544 = true := by decide +kernel
lemma lb571 : Lower lb429 lb420 4 := carry_of lb572 lb568
def lb545 : Nat := 0xffc0ffc0c000c000ffc0ffc0c000c000
lemma lb570 : liftCheck 0 2 lb2 lb545 lb429 lb420 [(VAR 1,14,12)] = true := by decide +kernel
lemma lb569 : Lower lb2 lb545 5 := lift_of lb570 lb571
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q9d : Lower (varsOf 51) 0xeeee888888888888eeee888888888888 5 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (2, 3), (0, 1), (1, 2)]) (roots2 := lb2) (T2 := lb545) _ lb569
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q9 : Lower (varsOf 51) 0xeeeeeeeeeeee8888eeeeeeeeeeee8888 5 := dualLower (by decide +kernel) (by decide +kernel) q9d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q10d : Lower (varsOf 54) 0xfcfcccccc0c0c0c0fcfcccccc0c0c0c0 5 := by
  apply carry_of (swaps := [(4, 5), (0, 1), (1, 2), (0, 1)]) (roots2 := lb521) (T2 := lb517) _ lb539
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q10 : Lower (varsOf 54) 0xfcfcfcfcccccc0c0fcfcfcfcccccc0c0 5 := dualLower (by decide +kernel) (by decide +kernel) q10d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q11d : Lower (varsOf 46) 0xfcf0fcf0c0c0c0c0fcf0fcf0c0c0c0c0 5 := by
  apply carry_of (swaps := [(4, 5), (3, 4), (1, 2), (0, 1)]) (roots2 := lb521) (T2 := lb517) _ lb539
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q11 : Lower (varsOf 46) 0xfcfcfcfcf0c0f0c0fcfcfcfcf0c0f0c0 5 := dualLower (by decide +kernel) (by decide +kernel) q11d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q12d : Lower (varsOf 45) 0xfaa0faa0a0a0a0a0faa0faa0a0a0a0a0 5 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (3, 4), (1, 2), (2, 3), (0, 1)]) (roots2 := lb2) (T2 := lb545) _ lb569
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q12 : Lower (varsOf 45) 0xfafafafafaa0faa0fafafafafaa0faa0 5 := dualLower (by decide +kernel) (by decide +kernel) q12d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q13d : Lower (varsOf 30) 0xfff0c000fff0c000fff0c000fff0c000 5 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (2, 3), (0, 1), (1, 2)]) (roots2 := lb521) (T2 := lb517) _ lb539
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q13 : Lower (varsOf 30) 0xfffcf000fffcf000fffcf000fffcf000 5 := dualLower (by decide +kernel) (by decide +kernel) q13d
def lb576 : Nat := 0xfff0ff00fff00000fff0ff00fff00000
def lb601 : List Nat := [20,20,24,24,28,40,40,44,44,52,52,56,20,20,20,24,24,24,40,40,40]
def lb599 : List Nat := [16,4,16,8,12,32,8,36,12,48,36,48,12,36,48,12,36,48,12,36,48]
def lb582 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7793,0xdb592),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f89fc,0x49158),(0xffff0000ffff0000ffff0000ffff0000,0x3fe1f,0x124a05),(0xffffffff00000000ffffffff00000000,0x1c0fe0,0x1b6ea0)]
def lb579 : Array Decor := buildWires lb582 lb82
def lb577 : Array (Option BoundPool) := buildPools lb579 lb11 lb510 lb81
lemma lb597 : goodPairs lb576 lb601 lb599 := goodPairs_of (by decide +kernel)
lemma lb583 : ∀ x ∈ lb582, faithful lb601 lb599 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb580 : ∀ x ∈ lb579.toList, faithful lb601 lb599 x ∧ x.1 < 2^128 := buildWires_faithful lb583
lemma lb581 : ∀ sw ∈ lb435.toList, swapsValid sw = true ∧ permWord sw lb576 = lb576 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma lb602 : ∀ i (hi : i < lb510.size), Slice lb11 lb576 lb510[i].1 lb510[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb11 lb576 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb578 : ∀ i (hi : i < lb577.size), ∀ c, lb577[i] = some c → ValidPool lb11 lb576 c := buildPools_sound lb602
lemma lb590 : ∀ i (hi : i < lb449.size), ∀ xs ∈ lb449[i], Impossible lb576 (0 - 1) xs.toFinset := by intro i hi; simp [lb449] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb591 : checkNodes lb579 lb576 lb32 lb577 lb435 lb449 0 lb492 = true := by decide +kernel
def lb584 : Array (List (List Nat)) := buildBuckets 1 lb579 lb492
lemma lb585 : ∀ i (hi : i < lb584.size), ∀ xs ∈ lb584[i], Impossible lb576 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb597 lb580 lb578 lb581 lb590 lb591
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb592 : checkNodes lb579 lb576 lb32 lb577 lb435 lb584 1 lb492 = true := by decide +kernel
lemma lb586 : ∀ i (hi : i < lb584.size), ∀ xs ∈ lb584[i], Impossible lb576 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb597 lb580 lb578 lb581 lb585 lb592
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb593 : checkNodes lb579 lb576 lb32 lb577 lb435 lb584 2 lb492 = true := by decide +kernel
lemma lb587 : ∀ i (hi : i < lb584.size), ∀ xs ∈ lb584[i], Impossible lb576 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb597 lb580 lb578 lb581 lb586 lb593
def lb600 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb594 : checkNodes lb579 lb576 lb32 lb577 lb435 lb584 3 lb600 = true := by decide +kernel
def lb588 : Array (List (List Nat)) := buildBuckets 1 lb579 lb600
lemma lb589 : ∀ i (hi : i < lb588.size), ∀ xs ∈ lb588[i], Impossible lb576 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb597 lb580 lb578 lb581 lb587 lb594
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb596 : forestRootCheck lb11 lb576 [(VAR 2,20,16),(VAR 3,24,16),(VAR 4,20,4),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb595 : bucketContains lb588 lb11 = true := by decide +kernel
lemma lb598 : Lower lb11 lb576 4 := lower_of_forest lb596 lb589 lb595
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q14 : Lower (varsOf 60) 0xfff0f0f0ff00f000fff0f0f0ff00f000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4)]) (roots2 := lb11) (T2 := lb576) _ lb598
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q15 : Lower (varsOf 58) 0xffccccccffcc0000ffccccccffcc0000 4 := by
  apply carry_of (swaps := [(2, 3), (1, 2)]) (roots2 := lb11) (T2 := lb576) _ lb598
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q16 : Lower (varsOf 54) 0xfcfcfcfccccc0000fcfcfcfccccc0000 4 := by
  apply carry_of (swaps := [(4, 5), (1, 2), (2, 3), (1, 2)]) (roots2 := lb11) (T2 := lb576) _ lb598
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q17 : Lower (varsOf 46) 0xfcfcfcfcf000f000fcfcfcfcf000f000 4 := by
  apply carry_of (swaps := [(4, 5), (1, 2), (2, 3), (3, 4)]) (roots2 := lb11) (T2 := lb576) _ lb598
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q18 : Lower (varsOf 37) 0xfafafafaa0a0a0a0fafafafaa0a0a0a0 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1)]) (roots2 := lb548) (T2 := lb544) _ lb568
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q19 : Lower (varsOf 35) 0xeeeeeeee88888888eeeeeeee88888888 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2)]) (roots2 := lb548) (T2 := lb544) _ lb568
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q20 : Lower (varsOf 30) 0xffccf000ffccf000ffccf000ffccf000 4 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (3, 4), (2, 3)]) (roots2 := lb11) (T2 := lb576) _ lb598
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q21 : Lower (varsOf 25) 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00 4 := by
  apply carry_of (swaps := [(3, 4), (2, 3), (0, 1)]) (roots2 := lb548) (T2 := lb544) _ lb568
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q22 : Lower (varsOf 19) 0xeeee8888eeee8888eeee8888eeee8888 4 := by
  apply carry_of (swaps := [(3, 4), (0, 1), (1, 2)]) (roots2 := lb548) (T2 := lb544) _ lb568
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q23 : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0 4 := by
  apply carry_of (swaps := [(0, 1)]) (roots2 := lb548) (T2 := lb544) _ lb568
  decide +kernel
def s0NR : List Nat := varsOf 63
def s0NG : Nat := 0xfffefefeffeefaa8fffefefeffeefaa8
def s0NPos : List Nat := [3,3,3,3,3,3,5,5,5,5,7,7,7,7,7,9,9,9,9,11,11,11,12,12,12,12,12,12,12,12,13,14,14,14,14,14,17,17,17,17,17,17,18,18,18,18,18,18,18,18,19,19,19,21,21,21,21,22,22,22,22,22,23,24,24,24,24,24,24,24,24,25,25,26,26,26,28,28,28,28,28,33,33,33,33,34,34,34,34,34,34,34,34,35,35,35,36,36,36,36,36,36,36,36,37,37,38,38,38,38,41,41,42,42,44,49,49,49,49,50,50,50,50,52,52,52,52,56,56]
def s0NNeg : List Nat := [0,1,2,6,10,16,1,4,6,20,1,2,4,6,20,1,8,10,40,1,8,10,0,1,4,6,8,10,20,40,1,2,4,6,8,10,0,1,2,16,20,48,0,1,2,6,10,16,20,48,0,1,2,1,6,16,20,2,4,6,16,20,20,0,6,8,10,16,20,40,48,1,16,8,10,16,4,8,10,16,20,1,32,40,48,1,2,4,6,10,32,40,48,1,2,32,0,2,4,6,20,32,40,48,1,32,2,4,6,32,1,40,10,40,40,1,16,32,48,2,16,32,48,4,6,20,48,40,48]
def s0NMask : Nat := fullMask 129
def s0NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x78c300e01e018041fc03f0403fffff,0x84100202200800028082040888442),(0xcccccccccccccccccccccccccccccccc,0x7833c00ffe00e007e1ffc0f80387c3f,0x1081140a434044050a50704a8a22291c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x78043fff0001f0007fe0000fffc07fc0,0x3800181c018110116d41210313007388),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x18007c0000001ffff8000000fffff8000,0x800780400a0866260000400c2c370010),(0xffff0000ffff0000ffff0000ffff0000,0x1fff800000001fffffffffff000000000,0x165500090101189587183838010004220),(0xffffffff00000000ffffffff00000000,0x1fffffffffffe00000000000000000000,0x1c666a2e09c1c00600002020020040000)]
def s0NSteps : List (Nat × Nat × Nat) := [(0,0,1),(1,6,2),(1,2,3),(1,2,4),(1,7,3),(1,7,4),(3,6,2),(1,6,3),(3,6,3),(1,6,4),(1,3,5),(3,6,4),(1,6,5),(3,6,5),(1,0,1),(1,0,2),(1,0,3),(1,1,2),(2,20,3),(1,23,3),(1,1,3),(2,20,2),(1,0,4),(1,0,5),(3,1,21),(1,2,5),(1,1,5),(2,20,5),(2,21,5),(1,20,3),(1,21,4),(2,21,4),(2,23,3),(1,23,4),(2,23,4),(1,1,21),(2,41,5),(1,30,3),(1,30,4),(1,30,5),(2,2,3),(2,21,3),(2,1,3),(1,1,4),(2,1,4),(2,1,5),(1,41,3),(2,52,4),(2,52,5),(2,41,3),(1,41,4),(2,41,4),(3,2,35),(2,35,4),(1,20,4),(3,2,60),(2,20,4),(1,20,5),(3,2,63),(2,2,5),(2,2,4),(1,21,3),(1,21,5),(3,0,2),(1,69,1),(1,70,4),(1,70,3),(1,69,3),(1,69,4),(1,27,3),(1,27,4),(1,24,69),(1,62,69),(2,78,5),(3,0,3),(2,1,2),(1,81,4),(1,3,4),(1,26,4),(3,1,4),(3,2,49),(1,28,5),(2,28,5),(1,49,5),(3,1,28),(1,90,2),(2,91,3),(1,90,5),(1,4,5),(1,51,4),(3,2,4),(3,2,28),(3,3,4),(1,3,28),(3,3,28),(3,0,4),(1,101,1),(1,102,2),(1,101,2),(1,27,101),(1,62,2),(2,106,5),(1,85,2),(3,1,2),(1,109,4),(1,109,28),(3,109,28),(0,20,2),(1,113,4),(0,20,4),(1,115,2),(1,115,3),(1,9,5),(2,9,5),(2,2,28),(1,65,4),(1,25,4),(1,38,4),(3,23,4),(3,3,39),(1,39,5),(2,39,5),(1,23,5),(2,23,5),(1,129,4),(1,98,2),(1,98,23),(3,81,20),(1,46,4),(1,83,5),(1,84,5),(1,26,5),(1,50,2),(3,20,2),(0,20,28),(1,46,49),(0,2,28),(2,2,49),(1,143,20),(0,1,28),(3,145,20),(1,145,2),(1,145,5),(3,4,87),(3,51,20),(1,51,2),(1,151,4),(1,1,114),(1,139,4),(3,1,35),(3,1,63),(3,4,63),(1,8,4),(1,46,1),(2,0,4),(1,160,5),(2,26,4),(1,160,109),(2,25,4),(3,4,137),(3,160,41),(1,160,139),(1,66,1),(1,65,1),(3,0,5),(2,0,5),(3,1,3),(1,172,0),(1,172,2),(1,85,0),(1,24,2),(3,0,25),(3,0,39),(1,109,0),(2,179,4),(1,109,3),(2,0,110),(3,3,56),(2,56,5),(2,20,110),(3,109,4),(3,109,0),(1,187,4),(3,109,20),(3,109,35),(2,190,4),(1,59,109),(1,24,109),(3,109,60),(1,62,109),(2,195,5),(1,27,5),(0,35,4),(3,20,4),(0,20,3),(0,20,23),(3,20,3),(1,202,2),(1,202,23),(0,2,35),(2,35,5),(0,23,35),(2,3,4),(1,35,5),(3,24,2),(1,0,210),(1,24,5),(2,24,5),(3,115,3),(1,115,5),(1,199,2),(3,2,3),(3,3,63),(1,33,3),(1,217,5),(1,217,20),(3,217,20),(0,2,3),(1,0,223),(2,20,223),(1,223,4),(1,223,5),(1,217,0),(1,96,0),(1,96,20),(3,96,20),(3,0,9),(1,98,0),(1,66,0),(3,66,20),(3,23,3),(1,236,0),(0,0,25),(1,238,4),(1,238,5),(1,25,5),(2,25,5),(1,124,0),(0,0,39),(1,244,5),(1,40,3),(1,129,3),(0,3,4),(1,0,248),(1,20,248),(2,20,248),(1,2,248),(1,23,248),(1,208,20),(3,208,20),(1,208,23),(3,2,16),(1,133,4),(1,81,3),(3,81,35),(3,81,60),(3,85,41),(1,27,85),(0,20,49),(1,62,5),(1,143,0),(1,65,49),(3,50,20),(1,268,5),(1,138,3),(1,50,3),(1,271,5),(1,50,5),(3,50,41),(3,50,35),(3,50,63),(3,1,5),(1,113,3),(1,1,278),(3,113,35),(3,113,60),(0,41,5),(1,202,1),(1,42,202),(3,115,41),(2,285,5),(3,115,56),(3,1,52),(3,1,56),(1,41,5),(3,1,290),(2,42,1),(1,42,20),(1,139,3),(3,139,4),(0,41,3),(1,1,296),(3,296,52),(0,52,4),(3,282,52),(3,41,3),(1,301,1),(1,52,4),(2,303,5),(0,52,5),(1,52,5),(1,55,1),(1,55,4),(2,55,4),(1,55,5),(2,55,5),(1,1,248),(0,41,4),(3,41,4),(3,3,290),(1,4,290),(3,4,290),(1,42,3),(2,318,4),(1,42,4),(2,42,4),(2,42,2),(1,42,0),(1,42,1),(1,42,2),(0,318,4),(3,42,3),(3,42,4),(1,42,248),(1,41,248),(2,330,5),(2,41,248),(2,332,5),(1,208,1),(1,208,41),(2,335,5),(3,208,41),(3,27,3),(1,0,338),(1,1,338),(1,1,75),(1,75,4),(2,75,4),(1,75,5),(3,2,344),(2,75,5),(2,27,3),(1,347,4),(1,347,5),(3,1,76),(3,27,4),(0,1,76),(1,1,76),(3,3,76),(1,76,5),(3,1,355),(2,76,5),(2,27,4),(1,358,3),(1,358,5),(3,3,197),(3,4,197),(1,322,3),(1,322,4),(1,217,1),(1,96,1),(1,27,248),(1,208,27),(1,98,27),(1,1,116),(3,115,2),(3,115,5),(3,115,60),(2,60,5),(1,3,60),(3,3,60),(1,60,5),(3,1,377),(1,62,3),(3,20,9),(3,8,60),(1,46,60),(2,382,5),(3,46,60),(0,2,60),(3,385,56),(2,2,60),(1,387,1),(1,61,3),(1,61,5),(2,61,5),(3,1,375),(1,376,2),(1,376,5),(3,1,394),(2,376,5),(1,60,16),(3,62,2),(1,1,106),(1,106,3),(2,400,5),(2,106,3),(1,106,5),(0,106,5),(3,2,379),(1,379,5),(3,2,406),(3,4,406),(2,379,5),(2,62,3),(3,2,265),(3,3,265),(2,62,5),(1,413,2),(1,413,3),(1,62,46),(2,416,5),(3,1,9),(1,62,96),(1,65,62),(1,62,248),(1,208,0),(1,208,2),(3,4,16),(0,20,5),(3,20,5),(1,1,223),(1,20,223),(3,223,4),(3,223,5),(3,0,8),(1,431,1),(2,1,8),(1,433,2),(3,1,8),(1,435,0),(3,20,8),(1,8,5),(1,46,0),(1,46,20),(2,440,5),(2,440,4),(3,46,20),(1,443,4),(0,2,4),(1,0,445),(1,1,445),(1,20,445),(2,20,445),(1,232,1),(2,1,9),(1,418,0),(3,98,20),(3,3,9),(1,454,1),(1,454,20),(2,456,5),(3,20,118),(1,119,1),(1,119,20),(3,96,5),(0,2,5),(1,0,462),(1,1,462),(1,464,3),(1,20,462),(1,466,3),(2,466,3),(2,20,462),(1,469,3),(2,470,4),(1,462,3),(2,467,4),(2,20,472),(3,462,3),(3,462,4),(1,65,0),(1,169,3),(1,293,3),(2,293,3),(1,293,4),(2,293,4),(3,65,20),(1,483,3),(1,483,4),(1,65,3),(3,2,5),(1,487,0),(1,487,1),(1,489,3),(1,487,20),(1,491,3),(2,491,3),(3,487,20),(1,494,3),(2,495,4),(1,487,3),(0,3,5),(2,3,5),(3,3,5),(0,4,5),(1,0,501),(1,1,501),(1,20,501),(2,20,501),(2,0,1),(1,506,2),(1,507,4),(2,507,4),(2,507,3),(1,172,507),(1,217,507),(3,507,3),(1,513,2),(1,512,4),(3,3,515),(2,512,4),(1,512,5),(2,512,5),(1,510,4),(1,510,5),(0,3,508),(3,507,4),(1,523,2),(1,508,5),(3,1,525),(3,3,525),(2,508,5),(1,509,3),(1,509,5),(1,507,5),(3,3,531),(3,4,531),(2,507,5),(1,534,3),(1,534,4),(3,3,536),(1,507,248),(1,208,507),(1,98,507),(3,1,94),(1,506,3),(1,506,4),(1,46,543),(3,3,543),(1,3,543),(1,543,5),(2,543,5),(2,2,543),(1,549,4),(3,2,543),(1,551,3),(1,551,5),(1,65,543),(3,3,554),(1,545,2),(1,545,5),(1,543,16),(3,2,547),(3,3,547),(1,548,2),(1,548,3),(1,506,5),(1,506,223),(1,46,506),(1,506,445),(1,98,506),(1,454,506),(3,506,118),(3,1,118),(1,119,506),(1,66,506),(1,96,506),(1,506,462),(1,574,3),(3,2,575),(1,65,506),(1,577,3),(1,487,506),(1,579,3),(1,506,501),(3,0,1),(1,582,2),(1,583,3),(1,583,4),(1,582,3),(1,582,4),(1,582,5),(3,582,25),(3,582,39),(0,0,2),(2,0,2),(0,0,3),(2,0,3),(0,0,4),(0,0,5),(0,1,2),(1,0,597),(1,598,3),(2,598,3),(1,598,4),(2,598,4),(1,598,5),(2,598,5),(1,597,3),(1,597,4),(1,597,5),(1,42,236),(2,42,236),(1,42,23),(2,0,23),(1,611,3),(1,611,4),(3,0,23),(1,614,3),(1,615,4),(2,615,4),(1,614,4),(1,614,248),(1,208,614),(1,173,2),(2,0,26),(3,0,26),(1,40,0),(2,26,5),(1,48,0),(1,626,2),(1,175,2),(0,1,4),(1,140,2),(1,629,3),(1,629,5),(1,175,5),(2,175,5),(1,85,5),(1,51,0),(1,636,3),(2,636,3),(1,51,3),(3,238,52),(2,0,25),(1,641,1),(1,641,2),(1,177,4),(2,177,4),(1,177,5),(2,177,5),(3,0,122),(1,122,5),(3,0,649),(2,122,5),(1,164,0),(1,164,5),(2,164,5),(1,38,0),(1,655,4),(2,655,4),(3,0,123),(1,323,3),(2,323,3),(1,323,4),(2,323,4),(3,0,247),(1,247,4),(2,247,4),(1,2,249),(2,23,249),(2,0,248),(3,0,253),(0,0,23),(1,670,3),(1,670,4),(1,670,83),(1,670,5),(1,611,83),(2,422,2),(3,0,256),(1,611,5),(1,611,16),(3,2,679),(1,0,16),(1,81,0),(1,682,3),(2,682,3),(1,682,4),(2,682,4),(2,0,259),(1,687,1),(3,81,3),(3,81,0),(1,690,3),(0,1,3),(2,140,2),(1,140,3),(2,694,4),(2,140,3),(1,696,5),(1,140,5),(2,140,5),(1,694,5),(2,694,5),(3,1,697),(2,0,629),(1,629,2),(2,0,704),(3,629,2),(1,631,5),(2,0,631),(1,708,5),(3,0,707),(3,629,3),(3,629,5),(2,0,49),(1,713,1),(1,713,2),(3,0,49),(1,716,2),(1,713,3),(1,713,8),(3,0,141),(1,86,0),(1,50,0),(1,722,2),(2,723,5),(2,722,2),(1,725,3),(1,722,3),(2,722,3),(1,728,2),(1,728,5),(1,722,5),(2,722,5),(1,732,3),(2,733,4),(0,1,5),(2,4,5),(3,4,5)]
def s0NW : BT Decor := buildWiresBT 10 s0NBase s0NSteps
def s0NAutoList : List (List (Nat × Nat)) := [[],[(2,3),(4,5)],[(1,2),(3,4)],[(1,2),(2,4),(3,4),(4,5)],[(1,3),(2,3),(3,5),(4,5)],[(1,3),(2,5)],[(1,4),(3,5)],[(1,4),(2,5),(3,5),(4,5)],[(1,5),(2,3),(3,4),(4,5)],[(1,5),(2,4)]]
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
def s0NSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 1 0,7),some (subcubeFast 8 0,7),some (subcubeFast 16 0,7),some (0xc3c3c3c300000000c3c3c3c3,7),some (0xcc330000cc330000cc330000cc33,7),some (0xf0000f00f0000f00f0000f00f0000f,7),some (0xf000f00000f000f0f000f00000f000f,7),some (0x33330000000033333333000000003333,7),some (subcubeFast 48 0,5),some (0x41414141414141414141414141414141,5),some (0xc300c300c300c300c300c300c300c3,5),some (0x44114411441144114411441144114411,5),some (0x50500505505005055050050550500505,5),some (0x30300303303003033030030330300303,5),some (0x55550000000055555555000000005555,5),some (subcubeFast 3 0,4),some (subcubeFast 5 0,4),some (subcubeFast 9 0,4),some (subcubeFast 17 0,4),some (subcubeFast 26 0,4),some (subcubeFast 28 0,4),some (subcubeFast 33 0,4),some (subcubeFast 38 0,4),some (subcubeFast 44 0,4),some (subcubeFast 50 0,4)]
def s0NSlices : BT (Option (Nat × Nat)) := btOfList 5 s0NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice0 : Slice s0NR s0NG (subcubeFast 1 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffcfcfcffccf000fffcfcfcffccf000) (by decide +kernel) q1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice1 : Slice s0NR s0NG (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefefefeeeeea8a8fefefefeeeeea8a8) (by decide +kernel) q2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice2 : Slice s0NR s0NG (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfefefefefaa8faa8fefefefefaa8faa8) (by decide +kernel) q3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice3 : Slice s0NR s0NG 0xc3c3c3c300000000c3c3c3c3 7 := mappedSlice (f := identifyRow 32 0 1 2) (R := varsOf 27) (G := 0xffeeee88ffeeee88ffeeee88ffeeee88) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice4 : Slice s0NR s0NG 0xcc330000cc330000cc330000cc33 7 := mappedSlice (f := identifyRow 16 0 1 3) (R := varsOf 39) (G := 0xfefefefee8e8e8e8fefefefee8e8e8e8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice5 : Slice s0NR s0NG 0xf0000f00f0000f00f0000f00f0000f 7 := mappedSlice (f := identifyRow 8 0 2 4) (R := varsOf 39) (G := 0xfefefefee8e8e8e8fefefefee8e8e8e8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice6 : Slice s0NR s0NG 0xf000f00000f000f0f000f00000f000f 7 := mappedSlice (f := identifyRow 4 0 3 5) (R := varsOf 27) (G := 0xffeeee88ffeeee88ffeeee88ffeeee88) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice7 : Slice s0NR s0NG 0x33330000000033333333000000003333 7 := mappedSlice (f := identifyRow 2 0 4 5) (R := varsOf 29) (G := 0xfffafaa0fffafaa0fffafaa0fffafaa0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice8 : Slice s0NR s0NG (subcubeFast 48 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 15) (qGoal := 0xfaa8faa8faa8faa8faa8faa8faa8faa8) (by decide +kernel) q7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice9 : Slice s0NR s0NG 0x41414141414141414141414141414141 5 := mappedSlice (f := identifyRow 1 0 1 2) (R := varsOf 58) (G := 0xffccccccffcccc00ffccccccffcccc00) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice10 : Slice s0NR s0NG 0xc300c300c300c300c300c300c300c3 5 := mappedSlice (f := identifyRow 8 0 1 2) (R := varsOf 51) (G := 0xeeeeeeeeeeee8888eeeeeeeeeeee8888) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice11 : Slice s0NR s0NG 0x44114411441144114411441144114411 5 := mappedSlice (f := identifyRow 1 0 1 3) (R := varsOf 54) (G := 0xfcfcfcfcccccc0c0fcfcfcfcccccc0c0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice12 : Slice s0NR s0NG 0x50500505505005055050050550500505 5 := mappedSlice (f := identifyRow 1 0 2 4) (R := varsOf 46) (G := 0xfcfcfcfcf0c0f0c0fcfcfcfcf0c0f0c0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice13 : Slice s0NR s0NG 0x30300303303003033030030330300303 5 := mappedSlice (f := identifyRow 2 0 2 4) (R := varsOf 45) (G := 0xfafafafafaa0faa0fafafafafaa0faa0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice14 : Slice s0NR s0NG 0x55550000000055555555000000005555 5 := mappedSlice (f := identifyRow 1 0 4 5) (R := varsOf 30) (G := 0xfffcf000fffcf000fffcf000fffcf000) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice15 : Slice s0NR s0NG (subcubeFast 3 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 60) (qGoal := 0xfff0f0f0ff00f000fff0f0f0ff00f000) (by decide +kernel) q14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice16 : Slice s0NR s0NG (subcubeFast 5 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffccccccffcc0000ffccccccffcc0000) (by decide +kernel) q15
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice17 : Slice s0NR s0NG (subcubeFast 9 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 54) (qGoal := 0xfcfcfcfccccc0000fcfcfcfccccc0000) (by decide +kernel) q16
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice18 : Slice s0NR s0NG (subcubeFast 17 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 46) (qGoal := 0xfcfcfcfcf000f000fcfcfcfcf000f000) (by decide +kernel) q17
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice19 : Slice s0NR s0NG (subcubeFast 26 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 37) (qGoal := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0) (by decide +kernel) q18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice20 : Slice s0NR s0NG (subcubeFast 28 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) q19
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice21 : Slice s0NR s0NG (subcubeFast 33 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xffccf000ffccf000ffccf000ffccf000) (by decide +kernel) q20
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice22 : Slice s0NR s0NG (subcubeFast 38 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 25) (qGoal := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00) (by decide +kernel) q21
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice23 : Slice s0NR s0NG (subcubeFast 44 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 19) (qGoal := 0xeeee8888eeee8888eeee8888eeee8888) (by decide +kernel) q22
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice24 : Slice s0NR s0NG (subcubeFast 50 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 13) (qGoal := 0xfaa0faa0faa0faa0faa0faa0faa0faa0) (by decide +kernel) q23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s0NR s0NG p.1 p.2) s0NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s0NR s0NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s0NSlice0) (forall_cons (fun _ h => by cases h; exact s0NSlice1) (forall_cons (fun _ h => by cases h; exact s0NSlice2) (forall_cons (fun _ h => by cases h; exact s0NSlice3) (forall_cons (fun _ h => by cases h; exact s0NSlice4) (forall_cons (fun _ h => by cases h; exact s0NSlice5) (forall_cons (fun _ h => by cases h; exact s0NSlice6) (forall_cons (fun _ h => by cases h; exact s0NSlice7) (forall_cons (fun _ h => by cases h; exact s0NSlice8) (forall_cons (fun _ h => by cases h; exact s0NSlice9) (forall_cons (fun _ h => by cases h; exact s0NSlice10) (forall_cons (fun _ h => by cases h; exact s0NSlice11) (forall_cons (fun _ h => by cases h; exact s0NSlice12) (forall_cons (fun _ h => by cases h; exact s0NSlice13) (forall_cons (fun _ h => by cases h; exact s0NSlice14) (forall_cons (fun _ h => by cases h; exact s0NSlice15) (forall_cons (fun _ h => by cases h; exact s0NSlice16) (forall_cons (fun _ h => by cases h; exact s0NSlice17) (forall_cons (fun _ h => by cases h; exact s0NSlice18) (forall_cons (fun _ h => by cases h; exact s0NSlice19) (forall_cons (fun _ h => by cases h; exact s0NSlice20) (forall_cons (fun _ h => by cases h; exact s0NSlice21) (forall_cons (fun _ h => by cases h; exact s0NSlice22) (forall_cons (fun _ h => by cases h; exact s0NSlice23) (forall_cons (fun _ h => by cases h; exact s0NSlice24) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))
def s0NEmpty : BT (List (List Nat)) := BT.empty
lemma s0NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG (4 - 1) xs.toFinset) s0NEmpty := trivial
def s0NBlock4_0Specs : List PoolSpec := []
def s0NBlock4_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NBlock4_0Specs
def s0NBlock4_0 : List NodeSpec := [([61,0,23,3,215],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock4_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock4_0Pools s0NAutos s0NEmpty 4 s0NBlock4_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock4_0Mem : ∀ ns ∈ s0NBlock4_0, Impossible s0NG 4 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NEmptyOk s0NBlock4_0Ok
def s0NNodes4 : List NodeSpec := s0NBlock4_0
def s0NBucket4 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 4 xs.toFinset) s0NBucket4 := buildBucketsBT_of_mem s0NBlock4_0Mem
def s0NBlock5_0Specs : List PoolSpec := []
def s0NBlock5_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NBlock5_0Specs
def s0NBlock5_0 : List NodeSpec := [([417,0,1,2,3,4],[],[]),([333,0,1,2,3,4],[],[]),([286,0,1,2,3,4],[],[]),([196,0,1,2,3,4],[],[]),([79,0,1,2,3,4],[],[]),([33,119,0,23,3,4],[],[]),([33,217,0,23,4,16],[],[]),([33,0,23,3,4,220],[],[]),([457,0,1,2,3,4],[],[]),([65,206,0,23,3,4],[],[]),([65,20,23,3,28,94],[],[]),([107,101,0,1,2,3],[],[]),([129,88,20,2,3,4],[],[]),([129,20,2,3,28,94],[],[]),([42,319,0,1,2,3],[],[]),([42,59,0,1,2,3],[],[]),([42,53,0,1,2,3],[],[]),([42,214,0,1,2,4],[],[]),([42,0,1,2,326,3],[],[]),([42,0,1,2,3,299],[],[]),([42,0,1,2,117,4],[],[]),([42,0,264,2,3,4],[],[]),([42,0,2,3,312,4],[],[]),([42,1,2,3,249,4],[],[]),([42,20,2,3,28,49],[],[]),([336,0,1,2,3,4],[],[]),([401,0,1,2,3,4],[],[]),([331,0,1,2,3,4],[],[]),([331,1,2,3,249,4],[],[]),([54,53,0,1,2,3],[],[]),([54,0,1,2,3,299],[],[]),([383,0,1,2,3,4],[],[]),([184,0,1,2,3,154],[],[]),([184,0,1,2,3,110],[],[]),([304,0,1,2,3,4],[],[]),([160,164,20,2,3,5],[],[]),([160,165,20,2,3,5],[],[]),([191,0,1,2,3,5],[],[]),([319,0,1,2,3,5],[],[]),([471,0,1,2,3,5],[],[]),([162,20,2,3,5,161],[],[]),([496,0,1,2,3,5],[],[]),([59,0,1,2,282,3],[],[]),([59,0,201,2,3,5],[],[]),([59,0,2,207,3,5],[],[]),([59,0,2,3,275,5],[],[]),([473,0,1,2,472,5],[],[]),([53,0,1,2,282,3],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock5_0Pools s0NAutos s0NBucket4 5 s0NBlock5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_0Mem : ∀ ns ∈ s0NBlock5_0, Impossible s0NG 5 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket4Ok s0NBlock5_0Ok
def s0NBlock5_1Specs : List PoolSpec := []
def s0NBlock5_1Pools : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NBlock5_1Specs
def s0NBlock5_1 : List NodeSpec := [([53,0,1,2,3,5],[],[]),([24,2,3,28,39,5],[],[]),([24,2,35,28,49,5],[],[]),([24,211,23,3,4,5],[],[]),([24,21,23,22,4,5],[],[]),([24,23,3,28,9,5],[],[]),([46,545,0,1,9,5],[],[]),([510,98,0,1,9,5],[],[]),([510,0,1,252,4,5],[],[]),([510,0,2,312,4,5],[],[]),([510,1,2,249,4,5],[],[]),([92,0,20,2,4,5],[],[]),([92,20,2,4,28,5],[],[]),([38,20,3,28,9,5],[],[]),([55,0,1,2,299,5],[],[]),([55,0,1,252,4,5],[],[]),([55,0,2,312,4,5],[],[]),([55,1,2,249,4,5],[],[]),([537,0,1,2,4,5],[],[]),([555,0,1,2,4,5],[],[]),([125,20,2,3,28,5],[],[]),([183,0,1,2,154,5],[],[]),([183,0,1,2,110,5],[],[]),([527,0,1,2,4,5],[],[]),([300,0,1,2,3,4],[],[]),([298,0,1,2,4,5],[],[]),([611,257,1,3,4,29],[],[]),([608,0,1,2,3,4],[],[]),([27,0,23,3,198,5],[],[]),([58,0,1,282,3,4],[],[]),([58,0,23,3,198,5],[],[]),([61,0,1,2,3,215],[],[0]),([61,0,1,3,154,5],[],[]),([61,0,1,3,110,5],[],[]),([61,0,115,23,3,5],[],[0]),([407,0,1,3,4,5],[],[]),([386,0,1,3,4,5],[],[]),([285,0,1,3,9,5],[],[]),([284,0,1,2,3,4],[],[]),([287,0,1,2,3,5],[],[]),([195,0,1,3,9,5],[],[]),([192,0,1,2,3,5],[],[]),([30,20,3,4,29,31],[],[]),([356,0,2,3,4,5],[],[]),([69,20,3,28,39,5],[],[]),([614,0,26,9,83,5],[],[]),([177,20,2,259,4,5],[],[]),([650,1,2,3,4,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_1Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock5_1Pools s0NAutos s0NBucket4 5 s0NBlock5_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_1Mem : ∀ ns ∈ s0NBlock5_1, Impossible s0NG 5 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket4Ok s0NBlock5_1Ok
def s0NBlock5_2Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(20,[]),(23,[]),(4,[]),(8,[]),(13,[])]
def s0NBlock5_2Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock5_2Specs
def s0NBlock5_2 : List NodeSpec := [([640,1,2,3,4,5],[],[]),([0,1,2,329,3,4],[],[]),([0,1,2,3,56,215],[5],[]),([0,1,41,3,9,215],[6],[]),([0,1,41,117,9,5],[6],[]),([0,268,41,3,9,5],[1],[]),([0,20,2,3,39,215],[],[]),([0,20,23,3,9,215],[],[]),([0,20,23,117,9,5],[],[]),([0,2,23,3,60,215],[],[0]),([0,23,3,9,63,94],[3],[]),([0,23,26,9,5,135],[0,4,7],[]),([0,23,26,9,16,94],[0,1,3],[]),([0,23,35,4,31,16],[3],[]),([0,23,35,9,83,5],[3],[]),([233,20,23,3,9,5],[0],[]),([1,112,20,3,9,5],[],[]),([70,20,3,28,9,5],[3],[]),([20,2,23,117,28,5],[],[]),([20,2,132,3,28,5],[],[]),([20,2,3,25,239,5],[],[]),([20,2,3,4,39,245],[],[]),([20,2,3,4,161,128],[],[]),([20,2,3,4,161,137],[],[]),([20,2,3,130,28,5],[],[]),([20,2,3,123,28,5],[],[]),([20,2,3,188,49,5],[],[]),([20,2,3,28,141,5],[],[]),([20,2,3,28,71,5],[],[]),([20,2,3,28,153,5],[],[]),([20,2,3,28,11,5],[],[]),([20,2,3,28,39,5],[],[]),([20,2,3,28,122,5],[2],[]),([20,2,3,28,5,136],[],[]),([20,2,3,111,49,5],[],[]),([20,2,3,111,71,5],[],[]),([20,2,3,111,39,5],[],[]),([20,2,26,4,161,16],[],[]),([20,2,26,134,28,5],[],[]),([20,2,26,28,5,135],[],[]),([20,2,26,28,16,94],[],[]),([20,131,23,3,28,5],[],[]),([20,108,23,3,28,5],[0],[]),([20,21,22,25,4,5],[2],[]),([20,147,3,28,11,5],[],[]),([20,23,116,3,28,5],[],[]),([20,23,3,4,161,31],[],[]),([20,23,3,121,28,5],[3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_2Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock5_2Pools s0NAutos s0NBucket4 5 s0NBlock5_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_2Mem : ∀ ns ∈ s0NBlock5_2, Impossible s0NG 5 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket4Ok s0NBlock5_2Ok
def s0NBlock5_3Specs : List PoolSpec := [(19,[])]
def s0NBlock5_3Pools : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NBlock5_3Specs
def s0NBlock5_3 : List NodeSpec := [([20,23,3,28,114,5],[],[]),([20,23,3,28,9,5],[0],[]),([20,3,25,28,9,5],[],[]),([2,23,35,28,83,5],[],[]),([2,3,35,28,39,5],[],[]),([23,3,35,28,9,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_3Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock5_3Pools s0NAutos s0NBucket4 5 s0NBlock5_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_3Mem : ∀ ns ∈ s0NBlock5_3, Impossible s0NG 5 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket4Ok s0NBlock5_3Ok
def s0NNodes5 : List NodeSpec := s0NBlock5_0 ++ s0NBlock5_1 ++ s0NBlock5_2 ++ s0NBlock5_3
def s0NBucket5 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 5 xs.toFinset) s0NBucket5 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append s0NBlock5_0Mem s0NBlock5_1Mem) s0NBlock5_2Mem) s0NBlock5_3Mem)
def s0NBlock6_0Specs : List PoolSpec := [(19,[]),(22,[]),(3,[]),(6,[]),(20,[]),(12,[]),(1,[]),(9,[]),(3,[(1,0,1)]),(15,[]),(24,[]),(0,[(1,1,2),(2,23,5)]),(7,[(1,506,2),(2,507,5)])]
def s0NBlock6_0Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_0Specs
def s0NBlock6_0 : List NodeSpec := [([413,65,0,1,2,3,4],[],[4]),([413,0,1,2,3,9,5],[2,10],[]),([654,0,1,2,3,4,5],[3],[]),([213,0,2,23,3,4,5],[3],[]),([311,42,0,1,2,3,4],[],[]),([311,0,1,2,3,4,5],[],[]),([396,0,1,2,3,4,5],[],[]),([322,0,1,2,3,4,16],[6],[]),([292,42,0,1,2,3,4],[],[]),([292,42,0,20,2,3,4],[1],[]),([292,42,0,2,23,3,4],[1],[]),([292,42,0,2,41,3,4],[1],[]),([634,0,2,23,3,4,5],[],[]),([51,34,0,20,2,3,4],[],[]),([33,65,0,1,41,3,4],[2],[]),([33,65,0,20,23,3,4],[],[]),([33,65,0,23,3,4],[1,8],[]),([33,34,0,1,2,3,4],[8],[]),([33,129,0,20,2,3,4],[1],[]),([33,42,0,1,2,3,4],[],[]),([33,217,0,23,3,4,5],[],[0]),([33,0,2,23,3,4,63],[1],[]),([33,0,2,23,3,4,16],[],[0]),([33,0,23,3,4,9,5],[0],[0]),([33,1,2,21,3,4,29],[7,8],[]),([33,20,2,3,4,28,32],[9],[]),([33,20,2,3,28,49,5],[9],[]),([441,0,1,20,2,3,4],[],[]),([441,0,1,440,2,3,4],[2],[]),([441,0,1,2,3,4],[],[]),([65,160,20,23,3,4,5],[],[]),([65,24,0,23,3,4,5],[3],[]),([65,0,1,2,3,543,94],[5],[]),([65,0,1,106,3,4,5],[2],[]),([65,0,1,507,3,4,94],[],[]),([65,0,20,2,3,49,94],[],[]),([65,0,20,23,3,4,94],[4],[0]),([65,0,23,3,35,4,5],[4],[0]),([65,20,23,3,4,28,5],[4],[0]),([107,62,0,1,2,3,4],[],[]),([107,0,1,20,2,3,4],[],[6]),([107,0,1,2,106,3,4],[2],[]),([107,0,1,2,3,4],[],[0,6]),([107,0,1,2,3,4,5],[],[]),([534,0,1,2,3,4,94],[12],[]),([724,0,722,1,2,3,4],[],[]),([129,160,20,2,3,4,5],[11],[]),([129,0,20,2,3,4,16],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_0Pools s0NAutos s0NBucket5 6 s0NBlock6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_0Mem : ∀ ns ∈ s0NBlock6_0, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_0Ok
def s0NBlock6_1Specs : List PoolSpec := [(22,[]),(0,[]),(3,[]),(6,[]),(1,[]),(24,[]),(0,[(1,1,2),(2,23,5)]),(9,[(2,41,5)]),(0,[(1,20,2),(2,41,5)]),(6,[(1,0,1),(2,41,5)])]
def s0NBlock6_1Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_1Specs
def s0NBlock6_1 : List NodeSpec := [([129,0,20,2,3,4,94],[5,6],[0]),([129,20,2,3,4,28,5],[],[0]),([42,160,1,20,2,3,4],[],[]),([42,50,0,20,2,3,4],[],[]),([42,62,0,1,2,3,4],[],[]),([42,208,0,1,2,3,4],[],[]),([42,24,0,1,2,3,4],[],[]),([42,55,0,1,2,3,4],[],[]),([42,301,0,1,2,3,4],[],[0]),([42,236,0,1,2,3,4],[],[0,7]),([42,27,0,1,2,3,4],[],[]),([42,27,0,1,41,3,4],[0],[]),([42,202,0,1,2,3,4],[0],[0]),([42,199,0,1,2,3,4],[],[]),([42,30,0,20,2,3,4],[0],[]),([42,30,0,2,23,3,4],[0],[]),([42,85,0,1,2,3,4],[],[]),([42,85,0,2,23,3,4],[0],[]),([42,0,323,1,2,3,4],[],[]),([42,0,682,1,2,3,4],[],[]),([42,0,1,324,2,3,4],[],[]),([42,0,1,113,41,3,4],[7],[]),([42,0,1,115,2,3,4],[0],[0,4]),([42,0,1,20,2,3,4],[],[]),([42,0,1,293,2,3,4],[],[]),([42,0,1,2,507,3,4],[],[]),([42,0,1,2,296,3,4],[],[1]),([42,0,1,2,41,3,4],[2],[]),([42,0,1,2,248,3,4],[0,8,9],[0,2]),([42,0,1,2,327,3,4],[],[]),([42,0,1,2,3,318,4],[],[0]),([42,0,1,2,3,35,4],[],[0,1]),([42,0,1,2,3,25,4],[],[]),([42,0,1,2,3,52,4],[3],[0]),([42,0,1,2,3,4],[],[]),([42,0,1,2,3,4,49],[],[]),([42,0,1,2,3,4,60],[],[]),([42,0,1,2,3,4,83],[],[]),([42,0,1,2,3,4,63],[0],[]),([42,0,1,2,3,4,290],[1],[]),([42,0,1,2,3,4,16],[4],[]),([42,0,20,2,23,3,4],[0],[]),([42,0,20,2,3,4,49],[],[0]),([42,0,2,23,3,26,4],[0],[]),([42,1,20,2,3,4,28],[0],[0]),([409,0,1,2,3,4,5],[],[]),([346,0,1,2,3,4,5],[],[]),([701,0,1,2,631,4,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_1Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_1Pools s0NAutos s0NBucket5 6 s0NBlock6_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_1Mem : ∀ ns ∈ s0NBlock6_1, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_1Ok
def s0NBlock6_2Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(6,[]),(2,[]),(20,[]),(12,[]),(9,[]),(15,[]),(0,[(1,1,4)]),(0,[(1,1,3),(2,26,4)])]
def s0NBlock6_2Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_2Specs
def s0NBlock6_2 : List NodeSpec := [([701,1,140,2,3,4,5],[],[]),([206,0,2,23,3,4,5],[],[0]),([54,0,1,2,41,3,4],[1],[]),([357,0,1,2,3,4,5],[4],[]),([548,0,1,2,3,9,5],[3],[]),([88,20,2,23,3,4,5],[],[0,6]),([88,20,2,3,26,4,5],[],[]),([119,0,1,2,3,543,5],[6],[]),([119,0,1,507,3,4,5],[],[]),([119,0,20,23,3,4,5],[],[0,6]),([528,0,1,2,3,4,5],[],[]),([127,0,20,2,3,4,5],[],[1,6]),([184,0,1,20,2,3,4],[],[]),([184,0,1,2,3,4,9],[],[]),([651,0,1,2,3,4,5],[],[]),([309,0,1,2,3,4,5],[],[]),([387,61,0,1,3,4,5],[],[0,6]),([713,178,1,2,3,4,5],[],[]),([143,61,0,1,3,4,5],[],[0,6]),([143,20,2,3,28,49,5],[9],[0,6]),([120,20,23,3,4,28,5],[0,5],[6]),([182,1,20,2,3,110,5],[],[]),([160,50,20,2,3,9,5],[],[]),([160,66,20,23,3,4,5],[8],[]),([160,40,20,2,3,4,5],[],[]),([160,162,20,2,3,5],[0,10],[0]),([160,59,1,20,2,3,5],[],[]),([160,59,1,2,3,35,5],[0],[]),([160,24,2,23,3,4,5],[],[]),([160,46,20,2,26,4,5],[7],[]),([160,38,20,2,3,4,5],[7],[]),([160,1,20,2,3,154,5],[],[]),([160,1,20,2,3,110,5],[],[]),([160,1,144,2,3,4,5],[],[]),([160,169,20,2,3,4,5],[],[]),([160,168,20,2,3,4,5],[],[]),([160,159,20,2,3,4,5],[],[]),([160,70,20,2,3,4,5],[],[]),([160,20,2,151,3,4,5],[],[]),([160,20,2,138,3,4,5],[],[]),([160,20,2,23,3,4,5],[],[]),([160,20,2,3,25,4,5],[2],[0]),([160,20,2,3,4,39,5],[2],[0]),([160,20,2,3,4,5,128],[],[0]),([160,20,2,3,4,5,137],[],[0]),([160,20,2,26,4,5,16],[],[0]),([160,20,23,3,4,9,5],[0],[0]),([160,20,23,3,4,5,31],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_2Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_2Pools s0NAutos s0NBucket5 6 s0NBlock6_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_2Mem : ∀ ns ∈ s0NBlock6_2, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_2Ok
def s0NBlock6_3Specs : List PoolSpec := [(19,[]),(22,[]),(3,[]),(2,[]),(20,[]),(12,[]),(4,[]),(15,[]),(4,[(1,0,1)]),(24,[])]
def s0NBlock6_3Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_3Specs
def s0NBlock6_3 : List NodeSpec := [([160,2,23,3,35,4,5],[0],[]),([657,0,1,2,3,4,5],[],[]),([180,1,20,2,3,4,5],[],[]),([50,59,0,20,2,3,5],[],[]),([50,59,0,2,3,35,5],[3],[0]),([50,24,0,2,3,9,5],[],[]),([50,0,20,41,3,9,5],[1,5],[0]),([50,0,20,3,8,9,5],[],[]),([50,0,2,3,35,9,5],[4],[]),([185,0,1,2,3,110,5],[],[]),([62,208,0,1,2,379,5],[],[]),([62,424,0,1,2,3,5],[],[1,5]),([62,46,0,1,3,9,5],[],[1]),([62,86,0,20,2,3,5],[0],[]),([62,61,0,1,2,3,5],[],[]),([62,419,0,1,2,3,5],[],[]),([62,139,0,1,3,9,5],[],[0]),([62,380,0,1,2,3,5],[],[0]),([62,109,0,1,3,9,5],[],[0]),([62,90,0,2,3,49,5],[],[]),([62,90,0,2,3,60,5],[],[]),([62,90,20,2,3,28,5],[7],[]),([62,418,0,1,2,3,5],[],[]),([62,69,0,1,3,9,5],[],[]),([62,232,0,1,2,3,5],[],[]),([62,0,422,1,2,3,5],[8],[]),([62,0,229,1,2,3,5],[],[]),([62,0,1,20,3,252,5],[3],[]),([62,0,1,254,2,3,5],[6],[]),([62,0,1,230,2,3,5],[3],[]),([62,0,1,398,3,9,5],[],[]),([62,0,1,2,423,3,5],[],[]),([62,0,1,2,216,3,5],[],[]),([62,0,1,2,108,3,5],[],[]),([62,0,1,2,104,3,5],[],[]),([62,0,1,2,421,3,5],[],[]),([62,0,1,2,3,249,5],[],[]),([62,0,1,2,3,250,5],[3],[]),([62,0,1,2,3,252,5],[],[]),([62,0,1,2,3,121,5],[2],[]),([62,0,1,2,3,134,5],[2],[1]),([62,0,1,2,3,154,5],[],[]),([62,0,1,2,3,110,5],[2],[]),([62,0,1,2,3,74,5],[2],[]),([62,0,1,2,3,39,5],[2],[]),([62,0,1,2,3,56,5],[0,2],[]),([62,0,1,106,3,9,5],[9],[]),([62,0,1,23,3,9,5],[4],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_3Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_3Pools s0NAutos s0NBucket5 6 s0NBlock6_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_3Mem : ∀ ns ∈ s0NBlock6_3, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_3Ok
def s0NBlock6_4Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(6,[]),(2,[]),(12,[]),(9,[]),(15,[]),(8,[]),(4,[(1,0,1)]),(24,[])]
def s0NBlock6_4Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_4Specs
def s0NBlock6_4 : List NodeSpec := [([62,0,1,41,3,9,5],[5,10],[]),([62,0,1,3,252,5],[0,10],[]),([62,0,1,3,8,9,5],[0],[]),([62,0,168,2,3,4,5],[],[]),([62,0,334,20,2,3,5],[],[]),([62,0,366,20,2,3,5],[0],[]),([62,0,20,2,3,312,5],[],[]),([62,0,20,2,3,39,5],[0],[]),([62,0,20,23,3,9,5],[0],[]),([62,0,2,3,312,5],[10],[]),([62,0,2,3,26,28,5],[0,9],[]),([62,0,2,3,35,49,5],[0],[]),([62,229,1,20,2,3,5],[],[]),([62,1,20,2,3,249,5],[4],[]),([62,1,2,3,249,5],[0,10],[]),([62,20,2,23,3,28,5],[6],[]),([62,20,2,3,26,28,5],[7],[]),([62,20,2,3,28,49,5],[7],[]),([482,0,1,2,3,4,5],[],[]),([420,0,1,2,3,4,5],[],[4]),([442,0,1,2,3,4,5],[],[]),([66,0,1,106,3,4,5],[8],[]),([509,0,1,23,3,4,5],[3],[]),([509,0,1,3,8,4,5],[],[]),([40,24,0,2,3,4,5],[],[]),([40,0,2,3,35,4,5],[0],[]),([40,20,2,3,4,28,5],[0],[0]),([57,199,0,1,2,3,5],[],[0]),([57,85,0,1,2,3,5],[],[]),([57,85,0,2,23,3,5],[],[]),([57,0,1,2,3,49,5],[2],[]),([57,0,1,2,3,60,5],[2],[]),([57,0,20,2,3,49,5],[1],[]),([57,1,20,2,3,28,5],[6],[]),([208,614,0,2,26,4,5],[],[]),([208,0,1,2,3,5,265],[],[]),([208,0,1,2,75,4,5],[],[]),([208,0,2,23,35,4,5],[0],[]),([665,0,1,2,3,4,5],[],[]),([343,0,1,2,3,4,5],[],[]),([617,0,1,2,3,4,5],[],[]),([695,0,1,2,631,694,5],[4],[]),([695,1,140,2,3,694,5],[4],[]),([59,81,0,20,2,3,5],[9],[]),([59,81,0,2,3,35,5],[0],[]),([59,109,0,1,2,3,5],[],[0]),([59,69,0,1,2,3,5],[],[]),([59,0,722,1,2,3,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_4Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_4Pools s0NAutos s0NBucket5 6 s0NBlock6_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_4Mem : ∀ ns ∈ s0NBlock6_4, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_4Ok
def s0NBlock6_5Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(7,[]),(2,[]),(20,[]),(4,[]),(11,[]),(14,[]),(5,[(1,0,1),(1,1,2)])]
def s0NBlock6_5Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_5Specs
def s0NBlock6_5 : List NodeSpec := [([59,0,1,113,2,3,5],[],[0]),([59,0,1,2,21,3,5],[],[]),([59,0,1,2,23,3,5],[],[]),([59,0,1,2,3,28,5],[2],[]),([59,0,20,2,23,3,5],[],[0]),([59,0,20,2,3,49,5],[0],[]),([59,0,2,23,3,35,5],[0],[0]),([59,0,2,3,35,49,5],[0],[]),([59,1,20,2,3,28,5],[0,9],[]),([59,1,2,3,35,28,5],[0,9],[]),([517,0,1,2,3,4,5],[],[]),([164,0,1,2,3,122,5],[2],[]),([164,0,1,2,3,5,94],[3],[]),([164,0,20,2,3,4,5],[2],[0]),([53,0,1,20,2,3,5],[],[]),([53,0,1,2,41,3,5],[],[0]),([53,0,1,2,3,8,5],[],[]),([53,0,1,2,3,25,5],[],[]),([53,0,1,2,3,52,5],[6],[0,1]),([53,0,1,2,3,4,5],[],[]),([53,0,1,2,3,5],[],[]),([362,0,1,2,3,4,5],[],[]),([157,0,1,2,3,60,5],[2],[]),([157,0,20,2,3,49,5],[5],[]),([157,1,20,2,3,28,5],[10],[]),([533,0,1,2,3,4,5],[],[]),([641,177,1,2,3,4,5],[],[0]),([474,0,1,2,472,4,5],[],[]),([381,0,1,2,3,4,5],[],[]),([667,1,2,3,249,4,5],[],[]),([638,0,2,23,3,4,5],[4],[]),([660,0,1,2,3,4,5],[],[]),([24,69,0,23,3,4,5],[4],[]),([24,0,1,2,282,3,4],[1],[1]),([24,0,70,2,3,4,5],[],[]),([24,0,210,23,3,4,5],[11],[0]),([24,0,2,138,3,4,5],[],[]),([24,0,2,23,3,4,5],[4],[]),([24,0,2,23,35,4,5],[],[]),([24,0,2,3,4,39,5],[],[0]),([24,0,2,3,28,49,5],[8],[3]),([24,0,2,3,49,5,94],[],[]),([24,0,2,35,4,49,5],[],[0]),([24,0,176,23,3,4,5],[4],[]),([24,0,21,23,3,4,5],[7],[0]),([24,0,23,3,4,9,5],[0,7],[0]),([24,0,23,3,4,5,31],[4],[]),([24,179,1,2,3,4,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_5Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_5Pools s0NAutos s0NBucket5 6 s0NBlock6_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_5Mem : ∀ ns ∈ s0NBlock6_5, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_5Ok
def s0NBlock6_6Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(20,[]),(1,[]),(15,[]),(8,[]),(11,[])]
def s0NBlock6_6Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_6Specs
def s0NBlock6_6 : List NodeSpec := [([24,1,2,35,4,28,5],[8],[0]),([24,20,2,3,28,49,5],[8],[0]),([24,20,2,26,4,28,5],[6],[]),([24,2,23,3,4,28,5],[],[0]),([24,2,3,28,49,5],[0],[0]),([480,0,1,2,3,4,5],[],[]),([251,0,2,23,3,4,5],[6],[]),([493,0,1,2,3,4,5],[],[]),([46,545,0,1,2,4,5],[],[0,3]),([46,376,0,1,2,4,5],[],[2]),([46,0,1,3,4,508,5],[5],[]),([46,0,1,3,543,9,5],[],[0]),([46,0,20,21,26,4,5],[],[]),([46,20,2,3,28,49,5],[0],[0]),([46,20,2,26,4,28,5],[0],[0,6]),([402,0,1,2,3,4,5],[],[]),([416,0,1,2,3,4,5],[3],[0]),([510,98,0,1,2,4,5],[],[0,3]),([510,172,0,1,2,4,5],[],[]),([510,0,1,2,248,4,5],[],[0]),([510,0,1,2,26,4,5],[3],[]),([510,0,1,3,4,9,5],[],[0]),([47,0,1,2,35,4,5],[3,4],[]),([47,0,20,2,26,4,5],[],[]),([38,0,20,21,3,4,5],[2],[]),([38,0,20,3,4,9,5],[],[0]),([38,20,2,3,4,28,5],[0],[0]),([468,0,1,2,3,4,5],[],[]),([55,98,0,1,2,4,5],[],[2,4]),([55,301,0,1,2,4,5],[],[0]),([55,236,0,1,2,4,5],[],[]),([55,202,0,1,2,4,5],[],[]),([55,0,1,2,282,3,4],[1],[1]),([55,0,1,2,248,4,5],[],[0]),([55,0,1,2,3,4,5],[],[]),([55,0,1,2,25,4,5],[2],[]),([55,0,1,2,52,4,5],[2],[0]),([55,0,2,23,26,4,5],[0],[]),([332,0,1,2,3,4,5],[7],[0]),([98,0,1,2,3,508,5],[5],[]),([98,0,1,507,3,9,5],[],[0]),([98,0,20,23,3,9,5],[0],[0]),([98,20,2,23,3,28,5],[],[0]),([354,0,1,2,3,4,5],[],[]),([545,0,1,2,3,9,5],[],[0]),([545,0,1,2,4,5,16],[3],[]),([376,0,1,2,4,5,16],[3],[]),([454,0,1,2,3,543,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_6Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_6Pools s0NAutos s0NBucket5 6 s0NBlock6_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_6Mem : ∀ ns ∈ s0NBlock6_6, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_6Ok
def s0NBlock6_7Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(2,[]),(1,[]),(9,[]),(15,[]),(7,[(1,0,4)]),(0,[(1,507,4),(3,3,508)])]
def s0NBlock6_7Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_7Specs
def s0NBlock6_7 : List NodeSpec := [([454,0,1,507,3,4,5],[],[]),([516,0,1,2,507,4,5],[],[]),([516,0,1,2,3,4,5],[],[]),([516,0,1,2,4,543,5],[],[]),([516,0,1,2,4,9,5],[],[]),([516,0,1,2,4,508,5],[6],[]),([516,0,1,2,4,5],[10],[]),([125,0,1,2,25,4,5],[2],[]),([125,0,20,2,3,4,5],[],[0]),([125,0,2,23,26,4,5],[0],[]),([125,0,2,26,4,39,5],[],[]),([183,0,1,20,2,4,5],[],[]),([183,0,1,2,4,60,5],[],[]),([183,0,1,2,4,9,5],[],[]),([412,0,1,2,3,4,5],[5],[]),([361,0,1,2,3,4,5],[],[]),([218,0,2,23,3,4,5],[4],[]),([532,0,1,2,3,4,5],[],[]),([315,0,1,2,3,4,5],[],[]),([611,257,0,1,3,4,5],[],[0,2]),([611,177,1,2,3,4,5],[],[]),([611,1,2,3,4,29,16],[],[0]),([124,20,2,23,3,28,5],[0,9],[0]),([676,0,1,23,3,4,5],[3],[]),([27,257,0,1,3,4,5],[],[3,7]),([27,199,0,23,3,4,5],[],[]),([27,85,0,23,3,4,5],[],[]),([27,350,0,2,3,4,5],[],[]),([27,90,0,2,3,4,5],[],[]),([27,69,0,3,26,4,5],[],[]),([27,0,1,282,41,3,4],[3],[]),([27,0,1,3,252,4,5],[6],[]),([27,0,334,2,3,4,5],[6],[]),([27,0,365,2,3,4,5],[6],[]),([27,0,366,2,3,4,5],[],[]),([27,0,2,340,3,4,5],[],[]),([27,0,2,3,312,4,5],[],[]),([27,0,23,3,26,4,5],[0],[]),([27,0,23,3,35,4,5],[],[0]),([27,0,23,3,4,5,63],[],[]),([27,229,1,2,3,4,5],[],[]),([27,1,2,339,3,4,5],[],[1]),([27,1,2,3,249,4,5],[],[]),([27,1,21,3,22,4,5],[7],[1]),([27,20,2,3,28,49,5],[8],[]),([27,20,23,3,4,28,5],[8],[]),([368,0,1,2,3,4,5],[],[]),([225,0,23,3,4,5],[0,1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_7Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_7Pools s0NAutos s0NBucket5 6 s0NBlock6_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_7Mem : ∀ ns ∈ s0NBlock6_7, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_7Ok
def s0NBlock6_8Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(16,[]),(15,[]),(8,[]),(24,[]),(7,[(1,0,4)]),(7,[(2,20,2),(1,27,4)])]
def s0NBlock6_8Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_8Specs
def s0NBlock6_8 : List NodeSpec := [([369,0,1,2,3,4,5],[4],[]),([217,0,1,2,75,4,5],[],[]),([217,0,1,23,612,4,5],[],[]),([217,0,20,23,4,5,16],[],[0,7]),([217,0,23,3,4,5,63],[4],[]),([405,0,1,2,3,4,5],[],[]),([58,109,0,1,3,4,5],[],[]),([58,69,0,1,3,4,5],[],[]),([58,0,1,2,259,4,5],[],[]),([58,0,1,21,3,4,5],[2],[]),([58,0,1,23,3,4,5],[2],[]),([58,0,1,41,3,4,5],[2],[0]),([58,0,20,23,3,4,5],[],[]),([58,0,23,3,35,4,5],[],[0]),([96,0,1,2,3,76,5],[4,10],[]),([96,20,2,23,3,28,5],[0,9],[0]),([551,0,1,2,3,83,5],[],[]),([551,0,1,2,3,5,94],[3],[]),([86,0,20,2,3,28,5],[2],[]),([86,20,2,3,28,5],[0,5,8],[0]),([61,139,0,1,3,4,5],[],[0]),([61,109,0,1,3,4,5],[],[0]),([61,69,0,1,3,4,5],[],[]),([61,0,1,115,2,3,5],[],[0]),([61,0,1,2,3,4,5],[],[]),([61,0,1,21,3,4,5],[2],[]),([61,0,1,23,3,4,5],[2],[]),([61,0,1,41,3,4,5],[2],[]),([61,0,20,23,3,4,5],[],[0]),([411,0,1,2,3,4,5],[],[]),([64,0,1,21,3,4,5],[2],[]),([64,0,1,41,3,4,5],[2],[]),([64,0,20,23,3,4,5],[],[]),([64,0,23,3,4,5,63],[],[]),([257,0,20,23,3,4,5],[1],[7]),([559,0,1,2,3,4,5],[],[]),([139,20,2,3,28,49,5],[0],[0]),([167,1,20,2,3,4,5],[],[]),([285,0,1,2,3,4,5],[7],[0]),([214,0,1,2,41,4,5],[7],[0]),([214,0,20,2,23,4,5],[6],[]),([458,0,1,2,3,4,5],[],[]),([373,0,1,2,3,60,5],[],[]),([373,0,1,2,3,5],[],[]),([280,0,1,2,3,4,5],[],[]),([281,0,1,2,3,4,5],[],[]),([506,570,0,2,3,4,5],[],[6,7]),([506,177,1,2,3,4,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_8Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_8Pools s0NAutos s0NBucket5 6 s0NBlock6_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_8Mem : ∀ ns ∈ s0NBlock6_8, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_8Ok
def s0NBlock6_9Specs : List PoolSpec := [(19,[]),(0,[]),(3,[]),(6,[]),(7,[]),(9,[]),(15,[]),(8,[]),(18,[]),(14,[]),(0,[(1,2,4),(3,3,9)])]
def s0NBlock6_9Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_9Specs
def s0NBlock6_9 : List NodeSpec := [([506,178,1,2,3,4,5],[],[]),([506,233,1,2,3,9,5],[],[]),([506,179,1,3,4,9,5],[],[]),([506,436,1,2,3,4,5],[],[]),([506,452,1,2,3,4,5],[],[]),([506,1,2,3,110,111,5],[],[]),([577,0,1,2,3,4,94],[],[]),([571,0,1,2,3,4,5],[],[]),([146,20,2,3,4,28,5],[6],[]),([565,0,1,3,4,9,5],[],[]),([567,0,1,2,3,9,5],[],[]),([568,0,1,2,3,4,5],[10],[]),([109,0,1,3,4,508,5],[0],[]),([109,0,1,3,543,9,5],[8],[]),([109,1,20,3,28,9,5],[0],[0]),([109,20,2,3,28,49,5],[0],[0]),([163,1,20,2,3,4,5],[],[]),([195,0,1,2,3,4,5],[7],[0]),([193,0,1,2,3,4,5],[],[]),([30,0,20,2,282,3,4],[2],[]),([30,0,20,3,4,9,5],[],[4]),([30,0,20,3,4,5,31],[],[0]),([30,20,2,3,4,5,29],[5],[0]),([435,0,1,507,3,4,5],[],[]),([288,0,2,3,25,4,5],[1],[]),([288,0,2,3,52,4,5],[1],[]),([85,0,2,23,3,543,5],[],[]),([85,0,507,23,3,4,5],[5],[]),([85,20,2,23,3,28,5],[4],[0]),([350,0,2,3,4,76,5],[3],[]),([90,0,2,23,3,4,5],[2],[]),([90,20,2,3,4,5,87],[0,9],[]),([90,20,2,3,28,83,5],[8],[]),([418,0,1,2,3,543,5],[],[]),([418,0,1,507,3,4,5],[5],[]),([291,0,2,3,4,5,290],[1],[]),([541,0,2,507,3,4,5],[],[7]),([541,0,2,3,25,4,5],[3],[]),([378,0,2,3,4,543,5],[],[]),([378,0,2,3,4,5,547],[],[]),([263,0,1,2,3,4,5],[],[]),([582,232,0,23,3,4,5],[],[]),([582,0,432,2,3,4,5],[],[]),([582,0,450,2,3,4,5],[],[]),([69,0,1,3,75,4,5],[],[]),([69,0,1,3,4,76,5],[],[]),([69,0,20,3,25,4,5],[1],[]),([69,0,20,3,4,39,5],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_9Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_9Pools s0NAutos s0NBucket5 6 s0NBlock6_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_9Mem : ∀ ns ∈ s0NBlock6_9, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_9Ok
def s0NBlock6_10Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(6,[]),(7,[]),(20,[]),(1,[]),(8,[]),(10,[])]
def s0NBlock6_10Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_10Specs
def s0NBlock6_10 : List NodeSpec := [([69,0,23,3,35,4,5],[5],[]),([69,20,2,3,28,49,5],[0],[0]),([69,20,23,3,4,28,5],[5],[0,6]),([78,0,1,2,3,4,5],[7],[0]),([77,0,1,2,3,4,5],[2],[]),([614,0,334,2,3,4,5],[],[]),([614,0,2,3,312,4,5],[],[]),([614,0,2,26,4,83,5],[],[0]),([614,0,3,26,4,9,5],[],[0]),([614,1,2,3,249,4,5],[6],[]),([677,0,1,2,3,4,5],[],[]),([620,0,1,2,3,4,5],[],[]),([663,0,1,2,3,4,5],[],[]),([669,0,1,2,3,4,5],[],[]),([177,0,1,2,3,4,5],[],[]),([177,0,1,2,259,4,5],[4,8],[0]),([177,1,20,2,3,4,5],[2],[]),([177,1,2,41,3,4,5],[2],[]),([177,1,2,3,52,4,5],[2],[]),([177,20,2,23,3,4,5],[],[]),([177,20,2,3,25,4,5],[2],[]),([101,0,1,2,106,3,5],[],[0]),([101,0,20,2,3,39,5],[2],[0]),([101,0,20,23,3,9,5],[0],[0]),([658,0,1,2,3,4,5],[],[]),([720,0,1,2,3,4,5],[],[]),([232,0,1,583,3,4,5],[],[]),([232,0,20,23,3,4,5],[5],[]),([178,0,2,3,26,4,5],[],[]),([178,1,20,2,3,4,5],[2],[]),([178,1,2,3,4,60,5],[2],[]),([178,20,2,23,3,4,5],[],[]),([178,20,2,3,4,49,5],[1],[]),([178,20,2,3,4,39,5],[1],[]),([648,0,1,2,3,4,5],[],[]),([710,0,1,2,631,4,5],[],[]),([105,0,1,2,3,4,5],[3],[]),([187,1,2,3,35,4,5],[],[]),([187,20,2,3,4,49,5],[],[0]),([238,1,2,3,52,4,5],[],[0]),([238,20,2,3,25,4,5],[],[0,1]),([244,20,2,3,4,39,5],[1],[0]),([0,477,23,3,26,4,5],[0],[3]),([0,323,1,2,3,4,16],[],[]),([0,234,20,23,3,4,5],[4],[]),([0,624,2,3,26,4,5],[],[]),([0,652,1,2,3,4,5],[],[0]),([0,626,627,23,3,4,5],[1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_10Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_10Pools s0NAutos s0NBucket5 6 s0NBlock6_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_10Mem : ∀ ns ∈ s0NBlock6_10, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_10Ok
def s0NBlock6_11Specs : List PoolSpec := [(22,[]),(3,[]),(2,[]),(20,[]),(4,[]),(8,[]),(6,[(1,0,1),(2,41,5)]),(4,[(1,0,1),(2,20,2)])]
def s0NBlock6_11Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_11Specs
def s0NBlock6_11 : List NodeSpec := [([0,228,20,23,3,4,5],[],[]),([0,589,2,3,25,4,5],[],[]),([0,175,2,23,3,5,94],[3],[]),([0,175,628,23,3,4,5],[3],[]),([0,175,23,3,4,5,31],[],[]),([0,590,2,3,4,39,5],[],[]),([0,352,2,3,4,76,5],[7],[]),([0,1,262,2,3,4,5],[],[]),([0,1,190,2,3,4,5],[2],[0]),([0,1,194,2,3,4,5],[2],[]),([0,1,569,2,3,4,5],[],[]),([0,1,453,2,3,9,5],[],[]),([0,1,115,2,3,56,5],[4],[0]),([0,1,115,41,3,9,5],[0,5],[0]),([0,1,20,2,3,9,215],[3],[0]),([0,1,20,2,117,9,5],[3],[0]),([0,1,293,2,3,4,94],[],[]),([0,1,460,2,3,4,5],[],[4]),([0,1,440,3,4,9,5],[5],[]),([0,1,456,2,3,4,5],[1],[0,2]),([0,1,385,3,4,56,5],[],[0]),([0,1,2,414,3,4,5],[],[4]),([0,1,2,561,3,4,5],[],[]),([0,1,2,404,106,3,4],[],[4]),([0,1,2,643,259,4,5],[],[]),([0,1,2,729,3,4,5],[],[]),([0,1,2,131,3,543,5],[],[]),([0,1,2,556,3,4,5],[],[3]),([0,1,2,393,3,4,5],[],[2]),([0,1,2,507,522,4,5],[],[]),([0,1,2,539,3,4,5],[],[]),([0,1,2,540,3,4,5],[],[3]),([0,1,2,108,3,543,5],[],[]),([0,1,2,296,52,4,5],[4],[0]),([0,1,2,337,3,4,5],[],[]),([0,1,2,282,3,35,4],[1,5],[0]),([0,1,2,282,3,52,4],[5],[0]),([0,1,2,41,3,299,5],[4,5],[0]),([0,1,2,41,117,4,5],[5],[0]),([0,1,2,335,3,4,5],[1],[0]),([0,1,2,522,4,508,5],[],[3]),([0,1,2,3,363,4,5],[],[]),([0,1,2,3,733,4,5],[],[5]),([0,1,2,3,535,4,5],[],[]),([0,1,2,3,247,4,94],[2],[]),([0,1,2,3,318,4,5],[2,6],[0]),([0,1,2,3,562,4,5],[2],[]),([0,1,2,3,359,4,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_11Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_11Pools s0NAutos s0NBucket5 6 s0NBlock6_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_11Mem : ∀ ns ∈ s0NBlock6_11, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_11Ok
def s0NBlock6_12Specs : List PoolSpec := [(0,[]),(3,[]),(6,[]),(7,[]),(2,[]),(4,[]),(1,[]),(8,[]),(5,[(1,0,1),(2,20,2)]),(5,[(1,0,1),(2,20,4)])]
def s0NBlock6_12Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_12Specs
def s0NBlock6_12 : List NodeSpec := [([0,1,2,3,379,9,5],[],[]),([0,1,2,3,529,4,5],[],[]),([0,1,2,3,726,4,5],[],[]),([0,1,2,3,367,4,5],[6],[]),([0,1,2,3,470,4,5],[7],[0]),([0,1,2,3,384,4,5],[],[]),([0,1,2,3,552,4,5],[],[]),([0,1,2,3,389,4,5],[],[]),([0,1,2,3,619,4,5],[0],[]),([0,1,2,3,341,4,5],[4,8],[]),([0,1,2,3,495,4,5],[4],[0]),([0,1,2,3,484,4,5],[],[]),([0,1,2,3,719,4,5],[],[]),([0,1,2,3,400,4,5],[1,9],[0]),([0,1,2,3,538,4,5],[6],[]),([0,1,2,3,25,239,5],[],[0,3]),([0,1,2,3,299,52,5],[7],[0]),([0,1,2,3,330,4,5],[1,5],[0]),([0,1,2,3,52,4,5],[7],[0,1]),([0,1,2,3,4,364,5],[],[]),([0,1,2,3,4,536,5],[6],[0]),([0,1,2,3,4,348,5],[],[]),([0,1,2,3,4,520,5],[],[3]),([0,1,2,3,4,308,5],[],[2]),([0,1,2,3,4,554,5],[6],[0]),([0,1,2,3,4,544,5],[],[3]),([0,1,2,3,4,644,5],[],[]),([0,1,2,3,4,353,5],[],[]),([0,1,2,3,4,444,5],[5],[]),([0,1,2,3,4,485,5],[2],[]),([0,1,2,3,4,382,5],[1],[0,2]),([0,1,2,3,4,83,674],[],[]),([0,1,2,3,4,664,5],[],[]),([0,1,2,3,4,675,5],[],[]),([0,1,2,3,4,342,5],[5],[]),([0,1,2,3,4,616,5],[],[]),([0,1,2,3,4,673,5],[],[]),([0,1,2,3,4,515,5],[],[3]),([0,1,2,3,4,303,5],[1],[0,2]),([0,1,2,3,4,5,360],[],[]),([0,1,2,3,4,5,530],[4],[]),([0,1,2,3,4,5,653],[4],[]),([0,1,2,3,4,5,730],[],[]),([0,1,2,3,4,5,697],[3],[]),([0,1,2,3,4,5,521],[],[]),([0,1,2,3,4,5,310],[6],[]),([0,1,2,3,4,5,557],[],[7]),([0,1,2,3,4,5,394],[6],[7])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_12Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_12Pools s0NAutos s0NBucket5 6 s0NBlock6_12 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_12Mem : ∀ ns ∈ s0NBlock6_12, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_12Ok
def s0NBlock6_13Specs : List PoolSpec := [(19,[]),(0,[]),(3,[]),(6,[]),(2,[]),(23,[]),(1,[]),(18,[])]
def s0NBlock6_13Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_13Specs
def s0NBlock6_13 : List NodeSpec := [([0,1,2,3,4,5,553],[],[]),([0,1,2,3,4,5,403],[],[4]),([0,1,2,3,4,5,406],[3],[0,5]),([0,1,2,3,4,5,679],[],[2]),([0,1,2,3,4,5,344],[],[3]),([0,1,2,3,4,5,355],[3],[0]),([0,1,2,3,4,5,525],[6],[0,6]),([0,1,2,3,4,5,649],[1],[0]),([0,1,2,3,4,678,16],[1],[]),([0,1,2,3,4,197,94],[4],[]),([0,1,2,3,4,531,16],[6],[]),([0,1,2,3,121,543,5],[1],[]),([0,1,2,3,134,543,5],[1],[]),([0,1,2,3,613,49,5],[1],[]),([0,1,2,3,76,9,5],[3],[]),([0,1,2,3,76,5,94],[2],[]),([0,1,2,3,154,60,5],[1],[0]),([0,1,2,3,154,56,5],[5],[0]),([0,1,2,3,543,110,5],[1],[]),([0,1,2,3,543,550,5],[1],[]),([0,1,2,3,543,9,5],[1],[]),([0,1,2,3,543,39,5],[1],[]),([0,1,2,3,543,158,5],[1],[]),([0,1,2,3,543,5,118],[1],[]),([0,1,2,3,543,5,135],[1],[]),([0,1,2,3,543,16,94],[0],[]),([0,1,2,3,110,44,5],[],[]),([0,1,2,3,110,60,5],[1],[0]),([0,1,2,3,110,56,5],[5],[0]),([0,1,2,3,28,5,265],[],[]),([0,1,2,3,60,5,265],[],[]),([0,1,2,3,60,215],[0,7],[0]),([0,1,2,3,9,5,265],[3],[]),([0,1,2,3,9,5,547],[2],[]),([0,1,2,3,508,83,5],[6],[]),([0,1,2,3,508,5,94],[5],[]),([0,1,2,718,8,4,5],[1],[]),([0,1,2,379,4,5,16],[2],[]),([0,1,2,612,26,4,5],[1],[]),([0,1,2,612,25,4,5],[1],[]),([0,1,2,612,4,83,5],[1],[]),([0,1,2,612,4,5,16],[1],[]),([0,1,2,75,8,4,5],[1],[]),([0,1,2,75,4,83,5],[4],[]),([0,1,2,75,4,5,16],[2],[]),([0,1,2,181,35,4,5],[1],[]),([0,1,2,691,8,4,5],[1],[2]),([0,1,2,671,4,83,5],[1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_13Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_13Pools s0NAutos s0NBucket5 6 s0NBlock6_13 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_13Mem : ∀ ns ∈ s0NBlock6_13, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_13Ok
def s0NBlock6_14Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(7,[]),(2,[]),(4,[]),(1,[]),(9,[]),(8,[]),(24,[])]
def s0NBlock6_14Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_14Specs
def s0NBlock6_14 : List NodeSpec := [([0,1,2,683,25,4,5],[9],[2]),([0,1,2,631,4,5,709],[5],[5]),([0,1,2,694,4,5,707],[10],[]),([0,1,2,472,575,4,5],[4],[1]),([0,1,2,472,467,4,5],[3,10],[0,1,3]),([0,1,715,3,8,4,5],[2],[]),([0,1,106,3,4,9,5],[10],[]),([0,1,106,3,4,5,31],[3],[]),([0,1,423,507,3,4,5],[2],[]),([0,1,176,23,3,4,5],[3],[]),([0,1,131,507,3,4,5],[2],[]),([0,1,203,41,3,4,5],[2],[]),([0,1,216,41,3,4,5],[10],[]),([0,1,507,174,3,4,5],[2],[]),([0,1,507,108,3,4,5],[2],[]),([0,1,507,514,3,4,5],[2],[]),([0,1,507,524,3,4,5],[2],[]),([0,1,507,3,486,4,5],[],[]),([0,1,507,3,181,4,5],[7],[]),([0,1,507,3,252,4,5],[2],[0]),([0,1,507,3,25,4,5],[2],[]),([0,1,507,3,4,121,5],[],[]),([0,1,507,3,4,134,5],[],[]),([0,1,507,3,4,110,5],[],[]),([0,1,507,3,4,9,5],[2],[]),([0,1,507,3,4,39,5],[2],[]),([0,1,507,3,4,158,5],[2],[]),([0,1,507,3,4,5,438],[2],[7]),([0,1,507,3,4,5,118],[2],[7]),([0,1,507,3,4,31,16],[],[]),([0,1,507,3,110,5],[1],[]),([0,1,507,3,9,83,5],[],[]),([0,1,507,3,9,5,94],[1],[7]),([0,1,507,8,4,5,16],[],[7]),([0,1,108,41,3,4,5],[10],[]),([0,1,23,3,4,76,5],[4],[]),([0,1,23,3,4,508,5],[0],[]),([0,1,23,3,543,9,5],[0],[]),([0,1,41,3,4,76,5],[],[]),([0,1,41,3,4,114,5],[],[]),([0,1,41,3,4,5,197],[],[]),([0,1,3,615,4,9,5],[],[]),([0,1,3,8,4,508,5],[8],[]),([0,1,3,8,543,9,5],[],[]),([0,1,3,512,4,9,5],[6],[]),([0,169,20,2,3,4,94],[11],[6]),([0,459,20,2,3,4,5],[2],[6]),([0,388,2,3,4,543,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_14Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_14Pools s0NAutos s0NBucket5 6 s0NBlock6_14 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_14Mem : ∀ ns ∈ s0NBlock6_14, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_14Ok
def s0NBlock6_15Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(6,[]),(20,[]),(23,[]),(12,[]),(15,[]),(8,[]),(18,[]),(7,[(1,20,2)])]
def s0NBlock6_15Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_15Specs
def s0NBlock6_15 : List NodeSpec := [([0,168,2,3,4,543,5],[],[]),([0,168,507,3,4,5],[1],[]),([0,334,2,41,3,4,5],[5],[]),([0,642,2,3,25,4,5],[2],[]),([0,159,20,3,4,9,5],[0],[6]),([0,455,20,2,3,4,5],[2],[6]),([0,189,2,3,4,49,5],[2],[]),([0,70,20,3,4,9,5],[4],[0]),([0,70,2,3,35,4,5],[4],[]),([0,432,20,2,3,4,5],[2],[]),([0,450,20,2,3,4,5],[2],[]),([0,231,2,23,3,4,5],[],[]),([0,222,2,23,3,4,5],[],[]),([0,201,2,3,35,4,5],[9],[0]),([0,201,2,3,4,60,5],[],[]),([0,115,20,2,3,39,5],[1],[0]),([0,115,20,23,3,9,5],[1],[0]),([0,115,2,23,3,60,5],[],[0]),([0,115,2,41,3,49,5],[10],[]),([0,255,2,23,3,4,5],[3],[]),([0,235,2,3,4,49,5],[6],[]),([0,235,23,3,4,5],[1,7],[6]),([0,268,20,2,3,9,5],[],[0]),([0,268,2,41,3,4,5],[1],[0]),([0,140,23,630,3,4,5],[4],[]),([0,264,2,41,3,4,5],[8],[0]),([0,20,2,260,3,4,5],[],[]),([0,20,2,261,3,4,5],[],[]),([0,20,2,91,3,4,5],[],[0]),([0,20,2,23,3,198,5],[9],[0]),([0,20,2,23,117,4,5],[7],[0]),([0,20,2,256,3,4,5],[2],[]),([0,20,2,132,3,4,5],[2],[0]),([0,20,2,103,3,4,5],[2],[]),([0,20,2,274,3,4,5],[6],[]),([0,20,2,370,3,4,5],[2],[6]),([0,20,2,3,247,4,5],[2],[]),([0,20,2,3,271,9,5],[1],[]),([0,20,2,3,246,4,5],[2],[]),([0,20,2,3,43,4,5],[],[]),([0,20,2,3,72,4,5],[2],[]),([0,20,2,3,279,4,5],[2],[]),([0,20,2,3,275,4,5],[],[]),([0,20,2,3,270,4,5],[2],[]),([0,20,2,3,253,4,5],[2],[]),([0,20,2,3,25,4,5],[2],[]),([0,20,2,3,4,130,5],[],[0]),([0,20,2,3,4,123,5],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_15Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_15Pools s0NAutos s0NBucket5 6 s0NBlock6_15 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_15Mem : ∀ ns ∈ s0NBlock6_15, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_15Ok
def s0NBlock6_16Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(7,[]),(20,[]),(23,[]),(12,[]),(9,[]),(15,[]),(4,[(1,0,1)]),(24,[])]
def s0NBlock6_16Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_16Specs
def s0NBlock6_16 : List NodeSpec := [([0,20,2,3,4,44,5],[7],[]),([0,20,2,3,4,276,5],[],[]),([0,20,2,3,4,267,5],[2],[6]),([0,20,2,3,4,141,5],[2],[0]),([0,20,2,3,4,71,5],[2],[0]),([0,20,2,3,4,258,5],[],[]),([0,20,2,3,4,153,5],[2],[0]),([0,20,2,3,4,39,5],[2],[0]),([0,20,2,3,4,122,5],[2],[0]),([0,20,2,3,4,5,45],[],[]),([0,20,2,3,4,5,93],[],[]),([0,20,2,3,4,5,269],[8],[]),([0,20,2,3,4,5,272],[],[7]),([0,20,2,3,4,5,126],[2],[1,6]),([0,20,2,3,95,28,5],[2],[]),([0,20,2,3,82,28,5],[6],[]),([0,20,2,3,82,9,5],[6],[]),([0,20,2,3,154,49,5],[7],[0]),([0,20,2,3,154,71,5],[7],[0]),([0,20,2,3,110,49,5],[7],[0]),([0,20,2,3,110,39,5],[7],[0]),([0,20,2,3,28,49,5],[2],[]),([0,20,2,3,28,39,5],[2],[0,2]),([0,20,2,3,28,84,5],[0,2,9],[]),([0,20,2,3,49,5,265],[1],[]),([0,20,2,3,49,63,94],[10],[]),([0,20,2,3,49,16,94],[],[5,7]),([0,20,2,3,39,5,94],[],[6,7]),([0,20,2,271,4,5,16],[],[7]),([0,20,2,259,683,4,5],[7],[]),([0,20,2,259,8,4,5],[4],[]),([0,20,2,259,25,4,5],[4,7],[0]),([0,20,2,26,28,83,5],[],[]),([0,20,2,472,465,4,5],[5],[]),([0,20,138,3,4,9,5],[0],[6]),([0,20,176,23,3,4,5],[7],[]),([0,20,131,23,3,4,5],[],[0]),([0,20,203,23,3,4,5],[],[]),([0,20,216,23,3,4,5],[0],[]),([0,20,174,23,3,4,5],[3],[]),([0,20,108,23,3,4,5],[0],[0]),([0,20,104,23,3,4,5],[0],[]),([0,20,224,23,3,4,5],[0],[]),([0,20,21,3,25,4,5],[2],[0]),([0,20,23,116,3,4,5],[7],[0]),([0,20,23,3,252,4,5],[4],[]),([0,20,23,3,4,121,5],[4],[0]),([0,20,23,3,4,76,5],[8],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_16Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_16Pools s0NAutos s0NBucket5 6 s0NBlock6_16 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_16Mem : ∀ ns ∈ s0NBlock6_16, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_16Ok
def s0NBlock6_17Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(7,[]),(2,[]),(20,[]),(23,[]),(1,[]),(9,[]),(15,[]),(8,[]),(24,[]),(11,[])]
def s0NBlock6_17Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_17Specs
def s0NBlock6_17 : List NodeSpec := [([0,20,23,3,4,74,5],[7],[6]),([0,20,23,3,4,114,5],[],[0]),([0,20,23,3,4,9,5],[0],[0]),([0,20,23,3,4,5,197],[11],[]),([0,20,23,3,4,5,220],[],[0,1]),([0,20,23,3,4,5,118],[],[1,6]),([0,20,23,3,4,227],[0,1],[]),([0,20,23,3,4,31,16],[0],[0]),([0,20,23,3,28,9,5],[7],[]),([0,20,23,3,226,5],[0,1],[]),([0,20,23,3,9,83,5],[0],[0]),([0,20,23,3,9,5,94],[13],[0,1,6]),([0,20,116,370,3,4,5],[10],[6]),([0,20,3,25,4,9,5],[],[0]),([0,144,2,3,4,49,5],[2],[6]),([0,254,2,23,3,4,5],[3],[]),([0,221,2,23,3,4,5],[7],[]),([0,230,2,23,3,4,5],[3],[]),([0,205,23,3,35,4,5],[7],[]),([0,2,138,3,35,4,5],[0],[]),([0,2,507,3,312,4,5],[9],[0]),([0,2,260,3,35,4,5],[],[]),([0,2,207,3,35,4,5],[7],[0]),([0,2,23,3,219,4,5],[0],[]),([0,2,23,3,198,35,5],[7],[0]),([0,2,23,3,250,4,5],[7],[]),([0,2,23,3,4,5,212],[4],[]),([0,2,23,3,4,5,209],[7],[]),([0,2,23,3,4,63,94],[7],[0]),([0,2,23,612,26,4,5],[0],[]),([0,2,23,35,4,83,5],[0],[0]),([0,2,23,35,4,5,16],[7],[0]),([0,2,41,3,312,4,5],[8],[0,2]),([0,2,41,3,26,4,5],[8],[]),([0,2,3,26,39,5,94],[0,5],[5]),([0,2,3,275,35,4,5],[],[0]),([0,2,3,35,4,39,5],[14],[0]),([0,2,3,35,28,49,5],[6],[]),([0,2,3,35,49,5,94],[12],[5]),([0,507,23,3,26,4,5],[0],[]),([0,224,23,26,4,5],[0,1],[]),([0,21,23,3,35,4,5],[0,7],[]),([0,23,3,35,4,9,5],[7],[0]),([0,23,3,35,4,5,31],[7],[0]),([0,23,3,4,9,5,63],[7],[0]),([0,23,3,4,9,5,137],[0,7],[4]),([0,23,26,4,9,5,16],[7,8],[0,1]),([0,23,26,4,83,5,31],[0,7],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_17Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_17Pools s0NAutos s0NBucket5 6 s0NBlock6_17 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_17Mem : ∀ ns ∈ s0NBlock6_17, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_17Ok
def s0NBlock6_18Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(7,[]),(2,[]),(20,[]),(23,[]),(12,[]),(4,[]),(1,[]),(9,[]),(0,[(1,1,2)]),(15,[]),(8,[]),(0,[(1,1,4)]),(7,[(1,0,4)]),(21,[]),(13,[])]
def s0NBlock6_18Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock6_18Specs
def s0NBlock6_18 : List NodeSpec := [([0,23,26,226,5],[0,1],[]),([0,23,26,9,83,5],[0,6,7,18],[0,1,2,3]),([266,1,2,3,4,60,5],[3],[]),([266,20,2,3,4,49,5],[],[0]),([233,1,20,2,3,9,5],[5],[0]),([233,20,2,23,3,4,5],[4],[0]),([237,1,2,41,3,4,5],[2],[]),([237,20,2,23,3,4,5],[],[]),([243,20,2,23,3,4,5],[],[]),([229,1,2,507,3,4,5],[],[]),([229,20,2,23,3,4,5],[],[]),([179,1,20,3,4,9,5],[1,11],[]),([179,1,2,3,35,4,5],[10],[]),([179,20,2,3,4,49,5],[],[0]),([173,1,2,507,3,4,5],[],[]),([173,20,2,23,3,4,5],[],[]),([436,1,20,2,3,4,5],[2],[]),([175,20,2,23,3,4,5],[],[]),([452,1,20,2,3,4,5],[2],[]),([1,112,20,2,3,4,5],[],[0]),([1,140,2,3,4,5,697],[4],[5]),([1,20,2,166,3,4,5],[],[]),([1,20,2,3,4,111,5],[5],[0]),([1,20,2,3,4,161,31],[],[0]),([1,20,2,3,4,161,16],[],[0]),([1,20,2,3,134,28,5],[0],[0]),([1,20,2,3,154,28,5],[6],[0]),([1,20,2,3,154,111,5],[6],[0]),([1,20,2,3,110,28,5],[0],[0]),([1,20,2,3,110,111,5],[0],[0]),([1,20,2,3,28,114,5],[13],[0]),([1,20,2,3,28,39,5],[1],[]),([1,20,2,3,28,5,265],[17],[]),([1,20,21,22,8,4,5],[11],[0]),([1,20,23,3,28,9,5],[0],[]),([1,2,507,3,249,4,5],[10],[0]),([1,2,41,3,249,4,5],[9,14],[0,2]),([1,2,3,249,330,4,5],[9,14],[0,2]),([159,20,2,3,4,28,5],[0],[0,6]),([70,20,2,3,4,28,5],[6],[0]),([113,20,2,3,28,49,5],[0,15],[]),([113,20,23,3,4,28,5],[],[0]),([133,20,2,3,4,28,5],[8],[]),([115,20,2,23,3,28,5],[12,16],[0]),([140,20,2,3,28,49,5],[5,13],[]),([140,23,630,3,4,5],[1,6],[]),([150,20,2,3,4,28,5],[13],[]),([20,2,151,3,4,28,5],[],[6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_18Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_18Pools s0NAutos s0NBucket5 6 s0NBlock6_18 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_18Mem : ∀ ns ∈ s0NBlock6_18, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_18Ok
def s0NBlock6_19Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(7,[]),(2,[]),(20,[]),(12,[]),(9,[]),(3,[(1,0,1)]),(15,[]),(18,[]),(24,[]),(11,[]),(14,[])]
def s0NBlock6_19Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_19Specs
def s0NBlock6_19 : List NodeSpec := [([20,2,138,3,4,28,5],[3],[0,6]),([20,2,91,3,4,28,5],[6],[0]),([20,2,21,3,4,29,32],[7,8],[2]),([20,2,147,3,4,28,5],[6],[0,6]),([20,2,23,3,249,4,5],[5],[]),([20,2,23,3,4,28,5],[3],[0]),([20,2,23,3,4,5,161],[],[0]),([20,2,23,3,4,5,87],[3],[6]),([20,2,23,3,28,49,5],[0,1],[0]),([20,2,23,3,28,9,5],[5],[0]),([20,2,23,3,28,39,5],[0,1],[]),([20,2,23,3,28,83,5],[0],[0]),([20,2,23,3,28,5,94],[],[0,6]),([20,2,41,3,28,49,5],[1,7,11],[0]),([20,2,3,26,4,5,161],[],[0]),([20,2,3,26,28,5,94],[],[0,6]),([20,2,3,35,28,49,5],[0,12],[0]),([20,2,3,8,28,49,5],[0],[0]),([20,2,3,25,4,28,5],[10],[0]),([20,2,3,4,28,5,93],[13],[]),([20,2,3,4,28,5,128],[],[6]),([20,2,3,4,28,5,137],[],[0,6,7]),([20,2,3,4,28,148],[0,9,11],[6]),([20,2,3,4,28,32,87],[10],[8]),([20,2,3,4,161,32],[2,11],[0]),([20,2,3,95,28,5],[0,11,13],[6]),([20,2,3,82,28,5],[0,6,11],[0]),([20,2,3,28,49,60,5],[4,9],[]),([20,2,3,28,49,39,5],[0,1,5],[]),([20,2,3,28,49,5],[0,2,11],[0]),([20,2,3,28,49,5,63],[11,13],[]),([20,2,3,28,49,5,16],[0,11],[0,5,7]),([20,2,3,28,39,5],[0,1,2,5],[0,6]),([20,2,3,28,83,5,32],[],[0]),([20,2,3,28,84,5],[0,2],[0]),([20,2,26,4,28,5,16],[],[0,7]),([20,2,26,28,83,5],[0,9,10],[0]),([20,224,23,3,4,5],[0,1],[]),([20,21,23,3,22,4,5],[1,2],[0]),([20,147,3,4,28,5],[0,9,11],[0]),([20,23,3,4,28,36,5],[0,5,10],[2]),([20,23,3,4,28,5,31],[5],[6]),([20,23,3,28,9,5],[1,5,9,10],[0,6]),([2,23,3,249,250,4,5],[5],[]),([2,23,3,35,4,28,5],[0],[0]),([2,3,35,28,49,5],[0,12],[0,5]),([224,23,26,4,5],[0,1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_19Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_19Pools s0NAutos s0NBucket5 6 s0NBlock6_19 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_19Mem : ∀ ns ∈ s0NBlock6_19, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_19Ok
def s0NNodes6 : List NodeSpec := s0NBlock6_0 ++ s0NBlock6_1 ++ s0NBlock6_2 ++ s0NBlock6_3 ++ s0NBlock6_4 ++ s0NBlock6_5 ++ s0NBlock6_6 ++ s0NBlock6_7 ++ s0NBlock6_8 ++ s0NBlock6_9 ++ s0NBlock6_10 ++ s0NBlock6_11 ++ s0NBlock6_12 ++ s0NBlock6_13 ++ s0NBlock6_14 ++ s0NBlock6_15 ++ s0NBlock6_16 ++ s0NBlock6_17 ++ s0NBlock6_18 ++ s0NBlock6_19
def s0NBucket6 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 6 xs.toFinset) s0NBucket6 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append s0NBlock6_0Mem s0NBlock6_1Mem) s0NBlock6_2Mem) s0NBlock6_3Mem) s0NBlock6_4Mem) s0NBlock6_5Mem) s0NBlock6_6Mem) s0NBlock6_7Mem) s0NBlock6_8Mem) s0NBlock6_9Mem) s0NBlock6_10Mem) s0NBlock6_11Mem) s0NBlock6_12Mem) s0NBlock6_13Mem) s0NBlock6_14Mem) s0NBlock6_15Mem) s0NBlock6_16Mem) s0NBlock6_17Mem) s0NBlock6_18Mem) s0NBlock6_19Mem)
def s0NBlock7_0Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(7,[]),(20,[]),(23,[]),(12,[]),(9,[]),(3,[(1,0,1)]),(16,[]),(15,[]),(18,[]),(4,[(1,0,1)]),(24,[]),(14,[]),(0,[(1,1,2),(2,23,5)]),(0,[(1,20,2),(2,41,5)]),(6,[(1,0,1),(2,41,5)]),(7,[(1,20,2),(2,41,5)]),(0,[(1,1,2),(2,41,5)]),(5,[])]
def s0NBlock7_0Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_0Specs
def s0NBlock7_0 : List NodeSpec := [([413,0,1,2,3,4,5],[4,12,15],[0,1]),([322,0,1,2,3,4,5],[0,1,12],[0]),([732,0,1,2,3,4,5],[0,1,12,15],[0,5]),([51,160,20,2,3,4,5],[0,12,15],[0]),([51,0,20,2,21,3,4,5],[10,11,12],[0]),([51,0,20,2,3,4,28,5],[12,13],[0]),([51,20,2,3,4,28,5],[0,12,13,15],[0,6]),([604,0,1,2,3,4,5],[7,12,15],[]),([33,0,1,2,21,3,4,5],[9,10],[0,2]),([33,0,1,2,41,3,4,5],[1,9],[0,1,7]),([33,0,1,2,3,4,28,5],[12,15],[]),([33,0,1,2,3,4,60,5],[5,12],[]),([33,0,20,2,23,3,4,5],[1,12],[0,1]),([33,0,20,2,3,4,49,5],[12,15],[0,7]),([33,0,2,23,3,4,5],[1,5,10,12],[0,1]),([33,1,20,2,3,4,28,5],[0,2,12],[0]),([65,160,1,20,2,3,4,5],[12],[0]),([65,62,0,1,2,3,4,5],[0,1,12],[0]),([65,506,0,1,2,3,4,94],[5,6],[0,6]),([65,0,1,20,2,3,4,94],[6,15],[0,4,6,8]),([65,0,1,20,41,3,4,5],[1,11,12],[0]),([65,0,1,2,3,4,543,5],[4,13],[0]),([65,0,1,507,3,4,5],[1,11],[0]),([65,0,20,2,3,4,49,5],[15],[0,6]),([65,0,20,23,3,4,5],[0,1,6,10,12],[0]),([65,0,23,3,26,4,5],[0,1,6],[0,1,3]),([534,0,1,2,3,4,5],[0,1,11],[0]),([129,0,1,2,3,4,83,5],[0,1],[0,7]),([129,0,1,2,3,4,16],[1,7,15,17],[0,2,5,7]),([129,0,20,2,3,4,5],[1,10,12,17],[0,1]),([42,0,1,20,2,41,3,4],[1],[0]),([42,0,1,20,2,3,4],[1,10,18],[0,1]),([42,0,1,20,2,3,4,5],[1,9],[0,1]),([42,0,1,2,23,41,3,4],[1,21],[0,2]),([42,0,1,2,23,3,4],[1,21],[0,2,7]),([42,0,1,2,41,3,4],[1],[0,1,2,4]),([42,0,1,2,41,3,4,5],[1,9],[0,1,4]),([42,0,1,2,3,4],[1,18,19,20],[0,1,2,4]),([42,0,1,2,3,4,5],[0,1,18,19,20],[0,1,2]),([548,0,1,2,3,4,5],[4,13,15],[0]),([374,0,1,20,2,3,4,5],[15,16],[1]),([119,506,0,1,2,3,4,5],[6,8],[0,6]),([119,0,1,20,2,3,4,5],[6,12,15],[0,1,4,6]),([451,0,20,2,3,4,9,5],[6,14],[0,6]),([358,0,1,2,3,4,9,5],[],[0,2]),([358,0,1,2,3,4,5],[7,12],[0,1,4,6]),([387,0,1,2,3,4,60,5],[3],[0,2,6]),([713,0,1,2,3,8,4,5],[2,22],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_0Pools s0NAutos s0NBucket6 7 s0NBlock7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_0Mem : ∀ ns ∈ s0NBlock7_0, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_0Ok
def s0NBlock7_1Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(7,[]),(20,[]),(12,[]),(9,[]),(3,[(1,0,1)]),(0,[(1,1,2)]),(16,[]),(15,[]),(18,[]),(4,[(1,0,1)]),(0,[(1,1,3)]),(0,[(1,1,4)]),(24,[]),(0,[(1,1,5)]),(0,[(1,20,3)]),(11,[]),(21,[])]
def s0NBlock7_1Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_1Specs
def s0NBlock7_1 : List NodeSpec := [([713,0,1,2,3,4,39,5],[2,6],[0,2,6]),([143,0,1,2,3,4,60,5],[3,16],[0,2,6]),([143,0,20,2,3,4,49,5],[8,16],[0]),([160,50,20,2,3,4,5],[0,12,17],[0]),([160,66,1,20,2,3,4,5],[12],[0]),([160,24,1,2,3,4,5],[0,20],[0]),([160,46,1,20,2,3,4,5],[12],[0]),([160,81,20,2,3,4,5],[0,12,14,17],[0]),([160,139,1,20,2,3,4,5],[0],[0]),([160,109,1,20,2,3,4,5],[0,2],[0]),([160,1,20,2,23,3,4,5],[1,12],[]),([160,1,20,2,41,3,4,5],[8,17],[0]),([160,1,20,2,3,35,4,5],[0,20],[0]),([160,1,20,2,3,8,4,5],[8],[0]),([160,1,20,2,3,4,60,5],[0,12,13],[]),([160,1,20,2,3,4,9,5],[6,8],[0,6]),([160,1,20,2,3,4,5,63],[5,21],[]),([160,1,20,2,3,4,5,31],[8],[0]),([160,1,20,2,3,4,5,16],[0],[0,5]),([160,1,2,3,35,4,5],[0,19,20],[0,5]),([160,20,2,23,3,4,5],[0,1,10,12],[0]),([160,20,2,3,26,4,5],[0,15,20],[0]),([160,20,2,3,4,49,5],[0,12,16,17],[0]),([160,20,2,3,4,5,32],[12,17,18],[0]),([686,0,1,2,3,4,5],[0,1,12,17],[4]),([50,24,0,2,3,4,5],[0,12],[0]),([50,96,0,20,2,3,5],[0,1,13],[]),([50,0,20,2,21,3,4,5],[9,11],[2]),([50,0,20,2,41,3,4,5],[1],[0]),([50,0,20,2,3,35,4,5],[0,12],[0]),([50,0,20,2,3,8,4,5],[5],[0]),([50,0,20,2,3,4,28,5],[12,13],[0]),([50,0,20,2,3,4,60,5],[0,12,13],[]),([50,0,20,2,3,4,9,5],[0,6],[0,6]),([50,0,20,2,3,4,5,63],[1],[0]),([50,0,20,2,3,4,5,16],[0],[0,5,7]),([50,0,20,2,3,9,5],[0,1,6],[0,2]),([50,0,2,3,35,4,5],[0,12],[0,5]),([50,20,2,3,4,28,5],[0,12,13,17],[0,6]),([549,0,1,2,3,4,543,5],[0,7],[0,2]),([62,66,0,1,2,3,4,5],[4,12],[0,2,6]),([62,208,0,1,20,2,3,5],[0],[0,1]),([62,208,0,1,2,3,5],[0],[0,1,3]),([62,46,0,1,2,3,4,5],[0,4,12],[0,1]),([62,96,0,1,20,2,3,5],[0],[0]),([62,96,0,1,2,3,5],[0,4,17],[0,6]),([62,139,0,1,2,3,4,5],[0,12],[0]),([62,199,0,1,2,3,5],[0,12,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_1Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_1Pools s0NAutos s0NBucket6 7 s0NBlock7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_1Mem : ∀ ns ∈ s0NBlock7_1, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_1Ok
def s0NBlock7_2Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(2,[]),(20,[]),(23,[]),(12,[]),(4,[]),(1,[]),(9,[]),(0,[(1,1,2)]),(16,[]),(15,[]),(8,[]),(18,[]),(4,[(1,0,1)]),(24,[]),(11,[]),(21,[]),(5,[(1,0,1),(1,1,2)]),(7,[(1,20,4)]),(5,[(1,0,1),(2,20,4)]),(5,[(2,0,1),(1,506,2)])]
def s0NBlock7_2Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_2Specs
def s0NBlock7_2 : List NodeSpec := [([62,109,0,1,2,3,4,5],[0,3,14],[0]),([62,85,0,1,2,3,5],[0,14,18],[0]),([62,69,0,1,2,3,4,5],[0,4,14],[0]),([62,101,0,1,2,3,5],[0,14,18],[0]),([62,0,1,20,2,248,3,5],[0],[0]),([62,0,1,20,2,3,9,5],[1,5],[0]),([62,0,1,398,2,3,4,5],[0,14],[0,4]),([62,0,1,2,106,3,4,5],[4,14,18],[0]),([62,0,1,2,21,3,4,5],[0,1,13,14],[2]),([62,0,1,2,23,3,4,5],[0,6,12,14],[0]),([62,0,1,2,41,3,4,5],[6,14,18],[0]),([62,0,1,2,248,3,5],[0,18],[0]),([62,0,1,2,3,379,4,5],[0,19],[0,1]),([62,0,1,2,3,8,4,5],[0,6,14,23],[0]),([62,0,1,2,3,4,60,5],[0,16],[]),([62,0,1,2,3,4,9,5],[0,4,11],[0,2]),([62,0,1,2,3,4,5],[0,1,14,18],[4,6]),([62,0,1,2,3,4,5,265],[3,14],[0]),([62,0,1,2,3,4,5,31],[1,11],[0]),([62,0,1,2,3,4,5,16],[7,18,19],[0,1]),([62,0,1,2,3,49,5],[0,14,18],[0]),([62,0,1,2,3,60,5],[0,14,22],[0,1]),([62,0,1,2,3,9,5],[0,1,17,18],[0,1,2]),([62,0,20,2,23,3,4,5],[0,12,14],[0]),([62,0,20,2,3,4,49,5],[0,14],[0]),([62,0,20,2,3,49,5],[0,14],[0,1]),([505,0,1,2,3,4,5],[0,1],[]),([66,0,1,20,41,3,4,5],[1,13,14],[]),([66,0,1,2,3,4,543,5],[0,2,8],[0,2]),([66,0,1,507,3,4,5],[1,13,24],[0]),([66,0,20,2,3,4,49,5],[0],[0,6]),([66,0,20,23,3,4,5],[0,1,14,21],[0,6]),([509,0,1,2,3,4,5],[7,13],[0,2]),([40,0,20,2,3,4,5],[0,1,14],[0,2]),([40,0,2,3,26,4,5],[0,1,6],[0,2,3]),([57,0,1,20,2,3,4,5],[1,11,14],[0]),([208,27,0,1,2,3,4,5],[10,14],[0,1]),([208,614,0,1,2,3,4,5],[1,10],[0]),([208,0,1,2,507,3,4,5],[10,13],[0]),([208,0,1,2,41,3,4,5],[1,9,15],[0,1,2]),([208,0,20,2,23,3,4,5],[0,1,6],[0]),([164,0,1,2,23,3,4,5],[0,6],[2]),([164,0,1,2,3,25,4,5],[0],[0,2]),([164,0,1,2,3,4,5],[0,6,20],[0,2,3,6]),([641,0,1,2,3,25,4,5],[2],[0,1]),([433,0,20,2,3,8,4,5],[6],[0,1]),([347,0,1,2,3,8,4,5],[],[0,1]),([347,0,1,2,3,4,5],[14,15],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_2Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_2Pools s0NAutos s0NBucket6 7 s0NBlock7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_2Mem : ∀ ns ∈ s0NBlock7_2, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_2Ok
def s0NBlock7_3Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(7,[]),(2,[]),(20,[]),(23,[]),(1,[]),(9,[]),(3,[(1,0,1)]),(0,[(1,1,2)]),(16,[]),(15,[]),(8,[]),(18,[]),(24,[]),(11,[]),(6,[(1,0,1)]),(5,[(1,0,1)]),(5,[(1,0,1),(1,1,2)]),(3,[(1,0,1),(2,20,3)]),(5,[(1,0,1),(1,20,2)]),(0,[(1,2,4),(3,3,9)]),(3,[(2,682,3)]),(3,[(2,0,259)])]
def s0NBlock7_3Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_3Specs
def s0NBlock7_3 : List NodeSpec := [([708,0,1,2,631,4,5],[7,14,15],[0]),([687,0,1,2,259,4,5],[0,1,14,26],[0,2,3]),([728,0,1,2,3,4,5],[0,4,14],[0,6]),([668,1,2,23,3,4,5],[0,8,12],[]),([684,0,1,2,3,4,5],[0,4,14,25],[2]),([48,0,20,2,21,3,4,5],[1,11,13,14],[]),([600,0,1,2,3,4,5],[7,8,14],[]),([696,0,1,2,3,4,5],[3,7,14],[0]),([696,1,140,2,3,4,5],[7,14,15],[0]),([24,81,0,2,3,4,5],[0,4,14,22],[0]),([24,109,0,1,2,3,4,5],[0,4,10,18,20],[0]),([24,69,0,1,2,3,4,5],[4,14],[0]),([24,0,1,2,21,3,4,5],[1,13,14],[0,1]),([24,0,1,2,23,3,4,5],[7,12,14],[0,1]),([24,0,1,2,41,3,4,5],[1,7],[0,1]),([24,0,1,2,3,4,28,5],[0,14],[0,3]),([24,0,20,2,23,3,4,5],[1,14],[0]),([24,0,20,2,3,4,49,5],[14],[0]),([24,0,2,23,3,4,5],[0,1,21],[0,1,3]),([24,0,2,3,4,49,5],[0],[0,3]),([24,1,20,2,3,4,28,5],[0,2,14],[0]),([24,1,2,3,4,28,5],[0,18],[0,6]),([46,506,0,1,3,4,9,5],[7],[0,6]),([46,0,1,20,3,4,9,5],[1,7],[0,1,6]),([46,0,1,2,3,4,543,5],[7,16],[0]),([46,0,1,2,3,4,60,5],[7],[0,1]),([46,0,1,507,3,4,5],[1,9,13],[0,2]),([46,0,20,2,3,4,49,5],[0],[0]),([46,1,20,2,3,4,28,5],[0],[0,6]),([510,0,1,2,3,4,5],[13,17],[0,1,2]),([38,0,20,2,3,4,5],[0,1,5,14],[0]),([55,0,1,20,2,3,4,5],[1,10,14],[0,1]),([55,0,1,2,23,3,4,5],[0,10,12],[0,2]),([55,0,1,2,41,3,4,5],[1,9,10],[0,1]),([55,0,1,2,3,4,5],[0,1,10,23],[0,1,2,4]),([98,27,0,1,2,3,4,5],[6,10],[0]),([98,506,0,1,2,3,9,5],[7],[0]),([98,0,1,20,2,3,9,5],[1,7],[0,4]),([98,0,1,2,507,3,4,5],[0,13],[0]),([98,0,1,2,3,543,5],[0,16,17],[0]),([98,0,20,2,23,3,4,5],[1,7,12],[0]),([545,0,1,2,3,4,5],[0,4,16],[0]),([376,0,1,20,2,3,4,5],[0,16],[1]),([376,0,1,2,3,4,60,5],[0,16],[1,3]),([376,0,1,2,3,4,5],[0,4],[0,1,3]),([454,506,0,1,2,3,4,5],[7,24],[0,6]),([454,0,1,20,2,3,4,5],[7,14],[0,1,6]),([301,0,1,2,41,3,4,5],[1,8,19],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_3Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_3Pools s0NAutos s0NBucket6 7 s0NBlock7_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_3Mem : ∀ ns ∈ s0NBlock7_3, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_3Ok
def s0NBlock7_4Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(7,[]),(2,[]),(20,[]),(23,[]),(4,[]),(1,[]),(9,[]),(0,[(1,1,2)]),(16,[]),(15,[]),(8,[]),(18,[]),(4,[(1,0,1)]),(0,[(1,1,4)]),(24,[]),(6,[(1,0,1)]),(3,[(1,0,1),(1,20,3)]),(7,[(2,20,2)]),(7,[(1,506,2)]),(6,[(1,0,23)]),(5,[])]
def s0NBlock7_4Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_4Specs
def s0NBlock7_4 : List NodeSpec := [([611,85,0,2,23,3,4,5],[0,10],[0,2,4]),([611,0,1,2,3,26,4,5],[2,9],[0,2]),([611,0,1,2,3,25,4,5],[0,2],[0,2]),([611,0,1,2,3,4,49,5],[2,5],[0]),([611,0,1,2,3,4,83,5],[2,8],[0,2]),([611,0,1,2,3,4,5,16],[7,12],[0]),([611,0,2,23,3,26,4,5],[0,1],[0,2]),([705,0,1,704,3,4,5],[1,6,13],[]),([236,0,1,2,41,3,4,5],[1,7,11,23],[0,1,2]),([236,0,20,2,23,3,4,5],[1,11,19],[0]),([124,0,20,2,23,3,4,5],[1,4,6,11],[0]),([725,0,1,2,3,4,5],[1,13,24],[0,1,6]),([81,0,175,2,3,4,5],[0,6,18],[]),([81,0,20,2,3,35,4,5],[0,13,16],[0]),([81,0,20,2,3,8,4,5],[6,10],[0]),([81,0,20,2,3,4,28,5],[0,10,15,16],[0]),([81,0,20,2,3,4,60,5],[0,16],[0]),([81,0,20,2,3,4,9,5],[4,6,16],[0,6]),([81,0,2,3,35,4,5],[0,13,20],[0,1]),([81,20,2,3,4,28,5],[0,13,15,16,18],[0,6]),([513,0,1,2,507,3,4,5],[12],[0,2]),([523,0,1,2,507,3,4,5],[1,12,22],[0,2]),([693,0,1,2,3,4,5],[1,6,13],[]),([693,1,140,2,3,4,5],[1,6,13],[]),([27,217,0,1,2,3,4,5],[9,10],[0,1]),([27,96,0,1,2,3,4,5],[1,5,10,21],[0]),([27,202,0,1,2,3,4,5],[1,19],[0,1]),([27,199,0,1,2,3,4,5],[0],[0]),([27,85,0,1,2,3,4,5],[0,10],[0]),([27,69,0,1,3,4,5],[1,13],[0]),([27,101,0,1,2,3,4,5],[5,10],[0]),([27,0,1,2,338,3,4,5],[1,13,19],[0,1,3]),([27,0,1,2,351,3,4,5],[10],[6]),([27,0,1,2,41,3,4,5],[1,10],[0]),([27,0,1,2,248,3,4,5],[1,9,13,19],[0]),([27,0,1,2,3,75,4,5],[9,10],[1]),([27,0,1,2,3,8,4,5],[9,10],[0]),([27,0,1,2,3,4,76,5],[5,13],[0]),([27,0,1,2,3,4,28,5],[0,13,15],[0]),([27,0,1,2,3,4,49,5],[0,13,17],[]),([27,0,1,2,3,4,60,5],[6],[0]),([27,0,1,2,3,4,9,5],[5,10],[0,2]),([27,0,1,2,3,4,83,5],[0,10],[0,1]),([27,0,1,2,3,4,5],[0,1,13],[1,3,6]),([27,0,1,2,3,4,5,197],[3,10],[0]),([27,0,1,2,3,4,5,63],[1],[0]),([27,0,1,2,3,4,5,16],[1,7,13],[0,1,7]),([27,0,1,2,3,4,5,94],[10,14],[0,1,7])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_4Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_4Pools s0NAutos s0NBucket6 7 s0NBlock7_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_4Mem : ∀ ns ∈ s0NBlock7_4, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_4Ok
def s0NBlock7_5Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(7,[]),(2,[]),(20,[]),(23,[]),(12,[]),(1,[]),(9,[]),(0,[(1,1,2)]),(16,[]),(15,[]),(8,[]),(18,[]),(0,[(1,1,4)]),(24,[]),(11,[]),(21,[]),(6,[(1,0,1)]),(4,[(1,0,1),(3,2,60)]),(7,[(1,20,4),(3,2,60)]),(7,[(1,506,2)]),(17,[]),(7,[(1,506,4)]),(0,[(1,4,5),(3,1,94)]),(13,[])]
def s0NBlock7_5Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_5Specs
def s0NBlock7_5 : List NodeSpec := [([27,0,1,23,3,4,5],[0,1,11],[0]),([27,0,1,41,3,4,5],[1,11,14],[0,1]),([27,0,20,2,23,3,4,5],[3,11],[]),([27,0,20,2,3,4,49,5],[14],[0]),([27,0,20,23,3,4,5],[0,1,14],[0,1]),([27,1,20,2,3,4,28,5],[0,2,14],[0]),([469,0,1,2,3,4,5],[1,10,14,18],[0,1]),([449,0,1,2,3,4,5],[0,1],[]),([225,0,1,2,3,4,5],[0,1,14],[0,1]),([217,0,1,2,507,3,4,5],[10,13],[2]),([217,0,20,2,23,3,4,5],[1],[0]),([217,0,20,23,3,4,5],[0,1,5,14],[0,1]),([475,506,0,1,2,4,5],[0,13,20],[]),([475,0,1,20,2,4,5],[0,1,13,18],[]),([96,0,1,2,507,3,4,5],[1,6,13,24],[0,2]),([96,0,1,2,3,543,5],[0,4,16,18,26],[0]),([96,0,20,2,23,3,4,5],[0,1,5,12],[0]),([476,506,0,1,2,3,5],[0,1,16],[]),([476,0,1,20,2,3,5],[0,1,13,18],[]),([551,0,1,2,3,4,5],[3,10,16],[0,2]),([86,0,20,2,3,4,5],[0,14,18],[0]),([61,0,1,20,2,3,4,5],[0,9,14],[0]),([61,0,1,2,3,4,49,5],[13,17,28],[0,2]),([61,0,1,2,3,4,60,5],[3],[0,2,6]),([61,0,1,2,3,4,5],[0,8,9,11,22,23],[0,1,2,6,8]),([429,506,0,1,2,3,5],[1,16,25],[]),([429,0,1,20,2,3,5],[0,1,13,18],[]),([139,0,1,20,3,4,9,5],[0,1,7,11],[0,2,6]),([139,0,1,2,3,4,60,5],[0,3],[0,2]),([139,0,20,2,3,4,49,5],[0,11],[0]),([139,1,20,2,3,4,28,5],[0,7],[0,6]),([371,0,1,20,3,4,5],[0,1,14,18],[]),([202,0,1,2,41,3,4,5],[1,8,21],[0,1]),([202,0,20,2,23,3,4,5],[1,19,21],[0,1]),([214,0,1,20,2,4,5],[0,7,14,18],[0]),([437,0,1,20,2,3,4,5],[],[0]),([199,0,1,2,41,3,4,5],[1,15],[0,2]),([199,0,20,2,23,3,4,5],[1,7],[0]),([380,0,1,20,2,3,4,5],[1,7],[0,2]),([372,0,1,20,2,3,4],[0,1,14,18],[]),([506,109,0,1,3,4,9,5],[7,16],[0,4,6]),([506,435,0,1,2,3,4,5],[2,7],[0,1,2]),([506,85,0,2,23,3,4,5],[7,11],[0,6]),([506,418,0,1,2,3,4,5],[7,11],[0,4,6]),([506,541,0,2,3,4,5],[18,27],[0,1,6,7,8]),([506,0,1,186,2,3,5],[0,1,16],[]),([506,0,1,2,461,3,4],[0,1,9,18],[]),([506,0,1,2,108,3,4,5],[2,7],[0,2,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_5Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_5Pools s0NAutos s0NBucket6 7 s0NBlock7_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_5Mem : ∀ ns ∈ s0NBlock7_5, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_5Ok
def s0NBlock7_6Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(20,[]),(23,[]),(12,[]),(4,[]),(9,[]),(16,[]),(8,[]),(18,[]),(24,[]),(11,[]),(21,[]),(5,[(1,0,1)]),(5,[(2,0,1)])]
def s0NBlock7_6Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_6Specs
def s0NBlock7_6 : List NodeSpec := [([506,0,1,2,3,486,4,5],[2,5],[0,1]),([506,0,1,2,3,497,4,5],[2,6],[1,7]),([506,0,1,2,3,181,4,5],[5,14],[0,1,3]),([506,0,1,2,3,472,4,5],[5,10],[1]),([506,0,1,2,3,8,4,5],[2,5],[2,3]),([506,0,1,2,3,25,4,5],[2,5],[0,1]),([506,0,1,2,3,4,121,5],[2,5],[0,6]),([506,0,1,2,3,4,134,5],[2,5],[0,6]),([506,0,1,2,3,4,110,5],[5,9],[0,6]),([506,0,1,2,3,4,9,5],[2,5],[0,2,6]),([506,0,1,2,3,4,39,5],[2,5],[0,2,6]),([506,0,1,2,3,4,158,5],[2,5],[0,1,6]),([506,0,1,2,3,4,5,118],[5,9,11],[0,1,6,7]),([506,0,1,2,3,110,5],[1,5,10,17],[0]),([506,0,1,2,3,226,5],[0,1,7],[]),([506,0,1,2,3,9,83,5],[5,7],[0,1]),([506,0,1,2,3,9,5,94],[1,5,13],[0,1,6,7]),([506,0,1,2,472,4,5],[5,10,13],[0]),([506,0,1,23,3,4,9,5],[1,5],[0,2,6]),([506,0,1,3,8,4,9,5],[5,7],[0,1,6]),([506,0,168,2,3,4,5],[0,1,10,17],[0,6]),([506,0,2,427,3,4,5],[0,1,10],[]),([506,0,2,464,3,4,5],[5,10,13],[1]),([506,0,2,23,3,26,4,5],[0,5],[0,1]),([506,229,1,2,3,4,5],[0,7,13],[0]),([506,488,1,2,3,4,5],[1,13,15],[1]),([506,179,1,2,3,4,5],[1,9],[0,1,6]),([506,175,1,2,3,4,5],[0,12,13],[]),([506,1,2,224,3,4,5],[0,1,10],[]),([506,1,2,446,3,4,5],[0,10,13],[]),([506,1,2,463,3,4,5],[5,10,13],[1]),([506,1,2,3,4,502,5],[0,1,12,13],[]),([577,0,1,2,3,4,5],[0,1,10],[0,1]),([572,0,1,2,3,4,5],[1,2,10,17],[2,6]),([565,0,1,2,3,4,5],[1,8,10],[0,2]),([573,0,1,2,3,4,5],[0,2,12,13],[2]),([579,0,1,2,3,4,5],[1,4,13,15],[1]),([109,0,1,20,3,4,9,5],[0,1,5,9],[0,2]),([109,0,1,2,3,35,4,5],[0,5,16],[0,1]),([109,0,1,2,3,4,543,5],[4,12],[0,6]),([109,0,1,2,3,4,60,5],[0,3],[0,2]),([109,0,1,507,3,4,5],[0,1,10],[0]),([109,0,20,2,3,4,49,5],[0],[0]),([109,1,20,2,3,4,28,5],[0],[0]),([30,0,1,20,2,3,4,5],[1,9],[]),([30,0,20,2,41,3,4,5],[1,9],[0]),([30,0,20,2,3,4,5],[1,9,10],[0,2]),([30,0,2,23,41,3,4,5],[1,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_6Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_6Pools s0NAutos s0NBucket6 7 s0NBlock7_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_6Mem : ∀ ns ∈ s0NBlock7_6, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_6Ok
def s0NBlock7_7Specs : List PoolSpec := [(19,[]),(22,[]),(0,[(1,2,3)]),(0,[]),(6,[]),(7,[]),(0,[(1,3,5)]),(20,[]),(23,[]),(1,[]),(9,[]),(0,[(1,1,2)]),(16,[]),(15,[]),(8,[]),(18,[]),(4,[(1,0,1)]),(0,[(1,1,4)]),(24,[]),(11,[]),(6,[(1,0,1)]),(6,[(2,0,1)]),(13,[]),(6,[(3,0,23)]),(5,[(1,1,2),(3,0,25)]),(6,[(1,23,3),(3,0,25)])]
def s0NBlock7_7Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_7Specs
def s0NBlock7_7 : List NodeSpec := [([172,0,1,2,507,3,4,5],[1,9,12,21],[0,2]),([172,0,20,2,23,3,4,5],[1,11,20],[0,1]),([435,0,1,20,2,3,4,5],[0,3,7],[0]),([85,0,1,2,507,3,4,5],[0,12],[0,2]),([85,0,1,2,41,3,4,5],[1,14],[0,2]),([85,0,1,2,3,543,5],[0,13,18],[0]),([85,0,20,2,23,3,4,5],[1,7,11],[0]),([85,0,2,23,41,3,4,5],[1,18],[0,2]),([85,0,2,23,3,5,94],[1,7,18],[0,2,6,9]),([85,0,23,3,4,5,31],[1,7],[0,2,6,9]),([90,0,1,20,2,3,4,5],[0,13],[]),([90,0,20,2,3,4,60,5],[0,13,15],[0]),([90,0,20,2,3,4,5],[13,15,16,18],[0,4,6,8]),([90,0,2,3,4,49,60,5],[0],[0]),([90,1,20,2,3,4,28,5],[0,3,15],[6]),([90,20,2,3,4,28,5],[0,3,15,16],[0,6]),([418,0,1,20,2,3,4,5],[1,3,7],[0,2,6]),([582,431,0,1,2,3,4,5],[5,7],[0]),([582,232,0,1,2,3,4,5],[5,7],[0,2]),([582,0,2,3,8,25,4,5],[0,1,7],[]),([582,0,2,3,25,4,5],[0,1,3],[0,2,3]),([582,0,2,3,4,9,39,5],[1,7,22],[]),([582,0,2,3,4,39,5],[0,1,3],[0,2,6]),([582,0,23,3,4,9,5],[0,1,7],[0,2,6]),([69,0,1,20,3,8,4,5],[13],[0]),([69,0,1,20,3,4,9,5],[1,7,10],[0,2,6]),([69,0,1,2,3,35,4,5],[0,7],[0]),([69,0,1,2,3,4,60,5],[0,4],[0,2]),([69,0,20,2,3,26,4,5],[0,1,3],[0]),([69,0,20,2,3,4,49,5],[0,3],[0]),([69,0,20,23,3,4,5],[0,1,5,7,11],[0]),([69,1,20,2,3,4,28,5],[0,7],[0,6]),([614,0,1,2,248,3,4,5],[1,9,11,23],[0,2]),([614,0,1,2,3,4,83,5],[0,22],[0,2]),([614,0,2,3,26,4,5],[1,19],[0,2,3]),([431,0,1,20,2,3,4,5],[2,5,7],[0]),([177,0,1,2,23,3,4,5],[0,1,7],[0,2]),([177,0,1,2,3,25,4,5],[0,1,3,7],[0,2,3]),([177,0,1,2,3,4,5],[0,1,7,24,25],[0,1,2,3,6,7]),([101,0,1,20,2,3,9,5],[1,7,10],[0,4,6]),([101,0,20,2,23,3,4,5],[1,7],[0]),([101,0,20,2,3,49,5],[0,13,17,18],[0]),([232,0,1,20,2,3,4,5],[5,7],[0,2]),([178,0,1,2,3,4,49,5],[0,7,22],[0,6]),([17,0,1,2,3,5,16],[0,1,6],[]),([690,0,1,2,3,8,4,5],[3,7],[0,2]),([670,0,1,2,3,4,83,5],[0,3,8],[0,2]),([238,0,1,2,3,25,4,5],[0,1,3,7],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_7Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_7Pools s0NAutos s0NBucket6 7 s0NBlock7_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_7Mem : ∀ ns ∈ s0NBlock7_7, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_7Ok
def s0NBlock7_8Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(2,[]),(20,[]),(12,[]),(4,[]),(9,[]),(3,[(1,0,1)]),(16,[]),(15,[]),(8,[]),(18,[]),(24,[]),(11,[]),(21,[]),(0,[(1,1,2),(2,23,5)]),(5,[(1,0,1)]),(7,[(1,20,2)]),(0,[(1,20,2)]),(4,[(1,1,2)]),(3,[(1,51,0)])]
def s0NBlock7_8Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_8Specs
def s0NBlock7_8 : List NodeSpec := [([0,636,2,23,3,4,5],[0,1,11,22],[0,2,3,6,7]),([0,477,1,20,2,3,4,5],[8,9],[1]),([0,323,1,2,3,4,5],[0,1,17],[0,2,3,6]),([0,266,1,2,3,4,49,5],[0,8],[0,2,6]),([0,722,1,2,723,3,4,5],[1,8],[0,6]),([0,722,1,2,3,727,4,5],[0,15],[0]),([0,722,1,2,3,4,60,5],[0,11,13],[]),([0,722,1,2,3,4,5,731],[1,11],[]),([0,234,1,20,2,3,4,5],[1,8],[0]),([0,422,1,2,23,3,4,5],[1,15],[0,1,2]),([0,626,2,23,3,4,5],[0,1,21],[0,1,2,3]),([0,439,1,20,2,3,4,5],[1,8],[1]),([0,439,1,2,3,4,49,5],[0,10],[0,3]),([0,655,1,2,3,4,5],[0,1],[0,2,3,6]),([0,237,1,2,23,3,4,5],[1,15],[0,2]),([0,682,1,2,41,3,4,5],[1,8],[0]),([0,682,1,2,3,683,4,5],[0,8],[1]),([0,682,1,2,3,8,4,5],[5,8],[0,2,3]),([0,682,1,2,3,4,685,5],[0,8],[6]),([0,229,1,20,2,3,4,5],[0,13],[0]),([0,721,1,2,3,4,5],[0,2,14],[0,2]),([0,488,1,20,2,3,4,5],[1,16],[]),([0,179,1,20,2,3,4,5],[1,8],[]),([0,173,1,2,23,3,4,5],[1,15],[0,1,2]),([0,175,1,20,2,3,4,5],[0,11,13],[]),([0,175,1,2,23,3,4,5],[0,1,6],[0,2]),([0,175,2,23,3,4,5],[0,1,5],[0,2,9]),([0,1,186,20,2,3,5],[0,1,8,14],[]),([0,1,113,2,3,35,4,5],[0,5],[0]),([0,1,113,2,3,4,60,5],[],[0]),([0,1,113,41,3,4,5],[1,8],[0]),([0,1,494,2,3,4,5],[0,1,11,14],[0,1]),([0,1,231,2,3,4,5],[0,3,11,14],[0,4]),([0,1,598,2,3,599,4,5],[0,15],[]),([0,1,598,2,3,4,5,603],[1,11],[]),([0,1,443,2,3,4,5],[1,7,11],[0,1,3]),([0,1,115,20,2,3,9,5],[1,5],[0,6]),([0,1,115,2,41,3,4,5],[1,12,19,20],[0,4]),([0,1,115,2,3,60,5],[0,13,14],[0]),([0,1,235,2,3,4,5],[1,4,11,18],[0,6]),([0,1,140,2,630,3,4,5],[5,11],[0,6]),([0,1,140,2,3,694,4,5],[0,13],[5]),([0,1,483,2,3,4,5],[0,1,11],[0,1]),([0,1,20,293,2,3,4,5],[1,8],[0,1]),([0,1,20,144,2,3,4,5],[1,8],[]),([0,1,20,440,2,3,4,5],[1,8],[0]),([0,1,20,295,2,3,5],[0,1,8,14],[]),([0,1,20,230,2,3,4,5],[0,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_8Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_8Pools s0NAutos s0NBucket6 7 s0NBlock7_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_8Mem : ∀ ns ∈ s0NBlock7_8, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_8Ok
def s0NBlock7_9Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(6,[]),(7,[]),(20,[]),(23,[]),(12,[]),(9,[]),(16,[]),(15,[]),(18,[]),(24,[]),(11,[]),(21,[]),(5,[(1,0,1)])]
def s0NBlock7_9Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock7_9Specs
def s0NBlock7_9 : List NodeSpec := [([0,1,20,491,2,3,4,5],[1,14],[]),([0,1,20,2,106,3,4,5],[1,8,10],[0,6]),([0,1,20,2,461,3,4],[0,1,7,12],[]),([0,1,20,2,216,3,4,5],[5,8],[0,2]),([0,1,20,2,108,3,4,5],[5,8],[0,2,6]),([0,1,20,2,104,3,4,5],[5,8],[0,2,4]),([0,1,20,2,224,3,4,5],[0,9],[0,1]),([0,1,20,2,446,3,4,5],[0,9],[]),([0,1,20,2,463,3,4,5],[1,9],[1]),([0,1,20,2,428,3,4,5],[0,8],[]),([0,1,20,2,448,3,4,5],[0,8],[]),([0,1,20,2,116,3,4,5],[1,8,10],[0,4,6]),([0,1,20,2,282,41,3,4],[1],[0]),([0,1,20,2,282,3,4],[1,6,12,14],[0,1]),([0,1,20,2,466,3,4,5],[1,8],[1]),([0,1,20,2,41,3,4,5],[1,8],[0]),([0,1,20,2,3,486,4,5],[6,10],[1]),([0,1,20,2,3,379,4,5],[0,13],[1,6]),([0,1,20,2,3,75,4,5],[0,10,13],[1]),([0,1,20,2,3,497,4,5],[6,10],[1,3,7]),([0,1,20,2,3,294,4,5],[5,10],[0,1]),([0,1,20,2,3,181,4,5],[5,10],[0,1]),([0,1,20,2,3,73,4,5],[5,10],[0]),([0,1,20,2,3,278,4,5],[0,10],[0]),([0,1,20,2,3,472,4,5],[1,6,13],[1,3]),([0,1,20,2,3,8,4,5],[5,10],[0]),([0,1,20,2,3,25,4,5],[0,2,5],[0]),([0,1,20,2,3,52,4,5],[5,12],[0,1,2]),([0,1,20,2,3,4,121,5],[1,5,10],[0,4,6]),([0,1,20,2,3,4,134,5],[1,5,10],[0,1]),([0,1,20,2,3,4,76,5],[0,8,10,11],[0]),([0,1,20,2,3,4,154,5],[1,5,10],[0,2]),([0,1,20,2,3,4,110,5],[1,5,10],[0,2]),([0,1,20,2,3,4,74,5],[1,5,10],[0,2,6]),([0,1,20,2,3,4,502,5],[0,11],[]),([0,1,20,2,3,4,114,5],[0,3,10],[0]),([0,1,20,2,3,4,504,5],[0,11],[]),([0,1,20,2,3,4,60,5],[0,10,11],[]),([0,1,20,2,3,4,9,5],[1,5,8],[0,2,6]),([0,1,20,2,3,4,39,5],[1,2,5],[0,2]),([0,1,20,2,3,4,56,5],[0,4,5],[0,2]),([0,1,20,2,3,4,158,5],[5,10],[0,6]),([0,1,20,2,3,4,5,265],[10,12,14],[0]),([0,1,20,2,3,4,5,197],[1,10,14],[0]),([0,1,20,2,3,4,5,290],[1],[0,2]),([0,1,20,2,3,4,5,377],[12],[6]),([0,1,20,2,3,4,5,118],[5,10],[0,4,6,7]),([0,1,20,2,3,154,5],[1,5,8,15],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_9Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_9Pools s0NAutos s0NBucket6 7 s0NBlock7_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_9Mem : ∀ ns ∈ s0NBlock7_9, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_9Ok
def s0NBlock7_10Specs : List PoolSpec := [(19,[]),(22,[]),(0,[(1,2,3)]),(0,[(1,2,4)]),(0,[]),(3,[]),(6,[]),(2,[]),(20,[]),(23,[]),(12,[]),(4,[]),(1,[]),(9,[]),(3,[(1,0,1)]),(16,[]),(15,[]),(8,[]),(24,[]),(11,[]),(21,[]),(5,[(1,0,1)]),(7,[(1,20,4)]),(4,[(1,0,1),(1,62,2)]),(6,[(2,0,1)]),(17,[]),(13,[]),(10,[])]
def s0NBlock7_10Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_10Specs
def s0NBlock7_10 : List NodeSpec := [([0,1,20,2,3,110,5],[1,8,13,14,21],[0]),([0,1,20,2,3,60,5,94],[16,18,22],[1,6]),([0,1,20,2,3,226,5],[0,1,10],[0,1]),([0,1,20,2,3,9,83,5],[0,1,8],[0,1,4,5]),([0,1,20,2,3,9,5,94],[1,8,18],[0,1,4,6,7,8,9]),([0,1,20,2,117,4,5],[0,8,16,18],[0,6]),([0,1,20,2,472,4,5],[1,8,15,18],[0,1]),([0,1,20,23,3,4,9,5],[0,1,16],[0,2]),([0,1,20,116,3,4,5],[0,13,16,18],[0,4,6]),([0,1,20,41,3,4,9,5],[1,16,18],[0,6]),([0,1,20,41,3,4,5,31],[1,13],[0,7]),([0,1,20,3,8,4,9,5],[0,8],[0,4,6]),([0,1,293,2,3,4,5],[1,11,13],[0,1,6]),([0,1,144,2,3,4,5],[1,7,13,21],[0,2,6]),([0,1,440,2,3,4,5],[1,11,13],[0,1]),([0,1,230,2,3,4,5],[0,5,10,18],[0,2]),([0,1,491,2,3,4,5],[1,12,18,20],[0,3]),([0,1,385,2,3,4,60,5],[5],[0]),([0,1,2,715,3,4,49,5],[15,26],[2]),([0,1,2,106,3,4,5],[1,12,13,17,23],[0,1,2,4,6]),([0,1,2,564,3,4,5],[0,1,15],[]),([0,1,2,566,3,4,5],[0,15,18],[]),([0,1,2,574,3,4,5],[12,15,18],[1]),([0,1,2,507,41,3,4,5],[1,13],[0]),([0,1,2,507,248,3,4,5],[1,12,15,24],[0]),([0,1,2,507,3,26,4,5],[0,1,13],[0]),([0,1,2,507,3,8,4,5],[2,12,15],[]),([0,1,2,507,3,512,4,5],[15,25],[]),([0,1,2,507,3,4,49,5],[0,15],[0,2]),([0,1,2,507,3,4,9,5],[3,7,15],[]),([0,1,2,507,3,4,508,5],[10,15],[0]),([0,1,2,507,3,4,83,5],[0,15],[0]),([0,1,2,507,3,4,5,531],[15,20],[]),([0,1,2,507,3,4,5,16],[9,15],[0,1,7]),([0,1,2,507,3,4,5,94],[1,10,17],[0,7]),([0,1,2,717,3,4,5],[0,4,18],[2]),([0,1,2,21,3,35,4,5],[0,8],[0]),([0,1,2,21,3,4,60,5],[0,6],[0,2]),([0,1,2,21,3,4,5,63],[14],[0]),([0,1,2,23,256,3,4,5],[27],[]),([0,1,2,23,3,612,4,5],[0,19],[0,1,2]),([0,1,2,23,3,249,4,5],[0,1,8,25],[0,2]),([0,1,2,23,3,35,4,5],[0,8,19],[0]),([0,1,2,23,3,253,4,5],[27],[]),([0,1,2,23,3,4,543,5],[8,10],[0,2]),([0,1,2,23,3,4,60,5],[5,10],[0,2]),([0,1,2,23,3,4,122,5],[0,8],[]),([0,1,2,256,3,4,5],[0,4,9],[0,2,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_10Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_10Pools s0NAutos s0NBucket6 7 s0NBlock7_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_10Mem : ∀ ns ∈ s0NBlock7_10, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_10Ok
def s0NBlock7_11Specs : List PoolSpec := [(19,[]),(22,[]),(0,[(1,2,3)]),(0,[(1,2,4)]),(0,[(1,7,3)]),(0,[]),(3,[]),(6,[]),(20,[]),(23,[]),(12,[]),(4,[]),(1,[]),(9,[]),(0,[(1,1,2)]),(16,[]),(15,[]),(8,[]),(18,[]),(24,[]),(0,[(1,20,3)]),(11,[]),(14,[]),(6,[(1,0,1)]),(0,[(1,20,2)]),(5,[(1,0,1),(1,20,2)]),(6,[(1,0,1),(1,41,3)]),(6,[(1,0,1),(1,27,3)]),(4,[(1,0,1),(2,20,2)]),(7,[(2,20,2),(1,27,4)]),(5,[(2,0,1),(1,506,2)]),(17,[]),(0,[(1,507,3)]),(6,[(2,0,1),(1,507,3)])]
def s0NBlock7_11Pools : BT (Option BoundPool) := buildPoolsBT 6 s0NW s0NR s0NSlices s0NBlock7_11Specs
def s0NBlock7_11 : List NodeSpec := [([0,1,2,296,41,3,4,5],[1,9],[0,1]),([0,1,2,428,3,4,5],[0,1,13],[]),([0,1,2,448,3,4,5],[0,1,13,19],[]),([0,1,2,282,41,3,4],[1,9,17],[0,1,2,4]),([0,1,2,466,3,4,5],[1,12,13,19],[0,1]),([0,1,2,41,248,3,4,5],[1,11,17,23,24],[0,2]),([0,1,2,41,3,35,4,5],[0,1],[0,1]),([0,1,2,41,3,25,4,5],[1,9,14],[0]),([0,1,2,41,3,52,4,5],[1,12],[0,2]),([0,1,2,41,3,4,49,5],[1,13,17],[0,2]),([0,1,2,41,3,4,60,5],[1,19],[0,2,4]),([0,1,2,41,3,4,83,5],[11,17],[0,1,4]),([0,1,2,41,3,4,5],[1,11,13],[0,2]),([0,1,2,41,3,4,5,63],[1],[0]),([0,1,2,41,3,4,5,290],[1],[0,2]),([0,1,2,41,3,4,5,16],[1,9],[0,1,4,5,7]),([0,1,2,3,247,4,5],[1,9,18],[0,2,3]),([0,1,2,3,379,4,5],[0,7,21],[0,1,3,6]),([0,1,2,3,75,4,5],[0,6,21,27],[0,1,2]),([0,1,2,3,615,4,5],[1,18],[0,3]),([0,1,2,3,35,4,28,5],[0,20],[0,5]),([0,1,2,3,8,512,4,5],[15,31],[]),([0,1,2,3,8,584,4,5],[0,1],[]),([0,1,2,3,8,10,4,5],[0,1],[]),([0,1,2,3,8,52,4,5],[0,7,13],[0,1,2,3]),([0,1,2,3,8,4,543,5],[8,18],[0]),([0,1,2,3,8,4,60,5],[8],[0]),([0,1,2,3,8,15,5],[0,1,2],[]),([0,1,2,3,512,4,5],[15,19,30,31,32,33],[0,1,2]),([0,1,2,3,584,4,5],[0,1,5],[0,2,3]),([0,1,2,3,10,4,5],[0,1,4],[]),([0,1,2,3,253,4,5],[0,5,9],[0,2]),([0,1,2,3,25,52,4,5],[0,1,5],[0,1]),([0,1,2,3,25,4,39,5],[0],[0,2]),([0,1,2,3,25,4,122,5],[0,8],[0]),([0,1,2,3,25,4,5],[0,1,5,8],[0,2,3]),([0,1,2,3,25,4,5,94],[0,17],[0,1,4,5]),([0,1,2,3,52,4,5],[17,25,26],[0,1,2,4,5]),([0,1,2,3,4,123,5],[0,1,5],[0,2,6]),([0,1,2,3,4,76,5],[0,9,13,18,28,29],[0,1,2]),([0,1,2,3,4,581,5],[0,1,18],[]),([0,1,2,3,4,543,60,5],[0,16,18],[]),([0,1,2,3,4,543,9,5],[3,7,18],[]),([0,1,2,3,4,543,508,5],[0,10,18],[0]),([0,1,2,3,4,543,546,5],[18,31],[]),([0,1,2,3,4,543,5,31],[1,18],[0]),([0,1,2,3,4,543,5,16],[9,19,22],[0,1]),([0,1,2,3,4,543,5,547],[19,22],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_11Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_11Pools s0NAutos s0NBucket6 7 s0NBlock7_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_11Mem : ∀ ns ∈ s0NBlock7_11, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_11Ok
def s0NBlock7_12Specs : List PoolSpec := [(19,[]),(22,[]),(0,[(1,2,3)]),(0,[(1,2,4)]),(0,[(1,7,3)]),(0,[(1,7,4)]),(0,[]),(3,[]),(6,[]),(0,[(1,2,15)]),(0,[(1,3,5)]),(2,[]),(20,[]),(23,[]),(12,[]),(4,[]),(9,[]),(3,[(1,0,1)]),(0,[(1,1,2)]),(16,[]),(15,[]),(8,[]),(18,[]),(0,[(1,1,4)]),(24,[]),(11,[]),(14,[]),(21,[]),(5,[(1,0,1)]),(7,[(1,20,4)]),(0,[(1,2,5)]),(0,[(1,4,5)]),(6,[(2,0,1)]),(5,[(2,0,1),(1,506,2)]),(7,[(1,506,2),(1,2,4)]),(0,[(1,507,4)]),(7,[(1,506,2),(1,507,4)]),(0,[(1,507,5)]),(0,[(1,3,4)]),(0,[(1,543,5)]),(13,[]),(10,[]),(3,[(1,0,259)])]
def s0NBlock7_12Pools : BT (Option BoundPool) := buildPoolsBT 6 s0NW s0NR s0NSlices s0NBlock7_12Specs
def s0NBlock7_12 : List NodeSpec := [([0,1,2,3,4,141,5],[0,1,6,12],[0,2,6]),([0,1,2,3,4,504,5],[0,1,22],[]),([0,1,2,3,4,60,39,5],[12,23],[0,2,6]),([0,1,2,3,4,60,56,5],[0,7,24],[0,2,6]),([0,1,2,3,4,60,375,5],[0],[1,3,6]),([0,1,2,3,4,60,5],[0,7,20,22,24],[0,2]),([0,1,2,3,4,60,5,63],[29],[0,1]),([0,1,2,3,4,60,5,16],[13],[0,1,5,6,8]),([0,1,2,3,4,9,508,5],[0,14],[0]),([0,1,2,3,4,9,585,5],[40],[]),([0,1,2,3,4,9,11,5],[14],[]),([0,1,2,3,4,9,56,5],[13,16],[0,4,6]),([0,1,2,3,4,508,5],[0,7,14,35,36],[0,2,4]),([0,1,2,3,4,585,5],[0,1,6],[2,6]),([0,1,2,3,4,11,5],[0,1,5],[]),([0,1,2,3,4,83,5,128],[1,15],[0]),([0,1,2,3,4,122,5],[0,12,27],[0,2,3,6]),([0,1,2,3,4,5,265],[8,20,24],[0]),([0,1,2,3,4,5,197],[0,1,16],[0,2]),([0,1,2,3,4,5,531],[0,1,19,27,37],[0,1]),([0,1,2,3,4,5,290],[1,15],[0,1,2,4]),([0,1,2,3,4,5,547],[8,24,26,39],[0,1,8]),([0,1,2,3,543,49,5],[0,22,23,24],[0]),([0,1,2,3,543,9,5],[3,8,22,24],[0,1]),([0,1,2,3,543,83,5],[0,22,38],[0]),([0,1,2,3,543,5,94],[15,24,26,31],[0]),([0,1,2,3,15,9,5],[0,1,3],[]),([0,1,2,3,15,11,5],[0,1,9],[]),([0,1,2,3,15,5,16],[0,1,10],[]),([0,1,2,259,683,4,5],[0,12,16,42],[0,2]),([0,1,2,259,8,4,5],[0,13,16],[0,2,3]),([0,1,2,259,25,4,5],[0,1,16,41],[0,2]),([0,1,2,631,694,4,5],[0,12,21,25],[0,5,9]),([0,1,2,631,4,5,707],[1,12,25],[0,9]),([0,1,507,23,3,4,5],[0,1,16,18],[0]),([0,1,507,3,8,4,5],[2,19,32,33],[0,7]),([0,1,507,3,4,9,5],[1,3,11,19,34],[0,2,4,7]),([0,1,507,3,4,5,31],[1,19,30],[0,7]),([0,1,174,23,3,4,5],[0,1,12],[0,1,2,3]),([0,1,108,23,3,4,5],[1,12],[0,2,6]),([0,1,583,3,4,9,5],[0,1],[0,2,6]),([0,1,7,3,8,4,5],[0,1,2],[]),([0,1,7,3,10,4,5],[0,1,4],[]),([0,1,7,3,4,9,5],[0,1,3],[]),([0,1,7,3,4,11,5],[0,1,5],[]),([0,1,704,630,3,4,5],[1,12,16],[]),([0,169,20,2,3,4,5],[1,6,12,17],[0,1,6]),([0,168,20,2,3,4,5],[0,1,6,17,28],[0,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_12Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_12Pools s0NAutos s0NBucket6 7 s0NBlock7_12 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_12Mem : ∀ ns ∈ s0NBlock7_12, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_12Ok
def s0NBlock7_13Specs : List PoolSpec := [(19,[]),(22,[]),(0,[(1,2,3)]),(0,[]),(7,[]),(20,[]),(23,[]),(12,[]),(9,[]),(3,[(1,0,1)]),(0,[(1,1,2)]),(16,[]),(15,[]),(0,[(1,69,1)]),(18,[]),(4,[(1,0,1)]),(0,[(1,1,3)]),(0,[(1,1,4)]),(24,[]),(11,[]),(21,[]),(5,[(1,0,1),(1,1,2)]),(6,[(1,0,1),(1,23,3)])]
def s0NBlock7_13Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_13Specs
def s0NBlock7_13 : List NodeSpec := [([0,334,2,23,3,4,5],[0,6],[0,2,5]),([0,159,20,2,3,4,5],[0,1,3,9],[0,1,3]),([0,366,20,2,3,4,5],[0,3,18],[0,4,6]),([0,489,20,2,3,4,5],[1,3,18],[1,7]),([0,70,20,2,3,4,5],[1,5,8,13],[0]),([0,102,20,2,3,4,5],[0,12,18],[0]),([0,113,20,2,3,4,49,5],[0,12,17],[0]),([0,113,20,23,3,4,5],[0,1,12],[0]),([0,133,20,2,3,4,5],[9,12,15],[0]),([0,200,20,2,23,3,4,5],[1,10,12],[0]),([0,115,20,2,23,3,4,5],[0,1,4,10,12],[0]),([0,115,20,2,3,49,5],[4,12,18],[0]),([0,268,20,2,3,4,5],[1,9,12,14,15],[0,1]),([0,140,2,23,3,4,5],[1,5],[0,2]),([0,20,223,23,3,4,5],[0,1,12],[0]),([0,20,2,138,3,4,5],[0,1,8,9],[0]),([0,20,2,21,23,3,4,5],[1,3],[]),([0,20,2,21,3,26,4,5],[0,11],[0,1,2]),([0,20,2,21,3,4,49,5],[11],[2]),([0,20,2,21,3,4,5,32],[8,9],[0,2]),([0,20,2,427,3,4,5],[0,1,3],[]),([0,20,2,447,3,4,5],[0,4,11,18],[]),([0,20,2,464,3,4,5],[1,3,5,18],[1]),([0,20,2,23,41,3,4,5],[1,8],[0]),([0,20,2,23,248,3,4,5],[1,4,5,10],[0]),([0,20,2,23,3,26,4,5],[0,1],[0,1]),([0,20,2,23,3,35,4,5],[0,1,19],[0]),([0,20,2,23,3,8,4,5],[0,1,5],[0]),([0,20,2,23,3,25,4,5],[0,1,5,10],[0]),([0,20,2,23,3,4,28,5],[1,5,7,10],[0,2]),([0,20,2,23,3,4,49,5],[0,1],[0]),([0,20,2,23,3,4,60,5],[0,1,7],[0]),([0,20,2,23,3,4,9,5],[1,5],[0]),([0,20,2,23,3,4,39,5],[0,1,5,10],[0]),([0,20,2,23,3,4,83,5],[0,1,5],[0]),([0,20,2,23,3,4,5],[0,1,8,9],[0,1]),([0,20,2,23,3,4,5,63],[1,20],[0]),([0,20,2,23,3,4,5,16],[1],[0,1,7]),([0,20,2,23,3,4,5,94],[1,10,18],[0,1]),([0,20,2,41,3,4,49,5],[1,8,18],[0]),([0,20,2,3,271,4,5],[0,1,15,19],[0,1]),([0,20,2,3,259,4,5],[0,1,9,15,19],[0]),([0,20,2,3,26,4,28,5],[0,14,15,16],[0]),([0,20,2,3,35,4,49,5],[0,19],[0]),([0,20,2,3,8,25,4,5],[0,1,2,5],[]),([0,20,2,3,8,4,49,5],[0],[0]),([0,20,2,3,25,4,5],[0,1,3,5,21,22],[0,1]),([0,20,2,3,4,82,5],[0,12,18],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_13Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_13Pools s0NAutos s0NBucket6 7 s0NBlock7_13 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_13Mem : ∀ ns ∈ s0NBlock7_13, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_13Ok
def s0NBlock7_14Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(7,[]),(2,[]),(20,[]),(23,[]),(12,[]),(9,[]),(3,[(1,0,1)]),(0,[(1,1,2)]),(15,[]),(8,[]),(18,[]),(4,[(1,0,1)]),(0,[(1,1,4)]),(24,[]),(7,[(1,0,4)]),(0,[(1,1,5)]),(11,[]),(14,[]),(21,[]),(5,[(1,0,1),(1,1,2)]),(6,[(1,0,1),(1,20,3)]),(7,[(1,2,4)]),(7,[(1,23,4)])]
def s0NBlock7_14Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_14Specs
def s0NBlock7_14 : List NodeSpec := [([0,20,2,3,4,28,49,5],[0,13,15],[]),([0,20,2,3,4,28,5,32],[13,16,18],[6,7,9]),([0,20,2,3,4,503,5],[0,1,2,16],[]),([0,20,2,3,4,49,60,5],[0,11],[0]),([0,20,2,3,4,49,9,5],[0,1,5],[0,6]),([0,20,2,3,4,49,39,5],[0,1,5,15],[0]),([0,20,2,3,4,49,5],[0,11,16],[0]),([0,20,2,3,4,49,5,63],[16,20],[0]),([0,20,2,3,4,49,5,31],[16],[0,1,6]),([0,20,2,3,4,49,5,16],[0,16],[0,1,5,7]),([0,20,2,3,4,9,39,5],[0,1,5],[6]),([0,20,2,3,4,39,5],[0,1,2,5,25],[0,1,2,6]),([0,20,2,3,4,5,273],[1,11,16],[0,1]),([0,20,2,3,4,5,128],[1,2,9],[0,1]),([0,20,2,3,4,5,89],[2,16],[0,1,6,7]),([0,20,2,3,28,49,5],[0,3,4,14,15,16,17],[0,1,2,6,8]),([0,20,2,3,49,5,94],[11,16],[0,6,7]),([0,20,2,259,4,5],[0,1,9,11,14],[0]),([0,20,21,23,3,4,5],[0,1,5,9,10],[0,2]),([0,20,23,3,4,9,5],[0,1,5,11,24],[0,1,2,6]),([0,20,23,3,4,5,31],[0,1,5,8,9],[0,1]),([0,223,23,26,4,5],[0,1],[0,1]),([0,2,583,3,26,4,5],[0,1],[0,2,3]),([0,2,23,41,3,26,4,5],[0,1,8],[0]),([0,2,23,3,639,4,5],[0,1],[1,2,3]),([0,2,23,3,312,4,5],[5,16,19],[0,2]),([0,2,23,3,26,25,4,5],[0,1],[]),([0,2,23,3,26,4,39,5],[0,1,5],[0]),([0,2,23,3,26,4,5],[0,1],[0,1,2,3]),([0,2,23,3,26,4,5,94],[0,5,6,16],[0,1,2,3]),([0,2,23,3,35,4,5],[0,5,19,22,23],[0]),([0,2,23,3,4,83,5,32],[0,12],[2]),([0,2,23,3,4,5,635],[1,5,16],[2,6,9]),([0,2,23,3,4,5,63],[1,3,9,21],[0]),([0,2,23,3,4,632],[1,5],[2,4]),([0,2,23,3,4,32,94],[0,1,6,16],[0,1,2,4,7,8]),([0,2,23,631,4,5],[1,5],[2]),([0,2,3,26,4,39,5],[0,1,5],[0,1,2,3,6]),([0,2,3,35,4,49,5],[0,19],[0,5]),([0,23,3,26,4,9,5],[0,1,5,6],[0,1,2,3,6]),([0,23,3,26,4,5,31],[0,1,5,6],[0,1,2,3,9]),([229,1,20,2,3,4,5],[0,7,16],[0,4]),([488,1,20,2,3,4,5],[1,16,21],[1]),([179,1,20,2,3,4,5],[1,8],[0,1]),([175,1,20,2,3,4,5],[0,11,13,16],[0]),([145,20,2,3,4,28,5],[0,2,11,13,14,16],[0,6]),([1,113,20,2,3,4,28,5],[0,2,11],[0]),([1,140,20,2,3,4,28,5],[0,2,11,13],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_14Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_14Pools s0NAutos s0NBucket6 7 s0NBlock7_14 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_14Mem : ∀ ns ∈ s0NBlock7_14, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_14Ok
def s0NBlock7_15Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(7,[]),(2,[]),(20,[]),(23,[]),(3,[(1,0,1)]),(0,[(1,1,2)]),(16,[]),(15,[]),(8,[]),(18,[]),(4,[(1,0,1)]),(0,[(1,1,3)]),(0,[(1,1,4)]),(24,[]),(7,[(1,0,4)]),(0,[(1,1,5)]),(0,[(1,20,3)]),(21,[]),(17,[])]
def s0NBlock7_15Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_15Specs
def s0NBlock7_15 : List NodeSpec := [([1,140,2,630,3,4,5],[1,5,10],[0,6]),([1,140,2,3,694,4,5],[0,5,10,11],[0,5]),([1,20,2,224,3,4,5],[0,1,9],[0,1]),([1,20,2,446,3,4,5],[0,1,9,16],[]),([1,20,2,463,3,4,5],[1,5,9,16],[1]),([1,20,2,21,3,22,4,5],[0,5],[0,1]),([1,20,2,21,3,4,5,29],[7],[0,2]),([1,20,2,23,3,4,28,5],[0,1],[0]),([1,20,2,41,3,4,28,5],[1,16],[0,2,6]),([1,20,2,3,35,4,28,5],[0],[0,1,6]),([1,20,2,3,8,4,28,5],[0],[0,6]),([1,20,2,3,4,502,5],[0,1,12,16],[]),([1,20,2,3,4,28,60,5],[0,10,12],[0]),([1,20,2,3,4,28,5],[0,2,10,12,16],[0,6]),([1,20,2,3,4,28,5,63],[17],[0,9]),([1,20,2,3,4,28,5,16],[0,16],[0,5,6,7]),([1,20,2,3,4,5,161],[2,10,16,20],[0]),([1,2,23,3,249,4,5],[0,6,21],[0,2]),([1,2,3,35,4,28,5],[0,19],[0,5,6,8]),([140,2,23,3,4,5],[1,5],[0,2]),([20,2,23,3,4,28,5],[0,1,2,5,8,12,17],[0,6]),([20,2,3,26,4,28,5],[0,12,13,14],[0,1,6]),([20,2,3,4,28,49,5],[0,15,16],[0,6]),([20,2,3,4,28,5,32],[12,16,18],[0,6,7]),([20,2,3,28,49,5],[0,2,3,4,13,15,16,17],[0,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_15Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_15Pools s0NAutos s0NBucket6 7 s0NBlock7_15 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_15Mem : ∀ ns ∈ s0NBlock7_15, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_15Ok
def s0NNodes7 : List NodeSpec := s0NBlock7_0 ++ s0NBlock7_1 ++ s0NBlock7_2 ++ s0NBlock7_3 ++ s0NBlock7_4 ++ s0NBlock7_5 ++ s0NBlock7_6 ++ s0NBlock7_7 ++ s0NBlock7_8 ++ s0NBlock7_9 ++ s0NBlock7_10 ++ s0NBlock7_11 ++ s0NBlock7_12 ++ s0NBlock7_13 ++ s0NBlock7_14 ++ s0NBlock7_15
def s0NBucket7 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 7 xs.toFinset) s0NBucket7 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append s0NBlock7_0Mem s0NBlock7_1Mem) s0NBlock7_2Mem) s0NBlock7_3Mem) s0NBlock7_4Mem) s0NBlock7_5Mem) s0NBlock7_6Mem) s0NBlock7_7Mem) s0NBlock7_8Mem) s0NBlock7_9Mem) s0NBlock7_10Mem) s0NBlock7_11Mem) s0NBlock7_12Mem) s0NBlock7_13Mem) s0NBlock7_14Mem) s0NBlock7_15Mem)
def s0NBlock8_0Specs : List PoolSpec := [(19,[]),(22,[]),(0,[(1,2,3)]),(0,[(1,2,4)]),(0,[]),(3,[]),(6,[]),(7,[]),(2,[]),(20,[]),(23,[]),(12,[]),(9,[]),(3,[(1,0,1)]),(0,[(1,1,2)]),(16,[]),(15,[]),(8,[]),(18,[]),(4,[(1,0,1)]),(0,[(1,1,4)]),(24,[]),(11,[]),(6,[(1,0,1)]),(5,[(1,0,1)]),(7,[(1,2,4)]),(7,[(2,20,2)]),(0,[(2,2,3)]),(0,[(2,2,4)]),(0,[(3,2,4)]),(0,[(1,2,5)]),(0,[(2,2,5)]),(0,[(3,2,5)]),(0,[(0,4,5)]),(0,[(1,4,5)]),(6,[(2,0,1)]),(17,[]),(5,[(2,0,1)]),(0,[(3,1,4)]),(4,[(1,1,2)])]
def s0NBlock8_0Pools : BT (Option BoundPool) := buildPoolsBT 6 s0NW s0NR s0NSlices s0NBlock8_0Specs
def s0NBlock8_0 : List NodeSpec := [([51,0,2,23,3,4,5],[0,1,9],[0,1,2,3,6,7]),([65,506,0,1,2,3,4,5],[0,1,9,31],[0,1,6]),([65,0,1,20,2,3,4,5],[0,1,7,9,16,31],[0,1,2,4,6]),([129,0,1,2,3,4,5],[1,4,10,21],[0,2,3,6,7]),([713,0,1,2,3,4,49,5],[0,9,12,20,21],[0,6]),([143,0,1,2,3,4,49,5],[0,1,12,20],[0,2,4,6]),([160,1,20,2,3,4,5],[0,4,16,19,21],[0]),([50,0,20,2,3,4,5],[0,1,4,7,16],[0,1]),([62,0,1,20,2,3,4,5],[0,1,4,7,16,21],[0,1,6]),([62,0,1,2,3,4,5],[0,4,6,7,16,19,21],[0,1,6]),([66,506,0,1,2,3,4,5],[1,4,7,8,11,37],[0,6]),([66,0,1,20,2,3,4,5],[1,7,8,16,24,28],[0,2,4,6]),([208,0,1,2,23,3,4,5],[0,1,10,14,36],[0,1,2,5]),([48,0,2,23,3,4,5],[0,1,6,39],[0,1,2,3]),([46,506,0,1,2,3,4,5],[0,1,27],[0,1,6]),([46,0,1,20,2,3,4,5],[0,1,7,16,27],[0,1,2,3]),([46,0,1,2,3,4,49,5],[0,1,15,20],[0,2,3,6]),([38,0,1,2,3,4,5],[0,1,4,5],[0,2,3,6]),([611,0,1,2,23,3,4,5],[0,1,11,14,22],[0,2]),([236,0,1,2,23,3,4,5],[0,1,6,14,22],[0,2,3]),([81,85,0,2,3,4,5],[9,21],[0,6]),([81,0,1,2,3,8,4,5],[1,9,12],[0,2,3]),([81,0,20,2,3,4,5],[0,1,4,13,16],[0,1]),([27,0,1,20,2,3,4,5],[0,1,4,7,12,16],[0,1]),([27,0,1,2,3,4,5],[0,1,4,5,12,16,23,26],[0,1,2]),([96,506,0,1,2,3,4,5],[6,7,21,29,37],[0,6]),([96,0,1,20,2,3,4,5],[4,6,7,16,21,24,29],[0,4,6]),([86,0,1,2,3,4,5],[0,4,9,21],[0,2,6]),([487,506,0,1,2,3,4,5],[1,9,21,32,36],[0,1,7]),([487,0,1,20,2,3,4,5],[0,1,4,7,9,16,21,32],[0,1,3,7]),([139,0,1,20,2,3,4,5],[0,1,9,12],[0,1]),([199,0,1,20,2,3,4,5],[0,1,9,16,18,21],[0]),([506,109,0,1,2,3,4,5],[0,1,4,15],[0,1,2,6]),([506,85,0,1,2,3,4,5],[0,1,21,38],[0,6]),([506,0,1,223,2,3,4,5],[0,1,4,7,15],[0,1]),([506,0,1,445,2,3,4,5],[0,4,15,21],[0]),([506,0,1,462,2,3,4,5],[4,7,9,15,21,36],[0,1]),([506,0,1,2,23,3,4,5],[0,1,14],[0,1,6]),([506,0,1,2,3,8,4,5],[0,1,2,9,35,37],[0,1,6,7]),([506,0,1,2,3,501,4,5],[0,1,21,33],[0]),([506,0,1,2,3,4,49,5],[0,1,20,21],[0,6]),([506,0,1,2,3,4,9,5],[0,1,3,9,21,25],[0,1,6,7]),([506,0,1,2,3,4,5,31],[0,1,9,30],[0,1,6,7]),([506,0,1,2,3,4,5,94],[0,1,7,21,34],[0,1,6,7]),([703,1,2,3,4,5],[0,1,4,8,9],[5]),([109,0,1,20,2,3,4,5],[0,1,4,12,13],[0,1]),([706,0,1,3,4,5],[0,6,7,8,17],[3,9]),([172,0,1,2,23,3,4,5],[0,1,6,14,22],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock8_0Pools s0NAutos s0NBucket7 8 s0NBlock8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_0Mem : ∀ ns ∈ s0NBlock8_0, Impossible s0NG 8 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket7Ok s0NBlock8_0Ok
def s0NBlock8_1Specs : List PoolSpec := [(19,[]),(22,[]),(0,[(1,2,3)]),(0,[(1,2,4)]),(0,[]),(3,[]),(6,[]),(7,[]),(2,[]),(20,[]),(23,[]),(4,[]),(3,[(1,0,1)]),(0,[(1,1,2)]),(16,[]),(15,[]),(18,[]),(4,[(1,0,1)]),(0,[(1,1,4)]),(24,[]),(7,[(1,0,4)]),(6,[(1,0,1)]),(5,[(1,0,1)]),(7,[(1,2,4)]),(0,[(1,20,2)]),(7,[(1,20,4)]),(0,[(1,20,4)]),(0,[(0,2,3)]),(0,[(0,2,4)]),(0,[(0,2,5)]),(0,[(1,2,5)]),(0,[(0,4,5)]),(0,[(1,4,5)]),(6,[(2,0,1)]),(7,[(1,506,2)]),(17,[]),(0,[(1,582,2)]),(5,[])]
def s0NBlock8_1Pools : BT (Option BoundPool) := buildPoolsBT 6 s0NW s0NR s0NSlices s0NBlock8_1Specs
def s0NBlock8_1 : List NodeSpec := [([711,0,1,2,4,5],[0,1,7,8,37],[2,9]),([85,0,1,20,2,3,4,5],[0,1,4,15,16,19],[0,6]),([85,0,1,2,23,3,4,5],[0,1,13,16],[0,2,6]),([85,0,2,23,3,4,5],[1,5,7,9],[0,2,6,9]),([582,0,1,2,3,8,4,5],[0,1,2,9],[0,2,3]),([582,0,1,2,3,4,9,5],[0,1,3,9],[0,2,6]),([582,0,2,23,3,4,5],[0,1,9,13],[0,1,2,3,6]),([582,0,2,3,4,49,5],[0,1,18,19],[0,2,6]),([69,0,1,20,2,3,4,5],[0,1,4,7,9,15],[0]),([614,0,1,2,3,4,5],[0,1,13],[0,2,3,6]),([101,0,1,20,2,3,4,5],[0,1,4,7,9,15,19],[0,4]),([716,0,1,2,3,4,5],[0,6,18,19],[0,2]),([12,0,1,3,4,5],[0,1,4,6,7],[]),([17,0,1,2,3,5],[0,1,4,8,9],[0]),([6,0,1,2,3,8,4,5],[0,1,2,9,10],[0,1]),([6,0,1,2,3,4,9,5],[0,1,3,9,11],[0,1]),([0,722,1,2,3,4,5],[0,1,7,15],[0,1,2,3,5,6,9]),([0,682,1,2,3,4,5],[0,1,5,7,15],[0,1,2,3,4,6]),([0,629,2,23,3,4,5],[1,6,9],[0,2]),([0,1,113,20,2,3,4,5],[0,1,4,7,9,15],[0,1]),([0,1,598,2,3,4,5],[0,1,6,7,15],[0,2,3,6,7]),([0,1,115,20,2,3,4,5],[0,1,4,7,9,15,19],[0,6]),([0,1,140,2,3,4,5],[0,1,7,8,9,15],[0,2,3,5,6,9]),([0,1,20,223,2,3,4,5],[0,1,4,7,15,27],[0,1]),([0,1,20,445,2,3,4,5],[0,1,4,7,15,19,28],[0]),([0,1,20,462,2,3,4,5],[0,1,4,7,9,15,19,29],[0,1]),([0,1,20,2,21,3,4,5],[0,1,4,6,7,9,12,14,15],[0,2]),([0,1,20,2,23,3,4,5],[0,1,7,13,15],[0,2]),([0,1,20,2,41,3,4,5],[0,1,12,15,24],[0,1]),([0,1,20,2,3,8,4,5],[0,1,2,7,9,15,21,22],[0,1,2,3]),([0,1,20,2,3,501,4,5],[0,1,4,7,15,19,31],[0]),([0,1,20,2,3,4,28,5],[0,1,4,7,8,9,15,16,17,19,20],[0,1,2,3,4,6,8,9]),([0,1,20,2,3,4,49,5],[0,1,7,15,18,19],[0,6]),([0,1,20,2,3,4,60,5],[0,1,15,17,19,25,26],[0,1]),([0,1,20,2,3,4,9,5],[0,1,3,7,9,15,17,19,23],[0,1,2,4,6]),([0,1,20,2,3,4,5],[0,1,4,7,15],[0,1]),([0,1,20,2,3,4,5,31],[0,1,7,9,15,30],[0,1,2,4,6,7]),([0,1,20,2,3,4,5,94],[4,7,9,15,19,22,32],[0,1,2,3,6,7,8,9]),([0,1,2,138,3,4,5],[0,1,4,9],[0,1,2,3,6]),([0,1,2,507,3,4,5],[0,1,4,14,33,34],[0,2,7]),([0,1,2,689,4,5],[0,5,7,9,37],[2,6]),([0,1,2,583,3,4,5],[0,1,36],[0,2,3,6]),([0,1,2,7,3,4,5],[0,1,4],[0]),([0,1,2,704,3,4,5],[1,4,9],[2]),([0,1,2,23,41,3,4,5],[0,1,13],[0,2,3,6]),([0,1,2,23,248,3,4,5],[0,1,6,10,13,35],[0,2]),([0,1,2,23,3,26,4,5],[0,1,13],[0,1,2,3]),([0,1,2,23,3,25,4,5],[0,1,9,13],[0,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_1Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock8_1Pools s0NAutos s0NBucket7 8 s0NBlock8_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_1Mem : ∀ ns ∈ s0NBlock8_1, Impossible s0NG 8 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket7Ok s0NBlock8_1Ok
def s0NBlock8_2Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(7,[]),(2,[]),(20,[]),(23,[]),(4,[]),(1,[]),(0,[(1,1,2)]),(8,[]),(18,[]),(4,[(1,0,1)]),(0,[(1,1,4)]),(24,[]),(7,[(1,0,4)]),(6,[(1,0,1)]),(7,[(1,20,2)]),(0,[(1,20,2)]),(7,[(1,20,4)]),(0,[(1,20,4)]),(7,[(1,506,4)]),(0,[(1,582,4)]),(5,[(1,1,2)]),(6,[(1,1,3)]),(6,[(1,23,3)]),(5,[])]
def s0NBlock8_2Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock8_2Specs
def s0NBlock8_2 : List NodeSpec := [([0,1,2,23,3,4,49,5],[0,1,7,11],[0,2,6]),([0,1,2,23,3,4,83,5],[0,1,7,11,12],[0,1,2,4,5,7,8]),([0,1,2,23,3,4,5],[0,1,2,7],[0,2,3,6]),([0,1,2,23,3,4,5,16],[1,7,8,11,16],[0,1,2,3,5,7]),([0,1,2,41,3,4,5],[1,3,9,18,19,20],[0,1,2,4]),([0,1,2,3,271,4,5],[0,1,2],[0,2,3,5,6,9]),([0,1,2,3,259,4,5],[0,1,2,3],[0,2,3]),([0,1,2,3,605,4,5],[2,5,7,8],[3]),([0,1,2,3,631,4,5],[2,5,7,12],[3,5,9]),([0,1,2,3,8,4,49,5],[0,1,7,15],[0,2,3,5,6,8]),([0,1,2,3,25,4,5],[0,1,2,7,8,25,27],[0,1,2,3,6,7]),([0,1,2,3,4,82,5],[0,2,3,7,28],[0,2,4,6]),([0,1,2,3,4,543,5],[0,2,4,13,16,23],[0,1,6]),([0,1,2,3,4,587,5],[0,1,16,24],[0,2,6]),([0,1,2,3,4,15,5],[0,1,2,5],[0]),([0,1,2,3,4,49,60,5],[0,7,15,16],[0,2,6]),([0,1,2,3,4,49,39,5],[0,1,7,15,16],[0,2,6]),([0,1,2,3,4,49,5],[0,2,7,16],[0,2,6]),([0,1,2,3,4,60,5],[0,3,14,16,21,22],[0,1,2,6,8]),([0,1,2,3,4,5,273],[0,1,2,16],[0,3,5,9]),([0,1,2,3,4,5,607],[1,2,8,16],[7]),([0,1,2,3,4,5,128],[1,2,8,16],[0,1,2,3,4,6,7]),([0,1,2,3,15,5],[0,1,2,5],[0]),([0,1,2,259,4,5],[0,1,3,5,9],[0,2]),([0,1,2,631,4,5],[0,1,5,6,7],[0,2,6,9]),([0,1,7,3,4,5],[0,1,2,3],[0]),([0,1,704,3,4,5],[0,3,5,6,7,28],[0]),([0,20,2,23,3,4,5],[1,2,5,7,11,18],[0,1]),([0,20,2,3,4,49,5],[0,2,5,14,15,16],[0,1]),([0,2,23,3,26,4,5],[0,1,7,8,10,25,26],[0,1,2,3,6,7]),([0,2,23,3,4,5,32],[1,3,5,8,16],[0,1,2,3,6,7]),([1,140,2,3,4,5],[0,1,5,6,7],[0,5,6]),([1,20,2,3,4,28,5],[0,2,5,6,14,16,17],[0,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_2Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock8_2Pools s0NAutos s0NBucket7 8 s0NBlock8_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_2Mem : ∀ ns ∈ s0NBlock8_2, Impossible s0NG 8 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket7Ok s0NBlock8_2Ok
def s0NNodes8 : List NodeSpec := s0NBlock8_0 ++ s0NBlock8_1 ++ s0NBlock8_2
def s0NBucket8 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 8 xs.toFinset) s0NBucket8 := buildBucketsBT_of_mem (forall_append (forall_append s0NBlock8_0Mem s0NBlock8_1Mem) s0NBlock8_2Mem)
def s0NBlock9_0Specs : List PoolSpec := [(19,[]),(22,[]),(0,[]),(3,[]),(6,[]),(7,[]),(2,[]),(20,[]),(4,[]),(1,[]),(24,[])]
def s0NBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock9_0Specs
def s0NBlock9_0 : List NodeSpec := [([50,0,1,2,3,4,5],[0,1,2,3,4,5,8],[0,1,2,3,5,6,9]),([81,0,1,2,3,4,5],[0,2,3,4,5,6,9],[0,1,2,3,4,6]),([506,0,1,2,3,4,5],[2,3,4,5,6,9],[0,1,6,7]),([582,0,1,2,3,4,5],[0,1,2,3,4,5,6,9],[0,1,2,3,6,7]),([6,0,1,2,3,4,5],[0,1,2,3,4,5,6,9],[0,1]),([0,597,1,2,3,4,5],[0,2,3,4,5,6,9],[0,2,3,6,7]),([0,629,1,2,3,4,5],[1,2,3,4,5,7,8,9],[0,2,3,5,6,9]),([0,1,20,2,3,4,5],[2,3,4,5,8,9],[0,1]),([0,1,2,23,3,4,5],[1,2,3,4,5,8,9],[0,2,3,6,7]),([0,1,2,3,4,49,5],[0,2,3,4,5,8,9,10],[0,1,2,3,4,5,6,8,9])]
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
def s0NBlock10_0Specs : List PoolSpec := []
def s0NBlock10_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NBlock10_0Specs
def s0NBlock10_0 : List NodeSpec := [([0,1,2,3,4,5],[],[0,1,2,3,4,5,6,7,8,9])]
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
lemma q0 : Lower (varsOf 123) 0xffffffffffffffeeffeeffaaeeeecc00 11 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (4, 5), (3, 4), (1, 2), (2, 3)]) (roots2 := s0NR) (T2 := s0NG) _ s0NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q24 : Lower (varsOf 126) 0xfffffffffffffffcfffcfff0fcfccc00 11 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (4, 5), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := s0NR) (T2 := s0NG) _ s0NBound
  decide +kernel
def lb603 : Nat := 0xfcc00000fcc00000fcc00000fcc00000
lemma lb639 : liftCheck 0 16 lb77 lb603 lb548 lb544 [(VAR 4,22,6)] = true := by decide +kernel
lemma lb638 : Lower lb77 lb603 5 := lift_of lb639 lb568
def lb604 : Nat := 0xfcc0fc00fcc0fc00fcc0fc00fcc0fc00
lemma lb641 : liftCheck 0 16 lb77 lb604 lb548 lb544 [(VAR 4,22,6)] = true := by decide +kernel
lemma lb640 : Lower lb77 lb604 5 := lift_of lb641 lb568
def lb605 : Nat := 0xffccff00ffcc0000ffccff00ffcc0000
lemma lb643 : carryOK [(1,2)] lb8 lb605 lb11 lb576 = true := by decide +kernel
lemma lb642 : Lower lb8 lb605 4 := carry_of lb643 lb598
def lb606 : Nat := 0xfcc0fc00fcc00000fcc0fc00fcc00000
def lb649 : List Nat := [22,22,22,26,26,26,28,28,28,30,42,42,42,44,44,44,46,46,54,54,54,58,58,60,60,22,22,22,22,22,26,26,26,26,26,28,28,28,28,28,42,42,42,42,42,44,44,44,44,44]
def lb645 : List Nat := [20,18,6,24,18,10,24,20,12,14,40,34,10,40,36,12,38,14,52,50,38,56,50,56,52,14,38,50,52,56,14,38,50,52,56,14,38,50,52,56,14,38,50,52,56,14,38,50,52,56]
def lb634 : Nat := fullMask 50
def lb613 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1f07fe7f1e3f,0xe739ce5b1a36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3e0f83f9fe3c7,0x16b5ad717c385),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffffc1e3fff8,0x2318c62a2b768),(0xffff0000ffff0000ffff0000ffff0000,0xfffffc03ff,0x39ce739ec00db),(0xffffffff00000000ffffffff00000000,0x3ff0001fffc00,0x3def7bdfd6c00)]
def lb664 : List (Nat × Nat × Nat) := [(2,0,2),(0,0,2),(0,0,1),(3,6,1)]
def lb609 : Array Decor := buildWires lb613 lb664
def lb611 : Array (List (Nat × Nat)) := #[[],[(1,2)]]
def lb661 : List (Nat × Nat) := [(subcube 0 32,5),(subcube 32 0,5),(subcube 0 2,4),(subcube 0 4,4),(subcube 0 48,4)]
def lb662 : Array (Nat × Nat) := lb661.toArray
def lb650 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def lb607 : Array (Option BoundPool) := buildPools lb609 lb41 lb662 lb650
lemma lb637 : goodPairs lb606 lb649 lb645 := goodPairs_of (by decide +kernel)
lemma lb614 : ∀ x ∈ lb613, faithful lb649 lb645 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb610 : ∀ x ∈ lb609.toList, faithful lb649 lb645 x ∧ x.1 < 2^128 := buildWires_faithful lb614
lemma lb612 : ∀ sw ∈ lb611.toList, swapsValid sw = true ∧ permWord sw lb606 = lb606 := autos_of (by decide +kernel)
lemma lb652 : sliceDirectCheck 0 32 0 lb41 lb606 lb77 lb604 = true := by decide +kernel
lemma lb651 : Slice lb41 lb606 (subcube 0 32) 5 := slice_direct lb652 lb640
lemma lb654 : sliceDirectCheck 32 0 0 lb41 lb606 lb77 lb603 = true := by decide +kernel
lemma lb653 : Slice lb41 lb606 (subcube 32 0) 5 := slice_direct lb654 lb638
lemma lb656 : sliceDirectCheck 0 2 0 lb41 lb606 lb11 lb576 = true := by decide +kernel
lemma lb655 : Slice lb41 lb606 (subcube 0 2) 4 := slice_direct lb656 lb598
lemma lb658 : sliceDirectCheck 0 4 0 lb41 lb606 lb8 lb605 = true := by decide +kernel
lemma lb657 : Slice lb41 lb606 (subcube 0 4) 4 := slice_direct lb658 lb642
lemma lb660 : sliceDirectCheck 0 48 0 lb41 lb606 lb548 lb544 = true := by decide +kernel
lemma lb659 : Slice lb41 lb606 (subcube 0 48) 4 := slice_direct lb660 lb568
set_option maxRecDepth 200000 in
lemma lb663 : ∀ i (hi : i < lb662.size), Slice lb41 lb606 lb662[i].1 lb662[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb41 lb606 p.1 p.2) (forall_cons lb651 (forall_cons lb653 (forall_cons lb655 (forall_cons lb657 (forall_cons lb659 (fun _ h => (List.not_mem_nil h).elim))))))
lemma lb608 : ∀ i (hi : i < lb607.size), ∀ c, lb607[i] = some c → ValidPool lb41 lb606 c := buildPools_sound lb663
lemma lb626 : ∀ i (hi : i < lb449.size), ∀ xs ∈ lb449[i], Impossible lb606 (0 - 1) xs.toFinset := by intro i hi; simp [lb449] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb627 : checkNodes lb609 lb606 lb634 lb607 lb611 lb449 0 lb492 = true := by decide +kernel
def lb615 : Array (List (List Nat)) := buildBuckets 1 lb609 lb492
lemma lb616 : ∀ i (hi : i < lb615.size), ∀ xs ∈ lb615[i], Impossible lb606 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb637 lb610 lb608 lb612 lb626 lb627
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb628 : checkNodes lb609 lb606 lb634 lb607 lb611 lb615 1 lb492 = true := by decide +kernel
lemma lb617 : ∀ i (hi : i < lb615.size), ∀ xs ∈ lb615[i], Impossible lb606 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb637 lb610 lb608 lb612 lb616 lb628
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb629 : checkNodes lb609 lb606 lb634 lb607 lb611 lb615 2 lb492 = true := by decide +kernel
lemma lb618 : ∀ i (hi : i < lb615.size), ∀ xs ∈ lb615[i], Impossible lb606 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb637 lb610 lb608 lb612 lb617 lb629
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb630 : checkNodes lb609 lb606 lb634 lb607 lb611 lb615 3 lb492 = true := by decide +kernel
lemma lb619 : ∀ i (hi : i < lb615.size), ∀ xs ∈ lb615[i], Impossible lb606 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb637 lb610 lb608 lb612 lb618 lb630
def lb646 : List NodeSpec := [([8,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb631 : checkNodes lb609 lb606 lb634 lb607 lb611 lb615 4 lb646 = true := by decide +kernel
def lb620 : Array (List (List Nat)) := buildBuckets 1 lb609 lb646
lemma lb621 : ∀ i (hi : i < lb620.size), ∀ xs ∈ lb620[i], Impossible lb606 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb637 lb610 lb608 lb612 lb619 lb631
def lb647 : List NodeSpec := [([5,0,1,2,3,4],[0,1,2],[]),([6,0,1,2,3,4],[3],[0]),([7,0,1,2,3,4],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb632 : checkNodes lb609 lb606 lb634 lb607 lb611 lb620 5 lb647 = true := by decide +kernel
def lb622 : Array (List (List Nat)) := buildBuckets 2 lb609 lb647
lemma lb623 : ∀ i (hi : i < lb622.size), ∀ xs ∈ lb622[i], Impossible lb606 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb637 lb610 lb608 lb612 lb621 lb632
def lb648 : List NodeSpec := [([0,1,2,3,4],[2,3,4,1],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb633 : checkNodes lb609 lb606 lb634 lb607 lb611 lb622 6 lb648 = true := by decide +kernel
def lb624 : Array (List (List Nat)) := buildBuckets 1 lb609 lb648
lemma lb625 : ∀ i (hi : i < lb624.size), ∀ xs ∈ lb624[i], Impossible lb606 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb637 lb610 lb608 lb612 lb623 lb633
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb636 : forestRootCheck lb41 lb606 [(VAR 1,22,20),(VAR 2,22,18),(VAR 3,26,18),(VAR 4,22,6),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb635 : bucketContains lb624 lb41 = true := by decide +kernel
lemma lb644 : Lower lb41 lb606 7 := lower_of_forest lb636 lb625 lb635
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q26d : Lower (varsOf 62) 0xfcf0f000ccc0c000fcf0f000ccc0c000 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (1, 2)]) (roots2 := lb41) (T2 := lb606) _ lb644
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q26 : Lower (varsOf 62) 0xfffcfcccfff0f0c0fffcfcccfff0f0c0 7 := dualLower (by decide +kernel) (by decide +kernel) q26d
def lb681 : BT Decor := buildWiresBT 2 lb552 lb82
set_option maxRecDepth 500000 in
lemma lb682 : btAll (fun x => faithful lb574 lb573 x ∧ x.1 < 2^128) lb681 := buildWiresBT_faithful lb553
set_option maxRecDepth 500000 in
lemma lb688 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb544 = lb544) lb363 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb757 : btAll (fun o => ∀ p, o = some p → Slice lb548 lb544 p.1 p.2) lb79 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb548 lb544 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb696 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb544 2 xs.toFinset) lb67 := trivial
def lb672 : BT (Option BoundPool) := buildPoolsSubBT 1 lb681 lb548 lb79 lb404 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb709 : checkNodesBT lb681 lb544 lb378 lb672 lb363 lb67 3 lb400 = true := by decide +kernel
def lb697 : BT (List (List Nat)) := buildBucketsBT lb681 lb400
set_option maxRecDepth 500000 in
lemma lb698 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb544 3 xs.toFinset) lb697 :=
  buildBucketsBT_sound (by decide) lb567 lb682 (buildPoolsSubBT_sound lb757) lb688 lb696 lb709
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb716 : forestRootCheck lb548 lb544 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb715 : bucketContainsBT lb697 lb548 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb723 : Lower lb548 lb544 4 := lower_of_forestBT lb716 lb698 lb715
def lb665 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def lb677 : List Nat := varsOf 7
lemma lb728 : carryOK [(0,3),(0,2),(0,1)] lb677 lb665 lb548 lb544 = true := by decide +kernel
lemma lb724 : Lower lb677 lb665 4 := carry_of lb728 lb723
def lb668 : Nat := 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8
def lb680 : List Nat := varsOf 39
lemma lb730 : liftCheck 32 0 lb680 lb668 lb677 lb665 [(VAR 5,33,1)] = true := by decide +kernel
lemma lb729 : Lower lb680 lb668 5 := lift_of lb730 lb724
def lb669 : Nat := 0xfaaafaaaf0a0f0a0faaafaaaf0a0f0a0
def lb742 : List Nat := [5,5,12,12,13,33,33,37,41,41,44,44,5,5,5,12,12,12,33,33,33]
def lb737 : List Nat := [4,1,8,4,9,32,1,36,40,9,40,36,9,36,40,9,36,40,9,36,40]
def lb694 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1c73f3,0x49252),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3fc9f,0x92889),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x38f1c,0x16d714),(0xffffffff00000000ffffffff00000000,0x1c0fe0,0x1b6da0)]
def lb685 : BT Decor := buildWiresBT 2 lb694 lb82
lemma lb722 : goodPairs lb669 lb742 lb737 := goodPairs_of (by decide +kernel)
lemma lb695 : ∀ x ∈ lb694, faithful lb742 lb737 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb686 : btAll (fun x => faithful lb742 lb737 x ∧ x.1 < 2^128) lb685 := buildWiresBT_faithful lb695
set_option maxRecDepth 500000 in
lemma lb691 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb669 = lb669) lb363 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb760 : btAll (fun o => ∀ p, o = some p → Slice lb520 lb669 p.1 p.2) lb79 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb520 lb669 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb706 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb669 2 xs.toFinset) lb67 := trivial
def lb676 : BT (Option BoundPool) := buildPoolsSubBT 1 lb685 lb520 lb79 lb404 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb713 : checkNodesBT lb685 lb669 lb32 lb676 lb363 lb67 3 lb600 = true := by decide +kernel
def lb707 : BT (List (List Nat)) := buildBucketsBT lb685 lb600
set_option maxRecDepth 500000 in
lemma lb708 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb669 3 xs.toFinset) lb707 :=
  buildBucketsBT_sound (by decide) lb722 lb686 (buildPoolsSubBT_sound lb760) lb691 lb706 lb713
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb720 : forestRootCheck lb520 lb669 [(VAR 0,5,4),(VAR 2,5,1),(VAR 3,12,4),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb719 : bucketContainsBT lb707 lb520 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb731 : Lower lb520 lb669 4 := lower_of_forestBT lb720 lb708 lb719
def lb670 : Nat := 0xfce8fce8fce8fce8fce8fce8fce8fce8
lemma lb733 : liftCheck 1 0 lb353 lb670 lb548 lb544 [(VAR 0,3,2)] = true := by decide +kernel
lemma lb732 : Lower lb353 lb670 5 := lift_of lb733 lb723
def lb671 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
lemma lb735 : liftCheck 1 0 lb353 lb671 lb548 lb544 [(VAR 0,1,0)] = true := by decide +kernel
lemma lb734 : Lower lb353 lb671 5 := lift_of lb735 lb723
def lb666 : Nat := 0xeeaaeeaacc88cc88eeaaeeaacc88cc88
def lb678 : List Nat := varsOf 43
lemma lb726 : carryOK [(1,2)] lb678 lb666 lb520 lb669 = true := by decide +kernel
lemma lb725 : Lower lb678 lb666 4 := carry_of lb726 lb731
def lb667 : Nat := 0xfeeafeeafce8fce8feeafeeafce8fce8
def lb679 : List Nat := varsOf 47
def lb741 : List Nat := [3,3,5,5,6,6,10,10,11,12,12,13,33,33,35,37,38,38,41,41,42,42,44,44,3,3,3,3,5,5,5,5,6,6,6,6,10,10,10,10,12,12,12,12,33,33,33,33]
def lb736 : List Nat := [2,1,4,1,4,2,8,2,9,8,4,9,32,1,34,36,36,34,40,9,40,34,40,36,9,34,36,40,9,34,36,40,9,34,36,40,9,34,36,40,9,34,36,40,9,34,36,40]
def lb714 : Nat := fullMask 48
def lb692 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf000ff0cf90f,0x11111108290a),(0xcccccccccccccccccccccccccccccccc,0xff0f3341f3,0x2222222240a1),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0ff0c38e3c,0x444444818414),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xff000fc0fc0,0x9999995c0b40),(0xffffffff00000000ffffffff00000000,0xf00000fff000,0xeeeeeef7d000)]
def lb761 : List (Nat × Nat × Nat) := [(1,1,2),(2,5,3)]
def lb683 : BT Decor := buildWiresBT 3 lb692 lb761
def lb687 : List (List (Nat × Nat)) := [[]]
def lb689 : BT (List (Nat × Nat)) := btOfList 1 lb687
def lb756 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 8 0,5),some (subcubeFast 0 32,5),some (subcubeFast 32 0,5),some (subcubeFast 1 32,4),some (subcubeFast 4 0,4)]
def lb758 : BT (Option (Nat × Nat)) := btOfList 3 lb756
def lb743 : BT (Option PoolSpec) := btOfList 3 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[])]
lemma lb721 : goodPairs lb667 lb741 lb736 := goodPairs_of (by decide +kernel)
lemma lb693 : ∀ x ∈ lb692, faithful lb741 lb736 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb684 : btAll (fun x => faithful lb741 lb736 x ∧ x.1 < 2^128) lb683 := buildWiresBT_faithful lb693
set_option maxRecDepth 500000 in
lemma lb690 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb667 = lb667) lb689 := btAll_ofList (autos_of (by decide +kernel))
lemma lb745 : sliceDirectCheck 2 0 0 lb679 lb667 lb520 lb669 = true := by decide +kernel
lemma lb744 : Slice lb679 lb667 (subcubeFast 2 0) 4 := slice_fast_direct lb745 lb731
lemma lb747 : sliceDirectCheck 8 0 0 lb679 lb667 lb680 lb668 = true := by decide +kernel
lemma lb746 : Slice lb679 lb667 (subcubeFast 8 0) 5 := slice_fast_direct lb747 lb729
lemma lb749 : sliceDirectCheck 0 32 0 lb679 lb667 lb353 lb671 = true := by decide +kernel
lemma lb748 : Slice lb679 lb667 (subcubeFast 0 32) 5 := slice_fast_direct lb749 lb734
lemma lb751 : sliceDirectCheck 32 0 0 lb679 lb667 lb353 lb670 = true := by decide +kernel
lemma lb750 : Slice lb679 lb667 (subcubeFast 32 0) 5 := slice_fast_direct lb751 lb732
lemma lb753 : sliceDirectCheck 1 32 0 lb679 lb667 lb548 lb544 = true := by decide +kernel
lemma lb752 : Slice lb679 lb667 (subcubeFast 1 32) 4 := slice_fast_direct lb753 lb723
lemma lb755 : sliceDirectCheck 4 0 0 lb679 lb667 lb678 lb666 = true := by decide +kernel
lemma lb754 : Slice lb679 lb667 (subcubeFast 4 0) 4 := slice_fast_direct lb755 lb725
set_option maxRecDepth 500000 in
lemma lb759 : btAll (fun o => ∀ p, o = some p → Slice lb679 lb667 p.1 p.2) lb758 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb679 lb667 p.1 p.2) (forall_cons (fun _ h => by cases h; exact lb744) (forall_cons (fun _ h => by cases h; exact lb746) (forall_cons (fun _ h => by cases h; exact lb748) (forall_cons (fun _ h => by cases h; exact lb750) (forall_cons (fun _ h => by cases h; exact lb752) (forall_cons (fun _ h => by cases h; exact lb754) (fun _ h => (List.not_mem_nil h).elim)))))))
lemma lb699 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb667 3 xs.toFinset) lb67 := trivial
def lb738 : List NodeSpec := [([6,0,1,2,4],[],[])]
def lb673 : BT (Option BoundPool) := buildPoolsSubBT 3 lb683 lb679 lb758 lb743 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb710 : checkNodesBT lb683 lb667 lb714 lb673 lb689 lb67 4 lb738 = true := by decide +kernel
def lb700 : BT (List (List Nat)) := buildBucketsBT lb683 lb738
set_option maxRecDepth 500000 in
lemma lb701 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb667 4 xs.toFinset) lb700 :=
  buildBucketsBT_sound (by decide) lb721 lb684 (buildPoolsSubBT_sound lb759) lb690 lb699 lb710
def lb739 : List NodeSpec := [([0,1,2,5,3,4],[0,1,2,3],[0])]
def lb674 : BT (Option BoundPool) := buildPoolsSubBT 3 lb683 lb679 lb758 lb743 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb711 : checkNodesBT lb683 lb667 lb714 lb674 lb689 lb700 5 lb739 = true := by decide +kernel
def lb702 : BT (List (List Nat)) := buildBucketsBT lb683 lb739
set_option maxRecDepth 500000 in
lemma lb703 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb667 5 xs.toFinset) lb702 :=
  buildBucketsBT_sound (by decide) lb721 lb684 (buildPoolsSubBT_sound lb759) lb690 lb701 lb711
def lb740 : List NodeSpec := [([0,1,2,3,4],[4,1,3,0,5],[0])]
def lb675 : BT (Option BoundPool) := buildPoolsSubBT 3 lb683 lb679 lb758 lb743 [0,1,3,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb712 : checkNodesBT lb683 lb667 lb714 lb675 lb689 lb702 6 lb740 = true := by decide +kernel
def lb704 : BT (List (List Nat)) := buildBucketsBT lb683 lb740
set_option maxRecDepth 500000 in
lemma lb705 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb667 6 xs.toFinset) lb704 :=
  buildBucketsBT_sound (by decide) lb721 lb684 (buildPoolsSubBT_sound lb759) lb690 lb703 lb712
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb718 : forestRootCheck lb679 lb667 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,10,2),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb717 : bucketContainsBT lb704 lb679 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb727 : Lower lb679 lb667 7 := lower_of_forestBT lb718 lb705 lb717
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q27 : Lower (varsOf 61) 0xfffafaaafffafa00fffafaaafffafa00 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (1, 2)]) (roots2 := lb679) (T2 := lb667) _ lb727
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q28d : Lower (varsOf 59) 0xffaaaa0088888800ffaaaa0088888800 7 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb41) (T2 := lb606) _ lb644
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q28 : Lower (varsOf 59) 0xffeeeeeeffaaaa00ffeeeeeeffaaaa00 7 := dualLower (by decide +kernel) (by decide +kernel) q28d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q29 : Lower (varsOf 55) 0xfefeeeeefafac0c0fefeeeeefafac0c0 7 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3)]) (roots2 := lb41) (T2 := lb31) _ lb20
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q30 : Lower (varsOf 47) 0xfeeefeeefac0fac0feeefeeefac0fac0 7 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4)]) (roots2 := lb41) (T2 := lb31) _ lb20
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q31 : Lower (varsOf 31) 0xfffafac0fffafac0fffafac0fffafac0 7 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb679) (T2 := lb667) _ lb727
  decide +kernel
def lb762 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def lb766 : List Nat := varsOf 22
def lb790 : List Nat := [6,6,18,18,20,20,6,18,20]
def lb789 : List Nat := [4,2,16,2,16,4,16,4,2]
def lb770 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def lb767 : Array Decor := buildWires lb770 lb82
def lb764 : Array (Option BoundPool) := buildPools lb767 lb766 lb510 lb81
lemma lb785 : goodPairs lb762 lb790 lb789 := goodPairs_of (by decide +kernel)
lemma lb771 : ∀ x ∈ lb770, faithful lb790 lb789 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb768 : ∀ x ∈ lb767.toList, faithful lb790 lb789 x ∧ x.1 < 2^128 := buildWires_faithful lb771
lemma lb769 : ∀ sw ∈ lb435.toList, swapsValid sw = true ∧ permWord sw lb762 = lb762 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma lb791 : ∀ i (hi : i < lb510.size), Slice lb766 lb762 lb510[i].1 lb510[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb766 lb762 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb765 : ∀ i (hi : i < lb764.size), ∀ c, lb764[i] = some c → ValidPool lb766 lb762 c := buildPools_sound lb791
lemma lb778 : ∀ i (hi : i < lb449.size), ∀ xs ∈ lb449[i], Impossible lb762 (0 - 1) xs.toFinset := by intro i hi; simp [lb449] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb779 : checkNodes lb767 lb762 lb378 lb764 lb435 lb449 0 lb492 = true := by decide +kernel
def lb772 : Array (List (List Nat)) := buildBuckets 1 lb767 lb492
lemma lb773 : ∀ i (hi : i < lb772.size), ∀ xs ∈ lb772[i], Impossible lb762 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb785 lb768 lb765 lb769 lb778 lb779
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb780 : checkNodes lb767 lb762 lb378 lb764 lb435 lb772 1 lb492 = true := by decide +kernel
lemma lb774 : ∀ i (hi : i < lb772.size), ∀ xs ∈ lb772[i], Impossible lb762 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb785 lb768 lb765 lb769 lb773 lb780
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb781 : checkNodes lb767 lb762 lb378 lb764 lb435 lb772 2 lb492 = true := by decide +kernel
lemma lb775 : ∀ i (hi : i < lb772.size), ∀ xs ∈ lb772[i], Impossible lb762 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb785 lb768 lb765 lb769 lb774 lb781
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb782 : checkNodes lb767 lb762 lb378 lb764 lb435 lb772 3 lb400 = true := by decide +kernel
def lb776 : Array (List (List Nat)) := buildBuckets 1 lb767 lb400
lemma lb777 : ∀ i (hi : i < lb776.size), ∀ xs ∈ lb776[i], Impossible lb762 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb785 lb768 lb765 lb769 lb775 lb782
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb784 : forestRootCheck lb766 lb762 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb783 : bucketContains lb776 lb766 = true := by decide +kernel
lemma lb786 : Lower lb766 lb762 4 := lower_of_forest lb784 lb777 lb783
def lb763 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
lemma lb788 : liftCheck 0 8 lb77 lb763 lb766 lb762 [(VAR 3,14,6)] = true := by decide +kernel
lemma lb787 : Lower lb77 lb763 5 := lift_of lb788 lb786
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q32d : Lower (varsOf 57) 0xffaaaa0000000000ffaaaa0000000000 5 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (3, 4), (2, 3), (0, 1)]) (roots2 := lb77) (T2 := lb763) _ lb787
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q32 : Lower (varsOf 57) 0xffffffffffaaaa00ffffffffffaaaa00 5 := dualLower (by decide +kernel) (by decide +kernel) q32d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q33d : Lower (varsOf 57) 0xffaaaa00aaaaaa00ffaaaa00aaaaaa00 5 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3)]) (roots2 := lb521) (T2 := lb517) _ lb539
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q33 : Lower (varsOf 57) 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00 5 := dualLower (by decide +kernel) (by decide +kernel) q33d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q34d : Lower (varsOf 30) 0xfcf0f000fcf0f000fcf0f000fcf0f000 5 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (3, 4), (0, 1), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb521) (T2 := lb517) _ lb539
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q34 : Lower (varsOf 30) 0xfff0f0c0fff0f0c0fff0f0c0fff0f0c0 5 := dualLower (by decide +kernel) (by decide +kernel) q34d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q35d : Lower (varsOf 29) 0xffa0a000ffa0a000ffa0a000ffa0a000 5 := by
  apply carry_of (swaps := [(4, 5), (0, 1)]) (roots2 := lb2) (T2 := lb545) _ lb569
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q35 : Lower (varsOf 29) 0xfffafa00fffafa00fffafa00fffafa00 5 := dualLower (by decide +kernel) (by decide +kernel) q35d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q36d : Lower (varsOf 53) 0xfafaa0a0aaaaa0a0fafaa0a0aaaaa0a0 5 := by
  apply carry_of (swaps := [(0, 1), (1, 2)]) (roots2 := lb521) (T2 := lb517) _ lb539
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q36 : Lower (varsOf 53) 0xfafaaaaafafaa0a0fafaaaaafafaa0a0 5 := dualLower (by decide +kernel) (by decide +kernel) q36d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q37d : Lower (varsOf 51) 0xeeeeaaaa88888888eeeeaaaa88888888 5 := by
  apply carry_of (swaps := [(4, 5), (0, 1)]) (roots2 := lb521) (T2 := lb517) _ lb539
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q37 : Lower (varsOf 51) 0xeeeeeeeeaaaa8888eeeeeeeeaaaa8888 5 := dualLower (by decide +kernel) (by decide +kernel) q37d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q38d : Lower (varsOf 43) 0xeeaaeeaa88888888eeaaeeaa88888888 5 := by
  apply carry_of (swaps := [(4, 5), (3, 4), (0, 1)]) (roots2 := lb521) (T2 := lb517) _ lb539
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q38 : Lower (varsOf 43) 0xeeeeeeeeaa88aa88eeeeeeeeaa88aa88 5 := dualLower (by decide +kernel) (by decide +kernel) q38d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q39d : Lower (varsOf 39) 0xecececec88888888ecececec88888888 5 := by
  apply carry_of (swaps := [(4, 5), (3, 4), (2, 3)]) (roots2 := lb521) (T2 := lb517) _ lb539
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q39 : Lower (varsOf 39) 0xeeeeeeeec8c8c8c8eeeeeeeec8c8c8c8 5 := dualLower (by decide +kernel) (by decide +kernel) q39d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q40 : Lower (varsOf 54) 0xfcfcccccf0f0c0c0fcfcccccf0f0c0c0 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3)]) (roots2 := lb11) (T2 := lb576) _ lb598
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q41 : Lower (varsOf 53) 0xfafaaaaafafa0000fafaaaaafafa0000 4 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (1, 2), (0, 1)]) (roots2 := lb11) (T2 := lb576) _ lb598
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q42 : Lower (varsOf 46) 0xfcccfcccf0c0f0c0fcccfcccf0c0f0c0 4 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (1, 2), (2, 3)]) (roots2 := lb11) (T2 := lb576) _ lb598
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q43 : Lower (varsOf 45) 0xfaaafaaafa00fa00faaafaaafa00fa00 4 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (1, 2), (0, 1)]) (roots2 := lb11) (T2 := lb576) _ lb598
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q44 : Lower (varsOf 39) 0xeeeeeeeec0c0c0c0eeeeeeeec0c0c0c0 4 := by
  apply carry_of (swaps := [(4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3)]) (roots2 := lb11) (T2 := lb576) _ lb598
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q45 : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000 4 := by
  apply carry_of (swaps := [(3, 4), (2, 3), (1, 2)]) (roots2 := lb548) (T2 := lb544) _ lb568
  decide +kernel
def s1NR : List Nat := varsOf 63
def s1NG : Nat := 0xfffefeeefffafac0fffefeeefffafac0
def s1NPos : List Nat := [6,6,6,6,6,7,7,9,9,9,9,9,11,11,12,12,12,12,13,17,17,17,19,19,20,20,20,21,21,24,24,25,26,26,33,33,33,33,34,34,34,35,37,37,38,41,42,42,44,44,49,50,50,52,52,56,56]
def s1NNeg : List Nat := [2,3,4,5,18,3,5,0,1,3,8,10,3,10,0,4,8,10,5,1,3,16,3,18,4,5,16,1,5,8,16,1,10,18,1,3,32,40,2,3,32,3,5,36,36,40,10,40,36,40,48,18,48,36,48,40,48]
def s1NMask : Nat := fullMask 57
def s1NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x42e3c98fc3fe0,0x68c9a5c136a),(0xcccccccccccccccccccccccccccccccc,0x18d3c300c0307f,0x842cb00d23a33),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x631c001f07c07f,0x211c001304804c),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x183e003e007ff80,0x82e02120032c00),(0xffff0000ffff0000ffff0000ffff0000,0x1fc0003fff80000,0x15c000244a00010),(0xffffffff00000000ffffffff00000000,0x1fffffc00000000,0x1f7b93000000000)]
def s1NSteps : List (Nat × Nat × Nat) := [(1,0,1),(2,6,5),(1,3,4),(3,0,8),(1,0,2),(1,0,3),(1,2,4),(2,10,3),(1,10,4),(2,10,4),(1,11,4),(2,11,4),(1,0,4),(1,2,3),(1,10,3),(0,20,4),(2,20,4),(1,20,4),(3,3,23),(1,13,4),(2,13,4),(1,2,8),(3,2,11),(3,2,18),(1,1,2),(1,1,11),(1,1,4),(1,28,4),(3,2,16),(1,17,2),(1,0,5),(1,1,3),(3,0,37),(1,38,4),(2,37,4),(1,40,0),(1,1,5),(1,2,5),(1,9,2),(1,1,8),(3,2,45),(3,2,8),(1,8,5),(1,3,5),(1,4,5)]
def s1NW : BT Decor := buildWiresBT 6 s1NBase s1NSteps
def s1NAutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(0,2),(1,5)],[(0,2),(1,5),(3,4)]]
def s1NAutos : BT (List (Nat × Nat)) := btOfList 2 s1NAutoList
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
def s1NSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 1 0,7),some (subcubeFast 2 0,7),some (subcubeFast 4 0,7),some (subcubeFast 8 0,7),some (subcubeFast 16 0,7),some (subcubeFast 32 0,7),some (0x999999990000000099999999,7),some (subcubeFast 4 2,5),some (subcubeFast 6 0,5),some (subcubeFast 33 0,5),some (subcubeFast 34 0,5),some (0x990099009900990099009900990099,5),some (0xa500a500a500a500a500a500a500a5,5),some (0xa5a50000a5a50000a5a50000a5a5,5),some (0xcc330000cc330000cc330000cc33,5),some (subcubeFast 9 0,4),some (subcubeFast 10 0,4),some (subcubeFast 17 0,4),some (subcubeFast 18 0,4),some (subcubeFast 24 0,4),some (subcubeFast 3 32,4),some (subcubeFast 36 2,4),some (subcubeFast 38 0,4)]
def s1NSlices : BT (Option (Nat × Nat)) := btOfList 5 s1NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice0 : Slice s1NR s1NG (subcubeFast 1 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffcfcccfff0f0c0fffcfcccfff0f0c0) (by decide +kernel) q26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice1 : Slice s1NR s1NG (subcubeFast 2 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafaaafffafa00fffafaaafffafa00) (by decide +kernel) q27
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice2 : Slice s1NR s1NG (subcubeFast 4 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeeeeeffaaaa00ffeeeeeeffaaaa00) (by decide +kernel) q28
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice3 : Slice s1NR s1NG (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeeeeefafac0c0fefeeeeefafac0c0) (by decide +kernel) q29
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice4 : Slice s1NR s1NG (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfeeefeeefac0fac0feeefeeefac0fac0) (by decide +kernel) q30
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice5 : Slice s1NR s1NG (subcubeFast 32 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfffafac0fffafac0fffafac0fffafac0) (by decide +kernel) q31
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice6 : Slice s1NR s1NG 0x999999990000000099999999 7 := mappedSlice (f := identifyRow 32 0 0 1) (R := varsOf 29) (G := 0xfffafaa0fffafaa0fffafaa0fffafaa0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice7 : Slice s1NR s1NG (subcubeFast 4 2) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 57) (qGoal := 0xffffffffffaaaa00ffffffffffaaaa00) (by decide +kernel) q32
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice8 : Slice s1NR s1NG (subcubeFast 6 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 57) (qGoal := 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00) (by decide +kernel) q33
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice9 : Slice s1NR s1NG (subcubeFast 33 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xfff0f0c0fff0f0c0fff0f0c0fff0f0c0) (by decide +kernel) q34
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice10 : Slice s1NR s1NG (subcubeFast 34 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 29) (qGoal := 0xfffafa00fffafa00fffafa00fffafa00) (by decide +kernel) q35
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice11 : Slice s1NR s1NG 0x990099009900990099009900990099 5 := mappedSlice (f := identifyRow 8 0 0 1) (R := varsOf 53) (G := 0xfafaaaaafafaa0a0fafaaaaafafaa0a0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q36
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice12 : Slice s1NR s1NG 0xa500a500a500a500a500a500a500a5 5 := mappedSlice (f := identifyRow 8 0 0 2) (R := varsOf 51) (G := 0xeeeeeeeeaaaa8888eeeeeeeeaaaa8888) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q37
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice13 : Slice s1NR s1NG 0xa5a50000a5a50000a5a50000a5a5 5 := mappedSlice (f := identifyRow 16 0 0 2) (R := varsOf 43) (G := 0xeeeeeeeeaa88aa88eeeeeeeeaa88aa88) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q38
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice14 : Slice s1NR s1NG 0xcc330000cc330000cc330000cc33 5 := mappedSlice (f := identifyRow 16 0 1 3) (R := varsOf 39) (G := 0xeeeeeeeec8c8c8c8eeeeeeeec8c8c8c8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q39
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice15 : Slice s1NR s1NG (subcubeFast 9 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 54) (qGoal := 0xfcfcccccf0f0c0c0fcfcccccf0f0c0c0) (by decide +kernel) q40
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice16 : Slice s1NR s1NG (subcubeFast 10 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 53) (qGoal := 0xfafaaaaafafa0000fafaaaaafafa0000) (by decide +kernel) q41
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice17 : Slice s1NR s1NG (subcubeFast 17 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 46) (qGoal := 0xfcccfcccf0c0f0c0fcccfcccf0c0f0c0) (by decide +kernel) q42
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice18 : Slice s1NR s1NG (subcubeFast 18 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 45) (qGoal := 0xfaaafaaafa00fa00faaafaaafa00fa00) (by decide +kernel) q43
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice19 : Slice s1NR s1NG (subcubeFast 24 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 39) (qGoal := 0xeeeeeeeec0c0c0c0eeeeeeeec0c0c0c0) (by decide +kernel) q44
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice20 : Slice s1NR s1NG (subcubeFast 3 32) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) q45
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice21 : Slice s1NR s1NG (subcubeFast 36 2) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 25) (qGoal := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00) (by decide +kernel) q21
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice22 : Slice s1NR s1NG (subcubeFast 38 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 25) (qGoal := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00) (by decide +kernel) q21
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s1NR s1NG p.1 p.2) s1NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s1NR s1NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s1NSlice0) (forall_cons (fun _ h => by cases h; exact s1NSlice1) (forall_cons (fun _ h => by cases h; exact s1NSlice2) (forall_cons (fun _ h => by cases h; exact s1NSlice3) (forall_cons (fun _ h => by cases h; exact s1NSlice4) (forall_cons (fun _ h => by cases h; exact s1NSlice5) (forall_cons (fun _ h => by cases h; exact s1NSlice6) (forall_cons (fun _ h => by cases h; exact s1NSlice7) (forall_cons (fun _ h => by cases h; exact s1NSlice8) (forall_cons (fun _ h => by cases h; exact s1NSlice9) (forall_cons (fun _ h => by cases h; exact s1NSlice10) (forall_cons (fun _ h => by cases h; exact s1NSlice11) (forall_cons (fun _ h => by cases h; exact s1NSlice12) (forall_cons (fun _ h => by cases h; exact s1NSlice13) (forall_cons (fun _ h => by cases h; exact s1NSlice14) (forall_cons (fun _ h => by cases h; exact s1NSlice15) (forall_cons (fun _ h => by cases h; exact s1NSlice16) (forall_cons (fun _ h => by cases h; exact s1NSlice17) (forall_cons (fun _ h => by cases h; exact s1NSlice18) (forall_cons (fun _ h => by cases h; exact s1NSlice19) (forall_cons (fun _ h => by cases h; exact s1NSlice20) (forall_cons (fun _ h => by cases h; exact s1NSlice21) (forall_cons (fun _ h => by cases h; exact s1NSlice22) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))
def s1NEmpty : BT (List (List Nat)) := BT.empty
lemma s1NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG (5 - 1) xs.toFinset) s1NEmpty := trivial
def s1NBlock5_0Specs : List PoolSpec := [(3,[])]
def s1NBlock5_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock5_0Specs
def s1NBlock5_0 : List NodeSpec := [([13,0,1,2,21,5],[],[]),([24,0,1,2,4,5],[],[]),([28,1,2,18,8,5],[],[]),([1,2,11,14,8,5],[0],[]),([1,10,11,12,8,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock5_0Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock5_0Pools s1NAutos s1NEmpty 5 s1NBlock5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock5_0Mem : ∀ ns ∈ s1NBlock5_0, Impossible s1NG 5 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NEmptyOk s1NBlock5_0Ok
def s1NNodes5 : List NodeSpec := s1NBlock5_0
def s1NBucket5 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 5 xs.toFinset) s1NBucket5 := buildBucketsBT_of_mem s1NBlock5_0Mem
def s1NBlock6_0Specs : List PoolSpec := [(3,[(1,0,1),(2,6,5)]),(3,[]),(3,[(1,0,2),(2,10,4)]),(2,[(1,0,3),(2,11,4)]),(4,[(1,0,2)]),(4,[(1,0,2),(2,10,3)]),(0,[]),(8,[])]
def s1NBlock6_0Pools : BT (Option BoundPool) := buildPoolsBT 3 s1NW s1NR s1NSlices s1NBlock6_0Specs
def s1NBlock6_0 : List NodeSpec := [([7,0,1,2,3,4,8],[0],[]),([26,0,1,2,3,4,5],[5],[]),([15,1,2,3,11,4,5],[2],[]),([17,0,1,2,3,32,5],[7],[]),([17,1,2,10,3,4,5],[3],[]),([22,0,1,2,10,3,5],[],[]),([22,0,1,2,3,11,5],[],[]),([22,0,1,2,3,20,5],[4],[]),([22,0,1,2,3,4,5],[],[]),([22,0,1,2,3,5],[],[]),([13,0,1,2,11,4,5],[6],[]),([13,0,1,2,20,4,5],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_0Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_0Pools s1NAutos s1NBucket5 6 s1NBlock6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_0Mem : ∀ ns ∈ s1NBlock6_0, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_0Ok
def s1NBlock6_1Specs : List PoolSpec := [(6,[(1,3,4),(3,0,8)]),(2,[(1,0,3),(2,11,4)]),(12,[]),(4,[(1,0,2),(2,10,3)]),(3,[(1,1,8),(3,2,45)])]
def s1NBlock6_1Pools : BT (Option BoundPool) := buildPoolsBT 3 s1NW s1NR s1NSlices s1NBlock6_1Specs
def s1NBlock6_1 : List NodeSpec := [([13,1,2,10,11,4,5],[],[]),([28,0,1,2,4,8,5],[2],[0]),([28,1,2,3,4,18,5],[],[0]),([34,0,1,2,3,4,5],[],[]),([46,0,1,3,4,8,5],[4],[]),([9,1,6,2,3,4,5],[0],[]),([0,41,1,2,3,4,5],[],[]),([0,1,2,35,3,4,5],[1],[]),([0,1,2,44,3,4,5],[],[]),([0,1,2,3,21,20,5],[],[0,1]),([0,1,2,3,4,25,5],[3],[]),([0,1,2,3,4,33,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_1Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_1Pools s1NAutos s1NBucket5 6 s1NBlock6_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_1Mem : ∀ ns ∈ s1NBlock6_1, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_1Ok
def s1NBlock6_2Specs : List PoolSpec := [(20,[]),(7,[]),(3,[]),(4,[(1,0,2)]),(19,[]),(3,[(1,0,4)]),(15,[])]
def s1NBlock6_2Pools : BT (Option BoundPool) := buildPoolsBT 3 s1NW s1NR s1NSlices s1NBlock6_2Specs
def s1NBlock6_2 : List NodeSpec := [([0,1,2,3,4,39,5],[],[]),([0,1,2,3,4,23,5],[],[0,1]),([0,1,2,11,12,8,5],[6],[0,3]),([0,1,2,20,4,8,5],[3],[1,3]),([1,2,10,3,4,16,5],[1],[]),([1,2,10,11,4,8,5],[],[0]),([1,2,3,11,4,14,5],[2],[0]),([1,2,11,18,8,5],[0,4,5],[0,1]),([1,10,3,11,4,12,5],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_2Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock6_2Pools s1NAutos s1NBucket5 6 s1NBlock6_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock6_2Mem : ∀ ns ∈ s1NBlock6_2, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket5Ok s1NBlock6_2Ok
def s1NNodes6 : List NodeSpec := s1NBlock6_0 ++ s1NBlock6_1 ++ s1NBlock6_2
def s1NBucket6 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 6 xs.toFinset) s1NBucket6 := buildBucketsBT_of_mem (forall_append (forall_append s1NBlock6_0Mem s1NBlock6_1Mem) s1NBlock6_2Mem)
def s1NBlock7_0Specs : List PoolSpec := [(3,[(1,0,1),(2,6,5)]),(20,[]),(7,[]),(4,[(1,0,1),(2,6,5)]),(6,[(1,3,4),(3,0,8)]),(3,[(1,0,1)]),(6,[(1,3,4)]),(21,[]),(2,[(1,0,3),(2,11,4)]),(2,[(1,0,3)]),(3,[(1,0,2)]),(12,[]),(4,[(1,0,2)]),(4,[(1,0,2),(2,10,3)]),(0,[(2,10,3)]),(2,[(2,10,3)]),(19,[]),(0,[]),(4,[(1,0,3)]),(15,[]),(8,[]),(18,[]),(13,[]),(0,[(1,3,4)]),(16,[])]
def s1NBlock7_0Pools : BT (Option BoundPool) := buildPoolsBT 5 s1NW s1NR s1NSlices s1NBlock7_0Specs
def s1NBlock7_0 : List NodeSpec := [([7,0,1,2,3,4],[0,1,2,3],[0]),([17,0,1,2,3,4,5],[1,7,8,18,19],[0]),([40,0,1,2,3,4,5],[7,17,24],[0]),([13,0,1,2,10,3,4,5],[10,11],[0,2]),([13,0,1,2,3,4,5],[1,7,10,13,14,15],[0,1,3]),([28,0,1,2,3,4,5],[1,7,9,19,21],[0]),([38,0,1,2,3,4,5],[7,22,24],[0]),([9,0,1,2,3,4,5],[1,2,4,16,23],[0]),([0,1,6,2,3,4,8,5],[1,2,5,6],[0]),([0,1,2,10,3,20,4,5],[10,11,12],[0]),([0,1,2,10,3,4,8,5],[1,2,10,16],[0,1,2,3]),([0,1,2,30,3,11,4,5],[2,20],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_0Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock7_0Pools s1NAutos s1NBucket6 7 s1NBlock7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_0Mem : ∀ ns ∈ s1NBlock7_0, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket6Ok s1NBlock7_0Ok
def s1NBlock7_1Specs : List PoolSpec := [(20,[]),(7,[]),(21,[]),(3,[]),(3,[(1,0,2)]),(12,[]),(4,[(1,0,2)]),(0,[(1,10,3)]),(2,[(1,10,3)]),(19,[]),(4,[(1,0,3)]),(15,[]),(17,[]),(11,[]),(9,[]),(18,[]),(13,[]),(0,[(1,3,4)]),(0,[(1,11,4)]),(3,[(1,0,5)]),(16,[]),(10,[]),(3,[(1,1,5)]),(3,[(1,0,8)]),(14,[]),(2,[(1,3,4)]),(3,[(1,1,8)])]
def s1NBlock7_1Pools : BT (Option BoundPool) := buildPoolsBT 5 s1NW s1NR s1NSlices s1NBlock7_1Specs
def s1NBlock7_1 : List NodeSpec := [([0,1,2,3,11,31,4,5],[0,13,14],[]),([0,1,2,3,11,20,4,5],[5,10,11],[0]),([0,1,2,3,11,4,32,5],[1,15],[0]),([0,1,2,3,11,4,12,5],[11,16],[0,3]),([0,1,2,3,11,4,16,5],[9,11,12],[]),([0,1,2,3,20,4,5],[0,2,4,5,6,7,8],[0,1,3]),([0,1,2,3,4,8,16,5],[9,11,12,23],[]),([0,1,2,3,4,8,45,5],[9,20,24,25,26],[0]),([0,1,2,3,4,8,5,36],[0,14,19],[]),([0,1,2,3,4,8,5,42],[1,21,22],[]),([0,1,2,3,4,16,5],[0,2,9,11,12,18],[0]),([0,1,2,11,4,8,5],[0,3,9,10,11,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_1Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock7_1Pools s1NAutos s1NBucket6 7 s1NBlock7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_1Mem : ∀ ns ∈ s1NBlock7_1, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket6Ok s1NBlock7_1Ok
def s1NBlock7_2Specs : List PoolSpec := [(20,[]),(21,[]),(2,[(1,0,3)]),(3,[(1,0,2)]),(12,[]),(3,[(1,0,4)]),(4,[(1,0,3)]),(15,[]),(17,[])]
def s1NBlock7_2Pools : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NBlock7_2Specs
def s1NBlock7_2 : List NodeSpec := [([1,2,10,3,11,4,5],[0,1,2,3,4],[0]),([1,2,3,11,4,18,5],[0,5,6,7,8],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_2Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock7_2Pools s1NAutos s1NBucket6 7 s1NBlock7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock7_2Mem : ∀ ns ∈ s1NBlock7_2, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NBucket6Ok s1NBlock7_2Ok
def s1NNodes7 : List NodeSpec := s1NBlock7_0 ++ s1NBlock7_1 ++ s1NBlock7_2
def s1NBucket7 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 7 xs.toFinset) s1NBucket7 := buildBucketsBT_of_mem (forall_append (forall_append s1NBlock7_0Mem s1NBlock7_1Mem) s1NBlock7_2Mem)
def s1NBlock8_0Specs : List PoolSpec := [(20,[]),(7,[]),(3,[(1,0,1)]),(6,[(1,3,4)]),(21,[]),(5,[]),(4,[(1,0,1)]),(3,[]),(2,[(1,0,3)]),(3,[(1,0,2)]),(4,[(1,0,2)]),(19,[]),(0,[]),(2,[]),(4,[(1,0,3)]),(15,[]),(9,[]),(0,[(1,3,4)]),(3,[(1,0,5)]),(4,[(1,0,5)]),(1,[]),(4,[(1,1,3)]),(3,[(1,1,5)]),(22,[]),(4,[(1,1,5)]),(2,[(1,3,4)]),(4,[]),(1,[(1,3,4)])]
def s1NBlock8_0Pools : BT (Option BoundPool) := buildPoolsBT 5 s1NW s1NR s1NSlices s1NBlock8_0Specs
def s1NBlock8_0 : List NodeSpec := [([0,1,6,2,3,4,5],[0,2,4,5,6],[0]),([0,1,2,10,3,4,5],[0,4,9,10,12,13],[0,1,2,3]),([0,1,2,3,11,4,5],[0,1,7,8,12,14,15,16],[0]),([0,1,2,3,37,4,5],[0,4,7,20,21],[0,1]),([0,1,2,3,4,8,5],[0,1,3,7,11,17,25,26,27],[0,1,2,3]),([0,1,2,3,4,5,36],[0,4,16,18,19],[0,2,3]),([0,1,2,3,4,5,42],[0,22,23,24],[0])]
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
def s1NBlock9_0Specs : List PoolSpec := [(3,[]),(0,[]),(2,[]),(1,[]),(4,[]),(6,[])]
def s1NBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 3 s1NW s1NR s1NSlices s1NBlock9_0Specs
def s1NBlock9_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5],[0,1,2,3])]
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
lemma s1NBound : Lower s1NR s1NG 10 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) s1NBucket9Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q25 : Lower (varsOf 63) 0xfffefffafefeeca0fffefffafefeeca0 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (0, 1)]) (roots2 := s1NR) (T2 := s1NG) _ s1NBound
  decide +kernel
lemma lb120 : Lower lb677 lb665 4 := carry_of lb728 lb568
lemma lb125 : carryOK [(3,4),(0,2),(0,1)] lb355 lb346 lb548 lb544 = true := by decide +kernel
lemma lb122 : Lower lb355 lb346 4 := carry_of lb125 lb568
lemma lb127 : carryOK [(3,4),(0,1)] lb519 lb515 lb548 lb544 = true := by decide +kernel
lemma lb126 : Lower lb519 lb515 4 := carry_of lb127 lb568
lemma lb129 : carryOK [(3,4)] lb766 lb762 lb548 lb544 = true := by decide +kernel
lemma lb128 : Lower lb766 lb762 4 := carry_of lb129 lb568
def lb86 : Nat := 0xe8e88080e8e88080e8e88080e8e88080
def lb131 : List Nat := [7,7,7,19,19,19,21,21,21,22,22,22,7,7,7,19,19,19,21,21,21,22,22,22]
def lb130 : List Nat := [6,5,3,18,17,3,20,17,5,20,18,6,17,18,20,5,6,20,3,6,18,3,5,17]
def lb95 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ff1ff,0xe491b6),(0xcccccccccccccccccccccccccccccccc,0xe3fe3f,0x3d2c2d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfc7fc7,0x4bcb43),(0xffff0000ffff0000ffff0000ffff0000,0xff8ff8,0x9276d8)]
def lb91 : Array Decor := buildWires lb95 lb514
def lb93 : Array (List (Nat × Nat)) := #[[],[(2,4)],[(0,1)],[(2,4),(0,1)],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def lb140 : List (Nat × Nat) := [(subcube 0 4,4),(subcube 0 1,4),(subcube 0 2,4),(subcube 0 16,4)]
def lb141 : Array (Nat × Nat) := lb140.toArray
def lb88 : Array (Option BoundPool) := buildPools lb91 lb356 lb141 lb499
lemma lb119 : goodPairs lb86 lb131 lb130 := goodPairs_of (by decide +kernel)
lemma lb96 : ∀ x ∈ lb95, faithful lb131 lb130 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb92 : ∀ x ∈ lb91.toList, faithful lb131 lb130 x ∧ x.1 < 2^128 := buildWires_faithful lb96
lemma lb94 : ∀ sw ∈ lb93.toList, swapsValid sw = true ∧ permWord sw lb86 = lb86 := autos_of (by decide +kernel)
lemma lb133 : sliceDirectCheck 0 4 0 lb356 lb86 lb355 lb346 = true := by decide +kernel
lemma lb132 : Slice lb356 lb86 (subcube 0 4) 4 := slice_direct lb133 lb122
lemma lb135 : sliceDirectCheck 0 1 0 lb356 lb86 lb766 lb762 = true := by decide +kernel
lemma lb134 : Slice lb356 lb86 (subcube 0 1) 4 := slice_direct lb135 lb128
lemma lb137 : sliceDirectCheck 0 2 0 lb356 lb86 lb519 lb515 = true := by decide +kernel
lemma lb136 : Slice lb356 lb86 (subcube 0 2) 4 := slice_direct lb137 lb126
lemma lb139 : sliceDirectCheck 0 16 0 lb356 lb86 lb677 lb665 = true := by decide +kernel
lemma lb138 : Slice lb356 lb86 (subcube 0 16) 4 := slice_direct lb139 lb120
set_option maxRecDepth 200000 in
lemma lb142 : ∀ i (hi : i < lb141.size), Slice lb356 lb86 lb141[i].1 lb141[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb356 lb86 p.1 p.2) (forall_cons lb132 (forall_cons lb134 (forall_cons lb136 (forall_cons lb138 (fun _ h => (List.not_mem_nil h).elim)))))
lemma lb89 : ∀ i (hi : i < lb88.size), ∀ c, lb88[i] = some c → ValidPool lb356 lb86 c := buildPools_sound lb142
lemma lb109 : ∀ i (hi : i < lb449.size), ∀ xs ∈ lb449[i], Impossible lb86 (0 - 1) xs.toFinset := by intro i hi; simp [lb449] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb110 : checkNodes lb91 lb86 lb475 lb88 lb93 lb449 0 lb492 = true := by decide +kernel
def lb97 : Array (List (List Nat)) := buildBuckets 1 lb91 lb492
lemma lb98 : ∀ i (hi : i < lb97.size), ∀ xs ∈ lb97[i], Impossible lb86 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb119 lb92 lb89 lb94 lb109 lb110
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb111 : checkNodes lb91 lb86 lb475 lb88 lb93 lb97 1 lb492 = true := by decide +kernel
lemma lb99 : ∀ i (hi : i < lb97.size), ∀ xs ∈ lb97[i], Impossible lb86 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb119 lb92 lb89 lb94 lb98 lb111
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb112 : checkNodes lb91 lb86 lb475 lb88 lb93 lb97 2 lb492 = true := by decide +kernel
lemma lb100 : ∀ i (hi : i < lb97.size), ∀ xs ∈ lb97[i], Impossible lb86 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb119 lb92 lb89 lb94 lb99 lb112
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb113 : checkNodes lb91 lb86 lb475 lb88 lb93 lb97 3 lb493 = true := by decide +kernel
def lb101 : Array (List (List Nat)) := buildBuckets 1 lb91 lb493
lemma lb102 : ∀ i (hi : i < lb101.size), ∀ xs ∈ lb101[i], Impossible lb86 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb119 lb92 lb89 lb94 lb100 lb113
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb114 : checkNodes lb91 lb86 lb475 lb88 lb93 lb101 4 lb494 = true := by decide +kernel
def lb103 : Array (List (List Nat)) := buildBuckets 2 lb91 lb494
lemma lb104 : ∀ i (hi : i < lb103.size), ∀ xs ∈ lb103[i], Impossible lb86 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb119 lb92 lb89 lb94 lb102 lb114
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb115 : checkNodes lb91 lb86 lb475 lb88 lb93 lb103 5 lb495 = true := by decide +kernel
def lb105 : Array (List (List Nat)) := buildBuckets 1 lb91 lb495
lemma lb106 : ∀ i (hi : i < lb105.size), ∀ xs ∈ lb105[i], Impossible lb86 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb119 lb92 lb89 lb94 lb104 lb115
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb116 : checkNodes lb91 lb86 lb475 lb88 lb93 lb105 6 lb496 = true := by decide +kernel
def lb107 : Array (List (List Nat)) := buildBuckets 1 lb91 lb496
lemma lb108 : ∀ i (hi : i < lb107.size), ∀ xs ∈ lb107[i], Impossible lb86 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb119 lb92 lb89 lb94 lb106 lb116
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb118 : forestRootCheck lb356 lb86 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 4,19,3)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb117 : bucketContains lb107 lb356 = true := by decide +kernel
lemma lb121 : Lower lb356 lb86 7 := lower_of_forest lb118 lb108 lb117
def lb87 : Nat := 0xe8e88080e8e80000e8e88080e8e80000
def lb90 : List Nat := varsOf 55
lemma lb124 : liftCheck 0 32 lb90 lb87 lb356 lb86 [(VAR 5,39,7)] = true := by decide +kernel
lemma lb123 : Lower lb90 lb87 8 := lift_of lb124 lb121
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q47d : Lower (varsOf 61) 0xfaa0a000aaa0a000faa0a000aaa0a000 8 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := lb90) (T2 := lb87) _ lb123
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q47 : Lower (varsOf 61) 0xfffafaaafffafaa0fffafaaafffafaa0 8 := dualLower (by decide +kernel) (by decide +kernel) q47d
def lb152 : BT Decor := buildWiresBT 2 lb439 lb82
set_option maxRecDepth 500000 in
lemma lb153 : btAll (fun x => faithful lb497 lb490 x ∧ x.1 < 2^128) lb152 := buildWiresBT_faithful lb440
set_option maxRecDepth 500000 in
lemma lb157 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb418 = lb418) lb363 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb231 : btAll (fun o => ∀ p, o = some p → Slice lb427 lb418 p.1 p.2) lb79 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb427 lb418 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb168 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb418 (0 - 1) xs.toFinset) lb67 := trivial
def lb147 : BT (Option BoundPool) := buildPoolsSubBT 1 lb152 lb427 lb79 lb404 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb183 : checkNodesBT lb152 lb418 lb378 lb147 lb363 lb67 0 lb492 = true := by decide +kernel
def lb162 : BT (List (List Nat)) := buildBucketsBT lb152 lb492
set_option maxRecDepth 500000 in
lemma lb163 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb418 0 xs.toFinset) lb162 :=
  buildBucketsBT_sound (by decide) lb480 lb153 (buildPoolsSubBT_sound lb231) lb157 lb168 lb183
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb184 : checkNodesBT lb152 lb418 lb378 lb147 lb363 lb162 1 lb492 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb164 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb418 1 xs.toFinset) lb162 :=
  buildBucketsBT_sound (by decide) lb480 lb153 (buildPoolsSubBT_sound lb231) lb157 lb163 lb184
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb185 : checkNodesBT lb152 lb418 lb378 lb147 lb363 lb162 2 lb492 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb165 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb418 2 xs.toFinset) lb162 :=
  buildBucketsBT_sound (by decide) lb480 lb153 (buildPoolsSubBT_sound lb231) lb157 lb164 lb185
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb186 : checkNodesBT lb152 lb418 lb378 lb147 lb363 lb162 3 lb400 = true := by decide +kernel
def lb166 : BT (List (List Nat)) := buildBucketsBT lb152 lb400
set_option maxRecDepth 500000 in
lemma lb167 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb418 3 xs.toFinset) lb166 :=
  buildBucketsBT_sound (by decide) lb480 lb153 (buildPoolsSubBT_sound lb231) lb157 lb165 lb186
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb196 : forestRootCheck lb427 lb418 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb195 : bucketContainsBT lb166 lb427 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb200 : Lower lb427 lb418 4 := lower_of_forestBT lb196 lb167 lb195
lemma lb209 : carryOK [(1,2),(1,5),(2,4),(1,3)] lb548 lb544 lb427 lb418 = true := by decide +kernel
lemma lb208 : Lower lb548 lb544 4 := carry_of lb209 lb200
def lb146 : Nat := 0xfff0ff00ff000000fff0ff00ff000000
lemma lb211 : liftCheck 0 4 lb11 lb146 lb427 lb418 [(VAR 2,52,48)] = true := by decide +kernel
lemma lb210 : Lower lb11 lb146 5 := lift_of lb211 lb200
lemma lb202 : carryOK [(1,2),(2,5),(1,4)] lb77 lb604 lb11 lb146 = true := by decide +kernel
lemma lb201 : Lower lb77 lb604 5 := carry_of lb202 lb210
def lb143 : Nat := 0xfcc0fcc0fc00fc00fcc0fcc0fc00fc00
lemma lb204 : carryOK [(2,5),(1,4)] lb2 lb143 lb11 lb146 = true := by decide +kernel
lemma lb203 : Lower lb2 lb143 5 := carry_of lb204 lb210
def lb144 : Nat := 0xffccff00ff000000ffccff00ff000000
lemma lb206 : carryOK [(1,2)] lb8 lb144 lb11 lb146 = true := by decide +kernel
lemma lb205 : Lower lb8 lb144 5 := carry_of lb206 lb210
def lb145 : Nat := 0xfcc0fc00fc000000fcc0fc00fc000000
def lb217 : List Nat := [26,26,26,28,28,28,30,30,42,42,42,44,44,44,46,46,54,54,54,54,58,58,60,60,26,26,26,26,26,26,28,28,28,28,28,28,42,42,42,42,42,42,44,44,44,44,44,44,54,54]
def lb212 : List Nat := [24,18,10,24,20,12,22,14,40,34,10,40,36,12,38,14,52,50,38,22,56,50,56,52,14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56,14,56]
def lb160 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x303f03f3fc7c7,0x13cf3cf2ec6c6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3fc0fc0cff8f8,0x15d75d78df0f0),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffffff0ffff,0x386186150adad),(0xffff0000ffff0000ffff0000ffff0000,0x3000fffff00ff,0x2ebaebafb005b),(0xffffffff00000000ffffffff00000000,0x3fff000ffff00,0x2f3cf3cf75b00)]
def lb234 : List (Nat × Nat × Nat) := [(0,0,3),(2,0,2),(0,0,2),(0,6,3),(3,5,2),(1,5,2),(3,7,3),(0,7,3),(3,6,3),(3,7,1),(0,1,10),(3,13,4),(3,12,1)]
def lb154 : BT Decor := buildWiresBT 5 lb160 lb234
def lb156 : List (List (Nat × Nat)) := [[],[(2,5),(1,4)],[(4,5)],[(1,2)],[(4,5),(1,2)],[(1,2),(2,5),(1,4)]]
def lb158 : BT (List (Nat × Nat)) := btOfList 3 lb156
def lb230 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 6,4),some (subcubeFast 0 4,5),some (subcubeFast 0 2,5),some (subcubeFast 0 32,5),some (subcubeFast 0 48,4)]
def lb232 : BT (Option (Nat × Nat)) := btOfList 3 lb230
lemma lb199 : goodPairs lb145 lb217 lb212 := goodPairs_of (by decide +kernel)
lemma lb161 : ∀ x ∈ lb160, faithful lb217 lb212 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb155 : btAll (fun x => faithful lb217 lb212 x ∧ x.1 < 2^128) lb154 := buildWiresBT_faithful lb161
set_option maxRecDepth 500000 in
lemma lb159 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb145 = lb145) lb158 := btAll_ofList (autos_of (by decide +kernel))
lemma lb219 : sliceDirectCheck 0 16 0 lb41 lb145 lb2 lb143 = true := by decide +kernel
lemma lb218 : Slice lb41 lb145 (subcubeFast 0 16) 5 := slice_fast_direct lb219 lb203
lemma lb221 : sliceDirectCheck 0 6 0 lb41 lb145 lb427 lb418 = true := by decide +kernel
lemma lb220 : Slice lb41 lb145 (subcubeFast 0 6) 4 := slice_fast_direct lb221 lb200
lemma lb223 : sliceDirectCheck 0 4 0 lb41 lb145 lb8 lb144 = true := by decide +kernel
lemma lb222 : Slice lb41 lb145 (subcubeFast 0 4) 5 := slice_fast_direct lb223 lb205
lemma lb225 : sliceDirectCheck 0 2 0 lb41 lb145 lb11 lb146 = true := by decide +kernel
lemma lb224 : Slice lb41 lb145 (subcubeFast 0 2) 5 := slice_fast_direct lb225 lb210
lemma lb227 : sliceDirectCheck 0 32 0 lb41 lb145 lb77 lb604 = true := by decide +kernel
lemma lb226 : Slice lb41 lb145 (subcubeFast 0 32) 5 := slice_fast_direct lb227 lb201
lemma lb229 : sliceDirectCheck 0 48 0 lb41 lb145 lb548 lb544 = true := by decide +kernel
lemma lb228 : Slice lb41 lb145 (subcubeFast 0 48) 4 := slice_fast_direct lb229 lb208
set_option maxRecDepth 500000 in
lemma lb233 : btAll (fun o => ∀ p, o = some p → Slice lb41 lb145 p.1 p.2) lb232 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb41 lb145 p.1 p.2) (forall_cons (fun _ h => by cases h; exact lb218) (forall_cons (fun _ h => by cases h; exact lb220) (forall_cons (fun _ h => by cases h; exact lb222) (forall_cons (fun _ h => by cases h; exact lb224) (forall_cons (fun _ h => by cases h; exact lb226) (forall_cons (fun _ h => by cases h; exact lb228) (fun _ h => (List.not_mem_nil h).elim)))))))
lemma lb182 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb145 (0 - 1) xs.toFinset) lb67 := trivial
def lb148 : BT (Option BoundPool) := buildPoolsSubBT 3 lb154 lb41 lb232 lb743 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb187 : checkNodesBT lb154 lb145 lb634 lb148 lb158 lb67 0 lb492 = true := by decide +kernel
def lb169 : BT (List (List Nat)) := buildBucketsBT lb154 lb492
set_option maxRecDepth 500000 in
lemma lb170 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb145 0 xs.toFinset) lb169 :=
  buildBucketsBT_sound (by decide) lb199 lb155 (buildPoolsSubBT_sound lb233) lb159 lb182 lb187
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb188 : checkNodesBT lb154 lb145 lb634 lb148 lb158 lb169 1 lb492 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb171 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb145 1 xs.toFinset) lb169 :=
  buildBucketsBT_sound (by decide) lb199 lb155 (buildPoolsSubBT_sound lb233) lb159 lb170 lb188
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb189 : checkNodesBT lb154 lb145 lb634 lb148 lb158 lb169 2 lb492 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb172 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb145 2 xs.toFinset) lb169 :=
  buildBucketsBT_sound (by decide) lb199 lb155 (buildPoolsSubBT_sound lb233) lb159 lb171 lb189
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb190 : checkNodesBT lb154 lb145 lb634 lb148 lb158 lb169 3 lb492 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb173 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb145 3 xs.toFinset) lb169 :=
  buildBucketsBT_sound (by decide) lb199 lb155 (buildPoolsSubBT_sound lb233) lb159 lb172 lb190
def lb213 : List NodeSpec := [([0,15,2,3,4],[],[]),([16,0,1,2,3],[],[]),([17,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb191 : checkNodesBT lb154 lb145 lb634 lb148 lb158 lb169 4 lb213 = true := by decide +kernel
def lb174 : BT (List (List Nat)) := buildBucketsBT lb154 lb213
set_option maxRecDepth 500000 in
lemma lb175 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb145 4 xs.toFinset) lb174 :=
  buildBucketsBT_sound (by decide) lb199 lb155 (buildPoolsSubBT_sound lb233) lb159 lb173 lb191
def lb214 : List NodeSpec := [([8,0,1,2,3,4],[],[]),([7,5,1,2,3,4],[0,1],[]),([9,0,1,2,3,4],[],[]),([0,1,2,10,3,4],[0,2,3,4],[0,1]),([11,0,1,2,3,4],[],[]),([12,0,1,2,3,4],[2,4],[0,1]),([0,1,2,13,3,4],[4],[0]),([14,0,2,3,4],[],[]),([14,7,0,2,3,4],[2],[]),([6,7,1,2,3,4],[1],[])]
def lb149 : BT (Option BoundPool) := buildPoolsSubBT 3 lb154 lb41 lb232 lb743 [0,1,2,3,4]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb192 : checkNodesBT lb154 lb145 lb634 lb149 lb158 lb174 5 lb214 = true := by decide +kernel
def lb176 : BT (List (List Nat)) := buildBucketsBT lb154 lb214
set_option maxRecDepth 500000 in
lemma lb177 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb145 5 xs.toFinset) lb176 :=
  buildBucketsBT_sound (by decide) lb199 lb155 (buildPoolsSubBT_sound lb233) lb159 lb175 lb192
def lb215 : List NodeSpec := [([5,0,1,2,3,4],[1,5],[0,1]),([6,0,1,2,3,4],[1,0,4],[0,2]),([7,0,1,2,3,4],[1,0,4],[0,2])]
def lb150 : BT (Option BoundPool) := buildPoolsSubBT 3 lb154 lb41 lb232 lb743 [0,1,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb193 : checkNodesBT lb154 lb145 lb634 lb150 lb158 lb176 6 lb215 = true := by decide +kernel
def lb178 : BT (List (List Nat)) := buildBucketsBT lb154 lb215
set_option maxRecDepth 500000 in
lemma lb179 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb145 6 xs.toFinset) lb178 :=
  buildBucketsBT_sound (by decide) lb199 lb155 (buildPoolsSubBT_sound lb233) lb159 lb177 lb193
def lb216 : List NodeSpec := [([0,1,2,3,4],[1,5],[0,2,3,4,1,5])]
def lb151 : BT (Option BoundPool) := buildPoolsSubBT 3 lb154 lb41 lb232 lb743 [1,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb194 : checkNodesBT lb154 lb145 lb634 lb151 lb158 lb178 7 lb216 = true := by decide +kernel
def lb180 : BT (List (List Nat)) := buildBucketsBT lb154 lb216
set_option maxRecDepth 500000 in
lemma lb181 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb145 7 xs.toFinset) lb180 :=
  buildBucketsBT_sound (by decide) lb199 lb155 (buildPoolsSubBT_sound lb233) lb159 lb179 lb194
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb198 : forestRootCheck lb41 lb145 [(VAR 1,26,24),(VAR 2,28,24),(VAR 3,26,18),(VAR 4,26,10),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb197 : bucketContainsBT lb180 lb41 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb207 : Lower lb41 lb145 8 := lower_of_forestBT lb198 lb181 lb197
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q48d : Lower (varsOf 59) 0xeeaaaa0088888800eeaaaa0088888800 8 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (0, 1)]) (roots2 := lb41) (T2 := lb145) _ lb207
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q48 : Lower (varsOf 59) 0xffeeeeeeffaaaa88ffeeeeeeffaaaa88 8 := dualLower (by decide +kernel) (by decide +kernel) q48d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q49 : Lower (varsOf 55) 0xfefeeeeefafae8e8fefeeeeefafae8e8 7 := by
  apply carry_of (swaps := [(4, 5), (3, 4)]) (roots2 := lb354) (T2 := lb345) _ lb391
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q50 : Lower (varsOf 47) 0xfeeefeeefae8fae8feeefeeefae8fae8 7 := by
  apply carry_of (swaps := [(4, 5)]) (roots2 := lb354) (T2 := lb345) _ lb391
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q51d : Lower (varsOf 30) 0xccc0c000ccc0c000ccc0c000ccc0c000 5 := by
  apply carry_of (swaps := [(2, 3), (1, 2)]) (roots2 := lb77) (T2 := lb763) _ lb787
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q51 : Lower (varsOf 30) 0xfffcfcccfffcfcccfffcfcccfffcfccc 5 := dualLower (by decide +kernel) (by decide +kernel) q51d
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
lemma s2NSlice0 : Slice s2NR s2NG (subcubeFast 2 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafaaafffafaa0fffafaaafffafaa0) (by decide +kernel) q47
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice1 : Slice s2NR s2NG (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeeeeeffaaaa88ffeeeeeeffaaaa88) (by decide +kernel) q48
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice2 : Slice s2NR s2NG (subcubeFast 1 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffcfcccfff0f0c0fffcfcccfff0f0c0) (by decide +kernel) q26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice3 : Slice s2NR s2NG (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeeeeefafae8e8fefeeeeefafae8e8) (by decide +kernel) q49
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice4 : Slice s2NR s2NG (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfeeefeeefae8fae8feeefeeefae8fae8) (by decide +kernel) q50
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice5 : Slice s2NR s2NG (subcubeFast 34 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 29) (qGoal := 0xfffafaa0fffafaa0fffafaa0fffafaa0) (by decide +kernel) q6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice6 : Slice s2NR s2NG (subcubeFast 1 32) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xfffcfcccfffcfcccfffcfcccfffcfccc) (by decide +kernel) q51
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice7 : Slice s2NR s2NG (subcubeFast 9 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 54) (qGoal := 0xfcfcccccf0f0c0c0fcfcccccf0f0c0c0) (by decide +kernel) q40
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice8 : Slice s2NR s2NG (subcubeFast 17 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 46) (qGoal := 0xfcccfcccf0c0f0c0fcccfcccf0c0f0c0) (by decide +kernel) q42
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice9 : Slice s2NR s2NG (subcubeFast 28 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) q19
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
def s2NBlock7_0Specs : List PoolSpec := [(9,[]),(6,[]),(0,[(1,0,3),(1,0,4)]),(7,[]),(8,[]),(2,[(1,3,4)]),(0,[(1,0,3),(1,3,4)]),(5,[(1,0,3),(1,6,4)]),(5,[(1,0,3),(2,6,4)])]
def s2NBlock7_0Pools : BT (Option BoundPool) := buildPoolsBT 4 s2NW s2NR s2NSlices s2NBlock7_0Specs
def s2NBlock7_0 : List NodeSpec := [([10,0,1,2,3,4,5],[0,3,8],[]),([0,1,2,3,6,4,9,5],[0,3,4],[]),([0,1,2,3,4,9,5],[0,3,4,7],[]),([0,1,2,6,4,8,5],[0,1,3,5,6],[0]),([1,2,3,6,4,7,5],[0,1,2,3,4],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock7_0Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock7_0Pools s2NAutos s2NBucket6 7 s2NBlock7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock7_0Mem : ∀ ns ∈ s2NBlock7_0, Impossible s2NG 7 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket6Ok s2NBlock7_0Ok
def s2NNodes7 : List NodeSpec := s2NBlock7_0
def s2NBucket7 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 7 xs.toFinset) s2NBucket7 := buildBucketsBT_of_mem s2NBlock7_0Mem
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
lemma q46 : Lower (varsOf 95) 0xfffffffefffffffefefeeca0fefeeca0 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (0, 1)]) (roots2 := s2NR) (T2 := s2NG) _ s2NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q52 : Lower (varsOf 111) 0xfffffffffffefffefffafffaeca0eca0 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (1, 2)]) (roots2 := s2NR) (T2 := s2NG) _ s2NBound
  decide +kernel
lemma lb299 : Lower lb548 lb544 4 := carry_of lb209 lb482
def lb242 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def lb247 : List Nat := varsOf 38
lemma lb301 : carryOK [(2,4),(1,3)] lb247 lb242 lb427 lb418 = true := by decide +kernel
lemma lb300 : Lower lb247 lb242 4 := carry_of lb301 lb482
def lb235 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def lb245 : List Nat := varsOf 42
lemma lb287 : carryOK [(2,4),(1,2),(1,3)] lb245 lb235 lb427 lb418 = true := by decide +kernel
lemma lb286 : Lower lb245 lb235 4 := carry_of lb287 lb482
def lb236 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def lb246 : List Nat := varsOf 50
lemma lb289 : carryOK [(1,2),(1,3)] lb246 lb236 lb427 lb418 = true := by decide +kernel
lemma lb288 : Lower lb246 lb236 4 := carry_of lb289 lb482
def lb237 : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000
lemma lb291 : carryOK [(1,5),(1,4),(1,3),(1,2)] lb77 lb237 lb11 lb422 = true := by decide +kernel
lemma lb290 : Lower lb77 lb237 7 := carry_of lb291 lb489
def lb238 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
lemma lb293 : carryOK [(1,4),(1,3),(1,2)] lb2 lb238 lb11 lb422 = true := by decide +kernel
lemma lb292 : Lower lb2 lb238 7 := carry_of lb293 lb489
def lb239 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
lemma lb295 : carryOK [(1,3),(1,2)] lb5 lb239 lb11 lb422 = true := by decide +kernel
lemma lb294 : Lower lb5 lb239 7 := carry_of lb295 lb489
def lb240 : Nat := 0xffcccc00cc000000ffcccc00cc000000
lemma lb297 : carryOK [(1,2)] lb8 lb240 lb11 lb422 = true := by decide +kernel
lemma lb296 : Lower lb8 lb240 7 := carry_of lb297 lb489
def lb241 : Nat := 0xfcc0c000c0000000fcc0c000c0000000
def lb310 : List Nat := [30,30,30,30,46,46,46,46,54,54,54,54,58,58,58,58,60,60,60,60,30,30,30,30,30,30,46,46,46,46,46,46,54,54,54,54,54,54,58,58,58,58,58,58,60,60,60,60,60,60]
def lb302 : List Nat := [28,26,22,14,44,42,38,14,52,50,38,22,56,50,42,26,56,52,44,28,38,42,44,50,52,56,22,26,28,50,52,56,14,26,28,42,44,56,14,22,28,38,44,52,14,22,26,38,42,50]
def lb252 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xffffff0ffff,0x3f2cb2cb0eeee),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3f03fffff0fff,0xbfd5555e0ddd),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffc0fffff0ff,0x1557f9a6dd0bb),(0xffff0000ffff0000ffff0000ffff0000,0x3ffff03ffff0f,0x269a6ff8bbb07),(0xffffffff00000000ffffffff00000000,0x3fffffc0ffff0,0x38e38e3f77770)]
def lb341 : List (Nat × Nat × Nat) := [(0,0,1),(0,2,3),(0,0,2),(3,5,2),(0,5,2),(0,1,3),(0,3,4),(3,8,3),(2,5,6),(0,9,3),(0,1,2),(0,0,3),(3,9,3),(0,5,3),(3,13,0),(0,1,4),(0,2,4),(3,12,4),(3,16,4),(3,14,4),(0,0,4),(3,14,0),(0,12,4),(1,14,4),(2,2,11),(0,17,4),(0,14,4),(0,16,4),(3,17,4),(3,14,1),(3,31,0)]
def lb248 : Array Decor := buildWires lb252 lb341
def lb250 : Array (List (Nat × Nat)) := #[[],[(1,2)],[(1,3),(1,2)],[(1,2),(2,4),(1,5)],[(4,5)],[(1,5),(1,4),(1,3),(1,2)],[(3,5),(3,4)],[(3,5),(2,3),(2,4)],[(3,5),(1,2),(1,4)],[(2,3),(1,3),(2,5),(1,4)],[(2,3),(3,5),(2,4)],[(3,4),(3,5)],[(3,4)],[(3,4),(2,3),(2,5)],[(2,3),(2,4)],[(3,4),(2,3),(1,2),(1,5)],[(2,3),(1,2),(1,4)],[(3,5),(2,3),(1,2),(1,4)],[(3,5),(2,4)],[(2,5),(2,4),(2,3)],[(2,4)],[(2,3),(3,5),(1,2),(1,4)],[(2,3)],[(1,4),(1,3),(1,2)],[(2,4),(2,3)],[(4,5),(1,2),(1,3)],[(2,5),(1,4)],[(4,5),(1,2)],[(4,5),(2,3)],[(1,2),(1,4)],[(3,4),(1,2)],[(4,5),(1,3),(1,2)],[(2,5),(2,4)],[(3,5),(3,4),(1,2)],[(1,3),(1,4),(1,2)],[(3,5),(1,3),(1,4),(1,2)],[(2,4),(1,3)],[(1,2),(2,3),(1,4)],[(1,2),(1,3)],[(2,4),(1,2),(1,3)],[(2,3),(2,5),(1,4)],[(2,5),(2,4),(1,2),(1,3)],[(2,5),(2,4),(1,3)],[(1,2),(1,5),(2,4),(1,3)]]
def lb338 : List (Nat × Nat) := [(subcube 0 12,4),(subcube 0 6,4),(subcube 0 32,7),(subcube 0 48,4),(subcube 0 2,7),(subcube 0 24,4),(subcube 0 20,4),(subcube 0 10,4),(subcube 0 8,7),(subcube 0 16,7),(subcube 0 4,7),(subcube 0 34,4),(subcube 0 18,4)]
def lb339 : Array (Nat × Nat) := lb338.toArray
def lb311 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(2,[(0,0,1),(0,0,2),(0,1,2)]),(8,[(0,0,1),(0,0,3),(0,1,3)]),(9,[]),(4,[(0,5,2),(0,9,3),(3,14,4)]),(2,[(0,0,1),(0,5,2),(3,9,3)]),(4,[(0,5,2),(0,5,3),(0,2,3)]),(10,[]),(9,[(0,0,1),(0,0,2)]),(8,[(0,0,1),(0,1,3)]),(2,[(0,0,1),(3,5,2)]),(8,[(0,0,1),(3,8,3)]),(9,[(0,0,1),(3,5,2)]),(4,[(0,2,3),(2,5,6)]),(8,[]),(9,[(0,0,1),(0,5,2)]),(4,[(0,5,2),(0,2,3)]),(2,[(0,0,1),(0,5,2)]),(4,[(0,1,2)]),(9,[(0,0,1),(0,0,2),(0,1,2)]),(10,[(0,5,2),(0,0,3)]),(8,[(0,0,1),(0,0,3)]),(11,[]),(4,[(0,5,2),(0,9,3)]),(4,[(0,5,2),(3,9,3)]),(10,[(0,5,2),(3,9,3)]),(8,[(0,0,1),(3,9,3)]),(2,[(0,0,1),(0,0,2)]),(10,[(0,5,2),(0,9,3)]),(8,[(0,0,1),(0,9,3)]),(4,[(0,5,2),(0,5,3)]),(12,[]),(8,[(0,0,1)]),(9,[(0,0,1)]),(4,[(0,2,3)]),(10,[(0,2,3)]),(10,[(0,0,2)]),(4,[(0,5,2)]),(10,[(0,5,2)]),(2,[(0,0,1)])]
def lb243 : Array (Option BoundPool) := buildPools lb248 lb41 lb339 lb311
lemma lb285 : goodPairs lb241 lb310 lb302 := goodPairs_of (by decide +kernel)
lemma lb253 : ∀ x ∈ lb252, faithful lb310 lb302 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb249 : ∀ x ∈ lb248.toList, faithful lb310 lb302 x ∧ x.1 < 2^128 := buildWires_faithful lb253
lemma lb251 : ∀ sw ∈ lb250.toList, swapsValid sw = true ∧ permWord sw lb241 = lb241 := autos_of (by decide +kernel)
lemma lb313 : sliceDirectCheck 0 12 0 lb41 lb241 lb246 lb236 = true := by decide +kernel
lemma lb312 : Slice lb41 lb241 (subcube 0 12) 4 := slice_direct lb313 lb288
lemma lb321 : sliceDirectCheck 0 6 0 lb41 lb241 lb427 lb418 = true := by decide +kernel
lemma lb314 : Slice lb41 lb241 (subcube 0 6) 4 := slice_direct lb321 lb482
lemma lb323 : sliceDirectCheck 0 32 0 lb41 lb241 lb77 lb237 = true := by decide +kernel
lemma lb322 : Slice lb41 lb241 (subcube 0 32) 7 := slice_direct lb323 lb290
lemma lb325 : sliceDirectCheck 0 48 0 lb41 lb241 lb548 lb544 = true := by decide +kernel
lemma lb324 : Slice lb41 lb241 (subcube 0 48) 4 := slice_direct lb325 lb299
lemma lb327 : sliceDirectCheck 0 2 0 lb41 lb241 lb11 lb422 = true := by decide +kernel
lemma lb326 : Slice lb41 lb241 (subcube 0 2) 7 := slice_direct lb327 lb489
lemma lb329 : sliceDirectCheck 0 24 0 lb41 lb241 lb247 lb242 = true := by decide +kernel
lemma lb328 : Slice lb41 lb241 (subcube 0 24) 4 := slice_direct lb329 lb300
lemma lb331 : sliceDirectCheck 0 20 0 lb41 lb241 lb245 lb235 = true := by decide +kernel
lemma lb330 : Slice lb41 lb241 (subcube 0 20) 4 := slice_direct lb331 lb286
lemma lb333 : sliceDirectCheck 0 10 0 lb41 lb241 lb430 lb421 = true := by decide +kernel
lemma lb332 : Slice lb41 lb241 (subcube 0 10) 4 := slice_direct lb333 lb487
lemma lb335 : sliceDirectCheck 0 8 0 lb41 lb241 lb5 lb239 = true := by decide +kernel
lemma lb334 : Slice lb41 lb241 (subcube 0 8) 7 := slice_direct lb335 lb294
lemma lb337 : sliceDirectCheck 0 16 0 lb41 lb241 lb2 lb238 = true := by decide +kernel
lemma lb336 : Slice lb41 lb241 (subcube 0 16) 7 := slice_direct lb337 lb292
lemma lb316 : sliceDirectCheck 0 4 0 lb41 lb241 lb8 lb240 = true := by decide +kernel
lemma lb315 : Slice lb41 lb241 (subcube 0 4) 7 := slice_direct lb316 lb296
lemma lb318 : sliceDirectCheck 0 34 0 lb41 lb241 lb428 lb419 = true := by decide +kernel
lemma lb317 : Slice lb41 lb241 (subcube 0 34) 4 := slice_direct lb318 lb483
lemma lb320 : sliceDirectCheck 0 18 0 lb41 lb241 lb429 lb420 = true := by decide +kernel
lemma lb319 : Slice lb41 lb241 (subcube 0 18) 4 := slice_direct lb320 lb485
set_option maxRecDepth 200000 in
lemma lb340 : ∀ i (hi : i < lb339.size), Slice lb41 lb241 lb339[i].1 lb339[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb41 lb241 p.1 p.2) (forall_cons lb312 (forall_cons lb314 (forall_cons lb322 (forall_cons lb324 (forall_cons lb326 (forall_cons lb328 (forall_cons lb330 (forall_cons lb332 (forall_cons lb334 (forall_cons lb336 (forall_cons lb315 (forall_cons lb317 (forall_cons lb319 (fun _ h => (List.not_mem_nil h).elim))))))))))))))
lemma lb244 : ∀ i (hi : i < lb243.size), ∀ c, lb243[i] = some c → ValidPool lb41 lb241 c := buildPools_sound lb340
lemma lb272 : ∀ i (hi : i < lb449.size), ∀ xs ∈ lb449[i], Impossible lb241 (0 - 1) xs.toFinset := by intro i hi; simp [lb449] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb273 : checkNodes lb248 lb241 lb634 lb243 lb250 lb449 0 lb492 = true := by decide +kernel
def lb254 : Array (List (List Nat)) := buildBuckets 1 lb248 lb492
lemma lb255 : ∀ i (hi : i < lb254.size), ∀ xs ∈ lb254[i], Impossible lb241 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb285 lb249 lb244 lb251 lb272 lb273
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb274 : checkNodes lb248 lb241 lb634 lb243 lb250 lb254 1 lb492 = true := by decide +kernel
lemma lb256 : ∀ i (hi : i < lb254.size), ∀ xs ∈ lb254[i], Impossible lb241 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb285 lb249 lb244 lb251 lb255 lb274
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb275 : checkNodes lb248 lb241 lb634 lb243 lb250 lb254 2 lb492 = true := by decide +kernel
lemma lb257 : ∀ i (hi : i < lb254.size), ∀ xs ∈ lb254[i], Impossible lb241 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb285 lb249 lb244 lb251 lb256 lb275
def lb303 : List NodeSpec := [([29,8,16,20],[],[]),([29,12,25,1],[],[]),([9,32,10,21],[0],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb276 : checkNodes lb248 lb241 lb634 lb243 lb250 lb254 3 lb303 = true := by decide +kernel
def lb258 : Array (List (List Nat)) := buildBuckets 2 lb248 lb303
lemma lb259 : ∀ i (hi : i < lb258.size), ∀ xs ∈ lb258[i], Impossible lb241 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb285 lb249 lb244 lb251 lb257 lb276
def lb304 : List NodeSpec := [([8,16,20,2,11],[1],[0]),([23,8,10,2,4],[],[]),([29,12,0,1,4],[],[0,1]),([12,25,1,2,11],[2],[0]),([12,25,20,2,3],[],[]),([26,34,2,3,4],[],[]),([26,1,2,3,28],[],[]),([9,16,20,2,11],[3],[2]),([23,9,10,2,4],[],[]),([17,25,20,2,3],[],[]),([35,1,2,3,4],[],[]),([9,32,10,2,4],[0],[0]),([9,16,10,21,4],[],[0,1]),([5,7,10,21,11],[],[]),([29,8,16,1,4],[],[3,4,0]),([14,25,20,2,3],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb277 : checkNodes lb248 lb241 lb634 lb243 lb250 lb258 4 lb304 = true := by decide +kernel
def lb260 : Array (List (List Nat)) := buildBuckets 6 lb248 lb304
lemma lb261 : ∀ i (hi : i < lb260.size), ∀ xs ∈ lb260[i], Impossible lb241 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb285 lb249 lb244 lb251 lb259 lb277
def lb305 : List NodeSpec := [([5,19,1,2,3,4],[4],[]),([14,0,1,2,3,4],[2],[5]),([5,7,10,6,4],[5,1,6,7],[6,7,8,9]),([8,16,1,2,11,4],[1],[4,8,0]),([8,16,20,2,3,4],[],[10,8,0]),([5,7,15,11,3,4],[5,1,6,7,0,8],[11,12,6,13,14,7,15,16,17]),([8,16,10,2,4],[5,1,9],[4,18,8]),([5,7,10,21,3,4],[],[19,20,15,21,9,0]),([12,0,1,2,11,4],[2],[0,1]),([22,0,1,2,3,4],[],[]),([23,8,1,2,3,4],[],[0]),([9,16,10,2,4],[10,0,7,1,9],[4,0,1]),([9,5,16,10,2,4],[0,6,7,1],[]),([24,5,0,1,2,3],[11],[]),([9,5,16,1,6,4],[0,7,6,1],[]),([17,25,1,2,3,4],[2,12],[0,22]),([17,5,16,1,2,4],[10,7],[]),([26,5,1,2,3,4],[4],[]),([12,25,1,2,3,4],[2],[0]),([27,0,1,2,3,4],[],[2]),([24,0,1,2,3,4],[],[]),([14,0,1,2,3,28],[],[0,1,2,23,5]),([9,16,1,2,11,4],[3],[19,1,0,2,22]),([26,9,1,2,3,4],[4],[24]),([14,25,1,2,3,4],[2],[0,22,24]),([9,16,20,2,3,4],[],[4,1,22,25,0]),([26,14,1,2,3,4],[4],[0,22,24]),([29,8,0,1,3,4],[],[2,26,3,0,4,27]),([30,0,1,2,3,4],[12],[]),([17,9,16,1,2,4],[10,7,1],[]),([24,14,0,1,2,3],[2],[]),([9,18,0,1,6,4],[0,6,13],[]),([24,9,0,1,2,3],[],[]),([23,9,1,2,3,4],[],[0,22]),([24,0,1,2,3],[],[]),([31,0,1,2,3,4],[],[0,1,2,23,5]),([9,32,1,2,3,4],[0],[0,4,22,28]),([33,0,1,2,3,4],[12],[23])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb278 : checkNodes lb248 lb241 lb634 lb243 lb250 lb260 5 lb305 = true := by decide +kernel
def lb262 : Array (List (List Nat)) := buildBuckets 13 lb248 lb305
lemma lb263 : ∀ i (hi : i < lb262.size), ∀ xs ∈ lb262[i], Impossible lb241 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb285 lb249 lb244 lb251 lb261 lb278
def lb306 : List NodeSpec := [([5,7,10,2,3,4],[14,4,1,6,7,15,16],[6,20,14,7,16,29,8,0,30]),([8,0,1,2,11,3,4],[1,3,0,17],[0,4,18,8,1,27]),([12,0,1,2,3,4],[6,4,1,18,2,19],[0,1]),([13,5,0,1,2,3,4],[20],[0,1]),([9,5,0,1,6,3,4],[21,0,7,6,1,22,23],[0,1]),([14,9,0,1,2,3,4],[10,24,22],[0,1,2,23]),([9,0,1,2,11,3,4],[3,1,0,24],[0,23,5,4,1,27,2,31]),([5,7,15,3,4],[25,14,21,1,0,26,8,7],[12,6,14,7,16,17,0]),([9,16,1,2,3,4],[10,0,7,1,22,27,28],[0,4,22]),([17,9,0,1,2,3,4],[10,0,1,7,22],[23,0,1,2]),([14,5,0,1,2,3,4],[5,29,30],[0,1]),([17,5,0,1,2,3,4],[21,10,6,0,7,22,31],[23,0,1]),([8,16,1,2,3,4],[5,4,1,28,19],[4,18,0]),([17,0,1,2,3,4],[0,4,7,1,22,2,31,32,33,12],[23,0,1,2]),([5,7,1,2,11,3,4],[5,1,6,7,34],[11,24,19,13,20,32,0,8,30,33,9,34,35]),([14,0,1,2,3,4],[30,35,36,22,2],[0,1,2,23]),([9,5,16,1,2,3,4],[0,7,6,1],[0]),([9,18,0,1,2,3,4],[22,21,0,37],[23,2,0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb279 : checkNodes lb248 lb241 lb634 lb243 lb250 lb262 6 lb306 = true := by decide +kernel
def lb264 : Array (List (List Nat)) := buildBuckets 7 lb248 lb306
lemma lb265 : ∀ i (hi : i < lb264.size), ∀ xs ∈ lb264[i], Impossible lb241 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb285 lb249 lb244 lb251 lb263 lb279
def lb307 : List NodeSpec := [([5,0,1,6,2,3,4],[0,38,5,1,39,40,3,41,42,29],[0,36,2,23,12,6,14,22,24,16,37,38,39,33,9,40]),([5,7,1,2,3,4],[43,21,0,4,1,15,34,7,39],[12,6,14,7,0,4,22,28]),([8,0,1,2,3,4],[14,0,4,1,39,10,2,17,19],[0,4,1,27]),([9,5,0,1,2,3,4],[21,0,7,1,6,29,22,24,44,45,39],[0,4,1,27]),([9,0,1,2,3,4],[0,7,1,10,22,2,24,44,45,39],[0,4,1,27,2,31])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb280 : checkNodes lb248 lb241 lb634 lb243 lb250 lb264 7 lb307 = true := by decide +kernel
def lb266 : Array (List (List Nat)) := buildBuckets 2 lb248 lb307
lemma lb267 : ∀ i (hi : i < lb266.size), ∀ xs ∈ lb266[i], Impossible lb241 7 xs.toFinset :=
  buildBuckets_sound (by decide) lb285 lb249 lb244 lb251 lb265 lb280
def lb308 : List NodeSpec := [([5,0,1,2,3,4],[14,4,21,1,39,10,40,2,46],[0,12,6,1,30,33,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb281 : checkNodes lb248 lb241 lb634 lb243 lb250 lb266 8 lb308 = true := by decide +kernel
def lb268 : Array (List (List Nat)) := buildBuckets 1 lb248 lb308
lemma lb269 : ∀ i (hi : i < lb268.size), ∀ xs ∈ lb268[i], Impossible lb241 8 xs.toFinset :=
  buildBuckets_sound (by decide) lb285 lb249 lb244 lb251 lb267 lb281
def lb309 : List NodeSpec := [([0,1,2,3,4],[4,14,21,10,2],[0,22,24,19,38,39,41,36,42,43])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb282 : checkNodes lb248 lb241 lb634 lb243 lb250 lb268 9 lb309 = true := by decide +kernel
def lb270 : Array (List (List Nat)) := buildBuckets 1 lb248 lb309
lemma lb271 : ∀ i (hi : i < lb270.size), ∀ xs ∈ lb270[i], Impossible lb241 9 xs.toFinset :=
  buildBuckets_sound (by decide) lb285 lb249 lb244 lb251 lb269 lb282
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb284 : forestRootCheck lb41 lb241 [(VAR 1,30,28),(VAR 2,30,26),(VAR 3,30,22),(VAR 4,30,14),(VAR 5,46,14)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb283 : bucketContains lb270 lb41 = true := by decide +kernel
lemma lb298 : Lower lb41 lb241 10 := lower_of_forest lb284 lb271 lb283
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q54d : Lower (varsOf 31) 0xe8808000e8808000e8808000e8808000 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]) (roots2 := lb41) (T2 := lb241) _ lb298
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q54 : Lower (varsOf 31) 0xfffefee8fffefee8fffefee8fffefee8 10 := dualLower (by decide +kernel) (by decide +kernel) q54d
def s3NR : List Nat := varsOf 63
def s3NG : Nat := 0xfffefeeefffafee8fffefeeefffafee8
def s3NPos : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12,17,17,20,20,24,24,33,33,34,44,44,50,50,52]
def s3NNeg : List Nat := [1,2,1,4,2,4,1,8,2,8,4,8,1,16,4,16,8,16,1,32,2,36,40,18,48,36]
def s3NMask : Nat := fullMask 26
def s3NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc30cf,0x41045),(0xcccccccccccccccccccccccccccccccc,0x1900333,0x900112),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x260cc3c,0x2204428),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x630fc0,0x410a80),(0xffff0000ffff0000ffff0000ffff0000,0x383f000,0x182a000),(0xffffffff00000000ffffffff00000000,0x3fc0000,0x3680000)]
def s3NSteps : List (Nat × Nat × Nat) := []
def s3NW : BT Decor := buildWiresBT 3 s3NBase s3NSteps
def s3NAutoList : List (List (Nat × Nat)) := [[],[(2,3)]]
def s3NAutos : BT (List (Nat × Nat)) := btOfList 1 s3NAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NPairs : goodPairs s3NG s3NPos s3NNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBaseOk : ∀ x ∈ s3NBase, faithful s3NPos s3NNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NWOk : btAll (fun x => faithful s3NPos s3NNeg x ∧ x.1 < 2^128) s3NW := buildWiresBT_faithful s3NBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw s3NG = s3NG) s3NAutos := btAll_ofList (autos_of (by decide +kernel))
def s3NSliceList : List (Option (Nat × Nat)) := [some (0xffff00000000ffffffff00000000ffff,10)]
def s3NSlices : BT (Option (Nat × Nat)) := btOfList 1 s3NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NSlice0 : Slice s3NR s3NG 0xffff00000000ffffffff00000000ffff 10 := mappedSlice (f := identifyRow 0 0 4 5) (R := varsOf 31) (G := 0xfffefee8fffefee8fffefee8fffefee8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q54
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s3NR s3NG p.1 p.2) s3NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s3NR s3NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s3NSlice0) (fun _ h => (List.not_mem_nil h).elim))
def s3NEmpty : BT (List (List Nat)) := BT.empty
lemma s3NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s3NG (9 - 1) xs.toFinset) s3NEmpty := trivial
def s3NBlock9_0Specs : List PoolSpec := [(0,[])]
def s3NBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s3NW s3NR s3NSlices s3NBlock9_0Specs
def s3NBlock9_0 : List NodeSpec := [([0,1,2,3,4,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBlock9_0Ok : checkNodesBT s3NW s3NG s3NMask s3NBlock9_0Pools s3NAutos s3NEmpty 9 s3NBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBlock9_0Mem : ∀ ns ∈ s3NBlock9_0, Impossible s3NG 9 (nodeValsBT s3NW ns).toFinset := checkNodesBT_mem (by decide) s3NPairs s3NWOk (buildPoolsBT_sound s3NSlicesOk) s3NAutosOk s3NEmptyOk s3NBlock9_0Ok
def s3NNodes9 : List NodeSpec := s3NBlock9_0
def s3NBucket9 : BT (List (List Nat)) := buildBucketsBT s3NW s3NNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s3NG 9 xs.toFinset) s3NBucket9 := buildBucketsBT_of_mem s3NBlock9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBound : Lower s3NR s3NG 10 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) s3NBucket9Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q53 : Lower (varsOf 119) 0xfffffffffffffefefefefafafefea0a0 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (1, 2)]) (roots2 := s3NR) (T2 := s3NG) _ s3NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q55 : Lower (varsOf 125) 0xfffffffffffffffafffafffafafaa0a0 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (2, 3), (3, 4), (2, 3), (1, 2)]) (roots2 := s3NR) (T2 := s3NG) _ s3NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q56d : Lower (varsOf 79) 0xfac8fac8fac8fac88000800080008000 8 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (5, 6), (0, 1), (1, 2), (2, 3), (3, 4), (1, 2)]) (roots2 := lb41) (T2 := lb145) _ lb207
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q56 : Lower (varsOf 79) 0xfffefffefffefffeeca0eca0eca0eca0 8 := dualLower (by decide +kernel) (by decide +kernel) q56d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q57d : Lower (varsOf 93) 0xfafaa0a0fafaa0a0a0000000a0000000 8 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (2, 3), (3, 4), (1, 2)]) (roots2 := lb90) (T2 := lb87) _ lb123
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q57 : Lower (varsOf 93) 0xfffffffafffffffafafaa0a0fafaa0a0 8 := dualLower (by decide +kernel) (by decide +kernel) q57d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q58d : Lower (varsOf 85) 0xfafaa0a0fafaa0a0a0a00000a0a00000 7 := by
  apply carry_of (swaps := [(5, 6), (1, 2), (2, 3), (0, 1)]) (roots2 := lb11) (T2 := lb422) _ lb489
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q58 : Lower (varsOf 85) 0xfffffafafffffafafafaa0a0fafaa0a0 7 := dualLower (by decide +kernel) (by decide +kernel) q58d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q59d : Lower (varsOf 101) 0xfafafafaa0a0a0a0a0a0a0a000000000 7 := by
  apply carry_of (swaps := [(5, 6), (4, 5), (1, 2), (2, 3), (0, 1)]) (roots2 := lb11) (T2 := lb422) _ lb489
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q59 : Lower (varsOf 101) 0xfffffffffafafafafafafafaa0a0a0a0 7 := dualLower (by decide +kernel) (by decide +kernel) q59d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q60d : Lower (varsOf 31) 0xfac88080fac88080fac88080fac88080 7 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (2, 3), (3, 4), (1, 2)]) (roots2 := lb41) (T2 := lb606) _ lb644
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q60 : Lower (varsOf 31) 0xfefeeca0fefeeca0fefeeca0fefeeca0 7 := dualLower (by decide +kernel) (by decide +kernel) q60d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q61d : Lower (varsOf 47) 0xfac8fac8a000a000fac8fac8a000a000 7 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (2, 3), (1, 2)]) (roots2 := lb41) (T2 := lb606) _ lb644
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q61 : Lower (varsOf 47) 0xfffafffaeca0eca0fffafffaeca0eca0 7 := dualLower (by decide +kernel) (by decide +kernel) q61d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q62 : Lower (varsOf 55) 0xfefefafafefea0a0fefefafafefea0a0 7 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (2, 3), (1, 2)]) (roots2 := lb679) (T2 := lb667) _ lb727
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q63 : Lower (varsOf 61) 0xfffafffafafaa0a0fffafffafafaa0a0 7 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (2, 3), (3, 4), (1, 2)]) (roots2 := lb679) (T2 := lb667) _ lb727
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q64 : Lower (varsOf 21) 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0 4 := by
  apply carry_of (swaps := [(3, 4), (0, 1)]) (roots2 := lb548) (T2 := lb544) _ lb568
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q65 : Lower (varsOf 69) 0xfafafafafafafafaa0a0a0a0a0a0a0a0 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (5, 6), (0, 1)]) (roots2 := lb548) (T2 := lb544) _ lb568
  decide +kernel
def rootNR : List Nat := varsOf 127
def rootNG : Nat := 0xfffffffffffffffefffefffafefeeca0
def rootNPos : List Nat := [5,5,7,7,10,10,11,11,13,13,14,14,17,17,17,18,18,18,18,18,19,20,20,22,25,26,28,33,33,33,35,36,36,38,40,40,40,40,41,42,44,50,50,56,56,65,65,65,65,66,66,66,67,68,68,70,72,72,72,73,76,80,80,80,88,96,96,96,98,112]
def rootNNeg : List Nat := [1,4,3,6,2,8,3,9,9,12,6,12,1,3,16,2,16,24,34,48,3,4,16,6,9,24,12,1,3,32,3,4,32,6,8,24,32,48,9,34,12,34,48,24,48,1,3,9,64,2,34,64,3,4,64,6,8,24,64,9,12,16,48,64,24,32,34,64,34,48]
def rootNMask : Nat := fullMask 70
def rootNBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x811e040791073cf,0x810e040591031c5),(0xcccccccccccccccccccccccccccccccc,0x10009e0682429f8cfc,0x14009642825094a45c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x10e0010384e00f0f,0x10a0010284a00e0a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x11f0019fc07000ff0,0x11b00894c07020ba0),(0xffff0000ffff0000ffff0000ffff0000,0x21e0001e0007fff000,0x2162001c28024b4000),(0xffffffff00000000ffffffff00000000,0x3e00001ffff8000000,0x36400416b1200c0000),(0xffffffffffffffff0000000000000000,0x3fffffe00000000000,0x88449000000000000)]
def rootNSteps : List (Nat × Nat × Nat) := [(1,1,3),(1,1,6),(1,3,6),(1,7,6),(1,1,4),(1,4,6),(1,11,5),(1,5,12),(1,5,6),(1,13,6),(3,3,16),(2,13,6),(1,11,6),(3,5,19),(1,1,5),(1,4,5),(1,21,6),(3,1,12),(3,4,15),(3,3,23),(3,4,23),(3,3,8),(3,4,8),(1,29,5),(3,3,30),(3,5,8),(1,32,4),(1,3,4),(1,3,5),(1,3,22),(1,3,12),(3,1,37),(3,3,12),(3,1,14),(1,3,14),(3,3,14),(1,24,5),(1,39,5),(3,5,12),(1,45,1),(1,45,3)]
def rootNW : BT Decor := buildWiresBT 6 rootNBase rootNSteps
def rootNAutoList : List (List (Nat × Nat)) := [[],[(1,3),(4,5)],[(0,2)],[(0,2),(1,3),(4,5)]]
def rootNAutos : BT (List (Nat × Nat)) := btOfList 2 rootNAutoList
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
def rootNSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,11),some (subcubeFast 1 0,11),some (subcubeFast 64 0,10),some (subcubeFast 32 0,10),some (subcubeFast 16 0,10),some (subcubeFast 8 0,10),some (subcubeFast 2 0,10),some (subcubeFast 48 0,8),some (subcubeFast 34 0,8),some (subcubeFast 42 0,7),some (subcubeFast 26 0,7),some (subcubeFast 96 0,7),some (subcubeFast 80 0,7),some (subcubeFast 72 0,7),some (subcubeFast 66 0,7),some (subcubeFast 98 8,4),some (subcubeFast 106 0,4),some (subcubeFast 88 2,4),some (subcubeFast 90 0,4),some (subcubeFast 58 0,4)]
def rootNSlices : BT (Option (Nat × Nat)) := btOfList 5 rootNSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice0 : Slice rootNR rootNG (subcubeFast 4 0) 11 := slice_fast_direct (zDead := 0) (qRoots := varsOf 123) (qGoal := 0xffffffffffffffeeffeeffaaeeeecc00) (by decide +kernel) q0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice1 : Slice rootNR rootNG (subcubeFast 1 0) 11 := slice_fast_direct (zDead := 0) (qRoots := varsOf 126) (qGoal := 0xfffffffffffffffcfffcfff0fcfccc00) (by decide +kernel) q24
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice2 : Slice rootNR rootNG (subcubeFast 64 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 63) (qGoal := 0xfffefffafefeeca0fffefffafefeeca0) (by decide +kernel) q25
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice3 : Slice rootNR rootNG (subcubeFast 32 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 95) (qGoal := 0xfffffffefffffffefefeeca0fefeeca0) (by decide +kernel) q46
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice4 : Slice rootNR rootNG (subcubeFast 16 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 111) (qGoal := 0xfffffffffffefffefffafffaeca0eca0) (by decide +kernel) q52
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice5 : Slice rootNR rootNG (subcubeFast 8 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 119) (qGoal := 0xfffffffffffffefefefefafafefea0a0) (by decide +kernel) q53
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice6 : Slice rootNR rootNG (subcubeFast 2 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 125) (qGoal := 0xfffffffffffffffafffafffafafaa0a0) (by decide +kernel) q55
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice7 : Slice rootNR rootNG (subcubeFast 48 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 79) (qGoal := 0xfffefffefffefffeeca0eca0eca0eca0) (by decide +kernel) q56
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice8 : Slice rootNR rootNG (subcubeFast 34 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 93) (qGoal := 0xfffffffafffffffafafaa0a0fafaa0a0) (by decide +kernel) q57
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice9 : Slice rootNR rootNG (subcubeFast 42 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 85) (qGoal := 0xfffffafafffffafafafaa0a0fafaa0a0) (by decide +kernel) q58
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice10 : Slice rootNR rootNG (subcubeFast 26 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 101) (qGoal := 0xfffffffffafafafafafafafaa0a0a0a0) (by decide +kernel) q59
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice11 : Slice rootNR rootNG (subcubeFast 96 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfefeeca0fefeeca0fefeeca0fefeeca0) (by decide +kernel) q60
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice12 : Slice rootNR rootNG (subcubeFast 80 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfffafffaeca0eca0fffafffaeca0eca0) (by decide +kernel) q61
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice13 : Slice rootNR rootNG (subcubeFast 72 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefefafafefea0a0fefefafafefea0a0) (by decide +kernel) q62
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice14 : Slice rootNR rootNG (subcubeFast 66 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafffafafaa0a0fffafffafafaa0a0) (by decide +kernel) q63
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice15 : Slice rootNR rootNG (subcubeFast 98 8) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 21) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) q64
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice16 : Slice rootNR rootNG (subcubeFast 106 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 21) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) q64
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice17 : Slice rootNR rootNG (subcubeFast 88 2) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 37) (qGoal := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0) (by decide +kernel) q18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice18 : Slice rootNR rootNG (subcubeFast 90 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 37) (qGoal := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0) (by decide +kernel) q18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice19 : Slice rootNR rootNG (subcubeFast 58 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 69) (qGoal := 0xfafafafafafafafaa0a0a0a0a0a0a0a0) (by decide +kernel) q65
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlicesOk : btAll (fun o => ∀ p, o = some p → Slice rootNR rootNG p.1 p.2) rootNSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice rootNR rootNG p.1 p.2) (forall_cons (fun _ h => by cases h; exact rootNSlice0) (forall_cons (fun _ h => by cases h; exact rootNSlice1) (forall_cons (fun _ h => by cases h; exact rootNSlice2) (forall_cons (fun _ h => by cases h; exact rootNSlice3) (forall_cons (fun _ h => by cases h; exact rootNSlice4) (forall_cons (fun _ h => by cases h; exact rootNSlice5) (forall_cons (fun _ h => by cases h; exact rootNSlice6) (forall_cons (fun _ h => by cases h; exact rootNSlice7) (forall_cons (fun _ h => by cases h; exact rootNSlice8) (forall_cons (fun _ h => by cases h; exact rootNSlice9) (forall_cons (fun _ h => by cases h; exact rootNSlice10) (forall_cons (fun _ h => by cases h; exact rootNSlice11) (forall_cons (fun _ h => by cases h; exact rootNSlice12) (forall_cons (fun _ h => by cases h; exact rootNSlice13) (forall_cons (fun _ h => by cases h; exact rootNSlice14) (forall_cons (fun _ h => by cases h; exact rootNSlice15) (forall_cons (fun _ h => by cases h; exact rootNSlice16) (forall_cons (fun _ h => by cases h; exact rootNSlice17) (forall_cons (fun _ h => by cases h; exact rootNSlice18) (forall_cons (fun _ h => by cases h; exact rootNSlice19) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))
def rootNEmpty : BT (List (List Nat)) := BT.empty
lemma rootNEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG (8 - 1) xs.toFinset) rootNEmpty := trivial
def rootNBlock8_0Specs : List PoolSpec := [(17,[]),(10,[]),(15,[]),(0,[(1,1,4),(1,1,6),(1,4,6),(1,11,5)]),(1,[(1,1,4),(1,1,6),(1,4,6),(1,11,5)]),(8,[(1,4,6)]),(0,[(1,1,4),(1,1,6),(1,4,6),(1,5,12)]),(1,[(1,1,4),(1,1,6),(1,4,6),(1,5,12)]),(7,[(1,1,6)]),(0,[(1,1,4),(1,11,5),(1,13,6),(3,3,16)]),(19,[]),(0,[(1,1,5),(1,1,6),(1,4,5),(1,4,6)]),(1,[(1,1,5),(1,1,6),(1,4,5),(1,4,6)]),(0,[(1,1,6),(3,4,8),(1,29,5),(3,3,30)]),(7,[(1,3,12),(3,1,37)]),(0,[(1,4,5),(1,4,6),(1,3,12),(3,1,37)]),(1,[(1,4,5),(1,4,6),(1,3,12),(3,1,37)]),(0,[(1,4,5),(1,22,6),(1,1,14),(3,3,16)]),(1,[(1,4,5),(1,22,6),(1,1,14),(3,3,16)]),(0,[(1,4,6),(1,3,12),(3,1,37),(1,5,12)]),(1,[(1,4,6),(1,3,12),(3,1,37),(1,5,12)])]
def rootNBlock8_0Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock8_0Specs
def rootNBlock8_0 : List NodeSpec := [([31,0,1,2,4,5,6],[0,2,13],[]),([17,0,1,2,4,5,6],[0,2,9],[]),([17,0,1,2,4,5,6,14],[0,2,10,17,18],[]),([38,0,2,3,4,5,6,14],[0,2,10,19,20],[]),([38,0,2,3,5,22,6,12],[0,14,15,16],[]),([0,2,3,11,5,8,12,14],[0,5,6,7],[]),([0,2,3,5,13,8,12],[0,1,3,4],[]),([0,2,3,21,22,8,12],[0,8,11,12],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_0Pools rootNAutos rootNEmpty 8 rootNBlock8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_0Mem : ∀ ns ∈ rootNBlock8_0, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNEmptyOk rootNBlock8_0Ok
def rootNNodes8 : List NodeSpec := rootNBlock8_0
def rootNBucket8 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 8 xs.toFinset) rootNBucket8 := buildBucketsBT_of_mem rootNBlock8_0Mem
def rootNBlock9_0Specs : List PoolSpec := [(9,[]),(17,[]),(15,[]),(8,[(1,4,6)]),(7,[(1,1,6)]),(19,[]),(0,[(1,1,4),(1,11,5),(2,13,6)]),(18,[]),(0,[(1,1,4),(1,11,6),(3,5,19)]),(1,[(1,1,4),(1,11,6),(3,5,19)]),(0,[(1,1,5),(1,4,6),(3,1,12)]),(1,[(1,1,5),(1,4,6),(3,1,12)]),(0,[(1,1,5),(1,5,6),(3,4,15)]),(1,[(1,1,5),(1,5,6),(3,4,15)]),(0,[(1,1,5),(1,21,6),(3,3,23)]),(1,[(1,1,5),(1,21,6),(3,3,23)]),(0,[(1,1,5),(1,21,6),(3,4,23)]),(9,[(1,4,6)]),(0,[(1,1,6),(1,4,5),(3,4,8)]),(1,[(1,1,6),(1,4,5),(3,4,8)]),(0,[(1,1,6),(1,5,8),(3,3,23)]),(7,[(3,3,12)]),(0,[(1,4,5),(1,4,6),(3,3,12)]),(1,[(1,4,5),(1,4,6),(3,3,12)]),(0,[(1,4,6),(1,5,12),(3,3,14)]),(1,[(1,4,6),(1,5,12),(3,3,14)])]
def rootNBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock9_0Specs
def rootNBlock9_0 : List NodeSpec := [([18,0,1,2,3,4,5,6],[1,5,6],[]),([20,0,1,2,3,4,5,6],[1,7,8,9],[]),([29,0,1,2,3,5,22,6],[2,4,18,19],[]),([25,0,1,2,3,4,21,6],[0,1,2,12,13],[]),([27,0,1,2,3,4,5,6],[1,2,16],[]),([39,0,1,2,3,5,22,6],[2,21,22,23],[]),([26,0,1,2,4,5,6],[0,1,14,15],[]),([26,0,1,2,4,5,6,8],[1,2,20],[]),([26,0,1,2,4,5,6,23],[0,1,2,14],[]),([42,0,1,2,3,4,5,6,12],[1,2,17,24,25],[]),([42,0,1,2,3,4,5,6,12,14],[1,2,5,17],[]),([24,0,2,3,4,5,21,6],[1,3,10,11],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_0Pools rootNAutos rootNBucket8 9 rootNBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_0Mem : ∀ ns ∈ rootNBlock9_0, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_0Ok
def rootNBlock9_1Specs : List PoolSpec := [(9,[]),(17,[]),(15,[]),(8,[(1,4,6)]),(7,[(1,1,6)]),(12,[]),(19,[]),(18,[]),(8,[(1,22,6)]),(16,[]),(9,[(1,4,6)]),(0,[(1,1,6),(3,4,8),(1,29,5)]),(0,[(1,1,6),(3,5,8),(1,32,4)]),(1,[(1,1,6),(3,5,8),(1,32,4)]),(0,[(1,4,5),(1,22,6),(3,1,14)]),(1,[(1,4,5),(1,22,6),(3,1,14)]),(0,[(1,4,6),(1,1,12),(1,5,12)]),(1,[(1,4,6),(1,1,12),(1,5,12)]),(0,[(1,4,6),(3,1,12),(1,24,5)]),(1,[(1,4,6),(3,1,12),(1,24,5)]),(0,[(1,4,6),(1,3,12),(3,1,37)]),(1,[(1,4,6),(1,3,12),(3,1,37)]),(0,[(1,4,6),(1,3,12),(1,5,12)]),(1,[(1,4,6),(1,3,12),(1,5,12)]),(0,[(1,4,6),(3,3,12),(1,39,5)]),(1,[(1,4,6),(3,3,12),(1,39,5)]),(0,[(1,4,6),(3,5,12),(1,45,1)]),(0,[(1,4,6),(3,5,12),(1,45,3)])]
def rootNBlock9_1Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock9_1Specs
def rootNBlock9_1 : List NodeSpec := [([38,0,2,3,4,5,6,12],[1,2,20,21],[0]),([40,0,1,2,3,4,5,6],[1,8,14,15],[]),([40,0,1,2,3,4,5,6,14],[1,2,6,8,14,15],[]),([0,1,46,2,3,4,5,6],[1,3,7,26],[]),([0,1,2,3,47,4,5,6],[1,2,27],[]),([0,1,2,3,4,33,5,6],[4,7,12,13],[]),([0,1,2,3,4,5,30,6],[0,1,2,11],[0]),([0,1,2,3,4,5,44,6],[2,5,24,25],[]),([0,1,2,3,4,5,43,6],[5,10,18,19],[]),([0,1,2,3,4,5,6,12,14,41],[1,2,6,7,9],[]),([0,1,2,3,4,5,6,19,14],[1,2,6,7,16,17],[]),([0,1,2,3,4,5,6,37,14],[1,2,3,6,22,23],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_1Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_1Pools rootNAutos rootNBucket8 9 rootNBlock9_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_1Mem : ∀ ns ∈ rootNBlock9_1, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_1Ok
def rootNBlock9_2Specs : List PoolSpec := [(9,[]),(17,[]),(10,[]),(2,[]),(15,[]),(14,[]),(8,[(1,4,6)]),(7,[(1,1,6)]),(0,[(1,1,4),(1,4,6),(1,5,12)]),(1,[(1,1,4),(1,4,6),(1,5,12)]),(7,[]),(12,[]),(0,[(1,1,4),(1,11,5),(1,5,6)]),(1,[(1,1,4),(1,11,5),(1,5,6)]),(9,[(1,13,6)]),(0,[(1,1,4),(1,11,5),(1,13,6)]),(1,[(1,1,4),(1,11,5),(1,13,6)]),(19,[]),(18,[]),(0,[(1,1,4),(1,5,6),(1,11,15)]),(1,[(1,1,4),(1,5,6),(1,11,15)]),(11,[]),(7,[(1,21,6)]),(0,[(1,1,5),(1,4,5),(1,21,6)]),(1,[(1,1,5),(1,4,5),(1,21,6)]),(0,[(1,1,5),(1,4,5),(1,22,6)]),(1,[(1,1,5),(1,4,5),(1,22,6)]),(8,[(1,22,6)]),(0,[(1,1,5),(1,5,6),(1,4,15)]),(1,[(1,1,5),(1,5,6),(1,4,15)]),(9,[(1,4,6)]),(0,[(1,1,6),(1,4,5),(1,4,6)]),(1,[(1,1,6),(1,4,5),(1,4,6)]),(0,[(1,1,6),(1,4,6),(1,5,12)]),(1,[(1,1,6),(1,4,6),(1,5,12)]),(7,[(1,1,12)]),(0,[(1,4,5),(1,4,6),(1,1,12)]),(1,[(1,4,5),(1,4,6),(1,1,12)]),(0,[(1,4,5),(1,4,6),(1,3,12)]),(1,[(1,4,5),(1,4,6),(1,3,12)]),(0,[(1,4,5),(1,22,6),(1,1,14)]),(1,[(1,4,5),(1,22,6),(1,1,14)]),(9,[(1,22,6)])]
def rootNBlock9_2Pools : BT (Option BoundPool) := buildPoolsBT 6 rootNW rootNR rootNSlices rootNBlock9_2Specs
def rootNBlock9_2 : List NodeSpec := [([0,1,2,3,4,5,6,15,16],[0,1,4,17,18,19,20],[]),([0,1,2,3,4,5,6,14,16],[1,4,17,18,40,41,42],[0]),([0,1,2,3,4,5,6,16],[1,14,15,16],[0]),([0,1,2,3,4,5,8,12,14],[1,6,21,33,34],[0]),([0,1,2,3,4,21,6,15,14],[1,4,10,21,28,29],[]),([0,1,2,3,4,21,6,14],[1,10,21,25,26,27],[]),([0,1,2,3,4,22,6,23],[0,1,22,23,24],[]),([0,1,2,3,4,13,6,15],[1,3,10,12,13],[]),([0,1,2,3,11,5,6,12,14],[1,6,8,9,10],[0]),([0,1,2,3,5,22,6,12,19],[2,18,35,36,37],[]),([0,1,2,3,5,22,6,12,37],[1,2,4,17,38,39],[0]),([0,1,2,3,5,22,8,12],[1,5,7,11,30,31,32],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_2Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_2Pools rootNAutos rootNBucket8 9 rootNBlock9_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_2Mem : ∀ ns ∈ rootNBlock9_2, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_2Ok
def rootNBlock9_3Specs : List PoolSpec := [(9,[]),(17,[]),(0,[(1,1,3),(1,1,6),(1,3,6)]),(1,[(1,1,3),(1,1,6),(1,3,6)]),(10,[]),(2,[]),(14,[]),(8,[(1,4,6)]),(0,[(1,1,4),(1,1,6),(1,4,6)]),(1,[(1,1,4),(1,1,6),(1,4,6)]),(7,[(1,1,6)]),(0,[(1,1,4),(1,1,6),(1,11,5)]),(1,[(1,1,4),(1,1,6),(1,11,5)]),(0,[(1,1,4),(1,4,6),(1,11,5)]),(1,[(1,1,4),(1,4,6),(1,11,5)]),(7,[]),(0,[(1,1,5),(1,1,6),(1,4,5)]),(1,[(1,1,5),(1,1,6),(1,4,5)]),(0,[(1,1,5),(1,1,6),(1,4,6)]),(1,[(1,1,5),(1,1,6),(1,4,6)]),(0,[(1,1,5),(1,4,5),(1,4,6)]),(1,[(1,1,5),(1,4,5),(1,4,6)])]
def rootNBlock9_3Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock9_3Specs
def rootNBlock9_3 : List NodeSpec := [([0,1,2,3,5,13,6,12],[1,7,13,14],[0]),([0,1,2,3,21,22,6,12],[0,1,15,20,21],[0]),([0,2,3,4,5,21,8,12],[1,7,18,19],[0]),([0,2,3,4,5,13,6,8],[1,10,11,12],[0]),([0,2,3,4,21,22,6,8],[1,10,16,17],[0]),([0,2,3,11,5,8,12],[1,4,6,7,8,9],[0]),([0,2,7,4,5,8,9],[0,1,2,3,4,5],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_3Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_3Pools rootNAutos rootNBucket8 9 rootNBlock9_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_3Mem : ∀ ns ∈ rootNBlock9_3, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_3Ok
def rootNNodes9 : List NodeSpec := rootNBlock9_0 ++ rootNBlock9_1 ++ rootNBlock9_2 ++ rootNBlock9_3
def rootNBucket9 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 9 xs.toFinset) rootNBucket9 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append rootNBlock9_0Mem rootNBlock9_1Mem) rootNBlock9_2Mem) rootNBlock9_3Mem)
def rootNBlock10_0Specs : List PoolSpec := [(9,[]),(17,[]),(10,[]),(2,[]),(15,[]),(14,[]),(13,[]),(8,[(1,4,6)]),(7,[(1,1,6)]),(2,[(1,1,4)]),(7,[]),(12,[]),(0,[(1,1,4),(1,11,5)]),(1,[(1,1,4),(1,11,5)]),(18,[]),(10,[(1,5,6)]),(0,[(1,1,4),(1,5,6)]),(1,[(1,1,4),(1,5,6)]),(11,[]),(0,[(1,1,5),(1,4,6)]),(1,[(1,1,5),(1,4,6)]),(16,[]),(0,[(1,1,6),(1,3,8)]),(0,[(1,1,6),(3,3,8)]),(1,[(1,1,6),(3,3,8)]),(9,[(1,4,6)]),(0,[(1,1,6),(1,4,5)]),(1,[(1,1,6),(1,4,5)]),(2,[(1,4,5)]),(0,[(1,1,6),(1,4,8)]),(1,[(1,1,6),(1,4,8)]),(0,[(1,1,6),(3,4,8)]),(1,[(1,1,6),(3,4,8)]),(0,[(1,1,6),(3,5,8)]),(1,[(1,1,6),(3,5,8)]),(0,[(1,4,6),(3,1,12)]),(1,[(1,4,6),(3,1,12)]),(0,[(1,4,6),(3,3,12)]),(1,[(1,4,6),(3,3,12)]),(0,[(1,4,6),(3,5,12)]),(1,[(1,4,6),(3,5,12)])]
def rootNBlock10_0Pools : BT (Option BoundPool) := buildPoolsBT 6 rootNW rootNR rootNSlices rootNBlock10_0Specs
def rootNBlock10_0 : List NodeSpec := [([32,0,1,2,3,4,5,6],[0,5,10,33,34],[0]),([45,0,1,2,3,4,5,6],[10,11,25,39,40],[0,1]),([29,0,1,2,3,4,5,6],[2,5,10,31,32],[0]),([28,0,1,2,3,4,5,6],[0,2,5,23,24],[]),([39,0,1,2,3,4,5,6],[2,10,11,37,38],[0]),([24,0,1,2,3,4,5,6],[2,10,11,35,36],[0]),([0,1,2,3,4,11,5,6,15],[9,10,15,16,17,18],[0]),([0,1,2,3,4,5,21,6,12],[1,7,10,11,19,20],[0]),([0,1,2,3,4,5,22,6,8],[0,1,4,5,8,26,27,28],[0]),([0,1,2,3,4,5,13,6],[0,1,2,3,10,12,13],[0]),([0,1,2,3,4,5,6,8,10],[0,1,5,6,21,22],[]),([0,1,2,3,4,5,6,8,19],[1,2,5,11,14,29,30],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock10_0Pools rootNAutos rootNBucket9 10 rootNBlock10_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_0Mem : ∀ ns ∈ rootNBlock10_0, Impossible rootNG 10 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket9Ok rootNBlock10_0Ok
def rootNBlock10_1Specs : List PoolSpec := [(9,[]),(17,[]),(10,[]),(2,[]),(15,[]),(14,[]),(0,[(1,1,3),(1,7,6)]),(1,[(1,1,3),(1,7,6)]),(13,[]),(7,[(1,1,6)]),(2,[(1,1,4)]),(7,[]),(12,[]),(18,[]),(0,[(1,1,4),(1,11,6)]),(1,[(1,1,4),(1,11,6)]),(7,[(1,11,6)]),(11,[]),(2,[(1,1,5)]),(0,[(1,1,5),(1,4,5)]),(1,[(1,1,5),(1,4,5)]),(0,[(1,1,5),(1,5,6)]),(1,[(1,1,5),(1,5,6)]),(0,[(1,1,5),(1,21,6)]),(1,[(1,1,5),(1,21,6)]),(0,[(1,1,6),(1,3,6)]),(1,[(1,1,6),(1,3,6)]),(9,[(1,4,6)]),(2,[(1,4,5)]),(0,[(1,1,6),(1,4,6)]),(1,[(1,1,6),(1,4,6)]),(0,[(1,1,6),(1,5,8)]),(7,[(1,1,12)]),(9,[(1,22,6)]),(0,[(1,4,5),(1,22,6)]),(1,[(1,4,5),(1,22,6)]),(0,[(1,4,6),(1,1,12)]),(1,[(1,4,6),(1,1,12)]),(0,[(1,4,6),(1,3,12)]),(1,[(1,4,6),(1,3,12)]),(0,[(1,4,6),(1,5,12)]),(1,[(1,4,6),(1,5,12)])]
def rootNBlock10_1Pools : BT (Option BoundPool) := buildPoolsBT 6 rootNW rootNR rootNSlices rootNBlock10_1Specs
def rootNBlock10_1 : List NodeSpec := [([0,1,2,3,4,5,6,8,23],[0,1,4,5,17,31],[0]),([0,1,2,3,4,5,6,10],[0,2,5,6,7,8],[]),([0,1,2,3,4,5,6,12,19],[1,2,5,12,13,32,36,37],[0]),([0,1,2,3,4,5,6,12,37],[1,2,8,12,27,38,39],[0,1]),([0,1,2,3,4,5,6,12,14],[1,11,12,17,27,40,41],[0,1]),([0,1,2,3,4,5,6,19],[1,2,5,10,12,13,14,15,16],[0]),([0,1,2,3,4,5,6,23],[0,1,5,11,17,23,24],[0]),([0,1,2,3,4,5,6,14],[11,12,17,28,33,34,35],[0,1]),([0,1,2,3,4,5,8,9],[0,2,3,5,8,25,26],[0]),([0,1,2,3,4,5,8,12],[1,2,5,9,12,29,30],[0]),([0,1,2,3,4,21,22,6],[0,11,19,20],[0]),([0,1,2,3,4,21,6,15],[0,11,17,18,21,22],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_1Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock10_1Pools rootNAutos rootNBucket9 10 rootNBlock10_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_1Mem : ∀ ns ∈ rootNBlock10_1, Impossible rootNG 10 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket9Ok rootNBlock10_1Ok
def rootNBlock10_2Specs : List PoolSpec := [(9,[]),(17,[]),(10,[]),(15,[]),(0,[(1,1,3),(1,1,6)]),(1,[(1,1,3),(1,1,6)]),(14,[]),(2,[(1,1,3)]),(0,[(1,1,4),(1,1,6)]),(1,[(1,1,4),(1,1,6)]),(2,[(1,1,4)]),(7,[]),(0,[(1,1,4),(1,4,6)]),(1,[(1,1,4),(1,4,6)]),(12,[]),(0,[(1,1,5),(1,1,6)]),(1,[(1,1,5),(1,1,6)]),(2,[(1,1,5)]),(2,[(1,4,5)]),(0,[(1,4,5),(1,4,6)]),(1,[(1,4,5),(1,4,6)])]
def rootNBlock10_2Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock10_2Specs
def rootNBlock10_2 : List NodeSpec := [([0,1,2,3,11,5,6,12],[2,10,11,12,13,14],[0]),([0,1,2,3,5,22,6,12],[2,11,14,18,19,20],[0,1]),([0,2,3,7,4,5,6,8],[0,2,3,4,5,6,7],[0]),([0,2,3,4,11,5,6,8],[1,2,6,8,9,10],[0]),([0,2,3,4,5,21,6,8],[0,1,6,11,15,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_2Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock10_2Pools rootNAutos rootNBucket9 10 rootNBlock10_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_2Mem : ∀ ns ∈ rootNBlock10_2, Impossible rootNG 10 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket9Ok rootNBlock10_2Ok
def rootNNodes10 : List NodeSpec := rootNBlock10_0 ++ rootNBlock10_1 ++ rootNBlock10_2
def rootNBucket10 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 10 xs.toFinset) rootNBucket10 := buildBucketsBT_of_mem (forall_append (forall_append rootNBlock10_0Mem rootNBlock10_1Mem) rootNBlock10_2Mem)
def rootNBlock11_0Specs : List PoolSpec := [(9,[]),(10,[]),(2,[]),(14,[]),(0,[(1,1,3)]),(1,[(1,1,3)]),(2,[(1,1,4)]),(7,[]),(12,[]),(0,[(1,1,4)]),(1,[(1,1,4)]),(2,[(1,1,5)]),(0,[(1,1,5)]),(1,[(1,1,5)]),(2,[(1,4,5)]),(0,[(1,1,6)]),(1,[(1,1,6)]),(6,[]),(0,[(1,4,5)]),(1,[(1,4,5)]),(0,[(1,4,6)]),(1,[(1,4,6)]),(4,[])]
def rootNBlock11_0Pools : BT (Option BoundPool) := buildPoolsBT 5 rootNW rootNR rootNSlices rootNBlock11_0Specs
def rootNBlock11_0 : List NodeSpec := [([0,1,2,3,7,4,5,6],[0,1,2,4,5],[0,1]),([0,1,2,3,4,11,5,6],[1,6,7,9,10],[0]),([0,1,2,3,4,5,21,6],[0,7,11,12,13],[0]),([0,1,2,3,4,5,22,6],[0,1,7,14,18,19],[0,1]),([0,1,2,3,4,5,6,8],[0,1,2,3,15,16,17],[0]),([0,1,2,3,4,5,6,12],[1,2,7,8,20,21,22],[0,1])]
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
def rootNBlock12_0Specs : List PoolSpec := [(2,[]),(6,[]),(4,[]),(0,[]),(1,[]),(3,[]),(5,[])]
def rootNBlock12_0Pools : BT (Option BoundPool) := buildPoolsBT 3 rootNW rootNR rootNSlices rootNBlock12_0Specs
def rootNBlock12_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5,6],[0,1])]
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

end Small
namespace Relate
def insertRow (r : Small.Row) : Wide.Row :=
  ⟨(0 + ((r.val / 1) % 2) * 1 + ((r.val / 2) % 2) * 2 + ((r.val / 4) % 2) * 4 + ((r.val / 8) % 2) * 8 + ((r.val / 16) % 2) * 16 + ((r.val / 32) % 2) * 32 + ((r.val / 64) % 2) * 128) % 256, Nat.mod_lt _ (by decide)⟩
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
lemma liftPins : Wide.Lower (Wide.varsOf 255) 0xfffffffffffffffefffffffffffffffefffffffefffffffefffefffafefeeca0 14 := by
  have bound : Wide.Lower (Wide.varsOf 191) 0xfffffffffffffffefffffffffffffffefffefffafefeeca0fffefffafefeeca0 13 := by
    intro n bank hr ha
    have proots : (((Wide.varsOf 191).map Wide.obs).map project) = (Small.varsOf 127).map Small.obs := by
      change [_,_,_,_,_,_,_] = [_,_,_,_,_,_,_]
      repeat' apply congrArg₂ List.cons
      all_goals first | rfl | funext r; revert r; decide +kernel
    have target : project (Wide.obs 0xfffffffffffffffefffffffffffffffefffefffafefeeca0fffefffafefeeca0) = Small.obs 0xfffffffffffffffefffefffafefeeca0 := by funext r; revert r; decide +kernel
    have r := reach hr
    have a := avail ha
    rw [proots] at r
    rw [target] at a
    exact Small.rootNBound n _ r a
  exact Wide.lift_of (z := 64) (o := 0) (essPairs := [(Wide.VAR 6,1,65)]) (by decide +kernel) bound
end Relate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def f (x : Fin 8 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)
def onWit : List Gate := [⟨.or, [0, 2]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [5, 10]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [12, 15]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [19, 21]⟩]

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
theorem onGraphCorrect : ∀ x : Fin 8 → Bool, f x = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

theorem onFinal :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfit _hone hev
  have hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y := fun y => (hev y).trans (onGraphCorrect y).symm
  have hrow : ∀ r : Wide.Row, f (Wide.evalInput r) = (0xfffffffffffffffefffffffffffffffefffffffefffffffefffefffafefeeca0 : Nat).testBit r.val := by decide +kernel
  have hw : ∀ r : Wide.Row, Circuit.eval ⟨onWit, 22⟩ (List.ofFn (Wide.evalInput r)) = (0xfffffffffffffffefffffffffffffffefffffffefffffffefffefffafefeeca0 : Nat).testBit r.val :=
    fun r => (onWitCorrect (Wide.evalInput r)).trans (hrow r)
  obtain ⟨gs, out, hg, hlen, hev⟩ := Wide.replace_of_lower (0xfffffffffffffffefffffffffffffffefffffffefffffffefffefffafefeeca0 : Nat) (by decide) (by decide) (by decide)
    14 Relate.liftPins onWit 22 (by decide) onWitBasis f hrow hw gates o hfit hf
  exact ⟨gs, out, hg, hlen, fun x => (hev x).trans (onGraphCorrect x)⟩
end PEqualNP.Outside.L_meta_52014

theorem PEqualNP.Outside.L_meta_52014 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_52014.onFinal
