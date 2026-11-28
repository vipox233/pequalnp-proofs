import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1326

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open Classical

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepWire x

lemma wiresOf_nil (x : List Bool) : wiresOf [] x = x := rfl

lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) :=
  List.foldl_append

lemma wiresOf_singleton (g : Gate) (x : List Bool) :
    wiresOf [g] x = stepWire x g := rfl

lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresOf]
  | cons g gs ih =>
    change (wiresOf gs (stepWire x g)).length = x.length + (gs.length + 1)
    rw [ih]
    simp [stepWire]
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : Nat) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_eq_default_of_le {α : Type*} (l : List α) (i : Nat) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wiresOf_getD_prefix (gs : List Gate) (x : List Bool) (u : Nat) (hu : u < x.length) :
    (wiresOf gs x).getD u false = x.getD u false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have hlen : u < (stepWire x g).length := by
      simp [stepWire]
      omega
    change (wiresOf gs (stepWire x g)).getD u false = x.getD u false
    rw [ih (stepWire x g) hlen]
    exact getD_append_left x _ u false hu

lemma wiresOf_take_getD (gs : List Gate) (x : List Bool) (m u : Nat)
    (hm : m ≤ gs.length) (hu : u < x.length + m) :
    (wiresOf gs x).getD u false = (wiresOf (gs.take m) x).getD u false := by
  have hsplit : gs = gs.take m ++ gs.drop m := (List.take_append_drop m gs).symm
  conv_lhs => rw [hsplit, wiresOf_append]
  apply wiresOf_getD_prefix
  rw [wiresOf_length, List.length_take]
  omega

lemma gateAt_eq_getElem (C : Circuit) (j : Nat) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ hj

lemma take_succ_eq_append (C : Circuit) (m : Nat) (hm : m < C.gates.length) :
    C.gates.take (m + 1) = C.gates.take m ++ [gateAt C m] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some, gateAt_eq_getElem C m hm]

noncomputable def inp (n : Nat) (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun a : Fin n => decide (a ∈ x)) ++ [false, true]

lemma inp_length (n : Nat) (x : Finset (Fin n)) : (inp n x).length = n + 2 := by
  simp [inp]

lemma inp_getD_lt (n : Nat) (x : Finset (Fin n)) (u : Nat) (hu : u < n) :
    (inp n x).getD u false = true ↔ ⟨u, hu⟩ ∈ x := by
  have h1 : (inp n x).getD u false =
      (List.ofFn (fun a : Fin n => decide (a ∈ x))).getD u false := by
    unfold inp
    apply getD_append_left
    simp [hu]
  rw [h1]
  have hlen : u < (List.ofFn (fun a : Fin n => decide (a ∈ x))).length := by simp [hu]
  rw [List.getD_eq_getElem _ _ hlen]
  simp

lemma inp_getD_n (n : Nat) (x : Finset (Fin n)) : (inp n x).getD n false = false := by
  simp [inp, List.getD_eq_getElem?_getD]

lemma inp_getD_n1 (n : Nat) (x : Finset (Fin n)) : (inp n x).getD (n + 1) false = true := by
  simp [inp, List.getD_eq_getElem?_getD]

lemma inp_mono (n : Nat) {x y : Finset (Fin n)} (hxy : x ⊆ y) (u : Nat) :
    (inp n x).getD u false = true → (inp n y).getD u false = true := by
  by_cases h1 : u < n
  · rw [inp_getD_lt n x u h1, inp_getD_lt n y u h1]
    exact fun hx => hxy hx
  · by_cases h2 : u = n
    · subst h2
      rw [inp_getD_n]
      intro h; cases h
    · by_cases h3 : u = n + 1
      · subst h3
        intro _
        exact inp_getD_n1 n y
      · have hge : (inp n x).length ≤ u := by rw [inp_length]; omega
        rw [getD_eq_default_of_le _ _ _ hge]
        intro h; cases h

lemma gateOp_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (l : List Nat) (f g : Nat → Bool) (hfg : ∀ u, f u = true → g u = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro h a ha
    exact hfg a (h a ha)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    rintro ⟨a, ha, hfa⟩
    exact ⟨a, ha, hfg a hfa⟩

lemma wiresOf_mono (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool) (hlen : x.length = y.length)
    (hxy : ∀ u, x.getD u false = true → y.getD u false = true) :
    ∀ u, (wiresOf gs x).getD u false = true → (wiresOf gs y).getD u false = true := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := hM g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
    apply ih hgs (stepWire x g) (stepWire y g)
    · simp [stepWire, hlen]
    · intro u hu
      by_cases hlt : u < x.length
      · have hlty : u < y.length := hlen ▸ hlt
        rw [stepWire, getD_append_left x _ u false hlt] at hu
        rw [stepWire, getD_append_left y _ u false hlty]
        exact hxy u hu
      · by_cases heq : u = x.length
        · subst heq
          rw [stepWire, getD_append_right_eq] at hu
          rw [stepWire, hlen, getD_append_right_eq]
          exact gateOp_mono g.op hg g.inputs (fun i => x.getD i false) (fun i => y.getD i false) hxy hu
        · have hge : (stepWire x g).length ≤ u := by simp [stepWire]; omega
          rw [getD_eq_default_of_le _ _ _ hge] at hu
          cases hu

lemma monotone2_to_fanInTwo (C : Circuit) (hM : Monotone2 C) : FanInTwo C := by
  intro g hg
  rcases hM g hg with ⟨hop, hlen⟩
  refine ⟨?_, hlen⟩
  rcases hop with h | h
  · rw [h]; exact Or.inl rfl
  · rw [h]; exact Or.inr (Or.inl rfl)

noncomputable def wireVal (n : Nat) (C : Circuit) (x : Finset (Fin n)) (u : Nat) : Bool :=
  (C.wires (inp n x)).getD u false

lemma circuit_mono (n : Nat) (C : Circuit) (hM : Monotone2 C)
    {x y : Finset (Fin n)} (hxy : x ⊆ y) (u : Nat) :
    wireVal n C x u = true → wireVal n C y u = true := by
  apply wiresOf_mono C.gates (fun g hg => (hM g hg).1) (inp n x) (inp n y)
  · rw [inp_length, inp_length]
  · exact inp_mono n hxy

def variesOn {n : Nat} (C : Circuit) (S : Finset (Finset (Fin n))) (u : Nat) : Prop :=
  (∃ x ∈ S, wireVal n C x u = false) ∧ (∃ y ∈ S, wireVal n C y u = true)

noncomputable def rank (n : Nat) (C : Circuit) (S : Finset (Finset (Fin n))) (m : Nat) : Nat :=
  ((Finset.range m).filter (fun j => variesOn C S (n + 2 + j))).card

noncomputable def remap (n : Nat) (C : Circuit) (S : Finset (Finset (Fin n))) (u : Nat) : Nat :=
  if u < n + 2 then u
  else if u < n + 2 + C.size ∧ variesOn C S u then n + 2 + rank n C S (u - (n + 2))
  else if ∃ x ∈ S, wireVal n C x u = true then n + 1
  else n

noncomputable def localGates (n : Nat) (C : Circuit) (S : Finset (Finset (Fin n))) : Nat → List Gate
  | 0 => []
  | m + 1 =>
    if variesOn C S (n + 2 + m) then
      localGates n C S m ++ [⟨(gateAt C m).op, (gateAt C m).inputs.map (remap n C S)⟩]
    else
      localGates n C S m

lemma localGates_length (n : Nat) (C : Circuit) (S : Finset (Finset (Fin n))) (m : Nat) :
    (localGates n C S m).length = rank n C S m := by
  induction m with
  | zero => simp [localGates, rank]
  | succ m ih =>
    simp only [localGates, rank, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [List.length_append, List.length_singleton, ih,
        Finset.card_insert_of_notMem]
      · rfl
      · simp
    · exact ih

lemma rank_lt_of_varies (n : Nat) (C : Circuit) (S : Finset (Finset (Fin n)))
    {j m : Nat} (hjm : j < m) (hv : variesOn C S (n + 2 + j)) :
    rank n C S j < rank n C S m := by
  unfold rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, ?_, ?_⟩
    · simp [hjm, hv]
    · simp
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
    exact ⟨lt_trans hr.1 hjm, hr.2⟩

lemma remap_lt (n : Nat) (C : Circuit) (S : Finset (Finset (Fin n)))
    {m u : Nat} (_hm : m ≤ C.size) (hu : u < n + 2 + m) :
    remap n C S u < n + 2 + rank n C S m := by
  unfold remap
  split_ifs with h1 h2 h3
  · omega
  · have hjm : u - (n + 2) < m := by omega
    have heq : n + 2 + (u - (n + 2)) = u := by omega
    have hv : variesOn C S (n + 2 + (u - (n + 2))) := heq.symm ▸ h2.2
    have hlt := rank_lt_of_varies n C S hjm hv
    omega
  · omega
  · omega

lemma localGates_monotone2 (n : Nat) (C : Circuit) (S : Finset (Finset (Fin n)))
    (hM : Monotone2 C) (m : Nat) (hm : m ≤ C.size) :
    Monotone2 ⟨localGates n C S m, 0⟩ := by
  induction m with
  | zero =>
    intro g hg
    simp [localGates] at hg
  | succ m ih =>
    intro g hg
    simp only [localGates] at hg
    split_ifs at hg with h
    · rw [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact ih (by omega) g hg
      · have hmlt : m < C.gates.length := hm
        have hmem : gateAt C m ∈ C.gates := by
          rw [gateAt_eq_getElem C m hmlt]
          exact List.getElem_mem hmlt
        rcases hM (gateAt C m) hmem with ⟨hop, hlen⟩
        exact ⟨hop, by simp [hlen]⟩
    · exact ih (by omega) g hg

lemma localGates_readsBack (n : Nat) (C : Circuit) (S : Finset (Finset (Fin n)))
    (hRB : ReadsBack (n + 2) C) (m : Nat) (hm : m ≤ C.size) :
    ReadsBack (n + 2) ⟨localGates n C S m, 0⟩ := by
  induction m with
  | zero =>
    intro j hj
    simp [localGates] at hj
  | succ m ih =>
    intro j hj u hu
    simp only [localGates] at hj ⊢
    split_ifs at hj with hv
    · have hlg : localGates n C S (m + 1) =
          localGates n C S m ++ [⟨(gateAt C m).op, (gateAt C m).inputs.map (remap n C S)⟩] := by
        simp [localGates, hv]
      rw [hlg] at hu
      rw [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < (localGates n C S m).length
      · have hgate : gateAt ⟨localGates n C S m ++ [⟨(gateAt C m).op, (gateAt C m).inputs.map (remap n C S)⟩], 0⟩ j =
            gateAt ⟨localGates n C S m, 0⟩ j := by
          unfold gateAt
          exact getD_append_left (localGates n C S m) _ j _ hlt
        rw [hgate] at hu
        exact ih (by omega) j hlt u hu
      · have heq : j = (localGates n C S m).length := by omega
        subst heq
        have hgate : gateAt ⟨localGates n C S m ++ [⟨(gateAt C m).op, (gateAt C m).inputs.map (remap n C S)⟩], 0⟩
            (localGates n C S m).length =
            ⟨(gateAt C m).op, (gateAt C m).inputs.map (remap n C S)⟩ := by
          unfold gateAt
          exact getD_append_right_eq (localGates n C S m) _ _
        rw [hgate] at hu
        rcases List.mem_map.mp hu with ⟨r, hr, rfl⟩
        have hrlt : r < n + 2 + m := hRB m hm r hr
        rw [localGates_length]
        exact remap_lt n C S (by omega) hrlt
    · have hlg : localGates n C S (m + 1) = localGates n C S m := by simp [localGates, hv]
      rw [hlg] at hu
      exact ih (by omega) j hj u hu

lemma localGates_wires_eq (n : Nat) (C : Circuit) (S : Finset (Finset (Fin n)))
    (hRB : ReadsBack (n + 2) C) (x : Finset (Fin n)) (hx : x ∈ S)
    (m : Nat) (hm : m ≤ C.size) :
    ∀ u < n + 2 + m,
      (wiresOf (localGates n C S m) (inp n x)).getD (remap n C S u) false =
      (wiresOf (C.gates.take m) (inp n x)).getD u false := by
  induction m with
  | zero =>
    intro u hu
    have hu2 : u < n + 2 := by omega
    simp [localGates, remap, hu2, wiresOf]
  | succ m ih =>
    intro u hu
    have hmlt : m < C.gates.length := hm
    have htake : C.gates.take (m + 1) = C.gates.take m ++ [gateAt C m] :=
      take_succ_eq_append C m hmlt
    have hWorig_len : (wiresOf (C.gates.take m) (inp n x)).length = n + 2 + m := by
      rw [wiresOf_length, inp_length, List.length_take]
      omega
    have hWloc_len : (wiresOf (localGates n C S m) (inp n x)).length = n + 2 + rank n C S m := by
      rw [wiresOf_length, inp_length, localGates_length]
    by_cases hult : u < n + 2 + m
    · have hrem_lt : remap n C S u < (wiresOf (localGates n C S m) (inp n x)).length := by
        rw [hWloc_len]
        exact remap_lt n C S (by omega) hult
      have hrhs : (wiresOf (C.gates.take (m + 1)) (inp n x)).getD u false =
          (wiresOf (C.gates.take m) (inp n x)).getD u false := by
        rw [htake, wiresOf_append, wiresOf_singleton, stepWire]
        exact getD_append_left _ _ _ _ (by omega)
      rw [hrhs, ← ih (by omega) u hult]
      simp only [localGates]
      split_ifs with hv
      · rw [wiresOf_append, wiresOf_singleton, stepWire]
        exact getD_append_left _ _ _ _ hrem_lt
      · rfl
    · have hueq : u = n + 2 + m := by omega
      subst hueq
      simp only [localGates]
      split_ifs with hv
      · have hrem_eq : remap n C S (n + 2 + m) = n + 2 + rank n C S m := by
          unfold remap
          have hnot : ¬ (n + 2 + m < n + 2) := by omega
          have hlt2 : n + 2 + m < n + 2 + C.size := Nat.add_lt_add_left hmlt (n + 2)
          simp [hnot, hlt2, hv]
        rw [hrem_eq, wiresOf_append, wiresOf_singleton, stepWire, ← hWloc_len,
          getD_append_right_eq]
        rw [htake, wiresOf_append, wiresOf_singleton, stepWire, ← hWorig_len,
          getD_append_right_eq]
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro r hr
        exact ih (by omega) r (hRB m hmlt r hr)
      · have hval_eq : (wiresOf (C.gates.take (m + 1)) (inp n x)).getD (n + 2 + m) false =
            wireVal n C x (n + 2 + m) := by
          symm
          apply wiresOf_take_getD C.gates (inp n x) (m + 1) (n + 2 + m) hm
          rw [inp_length]
          omega
        rw [hval_eq]
        have hnot1 : ¬ (n + 2 + m < n + 2) := by omega
        by_cases hex : ∃ y ∈ S, wireVal n C y (n + 2 + m) = true
        · have hrem_eq : remap n C S (n + 2 + m) = n + 1 := by
            unfold remap
            simp [hnot1, hv, hex]
          rw [hrem_eq]
          have hpre : (wiresOf (localGates n C S m) (inp n x)).getD (n + 1) false = true := by
            rw [wiresOf_getD_prefix _ _ _ (by rw [inp_length]; omega), inp_getD_n1]
          rw [hpre]
          cases hcx : wireVal n C x (n + 2 + m)
          · exfalso
            exact hv ⟨⟨x, hx, hcx⟩, hex⟩
          · rfl
        · have hrem_eq : remap n C S (n + 2 + m) = n := by
            unfold remap
            simp [hnot1, hv, hex]
          rw [hrem_eq]
          have hpre : (wiresOf (localGates n C S m) (inp n x)).getD n false = false := by
            rw [wiresOf_getD_prefix _ _ _ (by rw [inp_length]; omega), inp_getD_n]
          rw [hpre]
          cases hcx : wireVal n C x (n + 2 + m)
          · rfl
          · exfalso
            exact hex ⟨x, hx, hcx⟩

lemma variesOn_disjoint {n k : Nat} (G : Fin k → Finset (Finset (Fin n)))
    (hmono : ∀ i j, i < j → ∀ x ∈ G i, ∀ y ∈ G j, x ⊆ y)
    (C : Circuit) (hM : Monotone2 C) {i j : Fin k} (hij : i ≠ j) (u : Nat) :
    ¬ (variesOn C (G i) u ∧ variesOn C (G j) u) := by
  rintro ⟨hi, hj⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rcases hi.2 with ⟨x, hx, hxt⟩
    rcases hj.1 with ⟨y, hy, hyf⟩
    have hyt := circuit_mono n C hM (hmono i j hlt x hx y hy) u hxt
    rw [hyf] at hyt
    cases hyt
  · rcases hj.2 with ⟨x, hx, hxt⟩
    rcases hi.1 with ⟨y, hy, hyf⟩
    have hyt := circuit_mono n C hM (hmono j i hgt x hx y hy) u hxt
    rw [hyf] at hyt
    cases hyt

lemma sum_rank_le (n k : Nat) (G : Fin k → Finset (Finset (Fin n)))
    (hmono : ∀ i j, i < j → ∀ x ∈ G i, ∀ y ∈ G j, x ⊆ y)
    (C : Circuit) (hM : Monotone2 C) :
    (∑ i : Fin k, rank n C (G i) C.size) ≤ C.size := by
  let V : Fin k → Finset Nat :=
    fun i => (Finset.range C.size).filter (fun j => variesOn C (G i) (n + 2 + j))
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k))) V := by
    intro i _ j _ hij
    change Disjoint (V i) (V j)
    rw [Finset.disjoint_left]
    intro r hri hrj
    simp only [V, Finset.mem_filter] at hri hrj
    exact variesOn_disjoint G hmono C hM hij (n + 2 + r) ⟨hri.2, hrj.2⟩
  have hsum : (∑ i : Fin k, (V i).card) = (Finset.univ.biUnion V).card :=
    (Finset.card_biUnion hdisj).symm
  have hsub : Finset.univ.biUnion V ⊆ Finset.range C.size := by
    rw [Finset.biUnion_subset]
    intro i _
    exact Finset.filter_subset _ _
  calc (∑ i : Fin k, rank n C (G i) C.size)
      = ∑ i : Fin k, (V i).card := rfl
    _ = (Finset.univ.biUnion V).card := hsum
    _ ≤ (Finset.range C.size).card := Finset.card_le_card hsub
    _ = C.size := Finset.card_range C.size

def shiftWire (m off u : Nat) : Nat :=
  if u < m then u else u + off

def shiftGate (m off : Nat) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftWire m off)⟩

def shiftGates (m off : Nat) (gs : List Gate) : List Gate :=
  gs.map (shiftGate m off)

lemma shiftWire_lt {m off u b : Nat} (hu : u < m + b) :
    shiftWire m off u < m + off + b := by
  unfold shiftWire
  split_ifs <;> omega

lemma shiftGates_length (m off : Nat) (gs : List Gate) :
    (shiftGates m off gs).length = gs.length :=
  List.length_map _

lemma shiftGates_wires (m off : Nat) (gs2 : List Gate)
    (hRB : ReadsBack m ⟨gs2, 0⟩) (x W1 : List Bool)
    (hx : x.length = m) (hW1len : W1.length = m + off)
    (hpre : ∀ u < m, W1.getD u false = x.getD u false) :
    ∀ u < m + gs2.length,
      (wiresOf (shiftGates m off gs2) W1).getD (shiftWire m off u) false =
      (wiresOf gs2 x).getD u false := by
  induction gs2 using List.reverseRecOn with
  | nil =>
    intro u hu
    have hu' : u < m := by simpa using hu
    simp [shiftGates, shiftWire, hu', wiresOf]
    exact hpre u hu'
  | append_singleton gs g ih =>
    have hRB_gs : ReadsBack m ⟨gs, 0⟩ := by
      intro j hj r hr
      dsimp only at hj
      have hgate : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        unfold gateAt
        exact getD_append_left gs [g] j _ hj
      have hj' : j < (gs ++ [g]).length := by simp; omega
      exact hRB j hj' r (hgate.symm ▸ hr)
    have hRB_g : ∀ r ∈ g.inputs, r < m + gs.length := by
      intro r hr
      have hgate : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        unfold gateAt
        exact getD_append_right_eq gs g _
      have hj' : gs.length < (gs ++ [g]).length := by simp
      exact hRB gs.length hj' r (hgate.symm ▸ hr)
    have hshift : shiftGates m off (gs ++ [g]) =
        shiftGates m off gs ++ [shiftGate m off g] := by
      simp [shiftGates]
    have hlen1 : (wiresOf (shiftGates m off gs) W1).length = m + off + gs.length := by
      rw [wiresOf_length, hW1len, shiftGates_length]
    have hlen2 : (wiresOf gs x).length = m + gs.length := by
      rw [wiresOf_length, hx]
    intro u hu
    rw [List.length_append, List.length_singleton] at hu
    rw [hshift, wiresOf_append, wiresOf_singleton, stepWire,
      wiresOf_append, wiresOf_singleton, stepWire]
    by_cases hult : u < m + gs.length
    · have hlt1 : shiftWire m off u < (wiresOf (shiftGates m off gs) W1).length := by
        rw [hlen1]
        exact shiftWire_lt hult
      rw [getD_append_left _ _ _ _ hlt1, getD_append_left _ _ _ _ (by omega)]
      exact ih hRB_gs u hult
    · have hueq : u = m + gs.length := by omega
      subst hueq
      have hsw : shiftWire m off (m + gs.length) = (wiresOf (shiftGates m off gs) W1).length := by
        rw [hlen1]
        unfold shiftWire
        have hnot : ¬ (m + gs.length < m) := by omega
        simp [hnot]
        omega
      rw [hsw, getD_append_right_eq, ← hlen2, getD_append_right_eq]
      congr 1
      simp only [shiftGate]
      rw [List.map_map]
      apply List.map_congr_left
      intro r hr
      exact ih hRB_gs r (hRB_g r hr)

lemma concat_monotone2 (m off : Nat) (C1 C2 : Circuit)
    (h1 : Monotone2 C1) (h2 : Monotone2 C2) :
    Monotone2 ⟨C1.gates ++ shiftGates m off C2.gates, 0⟩ := by
  intro g hg
  rw [List.mem_append] at hg
  rcases hg with hg | hg
  · exact h1 g hg
  · rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
    rcases h2 g0 hg0 with ⟨hop, hlen⟩
    exact ⟨hop, by simp [shiftGate, hlen]⟩

lemma concat_readsBack (m : Nat) (C1 C2 : Circuit)
    (h1 : ReadsBack m C1) (h2 : ReadsBack m C2) :
    ReadsBack m ⟨C1.gates ++ shiftGates m C1.size C2.gates, 0⟩ := by
  intro j hj u hu
  rw [List.length_append, shiftGates_length] at hj
  by_cases hlt : j < C1.gates.length
  · have hgate : gateAt ⟨C1.gates ++ shiftGates m C1.size C2.gates, 0⟩ j = gateAt C1 j := by
      unfold gateAt
      exact getD_append_left C1.gates _ j _ hlt
    rw [hgate] at hu
    exact h1 j hlt u hu
  · have hrlt : j - C1.gates.length < C2.gates.length := by omega
    have hgate : gateAt ⟨C1.gates ++ shiftGates m C1.size C2.gates, 0⟩ j =
        shiftGate m C1.size (gateAt C2 (j - C1.gates.length)) := by
      have hj' : j < (C1.gates ++ shiftGates m C1.size C2.gates).length := by
        rw [List.length_append, shiftGates_length]; omega
      rw [gateAt_eq_getElem _ j hj', List.getElem_append_right (by omega)]
      simp [shiftGates, gateAt_eq_getElem C2 _ hrlt]
    rw [hgate] at hu
    rcases List.mem_map.mp hu with ⟨r, hr, rfl⟩
    have hr' : r < m + (j - C1.gates.length) := h2 (j - C1.gates.length) hrlt r hr
    have hlt2 : shiftWire m C1.size r < m + C1.size + (j - C1.gates.length) := shiftWire_lt hr'
    change shiftWire m C1.size r < m + j
    have hsz : C1.size = C1.gates.length := rfl
    omega

lemma backward (n k t : Nat)
    (G : Fin k → Finset (Finset (Fin n)))
    (ok : Fin k → Finset (Fin n) → (Fin t → Bool) → Prop)
    (s : Fin k → Nat)
    (hloc : ∀ i : Fin k, ∃ (C : Circuit) (tap : Fin t → Nat),
      ((FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size) ∧
        (∀ a : Fin t, tap a < n + 2 + C.size) ∧
        (∀ x ∈ G i, ok i x (fun a => (C.wires (inp n x)).getD (tap a) false))) ∧
      Monotone2 C ∧ C.size ≤ s i) :
    ∃ (C : Circuit) (tap : Fin k → Fin t → Nat),
      (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size) ∧
      Monotone2 C ∧ C.size ≤ (∑ i, s i) ∧
      ∀ i : Fin k,
        (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size) ∧
        (∀ a : Fin t, tap i a < n + 2 + C.size) ∧
        (∀ x ∈ G i, ok i x (fun a => (C.wires (inp n x)).getD (tap i a) false)) := by
  induction k with
  | zero =>
    refine ⟨⟨[], 0⟩, fun i => Fin.elim0 i, ?_, ?_, ?_, fun i => Fin.elim0 i⟩
    · refine ⟨fun g hg => (by cases hg), fun j hj => (by cases hj), by simp [Circuit.size]⟩
    · intro g hg; cases hg
    · simp [Circuit.size]
  | succ k ih =>
    rcases ih (fun i => G i.castSucc) (fun i => ok i.castSucc) (fun i => s i.castSucc)
      (fun i => hloc i.castSucc) with
      ⟨C1, tap1, ⟨hF1, hRB1, hO1⟩, hM1, hS1, hfits1⟩
    rcases hloc (Fin.last k) with
      ⟨C2, tap2, ⟨⟨hF2, hRB2, hO2⟩, htap2, hok2⟩, hM2, hS2⟩
    let C : Circuit := ⟨C1.gates ++ shiftGates (n + 2) C1.size C2.gates, 0⟩
    let tap : Fin (k + 1) → Fin t → Nat :=
      Fin.lastCases (fun a => shiftWire (n + 2) C1.size (tap2 a)) tap1
    have hCsize : C.size = C1.size + C2.size := by
      simp [C, Circuit.size, shiftGates_length]
    have hMC : Monotone2 C := concat_monotone2 (n + 2) C1.size C1 C2 hM1 hM2
    have hFC : FanInTwo C := monotone2_to_fanInTwo C hMC
    have hRBC : ReadsBack (n + 2) C := concat_readsBack (n + 2) C1 C2 hRB1 hRB2
    have hOC : C.output < n + 2 + C.size := by simp [C]
    have hvalidC : FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size :=
      ⟨hFC, hRBC, hOC⟩
    refine ⟨C, tap, hvalidC, hMC, ?_, ?_⟩
    · rw [hCsize, Fin.sum_univ_castSucc]
      exact Nat.add_le_add hS1 hS2
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · refine ⟨hvalidC, ?_, ?_⟩
        · intro a
          simp only [tap, Fin.lastCases_last]
          rw [hCsize]
          have hlt := shiftWire_lt (m := n + 2) (off := C1.size) (htap2 a)
          omega
        · intro x hx
          simp only [tap, Fin.lastCases_last]
          have hfun : (fun a => (C.wires (inp n x)).getD (shiftWire (n + 2) C1.size (tap2 a)) false) =
              (fun a => (C2.wires (inp n x)).getD (tap2 a) false) := by
            funext a
            change (wiresOf (C1.gates ++ shiftGates (n + 2) C1.size C2.gates) (inp n x)).getD
              (shiftWire (n + 2) C1.size (tap2 a)) false =
              (wiresOf C2.gates (inp n x)).getD (tap2 a) false
            rw [wiresOf_append]
            apply shiftGates_wires (n + 2) C1.size C2.gates hRB2 (inp n x)
              (wiresOf C1.gates (inp n x)) (inp_length n x)
            · rw [wiresOf_length, inp_length]; rfl
            · intro u hu
              exact wiresOf_getD_prefix C1.gates (inp n x) u (by rw [inp_length]; exact hu)
            · exact htap2 a
          rw [hfun]
          exact hok2 x hx
      · intro j
        rcases hfits1 j with ⟨_, htapj, hokj⟩
        refine ⟨hvalidC, ?_, ?_⟩
        · intro a
          simp only [tap, Fin.lastCases_castSucc]
          rw [hCsize]
          have := htapj a
          omega
        · intro x hx
          simp only [tap, Fin.lastCases_castSucc]
          have hfun : (fun a => (C.wires (inp n x)).getD (tap1 j a) false) =
              (fun a => (C1.wires (inp n x)).getD (tap1 j a) false) := by
            funext a
            change (wiresOf (C1.gates ++ shiftGates (n + 2) C1.size C2.gates) (inp n x)).getD
              (tap1 j a) false =
              (wiresOf C1.gates (inp n x)).getD (tap1 j a) false
            rw [wiresOf_append]
            apply wiresOf_getD_prefix
            rw [wiresOf_length, inp_length]
            exact htapj a
          rw [hfun]
          exact hokj x hx

lemma inp_eq_ofFn_decide {n : Nat} (x : Finset (Fin n)) :
    List.ofFn (fun a : Fin n => @decide (a ∈ x) (Classical.propDecidable (a ∈ x))) ++ [false, true] = inp n x := by
  unfold inp
  congr 1
  congr 1
  funext a
  exact congrArg (@decide (a ∈ x)) (Subsingleton.elim _ _)

lemma wires_eq_wiresOf (C : Circuit) (x : List Bool) : C.wires x = wiresOf C.gates x := rfl

end PEqualNP.Outside.L_lib_1326

theorem PEqualNP.Outside.L_lib_1326 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n k t : Nat) (G : Fin k → Finset (Finset (Fin n)))
      (ok : Fin k → Finset (Fin n) → (Fin t → Bool) → Prop),
      (∀ i j, i < j → ∀ x ∈ G i, ∀ y ∈ G j, x ⊆ y) →
      let valid := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
        C.output < n+2+C.size
      let fits := fun (i : Fin k) (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat) =>
        valid C ∧ (∀ a, tap a < n+2+C.size) ∧ ∀ x ∈ G i,
          let w := C.wires (List.ofFn (fun a : Fin n => decide (a ∈ x)) ++ [false,true])
          ok i x (fun a => w.getD (tap a) false)
      let localFit := fun (i : Fin k) (s : Nat) =>
        ∃ C tap, fits i C tap ∧ PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s
      ∀ P : Nat,
        (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin k → Fin t → Nat),
          valid C ∧ PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ P ∧ ∀ i, fits i C (tap i)) ↔
        ∃ s : Fin k → Nat, (∑ i, s i) ≤ P ∧ ∀ i, localFit i (s i) := by
  intro n k t G ok hmono valid fits localFit P
  constructor
  · rintro ⟨C, tap, hvalid, hM, hP, hfits⟩
    refine ⟨fun i => PEqualNP.Outside.L_lib_1326.rank n C (G i) C.size, ?_, ?_⟩
    · exact le_trans (PEqualNP.Outside.L_lib_1326.sum_rank_le n k G hmono C hM) hP
    · intro i
      rcases hfits i with ⟨⟨hFC, hRBC, hOC⟩, htap, hok⟩
      let Ci : PEqualNP.CircuitLowerBounds.Circuit :=
        ⟨PEqualNP.Outside.L_lib_1326.localGates n C (G i) C.size, 0⟩
      let tapi : Fin t → Nat := fun a => PEqualNP.Outside.L_lib_1326.remap n C (G i) (tap i a)
      have hCi_size : Ci.size = PEqualNP.Outside.L_lib_1326.rank n C (G i) C.size :=
        PEqualNP.Outside.L_lib_1326.localGates_length n C (G i) C.size
      have hMi : PEqualNP.MetaComplexity.Monotone2 Ci :=
        PEqualNP.Outside.L_lib_1326.localGates_monotone2 n C (G i) hM C.size (le_refl _)
      have hFi : PEqualNP.MetaComplexity.FanInTwo Ci :=
        PEqualNP.Outside.L_lib_1326.monotone2_to_fanInTwo Ci hMi
      have hRBi : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) Ci :=
        PEqualNP.Outside.L_lib_1326.localGates_readsBack n C (G i) hRBC C.size (le_refl _)
      have hOi : Ci.output < n + 2 + Ci.size := by simp [Ci]
      refine ⟨Ci, tapi, ⟨⟨hFi, hRBi, hOi⟩, ?_, ?_⟩, hMi, le_of_eq hCi_size⟩
      · intro a
        rw [hCi_size]
        exact PEqualNP.Outside.L_lib_1326.remap_lt n C (G i) (le_refl _) (htap a)
      · intro x hx
        have hokx := hok x hx
        dsimp only at hokx ⊢
        rw [PEqualNP.Outside.L_lib_1326.inp_eq_ofFn_decide x] at hokx ⊢
        have hfun : (fun a => (Ci.wires (PEqualNP.Outside.L_lib_1326.inp n x)).getD (tapi a) false) =
            (fun a => (C.wires (PEqualNP.Outside.L_lib_1326.inp n x)).getD (tap i a) false) := by
          funext a
          rw [PEqualNP.Outside.L_lib_1326.wires_eq_wiresOf,
            PEqualNP.Outside.L_lib_1326.wires_eq_wiresOf]
          have heq := PEqualNP.Outside.L_lib_1326.localGates_wires_eq n C (G i) hRBC x hx C.size (le_refl _) (tap i a) (htap a)
          have htake : C.gates.take C.size = C.gates := List.take_length
          rw [htake] at heq
          exact heq
        rw [hfun]
        exact hokx
  · rintro ⟨s, hsP, hloc⟩
    have hloc' : ∀ i : Fin k, ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat),
        ((PEqualNP.MetaComplexity.FanInTwo C ∧
            PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
            C.output < n + 2 + C.size) ∧
          (∀ a : Fin t, tap a < n + 2 + C.size) ∧
          (∀ x ∈ G i, ok i x (fun a => (C.wires (PEqualNP.Outside.L_lib_1326.inp n x)).getD (tap a) false))) ∧
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s i := by
      intro i
      rcases hloc i with ⟨C, tap, ⟨hv, ht, hok⟩, hM, hsz⟩
      refine ⟨C, tap, ⟨hv, ht, ?_⟩, hM, hsz⟩
      intro x hx
      have hokx := hok x hx
      dsimp only at hokx
      rw [PEqualNP.Outside.L_lib_1326.inp_eq_ofFn_decide x] at hokx
      exact hokx
    rcases PEqualNP.Outside.L_lib_1326.backward n k t G ok s hloc' with
      ⟨C, tap, hvalid, hM, hCsz, hfits⟩
    refine ⟨C, tap, hvalid, hM, le_trans hCsz hsP, ?_⟩
    intro i
    rcases hfits i with ⟨hv, ht, hok⟩
    refine ⟨hv, ht, ?_⟩
    intro x hx
    dsimp only
    rw [PEqualNP.Outside.L_lib_1326.inp_eq_ofFn_decide x]
    exact hok x hx
