import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace PEqualNP.Outside.L_clb_061_aux

open PEqualNP.CircuitLowerBounds

def evalW (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def depW (gs : List Gate) (n : ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1])
    (List.replicate n 0)

lemma evalW_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    evalW (gs ++ [g]) x =
      evalW gs x ++ [g.op.eval (g.inputs.map fun i => (evalW gs x).getD i false)] := by
  simp [evalW, List.foldl_append]

lemma depW_snoc (gs : List Gate) (g : Gate) (n : ℕ) :
    depW (gs ++ [g]) n =
      depW gs n ++ [(g.inputs.map fun i => (depW gs n).getD i 0).foldr max 0 + 1] := by
  simp [depW, List.foldl_append]

lemma evalW_length (gs : List Gate) (x : List Bool) :
    (evalW gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [evalW]
  | append_singleton gs g ih => rw [evalW_snoc]; simp [ih]; omega

lemma depW_length (gs : List Gate) (n : ℕ) : (depW gs n).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [depW]
  | append_singleton gs g ih => rw [depW_snoc]; simp [ih]; omega

lemma snoc_old {α : Type} (l : List α) (a d : α) (k : ℕ) (h : k < l.length) :
    (l ++ [a]).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma snoc_new {α : Type} (l : List α) (a d : α) (k : ℕ) (h : k = l.length) :
    (l ++ [a]).getD k d = a := by
  subst h
  simp [List.getD_eq_getElem?_getD]

lemma le_foldr_max (l : List ℕ) (a : ℕ) (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma foldr_max_le (l : List ℕ) (B : ℕ) (h : ∀ a ∈ l, a ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons b l ih =>
    exact max_le (h b List.mem_cons_self) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

def mapW (lit : ℕ → Bool ⊕ ℕ) (I N k : ℕ) : Bool ⊕ ℕ :=
  if k < I then lit k else Sum.inr (N + (k - I))

def tr (lit : ℕ → Bool ⊕ ℕ) (I N : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and =>
    if Sum.inl false ∈ g.inputs.map (mapW lit I N) then ⟨GateOp.or, []⟩
    else ⟨GateOp.and, (g.inputs.map (mapW lit I N)).filterMap Sum.getRight?⟩
  | _ =>
    if Sum.inl true ∈ g.inputs.map (mapW lit I N) then ⟨GateOp.and, []⟩
    else ⟨GateOp.or, (g.inputs.map (mapW lit I N)).filterMap Sum.getRight?⟩

def interp (v : List Bool) : Bool ⊕ ℕ → Bool :=
  Sum.elim id (fun w => v.getD w false)

lemma tr_eval (lit : ℕ → Bool ⊕ ℕ) (I N : ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (v : List Bool) :
    (tr lit I N g).op.eval ((tr lit I N g).inputs.map fun i => v.getD i false) =
      g.op.eval ((g.inputs.map (mapW lit I N)).map (interp v)) := by
  rcases g with ⟨op, ins⟩
  dsimp only at hg ⊢
  rcases hg with rfl | rfl
  · dsimp only [tr]
    generalize ins.map (mapW lit I N) = rs
    split
    · rename_i h
      symm
      show (rs.map (interp v)).all id = false
      rw [List.all_eq_false]
      exact ⟨false, List.mem_map.2 ⟨_, h, rfl⟩, by simp⟩
    · rename_i h
      show ((rs.filterMap Sum.getRight?).map fun i => v.getD i false).all id =
        (rs.map (interp v)).all id
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      constructor
      · intro H b hb
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hb
        rcases r with c | w
        · cases c
          · exact absurd hr h
          · rfl
        · exact H _ (List.mem_map.2 ⟨w, List.mem_filterMap.2 ⟨_, hr, rfl⟩, rfl⟩)
      · intro H b hb
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
        obtain ⟨r, hr, e⟩ := List.mem_filterMap.1 hw
        rw [Sum.getRight?_eq_some_iff] at e
        subst e
        exact H _ (List.mem_map.2 ⟨_, hr, rfl⟩)
  · dsimp only [tr]
    generalize ins.map (mapW lit I N) = rs
    split
    · rename_i h
      symm
      show (rs.map (interp v)).any id = true
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.2 ⟨_, h, rfl⟩, rfl⟩
    · rename_i h
      show ((rs.filterMap Sum.getRight?).map fun i => v.getD i false).any id =
        (rs.map (interp v)).any id
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨b, hb, hbt⟩
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
        obtain ⟨r, hr, e⟩ := List.mem_filterMap.1 hw
        rw [Sum.getRight?_eq_some_iff] at e
        subst e
        exact ⟨_, List.mem_map.2 ⟨_, hr, rfl⟩, hbt⟩
      · rintro ⟨b, hb, hbt⟩
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hb
        rcases r with c | w
        · cases c
          · simp [interp] at hbt
          · exact absurd hr h
        · exact ⟨_, List.mem_map.2 ⟨w, List.mem_filterMap.2 ⟨_, hr, rfl⟩, rfl⟩, hbt⟩

lemma tr_shape (lit : ℕ → Bool ⊕ ℕ) (I N : ℕ) (g : Gate) :
    ((tr lit I N g).op = GateOp.and ∨ (tr lit I N g).op = GateOp.or) ∧
      (tr lit I N g).inputs.length ≤ g.inputs.length ∧
      ∀ i ∈ (tr lit I N g).inputs, ∃ k ∈ g.inputs, mapW lit I N k = Sum.inr i := by
  have hlen : ((g.inputs.map (mapW lit I N)).filterMap Sum.getRight?).length ≤
      g.inputs.length :=
    le_trans (List.length_filterMap_le _ _) (by simp)
  have hmem : ∀ i ∈ (g.inputs.map (mapW lit I N)).filterMap Sum.getRight?,
      ∃ k ∈ g.inputs, mapW lit I N k = Sum.inr i := by
    intro i hi
    obtain ⟨r, hr, e⟩ := List.mem_filterMap.1 hi
    rw [Sum.getRight?_eq_some_iff] at e
    subst e
    exact List.mem_map.1 hr
  unfold tr
  split <;> split <;>
    first
    | exact ⟨Or.inl rfl, hlen, hmem⟩
    | exact ⟨Or.inr rfl, hlen, hmem⟩
    | exact ⟨Or.inl rfl, Nat.zero_le _, fun i hi => absurd hi List.not_mem_nil⟩
    | exact ⟨Or.inr rfl, Nat.zero_le _, fun i hi => absurd hi List.not_mem_nil⟩

lemma mapW_bound (lit : ℕ → Bool ⊕ ℕ) (I N : ℕ)
    (hlit : ∀ k w, lit k = Sum.inr w → w < N) (k m w : ℕ) (hk : k < I + m)
    (h : mapW lit I N k = Sum.inr w) : w < N + m := by
  unfold mapW at h
  split at h
  · have := hlit k w h
    omega
  · injection h with h
    omega

lemma sim_eval (lit : ℕ → Bool ⊕ ℕ) (I N : ℕ)
    (hlit : ∀ k w, lit k = Sum.inr w → w < N) (x y : List Bool) (hx : x.length = N)
    (hy : y.length = I) (hxy : ∀ k < I, y.getD k false = interp x (lit k)) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hrb : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < I + j) :
    ∀ k < I + gs.length,
      interp (evalW (gs.map (tr lit I N)) x) (mapW lit I N k) = (evalW gs y).getD k false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    have hk' : k < I := by simpa using hk
    simp only [mapW, if_pos hk']
    exact (hxy k hk').symm
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hm g' (List.mem_append_left _ hg')) (by
      intro j hj i hi
      refine hrb j (by simp; omega) i ?_
      rwa [snoc_old _ _ _ _ hj])
    intro k hk
    have hg : ∀ i ∈ g.inputs, i < I + gs.length := by
      intro i hi
      refine hrb gs.length (by simp) i ?_
      rwa [snoc_new _ _ _ _ rfl]
    rw [List.map_append, List.map_cons, List.map_nil, evalW_snoc, evalW_snoc]
    have lx : (evalW (gs.map (tr lit I N)) x).length = N + gs.length := by
      rw [evalW_length, hx, List.length_map]
    have ly : (evalW gs y).length = I + gs.length := by rw [evalW_length, hy]
    by_cases h : k < I + gs.length
    · rw [snoc_old (evalW gs y) _ _ k (by omega), ← ih' k h]
      cases e : mapW lit I N k with
      | inl b => rfl
      | inr w =>
        have := mapW_bound lit I N hlit k _ w h e
        exact snoc_old _ _ _ w (by omega)
    · have hk' : k = I + gs.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      have e : mapW lit I N k = Sum.inr (N + gs.length) := by
        rw [mapW, if_neg (by omega)]
        congr 1
        omega
      rw [e, snoc_new (evalW gs y) _ _ k (by omega)]
      show List.getD (_ ++ [_]) (N + gs.length) false = _
      rw [snoc_new _ _ _ _ lx.symm, tr_eval lit I N g (hm g (by simp)), List.map_map]
      congr 1
      exact List.map_congr_left fun i hi => ih' i (hg i hi)

lemma sim_depth (lit : ℕ → Bool ⊕ ℕ) (I N : ℕ)
    (hlit : ∀ k w, lit k = Sum.inr w → w < N) (gs : List Gate)
    (hrb : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < I + j) :
    ∀ k < I + gs.length, ∀ w, mapW lit I N k = Sum.inr w →
      (depW (gs.map (tr lit I N)) N).getD w 0 ≤ (depW gs I).getD k 0 := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk w e
    have hw : w < N := by simpa using mapW_bound lit I N hlit k 0 w (by simpa using hk) e
    simp [depW, List.getD_eq_getElem?_getD, hw]
  | append_singleton gs g ih =>
    have ih' := ih (by
      intro j hj i hi
      refine hrb j (by simp; omega) i ?_
      rwa [snoc_old _ _ _ _ hj])
    intro k hk w e
    have hg : ∀ i ∈ g.inputs, i < I + gs.length := by
      intro i hi
      refine hrb gs.length (by simp) i ?_
      rwa [snoc_new _ _ _ _ rfl]
    rw [List.map_append, List.map_cons, List.map_nil, depW_snoc, depW_snoc]
    have lx : (depW (gs.map (tr lit I N)) N).length = N + gs.length := by
      rw [depW_length, List.length_map]
    have ly : (depW gs I).length = I + gs.length := depW_length _ _
    by_cases h : k < I + gs.length
    · have := mapW_bound lit I N hlit k _ w h e
      rw [snoc_old (depW gs I) _ _ k (by omega), snoc_old _ _ _ w (by omega)]
      exact ih' k h w e
    · have hk' : k = I + gs.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      have hw : w = N + gs.length := by
        rw [mapW, if_neg (by omega)] at e
        injection e with e
        omega
      rw [snoc_new (depW gs I) _ _ k (by omega), snoc_new _ _ _ w (by omega)]
      refine Nat.add_le_add_right (foldr_max_le _ _ ?_) 1
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
      obtain ⟨j, hj, ej⟩ := (tr_shape lit I N g).2.2 i hi
      exact le_trans (ih' j (hg j hj) i ej)
        (le_foldr_max _ _ (List.mem_map.2 ⟨j, hj, rfl⟩))

def lo (d : ℕ) (g : Fin (d + d) → Bool) : ℕ :=
  Nat.ofBits fun k : Fin d => g ⟨k.val, by omega⟩

def hi (d : ℕ) (g : Fin (d + d) → Bool) : ℕ :=
  Nat.ofBits fun k : Fin d => g ⟨d + k.val, by omega⟩

def litOf (d s f p : ℕ) (g : Fin (d + d) → Bool) : Bool ⊕ ℕ :=
  if p % d ≠ 0 then Sum.inl true
  else if p / d + 1 = 2 ^ d then Sum.inl (decide (lo d g = f ∧ hi d g = s))
  else if lo d g = hi d g then Sum.inl true
  else Sum.inr (min (lo d g) (hi d g) * 2 ^ d + max (lo d g) (hi d g))

lemma litOf_bound (d s f p : ℕ) (g : Fin (d + d) → Bool) (w : ℕ)
    (h : litOf d s f p g = Sum.inr w) : w < 2 ^ d * 2 ^ d := by
  unfold litOf at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  injection h with h
  have h1 : lo d g < 2 ^ d := Nat.ofBits_lt_two_pow _
  have h2 : hi d g < 2 ^ d := Nat.ofBits_lt_two_pow _
  have h3 : min (lo d g) (hi d g) + 1 ≤ 2 ^ d := by omega
  have h4 : max (lo d g) (hi d g) < 2 ^ d := by omega
  have h5 := Nat.mul_le_mul_right (2 ^ d) h3
  rw [Nat.add_mul, one_mul] at h5
  omega

lemma reduction (d M n : ℕ) (hd : 0 < d) (hM : M = 2 ^ d) (hnM : n = M * d) (hn : 0 < n)
    (s f : Fin M) (x : List Bool) :
    (∃ word : Fin n → Bool, ∀ i : Fin n,
      interp x (litOf d s.val f.val i.val
        (fun k => word ⟨(i.val + k.val) % n, Nat.mod_lt _ hn⟩)) = true) ↔
    Relation.ReflTransGen
      (fun u v : Fin M => x.getD (min u.val v.val * M + max u.val v.val) false = true) s f := by
  have hM0 : 0 < M := by rw [hM]; exact Nat.two_pow_pos d
  have hbn : ∀ b < M, b * d < n := fun b hb => by
    rw [hnM]; exact Nat.mul_lt_mul_of_pos_right hb hd
  let blk : (Fin n → Bool) → ℕ → ℕ := fun word b =>
    Nat.ofBits fun k : Fin d => word ⟨(b * d + k.val) % n, Nat.mod_lt _ hn⟩
  have hblock : ∀ (word : Fin n → Bool) (b : ℕ),
      litOf d s.val f.val (b * d) (fun k => word ⟨(b * d + k.val) % n, Nat.mod_lt _ hn⟩) =
        if b + 1 = M then Sum.inl (decide (blk word b = f.val ∧ blk word (b + 1) = s.val))
        else if blk word b = blk word (b + 1) then Sum.inl true
        else Sum.inr (min (blk word b) (blk word (b + 1)) * M +
          max (blk word b) (blk word (b + 1))) := by
    intro word b
    have h1 : lo d (fun k => word ⟨(b * d + k.val) % n, Nat.mod_lt _ hn⟩) = blk word b := rfl
    have h2 : hi d (fun k => word ⟨(b * d + k.val) % n, Nat.mod_lt _ hn⟩) =
        blk word (b + 1) := by
      show Nat.ofBits _ = Nat.ofBits _
      refine congrArg Nat.ofBits (funext fun k => congrArg word (Fin.ext ?_))
      show (b * d + (d + k.val)) % n = ((b + 1) * d + k.val) % n
      rw [Nat.add_mul, one_mul, Nat.add_assoc]
    unfold litOf
    rw [h1, h2, Nat.mul_mod_left, Nat.mul_div_cancel _ hd, ← hM]
    simp
  have hwrap : ∀ word : Fin n → Bool, blk word M = blk word 0 := by
    intro word
    show Nat.ofBits _ = Nat.ofBits _
    refine congrArg Nat.ofBits (funext fun k => congrArg word (Fin.ext ?_))
    show (M * d + k.val) % n = (0 * d + k.val) % n
    rw [← hnM, Nat.zero_mul, Nat.zero_add, Nat.add_mod_left]
  constructor
  · rintro ⟨word, h⟩
    have hv : ∀ b, blk word b < M := fun b => by
      rw [hM]; exact Nat.ofBits_lt_two_pow _
    let v : ℕ → Fin M := fun b => ⟨blk word b, hv b⟩
    have hwin : ∀ b < M, interp x (if b + 1 = M then
          Sum.inl (decide (blk word b = f.val ∧ blk word (b + 1) = s.val))
        else if blk word b = blk word (b + 1) then Sum.inl true
        else Sum.inr (min (blk word b) (blk word (b + 1)) * M +
          max (blk word b) (blk word (b + 1)))) = true := by
      intro b hb
      rw [← hblock]
      exact h ⟨b * d, hbn b hb⟩
    have chain : ∀ b, b < M → Relation.ReflTransGen
        (fun u v : Fin M => x.getD (min u.val v.val * M + max u.val v.val) false = true)
        (v 0) (v b) := by
      intro b
      induction b with
      | zero => intro _; exact Relation.ReflTransGen.refl
      | succ b ih =>
        intro hb
        have hw := hwin b (by omega)
        rw [if_neg (by omega)] at hw
        by_cases e : blk word b = blk word (b + 1)
        · have : v (b + 1) = v b := Fin.ext e.symm
          rw [this]
          exact ih (by omega)
        · rw [if_neg e] at hw
          exact (ih (by omega)).tail hw
    have hlast := hwin (M - 1) (by omega)
    have e1 : M - 1 + 1 = M := by omega
    rw [if_pos e1, e1, hwrap] at hlast
    have hl : blk word (M - 1) = f.val ∧ blk word 0 = s.val := of_decide_eq_true hlast
    have h0 : v 0 = s := Fin.ext hl.2
    have h1 : v (M - 1) = f := Fin.ext hl.1
    have := chain (M - 1) (by omega)
    rwa [h0, h1] at this
  · intro h
    let G : SimpleGraph (Fin M) := SimpleGraph.fromRel
      (fun u v : Fin M => x.getD (min u.val v.val * M + max u.val v.val) false = true)
    have reach : ∀ t : Fin M, Relation.ReflTransGen
        (fun u v : Fin M => x.getD (min u.val v.val * M + max u.val v.val) false = true)
        s t → G.Reachable s t := by
      intro t ht
      induction ht with
      | refl => exact SimpleGraph.Reachable.refl _
      | @tail b c _ h2 ih =>
        by_cases hbc : b = c
        · exact hbc ▸ ih
        · have : G.Adj b c := ⟨hbc, Or.inl h2⟩
          exact ih.trans this.reachable
    have hr : G.Reachable s f := reach f h
    obtain ⟨p0⟩ := hr
    classical
    have hp : p0.bypass.length < M := by
      simpa using p0.bypass_isPath.length_lt
    let v : ℕ → Fin M := fun b => p0.bypass.getVert b
    let word : Fin n → Bool := fun q => (v (q.val / d)).val.testBit (q.val % d)
    have hblk : ∀ b < M, blk word b = (v b).val := by
      intro b hb
      have e : (fun k : Fin d => word ⟨(b * d + k.val) % n, Nat.mod_lt _ hn⟩) =
          fun k : Fin d => (v b).val.testBit k.val := by
        funext k
        have hlt : b * d + k.val < n := by
          have h5 := Nat.mul_le_mul_right d (show b + 1 ≤ M by omega)
          rw [Nat.add_mul, one_mul, ← hnM] at h5
          have := k.isLt
          omega
        have h1 : (b * d + k.val) / d = b := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt k.isLt,
            Nat.zero_add]
        have h2 : (b * d + k.val) % d = k.val := by
          rw [Nat.mul_add_mod', Nat.mod_eq_of_lt k.isLt]
        show (v (((b * d + k.val) % n) / d)).val.testBit (((b * d + k.val) % n) % d) = _
        rw [Nat.mod_eq_of_lt hlt, h1, h2]
      show Nat.ofBits _ = _
      rw [e, Nat.ofBits_testBit, ← hM]
      exact Nat.mod_eq_of_lt (v b).isLt
    refine ⟨word, fun i => ?_⟩
    by_cases h0 : i.val % d = 0
    · obtain ⟨b, hib⟩ : ∃ b, i.val = b * d :=
        ⟨i.val / d, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h0)).symm⟩
      have hbM : b < M := by
        have : b * d < M * d := by rw [← hib, ← hnM]; exact i.isLt
        exact Nat.lt_of_mul_lt_mul_right this
      have ew : (fun k : Fin (d + d) => word ⟨(i.val + k.val) % n, Nat.mod_lt _ hn⟩) =
          fun k : Fin (d + d) => word ⟨(b * d + k.val) % n, Nat.mod_lt _ hn⟩ := by
        funext k
        congr 1
        apply Fin.ext
        show (i.val + k.val) % n = (b * d + k.val) % n
        rw [hib]
      rw [ew, hib, hblock]
      split
      · rename_i hb1
        have e1 : v b = f := p0.bypass.getVert_of_length_le (by omega)
        have e2 : v 0 = s := p0.bypass.getVert_zero
        show decide _ = true
        rw [decide_eq_true_eq, hb1, hwrap, hblk b hbM, hblk 0 hM0, e1, e2]
        exact ⟨rfl, rfl⟩
      · rename_i hb1
        have hb2 : b + 1 < M := by omega
        rw [hblk b hbM, hblk (b + 1) hb2]
        split
        · rfl
        · rename_i hne
          have hlt : b < p0.bypass.length := by
            by_contra hc
            apply hne
            have e1 : v b = f := p0.bypass.getVert_of_length_le (by omega)
            have e2 : v (b + 1) = f := p0.bypass.getVert_of_length_le (by omega)
            rw [e1, e2]
          have hadj : G.Adj (v b) (v (b + 1)) := p0.bypass.adj_getVert_succ hlt
          rcases hadj.2 with h1 | h1
          · exact h1
          · rw [min_comm, max_comm] at h1
            exact h1
    · unfold litOf
      rw [if_pos h0]
      rfl

lemma core (d M n stride : ℕ) (hd : 0 < d) (hM : M = 2 ^ d) (hnM : n = M * d)
    (hst : stride = 2 ^ (d + d)) (hn : 0 < n) (s f : Fin M) (hsf : s ≠ f) (C : Circuit)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n * stride) C)
    (hout : C.output < n * stride + C.size)
    (hC : ∀ table : Fin n → (Fin (d + d) → Bool) → Bool,
        C.eval ((List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin stride =>
          table i (fun k => j.val.testBit k.val)))).flatten) = true ↔
        ∃ word : Fin n → Bool, ∀ i : Fin n,
          table i (fun k => word ⟨(i.val + k.val) % n, Nat.mod_lt _ hn⟩) = true) :
    ∃ D : Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (M * M) D ∧
      D.output < M * M + D.size ∧
      D.size ≤ C.size ∧ D.depth (M * M) ≤ C.depth (n * stride) ∧
      ∀ x : List Bool, x.length = M * M →
        (D.eval x = true ↔ Relation.ReflTransGen
          (fun u v : Fin M => x.getD (min u.val v.val * M + max u.val v.val) false = true)
          s f) := by
  have hst0 : 0 < stride := by rw [hst]; exact Nat.two_pow_pos _
  let lit : ℕ → Bool ⊕ ℕ := fun k =>
    litOf d s.val f.val (k / stride) (fun q => (k % stride).testBit q.val)
  have hlit : ∀ k w, lit k = Sum.inr w → w < M * M := by
    intro k w h
    rw [hM]
    exact litOf_bound _ _ _ _ _ _ h
  have hmono' : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    simpa using (hmono g hg).1
  have hrb' : ∀ j < C.gates.length,
      ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < n * stride + j := hrb
  have key : ∀ x : List Bool, x.length = M * M →
      (interp (evalW (C.gates.map (tr lit (n * stride) (M * M))) x)
          (mapW lit (n * stride) (M * M) C.output) = true ↔
        Relation.ReflTransGen
          (fun u v : Fin M => x.getD (min u.val v.val * M + max u.val v.val) false = true)
          s f) := by
    intro x hx
    let table : Fin n → (Fin (d + d) → Bool) → Bool := fun p g =>
      interp x (litOf d s.val f.val p.val g)
    have hy : (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin stride =>
          table i (fun k => j.val.testBit k.val)))).flatten =
        List.ofFn (fun k : Fin (n * stride) => interp x (lit k.val)) := by
      rw [List.ofFn_mul]
      congr 1
      apply congrArg List.ofFn
      funext i
      apply congrArg List.ofFn
      funext j
      have h1 : (i.val * stride + j.val) / stride = i.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hst0, Nat.div_eq_of_lt j.isLt,
          Nat.zero_add]
      have h2 : (i.val * stride + j.val) % stride = j.val := by
        rw [Nat.mul_add_mod', Nat.mod_eq_of_lt j.isLt]
      show interp x (litOf d s.val f.val i.val _) =
        interp x (litOf d s.val f.val ((i.val * stride + j.val) / stride)
          (fun q => ((i.val * stride + j.val) % stride).testBit q.val))
      rw [h1, h2]
    have h1 := sim_eval lit (n * stride) (M * M) hlit x
      (List.ofFn (fun k : Fin (n * stride) => interp x (lit k.val))) hx (by simp)
      (fun k hk => by simp [List.getD_eq_getElem?_getD, hk]) C.gates hmono' hrb' C.output hout
    rw [h1, ← hy]
    exact (hC table).trans (reduction d M n hd hM hnM hn s f x)
  have hwire : ∃ w, mapW lit (n * stride) (M * M) C.output = Sum.inr w := by
    cases e : mapW lit (n * stride) (M * M) C.output with
    | inr w => exact ⟨w, rfl⟩
    | inl b =>
      exfalso
      cases b
      · have h1 := (key (List.replicate (M * M) true) (by simp)).2
          (Relation.ReflTransGen.single (by
            have : min s.val f.val * M + max s.val f.val < M * M := by
              have h3 : min s.val f.val + 1 ≤ M := by omega
              have h4 : max s.val f.val < M := by omega
              have h5 := Nat.mul_le_mul_right M h3
              rw [Nat.add_mul, one_mul] at h5
              omega
            simp [List.getD_eq_getElem?_getD, this]))
        rw [e] at h1
        exact Bool.false_ne_true h1
      · have h1 := (key (List.replicate (M * M) false) (by simp)).1 (by rw [e]; rfl)
        rcases Relation.ReflTransGen.cases_tail h1 with h2 | ⟨c, _, h2⟩
        · exact hsf h2.symm
        · simp [List.getD_eq_getElem?_getD, List.getElem?_replicate] at h2
          split at h2 <;> simp at h2
  obtain ⟨w, hw⟩ := hwire
  refine ⟨⟨C.gates.map (tr lit (n * stride) (M * M)), w⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    have h := tr_shape lit (n * stride) (M * M) g'
    exact ⟨by simpa using h.1, le_trans h.2.1 (hmono g' hg').2⟩
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt
        ⟨C.gates.map (tr lit (n * stride) (M * M)), w⟩ j =
        tr lit (n * stride) (M * M) (C.gates.getD j ⟨GateOp.or, []⟩) := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj']
    rw [e] at hi
    obtain ⟨k, hk, ek⟩ := (tr_shape _ _ _ _).2.2 i hi
    exact mapW_bound lit _ _ hlit k j i (hrb' j hj' k hk) ek
  · show w < M * M + (C.gates.map _).length
    rw [List.length_map]
    exact mapW_bound lit _ _ hlit C.output _ w hout hw
  · show (C.gates.map _).length ≤ C.gates.length
    rw [List.length_map]
  · exact sim_depth lit _ _ hlit C.gates hrb' C.output hout w hw
  · intro x hx
    have h := key x hx
    rw [hw] at h
    exact h

end PEqualNP.Outside.L_clb_061_aux

theorem PEqualNP.Outside.L_clb_061 : (∀ (a : ℕ),
  let d := a + 1
  let M := 2 ^ d
  let n := M * d
  let stride := 2 ^ (d + d)
  let I := n * stride
  ∀ (hn : 0 < n) (s f : Fin M), s ≠ f →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack I C →
      C.output < I + C.size →
      (∀ table : Fin n → (Fin (d + d) → Bool) → Bool,
        let bits := (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin stride =>
          table i (fun k => j.val.testBit k.val)))).flatten
        C.eval bits = true ↔ ∃ word : Fin n → Bool, ∀ i : Fin n,
          table i (fun k => word ⟨(i.val + k.val) % n, Nat.mod_lt _ hn⟩) = true) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (M * M) D ∧
        D.output < M * M + D.size ∧
        D.size ≤ C.size ∧ D.depth (M * M) ≤ C.depth I ∧
        ∀ x : List Bool, x.length = M * M →
          let adj := fun u v : Fin M =>
            x.getD (min u.val v.val * M + max u.val v.val) false = true
          D.eval x = true ↔ Relation.ReflTransGen adj s f) := by
  intro a d M n stride I hn s f hsf C hmono hrb hout hC
  exact PEqualNP.Outside.L_clb_061_aux.core d M n stride (Nat.succ_pos a) rfl rfl rfl hn s f hsf C
    hmono hrb hout hC
