import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_787_aux

open PEqualNP.CircuitLowerBounds

def stp (x : List Bool) (g : Gate) : List Bool :=
  x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

def RecAt (gs : List Gate) (n : ℕ) (V : ℕ → Bool) (p : ℕ) : Prop :=
  ∀ g, gs[p]? = some g →
    V (n + p) = g.op.eval (g.inputs.map fun h => if h < n + p then V h else false)

theorem getD_out (x : List Bool) (w : ℕ) (hw : x.length ≤ w) : x.getD w false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hw]; rfl

theorem fold_spec : ∀ (gs : List Gate) (x : List Bool),
    (∀ w, w < x.length → (gs.foldl stp x).getD w false = x.getD w false) ∧
    (∀ p, RecAt gs x.length (fun w => (gs.foldl stp x).getD w false) p) ∧
    (∀ w, x.length + gs.length ≤ w → (gs.foldl stp x).getD w false = false)
  | [], x => by
    refine ⟨fun w _ => rfl, fun p g hg => by simp at hg, fun w hw => ?_⟩
    exact getD_out x w (by simpa using hw)
  | g :: gs, x => by
    obtain ⟨h1, h2, h3⟩ := fold_spec gs (stp x g)
    have hlen : (stp x g).length = x.length + 1 := by simp [stp]
    have hpre : ∀ w, w < x.length → (stp x g).getD w false = x.getD w false := by
      intro w hw
      simp only [stp, List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      rw [List.foldl_cons, h1 w (by omega), hpre w hw]
    · intro p g' hg'
      cases p with
      | zero =>
        simp only [List.length_cons, List.getElem?_cons_zero, Option.some.injEq] at hg'
        subst hg'
        simp only [List.foldl_cons, Nat.add_zero]
        rw [h1 x.length (by omega)]
        have hz : (stp x g).getD x.length false =
            g.op.eval (g.inputs.map fun i => x.getD i false) := by
          simp [stp, List.getD_eq_getElem?_getD]
        rw [hz]
        congr 1
        apply List.map_congr_left
        intro h _
        by_cases hh : h < x.length
        · simp only [hh, if_true]; rw [h1 h (by omega), hpre h hh]
        · simp only [hh, if_false]; exact getD_out x h (by omega)
      | succ q =>
        have := h2 q g' (by simpa using hg')
        rw [hlen] at this
        simp only [List.foldl_cons]
        have e : x.length + 1 + q = x.length + (q + 1) := by omega
        rw [e] at this
        exact this
    · intro w hw
      rw [List.foldl_cons]
      exact h3 w (by simp only [List.length_cons] at hw; omega)

noncomputable def used (g : Gate) : List ℕ :=
  @ite (List ℕ) (g.op = GateOp.not) (Classical.propDecidable _) (g.inputs.take 1) g.inputs

theorem eval_congr (g : Gate) (f1 f2 : ℕ → Bool) (h : ∀ u ∈ used g, f1 u = f2 u) :
    g.op.eval (g.inputs.map f1) = g.op.eval (g.inputs.map f2) := by
  by_cases hn : g.op = GateOp.not
  · have hu : used g = g.inputs.take 1 := by unfold used; rw [if_pos hn]
    rw [hn]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      rw [h a (by rw [hu, hi]; simp)]
  · have hu : used g = g.inputs := by unfold used; rw [if_neg hn]
    rw [List.map_congr_left (fun u hu' => h u (hu ▸ hu'))]

def Edge (gs : List Gate) (n : ℕ) (u w : ℕ) : Prop :=
  ∃ p g, gs[p]? = some g ∧ w = n + p ∧ u ∈ used g ∧ u < w

theorem dep (gs : List Gate) (n : ℕ) (V1 V2 : ℕ → Bool) (X : ℕ → Prop)
    (hin : ∀ w, w < n → ¬ X w → V1 w = V2 w)
    (hrec : ∀ p, p < gs.length → ¬ X (n + p) → RecAt gs n V1 p ∧ RecAt gs n V2 p)
    (hbig : ∀ w, n + gs.length ≤ w → ¬ X w → V1 w = V2 w) :
    ∀ w, V1 w ≠ V2 w → ∃ x, X x ∧ V1 x ≠ V2 x ∧ Relation.ReflTransGen (Edge gs n) x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hne
    by_cases hX : X w
    · exact ⟨w, hX, hne, .refl⟩
    rcases lt_or_ge w n with hw | hw
    · exact absurd (hin w hw hX) hne
    obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
    by_cases hp : p < gs.length
    swap
    · exact absurd (hbig _ (by omega) hX) hne
    obtain ⟨r1, r2⟩ := hrec p hp hX
    have hg : gs[p]? = some gs[p] := List.getElem?_eq_getElem hp
    rw [r1 _ hg, r2 _ hg] at hne
    by_contra hcon
    apply hne
    apply eval_congr
    intro u hu
    by_cases hlt : u < n + p
    · simp only [hlt, if_true]
      by_contra hne'
      obtain ⟨x, hx, hx2, hr⟩ := ih u hlt hne'
      exact hcon ⟨x, hx, hx2, hr.tail ⟨p, _, hg, rfl, hu, hlt⟩⟩
    · simp [hlt]


section graph

variable (gs : List Gate) (n : ℕ) {m : ℕ} (P : Finset (Fin m)) (out : Fin m → ℕ)

def Live (u : ℕ) : Prop := ∃ j ∈ P, Relation.ReflTransGen (Edge gs n) u (out j)

open Classical in
noncomputable def liveOut (u : ℕ) : Finset ℕ :=
  (Finset.range (n + gs.length)).filter (fun w => Live gs n P out w ∧ Edge gs n u w)

open Classical in
noncomputable def sinkOut (u : ℕ) : ℕ := (P.filter fun j => out j = u).card

def passing (u : ℕ) : Prop :=
  Live gs n P out u ∧ (liveOut gs n P out u).card = 1 ∧ sinkOut P out u = 0

open Classical in
noncomputable def nxt (u : ℕ) : ℕ :=
  if h : passing gs n P out u then Classical.choose (Finset.card_eq_one.mp h.2.1) else u

noncomputable def chain (i : ℕ) (k : ℕ) : ℕ := (nxt gs n P out)^[k] i

variable {gs n P out}

theorem edge_lt {u w : ℕ} (e : Edge gs n u w) : u < w := by
  obtain ⟨_, _, _, _, _, h⟩ := e; exact h

theorem rtg_le {u w : ℕ} (h : Relation.ReflTransGen (Edge gs n) u w) : u ≤ w := by
  induction h with
  | refl => exact le_rfl
  | tail _ e ih => exact le_trans ih (edge_lt e).le

theorem live_lt (hP : ∀ j ∈ P, out j < n + gs.length) {u : ℕ} (h : Live gs n P out u) :
    u < n + gs.length := by
  obtain ⟨j, hj, hr⟩ := h
  exact lt_of_le_of_lt (rtg_le hr) (hP j hj)

theorem live_of_edge {u w : ℕ} (hw : Live gs n P out w) (e : Edge gs n u w) :
    Live gs n P out u := by
  obtain ⟨j, hj, hr⟩ := hw
  exact ⟨j, hj, Relation.ReflTransGen.head e hr⟩

theorem mem_liveOut {u w : ℕ} :
    w ∈ liveOut gs n P out u ↔ w < n + gs.length ∧ Live gs n P out w ∧ Edge gs n u w := by
  unfold liveOut; simp

theorem od_pos (hP : ∀ j ∈ P, out j < n + gs.length) {u : ℕ} (h : Live gs n P out u) :
    1 ≤ (liveOut gs n P out u).card + sinkOut P out u := by
  obtain ⟨j, hj, hr⟩ := h
  rcases Relation.ReflTransGen.cases_head hr with h1 | ⟨c, e, hc⟩
  · have : 0 < sinkOut P out u := by
      unfold sinkOut
      apply Finset.card_pos.mpr
      exact ⟨j, by simp [hj, h1]⟩
    omega
  · have hcl : Live gs n P out c := ⟨j, hj, hc⟩
    have : 0 < (liveOut gs n P out u).card := by
      apply Finset.card_pos.mpr
      exact ⟨c, mem_liveOut.mpr ⟨live_lt hP hcl, hcl, e⟩⟩
    omega

theorem nxt_spec {u : ℕ} (h : passing gs n P out u) :
    liveOut gs n P out u = {nxt gs n P out u} := by
  unfold nxt
  rw [dif_pos h]
  exact Classical.choose_spec (Finset.card_eq_one.mp h.2.1)

theorem nxt_fix {u : ℕ} (h : ¬ passing gs n P out u) : nxt gs n P out u = u := by
  unfold nxt; rw [dif_neg h]

theorem passing_next {u : ℕ} (h : passing gs n P out u) :
    nxt gs n P out u < n + gs.length ∧ Live gs n P out (nxt gs n P out u) ∧
      Edge gs n u (nxt gs n P out u) := by
  have hm : nxt gs n P out u ∈ liveOut gs n P out u := by rw [nxt_spec h]; simp
  exact mem_liveOut.mp hm

theorem chain_succ (i k : ℕ) : chain gs n P out i (k + 1) = nxt gs n P out (chain gs n P out i k) := by
  unfold chain; rw [Function.iterate_succ_apply']

theorem chain_live {i : ℕ} (hi : Live gs n P out i) : ∀ k, Live gs n P out (chain gs n P out i k) := by
  intro k
  induction k with
  | zero => exact hi
  | succ k ih =>
    rw [chain_succ]
    by_cases hp : passing gs n P out (chain gs n P out i k)
    · exact (passing_next hp).2.1
    · rw [nxt_fix hp]; exact ih

theorem chain_fix {i k : ℕ} (h : ¬ passing gs n P out (chain gs n P out i k)) :
    ∀ t, chain gs n P out i (k + t) = chain gs n P out i k := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [← Nat.add_assoc, chain_succ, ih, nxt_fix h]

theorem chain_end (hP : ∀ j ∈ P, out j < n + gs.length) {i : ℕ} :
    ¬ passing gs n P out (chain gs n P out i (n + gs.length)) := by
  intro hW
  have hall : ∀ k, k ≤ n + gs.length → passing gs n P out (chain gs n P out i k) := by
    intro k hk
    by_contra hk'
    have := chain_fix hk' (n + gs.length - k)
    rw [show k + (n + gs.length - k) = n + gs.length by omega] at this
    rw [this] at hW
    exact hk' hW
  have hge : ∀ k, k ≤ n + gs.length → k ≤ chain gs n P out i k := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      rw [chain_succ]
      have h1 := ih (by omega)
      have h2 := edge_lt (passing_next (hall k (by omega))).2.2
      omega
  have h1 := hge _ le_rfl
  have h2 := live_lt hP hW.1
  omega

theorem chain_np (hP : ∀ j ∈ P, out j < n + gs.length) {i k : ℕ}
    (h : ¬ passing gs n P out (chain gs n P out i k)) :
    chain gs n P out i k = chain gs n P out i (n + gs.length) := by
  rcases le_total k (n + gs.length) with hk | hk
  · have := chain_fix h (n + gs.length - k)
    rw [show k + (n + gs.length - k) = n + gs.length by omega] at this
    exact this.symm
  · have := chain_fix (chain_end hP (i := i)) (k - (n + gs.length))
    rw [show n + gs.length + (k - (n + gs.length)) = k by omega] at this
    exact this

end graph


section count

variable {gs : List Gate} {n : ℕ} {m : ℕ} {P : Finset (Fin m)} {out : Fin m → ℕ}

noncomputable def costF (gs : List Gate) (n : ℕ) (p : Fin gs.length) : ℕ :=
  ((used (gs.get p)).toFinset.filter (fun h => h < n + p.val)).card - 1

open Classical in
noncomputable def LiveS (gs : List Gate) (n : ℕ) (P : Finset (Fin m)) (out : Fin m → ℕ) : Finset ℕ :=
  (Finset.range (n + gs.length)).filter (Live gs n P out)

open Classical in
noncomputable def Forks (gs : List Gate) (n : ℕ) (P : Finset (Fin m)) (out : Fin m → ℕ) : Finset ℕ :=
  (LiveS gs n P out).filter (fun u => 2 ≤ (liveOut gs n P out u).card + sinkOut P out u)

theorem mem_LiveS {u : ℕ} : u ∈ LiveS gs n P out ↔ u < n + gs.length ∧ Live gs n P out u := by
  unfold LiveS; simp

theorem count (hP : ∀ j ∈ P, out j < n + gs.length) :
    ((LiveS gs n P out).filter (· < n)).card + (Forks gs n P out).card ≤
      P.card + ∑ p : Fin gs.length, costF gs n p := by
  classical
  set S := LiveS gs n P out with hS
  have hod : ∀ u ∈ S, 1 ≤ (liveOut gs n P out u).card + sinkOut P out u :=
    fun u hu => od_pos hP (mem_LiveS.mp hu).2
  have A1 : S.card + (Forks gs n P out).card ≤
      ∑ u ∈ S, ((liveOut gs n P out u).card + sinkOut P out u) := by
    unfold Forks
    rw [← hS, Finset.card_filter, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u hu
    have := hod u hu
    split_ifs <;> omega
  have A2 : ∑ u ∈ S, ((liveOut gs n P out u).card + sinkOut P out u) =
      ∑ u ∈ S, (liveOut gs n P out u).card + ∑ u ∈ S, sinkOut P out u :=
    Finset.sum_add_distrib
  have A3 : ∑ u ∈ S, sinkOut P out u = P.card := by
    unfold sinkOut
    rw [Finset.card_eq_sum_card_fiberwise (f := out) (t := S)]
    intro j hj
    have hj' : j ∈ P := Finset.mem_coe.mp hj
    exact Finset.mem_coe.mpr (mem_LiveS.mpr ⟨hP j hj', ⟨j, hj', .refl⟩⟩)
  have A4 : ∀ u, liveOut gs n P out u = S.filter (fun w => Edge gs n u w) := by
    intro u; ext w
    rw [mem_liveOut, Finset.mem_filter, mem_LiveS]
    tauto
  have A5 : ∑ u ∈ S, (liveOut gs n P out u).card =
      ∑ w ∈ S, (S.filter (fun u => Edge gs n u w)).card := by
    simp_rw [A4, Finset.card_filter]
    exact Finset.sum_comm
  let cst : ℕ → ℕ := fun w =>
    if h : n ≤ w ∧ w - n < gs.length then costF gs n ⟨w - n, h.2⟩ else 0
  have A6 : ∀ w ∈ S, (S.filter (fun u => Edge gs n u w)).card ≤
      cst w + (if ¬ w < n then 1 else 0) := by
    intro w hw
    by_cases hwn : w < n
    · have : S.filter (fun u => Edge gs n u w) = ∅ := by
        apply Finset.filter_false_of_mem
        intro u _ e
        obtain ⟨p, g, _, hw', _, _⟩ := e
        omega
      rw [this]; simp
    · have hwW := (mem_LiveS.mp hw).1
      have hp : w - n < gs.length := by omega
      have hc : cst w = costF gs n ⟨w - n, hp⟩ := by
        simp only [cst]; rw [dif_pos ⟨by omega, hp⟩]
      rw [hc, if_pos hwn]
      have hsub : S.filter (fun u => Edge gs n u w) ⊆
          (used (gs.get ⟨w - n, hp⟩)).toFinset.filter (fun h => h < n + (w - n)) := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨p, g, hg, hw', hu', hlt⟩ := hu.2
        have hpe : p = w - n := by omega
        subst hpe
        have : g = gs.get ⟨w - n, hp⟩ := by
          rw [List.getElem?_eq_getElem hp] at hg
          simp only [Option.some.injEq] at hg
          rw [← hg]; rfl
        subst this
        rw [Finset.mem_filter, List.mem_toFinset]
        exact ⟨hu', by omega⟩
      have := Finset.card_le_card hsub
      unfold costF
      simp only at this ⊢
      omega
  have A7 : ∑ w ∈ S, (S.filter (fun u => Edge gs n u w)).card ≤
      ∑ w ∈ S, cst w + (S.filter (fun w => ¬ w < n)).card := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum A6
  have A8 : (S.filter (· < n)).card + (S.filter (fun w => ¬ w < n)).card = S.card :=
    Finset.card_filter_add_card_filter_not _
  have A9 : ∑ w ∈ S, cst w ≤ ∑ w ∈ Finset.range (n + gs.length), cst w :=
    Finset.sum_le_sum_of_subset (by
      intro u hu; exact Finset.mem_range.mpr (mem_LiveS.mp hu).1)
  have A10 : ∑ w ∈ Finset.range (n + gs.length), cst w = ∑ p : Fin gs.length, costF gs n p := by
    rw [Finset.sum_range_add]
    have z : ∑ x ∈ Finset.range n, cst x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [cst]
      rw [dif_neg (by simp at hx; omega)]
    rw [z, Nat.zero_add]
    rw [← Fin.sum_univ_eq_sum_range (fun x => cst (n + x))]
    apply Finset.sum_congr rfl
    intro p _
    simp only [cst]
    rw [dif_pos ⟨by omega, by simp⟩]
    congr 1
    ext
    simp
  omega

end count


section mainpart

abbrev Vf (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (gs.foldl stp x).getD w false

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (w : ℕ) :
    (List.ofFn f).getD w false = if h : w < n then f ⟨w, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem vspec (gs : List Gate) {n : ℕ} (v : Fin n → Bool) :
    (∀ w, w < n → Vf gs (List.ofFn v) w = (List.ofFn v).getD w false) ∧
    (∀ p, RecAt gs n (Vf gs (List.ofFn v)) p) ∧
    (∀ w, n + gs.length ≤ w → Vf gs (List.ofFn v) w = false) := by
  have := fold_spec gs (List.ofFn v)
  rw [List.length_ofFn] at this
  exact this

theorem forced_exists (gs : List Gate) {n : ℕ} (a : Fin n → Bool) (f : ℕ) (b : Bool)
    (hf : f < n + gs.length) :
    ∃ G : ℕ → Bool, G f = b ∧ (∀ w, w < n → w ≠ f → G w = (List.ofFn a).getD w false) ∧
      (∀ p, p < gs.length → n + p ≠ f → RecAt gs n G p) ∧
      (∀ w, n + gs.length ≤ w → w ≠ f → G w = false) := by
  by_cases hfn : f < n
  · let a' : Fin n → Bool := fun h => if h.val = f then b else a h
    obtain ⟨s1, s2, s3⟩ := vspec gs a'
    refine ⟨Vf gs (List.ofFn a'), ?_, ?_, fun p _ _ => s2 p, fun w hw _ => s3 w hw⟩
    · rw [s1 f hfn, ofFn_getD, dif_pos hfn]; simp [a']
    · intro w hw hne
      rw [s1 w hw, ofFn_getD, ofFn_getD, dif_pos hw, dif_pos hw]
      simp [a', hne]
  · obtain ⟨q, rfl⟩ : ∃ q, f = n + q := ⟨f - n, by omega⟩
    have hq : q < gs.length := by omega
    let gs' := gs.set q ⟨if b then GateOp.and else GateOp.or, []⟩
    have hl : gs'.length = gs.length := List.length_set
    obtain ⟨s1, s2, s3⟩ := vspec gs' a
    refine ⟨Vf gs' (List.ofFn a), ?_, ?_, ?_, ?_⟩
    · have hgq : gs'[q]? = some ⟨if b then GateOp.and else GateOp.or, []⟩ := by
        simp [gs', hq]
      rw [s2 q _ hgq]
      cases b <;> rfl
    · intro w hw _; exact s1 w hw
    · intro p _ hne g hg
      apply s2 p g
      have hqp : q ≠ p := by omega
      simp only [gs']
      rw [List.getElem?_set_ne hqp]
      exact hg
    · intro w hw _
      exact s3 w (by omega)

theorem bool_ne (x y : Bool) (h : x ≠ y) : x = !y := by
  cases x <;> cases y <;> simp_all

end mainpart

end PEqualNP.Outside.L_lib_787_aux

open PEqualNP.Outside.L_lib_787_aux in
theorem PEqualNP.Outside.L_lib_787 : ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (a : Fin n → Bool) (out : Fin m → ℕ),
  let value := fun (v : Fin n → Bool) (j : Fin m) =>
    (C.wires (List.ofFn v)).getD (out j) false
  let delta := fun i : Fin n => Finset.univ.filter (fun j : Fin m =>
    value (fun h => if h = i then !(a h) else a h) j ≠ value a j)
  let moved := Finset.univ.filter (fun i : Fin n => (delta i).Nonempty)
  let wide := (Finset.univ.image delta).filter (fun s => 2 ≤ s.card)
  let ports := Finset.univ.filter (fun j : Fin m => ∃ i : Fin n, j ∈ delta i)
  let cost := fun p : Fin C.gates.length =>
    let g := C.gates.get p
    let used := @ite (List ℕ) (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
      (Classical.propDecidable _) (g.inputs.take 1) g.inputs
    ((used.toFinset.filter (fun h => h < n + p.val)).card - 1)
  moved.card + wide.card ≤ ports.card + ∑ p, cost p := by
  intro n m C a out value delta moved wide ports cost
  classical
  let V0 : ℕ → Bool := Vf C.gates (List.ofFn a)
  let fl : Fin n → Fin n → Bool := fun i => fun h => if h = i then !(a h) else a h
  let Vi : Fin n → ℕ → Bool := fun i => Vf C.gates (List.ofFn (fl i))
  have hdel : ∀ i j, j ∈ delta i ↔ Vi i (out j) ≠ V0 (out j) := by
    intro i j
    simp only [delta, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  have hports : ∀ j, j ∈ ports ↔ ∃ i, j ∈ delta i := by
    intro j
    simp only [ports, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmoved : ∀ i, i ∈ moved ↔ (delta i).Nonempty := by
    intro i
    simp only [moved, Finset.mem_filter, Finset.mem_univ, true_and]
  have hwide : ∀ s, s ∈ wide ↔ (∃ i, delta i = s) ∧ 2 ≤ s.card := by
    intro s
    simp only [wide, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  have hcost : ∑ p, cost p = ∑ p, costF C.gates n p := rfl
  have spec0 : (∀ w, w < n → V0 w = (List.ofFn a).getD w false) ∧
      (∀ p, RecAt C.gates n V0 p) ∧
      (∀ w, n + C.gates.length ≤ w → V0 w = false) := vspec C.gates a
  obtain ⟨a1, a2, a3⟩ := spec0
  have spec_i : ∀ i, (∀ w, w < n → Vi i w = (List.ofFn (fl i)).getD w false) ∧
      (∀ p, RecAt C.gates n (Vi i) p) ∧
      (∀ w, n + C.gates.length ≤ w → Vi i w = false) := fun i => vspec C.gates (fl i)
  have hflipin : ∀ i w, w < n → w ≠ i.val →
      (List.ofFn (fl i)).getD w false = (List.ofFn a).getD w false := by
    intro i w hw hne
    rw [ofFn_getD, ofFn_getD, dif_pos hw, dif_pos hw]
    simp only [fl]
    rw [if_neg]
    intro h
    exact hne (congrArg Fin.val h)
  have hP : ∀ j ∈ ports, out j < n + C.gates.length := by
    intro j hj
    obtain ⟨i, hi⟩ := (hports j).mp hj
    rw [hdel] at hi
    by_contra hc
    push_neg at hc
    exact hi (by rw [(spec_i i).2.2 _ hc]; exact (a3 _ hc).symm)
  have hdep_i : ∀ i w, Vi i w ≠ V0 w → Relation.ReflTransGen (Edge C.gates n) i.val w := by
    intro i w hne
    obtain ⟨x, hx, _, hr⟩ := dep C.gates n (Vi i) V0 (· = i.val)
      (fun w hw hne => by rw [(spec_i i).1 w hw, a1 w hw]; exact hflipin i w hw hne)
      (fun p _ _ => ⟨(spec_i i).2.1 p, a2 p⟩)
      (fun w hw _ => by rw [(spec_i i).2.2 w hw, a3 w hw]) w hne
    subst hx
    exact hr
  have hlive_moved : ∀ i ∈ moved, Live C.gates n ports out i.val := by
    intro i hi
    obtain ⟨j, hj⟩ := (hmoved i).mp hi
    exact ⟨j, (hports j).mpr ⟨i, hj⟩, hdep_i i _ ((hdel i j).mp hj)⟩
  have hM : moved.card ≤ ((LiveS C.gates n ports out).filter (· < n)).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val)
    · intro i hi
      have hi' : i ∈ moved := by simpa using hi
      have hl := hlive_moved i hi'
      have : i.val ∈ (LiveS C.gates n ports out).filter (· < n) :=
        Finset.mem_filter.mpr ⟨mem_LiveS.mpr ⟨live_lt hP hl, hl⟩, i.isLt⟩
      simpa using this
    · intro i _ j _ h
      exact Fin.ext h
  let GG : ℕ → Bool → ℕ → Bool := fun f b =>
    if h : f < n + C.gates.length then Classical.choose (forced_exists C.gates a f b h)
    else fun _ => false
  have GGspec : ∀ f b, f < n + C.gates.length → (GG f b f = b ∧
      (∀ w, w < n → w ≠ f → GG f b w = (List.ofFn a).getD w false) ∧
      (∀ p, p < C.gates.length → n + p ≠ f → RecAt C.gates n (GG f b) p) ∧
      (∀ w, n + C.gates.length ≤ w → w ≠ f → GG f b w = false)) := by
    intro f b h
    simp only [GG, dif_pos h]
    exact Classical.choose_spec (forced_exists C.gates a f b h)
  have hV0G : ∀ f, f < n + C.gates.length → ∀ w, V0 w = GG f (V0 f) w := by
    intro f hf w
    by_contra hne
    obtain ⟨g1, g2, g3, g4⟩ := GGspec f (V0 f) hf
    obtain ⟨x, hx, hx2, _⟩ := dep C.gates n V0 (GG f (V0 f)) (· = f)
      (fun w hw hne => by rw [a1 w hw, g2 w hw hne])
      (fun p hp hne => ⟨a2 p, g3 p hp hne⟩)
      (fun w hw hne => by rw [a3 w hw, g4 w hw hne]) w hne
    subst hx
    exact hx2 g1.symm
  have hGG : ∀ f b b', f < n + C.gates.length → ∀ w, GG f b w ≠ GG f b' w →
      Relation.ReflTransGen (Edge C.gates n) f w := by
    intro f b b' hf w hne
    obtain ⟨g1, g2, g3, g4⟩ := GGspec f b hf
    obtain ⟨h1, h2, h3, h4⟩ := GGspec f b' hf
    obtain ⟨x, hx, _, hr⟩ := dep C.gates n (GG f b) (GG f b') (· = f)
      (fun w hw hne => by rw [g2 w hw hne, h2 w hw hne])
      (fun p hp hne => ⟨g3 p hp hne, h3 p hp hne⟩)
      (fun w hw hne => by rw [g4 w hw hne, h4 w hw hne]) w hne
    subst hx
    exact hr
  let fk : Fin n → ℕ := fun i => chain C.gates n ports out i.val (n + C.gates.length)
  have hkey : ∀ i ∈ moved, ∀ w, Live C.gates n ports out w →
      (∀ k, chain C.gates n ports out i.val k = w → ¬ passing C.gates n ports out w) →
      Vi i w = GG (fk i) (Vi i (fk i)) w := by
    intro i hi w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hnc
      have hfW : fk i < n + C.gates.length := live_lt hP (chain_live (hlive_moved i hi) _)
      obtain ⟨g1, g2, g3, g4⟩ := GGspec (fk i) (Vi i (fk i)) hfW
      by_cases hwf : w = fk i
      · rw [hwf, g1]
      have hwW := live_lt hP hw
      by_cases hwn : w < n
      · rw [(spec_i i).1 w hwn, g2 w hwn hwf]
        apply hflipin i w hwn
        intro hwi
        apply hwf
        have h0 : chain C.gates n ports out i.val 0 = w := by
          simp [chain, hwi]
        have := chain_np hP (i := i.val) (k := 0) (by rw [h0]; exact hnc 0 h0)
        rw [h0] at this
        exact this
      · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
        have hpl : p < C.gates.length := by omega
        have hg := List.getElem?_eq_getElem hpl
        rw [(spec_i i).2.1 p _ hg, g3 p hpl hwf _ hg]
        apply eval_congr
        intro u hu
        by_cases hlt : u < n + p
        · simp only [hlt, if_true]
          have e : Edge C.gates n u (n + p) := ⟨p, _, hg, rfl, hu, hlt⟩
          have hul := live_of_edge hw e
          apply ih u hlt hul
          intro k hk hpass
          have hm : n + p ∈ liveOut C.gates n ports out u := mem_liveOut.mpr ⟨hwW, hw, e⟩
          subst hk
          rw [nxt_spec hpass, Finset.mem_singleton, ← chain_succ] at hm
          apply hwf
          rw [hm]
          exact chain_np hP (by rw [← hm]; exact hnc (k + 1) hm.symm)
        · simp [hlt]
  have hport_np : ∀ j ∈ ports, ¬ passing C.gates n ports out (out j) := by
    intro j hj hp
    have h0 := hp.2.2
    unfold sinkOut at h0
    have hm : j ∈ ports.filter (fun j' => out j' = out j) := Finset.mem_filter.mpr ⟨hj, rfl⟩
    rw [Finset.card_eq_zero.mp h0] at hm
    simp at hm
  let Δ : ℕ → Finset (Fin m) := fun f =>
    Finset.univ.filter (fun j => j ∈ ports ∧ GG f (!(V0 f)) (out j) ≠ V0 (out j))
  have hwide_i : ∀ i, 2 ≤ (delta i).card →
      fk i ∈ Forks C.gates n ports out ∧ delta i = Δ (fk i) := by
    intro i h2
    have hne : (delta i).Nonempty := Finset.card_pos.mp (by omega)
    have hi : i ∈ moved := (hmoved i).mpr hne
    have hil := hlive_moved i hi
    have hfl : Live C.gates n ports out (fk i) := chain_live hil _
    have hfW := live_lt hP hfl
    have hfnp : ¬ passing C.gates n ports out (fk i) := chain_end hP
    have hout : ∀ j ∈ ports, Vi i (out j) = GG (fk i) (Vi i (fk i)) (out j) :=
      fun j hj => hkey i hi (out j) ⟨j, hj, .refl⟩ (fun _ _ => hport_np j hj)
    have hb : Vi i (fk i) = !(V0 (fk i)) := by
      obtain ⟨j, hj⟩ := hne
      have hj' := (hdel i j).mp hj
      have hjp : j ∈ ports := (hports j).mpr ⟨i, hj⟩
      apply bool_ne
      intro heq
      apply hj'
      rw [hout j hjp, heq, ← hV0G _ hfW]
    have hdeq : delta i = Δ (fk i) := by
      ext j
      rw [hdel]
      simp only [Δ, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        have hjp : j ∈ ports := (hports j).mpr ⟨i, (hdel i j).mpr h⟩
        refine ⟨hjp, ?_⟩
        rw [← hb, ← hout j hjp]
        exact h
      · rintro ⟨hjp, h⟩
        rw [hout j hjp, hb]
        exact h
    refine ⟨?_, hdeq⟩
    unfold Forks
    rw [Finset.mem_filter, mem_LiveS]
    refine ⟨⟨hfW, hfl⟩, ?_⟩
    by_contra hlt
    push_neg at hlt
    have h1 := od_pos hP hfl
    have hlo : (liveOut C.gates n ports out (fk i)).card = 0 := by
      by_contra h0
      exact hfnp ⟨hfl, by omega, by omega⟩
    have hsub : delta i ⊆ ports.filter (fun j => out j = fk i) := by
      intro j hj
      have hjp : j ∈ ports := (hports j).mpr ⟨i, hj⟩
      have h' := (hdel i j).mp hj
      rw [hout j hjp, hV0G _ hfW (out j)] at h'
      have hr := hGG (fk i) _ _ hfW (out j) h'
      rw [Finset.mem_filter]
      refine ⟨hjp, ?_⟩
      rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, e, hc⟩
      · exact h.symm
      · exfalso
        have hcl : Live C.gates n ports out c := ⟨j, hjp, hc⟩
        have hm : c ∈ liveOut C.gates n ports out (fk i) :=
          mem_liveOut.mpr ⟨live_lt hP hcl, hcl, e⟩
        rw [Finset.card_eq_zero.mp hlo] at hm
        simp at hm
    have hs : sinkOut ports out (fk i) = (ports.filter (fun j => out j = fk i)).card := by
      unfold sinkOut
      congr 1
    have := Finset.card_le_card hsub
    omega
  have hWd : wide.card ≤ (Forks C.gates n ports out).card := by
    have hsub : wide ⊆ (Forks C.gates n ports out).image Δ := by
      intro s hs
      rw [hwide] at hs
      obtain ⟨⟨i, rfl⟩, h2⟩ := hs
      obtain ⟨hf, hd⟩ := hwide_i i h2
      rw [Finset.mem_image]
      exact ⟨fk i, hf, hd.symm⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hC := count (gs := C.gates) (n := n) (P := ports) (out := out) hP
  rw [hcost]
  omega
