import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33668

variable {α : Type} [Fintype α] [DecidableEq α]

def IsM (M : Finset (Finset α)) : Prop :=
  (∀ e ∈ M, e.card = 2) ∧ (∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g)

theorem IsM.mono {M N : Finset (Finset α)} (valid : IsM M) (sub : N ⊆ M) : IsM N :=
  ⟨fun edge member => valid.1 edge (sub member), fun edge member other included => valid.2 edge (sub member) other (sub included)⟩

theorem isM_empty : IsM (∅ : Finset (Finset α)) := ⟨by simp, by simp⟩
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_run (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) :=
  List.foldl_append

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) : run (g :: gs) w = run gs (step w g) := rfl

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih]; simp [step]; omega

theorem getD_keep (w t : List Bool) {i : ℕ} (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_new (w : List Bool) (v : Bool) {i : ℕ} (hi : i = w.length) :
    (w ++ [v]).getD i false = v := by
  subst hi
  simp [List.getD_eq_getElem?_getD]

theorem prefix_keep (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp [step]; omega)]
    exact getD_keep _ _ hi

def value (C : Circuit) (x : List Bool) (i : ℕ) := (C.wires x).getD i false

theorem value_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    value C x (x.length + j) =
      (C.gates[j]).op.eval
        ((C.gates[j]).inputs.map fun i => if i < x.length + j then value C x i else false) := by
  let gs := C.gates
  let w := run (gs.take j) x
  have hlen : w.length = x.length + j := by
    simp only [w, run_length, gs, List.length_take, Nat.min_eq_left hj.le]
  have hs : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    simp [gs, List.take_append_drop]
  have hrun : C.wires x = run (gs.drop (j + 1)) (step w gs[j]) := by
    change run gs x = _
    conv_lhs => rw [hs, run_append, run_cons]
  have hread (i : ℕ) (hi : i < w.length) : value C x i = w.getD i false := by
    change (run gs x).getD i false = _
    conv_lhs => rw [← List.take_append_drop j gs, run_append]
    exact prefix_keep _ _ hi
  unfold value
  conv_lhs => rw [hrun]
  rw [prefix_keep _ _ (by simp [step, hlen])]
  rw [← hlen]
  simp only [step]
  rw [getD_new _ _ rfl]
  apply congrArg _
  apply List.map_congr_left
  intro i _
  split
  · rename_i hi
    exact (hread i hi).symm
  · rename_i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.2 (by omega : w.length ≤ i)]

section tree

variable (C : Circuit) (n : ℕ)

def gateAt (w : ℕ) : Gate := C.gates.getD (w - n) ⟨GateOp.and, []⟩

def isNot (w : ℕ) : Prop := n ≤ w ∧ (gateAt C n w).op = GateOp.not

open Classical in
noncomputable def reads (w : ℕ) : List ℕ :=
  if (gateAt C n w).op = GateOp.not then (gateAt C n w).inputs.take 1 else (gateAt C n w).inputs

noncomputable def ch (w : ℕ) : List ℕ :=
  if n ≤ w ∧ w - n < C.gates.length then (reads C n w).filter (fun c => decide (c < w)) else []

theorem ch_lt {w c : ℕ} (h : c ∈ ch C n w) : c < w := by
  unfold ch at h
  split at h
  · simpa using (List.mem_filter.1 h).2
  · simp at h

theorem ch_ge {w c : ℕ} (h : c ∈ ch C n w) : n ≤ w := by
  unfold ch at h
  split at h
  · rename_i h'
    exact h'.1
  · simp at h

noncomputable def desc (w : ℕ) : Finset ℕ :=
  insert w ((ch C n w).toFinset.attach.biUnion fun c => desc c.1)
termination_by w
decreasing_by exact ch_lt C n (List.mem_toFinset.mp c.2)

theorem mem_desc (w v : ℕ) : v ∈ desc C n w ↔ v = w ∨ ∃ c ∈ ch C n w, v ∈ desc C n c := by
  conv_lhs => rw [desc]
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists,
    List.mem_toFinset, exists_prop]

theorem self_desc (w : ℕ) : w ∈ desc C n w := (mem_desc C n w w).2 (Or.inl rfl)

theorem desc_le : ∀ w v, v ∈ desc C n w → v ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    rcases (mem_desc C n w v).1 hv with rfl | ⟨c, hc, h⟩
    · exact le_rfl
    · exact (ih c (ch_lt C n hc) v h).trans (ch_lt C n hc).le

theorem desc_trans : ∀ w v, v ∈ desc C n w → desc C n v ⊆ desc C n w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    rcases (mem_desc C n w v).1 hv with rfl | ⟨c, hc, h⟩
    · exact Finset.Subset.refl _
    · intro u hu
      exact (mem_desc C n w u).2 (Or.inr ⟨c, hc, ih c (ch_lt C n hc) v h hu⟩)

theorem desc_parent : ∀ w v, v ∈ desc C n w → v ≠ w → ∃ p ∈ desc C n w, v ∈ ch C n p := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv hne
    rcases (mem_desc C n w v).1 hv with rfl | ⟨c, hc, h⟩
    · exact absurd rfl hne
    · by_cases hvc : v = c
      · exact ⟨w, self_desc C n w, hvc ▸ hc⟩
      · obtain ⟨p, hp, hvp⟩ := ih c (ch_lt C n hc) v h hvc
        exact ⟨p, (mem_desc C n w p).2 (Or.inr ⟨c, hc, hp⟩), hvp⟩

theorem child_desc {o p c : ℕ} (hp : p ∈ desc C n o) (hc : c ∈ ch C n p) : c ∈ desc C n o :=
  desc_trans C n o p hp ((mem_desc C n p c).2 (Or.inr ⟨c, hc, self_desc C n c⟩))

def GoodC : Prop := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem gateAt_eq {w : ℕ} (h : w - n < C.gates.length) : gateAt C n w = C.gates[w - n] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

open Classical in
noncomputable def bnd (w : ℕ) : ℕ := if isNot C n w then 1 else 2

theorem ch_len (hg : GoodC C) {w : ℕ} (hw : n ≤ w) : (ch C n w).length ≤ bnd C n w := by
  classical
  unfold ch bnd
  split
  · rename_i h
    refine (List.length_filter_le _ _).trans ?_
    unfold reads
    have hg' : (gateAt C n w).inputs.length ≤ 2 := by
      rw [gateAt_eq C n h.2]
      exact (hg _ (List.getElem_mem h.2)).2
    by_cases hn : (gateAt C n w).op = GateOp.not
    · rw [if_pos hn, if_pos (show isNot C n w from ⟨hw, hn⟩), List.length_take]
      omega
    · rw [if_neg hn, if_neg (show ¬ isNot C n w from fun c => hn c.2)]
      exact hg'
  · simp

noncomputable def gatesIn (o : ℕ) : Finset ℕ := (desc C n o).filter (fun w => n ≤ w)
noncomputable def leaves (o : ℕ) : Finset ℕ := (desc C n o).filter (fun w => w < n)
open Classical in
noncomputable def nots (o : ℕ) : Finset ℕ := (desc C n o).filter (fun w => isNot C n w)

open Classical in
theorem sum_bnd (o : ℕ) : ∑ p ∈ gatesIn C n o, bnd C n p + (nots C n o).card = 2 * (gatesIn C n o).card := by
  have h1 : nots C n o = (gatesIn C n o).filter (fun w => isNot C n w) := by
    unfold nots gatesIn
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro w _
    exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩
  rw [h1, Finset.card_filter, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro p _
  unfold bnd
  split <;> rfl

theorem leaves_gates (o : ℕ) : (leaves C n o).card + (gatesIn C n o).card = (desc C n o).card := by
  unfold leaves gatesIn
  have := Finset.card_filter_add_card_filter_not (s := desc C n o) (fun w => w < n)
  simpa only [not_lt] using this

theorem parent_cover (o : ℕ) : (desc C n o).erase o ⊆ (gatesIn C n o).biUnion (fun p => (ch C n p).toFinset) := by
  intro v hv
  rw [Finset.mem_erase] at hv
  obtain ⟨p, hp, hvp⟩ := desc_parent C n o v hv.2 hv.1
  rw [Finset.mem_biUnion]
  exact ⟨p, Finset.mem_filter.2 ⟨hp, ch_ge C n hvp⟩, List.mem_toFinset.2 hvp⟩

theorem card_ch_le (hg : GoodC C) (o p : ℕ) (hp : p ∈ gatesIn C n o) : (ch C n p).toFinset.card ≤ bnd C n p :=
  (List.toFinset_card_le _).trans (ch_len C n hg (Finset.mem_filter.1 hp).2)

theorem count (hg : GoodC C) (o : ℕ) : (leaves C n o).card + (nots C n o).card ≤ (gatesIn C n o).card + 1 := by
  have h1 := Finset.card_le_card (parent_cover C n o)
  rw [Finset.card_erase_of_mem (self_desc C n o)] at h1
  have h2 : ((gatesIn C n o).biUnion (fun p => (ch C n p).toFinset)).card ≤
      ∑ p ∈ gatesIn C n o, (ch C n p).toFinset.card := Finset.card_biUnion_le
  have h3 := Finset.sum_le_sum (card_ch_le C n hg o)
  have h4 := sum_bnd C n o
  have h5 := leaves_gates C n o
  omega

theorem exact_count (hg : GoodC C) (o : ℕ)
    (hex : (gatesIn C n o).card + 1 ≤ (leaves C n o).card + (nots C n o).card) :
    (∀ p ∈ gatesIn C n o, (ch C n p).toFinset.card = bnd C n p) ∧
    (∀ p ∈ desc C n o, ∀ r ∈ desc C n o, ∀ c, c ∈ ch C n p → c ∈ ch C n r → p = r) := by
  have h1 := Finset.card_le_card (parent_cover C n o)
  rw [Finset.card_erase_of_mem (self_desc C n o)] at h1
  have h2 : ((gatesIn C n o).biUnion (fun p => (ch C n p).toFinset)).card ≤
      ∑ p ∈ gatesIn C n o, (ch C n p).toFinset.card := Finset.card_biUnion_le
  have h3 := Finset.sum_le_sum (card_ch_le C n hg o)
  have h4 := sum_bnd C n o
  have h5 := leaves_gates C n o
  have h6 : ∑ p ∈ gatesIn C n o, (ch C n p).toFinset.card = ∑ p ∈ gatesIn C n o, bnd C n p := by omega
  have h7 : ∑ p ∈ gatesIn C n o, (ch C n p).toFinset.card ≤
      ((gatesIn C n o).biUnion (fun p => (ch C n p).toFinset)).card := by omega
  refine ⟨(Finset.sum_eq_sum_iff_of_le (card_ch_le C n hg o)).1 h6, ?_⟩
  intro p hp r hr c hcp hcr
  by_contra hpr
  have hpG : p ∈ gatesIn C n o := Finset.mem_filter.2 ⟨hp, ch_ge C n hcp⟩
  have hrG : r ∈ gatesIn C n o := Finset.mem_filter.2 ⟨hr, ch_ge C n hcr⟩
  let F : ℕ → Finset ℕ := fun s => if s = r then (ch C n s).toFinset.erase c else (ch C n s).toFinset
  have hsub : (gatesIn C n o).biUnion (fun p => (ch C n p).toFinset) ⊆ (gatesIn C n o).biUnion F := by
    intro v hv
    rw [Finset.mem_biUnion] at hv ⊢
    obtain ⟨s, hs, hvs⟩ := hv
    by_cases hvc : v = c
    · refine ⟨p, hpG, ?_⟩
      simp only [F, if_neg hpr, hvc]
      exact List.mem_toFinset.2 hcp
    · refine ⟨s, hs, ?_⟩
      simp only [F]
      split
      · exact Finset.mem_erase.2 ⟨hvc, hvs⟩
      · exact hvs
  have h8 : ∑ s ∈ gatesIn C n o, (F s).card < ∑ s ∈ gatesIn C n o, (ch C n s).toFinset.card := by
    apply Finset.sum_lt_sum
    · intro s _
      simp only [F]
      split
      · exact Finset.card_erase_le
      · exact le_rfl
    · refine ⟨r, hrG, ?_⟩
      simp only [F, if_true]
      exact Finset.card_erase_lt_of_mem (List.mem_toFinset.2 hcr)
  have h9 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  omega

theorem sib_disj (o : ℕ)
    (huniq : ∀ p ∈ desc C n o, ∀ r ∈ desc C n o, ∀ c, c ∈ ch C n p → c ∈ ch C n r → p = r)
    (p a b : ℕ) (hp : p ∈ desc C n o) (ha : a ∈ ch C n p) (hb : b ∈ ch C n p) (hab : a ≠ b) :
    Disjoint (desc C n a) (desc C n b) := by
  have haT := child_desc C n hp ha
  have hbT := child_desc C n hp hb
  have top : ∀ a b : ℕ, a ∈ ch C n p → b ∈ ch C n p → a ≠ b → a ∈ desc C n o → b ∈ desc C n o →
      a ∈ desc C n b → False := by
    intro a b ha hb hab haT hbT h
    obtain ⟨r, hr, har⟩ := desc_parent C n b a h hab
    have hrT := desc_trans C n o b hbT hr
    have : p = r := huniq p hp r hrT a ha har
    have := desc_le C n b r hr
    have := ch_lt C n hb
    omega
  have main : ∀ d v, p - v = d → v ∈ desc C n a → v ∈ desc C n b → False := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro v hd hva hvb
      by_cases h1 : v = a
      · exact top a b ha hb hab haT hbT (h1 ▸ hvb)
      by_cases h2 : v = b
      · exact top b a hb ha hab.symm hbT haT (h2 ▸ hva)
      obtain ⟨s, hs, hvs⟩ := desc_parent C n a v hva h1
      obtain ⟨r, hr, hvr⟩ := desc_parent C n b v hvb h2
      have hsr : s = r := huniq s (desc_trans C n o a haT hs) r (desc_trans C n o b hbT hr) v hvs hvr
      subst hsr
      have h3 := desc_le C n a s hs
      have h4 := ch_lt C n ha
      have h5 := ch_lt C n hvs
      exact ih (p - s) (by omega) s rfl hs hr
  rw [Finset.disjoint_left]
  intro v hva hvb
  exact main _ v rfl hva hvb

end tree

def Node (n : ℕ) (T : Finset ℕ) (V : ℕ → (ℕ → Bool) → Bool) (S : ℕ → Finset ℕ) (N : ℕ → Prop) (w : ℕ) : Prop :=
  (w < n ∧ S w = {w} ∧ ∀ f, V w f = f w) ∨
  (n ≤ w ∧ ¬ N w ∧ ∃ a ∈ T, ∃ b ∈ T, a < w ∧ b < w ∧ Disjoint (S a) (S b) ∧ S w = insert w (S a ∪ S b) ∧
    ((∀ f, V w f = (V a f && V b f)) ∨ ∀ f, V w f = (V a f || V b f))) ∨
  (n ≤ w ∧ N w ∧ ∃ a ∈ T, a < w ∧ S w = insert w (S a) ∧ ∀ f, V w f = !V a f)

def inp (n : ℕ) (f : ℕ → Bool) : List Bool := (List.range n).map f

theorem tree_nodes (C : Circuit) (n : ℕ) (hg : GoodC C) (o : ℕ) (ho : o < n + C.gates.length)
    (hex : (gatesIn C n o).card + 1 ≤ (leaves C n o).card + (nots C n o).card) :
    ∀ w ∈ desc C n o, Node n (desc C n o) (fun w f => value C (inp n f) w) (desc C n) (isNot C n) w := by
  classical
  intro w hw
  obtain ⟨hcard, huniq⟩ := exact_count C n hg o hex
  have hlen : ∀ f, (inp n f).length = n := fun f => by simp [inp]
  by_cases hwn : w < n
  · refine Or.inl ⟨hwn, ?_, ?_⟩
    · ext v
      rw [mem_desc]
      have : ch C n w = [] := by
        unfold ch
        rw [if_neg (by omega)]
      simp [this]
    · intro f
      change (run C.gates (inp n f)).getD w false = f w
      rw [prefix_keep _ _ (by rw [hlen]; exact hwn)]
      simp [inp, List.getD_eq_getElem?_getD, hwn]
  have hwn' : n ≤ w := by omega
  right
  have hwo := desc_le C n o w hw
  have hj : w - n < C.gates.length := by omega
  have hnw : n + (w - n) = w := by omega
  have hval : ∀ f, value C (inp n f) w = (gateAt C n w).op.eval
      ((gateAt C n w).inputs.map fun i => if i < w then value C (inp n f) i else false) := by
    intro f
    have := value_gate C (inp n f) (w - n) hj
    rw [hlen, hnw] at this
    rw [gateAt_eq C n hj]
    exact this
  have hG : w ∈ gatesIn C n o := Finset.mem_filter.2 ⟨hw, hwn'⟩
  have hc := hcard w hG
  have hch : ch C n w = (reads C n w).filter (fun c => decide (c < w)) := by
    unfold ch
    rw [if_pos ⟨hwn', hj⟩]
  have hop := hg _ (List.getElem_mem hj)
  rw [← gateAt_eq C n hj] at hop
  have hdesc : ∀ v, v ∈ desc C n w ↔ v = w ∨ ∃ c ∈ ch C n w, v ∈ desc C n c := mem_desc C n w
  have hlenle : (ch C n w).toFinset.card ≤ (ch C n w).length := List.toFinset_card_le _
  by_cases hN : isNot C n w
  · right
    refine ⟨hwn', hN, ?_⟩
    have hop' : (gateAt C n w).op = GateOp.not := hN.2
    have hreads : reads C n w = (gateAt C n w).inputs.take 1 := by
      unfold reads
      rw [if_pos hop']
    rw [show bnd C n w = 1 from if_pos hN] at hc
    cases hin : (gateAt C n w).inputs with
    | nil =>
      rw [hin] at hreads
      rw [hch, hreads] at hc
      simp at hc
    | cons a l =>
      rw [hin] at hreads
      simp only [List.take_succ_cons, List.take_zero] at hreads
      have haw : a < w := by
        by_contra h
        rw [hch, hreads] at hc
        simp [h] at hc
      have hcha : ch C n w = [a] := by
        rw [hch, hreads]
        simp [haw]
      have haT : a ∈ desc C n o := child_desc C n hw (hcha ▸ List.mem_singleton_self a)
      refine ⟨a, haT, haw, ?_, ?_⟩
      · ext v
        rw [hdesc, hcha]
        simp
      · intro f
        change value C (inp n f) w = !value C (inp n f) a
        rw [hval, hop', hin]
        simp [GateOp.eval, haw]
  · left
    refine ⟨hwn', hN, ?_⟩
    have hop' : (gateAt C n w).op ≠ GateOp.not := fun c => hN ⟨hwn', c⟩
    have hreads : reads C n w = (gateAt C n w).inputs := by
      unfold reads
      rw [if_neg hop']
    rw [show bnd C n w = 2 from if_neg hN] at hc
    have h2 := hop.2
    have hfl := List.length_filter_le (fun c => decide (c < w)) (gateAt C n w).inputs
    rw [hch, hreads] at hlenle hc
    have hlen2 : (gateAt C n w).inputs.length = 2 := by omega
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen2
    rw [hab] at hlenle hc hfl
    have haw : a < w := by
      by_contra h
      by_cases h' : b < w <;> simp [h, h'] at hc
    have hbw : b < w := by
      by_contra h
      simp [haw, h] at hc
    have hne : a ≠ b := by
      intro h
      subst h
      simp [haw] at hc
    have hchab : ch C n w = [a, b] := by
      rw [hch, hreads, hab]
      simp [haw, hbw]
    have haT : a ∈ desc C n o := child_desc C n hw (by rw [hchab]; simp)
    have hbT : b ∈ desc C n o := child_desc C n hw (by rw [hchab]; simp)
    refine ⟨a, haT, b, hbT, haw, hbw, ?_, ?_, ?_⟩
    · exact sib_disj C n o huniq w a b hw (by rw [hchab]; simp) (by rw [hchab]; simp) hne
    · ext v
      rw [hdesc, hchab]
      simp
    · rcases hop.1 with h | h | h
      · left
        intro f
        change value C (inp n f) w = (value C (inp n f) a && value C (inp n f) b)
        rw [hval, h, hab]
        simp [GateOp.eval, haw, hbw]
      · right
        intro f
        change value C (inp n f) w = (value C (inp n f) a || value C (inp n f) b)
        rw [hval, h, hab]
        simp [GateOp.eval, haw, hbw]
      · exact absurd h hop'

def only (z : ℕ) : ℕ → Bool := fun i => decide (i = z)
def two (a b : ℕ) : ℕ → Bool := fun i => decide (i = a ∨ i = b)
def zero : ℕ → Bool := fun _ => false

section nodes

variable {n : ℕ} {T : Finset ℕ} {V : ℕ → (ℕ → Bool) → Bool} {S : ℕ → Finset ℕ} {N : ℕ → Prop}
  (H : ∀ w ∈ T, Node n T V S N w)

def sup (n : ℕ) (S : ℕ → Finset ℕ) (w : ℕ) : Finset ℕ := (S w).filter (fun i => i < n)

theorem sup_bin {a b w : ℕ} (h : S w = insert w (S a ∪ S b)) (hw : n ≤ w) (i : ℕ) :
    i ∈ sup n S w ↔ i ∈ sup n S a ∨ i ∈ sup n S b := by
  unfold sup
  rw [h, Finset.filter_insert, if_neg (by omega), Finset.filter_union, Finset.mem_union]

theorem sup_un {a w : ℕ} (h : S w = insert w (S a)) (hw : n ≤ w) : sup n S w = sup n S a := by
  unfold sup
  rw [h, Finset.filter_insert, if_neg (by omega)]

theorem sup_leaf {w : ℕ} (h : S w = {w}) (hw : w < n) : sup n S w = {w} := by
  unfold sup
  rw [h, Finset.filter_singleton, if_pos hw]

theorem sup_disj {a b : ℕ} (h : Disjoint (S a) (S b)) {i : ℕ} (ha : i ∈ sup n S a) (hb : i ∈ sup n S b) : False :=
  Finset.disjoint_left.1 h (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hb).1

include H

theorem self_mem : ∀ w ∈ T, w ∈ S w := by
  intro w hw
  rcases H w hw with ⟨_, h, _⟩ | ⟨_, _, a, _, b, _, _, _, _, h, _⟩ | ⟨_, _, a, _, _, h, _⟩
  · rw [h]
    exact Finset.mem_singleton_self _
  · rw [h]
    exact Finset.mem_insert_self _ _
  · rw [h]
    exact Finset.mem_insert_self _ _

theorem sup_ne : ∀ w ∈ T, (sup n S w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    rcases H w hw with ⟨h1, h2, _⟩ | ⟨h0, _, a, ha, b, _, haw, _, _, h, _⟩ | ⟨h0, _, a, ha, haw, h, _⟩
    · rw [sup_leaf h2 h1]
      exact Finset.singleton_nonempty _
    · obtain ⟨i, hi⟩ := ih a haw ha
      exact ⟨i, (sup_bin h h0 i).2 (Or.inl hi)⟩
    · rw [sup_un h h0]
      exact ih a haw ha

theorem dep : ∀ w ∈ T, ∀ f g : ℕ → Bool, (∀ i ∈ sup n S w, f i = g i) → V w f = V w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw f g hfg
    rcases H w hw with ⟨h1, h2, h3⟩ | ⟨h0, _, a, ha, b, hb, haw, hbw, _, h, hv⟩ | ⟨h0, _, a, ha, haw, h, hv⟩
    · rw [h3, h3]
      exact hfg w (by rw [sup_leaf h2 h1]; simp)
    · have e1 := ih a haw ha f g (fun i hi => hfg i ((sup_bin h h0 i).2 (Or.inl hi)))
      have e2 := ih b hbw hb f g (fun i hi => hfg i ((sup_bin h h0 i).2 (Or.inr hi)))
      rcases hv with hv | hv <;> rw [hv, hv, e1, e2]
    · rw [hv, hv, ih a haw ha f g (fun i hi => hfg i (by rw [sup_un h h0]; exact hi))]

theorem mono : ∀ w ∈ T, (∀ v ∈ S w, ¬ N v) → ∀ f g : ℕ → Bool, (∀ i, f i = true → g i = true) →
    V w f = true → V w g = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm f g hfg
    rcases H w hw with ⟨_, _, h3⟩ | ⟨_, _, a, ha, b, hb, haw, hbw, _, h, hv⟩ | ⟨_, hN, _⟩
    · rw [h3, h3]
      exact hfg w
    · have ma := ih a haw ha (fun v hv => hm v (by rw [h]; simp [hv])) f g hfg
      have mb := ih b hbw hb (fun v hv => hm v (by rw [h]; simp [hv])) f g hfg
      rcases hv with hv | hv <;> rw [hv, hv]
      · simp only [Bool.and_eq_true]
        exact fun p => ⟨ma p.1, mb p.2⟩
      · simp only [Bool.or_eq_true]
        exact fun p => p.imp ma mb
    · exact absurd hN (hm w (self_mem H w hw))

theorem mono_zero : ∀ w ∈ T, (∀ v ∈ S w, ¬ N v) → V w zero = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm
    rcases H w hw with ⟨_, _, h3⟩ | ⟨_, _, a, ha, b, hb, haw, hbw, _, h, hv⟩ | ⟨_, hN, _⟩
    · rw [h3]
      rfl
    · have ma := ih a haw ha (fun v hv => hm v (by rw [h]; simp [hv]))
      have mb := ih b hbw hb (fun v hv => hm v (by rw [h]; simp [hv]))
      rcases hv with hv | hv <;> rw [hv, ma, mb] <;> rfl
    · exact absurd hN (hm w (self_mem H w hw))

theorem off {w : ℕ} (hw : w ∈ T) (hm : ∀ v ∈ S w, ¬ N v) (f : ℕ → Bool)
    (hf : ∀ i ∈ sup n S w, f i = false) : V w f = false :=
  (dep H w hw f zero hf).trans (mono_zero H w hw hm)

theorem in_sup {w : ℕ} (hw : w ∈ T) (a b : ℕ) (h1 : V w (two a b) = true) (h2 : V w (only b) = false) :
    a ∈ sup n S w := by
  by_contra h
  have : V w (two a b) = V w (only b) := by
    apply dep H w hw
    intro i hi
    have : i ≠ a := fun c => h (c ▸ hi)
    simp [two, only, this]
  rw [this, h2] at h1
  exact Bool.false_ne_true h1

end nodes

def Pr {k : ℕ} (xi yi : Fin k → ℕ) (s : Finset (Fin k)) (M : Finset (Finset (Fin k))) (f : ℕ → Bool) : Prop :=
  (∃ u ∈ s, f (xi u) = true ∧ f (yi u) = true) ∨
  ∃ e ∈ M, (∀ u ∈ e, f (xi u) = true) ∨ (∀ u ∈ e, f (yi u) = true)

theorem Pr_union {k : ℕ} (xi yi : Fin k → ℕ) (s t : Finset (Fin k)) (M L : Finset (Finset (Fin k)))
    (f : ℕ → Bool) : Pr xi yi (s ∪ t) (M ∪ L) f ↔ Pr xi yi s M f ∨ Pr xi yi t L f := by
  simp only [Pr, Finset.mem_union, or_and_right, exists_or]
  exact or_or_or_comm

theorem isM_union {k : ℕ} (s t : Finset (Fin k)) (M L : Finset (Finset (Fin k))) (hM : IsM M) (hL : IsM L)
    (hs : ∀ e ∈ M, e ⊆ s) (ht : ∀ e ∈ L, e ⊆ t) (hd : Disjoint s t) :
    IsM (M ∪ L) ∧ ∀ e ∈ M ∪ L, e ⊆ s ∪ t := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact hM.1 e h
    · exact hL.1 e h
  · intro e he g hg hne
    rcases Finset.mem_union.1 he with h | h <;> rcases Finset.mem_union.1 hg with h' | h'
    · exact hM.2 e h g h' hne
    · exact hd.mono (hs e h) (ht g h')
    · exact (hd.mono (hs g h') (ht e h)).symm
    · exact hL.2 e h g h' hne
  · intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact (hs e h).trans Finset.subset_union_left
    · exact (ht e h).trans Finset.subset_union_right

section classify

variable {n : ℕ} {T : Finset ℕ} {V : ℕ → (ℕ → Bool) → Bool} {S : ℕ → Finset ℕ} {N : ℕ → Prop}
  (H : ∀ w ∈ T, Node n T V S N w) {k : ℕ} (xi yi : Fin k → ℕ)
  (hx : ∀ u v, xi u = xi v → u = v) (hy : ∀ u v, yi u = yi v → u = v) (hxy : ∀ u v, xi u ≠ yi v)

include H

theorem and_child {a : ℕ} (ha : a ∈ T) (ma : ∀ v ∈ S a, ¬ N v) (f : ℕ → Bool)
    (h1 : ∀ z ∈ sup n S a, V a (only z) = true) : V a f = true ↔ ∃ z ∈ sup n S a, f z = true := by
  constructor
  · intro h
    by_contra c
    have : V a f = false := off H ha ma f (fun i hi => by
      cases hfi : f i
      · rfl
      · exact absurd ⟨i, hi, hfi⟩ c)
    rw [this] at h
    exact Bool.false_ne_true h
  · rintro ⟨z, hz, hfz⟩
    apply mono H a ha ma (only z) f _ (h1 z hz)
    intro i hi
    simp only [only, decide_eq_true_eq] at hi
    rw [hi]
    exact hfz

include hx hy hxy

theorem cls_id : ∀ w ∈ T, (∀ v ∈ S w, ¬ N v) → ∀ s : Finset (Fin k),
    (∀ i, i ∈ sup n S w ↔ ∃ u ∈ s, i = xi u ∨ i = yi u) →
    (∀ u ∈ s, ∀ v ∈ s, V w (two (xi u) (yi v)) = decide (u = v)) →
    (∀ z, V w (only z) = false) →
    ∃ M : Finset (Finset (Fin k)), IsM M ∧ (∀ e ∈ M, e ⊆ s) ∧ ∀ f, (V w f = true ↔ Pr xi yi s M f) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm s hs hval hsing
    rcases H w hw with ⟨h1, h2, _⟩ | ⟨h0, _, a, ha, b, hb, haw, hbw, hd, h, hv⟩ | ⟨_, hN, _⟩
    · exfalso
      obtain ⟨i, hi⟩ := sup_ne H w hw
      obtain ⟨u, hu, _⟩ := (hs i).1 hi
      have e1 : xi u ∈ sup n S w := (hs _).2 ⟨u, hu, Or.inl rfl⟩
      have e2 : yi u ∈ sup n S w := (hs _).2 ⟨u, hu, Or.inr rfl⟩
      rw [sup_leaf h2 h1, Finset.mem_singleton] at e1 e2
      exact hxy u u (e1.trans e2.symm)
    swap
    · exact absurd hN (hm w (self_mem H w hw))
    have ma : ∀ v ∈ S a, ¬ N v := fun v hv => hm v (by rw [h]; simp [hv])
    have mb : ∀ v ∈ S b, ¬ N v := fun v hv => hm v (by rw [h]; simp [hv])
    have hsup := sup_bin (n := n) h h0
    have disj : ∀ i, i ∈ sup n S a → i ∈ sup n S b → False := fun i => sup_disj hd
    have inab : ∀ u ∈ s, (xi u ∈ sup n S a ∨ xi u ∈ sup n S b) ∧ (yi u ∈ sup n S a ∨ yi u ∈ sup n S b) :=
      fun u hu => ⟨(hsup _).1 ((hs _).2 ⟨u, hu, Or.inl rfl⟩), (hsup _).1 ((hs _).2 ⟨u, hu, Or.inr rfl⟩)⟩
    have offt : ∀ c ∈ T, (∀ v ∈ S c, ¬ N v) → ∀ p q : ℕ, p ∉ sup n S c → q ∉ sup n S c →
        V c (two p q) = false := by
      intro c hc mc p q hp hq
      apply off H hc mc
      intro i hi
      have e1 : i ≠ p := fun e => hp (e ▸ hi)
      have e2 : i ≠ q := fun e => hq (e ▸ hi)
      simp [two, e1, e2]
    have onel : ∀ c ∈ T, ∀ p q : ℕ, q ∉ sup n S c → V c (two p q) = V c (only p) := by
      intro c hc p q hq
      apply dep H c hc
      intro i hi
      have e : i ≠ q := fun e => hq (e ▸ hi)
      simp [two, only, e]
    have oner : ∀ c ∈ T, ∀ p q : ℕ, p ∉ sup n S c → V c (two p q) = V c (only q) := by
      intro c hc p q hp
      apply dep H c hc
      intro i hi
      have e : i ≠ p := fun e => hp (e ▸ hi)
      simp [two, only, e]
    rcases hv with hv | hv
    · have h1 : ∀ u ∈ s, V a (two (xi u) (yi u)) = true ∧ V b (two (xi u) (yi u)) = true := by
        intro u hu
        have := hval u hu u hu
        rw [hv] at this
        simpa using this
      have h2 : ∀ u ∈ s, (xi u ∈ sup n S a ∨ yi u ∈ sup n S a) ∧ (xi u ∈ sup n S b ∨ yi u ∈ sup n S b) := by
        intro u hu
        constructor
        · by_contra c
          rw [not_or] at c
          have := offt a ha ma _ _ c.1 c.2
          rw [(h1 u hu).1] at this
          exact Bool.noConfusion this
        · by_contra c
          rw [not_or] at c
          have := offt b hb mb _ _ c.1 c.2
          rw [(h1 u hu).2] at this
          exact Bool.noConfusion this
      have h3a : ∀ z ∈ sup n S a, V a (only z) = true := by
        intro z hz
        obtain ⟨u, hu, rfl | rfl⟩ := (hs z).1 ((hsup z).2 (Or.inl hz))
        · have : yi u ∉ sup n S a := by
            intro c
            rcases (h2 u hu).2 with d | d
            · exact disj _ hz d
            · exact disj _ c d
          rw [← onel a ha (xi u) (yi u) this]
          exact (h1 u hu).1
        · have : xi u ∉ sup n S a := by
            intro c
            rcases (h2 u hu).2 with d | d
            · exact disj _ c d
            · exact disj _ hz d
          rw [← oner a ha (xi u) (yi u) this]
          exact (h1 u hu).1
      have h3b : ∀ z ∈ sup n S b, V b (only z) = true := by
        intro z hz
        obtain ⟨u, hu, rfl | rfl⟩ := (hs z).1 ((hsup z).2 (Or.inr hz))
        · have : yi u ∉ sup n S b := by
            intro c
            rcases (h2 u hu).1 with d | d
            · exact disj _ d hz
            · exact disj _ d c
          rw [← onel b hb (xi u) (yi u) this]
          exact (h1 u hu).2
        · have : xi u ∉ sup n S b := by
            intro c
            rcases (h2 u hu).1 with d | d
            · exact disj _ d c
            · exact disj _ d hz
          rw [← oner b hb (xi u) (yi u) this]
          exact (h1 u hu).2
      have core : ∀ a ∈ T, ∀ b ∈ T, (∀ v ∈ S a, ¬ N v) → (∀ v ∈ S b, ¬ N v) →
          (∀ i, i ∈ sup n S w ↔ i ∈ sup n S a ∨ i ∈ sup n S b) →
          (∀ i, i ∈ sup n S a → i ∈ sup n S b → False) →
          (∀ z ∈ sup n S a, V a (only z) = true) → (∀ z ∈ sup n S b, V b (only z) = true) →
          (∀ f, V w f = (V a f && V b f)) →
          ∀ p ∈ s, ∀ q ∈ s, q ≠ p → xi p ∈ sup n S a →
          ∃ M : Finset (Finset (Fin k)), IsM M ∧ (∀ e ∈ M, e ⊆ s) ∧ ∀ f, (V w f = true ↔ Pr xi yi s M f) := by
        intro a ha b hb ma mb hsup disj h3a h3b hv p hp q hq hqp hpa
        have cross : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → xi u ∈ sup n S a → yi v ∈ sup n S b → False := by
          intro u hu v hv' huv h1 h2
          have e1 : V a (two (xi u) (yi v)) = true :=
            (and_child H ha ma _ h3a).2 ⟨_, h1, by simp [two]⟩
          have e2 : V b (two (xi u) (yi v)) = true :=
            (and_child H hb mb _ h3b).2 ⟨_, h2, by simp [two]⟩
          have := hval u hu v hv'
          rw [hv, e1, e2] at this
          simp [huv] at this
        have cross' : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → xi u ∈ sup n S b → yi v ∈ sup n S a → False := by
          intro u hu v hv' huv h1 h2
          have e1 : V a (two (xi u) (yi v)) = true :=
            (and_child H ha ma _ h3a).2 ⟨_, h2, by simp [two]⟩
          have e2 : V b (two (xi u) (yi v)) = true :=
            (and_child H hb mb _ h3b).2 ⟨_, h1, by simp [two]⟩
          have := hval u hu v hv'
          rw [hv, e1, e2] at this
          simp [huv] at this
        have mem : ∀ u ∈ s, ∀ z, (z = xi u ∨ z = yi u) → z ∈ sup n S a ∨ z ∈ sup n S b := by
          intro u hu z hz
          exact (hsup z).1 ((hs z).2 ⟨u, hu, hz⟩)
        have yqa : yi q ∈ sup n S a :=
          (mem q hq _ (Or.inr rfl)).resolve_right (fun c => cross p hp q hq hqp.symm hpa c)
        have xqb : xi q ∈ sup n S b := by
          refine (mem q hq _ (Or.inl rfl)).resolve_left (fun c => ?_)
          have : V b (two (xi q) (yi q)) = false := by
            apply off H hb mb
            intro i hi
            have e1 : i ≠ xi q := fun e => disj _ c (e ▸ hi)
            have e2 : i ≠ yi q := fun e => disj _ yqa (e ▸ hi)
            simp [two, e1, e2]
          have h := hval q hq q hq
          rw [hv, this] at h
          simp at h
        have ypb : yi p ∈ sup n S b :=
          (mem p hp _ (Or.inr rfl)).resolve_left (fun c => cross' q hq p hp hqp xqb c)
        have only2 : ∀ r ∈ s, r = p ∨ r = q := by
          intro r hr
          by_contra c
          rw [not_or] at c
          rcases mem r hr (yi r) (Or.inr rfl) with d | d
          · exact cross' q hq r hr (Ne.symm c.2) xqb d
          · exact cross p hp r hr (Ne.symm c.1) hpa d
        have hs2 : s = {p, q} := by
          ext r
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · exact only2 r
          · rintro (rfl | rfl) <;> assumption
        have ma' : ∀ z, z ∈ sup n S a ↔ z = xi p ∨ z = yi q := by
          intro z
          constructor
          · intro hz
            obtain ⟨u, hu, e⟩ := (hs z).1 ((hsup z).2 (Or.inl hz))
            rcases only2 u hu with rfl | rfl <;> rcases e with rfl | rfl
            · exact Or.inl rfl
            · exact (disj _ hz ypb).elim
            · exact (disj _ hz xqb).elim
            · exact Or.inr rfl
          · rintro (rfl | rfl) <;> assumption
        have mb' : ∀ z, z ∈ sup n S b ↔ z = xi q ∨ z = yi p := by
          intro z
          constructor
          · intro hz
            obtain ⟨u, hu, e⟩ := (hs z).1 ((hsup z).2 (Or.inr hz))
            rcases only2 u hu with rfl | rfl <;> rcases e with rfl | rfl
            · exact (disj _ hpa hz).elim
            · exact Or.inr rfl
            · exact Or.inl rfl
            · exact (disj _ yqa hz).elim
          · rintro (rfl | rfl) <;> assumption
        refine ⟨{{p, q}}, ⟨?_, ?_⟩, ?_, ?_⟩
        · intro e he
          rw [Finset.mem_singleton] at he
          rw [he, Finset.card_pair hqp.symm]
        · intro e he g hg hne
          rw [Finset.mem_singleton] at he hg
          exact absurd (he.trans hg.symm) hne
        · intro e he
          rw [Finset.mem_singleton] at he
          rw [he, hs2]
        · intro f
          rw [hv, Bool.and_eq_true, and_child H ha ma f h3a, and_child H hb mb f h3b]
          simp only [ma', mb', or_and_right, exists_or, exists_eq_left]
          rw [hs2]
          simp only [Pr, Finset.mem_insert, Finset.mem_singleton, or_and_right, exists_or, exists_eq_left,
            forall_eq_or_imp, forall_eq]
          tauto
      obtain ⟨i, hi⟩ := sup_ne H w hw
      obtain ⟨p, hp, _⟩ := (hs i).1 hi
      by_cases hq : ∃ q ∈ s, q ≠ p
      · obtain ⟨q, hq, hqp⟩ := hq
        rcases (inab p hp).1 with c | c
        · exact core a ha b hb ma mb hsup disj h3a h3b hv p hp q hq hqp c
        · exact core b hb a ha mb ma (fun i => (hsup i).trans or_comm) (fun i x y => disj i y x) h3b h3a
            (fun f => by rw [hv, Bool.and_comm]) p hp q hq hqp c
      · have only1 : ∀ r ∈ s, r = p := fun r hr => by
          by_contra c
          exact hq ⟨r, hr, c⟩
        have hs1 : s = {p} := by
          ext r
          rw [Finset.mem_singleton]
          exact ⟨only1 r, fun e => e ▸ hp⟩
        have vars : ∀ z, z ∈ sup n S w → z = xi p ∨ z = yi p := by
          intro z hz
          obtain ⟨u, hu, e⟩ := (hs z).1 hz
          rwa [only1 u hu] at e
        refine ⟨∅, isM_empty, by simp, ?_⟩
        intro f
        rw [hv, Bool.and_eq_true, and_child H ha ma f h3a, and_child H hb mb f h3b]
        have goal : Pr xi yi s ∅ f ↔ f (xi p) = true ∧ f (yi p) = true := by
          simp [Pr, hs1]
        rw [goal]
        have key : (xi p ∈ sup n S a ∧ yi p ∈ sup n S b) ∨ (yi p ∈ sup n S a ∧ xi p ∈ sup n S b) := by
          rcases (inab p hp).1 with c | c
          · rcases (h2 p hp).2 with d | d
            · exact (disj _ c d).elim
            · exact Or.inl ⟨c, d⟩
          · rcases (h2 p hp).1 with d | d
            · exact (disj _ d c).elim
            · exact Or.inr ⟨d, c⟩
        have uni : ∀ c : ℕ, ∀ z0, z0 ∈ sup n S c → (∀ z ∈ sup n S c, z = z0) →
            ((∃ z ∈ sup n S c, f z = true) ↔ f z0 = true) := by
          intro c z0 h0' hu
          constructor
          · rintro ⟨z, hz, hf⟩
            rwa [hu z hz] at hf
          · intro hf
            exact ⟨z0, h0', hf⟩
        rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · rw [uni a (xi p) k1, uni b (yi p) k2]
          · intro z hz
            rcases vars z ((hsup z).2 (Or.inr hz)) with e | e
            · exact (disj _ k1 (e ▸ hz)).elim
            · exact e
          · intro z hz
            rcases vars z ((hsup z).2 (Or.inl hz)) with e | e
            · exact e
            · exact (disj _ (e ▸ hz) k2).elim
        · rw [uni a (yi p) k1, uni b (xi p) k2, and_comm]
          · intro z hz
            rcases vars z ((hsup z).2 (Or.inr hz)) with e | e
            · exact e
            · exact (disj _ k1 (e ▸ hz)).elim
          · intro z hz
            rcases vars z ((hsup z).2 (Or.inl hz)) with e | e
            · exact (disj _ (e ▸ hz) k2).elim
            · exact e
    · have sa0 : ∀ z, V a (only z) = false ∧ V b (only z) = false := by
        intro z
        have := hsing z
        rw [hv] at this
        simpa using this
      have tog : ∀ u ∈ s, (xi u ∈ sup n S a ∧ yi u ∈ sup n S a) ∨ (xi u ∈ sup n S b ∧ yi u ∈ sup n S b) := by
        intro u hu
        have tr : V w (two (xi u) (yi u)) = true := by
          rw [hval u hu u hu]
          simp
        rw [hv] at tr
        rcases (inab u hu).1 with c1 | c1 <;> rcases (inab u hu).2 with c2 | c2
        · exact Or.inl ⟨c1, c2⟩
        · rw [onel a ha _ _ (fun c => disj _ c c2), oner b hb _ _ (fun c => disj _ c1 c),
            (sa0 _).1, (sa0 _).2] at tr
          exact Bool.noConfusion tr
        · rw [oner a ha _ _ (fun c => disj _ c c1), onel b hb _ _ (fun c => disj _ c2 c),
            (sa0 _).1, (sa0 _).2] at tr
          exact Bool.noConfusion tr
        · exact Or.inr ⟨c1, c2⟩
      have part : ∀ a ∈ T, ∀ b ∈ T, a < w → (∀ v ∈ S a, ¬ N v) → (∀ v ∈ S b, ¬ N v) →
          (∀ i, i ∈ sup n S w ↔ i ∈ sup n S a ∨ i ∈ sup n S b) →
          (∀ i, i ∈ sup n S a → i ∈ sup n S b → False) →
          (∀ f, V w f = (V a f || V b f)) →
          (∀ u ∈ s, (xi u ∈ sup n S a ∧ yi u ∈ sup n S a) ∨ (xi u ∈ sup n S b ∧ yi u ∈ sup n S b)) →
          ∃ M : Finset (Finset (Fin k)), IsM M ∧ (∀ e ∈ M, e ⊆ s.filter (fun u => xi u ∈ sup n S a)) ∧
            ∀ f, (V a f = true ↔ Pr xi yi (s.filter (fun u => xi u ∈ sup n S a)) M f) := by
        intro a ha b hb haw ma mb hsup disj hv tog
        apply ih a haw ha ma
        · intro i
          constructor
          · intro hi
            obtain ⟨u, hu, e⟩ := (hs i).1 ((hsup i).2 (Or.inl hi))
            refine ⟨u, Finset.mem_filter.2 ⟨hu, ?_⟩, e⟩
            rcases tog u hu with c | c
            · exact c.1
            · rcases e with e | e
              · exact (disj _ (e ▸ hi) c.1).elim
              · exact (disj _ (e ▸ hi) c.2).elim
          · rintro ⟨u, hu, e⟩
            rw [Finset.mem_filter] at hu
            rcases tog u hu.1 with c | c
            · rcases e with rfl | rfl
              · exact c.1
              · exact c.2
            · exact (disj _ hu.2 c.1).elim
        · intro u hu v hv'
          rw [Finset.mem_filter] at hu hv'
          have t := hval u hu.1 v hv'.1
          rw [hv] at t
          have ub : xi u ∉ sup n S b := fun c => disj _ hu.2 c
          have vb : yi v ∉ sup n S b := by
            intro c
            rcases tog v hv'.1 with d | d
            · exact disj _ d.2 c
            · exact disj _ hv'.2 d.1
          rw [offt b hb mb _ _ ub vb, Bool.or_false] at t
          exact t
        · intro z
          have := hsing z
          rw [hv] at this
          exact (Bool.or_eq_false_iff.1 this).1
      obtain ⟨Ma, hMa, sMa, va⟩ := part a ha b hb haw ma mb hsup disj hv tog
      obtain ⟨Mb, hMb, sMb, vb⟩ := part b hb a ha hbw mb ma (fun i => (hsup i).trans or_comm)
        (fun i x y => disj i y x) (fun f => by rw [hv, Bool.or_comm]) (fun u hu => (tog u hu).symm)
      have hsplit : s.filter (fun u => xi u ∈ sup n S a) ∪ s.filter (fun u => xi u ∈ sup n S b) = s := by
        rw [← Finset.filter_or]
        apply Finset.filter_true_of_mem
        intro u hu
        exact (inab u hu).1
      have hdj : Disjoint (s.filter (fun u => xi u ∈ sup n S a)) (s.filter (fun u => xi u ∈ sup n S b)) := by
        rw [Finset.disjoint_left]
        intro u h1 h2
        exact disj _ (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
      obtain ⟨hM, hMs⟩ := isM_union _ _ Ma Mb hMa hMb sMa sMb hdj
      rw [hsplit] at hMs
      refine ⟨Ma ∪ Mb, hM, hMs, ?_⟩
      intro f
      rw [hv, Bool.or_eq_true, va, vb, ← Pr_union, hsplit]

theorem cls_z (z : ℕ) (hzx : ∀ u, z ≠ xi u) (hzy : ∀ u, z ≠ yi u) : ∀ w ∈ T, (∀ v ∈ S w, ¬ N v) →
    ∀ s : Finset (Fin k),
    (∀ i, i ∈ sup n S w ↔ i = z ∨ ∃ u ∈ s, i = xi u ∨ i = yi u) →
    (∀ u ∈ s, ∀ v ∈ s, V w (two (xi u) (yi v)) = decide (u = v)) →
    (∀ i, i ≠ z → V w (only i) = false) → V w (only z) = true →
    ∃ M : Finset (Finset (Fin k)), IsM M ∧ (∀ e ∈ M, e ⊆ s) ∧
      ∀ f, (V w f = true ↔ f z = true ∨ Pr xi yi s M f) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm s hs hval hsing hz
    rcases H w hw with ⟨h1, h2, h3⟩ | ⟨h0, _, a, ha, b, hb, haw, hbw, hd, h, hv⟩ | ⟨_, hN, _⟩
    · have ez : z = w := by
        have := (hs z).2 (Or.inl rfl)
        rwa [sup_leaf h2 h1, Finset.mem_singleton] at this
      have es : s = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro u hu
        have := (hs (xi u)).2 (Or.inr ⟨u, hu, Or.inl rfl⟩)
        rw [sup_leaf h2 h1, Finset.mem_singleton] at this
        exact hzx u (ez.trans this.symm)
      refine ⟨∅, isM_empty, by simp, fun f => ?_⟩
      rw [h3, es, ez]
      simp [Pr]
    swap
    · exact absurd hN (hm w (self_mem H w hw))
    have ma : ∀ v ∈ S a, ¬ N v := fun v hv => hm v (by rw [h]; simp [hv])
    have mb : ∀ v ∈ S b, ¬ N v := fun v hv => hm v (by rw [h]; simp [hv])
    have hsup := sup_bin (n := n) h h0
    have disj : ∀ i, i ∈ sup n S a → i ∈ sup n S b → False := fun i => sup_disj hd
    have core : ∀ a ∈ T, ∀ b ∈ T, a < w → b < w → (∀ v ∈ S a, ¬ N v) → (∀ v ∈ S b, ¬ N v) →
        (∀ i, i ∈ sup n S w ↔ i ∈ sup n S a ∨ i ∈ sup n S b) →
        (∀ i, i ∈ sup n S a → i ∈ sup n S b → False) →
        (∀ f, V w f = (V a f || V b f)) → z ∈ sup n S a →
        ∃ M : Finset (Finset (Fin k)), IsM M ∧ (∀ e ∈ M, e ⊆ s) ∧
          ∀ f, (V w f = true ↔ f z = true ∨ Pr xi yi s M f) := by
      intro a ha b hb haw hbw ma mb hsup disj hv hza
      have zb : z ∉ sup n S b := disj z hza
      have bz : V b (only z) = false := by
        apply off H hb mb
        intro i hi
        have : i ≠ z := fun e => zb (e ▸ hi)
        simp [only, this]
      have asing : ∀ i, i ≠ z → V a (only i) = false := by
        intro i hi
        have := hsing i hi
        rw [hv] at this
        exact (Bool.or_eq_false_iff.1 this).1
      have bsing : ∀ i, V b (only i) = false := by
        intro i
        by_cases e : i = z
        · rw [e, bz]
        · have := hsing i e
          rw [hv] at this
          exact (Bool.or_eq_false_iff.1 this).2
      have az : V a (only z) = true := by
        have := hz
        rw [hv, bz, Bool.or_false] at this
        exact this
      have inab : ∀ u ∈ s, ∀ i, (i = xi u ∨ i = yi u) → i ∈ sup n S a ∨ i ∈ sup n S b :=
        fun u hu i e => (hsup i).1 ((hs i).2 (Or.inr ⟨u, hu, e⟩))
      have onel : ∀ c ∈ T, ∀ p q : ℕ, q ∉ sup n S c → V c (two p q) = V c (only p) := by
        intro c hc p q hq
        apply dep H c hc
        intro i hi
        have e : i ≠ q := fun e => hq (e ▸ hi)
        simp [two, only, e]
      have oner : ∀ c ∈ T, ∀ p q : ℕ, p ∉ sup n S c → V c (two p q) = V c (only q) := by
        intro c hc p q hp
        apply dep H c hc
        intro i hi
        have e : i ≠ p := fun e => hp (e ▸ hi)
        simp [two, only, e]
      have tog : ∀ u ∈ s, (xi u ∈ sup n S a ∧ yi u ∈ sup n S a) ∨ (xi u ∈ sup n S b ∧ yi u ∈ sup n S b) := by
        intro u hu
        have tr : V w (two (xi u) (yi u)) = true := by
          rw [hval u hu u hu]
          simp
        rw [hv] at tr
        rcases inab u hu _ (Or.inl rfl) with c1 | c1 <;> rcases inab u hu _ (Or.inr rfl) with c2 | c2
        · exact Or.inl ⟨c1, c2⟩
        · rw [onel a ha _ _ (fun c => disj _ c c2), oner b hb _ _ (fun c => disj _ c1 c),
            asing _ (hzx u).symm, bsing] at tr
          exact Bool.noConfusion tr
        · rw [oner a ha _ _ (fun c => disj _ c c1), onel b hb _ _ (fun c => disj _ c2 c),
            asing _ (hzy u).symm, bsing] at tr
          exact Bool.noConfusion tr
        · exact Or.inr ⟨c1, c2⟩
      let sa := s.filter (fun u => xi u ∈ sup n S a)
      let sb := s.filter (fun u => xi u ∈ sup n S b)
      have mema : ∀ u ∈ sa, xi u ∈ sup n S a ∧ yi u ∈ sup n S a := by
        intro u hu
        have hu' := Finset.mem_filter.1 hu
        rcases tog u hu'.1 with c | c
        · exact c
        · exact (disj _ hu'.2 c.1).elim
      have memb : ∀ u ∈ sb, xi u ∈ sup n S b ∧ yi u ∈ sup n S b := by
        intro u hu
        have hu' := Finset.mem_filter.1 hu
        rcases tog u hu'.1 with c | c
        · exact (disj _ c.1 hu'.2).elim
        · exact c
      have tos : ∀ u ∈ s, ∀ i, (i = xi u ∨ i = yi u) → (i ∈ sup n S a → u ∈ sa) ∧ (i ∈ sup n S b → u ∈ sb) := by
        intro u hu i e
        constructor
        · intro hi
          refine Finset.mem_filter.2 ⟨hu, ?_⟩
          rcases tog u hu with c | c
          · exact c.1
          · rcases e with e | e
            · exact (disj _ (e ▸ hi) c.1).elim
            · exact (disj _ (e ▸ hi) c.2).elim
        · intro hi
          refine Finset.mem_filter.2 ⟨hu, ?_⟩
          rcases tog u hu with c | c
          · rcases e with e | e
            · exact (disj _ c.1 (e ▸ hi)).elim
            · exact (disj _ c.2 (e ▸ hi)).elim
          · exact c.1
      obtain ⟨Ma, hMa, sMa, va⟩ := ih a haw ha ma sa (by
          intro i
          constructor
          · intro hi
            rcases (hs i).1 ((hsup i).2 (Or.inl hi)) with e | ⟨u, hu, e⟩
            · exact Or.inl e
            · exact Or.inr ⟨u, (tos u hu i e).1 hi, e⟩
          · rintro (rfl | ⟨u, hu, rfl | rfl⟩)
            · exact hza
            · exact (mema u hu).1
            · exact (mema u hu).2) (by
          intro u hu v hv'
          have t := hval u (Finset.mem_filter.1 hu).1 v (Finset.mem_filter.1 hv').1
          rw [hv] at t
          have : V b (two (xi u) (yi v)) = false := by
            apply off H hb mb
            intro i hi
            have e1 : i ≠ xi u := fun e => disj _ (mema u hu).1 (e ▸ hi)
            have e2 : i ≠ yi v := fun e => disj _ (mema v hv').2 (e ▸ hi)
            simp [two, e1, e2]
          rw [this, Bool.or_false] at t
          exact t) asing az
      obtain ⟨Mb, hMb, sMb, vb⟩ := cls_id H xi yi hx hy hxy b hb mb sb (by
          intro i
          constructor
          · intro hi
            rcases (hs i).1 ((hsup i).2 (Or.inr hi)) with e | ⟨u, hu, e⟩
            · exact (zb (e ▸ hi)).elim
            · exact ⟨u, (tos u hu i e).2 hi, e⟩
          · rintro ⟨u, hu, rfl | rfl⟩
            · exact (memb u hu).1
            · exact (memb u hu).2) (by
          intro u hu v hv'
          have t := hval u (Finset.mem_filter.1 hu).1 v (Finset.mem_filter.1 hv').1
          rw [hv] at t
          have : V a (two (xi u) (yi v)) = false := by
            have e1 : xi u ∉ sup n S a := fun c => disj _ c (memb u hu).1
            have e2 : yi v ∉ sup n S a := fun c => disj _ c (memb v hv').2
            have : V a (two (xi u) (yi v)) = V a zero := by
              apply dep H a ha
              intro i hi
              have f1 : i ≠ xi u := fun e => e1 (e ▸ hi)
              have f2 : i ≠ yi v := fun e => e2 (e ▸ hi)
              simp [two, zero, f1, f2]
            rw [this, mono_zero H a ha ma]
          rw [this, Bool.false_or] at t
          exact t) bsing
      have hsplit : sa ∪ sb = s := by
        simp only [sa, sb]
        rw [← Finset.filter_or]
        apply Finset.filter_true_of_mem
        intro u hu
        exact inab u hu _ (Or.inl rfl)
      have hdj : Disjoint sa sb := by
        rw [Finset.disjoint_left]
        intro u h1 h2
        exact disj _ (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
      obtain ⟨hM, hMs⟩ := isM_union _ _ Ma Mb hMa hMb sMa sMb hdj
      rw [hsplit] at hMs
      refine ⟨Ma ∪ Mb, hM, hMs, ?_⟩
      intro f
      rw [hv, Bool.or_eq_true, va, vb, or_assoc, ← Pr_union, hsplit]
    rcases hv with hv | hv
    · exfalso
      rw [hv, Bool.and_eq_true] at hz
      have off1 : ∀ c ∈ T, (∀ v ∈ S c, ¬ N v) → z ∉ sup n S c → V c (only z) = false := by
        intro c hc mc hzc
        apply off H hc mc
        intro i hi
        have : i ≠ z := fun e => hzc (e ▸ hi)
        simp [only, this]
      by_cases c : z ∈ sup n S a
      · have := off1 b hb mb (disj z c)
        rw [hz.2] at this
        exact Bool.noConfusion this
      · have := off1 a ha ma c
        rw [hz.1] at this
        exact Bool.noConfusion this
    · rcases (hsup z).1 ((hs z).2 (Or.inl rfl)) with c | c
      · exact core a ha b hb haw hbw ma mb hsup disj hv c
      · exact core b hb a ha hbw haw mb ma (fun i => (hsup i).trans or_comm) (fun i x y => disj i y x)
          (fun f => by rw [hv, Bool.or_comm]) c

end classify

theorem no_crown {n : ℕ} {T : Finset ℕ} {V : ℕ → (ℕ → Bool) → Bool} {S : ℕ → Finset ℕ} {N : ℕ → Prop}
    (H : ∀ w ∈ T, Node n T V S N w) {k : ℕ} (hk : 3 ≤ k) (xi yi : Fin k → ℕ)
    (hx : ∀ u v, xi u = xi v → u = v) (hy : ∀ u v, yi u = yi v → u = v) (hxy : ∀ u v, xi u ≠ yi v)
    (z : ℕ) (hzx : ∀ u, z ≠ xi u) (hzy : ∀ u, z ≠ yi u) :
    ∀ w ∈ T, (∀ v ∈ S w, ¬ N v) →
      (∀ u v, V w (two (xi u) (yi v)) = decide (u ≠ v)) →
      (∀ u, V w (two (xi u) z) = true) → V w (only z) = false → False := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm hval hcol hz
    have p0 : 0 < k := by omega
    have p1 : 1 < k := by omega
    have p2 : 2 < k := by omega
    let i0 : Fin k := ⟨0, p0⟩
    let i1 : Fin k := ⟨1, p1⟩
    let i2 : Fin k := ⟨2, p2⟩
    have n01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have n02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    have n12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
    have sing : ∀ u, V w (only (xi u)) = false ∧ V w (only (yi u)) = false := by
      intro u
      have h0 : V w (two (xi u) (yi u)) = false := by
        rw [hval]
        simp
      constructor
      · by_contra c
        rw [Bool.not_eq_false] at c
        have := mono H w hw hm (only (xi u)) (two (xi u) (yi u)) (fun i hi => by
          simp only [only, two, decide_eq_true_eq] at hi ⊢
          exact Or.inl hi) c
        rw [h0] at this
        exact Bool.noConfusion this
      · by_contra c
        rw [Bool.not_eq_false] at c
        have := mono H w hw hm (only (yi u)) (two (xi u) (yi u)) (fun i hi => by
          simp only [only, two, decide_eq_true_eq] at hi ⊢
          exact Or.inr hi) c
        rw [h0] at this
        exact Bool.noConfusion this
    rcases H w hw with ⟨_, _, h3⟩ | ⟨h0, _, a, ha, b, hb, haw, hbw, hd, h, hv⟩ | ⟨_, hN, _⟩
    · have e1 := hval i0 i1
      have e2 := hval i1 i0
      rw [h3] at e1 e2
      simp only [two, n01, n01.symm, ne_eq, not_false_eq_true, decide_true, decide_eq_true_eq] at e1 e2
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
      · exact n01 (hx _ _ (e1.symm.trans e2))
      · exact hxy _ _ (e1.symm.trans e2)
      · exact hxy _ _ (e2.symm.trans e1)
      · exact n01 (hy _ _ (e2.symm.trans e1))
    swap
    · exact absurd hN (hm w (self_mem H w hw))
    have ma : ∀ v ∈ S a, ¬ N v := fun v hv => hm v (by rw [h]; simp [hv])
    have mb : ∀ v ∈ S b, ¬ N v := fun v hv => hm v (by rw [h]; simp [hv])
    have hsup := sup_bin (n := n) h h0
    have disj : ∀ i, i ∈ sup n S a → i ∈ sup n S b → False := fun i => sup_disj hd
    have onel : ∀ c ∈ T, ∀ p q : ℕ, q ∉ sup n S c → V c (two p q) = V c (only p) := by
      intro c hc p q hq
      apply dep H c hc
      intro i hi
      have e : i ≠ q := fun e => hq (e ▸ hi)
      simp [two, only, e]
    have oner : ∀ c ∈ T, ∀ p q : ℕ, p ∉ sup n S c → V c (two p q) = V c (only q) := by
      intro c hc p q hp
      apply dep H c hc
      intro i hi
      have e : i ≠ p := fun e => hp (e ▸ hi)
      simp [two, only, e]
    rcases hv with hv | hv
    · have nab : V a zero = false ∧ V b zero = false := ⟨mono_zero H a ha ma, mono_zero H b hb mb⟩
      have both : ∀ u v : Fin k, u ≠ v → V a (two (xi u) (yi v)) = true ∧ V b (two (xi u) (yi v)) = true := by
        intro u v huv
        have := hval u v
        rw [hv] at this
        simpa [huv] using this
      have one : ∀ c ∈ T, (∀ v ∈ S c, ¬ N v) → ∀ p q : ℕ, V c (two p q) = true →
          p ∈ sup n S c ∨ q ∈ sup n S c := by
        intro c hc mc p q ht
        by_contra c'
        rw [not_or] at c'
        have : V c (two p q) = false := by
          apply off H hc mc
          intro i hi
          have e1 : i ≠ p := fun e => c'.1 (e ▸ hi)
          have e2 : i ≠ q := fun e => c'.2 (e ▸ hi)
          simp [two, e1, e2]
        rw [this] at ht
        exact Bool.noConfusion ht
      have core : ∀ a ∈ T, ∀ b ∈ T, (∀ v ∈ S a, ¬ N v) → (∀ v ∈ S b, ¬ N v) →
          (∀ i, i ∈ sup n S a → i ∈ sup n S b → False) →
          (∀ u v : Fin k, u ≠ v → V a (two (xi u) (yi v)) = true ∧ V b (two (xi u) (yi v)) = true) →
          (∀ f, V w f = (V a f && V b f)) → xi i0 ∈ sup n S a → False := by
        intro a ha b hb ma mb disj both hv h0a
        have split : ∀ u v : Fin k, u ≠ v →
            (xi u ∈ sup n S a → yi v ∈ sup n S b) ∧ (yi v ∈ sup n S b → xi u ∈ sup n S a) := by
          intro u v huv
          have c1 := one a ha ma _ _ (both u v huv).1
          have c2 := one b hb mb _ _ (both u v huv).2
          constructor
          · intro h1
            rcases c2 with c2 | c2
            · exact (disj _ h1 c2).elim
            · exact c2
          · intro h2
            rcases c1 with c1 | c1
            · exact c1
            · exact (disj _ c1 h2).elim
        have y1 := (split i0 i1 n01).1 h0a
        have x2 := (split i2 i1 n12.symm).2 y1
        have y0 := (split i2 i0 n02.symm).1 x2
        have y2 := (split i0 i2 n02).1 h0a
        have x1 := (split i1 i2 n12).2 y2
        have e1 : V a (two (xi i0) (yi i0)) = true := by
          rw [onel a ha _ _ (fun c => disj _ c y0), ← onel a ha _ (yi i1) (fun c => disj _ c y1)]
          exact (both i0 i1 n01).1
        have e2 : V b (two (xi i0) (yi i0)) = true := by
          rw [oner b hb _ _ (fun c => disj _ h0a c), ← oner b hb (xi i1) _ (fun c => disj _ x1 c)]
          exact (both i1 i0 n01.symm).2
        have := hval i0 i0
        rw [hv, e1, e2] at this
        simp at this
      rcases one a ha ma _ _ (both i0 i1 n01).1 with c | c
      · exact core a ha b hb ma mb disj both hv c
      · have xb : xi i0 ∈ sup n S b := by
          rcases one b hb mb _ _ (both i0 i1 n01).2 with d | d
          · exact d
          · exact (disj _ c d).elim
        exact core b hb a ha mb ma (fun i x y => disj i y x) (fun u v huv => (both u v huv).symm)
          (fun f => by rw [hv, Bool.and_comm]) xb
    · have sa : ∀ i, V w (only i) = false → V a (only i) = false ∧ V b (only i) = false := by
        intro i hi
        rw [hv] at hi
        exact Bool.or_eq_false_iff.1 hi
      have same : ∀ c ∈ T, ∀ u v : Fin k, V c (two (xi u) (yi v)) = true → V c (only (xi u)) = false →
          V c (only (yi v)) = false → xi u ∈ sup n S c ∧ yi v ∈ sup n S c := by
        intro c hc u v ht h1 h2
        constructor
        · by_contra d
          rw [oner c hc _ _ d, h2] at ht
          exact Bool.noConfusion ht
        · by_contra d
          rw [onel c hc _ _ d, h1] at ht
          exact Bool.noConfusion ht
      have core : ∀ a ∈ T, ∀ b ∈ T, a < w → (∀ v ∈ S a, ¬ N v) → (∀ v ∈ S b, ¬ N v) →
          (∀ i, i ∈ sup n S a → i ∈ sup n S b → False) →
          (∀ f, V w f = (V a f || V b f)) → xi i0 ∈ sup n S a → False := by
        intro a ha b hb haw ma mb disj hv h0a
        have sa : ∀ i, V w (only i) = false → V a (only i) = false ∧ V b (only i) = false := by
          intro i hi
          rw [hv] at hi
          exact Bool.or_eq_false_iff.1 hi
        have link : ∀ u v : Fin k, u ≠ v → (xi u ∈ sup n S a ↔ yi v ∈ sup n S a) := by
          intro u v huv
          have t := hval u v
          rw [hv] at t
          simp only [huv, ne_eq, not_false_eq_true, decide_true, Bool.or_eq_true] at t
          rcases t with t | t
          · have := same a ha u v t (sa _ (sing u).1).1 (sa _ (sing v).2).1
            exact ⟨fun _ => this.2, fun _ => this.1⟩
          · have := same b hb u v t (sa _ (sing u).1).2 (sa _ (sing v).2).2
            exact ⟨fun c => (disj _ c this.1).elim, fun c => (disj _ c this.2).elim⟩
        have y1 := (link i0 i1 n01).1 h0a
        have x2 := (link i2 i1 n12.symm).2 y1
        have y0 := (link i2 i0 n02.symm).1 x2
        have y2 := (link i0 i2 n02).1 h0a
        have x1 := (link i1 i2 n12).2 y2
        have ally : ∀ v : Fin k, yi v ∈ sup n S a := by
          intro v
          by_cases c : v = i0
          · exact c ▸ y0
          · exact (link i0 v (Ne.symm c)).1 h0a
        have allx : ∀ u : Fin k, xi u ∈ sup n S a := by
          intro u
          by_cases c : u = i1
          · exact c ▸ x1
          · exact (link u i1 c).2 y1
        have xnb : ∀ u, xi u ∉ sup n S b := fun u c => disj _ (allx u) c
        have ynb : ∀ u, yi u ∉ sup n S b := fun u c => disj _ (ally u) c
        have znb : z ∉ sup n S b := by
          intro zb
          have t := hcol i0
          rw [hv, oner b hb _ _ (xnb i0), (sa z hz).2, Bool.or_false,
            onel a ha _ _ (fun c => disj _ c zb), (sa _ (sing i0).1).1] at t
          exact Bool.noConfusion t
        have bz : ∀ p q : ℕ, (p = z ∨ p ∉ sup n S b) → (q = z ∨ q ∉ sup n S b) → V b (two p q) = false := by
          intro p q hp hq
          apply off H hb mb
          intro i hi
          have e1 : i ≠ p := by
            intro e
            rcases hp with d | d
            · exact znb (d ▸ e ▸ hi)
            · exact d (e ▸ hi)
          have e2 : i ≠ q := by
            intro e
            rcases hq with d | d
            · exact znb (d ▸ e ▸ hi)
            · exact d (e ▸ hi)
          simp [two, e1, e2]
        apply ih a haw ha ma
        · intro u v
          have t := hval u v
          rw [hv, bz _ _ (Or.inr (xnb u)) (Or.inr (ynb v)), Bool.or_false] at t
          exact t
        · intro u
          have t := hcol u
          rw [hv, bz _ _ (Or.inr (xnb u)) (Or.inl rfl), Bool.or_false] at t
          exact t
        · exact (sa z hz).1
      have t := hval i0 i1
      rw [hv] at t
      simp only [n01, ne_eq, not_false_eq_true, decide_true, Bool.or_eq_true] at t
      rcases t with t | t
      · exact core a ha b hb haw ma mb disj hv
          (same a ha _ _ t (sa _ (sing i0).1).1 (sa _ (sing i1).2).1).1
      · exact core b hb a ha hbw mb ma (fun i x y => disj i y x) (fun f => by rw [hv, Bool.or_comm])
          (same b hb _ _ t (sa _ (sing i0).1).2 (sa _ (sing i1).2).2).1

section circ

variable (C : Circuit) (n : ℕ)

def val (o : ℕ) (f : ℕ → Bool) : Bool := value C (inp n f) o

theorem inp_len (f : ℕ → Bool) : (inp n f).length = n := by simp [inp]

theorem val_input (o : ℕ) (ho : o < n) (f : ℕ → Bool) : val C n o f = f o := by
  change (run C.gates (inp n f)).getD o false = f o
  rw [prefix_keep _ _ (by rw [inp_len]; exact ho)]
  simp [inp, List.getD_eq_getElem?_getD, ho]

theorem val_gate (o : ℕ) (ho : n ≤ o) (hj : o - n < C.gates.length) (f : ℕ → Bool) :
    val C n o f = (gateAt C n o).op.eval
      ((gateAt C n o).inputs.map fun i => if i < o then val C n i f else false) := by
  have hnw : n + (o - n) = o := by omega
  have := value_gate C (inp n f) (o - n) (by exact hj)
  rw [inp_len, hnw] at this
  rw [gateAt_eq C n hj]
  exact this

theorem val_out (o : ℕ) (ho : n + C.gates.length ≤ o) (f : ℕ → Bool) : val C n o f = false := by
  change (run C.gates (inp n f)).getD o false = false
  have : (run C.gates (inp n f)).length ≤ o := by
    rw [run_length, inp_len]
    exact ho
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.2 this]

theorem mem_ch {w i : ℕ} (hn : n ≤ w) (hj : w - n < C.gates.length) (hi : i ∈ reads C n w) (hiw : i < w) :
    i ∈ ch C n w := by
  unfold ch
  rw [if_pos ⟨hn, hj⟩, List.mem_filter]
  exact ⟨hi, by simpa using hiw⟩

theorem dep0 : ∀ w, ∀ f g : ℕ → Bool, (∀ i ∈ desc C n w, i < n → f i = g i) → val C n w f = val C n w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro f g h
    by_cases h1 : w < n
    · rw [val_input C n w h1, val_input C n w h1]
      exact h w (self_desc C n w) h1
    by_cases h2 : n + C.gates.length ≤ w
    · rw [val_out C n w h2, val_out C n w h2]
    have hn : n ≤ w := by omega
    have hj : w - n < C.gates.length := by omega
    rw [val_gate C n w hn hj, val_gate C n w hn hj]
    have key : ∀ i ∈ reads C n w, (if i < w then val C n i f else false) =
        (if i < w then val C n i g else false) := by
      intro i hi
      split
      · rename_i hiw
        have hc := mem_ch C n hn hj hi hiw
        apply ih i hiw
        intro v hv
        exact h v ((mem_desc C n w v).2 (Or.inr ⟨i, hc, hv⟩))
      · rfl
    unfold reads at key
    by_cases hop : (gateAt C n w).op = GateOp.not
    · rw [if_pos hop] at key
      rw [hop]
      cases hin : (gateAt C n w).inputs with
      | nil => rfl
      | cons a l =>
        rw [hin] at key
        have := key a (by simp)
        simp only [GateOp.eval, List.map_cons, List.headD_cons, this]
    · rw [if_neg hop] at key
      congr 1
      exact List.map_congr_left key

theorem mono0 (hg : GoodC C) : ∀ w, (∀ v ∈ desc C n w, ¬ isNot C n v) → ∀ f g : ℕ → Bool,
    (∀ i, f i = true → g i = true) → val C n w f = true → val C n w g = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hm f g hfg
    by_cases h1 : w < n
    · rw [val_input C n w h1, val_input C n w h1]
      exact hfg w
    by_cases h2 : n + C.gates.length ≤ w
    · rw [val_out C n w h2]
      exact fun h => (Bool.noConfusion h)
    have hn : n ≤ w := by omega
    have hj : w - n < C.gates.length := by omega
    rw [val_gate C n w hn hj, val_gate C n w hn hj]
    have hop : (gateAt C n w).op ≠ GateOp.not := fun c => hm w (self_desc C n w) ⟨hn, c⟩
    have hg' : (gateAt C n w).op = GateOp.and ∨ (gateAt C n w).op = GateOp.or := by
      rw [gateAt_eq C n hj] at hop ⊢
      rcases (hg _ (List.getElem_mem hj)).1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hop
    have key : ∀ i ∈ (gateAt C n w).inputs, (if i < w then val C n i f else false) = true →
        (if i < w then val C n i g else false) = true := by
      intro i hi
      split
      · rename_i hiw
        have hc : i ∈ ch C n w := mem_ch C n hn hj (by unfold reads; rw [if_neg hop]; exact hi) hiw
        apply ih i hiw _ f g hfg
        intro v hv
        exact hm v ((mem_desc C n w v).2 (Or.inr ⟨i, hc, hv⟩))
      · exact id
    rcases hg' with h | h <;> rw [h] <;>
      simp only [GateOp.eval, List.all_eq_true, List.any_eq_true, List.mem_map, id]
    · rintro p b ⟨i, hi, rfl⟩
      exact key i hi (p _ ⟨i, hi, rfl⟩)
    · rintro ⟨b, ⟨i, hi, rfl⟩, p⟩
      exact ⟨_, ⟨i, hi, rfl⟩, key i hi p⟩

theorem gates_le (o : ℕ) (ho : o < n + C.gates.length) : (gatesIn C n o).card ≤ C.gates.length := by
  have : gatesIn C n o ⊆ Finset.Ico n (n + C.gates.length) := by
    intro v hv
    have hv' := Finset.mem_filter.1 hv
    have := desc_le C n o v hv'.1
    rw [Finset.mem_Ico]
    exact ⟨hv'.2, by omega⟩
  have := Finset.card_le_card this
  rw [Nat.card_Ico] at this
  omega

theorem sup_eq_leaves (o : ℕ) : sup n (desc C n) o = leaves C n o := rfl

end circ

theorem class_id (k : ℕ) (hk : 2 ≤ k) (C : Circuit) (hg : GoodC C)
    (hmon : ∀ g ∈ C.gates, g.op ≠ GateOp.not) (hsize : C.gates.length + 1 ≤ 2 * k)
    (hrep : ∀ u v : Fin k, val C (k + k) C.output (two u.val (k + v.val)) = decide (u = v)) :
    ∃ M : Finset (Finset (Fin k)), IsM M ∧ ∀ f,
      (val C (k + k) C.output f = true ↔ Pr (fun u => u.val) (fun u => k + u.val) Finset.univ M f) := by
  have hnot : ∀ v, ¬ isNot C (k + k) v := by
    intro v h
    have h2 := h.2
    unfold gateAt at h2
    by_cases c : v - (k + k) < C.gates.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem c] at h2
      exact hmon _ (List.getElem_mem c) h2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.2 (by omega)] at h2
      exact GateOp.noConfusion h2
  have ho : C.output < k + k + C.gates.length := by
    by_contra c
    have := hrep ⟨0, by omega⟩ ⟨0, by omega⟩
    rw [val_out C _ _ (by omega)] at this
    simp at this
  have other : ∀ u : Fin k, ∃ w : Fin k, w ≠ u := by
    intro u
    by_cases c : u.val = 0
    · exact ⟨⟨1, by omega⟩, by simp [Fin.ext_iff, c]⟩
    · exact ⟨⟨0, by omega⟩, by simp [Fin.ext_iff, eq_comm, c]⟩
  have mo := mono0 C (k + k) hg C.output (fun v _ => hnot v)
  have fx : ∀ u : Fin k, val C (k + k) C.output (only u.val) = false ∧
      val C (k + k) C.output (only (k + u.val)) = false := by
    intro u
    obtain ⟨w, hw⟩ := other u
    constructor
    · by_contra c
      rw [Bool.not_eq_false] at c
      have := mo (only u.val) (two u.val (k + w.val)) (fun i hi => by
        simp only [only, two, decide_eq_true_eq] at hi ⊢
        exact Or.inl hi) c
      rw [hrep] at this
      simp [Ne.symm hw] at this
    · by_contra c
      rw [Bool.not_eq_false] at c
      have := mo (only (k + u.val)) (two w.val (k + u.val)) (fun i hi => by
        simp only [only, two, decide_eq_true_eq] at hi ⊢
        exact Or.inr hi) c
      rw [hrep] at this
      simp [hw] at this
  have hleaf : ∀ i < k + k, i ∈ desc C (k + k) C.output := by
    intro i hi
    by_contra c
    have key : ∀ u : Fin k, (i = u.val ∨ i = k + u.val) → False := by
      intro u e
      have h1 := hrep u u
      simp only [decide_true] at h1
      rcases e with e | e
      · have : val C (k + k) C.output (two u.val (k + u.val)) =
            val C (k + k) C.output (only (k + u.val)) := by
          apply dep0
          intro v hv _
          have : v ≠ u.val := fun d => c (e ▸ d ▸ hv)
          simp [two, only, this]
        rw [this, (fx u).2] at h1
        exact Bool.noConfusion h1
      · have : val C (k + k) C.output (two u.val (k + u.val)) = val C (k + k) C.output (only u.val) := by
          apply dep0
          intro v hv _
          have : v ≠ k + u.val := fun d => c (e ▸ d ▸ hv)
          simp [two, only, this]
        rw [this, (fx u).1] at h1
        exact Bool.noConfusion h1
    by_cases d : i < k
    · exact key ⟨i, d⟩ (Or.inl rfl)
    · exact key ⟨i - k, by omega⟩ (Or.inr (show i = k + (i - k) by omega))
  have hL : leaves C (k + k) C.output = Finset.range (k + k) := by
    ext i
    unfold leaves
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hleaf i h, h⟩⟩
  have hex : (gatesIn C (k + k) C.output).card + 1 ≤
      (leaves C (k + k) C.output).card + (nots C (k + k) C.output).card := by
    have := gates_le C (k + k) C.output ho
    rw [hL, Finset.card_range]
    omega
  have H := tree_nodes C (k + k) hg C.output ho hex
  have hs : sup (k + k) (desc C (k + k)) C.output = Finset.range (k + k) := hL
  have hself := self_desc C (k + k) C.output
  obtain ⟨M, hM, _, hv⟩ := cls_id H (fun u : Fin k => u.val) (fun u : Fin k => k + u.val)
    (fun u v h => Fin.ext h) (fun u v h => Fin.ext (by omega)) (fun u v h => by have := u.isLt; omega)
    C.output hself (fun v _ => hnot v) Finset.univ (by
      intro i
      rw [hs, Finset.mem_range]
      constructor
      · intro hi
        by_cases d : i < k
        · exact ⟨⟨i, d⟩, Finset.mem_univ _, Or.inl rfl⟩
        · exact ⟨⟨i - k, by omega⟩, Finset.mem_univ _, Or.inr (show i = k + (i - k) by omega)⟩
      · rintro ⟨u, _, rfl | rfl⟩ <;> have := u.isLt <;> omega)
    (fun u _ v _ => hrep u v)
    (by
      intro z
      change val C (k + k) C.output (only z) = false
      by_cases d : z < k
      · exact (fx ⟨z, d⟩).1
      by_cases e : z < k + k
      · have := (fx ⟨z - k, by omega⟩).2
        have ez : k + (z - k) = z := by omega
        simpa [ez] using this
      refine off H hself (fun v _ => hnot v) _ ?_
      intro i hi
      rw [hs, Finset.mem_range] at hi
      have : i ≠ z := by omega
      simp [only, this])
  exact ⟨M, hM, hv⟩

def Qc (k u v : ℕ) : Prop := u ≠ k + 1 ∧ ¬ (u < k ∧ u = v)

theorem rows_distinct (k : ℕ) (hk : 2 ≤ k) (u u' : ℕ) (hu : u < k + 2) (hu' : u' < k + 2)
    (h : ∀ v < k + 1, (Qc k u v ↔ Qc k u' v)) : u = u' := by
  unfold Qc at h
  by_contra c
  have hk0 := h k (by omega)
  by_cases a : u < k
  · have h1 := h u (by omega)
    omega
  by_cases b : u' < k
  · have h1 := h u' (by omega)
    omega
  omega

theorem cols_distinct (k : ℕ) (v v' : ℕ) (hv : v < k + 1) (hv' : v' < k + 1)
    (h : ∀ u < k + 2, (Qc k u v ↔ Qc k u v')) : v = v' := by
  unfold Qc at h
  by_contra c
  by_cases a : v < k
  · have h1 := h v (by omega)
    omega
  · have h1 := h v' (by omega)
    omega

theorem avoid (k : ℕ) (hk : 5 ≤ k) (a b c d : ℕ) : ∃ u, u < k ∧ u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ d := by
  have : ¬ Finset.range 5 ⊆ {a, b, c, d} := by
    intro h
    have h1 := Finset.card_le_card h
    have h2 : ({a, b, c, d} : Finset ℕ).card ≤ 4 := Finset.card_le_four
    rw [Finset.card_range] at h1
    omega
  rw [Finset.not_subset] at this
  obtain ⟨u, hu, hn⟩ := this
  rw [Finset.mem_range] at hu
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  exact ⟨u, by omega, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2⟩

theorem almost_all (m : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (h : ∀ a b, a < m → b < m → ¬ p a → ¬ p b → a = b) : m ≤ ((Finset.range m).filter p).card + 1 := by
  have h1 : ((Finset.range m).filter (fun a => ¬ p a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter, Finset.mem_range] at ha hb
    exact h a b ha.1 hb.1 ha.2 hb.2
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.range m) p
  rw [Finset.card_range] at h2
  omega

section single

variable (C : Circuit) (n o ν c : ℕ)
  (H : ∀ w ∈ desc C n o, Node n (desc C n o) (fun w f => value C (inp n f) w) (desc C n) (isNot C n) w)
  (huni : ∀ v ∈ desc C n o, isNot C n v → v = ν)
  (hν : isNot C n ν) (hc : c < ν) (hcT : c ∈ desc C n o)
  (hS : desc C n ν = insert ν (desc C n c))
  (hV : ∀ f, val C n ν f = !val C n c f)

include huni hc

theorem below_c : ∀ v ∈ desc C n c, v ∈ desc C n o → ¬ isNot C n v := by
  intro v hv hvo h
  have := huni v hvo h
  have := desc_le C n c v hv
  omega

theorem nonu {w : ℕ} (hw : w ∈ desc C n o) (h : ν ∉ desc C n w) : ∀ v ∈ desc C n w, ¬ isNot C n v := by
  intro v hv hn
  have := huni v (desc_trans C n o w hw hv) hn
  exact h (this ▸ hv)

include H hcT hS

theorem sup_c_sub {a : ℕ} (h : ν ∈ desc C n a) : ∀ i ∈ sup n (desc C n) c, i ∈ sup n (desc C n) a := by
  intro i hi
  have hi' := Finset.mem_filter.1 hi
  refine Finset.mem_filter.2 ⟨desc_trans C n a ν h ?_, hi'.2⟩
  rw [hS]
  exact Finset.mem_insert_of_mem hi'.1

theorem step_nu : ∀ w ∈ desc C n o, ν ∈ desc C n w → w ≠ ν →
    ∃ a ∈ desc C n o, ∃ b ∈ desc C n o, a < w ∧ ν ∈ desc C n a ∧ ν ∉ desc C n b ∧
      (∀ i ∈ sup n (desc C n) b, i ∉ sup n (desc C n) c) ∧
      (∀ i, i ∈ sup n (desc C n) w ↔ i ∈ sup n (desc C n) a ∨ i ∈ sup n (desc C n) b) ∧
      ((∀ f, val C n w f = (val C n a f && val C n b f)) ∨ ∀ f, val C n w f = (val C n a f || val C n b f)) := by
  intro w hw hνw hne
  have hlev := desc_le C n w ν hνw
  rcases H w hw with ⟨h1, h2, _⟩ | ⟨h0, _, a, ha, b, hb, haw, _, hd, h, hv⟩ | ⟨_, hN, _⟩
  · rw [h2, Finset.mem_singleton] at hνw
    exact absurd hνw.symm hne
  · have key : ∀ a ∈ desc C n o, ∀ b ∈ desc C n o, a < w → Disjoint (desc C n a) (desc C n b) →
        desc C n w = insert w (desc C n a ∪ desc C n b) → ν ∈ desc C n a →
        ((∀ f, val C n w f = (val C n a f && val C n b f)) ∨ ∀ f, val C n w f = (val C n a f || val C n b f)) →
        ∃ a ∈ desc C n o, ∃ b ∈ desc C n o, a < w ∧ ν ∈ desc C n a ∧ ν ∉ desc C n b ∧
          (∀ i ∈ sup n (desc C n) b, i ∉ sup n (desc C n) c) ∧
          (∀ i, i ∈ sup n (desc C n) w ↔ i ∈ sup n (desc C n) a ∨ i ∈ sup n (desc C n) b) ∧
          ((∀ f, val C n w f = (val C n a f && val C n b f)) ∨
            ∀ f, val C n w f = (val C n a f || val C n b f)) := by
      intro a ha b hb haw hd h hνa hv
      refine ⟨a, ha, b, hb, haw, hνa, Finset.disjoint_left.1 hd hνa, ?_, sup_bin h h0, hv⟩
      intro i hib hic
      exact sup_disj hd (sup_c_sub C n o ν c H huni hc hcT hS hνa i hic) hib
    rw [h, Finset.mem_insert, Finset.mem_union] at hνw
    rcases hνw with e | e | e
    · exact absurd e.symm hne
    · exact key a ha b hb haw hd h e hv
    · refine key b hb a ha (by assumption) hd.symm (by rw [h, Finset.union_comm]) e ?_
      rcases hv with hv | hv
      · exact Or.inl fun f => (hv f).trans (Bool.and_comm _ _)
      · exact Or.inr fun f => (hv f).trans (Bool.or_comm _ _)
  · have := huni w hw hN
    exact absurd this hne

include hV

theorem polar : ∀ w ∈ desc C n o, ν ∈ desc C n w → ∀ f g : ℕ → Bool,
    (∀ i, i ∉ sup n (desc C n) c → f i = true → g i = true) →
    (∀ i ∈ sup n (desc C n) c, g i = true → f i = true) →
    val C n w f = true → val C n w g = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hνw f g h1 h2
    by_cases e : w = ν
    · subst e
      rw [hV, hV]
      have mc : val C n c g = true → val C n c f = true := by
        intro hg
        let g' : ℕ → Bool := fun i => if i ∈ sup n (desc C n) c then g i else false
        have e1 : val C n c g = val C n c g' := by
          apply dep H c hcT
          intro i hi
          simp only [g', if_pos hi]
        apply mono H c hcT (fun v hv => below_c C n o _ c huni hc v hv (desc_trans C n o c hcT hv)) g' f _
          (e1.symm.trans hg)
        intro i hi
        simp only [g'] at hi
        split at hi
        · rename_i d
          exact h2 i d hi
        · exact Bool.noConfusion hi
      intro h
      cases hg : val C n c g
      · rfl
      · rw [mc hg] at h
        exact Bool.noConfusion h
    · obtain ⟨a, ha, b, hb, haw, hνa, hνb, hbc, _, hv⟩ :=
        step_nu C n o ν c H huni hc hcT hS w hw hνw e
      have ia := ih a haw ha hνa f g h1 h2
      have ib : val C n b f = true → val C n b g = true := by
        intro hf
        let f' : ℕ → Bool := fun i => if i ∈ sup n (desc C n) b then f i else false
        have e1 : val C n b f = val C n b f' := by
          apply dep H b hb
          intro i hi
          simp only [f', if_pos hi]
        apply mono H b hb (nonu C n o ν c huni hc hb hνb) f' g _ (e1.symm.trans hf)
        intro i hi
        simp only [f'] at hi
        split at hi
        · rename_i d
          exact h1 i (hbc i d) hi
        · exact Bool.noConfusion hi
      rcases hv with hv | hv <;> rw [hv, hv]
      · simp only [Bool.and_eq_true]
        exact fun p => ⟨ia p.1, ib p.2⟩
      · simp only [Bool.or_eq_true]
        exact fun p => p.imp ia ib

theorem bit : ∀ w ∈ desc C n o, ν ∈ desc C n w → ∀ f g : ℕ → Bool,
    (∀ i, i ∉ sup n (desc C n) c → f i = g i) → val C n c f = val C n c g →
    val C n w f = val C n w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hνw f g h1 h2
    by_cases e : w = ν
    · subst e
      rw [hV, hV, h2]
    · obtain ⟨a, ha, b, hb, haw, hνa, _, hbc, _, hv⟩ :=
        step_nu C n o ν c H huni hc hcT hS w hw hνw e
      have ia := ih a haw ha hνa f g h1 h2
      have ib : val C n b f = val C n b g := dep H b hb f g (fun i hi => h1 i (hbc i hi))
      rcases hv with hv | hv <;> rw [hv, hv, ia, ib]

omit hV in
theorem outside (hνo : ν ∈ desc C n o) (hne : o ≠ ν) :
    ∃ i ∈ sup n (desc C n) o, i ∉ sup n (desc C n) c := by
  obtain ⟨a, _, b, hb, _, _, _, hbc, hsup, _⟩ :=
    step_nu C n o ν c H huni hc hcT hS o (self_desc C n o) hνo hne
  obtain ⟨i, hi⟩ := sup_ne H b hb
  exact ⟨i, (hsup i).2 (Or.inr hi), hbc i hi⟩

end single

theorem class_crown (k : ℕ) (hk : 7 ≤ k) (C : Circuit) (hg : GoodC C) (hsize : C.gates.length ≤ 2 * k + 1)
    (hrep : ∀ u < k + 2, ∀ v < k + 1,
      (val C (k + 2 + (k + 1)) C.output (two u (k + 2 + v)) = true ↔ Qc k u v)) :
    ∃ M : Finset (Finset (Fin k)), IsM M ∧ ∀ f,
      (val C (k + 2 + (k + 1)) C.output f = true ↔
        ¬ (f (k + 1) = true ∨ Pr (fun u => u.val) (fun u => k + 2 + u.val) Finset.univ M f)) := by
  classical
  generalize hn : k + 2 + (k + 1) = n at hrep ⊢
  generalize ho' : C.output = o at hrep ⊢
  have ho : o < n + C.gates.length := by
    by_contra c
    have := (hrep 0 (by omega) 1 (by omega)).2 (by unfold Qc; omega)
    rw [val_out C _ _ (by omega)] at this
    exact Bool.noConfusion this
  have unx : ∀ u u', u < k + 2 → u' < k + 2 → u ∉ desc C n o → u' ∉ desc C n o → u = u' := by
    intro u u' hu hu' h1 h2
    apply rows_distinct k (by omega) u u' hu hu'
    intro v hv
    have drop : ∀ r, r ∉ desc C n o → val C n o (two r (k + 2 + v)) = val C n o (only (k + 2 + v)) := by
      intro r hr
      apply dep0
      intro i hi _
      have : i ≠ r := fun e => hr (e ▸ hi)
      simp [two, only, this]
    rw [← hrep u hu v hv, ← hrep u' hu' v hv, drop u h1, drop u' h2]
  have uny : ∀ v v', v < k + 1 → v' < k + 1 → k + 2 + v ∉ desc C n o → k + 2 + v' ∉ desc C n o → v = v' := by
    intro v v' hv hv' h1 h2
    apply cols_distinct k v v' hv hv'
    intro u hu
    have drop : ∀ r, r ∉ desc C n o → val C n o (two u r) = val C n o (only u) := by
      intro r hr
      apply dep0
      intro i hi _
      have : i ≠ r := fun e => hr (e ▸ hi)
      simp [two, only, this]
    rw [← hrep u hu v hv, ← hrep u hu v' hv', drop _ h1, drop _ h2]
  have xread := almost_all (k + 2) (fun u => u ∈ desc C n o) unx
  have yread := almost_all (k + 1) (fun v => k + 2 + v ∈ desc C n o) (fun a b ha hb => uny a b ha hb)
  have leafge : ∀ (X Y : Finset ℕ), (∀ u ∈ X, u < k + 2 ∧ u ∈ desc C n o) →
      (∀ v ∈ Y, v < k + 1 ∧ k + 2 + v ∈ desc C n o) → X.card + Y.card ≤ (leaves C n o).card := by
    intro X Y hX hY
    have e : (Y.image (fun v => k + 2 + v)).card = Y.card :=
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)
    rw [← e, ← Finset.card_union_of_disjoint]
    · apply Finset.card_le_card
      intro i hi
      unfold leaves
      rw [Finset.mem_filter]
      rcases Finset.mem_union.1 hi with h | h
      · exact ⟨(hX i h).2, by have := (hX i h).1; omega⟩
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
        exact ⟨(hY v hv).2, by have := (hY v hv).1; omega⟩
    · rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hi'
      have := (hX _ hi).1
      omega
  have lge : 2 * k + 1 ≤ (leaves C n o).card := by
    have := leafge ((Finset.range (k + 2)).filter (fun u => u ∈ desc C n o))
      ((Finset.range (k + 1)).filter (fun v => k + 2 + v ∈ desc C n o))
      (fun u hu => by simpa using hu) (fun v hv => by simpa using hv)
    omega
  have hgl := gates_le C n o ho
  have hcnt := count C n hg o
  have hself := self_desc C n o
  have z1 : ∀ u, u < k → (k + 1 ≠ u) := fun u hu => by omega
  by_cases hnots : nots C n o = ∅
  · exfalso
    have hnn : ∀ v ∈ desc C n o, ¬ isNot C n v := by
      intro v hv h
      have : v ∈ nots C n o := Finset.mem_filter.2 ⟨hv, h⟩
      rw [hnots] at this
      exact Finset.notMem_empty _ this
    have mo := mono0 C n hg o hnn
    have xr : ∀ u < k + 1, u ∈ desc C n o := by
      intro u hu
      by_contra hu0
      have h1 : ∀ u' < k + 2, ∀ v < k + 1, Qc k u v → Qc k u' v := by
        intro u' hu' v hv hq
        have h2 := (hrep u (by omega) v hv).2 hq
        have e : val C n o (two u (k + 2 + v)) = val C n o (only (k + 2 + v)) := by
          apply dep0
          intro i hi _
          have : i ≠ u := fun e => hu0 (e ▸ hi)
          simp [two, only, this]
        rw [e] at h2
        apply (hrep u' hu' v hv).1
        exact mo _ _ (fun i hi => by
          simp only [only, two, decide_eq_true_eq] at hi ⊢
          exact Or.inr hi) h2
      by_cases d : u < k
      · obtain ⟨w, hw, hwu, _⟩ := avoid k (by omega) u u u u
        have := h1 w (by omega) w (by omega) (by unfold Qc; omega)
        unfold Qc at this
        omega
      · have := h1 0 (by omega) 0 (by omega) (by unfold Qc; omega)
        unfold Qc at this
        omega
    have yr : ∀ v < k + 1, k + 2 + v ∈ desc C n o := by
      intro v hv
      by_contra hv0
      have h1 : ∀ v' < k + 1, ∀ u < k + 2, Qc k u v → Qc k u v' := by
        intro v' hv' u hu hq
        have h2 := (hrep u hu v hv).2 hq
        have e : val C n o (two u (k + 2 + v)) = val C n o (only u) := by
          apply dep0
          intro i hi _
          have : i ≠ k + 2 + v := fun e => hv0 (e ▸ hi)
          simp [two, only, this]
        rw [e] at h2
        apply (hrep u hu v' hv').1
        exact mo _ _ (fun i hi => by
          simp only [only, two, decide_eq_true_eq] at hi ⊢
          exact Or.inl hi) h2
      obtain ⟨w, hw, hwv, _⟩ := avoid k (by omega) v v v v
      have := h1 w (by omega) w (by omega) (by unfold Qc; omega)
      unfold Qc at this
      omega
    have := leafge (Finset.range (k + 1)) (Finset.range (k + 1))
      (fun u hu => by
        rw [Finset.mem_range] at hu
        exact ⟨by omega, xr u hu⟩)
      (fun v hv => by
        rw [Finset.mem_range] at hv
        exact ⟨hv, yr v hv⟩)
    rw [Finset.card_range] at this
    have hex : (gatesIn C n o).card + 1 ≤ (leaves C n o).card + (nots C n o).card := by omega
    have H := tree_nodes C n hg o ho hex
    refine no_crown H (k := k) (by omega) (fun u => u.val) (fun u => k + 2 + u.val)
      (fun u v h => Fin.ext h) (fun u v h => Fin.ext (by omega)) (fun u v h => by have := u.isLt; omega)
      (k + 2 + k) (fun u => by have := u.isLt; omega) (fun u => by have := u.isLt; omega)
      o hself hnn ?_ ?_ ?_
    · intro u v
      change val C n o (two u.val (k + 2 + v.val)) = _
      have hu := u.isLt
      have hv := v.isLt
      rw [Bool.eq_iff_iff, hrep _ (by omega) _ (by omega), decide_eq_true_eq]
      unfold Qc
      simp only [ne_eq, Fin.ext_iff]
      omega
    · intro u
      change val C n o (two u.val (k + 2 + k)) = true
      have hu := u.isLt
      rw [hrep _ (by omega) _ (by omega)]
      unfold Qc
      omega
    · change val C n o (only (k + 2 + k)) = false
      by_contra d
      rw [Bool.not_eq_false] at d
      have := (hrep (k + 1) (by omega) k (by omega)).1 (mo _ _ (fun i hi => by
        simp only [only, two, decide_eq_true_eq] at hi ⊢
        exact Or.inr hi) d)
      unfold Qc at this
      omega
  have hpos : 0 < (nots C n o).card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hnots)
  have hex : (gatesIn C n o).card + 1 ≤ (leaves C n o).card + (nots C n o).card := by omega
  have hone : (nots C n o).card = 1 := by omega
  have H := tree_nodes C n hg o ho hex
  obtain ⟨ν, hν⟩ := Finset.card_eq_one.1 hone
  have hνm : ν ∈ nots C n o := by
    rw [hν]
    exact Finset.mem_singleton_self _
  obtain ⟨hνo, hνn⟩ := Finset.mem_filter.1 hνm
  have huni : ∀ v ∈ desc C n o, isNot C n v → v = ν := by
    intro v hv h
    have : v ∈ nots C n o := Finset.mem_filter.2 ⟨hv, h⟩
    rwa [hν, Finset.mem_singleton] at this
  have hnode : ∃ c ∈ desc C n o, c < ν ∧ desc C n ν = insert ν (desc C n c) ∧
      ∀ f, val C n ν f = !val C n c f := by
    rcases H ν hνo with ⟨h1, _⟩ | ⟨_, h, _⟩ | ⟨_, _, c, hcT, hcν, hS, hV⟩
    · have := hνn.1
      omega
    · exact absurd hνn h
    · exact ⟨c, hcT, hcν, hS, hV⟩
  obtain ⟨c, hcT, hcν, hS, hV⟩ := hnode
  have csub : ∀ i ∈ sup n (desc C n) c, i ∈ sup n (desc C n) o :=
    sup_c_sub C n o ν c H huni hcν hcT hS hνo
  have memsup : ∀ i, i ∈ sup n (desc C n) o ↔ i ∈ desc C n o ∧ i < n := fun i => Finset.mem_filter
  have pol := polar C n o ν c H huni hcν hcT hS hV o hself hνo
  have bt := bit C n o ν c H huni hcν hcT hS hV o hself hνo
  have hroot : o = ν := by
    by_contra hne
    obtain ⟨z, hzo, hzc⟩ := outside C n o ν c H huni hcν hcT hS hνo hne
    obtain ⟨i, hi⟩ := sup_ne H c hcT
    have xpos : ∀ u v : ℕ, u ∉ sup n (desc C n) c → val C n o (only (k + 2 + v)) = true →
        val C n o (two u (k + 2 + v)) = true := by
      intro u v hu h
      refine pol _ _ (fun j _ hj => ?_) (fun j hj h2 => ?_) h
      · simp only [only, two, decide_eq_true_eq] at hj ⊢
        exact Or.inr hj
      · simp only [only, two, decide_eq_true_eq] at h2 ⊢
        rcases h2 with e | e
        · exact absurd (e ▸ hj) hu
        · exact e
    have xneg : ∀ u v : ℕ, u ∈ sup n (desc C n) c → val C n o (two u (k + 2 + v)) = true →
        val C n o (only (k + 2 + v)) = true := by
      intro u v hu h
      refine pol _ _ (fun j hj h2 => ?_) (fun j _ h2 => ?_) h
      · simp only [only, two, decide_eq_true_eq] at h2 ⊢
        rcases h2 with e | e
        · exact absurd (e ▸ hu) hj
        · exact e
      · simp only [only, two, decide_eq_true_eq] at h2 ⊢
        exact Or.inr h2
    have ypos : ∀ u v : ℕ, k + 2 + v ∉ sup n (desc C n) c → val C n o (only u) = true →
        val C n o (two u (k + 2 + v)) = true := by
      intro u v hv h
      refine pol _ _ (fun j _ hj => ?_) (fun j hj h2 => ?_) h
      · simp only [only, two, decide_eq_true_eq] at hj ⊢
        exact Or.inl hj
      · simp only [only, two, decide_eq_true_eq] at h2 ⊢
        rcases h2 with e | e
        · exact e
        · exact absurd (e ▸ hj) hv
    have yneg : ∀ u v : ℕ, k + 2 + v ∈ sup n (desc C n) c → val C n o (two u (k + 2 + v)) = true →
        val C n o (only u) = true := by
      intro u v hv h
      refine pol _ _ (fun j hj h2 => ?_) (fun j _ h2 => ?_) h
      · simp only [only, two, decide_eq_true_eq] at h2 ⊢
        rcases h2 with e | e
        · exact e
        · exact absurd (e ▸ hv) hj
      · simp only [only, two, decide_eq_true_eq] at h2 ⊢
        exact Or.inl h2
    have r1 : ∀ u v : ℕ, u < k + 2 → v < k + 1 → Qc k u v → val C n o (two u (k + 2 + v)) = true :=
      fun u v hu hv h => (hrep u hu v hv).2 h
    have r0 : ∀ u : ℕ, u < k → val C n o (two u (k + 2 + u)) = false := by
      intro u hu
      rw [Bool.eq_false_iff]
      intro h
      have := (hrep u (by omega) u (by omega)).1 h
      unfold Qc at this
      omega
    have rz : ∀ v : ℕ, v < k + 1 → val C n o (two (k + 1) (k + 2 + v)) = false := by
      intro v hv
      rw [Bool.eq_false_iff]
      intro h
      have := (hrep (k + 1) (by omega) v hv).1 h
      unfold Qc at this
      omega
    have missx : ∃ m, ∀ u < k + 2, u ≠ m → u ∈ desc C n o := by
      by_cases h : ∃ m < k + 2, m ∉ desc C n o
      · obtain ⟨m, hm, hm'⟩ := h
        refine ⟨m, fun u hu hne => ?_⟩
        by_contra d
        exact hne (unx u m hu hm d hm')
      · refine ⟨0, fun u hu _ => ?_⟩
        by_contra d
        exact h ⟨u, hu, d⟩
    have missy : ∃ m, ∀ v < k + 1, v ≠ m → k + 2 + v ∈ desc C n o := by
      by_cases h : ∃ m < k + 1, k + 2 + m ∉ desc C n o
      · obtain ⟨m, hm, hm'⟩ := h
        refine ⟨m, fun v hv hne => ?_⟩
        by_contra d
        exact hne (uny v m hv hm d hm')
      · refine ⟨0, fun v hv _ => ?_⟩
        by_contra d
        exact h ⟨v, hv, d⟩
    obtain ⟨mx, hmx⟩ := missx
    obtain ⟨my, hmy⟩ := missy
    have xin : ∀ u < k, u ≠ mx → u ∈ sup n (desc C n) o := fun u hu h =>
      (memsup u).2 ⟨hmx u (by omega) h, by omega⟩
    have yin : ∀ v < k, v ≠ my → k + 2 + v ∈ sup n (desc C n) o := fun v hv h =>
      (memsup _).2 ⟨hmy v (by omega) h, by omega⟩
    have samex : ∀ u w, u < k → w < k → u ≠ w → u ∉ sup n (desc C n) c → w ∈ sup n (desc C n) c → False := by
      intro u w hu hw huw h1 h2
      have a := r1 w u (by omega) (by omega) (by unfold Qc; omega)
      have b := xpos u u h1 (xneg w u h2 a)
      rw [r0 u hu] at b
      exact Bool.noConfusion b
    have samey : ∀ v w, v < k → w < k → v ≠ w → k + 2 + v ∉ sup n (desc C n) c →
        k + 2 + w ∈ sup n (desc C n) c → False := by
      intro v w hv hw hvw h1 h2
      have a := r1 v w (by omega) (by omega) (by unfold Qc; omega)
      have b := ypos v v h1 (yneg v w h2 a)
      rw [r0 v hv] at b
      exact Bool.noConfusion b
    let px : Prop := ∃ u < k, u ≠ mx ∧ u ∈ sup n (desc C n) c
    let py : Prop := ∃ v < k, v ≠ my ∧ k + 2 + v ∈ sup n (desc C n) c
    have allx : px → ∀ u < k, u ≠ mx → u ∈ sup n (desc C n) c := by
      rintro ⟨w, hw, _, hwc⟩ u hu _
      by_contra d
      exact samex u w hu hw (fun e => d (e ▸ hwc)) d hwc
    have ally : py → ∀ v < k, v ≠ my → k + 2 + v ∈ sup n (desc C n) c := by
      rintro ⟨w, hw, _, hwc⟩ v hv _
      by_contra d
      exact samey v w hv hw (fun e => d (e ▸ hwc)) d hwc
    have nox : ¬ px → ∀ u < k, u ∉ sup n (desc C n) c := by
      intro h u hu d
      have : u ≠ mx := by
        intro e
        have h1 := (memsup u).1 (csub u d)
        have h2 : ∃ w < k, w ≠ mx := by
          obtain ⟨w, hw, hwm, _⟩ := avoid k (by omega) mx mx mx mx
          exact ⟨w, hw, hwm⟩
        obtain ⟨w, hw, hwm⟩ := h2
        have hwc : w ∉ sup n (desc C n) c := fun e' => h ⟨w, hw, hwm, e'⟩
        exact samex w u hw hu (by omega) hwc d
      exact h ⟨u, hu, this, d⟩
    have noy : ¬ py → ∀ v < k, k + 2 + v ∉ sup n (desc C n) c := by
      intro h v hv d
      have : v ≠ my := by
        intro e
        obtain ⟨w, hw, hwm, _⟩ := avoid k (by omega) my my my my
        have hwc : k + 2 + w ∉ sup n (desc C n) c := fun e' => h ⟨w, hw, hwm, e'⟩
        exact samey w v hw hv (by omega) hwc d
      exact h ⟨v, hv, this, d⟩
    have zform : ∀ j, j ∈ sup n (desc C n) o → j < k + 2 ∨ ∃ v < k + 1, j = k + 2 + v := by
      intro j hj
      have := ((memsup j).1 hj).2
      by_cases d : j < k + 2
      · exact Or.inl d
      · exact Or.inr ⟨j - (k + 2), by omega, by omega⟩
    have cread : ∀ j, j ∈ sup n (desc C n) o → j ∈ desc C n o := fun j hj => ((memsup j).1 hj).1
    by_cases hpx : px <;> by_cases hpy : py
    · have z0 : ∀ j < k + 1, val C n o (only (k + 2 + j)) = true := by
        intro j hj
        obtain ⟨w, hw, hwm, hwj, _⟩ := avoid k (by omega) mx j j j
        exact xneg w j (allx hpx w hw hwm) (r1 w j (by omega) hj (by unfold Qc; omega))
      have c0 : ∀ i < k + 2, i ≠ k + 1 → val C n o (only i) = true := by
        intro i hi hik
        obtain ⟨w, hw, hwm, hwi, _⟩ := avoid k (by omega) my i i i
        exact yneg i w (ally hpy w hw hwm) (r1 i w hi (by omega) (by unfold Qc; omega))
      rcases zform z hzo with hz | ⟨t, ht, rfl⟩
      · by_cases d : z < k
        · by_cases e : z = mx
          · obtain ⟨w, hw, hwm, _⟩ := avoid k (by omega) mx mx mx mx
            exact samex z w d hw (by omega) hzc (allx hpx w hw hwm)
          · exact hzc (allx hpx z d e)
        by_cases e : z = k
        · subst e
          have row : mx = z := by
            have hmxlt : mx < z + 2 := by
              by_contra g
              have h1 : ∀ u < z + 2, u ∈ desc C n o := fun u hu => hmx u hu (by omega)
              have := leafge (Finset.range (z + 2))
                ((Finset.range (z + 1)).filter (fun v => z + 2 + v ∈ desc C n o))
                (fun u hu => by
                  rw [Finset.mem_range] at hu
                  exact ⟨hu, h1 u hu⟩)
                (fun v hv => by simpa using hv)
              rw [Finset.card_range] at this
              omega
            by_cases g : mx ∈ desc C n o
            · have h1 : ∀ u < z + 2, u ∈ desc C n o := fun u hu => by
                by_cases e : u = mx
                · exact e ▸ g
                · exact hmx u hu e
              have := leafge (Finset.range (z + 2))
                ((Finset.range (z + 1)).filter (fun v => z + 2 + v ∈ desc C n o))
                (fun u hu => by
                  rw [Finset.mem_range] at hu
                  exact ⟨hu, h1 u hu⟩)
                (fun v hv => by simpa using hv)
              rw [Finset.card_range] at this
              omega
            apply rows_distinct z (by omega) mx z hmxlt (by omega)
            intro v hv
            have e1 : val C n o (two mx (z + 2 + v)) = val C n o (only (z + 2 + v)) := by
              apply dep0
              intro i hi _
              have : i ≠ mx := fun e => g (e ▸ hi)
              simp [two, only, this]
            rw [← hrep mx hmxlt v hv, ← hrep z (by omega) v hv, e1, z0 v hv,
              r1 z v (by omega) hv (by unfold Qc; omega)]
          obtain ⟨g1, _⟩ := (memsup z).1 hzo
          have : ∀ u < z + 2, u ∈ desc C n o := fun u hu => by
            by_cases e : u = z
            · exact e ▸ g1
            · exact hmx u hu (by omega)
          have := leafge (Finset.range (z + 2))
            ((Finset.range (z + 1)).filter (fun v => z + 2 + v ∈ desc C n o))
            (fun u hu => by
              rw [Finset.mem_range] at hu
              exact ⟨hu, this u hu⟩)
            (fun v hv => by simpa using hv)
          rw [Finset.card_range] at this
          omega
        have ez : z = k + 1 := by omega
        have a := xpos z 0 hzc (z0 0 (by omega))
        rw [ez, rz 0 (by omega)] at a
        exact Bool.noConfusion a
      · by_cases d : t < k
        · by_cases e : t = my
          · obtain ⟨w, hw, hwm, _⟩ := avoid k (by omega) my my my my
            exact samey t w d hw (by omega) hzc (ally hpy w hw hwm)
          · exact hzc (ally hpy t d e)
        have et : t = k := by omega
        subst et
        have col : ∀ i < t + 2, (val C n o (only i) = true ↔ Qc t i t) := by
          intro i hi
          by_cases e : i = t + 1
          · have hf : val C n o (only i) = false := by
              rw [Bool.eq_false_iff]
              intro h
              have a := ypos i t hzc h
              rw [e, rz t (by omega)] at a
              exact Bool.noConfusion a
            rw [hf]
            unfold Qc
            simp [e]
          · rw [c0 i hi e]
            unfold Qc
            exact ⟨fun _ => by omega, fun _ => rfl⟩
        have g1 := cread _ hzo
        have miss : ∃ v < t + 1, t + 2 + v ∉ desc C n o := by
          by_contra g
          have h1 : ∀ v < t + 1, t + 2 + v ∈ desc C n o := fun v hv => by
            by_contra d'
            exact g ⟨v, hv, d'⟩
          have := leafge ((Finset.range (t + 2)).filter (fun u => u ∈ desc C n o)) (Finset.range (t + 1))
            (fun u hu => by simpa using hu)
            (fun v hv => by
              rw [Finset.mem_range] at hv
              exact ⟨hv, h1 v hv⟩)
          rw [Finset.card_range] at this
          omega
        obtain ⟨m, hm, hm'⟩ := miss
        have : m = t := by
          apply cols_distinct t m t hm (by omega)
          intro u hu
          have e1 : val C n o (two u (t + 2 + m)) = val C n o (only u) := by
            apply dep0
            intro i hi _
            have : i ≠ t + 2 + m := fun e => hm' (e ▸ hi)
            simp [two, only, this]
          rw [← hrep u hu m hm, e1, col u hu]
        exact hm' (this ▸ g1)
    · obtain ⟨a, ha, ham, _⟩ := avoid k (by omega) mx mx mx mx
      obtain ⟨b, hb, hbm, hba, _⟩ := avoid k (by omega) mx a a a
      obtain ⟨d, hd, hdm, hda, hdb, _⟩ := avoid k (by omega) mx a b b
      have ync : ∀ j < k, k + 2 + j ∉ sup n (desc C n) c := noy hpy
      have eqc : ∀ u j, j < k → val C n c (two u (k + 2 + j)) = val C n c (only u) := by
        intro u j hj
        apply dep H c hcT
        intro i hi
        have : i ≠ k + 2 + j := fun e => ync j hj (e ▸ hi)
        simp [two, only, this]
      have pig : ∀ u w, u < k → w < k → u ≠ w → u ≠ mx → w ≠ mx →
          val C n c (only u) = val C n c (only w) → False := by
        intro u w hu hw huw hum hwm h
        have uc := allx hpx u hu hum
        have wc := allx hpx w hw hwm
        have key : val C n o (two u (k + 2 + u)) = val C n o (two w (k + 2 + u)) := by
          apply bt
          · intro i hi
            have e1 : i ≠ u := fun e => hi (e ▸ uc)
            have e2 : i ≠ w := fun e => hi (e ▸ wc)
            simp [two, e1, e2]
          · rw [eqc u u hu, eqc w u hu, h]
        rw [r0 u hu, r1 w u (by omega) (by omega) (by unfold Qc; omega)] at key
        exact Bool.noConfusion key
      have three : ∀ p q r : Bool, p = q ∨ p = r ∨ q = r := by decide
      rcases three (val C n c (only a)) (val C n c (only b)) (val C n c (only d)) with h | h | h
      · exact pig a b ha hb hba.symm ham hbm h
      · exact pig a d ha hd hda.symm ham hdm h
      · exact pig b d hb hd hdb.symm hbm hdm h
    · obtain ⟨a, ha, ham, _⟩ := avoid k (by omega) my my my my
      obtain ⟨b, hb, hbm, hba, _⟩ := avoid k (by omega) my a a a
      obtain ⟨d, hd, hdm, hda, hdb, _⟩ := avoid k (by omega) my a b b
      have xnc : ∀ j < k, j ∉ sup n (desc C n) c := nox hpx
      have eqc : ∀ v j, j < k → val C n c (two j (k + 2 + v)) = val C n c (only (k + 2 + v)) := by
        intro v j hj
        apply dep H c hcT
        intro i hi
        have : i ≠ j := fun e => xnc j hj (e ▸ hi)
        simp [two, only, this]
      have pig : ∀ u w, u < k → w < k → u ≠ w → u ≠ my → w ≠ my →
          val C n c (only (k + 2 + u)) = val C n c (only (k + 2 + w)) → False := by
        intro u w hu hw huw hum hwm h
        have uc := ally hpy u hu hum
        have wc := ally hpy w hw hwm
        have key : val C n o (two u (k + 2 + u)) = val C n o (two u (k + 2 + w)) := by
          apply bt
          · intro i hi
            have e1 : i ≠ k + 2 + u := fun e => hi (e ▸ uc)
            have e2 : i ≠ k + 2 + w := fun e => hi (e ▸ wc)
            simp [two, e1, e2]
          · rw [eqc u u hu, eqc w u hu, h]
        rw [r0 u hu, r1 u w (by omega) (by omega) (by unfold Qc; omega)] at key
        exact Bool.noConfusion key
      have three : ∀ p q r : Bool, p = q ∨ p = r ∨ q = r := by decide
      rcases three (val C n c (only (k + 2 + a))) (val C n c (only (k + 2 + b)))
          (val C n c (only (k + 2 + d))) with h | h | h
      · exact pig a b ha hb hba.symm ham hbm h
      · exact pig a d ha hd hda.symm ham hdm h
      · exact pig b d hb hd hdb.symm hbm hdm h
    · have xnc : ∀ j < k, j ∉ sup n (desc C n) c := nox hpx
      have ync : ∀ j < k, k + 2 + j ∉ sup n (desc C n) c := noy hpy
      have nk : k ∉ sup n (desc C n) c := by
        intro h
        obtain ⟨j, hj, hjm, _⟩ := avoid k (by omega) mx mx mx mx
        have a := xneg k j h (r1 k j (by omega) (by omega) (by unfold Qc; omega))
        have b := xpos j j (xnc j hj) a
        rw [r0 j hj] at b
        exact Bool.noConfusion b
      have nyk : k + 2 + k ∉ sup n (desc C n) c := by
        intro h
        obtain ⟨j, hj, hjm, _⟩ := avoid k (by omega) my my my my
        have a := yneg j k h (r1 j k (by omega) (by omega) (by unfold Qc; omega))
        have b := ypos j j (ync j hj) a
        rw [r0 j hj] at b
        exact Bool.noConfusion b
      have hik : i = k + 1 := by
        rcases zform i (csub i hi) with h | ⟨t, ht, rfl⟩
        · by_cases d : i < k
          · exact absurd hi (xnc i d)
          by_cases e : i = k
          · exact absurd (e ▸ hi) nk
          omega
        · by_cases d : t < k
          · exact absurd hi (ync t d)
          have : t = k := by omega
          exact absurd (this ▸ hi) nyk
      have g1 := cread _ (csub i hi)
      rw [hik] at g1
      have z0 : ∀ j < k, j ≠ mx → val C n o (only (k + 2 + j)) = false := by
        intro j hj hjm
        rw [Bool.eq_false_iff]
        intro h
        have a := xpos j j (xnc j hj) h
        rw [r0 j hj] at a
        exact Bool.noConfusion a
      have miss : ∃ m < k + 2, m ∉ desc C n o := by
        by_contra g
        have h1 : ∀ u < k + 2, u ∈ desc C n o := fun u hu => by
          by_contra d'
          exact g ⟨u, hu, d'⟩
        have := leafge (Finset.range (k + 2))
          ((Finset.range (k + 1)).filter (fun v => k + 2 + v ∈ desc C n o))
          (fun u hu => by
            rw [Finset.mem_range] at hu
            exact ⟨hu, h1 u hu⟩)
          (fun v hv => by simpa using hv)
        rw [Finset.card_range] at this
        omega
      obtain ⟨m, hm, hm'⟩ := miss
      have mrow : ∀ v < k + 1, (val C n o (only (k + 2 + v)) = true ↔ Qc k m v) := by
        intro v hv
        have e1 : val C n o (two m (k + 2 + v)) = val C n o (only (k + 2 + v)) := by
          apply dep0
          intro i hi _
          have : i ≠ m := fun e => hm' (e ▸ hi)
          simp [two, only, this]
        rw [← e1, hrep m hm v hv]
      have mne : m ≠ k + 1 := fun e => hm' (e ▸ g1)
      by_cases d : m < k
      · obtain ⟨j, hj, hjm, hjm', _⟩ := avoid k (by omega) mx m m m
        have a := (mrow j (by omega)).2 (by unfold Qc; omega)
        rw [z0 j hj hjm] at a
        exact Bool.noConfusion a
      · obtain ⟨j, hj, hjm, _⟩ := avoid k (by omega) mx mx mx mx
        have a := (mrow j (by omega)).2 (by unfold Qc; omega)
        rw [z0 j hj hjm] at a
        exact Bool.noConfusion a
  subst hroot
  have hFG : ∀ f, val C n o f = !val C n c f := hV
  have cmon : ∀ v ∈ desc C n c, ¬ isNot C n v := fun v hv =>
    below_c C n o o c huni hcν v hv (desc_trans C n o c hcT hv)
  have supc : sup n (desc C n) c = sup n (desc C n) o := (sup_un hS hνn.1).symm
  have mc := mono H c hcT cmon
  have G : ∀ u < k + 2, ∀ v < k + 1, (val C n c (two u (k + 2 + v)) = true ↔ ¬ Qc k u v) := by
    intro u hu v hv
    rw [← hrep u hu v hv, hFG]
    cases val C n c (two u (k + 2 + v)) <;> simp
  have notin : ∀ i, i < n → i ∉ desc C n o → i ∉ sup n (desc C n) c := by
    intro i _ h d
    rw [supc] at d
    exact h ((memsup i).1 d).1
  have gdrop : ∀ r s, r ∉ sup n (desc C n) c → val C n c (two r s) = val C n c (only s) := by
    intro r s hr
    apply dep H c hcT
    intro i hi
    have : i ≠ r := fun e => hr (e ▸ hi)
    simp [two, only, this]
  have gdrop' : ∀ r s, s ∉ sup n (desc C n) c → val C n c (two r s) = val C n c (only r) := by
    intro r s hs
    apply dep H c hcT
    intro i hi
    have : i ≠ s := fun e => hs (e ▸ hi)
    simp [two, only, this]
  have up1 : ∀ a b, val C n c (only a) = true → val C n c (two a b) = true := fun a b h =>
    mc _ _ (fun i hi => by
      simp only [only, two, decide_eq_true_eq] at hi ⊢
      exact Or.inl hi) h
  have up2 : ∀ a b, val C n c (only b) = true → val C n c (two a b) = true := fun a b h =>
    mc _ _ (fun i hi => by
      simp only [only, two, decide_eq_true_eq] at hi ⊢
      exact Or.inr hi) h
  have xk : ∃ m < k + 2, m ∉ desc C n o := by
    by_contra g
    have h1 : ∀ u < k + 2, u ∈ desc C n o := fun u hu => by
      by_contra d'
      exact g ⟨u, hu, d'⟩
    have := leafge (Finset.range (k + 2))
      ((Finset.range (k + 1)).filter (fun v => k + 2 + v ∈ desc C n o))
      (fun u hu => by
        rw [Finset.mem_range] at hu
        exact ⟨hu, h1 u hu⟩)
      (fun v hv => by simpa using hv)
    rw [Finset.card_range] at this
    omega
  have yk : ∃ m < k + 1, k + 2 + m ∉ desc C n o := by
    by_contra g
    have h1 : ∀ v < k + 1, k + 2 + v ∈ desc C n o := fun v hv => by
      by_contra d'
      exact g ⟨v, hv, d'⟩
    have := leafge ((Finset.range (k + 2)).filter (fun u => u ∈ desc C n o)) (Finset.range (k + 1))
      (fun u hu => by simpa using hu)
      (fun v hv => by
        rw [Finset.mem_range] at hv
        exact ⟨hv, h1 v hv⟩)
    rw [Finset.card_range] at this
    omega
  obtain ⟨mx, hmx, hmx'⟩ := xk
  obtain ⟨my, hmy, hmy'⟩ := yk
  have emx : mx = k := by
    have hz : ∀ v < k + 1, ¬ Qc k mx v → ¬ Qc k k v := by
      intro v hv h
      have a := (G mx hmx v hv).2 h
      rw [gdrop _ _ (notin mx (by omega) hmx')] at a
      exact (G k (by omega) v hv).1 (up2 k _ a)
    have allq : ∀ v < k + 1, Qc k mx v := by
      intro v hv
      by_contra d
      apply hz v hv d
      unfold Qc
      omega
    by_contra d
    by_cases e : mx < k
    · have := allq mx (by omega)
      unfold Qc at this
      omega
    · have := allq 0 (by omega)
      unfold Qc at this
      omega
  have emy : my = k := by
    by_contra d
    have hmyk : my < k := by omega
    have a := (G my (by omega) my hmy).2 (by unfold Qc; omega)
    rw [gdrop' _ _ (notin _ (by omega) hmy')] at a
    obtain ⟨w, hw, hwm, _⟩ := avoid k (by omega) my my my my
    have b := (G my (by omega) w (by omega)).1 (up1 my _ a)
    apply b
    unfold Qc
    omega
  subst mx
  subst my
  have xin : ∀ u < k + 2, u ≠ k → u ∈ desc C n o := fun u hu h => by
    by_contra d
    exact h (unx u k hu (by omega) d hmx')
  have yin : ∀ v < k, k + 2 + v ∈ desc C n o := fun v hv => by
    by_contra d
    have := uny v k (by omega) (by omega) d hmy'
    omega
  have hsupc : ∀ i, i ∈ sup n (desc C n) c ↔
      i = k + 1 ∨ ∃ u ∈ (Finset.univ : Finset (Fin k)), i = u.val ∨ i = k + 2 + u.val := by
    intro i
    rw [supc, memsup]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases d : i < k
      · exact Or.inr ⟨⟨i, d⟩, Finset.mem_univ _, Or.inl rfl⟩
      by_cases e : i = k
      · exact absurd (e ▸ h1) hmx'
      by_cases f : i = k + 1
      · exact Or.inl f
      by_cases g : i = k + 2 + k
      · exact absurd (g ▸ h1) hmy'
      exact Or.inr ⟨⟨i - (k + 2), by omega⟩, Finset.mem_univ _,
        Or.inr (show i = k + 2 + (i - (k + 2)) by omega)⟩
    · rintro (rfl | ⟨u, _, rfl | rfl⟩)
      · exact ⟨xin _ (by omega) (by omega), by omega⟩
      · have := u.isLt
        exact ⟨xin _ (by omega) (by omega), by omega⟩
      · have := u.isLt
        exact ⟨yin _ this, by omega⟩
  have notk : k + 2 + k ∉ sup n (desc C n) c := notin _ (by omega) hmy'
  have zk : val C n c (only (k + 1)) = true := by
    have a := (G (k + 1) (by omega) k (by omega)).2 (by unfold Qc; omega)
    rwa [gdrop' _ _ notk] at a
  have core0 : ∀ i, i ≠ k + 1 → val C n c (only i) = false := by
    intro i hi
    by_cases d : i ∈ sup n (desc C n) c
    swap
    · apply off H hcT cmon
      intro j hj
      have : j ≠ i := fun e => d (e ▸ hj)
      simp [only, this]
    rcases (hsupc i).1 d with e | ⟨u, _, e | e⟩
    · exact absurd e hi
    · have hu := u.isLt
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨w, hw, hwu, _⟩ := avoid k (by omega) u.val u.val u.val u.val
      have := (G u.val (by omega) w (by omega)).1 (up1 _ _ (e ▸ h))
      apply this
      unfold Qc
      omega
    · have hu := u.isLt
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨w, hw, hwu, _⟩ := avoid k (by omega) u.val u.val u.val u.val
      have := (G w (by omega) u.val (by omega)).1 (up2 _ _ (e ▸ h))
      apply this
      unfold Qc
      omega
  obtain ⟨M, hM, _, hv⟩ := cls_z H (fun u : Fin k => u.val) (fun u : Fin k => k + 2 + u.val)
    (fun u v h => Fin.ext h) (fun u v h => Fin.ext (by omega)) (fun u v h => by have := u.isLt; omega)
    (k + 1) (fun u => by have := u.isLt; omega) (fun u => by have := u.isLt; omega)
    c hcT cmon Finset.univ hsupc (by
      intro u _ v _
      change val C n c (two u.val (k + 2 + v.val)) = _
      have hu := u.isLt
      have hv := v.isLt
      rw [Bool.eq_iff_iff, G _ (by omega) _ (by omega), decide_eq_true_eq, Fin.ext_iff]
      unfold Qc
      omega) core0 zk
  refine ⟨M, hM, fun f => ?_⟩
  rw [hFG, ← hv]
  change (!val C n c f) = true ↔ ¬ val C n c f = true
  cases val C n c f <;> simp

section build

variable (nr : ℕ) {k : ℕ}

def term (b : Fin k × Fin k) (f : ℕ → Bool) : Bool :=
  if b.1 = b.2 then f b.1.val && f (nr + b.1.val)
  else (f b.1.val || f (nr + b.2.val)) && (f b.2.val || f (nr + b.1.val))

def blk (m : ℕ) (b : Fin k × Fin k) : List Gate × ℕ :=
  if b.1 = b.2 then ([⟨GateOp.and, [b.1.val, nr + b.1.val]⟩], m)
  else ([⟨GateOp.or, [b.1.val, nr + b.2.val]⟩, ⟨GateOp.or, [b.2.val, nr + b.1.val]⟩,
    ⟨GateOp.and, [m, m + 1]⟩], m + 2)

def bcost (b : Fin k × Fin k) : ℕ := if b.1 = b.2 then 2 else 4

def build (n : ℕ) : List (Fin k × Fin k) → List Gate × ℕ
  | [] => ([], 0)
  | [b] => blk nr n b
  | b :: b' :: l =>
    let r := build n (b' :: l)
    let s := blk nr (n + r.1.length) b
    (r.1 ++ s.1 ++ [⟨GateOp.or, [r.2, s.2]⟩], n + r.1.length + s.1.length)

def Mon (gs : List Gate) : Prop := ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem run_one (g : Gate) (w : List Bool) : run [g] w = step w g := rfl

theorem blk_ok (n : ℕ) (hn : ∀ u : Fin k, u.val < n ∧ nr + u.val < n) (f : ℕ → Bool) (w : List Bool)
    (hlen : n ≤ w.length) (hf : ∀ i < n, w.getD i false = f i) (b : Fin k × Fin k) :
    (run (blk nr w.length b).1 w).getD (blk nr w.length b).2 false = term nr b f ∧
    (blk nr w.length b).2 < w.length + (blk nr w.length b).1.length ∧
    (blk nr w.length b).1.length + 1 = bcost b ∧ Mon (blk nr w.length b).1 := by
  have a1 := hn b.1
  have a2 := hn b.2
  have keep : ∀ (t : List Bool) (i : ℕ), i < n → (w ++ t).getD i false = f i := by
    intro t i hi
    rw [getD_keep _ _ (by omega)]
    exact hf i hi
  by_cases h : b.1 = b.2
  · simp only [blk, term, bcost, if_pos h]
    refine ⟨?_, by simp, by simp, ?_⟩
    · rw [run_one]
      simp only [step]
      rw [getD_new _ _ rfl]
      simp [GateOp.eval, ← List.getD_eq_getElem?_getD, hf _ a1.1, hf _ a1.2]
    · intro g hg
      rw [List.mem_singleton] at hg
      subst hg
      simp
  · simp only [blk, term, bcost, if_neg h]
    refine ⟨?_, by simp, by simp, ?_⟩
    · have s1 : step w ⟨GateOp.or, [b.1.val, nr + b.2.val]⟩ = w ++ [f b.1.val || f (nr + b.2.val)] := by
        simp only [step, List.map_cons, List.map_nil, hf _ a1.1, hf _ a2.2]
        simp [GateOp.eval]
      have s2 : ∀ x : Bool, step (w ++ [x]) ⟨GateOp.or, [b.2.val, nr + b.1.val]⟩ =
          w ++ [x] ++ [f b.2.val || f (nr + b.1.val)] := by
        intro x
        simp only [step, List.map_cons, List.map_nil, keep _ _ a2.1, keep _ _ a1.2]
        simp [GateOp.eval]
      have s3 : ∀ x y : Bool, step (w ++ [x] ++ [y]) ⟨GateOp.and, [w.length, w.length + 1]⟩ =
          w ++ [x] ++ [y] ++ [x && y] := by
        intro x y
        have e1 : (w ++ [x] ++ [y]).getD w.length false = x := by
          rw [getD_keep _ _ (by simp), getD_new _ _ rfl]
        have e2 : (w ++ [x] ++ [y]).getD (w.length + 1) false = y := getD_new _ _ (by simp)
        simp only [step, List.map_cons, List.map_nil, e1, e2]
        simp [GateOp.eval]
      rw [run_cons, s1, run_cons, s2, run_cons, s3, run_nil]
      exact getD_new _ _ (by simp)
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp

theorem build_ok (n : ℕ) (hn : ∀ u : Fin k, u.val < n ∧ nr + u.val < n) (f : ℕ → Bool) (w : List Bool)
    (hlen : w.length = n) (hf : ∀ i < n, w.getD i false = f i) :
    ∀ l : List (Fin k × Fin k), l ≠ [] →
      (run (build nr n l).1 w).getD (build nr n l).2 false = l.any (fun b => term nr b f) ∧
      (build nr n l).2 < n + (build nr n l).1.length ∧
      (build nr n l).1.length + 1 = (l.map bcost).sum ∧ Mon (build nr n l).1 := by
  intro l
  induction l with
  | nil => exact fun h => absurd rfl h
  | cons b l ih =>
    intro _
    cases l with
    | nil =>
      have := blk_ok nr n hn f w (by omega) hf b
      rw [hlen] at this
      simpa [build] using this
    | cons b' l =>
      obtain ⟨h1, h2, h3, h4⟩ := ih (by simp)
      simp only [build]
      generalize hr : build nr n (b' :: l) = r at h1 h2 h3 h4
      let w1 := run r.1 w
      have l1 : w1.length = n + r.1.length := by
        simp only [w1, run_length, hlen]
      have hf1 : ∀ i < n, w1.getD i false = f i := by
        intro i hi
        simp only [w1]
        rw [prefix_keep _ _ (by omega)]
        exact hf i hi
      obtain ⟨k1, k2, k3, k4⟩ := blk_ok nr n hn f w1 (by omega) hf1 b
      rw [l1] at k1 k2 k3 k4
      generalize hs : blk nr (n + r.1.length) b = s at k1 k2 k3 k4
      let w2 := run s.1 w1
      have l2 : w2.length = n + r.1.length + s.1.length := by
        simp only [w2, run_length, l1]
      have keep : w2.getD r.2 false = w1.getD r.2 false := by
        simp only [w2]
        exact prefix_keep _ _ (by omega)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [run_append, run_append, run_one]
        change (step w2 ⟨GateOp.or, [r.2, s.2]⟩).getD (n + r.1.length + s.1.length) false = _
        simp only [step]
        rw [getD_new _ _ l2.symm]
        simp only [List.map_cons, List.map_nil]
        rw [keep]
        change GateOp.or.eval [w1.getD r.2 false, (run s.1 w1).getD s.2 false] = _
        rw [show w1.getD r.2 false = _ from h1, k1, List.any_cons (a := b)]
        simp [GateOp.eval, Bool.or_comm]
      · simp only [List.length_append, List.length_singleton]
        omega
      · rw [List.map_cons, List.sum_cons]
        simp only [List.length_append, List.length_singleton]
        omega
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with (hg | hg) | hg
        · exact h4 g hg
        · exact k4 g hg
        · subst hg
          simp

theorem blocks (nr : ℕ) (M : Finset (Finset (Fin k))) (hM : IsM M) :
    ∃ l : List (Fin k × Fin k), (l.map bcost).sum = 2 * k ∧
      ∀ f, (l.any (fun b => term nr b f) = true ↔
        Pr (fun u => u.val) (fun u => nr + u.val) Finset.univ M f) := by
  have pairs : ∀ M : Finset (Finset (Fin k)), IsM M → ∃ l : List (Fin k × Fin k),
      (l.map bcost).sum = 2 * (M.biUnion id).card ∧
      ∀ f, (l.any (fun b => term nr b f) = true ↔
        Pr (fun u => u.val) (fun u => nr + u.val) (M.biUnion id) M f) := by
    intro M
    induction M using Finset.induction_on with
    | empty => exact fun _ => ⟨[], by simp, fun f => by simp [Pr]⟩
    | @insert e M he ih =>
      intro hM
      obtain ⟨l, h1, h2⟩ := ih (hM.mono (Finset.subset_insert _ _))
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (hM.1 e (Finset.mem_insert_self _ _))
      have hdj : Disjoint ({a, b} : Finset (Fin k)) (M.biUnion id) := by
        rw [Finset.disjoint_biUnion_right]
        intro g hg
        exact hM.2 _ (Finset.mem_insert_self _ _) g (Finset.mem_insert_of_mem hg) (fun c => he (c ▸ hg))
      refine ⟨(a, b) :: l, ?_, fun f => ?_⟩
      · rw [List.map_cons, List.sum_cons, h1, Finset.biUnion_insert, id,
          Finset.card_union_of_disjoint hdj, Finset.card_pair hab]
        simp only [bcost, if_neg hab]
        omega
      · rw [List.any_cons, Bool.or_eq_true, h2, Finset.biUnion_insert, id]
        have e1 : insert ({a, b} : Finset (Fin k)) M = {{a, b}} ∪ M := Finset.insert_eq _ _
        rw [e1, Pr_union]
        apply or_congr _ Iff.rfl
        simp only [term, if_neg hab, Pr, Finset.mem_insert, Finset.mem_singleton, or_and_right,
          exists_or, exists_eq_left, forall_eq_or_imp, forall_eq, Bool.and_eq_true, Bool.or_eq_true]
        tauto
  obtain ⟨l, h1, h2⟩ := pairs M hM
  let R := Finset.univ \ M.biUnion id
  refine ⟨l ++ R.toList.map (fun u => (u, u)), ?_, fun f => ?_⟩
  · have : (R.toList.map (fun u => (u, u))).map bcost = List.replicate R.card 2 := by
      rw [List.map_map, ← Finset.length_toList, ← List.map_const']
      apply List.map_congr_left
      intro u _
      simp [bcost]
    rw [List.map_append, List.sum_append, h1, this, List.sum_replicate, smul_eq_mul]
    have h3 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (M.biUnion id))
    rw [Finset.card_univ, Fintype.card_fin] at h3
    simp only [R]
    omega
  · rw [List.any_append, Bool.or_eq_true, h2]
    have hu : M.biUnion id ∪ R = Finset.univ := by
      simp [R]
    have e : Pr (fun u => u.val) (fun u => nr + u.val) Finset.univ M f ↔
        Pr (fun u => u.val) (fun u => nr + u.val) (M.biUnion id) M f ∨
        Pr (fun u => u.val) (fun u => nr + u.val) R ∅ f := by
      rw [← Pr_union, hu, Finset.union_empty]
    rw [e]
    apply or_congr Iff.rfl
    simp [Pr, term, List.any_map, List.any_eq_true]

end build

theorem list_inp (l : List Bool) (n : ℕ) (h : l.length = n) : l = inp n (fun i => l.getD i false) := by
  apply List.ext_getElem
  · simp [inp, h]
  · intro i h1 h2
    simp [inp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem getD_app_left {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) (i : ℕ) (hi : i < a) :
    (List.ofFn x ++ List.ofFn y).getD i false = x ⟨i, hi⟩ := by
  rw [getD_keep _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_app_right {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) (i : ℕ) (hi : i < b) :
    (List.ofFn x ++ List.ofFn y).getD (a + i) false = y ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [hi]

theorem oneEach_inp {a b : ℕ} (u : Fin a) (v : Fin b) :
    PEqualNP.Represents.oneEach u v = inp (a + b) (two u.val (a + v.val)) := by
  apply List.ext_getElem
  · simp [PEqualNP.Represents.oneEach, inp]
  · intro i h1 h2
    have hi : i < a + b := by simpa [inp] using h2
    have key : (PEqualNP.Represents.oneEach u v).getD i false = two u.val (a + v.val) i := by
      unfold PEqualNP.Represents.oneEach two
      have hu := u.isLt
      have hv := v.isLt
      by_cases d : i < a
      · rw [getD_app_left _ _ i d]
        rw [decide_eq_decide, Fin.ext_iff]
        simp only
        omega
      · have e : i = a + (i - a) := by omega
        conv_lhs => rw [e]
        rw [getD_app_right _ _ (i - a) (by omega)]
        rw [decide_eq_decide, Fin.ext_iff]
        simp only
        omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at key
    rw [key]
    simp [inp]

open PEqualNP.MetaComplexity PEqualNP.Represents

theorem pr_point (k d u v : ℕ) (hkd : k ≤ d) (hu : u < d) (M : Finset (Finset (Fin k))) (hM : IsM M) :
    Pr (fun w => w.val) (fun w => d + w.val) Finset.univ M (two u (d + v)) ↔ u = v ∧ u < k := by
  constructor
  · rintro (⟨w, _, h1, h2⟩ | ⟨e, he, h⟩)
    · simp only [two, decide_eq_true_eq] at h1 h2
      have := w.isLt
      omega
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (hM.1 e he)
      have hne : a.val ≠ b.val := fun c => hab (Fin.ext c)
      have ha := a.isLt
      have hb := b.isLt
      simp only [two, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
        forall_eq] at h
      omega
  · rintro ⟨h, hk⟩
    left
    refine ⟨⟨u, hk⟩, Finset.mem_univ _, by simp [two], by simp [two, h]⟩

theorem pr_pred (k nr nc : ℕ) (h1 : k ≤ nr) (h2 : k ≤ nc) (x : Fin nr → Bool) (y : Fin nc → Bool)
    (M : Finset (Finset (Fin k))) (hM : IsM M) :
    Pr (fun w => w.val) (fun w => nr + w.val) Finset.univ M (fun i => (List.ofFn x ++ List.ofFn y).getD i false) ↔
      (Finset.univ.filter (fun i : Fin k => (List.ofFn x).getD i.val false = true) ∩
        Finset.univ.filter (fun i : Fin k => (List.ofFn y).getD i.val false = true)).Nonempty ∨
      (M ∩ Finset.univ.filter (fun e : Finset (Fin k) => e.card = 2 ∧
        (e ⊆ Finset.univ.filter (fun i : Fin k => (List.ofFn x).getD i.val false = true) ∨
         e ⊆ Finset.univ.filter (fun i : Fin k => (List.ofFn y).getD i.val false = true)))).Nonempty := by
  have ex : ∀ w : Fin k, (List.ofFn x ++ List.ofFn y).getD w.val false = (List.ofFn x).getD w.val false := by
    intro w
    have := w.isLt
    exact getD_keep _ _ (by rw [List.length_ofFn]; omega)
  have ey : ∀ w : Fin k, (List.ofFn x ++ List.ofFn y).getD (nr + w.val) false =
      (List.ofFn y).getD w.val false := by
    intro w
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.getD_eq_getElem?_getD]
    simp
  unfold Pr
  apply or_congr
  · constructor
    · rintro ⟨w, _, a, b⟩
      exact ⟨w, Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, (ex w).symm.trans a⟩,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, (ey w).symm.trans b⟩⟩⟩
    · rintro ⟨w, hw⟩
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hw
      exact ⟨w, Finset.mem_univ _, (ex w).trans hw.1.2, (ey w).trans hw.2.2⟩
  · constructor
    · rintro ⟨e, he, h⟩
      refine ⟨e, Finset.mem_inter.2 ⟨he, Finset.mem_filter.2 ⟨Finset.mem_univ _, hM.1 e he, ?_⟩⟩⟩
      rcases h with h | h
      · left
        intro w hw
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (ex w).symm.trans (h w hw)⟩
      · right
        intro w hw
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (ey w).symm.trans (h w hw)⟩
    · rintro ⟨e, he⟩
      rw [Finset.mem_inter, Finset.mem_filter] at he
      refine ⟨e, he.1, ?_⟩
      rcases he.2.2.2 with h | h
      · left
        intro w hw
        exact (ex w).trans (Finset.mem_filter.1 (h hw)).2
      · right
        intro w hw
        exact (ey w).trans (Finset.mem_filter.1 (h hw)).2

theorem goodC_of_fan (C : Circuit) (h : FanInTwo C) : GoodC C := by
  intro g hg
  have := h g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  exact this

theorem eval_val (C : Circuit) (n : ℕ) (l : List Bool) (h : l.length = n) :
    C.eval l = val C n C.output (fun i => l.getD i false) := by
  change C.eval l = C.eval (inp n (fun i => l.getD i false))
  rw [← list_inp l n h]

theorem classify_false (k : ℕ) (hk : 2 ≤ k) (C : Circuit) (hm : Monotone2 C) (hs : C.size + 1 ≤ 2 * k)
    (hR : ∀ u v : Fin k, C.eval (oneEach u v) = decide (u.val = v.val)) :
    ∃ M : Finset (Finset (Fin k)), IsM M ∧ ∀ x y : Fin k → Bool,
      C.eval (List.ofFn x ++ List.ofFn y) = true ↔
        Pr (fun w => w.val) (fun w => k + w.val) Finset.univ M (fun i => (List.ofFn x ++ List.ofFn y).getD i false) := by
  have hg : GoodC C := by
    intro g hg
    have := hm g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    exact ⟨this.1.imp id Or.inl, this.2⟩
  have hmon : ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
    intro g hg c
    have := (hm g hg).1
    rw [c] at this
    simp at this
  obtain ⟨M, hM, h⟩ := class_id k hk C hg hmon hs (by
    intro u v
    have := hR u v
    rw [oneEach_inp] at this
    rw [show decide (u = v) = decide (u.val = v.val) from decide_eq_decide.2 Fin.ext_iff]
    exact this)
  refine ⟨M, hM, fun x y => ?_⟩
  rw [eval_val C (k + k) _ (by simp)]
  exact h _

theorem classify_true (k : ℕ) (hk : 7 ≤ k) (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 2 * k + 1)
    (hR : ∀ (u : Fin (k + 2)) (v : Fin (k + 1)), C.eval (oneEach u v) =
      decide (u.val ≠ k + 1 ∧ ¬ (u.val < k ∧ u.val = v.val))) :
    ∃ M : Finset (Finset (Fin k)), IsM M ∧ ∀ (x : Fin (k + 2) → Bool) (y : Fin (k + 1) → Bool),
      C.eval (List.ofFn x ++ List.ofFn y) = true ↔
        ¬ ((List.ofFn x ++ List.ofFn y).getD (k + 1) false = true ∨
          Pr (fun w => w.val) (fun w => k + 2 + w.val) Finset.univ M (fun i => (List.ofFn x ++ List.ofFn y).getD i false)) := by
  obtain ⟨M, hM, h⟩ := class_crown k hk C (goodC_of_fan C hf) hs (by
    intro u hu v hv
    have := hR ⟨u, hu⟩ ⟨v, hv⟩
    rw [oneEach_inp] at this
    change val C (k + 2 + (k + 1)) C.output (two u (k + 2 + v)) = _ at this
    rw [this, decide_eq_true_eq]
    rfl)
  refine ⟨M, hM, fun x y => ?_⟩
  rw [eval_val C (k + 2 + (k + 1)) _ (by rw [List.length_append, List.length_ofFn, List.length_ofFn])]
  exact h _

theorem construct (k nr n : ℕ) (hk : 2 ≤ k) (hn : ∀ u : Fin k, u.val < n ∧ nr + u.val < n)
    (M : Finset (Finset (Fin k))) (hM : IsM M) :
    ∃ (gs : List Gate) (o : ℕ), Mon gs ∧ gs.length + 1 = 2 * k ∧ o < n + gs.length ∧
      ∀ f, (run gs (inp n f)).getD o false = true ↔ Pr (fun w => w.val) (fun w => nr + w.val) Finset.univ M f := by
  obtain ⟨l, h1, h2⟩ := blocks nr M hM
  have hl : l ≠ [] := by
    intro c
    rw [c] at h1
    simp at h1
    omega
  have key : ∀ f, _ := fun f => build_ok nr n hn f (inp n f) (inp_len n f)
    (fun i hi => by simp [inp, List.getD_eq_getElem?_getD, hi]) l hl
  refine ⟨(build nr n l).1, (build nr n l).2, (key (fun _ => false)).2.2.2,
    (key (fun _ => false)).2.2.1.trans h1, (key (fun _ => false)).2.1, fun f => ?_⟩
  rw [(key f).1]
  exact h2 f

theorem circuit_false (k : ℕ) (hk : 2 ≤ k) (M : Finset (Finset (Fin k))) (hM : IsM M) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 ≤ 2 * k ∧
      (∀ u v : Fin k, C.eval (oneEach u v) = decide (u.val = v.val)) ∧
      ∀ x y : Fin k → Bool, C.eval (List.ofFn x ++ List.ofFn y) = true ↔
        Pr (fun w => w.val) (fun w => k + w.val) Finset.univ M (fun i => (List.ofFn x ++ List.ofFn y).getD i false) := by
  obtain ⟨gs, o, h1, h2, _, h4⟩ := construct k k (k + k) hk (fun u => by have := u.isLt; omega) M hM
  have ev : ∀ f, (⟨gs, o⟩ : Circuit).eval (inp (k + k) f) = true ↔
      Pr (fun w => w.val) (fun w => k + w.val) Finset.univ M f := h4
  refine ⟨⟨gs, o⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have := h1 g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact this
  · change gs.length + 1 ≤ 2 * k
    omega
  · intro u v
    have hu := u.isLt
    rw [oneEach_inp, Bool.eq_iff_iff, ev, pr_point k k u.val v.val le_rfl hu M hM, decide_eq_true_eq]
    omega
  · intro x y
    have e := list_inp (List.ofFn x ++ List.ofFn y) (k + k) (by simp)
    conv_lhs => rw [e]
    exact ev _

theorem circuit_true (k : ℕ) (hk : 2 ≤ k) (M : Finset (Finset (Fin k))) (hM : IsM M) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 2 * k + 1 ∧
      (∀ (u : Fin (k + 2)) (v : Fin (k + 1)), C.eval (oneEach u v) =
        decide (u.val ≠ k + 1 ∧ ¬ (u.val < k ∧ u.val = v.val))) ∧
      ∀ (x : Fin (k + 2) → Bool) (y : Fin (k + 1) → Bool), C.eval (List.ofFn x ++ List.ofFn y) = true ↔
        ¬ ((List.ofFn x ++ List.ofFn y).getD (k + 1) false = true ∨
          Pr (fun w => w.val) (fun w => k + 2 + w.val) Finset.univ M (fun i => (List.ofFn x ++ List.ofFn y).getD i false)) := by
  obtain ⟨gs, o, h1, h2, h3, h4⟩ := construct k (k + 2) (k + 2 + (k + 1)) hk
    (fun u => by have := u.isLt; omega) M hM
  let n := k + 2 + (k + 1)
  let m := n + gs.length
  let C : Circuit := ⟨gs ++ [⟨GateOp.or, [o, k + 1]⟩, ⟨GateOp.not, [m]⟩], m + 1⟩
  have ev : ∀ f, C.eval (inp n f) = true ↔
      ¬ (f (k + 1) = true ∨ Pr (fun w => w.val) (fun w => k + 2 + w.val) Finset.univ M f) := by
    intro f
    let w := run gs (inp n f)
    have lw : w.length = m := by simp only [w, run_length, inp_len, m]
    have a1 : w.getD (k + 1) false = f (k + 1) := by
      simp only [w]
      rw [prefix_keep _ _ (by rw [inp_len]; omega)]
      have : k + 1 < n := by omega
      simp [inp, List.getD_eq_getElem?_getD, this]
    have s1 : step w ⟨GateOp.or, [o, k + 1]⟩ = w ++ [w.getD o false || f (k + 1)] := by
      simp only [step, List.map_cons, List.map_nil, a1]
      simp [GateOp.eval]
    have s2 : ∀ b : Bool, step (w ++ [b]) ⟨GateOp.not, [m]⟩ = w ++ [b] ++ [!b] := by
      intro b
      simp only [step, List.map_cons, List.map_nil]
      rw [getD_new _ _ lw.symm]
      simp [GateOp.eval]
    have e : C.eval (inp n f) = !(w.getD o false || f (k + 1)) := by
      change (run (gs ++ [⟨GateOp.or, [o, k + 1]⟩, ⟨GateOp.not, [m]⟩]) (inp n f)).getD (m + 1) false = _
      rw [run_append]
      change (run [⟨GateOp.or, [o, k + 1]⟩, ⟨GateOp.not, [m]⟩] w).getD (m + 1) false = _
      rw [run_cons, s1, run_cons, s2, run_nil]
      exact getD_new _ _ (by simp [lw])
    rw [e, ← h4 f]
    change (!(w.getD o false || f (k + 1))) = true ↔ ¬ (f (k + 1) = true ∨ w.getD o false = true)
    cases w.getD o false <;> cases f (k + 1) <;> simp
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    simp only [C, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · have := h1 g hg
      exact ⟨this.1.imp id Or.inl, this.2⟩
    · simp
    · simp
  · change (gs ++ [_, _]).length ≤ 2 * k + 1
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    rw [oneEach_inp, Bool.eq_iff_iff, ev, pr_point k (k + 2) u.val v.val (by omega) hu M hM,
      decide_eq_true_eq]
    simp only [two, decide_eq_true_eq]
    omega
  · intro x y
    have e := list_inp (List.ofFn x ++ List.ofFn y) n
      (by rw [List.length_append, List.length_ofFn, List.length_ofFn])
    conv_lhs => rw [e]
    exact ev _

def route (bits : Nat → Bool) (depth : Nat) : Nat :=
  (List.range depth).foldl (fun node _ => 2 * node + 1 + (if bits node then 1 else 0)) 0

theorem route_step (bits : Nat → Bool) (depth : Nat) :
    route bits (depth + 1) = 2 * route bits depth + 1 + (if bits (route bits depth) then 1 else 0) := by
  unfold route
  rw [List.range_succ, List.foldl_append]
  rfl

theorem route_bounds (bits : Nat → Bool) (depth : Nat) :
    2 ^ depth ≤ route bits depth + 1 ∧ route bits depth + 2 ≤ 2 ^ (depth + 1) := by
  induction depth with
  | zero => simp [route]
  | succ depth ih =>
    rw [route_step, pow_succ 2 (depth + 1), pow_succ 2 depth]
    split <;> omega

theorem route_congr (bits other : Nat → Bool) (depth : Nat)
    (agree : ∀ node, node + 2 ≤ 2 ^ depth → bits node = other node) :
    route bits depth = route other depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    have shorter := ih (fun node bound => agree node (by rw [pow_succ]; omega))
    rw [route_step, route_step, agree _ (route_bounds bits depth).2, shorter]

theorem route_inj_height (bits : Nat → Bool) : StrictMono (route bits) := by
  apply strictMono_nat_of_lt_succ
  intro depth
  rw [route_step]
  split <;> omega

theorem route_steps_eq (bits other : Nat → Bool) (depth : Nat) :
    route bits depth = route other depth ↔
      ∀ level < depth, bits (route other level) = other (route other level) := by
  induction depth with
  | zero => simp [route]
  | succ depth ih =>
    rw [route_step, route_step]
    have next_eq : ∀ (a b : Nat) (x y : Bool),
        2 * a + 1 + (if x then 1 else 0) = 2 * b + 1 + (if y then 1 else 0) ↔ a = b ∧ x = y := by
      intro a b x y
      cases x <;> cases y <;> simp <;> omega
    rw [next_eq]
    constructor
    · rintro ⟨same, step⟩ level bound
      by_cases last : level = depth
      · simpa [last, same] using step
      · exact ih.mp same level (by omega)
    · intro agree
      have same := ih.mpr (fun level hl => agree level (by omega))
      exact ⟨same, same ▸ agree depth (by omega)⟩

theorem route_last_only (depth : Nat) (baseline current : Nat → Bool)
    (outside : ∀ node, 2 ^ depth ≤ node + 1 → node ≠ route baseline depth → current node = false) :
    current (route current depth) = true ↔ current (route baseline depth) = true ∧
      ∀ level < depth, current (route baseline level) = baseline (route baseline level) := by
  by_cases same : route current depth = route baseline depth
  · rw [same]
    exact (and_iff_left ((route_steps_eq _ _ _).mp same)).symm
  · rw [outside _ (route_bounds _ _).1 same]
    have diff := mt (route_steps_eq current baseline depth).mpr same
    simp [diff]

def queryTrace {α : Type} [DecidableEq α] (ask : Nat → α) (edges : Finset α) (depth : Nat) : Finset α :=
  (Finset.range depth).image (fun level => ask (route (fun node => decide (ask node ∈ edges)) level))

theorem sameTrace {α : Type} [DecidableEq α] (ask : Nat → α) (edges other : Finset α) (depth : Nat)
    (agree : ∀ edge ∈ queryTrace ask edges depth, (edge ∈ edges ↔ edge ∈ other)) :
    route (fun node => decide (ask node ∈ other)) depth = route (fun node => decide (ask node ∈ edges)) depth := by
  apply (route_steps_eq _ _ _).mpr
  intro level hl
  apply decide_eq_decide.mpr
  apply Iff.symm
  exact agree _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hl))

def toggleEdge {β : Type} [DecidableEq β] (base : Finset β) (edge : β) : Finset β :=
  if edge ∈ base then base.erase edge else insert edge base

theorem mem_toggleEdge {β : Type} [DecidableEq β] (base : Finset β) (edge vertex : β) :
    vertex ∈ toggleEdge base edge ↔ if vertex = edge then vertex ∉ base else vertex ∈ base := by
  by_cases hit : vertex = edge <;> by_cases existsEdge : edge ∈ base <;> simp [toggleEdge, *]

theorem toggle_delta {β : Type} [DecidableEq β] (base : Finset β) (edge : β) (weight : β → Int) :
    (toggleEdge base edge).sum weight = base.sum weight + (if edge ∈ base then -(weight edge) else weight edge) := by
  by_cases hit : edge ∈ base
  · have val := Finset.sum_erase_add base weight hit
    simp only [toggleEdge, if_pos hit]
    exact eq_sub_of_add_eq (by simpa using val)
  · simp [toggleEdge, hit, Finset.sum_insert, add_comm]

theorem toggle_square {β : Type} [DecidableEq β] (base : Finset β) (a b : β) (diff : a ≠ b) (weight : β → Int) :
    base.sum weight + (toggleEdge (toggleEdge base a) b).sum weight =
      (toggleEdge base a).sum weight + (toggleEdge base b).sum weight := by
  simp only [toggle_delta, mem_toggleEdge, Ne.symm diff, ↓reduceIte]
  ring

theorem fixed_imp_chain {E : Type} [DecidableEq E] (full mask I : Finset E) (incl : mask ⊆ full)
    (aff : ∃ (base : Int) (weights : E → Int), ∀ s ⊆ full, s ∩ I = mask ∩ I →
      (if s = mask then (1 : Int) else 0) = base + (s \ I).sum weights) :
    ∀ a ∈ full, ∀ b ∈ full, a ∉ I → b ∉ I → a = b := by
  intro a ha b hb freeA freeB
  by_contra diff
  obtain ⟨base, w, model⟩ := aff
  have sub (s : Finset E) (hs : s ⊆ full) (e : E) (he : e ∈ full) : toggleEdge s e ⊆ full := by
    unfold toggleEdge
    split
    · exact (Finset.erase_subset _ _).trans hs
    · exact Finset.insert_subset he hs
  have fiber (s : Finset E) (e : E) (free : e ∉ I) : toggleEdge s e ∩ I = s ∩ I := by
    ext x
    by_cases eq : x = e <;> simp [mem_toggleEdge, eq, free]
  have del (s : Finset E) (e : E) (free : e ∉ I) : (toggleEdge s e) \ I = toggleEdge (s \ I) e := by
    ext x
    by_cases eq : x = e <;> simp [mem_toggleEdge, eq, free]
  have changed (s : Finset E) (e : E) : toggleEdge s e ≠ s := by
    intro eq
    have flip := mem_toggleEdge s e e
    rw [eq, if_pos rfl] at flip
    tauto
  have double : toggleEdge (toggleEdge mask a) b ≠ mask := by
    intro eq
    have flip := mem_toggleEdge (toggleEdge mask a) b a
    rw [eq, if_neg diff, mem_toggleEdge, if_pos rfl] at flip
    tauto
  have e0 := model mask incl rfl
  have e1 := model _ (sub mask incl a ha) (fiber mask a freeA)
  have e2 := model _ (sub mask incl b hb) (fiber mask b freeB)
  have e3 := model _ (sub _ (sub mask incl a ha) b hb) ((fiber _ b freeB).trans (fiber _ a freeA))
  simp only [if_pos rfl, if_neg (changed _ _), if_neg double, del _ _ freeA, del _ _ freeB] at e0 e1 e2 e3
  have sq := toggle_square (mask \ I) a b diff w
  change (1 : Int) = base + (mask \ I).sum w at e0
  linarith only [e0, e1, e2, e3, sq]

theorem trace_unchanged {β : Type} [DecidableEq β] (baseline : Finset β) (a b : β) (ask : Nat → β) (d : Nat)
    (ha : a ∉ queryTrace ask baseline d) (hb : b ∉ queryTrace ask baseline d) :
    let path := fun s : Finset β => route (fun j => decide (ask j ∈ s)) d
    path (toggleEdge baseline a) = path baseline ∧ path (toggleEdge baseline b) = path baseline ∧
      path (toggleEdge (toggleEdge baseline a) b) = path baseline := by
  intro path
  have neA (e) (hm : e ∈ queryTrace ask baseline d) : e ≠ a := fun h => ha (h ▸ hm)
  have neB (e) (hm : e ∈ queryTrace ask baseline d) : e ≠ b := fun h => hb (h ▸ hm)
  refine ⟨sameTrace _ _ _ _ ?_, sameTrace _ _ _ _ ?_, sameTrace _ _ _ _ ?_⟩ <;>
    intro e hm <;> simp [mem_toggleEdge, neA e hm, neB e hm]

def edgeAt (count : Nat) (node : Nat) : Fin (2 * count + 6) × Fin (2 * count + 6) :=
  if bound : node < count then (⟨2 * node, by omega⟩, ⟨2 * node + 1, by omega⟩) else (0, 0)

def ends {k : Nat} (edge : Fin k × Fin k) : Finset (Fin k) := {edge.1, edge.2}

theorem block_matching {k : Nat} (edges : Finset (Fin k × Fin k))
    (form : ∀ edge ∈ edges, ∃ node : Nat, edge.1.val = 2 * node ∧ edge.2.val = 2 * node + 1) :
    IsM (edges.image ends) := by
  constructor
  · intro key hk
    obtain ⟨edge, hm, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨node, first, second⟩ := form edge hm
    have ne : edge.1 ≠ edge.2 := by
      intro eq
      have := congrArg Fin.val eq
      omega
    simp [ends, ne]
  · intro key hk other ho distinct
    obtain ⟨edge, hm, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨edge', hm', rfl⟩ := Finset.mem_image.mp ho
    obtain ⟨node, first, second⟩ := form edge hm
    obtain ⟨node', first', second'⟩ := form edge' hm'
    have diff : node ≠ node' := by
      rintro rfl
      apply distinct
      congr 1
      exact Prod.ext (Fin.ext (first.trans first'.symm)) (Fin.ext (second.trans second'.symm))
    rw [Finset.disjoint_left]
    intro vertex hv hw
    simp only [ends, Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with eq | eq <;> have := congrArg Fin.val eq <;> omega

theorem ends_injective {k : Nat} (edge other : Fin k × Fin k)
    (ord : edge.1 < edge.2) (ord' : other.1 < other.2) (eq : ends edge = ends other) : edge = other := by
  have left : edge.1 ∈ ends other := eq ▸ Finset.mem_insert_self _ _
  have right : edge.2 ∈ ends other := eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [ends, Finset.mem_insert, Finset.mem_singleton] at left right
  rcases left with left | left <;> rcases right with right | right
  · exact (ord.ne (left.trans right.symm)).elim
  · exact Prod.ext left right
  · rw [left, right] at ord
    exact (lt_asymm ord ord').elim
  · exact (ord.ne (left.trans right.symm)).elim

theorem probe_Pr {k nr nc : Nat} (h1 : k ≤ nr) (h2 : k ≤ nc)
    (edge : Fin k × Fin k) (ord : edge.1 < edge.2) (matching : Finset (Finset (Fin k))) (hm : IsM matching) :
    let x := fun i : Fin nr => decide (i.val = edge.1.val ∨ i.val = edge.2.val)
    let y := fun _ : Fin nc => false
    Pr (fun w => w.val) (fun w => nr + w.val) Finset.univ matching
      (fun i => (List.ofFn x ++ List.ofFn y).getD i false) ↔ ends edge ∈ matching := by
  intro x y
  have hv (w : Fin k) : w.val < nr := w.isLt.trans_le h1
  have hw (w : Fin k) : w.val < nc := w.isLt.trans_le h2
  simp only [Pr, getD_app_left x y _ (hv _), getD_app_right x y _ (hw _), x, y,
    Bool.false_eq_true, and_false, exists_const, Finset.mem_univ, true_and, false_or, decide_eq_true_eq,
    Fin.val_eq_val, exists_false]
  constructor
  · rintro ⟨key, hk, left | empty⟩
    · have sub : key ⊆ ends edge := by
        intro v hv
        simpa only [ends, Finset.mem_insert, Finset.mem_singleton] using left v hv
      have eq : key = ends edge := Finset.eq_of_subset_of_card_le sub (by simp [ends, ord.ne, hm.1 key hk])
      exact eq ▸ hk
    · obtain ⟨v, hv'⟩ := Finset.card_pos.mp (show 0 < key.card by rw [hm.1 key hk]; decide)
      exact False.elim (empty v hv')
  · intro member
    exact ⟨_, member, Or.inl (by simp [ends])⟩

theorem edgeAt_val (count node : Nat) (bound : node < count) :
    (edgeAt count node).1.val = 2 * node ∧ (edgeAt count node).2.val = 2 * node + 1 := by
  simp [edgeAt, bound]

theorem edgeAt_inj {count left right : Nat} (hl : left < count) (hr : right < count) :
    edgeAt count left = edgeAt count right ↔ left = right := by
  constructor
  · intro eq
    have h := congrArg (fun e : Fin (2 * count + 6) × Fin (2 * count + 6) => e.1.val) eq
    simpa [edgeAt, hl, hr] using h
  · rintro rfl; rfl

def lastNode (h : Nat) := 2 ^ h - 1

theorem left_chain (h : Nat) : route (fun _ => false) h = lastNode h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [route_step, ih]
    simp only [lastNode, pow_succ, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    have := Nat.two_pow_pos h
    omega

theorem left_only {h : Nat} (bits : Nat → Bool) (out : ∀ n, lastNode h < n → bits n = false) :
    bits (route bits h) = true ↔ bits (lastNode h) = true ∧ ∀ i < h, bits (lastNode i) = false := by
  simpa only [left_chain] using route_last_only h (fun _ => false) bits (by
    intro n hn diff
    apply out
    rw [left_chain] at diff
    dsimp [lastNode] at *
    omega)

theorem chain_small (h level : Nat) (bound : level ≤ h) : lastNode level < 2 ^ (h + 1) - 1 := by
  have hle : 2 ^ level ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) bound
  have := Nat.two_pow_pos h
  rw [pow_succ]
  dsimp [lastNode]
  omega

def chainEdges (h count : Nat) :=
  (Finset.range (h + 1)).image (fun j => edgeAt count (lastNode j))

theorem chainEdges_card (h : Nat) : (chainEdges h (2 ^ (h + 1) - 1)).card = h + 1 := by
  unfold chainEdges
  rw [Finset.card_image_iff.mpr, Finset.card_range]
  intro i hi j hj eq
  have hi' : i ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hj' : j ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have same := (edgeAt_inj (chain_small h i hi') (chain_small h j hj')).mp eq
  rw [← left_chain, ← left_chain] at same
  exact (route_inj_height (fun _ => false)).injective same

theorem reach_level (h node : Nat) (lo : 2 ^ h ≤ node + 1) (hi : node + 2 ≤ 2 ^ (h + 1)) :
    ∃ bits : Nat → Bool, route bits h = node := by
  induction h generalizing node with
  | zero => have : node = 0 := by norm_num at hi; omega
            exact ⟨fun _ => false, this.symm⟩
  | succ h ih =>
    let parent := (node - 1) / 2
    rw [pow_succ] at lo
    rw [pow_succ] at hi
    have pos := Nat.two_pow_pos h
    obtain ⟨bits, hit⟩ := ih parent (by dsimp [parent]; omega) (by dsimp [parent]; omega)
    let edited := Function.update bits parent (decide (node = 2 * parent + 2))
    have preserved : route edited h = route bits h := by
      apply (route_steps_eq _ _ _).2
      intro level earlier
      have ne : route bits level ≠ parent := hit ▸ (route_inj_height bits earlier).ne
      simp [edited, ne]
    refine ⟨edited, ?_⟩
    rw [route_step, preserved, hit]
    simp only [edited, Function.update_self, decide_eq_true_eq]
    dsimp [parent]
    split <;> omega

theorem hit_before (h node : Nat) (hi : node < 2 ^ (h + 1) - 1) :
    ∃ level ≤ h, ∃ bits : Nat → Bool, route bits level = node := by
  induction h with
  | zero =>
    have : node = 0 := by norm_num at hi; omega
    exact ⟨0, le_rfl, fun _ => false, this.symm⟩
  | succ h ih =>
    by_cases before : node < 2 ^ (h + 1) - 1
    · obtain ⟨level, le, bits, hit⟩ := ih before
      exact ⟨level, by omega, bits, hit⟩
    · obtain ⟨bits, hit⟩ := reach_level (h + 1) node (by omega) (by omega)
      exact ⟨h + 1, le_rfl, bits, hit⟩

theorem route_prefix_eq (bits other : Nat → Bool) (h : Nat) (same : route bits h = route other h)
    (level : Nat) (bound : level ≤ h) : route bits level = route other level := by
  exact (route_steps_eq _ _ _).mpr (fun x hx => (route_steps_eq bits other h).mp same x (by omega))

theorem leaf_antichain (h : Nat) (unasked : Finset Nat) (bound : ∀ v ∈ unasked, v < 2 ^ (h + 1) - 1)
    (anti : ∀ (bits : Nat → Bool) i j, i ≤ h → j ≤ h → route bits i ∈ unasked → route bits j ∈ unasked → i = j) :
    unasked.card ≤ 2 ^ h := by
  classical
  have exists_path (v : Nat) : ∃ level : Nat, ∃ bits : Nat → Bool, v ∈ unasked → level ≤ h ∧ route bits level = v := by
    by_cases mem : v ∈ unasked
    · obtain ⟨level, le, bits, hit⟩ := hit_before h v (bound v mem)
      exact ⟨level, bits, fun _ => ⟨le, hit⟩⟩
    · exact ⟨0, fun _ => false, fun hv => (mem hv).elim⟩
  choose level path spec using exists_path
  let endpt := fun v => route (path v) h
  have extent : unasked.image endpt ⊆ Finset.Ico (2 ^ h - 1) (2 ^ (h + 1) - 1) := by
    intro leaf hm
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hm
    have ext := route_bounds (path v) h
    exact Finset.mem_Ico.mpr ⟨by dsimp [endpt]; omega, by dsimp [endpt]; omega⟩
  have inj : Set.InjOn endpt unasked := by
    intro a ha b hb eq
    have ea := spec a ha
    have eb := spec b hb
    have align := route_prefix_eq (path a) (path b) h eq (level a) ea.1
    have na : route (path b) (level a) = a := align.symm.trans ea.2
    have same := anti (path b) (level a) (level b) ea.1 eb.1 (by rw [na]; exact ha) (by rw [eb.2]; exact hb)
    exact na.symm.trans (same ▸ eb.2)
  have size := Finset.card_le_card extent
  rw [Finset.card_image_iff.mpr inj, Nat.card_Ico, pow_succ] at size
  have := Nat.two_pow_pos h
  omega

theorem path_subcube {E : Type} [DecidableEq E] (h : Nat) (bits : Nat → Bool) (key : Nat → E)
    (inject : ∀ i j, i < 2 ^ (h + 1) - 1 → j < 2 ^ (h + 1) - 1 → key i = key j → i = j) :
    let path := fun level => key (route bits level)
    let full := (Finset.range (h + 1)).image path
    let mask := ((Finset.range (h + 1)).filter (fun lev => lev = h ∨ bits (route bits lev) = true)).image path
    ∀ S ⊆ full, ∀ other : Nat → Bool, (∀ j < 2 ^ (h + 1) - 1, other j = decide (key j ∈ S)) →
      (other (route other h) = true ↔ S = mask) := by
  intro path full mask S subset other agrees
  have bounded (bt : Nat → Bool) (i : Nat) (hi : i ≤ h) : route bt i < 2 ^ (h + 1) - 1 := by
    have ext := (route_bounds bt i).2
    have mono : 2 ^ (i + 1) ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have pinj (i j) (hi : i ≤ h) (hj : j ≤ h) (eq : path i = path j) : i = j :=
    (route_inj_height bits).injective (inject _ _ (bounded bits i hi) (bounded bits j hj) eq)
  have mem_mask (level) (le : level ≤ h) : path level ∈ mask ↔ level = h ∨ bits (route bits level) = true := by
    constructor
    · intro hl
      obtain ⟨i, hi, eq⟩ := Finset.mem_image.mp hl
      obtain ⟨hr, yes⟩ := Finset.mem_filter.mp hi
      exact pinj _ _ (Nat.le_of_lt_succ (Finset.mem_range.mp hr)) le eq ▸ yes
    · intro yes
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), yes⟩)
  have bit (i) (hi : i ≤ h) : other (route bits i) = true ↔ path i ∈ S := by
    rw [agrees _ (bounded _ _ hi), decide_eq_true_eq]
  have leaf_only : other (route other h) = true → route other h = route bits h := by
    intro yes
    rw [agrees _ (bounded _ _ le_rfl), decide_eq_true_eq] at yes
    obtain ⟨level, hl, equal⟩ := Finset.mem_image.mp (subset yes)
    have le := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    have hit := inject _ _ (bounded bits level le) (bounded other h le_rfl) equal
    by_cases last : level = h
    · simpa [last] using hit.symm
    · have early := (route_bounds bits level).2
      have late := (route_bounds other h).1
      have mono : 2 ^ (level + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  constructor
  · intro yes
    have leaf := leaf_only yes
    have same := (route_steps_eq other bits h).mp leaf
    have visited (i : Nat) (le : i ≤ h) : path i ∈ S ↔ path i ∈ mask := by
      rw [← bit _ le, mem_mask _ le]
      by_cases eq : i = h
      · subst i; simp [← leaf, yes]
      · simp [eq, same i (by omega)]
    ext e
    constructor
    · intro he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (subset he)
      exact (visited i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).mp he
    · intro he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      have le := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
      exact (visited i le).mpr (Finset.mem_image_of_mem _ hi)
  · rintro rfl
    have same : route other h = route bits h := by
      apply (route_steps_eq _ _ _).mpr
      intro i hi
      apply Bool.eq_iff_iff.mpr
      rw [bit _ hi.le, mem_mask _ hi.le, or_iff_right hi.ne]
    rw [same, bit _ le_rfl, mem_mask _ le_rfl]
    exact Or.inl rfl

theorem probe_bit (count node : Nat) (bound : node < count)
    (edges : Finset (Fin (2 * count + 6) × Fin (2 * count + 6))) :
    (∃ edge ∈ edges, edge.1.val = 2 * node ∧ edge.2.val = 2 * node + 1) ↔
      edgeAt count node ∈ edges := by
  obtain ⟨first, second⟩ := edgeAt_val count node bound
  constructor
  · rintro ⟨edge, member, left, right⟩
    have same : edge = edgeAt count node := Prod.ext (Fin.ext (left.trans first.symm)) (Fin.ext (right.trans second.symm))
    exact same ▸ member
  · exact fun member => ⟨_, member, first, second⟩

theorem matching_witness (k : Nat) (big : 7 ≤ k) (crown : Bool)
    (matching : Finset (Finset (Fin k))) (hm : IsM matching) :
    let nr := if crown then k + 2 else k
    let nc := if crown then k + 1 else k
    let A := fun (i : Fin nr) (j : Fin nc) => if crown then
      decide (i.val ≠ k + 1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
    ∃ C : Circuit, (if crown then FanInTwo C ∧ C.size ≤ 2 * k + 1 else Monotone2 C ∧ C.size + 1 ≤ 2 * k) ∧
      Represents A C ∧ ∀ (edge : Fin k × Fin k), edge.1 < edge.2 →
        (C.eval (List.ofFn (fun i : Fin nr => decide (i.val = edge.1.val ∨ i.val = edge.2.val)) ++
          List.ofFn (fun _ : Fin nc => false)) = !crown ↔ ends edge ∈ matching) := by
  cases crown
  · obtain ⟨circ, good, size, repr, ev⟩ := circuit_false k (by omega) matching hm
    refine ⟨circ, ⟨good, size⟩, repr, fun edge ord => ?_⟩
    exact (ev _ _).trans (probe_Pr le_rfl le_rfl edge ord matching hm)
  · obtain ⟨circ, good, size, repr, ev⟩ := circuit_true k (by omega) matching hm
    refine ⟨circ, ⟨good, size⟩, repr, fun edge ord => ?_⟩
    let x := fun i : Fin (k + 2) => decide (i.val = edge.1.val ∨ i.val = edge.2.val)
    let y := fun _ : Fin (k + 1) => false
    have last : (List.ofFn x ++ List.ofFn y).getD (k + 1) false = false := by
      rw [getD_app_left x y _ (by omega)]
      have hleft := edge.1.isLt
      have hright := edge.2.isLt
      simp [x, show k + 1 ≠ edge.1.val by omega, show k + 1 ≠ edge.2.val by omega]
    have flip := ev x y
    rw [last] at flip
    simp only [Bool.false_eq_true, false_or] at flip
    have law : Pr (fun w => w.val) (fun w => k + 2 + w.val) Finset.univ matching
        (fun i => (List.ofFn x ++ List.ofFn y).getD i false) ↔ ends edge ∈ matching :=
      probe_Pr (show k ≤ k + 2 by omega) (show k ≤ k + 1 by omega) edge ord matching hm
    change (circ.eval (List.ofFn x ++ List.ofFn y) = false ↔ ends edge ∈ matching)
    exact (show circ.eval (List.ofFn x ++ List.ofFn y) = false ↔ _ from by
      simpa only [Bool.not_eq_true, not_not] using not_congr flip).trans law

theorem indicator {α : Type} [DecidableEq α] (edges : Finset α) (edge : α) :
    edges.sum (fun other => if other = edge then (1 : Int) else 0) = if edge ∈ edges then 1 else 0 := by
  simp

def active {k nr nc : Nat} (matching : Finset (Finset (Fin k)))
    (x : Fin nr → Bool) (y : Fin nc → Bool) : Prop :=
  Pr (fun w => w.val) (fun w => nr + w.val) Finset.univ matching
    (fun i => (List.ofFn x ++ List.ofFn y).getD i false)

theorem left_active {k nr nc : Nat} (h1 : k ≤ nr) (h2 : k ≤ nc)
    (matching : Finset (Finset (Fin k))) (hm : IsM matching) (x : Fin nr → Bool) :
    active matching x (fun _ : Fin nc => false) ↔ ∃ key ∈ matching, ∀ v ∈ key, x (v.castLE h1) = true := by
  have left (v : Fin k) := getD_app_left x (fun _ : Fin nc => false) v.val (v.isLt.trans_le h1)
  have right (v : Fin k) := getD_app_right x (fun _ : Fin nc => false) v.val (v.isLt.trans_le h2)
  unfold active Pr
  constructor
  · rintro (⟨v, _, _, bad⟩ | ⟨key, hk, lft | rgt⟩)
    · exact Bool.false_ne_true ((right v).symm.trans bad) |>.elim
    · exact ⟨key, hk, fun v hv => (left v).symm.trans (lft v hv)⟩
    · obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [hm.1 key hk]; decide)
      have bad := rgt v hv
      exact Bool.false_ne_true ((right v).symm.trans bad) |>.elim
  · rintro ⟨key, hk, lft⟩
    exact Or.inr ⟨key, hk, Or.inl (fun v hv => (left v).trans (lft v hv))⟩

theorem classify_observations (k : Nat) (big : 7 ≤ k) (crown : Bool) :
    let nr := if crown then k + 2 else k
    let nc := if crown then k + 1 else k
    let A := fun (i : Fin nr) (j : Fin nc) => if crown then
      decide (i.val ≠ k + 1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
    ∀ C : Circuit, (if crown then FanInTwo C ∧ C.size ≤ 2 * k + 1 else Monotone2 C ∧ C.size + 1 ≤ 2 * k) →
      Represents A C → ∃ matching : Finset (Finset (Fin k)), IsM matching ∧
      ∀ (x : Fin nr → Bool) (y : Fin nc → Bool),
        C.eval (List.ofFn x ++ List.ofFn y) = !crown ↔
          (crown = true ∧ (List.ofFn x ++ List.ofFn y).getD (k + 1) false = true) ∨ active matching x y := by
  cases crown
  · intro nr nc A circ good repr
    obtain ⟨matching, hm, law⟩ := classify_false k (by omega) circ good.1 good.2 repr
    refine ⟨matching, hm, fun x y => ?_⟩
    simp only [Bool.not_false, Bool.false_eq_true, false_and, false_or]
    exact law x y
  · intro nr nc A circ good repr
    obtain ⟨matching, hm, law⟩ := classify_true k big circ good.1 good.2 repr
    refine ⟨matching, hm, fun x y => ?_⟩
    have spec := law x y
    change (circ.eval (List.ofFn x ++ List.ofFn y) = false ↔ _)
    simp only [true_and]
    have res := not_congr spec
    simp only [Bool.not_eq_true, not_not] at res
    exact res

theorem min_key_sorted {k : Nat} (key : Finset (Fin k)) (sz : key.card = 2) :
    ∃ edge : Fin k × Fin k, edge.1 < edge.2 ∧ ends edge = key := by
  obtain ⟨a, b, ne, rfl⟩ := Finset.card_eq_two.mp sz
  rcases lt_or_gt_of_ne ne with ord | ord
  · exact ⟨(a, b), ord, rfl⟩
  · exact ⟨(b, a), ord, Finset.pair_comm _ _⟩

theorem exists_observations (k : Nat) (big : 7 ≤ k) (crown : Bool) (matching : Finset (Finset (Fin k)))
    (hm : IsM matching) :
    let nr := if crown then k + 2 else k
    let nc := if crown then k + 1 else k
    let A := fun (i : Fin nr) (j : Fin nc) => if crown then
      decide (i.val ≠ k + 1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
    ∃ C : Circuit, (if crown then FanInTwo C ∧ C.size ≤ 2 * k + 1 else Monotone2 C ∧ C.size + 1 ≤ 2 * k) ∧
      Represents A C ∧ ∀ (x : Fin nr → Bool) (y : Fin nc → Bool),
        C.eval (List.ofFn x ++ List.ofFn y) = !crown ↔
          (crown = true ∧ (List.ofFn x ++ List.ofFn y).getD (k + 1) false = true) ∨ active matching x y := by
  cases crown
  · obtain ⟨c, mon, size, rep, ev⟩ := circuit_false k (by omega) matching hm
    refine ⟨c, ⟨mon, size⟩, rep, fun x y => ?_⟩
    simp only [Bool.not_false, Bool.false_eq_true, false_and, false_or]
    exact ev x y
  · obtain ⟨c, fan, size, rep, ev⟩ := circuit_true k (by omega) matching hm
    refine ⟨c, ⟨fan, size⟩, rep, fun x y => ?_⟩
    have spec := not_congr (ev x y)
    simp only [Bool.not_eq_true, not_not] at spec
    simp only [Bool.not_true, true_and]
    exact spec

theorem probe_as_matching {k nr nc : Nat} (h1 : k ≤ nr) (h2 : k ≤ nc) (crown : Bool)
    (h3 : crown = true → k + 1 < nr) (matching : Finset (Finset (Fin k))) (hm : IsM matching)
    (f : (Fin nr → Bool) → (Fin nc → Bool) → Bool)
    (law : ∀ x y, f x y = !crown ↔ (crown = true ∧ (List.ofFn x ++ List.ofFn y).getD (k + 1) false = true) ∨ active matching x y)
    (edge : Fin k × Fin k) (ord : edge.1 < edge.2) :
      f (fun i => decide (i.val = edge.1.val ∨ i.val = edge.2.val)) (fun _ => false) = !crown ↔ ends edge ∈ matching := by
  let x := fun i : Fin nr => decide (i.val = edge.1.val ∨ i.val = edge.2.val)
  let y := fun _ : Fin nc => false
  change f x y = !crown ↔ _
  rw [law]
  have noextra : ¬ (crown = true ∧ (List.ofFn x ++ List.ofFn y).getD (k + 1) false = true) := by
    rintro ⟨hc, hit⟩
    rw [getD_app_left x y _ (h3 hc)] at hit
    have hl := edge.1.isLt
    have hr := edge.2.isLt
    simp [x, show k + 1 ≠ edge.1.val by omega, show k + 1 ≠ edge.2.val by omega] at hit
  rw [or_iff_right noextra]
  exact probe_Pr h1 h2 edge ord matching hm

def scanFrom (bits : Nat → Bool) (node : Nat) : Nat → Nat
  | 0 => node
  | depth + 1 => scanFrom bits (2 * node + 1 + (if bits node then 1 else 0)) depth

theorem scan_fold (bits : Nat → Bool) (len start : Nat) :
    ∀ xs : List Nat, xs.length = len →
      xs.foldl (fun node _ => 2 * node + 1 + (if bits node then 1 else 0)) start = scanFrom bits start len := by
  induction len generalizing start with
  | zero => intro xs hx; simp_all [scanFrom]
  | succ len ih =>
    rintro (_ | ⟨head, tail⟩) hx
    · simp at hx
    · simp only [List.foldl_cons, scanFrom]
      apply ih
      simpa using hx

def terms (depth node : Nat) : List (Finset Nat × Bool) :=
  match depth with
  | 0 => [({node}, true)]
  | d + 1 =>
    let left := terms d (2 * node + 1)
    let right := terms d (2 * node + 2)
    left.map (fun term => (insert node term.1, term.2)) ++
      right.map (fun term => (insert node term.1, !term.2)) ++ right

theorem terms_count (depth node : Nat) : (terms depth node).length = 3 ^ depth := by
  induction depth generalizing node with
  | zero => rfl
  | succ depth ih => simp only [terms, List.length_append, List.length_map, ih, pow_succ]; omega

def sign (positive : Bool) : Int := if positive then 1 else -1

def weight (bits : Nat → Bool) (term : Finset Nat × Bool) : Int :=
  if ∀ j ∈ term.1, bits j = false then sign term.2 else 0

theorem weight_extend (bits : Nat → Bool) (node : Nat) (term : Finset Nat × Bool) :
    weight bits (insert node term.1, term.2) = if bits node then 0 else weight bits term := by
  cases hn : bits node <;> simp [weight, hn]

theorem weight_flip (bits : Nat → Bool) (node : Nat) (term : Finset Nat × Bool) :
    weight bits (insert node term.1, !term.2) = -(weight bits (insert node term.1, term.2)) := by
  rcases term with ⟨support, positive⟩
  cases positive <;> simp [weight, sign] <;> split <;> simp_all

theorem negated_weights (bits : Nat → Bool) (lst : List (Finset Nat × Bool)) :
    (lst.map (fun x => -weight bits x)).sum = -(lst.map (weight bits)).sum := by
  induction lst with
  | nil => simp
  | cons hd tl ih => simp [ih, add_comm]

theorem terms_score (bits : Nat → Bool) (depth node : Nat) :
    ((terms depth node).map (weight bits)).sum = if bits (scanFrom bits node depth) then 0 else 1 := by
  induction depth generalizing node with
  | zero => cases hb : bits node <;> simp [terms, scanFrom, weight, sign, hb]
  | succ depth ih =>
    cases hb : bits node <;>
      simp [terms, scanFrom, List.map_map, Function.comp_def, weight_flip, weight_extend, hb, ih,
        negated_weights, Nat.add_assoc]

theorem counted_terms (bits : Nat → Bool) (accept : Finset Nat × Bool → Bool)
    (correct : ∀ t, accept t = true ↔ ((∃ v ∈ t.1, bits v = true) ↔ t.2 = true))
    (lst : List (Finset Nat × Bool)) :
    2 * ((lst.filter accept).length : Int) + 2 * (lst.map (weight bits)).sum =
      (lst.length : Int) + (lst.map (weight (fun _ => false))).sum := by
  induction lst with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨support, positive⟩
    have local_eq : 2 * (if accept (support, positive) then (1 : Int) else 0) + 2 * weight bits (support, positive) =
        1 + weight (fun _ => false) (support, positive) := by
      have eq := correct (support, positive)
      by_cases hit : ∃ v ∈ support, bits v = true
      · have hn : ¬ ∀ v ∈ support, bits v = false := by
          obtain ⟨v, hv, yes⟩ := hit
          intro no
          simpa [no v hv] using yes
        cases positive <;> cases hb : accept (support, _) <;> simp_all [weight, sign]
      · have hn : ∀ v ∈ support, bits v = false := by
          intro v hv
          exact Bool.eq_false_iff.mpr (fun yes => hit ⟨v, hv, yes⟩)
        cases positive <;> cases hb : accept (support, _) <;> simp_all [weight, sign] <;> grind
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, List.filter_cons]
    cases acc : accept (support, positive) <;> simp_all <;> omega

theorem term_support (depth node : Nat) (term : Finset Nat × Bool) (member : term ∈ terms depth node) :
    (∀ vertex ∈ term.1, node ≤ vertex) ∧
    ∃ leaf ∈ term.1, (∀ vertex ∈ term.1, vertex ≤ leaf) ∧
      2 ^ depth * (node + 1) ≤ leaf + 1 ∧ leaf + 1 < 2 ^ depth * (node + 2) := by
  induction depth generalizing node term with
  | zero =>
    simp only [terms, List.mem_singleton] at member
    subst term
    simp
  | succ depth ih =>
    have lift (child : Nat) (term' : Finset Nat × Bool) (hmem : term' ∈ terms depth child)
        (poss : child = 2 * node + 1 ∨ child = 2 * node + 2)
        (form : term.1 = insert node term'.1 ∨ term.1 = term'.1) :
        (∀ vertex ∈ term.1, node ≤ vertex) ∧
        ∃ leaf ∈ term.1, (∀ vertex ∈ term.1, vertex ≤ leaf) ∧
          2 ^ (depth + 1) * (node + 1) ≤ leaf + 1 ∧ leaf + 1 < 2 ^ (depth + 1) * (node + 2) := by
      obtain ⟨lower, leaf, hLeaf, upper, lo, hi⟩ := ih _ _ hmem
      have smaller : node ≤ child := by rcases poss with h | h <;> omega
      have extent : 2 ^ (depth + 1) * (node + 1) ≤ leaf + 1 ∧ leaf + 1 < 2 ^ (depth + 1) * (node + 2) := by
        rw [pow_succ]
        rcases poss with rfl | rfl <;> constructor <;> nlinarith [Nat.zero_le (2 ^ depth)]
      rcases form with eq | eq
      · rw [eq]
        simp only [Finset.forall_mem_insert, le_refl, true_and]
        exact ⟨fun v hv => smaller.trans (lower v hv), leaf, Finset.mem_insert_of_mem hLeaf,
          ⟨smaller.trans (lower leaf hLeaf), upper⟩, extent⟩
      · rw [eq]
        exact ⟨fun v hv => smaller.trans (lower v hv), leaf, hLeaf, upper, extent⟩
    simp only [terms, List.mem_append, List.mem_map] at member
    rcases member with ((⟨prev, hm, rfl⟩ | ⟨prev, hm, rfl⟩) | hm)
    · exact lift _ _ hm (Or.inl rfl) (Or.inl rfl)
    · exact lift _ _ hm (Or.inr rfl) (Or.inl rfl)
    · exact lift _ _ hm (Or.inr rfl) (Or.inr rfl)

def patterns (depth node : Nat) := (terms depth node).map Prod.fst

theorem distinct_patterns (depth node : Nat) : (patterns depth node).Nodup := by
  induction depth generalizing node with
  | zero => simp [patterns, terms]
  | succ d ih =>
    let left := patterns d (2 * node + 1)
    let right := patterns d (2 * node + 2)
    have bounds {child : Nat} {key : Finset Nat} (mem : key ∈ patterns d child) :
        (∀ vertex ∈ key, child ≤ vertex) ∧ ∃ leaf ∈ key, (∀ vertex ∈ key, vertex ≤ leaf) ∧
          2 ^ d * (child + 1) ≤ leaf + 1 ∧ leaf + 1 < 2 ^ d * (child + 2) := by
      obtain ⟨term, ht, rfl⟩ := List.mem_map.mp mem
      exact term_support d child term ht
    have freshL (key) (mem : key ∈ left) : node ∉ key := fun hit => by
      have := (bounds mem).1 node hit
      omega
    have freshR (key) (mem : key ∈ right) : node ∉ key := fun hit => by
      have := (bounds mem).1 node hit
      omega
    have apart (key) (hl : key ∈ left) (hr : key ∈ right) : False := by
      obtain ⟨a, ha, maxA, _, hi⟩ := (bounds hl).2
      obtain ⟨b, hb, maxB, lo, _⟩ := (bounds hr).2
      have eq : a = b := le_antisymm (maxB a ha) (maxA b hb)
      rw [eq] at hi
      have splitEq : 2 * node + 1 + 2 = 2 * node + 2 + 1 := by omega
      rw [splitEq] at hi
      omega
    have app : patterns (d + 1) node = left.map (insert node) ++ right.map (insert node) ++ right := by
      simp [patterns, terms, List.map_map, Function.comp_def, left, right]
    rw [app, List.nodup_append', List.nodup_append']
    refine ⟨⟨(ih _).map_on (fun x hx y hy => Finset.insert_injOn_notMem node (freshL x hx) (freshL y hy)),
      (ih _).map_on (fun x hx y hy => Finset.insert_injOn_notMem node (freshR x hx) (freshR y hy)), ?_⟩,
      ih _, ?_⟩
    · intro key hl hr
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      obtain ⟨y, hy, eq⟩ := List.mem_map.mp hr
      have same := Finset.insert_injOn_notMem node (freshR y hy) (freshL x hx) eq
      exact apart x hx (same ▸ hy)
    · intro key hIns hRight
      apply freshR _ hRight
      rcases List.mem_append.mp hIns with hIns | hIns <;>
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hIns <;> exact Finset.mem_insert_self _ _

open Finset

theorem alt_sum (W : Finset Nat) :
    W.powerset.sum (fun V => (-1 : ℤ) ^ (W.card - V.card)) = if W = ∅ then 1 else 0 := by
  have h : ∀ V ∈ W.powerset, (-1 : ℤ) ^ (W.card - V.card) = (-1) ^ W.card * (-1) ^ V.card := by
    intro V hV
    have hle : V.card ≤ W.card := card_le_card (mem_powerset.mp hV)
    have e : (-1 : ℤ) ^ W.card = (-1) ^ (W.card - V.card) * (-1) ^ V.card := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [e, mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  rw [sum_congr rfl h, ← mul_sum, sum_powerset_neg_one_pow_card]
  split_ifs with hW <;> simp [hW]

theorem mob_ind (A S : Finset Nat) :
    S.powerset.sum (fun T => (-1 : ℤ) ^ (S.card - T.card) * (if A ⊆ T then 1 else 0))
      = if A = S then 1 else 0 := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  by_cases hAS : A ⊆ S
  · have key : (S.powerset.filter (fun T => A ⊆ T)).sum (fun T => (-1 : ℤ) ^ (S.card - T.card))
        = (S \ A).powerset.sum (fun V => (-1 : ℤ) ^ ((S \ A).card - V.card)) := by
      apply sum_nbij' (fun T => T \ A) (fun V => V ∪ A)
      · intro T hT
        simp only [mem_filter, mem_powerset] at hT
        simp only [mem_powerset]
        exact sdiff_subset_sdiff hT.1 le_rfl
      · intro V hV
        simp only [mem_powerset] at hV
        simp only [mem_filter, mem_powerset]
        exact ⟨union_subset (hV.trans sdiff_subset) hAS, subset_union_right⟩
      · intro T hT
        simp only [mem_filter, mem_powerset] at hT
        exact sdiff_union_of_subset hT.2
      · intro V hV
        simp only [mem_powerset] at hV
        exact union_sdiff_cancel_right (disjoint_of_subset_left hV disjoint_sdiff_self_left)
      · intro T hT
        simp only [mem_filter, mem_powerset] at hT
        have h1 := card_sdiff_add_card_eq_card hAS
        have h2 := card_sdiff_add_card_eq_card hT.2
        have h3 := card_le_card hT.1
        congr 1
        omega
    rw [key, alt_sum]
    by_cases hA : A = S
    · subst hA; simp
    · rw [if_neg hA, if_neg]
      intro he
      exact hA (subset_antisymm hAS (sdiff_eq_empty_iff_subset.mp he))
  · have : S.powerset.filter (fun T => A ⊆ T) = ∅ := by
      rw [filter_eq_empty_iff]
      intro T hT hA
      exact hAS (hA.trans (mem_powerset.mp hT))
    rw [this, sum_empty, if_neg]
    rintro rfl
    exact hAS subset_rfl

def evaluateRows (data : List (Finset Nat × Int)) (missing : Finset Nat) : Int :=
  (data.map (fun t => if t.1 ⊆ missing then t.2 else 0)).sum

def extract (key : Finset Nat) (val : Finset Nat → Int) : Int :=
  key.powerset.sum (fun sub => (-1 : Int) ^ (key.card - sub.card) * val sub)

theorem extract_rows (key : Finset Nat) (data : List (Finset Nat × Int)) :
    extract key (evaluateRows data) = (data.map (fun t => if t.1 = key then t.2 else 0)).sum := by
  induction data with
  | nil => simp [extract, evaluateRows]
  | cons term rest ih =>
    have expand (sub : Finset Nat) : evaluateRows (term :: rest) sub =
        (if term.1 ⊆ sub then (1 : Int) else 0) * term.2 + evaluateRows rest sub := by
      simp [evaluateRows, ite_mul]
    unfold extract at ih ⊢
    simp_rw [expand, mul_add, ← mul_assoc]
    rw [sum_add_distrib, ← sum_mul, mob_ind, ih]
    simp [ite_mul]

theorem coefficients_unique (left right : List (Finset Nat × Int)) (offset : Int) (key : Finset Nat)
    (nonempty : key ≠ ∅) (agree : ∀ sub ⊆ key, evaluateRows left sub = offset + evaluateRows right sub) :
    (left.map (fun t => if t.1 = key then t.2 else 0)).sum = (right.map (fun t => if t.1 = key then t.2 else 0)).sum := by
  rw [← extract_rows, ← extract_rows]
  unfold extract
  rw [sum_congr rfl (fun sub mem => congrArg (_ * ·) (agree sub (mem_powerset.mp mem)))]
  simp_rw [mul_add]
  rw [sum_add_distrib, ← sum_mul, alt_sum, if_neg nonempty, zero_mul, zero_add]

theorem coefficient_present (data : List (Finset Nat × Int)) (key : Finset Nat)
    (nonzero : (data.map (fun t => if t.1 = key then t.2 else 0)).sum ≠ 0) : key ∈ data.map Prod.fst := by
  contrapose! nonzero
  induction data with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at nonzero
    simp [Ne.symm nonzero.1, ih nonzero.2]

theorem distinct_coefficient (data : List (Finset Nat × Int)) (term : Finset Nat × Int)
    (nd : (data.map Prod.fst).Nodup) (occ : term ∈ data) :
    (data.map (fun t => if t.1 = term.1 then t.2 else 0)).sum = term.2 := by
  induction data with
  | nil => simp at occ
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.mp occ with rfl | occurs
    · have zero := mt (coefficient_present tl term.1) nd.1
      simp only [not_not] at zero
      simp [zero]
    · have ne : hd.1 ≠ term.1 := fun eq => nd.1 (eq ▸ List.mem_map_of_mem occurs)
      simp [ne, ih nd.2 occurs]

theorem row_cost_lower (depth : Nat) (data : List (Finset Nat × Int)) (offset : Int)
    (agree : ∀ sub ⊆ Finset.range (2 ^ (depth + 1) - 1),
      ((terms depth 0).map (weight (fun j => decide (j ∉ sub)))).sum = offset + evaluateRows data sub) :
    3 ^ depth ≤ data.length := by
  let expected := (terms depth 0).map (fun t => (t.1, sign t.2))
  have nd : (expected.map Prod.fst).Nodup := by
    simpa only [patterns, expected, List.map_map, Function.comp_def] using distinct_patterns depth 0
  have needed : (expected.map Prod.fst).toFinset ⊆ (data.map Prod.fst).toFinset := by
    intro key present
    obtain ⟨term, found, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
    obtain ⟨source, member, rfl⟩ := List.mem_map.mp found
    obtain ⟨_, leaf, leafHit, highest, low, high⟩ := term_support depth 0 source member
    have subrange : source.1 ⊆ Finset.range (2 ^ (depth + 1) - 1) := by
      intro v hv
      have := highest v hv
      rw [Finset.mem_range, pow_succ]
      simp at high
      omega
    have nonempty := Finset.nonempty_iff_ne_empty.mp (show source.1.Nonempty from ⟨_, leafHit⟩)
    have same := coefficients_unique expected data offset source.1 nonempty (fun sub hs => by
      have eq := agree sub (hs.trans subrange)
      have fn : weight (fun j => decide (j ∉ sub)) = fun t : Finset Nat × Bool => if t.1 ⊆ sub then sign t.2 else 0 := by
        funext t
        unfold weight
        by_cases included : t.1 ⊆ sub
        · have all : ∀ j ∈ t.1, decide (j ∉ sub) = false := fun j hj => by simp [included hj]
          rw [if_pos all, if_pos included]
        · have fail : ¬∀ j ∈ t.1, decide (j ∉ sub) = false := by
            intro ht
            apply included
            intro j hj
            simpa using ht j hj
          rw [if_neg fail, if_neg included]
      rw [fn] at eq
      simpa only [expected, evaluateRows, List.map_map, Function.comp_def] using eq)
    apply List.mem_toFinset.mpr
    apply coefficient_present
    rw [← same, distinct_coefficient expected (source.1, sign source.2) nd (List.mem_map_of_mem member)]
    cases source.2 <;> simp [sign]
  have bound := Finset.card_le_card needed
  rw [List.toFinset_card_of_nodup nd, List.length_map, show expected.length = 3 ^ depth by simp [expected, terms_count]] at bound
  exact bound.trans ((List.toFinset_card_le _).trans (List.length_map _).le)

end PEqualNP.Outside.L_meta_33668

open PEqualNP.Outside.L_meta_33668

theorem PEqualNP.Outside.L_meta_33668 : (let pairs := fun n : Nat => (List.finRange n).flatMap (fun i =>
  ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)))
∀ (h : Nat) (crown : Bool),
  let N := 2^(h+1)-1
  let k := 2*N+6
  let nr := if crown then k+2 else k
  let nc := if crown then k+1 else k
  let A := fun (i : Fin nr) (j : Fin nc) => if crown then
    decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
  let Fn := (Fin nr → Bool) → (Fin nc → Bool) → Bool
  let eligible := fun f : Fn => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    (if crown then PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2*k+1 else PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k) ∧
    PEqualNP.Represents.Represents A C ∧ ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
  let probe := fun f : Fn => (pairs k).toFinset.filter (fun e =>
    f (fun i => decide (i.val = e.1.val ∨ i.val = e.2.val)) (fun _ => false) = !crown)
  let vs := (pairs k).toFinset
  let block := fun (e : Fin k × Fin k) (j : Nat) => e.1.val = 2*j ∧ e.2.val = 2*j+1
  let blocks := vs.filter (fun e => ∃ j < N, block e j)
  let fits := fun f : Fn => eligible f ∧ probe f ⊆ blocks
  let value := fun (f : Fn) (j : Nat) => decide (∃ e ∈ probe f, block e j)
  let target := fun f : Fn =>
    let leaf := (List.range h).foldl (fun j _ => 2*j+1+(if value f j then 1 else 0)) 0
    if value f leaf then (1 : Int) else 0
  let Rows := List (((Fin nr → Bool) × (Fin nc → Bool)) × Bool)
  let score := fun (L : Rows) (f : Fn) => (L.filter (fun r => decide (f r.1.1 r.1.2 = r.2))).length
  let realizes := fun L : Rows => ∃ b : Int, ∀ f : Fn, fits f → (score L f : Int) = b + target f
  let strong := fun I : Finset (Fin k × Fin k) => ∀ K ⊆ I,
    ∃ (b : Int) (w : Fin k × Fin k → Int), ∀ f : Fn, fits f → probe f ∩ I = K →
      target f = b + ((probe f) \ I).sum w
  let adap := fun d : Nat =>
    ∃ (ask : Nat → Fin k × Fin k) (b : Nat → Int) (w : Nat → (Fin k × Fin k) → Int),
      ∀ f : Fn, fits f →
        let j := (List.range d).foldl (fun u _ => 2*u+1+(if ask u ∈ probe f then 1 else 0)) 0
        target f = b j + (probe f).sum (w j)
  (∀ S ⊆ blocks, ∃ f : Fn, fits f ∧ probe f = S) ∧
  (∃ L : Rows, L.length = 3^h ∧ (∀ r ∈ L, ∀ j, r.1.2 j = false) ∧
    ∀ f : Fn, fits f → (score L f : Int) = (((3^h-1)/2 : Nat) : Int) + target f) ∧
  (∀ L : Rows, realizes L → 3^h ≤ L.length) ∧
  adap h ∧ (∀ d, adap d → h ≤ d) ∧
  (∃ I ⊆ vs, strong I ∧ I.card = 2^h-1) ∧ (∀ I ⊆ vs, strong I → 2^h-1 ≤ I.card)) := by
  intro pairs h crown N k nr nc A Fn eligible probe vs block blocks fits value target Rows score realizes strong adap
  have count_bound : 0 < N := by
    dsimp [N]
    have hp : 0 < 2 ^ h := Nat.two_pow_pos h
    rw [pow_succ]
    omega
  have bit_rule (f : Fn) (node : Nat) (bound : node < N) :
      value f node = decide (edgeAt N node ∈ probe f) :=
    decide_eq_decide.2 (probe_bit N node bound (probe f))
  have leaf_bound (bits : Nat → Bool) : route bits h < N := by
    have := (route_bounds bits h).2
    dsimp [N]
    omega
  have internal_bound (node : Nat) (internal : node < 2 ^ h - 1) : node < N := by
    dsimp [N]
    rw [pow_succ]
    omega
  have strict_mem (edge : Fin k × Fin k) (order : edge.1 < edge.2) : edge ∈ vs := by
    rcases edge with ⟨left, right⟩
    simp [vs, pairs, List.mem_flatMap, List.mem_map, order]
  let internal := (Finset.range (2 ^ h - 1)).image (edgeAt N)
  have internal_iff (node : Nat) (bound : node < N) :
      edgeAt N node ∈ internal ↔ node < 2 ^ h - 1 := by
    constructor
    · intro hm
      obtain ⟨other, hOther, eq⟩ := Finset.mem_image.mp hm
      have within := Finset.mem_range.mp hOther
      have eq' := congrArg (fun edge : Fin k × Fin k => edge.1.val) eq
      change (edgeAt N other).1.val = (edgeAt N node).1.val at eq'
      rw [(edgeAt_val _ _ (internal_bound other within)).1, (edgeAt_val _ _ bound).1] at eq'
      omega
    · intro within
      exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr within, rfl⟩
  have fixed_upper : ∃ I ⊆ vs, strong I ∧ I.card = 2 ^ h - 1 := by
    refine ⟨internal, ?_, ?_, ?_⟩
    · intro edge hm
      obtain ⟨node, hNode, rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨left, right⟩ := edgeAt_val N node (internal_bound node (Finset.mem_range.mp hNode))
      apply strict_mem
      change (edgeAt N node).1.val < (edgeAt N node).2.val
      omega
    · intro K hK
      let bits := fun node => decide (edgeAt N node ∈ K)
      let leaf := route bits h
      refine ⟨0, fun edge => if edge = edgeAt N leaf then 1 else 0, ?_⟩
      intro f hf fiber
      have leaf_free : edgeAt N leaf ∉ internal := by
        rw [internal_iff leaf (leaf_bound bits)]
        have := (route_bounds bits h).1
        dsimp [leaf]
        omega
      have path : route (value f) h = leaf := by
        apply route_congr
        intro node bound
        have hi : node < 2 ^ h - 1 := by omega
        rw [bit_rule _ _ (internal_bound _ hi)]
        change decide (_ ∈ probe f) = decide (_ ∈ K)
        rw [← fiber]
        simp [(internal_iff node (internal_bound _ hi)).2 hi]
      change (if value f (route (value f) h) then (1 : Int) else 0) = _
      rw [path, bit_rule _ _ (leaf_bound bits), indicator]
      simp [leaf_free] <;> rfl
    · unfold internal
      rw [Finset.card_image_iff.mpr, Finset.card_range]
      intro left leftMem right rightMem eq
      have eq' := congrArg (fun edge : Fin k × Fin k => edge.1.val) eq
      change (edgeAt N left).1.val = (edgeAt N right).1.val at eq'
      rw [(edgeAt_val _ _ (internal_bound _ (Finset.mem_range.mp leftMem))).1,
        (edgeAt_val _ _ (internal_bound _ (Finset.mem_range.mp rightMem))).1] at eq'
      omega
  have depth_upper : adap h := by
    refine ⟨edgeAt N, fun _ => 0, fun j other => if other = edgeAt N j then 1 else 0, ?_⟩
    intro f hf
    let bits := fun node => decide (edgeAt N node ∈ probe f)
    have path : route (value f) h = route bits h := by
      apply route_congr
      intro node bound
      apply bit_rule
      dsimp [N]
      rw [pow_succ]
      omega
    have eq : (if value f (route (value f) h) then (1 : Int) else 0) =
        0 + (probe f).sum (fun other => if other = edgeAt N (route bits h) then 1 else 0) := by
      rw [path, bit_rule _ _ (leaf_bound bits), indicator]
      simp
    simp only [target, route, bits, decide_eq_true_eq] at eq ⊢
    exact eq
  have cube : ∀ S ⊆ blocks, ∃ f : Fn, fits f ∧ probe f = S := by
    intro S subset
    have ordered (edge : Fin k × Fin k) (hm : edge ∈ vs) : edge.1 < edge.2 := by
      rcases edge with ⟨u, v⟩
      simpa [vs, pairs, List.mem_flatMap, List.mem_map] using hm
    have within : S ⊆ vs := subset.trans (Finset.filter_subset _ _)
    have form (edge : Fin k × Fin k) (hm : edge ∈ S) :
        ∃ node : Nat, edge.1.val = 2 * node ∧ edge.2.val = 2 * node + 1 := by
      obtain ⟨node, _, spec⟩ := (Finset.mem_filter.mp (subset hm)).2
      exact ⟨node, spec⟩
    obtain ⟨circ, good, repr, law⟩ := matching_witness k (by dsimp [k]; omega) crown
      (S.image ends) (block_matching S form)
    let f : Fn := fun x y => circ.eval (List.ofFn x ++ List.ofFn y)
    have eq : probe f = S := by
      ext edge
      change edge ∈ vs.filter _ ↔ edge ∈ S
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hEdge, yes⟩
        obtain ⟨other, hm, key⟩ := Finset.mem_image.mp ((law edge (ordered edge hEdge)).1 yes)
        exact ends_injective other edge (ordered other (within hm)) (ordered edge hEdge) key ▸ hm
      · intro hm
        exact ⟨within hm, (law edge (ordered _ (within hm))).2 (Finset.mem_image_of_mem ends hm)⟩
    exact ⟨f, ⟨⟨circ, good, repr, fun _ _ => rfl⟩, eq ▸ subset⟩, eq⟩
  let chain := chainEdges h N
  let last := edgeAt N (lastNode h)
  have in_chain (level : Nat) (hl : level ≤ h) : edgeAt N (lastNode level) ∈ chain :=
    Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
  have chain_subset : chain ⊆ blocks := by
    intro edge hit
    obtain ⟨level, hl, rfl⟩ := Finset.mem_image.mp hit
    have bound : lastNode level < N := chain_small h level (Nat.le_of_lt_succ (Finset.mem_range.mp hl))
    have spec := edgeAt_val _ _ bound
    exact Finset.mem_filter.mpr ⟨strict_mem _ (show (edgeAt N (lastNode level)).1.val < _ by omega),
      lastNode level, bound, spec⟩
  have chain_eval (S : Finset (Fin k × Fin k)) (hs : S ⊆ chain) (f : Fn) (hf : probe f = S) :
      target f = if S = {last} then 1 else 0 := by
    have iff_bit (node : Nat) : value f node = true ↔ ∃ level ≤ h, node = lastNode level ∧ edgeAt N node ∈ S := by
      constructor
      · intro yes
        change decide (∃ e ∈ probe f, block e node) = true at yes
        obtain ⟨e, he, first, second⟩ := of_decide_eq_true yes
        have mem : e ∈ S := hf ▸ he
        obtain ⟨level, hl, rfl⟩ := Finset.mem_image.mp (hs mem)
        have depth := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
        have eq := (edgeAt_val N (lastNode level) (chain_small h level depth)).1
        have same : node = lastNode level := by omega
        exact ⟨level, depth, same, same ▸ mem⟩
      · rintro ⟨level, depth, rfl, mem⟩
        rw [bit_rule _ _ (chain_small _ _ depth), hf]
        exact decide_eq_true mem
    have bv (i : Nat) (hi : i ≤ h) : value f (lastNode i) = true ↔ edgeAt N (lastNode i) ∈ S := by
      rw [bit_rule _ _ (chain_small _ _ hi), hf, decide_eq_true_eq]
    have increasing : StrictMono lastNode := fun i j lt => by simpa only [left_chain] using route_inj_height (fun _ => false) lt
    have outside (node) (gt : lastNode h < node) : value f node = false := by
      cases yes : value f node
      · rfl
      · obtain ⟨level, depth, rfl, mem⟩ := (iff_bit _).mp yes
        exact False.elim ((not_lt_of_ge (increasing.monotone depth)) gt)
    have eq : value f (route (value f) h) = true ↔ S = {last} := by
      rw [left_only (h := h) _ outside]
      constructor
      · rintro ⟨leaf, zero⟩
        ext edge
        rw [Finset.mem_singleton]
        constructor
        · intro hit
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hs hit)
          have le := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          by_cases eq : i = h
          · rw [eq]
          · have val := (bv i le).mpr hit
            rw [zero i (by omega)] at val
            contradiction
        · rintro rfl
          exact (bv h le_rfl).mp leaf
      · rintro rfl
        refine ⟨(bv h le_rfl).mpr (Finset.mem_singleton_self _), ?_⟩
        intro level lt
        cases yes : value f (lastNode level)
        · rfl
        · have eq' := Finset.mem_singleton.mp ((bv level lt.le).mp yes)
          have same := (edgeAt_inj (chain_small h level lt.le) (chain_small h h le_rfl)).mp eq'
          exact False.elim (lt.ne (increasing.injective same))
    change (if value f (route (value f) h) then (1 : Int) else 0) = _
    simp only [eq]
  have adaptive_lower : ∀ d, adap d → h ≤ d := by
    intro d adaptive
    obtain ⟨ask, base, weights, law⟩ := adaptive
    by_contra! short
    let initial : Finset (Fin k × Fin k) := {last}
    let used := queryTrace ask initial d
    have used_size : used.card ≤ d := by
      exact (Finset.card_image_le).trans (Finset.card_range d).le
    have capacity : 1 < (chain \ used).card := by
      have le := Finset.card_le_card_sdiff_add_card (s := chain) (t := used)
      have card : chain.card = h + 1 := chainEdges_card h
      omega
    obtain ⟨a, ha, b, hb, diff⟩ := Finset.one_lt_card.mp capacity
    obtain ⟨haChain, haFree⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨hbChain, hbFree⟩ := Finset.mem_sdiff.mp hb
    have samePath := trace_unchanged initial a b ask d haFree hbFree
    dsimp only at samePath
    let path := fun S : Finset (Fin k × Fin k) => route (fun j => decide (ask j ∈ S)) d
    have eq (S : Finset (Fin k × Fin k)) (sub : S ⊆ chain) :
        (if S = initial then (1 : Int) else 0) = base (path S) + S.sum (weights (path S)) := by
      obtain ⟨f, ok, same⟩ := cube S (sub.trans chain_subset)
      have spec := law f ok
      rw [chain_eval S sub f same] at spec
      simp only [same] at spec
      simpa only [path, route, decide_eq_true_eq, initial] using spec
    have incl : initial ⊆ chain := Finset.singleton_subset_iff.mpr (in_chain h le_rfl)
    have tog (S : Finset (Fin k × Fin k)) (s : S ⊆ chain) (v : Fin k × Fin k) (hv : v ∈ chain) : toggleEdge S v ⊆ chain := by
      unfold toggleEdge
      split
      · exact (Finset.erase_subset _ _).trans s
      · exact Finset.insert_subset hv s
    have e0 := eq initial incl
    have e1 := eq _ (tog _ incl _ haChain)
    have e2 := eq _ (tog _ incl _ hbChain)
    have e3 := eq _ (tog _ (tog _ incl _ haChain) _ hbChain)
    have neq (S : Finset (Fin k × Fin k)) (v : Fin k × Fin k) : toggleEdge S v ≠ S := by
      intro equal
      have flip := mem_toggleEdge S v v
      rw [equal] at flip
      simp only [↓reduceIte] at flip
      tauto
    have both : toggleEdge (toggleEdge initial a) b ≠ initial := by
      intro equal
      have flip := mem_toggleEdge (toggleEdge initial a) b a
      rw [equal, if_neg diff, mem_toggleEdge, if_pos rfl] at flip
      tauto
    change path (toggleEdge initial a) = path initial ∧ path (toggleEdge initial b) = path initial ∧
      path (toggleEdge (toggleEdge initial a) b) = path initial at samePath
    simp only [ite_true, if_pos rfl, if_neg (neq _ _), if_neg both, samePath.1, samePath.2.1, samePath.2.2] at e0 e1 e2 e3
    have rectangle := toggle_square initial a b diff (weights (path initial))
    linarith only [e0, e1, e2, e3, rectangle]
  let rowX := fun (support : Finset Nat) (i : Fin nr) => decide (i.val < 2*N ∧ i.val / 2 ∈ support)
  have row_law (f : Fn) (ok : fits f) (support : Finset Nat) :
      f (rowX support) (fun _ => false) = !crown ↔ ∃ node ∈ support, value f node = true := by
    obtain ⟨⟨circ, good, repr, eval⟩, sub⟩ := ok
    obtain ⟨matching, hm, law⟩ := classify_observations k (by dsimp [k]; omega) crown circ good repr
    have h1 : k ≤ nr := by dsimp [nr]; split <;> omega
    have h2 : k ≤ nc := by dsimp [nc]; split <;> omega
    have probe_law (edge : Fin k × Fin k) (ord : edge.1 < edge.2) :
        edge ∈ probe f ↔ ends edge ∈ matching := by
      let x := fun i : Fin nr => decide (i.val = edge.1.val ∨ i.val = edge.2.val)
      let y := fun _ : Fin nc => false
      change edge ∈ vs.filter _ ↔ _
      rw [Finset.mem_filter, and_iff_right (strict_mem _ ord)]
      change f x y = !crown ↔ _
      rw [eval, law]
      have noextra : ¬ (crown = true ∧ (List.ofFn x ++ List.ofFn y).getD (k + 1) false = true) := by
        rintro ⟨hc, hit⟩
        have bound : k + 1 < nr := by simp [nr, hc]
        rw [getD_app_left x y _ bound] at hit
        have hl := edge.1.isLt
        have hr := edge.2.isLt
        simp [x, show k + 1 ≠ edge.1.val by omega, show k + 1 ≠ edge.2.val by omega] at hit
      rw [or_iff_right noextra]
      exact probe_Pr h1 h2 edge ord matching hm
    rw [eval, law]
    have noextra : ¬ (crown = true ∧ (List.ofFn (rowX support) ++ List.ofFn (fun _ : Fin nc => false)).getD (k + 1) false = true) := by
      rintro ⟨hc, hit⟩
      rw [getD_app_left _ _ _ (show k + 1 < nr by simp [nr, hc])] at hit
      simp [rowX, k] at hit
      omega
    rw [or_iff_right noextra, left_active h1 h2 matching hm]
    constructor
    · rintro ⟨key, member, contained⟩
      obtain ⟨edge, ord, rfl⟩ := min_key_sorted key (hm.1 key member)
      have hEdge := (probe_law edge ord).2 member
      obtain ⟨node, hNode, first, second⟩ := (Finset.mem_filter.mp (sub hEdge)).2
      have firstHit := contained edge.1 (Finset.mem_insert_self _ _)
      change decide (edge.1.val < 2 * N ∧ edge.1.val / 2 ∈ support) = true at firstHit
      rw [first, decide_eq_true_eq] at firstHit
      refine ⟨node, ?_, ?_⟩
      · simpa using firstHit.2
      · change decide (∃ e ∈ probe f, block e node) = true
        exact decide_eq_true ⟨edge, hEdge, first, second⟩
    · rintro ⟨node, hNode, bit⟩
      change decide (∃ e ∈ probe f, block e node) = true at bit
      obtain ⟨edge, hEdge, first, second⟩ := of_decide_eq_true bit
      obtain ⟨j, hj, hj1, hj2⟩ := (Finset.mem_filter.mp (sub hEdge)).2
      change edge.1.val = 2*j at hj1
      have bound : node < N := by omega
      have ord : edge.1 < edge.2 := by change edge.1.val < edge.2.val; omega
      refine ⟨_, (probe_law _ ord).1 hEdge, ?_⟩
      intro v hv
      simp only [ends, Finset.mem_insert, Finset.mem_singleton] at hv
      change decide (v.val < 2*N ∧ v.val / 2 ∈ support) = true
      rw [decide_eq_true_eq]
      rcases hv with rfl | rfl <;> constructor
      · omega
      · rwa [show edge.1.val / 2 = node by omega]
      · omega
      · rwa [show edge.2.val / 2 = node by omega]
  have observations_upper : ∃ L : Rows, L.length = 3^h ∧ (∀ r ∈ L, ∀ j, r.1.2 j = false) ∧
      ∀ f : Fn, fits f → (score L f : Int) = (((3^h-1)/2 : Nat) : Int) + target f := by
    let row := fun (t : Finset Nat × Bool) => ((rowX t.1, fun _ : Fin nc => false), if t.2 then !crown else crown)
    refine ⟨(terms h 0).map row, by simp [terms_count], ?_, ?_⟩
    · intro r hr j
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hr
      rfl
    · intro f ok
      let accept := fun t : Finset Nat × Bool => decide (f (row t).1.1 (row t).1.2 = (row t).2)
      have correct (t : Finset Nat × Bool) : accept t = true ↔ ((∃ v ∈ t.1, value f v = true) ↔ t.2 = true) := by
        rcases t with ⟨support, positive⟩
        have eq := row_law f ok support
        change (decide (f (rowX support) (fun _ => false) = (if positive then !crown else crown)) = true) ↔ _
        rw [decide_eq_true_eq]
        cases positive <;> simp only [Bool.false_eq_true, eq_self, ↓reduceIte, iff_true, iff_false]
        · rw [← eq]
          generalize f (rowX support) (fun _ => false) = ans
          cases ans <;> cases crown <;> decide
        · exact eq
      have eq := counted_terms (value f) accept correct (terms h 0)
      rw [terms_count, terms_score, terms_score] at eq
      have path : route (value f) h = scanFrom (value f) 0 h :=
        scan_fold (value f) h 0 _ List.length_range
      have cnt : score ((terms h 0).map row) f = ((terms h 0).filter accept).length := by
        change (List.filter _ (List.map _ _)).length = _
        simp only [List.filter_map, List.length_map, accept, Function.comp_def]
      rw [cnt]
      change _ = _ + (if value f (route (value f) h) then (1 : Int) else 0)
      rw [path]
      have hp : 0 < (3 : Nat)^h := by positivity
      simp only [Bool.false_eq_true, ↓reduceIte] at eq
      split at eq <;> simp_all <;> omega
  have fixed_lower : ∀ I ⊆ vs, strong I → 2 ^ h - 1 ≤ I.card := by
    intro I sub conditional
    let unknown := (Finset.range N).filter (fun j => edgeAt N j ∉ I)
    have anti : ∀ (bt : Nat → Bool) i j, i ≤ h → j ≤ h → route bt i ∈ unknown → route bt j ∈ unknown → i = j := by
      intro bt i j hi hj freeI freeJ
      let path := fun level => edgeAt N (route bt level)
      let full := (Finset.range (h + 1)).image path
      let mask := ((Finset.range (h + 1)).filter (fun lev => lev = h ∨ bt (route bt lev) = true)).image path
      have incl : mask ⊆ full := Finset.image_subset_image (Finset.filter_subset _ _)
      have allowed : full ⊆ blocks := by
        intro edge he
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
        have depth : d ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
        have ext := (route_bounds bt d).2
        have ascend : 2 ^ (d + 1) ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        have bound : route bt d < N := by dsimp [N]; omega
        have spec := edgeAt_val N (route bt d) bound
        refine Finset.mem_filter.mpr ⟨strict_mem _ ?_, route bt d, bound, spec⟩
        change (edgeAt N (route bt d)).1.val < (edgeAt N (route bt d)).2.val
        omega
      have single := fixed_imp_chain full mask I incl (by
        obtain ⟨b, w, eval⟩ := conditional (mask ∩ I) Finset.inter_subset_right
        refine ⟨b, w, ?_⟩
        intro S subS fiber
        obtain ⟨f, ok, eq⟩ := cube S (subS.trans allowed)
        have iden := eval f ok (eq ▸ fiber)
        rw [eq] at iden
        have exactly := path_subcube h bt (edgeAt N) (fun _ _ hi hj => (edgeAt_inj hi hj).mp) S subS
          (value f) (fun node hn => by rw [bit_rule _ _ hn, eq])
        change (if value f (route (value f) h) then (1 : Int) else 0) = _ at iden
        simp only [exactly] at iden
        exact iden)
      have same := single (path i) (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))
        (path j) (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))
        (Finset.mem_filter.mp freeI).2 (Finset.mem_filter.mp freeJ).2
      exact (route_inj_height bt).injective ((edgeAt_inj (Finset.mem_range.mp (Finset.mem_filter.mp freeI).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp freeJ).1)).mp same)
    have bound : unknown.card ≤ 2 ^ h := leaf_antichain h unknown
      (fun _ mem => Finset.mem_range.mp (Finset.mem_filter.mp mem).1) anti
    let known := (Finset.range N) \ unknown
    have fitsI : known.image (edgeAt N) ⊆ I := by
      intro edge hit
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hit
      by_contra miss
      exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1, miss⟩)
    have lower := Finset.card_le_card fitsI
    have unique : Set.InjOn (edgeAt N) known := fun _ ha _ hb =>
      (edgeAt_inj (Finset.mem_range.mp (Finset.mem_sdiff.mp ha).1) (Finset.mem_range.mp (Finset.mem_sdiff.mp hb).1)).mp
    rw [Finset.card_image_iff.mpr unique] at lower
    have partition := Finset.card_sdiff_add_card_eq_card (show unknown ⊆ Finset.range N from Finset.filter_subset _ _)
    change known.card + unknown.card = (Finset.range N).card at partition
    rw [Finset.card_range] at partition
    dsimp [N] at partition
    rw [pow_succ] at partition
    omega
  refine ⟨cube, observations_upper, ?_, depth_upper, adaptive_lower, fixed_upper, fixed_lower⟩
  intro L hr
  classical
  obtain ⟨shift, invariant⟩ := hr
  let Entry := ((Fin nr → Bool) × (Fin nc → Bool)) × Bool
  let wire := fun (r : Entry) (i : Nat) => (List.ofFn r.1.1 ++ List.ofFn r.1.2).getD i false
  let baseHit := fun (r : Entry) =>
    (crown = true ∧ wire r (k + 1) = true) ∨ ∃ v : Fin k, wire r v = true ∧ wire r (nr + v) = true
  let cover := fun (r : Entry) (node : Nat) => (∀ v ∈ ends (edgeAt N node), wire r v = true) ∨
    (∀ v ∈ ends (edgeAt N node), wire r (nr + v) = true)
  let support := fun (r : Entry) => (Finset.range N).filter (cover r)
  let correctHit := fun (r : Entry) => !crown = r.2
  let gain := fun (r : Entry) => if baseHit r then (0 : Int) else if correctHit r then -1 else 1
  let bias := fun (r : Entry) => if correctHit r then (1 : Int) else 0
  let data := L.map (fun r => (support r, -(gain r)))
  have hnr : k ≤ nr := by dsimp [nr]; split <;> omega
  have hnc : k ≤ nc := by dsimp [nc]; split <;> omega
  have hall := row_cost_lower h data (1 + shift - (L.map bias).sum) (by
    intro missing inc
    let nodes := Finset.range N \ missing
    let S := nodes.image (edgeAt N)
    let matching := S.image ends
    have form (edge) (mem : edge ∈ S) :
        ∃ j : Nat, edge.1.val = 2*j ∧ edge.2.val = 2*j+1 := by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp mem
      exact ⟨j, edgeAt_val N j (Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1)⟩
    have good := block_matching S form
    obtain ⟨circ, small, represent, law⟩ := exists_observations k (by dsimp [k]; omega) crown matching good
    let f : Fn := fun x y => circ.eval (List.ofFn x ++ List.ofFn y)
    have edges : probe f = S := by
      ext edge
      change edge ∈ vs.filter _ ↔ edge ∈ S
      rw [Finset.mem_filter]
      have sorted (hx : edge ∈ vs) : edge.1 < edge.2 := by
        rcases edge with ⟨u,v⟩; simpa [vs, pairs, List.mem_flatMap, List.mem_map] using hx
      have ord (e) (hm : e ∈ S) : e.1 < e.2 := by
        obtain ⟨j, left, right⟩ := form e hm
        change e.1.val < e.2.val
        omega
      have test := probe_as_matching hnr hnc crown (fun eq => by simp [nr, eq]) matching good f law edge
      constructor
      · rintro ⟨hv, hit⟩
        obtain ⟨e, he, eq⟩ := Finset.mem_image.mp ((test (sorted hv)).mp hit)
        exact ends_injective e edge (ord e he) (sorted hv) eq ▸ he
      · intro he
        exact ⟨strict_mem _ (ord _ he), (test (ord _ he)).mpr (Finset.mem_image_of_mem _ he)⟩
    have fitsF : fits f := by
      refine ⟨⟨circ, small, represent, fun _ _ => rfl⟩, ?_⟩
      rw [edges]
      intro e he
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
      have bound := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
      have ep := edgeAt_val N j bound
      exact Finset.mem_filter.mpr ⟨strict_mem _ (show (edgeAt N j).1.val < _ by omega), j, bound, ep⟩
    have bits (j : Nat) (bound : j < N) : value f j = decide (j ∉ missing) := by
      rw [bit_rule _ _ bound, edges]
      apply decide_eq_decide.mpr
      constructor
      · intro he
        obtain ⟨i, hi, eq⟩ := Finset.mem_image.mp he
        obtain ⟨hi', no⟩ := Finset.mem_sdiff.mp hi
        exact (edgeAt_inj (Finset.mem_range.mp hi') bound).mp eq ▸ no
      · intro no
        exact Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr bound, no⟩)
    let abstractBits := fun j => decide (j ∉ missing)
    have routeEq : route (value f) h = route abstractBits h := by
      apply route_congr
      intro j bound
      apply bits
      dsimp [N]; rw [pow_succ]; omega
    have output : target f = if abstractBits (scanFrom abstractBits 0 h) then 1 else 0 := by
      change (if value f (route (value f) h) then (1 : Int) else 0) = _
      rw [routeEq, bits _ (leaf_bound _)]
      rw [show route abstractBits h = scanFrom abstractBits 0 h from scan_fold _ _ _ _ List.length_range]
    have rlaw (r : Entry) : f r.1.1 r.1.2 = !crown ↔ baseHit r ∨ ¬support r ⊆ missing := by
      change circ.eval _ = !crown ↔ _
      rw [law]
      change (_ ∨ ((∃ v ∈ (Finset.univ : Finset (Fin k)), wire r v = true ∧ wire r (nr + v) = true) ∨
        ∃ e ∈ matching, (∀ v ∈ e, wire r v = true) ∨ (∀ v ∈ e, wire r (nr + v) = true))) ↔ _
      have eq : (∃ e ∈ matching, (∀ v ∈ e, wire r v = true) ∨ (∀ v ∈ e, wire r (nr + v) = true)) ↔ ¬support r ⊆ missing := by
        constructor
        · rintro ⟨e, he, covered⟩ sub
          obtain ⟨edge, hEdge, rfl⟩ := Finset.mem_image.mp he
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hEdge
          obtain ⟨inside, outside⟩ := Finset.mem_sdiff.mp hj
          exact outside (sub (Finset.mem_filter.mpr ⟨inside, covered⟩))
        · intro no
          obtain ⟨j, hj, absent⟩ := Finset.not_subset.mp no
          obtain ⟨inside, cv⟩ := Finset.mem_filter.mp hj
          exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨inside, absent⟩)), cv⟩
      rw [eq]
      simp [baseHit, or_assoc, wire]
    have single (r : Entry) : (if f r.1.1 r.1.2 = r.2 then (1 : Int) else 0) =
        bias r + (if support r ⊆ missing then gain r else 0) := by
      have logic := rlaw r
      have two : f r.1.1 r.1.2 = r.2 ↔ ((f r.1.1 r.1.2 = !crown) ↔ correctHit r) := by
        generalize f r.1.1 r.1.2 = answer
        unfold correctHit
        cases answer <;> cases crown <;> cases r.2 <;> decide
      have scoreLaw : (f r.1.1 r.1.2 = r.2) ↔ ((baseHit r ∨ ¬support r ⊆ missing) ↔ correctHit r) :=
        two.trans (iff_congr logic Iff.rfl)
      by_cases base : baseHit r <;> by_cases miss : support r ⊆ missing <;> by_cases c : correctHit r <;>
        simp [scoreLaw, bias, gain, base, miss, c]
    have total (list : Rows) : (score list f : Int) =
        (list.map bias).sum - evaluateRows (list.map (fun r => (support r, -gain r))) missing := by
      induction list with
      | nil => simp [score, evaluateRows]
      | cons r rs ih =>
        have e := single r
        unfold evaluateRows at ih ⊢
        dsimp [score] at ih ⊢
        by_cases hit : f r.1.1 r.1.2 = r.2 <;> by_cases miss : support r ⊆ missing <;>
          simp only [List.filter_cons, List.map_cons, List.sum_cons, hit, miss, decide_true, decide_false,
            Bool.false_eq_true, ↓reduceIte, List.length_cons, Nat.cast_add, Nat.cast_one] at e ⊢ <;> linarith only [ih, e]
    have counts := total L
    have realizesF := invariant f fitsF
    rw [output] at realizesF
    rw [terms_score]
    change (if abstractBits (scanFrom abstractBits 0 h) then (0 : Int) else 1) = _
    change (score L f : Int) = (L.map bias).sum - evaluateRows data missing at counts
    split_ifs at * <;> omega)
  simpa only [data, List.length_map] using hall
