import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32017_aux
namespace CircuitSource

section duality

variable {α : Type} [Fintype α] [DecidableEq α]

def IsM (M : Finset (Finset α)) : Prop :=
  (∀ e ∈ M, e.card = 2) ∧ (∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g)

theorem IsM.mono {M N : Finset (Finset α)} (h : IsM M) (hs : N ⊆ M) : IsM N :=
  ⟨fun e he => h.1 e (hs he), fun e he g hg => h.2 e (hs he) g (hs hg)⟩

theorem isM_empty : IsM (∅ : Finset (Finset α)) := ⟨by simp, by simp⟩
end duality
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

end CircuitSource

namespace Gadgets

def k (N : Nat) : Nat := 8 * N + 1

def name (N : Nat) (i : Fin N) (s : Fin 8) : Fin (k N) :=
  Fin.ofNat (8 * N + 1) (8 * i.val + s.val)

def leaf (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) : Fin (k N) :=
  name N i (Fin.ofNat 8 (2 + 2 * c.val + b.toNat))

def flag (N : Nat) (i : Fin N) (c : Fin 3) : Finset (Fin (k N)) :=
  {leaf N i c false, leaf N i c true}

def orient (N : Nat) (i : Fin N) : Finset (Fin (k N)) :=
  insert (name N i 0) (Finset.univ.image (fun c : Fin 3 => leaf N i c false))

def triangle (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) : Finset (Fin (k N)) :=
  insert (name N i (if b then 1 else 0)) (flag N i c)

def nextIdx (N : Nat) (i : Fin N) : Fin N :=
  ⟨(i.val + 1) % N, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

def pad (N : Nat) (i : Fin N) (j : Fin 4) : Fin (k N) :=
  name N (nextIdx N i) (Fin.ofNat 8 j.val)

def padded (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) (j : Fin 4) : Finset (Fin (k N)) :=
  insert (pad N i j) (triangle N i c b)

def spare (N : Nat) : Fin (k N) :=
  ⟨8 * N, by unfold k; omega⟩

def hits {N : Nat} (P : Equiv.Perm (Fin (k N))) (S : Finset (Fin (k N))) : Prop :=
  ∃ u ∈ S, P u ∈ S ∧ P u ≠ u

lemma name_val (N : Nat) (i : Fin N) (s : Fin 8) :
    (name N i s).val = 8 * i.val + s.val := by
  change (8 * i.val + s.val) % (8 * N + 1) = 8 * i.val + s.val
  exact Nat.mod_eq_of_lt (by omega)

lemma name_inj {N : Nat} {i i' : Fin N} {s s' : Fin 8} :
    name N i s = name N i' s' ↔ i = i' ∧ s = s' := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [name_val, name_val] at hv
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma name_div (N : Nat) (i : Fin N) (s : Fin 8) :
    (name N i s).val / 8 = i.val := by
  rw [name_val]
  omega

lemma name_mod (N : Nat) (i : Fin N) (s : Fin 8) :
    (name N i s).val % 8 = s.val := by
  rw [name_val]
  omega

lemma name_ne_spare (N : Nat) (i : Fin N) (s : Fin 8) :
    name N i s ≠ spare N := by
  intro h
  have hv := congrArg Fin.val h
  rw [name_val] at hv
  simp only [spare] at hv
  omega

lemma eq_name_or_spare (N : Nat) (u : Fin (k N)) :
    (∃ i s, u = name N i s) ∨ u = spare N := by
  by_cases hu : u.val < 8 * N
  · left
    refine ⟨⟨u.val / 8, by omega⟩, ⟨u.val % 8, by omega⟩, Fin.ext ?_⟩
    rw [name_val]
    dsimp only
    omega
  · right
    apply Fin.ext
    have hlt := u.isLt
    unfold k at hlt
    simp only [spare]
    omega

lemma nextIdx_ne {N : Nat} (hN : 2 ≤ N) (i : Fin N) :
    nextIdx N i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [nextIdx] at hv
  by_cases h1 : i.val + 1 < N
  · rw [Nat.mod_eq_of_lt h1] at hv
    omega
  · have h2 : i.val + 1 = N := by omega
    rw [h2, Nat.mod_self] at hv
    omega

lemma leaf_val (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) :
    (leaf N i c b).val = 8 * i.val + (2 + 2 * c.val + b.toNat) := by
  unfold leaf
  rw [name_val]
  have hmod : (Fin.ofNat 8 (2 + 2 * c.val + b.toNat)).val = 2 + 2 * c.val + b.toNat := by
    change (2 + 2 * c.val + b.toNat) % 8 = 2 + 2 * c.val + b.toNat
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> exact Nat.mod_eq_of_lt (by omega)
  rw [hmod]

lemma leaf_div (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) :
    (leaf N i c b).val / 8 = i.val := by
  rw [leaf_val]
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

lemma leaf_mod (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) :
    (leaf N i c b).val % 8 = 2 + 2 * c.val + b.toNat := by
  rw [leaf_val]
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

lemma leaf_inj {N : Nat} {i i' : Fin N} {c c' : Fin 3} {b b' : Bool} :
    leaf N i c b = leaf N i' c' b' ↔ i = i' ∧ c = c' ∧ b = b' := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [leaf_val, leaf_val] at hv
    cases b <;> cases b' <;> simp only [Bool.toNat_false, Bool.toNat_true] at hv
    · exact ⟨Fin.ext (by omega), Fin.ext (by omega), rfl⟩
    · omega
    · omega
    · exact ⟨Fin.ext (by omega), Fin.ext (by omega), rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

lemma leaf_ne_hub0 (N : Nat) (i i' : Fin N) (c : Fin 3) (b : Bool) :
    leaf N i c b ≠ name N i' 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [leaf_val, name_val] at hv
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Fin.val_zero] at hv <;> omega

lemma leaf_ne_hub1 (N : Nat) (i i' : Fin N) (c : Fin 3) (b : Bool) :
    leaf N i c b ≠ name N i' 1 := by
  intro h
  have hv := congrArg Fin.val h
  rw [leaf_val, name_val] at hv
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Fin.val_one] at hv <;> omega

lemma hub0_ne_hub1 (N : Nat) (i i' : Fin N) :
    name N i 0 ≠ name N i' 1 := by
  intro h
  have hv := congrArg Fin.val h
  rw [name_val, name_val] at hv
  simp only [Fin.val_zero, Fin.val_one] at hv
  omega

lemma pad_val (N : Nat) (i : Fin N) (j : Fin 4) :
    (pad N i j).val = 8 * (nextIdx N i).val + j.val := by
  unfold pad
  rw [name_val]
  have hmod : (Fin.ofNat 8 j.val).val = j.val := by
    change j.val % 8 = j.val
    exact Nat.mod_eq_of_lt (by omega)
  rw [hmod]

lemma pad_div (N : Nat) (i : Fin N) (j : Fin 4) :
    (pad N i j).val / 8 = (nextIdx N i).val := by
  rw [pad_val]
  omega

lemma pad_inj {N : Nat} {i : Fin N} {j j' : Fin 4} :
    pad N i j = pad N i j' ↔ j = j' := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [pad_val, pad_val] at hv
    exact Fin.ext (by omega)
  · rintro rfl
    rfl

lemma flag_card (N : Nat) (i : Fin N) (c : Fin 3) :
    (flag N i c).card = 2 := by
  unfold flag
  rw [Finset.card_pair]
  intro h
  have := (leaf_inj.mp h).2.2
  cases this

lemma triangle_card (N : Nat) (i : Fin N) (c : Fin 3) (b : Bool) :
    (triangle N i c b).card = 3 := by
  unfold triangle
  rw [Finset.card_insert_of_notMem, flag_card]
  intro hm
  simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hm
  cases b
  · rcases hm with h | h
    · exact leaf_ne_hub0 N i i c false h.symm
    · exact leaf_ne_hub0 N i i c true h.symm
  · rcases hm with h | h
    · exact leaf_ne_hub1 N i i c false h.symm
    · exact leaf_ne_hub1 N i i c true h.symm

lemma orient_card (N : Nat) (i : Fin N) :
    (orient N i).card = 4 := by
  unfold orient
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective]
    · simp
    · intro c1 c2 h
      exact (leaf_inj.mp h).2.1
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨c, _, hc⟩
    exact leaf_ne_hub0 N i i c false hc

lemma pad_notMem_triangle {N : Nat} (hN : 2 ≤ N) (i : Fin N) (c : Fin 3) (b : Bool) (j : Fin 4) :
    pad N i j ∉ triangle N i c b := by
  intro hm
  have hne : nextIdx N i ≠ i := nextIdx_ne hN i
  simp only [triangle, flag, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h
  · have := congrArg (fun u : Fin (k N) => u.val / 8) h
    rw [pad_div, name_div] at this
    exact hne (Fin.ext this)
  · have := congrArg (fun u : Fin (k N) => u.val / 8) h
    rw [pad_div, leaf_div] at this
    exact hne (Fin.ext this)
  · have := congrArg (fun u : Fin (k N) => u.val / 8) h
    rw [pad_div, leaf_div] at this
    exact hne (Fin.ext this)

lemma padded_card {N : Nat} (hN : 2 ≤ N) (i : Fin N) (c : Fin 3) (b : Bool) (j : Fin 4) :
    (padded N i c b j).card = 4 := by
  unfold padded
  rw [Finset.card_insert_of_notMem (pad_notMem_triangle hN i c b j), triangle_card]

lemma flag_disjoint {N : Nat} {i1 i2 : Fin N} (h : i1 ≠ i2) (c1 c2 : Fin 3) :
    Disjoint (flag N i1 c1) (flag N i2 c2) := by
  rw [Finset.disjoint_left]
  intro u hu1 hu2
  simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu1 hu2
  rcases hu1 with rfl | rfl <;> rcases hu2 with h2 | h2
  · exact h (leaf_inj.mp h2).1
  · exact h (leaf_inj.mp h2).1
  · exact h (leaf_inj.mp h2).1
  · exact h (leaf_inj.mp h2).1

lemma forb_card {N : Nat} {i1 i2 : Fin N} (h : i1 ≠ i2) (c1 c2 : Fin 3) :
    (flag N i1 c1 ∪ flag N i2 c2).card = 4 := by
  rw [Finset.card_union_of_disjoint (flag_disjoint h c1 c2), flag_card, flag_card]

def blockFilter (N : Nat) (S : Finset (Fin (k N))) (r : Fin N) : Finset (Fin (k N)) :=
  S.filter (fun u => u.val / 8 = r.val)

lemma blockFilter_orient (N : Nat) (i r : Fin N) :
    (blockFilter N (orient N i) r).card = if r = i then 4 else 0 := by
  unfold blockFilter
  by_cases h : r = i
  · subst h
    have heq : (orient N r).filter (fun u => u.val / 8 = r.val) = orient N r := by
      rw [Finset.filter_eq_self]
      intro u hu
      simp only [orient, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hu
      rcases hu with rfl | ⟨c, rfl⟩
      · exact name_div N r 0
      · exact leaf_div N r c false
    rw [if_pos rfl, heq, orient_card]
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u hu
    simp only [orient, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hu
    rcases hu with rfl | ⟨c, rfl⟩
    · rw [name_div]; intro heq; exact h (Fin.ext heq.symm)
    · rw [leaf_div]; intro heq; exact h (Fin.ext heq.symm)

lemma blockFilter_padded {N : Nat} (hN : 2 ≤ N) (i r : Fin N) (c : Fin 3) (b : Bool) (j : Fin 4) :
    (blockFilter N (padded N i c b j) r).card =
      if r = i then 3 else if r = nextIdx N i then 1 else 0 := by
  unfold blockFilter
  have hne : nextIdx N i ≠ i := nextIdx_ne hN i
  by_cases h1 : r = i
  · subst h1
    have heq : (padded N r c b j).filter (fun u => u.val / 8 = r.val) = triangle N r c b := by
      ext u
      simp only [padded, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | ht, hdiv⟩
        · rw [pad_div] at hdiv
          exact absurd (Fin.ext hdiv) hne
        · exact ht
      · intro ht
        refine ⟨Or.inr ht, ?_⟩
        simp only [triangle, flag, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact name_div N r _
        · exact leaf_div N r c false
        · exact leaf_div N r c true
    rw [if_pos rfl, heq, triangle_card]
  · rw [if_neg h1]
    by_cases h2 : r = nextIdx N i
    · subst h2
      have heq : (padded N i c b j).filter (fun u => u.val / 8 = (nextIdx N i).val) = {pad N i j} := by
        ext u
        simp only [padded, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | ht, hdiv⟩
          · rfl
          · simp only [triangle, flag, Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl | rfl
            · rw [name_div] at hdiv; exact absurd (Fin.ext hdiv.symm) hne
            · rw [leaf_div] at hdiv; exact absurd (Fin.ext hdiv.symm) hne
            · rw [leaf_div] at hdiv; exact absurd (Fin.ext hdiv.symm) hne
        · rintro rfl
          exact ⟨Or.inl rfl, pad_div N i j⟩
      rw [if_pos rfl, heq, Finset.card_singleton]
    · rw [if_neg h2, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u hu
      simp only [padded, triangle, flag, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · rw [pad_div]; intro heq; exact h2 (Fin.ext heq.symm)
      · rw [name_div]; intro heq; exact h1 (Fin.ext heq.symm)
      · rw [leaf_div]; intro heq; exact h1 (Fin.ext heq.symm)
      · rw [leaf_div]; intro heq; exact h1 (Fin.ext heq.symm)

lemma blockFilter_forb {N : Nat} {i1 i2 : Fin N} (h12 : i1 ≠ i2) (c1 c2 : Fin 3) (r : Fin N) :
    (blockFilter N (flag N i1 c1 ∪ flag N i2 c2) r).card =
      if r = i1 then 2 else if r = i2 then 2 else 0 := by
  unfold blockFilter
  by_cases h1 : r = i1
  · subst h1
    have heq : (flag N r c1 ∪ flag N i2 c2).filter (fun u => u.val / 8 = r.val) = flag N r c1 := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hu | hu, hdiv⟩
        · exact hu
        · simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl <;> rw [leaf_div] at hdiv <;> exact absurd (Fin.ext hdiv.symm) h12
      · intro hu
        refine ⟨Or.inl hu, ?_⟩
        simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> exact leaf_div N r c1 _
    rw [if_pos rfl, heq, flag_card]
  · rw [if_neg h1]
    by_cases h2 : r = i2
    · subst h2
      have heq : (flag N i1 c1 ∪ flag N r c2).filter (fun u => u.val / 8 = r.val) = flag N r c2 := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hu | hu, hdiv⟩
          · simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl <;> rw [leaf_div] at hdiv <;> exact absurd (Fin.ext hdiv) h12
          · exact hu
        · intro hu
          refine ⟨Or.inr hu, ?_⟩
          simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl <;> exact leaf_div N r c2 _
      rw [if_pos rfl, heq, flag_card]
    · rw [if_neg h2, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u hu
      simp only [Finset.mem_union, flag, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with (rfl | rfl) | (rfl | rfl)
      · rw [leaf_div]; intro heq; exact h1 (Fin.ext heq.symm)
      · rw [leaf_div]; intro heq; exact h1 (Fin.ext heq.symm)
      · rw [leaf_div]; intro heq; exact h2 (Fin.ext heq.symm)
      · rw [leaf_div]; intro heq; exact h2 (Fin.ext heq.symm)

lemma orient_inj {N : Nat} {i i' : Fin N} (h : orient N i = orient N i') : i = i' := by
  have hc := congrArg (fun S => (blockFilter N S i).card) h
  rw [blockFilter_orient, blockFilter_orient, if_pos rfl] at hc
  by_contra hne
  rw [if_neg hne] at hc
  omega

lemma padded_inj {N : Nat} (hN : 2 ≤ N) {i i' : Fin N} {c c' : Fin 3} {b b' : Bool} {j j' : Fin 4}
    (h : padded N i c b j = padded N i' c' b' j') :
    i = i' ∧ c = c' ∧ b = b' ∧ j = j' := by
  have hi : i = i' := by
    have hc := congrArg (fun S => (blockFilter N S i).card) h
    rw [blockFilter_padded hN, blockFilter_padded hN, if_pos rfl] at hc
    by_contra hne
    rw [if_neg hne] at hc
    split_ifs at hc <;> omega
  subst hi
  have hj : j = j' := by
    have hmem : pad N i j ∈ padded N i c' b' j' := by
      rw [← h]
      exact Finset.mem_insert_self _ _
    simp only [padded, Finset.mem_insert] at hmem
    rcases hmem with hpad | htri
    · exact pad_inj.mp hpad
    · exact absurd htri (pad_notMem_triangle hN i c' b' j)
  subst hj
  have hb : b = b' := by
    have hmem : name N i (if b then 1 else 0) ∈ padded N i c' b' j := by
      rw [← h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    simp only [padded, triangle, flag, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h2 | h3 | h4
    · have := congrArg (fun u : Fin (k N) => u.val / 8) h1
      rw [name_div, pad_div] at this
      exact absurd (Fin.ext this.symm) (nextIdx_ne hN i)
    · cases b <;> cases b'
      · rfl
      · exact absurd h2 (hub0_ne_hub1 N i i)
      · exact absurd h2.symm (hub0_ne_hub1 N i i)
      · rfl
    · cases b
      · exact absurd h3.symm (leaf_ne_hub0 N i i c' false)
      · exact absurd h3.symm (leaf_ne_hub1 N i i c' false)
    · cases b
      · exact absurd h4.symm (leaf_ne_hub0 N i i c' true)
      · exact absurd h4.symm (leaf_ne_hub1 N i i c' true)
  subst hb
  have hc : c = c' := by
    have hmem : leaf N i c false ∈ padded N i c' b j := by
      rw [← h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    simp only [padded, triangle, flag, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h2 | h3 | h4
    · have := congrArg (fun u : Fin (k N) => u.val / 8) h1
      rw [leaf_div, pad_div] at this
      exact absurd (Fin.ext this.symm) (nextIdx_ne hN i)
    · cases b
      · exact absurd h2 (leaf_ne_hub0 N i i c false)
      · exact absurd h2 (leaf_ne_hub1 N i i c false)
    · exact (leaf_inj.mp h3).2.1
    · exact (leaf_inj.mp h4).2.1
  exact ⟨rfl, hc, rfl, rfl⟩

lemma forb_inj {N : Nat} {e1 e2 : (Fin N × Fin 3) × (Fin N × Fin 3)}
    (he1 : e1.1.1 < e1.2.1) (he2 : e2.1.1 < e2.2.1)
    (h : flag N e1.1.1 e1.1.2 ∪ flag N e1.2.1 e1.2.2 =
         flag N e2.1.1 e2.1.2 ∪ flag N e2.2.1 e2.2.2) :
    e1 = e2 := by
  have h12 : e1.1.1 ≠ e1.2.1 := ne_of_lt he1
  have h22 : e2.1.1 ≠ e2.2.1 := ne_of_lt he2
  have hmem1 : e1.1.1 = e2.1.1 ∨ e1.1.1 = e2.2.1 := by
    by_cases ha : e1.1.1 = e2.1.1
    · exact Or.inl ha
    · by_cases hb : e1.1.1 = e2.2.1
      · exact Or.inr hb
      · exfalso
        have hc := congrArg (fun S => (blockFilter N S e1.1.1).card) h
        rw [blockFilter_forb h12, blockFilter_forb h22] at hc
        simp [ha, hb] at hc
  have hmem2 : e1.2.1 = e2.1.1 ∨ e1.2.1 = e2.2.1 := by
    by_cases ha : e1.2.1 = e2.1.1
    · exact Or.inl ha
    · by_cases hb : e1.2.1 = e2.2.1
      · exact Or.inr hb
      · exfalso
        have hc := congrArg (fun S => (blockFilter N S e1.2.1).card) h
        rw [blockFilter_forb h12, blockFilter_forb h22] at hc
        simp [h12.symm, ha, hb] at hc
  have hi1 : e1.1.1 = e2.1.1 := by
    rcases hmem1 with h1 | h1 <;> rcases hmem2 with h2 | h2
    · exact h1
    · exact h1
    · exfalso
      have : e1.1.1 < e1.2.1 := he1
      rw [h1, h2] at this
      exact absurd (lt_trans this he2) (lt_irrefl _)
    · exfalso; exact h12 (h1.trans h2.symm)
  have hi2 : e1.2.1 = e2.2.1 := by
    rcases hmem2 with h2 | h2
    · exfalso; exact h12 (hi1.trans h2.symm)
    · exact h2
  have hc1 : e1.1.2 = e2.1.2 := by
    have hm : leaf N e1.1.1 e1.1.2 false ∈ flag N e2.1.1 e2.1.2 ∪ flag N e2.2.1 e2.2.2 := by
      rw [← h]
      exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    simp only [Finset.mem_union, flag, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with (h3 | h3) | (h3 | h3)
    · exact (leaf_inj.mp h3).2.1
    · exact (leaf_inj.mp h3).2.1
    · exact absurd ((leaf_inj.mp h3).1.symm.trans hi1) h22.symm
    · exact absurd ((leaf_inj.mp h3).1.symm.trans hi1) h22.symm
  have hc2 : e1.2.2 = e2.2.2 := by
    have hm : leaf N e1.2.1 e1.2.2 false ∈ flag N e2.1.1 e2.1.2 ∪ flag N e2.2.1 e2.2.2 := by
      rw [← h]
      exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    simp only [Finset.mem_union, flag, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with (h3 | h3) | (h3 | h3)
    · exact absurd ((leaf_inj.mp h3).1.symm.trans hi2) h22
    · exact absurd ((leaf_inj.mp h3).1.symm.trans hi2) h22
    · exact (leaf_inj.mp h3).2.1
    · exact (leaf_inj.mp h3).2.1
  rcases e1 with ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩
  rcases e2 with ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩
  simp only at hi1 hi2 hc1 hc2
  subst hi1; subst hi2; subst hc1; subst hc2
  rfl

lemma orient_ne_padded {N : Nat} (hN : 2 ≤ N) (i i' : Fin N) (c : Fin 3) (b : Bool) (j : Fin 4) :
    orient N i ≠ padded N i' c b j := by
  intro h
  have hc := congrArg (fun S => (blockFilter N S i).card) h
  rw [blockFilter_orient, blockFilter_padded hN, if_pos rfl] at hc
  split_ifs at hc <;> omega

lemma orient_ne_forb {N : Nat} {i1 i2 : Fin N} (h12 : i1 ≠ i2) (i : Fin N) (c1 c2 : Fin 3) :
    orient N i ≠ flag N i1 c1 ∪ flag N i2 c2 := by
  intro h
  have hc := congrArg (fun S => (blockFilter N S i).card) h
  rw [blockFilter_orient, blockFilter_forb h12, if_pos rfl] at hc
  split_ifs at hc <;> omega

lemma padded_ne_forb {N : Nat} (hN : 2 ≤ N) {i1 i2 : Fin N} (h12 : i1 ≠ i2)
    (i : Fin N) (c : Fin 3) (b : Bool) (j : Fin 4) (c1 c2 : Fin 3) :
    padded N i c b j ≠ flag N i1 c1 ∪ flag N i2 c2 := by
  intro h
  have hc := congrArg (fun S => (blockFilter N S i).card) h
  rw [blockFilter_padded hN, blockFilter_forb h12, if_pos rfl] at hc
  split_ifs at hc <;> omega

def blockSwap (c : Fin 3) (s : Fin 8) : Fin 8 :=
  if s.val = 0 then Fin.ofNat 8 (2 + 2 * c.val)
  else if s.val = 1 then Fin.ofNat 8 (3 + 2 * c.val)
  else if s.val = 2 + 2 * c.val then 0
  else if s.val = 3 + 2 * c.val then 1
  else if s.val % 2 = 0 then Fin.ofNat 8 (s.val + 1)
  else Fin.ofNat 8 (s.val - 1)

lemma blockSwap_invol : ∀ (c : Fin 3) (s : Fin 8), blockSwap c (blockSwap c s) = s := by
  decide

lemma blockSwap_zero : ∀ c : Fin 3, blockSwap c 0 = Fin.ofNat 8 (2 + 2 * c.val) := by
  decide

lemma blockSwap_one : ∀ c : Fin 3, blockSwap c 1 = Fin.ofNat 8 (3 + 2 * c.val) := by
  decide

lemma blockSwap_leaf_eq :
    ∀ (c : Fin 3) (b : Bool),
      blockSwap c (Fin.ofNat 8 (2 + 2 * c.val + b.toNat)) = if b then 1 else 0 := by
  decide

lemma blockSwap_leaf_ne :
    ∀ (c c' : Fin 3) (b : Bool), c ≠ c' →
      blockSwap c (Fin.ofNat 8 (2 + 2 * c'.val + b.toNat)) =
        Fin.ofNat 8 (2 + 2 * c'.val + (!b).toNat) := by
  decide

lemma blockSwap_diff_card :
    ∀ (c1 c2 : Fin 3), c1 ≠ c2 →
      (Finset.univ.filter (fun s : Fin 8 => blockSwap c1 s ≠ blockSwap c2 s)).card = 6 := by
  decide

def permFun (N : Nat) (a : Fin N → Fin 3) (u : Fin (k N)) : Fin (k N) :=
  if hu : u.val < 8 * N then
    name N ⟨u.val / 8, by omega⟩ (blockSwap (a ⟨u.val / 8, by omega⟩) ⟨u.val % 8, by omega⟩)
  else
    u

lemma permFun_name (N : Nat) (a : Fin N → Fin 3) (i : Fin N) (s : Fin 8) :
    permFun N a (name N i s) = name N i (blockSwap (a i) s) := by
  unfold permFun
  have hlt : (name N i s).val < 8 * N := by rw [name_val]; omega
  rw [dif_pos hlt]
  have hi : (⟨(name N i s).val / 8, by omega⟩ : Fin N) = i := Fin.ext (name_div N i s)
  have hs : (⟨(name N i s).val % 8, by omega⟩ : Fin 8) = s := Fin.ext (name_mod N i s)
  rw [hi, hs]

lemma permFun_spare (N : Nat) (a : Fin N → Fin 3) :
    permFun N a (spare N) = spare N := by
  unfold permFun
  have hnot : ¬ (spare N).val < 8 * N := by simp [spare]
  rw [dif_neg hnot]

lemma permFun_invol (N : Nat) (a : Fin N → Fin 3) :
    Function.Involutive (permFun N a) := by
  intro u
  rcases eq_name_or_spare N u with ⟨i, s, rfl⟩ | rfl
  · rw [permFun_name, permFun_name, blockSwap_invol]
  · rw [permFun_spare, permFun_spare]

def permOf (N : Nat) (a : Fin N → Fin 3) : Equiv.Perm (Fin (k N)) :=
  ⟨permFun N a, permFun N a, permFun_invol N a, permFun_invol N a⟩

lemma permOf_name (N : Nat) (a : Fin N → Fin 3) (i : Fin N) (s : Fin 8) :
    permOf N a (name N i s) = name N i (blockSwap (a i) s) :=
  permFun_name N a i s

lemma permOf_spare (N : Nat) (a : Fin N → Fin 3) :
    permOf N a (spare N) = spare N :=
  permFun_spare N a

lemma permOf_invol (N : Nat) (a : Fin N → Fin 3) :
    Function.Involutive (permOf N a) :=
  permFun_invol N a

lemma permOf_leaf_eq (N : Nat) (a : Fin N → Fin 3) (i : Fin N) (b : Bool) :
    permOf N a (leaf N i (a i) b) = name N i (if b then 1 else 0) := by
  unfold leaf
  rw [permOf_name, blockSwap_leaf_eq]

lemma permOf_leaf_ne (N : Nat) (a : Fin N → Fin 3) (i : Fin N) (c : Fin 3) (b : Bool)
    (h : a i ≠ c) :
    permOf N a (leaf N i c b) = leaf N i c (!b) := by
  unfold leaf
  rw [permOf_name, blockSwap_leaf_ne (a i) c b h]

lemma permOf_hits_flag_iff (N : Nat) (a : Fin N → Fin 3) (i : Fin N) (c : Fin 3) :
    (¬ hits (permOf N a) (flag N i c)) ↔ a i = c := by
  constructor
  · intro hnh
    by_contra hne
    apply hnh
    refine ⟨leaf N i c false, Finset.mem_insert_self _ _, ?_, ?_⟩
    · rw [permOf_leaf_ne N a i c false hne]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rw [permOf_leaf_ne N a i c false hne]
      intro h
      have := (leaf_inj.mp h).2.2
      cases this
  · intro heq
    subst heq
    rintro ⟨u, hu, hpu, _⟩
    simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu hpu
    rcases hu with rfl | rfl
    · rw [permOf_leaf_eq N a i false] at hpu
      simp only [Bool.false_eq_true, ite_false] at hpu
      rcases hpu with h | h
      · exact leaf_ne_hub0 N i i (a i) false h.symm
      · exact leaf_ne_hub0 N i i (a i) true h.symm
    · rw [permOf_leaf_eq N a i true] at hpu
      simp only [ite_true] at hpu
      rcases hpu with h | h
      · exact leaf_ne_hub1 N i i (a i) false h.symm
      · exact leaf_ne_hub1 N i i (a i) true h.symm

lemma permOf_hits_orient (N : Nat) (a : Fin N → Fin 3) (i : Fin N) :
    hits (permOf N a) (orient N i) := by
  refine ⟨name N i 0, Finset.mem_insert_self _ _, ?_, ?_⟩
  · rw [permOf_name, blockSwap_zero]
    have hlf : name N i (Fin.ofNat 8 (2 + 2 * (a i).val)) = leaf N i (a i) false := rfl
    rw [hlf]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a i, Finset.mem_univ _, rfl⟩)
  · rw [permOf_name, blockSwap_zero]
    have hlf : name N i (Fin.ofNat 8 (2 + 2 * (a i).val)) = leaf N i (a i) false := rfl
    rw [hlf]
    exact leaf_ne_hub0 N i i (a i) false

lemma permOf_hits_triangle (N : Nat) (a : Fin N → Fin 3) (i : Fin N) (c : Fin 3) (b : Bool) :
    hits (permOf N a) (triangle N i c b) := by
  by_cases hc : a i = c
  · subst hc
    refine ⟨leaf N i (a i) b, ?_, ?_, ?_⟩
    · cases b
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · rw [permOf_leaf_eq]
      exact Finset.mem_insert_self _ _
    · rw [permOf_leaf_eq]
      cases b
      · exact (leaf_ne_hub0 N i i (a i) false).symm
      · exact (leaf_ne_hub1 N i i (a i) true).symm
  · refine ⟨leaf N i c false, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_, ?_⟩
    · rw [permOf_leaf_ne N a i c false hc]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · rw [permOf_leaf_ne N a i c false hc]
      intro h
      have := (leaf_inj.mp h).2.2
      cases this

lemma permOf_dist (N : Nat) (a b : Fin N → Fin 3) :
    (Finset.univ.filter (fun u : Fin (k N) => permOf N a u ≠ permOf N b u)).card =
      6 * (Finset.univ.filter (fun i : Fin N => a i ≠ b i)).card := by
  let D := Finset.univ.filter (fun i : Fin N => a i ≠ b i)
  let F : Fin N → Finset (Fin (k N)) := fun i =>
    (Finset.univ.filter (fun s : Fin 8 => blockSwap (a i) s ≠ blockSwap (b i) s)).image (name N i)
  have heq : Finset.univ.filter (fun u : Fin (k N) => permOf N a u ≠ permOf N b u) = D.biUnion F := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, D, F, Finset.mem_image]
    constructor
    · intro hne
      rcases eq_name_or_spare N u with ⟨i, s, rfl⟩ | rfl
      · rw [permOf_name, permOf_name] at hne
        have hsne : blockSwap (a i) s ≠ blockSwap (b i) s := fun h => hne (by rw [h])
        have hine : a i ≠ b i := fun h => hsne (by rw [h])
        exact ⟨i, hine, s, hsne, rfl⟩
      · rw [permOf_spare, permOf_spare] at hne
        exact absurd rfl hne
    · rintro ⟨i, _, s, hsne, rfl⟩
      rw [permOf_name, permOf_name]
      intro h
      exact hsne (name_inj.mp h).2
  rw [heq, Finset.card_biUnion]
  · have hcard : ∀ i ∈ D, (F i).card = 6 := by
      intro i hi
      have hine : a i ≠ b i := (Finset.mem_filter.mp hi).2
      dsimp only [F]
      rw [Finset.card_image_of_injective _ (fun s1 s2 h => (name_inj.mp h).2)]
      exact blockSwap_diff_card (a i) (b i) hine
    rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]
  · intro i1 _ i2 _ hne
    show Disjoint (F i1) (F i2)
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    rcases Finset.mem_image.mp hu1 with ⟨s1, _, rfl⟩
    rcases Finset.mem_image.mp hu2 with ⟨s2, _, h2⟩
    exact hne (name_inj.mp h2).1.symm

lemma hits_triangle_of_padded {N : Nat} (P : Equiv.Perm (Fin (k N)))
    (hinv : Function.Involutive P)
    (i : Fin N) (c : Fin 3) (b : Bool)
    (hpad : ∀ j : Fin 4, hits P (padded N i c b j)) :
    hits P (triangle N i c b) := by
  by_contra hnt
  have hsub : Finset.univ.image (fun j : Fin 4 => P (pad N i j)) ⊆ triangle N i c b := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨j, _, rfl⟩
    rcases hpad j with ⟨u, hu, hpu, hne⟩
    simp only [padded, Finset.mem_insert] at hu hpu
    rcases hu with rfl | hut
    · rcases hpu with hp | hpt
      · exact absurd hp hne
      · exact hpt
    · rcases hpu with hp | hpt
      · have hpu' : P (pad N i j) = u := by rw [← hp, hinv u]
        rw [hpu']
        exact hut
      · exact absurd ⟨u, hut, hpt, hne⟩ hnt
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin, triangle_card] at hle
  · omega
  · intro j1 j2 hj
    exact pad_inj.mp (P.injective hj)

lemma hits_flag_eq_swap {N : Nat} (P : Equiv.Perm (Fin (k N))) (hinv : Function.Involutive P)
    (i : Fin N) (c : Fin 3) (hh : hits P (flag N i c)) :
    P (leaf N i c false) = leaf N i c true ∧ P (leaf N i c true) = leaf N i c false := by
  rcases hh with ⟨u, hu, hpu, hne⟩
  simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hu hpu
  rcases hu with rfl | rfl <;> rcases hpu with hp | hp
  · exact absurd hp hne
  · exact ⟨hp, by rw [← hp, hinv]⟩
  · exact ⟨by rw [← hp, hinv], hp⟩
  · exact absurd hp hne

lemma hub_maps_into_flag {N : Nat} (P : Equiv.Perm (Fin (k N))) (hinv : Function.Involutive P)
    (i : Fin N) (c : Fin 3) (b : Bool)
    (htri : hits P (triangle N i c b)) (hnh : ¬ hits P (flag N i c)) :
    P (name N i (if b then 1 else 0)) ∈ flag N i c := by
  rcases htri with ⟨u, hu, hpu, hne⟩
  simp only [triangle, Finset.mem_insert] at hu hpu
  rcases hu with rfl | huf
  · rcases hpu with hp | hpf
    · exact absurd hp hne
    · exact hpf
  · rcases hpu with hp | hpf
    · have : P (name N i (if b then 1 else 0)) = u := by rw [← hp, hinv]
      rw [this]
      exact huf
    · exact absurd ⟨u, huf, hpf, hne⟩ hnh

lemma exists_unique_unhit_flag {N : Nat} (P : Equiv.Perm (Fin (k N))) (hinv : Function.Involutive P)
    (i : Fin N)
    (hori : hits P (orient N i))
    (htri : ∀ c b, hits P (triangle N i c b)) :
    ∃! c : Fin 3, ¬ hits P (flag N i c) := by
  have hex : ∃ c : Fin 3, ¬ hits P (flag N i c) := by
    by_contra hall
    push Not at hall
    rcases hori with ⟨u, hu, hpu, hne⟩
    simp only [orient, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hu hpu
    rcases hu with rfl | ⟨c, rfl⟩
    · rcases hpu with hp | ⟨c, hpc⟩
      · exact hne hp
      · have hsw := (hits_flag_eq_swap P hinv i c (hall c)).1
        have hback : P (leaf N i c false) = name N i 0 := by rw [hpc, hinv]
        rw [hsw] at hback
        exact leaf_ne_hub0 N i i c true hback
    · have hsw := (hits_flag_eq_swap P hinv i c (hall c)).1
      rw [hsw] at hpu
      rcases hpu with hp | ⟨c', hpc'⟩
      · exact leaf_ne_hub0 N i i c true hp
      · have := (leaf_inj.mp hpc').2.2
        cases this
  rcases hex with ⟨c0, hc0⟩
  refine ⟨c0, hc0, ?_⟩
  intro c1 hc1
  have hm0 := hub_maps_into_flag P hinv i c0 false (htri c0 false) hc0
  have hm1 := hub_maps_into_flag P hinv i c1 false (htri c1 false) hc1
  simp only [flag, Finset.mem_insert, Finset.mem_singleton] at hm0 hm1
  rcases hm0 with h0 | h0 <;> rcases hm1 with h1 | h1 <;>
    exact (leaf_inj.mp (h1.symm.trans h0)).2.1

lemma eq_permOf_of_controls {N : Nat} (P : Equiv.Perm (Fin (k N))) (hinv : Function.Involutive P)
    (a : Fin N → Fin 3)
    (hori : ∀ i, hits P (orient N i))
    (htri : ∀ i c b, hits P (triangle N i c b))
    (hunhit : ∀ i, ¬ hits P (flag N i (a i)))
    (hhit : ∀ i c, c ≠ a i → hits P (flag N i c)) :
    P = permOf N a := by
  have hblock : ∀ (i : Fin N) (s : Fin 8), P (name N i s) = permOf N a (name N i s) := by
    intro i s
    have h0 : P (name N i 0) = leaf N i (a i) false := by
      rcases hori i with ⟨u, hu, hpu, hne⟩
      simp only [orient, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hu hpu
      rcases hu with rfl | ⟨c, rfl⟩
      · rcases hpu with hp | ⟨c, hpc⟩
        · exact absurd hp hne
        · by_cases hc : c = a i
          · subst hc; exact hpc.symm
          · exfalso
            have hsw := (hits_flag_eq_swap P hinv i c (hhit i c hc)).1
            have hback : P (leaf N i c false) = name N i 0 := by rw [hpc, hinv]
            rw [hsw] at hback
            exact leaf_ne_hub0 N i i c true hback
      · by_cases hc : c = a i
        · subst hc
          rcases hpu with hp | ⟨c', hpc'⟩
          · rw [← hp, hinv]
          · exfalso
            by_cases hc' : c' = a i
            · subst hc'; exact hne hpc'.symm
            · have hsw := (hits_flag_eq_swap P hinv i c' (hhit i c' hc')).1
              have hback : P (leaf N i c' false) = leaf N i (a i) false := by rw [hpc', hinv]
              rw [hsw] at hback
              have := (leaf_inj.mp hback).2.2
              cases this
        · exfalso
          have hsw := (hits_flag_eq_swap P hinv i c (hhit i c hc)).1
          rw [hsw] at hpu
          rcases hpu with hp | ⟨c', hpc'⟩
          · exact leaf_ne_hub0 N i i c true hp
          · have := (leaf_inj.mp hpc').2.2
            cases this
    have h0_rev : P (leaf N i (a i) false) = name N i 0 := by rw [← h0, hinv]
    have h1 : P (name N i 1) = leaf N i (a i) true := by
      have hm := hub_maps_into_flag P hinv i (a i) true (htri i (a i) true) (hunhit i)
      simp only [ite_true, flag, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hp | hp
      · exfalso
        have heq : name N i 1 = name N i 0 := P.injective (hp.trans h0.symm)
        exact hub0_ne_hub1 N i i heq.symm
      · exact hp
    have h1_rev : P (leaf N i (a i) true) = name N i 1 := by rw [← h1, hinv]
    have hleaf : ∀ (c : Fin 3) (b : Bool), P (leaf N i c b) = permOf N a (leaf N i c b) := by
      intro c b
      by_cases hc : c = a i
      · subst hc
        rw [permOf_leaf_eq]
        cases b
        · exact h0_rev
        · exact h1_rev
      · rw [permOf_leaf_ne N a i c b (Ne.symm hc)]
        have hsw := hits_flag_eq_swap P hinv i c (hhit i c hc)
        cases b
        · exact hsw.1
        · exact hsw.2
    fin_cases s
    · change P (name N i 0) = permOf N a (name N i 0)
      rw [h0, permOf_name, blockSwap_zero]; rfl
    · change P (name N i 1) = permOf N a (name N i 1)
      rw [h1, permOf_name, blockSwap_one]
      apply Fin.ext
      rw [leaf_val, name_val]
      have hmod : (Fin.ofNat 8 (3 + 2 * (a i).val)).val = 3 + 2 * (a i).val := by
        change (3 + 2 * (a i).val) % 8 = 3 + 2 * (a i).val
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      simp only [Bool.toNat_true]
      omega
    · exact hleaf 0 false
    · exact hleaf 0 true
    · exact hleaf 1 false
    · exact hleaf 1 true
    · exact hleaf 2 false
    · exact hleaf 2 true
  ext u
  rcases eq_name_or_spare N u with ⟨i, s, rfl⟩ | rfl
  · exact congrArg Fin.val (hblock i s)
  · rw [permOf_spare]
    rcases eq_name_or_spare N (P (spare N)) with ⟨i, s, hsp⟩ | hsp
    · exfalso
      have hback : P (name N i s) = spare N := by rw [← hsp, hinv]
      rw [hblock i s, permOf_name] at hback
      exact name_ne_spare N i _ hback
    · exact congrArg Fin.val hsp

end Gadgets

theorem Gadgets : (∀ (N : Nat), 2 ≤ N →
  let Tag := Fin N × Fin 3
  ∀ B : Finset (Tag × Tag), (∀ e ∈ B, e.1.1 < e.2.1) →
  let k := 8*N+1
  let name := fun (i : Fin N) (s : Fin 8) => Fin.ofNat (8*N+1) (8*i.val+s.val)
  let leaf := fun (i : Fin N) (c : Fin 3) (b : Bool) =>
    name i (Fin.ofNat 8 (2+2*c.val+b.toNat))
  let flag := fun (i : Fin N) (c : Fin 3) => ({leaf i c false,leaf i c true} : Finset (Fin k))
  let orient := fun i : Fin N => insert (name i 0) (Finset.univ.image (fun c : Fin 3 => leaf i c false))
  let triangle := fun (i : Fin N) (c : Fin 3) (b : Bool) => insert (name i (if b then 1 else 0)) (flag i c)
  let pad := fun (i : Fin N) (j : Fin 4) =>
    name (⟨(i.val+1)%N,Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin N) (Fin.ofNat 8 j.val)
  let control := fun S : Finset (Fin k) =>
    (∃ i, S = orient i) ∨ (∃ i c b j, S = insert (pad i j) (triangle i c b))
  let tests := Finset.univ.filter (fun S : Finset (Fin k) =>
    control S ∨ ∃ e ∈ B, S = flag e.1.1 e.1.2 ∪ flag e.2.1 e.2.2)
  let valid := fun a : Fin N → Fin 3 => ∀ e ∈ B, a e.1.1 ≠ e.1.2 ∨ a e.2.1 ≠ e.2.2
  let hits := fun (P : Equiv.Perm (Fin k)) (S : Finset (Fin k)) =>
    ∃ u ∈ S, P u ∈ S ∧ P u ≠ u
  let Fits := {P : Equiv.Perm (Fin k) // Function.Involutive P ∧ ∀ S ∈ tests, hits P S}
  tests.card = 25*N+B.card ∧ (∀ S ∈ tests, S.card = 4) ∧
  ∃ E : {a : Fin N → Fin 3 // valid a} ≃ Fits,
    (∀ a i c, (¬ hits (E a).val (flag i c)) ↔ a.val i = c) ∧
    ∀ a b, (Finset.univ.filter (fun u : Fin k => (E a).val u ≠ (E b).val u)).card =
      6*(Finset.univ.filter (fun i : Fin N => a.val i ≠ b.val i)).card) := by
  classical
  intro N hN Tag B hB
  dsimp only
  let O : Finset (Finset (Fin (Gadgets.k N))) :=
    Finset.univ.image (Gadgets.orient N)
  let T : Finset (Finset (Fin (Gadgets.k N))) :=
    Finset.univ.image (fun p : Fin N × Fin 3 × Bool × Fin 4 =>
      Gadgets.padded N p.1 p.2.1 p.2.2.1 p.2.2.2)
  let F : Finset (Finset (Fin (Gadgets.k N))) :=
    B.image (fun e => Gadgets.flag N e.1.1 e.1.2 ∪
      Gadgets.flag N e.2.1 e.2.2)
  have htests_eq :
      Finset.univ.filter (fun S : Finset (Fin (Gadgets.k N)) =>
        ((∃ i, S = Gadgets.orient N i) ∨
          (∃ i c b j, S = Gadgets.padded N i c b j)) ∨
        ∃ e ∈ B, S = Gadgets.flag N e.1.1 e.1.2 ∪
          Gadgets.flag N e.2.1 e.2.2) = O ∪ T ∪ F := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      O, T, F, Finset.mem_image]
    constructor
    · rintro ((⟨i, rfl⟩ | ⟨i, c, b, j, rfl⟩) | ⟨e, he, rfl⟩)
      · exact Or.inl (Or.inl ⟨i, rfl⟩)
      · exact Or.inl (Or.inr ⟨(i, c, b, j), rfl⟩)
      · exact Or.inr ⟨e, he, rfl⟩
    · rintro ((⟨i, rfl⟩ | ⟨⟨i, c, b, j⟩, rfl⟩) | ⟨e, he, rfl⟩)
      · exact Or.inl (Or.inl ⟨i, rfl⟩)
      · exact Or.inl (Or.inr ⟨i, c, b, j, rfl⟩)
      · exact Or.inr ⟨e, he, rfl⟩
  have hO_card : O.card = N := by
    dsimp only [O]
    rw [Finset.card_image_of_injective _ (fun _ _ h => Gadgets.orient_inj h)]
    simp
  have hT_card : T.card = 24 * N := by
    dsimp only [T]
    rw [Finset.card_image_of_injective]
    · simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      omega
    · rintro ⟨i1, c1, b1, j1⟩ ⟨i2, c2, b2, j2⟩ h
      rcases Gadgets.padded_inj hN h with ⟨rfl, rfl, rfl, rfl⟩
      rfl
  have hF_card : F.card = B.card := by
    dsimp only [F]
    rw [Finset.card_image_of_injOn]
    intro e1 he1 e2 he2 h
    exact Gadgets.forb_inj (hB e1 he1) (hB e2 he2) h
  have hOT_disj : Disjoint O T := by
    rw [Finset.disjoint_left]
    intro S hSO hST
    rcases Finset.mem_image.mp hSO with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hST with ⟨⟨i', c, b, j⟩, _, h⟩
    exact Gadgets.orient_ne_padded hN i i' c b j h.symm
  have hOTF_disj : Disjoint (O ∪ T) F := by
    rw [Finset.disjoint_left]
    intro S hSOT hSF
    rcases Finset.mem_image.mp hSF with ⟨e, he, rfl⟩
    have hne : e.1.1 ≠ e.2.1 := ne_of_lt (hB e he)
    rcases Finset.mem_union.mp hSOT with hSO | hST
    · rcases Finset.mem_image.mp hSO with ⟨i, _, h⟩
      exact Gadgets.orient_ne_forb hne i e.1.2 e.2.2 h
    · rcases Finset.mem_image.mp hST with ⟨⟨i, c, b, j⟩, _, h⟩
      exact Gadgets.padded_ne_forb hN hne i c b j e.1.2 e.2.2 h
  refine ⟨?_, ?_, ?_⟩
  · change (Finset.univ.filter (fun S : Finset (Fin (Gadgets.k N)) =>
        ((∃ i, S = Gadgets.orient N i) ∨
          (∃ i c b j, S = Gadgets.padded N i c b j)) ∨
        ∃ e ∈ B, S = Gadgets.flag N e.1.1 e.1.2 ∪
          Gadgets.flag N e.2.1 e.2.2)).card = 25 * N + B.card
    rw [htests_eq, Finset.card_union_of_disjoint hOTF_disj,
      Finset.card_union_of_disjoint hOT_disj, hO_card, hT_card, hF_card]
    omega
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rcases hS with (⟨i, rfl⟩ | ⟨i, c, b, j, rfl⟩) | ⟨e, he, rfl⟩
    · exact Gadgets.orient_card N i
    · exact Gadgets.padded_card hN i c b j
    · exact Gadgets.forb_card (ne_of_lt (hB e he)) e.1.2 e.2.2
  · let toFits : {a : Fin N → Fin 3 // ∀ e ∈ B, a e.1.1 ≠ e.1.2 ∨ a e.2.1 ≠ e.2.2} →
        {P : Equiv.Perm (Fin (Gadgets.k N)) //
          Function.Involutive P ∧ ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin (Gadgets.k N)) =>
            ((∃ i, S = Gadgets.orient N i) ∨
              (∃ i c b j, S = Gadgets.padded N i c b j)) ∨
            ∃ e ∈ B, S = Gadgets.flag N e.1.1 e.1.2 ∪
              Gadgets.flag N e.2.1 e.2.2),
            Gadgets.hits P S} :=
      fun a => ⟨Gadgets.permOf N a.val,
        Gadgets.permOf_invol N a.val, by
          intro S hS
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
          rcases hS with (⟨i, rfl⟩ | ⟨i, c, b, j, rfl⟩) | ⟨e, he, rfl⟩
          · exact Gadgets.permOf_hits_orient N a.val i
          · rcases Gadgets.permOf_hits_triangle N a.val i c b with ⟨u, hu, hpu, hne⟩
            exact ⟨u, Finset.mem_insert_of_mem hu, Finset.mem_insert_of_mem hpu, hne⟩
          · rcases a.property e he with h1 | h2
            · have hh : Gadgets.hits (Gadgets.permOf N a.val)
                  (Gadgets.flag N e.1.1 e.1.2) := by
                by_contra hnh
                exact h1 ((Gadgets.permOf_hits_flag_iff N a.val e.1.1 e.1.2).mp hnh)
              rcases hh with ⟨u, hu, hpu, hne⟩
              exact ⟨u, Finset.mem_union_left _ hu, Finset.mem_union_left _ hpu, hne⟩
            · have hh : Gadgets.hits (Gadgets.permOf N a.val)
                  (Gadgets.flag N e.2.1 e.2.2) := by
                by_contra hnh
                exact h2 ((Gadgets.permOf_hits_flag_iff N a.val e.2.1 e.2.2).mp hnh)
              rcases hh with ⟨u, hu, hpu, hne⟩
              exact ⟨u, Finset.mem_union_right _ hu, Finset.mem_union_right _ hpu, hne⟩⟩
    have hdecode : ∀ P : {P : Equiv.Perm (Fin (Gadgets.k N)) //
          Function.Involutive P ∧ ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin (Gadgets.k N)) =>
            ((∃ i, S = Gadgets.orient N i) ∨
              (∃ i c b j, S = Gadgets.padded N i c b j)) ∨
            ∃ e ∈ B, S = Gadgets.flag N e.1.1 e.1.2 ∪
              Gadgets.flag N e.2.1 e.2.2),
            Gadgets.hits P S},
        ∃ a : {a : Fin N → Fin 3 // ∀ e ∈ B, a e.1.1 ≠ e.1.2 ∨ a e.2.1 ≠ e.2.2}, toFits a = P := by
      intro P
      have hori : ∀ i, Gadgets.hits P.val (Gadgets.orient N i) := by
        intro i
        apply P.property.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl (Or.inl ⟨i, rfl⟩)
      have htri : ∀ i c b, Gadgets.hits P.val (Gadgets.triangle N i c b) := by
        intro i c b
        apply Gadgets.hits_triangle_of_padded P.val P.property.1 i c b
        intro j
        apply P.property.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl (Or.inr ⟨i, c, b, j, rfl⟩)
      have huniq : ∀ i, ∃! c : Fin 3, ¬ Gadgets.hits P.val (Gadgets.flag N i c) :=
        fun i => Gadgets.exists_unique_unhit_flag P.val P.property.1 i (hori i) (htri i)
      let a : Fin N → Fin 3 := fun i => Classical.choose (huniq i)
      have ha_spec : ∀ i, ¬ Gadgets.hits P.val (Gadgets.flag N i (a i)) ∧
          ∀ c, ¬ Gadgets.hits P.val (Gadgets.flag N i c) → c = a i :=
        fun i => Classical.choose_spec (huniq i)
      have hhit : ∀ i c, c ≠ a i → Gadgets.hits P.val (Gadgets.flag N i c) := by
        intro i c hne
        by_contra hnh
        exact hne ((ha_spec i).2 c hnh)
      have hPeq : P.val = Gadgets.permOf N a :=
        Gadgets.eq_permOf_of_controls P.val P.property.1 a hori htri (fun i => (ha_spec i).1) hhit
      have hval : ∀ e ∈ B, a e.1.1 ≠ e.1.2 ∨ a e.2.1 ≠ e.2.2 := by
        intro e he
        by_contra hboth
        push Not at hboth
        rcases hboth with ⟨he1, he2⟩
        have hS : Gadgets.hits P.val
            (Gadgets.flag N e.1.1 e.1.2 ∪ Gadgets.flag N e.2.1 e.2.2) := by
          apply P.property.2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inr ⟨e, he, rfl⟩
        rw [hPeq] at hS
        rcases hS with ⟨u, hu, hpu, _⟩
        simp only [Finset.mem_union, Gadgets.flag,
          Finset.mem_insert, Finset.mem_singleton] at hu hpu
        rcases hu with (rfl | rfl) | (rfl | rfl)
        · rw [← he1, Gadgets.permOf_leaf_eq N a e.1.1 false] at hpu
          rcases hpu with (h | h) | (h | h)
          · exact Gadgets.leaf_ne_hub0 N _ _ _ false h.symm
          · exact Gadgets.leaf_ne_hub0 N _ _ _ true h.symm
          · exact Gadgets.leaf_ne_hub0 N _ _ _ false h.symm
          · exact Gadgets.leaf_ne_hub0 N _ _ _ true h.symm
        · rw [← he1, Gadgets.permOf_leaf_eq N a e.1.1 true] at hpu
          rcases hpu with (h | h) | (h | h)
          · exact Gadgets.leaf_ne_hub1 N _ _ _ false h.symm
          · exact Gadgets.leaf_ne_hub1 N _ _ _ true h.symm
          · exact Gadgets.leaf_ne_hub1 N _ _ _ false h.symm
          · exact Gadgets.leaf_ne_hub1 N _ _ _ true h.symm
        · rw [← he2, Gadgets.permOf_leaf_eq N a e.2.1 false] at hpu
          rcases hpu with (h | h) | (h | h)
          · exact Gadgets.leaf_ne_hub0 N _ _ _ false h.symm
          · exact Gadgets.leaf_ne_hub0 N _ _ _ true h.symm
          · exact Gadgets.leaf_ne_hub0 N _ _ _ false h.symm
          · exact Gadgets.leaf_ne_hub0 N _ _ _ true h.symm
        · rw [← he2, Gadgets.permOf_leaf_eq N a e.2.1 true] at hpu
          rcases hpu with (h | h) | (h | h)
          · exact Gadgets.leaf_ne_hub1 N _ _ _ false h.symm
          · exact Gadgets.leaf_ne_hub1 N _ _ _ true h.symm
          · exact Gadgets.leaf_ne_hub1 N _ _ _ false h.symm
          · exact Gadgets.leaf_ne_hub1 N _ _ _ true h.symm
      exact ⟨⟨a, hval⟩, Subtype.ext hPeq.symm⟩
    have hbij : Function.Bijective toFits := by
      constructor
      · intro a1 a2 heq
        apply Subtype.ext
        funext i
        have hperm : Gadgets.permOf N a1.val =
            Gadgets.permOf N a2.val := congrArg Subtype.val heq
        have h1 : ¬ Gadgets.hits (Gadgets.permOf N a1.val)
            (Gadgets.flag N i (a1.val i)) :=
          (Gadgets.permOf_hits_flag_iff N a1.val i (a1.val i)).mpr rfl
        rw [hperm] at h1
        exact ((Gadgets.permOf_hits_flag_iff N a2.val i (a1.val i)).mp h1).symm
      · exact hdecode
    refine ⟨Equiv.ofBijective toFits hbij, ?_, ?_⟩
    · intro a i c
      exact Gadgets.permOf_hits_flag_iff N a.val i c
    · intro a b
      exact Gadgets.permOf_dist N a.val b.val


namespace OrderedSAT
abbrev Literals (n m : ℕ) := Fin m → Fin 3 → Fin n × Bool

def trueAt {n m} (lit : Literals n m) (a : Fin n → Bool) (j : Fin m) (t : Fin 3) :=
  a (lit j t).1 = (lit j t).2

def isFirst {n m} (lit : Literals n m) (a : Fin n → Bool) (j : Fin m) (h : Fin 3) :=
  trueAt lit a j h ∧ ∀ t, t < h → ¬trueAt lit a j t

def compatible {n m} (lit : Literals n m) (a : Fin n → Bool) (j : Fin m) (h : Fin 3) :=
  ∀ t, t ≤ h → a (lit j t).1 ≠ (if t = h then !(lit j t).2 else (lit j t).2)

theorem compat_iff {n m} (lit : Literals n m) (a : Fin n → Bool) (j : Fin m) (h : Fin 3) :
    compatible lit a j h ↔ isFirst lit a j h := by
  constructor
  · intro ok
    constructor
    · have self := ok h le_rfl
      simpa [trueAt] using self
    · intro t lt
      simpa [trueAt,ne_of_lt lt] using ok t lt.le
  · rintro ⟨yes,before⟩ t le
    by_cases eq : t = h
    · subst t
      simp only [if_pos rfl]
      rw [show a (lit j h).1 = (lit j h).2 from yes]
      cases (lit j h).2 <;> decide
    · simpa [eq,trueAt] using before t (lt_of_le_of_ne le eq)

theorem first_unique {n m} {lit : Literals n m} {a : Fin n → Bool} {j : Fin m}
    {h t : Fin 3} (x : isFirst lit a j h) (y : isFirst lit a j t) : h=t := by
  rcases lt_trichotomy h t with lt|eq|gt
  · exact False.elim (y.2 h lt x.1)
  · exact eq
  · exact False.elim (x.2 t gt y.1)

theorem first_exists {n m} (lit : Literals n m) (a : Fin n → Bool) (j : Fin m)
    (ok : ∃ t, trueAt lit a j t) : ∃ h, isFirst lit a j h := by
  classical
  let T := Finset.univ.filter (trueAt lit a j)
  have ne : T.Nonempty := by obtain ⟨t,ht⟩ := ok; exact ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩⟩
  refine ⟨T.min' ne,(Finset.mem_filter.mp (T.min'_mem ne)).2,?_⟩
  intro t lt ht
  exact (not_le_of_gt lt) (T.min'_le t (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩))

abbrev Models {n m} (lit : Literals n m) := {a : Fin n → Bool // ∀ j, ∃ t, trueAt lit a j t}
abbrev Valid {n m} (lit : Literals n m) :=
  {p : (Fin n → Bool) × (Fin m → Fin 3) // ∀ j, compatible lit p.1 j (p.2 j)}

noncomputable def extend {n m} (lit : Literals n m) : Models lit ≃ Valid lit where
  toFun a := ⟨(a.val, fun j => (first_exists lit a.val j (a.property j)).choose),
    fun j => (compat_iff ..).mpr (first_exists lit a.val j (a.property j)).choose_spec⟩
  invFun p := ⟨p.val.1, fun j => ⟨p.val.2 j,((compat_iff ..).mp (p.property j)).1⟩⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j
      apply first_unique _ ((compat_iff ..).mp (p.property j))
      exact (first_exists lit p.val.1 j ⟨p.val.2 j,((compat_iff ..).mp (p.property j)).1⟩).choose_spec

end OrderedSAT
namespace OrderedSAT
abbrev Tag (N : ℕ) := Fin N × Fin 3
def var {n m} (i : Fin n) : Fin (n+m) := i.castAdd m
def clause {n m} (j : Fin m) : Fin (n+m) := j.natAdd n
def next {n} (i : Fin n) : Fin n := ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_le i.val |>.trans_lt i.isLt)⟩
def code (b : Bool) : Fin 3 := if b then 1 else 0
def forbid {n m} (lit : Literals n m) (u v : Tag (n+m)) : Prop :=
  (∃ i d, u=(var i,2) ∧ v=(var (next i),d)) ∨
  ∃ (j : Fin m) (h t : Fin 3), t ≤ h ∧ u=(clause j,h) ∧
    v=(var (lit j t).1,code (if t=h then !(lit j t).2 else (lit j t).2))
theorem forbid_distinct {n m} (hn : 2 ≤ n) (lit : Literals n m) {u v} (h : forbid lit u v) : u.1 ≠ v.1 := by
  rcases h with ⟨i,d,rfl,rfl⟩ | ⟨j,h,t,le,rfl,rfl⟩
  · intro eq
    exact Gadgets.nextIdx_ne hn i (Fin.ext (congrArg (fun z : Fin (n+m) => z.val) eq.symm))
  · intro eq
    have he := congrArg (fun z : Fin (n+m) => z.val) eq
    change n+j.val=(lit j t).1.val at he
    have := (lit j t).1.isLt
    omega

noncomputable def sorted {N} (R : Tag N → Tag N → Prop) : Finset (Tag N × Tag N) := by
  classical
  exact Finset.univ.filter fun e => e.1.1 < e.2.1 ∧ (R e.1 e.2 ∨ R e.2 e.1)
theorem sorted_spec {N R} {e : Tag N × Tag N} :
    e ∈ sorted R ↔ e.1.1 < e.2.1 ∧ (R e.1 e.2 ∨ R e.2 e.1) := by classical simp [sorted]

theorem sorted_forall {N} {R : Tag N → Tag N → Prop} (dis : ∀ {u v}, R u v → u.1 ≠ v.1)
    (P : Tag N → Tag N → Prop) (sy : ∀ u v, P u v → P v u) :
    (∀ e ∈ sorted R, P e.1 e.2) ↔ ∀ u v, R u v → P u v := by
  constructor
  · intro ok u v hr
    rcases lt_or_gt_of_ne (dis hr) with lt|gt
    · exact ok (u,v) (sorted_spec.mpr ⟨lt,Or.inl hr⟩)
    · exact sy v u (ok (v,u) (sorted_spec.mpr ⟨gt,Or.inr hr⟩))
  · intro ok e he
    rcases (sorted_spec.mp he).2 with hr|hr
    · exact ok _ _ hr
    · exact sy _ _ (ok _ _ hr)

abbrev Allowed {n m} (lit : Literals n m) := {w : Fin (n+m) → Fin 3 //
  ∀ u v, forbid lit u v → w u.1 ≠ u.2 ∨ w v.1 ≠ v.2}

def encode {n m} {lit : Literals n m} (p : Valid lit) : Fin (n+m) → Fin 3 :=
  Fin.addCases (fun i => code (p.val.1 i)) (fun j => p.val.2 j)

@[simp] theorem encode_var {n m} {lit : Literals n m} (p : Valid lit) (i : Fin n) :
    encode p (var i) = code (p.val.1 i) := by simp [encode,var]
@[simp] theorem encode_clause {n m} {lit : Literals n m} (p : Valid lit) (j : Fin m) :
    encode p (clause j) = p.val.2 j := by simp [encode,clause]
theorem code_inj : Function.Injective code := by decide

def addTags {n m} (lit : Literals n m) (p : Valid lit) : Allowed lit := by
  refine ⟨encode p,?_⟩
  intro u v hr
  rcases hr with ⟨i,d,rfl,rfl⟩ | ⟨j,h,t,le,rfl,rfl⟩
  · left
    change encode p (var i) ≠ 2
    rw [encode_var]
    cases p.val.1 i <;> decide
  · change encode p (clause j) ≠ h ∨ encode p (var (lit j t).1) ≠ _
    rw [encode_clause,encode_var]
    by_cases eq : p.val.2 j=h
    · right
      exact fun same => (eq ▸ p.property j : compatible lit p.val.1 j h) t le (code_inj same)
    · exact Or.inl eq

theorem var_ne_two {n m} {lit : Literals n m} (w : Allowed lit) (i : Fin n) : w.val (var i) ≠ 2 :=
  (w.property (var i,2) (var (next i),w.val (var (next i))) (Or.inl ⟨i,w.val (var (next i)),rfl,rfl⟩)).resolve_right (not_ne_iff.mpr rfl)

def bit (t : Fin 3) : Bool := decide (t=1)
theorem bit_code (b : Bool) : bit (code b)=b := by cases b <;> rfl
theorem code_bit (t : Fin 3) (h : t ≠ 2) : code (bit t) = t := by fin_cases t <;> simp_all [bit,code]

def readTags {n m} {lit : Literals n m} (w : Allowed lit) : Valid lit := by
  refine ⟨(fun i => bit (w.val (var i)),fun j => w.val (clause j)),?_⟩
  intro j t le eq
  let h := w.val (clause j)
  let s := if t=h then !(lit j t).2 else (lit j t).2
  have hr : forbid lit (clause j,h) (var (lit j t).1,code s) := Or.inr ⟨j,h,t,le,rfl,rfl⟩
  have no := (w.property _ _ hr).resolve_left (not_ne_iff.mpr rfl)
  apply no
  change w.val (var (lit j t).1)=code s
  rw [← code_bit _ (var_ne_two w _)]
  exact congrArg code eq

def tagEquiv {n m} (lit : Literals n m) : Valid lit ≃ Allowed lit where
  toFun := addTags lit
  invFun := readTags
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change bit (encode p (var i))=_
      rw [encode_var,bit_code]
    · funext j
      exact encode_clause p j
  right_inv w := by
    apply Subtype.ext
    funext t
    refine Fin.addCases (fun i => ?_) (fun j => ?_) t
    · change encode (readTags w) (var i) = _
      rw [encode_var]
      exact code_bit _ (var_ne_two w _)
    · exact encode_clause (readTags w) j
end OrderedSAT

namespace OrderedSAT
open Gadgets

set_option maxHeartbeats 1800000 in
theorem bounds : (∀ (n m : Nat), 2 ≤ n → ∀ (lit : Fin m → Fin 3 → Fin n × Bool) (crown : Bool),
  let N := n+m
  let k := 8*N+1
  let name := fun (i : Fin N) (s : Fin 8) => Fin.ofNat (8*N+1) (8*i.val+s.val)
  let leaf := fun (i : Fin N) (c : Fin 3) (b : Bool) =>
    name i (Fin.ofNat 8 (2+2*c.val+b.toNat))
  let flag := fun (i : Fin N) (c : Fin 3) => ({leaf i c false,leaf i c true} : Finset (Fin k))
  let orient := fun i : Fin N => insert (name i 0) (Finset.univ.image (fun c : Fin 3 => leaf i c false))
  let triangle := fun (i : Fin N) (c : Fin 3) (b : Bool) => insert (name i (if b then 1 else 0)) (flag i c)
  let pad := fun (i : Fin N) (j : Fin 4) =>
    name (⟨(i.val+1)%N,Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin N) (Fin.ofNat 8 j.val)
  let control := fun S : Finset (Fin k) =>
    (∃ i, S = orient i) ∨ (∃ i c b j, S = insert (pad i j) (triangle i c b))
  let nr := if crown then k+2 else k
  let nc := if crown then k+1 else k
  let A := fun (i : Fin nr) (j : Fin nc) => if crown then
    decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
  let Fn := (Fin nr → Bool) → (Fin nc → Bool) → Bool
  let eligible := fun f : Fn => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    (if crown then PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2*k+1
     else PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k) ∧
    PEqualNP.Represents.Represents A C ∧ ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
  let passes := fun (f : Fn) (S : Finset (Fin k)) =>
    f (fun u => decide (∃ v ∈ S, v.val = u.val)) (fun _ => false) = !crown
  let var := fun i : Fin n => (i.castAdd m : Fin N)
  let clause := fun j : Fin m => (j.natAdd n : Fin N)
  let other := fun i : Fin n => (⟨(i.val+1)%n,Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let code := fun b : Bool => (if b then 1 else 0 : Fin 3)
  let tests := Finset.univ.filter (fun S : Finset (Fin k) =>
    control S ∨ (∃ (i : Fin n) (d : Fin 3), S = flag (var i) 2 ∪ flag (var (other i)) d) ∨
    (∃ (j : Fin m) (h t : Fin 3), t ≤ h ∧ S = flag (clause j) h ∪
      flag (var (lit j t).1) (code (if t = h then !(lit j t).2 else (lit j t).2))))
  let truth := fun (a : Fin n → Bool) (j : Fin m) (t : Fin 3) => a (lit j t).1 = (lit j t).2
  let Models := {a : Fin n → Bool // ∀ j, ∃ t, truth a j t}
  let Fits := {f : Fn // eligible f ∧ ∀ S ∈ tests, passes f S}
  tests.card ≤ 28*n+31*m ∧ (∀ S ∈ tests, S.card = 4)) := by
  classical
  intro n m hn lit crown N k name leaf flag orient triangle pad control nr nc A Fn eligible passes var clause other code tests truth Models Fits
  let pairs := {ht : Fin 3 × Fin 3 // ht.2 ≤ ht.1}
  let O := Finset.univ.image orient
  let T := Finset.univ.image (fun p : Fin N × Fin 3 × Bool × Fin 4 => insert (pad p.1 p.2.2.2) (triangle p.1 p.2.1 p.2.2.1))
  let V := Finset.univ.image (fun p : Fin n × Fin 3 => flag (var p.1) 2 ∪ flag (var (other p.1)) p.2)
  let C := Finset.univ.image (fun p : Fin m × pairs =>
    flag (clause p.1) p.2.val.1 ∪ flag (var (lit p.1 p.2.val.2).1) (code (if p.2.val.2 = p.2.val.1 then !(lit p.1 p.2.val.2).2 else (lit p.1 p.2.val.2).2)))
  have sub : tests ⊆ O ∪ T ∪ V ∪ C := by
    intro S hs
    rcases (Finset.mem_filter.mp hs).2 with ((⟨i,rfl⟩ | ⟨i,c,b,j,rfl⟩) | ⟨i,d,rfl⟩ | ⟨j,h,t,le,rfl⟩)
    · simp only [Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (show _ ∈ O from Finset.mem_image_of_mem orient (Finset.mem_univ i))))
    · simp only [Finset.mem_union]
      apply Or.inl; apply Or.inl; apply Or.inr
      exact Finset.mem_image.mpr ⟨(i,c,b,j), Finset.mem_univ _,rfl⟩
    · simp only [Finset.mem_union]
      apply Or.inl; apply Or.inr
      exact Finset.mem_image.mpr ⟨(i,d),Finset.mem_univ _,rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(j,(⟨(h,t),le⟩ : pairs)),Finset.mem_univ _,rfl⟩
  have co : O.card ≤ N := Finset.card_image_le.trans_eq (by simp)
  have ct : T.card ≤ N*24 := Finset.card_image_le.trans_eq (by simp)
  have cv : V.card ≤ n*3 := Finset.card_image_le.trans_eq (by simp)
  have cp : Fintype.card pairs = 6 := by decide
  have cc : C.card ≤ m*6 := Finset.card_image_le.trans_eq (by simp [cp])
  have hN : 2 ≤ N := by dsimp [N]; omega
  constructor
  · have h1 := Finset.card_le_card sub
    have h2 := Finset.card_union_le (O ∪ T ∪ V) C
    have h3 := Finset.card_union_le (O ∪ T) V
    have h4 := Finset.card_union_le O T
    dsimp only [N] at co ct
    omega
  · intro S hs
    rcases (Finset.mem_filter.mp hs).2 with ((⟨i,rfl⟩ | ⟨i,c,b,j,rfl⟩) | ⟨i,d,rfl⟩ | ⟨j,h,t,le,rfl⟩)
    · exact orient_card N i
    · exact padded_card hN i c b j
    · apply forb_card
      intro eq
      have bad : i = other i := Fin.ext (congrArg (fun z : Fin N => z.val) eq)
      exact nextIdx_ne hn i bad.symm
    · apply forb_card
      intro eq
      have he := congrArg Fin.val eq
      change n+j.val = (lit j t).1.val at he
      have := (lit j t).1.isLt
      omega
end OrderedSAT

namespace OrderedSAT
variable {α : Type*}
theorem relation_involution (R : α → α → Prop)
    (hs : ∀ {a b}, R a b → R b a) (hi : ∀ a, ¬ R a a)
    (hu : ∀ a b c, R a b → R a c → b = c) :
    ∃ p : Equiv.Perm α, Function.Involutive p ∧
      (∀ a b, R a b ↔ p a = b ∧ b ≠ a) ∧
      (∀ q : Equiv.Perm α, (∀ a b, R a b ↔ q a = b ∧ b ≠ a) → q = p) := by
  classical
  let p : α → α := fun a => if h : ∃ b, R a b then Classical.choose h else a
  have hpR : ∀ a b, R a b → p a = b := by
    intro a b h
    have he : ∃ b, R a b := ⟨b, h⟩
    dsimp only [p]
    rw [dite_eq_left he]
    exact hu a _ b (Classical.choose_spec he) h
  have hp : ∀ a, p a = a ∨ R a (p a) := by
    intro a
    by_cases he : ∃ b, R a b
    · right
      dsimp only [p]
      rw [dite_eq_left he]
      exact Classical.choose_spec he
    · left
      simp [p, he]
  have hpi : Function.Involutive p := by
    intro a
    rcases hp a with h | h
    · rw [h, h]
    · exact hpR _ _ (hs h)
  let e : Equiv.Perm α := hpi.toPerm p
  have heval : ∀ a, e a = p a := fun _ => rfl
  have hiff : ∀ a b, R a b ↔ e a = b ∧ b ≠ a := by
    intro a b
    constructor
    · intro h
      refine ⟨hpR a b h, ?_⟩
      intro hab
      exact hi a (hab ▸ h)
    · rintro ⟨hab, hn⟩
      rcases hp a with h | h
      · exact False.elim (hn (hab.symm.trans h))
      · exact hab ▸ h
  refine ⟨e, hpi, hiff, ?_⟩
  intro q hq
  apply Equiv.ext
  intro a
  by_cases h : p a = a
  · by_cases hqa : q a = a
    · exact hqa.trans h.symm
    · have hr := (hq a (q a)).2 ⟨rfl, hqa⟩
      have he := hpR a (q a) hr
      exact False.elim (hqa (he.symm.trans h))
  · have hr := (hiff a (e a)).2 ⟨rfl, h⟩
    exact (hq a (e a)).1 hr |>.1

section matchings
variable {k : ℕ}
abbrev Invs (k : ℕ) := {p : Equiv.Perm (Fin k) // Function.Involutive p}
abbrev Matching (k : ℕ) := {M : Finset (Finset (Fin k)) //
  (∀ e ∈ M, e.card = 2) ∧ ∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g}

def Edge (M : Matching k) (a b : Fin k) := a ≠ b ∧ ({a,b} : Finset _) ∈ M.val

theorem edge_symm {M : Matching k} {a b} (h : Edge M a b) : Edge M b a :=
  ⟨h.1.symm,by simpa [Finset.pair_comm] using h.2⟩

theorem edge_unique (M : Matching k) (a b c : Fin k) (h : Edge M a b) (g : Edge M a c) : b = c := by
  have sets : ({a,b} : Finset _) = {a,c} := by
    by_contra ne
    exact Finset.disjoint_left.mp (M.property.2 _ h.2 _ g.2 ne) (Finset.mem_insert_self ..) (Finset.mem_insert_self ..)
  have hb : b ∈ ({a,c} : Finset _) := sets ▸ (by simp : b ∈ ({a,b} : Finset _))
  exact (Finset.mem_insert.mp hb).resolve_left h.1.symm |> Finset.mem_singleton.mp

noncomputable def fromMatching (M : Matching k) : Invs k :=
  let x := relation_involution (Edge M) (@edge_symm _ M) (fun _ h => h.1 rfl) (edge_unique M)
  ⟨x.choose,x.choose_spec.1⟩

theorem from_spec (M : Matching k) (a b : Fin k) :
    Edge M a b ↔ (fromMatching M).val a = b ∧ b ≠ a :=
  (relation_involution (Edge M) (@edge_symm _ M) (fun _ h => h.1 rfl) (edge_unique M)).choose_spec.2.1 a b

def edges (p : Invs k) : Finset (Finset (Fin k)) :=
  (Finset.univ.filter (fun a => p.val a ≠ a)).image (fun a => {a,p.val a})

theorem edges_valid (p : Invs k) : (∀ e ∈ edges p, e.card = 2) ∧
    ∀ e ∈ edges p, ∀ g ∈ edges p, e ≠ g → Disjoint e g := by
  have mem {e} (he : e ∈ edges p) : ∃ a, p.val a ≠ a ∧ e = {a,p.val a} := by
    obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp he
    exact ⟨a,(Finset.mem_filter.mp ha).2,eq.symm⟩
  constructor
  · intro e he
    obtain ⟨a,ha,rfl⟩ := mem he
    simp [ha.symm]
  · intro e he g hg ne
    obtain ⟨a,_,rfl⟩ := mem he
    obtain ⟨b,_,rfl⟩ := mem hg
    apply Finset.disjoint_left.mpr
    intro u hu hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
    rcases hu with h|h <;> rcases hv with g|g
    · exact ne (h.symm.trans g ▸ rfl)
    · have ab : a = p.val b := h.symm.trans g
      exact ne (by rw [ab,p.property]; apply Finset.pair_comm)
    · have ba : b = p.val a := g.symm.trans h
      exact ne (by rw [ba,p.property]; apply Finset.pair_comm)
    · exact ne (p.val.injective (h.symm.trans g) ▸ rfl)

def toMatching (p : Invs k) : Matching k := ⟨edges p,edges_valid p⟩

theorem to_spec (p : Invs k) (a b : Fin k) :
    Edge (toMatching p) a b ↔ p.val a=b ∧ b ≠ a := by
  constructor
  · rintro ⟨ab,h⟩
    obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp h
    have ha : a ∈ ({u,p.val u} : Finset _) := eq.symm ▸ (by simp)
    have hb : b ∈ ({u,p.val u} : Finset _) := eq.symm ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    exact ⟨by rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> simp_all <;> exact p.property _,ab.symm⟩
  · rintro ⟨rfl,ne⟩
    exact ⟨ne.symm,Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne⟩,rfl⟩⟩

theorem inv_ext {p q : Invs k} (h : ∀ a b, (p.val a = b ∧ b ≠ a) ↔ (q.val a = b ∧ b ≠ a)) : p=q := by
  apply Subtype.ext
  apply Equiv.ext
  intro a
  by_cases pa : p.val a = a
  · by_contra ne
    have qa : q.val a ≠ a := by simpa [pa,eq_comm] using ne
    exact ne ((h a _).mpr ⟨rfl,qa⟩).1
  · exact ((h a _).mp ⟨rfl,pa⟩).1.symm

noncomputable def matchingEquiv : Invs k ≃ Matching k := by
  classical
  exact
    { toFun := toMatching
      invFun := fromMatching
      left_inv := fun p => inv_ext (fun a b => ((from_spec _ a b).symm).trans (to_spec p a b))
      right_inv := by
        intro M
        apply Subtype.ext
        ext e
        by_cases size : e.card = 2
        · obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp size
          have ed := (to_spec (fromMatching M) a b).trans (from_spec M a b).symm
          simpa [Edge,ab] using ed
        · exact iff_of_false (fun h => size ((toMatching (fromMatching M)).property.1 e h)) (fun h => size (M.property.1 e h)) }

end matchings
end OrderedSAT
namespace OrderedSAT
open CircuitSource
abbrev NR (k : ℕ) (b : Bool) := if b then k+2 else k
abbrev NC (k : ℕ) (b : Bool) := if b then k+1 else k
abbrev Fn (k : ℕ) (b : Bool) := (Fin (NR k b) → Bool) → (Fin (NC k b) → Bool) → Bool
def matrix (k : ℕ) (b : Bool) (i : Fin (NR k b)) (j : Fin (NC k b)) :=
  if b then decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
def Eligible {k : ℕ} {b : Bool} (f : Fn k b) := ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    (if b then PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2*k+1
     else PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k) ∧
    PEqualNP.Represents.Represents (matrix k b) C ∧ ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
noncomputable def canon {k} (b : Bool) (M : Matching k) : Fn k b := by
  classical
  exact fun x y =>
    let z := fun i => (List.ofFn x ++ List.ofFn y).getD i false
    let H := Pr (fun u : Fin k => u.val) (fun u => NR k b + u.val) Finset.univ M.val z
    if b then decide (¬(z (k+1) = true ∨ H)) else decide H

theorem characterize {k} (hk : 7 ≤ k) (b : Bool) (f : Fn k b) :
    Eligible f ↔ ∃ M : Matching k, f = canon b M := by
  classical
  constructor
  · rintro ⟨C,hh,hA,ev⟩
    cases b
    · obtain ⟨M,hm,h⟩ := classify_false k (by omega) C hh.1 hh.2 hA
      refine ⟨⟨M,hm⟩,?_⟩
      funext x y
      rw [ev]
      apply Bool.eq_iff_iff.mpr
      simpa [canon,NR,NC] using h x y
    · obtain ⟨M,hm,h⟩ := classify_true k hk C hh.1 hh.2 hA
      refine ⟨⟨M,hm⟩,?_⟩
      funext x y
      rw [ev]
      apply Bool.eq_iff_iff.mpr
      simpa [canon,NR,NC] using h x y
  · rintro ⟨M,rfl⟩
    cases b
    · obtain ⟨C,hm,hs,hr,he⟩ := circuit_false k (by omega) M.val M.property
      refine ⟨C,⟨hm,hs⟩,hr,?_⟩
      intro x y
      symm
      apply Bool.eq_iff_iff.mpr
      simpa [canon,NR,NC] using he x y
    · obtain ⟨C,hm,hs,hr,he⟩ := circuit_true k (by omega) M.val M.property
      refine ⟨C,⟨hm,hs⟩,hr,?_⟩
      intro x y
      symm
      apply Bool.eq_iff_iff.mpr
      simpa [canon,NR,NC] using he x y

def passes {k b} (f : Fn k b) (S : Finset (Fin k)) :=
  f (fun u => decide (∃ v ∈ S, v.val = u.val)) (fun _ => false) = !b

theorem probe {k} (b : Bool) (M : Matching k) (S : Finset (Fin k)) :
    passes (canon b M) S ↔ ∃ e ∈ M.val, e ⊆ S := by
  classical
  let x : Fin (NR k b) → Bool := fun u => decide (∃ v ∈ S, v.val = u.val)
  let y : Fin (NC k b) → Bool := fun _ => false
  let z := fun i => (List.ofFn x ++ List.ofFn y).getD i false
  have xn : k ≤ NR k b := by cases b <;> simp [NR]
  have yn : k ≤ NC k b := by cases b <;> simp [NC]
  have left (i : Fin k) : z i.val = true ↔ i ∈ S := by
    change (List.ofFn x ++ List.ofFn y).getD i.val false = true ↔ _
    rw [getD_app_left x y _ (lt_of_lt_of_le i.isLt xn)]
    simp [x,Fin.val_inj]
  have right (i : Fin k) : z (NR k b + i.val) = false := getD_app_right x y _ (lt_of_lt_of_le i.isLt yn)
  have sz (e) (he : e ∈ M.val) : e.Nonempty := Finset.card_pos.mp (by rw [M.property.1 e he]; decide)
  have hit : Pr (fun i : Fin k => i.val) (fun i => NR k b+i.val) Finset.univ M.val z ↔ ∃ e ∈ M.val, e ⊆ S := by
    constructor
    · rintro (⟨i,_,_,hi⟩ | ⟨e,he,h | h⟩)
      · simp [right] at hi
      · exact ⟨e,he,fun i hi => (left i).mp (h i hi)⟩
      · obtain ⟨i,hi⟩ := sz e he
        have := h i hi
        simp [right] at this
    · rintro ⟨e,he,hs⟩
      exact Or.inr ⟨e,he,Or.inl (fun i hi => (left i).mpr (hs hi))⟩
  have extra (hb : b=true) : z (k+1) = false := by
    have hnr : k+1 < NR k b := by simp [hb,NR]
    change (List.ofFn x ++ List.ofFn y).getD (k+1) false = false
    rw [getD_app_left x y _ hnr]
    simp only [x,decide_eq_false_iff_not]
    rintro ⟨i,_,e⟩
    have := i.isLt
    omega
  let H := Pr (fun i : Fin k => i.val) (fun i => NR k b+i.val) Finset.univ M.val z
  change (if b then decide (¬(z (k+1) = true ∨ H)) else decide H) = !b ↔ _
  cases b
  · simpa [H] using hit
  · simpa [H,extra rfl] using hit

theorem canon_inj {k} (b : Bool) : Function.Injective (@canon k b) := by
  intro M L h
  apply Subtype.ext
  ext e
  have same := (probe b M e).symm.trans ((congrArg (fun f : Fn k b => passes f e) h).to_iff.trans (probe b L e))
  have iff_mem (T : Matching k) (he : e.card=2) : (∃ g ∈ T.val, g ⊆ e) ↔ e ∈ T.val := by
    constructor
    · rintro ⟨g,hg,sub⟩
      exact Finset.eq_of_subset_of_card_le sub (by rw [he,T.property.1 g hg]) ▸ hg
    · intro h; exact ⟨e,h,Finset.Subset.refl _⟩
  by_cases he : e.card=2
  · exact (iff_mem M he).symm.trans (same.trans (iff_mem L he))
  · exact iff_of_false (fun h => he (M.property.1 e h)) (fun h => he (L.property.1 e h))
end OrderedSAT
namespace OrderedSAT
def hits {k} (p : Invs k) (S : Finset (Fin k)) := ∃ u ∈ S, p.val u ∈ S ∧ p.val u ≠ u
theorem probe_inv {k} (b : Bool) (p : Invs k) (S : Finset (Fin k)) :
    passes (canon b (toMatching p)) S ↔ hits p S := by
  rw [probe]
  constructor
  · rintro ⟨e,he,sub⟩
    obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp ((toMatching p).property.1 _ he)
    have same := (to_spec p a b).mp ⟨ab,he⟩
    exact ⟨a,sub (by simp),same.1 ▸ sub (by simp),same.1 ▸ same.2⟩
  · rintro ⟨a,ha,hpa,ne⟩
    refine ⟨{a,p.val a},((to_spec p a _).mpr ⟨rfl,ne⟩).2,?_⟩
    simpa using Finset.insert_subset_iff.mpr ⟨ha,Finset.singleton_subset_iff.mpr hpa⟩

abbrev GoodPerm {k} (tests : Finset (Finset (Fin k))) :=
  {p : Equiv.Perm (Fin k) // Function.Involutive p ∧ ∀ S ∈ tests, ∃ u ∈ S, p u ∈ S ∧ p u ≠ u}
abbrev GoodFn {k} (b : Bool) (tests : Finset (Finset (Fin k))) :=
  {f : Fn k b // Eligible f ∧ ∀ S ∈ tests, passes f S}

noncomputable def fitMap {k} (hk : 7 ≤ k) (b) (tests) (p : GoodPerm (k:=k) tests) : GoodFn b tests :=
  let P : Invs k := ⟨p.val,p.property.1⟩
  ⟨canon b (toMatching P), (characterize hk b _).mpr ⟨_,rfl⟩,
    fun S hs => (probe_inv b P S).mpr (p.property.2 S hs)⟩

theorem fitBij {k} (hk : 7 ≤ k) (b) (tests) : Function.Bijective (fitMap hk b tests) := by
  constructor
  · intro p q eq
    have h := canon_inj b (congrArg Subtype.val eq)
    have h2 : (⟨p.val,p.property.1⟩ : Invs k) = ⟨q.val,q.property.1⟩ := matchingEquiv.injective h
    exact Subtype.ext (congrArg (fun z : Invs k => z.val) h2)
  · rintro ⟨f,hel,all⟩
    obtain ⟨M,rfl⟩ := (characterize hk b f).mp hel
    let P := fromMatching M
    have eq : toMatching P = M := matchingEquiv.right_inv M
    have good : ∀ S ∈ tests, hits P S := fun S hs => (probe_inv b P S).mp (eq ▸ all S hs)
    exact ⟨⟨P.val,P.property,good⟩,Subtype.ext (congrArg (canon b) eq)⟩

noncomputable def fitEquiv {k} (hk : 7 ≤ k) (b) (tests) : GoodPerm (k:=k) tests ≃ GoodFn b tests :=
  Equiv.ofBijective _ (fitBij hk b tests)

end OrderedSAT
end PEqualNP.Outside.L_meta_32017_aux
open PEqualNP.Outside.L_meta_32017_aux
open PEqualNP.Outside.L_meta_32017_aux.OrderedSAT in
theorem PEqualNP.Outside.L_meta_32017 : (∀ (n m : Nat), 2 ≤ n → ∀ (lit : Fin m → Fin 3 → Fin n × Bool) (crown : Bool),
  let N := n+m
  let k := 8*N+1
  let name := fun (i : Fin N) (s : Fin 8) => Fin.ofNat (8*N+1) (8*i.val+s.val)
  let leaf := fun (i : Fin N) (c : Fin 3) (b : Bool) =>
    name i (Fin.ofNat 8 (2+2*c.val+b.toNat))
  let flag := fun (i : Fin N) (c : Fin 3) => ({leaf i c false,leaf i c true} : Finset (Fin k))
  let orient := fun i : Fin N => insert (name i 0) (Finset.univ.image (fun c : Fin 3 => leaf i c false))
  let triangle := fun (i : Fin N) (c : Fin 3) (b : Bool) => insert (name i (if b then 1 else 0)) (flag i c)
  let pad := fun (i : Fin N) (j : Fin 4) =>
    name (⟨(i.val+1)%N,Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin N) (Fin.ofNat 8 j.val)
  let control := fun S : Finset (Fin k) =>
    (∃ i, S = orient i) ∨ (∃ i c b j, S = insert (pad i j) (triangle i c b))
  let nr := if crown then k+2 else k
  let nc := if crown then k+1 else k
  let A := fun (i : Fin nr) (j : Fin nc) => if crown then
    decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
  let Fn := (Fin nr → Bool) → (Fin nc → Bool) → Bool
  let eligible := fun f : Fn => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    (if crown then PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2*k+1
     else PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k) ∧
    PEqualNP.Represents.Represents A C ∧ ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
  let passes := fun (f : Fn) (S : Finset (Fin k)) =>
    f (fun u => decide (∃ v ∈ S, v.val = u.val)) (fun _ => false) = !crown
  let var := fun i : Fin n => (i.castAdd m : Fin N)
  let clause := fun j : Fin m => (j.natAdd n : Fin N)
  let other := fun i : Fin n => (⟨(i.val+1)%n,Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let code := fun b : Bool => (if b then 1 else 0 : Fin 3)
  let tests := Finset.univ.filter (fun S : Finset (Fin k) =>
    control S ∨ (∃ (i : Fin n) (d : Fin 3), S = flag (var i) 2 ∪ flag (var (other i)) d) ∨
    (∃ (j : Fin m) (h t : Fin 3), t ≤ h ∧ S = flag (clause j) h ∪
      flag (var (lit j t).1) (code (if t = h then !(lit j t).2 else (lit j t).2))))
  let truth := fun (a : Fin n → Bool) (j : Fin m) (t : Fin 3) => a (lit j t).1 = (lit j t).2
  let Models := {a : Fin n → Bool // ∀ j, ∃ t, truth a j t}
  let Fits := {f : Fn // eligible f ∧ ∀ S ∈ tests, passes f S}
  tests.card ≤ 28*n+31*m ∧ (∀ S ∈ tests, S.card = 4) ∧
  ∃ E : Models ≃ Fits, (∀ a i b, (¬ passes (E a).val (flag (var i) (code b))) ↔ a.val i = b) ∧
    ∀ a j h, (¬ passes (E a).val (flag (clause j) h)) ↔
      truth a.val j h ∧ ∀ t, t < h → ¬ truth a.val j t) := by
  classical
  intro n m hn lit crown N k name leaf flag orient triangle pad control nr nc A Fn eligible passes var clause other code tests truth Models Fits
  have bd := bounds n m hn lit crown
  refine ⟨bd.1,bd.2,?_⟩
  let R := forbid lit
  let B := sorted R
  let tagSet (u v : Tag N) := flag u.1 u.2 ∪ flag v.1 v.2
  let testsB := Finset.univ.filter fun S : Finset (Fin k) =>
    control S ∨ ∃ e ∈ B, S = tagSet e.1 e.2
  have dis : ∀ {u v}, R u v → u.1 ≠ v.1 := fun h => forbid_distinct hn lit h
  have same (S : Finset (Fin k)) : (∃ e ∈ B, S = tagSet e.1 e.2) ↔ ∃ u v, R u v ∧ S = tagSet u v := by
    constructor
    · rintro ⟨e,he,eq⟩
      rcases (sorted_spec.mp he).2 with hr|hr
      · exact ⟨e.1,e.2,hr,eq⟩
      · exact ⟨e.2,e.1,hr,eq.trans (Finset.union_comm ..)⟩
    · rintro ⟨u,v,hr,eq⟩
      rcases lt_or_gt_of_ne (dis hr) with lt|gt
      · exact ⟨(u,v),sorted_spec.mpr ⟨lt,Or.inl hr⟩,eq⟩
      · exact ⟨(v,u),sorted_spec.mpr ⟨gt,Or.inr hr⟩,eq.trans (Finset.union_comm ..)⟩
  have sets_eq : testsB=tests := by
    ext S
    simp only [testsB,tests,Finset.mem_filter,Finset.mem_univ,true_and,same]
    apply or_congr_right
    constructor
    · rintro ⟨u,v,hr,rfl⟩
      rcases hr with ⟨i,c,rfl,rfl⟩ | ⟨j,h,t,le,rfl,rfl⟩
      · exact Or.inl ⟨i,c,rfl⟩
      · exact Or.inr ⟨j,h,t,le,rfl⟩
    · rintro (⟨i,d,rfl⟩ | ⟨j,h,t,le,rfl⟩)
      · exact ⟨_,_,Or.inl ⟨i,d,rfl,rfl⟩,rfl⟩
      · exact ⟨_,_,Or.inr ⟨j,h,t,le,rfl,rfl⟩,rfl⟩
  let Tgood := {w : Fin N → Fin 3 // ∀ e ∈ B, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2}
  let lift : Allowed lit ≃ Tgood := Equiv.subtypeEquivRight fun w =>
    (sorted_forall dis (fun u v => w u.1 ≠ u.2 ∨ w v.1 ≠ v.2) (fun _ _ => Or.symm)).symm
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hk : 7 ≤ k := by dsimp [k]; omega
  obtain ⟨_,_,E,reading,_⟩ := Gadgets N hN B (fun e he => (sorted_spec.mp he).1)
  change Tgood ≃ GoodPerm testsB at E
  let sat := (extend lit).trans ((tagEquiv lit).trans lift)
  let F := fitEquiv hk crown testsB
  let G : GoodFn crown testsB ≃ Fits := Equiv.subtypeEquivRight (fun f => by
    change (Eligible f ∧ ∀ S ∈ testsB, OrderedSAT.passes f S) ↔ (Eligible f ∧ ∀ S ∈ tests, OrderedSAT.passes f S)
    rw [sets_eq])
  have read (a : Models) (i : Fin N) (c : Fin 3) :
      (¬passes ((sat.trans (E.trans (F.trans G))) a).val (flag i c)) ↔ (sat a).val i=c := by
    let p := E (sat a)
    let P : Invs k := ⟨p.val,p.property.1⟩
    change (¬OrderedSAT.passes (canon crown (toMatching P)) (flag i c)) ↔ _
    rw [probe_inv]
    exact reading (sat a) i c
  refine ⟨sat.trans (E.trans (F.trans G)),?_,?_⟩
  · intro a i b
    refine (read a (var i) (code b)).trans ?_
    change (encode (extend lit a) (OrderedSAT.var i) = OrderedSAT.code b) ↔ _
    rw [encode_var]
    exact code_inj.eq_iff
  · intro a j h
    refine (read a (clause j) h).trans ?_
    change encode (extend lit a) (OrderedSAT.clause j) = h ↔ isFirst lit a.val j h
    rw [encode_clause]
    have first := (compat_iff ..).mp ((extend lit a).property j)
    change isFirst lit a.val j ((extend lit a).val.2 j) at first
    exact ⟨fun eq => eq ▸ first,fun other => first_unique first other⟩
