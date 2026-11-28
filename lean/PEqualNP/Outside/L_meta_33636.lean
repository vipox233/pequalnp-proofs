import Mathlib.Tactic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Int.ModEq
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33636

namespace Obs
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
 ·
  rename_i hi
  exact (hread i hi).symm
 ·
  rename_i hi
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
 ·
  rename_i h'
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
  ·
   intro u hu
   exact (mem_desc C n w u).2 (Or.inr ⟨c, hc, ih c (ch_lt C n hc) v h hu⟩)
theorem desc_parent : ∀ w v, v ∈ desc C n w → v ≠ w → ∃ p ∈ desc C n w, v ∈ ch C n p := by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro v hv hne
  rcases (mem_desc C n w v).1 hv with rfl | ⟨c, hc, h⟩
  · exact absurd rfl hne
  ·
   by_cases hvc : v = c
   · exact ⟨w, self_desc C n w, hvc ▸ hc⟩
   ·
    obtain ⟨p, hp, hvp⟩ := ih c (ch_lt C n hc) v h hvc
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
 ·
  rename_i h
  refine (List.length_filter_le _ _).trans ?_
  unfold reads
  have hg' : (gateAt C n w).inputs.length ≤ 2 := by
   rw [gateAt_eq C n h.2]
   exact (hg _ (List.getElem_mem h.2)).2
  by_cases hn : (gateAt C n w).op = GateOp.not
  ·
   rw [if_pos hn, if_pos (show isNot C n w from ⟨hw, hn⟩), List.length_take]
   omega
  ·
   rw [if_neg hn, if_neg (show ¬ isNot C n w from fun c => hn c.2)]
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
  ·
   refine ⟨p, hpG, ?_⟩
   simp only [F, if_neg hpr, hvc]
   exact List.mem_toFinset.2 hcp
  ·
   refine ⟨s, hs, ?_⟩
   simp only [F]
   split
   · exact Finset.mem_erase.2 ⟨hvc, hvs⟩
   · exact hvs
 have h8 : ∑ s ∈ gatesIn C n o, (F s).card < ∑ s ∈ gatesIn C n o, (ch C n s).toFinset.card := by
  apply Finset.sum_lt_sum
  ·
   intro s _
   simp only [F]
   split
   · exact Finset.card_erase_le
   · exact le_rfl
  ·
   refine ⟨r, hrG, ?_⟩
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
 ·
  refine Or.inl ⟨hwn, ?_, ?_⟩
  ·
   ext v
   rw [mem_desc]
   have : ch C n w = [] := by
    unfold ch
    rw [if_neg (by omega)]
   simp [this]
  ·
   intro f
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
 ·
  right
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
   ·
    ext v
    rw [hdesc, hcha]
    simp
   ·
    intro f
    change value C (inp n f) w = !value C (inp n f) a
    rw [hval, hop', hin]
    simp [GateOp.eval, haw]
 ·
  left
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
  ·
   ext v
   rw [hdesc, hchab]
   simp
  ·
   rcases hop.1 with h | h | h
   ·
    left
    intro f
    change value C (inp n f) w = (value C (inp n f) a && value C (inp n f) b)
    rw [hval, h, hab]
    simp [GateOp.eval, haw, hbw]
   ·
    right
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
 ·
  rw [h]
  exact Finset.mem_singleton_self _
 ·
  rw [h]
  exact Finset.mem_insert_self _ _
 ·
  rw [h]
  exact Finset.mem_insert_self _ _
theorem sup_ne : ∀ w ∈ T, (sup n S w).Nonempty := by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro hw
  rcases H w hw with ⟨h1, h2, _⟩ | ⟨h0, _, a, ha, b, _, haw, _, _, h, _⟩ | ⟨h0, _, a, ha, haw, h, _⟩
  ·
   rw [sup_leaf h2 h1]
   exact Finset.singleton_nonempty _
  ·
   obtain ⟨i, hi⟩ := ih a haw ha
   exact ⟨i, (sup_bin h h0 i).2 (Or.inl hi)⟩
  ·
   rw [sup_un h h0]
   exact ih a haw ha
theorem dep : ∀ w ∈ T, ∀ f g : ℕ → Bool, (∀ i ∈ sup n S w, f i = g i) → V w f = V w g := by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro hw f g hfg
  rcases H w hw with ⟨h1, h2, h3⟩ | ⟨h0, _, a, ha, b, hb, haw, hbw, _, h, hv⟩ | ⟨h0, _, a, ha, haw, h, hv⟩
  ·
   rw [h3, h3]
   exact hfg w (by rw [sup_leaf h2 h1]; simp)
  ·
   have e1 := ih a haw ha f g (fun i hi => hfg i ((sup_bin h h0 i).2 (Or.inl hi)))
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
  ·
   rw [h3, h3]
   exact hfg w
  ·
   have ma := ih a haw ha (fun v hv => hm v (by rw [h]; simp [hv])) f g hfg
   have mb := ih b hbw hb (fun v hv => hm v (by rw [h]; simp [hv])) f g hfg
   rcases hv with hv | hv <;> rw [hv, hv]
   ·
    simp only [Bool.and_eq_true]
    exact fun p => ⟨ma p.1, mb p.2⟩
   ·
    simp only [Bool.or_eq_true]
    exact fun p => p.imp ma mb
  · exact absurd hN (hm w (self_mem H w hw))
theorem mono_zero : ∀ w ∈ T, (∀ v ∈ S w, ¬ N v) → V w zero = false := by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro hw hm
  rcases H w hw with ⟨_, _, h3⟩ | ⟨_, _, a, ha, b, hb, haw, hbw, _, h, hv⟩ | ⟨_, hN, _⟩
  ·
   rw [h3]
   rfl
  ·
   have ma := ih a haw ha (fun v hv => hm v (by rw [h]; simp [hv]))
   have mb := ih b hbw hb (fun v hv => hm v (by rw [h]; simp [hv]))
   rcases hv with hv | hv <;> rw [hv, ma, mb] <;> rfl
  · exact absurd hN (hm w (self_mem H w hw))
theorem off {w : ℕ} (hw : w ∈ T) (hm : ∀ v ∈ S w, ¬ N v) (f : ℕ → Bool)
  (hf : ∀ i ∈ sup n S w, f i = false) : V w f = false :=
 (dep H w hw f zero hf).trans (mono_zero H w hw hm)
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
 ·
  intro e he
  rcases Finset.mem_union.1 he with h | h
  · exact hM.1 e h
  · exact hL.1 e h
 ·
  intro e he g hg hne
  rcases Finset.mem_union.1 he with h | h <;> rcases Finset.mem_union.1 hg with h' | h'
  · exact hM.2 e h g h' hne
  · exact hd.mono (hs e h) (ht g h')
  · exact (hd.mono (hs g h') (ht e h)).symm
  · exact hL.2 e h g h' hne
 ·
  intro e he
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
 ·
  intro h
  by_contra c
  have : V a f = false := off H ha ma f (fun i hi => by
   cases hfi : f i
   · rfl
   · exact absurd ⟨i, hi, hfi⟩ c)
  rw [this] at h
  exact Bool.false_ne_true h
 ·
  rintro ⟨z, hz, hfz⟩
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
  ·
   exfalso
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
  ·
   have h1 : ∀ u ∈ s, V a (two (xi u) (yi u)) = true ∧ V b (two (xi u) (yi u)) = true := by
    intro u hu
    have := hval u hu u hu
    rw [hv] at this
    simpa using this
   have h2 : ∀ u ∈ s, (xi u ∈ sup n S a ∨ yi u ∈ sup n S a) ∧ (xi u ∈ sup n S b ∨ yi u ∈ sup n S b) := by
    intro u hu
    constructor
    ·
     by_contra c
     rw [not_or] at c
     have := offt a ha ma _ _ c.1 c.2
     rw [(h1 u hu).1] at this
     exact Bool.noConfusion this
    ·
     by_contra c
     rw [not_or] at c
     have := offt b hb mb _ _ c.1 c.2
     rw [(h1 u hu).2] at this
     exact Bool.noConfusion this
   have h3a : ∀ z ∈ sup n S a, V a (only z) = true := by
    intro z hz
    obtain ⟨u, hu, rfl | rfl⟩ := (hs z).1 ((hsup z).2 (Or.inl hz))
    ·
     have : yi u ∉ sup n S a := by
      intro c
      rcases (h2 u hu).2 with d | d
      · exact disj _ hz d
      · exact disj _ c d
     rw [← onel a ha (xi u) (yi u) this]
     exact (h1 u hu).1
    ·
     have : xi u ∉ sup n S a := by
      intro c
      rcases (h2 u hu).2 with d | d
      · exact disj _ c d
      · exact disj _ hz d
     rw [← oner a ha (xi u) (yi u) this]
     exact (h1 u hu).1
   have h3b : ∀ z ∈ sup n S b, V b (only z) = true := by
    intro z hz
    obtain ⟨u, hu, rfl | rfl⟩ := (hs z).1 ((hsup z).2 (Or.inr hz))
    ·
     have : yi u ∉ sup n S b := by
      intro c
      rcases (h2 u hu).1 with d | d
      · exact disj _ d hz
      · exact disj _ d c
     rw [← onel b hb (xi u) (yi u) this]
     exact (h1 u hu).2
    ·
     have : xi u ∉ sup n S b := by
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
     ·
      intro hz
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
     ·
      intro hz
      obtain ⟨u, hu, e⟩ := (hs z).1 ((hsup z).2 (Or.inr hz))
      rcases only2 u hu with rfl | rfl <;> rcases e with rfl | rfl
      · exact (disj _ hpa hz).elim
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact (disj _ yqa hz).elim
     · rintro (rfl | rfl) <;> assumption
    refine ⟨{{p, q}}, ⟨?_, ?_⟩, ?_, ?_⟩
    ·
     intro e he
     rw [Finset.mem_singleton] at he
     rw [he, Finset.card_pair hqp.symm]
    ·
     intro e he g hg hne
     rw [Finset.mem_singleton] at he hg
     exact absurd (he.trans hg.symm) hne
    ·
     intro e he
     rw [Finset.mem_singleton] at he
     rw [he, hs2]
    ·
     intro f
     rw [hv, Bool.and_eq_true, and_child H ha ma f h3a, and_child H hb mb f h3b]
     simp only [ma', mb', or_and_right, exists_or, exists_eq_left]
     rw [hs2]
     simp only [Pr, Finset.mem_insert, Finset.mem_singleton, or_and_right, exists_or, exists_eq_left,
      forall_eq_or_imp, forall_eq]
     tauto
   obtain ⟨i, hi⟩ := sup_ne H w hw
   obtain ⟨p, hp, _⟩ := (hs i).1 hi
   by_cases hq : ∃ q ∈ s, q ≠ p
   ·
    obtain ⟨q, hq, hqp⟩ := hq
    rcases (inab p hp).1 with c | c
    · exact core a ha b hb ma mb hsup disj h3a h3b hv p hp q hq hqp c
    ·
     exact core b hb a ha mb ma (fun i => (hsup i).trans or_comm) (fun i x y => disj i y x) h3b h3a
      (fun f => by rw [hv, Bool.and_comm]) p hp q hq hqp c
   ·
    have only1 : ∀ r ∈ s, r = p := fun r hr => by
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
     ·
      rcases (h2 p hp).2 with d | d
      · exact (disj _ c d).elim
      · exact Or.inl ⟨c, d⟩
     ·
      rcases (h2 p hp).1 with d | d
      · exact (disj _ d c).elim
      · exact Or.inr ⟨d, c⟩
    have uni : ∀ c : ℕ, ∀ z0, z0 ∈ sup n S c → (∀ z ∈ sup n S c, z = z0) →
      ((∃ z ∈ sup n S c, f z = true) ↔ f z0 = true) := by
     intro c z0 h0' hu
     constructor
     ·
      rintro ⟨z, hz, hf⟩
      rwa [hu z hz] at hf
     ·
      intro hf
      exact ⟨z0, h0', hf⟩
    rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
    ·
     rw [uni a (xi p) k1, uni b (yi p) k2]
     ·
      intro z hz
      rcases vars z ((hsup z).2 (Or.inr hz)) with e | e
      · exact (disj _ k1 (e ▸ hz)).elim
      · exact e
     ·
      intro z hz
      rcases vars z ((hsup z).2 (Or.inl hz)) with e | e
      · exact e
      · exact (disj _ (e ▸ hz) k2).elim
    ·
     rw [uni a (yi p) k1, uni b (xi p) k2, and_comm]
     ·
      intro z hz
      rcases vars z ((hsup z).2 (Or.inr hz)) with e | e
      · exact e
      · exact (disj _ k1 (e ▸ hz)).elim
     ·
      intro z hz
      rcases vars z ((hsup z).2 (Or.inl hz)) with e | e
      · exact (disj _ (e ▸ hz) k2).elim
      · exact e
  ·
   have sa0 : ∀ z, V a (only z) = false ∧ V b (only z) = false := by
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
    ·
     rw [onel a ha _ _ (fun c => disj _ c c2), oner b hb _ _ (fun c => disj _ c1 c),
      (sa0 _).1, (sa0 _).2] at tr
     exact Bool.noConfusion tr
    ·
     rw [oner a ha _ _ (fun c => disj _ c c1), onel b hb _ _ (fun c => disj _ c2 c),
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
    ·
     intro i
     constructor
     ·
      intro hi
      obtain ⟨u, hu, e⟩ := (hs i).1 ((hsup i).2 (Or.inl hi))
      refine ⟨u, Finset.mem_filter.2 ⟨hu, ?_⟩, e⟩
      rcases tog u hu with c | c
      · exact c.1
      ·
       rcases e with e | e
       · exact (disj _ (e ▸ hi) c.1).elim
       · exact (disj _ (e ▸ hi) c.2).elim
     ·
      rintro ⟨u, hu, e⟩
      rw [Finset.mem_filter] at hu
      rcases tog u hu.1 with c | c
      ·
       rcases e with rfl | rfl
       · exact c.1
       · exact c.2
      · exact (disj _ hu.2 c.1).elim
    ·
     intro u hu v hv'
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
    ·
     intro z
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
  ·
   have ez : z = w := by
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
    ·
     have := hsing i e
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
    ·
     rw [onel a ha _ _ (fun c => disj _ c c2), oner b hb _ _ (fun c => disj _ c1 c),
      asing _ (hzx u).symm, bsing] at tr
     exact Bool.noConfusion tr
    ·
     rw [oner a ha _ _ (fun c => disj _ c c1), onel b hb _ _ (fun c => disj _ c2 c),
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
    ·
     intro hi
     refine Finset.mem_filter.2 ⟨hu, ?_⟩
     rcases tog u hu with c | c
     · exact c.1
     ·
      rcases e with e | e
      · exact (disj _ (e ▸ hi) c.1).elim
      · exact (disj _ (e ▸ hi) c.2).elim
    ·
     intro hi
     refine Finset.mem_filter.2 ⟨hu, ?_⟩
     rcases tog u hu with c | c
     ·
      rcases e with e | e
      · exact (disj _ c.1 (e ▸ hi)).elim
      · exact (disj _ c.2 (e ▸ hi)).elim
     · exact c.1
   obtain ⟨Ma, hMa, sMa, va⟩ := ih a haw ha ma sa (by
     intro i
     constructor
     ·
      intro hi
      rcases (hs i).1 ((hsup i).2 (Or.inl hi)) with e | ⟨u, hu, e⟩
      · exact Or.inl e
      · exact Or.inr ⟨u, (tos u hu i e).1 hi, e⟩
     ·
      rintro (rfl | ⟨u, hu, rfl | rfl⟩)
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
     ·
      intro hi
      rcases (hs i).1 ((hsup i).2 (Or.inr hi)) with e | ⟨u, hu, e⟩
      · exact (zb (e ▸ hi)).elim
      · exact ⟨u, (tos u hu i e).2 hi, e⟩
     ·
      rintro ⟨u, hu, rfl | rfl⟩
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
  ·
   exfalso
   rw [hv, Bool.and_eq_true] at hz
   have off1 : ∀ c ∈ T, (∀ v ∈ S c, ¬ N v) → z ∉ sup n S c → V c (only z) = false := by
    intro c hc mc hzc
    apply off H hc mc
    intro i hi
    have : i ≠ z := fun e => hzc (e ▸ hi)
    simp [only, this]
   by_cases c : z ∈ sup n S a
   ·
    have := off1 b hb mb (disj z c)
    rw [hz.2] at this
    exact Bool.noConfusion this
   ·
    have := off1 a ha ma c
    rw [hz.1] at this
    exact Bool.noConfusion this
  ·
   rcases (hsup z).1 ((hs z).2 (Or.inl rfl)) with c | c
   · exact core a ha b hb haw hbw ma mb hsup disj hv c
   ·
    exact core b hb a ha hbw haw mb ma (fun i => (hsup i).trans or_comm) (fun i x y => disj i y x)
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
   ·
    by_contra c
    rw [Bool.not_eq_false] at c
    have := mono H w hw hm (only (xi u)) (two (xi u) (yi u)) (fun i hi => by
     simp only [only, two, decide_eq_true_eq] at hi ⊢
     exact Or.inl hi) c
    rw [h0] at this
    exact Bool.noConfusion this
   ·
    by_contra c
    rw [Bool.not_eq_false] at c
    have := mono H w hw hm (only (yi u)) (two (xi u) (yi u)) (fun i hi => by
     simp only [only, two, decide_eq_true_eq] at hi ⊢
     exact Or.inr hi) c
    rw [h0] at this
    exact Bool.noConfusion this
  rcases H w hw with ⟨_, _, h3⟩ | ⟨h0, _, a, ha, b, hb, haw, hbw, hd, h, hv⟩ | ⟨_, hN, _⟩
  ·
   have e1 := hval i0 i1
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
  ·
   have nab : V a zero = false ∧ V b zero = false := ⟨mono_zero H a ha ma, mono_zero H b hb mb⟩
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
     ·
      intro h1
      rcases c2 with c2 | c2
      · exact (disj _ h1 c2).elim
      · exact c2
     ·
      intro h2
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
   ·
    have xb : xi i0 ∈ sup n S b := by
     rcases one b hb mb _ _ (both i0 i1 n01).2 with d | d
     · exact d
     · exact (disj _ c d).elim
    exact core b hb a ha mb ma (fun i x y => disj i y x) (fun u v huv => (both u v huv).symm)
     (fun f => by rw [hv, Bool.and_comm]) xb
  ·
   have sa : ∀ i, V w (only i) = false → V a (only i) = false ∧ V b (only i) = false := by
    intro i hi
    rw [hv] at hi
    exact Bool.or_eq_false_iff.1 hi
   have same : ∀ c ∈ T, ∀ u v : Fin k, V c (two (xi u) (yi v)) = true → V c (only (xi u)) = false →
     V c (only (yi v)) = false → xi u ∈ sup n S c ∧ yi v ∈ sup n S c := by
    intro c hc u v ht h1 h2
    constructor
    ·
     by_contra d
     rw [oner c hc _ _ d, h2] at ht
     exact Bool.noConfusion ht
    ·
     by_contra d
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
     ·
      have := same a ha u v t (sa _ (sing u).1).1 (sa _ (sing v).2).1
      exact ⟨fun _ => this.2, fun _ => this.1⟩
     ·
      have := same b hb u v t (sa _ (sing u).1).2 (sa _ (sing v).2).2
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
    ·
     intro u v
     have t := hval u v
     rw [hv, bz _ _ (Or.inr (xnb u)) (Or.inr (ynb v)), Bool.or_false] at t
     exact t
    ·
     intro u
     have t := hcol u
     rw [hv, bz _ _ (Or.inr (xnb u)) (Or.inl rfl), Bool.or_false] at t
     exact t
    · exact (sa z hz).1
   have t := hval i0 i1
   rw [hv] at t
   simp only [n01, ne_eq, not_false_eq_true, decide_true, Bool.or_eq_true] at t
   rcases t with t | t
   ·
    exact core a ha b hb haw ma mb disj hv
     (same a ha _ _ t (sa _ (sing i0).1).1 (sa _ (sing i1).2).1).1
   ·
    exact core b hb a ha hbw mb ma (fun i x y => disj i y x) (fun f => by rw [hv, Bool.or_comm])
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
  ·
   rw [val_input C n w h1, val_input C n w h1]
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
   ·
    rename_i hiw
    have hc := mem_ch C n hn hj hi hiw
    apply ih i hiw
    intro v hv
    exact h v ((mem_desc C n w v).2 (Or.inr ⟨i, hc, hv⟩))
   · rfl
  unfold reads at key
  by_cases hop : (gateAt C n w).op = GateOp.not
  ·
   rw [if_pos hop] at key
   rw [hop]
   cases hin : (gateAt C n w).inputs with
   | nil => rfl
   | cons a l =>
    rw [hin] at key
    have := key a (by simp)
    simp only [GateOp.eval, List.map_cons, List.headD_cons, this]
  ·
   rw [if_neg hop] at key
   congr 1
   exact List.map_congr_left key
theorem mono0 (hg : GoodC C) : ∀ w, (∀ v ∈ desc C n w, ¬ isNot C n v) → ∀ f g : ℕ → Bool,
  (∀ i, f i = true → g i = true) → val C n w f = true → val C n w g = true := by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro hm f g hfg
  by_cases h1 : w < n
  ·
   rw [val_input C n w h1, val_input C n w h1]
   exact hfg w
  by_cases h2 : n + C.gates.length ≤ w
  ·
   rw [val_out C n w h2]
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
   ·
    rename_i hiw
    have hc : i ∈ ch C n w := mem_ch C n hn hj (by unfold reads; rw [if_neg hop]; exact hi) hiw
    apply ih i hiw _ f g hfg
    intro v hv
    exact hm v ((mem_desc C n w v).2 (Or.inr ⟨i, hc, hv⟩))
   · exact id
  rcases hg' with h | h <;> rw [h] <;>
   simp only [GateOp.eval, List.all_eq_true, List.any_eq_true, List.mem_map, id]
  ·
   rintro p b ⟨i, hi, rfl⟩
   exact key i hi (p _ ⟨i, hi, rfl⟩)
  ·
   rintro ⟨b, ⟨i, hi, rfl⟩, p⟩
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
  ·
   rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem c] at h2
   exact hmon _ (List.getElem_mem c) h2
  ·
   rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.2 (by omega)] at h2
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
  ·
   by_contra c
   rw [Bool.not_eq_false] at c
   have := mo (only u.val) (two u.val (k + w.val)) (fun i hi => by
    simp only [only, two, decide_eq_true_eq] at hi ⊢
    exact Or.inl hi) c
   rw [hrep] at this
   simp [Ne.symm hw] at this
  ·
   by_contra c
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
   ·
    have : val C (k + k) C.output (two u.val (k + u.val)) =
      val C (k + k) C.output (only (k + u.val)) := by
     apply dep0
     intro v hv _
     have : v ≠ u.val := fun d => c (e ▸ d ▸ hv)
     simp [two, only, this]
    rw [this, (fx u).2] at h1
    exact Bool.noConfusion h1
   ·
    have : val C (k + k) C.output (two u.val (k + u.val)) = val C (k + k) C.output (only u.val) := by
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
   ·
    intro hi
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
   ·
    have := (fx ⟨z - k, by omega⟩).2
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
 ·
  have h1 := h u (by omega)
  omega
 by_cases b : u' < k
 ·
  have h1 := h u' (by omega)
  omega
 omega
theorem cols_distinct (k : ℕ) (v v' : ℕ) (hv : v < k + 1) (hv' : v' < k + 1)
  (h : ∀ u < k + 2, (Qc k u v ↔ Qc k u v')) : v = v' := by
 unfold Qc at h
 by_contra c
 by_cases a : v < k
 ·
  have h1 := h v (by omega)
  omega
 ·
  have h1 := h v' (by omega)
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
 ·
  rw [h2, Finset.mem_singleton] at hνw
  exact absurd hνw.symm hne
 ·
  have key : ∀ a ∈ desc C n o, ∀ b ∈ desc C n o, a < w → Disjoint (desc C n a) (desc C n b) →
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
  ·
   refine key b hb a ha (by assumption) hd.symm (by rw [h, Finset.union_comm]) e ?_
   rcases hv with hv | hv
   · exact Or.inl fun f => (hv f).trans (Bool.and_comm _ _)
   · exact Or.inr fun f => (hv f).trans (Bool.or_comm _ _)
 ·
  have := huni w hw hN
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
  ·
   subst e
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
    ·
     rename_i d
     exact h2 i d hi
    · exact Bool.noConfusion hi
   intro h
   cases hg : val C n c g
   · rfl
   ·
    rw [mc hg] at h
    exact Bool.noConfusion h
  ·
   obtain ⟨a, ha, b, hb, haw, hνa, hνb, hbc, _, hv⟩ :=
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
    ·
     rename_i d
     exact h1 i (hbc i d) hi
    · exact Bool.noConfusion hi
   rcases hv with hv | hv <;> rw [hv, hv]
   ·
    simp only [Bool.and_eq_true]
    exact fun p => ⟨ia p.1, ib p.2⟩
   ·
    simp only [Bool.or_eq_true]
    exact fun p => p.imp ia ib
theorem bit : ∀ w ∈ desc C n o, ν ∈ desc C n w → ∀ f g : ℕ → Bool,
  (∀ i, i ∉ sup n (desc C n) c → f i = g i) → val C n c f = val C n c g →
  val C n w f = val C n w g := by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro hw hνw f g h1 h2
  by_cases e : w = ν
  ·
   subst e
   rw [hV, hV, h2]
  ·
   obtain ⟨a, ha, b, hb, haw, hνa, _, hbc, _, hv⟩ :=
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
  ·
   apply Finset.card_le_card
   intro i hi
   unfold leaves
   rw [Finset.mem_filter]
   rcases Finset.mem_union.1 hi with h | h
   · exact ⟨(hX i h).2, by have := (hX i h).1; omega⟩
   ·
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    exact ⟨(hY v hv).2, by have := (hY v hv).1; omega⟩
  ·
   rw [Finset.disjoint_left]
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
 ·
  exfalso
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
   ·
    obtain ⟨w, hw, hwu, _⟩ := avoid k (by omega) u u u u
    have := h1 w (by omega) w (by omega) (by unfold Qc; omega)
    unfold Qc at this
    omega
   ·
    have := h1 0 (by omega) 0 (by omega) (by unfold Qc; omega)
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
  ·
   intro u v
   change val C n o (two u.val (k + 2 + v.val)) = _
   have hu := u.isLt
   have hv := v.isLt
   rw [Bool.eq_iff_iff, hrep _ (by omega) _ (by omega), decide_eq_true_eq]
   unfold Qc
   simp only [ne_eq, Fin.ext_iff]
   omega
  ·
   intro u
   change val C n o (two u.val (k + 2 + k)) = true
   have hu := u.isLt
   rw [hrep _ (by omega) _ (by omega)]
   unfold Qc
   omega
  ·
   change val C n o (only (k + 2 + k)) = false
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
  ·
   have := hνn.1
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
   ·
    simp only [only, two, decide_eq_true_eq] at hj ⊢
    exact Or.inr hj
   ·
    simp only [only, two, decide_eq_true_eq] at h2 ⊢
    rcases h2 with e | e
    · exact absurd (e ▸ hj) hu
    · exact e
  have xneg : ∀ u v : ℕ, u ∈ sup n (desc C n) c → val C n o (two u (k + 2 + v)) = true →
    val C n o (only (k + 2 + v)) = true := by
   intro u v hu h
   refine pol _ _ (fun j hj h2 => ?_) (fun j _ h2 => ?_) h
   ·
    simp only [only, two, decide_eq_true_eq] at h2 ⊢
    rcases h2 with e | e
    · exact absurd (e ▸ hu) hj
    · exact e
   ·
    simp only [only, two, decide_eq_true_eq] at h2 ⊢
    exact Or.inr h2
  have ypos : ∀ u v : ℕ, k + 2 + v ∉ sup n (desc C n) c → val C n o (only u) = true →
    val C n o (two u (k + 2 + v)) = true := by
   intro u v hv h
   refine pol _ _ (fun j _ hj => ?_) (fun j hj h2 => ?_) h
   ·
    simp only [only, two, decide_eq_true_eq] at hj ⊢
    exact Or.inl hj
   ·
    simp only [only, two, decide_eq_true_eq] at h2 ⊢
    rcases h2 with e | e
    · exact e
    · exact absurd (e ▸ hj) hv
  have yneg : ∀ u v : ℕ, k + 2 + v ∈ sup n (desc C n) c → val C n o (two u (k + 2 + v)) = true →
    val C n o (only u) = true := by
   intro u v hv h
   refine pol _ _ (fun j hj h2 => ?_) (fun j _ h2 => ?_) h
   ·
    simp only [only, two, decide_eq_true_eq] at h2 ⊢
    rcases h2 with e | e
    · exact e
    · exact absurd (e ▸ hv) hj
   ·
    simp only [only, two, decide_eq_true_eq] at h2 ⊢
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
   ·
    obtain ⟨m, hm, hm'⟩ := h
    refine ⟨m, fun u hu hne => ?_⟩
    by_contra d
    exact hne (unx u m hu hm d hm')
   ·
    refine ⟨0, fun u hu _ => ?_⟩
    by_contra d
    exact h ⟨u, hu, d⟩
  have missy : ∃ m, ∀ v < k + 1, v ≠ m → k + 2 + v ∈ desc C n o := by
   by_cases h : ∃ m < k + 1, k + 2 + m ∉ desc C n o
   ·
    obtain ⟨m, hm, hm'⟩ := h
    refine ⟨m, fun v hv hne => ?_⟩
    by_contra d
    exact hne (uny v m hv hm d hm')
   ·
    refine ⟨0, fun v hv _ => ?_⟩
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
  ·
   have z0 : ∀ j < k + 1, val C n o (only (k + 2 + j)) = true := by
    intro j hj
    obtain ⟨w, hw, hwm, hwj, _⟩ := avoid k (by omega) mx j j j
    exact xneg w j (allx hpx w hw hwm) (r1 w j (by omega) hj (by unfold Qc; omega))
   have c0 : ∀ i < k + 2, i ≠ k + 1 → val C n o (only i) = true := by
    intro i hi hik
    obtain ⟨w, hw, hwm, hwi, _⟩ := avoid k (by omega) my i i i
    exact yneg i w (ally hpy w hw hwm) (r1 i w hi (by omega) (by unfold Qc; omega))
   rcases zform z hzo with hz | ⟨t, ht, rfl⟩
   ·
    by_cases d : z < k
    ·
     by_cases e : z = mx
     ·
      obtain ⟨w, hw, hwm, _⟩ := avoid k (by omega) mx mx mx mx
      exact samex z w d hw (by omega) hzc (allx hpx w hw hwm)
     · exact hzc (allx hpx z d e)
    by_cases e : z = k
    ·
     subst e
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
      ·
       have h1 : ∀ u < z + 2, u ∈ desc C n o := fun u hu => by
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
   ·
    by_cases d : t < k
    ·
     by_cases e : t = my
     ·
      obtain ⟨w, hw, hwm, _⟩ := avoid k (by omega) my my my my
      exact samey t w d hw (by omega) hzc (ally hpy w hw hwm)
     · exact hzc (ally hpy t d e)
    have et : t = k := by omega
    subst et
    have col : ∀ i < t + 2, (val C n o (only i) = true ↔ Qc t i t) := by
     intro i hi
     by_cases e : i = t + 1
     ·
      have hf : val C n o (only i) = false := by
       rw [Bool.eq_false_iff]
       intro h
       have a := ypos i t hzc h
       rw [e, rz t (by omega)] at a
       exact Bool.noConfusion a
      rw [hf]
      unfold Qc
      simp [e]
     ·
      rw [c0 i hi e]
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
  ·
   obtain ⟨a, ha, ham, _⟩ := avoid k (by omega) mx mx mx mx
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
     ·
      intro i hi
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
  ·
   obtain ⟨a, ha, ham, _⟩ := avoid k (by omega) my my my my
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
     ·
      intro i hi
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
  ·
   have xnc : ∀ j < k, j ∉ sup n (desc C n) c := nox hpx
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
    ·
     by_cases d : i < k
     · exact absurd hi (xnc i d)
     by_cases e : i = k
     · exact absurd (e ▸ hi) nk
     omega
    ·
     by_cases d : t < k
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
   ·
    obtain ⟨j, hj, hjm, hjm', _⟩ := avoid k (by omega) mx m m m
    have a := (mrow j (by omega)).2 (by unfold Qc; omega)
    rw [z0 j hj hjm] at a
    exact Bool.noConfusion a
   ·
    obtain ⟨j, hj, hjm, _⟩ := avoid k (by omega) mx mx mx mx
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
  ·
   have := allq mx (by omega)
   unfold Qc at this
   omega
  ·
   have := allq 0 (by omega)
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
  ·
   rintro ⟨h1, h2⟩
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
  ·
   rintro (rfl | ⟨u, _, rfl | rfl⟩)
   · exact ⟨xin _ (by omega) (by omega), by omega⟩
   ·
    have := u.isLt
    exact ⟨xin _ (by omega) (by omega), by omega⟩
   ·
    have := u.isLt
    exact ⟨yin _ this, by omega⟩
 have notk : k + 2 + k ∉ sup n (desc C n) c := notin _ (by omega) hmy'
 have zk : val C n c (only (k + 1)) = true := by
  have a := (G (k + 1) (by omega) k (by omega)).2 (by unfold Qc; omega)
  rwa [gdrop' _ _ notk] at a
 have core0 : ∀ i, i ≠ k + 1 → val C n c (only i) = false := by
  intro i hi
  by_cases d : i ∈ sup n (desc C n) c
  swap
  ·
   apply off H hcT cmon
   intro j hj
   have : j ≠ i := fun e => d (e ▸ hj)
   simp [only, this]
  rcases (hsupc i).1 d with e | ⟨u, _, e | e⟩
  · exact absurd e hi
  ·
   have hu := u.isLt
   rw [Bool.eq_false_iff]
   intro h
   obtain ⟨w, hw, hwu, _⟩ := avoid k (by omega) u.val u.val u.val u.val
   have := (G u.val (by omega) w (by omega)).1 (up1 _ _ (e ▸ h))
   apply this
   unfold Qc
   omega
  ·
   have hu := u.isLt
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
 ·
  simp only [blk, term, bcost, if_pos h]
  refine ⟨?_, by simp, by simp, ?_⟩
  ·
   rw [run_one]
   simp only [step]
   rw [getD_new _ _ rfl]
   simp [GateOp.eval, ← List.getD_eq_getElem?_getD, hf _ a1.1, hf _ a1.2]
  ·
   intro g hg
   rw [List.mem_singleton] at hg
   subst hg
   simp
 ·
  simp only [blk, term, bcost, if_neg h]
  refine ⟨?_, by simp, by simp, ?_⟩
  ·
   have s1 : step w ⟨GateOp.or, [b.1.val, nr + b.2.val]⟩ = w ++ [f b.1.val || f (nr + b.2.val)] := by
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
  ·
   intro g hg
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
   ·
    rw [run_append, run_append, run_one]
    change (step w2 ⟨GateOp.or, [r.2, s.2]⟩).getD (n + r.1.length + s.1.length) false = _
    simp only [step]
    rw [getD_new _ _ l2.symm]
    simp only [List.map_cons, List.map_nil]
    rw [keep]
    change GateOp.or.eval [w1.getD r.2 false, (run s.1 w1).getD s.2 false] = _
    rw [show w1.getD r.2 false = _ from h1, k1, List.any_cons (a := b)]
    simp [GateOp.eval, Bool.or_comm]
   ·
    simp only [List.length_append, List.length_singleton]
    omega
   ·
    rw [List.map_cons, List.sum_cons]
    simp only [List.length_append, List.length_singleton]
    omega
   ·
    intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact h4 g hg
    · exact k4 g hg
    ·
     subst hg
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
   ·
    rw [List.map_cons, List.sum_cons, h1, Finset.biUnion_insert, id,
     Finset.card_union_of_disjoint hdj, Finset.card_pair hab]
    simp only [bcost, if_neg hab]
    omega
   ·
    rw [List.any_cons, Bool.or_eq_true, h2, Finset.biUnion_insert, id]
    have e1 : insert ({a, b} : Finset (Fin k)) M = {{a, b}} ∪ M := Finset.insert_eq _ _
    rw [e1, Pr_union]
    apply or_congr _ Iff.rfl
    simp only [term, if_neg hab, Pr, Finset.mem_insert, Finset.mem_singleton, or_and_right,
     exists_or, exists_eq_left, forall_eq_or_imp, forall_eq, Bool.and_eq_true, Bool.or_eq_true]
    tauto
 obtain ⟨l, h1, h2⟩ := pairs M hM
 let R := Finset.univ \ M.biUnion id
 refine ⟨l ++ R.toList.map (fun u => (u, u)), ?_, fun f => ?_⟩
 ·
  have : (R.toList.map (fun u => (u, u))).map bcost = List.replicate R.card 2 := by
   rw [List.map_map, ← Finset.length_toList, ← List.map_const']
   apply List.map_congr_left
   intro u _
   simp [bcost]
  rw [List.map_append, List.sum_append, h1, this, List.sum_replicate, smul_eq_mul]
  have h3 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (M.biUnion id))
  rw [Finset.card_univ, Fintype.card_fin] at h3
  simp only [R]
  omega
 ·
  rw [List.any_append, Bool.or_eq_true, h2]
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
 ·
  intro i h1 h2
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
 ·
  intro i h1 h2
  have hi : i < a + b := by simpa [inp] using h2
  have key : (PEqualNP.Represents.oneEach u v).getD i false = two u.val (a + v.val) i := by
   unfold PEqualNP.Represents.oneEach two
   have hu := u.isLt
   have hv := v.isLt
   by_cases d : i < a
   ·
    rw [getD_app_left _ _ i d]
    rw [decide_eq_decide, Fin.ext_iff]
    simp only
    omega
   ·
    have e : i = a + (i - a) := by omega
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
 ·
  rintro (⟨w, _, h1, h2⟩ | ⟨e, he, h⟩)
  ·
   simp only [two, decide_eq_true_eq] at h1 h2
   have := w.isLt
   omega
  ·
   obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (hM.1 e he)
   have hne : a.val ≠ b.val := fun c => hab (Fin.ext c)
   have ha := a.isLt
   have hb := b.isLt
   simp only [two, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq] at h
   omega
 ·
  rintro ⟨h, hk⟩
  left
  refine ⟨⟨u, hk⟩, Finset.mem_univ _, by simp [two], by simp [two, h]⟩
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
 ·
  intro g hg
  have := h1 g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact this
 ·
  change gs.length + 1 ≤ 2 * k
  omega
 ·
  intro u v
  have hu := u.isLt
  rw [oneEach_inp, Bool.eq_iff_iff, ev, pr_point k k u.val v.val le_rfl hu M hM, decide_eq_true_eq]
  omega
 ·
  intro x y
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
 ·
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  simp only [C, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | rfl | rfl
  ·
   have := h1 g hg
   exact ⟨this.1.imp id Or.inl, this.2⟩
  · simp
  · simp
 ·
  change (gs ++ [_, _]).length ≤ 2 * k + 1
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega
 ·
  intro u v
  have hu := u.isLt
  have hv := v.isLt
  rw [oneEach_inp, Bool.eq_iff_iff, ev, pr_point k (k + 2) u.val v.val (by omega) hu M hM,
   decide_eq_true_eq]
  simp only [two, decide_eq_true_eq]
  omega
 ·
  intro x y
  have e := list_inp (List.ofFn x ++ List.ofFn y) n
   (by rw [List.length_append, List.length_ofFn, List.length_ofFn])
  conv_lhs => rw [e]
  exact ev _
def ends {k : Nat} (edge : Fin k × Fin k) : Finset (Fin k) := {edge.1, edge.2}
theorem ends_injective {k : Nat} (edge other : Fin k × Fin k)
  (ord : edge.1 < edge.2) (ord' : other.1 < other.2) (eq : ends edge = ends other) : edge = other := by
 have left : edge.1 ∈ ends other := eq ▸ Finset.mem_insert_self _ _
 have right : edge.2 ∈ ends other := eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
 simp only [ends, Finset.mem_insert, Finset.mem_singleton] at left right
 rcases left with left | left <;> rcases right with right | right
 · exact (ord.ne (left.trans right.symm)).elim
 · exact Prod.ext left right
 ·
  rw [left, right] at ord
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
 ·
  rintro ⟨key, hk, left | empty⟩
  ·
   have sub : key ⊆ ends edge := by
    intro v hv
    simpa only [ends, Finset.mem_insert, Finset.mem_singleton] using left v hv
   have eq : key = ends edge := Finset.eq_of_subset_of_card_le sub (by simp [ends, ord.ne, hm.1 key hk])
   exact eq ▸ hk
  ·
   obtain ⟨v, hv'⟩ := Finset.card_pos.mp (show 0 < key.card by rw [hm.1 key hk]; decide)
   exact False.elim (empty v hv')
 ·
  intro member
  exact ⟨_, member, Or.inl (by simp [ends])⟩
def active {k nr nc : Nat} (matching : Finset (Finset (Fin k)))
  (x : Fin nr → Bool) (y : Fin nc → Bool) : Prop :=
 Pr (fun w => w.val) (fun w => nr + w.val) Finset.univ matching
  (fun i => (List.ofFn x ++ List.ofFn y).getD i false)
theorem min_key_sorted {k : Nat} (key : Finset (Fin k)) (sz : key.card = 2) :
  ∃ edge : Fin k × Fin k, edge.1 < edge.2 ∧ ends edge = key := by
 obtain ⟨a, b, ne, rfl⟩ := Finset.card_eq_two.mp sz
 rcases lt_or_gt_of_ne ne with ord | ord
 · exact ⟨(a, b), ord, rfl⟩
 · exact ⟨(b, a), ord, Finset.pair_comm _ _⟩
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
end Obs

namespace TM
namespace Lib
abbrev CPTs (f:List Bool → List Bool):Prop:=PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f
end Lib
section
namespace Lib.Machines
open Turing
theorem d43 {σ : Type} (f : σ → Option σ) (n:ℕ) :
  (flip bind f)^[n] none=none:=by
 induction n with
 | zero=>rfl
 | succ n ih=>rw [Function.iterate_succ_apply];exact ih
theorem d59 {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
  (h:∀ c c',f c=some c' → g (emb c)=some (emb c')) :
  ∀ (n:ℕ) (a b : σ),(flip bind f)^[n] (some a)=some b →
   (flip bind g)^[n] (some (emb a))=some (emb b):=by
 intro n
 induction n with
 | zero =>
  intro a b hab
  have:a=b:=Option.some.inj hab
  rw [this];rfl
 | succ n ih =>
  intro a b hab
  rw [Function.iterate_succ_apply] at hab ⊢
  cases hfa:f a with
  | none =>
   have e:flip bind f (some a)=none:=hfa
   rw [e,d43] at hab
   exact absurd hab (by simp)
  | some c =>
   have e:flip bind f (some a)=some c:=hfa
   have e':flip bind g (some (emb a))=some (emb c):=h a c hfa
   rw [e] at hab
   rw [e']
   exact ih c b hab
section pushes
variable {K:Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
def pushes:TM2.Stmt Γ Λ σ → ℕ
 | .push _ _ q=>pushes q+1
 | .peek _ _ q=>pushes q
 | .pop _ _ q=>pushes q
 | .load _ q=>pushes q
 | .branch _ q₁ q₂=>max (pushes q₁) (pushes q₂)
 | .goto _=>0
 | .halt=>0
theorem d58 (q:TM2.Stmt Γ Λ σ) (v : σ) (S:∀ k,List (Γ k)) (k:K) :
  ((TM2.stepAux q v S).stk k).length ≤ (S k).length+pushes q:=by
 induction q generalizing v S with
 | push k' f q ih =>
  simp only [TM2.stepAux,pushes]
  refine (ih _ _).trans ?_
  by_cases h:k=k'
  ·
   subst h
   rw [Function.update_self,List.length_cons];omega
  · rw [Function.update_of_ne h];omega
 | peek k' f q ih=>exact ih _ _
 | pop k' f q ih =>
  simp only [TM2.stepAux,pushes]
  refine (ih _ _).trans ?_
  by_cases h:k=k'
  ·
   subst h
   rw [Function.update_self,List.length_tail];omega
  · rw [Function.update_of_ne h]
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂ =>
  simp only [TM2.stepAux,pushes]
  cases f v
  · exact (ih₂ v S).trans (by have:=le_max_right (pushes q₁) (pushes q₂);omega)
  · exact (ih₁ v S).trans (by have:=le_max_left (pushes q₁) (pushes q₂);omega)
 | goto f=>simp [TM2.stepAux,pushes]
 | halt=>simp [TM2.stepAux,pushes]
end pushes
noncomputable def maxPush (tm:FinTM2):ℕ :=
 (@Finset.univ tm.Λ tm.ΛFin).sup fun l=>pushes (tm.m l)
theorem d86 (tm:FinTM2) (c c':TM2.Cfg tm.Γ tm.Λ tm.σ)
  (h:TM2.step tm.m c=some c') (k:tm.K) :
  (c'.stk k).length ≤ (c.stk k).length+maxPush tm:=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l =>
  simp only [TM2.step,Option.some.injEq] at h
  subst h
  refine (d58 _ _ _ _).trans ?_
  have:pushes (tm.m l) ≤ maxPush tm :=
   Finset.le_sup (f:=fun l=>pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
  simpa using this
theorem d67 (tm:FinTM2) (k:tm.K) :
  ∀ (n:ℕ) (a b:TM2.Cfg tm.Γ tm.Λ tm.σ),
   (flip bind (TM2.step tm.m))^[n] (some a)=some b →
   (b.stk k).length ≤ (a.stk k).length+maxPush tm * n:=by
 intro n
 induction n with
 | zero =>
  intro a b hab
  have:a=b:=Option.some.inj hab
  rw [this];simp
 | succ n ih =>
  intro a b hab
  rw [Function.iterate_succ_apply] at hab
  cases hfa:TM2.step tm.m a with
  | none =>
   have e:flip bind (TM2.step tm.m) (some a)=none:=hfa
   rw [e,d43] at hab
   exact absurd hab (by simp)
  | some c =>
   have e:flip bind (TM2.step tm.m) (some a)=some c:=hfa
   rw [e] at hab
   have h1:=ih c b hab
   have h2:=d86 tm a c hfa k
   rw [Nat.mul_succ];omega
theorem d4 (tm:FinTM2) (s:List (tm.Γ tm.k₀)) :
  initList tm s =
   (⟨some tm.main,tm.initialState,Function.update (fun _=>[]) tm.k₀ s⟩ :
    TM2.Cfg tm.Γ tm.Λ tm.σ):=by
 unfold initList
 congr 1
 funext k
 by_cases h:k=tm.k₀
 · subst h;simp
 · simp [h]
theorem d5 (tm:FinTM2) (s:List (tm.Γ tm.k₁)) :
  haltList tm s =
   (⟨none,tm.initialState,Function.update (fun _=>[]) tm.k₁ s⟩ :
    TM2.Cfg tm.Γ tm.Λ tm.σ):=by
 unfold haltList
 congr 1
 funext k
 by_cases h:k=tm.k₁
 · subst h;simp
 · simp [h]
theorem d37 (p:Polynomial ℕ) {x y:ℕ} (h:x ≤ y):p.eval x ≤ p.eval y:=by
 induction p using Polynomial.induction_on' with
 | add p q hp hq =>
  rw [Polynomial.eval_add,Polynomial.eval_add];exact add_le_add hp hq
 | monomial d c =>
  rw [Polynomial.eval_monomial,Polynomial.eval_monomial]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
def d60:List Bool → TM2.Stmt (fun _:Unit=>Bool) Unit Bool
 | [] => .halt
 | a :: l => .push () (fun _=>a) (d60 l)
def d3 (l:List Bool):Unit → TM2.Stmt (fun _:Unit=>Bool) Unit Bool :=
 fun _ => .pop () (fun _ o=>o.isSome)
  (.branch (fun s=>s)
   (.load (fun _=>false) (.goto fun _=>()))
   (d60 l.reverse))
def d20 (l:List Bool):FinTM2 where
  K:=Unit
  k₀:=()
  k₁:=()
  Γ _:=Bool
  Λ := Unit
  main:=()
  σ := Bool
  initialState:=false
  m:=d3 l
abbrev CLCfg:Type:=TM2.Cfg (fun _:Unit=>Bool) Unit Bool
theorem d17 (S T:List Bool) :
  Function.update (fun _:Unit=>S) () T=fun _=>T:=by
 funext k
 simp
theorem d42 (l:List Bool) (v:Bool) (S:List Bool) :
  TM2.stepAux (d60 l) v (fun _:Unit=>S) =
   (⟨none,v,fun _=>l.reverse++S⟩:CLCfg):=by
 induction l generalizing S with
 | nil=>rfl
 | cons a l ih =>
  simp only [d60,TM2.stepAux]
  rw [d17,ih]
  simp
theorem d64 (l:List Bool) (x:Bool) (a:List Bool) :
  TM2.step (d3 l) (⟨some (),false,fun _=>x :: a⟩:CLCfg) =
   some ⟨some (),false,fun _=>a⟩:=by
 simp only [TM2.step,d3,TM2.stepAux]
 rw [d17]
 simp
theorem d76 (l:List Bool) :
  TM2.step (d3 l) (⟨some (),false,fun _=>[]⟩:CLCfg) =
   some ⟨none,false,fun _=>l⟩:=by
 simp only [TM2.step,d3,TM2.stepAux]
 rw [d17]
 simp only [List.head?_nil,Option.isSome_none,Bool.cond_false,List.tail_nil]
 rw [d42]
 simp
theorem d63 (l:List Bool) (a:List Bool) :
  (flip bind (TM2.step (d3 l)))^[a.length+1]
    (some (⟨some (),false,fun _=>a⟩:CLCfg)) =
   some ⟨none,false,fun _=>l⟩:=by
 induction a with
 | nil=>exact d76 l
 | cons x a ih =>
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (d3 l))
    (some (⟨some (),false,fun _=>x :: a⟩:CLCfg)) =
    some ⟨some (),false,fun _=>a⟩:=d64 l x a
  rw [e,ih]
theorem d75 (l:List Bool) (a:List Bool) :
  (flip bind (TM2.step (d3 l)))^[a.length+1]
   (some (initList (d20 l) a))=some (haltList (d20 l) l):=by
 refine (congrArg (fun c=>(flip bind (TM2.step (d3 l)))^[a.length+1]
  (some c)) (d4 (d20 l) a)).trans
  (Eq.trans ?_ (congrArg some (d5 (d20 l) l)).symm)
 show (flip bind (TM2.step (d3 l)))^[a.length+1]
  (some (⟨some (),false,Function.update (fun _=>[]) () a⟩:CLCfg)) =
  some (⟨none,false,Function.update (fun _=>[]) () l⟩:CLCfg)
 rw [d17,d17]
 exact d63 l a
theorem d11 (l:List Bool) :
    Nonempty (Turing.TM2ComputableInPolyTime (fun x:List Bool=>x)
      (fun x:List Bool=>x) (fun _:List Bool=>l)) :=
  ⟨{
    tm:=d20 l
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.X+1
    outputsFun:=fun a =>
      { steps:=a.length+1
        evals_in_steps:=by
          have hm:∀ l:List Bool,List.map (Equiv.refl Bool).invFun l=l:=fun l=>by simp
          exact (congrArg (fun x=>(flip bind (TM2.step (d3 l)))^[a.length+1]
            (some (initList (d20 l) x))) (hm a)).trans
            ((d75 l a).trans
              (congrArg (fun x=>some (haltList (d20 l) x)) (hm l).symm))
        steps_le_m:=by simp } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
section update
variable {ι : Type} [DecidableEq ι] {β : ι → Type}
theorem d51 (E:∀ i,β i) {a b c : ι} (hab:a≠b) (hac:a≠c)
  (x x' : β a) (y : β b) (z : β c) :
  Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x' =
   Function.update (Function.update (Function.update E a x') b y) c z:=by
 rw [Function.update_comm hac.symm,Function.update_comm hab.symm,Function.update_idem]
theorem d50 (E:∀ i,β i) {a b c : ι} (hbc:b≠c)
  (x : β a) (y y' : β b) (z : β c) :
  Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y' =
   Function.update (Function.update (Function.update E a x) b y') c z:=by
 rw [Function.update_comm hbc.symm,Function.update_idem]
end update
variable (M1 M2:FinTM2)
abbrev CK:Type:=Option (M1.K ⊕ M2.K)
abbrev CΓ : CK M1 M2 → Type
 | none=>M2.Γ M2.k₀
 | some (Sum.inl k)=>M1.Γ k
 | some (Sum.inr k)=>M2.Γ k
abbrev CΛ : Type:=M1.Λ ⊕ M2.Λ ⊕ Bool
abbrev Cσ : Type:=M1.σ × M2.σ × Option (M2.Γ M2.k₀)
variable {M1 M2}
def tr1:TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | .push k f q => .push (some (Sum.inl k)) (fun s=>f s.1) (tr1 q)
 | .peek k f q => .peek (some (Sum.inl k)) (fun s o=>(f s.1 o,s.2)) (tr1 q)
 | .pop k f q => .pop (some (Sum.inl k)) (fun s o=>(f s.1 o,s.2)) (tr1 q)
 | .load a q => .load (fun s=>(a s.1,s.2)) (tr1 q)
 | .branch f q₁ q₂ => .branch (fun s=>f s.1) (tr1 q₁) (tr1 q₂)
 | .goto f => .goto (fun s=>Sum.inl (f s.1))
 | .halt => .goto (fun _=>Sum.inr (Sum.inr false))
def tr2:TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | .push k f q => .push (some (Sum.inr k)) (fun s=>f s.2.1) (tr2 q)
 | .peek k f q => .peek (some (Sum.inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
 | .pop k f q => .pop (some (Sum.inr k)) (fun s o=>(s.1,f s.2.1 o,s.2.2)) (tr2 q)
 | .load a q => .load (fun s=>(s.1,a s.2.1,s.2.2)) (tr2 q)
 | .branch f q₁ q₂ => .branch (fun s=>f s.2.1) (tr2 q₁) (tr2 q₂)
 | .goto f => .goto (fun s=>Sum.inr (Sum.inl (f s.2.1)))
 | .halt => .halt
variable (M1 M2)
def tA (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) :
  Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | none => .goto (fun _=>Sum.inr (Sum.inl M2.main))
 | some d =>
  .pop (some (Sum.inl M1.k₁)) (fun s o=>(s.1,s.2.1,o.map φ))
   (.branch (fun s=>s.2.2.isSome)
    (.push none (fun s=>s.2.2.getD d) (.goto fun _=>Sum.inr (Sum.inr false)))
    (.goto fun _=>Sum.inr (Sum.inr true)))
def tB:Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | none => .goto (fun _=>Sum.inr (Sum.inl M2.main))
 | some d =>
  .pop none (fun s o=>(s.1,s.2.1,o))
   (.branch (fun s=>s.2.2.isSome)
    (.push (some (Sum.inr M2.k₀)) (fun s=>s.2.2.getD d)
     (.goto fun _=>Sum.inr (Sum.inr true)))
    (.goto fun _=>Sum.inr (Sum.inl M2.main)))
def prog (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)) :
  CΛ M1 M2 → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
 | Sum.inl l=>tr1 (M1.m l)
 | Sum.inr (Sum.inl l)=>tr2 (M2.m l)
 | Sum.inr (Sum.inr false)=>tA M1 M2 φ d
 | Sum.inr (Sum.inr true)=>tB M1 M2 d
def comp (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀)):FinTM2 :=
  haveI:=M1.kFin
  haveI:=M2.kFin
  haveI:=M1.ΛFin
  haveI:=M2.ΛFin
  haveI:=M1.σFin
  haveI:=M2.σFin
  haveI:=M2.Γk₀Fin
  { K:=CK M1 M2
    k₀:=some (Sum.inl M1.k₀)
    k₁:=some (Sum.inr M2.k₁)
    Γ := CΓ M1 M2
    Λ := CΛ M1 M2
    main:=Sum.inl M1.main
    σ := Cσ M1 M2
    initialState:=(M1.initialState,M2.initialState,none)
    Γk₀Fin:=M1.Γk₀Fin
    m:=prog M1 M2 φ d }
variable {M1 M2}
def d49 (S:∀ k,List (M1.Γ k)):∀ k,List (CΓ M1 M2 k)
 | none=>[]
 | some (Sum.inl k)=>S k
 | some (Sum.inr _)=>[]
def d48 (S:∀ k,List (M2.Γ k)):∀ k,List (CΓ M1 M2 k)
 | none=>[]
 | some (Sum.inl _)=>[]
 | some (Sum.inr k)=>S k
theorem d13 (S:∀ k,List (M1.Γ k)) (k:M1.K) (x:List (M1.Γ k)) :
  (d49 (Function.update S k x):∀ k,List (CΓ M1 M2 k)) =
   Function.update (d49 S) (some (Sum.inl k)) x:=by
 funext j
 rcases j with _ | j | j
 · rw [Function.update_of_ne (by simp)];rfl
 ·
  by_cases h:j=k
  ·
   subst h
   rw [Function.update_self]
   show Function.update S j x j=x
   rw [Function.update_self]
  ·
   rw [Function.update_of_ne (by simpa using h)]
   show Function.update S k x j=S j
   rw [Function.update_of_ne h]
 · rw [Function.update_of_ne (by simp)];rfl
theorem d12 (S:∀ k,List (M2.Γ k)) (k:M2.K) (x:List (M2.Γ k)) :
  (d48 (Function.update S k x):∀ k,List (CΓ M1 M2 k)) =
   Function.update (d48 S) (some (Sum.inr k)) x:=by
 funext j
 rcases j with _ | j | j
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 ·
  by_cases h:j=k
  ·
   subst h
   rw [Function.update_self]
   show Function.update S j x j=x
   rw [Function.update_self]
  ·
   rw [Function.update_of_ne (by simpa using h)]
   show Function.update S k x j=S j
   rw [Function.update_of_ne h]
theorem d56 :
  (d49 (fun _=>[]):∀ k,List (CΓ M1 M2 k))=fun _=>[]:=by
 funext j;rcases j with _ | j | j <;> rfl
theorem d55 :
  (d48 (fun _=>[]):∀ k,List (CΓ M1 M2 k))=fun _=>[]:=by
 funext j;rcases j with _ | j | j <;> rfl
def emb1 (w:M2.σ × Option (M2.Γ M2.k₀)) (c:TM2.Cfg M1.Γ M1.Λ M1.σ) :
  TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
 ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl),(c.var,w),d49 c.stk⟩
def emb2 (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c:TM2.Cfg M2.Γ M2.Λ M2.σ) :
  TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
 ⟨c.l.map (fun l=>Sum.inr (Sum.inl l)),(u,c.var,b),d48 c.stk⟩
theorem sim1 (w:M2.σ × Option (M2.Γ M2.k₀)) (q:TM2.Stmt M1.Γ M1.Λ M1.σ) (v:M1.σ)
  (S:∀ k,List (M1.Γ k)) :
  TM2.stepAux (tr1 q) ((v,w):Cσ M1 M2) (d49 S)=emb1 w (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih =>
  have:=ih v (Function.update S k (f v :: S k))
  rw [d13] at this
  exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih =>
  have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
  rw [d13] at this
  exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂ =>
  simp only [tr1,TM2.stepAux]
  cases f v
  · exact ih₂ v S
  · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
theorem sim2 (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (q:TM2.Stmt M2.Γ M2.Λ M2.σ) (v:M2.σ)
  (S:∀ k,List (M2.Γ k)) :
  TM2.stepAux (tr2 q) ((u,v,b):Cσ M1 M2) (d48 S)=emb2 u b (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih =>
  have:=ih v (Function.update S k (f v :: S k))
  rw [d12] at this
  exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih =>
  have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
  rw [d12] at this
  exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂ =>
  simp only [tr2,TM2.stepAux]
  cases f v
  · exact ih₂ v S
  · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
variable (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d:Option (M2.Γ M2.k₀))
theorem step1 (w:M2.σ × Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M1.Γ M1.Λ M1.σ)
  (h:TM2.step M1.m c=some c') :
  TM2.step (prog M1 M2 φ d) (emb1 w c)=some (emb1 w c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l =>
  simp only [TM2.step,Option.some.injEq] at h
  subst h
  exact congrArg some (sim1 w (M1.m l) v S)
theorem step2 (u:M1.σ) (b:Option (M2.Γ M2.k₀)) (c c':TM2.Cfg M2.Γ M2.Λ M2.σ)
  (h:TM2.step M2.m c=some c') :
  TM2.step (prog M1 M2 φ d) (emb2 u b c)=some (emb2 u b c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l =>
  simp only [TM2.step,Option.some.injEq] at h
  subst h
  exact congrArg some (sim2 u b (M2.m l) v S)
def st (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)):∀ k,List (CΓ M1 M2 k) :=
 Function.update (Function.update (Function.update (fun _=>[])
  (some (Sum.inl M1.k₁)) l) none t) (some (Sum.inr M2.k₀)) u
theorem st_fst (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
  (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁))=l:=by
 unfold st
 rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp),Function.update_self]
theorem st_snd (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
  (st l t u:∀ k,List (CΓ M1 M2 k)) none=t:=by
 unfold st
 rw [Function.update_of_ne (by simp),Function.update_self]
theorem st_thd (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
  (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))=u:=by
 unfold st
 rw [Function.update_self]
theorem d66 (l l':List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
  Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l'=st l' t u :=
 d51 _ (by simp) (by simp) _ _ _ _
theorem d41 (l:List (M1.Γ M1.k₁)) (t t' u:List (M2.Γ M2.k₀)) :
  Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) none t'=st l t' u :=
 d50 _ (by simp) _ _ _ _
theorem d90 (l:List (M1.Γ M1.k₁)) (t u u':List (M2.Γ M2.k₀)) :
  Function.update (st l t u:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u'=st l t u' :=
 Function.update_idem _ _ _
theorem d79 (l:List (M1.Γ M1.k₁)) :
  (st l [] []:∀ k,List (CΓ M1 M2 k)) =
   Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l:=by
 unfold st
 rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rw [Function.update_of_ne (by simp)]
 · rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp)]
theorem st_end (u:List (M2.Γ M2.k₀)) :
  (st [] [] u:∀ k,List (CΓ M1 M2 k)) =
   Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u:=by
 unfold st
 congr 1
 rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rfl
 · rw [Function.update_of_ne (by simp)]
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
variable {M1 M2:FinTM2} (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀)
abbrev CCfg (M1 M2:FinTM2):Type:=TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
theorem d89 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
  (x:M1.Γ M1.k₁) (l:List (M1.Γ M1.k₁)) (t u:List (M2.Γ M2.k₀)) :
  TM2.step (prog M1 M2 φ (some dd))
    (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st (x :: l) t u⟩:CCfg M1 M2) =
   some ⟨some (Sum.inr (Sum.inr false)),(v1,v2,some (φ x)),st l (φ x :: t) u⟩:=by
 simp only [TM2.step,prog,tA,TM2.stepAux]
 rw [st_fst]
 simp only [List.head?_cons,List.tail_cons,Option.map_some,Option.isSome_some,Bool.cond_true,
  Option.getD_some]
 rw [d66,st_snd,d41]
theorem d105 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
  (t u:List (M2.Γ M2.k₀)) :
  TM2.step (prog M1 M2 φ (some dd))
    (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st [] t u⟩:CCfg M1 M2) =
   some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,none),st [] t u⟩:=by
 simp only [TM2.step,prog,tA,TM2.stepAux]
 rw [st_fst]
 simp only [List.head?_nil,List.tail_nil,Option.map_none,Option.isSome_none,Bool.cond_false]
 rw [d66]
theorem d88 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
  (x:M2.Γ M2.k₀) (t u:List (M2.Γ M2.k₀)) :
  TM2.step (prog M1 M2 φ (some dd))
    (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] (x :: t) u⟩:CCfg M1 M2) =
   some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,some x),st [] t (x :: u)⟩:=by
 simp only [TM2.step,prog,tB,TM2.stepAux]
 rw [st_snd]
 simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some]
 rw [d41,st_thd,d90]
theorem d104 (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (b:Option (M2.Γ M2.k₀))
  (u:List (M2.Γ M2.k₀)) :
  TM2.step (prog M1 M2 φ (some dd))
    (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] [] u⟩:CCfg M1 M2) =
   some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),st [] [] u⟩:=by
 simp only [TM2.step,prog,tB,TM2.stepAux]
 rw [st_snd]
 simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
 rw [d41]
theorem loopA (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) (u:List (M2.Γ M2.k₀)) :
  ∀ (l:List (M1.Γ M1.k₁)) (t:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
   (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[l.length+1]
     (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st l t u⟩:CCfg M1 M2)) =
    some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,none),st [] ((l.map φ).reverse++t) u⟩:=by
 intro l
 induction l with
 | nil=>intro t b;exact d105 φ dd v1 v2 b t u
 | cons x l ih =>
  intro t b
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (prog M1 M2 φ (some dd)))
    (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,b),st (x :: l) t u⟩:CCfg M1 M2)) =
    some ⟨some (Sum.inr (Sum.inr false)),(v1,v2,some (φ x)),st l (φ x :: t) u⟩ :=
   d89 φ dd v1 v2 b x l t u
  rw [e,ih]
  simp
theorem loopB (dd:M2.Γ M2.k₀) (v1:M1.σ) (v2:M2.σ) :
  ∀ (t u:List (M2.Γ M2.k₀)) (b:Option (M2.Γ M2.k₀)),
   (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[t.length+1]
     (some (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] t u⟩:CCfg M1 M2)) =
    some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),st [] [] (t.reverse++u)⟩:=by
 intro t
 induction t with
 | nil=>intro u b;exact d104 φ dd v1 v2 b u
 | cons x t ih =>
  intro u b
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (prog M1 M2 φ (some dd)))
    (some (⟨some (Sum.inr (Sum.inr true)),(v1,v2,b),st [] (x :: t) u⟩:CCfg M1 M2)) =
    some ⟨some (Sum.inr (Sum.inr true)),(v1,v2,some x),st [] t (x :: u)⟩ :=
   d88 φ dd v1 v2 b x t u
  rw [e,ih]
  simp
theorem d120 (d:Option (M2.Γ M2.k₀)) (hd:d=none → IsEmpty (M2.Γ M2.k₀))
  (v1:M1.σ) (v2:M2.σ) (o:List (M1.Γ M1.k₁)) :
  ∃ n,n ≤ 2 * o.length+2 ∧
   (flip bind (TM2.step (prog M1 M2 φ d)))^[n]
     (some (⟨some (Sum.inr (Sum.inr false)),(v1,v2,none),
      Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
      CCfg M1 M2)) =
    some ⟨some (Sum.inr (Sum.inl M2.main)),(v1,v2,none),
     Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))
      (o.map φ)⟩:=by
 cases d with
 | none =>
  have:=hd rfl
  have ho:o=[]:=by
   cases o with
   | nil=>rfl
   | cons x _=>exact (IsEmpty.false (φ x)).elim
  subst ho
  refine ⟨1,by omega,?_⟩
  show some _=some _
  simp only [prog,tA,TM2.stepAux,List.map_nil]
  rw [Function.update_eq_self_iff.mpr rfl,Function.update_eq_self_iff.mpr rfl]
 | some dd =>
  refine ⟨((o.map φ).reverse++[]).length+1+(o.length+1),by simp;omega,?_⟩
  rw [Function.iterate_add_apply,← d79,loopA,loopB,← st_end]
  simp
theorem d114 (d:Option (M2.Γ M2.k₀)) (i:List (M1.Γ M1.k₀)) :
  emb1 (M2.initialState,none) (initList M1 i)=initList (comp M1 M2 φ d) i:=by
 rw [d4]
 refine Eq.trans ?_ (d4 (comp M1 M2 φ d) i).symm
 show (⟨_,_,d49 _⟩:CCfg M1 M2)=_
 rw [d13,d56]
 rfl
theorem d115 (w:M2.σ × Option (M2.Γ M2.k₀)) (o:List (M1.Γ M1.k₁)) :
  emb1 w (haltList M1 o) =
   (⟨some (Sum.inr (Sum.inr false)),(M1.initialState,w),
    Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
    CCfg M1 M2):=by
 rw [d5]
 show (⟨_,_,d49 _⟩:CCfg M1 M2)=_
 rw [d13,d56]
 rfl
theorem d112 (u:M1.σ) (i:List (M2.Γ M2.k₀)) :
  emb2 u none (initList M2 i) =
   (⟨some (Sum.inr (Sum.inl M2.main)),(u,M2.initialState,none),
    Function.update (fun _=>[]:∀ k,List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) i⟩ :
    CCfg M1 M2):=by
 rw [d4]
 show (⟨_,_,d48 _⟩:CCfg M1 M2)=_
 rw [d12,d55]
 rfl
theorem d113 (d:Option (M2.Γ M2.k₀)) (o:List (M2.Γ M2.k₁)) :
  emb2 M1.initialState none (haltList M2 o)=haltList (comp M1 M2 φ d) o:=by
 rw [d5]
 refine Eq.trans ?_ (d5 (comp M1 M2 φ d) o).symm
 show (⟨_,_,d48 _⟩:CCfg M1 M2)=_
 rw [d12,d55]
 rfl
theorem d136 (d:Option (M2.Γ M2.k₀)) (hd:d=none → IsEmpty (M2.Γ M2.k₀))
  (i:List (M1.Γ M1.k₀)) (o1:List (M1.Γ M1.k₁)) (o2:List (M2.Γ M2.k₁)) (s1 s2:ℕ)
  (h1:(flip bind (TM2.step M1.m))^[s1] (some (initList M1 i))=some (haltList M1 o1))
  (h2:(flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ))) =
   some (haltList M2 o2)) :
  ∃ n,n ≤ s1+(2 * o1.length+2)+s2∧o1.length ≤ i.length+maxPush M1 * s1 ∧
   (flip bind (TM2.step (prog M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i)) =
    some (haltList (comp M1 M2 φ d) o2):=by
 have p1:=d59 (TM2.step M1.m) (TM2.step (prog M1 M2 φ d))
  (emb1 (M2.initialState,none)) (step1 φ d _) s1 _ _ h1
 rw [d114 φ d,d115] at p1
 obtain ⟨nt,hnt,pt⟩:=d120 φ d hd M1.initialState M2.initialState o1
 have p2:=d59 (TM2.step M2.m) (TM2.step (prog M1 M2 φ d))
  (emb2 M1.initialState none) (step2 φ d _ _) s2 _ _ h2
 rw [d112,d113 φ d] at p2
 refine ⟨s2+(nt+s1),by omega,?_,?_⟩
 ·
  have:=d67 M1 M1.k₁ s1 _ _ h1
  rw [d5,d4] at this
  simp only [Function.update_self] at this
  refine this.trans (Nat.add_le_add_right ?_ _)
  by_cases h:M1.k₁=M1.k₀
  · rw [h,Function.update_self]
  · rw [Function.update_of_ne h];simp
 ·
  rw [Function.iterate_add_apply,Function.iterate_add_apply,p1,pt,p2]
  rfl
theorem d77 {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ) (c1:TM2ComputableInPolyTime ea eb f)
    (c2:TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (fun a=>g (f a))):=by
  classical
  let φ : c1.tm.Γ c1.tm.k₁ → c2.tm.Γ c2.tm.k₀ :=
    fun x=>c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d:Option (c2.tm.Γ c2.tm.k₀) :=
    if h:Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd:d=none → IsEmpty (c2.tm.Γ c2.tm.k₀):=by
    intro h
    by_cases hn:Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d,hn] at h
    · exact not_nonempty_iff.mp hn
  let T:Polynomial ℕ :=
    c1.time+(Polynomial.C 2 * (Polynomial.X+Polynomial.C (maxPush c1.tm) * c1.time) +
      Polynomial.C 2) +
      c2.time.comp (Polynomial.X+Polynomial.C (maxPush c1.tm) * c1.time)
  have key:∀ a,∃ n,n ≤ T.eval (ea a).length ∧
      (flip bind (TM2.step (prog c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))):=by
    intro a
    have r1:=c1.outputsFun a
    have r2:=c2.outputsFun (f a)
    have hφ : (List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)):=by
      rw [List.map_map]
      refine List.map_congr_left fun y _ => ?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y))=_
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2:(flip bind (TM2.step c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))):=by
      rw [hφ];exact r2.evals_in_steps
    obtain ⟨n,hn,hlen,hrun⟩:=d136 φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n,hn.trans ?_,hrun⟩
    have b1:=r1.steps_le_m
    have b2:=r2.steps_le_m
    simp only [List.length_map] at hlen
    have hmul:maxPush c1.tm * r1.steps ≤
        maxPush c1.tm * Polynomial.eval (ea a).length c1.time:=Nat.mul_le_mul_left _ b1
    have b3:Polynomial.eval (eb (f a)).length c2.time ≤
        Polynomial.eval ((ea a).length+maxPush c1.tm * Polynomial.eval (ea a).length c1.time)
          c2.time:=d37 _ (by omega)
    simp only [T,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_comp,List.length_map]
    omega
  exact ⟨{
    tm:=comp c1.tm c2.tm φ d
    inputAlphabet:=c1.inputAlphabet
    outputAlphabet:=c2.outputAlphabet
    time:=T
    outputsFun:=fun a =>
      ⟨⟨Classical.choose (key a),(Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
variable {Γ₀ Γ₁:Type}
abbrev FΓ (Γ₀ Γ₁:Type):Option Bool → Type
 | some false => Γ₀
 | none=>Option Γ₀
 | some true => Γ₁
def fmProg (φ : Γ₀ → Option Γ₁) (d:Option Γ₁):Bool → TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
 | false =>
  .pop (some false) (fun _ o=>o)
   (.branch (fun s=>s.isSome)
    (.push none (fun s=>s) (.goto fun _=>false))
    (.goto fun _=>true))
 | true =>
  .pop none (fun _ o=>o.join)
   (.branch (fun s=>s.isSome)
    (.branch (fun s=>(s.bind φ).isSome)
     (match d with
      | some dd => .push (some true) (fun s=>(s.bind φ).getD dd) (.goto fun _=>true)
      | none => .goto fun _=>true)
     (.goto fun _=>true))
    .halt)
def fm [Fintype Γ₀] (φ : Γ₀ → Option Γ₁) (d:Option Γ₁):FinTM2 where
  K:=Option Bool
  k₀:=some false
  k₁:=some true
  Γ := FΓ Γ₀ Γ₁
  Λ := Bool
  main:=false
  σ := Option Γ₀
  initialState:=none
  Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
  m:=fmProg φ d
def fst3 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁):∀ k,List (FΓ Γ₀ Γ₁ k) :=
 Function.update (Function.update (Function.update (fun _=>[])
  (some false) l) none t) (some true) u
theorem d99 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
  fst3 l t u (some false)=l:=by
 unfold fst3
 rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp),Function.update_self]
theorem d81 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
  fst3 l t u none=t:=by
 unfold fst3
 rw [Function.update_of_ne (by simp),Function.update_self]
theorem d131 (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
  fst3 l t u (some true)=u:=by
 unfold fst3
 rw [Function.update_self]
theorem d47 (l l':List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
  Function.update (fst3 l t u) (some false) l'=fst3 l' t u :=
 d51 _ (by simp) (by simp) _ _ _ _
theorem d27 (l:List Γ₀) (t t':List (Option Γ₀)) (u:List Γ₁) :
  Function.update (fst3 l t u) none t'=fst3 l t' u :=
 d50 _ (by simp) _ _ _ _
theorem d82 (l:List Γ₀) (t:List (Option Γ₀)) (u u':List Γ₁) :
  Function.update (fst3 l t u) (some true) u'=fst3 l t u' :=
 Function.update_idem _ _ _
theorem d98 (l:List Γ₀) :
  (fst3 l [] []:∀ k,List (FΓ Γ₀ Γ₁ k)) =
   Function.update (fun _=>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some false) l:=by
 unfold fst3
 rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rw [Function.update_of_ne (by simp)]
 · rw [Function.update_of_ne (by simp),Function.update_of_ne (by simp)]
theorem d132 (u:List Γ₁) :
  (fst3 [] [] u:∀ k,List (FΓ Γ₀ Γ₁ k)) =
   Function.update (fun _=>[]:∀ k,List (FΓ Γ₀ Γ₁ k)) (some true) u:=by
 unfold fst3
 congr 1
 rw [Function.update_eq_self_iff.mpr,Function.update_eq_self_iff.mpr]
 · rfl
 · rw [Function.update_of_ne (by simp)]
abbrev FCfg (Γ₀ Γ₁:Type):Type:=TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
variable (φ : Γ₀ → Option Γ₁) (d:Option Γ₁)
theorem d134 (b:Option Γ₀) (x : Γ₀) (l:List Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
  TM2.step (fmProg φ d) (⟨some false,b,fst3 (x :: l) t u⟩:FCfg Γ₀ Γ₁) =
   some ⟨some false,some x,fst3 l (some x :: t) u⟩:=by
 simp only [TM2.step,fmProg,TM2.stepAux]
 rw [d99]
 simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true]
 rw [d47,d81,d27]
theorem d164 (b:Option Γ₀) (t:List (Option Γ₀)) (u:List Γ₁) :
  TM2.step (fmProg φ d) (⟨some false,b,fst3 [] t u⟩:FCfg Γ₀ Γ₁) =
   some ⟨some true,none,fst3 [] t u⟩:=by
 simp only [TM2.step,fmProg,TM2.stepAux]
 rw [d99]
 simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
 rw [d47]
theorem d133 (hd:d=none → ∀ x,φ x=none) (b:Option Γ₀) (x : Γ₀)
  (t:List (Option Γ₀)) (u:List Γ₁) :
  TM2.step (fmProg φ d) (⟨some true,b,fst3 [] (some x :: t) u⟩:FCfg Γ₀ Γ₁) =
   some ⟨some true,some x,fst3 [] t ((φ x).toList++u)⟩:=by
 simp only [TM2.step,fmProg,TM2.stepAux]
 rw [d81]
 simp only [List.head?_cons,List.tail_cons,Option.join_some,Option.isSome_some,
  Bool.cond_true,Option.bind_some]
 rw [d27]
 cases hφ : φ x with
 | none=>simp
 | some y =>
  cases d with
  | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
  | some dd =>
   simp only [Option.isSome_some,Bool.cond_true,TM2.stepAux,
    Option.toList_some,List.singleton_append]
   rw [d131,d82]
   simp [hφ]
theorem d163 (b:Option Γ₀) (u:List Γ₁) :
  TM2.step (fmProg φ d) (⟨some true,b,fst3 [] [] u⟩:FCfg Γ₀ Γ₁) =
   some ⟨none,none,fst3 [] [] u⟩:=by
 simp only [TM2.step,fmProg,TM2.stepAux]
 rw [d81]
 simp only [List.head?_nil,List.tail_nil,Option.join_none,Option.isSome_none,
  Bool.cond_false]
 rw [d27]
theorem d162 (u:List Γ₁) :
  ∀ (l:List Γ₀) (t:List (Option Γ₀)) (b:Option Γ₀),
   (flip bind (TM2.step (fmProg φ d)))^[l.length+1]
     (some (⟨some false,b,fst3 l t u⟩:FCfg Γ₀ Γ₁)) =
    some ⟨some true,none,fst3 [] (l.reverse.map some++t) u⟩:=by
 intro l
 induction l with
 | nil=>intro t b;exact d164 φ d b t u
 | cons x l ih =>
  intro t b
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (fmProg φ d))
    (some (⟨some false,b,fst3 (x :: l) t u⟩:FCfg Γ₀ Γ₁)) =
    some ⟨some false,some x,fst3 l (some x :: t) u⟩:=d134 φ d b x l t u
  rw [e,ih]
  simp
theorem d161 (hd:d=none → ∀ x,φ x=none) :
  ∀ (t:List Γ₀) (u:List Γ₁) (b:Option Γ₀),
   (flip bind (TM2.step (fmProg φ d)))^[t.length+1]
     (some (⟨some true,b,fst3 [] (t.map some) u⟩:FCfg Γ₀ Γ₁)) =
    some ⟨none,none,fst3 [] [] ((t.filterMap φ).reverse++u)⟩:=by
 intro t
 induction t with
 | nil=>intro u b;exact d163 φ d b u
 | cons x t ih =>
  intro u b
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (fmProg φ d))
    (some (⟨some true,b,fst3 [] ((x :: t).map some) u⟩:FCfg Γ₀ Γ₁)) =
    some ⟨some true,some x,fst3 [] (t.map some) ((φ x).toList++u)⟩ :=
   d133 φ d hd b x (t.map some) u
  rw [e,ih]
  cases hφ : φ x <;> simp [hφ]
theorem fm_run [Fintype Γ₀] (hd:d=none → ∀ x,φ x=none) (l:List Γ₀) :
  (flip bind (TM2.step (fmProg φ d)))^[l.length+1+(l.length+1)]
   (some (initList (fm φ d) l))=some (haltList (fm φ d) (l.filterMap φ)):=by
 refine (congrArg (fun c=>(flip bind (TM2.step (fmProg φ d)))^[l.length+1+(l.length+1)]
  (some c)) (d4 (fm φ d) l)).trans
  (Eq.trans ?_ (congrArg some (d5 (fm φ d) (l.filterMap φ))).symm)
 show (flip bind (TM2.step (fmProg φ d)))^[l.length+1+(l.length+1)]
  (some (⟨some false,none,Function.update (fun _=>[]) (some false) l⟩:FCfg Γ₀ Γ₁)) =
  some (⟨none,none,Function.update (fun _=>[]) (some true) (l.filterMap φ)⟩:FCfg Γ₀ Γ₁)
 rw [Function.iterate_add_apply,← d98,d162,← d132]
 have:=d161 φ d hd l.reverse [] none
 rw [List.length_reverse] at this
 simpa [List.filterMap_reverse] using this
theorem d7 {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ : αΓ → Option βΓ)
    (h:∀ a,eb (f a)=(ea a).filterMap φ) :
    Nonempty (TM2ComputableInPolyTime ea eb f):=by
  classical
  let d:Option βΓ := if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:d=none → ∀ x,φ x=none:=by
    intro hdn x
    by_cases hn:Nonempty βΓ
    · simp [d,hn] at hdn
    · cases hφ : φ x with
      | none=>rfl
      | some y=>exact absurd ⟨y⟩ hn
  exact ⟨{
    tm:=fm φ d
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.C 2 * Polynomial.X+Polynomial.C 2
    outputsFun:=fun a =>
      { steps:=(ea a).length+1+((ea a).length+1)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          have:=fm_run φ d hd (ea a)
          exact (congrArg (fun l=>(flip bind (TM2.step (fmProg φ d)))^[(ea a).length+1 +
            ((ea a).length+1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l=>some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:=by
          simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
inductive TPK:Type
 | inp | t1 | t2 | t3 | out
 deriving DecidableEq
instance:Fintype TPK :=
 Fintype.ofList [.inp,.t1,.t2,.t3,.out] (fun x=>by cases x <;> simp)
inductive TPL:Type
 | a | b | c | e
 deriving DecidableEq
instance:Fintype TPL :=
 Fintype.ofList [.a,.b,.c,.e] (fun x=>by cases x <;> simp)
variable {Γ₀ Γ₁:Type}
abbrev TPΓ (Γ₀ Γ₁:Type):TPK → Type
 | .inp => Γ₀
 | .t1=>Option Γ₀
 | .t2=>Option Γ₀
 | .t3=>Option Γ₀
 | .out => Γ₁
def d52 (φ : Γ₀ → Option Γ₁) (d:Option Γ₁) (lbl:TPL) :
  TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
 .branch (fun s=>(s.bind φ).isSome)
  (match d with
   | some dd => .push .out (fun s=>(s.bind φ).getD dd) (.goto fun _=>lbl)
   | none => .goto fun _=>lbl)
  (.goto fun _=>lbl)
def tpProg (φ₁ φ₂ : Γ₀ → Option Γ₁) (d:Option Γ₁) :
  TPL → TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
 | .a =>
  .pop .inp (fun _ o=>o)
   (.branch (fun s=>s.isSome)
    (.push .t1 (fun s=>s) (.goto fun _ => .a))
    (.goto fun _ => .b))
 | .b =>
  .pop .t1 (fun _ o=>o.join)
   (.branch (fun s=>s.isSome)
    (.push .t2 (fun s=>s) (d52 φ₂ d .b))
    (.goto fun _ => .c))
 | .c =>
  .pop .t2 (fun _ o=>o.join)
   (.branch (fun s=>s.isSome)
    (.push .t3 (fun s=>s) (.goto fun _ => .c))
    (.goto fun _ => .e))
 | .e =>
  .pop .t3 (fun _ o=>o.join)
   (.branch (fun s=>s.isSome)
    (d52 φ₁ d .e)
    .halt)
def tp [Fintype Γ₀] (φ₁ φ₂ : Γ₀ → Option Γ₁) (d:Option Γ₁):FinTM2 where
  K:=TPK
  k₀ := .inp
  k₁ := .out
  Γ := TPΓ Γ₀ Γ₁
  Λ := TPL
  main := .a
  σ := Option Γ₀
  initialState:=none
  Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
  m:=tpProg φ₁ φ₂ d
def st5 (l:List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁):∀ k,List (TPΓ Γ₀ Γ₁ k)
 | .inp=>l
 | .t1=>a
 | .t2=>b
 | .t3=>c
 | .out=>u
theorem d54 (l l':List Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁) :
  Function.update (st5 l a b c u) .inp l'=st5 l' a b c u:=by
 funext k;cases k <;> simp [st5]
theorem d31 (l:List Γ₀) (a a' b c:List (Option Γ₀)) (u:List Γ₁) :
  Function.update (st5 l a b c u) .t1 a'=st5 l a' b c u:=by
 funext k;cases k <;> simp [st5]
theorem d30 (l:List Γ₀) (a b b' c:List (Option Γ₀)) (u:List Γ₁) :
  Function.update (st5 l a b c u) .t2 b'=st5 l a b' c u:=by
 funext k;cases k <;> simp [st5]
theorem d29 (l:List Γ₀) (a b c c':List (Option Γ₀)) (u:List Γ₁) :
  Function.update (st5 l a b c u) .t3 c'=st5 l a b c' u:=by
 funext k;cases k <;> simp [st5]
theorem d53 (l:List Γ₀) (a b c:List (Option Γ₀)) (u u':List Γ₁) :
  Function.update (st5 l a b c u) .out u'=st5 l a b c u':=by
 funext k;cases k <;> simp [st5]
theorem d106 (l:List Γ₀) :
  (st5 l [] [] [] []:∀ k,List (TPΓ Γ₀ Γ₁ k)) =
   Function.update (fun _=>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .inp l:=by
 funext k;cases k <;> simp [st5]
theorem d151 (u:List Γ₁) :
  (st5 [] [] [] [] u:∀ k,List (TPΓ Γ₀ Γ₁ k)) =
   Function.update (fun _=>[]:∀ k,List (TPΓ Γ₀ Γ₁ k)) .out u:=by
 funext k;cases k <;> simp [st5]
abbrev TPCfg (Γ₀ Γ₁:Type):Type:=TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
variable (φ₁ φ₂ : Γ₀ → Option Γ₁) (d:Option Γ₁)
theorem d127 (s:Option Γ₀) (x : Γ₀) (l:List Γ₀) (a b c:List (Option Γ₀))
  (u:List Γ₁) :
  TM2.step (tpProg φ₁ φ₂ d) (⟨some .a,s,st5 (x :: l) a b c u⟩:TPCfg Γ₀ Γ₁) =
   some ⟨some .a,some x,st5 l (some x :: a) b c u⟩:=by
 simp [TM2.step,tpProg,TM2.stepAux,st5,d54,d31]
theorem d150 (s:Option Γ₀) (a b c:List (Option Γ₀)) (u:List Γ₁) :
  TM2.step (tpProg φ₁ φ₂ d) (⟨some .a,s,st5 [] a b c u⟩:TPCfg Γ₀ Γ₁) =
   some ⟨some .b,none,st5 [] a b c u⟩:=by
 simp [TM2.step,tpProg,TM2.stepAux,st5,d54]
theorem d126 (hd:d=none → ∀ x,φ₂ x=none) (s:Option Γ₀) (x : Γ₀)
  (a b c:List (Option Γ₀)) (u:List Γ₁) :
  TM2.step (tpProg φ₁ φ₂ d) (⟨some .b,s,st5 [] (some x :: a) b c u⟩:TPCfg Γ₀ Γ₁) =
   some ⟨some .b,some x,st5 [] a (some x :: b) c ((φ₂ x).toList++u)⟩:=by
 cases hφ : φ₂ x with
 | none =>
  cases d <;>
   simp [TM2.step,tpProg,d52,TM2.stepAux,st5,d31,d30,hφ]
 | some y =>
  cases d with
  | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
  | some dd =>
   simp [TM2.step,tpProg,d52,TM2.stepAux,st5,d31,d30,
    d53,hφ]
theorem d149 (s:Option Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁) :
  TM2.step (tpProg φ₁ φ₂ d) (⟨some .b,s,st5 [] [] b c u⟩:TPCfg Γ₀ Γ₁) =
   some ⟨some .c,none,st5 [] [] b c u⟩:=by
 simp [TM2.step,tpProg,TM2.stepAux,st5,d31]
theorem d125 (s:Option Γ₀) (x : Γ₀) (b c:List (Option Γ₀)) (u:List Γ₁) :
  TM2.step (tpProg φ₁ φ₂ d) (⟨some .c,s,st5 [] [] (some x :: b) c u⟩:TPCfg Γ₀ Γ₁) =
   some ⟨some .c,some x,st5 [] [] b (some x :: c) u⟩:=by
 simp [TM2.step,tpProg,TM2.stepAux,st5,d30,d29]
theorem d148 (s:Option Γ₀) (c:List (Option Γ₀)) (u:List Γ₁) :
  TM2.step (tpProg φ₁ φ₂ d) (⟨some .c,s,st5 [] [] [] c u⟩:TPCfg Γ₀ Γ₁) =
   some ⟨some .e,none,st5 [] [] [] c u⟩:=by
 simp [TM2.step,tpProg,TM2.stepAux,st5,d30]
theorem d124 (hd:d=none → ∀ x,φ₁ x=none) (s:Option Γ₀) (x : Γ₀)
  (c:List (Option Γ₀)) (u:List Γ₁) :
  TM2.step (tpProg φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] (some x :: c) u⟩:TPCfg Γ₀ Γ₁) =
   some ⟨some .e,some x,st5 [] [] [] c ((φ₁ x).toList++u)⟩:=by
 cases hφ : φ₁ x with
 | none =>
  cases d <;>
   simp [TM2.step,tpProg,d52,TM2.stepAux,st5,d29,hφ]
 | some y =>
  cases d with
  | none=>rw [hd rfl x] at hφ;exact absurd hφ (by simp)
  | some dd =>
   simp [TM2.step,tpProg,d52,TM2.stepAux,st5,d29,d53,hφ]
theorem d147 (s:Option Γ₀) (u:List Γ₁) :
  TM2.step (tpProg φ₁ φ₂ d) (⟨some .e,s,st5 [] [] [] [] u⟩:TPCfg Γ₀ Γ₁) =
   some ⟨none,none,st5 [] [] [] [] u⟩:=by
 simp [TM2.step,tpProg,TM2.stepAux,st5,d29]
theorem d146 (b c:List (Option Γ₀)) (u:List Γ₁) :
  ∀ (l:List Γ₀) (a:List (Option Γ₀)) (s:Option Γ₀),
   (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
     (some (⟨some .a,s,st5 l a b c u⟩:TPCfg Γ₀ Γ₁)) =
    some ⟨some .b,none,st5 [] (l.reverse.map some++a) b c u⟩:=by
 intro l
 induction l with
 | nil=>intro a s;exact d150 φ₁ φ₂ d s a b c u
 | cons x l ih =>
  intro a s
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (tpProg φ₁ φ₂ d))
    (some (⟨some .a,s,st5 (x :: l) a b c u⟩:TPCfg Γ₀ Γ₁)) =
    some ⟨some .a,some x,st5 l (some x :: a) b c u⟩:=d127 φ₁ φ₂ d s x l a b c u
  rw [e,ih]
  simp
theorem d145 (hd:d=none → ∀ x,φ₂ x=none) (c:List (Option Γ₀)) :
  ∀ (t:List Γ₀) (b:List (Option Γ₀)) (u:List Γ₁) (s:Option Γ₀),
   (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length+1]
     (some (⟨some .b,s,st5 [] (t.map some) b c u⟩:TPCfg Γ₀ Γ₁)) =
    some ⟨some .c,none,
     st5 [] [] (t.reverse.map some++b) c ((t.filterMap φ₂).reverse++u)⟩:=by
 intro t
 induction t with
 | nil=>intro b u s;exact d149 φ₁ φ₂ d s b c u
 | cons x t ih =>
  intro b u s
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (tpProg φ₁ φ₂ d))
    (some (⟨some .b,s,st5 [] ((x :: t).map some) b c u⟩:TPCfg Γ₀ Γ₁)) =
    some ⟨some .b,some x,st5 [] (t.map some) (some x :: b) c ((φ₂ x).toList++u)⟩ :=
   d126 φ₁ φ₂ d hd s x (t.map some) b c u
  rw [e,ih]
  cases hφ : φ₂ x <;> simp [hφ]
theorem d144 (u:List Γ₁) :
  ∀ (t:List Γ₀) (c:List (Option Γ₀)) (s:Option Γ₀),
   (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length+1]
     (some (⟨some .c,s,st5 [] [] (t.map some) c u⟩:TPCfg Γ₀ Γ₁)) =
    some ⟨some .e,none,st5 [] [] [] (t.reverse.map some++c) u⟩:=by
 intro t
 induction t with
 | nil=>intro c s;exact d148 φ₁ φ₂ d s c u
 | cons x t ih =>
  intro c s
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (tpProg φ₁ φ₂ d))
    (some (⟨some .c,s,st5 [] [] ((x :: t).map some) c u⟩:TPCfg Γ₀ Γ₁)) =
    some ⟨some .c,some x,st5 [] [] (t.map some) (some x :: c) u⟩ :=
   d125 φ₁ φ₂ d s x (t.map some) c u
  rw [e,ih]
  simp
theorem d143 (hd:d=none → ∀ x,φ₁ x=none) :
  ∀ (t:List Γ₀) (u:List Γ₁) (s:Option Γ₀),
   (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length+1]
     (some (⟨some .e,s,st5 [] [] [] (t.map some) u⟩:TPCfg Γ₀ Γ₁)) =
    some ⟨none,none,st5 [] [] [] [] ((t.filterMap φ₁).reverse++u)⟩:=by
 intro t
 induction t with
 | nil=>intro u s;exact d147 φ₁ φ₂ d s u
 | cons x t ih =>
  intro u s
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (tpProg φ₁ φ₂ d))
    (some (⟨some .e,s,st5 [] [] [] ((x :: t).map some) u⟩:TPCfg Γ₀ Γ₁)) =
    some ⟨some .e,some x,st5 [] [] [] (t.map some) ((φ₁ x).toList++u)⟩ :=
   d124 φ₁ φ₂ d hd s x (t.map some) u
  rw [e,ih]
  cases hφ : φ₁ x <;> simp [hφ]
theorem tp_run [Fintype Γ₀] (hd₁:d=none → ∀ x,φ₁ x=none)
  (hd₂:d=none → ∀ x,φ₂ x=none) (l:List Γ₀) :
  (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1) +
    (l.length+1)]
    (some (initList (tp φ₁ φ₂ d) l)) =
   some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁++l.filterMap φ₂)):=by
 refine (congrArg (fun c=>(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1 +
  (l.length+1)+(l.length+1)+(l.length+1)]
  (some c)) (d4 (tp φ₁ φ₂ d) l)).trans
  (Eq.trans ?_ (congrArg some
   (d5 (tp φ₁ φ₂ d) (l.filterMap φ₁++l.filterMap φ₂))).symm)
 show (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1+(l.length+1)+(l.length+1) +
   (l.length+1)]
  (some (⟨some .a,none,Function.update (fun _=>[]) .inp l⟩:TPCfg Γ₀ Γ₁)) =
  some (⟨none,none,Function.update (fun _=>[]) .out
   (l.filterMap φ₁++l.filterMap φ₂)⟩:TPCfg Γ₀ Γ₁)
 have hA:(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
   (some (⟨some .a,none,st5 l [] [] [] []⟩:TPCfg Γ₀ Γ₁)) =
   some ⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:=by
  simpa using d146 φ₁ φ₂ d [] [] [] l [] none
 have hB:(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
   (some (⟨some .b,none,st5 [] (l.reverse.map some) [] [] []⟩:TPCfg Γ₀ Γ₁)) =
   some ⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:=by
  have:=d145 φ₁ φ₂ d hd₂ [] l.reverse [] [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this
 have hC:(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
   (some (⟨some .c,none,st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩:TPCfg Γ₀ Γ₁)) =
   some ⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩:=by
  simpa using d144 φ₁ φ₂ d (l.filterMap φ₂) l [] none
 have hE:(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length+1]
   (some (⟨some .e,none,st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ :
    TPCfg Γ₀ Γ₁)) =
   some ⟨none,none,st5 [] [] [] [] (l.filterMap φ₁++l.filterMap φ₂)⟩:=by
  have:=d143 φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this
 rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
  ← d106,hA,hB,hC,hE,d151]
theorem d10 {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ₁ φ₂ : αΓ → Option βΓ)
    (h:∀ a,eb (f a)=(ea a).filterMap φ₁++(ea a).filterMap φ₂) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=by
  classical
  let d:Option βΓ := if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:∀ φ : αΓ → Option βΓ,d=none → ∀ x,φ x=none:=by
    intro φ hdn x
    by_cases hn:Nonempty βΓ
    · simp [d,hn] at hdn
    · cases hφ : φ x with
      | none=>rfl
      | some y=>exact absurd ⟨y⟩ hn
  exact ⟨{
    tm:=tp φ₁ φ₂ d
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.C 4 * Polynomial.X+Polynomial.C 4
    outputsFun:=fun a =>
      { steps:=(ea a).length+1+((ea a).length+1)+((ea a).length+1) +
          ((ea a).length+1)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          have:=tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
          exact (congrArg (fun l=>(flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[(ea a).length+1 +
            ((ea a).length+1)+((ea a).length+1)+((ea a).length+1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l=>some (haltList (tp φ₁ φ₂ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:=by
          simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
inductive FX
 | I | W | T | O
 deriving DecidableEq
instance:Fintype FX :=
 Fintype.ofList [FX.I,FX.W,FX.T,FX.O] (fun x=>by cases x <;> simp)
inductive FL
 | l1 | l2 | l3 | l4 | l5
 deriving DecidableEq
instance:Fintype FL :=
 Fintype.ofList [FL.l1,FL.l2,FL.l3,FL.l4,FL.l5] (fun x=>by cases x <;> simp)
variable (M:FinTM2)
abbrev FstΓ : M.K ⊕ FX → Type
 | Sum.inl k=>M.Γ k
 | Sum.inr FX.I=>Bool ⊕ Bool
 | Sum.inr FX.W=>Bool
 | Sum.inr FX.T=>Bool
 | Sum.inr FX.O=>Bool ⊕ Bool
abbrev FstΛ : Type:=M.Λ ⊕ FL
abbrev Fstσ : Type:=M.σ × Option (Bool ⊕ Bool)
def bit:Option (Bool ⊕ Bool) → Bool
 | none=>false
 | some (Sum.inl b)=>b
 | some (Sum.inr b)=>b
def isFst:Option (Bool ⊕ Bool) → Bool
 | some (Sum.inl _)=>true
 | _=>false
variable {M}
def trF:TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
 | .push k f q => .push (Sum.inl k) (fun s=>f s.1) (trF q)
 | .peek k f q => .peek (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trF q)
 | .pop k f q => .pop (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trF q)
 | .load a q => .load (fun s=>(a s.1,s.2)) (trF q)
 | .branch f q₁ q₂ => .branch (fun s=>f s.1) (trF q₁) (trF q₂)
 | .goto f => .goto (fun s=>Sum.inl (f s.1))
 | .halt => .goto (fun _=>Sum.inr FL.l3)
variable (M)
def d0 (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool) :
  FstΛ M → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
 | Sum.inl l=>trF (M.m l)
 | Sum.inr FL.l1 =>
  .pop (Sum.inr FX.I) (fun s o=>(s.1,o))
   (.branch (fun s=>s.2.isSome)
    (.branch (fun s=>isFst s.2)
     (.push (Sum.inr FX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr FL.l1))
     (.push (Sum.inr FX.W) (fun s=>bit s.2) (.goto fun _=>Sum.inr FL.l1)))
    (.goto fun _=>Sum.inr FL.l2))
 | Sum.inr FL.l2 =>
  .pop (Sum.inr FX.T) (fun s o=>(s.1,o.map Sum.inl))
   (.branch (fun s=>s.2.isSome)
    (.push (Sum.inl M.k₀) (fun s=>e₀ (bit s.2)) (.goto fun _=>Sum.inr FL.l2))
    (.goto fun _=>Sum.inl M.main))
 | Sum.inr FL.l3 =>
  .pop (Sum.inr FX.W) (fun s o=>(s.1,o.map Sum.inl))
   (.branch (fun s=>s.2.isSome)
    (.push (Sum.inr FX.O) (fun s=>Sum.inr (bit s.2)) (.goto fun _=>Sum.inr FL.l3))
    (.goto fun _=>Sum.inr FL.l4))
 | Sum.inr FL.l4 =>
  .pop (Sum.inl M.k₁) (fun s o=>(s.1,o.map fun y=>Sum.inl (e₁ y)))
   (.branch (fun s=>s.2.isSome)
    (.push (Sum.inr FX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr FL.l4))
    (.goto fun _=>Sum.inr FL.l5))
 | Sum.inr FL.l5 =>
  .pop (Sum.inr FX.T) (fun s o=>(s.1,o.map Sum.inl))
   (.branch (fun s=>s.2.isSome)
    (.push (Sum.inr FX.O) (fun s=>Sum.inl (bit s.2)) (.goto fun _=>Sum.inr FL.l5))
    .halt)
def firstM (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool):FinTM2 :=
  haveI:=M.kFin
  haveI:=M.ΛFin
  haveI:=M.σFin
  { K:=M.K ⊕ FX
    k₀:=Sum.inr FX.I
    k₁:=Sum.inr FX.O
    Γ := FstΓ M
    Λ := FstΛ M
    main:=Sum.inr FL.l1
    σ := Fstσ M
    initialState:=(M.initialState,none)
    Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
    m:=d0 M e₀ e₁ }
variable {M}
def fstk (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
  (o:List (Bool ⊕ Bool)):∀ k,List (FstΓ M k)
 | Sum.inl k=>S k
 | Sum.inr FX.I=>i
 | Sum.inr FX.W=>w
 | Sum.inr FX.T=>t
 | Sum.inr FX.O=>o
section fstk
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
 (o:List (Bool ⊕ Bool))
theorem d23 (k:M.K) (x:List (M.Γ k)) :
  Function.update (fstk S i w t o) (Sum.inl k) x=fstk (Function.update S k x) i w t o:=by
 funext j
 rcases j with j | j
 ·
  by_cases h:j=k
  ·
   subst h
   rw [Function.update_self]
   show x=Function.update S j x j
   rw [Function.update_self]
  ·
   rw [Function.update_of_ne (by simpa using h)]
   show S j=Function.update S k x j
   rw [Function.update_of_ne h]
 · rw [Function.update_of_ne (by simp)];cases j <;> rfl
theorem d33 (i':List (Bool ⊕ Bool)) :
  Function.update (fstk S i w t o) (Sum.inr FX.I) i'=fstk S i' w t o:=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
theorem d45 (w':List Bool) :
  Function.update (fstk S i w t o) (Sum.inr FX.W) w'=fstk S i w' t o:=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
theorem d18 (t':List Bool) :
  Function.update (fstk S i w t o) (Sum.inr FX.T) t'=fstk S i w t' o:=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
 · rw [Function.update_of_ne (by simp)];rfl
theorem d46 (o':List (Bool ⊕ Bool)) :
  Function.update (fstk S i w t o) (Sum.inr FX.O) o'=fstk S i w t o':=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
end fstk
abbrev FCfg1 (M:FinTM2):Type:=TM2.Cfg (FstΓ M) (FstΛ M) (Fstσ M)
def embF (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
  (o:List (Bool ⊕ Bool)) (c:TM2.Cfg M.Γ M.Λ M.σ):FCfg1 M :=
 ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl),(c.var,b),fstk c.stk i w t o⟩
theorem simF (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
  (o:List (Bool ⊕ Bool)) (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)) :
  TM2.stepAux (trF q) ((v,b):Fstσ M) (fstk S i w t o) =
   embF b i w t o (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih =>
  have:=ih v (Function.update S k (f v :: S k))
  rw [← d23] at this
  exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih =>
  have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
  rw [← d23] at this
  exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂ =>
  simp only [trF,TM2.stepAux]
  cases f v
  · exact ih₂ v S
  · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
theorem stepF (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool) (b:Option (Bool ⊕ Bool))
  (i:List (Bool ⊕ Bool)) (w t:List Bool) (o:List (Bool ⊕ Bool))
  (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c') :
  TM2.step (d0 M e₀ e₁) (embF b i w t o c)=some (embF b i w t o c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l =>
  simp only [TM2.step,Option.some.injEq] at h
  subst h
  exact congrArg some (simF b i w t o (M.m l) v S)
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
theorem d6 {σ : Type} (f : σ → Option σ) {a b:ℕ} {x y z : σ}
  (h₁:(flip bind f)^[a] (some x)=some y) (h₂:(flip bind f)^[b] (some y)=some z) :
  (flip bind f)^[b+a] (some x)=some z:=by
 rw [Function.iterate_add_apply,h₁,h₂]
variable {M:FinTM2} (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool)
section fstk
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
 (o:List (Bool ⊕ Bool))
@[simp] theorem fstk_M (k:M.K):fstk S i w t o (Sum.inl k)=S k:=rfl
@[simp] theorem fstk_I:fstk S i w t o (Sum.inr FX.I)=i:=rfl
@[simp] theorem fstk_W:fstk S i w t o (Sum.inr FX.W)=w:=rfl
@[simp] theorem fstk_T:fstk S i w t o (Sum.inr FX.T)=t:=rfl
@[simp] theorem fstk_O:fstk S i w t o (Sum.inr FX.O)=o:=rfl
end fstk
variable (v:M.σ) (S:∀ k,List (M.Γ k)) (w:List Bool) (o:List (Bool ⊕ Bool))
theorem f1_inl (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:List Bool) :
  TM2.step (d0 M e₀ e₁)
    (⟨some (Sum.inr FL.l1),(v,b),fstk S (Sum.inl a :: i) w t o⟩:FCfg1 M) =
   some ⟨some (Sum.inr FL.l1),(v,some (Sum.inl a)),fstk S i w (a :: t) o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d33,d18,isFst,bit]
theorem f1_inr (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool)) (t:List Bool) :
  TM2.step (d0 M e₀ e₁)
    (⟨some (Sum.inr FL.l1),(v,b),fstk S (Sum.inr a :: i) w t o⟩:FCfg1 M) =
   some ⟨some (Sum.inr FL.l1),(v,some (Sum.inr a)),fstk S i (a :: w) t o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d33,d45,isFst,bit]
theorem f1_nil (b:Option (Bool ⊕ Bool)) (t:List Bool) :
  TM2.step (d0 M e₀ e₁)
    (⟨some (Sum.inr FL.l1),(v,b),fstk S [] w t o⟩:FCfg1 M) =
   some ⟨some (Sum.inr FL.l2),(v,none),fstk S [] w t o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d33]
theorem loop1:∀ (i:List (Bool ⊕ Bool)) (w t:List Bool) (b:Option (Bool ⊕ Bool)),
  (flip bind (TM2.step (d0 M e₀ e₁)))^[i.length+1]
    (some (⟨some (Sum.inr FL.l1),(v,b),fstk S i w t o⟩:FCfg1 M)) =
   some ⟨some (Sum.inr FL.l2),(v,none),
    fstk S [] ((i.filterMap Sum.getRight?).reverse++w)
     ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
 intro i
 induction i with
 | nil=>intro w t b;exact f1_nil e₀ e₁ v S w o b t
 | cons x i ih =>
  intro w t b
  rw [List.length_cons,Function.iterate_succ_apply]
  cases x with
  | inl a =>
   have e:flip bind (TM2.step (d0 M e₀ e₁))
     (some (⟨some (Sum.inr FL.l1),(v,b),fstk S (Sum.inl a :: i) w t o⟩:FCfg1 M)) =
     some ⟨some (Sum.inr FL.l1),(v,some (Sum.inl a)),fstk S i w (a :: t) o⟩ :=
    f1_inl e₀ e₁ v S w o b a i t
   rw [e,ih];simp [List.filterMap_cons]
  | inr a =>
   have e:flip bind (TM2.step (d0 M e₀ e₁))
     (some (⟨some (Sum.inr FL.l1),(v,b),fstk S (Sum.inr a :: i) w t o⟩:FCfg1 M)) =
     some ⟨some (Sum.inr FL.l1),(v,some (Sum.inr a)),fstk S i (a :: w) t o⟩ :=
    f1_inr e₀ e₁ v S w o b a i t
   rw [e,ih];simp [List.filterMap_cons]
theorem d168 (b:Option (Bool ⊕ Bool)) (a:Bool) (t:List Bool) :
  TM2.step (d0 M e₀ e₁)
    (⟨some (Sum.inr FL.l2),(v,b),fstk S [] w (a :: t) o⟩:FCfg1 M) =
   some ⟨some (Sum.inr FL.l2),(v,some (Sum.inl a)),
    fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d18,d23,bit]
theorem f2_nil (b:Option (Bool ⊕ Bool)) :
  TM2.step (d0 M e₀ e₁)
    (⟨some (Sum.inr FL.l2),(v,b),fstk S [] w [] o⟩:FCfg1 M) =
   some ⟨some (Sum.inl M.main),(v,none),fstk S [] w [] o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d18]
theorem loop2:∀ (t:List Bool) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
  (flip bind (TM2.step (d0 M e₀ e₁)))^[t.length+1]
    (some (⟨some (Sum.inr FL.l2),(v,b),fstk S [] w t o⟩:FCfg1 M)) =
   some ⟨some (Sum.inl M.main),(v,none),
    fstk (Function.update S M.k₀ (t.reverse.map e₀++S M.k₀)) [] w [] o⟩:=by
 intro t
 induction t with
 | nil =>
  intro S b
  have:Function.update S M.k₀ (([]:List Bool).reverse.map e₀++S M.k₀)=S:=by simp
  rw [this]
  exact f2_nil e₀ e₁ v S w o b
 | cons a t ih =>
  intro S b
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (d0 M e₀ e₁))
    (some (⟨some (Sum.inr FL.l2),(v,b),fstk S [] w (a :: t) o⟩:FCfg1 M)) =
    some ⟨some (Sum.inr FL.l2),(v,some (Sum.inl a)),
     fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩:=d168 e₀ e₁ v S w o b a t
  rw [e,ih];simp
theorem d167 (b:Option (Bool ⊕ Bool)) (a:Bool) (w:List Bool) :
  TM2.step (d0 M e₀ e₁)
    (⟨some (Sum.inr FL.l3),(v,b),fstk S [] (a :: w) [] o⟩:FCfg1 M) =
   some ⟨some (Sum.inr FL.l3),(v,some (Sum.inl a)),fstk S [] w [] (Sum.inr a :: o)⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d45,d46,bit]
theorem f3_nil (b:Option (Bool ⊕ Bool)) :
  TM2.step (d0 M e₀ e₁)
    (⟨some (Sum.inr FL.l3),(v,b),fstk S [] [] [] o⟩:FCfg1 M) =
   some ⟨some (Sum.inr FL.l4),(v,none),fstk S [] [] [] o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d45]
theorem loop3:∀ (w:List Bool) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
  (flip bind (TM2.step (d0 M e₀ e₁)))^[w.length+1]
    (some (⟨some (Sum.inr FL.l3),(v,b),fstk S [] w [] o⟩:FCfg1 M)) =
   some ⟨some (Sum.inr FL.l4),(v,none),fstk S [] [] [] (w.reverse.map Sum.inr++o)⟩:=by
 intro w
 induction w with
 | nil=>intro o b;exact f3_nil e₀ e₁ v S o b
 | cons a w ih =>
  intro o b
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (d0 M e₀ e₁))
    (some (⟨some (Sum.inr FL.l3),(v,b),fstk S [] (a :: w) [] o⟩:FCfg1 M)) =
    some ⟨some (Sum.inr FL.l3),(v,some (Sum.inl a)),fstk S [] w [] (Sum.inr a :: o)⟩ :=
   d167 e₀ e₁ v S o b a w
  rw [e,ih];simp
theorem d166 (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁)) (t:List Bool) :
  TM2.step (d0 M e₀ e₁)
    (⟨some (Sum.inr FL.l4),(v,b),fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
     FCfg1 M) =
   some ⟨some (Sum.inr FL.l4),(v,some (Sum.inl (e₁ y))),
    fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d18,d23,bit]
theorem f4_nil (b:Option (Bool ⊕ Bool)) (t:List Bool) :
  TM2.step (d0 M e₀ e₁)
    (⟨some (Sum.inr FL.l4),(v,b),fstk (Function.update S M.k₁ []) [] [] t o⟩:FCfg1 M) =
   some ⟨some (Sum.inr FL.l5),(v,none),fstk (Function.update S M.k₁ []) [] [] t o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d23]
theorem loop4:∀ (m:List (M.Γ M.k₁)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
  (flip bind (TM2.step (d0 M e₀ e₁)))^[m.length+1]
    (some (⟨some (Sum.inr FL.l4),(v,b),fstk (Function.update S M.k₁ m) [] [] t o⟩ :
     FCfg1 M)) =
   some ⟨some (Sum.inr FL.l5),(v,none),
    fstk (Function.update S M.k₁ []) [] [] (m.reverse.map e₁++t) o⟩:=by
 intro m
 induction m with
 | nil=>intro t b;exact f4_nil e₀ e₁ v S o b t
 | cons y m ih =>
  intro t b
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (d0 M e₀ e₁))
    (some (⟨some (Sum.inr FL.l4),(v,b),fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
     FCfg1 M)) =
    some ⟨some (Sum.inr FL.l4),(v,some (Sum.inl (e₁ y))),
     fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩:=d166 e₀ e₁ v S o b y m t
  rw [e,ih];simp
theorem d165 (b:Option (Bool ⊕ Bool)) (a:Bool) (t:List Bool) :
  TM2.step (d0 M e₀ e₁)
    (⟨some (Sum.inr FL.l5),(v,b),fstk S [] [] (a :: t) o⟩:FCfg1 M) =
   some ⟨some (Sum.inr FL.l5),(v,some (Sum.inl a)),fstk S [] [] t (Sum.inl a :: o)⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d18,d46,bit]
theorem f5_nil (b:Option (Bool ⊕ Bool)) :
  TM2.step (d0 M e₀ e₁)
    (⟨some (Sum.inr FL.l5),(v,b),fstk S [] [] [] o⟩:FCfg1 M) =
   some ⟨none,(v,none),fstk S [] [] [] o⟩:=by
 simp [TM2.step,d0,TM2.stepAux,d18]
theorem loop5:∀ (t:List Bool) (o:List (Bool ⊕ Bool)) (b:Option (Bool ⊕ Bool)),
  (flip bind (TM2.step (d0 M e₀ e₁)))^[t.length+1]
    (some (⟨some (Sum.inr FL.l5),(v,b),fstk S [] [] t o⟩:FCfg1 M)) =
   some ⟨none,(v,none),fstk S [] [] [] (t.reverse.map Sum.inl++o)⟩:=by
 intro t
 induction t with
 | nil=>intro o b;exact f5_nil e₀ e₁ v S o b
 | cons a t ih =>
  intro o b
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (d0 M e₀ e₁))
    (some (⟨some (Sum.inr FL.l5),(v,b),fstk S [] [] (a :: t) o⟩:FCfg1 M)) =
    some ⟨some (Sum.inr FL.l5),(v,some (Sum.inl a)),fstk S [] [] t (Sum.inl a :: o)⟩ :=
   d165 e₀ e₁ v S o b a t
  rw [e,ih];simp
end Lib.Machines
end
section
namespace Lib.Machines
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool → M.Γ M.k₀) (e₁:M.Γ M.k₁ → Bool)
theorem d97:(fstk (fun _=>[]) [] [] [] []:∀ k,List (FstΓ M k))=fun _=>[]:=by
 funext j;rcases j with j | (_ | _ | _ | _) <;> rfl
theorem d96 (i:List (Bool ⊕ Bool)) :
  (fstk (fun _=>[]) i [] [] []:∀ k,List (FstΓ M k)) =
   Function.update (fun _=>[]:∀ k,List (FstΓ M k)) (Sum.inr FX.I) i :=
 (d33 (fun _=>[]) [] [] [] [] i).symm.trans (by rw [d97])
theorem d95 (o:List (Bool ⊕ Bool)) :
  (fstk (fun _=>[]) [] [] [] o:∀ k,List (FstΓ M k)) =
   Function.update (fun _=>[]:∀ k,List (FstΓ M k)) (Sum.inr FX.O) o :=
 (d46 (fun _=>[]) [] [] [] [] o).symm.trans (by rw [d97])
theorem d110 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
  (o:List (Bool ⊕ Bool)) (l:List (M.Γ M.k₀)) :
  embF b i w t o (initList M l) =
   (⟨some (Sum.inl M.main),(M.initialState,b),
    fstk (Function.update (fun _=>[]) M.k₀ l) i w t o⟩:FCfg1 M):=by
 rw [d4];rfl
theorem d111 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (w t:List Bool)
  (o:List (Bool ⊕ Bool)) (m:List (M.Γ M.k₁)) :
  embF b i w t o (haltList M m) =
   (⟨some (Sum.inr FL.l3),(M.initialState,b),
    fstk (Function.update (fun _=>[]) M.k₁ m) i w t o⟩:FCfg1 M):=by
 rw [d5];rfl
theorem d16 {γ δ : Type} (l:List γ) :
  l.filterMap (fun _=>(none:Option δ))=[]:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp
theorem d26 (x w:List Bool) :
  (encodePair (x,w)).filterMap Sum.getLeft? = x:=by
 have h1:(Sum.getLeft? ∘ (Sum.inl:Bool → Bool ⊕ Bool):Bool → Option Bool)=some:=rfl
 have h2:(Sum.getLeft? ∘ (Sum.inr:Bool → Bool ⊕ Bool):Bool → Option Bool)=fun _=>none:=rfl
 simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
  List.filterMap_some,d16,List.append_nil]
theorem d24 (x w:List Bool) :
  (encodePair (x,w)).filterMap Sum.getRight? = w:=by
 have h1:(Sum.getRight? ∘ (Sum.inl:Bool → Bool ⊕ Bool):Bool → Option Bool)=fun _=>none:=rfl
 have h2:(Sum.getRight? ∘ (Sum.inr:Bool → Bool ⊕ Bool):Bool → Option Bool)=some:=rfl
 simp only [encodePair,List.filterMap_append,List.filterMap_map,h1,h2,
  List.filterMap_some,d16,List.nil_append]
theorem d9 (x w:List Bool) :
  (encodePair (x,w)).length=x.length+w.length:=by
 simp [encodePair]
theorem d107 (x w0:List Bool) (m:List (M.Γ M.k₁)) (s:ℕ)
  (h:(flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀)))=some (haltList M m)) :
  ∃ n,n ≤ s+2 * x.length+2 * w0.length+2 * m.length+5 ∧
   (flip bind (TM2.step (d0 M e₀ e₁)))^[n]
     (some (initList (firstM M e₀ e₁) (encodePair (x,w0)))) =
    some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁,w0))):=by
 have q1:(flip bind (TM2.step (d0 M e₀ e₁)))^[(encodePair (x,w0)).length+1]
   (some (initList (firstM M e₀ e₁) (encodePair (x,w0)))) =
   some (⟨some (Sum.inr FL.l2),(M.initialState,none),
    fstk (fun _=>[]) [] w0.reverse x.reverse []⟩:FCfg1 M):=by
  have:=loop1 e₀ e₁ M.initialState (fun _=>[]) [] (encodePair (x,w0)) [] [] none
  rw [d26,d24,List.append_nil,List.append_nil,d96] at this
  exact (congrArg (fun c=>(flip bind (TM2.step (d0 M e₀ e₁)))^[
   (encodePair (x,w0)).length+1] (some c))
   (d4 (firstM M e₀ e₁) (encodePair (x,w0)))).trans this
 have q2:(flip bind (TM2.step (d0 M e₀ e₁)))^[x.reverse.length+1]
   (some (⟨some (Sum.inr FL.l2),(M.initialState,none),
    fstk (fun _=>[]) [] w0.reverse x.reverse []⟩:FCfg1 M)) =
   some (embF none [] w0.reverse [] [] (initList M (x.map e₀))):=by
  have:=loop2 e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _=>[]) none
  rw [d110]
  simpa using this
 have q3:=d59 (TM2.step M.m) (TM2.step (d0 M e₀ e₁))
  (embF none [] w0.reverse [] []) (stepF e₀ e₁ none [] w0.reverse [] []) s _ _ h
 rw [d111] at q3
 have q4:(flip bind (TM2.step (d0 M e₀ e₁)))^[w0.reverse.length+1]
   (some (⟨some (Sum.inr FL.l3),(M.initialState,none),
    fstk (Function.update (fun _=>[]) M.k₁ m) [] w0.reverse [] []⟩:FCfg1 M)) =
   some (⟨some (Sum.inr FL.l4),(M.initialState,none),
    fstk (Function.update (fun _=>[]) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩:FCfg1 M):=by
  have:=loop3 e₀ e₁ M.initialState (Function.update (fun _=>[]) M.k₁ m) w0.reverse [] none
  simpa using this
 have q5:(flip bind (TM2.step (d0 M e₀ e₁)))^[m.length+1]
   (some (⟨some (Sum.inr FL.l4),(M.initialState,none),
    fstk (Function.update (fun _=>[]) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩:FCfg1 M)) =
   some (⟨some (Sum.inr FL.l5),(M.initialState,none),
    fstk (fun _=>[]) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩:FCfg1 M):=by
  have:=loop4 e₀ e₁ M.initialState (fun _=>[]) (w0.map Sum.inr) m [] none
  simpa using this
 have q6:(flip bind (TM2.step (d0 M e₀ e₁)))^[(m.reverse.map e₁).length+1]
   (some (⟨some (Sum.inr FL.l5),(M.initialState,none),
    fstk (fun _=>[]) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩:FCfg1 M)) =
   some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁,w0))):=by
  have:=loop5 e₀ e₁ M.initialState (fun _=>[]) (m.reverse.map e₁) (w0.map Sum.inr) none
  rw [d95] at this
  refine this.trans (Eq.trans ?_
   (congrArg some (d5 (firstM M e₀ e₁) (encodePair (m.map e₁,w0)))).symm)
  simp [encodePair]
  rfl
 refine ⟨_,?_,d6 _ (d6 _ (d6 _ (d6 _ (d6 _ q1 q2) q3)
  q4) q5) q6⟩
 simp only [d9,List.length_reverse,List.length_map]
 omega
theorem d61 (f:List Bool → List Bool)
    (c:TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) f) :
    Nonempty (TM2ComputableInPolyTime encodePair encodePair
      (fun p:List Bool × List Bool=>(f p.1,p.2))):=by
  let e₀:Bool → c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun
  let e₁:c.tm.Γ c.tm.k₁ → Bool:=c.outputAlphabet
  let T:Polynomial ℕ :=
    c.time+Polynomial.C 2 * (Polynomial.X+Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X+Polynomial.C 5
  have key:∀ p:List Bool × List Bool,∃ n,n ≤ T.eval (encodePair p).length ∧
      (flip bind (TM2.step (d0 c.tm e₀ e₁)))^[n]
          (some (initList (firstM c.tm e₀ e₁) (encodePair p))) =
        some (haltList (firstM c.tm e₀ e₁) (encodePair (f p.1,p.2))):=by
    rintro ⟨x,w⟩
    have hs:∃ s,s ≤ Polynomial.eval x.length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps,(c.outputsFun x).steps_le_m,(c.outputsFun x).evals_in_steps⟩
    obtain ⟨s,b1,h⟩:=hs
    obtain ⟨n,hn,hrun⟩:=d107 e₀ e₁ x w _ s h
    have hm:(List.map c.outputAlphabet.invFun (f x)).map e₁=f x:=by
      rw [List.map_map]
      conv_rhs=>rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _=>c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n,hn.trans ?_,hrun⟩
    have h':=h
    rw [d5,d4] at h'
    have hlen:=d67 c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self,List.length_map] at hlen
    have hin:((Function.update (fun _=>[]:∀ k,List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
        c.tm.k₁).length ≤ x.length:=by
      by_cases hk:c.tm.k₁=c.tm.k₀
      · rw [hk,Function.update_self,List.length_map]
      · rw [Function.update_of_ne hk];simp
    have b2:Polynomial.eval x.length c.time ≤ Polynomial.eval (x.length+w.length) c.time :=
      d37 _ (by omega)
    have hmul:maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval (x.length+w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,d9,List.length_map]
    omega
  exact ⟨{
    tm:=firstM c.tm e₀ e₁
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=T
    outputsFun:=fun p =>
      { steps:=Classical.choose (key p)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          exact (congrArg (fun l=>(flip bind (TM2.step (d0 c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
            (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l=>some (haltList (firstM c.tm e₀ e₁) l))
              (hm _ (encodePair (f p.1,p.2))).symm))
        steps_le_m:=(Classical.choose_spec (key p)).1 } }⟩
end Lib.Machines
end
section
namespace Lib.Machines.Iter
open Turing
inductive IX
 | I | C | T | O
 deriving DecidableEq
instance:Fintype IX :=
 Fintype.ofList [IX.I,IX.C,IX.T,IX.O] (fun x=>by cases x <;> simp)
inductive IL
 | l1 | l2 | l3 | l4 | l5 | l6
 deriving DecidableEq
instance:Fintype IL :=
 Fintype.ofList [IL.l1,IL.l2,IL.l3,IL.l4,IL.l5,IL.l6] (fun x=>by cases x <;> simp)
variable (M:FinTM2)
abbrev ItΓ : M.K ⊕ IX → Type
 | Sum.inl k=>M.Γ k
 | Sum.inr IX.I=>Bool ⊕ Bool
 | Sum.inr IX.C=>Bool
 | Sum.inr IX.T=>Bool
 | Sum.inr IX.O=>Bool
abbrev ItΛ : Type:=M.Λ ⊕ IL
abbrev Itσ : Type:=M.σ × Option (Bool ⊕ Bool)
variable {M}
def trI:TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
 | .push k f q => .push (Sum.inl k) (fun s=>f s.1) (trI q)
 | .peek k f q => .peek (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trI q)
 | .pop k f q => .pop (Sum.inl k) (fun s o=>(f s.1 o,s.2)) (trI q)
 | .load a q => .load (fun s=>(a s.1,s.2)) (trI q)
 | .branch f q₁ q₂ => .branch (fun s=>f s.1) (trI q₁) (trI q₂)
 | .goto f => .goto (fun s=>Sum.inl (f s.1))
 | .halt => .goto (fun _=>Sum.inr IL.l4)
variable (M)
def d1 (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool) :
  ItΛ M → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
 | Sum.inl l=>trI (M.m l)
 | Sum.inr IL.l1 =>
  .pop (Sum.inr IX.I) (fun s o=>(s.1,o))
   (.branch (fun s=>s.2.isSome)
    (.branch (fun s=>isFst s.2)
     (.push (Sum.inr IX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l1))
     (.push (Sum.inr IX.C) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l1)))
    (.goto fun _=>Sum.inr IL.l2))
 | Sum.inr IL.l2 =>
  .pop (Sum.inr IX.T) (fun s o=>(s.1,o.map Sum.inl))
   (.branch (fun s=>s.2.isSome)
    (.push (Sum.inl M.k₀) (fun s=>e₀ (bit s.2)) (.goto fun _=>Sum.inr IL.l2))
    (.goto fun _=>Sum.inr IL.l3))
 | Sum.inr IL.l3 =>
  .pop (Sum.inr IX.C) (fun s o=>(s.1,o.map Sum.inl))
   (.branch (fun s=>s.2.isSome)
    (.goto fun _=>Sum.inl M.main)
    (.goto fun _=>Sum.inr IL.l5))
 | Sum.inr IL.l4 =>
  .pop (Sum.inl M.k₁) (fun s o=>(s.1,o.map fun y=>Sum.inl (e₁ y)))
   (.branch (fun s=>s.2.isSome)
    (.push (Sum.inr IX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l4))
    (.goto fun _=>Sum.inr IL.l2))
 | Sum.inr IL.l5 =>
  .pop (Sum.inl M.k₀) (fun s o=>(s.1,o.map fun y=>Sum.inl (d₀ y)))
   (.branch (fun s=>s.2.isSome)
    (.push (Sum.inr IX.T) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l5))
    (.goto fun _=>Sum.inr IL.l6))
 | Sum.inr IL.l6 =>
  .pop (Sum.inr IX.T) (fun s o=>(s.1,o.map Sum.inl))
   (.branch (fun s=>s.2.isSome)
    (.push (Sum.inr IX.O) (fun s=>bit s.2) (.goto fun _=>Sum.inr IL.l6))
    .halt)
def iterM (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool):FinTM2 :=
  haveI:=M.kFin
  haveI:=M.ΛFin
  haveI:=M.σFin
  { K:=M.K ⊕ IX
    k₀:=Sum.inr IX.I
    k₁:=Sum.inr IX.O
    Γ := ItΓ M
    Λ := ItΛ M
    main:=Sum.inr IL.l1
    σ := Itσ M
    initialState:=(M.initialState,none)
    Γk₀Fin:=inferInstanceAs (Fintype (Bool ⊕ Bool))
    m:=d1 M e₀ d₀ e₁ }
variable {M}
def istk (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
  ∀ k,List (ItΓ M k)
 | Sum.inl k=>S k
 | Sum.inr IX.I=>i
 | Sum.inr IX.C=>cn
 | Sum.inr IX.T=>t
 | Sum.inr IX.O=>o
section istk
variable (S:∀ k,List (M.Γ k)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
@[simp] theorem istk_M (k:M.K):istk S i cn t o (Sum.inl k)=S k:=rfl
@[simp] theorem istk_I:istk S i cn t o (Sum.inr IX.I)=i:=rfl
@[simp] theorem istk_C:istk S i cn t o (Sum.inr IX.C)=cn:=rfl
@[simp] theorem istk_T:istk S i cn t o (Sum.inr IX.T)=t:=rfl
@[simp] theorem istk_O:istk S i cn t o (Sum.inr IX.O)=o:=rfl
theorem d15 (k:M.K) (x:List (M.Γ k)) :
  Function.update (istk S i cn t o) (Sum.inl k) x=istk (Function.update S k x) i cn t o:=by
 funext j
 rcases j with j | j
 ·
  by_cases h:j=k
  ·
   subst h
   rw [Function.update_self]
   show x=Function.update S j x j
   rw [Function.update_self]
  ·
   rw [Function.update_of_ne (by simpa using h)]
   show S j=Function.update S k x j
   rw [Function.update_of_ne h]
 · rw [Function.update_of_ne (by simp)];cases j <;> rfl
theorem d32 (i':List (Bool ⊕ Bool)) :
  Function.update (istk S i cn t o) (Sum.inr IX.I) i'=istk S i' cn t o:=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
theorem d44 (cn':List Bool) :
  Function.update (istk S i cn t o) (Sum.inr IX.C) cn'=istk S i cn' t o:=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
theorem d14 (t':List Bool) :
  Function.update (istk S i cn t o) (Sum.inr IX.T) t'=istk S i cn t' o:=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
 · rw [Function.update_of_ne (by simp)];rfl
theorem d72 (o':List Bool) :
  Function.update (istk S i cn t o) (Sum.inr IX.O) o'=istk S i cn t o':=by
 funext j
 rcases j with j | (_ | _ | _ | _)
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_of_ne (by simp)];rfl
 · rw [Function.update_self];rfl
end istk
abbrev ICfg (M:FinTM2):Type:=TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)
def embI (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
  (c:TM2.Cfg M.Γ M.Λ M.σ):ICfg M :=
 ⟨some (c.l.elim (Sum.inr IL.l4) Sum.inl),(c.var,b),istk c.stk i cn t o⟩
theorem simI (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
  (q:TM2.Stmt M.Γ M.Λ M.σ) (v:M.σ) (S:∀ k,List (M.Γ k)) :
  TM2.stepAux (trI q) ((v,b):Itσ M) (istk S i cn t o) =
   embI b i cn t o (TM2.stepAux q v S):=by
 induction q generalizing v S with
 | push k f q ih =>
  have:=ih v (Function.update S k (f v :: S k))
  rw [← d15] at this
  exact this
 | peek k f q ih=>exact ih _ _
 | pop k f q ih =>
  have:=ih (f v (S k).head?) (Function.update S k (S k).tail)
  rw [← d15] at this
  exact this
 | load a q ih=>exact ih _ _
 | branch f q₁ q₂ ih₁ ih₂ =>
  simp only [trI,TM2.stepAux]
  cases f v
  · exact ih₂ v S
  · exact ih₁ v S
 | goto f=>rfl
 | halt=>rfl
theorem stepI (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool)
  (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
  (c c':TM2.Cfg M.Γ M.Λ M.σ) (h:TM2.step M.m c=some c') :
  TM2.step (d1 M e₀ d₀ e₁) (embI b i cn t o c)=some (embI b i cn t o c'):=by
 obtain ⟨l,v,S⟩:=c
 cases l with
 | none=>simp [TM2.step] at h
 | some l =>
  simp only [TM2.step,Option.some.injEq] at h
  subst h
  exact congrArg some (simI b i cn t o (M.m l) v S)
theorem d108 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
  (l:List (M.Γ M.k₀)) :
  embI b i cn t o (initList M l) =
   (⟨some (Sum.inl M.main),(M.initialState,b),
    istk (Function.update (fun _=>[]) M.k₀ l) i cn t o⟩:ICfg M):=by
 rw [d4];rfl
theorem d109 (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool)
  (m:List (M.Γ M.k₁)) :
  embI b i cn t o (haltList M m) =
   (⟨some (Sum.inr IL.l4),(M.initialState,b),
    istk (Function.update (fun _=>[]) M.k₁ m) i cn t o⟩:ICfg M):=by
 rw [d5];rfl
theorem d94:(istk (fun _=>[]) [] [] [] []:∀ k,List (ItΓ M k))=fun _=>[]:=by
 funext j;rcases j with j | (_ | _ | _ | _) <;> rfl
theorem d93 (i:List (Bool ⊕ Bool)) :
  (istk (fun _=>[]) i [] [] []:∀ k,List (ItΓ M k)) =
   Function.update (fun _=>[]:∀ k,List (ItΓ M k)) (Sum.inr IX.I) i :=
 (d32 (fun _=>[]) [] [] [] [] i).symm.trans (by rw [d94])
theorem d92 (o:List Bool) :
  (istk (fun _=>[]) [] [] [] o:∀ k,List (ItΓ M k)) =
   Function.update (fun _=>[]:∀ k,List (ItΓ M k)) (Sum.inr IX.O) o :=
 (d72 (fun _=>[]) [] [] [] [] o).symm.trans (by rw [d94])
end Lib.Machines.Iter
end
section
namespace Lib.Machines.Iter
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool)
variable (v:M.σ) (S:∀ k,List (M.Γ k))
theorem i1_inl (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
  (cn t o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l1),(v,b),istk S (Sum.inl a :: i) cn t o⟩:ICfg M) =
   some ⟨some (Sum.inr IL.l1),(v,some (Sum.inl a)),istk S i cn (a :: t) o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d32,d14,isFst,bit]
theorem i1_inr (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
  (cn t o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l1),(v,b),istk S (Sum.inr a :: i) cn t o⟩:ICfg M) =
   some ⟨some (Sum.inr IL.l1),(v,some (Sum.inr a)),istk S i (a :: cn) t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d32,d44,isFst,bit]
theorem i1_nil (b:Option (Bool ⊕ Bool)) (cn t o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l1),(v,b),istk S [] cn t o⟩:ICfg M) =
   some ⟨some (Sum.inr IL.l2),(v,none),istk S [] cn t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d32]
theorem iloop1 (o:List Bool) :
  ∀ (i:List (Bool ⊕ Bool)) (cn t:List Bool) (b:Option (Bool ⊕ Bool)),
  ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[i.length+1]
    (some (⟨some (Sum.inr IL.l1),(v,b),istk S i cn t o⟩:ICfg M)) =
   some ⟨some (Sum.inr IL.l2),(v,none),
    istk S [] ((i.filterMap Sum.getRight?).reverse++cn)
     ((i.filterMap Sum.getLeft?).reverse++t) o⟩:=by
 intro i
 induction i with
 | nil=>intro cn t b;exact i1_nil e₀ d₀ e₁ v S b cn t o
 | cons x i ih =>
  intro cn t b
  rw [List.length_cons,Function.iterate_succ_apply]
  cases x with
  | inl a =>
   have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
     (some (⟨some (Sum.inr IL.l1),(v,b),istk S (Sum.inl a :: i) cn t o⟩:ICfg M)) =
     some ⟨some (Sum.inr IL.l1),(v,some (Sum.inl a)),istk S i cn (a :: t) o⟩ :=
    i1_inl e₀ d₀ e₁ v S b a i cn t o
   rw [e,ih];simp [List.filterMap_cons]
  | inr a =>
   have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
     (some (⟨some (Sum.inr IL.l1),(v,b),istk S (Sum.inr a :: i) cn t o⟩:ICfg M)) =
     some ⟨some (Sum.inr IL.l1),(v,some (Sum.inr a)),istk S i (a :: cn) t o⟩ :=
    i1_inr e₀ d₀ e₁ v S b a i cn t o
   rw [e,ih];simp [List.filterMap_cons]
theorem d158 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
  (cn t o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l2),(v,b),istk S i cn (a :: t) o⟩:ICfg M) =
   some ⟨some (Sum.inr IL.l2),(v,some (Sum.inl a)),
    istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d14,d15,bit]
theorem i2_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l2),(v,b),istk S i cn [] o⟩:ICfg M) =
   some ⟨some (Sum.inr IL.l3),(v,none),istk S i cn [] o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d14]
theorem iloop2 (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
  ∀ (t:List Bool) (S:∀ k,List (M.Γ k)) (b:Option (Bool ⊕ Bool)),
  ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[t.length+1]
    (some (⟨some (Sum.inr IL.l2),(v,b),istk S i cn t o⟩:ICfg M)) =
   some ⟨some (Sum.inr IL.l3),(v,none),
    istk (Function.update S M.k₀ (t.reverse.map e₀++S M.k₀)) i cn [] o⟩:=by
 intro t
 induction t with
 | nil =>
  intro S b
  have:Function.update S M.k₀ (([]:List Bool).reverse.map e₀++S M.k₀)=S:=by simp
  rw [this]
  exact i2_nil e₀ d₀ e₁ v S b i cn o
 | cons a t ih =>
  intro S b
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
    (some (⟨some (Sum.inr IL.l2),(v,b),istk S i cn (a :: t) o⟩:ICfg M)) =
    some ⟨some (Sum.inr IL.l2),(v,some (Sum.inl a)),
     istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ :=
   d158 e₀ d₀ e₁ v S b a i cn t o
  rw [e,ih];simp
theorem d157 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
  (cn t o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l3),(v,b),istk S i (a :: cn) t o⟩:ICfg M) =
   some ⟨some (Sum.inl M.main),(v,some (Sum.inl a)),istk S i cn t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d44]
theorem i3_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (t o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l3),(v,b),istk S i [] t o⟩:ICfg M) =
   some ⟨some (Sum.inr IL.l5),(v,none),istk S i [] t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d44]
theorem d156 (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₁) (m:List (M.Γ M.k₁))
  (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l4),(v,b),istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ :
     ICfg M) =
   some ⟨some (Sum.inr IL.l4),(v,some (Sum.inl (e₁ y))),
    istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d14,d15,bit]
theorem i4_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l4),(v,b),istk (Function.update S M.k₁ []) i cn t o⟩:ICfg M) =
   some ⟨some (Sum.inr IL.l2),(v,none),istk (Function.update S M.k₁ []) i cn t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d15]
theorem iloop4 (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
  ∀ (m:List (M.Γ M.k₁)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
  ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[m.length+1]
    (some (⟨some (Sum.inr IL.l4),(v,b),istk (Function.update S M.k₁ m) i cn t o⟩ :
     ICfg M)) =
   some ⟨some (Sum.inr IL.l2),(v,none),
    istk (Function.update S M.k₁ []) i cn (m.reverse.map e₁++t) o⟩:=by
 intro m
 induction m with
 | nil=>intro t b;exact i4_nil e₀ d₀ e₁ v S b i cn t o
 | cons y m ih =>
  intro t b
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
    (some (⟨some (Sum.inr IL.l4),(v,b),
     istk (Function.update S M.k₁ (y :: m)) i cn t o⟩:ICfg M)) =
    some ⟨some (Sum.inr IL.l4),(v,some (Sum.inl (e₁ y))),
     istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ :=
   d156 e₀ d₀ e₁ v S b y m i cn t o
  rw [e,ih];simp
theorem d155 (b:Option (Bool ⊕ Bool)) (y:M.Γ M.k₀) (m:List (M.Γ M.k₀))
  (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l5),(v,b),istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ :
     ICfg M) =
   some ⟨some (Sum.inr IL.l5),(v,some (Sum.inl (d₀ y))),
    istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d14,d15,bit]
theorem i5_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn t o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l5),(v,b),istk (Function.update S M.k₀ []) i cn t o⟩:ICfg M) =
   some ⟨some (Sum.inr IL.l6),(v,none),istk (Function.update S M.k₀ []) i cn t o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d15]
theorem iloop5 (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
  ∀ (m:List (M.Γ M.k₀)) (t:List Bool) (b:Option (Bool ⊕ Bool)),
  ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[m.length+1]
    (some (⟨some (Sum.inr IL.l5),(v,b),istk (Function.update S M.k₀ m) i cn t o⟩ :
     ICfg M)) =
   some ⟨some (Sum.inr IL.l6),(v,none),
    istk (Function.update S M.k₀ []) i cn (m.reverse.map d₀++t) o⟩:=by
 intro m
 induction m with
 | nil=>intro t b;exact i5_nil e₀ d₀ e₁ v S b i cn t o
 | cons y m ih =>
  intro t b
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
    (some (⟨some (Sum.inr IL.l5),(v,b),
     istk (Function.update S M.k₀ (y :: m)) i cn t o⟩:ICfg M)) =
    some ⟨some (Sum.inr IL.l5),(v,some (Sum.inl (d₀ y))),
     istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ :=
   d155 e₀ d₀ e₁ v S b y m i cn t o
  rw [e,ih];simp
theorem d154 (b:Option (Bool ⊕ Bool)) (a:Bool) (i:List (Bool ⊕ Bool))
  (cn t o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l6),(v,b),istk S i cn (a :: t) o⟩:ICfg M) =
   some ⟨some (Sum.inr IL.l6),(v,some (Sum.inl a)),istk S i cn t (a :: o)⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d14,d72,bit]
theorem i6_nil (b:Option (Bool ⊕ Bool)) (i:List (Bool ⊕ Bool)) (cn o:List Bool) :
  TM2.step (d1 M e₀ d₀ e₁)
    (⟨some (Sum.inr IL.l6),(v,b),istk S i cn [] o⟩:ICfg M) =
   some ⟨none,(v,none),istk S i cn [] o⟩:=by
 simp [TM2.step,d1,TM2.stepAux,d14]
theorem iloop6 (i:List (Bool ⊕ Bool)) (cn:List Bool) :
  ∀ (t o:List Bool) (b:Option (Bool ⊕ Bool)),
  ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[t.length+1]
    (some (⟨some (Sum.inr IL.l6),(v,b),istk S i cn t o⟩:ICfg M)) =
   some ⟨none,(v,none),istk S i cn [] (t.reverse++o)⟩:=by
 intro t
 induction t with
 | nil=>intro o b;exact i6_nil e₀ d₀ e₁ v S b i cn o
 | cons a t ih =>
  intro o b
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:(flip bind (TM2.step (d1 M e₀ d₀ e₁)))
    (some (⟨some (Sum.inr IL.l6),(v,b),istk S i cn (a :: t) o⟩:ICfg M)) =
    some ⟨some (Sum.inr IL.l6),(v,some (Sum.inl a)),istk S i cn t (a :: o)⟩ :=
   d154 e₀ d₀ e₁ v S b a i cn t o
  rw [e,ih];simp
theorem d28 (k:M.K) :
  Function.update (fun _=>[]:∀ k,List (M.Γ k)) k []=fun _=>[] :=
 Function.update_eq_self k (fun _=>[]:∀ k,List (M.Γ k))
end Lib.Machines.Iter
end
section
namespace Lib.Machines.Iter
open Turing PEqualNP.Library
variable {M:FinTM2} (e₀:Bool → M.Γ M.k₀) (d₀:M.Γ M.k₀ → Bool) (e₁:M.Γ M.k₁ → Bool)
theorem d71 (g:List Bool → List Bool) (p:Polynomial ℕ)
  (hd:∀ a,d₀ (e₀ a)=a)
  (hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s ≤ p.eval z.length ∧
   (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m) ∧
    m.map e₁=g z) :
  ∀ (cn z:List Bool) (L:ℕ) (b:Option (Bool ⊕ Bool)),
   (∀ j ≤ cn.length,(g^[j] z).length ≤ L) →
   ∃ n,n ≤ cn.length * (p.eval L+2 * L+3)+2 * L+3 ∧
    ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
       istk (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] cn [] []⟩:ICfg M)) =
     some ⟨none,(M.initialState,none),
      istk (fun _=>[]) [] [] [] (g^[cn.length] z)⟩:=by
 intro cn
 induction cn with
 | nil =>
  intro z L b hL
  have hz:((z.map e₀).reverse.map d₀).reverse=z:=by
   rw [List.map_reverse,List.reverse_reverse,List.map_map]
   conv_rhs=>rw [← List.map_id z]
   exact List.map_congr_left fun a _=>hd a
  have q1:((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[1]
    (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
     istk (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩:ICfg M)) =
    some ⟨some (Sum.inr IL.l5),(M.initialState,none),
     istk (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
   i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
  have q2:=iloop5 e₀ d₀ e₁ M.initialState (fun _=>[]) [] [] [] (z.map e₀) [] none
  rw [d28,List.append_nil] at q2
  have q3:=iloop6 e₀ d₀ e₁ M.initialState (fun _=>[]) [] []
   ((z.map e₀).reverse.map d₀) [] none
  rw [List.append_nil,hz] at q3
  refine ⟨_,?_,d6 _ (d6 _ q1 q2) q3⟩
  have hz0:z.length ≤ L:=hL 0 (Nat.zero_le _)
  simp only [List.length_reverse,List.length_map,List.length_nil] at hz0 ⊢
  omega
 | cons a cn ih =>
  intro z L b hL
  obtain ⟨s,m,hs,hm,hmg⟩:=hrun z
  rw [List.length_cons] at hL
  have hz0:z.length ≤ L:=hL 0 (Nat.zero_le _)
  have hgz:(g z).length ≤ L:=hL 1 (by omega)
  have hml:m.length=(g z).length:=by rw [← hmg,List.length_map]
  have q1:((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[1]
    (some (⟨some (Sum.inr IL.l3),(M.initialState,b),
     istk (Function.update (fun _=>[]) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩:ICfg M)) =
    some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))):=by
   rw [d108]
   exact d157 e₀ d₀ e₁ M.initialState _ b a [] cn [] []
  have q2:=d59 (TM2.step M.m) (TM2.step (d1 M e₀ d₀ e₁))
   (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
   s _ _ hm
  rw [d109] at q2
  have q3:=iloop4 e₀ d₀ e₁ M.initialState (fun _=>[]) [] cn [] m [] (some (Sum.inl a))
  rw [d28,List.append_nil,List.map_reverse,hmg] at q3
  have q4:=iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _=>[]) none
  rw [List.append_nil,List.reverse_reverse] at q4
  obtain ⟨n,hn,q5⟩:=ih (g z) L none (fun j hj=>by
   have:=hL (j+1) (by omega)
   rwa [Function.iterate_succ_apply] at this)
  have e:g^[(a :: cn).length] z=g^[cn.length] (g z):=Function.iterate_succ_apply g _ z
  rw [e]
  refine ⟨_,?_,d6 _ (d6 _ (d6 _ (d6 _ q1 q2) q3) q4) q5⟩
  have hp:p.eval z.length ≤ p.eval L:=d37 p (by omega)
  rw [List.length_reverse,List.length_cons,Nat.succ_mul]
  generalize cn.length * (p.eval L+2 * L+3)=A at hn ⊢
  omega
theorem d80 (g:List Bool → List Bool) (p:Polynomial ℕ)
  (hd:∀ a,d₀ (e₀ a)=a)
  (hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (M.Γ M.k₁)),s ≤ p.eval z.length ∧
   (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀)))=some (haltList M m) ∧
    m.map e₁=g z)
  (y u:List Bool) (L:ℕ) (hL:∀ j ≤ u.length,(g^[j] y).length ≤ L) :
  ∃ n,n ≤ u.length * (p.eval L+2 * L+3)+2 * L+2 * y.length+u.length+5 ∧
   ((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
    some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)):=by
 have q1:((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1]
   (some (initList (iterM M e₀ d₀ e₁) (encodePair (y,u)))) =
   some (⟨some (Sum.inr IL.l2),(M.initialState,none),
    istk (fun _=>[]) [] u.reverse y.reverse []⟩:ICfg M):=by
  have:=iloop1 e₀ d₀ e₁ M.initialState (fun _=>[]) [] (encodePair (y,u)) [] [] none
  rw [d26,d24,List.append_nil,List.append_nil,d93] at this
  exact (congrArg (fun c=>((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[(encodePair (y,u)).length+1] (some c))
   (d4 (iterM M e₀ d₀ e₁) (encodePair (y,u)))).trans this
 have q2:=iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _=>[]) none
 rw [List.append_nil,List.reverse_reverse] at q2
 obtain ⟨n,hn,q3⟩:=d71 e₀ d₀ e₁ g p hd hrun u.reverse y L none
  (by rw [List.length_reverse];exact hL)
 rw [List.length_reverse] at hn q3
 rw [d92] at q3
 have q3':((flip bind (TM2.step (d1 M e₀ d₀ e₁))))^[n]
   (some (⟨some (Sum.inr IL.l3),(M.initialState,none),
    istk (Function.update (fun _=>[]) M.k₀ (y.map e₀)) [] u.reverse [] []⟩:ICfg M)) =
   some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
  q3.trans (congrArg some (d5 (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
 refine ⟨_,?_,d6 _ (d6 _ q1 q2) q3'⟩
 rw [d9,List.length_reverse]
 omega
theorem d22 (g:List Bool → List Bool) (m:List Bool → ℕ)
  (hm:∀ y:List Bool,m (g y) ≤ m y)
  (hg:∀ y:List Bool,(g y).length ≤ y.length+m y) (y:List Bool) :
  ∀ j:ℕ,m (g^[j] y) ≤ m y∧(g^[j] y).length ≤ y.length+j * m y:=by
 intro j
 induction j with
 | zero=>simp
 | succ j ih =>
  rw [Function.iterate_succ_apply',Nat.succ_mul]
  have h1:=hm (g^[j] y)
  have h2:=hg (g^[j] y)
  obtain ⟨i1,i2⟩:=ih
  generalize j * m y=A at i2 ⊢
  exact ⟨by omega,by omega⟩
theorem d70 (A B L V y u:ℕ) (hLV:L ≤ V) (hAB:A ≤ B) :
  A+2 * L+2 * y+u+5 ≤ B+2 * V+3 * (y+u)+5:=by
 omega
theorem iter_polyTime_measure (g:List Bool → List Bool)
    (c:Turing.TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) g)
    (m:List Bool → ℕ) (a:ℕ)
    (hm:∀ y:List Bool,m (g y) ≤ m y)
    (hg:∀ y:List Bool,(g y).length ≤ y.length+m y)
    (ha:∀ y:List Bool,m y ≤ a * y.length+a) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x:List Bool=>x) (fun p:List Bool × List Bool=>g^[p.2.length] p.1)):=by
  let e₀:Bool → c.tm.Γ c.tm.k₀:=c.inputAlphabet.invFun
  let d₀:c.tm.Γ c.tm.k₀ → Bool:=c.inputAlphabet
  let e₁:c.tm.Γ c.tm.k₁ → Bool:=c.outputAlphabet
  let W:Polynomial ℕ :=
    Polynomial.X+Polynomial.X * (Polynomial.C a * Polynomial.X+Polynomial.C a)
  let T:Polynomial ℕ :=
    Polynomial.X * (c.time.comp W+Polynomial.C 2 * W+Polynomial.C 3) +
      Polynomial.C 2 * W+Polynomial.C 3 * Polynomial.X+Polynomial.C 5
  have hd:∀ a,d₀ (e₀ a)=a:=fun a=>c.inputAlphabet.right_inv a
  have hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m)∧m.map e₁=g z:=by
    intro z
    refine ⟨(c.outputsFun z).steps,List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m,(c.outputsFun z).evals_in_steps,?_⟩
    rw [List.map_map]
    conv_rhs=>rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _=>c.outputAlphabet.right_inv y
  have key:∀ q:List Bool × List Bool,∃ n,n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (d1 c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)):=by
    rintro ⟨y,u⟩
    have hL:∀ j ≤ u.length,
        (g^[j] y).length ≤ y.length+u.length * (a * y.length+a):=by
      intro j hj
      have h1:=(d22 g m hm hg y j).2
      have h2:j * m y ≤ u.length * (a * y.length+a):=Nat.mul_le_mul hj (ha y)
      omega
    obtain ⟨n,hn,hr⟩:=d80 e₀ d₀ e₁ g c.time hd hrun y u
      (y.length+u.length * (a * y.length+a)) hL
    have hLV:y.length+u.length * (a * y.length+a) ≤
        (y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a) :=
      Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _))
    have hp:=d37 c.time hLV
    have hmul:u.length * (Polynomial.eval (y.length+u.length * (a * y.length+a)) c.time +
          2 * (y.length+u.length * (a * y.length+a))+3) ≤
        (y.length+u.length) * (Polynomial.eval
          ((y.length+u.length)+(y.length+u.length) * (a * (y.length+u.length)+a))
            c.time +
            2 * ((y.length+u.length) +
              (y.length+u.length) * (a * (y.length+u.length)+a))+3) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine ⟨n,hn.trans ?_,hr⟩
    simp only [T,W,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_comp,d9]
    exact d70 _ _ _ _ _ _ hLV hmul
  exact ⟨{
    tm:=iterM c.tm e₀ d₀ e₁
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=T
    outputsFun:=fun q =>
      { steps:=Classical.choose (key q)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          exact (congrArg (fun l=>(flip bind (TM2.step (d1 c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l=>some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m:=(Classical.choose_spec (key q)).1 } }⟩
theorem iter_polyTime (g:List Bool → List Bool)
  (c:TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x) g)
  (k:ℕ) (hk:∀ y:List Bool,(g y).length ≤ y.length+k) :
  ComputableInPolyTime encodePair (fun x:List Bool=>x)
   (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
 iter_polyTime_measure g c (fun _=>k) k (fun _=>le_rfl) hk (fun _=>Nat.le_add_left k _)
end Lib.Machines.Iter
end
section
namespace Lib.Machines
open PEqualNP.Library
private theorem d2 {α β γ : Type} (h : α → β) (φ : β → Option γ) (g : α → γ)
  (hφ : ∀ a,φ (h a)=some (g a)) (l:List α):(l.map h).filterMap φ = l.map g:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp [hφ,ih]
private theorem d8 {α β γ : Type} (h : α → β) (φ : β → Option γ)
  (hφ : ∀ a,φ (h a)=none) (l:List α):(l.map h).filterMap φ = []:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp [hφ,ih]
theorem cpt_comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
  {ec : γ → List γΓ} {f : α → β} {g : β → γ}
  (hf:PEqualNP.Library.ComputableInPolyTime ea eb f)
  (hg:PEqualNP.Library.ComputableInPolyTime eb ec g) :
  PEqualNP.Library.ComputableInPolyTime ea ec (fun a=>g (f a)):=by
 obtain ⟨c1⟩:=hf
 obtain ⟨c2⟩:=hg
 exact d77 ea eb ec f g c1 c2
theorem d84 :
  PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
   PEqualNP.Library.encodePair (fun p:List Bool × List Bool=>(p.2,p.1)):=by
 refine d10 _ _ _
  (fun s:Bool ⊕ Bool=>Sum.elim (fun _=>none) (fun b=>some (Sum.inl b)) s)
  (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some (Sum.inr b)) (fun _=>none) s) ?_
 rintro ⟨x,w⟩
 simp only [encodePair,List.filterMap_append]
 rw [d8 Sum.inl _ (fun _=>rfl) x,
  d2 Sum.inr _ Sum.inl (fun _=>rfl) w,
  d2 Sum.inl _ Sum.inr (fun _=>rfl) x,
  d8 Sum.inr _ (fun _=>rfl) w]
 simp
theorem d171 :
  PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x)
   PEqualNP.Library.encodePair (fun x:List Bool=>(x,x)):=by
 refine d10 _ _ _
  (fun b:Bool=>some (Sum.inl b)) (fun b:Bool=>some (Sum.inr b)) ?_
 intro x
 have h1:=d2 (fun b:Bool=>b) (fun b:Bool=>some (Sum.inl (β := Bool) b))
  Sum.inl (fun _=>rfl) x
 have h2:=d2 (fun b:Bool=>b) (fun b:Bool=>some (Sum.inr (α := Bool) b))
  Sum.inr (fun _=>rfl) x
 simp only [List.map_id'] at h1 h2
 simp only [encodePair,h1,h2]
theorem d170 :
  PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
   (fun x:List Bool=>x) (fun p:List Bool × List Bool=>p.1):=by
 refine d7 _ _ _
  (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some b) (fun _=>none) s) ?_
 rintro ⟨x,w⟩
 simp only [encodePair,List.filterMap_append]
 rw [d2 Sum.inl _ (fun b=>b) (fun _=>rfl) x,
  d8 Sum.inr _ (fun _=>rfl) w]
 simp
theorem d169 :
  PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
   (fun x:List Bool=>x) (fun p:List Bool × List Bool=>p.2):=by
 refine d7 _ _ _
  (fun s:Bool ⊕ Bool=>Sum.elim (fun _=>none) (fun b=>some b) s) ?_
 rintro ⟨x,w⟩
 simp only [encodePair,List.filterMap_append]
 rw [d8 Sum.inl _ (fun _=>rfl) x,
  d2 Sum.inr _ (fun b=>b) (fun _=>rfl) w]
 simp
theorem d74 :
  PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
   (fun x:List Bool=>x) (fun p:List Bool × List Bool=>p.1++p.2):=by
 refine d7 _ _ _
  (fun s:Bool ⊕ Bool=>Sum.elim (fun b=>some b) (fun b=>some b) s) ?_
 rintro ⟨x,w⟩
 simp only [encodePair,List.filterMap_append]
 rw [d2 Sum.inl _ (fun b=>b) (fun _=>rfl) x,
  d2 Sum.inr _ (fun b=>b) (fun _=>rfl) w]
 simp
theorem d38 {f:List Bool → List Bool}
  (hf:Lib.CPTs f) :
  PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
   PEqualNP.Library.encodePair (fun p:List Bool × List Bool=>(f p.1,p.2)):=by
 obtain ⟨c⟩:=hf
 exact d61 f c
theorem d101 {g:List Bool → List Bool}
  (hg:Lib.CPTs g) :
  PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
   PEqualNP.Library.encodePair (fun p:List Bool × List Bool=>(p.1,g p.2)) :=
 cpt_comp (cpt_comp d84 (d38 hg)) d84
theorem cpt_pair {f g:List Bool → List Bool}
  (hf:Lib.CPTs f)
  (hg:Lib.CPTs g) :
  PEqualNP.Library.ComputableInPolyTime (fun x:List Bool=>x)
   PEqualNP.Library.encodePair (fun x:List Bool=>(f x,g x)) :=
 cpt_comp (cpt_comp d171 (d101 hg)) (d38 hf)
theorem cpt_id :
  Lib.CPTs (fun x:List Bool=>x):=by
 refine d7 _ _ _ (fun b:Bool=>some b) ?_
 intro x
 have h:=d2 (fun b:Bool=>b) (fun b:Bool=>some b) (fun b=>b)
  (fun _=>rfl) x
 simp only [List.map_id'] at h
 exact h.symm
end Lib.Machines
end
section
namespace Lib.Machines
open Turing
def fstRun {Γ₀ Γ₁ Q:Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin:Q → Option Γ₁) :
  Q → List Γ₀ → List Γ₁
 | q,[]=>(fin q).toList
 | q,a :: l=>(δ q a).2.toList++fstRun δ fin (δ q a).1 l
def fstRun2 {Γ₀ Γ₁ Q:Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) :
  Q → List Γ₀ → List Γ₁
 | q,[]=>(fin q).toList
 | q,a :: l=>(δ q a).2.1.toList++(δ q a).2.2.toList++fstRun2 δ fin (δ q a).1 l
theorem d36 {Γ₀ Γ₁ Q:Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin:Q → Option Γ₁)
  (q:Q) (l:List Γ₀) :
  fstRun δ fin q l=fstRun2 (fun q a=>((δ q a).1,(δ q a).2,none)) fin q l:=by
 induction l generalizing q with
 | nil=>rfl
 | cons a l ih=>simp [fstRun,fstRun2,ih]
inductive TrK:Type
 | inp | tmp | out
 deriving DecidableEq
instance:Fintype TrK :=
 Fintype.ofList [.inp,.tmp,.out] (fun x=>by cases x <;> simp)
variable {Γ₀ Γ₁ Q:Type}
abbrev TrΓ (Γ₀ Γ₁ Q:Type):TrK → Type
 | .inp => Γ₀
 | .tmp=>Q × Option Γ₀
 | .out => Γ₁
abbrev TrS (Γ₀ Q:Type):Type:=Q × Option Γ₀ × Bool
def trO1 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) :
  Q × Option Γ₀ → Option Γ₁
 | (q,some a)=>(δ q a).2.1
 | (q,none)=>fin q
def trO2 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁):Q × Option Γ₀ → Option Γ₁
 | (q,some a)=>(δ q a).2.2
 | (_,none)=>none
def trOut (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁)
  (e:Q × Option Γ₀):List Γ₁ :=
 (trO1 δ fin e).toList++(trO2 δ e).toList
def d21 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁):Q → List Γ₀ → List (Q × Option Γ₀)
 | q,[]=>[(q,none)]
 | q,a :: l=>(q,some a) :: d21 δ (δ q a).1 l
theorem d57 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (q:Q) (l:List Γ₀) :
  (d21 δ q l).length=l.length+1:=by
 induction l generalizing q with
 | nil=>rfl
 | cons a l ih=>simp [d21,ih]
theorem d85 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) (q:Q)
  (l:List Γ₀):(d21 δ q l).flatMap (trOut δ fin)=fstRun2 δ fin q l:=by
 induction l generalizing q with
 | nil=>simp [d21,trOut,trO1,trO2,fstRun2]
 | cons a l ih=>simp [d21,trOut,trO1,trO2,fstRun2,ih]
def d65 (o:TrS Γ₀ Q → Option Γ₁) (d:Option Γ₁)
  (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
  TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
 .branch (fun s=>(o s).isSome)
  (match d with
   | some dd => .push .out (fun s=>(o s).getD dd) next
   | none=>next)
  next
def trProg (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) (q₀:Q)
  (d:Option Γ₁):Bool → TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
 | false =>
  .pop .inp (fun s o=>(s.1,o,o.isSome))
   (.branch (fun s=>s.2.2)
    (.push .tmp (fun s=>(s.1,s.2.1))
     (.load (fun s=>(match s.2.1 with
       | some a=>(δ s.1 a).1
       | none=>s.1,none,false))
      (.goto fun _=>false)))
    (.push .tmp (fun s=>(s.1,none))
     (.load (fun _=>(q₀,none,false)) (.goto fun _=>true))))
 | true =>
  .pop .tmp (fun _ o=>match o with
    | some e=>(e.1,e.2,true)
    | none=>(q₀,none,false))
   (.branch (fun s=>s.2.2)
    (d65 (fun s=>trO2 δ (s.1,s.2.1)) d
     (d65 (fun s=>trO1 δ fin (s.1,s.2.1)) d (.goto fun _=>true)))
    .halt)
def trM [Fintype Γ₀] [Fintype Q] (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (fin:Q → Option Γ₁) (q₀:Q) (d:Option Γ₁):FinTM2 where
  K:=TrK
  k₀ := .inp
  k₁ := .out
  Γ := TrΓ Γ₀ Γ₁ Q
  Λ := Bool
  main:=false
  σ := TrS Γ₀ Q
  initialState:=(q₀,none,false)
  Γk₀Fin:=inferInstanceAs (Fintype Γ₀)
  m:=trProg δ fin q₀ d
def trSt (l:List Γ₀) (t:List (Q × Option Γ₀)) (u:List Γ₁):∀ k,List (TrΓ Γ₀ Γ₁ Q k)
 | .inp=>l
 | .tmp=>t
 | .out=>u
theorem d40 (l l':List Γ₀) (t:List (Q × Option Γ₀)) (u:List Γ₁) :
  Function.update (trSt l t u) .inp l'=trSt l' t u:=by
 funext k;cases k <;> simp [trSt]
theorem d19 (l:List Γ₀) (t t':List (Q × Option Γ₀)) (u:List Γ₁) :
  Function.update (trSt l t u) .tmp t'=trSt l t' u:=by
 funext k;cases k <;> simp [trSt]
theorem d78 (l:List Γ₀) (t:List (Q × Option Γ₀)) (u u':List Γ₁) :
  Function.update (trSt l t u) .out u'=trSt l t u':=by
 funext k;cases k <;> simp [trSt]
theorem d87 (l:List Γ₀) :
  (trSt l [] []:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) =
   Function.update (fun _=>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .inp l:=by
 funext k;cases k <;> simp [trSt]
theorem d121 (u:List Γ₁) :
  (trSt [] [] u:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) =
   Function.update (fun _=>[]:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .out u:=by
 funext k;cases k <;> simp [trSt]
abbrev TrCfg (Γ₀ Γ₁ Q:Type):Type:=TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
theorem d25 (o:TrS Γ₀ Q → Option Γ₁) (d:Option Γ₁) (hd:∀ _ : Γ₁,d≠none)
  (next:TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s:TrS Γ₀ Q) (l:List Γ₀)
  (t:List (Q × Option Γ₀)) (u:List Γ₁) :
  TM2.stepAux (d65 o d next) s (trSt l t u) =
   TM2.stepAux next s (trSt l t ((o s).toList++u)):=by
 cases ho:o s with
 | none=>cases d <;> simp [d65,TM2.stepAux,ho]
 | some y =>
  cases d with
  | none=>exact absurd rfl (hd y)
  | some dd=>simp [d65,TM2.stepAux,ho,trSt,d78]
variable (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin:Q → Option Γ₁) (q₀:Q)
 (d:Option Γ₁)
theorem d123 (s:TrS Γ₀ Q) (a : Γ₀) (l:List Γ₀) (t:List (Q × Option Γ₀))
  (u:List Γ₁) :
  TM2.step (trProg δ fin q₀ d) (⟨some false,s,trSt (a :: l) t u⟩:TrCfg Γ₀ Γ₁ Q) =
   some ⟨some false,((δ s.1 a).1,none,false),trSt l ((s.1,some a) :: t) u⟩:=by
 simp [TM2.step,trProg,TM2.stepAux,trSt,d40,d19]
theorem d142 (s:TrS Γ₀ Q) (t:List (Q × Option Γ₀)) (u:List Γ₁) :
  TM2.step (trProg δ fin q₀ d) (⟨some false,s,trSt [] t u⟩:TrCfg Γ₀ Γ₁ Q) =
   some ⟨some true,(q₀,none,false),trSt [] ((s.1,none) :: t) u⟩:=by
 simp [TM2.step,trProg,TM2.stepAux,trSt,d40,d19]
theorem d122 (hd:∀ _ : Γ₁,d≠none) (s:TrS Γ₀ Q) (e:Q × Option Γ₀)
  (t:List (Q × Option Γ₀)) (u:List Γ₁) :
  TM2.step (trProg δ fin q₀ d) (⟨some true,s,trSt [] (e :: t) u⟩:TrCfg Γ₀ Γ₁ Q) =
   some ⟨some true,(e.1,e.2,true),trSt [] t (trOut δ fin e++u)⟩:=by
 simp only [TM2.step,trProg,TM2.stepAux]
 have e1:(trSt [] (e :: t) u:∀ k,List (TrΓ Γ₀ Γ₁ Q k)) .tmp=e :: t:=rfl
 rw [e1]
 simp only [List.head?_cons,List.tail_cons,Bool.cond_true]
 rw [d19,d25 _ _ hd,d25 _ _ hd]
 simp [TM2.stepAux,trOut]
theorem d141 (s:TrS Γ₀ Q) (u:List Γ₁) :
  TM2.step (trProg δ fin q₀ d) (⟨some true,s,trSt [] [] u⟩:TrCfg Γ₀ Γ₁ Q) =
   some ⟨none,(q₀,none,false),trSt [] [] u⟩:=by
 simp [TM2.step,trProg,TM2.stepAux,trSt,d19]
theorem d140 (u:List Γ₁) :
  ∀ (l:List Γ₀) (t:List (Q × Option Γ₀)) (s:TrS Γ₀ Q),
   (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1]
     (some (⟨some false,s,trSt l t u⟩:TrCfg Γ₀ Γ₁ Q)) =
    some ⟨some true,(q₀,none,false),trSt [] ((d21 δ s.1 l).reverse++t) u⟩:=by
 intro l
 induction l with
 | nil=>intro t s;exact d142 δ fin q₀ d s t u
 | cons a l ih =>
  intro t s
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step (trProg δ fin q₀ d))
    (some (⟨some false,s,trSt (a :: l) t u⟩:TrCfg Γ₀ Γ₁ Q)) =
    some ⟨some false,((δ s.1 a).1,none,false),trSt l ((s.1,some a) :: t) u⟩ :=
   d123 δ fin q₀ d s a l t u
  rw [e,ih]
  simp [d21]
theorem d139 (hd:∀ _ : Γ₁,d≠none) :
  ∀ (t:List (Q × Option Γ₀)) (u:List Γ₁) (s:TrS Γ₀ Q),
   (flip bind (TM2.step (trProg δ fin q₀ d)))^[t.length+1]
     (some (⟨some true,s,trSt [] t u⟩:TrCfg Γ₀ Γ₁ Q)) =
    some ⟨none,(q₀,none,false),trSt [] [] (t.reverse.flatMap (trOut δ fin)++u)⟩:=by
 intro t
 induction t with
 | nil=>intro u s;exact d141 δ fin q₀ d s u
 | cons e t ih =>
  intro u s
  rw [List.length_cons,Function.iterate_succ_apply]
  have e':flip bind (TM2.step (trProg δ fin q₀ d))
    (some (⟨some true,s,trSt [] (e :: t) u⟩:TrCfg Γ₀ Γ₁ Q)) =
    some ⟨some true,(e.1,e.2,true),trSt [] t (trOut δ fin e++u)⟩ :=
   d122 δ fin q₀ d hd s e t u
  rw [e',ih]
  simp [List.flatMap_append]
theorem d138 [Fintype Γ₀] [Fintype Q] (hd:∀ _ : Γ₁,d≠none) (l:List Γ₀) :
  (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
    (some (initList (trM δ fin q₀ d) l)) =
   some (haltList (trM δ fin q₀ d) (fstRun2 δ fin q₀ l)):=by
 refine (congrArg (fun c=>(flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1+1 +
  (l.length+1)] (some c)) (d4 (trM δ fin q₀ d) l)).trans
  (Eq.trans ?_ (congrArg some (d5 (trM δ fin q₀ d) (fstRun2 δ fin q₀ l))).symm)
 show (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1+1+(l.length+1)]
  (some (⟨some false,(q₀,none,false),Function.update (fun _=>[]) .inp l⟩ :
   TrCfg Γ₀ Γ₁ Q)) =
  some (⟨none,(q₀,none,false),Function.update (fun _=>[]) .out (fstRun2 δ fin q₀ l)⟩ :
   TrCfg Γ₀ Γ₁ Q)
 have hA:(flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1]
   (some (⟨some false,(q₀,none,false),trSt l [] []⟩:TrCfg Γ₀ Γ₁ Q)) =
   some ⟨some true,(q₀,none,false),trSt [] (d21 δ q₀ l).reverse []⟩:=by
  have:=d140 δ fin q₀ d [] l [] (q₀,none,false)
  rw [List.append_nil] at this
  exact this
 have hB:(flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length+1+1]
   (some (⟨some true,(q₀,none,false),trSt [] (d21 δ q₀ l).reverse []⟩ :
    TrCfg Γ₀ Γ₁ Q)) =
   some ⟨none,(q₀,none,false),trSt [] [] (fstRun2 δ fin q₀ l)⟩:=by
  have:=d139 δ fin q₀ d hd (d21 δ q₀ l).reverse [] (q₀,none,false)
  rw [List.length_reverse,d57,List.reverse_reverse,d85,
   List.append_nil] at this
  exact this
 rw [Function.iterate_add_apply,← d87,hA,hB,d121]
theorem fst2_polyTime {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin:Q → Option βΓ) (q₀:Q) (h:∀ a,eb (f a)=fstRun2 δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f):=by
  classical
  let d:Option βΓ := if h:Nonempty βΓ then some (Classical.choice h) else none
  have hd:∀ _ : βΓ,d≠none:=by
    intro y
    have hn:Nonempty βΓ := ⟨y⟩
    simp [d,hn]
  exact ⟨{
    tm:=trM δ fin q₀ d
    inputAlphabet:=Equiv.refl _
    outputAlphabet:=Equiv.refl _
    time:=Polynomial.C 2 * Polynomial.X+Polynomial.C 3
    outputsFun:=fun a =>
      { steps:=(ea a).length+1+1+((ea a).length+1)
        evals_in_steps:=by
          have hm:∀ (γ : Type) (l:List γ),List.map (Equiv.refl γ).invFun l=l :=
            fun γ l=>by simp
          have:=d138 δ fin q₀ d hd (ea a)
          exact (congrArg (fun l=>(flip bind (TM2.step (trProg δ fin q₀ d)))^[(ea a).length +
            1+1+((ea a).length+1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l=>some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m:=by
          simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩
theorem fst_polyTime {α β αΓ βΓ Q:Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
  (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ) (fin:Q → Option βΓ) (q₀:Q)
  (h:∀ a,eb (f a)=fstRun δ fin q₀ (ea a)) :
  Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
 fst2_polyTime ea eb f (fun q a=>((δ q a).1,(δ q a).2,none)) fin q₀
  (fun a=>(h a).trans (d36 δ fin q₀ (ea a)))
end Lib.Machines
end
section
namespace Lib.Machines.Rev
open Turing PEqualNP.Library Lib.Machines
def prog:Unit → TM2.Stmt (fun _:Bool=>Bool) Unit (Option Bool)
 | () =>
  .pop false (fun _ o=>o)
   (.branch (fun s=>s.isSome)
    (.push true (fun s=>s.getD false) (.load (fun _=>none) (.goto fun _=>())))
    .halt)
def tm:FinTM2 where
  K:=Bool
  k₀:=false
  k₁:=true
  Γ _:=Bool
  Λ := Unit
  main:=()
  σ := Option Bool
  initialState:=none
  m:=prog
abbrev RCfg:Type:=TM2.Cfg (fun _:Bool=>Bool) Unit (Option Bool)
def st (l u:List Bool):Bool → List Bool:=fun k=>cond k u l
theorem d79 (l:List Bool) :
  st l []=Function.update (fun _=>([]:List Bool)) false l:=by
 funext k;cases k <;> simp [st]
theorem st_end (u:List Bool) :
  st [] u=Function.update (fun _=>([]:List Bool)) true u:=by
 funext k;cases k <;> simp [st]
theorem d103 (x:Bool) (l u:List Bool) :
  TM2.step prog (⟨some (),none,st (x :: l) u⟩:RCfg) =
   some ⟨some (),none,st l (x :: u)⟩:=by
 simp only [TM2.step,prog,TM2.stepAux]
 simp only [st,Bool.cond_false,List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,
  Option.getD_some,Option.some.injEq,TM2.Cfg.mk.injEq,true_and]
 funext k;cases k <;> simp [st]
theorem d129 (u:List Bool) :
  TM2.step prog (⟨some (),none,st [] u⟩:RCfg)=some ⟨none,none,st [] u⟩:=by
 simp only [TM2.step,prog,TM2.stepAux]
 simp only [st,Bool.cond_false,List.head?_nil,List.tail_nil,Option.isSome_none,
  Option.some.injEq,TM2.Cfg.mk.injEq,true_and]
 funext k;cases k <;> simp [st]
theorem loop:∀ (l u:List Bool),
  (flip bind (TM2.step prog))^[l.length+1] (some (⟨some (),none,st l u⟩:RCfg)) =
   some ⟨none,none,st [] (l.reverse++u)⟩:=by
 intro l
 induction l with
 | nil=>intro u;exact d129 u
 | cons x l ih =>
  intro u
  rw [List.length_cons,Function.iterate_succ_apply]
  have e:flip bind (TM2.step prog) (some (⟨some (),none,st (x :: l) u⟩:RCfg)) =
    some ⟨some (),none,st l (x :: u)⟩:=d103 x l u
  rw [e,ih]
  simp
theorem run (l:List Bool) :
  (flip bind (TM2.step prog))^[l.length+1] (some (initList tm l)) =
   some (haltList tm l.reverse):=by
 refine (congrArg (fun c=>(flip bind (TM2.step prog))^[l.length+1] (some c))
  (d4 tm l)).trans (Eq.trans ?_ (congrArg some (d5 tm l.reverse)).symm)
 show (flip bind (TM2.step prog))^[l.length+1]
  (some (⟨some (),none,Function.update (fun _=>[]) false l⟩:RCfg)) =
  some (⟨none,none,Function.update (fun _=>[]) true l.reverse⟩:RCfg)
 rw [← d79,loop,← st_end]
 simp
noncomputable def reverseComputable :
    TM2ComputableInPolyTime (fun x:List Bool=>x) (fun x:List Bool=>x)
      (fun x:List Bool=>x.reverse) where
  tm:=tm
  inputAlphabet:=Equiv.refl _
  outputAlphabet:=Equiv.refl _
  time:=Polynomial.X+1
  outputsFun a :=
    { steps:=a.length+1
      evals_in_steps:=by
        have hm:∀ l:List Bool,List.map (Equiv.refl Bool).invFun l=l:=fun l=>by simp
        exact (congrArg (fun l=>(flip bind (TM2.step prog))^[a.length+1]
          (some (initList tm l))) (hm a)).trans
          ((run a).trans (congrArg (fun l=>some (haltList tm l)) (hm a.reverse).symm))
      steps_le_m:=by simp }
end Lib.Machines.Rev
end
section
namespace Lib.Universal
def un (n:ℕ):List Bool:=List.replicate n true
def pairB (a b:List Bool):List Bool:=un a.length++false :: (a++b)
def unpairB (s:List Bool):List Bool × List Bool :=
 (((s.dropWhile id).tail).take (s.takeWhile id).length,
  ((s.dropWhile id).tail).drop (s.takeWhile id).length)
theorem unpairB_pairB (a b:List Bool):unpairB (pairB a b)=(a,b):=by
 have h1:(pairB a b).takeWhile id=un a.length:=by
  simp [pairB,un]
 have h2:(pairB a b).dropWhile id=false :: (a++b):=by
  simp [pairB,un]
 simp [unpairB,h1,h2,un]
end Lib.Universal
end
section
namespace Lib.Universal
def bflag (b:Bool):List Bool:=if b then [true] else []
@[simp] theorem un_zero:un 0=[]:=rfl
@[simp] theorem un_length (n:ℕ):(un n).length=n:=List.length_replicate
theorem un_succ (n:ℕ):un (n+1)=true :: un n:=rfl
def hd (s:List Bool):List Bool:=s.takeWhile id
def dropN (s:List Bool):List Bool:=(s.dropWhile id).tail
def sel (f a b:List Bool):List Bool:=if f=[] then a else b
def mulU (u v:List Bool):List Bool:=un (u.length * v.length)
def blank (s:List Bool):List Bool:=s.map fun _=>false
theorem hd_length (s:List Bool):(hd s).length ≤ s.length :=
 List.IsPrefix.length_le (List.takeWhile_prefix id)
theorem dropN_length (s:List Bool):(dropN s).length ≤ s.length:=by
 have h1:=List.IsSuffix.length_le (List.dropWhile_suffix (p:=id) (l:=s))
 simp only [dropN,List.length_tail]
 omega
theorem unpairB_length (s:List Bool) :
  2 * (unpairB s).1.length+(unpairB s).2.length ≤ s.length:=by
 have h:=congrArg List.length (List.takeWhile_append_dropWhile (p:=id) (l:=s))
 simp only [List.length_append] at h
 simp only [unpairB,List.length_take,List.length_drop,List.length_tail]
 omega
theorem pairB_length (a b:List Bool):(pairB a b).length=2 * a.length+b.length+1:=by
 simp [pairB];omega
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private theorem d39 {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
  {f f' : α → β} (h:ComputableInPolyTime ea eb f) (e:∀ a,f a=f' a) :
  ComputableInPolyTime ea eb f':=by
 obtain rfl:f=f':=funext e
 exact h
private theorem d119 {A B C:Type} (φl:A → Option C) (φr:B → Option C) (x:List A)
  (w:List B) :
  (x.map Sum.inl++w.map Sum.inr).filterMap (Sum.elim φl φr) =
   x.filterMap φl++w.filterMap φr:=by
 have h1:∀ x:List A,(x.map Sum.inl).filterMap (Sum.elim φl φr)=x.filterMap φl:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l ih=>simp [List.filterMap_cons,ih]
 have h2:∀ w:List B,(w.map Sum.inr).filterMap (Sum.elim φl φr)=w.filterMap φr:=by
  intro w;induction w with
  | nil=>rfl
  | cons a l ih=>simp [List.filterMap_cons,ih]
 rw [List.filterMap_append,h1,h2]
private theorem d100 {A C:Type} (g:A → C) (l:List A) :
  l.filterMap (fun a=>some (g a))=l.map g:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp [ih]
private theorem d160 {A C:Type} (l:List A) :
  l.filterMap (fun _:A=>(none:Option C))=[]:=by
 induction l with
 | nil=>rfl
 | cons a l ih=>simp
theorem d117 :
  ComputableInPolyTime encodePair (fun x:List Bool=>x)
   (fun p:List Bool × List Bool=>pairB p.1 p.2):=by
 have hA:ComputableInPolyTime encodePair encodePair
   (fun p:List Bool × List Bool=>(p.1,p.1++p.2)):=by
  refine d10 _ _ _
   (Sum.elim (fun b:Bool=>some (Sum.inl b)) (fun _:Bool=>none))
   (Sum.elim (fun b:Bool=>some (Sum.inr b)) (fun b:Bool=>some (Sum.inr b))) ?_
  rintro ⟨x,w⟩
  simp only [encodePair]
  rw [d119,d119,d100,d100,d100,d160]
  simp
 have hU:Lib.CPTs
   (fun a:List Bool=>a.map (fun _=>true)++[false]):=by
  refine fst_polyTime _ _ _ (fun (_:Unit) (_:Bool)=>((),some true))
   (fun _=>some false) () ?_
  intro a
  induction a with
  | nil=>rfl
  | cons b l ih =>
   simp only [fstRun,List.map_cons,List.cons_append,Option.toList_some] at ih ⊢
   rw [← ih];rfl
 refine d39 (cpt_comp (cpt_comp hA (d38 hU)) d74) ?_
 rintro ⟨x,w⟩
 simp [pairB,un]
theorem d35 :
  ComputableInPolyTime encodePair (fun x:List Bool=>x)
   (fun p:List Bool × List Bool=>if p.1=[] then p.2 else []):=by
 obtain ⟨c⟩:=d11 []
 have hI:=Iter.iter_polyTime (fun _:List Bool=>([]:List Bool)) c 0 (by simp)
 refine d39 (cpt_comp d84 hI) ?_
 rintro ⟨x,w⟩
 cases x with
 | nil=>simp
 | cons b l=>simp [Function.iterate_succ_apply']
theorem d62 :
  ComputableInPolyTime encodePair (fun x:List Bool=>x)
   (fun p:List Bool × List Bool=>if p.1=[] then [] else p.2):=by
 have hneg:Lib.CPTs
   (fun x:List Bool=>if x=[] then [true] else []) :=
  cpt_comp (cpt_pair cpt_id (d11 [true])) d35
 refine d39 (cpt_comp (d38 hneg) d35) ?_
 rintro ⟨x,w⟩
 cases x with
 | nil=>simp
 | cons b l=>simp
private def encT (u:List Bool):List Bool:=u.flatMap (fun b=>[true,b])
private def encF (v:List Bool):List Bool:=v.flatMap (fun b=>[false,b])
private def twD:Bool → Bool → Bool × Option Bool
 | true,true=>(true,some true)
 | _,_=>(false,none)
private theorem d137 (l:List Bool) :
  fstRun twD (fun _=>none) false l=[] ∧
   fstRun twD (fun _=>none) true l=l.takeWhile id:=by
 induction l with
 | nil=>exact ⟨rfl,rfl⟩
 | cons b l ih=>cases b <;> simp [fstRun,twD,ih.1,ih.2]
private def e0D:Bool → Bool → Bool × Option Bool × Option Bool
 | false,true=>(false,none,none)
 | false,false=>(true,none,none)
 | true,b=>(true,some false,some b)
private theorem d83 (l:List Bool) :
  fstRun2 e0D (fun _=>none) true l=encF l:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>simp [fstRun2,e0D,encF,ih]
private theorem d73 (l:List Bool) :
  fstRun2 e0D (fun _=>none) false l=encF (l.dropWhile id).tail:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>cases b <;> simp [fstRun2,e0D,ih,d83]
private def mkD:Bool × Bool → Bool → (Bool × Bool) × Option Bool
 | (d,false),t=>((d || !t,true),some (t || !d))
 | (d,true),b=>((d,false),some b)
private def mk (l:List Bool):List Bool:=fstRun mkD (fun _=>none) (false,false) l
private theorem d91 (q:Bool × Bool) (l:List Bool) :
  (fstRun mkD (fun _=>none) q l).length=l.length:=by
 induction l generalizing q with
 | nil=>rfl
 | cons b l ih=>obtain ⟨d,ph⟩:=q;cases ph <;> simp [fstRun,mkD,ih]
private theorem d130 (v:List Bool) :
  fstRun mkD (fun _=>none) (true,false) (encF v)=encF v:=by
 induction v with
 | nil=>rfl
 | cons b v ih=>simp [fstRun,mkD,encF] at ih ⊢;exact ih
private theorem d69 (u r:List Bool) :
  fstRun mkD (fun _=>none) (false,false) (encT u++r) =
   encT u++fstRun mkD (fun _=>none) (false,false) r:=by
 induction u with
 | nil=>rfl
 | cons b u ih=>simp [fstRun,mkD,encT] at ih ⊢;exact ih
private theorem mk_nil (u:List Bool):mk (encT u++encF [])=encT u++encF []:=by
 unfold mk;rw [d69];rfl
private theorem d153 (u:List Bool) (b:Bool) (v:List Bool) :
  mk (encT u++encF (b :: v))=encT (u++[b])++encF v:=by
 unfold mk
 rw [d69]
 have h:fstRun mkD (fun _=>none) (false,false) (encF (b :: v)) =
   true :: b :: encF v:=by
  have h':=d130 v
  simp [fstRun,mkD,encF] at h' ⊢
  exact h'
 rw [h]
 simp [encT]
private theorem d152 (k:ℕ):∀ u t:List Bool,
  mk^[k] (encT u++encF t)=encT (u++t.take k)++encF (t.drop k):=by
 induction k with
 | zero=>intro u t;simp
 | succ k ih =>
  intro u t
  rw [Function.iterate_succ_apply]
  cases t with
  | nil=>rw [mk_nil,ih];simp
  | cons b t=>rw [d153,ih];simp
private def dcD:Option Bool → Bool → Option Bool × Option (Bool ⊕ Bool)
 | none,t=>(some t,none)
 | some t,b=>(none,some (if t then Sum.inl b else Sum.inr b))
private theorem dcD_F (v:List Bool) :
  fstRun dcD (fun _=>none) none (encF v)=v.map Sum.inr:=by
 induction v with
 | nil=>rfl
 | cons b v ih=>simp [fstRun,dcD,encF] at ih ⊢;exact ih
private theorem dcD_T (u r:List Bool) :
  fstRun dcD (fun _=>none) none (encT u++r) =
   u.map Sum.inl++fstRun dcD (fun _=>none) none r:=by
 induction u with
 | nil=>rfl
 | cons b u ih=>simp [fstRun,dcD,encT] at ih ⊢;exact ih
private def rawDec (l:List (Bool ⊕ Bool)):List Bool × List Bool :=
 (l.filterMap Sum.getLeft?,l.filterMap Sum.getRight?)
private theorem d68 (u v:List Bool) :
  rawDec (u.map Sum.inl++v.map Sum.inr)=(u,v):=by
 have h1:∀ x:List Bool,(x.map (Sum.inl (β := Bool))).filterMap Sum.getLeft? = x:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l ih=>exact congrArg (a :: ·) ih
 have h2:∀ x:List Bool,(x.map (Sum.inr (α := Bool))).filterMap Sum.getLeft? = []:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l ih=>exact ih
 have h3:∀ x:List Bool,(x.map (Sum.inl (β := Bool))).filterMap Sum.getRight? = []:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l ih=>exact ih
 have h4:∀ x:List Bool,(x.map (Sum.inr (α := Bool))).filterMap Sum.getRight? = x:=by
  intro x;induction x with
  | nil=>rfl
  | cons a l ih=>exact congrArg (a :: ·) ih
 simp only [rawDec,List.filterMap_append,h1,h2,h3,h4,List.append_nil,List.nil_append]
theorem d34 :
  ComputableInPolyTime (fun x:List Bool=>x) encodePair unpairB:=by
 have hTw:Lib.CPTs
   (fun s:List Bool=>s.takeWhile id) :=
  fst_polyTime _ _ _ twD (fun _=>none) true (fun s=>(d137 s).2.symm)
 have hE0:Lib.CPTs
   (fun s:List Bool=>encF (s.dropWhile id).tail) :=
  fst2_polyTime _ _ _ e0D (fun _=>none) false (fun s=>(d73 s).symm)
 have hMk:Lib.CPTs mk :=
  fst_polyTime _ _ _ mkD (fun _=>none) (false,false) (fun _=>rfl)
 obtain ⟨cMk⟩:=hMk
 have hIt:=Iter.iter_polyTime mk cMk 0 (fun y=>by simp [mk,d91])
 have hDc:ComputableInPolyTime (fun x:List Bool=>x) (fun l:List (Bool ⊕ Bool)=>l)
   (fun l:List Bool=>fstRun dcD (fun _=>none) none l) :=
  fst_polyTime _ _ _ dcD (fun _=>none) none (fun _=>rfl)
 have hRaw:ComputableInPolyTime (fun l:List (Bool ⊕ Bool)=>l) encodePair rawDec:=by
  refine d10 _ _ _
   (fun s:Bool ⊕ Bool=>(Sum.getLeft? s).map Sum.inl)
   (fun s:Bool ⊕ Bool=>(Sum.getRight? s).map Sum.inr) ?_
  intro l
  simp only [rawDec,encodePair,List.map_filterMap]
 refine d39 (cpt_comp (cpt_comp (cpt_comp (cpt_pair hE0 hTw) hIt) hDc) hRaw) ?_
 intro s
 have h:=d152 (s.takeWhile id).length [] (s.dropWhile id).tail
 have e:encT []++encF (s.dropWhile id).tail=encF (s.dropWhile id).tail:=rfl
 rw [e] at h
 simp only [h,List.nil_append]
 rw [dcD_T,dcD_F,d68]
 rfl
end Lib.Universal
end
section
namespace Lib.Universal
open PEqualNP.Library Lib.Machines
private theorem cptc {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
  {f f' : α → β} (h:ComputableInPolyTime ea eb f) (e:∀ a,f a=f' a) :
  ComputableInPolyTime ea eb f':=by
 obtain rfl:f=f':=funext e
 exact h
private def hdD:Bool → Bool → Bool × Option Bool
 | true,true=>(true,some true)
 | _,_=>(false,none)
private theorem d159 (l:List Bool) :
  fstRun hdD (fun _=>none) false l=[] ∧
   fstRun hdD (fun _=>none) true l=l.takeWhile id:=by
 induction l with
 | nil=>exact ⟨rfl,rfl⟩
 | cons b l ih=>cases b <;> simp [fstRun,hdD,ih.1,ih.2]
theorem cpt_hd :
  Lib.CPTs hd :=
 fst_polyTime _ _ _ hdD (fun _=>none) true (fun s=>(d159 s).2.symm)
private def dnD:Bool → Bool → Bool × Option Bool
 | false,true=>(false,none)
 | false,false=>(true,none)
 | true,b=>(true,some b)
private theorem d135 (l:List Bool):fstRun dnD (fun _=>none) true l=l:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>simp [fstRun,dnD,ih]
private theorem d116 (l:List Bool) :
  fstRun dnD (fun _=>none) false l=(l.dropWhile id).tail:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>cases b <;> simp [fstRun,dnD,ih,d135]
theorem cpt_dropN :
  Lib.CPTs dropN :=
 fst_polyTime _ _ _ dnD (fun _=>none) false (fun s=>(d116 s).symm)
private def tlD:Bool → Bool → Bool × Option Bool
 | false,_=>(true,none)
 | true,b=>(true,some b)
private theorem d128 (l:List Bool):fstRun tlD (fun _=>none) true l=l:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>simp [fstRun,tlD,ih]
private theorem d102 (l:List Bool):fstRun tlD (fun _=>none) false l=l.tail:=by
 cases l with
 | nil=>rfl
 | cons b l=>simp [fstRun,tlD,d128]
theorem cpt_tail :
  Lib.CPTs
   (fun s:List Bool=>s.tail) :=
 fst_polyTime _ _ _ tlD (fun _=>none) false (fun s=>(d102 s).symm)
private theorem d118 (l:List Bool) :
  fstRun (fun (_:Unit) (_:Bool)=>((),some false)) (fun _=>none) () l=blank l:=by
 induction l with
 | nil=>rfl
 | cons b l ih=>simp [fstRun,blank] at ih ⊢;exact ih
theorem cpt_blank :
  Lib.CPTs blank :=
 fst_polyTime _ _ _ (fun (_:Unit) (_:Bool)=>((),some false)) (fun _=>none) ()
  (fun s=>(d118 s).symm)
theorem cpt_const (l:List Bool) :
  Lib.CPTs
   (fun _:List Bool=>l) :=
 d11 l
theorem cpt_unpairB1 :
  Lib.CPTs
   (fun s:List Bool=>(unpairB s).1) :=
 cptc (cpt_comp d34 d170) (fun _=>rfl)
theorem cpt_unpairB2 :
  Lib.CPTs
   (fun s:List Bool=>(unpairB s).2) :=
 cptc (cpt_comp d34 d169) (fun _=>rfl)
theorem cpt_app2 {u v:List Bool → List Bool}
  (hu:Lib.CPTs u)
  (hv:Lib.CPTs v) :
  Lib.CPTs
   (fun s=>u s++v s) :=
 cptc (cpt_comp (cpt_pair hu hv) d74) (fun _=>rfl)
theorem cpt_pairB2 {u v:List Bool → List Bool}
  (hu:Lib.CPTs u)
  (hv:Lib.CPTs v) :
  Lib.CPTs
   (fun s=>pairB (u s) (v s)) :=
 cptc (cpt_comp (cpt_pair hu hv) d117) (fun _=>rfl)
theorem cpt_sel {f a b:List Bool → List Bool}
  (hf:Lib.CPTs f)
  (ha:Lib.CPTs a)
  (hb:Lib.CPTs b) :
  Lib.CPTs
   (fun s=>sel (f s) (a s) (b s)):=by
 have h1:=cpt_comp (cpt_pair hf ha) d35
 have h2:=cpt_comp (cpt_pair hf hb) d62
 refine cptc (cpt_app2 h1 h2) ?_
 intro s
 by_cases h:f s=[] <;> simp [sel,h]
end Lib.Universal
end
namespace MachineBits
open PEqualNP.Library Lib Lib.Universal Lib.Machines
lemma q39 {f g:List Bool → List Bool} (hf:CPTs f) (h:∀ x,f x=g x):CPTs g:=by
 have:f=g:=funext h
 rwa [← this]
lemma q157:CPTs (fun s:List Bool=>s.reverse):=⟨Rev.reverseComputable⟩
lemma q121 {g cnt arg:List Bool → List Bool} (k:ℕ)
  (hg:CPTs g) (hgl:∀ s,(g s).length ≤ s.length+k)
  (hcnt:CPTs cnt) (harg:CPTs arg) :
  CPTs (fun s=>g^[(cnt s).length] (arg s)):=by
 obtain ⟨c⟩:=hg
 have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
   (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
  Iter.iter_polyTime g c k hgl
 exact q39 (cpt_comp (cpt_pair harg hcnt) hI) (fun _=>rfl)
lemma q213 {g cnt arg:List Bool → List Bool}
  (m:List Bool → ℕ) (a:ℕ)
  (hg:CPTs g)
  (hm:∀ y,m (g y) ≤ m y)
  (hgl:∀ y,(g y).length ≤ y.length+m y)
  (ha:∀ y,m y ≤ a * y.length+a)
  (hcnt:CPTs cnt) (harg:CPTs arg) :
  CPTs (fun s=>g^[(cnt s).length] (arg s)):=by
 obtain ⟨c⟩:=hg
 have hI:ComputableInPolyTime encodePair (fun x:List Bool=>x)
   (fun p:List Bool × List Bool=>g^[p.2.length] p.1) :=
  Iter.iter_polyTime_measure g c m a hm hgl ha
 exact q39 (cpt_comp (cpt_pair harg hcnt) hI) (fun _=>rfl)
lemma q7 (a b:List Bool):(pairB a b).length=2 * a.length+b.length+1:=by
 simp [pairB,un];omega
lemma q0 (y:List Bool) :
  2 * (unpairB y).1.length+(unpairB y).2.length ≤ y.length:=by
 dsimp only [unpairB]
 have hsplit:y=y.takeWhile id++y.dropWhile id:=(List.takeWhile_append_dropWhile (p:=id) (l:=y)).symm
 have hylen:y.length=(y.takeWhile id).length+(y.dropWhile id).length:=by
  conv_lhs=>rw [hsplit]
  exact List.length_append
 set a:=(y.takeWhile id).length
 set t:=(y.dropWhile id).tail
 have htlen:t.length ≤ (y.dropWhile id).length:=by
  dsimp only [t];cases y.dropWhile id <;> simp
 have htake:(t.take a).length=min a t.length:=List.length_take
 have hdrop:(t.drop a).length=t.length - a:=List.length_drop
 omega
lemma q18 {g cnt arg:List Bool → List Bool} (c:ℕ)
  (hg:CPTs g)
  (hw:∀ y,(unpairB (g y)).1=(unpairB y).1)
  (hgl:∀ y,(g y).length ≤ y.length+c * (unpairB y).1.length+c)
  (hcnt:CPTs cnt) (harg:CPTs arg) :
  CPTs (fun s=>g^[(cnt s).length] (arg s)):=by
 refine q213 (fun y=>c * (unpairB y).1.length+c) c hg
  (fun y=>by rw [hw y])
  (fun y=>by have:=hgl y;omega)
  (fun y=>by
   have h1:(unpairB y).1.length ≤ y.length:=by have:=q0 y;omega
   have h2:=Nat.mul_le_mul_left c h1
   omega)
  hcnt harg
def q47 (s:List Bool):List Bool:=List.replicate s.length true
lemma q152 (s:List Bool):(q47 s).length=s.length:=List.length_replicate
lemma q89:CPTs q47 :=
 fst_polyTime _ _ _ (fun (_:Unit) (_:Bool)=>((),some true)) (fun _=>none) () (fun s=>by
  induction s with
  | nil=>rfl
  | cons b l ih=>simp only [fstRun,q47,List.length_cons,List.replicate_succ];exact congrArg (true :: ·) ih)
def q79 (s:List Bool):List Bool :=
 pairB (unpairB s).1 ((unpairB s).2++(unpairB s).1)
lemma q169:CPTs q79 :=
 cpt_pairB2 cpt_unpairB1 (cpt_app2 cpt_unpairB2 cpt_unpairB1)
lemma q99 (a:List Bool):∀ k b,q79^[k] (pairB (q47 a) b)=pairB (q47 a) (b++un (k * a.length))
 | 0,b=>by simp [un]
 | k+1,b=>by
  rw [Function.iterate_succ_apply,q79,unpairB_pairB,q99 a k (b++q47 a)]
  congr 1
  simp [q47,un,List.append_assoc,← List.replicate_add,Nat.succ_mul,Nat.add_comm]
lemma q42 {u v:List Bool → List Bool} (hu:CPTs u) (hv:CPTs v) :
  CPTs (fun s=>mulU (u s) (v s)):=by
 have h1:CPTs (fun s=>q79^[(u s).length] (pairB (q47 (v s)) [])) :=
  q18 1 q169 (fun y=>by rw [q79,unpairB_pairB])
   (fun y=>by
    rw [q79,q7,List.length_append]
    have:=q0 y
    omega)
   hu (cpt_pairB2 (cpt_comp hv q89) (cpt_const []))
 have h2:=cpt_comp h1 cpt_unpairB2
 have heq:(fun s=>(unpairB (q79^[(u s).length] (pairB (q47 (v s)) []))).2)=(fun s=>mulU (u s) (v s)):=by
  funext s
  rw [q99,unpairB_pairB,List.nil_append];rfl
 rwa [heq] at h2
def q17 (s:List Bool):List Bool :=
 match s with
 | true :: _=>[true]
 | _=>[]
lemma q35:CPTs q17 :=
 fst_polyTime _ _ _
  (fun (st:Bool) (b:Bool)=>if st then (false,if b then some true else none) else (false,none))
  (fun _=>none) true (fun s=>by
   have hfalse:∀ l,fstRun (fun (st:Bool) (b:Bool) =>
     if st then (false,if b then some true else none) else (false,none))
     (fun _=>none) false l=[]:=by
    intro l;induction l with | nil=>rfl | cons b l ih=>simp [fstRun,ih]
   cases s with
   | nil=>rfl
   | cons b l=>cases b <;> simp [fstRun,q17,hfalse])
def takeN (lenU xs:List Bool):List Bool :=
 (unpairB (q47 lenU++false :: xs)).1
def dropN' (lenU xs:List Bool):List Bool :=
 (unpairB (q47 lenU++false :: xs)).2
lemma q12 (lenU xs:List Bool):takeN lenU xs=xs.take lenU.length:=by
 have h1:(q47 lenU++false :: xs).takeWhile id=q47 lenU:=by
  simp [q47]
 have h2:(q47 lenU++false :: xs).dropWhile id=false :: xs:=by
  simp [q47]
 simp [takeN,unpairB,h1,h2,q152]
lemma q40 (lenU xs:List Bool):dropN' lenU xs=xs.drop lenU.length:=by
 have h1:(q47 lenU++false :: xs).takeWhile id=q47 lenU:=by
  simp [q47]
 have h2:(q47 lenU++false :: xs).dropWhile id=false :: xs:=by
  simp [q47]
 simp [dropN',unpairB,h1,h2,q152]
lemma q24 {u v:List Bool → List Bool} (hu:CPTs u) (hv:CPTs v) :
  CPTs (fun s=>takeN (u s) (v s)) :=
 q39 (cpt_comp (cpt_app2 (cpt_comp hu q89) (cpt_app2 (cpt_const [false]) hv)) cpt_unpairB1) (fun _=>rfl)
lemma cpt_dropN' {u v:List Bool → List Bool} (hu:CPTs u) (hv:CPTs v) :
  CPTs (fun s=>dropN' (u s) (v s)) :=
 q39 (cpt_comp (cpt_app2 (cpt_comp hu q89) (cpt_app2 (cpt_const [false]) hv)) cpt_unpairB2) (fun _=>rfl)
def val:List Bool → ℕ
 | []=>0
 | b :: l=>b.toNat+2 * val l
lemma q124 (l:List Bool):val l < 2 ^ l.length:=by
 induction l with
 | nil=>simp [val]
 | cons b l ih =>
  simp only [val,List.length_cons,pow_succ]
  cases b <;> simp <;> omega
lemma q58 (a b:List Bool):val (a++b)=val a+2 ^ a.length * val b:=by
 induction a with
 | nil=>simp [val]
 | cons x l ih =>
  simp only [List.cons_append,val,List.length_cons,pow_succ,ih]
  ring
lemma q52 (k:ℕ):val (List.replicate k false)=0:=by
 induction k with
 | zero=>rfl
 | succ k ih=>simp [List.replicate_succ,val,ih]
lemma q37 (l:List Bool):val (blank l)=0:=by
 have h:blank l=List.replicate l.length false:=by
  induction l with
  | nil=>rfl
  | cons _ r ih=>simp [blank,List.replicate_succ,ih]
 rw [h,q52]
lemma q33 (l:List Bool):(blank l).length=l.length:=by
 induction l with
 | nil=>rfl
 | cons _ r ih=>simp [blank,ih]
lemma q140 (k:ℕ) (l:List Bool):val (l.take k)=val l % 2 ^ k:=by
 induction k generalizing l with
 | zero=>simp [val,Nat.mod_one]
 | succ k ih =>
  cases l with
  | nil=>simp [val]
  | cons b r =>
   simp only [List.take_succ_cons,val,ih,pow_succ']
   have hlt:b.toNat < 2:=by cases b <;> decide
   have hdiv:(b.toNat+2 * val r) % (2 * 2 ^ k)=b.toNat+2 * (val r % 2 ^ k):=by
    have h1:=Nat.div_add_mod (val r) (2 ^ k)
    have h2:val r % 2 ^ k < 2 ^ k:=Nat.mod_lt _ (by positivity)
    have h3:b.toNat+2 * val r=(2 * 2 ^ k) * (val r / 2 ^ k)+(b.toNat+2 * (val r % 2 ^ k)):=by
     linarith
    rw [h3,Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
   exact hdiv.symm
lemma q194 (n:ℕ):val n.bits=n:=by
 induction n using Nat.binaryRec with
 | zero=>simp [val]
 | bit b m ih =>
  by_cases h:b=false∧m=0
  · rcases h with ⟨rfl,rfl⟩;simp [val]
  ·
   rw [Nat.bits_append_bit m b (fun hm=>by subst hm;cases b <;> simp_all)]
   simp only [val,ih,Nat.bit]
   cases b <;> simp <;> omega
lemma q175 (k:ℕ) (hk:0 < k):k.bits.length=k.log2+1:=by
 induction k using Nat.strong_induction_on with
 | ind k ih =>
  by_cases h2:k < 2
  ·
   have hk1:k=1:=by omega
   subst hk1;decide
  ·
   have hdiv_pos:0 < k / 2:=by omega
   have hdiv_lt:k / 2 < k:=Nat.div_lt_self hk (by omega)
   have hlog:k.log2=(k / 2).log2+1:=by
    rw [Nat.log2_def];simp [show 2 ≤ k by omega]
   have hbits:k.bits=(decide (k % 2=1)) :: (k / 2).bits:=by
    have hdecomp:k=Nat.bit (decide (k % 2=1)) (k / 2):=by
     cases hmod:k % 2 with
     | zero=>simp [Nat.bit];omega
     | succ r =>
      have hr:r=0:=by omega
      subst hr;simp [Nat.bit];omega
    conv_lhs=>rw [hdecomp]
    rw [Nat.bits_append_bit (k / 2) (decide (k % 2=1)) (fun h0=>by omega)]
   rw [hbits,List.length_cons,ih (k / 2) hdiv_lt hdiv_pos,hlog]
def q28:List Bool → List Bool
 | []=>[true]
 | false :: l=>true :: l
 | true :: l=>false :: q28 l
lemma q182 (l:List Bool):val (q28 l)=val l+1:=by
 induction l with
 | nil=>simp [q28,val]
 | cons b l ih=>cases b <;> simp [q28,val,ih] <;> omega
lemma q183 (l:List Bool):(q28 l).length ≤ l.length+1:=by
 induction l with
 | nil=>simp [q28]
 | cons b l ih=>cases b <;> simp [q28] <;> omega
lemma q163 (n:ℕ):q28 n.bits=(n+1).bits:=by
 induction n using Nat.binaryRec with
 | zero=>decide
 | bit b m ih =>
  cases b with
  | false =>
   by_cases hm:m=0
   · subst hm;decide
   ·
    have h1:(Nat.bit false m).bits=false :: m.bits :=
     Nat.bits_append_bit m false (fun h=>(hm h).elim)
    have h2:Nat.bit false m+1=Nat.bit true m:=by simp [Nat.bit]
    have h3:(Nat.bit true m).bits=true :: m.bits :=
     Nat.bits_append_bit m true (fun _=>by simp)
    rw [h1,h2,h3,q28]
  | true =>
   have h1:(Nat.bit true m).bits=true :: m.bits :=
    Nat.bits_append_bit m true (fun _=>by simp)
   have h2:Nat.bit true m+1=Nat.bit false (m+1):=by simp [Nat.bit];omega
   have h3:(Nat.bit false (m+1)).bits=false :: (m+1).bits :=
    Nat.bits_append_bit (m+1) false (fun h=>by omega)
   rw [h1,h2,h3,q28,ih]
lemma q139:CPTs q28:=by
 let δ : Bool → Bool → Bool × Option Bool:=fun c b =>
  match c,b with
  | false,b=>(false,some b)
  | true,false=>(false,some true)
  | true,true=>(true,some false)
 let fin:Bool → Option Bool:=fun c=>if c then some true else none
 refine fst_polyTime _ _ _ δ fin true fun s => ?_
 have hfalse:∀ l,fstRun δ fin false l=l:=by
  intro l;induction l with | nil=>rfl | cons b r ih=>simp [fstRun,δ,fin,ih]
 have htrue:∀ l,fstRun δ fin true l=q28 l:=by
  intro l
  induction l with
  | nil=>rfl
  | cons b r ih=>cases b <;> simp [fstRun,δ,fin,q28,hfalse,ih]
 exact (htrue s).symm
def q48 (u:List Bool):List Bool:=q28^[u.length] []
lemma q71 (u:List Bool):q48 u=u.length.bits:=by
 dsimp only [q48]
 have h:∀ k,q28^[k] []=k.bits:=by
  intro k
  induction k with
  | zero=>rfl
  | succ k ih=>rw [Function.iterate_succ_apply',ih,q163]
 exact h u.length
lemma q41:CPTs q48 :=
 q121 1 q139 q183 cpt_id (cpt_const [])
def padW (wU x:List Bool):List Bool:=takeN wU (x++blank wU)
lemma q19 (wU x:List Bool):(padW wU x).length=wU.length:=by
 dsimp only [padW]
 rw [q12,List.length_take,List.length_append,q33]
 omega
lemma q26 (wU x:List Bool):val (padW wU x)=val x % 2 ^ wU.length:=by
 dsimp only [padW]
 rw [q12,q140,q58,q37,mul_zero,add_zero]
lemma q13 {uw ux:List Bool → List Bool} (hw:CPTs uw) (hx:CPTs ux) :
  CPTs (fun s=>padW (uw s) (ux s)) :=
 q24 hw (cpt_app2 hx (cpt_comp hw cpt_blank))
def natW (wU u:List Bool):List Bool:=padW wU (q48 u)
lemma q54 (wU u:List Bool):(natW wU u).length=wU.length:=q19 wU _
lemma q114 (wU u:List Bool):val (natW wU u)=u.length % 2 ^ wU.length:=by
 dsimp only [natW];rw [q26,q71,q194]
lemma q50 {uw uu:List Bool → List Bool} (hw:CPTs uw) (hu:CPTs uu) :
  CPTs (fun s=>natW (uw s) (uu s)) :=
 q13 hw (cpt_comp hu q41)
def q77 (x:List Bool):List Bool:=x.map (!·)
lemma q195 (x:List Bool):val (q77 x)+val x+1=2 ^ x.length:=by
 induction x with
 | nil=>simp [q77,val]
 | cons b l ih =>
  simp only [q77,List.map_cons,val,List.length_cons,pow_succ] at ih ⊢
  cases b <;> simp <;> omega
lemma q204:CPTs q77 :=
 fst_polyTime _ _ _ (fun (_:Unit) (b:Bool)=>((),some (!b))) (fun _=>none) () fun s=>by
  induction s with
  | nil=>rfl
  | cons b l ih=>simp only [fstRun,q77,List.map_cons];exact congrArg ((!b) :: ·) ih
def incW (wU x:List Bool):List Bool:=takeN wU (q28 (padW wU x))
lemma q215 (wU x:List Bool):(incW wU x).length=wU.length:=by
 dsimp only [incW];rw [q12,List.length_take]
 have h1:(padW wU x).length ≤ (q28 (padW wU x)).length:=by
  have:∀ l,l.length ≤ (q28 l).length:=by
   intro l;induction l with | nil=>simp [q28] | cons b r ih=>cases b <;> simp [q28] <;> omega
  exact this _
 rw [q19] at h1;omega
lemma q214 (wU x:List Bool):val (incW wU x)=(val x+1) % 2 ^ wU.length:=by
 dsimp only [incW]
 rw [q12,q140,q182,q26,Nat.mod_add_mod]
lemma q218 {uw ux:List Bool → List Bool} (hw:CPTs uw) (hx:CPTs ux) :
  CPTs (fun s=>incW (uw s) (ux s)) :=
 q24 hw (cpt_comp (q13 hw hx) q139)
def negW (wU x:List Bool):List Bool:=incW wU (q77 (padW wU x))
lemma q113 (wU x:List Bool) :
  ((val (negW wU x):ℤ) ≡ -(val x:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
 dsimp only [negW]
 rw [q214]
 have hnot:=q195 (padW wU x)
 rw [q19] at hnot
 have h1:val (q77 (padW wU x))+1=2 ^ wU.length - val (padW wU x):=by omega
 have h2:((val (q77 (padW wU x))+1) % 2 ^ wU.length:ℤ) ≡
   ((val (q77 (padW wU x))+1:ℕ):ℤ) [ZMOD (2:ℤ) ^ wU.length]:=by
  exact_mod_cast (Nat.mod_modEq (val (q77 (padW wU x))+1) (2 ^ wU.length))
 have h3:((val (q77 (padW wU x))+1:ℕ):ℤ)+(val (padW wU x):ℤ)=(2:ℤ) ^ wU.length:=by
  exact_mod_cast (by omega:val (q77 (padW wU x))+1+val (padW wU x)=2 ^ wU.length)
 have h4:((val (padW wU x):ℕ):ℤ) ≡ (val x:ℤ) [ZMOD (2:ℤ) ^ wU.length]:=by
  rw [q26];exact_mod_cast (Nat.mod_modEq (val x) (2 ^ wU.length))
 have h5:((val (q77 (padW wU x))+1:ℕ):ℤ) ≡ -(val (padW wU x):ℤ) [ZMOD (2:ℤ) ^ wU.length]:=by
  rw [Int.modEq_iff_dvd]
  have : -(val (padW wU x):ℤ) - ((val (q77 (padW wU x))+1:ℕ):ℤ) = -((2:ℤ) ^ wU.length):=by linarith
  rw [this];exact dvd_neg.2 (dvd_refl _)
 exact h2.trans (h5.trans h4.neg)
lemma q120 {uw ux:List Bool → List Bool} (hw:CPTs uw) (hx:CPTs ux) :
  CPTs (fun s=>negW (uw s) (ux s)) :=
 q218 hw (cpt_comp (q13 hw hx) q204)
def shl1W (wU x:List Bool):List Bool:=takeN wU (false :: padW wU x)
lemma q176 (wU x:List Bool):(shl1W wU x).length=wU.length:=by
 dsimp only [shl1W];rw [q12,List.length_take,List.length_cons,q19];omega
lemma q206 (wU x:List Bool):val (shl1W wU x)=(2 * val x) % 2 ^ wU.length:=by
 dsimp only [shl1W]
 rw [q12,q140,val,Bool.toNat_false,zero_add,q26,Nat.mul_mod_mod]
lemma q210 {uw ux:List Bool → List Bool} (hw:CPTs uw) (hx:CPTs ux) :
  CPTs (fun s=>shl1W (uw s) (ux s)) :=
 q24 hw (cpt_app2 (cpt_const [false]) (q13 hw hx))
def q16 (f:List Bool):List Bool:=sel f [false] [true]
lemma q73 {uf:List Bool → List Bool} (hf:CPTs uf) :
  CPTs (fun s=>q16 (uf s)) :=
 cpt_sel hf (cpt_const [false]) (cpt_const [true])
def xorF (a b:List Bool):List Bool:=sel a (sel b [] [true]) (sel b [true] [])
def majF (a b c:List Bool):List Bool :=
 sel a (sel b [] (sel c [] [true])) (sel b (sel c [] [true]) [true])
lemma q200 {ua ub:List Bool → List Bool} (ha:CPTs ua) (hb:CPTs ub) :
  CPTs (fun s=>xorF (ua s) (ub s)) :=
 cpt_sel ha (cpt_sel hb (cpt_const []) (cpt_const [true])) (cpt_sel hb (cpt_const [true]) (cpt_const []))
lemma q217 {ua ub uc:List Bool → List Bool} (ha:CPTs ua) (hb:CPTs ub) (hc:CPTs uc) :
  CPTs (fun s=>majF (ua s) (ub s) (uc s)) :=
 cpt_sel ha (cpt_sel hb (cpt_const []) (cpt_sel hc (cpt_const []) (cpt_const [true])))
  (cpt_sel hb (cpt_sel hc (cpt_const []) (cpt_const [true])) (cpt_const [true]))
def q123 (y:List Bool):List Bool :=
 let a:=(unpairB y).1
 let r1:=(unpairB y).2
 let b:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let c:=(unpairB r2).1
 let acc:=(unpairB r2).2
 let ba:=q17 a
 let bb:=q17 b
 let bc:=q17 c
 let sBit:=q16 (xorF (xorF ba bb) bc)
 let c':=majF ba bb bc
 pairB a.tail (pairB b.tail (pairB c' (sBit++acc)))
lemma q193 (y:List Bool):(q123 y).length ≤ y.length+6:=by
 dsimp only [q123]
 have h1:=q0 y
 have h2:=q0 (unpairB y).2
 have h3:=q0 (unpairB (unpairB y).2).2
 rw [q7,q7,q7,List.length_append]
 have ha:(unpairB y).1.tail.length ≤ (unpairB y).1.length:=by cases (unpairB y).1 <;> simp
 have hb:(unpairB (unpairB y).2).1.tail.length ≤ (unpairB (unpairB y).2).1.length:=by
  cases (unpairB (unpairB y).2).1 <;> simp
 have hs:(q16 (xorF (xorF (q17 (unpairB y).1) (q17 (unpairB (unpairB y).2).1))
   (q17 (unpairB (unpairB (unpairB y).2).2).1))).length=1:=by
  unfold q16 sel;split_ifs <;> rfl
 have hc:(majF (q17 (unpairB y).1) (q17 (unpairB (unpairB y).2).1)
   (q17 (unpairB (unpairB (unpairB y).2).2).1)).length ≤ 1:=by
  unfold majF sel;split_ifs <;> simp
 omega
lemma q192:CPTs q123:=by
 have hA:CPTs (fun y=>(unpairB y).1):=cpt_unpairB1
 have hR1:CPTs (fun y=>(unpairB y).2):=cpt_unpairB2
 have hB:CPTs (fun y=>(unpairB (unpairB y).2).1):=q39 (cpt_comp hR1 cpt_unpairB1) (fun _=>rfl)
 have hR2:CPTs (fun y=>(unpairB (unpairB y).2).2):=q39 (cpt_comp hR1 cpt_unpairB2) (fun _=>rfl)
 have hC:CPTs (fun y=>(unpairB (unpairB (unpairB y).2).2).1):=q39 (cpt_comp hR2 cpt_unpairB1) (fun _=>rfl)
 have hAcc:CPTs (fun y=>(unpairB (unpairB (unpairB y).2).2).2):=q39 (cpt_comp hR2 cpt_unpairB2) (fun _=>rfl)
 have hba:=cpt_comp hA q35
 have hbb:=cpt_comp hB q35
 have hbc:=cpt_comp hC q35
 have hs:=q73 (q200 (q200 hba hbb) hbc)
 have hc':=q217 hba hbb hbc
 exact q39 (cpt_pairB2 (cpt_comp hA cpt_tail)
  (cpt_pairB2 (cpt_comp hB cpt_tail) (cpt_pairB2 hc' (cpt_app2 hs hAcc)))) (fun _=>rfl)
def addW (wU a b:List Bool):List Bool :=
 let fin:=q123^[wU.length] (pairB (padW wU a) (pairB (padW wU b) (pairB [] [])))
 (unpairB (unpairB (unpairB fin).2).2).2.reverse
lemma q108 (k:ℕ):∀ (a b:List Bool) (c:Bool) (acc:List Bool),
  a.length=k → b.length=k →
  ∃ (acc':List Bool) (c':Bool),
   q123^[k] (pairB a (pairB b (pairB (if c then [true] else []) acc))) =
    pairB [] (pairB [] (pairB (if c' then [true] else []) (acc'.reverse++acc))) ∧
   acc'.length=k ∧
   val acc'+2 ^ k * c'.toNat=val a+val b+c.toNat:=by
 induction k with
 | zero =>
  intro a b c acc ha hb
  cases a;cases b
  · exact ⟨[],c,by simp,rfl,by simp [val]⟩
  · simp at hb
  · simp at ha
 | succ k ih =>
  intro a b c acc ha hb
  cases a with
  | nil=>simp at ha
  | cons ba ar =>
   cases b with
   | nil=>simp at hb
   | cons bb br =>
    rw [Function.iterate_succ_apply]
    have hstep:q123 (pairB (ba :: ar) (pairB (bb :: br) (pairB (if c then [true] else []) acc))) =
      pairB ar (pairB br (pairB (if ((ba && bb) || (c && (ba || bb))) then [true] else [])
       (((xor (xor ba bb) c) :: acc)))):=by
     dsimp only [q123]
     simp only [unpairB_pairB,List.tail_cons]
     cases ba <;> cases bb <;> cases c <;> rfl
    rw [hstep]
    obtain ⟨acc',c',hiter,hlen,hval⟩:=ih ar br ((ba && bb) || (c && (ba || bb)))
     ((xor (xor ba bb) c) :: acc) (by simpa using ha) (by simpa using hb)
    refine ⟨(xor (xor ba bb) c) :: acc',c',?_,by simp [hlen],?_⟩
    · rw [hiter];simp
    ·
     simp only [val,pow_succ']
     have hbit:(xor (xor ba bb) c).toNat+2 * ((ba && bb) || (c && (ba || bb))).toNat =
       ba.toNat+bb.toNat+c.toNat:=by
      cases ba <;> cases bb <;> cases c <;> decide
     linarith
lemma q180 (wU a b:List Bool) :
  (addW wU a b).length=wU.length∧val (addW wU a b)=(val a+val b) % 2 ^ wU.length:=by
 dsimp only [addW]
 obtain ⟨acc',c',hiter,hlen,hval⟩ :=
  q108 wU.length (padW wU a) (padW wU b) false [] (q19 wU a) (q19 wU b)
 simp only [Bool.false_eq_true,↓reduceIte,List.append_nil,Bool.toNat_false,add_zero] at hiter hval
 rw [hiter]
 simp only [unpairB_pairB,List.reverse_reverse]
 refine ⟨hlen,?_⟩
 have hlt:val acc' < 2 ^ wU.length:=by rw [← hlen];exact q124 acc'
 have hmod1:val acc'=(val (padW wU a)+val (padW wU b)) % 2 ^ wU.length:=by
  have:val (padW wU a)+val (padW wU b)=2 ^ wU.length * c'.toNat+val acc':=by linarith
  rw [this,Nat.mul_add_mod,Nat.mod_eq_of_lt hlt]
 rw [hmod1,q26,q26,Nat.mod_add_mod,Nat.add_mod_mod]
lemma q36 (wU a b:List Bool):(addW wU a b).length=wU.length:=(q180 wU a b).1
lemma q205 (wU a b:List Bool):val (addW wU a b)=(val a+val b) % 2 ^ wU.length :=
 (q180 wU a b).2
lemma q98 (wU a b:List Bool) :
  ((val (addW wU a b):ℤ) ≡ (val a:ℤ)+(val b:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
 rw [q205];exact_mod_cast (Nat.mod_modEq (val a+val b) (2 ^ wU.length))
lemma q82 {uw ua ub:List Bool → List Bool} (hw:CPTs uw) (ha:CPTs ua) (hb:CPTs ub) :
  CPTs (fun s=>addW (uw s) (ua s) (ub s)):=by
 have hfin:=q121 6 q192 q193 hw
  (cpt_pairB2 (q13 hw ha) (cpt_pairB2 (q13 hw hb) (cpt_const (pairB [] []))))
 exact cpt_comp (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) q157
def subW (wU a b:List Bool):List Bool:=addW wU a (negW wU b)
lemma q63 (wU a b:List Bool):(subW wU a b).length=wU.length:=q36 wU _ _
lemma q142 (wU a b:List Bool) :
  ((val (subW wU a b):ℤ) ≡ (val a:ℤ) - (val b:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
 dsimp only [subW]
 have h1:=q98 wU a (negW wU b)
 have h2:=q113 wU b
 simpa only [sub_eq_add_neg] using h1.trans (Int.ModEq.add_left _ h2)
lemma q83 (wU a b:List Bool) (ha:val a < 2 ^ wU.length) (hge:val b ≤ val a) :
  val (subW wU a b)=val a - val b:=by
 have hmod:=q142 wU a b
 have hlt1:val (subW wU a b) < 2 ^ wU.length:=by rw [← q63 wU a b];exact q124 _
 have hlt2:val a - val b < 2 ^ wU.length:=by omega
 have hcast:((val a - val b:ℕ):ℤ)=(val a:ℤ) - (val b:ℤ):=by omega
 rw [← hcast] at hmod
 have hnat:val (subW wU a b) ≡ val a - val b [MOD 2 ^ wU.length]:=by exact_mod_cast hmod
 rw [Nat.ModEq,Nat.mod_eq_of_lt hlt1,Nat.mod_eq_of_lt hlt2] at hnat
 exact hnat
lemma q148 {uw ua ub:List Bool → List Bool} (hw:CPTs uw) (ha:CPTs ua) (hb:CPTs ub) :
  CPTs (fun s=>subW (uw s) (ua s) (ub s)) :=
 q82 hw ha (q120 hw hb)
def q116 (y:List Bool):List Bool :=
 let wU:=(unpairB y).1
 let r1:=(unpairB y).2
 let bRem:=(unpairB r1).1
 let r2:=(unpairB r1).2
 let aSh:=(unpairB r2).1
 let acc:=(unpairB r2).2
 let acc':=sel (q17 bRem) (padW wU acc) (addW wU acc aSh)
 let aSh':=shl1W wU aSh
 pairB wU (pairB bRem.tail (pairB aSh' acc'))
lemma q186:CPTs q116:=by
 have hw:=cpt_unpairB1
 have hr1:=cpt_unpairB2
 have hb:=cpt_comp hr1 cpt_unpairB1
 have hr2:=cpt_comp hr1 cpt_unpairB2
 have ha:=cpt_comp hr2 cpt_unpairB1
 have hacc:=cpt_comp hr2 cpt_unpairB2
 have hacc':=cpt_sel (cpt_comp hb q35) (q13 hw hacc) (q82 hw hacc ha)
 have ha':=q210 hw ha
 exact cpt_pairB2 hw (cpt_pairB2 (cpt_comp hb cpt_tail) (cpt_pairB2 ha' hacc'))
def mulW (wU a b:List Bool):List Bool :=
 let fin:=q116^[wU.length] (pairB wU (pairB (padW wU b) (pairB (padW wU a) (blank wU))))
 (unpairB (unpairB (unpairB fin).2).2).2
lemma q32 {uw ua ub:List Bool → List Bool} (hw:CPTs uw) (ha:CPTs ua) (hb:CPTs ub) :
  CPTs (fun s=>mulW (uw s) (ua s) (ub s)):=by
 have hfin:=q18 4 q186
  (fun y=>by dsimp only [q116];rw [unpairB_pairB])
  (fun y=>by
   dsimp only [q116]
   set wU:=(unpairB y).1;set r1:=(unpairB y).2
   set bRem:=(unpairB r1).1;set r2:=(unpairB r1).2
   set aSh:=(unpairB r2).1;set acc:=(unpairB r2).2
   have h1:2 * wU.length+r1.length ≤ y.length:=q0 y
   have h2:2 * bRem.length+r2.length ≤ r1.length:=q0 r1
   have h3:2 * aSh.length+acc.length ≤ r2.length:=q0 r2
   rw [q7,q7,q7,q176]
   have hbt:bRem.tail.length ≤ bRem.length:=by cases bRem <;> simp
   have hacc:(sel (q17 bRem) (padW wU acc) (addW wU acc aSh)).length=wU.length:=by
    unfold sel;split_ifs
    · exact q19 _ _
    · exact q36 _ _ _
   omega)
  hw (cpt_pairB2 hw (cpt_pairB2 (q13 hw hb) (cpt_pairB2 (q13 hw ha) (cpt_comp hw cpt_blank))))
 exact q39 (cpt_comp (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
lemma q102 (wU:List Bool) (k:ℕ):∀ (bRem aSh acc:List Bool),
  bRem.length=k → aSh.length=wU.length → acc.length=wU.length →
  ∃ aSh' acc',
   q116^[k] (pairB wU (pairB bRem (pairB aSh acc))) =
    pairB wU (pairB [] (pairB aSh' acc')) ∧
   acc'.length=wU.length ∧
   val acc' % 2 ^ wU.length=(val acc+val aSh * val bRem) % 2 ^ wU.length:=by
 induction k with
 | zero =>
  intro bRem aSh acc hb _ hacc
  cases bRem
  · exact ⟨aSh,acc,rfl,hacc,by simp [val]⟩
  · simp at hb
 | succ k ih =>
  intro bRem aSh acc hb ha hacc
  cases bRem with
  | nil=>simp at hb
  | cons bb br =>
   rw [Function.iterate_succ_apply]
   have hstep:q116 (pairB wU (pairB (bb :: br) (pairB aSh acc))) =
     pairB wU (pairB br (pairB (shl1W wU aSh) (if bb then addW wU acc aSh else padW wU acc))):=by
    dsimp only [q116]
    simp only [unpairB_pairB,List.tail_cons]
    cases bb <;> rfl
   rw [hstep]
   have hacc1_len:(if bb then addW wU acc aSh else padW wU acc).length=wU.length:=by
    cases bb <;> simp [q36,q19]
   obtain ⟨aSh',acc',hiter,hlen',hval'⟩ :=
    ih br (shl1W wU aSh) (if bb then addW wU acc aSh else padW wU acc)
     (by simpa using hb) (q176 wU aSh) hacc1_len
   refine ⟨aSh',acc',hiter,hlen',?_⟩
   rw [hval',q206]
   have hmod1:val (if bb then addW wU acc aSh else padW wU acc) ≡
     val acc+val aSh * bb.toNat [MOD 2 ^ wU.length]:=by
    cases bb with
    | false =>
     simp only [Bool.false_eq_true,↓reduceIte,Bool.toNat_false,mul_zero,add_zero,q26]
     exact Nat.mod_modEq _ _
    | true =>
     simp only [↓reduceIte,Bool.toNat_true,mul_one,q205]
     exact Nat.mod_modEq _ _
   have hmod2:((2 * val aSh) % 2 ^ wU.length) * val br ≡ (2 * val aSh) * val br [MOD 2 ^ wU.length] :=
    (Nat.mod_modEq _ _).mul_right _
   have hcomb:=hmod1.add hmod2
   have hrew:val acc+val aSh * bb.toNat+2 * val aSh * val br =
     val acc+val aSh * (bb.toNat+2 * val br):=by ring
   rw [hrew] at hcomb
   simpa only [Nat.ModEq,val] using hcomb
lemma q179 (wU a b:List Bool) :
  (mulW wU a b).length=wU.length∧val (mulW wU a b)=(val a * val b) % 2 ^ wU.length:=by
 dsimp only [mulW]
 obtain ⟨aSh',acc',hiter,hlen,hval⟩ :=
  q102 wU wU.length (padW wU b) (padW wU a) (blank wU)
   (q19 wU b) (q19 wU a) (q33 wU)
 rw [hiter]
 simp only [unpairB_pairB]
 refine ⟨hlen,?_⟩
 rw [q37,zero_add,q26,q26] at hval
 have hlt:val acc' < 2 ^ wU.length:=by rw [← hlen];exact q124 acc'
 rw [Nat.mod_eq_of_lt hlt] at hval
 rw [hval,Nat.mod_mul_mod,Nat.mul_mod_mod]
lemma q93 (wU a b:List Bool):(mulW wU a b).length=wU.length:=(q179 wU a b).1
lemma q115 (wU a b:List Bool):val (mulW wU a b)=(val a * val b) % 2 ^ wU.length :=
 (q179 wU a b).2
lemma q55 (wU a b:List Bool) :
  ((val (mulW wU a b):ℤ) ≡ (val a:ℤ) * (val b:ℤ) [ZMOD (2:ℤ) ^ wU.length]):=by
 rw [q115];exact_mod_cast (Nat.mod_modEq (val a * val b) (2 ^ wU.length))
def q87 (l:List Bool):List Bool:=l.dropWhile (fun b => !b)
lemma q159:CPTs q87:=by
 let δ : Bool → Bool → Bool × Option Bool:=fun st b =>
  match st,b with
  | true,b=>(true,some b)
  | false,false=>(false,none)
  | false,true=>(true,some true)
 refine fst_polyTime _ _ _ δ (fun _=>none) false fun s => ?_
 have htrue:∀ l,fstRun δ (fun _=>none) true l=l:=by
  intro l;induction l with | nil=>rfl | cons b r ih=>simp [fstRun,δ,ih]
 have hfalse:∀ l,fstRun δ (fun _=>none) false l=q87 l:=by
  intro l
  induction l with
  | nil=>rfl
  | cons b r ih=>cases b <;> simp [fstRun,δ,q87,htrue,ih]
 exact (hfalse s).symm
def q141 (x:List Bool):List Bool:=(q87 x.reverse).reverse
lemma q167:CPTs q141 :=
 q39 (cpt_comp (cpt_comp q157 q159) q157) (fun _=>rfl)
lemma q109 (x:List Bool):q141 x=(val x).bits:=by
 induction x using List.reverseRecOn with
 | nil=>rfl
 | append_singleton l b ih =>
  dsimp only [q141,q87] at ih ⊢
  rw [List.reverse_append,List.reverse_singleton,List.singleton_append]
  cases b with
  | false =>
   simp only [List.dropWhile_cons,Bool.not_false,↓reduceIte]
   rw [ih,q58]
   simp [val]
  | true =>
   simp only [List.dropWhile_cons,Bool.not_true,Bool.false_eq_true,↓reduceIte,
    List.reverse_cons,List.reverse_reverse]
   have hpos:∀ r:List Bool,(val (r++[true])).bits=r++[true]:=by
    intro r
    induction r with
    | nil=>decide
    | cons c r ihr =>
     have hval:val ((c :: r)++[true])=Nat.bit c (val (r++[true])):=by
      simp only [List.cons_append,val,Nat.bit]
      cases c <;> simp <;> omega
     have hne:val (r++[true])≠0:=by
      rw [q58];simp [val]
     rw [hval,Nat.bits_append_bit _ c (fun h0=>(hne h0).elim),ihr]
     rfl
   exact (hpos l).symm
def q49 (s:List Bool):List Bool:=s.filter id
lemma q150:CPTs q49 :=
 fst_polyTime _ _ _ (fun (_:Unit) (b:Bool)=>((),if b then some true else none))
  (fun _=>none) () fun s=>by
   induction s with
   | nil=>rfl
   | cons b r ih=>cases b <;> simp [fstRun,q49] at ih ⊢ <;> exact ih
def q112 (u:List Bool):List Bool:=if u.length % 2=1 then [true] else []
lemma q137:CPTs q112:=by
 let δ : Bool → Bool → Bool × Option Bool:=fun st _=>(!st,none)
 let fin:Bool → Option Bool:=fun st=>if st then some true else none
 refine fst_polyTime _ _ _ δ fin false fun s => ?_
 have hrun:∀ (st:Bool) (l:List Bool),
   fstRun δ fin st l=if (xor st (decide (l.length % 2=1))) then [true] else []:=by
  intro st l
  induction l generalizing st with
  | nil=>cases st <;> rfl
  | cons _ r ih =>
   simp only [fstRun,δ,List.length_cons,ih]
   cases st <;> by_cases h:r.length % 2=1 <;> simp [h] <;> omega
 simpa [q112] using (hrun false s).symm
def q132 (y:List Bool):List Bool :=
 let wU:=(unpairB y).1
 let r1:=(unpairB y).2
 let base:=(unpairB r1).1
 let acc:=(unpairB r1).2
 pairB wU (pairB base (mulW wU acc base))
lemma q185:CPTs q132:=by
 have hw:=cpt_unpairB1
 have hr1:=cpt_unpairB2
 have hb:=cpt_comp hr1 cpt_unpairB1
 have hacc:=cpt_comp hr1 cpt_unpairB2
 exact cpt_pairB2 hw (cpt_pairB2 hb (q32 hw hacc hb))
def powW (wU baseW eU:List Bool):List Bool :=
 let fin:=q132^[eU.length] (pairB wU (pairB (padW wU baseW) (natW wU [true])))
 (unpairB (unpairB fin).2).2
lemma q202 {uw ub ue:List Bool → List Bool} (hw:CPTs uw) (hb:CPTs ub) (he:CPTs ue) :
  CPTs (fun s=>powW (uw s) (ub s) (ue s)):=by
 have hfin:=q18 6 q185
  (fun y=>by dsimp only [q132];rw [unpairB_pairB])
  (fun y=>by
   dsimp only [q132]
   have h1:=q0 y
   have h2:=q0 (unpairB y).2
   rw [q7,q7,q93]
   omega)
  he (cpt_pairB2 hw (cpt_pairB2 (q13 hw hb) (q50 hw (cpt_const [true]))))
 exact q39 (cpt_comp (cpt_comp hfin cpt_unpairB2) cpt_unpairB2) (fun _=>rfl)
lemma q178 (wU baseW eU:List Bool) :
  (powW wU baseW eU).length=wU.length∧val (powW wU baseW eU)=(val baseW) ^ eU.length % 2 ^ wU.length:=by
 dsimp only [powW]
 have hiter:∀ k,
   ∃ acc,q132^[k] (pairB wU (pairB (padW wU baseW) (natW wU [true]))) =
     pairB wU (pairB (padW wU baseW) acc) ∧
    acc.length=wU.length∧val acc=(val baseW) ^ k % 2 ^ wU.length:=by
  intro k
  induction k with
  | zero =>
   refine ⟨natW wU [true],rfl,q54 _ _,by simp [q114]⟩
  | succ k ih =>
   obtain ⟨acc,h1,hlen,hval⟩:=ih
   rw [Function.iterate_succ_apply',h1]
   dsimp only [q132]
   simp only [unpairB_pairB]
   refine ⟨mulW wU acc (padW wU baseW),rfl,q93 _ _ _,?_⟩
   rw [q115,hval,q26,Nat.mod_mul_mod,Nat.mul_mod_mod,pow_succ]
 obtain ⟨acc,h1,hlen,hval⟩:=hiter eU.length
 rw [h1];simp only [unpairB_pairB];exact ⟨hlen,hval⟩
end MachineBits
open MachineBits
abbrev Edge (n : ℕ) := Fin n × Fin n
abbrev Row (n : ℕ) := Finset (Edge n) × Bool
def ends {n : ℕ} (e : Edge n) : Finset (Fin n) := {e.1, e.2}
def disjointEdges {n : ℕ} (Q : Finset (Edge n)) : Prop :=
 ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f)
def choices {n : ℕ} (E : Finset (Edge n)) (k : ℕ) : Finset (Finset (Edge n)) :=
 E.powerset.filter (fun Q => Q.card = k ∧
  ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f))
def signed {n : ℕ} (rows : List (Row n)) (Q : Finset (Edge n)) : ℤ :=
 ((rows.filter (fun t => t.2 && decide (Q ⊆ t.1))).length : ℤ) -
  ((rows.filter (fun t => !t.2 && decide (Q ⊆ t.1))).length : ℤ)
def weight {n : ℕ} (Q : Finset (Edge n)) : ℕ :=
 let V := Q.biUnion ends
 V.prod (fun i => (V.filter (fun j => i < j)).prod (fun j => (j.val-i.val)^2))
def total {n : ℕ} (E : Finset (Edge n)) (k : ℕ) (rows : List (Row n)) : ℕ :=
 (choices E k).sum (fun Q => weight Q * (signed rows Q).natAbs^2)
lemma weight_pos {n : ℕ} (Q : Finset (Edge n)) : 0 < weight Q := by
 unfold weight
 refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => pow_pos ?_ _
 exact Nat.sub_pos_of_lt (Finset.mem_filter.mp hj).2
lemma total_pos {n k : ℕ} (E : Finset (Edge n)) (rows : List (Row n)) :
  0 < total E k rows ↔ ∃ Q ∈ choices E k, signed rows Q ≠ 0 := by
 classical
 have hz : total E k rows = 0 ↔ ∀ Q ∈ choices E k, signed rows Q = 0 := by
  rw [total, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  refine forall_congr' fun Q => imp_congr_right fun _ => ?_
  simp [(Nat.pos_iff_ne_zero.mp (weight_pos Q))]
 rw [Nat.pos_iff_ne_zero]
 change (¬ total E k rows = 0) ↔ _
 rw [hz]
 push_neg
 rfl
def sign (b : Bool) : ℤ := if b then 1 else -1
def rowContribution {n : ℕ} (Q : Finset (Edge n)) (r : Row n) : ℤ :=
 if Q ⊆ r.1 then sign r.2 else 0
lemma signed_eq_sum {n : ℕ} (rows : List (Row n)) (Q : Finset (Edge n)) :
  signed rows Q = (rows.map (rowContribution Q)).sum := by
 induction rows with
 | nil => rfl
 | cons r rows ih =>
  simp only [List.map_cons, List.sum_cons, ← ih]
  unfold signed rowContribution sign
  split <;> cases hr : r.2 <;> simp [*] <;> ring
lemma list_sum_finset_sum {α β : Type*} (L : List α) (S : Finset β) (f : α → β → ℤ) :
  (L.map (fun a => ∑ b ∈ S, f a b)).sum = ∑ b ∈ S, (L.map (fun a => f a b)).sum := by
 induction L with
 | nil => simp
 | cons a L ih => simp [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]
lemma filter_choices {n k : ℕ} (E A B : Finset (Edge n)) :
  (choices E k).filter (fun Q => Q ⊆ A ∧ Q ⊆ B) = choices (E ∩ A ∩ B) k := by
 ext Q
 simp only [choices, Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
 tauto
lemma weight_cast_sq {z : ℤ} : ((z.natAbs^2 : ℕ) : ℤ) = z^2 := by
 simpa only [pow_two] using (Int.natAbs_mul_self (a := z))
lemma total_eq_row_pairs {n k : ℕ} (E : Finset (Edge n)) (rows : List (Row n)) :
  (total E k rows : ℤ) = (rows.map (fun r => (rows.map (fun s =>
   sign r.2 * sign s.2 * (choices (E ∩ r.1 ∩ s.1) k).sum (fun Q => (weight Q : ℤ)))).sum)).sum := by
 classical
 have hh (r s : Row n) :
   sign r.2 * sign s.2 * (choices (E ∩ r.1 ∩ s.1) k).sum (fun Q => (weight Q : ℤ)) =
    (choices E k).sum (fun Q => (weight Q : ℤ) * rowContribution Q r * rowContribution Q s) := by
  rw [← filter_choices, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hr : Q ⊆ r.1 <;> by_cases hs : Q ⊆ s.1 <;>
   simp [rowContribution, hr, hs] <;> ring
 simp_rw [hh, list_sum_finset_sum]
 unfold total
 simp only [Nat.cast_sum, Nat.cast_mul]
 apply Finset.sum_congr rfl
 intro Q _
 rw [weight_cast_sq, signed_eq_sum]
 have inner (r : Row n) :
   (rows.map (fun s => (weight Q : ℤ) * rowContribution Q r * rowContribution Q s)).sum =
    (weight Q : ℤ) * rowContribution Q r * (rows.map (rowContribution Q)).sum := by
  rw [List.sum_map_mul_left]
 simp_rw [inner, List.sum_map_mul_right, List.sum_map_mul_left]
 ring
def width (n m : ℕ) : ℕ := n*n + (2*n)*n*n + 2*m + 1
lemma weight_le {n : ℕ} (Q : Finset (Edge n)) : weight Q ≤ 2 ^ ((2*n)*n*n) := by
  unfold weight
  let V := Q.biUnion ends
  have hv : V.card ≤ n := by simpa using Finset.card_le_univ V
  have hinner (i : Fin n) :
      (V.filter (fun j => i < j)).prod (fun j => (j.val-i.val)^2) ≤ (2^(2*n))^n := by
    calc
      _ ≤ (2^(2*n))^((V.filter (fun j => i < j)).card) := by
        apply Finset.prod_le_pow_card
        intro j _
        rw [mul_comm 2 n, pow_mul]
        exact Nat.pow_le_pow_left (Nat.sub_le .. |>.trans (j.isLt.le.trans (Nat.lt_two_pow_self).le)) 2
      _ ≤ _ := Nat.pow_le_pow_right (by positivity) ((Finset.card_filter_le _ _).trans hv)
  calc
    _ ≤ ((2^(2*n))^n)^V.card := Finset.prod_le_pow_card _ _ _ (fun i _ => hinner i)
    _ ≤ ((2^(2*n))^n)^n := Nat.pow_le_pow_right (by positivity) hv
    _ = _ := by simp only [← pow_mul, Nat.mul_assoc]
lemma signed_abs_le {n : ℕ} (rows : List (Row n)) (Q : Finset (Edge n)) :
  (signed rows Q).natAbs ≤ rows.length := by
 unfold signed
 have hp := List.length_filter_le (p := fun t : Row n => t.2 && decide (Q ⊆ t.1)) (l := rows)
 have hm := List.length_filter_le (p := fun t : Row n => !t.2 && decide (Q ⊆ t.1)) (l := rows)
 omega
lemma total_lt {n k : ℕ} (E : Finset (Edge n)) (rows : List (Row n)) :
    total E k rows < 2^(width n rows.length) := by
  have hE : E.card ≤ n*n := by simpa [Fintype.card_prod] using Finset.card_le_univ E
  have hC : (choices E k).card ≤ 2^(n*n) := by
    apply le_trans (Finset.card_filter_le _ _)
    rw [Finset.card_powerset]
    exact Nat.pow_le_pow_right (by decide) hE
  have hm (Q : Finset (Edge n)) : (signed rows Q).natAbs^2 ≤ 2^(2*rows.length) := by
    rw [mul_comm 2 rows.length, pow_mul]
    exact Nat.pow_le_pow_left ((signed_abs_le rows Q).trans (Nat.lt_two_pow_self).le) 2
  calc
    total E k rows ≤ (choices E k).card * (2^((2*n)*n*n) * 2^(2*rows.length)) := by
      unfold total
      simpa [nsmul_eq_mul] using
        Finset.sum_le_card_nsmul (choices E k) (fun Q => weight Q * (signed rows Q).natAbs^2)
          (2^((2*n)*n*n) * 2^(2*rows.length)) (fun Q _ => Nat.mul_le_mul (weight_le Q) (hm Q))
    _ ≤ 2^(n*n) * (2^((2*n)*n*n) * 2^(2*rows.length)) := Nat.mul_le_mul_right _ hC
    _ = 2^(n*n + (2*n)*n*n + 2*rows.length) := by rw [← mul_assoc, ← pow_add, ← pow_add]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by simp [width])
namespace Padding
open Turing PEqualNP.Library Lib.Machines Lib.Universal
private def pushedSymbols {K:Type} {Γ:K→ Type} {Λ σ:Type}:Turing.TM2.Stmt Γ Λ σ→ Set (Σ k,Γ k)
 | .push k g q=>Set.range (fun v=>(⟨k,g v⟩:Σ k,Γ k))∪ pushedSymbols q
 | .peek _ _ q=>pushedSymbols q
 | .pop _ _ q=>pushedSymbols q
 | .load _ q=>pushedSymbols q
 | .branch _ q₁ q₂=>pushedSymbols q₁∪ pushedSymbols q₂
 | .goto _=>∅
 | .halt=>∅
private lemma pushedSymbols_finite {K:Type} {Γ:K→ Type} {Λ σ:Type} [Finite σ]
  (q:Turing.TM2.Stmt Γ Λ σ):(pushedSymbols q).Finite:=by
 induction q with
 | push _ _ _ ih=>exact (Set.finite_range _).union ih
 | peek _ _ _ ih=>exact ih
 | pop _ _ _ ih=>exact ih
 | load _ _ ih=>exact ih
 | branch _ _ _ ih₁ ih₂=>exact ih₁.union ih₂
 | goto _=>exact Set.finite_empty
 | halt=>exact Set.finite_empty
private def restrictStmt {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
  (T:∀ k,Set (Γ k)) :
  ∀ (q:Turing.TM2.Stmt Γ Λ σ),(∀ k s,(⟨k,s⟩:Σ j,Γ j)∈ pushedSymbols q→ s∈ T k) →
  Turing.TM2.Stmt (fun k=>{s:Γ k // s∈ T k}) Λ σ
 | .push k g q,h=>.push k (fun v=>⟨g v,h k (g v) (Or.inl ⟨v,rfl⟩)⟩)
   (restrictStmt T q (fun j s hs=>h j s (Or.inr hs)))
 | .peek k f q,h=>.peek k (fun v o=>f v (o.map Subtype.val)) (restrictStmt T q h)
 | .pop k f q,h=>.pop k (fun v o=>f v (o.map Subtype.val)) (restrictStmt T q h)
 | .load a q,h=>.load a (restrictStmt T q h)
 | .branch f q₁ q₂,h=>.branch f
   (restrictStmt T q₁ (fun j s hs=>h j s (Or.inl hs)))
   (restrictStmt T q₂ (fun j s hs=>h j s (Or.inr hs)))
 | .goto f,_=>.goto f
 | .halt,_=>.halt
private def forgetCfg {K : Type} {Γ : K → Type} {Λ σ : Type} (T : ∀ k, Set (Γ k))
  (cfg:Turing.TM2.Cfg (fun k=>{s:Γ k // s∈ T k}) Λ σ):Turing.TM2.Cfg Γ Λ σ :=
 ⟨cfg.l,cfg.var,fun k=>(cfg.stk k).map Subtype.val⟩
private lemma forgetCfg_injective {K:Type} {Γ:K→ Type} {Λ σ:Type} (T:∀ k,Set (Γ k)) :
  Function.Injective (forgetCfg (Λ:=Λ) (σ:=σ) T):=by
 rintro ⟨l₁,v₁,S₁⟩ ⟨l₂,v₂,S₂⟩ h
 simp only [forgetCfg,Turing.TM2.Cfg.mk.injEq] at h
 obtain ⟨rfl,rfl,hS⟩:=h
 congr 1
 funext k
 exact List.map_injective_iff.mpr Subtype.val_injective (congrFun hS k)
private lemma map_subtype_update {K:Type} [DecidableEq K] {Γ:K→ Type} (T:∀ k,Set (Γ k))
  (S:∀ k,List {s:Γ k // s∈ T k}) (k:K) (l:List {s:Γ k // s∈ T k}) :
  (fun j=>(Function.update S k l j).map Subtype.val) =
   Function.update (fun j=>(S j).map Subtype.val) k (l.map Subtype.val):=by
 funext j
 by_cases h:j= k
 · subst h; simp
 · simp [h]
private lemma restrictStmt_stepAux {K:Type} [DecidableEq K] {Γ:K→ Type} {Λ σ:Type}
  (T:∀ k,Set (Γ k)) (q:Turing.TM2.Stmt Γ Λ σ)
  (hq:∀ k s,(⟨k,s⟩:Σ j,Γ j)∈ pushedSymbols q→ s∈ T k)
  (v:σ) (S:∀ k,List {s:Γ k // s∈ T k}) :
  forgetCfg T (Turing.TM2.stepAux (restrictStmt T q hq) v S) =
   Turing.TM2.stepAux q v (fun k=>(S k).map Subtype.val):=by
 induction q generalizing v S with
 | push k g q ih =>
  simp only [restrictStmt,Turing.TM2.stepAux]
  rw [ih,map_subtype_update]
  rfl
 | peek k f q ih =>
  simp only [restrictStmt,Turing.TM2.stepAux]
  exact (ih hq _ _).trans (by rw [List.head?_map])
 | pop k f q ih =>
  simp only [restrictStmt,Turing.TM2.stepAux]
  exact (ih hq _ _).trans (by rw [map_subtype_update,List.head?_map,List.map_tail])
 | load a q ih =>
  simp only [restrictStmt,Turing.TM2.stepAux]
  exact ih hq (a v) S
 | branch f q₁ q₂ ih₁ ih₂ =>
  simp only [restrictStmt,Turing.TM2.stepAux]
  cases f v
  · exact ih₂ _ v S
  · exact ih₁ _ v S
 | goto f=>rfl
 | halt=>rfl
private lemma finiteAlphabetTransport (c:Turing.TM2ComputableAux Bool Bool) :
    ∃ c' : Turing.TM2ComputableAux Bool Bool, (∀ j, Finite (c'.tm.Γ j)) ∧
      ∀ (x y : List Bool) (s : ℕ),
        Turing.TM2OutputsInTime c.tm (x.map c.inputAlphabet.invFun)
            (some (y.map c.outputAlphabet.invFun)) s →
        Nonempty (Turing.TM2OutputsInTime c'.tm (x.map c'.inputAlphabet.invFun)
            (some (y.map c'.outputAlphabet.invFun)) s):=by
  classical
  let _:DecidableEq c.tm.K:=c.tm.kDecidableEq
  let _:Fintype c.tm.K:=c.tm.kFin
  let _:Fintype c.tm.Λ:=c.tm.ΛFin
  let _:Fintype c.tm.σ:=c.tm.σFin
  let _:Fintype (c.tm.Γ c.tm.k₀):=c.tm.Γk₀Fin
  let T:∀ k:c.tm.K,Set (c.tm.Γ k):=fun k =>
    {s | k= c.tm.k₀∨ k= c.tm.k₁ ∨
      (⟨k,s⟩:Σ j,c.tm.Γ j)∈ ⋃ l:c.tm.Λ,pushedSymbols (c.tm.m l)}
  let e₀:{s:c.tm.Γ c.tm.k₀ // s∈ T c.tm.k₀} ≃ c.tm.Γ c.tm.k₀ :=
    { toFun := Subtype.val
      invFun:=fun s=>⟨s,Or.inl rfl⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  let e₁:{s:c.tm.Γ c.tm.k₁ // s∈ T c.tm.k₁} ≃ c.tm.Γ c.tm.k₁ :=
    { toFun := Subtype.val
      invFun:=fun s=>⟨s,Or.inr (Or.inl rfl)⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  let hΓ0Fin:Fintype {s:c.tm.Γ c.tm.k₀ // s∈ T c.tm.k₀}:=Fintype.ofEquiv _ e₀.symm
  let tm':Turing.FinTM2 :=
    { K := c.tm.K
      kDecidableEq:=c.tm.kDecidableEq
      kFin:=c.tm.kFin
      k₀:=c.tm.k₀
      k₁:=c.tm.k₁
      Γ:=fun k=>{s:c.tm.Γ k // s∈ T k}
      Λ:=c.tm.Λ
      main:=c.tm.main
      ΛFin:=c.tm.ΛFin
      σ:=c.tm.σ
      initialState:=c.tm.initialState
      σFin:=c.tm.σFin
      Γk₀Fin:=hΓ0Fin
      m := fun l => restrictStmt T (c.tm.m l)
        (fun k s hs=>Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨l,hs⟩))) }
  have hFin:∀ j:tm'.K,Finite (tm'.Γ j):=by
    intro j
    by_cases h0:j= c.tm.k₀
    · subst h0; exact Finite.of_fintype _
    · by_cases h1 : j = c.tm.k₁
      · subst h1
        have:Finite (c.tm.Γ c.tm.k₁):=Finite.of_equiv Bool c.outputAlphabet.symm
        exact Finite.of_equiv _ e₁.symm
      · have hUfin:(⋃ l:c.tm.Λ,pushedSymbols (c.tm.m l)).Finite :=
          Set.finite_iUnion fun l=>pushedSymbols_finite (c.tm.m l)
        have:Finite ↥(⋃ l:c.tm.Λ,pushedSymbols (c.tm.m l)):=hUfin.to_subtype
        refine Finite.of_injective (f:=fun x:tm'.Γ j =>
            (⟨⟨j,x.1⟩,by
              rcases x.2 with h | h | h
              · exact (h0 h).elim
              · exact (h1 h).elim
              · exact h⟩:↥(⋃ l:c.tm.Λ,pushedSymbols (c.tm.m l)))) ?_
        intro x y hxy
        have h1':=congrArg (fun z=>z.1) hxy
        exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp h1').2)
  have hstep:∀ cfg:tm'.Cfg,
      Option.map (forgetCfg T) (tm'.step cfg)= c.tm.step (forgetCfg T cfg):=by
    rintro ⟨l,v,S⟩
    cases l with
    | none=>rfl
    | some l =>
      change some (forgetCfg T (Turing.TM2.stepAux (restrictStmt T (c.tm.m l) _) v S)) =
        some (Turing.TM2.stepAux (c.tm.m l) v (fun k=>(S k).map Subtype.val))
      exact congrArg some (restrictStmt_stepAux T (c.tm.m l) _ v S)
  have hiter:∀ (steps:ℕ) (cfg:tm'.Cfg),
      Option.map (forgetCfg T) ((flip bind tm'.step)^[steps] (some cfg)) =
        (flip bind c.tm.step)^[steps] (some (forgetCfg T cfg)):=by
    intro steps
    induction steps with
    | zero=>intro cfg; rfl
    | succ steps ih =>
      intro cfg
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      cases hcur:(flip bind tm'.step)^[steps] (some cfg) with
      | none =>
        have hih:=ih cfg
        rw [hcur] at hih
        rw [← hih]; rfl
      | some cfg' =>
        have hih:=ih cfg
        rw [hcur] at hih
        rw [← hih]
        exact hstep cfg'
  refine ⟨⟨tm',e₀.trans c.inputAlphabet,e₁.trans c.outputAlphabet⟩,hFin,?_⟩
  intro x y s h
  refine ⟨{ steps:=h.steps,evals_in_steps:=?_,steps_le_m:=h.steps_le_m }⟩
  have horig:=h.evals_in_steps
  have hinit:forgetCfg T (Turing.initList tm' (x.map (e₀.trans c.inputAlphabet).invFun)) =
      Turing.initList c.tm (x.map c.inputAlphabet.invFun):=by
    simp only [forgetCfg,Turing.initList]
    congr 1; funext k
    by_cases hk:k= c.tm.k₀
    · subst hk
      dsimp only [tm']
      simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map]
      rfl
    · dsimp only [tm']
      simp only [hk,↓reduceDIte,List.map_nil]
  have hhalt:forgetCfg T (Turing.haltList tm' (y.map (e₁.trans c.outputAlphabet).invFun)) =
      Turing.haltList c.tm (y.map c.outputAlphabet.invFun):=by
    simp only [forgetCfg,Turing.haltList]
    congr 1; funext k
    by_cases hk:k= c.tm.k₁
    · subst hk
      dsimp only [tm']
      simp only [↓reduceDIte,eq_mpr_eq_cast,cast_eq,List.map_map]
      rfl
    · dsimp only [tm']
      simp only [hk,↓reduceDIte,List.map_nil]
  apply Option.map_injective (forgetCfg_injective T)
  rw [hiter,hinit,horig]
  exact (congrArg some hhalt).symm
private def mrW (parameter : List Bool → List Bool) (x : List Bool) : ℕ :=
 (parameter x).length
private def mrPad (parameter : List Bool → List Bool) (x : List Bool) : List Bool :=
 un (2 ^ (mrW parameter x + 1)) ++ false :: x
private def seedPair (parameter : List Bool → List Bool) (x : List Bool) :
  List Bool × List Bool :=
 (true :: false :: x, true :: parameter x)
private def doubleHeader (x : List Bool) : List Bool := hd x ++ x
private lemma hd_header (n : ℕ) (x : List Bool) :
  hd (un n ++ false :: x) = un n := by
 simp [hd, un]
private lemma doubleHeader_iter (x : List Bool) (j : ℕ) :
  doubleHeader^[j] (true :: false :: x) = un (2 ^ j) ++ false :: x := by
 induction j with
 | zero => rfl
 | succ j ih =>
  rw [Function.iterate_succ_apply', ih]
  show hd (un (2 ^ j) ++ false :: x) ++ (un (2 ^ j) ++ false :: x) = _
  rw [hd_header, ← List.append_assoc, pow_succ, mul_two]
  simp only [un, List.replicate_add]
private lemma doubleHeader_cpt : Lib.CPTs doubleHeader :=
 cpt_app2 cpt_hd cpt_id
private lemma seedPair_cpt {parameter : List Bool → List Bool} (hp : Lib.CPTs parameter) :
  ComputableInPolyTime (fun x : List Bool => x) encodePair (seedPair parameter) :=
 cpt_pair (cpt_app2 (cpt_const [true, false]) cpt_id)
  (cpt_app2 (cpt_const [true]) hp)
private lemma eval_power_bound_positive (p:Polynomial ℕ):∃ a d:ℕ,∀ m:ℕ,1≤ m→ p.eval m≤ a* m ^ d:=by
 induction p using Polynomial.induction_on' with
 | add p q hp hq =>
  obtain ⟨a,d,h⟩:=hp
  obtain ⟨b,e,h'⟩:=hq
  refine ⟨a+b,d+e,fun m hm=>?_⟩
  rw [Polynomial.eval_add,Nat.add_mul]
  have h1:m ^ d≤ m ^ (d+e):=Nat.pow_le_pow_right hm (by omega)
  have h2:m ^ e≤ m ^ (d+e):=Nat.pow_le_pow_right hm (by omega)
  exact add_le_add ((h m hm).trans (Nat.mul_le_mul_left _ h1))
   ((h' m hm).trans (Nat.mul_le_mul_left _ h2))
 | monomial d c=>exact ⟨c,d,fun m _=>by rw [Polynomial.eval_monomial]⟩
private lemma eval_power_bound (p:Polynomial ℕ):∃ A,1≤ A∧ ∀ m,p.eval m≤ A* (m+ 1) ^ A:=by
  obtain ⟨a,d,h⟩:=eval_power_bound_positive p
  refine ⟨a+ d+ 1,by omega,fun m=>?_⟩
  calc p.eval m ≤ p.eval (m + 1) := d37 p (by omega)
    _≤ a* (m+ 1) ^ d:=h (m+ 1) (by omega)
    _ ≤ (a + d + 1) * (m + 1) ^ (a + d + 1) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
private lemma combined_step_bound (A B P s1 tg s3 n2 n w L:ℕ) (hA:1≤ A) (hB:1≤ B) (hBP:B≤ P)
  (h1:s1≤ A* P) (hg:tg≤ A* P) (h3:s3≤ A* P) (hn:n+ 2≤ B) (hw:w+ 1≤ B)
  (hL:L≤ B)
  (h2:n2≤ (w+ 1)* (tg+ 2* L+ 3)+ 2* L+ 2* (n+ 2)+ (w+ 1)+ 5) :
  s1+ (2* ((n+ 2)+ (w+ 1))+ 2)+ (n2+ (2* L+ 2)+ s3)≤ (3* A+ 25)* (B* P):=by
 have e1:(w+ 1)* (tg+ 2* L+ 3)≤ B* (A* P+ 2* B+ 3):=Nat.mul_le_mul hw (by omega)
 have e2:B* (A* P+ 2* B+ 3)= A* (B* P)+ 2* (B* B)+ 3* B:=by ring
 have e3:B* B≤ B* P:=Nat.mul_le_mul_left B hBP
 have e4:B≤ B* P:=Nat.le_mul_of_pos_right B (by omega)
 have e5:P≤ B* P:=Nat.le_mul_of_pos_left P (by omega)
 have e6:A* P≤ A* (B* P):=Nat.mul_le_mul_left A e5
 have e7:(3* A+ 25)* (B* P)= 3* (A* (B* P))+ 25* (B* P):=by ring
 rw [e7]
 generalize B* P= Q at *
 generalize A* Q= AQ at *
 generalize A* P= AP at *
 generalize B* B= BB at *
 omega
private lemma absorb_step_bound (A K n w:ℕ) (hK:A+ 1≤ K) :
    K* (2 ^ (w+ 1)* (n+ 2)) ^ (A+ 1)≤ 2 ^ (2* K* (w+ 1))* (n+ 2) ^ (2* K):=by
  have h1:K< 2 ^ K:=Nat.lt_two_pow_self
  have hB1:1≤ 2 ^ (w+ 1)* (n+ 2):=Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2:(2 ^ (w+ 1)* (n+ 2)) ^ (A+ 1)≤ (2 ^ (w+ 1)* (n+ 2)) ^ K :=
    Nat.pow_le_pow_right hB1 hK
  have h3:(2 ^ (w+ 1)* (n+ 2)) ^ K= 2 ^ (K* (w+ 1))* (n+ 2) ^ K:=by
    rw [mul_pow,← pow_mul,mul_comm (w+ 1) K]
  have h4:K+ K* (w+ 1)≤ 2* K* (w+ 1):=by nlinarith
  calc K * (2 ^ (w + 1) * (n + 2)) ^ (A + 1) ≤ 2 ^ K * (2 ^ (w + 1) * (n + 2)) ^ K :=
        Nat.mul_le_mul h1.le h2
    _= 2 ^ (K+ K* (w+ 1))* (n+ 2) ^ K:=by rw [h3,← mul_assoc,← pow_add]
    _ ≤ 2 ^ (2 * K * (w + 1)) * (n + 2) ^ (2 * K) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) h4)
          (Nat.pow_le_pow_right (by omega) (by omega))
lemma mr_fpt (parameter G : List Bool → List Bool)
    (hp : Lib.CPTs parameter) (hlen : ∀ x, (parameter x).length ≤ x.length)
    (hG : Lib.CPTs G) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ x : List Bool, Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
        (some ((G (List.replicate (2 ^ ((parameter x).length + 1)) true ++ false :: x)).map
          M.outputAlphabet.invFun))
        (2 ^ (c * ((parameter x).length + 1)) * (x.length + 2) ^ c)) := by
  classical
  obtain ⟨c1⟩:=seedPair_cpt hp
  obtain ⟨cg⟩:=doubleHeader_cpt
  obtain ⟨c3⟩:=hG
  obtain ⟨A1,hA1,hp1⟩:=eval_power_bound c1.time
  obtain ⟨Ag,hAg,hpg⟩:=eval_power_bound cg.time
  obtain ⟨A3,hA3,hp3⟩:=eval_power_bound c3.time
  let e₀:Bool→ cg.tm.Γ cg.tm.k₀:=cg.inputAlphabet.invFun
  let d₀:cg.tm.Γ cg.tm.k₀→ Bool:=cg.inputAlphabet
  let e₁:cg.tm.Γ cg.tm.k₁→ Bool:=cg.outputAlphabet
  let Mit:FinTM2:=Iter.iterM cg.tm e₀ d₀ e₁
  let φ2:Mit.Γ Mit.k₁→ c3.tm.Γ c3.tm.k₀:=fun b=>c3.inputAlphabet.invFun b
  let d2:Option (c3.tm.Γ c3.tm.k₀):=some (c3.inputAlphabet.invFun true)
  let M2:FinTM2:=comp Mit c3.tm φ2 d2
  let φ1:c1.tm.Γ c1.tm.k₁→ M2.Γ M2.k₀:=fun s=>c1.outputAlphabet s
  let d1:Option (M2.Γ M2.k₀):=some (Sum.inl true:Bool ⊕ Bool)
  let M1:FinTM2:=comp c1.tm M2 φ1 d1
  let A:=A1+ Ag+ A3
  let K:=3* A+ 25
  have hrun:∀ z:List Bool,∃ (s:ℕ) (m:List (cg.tm.Γ cg.tm.k₁)),
      s≤ cg.time.eval z.length ∧
      (flip bind (TM2.step cg.tm.m))^[s] (some (initList cg.tm (z.map e₀))) =
        some (haltList cg.tm m)∧ m.map e₁= doubleHeader z:=by
    intro z
    refine ⟨(cg.outputsFun z).steps,List.map cg.outputAlphabet.invFun (doubleHeader z),
      (cg.outputsFun z).steps_le_m,(cg.outputsFun z).evals_in_steps,?_⟩
    rw [List.map_map]
    conv_rhs=>rw [← List.map_id (doubleHeader z)]
    exact List.map_congr_left fun y _=>cg.outputAlphabet.right_inv y
  have key:∀ x:List Bool,∃ n,n≤ 2 ^ (2* K* (mrW parameter x+ 1))* (x.length+ 2) ^ (2* K) ∧
      (flip bind (TM2.step M1.m))^[n] (some (initList M1 (x.map c1.inputAlphabet.invFun))) =
        some (haltList M1 ((G (mrPad parameter x)).map c3.outputAlphabet.invFun)):=by
    intro x
    let n:=x.length
    let w:=mrW parameter x
    let L:=2 ^ (w+ 1)+ 1+ n
    have hw:w≤ n:=hlen x
    have hpadlen:(mrPad parameter x).length= L:=by
      simp only [mrPad,List.length_append,un_length,List.length_cons,L,n,w]; omega
    have r1:=c1.outputsFun x
    have hL:∀ j≤ (true::parameter x).length,
        (doubleHeader^[j] (true::false::x)).length≤ L:=by
      intro j hj
      rw [doubleHeader_iter]
      have hj':j≤ w+ 1:=hj
      have:2 ^ j≤ 2 ^ (w+ 1):=Nat.pow_le_pow_right (by norm_num) hj'
      simp only [List.length_append,un_length,List.length_cons,L,n]
      omega
    obtain ⟨n2,hn2,h2run⟩:=Iter.d80 e₀ d₀ e₁ doubleHeader cg.time
      (fun a=>cg.inputAlphabet.right_inv a) hrun (true::false::x) (true::parameter x)
      L hL
    have hiter:doubleHeader^[(true::parameter x).length] (true::false::x)= mrPad parameter x :=
      doubleHeader_iter x (w+ 1)
    rw [hiter] at h2run
    have r3:=c3.outputsFun (mrPad parameter x)
    obtain ⟨n23,hn23,-,h23⟩:=d136 φ2 d2 (fun h=>by simp [d2] at h)
      (encodePair (seedPair parameter x)) (mrPad parameter x) ((G (mrPad parameter x)).map c3.outputAlphabet.invFun)
      n2 r3.steps h2run r3.evals_in_steps
    have hφ1:((encodePair (seedPair parameter x)).map c1.outputAlphabet.invFun).map φ1 =
        encodePair (seedPair parameter x):=by
      rw [List.map_map]
      conv_rhs=>rw [← List.map_id (encodePair (seedPair parameter x))]
      exact List.map_congr_left fun y _=>c1.outputAlphabet.right_inv y
    rw [← hφ1] at h23
    obtain ⟨nt,hnt,-,ht⟩:=d136 φ1 d1 (fun h=>by simp [d1] at h)
      (x.map c1.inputAlphabet.invFun) ((encodePair (seedPair parameter x)).map c1.outputAlphabet.invFun)
      ((G (mrPad parameter x)).map c3.outputAlphabet.invFun) r1.steps n23 r1.evals_in_steps h23
    refine ⟨nt,?_,ht⟩
    have hlen1:((encodePair (seedPair parameter x)).map c1.outputAlphabet.invFun).length =
        (n+ 2)+ (w+ 1):=by
      simp only [List.length_map,seedPair,Lib.Machines.d9,List.length_cons,n,w,mrW]
    have hnt':nt≤ r1.steps+ (2* ((n+ 2)+ (w+ 1))+ 2)+ n23:=by omega
    have hn23':n23≤ n2+ (2* L+ 2)+ r3.steps:=by
      have e:List.length (α:=Mit.Γ Mit.k₁) (mrPad parameter x)= L:=hpadlen
      omega
    let B:=2 ^ (w+ 1)* (n+ 2)
    have hE2:2≤ 2 ^ (w+ 1):=by
      calc 2 = 2 ^ 1 := rfl
        _≤ 2 ^ (w+ 1):=Nat.pow_le_pow_right (by norm_num) (by omega)
    have hEw:w+ 1< 2 ^ (w+ 1):=Nat.lt_two_pow_self
    have hBexp:B= 2 ^ (w+ 1)* n+ 2* 2 ^ (w+ 1):=by simp only [B]; ring
    have hEn:n≤ 2 ^ (w+ 1)* n:=Nat.le_mul_of_pos_left n (by omega)
    have hB1:1≤ B:=by omega
    have hBn:n+ 2≤ B:=by omega
    have hBw:w+ 1≤ B:=by omega
    have hBL:L+ 1≤ B:=by simp only [L]; omega
    let P:=B ^ A
    have hBP:B≤ P:=Nat.le_self_pow (by omega) B
    have hpow:∀ (Ai m:ℕ),Ai≤ A→ m+ 1≤ B→ Ai* (m+ 1) ^ Ai≤ A* P:=by
      intro Ai m hAi hm
      exact Nat.mul_le_mul hAi ((Nat.pow_le_pow_left hm Ai).trans
        (Nat.pow_le_pow_right (by omega) hAi))
    have b1:r1.steps≤ A* P:=r1.steps_le_m.trans ((hp1 _).trans
      (hpow A1 n (by omega) (by omega)))
    have bg:cg.time.eval L≤ A* P:=(hpg L).trans (hpow Ag L (by omega) hBL)
    have b3':Polynomial.eval (mrPad parameter x).length c3.time≤ A* P:=by
      rw [hpadlen]; exact (hp3 L).trans (hpow A3 L (by omega) hBL)
    have b3:r3.steps≤ A* P:=r3.steps_le_m.trans b3'
    have hn2':n2≤ (w+ 1)* (cg.time.eval L+ 2* L+ 3)+ 2* L+ 2* (n+ 2) +
        (w+ 1)+ 5:=by
      have e:(true::parameter x).length= w+ 1:=rfl
      have e':(true::false::x).length= n+ 2:=rfl
      rw [e,e'] at hn2
      exact hn2
    have hA:1≤ A:=by omega
    have:=combined_step_bound A B P r1.steps (cg.time.eval L) r3.steps n2 n w L hA hB1 hBP b1 bg b3
      hBn hBw (by omega) hn2'
    have hBP':B* P= B ^ (A+ 1):=by simp only [P]; rw [pow_succ,mul_comm]
    have hfin:=absorb_step_bound A K n w (by omega)
    calc nt ≤ r1.steps + (2 * ((n + 2) + (w + 1)) + 2) + n23 := hnt'
      _≤ r1.steps+ (2* ((n+ 2)+ (w+ 1))+ 2)+ (n2+ (2* L+ 2)+ r3.steps):=by omega
      _≤ K* (B* P):=this
      _= K* (2 ^ (w+ 1)* (n+ 2)) ^ (A+ 1):=by rw [hBP']
      _≤ _:=hfin
  let Mx:Turing.TM2ComputableAux Bool Bool:=⟨M1,c1.inputAlphabet,c3.outputAlphabet⟩
  obtain ⟨M',hfin,htrans⟩:=finiteAlphabetTransport Mx
  refine ⟨M',2* K,hfin,fun x=>htrans x (G (mrPad parameter x)) _ ?_⟩
  exact { steps := Classical.choose (key x)
          evals_in_steps:=(Classical.choose_spec (key x)).2
          steps_le_m:=(Classical.choose_spec (key x)).1 }
end Padding
namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal
def left (s : List Bool) : List Bool := (unpairB s).1
def right (s : List Bool) : List Bool := (unpairB s).2
lemma cpLeft {f : List Bool → List Bool} (h : Lib.CPTs f) :
 Lib.CPTs (fun s => left (f s)) := cpt_comp h cpt_unpairB1
lemma cpRight {f : List Bool → List Bool} (h : Lib.CPTs f) :
 Lib.CPTs (fun s => right (f s)) := cpt_comp h cpt_unpairB2
lemma cpCons (b : Bool) {f : List Bool → List Bool} (h : Lib.CPTs f) :
 Lib.CPTs (fun s => b :: f s) := cpt_app2 (cpt_const [b]) h
lemma cpTail {f : List Bool → List Bool} (h : Lib.CPTs f) :
 Lib.CPTs (fun s => (f s).tail) := cpt_comp h cpt_tail
lemma cpTake {f g : List Bool → List Bool} (h : Lib.CPTs f) (hg : Lib.CPTs g) :
  Lib.CPTs (fun s => (g s).take (f s).length) :=
 q39 (q24 h hg) (fun s => q12 (f s) (g s))
lemma cpDrop {f g : List Bool → List Bool} (h : Lib.CPTs f) (hg : Lib.CPTs g) :
  Lib.CPTs (fun s => (g s).drop (f s).length) :=
 q39 (cpt_dropN' h hg) (fun s => q40 (f s) (g s))
def indexed (join : List Bool → List Bool → List Bool → List Bool)
  (f : List Bool → List Bool) (y : List Bool) : List Bool :=
 let cap := left y
 let count := (left (right y)).tail
 let args := left (right (right y))
 let acc := right (right (right y))
 pairB cap (pairB count (pairB args (join cap (f (pairB count (pairB args acc))) acc)))
lemma cpIndexed {join : List Bool → List Bool → List Bool → List Bool}
  (hjoin : ∀ {u v w : List Bool → List Bool}, Lib.CPTs u → Lib.CPTs v → Lib.CPTs w →
   Lib.CPTs (fun s => join (u s) (v s) (w s))) {f : List Bool → List Bool} (hf : Lib.CPTs f) :
  Lib.CPTs (indexed join f) := by
 have hcap := cpLeft cpt_id
 have hcount := cpTail (cpLeft (cpRight cpt_id))
 have hargs := cpLeft (cpRight (cpRight cpt_id))
 have hacc := cpRight (cpRight (cpRight cpt_id))
 exact cpt_pairB2 hcap (cpt_pairB2 hcount (cpt_pairB2 hargs
  (hjoin hcap (cpt_comp (cpt_pairB2 hcount (cpt_pairB2 hargs hacc)) hf) hacc)))
lemma indexed_length {join : List Bool → List Bool → List Bool → List Bool}
  (hjoin : ∀ cap val acc, (join cap val acc).length ≤ cap.length + acc.length)
  (f : List Bool → List Bool) (y : List Bool) :
  (indexed join f y).length ≤ y.length + 3 * (left y).length + 3 := by
 have h1 := unpairB_length y
 have h2 := unpairB_length (right y)
 have h3 := unpairB_length (right (right y))
 have h4 := hjoin (left y)
  (f (pairB (left (right y)).tail (pairB (left (right (right y))) (right (right (right y))))))
  (right (right (right y)))
 have h5 : (left (right y)).tail.length ≤ (left (right y)).length := by simp
 change 2 * (left y).length + (right y).length ≤ y.length at h1
 change 2 * (left (right y)).length + (right (right y)).length ≤ (right y).length at h2
 change 2 * (left (right (right y))).length + (right (right (right y))).length ≤
  (right (right y)).length at h3
 simp only [indexed, pairB_length]
 omega
def runIndexed (join : List Bool → List Bool → List Bool → List Bool)
  (f : List Bool → List Bool) (cap count args acc : List Bool) : List Bool :=
 right (right (right ((indexed join f)^[count.length]
  (pairB cap (pairB (un count.length) (pairB args acc))))))
lemma cpRunIndexed {join : List Bool → List Bool → List Bool → List Bool}
  (hjoin : ∀ {u v w : List Bool → List Bool}, Lib.CPTs u → Lib.CPTs v → Lib.CPTs w →
   Lib.CPTs (fun s => join (u s) (v s) (w s)))
  (hlen : ∀ cap val acc, (join cap val acc).length ≤ cap.length + acc.length)
  {f cap count args acc : List Bool → List Bool}
  (hf : Lib.CPTs f) (hcap : Lib.CPTs cap) (hcount : Lib.CPTs count)
  (hargs : Lib.CPTs args) (hacc : Lib.CPTs acc) :
  Lib.CPTs (fun s => runIndexed join f (cap s) (count s) (args s) (acc s)) := by
 have hinit := cpt_pairB2 hcap (cpt_pairB2 (cpt_comp hcount q89) (cpt_pairB2 hargs hacc))
 have hrun := q18 3 (cpIndexed hjoin hf)
  (fun y => by simp only [indexed, unpairB_pairB, left])
  (indexed_length hlen f) hcount hinit
 exact cpRight (cpRight (cpRight hrun))
lemma indexed_iter (join : List Bool → List Bool → List Bool → List Bool)
  (f : List Bool → List Bool) (cap args : List Bool) (n : ℕ) (acc : List Bool) :
  (indexed join f)^[n] (pairB cap (pairB (un n) (pairB args acc))) =
   pairB cap (pairB [] (pairB args ((List.range n).foldr
    (fun i x => join cap (f (pairB (un i) (pairB args x))) x) acc))) := by
 induction n generalizing acc with
 | zero => simp
 | succ n ih =>
  rw [Function.iterate_succ_apply, List.range_succ, List.foldr_append]
  simp only [indexed, left, right, unpairB_pairB, un_succ, List.tail_cons, List.foldr_cons, List.foldr_nil]
  exact ih _
lemma runIndexed_eq (join : List Bool → List Bool → List Bool → List Bool)
  (f : List Bool → List Bool) (cap count args acc : List Bool) :
  runIndexed join f cap count args acc = (List.range count.length).foldr
   (fun i x => join cap (f (pairB (un i) (pairB args x))) x) acc := by
 simp only [runIndexed, indexed_iter, right, unpairB_pairB]
def appendBound (cap val acc : List Bool) : List Bool := val.take cap.length ++ acc
def replaceBound (cap val _ : List Bool) : List Bool := val.take cap.length
lemma appendBound_cpt {u v w : List Bool → List Bool} (hu : Lib.CPTs u) (hv : Lib.CPTs v)
  (hw : Lib.CPTs w) : Lib.CPTs (fun s => appendBound (u s) (v s) (w s)) :=
 cpt_app2 (cpTake hu hv) hw
lemma replaceBound_cpt {u v w : List Bool → List Bool} (hu : Lib.CPTs u) (hv : Lib.CPTs v)
 (_ : Lib.CPTs w) : Lib.CPTs (fun s => replaceBound (u s) (v s) (w s)) := cpTake hu hv
lemma appendBound_length (cap val acc : List Bool) :
 (appendBound cap val acc).length ≤ cap.length + acc.length := by simp [appendBound]
lemma replaceBound_length (cap val acc : List Bool) :
 (replaceBound cap val acc).length ≤ cap.length + acc.length := by simp [replaceBound]
def mapRange (f : List Bool → List Bool) (cap count args : List Bool) : List Bool :=
 runIndexed appendBound (fun s => f (pairB (left s) (left (right s)))) cap count args []
lemma cpMapRange {f cap count args : List Bool → List Bool} (hf : Lib.CPTs f)
  (hcap : Lib.CPTs cap) (hc : Lib.CPTs count) (ha : Lib.CPTs args) :
  Lib.CPTs (fun s => mapRange f (cap s) (count s) (args s)) :=
 cpRunIndexed appendBound_cpt appendBound_length
  (cpt_comp (cpt_pairB2 (cpLeft cpt_id) (cpLeft (cpRight cpt_id))) hf) hcap hc ha (cpt_const [])
lemma mapRange_eq (f : List Bool → List Bool) (cap count args : List Bool)
  (h : ∀ i < count.length, (f (pairB (un i) args)).length ≤ cap.length) :
  mapRange f cap count args = (List.range count.length).flatMap (fun i => f (pairB (un i) args)) := by
 simp only [mapRange, runIndexed_eq, left, right, unpairB_pairB, appendBound]
 have hg (L : List ℕ) (hL : ∀ i ∈ L, i < count.length) :
   L.foldr (fun i x => (f (pairB (un i) args)).take cap.length ++ x) [] =
    L.flatMap (fun i => f (pairB (un i) args)) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
   simp [List.take_of_length_le (h i (hL i (by simp))), ih (fun j hj => hL j (by simp [hj]))]
 exact hg _ (fun i hi => List.mem_range.mp hi)
end Packed
namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal
def slot (word idx stream : List Bool) : List Bool :=
 (stream.drop (word.length * idx.length)).take word.length
lemma cpSlot {w i s : List Bool → List Bool} (hw : Lib.CPTs w) (hi : Lib.CPTs i) (hs : Lib.CPTs s) :
  Lib.CPTs (fun x => slot (w x) (i x) (s x)) :=
 q39 (cpTake hw (cpDrop (q42 hw hi) hs)) (fun x => by simp [slot, mulU])
lemma slot_flatMap {α : Type*} (L : List α) (f : α → List Bool) (w : List Bool) (i : ℕ)
  (hi : i < L.length) (hw : ∀ a ∈ L, (f a).length = w.length) :
  slot w (un i) (L.flatMap f) = f L[i] := by
 induction L generalizing i with
 | nil => simp at hi
 | cons a L ih =>
  have ha := hw a (by simp)
  have hL : ∀ b ∈ L, (f b).length = w.length := fun b hb => hw b (by simp [hb])
  cases i with
  | zero =>
   simp only [slot, un_length, Nat.mul_zero, List.drop_zero, List.flatMap_cons,
    List.getElem_cons_zero]
   rw [← ha, List.take_left]
  | succ i =>
   simp only [slot, un_length, List.flatMap_cons, List.getElem_cons_succ]
   rw [Nat.mul_succ, Nat.add_comm, ← ha, List.drop_length_add_append, ha]
   simpa only [slot, un_length] using ih i (by simp at hi; omega) hL
def doubleStep (s : List Bool) : List Bool :=
 (right (right s)) ++ (right (right s))
def powerTwo (cap exp : List Bool) : List Bool :=
 runIndexed replaceBound doubleStep cap exp [] (un 1)
lemma powerTwo_cpt {u v : List Bool → List Bool} (hu : Lib.CPTs u) (hv : Lib.CPTs v) :
  Lib.CPTs (fun s => powerTwo (u s) (v s)) := by
 have h := cpRight (cpRight cpt_id)
 exact cpRunIndexed replaceBound_cpt replaceBound_length (cpt_app2 h h) hu hv
  (cpt_const []) (cpt_const [true])
lemma runIndexed_ofListFold (join : List Bool → List Bool → List Bool → List Bool)
  (f : List Bool → List Bool) (cap count args acc : List Bool) {α : Type*}
  (spec : List Bool → α → Prop) (step : ℕ → α → α) (initial : α)
  (hinit : spec acc initial)
  (hstep : ∀ i < count.length, ∀ x a, spec x a →
   spec (join cap (f (pairB (un i) (pairB args x))) x) (step i a)) :
  spec (runIndexed join f cap count args acc) ((List.range count.length).foldr step initial) := by
 rw [runIndexed_eq]
 generalize hL : List.range count.length = L
 have hs : ∀ i ∈ L, i < count.length := by simp [← hL]
 clear hL
 induction L with
 | nil => exact hinit
 | cons i L ih =>
  simp only [List.foldr_cons]
  exact hstep i (hs i (by simp)) _ _ (ih (fun j hj => hs j (by simp [hj])))
lemma powerTwo_eq (cap exp : List Bool) (h : 2 ^ exp.length ≤ cap.length) :
  powerTwo cap exp = un (2 ^ exp.length) := by
 rw [powerTwo, runIndexed_eq]
 generalize hv : List.range exp.length = L
 have hlen : L.length = exp.length := by simp [← hv]
 have hL : L.length ≤ exp.length := hlen.le
 have goal : L.foldr (fun i x => replaceBound cap (doubleStep (pairB (un i) (pairB [] x))) x)
   (un 1) = un (2 ^ L.length) := by
  clear hv hlen
  induction L with
  | nil => rfl
  | cons i L ih =>
   have ht : L.length ≤ exp.length := by simp at hL; omega
   rw [List.foldr_cons, ih ht]
   simp only [doubleStep, right, unpairB_pairB, replaceBound, List.length_cons]
   have he : un (2 ^ L.length) ++ un (2 ^ L.length) = un (2 ^ (L.length+1)) := by
    simp only [un, pow_succ, Nat.mul_two, List.replicate_add]
   rw [he, List.take_of_length_le]
   simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hL).trans h
 exact goal.trans (congrArg (fun l : ℕ => un (2^l)) hlen)
def joinAdd (w v a : List Bool) : List Bool := addW w v a
lemma cpJoinAdd {u v w : List Bool → List Bool} (hu : Lib.CPTs u) (hv : Lib.CPTs v)
 (hw : Lib.CPTs w) : Lib.CPTs (fun s => joinAdd (u s) (v s) (w s)) := q82 hu hv hw
lemma joinAdd_length (w v a : List Bool) : (joinAdd w v a).length ≤ w.length + a.length := by
 rw [joinAdd, q36]; omega
def sumRange (f : List Bool → List Bool) (w count args : List Bool) : List Bool :=
 runIndexed joinAdd (fun s => f (pairB (left s) (left (right s)))) w count args (blank w)
lemma cpSumRange {f w c a : List Bool → List Bool} (hf : Lib.CPTs f) (hw : Lib.CPTs w)
  (hc : Lib.CPTs c) (ha : Lib.CPTs a) : Lib.CPTs (fun s => sumRange f (w s) (c s) (a s)) :=
 cpRunIndexed cpJoinAdd joinAdd_length
  (cpt_comp (cpt_pairB2 (cpLeft cpt_id) (cpLeft (cpRight cpt_id))) hf) hw hc ha (cpt_comp hw cpt_blank)
lemma sumRange_length (f : List Bool → List Bool) (w count args : List Bool) :
  (sumRange f w count args).length = w.length := by
 simp only [sumRange, runIndexed_eq]
 cases List.range count.length with
 | nil => exact q33 w
 | cons i L => exact q36 _ _ _
def rep (w b : List Bool) (z : ℤ) : Prop := (val b : ℤ) ≡ z [ZMOD (2:ℤ)^w.length]
lemma rep_zero (w : List Bool) : rep w (blank w) 0 := by simp [rep, q37]
lemma rep_nat (w u : List Bool) : rep w (natW w u) (u.length : ℤ) := by
 rw [rep, q114]
 exact_mod_cast (Nat.mod_modEq u.length (2 ^ w.length))
lemma rep_add {w a b : List Bool} {x y : ℤ} (hx : rep w a x) (hy : rep w b y) :
 rep w (addW w a b) (x + y) := (q98 w a b).trans (hx.add hy)
lemma rep_mul {w a b : List Bool} {x y : ℤ} (hx : rep w a x) (hy : rep w b y) :
 rep w (mulW w a b) (x * y) := (q55 w a b).trans (hx.mul hy)
lemma rep_neg {w a : List Bool} {x : ℤ} (hx : rep w a x) :
 rep w (negW w a) (-x) := (q113 w a).trans hx.neg
lemma rep_pow {w a : List Bool} {x : ℤ} (hx : rep w a x) (e : List Bool) :
  rep w (powW w a e) (x ^ e.length) := by
 have h : (val (powW w a e) : ℤ) ≡ (val a : ℤ)^e.length [ZMOD (2:ℤ)^w.length] := by
  rw [(q178 w a e).2]
  exact_mod_cast (Nat.mod_modEq ((val a)^e.length) (2 ^ w.length))
 exact h.trans (hx.pow _)
lemma sumRange_rep (f : List Bool → List Bool) (w count args : List Bool) (z : ℕ → ℤ)
  (h : ∀ i < count.length, rep w (f (pairB (un i) args)) (z i)) :
  rep w (sumRange f w count args) ((List.range count.length).map z).sum := by
 simp only [sumRange, runIndexed_eq, left, right, unpairB_pairB, joinAdd]
 generalize hr : List.range count.length = L
 have hL : ∀ i ∈ L, i < count.length := by simp [← hr]
 clear hr
 induction L with
 | nil => exact rep_zero w
 | cons i L ih =>
  simp only [List.foldr_cons, List.map_cons, List.sum_cons]
  exact rep_add (h i (hL i (by simp))) (ih (fun j hj => hL j (by simp [hj])))
lemma val_eq_of_rep {w b : List Bool} {z : ℕ} (hlen : b.length = w.length)
  (hb : rep w b (z : ℤ)) (hz : z < 2 ^ w.length) : val b = z := by
 have hx : val b < 2 ^ w.length := hlen ▸ q124 b
 have hx' : (val b : ℤ) < (2:ℤ)^w.length := by exact_mod_cast hx
 have hz' : (z : ℤ) < (2:ℤ)^w.length := by exact_mod_cast hz
 unfold rep Int.ModEq at hb
 rw [Int.emod_eq_of_lt (by positivity) hx', Int.emod_eq_of_lt (by positivity) hz'] at hb
 exact_mod_cast hb
def bitFlagAt (i x : List Bool) : List Bool := q17 (x.drop i.length)
lemma cpBitFlagAt {i x : List Bool → List Bool} (hi : Lib.CPTs i) (hx : Lib.CPTs x) :
 Lib.CPTs (fun s => bitFlagAt (i s) (x s)) := cpt_comp (cpDrop hi hx) q35
lemma bitFlagAt_eq (i x : List Bool) : bitFlagAt i x = bflag (x.getD i.length false) := by
 unfold bitFlagAt
 generalize i.length = j
 induction j generalizing x with
 | zero => cases x with | nil => rfl | cons b l => cases b <;> rfl
 | succ j ih => cases x with | nil => rfl | cons b l => exact ih l
end Packed
section MatchingExterior
open scoped BigOperators Matrix
abbrev extTable (d : ℕ) := Finset (Fin d) → Finset (Fin d) → ℤ
def extVector {n d : ℕ} (x : Fin n) (i : Fin d) : ℤ := (x.val : ℤ) ^ i.val
def extAppendLeft {d : ℕ} (v : Fin d → ℤ) (D : extTable d) : extTable d :=
 fun S T => ∑ i ∈ S, (-1 : ℤ) ^ (S.filter (fun j => i < j)).card * v i * D (S.erase i) T
def extAppendRight {d : ℕ} (v : Fin d → ℤ) (D : extTable d) : extTable d :=
 fun S T => ∑ i ∈ T, (-1 : ℤ) ^ (T.filter (fun j => i < j)).card * v i * D S (T.erase i)
def extInit (d : ℕ) : extTable d := fun S T => if S = ∅ ∧ T = ∅ then 1 else 0
def extTake {n d : ℕ} (e : Fin n × Fin n) (D : extTable d) : extTable d :=
 extAppendRight (extVector e.2) (extAppendRight (extVector e.1)
  (extAppendLeft (extVector e.2) (extAppendLeft (extVector e.1) D)))
def extStep {n d : ℕ} (e : Fin n × Fin n) (D : extTable d) : extTable d := D + extTake e D
def extRun {n : ℕ} (d : ℕ) (edges : List (Fin n × Fin n)) : extTable d :=
 edges.foldr extStep (extInit d)
def extEdgeEnds {n : ℕ} (e : Fin n × Fin n) : Finset (Fin n) := {e.1, e.2}
def extMatching {n : ℕ} (Q : Finset (Fin n × Fin n)) : Prop :=
 ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (extEdgeEnds e) (extEdgeEnds f)
def extWeight {n : ℕ} (V : Finset (Fin n)) : ℕ :=
 ∏ i ∈ V, ∏ j ∈ V.filter (fun j => i < j), (j.val - i.val) ^ 2
private theorem extGreater_map {n r : ℕ} (S : Finset (Fin n)) (h : S.card = r) (i : Fin r) :
    (Finset.Ioi i).map (S.orderEmbOfFin h).toEmbedding =
      S.filter (fun j => S.orderEmbOfFin h i < j) := by
  let f := S.orderEmbOfFin h
  calc
    _ = (Finset.univ.map f.toEmbedding).filter (fun j => f i < j) := by
      rw [Finset.filter_map]
      congr 1
      ext j
      simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.comp_apply]
      exact f.strictMono.lt_iff_lt.symm
    _ = _ := by rw [show Finset.univ.map f.toEmbedding = S from
      Finset.map_orderEmbOfFin_univ S h]
private theorem extErase_orderEmb {d r : ℕ} (S : Finset (Fin d)) (h : S.card = r + 1)
  (i : Fin (r + 1)) (h' : (S.erase (S.orderEmbOfFin h i)).card = r) :
  (fun j => S.orderEmbOfFin h (i.succAbove j)) =
   ⇑((S.erase (S.orderEmbOfFin h i)).orderEmbOfFin h') := by
 apply Finset.orderEmbOfFin_unique h'
 ·
  intro j
  exact Finset.mem_erase.mpr ⟨fun hj => Fin.succAbove_ne i j
   ((S.orderEmbOfFin h).injective hj), S.orderEmbOfFin_mem h _⟩
 · exact (S.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove i)
private noncomputable def extMinorTuple {n d r : ℕ} (S : Finset (Fin d))
  (xs : Fin r → Fin n) : ℤ :=
 if h : S.card = r then
  (Matrix.of (fun i j : Fin r => extVector (xs j) (S.orderEmbOfFin h i))).det
 else 0
private noncomputable def extMinor {n d : ℕ} (S : Finset (Fin d)) (xs : List (Fin n)) : ℤ :=
 extMinorTuple S xs.get
private theorem extMinorTuple_snoc {n d r : ℕ} (S : Finset (Fin d))
    (xs : Fin r → Fin n) (x : Fin n) :
    extMinorTuple S (Fin.snoc xs x : Fin (r + 1) → Fin n) =
      ∑ a ∈ S, (-1 : ℤ) ^ (S.filter (fun j => a < j)).card * extVector x a *
        extMinorTuple (S.erase a) xs := by
  by_cases h : S.card = r + 1
  · let f := (S.orderEmbOfFin h).toEmbedding
    let term (a : Fin d) := (-1 : ℤ) ^ (S.filter (fun j => a < j)).card * extVector x a *
      extMinorTuple (S.erase a) xs
    let M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ :=
      Matrix.of (fun i j => extVector ((Fin.snoc xs x : Fin (r + 1) → Fin n) j) (f i))
    change (if h' : S.card = r + 1 then
      (Matrix.of (fun i j : Fin (r + 1) => extVector ((Fin.snoc xs x : Fin (r + 1) → Fin n) j)
        (S.orderEmbOfFin h' i))).det else 0) = S.sum term
    rw [dif_pos h]
    change M.det = S.sum term
    calc
      M.det = ∑ i : Fin (r + 1), term (f i) := by
        rw [Matrix.det_succ_column M (Fin.last r)]
        apply Finset.sum_congr rfl
        intro i _
        have hi : f i ∈ S := S.orderEmbOfFin_mem h i
        have herase : (S.erase (f i)).card = r := by
          rw [Finset.card_erase_of_mem hi, h, Nat.add_sub_cancel]
        have hrank : (S.filter (fun j => f i < j)).card = r - i.val := by
          change (S.filter (fun j => S.orderEmbOfFin h i < j)).card = _
          simp only [← extGreater_map S h i, Finset.card_map, Fin.card_Ioi, Nat.succ_sub_one]
        have hpow : (-1 : ℤ) ^ (i.val + r) = (-1 : ℤ) ^ (r - i.val) := by
          have hi' := i.isLt
          rw [show i.val + r = (r - i.val) + 2 * i.val by omega, pow_add, pow_mul]
          norm_num
        have hsub : M.submatrix i.succAbove (Fin.last r).succAbove =
            Matrix.of (fun p q : Fin r =>
              extVector (xs q) ((S.erase (f i)).orderEmbOfFin herase p)) := by
          ext p q
          change extVector ((Fin.snoc xs x : Fin (r + 1) → Fin n) ((Fin.last r).succAbove q))
            (f (i.succAbove p)) = _
          rw [Fin.succAbove_last, Fin.snoc_castSucc]
          exact congrArg (extVector (xs q)) (congrFun (extErase_orderEmb S h i herase) p)
        change (-1 : ℤ) ^ (i.val + r) *
          extVector ((Fin.snoc xs x : Fin (r + 1) → Fin n) (Fin.last r)) (f i) *
          (M.submatrix i.succAbove (Fin.last r).succAbove).det = term (f i)
        rw [hpow, Fin.snoc_last, hsub]
        simp only [term, hrank, extMinorTuple, dif_pos herase]
      _ = (Finset.univ.map f).sum term := (Finset.sum_map _ _ _).symm
      _ = S.sum term :=
        congrArg (fun R : Finset (Fin d) => R.sum term) (Finset.map_orderEmbOfFin_univ S h)
  · rw [extMinorTuple, dif_neg h]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    have h' : (S.erase a).card ≠ r := by
      intro heq
      exact h ((Finset.card_erase_add_one ha).symm.trans (congrArg (· + 1) heq))
    simp only [extMinorTuple, dif_neg h', mul_zero]
private theorem extMinorTuple_cast {n d r s : ℕ} (S : Finset (Fin d)) (h : r = s)
  (xs : Fin s → Fin n) : extMinorTuple S (fun i => xs (Fin.cast h i)) = extMinorTuple S xs := by
 subst s
 rfl
private theorem extMinor_concat {n d : ℕ} (S : Finset (Fin d)) (xs : List (Fin n)) (x : Fin n) :
  extMinor S (xs.concat x) =
   ∑ a ∈ S, (-1 : ℤ) ^ (S.filter (fun j => a < j)).card * extVector x a *
    extMinor (S.erase a) xs := by
 have hlen : xs.length + 1 = (xs.concat x).length := List.length_concat.symm
 have hget : (fun i => (xs.concat x).get (Fin.cast hlen i)) =
   (Fin.snoc xs.get x : Fin (xs.length + 1) → Fin n) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  ·
   simpa only [Fin.snoc_last, List.get_eq_getElem, Fin.val_cast, Fin.val_last,
    List.concat_eq_append] using
    (List.getElem_concat_length (l := xs) (a := x) rfl (by simp))
  ·
   simpa only [Fin.snoc_castSucc, List.get_eq_getElem, Fin.val_cast, Fin.val_castSucc,
    List.concat_eq_append] using
    (List.getElem_append_left (as := xs) (bs := [x]) j.isLt
     (h' := by simpa using Nat.lt_succ_of_lt j.isLt))
 change extMinorTuple S (xs.concat x).get = _
 rw [← extMinorTuple_cast S hlen (xs.concat x).get, hget, extMinorTuple_snoc] <;> rfl
private noncomputable def extOuter {n : ℕ} (d : ℕ) (xs ys : List (Fin n)) : extTable d :=
 fun S T => extMinor S xs * extMinor T ys
private theorem extAppendLeft_outer {n d : ℕ} (xs ys : List (Fin n)) (x : Fin n) :
  extAppendLeft (extVector x) (extOuter d xs ys) = extOuter d (xs.concat x) ys := by
 funext S T
 simp only [extAppendLeft, extOuter, extMinor_concat, Finset.sum_mul, mul_assoc]
private theorem extAppendRight_outer {n d : ℕ} (xs ys : List (Fin n)) (x : Fin n) :
  extAppendRight (extVector x) (extOuter d xs ys) = extOuter d xs (ys.concat x) := by
 funext S T
 simp only [extAppendRight, extOuter, extMinor_concat, Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro i _
 ring
private theorem extAppendLeft_sum {d : ℕ} {α : Type*} (P : Finset α) (v : Fin d → ℤ)
  (F : α → extTable d) : extAppendLeft v (P.sum F) = P.sum (fun a => extAppendLeft v (F a)) := by
 funext S T
 simp only [extAppendLeft, Finset.sum_apply, Finset.mul_sum]
 rw [Finset.sum_comm]
private theorem extAppendRight_sum {d : ℕ} {α : Type*} (P : Finset α) (v : Fin d → ℤ)
  (F : α → extTable d) : extAppendRight v (P.sum F) = P.sum (fun a => extAppendRight v (F a)) := by
 funext S T
 simp only [extAppendRight, Finset.sum_apply, Finset.mul_sum]
 rw [Finset.sum_comm]
private theorem extTake_sum {n d : ℕ} {α : Type*} (P : Finset α) (e : Fin n × Fin n)
  (F : α → extTable d) : extTake e (P.sum F) = P.sum (fun a => extTake e (F a)) := by
 simp only [extTake, extAppendLeft_sum, extAppendRight_sum]
private def extEndpoints {n : ℕ} : List (Fin n × Fin n) → Finset (Fin n × Fin n) → List (Fin n)
 | [], _ => []
 | e :: es, Q =>
  if e ∈ Q then ((extEndpoints es Q).concat e.1).concat e.2 else extEndpoints es Q
private theorem extEndpoints_congr {n : ℕ} (es : List (Fin n × Fin n)) {Q R : Finset (Fin n × Fin n)}
  (h : ∀ e ∈ es, e ∈ Q ↔ e ∈ R) : extEndpoints es Q = extEndpoints es R := by
 induction es with
 | nil => rfl
 | cons e es ih =>
  have he := h e List.mem_cons_self
  have ht := ih (fun f hf => h f (List.mem_cons_of_mem _ hf))
  simp only [extEndpoints, he, ht]
private theorem extRun_eq_sum {n : ℕ} (d : ℕ) (es : List (Fin n × Fin n)) (hn : es.Nodup) :
  extRun d es = ∑ Q ∈ es.toFinset.powerset, extOuter d (extEndpoints es Q) (extEndpoints es Q) := by
 induction es with
 | nil =>
  funext S T
  simp only [extRun, List.foldr_nil, List.toFinset_nil, Finset.powerset_empty, Finset.sum_singleton,
   extEndpoints, extOuter, extInit, extMinor, List.length_nil, extMinorTuple]
  by_cases hS : S = ∅ <;> by_cases hT : T = ∅ <;>
   simp [hS, hT, Finset.card_eq_zero]
 | cons e es ih =>
  have ⟨he', hn'⟩ := List.nodup_cons.mp hn
  have he : e ∉ es.toFinset := by simpa using he'
  have hnQ : ∀ {Q}, Q ∈ es.toFinset.powerset → e ∉ Q :=
   fun hQ h => he (Finset.mem_powerset.mp hQ h)
  have hdis : Disjoint es.toFinset.powerset (es.toFinset.powerset.image (insert e)) := by
   refine Finset.disjoint_left.mpr (fun Q hQ hI => ?_)
   obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hI
   exact hnQ hQ (Finset.mem_insert_self _ _)
  have hins : Set.InjOn (insert e) (↑es.toFinset.powerset : Set (Finset (Fin n × Fin n))) := by
   intro Q hQ R hR h
   have hQ' := hnQ hQ
   have hR' := hnQ hR
   simpa only [Finset.erase_insert hQ', Finset.erase_insert hR'] using
    congrArg (fun S : Finset (Fin n × Fin n) => S.erase e) h
  have htail : ∀ Q, extEndpoints es (insert e Q) = extEndpoints es Q := by
   intro Q
   exact extEndpoints_congr es (fun f hf => by
    have hfe : f ≠ e := fun h => he' (h ▸ hf)
    simp [Finset.mem_insert, hfe])
  change extStep e (extRun d es) = _
  rw [extStep, ih hn', extTake_sum, List.toFinset_cons, Finset.powerset_insert,
   Finset.sum_union hdis, Finset.sum_image hins]
  congr 1
  ·
   apply Finset.sum_congr rfl
   intro Q hQ
   simp only [extEndpoints, if_neg (hnQ hQ)]
  ·
   apply Finset.sum_congr rfl
   intro Q _
   simp only [extTake, extAppendLeft_outer, extAppendRight_outer, extEndpoints,
    Finset.mem_insert_self, if_true, htail]
private def extSelected {n : ℕ} (es : List (Fin n × Fin n)) (Q : Finset (Fin n × Fin n)) :=
 (es.filter (fun e => decide (e ∈ Q))).reverse
private def extEdgeList {n : ℕ} (e : Fin n × Fin n) : List (Fin n) := [e.1, e.2]
private theorem extEndpoints_flatMap {n : ℕ} (es : List (Fin n × Fin n))
  (Q : Finset (Fin n × Fin n)) : extEndpoints es Q = (extSelected es Q).flatMap extEdgeList := by
 induction es with
 | nil => rfl
 | cons e es ih =>
  by_cases h : e ∈ Q <;>
   simp [extEndpoints, extSelected, ih, h, extEdgeList, List.reverse_cons, List.flatMap_append,
    List.append_assoc]
private theorem extSelected_mem {n : ℕ} {es : List (Fin n × Fin n)} {Q : Finset (Fin n × Fin n)}
  (hQ : Q ⊆ es.toFinset) (e : Fin n × Fin n) : e ∈ extSelected es Q ↔ e ∈ Q := by
 simp only [extSelected, List.mem_reverse, List.mem_filter, decide_eq_true_eq]
 exact ⟨And.right, fun he => ⟨List.mem_toFinset.mp (hQ he), he⟩⟩
private theorem extSelected_nodup {n : ℕ} {es : List (Fin n × Fin n)} (hn : es.Nodup)
  (Q : Finset (Fin n × Fin n)) : (extSelected es Q).Nodup :=
 List.nodup_reverse.mpr (hn.filter _)
private theorem extEndpoints_length {n : ℕ} {es : List (Fin n × Fin n)} (hn : es.Nodup)
    {Q : Finset (Fin n × Fin n)} (hQ : Q ⊆ es.toFinset) :
    (extEndpoints es Q).length = 2 * Q.card := by
  have hcard : (extSelected es Q).toFinset = Q := Finset.ext (fun e =>
    List.mem_toFinset.trans (extSelected_mem hQ e))
  calc
    (extEndpoints es Q).length = 2 * (extSelected es Q).length := by
      rw [extEndpoints_flatMap]
      generalize extSelected es Q = L
      induction L with
      | nil => simp
      | cons e L ih => simp [extEdgeList, ih, Nat.mul_succ, Nat.add_comm] <;> omega
    _ = 2 * Q.card := by
      rw [← List.toFinset_card_of_nodup (extSelected_nodup hn Q), hcard]
private theorem extEndpoints_toFinset {n : ℕ} {es : List (Fin n × Fin n)}
  {Q : Finset (Fin n × Fin n)} (hQ : Q ⊆ es.toFinset) :
  (extEndpoints es Q).toFinset = Q.biUnion extEdgeEnds := by
 rw [extEndpoints_flatMap]
 ext x
 simp [List.mem_flatMap, Finset.mem_biUnion, extSelected_mem hQ, extEdgeList, extEdgeEnds]
private theorem extEdgeList_disjoint {n : ℕ} (e f : Fin n × Fin n) :
  List.Disjoint (extEdgeList e) (extEdgeList f) ↔ Disjoint (extEdgeEnds e) (extEdgeEnds f) := by
 simp [List.disjoint_left, Finset.disjoint_left, extEdgeEnds, extEdgeList]
private theorem extEndpoints_nodup {n : ℕ} {es : List (Fin n × Fin n)} (hn : es.Nodup)
  {Q : Finset (Fin n × Fin n)} (hQ : Q ⊆ es.toFinset) (ho : ∀ e ∈ Q, e.1 < e.2) :
  (extEndpoints es Q).Nodup ↔ extMatching Q := by
 rw [extEndpoints_flatMap, List.nodup_flatMap]
 have hwithin : ∀ e ∈ extSelected es Q, (extEdgeList e).Nodup := by
  intro e he
  have hne := ne_of_lt (ho e ((extSelected_mem hQ e).mp he))
  simp [extEdgeList, hne]
 rw [and_iff_right hwithin]
 constructor
 ·
  intro hp e he f hf hne
  let R := fun e f : Fin n × Fin n => Disjoint (extEdgeEnds e) (extEdgeEnds f)
  haveI : Std.Symm R := ⟨fun _ _ h => h.symm⟩
  have hp' : (extSelected es Q).Pairwise R := hp.imp (fun {e f} h =>
   (extEdgeList_disjoint e f).mp h)
  exact hp'.forall ((extSelected_mem hQ e).mpr he) ((extSelected_mem hQ f).mpr hf) hne
 ·
  intro hp
  apply (extSelected_nodup hn Q).pairwise_of_forall_ne
  intro e he f hf hne
  exact (extEdgeList_disjoint e f).mpr
   (hp e ((extSelected_mem hQ e).mp he) f ((extSelected_mem hQ f).mp hf) hne)
private theorem extMinor_univ {n d : ℕ} (xs : List (Fin n)) :
  extMinor (Finset.univ : Finset (Fin d)) xs =
   if d = xs.length then (Matrix.vandermonde (fun i => ((xs.get i).val : ℤ))).det else 0 := by
 by_cases h : d = xs.length
 ·
  subst d
  have hu : (Finset.univ : Finset (Fin xs.length)).card = xs.length := by simp
  have hid : (fun i : Fin xs.length => i) =
    ⇑((Finset.univ : Finset (Fin xs.length)).orderEmbOfFin hu) :=
   Finset.orderEmbOfFin_unique hu (fun _ => Finset.mem_univ _) strictMono_id
  rw [extMinor, extMinorTuple, dif_pos hu, if_pos rfl]
  have hm : (Matrix.of (fun i j : Fin xs.length => extVector (xs.get j)
    ((Finset.univ : Finset (Fin xs.length)).orderEmbOfFin hu i))) =
    (Matrix.vandermonde (fun i => ((xs.get i).val : ℤ)))ᵀ := by
   ext i j
   change ((xs.get j).val : ℤ) ^ ((Finset.univ : Finset (Fin xs.length)).orderEmbOfFin hu i).val =
    ((xs.get j).val : ℤ) ^ i.val
   rw [← hid]
  rw [hm, Matrix.det_transpose]
 · simp [extMinor, extMinorTuple, h]
private theorem extVandermonde_sorted_sq {n r : ℕ} (V : Finset (Fin n)) (h : V.card = r) :
    (Matrix.vandermonde (fun i => ((V.orderEmbOfFin h i).val : ℤ))).det ^ 2 =
      (extWeight V : ℤ) := by
  rw [Matrix.det_vandermonde]
  simp only [← Finset.prod_pow, extWeight, Nat.cast_prod, Nat.cast_pow]
  let f := (V.orderEmbOfFin h).toEmbedding
  let g (x : Fin n) : ℤ := ∏ y ∈ V.filter (fun y => x < y), ((y.val - x.val : ℕ) : ℤ) ^ 2
  calc
    _ = ∏ i : Fin r, g (f i) := by
      apply Finset.prod_congr rfl
      intro i _
      change (∏ j ∈ Finset.Ioi i, (((f j).val : ℤ) - (f i).val) ^ 2) =
        ∏ y ∈ V.filter (fun y => V.orderEmbOfFin h i < y), ((y.val - (f i).val : ℕ) : ℤ) ^ 2
      rw [← extGreater_map V h i, Finset.prod_map]
      apply Finset.prod_congr rfl
      intro j hj
      have hle : (f i).val ≤ (f j).val :=
        ((V.orderEmbOfFin h).strictMono (Finset.mem_Ioi.mp hj)).le
      rw [Nat.cast_sub hle]
    _ = (Finset.univ.map f).prod g := (Finset.prod_map _ _ _).symm
    _ = _ := congrArg (fun R : Finset (Fin n) => R.prod g) (Finset.map_orderEmbOfFin_univ V h)
private theorem extVandermonde_sq {n : ℕ} (xs : List (Fin n)) (hn : xs.Nodup) :
    (Matrix.vandermonde (fun i => ((xs.get i).val : ℤ))).det ^ 2 =
      (extWeight xs.toFinset : ℤ) := by
  let V := xs.toFinset
  have hV : V.card = xs.length := List.toFinset_card_of_nodup hn
  let f (i : Fin xs.length) : ↥V := ⟨xs.get i, List.mem_toFinset.mpr (List.get_mem xs i)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact hn.injective_get (congrArg Subtype.val hij)
    · intro v
      obtain ⟨i, hi⟩ := List.get_of_mem (List.mem_toFinset.mp v.property)
      exact ⟨i, Subtype.ext hi⟩
  let E := V.orderIsoOfFin hV
  let σ : Equiv.Perm (Fin xs.length) := (Equiv.ofBijective f hf).trans E.toEquiv.symm
  have hσ (i : Fin xs.length) : V.orderEmbOfFin hV (σ i) = xs.get i := by
    change (↑(E (E.symm (f i))) : Fin n) = xs.get i
    rw [E.apply_symm_apply] <;> rfl
  let M := Matrix.vandermonde (fun i => ((V.orderEmbOfFin hV i).val : ℤ))
  have hm : Matrix.vandermonde (fun i => ((xs.get i).val : ℤ)) = M.submatrix σ id := by
    ext i j
    change ((xs.get i).val : ℤ) ^ j.val = ((V.orderEmbOfFin hV (σ i)).val : ℤ) ^ j.val
    rw [hσ]
  rw [hm, ← extVandermonde_sorted_sq V hV]
  have ha := Matrix.abs_det_submatrix_equiv_equiv σ (Equiv.refl _) M
  change (M.submatrix σ id).det ^ 2 = M.det ^ 2
  calc
    _ = |(M.submatrix σ id).det| ^ 2 := (sq_abs _).symm
    _ = |M.det| ^ 2 := congrArg (fun z : ℤ => z ^ (2 : ℕ)) ha
    _ = _ := sq_abs _
private theorem extVandermonde_zero {n : ℕ} (xs : List (Fin n)) (hn : ¬ xs.Nodup) :
  (Matrix.vandermonde (fun i => ((xs.get i).val : ℤ))).det = 0 := by
 apply Matrix.det_vandermonde_eq_zero_iff.mpr
 by_contra h
 exact hn (List.nodup_iff_injective_get.mpr (fun i j hij => by
  by_contra hne
  exact h ⟨i, j, congrArg (fun v : Fin n => (v.val : ℤ)) hij, hne⟩))
open scoped Classical in

theorem extRun_matching {n : ℕ} (k : ℕ) (edges : List (Fin n × Fin n))
  (hn : edges.Nodup) (ho : ∀ e ∈ edges, e.1 < e.2) :
  extRun (2 * k) edges Finset.univ Finset.univ =
   ∑ Q ∈ (edges.toFinset.powerset.filter (fun Q => Q.card = k ∧ extMatching Q)),
    (extWeight (Q.biUnion extEdgeEnds) : ℤ) := by
 classical
 rw [extRun_eq_sum _ edges hn, Finset.sum_apply, Finset.sum_apply, Finset.sum_filter]
 apply Finset.sum_congr rfl
 intro Q hQ'
 have hQ := Finset.mem_powerset.mp hQ'
 have hlen : 2 * k = (extEndpoints edges Q).length ↔ Q.card = k := by
  rw [extEndpoints_length hn hQ]
  omega
 have hN : (extEndpoints edges Q).Nodup ↔ extMatching Q :=
  extEndpoints_nodup hn hQ (fun e he => ho e (List.mem_toFinset.mp (hQ he)))
 rw [extOuter, extMinor_univ]
 by_cases hc : Q.card = k
 ·
  rw [ite_eq_left (hlen.mpr hc)]
  by_cases hM : extMatching Q
  ·
   rw [if_pos (And.intro hc hM), ← pow_two, extVandermonde_sq _ (hN.mpr hM),
    extEndpoints_toFinset hQ]
  ·
   have hbad : ¬ (Q.card = k ∧ extMatching Q) := fun hh => hM hh.2
   rw [if_neg hbad, extVandermonde_zero _ (mt hN.mp hM), zero_mul]
 ·
  have hbad : ¬ (Q.card = k ∧ extMatching Q) := fun hh => hc hh.1
  rw [ite_eq_right (mt hlen.mp hc), ite_eq_right hbad, zero_mul]
open scoped Classical in

theorem extRun_matching_of_toFinset {n : ℕ} (k : ℕ) (A : Finset (Fin n × Fin n))
  (edges : List (Fin n × Fin n)) (hn : edges.Nodup) (hA : edges.toFinset = A)
  (ho : ∀ e ∈ A, e.1 < e.2) :
  extRun (2 * k) edges Finset.univ Finset.univ =
   ∑ Q ∈ (A.powerset.filter (fun Q => Q.card = k ∧ extMatching Q)),
    (extWeight (Q.biUnion extEdgeEnds) : ℤ) := by
 classical
 rw [← hA]
 exact extRun_matching k edges hn (fun e he => ho e (hA ▸ List.mem_toFinset.mpr he))
end MatchingExterior
namespace Packed
open Lib.Universal
def maskBits {d : ℕ} (S : Finset (Fin d)) : List Bool :=
 (List.finRange d).map (fun i => decide (i ∈ S))
def maskIndex {d : ℕ} (S : Finset (Fin d)) : ℕ := val (maskBits S)
lemma maskBits_length {d : ℕ} (S : Finset (Fin d)) : (maskBits S).length = d := by simp [maskBits]
lemma maskIndex_lt {d : ℕ} (S : Finset (Fin d)) : maskIndex S < 2^d := by
 simpa [maskIndex, maskBits_length] using q124 (maskBits S)
lemma val_cons_bit (b : Bool) (xs : List Bool) : val (b :: xs) = Nat.bit b (val xs) := by
 cases b <;> simp [val, Nat.bit] <;> omega
lemma val_length_inj {a b : List Bool} (h : a.length = b.length) (hv : val a = val b) : a = b := by
 induction a generalizing b with
 | nil => simpa using h.symm
 | cons x a ih =>
  cases b with
  | nil => simp at h
  | cons y b =>
   have he : x = y := by
    have hm := congrArg (· % 2) hv
    change (x.toNat + 2 * val a) % 2 = (y.toNat + 2 * val b) % 2 at hm
    cases x <;> cases y <;> simp at hm ⊢ <;> omega
   subst y
   have hh : val a = val b := by simp only [val] at hv; omega
   exact congrArg (x :: ·) (ih (by simpa using h) hh)
lemma val_bitAt (xs : List Bool) (i : ℕ) : (val xs).testBit i = xs.getD i false := by
 induction xs generalizing i with
 | nil => simp [val]
 | cons b xs ih =>
  cases i with
  | zero => simp [val_cons_bit, Nat.testBit_bit_zero]
  | succ i => simpa [val_cons_bit, Nat.testBit_bit_succ] using ih i
lemma maskIndex_bit {d : ℕ} (S : Finset (Fin d)) (j : Fin d) :
  (maskIndex S).testBit j.val = decide (j ∈ S) := by
 rw [maskIndex, val_bitAt, maskBits, List.getD_eq_getElem _ _ (by simpa using j.isLt)]
 simp
lemma val_ofFn {d : ℕ} (f : Fin d → Bool) :
  val (List.ofFn f) = ∑ i : Fin d, if f i then 2^i.val else 0 := by
 induction d with
 | zero => simp [val]
 | succ d ih =>
  rw [List.ofFn_succ, val, ih, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero, pow_succ, Finset.mul_sum]
  cases h0 : f 0 <;> simp [h0, mul_comm 2]
lemma maskIndex_eq_sum {d : ℕ} (S : Finset (Fin d)) : maskIndex S = ∑ i ∈ S, 2^i.val := by
 rw [maskIndex, maskBits, List.finRange, List.map_ofFn, val_ofFn]
 simp [Finset.sum_filter]
lemma maskIndex_erase {d : ℕ} (S : Finset (Fin d)) {i : Fin d} (hi : i ∈ S) :
  maskIndex S - 2^i.val = maskIndex (S.erase i) := by
 rw [maskIndex_eq_sum, maskIndex_eq_sum, ← Finset.sum_erase_add _ _ hi]
 exact Nat.add_sub_cancel _ _
lemma maskIndex_empty {d : ℕ} (S : Finset (Fin d)) : maskIndex S = 0 ↔ S = ∅ := by
 constructor
 ·
  intro h
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hh := maskIndex_bit S i
  simp [h, hi] at hh
 ·
  rintro rfl
  simp [maskIndex_eq_sum]
lemma maskIndex_univ (d : ℕ) : maskIndex (Finset.univ : Finset (Fin d)) = 2^d - 1 := by
 apply Nat.eq_of_testBit_eq
 intro i
 rw [Nat.testBit_two_pow_sub_one]
 by_cases hi : i < d
 · simpa [hi] using maskIndex_bit (Finset.univ : Finset (Fin d)) ⟨i, hi⟩
 ·
  have hh : maskIndex (Finset.univ : Finset (Fin d)) < 2^i :=
   (maskIndex_lt _).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi))
  simp [hi, Nat.testBit_eq_false_of_lt hh]
lemma maskBits_pad {d : ℕ} (S : Finset (Fin d)) :
  padW (un d) (q48 (un (maskIndex S))) = maskBits S := by
 apply val_length_inj
 · simp [q19, maskBits_length]
 ·
  rw [q26, q71, q194, un_length, un_length, Nat.mod_eq_of_lt (maskIndex_lt S)]
  rfl
lemma mem_finRange_drop {d : ℕ} (j : Fin d) (i : ℕ) :
  j ∈ (List.finRange d).drop i ↔ i ≤ j.val := by
 constructor
 ·
  intro h
  obtain ⟨p, hp⟩ := List.get_of_mem h
  have hp' : p.val < d - i := by simpa using p.isLt
  have he : (List.finRange d)[i + p.val]'(by simp; omega) = j := by
   simpa only [List.get_eq_getElem, List.getElem_drop, Nat.add_comm] using hp
  have he' := congrArg Fin.val he
  simp at he'
  omega
 ·
  intro h
  let p : Fin ((List.finRange d).drop i).length := ⟨j.val-i, by simp; omega⟩
  have hp : ((List.finRange d).drop i).get p = j := by
   apply Fin.ext
   simp [p]
   omega
  rw [← hp]
  exact List.get_mem _ _
lemma maskBits_gt {d : ℕ} (S : Finset (Fin d)) (i : Fin d) :
  (q49 ((maskBits S).drop (i.val+1))).length = (S.filter (fun j => i < j)).card := by
 let L := (((List.finRange d).drop (i.val+1)).filter (fun j => decide (j ∈ S)))
 have hL : L.Nodup := (List.nodup_finRange d).drop.filter _
 have hS : L.toFinset = S.filter (fun j => i < j) := by
  ext j
  simp only [L, List.mem_toFinset, List.mem_filter, mem_finRange_drop, decide_eq_true_eq, Finset.mem_filter]
  exact ⟨fun ⟨h, hS⟩ => ⟨hS,h⟩, fun ⟨hS,h⟩ => ⟨h,hS⟩⟩
 rw [← hS, List.toFinset_card_of_nodup hL]
 simp only [q49, maskBits, ← List.map_drop, List.filter_map, List.length_map, L, Function.comp_def, id]
end Packed
namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal
def pack : List (List Bool) → List Bool
 | [] => []
 | x :: xs => pairB x (pack xs)
def field : ℕ → List Bool → List Bool
 | 0, x => left x
 | j+1, x => field j (right x)
lemma cpField (j : ℕ) {f : List Bool → List Bool} (hf : Lib.CPTs f) :
  Lib.CPTs (fun s => field j (f s)) := by
 induction j generalizing f with
 | zero => exact cpLeft hf
 | succ j ih => exact ih (cpRight hf)
lemma cpPack (L : List (List Bool → List Bool)) (h : ∀ f ∈ L, Lib.CPTs f) :
  Lib.CPTs (fun s => pack (L.map (fun f => f s))) := by
 induction L with
 | nil => exact cpt_const []
 | cons f L ih => exact cpt_pairB2 (h f (by simp)) (ih (fun g hg => h g (by simp [hg])))
lemma field_pack_zero (x : List Bool) (xs : List (List Bool)) :
 field 0 (pack (x :: xs)) = x := by simp [field, pack, left, unpairB_pairB]
lemma field_pack_succ (j : ℕ) (x : List Bool) (xs : List (List Bool)) :
 field (j+1) (pack (x :: xs)) = field j (pack xs) := by simp [field, pack, right, unpairB_pairB]
lemma field_right_pair (a b : List Bool) : right (pairB a b) = b := by simp [right, unpairB_pairB]
lemma field_left_pair (a b : List Bool) : left (pairB a b) = a := by simp [left, unpairB_pairB]
def tableAt (w count s t tab : List Bool) : List Bool :=
 slot w t (slot (mulU count w) s tab)
lemma cpTableAt {w b i j tab : List Bool → List Bool} (hw : Lib.CPTs w) (hb : Lib.CPTs b)
  (hi : Lib.CPTs i) (hj : Lib.CPTs j) (ht : Lib.CPTs tab) :
  Lib.CPTs (fun s => tableAt (w s) (b s) (i s) (j s) (tab s)) :=
 cpSlot hw hj (cpSlot (q42 hb hw) hi ht)
def tableCell (f : List Bool → List Bool) (x : List Bool) : List Bool :=
 f (pairB (left (right x)) (pairB (left x) (right (right x))))
lemma cpTableCell {f : List Bool → List Bool} (hf : Lib.CPTs f) : Lib.CPTs (tableCell f) := by
 unfold tableCell
 exact cpt_comp (cpt_pairB2 (cpLeft (cpRight cpt_id))
  (cpt_pairB2 (cpLeft cpt_id) (cpRight (cpRight cpt_id)))) hf
def tableRow (f : List Bool → List Bool) (w b s a : List Bool) : List Bool :=
 mapRange (tableCell f) w b (pairB s a)
lemma cpTableRow {f w b s a : List Bool → List Bool} (hf : Lib.CPTs f) (hw : Lib.CPTs w)
  (hb : Lib.CPTs b) (hs : Lib.CPTs s) (ha : Lib.CPTs a) :
  Lib.CPTs (fun x => tableRow f (w x) (b x) (s x) (a x)) :=
 cpMapRange (cpTableCell hf) hw hb (cpt_pairB2 hs ha)
def tableRowPacked (f : List Bool → List Bool) (x : List Bool) : List Bool :=
 tableRow f (field 0 (right x)) (field 1 (right x)) (left x) (field 2 (right x))
def tableMake (f : List Bool → List Bool) (w b a : List Bool) : List Bool :=
 mapRange (tableRowPacked f) (mulU b w) b (pack [w,b,a])
lemma cpTableMake {f w b a : List Bool → List Bool} (hf : Lib.CPTs f) (hw : Lib.CPTs w)
  (hb : Lib.CPTs b) (ha : Lib.CPTs a) :
  Lib.CPTs (fun x => tableMake f (w x) (b x) (a x)) := by
 have hrow : Lib.CPTs (tableRowPacked f) :=
  cpTableRow hf (cpField 0 (cpRight cpt_id)) (cpField 1 (cpRight cpt_id))
   (cpLeft cpt_id) (cpField 2 (cpRight cpt_id))
 have hargs : Lib.CPTs (fun x => pack [w x,b x,a x]) := by
  apply cpPack [w,b,a]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> assumption
 exact cpMapRange hrow (q42 hb hw) hb hargs
lemma flatMap_len {α : Type*} (L : List α) (f : α → List Bool) (k : ℕ)
  (h : ∀ a ∈ L, (f a).length = k) : (L.flatMap f).length = L.length * k := by
 induction L with
 | nil => simp
 | cons a L ih =>
  simp [h a (by simp), ih (fun b hb => h b (by simp [hb])), Nat.succ_mul, Nat.add_comm]
lemma tableMake_eq (f : List Bool → List Bool) (w b a : List Bool)
  (h : ∀ s < b.length, ∀ t < b.length, (f (pairB (un s) (pairB (un t) a))).length = w.length) :
  tableMake f w b a = (List.range b.length).flatMap (fun s =>
    (List.range b.length).flatMap (fun t => f (pairB (un s) (pairB (un t) a)))) := by
 have hrow (s : ℕ) (hs : s < b.length) :
   tableRowPacked f (pairB (un s) (pack [w,b,a])) =
   (List.range b.length).flatMap (fun t => f (pairB (un s) (pairB (un t) a))) := by
  simp only [tableRowPacked, field_left_pair, field_right_pair, field_pack_succ, field_pack_zero, tableRow]
  rw [mapRange_eq]
  · simp [tableCell, field_left_pair, field_right_pair]
  ·
   intro t ht
   simp [tableCell, field_left_pair, field_right_pair, h s hs t ht]
 unfold tableMake
 rw [mapRange_eq]
 · exact List.flatMap_congr fun s hs => hrow s (List.mem_range.mp hs)
 ·
  intro s hs
  rw [hrow s hs, flatMap_len _ _ w.length (fun t ht => h s hs t (List.mem_range.mp ht))]
  simp [mulU]
lemma tableMake_length (f : List Bool → List Bool) (w b a : List Bool)
  (h : ∀ s < b.length, ∀ t < b.length, (f (pairB (un s) (pairB (un t) a))).length = w.length) :
  (tableMake f w b a).length = b.length * (b.length * w.length) := by
 rw [tableMake_eq f w b a h]
 refine (flatMap_len _ _ (b.length * w.length) (fun s hs => ?_)).trans (by rw [List.length_range])
 simpa using flatMap_len _ _ w.length (fun t ht => h s (List.mem_range.mp hs) t (List.mem_range.mp ht))
lemma tableAt_make (f : List Bool → List Bool) (w b a : List Bool) (s t : ℕ)
  (hs : s < b.length) (ht : t < b.length)
  (h : ∀ s < b.length, ∀ t < b.length, (f (pairB (un s) (pairB (un t) a))).length = w.length) :
  tableAt w b (un s) (un t) (tableMake f w b a) = f (pairB (un s) (pairB (un t) a)) := by
 let row (i : ℕ) := (List.range b.length).flatMap (fun j => f (pairB (un i) (pairB (un j) a)))
 have hrow : ∀ i ∈ List.range b.length, (row i).length = (mulU b w).length := by
  intro i hi
  dsimp only [row]
  rw [flatMap_len _ _ w.length (fun j hj => h i (List.mem_range.mp hi) j (List.mem_range.mp hj))]
  simp [mulU]
 have hs' : s < (List.range b.length).length := by simpa
 have ht' : t < (List.range b.length).length := by simpa
 rw [tableMake_eq f w b a h, tableAt, slot_flatMap (List.range b.length) row _ s hs' hrow]
 simp only [List.getElem_range, row]
 rw [slot_flatMap _ _ _ t ht' (fun j hj => h s hs j (List.mem_range.mp hj))]
 simp
def tableRep {d : ℕ} (w b tab : List Bool) (D : extTable d) : Prop :=
 tab.length = b.length * (b.length * w.length) ∧
 ∀ S T, rep w (tableAt w b (un (maskIndex S)) (un (maskIndex T)) tab) (D S T)
lemma tableMake_rep {d : ℕ} (f : List Bool → List Bool) (w b a : List Bool) (D : extTable d)
  (hb : b.length = 2^d)
  (hlen : ∀ s < b.length, ∀ t < b.length, (f (pairB (un s) (pairB (un t) a))).length = w.length)
  (h : ∀ S T : Finset (Fin d),
   rep w (f (pairB (un (maskIndex S)) (pairB (un (maskIndex T)) a))) (D S T)) :
  tableRep w b (tableMake f w b a) D := by
 refine ⟨tableMake_length f w b a hlen, fun S T => ?_⟩
 rw [tableAt_make f w b a _ _ (hb ▸ maskIndex_lt S) (hb ▸ maskIndex_lt T) hlen]
 exact h S T
end Packed
namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal
def signedWord (w flag b : List Bool) : List Bool := sel flag b (negW w b)
lemma cpSignedWord {w f b : List Bool → List Bool} (hw : Lib.CPTs w) (hf : Lib.CPTs f)
  (hb : Lib.CPTs b) : Lib.CPTs (fun s => signedWord (w s) (f s) (b s)) :=
 cpt_sel hf hb (q120 hw hb)
lemma pow_neg_one_mod (a : ℕ) : (-1 : ℤ)^a = if a % 2 = 1 then -1 else 1 := by
  calc
    _ = (-1 : ℤ)^(2*(a/2) + a%2) := congrArg ((-1 : ℤ) ^ ·) (by omega)
    _ = _ := by
      rw [pow_add, pow_mul]
      norm_num
      rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]
lemma parity_word_rep {w x u : List Bool} {z : ℤ} (hz : rep w x z) :
  rep w (signedWord w (q112 u) x) ((-1 : ℤ)^u.length * z) := by
 rw [pow_neg_one_mod]
 by_cases h : u.length % 2 = 1
 · simpa [signedWord, sel, q112, h] using rep_neg hz
 · simpa [signedWord, sel, q112, h] using hz
def initCell (s : List Bool) : List Bool :=
 let w := right (right s)
 natW w (sel (left s ++ left (right s)) [true] [])
lemma cpInitCell : Lib.CPTs initCell :=
 q50 (cpRight (cpRight cpt_id))
  (cpt_sel (cpt_app2 (cpLeft cpt_id) (cpLeft (cpRight cpt_id))) (cpt_const [true]) (cpt_const []))
def tableInit (w b : List Bool) : List Bool := tableMake initCell w b w
lemma cpTableInit {w b : List Bool → List Bool} (hw : Lib.CPTs w) (hb : Lib.CPTs b) :
 Lib.CPTs (fun s => tableInit (w s) (b s)) := cpTableMake cpInitCell hw hb hw
lemma tableInit_rep {d : ℕ} (w b : List Bool) (hb : b.length = 2^d) :
  tableRep w b (tableInit w b) (extInit d) := by
 apply tableMake_rep _ _ _ _ _ hb
 ·
  intro s hs t ht
  simp [initCell, field_left_pair, field_right_pair, q54]
 ·
  intro S T
  simp only [initCell, field_left_pair, field_right_pair, extInit]
  have h := rep_nat w (sel (un (maskIndex S) ++ un (maskIndex T)) [true] [])
  by_cases hs : S = ∅ <;> by_cases ht : T = ∅ <;>
   simpa [sel, un, hs, ht, maskIndex_empty] using h
def wedgeTerm (onRight : Bool) (s : List Bool) : List Bool :=
 let i := left s
 let a := right s
 let w := field 0 a
 let d := field 1 a
 let b := field 2 a
 let v := field 3 a
 let S := field 4 a
 let T := field 5 a
 let tab := field 6 a
 let U := if onRight then T else S
 let bits := padW d (q48 U)
 let erase := U.drop (powerTwo b i).length
 let coeff := tableAt w b (if onRight then S else erase) (if onRight then erase else T) tab
 let prod := mulW w (powW w (natW w v) i) coeff
 sel (bitFlagAt i bits) (blank w) (signedWord w (q112 (q49 (bits.drop (i.length+1)))) prod)
set_option maxHeartbeats 1000000 in
lemma cpWedgeTerm (r : Bool) : Lib.CPTs (wedgeTerm r) := by
 have hi := cpLeft cpt_id
 have ha := cpRight cpt_id
 have hw := cpField 0 ha
 have hd := cpField 1 ha
 have hb := cpField 2 ha
 have hv := cpField 3 ha
 have hs := cpField 4 ha
 have ht := cpField 5 ha
 have htab := cpField 6 ha
 have hu : Lib.CPTs (fun x => if r then field 5 (right x) else field 4 (right x)) := by
  cases r
  · exact hs
  · exact ht
 have hbits := q13 hd (cpt_comp hu q41)
 have he := cpDrop (powerTwo_cpt hb hi) hu
 have hleft : Lib.CPTs (fun x => if r then field 4 (right x) else
   (if r then field 5 (right x) else field 4 (right x)).drop (powerTwo (field 2 (right x)) (left x)).length) := by
  cases r
  · exact he
  · exact hs
 have hright : Lib.CPTs (fun x => if r then
   (if r then field 5 (right x) else field 4 (right x)).drop (powerTwo (field 2 (right x)) (left x)).length
   else field 5 (right x)) := by
  cases r
  · exact ht
  · exact he
 exact cpt_sel (cpBitFlagAt hi hbits) (cpt_comp hw cpt_blank)
  (cpSignedWord hw (cpt_comp (cpt_comp (cpDrop (cpCons true hi) hbits) q150) q137)
   (q32 hw (q202 hw (q50 hw hv) hi) (cpTableAt hw hb hleft hright htab)))
def wedgeCell (r : Bool) (s : List Bool) : List Bool :=
 let a := right (right s)
 let w := field 0 a
 let d := field 1 a
 sumRange (wedgeTerm r) w d (pack [w,d,field 2 a,field 3 a,left s,left (right s),field 4 a])
lemma cpWedgeCell (r : Bool) : Lib.CPTs (wedgeCell r) := by
 have ha := cpRight (cpRight cpt_id)
 have hw := cpField 0 ha
 have hd := cpField 1 ha
 unfold wedgeCell
 apply cpSumRange (cpWedgeTerm r) hw hd
 apply cpPack [fun s => field 0 (right (right s)), fun s => field 1 (right (right s)),
  fun s => field 2 (right (right s)), fun s => field 3 (right (right s)), left,
  fun s => left (right s), fun s => field 4 (right (right s))]
 intro g hg
 simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
 rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact hw
 · exact hd
 · exact cpField 2 ha
 · exact cpField 3 ha
 · exact cpLeft cpt_id
 · exact cpLeft (cpRight cpt_id)
 · exact cpField 4 ha
def wedgeTable (r : Bool) (w d b v tab : List Bool) : List Bool :=
 tableMake (wedgeCell r) w b (pack [w,d,b,v,tab])
lemma cpWedgeTable (r : Bool) {w d b v tab : List Bool → List Bool} (hw : Lib.CPTs w)
  (hd : Lib.CPTs d) (hb : Lib.CPTs b) (hv : Lib.CPTs v) (htab : Lib.CPTs tab) :
  Lib.CPTs (fun s => wedgeTable r (w s) (d s) (b s) (v s) (tab s)) := by
 apply cpTableMake (cpWedgeCell r) hw hb
 apply cpPack [w,d,b,v,tab]
 intro g hg
 simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
 rcases hg with rfl | rfl | rfl | rfl | rfl <;> assumption
lemma wedgeTerm_rep {n d : ℕ} (r : Bool) (w b tab : List Bool) (v : Fin n)
  (T : extTable d) (hb : b.length = 2^d) (hT : tableRep w b tab T)
  (S U : Finset (Fin d)) (i : Fin d) :
  let M := if r then U else S
  let ix := fun X : Finset (Fin d) => un (maskIndex X)
  rep w (wedgeTerm r (pairB (un i.val) (pack [w,un d,b,un v.val,ix S,ix U,tab])))
   (if i ∈ M then (-1 : ℤ)^(M.filter (fun j => i < j)).card * extVector v i *
    T (if r then S else S.erase i) (if r then U.erase i else U) else 0) := by
 let M := if r then U else S
 let ix := fun X : Finset (Fin d) => un (maskIndex X)
 have hbits : padW (un d) (q48 (ix M)) = maskBits M := maskBits_pad M
 have hbit : bitFlagAt (un i.val) (maskBits M) = bflag (decide (i ∈ M)) := by
  rw [bitFlagAt_eq, un_length, ← val_bitAt, ← maskIndex, maskIndex_bit]
 have hcap : 2^(un i.val).length ≤ b.length := by
  rw [un_length, hb]
  exact Nat.pow_le_pow_right (by decide) i.isLt.le
 have hpow := powerTwo_eq b (un i.val) hcap
 have hsign := maskBits_gt M i
 dsimp only
 simp only [wedgeTerm, field_left_pair, field_right_pair, field_pack_succ, field_pack_zero]
 have hm : (if r then ix U else ix S) = ix M := by cases r <;> rfl
 rw [hm, hbits, hbit]
 by_cases hi : i ∈ M
 ·
  rw [if_pos hi]
  simp only [hi, decide_true, bflag, sel, List.cons_ne_nil, ↓reduceIte]
  have he : (ix M).drop (powerTwo b (un i.val)).length = ix (M.erase i) := by
   rw [hpow]
   simp [ix, un, List.drop_replicate, maskIndex_erase M hi]
  rw [he]
  have harg1 : (if r then ix S else ix (M.erase i)) = ix (if r then S else S.erase i) := by
   cases r <;> rfl
  have harg2 : (if r then ix (M.erase i) else ix U) = ix (if r then U.erase i else U) := by
   cases r <;> rfl
  rw [harg1,harg2]
  have hc := hT.2 (if r then S else S.erase i) (if r then U.erase i else U)
  have hv := rep_pow (rep_nat w (un v.val)) (un i.val)
  have hp := rep_mul hv hc
  have hr := parity_word_rep (u := q49 ((maskBits M).drop ((un i.val).length+1))) hp
  rw [un_length, hsign] at hr
  simpa [extVector, ← mul_assoc, un_length] using hr
 ·
  rw [if_neg hi]
  simpa [hi, bflag, sel] using rep_zero w
lemma sum_range_fin (d : ℕ) (z : Fin d → ℤ) :
  ((List.range d).map (fun i => if h : i<d then z ⟨i,h⟩ else 0)).sum = ∑ i, z i := by
 rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, ← Fin.sum_univ_eq_sum_range]
 apply Finset.sum_congr rfl
 intro i _
 simp [i.isLt]
lemma wedgeTable_rep {n d : ℕ} (r : Bool) (w b tab : List Bool) (v : Fin n)
  (T : extTable d) (hb : b.length = 2^d) (hT : tableRep w b tab T) :
  tableRep w b (wedgeTable r w (un d) b (un v.val) tab)
   (if r then extAppendRight (extVector v) T else extAppendLeft (extVector v) T) := by
 apply tableMake_rep _ _ _ _ _ hb
 ·
  intro s hs t ht
  simp [wedgeCell, field_left_pair, field_right_pair, field_pack_succ, field_pack_zero, sumRange_length]
 ·
  intro S U
  let M := if r then U else S
  let z : Fin d → ℤ := fun i => if i ∈ M then
   (-1 : ℤ)^((M.filter (fun j => i < j)).card) * extVector v i *
    T (if r then S else S.erase i) (if r then U.erase i else U) else 0
  have h := sumRange_rep (wedgeTerm r) w (un d)
   (pack [w,un d,b,un v.val,un (maskIndex S),un (maskIndex U),tab])
   (fun i => if hi : i<d then z ⟨i,hi⟩ else 0)
   (fun i hi => by
    rw [un_length] at hi
    simpa [hi, z, M] using wedgeTerm_rep r w b tab v T hb hT S U ⟨i,hi⟩)
  rw [un_length, sum_range_fin] at h
  have hz : (∑ i, z i) = (if r then extAppendRight (extVector v) T else extAppendLeft (extVector v) T) S U := by
   cases r <;> simp [z, M, extAppendRight, extAppendLeft, Finset.sum_filter]
  rw [hz] at h
  simpa only [wedgeCell, field_left_pair, field_right_pair, field_pack_zero, field_pack_succ] using h
end Packed
namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal
def header (n : ℕ) : List Bool := un n ++ [false]
def pairs (n : ℕ) : List (Edge n) := (List.finRange n).flatMap (fun i =>
 ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)))
def mask {n : ℕ} (E : Finset (Edge n)) : List Bool := (pairs n).map (fun e => decide (e ∈ E))
def rowBits {n : ℕ} (r : Row n) : List Bool := r.2 :: mask r.1
lemma mask_length {n : ℕ} (E : Finset (Edge n)) : (mask E).length = (pairs n).length := by simp [mask]
lemma pairs_mem {n : ℕ} (e : Edge n) : e ∈ pairs n ↔ e.1 < e.2 := by
 obtain ⟨a,b⟩ := e
 simp [pairs]
lemma pairs_nodup (n : ℕ) : (pairs n).Nodup := by
 rw [pairs,List.nodup_flatMap]
 refine ⟨fun i _=>((List.nodup_finRange n).filter _).map (fun a b h=>(Prod.mk.inj h).2),?_⟩
 refine (List.nodup_finRange n).imp (fun {a b} hab=>?_)
 intro x hx hy
 simp only [List.mem_map] at hx hy
 obtain ⟨_,_,rfl⟩:=hx
 obtain ⟨_,_,h⟩:=hy
 exact hab (Prod.mk.inj h).1.symm
def pairCell (f : List Bool → List Bool) (s : List Bool) : List Bool :=
 let j := left s
 let i := left (right s)
 let n := right (right s)
 sel (j.drop i.length) [] (f (pack [i,j,n]))
lemma cpPairCell {f : List Bool → List Bool} (hf : Lib.CPTs f) : Lib.CPTs (pairCell f) := by
 have hi := cpLeft (cpRight cpt_id)
 have hj := cpLeft cpt_id
 have hn := cpRight (cpRight cpt_id)
 apply cpt_sel (cpDrop hi hj) (cpt_const [])
 apply cpt_comp _ hf
 apply cpPack [fun s => left (right s), left, fun s => right (right s)]
 intro g hg
 simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
 rcases hg with rfl | rfl | rfl <;> assumption
def pairRow (f : List Bool → List Bool) (s : List Bool) : List Bool :=
 let i := left s
 let n := left (right s)
 let cap := right (right s)
 mapRange (pairCell f) cap n (pairB i n)
lemma cpPairRow {f : List Bool → List Bool} (hf : Lib.CPTs f) : Lib.CPTs (pairRow f) :=
 cpMapRange (cpPairCell hf) (cpRight (cpRight cpt_id)) (cpLeft (cpRight cpt_id))
  (cpt_pairB2 (cpLeft cpt_id) (cpLeft (cpRight cpt_id)))
def pairMap (f : List Bool → List Bool) (n cap : List Bool) : List Bool :=
 mapRange (pairRow f) (mulU n cap) n (pairB n cap)
lemma cpPairMap {f n cap : List Bool → List Bool} (hf : Lib.CPTs f) (hn : Lib.CPTs n)
  (hc : Lib.CPTs cap) : Lib.CPTs (fun s => pairMap f (n s) (cap s)) :=
 cpMapRange (cpPairRow hf) (q42 hn hc) hn (cpt_pairB2 hn hc)
lemma flatMap_filter_eq {α β : Type*} (L : List α) (p : α → Bool) (f : α → List β) :
  (L.filter p).flatMap f = L.flatMap (fun x => if p x then f x else []) := by
 induction L with
 | nil => rfl
 | cons a L ih => cases hp : p a <;> simp [hp, ih]
lemma flatMap_len_le {α : Type*} (L : List α) (f : α → List Bool) (cap : ℕ)
  (h : ∀ a ∈ L, (f a).length ≤ cap) : (L.flatMap f).length ≤ L.length * cap := by
 induction L with
 | nil => simp
 | cons a L ih =>
  simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (h a (by simp))
   (ih (fun b hb => h b (by simp [hb])))
lemma pairMap_eq (f : List Bool → List Bool) (n : ℕ) (cap : List Bool)
  (h : ∀ i < n, ∀ j < n, i < j → (f (pack [un i,un j,un n])).length ≤ cap.length) :
  pairMap f (un n) cap = (pairs n).flatMap (fun e => f (pack [un e.1.val, un e.2.val, un n])) := by
 let emit (i j : ℕ) := if i < j then f (pack [un i,un j,un n]) else []
 have hcell (i j : ℕ) : pairCell f (pairB (un j) (pairB (un i) (un n))) = emit i j := by
  by_cases hij : i < j
  ·
   simp [pairCell, emit, field_left_pair, field_right_pair, un, List.drop_replicate, sel, hij,
    Nat.sub_ne_zero_of_lt hij]
  ·
   simp [pairCell, emit, field_left_pair, field_right_pair, un, List.drop_replicate, sel, hij,
    Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hij)]
 have hrow (i : ℕ) (hi : i < n) : pairRow f (pairB (un i) (pairB (un n) cap)) =
   (List.range n).flatMap (emit i) := by
  simp only [pairRow, field_left_pair, field_right_pair]
  rw [mapRange_eq]
  · simp [hcell]
  ·
   intro j hj
   rw [hcell]
   rw [un_length] at hj
   by_cases hij : i < j
   · simpa [emit, hij] using h i hi j hj hij
   · simp [emit, hij]
 have bound (i : ℕ) (hi : i < n) : ((List.range n).flatMap (emit i)).length ≤ n * cap.length := by
  refine (flatMap_len_le _ _ cap.length fun j hj => ?_).trans (by rw [List.length_range])
  have hj' := List.mem_range.mp hj
  by_cases hij : i < j
  · simpa [emit, hij] using h i hi j hj' hij
  · simp [emit, hij]
 rw [pairMap, mapRange_eq]
 ·
  simp only [un_length]
  rw [show (List.range n).flatMap (fun i => pairRow f (pairB (un i) (pairB (un n) cap))) =
   (List.range n).flatMap (fun i => (List.range n).flatMap (emit i)) from
    List.flatMap_congr fun i hi => hrow i (List.mem_range.mp hi)]
  simp only [pairs, List.flatMap_assoc, List.flatMap_map, flatMap_filter_eq]
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  simp only [List.flatMap_map, Function.comp_apply, decide_eq_true_eq]
  rfl
 ·
  intro i hi
  rw [un_length] at hi
  rw [hrow i hi]
  simpa [mulU] using bound i hi
def pairCount (n : List Bool) : List Bool := pairMap (fun _ => [true]) n [true]
lemma cpPairCount {n : List Bool → List Bool} (hn : Lib.CPTs n) :
 Lib.CPTs (fun s => pairCount (n s)) := cpPairMap (cpt_const [true]) hn (cpt_const [true])
lemma pairCount_length (n : ℕ) : (pairCount (un n)).length = (pairs n).length := by
 rw [pairCount, pairMap_eq]
 · simpa using flatMap_len (pairs n) (fun _ => [true]) 1 (by simp)
 · simp
def endpointCode (n x : List Bool) : List Bool := (x ++ blank n).take n.length
lemma cpEndpointCode {n x : List Bool → List Bool} (hn : Lib.CPTs n) (hx : Lib.CPTs x) :
 Lib.CPTs (fun s => endpointCode (n s) (x s)) := cpTake hn (cpt_app2 hx (cpt_comp hn cpt_blank))
lemma endpointCode_length (n x : List Bool) : (endpointCode n x).length = n.length := by
 simp [endpointCode, q33]
def pairCode (s : List Bool) : List Bool :=
 endpointCode (field 2 s) (field 0 s) ++ endpointCode (field 2 s) (field 1 s)
lemma cpPairCode : Lib.CPTs pairCode :=
 cpt_app2 (cpEndpointCode (cpField 2 cpt_id) (cpField 0 cpt_id))
  (cpEndpointCode (cpField 2 cpt_id) (cpField 1 cpt_id))
def pairWords (n : List Bool) : List Bool := pairMap pairCode n (n ++ n)
lemma cpPairWords {n : List Bool → List Bool} (hn : Lib.CPTs n) :
 Lib.CPTs (fun s => pairWords (n s)) := cpPairMap cpPairCode hn (cpt_app2 hn hn)
lemma pairWords_eq (n : ℕ) : pairWords (un n) = (pairs n).flatMap (fun e =>
  endpointCode (un n) (un e.1.val) ++ endpointCode (un n) (un e.2.val)) := by
 rw [pairWords, pairMap_eq]
 · simp [pairCode, field_pack_zero, field_pack_succ]
 · simp [pairCode, endpointCode_length, field_pack_zero, field_pack_succ]
lemma hd_un_false (i : ℕ) (x : List Bool) : hd (un i ++ false :: x) = un i := by simp [hd, un]
lemma dropN_un_false (i : ℕ) (x : List Bool) : dropN (un i ++ false :: x) = x := by
 have h : (un i ++ false :: x).dropWhile id = false :: x := by simp [un]
 simp [dropN, h]
lemma hd_endpointCode (n i : ℕ) (hi : i ≤ n) : hd (endpointCode (un n) (un i)) = un i := by
 unfold endpointCode
 rw [un_length, List.take_append, List.take_of_length_le (by simpa using hi)]
 have h : (blank (un n)).take (n-i) = List.replicate (n-i) false := by
  simp [blank, un, Nat.sub_le]
 rw [un_length, h]
 cases e : n-i with
 | zero => simp [hd, un]
 | succ k => exact hd_un_false i _
lemma pairWords_get (n i : ℕ) (hi : i < (pairs n).length) :
  let word := slot (un n ++ un n) (un i) (pairWords (un n))
  let e := (pairs n)[i]
  hd (word.take n) = un e.1.val ∧ hd (word.drop n) = un e.2.val := by
 rw [pairWords_eq, slot_flatMap _ _ _ _ hi]
 ·
  dsimp only
  have hfirst := endpointCode_length (un n) (un (pairs n)[i].1.val)
  rw [un_length] at hfirst
  let l := endpointCode (un n) (un (pairs n)[i].1.val)
  let r := endpointCode (un n) (un (pairs n)[i].2.val)
  have ht : (l ++ r).take n = l :=
   (congrArg (fun p => (l ++ r).take p) hfirst.symm).trans List.take_left
  have hd' : (l ++ r).drop n = r :=
   (congrArg (fun p => (l ++ r).drop p) hfirst.symm).trans List.drop_append_length
  rw [ht, hd']
  exact ⟨hd_endpointCode _ _ (pairs n)[i].1.isLt.le, hd_endpointCode _ _ (pairs n)[i].2.isLt.le⟩
 · simp [endpointCode_length]
end Packed
namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal
def plusCell (s : List Bool) : List Bool :=
 let a := right (right s)
 let w := field 0 a
 let b := field 1 a
 let i := left s
 let j := left (right s)
 addW w (tableAt w b i j (field 2 a)) (tableAt w b i j (field 3 a))
lemma cpPlusCell : Lib.CPTs plusCell := by
 have ha := cpRight (cpRight cpt_id)
 have hw := cpField 0 ha
 have hb := cpField 1 ha
 have hi := cpLeft cpt_id
 have hj := cpLeft (cpRight cpt_id)
 exact q82 hw (cpTableAt hw hb hi hj (cpField 2 ha)) (cpTableAt hw hb hi hj (cpField 3 ha))
def tablePlus (w b x y : List Bool) : List Bool := tableMake plusCell w b (pack [w,b,x,y])
lemma cpTablePlus {w b x y : List Bool → List Bool} (hw : Lib.CPTs w) (hb : Lib.CPTs b)
  (hx : Lib.CPTs x) (hy : Lib.CPTs y) : Lib.CPTs (fun s => tablePlus (w s) (b s) (x s) (y s)) := by
 apply cpTableMake cpPlusCell hw hb
 apply cpPack [w,b,x,y]
 intro f hf
 simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
 rcases hf with rfl | rfl | rfl | rfl <;> assumption
lemma tablePlus_rep {d : ℕ} (w b x y : List Bool) {A B : extTable d} (hb : b.length = 2^d)
  (ha : tableRep w b x A) (hB : tableRep w b y B) : tableRep w b (tablePlus w b x y) (A + B) := by
 apply tableMake_rep _ _ _ _ _ hb
 ·
  intro i hi j hj
  simp [plusCell, field_left_pair, field_right_pair, field_pack_zero, field_pack_succ, q36]
 ·
  intro S T
  simpa only [plusCell, field_left_pair, field_right_pair, field_pack_zero, field_pack_succ, Pi.add_apply]
   using rep_add (ha.2 S T) (hB.2 S T)
def takeTable (w d b u v tab : List Bool) : List Bool :=
 wedgeTable true w d b v (wedgeTable true w d b u (wedgeTable false w d b v (wedgeTable false w d b u tab)))
lemma cpTakeTable {w d b u v tab : List Bool → List Bool} (hw : Lib.CPTs w) (hd : Lib.CPTs d)
  (hb : Lib.CPTs b) (hu : Lib.CPTs u) (hv : Lib.CPTs v) (htab : Lib.CPTs tab) :
  Lib.CPTs (fun s => takeTable (w s) (d s) (b s) (u s) (v s) (tab s)) :=
 cpWedgeTable true hw hd hb hv (cpWedgeTable true hw hd hb hu
  (cpWedgeTable false hw hd hb hv (cpWedgeTable false hw hd hb hu htab)))
lemma takeTable_rep {n d : ℕ} (w b tab : List Bool) (e : Edge n) (D : extTable d)
  (hb : b.length = 2^d) (hD : tableRep w b tab D) :
  tableRep w b (takeTable w (un d) b (un e.1.val) (un e.2.val) tab) (extTake e D) :=
 wedgeTable_rep true _ _ _ e.2 _ hb (wedgeTable_rep true _ _ _ e.1 _ hb
  (wedgeTable_rep false _ _ _ e.2 _ hb (wedgeTable_rep false _ _ _ e.1 _ hb hD)))
def edgeUpdate (s : List Bool) : List Bool :=
 let i := left s
 let a := left (right s)
 let tab := right (right s)
 let w := field 0 a
 let d := field 1 a
 let b := field 2 a
 let n := field 3 a
 let E := field 4 a
 let A := field 5 a
 let B := field 6 a
 let edges := field 7 a
 let keep := sel (bitFlagAt i E) [] (sel (bitFlagAt i A) [] (bitFlagAt i B))
 let e := slot (n ++ n) i edges
 let u := hd (e.take n.length)
 let v := hd (e.drop n.length)
 sel keep tab (tablePlus w b tab (takeTable w d b u v tab))
lemma cpEdgeUpdate : Lib.CPTs edgeUpdate := by
 have hi := cpLeft cpt_id
 have ha := cpLeft (cpRight cpt_id)
 have ht := cpRight (cpRight cpt_id)
 have hw := cpField 0 ha
 have hd' := cpField 1 ha
 have hb := cpField 2 ha
 have hn := cpField 3 ha
 have hE := cpBitFlagAt hi (cpField 4 ha)
 have hA := cpBitFlagAt hi (cpField 5 ha)
 have hB := cpBitFlagAt hi (cpField 6 ha)
 have he := cpSlot (cpt_app2 hn hn) hi (cpField 7 ha)
 have hu := cpt_comp (cpTake hn he) cpt_hd
 have hv := cpt_comp (cpDrop hn he) cpt_hd
 exact cpt_sel (cpt_sel hE (cpt_const []) (cpt_sel hA (cpt_const []) hB)) ht
  (cpTablePlus hw hb ht (cpTakeTable hw hd' hb hu hv ht))
def edgeRun (w d b n E A B edges p : List Bool) : List Bool :=
 runIndexed replaceBound edgeUpdate (mulU b (mulU b w)) p (pack [w,d,b,n,E,A,B,edges]) (tableInit w b)
lemma cpEdgeRun {w d b n E A B edges p : List Bool → List Bool} (hw : Lib.CPTs w) (hd' : Lib.CPTs d)
  (hb : Lib.CPTs b) (hn : Lib.CPTs n) (hE : Lib.CPTs E) (hA : Lib.CPTs A) (hB : Lib.CPTs B)
  (hedges : Lib.CPTs edges) (hp : Lib.CPTs p) : Lib.CPTs (fun s =>
   edgeRun (w s) (d s) (b s) (n s) (E s) (A s) (B s) (edges s) (p s)) := by
 apply cpRunIndexed replaceBound_cpt replaceBound_length cpEdgeUpdate (q42 hb (q42 hb hw)) hp _
  (cpTableInit hw hb)
 apply cpPack [w,d,b,n,E,A,B,edges]
 intro f hf
 simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
 rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
lemma foldr_range_get {α β : Type*} (L : List α) (f : α → β → β) (z : β) :
  (List.range L.length).foldr (fun i a => if hi : i < L.length then f L[i] a else a) z = L.foldr f z := by
 induction L with
 | nil => rfl
 | cons x L ih =>
  simp only [List.length_cons, List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
  rw [dif_pos (Nat.zero_lt_succ _), List.getElem_cons_zero]
  congr 1
  rw [← ih]
  congr 1
  funext i a
  by_cases hi : i < L.length
  · simp [hi, Nat.succ_lt_succ hi]
  ·
   have hni : ¬ i.succ < L.length.succ := fun h => hi (Nat.lt_of_succ_lt_succ h)
   simp [hi, hni]
lemma foldr_filter_apply {α β : Type*} (L : List α) (p : α → Bool) (f : α → β → β) (z : β) :
  L.foldr (fun i a => if p i then f i a else a) z = (L.filter p).foldr f z := by
 induction L with
 | nil => rfl
 | cons x L ih => cases hp : p x <;> simp [hp, ih]
lemma mask_bit {n : ℕ} (A : Finset (Edge n)) (i : ℕ) (hi : i < (pairs n).length) :
  bitFlagAt (un i) (mask A) = bflag (decide ((pairs n)[i] ∈ A)) := by
 rw [bitFlagAt_eq, un_length, List.getD_eq_getElem _ _ (by simpa [mask_length] using hi)]
 simp [mask]
lemma edgeRun_rep {n d : ℕ} (w b p : List Bool) (E A B : Finset (Edge n))
  (hb : b.length = 2^d) (hp : p.length = (pairs n).length) :
  tableRep w b (edgeRun w (un d) b (un n) (mask E) (mask A) (mask B) (pairWords (un n)) p)
   (extRun d ((pairs n).filter (fun e => decide (e ∈ E ∩ A ∩ B)))) := by
 let step (i : ℕ) (D : extTable d) := if hi : i < (pairs n).length then
  (if (pairs n)[i] ∈ E ∩ A ∩ B then extStep (pairs n)[i] D else D) else D
 have hfold : (List.range p.length).foldr step (extInit d) =
   extRun d ((pairs n).filter (fun e => decide (e ∈ E ∩ A ∩ B))) := by
  rw [hp]
  unfold step extRun
  exact (foldr_range_get (pairs n) (fun e D => if e ∈ E ∩ A ∩ B then extStep e D else D)
   (extInit d)).trans (by
    simpa using foldr_filter_apply (pairs n) (fun e => decide (e ∈ E ∩ A ∩ B)) extStep (extInit d))
 rw [← hfold]
 unfold edgeRun
 apply runIndexed_ofListFold _ _ _ _ _ _ (tableRep w b) step _ (tableInit_rep w b hb)
 intro i hi tab D hD
 have hix : i < (pairs n).length := hp ▸ hi
 have he := pairWords_get n i hix
 let e := (pairs n)[i]
 have hkeep : sel (bitFlagAt (un i) (mask E)) []
   (sel (bitFlagAt (un i) (mask A)) [] (bitFlagAt (un i) (mask B))) = bflag (decide (e ∈ E ∩ A ∩ B)) := by
  rw [mask_bit E i hix, mask_bit A i hix, mask_bit B i hix]
  change sel (bflag (decide (e ∈ E))) [] (sel (bflag (decide (e ∈ A))) [] (bflag (decide (e ∈ B)))) = _
  by_cases hE : e ∈ E <;> by_cases hA : e ∈ A <;> by_cases hB : e ∈ B <;>
   simp [sel, bflag, hE, hA, hB]
 simp only [edgeUpdate, field_left_pair, field_right_pair, field_pack_zero, field_pack_succ, un_length,
  step, dif_pos hix, hkeep]
 rw [he.1,he.2]
 by_cases he' : (pairs n)[i] ∈ E ∩ A ∩ B
 ·
  rw [if_pos he']
  simp only [show e ∈ E ∩ A ∩ B from he', decide_true, bflag, sel, List.cons_ne_nil, ↓reduceIte]
  have hs : tableRep w b (tablePlus w b tab (takeTable w (un d) b (un e.1.val) (un e.2.val) tab))
    (extStep e D) := tablePlus_rep w b _ _ hb hD (takeTable_rep w b tab e D hb hD)
  have hh : (tablePlus w b tab (takeTable w (un d) b (un e.1.val) (un e.2.val) tab)).length ≤
    (mulU b (mulU b w)).length := by rw [hs.1]; simp [mulU]
  change tableRep w b ((tablePlus w b tab (takeTable w (un d) b (un e.1.val) (un e.2.val) tab)).take
   (mulU b (mulU b w)).length) (extStep e D)
  rwa [List.take_of_length_le hh]
 ·
  rw [if_neg he']
  simp only [show ¬ e ∈ E ∩ A ∩ B from he', decide_false, bflag, Bool.false_eq_true, sel, ↓reduceIte]
  have hh : tab.length ≤ (mulU b (mulU b w)).length := by rw [hD.1]; simp [mulU]
  change tableRep w b (tab.take (mulU b (mulU b w)).length) D
  rwa [List.take_of_length_le hh]
set_option maxHeartbeats 1000000 in
lemma common_top {n k : ℕ} (E A B : Finset (Edge n)) (hE : ∀ e ∈ E, e.1 < e.2) :
  extRun (2*k) ((pairs n).filter (fun e => decide (e ∈ E ∩ A ∩ B))) Finset.univ Finset.univ =
   (choices (E ∩ A ∩ B) k).sum (fun Q => (weight Q : ℤ)) := by
 let L := (pairs n).filter (fun e => decide (e ∈ E ∩ A ∩ B))
 have hsub : ∀ e ∈ E ∩ A ∩ B, e.1 < e.2 := by
  intro e he
  exact hE e (Finset.mem_inter.mp (Finset.mem_inter.mp he).1).1
 have hL : L.toFinset = E ∩ A ∩ B := by
  ext e
  constructor
  ·
   intro he
   exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp he)).2
  ·
   intro he
   exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨(pairs_mem e).mpr (hsub e he), decide_eq_true he⟩)
 classical
 have h := extRun_matching_of_toFinset k _ _ ((pairs_nodup n).filter _) hL hsub
 have hc : (E ∩ A ∩ B).powerset.filter (fun Q => Q.card = k ∧ extMatching Q) =
   choices (E ∩ A ∩ B) k := by
  ext Q
  simp only [choices, Finset.mem_filter]
  rfl
 rw [hc] at h
 exact h.trans (Finset.sum_congr rfl fun _ _ => rfl)
end Packed
namespace Packed
open PEqualNP.Library Lib.Machines Lib.Universal
def rowAt (p i data : List Bool) : List Bool := slot (true :: p) i data
lemma cpRowAt {p i data : List Bool → List Bool} (hp : Lib.CPTs p) (hi : Lib.CPTs i)
 (hd : Lib.CPTs data) : Lib.CPTs (fun x => rowAt (p x) (i x) (data x)) := cpSlot (cpCons true hp) hi hd
lemma rowAt_eq {n : ℕ} (p : List Bool) (rows : List (Row n)) (hp : p.length = (pairs n).length)
  (i : ℕ) (hi : i < rows.length) : rowAt p (un i) (rows.flatMap rowBits) = rowBits rows[i] := by
 apply slot_flatMap _ _ _ _ hi
 intro r _
 simp [rowBits, mask_length, hp]
def commonWord (w d b n E A B edges p : List Bool) : List Bool :=
 tableAt w b b.tail b.tail (edgeRun w d b n E A B edges p)
lemma cpCommonWord {w d b n E A B edges p : List Bool → List Bool} (hw : Lib.CPTs w) (hd : Lib.CPTs d)
  (hb : Lib.CPTs b) (hn : Lib.CPTs n) (hE : Lib.CPTs E) (hA : Lib.CPTs A) (hB : Lib.CPTs B)
  (hedges : Lib.CPTs edges) (hp : Lib.CPTs p) : Lib.CPTs (fun s =>
   commonWord (w s) (d s) (b s) (n s) (E s) (A s) (B s) (edges s) (p s)) :=
 cpTableAt hw hb (cpTail hb) (cpTail hb) (cpEdgeRun hw hd hb hn hE hA hB hedges hp)
lemma commonWord_rep {n k : ℕ} (w p : List Bool) (E A B : Finset (Edge n))
  (hE : ∀ e ∈ E, e.1 < e.2) (hp : p.length = (pairs n).length) :
  rep w (commonWord w (un (2*k)) (un (2^(2*k))) (un n) (mask E) (mask A) (mask B) (pairWords (un n)) p)
   ((choices (E ∩ A ∩ B) k).sum (fun Q => (weight Q : ℤ))) := by
 have h := (edgeRun_rep w (un (2^(2*k))) p E A B (by simp : (un (2^(2*k))).length = 2^(2*k)) hp).2
  Finset.univ Finset.univ
 rw [common_top E A B hE] at h
 simpa only [commonWord, maskIndex_univ, un, List.tail_replicate] using h
def rowPair (s : List Bool) : List Bool :=
 let i := left s
 let A := left (right s)
 let a := right (right s)
 let w := field 0 a
 let p := field 4 a
 let B := rowAt p i (field 8 a)
 signedWord w (xorF (q17 A) (q17 B))
  (commonWord w (field 1 a) (field 2 a) (field 3 a) (field 6 a) A.tail B.tail (field 7 a) p)
lemma cpRowPair : Lib.CPTs rowPair := by
 have ha := cpRight (cpRight cpt_id)
 have hA := cpLeft (cpRight cpt_id)
 have hp := cpField 4 ha
 have hw := cpField 0 ha
 have hB := cpRowAt hp (cpLeft cpt_id) (cpField 8 ha)
 exact cpSignedWord hw (q200 (cpt_comp hA q35) (cpt_comp hB q35))
  (cpCommonWord hw (cpField 1 ha) (cpField 2 ha) (cpField 3 ha) (cpField 6 ha) (cpTail hA)
   (cpTail hB) (cpField 7 ha) hp)
def rowSum (s : List Bool) : List Bool :=
 let a := right s
 let row := rowAt (field 4 a) (left s) (field 8 a)
 sumRange rowPair (field 0 a) (field 5 a) (pairB row a)
lemma cpRowSum : Lib.CPTs rowSum := by
 have ha := cpRight cpt_id
 exact cpSumRange cpRowPair (cpField 0 ha) (cpField 5 ha)
  (cpt_pairB2 (cpRowAt (cpField 4 ha) (cpLeft cpt_id) (cpField 8 ha)) ha)
def aggregate (a : List Bool) : List Bool := sumRange rowSum (field 0 a) (field 5 a) a
lemma cpAggregate : Lib.CPTs aggregate := cpSumRange cpRowSum (cpField 0 cpt_id) (cpField 5 cpt_id) cpt_id
def validArgs {n k : ℕ} (w : List Bool) (E : Finset (Edge n)) (rows : List (Row n)) : List Bool :=
 pack [w, un (2*k), un (2^(2*k)), un n, pairCount (un n), un rows.length, mask E, pairWords (un n), rows.flatMap rowBits]
lemma rowPair_rep {n k : ℕ} (w : List Bool) (E : Finset (Edge n)) (rows : List (Row n))
  (hE : ∀ e ∈ E, e.1 < e.2) (A : Row n) (j : ℕ) (hj : j < rows.length) :
  rep w (rowPair (pairB (un j) (pairB (rowBits A) (validArgs (k := k) w E rows))))
   (sign A.2 * sign rows[j].2 * (choices (E ∩ A.1 ∩ rows[j].1) k).sum (fun Q => (weight Q : ℤ))) := by
 simp only [rowPair, field_left_pair, field_right_pair, validArgs, field_pack_zero, field_pack_succ]
 rw [rowAt_eq _ rows (pairCount_length n) j hj]
 have h := commonWord_rep (k := k) w (pairCount (un n)) E A.1 rows[j].1 hE (pairCount_length n)
 cases hA : A.2 <;> cases hB : rows[j].2
 · simpa [rowBits, hA, hB, q17, xorF, sel, signedWord, sign, Finset.inter_assoc] using h
 · simpa [rowBits, hA, hB, q17, xorF, sel, signedWord, sign, Finset.inter_assoc] using rep_neg h
 · simpa [rowBits, hA, hB, q17, xorF, sel, signedWord, sign, Finset.inter_assoc] using rep_neg h
 · simpa [rowBits, hA, hB, q17, xorF, sel, signedWord, sign, Finset.inter_assoc] using h
lemma sum_range_list_get {α : Type*} (L : List α) (f : α → ℤ) :
  ((List.range L.length).map (fun i => if hi : i<L.length then f L[i] else 0)).sum = (L.map f).sum := by
 induction L with
 | nil => rfl
 | cons a l ih =>
  simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  rw [dif_pos (Nat.zero_lt_succ _), List.getElem_cons_zero, ← ih]
  congr 2
  apply List.map_congr_left
  intro i _
  by_cases hi : i < l.length
  · simp [hi, Nat.succ_lt_succ hi]
  ·
   have hn : ¬ i.succ < l.length.succ := fun h => hi (Nat.lt_of_succ_lt_succ h)
   simp [hi, hn]
lemma rowSum_rep {n k : ℕ} (w : List Bool) (E : Finset (Edge n)) (rows : List (Row n))
  (hE : ∀ e ∈ E, e.1 < e.2) (i : ℕ) (hi : i < rows.length) :
  rep w (rowSum (pairB (un i) (validArgs (k := k) w E rows)))
   ((rows.map (fun r => sign rows[i].2 * sign r.2 *
    (choices (E ∩ rows[i].1 ∩ r.1) k).sum (fun Q => (weight Q : ℤ)))).sum) := by
 simp only [rowSum, field_left_pair, field_right_pair, validArgs, field_pack_zero, field_pack_succ]
 rw [rowAt_eq _ rows (pairCount_length n) i hi]
 let f (r : Row n) : ℤ := sign rows[i].2 * sign r.2 *
   (choices (E ∩ rows[i].1 ∩ r.1) k).sum (fun Q => (weight Q : ℤ))
 have hs := sumRange_rep rowPair w (un rows.length) (pairB (rowBits rows[i]) (validArgs (k := k) w E rows))
  (fun j => if hj : j < rows.length then f rows[j] else 0) (fun j hj => by
   rw [un_length] at hj
   simpa [hj, f] using rowPair_rep (k := k) w E rows hE rows[i] j hj)
 rw [un_length, sum_range_list_get] at hs
 exact hs
lemma aggregate_rep {n k : ℕ} (w : List Bool) (E : Finset (Edge n)) (rows : List (Row n))
  (hE : ∀ e ∈ E, e.1 < e.2) : rep w (aggregate (validArgs (k := k) w E rows)) (total E k rows : ℤ) := by
 simp only [aggregate, validArgs, field_pack_zero, field_pack_succ]
 let f (r : Row n) : ℤ := (rows.map (fun s => sign r.2 * sign s.2 *
    (choices (E ∩ r.1 ∩ s.1) k).sum (fun Q => (weight Q : ℤ)))).sum
 have hs := sumRange_rep rowSum w (un rows.length) (validArgs (k := k) w E rows)
  (fun j => if hj : j < rows.length then f rows[j] else 0) (fun j hj => by
   rw [un_length] at hj
   simpa [hj, f] using rowSum_rep (k := k) w E rows hE j hj)
 rw [un_length, sum_range_list_get] at hs
 rw [total_eq_row_pairs (k := k) E rows]
 exact hs
def widthCode (n m : List Bool) : List Bool :=
 let a := mulU n n
 a ++ mulU (n ++ n) a ++ m ++ m ++ [true]
lemma cpWidthCode {n m : List Bool → List Bool} (hn : Lib.CPTs n) (hm : Lib.CPTs m) :
  Lib.CPTs (fun s => widthCode (n s) (m s)) := by
 let ha := q42 hn hn
 exact cpt_app2 (cpt_app2 (cpt_app2 (cpt_app2 ha (q42 (cpt_app2 hn hn) ha)) hm) hm) (cpt_const [true])
lemma widthCode_length (n m : ℕ) : (widthCode (un n) (un m)).length = width n m := by
 simp [widthCode, width, mulU, two_mul, Nat.add_assoc, Nat.mul_assoc]
end Packed
end TM

namespace Math
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def nr (k : ℕ) (crown : Bool) : ℕ := if crown then k + 2 else k
def nc (k : ℕ) (crown : Bool) : ℕ := if crown then k + 1 else k
def adjA (k : ℕ) (crown : Bool) (i : Fin (nr k crown)) (j : Fin (nc k crown)) : Bool :=
 if crown then decide (i.val ≠ k + 1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
abbrev Fn (k : ℕ) (crown : Bool) := (Fin (nr k crown) → Bool) → (Fin (nc k crown) → Bool) → Bool
def eligible (k : ℕ) (crown : Bool) (f : Fn k crown) : Prop :=
 ∃ C : Circuit,
  (if crown then FanInTwo C ∧ C.size ≤ 2 * k + 1 else Monotone2 C ∧ C.size + 1 ≤ 2 * k) ∧
  Represents (adjA k crown) C ∧ ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
def fits (k : ℕ) (crown : Bool) (hard : List ((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)))
  (f : Fn k crown) : Prop :=
 eligible k crown f ∧ ∀ h ∈ hard, f h.1 h.2 = crown
def score (k : ℕ) (crown : Bool)
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool))
  (f : Fn k crown) : ℕ :=
 (soft.filter (fun t => decide (f t.1.1 t.1.2 = t.2))).length
def probe (k : ℕ) (crown : Bool) (f : Fn k crown) : Finset (Fin k × Fin k) :=
 (TM.Packed.pairs k).toFinset.filter (fun e =>
  f (fun i => decide (i.val = e.1.val ∨ i.val = e.2.val)) (fun _ => false) = !crown)
def low (k d : ℕ) (crown : Bool)
  (hard : List ((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)))
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool)) : Prop :=
 ∃ a : Finset (Fin k × Fin k) → ℤ, ∀ f : Fn k crown, fits k crown hard f →
  (score k crown soft f : ℤ) = ((probe k crown f).powerset.filter (fun T => T.card ≤ d)).sum a
def realizes (k d : ℕ) (crown : Bool)
  (hard : List ((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)))
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool))
  (Q : Finset (Fin k × Fin k)) (value : ℤ) : Prop :=
 d < Q.card ∧ (∀ e ∈ Q, e.1 < e.2) ∧
 (∀ e ∈ Q, ∀ z ∈ Q, e ≠ z → Disjoint (TM.ends e) (TM.ends z)) ∧
 ∃ cube : Finset (Fin k × Fin k) → Fn k crown,
  (∀ T ⊆ Q, fits k crown hard (cube T) ∧ probe k crown (cube T) = T) ∧
  Q.powerset.sum (fun T => (-1 : ℤ) ^ (Q.card - T.card) * (score k crown soft (cube T) : ℤ)) = value
def wire {nr nc : ℕ} (z : (Fin nr → Bool) × (Fin nc → Bool)) (i : ℕ) : Bool :=
 (List.ofFn z.1 ++ List.ofFn z.2).getD i false
def baseHit (k : ℕ) (crown : Bool)
  (z : (Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) : Bool :=
 decide ((crown = true ∧ wire z (k + 1) = true) ∨
  ∃ v : Fin k, wire z v.val = true ∧ wire z (nr k crown + v.val) = true)
def support (k : ℕ) (crown : Bool)
  (z : (Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) : Finset (Fin k × Fin k) :=
 (TM.Packed.pairs k).toFinset.filter (fun e =>
  (wire z e.1.val && wire z e.2.val) || (wire z (nr k crown + e.1.val) && wire z (nr k crown + e.2.val)))
def hardBad (k : ℕ) (crown : Bool)
  (hard : List ((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool))) : Bool :=
 hard.any (baseHit k crown)
def allowedEdges (k : ℕ) (crown : Bool)
  (hard : List ((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool))) : Finset (Fin k × Fin k) :=
 (TM.Packed.pairs k).toFinset.filter (fun e => hard.all (fun h => !decide (e ∈ support k crown h)))
def unforcedRows (k : ℕ) (crown : Bool)
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool)) : List (TM.Row k) :=
 (soft.filter (fun t => !baseHit k crown t.1)).map (fun t => (support k crown t.1, t.2 == crown))
def paddedRows (k : ℕ) (crown : Bool)
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool)) : List (TM.Row k) :=
 soft.map (fun t => if baseHit k crown t.1 then (∅, false) else (support k crown t.1, t.2 == crown))
lemma paddedRows_length (k : ℕ) (crown : Bool)
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool)) :
  (paddedRows k crown soft).length = soft.length := by
 simp [paddedRows]
lemma signed_padded_eq (k : ℕ) (crown : Bool)
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool))
  {Q : Finset (Fin k × Fin k)} (hQ : Q.Nonempty) :
  TM.signed (paddedRows k crown soft) Q = TM.signed (unforcedRows k crown soft) Q := by
 rw [TM.signed_eq_sum, TM.signed_eq_sum]
 unfold paddedRows unforcedRows
 induction soft with
 | nil => rfl
 | cons t ts ih =>
  simp only [List.map_cons, List.filter_cons]
  cases hb : baseHit k crown t.1
  ·
   simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, List.map_cons, List.sum_cons]
   rw [ih]
  ·
   simp only [hb, ↓reduceIte, Bool.not_true, List.map_cons, List.sum_cons]
   have hn : ¬ Q ⊆ ∅ := fun h => by
    obtain ⟨e, he⟩ := hQ
    exact Finset.notMem_empty e (h he)
   simp only [TM.rowContribution, hn, if_false, zero_add]
   simp only [paddedRows, unforcedRows, List.map_map] at ih ⊢
   exact ih
lemma isM_of_disjoint {k : ℕ} {Q : Finset (Fin k × Fin k)}
  (hord : ∀ e ∈ Q, e.1 < e.2) (hdis : TM.disjointEdges Q) :
  Obs.IsM (Q.image Obs.ends) := by
 refine ⟨?_, ?_⟩
 ·
  intro s hs
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
  have hne : e.1 ≠ e.2 := ne_of_lt (hord e he)
  simp [Obs.ends, hne]
 ·
  intro s hs t ht hne
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ht
  have hef : e ≠ f := fun h => hne (congrArg Obs.ends h)
  exact hdis e he f hf hef
lemma mem_image_ends {k : ℕ} {Q : Finset (Fin k × Fin k)}
  (hord : ∀ e ∈ Q, e.1 < e.2) (e : Fin k × Fin k) (he : e.1 < e.2) :
  Obs.ends e ∈ Q.image Obs.ends ↔ e ∈ Q := by
 constructor
 ·
  intro h
  obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp h
  have := Obs.ends_injective f e (hord f hf) he hfe
  rwa [← this]
 · exact Finset.mem_image_of_mem Obs.ends
lemma active_iff_hit {k : ℕ} {crown : Bool} {Q : Finset (Fin k × Fin k)}
  (hQ : Q ⊆ (TM.Packed.pairs k).toFinset)
  (z : (Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) :
  ((crown = true ∧ wire z (k + 1) = true) ∨ Obs.active (Q.image Obs.ends) z.1 z.2) ↔
   (baseHit k crown z = true ∨ ¬ Disjoint Q (support k crown z)) := by
 simp only [baseHit, decide_eq_true_eq, Obs.active, Obs.Pr, Finset.mem_univ, true_and,
  Finset.disjoint_left, not_forall, not_not]
 have hmatch : (∃ x ∈ Q.image Obs.ends,
   (∀ u ∈ x, wire z u.val = true) ∨
   (∀ u ∈ x, wire z (nr k crown + u.val) = true)) ↔
   ∃ e ∈ Q, e ∈ support k crown z := by
  simp only [Finset.mem_image]
  constructor
  ·
   rintro ⟨s, ⟨e, he, rfl⟩, hside⟩
   refine ⟨e, he, Finset.mem_filter.mpr ⟨hQ he, ?_⟩⟩
   rcases hside with hl | hr
   ·
    simp [Obs.ends, hl e.1 (Finset.mem_insert_self _ _),
     hl e.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
   ·
    simp [Obs.ends, hr e.1 (Finset.mem_insert_self _ _),
     hr e.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
  ·
   rintro ⟨e, he, hsup⟩
   have hcond := (Finset.mem_filter.mp hsup).2
   refine ⟨Obs.ends e, ⟨e, he, rfl⟩, ?_⟩
   simp only [Bool.or_eq_true, Bool.and_eq_true] at hcond
   rcases hcond with ⟨h1, h2⟩ | ⟨h1, h2⟩
   ·
    left; intro v hv
    simp only [Obs.ends, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
   ·
    right; intro v hv
    simp only [Obs.ends, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
 change ((crown = true ∧ wire z (k + 1) = true) ∨
  (∃ v : Fin k, wire z v.val = true ∧ wire z (nr k crown + v.val) = true) ∨
  (∃ x ∈ Q.image Obs.ends, (∀ u ∈ x, wire z u.val = true) ∨ (∀ u ∈ x, wire z (nr k crown + u.val) = true))) ↔ _
 rw [hmatch]
 simp only [exists_prop, or_assoc, iff_self]
lemma classify_obs {k : ℕ} {crown : Bool} (hk2 : 2 ≤ k) (hk7 : crown = true → 7 ≤ k)
  {f : Fn k crown} (hf : eligible k crown f) :
  ∃ Q : Finset (Fin k × Fin k), Q ⊆ (TM.Packed.pairs k).toFinset ∧ TM.disjointEdges Q ∧
   probe k crown f = Q ∧
   ∀ z, f z.1 z.2 = !crown ↔ baseHit k crown z = true ∨ ¬ Disjoint Q (support k crown z) := by
 cases crown
 ·
  obtain ⟨C, hC, hR, heval⟩ := hf
  obtain ⟨M, hM, h⟩ := Obs.classify_false k hk2 C hC.1 hC.2 (by
   intro u v; simpa [nr, nc, adjA] using hR u v)
  have hMlaw : ∀ (x : Fin (nr k false) → Bool) (y : Fin (nc k false) → Bool),
    C.eval (List.ofFn x ++ List.ofFn y) = !false ↔
     (false = true ∧ (List.ofFn x ++ List.ofFn y).getD (k + 1) false = true) ∨ Obs.active M x y := by
   intro x y
   simp only [Bool.not_false, Bool.false_eq_true, false_and, false_or, Obs.active]
   exact h x y
  let Q : Finset (Fin k × Fin k) := (TM.Packed.pairs k).toFinset.filter (fun e => Obs.ends e ∈ M)
  have hQsub : Q ⊆ (TM.Packed.pairs k).toFinset := Finset.filter_subset _ _
  have hQord : ∀ e ∈ Q, e.1 < e.2 := fun e he => (TM.Packed.pairs_mem e).mp (List.mem_toFinset.mp (hQsub he))
  have hQdis : TM.disjointEdges Q := by
   intro e he f' hf' hne
   exact hM.2 _ (Finset.mem_filter.mp he).2 _ (Finset.mem_filter.mp hf').2
    (fun eq => hne (Obs.ends_injective e f' (hQord e he) (hQord f' hf') eq))
  have hQimg : Q.image Obs.ends = M := by
   ext s; constructor
   · intro hs; obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs; exact (Finset.mem_filter.mp he).2
   ·
    intro hs; obtain ⟨e, hlt, rfl⟩ := Obs.min_key_sorted s (hM.1 s hs)
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ((TM.Packed.pairs_mem e).mpr hlt), hs⟩)
  have hflaw : ∀ x y, f x y = !false ↔
    (false = true ∧ (List.ofFn x ++ List.ofFn y).getD (k + 1) false = true) ∨ Obs.active M x y := by
   intro x y; rw [heval x y]; exact hMlaw x y
  have hprobe : probe k false f = Q := by
   ext e; simp only [probe, Q, Finset.mem_filter]; constructor
   ·
    rintro ⟨hep, hev⟩
    have hlt := (TM.Packed.pairs_mem e).mp (List.mem_toFinset.mp hep)
    exact ⟨hep, (Obs.probe_as_matching le_rfl le_rfl false (by simp) M hM f hflaw e hlt).mp hev⟩
   ·
    rintro ⟨hep, heM⟩
    have hlt := (TM.Packed.pairs_mem e).mp (List.mem_toFinset.mp hep)
    exact ⟨hep, (Obs.probe_as_matching le_rfl le_rfl false (by simp) M hM f hflaw e hlt).mpr heM⟩
  refine ⟨Q, hQsub, hQdis, hprobe, fun z => ?_⟩
  rw [hflaw z.1 z.2, ← hQimg]
  exact active_iff_hit hQsub z
 ·
  obtain ⟨C, hC, hR, heval⟩ := hf
  obtain ⟨M, hM, h⟩ := Obs.classify_true k (hk7 rfl) C hC.1 hC.2 (by
   intro u v; simpa [nr, nc, adjA] using hR u v)
  have hMlaw : ∀ (x : Fin (nr k true) → Bool) (y : Fin (nc k true) → Bool),
    C.eval (List.ofFn x ++ List.ofFn y) = !true ↔
     (true = true ∧ (List.ofFn x ++ List.ofFn y).getD (k + 1) false = true) ∨ Obs.active M x y := by
   intro x y
   have h1 := not_congr (h x y)
   simp only [Bool.not_eq_true, not_not] at h1
   simp only [Bool.not_true, true_and, Obs.active]
   exact h1
  let Q : Finset (Fin k × Fin k) := (TM.Packed.pairs k).toFinset.filter (fun e => Obs.ends e ∈ M)
  have hQsub : Q ⊆ (TM.Packed.pairs k).toFinset := Finset.filter_subset _ _
  have hQord : ∀ e ∈ Q, e.1 < e.2 := fun e he => (TM.Packed.pairs_mem e).mp (List.mem_toFinset.mp (hQsub he))
  have hQdis : TM.disjointEdges Q := by
   intro e he f' hf' hne
   exact hM.2 _ (Finset.mem_filter.mp he).2 _ (Finset.mem_filter.mp hf').2
    (fun eq => hne (Obs.ends_injective e f' (hQord e he) (hQord f' hf') eq))
  have hQimg : Q.image Obs.ends = M := by
   ext s; constructor
   · intro hs; obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs; exact (Finset.mem_filter.mp he).2
   ·
    intro hs; obtain ⟨e, hlt, rfl⟩ := Obs.min_key_sorted s (hM.1 s hs)
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ((TM.Packed.pairs_mem e).mpr hlt), hs⟩)
  have hflaw : ∀ x y, f x y = !true ↔
    (true = true ∧ (List.ofFn x ++ List.ofFn y).getD (k + 1) false = true) ∨ Obs.active M x y := by
   intro x y; rw [heval x y]; exact hMlaw x y
  have hprobe : probe k true f = Q := by
   ext e; simp only [probe, Q, Finset.mem_filter]; constructor
   ·
    rintro ⟨hep, hev⟩
    have hlt := (TM.Packed.pairs_mem e).mp (List.mem_toFinset.mp hep)
    exact ⟨hep, (Obs.probe_as_matching (by simp [nr]) (by simp [nc]) true (fun _ => by simp [nr]) M hM f hflaw e hlt).mp hev⟩
   ·
    rintro ⟨hep, heM⟩
    have hlt := (TM.Packed.pairs_mem e).mp (List.mem_toFinset.mp hep)
    exact ⟨hep, (Obs.probe_as_matching (by simp [nr]) (by simp [nc]) true (fun _ => by simp [nr]) M hM f hflaw e hlt).mpr heM⟩
  refine ⟨Q, hQsub, hQdis, hprobe, fun z => ?_⟩
  rw [hflaw z.1 z.2, ← hQimg]
  exact active_iff_hit hQsub z
lemma exists_obs {k : ℕ} {crown : Bool} (hk2 : 2 ≤ k)
  {Q : Finset (Fin k × Fin k)} (hQ : Q ⊆ (TM.Packed.pairs k).toFinset) (hdis : TM.disjointEdges Q) :
  ∃ f : Fn k crown, eligible k crown f ∧ probe k crown f = Q ∧
   ∀ z, f z.1 z.2 = !crown ↔ baseHit k crown z = true ∨ ¬ Disjoint Q (support k crown z) := by
 have hord : ∀ e ∈ Q, e.1 < e.2 := fun e he => (TM.Packed.pairs_mem e).mp (List.mem_toFinset.mp (hQ he))
 let M := Q.image Obs.ends
 have hM : Obs.IsM M := isM_of_disjoint hord hdis
 cases crown
 ·
  obtain ⟨C, hm, hs, hR, hev⟩ := Obs.circuit_false k hk2 M hM
  let f : Fn k false := fun x y => C.eval (List.ofFn x ++ List.ofFn y)
  have hClaw : ∀ x y, f x y = !false ↔
    (false = true ∧ (List.ofFn x ++ List.ofFn y).getD (k + 1) false = true) ∨ Obs.active M x y := by
   intro x y
   simp only [f, Bool.not_false, Bool.false_eq_true, false_and, false_or, Obs.active]
   exact hev x y
  have hprobe : probe k false f = Q := by
   ext e; simp only [probe, Finset.mem_filter]; constructor
   ·
    rintro ⟨hep, hev'⟩
    have hlt := (TM.Packed.pairs_mem e).mp (List.mem_toFinset.mp hep)
    exact (mem_image_ends hord e hlt).mp
     ((Obs.probe_as_matching le_rfl le_rfl false (by simp) M hM f hClaw e hlt).mp hev')
   ·
    intro heQ
    have hep := hQ heQ
    have hlt := (TM.Packed.pairs_mem e).mp (List.mem_toFinset.mp hep)
    exact ⟨hep, (Obs.probe_as_matching le_rfl le_rfl false (by simp) M hM f hClaw e hlt).mpr
     ((mem_image_ends hord e hlt).mpr heQ)⟩
  refine ⟨f, ⟨C, ⟨hm, hs⟩, (fun u v => by simpa [nr, nc, adjA] using hR u v), fun _ _ => rfl⟩, hprobe, fun z => ?_⟩
  rw [hClaw z.1 z.2]
  exact active_iff_hit hQ z
 ·
  obtain ⟨C, hf, hs, hR, hev⟩ := Obs.circuit_true k hk2 M hM
  let f : Fn k true := fun x y => C.eval (List.ofFn x ++ List.ofFn y)
  have hClaw : ∀ x y, f x y = !true ↔
    (true = true ∧ (List.ofFn x ++ List.ofFn y).getD (k + 1) false = true) ∨ Obs.active M x y := by
   intro x y
   have h1 := not_congr (hev x y)
   simp only [Bool.not_eq_true, not_not] at h1
   simp only [f, Bool.not_true, true_and, Obs.active]
   exact h1
  have hprobe : probe k true f = Q := by
   ext e; simp only [probe, Finset.mem_filter]; constructor
   ·
    rintro ⟨hep, hev'⟩
    have hlt := (TM.Packed.pairs_mem e).mp (List.mem_toFinset.mp hep)
    exact (mem_image_ends hord e hlt).mp
     ((Obs.probe_as_matching (by simp [nr]) (by simp [nc]) true (fun _ => by simp [nr]) M hM f hClaw e hlt).mp hev')
   ·
    intro heQ
    have hep := hQ heQ
    have hlt := (TM.Packed.pairs_mem e).mp (List.mem_toFinset.mp hep)
    exact ⟨hep, (Obs.probe_as_matching (by simp [nr]) (by simp [nc]) true (fun _ => by simp [nr]) M hM f hClaw e hlt).mpr
     ((mem_image_ends hord e hlt).mpr heQ)⟩
  refine ⟨f, ⟨C, ⟨hf, hs⟩, (fun u v => by simpa [nr, nc, adjA] using hR u v), fun _ _ => rfl⟩, hprobe, fun z => ?_⟩
  rw [hClaw z.1 z.2]
  exact active_iff_hit hQ z
lemma bool_ne_iff_eq_not (a b : Bool) : a ≠ b ↔ a = !b := by
 cases a <;> cases b <;> decide
lemma fits_of_hardBad {k : ℕ} {crown : Bool} (hk2 : 2 ≤ k) (hk7 : crown = true → 7 ≤ k)
  {hard : List ((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool))}
  (hbad : hardBad k crown hard = true) :
  ∀ f : Fn k crown, ¬ fits k crown hard f := by
 intro f ⟨helig, hhard⟩
 obtain ⟨h, hh, hbh⟩ := List.any_eq_true.mp hbad
 obtain ⟨_, _, _, _, hlaw⟩ := classify_obs hk2 hk7 helig
 have hf1 : f h.1 h.2 = crown := hhard h hh
 have hf2 : f h.1 h.2 = !crown := (hlaw h).mpr (Or.inl hbh)
 rw [hf1] at hf2
 cases crown <;> simp at hf2
lemma fits_iff_allowed {k : ℕ} {crown : Bool} (hk2 : 2 ≤ k) (hk7 : crown = true → 7 ≤ k)
  {hard : List ((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool))}
  (hok : hardBad k crown hard = false) {f : Fn k crown} (helig : eligible k crown f) :
  fits k crown hard f ↔ probe k crown f ⊆ allowedEdges k crown hard := by
 obtain ⟨Q, hQ, _, hprobe, hlaw⟩ := classify_obs hk2 hk7 helig
 rw [hprobe]
 have hno : ∀ h ∈ hard, baseHit k crown h = false := by
  intro h hh
  cases hb : baseHit k crown h
  · rfl
  ·
   have : hardBad k crown hard = true := List.any_eq_true.mpr ⟨h, hh, hb⟩
   rw [hok] at this
   contradiction
 constructor
 ·
  rintro ⟨_, hhard⟩ e he
  refine Finset.mem_filter.mpr ⟨hQ he, List.all_eq_true.mpr fun h hh => ?_⟩
  by_contra hsup
  have hsup : e ∈ support k crown h := by simpa using hsup
  have hf1 : f h.1 h.2 = crown := hhard h hh
  have hf2 : f h.1 h.2 = !crown := (hlaw h).mpr (Or.inr (Finset.not_disjoint_iff.mpr ⟨e, he, hsup⟩))
  rw [hf1] at hf2
  cases crown <;> simp at hf2
 ·
  intro hsub
  refine ⟨helig, fun h hh => ?_⟩
  by_contra hne
  have hf2 : f h.1 h.2 = !crown := (bool_ne_iff_eq_not _ _).mp hne
  rcases (hlaw h).mp hf2 with hbad | hnd
  · have := hno h hh; rw [hbad] at this; contradiction
  ·
   obtain ⟨e, heQ, hesup⟩ := Finset.not_disjoint_iff.mp hnd
   have hall := List.all_eq_true.mp (Finset.mem_filter.mp (hsub heQ)).2 h hh
   simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hall
   exact hall hesup
lemma exists_fits {k : ℕ} {crown : Bool} (hk2 : 2 ≤ k)
  {hard : List ((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool))}
  (hok : hardBad k crown hard = false) {Q : Finset (Fin k × Fin k)}
  (hQ : Q ⊆ allowedEdges k crown hard) (hdis : TM.disjointEdges Q) :
  ∃ f : Fn k crown, fits k crown hard f ∧ probe k crown f = Q := by
 have hQp : Q ⊆ (TM.Packed.pairs k).toFinset := hQ.trans (Finset.filter_subset _ _)
 obtain ⟨f, helig, hprobe, hlaw⟩ := exists_obs hk2 hQp hdis
 refine ⟨f, ⟨helig, fun h hh => ?_⟩, hprobe⟩
 have hno : baseHit k crown h = false := by
  cases hb : baseHit k crown h
  · rfl
  ·
   have : hardBad k crown hard = true := List.any_eq_true.mpr ⟨h, hh, hb⟩
   rw [hok] at this
   contradiction
 by_contra hne
 have hf2 : f h.1 h.2 = !crown := (bool_ne_iff_eq_not _ _).mp hne
 rcases (hlaw h).mp hf2 with hbad | hnd
 · rw [hbad] at hno; contradiction
 ·
  obtain ⟨e, heQ, hesup⟩ := Finset.not_disjoint_iff.mp hnd
  have hall := List.all_eq_true.mp (Finset.mem_filter.mp (hQ heQ)).2 h hh
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hall
  exact hall hesup
def baseOffset (k : ℕ) (crown : Bool)
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool)) : ℤ :=
 ((soft.filter (fun t => baseHit k crown t.1 && (t.2 == !crown))).length : ℤ) +
  (((unforcedRows k crown soft).filter (fun r => !r.2)).length : ℤ)
def coeff (k : ℕ) (crown : Bool)
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool))
  (T : Finset (Fin k × Fin k)) : ℤ :=
 (if T = ∅ then baseOffset k crown soft else 0) +
  (-1 : ℤ) ^ T.card * TM.signed (unforcedRows k crown soft) T
lemma sum_powerset_disjoint {α : Type*} [DecidableEq α] (Q R : Finset α) :
  Q.powerset.sum (fun T => if T ⊆ R then (-1 : ℤ) ^ T.card else 0) =
   if Disjoint Q R then 1 else 0 := by
 rw [← Finset.sum_filter]
 have hfilt : Q.powerset.filter (fun T => T ⊆ R) = (Q ∩ R).powerset := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
 rw [hfilt, Finset.sum_powerset_neg_one_pow_card]
 by_cases hd : Disjoint Q R
 ·
  have he : Q ∩ R = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd
  simp [hd, he]
 ·
  have hne : Q ∩ R ≠ ∅ := fun he => hd (Finset.disjoint_iff_inter_eq_empty.mpr he)
  simp [hd, hne]
lemma score_eq_sum {k : ℕ} {crown : Bool} (hk2 : 2 ≤ k) (hk7 : crown = true → 7 ≤ k)
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool))
  {f : Fn k crown} (helig : eligible k crown f) :
  (score k crown soft f : ℤ) = (probe k crown f).powerset.sum (coeff k crown soft) := by
 obtain ⟨Q, _, _, hprobe, hlaw⟩ := classify_obs hk2 hk7 helig
 rw [hprobe]
 have h1 : (score k crown soft f : ℤ) =
   baseOffset k crown soft +
    ((unforcedRows k crown soft).map (fun r => if Disjoint Q r.1 then TM.sign r.2 else 0)).sum := by
  unfold score baseOffset unforcedRows
  induction soft with
  | nil => simp
  | cons t ts ih =>
   simp only [List.filter_cons]
   have htf := hlaw t.1
   cases hb : baseHit k crown t.1
   ·
    simp only [hb, Bool.false_eq_true, false_and, ↓reduceIte, Bool.not_false,
     List.map_cons, List.filter_cons, List.sum_cons]
    by_cases hd : Disjoint Q (support k crown t.1)
    ·
     have hfn : f t.1.1 t.1.2 = crown := by
      by_contra hne
      rcases htf.mp ((bool_ne_iff_eq_not _ _).mp hne) with hbad | hnd
      · rw [hbad] at hb; contradiction
      · exact hnd hd
     have hdec : decide (f t.1.1 t.1.2 = t.2) = (t.2 == crown) := by
      rw [hfn]; cases crown <;> cases t.2 <;> rfl
     rw [hdec]
     cases ht : (t.2 == crown) <;> simp [ht, TM.sign, hd] at ih ⊢ <;> omega
    ·
     have hfn : f t.1.1 t.1.2 = !crown := htf.mpr (Or.inr hd)
     have hdec : decide (f t.1.1 t.1.2 = t.2) = !(t.2 == crown) := by
      rw [hfn]; cases crown <;> cases t.2 <;> rfl
     rw [hdec]
     cases ht : (t.2 == crown) <;> simp [ht, TM.sign, hd] at ih ⊢ <;> omega
   ·
    have hfn : f t.1.1 t.1.2 = !crown := htf.mpr (Or.inl hb)
    have hdec : decide (f t.1.1 t.1.2 = t.2) = (t.2 == !crown) := by
     rw [hfn]; cases crown <;> cases t.2 <;> rfl
    simp only [hb, Bool.true_and, Bool.not_true, hdec]
    cases ht : (t.2 == !crown) <;> simp [ht] at ih ⊢ <;> omega
 have h2 : ((unforcedRows k crown soft).map (fun r => if Disjoint Q r.1 then TM.sign r.2 else 0)).sum =
   Q.powerset.sum (fun T => (-1 : ℤ) ^ T.card * TM.signed (unforcedRows k crown soft) T) := by
  have hrow (r : TM.Row k) :
    (if Disjoint Q r.1 then TM.sign r.2 else 0) =
     Q.powerset.sum (fun T => (-1 : ℤ) ^ T.card * TM.rowContribution T r) := by
   have hite : (if Disjoint Q r.1 then TM.sign r.2 else 0) =
     TM.sign r.2 * (if Disjoint Q r.1 then 1 else 0) := by split_ifs <;> simp
   rw [hite, ← sum_powerset_disjoint Q r.1, Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro T _
   by_cases hsub : T ⊆ r.1 <;> simp [TM.rowContribution, hsub, mul_comm]
  simp_rw [hrow, TM.list_sum_finset_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [TM.signed_eq_sum]
  change ((unforcedRows k crown soft).map (fun r => (-1 : ℤ) ^ T.card * TM.rowContribution T r)).sum =
   (-1 : ℤ) ^ T.card * ((unforcedRows k crown soft).map (TM.rowContribution T)).sum
  rw [List.sum_map_mul_left]
 rw [h1, h2]
 unfold coeff
 simp only [Finset.sum_add_distrib]
 rw [Finset.sum_ite_eq', if_pos (Finset.mem_powerset.mpr (Finset.empty_subset Q))]
lemma mob_ind_finset {α : Type*} [DecidableEq α] (A S : Finset α) :
  S.powerset.sum (fun T => (-1 : ℤ) ^ (S.card - T.card) * (if A ⊆ T then 1 else 0)) =
   if A = S then 1 else 0 := by
 simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
 by_cases hAS : A ⊆ S
 ·
  have key : (S.powerset.filter (fun T => A ⊆ T)).sum (fun T => (-1 : ℤ) ^ (S.card - T.card)) =
    (S \ A).powerset.sum (fun V => (-1 : ℤ) ^ ((S \ A).card - V.card)) := by
   apply Finset.sum_nbij' (fun T => T \ A) (fun V => V ∪ A)
   ·
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
    exact Finset.sdiff_subset_sdiff hT.1 le_rfl
   ·
    intro V hV
    simp only [Finset.mem_filter, Finset.mem_powerset] at hV ⊢
    exact ⟨Finset.union_subset (hV.trans Finset.sdiff_subset) hAS, Finset.subset_union_right⟩
   ·
    intro T hT
    exact Finset.sdiff_union_of_subset (Finset.mem_filter.mp hT).2
   ·
    intro V hV
    exact Finset.union_sdiff_cancel_right
     (Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hV) disjoint_sdiff_self_left)
   ·
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    have h1 := Finset.card_sdiff_add_card_eq_card hAS
    have h2 := Finset.card_sdiff_add_card_eq_card hT.2
    have h3 := Finset.card_le_card hT.1
    congr 1; omega
  rw [key]
  have halt : ∀ W : Finset α, W.powerset.sum (fun V => (-1 : ℤ) ^ (W.card - V.card)) =
    if W = ∅ then 1 else 0 := by
   intro W
   have h : ∀ V ∈ W.powerset, (-1 : ℤ) ^ (W.card - V.card) = (-1) ^ W.card * (-1) ^ V.card := by
    intro V hV
    have hle : V.card ≤ W.card := Finset.card_le_card (Finset.mem_powerset.mp hV)
    have e : (-1 : ℤ) ^ W.card = (-1) ^ (W.card - V.card) * (-1) ^ V.card := by
     rw [← pow_add, Nat.sub_add_cancel hle]
    rw [e, mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
   rw [Finset.sum_congr rfl h, ← Finset.mul_sum, Finset.sum_powerset_neg_one_pow_card]
   split_ifs with hW <;> simp [hW]
  rw [halt]
  by_cases hA : A = S
  · subst hA; simp
  ·
   rw [ite_eq_right hA, ite_eq_right]
   intro he
   exact hA (Finset.Subset.antisymm hAS (Finset.sdiff_eq_empty_iff_subset.mp he))
 ·
  have : S.powerset.filter (fun T => A ⊆ T) = ∅ := by
   rw [Finset.filter_eq_empty_iff]
   intro T hT hA
   exact hAS (hA.trans (Finset.mem_powerset.mp hT))
  rw [this, Finset.sum_empty, ite_eq_right]
  rintro rfl
  exact hAS Finset.Subset.rfl
lemma alt_sum_of_powerset {α : Type*} [DecidableEq α] (Q : Finset α) (g : Finset α → ℤ)
  (val : Finset α → ℤ) (hval : ∀ T ⊆ Q, val T = T.powerset.sum g) :
  Q.powerset.sum (fun T => (-1 : ℤ) ^ (Q.card - T.card) * val T) = g Q := by
 have h1 : Q.powerset.sum (fun T => (-1 : ℤ) ^ (Q.card - T.card) * val T) =
   Q.powerset.sum (fun T => Q.powerset.sum (fun U =>
    (-1 : ℤ) ^ (Q.card - T.card) * (if U ⊆ T then g U else 0))) := by
  apply Finset.sum_congr rfl
  intro T hT
  rw [hval T (Finset.mem_powerset.mp hT), Finset.mul_sum]
  have hsub : T.powerset = Q.powerset.filter (fun U => U ⊆ T) := by
   ext U; simp only [Finset.mem_powerset, Finset.mem_filter]
   exact ⟨fun h => ⟨h.trans (Finset.mem_powerset.mp hT), h⟩, And.right⟩
  rw [hsub, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro U _
  split_ifs <;> simp
 rw [h1, Finset.sum_comm]
 have h2 : ∀ U ∈ Q.powerset,
   Q.powerset.sum (fun T => (-1 : ℤ) ^ (Q.card - T.card) * (if U ⊆ T then g U else 0)) =
    if U = Q then g Q else 0 := by
  intro U _
  have hfactor : ∀ T ∈ Q.powerset,
    (-1 : ℤ) ^ (Q.card - T.card) * (if U ⊆ T then g U else 0) =
     g U * ((-1 : ℤ) ^ (Q.card - T.card) * (if U ⊆ T then 1 else 0)) := by
   intro T _; split_ifs <;> ring
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum, mob_ind_finset]
  split_ifs with hUQ <;> simp [hUQ]
 rw [Finset.sum_congr rfl h2]
 simp
lemma alt_sum_score {k : ℕ} {crown : Bool} (hk2 : 2 ≤ k) (hk7 : crown = true → 7 ≤ k)
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool))
  {Q : Finset (Fin k × Fin k)} (hQne : Q.Nonempty)
  (cube : Finset (Fin k × Fin k) → Fn k crown)
  (hcube : ∀ T ⊆ Q, eligible k crown (cube T) ∧ probe k crown (cube T) = T) :
  Q.powerset.sum (fun T => (-1 : ℤ) ^ (Q.card - T.card) * (score k crown soft (cube T) : ℤ)) =
   (-1 : ℤ) ^ Q.card * TM.signed (unforcedRows k crown soft) Q := by
 have hval : ∀ T ⊆ Q, (score k crown soft (cube T) : ℤ) = T.powerset.sum (coeff k crown soft) := by
  intro T hT
  rw [score_eq_sum hk2 hk7 soft (hcube T hT).1, (hcube T hT).2]
 rw [alt_sum_of_powerset Q (coeff k crown soft) _ hval, coeff]
 simp [hQne.ne_empty]
lemma low_iff_signed_zero {k d : ℕ} {crown : Bool} (hk2 : 2 ≤ k) (hk7 : crown = true → 7 ≤ k)
  {hard : List ((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool))}
  (hok : hardBad k crown hard = false)
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool)) :
  low k d crown hard soft ↔
   ∀ Q, Q ⊆ allowedEdges k crown hard → TM.disjointEdges Q → d < Q.card →
    TM.signed (unforcedRows k crown soft) Q = 0 := by
 constructor
 ·
  rintro ⟨a, ha⟩ Q hQ hdis hdQ
  have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
  have hcube : ∀ T : Finset (Fin k × Fin k),
    ∃ f : Fn k crown, T ⊆ Q → fits k crown hard f ∧ probe k crown f = T := by
   intro T
   by_cases hTQ : T ⊆ Q
   ·
    obtain ⟨f, hf, hp⟩ := exists_fits hk2 hok (hTQ.trans hQ)
     (fun e he z hz hne => hdis e (hTQ he) z (hTQ hz) hne)
    exact ⟨f, fun _ => ⟨hf, hp⟩⟩
   · exact ⟨fun _ _ => false, fun h => (hTQ h).elim⟩
  let cube : Finset (Fin k × Fin k) → Fn k crown := fun T => (hcube T).choose
  have hc : ∀ T ⊆ Q, fits k crown hard (cube T) ∧ probe k crown (cube T) = T :=
   fun T hT => (hcube T).choose_spec hT
  have halt := alt_sum_score hk2 hk7 soft hQne cube (fun T hT => ⟨(hc T hT).1.1, (hc T hT).2⟩)
  let g : Finset (Fin k × Fin k) → ℤ := fun T => if T.card ≤ d then a T else 0
  have hval : ∀ T ⊆ Q, (score k crown soft (cube T) : ℤ) = T.powerset.sum g := by
   intro T hT
   rw [ha (cube T) (hc T hT).1, (hc T hT).2, Finset.sum_filter]
  have hzero := alt_sum_of_powerset Q g _ hval
  have hgQ : g Q = 0 := by simp [g, show ¬ Q.card ≤ d by omega]
  rw [halt, hgQ] at hzero
  rcases mul_eq_zero.mp hzero with hpow | hs
  · exact absurd hpow (pow_ne_zero _ (by norm_num))
  · exact hs
 ·
  intro hall
  refine ⟨coeff k crown soft, fun f hf => ?_⟩
  rw [score_eq_sum hk2 hk7 soft hf.1, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hTd : T.card ≤ d
  · simp [hTd]
  ·
   simp only [hTd, ↓reduceIte]
   have hTp : T ⊆ probe k crown f := Finset.mem_powerset.mp hT
   have hpf := (fits_iff_allowed hk2 hk7 hok hf.1).mp hf
   obtain ⟨P, _, hPdis, hPp, _⟩ := classify_obs hk2 hk7 hf.1
   rw [hPp] at hTp
   have hTdis : TM.disjointEdges T := fun e he z hz hne => hPdis e (hTp he) z (hTp hz) hne
   have hTall : T ⊆ allowedEdges k crown hard := hTp.trans (hPp ▸ hpf)
   have hs0 := hall T hTall hTdis (by omega)
   have hTne : T ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp (by omega))
   simp [coeff, hTne, hs0]
lemma realizes_of_signed {k d : ℕ} {crown : Bool} (hk2 : 2 ≤ k) (hk7 : crown = true → 7 ≤ k)
  {hard : List ((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool))}
  (hok : hardBad k crown hard = false)
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool))
  {Q : Finset (Fin k × Fin k)} (hQ : Q ⊆ allowedEdges k crown hard)
  (hdis : TM.disjointEdges Q) (hdQ : d < Q.card) :
  realizes k d crown hard soft Q ((-1 : ℤ) ^ Q.card * TM.signed (unforcedRows k crown soft) Q) := by
 have hQord : ∀ e ∈ Q, e.1 < e.2 := fun e he =>
  (TM.Packed.pairs_mem e).mp (List.mem_toFinset.mp (Finset.filter_subset _ _ (hQ he)))
 have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
 have hcube : ∀ T : Finset (Fin k × Fin k),
   ∃ f : Fn k crown, T ⊆ Q → fits k crown hard f ∧ probe k crown f = T := by
  intro T
  by_cases hTQ : T ⊆ Q
  ·
   obtain ⟨f, hf, hp⟩ := exists_fits hk2 hok (hTQ.trans hQ)
    (fun e he z hz hne => hdis e (hTQ he) z (hTQ hz) hne)
   exact ⟨f, fun _ => ⟨hf, hp⟩⟩
  · exact ⟨fun _ _ => false, fun h => (hTQ h).elim⟩
 let cube : Finset (Fin k × Fin k) → Fn k crown := fun T => (hcube T).choose
 have hc : ∀ T ⊆ Q, fits k crown hard (cube T) ∧ probe k crown (cube T) = T :=
  fun T hT => (hcube T).choose_spec hT
 refine ⟨hdQ, hQord, hdis, cube, hc, ?_⟩
 exact alt_sum_score hk2 hk7 soft hQne cube (fun T hT => ⟨(hc T hT).1.1, (hc T hT).2⟩)
lemma realizes_imp {k d : ℕ} {crown : Bool} (hk2 : 2 ≤ k) (hk7 : crown = true → 7 ≤ k)
  {hard : List ((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool))}
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool))
  {Z : Finset (Fin k × Fin k)} {v : ℤ} (hv : v ≠ 0)
  (hreal : realizes k d crown hard soft Z v) :
  hardBad k crown hard = false ∧ Z ⊆ allowedEdges k crown hard ∧
   TM.disjointEdges Z ∧ d < Z.card ∧ TM.signed (unforcedRows k crown soft) Z ≠ 0 := by
 obtain ⟨hdZ, _, hZdis, cube, hcube, hsum⟩ := hreal
 have hZne : Z.Nonempty := Finset.card_pos.mp (by omega)
 have hfit := (hcube Z Finset.Subset.rfl).1
 have hprobe := (hcube Z Finset.Subset.rfl).2
 have hok : hardBad k crown hard = false := by
  cases hb : hardBad k crown hard
  · rfl
  · exact (fits_of_hardBad hk2 hk7 hb (cube Z) hfit).elim
 have hZsub : Z ⊆ allowedEdges k crown hard := by
  rw [← hprobe]
  exact (fits_iff_allowed hk2 hk7 hok hfit.1).mp hfit
 have halt := alt_sum_score hk2 hk7 soft hZne cube (fun T hT => ⟨(hcube T hT).1.1, (hcube T hT).2⟩)
 rw [hsum] at halt
 have hsne : TM.signed (unforcedRows k crown soft) Z ≠ 0 := by
  intro hs0
  rw [hs0, mul_zero] at halt
  exact hv halt
 exact ⟨hok, hZsub, hZdis, hdZ, hsne⟩
lemma min_card_le_log2 {k d : ℕ} {crown : Bool}
  {hard : List ((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool))}
  (soft : List (((Fin (nr k crown) → Bool) × (Fin (nc k crown) → Bool)) × Bool))
  {Q : Finset (Fin k × Fin k)} (hQ : Q ⊆ allowedEdges k crown hard)
  (hdis : TM.disjointEdges Q) (hdQ : d < Q.card)
  (hsne : TM.signed (unforcedRows k crown soft) Q ≠ 0)
  (hmin : ∀ Z, Z ⊆ allowedEdges k crown hard → TM.disjointEdges Z → d < Z.card →
   TM.signed (unforcedRows k crown soft) Z ≠ 0 → Q.card ≤ Z.card) :
  Q.card ≤ d + 1 + soft.length.log2 := by
 obtain ⟨A, hAQ, hAcard⟩ := Finset.exists_subset_card_eq (show d + 1 ≤ Q.card by omega)
 let M := Q \ A
 have hMcard : M.card = Q.card - (d + 1) := by
  have := Finset.card_sdiff_add_card_eq_card hAQ
  change M.card + A.card = Q.card at this
  omega
 let rows := unforcedRows k crown soft
 have hsurj : ∀ U ∈ M.powerset, ∃ i : Fin rows.length, A ⊆ rows[i].1 ∧ M ∩ rows[i].1 = U := by
  intro U hU
  have hUM : U ⊆ M := Finset.mem_powerset.mp hU
  let S := (M.powerset.filter (fun V => U ⊆ V)).sum
   (fun V => (-1 : ℤ) ^ (M.card - V.card) * TM.signed rows (A ∪ V))
  have hS1 : S = TM.signed rows Q := by
   have hterm : ∀ V ∈ M.powerset.filter (fun V => U ⊆ V),
     (-1 : ℤ) ^ (M.card - V.card) * TM.signed rows (A ∪ V) =
      if V = M then TM.signed rows Q else 0 := by
    intro V hV
    have hVM : V ⊆ M := Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1
    by_cases heq : V = M
    ·
     subst heq
     have hAM : A ∪ M = Q := Finset.union_sdiff_of_subset hAQ
     simp [hAM]
    ·
     have hlt : V.card < M.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hVM, heq⟩)
     have hAVQ : A ∪ V ⊆ Q := Finset.union_subset hAQ (hVM.trans Finset.sdiff_subset)
     have hAVdis : TM.disjointEdges (A ∪ V) :=
      fun e he z hz hne => hdis e (hAVQ he) z (hAVQ hz) hne
     have hdisAM : Disjoint A V := Disjoint.mono_right hVM disjoint_sdiff_self_right
     have hcard1 : (A ∪ V).card = A.card + V.card := Finset.card_union_of_disjoint hdisAM
     have hcard2 : (A ∪ V).card < Q.card := by omega
     have hdAV : d < (A ∪ V).card := by omega
     have hz : TM.signed rows (A ∪ V) = 0 := by
      by_contra hnz
      have := hmin (A ∪ V) (hAVQ.trans hQ) hAVdis hdAV hnz
      omega
     simp [heq, hz]
   dsimp only [S]
   rw [Finset.sum_congr rfl hterm]
   simp [Finset.sum_ite_eq', hUM]
  have hlist : rows = (List.finRange rows.length).map (fun i => rows[i]) := by
   apply List.ext_getElem (by simp)
   intro i _ _
   simp
  have hS2 : S = ((List.finRange rows.length).map (fun i =>
    TM.sign rows[i].2 * (M.powerset.filter (fun V => U ⊆ V)).sum
     (fun V => (-1 : ℤ) ^ (M.card - V.card) *
      (if A ⊆ rows[i].1 ∧ V ⊆ M ∩ rows[i].1 then 1 else 0)))).sum := by
   have hexp : ∀ V ∈ M.powerset.filter (fun V => U ⊆ V), TM.signed rows (A ∪ V) =
     ((List.finRange rows.length).map (fun i =>
      TM.sign rows[i].2 * (if A ⊆ rows[i].1 ∧ V ⊆ M ∩ rows[i].1 then 1 else 0))).sum := by
    intro V hV
    have hVM : V ⊆ M := Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1
    rw [TM.signed_eq_sum]
    conv_lhs => rw [hlist, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    dsimp only [Function.comp_def]
    by_cases h1 : A ⊆ rows[i].1 <;> by_cases h2 : V ⊆ M ∩ rows[i].1
    ·
     have hsub : A ∪ V ⊆ rows[i].1 := Finset.union_subset h1 (h2.trans Finset.inter_subset_right)
     rw [TM.rowContribution, if_pos hsub, if_pos ⟨h1, h2⟩, mul_one]
    ·
     have hsub : ¬ A ∪ V ⊆ rows[i].1 := fun h =>
      h2 (Finset.subset_inter hVM (Finset.subset_union_right.trans h))
     rw [TM.rowContribution, if_neg hsub, if_neg (fun ⟨_, h⟩ => h2 h), mul_zero]
    ·
     have hsub : ¬ A ∪ V ⊆ rows[i].1 := fun h => h1 (Finset.subset_union_left.trans h)
     rw [TM.rowContribution, if_neg hsub, if_neg (fun ⟨h, _⟩ => h1 h), mul_zero]
    ·
     have hsub : ¬ A ∪ V ⊆ rows[i].1 := fun h => h1 (Finset.subset_union_left.trans h)
     rw [TM.rowContribution, if_neg hsub, if_neg (fun ⟨h, _⟩ => h1 h), mul_zero]
   have hmul : ∀ V ∈ M.powerset.filter (fun V => U ⊆ V),
     (-1 : ℤ) ^ (M.card - V.card) * TM.signed rows (A ∪ V) =
      ((List.finRange rows.length).map (fun i =>
       TM.sign rows[i].2 * ((-1 : ℤ) ^ (M.card - V.card) *
        (if A ⊆ rows[i].1 ∧ V ⊆ M ∩ rows[i].1 then 1 else 0)))).sum := by
    intro V hV
    rw [hexp V hV]
    change (-1 : ℤ) ^ (M.card - V.card) * _ = _
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro i _
    ring
   change (M.powerset.filter (fun V => U ⊆ V)).sum
    (fun V => (-1 : ℤ) ^ (M.card - V.card) * TM.signed rows (A ∪ V)) = _
   rw [Finset.sum_congr rfl hmul, ← TM.list_sum_finset_sum]
   congr 1
   apply List.map_congr_left
   intro i _
   rw [← Finset.mul_sum]
  by_contra hnone
  push Not at hnone
  have hzero : S = 0 := by
   rw [hS2]
   apply List.sum_eq_zero
   intro x hx
   obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
   by_cases hAi : A ⊆ rows[i].1
   ·
    let Si := M ∩ rows[i].1
    have hne : U ≠ Si := fun h => hnone i hAi h.symm
    have hsum : (M.powerset.filter (fun V => U ⊆ V)).sum
      (fun V => (-1 : ℤ) ^ (M.card - V.card) * (if A ⊆ rows[i].1 ∧ V ⊆ Si then 1 else 0)) = 0 := by
     by_cases hUS : U ⊆ Si
     ·
      have hfilt : (M.powerset.filter (fun V => U ⊆ V)).sum
        (fun V => (-1 : ℤ) ^ (M.card - V.card) * (if A ⊆ rows[i].1 ∧ V ⊆ Si then 1 else 0)) =
        (-1 : ℤ) ^ (M.card - Si.card) *
         Si.powerset.sum (fun V => (-1 : ℤ) ^ (Si.card - V.card) * (if U ⊆ V then 1 else 0)) := by
       have hl : (M.powerset.filter (fun V => U ⊆ V)).sum
         (fun V => (-1 : ℤ) ^ (M.card - V.card) * (if A ⊆ rows[i].1 ∧ V ⊆ Si then 1 else 0)) =
         ((M.powerset.filter (fun V => U ⊆ V)).filter (fun V => A ⊆ rows[i].1 ∧ V ⊆ Si)).sum
         (fun V => (-1 : ℤ) ^ (M.card - V.card)) := by
        simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
       have hr : Si.powerset.sum (fun V => (-1 : ℤ) ^ (Si.card - V.card) * (if U ⊆ V then 1 else 0)) =
         (Si.powerset.filter (fun V => U ⊆ V)).sum (fun V => (-1 : ℤ) ^ (Si.card - V.card)) := by
        simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
       have heqF : (M.powerset.filter (fun V => U ⊆ V)).filter (fun V => A ⊆ rows[i].1 ∧ V ⊆ Si) =
         Si.powerset.filter (fun V => U ⊆ V) := by
        ext V
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun ⟨⟨_, hUV⟩, _, hVS⟩ => ⟨hVS, hUV⟩,
         fun ⟨hVS, hUV⟩ => ⟨⟨hVS.trans Finset.inter_subset_left, hUV⟩, hAi, hVS⟩⟩
       rw [hl, hr, heqF, Finset.mul_sum]
       apply Finset.sum_congr rfl
       intro V hV
       have hVS : V ⊆ Si := Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1
       have h1 : V.card ≤ Si.card := Finset.card_le_card hVS
       have h2 : Si.card ≤ M.card := Finset.card_le_card Finset.inter_subset_left
       rw [← pow_add, show M.card - Si.card + (Si.card - V.card) = M.card - V.card by omega]
      rw [hfilt, mob_ind_finset, ite_eq_right hne, mul_zero]
     ·
      apply Finset.sum_eq_zero
      intro V hV
      have hUV : U ⊆ V := (Finset.mem_filter.mp hV).2
      have hnot : ¬ (A ⊆ rows[i].1 ∧ V ⊆ Si) := fun h => hUS (hUV.trans h.2)
      rw [if_neg hnot, mul_zero]
    rw [hsum, mul_zero]
   ·
    have hsum : (M.powerset.filter (fun V => U ⊆ V)).sum
      (fun V => (-1 : ℤ) ^ (M.card - V.card) * (if A ⊆ rows[i].1 ∧ V ⊆ M ∩ rows[i].1 then 1 else 0)) = 0 := by
     apply Finset.sum_eq_zero
     intro V _
     have hnot : ¬ (A ⊆ rows[i].1 ∧ V ⊆ M ∩ rows[i].1) := fun h => hAi h.1
     rw [if_neg hnot, mul_zero]
    rw [hsum, mul_zero]
  rw [hS1] at hzero
  exact hsne hzero
 have hsub : M.powerset ⊆ (Finset.univ : Finset (Fin rows.length)).image (fun i => M ∩ rows[i].1) := by
  intro U hU
  obtain ⟨i, _, hi⟩ := hsurj U hU
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
 have hcard : 2 ^ M.card ≤ soft.length := by
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_powerset] at h1
  have h2 : ((Finset.univ : Finset (Fin rows.length)).image (fun i => M ∩ rows[i].1)).card ≤ rows.length :=
   Finset.card_image_le.trans (by simp)
  have h3 : rows.length ≤ soft.length := by
   simp only [rows, unforcedRows, List.length_map]
   exact List.length_filter_le _ _
  omega
 have hsoft0 : soft.length ≠ 0 := by
  have : 0 < 2 ^ M.card := Nat.two_pow_pos _
  omega
 have hlog : M.card ≤ soft.length.log2 := (Nat.le_log2 hsoft0).mpr hcard
 omega
end Math

namespace Alg
open TM TM.Lib TM.Lib.Machines TM.Lib.Universal TM.MachineBits TM.Packed
def orFlag (a b : List Bool) : List Bool := sel a b [true]
def andFlag (a b : List Bool) : List Bool := sel a [] b
def notFlag (a : List Bool) : List Bool := sel a [true] []
lemma cpOrFlag {u v : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) :
 CPTs (fun s => orFlag (u s) (v s)) := cpt_sel hu hv (cpt_const [true])
lemma cpAndFlag {u v : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) :
 CPTs (fun s => andFlag (u s) (v s)) := cpt_sel hu (cpt_const []) hv
lemma cpNotFlag {u : List Bool → List Bool} (hu : CPTs u) :
 CPTs (fun s => notFlag (u s)) := cpt_sel hu (cpt_const [true]) (cpt_const [])
lemma orFlag_bflag (x y : Bool) : orFlag (bflag x) (bflag y) = bflag (x || y) := by
 cases x <;> cases y <;> rfl
lemma andFlag_bflag (x y : Bool) : andFlag (bflag x) (bflag y) = bflag (x && y) := by
 cases x <;> cases y <;> rfl
lemma notFlag_bflag (x : Bool) : notFlag (bflag x) = bflag (!x) := by
 cases x <;> rfl
lemma q16_bflag (x : Bool) : q16 (bflag x) = [x] := by
 cases x <;> rfl
lemma bflag_take_one (x : Bool) : (bflag x).take 1 = bflag x := by
 cases x <;> rfl
lemma range_flatMap_get_list {α β : Type*} (L : List α) (f : α → List β) (g : ℕ → List β)
  (hg : ∀ i (hi : i < L.length), g i = f L[i]) :
  (List.range L.length).flatMap g = L.flatMap f := by
 induction L generalizing g with
 | nil => rfl
 | cons a L ih =>
  rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  rw [hg 0 (Nat.zero_lt_succ _), List.getElem_cons_zero, List.flatMap_cons]
  congr 1
  exact ih (fun i => g (i + 1)) (fun i hi => by
   simpa using hg (i + 1) (Nat.succ_lt_succ hi))
lemma range_flatMap_get_map {α β : Type*} (L : List α) (f : α → β) (g : ℕ → List β)
  (hg : ∀ i (hi : i < L.length), g i = [f L[i]]) :
  (List.range L.length).flatMap g = L.map f := by
 rw [range_flatMap_get_list L (fun a => [f a]) g hg]
 clear hg
 induction L with
 | nil => rfl
 | cons a L ih => simp [List.flatMap_cons, ih]
def baseHitStep (s : List Bool) : List Bool :=
 let v := left s
 let args := left (right s)
 let nrU := left args
 let bank := right args
 let acc := right (right s)
 orFlag acc (andFlag (bitFlagAt v bank) (bitFlagAt (nrU ++ v) bank))
lemma cpBaseHitStep : CPTs baseHitStep :=
 cpOrFlag (cpRight (cpRight cpt_id))
  (cpAndFlag (cpBitFlagAt (cpLeft cpt_id) (cpRight (cpLeft (cpRight cpt_id))))
   (cpBitFlagAt (cpt_app2 (cpLeft (cpLeft (cpRight cpt_id))) (cpLeft cpt_id))
    (cpRight (cpLeft (cpRight cpt_id)))))
def baseHitLoop (kU nrU bank : List Bool) : List Bool :=
 runIndexed replaceBound baseHitStep [true] kU (pairB nrU bank) []
lemma cpBaseHitLoop {kU nrU bank : List Bool → List Bool}
  (hk : CPTs kU) (hnr : CPTs nrU) (hb : CPTs bank) :
  CPTs (fun s => baseHitLoop (kU s) (nrU s) (bank s)) :=
 cpRunIndexed replaceBound_cpt replaceBound_length cpBaseHitStep
  (cpt_const [true]) hk (cpt_pairB2 hnr hb) (cpt_const [])
lemma baseHitLoop_eq (k nr : ℕ) (bank : List Bool) :
  baseHitLoop (un k) (un nr) bank =
   bflag (decide (∃ v : Fin k, bank.getD v.val false = true ∧ bank.getD (nr + v.val) false = true)) := by
 unfold baseHitLoop
 have h := runIndexed_ofListFold replaceBound baseHitStep [true] (un k) (pairB (un nr) bank) []
  (fun l b => l = bflag b)
  (fun i b => b || (bank.getD i false && bank.getD (nr + i) false))
  false rfl (fun i _ x b hx => by
   subst hx
   simp only [baseHitStep, left, right, unpairB_pairB, replaceBound, List.length_singleton,
    bitFlagAt_eq, un_length, List.length_append, orFlag_bflag, andFlag_bflag, bflag_take_one])
 rw [un_length] at h
 have hfold : ∀ (n : ℕ) (b₀ : Bool),
   (List.range n).foldr (fun i b => b || (bank.getD i false && bank.getD (nr + i) false)) b₀ =
    (b₀ || decide (∃ i < n, bank.getD i false = true ∧ bank.getD (nr + i) false = true)) := by
  intro n
  induction n with
  | zero => intro b₀; simp
  | succ n ih =>
   intro b₀
   rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih]
   cases b₀ <;> cases hp : (bank.getD n false && bank.getD (nr + n) false)
   ·
    simp only [Bool.false_or, decide_eq_decide]
    constructor
    · rintro ⟨i, hi, h1, h2⟩; exact ⟨i, by omega, h1, h2⟩
    ·
     rintro ⟨i, hi, h1, h2⟩
     rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
     · exact ⟨i, hlt, h1, h2⟩
     ·
      rw [h1, h2] at hp
      cases hp
   ·
    simp only [Bool.false_or, Bool.true_or]
    rw [eq_comm, decide_eq_true_eq]
    simp only [Bool.and_eq_true] at hp
    exact ⟨n, Nat.lt_succ_self n, hp.1, hp.2⟩
   · simp
   · simp
 rw [hfold k false, Bool.false_or] at h
 rw [h]
 congr 1
 simp only [decide_eq_decide]
 constructor
 · rintro ⟨i, hi, h1, h2⟩; exact ⟨⟨i, hi⟩, h1, h2⟩
 · rintro ⟨v, h1, h2⟩; exact ⟨v.val, v.isLt, h1, h2⟩
def baseHitFlag (crownF kU nrU bank : List Bool) : List Bool :=
 orFlag (andFlag crownF (bitFlagAt (kU ++ [true]) bank)) (baseHitLoop kU nrU bank)
lemma cpBaseHitFlag {crownF kU nrU bank : List Bool → List Bool}
  (hc : CPTs crownF) (hk : CPTs kU) (hnr : CPTs nrU) (hb : CPTs bank) :
  CPTs (fun s => baseHitFlag (crownF s) (kU s) (nrU s) (bank s)) :=
 cpOrFlag (cpAndFlag hc (cpBitFlagAt (cpt_app2 hk (cpt_const [true])) hb)) (cpBaseHitLoop hk hnr hb)
lemma baseHitFlag_eq {k : ℕ} {crown : Bool}
  (z : (Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool)) :
  baseHitFlag (bflag crown) (un k) (un (Math.nr k crown)) (List.ofFn z.1 ++ List.ofFn z.2) =
   bflag (Math.baseHit k crown z) := by
 simp only [baseHitFlag, bitFlagAt_eq, List.length_append, un_length, List.length_singleton,
  baseHitLoop_eq, andFlag_bflag, orFlag_bflag]
 cases crown <;> simp [Math.baseHit, Math.wire]
def supportEdgeBit (s : List Bool) : List Bool :=
 let i := left s
 let a := right s
 let kU := field 0 a
 let nrU := field 1 a
 let bank := field 2 a
 let pw := field 3 a
 let word := slot (kU ++ kU) i pw
 let u := hd (word.take kU.length)
 let v := hd (word.drop kU.length)
 let hit := orFlag (andFlag (bitFlagAt u bank) (bitFlagAt v bank))
  (andFlag (bitFlagAt (nrU ++ u) bank) (bitFlagAt (nrU ++ v) bank))
 q16 hit
lemma cpSupportEdgeBit : CPTs supportEdgeBit := by
 have hi := cpLeft cpt_id
 have ha := cpRight cpt_id
 have hk := cpField 0 ha
 have hnr := cpField 1 ha
 have hb := cpField 2 ha
 have hpw := cpField 3 ha
 have hw := cpSlot (cpt_app2 hk hk) hi hpw
 have hu := cpt_comp (cpTake hk hw) cpt_hd
 have hv := cpt_comp (cpDrop hk hw) cpt_hd
 exact q73 (cpOrFlag (cpAndFlag (cpBitFlagAt hu hb) (cpBitFlagAt hv hb))
  (cpAndFlag (cpBitFlagAt (cpt_app2 hnr hu) hb) (cpBitFlagAt (cpt_app2 hnr hv) hb)))
def supportMask (kU nrU pCount pw bank : List Bool) : List Bool :=
 mapRange supportEdgeBit [true] pCount (pack [kU, nrU, bank, pw])
lemma cpSupportMask {kU nrU pCount pw bank : List Bool → List Bool}
  (hk : CPTs kU) (hnr : CPTs nrU) (hp : CPTs pCount) (hpw : CPTs pw) (hb : CPTs bank) :
  CPTs (fun s => supportMask (kU s) (nrU s) (pCount s) (pw s) (bank s)) :=
 cpMapRange cpSupportEdgeBit (cpt_const [true]) hp
  (cpt_pairB2 hk (cpt_pairB2 hnr (cpt_pairB2 hb (cpt_pairB2 hpw (cpt_const [])))))
lemma supportEdgeBit_eq {k : ℕ} {crown : Bool}
  (z : (Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool))
  (i : ℕ) (hi : i < (pairs k).length) :
  supportEdgeBit (pairB (un i) (pack [un k, un (Math.nr k crown), List.ofFn z.1 ++ List.ofFn z.2, pairWords (un k)])) =
   [decide ((pairs k)[i] ∈ Math.support k crown z)] := by
 have hpw := pairWords_get k i hi
 simp only [supportEdgeBit, field_left_pair, field_right_pair, field_pack_zero, field_pack_succ,
  un_length]
 rw [hpw.1, hpw.2]
 simp only [bitFlagAt_eq, un_length, List.length_append, andFlag_bflag, orFlag_bflag, q16_bflag]
 congr 2
 have hmem : (pairs k)[i] ∈ (pairs k).toFinset := List.mem_toFinset.mpr (List.getElem_mem hi)
 simp [Math.support, Math.wire, hmem]
lemma supportMask_eq {k : ℕ} {crown : Bool}
  (z : (Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool)) :
  supportMask (un k) (un (Math.nr k crown)) (pairCount (un k)) (pairWords (un k))
    (List.ofFn z.1 ++ List.ofFn z.2) =
   mask (Math.support k crown z) := by
 unfold supportMask
 rw [mapRange_eq]
 ·
  rw [pairCount_length]
  exact range_flatMap_get_map (pairs k) (fun e => decide (e ∈ Math.support k crown z)) _
   (fun i hi => supportEdgeBit_eq z i hi)
 ·
  intro i hi
  rw [pairCount_length] at hi
  rw [supportEdgeBit_eq z i hi]
  rfl
def hardBadStep (s : List Bool) : List Bool :=
 let i := left s
 let a := left (right s)
 let crownF := field 0 a
 let kU := field 1 a
 let nrU := field 2 a
 let bankLenU := field 3 a
 let hardStream := field 4 a
 let acc := right (right s)
 orFlag acc (baseHitFlag crownF kU nrU (slot bankLenU i hardStream))
lemma cpHardBadStep : CPTs hardBadStep := by
 have hi := cpLeft cpt_id
 have ha := cpLeft (cpRight cpt_id)
 exact cpOrFlag (cpRight (cpRight cpt_id))
  (cpBaseHitFlag (cpField 0 ha) (cpField 1 ha) (cpField 2 ha)
   (cpSlot (cpField 3 ha) hi (cpField 4 ha)))
def hardBadFlag (crownF kU nrU bankLenU hardLenU hardStream : List Bool) : List Bool :=
 runIndexed replaceBound hardBadStep [true] hardLenU
  (pack [crownF, kU, nrU, bankLenU, hardStream]) []
lemma cpHardBadFlag {crownF kU nrU bankLenU hardLenU hardStream : List Bool → List Bool}
  (hc : CPTs crownF) (hk : CPTs kU) (hnr : CPTs nrU)
  (hbl : CPTs bankLenU) (hhl : CPTs hardLenU) (hhs : CPTs hardStream) :
  CPTs (fun s => hardBadFlag (crownF s) (kU s) (nrU s) (bankLenU s) (hardLenU s) (hardStream s)) :=
 cpRunIndexed replaceBound_cpt replaceBound_length cpHardBadStep (cpt_const [true]) hhl
  (cpt_pairB2 hc (cpt_pairB2 hk (cpt_pairB2 hnr (cpt_pairB2 hbl (cpt_pairB2 hhs (cpt_const []))))))
  (cpt_const [])
lemma hardBadFlag_eq {k : ℕ} {crown : Bool}
  (hard : List ((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool))) :
  hardBadFlag (bflag crown) (un k) (un (Math.nr k crown))
    (un (Math.nr k crown + Math.nc k crown)) (un hard.length)
    (hard.flatMap (fun z => List.ofFn z.1 ++ List.ofFn z.2)) =
   bflag (Math.hardBad k crown hard) := by
 unfold hardBadFlag
 let banks := fun z : (Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool) =>
  List.ofFn z.1 ++ List.ofFn z.2
 have hbanks : ∀ z ∈ hard, (banks z).length = (un (Math.nr k crown + Math.nc k crown)).length := by
  intro z _; simp [banks]
 have h := runIndexed_ofListFold replaceBound hardBadStep [true] (un hard.length)
  (pack [bflag crown, un k, un (Math.nr k crown), un (Math.nr k crown + Math.nc k crown), hard.flatMap banks])
  [] (fun l b => l = bflag b)
  (fun i b => b || (hard[i]?.elim false (Math.baseHit k crown)))
  false rfl (fun i hi x b hx => by
   subst hx
   rw [un_length] at hi
   simp only [hardBadStep, left, right, unpairB_pairB, field_pack_zero, field_pack_succ,
    replaceBound, List.length_singleton]
   rw [slot_flatMap hard banks _ i hi hbanks, baseHitFlag_eq, orFlag_bflag, bflag_take_one]
   simp [List.getElem?_eq_getElem hi, Bool.or_comm])
 rw [un_length] at h
 have hfold : ∀ (L : List ((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool))) (b₀ : Bool),
   (List.range L.length).foldr
    (fun i b => b || (L[i]?.elim false (Math.baseHit k crown))) b₀ =
    (b₀ || L.any (Math.baseHit k crown)) := by
  intro L
  induction L with
  | nil => intro b₀; simp
  | cons a L ih =>
   intro b₀
   rw [List.length_cons, List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
   simp only [List.getElem?_cons_zero, Option.elim_some, List.any_cons, List.getElem?_cons_succ]
   rw [ih]
   cases b₀ <;> cases Math.baseHit k crown a <;> simp
 rw [hfold hard false, Bool.false_or] at h
 exact h
def edgeForbiddenStep (s : List Bool) : List Bool :=
 let i := left s
 let a := left (right s)
 let acc := right (right s)
 let kU := field 0 a
 let nrU := field 1 a
 let bankLenU := field 2 a
 let hardStream := field 3 a
 let u := field 4 a
 let v := field 5 a
 let bank := slot bankLenU i hardStream
 let hit := orFlag (andFlag (bitFlagAt u bank) (bitFlagAt v bank))
  (andFlag (bitFlagAt (nrU ++ u) bank) (bitFlagAt (nrU ++ v) bank))
 orFlag acc hit
lemma cpEdgeForbiddenStep : CPTs edgeForbiddenStep := by
 have hi := cpLeft cpt_id
 have ha := cpLeft (cpRight cpt_id)
 have hnr := cpField 1 ha
 have hbank := cpSlot (cpField 2 ha) hi (cpField 3 ha)
 have hu := cpField 4 ha
 have hv := cpField 5 ha
 exact cpOrFlag (cpRight (cpRight cpt_id))
  (cpOrFlag (cpAndFlag (cpBitFlagAt hu hbank) (cpBitFlagAt hv hbank))
   (cpAndFlag (cpBitFlagAt (cpt_app2 hnr hu) hbank) (cpBitFlagAt (cpt_app2 hnr hv) hbank)))
def allowedEdgeBit (s : List Bool) : List Bool :=
 let p := left s
 let a := right s
 let kU := field 0 a
 let nrU := field 1 a
 let bankLenU := field 2 a
 let hardLenU := field 3 a
 let hardStream := field 4 a
 let pw := field 5 a
 let word := slot (kU ++ kU) p pw
 let u := hd (word.take kU.length)
 let v := hd (word.drop kU.length)
 q16 (notFlag (runIndexed replaceBound edgeForbiddenStep [true] hardLenU
  (pack [kU, nrU, bankLenU, hardStream, u, v]) []))
lemma cpAllowedEdgeBit : CPTs allowedEdgeBit := by
 have hp := cpLeft cpt_id
 have ha := cpRight cpt_id
 have hk := cpField 0 ha
 have hnr := cpField 1 ha
 have hbl := cpField 2 ha
 have hhl := cpField 3 ha
 have hhs := cpField 4 ha
 have hpw := cpField 5 ha
 have hw := cpSlot (cpt_app2 hk hk) hp hpw
 have hu := cpt_comp (cpTake hk hw) cpt_hd
 have hv := cpt_comp (cpDrop hk hw) cpt_hd
 exact q73 (cpNotFlag (cpRunIndexed replaceBound_cpt replaceBound_length cpEdgeForbiddenStep
  (cpt_const [true]) hhl
  (cpt_pairB2 hk (cpt_pairB2 hnr (cpt_pairB2 hbl (cpt_pairB2 hhs (cpt_pairB2 hu (cpt_pairB2 hv (cpt_const [])))))))
  (cpt_const [])))
def allowedMask (kU nrU bankLenU hardLenU hardStream pCount pw : List Bool) : List Bool :=
 mapRange allowedEdgeBit [true] pCount (pack [kU, nrU, bankLenU, hardLenU, hardStream, pw])
lemma cpAllowedMask {kU nrU bankLenU hardLenU hardStream pCount pw : List Bool → List Bool}
  (hk : CPTs kU) (hnr : CPTs nrU) (hbl : CPTs bankLenU) (hhl : CPTs hardLenU)
  (hhs : CPTs hardStream) (hp : CPTs pCount) (hpw : CPTs pw) :
  CPTs (fun s => allowedMask (kU s) (nrU s) (bankLenU s) (hardLenU s) (hardStream s) (pCount s) (pw s)) :=
 cpMapRange cpAllowedEdgeBit (cpt_const [true]) hp
  (cpt_pairB2 hk (cpt_pairB2 hnr (cpt_pairB2 hbl (cpt_pairB2 hhl (cpt_pairB2 hhs (cpt_pairB2 hpw (cpt_const [])))))))
lemma allowedEdgeBit_eq {k : ℕ} {crown : Bool}
  (hard : List ((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool)))
  (p : ℕ) (hp : p < (pairs k).length) :
  allowedEdgeBit (pairB (un p) (pack [un k, un (Math.nr k crown),
    un (Math.nr k crown + Math.nc k crown), un hard.length,
    hard.flatMap (fun z => List.ofFn z.1 ++ List.ofFn z.2), pairWords (un k)])) =
   [decide ((pairs k)[p] ∈ Math.allowedEdges k crown hard)] := by
 let banks := fun z : (Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool) =>
  List.ofFn z.1 ++ List.ofFn z.2
 have hbanks : ∀ z ∈ hard, (banks z).length = (un (Math.nr k crown + Math.nc k crown)).length := by
  intro z _; simp [banks]
 have hpw := pairWords_get k p hp
 simp only [allowedEdgeBit, field_left_pair, field_right_pair, field_pack_zero, field_pack_succ,
  un_length]
 rw [hpw.1, hpw.2]
 let e := (pairs k)[p]
 have hemem : e ∈ (pairs k).toFinset := List.mem_toFinset.mpr (List.getElem_mem hp)
 have hrun := runIndexed_ofListFold replaceBound edgeForbiddenStep [true] (un hard.length)
  (pack [un k, un (Math.nr k crown), un (Math.nr k crown + Math.nc k crown),
   hard.flatMap banks, un e.1.val, un e.2.val])
  [] (fun l b => l = bflag b)
  (fun i b => b || (hard[i]?.elim false (fun h => decide (e ∈ Math.support k crown h))))
  false rfl (fun i hi x b hx => by
   subst hx
   rw [un_length] at hi
   simp only [edgeForbiddenStep, left, right, unpairB_pairB, field_pack_zero, field_pack_succ,
    replaceBound, List.length_singleton]
   rw [slot_flatMap hard banks _ i hi hbanks]
   simp only [bitFlagAt_eq, un_length, List.length_append, andFlag_bflag, orFlag_bflag, bflag_take_one]
   congr 1
   simp [List.getElem?_eq_getElem hi, e, Math.support, Math.wire, banks, hemem, Bool.or_comm])
 rw [un_length] at hrun
 have hfold : ∀ (L : List ((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool))) (b₀ : Bool),
   (List.range L.length).foldr
    (fun i b => b || (L[i]?.elim false (fun h => decide (e ∈ Math.support k crown h)))) b₀ =
    (b₀ || !(L.all (fun h => !decide (e ∈ Math.support k crown h)))) := by
  intro L
  induction L with
  | nil => intro b₀; simp
  | cons a L ih =>
   intro b₀
   rw [List.length_cons, List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
   simp only [List.getElem?_cons_zero, Option.elim_some, List.all_cons, Bool.not_and,
    Bool.not_not, List.getElem?_cons_succ]
   rw [ih]
   cases b₀ <;> cases decide (e ∈ Math.support k crown a) <;> simp
 rw [hfold hard false, Bool.false_or] at hrun
 rw [hrun, notFlag_bflag, Bool.not_not, q16_bflag]
 rw [show (pairs k)[p] = e from rfl]
 congr 1
 simp only [Math.allowedEdges, Finset.mem_filter, hemem, true_and]
 exact (Bool.decide_eq_true).symm
lemma allowedMask_eq {k : ℕ} {crown : Bool}
  (hard : List ((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool))) :
  allowedMask (un k) (un (Math.nr k crown)) (un (Math.nr k crown + Math.nc k crown))
    (un hard.length) (hard.flatMap (fun z => List.ofFn z.1 ++ List.ofFn z.2))
    (pairCount (un k)) (pairWords (un k)) =
   mask (Math.allowedEdges k crown hard) := by
 unfold allowedMask
 rw [mapRange_eq]
 ·
  rw [pairCount_length]
  exact range_flatMap_get_map (pairs k) (fun e => decide (e ∈ Math.allowedEdges k crown hard)) _
   (fun p hp => allowedEdgeBit_eq hard p hp)
 ·
  intro p hp
  rw [pairCount_length] at hp
  rw [allowedEdgeBit_eq hard p hp]
  rfl
def buildRowItem (s : List Bool) : List Bool :=
 let i := left s
 let a := right s
 let crownF := field 0 a
 let kU := field 1 a
 let nrU := field 2 a
 let bankLenU := field 3 a
 let pCount := field 4 a
 let pw := field 5 a
 let softStream := field 6 a
 let entry := slot (bankLenU ++ [true]) i softStream
 let bank := entry.take bankLenU.length
 let t2 := bitFlagAt bankLenU entry
 let forced := baseHitFlag crownF kU nrU bank
 let signBit := q16 (sel crownF (notFlag t2) t2)
 sel forced (signBit ++ supportMask kU nrU pCount pw bank) (false :: blank pCount)
lemma cpBuildRowItem : CPTs buildRowItem := by
 have hi := cpLeft cpt_id
 have ha := cpRight cpt_id
 have hc := cpField 0 ha
 have hk := cpField 1 ha
 have hnr := cpField 2 ha
 have hbl := cpField 3 ha
 have hp := cpField 4 ha
 have hpw := cpField 5 ha
 have hss := cpField 6 ha
 have hent := cpSlot (cpt_app2 hbl (cpt_const [true])) hi hss
 have hbank := cpTake hbl hent
 have ht2 := cpBitFlagAt hbl hent
 have hforced := cpBaseHitFlag hc hk hnr hbank
 have hsign := q73 (cpt_sel hc (cpNotFlag ht2) ht2)
 exact cpt_sel hforced (cpt_app2 hsign (cpSupportMask hk hnr hp hpw hbank))
  (cpCons false (cpt_comp hp cpt_blank))
def buildRows (crownF kU nrU bankLenU pCount pw softLenU softStream : List Bool) : List Bool :=
 mapRange buildRowItem (true :: pCount) softLenU
  (pack [crownF, kU, nrU, bankLenU, pCount, pw, softStream])
lemma cpBuildRows {crownF kU nrU bankLenU pCount pw softLenU softStream : List Bool → List Bool}
  (hc : CPTs crownF) (hk : CPTs kU) (hnr : CPTs nrU) (hbl : CPTs bankLenU)
  (hp : CPTs pCount) (hpw : CPTs pw) (hsl : CPTs softLenU) (hss : CPTs softStream) :
  CPTs (fun s => buildRows (crownF s) (kU s) (nrU s) (bankLenU s) (pCount s) (pw s) (softLenU s) (softStream s)) :=
 cpMapRange cpBuildRowItem (cpCons true hp) hsl
  (cpt_pairB2 hc (cpt_pairB2 hk (cpt_pairB2 hnr (cpt_pairB2 hbl (cpt_pairB2 hp (cpt_pairB2 hpw (cpt_pairB2 hss (cpt_const []))))))))
lemma blank_getElem (l : List Bool) (j : ℕ) (hj : j < (blank l).length) :
  (blank l)[j] = false := by
 induction l generalizing j with
 | nil => simp [blank] at hj
 | cons _ r ih =>
  cases j with
  | zero => rfl
  | succ j => exact ih j (by simpa [blank] using hj)
lemma buildRowItem_eq {k : ℕ} {crown : Bool}
  (soft : List (((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool)) × Bool))
  (i : ℕ) (hi : i < soft.length) :
  buildRowItem (pairB (un i) (pack [bflag crown, un k, un (Math.nr k crown),
    un (Math.nr k crown + Math.nc k crown), pairCount (un k), pairWords (un k),
    soft.flatMap (fun t => (List.ofFn t.1.1 ++ List.ofFn t.1.2) ++ [t.2])])) =
   rowBits ((Math.paddedRows k crown soft)[i]'(Math.paddedRows_length k crown soft ▸ hi)) := by
 let enc := fun t : ((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool)) × Bool =>
  (List.ofFn t.1.1 ++ List.ofFn t.1.2) ++ [t.2]
 have henc : ∀ t ∈ soft, (enc t).length = (un (Math.nr k crown + Math.nc k crown) ++ [true]).length := by
  intro t _; simp [enc]; omega
 simp only [buildRowItem, field_left_pair, field_right_pair, field_pack_zero, field_pack_succ]
 rw [slot_flatMap soft enc _ i hi henc]
 let t := soft[i]
 let b := List.ofFn t.1.1 ++ List.ofFn t.1.2
 have hbLen : b.length = Math.nr k crown + Math.nc k crown := by simp [b]
 have htake : (b ++ [t.2]).take (un (Math.nr k crown + Math.nc k crown)).length = b := by
  rw [un_length, ← hbLen, List.take_left]
 have ht2 : bitFlagAt (un (Math.nr k crown + Math.nc k crown)) (b ++ [t.2]) = bflag t.2 := by
  rw [bitFlagAt_eq, un_length, ← hbLen]
  simp
 rw [htake, ht2, baseHitFlag_eq t.1]
 have hsign : q16 (sel (bflag crown) (notFlag (bflag t.2)) (bflag t.2)) = [t.2 == crown] := by
  cases crown <;> cases t.2 <;> rfl
 rw [hsign, supportMask_eq t.1]
 simp only [Math.paddedRows, List.getElem_map]
 cases hb : Math.baseHit k crown t.1
 · simp [bflag, sel, rowBits, t, b]
 ·
  simp only [bflag, sel, List.cons_ne_nil, ↓reduceIte, rowBits]
  congr 1
  have hemp : mask (∅ : Finset (Edge k)) = blank (pairCount (un k)) := by
   apply List.ext_getElem
   · simp [mask_length, pairCount_length, q33]
   ·
    intro j hj _
    simp only [mask, List.getElem_map, Finset.notMem_empty, decide_false]
    rw [blank_getElem]
  exact hemp.symm
lemma buildRows_eq {k : ℕ} {crown : Bool}
  (soft : List (((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool)) × Bool)) :
  buildRows (bflag crown) (un k) (un (Math.nr k crown))
    (un (Math.nr k crown + Math.nc k crown)) (pairCount (un k)) (pairWords (un k))
    (un soft.length) (soft.flatMap (fun t => (List.ofFn t.1.1 ++ List.ofFn t.1.2) ++ [t.2])) =
   (Math.paddedRows k crown soft).flatMap rowBits := by
 unfold buildRows
 rw [mapRange_eq]
 ·
  rw [un_length, ← Math.paddedRows_length k crown soft]
  exact range_flatMap_get_list (Math.paddedRows k crown soft) rowBits _ (fun i hi => by
   rw [Math.paddedRows_length] at hi
   exact buildRowItem_eq soft i hi)
 ·
  intro i hi
  rw [un_length] at hi
  rw [buildRowItem_eq soft i hi]
  simp [rowBits, mask_length, pairCount_length]
def testSizePos (w capB sU kU pCount softLenU E_mask pw rowsStream : List Bool) : List Bool :=
 let d2 := sU ++ sU
 let b := powerTwo capB d2
 q141 (aggregate (pack [w, d2, b, kU, pCount, softLenU, E_mask, pw, rowsStream]))
lemma cpTestSizePos {w capB sU kU pCount softLenU E_mask pw rowsStream : List Bool → List Bool}
  (hw : CPTs w) (hc : CPTs capB) (hs : CPTs sU) (hk : CPTs kU) (hp : CPTs pCount)
  (hsl : CPTs softLenU) (hE : CPTs E_mask) (hpw : CPTs pw) (hr : CPTs rowsStream) :
  CPTs (fun s => testSizePos (w s) (capB s) (sU s) (kU s) (pCount s) (softLenU s) (E_mask s) (pw s) (rowsStream s)) := by
 have hd2 : CPTs (fun s => sU s ++ sU s) := cpt_app2 hs hs
 have hb : CPTs (fun s => powerTwo (capB s) (sU s ++ sU s)) := powerTwo_cpt hc hd2
 have hargs : CPTs (fun s => pack [w s, sU s ++ sU s, powerTwo (capB s) (sU s ++ sU s),
   kU s, pCount s, softLenU s, E_mask s, pw s, rowsStream s]) :=
  cpt_pairB2 hw (cpt_pairB2 hd2 (cpt_pairB2 hb (cpt_pairB2 hk (cpt_pairB2 hp
   (cpt_pairB2 hsl (cpt_pairB2 hE (cpt_pairB2 hpw (cpt_pairB2 hr (cpt_const [])))))))))
 have hagg : CPTs (fun s => aggregate (pack [w s, sU s ++ sU s, powerTwo (capB s) (sU s ++ sU s),
   kU s, pCount s, softLenU s, E_mask s, pw s, rowsStream s])) :=
  cpt_comp hargs cpAggregate
 unfold testSizePos
 dsimp only
 exact cpt_comp hagg q167
lemma testSizePos_core {k s_size : ℕ} (w capB : List Bool) {E : Finset (Edge k)}
  (rows : List (Row k)) (hE : ∀ e ∈ E, e.1 < e.2)
  (hw : w.length = width k rows.length)
  (hcap : 2 ^ (un s_size ++ un s_size).length ≤ capB.length) :
  testSizePos w capB (un s_size) (un k) (pairCount (un k)) (un rows.length)
    (mask E) (pairWords (un k)) (rows.flatMap rowBits) =
   (total E s_size rows).bits := by
 have h2s : un s_size ++ un s_size = un (2 * s_size) := by
  dsimp only [un]; rw [two_mul, List.replicate_add]
 have hpw := powerTwo_eq capB (un s_size ++ un s_size) hcap
 rw [h2s, un_length] at hpw
 simp only [testSizePos, h2s, hpw, q109]
 apply congrArg Nat.bits
 have hva : pack [w, un (2 * s_size), un (2 ^ (2 * s_size)), un k, pairCount (un k),
   un rows.length, mask E, pairWords (un k), rows.flatMap rowBits] =
   validArgs (k := s_size) w E rows := by
  unfold validArgs
  rfl
 rw [hva]
 apply val_eq_of_rep (w := w)
 · simp only [aggregate, sumRange_length, validArgs, field_pack_zero]
 · exact aggregate_rep w E rows hE
 · rw [hw]; exact total_lt E rows
lemma testSizePos_eq {k d s_size : ℕ} {crown : Bool}
    (soft : List (((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool)) × Bool))
    (hsoft : 0 < soft.length) (hs : s_size ≤ d + 1 + soft.length.log2)
    {E : Finset (Edge k)} (hE : ∀ e ∈ E, e.1 < e.2) :
    let w := widthCode (un k) (un soft.length)
    let capB := mulU (mulU (un (2 ^ (d + 1))) (un (2 ^ (d + 1)))) (mulU (un soft.length) (un soft.length))
    testSizePos w capB (un s_size) (un k) (pairCount (un k)) (un soft.length)
        (mask E) (pairWords (un k)) ((Math.paddedRows k crown soft).flatMap rowBits) =
      (total E s_size (Math.paddedRows k crown soft)).bits := by
  intro w capB
  have hcap : 2 ^ (un s_size ++ un s_size).length ≤ capB.length := by
    simp only [List.length_append, un_length, capB, mulU]
    have hlog : 2 ^ soft.length.log2 ≤ soft.length :=
      (Nat.le_log2 (Nat.ne_of_gt hsoft)).mp (le_refl _)
    have hpow : 2 ^ (s_size + s_size) ≤ 2 ^ (2 * (d + 1) + 2 * soft.length.log2) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    calc 2 ^ (s_size + s_size) ≤ 2 ^ (2 * (d + 1) + 2 * soft.length.log2) := hpow
      _ = (2 ^ (d + 1) * 2 ^ (d + 1)) * (2 ^ soft.length.log2 * 2 ^ soft.length.log2) := by
          rw [pow_add, two_mul (d + 1), two_mul soft.length.log2,
            pow_add 2 (d + 1) (d + 1), pow_add 2 soft.length.log2 soft.length.log2]
      _ ≤ (2 ^ (d + 1) * 2 ^ (d + 1)) * (soft.length * soft.length) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hlog hlog)
  have hlen_soft : soft.length = (Math.paddedRows k crown soft).length :=
    (Math.paddedRows_length k crown soft).symm
  rw [hlen_soft]
  exact testSizePos_core w capB (Math.paddedRows k crown soft) hE
    (by rw [← hlen_soft]; exact widthCode_length k soft.length) hcap
lemma bits_eq_nil_iff (n : ℕ) : n.bits = [] ↔ n = 0 := by
 cases n with
 | zero => simp
 | succ n =>
  have h := q175 (n + 1) (Nat.succ_pos n)
  constructor
  · intro heq; rw [heq] at h; simp at h
  · intro h0; omega
def scanSizeStep (s : List Bool) : List Bool :=
 let i := left s
 let a := left (right s)
 let acc := right (right s)
 let w := field 0 a
 let capB := field 1 a
 let dU := field 2 a
 let kU := field 3 a
 let pCount := field 4 a
 let softLenU := field 5 a
 let E_mask := field 6 a
 let pw := field 7 a
 let rowsStream := field 8 a
 sel (testSizePos w capB (dU ++ [true] ++ i) kU pCount softLenU E_mask pw rowsStream) acc (true :: i)
lemma cpScanSizeStep : CPTs scanSizeStep := by
 have hi := cpLeft cpt_id
 have ha := cpLeft (cpRight cpt_id)
 have hacc := cpRight (cpRight cpt_id)
 have ht := cpTestSizePos (cpField 0 ha) (cpField 1 ha)
  (cpt_app2 (cpt_app2 (cpField 2 ha) (cpt_const [true])) hi)
  (cpField 3 ha) (cpField 4 ha) (cpField 5 ha) (cpField 6 ha) (cpField 7 ha) (cpField 8 ha)
 exact cpt_sel ht hacc (cpCons true hi)
def scanSize (w capB dU kU pCount softLenU logSoftU E_mask pw rowsStream : List Bool) : List Bool :=
 runIndexed replaceBound scanSizeStep (true :: logSoftU) (true :: logSoftU)
  (pack [w, capB, dU, kU, pCount, softLenU, E_mask, pw, rowsStream]) []
lemma cpScanSize {w capB dU kU pCount softLenU logSoftU E_mask pw rowsStream : List Bool → List Bool}
  (hw : CPTs w) (hc : CPTs capB) (hd : CPTs dU) (hk : CPTs kU) (hp : CPTs pCount)
  (hsl : CPTs softLenU) (hls : CPTs logSoftU) (hE : CPTs E_mask) (hpw : CPTs pw) (hr : CPTs rowsStream) :
  CPTs (fun s => scanSize (w s) (capB s) (dU s) (kU s) (pCount s) (softLenU s)
   (logSoftU s) (E_mask s) (pw s) (rowsStream s)) :=
 cpRunIndexed replaceBound_cpt replaceBound_length cpScanSizeStep
  (cpCons true hls) (cpCons true hls)
  (cpt_pairB2 hw (cpt_pairB2 hc (cpt_pairB2 hd (cpt_pairB2 hk (cpt_pairB2 hp (cpt_pairB2 hsl (cpt_pairB2 hE (cpt_pairB2 hpw (cpt_pairB2 hr (cpt_const []))))))))))
  (cpt_const [])
lemma foldr_min_scan (P : ℕ → Bool) (f : ℕ → List Bool) (n : ℕ) :
  (List.range n).foldr (fun i acc => if P i then f i else acc) [] = [] ∧
   (∀ i < n, P i = false) ∨
  ∃ i₀ < n, P i₀ = true ∧ (∀ j < i₀, P j = false) ∧
   (List.range n).foldr (fun i acc => if P i then f i else acc) [] = f i₀ := by
 induction n generalizing P f with
 | zero => left; exact ⟨rfl, fun i hi => by simp at hi⟩
 | succ n ih =>
  rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
  simp only [Nat.succ_eq_add_one]
  cases h0 : P 0
  ·
   simp only [Bool.false_eq_true, ↓reduceIte]
   rcases ih (fun i => P (i + 1)) (fun i => f (i + 1)) with ⟨heq, hfalse⟩ | ⟨i₀, hi0, hp0, hmin0, heq⟩
   ·
    left
    refine ⟨heq, fun i hi => ?_⟩
    cases i with
    | zero => exact h0
    | succ i => exact hfalse i (Nat.succ_lt_succ_iff.mp hi)
   ·
    right
    refine ⟨i₀ + 1, Nat.succ_lt_succ hi0, hp0, fun j hj => ?_, heq⟩
    cases j with
    | zero => exact h0
    | succ j => exact hmin0 j (Nat.succ_lt_succ_iff.mp hj)
  ·
   simp only [↓reduceIte]
   right
   exact ⟨0, Nat.zero_lt_succ n, h0, fun j hj => by simp at hj, rfl⟩
lemma scanSize_eq {k d : ℕ} {crown : Bool}
  (soft : List (((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool)) × Bool))
  (hsoft : 0 < soft.length)
  {E : Finset (Edge k)} (hE : ∀ e ∈ E, e.1 < e.2) :
  let w := widthCode (un k) (un soft.length)
  let capB := mulU (mulU (un (2 ^ (d + 1))) (un (2 ^ (d + 1)))) (mulU (un soft.length) (un soft.length))
  let logSoftU := (q48 (un soft.length)).tail
  let rowsStream := (Math.paddedRows k crown soft).flatMap rowBits
  let res := scanSize w capB (un d) (un k) (pairCount (un k)) (un soft.length) logSoftU (mask E) (pairWords (un k)) rowsStream
  (res = [] ∧ ∀ s, d < s → s ≤ d + 1 + soft.length.log2 → total E s (Math.paddedRows k crown soft) = 0) ∨
  ∃ i₀ ≤ soft.length.log2,
   res = true :: un i₀ ∧
   0 < total E (d + 1 + i₀) (Math.paddedRows k crown soft) ∧
   ∀ s, d < s → s < d + 1 + i₀ → total E s (Math.paddedRows k crown soft) = 0 := by
 intro w capB logSoftU rowsStream res
 have hlogLen : (true :: logSoftU).length = soft.length.log2 + 1 := by
  simp only [logSoftU, q71, un_length, List.length_cons]
  have hq := q175 soft.length hsoft
  cases hbits : soft.length.bits with
  | nil => rw [hbits] at hq; simp at hq
  | cons b bs => rw [hbits] at hq; simp [List.tail_cons] at hq ⊢; omega
 let P : ℕ → Bool := fun i => decide (0 < total E (d + 1 + i) (Math.paddedRows k crown soft))
 let step : ℕ → List Bool → List Bool := fun i acc => if P i then true :: un i else acc
 have hrun := runIndexed_ofListFold replaceBound scanSizeStep (true :: logSoftU) (true :: logSoftU)
  (pack [w, capB, un d, un k, pairCount (un k), un soft.length, mask E, pairWords (un k), rowsStream])
  [] (fun l r => l = r ∧ l.length ≤ soft.length.log2 + 1) step [] ⟨rfl, by simp⟩
  (fun i hi x a hx => by
   rw [hlogLen] at hi
   rcases hx with ⟨rfl, hlen⟩
   simp only [scanSizeStep, left, right, unpairB_pairB, field_pack_zero, field_pack_succ, replaceBound]
   have hs : d + 1 + i ≤ d + 1 + soft.length.log2 := by omega
   have hcat : un d ++ [true] ++ un i = un (d + 1 + i) := by
    dsimp only [un]
    rw [List.append_assoc, List.singleton_append, ← List.replicate_succ, ← List.replicate_add]
    rw [show d + (i + 1) = d + 1 + i by omega]
   rw [hcat, testSizePos_eq soft hsoft hs hE]
   by_cases hpos : 0 < total E (d + 1 + i) (Math.paddedRows k crown soft)
   ·
    have hne : (total E (d + 1 + i) (Math.paddedRows k crown soft)).bits ≠ [] := by
     rw [ne_eq, bits_eq_nil_iff]; omega
    simp only [sel, hne, ↓reduceIte, step, P, hpos, decide_true]
    rw [List.take_of_length_le (by simp [hlogLen]; omega)]
    exact ⟨rfl, by simp; omega⟩
   ·
    have heq : (total E (d + 1 + i) (Math.paddedRows k crown soft)).bits = [] := by
     rw [bits_eq_nil_iff]; omega
    simp only [sel, heq, ↓reduceIte, step, P, hpos, decide_false, Bool.false_eq_true]
    rw [List.take_of_length_le (by rw [hlogLen]; exact hlen)]
    exact ⟨rfl, hlen⟩)
 rw [hlogLen] at hrun
 have hres : res = (List.range (soft.length.log2 + 1)).foldr step [] := hrun.1
 rcases foldr_min_scan P (fun i => true :: un i) (soft.length.log2 + 1) with ⟨hnil, hall⟩ | ⟨i₀, hi0, hp0, hmin0, heq⟩
 ·
  left
  refine ⟨hres.trans hnil, fun s hs1 hs2 => ?_⟩
  have hlt : s - (d + 1) < soft.length.log2 + 1 := by omega
  have hf := hall (s - (d + 1)) hlt
  simp only [P, show d + 1 + (s - (d + 1)) = s by omega, decide_eq_false_iff_not, not_lt, Nat.le_zero] at hf
  exact hf
 ·
  right
  refine ⟨i₀, by omega, hres.trans heq, ?_, fun s hs1 hs2 => ?_⟩
  · simpa [P] using hp0
  ·
   have hf := hmin0 (s - (d + 1)) (by omega)
   simp only [P, show d + 1 + (s - (d + 1)) = s by omega, decide_eq_false_iff_not, not_lt, Nat.le_zero] at hf
   exact hf
def clearBitAt (p E : List Bool) : List Bool :=
 E.take p.length ++ [false] ++ E.drop (p.length + 1)
lemma cpClearBitAt {p E : List Bool → List Bool} (hp : CPTs p) (hE : CPTs E) :
  CPTs (fun s => clearBitAt (p s) (E s)) :=
 cpt_app2 (cpt_app2 (cpTake hp hE) (cpt_const [false])) (cpDrop (cpCons true hp) hE)
lemma clearBitAt_mask {k : ℕ} (S : Finset (Edge k)) (p : ℕ) (hp : p < (pairs k).length) :
  clearBitAt (un p) (mask S) = mask (S.erase (pairs k)[p]) := by
 unfold clearBitAt
 rw [un_length]
 apply List.ext_getElem
 · simp [mask_length]; omega
 ·
  intro j hj1 hj2
  rw [mask_length] at hj2
  by_cases hjp : j < p
  ·
   have htake : j < ((mask S).take p).length := by
    rw [List.length_take, mask_length, Nat.min_eq_left hp.le]; exact hjp
   rw [List.getElem_append_left (by rw [List.length_append, List.length_singleton, List.length_take, mask_length, Nat.min_eq_left hp.le]; omega),
    List.getElem_append_left htake, List.getElem_take]
   simp only [mask, List.getElem_map]
   have hne : (pairs k)[j] ≠ (pairs k)[p] :=
    fun he => absurd (congrArg Fin.val ((pairs_nodup k).get_inj_iff.mp he)) (by dsimp; omega)
   simp [hne]
  ·
   by_cases heq : j = p
   ·
    subst heq
    have hlen : ((mask S).take j).length = j := by
     rw [List.length_take, mask_length, Nat.min_eq_left hp.le]
    rw [List.getElem_append_left (by rw [List.length_append, List.length_singleton, hlen]; omega),
     List.getElem_append_right (by rw [hlen])]
    simp [mask]
   ·
    have hgt : p + 1 ≤ j := by omega
    have hlen : (((mask S).take p) ++ [false]).length = p + 1 := by
     rw [List.length_append, List.length_singleton, List.length_take, mask_length, Nat.min_eq_left hp.le]
    rw [List.getElem_append_right (by rw [hlen]; omega), List.getElem_drop]
    have hidx : p + 1 + (j - (List.take p (mask S) ++ [false]).length) = j := by rw [hlen]; omega
    simp only [mask, List.getElem_map]
    have hidx' : p + 1 + (j - (List.take p (List.map (fun e => decide (e ∈ S)) (pairs k)) ++ [false]).length) = j := hidx
    have hmem : (pairs k)[p + 1 + (j - (List.take p (List.map (fun e => decide (e ∈ S)) (pairs k)) ++ [false]).length)] =
      (pairs k)[j] := by congr 1
    rw [hmem]
    have hne : (pairs k)[j] ≠ (pairs k)[p] :=
     fun he => absurd (congrArg Fin.val ((pairs_nodup k).get_inj_iff.mp he)) (by dsimp; omega)
    simp [hne]
def deleteEdgeStep (s : List Bool) : List Bool :=
 let p := left s
 let a := left (right s)
 let E_cur := right (right s)
 let w := field 0 a
 let capB := field 1 a
 let s0U := field 2 a
 let kU := field 3 a
 let pCount := field 4 a
 let softLenU := field 5 a
 let pw := field 6 a
 let rowsStream := field 7 a
 let E_try := clearBitAt p E_cur
 sel (bitFlagAt p E_cur) E_cur
  (sel (testSizePos w capB s0U kU pCount softLenU E_try pw rowsStream) E_cur E_try)
lemma cpDeleteEdgeStep : CPTs deleteEdgeStep := by
 have hp := cpLeft cpt_id
 have ha := cpLeft (cpRight cpt_id)
 have hE := cpRight (cpRight cpt_id)
 have htry := cpClearBitAt hp hE
 have ht := cpTestSizePos (cpField 0 ha) (cpField 1 ha) (cpField 2 ha) (cpField 3 ha)
  (cpField 4 ha) (cpField 5 ha) htry (cpField 6 ha) (cpField 7 ha)
 exact cpt_sel (cpBitFlagAt hp hE) hE (cpt_sel ht hE htry)
def deleteEdges (w capB s0U kU pCount softLenU pw rowsStream E_mask : List Bool) : List Bool :=
 runIndexed replaceBound deleteEdgeStep pCount pCount
  (pack [w, capB, s0U, kU, pCount, softLenU, pw, rowsStream]) E_mask
lemma cpDeleteEdges {w capB s0U kU pCount softLenU pw rowsStream E_mask : List Bool → List Bool}
  (hw : CPTs w) (hc : CPTs capB) (hs : CPTs s0U) (hk : CPTs kU) (hp : CPTs pCount)
  (hsl : CPTs softLenU) (hpw : CPTs pw) (hr : CPTs rowsStream) (hE : CPTs E_mask) :
  CPTs (fun s => deleteEdges (w s) (capB s) (s0U s) (kU s) (pCount s) (softLenU s)
   (pw s) (rowsStream s) (E_mask s)) :=
 cpRunIndexed replaceBound_cpt replaceBound_length cpDeleteEdgeStep hp hp
  (cpt_pairB2 hw (cpt_pairB2 hc (cpt_pairB2 hs (cpt_pairB2 hk (cpt_pairB2 hp (cpt_pairB2 hsl (cpt_pairB2 hpw (cpt_pairB2 hr (cpt_const [])))))))))
  hE
lemma total_mono {k s : ℕ} {A B : Finset (Edge k)} (hAB : A ⊆ B) (rows : List (Row k)) :
  total A s rows ≤ total B s rows := by
 unfold total
 apply Finset.sum_le_sum_of_subset
 intro Q hQ
 simp only [choices, Finset.mem_filter, Finset.mem_powerset] at hQ ⊢
 exact ⟨hQ.1.trans hAB, hQ.2⟩
lemma foldr_delete_inv {k s₀ : ℕ} (rows : List (Row k)) (L : List ℕ)
  (hL : ∀ p ∈ L, p < (pairs k).length) (S₀ : Finset (Edge k)) (hpos : 0 < total S₀ s₀ rows) :
  let step : ℕ → Finset (Edge k) → Finset (Edge k) := fun p S =>
   if hp : p < (pairs k).length then
    if (pairs k)[p] ∈ S ∧ 0 < total (S.erase (pairs k)[p]) s₀ rows then S.erase (pairs k)[p] else S
   else S
  let S_out := L.foldr step S₀
  S_out ⊆ S₀ ∧ 0 < total S_out s₀ rows ∧
   ∀ p (hp : p ∈ L), (pairs k)[p]'(hL p hp) ∈ S_out → total (S_out.erase ((pairs k)[p]'(hL p hp))) s₀ rows = 0 := by
 induction L with
 | nil => exact ⟨Finset.Subset.rfl, hpos, fun _ hp => by simp at hp⟩
 | cons p L ih =>
  have hp := hL p (by simp)
  obtain ⟨hsub, hpos1, hmin1⟩ := ih (fun q hq => hL q (by simp [hq]))
  dsimp only
  rw [List.foldr_cons, dif_pos hp]
  set S₁ := L.foldr (fun p S => if hp : p < (pairs k).length then
   if (pairs k)[p] ∈ S ∧ 0 < total (S.erase (pairs k)[p]) s₀ rows then S.erase (pairs k)[p] else S else S) S₀
  by_cases hcond : (pairs k)[p] ∈ S₁ ∧ 0 < total (S₁.erase (pairs k)[p]) s₀ rows
  ·
   rw [if_pos hcond]
   refine ⟨(Finset.erase_subset _ _).trans hsub, hcond.2, fun q hq hmem => ?_⟩
   rcases List.mem_cons.mp hq with rfl | hq'
   · exfalso; exact (Finset.mem_erase.mp hmem).1 rfl
   ·
    have hqL : q < (pairs k).length := hL q (by simp [hq'])
    have hmem1 : (pairs k)[q]'hqL ∈ S₁ := Finset.erase_subset _ _ hmem
    have hz := hmin1 q hq' hmem1
    have hmono := total_mono (s := s₀) (Finset.erase_subset_erase ((pairs k)[q]'hqL) (Finset.erase_subset ((pairs k)[p]'hp) S₁)) rows
    omega
  ·
   rw [if_neg hcond]
   refine ⟨hsub, hpos1, fun q hq hmem => ?_⟩
   rcases List.mem_cons.mp hq with rfl | hq'
   ·
    by_contra hne
    exact hcond ⟨hmem, Nat.pos_of_ne_zero hne⟩
   · exact hmin1 q hq' hmem
lemma deleteEdges_eq {k d s₀ : ℕ} {crown : Bool}
  (soft : List (((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool)) × Bool))
  (hsoft : 0 < soft.length) (hs : s₀ ≤ d + 1 + soft.length.log2)
  {E₀ : Finset (Edge k)} (hE₀ : E₀ ⊆ (pairs k).toFinset)
  (hpos : 0 < total E₀ s₀ (Math.paddedRows k crown soft)) :
  let w := widthCode (un k) (un soft.length)
  let capB := mulU (mulU (un (2 ^ (d + 1))) (un (2 ^ (d + 1)))) (mulU (un soft.length) (un soft.length))
  let rowsStream := (Math.paddedRows k crown soft).flatMap rowBits
  ∃ Q ∈ choices E₀ s₀,
   deleteEdges w capB (un s₀) (un k) (pairCount (un k)) (un soft.length) (pairWords (un k)) rowsStream (mask E₀) =
    mask Q ∧
   TM.signed (Math.paddedRows k crown soft) Q ≠ 0 := by
 intro w capB rowsStream
 let step : ℕ → Finset (Edge k) → Finset (Edge k) := fun p S =>
  if hp : p < (pairs k).length then
   if (pairs k)[p] ∈ S ∧ 0 < total (S.erase (pairs k)[p]) s₀ (Math.paddedRows k crown soft) then
    S.erase (pairs k)[p]
   else S
  else S
 have hrun := runIndexed_ofListFold replaceBound deleteEdgeStep (pairCount (un k)) (pairCount (un k))
  (pack [w, capB, un s₀, un k, pairCount (un k), un soft.length, pairWords (un k), rowsStream])
  (mask E₀) (fun l S => l = mask S ∧ S ⊆ E₀) step E₀ ⟨rfl, Finset.Subset.rfl⟩
  (fun p hp x S hx => by
   rw [pairCount_length] at hp
   rcases hx with ⟨rfl, hSE⟩
   have hSord : ∀ e ∈ S, e.1 < e.2 := fun e he => (pairs_mem e).mp (List.mem_toFinset.mp (hE₀ (hSE he)))
   simp only [deleteEdgeStep, left, right, unpairB_pairB, field_pack_zero, field_pack_succ,
    replaceBound, step, dif_pos hp]
   rw [mask_bit S p hp, clearBitAt_mask S p hp]
   by_cases hmem : (pairs k)[p] ∈ S
   ·
    simp only [hmem, decide_true, bflag, sel, List.cons_ne_nil, ↓reduceIte]
    have hS'ord : ∀ e ∈ S.erase (pairs k)[p], e.1 < e.2 :=
     fun e he => hSord e (Finset.erase_subset _ _ he)
    rw [testSizePos_eq soft hsoft hs hS'ord]
    by_cases hpos' : 0 < total (S.erase (pairs k)[p]) s₀ (Math.paddedRows k crown soft)
    ·
     have hne : (total (S.erase (pairs k)[p]) s₀ (Math.paddedRows k crown soft)).bits ≠ [] := by
      rw [ne_eq, bits_eq_nil_iff]; omega
     simp only [hne, ↓reduceIte, hmem, hpos', and_self]
     rw [List.take_of_length_le (by simp [mask_length, pairCount_length])]
     exact ⟨rfl, (Finset.erase_subset _ _).trans hSE⟩
    ·
     have heq : (total (S.erase (pairs k)[p]) s₀ (Math.paddedRows k crown soft)).bits = [] := by
      rw [bits_eq_nil_iff]; omega
     simp only [heq, ↓reduceIte, hpos', and_false]
     rw [List.take_of_length_le (by simp [mask_length, pairCount_length])]
     exact ⟨rfl, hSE⟩
   ·
    simp only [hmem, decide_false, bflag, Bool.false_eq_true, ↓reduceIte, sel, false_and]
    rw [List.take_of_length_le (by simp [mask_length, pairCount_length])]
    exact ⟨rfl, hSE⟩)
 rw [pairCount_length] at hrun
 set S_out := (List.range (pairs k).length).foldr step E₀
 have hinv := foldr_delete_inv (s₀ := s₀) (Math.paddedRows k crown soft) (List.range (pairs k).length)
  (fun p hp => List.mem_range.mp hp) E₀ hpos
 change S_out ⊆ E₀ ∧ 0 < total S_out s₀ (Math.paddedRows k crown soft) ∧ _ at hinv
 obtain ⟨hSE, hSpos, hSmin⟩ := hinv
 obtain ⟨Q, hQch, hQsne⟩ := (total_pos (k := s₀) S_out (Math.paddedRows k crown soft)).mp hSpos
 have hQS : Q = S_out := by
  by_contra hne
  have hsub : Q ⊆ S_out := Finset.mem_powerset.mp (Finset.mem_filter.mp hQch).1
  obtain ⟨e, heS, heQ⟩ := Finset.not_subset.mp (fun h => hne (Finset.Subset.antisymm hsub h))
  have hep : e ∈ pairs k := List.mem_toFinset.mp (hE₀ (hSE heS))
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hep
  have hz := hSmin p (List.mem_range.mpr hp) heS
  have hQerase : Q ∈ choices (S_out.erase (pairs k)[p]) s₀ := by
   simp only [choices, Finset.mem_filter, Finset.mem_powerset] at hQch ⊢
   exact ⟨Finset.subset_erase.mpr ⟨hsub, heQ⟩, hQch.2⟩
  have hqpos : 0 < total (S_out.erase (pairs k)[p]) s₀ (Math.paddedRows k crown soft) :=
   (total_pos (k := s₀) _ _).mpr ⟨Q, hQerase, hQsne⟩
  exact absurd hqpos (by rw [hz]; exact Nat.not_lt_zero _)
 rw [hQS] at hQch hQsne
 refine ⟨S_out, ?_, hrun.1, hQsne⟩
 simp only [choices, Finset.mem_filter, Finset.mem_powerset] at hQch ⊢
 exact ⟨hSE, hQch.2⟩
def subsetBadStep (s : List Bool) : List Bool :=
 let p := left s
 let a := left (right s)
 let acc := right (right s)
 let Q_mask := left a
 let r_mask := right a
 orFlag acc (andFlag (bitFlagAt p Q_mask) (notFlag (bitFlagAt p r_mask)))
lemma cpSubsetBadStep : CPTs subsetBadStep := by
 have hp := cpLeft cpt_id
 have ha := cpLeft (cpRight cpt_id)
 exact cpOrFlag (cpRight (cpRight cpt_id))
  (cpAndFlag (cpBitFlagAt hp (cpLeft ha)) (cpNotFlag (cpBitFlagAt hp (cpRight ha))))
def subsetFlag (pCount Q_mask r_mask : List Bool) : List Bool :=
 notFlag (runIndexed replaceBound subsetBadStep [true] pCount (pairB Q_mask r_mask) [])
lemma cpSubsetFlag {pCount Q_mask r_mask : List Bool → List Bool}
  (hp : CPTs pCount) (hQ : CPTs Q_mask) (hr : CPTs r_mask) :
  CPTs (fun s => subsetFlag (pCount s) (Q_mask s) (r_mask s)) :=
 cpNotFlag (cpRunIndexed replaceBound_cpt replaceBound_length cpSubsetBadStep
  (cpt_const [true]) hp (cpt_pairB2 hQ hr) (cpt_const []))
lemma subsetFlag_eq {k : ℕ} {Q R : Finset (Edge k)} (hQ : Q ⊆ (pairs k).toFinset) :
  subsetFlag (pairCount (un k)) (mask Q) (mask R) = bflag (decide (Q ⊆ R)) := by
 unfold subsetFlag
 have h := runIndexed_ofListFold replaceBound subsetBadStep [true] (pairCount (un k))
  (pairB (mask Q) (mask R)) [] (fun l b => l = bflag b)
  (fun p b => b || ((pairs k)[p]?.elim false (fun e => decide (e ∈ Q) && !decide (e ∈ R))))
  false rfl (fun p hp x b hx => by
   subst hx
   rw [pairCount_length] at hp
   simp only [subsetBadStep, left, right, unpairB_pairB, replaceBound, List.length_singleton,
    mask_bit Q p hp, mask_bit R p hp, notFlag_bflag, andFlag_bflag, orFlag_bflag, bflag_take_one]
   simp [List.getElem?_eq_getElem hp])
 rw [pairCount_length] at h
 have hfold : ∀ (n : ℕ) (b₀ : Bool), (List.range n).foldr (fun p b =>
   b || ((pairs k)[p]?.elim false (fun e => decide (e ∈ Q) && !decide (e ∈ R)))) b₀ =
   (b₀ || decide (∃ p < n, ∃ hp : p < (pairs k).length, (pairs k)[p] ∈ Q ∧ (pairs k)[p] ∉ R)) := by
  intro n
  induction n with
  | zero => intro b₀; simp
  | succ n ih =>
   intro b₀
   rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih]
   cases b₀
   ·
    simp only [Bool.false_or]
    by_cases hn : n < (pairs k).length
    ·
     simp only [List.getElem?_eq_getElem hn, Option.elim_some]
     by_cases h1 : (pairs k)[n] ∈ Q <;> by_cases h2 : (pairs k)[n] ∈ R
     ·
      simp only [h1, h2, decide_true, Bool.not_true, Bool.and_false, Bool.or_false, Bool.false_or]
      rw [decide_eq_decide]
      exact ⟨fun ⟨p, hp1, hp2, a, b⟩ => ⟨p, by omega, hp2, a, b⟩,
       fun ⟨p, hp1, hp2, a, b⟩ => ⟨p, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hp1) (by rintro rfl; exact b h2), hp2, a, b⟩⟩
     ·
      simp only [h1, h2, decide_true, decide_false, Bool.not_false, Bool.and_true, Bool.or_true, Bool.true_or]
      rw [eq_comm, decide_eq_true_eq]
      exact ⟨n, Nat.lt_succ_self n, hn, h1, h2⟩
     ·
      simp only [h1, h2, decide_false, Bool.false_and, Bool.or_false, Bool.false_or]
      rw [decide_eq_decide]
      exact ⟨fun ⟨p, hp1, hp2, a, b⟩ => ⟨p, by omega, hp2, a, b⟩,
       fun ⟨p, hp1, hp2, a, b⟩ => ⟨p, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hp1) (by rintro rfl; exact h1 a), hp2, a, b⟩⟩
     ·
      simp only [h1, h2, decide_false, Bool.false_and, Bool.or_false, Bool.false_or]
      rw [decide_eq_decide]
      exact ⟨fun ⟨p, hp1, hp2, a, b⟩ => ⟨p, by omega, hp2, a, b⟩,
       fun ⟨p, hp1, hp2, a, b⟩ => ⟨p, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hp1) (by rintro rfl; exact h1 a), hp2, a, b⟩⟩
    ·
     simp only [List.getElem?_eq_none (by omega : (pairs k).length ≤ n), Option.elim_none, Bool.or_false, Bool.false_or]
     rw [decide_eq_decide]
     exact ⟨fun ⟨p, hp1, hp2, a, b⟩ => ⟨p, by omega, hp2, a, b⟩,
      fun ⟨p, hp1, hp2, a, b⟩ => ⟨p, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hp1) (by rintro rfl; omega), hp2, a, b⟩⟩
   · simp only [Bool.true_or]
 rw [hfold (pairs k).length false, Bool.false_or] at h
 rw [h, notFlag_bflag]
 by_cases hsub : Q ⊆ R
 ·
  have hf : decide (∃ p < (pairs k).length, ∃ hp : p < (pairs k).length,
    (pairs k)[p] ∈ Q ∧ (pairs k)[p] ∉ R) = false := decide_eq_false (by
   rintro ⟨p, _, _, h1, h2⟩
   exact h2 (hsub h1))
  rw [hf, decide_eq_true hsub]
  rfl
 ·
  obtain ⟨e, heQ, heR⟩ := Finset.not_subset.mp hsub
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp (hQ heQ))
  have ht : decide (∃ p < (pairs k).length, ∃ hp : p < (pairs k).length,
    (pairs k)[p] ∈ Q ∧ (pairs k)[p] ∉ R) = true := decide_eq_true ⟨p, hp, hp, heQ, heR⟩
  rw [ht, decide_eq_false hsub]
  rfl
def countRowStep (s : List Bool) : List Bool :=
 let j := left s
 let a := left (right s)
 let acc := right (right s)
 let posW := left acc
 let negW := right acc
 let w := field 0 a
 let pCount := field 1 a
 let Q_mask := field 2 a
 let rowsStream := field 3 a
 let r := rowAt pCount j rowsStream
 let r_sign := q17 r
 let r_mask := r.tail
 let ok := subsetFlag pCount Q_mask r_mask
 let acc_next := sel r_sign (pairB posW (incW w negW)) (pairB (incW w posW) negW)
 sel ok acc acc_next
lemma cpCountRowStep : CPTs countRowStep := by
 have hj := cpLeft cpt_id
 have ha := cpLeft (cpRight cpt_id)
 have hacc := cpRight (cpRight cpt_id)
 have hpos := cpLeft hacc
 have hneg := cpRight hacc
 have hw := cpField 0 ha
 have hp := cpField 1 ha
 have hQ := cpField 2 ha
 have hrs := cpField 3 ha
 have hr := cpRowAt hp hj hrs
 have hrsign := cpt_comp hr q35
 have hrmask := cpTail hr
 have hok := cpSubsetFlag hp hQ hrmask
 have hnext := cpt_sel hrsign (cpt_pairB2 hpos (q218 hw hneg)) (cpt_pairB2 (q218 hw hpos) hneg)
 exact cpt_sel hok hacc hnext
def countRows (w pCount softLenU Q_mask rowsStream : List Bool) : List Bool :=
 runIndexed replaceBound countRowStep (w ++ w ++ w ++ [true]) softLenU
  (pack [w, pCount, Q_mask, rowsStream]) (pairB (blank w) (blank w))
lemma cpCountRows {w pCount softLenU Q_mask rowsStream : List Bool → List Bool}
  (hw : CPTs w) (hp : CPTs pCount) (hsl : CPTs softLenU) (hQ : CPTs Q_mask) (hr : CPTs rowsStream) :
  CPTs (fun s => countRows (w s) (pCount s) (softLenU s) (Q_mask s) (rowsStream s)) :=
 cpRunIndexed replaceBound_cpt replaceBound_length cpCountRowStep
  (cpt_app2 (cpt_app2 (cpt_app2 hw hw) hw) (cpt_const [true])) hsl
  (cpt_pairB2 hw (cpt_pairB2 hp (cpt_pairB2 hQ (cpt_pairB2 hr (cpt_const [])))))
  (cpt_pairB2 (cpt_comp hw cpt_blank) (cpt_comp hw cpt_blank))
lemma filter_range_getElem?_length {α : Type*} (L : List α) (p : α → Bool) :
  ((List.range L.length).filter (fun j => L[j]?.elim false p)).length = (L.filter p).length := by
 induction L with
 | nil => rfl
 | cons r rs ih =>
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_cons,
   List.getElem?_cons_zero, Option.elim_some]
  have hsub : (List.range rs.length).filter (fun j => (r :: rs)[j + 1]?.elim false p) =
    (List.range rs.length).filter (fun j => rs[j]?.elim false p) := by
   apply List.filter_congr
   intro x _
   simp [List.getElem?_cons_succ]
  cases hp : p r
  ·
   simp only [hp, Bool.false_eq_true, ↓reduceIte, List.filter_map]
   change (List.map Nat.succ (List.filter (fun j => (r :: rs)[j + 1]?.elim false p) (List.range rs.length))).length = _
   rw [List.length_map, hsub, ih]
  ·
   simp only [hp, ↓reduceIte, List.length_cons, List.filter_map]
   change (List.map Nat.succ (List.filter (fun j => (r :: rs)[j + 1]?.elim false p) (List.range rs.length))).length + 1 = _
   rw [List.length_map, hsub, ih]
lemma countRows_eq {k : ℕ} (w : List Bool) (rows : List (Row k))
  (hlen : rows.length + 1 ≤ 2 ^ w.length) {Q : Finset (Edge k)} (hQ : Q ⊆ (pairs k).toFinset) :
  ∃ posW negW : List Bool,
   countRows w (pairCount (un k)) (un rows.length) (mask Q) (rows.flatMap rowBits) = pairB posW negW ∧
   posW.length = w.length ∧ negW.length = w.length ∧
   val posW = (rows.filter (fun r => r.2 && decide (Q ⊆ r.1))).length ∧
   val negW = (rows.filter (fun r => !r.2 && decide (Q ⊆ r.1))).length := by
 let fstep : ℕ → List Bool → List Bool := fun j acc =>
  replaceBound (w ++ w ++ w ++ [true])
   (countRowStep (pairB (un j) (pairB (pack [w, pairCount (un k), mask Q, rows.flatMap rowBits]) acc))) acc
 have hfold : ∀ L : List ℕ, L.Nodup → (∀ j ∈ L, j < rows.length) →
   ∃ pw nw : List Bool,
    L.foldr fstep (pairB (blank w) (blank w)) = pairB pw nw ∧
    pw.length = w.length ∧ nw.length = w.length ∧
    val pw = (L.filter (fun j => rows[j]?.elim false (fun r => r.2 && decide (Q ⊆ r.1)))).length ∧
    val nw = (L.filter (fun j => rows[j]?.elim false (fun r => !r.2 && decide (Q ⊆ r.1)))).length := by
  intro L hnd hL
  induction L with
  | nil =>
   refine ⟨blank w, blank w, rfl, q33 w, q33 w, ?_, ?_⟩ <;> simp [q37]
  | cons j L ih =>
   have ⟨hjnd, hLnd⟩ := List.nodup_cons.mp hnd
   have hj := hL j (by simp)
   obtain ⟨pw, nw, hacc, hpwlen, hnwlen, hpwval, hnwval⟩ :=
    ih hLnd (fun i hi => hL i (by simp [hi]))
   have hLlen : L.length < rows.length := by
    have hsub : L.toFinset ⊆ (Finset.range rows.length).erase j := by
     intro i hi
     rw [Finset.mem_erase, Finset.mem_range]
     have hiL := List.mem_toFinset.mp hi
     exact ⟨fun he => hjnd (he ▸ hiL), hL i (by simp [hiL])⟩
    have hc := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hLnd, Finset.card_erase_of_mem (Finset.mem_range.mpr hj),
     Finset.card_range] at hc
    omega
   have hpw_lt : val pw + 1 < 2 ^ w.length := by
    have hle := List.length_filter_le (l := L)
     (p := fun i => rows[i]?.elim false (fun r => r.2 && decide (Q ⊆ r.1)))
    omega
   have hnw_lt : val nw + 1 < 2 ^ w.length := by
    have hle := List.length_filter_le (l := L)
     (p := fun i => rows[i]?.elim false (fun r => !r.2 && decide (Q ⊆ r.1)))
    omega
   rw [List.foldr_cons]
   dsimp only [fstep]
   rw [hacc]
   simp only [countRowStep, left, right, unpairB_pairB, field_pack_zero, field_pack_succ, replaceBound]
   rw [rowAt_eq (pairCount (un k)) rows (pairCount_length k) j hj]
   have hsign : q17 (rowBits rows[j]) = bflag rows[j].2 := by
    cases hb : rows[j].2 <;> simp [hb, rowBits, q17, bflag]
   have htail : (rowBits rows[j]).tail = mask rows[j].1 := rfl
   rw [hsign, htail, subsetFlag_eq hQ]
   simp only [List.filter_cons, List.getElem?_eq_getElem hj, Option.elim_some]
   by_cases hsub : Q ⊆ rows[j].1
   ·
    simp only [hsub, decide_true, bflag, sel, List.cons_ne_nil, ↓reduceIte]
    cases hr2 : rows[j].2
    ·
     simp only [hr2, bflag, Bool.false_eq_true, sel, ↓reduceIte, Bool.false_and, Bool.not_false, Bool.true_and]
     rw [List.take_of_length_le (by simp [pairB_length, q215, hpwlen]; omega)]
     refine ⟨pw, incW w nw, rfl, hpwlen, q215 w nw, hpwval, ?_⟩
     rw [q214, Nat.mod_eq_of_lt hnw_lt, hnwval, List.length_cons]
    ·
     simp only [hr2, bflag, sel, List.cons_ne_nil, ↓reduceIte, Bool.true_and, Bool.not_true, Bool.false_and,
      Bool.false_eq_true]
     rw [List.take_of_length_le (by simp [pairB_length, q215, hnwlen]; omega)]
     refine ⟨incW w pw, nw, rfl, q215 w pw, hnwlen, ?_, hnwval⟩
     rw [q214, Nat.mod_eq_of_lt hpw_lt, hpwval, List.length_cons]
   ·
    simp only [hsub, decide_false, bflag, Bool.false_eq_true, sel, ↓reduceIte, Bool.and_false]
    rw [List.take_of_length_le (by simp [pairB_length, hpwlen, hnwlen]; omega)]
    exact ⟨pw, nw, rfl, hpwlen, hnwlen, hpwval, hnwval⟩
 obtain ⟨pw, nw, heq, hpwlen, hnwlen, hpwval, hnwval⟩ :=
  hfold (List.range rows.length) List.nodup_range (fun j hj => List.mem_range.mp hj)
 have hcount : countRows w (pairCount (un k)) (un rows.length) (mask Q) (rows.flatMap rowBits) =
   (List.range rows.length).foldr fstep (pairB (blank w) (blank w)) := by
  unfold countRows
  rw [runIndexed_eq, un_length]
 rw [hcount, heq]
 refine ⟨pw, nw, rfl, hpwlen, hnwlen, ?_, ?_⟩
 · rw [hpwval]; exact filter_range_getElem?_length rows (fun r => r.2 && decide (Q ⊆ r.1))
 · rw [hnwval]; exact filter_range_getElem?_length rows (fun r => !r.2 && decide (Q ⊆ r.1))
def emitNegOut (w softLenU s0U pCount Q_mask rowsStream : List Bool) : List Bool :=
 let counts := countRows w pCount softLenU Q_mask rowsStream
 let posW := left counts
 let negW := right counts
 let odd := q112 s0U
 let pW := sel odd posW negW
 let nW := sel odd negW posW
 let w1 := w ++ [true]
 let diff1 := subW w1 pW nW
 let isNeg := bitFlagAt w diff1
 let absW := sel isNeg (subW w pW nW) (subW w nW pW)
 let absBits := padW (q48 softLenU) absW
 [false] ++ Q_mask ++ q16 isNeg ++ absBits
lemma cpEmitNegOut {w softLenU s0U pCount Q_mask rowsStream : List Bool → List Bool}
  (hw : CPTs w) (hsl : CPTs softLenU) (hs0 : CPTs s0U) (hp : CPTs pCount)
  (hQ : CPTs Q_mask) (hr : CPTs rowsStream) :
  CPTs (fun s => emitNegOut (w s) (softLenU s) (s0U s) (pCount s) (Q_mask s) (rowsStream s)) := by
 have hc := cpCountRows hw hp hsl hQ hr
 have hpos := cpLeft hc
 have hneg := cpRight hc
 have hodd := cpt_comp hs0 q137
 have hpW := cpt_sel hodd hpos hneg
 have hnW := cpt_sel hodd hneg hpos
 have hw1 := cpt_app2 hw (cpt_const [true])
 have hdiff := q148 hw1 hpW hnW
 have hisNeg := cpBitFlagAt hw hdiff
 have habsW := cpt_sel hisNeg (q148 hw hpW hnW) (q148 hw hnW hpW)
 have habsBits := q13 (cpt_comp hsl q41) habsW
 exact cpt_app2 (cpt_app2 (cpt_app2 (cpt_const [false]) hQ) (q73 hisNeg)) habsBits
lemma neg_bit_of_mod (W d p n : ℕ) (v : ℤ)
    (hp : p < 2 ^ W) (hn : n < 2 ^ W)
    (hv : (p : ℤ) - (n : ℤ) = v)
    (hd_lt : d < 2 ^ (W + 1))
    (hmod : ((d : ℤ) ≡ v [ZMOD (2 : ℤ) ^ (W + 1)])) :
    d.testBit W = decide (v < 0) := by
  by_cases hneg : v < 0
  · have hlt : p < n := by omega
    have hcast : v = -((n - p : ℕ) : ℤ) := by omega
    have hsub_lt : n - p < 2 ^ W := by omega
    have heqZ : (d : ℤ) = ((2 ^ (W + 1) - (n - p) : ℕ) : ℤ) := by
      rw [Int.ModEq, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hd_lt)] at hmod
      have heq_sub : ((2 ^ (W + 1) - (n - p) : ℕ) : ℤ) = (2 : ℤ) ^ (W + 1) + v := by
        rw [Nat.cast_sub (by have : 2 ^ W ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega); omega), hcast]
        push_cast; ring
      have hv_ge : -(2 ^ W : ℤ) < v := by omega
      have hpow_le : (2 : ℤ) ^ W < (2 : ℤ) ^ (W + 1) := by
        exact_mod_cast Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self W)
      have hmod_rhs : v % (2 : ℤ) ^ (W + 1) = ((2 ^ (W + 1) - (n - p) : ℕ) : ℤ) := by
        calc v % (2 : ℤ) ^ (W + 1)
            = ((2 : ℤ) ^ (W + 1) + v) % (2 : ℤ) ^ (W + 1) := by
                rw [Int.add_emod, Int.emod_self, zero_add, Int.emod_emod]
          _ = (2 : ℤ) ^ (W + 1) + v := Int.emod_eq_of_lt (by linarith) (by linarith)
          _ = ((2 ^ (W + 1) - (n - p) : ℕ) : ℤ) := heq_sub.symm
      rw [hmod, hmod_rhs]
    have hd_eq : d = 2 ^ (W + 1) - (n - p) := by exact_mod_cast heqZ
    have hd_ge : 2 ^ W ≤ d := by rw [hd_eq, pow_succ]; omega
    have hdiv : d / 2 ^ W = 1 :=
      Nat.div_eq_of_lt_le (by simpa using hd_ge) (by simpa [Nat.mul_two, ← two_mul, pow_succ] using hd_lt)
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv, decide_eq_true hneg]
    rfl
  · have hge : n ≤ p := by omega
    have heqZ : (d : ℤ) = ((p - n : ℕ) : ℤ) := by
      rw [Int.ModEq, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hd_lt)] at hmod
      have hval_nonneg : 0 ≤ v := by omega
      have hpow_le : (2 : ℤ) ^ W ≤ (2 : ℤ) ^ (W + 1) := by
        exact_mod_cast Nat.pow_le_pow_right (by decide) (by omega : W ≤ W + 1)
      have hval_lt : v < (2 : ℤ) ^ (W + 1) := by linarith
      rw [Int.emod_eq_of_lt hval_nonneg hval_lt] at hmod
      omega
    have hd_eq : d = p - n := by exact_mod_cast heqZ
    have hd_lt_W : d < 2 ^ W := by omega
    rw [Nat.testBit_eq_false_of_lt hd_lt_W]
    simp [hneg]
lemma padW_getElem (nU x : List Bool) (i : ℕ) (hi : i < nU.length) :
  (padW nU x)[i]'(by rw [q19]; exact hi) = x.getD i false := by
 dsimp only [padW]
 simp only [q12, List.getElem_take]
 by_cases hix : i < x.length
 · rw [List.getElem_append_left hix, List.getD_eq_getElem _ _ hix]
 ·
  rw [List.getElem_append_right (by omega), List.getD_eq_default _ _ (by omega)]
  exact blank_getElem nU (i - x.length) (by rw [q33]; omega)
lemma emitNegOut_eq {k : ℕ} {crown : Bool} (hk2 : 2 ≤ k)
  (soft : List (((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool)) × Bool))
  (hsoft : 0 < soft.length) {Q : Finset (Edge k)} (hQ : Q ⊆ (pairs k).toFinset)
  (hQne : Q.Nonempty)
  (hval_ne : (-1 : ℤ) ^ Q.card * TM.signed (Math.unforcedRows k crown soft) Q ≠ 0) :
  let w := widthCode (un k) (un soft.length)
  let rowsStream := (Math.paddedRows k crown soft).flatMap rowBits
  let value := (-1 : ℤ) ^ Q.card * TM.signed (Math.unforcedRows k crown soft) Q
  emitNegOut w (un soft.length) (un Q.card) (pairCount (un k)) (mask Q) rowsStream =
   [false] ++ (pairs k).map (fun e => decide (e ∈ Q)) ++ [decide (value < 0)] ++
    (List.range (soft.length.log2 + 1)).map (fun i => value.natAbs.testBit i) := by
 intro w rowsStream value
 have hwlen : w.length = width k soft.length := widthCode_length k soft.length
 have hpow_b : soft.length + 1 ≤ 2 ^ w.length := by
  rw [hwlen]
  have hw_ge : soft.length + 1 ≤ width k soft.length := by
   unfold width
   have hk_ge : 1 ≤ k * k := Nat.mul_pos (by omega) (by omega)
   omega
  exact hw_ge.trans (Nat.lt_two_pow_self).le
 have hrows_len : (Math.paddedRows k crown soft).length = soft.length :=
  Math.paddedRows_length k crown soft
 obtain ⟨posW, negW, hcnt, hposlen, hneglen, hposval, hnegval⟩ :=
  countRows_eq w (Math.paddedRows k crown soft) (hrows_len ▸ hpow_b) hQ
 have hpos_le : val posW ≤ soft.length := by
  rw [hposval, ← hrows_len]; exact List.length_filter_le _ _
 have hneg_le : val negW ≤ soft.length := by
  rw [hnegval, ← hrows_len]; exact List.length_filter_le _ _
 have hsigned : (val posW : ℤ) - (val negW : ℤ) = TM.signed (Math.unforcedRows k crown soft) Q := by
  rw [← Math.signed_padded_eq k crown soft hQne, TM.signed, hposval, hnegval]
 let odd := q112 (un Q.card)
 have hodd : odd = if Q.card % 2 = 1 then [true] else [] := by simp [odd, q112]
 let pW := sel odd posW negW
 let nW := sel odd negW posW
 have hpW_len : pW.length = w.length := by
  dsimp [pW, sel]; split_ifs <;> assumption
 have hnW_len : nW.length = w.length := by
  dsimp [nW, sel]; split_ifs <;> assumption
 have hpW_le : val pW ≤ soft.length := by
  dsimp [pW, sel]; split_ifs <;> assumption
 have hnW_le : val nW ≤ soft.length := by
  dsimp [nW, sel]; split_ifs <;> assumption
 have hval_diff : (val pW : ℤ) - (val nW : ℤ) = value := by
  dsimp only [value]
  rw [pow_neg_one_mod Q.card]
  by_cases hmod : Q.card % 2 = 1
  ·
   have hne : odd ≠ [] := by simp only [hodd, hmod, ↓reduceIte, ne_eq, List.cons_ne_nil, not_false_eq_true]
   simp only [pW, nW, sel, hne, ↓reduceIte, hmod, ← hsigned]
   ring
  ·
   have heq : odd = [] := by simp only [hodd, hmod, ↓reduceIte]
   simp only [pW, nW, sel, heq, ↓reduceIte, hmod, ← hsigned]
   ring
 have hpW_lt : val pW < 2 ^ w.length := by omega
 have hnW_lt : val nW < 2 ^ w.length := by omega
 let W := w.length
 let w1 := w ++ [true]
 have hw1_len : w1.length = W + 1 := by simp [w1, W]
 let diff1 := subW w1 pW nW
 have hdiff1_len : diff1.length = W + 1 := by rw [q63, hw1_len]
 have hdiff1_lt : val diff1 < 2 ^ (W + 1) := by rw [← hdiff1_len]; exact q124 diff1
 have hdiff1_mod : ((val diff1 : ℤ) ≡ value [ZMOD (2 : ℤ) ^ (W + 1)]) := by
  have hm := q142 w1 pW nW
  rw [hw1_len, hval_diff] at hm
  exact hm
 have hisNeg : bitFlagAt w diff1 = bflag (decide (value < 0)) := by
  rw [bitFlagAt_eq, ← val_bitAt,
   neg_bit_of_mod w.length (val diff1) (val pW) (val nW) value hpW_lt hnW_lt hval_diff hdiff1_lt hdiff1_mod]
 let absW := sel (bitFlagAt w diff1) (subW w pW nW) (subW w nW pW)
 have habs_val : val absW = value.natAbs := by
  dsimp [absW]
  rw [hisNeg]
  by_cases hneg : value < 0
  ·
   simp only [hneg, decide_true, bflag, sel, List.cons_ne_nil, ↓reduceIte]
   rw [q83 w nW pW hnW_lt (by omega)]
   omega
  ·
   simp only [hneg, decide_false, bflag, Bool.false_eq_true, sel, ↓reduceIte]
   rw [q83 w pW nW hpW_lt (by omega)]
   omega
 have habs_bits : padW (q48 (un soft.length)) absW =
   (List.range (soft.length.log2 + 1)).map (fun i => value.natAbs.testBit i) := by
  have hlog : (q48 (un soft.length)).length = soft.length.log2 + 1 := by
   rw [q71, un_length, q175 soft.length hsoft]
  apply List.ext_getElem
  · rw [q19, hlog, List.length_map, List.length_range]
  ·
   intro i hi1 hi2
   rw [List.length_map, List.length_range] at hi2
   rw [List.getElem_map, List.getElem_range, ← habs_val, val_bitAt]
   exact padW_getElem (q48 (un soft.length)) absW i (by rw [hlog]; exact hi2)
 have hemit_rw : emitNegOut w (un soft.length) (un Q.card) (pairCount (un k)) (mask Q) rowsStream =
   [false] ++ mask Q ++ q16 (bitFlagAt w diff1) ++ padW (q48 (un soft.length)) absW := by
  unfold emitNegOut
  dsimp only [rowsStream]
  rw [← hrows_len, hcnt, field_left_pair, field_right_pair]
 rw [hemit_rw, hisNeg, q16_bflag, habs_bits]
 rfl
def solveG (s : List Bool) : List Bool :=
 let pad := hd s
 let x := dropN s
 let crownF := q17 x
 let x1 := x.tail
 let kU := hd x1
 let t1 := dropN x1
 let dU := hd t1
 let t2 := dropN t1
 let hardLenU := hd t2
 let t3 := dropN t2
 let nrU := sel crownF kU (kU ++ [true, true])
 let ncU := sel crownF kU (kU ++ [true])
 let bankLenU := nrU ++ ncU
 let hardBytes := mulU hardLenU bankLenU
 let hardStream := t3.take hardBytes.length
 let t4 := t3.drop hardBytes.length
 let softLenU := hd t4
 let softStream := dropN t4
 let pCount := pairCount kU
 let pw := pairWords kU
 let w := widthCode kU softLenU
 let capB := mulU (mulU pad pad) (mulU softLenU softLenU)
 let logSoftU := (q48 softLenU).tail
 let E_mask := allowedMask kU nrU bankLenU hardLenU hardStream pCount pw
 let rowsStream := buildRows crownF kU nrU bankLenU pCount pw softLenU softStream
 let scan := scanSize w capB dU kU pCount softLenU logSoftU E_mask pw rowsStream
 let s0U := dU ++ scan
 let Q_mask := deleteEdges w capB s0U kU pCount softLenU pw rowsStream E_mask
 let negOut := emitNegOut w softLenU s0U pCount Q_mask rowsStream
 sel softLenU [true]
  (sel (hardBadFlag crownF kU nrU bankLenU hardLenU hardStream)
   (sel scan [true] negOut)
   [true])
lemma cpSolveG : CPTs solveG := by
 have hpad := cpt_hd
 have hx := cpt_dropN
 have hcrown := cpt_comp hx q35
 have hx1 := cpTail hx
 have hk := cpt_comp hx1 cpt_hd
 have ht1 := cpt_comp hx1 cpt_dropN
 have hd := cpt_comp ht1 cpt_hd
 have ht2 := cpt_comp ht1 cpt_dropN
 have hhl := cpt_comp ht2 cpt_hd
 have ht3 := cpt_comp ht2 cpt_dropN
 have hnr := cpt_sel hcrown hk (cpt_app2 hk (cpt_const [true, true]))
 have hnc := cpt_sel hcrown hk (cpt_app2 hk (cpt_const [true]))
 have hbl := cpt_app2 hnr hnc
 have hhb := q42 hhl hbl
 have hhs := cpTake hhb ht3
 have ht4 := cpDrop hhb ht3
 have hsl := cpt_comp ht4 cpt_hd
 have hss := cpt_comp ht4 cpt_dropN
 have hp := cpPairCount hk
 have hpw := cpPairWords hk
 have hw := cpWidthCode hk hsl
 have hcap := q42 (q42 hpad hpad) (q42 hsl hsl)
 have hlog := cpTail (cpt_comp hsl q41)
 have hE := cpAllowedMask hk hnr hbl hhl hhs hp hpw
 have hrows := cpBuildRows hcrown hk hnr hbl hp hpw hsl hss
 have hscan := cpScanSize hw hcap hd hk hp hsl hlog hE hpw hrows
 have hs0 := cpt_app2 hd hscan
 have hQ := cpDeleteEdges hw hcap hs0 hk hp hsl hpw hrows hE
 have hneg := cpEmitNegOut hw hsl hs0 hp hQ hrows
 have hbad := cpHardBadFlag hcrown hk hnr hbl hhl hhs
 exact cpt_sel hsl (cpt_const [true])
  (cpt_sel hbad (cpt_sel hscan (cpt_const [true]) hneg) (cpt_const [true]))
def paramFn (x : List Bool) : List Bool := hd (dropN x.tail)
lemma cpParamFn : CPTs paramFn := by
 unfold paramFn
 exact cpt_comp (cpt_comp cpt_tail cpt_dropN) cpt_hd
lemma paramFn_len (x : List Bool) : (paramFn x).length ≤ x.length := by
 have h1 := hd_length (dropN x.tail)
 have h2 := dropN_length x.tail
 have h3 : x.tail.length ≤ x.length := by simp
 dsimp only [paramFn]
 omega
lemma paramFn_encoded (crown : Bool) (k d : ℕ) (rest : List Bool) :
  paramFn ([crown] ++ header k ++ header d ++ rest) = un d := by
 simp only [paramFn, List.cons_append, List.nil_append, List.tail_cons, header, List.append_assoc]
 rw [dropN_un_false, hd_un_false]
lemma solveG_spec (k d : ℕ) (crown : Bool) (hk2 : 2 ≤ k) (hk7 : crown = true → 7 ≤ k)
  (hard : List ((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool)))
  (soft : List (((Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool)) × Bool)) :
  let banks := fun z : (Fin (Math.nr k crown) → Bool) × (Fin (Math.nc k crown) → Bool) =>
   List.ofFn z.1 ++ List.ofFn z.2
  let x := [crown] ++ header k ++ header d ++ header hard.length ++ hard.flatMap banks ++
   header soft.length ++ soft.flatMap (fun t => banks t.1 ++ [t.2])
  let out := solveG (un (2 ^ (d + 1)) ++ false :: x)
  (out = [true] ↔ Math.low k d crown hard soft) ∧ (soft = [] → out = [true]) ∧
  (¬ Math.low k d crown hard soft → ∃ Q value, value ≠ 0 ∧ Math.realizes k d crown hard soft Q value ∧
   value.natAbs ≤ soft.length ∧ Q.card ≤ d + 1 + soft.length.log2 ∧
   (∀ Z v, v ≠ 0 → Math.realizes k d crown hard soft Z v → Q.card ≤ Z.card) ∧
   out = [false] ++ (pairs k).map (fun e => decide (e ∈ Q)) ++ [decide (value < 0)] ++
    (List.range (soft.length.log2 + 1)).map (fun i => value.natAbs.testBit i)) := by
 intro banks x out
 let hardStream := hard.flatMap banks
 let softStream := soft.flatMap (fun t => banks t.1 ++ [t.2])
 have hhb_len : (mulU (un hard.length) (un (Math.nr k crown + Math.nc k crown))).length = hardStream.length := by
  simp only [mulU, un_length, hardStream]
  rw [flatMap_len hard banks (Math.nr k crown + Math.nc k crown) (fun z _ => by simp [banks])]
 have hx_eq : x = crown :: (un k ++ false :: (un d ++ false :: (un hard.length ++ false ::
   (hardStream ++ (un soft.length ++ false :: softStream))))) := by
  simp only [x, header, hardStream, softStream, List.append_assoc, List.cons_append, List.nil_append]
 have hpad : hd (un (2 ^ (d + 1)) ++ false :: x) = un (2 ^ (d + 1)) := hd_un_false _ _
 have hx : dropN (un (2 ^ (d + 1)) ++ false :: x) = x := dropN_un_false _ _
 have hcrownF : q17 x = bflag crown := by rw [hx_eq]; cases crown <;> rfl
 have hkU : hd x.tail = un k := by rw [hx_eq]; simp [hd_un_false]
 have ht1 : dropN x.tail = un d ++ false :: (un hard.length ++ false ::
   (hardStream ++ (un soft.length ++ false :: softStream))) := by rw [hx_eq]; simp [dropN_un_false]
 have hdU : hd (dropN x.tail) = un d := by rw [ht1, hd_un_false]
 have ht2 : dropN (dropN x.tail) = un hard.length ++ false ::
   (hardStream ++ (un soft.length ++ false :: softStream)) := by rw [ht1, dropN_un_false]
 have hhlU : hd (dropN (dropN x.tail)) = un hard.length := by rw [ht2, hd_un_false]
 have ht3 : dropN (dropN (dropN x.tail)) = hardStream ++ (un soft.length ++ false :: softStream) := by
  rw [ht2, dropN_un_false]
 have hnrU : sel (q17 x) (hd x.tail) (hd x.tail ++ [true, true]) = un (Math.nr k crown) := by
  rw [hcrownF, hkU]
  cases crown <;> simp [sel, bflag, Math.nr, un, List.replicate_add]
 have hncU : sel (q17 x) (hd x.tail) (hd x.tail ++ [true]) = un (Math.nc k crown) := by
  rw [hcrownF, hkU]
  cases crown <;> simp [sel, bflag, Math.nc, un, List.replicate_add]
 have hbankLenU : un (Math.nr k crown) ++ un (Math.nc k crown) = un (Math.nr k crown + Math.nc k crown) := by
  rw [un, un, un, ← List.replicate_add]
 have hhardStream : (dropN (dropN (dropN x.tail))).take
   (mulU (hd (dropN (dropN x.tail))) (un (Math.nr k crown + Math.nc k crown))).length = hardStream := by
  rw [hhlU, hhb_len, ht3, List.take_left]
 have ht4 : (dropN (dropN (dropN x.tail))).drop
   (mulU (hd (dropN (dropN x.tail))) (un (Math.nr k crown + Math.nc k crown))).length =
   un soft.length ++ false :: softStream := by
  rw [hhlU, hhb_len, ht3, List.drop_append_length]
 have hslU : hd (un soft.length ++ false :: softStream) = un soft.length := hd_un_false _ _
 have hsoftStream : dropN (un soft.length ++ false :: softStream) = softStream := dropN_un_false _ _
 have hout_rw : out =
   let w := widthCode (un k) (un soft.length)
   let capB := mulU (mulU (un (2 ^ (d + 1))) (un (2 ^ (d + 1)))) (mulU (un soft.length) (un soft.length))
   let logSoftU := (q48 (un soft.length)).tail
   let E_mask := allowedMask (un k) (un (Math.nr k crown)) (un (Math.nr k crown + Math.nc k crown))
    (un hard.length) hardStream (pairCount (un k)) (pairWords (un k))
   let rowsStream := buildRows (bflag crown) (un k) (un (Math.nr k crown))
    (un (Math.nr k crown + Math.nc k crown)) (pairCount (un k)) (pairWords (un k))
    (un soft.length) softStream
   let scan := scanSize w capB (un d) (un k) (pairCount (un k)) (un soft.length)
    logSoftU E_mask (pairWords (un k)) rowsStream
   let s0U := un d ++ scan
   let Q_mask := deleteEdges w capB s0U (un k) (pairCount (un k)) (un soft.length)
    (pairWords (un k)) rowsStream E_mask
   let negOut := emitNegOut w (un soft.length) s0U (pairCount (un k)) Q_mask rowsStream
   sel (un soft.length) [true]
    (sel (hardBadFlag (bflag crown) (un k) (un (Math.nr k crown))
      (un (Math.nr k crown + Math.nc k crown)) (un hard.length) hardStream)
     (sel scan [true] negOut)
     [true]) := by
  dsimp only [out, solveG]
  rw [hpad, hx, hcrownF, hkU, ht1]
  simp only [hd_un_false, dropN_un_false]
  have hnrU' : sel (bflag crown) (un k) (un k ++ [true, true]) = un (Math.nr k crown) := by
   cases crown <;> simp [sel, bflag, Math.nr, un, List.replicate_add]
  have hncU' : sel (bflag crown) (un k) (un k ++ [true]) = un (Math.nc k crown) := by
   cases crown <;> simp [sel, bflag, Math.nc, un, List.replicate_add]
  rw [hnrU', hncU', hbankLenU, hhb_len, List.take_left, List.drop_append_length, hd_un_false, dropN_un_false]
 by_cases hsoft_nil : soft = []
 ·
  subst hsoft_nil
  have hout_true : out = [true] := by rw [hout_rw]; simp [sel]
  have hlow : Math.low k d crown hard [] := by
   refine ⟨fun _ => 0, fun f _ => ?_⟩
   simp [Math.score]
  exact ⟨⟨fun _ => hlow, fun _ => hout_true⟩, fun _ => hout_true, fun h => (h hlow).elim⟩
 ·
  have hsoft_pos : 0 < soft.length := List.length_pos_of_ne_nil hsoft_nil
  have hsl_ne : un soft.length ≠ [] := by
   intro h
   have hl : (un soft.length).length = 0 := by rw [h]; rfl
   rw [un_length] at hl
   omega
  have hE_eq : allowedMask (un k) (un (Math.nr k crown)) (un (Math.nr k crown + Math.nc k crown))
    (un hard.length) hardStream (pairCount (un k)) (pairWords (un k)) =
    mask (Math.allowedEdges k crown hard) := by
   dsimp only [hardStream, banks]
   exact allowedMask_eq hard
  have hrows_eq : buildRows (bflag crown) (un k) (un (Math.nr k crown))
    (un (Math.nr k crown + Math.nc k crown)) (pairCount (un k)) (pairWords (un k))
    (un soft.length) softStream = (Math.paddedRows k crown soft).flatMap rowBits := by
   dsimp only [softStream, banks]
   exact buildRows_eq soft
  have hhb_eq : hardBadFlag (bflag crown) (un k) (un (Math.nr k crown))
    (un (Math.nr k crown + Math.nc k crown)) (un hard.length) hardStream =
    bflag (Math.hardBad k crown hard) := by
   dsimp only [hardStream, banks]
   exact hardBadFlag_eq hard
  cases hbad : Math.hardBad k crown hard
  ·
   have hE_sub : Math.allowedEdges k crown hard ⊆ (pairs k).toFinset := Finset.filter_subset _ _
   have hE_ord : ∀ e ∈ Math.allowedEdges k crown hard, e.1 < e.2 :=
    fun e he => (pairs_mem e).mp (List.mem_toFinset.mp (hE_sub he))
   have hscan_spec := scanSize_eq (d := d) soft hsoft_pos hE_ord
   dsimp only at hscan_spec
   rcases hscan_spec with ⟨hscan_nil, hscan_zero⟩ | ⟨i₀, hi₀, hscan_eq, hpos_s₀, hmin_s₀⟩
   ·
    have hout_true : out = [true] := by
     dsimp only at hout_rw
     rw [hout_rw, hhb_eq, hbad, hE_eq, hrows_eq, hscan_nil]
     simp [sel, hsl_ne, bflag]
    have hlow : Math.low k d crown hard soft := by
     rw [Math.low_iff_signed_zero hk2 hk7 hbad]
     by_contra hnot
     push Not at hnot
     let P : ℕ → Prop := fun s => ∃ Q, Q ⊆ Math.allowedEdges k crown hard ∧
      disjointEdges Q ∧ d < Q.card ∧ Q.card = s ∧ TM.signed (Math.unforcedRows k crown soft) Q ≠ 0
     have hPex : ∃ s, P s := by
      obtain ⟨Q, hQ, hdis, hdQ, hsne⟩ := hnot
      exact ⟨Q.card, Q, hQ, hdis, hdQ, rfl, hsne⟩
     classical
     let s_min := Nat.find hPex
     obtain ⟨Q_min, hQm, hQm_dis, hm_d, hm_card, hQm_ne⟩ := Nat.find_spec hPex
     have hm_le : Q_min.card ≤ d + 1 + soft.length.log2 := by
      apply Math.min_card_le_log2 soft hQm hQm_dis hm_d hQm_ne
      intro Z hZ hZdis hdZ hZne
      rw [hm_card]
      exact Nat.find_le ⟨Z, hZ, hZdis, hdZ, rfl, hZne⟩
     have hzero_m := hscan_zero Q_min.card hm_d hm_le
     have hQne : Q_min.Nonempty := Finset.card_pos.mp (by omega)
     have hQch : Q_min ∈ choices (Math.allowedEdges k crown hard) Q_min.card := by
      simp only [choices, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hQm, trivial, hQm_dis⟩
     have hpos_m : 0 < total (Math.allowedEdges k crown hard) Q_min.card (Math.paddedRows k crown soft) :=
      (total_pos (k := _) _ _).mpr ⟨Q_min, hQch, by rw [Math.signed_padded_eq k crown soft hQne]; exact hQm_ne⟩
     omega
    exact ⟨⟨fun _ => hlow, fun _ => hout_true⟩, fun h => (hsoft_nil h).elim, fun h => (h hlow).elim⟩
   ·
    have hs₀_le : d + 1 + i₀ ≤ d + 1 + soft.length.log2 := by omega
    have hdel := deleteEdges_eq soft hsoft_pos hs₀_le hE_sub hpos_s₀
    dsimp only at hdel
    obtain ⟨Q, hQch, hdel_eq, hQsne⟩ := hdel
    have hQsub : Q ⊆ Math.allowedEdges k crown hard := Finset.mem_powerset.mp (Finset.mem_filter.mp hQch).1
    have hQcard : Q.card = d + 1 + i₀ := (Finset.mem_filter.mp hQch).2.1
    have hQdis : disjointEdges Q := (Finset.mem_filter.mp hQch).2.2
    have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
    have hQunforced : TM.signed (Math.unforcedRows k crown soft) Q ≠ 0 := by
     rwa [← Math.signed_padded_eq k crown soft hQne]
    let value := (-1 : ℤ) ^ Q.card * TM.signed (Math.unforcedRows k crown soft) Q
    have hval_ne : value ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hQunforced
    have hemit := emitNegOut_eq hk2 soft hsoft_pos (hQsub.trans hE_sub) hQne hval_ne
    have hs0U : un d ++ (true :: un i₀) = un Q.card := by
     rw [hQcard]
     dsimp only [un]
     rw [← List.replicate_succ, ← List.replicate_add]
     rw [show d + (i₀ + 1) = d + 1 + i₀ by omega]
    have hout_neg : out = [false] ++ (pairs k).map (fun e => decide (e ∈ Q)) ++ [decide (value < 0)] ++
      (List.range (soft.length.log2 + 1)).map (fun i => value.natAbs.testBit i) := by
     dsimp only at hout_rw
     rw [hout_rw, hhb_eq, hbad, hE_eq, hrows_eq, hscan_eq]
     simp only [sel, hsl_ne, ↓reduceIte, Bool.false_eq_true, bflag, List.cons_ne_nil, hs0U]
     rw [← hQcard] at hdel_eq
     rw [hdel_eq, hemit]
    have hne_true : out ≠ [true] := by rw [hout_neg]; simp
    have hnot_low : ¬ Math.low k d crown hard soft := by
     rw [Math.low_iff_signed_zero hk2 hk7 hbad]
     push Not
     exact ⟨Q, hQsub, hQdis, by omega, hQunforced⟩
    refine ⟨⟨fun h => (hne_true h).elim, fun h => (hnot_low h).elim⟩,
     fun h => (hsoft_nil h).elim, fun _ => ?_⟩
    refine ⟨Q, value, hval_ne, Math.realizes_of_signed hk2 hk7 hbad soft hQsub hQdis (by omega), ?_, ?_, ?_, hout_neg⟩
    ·
     dsimp only [value]
     rw [Int.natAbs_mul, Int.natAbs_pow]
     simp only [Int.reduceNeg, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]
     exact (signed_abs_le _ _).trans (by simp [Math.unforcedRows]; exact List.length_filter_le _ _)
    · omega
    ·
     intro Z v hv hrealZ
     obtain ⟨_, hZsub, hZdis, hdZ, hZsne⟩ := Math.realizes_imp hk2 hk7 soft hv hrealZ
     by_cases hZle : Z.card ≤ d + 1 + soft.length.log2
     ·
      by_contra hlt
      have hz := hmin_s₀ Z.card hdZ (by omega)
      have hZne : Z.Nonempty := Finset.card_pos.mp (by omega)
      have hZch : Z ∈ choices (Math.allowedEdges k crown hard) Z.card := by
       simp only [choices, Finset.mem_filter, Finset.mem_powerset]
       exact ⟨hZsub, trivial, hZdis⟩
      have hZpos : 0 < total (Math.allowedEdges k crown hard) Z.card (Math.paddedRows k crown soft) :=
       (total_pos (k := _) _ _).mpr ⟨Z, hZch, by rw [Math.signed_padded_eq k crown soft hZne]; exact hZsne⟩
      omega
     · omega
  ·
   have hout_true : out = [true] := by
    rw [hout_rw, hhb_eq, hbad]
    simp [sel, hsl_ne, bflag]
   have hlow : Math.low k d crown hard soft := by
    refine ⟨fun _ => 0, fun f hf => ?_⟩
    exact (Math.fits_of_hardBad hk2 hk7 hbad f hf).elim
   exact ⟨⟨fun _ => hlow, fun _ => hout_true⟩, fun _ => hout_true, fun h => (h hlow).elim⟩
end Alg

end PEqualNP.Outside.L_meta_33636

open PEqualNP.Outside.L_meta_33636 in
theorem PEqualNP.Outside.L_meta_33636 : (let header := fun z : Nat => List.replicate z true ++ [false]
let pairs := fun n : Nat => (List.finRange n).flatMap (fun i =>
  ((List.finRange n).filter (fun j => decide (i < j))).map (fun j => (i,j)))
∃ (M : Turing.TM2ComputableAux Bool Bool) (c : Nat), (∀ i, Finite (M.tm.Γ i)) ∧
∀ (k d : Nat) (crown : Bool), 2 ≤ k → (crown = true → 7 ≤ k) →
  let nr := if crown then k+2 else k
  let nc := if crown then k+1 else k
  let A := fun (i : Fin nr) (j : Fin nc) => if crown then
    decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
  let Fn := (Fin nr → Bool) → (Fin nc → Bool) → Bool
  let eligible := fun f : Fn => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    (if crown then PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2*k+1 else PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k) ∧
    PEqualNP.Represents.Represents A C ∧ ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
  ∀ (hard : List ((Fin nr → Bool) × (Fin nc → Bool)))
    (soft : List (((Fin nr → Bool) × (Fin nc → Bool)) × Bool)),
  let fits := fun f : Fn => eligible f ∧ ∀ h ∈ hard, f h.1 h.2 = crown
  let score := fun f : Fn => (soft.filter (fun t => decide (f t.1.1 t.1.2 = t.2))).length
  let probe := fun f : Fn => (pairs k).toFinset.filter (fun e =>
    f (fun i => decide (i.val = e.1.val ∨ i.val = e.2.val)) (fun _ => false) = !crown)
  let low := ∃ a : Finset (Fin k × Fin k) → Int, ∀ f : Fn, fits f →
    (score f : Int) = ((probe f).powerset.filter (fun T => T.card ≤ d)).sum a
  let ends := fun e : Fin k × Fin k => ({e.1,e.2} : Finset (Fin k))
  let realizes := fun (Q : Finset (Fin k × Fin k)) (value : Int) => d < Q.card ∧ (∀ e ∈ Q, e.1 < e.2) ∧
    (∀ e ∈ Q, ∀ z ∈ Q, e ≠ z → Disjoint (ends e) (ends z)) ∧
    ∃ cube : Finset (Fin k × Fin k) → Fn,
      (∀ T ⊆ Q, fits (cube T) ∧ probe (cube T) = T) ∧
      Q.powerset.sum (fun T => (-1 : Int)^(Q.card-T.card)*(score (cube T) : Int)) = value
  let banks := fun z : (Fin nr → Bool) × (Fin nc → Bool) => List.ofFn z.1 ++ List.ofFn z.2
  let x := [crown] ++ header k ++ header d ++ header hard.length ++ hard.flatMap banks ++
    header soft.length ++ soft.flatMap (fun t => banks t.1 ++ [t.2])
  ∃ out : List Bool,
    Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
      (some (out.map M.outputAlphabet.invFun)) (2^(c*(d+1))*(x.length+2)^c)) ∧
    (out = [true] ↔ low) ∧ (soft = [] → out = [true]) ∧
    (¬low → ∃ Q value, value ≠ 0 ∧ realizes Q value ∧ value.natAbs ≤ soft.length ∧
      Q.card ≤ d+1+soft.length.log2 ∧
      (∀ Z v, v ≠ 0 → realizes Z v → Q.card ≤ Z.card) ∧
      out = [false] ++ (pairs k).map (fun e => decide (e ∈ Q)) ++ [decide (value < 0)] ++
        (List.range (soft.length.log2+1)).map (fun i => value.natAbs.testBit i))) := by
  intro header pairs
  obtain ⟨M, c, hfin, hrun⟩ :=
    TM.Padding.mr_fpt
      Alg.paramFn
      Alg.solveG
      Alg.cpParamFn
      Alg.paramFn_len
      Alg.cpSolveG
  refine ⟨M, c, hfin, fun k d crown hk2 hk7 => ?_⟩
  intro nr nc A Fn eligible hard soft fits score probe low ends realizes banks x
  have hpad : Alg.paramFn x = List.replicate d true := by
    dsimp only [x, header, banks]
    simpa only [TM.Packed.header, TM.Lib.Universal.un,
      List.append_assoc] using Alg.paramFn_encoded crown k d _
  have hrunx := hrun x
  rw [hpad, List.length_replicate] at hrunx
  let out := Alg.solveG
    (List.replicate (2 ^ (d + 1)) true ++ false :: x)
  refine ⟨out, hrunx, ?_⟩
  have hspec := Alg.solveG_spec k d crown hk2 hk7 hard soft
  unfold Math.low Math.realizes
    Math.fits Math.score
    Math.probe Math.eligible
    Math.adjA Math.Fn
    Math.nr Math.nc
    TM.ends TM.Packed.header
    TM.Lib.Universal.un
    TM.Packed.pairs at hspec
  dsimp only [x, out, banks, header, pairs, nr, nc, A, Fn, eligible, fits, score, probe, low, ends, realizes]
  simpa only [List.append_assoc] using hspec
