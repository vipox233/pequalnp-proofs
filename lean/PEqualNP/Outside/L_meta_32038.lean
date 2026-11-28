import PEqualNP.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
namespace PEqualNP.Outside.L_meta_32038
open PEqualNP.CircuitLowerBounds
def pull (n : ℕ) (G : List Gate) (T : Finset ℕ) : Finset ℕ :=
  match G with
  | [] => T
  | a :: gs =>
    let U := pull (n+1) gs T
    if n ∈ U then U.erase n ∪ a.inputs.toFinset else U

def unaryCount (G : List Gate) : ℕ :=
  (G.filter (fun a => decide (a.inputs.length ≤ 1))).length

lemma pull_card (n : ℕ) (G : List Gate) (T : Finset ℕ)
    (hG : ∀ a ∈ G, a.inputs.length ≤ 2) :
    (pull n G T).card + unaryCount G ≤ T.card + G.length := by
  induction G generalizing n with
  | nil => simp [pull, unaryCount]
  | cons a gs ih =>
    have ha := hG a (by simp)
    have ih' := ih (n+1) (fun a h => hG a (by simp [h]))
    let U := pull (n+1) gs T
    change U.card + unaryCount gs ≤ T.card + gs.length at ih'
    change (if n ∈ U then U.erase n ∪ a.inputs.toFinset else U).card +
      unaryCount (a :: gs) ≤ T.card + (a :: gs).length
    have ht : a.inputs.toFinset.card ≤ a.inputs.length := List.toFinset_card_le _
    have hc := Finset.card_union_le (U.erase n) a.inputs.toFinset
    have hu : unaryCount (a :: gs) =
        unaryCount gs + (if a.inputs.length ≤ 1 then 1 else 0) := by
      by_cases h : a.inputs.length ≤ 1 <;> simp [unaryCount, h]
    rw [hu]
    by_cases hn : n ∈ U
    · have he := Finset.card_erase_of_mem hn
      have hp : 0 < U.card := Finset.card_pos.mpr ⟨n, hn⟩
      by_cases h : a.inputs.length ≤ 1 <;> simp only [if_pos hn, h, ite_true, ite_false,
        List.length_cons] <;> omega
    · by_cases h : a.inputs.length ≤ 1 <;> simp only [if_neg hn, h, ite_true, ite_false,
        List.length_cons] <;> omega

def step (a : Gate) (x : List Bool) : List Bool :=
  x ++ [a.op.eval (a.inputs.map (fun i => x.getD i false))]

def Agree (S : Finset ℕ) (x y : List Bool) : Prop :=
  ∀ i ∈ S, x.getD i false = y.getD i false

lemma getD_step_ne (a : Gate) (x : List Bool) (i : ℕ) (hi : i ≠ x.length) :
    (step a x).getD i false = x.getD i false := by
  by_cases h : i < x.length
  · exact List.getD_append _ _ _ _ h
  · have h' : x.length + 1 ≤ i := by omega
    rw [List.getD_eq_default _ _ (by simp [step]; omega),
      List.getD_eq_default _ _ (by omega)]

lemma agree_step (n : ℕ) (a : Gate) (U : Finset ℕ) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (h : Agree (if n ∈ U then U.erase n ∪ a.inputs.toFinset else U) x y) :
    Agree U (step a x) (step a y) := by
  intro i hi
  by_cases hin : i = n
  · subst i
    simp only [if_pos hi] at h
    have hm : a.inputs.map (fun i => x.getD i false) =
        a.inputs.map (fun i => y.getD i false) :=
      List.map_congr_left (fun j hj => h j (Finset.mem_union.mpr
        (Or.inr (List.mem_toFinset.mpr hj))))
    unfold step
    rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    simpa [hx, hy] using congrArg (fun l => a.op.eval l) hm
  · rw [getD_step_ne _ _ _ (by omega), getD_step_ne _ _ _ (by omega)]
    apply h i
    split_ifs
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hin, hi⟩))
    · exact hi

lemma agree_pull (n : ℕ) (G : List Gate) (T : Finset ℕ) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n) (h : Agree (pull n G T) x y) :
    Agree T (G.foldl (fun x a => step a x) x) (G.foldl (fun x a => step a x) y) := by
  induction G generalizing n x y with
  | nil => exact h
  | cons a gs ih =>
    apply ih (n+1)
    · simp [step, hx]
    · simp [step, hy]
    · exact agree_step n a (pull (n+1) gs T) x y hx hy h

def LE (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

lemma op_mono (a : Gate) (ha : a.op = .and ∨ a.op = .or)
    (x y : List Bool) (h : LE x y) :
    a.op.eval (a.inputs.map (fun i => x.getD i false)) = true →
    a.op.eval (a.inputs.map (fun i => y.getD i false)) = true := by
  rcases ha with ha | ha
  · simp only [ha, GateOp.eval, List.all_eq_true, List.mem_map]
    intro hx z hz
    obtain ⟨i, hi, rfl⟩ := hz
    exact h i (hx _ ⟨i, hi, rfl⟩)
  · simp only [ha, GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hb⟩

lemma step_mono (a : Gate) (ha : a.op = .and ∨ a.op = .or)
    (x y : List Bool) (hlen : x.length = y.length) (h : LE x y) :
    LE (step a x) (step a y) := by
  intro i
  by_cases hi : i = x.length
  · subst i
    unfold step
    rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    simp only [← hlen, Nat.sub_self, List.getD_cons_zero]
    exact op_mono a ha x y h
  · rw [getD_step_ne _ _ _ hi, getD_step_ne _ _ _ (by omega)]
    exact h i

lemma circuit_mono (G : List Gate) (hG : ∀ a ∈ G, a.op = .and ∨ a.op = .or)
    (x y : List Bool) (hlen : x.length = y.length) (h : LE x y) :
    LE (G.foldl (fun x a => step a x) x) (G.foldl (fun x a => step a x) y) := by
  induction G generalizing x y with
  | nil => exact h
  | cons a gs ih =>
    apply ih (fun a ha => hG a (by simp [ha]))
    · simp [step, hlen]
    · exact step_mono a (hG a (by simp)) x y hlen h

lemma support_exists (n : ℕ) (C : Circuit)
    (hg : ∀ a ∈ C.gates, a.inputs.length ≤ 2 ∧
      (a.op = .and ∨ a.op = .or ∨ (a.op = .not ∧ a.inputs.length = 1))) :
    ∃ S : Finset ℕ, S.card ≤ C.size + 1 ∧
      (∀ x y : List Bool, x.length = n → y.length = n →
        Agree S x y → C.eval x = C.eval y) ∧
      (S.card ≤ C.size ∨ (∀ x y : List Bool, x.length = y.length →
        LE x y → C.eval x = true → C.eval y = true)) := by
  let S := pull n C.gates {C.output}
  have hc := pull_card n C.gates {C.output} (fun a ha => (hg a ha).1)
  have hc' : S.card + unaryCount C.gates ≤ 1 + C.size := by
    simpa [S, Circuit.size] using hc
  refine ⟨S, by omega, ?_, ?_⟩
  · intro x y hx hy h
    exact agree_pull n C.gates {C.output} x y hx hy h C.output (by simp)
  · by_cases hu : unaryCount C.gates = 0
    · right
      have ha : ∀ a ∈ C.gates, a.op = .and ∨ a.op = .or := by
        intro a h
        rcases (hg a h).2 with h | h | ⟨h, he⟩
        · exact Or.inl h
        · exact Or.inr h
        · have hm : a ∈ C.gates.filter (fun a => decide (a.inputs.length ≤ 1)) :=
            List.mem_filter.mpr ⟨‹a ∈ C.gates›, by simp [he]⟩
          have hn := List.length_pos_of_mem hm
          unfold unaryCount at hu
          omega
      intro x y hlen h
      exact circuit_mono C.gates ha x y hlen h C.output
    · left
      omega

def rows (N : ℕ) (S : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun x => x.val ∈ S)
def cols (N : ℕ) (S : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun y => N+y.val ∈ S)
def primary (N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (rows N S).image Fin.val ∪ (cols N S).image (fun y => N+y.val)

lemma primary_sub (N : ℕ) (S : Finset ℕ) : primary N S ⊆ S := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hx).2
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hy).2

lemma primary_card (N : ℕ) (S : Finset ℕ) :
    (primary N S).card = (rows N S).card + (cols N S).card := by
  have hd : Disjoint ((rows N S).image Fin.val)
      ((cols N S).image (fun y => N+y.val)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hj
    have := x.isLt
    omega
  rw [primary, Finset.card_union_of_disjoint hd]
  rw [Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]

lemma primary_card_le (N : ℕ) (S : Finset ℕ) :
    (rows N S).card + (cols N S).card ≤ S.card := by
  rw [← primary_card]
  exact Finset.card_le_card (primary_sub N S)

def strip {N : ℕ} (R Q : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  (R ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ Q)

lemma strip_card {N : ℕ} (R Q : Finset (Fin N)) :
    (strip R Q).card + R.card * Q.card = N * (R.card + Q.card) := by
  have he : (R ×ˢ (Finset.univ : Finset (Fin N))) ∩
      ((Finset.univ : Finset (Fin N)) ×ˢ Q) = R ×ˢ Q := by
    ext z
    simp
  have hc := Finset.card_union_add_card_inter
    (R ×ˢ (Finset.univ : Finset (Fin N)))
    ((Finset.univ : Finset (Fin N)) ×ˢ Q)
  rw [he] at hc
  simpa only [strip, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Nat.mul_add, Nat.mul_comm R.card N] using hc

lemma strip_eq {N : ℕ} (R Q : Finset (Fin N)) (A : Finset (Fin N × Fin N))
    (hN : 0 < N) (hs : A ⊆ strip R Q)
    (he : A.card = N * (R.card + Q.card)) :
    A = strip R Q ∧ (R = ∅ ∨ Q = ∅) := by
  have hle := Finset.card_le_card hs
  have hc := strip_card R Q
  have hz : R.card * Q.card = 0 := by omega
  constructor
  · apply Finset.eq_of_subset_of_card_le hs
    omega
  · rcases Nat.mul_eq_zero.mp hz with hr | hq
    · exact Or.inl (Finset.card_eq_zero.mp hr)
    · exact Or.inr (Finset.card_eq_zero.mp hq)

lemma bit_read {N : ℕ} (x : Fin N) (i : ℕ) :
    (List.ofFn (fun j : Fin N => decide (j = x))).getD i false = decide (i = x.val) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs with hi
  · simp [Fin.ext_iff]
  · have hn : i ≠ x.val := by have := x.isLt; omega
    simp [hn]

lemma oe_read {N : ℕ} (x y : Fin N) (i : ℕ) :
    (PEqualNP.Represents.oneEach x y).getD i false =
      (decide (i = x.val) || decide (i = N+y.val)) := by
  unfold PEqualNP.Represents.oneEach
  by_cases hi : i < N
  · rw [List.getD_append _ _ _ _ (by simpa using hi), bit_read]
    have hn : i ≠ N+y.val := by omega
    simp [hn]
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi),
      List.length_ofFn, bit_read]
    have hn : i ≠ x.val := by have := x.isLt; omega
    simp only [hn, decide_false, Bool.false_or]
    simp only [decide_eq_decide]
    omega

lemma outside_read {N h : ℕ} (x y : Fin N) (w : Fin h → Bool) (i : ℕ)
    (hx : i ≠ x.val) (hy : i ≠ N+y.val) :
    (PEqualNP.Represents.oneEach x y ++ List.ofFn w).getD i false =
      (List.replicate (N+N) false ++ List.ofFn w).getD i false := by
  have hl : (PEqualNP.Represents.oneEach x y).length = N+N := by
    simp [PEqualNP.Represents.oneEach]
  by_cases hi : i < N+N
  · rw [List.getD_append _ _ _ _ (by omega),
      List.getD_append _ _ _ _ (by simpa using hi), oe_read,
      List.getD_replicate false hi]
    simp [hx, hy]
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi),
      hl, List.length_replicate]

lemma baseline_le {N h : ℕ} (x y : Fin N) (w : Fin h → Bool) :
    LE (List.replicate (N+N) false ++ List.ofFn w)
      (PEqualNP.Represents.oneEach x y ++ List.ofFn w) := by
  intro i hi
  have hl : (PEqualNP.Represents.oneEach x y).length = N+N := by
    simp [PEqualNP.Represents.oneEach]
  by_cases hi' : i < N+N
  · rw [List.getD_append _ _ _ _ (by simpa using hi'), List.getD_replicate false hi'] at hi
    contradiction
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi'),
      List.length_replicate] at hi
    rwa [List.getD_append_right _ _ _ _ (by omega), hl]

lemma outside_agree {N h : ℕ} (S : Finset ℕ) (x y : Fin N) (w : Fin h → Bool)
    (hx : x ∉ rows N S) (hy : y ∉ cols N S) :
    Agree S (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
      (List.replicate (N+N) false ++ List.ofFn w) := by
  intro i hi
  apply outside_read x y w i
  · intro he
    apply hx
    simp only [rows, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [he] at hi
  · intro he
    apply hy
    simp only [cols, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [he] at hi

lemma seed_agree {N h : ℕ} (S : Finset ℕ) (he : primary N S = S)
    (x y : Fin N) (w v : Fin h → Bool) :
    Agree S (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
      (PEqualNP.Represents.oneEach x y ++ List.ofFn v) := by
  intro i hi
  have hi' : i < N+N := by
    rw [← he] at hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      have := a.isLt
      omega
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      have := a.isLt
      omega
  have hl : (PEqualNP.Represents.oneEach x y).length = N+N := by
    simp [PEqualNP.Represents.oneEach]
  rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]

def cells {N : ℕ} (H : Fin N → Fin N → Bool) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun z => H z.1 z.2 = true)
def tab {N : ℕ} (h : ℕ) (C : Circuit) (w : Fin h → Bool) (x y : Fin N) :=
  C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)

lemma profile {N m h : ℕ} (C : Circuit) (hm : m < N)
    (hg : ∀ a ∈ C.gates, a.inputs.length ≤ 2 ∧
      (a.op = .and ∨ a.op = .or ∨ (a.op = .not ∧ a.inputs.length = 1)))
    (cap : ∀ w, (cells (tab (N := N) h C w)).card ≤ m*N) :
    ∃ S : Finset ℕ, S.card ≤ C.size + 1 ∧
      (primary N S = S → ∀ w v (x y : Fin N), tab h C w x y = tab h C v x y) ∧
      ∀ w, (cells (tab h C w) ⊆ strip (rows N S) (cols N S)) ∨
        ((cells (tab h C w))ᶜ ⊆ strip (rows N S) (cols N S) ∧ S.card ≤ C.size) := by
  obtain ⟨S, hS, hag, hmS⟩ := support_exists (N+N+h) C hg
  refine ⟨S, hS, ?_, ?_⟩
  · intro he w v x y
    apply hag
    · simp [PEqualNP.Represents.oneEach, Nat.add_assoc]
    · simp [PEqualNP.Represents.oneEach, Nat.add_assoc]
    · exact seed_agree S he x y w v
  · intro w
    let b := C.eval (List.replicate (N+N) false ++ List.ofFn w)
    have hout : ∀ x y, x ∉ rows N S → y ∉ cols N S → tab h C w x y = b := by
      intro x y hx hy
      apply hag
      · simp [PEqualNP.Represents.oneEach, Nat.add_assoc]
      · simp
      · exact outside_agree S x y w hx hy
    cases hb : b with
    | false =>
      left
      intro z hz
      by_contra hn
      have hn' : z.1 ∉ rows N S ∧ z.2 ∉ cols N S := by
        simpa [strip] using hn
      have ho := hout z.1 z.2 hn'.1 hn'.2
      simp only [cells, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rw [hb] at ho
      exact Bool.false_ne_true (ho.symm.trans hz)
    | true =>
      right
      refine ⟨?_, ?_⟩
      · intro z hz
        by_contra hn
        have hn' : z.1 ∉ rows N S ∧ z.2 ∉ cols N S := by
          simpa [strip] using hn
        have ho := hout z.1 z.2 hn'.1 hn'.2
        have hz' : tab h C w z.1 z.2 ≠ true := by simpa [cells] using hz
        exact hz' (ho.trans hb)
      · rcases hmS with hle | hmono
        · exact hle
        · have hall : ∀ x y : Fin N, tab h C w x y = true := by
            intro x y
            exact hmono _ _ (by simp [PEqualNP.Represents.oneEach, Nat.add_assoc])
              (baseline_le x y w) hb
          have hc : cells (tab (N := N) h C w) = Finset.univ := by
            ext z
            simp [cells, hall]
          have he := cap w
          rw [hc] at he
          have hn : 0 < N := by omega
          have hn' := Nat.mul_lt_mul_of_pos_right hm hn
          simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at he
          omega

lemma area_bound {N m g h : ℕ} (C : Circuit) (hm : m < N)
    (hg : ∀ a ∈ C.gates, a.inputs.length ≤ 2 ∧
      (a.op = .and ∨ a.op = .or ∨ (a.op = .not ∧ a.inputs.length = 1)))
    (hs : C.size ≤ g) (cap : ∀ w, (cells (tab (N := N) h C w)).card ≤ m*N) :
    ∀ w, (cells (tab (N := N) h C w)).card ≤
      N * (if N-m ≤ g then m else min m (g+1)) := by
  obtain ⟨S, hS, hind, hp⟩ := profile C hm hg cap
  have hk := primary_card_le N S
  have hc := strip_card (rows N S) (cols N S)
  intro w
  by_cases hgm : N-m ≤ g
  · simpa [hgm, Nat.mul_comm] using cap w
  · simp only [if_neg hgm]
    by_cases hmg : m ≤ g+1
    · simpa [min_eq_left hmg, Nat.mul_comm] using cap w
    rw [min_eq_right (show g+1 ≤ m by omega)]
    rcases hp w with hsu | ⟨hsu, hcard⟩
    · have h1 := Finset.card_le_card hsu
      have h2 := Nat.mul_le_mul_left N (show (rows N S).card + (cols N S).card ≤ g+1 by omega)
      omega
    · have h1 := Finset.card_le_card hsu
      have h2 := Nat.mul_le_mul_left N (show (rows N S).card + (cols N S).card ≤ g by omega)
      have h3 := cap w
      have h4 : (cells (tab (N := N) h C w)).card +
          (cells (tab (N := N) h C w))ᶜ.card = N*N := by
        simpa using Finset.card_add_card_compl (cells (tab (N := N) h C w))
      have h5 : g + m < N := by omega
      have h6 := Nat.mul_lt_mul_of_pos_left h5 (show 0 < N by omega)
      rw [Nat.mul_add] at h6
      have h7 : N*m = m*N := Nat.mul_comm _ _
      omega

lemma saturation {N v : ℕ} (hN : 0 < N) (S : Finset ℕ)
    (A : Finset (Fin N × Fin N)) (ha : A ⊆ strip (rows N S) (cols N S))
    (hc : A.card = N*v) (hv : S.card ≤ v) :
    primary N S = S ∧ ∃ T : Finset (Fin N), T.card = v ∧
      ((∀ x y, (x,y) ∈ A ↔ x ∈ T) ∨ (∀ x y, (x,y) ∈ A ↔ y ∈ T)) := by
  have hk := primary_card_le N S
  have hs := strip_card (rows N S) (cols N S)
  have hle := Finset.card_le_card ha
  have hmul : N*v ≤ N*((rows N S).card+(cols N S).card) := by omega
  have hvk := Nat.le_of_mul_le_mul_left hmul hN
  have he : (rows N S).card + (cols N S).card = v := by omega
  have hPS : primary N S = S := by
    apply Finset.eq_of_subset_of_card_le (primary_sub N S)
    rw [primary_card]
    omega
  refine ⟨hPS, ?_⟩
  obtain ⟨hA, hrow | hcol⟩ := strip_eq (rows N S) (cols N S) A hN ha (by rw [he]; exact hc)
  · refine ⟨cols N S, ?_, Or.inr ?_⟩
    · simpa [hrow] using he
    · intro x y
      rw [hA, hrow]
      simp [strip]
  · refine ⟨rows N S, ?_, Or.inl ?_⟩
    · simpa [hcol] using he
    · intro x y
      rw [hA, hcol]
      simp [strip]

def Stripes {N : ℕ} (h : ℕ) (C : Circuit) (s : ℕ) : Prop :=
  ∃ T : Finset (Fin N), T.card = s ∧
    ((∀ w x y, tab h C w x y = decide (x ∈ T)) ∨
     (∀ w x y, tab h C w x y = decide (y ∈ T)))

lemma rigid {N m g h u : ℕ} (C : Circuit) (hm : m < N)
    (hg : ∀ a ∈ C.gates, a.inputs.length ≤ 2 ∧
      (a.op = .and ∨ a.op = .or ∨ (a.op = .not ∧ a.inputs.length = 1)))
    (hs : C.size ≤ g) (cap : ∀ w, (cells (tab (N := N) h C w)).card ≤ m*N)
    (hu : u ≤ N) (hgu : g+1 ≤ u) (hgu' : g ≤ N-u)
    (w₀ : Fin h → Bool) (hext : (cells (tab (N := N) h C w₀)).card = N*u) :
    Stripes (N := N) h C u := by
  have hN : 0 < N := by omega
  obtain ⟨S, hS, hind, hp⟩ := profile C hm hg cap
  rcases hp w₀ with hA | ⟨hA, hs'⟩
  · obtain ⟨heS, T, hT, hr | hc⟩ :=
      saturation hN S _ hA hext (show S.card ≤ u by omega)
    · refine ⟨T, hT, Or.inl ?_⟩
      intro w x y
      rw [hind heS w w₀ x y]
      apply Bool.eq_iff_iff.mpr
      simpa [cells] using hr x y
    · refine ⟨T, hT, Or.inr ?_⟩
      intro w x y
      rw [hind heS w w₀ x y]
      apply Bool.eq_iff_iff.mpr
      simpa [cells] using hc x y
  · have hcomp : (cells (tab (N := N) h C w₀))ᶜ.card = N*(N-u) := by
      rw [Finset.card_compl, Fintype.card_prod, Fintype.card_fin, hext,
        Nat.mul_sub_left_distrib]
    obtain ⟨heS, T, hT, hr | hc⟩ :=
      saturation hN S _ hA hcomp (show S.card ≤ N-u by omega)
    · refine ⟨Tᶜ, ?_, Or.inl ?_⟩
      · rw [Finset.card_compl, Fintype.card_fin, hT]
        omega
      · intro w x y
        rw [hind heS w w₀ x y]
        apply Bool.eq_iff_iff.mpr
        simpa [cells] using not_congr (hr x y)
    · refine ⟨Tᶜ, ?_, Or.inr ?_⟩
      · rw [Finset.card_compl, Fintype.card_fin, hT]
        omega
      · intro w x y
        rw [hind heS w w₀ x y]
        apply Bool.eq_iff_iff.mpr
        simpa [cells] using not_congr (hc x y)

open scoped BigOperators
def loss {N : ℕ} (color : Fin N → Fin N → Fin N)
    (H : Fin N → Fin N → Bool) (U : Finset (Fin N)) : ℕ :=
  (Finset.univ.filter (fun z : Fin N × Fin N => H z.1 z.2 ≠ decide (color z.1 z.2 ∈ U))).card

def rot {N : ℕ} [NeZero N] (T : Finset (Fin N)) (z : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun c => c+z ∈ T)

lemma rot_card {N : ℕ} [NeZero N] (T : Finset (Fin N)) (z : Fin N) :
    (rot T z).card = T.card := by
  have he := Fintype.sum_bijective (fun c : Fin N => c+z) (Equiv.addRight z).bijective
    (fun c : Fin N => if c+z ∈ T then (1 : ℕ) else 0)
    (fun c : Fin N => if c ∈ T then (1 : ℕ) else 0) (fun c => rfl)
  simpa [rot, Finset.sum_boole] using he

lemma rot_cover {N : ℕ} [NeZero N] (T : Finset (Fin N)) (c : Fin N) :
    (∑ z : Fin N, if c ∈ rot T z then (1 : ℝ) else 0) = T.card := by
  have he := Fintype.sum_bijective (fun z : Fin N => c+z) (Equiv.addLeft c).bijective
    (fun z : Fin N => if c+z ∈ T then (1 : ℝ) else 0)
    (fun z : Fin N => if z ∈ T then (1 : ℝ) else 0) (fun z => rfl)
  simpa [rot, Finset.sum_boole] using he

lemma mismatch_sum {N : ℕ} [NeZero N] (T : Finset (Fin N)) (c : Fin N) (b : Bool) :
    (∑ z : Fin N, if b ≠ decide (c ∈ rot T z) then (1 : ℝ) else 0) =
      (T.card : ℝ) + ((N : ℝ)-2*T.card) * (if b = true then 1 else 0) := by
  cases b
  · simpa using rot_cover T c
  · have hh : ∀ z : Fin N,
        (if true ≠ decide (c ∈ rot T z) then (1 : ℝ) else 0) =
        1 - (if c ∈ rot T z then 1 else 0) := by
      intro z
      by_cases hz : c ∈ rot T z <;> simp [hz]
    simp_rw [hh]
    rw [Finset.sum_sub_distrib, rot_cover]
    simp
    ring

lemma average_loss {N : ℕ} [NeZero N] (color : Fin N → Fin N → Fin N)
    (T : Finset (Fin N)) (H : Fin N → Fin N → Bool) :
    (∑ z : Fin N, (loss color H (rot T z) : ℝ)) =
      (N : ℝ)*N*T.card - (2*T.card-N)*(cells H).card := by
  have hs : ∀ z, (loss color H (rot T z) : ℝ) =
      ∑ p : Fin N × Fin N, if H p.1 p.2 ≠ decide (color p.1 p.2 ∈ rot T z)
        then (1 : ℝ) else 0 := by
    intro z
    exact (Finset.sum_boole (R := ℝ)
      (fun p : Fin N × Fin N => H p.1 p.2 ≠ decide (color p.1 p.2 ∈ rot T z))
      Finset.univ).symm
  simp_rw [hs]
  rw [Finset.sum_comm]
  simp_rw [mismatch_sum]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have he : (∑ p : Fin N × Fin N, if H p.1 p.2 = true then (1 : ℝ) else 0) =
      (cells H).card := by simp [cells, Finset.sum_boole]
  rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul]
  ring

lemma average_risk {N h : ℕ} [NeZero N] (color : Fin N → Fin N → Fin N)
    (T : Finset (Fin N)) (C : Circuit) (P : (Fin h → Bool) → ℝ)
    (hP : (∑ w, P w) = 1) :
    (∑ z : Fin N, ∑ w, P w * (loss color (tab h C w) (rot T z) : ℝ)) =
      (N : ℝ)*N*T.card - (2*T.card-N)*∑ w, P w * ((cells (tab (N := N) h C w)).card : ℝ) := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, average_loss, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hP]
  have he : (∑ w, P w * ((2*(T.card : ℝ)-N)*(cells (tab (N := N) h C w)).card)) =
      (2*(T.card : ℝ)-N)*∑ w, P w * ((cells (tab (N := N) h C w)).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    ring
  rw [he, one_mul]

lemma value_cast {N t u : ℕ} (ht : t ≤ N) (ht' : N ≤ 2*t) (hu : u ≤ N) :
    ((N*t - (2*t-N)*u : ℕ) : ℝ) =
      (N : ℝ)*t - (2*t-N)*u := by
  have hh : (2*t-N)*u ≤ N*t := by
    have hh := Nat.mul_le_mul (show 2*t-N ≤ t by omega) hu
    simpa [Nat.mul_comm] using hh
  rw [Nat.cast_sub hh, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub ht']
  push_cast
  ring

lemma minimax {N t u h : ℕ} (hN : 0 < N) (ht : t ≤ N) (ht' : N < 2*t)
    (hu : u ≤ N) (color : Fin N → Fin N → Fin N) (C : Circuit)
    (P : (Fin h → Bool) → ℝ) (hP : ∀ w, 0 ≤ P w) (hPsum : (∑ w, P w) = 1)
    (cap : ∀ w, (cells (tab (N := N) h C w)).card ≤ N*u) :
    (∃ U : Finset (Fin N), U.card = t ∧
      ((N*t-(2*t-N)*u : ℕ) : ℝ) ≤ ∑ w, P w * (loss color (tab h C w) U : ℝ)) ∧
    ((∀ U : Finset (Fin N), U.card = t →
      (∑ w, P w * (loss color (tab h C w) U : ℝ)) ≤ ((N*t-(2*t-N)*u : ℕ) : ℝ)) →
      ∃ w, (cells (tab (N := N) h C w)).card = N*u) := by
  classical
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨T, hsub, hT⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin N))) (by simpa using ht)
  let q : ℝ := ∑ w, P w * ((cells (tab (N := N) h C w)).card : ℝ)
  let v : ℝ := ((N*t-(2*t-N)*u : ℕ) : ℝ)
  have hv : v = (N : ℝ)*t-(2*t-N)*u := value_cast ht (by omega) hu
  have hd : (0 : ℝ) < 2*t-N := by
    have hh : (N : ℝ) < 2*t := by exact_mod_cast ht'
    linarith
  have hq : q ≤ (N : ℝ)*u := by
    calc
      q ≤ ∑ w, P w * ((N : ℝ)*u) := by
        apply Finset.sum_le_sum
        intro w hw
        apply mul_le_mul_of_nonneg_left _ (hP w)
        exact_mod_cast cap w
      _ = (N : ℝ)*u := by rw [← Finset.sum_mul, hPsum, one_mul]
  have havg := average_risk color T C P hPsum
  rw [hT] at havg
  change (∑ z : Fin N, ∑ w, P w * (loss color (tab h C w) (rot T z) : ℝ)) =
    (N : ℝ)*N*t-(2*t-N)*q at havg
  have hlow : (N : ℝ)*v ≤ ∑ z : Fin N, ∑ w, P w *
      (loss color (tab h C w) (rot T z) : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hq (le_of_lt hd)
    nlinarith [havg, hv]
  constructor
  · obtain ⟨z, hz, hle⟩ := Finset.exists_le_of_sum_le
      (s := (Finset.univ : Finset (Fin N)))
      (f := fun _ => v)
      (g := fun z => ∑ w, P w * (loss color (tab h C w) (rot T z) : ℝ))
      ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (by simpa using hlow)
    exact ⟨rot T z, (rot_card T z).trans hT, hle⟩
  · intro hupper
    have hsum : (∑ z : Fin N, ∑ w, P w * (loss color (tab h C w) (rot T z) : ℝ)) ≤
        (N : ℝ)*v := by
      calc
        _ ≤ ∑ _z : Fin N, v := Finset.sum_le_sum (fun z hz =>
          hupper (rot T z) ((rot_card T z).trans hT))
        _ = _ := by simp
    have hprod : (2*(t : ℝ)-N)*((N : ℝ)*u) ≤ (2*(t : ℝ)-N)*q := by
      nlinarith [hsum, havg, hv]
    have hmean : (N : ℝ)*u ≤ q := by
      by_contra hn
      have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hd
      linarith
    obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image
      (Finset.univ : Finset (Fin h → Bool))
      (fun w => (cells (tab (N := N) h C w)).card)
      ⟨fun _ => false, Finset.mem_univ _⟩
    have hqmax : q ≤ ((cells (tab (N := N) h C w)).card : ℝ) := by
      calc
        q ≤ ∑ v, P v * ((cells (tab (N := N) h C w)).card : ℝ) := by
          apply Finset.sum_le_sum
          intro v hv
          apply mul_le_mul_of_nonneg_left _ (hP v)
          exact_mod_cast hmax v (Finset.mem_univ _)
        _ = _ := by rw [← Finset.sum_mul, hPsum, one_mul]
    refine ⟨w, Nat.le_antisymm (cap w) ?_⟩
    exact_mod_cast hmean.trans hqmax

def Good (n : ℕ) (C : Circuit) : Prop :=
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ C.output < n+C.size ∧
  ∀ a ∈ C.gates, a.inputs.length ≤ 2 ∧
    (a.op = .and ∨ a.op = .or ∨ (a.op = .not ∧ a.inputs.length = 1))

def extend (n : ℕ) (C : Circuit) (a : Gate) : Circuit :=
  ⟨C.gates ++ [a], n+C.size⟩

lemma extend_size (n : ℕ) (C : Circuit) (a : Gate) :
    (extend n C a).size = C.size + 1 := by simp [extend, Circuit.size]

lemma extend_good {n : ℕ} {C : Circuit} {a : Gate} (hC : Good n C)
    (ha : ∀ i ∈ a.inputs, i < n+C.size)
    (hag : a.inputs.length ≤ 2 ∧
      (a.op = .and ∨ a.op = .or ∨ (a.op = .not ∧ a.inputs.length = 1))) :
    Good n (extend n C a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj i hi
    have hlen : (extend n C a).gates.length = C.gates.length + 1 := by simp [extend]
    by_cases hj' : j < C.gates.length
    · have he : PEqualNP.MetaComplexity.NestedCover.gateAt (extend n C a) j =
          PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        exact List.getD_append _ _ _ _ hj'
      rw [he] at hi
      exact hC.1 j hj' i hi
    · have hj' : j = C.gates.length := by omega
      subst j
      have he : PEqualNP.MetaComplexity.NestedCover.gateAt (extend n C a) C.gates.length = a := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, extend]
      rw [he] at hi
      exact ha i hi
  · simp [extend, Circuit.size]
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hC.2.2 b hb
    · have he : b = a := by simpa using hb
      subst b
      exact hag

lemma wires_length (G : List Gate) (x : List Bool) :
    (G.foldl (fun x a => step a x) x).length = x.length + G.length := by
  induction G generalizing x with
  | nil => simp
  | cons a gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma wires_input (G : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (G.foldl (fun x a => step a x) x).getD i false = x.getD i false := by
  induction G generalizing x with
  | nil => rfl
  | cons a gs ih =>
    rw [List.foldl_cons, ih (step a x) (by simp [step]; omega)]
    exact getD_step_ne _ _ _ (by omega)

lemma extend_eval (n : ℕ) (C : Circuit) (a : Gate) (x : List Bool) (hx : x.length = n) :
    (extend n C a).eval x =
      a.op.eval (a.inputs.map (fun i => (C.wires x).getD i false)) := by
  have hl : (C.wires x).length = n+C.size := by
    simpa [Circuit.size, Circuit.wires, step, hx] using wires_length C.gates x
  change ((C.gates ++ [a]).foldl (fun x a => step a x) x).getD (n+C.size) false = _
  rw [List.foldl_append]
  change (step a (C.wires x)).getD (n+C.size) false = _
  unfold step
  rw [List.getD_append_right _ _ _ _ (by omega), ← hl]
  simp

lemma or_exists (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    ∃ C : Circuit, Good n C ∧ C.size = k-1 ∧
      ∀ x : List Bool, x.length = n →
        C.eval x = (List.range k).any (fun i => x.getD i false) := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      refine ⟨⟨[], 0⟩, ?_, rfl, ?_⟩
      · constructor
        · simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack]
        · constructor
          · simpa [Circuit.size] using hk.trans_le hkn
          · simp
      · intro x hx
        simp [Circuit.eval, Circuit.wires]
    | succ k =>
      obtain ⟨C, hC, hsize, hev⟩ := ih (by omega) (by omega)
      let a : Gate := ⟨.or, [C.output, k+1]⟩
      refine ⟨extend n C a, extend_good hC ?_ (by simp [a]), ?_, ?_⟩
      · intro i hi
        simp only [a, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hC.2.1
        · omega
      · rw [extend_size, hsize]
        omega
      · intro x hx
        rw [extend_eval _ _ _ _ hx]
        simp only [a, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
          List.any_nil, id_eq, Bool.or_false]
        change (C.eval x || (C.wires x).getD (k+1) false) = _
        rw [show (C.wires x).getD (k+1) false = x.getD (k+1) false from
          wires_input C.gates x (k+1) (by omega), hev x hx, List.range_succ (n := k+1),
          List.any_append]
        simp

lemma or_rows {N k : ℕ} (hk : 0 < k) (hkN : k < N) :
    ∃ C : Circuit, Good (N+N) C ∧ C.size = k-1 ∧
      ∃ T : Finset (Fin N), T.card = k ∧
        ∀ w : Fin 0 → Bool, ∀ x y, tab 0 C w x y = decide (x ∈ T) := by
  obtain ⟨C, hC, hs, hev⟩ := or_exists (N+N) k hk (by omega)
  let T : Finset (Fin N) := Finset.Iio ⟨k, hkN⟩
  refine ⟨C, hC, hs, T, ?_, ?_⟩
  · simp [T]
  · intro w x y
    have hw : List.ofFn w = [] := by simp
    unfold tab
    rw [hw, List.append_nil, hev _ (by simp [PEqualNP.Represents.oneEach])]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq, T, Finset.mem_Iio, Fin.lt_def]
    constructor
    · rintro ⟨i, hi, hb⟩
      rw [oe_read] at hb
      have hn : i ≠ N+y.val := by omega
      simp [hn] at hb
      omega
    · intro hx
      refine ⟨x.val, hx, ?_⟩
      simpa using oe_read x y x.val

lemma optimal_rows {N m g : ℕ} (hm : 0 < m) (hmN : m < N) :
    let u := if N-m ≤ g then m else min m (g+1)
    ∃ C : Circuit, Good (N+N) C ∧ C.size ≤ g ∧
      ∃ T : Finset (Fin N), T.card = u ∧
        ∀ w : Fin 0 → Bool, ∀ x y, tab 0 C w x y = decide (x ∈ T) := by
  dsimp
  by_cases hd : N-m ≤ g
  · rw [if_pos hd]
    obtain ⟨C, hC, hs, T, hT, hev⟩ := or_rows (N := N) (k := N-m) (by omega) (by omega)
    let a : Gate := ⟨.not, [C.output]⟩
    refine ⟨extend (N+N) C a, extend_good hC ?_ (by simp [a]), ?_, Tᶜ, ?_, ?_⟩
    · intro i hi
      have he : i = C.output := by simpa [a] using hi
      subst i
      exact hC.2.1
    · rw [extend_size, hs]
      omega
    · rw [Finset.card_compl, Fintype.card_fin, hT]
      omega
    · intro w x y
      unfold tab
      rw [extend_eval _ _ _ _ (by simp [PEqualNP.Represents.oneEach, Nat.add_assoc])]
      change Bool.not (tab 0 C w x y) = decide (x ∈ Tᶜ)
      rw [hev w x y]
      simp
  · rw [if_neg hd]
    obtain ⟨C, hC, hs, T, hT, hev⟩ :=
      or_rows (N := N) (k := min m (g+1)) (by omega) (by omega)
    refine ⟨C, hC, ?_, T, hT, hev⟩
    rw [hs]
    omega

lemma row_area {N : ℕ} (T : Finset (Fin N)) (H : Fin N → Fin N → Bool)
    (hH : ∀ x y, H x y = decide (x ∈ T)) :
    (cells H).card = T.card*N := by
  have he : cells H = T ×ˢ (Finset.univ : Finset (Fin N)) := by
    ext z
    simp [cells, hH]
  rw [he, Finset.card_product, Finset.card_univ, Fintype.card_fin]

lemma mismatch_univ {N : ℕ} (T : Finset (Fin N)) (b : Bool) :
    (∑ z : Fin N, if b ≠ decide (z ∈ T) then (1 : ℝ) else 0) =
      (T.card : ℝ) + ((N : ℝ)-2*T.card) * (if b = true then 1 else 0) := by
  cases b
  · simp [Finset.sum_boole]
  · have hh : ∀ z : Fin N,
        (if true ≠ decide (z ∈ T) then (1 : ℝ) else 0) =
        1 - (if z ∈ T then 1 else 0) := by
      intro z
      by_cases hz : z ∈ T <;> simp [hz]
    simp_rw [hh]
    rw [Finset.sum_sub_distrib, Finset.sum_boole]
    simp
    ring

lemma row_loss_real {N : ℕ} (color : Fin N → Fin N → Fin N)
    (hcolor : ∀ x, Function.Bijective (color x)) (T U : Finset (Fin N))
    (H : Fin N → Fin N → Bool) (hH : ∀ x y, H x y = decide (x ∈ T)) :
    (loss color H U : ℝ) = (N : ℝ)*U.card - (2*U.card-N)*T.card := by
  have hs : (loss color H U : ℝ) =
      ∑ p : Fin N × Fin N, if H p.1 p.2 ≠ decide (color p.1 p.2 ∈ U)
        then (1 : ℝ) else 0 :=
    (Finset.sum_boole (R := ℝ) _ _).symm
  rw [hs, Fintype.sum_prod_type]
  simp_rw [hH]
  have he : ∀ x : Fin N,
      (∑ y : Fin N, if decide (x ∈ T) ≠ decide (color x y ∈ U) then (1 : ℝ) else 0) =
      (U.card : ℝ) + ((N : ℝ)-2*U.card) * (if x ∈ T then 1 else 0) := by
    intro x
    rw [Fintype.sum_bijective (color x) (hcolor x) _
      (fun z => if decide (x ∈ T) ≠ decide (z ∈ U) then (1 : ℝ) else 0) (fun y => rfl)]
    simpa using mismatch_univ U (decide (x ∈ T))
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp
  ring

lemma row_loss_nat {N t u : ℕ} (color : Fin N → Fin N → Fin N)
    (hcolor : ∀ x, Function.Bijective (color x)) (T U : Finset (Fin N))
    (hT : T.card = u) (hU : U.card = t) (ht : t ≤ N) (ht' : N ≤ 2*t) (hu : u ≤ N)
    (H : Fin N → Fin N → Bool) (hH : ∀ x y, H x y = decide (x ∈ T)) :
    loss color H U = N*t-(2*t-N)*u := by
  have he := row_loss_real color hcolor T U H hH
  rw [hT, hU] at he
  have hv := value_cast ht ht' hu
  exact_mod_cast he.trans hv.symm

end PEqualNP.Outside.L_meta_32038

open PEqualNP.Outside.L_meta_32038

theorem PEqualNP.Outside.L_meta_32038 : (∀ (N m t g : ℕ), 0 < m → m < N → N < 2*t → t ≤ N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (h : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N+h) C ∧ C.output < N+N+h+C.size ∧
    ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))
  let table := fun (h : ℕ) (C : Circ) (w : Fin h → Bool) (x y : X) =>
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
  let area := fun (H : X → X → Bool) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => H z.1 z.2 = true)).card
  let stripes := fun (h : ℕ) (C : Circ) (s : ℕ) =>
    ∃ T : Finset X, T.card = s ∧
      ((∀ (w : Fin h → Bool) (x y : X), table h C w x y = decide (x ∈ T)) ∨
       (∀ (w : Fin h → Bool) (x y : X), table h C w x y = decide (y ∈ T)))
  ∀ color : X → X → X,
    (∀ x, Function.Bijective (color x)) → (∀ y, Function.Bijective (fun x => color x y)) →
    let u := if N-m ≤ g then m else min m (g+1)
    let value := N*t - (2*t-N)*u
    let loss := fun (H : X → X → Bool) (U : Finset X) =>
      ((Finset.univ : Finset (X × X)).filter (fun z =>
        H z.1 z.2 ≠ decide (color z.1 z.2 ∈ U))).card
    let fits := fun (h : ℕ) (C : Circ) =>
      legal h C ∧ C.size ≤ g ∧ ∀ w : Fin h → Bool, area (table h C w) ≤ m*N
    let risk := fun (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ) (U : Finset X) =>
      ∑ w, P w * (loss (table h C w) U : ℝ)
    (∃ D : Circ, fits 0 D ∧ stripes 0 D u ∧
      ∀ (w : Fin 0 → Bool) (U : Finset X), U.card = t → loss (table 0 D w) U = value) ∧
    ∀ (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ),
      fits h C → (∀ w, 0 ≤ P w) → (∑ w, P w) = 1 →
      (∃ U : Finset X, U.card = t ∧ (value : ℝ) ≤ risk h C P U) ∧
      (g ≤ min (m-1) (N-m) →
        (∀ U : Finset X, U.card = t → risk h C P U ≤ (value : ℝ)) →
        stripes h C u)) := by
  classical
  intro N m t g hm hmN hNt ht
  dsimp only
  intro color hrow hcol
  let u := if N-m ≤ g then m else min m (g+1)
  let v := N*t-(2*t-N)*u
  change
    (∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      (Good (N+N) D ∧ D.size ≤ g ∧
        ∀ w, (cells (tab (N := N) 0 D w)).card ≤ m*N) ∧
      Stripes (N := N) 0 D u ∧
      ∀ w U, U.card = t → loss color (tab 0 D w) U = v) ∧
    ∀ (h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (P : (Fin h → Bool) → ℝ),
      (Good (N+N+h) C ∧ C.size ≤ g ∧
        ∀ w, (cells (tab (N := N) h C w)).card ≤ m*N) →
      (∀ w, 0 ≤ P w) → (∑ w, P w) = 1 →
      (∃ U, U.card = t ∧ (v : ℝ) ≤ ∑ w, P w * (loss color (tab h C w) U : ℝ)) ∧
      (g ≤ min (m-1) (N-m) →
        (∀ U, U.card = t → (∑ w, P w * (loss color (tab h C w) U : ℝ)) ≤ (v : ℝ)) →
        Stripes (N := N) h C u)
  have hN : 0 < N := by omega
  have hu : u ≤ m := by
    dsimp [u]
    split_ifs <;> omega
  have huN : u ≤ N := by omega
  constructor
  · obtain ⟨D, hD, hs, T, hT, hev⟩ := optimal_rows (g := g) hm hmN
    refine ⟨D, ⟨hD, hs, ?_⟩, ⟨T, hT, Or.inl hev⟩, ?_⟩
    · intro w
      rw [row_area T _ (hev w), hT]
      exact Nat.mul_le_mul_right N hu
    · intro w U hU
      exact row_loss_nat color hrow T U hT hU ht (by omega) huN _ (hev w)
  · intro h C P hfit hP hPsum
    have hbound := area_bound C hmN hfit.1.2.2 hfit.2.1 hfit.2.2
    obtain ⟨hlow, hmax⟩ := minimax hN ht hNt huN color C P hP hPsum hbound
    refine ⟨hlow, ?_⟩
    intro hbudget hupper
    obtain ⟨w, hext⟩ := hmax hupper
    apply rigid C hmN hfit.1.2.2 hfit.2.1 hfit.2.2 huN ?_ ?_ w hext
    · dsimp [u]
      split_ifs <;> omega
    · dsimp [u]
      split_ifs <;> omega
